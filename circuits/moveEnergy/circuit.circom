/*
    Prove: I know (x1,y1,x2,y2,p2,r2,distMax) such that:
    - x2^2 + y2^2 <= r^2
    - perlin(x2, y2) = p2
    - (x1-x2)^2 + (y1-y2)^2 <= distMax^2
    - MiMCSponge(x1,y1) = pub1
    - MiMCSponge(x2,y2) = pub2
*/

// include "../../client/node_modules/circomlib/circuits/mimcsponge.circom";
// include "../../client/node_modules/circomlib/circuits/comparators.circom";
//
// For my_compile.sh

include "mimcsponge.circom";
include "comparators.circom";


function isTriangle(x1,y1,x2,y2,x3,y3)
{
    // Calculation the area of
    // triangle. We have skipped
    // multiplication with 0.5
    // to avoid floating point
    // computations
    var a = x1 * (y2 - y3)
            + x2 * (y3 - y1)
            + x3 * (y1 - y2);
    // https://www.geeksforgeeks.org/check-whether-triangle-is-valid-or-not-if-three-points-are-given/


    return a;
}


// include "../range_proof/circuit.circom"; // The code is copy paste below
// include "../perlin/compiled.circom"

template Main() {

    //Coordinates A(x1, y1); B(x2, y2); C(x3, y3)
    // signal private input x1; //point A x
    // signal private input y1; //point A y
    // signal private input x2; //point B x
    // signal private input y2; //point B y
    // signal private input x3; //point C x
    // signal private input y3; //point C y
    signal input x1; //point A x
    signal input y1; //point A y
    signal input x2; //point B x
    signal input y2; //point B y
    signal input x3; //point C x
    signal input y3; //point C y

    signal input p2; //This is not used anymore 

    // Distance up to the edge from origin
    signal input r;

    // Maximum distance between points
    signal input distMax;

    //EnergyPoints
    signal input energyPoints;

    //Outputs
    signal output pub1;
    signal output pub2;
    signal output pub3;

    /* check abs(x1), abs(y1), abs(x2), abs(y2), abs(x3), abs(y3) < 2 ** 32 */
    component rp = MultiRangeProof(6, 40, 2 ** 32);
    rp.in[0] <== x1;
    rp.in[1] <== y1;
    rp.in[2] <== x2;
    rp.in[3] <== y2;
    rp.in[4] <== x3; //Extra checks for third point
    rp.in[5] <== y3; //Extra checks for third point

    /* check x2^2 + y2^2 < r^2 */
    component comp2 = LessThan(32);
    signal x2Sq;
    signal y2Sq;
    signal rSq;
    x2Sq <== x2 * x2;
    y2Sq <== y2 * y2;
    rSq <== r * r;
    comp2.in[0] <== x2Sq + y2Sq;
    comp2.in[1] <== rSq;
    comp2.out === 1;

    //The above checks it looks like checking that the point 
    // is not ouside the bouderies so the distance from origin
    // to margin is grater or equal (point at the edge) compared with the position of checked point
    // No check for A as is current position but a second check for third point is added
    component comp3 = LessThan(32);
    signal x3Sq;
    signal y3Sq;
    x3Sq <== x3 * x3;
    y3Sq <== y3 * y3;
    comp3.in[0] <== x3Sq + y3Sq;
    comp3.in[1] <== rSq;
    comp3.out === 1;



    /* check (x1-x2)^2 + (y1-y2)^2 <= distMax^2 */
    // distance from point A to point B is less or equal with distMax
    signal diffXAB;
    diffXAB <== x1 - x2;
    signal diffYAB;
    diffYAB <== y1 - y2;

    component ltDist1 = LessThan(32);
    signal distABSquare; 
    signal firstDistABSquare;
    signal secondDistABSquare;

    firstDistABSquare <== diffXAB * diffXAB;
    secondDistABSquare <== diffYAB * diffYAB;
    distABSquare <== firstDistABSquare + secondDistABSquare;

    ltDist1.in[0] <== distABSquare;
    ltDist1.in[1] <== distMax * distMax + 1;
    ltDist1.out === 1;

    /* check (x2-x3)^2 + (y2-y3)^2 <= distMax^2 */
    // distance from point B to point C is less or equal with distMax
    signal diffXBC;
    diffXBC <== x2 - x3;
    signal diffYBC;
    diffYBC <== y2 - y3;

    component ltDist2 = LessThan(32);
    signal distBCSquare; 
    signal firstDistBCSquare;
    signal secondDistBCSquare;

    firstDistBCSquare <== diffXBC * diffXBC;
    secondDistBCSquare <== diffYBC * diffYBC;
    distBCSquare <== firstDistBCSquare + secondDistBCSquare;


    ltDist2.in[0] <== distBCSquare;
    ltDist2.in[1] <== distMax * distMax + 1;
    ltDist2.out === 1;

    /* check (x3-x1)^2 + (y3-y1)^2 <= distMax^2 */
    // distance from point C to point A is less or equal with distMax
    signal diffXCA;
    diffXCA <== x3 - x1;
    signal diffYCA;
    diffYCA <== y3 - y1;

    component ltDist3 = LessThan(32);
    signal distCASquare; 
    signal firstDistCASquare;
    signal secondDistCASquare;

    firstDistCASquare <== diffXCA * diffXCA;
    secondDistCASquare <== diffYCA * diffYCA;
    distCASquare <== firstDistCASquare + secondDistCASquare;

    ltDist3.in[0] <== distCASquare;
    ltDist3.in[1] <== distMax * distMax + 1;
    ltDist3.out === 1;

    //Check if it's not a triangle 
    //Lenght of each side is not bigger or equal with sum of the other two

    assert(isTriangle(x1,y1,x2,y2,x3,y3));

    //Check if the energy is enough
    //As of my understanding the hop from A to B to C and back to A is in one move so
    // all the sum distance should be smaller than energy points square

    assert((distCASquare + distBCSquare + distABSquare) <= (energyPoints*energyPoints));

    /* check MiMCSponge(x1,y1) = pub1, MiMCSponge(x2,y2) = pub2 */
    /*
        220 = 2 * ceil(log_5 p), as specified by mimc paper, where
        p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    */
    component mimc1 = MiMCSponge(2, 220, 1);
    component mimc2 = MiMCSponge(2, 220, 1);
    component mimc3 = MiMCSponge(2, 220, 1);

    mimc1.ins[0] <== x1;
    mimc1.ins[1] <== y1;
    mimc1.k <== 0;
    mimc2.ins[0] <== x2;
    mimc2.ins[1] <== y2;
    mimc2.k <== 0;
    mimc3.ins[0] <== x3;
    mimc3.ins[1] <== y3;
    mimc3.k <== 0;

    pub1 <== mimc1.outs[0];
    pub2 <== mimc2.outs[0];
    pub3 <== mimc3.outs[0];

    /* check perlin(x2, y2) = p2 */
    /*
    component perlin = MultiScalePerlin(3);
    perlin.p[0] <== x2;
    perlin.p[1] <== y2;
    perlin.out === p2;
    */
}

//Just the Rang Proof Code

// NB: RangeProof is inclusive.
// input: field element, whose abs is claimed to be less than max_abs_value
// output: none
// we also want something like 4 * (abs(in) + max_abs_value) < 2 ** bits
// and bits << 256
template RangeProof(bits, max_abs_value) {
    signal input in; 

    component lowerBound = LessThan(bits);
    component upperBound = LessThan(bits);

    lowerBound.in[0] <== max_abs_value + in; 
    lowerBound.in[1] <== 0;
    lowerBound.out === 0;

    upperBound.in[0] <== 2 * max_abs_value;
    upperBound.in[1] <== max_abs_value + in; 
    upperBound.out === 0;
}

// input: n field elements, whose abs are claimed to be less than max_abs_value
// output: none
template MultiRangeProof(n, bits, max_abs_value) {
    signal input in[n];
    component rangeProofs[n];

    for (var i = 0; i < n; i++) {
        rangeProofs[i] = RangeProof(bits, max_abs_value);
        rangeProofs[i].in <== in[i];
    }
}


component main = Main();
