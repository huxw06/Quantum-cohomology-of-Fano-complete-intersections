# Quantum-cohomology-of-Fano-complete-intersections
These are Macaulay2 packages that accompany the paper https://arxiv.org/abs/1501.03683 on quantum cohomology of non-exceptional Fano complete intersections, and the paper  https://arxiv.org/abs/2109.11469 on quantum cohomology of even dimensional complete intersections of two quadrics.

To use the package QuantumCohomologyFanoCompleteIntersection.m2, for example in Mac OS, please put it into the directory

/applications/macaulay2-1.xx/share/macaulay2

where 1.xx is your Macaulay2 version, or use the command 

path = append(path, "...")

where ... is the directory containing the downloaded package. For other OS please consult http://www2.macaulay2.com/Macaulay2/Downloads/.

Then in Macaulay2 running

loadPackage "QuantumCohomologyFanoCompleteIntersection"

----------------------------

Let X be a Fano complete intersection of dim n and multidegree d=(d_1,…d_r) in P^{n+r}, where each d_i>=2. Let h be the hyperplane cohomology class on X. Denote by t_0,t_1,…,t_n the basis dual to 1,h,…,h^n.
Then running

ambientGeneratingFuncOfDegreeUpToB {n,{d_1,…,d_r},B}

returns the generating function of ambient genus 0 primary Gromov-Witten invariants of X. One can compare the results to those from Giosuè's Julia package, which is based on virtual torus localization directly.

Suppose X is Not an even dimensional complete intersections of two quadrics. Namely if d=(2,2) then n must be odd. The generating function of genus 0 Gromov-Witten invariants of X, allowing non-ambient classes as insertions, depends on the variables dual to an orthonormal basis of primitive cohomology through only one variable s. For the precise definition of s see https://arxiv.org/abs/1501.03683 .

 Then running
 
generatingFuncOfDegreeUpToB {n,{d_1,…,d_r},B}

returns the generating function of genus 0 primary Gromov-Witten invariants of X. 

Warning:

(i) Our algorithm, based on the square root recursion, will check whether some quadratic equations have two equal roots at certain steps. If running generatingFuncOfDegreeUpToB returns a polynomial, it means that all the checks encountered are valid. But a priori the effectivity of our algorithm in running generatingFuncOfDegreeUpToB in all s-degrees is a conjecture;

(ii) When n is odd, the terms with s-degree > m/4+1 is hypothetical, where m is the rank of the primitive cohomology.

If you encounter an information “the square root recursion fails at order ..” when you use generatingFuncOfDegreeUpToB, please contact the author! The main conjecture in an forthcoming update of  https://arxiv.org/abs/1501.03683 is, among other things, that such information will never appear.

If X is an even dimensional complete intersections of two quadrics, this package also contains functions to compute the genus 0 invariants, up to an unknown special invariant. 

Update in 2022/05/05: the bug on the function generatingFuncOfDegreeUpToB fixed. Thanks Shuai Guo for finding this. 
