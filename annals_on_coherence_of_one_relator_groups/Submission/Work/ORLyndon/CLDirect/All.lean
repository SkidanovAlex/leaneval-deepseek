import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.nonempty_clData
import Submission.Work.ORLyndon.CLDirect.conj_pow_eq
import Submission.Work.ORLyndon.CLDirect.normalClosure_pow_le
import Submission.Work.ORLyndon.CLDirect.clPi_of
import Submission.Work.ORLyndon.CLDirect.clDelta_mul
import Submission.Work.ORLyndon.CLDirect.clDelta_of
import Submission.Work.ORLyndon.CLDirect.clDelta_one
import Submission.Work.ORLyndon.CLDirect.clDelta_pow
import Submission.Work.ORLyndon.CLDirect.clDelta_conj_of_trivial
import Submission.Work.ORLyndon.CLDirect.clChi_conj
import Submission.Work.ORLyndon.CLDirect.clChi_eq_one_of_mem
import Submission.Work.ORLyndon.CLDirect.orderOf_presentRho_of_clData
import Submission.Work.ORLyndon.CLDirect.thetaLin_of
import Submission.Work.ORLyndon.CLDirect.presentSec_inv_mul_mem
import Submission.Work.ORLyndon.CLDirect.thetaFun_mul_mem
import Submission.Work.ORLyndon.CLDirect.thetaLin_mul_of_mem_span
import Submission.Work.ORLyndon.CLDirect.sum_smul_of_sub_one_eq
import Submission.Work.ORLyndon.CLDirect.foxKernel_vanish
import Submission.Work.ORLyndon.CLDirect.presentAlg_foxD_conj
import Submission.Work.ORLyndon.CLDirect.clPhi_one
import Submission.Work.ORLyndon.CLDirect.clPhi_mul
import Submission.Work.ORLyndon.CLDirect.clPhi_inv
import Submission.Work.ORLyndon.CLDirect.clPhi_conj_pow
import Submission.Work.ORLyndon.CLDirect.clPhi_conj
import Submission.Work.ORLyndon.CLDirect.coeffs_zero_of_sum_mul_normElem
import Submission.Work.ORLyndon.CLDirect.lyndonIndependence_of_clData

/-!
# The Cohen--Lyndon route to `lyndon_independence_of_pow` (`Submission/Work/ORLyndon/CLDirect`)

Umbrella module for the chapter of `Submission/Work/ORLyndon/CLDirect`.  Design document:
`Submission/Work/ORLyndon/CASE2INPUT_LEAD.md`.

Route (all under `namespace Work.ORLyndon.CLDirect`):

* `cldDefs` — `CLData` (N4's Cohen--Lyndon basis data), the character `clChi`, the crossed
  homomorphism `clDelta` and its transport `clPhi`, and the Fox-kernel machinery
  `presentSec`/`thetaFun`/`thetaLin`;
* A-chain: `nonempty_clData`, `conj_pow_eq`, `normalClosure_pow_le`, `clChi_conj`,
  `clChi_eq_one_of_mem`, `orderOf_presentRho_of_clData` — the order of `u` in `⟨X | u^l⟩` is `l`;
* B-chain: `clPi_of`, `clDelta_mul`, `clDelta_of`, `clDelta_one`, `clDelta_pow`,
  `clDelta_conj_of_trivial`, `clPhi_one`, `clPhi_mul`, `clPhi_inv`, `clPhi_conj_pow`, `clPhi_conj`
  — `clPhi` is additive on `⟪u^l⟫` and equivariant under conjugation;
* C-chain: `thetaLin_of`, `presentSec_inv_mul_mem`, `thetaFun_mul_mem`, `thetaLin_mul_of_mem_span`,
  `sum_smul_of_sub_one_eq`, `foxKernel_vanish` — the Fox-kernel (Magnus embedding) lemma;
* D-chain: `presentAlg_foxD_conj`, `coeffs_zero_of_sum_mul_normElem`, `lyndonIndependence_of_clData`
  — the assembly, giving `Work.ORLyndon.LyndonIndependence K (u^l) u`.

`Work.ORLyndon.lyndon_independence_of_pow` (`Submission/Work/ORLyndon/lyndon_independence_of_pow.lean`)
is the `CLData`-free form, and `Submission/Work/ORLyndon/lyndonIdentity_of_pow.lean` the
unconditional Lyndon identity theorem and `globalDim ≤ 2`.
-/
