import Mathlib
import Submission.Work.Peluse.LadderP.p2jensen
import Submission.Work.Peluse.LadderP.p2UNormSplit
import Submission.Work.Peluse.LadderP.p2ClassFit
import Submission.Work.Peluse.LadderP.p2ClassData

/-! ## The reduction of the frozen `lemma51P 2` to its class data

The definitions (`p2Cls`, `p2ClsFn`, `p2Sup`, `p2Wt`, `p2BoxAvg`, `p2Heart`) live in
`Submission/Work/Peluse/LadderP/p2Defs.lean`.  This module contains the *assembly* of the P2 node: the frozen `lemma51P 2` follows from the `c = 1`
heart `p2Heart` applied to the residue classes mod `c`.

Mathematical content: the paper's "split `ℤ` into arithmetic progressions mod `c`" step.  For

  `S_r = {x ∈ symIcc N : x ≡ r (mod c)}`,   `f_r(ξ) = f (r + c ξ)`,

* the dilate-splitting identity (`p2dilateSplit`) gives
  `‖f‖^{4}_{□²_{c((a+b_i)[M₂])}(symIcc N)} = ∑_r w_r ‖f_r‖^{4}_{□²_{((a+b_i)[M₂])}(S_r)}` with
  `w_r = |S_r| / |symIcc N|`, so the averaged hypothesis `γ ≤ boxAvgA 2 c M₁ M₂ b N f` implies
  `γ ≤ ∑_r w_r γ_r` with `γ_r = p2BoxAvg M₁ M₂ b S_r f_r` (weighted power mean);
* the heart applied to the classes with `γ_r ≥ γ/2` gives `C_h γ_r^e ≤ ‖f_r‖_{U^{s'}_{[D]}(S_r)}`;
* the dilate-splitting identity for the uniformity norm converts the class conclusions back into
  `‖f‖^{2^{s'}}_{U^{s'}_{c[D]}(symIcc N)}`, and Jensen's inequality completes the assembly.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-! ## The assembly -/

/-- `uNormPow` is the `2^{s}`-th power of `uNorm`. -/
lemma p2uNormPow_eq_pow (s : ℕ) (Q S : Finset ℤ) (g : ℤ → ℂ) :
    uNormPow s Q S g = (uNorm s Q S g) ^ (2 ^ s) :=
  (Work.Peluse.BoxNorm.boxNorm_pow s (fun _ : Fin s => Q) S g).symm

/-- The class weights lie in `[0,1]`. -/
lemma p2Wt_le_one (c : ℤ) (N r : ℕ) : p2Wt c N r ≤ 1 := by
  rw [p2Wt, div_le_one (by exact_mod_cast card_symIcc_pos (N := N))]
  exact_mod_cast p2Cls_card_le c N r

end

end Work.Peluse.LadderP
