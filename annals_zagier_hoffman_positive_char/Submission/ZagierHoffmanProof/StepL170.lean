import Submission.ZagierHoffmanProof.StepL145
import Submission.ZagierHoffmanProof.StepL161

set_option autoImplicit false
set_option maxHeartbeats 20000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L170: the G5 member DEPTH invariants (`depth ≥ depth s`)

The G5 (all-`q` front) chain of `maink_case1_j0` (StepL146) has members
`D.cA i` (`i` the iterate's a-indices, `D = BCqIter F (k-1) (toData F R0)`) and
`D.cB p`.  For the AMBIENT chain port (route (C)) each member needs
`ambNu Λ m < ambNu Λ s`; the cleanest half is the DEPTH invariant
`r ≤ D.depA i` (resp. `r ≤ D.depB p`), the analogue of StepL161's `type1_dep_ge`
for the G5 chain.  The proof is the same contradiction argument: the member's
weight is `psum s r - psum s (k-1)`, so the cumulative (`LePad`) bound `hpref`
together with `lemma29_qExp_telescope` forces
`psum s r ≤ psum s (k + depA - 1) ≤ psum s (r-1) < psum s r`.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The G5 a-side member depth is at least `depth s`. -/
theorem maink_g5_aSide_dep_ge (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (R0 : BinaryRel F) (u : R0.ιA)
    (hwtA : ∀ i : R0.ιA, i ≠ u →
      weight (R0.depA i) (R0.cA i) = psum s r - psum s (k - 1))
    (hpref : ∀ i : R0.ιA, i ≠ u → ∀ m : ℕ,
      psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))) m) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ∀ i : D.ιA, i ≠ RelData.iterIdx F (k - 1) (toData F R0) u → r ≤ D.depA i := by
  classical
  intro D i hi
  let i₀ : R0.ιA := Eq.mpr (RelData.BCqIter_ιA F (k - 1) (toData F R0)).symm i
  have hiter : RelData.iterIdx F (k - 1) (toData F R0) i₀ = i := by
    dsimp only [RelData.iterIdx, i₀]
    exact eq_mpr_symm_id (RelData.BCqIter_ιA F (k - 1) (toData F R0)) i
  have hDdep : D.depA i = R0.depA i₀ + (k - 1) := by
    dsimp only [D]
    have h := RelData.BCqIter_depA_at F (k - 1) (toData F R0) i₀
    rw [hiter] at h
    exact h
  have hi₀ : i₀ ≠ u := by intro hc; exact hi (by rw [← hiter, hc])
  rw [hDdep]
  by_contra hcon
  have hwt := hwtA i₀ hi₀
  have hpre := hpref i₀ hi₀
  have hle : R0.depA i₀ ≤ r - k := by omega
  have hpos : 0 < R0.depA i₀ := R0.hdepA i₀
  let X : ℕ → ℕ :=
    tupPadSum (single (qExp F)) (consVec (w1Of F r s k hk1 hkr hbig) (sTail r s k hkr))
  have htel := lemma29_qExp_telescope F r s k hk1 hkr hbig (R0.depA i₀) hpos
  have h1 := hpre (R0.depA i₀)
  have h2 : psum (R0.cA i₀) (R0.depA i₀) = weight (R0.depA i₀) (R0.cA i₀) :=
    psum_ge_depth (R0.cA i₀) (le_refl _)
  rw [h2, hwt] at h1
  have h3 : psumSeq X (R0.depA i₀) =
      (s ⟨k - 1, by omega⟩ : ℕ) + (psum s (k + R0.depA i₀ - 1) - psum s k) := by
    exact htel
  rw [h3] at h1
  have hpk := psum_last_eq r s k hk1 hkr
  have hkm : k + R0.depA i₀ - 1 ≤ r - 1 := by omega
  have hmono : psum s (k + R0.depA i₀ - 1) ≤ psum s (r - 1) := psum_mono s hkm
  have hpk1 : psum s (k - 1) ≤ psum s r := psum_mono s (by omega)
  have hlt : psum s (r - 1) < psum s r := psum_lt_psum_of_lt s (by omega) (le_refl r)
  have hkey : psum s (k - 1) + (psum s r - psum s (k - 1)) ≤
      psum s (k - 1) + ((s ⟨k - 1, by omega⟩ : ℕ) +
        (psum s (k + R0.depA i₀ - 1) - psum s k)) :=
    Nat.add_le_add_left h1 _
  rw [Nat.add_sub_cancel' hpk1] at hkey
  have hsk : psum s (k - 1) + ((s ⟨k - 1, by omega⟩ : ℕ) +
      (psum s (k + R0.depA i₀ - 1) - psum s k)) = psum s (k + R0.depA i₀ - 1) := by
    have hle' : psum s k ≤ psum s (k + R0.depA i₀ - 1) := psum_mono s (by omega)
    omega
  rw [hsk] at hkey
  omega

end ZagierHoffmanPositiveChar
