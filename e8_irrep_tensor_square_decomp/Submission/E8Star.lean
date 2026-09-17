import Submission.E8CertAll
import Submission.E8Regroup

/-!
# The candidate characters of the constituents of the tensor square

`Submission.E8Cert.Mnu i` is the candidate multiplicity function of `L(ord40 i)`, built from the
Freudenthal table `Mtab` and the dominant-conjugate lookup.  This file proves the three *easy*
hypotheses of `Submission.E8Character.eq_of_freudenthal` for it:

* `Mnu_dom`      -- `Mnu i (ord40 i) = 1` (and, more generally, `Mnu i (ord40 d) = Mtab i d`);
* `Mnu_support`  -- a non-zero value is only attained at weights dominated by `ord40 i`;
* `Mnu_dc`       -- invariance under the dominant conjugate.

The Freudenthal recursion (the fourth hypothesis) is proved in `Submission/E8Rec.lean`.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8Star

open Submission.E8Extract Submission.E8Orbit Submission.E8Character Submission.E8Casimir Submission.E8Cert
open Submission.E8Enum Submission.E8Numerics Submission.E8Engine
open Submission.WeylReflect Submission.WeylReflect Submission.WeylWeights

/-- **The dominant conjugate of a weight of the forty is itself**, so the lookup returns its index. -/
theorem domIdx_dom : ∀ d : Fin 40, domIdx (ord40get d) = some d := by
  decide

/-- **The candidate character at a dominant weight is the Freudenthal table.** -/
theorem Mnu_dom (i d : Fin 40) : Mnu i (ord40get d) = Mtab i d := by
  rw [Mnu, domIdx_dom d]
  rfl

/-- The candidate character of `L(ord40 i)` takes the value `1` at its top weight. -/
theorem Mnu_top : ∀ i : Fin 40, Mnu i (ord40get i) = 1 := by
  decide

/-- **The dominant-conjugate lookup is invariant.** -/
theorem domIdx_dcX (v : Fin 8 → ℤ) : domIdx (dcX v) = domIdx v := by
  have hq : E8Engine.qE (dcX v) ≤ 40 ↔ E8Engine.qE v ≤ 40 := by
    rw [E8Engine.qE_eq_qq, E8Engine.qE_eq_qq, qZ_dcX]
  have hdc : Submission.DcFast.dcWE (dcX v) = Submission.DcFast.dcWE v := by
    rw [Submission.DcFast.dcWE_eq_dcXE, Submission.DcFast.dcWE_eq_dcXE, dcXE_eq, dcXE_eq,
      dcX_idem]
  rw [domIdx, domIdx, hdc]
  by_cases h : E8Engine.qE v ≤ 40
  · rw [if_pos h, if_pos (hq.mpr h)]
  · rw [if_neg h, if_neg (fun hh => h (hq.mp hh))]

/-- **Invariance of the candidate character under the dominant conjugate.** -/
theorem Mnu_dc (i : Fin 40) (v : Fin 8 → ℤ) : Mnu i (dc v) = Mnu i v := by
  rw [← dcX_eq_dc]
  show (domIdx (dcX v)).elim 0 (fun e => Mtab i e) = (domIdx v).elim 0 (fun e => Mtab i e)
  rw [domIdx_dcX]

/-- `posCon` tested through the kernel-fast `mvn`. -/
def posF (γ : Fin 8 → ℤ) : Bool := (List.finRange 8).all (fun i => decide (0 ≤ mvn γ i))

lemma posF_true {γ : Fin 8 → ℤ} : posF γ = true ↔ posCon γ := by
  rw [posCon]
  constructor
  · intro h i
    have h1 : ∀ i ∈ List.finRange 8, (0 : ℤ) ≤ mvn γ i := by
      intro i hi
      have h2 := (List.all_eq_true.mp h) i hi
      simpa using h2
    have h2 : (0 : ℤ) ≤ mvn γ i := h1 i (List.mem_finRange i)
    have hmc : mvn γ i = coords γ i := by rw [mvn_eq, coords_eq]
    rwa [hmc] at h2
  · intro h
    apply List.all_eq_true.mpr
    intro i _
    have hmc : mvn γ i = coords γ i := by rw [mvn_eq, coords_eq]
    rw [hmc]
    exact decide_eq_true (h i)

theorem Mtab_support : ∀ (i e : Fin 40), Mtab i e ≠ 0 → posF (ord40get i - ord40get e) = true := by
  decide

/-- **The support condition** for the candidate character. -/
theorem Mnu_support (i : Fin 40) {v : Fin 8 → ℤ} (h : Mnu i v ≠ 0) :
    ord40get i - v = 0 ∨ posCon (ord40get i - v) := by
  obtain ⟨e, he⟩ : ∃ e, domIdx v = some e := by
    cases hd : domIdx v with
    | none => exact absurd (by simp [Mnu, hd]) h
    | some e => exact ⟨e, rfl⟩
  have htab : Mtab i e ≠ 0 := by
    intro h0
    exact h (by simp [Mnu, he, h0])
  have hcon : posCon (ord40get i - ord40get e) :=
    posF_true.mp (Mtab_support i e htab)
  have hstep : posCon (ord40get e - v) := by
    rw [show ord40get e = dcX v from domIdx_sound he]
    exact dcX_sub_posCon v
  have : ord40get i - v = (ord40get i - ord40get e) + (ord40get e - v) := by abel
  rw [this]
  exact Or.inr (posCon_add hcon hstep)

end Submission.E8Star
