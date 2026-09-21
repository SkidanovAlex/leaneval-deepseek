import Mathlib
import Submission.Work.OddCurveB.Est.Defs
import Submission.Work.OddCurveB.Est.Model
import Submission.Work.OddCurveB.Est.psi_inverse
import Submission.Work.OddCurveB.Est.psi_continuous

/-!
# The diagonal linearization of the unperturbed odd Volterra map, uniformly on a slope interval

`fderiv_Godd` (in `Est/Model.lean`) computes `fderiv ℝ (fun z => Godd n 0 s z) (baseState s)`
as the explicit block map `Phi n s`, and `psi_inverse` (in `Est/psi_inverse.lean`) shows that
`Psi n s` — whose two non-constant rows are the rows of the inverse `2×2` block, transported by
the two linear relations — is a two-sided inverse of `Phi n s` whenever `pA n s, pC n s ≠ 0`
(true for `s > 0`).  `psi_continuous` (in `Est/psi_continuous.lean`) gives the continuity of
`s ↦ Psi n s` on every `[a,b]` with `a > 0`; compactness of `[a,b]` then bounds its norm.

Hence the `fderiv`s are uniformly invertible on `[a,b]`: there is a family
`A : ℝ → St ≃L[ℝ] St` of linear isometric equivalences whose underlying maps are the
`fderiv`s on `[a,b]`, whose inverse family is continuous on `[a,b]`, and whose inverse family is
bounded on `[a,b]`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddCurveB.Est

open Work.OddVolterra

noncomputable section

/-- The linear equivalence of `St` with inverse `Psi n s`, valid whenever `pA n s, pC n s ≠ 0`. -/
noncomputable def linEquiv (n : ℕ) (s : ℝ) (hA : pA n s ≠ 0) (hC : pC n s ≠ 0) :
    St ≃L[ℝ] St :=
  ContinuousLinearEquiv.equivOfInverse (Phi n s) (Psi n s)
    (psi_inverse n s hA hC).1 (psi_inverse n s hA hC).2

/-- The global family of linear equivalences: `Phi n s` where it is invertible, the identity
elsewhere (the values outside the invertibility locus are never used). -/
noncomputable def A (n : ℕ) : ℝ → St ≃L[ℝ] St := fun s =>
  if h : pA n s ≠ 0 ∧ pC n s ≠ 0 then linEquiv n s h.1 h.2
  else ContinuousLinearEquiv.refl ℝ St

lemma A_coe (n : ℕ) {s : ℝ} (hA : pA n s ≠ 0) (hC : pC n s ≠ 0) :
    ((A n s) : St →L[ℝ] St) = Phi n s := by
  unfold A
  rw [dif_pos ⟨hA, hC⟩]
  rfl

lemma A_symm_coe (n : ℕ) {s : ℝ} (hA : pA n s ≠ 0) (hC : pC n s ≠ 0) :
    (((A n s).symm : St ≃L[ℝ] St) : St →L[ℝ] St) = Psi n s := by
  unfold A
  rw [dif_pos ⟨hA, hC⟩]
  simp only [linEquiv]
  rw [ContinuousLinearEquiv.symm_equivOfInverse]
  rfl

theorem exists_linearization (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∃ A : ℝ → Work.OddVolterra.St ≃L[ℝ] Work.OddVolterra.St, ∃ B : ℝ, 0 < B ∧
      (∀ s ∈ Set.Icc a b, (A s : Work.OddVolterra.St →L[ℝ] Work.OddVolterra.St)
        = fderiv ℝ (fun z => Work.OddVolterra.Godd n 0 s z) (Work.OddVolterra.baseState s)) ∧
      ContinuousOn (fun s => ((A s).symm : Work.OddVolterra.St →L[ℝ] Work.OddVolterra.St)) (Set.Icc a b) ∧
      (∀ s ∈ Set.Icc a b, ‖((A s).symm : Work.OddVolterra.St →L[ℝ] Work.OddVolterra.St)‖ ≤ B) := by
  have hcont := psi_continuous (n := n) (a := a) (b := b) ha
  have hbdd : ∃ B, 0 < B ∧ ∀ s ∈ Set.Icc a b, ‖Psi n s‖ ≤ B := by
    obtain ⟨s₀, -, hmax⟩ :=
      isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hcont.norm
    exact ⟨‖Psi n s₀‖ + 1, by positivity,
      fun s hs => le_of_lt (lt_of_le_of_lt (hmax hs) (lt_add_one _))⟩
  obtain ⟨B, hBpos, hB⟩ := hbdd
  refine ⟨A n, B, hBpos, ?_, ?_, ?_⟩
  · intro s hs
    have hs0 : 0 < s := by linarith [hs.1, ha]
    rw [A_coe n (pA_ne_zero n hs0) (pC_ne_zero n hs0)]
    exact (fderiv_Godd n hn hs0).symm
  · refine hcont.congr ?_
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1, ha]
    exact (A_symm_coe n (pA_ne_zero n hs0) (pC_ne_zero n hs0))
  · intro s hs
    have hs0 : 0 < s := by linarith [hs.1, ha]
    rw [A_symm_coe n (pA_ne_zero n hs0) (pC_ne_zero n hs0)]
    exact hB s hs

end

end Work.OddCurveB.Est
