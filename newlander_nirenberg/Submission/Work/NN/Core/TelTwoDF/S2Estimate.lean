import Mathlib
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.NN.Core.TelTwoDF.EstimateDefs
import Submission.Work.NN.Core.TelTwoDF.ContDiffRec
import Submission.Work.NN.Core.TelTwoDF.S2Bound
import Submission.Work.NN.Core.TelTwoDF.dbarTransform_Eset_le
import Submission.Work.NN.Core.TelTwoDF.Rec2
import Submission.Work.NN.Core.TelTwoDF.Solves
import Submission.Work.NN.Core.TelTwoDF.holderNorm_dbarTransform_le
import Submission.Work.NN.Core.TelTwoDF.contDiff_dbarTransform_univ

namespace Work.NN.Core.TelTwoDF


/-- Loss-free `C^{k,α}` estimate and regularity for the parameterised `(0,2)` telescoping
`Work.NN.Core.TelTwoDF.S2` (`Submission/Work/NN/Core/TelTwoDF/Defs.lean`): for `0 < α < 1` and
`G : Geom n` there are constants `C k > 0` with, for every `k` and every family
`η : Fin n → Fin n → (ℂⁿ → ℂ)` with `C^k` components,

`‖(S2 G η)_j‖_{C^{k,α}(polydisc 0 G.e)} ≤ C k · Σ_{i,l} ‖η_{il}‖_{C^{k,α}(polydisc 0 G.b)}`,

and `(S2 G η)_j` is `C^k` on `polydisc 0 G.e`; moreover if `η` has (globally) smooth components
then `(S2 G η)_j` is smooth on `polydisc 0 G.e`.  The recursion (`uD`, `uPsi`, `S2` in
`TelTwoDF/Defs.lean`, with `uD_contDiff`, `E`, `E_mono`, `E_fiber`, `uD_vanish` in
`TelTwoDF/Rec2.lean`) multiplies the previous stage by the smooth cutoffs `1 - kappa G s` and
applies the Cauchy-type transform `TL G s`; the tracking sets `E G m` are polydiscs contained in
`polydisc 0 G.b`, so only a *localized* transform bound (data norm over `E G m`, cf.
`E_fiber`) is needed. -/
theorem S2Estimate {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (G : Work.NN.Core.TelTwoDF.Geom n) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      (∀ (k : ℕ) (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
        (∀ i l, ContDiff ℝ k (η i l)) →
        (∀ j : Fin n, ContDiffOn ℝ k (Work.NN.Core.TelTwoDF.S2 G η j)
            (Work.CR.Flat.polydisc 0 G.e)) ∧
        (∀ j : Fin n, Work.CR.Flat.holderNorm k α (Work.NN.Core.TelTwoDF.S2 G η j)
            (Work.CR.Flat.polydisc 0 G.e)
          ≤ ENNReal.ofReal (C k) * ∑ i, ∑ l,
              Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 G.b)))
      ∧ (∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
          (∀ i l, ContDiff ℝ (⊤ : ℕ∞) (η i l)) →
          ∀ j : Fin n, ContDiffOn ℝ (⊤ : ℕ∞) (Work.NN.Core.TelTwoDF.S2 G η j)
            (Work.CR.Flat.polydisc 0 G.e)) := by
  classical
  -- the estimate of `S2` at order `k`, with an `ENNReal` constant
  have hmain : ∀ k : ℕ, ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ), (∀ i l, ContDiff ℝ k (η i l)) →
      ∀ j : Fin n, Work.CR.Flat.holderNorm k α (S2 G η j) (Work.CR.Flat.polydisc 0 G.e)
        ≤ C * ∑ i : Fin n, ∑ l : Fin n,
            Work.CR.Flat.holderNorm k α (η i l) (Work.CR.Flat.polydisc 0 G.b) := by
    intro k
    obtain ⟨C, hCne, hC⟩ := S2_holderNorm_E_le_of_transform (n := n) hα0 hα1 k G
      (dbarTransform_Eset_le (n := n) hα0 hα1 k G)
    refine ⟨C, hCne, fun η hη j => ?_⟩
    have h := hC η hη j
    rw [Eset_n, Eset_zero] at h
    exact h
  choose Ce hCe using hmain
  refine ⟨fun k => (Ce k).toReal + 1, fun k => by positivity, ?_, ?_⟩
  · intro k η hη
    refine ⟨fun j => (S2_contDiff_k G hη j).contDiffOn, fun j => ?_⟩
    refine le_trans ((hCe k).2 η hη j) ?_
    have hle : Ce k ≤ ENNReal.ofReal ((Ce k).toReal + 1) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num : (0 : ℝ) ≤ 1),
        ENNReal.ofReal_toReal (hCe k).1, ENNReal.ofReal_one]
      exact le_add_right le_rfl
    exact mul_le_mul_left hle _
  · intro η hη j
    exact (S2_contDiff_top G hη j).contDiffOn

end Work.NN.Core.TelTwoDF
