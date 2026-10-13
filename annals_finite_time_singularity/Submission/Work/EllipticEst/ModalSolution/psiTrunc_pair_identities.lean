import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.EllipticEst.ModalSolution.PairIdent.eFam_finSum_bilin
import Submission.Work.EllipticEst.ModalSolution.PairIdent.lzero_finSum_eFam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

set_option autoImplicit false

/-!
# The two diagonal identities for the truncated mode series `psiTrunc`

For `psiTrunc α F N z θ = ∑_{m ≤ N} acoeff α m F z · eFam m θ` (the `N`-th partial sum of the
mode series for `bslOp α Ψ = F`, `FTS/PhiStar/Series/Defs.lean`) and the Dirichlet eigenbasis
`eFam m = cos θ · gC (2m+1)(sin θ)` of `Work.Elliptic.Lzero` with eigenvalues
`lam m = 2m(2m+5)`, the two weighted diagonal identities hold:

* `∫_{Iθ} (psiTrunc …)² cos θ = ∑_{m ≤ N} (∫_{Iθ} eFam m² cos θ) · (acoeff α m F z)²`
  (finite Parseval: expand the square into the double sum and use the orthogonality
  `Gegenbauer.eFam_orthogonal` off the diagonal);
* `∫_{Iθ} (Lzero (psiTrunc …)) · (psiTrunc …) · cos θ
     = ∑_{m ≤ N} lam m · (∫_{Iθ} eFam m² cos θ) · (acoeff α m F z)²`
  (`Lzero` acts diagonally, `Gegenbauer.eFam_Lzero`, and the cross terms die by orthogonality).

Both sides are finite sums, so no measurability, integrability or convergence hypothesis is
needed anywhere: the modes are `C^∞` (`FTS/PhiStar/Series/psiTrunc_solves.lean`, `contDiff_eFam`).
The only analytic bookkeeping is that `Lzero`'s `tan θ`-term needs `cos θ ≠ 0`, which holds on
`Iθ` except at the single null point `θ = π/2` (`cos_ne_zero_of_mem_Iθ`, `ae_ne_pi_half_volume`).

The two independent bricks are `PairIdent.eFam_finSum_bilin` (bilinear finite Parseval for the
basis, any coefficients) and `PairIdent.lzero_finSum_eFam` (the pointwise diagonal action of
`Lzero` on an arbitrary finite mode combination).
-/

/-- On `Iθ = [0, π/2]` the only zero of `cos` is the right endpoint, so away from `π/2` the
cosine does not vanish.  This is the hypothesis under which the eigenfunction identity
`Gegenbauer.eFam_Lzero` is available. -/
lemma cos_ne_zero_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (h : θ ≠ Real.pi / 2) :
    Real.cos θ ≠ 0 := by
  have hlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 h
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hlt⟩)

/-- The single point `π/2` is null, so `cos θ ≠ 0` holds almost everywhere on `Iθ`. -/
lemma ae_ne_pi_half_volume : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    θ ≠ Real.pi / 2 := by
  rw [MeasureTheory.ae_iff]
  have h : {θ : ℝ | ¬ θ ≠ Real.pi / 2} = ({Real.pi / 2} : Set ℝ) := by ext θ; simp
  rw [h]
  exact MeasureTheory.measure_singleton _

theorem psiTrunc_pair_identities (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ) :
    ((∫ θ in Work.Spaces.Iθ, (Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2 * Real.cos θ)
        = ∑ m ∈ Finset.range (N + 1),
            (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
              * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2)
    ∧ ((∫ θ in Work.Spaces.Iθ,
          Work.Elliptic.Lzero (fun _ θ' => Work.FTS.PhiStar.Series.psiTrunc α F N z θ') 0 θ
            * Work.FTS.PhiStar.Series.psiTrunc α F N z θ * Real.cos θ)
        = ∑ m ∈ Finset.range (N + 1),
            Work.FTS.PhiStar.Gegenbauer.lam m
              * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
              * (Work.FTS.PhiStar.Series.acoeff α m F z) ^ 2) := by
  constructor
  · -- First identity: expand the finite mode sum and use orthogonality of the basis.
    have h1 : (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.psiTrunc α F N z θ) ^ 2 * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ,
            (∑ m ∈ Finset.range (N + 1),
              Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * (∑ m ∈ Finset.range (N + 1),
                Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * Real.cos θ := by
      refine MeasureTheory.setIntegral_congr_fun ?_ ?_
      · rw [Work.Spaces.Iθ]; exact measurableSet_Icc
      · intro θ hθ
        simp only [Work.FTS.PhiStar.Series.psiTrunc]
        ring
    rw [h1]
    rw [PairIdent.eFam_finSum_bilin (fun m => Work.FTS.PhiStar.Series.acoeff α m F z)
      (fun m => Work.FTS.PhiStar.Series.acoeff α m F z) N]
    exact Finset.sum_congr rfl (fun m hm => by ring)
  · -- Second identity: `Lzero` acts diagonally on the truncated mode sum.
    have hf : (∫ θ in Work.Spaces.Iθ,
        Work.Elliptic.Lzero (fun _ θ' => Work.FTS.PhiStar.Series.psiTrunc α F N z θ') 0 θ
          * Work.FTS.PhiStar.Series.psiTrunc α F N z θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ,
            (∑ m ∈ Finset.range (N + 1),
              Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Series.acoeff α m F z
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * (∑ m ∈ Finset.range (N + 1),
                Work.FTS.PhiStar.Series.acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * Real.cos θ := by
      refine MeasureTheory.setIntegral_congr_ae ?_ ?_
      · rw [Work.Spaces.Iθ]; exact measurableSet_Icc
      · filter_upwards [ae_ne_pi_half_volume] with θ hθ hθI
        have hcos : Real.cos θ ≠ 0 := cos_ne_zero_of_mem_Iθ hθI hθ
        have hL := PairIdent.lzero_finSum_eFam
          (fun m => Work.FTS.PhiStar.Series.acoeff α m F z) N 0 θ hcos
        simp only [Work.FTS.PhiStar.Series.psiTrunc] at hL ⊢
        rw [hL]
    rw [hf]
    rw [PairIdent.eFam_finSum_bilin
      (fun m => Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Series.acoeff α m F z)
      (fun m => Work.FTS.PhiStar.Series.acoeff α m F z) N]
    exact Finset.sum_congr rfl (fun m hm => by ring)

end Work.EllipticEst.ModalSolution
