import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.ChiR0Defs
import Submission.Work.BoseFixR.Rb5Lin.chat_eq_cos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `LatticeW1sqPairing` — the `chat` pairing of the lattice cosine sum

For an integrable real weight `W` the corpus's Fourier transform
`chat W q = Re ∫ y, e^{-i⟪q,y⟫} W y dy` is the *cosine transform*
`∫ x, W x * cos⟪q,x⟫` (`Work.BoseFixR.Rb5Lin.chat_eq_cos`; no evenness of `W`
is needed, the real part already kills the sine part).  Consequently the
integral of `W` against a finite real combination of lattice cosines
`Σ_k c k · cos⟪kmomLab ℓ N k, ·⟫` factorises term by term:

`∫ x, W x * (Σ_k c k cos⟪p_k,x⟫) = Σ_k c k · chat W p_k`.

The proof is linearity of the integral (`integral_finsetSum`) together with
integrability of each summand: `x ↦ W x * cos⟪p_k,x⟫` is dominated by `|W|`
since `|cos| ≤ 1`.
-/

namespace Work.BoseFixR

theorem LatticeW1sqPairing {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hWe : ∀ x, W (-x) = W x)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (c : Work.BoseBoxFock.Lab N → ℝ) :
    (∫ x, W x * (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        c k * Real.cos (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x)))
      = ∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
          c k * chat W (Work.BoseBoxFock.kmomLab ℓ N k) := by
  classical
  have hcos_cont : ∀ q : EuclideanSpace ℝ (Fin 3),
      Continuous fun x : EuclideanSpace ℝ (Fin 3) => Real.cos (inner ℝ q x) :=
    fun q => Real.continuous_cos.comp (continuous_const.inner continuous_id)
  have hcont_k : ∀ k : Work.BoseBoxFock.Lab N,
      Continuous fun x : EuclideanSpace ℝ (Fin 3) =>
        c k * Real.cos (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x) :=
    fun k => continuous_const.mul (hcos_cont _)
  have hbound_k : ∀ k : Work.BoseBoxFock.Lab N,
      ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
        ‖c k * Real.cos (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x)‖ ≤ |c k| := by
    intro k
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    simpa using mul_le_of_le_one_right (abs_nonneg (c k)) (Real.abs_cos_le_one _)
  have hterm : ∀ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
      MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
        W x * (c k * Real.cos (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x))) :=
    fun k _ => hW.mul_bdd (hcont_k k).aestronglyMeasurable (hbound_k k)
  rw [show (fun x : EuclideanSpace ℝ (Fin 3) => W x *
        (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
          c k * Real.cos (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x)))
      = fun x => ∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
          W x * (c k * Real.cos (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x))
      from funext fun x => Finset.mul_sum _ _ _]
  rw [MeasureTheory.integral_finsetSum
    ((Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0) hterm]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (fun x : EuclideanSpace ℝ (Fin 3) =>
        W x * (c k * Real.cos (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x)))
      = fun x => (W x * Real.cos (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x)) * c k
      from funext fun x => by ring]
  rw [MeasureTheory.integral_mul_const]
  rw [← Work.BoseFixR.Rb5Lin.chat_eq_cos hW (Work.BoseBoxFock.kmomLab ℓ N k)]
  ring

end Work.BoseFixR
