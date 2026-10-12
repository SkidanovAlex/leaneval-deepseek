import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.BoxFockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.integral_mode_acube`

The box-integral of a mode of an orthonormal one-particle family `e : Fin m → L²(Sp)` whose
`0`-th member is the (normalised) condensate `e 0 = c·θ_Λ`, `|c|² = ℓ⁻³`:

`∫_{Λ(ℓ)} e l = c·ℓ³` for `l = 0` and `∫_{Λ(ℓ)} e l = 0` for `l ≠ 0`.

The proof is exactly the orthogonality computation, and uses **only** the three hypotheses
`he` (orthonormality), `huc` (`e 0 = c·θ_Λ` a.e.) and `hcc` (`|c|² = ℓ⁻³`): for every mode,

`conj c · ∫ θ_Λ e_l = ∫ conj(e_0) e_l = δ_{0l}`,

because `θ_Λ = 1_{Λ(ℓ)}` is real-valued (so conjugation fixes it) and equals the indicator of the
box (`corpusBox_boxL_eq_acube`); multiplying by `c` gives `ℓ⁻³·∫ θ_Λ e_l = c·δ_{0l}`, and
`∫_{Λ(ℓ)} e_l = ℓ³·c·δ_{0l}`.  The support hypothesis `hsupp` is not needed (the pointwise
identity `θ_Λ·e_l = 1_{Λ(ℓ)}·e_l` holds everywhere, with no support restriction).
-/

namespace Work.BoseBoxFock

theorem integral_mode_acube {m : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → Work.BoseDict.Sp → ℂ} {c : ℂ}
    (he : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (huc : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    (hcc : (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹)
    (l : Fin m) :
    (∫ y in Submission.BoseGases.acube ℓ, e l y)
      = if l = 0 then c * ((ℓ ^ 3 : ℝ) : ℂ) else 0 := by
  classical
  -- The sharp box indicator `θ_Λ` is the indicator of the box `boxL ℓ`.
  have hsmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet _ ℓ
  have hθpt : ∀ y : Work.BoseDict.Sp,
      (Work.BoseK15.corpusBox.boxL ℓ).indicator (e l) y
        = Work.BoseK15.corpusBox.thetaFun ℓ y * e l y := by
    intro y
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hy : y ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [Set.indicator_of_mem hy, if_pos hy, one_mul]
    · rw [Set.indicator_of_notMem hy, if_neg hy, zero_mul]
  -- `θ_Λ` is real valued, so conjugation fixes it.
  have hconjθ : ∀ y : Work.BoseDict.Sp,
      (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ y)
        = Work.BoseK15.corpusBox.thetaFun ℓ y := by
    intro y
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hy : y ∈ Work.BoseK15.corpusBox.boxL ℓ <;> simp [hy]
  -- the set integral over `acube ℓ` is the `θ_Λ`-weighted integral
  have hLHS : (∫ y in Submission.BoseGases.acube ℓ, e l y)
      = ∫ y, Work.BoseK15.corpusBox.thetaFun ℓ y * e l y := by
    rw [← Work.BoseBoxFock.corpusBox_boxL_eq_acube hℓ,
      ← MeasureTheory.integral_indicator (f := fun y => e l y) hsmeas]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hθpt)
  -- the key identity: `conj c · ∫ θ_Λ e_l = ∫ conj(e_0) e_l`
  have hae : (fun y : Work.BoseDict.Sp =>
        (starRingEnd ℂ) c * (Work.BoseK15.corpusBox.thetaFun ℓ y * e l y))
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))]
        (fun y : Work.BoseDict.Sp => (starRingEnd ℂ) (e 0 y) * e l y) := by
    filter_upwards [huc] with y hy
    rw [hy, map_mul, hconjθ y]
    ring
  have key : (starRingEnd ℂ) c * (∫ y, Work.BoseK15.corpusBox.thetaFun ℓ y * e l y)
      = ∫ y, (starRingEnd ℂ) (e 0 y) * e l y := by
    rw [← MeasureTheory.integral_const_mul ((starRingEnd ℂ) c)
      (fun y => Work.BoseK15.corpusBox.thetaFun ℓ y * e l y)]
    exact MeasureTheory.integral_congr_ae hae
  -- `|c|² = ℓ⁻³`
  have hL : (((ℓ ^ 3 : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 3 (ne_of_gt hℓ))
  have hcc' : (starRingEnd ℂ) c * c = (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹ := by
    simpa [Complex.ofReal_pow] using hcc
  -- multiplying `conj c · A = d` by `c` turns the left side into `ℓ⁻³ · A`
  have hscale : ∀ A d : ℂ, (starRingEnd ℂ) c * A = d →
      (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹ * A = c * d := by
    intro A d hA
    have h := congrArg (fun z : ℂ => c * z) hA
    rwa [← mul_assoc, mul_comm c ((starRingEnd ℂ) c), hcc'] at h
  -- and multiplying `ℓ⁻³ · A = d` by `ℓ³` solves for `A`
  have hcancel : ∀ A : ℂ, (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹ * A = c →
      A = c * (((ℓ ^ 3 : ℝ)) : ℂ) := by
    intro A hA
    have h := congrArg (fun z : ℂ => (((ℓ ^ 3 : ℝ)) : ℂ) * z) hA
    rw [← mul_assoc, mul_inv_cancel₀ hL, one_mul, mul_comm] at h
    exact h
  rw [hLHS]
  by_cases hl : l = 0
  · -- the condensate mode: `⟨θ, e_l⟩ = c·ℓ³`
    rw [if_pos hl]
    have h1 : ∫ y, (starRingEnd ℂ) (e 0 y) * e l y = 1 := by
      have h := he 0 l
      rwa [if_pos (hl.symm : (0 : Fin m) = l)] at h
    have h2 : (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹
        * (∫ y, Work.BoseK15.corpusBox.thetaFun ℓ y * e l y) = c := by
      simpa using hscale _ 1 (key.trans h1)
    exact hcancel _ h2
  · -- an excited mode: orthogonality to `e_0 = c·θ` forces `∫ θ e_l = 0`
    rw [if_neg hl]
    have h1 : ∫ y, (starRingEnd ℂ) (e 0 y) * e l y = 0 := by
      have h := he 0 l
      rw [if_neg (fun h0 : (0 : Fin m) = l => hl h0.symm)] at h
      exact h
    have h2 : (((ℓ ^ 3 : ℝ)) : ℂ)⁻¹
        * (∫ y, Work.BoseK15.corpusBox.thetaFun ℓ y * e l y) = 0 := by
      simpa using hscale _ 0 (key.trans h1)
    have h3 : (∫ y, Work.BoseK15.corpusBox.thetaFun ℓ y * e l y) = 0 := by
      have h := congrArg (fun z : ℂ => (((ℓ ^ 3 : ℝ)) : ℂ) * z) h2
      rw [mul_zero, ← mul_assoc, mul_inv_cancel₀ hL, one_mul] at h
      exact h
    rw [h3]

end Work.BoseBoxFock
