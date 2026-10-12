import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicPins
import Submission.Work.BoseBoxFock.thetaExp_eq_etaOf_of_pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The orthogonality pins `L²`.**  An `L^∞` (a.e. bounded and a.e. strongly measurable)
family whose members are orthonormal for the `L¹` pairing is in fact `L²`: the pairing of `e l`
with itself is `∫ ‖e l‖² = 1`, and a nonzero integral forces integrability
(`MeasureTheory.integral_undef`). -/
lemma memLp_two_of_orthonormal {m : ℕ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤) :
    ∀ l, MeasureTheory.MemLp (e l) 2
      (MeasureTheory.Volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  intro l
  -- `star z * z = ‖z‖²` for `z : ℂ`, so the self-pairing is `∫ ‖e l‖² = 1`.
  have hint : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) => ((‖e l x‖ ^ 2 : ℝ) : ℂ)) MeasureTheory.Volume := by
    have hf : MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin 3) => star (e l x) * e l x) MeasureTheory.Volume := by
      by_contra h
      have h1 := horth l l
      rw [if_pos rfl] at h1
      rw [MeasureTheory.integral_undef h] at h1
      simp at h1
    refine hf.congr (Filter.Eventually.of_forall fun x => ?_)
    change star (e l x) * e l x = ((‖e l x‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_pow]
    simpa using RCLike.conj_mul (e l x)
  have hr : MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) => ‖e l x‖ ^ 2) MeasureTheory.Volume := by
    have hre := hint.re
    simpa [- Complex.ofReal_pow] using hre
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm (hMemLp l).aestronglyMeasurable).2 hr

theorem pinTheta_etaOf {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (HM : Work.BoseBoxFock.HonestModes v μ) {e : Fin HM.m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hpair : ∀ (s : Work.BoseBoxFock.Lab HM.N) (l : Fin HM.m), s ≠ 0 →
      (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) *
          Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s) z)
        = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * HM.g s l : ℝ) : ℂ))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤) :
    ∀ s : Work.BoseBoxFock.Lab HM.N, s ≠ 0 →
      Work.BoseDict.etaOf e (HM.g s) =ᵐ[MeasureTheory.Volume]
        Work.BoseBoxFock.pinTheta v μ HM.N s := by
  classical
  have hL2 := memLp_two_of_orthonormal horth hMemLp
  have hCne : ((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.2 (pow_pos (Work.BoseBoxFock.ellH_pos v μ) 3))
  intro s hs
  have hmemT : ∀ t : Work.BoseBoxFock.Lab HM.N,
      MeasureTheory.MemLp
        (Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N t)) 2
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    fun t => (Work.BoseBoxFock.memLp_modes (Work.BoseBoxFock.ellH v μ)
      (Work.BoseBoxFock.ellH_pos v μ)).2.1
      (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N t)
  -- the pinning: `thetaExp =ᵐ √(ℓ³)·η_{g s}`
  have hmain := Work.BoseBoxFock.thetaExp_eq_etaOf_of_pairing v μ HM e horth hpair hL2 hmemT s hs
  -- divide by `√(ℓ³)`, which is exactly the normalisation in `pinTheta`
  have h2 : (fun x => (((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) *
        Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s) x)
      =ᵐ[MeasureTheory.Volume] Work.BoseDict.etaOf e (HM.g s) := by
    filter_upwards [hmain] with x hx
    rw [hx]
    rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hCne, one_mul]
  change Work.BoseDict.etaOf e (HM.g s) =ᵐ[MeasureTheory.Volume]
      fun x => (((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) *
        Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s) x
  exact h2.symm

end Work.BoseBoxFock
