import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotGroupDefs
import Submission.Work.BoseBoxFock.qVec_eq_etaOf_of_pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem thetaExp_eq_etaOf_of_pairing (v : ℝ³ → ℝ) (μ : ℝ) (HM : Work.BoseBoxFock.HonestModes v μ)
    (e : Fin HM.m → ℝ³ → ℂ)
    (horth : ∀ l l', (∫ x : ℝ³, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then 1 else 0)
    (hpair : ∀ (s : Work.BoseBoxFock.Lab HM.N) (l : Fin HM.m), s ≠ 0 →
      (∫ x : ℝ³, (starRingEnd ℂ) (e l x) *
          Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s) x)
        = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * (HM.g s l) : ℝ) : ℂ))
    (hmemE : ∀ l, MeasureTheory.MemLp (e l) 2 (MeasureTheory.Volume)
    )
    (hmemT : ∀ s, MeasureTheory.MemLp
      (Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s)) 2
      (MeasureTheory.volume : MeasureTheory.Measure ℝ³))
    (s : Work.BoseBoxFock.Lab HM.N) (hs : s ≠ 0) :
    Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s)
      =ᵐ[MeasureTheory.volume] fun x =>
        ((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3) : ℝ) : ℂ) *
          Work.BoseDict.etaOf e (HM.g s) x := by
  classical
  have hℓpos : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  -- `√(ℓ³) = ℓ^{3/2}`, the normalisation of the pinning data
  have hsqrt : Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3)
      = (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (Work.BoseBoxFock.ellH v μ) 3,
      ← Real.rpow_mul (le_of_lt hℓpos)]
    norm_num
  -- the pairing hypothesis in the `√(ℓ³)·g` form the general expansion lemma uses
  have hpair' : ∀ l : Fin HM.m,
      (∫ x : ℝ³, (starRingEnd ℂ) (e l x) *
          Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s) x)
        = ((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3) : ℝ) : ℂ)
            * ((HM.g s l : ℝ) : ℂ) := by
    intro l
    rw [hpair s l hs, Complex.ofReal_mul, ← hsqrt]
  have hk : Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s
      = (Work.BoseBoxFock.ellH v μ)⁻¹ • Work.BoseB4.vec (Work.BoseBoxFock.labVec HM.N s) := rfl
  -- Bessel equality: `Σ_l ‖√(ℓ³) g s l‖² = ∫ ‖Θ_s‖²`, i.e. `ℓ³·gram(g s)(g s) = ⟨Θ_s,Θ_s⟩`
  have hbessel : (∑ l : Fin HM.m,
        ‖((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3) : ℝ) : ℂ) * ((HM.g s l : ℝ) : ℂ)‖ ^ 2)
      = ∫ x : ℝ³, ‖Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
          (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s) x‖ ^ 2 := by
    have h1 : ∀ l : Fin HM.m,
        ‖((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3) : ℝ) : ℂ) * ((HM.g s l : ℝ) : ℂ)‖ ^ 2
          = (Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3)) ^ 2 * (HM.g s l) ^ 2 := by
      intro l
      rw [← Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
      ring
    simp only [h1]
    rw [← Finset.mul_sum, Real.sq_sqrt (by positivity)]
    have hgram : (∑ l : Fin HM.m, (HM.g s l) ^ 2) = Work.BoseB4.gram (HM.g s) (HM.g s) := by
      simp [Work.BoseB4.gram, pow_two]
    rw [hgram, HM.hg s s hs hs]
    rw [if_pos rfl, mul_one]
    rw [← realIP_self_eq_integral]
    rw [hk, Work.BoseB4.realIP_thetaExp_thetaExp_of_cell Work.BoseK15.corpusBox rfl hℓpos
      (Work.BoseBoxFock.labVec HM.N s) (Work.BoseBoxFock.labVec HM.N s)]
    rw [if_pos rfl]
  have hmain := eq_etaOf_of_pairing (e := e)
      (Q := fun x : ℝ³ => Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
            (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s) x)
      (c := fun l : Fin HM.m => ((Real.sqrt ((Work.BoseBoxFock.ellH v μ) ^ 3) : ℝ) : ℂ)
              * ((HM.g s l : ℝ) : ℂ))
      horth hpair' hmemE (hmemT s) hbessel
  refine hmain.trans ?_
  filter_upwards with x
  rw [Work.BoseDict.etaOf, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

end Work.BoseBoxFock
