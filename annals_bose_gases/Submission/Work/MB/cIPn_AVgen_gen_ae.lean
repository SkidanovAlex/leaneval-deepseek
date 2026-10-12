import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.AVgenDictGen.cIPn_AVgen_gen
import Submission.Work.MB.SlotWeakDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

theorem cIPn_AVgen_gen_ae {m : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → Work.BoseDict.Sp → ℂ}
    (hℓ : 0 < ℓ)
    (heorth : ∀ l l', (∫ x : Work.BoseDict.Sp, (starRingEnd ℂ) (e l x) * e l' x)
      = (if l = l' then (1 : ℂ) else 0))
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (T_NH : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (d : ℕ) (Ψ Ψ' : Work.BoseB4.RealFock m)
    (hΨ : ∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d)
    (hΨ' : ∀ α ∈ Ψ'.support, α.sum (fun _ k => k) = d) :
    Work.BoseDict.cIPn d (Work.BoseDict.boxRealise e d Ψ)
        (Work.BoseBoxFock.AVgen (fun T => Work.BoseDict.boxSlotSum e T)
          (id : (Work.BoseDict.Xn d → ℂ) → (Work.BoseDict.Xn d → ℂ))
          f g T_NH PHs E gHat0 (Work.BoseDict.boxRealise e d Ψ'))
      = ((Work.BoseB4.bomb m Ψ (Work.BoseBoxFock.H2ndF f g (Work.BoseB4.dGamma m T_NH)
          PHs E gHat0 Ψ') : ℝ) : ℂ) := by
  rw [← Work.BoseBoxFock.AVgenDictGen.boxRealise_H2ndF_gen heorth hbdd hsupp
    f g T_NH PHs E gHat0 d Ψ' hΨ']
  exact Work.BoseDict.boxRealise_cIPn_gen heorth hbdd hsupp Ψ
    (Work.BoseBoxFock.H2ndF f g (Work.BoseB4.dGamma m T_NH) PHs E gHat0 Ψ') hΨ

end Work.MB
