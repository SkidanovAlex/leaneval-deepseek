import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SboxEB
import Submission.Work.SmallBoxA0.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Pullback of a pair kernel to the small box

For a kernel `w` on the pair cube `Λ(s) × Λ(s)` (`Λ(s) = acube s`, the centred cube of
side `s`), the function `x ↦ w (x i, x j)` on the `(p+2)`-particle centred box `abox (p+2) s`
is integrable, and its integral is `(s³)^p` times the pair integral:
the `p` remaining coordinates are integrated out of the box, each contributing a factor
`vol (acube s) = s³`.

The proof peels the two distinguished slots `i`, `j` out of the box integral
(`Submission.BoseGases.abox_integral_peel2`), evaluates the inserted configuration
(`kc_insN_apply_same` / `kc_insN_apply_succ`), applies Fubini on the product cube
(`Submission.BoseGases.prod_setIntegral_eq_iter2_ae`) and integrates the constant over the
remaining `p`-particle box.
-/

namespace Work.SmallBoxA0

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Integral of a constant over the `N`-particle centred box: `c · (ℓ³)^N`. -/
lemma integral_const_abox_centred (N : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) (c : ℝ) :
    (∫ _x in Submission.BoseGases.abox N ℓ, c) = c * (ℓ ^ 3) ^ N := by
  have h1 : (∫ _x in Submission.BoseGases.abox N ℓ, c)
      = (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)).real Set.univ) • c := by
    simpa using (MeasureTheory.integral_const
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) (c := c))
  rw [h1, MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply_univ]
  rw [Submission.BoseGases.abox_volume N ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul]
  ring

lemma pair_pullback_integrable {p : ℕ} {s : ℝ} (hs : 0 < s) (i j : Fin (p + 2)) (hij : i ≠ j)
    {w : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwm : MeasureTheory.AEStronglyMeasurable w
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s)))
    (hwi : MeasureTheory.IntegrableOn w
      (Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s) MeasureTheory.volume) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (p + 2) => w (x i, x j))
      (Submission.BoseGases.abox (p + 2) s) MeasureTheory.volume ∧
    (∫ x in Submission.BoseGases.abox (p + 2) s, w (x i, x j))
      = (s ^ 3) ^ p * ∫ q in Submission.BoseGases.acube s ×ˢ Submission.BoseGases.acube s, w q := by
  have hint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (p + 2) => w (x i, x j))
      (Submission.BoseGases.abox (p + 2) s) MeasureTheory.volume :=
    Submission.BoseGases.integrableOn_pair_comp_ae hs i j hij hwi
  refine ⟨hint, ?_⟩
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
  have hpeel := Submission.BoseGases.abox_integral_peel2 (p := p) (ℓ := s) i j'
    (F := fun x : Submission.BoseGases.X (p + 2) => w (x i, x j)) hint
  rw [hpeel]
  have hpt : ∀ (r2 : Submission.BoseGases.X p) (y z : ℝ³),
      w (((Submission.BoseGases.kcInsN (p + 1) i)
            (y, (Submission.BoseGases.kcInsN p j') (z, r2))) i,
         ((Submission.BoseGases.kcInsN (p + 1) i)
            (y, (Submission.BoseGases.kcInsN p j') (z, r2))) j)
        = w (y, z) := by
    intro r2 y z
    have hY : ((Submission.BoseGases.kcInsN (p + 1) i)
        (y, (Submission.BoseGases.kcInsN p j') (z, r2))) i = y :=
      Submission.BoseGases.kc_insN_apply_same (p + 1) i y
        ((Submission.BoseGases.kcInsN p j') (z, r2))
    have hZ : ((Submission.BoseGases.kcInsN (p + 1) i)
        (y, (Submission.BoseGases.kcInsN p j') (z, r2))) j = z := by
      rw [← hj']
      exact (Submission.BoseGases.kc_insN_apply_succ (p + 1) i y
          ((Submission.BoseGases.kcInsN p j') (z, r2)) j').trans
        (Submission.BoseGases.kc_insN_apply_same p j' z r2)
    rw [hY, hZ]
  simp only [hpt]
  rw [integral_const_abox_centred p s hs]
  rw [Submission.BoseGases.prod_setIntegral_eq_iter2_ae hwi]
  ring

end Work.SmallBoxA0
