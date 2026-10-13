import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiaDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A.e. finiteness of the `σ`-slices of a diagonal-energy family

`ae_slice_lintegral_lt_top` is the `L¹`-to-`L^∞`-in-`σ` bridge of the diagonal-energy argument:
from a *uniform-in-`σ`* bound `∫_p (V σ p)² ρ p ≤ K` (for `σ ∈ [0,T]`) it concludes that for a.e.
`p` (with respect to the diagonal measure `diaM = dz dθ` on the quadrant) either `ρ p = 0` or the
`σ`-slice `σ ↦ (V σ p)²` is `lintegral`-finite over the bounded set `Ioc a b`.

The proof is Fubini/Tonelli in *both* orders for the jointly measurable function

`q ↦ ofReal ((V q.1 q.2.1 q.2.2)²) * ofReal (ρ q.2.1 q.2.2)`

on the product `(volume.restrict (Ioc a b)).prod diaM`.  Writing `G p = ∫⁻σ in Ioc a b,
ofReal ((V σ p)²)` and `c p = ofReal (ρ p)`, the two orders of Tonelli give

`∫⁻ p, G p * c p = ∫⁻ σ in Ioc a b, ∫⁻ p, ofReal ((V σ p)²) * c p ≤ ofReal K * vol (Ioc a b) < ⊤`,

where the middle inequality uses the per-`σ` hypothesis `hK` (via
`ofReal_integral_eq_lintegral_ofReal`, which needs the nonnegativity `hρnn`).  Finiteness of that
`lintegral` then forces `G p * c p < ⊤` for a.e. `p` (`ae_lt_top'`), and `G p * c p < ⊤` together
with `0 ≤ ρ p` splits into `ρ p = 0` or `G p < ⊤`.

The point of stating the conclusion a.e. (and with the `ρ p = 0` escape) is that **no**
measurability of the `σ`-slice `σ ↦ V σ p` is assumed — this is exactly the shape in which the
diagonal-energy estimates of the `ε`-scheme supply their data.
-/

namespace Work.FTS.StrongEps.EpsE4Thr

theorem ae_slice_lintegral_lt_top {V : ℝ → Work.FTS.Galerkin.Fn} {ρ : ℝ → ℝ → ℝ}
    {T a b K : ℝ} (hab : a ≤ b)
    (hIoc : Set.Ioc a b ⊆ Set.Icc (0:ℝ) T)
    (hmeasd : AEMeasurable (fun q : ℝ × (ℝ × ℝ) => V q.1 q.2.1 q.2.2)
      (MeasureTheory.volume.prod diaM))
    (hρmeas : AEMeasurable (Function.uncurry ρ) diaM)
    (hρnn : ∀ᵐ p ∂diaM, 0 ≤ ρ p.1 p.2)
    (hdiagd : ∀ σ ∈ Set.Icc (0:ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (V σ p.1 p.2) ^ 2 * ρ p.1 p.2) diaM)
    (hK : ∀ σ ∈ Set.Icc (0:ℝ) T,
      ∫ p : ℝ × ℝ, (V σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM ≤ K) :
    ∀ᵐ p ∂diaM, ρ p.1 p.2 = 0 ∨
      (∫⁻ σ in Set.Ioc a b, ENNReal.ofReal ((V σ p.1 p.2) ^ 2)) < ⊤ := by
  classical
  -- the `σ`-measure is `volume` restricted to the bounded set `Ioc a b`
  have hνle : (MeasureTheory.volume.restrict (Set.Ioc a b)).prod diaM
      ≤ MeasureTheory.volume.prod diaM :=
    MeasureTheory.Measure.prod_mono MeasureTheory.Measure.restrict_le_self le_rfl
  -- joint a.e.-measurability of the two factors of the integrand
  have hVA : AEMeasurable
      (fun q : ℝ × (ℝ × ℝ) => ENNReal.ofReal ((V q.1 q.2.1 q.2.2) ^ 2))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod diaM) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hmeasd.mono_measure hνle).pow_const 2)
  have hCA : AEMeasurable
      (fun q : ℝ × (ℝ × ℝ) => ENNReal.ofReal (ρ q.2.1 q.2.2))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod diaM) := by
    have hm : AEMeasurable (Function.uncurry ρ)
        (((MeasureTheory.volume.restrict (Set.Ioc a b)).prod diaM).map Prod.snd) := by
      rw [MeasureTheory.Measure.map_snd_prod]
      exact hρmeas.smul_measure _
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hm.comp_aemeasurable measurable_snd.aemeasurable)
  have hF : AEMeasurable
      (fun q : ℝ × (ℝ × ℝ) =>
        ENNReal.ofReal ((V q.1 q.2.1 q.2.2) ^ 2) * ENNReal.ofReal (ρ q.2.1 q.2.2))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod diaM) :=
    hVA.mul hCA
  -- the per-`σ` bound, upgraded to a `lintegral` bound
  have hinner : ∀ᵐ σ ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
      (∫⁻ p, ENNReal.ofReal ((V σ p.1 p.2) ^ 2) * ENNReal.ofReal (ρ p.1 p.2) ∂diaM)
        ≤ ENNReal.ofReal K := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with σ hσ
    have hσT : σ ∈ Set.Icc (0 : ℝ) T := hIoc hσ
    have hnn : 0 ≤ᵐ[diaM] fun p : ℝ × ℝ => (V σ p.1 p.2) ^ 2 * ρ p.1 p.2 :=
      hρnn.mono fun p hp => mul_nonneg (sq_nonneg _) hp
    have hmul : (∫⁻ p,
          ENNReal.ofReal ((V σ p.1 p.2) ^ 2) * ENNReal.ofReal (ρ p.1 p.2) ∂diaM)
        = ∫⁻ p, ENNReal.ofReal ((V σ p.1 p.2) ^ 2 * ρ p.1 p.2) ∂diaM :=
      MeasureTheory.lintegral_congr_ae (hρnn.mono fun p hp => by
        show ENNReal.ofReal ((V σ p.1 p.2) ^ 2) * ENNReal.ofReal (ρ p.1 p.2)
          = ENNReal.ofReal ((V σ p.1 p.2) ^ 2 * ρ p.1 p.2)
        rw [mul_comm ((V σ p.1 p.2) ^ 2) (ρ p.1 p.2), ENNReal.ofReal_mul hp]
        exact mul_comm _ _)
    rw [hmul, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hdiagd σ hσT) hnn]
    exact ENNReal.ofReal_le_ofReal (hK σ hσT)
  -- the integral over the product measure is finite
  have hAfin : (∫⁻ σ, (∫⁻ p, ENNReal.ofReal ((V σ p.1 p.2) ^ 2)
        * ENNReal.ofReal (ρ p.1 p.2) ∂diaM)
          ∂(MeasureTheory.volume.restrict (Set.Ioc a b))) < ⊤ := by
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae hinner) ?_
    rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hνfin : (∫⁻ q, ENNReal.ofReal ((V q.1 q.2.1 q.2.2) ^ 2)
        * ENNReal.ofReal (ρ q.2.1 q.2.2)
          ∂(MeasureTheory.volume.restrict (Set.Ioc a b)).prod diaM) < ⊤ := by
    rw [MeasureTheory.lintegral_prod (fun q : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal ((V q.1 q.2.1 q.2.2) ^ 2) * ENNReal.ofReal (ρ q.2.1 q.2.2)) hF]
    exact hAfin
  -- Tonelli, in the order that exhibits the product `G p * c p`
  have hEq : (∫⁻ p, (∫⁻ σ in Set.Ioc a b, ENNReal.ofReal ((V σ p.1 p.2) ^ 2))
          * ENNReal.ofReal (ρ p.1 p.2) ∂diaM)
      = ∫⁻ q, ENNReal.ofReal ((V q.1 q.2.1 q.2.2) ^ 2) * ENNReal.ofReal (ρ q.2.1 q.2.2)
          ∂(MeasureTheory.volume.restrict (Set.Ioc a b)).prod diaM := by
    have h1 : (∫⁻ p, (∫⁻ σ in Set.Ioc a b, ENNReal.ofReal ((V σ p.1 p.2) ^ 2))
            * ENNReal.ofReal (ρ p.1 p.2) ∂diaM)
        = ∫⁻ p, (∫⁻ σ in Set.Ioc a b,
            ENNReal.ofReal ((V σ p.1 p.2) ^ 2) * ENNReal.ofReal (ρ p.1 p.2)) ∂diaM :=
      MeasureTheory.lintegral_congr fun p =>
        (MeasureTheory.lintegral_mul_const' (ENNReal.ofReal (ρ p.1 p.2))
          (fun σ => ENNReal.ofReal ((V σ p.1 p.2) ^ 2)) ENNReal.ofReal_lt_top.ne).symm
    rw [h1]
    exact (MeasureTheory.lintegral_prod_symm (fun q : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal ((V q.1 q.2.1 q.2.2) ^ 2) * ENNReal.ofReal (ρ q.2.1 q.2.2)) hF).symm
  -- a.e. finiteness of the product
  have hmeas : AEMeasurable
      (fun p : ℝ × ℝ => (∫⁻ σ in Set.Ioc a b, ENNReal.ofReal ((V σ p.1 p.2) ^ 2))
        * ENNReal.ofReal (ρ p.1 p.2)) diaM :=
    (AEMeasurable.lintegral_prod_left (f := fun σ (p : ℝ × ℝ) =>
        ENNReal.ofReal ((V σ p.1 p.2) ^ 2) * ENNReal.ofReal (ρ p.1 p.2)) hF).congr
      (Filter.Eventually.of_forall fun p =>
        MeasureTheory.lintegral_mul_const' (ENNReal.ofReal (ρ p.1 p.2))
          (fun σ => ENNReal.ofReal ((V σ p.1 p.2) ^ 2)) ENNReal.ofReal_lt_top.ne)
  have hae := MeasureTheory.ae_lt_top' hmeas (hEq.trans_lt hνfin).ne
  -- split the a.e. statement
  filter_upwards [hae, hρnn] with p hp hρ
  by_cases h0 : ρ p.1 p.2 = 0
  · exact Or.inl h0
  · refine Or.inr (lt_top_iff_ne_top.mpr fun htop => ?_)
    have hpos : 0 < ρ p.1 p.2 := lt_of_le_of_ne hρ (Ne.symm h0)
    have hc : ENNReal.ofReal (ρ p.1 p.2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hpos
    have h2 : (⊤ : ENNReal) * ENNReal.ofReal (ρ p.1 p.2) < ⊤ := by rwa [htop] at hp
    rw [ENNReal.top_mul hc] at h2
    exact absurd h2 (lt_irrefl (⊤ : ENNReal))

end Work.FTS.StrongEps.EpsE4Thr
