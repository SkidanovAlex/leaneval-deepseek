import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.ChWordChains
import Submission.Work.BoseBoxFock.PCFU.lintegral_restrict_shift_le
import Submission.Work.BoseBoxFock.PCFU.prod_restrict_shift_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.integrableOn_abox_W1_shift`

The shifted two-body kernel `|W₁(x_j - x_i + c)|` (`W₁ = W1fun v h ℓ =
wScaled ℓ (g₀ v h)`, FS §4's `W₁ = g/(χ⋆χ)`) is integrable on the `n`-particle
centred box `abox n ℓ = (Λ(ℓ))ⁿ`.

**Route.**  The box volume is the product of the restricted cube volumes
(`Submission.BoseGases.restrict_abox_eq_pi`), and the integrand depends on the
configuration only through the pair `(x i, x j)`.  The pair-evaluation pullback
`Work.BoseBoxFock.PCFU.integrableOn_pair_pullback_abox` therefore reduces the
goal to integrability of the two-variable kernel
`p ↦ |W₁(p.2 - p.1 + c)|` for the product measure
`(volume ↾ acube ℓ).prod (volume ↾ acube ℓ)`.

That reduction is the content of the helper `integrable_prod_restrict_shift`
below: for a finite set `S` of finite Lebesgue measure and any **globally
Lebesgue-integrable** `g`, the composition `p ↦ g (p.2 - p.1 + c)` is integrable
for the product of the two restrictions.  The proof replaces `g` by a measurable
representative `G` (which exists by a.e. strong measurability of an integrable
function) away from a null set: the difference set pulls back to
`{p | p.2 - p.1 + c ∈ s}` with `s` measurable and null, which is null for the
product measure by `prod_restrict_shift_eq_zero` (Fubini + translation
invariance of Lebesgue measure).  Finiteness of the integral is then the
Tonelli/Fubini computation

  `∫⁻ p, ‖G (p.2 - p.1 + c)‖ₑ = ∫⁻ a, ∫⁻ b, ‖G (b - a + c)‖ₑ`
  `≤ ∫⁻ a, ∫⁻ z, ‖G z‖ₑ = (∫⁻ z, ‖G z‖ₑ) * S.univ < ⊤`,

the inner estimate being `lintegral_restrict_shift_le` (restriction to `S`
followed by translation invariance of Lebesgue measure).

Finally `W₁` itself is globally integrable by the corpus's mass bound
`Submission.BoseGases.wScaled_g0_integrable` (`|wScaled| ≤ 2|g₀|` in the dilute
regime `R ≤ ℓ·chiR0`), so the hypothesis of the core lemma is met.

This closes the "shifted `W₁` on the box" integrability leaf used by the PCFU
channel decompositions; the earlier `W1funFarIntegrable` road (a direct
`2R ≤ ℓ` bound) is not needed.
-/

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The measure-theoretic core -/

/-- **Two-variable shift integrability.**  If `S` has finite Lebesgue measure
and `g` is globally Lebesgue-integrable, then `p ↦ g (p.2 - p.1 + c)` is
integrable for the product of the two restrictions of Lebesgue measure to `S`.

The constraint that matters is the *finiteness* of the total mass
(`hSfin`): the `S`-slices are translated copies of (a subset of) `S`, so each
vertical integral is bounded by `∫⁻ ‖g‖ₑ` and the outer integration multiplies
by `volume S`. -/
theorem integrable_prod_restrict_shift {S : Set E3} (hS : MeasurableSet S)
    (hSfin : (volume : Measure E3) S < ⊤) (c : E3) {g : E3 → ℝ} (hg : Integrable g) :
    Integrable (fun p : E3 × E3 => g (p.2 - p.1 + c))
      (((volume : Measure E3).restrict S).prod ((volume : Measure E3).restrict S)) := by
  set ν : Measure E3 := (volume : Measure E3).restrict S with hνdef
  -- a measurable representative of `g`
  set G : E3 → ℝ := hg.1.mk g with hGdef
  have hGm : Measurable G := hg.1.measurable_mk
  have hGae : g =ᵐ[volume] G := hg.1.ae_eq_mk
  -- a measurable null superset of the difference set
  set s : Set E3 := toMeasurable (volume : Measure E3) {x : E3 | g x ≠ G x} with hsdef
  have hsm : MeasurableSet s := measurableSet_toMeasurable _ _
  have hs0 : (volume : Measure E3) s = 0 := by
    rw [hsdef, measure_toMeasurable]
    exact (ae_iff).1 hGae
  have hsub : {x : E3 | g x ≠ G x} ⊆ s := subset_toMeasurable _ _
  -- the two composed functions agree a.e.
  have hEq : (fun p : E3 × E3 => g (p.2 - p.1 + c)) =ᵐ[ν.prod ν]
      (fun p : E3 × E3 => G (p.2 - p.1 + c)) := by
    change ∀ᵐ p ∂(ν.prod ν), g (p.2 - p.1 + c) = G (p.2 - p.1 + c)
    rw [ae_iff]
    refine measure_mono_null ?_ (prod_restrict_shift_eq_zero hS c hsm hs0)
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    by_contra hcon
    exact hp (not_not.mp fun hh => hcon (hsub hh))
  have hGcomp : Measurable (fun p : E3 × E3 => G (p.2 - p.1 + c)) :=
    hGm.comp (by fun_prop)
  have hMeq : (fun p : E3 × E3 => ‖g (p.2 - p.1 + c)‖ₑ) =ᵐ[ν.prod ν]
      (fun p : E3 × E3 => ‖G (p.2 - p.1 + c)‖ₑ) := by
    filter_upwards [hEq] with p hp
    rw [hp]
  have hMG : (∫⁻ z : E3, ‖G z‖ₑ ∂(volume : Measure E3)) < ⊤ := by
    have hGeq : (fun z : E3 => ‖g z‖ₑ) =ᵐ[volume] (fun z : E3 => ‖G z‖ₑ) := by
      filter_upwards [hGae] with z hz
      rw [hz]
    rw [← lintegral_congr_ae hGeq]
    exact hg.2
  have hνtop : ν Set.univ < ⊤ := by
    rw [hνdef, Measure.restrict_apply_univ]
    exact hSfin
  refine ⟨hGcomp.aestronglyMeasurable.congr hEq.symm, ?_⟩
  change (∫⁻ p : E3 × E3, ‖g (p.2 - p.1 + c)‖ₑ ∂(ν.prod ν)) < ⊤
  rw [lintegral_congr_ae hMeq]
  rw [lintegral_prod _ hGcomp.enorm.aemeasurable]
  calc ∫⁻ a, ∫⁻ b, ‖G (b - a + c)‖ₑ ∂ν ∂ν
      ≤ ∫⁻ a, (∫⁻ z, ‖G z‖ₑ ∂(volume : Measure E3)) ∂ν :=
        lintegral_mono (fun a => lintegral_restrict_shift_le hS a c (fun z => ‖G z‖ₑ))
    _ = (∫⁻ z, ‖G z‖ₑ ∂(volume : Measure E3)) * ν Set.univ := lintegral_const _
    _ < ⊤ := ENNReal.mul_lt_top hMG hνtop

/-! ## The box statement -/

theorem integrableOn_abox_W1_shift {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (c : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        |Work.BoseFixR.W1fun v h ℓ (x j - x i + c)|)
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  -- `W₁ = wScaled ℓ (g₀ v h)` is globally integrable in the dilute regime.
  have hW : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => Work.BoseFixR.W1fun v h ℓ z) := by
    have h1 := Submission.BoseGases.wScaled_g0_integrable (v := v) (R := R) (ℓ := ℓ)
      hR hv_supp h hℓ hRℓ
    simpa [Work.BoseFixR.W1fun] using h1
  -- the two-variable kernel is integrable on the square of cubes.
  have hH : Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        |Work.BoseFixR.W1fun v h ℓ (p.2 - p.1 + c)|)
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ))) :=
    (integrable_prod_restrict_shift (S := Submission.BoseGases.acube ℓ)
      (Submission.BoseGases.acube_measurable ℓ)
      (Submission.BoseGases.acube_lt_top ℓ hℓ.le) c hW).abs
  -- peel the two slots out of the product measure.
  exact integrableOn_pair_pullback_abox hℓ hij hH

end Work.BoseBoxFock.PCFU
