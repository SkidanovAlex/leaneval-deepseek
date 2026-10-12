import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.slotSum_sectorPointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-! ## Two elementary ingredients

The slice of a sector is the section `u ↦ Θ (pairCoord S u y)` of the sector state
`Θ = slotExact e S Φ` along the slot splitting of the configuration space
(`MeasurableEquiv.piEquivPiSubtypeProd`, whose inverse is `pairCoord`).  Two facts are needed:

* the section of a bounded measurable compactly supported function is (a.e. in `y`) square
  integrable — this is the a.e.-`Integrable` conjunct of `sliceFubini`, proved here for the
  squared norm (kept `ℂ`-valued so that no real/complex coercion is involved);
* a nonnegative function with vanishing integral vanishes a.e.; an a.e. zero slice then already
  kills the quadratic form, because its integrand carries the factor `star (slice u)`. -/

/-- The squared norm as a norm of a product, `‖star z * z‖ = ‖z‖ ^ 2` (the `ℂ`-valued
counterpart of `(star z * z).re = ‖z‖ ^ 2`). -/
private lemma norm_star_mul_self (z : ℂ) : ‖star z * z‖ = ‖z‖ ^ 2 := by
  rw [norm_mul, norm_star]
  ring

/-- **For a.e. complement configuration `y`, the slice's squared-norm integrand is
integrable.**  This is the a.e.-`Integrable` content of the Fubini splitting of the sector's mass
along the slot splitting `MeasurableEquiv.piEquivPiSubtypeProd`. -/
theorem ae_integrable_sectorSlice_normSq {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (S : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΘm : Measurable (slotExact e S Φ))
    (hΘb : ∃ C, ∀ x, ‖slotExact e S Φ x‖ ≤ C)
    (hΘc : HasCompactSupport (slotExact e S Φ)) :
    ∀ᵐ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
      MeasureTheory.Integrable (fun u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3) =>
        ‖sectorSlice e S Φ y u‖ ^ 2) := by
  classical
  -- the full-space squared-norm integrand of the sector is integrable
  have hFint : MeasureTheory.Integrable (fun x : Fin n → EuclideanSpace ℝ (Fin 3) =>
      star (slotExact e S Φ x) * slotExact e S Φ x) :=
    integrable_mul_of_hasCompactSupport_of_bounded
      (hΘc.comp_left (g := star) (by simp)) (measurable_star_comp hΘm).aestronglyMeasurable
      (hΘb.imp (fun C hC x => by rw [norm_star]; exact hC x)) hΘm.aestronglyMeasurable hΘb
  -- hence, after the measure-preserving slot splitting, it is integrable on the product
  have hFi : MeasureTheory.Integrable
      (fun q : ({i // i ∈ S} → EuclideanSpace ℝ (Fin 3))
        × ({i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) =>
        star (slotExact e S Φ (pairCoord S q.1 q.2))
          * slotExact e S Φ (pairCoord S q.1 q.2)) :=
    integrable_pairCoord_comp S _ hFint
  -- and its sections at a.e. `y` are integrable; take norms
  filter_upwards [MeasureTheory.Integrable.prod_left_ae hFi] with y hy
  refine hy.norm.congr (Filter.Eventually.of_forall (fun u => ?_))
  exact norm_star_mul_self (sectorSlice e S Φ y u)

/-- **A slice whose mass integral vanishes vanishes a.e.** -/
theorem sectorSlice_mass_eq_zero_ae {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (S : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3))
    (hint : MeasureTheory.Integrable (fun u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3) =>
      ‖sectorSlice e S Φ y u‖ ^ 2))
    (h0 : (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
      ‖sectorSlice e S Φ y u‖ ^ 2) = 0) :
    (fun u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3) => sectorSlice e S Φ y u)
      =ᵐ[MeasureTheory.volume] 0 := by
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume]
      (fun u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3) => ‖sectorSlice e S Φ y u‖ ^ 2) :=
    Filter.Eventually.of_forall (fun u => sq_nonneg _)
  have hz := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp h0
  filter_upwards [hz] with u hu
  have hu' : ‖sectorSlice e S Φ y u‖ ^ 2 = 0 := hu
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (sectorSlice e S Φ y u)])

/-- **The slice form vanishes where the slice mass vanishes (a.e. in the complement
configuration).**  For orthonormal modes `e`, a one-body slot sum `T`, a sector `S` and a compactly
supported continuous state `Φ`, for almost every complement configuration `y`, the vanishing of the
slice's mass `∫_u ‖sectorSlice e S Φ y u‖²` forces the vanishing of the slice's quadratic form
`∫_u (star (sectorSlice e S Φ y u) * slotSumSub e T S (sectorSlice e S Φ y) u).re`.

This is the `hq0` hypothesis of the fibre selection.

Proof route: `slotExact e S Φ` is measurable, bounded and compactly supported
(`slotExact_measurable_bounded_compactSupport`); `integrable_pairCoord_comp` +
`Integrable.prod_left_ae` give, for a.e. `y`, the integrability of `u ↦ ‖sectorSlice e S Φ y u‖²`
(rewrite `(star z * z).re = ‖z‖²` by `star_mul_re_eq_normSq`); then
`integral_eq_zero_iff_of_nonneg_ae` turns `∫_u ‖slice‖² = 0` into `slice =ᵐ 0`, and
`integral_congr_ae` turns the form integrand into `0` a.e. (the factor `star (slice u)` already
vanishes wherever `slice u` does; no property of `slotSumSub` is used). -/
theorem sliceQZeroAe {m n : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (S : Finset (Fin n)) (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    ∀ᵐ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
      (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
          ‖Work.BoseBoxFock.sectorSlice e S Φ y u‖ ^ 2) = 0 →
      (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
          (star (Work.BoseBoxFock.sectorSlice e S Φ y u)
            * Work.BoseBoxFock.slotSumSub e T S (Work.BoseBoxFock.sectorSlice e S Φ y) u).re) = 0 := by
  classical
  obtain ⟨hΘm, hΘb, hΘc⟩ := slotExact_measurable_bounded_compactSupport e he hec S Φ hΦ hΦc
  filter_upwards [ae_integrable_sectorSlice_normSq e S Φ hΘm hΘb hΘc] with y hInt
  intro hmass
  -- the slice vanishes a.e. in `u`
  have hslice := sectorSlice_mass_eq_zero_ae e S Φ y hInt hmass
  -- hence so does the form integrand, whose first factor is `star` of the slice
  have hz : (fun u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3) =>
      (star (Work.BoseBoxFock.sectorSlice e S Φ y u)
        * Work.BoseBoxFock.slotSumSub e T S (Work.BoseBoxFock.sectorSlice e S Φ y) u).re)
      =ᵐ[MeasureTheory.volume] 0 := by
    filter_upwards [hslice] with u hu
    have hu' : sectorSlice e S Φ y u = 0 := hu
    rw [hu']
    simp
  rw [MeasureTheory.integral_congr_ae hz]
  simp

end Work.BoseBoxFock
