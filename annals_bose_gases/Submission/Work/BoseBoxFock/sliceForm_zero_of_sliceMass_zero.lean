import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.aeIntegrableSectorSlice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sliceForm_zero_of_sliceMass_zero`

The BF3c fibre selection consumes the slice `sectorSlice e S Φ y u = slotExact e S Φ (pairCoord S u y)`
of the `S`-sector `Θ = slotExact e S Φ` of a state `Φ` at a complement configuration `y`
(`sectorSliceDefs.lean`).  This lemma is the *degenerate* case of the pointwise decoupling: if the
slice has vanishing mass `∫_u ‖sectorSlice e S Φ y u‖² = 0`, then *every* sesquilinear form of the
slice against an arbitrary slot operator `OpS S (sectorSlice e S Φ y)` integrates to `0`:

    ∫_u Re(conj(slice_u) · (OpS S slice)_u) = 0 .

No hypothesis on `OpS` is needed: the content is entirely in the left factor.

## The argument

For almost every `y` the map `u ↦ ‖sectorSlice e S Φ y u‖²` is **integrable**.  Indeed `e l` is
continuous with compact support and `Φ` is continuous with compact support, so the sector
`Θ = slotExact e S Φ` is measurable, bounded and compactly supported
(`slotExact_measurable_bounded_compactSupport`), whence its slice — the composition of `Θ` with the
projection `x ↦ (x i)_{i ∈ S}`, which kills `u` outside the compact image of `tsupport Θ` — is
compactly supported in `u` and bounded; this is `aeIntegrableSectorSlice` (which in fact proves it
for every `y`).

With integrability in hand, the nonnegative function `u ↦ ‖sectorSlice e S Φ y u‖²` has vanishing
Bochner integral iff it vanishes almost everywhere
(`integral_eq_zero_iff_of_nonneg`), i.e. `sectorSlice e S Φ y = 0` a.e. in `u`.  Pointwise at every
`u` in that conull set the integrand of the assertion is `Re(conj 0 · _) = 0` (whatever the operator
does), so the integrand is a.e. `0` and its integral vanishes by `integral_congr_ae`.

Note where the compact support of `e`/`Φ` is *used*: without it the slice could be a continuous
non-integrable nonzero function, for which the hypothesis `∫ ‖·‖² = 0` holds only as the junk value
of a non-integrable Bochner integral.  `aeIntegrableSectorSlice` is exactly the bridge that excludes
this.

## Main declarations

* `Work.BoseBoxFock.integral_re_star_mul_eq_zero_of_ae_eq_zero` — the measure-theoretic skeleton:
  an a.e. vanishing left slot makes the sesquilinear form integrate to `0`, for an arbitrary right
  slot (no measurability of the right slot required);
* `Work.BoseBoxFock.ae_sectorSlice_eq_zero_of_integral_normSq_eq_zero` — the vanishing of the slice
  from the vanishing of its mass, for a.e. complement configuration;
* `Work.BoseBoxFock.sliceForm_zero_of_sliceMass_zero` — the target.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- **Vanishing sesquilinear form from an a.e. vanishing left slot.**  If `g` vanishes almost
everywhere then so does the integrand `x ↦ Re(conj (g x) · h x)`, for *any* right slot `h`
(no measurability, boundedness or integrability of `h` is needed: a.e. the product is `0`, and the
Bochner integral is insensitive to the values on the null set where `g ≠ 0`). -/
lemma integral_re_star_mul_eq_zero_of_ae_eq_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g h : α → ℂ} (hg : g =ᵐ[μ] 0) :
    ∫ x, (star (g x) * h x).re ∂μ = 0 := by
  have hF : (fun x => (star (g x) * h x).re) =ᵐ[μ] 0 := by
    filter_upwards [hg] with x hx
    rw [hx]
    simp
  rw [integral_congr_ae hF]
  simp

/-- **The slice vanishes a.e. when its mass vanishes.**  For almost every complement configuration
`y`, a vanishing squared-norm integral `∫_u ‖sectorSlice e S Φ y u‖² = 0` forces the slice to be
zero almost everywhere in the sector variables `u`.

The regularity of `e` and `Φ` (continuity and compact support) enters through
`slotExact_measurable_bounded_compactSupport`, which makes the slice bounded and compactly
supported and hence its squared norm integrable — the hypothesis on the integral is otherwise only
the junk value `0` of a non-integrable Bochner integral. -/
lemma ae_sectorSlice_eq_zero_of_integral_normSq_eq_zero {m n : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hcont : ∀ l, Continuous (e l)) (hcomp : ∀ l, HasCompactSupport (e l))
    (S : Finset (Fin n))
    (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) :
    ∀ᵐ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
      (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
        ‖Work.BoseBoxFock.sectorSlice e S Φ y u‖ ^ 2) = 0 →
      Work.BoseBoxFock.sectorSlice e S Φ y =ᵐ[volume] 0 := by
  obtain ⟨hm, hb, hc⟩ :=
    slotExact_measurable_bounded_compactSupport e hcont hcomp S Φ hΦ hΦc
  filter_upwards [aeIntegrableSectorSlice e S Φ hm hb hc] with y hy
  intro h
  have hz : (fun u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3) =>
      ‖Work.BoseBoxFock.sectorSlice e S Φ y u‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) hy).mp h
  filter_upwards [hz] with u hu
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hu)

theorem sliceForm_zero_of_sliceMass_zero {m n : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hcont : ∀ l, Continuous (e l)) (hcomp : ∀ l, HasCompactSupport (e l))
    (S : Finset (Fin n))
    (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ)
    (OpS : (S : Finset (Fin n)) → (({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ)
      → (({i // i ∈ S} → EuclideanSpace ℝ (Fin 3)) → ℂ)) :
    ∀ᵐ y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3),
      (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
        ‖Work.BoseBoxFock.sectorSlice e S Φ y u‖ ^ 2) = 0 →
      (∫ u : {i // i ∈ S} → EuclideanSpace ℝ (Fin 3),
          (star (Work.BoseBoxFock.sectorSlice e S Φ y u)
            * OpS S (Work.BoseBoxFock.sectorSlice e S Φ y) u).re) = 0 := by
  filter_upwards [ae_sectorSlice_eq_zero_of_integral_normSq_eq_zero e hcont hcomp S Φ hΦ hΦc]
    with y hy
  intro h
  exact integral_re_star_mul_eq_zero_of_ae_eq_zero (hy h)

end Work.BoseBoxFock
