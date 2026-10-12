import ChallengeDeps
import Submission.Work.BoseFixB1B.bornGap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.pairMassExcess_pos` — the pair-mass-excess integral is positive

For a nonnegative radial `L¹` potential `v` with `tsupport v ⊆ ball 0 R` (`R > 0`) admitting a
radial weak scattering solution and with `0 < a v`, the pair-mass-excess integral is strictly
positive:

    `0 < ∫ z, v z * (1 − w₀ z) * w₀ z`,   `w₀ := Classical.choose h`.

This is the sharpening of the strict Born gap (`Work.BoseFixB1B.bornGap`, `0 < ∫ v·w₀`) used to
pay the `(½ − c)` background in `Work.BoseFixB1.perSectorBoundG` (`c ≤ γ/2` with
`γ = ∫v(1−ω)ω/(8π a v)`): the *pair* mass excess with the `(1−ω)·ω` weight, not the Born gap
`∫v·ω` (which is `O(λ)` in the weak-coupling limit and therefore useless there).  See
`Submission/Work/BoseFixB1/perSectorBoundG_FINDING.md` §1b.

## Route

Everything is a.e.-nonnegativity plus a support-counting measure argument; no new analysis is
required beyond the corpus's scattering-profile theory.

1. `scattering_bounds_ae` gives `0 ≤ w₀ ≤ 1` a.e.; with `v ≥ 0` the integrand
   `f := v(1−w₀)` and `g := w₀` are a.e. nonnegative, and
   `scat_gomega_integrable` gives integrability of `v(1−w₀)w₀`.
2. `g0_integral` gives `∫ v(1−w₀) = 8π a v > 0`; since `v(1−w₀) ≥ 0` a.e. and is integrable,
   `integral_pos_iff_support_of_nonneg_ae` shows `support (v(1−w₀))` has positive measure.
3. `support (v(1−w₀)) ⊆ tsupport v ⊆ ball 0 R` (where `v = 0` forces `v(1−w₀) = 0`), and
   `scatteringProfile_pos_ae` (concavity of the canonical profile `U(r) = r·ω(r)` at its endpoint
   `U(R) = a v > 0`) gives `w₀ > 0` a.e. on `ball 0 R`.
4. Hence `{v(1−w₀) > 0} ∩ {w₀ > 0}` has positive measure and sits inside the support of
   `v(1−w₀)w₀`; `integral_pos_iff_support_of_nonneg_ae` finishes.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real ENNReal BigOperators

namespace Work.BoseFixB1

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open _root_.BoseGases

set_option linter.unusedVariables false

/-- **The pair-mass excess is positive for any radial scattering solution with positive flux.**
For a radial scattering solution `w` of a nonnegative radial `v` supported in `ball 0 R`, together
with the positive-mass hypothesis `0 < ∫ v(1−w)`, one has `0 < ∫ v(1−w)w`.  (The two extra inputs
`hconc`/`hUR` are the concavity of the canonical profile `U(r) = r·ω(r)` on `[0,R]` and its
strict positivity at `R`, which encode `0 ≤ ω ≤ 1` and `ω > 0` on `ball 0 R`.) -/
theorem pairMassExcess_pos_of_radial {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v)
    (hconc : ConcaveOn ℝ (Set.Icc 0 R) (canonicalProfile v w R))
    (hUR : 0 < canonicalProfile v w R R)
    (hpos : 0 < ∫ z : ℝ³, v z * (1 - w z)) :
    0 < ∫ z : ℝ³, v z * (1 - w z) * w z := by
  classical
  -- a.e. nonnegativity and integrability of the two factors
  have hgnn : 0 ≤ᵐ[volume] (fun z : ℝ³ => v z * (1 - w z)) :=
    scattering_g_nonneg (v := v) (w := w) (R := R) hR hv hvrad hv_supp hrad hw
  have hg_int : Integrable (fun z : ℝ³ => v z * (1 - w z)) :=
    scatG_integrable (v := v) (w := w) (R := R) hv_supp hw
  have hprod_int : Integrable (fun z : ℝ³ => v z * (1 - w z) * w z) :=
    scat_gomega_integrable (v := v) (w := w) (R := R) hv hvrad hv_supp hrad hw
  obtain ⟨hw_nn, _hw_le⟩ :=
    scattering_bounds_ae (v := v) (w := w) (R := R) hR hv hvrad hv_supp hrad hw
  have hprod_nn : 0 ≤ᵐ[volume] (fun z : ℝ³ => v z * (1 - w z) * w z) := by
    filter_upwards [hgnn, hw_nn] with z h1 h2
    exact mul_nonneg h1 h2
  -- positive mass ⇒ `support (v(1−w))` has positive measure
  have hsuppg_pos : 0 < volume (Function.support (fun z : ℝ³ => v z * (1 - w z))) :=
    (integral_pos_iff_support_of_nonneg_ae hgnn hg_int).mp hpos
  -- ... and that support lies in the ball
  have hsuppg_ball :
      Function.support (fun z : ℝ³ => v z * (1 - w z)) ⊆ Metric.ball (0 : ℝ³) R := by
    intro z hz
    have hvz : v z ≠ 0 := fun h0 => hz (by simp [h0])
    exact hv_supp (subset_tsupport v (Function.mem_support.mpr hvz))
  -- `w > 0` a.e. on the ball
  have hwpos : ∀ᵐ z : ℝ³, z ∈ Metric.ball (0 : ℝ³) R → 0 < w z :=
    Work.BoseFixB1B.scatteringProfile_pos_ae (v := v) (w := w) (R := R)
      hR hvrad hv_supp hrad hw hconc hUR
  have hball_null :
      volume ({z : ℝ³ | z ∈ Metric.ball (0 : ℝ³) R} ∩ {z : ℝ³ | ¬ 0 < w z}) = 0 := by
    have hzero : volume {z : ℝ³ | ¬ (z ∈ Metric.ball (0 : ℝ³) R → 0 < w z)} = 0 :=
      (MeasureTheory.ae_iff (μ := (volume : Measure ℝ³))
        (p := fun z : ℝ³ => z ∈ Metric.ball (0 : ℝ³) R → 0 < w z)).mp hwpos
    refine measure_mono_null ?_ hzero
    intro z hz
    exact fun hzb => hz.2 (hzb hz.1)
  -- the set where `v(1−w) < 0` is null
  have hneg_null : volume {z : ℝ³ | v z * (1 - w z) < 0} = 0 := by
    have hzero : volume {z : ℝ³ | ¬ (0 ≤ v z * (1 - w z))} = 0 :=
      (MeasureTheory.ae_iff (μ := (volume : Measure ℝ³))
        (p := fun z : ℝ³ => 0 ≤ v z * (1 - w z))).mp hgnn
    refine measure_mono_null ?_ hzero
    intro z hz
    exact not_le.mpr hz
  -- so `{v(1−w) > 0}` has positive measure
  have hE_pos : 0 < volume {z : ℝ³ | 0 < v z * (1 - w z)} := by
    have hsub : Function.support (fun z : ℝ³ => v z * (1 - w z))
        ⊆ {z : ℝ³ | 0 < v z * (1 - w z)} ∪ {z : ℝ³ | v z * (1 - w z) < 0} := by
      intro z hz
      rcases lt_trichotomy (v z * (1 - w z)) 0 with hlt | heq | hgt
      · exact Or.inr hlt
      · exact absurd heq hz
      · exact Or.inl hgt
    have hle : volume (Function.support (fun z : ℝ³ => v z * (1 - w z)))
        ≤ volume {z : ℝ³ | 0 < v z * (1 - w z)} :=
      calc volume (Function.support (fun z : ℝ³ => v z * (1 - w z)))
          ≤ volume ({z : ℝ³ | 0 < v z * (1 - w z)}
              ∪ {z : ℝ³ | v z * (1 - w z) < 0}) := measure_mono hsub
        _ ≤ volume {z : ℝ³ | 0 < v z * (1 - w z)}
              + volume {z : ℝ³ | v z * (1 - w z) < 0} := measure_union_le _ _
        _ = volume {z : ℝ³ | 0 < v z * (1 - w z)} := by rw [hneg_null, add_zero]
    exact lt_of_lt_of_le hsuppg_pos hle
  have hE_ball : {z : ℝ³ | 0 < v z * (1 - w z)} ⊆ Metric.ball (0 : ℝ³) R := by
    intro z hz
    exact hsuppg_ball (Function.mem_support.mpr (ne_of_gt hz))
  -- intersecting with `{w > 0}` keeps it of positive measure
  have hT_pos : 0 < volume ({z : ℝ³ | 0 < v z * (1 - w z)} ∩ {z : ℝ³ | 0 < w z}) := by
    have hsub : {z : ℝ³ | 0 < v z * (1 - w z)}
        ⊆ ({z : ℝ³ | 0 < v z * (1 - w z)} ∩ {z : ℝ³ | 0 < w z})
          ∪ ({z : ℝ³ | z ∈ Metric.ball (0 : ℝ³) R} ∩ {z : ℝ³ | ¬ 0 < w z}) := by
      intro z hz
      by_cases hwz : 0 < w z
      · exact Or.inl ⟨hz, hwz⟩
      · exact Or.inr ⟨hE_ball hz, hwz⟩
    have hle : volume {z : ℝ³ | 0 < v z * (1 - w z)}
        ≤ volume ({z : ℝ³ | 0 < v z * (1 - w z)} ∩ {z : ℝ³ | 0 < w z}) :=
      calc volume {z : ℝ³ | 0 < v z * (1 - w z)}
          ≤ volume (({z : ℝ³ | 0 < v z * (1 - w z)} ∩ {z : ℝ³ | 0 < w z})
              ∪ ({z : ℝ³ | z ∈ Metric.ball (0 : ℝ³) R} ∩ {z : ℝ³ | ¬ 0 < w z})) :=
            measure_mono hsub
        _ ≤ volume ({z : ℝ³ | 0 < v z * (1 - w z)} ∩ {z : ℝ³ | 0 < w z})
              + volume ({z : ℝ³ | z ∈ Metric.ball (0 : ℝ³) R}
                  ∩ {z : ℝ³ | ¬ 0 < w z}) := measure_union_le _ _
        _ = volume ({z : ℝ³ | 0 < v z * (1 - w z)} ∩ {z : ℝ³ | 0 < w z}) := by
            rw [hball_null, add_zero]
    exact lt_of_lt_of_le hE_pos hle
  -- which sits inside the support of the product
  have hT_sub :
      ({z : ℝ³ | 0 < v z * (1 - w z)} ∩ {z : ℝ³ | 0 < w z})
        ⊆ Function.support (fun z : ℝ³ => v z * (1 - w z) * w z) := by
    intro z hz
    exact Function.mem_support.mpr (mul_ne_zero (ne_of_gt hz.1) (ne_of_gt hz.2))
  have hprod_supp_pos :
      0 < volume (Function.support (fun z : ℝ³ => v z * (1 - w z) * w z)) :=
    lt_of_lt_of_le hT_pos (measure_mono hT_sub)
  exact (integral_pos_iff_support_of_nonneg_ae hprod_nn hprod_int).mpr hprod_supp_pos

/-- **The pair-mass excess at the chosen scattering solution is positive.**  Equivalently: the
`(1−ω)ω`-weighted mass `∫ v(1−ω)ω` — the payer of the `(½ − c)` background in the per-sector
residual — never vanishes; the relevant parameter `γ = ∫v(1−ω)ω/(8π a v)` is strictly positive. -/
theorem pairMassExcess_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (hav : 0 < _root_.BoseGases.a v) :
    0 < ∫ z : EuclideanSpace ℝ (Fin 3),
      v z * (1 - Classical.choose h z) * Classical.choose h z := by
  classical
  obtain ⟨hrad, hw⟩ := Classical.choose_spec h
  -- concavity of the canonical profile and its value `a v > 0` at the right endpoint
  have hconc := Work.BoseFixB1B.canonicalProfile_concaveOn_Icc (v := v) (w := Classical.choose h)
    (R := R) hR hv hvrad hv_supp hrad hw
  have hUR : 0 < canonicalProfile v (Classical.choose h) R R := by
    rw [Work.BoseFixB1B.canonicalProfile_at_R_eq_a (v := v) (R := R) hR hvrad hv_supp h]
    exact hav
  -- the scattering mass `∫ v(1−w₀) = 8π a v > 0`
  have hpos : 0 < ∫ z : EuclideanSpace ℝ (Fin 3), v z * (1 - Classical.choose h z) := by
    have hval : (∫ z : EuclideanSpace ℝ (Fin 3), v z * (1 - Classical.choose h z))
        = 8 * Real.pi * _root_.BoseGases.a v := by
      simpa only [Submission.BoseGases.g0] using
        Submission.BoseGases.g0_integral (v := v) (R := R) hR hv_supp h
    rw [hval]
    exact mul_pos (by positivity) hav
  exact pairMassExcess_pos_of_radial (v := v) (w := Classical.choose h) (R := R)
    hR hv hvrad hv_supp hrad hw hconc hUR hpos

end Work.BoseFixB1
