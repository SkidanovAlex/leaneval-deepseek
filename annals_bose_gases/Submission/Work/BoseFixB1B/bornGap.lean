import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1B.canonicalProfile_concaveOn_Icc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.bornGap` — the STRICT Born gap `8π·a v < ∫ v`

For a nonnegative radial `L¹` potential `v` with compact support (`tsupport v ⊆ ball 0 R`) and a
radial weak scattering solution `w` with `0 < ∫ v·(1−w)` (in particular for the chosen solution,
where `∫ v(1−w) = 8π·a v > 0`), one has `0 < ∫ x, v x * w x`, hence `8π · a v < ∫ x, v x`.

## Why this is needed

`Work.BoseFixB1B.PerBoxSectorBound` (the sector form of FS `thm:smallbox` at the sliding box,
consumed by `Work.BoseFixB1B.perBoxPointwise`) carries the background coefficient `(½ − c)` with
`c > 0`; the balance of the flat state forces `2c ≤ β := (∫v − 8π a v)/(8π a v) = ∫ v·w / (8π a v)`
(see `Submission/Work/BoseFixB1B/FINDING_perBoxSectorBound.md` §2).  The corpus only had the
*non-strict* `8π a v ≤ ∫ v` (`Work.WCrossD2.integral_v_ge_eight_pi_av`); this file supplies the
strict form, so that the residual is consistent with the sharp state family.

## Route

`canonicalProfile v w R r = ½(∫_{0<s≤r} s² γ(s) ds + r·∫_{s>r} s γ(s) ds)` with
`γ = radialProfile (v(1−w))`; since `supp v ⊆ ball 0 R`, `γ` vanishes beyond `R`, so

    `canonicalProfile v w R R = ∫ x, v x(1−w x) / (8π)`,     (`canonicalProfile_at_R_eq`)

using `∫_{ℝ³} G = 4π ∫_{0}^{∞} r² γ(r) dr`.  The exact solution of the Carathéodory ODE
`U'' = (vprof/2)(U − id)` is concave on `[0,R]` (the delegated
`Work.BoseFixB1B.canonicalProfile_concaveOn_Icc`), and `U(0) = 0`, so
`U(r) ≥ (r/R)·U(R) > 0` for `r ∈ (0,R)`.  Since `U r = r·radialProfile w r` for a.e. `r`
(`canonicalProfile_eq_profile`), `w > 0` a.e. on `ball 0 R`, and `v > 0` on a set of positive
measure inside `ball 0 R` (as `v ≠ 0` a.e. and `v ≥ 0`); hence `∫ v·w > 0`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real ENNReal BigOperators

namespace Work.BoseFixB1B

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open _root_.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary support facts -/

/-- `v` vanishes off its topological support. -/
lemma eq_zero_of_notMem_tsupport {v : ℝ³ → ℝ} {x : ℝ³} (hx : x ∉ tsupport v) : v x = 0 := by
  by_contra h
  exact hx (subset_tsupport v (Function.mem_support.mpr h))

/-- The product `v(1−w)` of two radial functions is radial. -/
lemma isRadial_mul_one_sub {v w : ℝ³ → ℝ} (hv : IsRadial v) (hw : IsRadial w) :
    IsRadial (fun x : ℝ³ => v x * (1 - w x)) :=
  fun x y h => by simp only [hv x y h, hw x y h]

/-- **The profile of `v(1−w)` vanishes beyond the range `R`.**  For `s > R` the point `s • radU0`
lies outside `ball 0 R`, hence outside `tsupport v`. -/
lemma radialProfile_mul_one_sub_eq_zero {v w : ℝ³ → ℝ} {R : ℝ} {s : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hR : 0 < R) (hs : R < s) :
    radialProfile (fun x : ℝ³ => v x * (1 - w x)) s = 0 := by
  have hspos : 0 < s := lt_of_le_of_lt hR.le hs
  have hsabs : ‖s • radU0‖ = s := by rw [norm_smul_radU0, abs_of_pos hspos]
  have hnot : s • radU0 ∉ ball (0 : ℝ³) R := by
    rw [mem_ball, dist_zero_right, hsabs]
    exact not_lt.mpr hs.le
  have hzero : v (s • radU0) = 0 := eq_zero_of_notMem_tsupport (fun h => hnot (hv_supp h))
  simp only [radialProfile, hzero, zero_mul]

/-! ## 2. The canonical profile at `R` is the scattering mass over `8π` -/

/-- **The value of the canonical profile at the right endpoint.**  With `γ = radialProfile (v(1−w))`
vanishing beyond `R`, the definition

`U(r) = ½(∫_{0<s≤r} s²γ(s)ds + r∫_{s>r} sγ(s)ds)`

collapses at `r = R` to `½ ∫_{0<s≤R} s²γ(s)ds = ½ ·(∫ v(1−w))/(4π)`, using the polar-coordinate
formula `∫_{ℝ³} G = 4π ∫_0^∞ r² γ(r)dr` for a radial `G`. -/
theorem canonicalProfile_at_R_eq {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hradG : IsRadial (fun x : ℝ³ => v x * (1 - w x)))
    (hint : Integrable (fun x : ℝ³ => v x * (1 - w x))) :
    canonicalProfile v w R R = (8 * π)⁻¹ * ∫ x : ℝ³, v x * (1 - w x) := by
  classical
  set γ : ℝ → ℝ := radialProfile (fun x : ℝ³ => v x * (1 - w x)) with hγ
  have hγ0 : ∀ s : ℝ, R < s → γ s = 0 := by
    intro s hs
    rw [hγ]
    exact radialProfile_mul_one_sub_eq_zero hv_supp hR hs
  -- the a.e. identification of the integrand with `γ ‖·‖`
  have hcongr : (fun x : ℝ³ => v x * (1 - w x)) =ᵐ[volume] (fun x : ℝ³ => γ ‖x‖) := by
    filter_upwards with x
    rw [hγ]
    exact radial_eq_profile hradG x
  have hintOn : IntegrableOn (fun r : ℝ => r ^ 2 * γ r) (Set.Ioi (0 : ℝ)) volume :=
    (integrable_radial_r3 (f := γ)).mp (hint.congr hcongr)
  have hpolar : (∫ x : ℝ³, v x * (1 - w x))
      = 4 * π * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * γ r) := by
    rw [show (∫ x : ℝ³, v x * (1 - w x)) = ∫ x : ℝ³, γ ‖x‖ from by
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [hγ]
      exact radial_eq_profile hradG x]
    exact integral_radial_r3 hintOn
  -- the tail integrals vanish
  have htail : (∫ r in Set.Ioi R, r * γ r) = 0 := by
    rw [show (∫ r in Set.Ioi R, r * γ r) = ∫ r in Set.Ioi R, (0 : ℝ) from
      setIntegral_congr_fun measurableSet_Ioi (fun r hr => by rw [hγ0 r hr, mul_zero])]
    simp
  have htail2 : (∫ r in Set.Ioi R, r ^ 2 * γ r) = 0 := by
    rw [show (∫ r in Set.Ioi R, r ^ 2 * γ r) = ∫ r in Set.Ioi R, (0 : ℝ) from
      setIntegral_congr_fun measurableSet_Ioi (fun r hr => by rw [hγ0 r hr, mul_zero])]
    simp
  -- the split of `Ioi 0`
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) R) (Set.Ioi R) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact absurd hx1.2 (not_le.mpr hx2)
  have hsplit : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * γ r)
      = (∫ r in Set.Ioc (0 : ℝ) R, r ^ 2 * γ r) + (∫ r in Set.Ioi R, r ^ 2 * γ r) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hR.le]
    exact setIntegral_union hdisj measurableSet_Ioi
      (hintOn.mono_set Set.Ioc_subset_Ioi_self) (hintOn.mono_set (Set.Ioi_subset_Ioi hR.le))
  have hIoc : (∫ r in Set.Ioc (0 : ℝ) R, r ^ 2 * γ r)
      = (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * γ r) := by
    rw [hsplit, htail2, add_zero]
  have hUR : canonicalProfile v w R R
      = (1 / 2) * ((∫ r in Set.Ioc (0 : ℝ) R, r ^ 2 * γ r)
          + R * (∫ r in Set.Ioi R, r * γ r)) := rfl
  have hmain : (∫ x : ℝ³, v x * (1 - w x))
      = 8 * π * ((1 / 2) * (∫ r in Set.Ioc (0 : ℝ) R, r ^ 2 * γ r)) := by
    rw [hpolar, ← hIoc]
    ring
  rw [hUR, htail, mul_zero, add_zero, hmain]
  have hpi : (8 * π) ≠ 0 := by positivity
  field_simp

/-! ## 3. `w` is positive a.e. on the ball -/

/-- **The scattering profile is positive almost everywhere on the ball.**  The canonical profile
`U = canonicalProfile v w R` is concave on `[0,R]` (`hconc`), vanishes at `0` and is positive at
`R` (`hUR`), so `U r ≥ (r/R)·U R > 0` for `r ∈ (0,R)`; the a.e. identity `U r = r·γ(r)`
(`canonicalProfile_eq_profile`) then gives `radialProfile w r > 0` for a.e. `r ∈ (0,R)`, and the
radiality of `w` lifts this to `ball 0 R` (the single point `0` being null). -/
theorem scatteringProfile_pos_ae {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v)
    (hconc : ConcaveOn ℝ (Set.Icc 0 R) (canonicalProfile v w R))
    (hUR : 0 < canonicalProfile v w R R) :
    ∀ᵐ x : ℝ³, x ∈ ball (0 : ℝ³) R → 0 < w x := by
  classical
  have hU0 : canonicalProfile v w R 0 = 0 := by
    simp [canonicalProfile]
  -- positivity of the profile on `(0,R)`
  have hUpos : ∀ r : ℝ, 0 < r → r < R → 0 < canonicalProfile v w R r := by
    intro r hr hrR
    have hle := hconc.2 (show (0 : ℝ) ∈ Set.Icc 0 R from ⟨le_refl 0, hR.le⟩)
      (show R ∈ Set.Icc 0 R from ⟨hR.le, le_refl R⟩)
      (show (0 : ℝ) ≤ 1 - r / R by
        rw [sub_nonneg, div_le_one hR]; exact hrR.le)
      (show (0 : ℝ) ≤ r / R by positivity)
      (by ring)
    simp only [smul_eq_mul] at hle
    have harg : r / R * R = r := by field_simp
    rw [hU0, mul_zero, zero_add, harg] at hle
    simp only [zero_add] at hle
    have hpos : 0 < r / R * canonicalProfile v w R R := mul_pos (div_pos hr hR) hUR
    linarith
  -- the bad radii
  have hae := canonicalProfile_eq_profile (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw
  have hN : (volume : Measure ℝ)
      {r : ℝ | ¬ (0 < r → canonicalProfile v w R r = r * radialProfile w r)} = 0 :=
    MeasureTheory.ae_iff.mp hae
  have hSnull : (volume : Measure ℝ)
      {r : ℝ | r ∈ Set.Ioo (0 : ℝ) R ∧ ¬ 0 < radialProfile w r} = 0 := by
    refine measure_mono_null ?_ hN
    intro r hr
    rcases hr with ⟨hrI, hrw⟩
    intro heq
    have hprod : 0 < r * radialProfile w r := by
      rw [← heq hrI.1]
      exact hUpos r hrI.1 hrI.2
    exact hrw ((mul_pos_iff_of_pos_left hrI.1).mp hprod)
  have hpre : (volume : Measure ℝ³)
      {x : ℝ³ | ‖x‖ ∈ {r : ℝ | r ∈ Set.Ioo (0 : ℝ) R ∧ ¬ 0 < radialProfile w r}} = 0 :=
    volume_preimage_norm_null hSnull
  -- conclude
  have hT : (volume : Measure ℝ³) {x : ℝ³ | ¬ (x ∈ ball (0 : ℝ³) R → 0 < w x)} = 0 := by
    refine measure_mono_null ?_ (measure_union_null hpre (measure_singleton (0 : ℝ³)))
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Classical.not_imp] at hx
    rcases hx with ⟨hxb, hxw⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Or.inr rfl
    · refine Or.inl ?_
      have hnorm : ‖x‖ < R := by simpa [mem_ball, dist_zero_right] using hxb
      refine ⟨⟨norm_pos_iff.mpr hx0, hnorm⟩, ?_⟩
      rw [← radial_eq_profile hrad x]
      exact hxw
  filter_upwards [(MeasureTheory.ae_iff (μ := (volume : Measure ℝ³))
    (p := fun x : ℝ³ => x ∈ ball (0 : ℝ³) R → 0 < w x)).mpr hT] with x hx
  exact hx

/-! ## 4. The integral of `v·w` is positive -/

/-- **The Born-gap integral is positive.**  With `v ≥ 0` not a.e. zero and `w > 0` a.e. on
`ball 0 R ⊇ supp v`, the function `v·w` is nonnegative and positive on a set of positive measure.

The integrability of `v·w` is obtained *without* any measurability input on `w`: pointwise
`v·w = v − v(1−w)` and both summands are integrable (`MemLp v 1` and `ScatG.scatG_integrable`). -/
theorem integral_mul_scatteringProfile_pos {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) (hv_ne : ¬ v =ᵐ[volume] 0)
    (hconc : ConcaveOn ℝ (Set.Icc 0 R) (canonicalProfile v w R))
    (hUR : 0 < canonicalProfile v w R R) :
    0 < ∫ x : ℝ³, v x * w x := by
  classical
  obtain ⟨hw0, _hw1⟩ :=
    scattering_bounds_ae (v := v) (w := w) (R := R) hR hv hvrad hv_supp hrad hw
  have hv_int : Integrable v := memLp_one_iff_integrable.mp hv1
  have hg_int : Integrable (fun x : ℝ³ => v x * (1 - w x)) := scatG_integrable hv_supp hw
  have hdiff_int : Integrable (fun x : ℝ³ => v x - v x * (1 - w x)) := hv_int.sub hg_int
  rw [show (∫ x : ℝ³, v x * w x) = ∫ x : ℝ³, (v x - v x * (1 - w x)) from by
    refine integral_congr_ae ?_
    filter_upwards with x
    ring]
  have hnn : 0 ≤ᵐ[volume] (fun x : ℝ³ => v x - v x * (1 - w x)) := by
    filter_upwards [hw0] with x hx
    rw [show v x - v x * (1 - w x) = v x * w x from by ring]
    exact mul_nonneg (hv x) hx
  -- the support of `v·w` has positive measure
  have hwev : ∀ᵐ x : ℝ³, x ∈ ball (0 : ℝ³) R → 0 < w x :=
    scatteringProfile_pos_ae hR hvrad hv_supp hrad hw hconc hUR
  have hNw : (volume : Measure ℝ³) {x : ℝ³ | ¬ (x ∈ ball (0 : ℝ³) R → 0 < w x)} = 0 :=
    (MeasureTheory.ae_iff (μ := (volume : Measure ℝ³))
      (p := fun x : ℝ³ => x ∈ ball (0 : ℝ³) R → 0 < w x)).mp hwev
  have hvpos : 0 < (volume : Measure ℝ³) {x : ℝ³ | 0 < v x} := by
    by_contra hcon
    refine hv_ne ?_
    have hzero : (volume : Measure ℝ³) {x : ℝ³ | 0 < v x} = 0 :=
      le_antisymm (not_lt.mp hcon) bot_le
    refine (MeasureTheory.ae_iff (μ := (volume : Measure ℝ³))
      (p := fun x : ℝ³ => v x = 0)).mpr ?_
    rw [show {x : ℝ³ | ¬ v x = 0} = {x : ℝ³ | 0 < v x} from by
      ext x
      exact ⟨fun hx => lt_of_le_of_ne (hv x) (fun h0 => hx h0.symm),
        fun hx => ne_of_gt hx⟩]
    exact hzero
  have hsubball : {x : ℝ³ | 0 < v x} ⊆ ball (0 : ℝ³) R := by
    intro x hx
    by_contra hxb
    exact absurd (eq_zero_of_notMem_tsupport (fun h => hxb (hv_supp h))) (ne_of_gt hx)
  -- `{0 < v} \ support(v·w)` is null
  have hdiffnull : (volume : Measure ℝ³)
      ({x : ℝ³ | 0 < v x} \ Function.support (fun x : ℝ³ => v x * w x)) = 0 := by
    refine measure_mono_null ?_ hNw
    intro x hx
    rcases hx with ⟨hvx, hxnot⟩
    have hwx0 : w x = 0 := by
      by_contra hne
      exact hxnot (mul_ne_zero (ne_of_gt hvx) hne)
    intro hmem
    have hpos := hmem (hsubball hvx)
    rw [hwx0] at hpos
    exact absurd hpos (lt_irrefl 0)
  have hle : (volume : Measure ℝ³) {x : ℝ³ | 0 < v x}
      ≤ (volume : Measure ℝ³) (Function.support (fun x : ℝ³ => v x * w x)) := by
    calc (volume : Measure ℝ³) {x : ℝ³ | 0 < v x}
        ≤ (volume : Measure ℝ³) (Function.support (fun x : ℝ³ => v x * w x)
            ∪ ({x : ℝ³ | 0 < v x} \ Function.support (fun x : ℝ³ => v x * w x))) :=
          measure_mono (fun x hx => by
            by_cases h : x ∈ Function.support (fun x : ℝ³ => v x * w x)
            · exact Or.inl h
            · exact Or.inr ⟨hx, h⟩)
      _ ≤ (volume : Measure ℝ³) (Function.support (fun x : ℝ³ => v x * w x))
            + (volume : Measure ℝ³)
              ({x : ℝ³ | 0 < v x} \ Function.support (fun x : ℝ³ => v x * w x)) :=
          measure_union_le _ _
      _ = (volume : Measure ℝ³) (Function.support (fun x : ℝ³ => v x * w x)) := by
          rw [hdiffnull, add_zero]
  have hsupp_eq : Function.support (fun x : ℝ³ => v x - v x * (1 - w x))
      = Function.support (fun x : ℝ³ => v x * w x) := by
    ext x
    simp only [Function.mem_support]
    rw [show v x - v x * (1 - w x) = v x * w x from by ring]
  exact (integral_pos_iff_support_of_nonneg_ae hnn hdiff_int).mpr
    (lt_of_lt_of_le hvpos (hsupp_eq ▸ hle))

/-! ## 5. The strict Born gap -/

/-- **The strict Born gap.**  For a nonnegative radial `L¹` potential `v` with `tsupport v ⊆ ball 0 R`
admitting a radial weak scattering solution and with `0 < a v`, the full mass of `v` strictly
exceeds `8π·a v` (equivalently `0 < ∫ v·w = ∫v − 8π·a v > 0`).

This is the strict companion of `Work.WCrossD2.integral_v_ge_eight_pi_av`; it is a *necessary
condition* for `Work.BoseFixB1B.PerBoxSectorBound` (whose background coefficient `½ − c`, `c > 0`,
forces `2c ≤ (∫v − 8π a v)/(8π a v)` in the flat-state balance). -/
theorem bornGap {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (hav : 0 < a v) :
    8 * π * a v < ∫ x : ℝ³, v x := by
  classical
  have hrad : IsRadial (Classical.choose h) := (Classical.choose_spec h).1
  have hw : IsScatteringSolution (Classical.choose h) v := (Classical.choose_spec h).2
  have hg0int : Integrable (fun x : ℝ³ => v x * (1 - Classical.choose h x)) :=
    scatG_integrable hv_supp hw
  have hg0 : (∫ x : ℝ³, v x * (1 - Classical.choose h x)) = 8 * π * a v := by
    simpa [g0] using g0_integral hR hv_supp h
  -- `v` is not a.e. zero
  have hv_ne : ¬ v =ᵐ[volume] 0 := by
    intro h0
    have hz : (∫ x : ℝ³, v x * (1 - Classical.choose h x)) = 0 := by
      rw [show (∫ x : ℝ³, v x * (1 - Classical.choose h x)) = ∫ x : ℝ³, (0 : ℝ) from by
        refine integral_congr_ae ?_
        filter_upwards [h0] with x hx
        simp [hx]]
      simp
    rw [hg0] at hz
    rcases mul_eq_zero.mp hz with h8 | ha
    · exact absurd h8 (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    · exact absurd ha (ne_of_gt hav)
  -- positivity of the canonical profile at `R`
  have hUR : 0 < canonicalProfile v (Classical.choose h) R R := by
    rw [canonicalProfile_at_R_eq hR hv_supp (isRadial_mul_one_sub hvrad hrad) hg0int, hg0]
    have h8pi : (0 : ℝ) < 8 * π := mul_pos (by norm_num) Real.pi_pos
    exact mul_pos (inv_pos.mpr h8pi) (mul_pos h8pi hav)
  have hconc : ConcaveOn ℝ (Set.Icc 0 R) (canonicalProfile v (Classical.choose h) R) :=
    canonicalProfile_concaveOn_Icc (v := v) (w := Classical.choose h) (R := R)
      hR hv hvrad hv_supp hrad hw
  have hpos : 0 < ∫ x : ℝ³, v x * Classical.choose h x :=
    integral_mul_scatteringProfile_pos (v := v) (w := Classical.choose h) (R := R)
      hR hv hv1 hvrad hv_supp hrad hw hv_ne hconc hUR
  -- split the mass of `v`
  have hv_int : Integrable v := memLp_one_iff_integrable.mp hv1
  have hvw_int : Integrable (fun x : ℝ³ => v x * Classical.choose h x) := by
    rw [show (fun x : ℝ³ => v x * Classical.choose h x)
        = fun x : ℝ³ => v x - v x * (1 - Classical.choose h x) from by
      funext x; ring]
    exact hv_int.sub hg0int
  have hsplit : (∫ x : ℝ³, v x)
      = (∫ x : ℝ³, v x * Classical.choose h x)
        + (∫ x : ℝ³, v x * (1 - Classical.choose h x)) := by
    rw [← integral_add hvw_int hg0int]
    refine integral_congr_ae ?_
    filter_upwards with x
    ring
  rw [hsplit, hg0]
  linarith

/-! ## 6. Corollaries -/

/-- **The canonical profile at the right endpoint is the scattering length**:
`canonicalProfile v w₀ R R = a v` for the chosen scattering solution.  (For a general radial
scattering solution this is `∫ v(1−w)/(8π)` by `canonicalProfile_at_R_eq`; for the chosen one that
integral is `a v` by definition.) -/
theorem canonicalProfile_at_R_eq_a {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    canonicalProfile v (Classical.choose h) R R = a v := by
  have hrad : IsRadial (Classical.choose h) := (Classical.choose_spec h).1
  have hw : IsScatteringSolution (Classical.choose h) v := (Classical.choose_spec h).2
  have hg0int : Integrable (fun x : ℝ³ => v x * (1 - Classical.choose h x)) :=
    scatG_integrable hv_supp hw
  rw [canonicalProfile_at_R_eq hR hv_supp (isRadial_mul_one_sub hvrad hrad) hg0int]
  have hg0 : (∫ x : ℝ³, v x * (1 - Classical.choose h x)) = 8 * π * a v := by
    simpa [g0] using g0_integral hR hv_supp h
  rw [hg0, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero), one_mul]

/-- **`∫ v·w > 0` for the chosen scattering solution**, the integral form of the strict Born gap. -/
theorem integral_mul_chosen_pos {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv : 0 ≤ v)
    (hv1 : MemLp v 1) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (hav : 0 < a v) :
    0 < ∫ x : ℝ³, v x * Classical.choose h x := by
  rw [show (∫ x : ℝ³, v x * Classical.choose h x)
      = (∫ x : ℝ³, v x) - (∫ x : ℝ³, v x * (1 - Classical.choose h x)) from by
    rw [← integral_sub (memLp_one_iff_integrable.mp hv1)
      (scatG_integrable hv_supp (Classical.choose_spec h).2)]
    refine integral_congr_ae ?_
    filter_upwards with x
    ring]
  have hg0 : (∫ x : ℝ³, v x * (1 - Classical.choose h x)) = 8 * π * a v := by
    simpa [g0] using g0_integral hR hv_supp h
  rw [hg0]
  linarith [bornGap hR hv hv1 hvrad hv_supp h hav]

/-- **The strict `𝓡`-bound**: `1 < 𝓡 v` whenever `0 < a v` (FS `sec:params` uses `𝓡 v ≥ 1`). -/
theorem one_lt_R {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (hav : 0 < a v) :
    1 < 𝓡 v := by
  have h8a : (0 : ℝ) < 8 * π * a v := mul_pos (by positivity) hav
  have hle := bornGap hR hv hv1 hvrad hv_supp h hav
  have hpoint : (∫ x : ℝ³, v x / (8 * π * a v)) = (∫ x : ℝ³, v x) / (8 * π * a v) :=
    integral_div _ _
  rw [𝓡, hpoint]
  rw [lt_div_iff₀ h8a]
  linarith

end Work.BoseFixB1B
