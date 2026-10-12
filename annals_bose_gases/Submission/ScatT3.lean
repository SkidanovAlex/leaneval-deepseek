import ChallengeDeps
import Submission.T3Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 3, T3 in chosen form: `0 ≤ ω ≤ 1` a.e., `0 < a v ≤ R`, `g ≥ 0` a.e.

With the maximum-principle bounds on the canonical scattering profile
(`T3Bounds.canonicalProfile_nonneg` / `canonicalProfile_le_r`:
`0 ≤ U(r) ≤ r` for `0 < r < R`) and its a.e. identity with the scattering
profile (`ProfileFormula.canonicalProfile_eq_profile`:
`U(r) = r·radialProfile w r` for a.e. `r > 0`), we obtain for a radial weak
scattering solution `w` of a non-negative radial `v` (`tsupport v ⊆ ball 0 R`)
the a.e. radial-profile bounds `0 ≤ radialProfile w r ≤ 1` for a.e. `r > 0`
and hence, by radiality, the 3D bounds `0 ≤ w ≤ 1` a.e. on `ℝ³`.

For the **chosen** scattering solution `w₀` of the `a v ≠ 0` branch
(`h : ∃w, IsRadial w ∧ IsScatteringSolution w v`), additionally:
* the exterior value is `a v` (`ScatChosen.chosen_scattering_av_exterior`:
  `w₀ x = a v/‖x‖` a.e. for `‖x‖ ≥ R`), so with the bounds one gets
  `0 ≤ a v ≤ R` (the value at `r = R`, `a v = U(R)`, lies between `0` and `R`
  by continuity and the bounds on `(0,R)`);
* `g := v(1−w₀)` is non-negative a.e. (`0 ≤ v` pointwise, `w₀ ≤ 1` a.e. on
  the support of `v` — which is contained in `ball 0 R`).

These are exactly the scattering facts T3 of the Layer-3 targets (in the
chosen form) that the box bound (`hbox`) needs.

## Route
1. **Radial-profile bounds.**  On `(0,R)`: for a.e. `r`,
   `u(r) := r·radialProfile w r = canonicalProfile v w R r ∈ [0, r]`
   (a.e. equality + pointwise bounds), so
   `0 ≤ radialProfile w r ≤ 1` for a.e. `r ∈ (0,R)`.
   Beyond `R`: `u ≡ c` (`canonicalProfile_const_beyond`, with `c` the exterior
   constant of `w`), and `0 ≤ c ≤ R` by continuity (`c = U(R)` and
   `0 ≤ U(r) ≤ r` on `(0,R)`); hence `radialProfile w r = c/r ∈ [0,1]` for
   all `r ≥ R`.  So `0 ≤ radialProfile w r ≤ 1` for a.e. `r > 0`.
2. **3D lift.**  `w x = radialProfile w ‖x‖` (radiality), and the set of bad
   radii is null; the norm-preimage of a null set of radii is null
   (`volume_preimage_norm_null`, `ScatProfileExterior`), giving
   `∀ᵐ x, 0 ≤ w x ∧ w x ≤ 1`.  (The sphere `{x | ‖x‖ = R}` is null, so the
   split at `R` causes no difficulty.)
3. **Chosen corollaries.**  `w₀ ≤ 1` a.e. & exterior form give `a v ≤ R`
   (from `w₀ x ≤ 1` at radii `r = R` and `w₀ x = a v/r`); `0 ≤ a v` from
   `w₀ ≥ 0` a.e. similarly.  `g = v(1−w₀) ≥ 0` a.e. on `{v ≠ 0}` (there
   `w₀ ≤ 1` a.e. and `v ≥ 0`) and `= 0` off `supp v`.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


/-- The canonical profile is non-negative at the right endpoint `R`
(`0 ≤ U(r) ≤ r` on `(0,R)` extends to `r = R` by right-continuity). -/
lemma canonicalProfile_nonneg_at_R {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    0 ≤ canonicalProfile v w R R := by
  let U : ℝ → ℝ := canonicalProfile v w R
  have hUtend : Tendsto U (𝓝[<] R) (𝓝 (U R)) := by
    have hc : ContinuousAt U R := by
      simpa [U] using (canonicalProfile_hasDerivAt_R (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw).continuousAt
    exact hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] R ≤ 𝓝 R)
  have hEv : ∀ᶠ r in 𝓝[<] R, (0 : ℝ) ≤ U r := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (half_lt_self hR)] with r hr2
    intro hrR
    have hr0 : 0 < r := lt_trans (half_pos hR) hr2
    simpa [U] using canonicalProfile_nonneg hR hv_nonneg hvrad hv_supp hrad hw r hr0 hrR
  exact le_of_tendsto_of_tendsto (b := 𝓝[<] R) (f := fun _ : ℝ => (0 : ℝ)) (g := U)
    tendsto_const_nhds hUtend hEv

/-- The canonical profile is at most `r` at the right endpoint `R`
(`0 ≤ U(r) ≤ r` on `(0,R)` extends to `r = R` by right-continuity). -/
lemma canonicalProfile_le_r_at_R {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    canonicalProfile v w R R ≤ R := by
  let U : ℝ → ℝ := canonicalProfile v w R
  have hUtend : Tendsto U (𝓝[<] R) (𝓝 (U R)) := by
    have hc : ContinuousAt U R := by
      simpa [U] using (canonicalProfile_hasDerivAt_R (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw).continuousAt
    exact hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] R ≤ 𝓝 R)
  have hidTend : Tendsto id (𝓝[<] R) (𝓝 R) := by
    exact (continuousAt_id : ContinuousAt id R).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] R ≤ 𝓝 R)
  have hEv : ∀ᶠ r in 𝓝[<] R, U r ≤ r := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (half_lt_self hR)] with r hr2
    intro hrR
    have hr0 : 0 < r := lt_trans (half_pos hR) hr2
    simpa [U] using canonicalProfile_le_r hR hv_nonneg hvrad hv_supp hrad hw r hr0 hrR
  have h := le_of_tendsto_of_tendsto (b := 𝓝[<] R) (f := U) (g := id) hUtend hidTend hEv
  simpa using h

/-- The radial profile of a radial weak scattering solution `w` of a
non-negative radial `v` (`tsupport v ⊆ ball 0 R`) is bounded by `0` and `1`
for almost every radius `r > 0`. -/
lemma radialProfile_bounds_ae {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    ∀ᵐ r : ℝ, 0 < r → 0 ≤ radialProfile w r ∧ radialProfile w r ≤ 1 := by
  classical
  rcases scattering_solution_exterior_form (w := w) (v := v) (R := R) hR hrad hw hv_supp with ⟨c, hform⟩
  let U : ℝ → ℝ := canonicalProfile v w R
  have hUc : ∀ r : ℝ, R ≤ r → U r = c := by
    intro r hr
    exact canonicalProfile_const_beyond (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw
      (c := c) hform r hr
  have hc0 : 0 ≤ c := by
    have h := canonicalProfile_nonneg_at_R hR hv_nonneg hvrad hv_supp hrad hw
    change 0 ≤ U R at h
    rw [hUc R le_rfl] at h
    exact h
  have hcR : c ≤ R := by
    have h := canonicalProfile_le_r_at_R hR hv_nonneg hvrad hv_supp hrad hw
    change U R ≤ R at h
    rw [hUc R le_rfl] at h
    exact h
  let prof : ℝ → ℝ := radialProfile w
  have hEq : ∀ᵐ r : ℝ, 0 < r → U r = r * prof r := by
    simpa [prof, U] using (canonicalProfile_eq_profile (v := v) (w := w) (R := R) hR hvrad hv_supp hrad hw)
  let E : Set ℝ := {r : ℝ | ¬ (0 < r → U r = r * prof r)}
  have hEvol : (volume : Measure ℝ) E = 0 := MeasureTheory.ae_iff.mp hEq
  let N : Set ℝ := {r : ℝ | ¬ (0 < r → 0 ≤ prof r ∧ prof r ≤ 1)}
  have hNsubE : N ⊆ E := by
    intro r hrN
    by_contra hrE
    change ¬(0 < r → 0 ≤ prof r ∧ prof r ≤ 1) at hrN
    rw [Classical.not_imp] at hrN
    rcases hrN with ⟨hr0, hbad⟩
    by_cases hrR : r < R
    · have hEqr : U r = r * prof r := by
        by_contra hneq
        have hmem : r ∈ E := by
          change ¬(0 < r → U r = r * prof r)
          intro hpos
          exact hneq (hpos hr0)
        exact hrE hmem
      have hUnonneg : 0 ≤ U r := canonicalProfile_nonneg hR hv_nonneg hvrad hv_supp hrad hw r hr0 hrR
      have hUle : U r ≤ r := canonicalProfile_le_r hR hv_nonneg hvrad hv_supp hrad hw r hr0 hrR
      have hprof0 : 0 ≤ prof r := by
        have h0 : 0 ≤ r * prof r := by simpa [hEqr, U] using hUnonneg
        exact (mul_nonneg_iff_of_pos_left hr0).mp h0
      have hprof1 : prof r ≤ 1 := by
        have h1 : r * prof r ≤ r * 1 := by simpa [hEqr, U] using hUle
        exact (mul_le_mul_iff_of_pos_left hr0).mp h1
      exact hbad ⟨hprof0, hprof1⟩
    · have hrR' : R ≤ r := le_of_not_gt hrR
      have hEqr : U r = r * prof r := by
        by_contra hneq
        have hmem : r ∈ E := by
          change ¬(0 < r → U r = r * prof r)
          intro hpos
          exact hneq (hpos hr0)
        exact hrE hmem
      have hUr0 : 0 ≤ U r := by
        rw [hUc r hrR']
        exact hc0
      have hUrr : U r ≤ r := by
        rw [hUc r hrR']
        linarith
      have hprof0 : 0 ≤ prof r := by
        have h0 : 0 ≤ r * prof r := by simpa [hEqr, U] using hUr0
        exact (mul_nonneg_iff_of_pos_left hr0).mp h0
      have hprof1 : prof r ≤ 1 := by
        have h1 : r * prof r ≤ r * 1 := by simpa [hEqr, U] using hUrr
        exact (mul_le_mul_iff_of_pos_left hr0).mp h1
      exact hbad ⟨hprof0, hprof1⟩
  have hNvol : (volume : Measure ℝ) N = 0 := measure_mono_null hNsubE hEvol
  rw [MeasureTheory.ae_iff]
  change (volume : Measure ℝ) N = 0
  exact hNvol

/-- **A.e. bounds on a scattering solution.**  A radial weak scattering
solution `w` of a non-negative radial `v` (`tsupport v ⊆ ball 0 R`) satisfies
`0 ≤ w x ≤ 1` for almost every `x : ℝ³`. -/
theorem scattering_bounds_ae {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    (∀ᵐ x : ℝ³, 0 ≤ w x) ∧ (∀ᵐ x : ℝ³, w x ≤ 1) := by
  classical
  let prof : ℝ → ℝ := radialProfile w
  have hprof : ∀ᵐ r : ℝ, 0 < r → 0 ≤ prof r ∧ prof r ≤ 1 := by
    simpa [prof] using (radialProfile_bounds_ae hR hv_nonneg hvrad hv_supp hrad hw)
  let N : Set ℝ := {r : ℝ | ¬ (0 < r → 0 ≤ prof r ∧ prof r ≤ 1)}
  have hNvol : (volume : Measure ℝ) N = 0 := MeasureTheory.ae_iff.mp hprof
  let S : Set ℝ := MeasureTheory.toMeasurable (volume : Measure ℝ) N
  have hSmeas : MeasurableSet S := MeasureTheory.measurableSet_toMeasurable (volume : Measure ℝ) N
  have hNS : N ⊆ S := MeasureTheory.subset_toMeasurable (volume : Measure ℝ) N
  have hSvol : (volume : Measure ℝ) S = 0 := by
    rw [MeasureTheory.measure_toMeasurable]
    exact hNvol
  have hprevol : (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ S} = 0 :=
    volume_preimage_norm_null_r3 hSmeas hSvol
  let bad : Set ℝ³ := {x : ℝ³ | ¬(0 ≤ w x ∧ w x ≤ 1)}
  have hbad_sub : bad ⊆ {x : ℝ³ | ‖x‖ ∈ S} ∪ {x : ℝ³ | ‖x‖ = 0} := by
    intro x hx
    by_cases hxS : ‖x‖ ∈ S
    · exact Or.inl hxS
    · right
      by_contra hx0
      have hx0' : ‖x‖ ≠ 0 := by
        intro h
        exact hx0 (by simpa using h)
      have hxpos : 0 < ‖x‖ := by
        exact norm_pos_iff.mpr (by intro hx; exact hx0' (by simp [hx]))
      have hxN : ‖x‖ ∉ N := by
        intro hmem
        exact hxS (hNS hmem)
      have hb : 0 ≤ prof ‖x‖ ∧ prof ‖x‖ ≤ 1 := by
        by_contra hnb
        apply hxN
        change ¬(0 < ‖x‖ → 0 ≤ prof ‖x‖ ∧ prof ‖x‖ ≤ 1)
        intro hI
        exact hnb (hI hxpos)
      have hw0 : 0 ≤ w x := by
        rw [radial_eq_profile hrad x]
        exact hb.1
      have hw1 : w x ≤ 1 := by
        rw [radial_eq_profile hrad x]
        exact hb.2
      exact hx ⟨hw0, hw1⟩
  have hpre0 : (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ = 0} = 0 := by
    have hset : {x : ℝ³ | ‖x‖ = 0} = Metric.sphere (0 : ℝ³) 0 := by
      ext x
      simp
    rw [hset]
    exact volume_sphere_r3 (0 : ℝ)
  have hbadvol : (volume : Measure ℝ³) bad = 0 := by
    have hunion : (volume : Measure ℝ³) ({x : ℝ³ | ‖x‖ ∈ S} ∪ {x : ℝ³ | ‖x‖ = 0}) = 0 :=
      measure_union_null hprevol hpre0
    exact measure_mono_null hbad_sub hunion
  have h3 : ∀ᵐ x : ℝ³, 0 ≤ w x ∧ w x ≤ 1 := by
    rw [MeasureTheory.ae_iff]
    change (volume : Measure ℝ³) bad = 0
    exact hbadvol
  constructor
  · filter_upwards [h3] with x hx
    exact hx.1
  · filter_upwards [h3] with x hx
    exact hx.2

/-
NOTE for the integrator: the originally planned statement
`chosen_av_bounds : ... (h : ∃ w, IsRadial w ∧ IsScatteringSolution w v) → 0 < a v ∧ a v ≤ R`
is **false as stated**: the identically-zero potential `v ≡ 0` satisfies every
hypothesis (`h` holds with `w ≡ 0`), yet `a v = 0`.  What the maximum-principle
route gives is the non-strict bounds `0 ≤ a v ≤ R` (`chosen_av_bounds_weak`
below); the strict inequality `0 < a v` additionally needs the branch condition
`a v ≠ 0` (or `v` not a.e. zero), which is available where these facts are
consumed (the `a v ≠ 0` branch of `hbox`).
-/
/-- **Bounds on the scattering length (chosen, non-strict).**  In the chosen
branch the scattering length satisfies `0 ≤ a v ≤ R`: the exterior value
`a v = U(R)` of the chosen profile lies in `[0,R]` by the endpoint bounds of
`canonicalProfile_nonneg_at_R` / `canonicalProfile_le_r_at_R`. -/
theorem chosen_av_bounds_weak {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    0 ≤ a v ∧ a v ≤ R := by
  let w₀ : ℝ³ → ℝ := Classical.choose h
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial w₀ := hspec.1
  have hw₀ : IsScatteringSolution w₀ v := hspec.2
  have hform : ∀ᵐ x : ℝ³, R ≤ ‖x‖ → w₀ x = a v / ‖x‖ := by
    simpa [w₀] using chosen_scattering_av_exterior (v := v) (R := R) hR hv_supp h
  have hUc : canonicalProfile v w₀ R R = a v := by
    exact canonicalProfile_const_beyond (v := v) (w := w₀) (R := R) hR hvrad hv_supp hrad₀ hw₀
      (c := a v) hform R le_rfl
  constructor
  · rw [← hUc]
    exact canonicalProfile_nonneg_at_R hR hv_nonneg hvrad hv_supp hrad₀ hw₀
  · rw [← hUc]
    exact canonicalProfile_le_r_at_R hR hv_nonneg hvrad hv_supp hrad₀ hw₀

/-- **Non-negativity of `g := v(1−w)`.**  For a radial weak scattering solution
`w` of a non-negative radial `v` (`tsupport v ⊆ ball 0 R`),
`0 ≤ v x·(1 − w x)` for almost every `x`. -/
theorem scattering_g_nonneg {v w : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    (∀ᵐ x : ℝ³, 0 ≤ v x * (1 - w x)) := by
  have hb := scattering_bounds_ae hR hv_nonneg hvrad hv_supp hrad hw
  filter_upwards [hb.2] with x hw1
  exact mul_nonneg (hv_nonneg x) (sub_nonneg.mpr hw1)

end Submission.BoseGases
