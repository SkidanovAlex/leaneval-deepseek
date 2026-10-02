import Mathlib
import Submission.Work.Landing.Rays
import Submission.Work.Landing.Rays.radialRay_norm
import Submission.Work.Landing.Rays.image_dynRay_subset
import Submission.Work.Landing.Rays.isBounded_dynRay_sublevel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The image of the accumulation set of a dynamic ray

For the antiholomorphic quadratic family `T_c(z) = z̄² + c` with a Böttcher coordinate `φ`, the
Böttcher equation `φ (T_c z) = conj (φ z)²` shows that `T_c` maps the dynamic ray `R_c(θ)` into
the dynamic ray `R_c(angDouble θ)` with `angDouble θ = Int.fract (-2θ)`, and regrouping the
`closure` in the definition of the *accumulation set* of a ray turns this into the equality

`Tantibar c '' rayAccum c φ θ = rayAccum c φ (angDouble θ)`.

The ingredients are

* the angle identity `rayDirection (angDouble θ) = conj (rayDirection θ)²` and the Böttcher
  equation, which give `T_c '' R_c(θ) ⊆ R_c(angDouble θ)` (`Work.Landing.Rays.image_dynRay_subset`)
  together with `‖φ (T_c z)‖ = ‖φ z‖²` (`norm_phi_Tantibar`), so that a truncated ray of level `ρ`
  maps into the truncated ray of level `ρ²` (forward inclusion);
* the asymptotic `φ z ~ z` at infinity, which makes the truncated rays
  `{z ∈ R_c(θ) : ‖φ z‖ ≤ ρ}` bounded, hence relatively compact
  (`Work.Landing.Rays.isBounded_dynRay_sublevel`); a sequence of preimages of ray points
  converging to the target therefore has a convergent subsequence (reverse inclusion);
* a preimage statement (`exists_preimage_mem_dynRay_homeo`): *every* point of `R_c(angDouble θ)`
  has a preimage on `R_c(θ)`.  For the Böttcher homeomorphism `IsDynBottcherHomeo` this is
  elementary: write `φ w = r · e^{2πi angDouble θ}` with `r > 1`; surjectivity of `φ` onto the
  exterior of the unit disk supplies a point `u` with `φ u = √r · e^{2πi θ}`, which by `√r > 1`
  lies on `R_c(θ)`, and injectivity on the escaping set identifies `T_c u` with `w`, because
  `φ (T_c u) = conj (φ u)² = r · e^{2πi angDouble θ} = φ w`.

Note that no hypothesis excluding the critical value `c` is needed: a ray point `w` is escaping,
so it is never the critical point `0`, and the preimage constructed above is the *unique* one.
-/

noncomputable section

open Classical Function Filter
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.ParamRays (IsDynBottcher Escaping escapingSet orbit orbit_succ)

namespace Work.Landing.Rays

/-! ## Elementary continuity and the Böttcher equation in modulus form -/

/-- `T_c` is continuous. -/
theorem continuous_Tantibar (c : ℂ) : Continuous (Tantibar c) := by
  have h : Tantibar c = fun z : ℂ => star z ^ 2 + c := rfl
  rw [h]
  exact (continuous_star.pow 2).add continuous_const

/-- The Böttcher equation read on moduli: `‖φ (T_c z)‖ = ‖φ z‖ ^ 2`. -/
theorem norm_phi_Tantibar {c : ℂ} {φ : ℂ → ℂ} (hφ : IsDynBottcher c φ) {z : ℂ}
    (hz : Escaping c z) : ‖φ (Tantibar c z)‖ = ‖φ z‖ ^ 2 := by
  rw [hφ.2.1 z hz, norm_pow, Complex.norm_conj]

/-- `T_c u` is escaping whenever `u` is. -/
theorem escaping_Tantibar {c u : ℂ} (hu : Escaping c u) : Escaping c (Tantibar c u) := by
  have h1 : orbit c u 1 = Tantibar c u := by simp [orbit]
  rw [← h1]
  exact hu.iterate 1

/-! ## Preimages on the prescribed ray -/

/-- Every point of the ray at angle `angDouble θ` has a preimage on the ray at angle `θ`.  Write
`φ w = r · e^{2πi angDouble θ}` with `r > 1`; surjectivity of the Böttcher homeomorphism gives a
point `u` with `φ u = √r · e^{2πi θ}`, which lies on `R_c(θ)` because `√r > 1`, and then
`φ (T_c u) = conj (φ u)² = r · e^{2πi angDouble θ} = φ w`, so `T_c u = w` by injectivity of `φ` on
the escaping set. -/
theorem exists_preimage_mem_dynRay_homeo {c : ℂ} {φ : ℂ → ℂ}
    (h : Work.Landing.IsDynBottcherHomeo c φ) {θ : ℝ} {w : ℂ}
    (hw : w ∈ dynRay c φ (angDouble θ)) :
    ∃ z : ℂ, Tantibar c z = w ∧ z ∈ dynRay c φ θ := by
  obtain ⟨hφ, hinj, hsurj⟩ := h
  obtain ⟨hwesc, r, hr1, hwr⟩ := hw
  -- the level `√r` on the `θ`-ray
  set ρ : ℝ := Real.sqrt r with hρdef
  have hρpos : 0 < ρ := Real.sqrt_pos.mpr (lt_trans zero_lt_one hr1)
  have hρ1 : 1 < ρ := by
    rw [hρdef, ← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt zero_le_one hr1
  have hρsq : ρ ^ 2 = r := Real.sq_sqrt (le_of_lt (lt_trans zero_lt_one hr1))
  have hnorm : ‖(ρ : ℂ) * rayDirection θ‖ = ρ := by
    rw [norm_mul, norm_rayDirection, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρpos]
  -- surjectivity supplies the point of the `θ`-ray
  obtain ⟨u, huesc, hφu⟩ := hsurj ((ρ : ℂ) * rayDirection θ) (by rw [hnorm]; exact hρ1)
  have hTuesc : Escaping c (Tantibar c u) := escaping_Tantibar huesc
  -- its image has the same Böttcher value as `w`
  have hval : φ (Tantibar c u) = φ w := by
    have hc : (starRingEnd ℂ) ((ρ : ℂ) * rayDirection θ) = (ρ : ℂ) * star (rayDirection θ) := by
      rw [map_mul, Complex.conj_ofReal, starRingEnd_apply]
    rw [hφ.2.1 u huesc, hφu, hwr, hc, mul_pow, ← ImageDynRay.rayDirection_angDouble θ,
      ← Complex.ofReal_pow, hρsq]
  exact ⟨u, hinj _ _ hTuesc hwesc hval, huesc, ρ, hρ1, hφu⟩

/-! ## The image of the accumulation set -/

/-- The accumulation set of the ray at angle `θ` is mapped onto the accumulation set of the ray
at angle `-2θ` by `T_c`, assuming the Böttcher coordinate is a homeomorphism of the escaping set
onto the exterior of the unit disk (`IsDynBottcherHomeo`): surjectivity produces a preimage on the
prescribed ray for every ray point, injectivity identifies it with the unique preimage of `T_c`. -/
theorem rayAccum_image_homeo {c : ℂ} {φ : ℂ → ℂ} (h : Work.Landing.IsDynBottcherHomeo c φ)
    (θ : ℝ) :
    LeanEval.ComplexAnalysis.Tantibar c '' Work.Landing.rayAccum c φ θ =
      Work.Landing.rayAccum c φ ((Work.Landing.angDouble) θ) := by
  obtain ⟨hφ, hinj, hsurj⟩ := h
  refine Set.Subset.antisymm ?_ ?_
  · -- the image of the truncated ray of level `√ρ` lies in the truncated ray of level `ρ`
    rintro _ ⟨x, hx, rfl⟩ ρ hρ
    have hσ : 1 < Real.sqrt ρ := (Real.lt_sqrt zero_le_one).mpr (by rw [one_pow]; exact hρ)
    have himg : Tantibar c '' {z : ℂ | z ∈ dynRay c φ θ ∧ ‖φ z‖ ≤ Real.sqrt ρ} ⊆
        {z : ℂ | z ∈ dynRay c φ (angDouble θ) ∧ ‖φ z‖ ≤ ρ} := by
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨image_dynRay_subset hφ θ ⟨z, hz.1, rfl⟩, ?_⟩
      rw [norm_phi_Tantibar hφ hz.1.1]
      have h2 : ‖φ z‖ ^ 2 ≤ (Real.sqrt ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz.2 2
      rwa [Real.sq_sqrt (le_of_lt (lt_trans zero_lt_one hρ))] at h2
    exact closure_mono himg (image_closure_subset_closure_image (continuous_Tantibar c)
      ⟨x, hx _ hσ, rfl⟩)
  · -- conversely: approximate the target by ray points, lift them to the `θ`-ray, and pass to a
    -- convergent subsequence
    intro y hy
    -- the level sequence `1 + 1/(n+1)`, decreasing to `1` from above and bounded by `2`
    set ρs : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1) with hρsdef
    have hρsgt : ∀ n, 1 < ρs n := fun n => by
      have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
      rw [hρsdef]; simp only; linarith
    have hρsle : ∀ n, ρs n ≤ 2 := fun n => by
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hpos]; linarith
      rw [hρsdef]; simp only; linarith
    have hρs_tend : Tendsto ρs atTop (𝓝 1) := by
      have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [hρsdef] using h1.add h2
    -- an approximating sequence of points of the ray at angle `angDouble θ`
    have hmem : ∀ n, ∃ w : ℂ,
        w ∈ {z : ℂ | z ∈ dynRay c φ (angDouble θ) ∧ ‖φ z‖ ≤ ρs n} ∧
          dist y w < 1 / ((n : ℝ) + 1) := fun n =>
      Metric.mem_closure_iff.mp (hy (ρs n) (hρsgt n)) _ (by positivity)
    choose w hwmem hwdist using hmem
    -- the corresponding preimages on the ray at angle `θ`
    have hpre : ∀ n, ∃ x : ℂ, Tantibar c x = w n ∧ x ∈ dynRay c φ θ := fun n =>
      exists_preimage_mem_dynRay_homeo ⟨hφ, hinj, hsurj⟩ (hwmem n).1
    choose x hxT hxmem using hpre
    have hxbnd : ∀ n, ‖φ (x n)‖ ^ 2 ≤ ρs n := fun n => by
      have h1 : ‖φ (x n)‖ ^ 2 = ‖φ (w n)‖ := by
        rw [← norm_phi_Tantibar hφ (hxmem n).1, hxT n]
      rw [h1]
      exact (hwmem n).2
    have hxn1 : ∀ n, 1 < ‖φ (x n)‖ := fun n => radialRay_norm (hxmem n).2
    have hxK : ∀ n, x n ∈ {z : ℂ | z ∈ dynRay c φ θ ∧ ‖φ z‖ ≤ (2 : ℝ)} := fun n => by
      refine ⟨hxmem n, ?_⟩
      have h3 : ‖φ (x n)‖ ≤ ‖φ (x n)‖ ^ 2 := by
        nlinarith [sq_nonneg (‖φ (x n)‖ - 1), hxn1 n]
      linarith [h3, hxbnd n, hρsle n]
    -- compactness of the truncated ray gives a convergent subsequence
    have hcomp : IsCompact (closure {z : ℂ | z ∈ dynRay c φ θ ∧ ‖φ z‖ ≤ (2 : ℝ)}) :=
      (isBounded_dynRay_sublevel hφ θ 2).isCompact_closure
    obtain ⟨a, -, u, hu, hutend⟩ := hcomp.tendsto_subseq (fun n => subset_closure (hxK n))
    have hutend' : Tendsto (fun k => x (u k)) atTop (𝓝 a) := hutend
    -- the ray points converge to the target
    have hw_tend : Tendsto w atTop (𝓝 y) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      refine ⟨N, fun n hn => ?_⟩
      have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (N : ℝ) + 1)
        linarith
      have h3 : dist y (w n) < ε :=
        lt_of_lt_of_le (hwdist n) (le_of_lt (lt_of_le_of_lt h2 hN))
      rwa [dist_comm]
    have h1t : Tendsto (fun k => w (u k)) atTop (𝓝 y) := hw_tend.comp hu.tendsto_atTop
    have h2t : Tendsto (fun k => w (u k)) atTop (𝓝 (Tantibar c a)) := by
      have h3 : Tendsto (fun k => Tantibar c (x (u k))) atTop (𝓝 (Tantibar c a)) :=
        ((continuous_Tantibar c).continuousAt).tendsto.comp hutend'
      simpa only [hxT] using h3
    have hTa : Tantibar c a = y := tendsto_nhds_unique h2t h1t
    refine ⟨a, ?_, hTa⟩
    -- `a` is an accumulation point of the ray at angle `θ`: the preimages still lie on the
    -- sublevel `‖φ‖ ≤ ρ` once the level has dropped below `ρ`
    intro ρ hρ
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    have hsqrt_tend : Tendsto (fun k => Real.sqrt (ρs (u k))) atTop (𝓝 1) := by
      have h4 : Tendsto (fun k => ρs (u k)) atTop (𝓝 1) := hρs_tend.comp hu.tendsto_atTop
      have h5 := (Real.continuous_sqrt.continuousAt (x := (1 : ℝ))).tendsto.comp h4
      simpa only [Function.comp_def, Real.sqrt_one] using h5
    have hev1 : ∀ᶠ k in atTop, x (u k) ∈ {z : ℂ | z ∈ dynRay c φ θ ∧ ‖φ z‖ ≤ ρ} := by
      filter_upwards [hsqrt_tend.eventually (isOpen_Iio.mem_nhds hρ)] with k hk
      refine ⟨hxmem (u k), ?_⟩
      have h6 : ‖φ (x (u k))‖ ≤ Real.sqrt (ρs (u k)) :=
        calc ‖φ (x (u k))‖ = Real.sqrt (‖φ (x (u k))‖ ^ 2) :=
              (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (ρs (u k)) := Real.sqrt_le_sqrt (hxbnd (u k))
      exact le_of_lt (lt_of_le_of_lt h6 hk)
    have hev2 : ∀ᶠ k in atTop, dist (x (u k)) a < ε :=
      (Metric.tendsto_nhds.mp hutend') ε hε
    obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
    exact ⟨x (u k), hk1, by rwa [dist_comm] at hk2⟩

end Work.Landing.Rays
