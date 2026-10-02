import Mathlib
import Submission.Work.FatouCoord.Flower
import Submission.Work.FatouCoord.Flower.germ_bounds
import Submission.Work.FatouCoord.Flower.tangency_of_antiholomorphic_root
import Submission.Work.FatouCoord.Flower.norm_star_sub_le
import Submission.Work.FatouCoord.Flower.germ_parabolicFlower
import Submission.Work.FatouCoord.Flower.transfer_parabolicFlower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Flower

open scoped Topology
open Work.FatouCoord Set Filter

/-- `ParabolicBounds` only constrains the germ on a disc, so it is insensitive to changing `f`
outside that disc. -/
theorem epf_Bounds_of_eqOn {f f' h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A')
    (hf : ∀ z : ℂ, ‖z‖ < r → f' z = f z) : ParabolicBounds f' h a r A A' := by
  refine ⟨hb.hr, hb.hA, hb.hA', ?_, hb.h_diff, hb.h_close, hb.h_bound, hb.h_deriv_bound⟩
  intro z hz
  rw [hf z (mem_ball_zero_iff.mp hz), hb.f_eq z hz]

/-- `ParabolicBounds` is monotone in the radius. -/
theorem epf_Bounds_mono {f h : ℂ → ℂ} {a : ℂ} {r r' A A' : ℝ} (hb : ParabolicBounds f h a r A A')
    (hr' : 0 < r') (hle : r' ≤ r) : ParabolicBounds f h a r' A A' := by
  refine ⟨hr', hb.hA, hb.hA', ?_, hb.h_diff.mono (Metric.ball_subset_ball hle),
    ?_, ?_, ?_⟩
  · intro z hz; exact hb.f_eq z (Metric.ball_subset_ball hle hz)
  · intro z hz; exact hb.h_close z (Metric.ball_subset_ball hle hz)
  · intro z hz; exact hb.h_bound z (Metric.ball_subset_ball hle hz)
  · intro z hz; exact hb.h_deriv_bound z (Metric.ball_subset_ball hle hz)

/-- The Abel constant of `ParabolicBounds` is the derivative of `h` at `0`. -/
theorem epf_deriv_h_eq_a {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') :
    deriv h 0 = a := by
  have h00 : h 0 = 1 := by
    have hcl := hb.h_close 0 (mem_ball_zero_iff.mpr (by simpa using hb.hr))
    have : ‖h 0 - 1‖ ≤ 0 := by simpa using hcl
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hmem : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball 0 r :=
    (show ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ Metric.ball 0 r from Metric.ball_mem_nhds 0 hb.hr).filter_mono
      nhdsWithin_le_nhds
  have hbnd : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖(h z - h 0) / z - a‖ ≤ A * ‖z‖ := by
    filter_upwards [hmem, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [show (h z - h 0) / z - a = (h z - 1 - a * z) / z by rw [h00]; field_simp]
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hz0')]
    calc ‖h z - 1 - a * z‖ ≤ A * ‖z‖ ^ 2 := hb.h_close z hz
      _ = A * ‖z‖ * ‖z‖ := by ring
  have htend : Tendsto (fun z : ℂ => (h z - h 0) / z) (𝓝[≠] (0 : ℂ)) (𝓝 a) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) hbnd ?_
    have h3 : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : ℂ)).mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))
    simpa using h3.const_mul A
  have hslope : HasDerivAt h a 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    refine htend.congr' (Filter.EventuallyEq.of_eq (funext fun z => ?_))
    rw [slope_def_field h 0 z, sub_zero]
  exact hslope.deriv

theorem exists_parabolicFlower (F g : ℂ → ℂ) (z₀ : ℂ) (hF : Differentiable ℂ F) (hg : ∀ z, DifferentiableAt ℂ (fun z => star (g z)) z) (hgg : g ∘ g = F) (hfix : F z₀ = z₀) (h1 : deriv F z₀ = 1) (h2 : iteratedDeriv 2 F z₀ ≠ 0) (hgz : g z₀ = z₀) : Nonempty (ParabolicFlower F g z₀) := by
  obtain ⟨f, h, a, r, A, A', lam, hlam, hb, hfeq⟩ := germ_bounds hF hfix h1 h2
  set f' : ℂ → ℂ := fun u => (F (z₀ + lam * u) - z₀) / lam with hf'def
  have hf'ent : Differentiable ℂ f' := by rw [hf'def]; fun_prop
  have hb' : ParabolicBounds f' h a r A A' :=
    epf_Bounds_of_eqOn hb (fun u hu => by
      show (F (z₀ + lam * u) - z₀) / lam = f u
      exact (hfeq u (mem_ball_zero_iff.mpr hu)).symm)
  set gU : ℂ → ℂ := fun u => (g (z₀ + lam * u) - z₀) / lam with hgUdef
  have hstar_gU : ∀ u : ℂ, star (gU u) = (star (g (z₀ + lam * u)) - star z₀) / star lam := by
    intro u; rw [hgUdef, star_div₀, star_sub]
  have hGdiff : Differentiable ℂ (fun u : ℂ => star (gU u)) := by
    have h0 : Differentiable ℂ (fun z : ℂ => star (g z)) := fun z => hg z
    have h1' : Differentiable ℂ (fun u : ℂ => star (g (z₀ + lam * u))) :=
      h0.comp (by fun_prop)
    have h2' : Differentiable ℂ (fun u : ℂ => (star (g (z₀ + lam * u)) - star z₀) / star lam) :=
      (h1'.sub_const _).div_const _
    have he : (fun u : ℂ => star (gU u))
        = fun u : ℂ => (star (g (z₀ + lam * u)) - star z₀) / star lam := funext hstar_gU
    rw [he]; exact h2'
  have hgU_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (gU z)) z :=
    fun z => hGdiff.differentiableAt
  have hggU : gU ∘ gU = f' := by
    funext u
    show (g (z₀ + lam * ((g (z₀ + lam * u) - z₀) / lam)) - z₀) / lam
        = (F (z₀ + lam * u) - z₀) / lam
    rw [show z₀ + lam * ((g (z₀ + lam * u) - z₀) / lam) = g (z₀ + lam * u) from by
          field_simp; ring,
      show g (g (z₀ + lam * u)) = F (z₀ + lam * u) from congrFun hgg (z₀ + lam * u)]
  have hgU0 : gU 0 = 0 := by
    show (g (z₀ + lam * 0) - z₀) / lam = 0
    rw [mul_zero, add_zero, hgz, sub_self, zero_div]
  set G : ℂ → ℂ := fun u => star (gU u) with hGdef
  have hGan : AnalyticAt ℂ G 0 := by rw [hGdef]; exact hGdiff.analyticAt 0
  have hG0 : G 0 = 0 := by show star (gU 0) = 0; rw [hgU0, star_zero]
  have hGstar : ∀ u : ℂ, star (G u) = gU u := by intro u; rw [hGdef]; simp
  have hhf : ∀ u : ℂ, ‖u‖ < r → f' u = star (G (star (G u))) := by
    intro u hu
    rw [← congrFun hggU u, Function.comp_apply, hGstar, hGstar]
  have hh0 : h 0 = 1 := by
    have hcl := hb.h_close 0 (mem_ball_zero_iff.mpr (by simpa using hb.hr))
    have : ‖h 0 - 1‖ ≤ 0 := by simpa using hcl
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hha : deriv h 0 = a := epf_deriv_h_eq_a hb
  have hhd : DifferentiableAt ℂ h 0 := hb.h_diff.differentiableAt (Metric.ball_mem_nhds 0 hb.hr)
  obtain ⟨hG1, ha_sym⟩ :=
    tangency_of_antiholomorphic_root hb.hr hGan hG0 hhf
      (fun u hu => hb'.f_eq u (mem_ball_zero_iff.mpr hu)) hhd hh0 hha
  obtain ⟨C, ρ', hρ', hC⟩ := norm_star_sub_le hGan hG0 hG1
  set ρ : ℝ := min ρ' r with hρdef
  have hρpos : 0 < ρ := lt_min hρ' hb.hr
  have hρr : ρ ≤ r := min_le_right _ _
  have hb'' : ParabolicBounds f' h a ρ A A' := epf_Bounds_mono hb' hρpos hρr
  have hgl : ∀ z : ℂ, ‖z‖ < ρ → ‖gU z - star z‖ ≤ C * ‖z‖ ^ 2 := by
    intro z hz
    have h1' := hC z (lt_of_lt_of_le hz (min_le_left _ _))
    rw [← hGstar z]
    exact h1'
  obtain ⟨hFp⟩ := germ_parabolicFlower hf'ent hb'' hρpos (le_refl ρ) hgl hgU_anti hggU hgU0 ha_sym
  refine transfer_parabolicFlower (F := F) (g := g) (f := f') (gU := gU) (z₀ := z₀) (lam := lam)
    hlam (fun z => hg z) ?_ ?_ hFp
  · intro u
    rw [hf'def]
    field_simp
    ring
  · intro u
    rw [hgUdef]
    field_simp
    ring

end Work.FatouCoord.Flower
