/-
# The repaired Leau–Fatou flower at a simple parabolic fixed point, with a Fatou coordinate
that saturates a right half-plane

`Work.FatouCoordFix.FlowerFix.exists_parabolicFlowerFix_small` produces a repaired Leau–Fatou
flower of an *arbitrary* simple parabolic germ `(F, g)` at `z₀` (holomorphic `F` with
`F z₀ = z₀`, `deriv F z₀ = 1`, `iteratedDeriv 2 F z₀ ≠ 0`, and an antiholomorphic square root
`g` of `F`), small enough to sit in a prescribed ball.  Its Fatou coordinate `φa` is an opaque
`∃`-witness, so no statement about its image can be extracted from it.

Here we re-run the same construction, but with the germ-level theorem
`Work.GATE2.PL.germ_parabolicFlowerFix_saturating`, whose Fatou coordinate — after the standard
affine normalisation of the germ — is *explicitly* the orbit coordinate
`z ↦ fatouCoord f (1 - a) z + s` on a small `g`-invariant half-plane petal `Pg`.  Since
`fatouCoordW_saturates_petal` says that the chart coordinate `w ↦ fatouCoordW f (1 - a) w`
surjects onto a right half-plane with preimages of arbitrarily large real part, the flower's
`φa` saturates a right half-plane on `Pg`; this is the extra statement the tricorn (Mandelbar)
path-connectivity proof needs.

The normalisation enters only through the value of the Abel parameter `a` of the germ: by
`Work.GATE2.PL.parabolicBounds_a_value`, `a = (2/3) F'''(z₀)/F''(z₀)²`, so the hypothesis
`((2/3) F'''(z₀)/F''(z₀)²).re < 1` of the statement is exactly `a.re < 1`.  The remaining
hypothesis of the germ theorem, `star a = a`, is a theorem
(`Work.FatouCoord.Flower.tangency_of_antiholomorphic_root`), not an assumption.

The last step transports the flower back along the affine chart; the transfer must remember the
saturation, which is why we use `Work.GATE2.PL.transfer_parabolicFlowerFix_saturating` rather
than `Work.FatouCoordFix.FlowerFix.transfer_parabolicFlowerFix` (whose `∃`-witness forgets the
fields of the transferred flower).
-/
import Mathlib
import Submission.Work.GATE2.PL.germ_parabolicFlowerFix_saturating
import Submission.Work.GATE2.PL.transfer_parabolicFlowerFix_saturating
import Submission.Work.GATE2.PL.parabolicBounds_a_value
import Submission.Work.FatouCoordFix.FlowerFix.TransferFix
import Submission.Work.FatouCoordFix.FlowerFix.ExistsFix

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Work.FatouCoord Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.GATE2.PL

noncomputable section

theorem parabolicFlowerFix_saturating {F g : ℂ → ℂ} {z₀ : ℂ}
    (hF : Differentiable ℂ F) (hg : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (g z)) z)
    (hgg : g ∘ g = F) (hfix : F z₀ = z₀) (h1 : deriv F z₀ = 1)
    (h2 : iteratedDeriv 2 F z₀ ≠ 0) (hgz : g z₀ = z₀) {δ : ℝ} (hδ : 0 < δ)
    (ha1 : ((2 / 3 : ℝ) * iteratedDeriv 3 F z₀ / (iteratedDeriv 2 F z₀) ^ 2).re < 1) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀,
      fl.Pa ⊆ Metric.ball z₀ δ ∧ fl.Pg ⊆ Metric.ball z₀ δ ∧
      ∃ X : ℝ, ∀ w : ℂ, X < w.re → ∃ z ∈ fl.Pg, fl.φa z = w := by
  -- ## The affine normalisation of the germ `F` at `z₀`
  obtain ⟨f, h, a, r, A, A', lam, hlam, hb, hfeq⟩ :=
    Work.FatouCoord.Flower.germ_bounds hF hfix h1 h2
  -- the Abel parameter of the germ is the affine invariant of `F` appearing in the hypothesis
  have ha_val : a = (2 / 3 : ℂ) * iteratedDeriv 3 F z₀ / (iteratedDeriv 2 F z₀) ^ 2 :=
    parabolicBounds_a_value hF h2 hb hfeq
  have ha_lt : a.re < 1 := by
    have hcast : (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) := by norm_num
    have hre : a.re = ((2 / 3 : ℝ) * iteratedDeriv 3 F z₀ / (iteratedDeriv 2 F z₀) ^ 2).re := by
      rw [ha_val, hcast]
    rw [hre]
    exact ha1
  -- `f'` is the germ written through the chart, i.e. the same germ on a disc
  set f' : ℂ → ℂ := fun u => (F (z₀ + lam * u) - z₀) / lam with hf'def
  have hf'ent : Differentiable ℂ f' := by rw [hf'def]; fun_prop
  have hb' : Work.FatouCoord.ParabolicBounds f' h a r A A' :=
    Work.FatouCoordFix.FlowerFix.epf_Bounds_of_eqOn hb (fun u hu => by
      show (F (z₀ + lam * u) - z₀) / lam = f u
      exact (hfeq u (mem_ball_zero_iff.mpr hu)).symm)
  -- the antiholomorphic square root transferred to the germ plane
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
  -- ## Tangency of the square root and the reality of the Abel parameter
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
  have hha : deriv h 0 = a := Work.FatouCoordFix.FlowerFix.epf_deriv_h_eq_a hb
  have hhd : DifferentiableAt ℂ h 0 := hb.h_diff.differentiableAt (Metric.ball_mem_nhds 0 hb.hr)
  obtain ⟨hG1, ha_sym⟩ :=
    Work.FatouCoord.Flower.tangency_of_antiholomorphic_root hb.hr hGan hG0 hhf
      (fun u hu => hb'.f_eq u (mem_ball_zero_iff.mpr hu)) hhd hh0 hha
  -- the tangency of `gU` to conjugation, in the quantitative form the germ theorem needs
  obtain ⟨C, ρ', hρ', hC⟩ := Work.FatouCoord.Flower.norm_star_sub_le hGan hG0 hG1
  set ρ : ℝ := min ρ' r with hρdef
  have hρpos : 0 < ρ := lt_min hρ' hb.hr
  have hρr : ρ ≤ r := min_le_right _ _
  have hb'' : Work.FatouCoord.ParabolicBounds f' h a ρ A A' :=
    Work.FatouCoordFix.FlowerFix.epf_Bounds_mono hb' hρpos hρr
  have hgl : ∀ z : ℂ, ‖z‖ < ρ → ‖gU z - star z‖ ≤ C * ‖z‖ ^ 2 := by
    intro z hz
    have h1' := hC z (lt_of_lt_of_le hz (min_le_left _ _))
    rw [← hGstar z]
    exact h1'
  -- ## The saturating flower of the germ
  have hδ' : 0 < δ / ‖lam‖ := div_pos hδ (norm_pos_iff.mpr hlam)
  obtain ⟨fl₀, hPa₀, hPg₀, hsat₀⟩ :=
    germ_parabolicFlowerFix_saturating hf'ent hb'' hρpos (le_refl ρ) hδ' ha_lt hgl
      hgU_anti hggU hgU0 ha_sym
  -- ## Transfer back to the dynamical plane
  have hFf : ∀ u : ℂ, F (z₀ + lam * u) = z₀ + lam * f' u := by
    intro u
    rw [hf'def]
    field_simp
    ring
  have hGg : ∀ u : ℂ, g (z₀ + lam * u) = z₀ + lam * gU u := by
    intro u
    rw [hgUdef]
    field_simp
    ring
  exact transfer_parabolicFlowerFix_saturating (F := F) (g := g) (f := f') (gU := gU)
    (z₀ := z₀) (lam := lam) (δ := δ) hlam (fun z => hg z) hFf hGg hδ fl₀ hPa₀ hPg₀ hsat₀

end

end Work.GATE2.PL
