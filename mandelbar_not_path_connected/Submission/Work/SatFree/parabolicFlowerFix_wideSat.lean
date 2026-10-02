import Mathlib
import Submission.Work.SatFree.Defs
import Submission.Work.SatFree.germ_flowerFix_wideSat
import Submission.Work.SatFree.transfer_parabolicFlowerFix_wideSat
import Submission.Work.GATE2.PL.parabolicFlowerFix_saturating

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Set Filter Metric Function
open Work.FatouCoord
open Work.FatouCoord.Flower

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.SatFree

noncomputable section

/-- **The wide, sign-free saturating repaired flower at a simple parabolic point.**

Copy of `Work.GATE2.PL.parabolicFlowerFix_saturating`
(`Submission/Work/GATE2/PL/parabolicFlowerFix_saturating.lean`) with the numeric hypothesis
`ha1` **deleted**, the germ input replaced by `SatFree.germ_flowerFix_wideSat` and the transfer by
`SatFree.transfer_parabolicFlowerFix_wideSat`; the two extra conjuncts (wide chart sector and
`SatHalfPlane`) are those of the transfer.

Route (identical to the GATE2 file up to the two replacements):

* `Work.FatouCoord.Flower.germ_bounds hF hfix h1 h2` gives `f, h, a, r, A, A', lam` with `lam ≠ 0`,
  `hb : ParabolicBounds f h a r A A'` and `hfeq : F (z₀ + lam u) = z₀ + lam (f u)`;
  `parabolicBounds_a_value` is no longer needed (it was used only to convert `ha1` into
  `a.re < 1`), but the tangency step is;
* `f' u := (F (z₀ + lam * u) - z₀)/lam`, `gU u := (g (z₀ + lam * u) - z₀)/lam`; `gU ∘ gU = f'`,
  `gU 0 = 0`, `star (gU u)` holomorphic (`hGdiff`, from `hg`);
* `Work.FatouCoord.Flower.tangency_of_antiholomorphic_root` gives `deriv G 0 = 1` and `star a = a`
  with `G := star ∘ gU`; `Work.FatouCoord.Flower.norm_star_sub_le` gives `ρ` and the quantitative
  tangency `hgl : ‖gU z - star z‖ ≤ C ‖z‖²` for `‖z‖ < ρ`;
* apply `SatFree.germ_flowerFix_wideSat` at radius `δ' := δ / ‖lam‖`;
* transfer back with `SatFree.transfer_parabolicFlowerFix_wideSat`, using
  `hFf : F (z₀ + lam u) = z₀ + lam (f' u)`, `hGg : g (z₀ + lam u) = z₀ + lam (gU u)`,
  `hPa_small` from `fl.Pa ⊆ ball 0 δ'` and `hPg_small` from `fl.Pg ⊆ fl.Pa` (`Pg_sub`) composed
  with it, plus the scaling `‖z₀ + lam * u - z₀‖ = ‖lam‖‖u‖ < δ`.  The wide conjunct is
  transported with the *same* `Ms` and with `lam`; the `SatHalfPlane` conjunct transfers with the
  same `X`. -/
theorem parabolicFlowerFix_wideSat {F g : ℂ → ℂ} {z₀ : ℂ}
    (hF : Differentiable ℂ F) (hg : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (g z)) z)
    (hgg : g ∘ g = F) (hfix : F z₀ = z₀) (h1 : deriv F z₀ = 1)
    (h2 : iteratedDeriv 2 F z₀ ≠ 0) (hgz : g z₀ = z₀) {δ : ℝ} (hδ : 0 < δ) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix F g z₀, fl.Pa ⊆ Metric.ball z₀ δ ∧
      (∃ (Ms : ℝ) (lam : ℂ), lam ≠ 0 ∧ ∀ W : ℂ, W ≠ 0 →
        Ms < Work.FatouCoord.Flower.sgauge W → z₀ - lam / W ∈ fl.Pa) ∧
      Work.SatFree.SatHalfPlane g fl.Pa fl.φa := by
  -- ## The affine normalisation of the germ `F` at `z₀`
  obtain ⟨f, h, a, r, A, A', lam, hlam, hb, hfeq⟩ :=
    Work.FatouCoord.Flower.germ_bounds hF hfix h1 h2
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
  -- ## The wide, sign-free saturating flower of the germ
  have hδ' : 0 < δ / ‖lam‖ := div_pos hδ (norm_pos_iff.mpr hlam)
  obtain ⟨fl₀, hPa₀, hwide₀, hsat₀⟩ :=
    germ_flowerFix_wideSat hf'ent hb'' hρpos (le_refl ρ) hδ' hgl
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
  obtain ⟨fl, hPa, hPg, ⟨Ms, hwideMs⟩, hsat⟩ :=
    transfer_parabolicFlowerFix_wideSat (F := F) (g := g) (f := f') (gU := gU)
      (z₀ := z₀) (lam := lam) (δ := δ) hlam (fun z => hg z) hFf hGg hδ fl₀ hPa₀
      (fun u hu => hPa₀ (fl₀.Pg_sub hu)) hwide₀ hsat₀
  exact ⟨fl, hPa, ⟨Ms, lam, hlam, hwideMs⟩, hsat⟩

end

end Work.SatFree
