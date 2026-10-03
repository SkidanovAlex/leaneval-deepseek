import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.CoordData
import Submission.Work.Parab.coordData.parabolicBounds_aeq
import Submission.Work.Parab.Setup
import Submission.Work.Parab.germ
import Submission.Work.Parab.basin_basic
import Submission.Work.Parab.petal_cone
import Submission.Work.Parab.flower
import Submission.Work.Parab.basinCoord.exists_basin_coordinate
import Submission.Work.Parab.enterLeft.eventually_mem_left
import Submission.Work.Parab.invOrbit.inv_orbit_QLeft
import Submission.Work.Parab.leftCoordData.exists_LeftCoordData
import Submission.Work.Parab.coordData.exists_CoordData
import Submission.Work.Parab.Eends.E_ends
import Submission.Work.Parab.petalExtras.petal_conn_sc_image

/-!
# PARAB0: every parabolic germ carries §4.1 data

Assembly of `MandelDim.ParabData` from
* the ζ-plane left coordinate (`Work.Parab.LeftCoordData`, `exists_LeftCoordData`),
* the maximal-domain coordinate `φ` (`Work.Parab.CoordData`, `exists_CoordData`),
* the basin coordinate `Φ` (`Work.Parab.basinCoord.exists_basin_coordinate`),
* the flower / petal facts (`Work.Parab.flower`),
* Lemma 5.1 in the form adapted to `InjOn φ (QLeft ξ₀)` (`Work.Parab.invOrbit.inv_orbit_QLeft`),
* the convergence of the lifted horn map at the two ends (`Work.Parab.Eends.E_ends`).
-/

namespace Work.Parab

open MandelDim
open Work.FatouCoord (Petal)

noncomputable section

/-- `QLeft ξ` is closed under `w ↦ w - 1` (local copy of
`Work.Parab.coordData.QLeft_sub_one`, to keep this file independent of the maximal-domain
construction). -/
theorem QLeft_sub_one_local (ξ : ℝ) {w : ℂ} (hw : w ∈ MandelDim.QLeft ξ) :
    w - 1 ∈ MandelDim.QLeft ξ := by
  rw [Work.Parab.QLeft_iff] at hw ⊢
  set u : ℂ := w + (ξ : ℂ) with hu
  have hsplit : (w - 1) + (ξ : ℂ) = u - 1 := by rw [hu]; ring
  rw [hsplit]
  have hnorm : ‖u‖ ≤ ‖u - 1‖ + 1 := by
    have h2 : u = (u - 1) + 1 := by ring
    calc ‖u‖ = ‖(u - 1) + 1‖ := congrArg norm h2
      _ ≤ ‖u - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖u - 1‖ + 1 := by simp
  have h2 : (u - 1).re = u.re - 1 := by simp
  rw [h2]
  linarith

theorem parab : ParabStatement := by
  intro f₀ D₀ hg _hnd -- the non-degeneracy hypothesis feeds the field orbit_avoid

  obtain ⟨Φ, hp, ap, rp, Ap, Ap', Mp, hbP, hballP, hMP, hpetalbasin, hmapsP, hconvP,
    hΦholo, hΦabel, hΦinjP, hΦagree⟩ :=
    Work.Parab.basinCoord.exists_basin_coordinate hg
  have hrp : 0 < rp := hbP.hr
  obtain ⟨dl⟩ := Work.Parab.leftCoordData.exists_LeftCoordData hg
  obtain ⟨d⟩ := Work.Parab.coordData.exists_CoordData dl hg
  -- a quantitative germ bound whose coefficient is `d.ag`, so that `ap = d.ag`
  obtain ⟨hG, rG, AG, AG', hbG⟩ := d.hbond
  have hagap : ap = d.ag := Work.Parab.coordData.parabolicBounds_aeq hbP hbG
  have hbP' : Work.FatouCoord.ParabolicBounds f₀ hp d.ag rp Ap Ap' := hagap ▸ hbP
  have hΦagree' : ∀ z ∈ Petal rp Mp, Φ z = Work.FatouCoord.fatouCoord f₀ (1 - d.ag) z :=
    fun z hz => by rw [hΦagree z hz, hagap]
  -- the level of the attracting petal, above every threshold
  obtain ⟨M₀, hM₀pos, hfac⟩ := Work.Parab.basinCoord.exists_petal_level_facts hbP
  set M : ℝ := max Mp (max M₀ (max 0 (2 / rp))) with hMdef
  have hMpos : 0 < M := by
    have h1 : (0 : ℝ) < max M₀ (max 0 (2 / rp)) :=
      lt_of_lt_of_le hM₀pos (le_max_left _ _)
    exact lt_of_lt_of_le h1 (le_max_right _ _)
  have hMpM : Mp ≤ M := le_max_left _ _
  have hM₀M : M₀ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hMr : 1 / rp < M := by
    have h1 : (0 : ℝ) < 1 / rp := one_div_pos.mpr hrp
    have h2 : 2 / rp ≤ max 0 (2 / rp) := le_max_right _ _
    have h3 : max 0 (2 / rp) ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
    have h4 : 2 / rp = 2 * (1 / rp) := by ring
    linarith
  obtain ⟨hmapM, _, _, _, hunifM⟩ := hfac M hM₀M
  have hsubM : Petal rp M ⊆ Petal rp Mp :=
    Work.FatouCoord.Petal_mono (M := M) (M' := Mp) le_rfl hMpM
  -- the limits of the lifted horn map at the two ends
  obtain ⟨cl, cl', hUp, hLo⟩ :=
    Work.Parab.Eends.E_ends hg d hbP' hpetalbasin hΦholo hΦabel hΦagree'
  -- the local injectivity of the germ
  obtain ⟨G₀, δ, hδ, -, -, -, -, hGleft, -⟩ := Work.Parab.exists_local_inverse_ball hg
  have hfinj : ∃ ρ : ℝ, 0 < ρ ∧ Set.InjOn f₀ (Metric.ball 0 ρ) :=
    ⟨δ, hδ, fun a ha b hb hab => by rw [← hGleft a ha, hab, hGleft b hb]⟩
  have hconvΩ : ∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∀ u ∈ Petal rp M, ‖(f₀^[k]) u‖ < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hunifM) ε hε)
    exact ⟨N, fun k hk u hu => by
      have h := hN k hk u hu
      simpa [dist_eq_norm] using h⟩
  have hextras := Work.Parab.petalExtras.petal_conn_sc_image hbP hMpos hMr
    (fun z hz => hΦagree z (hsubM hz))
  refine ⟨{
    ξ₀ := d.ξ₀
    φ := d.φ
    Dφ := d.Dφ
    Φ := fun z => Φ z - cl
    Ωp := Petal rp M
    η₀ := d.η₀
    ξ₀_pos := d.ξ₀_pos
    Dφ_open := d.Dφ_open
    Q_sub := d.Q_sub
    exhaust := d.exhaust
    left_inv := d.left_inv
    succ_iff := d.succ_iff
    φ_holo := d.φ_holo
    Q_maps := d.Q_maps
    φ_abel := d.φ_abel
    φ_inj := d.φ_inj
    φ_asymp := d.φ_asymp
    Φ_holo := hΦholo.sub_const cl
    Φ_abel := fun z hz => by
      show Φ (f₀ z) - cl = (Φ z - cl) + 1
      rw [hΦabel z hz]; ring
    Ωp_open := Work.FatouCoord.isOpen_Petal
    Ωp_sub := fun z hz => hpetalbasin (hsubM hz)
    Ωp_maps := hmapM
    Φ_inj := fun a ha b hb hab =>
      hΦinjP (hsubM ha) (hsubM hb) (by
        have h : Φ a - cl + cl = Φ b - cl + cl := congrArg (fun z => z + cl) hab
        simpa using h)
    basin_enter := fun z hz hzne => basin_enter_petal hbP hMpos z hz hzne
    flower := flower_petal (f := f₀) hrp hMpos d.cover
    Ωp_conn := hextras.1
    Ωp_sc := hextras.2.1
    Ωp_unif := hunifM
    Φ_image := fun b => by
      obtain ⟨C, hC⟩ := hextras.2.2 (b + |cl.im|)
      refine ⟨C - cl.re, fun w hw hwb => ?_⟩
      have hwb' : |(w + cl).im| ≤ b + |cl.im| := by
        rw [Complex.add_im]
        linarith [abs_add_le w.im cl.im]
      obtain ⟨z, hz, hzΦ⟩ := hC (w + cl) (by simp only [Complex.add_re]; linarith) hwb'
      exact ⟨z, hz, by
        show Φ z - cl = w
        rw [hzΦ]; ring⟩
    ends_sub := d.ends_sub
    E_upper := by
      have h := hUp.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : ℂ => cl) upperEnd (nhds cl))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    E_lower := ⟨cl' - cl, by
      have h := hLo.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : ℂ => cl) lowerEnd (nhds cl))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h⟩
    invOrbit := fun z hzD hz hlim hne => by
      have hf0 : f₀ 0 = 0 := hg.2.2.2.1
      obtain ⟨j₀, hj₀pos, hj₀⟩ := Work.Parab.enterLeft.eventually_mem_left
        (Work.FatouCoord.not_mem_Petal_zero (r := rp) (M := M)) hf0 hconvΩ
        (flower_petal (f := f₀) hrp hMpos d.cover) hz hlim hne
      exact Work.Parab.invOrbit.inv_orbit_QLeft d.Dφ_open (isOpen_QLeft d.ξ₀) d.Q_sub
        (fun w hw => QLeft_sub_one_local d.ξ₀ hw) d.left_inv d.succ_iff
        d.φ_abel d.preimage_far d.φ_holo d.φ_inj hfinj d.φ_asymp hzD hz hlim
        ⟨j₀, hj₀pos, hj₀⟩
    -- (lead 10-03) the former field horn_basin is now the theorem Work.Horn.horn_basin_thm about any d
    -- (MandelDim.HornBasinClause); see Submission/Work/Horn/HB/DESIGN.md.
    orbit_avoid := _hnd }⟩

end

end Work.Parab
