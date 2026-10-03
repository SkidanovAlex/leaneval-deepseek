import Mathlib
import Submission.Work.Horn.fiber_infinite_in_basin
import Submission.Work.Horn.basin_basic_Dg
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.pushdown_not_locally_const
import Submission.Work.Horn.E_not_locally_const

open MandelDim Set Metric Filter
open scoped Topology

namespace Work.Horn

noncomputable section

/-!
# `Work.Horn.not_immediateBasin_of_connected`

If the parabolic basin of the pushed-down horn map `g = pushdown d.E` on its domain
`D_g = {0} ∪ π(Bu ∪ Bl)` is preconnected, then `g` has **no** immediate basin on `D_g`.

The proof is a general obstruction: an immediate basin `B'` is a preconnected, nonempty subset of
the basin, so the maximality clause of `IsImmediateBasin` applied to the whole (preconnected) basin
forces `B' = basin`.  The properness clause then makes every fibre `B' ∩ g ⁻¹' {w}` over `w ∈ B'`
compact; but `Work.Horn.pushdown_fiber_infinite_in_basin` says the fibre of a nonzero basin point
inside the basin is infinite.  An infinite compact set has an accumulation point, at which `g`
would be locally constant (isolated-zeros principle), contradicting the fact that `g` is nowhere
locally constant on `D_g` (extracted here from the argument of `Work.Horn.basin_basic_Dg`).
-/

/-- The pushed-down horn map `g = pushdown d.E` is nowhere locally constant on its domain
`{0} ∪ π (Bu ∪ Bl)`.  This is the local-constancy input of `Work.Horn.basin_basic_Dg`, isolated for
reuse: at `0` it uses the normalisation `g'(0) = 1`; at `π w` with `w ∈ Bu ∪ Bl` it descends from
`Work.Horn.E_not_locally_const` through `π`. -/
theorem pushdown_not_locally_const_Dg {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    ∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      ¬ (∀ᶠ u in nhds z, MandelDim.pushdown d.E u = MandelDim.pushdown d.E z) := by
  obtain ⟨hBuO, hBlO, hBuT, hBlT, -, -, -⟩ :=
    horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hDEo : IsOpen d.DE := by
    rw [show d.DE = d.Dφ ∩ d.φ ⁻¹' MandelDim.ParabolicBasin f₀ D₀ from rfl]
    exact d.φ_holo.continuousOn.isOpen_inter_preimage d.Dφ_open (isOpen_parabolicBasin f₀ D₀)
  have hT : MandelDim.IsTInvariant (Bu ∪ Bl) := by
    intro u
    simp only [Set.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl ((hBuT u).mp h)
      · exact Or.inr ((hBlT u).mp h)
    · rintro (h | h)
      · exact Or.inl ((hBuT u).mpr h)
      · exact Or.inr ((hBlT u).mpr h)
  have heq : ∀ u ∈ Bu ∪ Bl, u + 1 ∈ Bu ∪ Bl → d.E (u + 1) = d.E u + 1 :=
    fun u hu _ => MandelDim.ParabData.E_add_one d (hsub hu) (hsub ((hT u).mp hu))
  intro z hz
  rcases Set.mem_insert_iff.mp hz with rfl | hz'
  · -- the germ at `0`, where `g'(0) = 1`
    intro hloc
    have hEq : (fun _ : ℂ => MandelDim.pushdown d.E 0) =ᶠ[𝓝 (0 : ℂ)]
        (MandelDim.pushdown d.E) := by
      filter_upwards [hloc] with ζ hζ using hζ.symm
    have hz0 : deriv (MandelDim.pushdown d.E) 0 = 0 := by
      rw [← hEq.deriv_eq]
      simp
    rw [Work.Horn.MandelDim.deriv_pushdown_E d] at hz0
    exact one_ne_zero hz0
  · -- the points of `π '' (Bu ∪ Bl)`, by descent from the lifted horn map
    obtain ⟨w, hw, rfl⟩ := hz'
    have hcont : ContinuousAt d.E w :=
      (Work.Horn.differentiableOn_E d).continuousOn.continuousAt (hDEo.mem_nhds (hsub hw))
    exact pushdown_not_locally_const hT heq hw ((hBuO.union hBlO).mem_nhds hw) hcont
      (E_not_locally_const d hBu hBl hsub hup hlo w hw)

/-- **If the basin of `g = pushdown d.E` on `D_g = {0} ∪ π(Bu ∪ Bl)` is preconnected, then `g` has
no immediate basin on `D_g`.** -/
theorem not_immediateBasin_of_connected {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hV : ∃ w : ℂ, w ≠ 0 ∧ w ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))))
    (hconn : IsPreconnected (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))))) :
    ¬ ∃ B' : Set ℂ, MandelDim.IsImmediateBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) B' := by
  rintro ⟨B', hB'⟩
  obtain ⟨hB'open, hB'conn, hB'sub, hB'max, hB'map, hB'surj, hB'prop⟩ := hB'
  obtain ⟨hBuO, hBlO, -, -, -, -, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  -- `B'` is a nonempty preconnected piece of the basin, so maximality gives `basin ⊆ B'`
  have hbne : B'.Nonempty := hB'conn.nonempty
  have hbasin_sub_B' : MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ⊆ B' := by
    refine hB'max _ hconn (subset_refl _) ?_
    obtain ⟨b, hb⟩ := hbne
    exact ⟨b, hb, hB'sub hb⟩
  have hB'_eq : B' = MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := le_antisymm hB'sub hbasin_sub_B'
  -- a nonzero point of the basin
  obtain ⟨w, hw0, hwbasin⟩ := hV
  have hwB' : w ∈ B' := by rw [hB'_eq]; exact hwbasin
  -- properness of `g : B' → B'` makes the fibre over `w` compact
  have hcomp : IsCompact (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ∩ (MandelDim.pushdown d.E) ⁻¹' {w}) := by
    have h1 : IsCompact (B' ∩ (MandelDim.pushdown d.E) ⁻¹' {w}) :=
      hB'prop {w} (by rintro z rfl; exact hwB') isCompact_singleton
    rwa [hB'_eq] at h1
  -- ... while it is infinite
  have hinf : (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ∩ (MandelDim.pushdown d.E) ⁻¹' {w}).Infinite := by
    have h := pushdown_fiber_infinite_in_basin hF0 d hB hBne hBu hBl hsub hup hlo hw0 hwbasin
    rwa [Set.inter_comm] at h
  -- an infinite compact set has an accumulation point
  obtain ⟨x, hxK, hxacc⟩ :=
    hinf.exists_accPt_of_subset_isCompact hcomp (subset_refl _)
  have hxw : (MandelDim.pushdown d.E) x = w :=
    Set.mem_singleton_iff.mp (Set.mem_preimage.mp hxK.2)
  -- at that point `g` is locally constant (isolated-zeros principle)
  have hxacc' : ∃ᶠ u in 𝓝[≠] x, (MandelDim.pushdown d.E) u = (MandelDim.pushdown d.E) x := by
    have h := accPt_iff_frequently_nhdsNE.mp hxacc
    refine h.mono ?_
    intro y hy
    have hyw : (MandelDim.pushdown d.E) y = w :=
      Set.mem_singleton_iff.mp (Set.mem_preimage.mp hy.2)
    rw [hyw, hxw]
  -- `x` lies in the domain of `g`, where `g` is holomorphic
  have hbasin_sub_Dg : MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := by
    intro z hz
    obtain ⟨U, hU, hiter, hconv⟩ := hz
    have hzU : z ∈ U := mem_of_mem_nhds hU
    have h := hiter 0 hzU
    simpa using h
  have hx_Dg : x ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := hbasin_sub_Dg hxK.1
  have han : AnalyticAt ℂ (MandelDim.pushdown d.E) x :=
    (pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo).analyticAt
      ((isOpen_insert_piExp hBuO hBlO hup hlo).mem_nhds hx_Dg)
  have hev : ∀ᶠ u in 𝓝 x, (MandelDim.pushdown d.E) u = (MandelDim.pushdown d.E) x := by
    have h := (AnalyticAt.frequently_eq_iff_eventually_eq
      (f := MandelDim.pushdown d.E) (g := fun _ : ℂ => (MandelDim.pushdown d.E) x)
      han analyticAt_const).mp hxacc'
    simpa using h
  exact (pushdown_not_locally_const_Dg hF0 d hB hBne hBu hBl hsub hup hlo) x hx_Dg hev

end

end Work.Horn
