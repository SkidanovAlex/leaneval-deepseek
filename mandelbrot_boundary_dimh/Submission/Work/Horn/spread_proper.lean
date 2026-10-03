import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.bdry_Dg
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.basin_basic_Dg
import Submission.Work.Horn.pushdown_fiber_bounded
import Submission.Work.Horn.pushdown_preimage_isBounded_of_isCompact
import Submission.Work.Horn.Dg_pieces

/-!
# `Work.Horn.spread_proper` — the properness clause of `IsImmediateBasin` from the confinement

Assembly of the last clause of `MandelDim.IsImmediateBasin (pushdown d.E) D_g B'`,

    ∀ L ⊆ B', IsCompact L → IsCompact (B' ∩ g ⁻¹' L)

from the single geometric input (Shishikura's unproved "`g₀ : V_{n+1} → V_n` is a proper branched
covering" content, here in the weakest usable form)

    closure (B' ∩ g ⁻¹' L) ⊆ insert 0 (π '' d.DE)      for every compact L ⊆ B',

using the two exact reductions of `Work.Horn.bdry_Dg`:

* `piExp_DE_inter_closure_subset`: `π '' d.DE ∩ closure D_g ⊆ D_g` (so the confinement implies
  `closure (B' ∩ g ⁻¹' L) ⊆ D_g`);
* `isCompact_inter_preimage_iff_closure_subset`: for a component `B'` of the basin,
  `IsCompact (B' ∩ g ⁻¹' L) ↔ closure (B' ∩ g ⁻¹' L) ⊆ D_g`.

The boundedness of the preimage of a compact set (the lower-end contraction `g ζ ≈ π cl · ζ`)
is supplied by the PROVED `Work.Horn.pushdown_preimage_isBounded_of_isCompact`.
-/

namespace Work.Horn

open MandelDim Set Filter Topology Metric
open scoped Topology

noncomputable section

/-- The immediate basin is closed in the parabolic basin. -/
theorem isImmediateBasin_closed_in_basin {f : ℂ → ℂ} {D B : Set ℂ}
    (hB : MandelDim.IsImmediateBasin f D B) :
    ∀ y ∈ MandelDim.ParabolicBasin f D, y ∈ closure B → y ∈ B := by
  intro y hyb hycl
  obtain ⟨-, -, -, hBmax, -⟩ := hB
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    ((Work.HornCov.isOpen_parabolicBasin f D).mem_nhds hyb)
  have hCball : Metric.ball y ε ⊆ connectedComponentIn (MandelDim.ParabolicBasin f D) y :=
    IsPreconnected.subset_connectedComponentIn isPreconnected_ball
      (Metric.mem_ball_self hε) hεsub
  have hmeet : (B ∩ connectedComponentIn (MandelDim.ParabolicBasin f D) y).Nonempty := by
    obtain ⟨b, hb, hbd⟩ := Metric.mem_closure_iff.mp hycl ε hε
    exact ⟨b, hb, hCball (Metric.mem_ball.mpr (by rw [dist_comm]; exact hbd))⟩
  exact hBmax _ isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) hmeet
    (mem_connectedComponentIn hyb)

/-- A component of an open set is closed in that set. -/
theorem component_closed_in {S : Set ℂ} (hS : IsOpen S) (v : ℂ) :
    ∀ y ∈ S, y ∈ closure (connectedComponentIn S v) → y ∈ connectedComponentIn S v := by
  intro y hyS hycl
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hyS)
  obtain ⟨v', hv', hvd⟩ := Metric.mem_closure_iff.mp hycl ε hε
  have hball : Metric.ball y ε ⊆ connectedComponentIn S y :=
    IsPreconnected.subset_connectedComponentIn isPreconnected_ball
      (Metric.mem_ball_self hε) (fun z hz => hεsub hz)
  have hv'comp : v' ∈ connectedComponentIn S y :=
    hball (Metric.mem_ball.mpr (by rw [dist_comm]; exact hvd))
  exact ((connectedComponentIn_eq hv').trans (connectedComponentIn_eq hv'comp).symm) ▸
    mem_connectedComponentIn hyS

/-- **The properness clause of `MandelDim.IsImmediateBasin` for the pushed-down horn map, from the
confinement.** -/
theorem isCompact_inter_preimage_of_confinement {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (hF0 : MandelDim.InF0 f₀ D₀) (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ}
    (hB : MandelDim.IsImmediateBasin f₀ D₀ B) (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    {B' : Set ℂ}
    (hB'sub : B' ⊆ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))))
    (hB'cl : ∀ y ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))), y ∈ closure B' → y ∈ B')
    (hconf : ∀ L : Set ℂ, L ⊆ B' → IsCompact L →
      closure (B' ∩ (MandelDim.pushdown d.E) ⁻¹' L) ⊆
        insert 0 (MandelDim.piExp '' d.DE)) :
    ∀ L : Set ℂ, L ⊆ B' → IsCompact L →
      IsCompact (B' ∩ (MandelDim.pushdown d.E) ⁻¹' L) := by
  obtain ⟨hBuO, hBlO, hBuT, hBlT, -, -, -⟩ :=
    horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hDopen : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hg : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  obtain ⟨-, -, hback⟩ := basin_basic_Dg hF0 d hB hBne hBu hBl hsub hup hlo
  -- `B' ⊆ D_g`
  have hB'subD : B' ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := by
    intro z hz
    obtain ⟨U, hU, hiter, -⟩ := hB'sub hz
    simpa using hiter 0 (mem_of_mem_nhds hU)
  -- identify `Bu`, `Bl` with components of `Btil`
  have hBtil : d.φ ⁻¹' B ∩ d.Dφ = MandelDim.Btil d B := by
    ext w; simp [MandelDim.Btil, and_comm]
  have hBu_cl : ∀ y ∈ MandelDim.Btil d B, y ∈ closure Bu → y ∈ Bu := by
    intro y hyB hcl
    rw [hBu, hBtil] at hcl ⊢
    exact component_closed_in (isOpen_Btil d hB.1) _ y hyB hcl
  have hBl_cl : ∀ y ∈ MandelDim.Btil d B, y ∈ closure Bl → y ∈ Bl := by
    intro y hyB hcl
    rw [hBl, hBtil] at hcl ⊢
    exact component_closed_in (isOpen_Btil d hB.1) _ y hyB hcl
  have hBu_sub : Bu ⊆ MandelDim.Btil d B := by
    rw [hBu, hBtil]
    exact connectedComponentIn_subset _ _
  have hBl_sub : Bl ⊆ MandelDim.Btil d B := by
    rw [hBl, hBtil]
    exact connectedComponentIn_subset _ _
  obtain ⟨cl, hcl⟩ := d.E_lower
  intro L hL hLc
  refine (isCompact_inter_preimage_iff_closure_subset hDopen hg hB'subD hB'sub hB'cl
    (fun z hz hgz => hback z hz hgz) hL hLc
    ((pushdown_preimage_isBounded_of_isCompact d hcl hLc).subset
      Set.inter_subset_right)).mpr ?_
  intro x hx
  have hx' : x ∈ insert 0 (MandelDim.piExp '' d.DE) := hconf L hL hLc hx
  rcases Set.mem_insert_iff.mp hx' with rfl | hxDE
  · exact Or.inl rfl
  · have hxDg : x ∈ closure (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
      closure_mono (fun z hz => hB'subD hz.1) hx
    exact piExp_DE_inter_closure_subset d hB.1
      (isImmediateBasin_closed_in_basin hB)
      hBu_sub hBuO hBu_cl hBuT hBl_sub hBlO hBl_cl hBlT ⟨hxDE, hxDg⟩

end

end Work.Horn
