import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.germ_expansion
import Submission.Work.Horn.flower_q_component_nz
import Submission.Work.Horn.petal_spread_component
import Submission.Work.Horn.Dg_pieces
import Submission.Work.Horn.basin_basic_Dg
import Submission.Work.Horn.zero_not_mem_basin_pushdown
import Submission.Work.Horn.hopen_Dg

namespace Work.Horn

/-!
# `Work.Horn.petal_components_upper_local`

The petal data of the pushed-down horn map `g = pushdown d.E` on `D_g = {0} ∪ π '' (Bu ∪ Bl)`:
for the Leau–Fatou flower `V : Fin q → Set ℂ` of the germ of `g` at `0`
(`Work.Horn.flower_q_component_nz`, with `q` from `Work.Horn.germ_expansion`), the components
`B' i` of the parabolic basin `P` carrying the petals are

* contained in `P`,
* components of `P` (`B' i = connectedComponentIn P z`),
* `g`-invariant (`MapsTo g (B' i) (B' i)`),
* a "trap" for every basin orbit (every `P`-point has an iterate in some `B' i`), and
* contained in the bounded *upper* piece `{0} ∪ π '' BuOf d B` (no-crossing of `D_g`, since the
  petals accumulate at `0 ∈ {0} ∪ π '' BuOf` while the lower piece `π '' BlOf` is separated from
  `0`).

This is the input `Work.Horn.basin_components_infinite` consumes through
`Work.HornB.components_infinite_abstract`; the delegation of the same statement lives in
`Submission/Work/HornB/petal_components_in_upper.lean`.
-/

open Set Filter Topology
open scoped Topology

noncomputable section

set_option maxHeartbeats 2000000

theorem petal_components_upper_local {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    ∃ (q : ℕ) (B' : Fin q → Set ℂ),
      (∀ i, B' i ⊆ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) ∧
      (∀ i, ∃ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))),
        B' i = connectedComponentIn (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) z) ∧
      (∀ i, Set.MapsTo (MandelDim.pushdown d.E) (B' i) (B' i)) ∧
      (∀ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))), ∃ n : ℕ, ∃ i : Fin q,
        (MandelDim.pushdown d.E)^[n] z ∈ B' i) ∧
      (∀ i, B' i ⊆ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))) := by
  classical
  obtain ⟨hBuO, hBlO, hBuT, hBlT, hup₀, hlo₀, hsub₀⟩ :=
    horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hBu_eq : Bu = MandelDim.BuOf d B := Bu_eq_BuOf d hBu hup hup₀
  have hBl_eq : Bl = MandelDim.BlOf d B := Bl_eq_BlOf d hBl hlo hlo₀
  obtain ⟨c, hsetup⟩ := isF0Setup_of_immediateBasin hF0 d hB hBne
  have hDg : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hg : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    zero_not_mem_basin_pushdown hF0 d hB hBne hBu hBl hsub hup hlo
  have h0 : (0 : ℂ) ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := Set.mem_insert _ _
  have hfix : MandelDim.pushdown d.E 0 = 0 := MandelDim.pushdown_zero d.E
  have hd1 : deriv (MandelDim.pushdown d.E) 0 = 1 := MandelDim.deriv_pushdown_E d
  have hρ : 0 < Real.exp (-(2 * Real.pi * d.η₀)) := Real.exp_pos _
  have hgball : DifferentiableOn ℂ (MandelDim.pushdown d.E)
      (Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi * d.η₀)))) := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact (pushdown_hasDerivAt_zero f₀ D₀ d).differentiableAt.differentiableWithinAt
    · have hnhds : Metric.ball (0 : ℂ) (Real.exp (-(2 * Real.pi * d.η₀))) \ {0} ∈ nhds z :=
        (Metric.isOpen_ball.inter isClosed_singleton.isOpen_compl).mem_nhds
          ⟨hz, by simpa using hz0⟩
      exact (((pushdown_differentiableOn_punctured f₀ D₀ d) z
        ⟨hz, hz0⟩).differentiableAt hnhds).differentiableWithinAt
  have hnz : ¬ (∀ᶠ ζ in nhds (0 : ℂ), MandelDim.pushdown d.E ζ = ζ) :=
    pushdown_not_eventually_id d hsetup
  obtain ⟨q, hq, a, ha, hgerm⟩ := germ_expansion hρ hgball hfix hd1 hnz
  have hopen : ∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      ∀ U ∈ nhds z, MandelDim.pushdown d.E '' U ∈ nhds (MandelDim.pushdown d.E z) := by
    have hset : insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) =
        insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) := by
      rw [hBu_eq, hBl_eq]
    rw [hset]
    exact hopen_Dg hF0 d hB hBne
  obtain ⟨V, hV1, hV0, hVmap, hVdisj, hVcl, hVinj, hVcapture, hVreach, hVindex⟩ :=
    flower_q_component_nz hDg h0 hg hq ha hfix hopen hgerm
  obtain ⟨B', hB1, hB2, hB3, hB4, hB5, hB6, hB7⟩ :=
    petal_spread_component hDg hg (fun i => (hV1 i).1) (fun i => (hV1 i).2.1)
      (fun i => (hV1 i).2.2) hVmap hVdisj hVcl hVcapture hVreach hVindex h0out
  obtain ⟨hUopen, hUbdd, hUconn, hUVeq, hUVdisj, hcross⟩ := Dg_pieces hF0 d hB hBne
  have hPsub : MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ⊆
      insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := by
    intro z hz
    obtain ⟨U, hU, hmap, -⟩ := hz
    exact hmap 0 (mem_of_mem_nhds hU)
  have hVsubDgOf : ∀ i, V i ⊆ insert 0 (MandelDim.piExp ''
      (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) := by
    intro i z hz
    have h := (hV1 i).2.2 hz
    rwa [hBu_eq, hBl_eq] at h
  have hVmeetU : ∀ i, (V i ∩ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))).Nonempty := by
    intro i
    by_contra hcon
    have hVsubV : V i ⊆ MandelDim.piExp '' (MandelDim.BlOf d B) := by
      intro z hz
      have hz' := hVsubDgOf i hz
      rw [hUVeq] at hz'
      rcases hz' with h | h
      · exact absurd ⟨z, hz, h⟩ hcon
      · exact h
    have h0in : (0 : ℂ) ∈ closure (MandelDim.piExp '' (MandelDim.BlOf d B)) :=
      closure_mono hVsubV (hVcl i)
    -- an open set disjoint from `S` is disjoint from `closure S`
    have hclsub : closure (MandelDim.piExp '' (MandelDim.BlOf d B)) ⊆
        (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)))ᶜ := by
      intro x hx hxU
      rw [Metric.mem_closure_iff] at hx
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hUopen x hxU
      obtain ⟨y, hyS, hyx⟩ := hx ε hε
      exact Set.disjoint_left.mp hUVdisj (hεU (Metric.mem_ball.mpr (by rw [dist_comm]; exact hyx))) hyS
    exact hclsub h0in (Set.mem_insert _ _)
  have hBcomp : ∀ i, ∃ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))),
      B' i = connectedComponentIn (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) z := by
    intro i
    obtain ⟨z, hz⟩ := (hV1 i).2.1.nonempty
    have hzB : z ∈ B' i := hB3 i hz
    have hzP : z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := hB4 i hzB
    refine ⟨z, hzP, le_antisymm ?_ ?_⟩
    · exact IsPreconnected.subset_connectedComponentIn (hB2 i).isPreconnected hzB (hB4 i)
    · exact hB5 i _ isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
        ⟨z, hzB, mem_connectedComponentIn hzP⟩
  have hBreach : ∀ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))), ∃ n : ℕ, ∃ i : Fin q,
      (MandelDim.pushdown d.E)^[n] z ∈ B' i := by
    intro z hz
    obtain ⟨n, hn⟩ := hVcapture z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hn
    exact ⟨n, i, hB3 i hi⟩
  refine ⟨q, B', hB4, hBcomp, hB6, hBreach, ?_⟩
  intro i
  refine hcross (B' i) (hB2 i).isPreconnected ?_ ?_
  · intro z hz
    have h := hPsub (hB4 i hz)
    rwa [hBu_eq, hBl_eq] at h
  · obtain ⟨z, hzV, hzU⟩ := hVmeetU i
    exact ⟨z, hB3 i hzV, hzU⟩

end

end Work.Horn
