import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.petal_components_upper_local
import Submission.Work.Horn.petal_spread_component
import Submission.Work.Horn.flower_q_component_nz
import Submission.Work.Horn.Dg_pieces

namespace Work.Horn

open Set Filter Topology
open scoped Topology

noncomputable section

set_option maxHeartbeats 2000000

/-!
# `Work.Horn.petal_family_of_germ_expansion`

Shishikura's Lemma 5.4, *existence of the petal family*: for the pushed-down horn map
`g = pushdown d.E` of an `𝓕₀`-germ with §4.1 data `d`, an immediate basin `B` and the two end
components `Bu`, `Bl` of `φ⁻¹(B) ∩ Dφ`, a germ expansion

  `g ζ = ζ + a ζ^{q+1} + o(ζ^{q+1})`,   `a ≠ 0`, `q ≥ 1`,

produces `q` pairwise disjoint nonempty `g`-invariant components `B' i` of the parabolic basin
`P = ParabolicBasin g (insert 0 (π '' (Bu ∪ Bl)))`, each contained in the bounded upper piece
`{0} ∪ π '' (BuOf d B)`.

This is exactly the hypothesis block of `MandelDim.HornComponentStatement` that the two
`q`-indexed spread constructions supply; unlike `Work.Horn.petal_components_upper_local` the
multiplicity `q` and the coefficient `a` of the germ expansion are *given*, so the assembly below
does not go through `Work.Horn.germ_expansion` (which would only produce `∃ q, …`).  The individual
inputs are used unchanged:

* `Work.Horn.horn_topo_facts`, `Work.Horn.isOpen_insert_piExp`, `Work.Horn.pushdown_g_holo`,
  `Work.Horn.zero_not_mem_basin_pushdown`, `Work.Horn.hopen_Dg` — the structure of `D_g` and `g`;
* `Work.Horn.flower_q_component_nz` — the Leau–Fatou flower `V : Fin q → Set ℂ` for the *given*
  germ expansion, with `0 ∉ V i`, capture and local constancy of the entered index;
* `Work.Horn.petal_spread_component` — the spreads `B' i = connectedComponentIn P (v i)` with
  `V i ⊆ B' i`, `g`-invariance and pairwise disjointness;
* `Work.Horn.Dg_pieces` — `P ⊆ D_g` cannot cross from the upper piece to the lower one, which
  confines `B' i` to `{0} ∪ π '' (BuOf d B)`.
-/

theorem petal_family_of_germ_expansion {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    {q : ℕ} {a : ℂ} (hq : 1 ≤ q) (ha : a ≠ 0)
    (hgerm : Filter.Tendsto (fun z : ℂ => (MandelDim.pushdown d.E z - z - a * z ^ (q + 1)) / z ^ (q + 1))
        (nhdsWithin 0 {0}ᶜ) (nhds 0)) :
    ∃ B' : Fin q → Set ℂ,
      (∀ i, ∃ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))),
        B' i = connectedComponentIn (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) z) ∧
      (∀ i, B' i ⊆ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))) ∧
      (∀ i, B' i ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ∧
      (∀ i, Set.MapsTo (MandelDim.pushdown d.E) (B' i) (B' i)) ∧
      (∀ i j : Fin q, i ≠ j → Disjoint (B' i) (B' j)) ∧
      (∀ i, (B' i).Nonempty) := by
  classical
  -- structure of the horn domain `D_g = {0} ∪ π '' (Bu ∪ Bl)`
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
  -- local openness of `g` on `D_g`
  have hopen : ∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      ∀ U ∈ nhds z, MandelDim.pushdown d.E '' U ∈ nhds (MandelDim.pushdown d.E z) := by
    have hset : insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) =
        insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) := by
      rw [hBu_eq, hBl_eq]
    rw [hset]
    exact hopen_Dg hF0 d hB hBne
  -- the Leau–Fatou flower for the *given* germ expansion `ζ + a ζ^(q+1) + o(ζ^(q+1))`
  obtain ⟨V, hV1, hV0, hVmap, hVdisj, hVcl, hVinj, hVcapture, hVreach, hVindex⟩ :=
    flower_q_component_nz hDg h0 hg hq ha hfix hopen hgerm
  -- the spreads: components of the basin carrying the petals
  obtain ⟨B', hB1, hB2, hB3, hB4, hB5, hB6, hB7⟩ :=
    petal_spread_component hDg hg (fun i => (hV1 i).1) (fun i => (hV1 i).2.1)
      (fun i => (hV1 i).2.2) hVmap hVdisj hVcl hVcapture hVreach hVindex h0out
  -- the basin sits inside its own domain
  have hPsub : MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ⊆
      insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := by
    intro z hz
    obtain ⟨U, hU, hmap, -⟩ := hz
    exact hmap 0 (mem_of_mem_nhds hU)
  -- the two pieces of `D_g`
  obtain ⟨hUopen, hUbdd, hUconn, hUVeq, hUVdisj, hcross⟩ := Dg_pieces hF0 d hB hBne
  have hVsubDgOf : ∀ i, V i ⊆ insert 0 (MandelDim.piExp ''
      (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) := by
    intro i z hz
    have h := (hV1 i).2.2 hz
    rwa [hBu_eq, hBl_eq] at h
  -- every petal meets the bounded upper piece `{0} ∪ π '' BuOf`
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
  -- the `B' i` are components of the basin
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
  refine ⟨B', hBcomp, ?_, ?_, hB6, hB7, ?_⟩
  · -- confinement to the bounded upper piece
    intro i
    refine hcross (B' i) (hB2 i).isPreconnected ?_ ?_
    · intro z hz
      have h := hPsub (hB4 i hz)
      rwa [hBu_eq, hBl_eq] at h
    · obtain ⟨z, hzV, hzU⟩ := hVmeetU i
      exact ⟨z, hB3 i hzV, hzU⟩
  · -- containment in the horn domain
    intro i z hz
    exact hPsub (hB4 i hz)
  · -- nonemptiness
    intro i
    obtain ⟨z, hz⟩ := (hV1 i).2.1.nonempty
    exact ⟨z, hB3 i hz⟩

end

end Work.Horn
