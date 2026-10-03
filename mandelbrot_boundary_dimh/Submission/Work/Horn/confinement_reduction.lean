import Mathlib
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.spread_proper
import Submission.Work.Horn.spread_surj_on_component
import Submission.Work.Horn.basin_basic_Dg

/-!
# `BasinDatum` from the `ParabData.horn_basin` field

`Work.Horn.horn_germ_F0` reduces (sessions 15–17, `NOTES_GERM_F0.md` §70) to `BasinDatum` for the
`g`-invariant component `B'` of the parabolic basin of `g = pushdown d.E` on
`D_g = {0} ∪ π(Bu ∪ Bl)`.  The horn-specific geometry that makes `g` proper on that component —
Shishikura's "`g₀ : V_{n+1} → V_n` is a branched covering with at most one critical point /
`deg g₀|_{V_n}` is eventually constant", equivalently the per-component confinement
`closure (B' ∩ g ⁻¹' L) ⊆ {0} ∪ π (DE)` — is carried by the objects and is now a field of
`MandelDim.ParabData` (`MandelDim.ParabData.horn_basin`), supplied by the §4.1/A.3 construction.

This file derives `BasinDatum` from that field.  Proof route: the field gives a component `B'` of
the basin that is `g`-invariant, proper, simply connected and contains a critical point of `g`;
properness gives the remaining clause `B' ⊆ g '' B'` of `IsImmediateBasin`
(`Work.Horn.spread_surj_on_component`), while openness, connectedness and maximality are the
component properties (`basin_basic_Dg`, `component_closed_in`).
-/

namespace Work.Horn

open Set Filter Topology
open scoped Topology

noncomputable section

/-- **`BasinDatum` from the `horn_basin` field.**  For the canonical end components
`BuOf d B`, `BlOf d B` of `φ⁻¹ B ∩ Dφ`, the field `d.horn_basin` supplies a `g`-invariant, proper,
simply connected component of the parabolic basin carrying a critical point of `g`; hence
`BasinDatum` for the target's data (whose `Bu`, `Bl` are these components, `Work.Horn.Bu_eq_BuOf`
and `Work.Horn.Bl_eq_BlOf`). -/
theorem basinDatum_of_horn_basin {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hhb : MandelDim.HornBasinClause d) :
    BasinDatum (d := d) (η := η) (Bu := Bu) (Bl := Bl) := by
  classical
  obtain ⟨hBuO, hBlO, -, -, hup₀, hlo₀, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hBu_eq : Bu = MandelDim.BuOf d B := Bu_eq_BuOf d hBu hup hup₀
  have hBl_eq : Bl = MandelDim.BlOf d B := Bl_eq_BlOf d hBl hlo hlo₀
  -- the field, instantiated at the canonical components
  have hBtil : d.φ ⁻¹' B ∩ d.Dφ = MandelDim.Btil d B := by
    ext w; simp [MandelDim.Btil, and_comm]
  have hdom : insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B))
      = insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := by
    rw [hBu_eq, hBl_eq]
  obtain ⟨B', hB'comp₀, hB'map₀, hB'prop₀, hB'sc, hcrit₀⟩ :=
    hhb hF0 B hB (MandelDim.BuOf d B) (MandelDim.BlOf d B)
      (by rw [hBtil]; rfl) (by rw [hBtil]; rfl)
  -- `MandelDim.ParabData.E d` is definitionally `fun w => d.Φ (d.φ w)`: fold it, and move the
  -- domain to the target's `Bu`, `Bl`.
  obtain ⟨z₀, hz₀P₀, hB'eq₀⟩ := hB'comp₀
  have hz₀P : z₀ ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := by
    rw [hdom] at hz₀P₀; exact hz₀P₀
  have hB'eq : B' = connectedComponentIn (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) z₀ := by
    rw [hdom] at hB'eq₀; exact hB'eq₀
  have hB'map : Set.MapsTo (MandelDim.pushdown d.E) B' B' := hB'map₀
  have hB'prop : ∀ L : Set ℂ, L ⊆ B' → IsCompact L →
      IsCompact (B' ∩ (MandelDim.pushdown d.E) ⁻¹' L) := hB'prop₀
  have hcrit : ∃ z ∈ B', deriv (MandelDim.pushdown d.E) z = 0 := hcrit₀
  refine ⟨B', ?_, hB'sc, hcrit⟩
  -- the remaining `IsImmediateBasin` clauses
  obtain ⟨hBuO', hBlO', -, -, -, -, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hDg : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO' hBlO' hup hlo
  obtain ⟨hPopen, _, -⟩ := basin_basic_Dg hF0 d hB hBne hBu hBl hsub hup hlo
  have hB'sub : B' ⊆ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := by
    rw [hB'eq]; exact connectedComponentIn_subset _ _
  have hB'open : IsOpen B' := by rw [hB'eq]; exact hPopen.connectedComponentIn
  have hB'conn : IsConnected B' := by
    rw [hB'eq]; exact isConnected_connectedComponentIn_iff.mpr hz₀P
  have hmax : ∀ C : Set ℂ, IsPreconnected C →
      C ⊆ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) →
      (B' ∩ C).Nonempty → C ⊆ B' := by
    intro C hCpre hCsub hmeet
    obtain ⟨y, hyB', hyC⟩ := hmeet
    have hycc : y ∈ connectedComponentIn (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) z₀ := by rw [← hB'eq]; exact hyB'
    have heq := connectedComponentIn_eq hycc
    rw [hB'eq, heq]
    exact IsPreconnected.subset_connectedComponentIn hCpre hyC hCsub
  have hsurj : B' ⊆ MandelDim.pushdown d.E '' B' := by
    have h := spread_surj_on_component hF0 d hB hBne hBu hBl hsub hup hlo (q := 1)
      (B' := fun _ : Fin 1 => B')
      (fun _ => by rw [hB'eq]; exact ⟨z₀, hz₀P, rfl⟩)
      (fun _ => hB'map) (fun _ L hL hLc => hB'prop L hL hLc)
    exact h 0
  exact ⟨hB'open, hB'conn, hB'sub, hmax, hB'map, hsurj, hB'prop⟩

end

end Work.Horn
