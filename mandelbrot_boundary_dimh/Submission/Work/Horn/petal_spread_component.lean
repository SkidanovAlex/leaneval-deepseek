import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.petal_components_disjoint
import Submission.Work.Horn.petal_image_ne_zero

namespace Work.Horn

open Set Filter Topology

noncomputable section

/-- **The elementary half of the petal-spread construction.**

`G` holomorphic on the open `D`; `V : Fin q → Set ℂ` are disjoint petals in `D`, forward
invariant modulo `0`, accumulating at `0`, which capture every orbit of the parabolic basin and
whose entered index is locally constant on the basin; `0` is not in the basin.

Then for each `i` there is a spread `B i ⊇ V i` which is open, connected, contained in the
parabolic basin, *maximal* among preconnected subsets of the basin meeting it (i.e. a union of
components of the basin), forward invariant (`MapsTo G (B i) (B i)`), and the `B i` are pairwise
disjoint.

This deliberately claims **no** properness and **no** `B i ⊆ G '' B i` — those are the hard,
horn-specific clauses, isolated separately (see `NOTES_GERM_F0.md` §36); with them added this
becomes `MandelDim.IsImmediateBasin`.  Suggested proof: `B i := connectedComponentIn
(ParabolicBasin G D) (v i)` for `v i ∈ V i`; `V i ⊆ ParabolicBasin G D` follows from `hVreach`
with `n = 0`; forward invariance of the basin follows from `hVreach`
(`G^[n-1](G z) = G^[n] z`), and then `G '' B i` is preconnected, inside the basin and meets
`B i` (at `G (v i)`, using that `G (v i) ≠ 0`, which `h0out` forces); disjointness uses
`hVindex` + `hVdisj`. -/
theorem petal_spread_component {G : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (hD : IsOpen D) (hG : DifferentiableOn ℂ G D)
    (hVopen : ∀ i, IsOpen (V i)) (hVconn : ∀ i, IsConnected (V i)) (hVsub : ∀ i, V i ⊆ D)
    (hVmap : ∀ i, ∀ z ∈ V i, G z ∈ V i ∪ {0})
    (hVdisj : ∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j))
    (hVcl : ∀ i, (0 : ℂ) ∈ closure (V i))
    (hVcapture : ∀ z ∈ MandelDim.ParabolicBasin G D, ∃ n : ℕ, G^[n] z ∈ ⋃ i, V i)
    (hVreach : ∀ z ∈ D, (∃ n : ℕ, (∀ k < n, G^[k] z ∈ D) ∧ G^[n] z ∈ ⋃ i, V i) →
      z ∈ MandelDim.ParabolicBasin G D)
    (hVindex : ∀ z ∈ MandelDim.ParabolicBasin G D, ∃ U ∈ nhds z, ∀ w ∈ U, ∀ i : Fin q,
      ((∃ n : ℕ, G^[n] z ∈ V i) ↔ (∃ n : ℕ, G^[n] w ∈ V i)))
    (h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin G D) :
    ∃ B : Fin q → Set ℂ,
      (∀ i, IsOpen (B i)) ∧ (∀ i, IsConnected (B i)) ∧ (∀ i, V i ⊆ B i) ∧
      (∀ i, B i ⊆ MandelDim.ParabolicBasin G D) ∧
      (∀ i, ∀ C : Set ℂ, IsPreconnected C → C ⊆ MandelDim.ParabolicBasin G D →
        (B i ∩ C).Nonempty → C ⊆ B i) ∧
      (∀ i, Set.MapsTo G (B i) (B i)) ∧
      (∀ i j : Fin q, i ≠ j → Disjoint (B i) (B j)) := by
  classical
  -- `hVopen` is not needed for the conclusion (only the reach/capture/index structure is used)
  have _hVopen := hVopen
  -- basic geometry of the basin
  have hBasinOpen : IsOpen (MandelDim.ParabolicBasin G D) := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨U, hU, hmap, hconv⟩ := hz
    obtain ⟨W, hWU, hWopen, hzW⟩ := mem_nhds_iff.mp hU
    exact Filter.mem_of_superset (hWopen.mem_nhds hzW) fun w hw =>
      ⟨U, Filter.mem_of_superset (hWopen.mem_nhds hw) hWU, hmap, hconv⟩
  have hBasinSubD : MandelDim.ParabolicBasin G D ⊆ D := by
    intro z hz
    obtain ⟨U, hU, hmap, -⟩ := hz
    exact hmap 0 (mem_of_mem_nhds hU)
  -- every petal lies in the basin (reach with `n = 0`)
  have hVbasin : ∀ i, V i ⊆ MandelDim.ParabolicBasin G D := by
    intro i z hz
    exact hVreach z (hVsub i hz) ⟨0, fun k hk => by omega,
      by simpa using (Set.mem_iUnion.mpr ⟨i, hz⟩ : z ∈ ⋃ i, V i)⟩
  -- the petals are not only invariant modulo `0`: they are invariant
  have hnozero : ∀ i, ∀ z ∈ V i, G z ≠ 0 :=
    petal_image_ne_zero hD hG hVconn hVsub hVcl hVreach h0out
  have hGV : ∀ i, Set.MapsTo G (V i) (V i) := by
    intro i z hz
    rcases hVmap i z hz with h | h
    · exact h
    · exact absurd h (hnozero i z hz)
  -- the basin is forward invariant
  have hFwd : Set.MapsTo G (MandelDim.ParabolicBasin G D) (MandelDim.ParabolicBasin G D) := by
    intro z hz
    obtain ⟨n, hn⟩ := hVcapture z hz
    obtain ⟨U, hU, hUmap, _hUconv⟩ := hz
    have hiterD : ∀ n : ℕ, G^[n] z ∈ D := fun n => hUmap n (mem_of_mem_nhds hU)
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hn
      have hGVi : G z ∈ V i := hGV i hi
      exact hVreach (G z) (hVsub i hGVi) ⟨0, fun k hk => by omega,
        by simpa using (Set.mem_iUnion.mpr ⟨i, hGVi⟩ : G z ∈ ⋃ i, V i)⟩
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hnpos)
      refine hVreach (G z) (hiterD 1) ⟨m, ?_, ?_⟩
      · intro k _hk
        simpa [Function.iterate_succ_apply, Nat.succ_eq_add_one] using hiterD (k + 1)
      · simpa [hm, Nat.succ_eq_add_one, Function.iterate_succ_apply] using hn
  -- basepoints, one in each petal
  let v : Fin q → ℂ := fun i => (hVconn i).nonempty.choose
  have hv : ∀ i, v i ∈ V i := fun i => (hVconn i).nonempty.choose_spec
  have hBopen : ∀ i, IsOpen (connectedComponentIn (MandelDim.ParabolicBasin G D) (v i)) :=
    fun i => hBasinOpen.connectedComponentIn
  have hBconn : ∀ i, IsConnected (connectedComponentIn (MandelDim.ParabolicBasin G D) (v i)) :=
    fun i => isConnected_connectedComponentIn_iff.mpr (hVbasin i (hv i))
  have hVB : ∀ i, V i ⊆ connectedComponentIn (MandelDim.ParabolicBasin G D) (v i) :=
    fun i => IsPreconnected.subset_connectedComponentIn (hVconn i).isPreconnected (hv i)
      (hVbasin i)
  have hBsub : ∀ i, connectedComponentIn (MandelDim.ParabolicBasin G D) (v i) ⊆
      MandelDim.ParabolicBasin G D := fun i => connectedComponentIn_subset _ _
  have hmax : ∀ i, ∀ C : Set ℂ, IsPreconnected C → C ⊆ MandelDim.ParabolicBasin G D →
      (connectedComponentIn (MandelDim.ParabolicBasin G D) (v i) ∩ C).Nonempty →
      C ⊆ connectedComponentIn (MandelDim.ParabolicBasin G D) (v i) := by
    intro i C hCpre hCsub hmeet
    obtain ⟨y, hyB, hyC⟩ := hmeet
    rw [connectedComponentIn_eq hyB]
    exact IsPreconnected.subset_connectedComponentIn hCpre hyC hCsub
  have hmapsTo : ∀ i, Set.MapsTo G (connectedComponentIn (MandelDim.ParabolicBasin G D) (v i))
      (connectedComponentIn (MandelDim.ParabolicBasin G D) (v i)) := by
    intro i
    have hcont : ContinuousOn G (connectedComponentIn (MandelDim.ParabolicBasin G D) (v i)) :=
      hG.continuousOn.mono fun w hw => hBasinSubD (hBsub i hw)
    have hpre : IsPreconnected (G '' connectedComponentIn (MandelDim.ParabolicBasin G D) (v i)) :=
      isPreconnected_connectedComponentIn.image G hcont
    have hsub : G '' connectedComponentIn (MandelDim.ParabolicBasin G D) (v i) ⊆
        MandelDim.ParabolicBasin G D := by
      rintro w ⟨y, hy, rfl⟩
      exact hFwd (hBsub i hy)
    have hmeet : (connectedComponentIn (MandelDim.ParabolicBasin G D) (v i) ∩
        G '' connectedComponentIn (MandelDim.ParabolicBasin G D) (v i)).Nonempty :=
      ⟨G (v i), hVB i (hGV i (hv i)), ⟨v i, hVB i (hv i), rfl⟩⟩
    exact fun w hw => hmax i _ hpre hsub hmeet ⟨w, hw, rfl⟩
  refine ⟨fun i => connectedComponentIn (MandelDim.ParabolicBasin G D) (v i),
    hBopen, hBconn, hVB, hBsub, hmax, hmapsTo, ?_⟩
  intro i j hij
  exact petal_components_disjoint v hv hD hGV hVsub hVcapture hVindex hVdisj i j hij

end

end Work.Horn
