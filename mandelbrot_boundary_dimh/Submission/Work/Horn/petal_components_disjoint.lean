import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.flower_q

set_option linter.unusedVariables false

/-!
# Disjointness of the components of the basin carrying different petals

Given a map `g` with an open domain `Dg` and finitely many pairwise disjoint, forward invariant
sets `V i ⊆ Dg`, assume that

* every orbit in the parabolic basin of `g` eventually enters `⋃ i, V i` (`hcapture`), and
* the "which `V i` is entered" index is locally constant on the basin (`hindex`).

Then the connected components of the basin through `y i ∈ V i` and `y j ∈ V j` are disjoint for
`i ≠ j`.  Indeed the orbit of a point of the basin can visit at most one of the `V i` (they are
disjoint and forward invariant, so a later visit is a forward iterate of an earlier one), so the
basin splits into the clopen "index" pieces `{z | the orbit of z enters V i}`; on those the index
function `Ind` is locally constant, hence constant on every preconnected set, in particular on a
connected component of the basin.  Since `Ind (y i) = i` (witness `n = 0`), the component of `y i`
consists entirely of points of index `i`, and likewise for `j`.
-/

namespace Work.Horn

open Filter Topology

theorem petal_components_disjoint {g : ℂ → ℂ} {Dg : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (y : Fin q → ℂ) (hy : ∀ i, y i ∈ V i)
    (hDg : IsOpen Dg)
    (hVmap : ∀ i, Set.MapsTo g (V i) (V i))
    (hVsub : ∀ i, V i ⊆ Dg)
    (hcapture : ∀ z ∈ MandelDim.ParabolicBasin g Dg, ∃ n : ℕ, g^[n] z ∈ ⋃ i, V i)
    (hindex : ∀ z ∈ MandelDim.ParabolicBasin g Dg, ∃ U ∈ nhds z, ∀ w' ∈ U, ∀ i : Fin q,
      ((∃ n : ℕ, g^[n] z ∈ V i) ↔ (∃ n : ℕ, g^[n] w' ∈ V i)))
    (hdisj : ∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j)) :
    ∀ i j : Fin q, i ≠ j →
      Disjoint (connectedComponentIn (MandelDim.ParabolicBasin g Dg) (y i))
        (connectedComponentIn (MandelDim.ParabolicBasin g Dg) (y j)) := by
  classical
  -- The set of indices visited by the orbit of a basin point is nonempty (`hcapture`) and a
  -- singleton: if `g^[n] z ∈ V k` and `g^[m] z ∈ V k'` then the later visit is a forward iterate
  -- of the earlier one (forward invariance of `V k`), so `V k ∩ V k' ≠ ∅` and `k = k'`.
  have hex : ∀ z : MandelDim.ParabolicBasin g Dg, ∃! k : Fin q, ∃ n : ℕ, g^[n] (z : ℂ) ∈ V k := by
    intro z
    obtain ⟨n, hn⟩ := hcapture (z : ℂ) z.2
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hn
    refine ⟨k, ⟨n, hk⟩, fun k' hk' => ?_⟩
    obtain ⟨m, hm⟩ := hk'
    rcases le_total n m with hnm | hmn
    · have hmem : g^[m] (z : ℂ) ∈ V k := by
        have h1 := (hVmap k).iterate (m - n) hk
        rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hnm] at h1
      by_contra hkk'
      exact (Set.disjoint_left.mp (hdisj k k' fun h => hkk' h.symm) hmem) hm
    · have hmem : g^[n] (z : ℂ) ∈ V k' := by
        have h1 := (hVmap k').iterate (n - m) hm
        rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hmn] at h1
      by_contra hkk'
      exact (Set.disjoint_left.mp (hdisj k' k hkk') hmem) hk
  -- The index of a basin point.
  let Ind : MandelDim.ParabolicBasin g Dg → Fin q := fun z => (hex z).choose
  have hInd_spec : ∀ z, ∃ n : ℕ, g^[n] (z : ℂ) ∈ V (Ind z) := fun z => (hex z).choose_spec.1
  have hInd_eq : ∀ (z : MandelDim.ParabolicBasin g Dg) (k : Fin q),
      (∃ n : ℕ, g^[n] (z : ℂ) ∈ V k) → Ind z = k := by
    intro z k hk
    exact ((hex z).choose_spec.2 k hk).symm
  -- `Ind` is locally constant on the basin: `hindex` says that the set of indices visited is
  -- constant on a neighbourhood, and that set has only one element.
  have hloc : IsLocallyConstant Ind := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    obtain ⟨U, hU, hUprop⟩ := hindex (z : ℂ) z.2
    refine Filter.mem_of_superset
      (ContinuousAt.preimage_mem_nhds (continuous_subtype_val.continuousAt) hU) ?_
    intro w hw
    exact hInd_eq w (Ind z) ((hUprop (w : ℂ) hw (Ind z)).mp (hInd_spec z))
  -- Hence `Ind` is constant on the basin component of each `y k`, where it equals `k`.
  have key : ∀ (k : Fin q) (w : MandelDim.ParabolicBasin g Dg),
      y k ∈ MandelDim.ParabolicBasin g Dg →
      (w : ℂ) ∈ connectedComponentIn (MandelDim.ParabolicBasin g Dg) (y k) → Ind w = k := by
    intro k w hyk hw
    rw [connectedComponentIn_eq_image hyk] at hw
    obtain ⟨u, hu, hueq⟩ := hw
    have huw : u = w := Subtype.ext hueq
    have hbase : Ind (⟨y k, hyk⟩ : MandelDim.ParabolicBasin g Dg) = k :=
      hInd_eq _ k ⟨0, by simpa using hy k⟩
    rw [← huw]
    exact (hloc.apply_eq_of_isPreconnected
      (isPreconnected_connectedComponent (x := (⟨y k, hyk⟩ : MandelDim.ParabolicBasin g Dg)))
      hu (mem_connectedComponent (x := (⟨y k, hyk⟩ : MandelDim.ParabolicBasin g Dg)))).trans hbase
  intro i j hij
  rw [Set.disjoint_left]
  intro z hzi hzj
  by_cases hyi : y i ∈ MandelDim.ParabolicBasin g Dg
  · have hzB : z ∈ MandelDim.ParabolicBasin g Dg := connectedComponentIn_subset _ _ hzi
    by_cases hyj : y j ∈ MandelDim.ParabolicBasin g Dg
    · exact hij ((key i ⟨z, hzB⟩ hyi hzi).symm.trans (key j ⟨z, hzB⟩ hyj hzj))
    · rw [connectedComponentIn_eq_empty hyj] at hzj
      exact hzj
  · rw [connectedComponentIn_eq_empty hyi] at hzi
    exact hzi

end Work.Horn
