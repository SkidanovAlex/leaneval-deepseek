import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.PlanarSC.Tools
import Submission.Work.PlanarSC.no_bounded_component_of_simplyConnected
import Submission.Work.PlanarSC.simplyConnected_of_no_bounded_component

/-! Guidance from the project lead (the requester):

AREA PLANAR-SC: prove PlanarInterSCStatement. Route and cost estimate: see `NOTES.md` in this
directory.  The statement is the classical "components of the intersection of two simply connected
plane domains are simply connected", proved through the classical criterion for plane domains

  `SimplyConnectedSpace Ω  ⟺  every component of Ωᶜ is unbounded`

whose two halves are delegated (`PlanarSC/no_bounded_component_of_simplyConnected`,
`PlanarSC/simplyConnected_of_no_bounded_component`) and whose "separation" step is proved here. -/

namespace Work.PlanarSC

open Set Bornology

open MandelDim

/-- Inserting a point of the closure of a preconnected set keeps it preconnected. -/
lemma isPreconnected_insert_of_mem_closure {X : Type*} [TopologicalSpace X] {s : Set X} {q : X}
    (hs : IsPreconnected s) (hq : q ∈ closure s) : IsPreconnected (insert q s) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv huv huvd
  have hsu : s ⊆ u ∪ v := (Set.subset_insert q s).trans huv
  have hsd : s ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro a ha
    exact Set.eq_empty_iff_forall_notMem.mp huvd a
      ⟨Set.mem_insert_iff.mpr (Or.inr ha.1), ha.2⟩
  rcases (isPreconnected_iff_subset_of_disjoint.mp hs u v hu hv hsu hsd) with hsu' | hsv'
  · left
    rcases huv (Set.mem_insert_iff.mpr (Or.inl rfl)) with hqu | hqv
    · exact Set.insert_subset hqu hsu'
    · exfalso
      obtain ⟨w, hwv, hws⟩ := (mem_closure_iff.mp hq) v hv hqv
      exact Set.eq_empty_iff_forall_notMem.mp huvd w
        ⟨Set.mem_insert_iff.mpr (Or.inr hws), hsu' hws, hwv⟩
  · right
    rcases huv (Set.mem_insert_iff.mpr (Or.inl rfl)) with hqu | hqv
    · exfalso
      obtain ⟨w, hwu, hws⟩ := (mem_closure_iff.mp hq) u hu hqu
      exact Set.eq_empty_iff_forall_notMem.mp huvd w
        ⟨Set.mem_insert_iff.mpr (Or.inr hws), hwu, hsv' hws⟩
    · exact Set.insert_subset hqv hsv'

/-- A nonempty bounded subset of `ℂ` has nonempty frontier. -/
lemma nonempty_frontier_of_isBounded {s : Set ℂ} (hne : s.Nonempty) (hb : Bornology.IsBounded s) :
    (frontier s).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  rcases (frontier_eq_empty_iff (s := s)).mp hempty with h1 | h1
  · exact hne.ne_empty h1
  · exfalso
    rw [h1] at hb
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hb
    have h1 : dist (0 : ℂ) (((|C| + 1 : ℝ)) : ℂ) ≤ C := hC (Set.mem_univ _) (Set.mem_univ _)
    have h2 : dist (0 : ℂ) (((|C| + 1 : ℝ)) : ℂ) = |C| + 1 := by
      rw [dist_zero_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h2] at h1
    linarith [le_abs_self C]

/-- **Separation step.**  If `U` and `V` are open subsets of `ℂ` whose complements have no bounded
connected component, then the same holds for every component of `U ∩ V`.

Proof.  Let `W` be the component of `x` in `U ∩ V`, let `z ∉ W`, and set `C :=` the component of `z`
in `Wᶜ`; suppose `C` bounded.

* If `z ∉ U`, the component `D` of `z` in `Uᶜ` is unbounded, is preconnected, contains `z` and lies
  in `Wᶜ ⊆ Uᶜ`, so `D ⊆ C`, contradicting boundedness of `C`.
* If `z ∈ U ∩ V`, then `z` lies in another component `W'` of `U ∩ V`, and `W' ⊆ Wᶜ`.  If `W'` is
  unbounded then `W' ⊆ C` contradicts boundedness of `C`.  Otherwise `W'` is bounded, so its
  frontier is nonempty: take `q ∈ frontier W'`.  As `W'` is open, `q ∈ closure W'` and `q ∉ W'`,
  and since `W' ⊆ (U ∩ V)ᶜ` with `(U ∩ V)ᶜ` closed we get `q ∉ U ∩ V`.  Then `W' ∪ {q}` is
  preconnected (a point of the closure may be adjoined) and contained in `Wᶜ`, so `q ∈ C`.
  Finally `q ∈ Uᶜ ∪ Vᶜ`; if `q ∉ U` then the component of `q` in `Uᶜ` is unbounded, is preconnected,
  contains `q ∈ C` and lies in `Wᶜ ⊆ Uᶜ`, hence is contained in `C`; contradiction. -/
theorem no_bounded_component_inter {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : ∀ z : ℂ, z ∉ U → ¬ Bornology.IsBounded (connectedComponentIn (Uᶜ) z))
    (hVc : ∀ z : ℂ, z ∉ V → ¬ Bornology.IsBounded (connectedComponentIn (Vᶜ) z))
    {x : ℂ} (hx : x ∈ U ∩ V) :
    ∀ z : ℂ, z ∉ connectedComponentIn (U ∩ V) x →
      ¬ Bornology.IsBounded (connectedComponentIn ((connectedComponentIn (U ∩ V) x)ᶜ) z) := by
  set W : Set ℂ := connectedComponentIn (U ∩ V) x with hW
  have hUVo : IsOpen (U ∩ V) := hU.inter hV
  have hWsub : W ⊆ U ∩ V := hW ▸ connectedComponentIn_subset (U ∩ V) x
  -- The component of any point of `Wᶜ` outside `U` or outside `V` is unbounded and sits in `Wᶜ`.
  have hmem : ∀ {p : ℂ}, p ∉ U → connectedComponentIn (Uᶜ) p ⊆ Wᶜ := by
    intro p hp a ha
    have haU : a ∈ Uᶜ := connectedComponentIn_subset (Uᶜ) p ha
    simp only [Set.mem_compl_iff] at haU ⊢
    intro haW
    exact haU (hWsub haW).1
  have hmem' : ∀ {p : ℂ}, p ∉ V → connectedComponentIn (Vᶜ) p ⊆ Wᶜ := by
    intro p hp a ha
    have haV : a ∈ Vᶜ := connectedComponentIn_subset (Vᶜ) p ha
    simp only [Set.mem_compl_iff] at haV ⊢
    intro haW
    exact haV (hWsub haW).2
  intro z hzW hzbd
  by_cases hzU : z ∈ U
  · by_cases hzV : z ∈ V
    · -- `z` lies in another component `W'` of `U ∩ V`
      set W' : Set ℂ := connectedComponentIn (U ∩ V) z with hW'def
      have hzW' : z ∈ W' := hW'def ▸ mem_connectedComponentIn ⟨hzU, hzV⟩
      have hW'pre : IsPreconnected W' := isPreconnected_connectedComponentIn
      have hW'sub : W' ⊆ U ∩ V := connectedComponentIn_subset (U ∩ V) z
      have hW'o : IsOpen W' := hW'def ▸ hUVo.connectedComponentIn
      have hW'ne : W' ≠ W := fun h => hzW (h ▸ hzW')
      have hW'compl : W' ⊆ Wᶜ := by
        intro a ha
        simp only [Set.mem_compl_iff]
        intro haW
        have h1 : connectedComponentIn (U ∩ V) z = connectedComponentIn (U ∩ V) a :=
          connectedComponentIn_eq ha
        have h2 : connectedComponentIn (U ∩ V) x = connectedComponentIn (U ∩ V) a :=
          connectedComponentIn_eq haW
        exact hW'ne (by rw [hW'def, hW, h1, h2])
      have hW'subC : W' ⊆ connectedComponentIn (Wᶜ) z :=
        hW'pre.subset_connectedComponentIn hzW' hW'compl
      by_cases hW'bdd : Bornology.IsBounded W'
      · -- `W'` bounded: a frontier point `q` of `W'` supplies the contradiction
        obtain ⟨q, hq⟩ := nonempty_frontier_of_isBounded ⟨z, hzW'⟩ hW'bdd
        have hqcl : q ∈ closure W' := frontier_subset_closure hq
        have hqnotW' : q ∉ W' := (hW'o.frontier_eq ▸ hq : q ∈ closure W' \ W').2
        have hpre : IsPreconnected (insert q W') :=
          isPreconnected_insert_of_mem_closure hW'pre hqcl
        have hqnotUV : q ∉ U ∩ V := by
          intro hqin
          have hsub : insert q W' ⊆ U ∩ V := Set.insert_subset hqin hW'sub
          have : insert q W' ⊆ W' :=
            hpre.subset_connectedComponentIn (Set.mem_insert_iff.mpr (Or.inr hzW')) hsub
          exact hqnotW' (this (Set.mem_insert_iff.mpr (Or.inl rfl)))
        have hqC : q ∈ connectedComponentIn (Wᶜ) z := by
          have hsub : insert q W' ⊆ Wᶜ := by
            refine Set.insert_subset ?_ hW'compl
            simp only [Set.mem_compl_iff]
            intro hqW
            exact hqnotUV (hWsub hqW)
          exact hpre.subset_connectedComponentIn (Set.mem_insert_iff.mpr (Or.inr hzW')) hsub
            (Set.mem_insert_iff.mpr (Or.inl rfl))
        have hqUV : q ∈ Uᶜ ∪ Vᶜ := by
          by_contra hcon
          rw [Set.mem_union, not_or] at hcon
          simp only [Set.mem_compl_iff, not_not] at hcon
          exact hqnotUV ⟨hcon.1, hcon.2⟩
        rcases hqUV with hqU | hqV
        · have hsub : connectedComponentIn (Uᶜ) q ⊆ connectedComponentIn (Wᶜ) z :=
            (connectedComponentIn_eq hqC).symm ▸
              isPreconnected_connectedComponentIn.subset_connectedComponentIn
                (mem_connectedComponentIn hqU) (hmem hqU)
          exact hUc q hqU (hzbd.subset hsub)
        · have hsub : connectedComponentIn (Vᶜ) q ⊆ connectedComponentIn (Wᶜ) z :=
            (connectedComponentIn_eq hqC).symm ▸
              isPreconnected_connectedComponentIn.subset_connectedComponentIn
                (mem_connectedComponentIn hqV) (hmem' hqV)
          exact hVc q hqV (hzbd.subset hsub)
      · exact hW'bdd (hzbd.subset hW'subC)
    · exact hVc z hzV (hzbd.subset (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn hzV) (hmem' hzV)))
  · exact hUc z hzU (hzbd.subset (isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hzU) (hmem hzU)))

/-! ## Assembly

The two halves of the classical criterion for plane domains are proved in the companion modules
`PlanarSC/no_bounded_component_of_simplyConnected` and `PlanarSC/simplyConnected_of_no_bounded_component`
and are used below exactly as stated. -/

theorem planar_inter_sc : PlanarInterSCStatement := by
  intro U V hUo hVo hUsc hVsc x hx
  have hUc : ∀ z : ℂ, z ∉ U → ¬ Bornology.IsBounded (connectedComponentIn (Uᶜ) z) :=
    fun z hz => no_bounded_component_of_simplyConnected hUo
      (isConnected_iff_connectedSpace.mpr inferInstance) hUsc hz
  have hVc : ∀ z : ℂ, z ∉ V → ¬ Bornology.IsBounded (connectedComponentIn (Vᶜ) z) :=
    fun z hz => no_bounded_component_of_simplyConnected hVo
      (isConnected_iff_connectedSpace.mpr inferInstance) hVsc hz
  have hW := no_bounded_component_inter hUo hVo hUc hVc hx
  have hWo : IsOpen (connectedComponentIn (U ∩ V) x) := (hUo.inter hVo).connectedComponentIn
  have hWc : IsConnected (connectedComponentIn (U ∩ V) x) :=
    ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩
  exact simplyConnected_of_no_bounded_component hWo hWc hW

end Work.PlanarSC
