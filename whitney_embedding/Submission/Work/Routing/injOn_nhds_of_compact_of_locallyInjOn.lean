import Mathlib

set_option linter.style.haveILetI false

namespace Work.Routing

open Topology Filter

/-- If `K` is a compact subset of `X` and `W` is an open subset of `X × X` containing `K ×ˢ K`,
then there is an open neighbourhood `T` of `K` with `T ×ˢ T ⊆ W`. -/
theorem exists_isOpen_superset_prod_subset {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {W : Set (X × X)} (hW : IsOpen W) (hKW : K ×ˢ K ⊆ W) :
    ∃ T : Set X, IsOpen T ∧ K ⊆ T ∧ T ×ˢ T ⊆ W := by
  have hmem : W ∈ nhdsSet (K ×ˢ K) := mem_nhdsSet_iff_exists.2 ⟨W, hW, hKW, subset_rfl⟩
  rw [hK.nhdsSet_prod_eq hK] at hmem
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_prod_iff.1 hmem
  have ht : t₁ ∩ t₂ ∈ nhdsSet K := inter_mem ht₁ ht₂
  obtain ⟨T, hTopen, hKT, hTsub⟩ := mem_nhdsSet_iff_exists.1 ht
  exact ⟨T, hTopen, hKT,
    (Set.prod_mono hTsub hTsub).trans
      ((Set.prod_mono Set.inter_subset_left Set.inter_subset_right).trans hsub)⟩

/-- A map continuous at the points of a compact set `K`, injective on `K` and locally injective at each point of `K`, is injective on an open neighbourhood of `K` (the purely topological half of `Work.Routing.injectiveOn_nhds_of_injective_arc`). -/
theorem injOn_nhds_of_compact_of_locallyInjOn
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} {K : Set X} (hK : IsCompact K)
    (hloc : ∀ x ∈ K, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U)
    (hcont : ∀ x ∈ K, ContinuousAt f x)
    (hKinj : Set.InjOn f K) :
    ∃ T : Set X, IsOpen T ∧ K ⊆ T ∧ Set.InjOn f T := by
  -- `Z` is the set of "bad pairs": distinct points with the same image.
  let Z : Set (X × X) := {p | f p.1 = f p.2 ∧ p.1 ≠ p.2}
  -- It suffices to find an open `T ⊇ K` with `(T ×ˢ T) ∩ Z = ∅`.
  have key : ∃ T : Set X, IsOpen T ∧ K ⊆ T ∧ (T ×ˢ T) ∩ Z = ∅ := by
    by_contra hcon
    have h : ∀ T : Set X, IsOpen T → K ⊆ T → (T ×ˢ T) ∩ Z ≠ ∅ := by
      intro T hT hKT hd
      exact hcon ⟨T, hT, hKT, hd⟩
    set W : Set (X × X) := (closure Z)ᶜ with hW
    have hWopen : IsOpen W := isClosed_closure.isOpen_compl
    by_cases hKW : K ×ˢ K ⊆ W
    · -- If `K ×ˢ K` avoids `closure Z`, we can separate it: contradiction with `h`.
      obtain ⟨T, hTopen, hKT, hTW⟩ := exists_isOpen_superset_prod_subset hK hWopen hKW
      rw [hW] at hTW
      have hempty : (T ×ˢ T) ∩ Z = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨q, hq1, hq2⟩
        exact (hTW hq1) (subset_closure hq2)
      exact h T hTopen hKT hempty
    · -- Otherwise `Z` accumulates at some point `(a, b) ∈ K ×ˢ K`.
      obtain ⟨p, hpK, hpnotW⟩ := Set.not_subset.1 hKW
      have hpcl : p ∈ closure Z := by
        rw [hW] at hpnotW
        simpa using hpnotW
      obtain ⟨a, b⟩ := p
      obtain ⟨ha, hb⟩ := Set.mem_prod.1 hpK
      have hg : ContinuousAt (fun q : X × X => (f q.1, f q.2)) (a, b) :=
        ContinuousAt.prodMk ((hcont a ha).comp continuousAt_fst)
          ((hcont b hb).comp continuousAt_snd)
      -- Passing to the limit along the filter where `Z` is large gives `f a = f b`.
      have hfab : f a = f b := by
        haveI : NeBot (𝓝 (a, b) ⊓ 𝓟 Z) := mem_closure_iff_clusterPt.1 hpcl
        have htend : Tendsto (fun q : X × X => (f q.1, f q.2)) (𝓝 (a, b) ⊓ 𝓟 Z) (𝓝 (f a, f b)) :=
          hg.tendsto.mono_left inf_le_left
        have hZmem : Z ∈ (𝓝 (a, b) ⊓ 𝓟 Z) :=
          Filter.mem_inf_iff.2 ⟨Set.univ, Filter.univ_mem, Z, Filter.mem_principal_self Z, by simp⟩
        have hev : ∀ᶠ q in (𝓝 (a, b) ⊓ 𝓟 Z), (f q.1, f q.2) ∈ Set.diagonal Y :=
          Filter.mem_of_superset hZmem (fun q hq => Set.mem_diagonal_iff.2 hq.1)
        exact Set.mem_diagonal_iff.1 (isClosed_diagonal.mem_of_tendsto htend hev)
      -- So `a = b` by injectivity on `K`, and local injectivity at `a` is contradicted.
      have hab : a = b := hKinj ha hb hfab
      rcases hloc a ha with ⟨U, hUopen, haU, hUinj⟩
      have hUpopen : IsOpen (U ×ˢ U) := hUopen.prod hUopen
      have hmemU : (a, b) ∈ U ×ˢ U := by
        rw [Set.mem_prod]; exact ⟨haU, hab ▸ haU⟩
      obtain ⟨q, hq1, hq2⟩ := mem_closure_iff.1 hpcl (U ×ˢ U) hUpopen hmemU
      rw [Set.mem_prod] at hq1
      exact hq2.2 (hUinj hq1.1 hq1.2 hq2.1)
  obtain ⟨T, hTopen, hKT, hdisj⟩ := key
  refine ⟨T, hTopen, hKT, ?_⟩
  intro x hx y hy hfxy
  by_contra hxy
  have hmem : (x, y) ∈ (T ×ˢ T) ∩ Z :=
    ⟨Set.mem_prod.2 ⟨hx, hy⟩, ⟨hfxy, hxy⟩⟩
  rw [hdisj] at hmem
  exact hmem

end Work.Routing
