import Mathlib

namespace Work.Horn.HB

open Set Metric Filter Topology

set_option linter.style.haveILetI false in
/-- A compact subset of the union of an increasing family of open subsets of `ℂ` is already
contained in a single member of the family. -/
theorem exists_subset_of_isCompact_subset_iUnion_of_monotone {V : ℕ → Set ℂ}
    (hopen : ∀ n, IsOpen (V n)) (hmono : ∀ n, V n ⊆ V (n + 1)) {K : Set ℂ}
    (hK : IsCompact K) (hKV : K ⊆ ⋃ n, V n) : ∃ N, K ⊆ V N := by
  have hmonoM : Monotone V := monotone_nat_of_le_succ hmono
  have hdir : DirectedOn (· ⊆ ·) (Set.range V) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨V (max a b), ⟨max a b, rfl⟩,
      fun x hx => hmonoM (le_max_left a b) hx, fun x hx => hmonoM (le_max_right a b) hx⟩
  obtain ⟨u, ⟨N, rfl⟩, hKu⟩ := hK.elim_directedOn_cover (Set.range V)
    (by rintro _ ⟨n, rfl⟩; exact hopen n) (by rwa [Set.sUnion_range]) hdir ⟨V 0, ⟨0, rfl⟩⟩
  exact ⟨N, hKu⟩

set_option linter.style.haveILetI false in
/-- An increasing union of open, nonempty, simply connected subsets of `ℂ` is simply connected. -/
theorem simplyConnectedSpace_iUnion_of_monotone {V : ℕ → Set ℂ}
    (hopen : ∀ n, IsOpen (V n)) (hmono : ∀ n, V n ⊆ V (n + 1))
    (hsc : ∀ n, SimplyConnectedSpace ↥(V n)) (hne : (V 0).Nonempty) :
    SimplyConnectedSpace ↥(⋃ n, V n) := by
  have hcompact_subset : ∀ {K : Set ℂ}, IsCompact K → K ⊆ ⋃ n, V n → ∃ N, K ⊆ V N :=
    fun hK hKV => exists_subset_of_isCompact_subset_iUnion_of_monotone hopen hmono hK hKV
  have hpcU : IsPathConnected (⋃ n, V n) := by
    rw [isPathConnected_iff]
    refine ⟨?_, ?_⟩
    · obtain ⟨z, hz⟩ := hne
      exact ⟨z, mem_iUnion.2 ⟨0, hz⟩⟩
    · intro x hx y hy
      obtain ⟨a, ha⟩ := mem_iUnion.1 hx
      obtain ⟨b, hb⟩ := mem_iUnion.1 hy
      have hxN : x ∈ V (max a b) := (monotone_nat_of_le_succ hmono) (le_max_left a b) ha
      have hyN : y ∈ V (max a b) := (monotone_nat_of_le_succ hmono) (le_max_right a b) hb
      haveI : SimplyConnectedSpace ↥(V (max a b)) := hsc (max a b)
      have hIPC : IsPathConnected (V (max a b)) :=
        isPathConnected_iff_pathConnectedSpace.mpr inferInstance
      exact (hIPC.joinedIn x hxN y hyN).mono (Set.subset_iUnion V (max a b))
  have hpc : PathConnectedSpace ↥(⋃ n, V n) := isPathConnected_iff_pathConnectedSpace.mp hpcU
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨hpc, ?_⟩
  intro x γ
  have hcomp : IsCompact (Subtype.val '' Set.range γ) :=
    (isCompact_range γ.continuous).image continuous_subtype_val
  have hsub : Subtype.val '' Set.range γ ⊆ ⋃ n, V n := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  obtain ⟨N, hN⟩ := hcompact_subset hcomp hsub
  have hxN : x.1 ∈ V N := hN ⟨x, ⟨0, γ.source⟩, rfl⟩
  let γ' : Path (⟨x.1, hxN⟩ : ↥(V N)) ⟨x.1, hxN⟩ :=
    { toFun := fun t => ⟨(γ t).1, hN ⟨γ t, ⟨t, rfl⟩, rfl⟩⟩
      continuous_toFun := by fun_prop
      source' := by apply Subtype.ext; simp
      target' := by apply Subtype.ext; simp }
  let fN : C(↥(V N), ↥(⋃ n, V n)) :=
    ⟨fun z => ⟨z.1, mem_iUnion.2 ⟨N, z.2⟩⟩,
      Continuous.subtype_mk continuous_subtype_val (fun z => mem_iUnion.2 ⟨N, z.2⟩)⟩
  haveI : SimplyConnectedSpace ↥(V N) := hsc N
  have h1 : Path.Homotopic (γ'.map fN.continuous)
      ((Path.refl (⟨x.1, hxN⟩ : ↥(V N))).map fN.continuous) :=
    (SimplyConnectedSpace.paths_homotopic γ' (Path.refl _)).map fN
  have e1 : γ'.map fN.continuous = γ := by
    apply Path.ext
    funext t
    simp only [Path.map_coe, Function.comp_apply]
    exact Subtype.ext rfl
  have e2 : (Path.refl (⟨x.1, hxN⟩ : ↥(V N))).map fN.continuous = Path.refl x := by
    apply Path.ext
    funext t
    simp only [Path.map_coe, Function.comp_apply]
    exact Subtype.ext rfl
  rw [e1, e2] at h1
  exact h1

end Work.Horn.HB
