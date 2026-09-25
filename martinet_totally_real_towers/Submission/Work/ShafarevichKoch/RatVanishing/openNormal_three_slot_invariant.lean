import Mathlib

namespace Work.ShafarevichKoch.RatVanishing

/-- **A locally constant function on a product of three copies of a profinite group is
invariant under right translation by a single open normal subgroup in each slot.**

Let `G` be a compact totally disconnected topological group (a profinite group) and let
`f : G × G × G → M` be locally constant (`M` arbitrary).  Then there is an open normal
subgroup `N ≤ G` such that `f` is invariant under right multiplication by an element of `N`
in any one of the three variables.

The proof is the standard "refine the clopen partition of a compact space by cosets of open
normal subgroups": locally constant means that each point `x` has an open neighbourhood `O_x`
on which `f` is constant; shrinking to a box `A × B × C` and then to right cosets
`H₁ x.1 × H₂ x.2.1 × H₃ x.2.2` of open *normal* subgroups (which exist by
`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`), compactness of `G × G × G`
gives finitely many such boxes covering the space, and an open normal subgroup contained in
the intersection of the finitely many defining subgroups is invariant. -/
theorem openNormal_three_slot_invariant {G M : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {f : G × G × G → M} (hf : IsLocallyConstant f) :
    ∃ N : Subgroup G, N.Normal ∧ IsOpen (N : Set G) ∧
      (∀ n ∈ N, ∀ σ τ ρ : G, f (σ * n, τ, ρ) = f (σ, τ, ρ)) ∧
      (∀ n ∈ N, ∀ σ τ ρ : G, f (σ, τ * n, ρ) = f (σ, τ, ρ)) ∧
      (∀ n ∈ N, ∀ σ τ ρ : G, f (σ, τ, ρ * n) = f (σ, τ, ρ)) := by
  classical
  -- At each point of `G × G × G`, a right-coset box carved out by open normal subgroups,
  -- on which `f` is constant and which is stable under right multiplication by its subgroups.
  have key : ∀ x : G × G × G, ∃ (H1 H2 H3 : OpenNormalSubgroup G) (bx : Set (G × G × G)),
      IsOpen bx ∧ x ∈ bx ∧ (∀ y ∈ bx, f y = f x) ∧
      (∀ y ∈ bx, ∀ n1 n2 n3 : G, n1 ∈ (H1 : Set G) → n2 ∈ (H2 : Set G) →
        n3 ∈ (H3 : Set G) → (y.1 * n1, y.2.1 * n2, y.2.2 * n3) ∈ bx) := by
    intro x
    obtain ⟨O, hO, hxO, hcO⟩ := hf.exists_open x
    obtain ⟨A, B, hA, hB, hxA, hxB, hAB⟩ := (isOpen_prod_iff.mp hO) x.1 x.2 hxO
    obtain ⟨A2, A3, hA2, hA3, hx2, hx3, hA23⟩ := (isOpen_prod_iff.mp hB) x.2.1 x.2.2 hxB
    have hW1 : IsOpen {w : G | w * x.1 ∈ A} := hA.preimage (continuous_id.mul continuous_const)
    have h1W1 : (1 : G) ∈ {w : G | w * x.1 ∈ A} := by simpa using hxA
    have hW2 : IsOpen {w : G | w * x.2.1 ∈ A2} := hA2.preimage (continuous_id.mul continuous_const)
    have h1W2 : (1 : G) ∈ {w : G | w * x.2.1 ∈ A2} := by simpa using hx2
    have hW3 : IsOpen {w : G | w * x.2.2 ∈ A3} := hA3.preimage (continuous_id.mul continuous_const)
    have h1W3 : (1 : G) ∈ {w : G | w * x.2.2 ∈ A3} := by simpa using hx3
    obtain ⟨H1, hH1⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW1 h1W1
    obtain ⟨H2, hH2⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW2 h1W2
    obtain ⟨H3, hH3⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW3 h1W3
    let bxx : Set (G × G × G) := {y | y.1 * x.1⁻¹ ∈ (H1 : Set G)} ∩
      ({y | y.2.1 * x.2.1⁻¹ ∈ (H2 : Set G)} ∩ {y | y.2.2 * x.2.2⁻¹ ∈ (H3 : Set G)})
    have hbx1 : IsOpen {y : G × G × G | y.1 * x.1⁻¹ ∈ (H1 : Set G)} :=
      (H1.toOpenSubgroup.isOpen).preimage (continuous_fst.mul continuous_const)
    have hbx2 : IsOpen {y : G × G × G | y.2.1 * x.2.1⁻¹ ∈ (H2 : Set G)} :=
      (H2.toOpenSubgroup.isOpen).preimage (continuous_snd.fst.mul continuous_const)
    have hbx3 : IsOpen {y : G × G × G | y.2.2 * x.2.2⁻¹ ∈ (H3 : Set G)} :=
      (H3.toOpenSubgroup.isOpen).preimage (continuous_snd.snd.mul continuous_const)
    have hbxmem : ∀ y, y ∈ bxx ↔ y.1 * x.1⁻¹ ∈ (H1 : Set G) ∧
        y.2.1 * x.2.1⁻¹ ∈ (H2 : Set G) ∧ y.2.2 * x.2.2⁻¹ ∈ (H3 : Set G) := by
      intro y; rw [show bxx = _ from rfl]; exact Set.mem_inter_iff _ _ _
    have hbxopen : IsOpen bxx := by
      rw [show bxx = _ from rfl]; exact hbx1.inter (hbx2.inter hbx3)
    refine ⟨H1, H2, H3, bxx, hbxopen, ?_, ?_, ?_⟩
    · rw [hbxmem]
      exact ⟨by rw [mul_inv_cancel]; exact H1.toSubgroup.one_mem,
        by rw [mul_inv_cancel]; exact H2.toSubgroup.one_mem,
        by rw [mul_inv_cancel]; exact H3.toSubgroup.one_mem⟩
    · intro y hy
      obtain ⟨hy1, hy2, hy3⟩ := hbxmem y |>.mp hy
      have hyA : y.1 ∈ A := by
        have h : (y.1 * x.1⁻¹) * x.1 ∈ A := hH1 hy1
        have h2 : (y.1 * x.1⁻¹) * x.1 = y.1 := by group
        rwa [h2] at h
      have hyA2 : y.2.1 ∈ A2 := by
        have h : (y.2.1 * x.2.1⁻¹) * x.2.1 ∈ A2 := hH2 hy2
        have h2 : (y.2.1 * x.2.1⁻¹) * x.2.1 = y.2.1 := by group
        rwa [h2] at h
      have hyA3 : y.2.2 ∈ A3 := by
        have h : (y.2.2 * x.2.2⁻¹) * x.2.2 ∈ A3 := hH3 hy3
        have h2 : (y.2.2 * x.2.2⁻¹) * x.2.2 = y.2.2 := by group
        rwa [h2] at h
      exact hcO y (hAB ⟨hyA, hA23 ⟨hyA2, hyA3⟩⟩)
    · intro y hy n1 n2 n3 hn1 hn2 hn3
      obtain ⟨hy1, hy2, hy3⟩ := hbxmem y |>.mp hy
      rw [hbxmem]
      refine ⟨?_, ?_, ?_⟩
      · have hconj : x.1 * n1 * x.1⁻¹ ∈ (H1 : Set G) := H1.isNormal'.conj_mem n1 hn1 x.1
        have heq : (y.1 * n1) * x.1⁻¹ = (y.1 * x.1⁻¹) * (x.1 * n1 * x.1⁻¹) := by group
        rw [heq]; exact mul_mem hy1 hconj
      · have hconj : x.2.1 * n2 * x.2.1⁻¹ ∈ (H2 : Set G) := H2.isNormal'.conj_mem n2 hn2 x.2.1
        have heq : (y.2.1 * n2) * x.2.1⁻¹ = (y.2.1 * x.2.1⁻¹) * (x.2.1 * n2 * x.2.1⁻¹) := by group
        rw [heq]; exact mul_mem hy2 hconj
      · have hconj : x.2.2 * n3 * x.2.2⁻¹ ∈ (H3 : Set G) := H3.isNormal'.conj_mem n3 hn3 x.2.2
        have heq : (y.2.2 * n3) * x.2.2⁻¹ = (y.2.2 * x.2.2⁻¹) * (x.2.2 * n3 * x.2.2⁻¹) := by group
        rw [heq]; exact mul_mem hy3 hconj
  choose H1 H2 H3 bx hbxopen hxmem hbxconst hbxinv using key
  -- finitely many boxes cover the compact space `G × G × G`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover bx hbxopen
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hxmem y⟩)
  -- an open normal subgroup contained in the intersection of the finitely many defining subgroups
  have hVopen : IsOpen (⋂ x ∈ t, ((H1 x : Set G) ∩ (H2 x : Set G) ∩ (H3 x : Set G))) :=
    isOpen_biInter_finset (fun x _ =>
      (((H1 x).toOpenSubgroup.isOpen).inter ((H2 x).toOpenSubgroup.isOpen)).inter
        ((H3 x).toOpenSubgroup.isOpen))
  have h1V : (1 : G) ∈ (⋂ x ∈ t, ((H1 x : Set G) ∩ (H2 x : Set G) ∩ (H3 x : Set G))) := by
    simp only [Set.mem_iInter]
    intro x _
    exact ⟨⟨(H1 x).toSubgroup.one_mem, (H2 x).toSubgroup.one_mem⟩, (H3 x).toSubgroup.one_mem⟩
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVopen h1V
  -- `f` is invariant under the simultaneous right action of `N` on all three slots
  have hmain : ∀ n1 n2 n3 : G, n1 ∈ N.toSubgroup → n2 ∈ N.toSubgroup → n3 ∈ N.toSubgroup →
      ∀ σ τ ρ : G, f (σ * n1, τ * n2, ρ * n3) = f (σ, τ, ρ) := by
    intro n1 n2 n3 hn1 hn2 hn3 σ τ ρ
    have hmem : (σ, (τ, ρ)) ∈ ⋃ x ∈ t, bx x := ht (Set.mem_univ _)
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨x, hxt, hxg⟩ := hmem
    have hn1x : n1 ∈ (H1 x : Set G) := by
      have h := hN hn1
      simp only [Set.mem_iInter] at h
      exact (h x hxt).1.1
    have hn2x : n2 ∈ (H2 x : Set G) := by
      have h := hN hn2
      simp only [Set.mem_iInter] at h
      exact (h x hxt).1.2
    have hn3x : n3 ∈ (H3 x : Set G) := by
      have h := hN hn3
      simp only [Set.mem_iInter] at h
      exact (h x hxt).2
    have hgn : (σ * n1, (τ * n2, ρ * n3)) ∈ bx x :=
      hbxinv x (σ, (τ, ρ)) hxg n1 n2 n3 hn1x hn2x hn3x
    rw [hbxconst x _ hgn, hbxconst x _ hxg]
  refine ⟨N.toSubgroup, N.isNormal', N.toOpenSubgroup.isOpen, ?_, ?_, ?_⟩
  · intro n hn σ τ ρ
    simpa using hmain n 1 1 hn N.toSubgroup.one_mem N.toSubgroup.one_mem σ τ ρ
  · intro n hn σ τ ρ
    simpa using hmain 1 n 1 N.toSubgroup.one_mem hn N.toSubgroup.one_mem σ τ ρ
  · intro n hn σ τ ρ
    simpa using hmain 1 1 n N.toSubgroup.one_mem N.toSubgroup.one_mem hn σ τ ρ

end Work.ShafarevichKoch.RatVanishing
