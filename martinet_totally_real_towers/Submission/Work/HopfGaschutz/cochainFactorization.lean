import Mathlib
import Submission.Work.HopfGaschutz.Profinite

namespace Work.HopfGaschutz

theorem cochainFactorization (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] :
    ∀ (M : Type) [AddCommGroup M] (f : LocallyConstant (Γ × Γ) M),
      ∃ U : OpenNormalSubgroup Γ, ∃ g : (Γ ⧸ U.toSubgroup) × (Γ ⧸ U.toSubgroup) → M,
        ⇑f = fun p => g (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2) := by
  intro M _ f
  -- Step 1: at every point `p` there is an open normal subgroup `V` of `Γ × Γ` such that `f` is
  -- constant on the right coset `p * V`.  Indeed `{v | f (p * v) = f p}` is a neighbourhood of `1`
  -- (the set `{q | f q = f p}` is open because `f` is locally constant), so it contains an open
  -- normal subgroup since `Γ × Γ` is compact and totally disconnected.
  have hpoint : ∀ p : Γ × Γ, ∃ V : OpenNormalSubgroup (Γ × Γ),
      ∀ v ∈ (V : Set (Γ × Γ)), f (p * v) = f p := by
    intro p
    have hT : IsOpen {q : Γ × Γ | f q = f p} := by
      have h := f.isLocallyConstant ({f p} : Set M)
      simpa [Set.preimage, Set.mem_singleton_iff] using h
    have hS : IsOpen {v : Γ × Γ | f (p * v) = f p} :=
      (continuous_const.mul continuous_id : Continuous fun v : Γ × Γ => p * v).isOpen_preimage _
        hT
    have h1 : (1 : Γ × Γ) ∈ {v : Γ × Γ | f (p * v) = f p} := by simp
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS h1
    exact ⟨V, fun v hv => hV hv⟩
  choose Vf hVf using hpoint
  -- Step 2: finitely many of the cosets `p * Vf p` cover `Γ × Γ` by compactness.
  have hopen : ∀ p : Γ × Γ, IsOpen ((fun v => p * v) '' (Vf p : Set (Γ × Γ))) :=
    fun p => isOpenMap_mul_left p _ (Vf p).isOpen
  have hcover : (Set.univ : Set (Γ × Γ)) ⊆ ⋃ p, ((fun v => p * v) '' (Vf p : Set (Γ × Γ))) := by
    intro p _
    exact Set.mem_iUnion.mpr ⟨p, ⟨1, (Vf p).one_mem, by simp⟩⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p : Γ × Γ => ((fun v => p * v) '' (Vf p : Set (Γ × Γ)))) hopen hcover
  have htne : t.Nonempty := by
    rcases Set.mem_iUnion.mp (ht (Set.mem_univ (1 : Γ × Γ))) with ⟨p, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hpt, _⟩
    exact ⟨p, hpt⟩
  let V : OpenNormalSubgroup (Γ × Γ) := t.inf' htne Vf
  have hVle : ∀ p ∈ t, V ≤ Vf p := fun p hp => Finset.inf'_le Vf hp
  -- Step 3: `f` is invariant under right multiplication by `V`.
  have hinv : ∀ (x v : Γ × Γ), v ∈ (V : Set (Γ × Γ)) → f (x * v) = f x := by
    intro x v hv
    rcases Set.mem_iUnion.mp (ht (Set.mem_univ x)) with ⟨p, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hpt, hpx⟩
    rcases hpx with ⟨w, hw, rfl⟩
    have hwv : w * v ∈ (Vf p : Set (Γ × Γ)) := (Vf p).mul_mem hw (hVle p hpt hv)
    rw [mul_assoc]
    exact (hVf p (w * v) hwv).trans (hVf p w hw).symm
  -- Step 4: an open normal subgroup `V` of the product contains a product `A × B` of open
  -- neighbourhoods of `1`, hence contains `U × U` for some open normal `U ≤ Γ`.
  obtain ⟨A, B, hAopen, hBopen, hA1, hB1, hAB⟩ :=
    isOpen_prod_iff.mp V.isOpen (1 : Γ) (1 : Γ) (by exact V.one_mem)
  obtain ⟨U, hU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hAopen.inter hBopen) ⟨hA1, hB1⟩
  have hUU : ∀ u1 ∈ (U : Set Γ), ∀ u2 ∈ (U : Set Γ), ((u1, u2) : Γ × Γ) ∈ (V : Set (Γ × Γ)) := by
    intro u1 h1 u2 h2
    exact hAB (Set.mem_prod.mpr ⟨(hU h1).1, (hU h2).2⟩)
  have hinv2 : ∀ (x y u1 u2 : Γ), u1 ∈ (U : Set Γ) → u2 ∈ (U : Set Γ) →
      f ((x * u1, y * u2) : Γ × Γ) = f ((x, y) : Γ × Γ) := by
    intro x y u1 u2 h1 h2
    exact hinv ((x, y) : Γ × Γ) ((u1, u2) : Γ × Γ) (hUU u1 h1 u2 h2)
  -- Step 5: `f` therefore factors through `Γ/U × Γ/U`.
  refine ⟨U, fun q => f ((Quotient.out q.1, Quotient.out q.2) : Γ × Γ), ?_⟩
  funext p
  obtain ⟨x, y⟩ := p
  change f (x, y) = f ((Quotient.out (QuotientGroup.mk' U.toSubgroup x),
      Quotient.out (QuotientGroup.mk' U.toSubgroup y)) : Γ × Γ)
  have hx : ∃ z ∈ U.toSubgroup, x * z = Quotient.out (QuotientGroup.mk' U.toSubgroup x) := by
    apply (QuotientGroup.mk'_eq_mk' U.toSubgroup).mp
    exact (Quotient.out_eq _).symm
  have hy : ∃ z ∈ U.toSubgroup, y * z = Quotient.out (QuotientGroup.mk' U.toSubgroup y) := by
    apply (QuotientGroup.mk'_eq_mk' U.toSubgroup).mp
    exact (Quotient.out_eq _).symm
  obtain ⟨z1, hz1, hxz1⟩ := hx
  obtain ⟨z2, hz2, hyz2⟩ := hy
  rw [← hxz1, ← hyz2]
  exact (hinv2 x y z1 z2 hz1 hz2).symm

end Work.HopfGaschutz
