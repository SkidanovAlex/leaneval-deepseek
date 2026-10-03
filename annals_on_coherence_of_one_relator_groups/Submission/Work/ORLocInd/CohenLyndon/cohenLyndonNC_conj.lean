import Mathlib
import Submission.Work.ORLocInd.CohenLyndon.NCForm

set_option autoImplicit false
set_option linter.dupNamespace false

universe u

namespace Work.ORLocInd.CohenLyndon

variable {G : Type u} [Group G]

/-! ## Elementary facts about conjugation

These are the group-theoretic inputs of the conjugation invariance of `CohenLyndonNC`: the normal
closure of a singleton is unaffected by conjugation, and conjugation carries the centralizer of `r`
to the centralizer of the conjugate `g * r * g⁻¹`. -/

/-- Membership in the image of a subgroup under conjugation: `x = g * k * g⁻¹` for some `k ∈ K`
iff `g⁻¹ * x * g ∈ K`. -/
lemma mem_map_conj_iff (K : Subgroup G) (g x : G) :
    x ∈ K.map (MulAut.conj g) ↔ g⁻¹ * x * g ∈ K := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    show g⁻¹ * (g * k * g⁻¹) * g ∈ K
    group
    exact hk
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

/-- The normal closure of a singleton is invariant under conjugation:
`⟪g * r * g⁻¹⟫ = ⟪r⟫`. -/
lemma normalClosure_conj_singleton (g r : G) :
    Subgroup.normalClosure ({g * r * g⁻¹} : Set G) = Subgroup.normalClosure ({r} : Set G) := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr ?_)
    simpa using (Subgroup.normalClosure_normal (s := ({r} : Set G))).conj_mem r
      (Subgroup.subset_normalClosure (by simp)) g
  · refine Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr ?_)
    have h := (Subgroup.normalClosure_normal (s := ({g * r * g⁻¹} : Set G))).conj_mem
      (g * r * g⁻¹) (Subgroup.subset_normalClosure (by simp)) g⁻¹
    show r ∈ Subgroup.normalClosure ({g * r * g⁻¹} : Set G)
    group at h
    simpa using h

/-- Conjugation carries the centralizer of `r` to the centralizer of the conjugate
`g * r * g⁻¹`: `C_G(g r g⁻¹) = g · C_G(r) · g⁻¹`. -/
lemma centralizer_conj_singleton (g r : G) :
    (Subgroup.centralizer ({r} : Set G)).map (MulAut.conj g) =
      Subgroup.centralizer ({g * r * g⁻¹} : Set G) := by
  ext x
  rw [mem_map_conj_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have h' := congrArg (fun z => g * z * g⁻¹) h
    group at h' ⊢
    exact h'
  · intro h
    have h' := congrArg (fun z => g⁻¹ * z * g) h
    group at h' ⊢
    exact h'

/-- A normal closure is invariant under conjugation by any element. -/
lemma normalClosure_map_conj (g r : G) :
    (Subgroup.normalClosure ({r} : Set G)).map (MulAut.conj g) =
      Subgroup.normalClosure ({r} : Set G) := by
  ext x
  rw [mem_map_conj_iff]
  constructor
  · intro h
    convert (Subgroup.normalClosure_normal (s := ({r} : Set G))).conj_mem
      (g⁻¹ * x * g) h g using 1
    group
  · intro h
    simpa using (Subgroup.normalClosure_normal (s := ({r} : Set G))).conj_mem x h g⁻¹

/-- The normal closure of the conjugate `g * r * g⁻¹` is the conjugate of the normal closure of
`r`, i.e. (as `⟪r⟫` is normal) simply `⟪r⟫`. -/
lemma map_conj_normalClosure (g r : G) :
    (Subgroup.normalClosure ({r} : Set G)).map (MulAut.conj g) =
      Subgroup.normalClosure ({g * r * g⁻¹} : Set G) := by
  rw [normalClosure_map_conj, normalClosure_conj_singleton]

/-- The subgroup `⟪r⟫ ⊔ C_G(r)` whose cosets index the classical Cohen--Lyndon transversal is
carried by conjugation to the corresponding subgroup for the conjugate relator `g * r * g⁻¹`. -/
lemma map_conj_sup_centralizer (g r : G) :
    (Subgroup.normalClosure ({r} : Set G) ⊔ Subgroup.centralizer ({r} : Set G)).map
        (MulAut.conj g) =
      Subgroup.normalClosure ({g * r * g⁻¹} : Set G) ⊔
        Subgroup.centralizer ({g * r * g⁻¹} : Set G) := by
  rw [Subgroup.map_sup, map_conj_normalClosure, centralizer_conj_singleton]

/-! ## The two transfer steps

Given a Cohen--Lyndon datum `(T, e)` for `r`, we produce one for the conjugate `g * r * g⁻¹`:
the index set is `T · g⁻¹ = {s : G | s * g ∈ T}` and the free basis is transplanted along the
bijection `s ↦ s * g`. -/

/-- **Conjugating a transversal of the cosets of a subgroup.**  Let `K ≤ G`, let `T` be a set of
left-coset representatives of `K` in `G`, in the form `∀ y, ∃! t ∈ T, y⁻¹ * t ∈ K` (this says
`t ∈ yK`, so `T` meets every left coset `yK` exactly once).  Let `K' ≤ G` be the conjugate of `K` in
the sense that for all `x`, `x ∈ K' ↔ g⁻¹ * x * g ∈ K` (e.g. `K' = K.map (MulAut.conj g)`).

Then `T' := {s : G | s * g ∈ T}` (the set `T · g⁻¹`) is a transversal of the cosets of `K'`:
for every `y` there is a unique `s ∈ T'` with `y⁻¹ * s ∈ K'`. -/
lemma transversal_conj (K K' : Subgroup G) (T : Set G) (g : G)
    (hKK' : ∀ x : G, x ∈ K' ↔ g⁻¹ * x * g ∈ K)
    (hT : ∀ y : G, ∃! t : G, t ∈ T ∧ y⁻¹ * t ∈ K) :
    ∀ y : G, ∃! s : G, s ∈ {s : G | s * g ∈ T} ∧ y⁻¹ * s ∈ K' := by
  intro y
  obtain ⟨t, ht, huniq⟩ := hT (y * g)
  refine ⟨t * g⁻¹, ⟨?_, ?_⟩, ?_⟩
  · show t * g⁻¹ * g ∈ T
    rw [show t * g⁻¹ * g = t from by group]
    exact ht.1
  · rw [hKK']
    have h : g⁻¹ * (y⁻¹ * (t * g⁻¹)) * g = (y * g)⁻¹ * t := by group
    rw [h]
    exact ht.2
  · intro s hs
    have hsg : s * g = t := by
      refine huniq (s * g) ⟨hs.1, ?_⟩
      rw [hKK'] at hs
      have h : (y * g)⁻¹ * (s * g) = g⁻¹ * (y⁻¹ * s) * g := by group
      rw [h]
      exact hs.2
    rw [← hsg]
    group

/-- **Transporting a "free basis of conjugates" presentation along right multiplication by
`g⁻¹`.**  Let `T ⊆ G` be an index set, `N ≤ G` a subgroup, and `e : FreeGroup T ≃* N` a group
isomorphism sending the generator `t` to the conjugate `t r t⁻¹` of a fixed element `r ∈ G`.

Then with `T' := {s : G | s * g ∈ T}` (the set `T · g⁻¹`; the map `T' → T`, `s ↦ s * g`, is a
bijection with inverse `t ↦ t * g⁻¹`), the same group `N` is free on `T'` with the generators
mapping to the conjugates of the *conjugate* element `g * r * g⁻¹`: there is `e' : FreeGroup T' ≃* N`
with `e' (of s) = s * (g * r * g⁻¹) * s⁻¹` for every `s ∈ T'`. -/
lemma basis_conj (T : Set G) (r g : G) (N : Subgroup G) (e : FreeGroup T ≃* ↥N)
    (he : ∀ t : T, ((e (FreeGroup.of t) : ↥N) : G) = (t : G) * r * (t : G)⁻¹) :
    ∃ e' : FreeGroup {s : G | s * g ∈ T} ≃* ↥N,
      ∀ s : {s : G | s * g ∈ T},
        ((e' (FreeGroup.of s) : ↥N) : G) = (s : G) * (g * r * g⁻¹) * (s : G)⁻¹ := by
  let τ : {s : G | s * g ∈ T} → T := fun s => ⟨s * g, s.2⟩
  have hτ : Function.Bijective τ := by
    constructor
    · intro s₁ s₂ h
      have h1 : (s₁ : G) * g = (s₂ : G) * g := by
        simpa [τ] using congrArg Subtype.val h
      exact Subtype.ext (mul_right_cancel h1)
    · intro t
      refine ⟨⟨(t : G) * g⁻¹, ?_⟩, ?_⟩
      · show t * g⁻¹ * g ∈ T
        rw [show t * g⁻¹ * g = (t : G) from by group]
        exact t.2
      · ext
        show (t : G) * g⁻¹ * g = (t : G)
        group
  let E : {s : G | s * g ∈ T} ≃ T := Equiv.ofBijective τ hτ
  have hE : ∀ s : {s : G | s * g ∈ T}, ((E s : T) : G) = (s : G) * g := fun s => rfl
  refine ⟨(FreeGroup.freeGroupCongr E).trans e, ?_⟩
  intro s
  have h1 : FreeGroup.freeGroupCongr E (FreeGroup.of s) = FreeGroup.of (E s) :=
    FreeGroup.map.of
  rw [MulEquiv.trans_apply, h1, he (E s), hE]
  show ((s : G) * g) * r * ((s : G) * g)⁻¹ = (s : G) * (g * r * g⁻¹) * (s : G)⁻¹
  group

/-- **One direction of conjugation invariance.**  If `r` has the Cohen--Lyndon property then so
does every conjugate `g * r * g⁻¹`: conjugating the index set by right multiplication by `g⁻¹`
permutes the `⟪r⟫ · C_G(r)`-cosets and carries the free basis `t r t⁻¹` to
`(t g⁻¹)(g r g⁻¹)(t g⁻¹)⁻¹`. -/
theorem cohenLyndonNC_conj_of {r : G} (g : G)
    (h : Work.CohenLyndon.CohenLyndonNC r) :
    Work.CohenLyndon.CohenLyndonNC (g * r * g⁻¹) := by
  obtain ⟨T, hT, e, he⟩ := h
  have hN : Subgroup.normalClosure ({g * r * g⁻¹} : Set G) =
      Subgroup.normalClosure ({r} : Set G) := normalClosure_conj_singleton g r
  have hK := map_conj_sup_centralizer (G := G) g r
  have hKK' : ∀ x : G,
      x ∈ (Subgroup.normalClosure ({g * r * g⁻¹} : Set G) ⊔
            Subgroup.centralizer ({g * r * g⁻¹} : Set G)) ↔
        g⁻¹ * x * g ∈ (Subgroup.normalClosure ({r} : Set G) ⊔
            Subgroup.centralizer ({r} : Set G)) := by
    intro x
    rw [← hK, mem_map_conj_iff]
  refine ⟨{s : G | s * g ∈ T}, transversal_conj _ _ T g hKK' hT, ?_⟩
  rw [hN]
  exact basis_conj T r g (Subgroup.normalClosure ({r} : Set G)) e he

/-- **Conjugation invariance of the Cohen--Lyndon property.**

The property `CohenLyndonNC r` depends only on the conjugacy class of `r`: conjugation permutes the
`⟪r⟫·C_G(r)`-cosets (the normal closure is normal, the centralizer is carried to the centralizer of
the conjugate) and carries the free basis `t r t⁻¹` to `(g t g⁻¹)(g r g⁻¹)(g t g⁻¹)⁻¹`.  This is
what allows an arbitrary `r` to be replaced by a cyclically reduced conjugate in the induction. -/
theorem cohenLyndonNC_conj {G : Type u} [Group G] {r : G} (g : G) :
    Work.CohenLyndon.CohenLyndonNC (g * r * g⁻¹) ↔ Work.CohenLyndon.CohenLyndonNC r := by
  constructor
  · intro h
    have h' := cohenLyndonNC_conj_of (G := G) (r := g * r * g⁻¹) g⁻¹ h
    rwa [show g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r from by group] at h'
  · intro h
    exact cohenLyndonNC_conj_of (G := G) (r := r) g h

end Work.ORLocInd.CohenLyndon
