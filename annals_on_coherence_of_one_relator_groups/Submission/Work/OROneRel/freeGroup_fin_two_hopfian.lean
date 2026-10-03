import Mathlib
import Submission.Work.ORLocInd.FKS.freeGroup_separated_by_finite_p_group

/-!
# `F₂` is Hopfian

We prove that every surjective endomorphism of the free group on two generators is injective,
i.e. that `FreeGroup (Fin 2)` is *Hopfian*.

The proof follows the classical route: a finitely generated residually finite group is Hopfian.
The ingredients are

* `finite_monoidHom_of_fg` : a homomorphism out of a finitely generated group is determined by its
  values on a finite generating set, so there are only finitely many homomorphisms to a finite
  monoid;
* `exists_perm_repr_of_index_aux` : a subgroup `H` of index `n` is the stabiliser of a point of
  some degree-`n` permutation representation of the ambient group (its action on its own cosets),
  whence `finite_subgroups_of_index_aux` : a finitely generated group has only finitely many
  subgroups of any prescribed nonzero index;
* `freeGroup_residuallyFinite_aux` : a finitely generated free group is residually finite, which is
  P. Hall's theorem that free groups are residually finite `p`-groups, already available in the
  workspace as `Work.ORLocInd.FKS.freeGroup_separated_by_finite_p_group`;
* `injective_of_surjective_of_finite_index_subgroups` : the classical criterion.

The last theorem, `freeGroup_fin_two_hopfian`, is the statement requested by our colleague.
-/

namespace Work.OROneRel

universe u

/-- A monoid homomorphism out of a finitely generated group is determined by its values on a finite
generating set; hence there are only finitely many of them when the target is finite. -/
theorem finite_monoidHom_of_fg {G : Type*} [Group G] [Group.FG G] {M : Type*} [Monoid M]
    [Finite M] : Finite (G →* M) := by
  obtain ⟨S, hS⟩ := Subgroup.isMulFG_iff.mp (Group.fg_def.mp ‹Group.FG G›)
  refine Finite.of_injective (fun φ : G →* M ↦ fun s : (S : Set G) ↦ φ s) ?_
  intro φ ψ hφψ
  refine MonoidHom.ext fun x ↦ ?_
  have hx : x ∈ Subgroup.closure (S : Set G) := hS ▸ Subgroup.mem_top x
  exact MonoidHom.eqOn_closure (f := φ) (g := ψ) (s := (S : Set G))
    (fun s _ ↦ congrFun hφψ ⟨s, (Finset.mem_coe.mp ‹s ∈ (S : Set G)›)⟩) hx

/-- **A subgroup of index `n` is the stabiliser of a point of a degree-`n` permutation
representation.**  Take the (left) action of `G` on its own cosets `G ⧸ H`, which is transitive
with `n` elements, transport it along any bijection `G ⧸ H ≃ Fin n`, and take the point given by
the coset `H`; the stabiliser of that point is exactly `H`. -/
theorem exists_perm_repr_of_index_aux {G : Type*} [Group G] (H : Subgroup G) {n : ℕ} (hn : n ≠ 0)
    (hH : H.index = n) :
    ∃ ψ : G →* Equiv.Perm (Fin n), ∃ p : Fin n, ∀ g : G, g ∈ H ↔ ψ g p = p := by
  have hne : H.index ≠ 0 := by rw [hH]; exact hn
  haveI : Finite (G ⧸ H) := Subgroup.index_ne_zero_iff_finite.mp hne
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcard : Fintype.card (G ⧸ H) = n := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hH]
  let e : (G ⧸ H) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let q : G ⧸ H := QuotientGroup.mk (1 : G)
  let ψ : G →* Equiv.Perm (Fin n) :=
    (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))
  refine ⟨ψ, e q, fun g ↦ ?_⟩
  have h1 : ψ g (e q) = e (g • q) := by
    simp only [ψ, q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe,
      Equiv.permCongr_apply, Equiv.symm_apply_apply, MulAction.toPermHom_apply,
      MulAction.toPerm_apply]
  rw [h1, e.injective.eq_iff, ← MulAction.mem_stabilizer_iff]
  rw [MulAction.stabilizer_quotient H]

/-- **The counting half of "a finitely generated group has finitely many subgroups of a given
finite index".**  If every subgroup `H` of index `n` is the stabiliser of a point of some
degree-`n` permutation representation of `G`, then there are only finitely many such `H`: each `H`
is recovered from the pair (representation, point), and there are finitely many of those because
`G` is finitely generated. -/
theorem finite_subgroups_of_index_of_perm_repr {G : Type*} [Group G] [Group.FG G] (n : ℕ)
    (hn : n ≠ 0)
    (h : ∀ H : Subgroup G, H.index = n → ∃ ψ : G →* Equiv.Perm (Fin n), ∃ p : Fin n,
      ∀ g : G, g ∈ H ↔ ψ g p = p) :
    Set.Finite {H : Subgroup G | H.index = n} := by
  haveI : Finite (G →* Equiv.Perm (Fin n)) := finite_monoidHom_of_fg
  let ψ : {H : Subgroup G // H.index = n} → G →* Equiv.Perm (Fin n) :=
    fun H ↦ (h H.1 H.2).choose
  let p : {H : Subgroup G // H.index = n} → Fin n :=
    fun H ↦ (h H.1 H.2).choose_spec.choose
  have hψp : ∀ (H : {H : Subgroup G // H.index = n}) (g : G),
      g ∈ H.1 ↔ ψ H g (p H) = p H :=
    fun H ↦ (h H.1 H.2).choose_spec.choose_spec
  have hF : Function.Injective (fun H : {H : Subgroup G // H.index = n} ↦ (ψ H, p H)) := by
    intro H K hHK
    have h1 : ψ H = ψ K := congrArg Prod.fst hHK
    have h2 : p H = p K := congrArg Prod.snd hHK
    refine Subtype.ext ?_
    ext g
    rw [hψp H g, hψp K g, h1, h2]
  haveI : Finite {H : Subgroup G // H.index = n} := Finite.of_injective _ hF
  exact Set.finite_coe_iff.mp (inferInstance : Finite {H : Subgroup G // H.index = n})

/-- **A finitely generated group has only finitely many subgroups of any prescribed nonzero
index.** -/
theorem finite_subgroups_of_index_aux {G : Type*} [Group G] [Group.FG G] (n : ℕ) (hn : n ≠ 0) :
    Set.Finite {H : Subgroup G | H.index = n} :=
  finite_subgroups_of_index_of_perm_repr n hn fun H hH ↦ exists_perm_repr_of_index_aux H hn hH

/-- **P. Hall (1950)**: a finitely generated free group is residually finite.  This is immediate
from the workspace theorem that such a group is residually a finite `p`-group
(`Work.ORLocInd.FKS.freeGroup_separated_by_finite_p_group`): the kernel of a finite quotient
separating `w ≠ 1` is a finite-index subgroup missing `w`. -/
theorem freeGroup_residuallyFinite_aux {α : Type u} [Fintype α] :
    Group.ResiduallyFinite (FreeGroup α) := by
  have key : ∀ w : FreeGroup α, w ≠ 1 →
      ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q) (_ : IsPGroup 2 Q)
        (ψ : FreeGroup α →* Q), ψ w ≠ 1 :=
    fun w hw ↦
      Work.ORLocInd.FKS.freeGroup_separated_by_finite_p_group (α := α) (p := 2) Nat.prime_two w hw
  rw [Group.residuallyFinite_iff_exists_finiteIndex]
  intro w hw
  obtain ⟨Q, hQ, hFin, _hP, ψ, hψ⟩ := key w hw
  haveI := hFin
  exact ⟨ψ.ker, Subgroup.finiteIndex_ker ψ, by simpa [MonoidHom.mem_ker] using hψ⟩

/-- **Auxiliary (the classical criterion).**  If `G` is finitely generated and residually finite,
and has only finitely many subgroups of each prescribed *nonzero* index, then every surjective
endomorphism of `G` is injective.

Proof: suppose `K = ker f ≠ ⊥`.  By residual finiteness there is a finite-index subgroup `N` with
`K ⊄ N`; let `n = [G : N] ≠ 0`.  The map `T : H ↦ f ⁻¹' H` sends the set of subgroups of index `n`
into itself (indices are preserved because `f` is onto) and is injective, hence --- that set being
finite --- surjective.  So `f ⁻¹' N₁ = N` for some subgroup `N₁` of index `n`.  But `K ⊆ f ⁻¹' N₁`
(as `f` kills `K`) while `K ⊄ N`, a contradiction. -/
theorem injective_of_surjective_of_finite_index_subgroups {G : Type*} [Group G] [Group.FG G]
    [Group.ResiduallyFinite G]
    (hfin : ∀ n : ℕ, n ≠ 0 → Set.Finite {H : Subgroup G | H.index = n})
    (f : G →* G) (hf : Function.Surjective f) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff f]
  by_contra hbot
  obtain ⟨k, hk⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := f.ker)).mp hbot
  have hkne : (k : G) ≠ 1 := fun h ↦ hk (Subtype.ext h)
  obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem (k : G) hkne
  set n : ℕ := (N : Subgroup G).index with hn
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact Subgroup.finiteIndex_iff.mp N.isFiniteIndex'
  have hfin' : Set.Finite {H : Subgroup G | H.index = n} := hfin n hn0
  haveI : Finite {H : Subgroup G // H.index = n} := hfin'.to_subtype
  -- the self-map `H ↦ f ⁻¹' H` of the subgroups of index `n`
  let T : {H : Subgroup G // H.index = n} → {H : Subgroup G // H.index = n} :=
    fun H ↦ ⟨H.1.comap f, by rw [Subgroup.index_comap_of_surjective H.1 hf, H.2]⟩
  have hinjT : Function.Injective T := by
    intro H K hHK
    have h1 : H.1.comap f = K.1.comap f := congrArg Subtype.val hHK
    refine Subtype.ext ?_
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hf x
      have hyH : y ∈ H.1.comap f := by rw [Subgroup.mem_comap, hy]; exact hx
      have hyK : y ∈ K.1.comap f := h1 ▸ hyH
      rwa [Subgroup.mem_comap, hy] at hyK
    · intro hx
      obtain ⟨y, hy⟩ := hf x
      have hyK : y ∈ K.1.comap f := by rw [Subgroup.mem_comap, hy]; exact hx
      have hyH : y ∈ H.1.comap f := h1.symm ▸ hyK
      rwa [Subgroup.mem_comap, hy] at hyH
  have hsurjT : Function.Surjective T := (Finite.injective_iff_surjective).mp hinjT
  obtain ⟨H₁, hH₁⟩ := hsurjT ⟨(N : Subgroup G), hn.symm⟩
  have hcomap : H₁.1.comap f = (N : Subgroup G) := congrArg Subtype.val hH₁
  have hkker : f (k : G) = 1 := MonoidHom.mem_ker.mp k.2
  have hmem : (k : G) ∈ H₁.1.comap f := by
    rw [Subgroup.mem_comap, hkker]
    exact H₁.1.one_mem
  rw [hcomap] at hmem
  exact hN hmem

/-- **`F₂` is Hopfian**: every surjective endomorphism of the free group on two generators is
injective (equivalently, is an automorphism). -/
theorem freeGroup_fin_two_hopfian (f : FreeGroup (Fin 2) →* FreeGroup (Fin 2))
    (hf : Function.Surjective f) : Function.Injective f := by
  haveI : Group.ResiduallyFinite (FreeGroup (Fin 2)) :=
    freeGroup_residuallyFinite_aux (α := Fin 2)
  exact injective_of_surjective_of_finite_index_subgroups
    (fun n hn ↦ finite_subgroups_of_index_aux n hn) f hf

end Work.OROneRel
