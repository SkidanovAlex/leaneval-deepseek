import Mathlib
import Submission.NK.TameData.Definitions

open scoped Classical

namespace NK.TameData.Abelianisation

/-! ## The torsion of a direct product, with one torsion-free factor

Shimizu's Lemma 2.1 (`NK.TameData.TameAbelianisationInput`) exhibits the abelianised tame
quotient of a `p`-adic field as a direct product `Ẑ × μ_{q-1}`.  The torsion of such a product
is the second factor, because `Ẑ` is torsion-free.  The Mathlib group `Ẑ`
(`NK.LocalAnabelian.Zhat`, the profinite completion of `ℤ`) is only known to be a *group*, not
a commutative group, so the product is not known to be commutative and Mathlib's
`CommGroup.torsion` — which needs a `CommGroup` — cannot be evaluated on it.  The extraction is
therefore done by hand, through `IsOfFinOrder`, which is available for arbitrary monoids. -/

/-- **The torsion of a direct product with a torsion-free factor.**  If `A ≃* G × H`, `G` is
torsion-free and every element of `H` has finite order — a `CommGroup` `H` that is an entire
torsion group — then the torsion subgroup of `A` is isomorphic to `H`.

The isomorphism is the composite of the given isomorphism with the second projection; it is
injective because an element of `G × H` lying in the kernel is `(g, 1)` with `g` of finite
order, hence `g = 1`, and surjective because `(1, h)` has finite order for every `h ∈ H`.

Note that the hypothesis on `H` is stated as `∀ x : H, IsOfFinOrder x` rather than as
`CommGroup.torsion H = ⊤` so that `H` needs only a `Group` structure in the applications: the
product `G × H` need not be known to be commutative. -/
theorem torsion_mulEquiv_of_mulEquiv_prod {A G H : Type*} [CommGroup A] [Group G] [Group H]
    [IsMulTorsionFree G] (hH : ∀ x : H, IsOfFinOrder x) (e : A ≃* (G × H)) :
    Nonempty (↥(CommGroup.torsion A) ≃* H) := by
  let φ : ↥(CommGroup.torsion A) →* H :=
    (MonoidHom.snd G H).comp (e.toMonoidHom.comp (CommGroup.torsion A).subtype)
  have hφ : ∀ z : ↥(CommGroup.torsion A), φ z = (e (z : A)).2 := fun z => rfl
  refine ⟨MulEquiv.ofBijective φ ⟨?_, ?_⟩⟩
  · -- injectivity: the kernel is trivial, since `G` is torsion-free
    rw [← MonoidHom.ker_eq_bot_iff φ, Subgroup.eq_bot_iff_forall]
    intro z hz
    have hz2 : IsOfFinOrder (e (z : A)) :=
      (Function.Injective.isOfFinOrder_iff (f := (e : A →* G × H)) e.injective).mpr
        ((CommGroup.mem_torsion (z : A)).mp z.2)
    obtain ⟨h1, h2⟩ := IsOfFinOrder.prod_iff.mp hz2
    have he1 : (e (z : A)).1 = 1 := (isOfFinOrder_iff_eq_one _).mp h1
    have he2 : (e (z : A)).2 = 1 := by rw [← hφ]; exact hz
    have hone : (z : A) = 1 := e.injective (by rw [map_one]; exact Prod.ext he1 he2)
    exact Subtype.ext hone
  · -- surjectivity: `(1, h)` is a torsion element mapping to `h`
    intro b
    refine ⟨⟨e.symm (1, b), ?_⟩, ?_⟩
    · rw [CommGroup.mem_torsion]
      exact (Function.Injective.isOfFinOrder_iff (f := (e.symm : (G × H) →* A))
        e.symm.injective).mpr
        (IsOfFinOrder.prod_iff.mpr ⟨IsOfFinOrder.one, hH b⟩)
    · rw [hφ, MulEquiv.apply_symm_apply]

/-- **Shimizu's 2.1 in its literal form, derived from the splitting of the abelianised tame
quotient**: if `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` (`NK.TameData.TameAbelianisationInput`) then the
torsion of `G_κ^{tr,ab}` is cyclic of order `q - 1`, i.e. isomorphic to `Multiplicative (ZMod (q-1))`.

The torsion of the product is the product of the torsions; that of `Ẑ` is trivial because `Ẑ` is
torsion-free, and `Multiplicative (ZMod (q-1))` is an entire torsion group.  Note the statement is
a `≃*` of the *subgroup* `NK.LocalTame.tameTorsion`, so the construction has to keep track of the
subgroup structures (the target product is not known to be commutative, since Mathlib knows only
that `Ẑ` is a group). -/
theorem torsion_mulEquiv_zmod {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] {p q : ℕ} (h : NK.TameData.TameAbelianisationInput p q κ K')
    [IsMulTorsionFree NK.LocalAnabelian.Zhat] :
    Nonempty (↥(NK.LocalTame.tameTorsion (κ := κ) (K' := K') p) ≃*
      Multiplicative (ZMod (q - 1))) := by
  obtain ⟨f, hf, hqf⟩ := h.q_eq
  -- `q = p ^ f` with `p` prime and `f > 0`, so `q - 1 > 0`
  have hq2 : 1 < q := by rw [hqf]; exact Nat.one_lt_pow hf.ne' h.hp.one_lt
  have hne : NeZero (q - 1) := ⟨by omega⟩
  -- every element of `μ_{q-1}` has finite order
  have hH : ∀ x : Multiplicative (ZMod (q - 1)), IsOfFinOrder x := fun x => by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨q - 1, NeZero.pos (q - 1), by ext; simp [toAdd_pow]⟩
  obtain ⟨e⟩ := h.nonempty_iso
  exact torsion_mulEquiv_of_mulEquiv_prod hH e

end NK.TameData.Abelianisation
