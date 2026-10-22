import Mathlib

namespace Work.ANALYTIC

open CategoryTheory CategoryTheory.Limits

universe u v

/-! ## Colimits in `Type` over discrete diagrams are van Kampen

We prove that every colimit cocone over a discrete diagram in `Type` is a van Kampen colimit,
i.e. that coproducts in `Type` are stable under pullback.  The proof is a direct
type-theoretic one:

* A cocone `c` over `F : Discrete ι ⥤ Type` is a colimit iff the canonical map
  `(Σ i, F.obj i) → c.pt`, `⟨i, x⟩ ↦ c.ι.app i x` is bijective
  (`nonempty_isColimit_iff_bijective_sigma`).
* The van Kampen condition for a cocone over a discrete diagram then reduces to a purely
  set-theoretic statement about two "jointly bijective" maps `p`, `q` and a compatible map `f`
  (`isPullback_forall_of_bijective_sigma`, `bijective_sigma_of_forall_isPullback`).
-/

/-- For a functor `F : Discrete ι ⥤ Type v`, the relation generating the colimit type is
trivial: two elements of `Σ i, F.obj i` related by `F.ColimitTypeRel` are equal.  (A morphism of
a discrete category which is not an identity lives in an empty hom set, and a functor sends
identities to identities.) -/
private lemma eq_of_colimitTypeRel {ι : Type u} {F : Discrete ι ⥤ Type v}
    {p p' : Σ i : Discrete ι, F.obj i} (h : F.ColimitTypeRel p p') : p = p' := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨⟨i⟩, x⟩ := p
  obtain ⟨⟨j⟩, y⟩ := p'
  obtain rfl : i = j := Discrete.eq_of_hom f
  dsimp only at hf
  have hy : y = x := by
    rw [hf, Subsingleton.elim f (𝟙 _), F.map_id]
    rfl
  subst hy
  rfl

/-- The canonical map `Σ i, F.obj i → F.ColimitType` is bijective for a discrete index. -/
private lemma bijective_quotientMap {ι : Type u} (F : Discrete ι ⥤ Type v) :
    Function.Bijective (fun z : Σ i : Discrete ι, F.obj i => F.ιColimitType z.1 z.2) := by
  constructor
  · intro z z' h
    have hq : Quot.mk F.ColimitTypeRel z = Quot.mk F.ColimitTypeRel z' := h
    have h2 := congrArg (Quot.lift (id : (Σ i : Discrete ι, F.obj i) → Σ i : Discrete ι, F.obj i)
      (fun a b hab => eq_of_colimitTypeRel hab)) hq
    simpa using h2
  · intro t
    obtain ⟨j, x, hx⟩ := F.ιColimitType_jointly_surjective t
    exact ⟨⟨j, x⟩, hx⟩

/-- **Criterion for a cocone over a discrete diagram in `Type` to be a colimit.**

A cocone over a discrete diagram in `Type` is a colimit iff the canonical map
`(Σ i, F.obj i) → c.pt`, `⟨i, x⟩ ↦ c.ι.app i x` is bijective. -/
lemma nonempty_isColimit_iff_bijective_sigma {ι : Type u} {F : Discrete ι ⥤ Type v}
    (c : Cocone F) :
    Nonempty (IsColimit c) ↔
      Function.Bijective (fun z : Σ i : Discrete ι, F.obj i => c.ι.app z.1 z.2) := by
  have hg : Function.Bijective (fun z : Σ i : Discrete ι, F.obj i => F.ιColimitType z.1 z.2) :=
    bijective_quotientMap F
  have heq : (F.descColimitType (F.coconeTypesEquiv.symm c)) ∘
      (fun z : Σ i : Discrete ι, F.obj i => F.ιColimitType z.1 z.2) =
      (fun z : Σ i : Discrete ι, F.obj i => c.ι.app z.1 z.2) := by
    funext z
    obtain ⟨i, x⟩ := z
    exact F.descColimitType_ιColimitType_apply (F.coconeTypesEquiv.symm c) i x
  rw [Types.isColimit_iff_coconeTypesIsColimit]
  have hiff : (F.coconeTypesEquiv.symm c).IsColimit ↔
      Function.Bijective (F.descColimitType (F.coconeTypesEquiv.symm c)) :=
    ⟨fun h => h.bijective, fun h => ⟨h⟩⟩
  rw [hiff, ← Function.Bijective.of_comp_iff _ hg, heq]
  rfl

/-- **A pullback square from jointly bijective "coproduct" maps.**

If `p : ∀ i, Y i → P` and `q : ∀ i, X i → Q` are the injections of coproducts (i.e. the
canonical maps out of `Σ i, Y i` and `Σ i, X i` are bijective) and `a`, `f` commute with them,
then each square is a pullback. -/
lemma isPullback_forall_of_bijective_sigma {I : Type u} {X Y : I → Type v} {P Q : Type v}
    (p : ∀ i, Y i ⟶ P) (q : ∀ i, X i ⟶ Q) (a : ∀ i, Y i ⟶ X i) (f : P ⟶ Q)
    (hcomm : ∀ i (y : Y i), f (p i y) = q i (a i y))
    (hbX : Function.Bijective (fun z : Σ i, X i => q z.1 z.2))
    (hbY : Function.Bijective (fun z : Σ i, Y i => p z.1 z.2)) :
    ∀ i, IsPullback (p i) (a i) f (q i) := by
  intro i
  refine (Types.isPullback_iff (p i) f (a i) (q i)).mpr ⟨?_, ?_, ?_⟩
  · ext y
    exact hcomm i y
  · intro x₁ y₁ h
    have h' : (⟨i, x₁⟩ : Σ i, Y i) = ⟨i, y₁⟩ := hbY.1 (by simpa using h.1)
    exact eq_of_heq (Sigma.mk.injEq .. |>.mp h').2
  · intro x₂ x₃ hx
    obtain ⟨⟨j, y⟩, hy⟩ := hbY.2 x₂
    have hy' : p j y = x₂ := hy
    have hq : q j (a j y) = q i x₃ := by rw [← hcomm j y, hy', hx]
    have h' : (⟨j, a j y⟩ : Σ k, X k) = ⟨i, x₃⟩ := hbX.1 hq
    obtain rfl : j = i := congrArg Sigma.fst h'
    exact ⟨y, hy', eq_of_heq (Sigma.mk.injEq .. |>.mp h').2⟩

/-- **The converse: a jointly bijective "coproduct" map from pullback squares.**

If each square
```
Y i --p i--> P
 |            |
a i          f
 v            v
X i --q i--> Q
```
is a pullback and the `q i` form a coproduct (bijectivity of the canonical map out of `Σ i, X i`),
then the `p i` form a coproduct. -/
lemma bijective_sigma_of_forall_isPullback {I : Type u} {X Y : I → Type v} {P Q : Type v}
    (p : ∀ i, Y i ⟶ P) (q : ∀ i, X i ⟶ Q) (a : ∀ i, Y i ⟶ X i) (f : P ⟶ Q)
    (hcomm : ∀ i (y : Y i), f (p i y) = q i (a i y))
    (hbX : Function.Bijective (fun z : Σ i, X i => q z.1 z.2))
    (hP : ∀ i, IsPullback (p i) (a i) f (q i)) :
    Function.Bijective (fun z : Σ i, Y i => p z.1 z.2) := by
  constructor
  · intro z z' h
    obtain ⟨i, x₁⟩ := z
    obtain ⟨j, x₂⟩ := z'
    change p i x₁ = p j x₂ at h
    have hq : q i (a i x₁) = q j (a j x₂) := by rw [← hcomm i x₁, ← hcomm j x₂, h]
    have h' : (⟨i, a i x₁⟩ : Σ k, X k) = ⟨j, a j x₂⟩ := hbX.1 hq
    obtain rfl : i = j := congrArg Sigma.fst h'
    have ha : a i x₁ = a i x₂ := eq_of_heq (Sigma.mk.injEq .. |>.mp h').2
    have hx : x₁ = x₂ := Types.ext_of_isPullback (hP i) h ha
    subst hx
    rfl
  · intro x₂
    obtain ⟨⟨j, y⟩, hy⟩ := hbX.2 (f x₂)
    have hy' : q j y = f x₂ := hy
    obtain ⟨x₁, h1, -⟩ := Types.exists_of_isPullback (hP j) x₂ y (by rw [hy'])
    exact ⟨⟨j, x₁⟩, h1⟩

/-- **Colimits in `Type` are van Kampen (stable under pullback).**

Every colimit cocone over a discrete diagram in `Type` is a van Kampen colimit, i.e. coproducts
in `Type` are stable under pullback.  It suffices to prove this for the "standard" coproduct cofan
`Cofan.mk (Sigma i, X i) (fun i => fun x => (i, x))` of a family `X : ι → Type`: an arbitrary
`F : Discrete ι ⥤ Type` can be replaced by `Discrete.functor (fun i => F.obj i)` using
`Functor.hext`, and `IsVanKampenColimit.of_iso` transfers van Kampen-ness across an isomorphism of
cocones.

Unfolding `IsVanKampenColimit` for such a cocone, with `g i := c'.ι.app ⟨i⟩`,
`a i := α.app ⟨i⟩`, the goal is `Nonempty (IsColimit c') ↔ ∀ i, IsPullback (g i) (a i) f (σ.ι.app ⟨i⟩)`.

* Reverse direction: by `CofanTypes.isColimit_iff_bijective_fromSigma`, `IsColimit` of a cofan in
  `Type` is bijectivity of `⟨i, x⟩ ↦ g i x`.  Surjectivity: given `q : c'.pt`, write
  `f q = ⟨j, y⟩`; then `Types.exists_of_isPullback (hP j)` applied to `q` and `y` (using
  `g j ≫ f = a j ≫ σ.ι j` from the cocone condition) yields `x` with `g j x = q`.  Injectivity
  follows from `Types.ext_of_isPullback (hP j)`.
* Forward direction: conversely `IsColimit c'` gives that bijection, and `Types.isPullback_iff`
  reduces each pullback condition to its three clauses, all immediate from the bijection and the
  cocone condition. -/
theorem isVanKampenColimit_of_isColimit_types {ι : Type} {F : CategoryTheory.Functor (CategoryTheory.Discrete ι) Type} {c : CategoryTheory.Limits.Cocone F} (hc : CategoryTheory.Limits.IsColimit c) : CategoryTheory.IsVanKampenColimit c := by
  intro F' c' α f hcomp hα
  have hcomm : ∀ i : Discrete ι, ∀ y : F'.obj i,
      f (c'.ι.app i y) = c.ι.app i (α.app i y) := by
    intro i y
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hcomp i) y
    simpa using h.symm
  have hbX : Function.Bijective (fun z : Σ i : Discrete ι, F.obj i => c.ι.app z.1 z.2) :=
    (nonempty_isColimit_iff_bijective_sigma c).mp ⟨hc⟩
  constructor
  · intro hc'
    exact isPullback_forall_of_bijective_sigma (fun i => c'.ι.app i) (fun i => c.ι.app i)
      (fun i => α.app i) f hcomm hbX ((nonempty_isColimit_iff_bijective_sigma c').mp hc')
  · intro hP
    exact (nonempty_isColimit_iff_bijective_sigma c').mpr
      (bijective_sigma_of_forall_isPullback (fun i => c'.ι.app i) (fun i => c.ι.app i)
        (fun i => α.app i) f hcomm hbX hP)

end Work.ANALYTIC
