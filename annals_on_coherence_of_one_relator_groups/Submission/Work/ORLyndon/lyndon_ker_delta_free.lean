import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORFP2.augIdeal_freeGroup_injective

/-!
# `δ` has trivial kernel for the trivial relator: `ker δ = ⊥`

The presentation `⟨X | 1⟩` with the single *trivial* relator is the free group `F(X)`; the second
map of its Lyndon complex is

`δ : K[G]^X → K[G],   (a_x) ↦ Σ_x a_x (x - 1)`,

where `G = ⟨X | 1⟩`.  This file proves that `δ` is injective, i.e.

`LinearMap.ker (lyndonDelta K 1) = ⊥`,

which is the statement that the augmentation ideal of `K[F(X)]` is a *free* left
`K[F(X)]`-module with basis the elements `x - 1` (`x ∈ X`), transported along the canonical
isomorphism `K[F(X)] ≅ K[⟨X | 1⟩]`.

The argument is:

* the canonical surjection `presentRho 1 : F(X) →* ⟨X | 1⟩` is bijective (the normal closure of the
  trivial relator is trivial, and the images of the generators generate the presented group), so it
  induces a ring isomorphism `E : K[F(X)] ≃+* K[⟨X | 1⟩]` (`trivialPresentRingEquiv`);
* the free version `b ↦ Σ_x b_x (x - 1)` of `δ` has trivial kernel: this is
  `Work.ORFP2.augIdeal_freeGroup_injective`, proved by exhibiting an inverse built from the Fox
  derivative `∂/∂x`;
* `E` intertwines the two maps (`lyndonDelta_one_mapRange`); since `E` is bijective, injectivity
  transfers from the free case to `δ`.

## Main results

* `Work.ORLyndon.presentRho_one_bijective`: `F(X) →* ⟨X | 1⟩` is bijective.
* `Work.ORLyndon.trivialPresentRingEquiv_of`, `Work.ORLyndon.lyndonDelta_one_mapRange`: the
  transport identities along `E`.
* `Work.ORLyndon.lyndon_ker_delta_free`: `ker δ = ⊥`.
-/

namespace Work.ORLyndon

open MonoidAlgebra

section TrivialRelator

variable {X : Type*} [DecidableEq X] {K : Type*} [Field K]

/-- The group presented by `⟨X | 1⟩`, i.e. with the single trivial relator, is the free group
`F(X)`: the canonical surjection `presentRho 1 : F(X) →* ⟨X | 1⟩` is bijective.  Injectivity holds
because the normal closure of `{1}` is trivial, surjectivity because the images of the generators
generate `⟨X | 1⟩`. -/
theorem presentRho_one_bijective : Function.Bijective (presentRho (1 : FreeGroup X)) := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker, presentRho_apply, PresentedGroup.mk_eq_one_iff] at hx
    have h1 : Subgroup.normalClosure ({1} : Set (FreeGroup X)) = ⊥ :=
      (Subgroup.normalClosure_eq_bot_iff (s := ({1} : Set (FreeGroup X)))).mpr (fun y hy => hy)
    rw [h1, Subgroup.mem_bot] at hx
    exact hx
  · exact PresentedGroup.mk_surjective _

/-- The ring isomorphism `K[F(X)] ≃+* K[⟨X | 1⟩]` induced by the presentation `⟨X | 1⟩` of the
free group. -/
noncomputable def trivialPresentRingEquiv :
    MonoidAlgebra K (FreeGroup X) ≃+*
      MonoidAlgebra K (OneRelatorGroup (1 : FreeGroup X)) :=
  MonoidAlgebra.mapDomainRingEquiv K
    (MulEquiv.ofBijective (presentRho (1 : FreeGroup X)) presentRho_one_bijective)

/-- `trivialPresentRingEquiv` maps the group algebra basis element `of w` onto
`of (presentRho 1 w)`. -/
theorem trivialPresentRingEquiv_of (w : FreeGroup X) :
    trivialPresentRingEquiv (X := X) (K := K) ((MonoidAlgebra.of K (FreeGroup X)) w) =
      (MonoidAlgebra.of K (OneRelatorGroup (1 : FreeGroup X)))
        (presentRho (1 : FreeGroup X) w) := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply]
  change (MonoidAlgebra.mapDomainRingEquiv K
      (MulEquiv.ofBijective (presentRho (1 : FreeGroup X)) presentRho_one_bijective))
        (MonoidAlgebra.single w (1 : K)) = MonoidAlgebra.single
        (presentRho (1 : FreeGroup X) w) (1 : K)
  rw [MonoidAlgebra.mapDomainRingEquiv_single]
  rfl

/-- **Transport identity.**  The ring isomorphism `trivialPresentRingEquiv` intertwines the second
map `δ` of the Lyndon complex of `⟨X | 1⟩` with its free counterpart `b ↦ Σ_x b_x (x - 1)` in
`K[F(X)]`.  Both sides are additive in `b`, and they agree on the finitely supported generators
`b = single x c`. -/
theorem lyndonDelta_one_mapRange (b : X →₀ MonoidAlgebra K (FreeGroup X)) :
    lyndonDelta K (1 : FreeGroup X)
        (Finsupp.mapRange (⇑(trivialPresentRingEquiv (X := X) (K := K))) (map_zero _) b) =
      trivialPresentRingEquiv (X := X) (K := K)
        (b.sum (fun x c =>
          c * ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1))) := by
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      have hmap : Finsupp.mapRange (⇑(trivialPresentRingEquiv (X := X) (K := K)))
            (map_zero _) (f + g)
          = Finsupp.mapRange (⇑(trivialPresentRingEquiv (X := X) (K := K))) (map_zero _) f
            + Finsupp.mapRange (⇑(trivialPresentRingEquiv (X := X) (K := K))) (map_zero _) g :=
        Finsupp.mapRange_add (map_add (trivialPresentRingEquiv (X := X) (K := K))) f g
      have hsum :
          (f + g).sum (fun x c =>
              c * ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1))
            = f.sum (fun x c =>
                c * ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1))
              + g.sum (fun x c =>
                c * ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1)) :=
        Finsupp.sum_add_index (fun a _ => by simp) (fun a _ b₁ b₂ => by rw [add_mul])
      rw [hmap, map_add, hf, hg, hsum, map_add]
  | single x c =>
      rw [Finsupp.mapRange_single, lyndonDelta_apply,
        Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp),
        map_mul, map_sub, map_one]
      rw [trivialPresentRingEquiv_of (X := X) (K := K) (FreeGroup.of x), presentAlg_of]

/-- The transport identity in the form used below: the free version of `δ` agrees with
`presentAlg K 1` composed with the map `b ↦ Σ_x b_x (x - 1)`. -/
theorem lyndonDelta_one_eq (b : X →₀ MonoidAlgebra K (FreeGroup X)) :
    lyndonDelta K (1 : FreeGroup X)
        (Finsupp.mapRange (⇑(trivialPresentRingEquiv (X := X) (K := K))) (map_zero _) b) =
      (presentAlg K (1 : FreeGroup X))
        (b.sum (fun x c =>
          c * ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1))) := by
  rw [lyndonDelta_one_mapRange (X := X) (K := K) b]
  rfl

end TrivialRelator

theorem lyndon_ker_delta_free {X : Type*} [DecidableEq X] {K : Type*} [Field K] :
    LinearMap.ker (Work.ORLyndon.lyndonDelta K (1 : FreeGroup X)) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro a ha
  -- lift `a` to `K[F(X)]^X` along the ring isomorphism `E = trivialPresentRingEquiv`
  obtain ⟨b, hb⟩ := Finsupp.mapRange_surjective
    (⇑(trivialPresentRingEquiv (X := X) (K := K))) (map_zero _)
    (trivialPresentRingEquiv (X := X) (K := K)).surjective a
  -- the lift dies in the free version of `δ`, by the injectivity of the free map
  have hbzero : b = 0 := by
    have hd : b.sum (fun x c =>
        c * ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of x) - 1)) = 0 := by
      apply (trivialPresentRingEquiv (X := X) (K := K)).injective
      rw [map_zero, ← lyndonDelta_one_mapRange (X := X) (K := K) b, hb, ha]
    refine Work.ORFP2.augIdeal_freeGroup_injective K X ?_
    simpa [MonoidAlgebra.of_apply, Finsupp.sum_zero_index] using hd
  rw [← hb, hbzero]
  simp

end Work.ORLyndon
