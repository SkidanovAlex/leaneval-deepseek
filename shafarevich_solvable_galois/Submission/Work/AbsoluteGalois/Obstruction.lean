/-
Copyright (c) 2025. All rights reserved.

# The obstruction calculus: the fibre product of an embedding problem with `G_ℚ`

This file provides the vocabulary that links the lifting formulation of embedding problems
(`Work.AbsoluteGalois.HasSurjectiveLift`) with the group-cohomological obstruction calculus.

## The dictionary

Let `E : Submission.EmbeddingProblem ℚ`, `M : E.ClosureModel` (so `E.L` is identified with a
subfield `M.L ⊆ ℚ̄`), and let

`M.pi : E.G →* Gal(M.L/ℚ)`

be the projection induced by `E.π` and the identification `M.e`.  A **lift** of `E.π` along the
restriction map is a homomorphism `ψ : G_ℚ →* E.G` with `M.pi.comp ψ = restrictHom M.L`.  Such
lifts are exactly the homomorphic sections of the projection of the fibre product

`pullback E M ⊆ G_ℚ × E.G`,  `pullback E M = {(σ, g) | restrictHom M.L σ = M.pi g}`,

which is an extension of `Gal(M.L/ℚ)` by the kernel of `E.π`.  Thus the lifting formulation of
the embedding problem is precisely the classical statement that the embedding problem *splits*
the restriction map; `HasSurjectiveLift` additionally demands that the splitting be surjective,
which is a strictly stronger condition: for a *split* embedding problem the extension class
vanishes and a plain lift exists (`ψ = σ ∘ ρ` for a section `σ` of `E.π`), but such a `ψ` is not
surjective when the kernel is non-trivial, and a surjective lift need not exist.

## Group cohomology

Choosing a set-theoretic section `s` of `E.π` produces the `2`-cocycle
`c (q, r) = s q * s r * (s (q * r))⁻¹ ∈ ker E.π`, whose class in `H²(Gal(E.L/ℚ), ker E.π)` is the
**extension class** of `E` (this is well defined because `ker E.π` is abelian in the applications,
so that conjugation turns it into a `Gal(E.L/ℚ)`-module).  In the classical calculus the class is
pulled back along `ρ := restrictHom M.L`:

`ρ^* : H²(Gal(E.L/ℚ), ker E.π) → H²(G_ℚ, ker E.π)`,

and a lift of `E.π` along `ρ` — i.e. a splitting of `pullback E M` over `G_ℚ` — exists if and only
if `ρ^* c` is a coboundary, i.e. if and only if the obstruction class vanishes.  The elementary
group-theoretic content of that statement (the twisted extension attached to a `2`-cocycle splits
if and only if the cocycle is a coboundary) is developed in
`Submission/Work/GroupCohomology/`; here we provide the pullback of cochains and the dictionary
between lifts and splittings.

## Main declarations

* `ClosureModel.pi`, `pullback`, `pullbackFst`, `pullbackFst_surjective`, `pullbackKerEquiv`;
* `ClosureModel.exists_lift_iff_exists_section` — lifts = sections of the fibre product;
* `pullbackCocycle` — the pullback of a `2`-cochain along a group homomorphism.
-/
import Mathlib
import Submission.EmbeddingProblem
import Submission.Work.AbsoluteGalois.Basic
import Submission.Work.AbsoluteGalois.ClosureModel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

namespace EmbeddingProblem

namespace ClosureModel

variable {E : EmbeddingProblem ℚ} (M : E.ClosureModel)

/-- The projection `E.G →* Gal(M.L/ℚ)` obtained by composing `E.π` with the identification
`M.autCongr : Gal(E.L/ℚ) ≃* Gal(M.L/ℚ)` of the base field with its image in `ℚ̄`.  The embedding
problem `E` is solved by a surjection `ψ : G_ℚ ↠ E.G` exactly when `M.pi.comp ψ` is the
restriction map `restrictHom M.L`. -/
noncomputable def pi : E.G →* (↥M.L ≃ₐ[ℚ] ↥M.L) :=
  M.autCongr.toMonoidHom.comp E.π

@[simp]
lemma pi_apply (g : E.G) : M.pi g = M.autCongr (E.π g) := rfl

@[simp]
lemma pi_surjective : Function.Surjective M.pi :=
  M.autCongr.surjective.comp E.surjective

/-- The **fibre product** of the projection `M.pi : E.G →* Gal(M.L/ℚ)` with the restriction map
`restrictHom M.L : G_ℚ →* Gal(M.L/ℚ)`: the subgroup of `G_ℚ × E.G` of pairs `(σ, g)` with
`restrictHom M.L σ = M.pi g`.  Its projection to `G_ℚ` is surjective with kernel `ker E.π`, so it
is an extension of `Gal(M.L/ℚ)` by `ker E.π`; a lift of `E.π` along the restriction map is the
same thing as a splitting of this extension. -/
def pullback : Subgroup (Field.absoluteGaloisGroup ℚ × E.G) where
  carrier := {x | Work.AbsoluteGalois.restrictHom M.L x.1 = M.pi x.2}
  mul_mem' := by
    intro a b ha hb
    have ha' : (Work.AbsoluteGalois.restrictHom M.L) a.1 = M.pi a.2 := ha
    have hb' : (Work.AbsoluteGalois.restrictHom M.L) b.1 = M.pi b.2 := hb
    show (Work.AbsoluteGalois.restrictHom M.L) (a.1 * b.1) = M.pi (a.2 * b.2)
    rw [map_mul, map_mul, ha', hb']
  one_mem' := by
    show (Work.AbsoluteGalois.restrictHom M.L) (1 : Field.absoluteGaloisGroup ℚ) = M.pi 1
    rw [map_one, map_one]
  inv_mem' := by
    intro a ha
    have ha' : (Work.AbsoluteGalois.restrictHom M.L) a.1 = M.pi a.2 := ha
    show (Work.AbsoluteGalois.restrictHom M.L) a.1⁻¹ = M.pi a.2⁻¹
    rw [map_inv, map_inv, ha']

@[simp]
lemma mem_pullback {x : Field.absoluteGaloisGroup ℚ × E.G} :
    x ∈ M.pullback ↔ Work.AbsoluteGalois.restrictHom M.L x.1 = M.pi x.2 := Iff.rfl

/-- The projection of the fibre product to `G_ℚ`. -/
def pullbackFst : ↥M.pullback →* Field.absoluteGaloisGroup ℚ where
  toFun x := x.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
lemma pullbackFst_apply (x : ↥M.pullback) : M.pullbackFst x = x.1.1 := rfl

/-- The projection of the fibre product to `G_ℚ` is surjective (the restriction map is). -/
lemma pullbackFst_surjective : Function.Surjective M.pullbackFst := by
  intro σ
  obtain ⟨g, hg⟩ : ∃ g : E.G, M.pi g = Work.AbsoluteGalois.restrictHom M.L σ :=
    M.pi_surjective (Work.AbsoluteGalois.restrictHom M.L σ)
  exact ⟨⟨(σ, g), hg.symm⟩, rfl⟩

/-- The kernel of the projection of the fibre product is `ker E.π`: thus `pullback E M` is an
extension of `Gal(M.L/ℚ)` by `ker E.π`. -/
noncomputable def pullbackKerEquiv : M.pullbackFst.ker ≃* E.π.ker where
  toFun x := ⟨x.1.1.2, by
    have hx : (x.1.1.1 : Field.absoluteGaloisGroup ℚ) = 1 := x.2
    have h := M.mem_pullback.mp x.1.2
    rw [hx, map_one] at h
    exact (MulEquiv.map_eq_one_iff M.autCongr).mp h.symm⟩
  invFun g := ⟨⟨(1, g.1), by
    show (Work.AbsoluteGalois.restrictHom M.L) (1 : Field.absoluteGaloisGroup ℚ) = M.pi g.1
    rw [map_one, M.pi_apply, MonoidHom.mem_ker.mp g.2, map_one]⟩, by
    show M.pullbackFst ⟨(1, g.1), _⟩ = 1
    rfl⟩
  left_inv x := by
    have hx : (x.1.1.1 : Field.absoluteGaloisGroup ℚ) = 1 := x.2
    refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
    rw [hx]
  right_inv g := by
    refine Subtype.ext rfl
  map_mul' x y := rfl

/-- **Lifts are splittings.**  A homomorphism `ψ : G_ℚ →* E.G` with `M.pi.comp ψ = restrictHom M.L`
is the same thing as a homomorphic section of the projection of the fibre product. -/
theorem exists_lift_iff_exists_section :
    (∃ ψ : Field.absoluteGaloisGroup ℚ →* E.G,
        M.pi.comp ψ = Work.AbsoluteGalois.restrictHom M.L) ↔
      (∃ t : Field.absoluteGaloisGroup ℚ →* ↥M.pullback, M.pullbackFst.comp t = MonoidHom.id _) := by
  constructor
  · rintro ⟨ψ, hψ⟩
    have hψ' : ∀ σ, M.pi (ψ σ) = Work.AbsoluteGalois.restrictHom M.L σ := fun σ => by
      have := congrFun (congrArg DFunLike.coe hψ) σ
      simpa using this
    refine ⟨{ toFun := fun σ => ⟨(σ, ψ σ), (hψ' σ).symm⟩
              map_one' := by
                refine Subtype.ext (Prod.ext rfl ?_)
                exact map_one ψ
              map_mul' := fun σ τ => by
                refine Subtype.ext (Prod.ext rfl ?_)
                exact map_mul ψ σ τ }, ?_⟩
    ext σ
    rfl
  · rintro ⟨t, ht⟩
    have ht' : ∀ σ, (t σ).1.1 = σ := fun σ => by
      have := congrFun (congrArg DFunLike.coe ht) σ
      simpa using this
    refine ⟨{ toFun := fun σ => (t σ).1.2
              map_one' := by
                have h := congrArg (fun x : ↥M.pullback => x.1.2) (map_one t)
                simpa using h
              map_mul' := fun σ τ => by
                have h := congrArg (fun x : ↥M.pullback => x.1.2) (map_mul t σ τ)
                simpa using h }, ?_⟩
    refine MonoidHom.ext fun σ => ?_
    have h := M.mem_pullback.mp (t σ).2
    rw [ht' σ] at h
    exact h.symm

/-- **Split embedding problems always have a plain lift.**  If `E.π` admits a section `σ` (i.e.
`E.G ≅ ker π ⋊ Gal(E.L/ℚ)`), then for every closure model the composite
`σ ∘ M.autCongr.symm ∘ restrictHom M.L` is a lift of `E.π` along the restriction map.  This is
the concrete form of "the extension class of `E` vanishes, hence so does its pullback, hence the
fibre product splits".

The lift is *not* surjective when `ker E.π` is non-trivial (its image is isomorphic to
`Gal(M.L/ℚ)`), so this does not solve `E`: a vanishing obstruction class gives a plain lift, not
necessarily a surjective one. -/
theorem exists_lift_of_split (M : E.ClosureModel) (σ : (E.L ≃ₐ[ℚ] E.L) →* E.G)
    (hσ : E.π.comp σ = MonoidHom.id _) :
    ∃ ψ : Field.absoluteGaloisGroup ℚ →* E.G,
      M.pi.comp ψ = Work.AbsoluteGalois.restrictHom M.L :=
  ⟨σ.comp (M.autCongr.symm.toMonoidHom.comp (Work.AbsoluteGalois.restrictHom M.L)),
    MonoidHom.ext fun x => by
      have h := congrFun (congrArg DFunLike.coe hσ) (M.autCongr.symm (Work.AbsoluteGalois.restrictHom M.L x))
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply] at h ⊢
      rw [M.pi_apply, h, MulEquiv.apply_symm_apply]⟩

end ClosureModel

end EmbeddingProblem

end Submission

namespace Work.AbsoluteGalois

open scoped Classical

noncomputable section

/-- The pullback of a `2`-cochain `c` on `Q` along a group homomorphism `ρ : H →* Q`.  This is
the cochain-level version of the pullback map `ρ^* : H²(Q, A) → H²(H, A)` appearing in the
obstruction calculus; see `Submission/Work/GroupCohomology/` for `Z²`, `B²` and `H²`. -/
def pullbackCocycle {Q H A : Type*} [Group Q] [Group H] (ρ : H →* Q) (c : Q × Q → A) :
    H × H → A := fun p => c (ρ p.1, ρ p.2)

@[simp]
lemma pullbackCocycle_apply {Q H A : Type*} [Group Q] [Group H] (ρ : H →* Q) (c : Q × Q → A)
    (p : H × H) : pullbackCocycle ρ c p = c (ρ p.1, ρ p.2) := rfl

end

end Work.AbsoluteGalois
