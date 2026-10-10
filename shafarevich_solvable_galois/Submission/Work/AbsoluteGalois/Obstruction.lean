import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Algebra.CharP.IntermediateField
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
