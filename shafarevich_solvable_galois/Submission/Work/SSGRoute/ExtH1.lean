import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.Work.SSGRoute.ExtH1Defs

/-!
# The derivation bridge `Hom(I, M) ≅` crossed homomorphisms

Continues `Submission.Work.SSGRoute.ExtH1Defs`.  For a group `G` and `Coeff = ULift ℤ` we prove,
writing `I ⊆ k[G]` for the augmentation ideal and `augDiff γ = γ - 1 ∈ I`:

* `augHom_eq_sum_coeff`: the augmentation of `Σ c_γ γ` is `Σ c_γ` (the sum of coefficients);
* `sum_coeff_smul_ebas`: `Σ c_γ • γ = x` (the coefficient decomposition);
* `eq_sum_smul_diff`, `sum_coeff_smul_augDiff`, `span_augDiff_eq_top`: `x = Σ c_γ • (γ - 1)`
  for `x ∈ I` (the augmentation ideal is spanned by the `γ - 1`);
* `hom_ext_augDiff`: a morphism `I ⟶ M` is determined by its values on the `γ - 1`;
* `cocycleLin_apply`, `cocycleLin_ebas`, `cocycleLin_diff`: the computation rules for the
  derivation map `Σ c_γ γ ↦ Σ c_γ • φ γ`.
-/

open CategoryTheory
open SSGRoute.PTExt

namespace Work.SSGRoute
namespace ExtH1

variable (G : Type) [Group G]

/-- The augmentation of `Σ c_γ γ` is the sum of the coefficients. -/
theorem augHom_eq_sum_coeff (x : regRep G) :
    (augHom G).hom x = (MonoidAlgebra.coeff x).sum (fun _ c => c) := by
  change (Finsupp.lift Coeff Coeff G (fun g => (unitRep G).ρ g 1))
      ((MonoidAlgebra.coeffLinearEquiv Coeff (S := Coeff) (M := G)) x) =
    (MonoidAlgebra.coeff x).sum (fun _ c => c)
  rw [MonoidAlgebra.coeffLinearEquiv_apply, Finsupp.lift_apply]
  refine Finsupp.sum_congr (fun g _ => ?_)
  rw [show (unitRep G).ρ g (1 : Coeff) = 1 from rfl, smul_eq_mul, mul_one]

/-- The coefficient decomposition `Σ_γ c_γ • γ = x`. -/
theorem sum_coeff_smul_ebas (x : regRep G) :
    (MonoidAlgebra.coeff x).sum (fun γ c => c • ebas G γ) = x := by
  have h : (MonoidAlgebra.coeff x).sum (fun γ c => c • ebas G γ)
      = (MonoidAlgebra.coeff x).sum (fun γ c => MonoidAlgebra.single γ c) := by
    refine Finsupp.sum_congr (fun γ _ => ?_)
    rw [show ebas G γ = MonoidAlgebra.single γ (1 : Coeff) from rfl,
      MonoidAlgebra.smul_single', mul_one]
  rw [h, MonoidAlgebra.sum_coeff_single]

/-- **The augmentation ideal is spanned by the `γ - 1`.**  For `x ∈ I` with coefficients `c_γ`,
`x = Σ_γ c_γ • (γ - 1)`. -/
theorem eq_sum_smul_diff (x : ↥(augSub G)) :
    (x : regRep G) = (MonoidAlgebra.coeff (x : regRep G)).sum
      (fun γ c => c • (ebas G γ - ebas G 1)) := by
  have hsum : (MonoidAlgebra.coeff (x : regRep G)).sum (fun _ c => c) = 0 := by
    rw [← augHom_eq_sum_coeff G (x : regRep G)]
    exact LinearMap.mem_ker.mp x.2
  rw [Finsupp.sum_congr (f := MonoidAlgebra.coeff (x : regRep G))
    (g1 := fun γ c => c • (ebas G γ - ebas G 1))
    (g2 := fun γ c => c • ebas G γ - c • ebas G 1) (fun γ _ => smul_sub _ _ _)]
  rw [Finsupp.sum_sub]
  rw [sum_coeff_smul_ebas G (x : regRep G)]
  have hconst : (MonoidAlgebra.coeff (x : regRep G)).sum (fun γ c => c • ebas G 1)
      = ((MonoidAlgebra.coeff (x : regRep G)).sum (fun _ c => c)) • ebas G 1 := by
    rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
  rw [hconst, hsum, zero_smul, sub_zero]

/-- The spanning statement inside `I` itself. -/
theorem sum_coeff_smul_augDiff (x : augI G) :
    (MonoidAlgebra.coeff (x : regRep G)).sum (fun γ c => c • augDiff G γ) = x := by
  apply Subtype.ext
  rw [Finsupp.sum, Submodule.coe_sum]
  trans ∑ i ∈ (MonoidAlgebra.coeff (x : regRep G)).support,
    (MonoidAlgebra.coeff (x : regRep G)) i • (ebas G i - ebas G 1)
  · refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Submodule.coe_smul]
    rfl
  · exact (eq_sum_smul_diff G ⟨(x : regRep G), x.2⟩).symm

/-- **The augmentation ideal is spanned by the elements `γ - 1`.** -/
theorem span_augDiff_eq_top :
    Submodule.span Coeff (Set.range (augDiff G)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  rw [← sum_coeff_smul_augDiff G x, Finsupp.sum]
  refine Submodule.sum_mem _ (fun γ _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, rfl⟩)

/-- **The derivation bridge (uniqueness part).**  A morphism `I ⟶ M` is determined by its values
on the elements `γ - 1`. -/
theorem hom_ext_augDiff (M : Type) [AddCommGroup M] [DistribMulAction G M]
    [SMulCommClass G Coeff M] (f g : augI G ⟶ modRep G M)
    (h : ∀ γ, f.hom (augDiff G γ) = g.hom (augDiff G γ)) : f = g := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change f.hom.toLinearMap x = g.hom.toLinearMap x
  rw [← sum_coeff_smul_augDiff G x, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [map_smul, map_smul, Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.toLinearMap_apply, h γ]

section Minimal

variable {M : Type} [AddCommGroup M]

/-- `cocycleLin φ` on a basis element: `cocycleLin φ γ = φ γ`. -/
theorem cocycleLin_ebas (φ : G → M) (γ : G) :
    cocycleLin G M φ (ebas G γ) = φ γ := by
  rw [cocycleLin, LinearMap.comp_apply, LinearEquiv.coe_coe,
    MonoidAlgebra.coeffLinearEquiv_apply]
  rw [show (ebas G γ).coeff = Finsupp.single γ 1 from rfl]
  rw [Finsupp.linearCombination_single]
  exact @one_smul Coeff M _ ((inferInstance : Module Coeff M)).toMulAction (φ γ)

/-- `cocycleLin φ` on `γ - 1`. -/
theorem cocycleLin_diff (φ : G → M) (γ : G) :
    cocycleLin G M φ (ebas G γ - ebas G 1) = φ γ - φ 1 := by
  rw [map_sub, cocycleLin_ebas, cocycleLin_ebas]

end Minimal

section Action

variable {M : Type} [AddCommGroup M] [DistribMulAction G M]
  [SMulCommClass G Coeff M]

/-- The crossed-homomorphism (cocycle) condition for the action of `G` on `M`. -/
def IsCrossedHom (φ : G → M) : Prop := ∀ g h : G, φ (g * h) = φ g + g • φ h

/-- The value at `1` of a crossed homomorphism is `0`. -/
theorem crossedHom_one (φ : G → M) (hφ : IsCrossedHom (G := G) (M := M) φ) : φ 1 = 0 := by
  have h := hφ 1 1
  rw [mul_one] at h
  have h2 : (1 : G) • (φ 1) = φ 1 := MulAction.one_smul _
  rw [h2] at h
  exact (add_left_cancel (by rw [add_zero]; exact h)).symm


/-- The action of `G` on `k[G]` is left multiplication. -/
theorem regRep_ρ_ebas (d γ : G) : (regRep G).ρ d (ebas G γ) = ebas G (d * γ) := by
  show (Representation.ofMulAction Coeff G G d) (MonoidAlgebra.single γ (1 : Coeff)) =
    MonoidAlgebra.single (d * γ) (1 : Coeff)
  rw [Representation.ofMulAction_single]
  rw [smul_eq_mul]

/-- The action of `G` on the augmentation ideal, on `γ - 1`. -/
theorem regRep_ρ_augDiff (d γ : G) :
    (((augI G).ρ d (augDiff G γ) : augI G) : regRep G) = ebas G (d * γ) - ebas G d := by
  rw [show (((augI G).ρ d (augDiff G γ) : augI G) : regRep G)
      = (regRep G).ρ d (((augDiff G γ : augI G) : regRep G)) from rfl]
  rw [show ((augDiff G γ : augI G) : regRep G) = ebas G γ - ebas G 1 from rfl]
  rw [map_sub, regRep_ρ_ebas, regRep_ρ_ebas, mul_one]

/-- **Equivariance of the derivation map on the augmentation ideal.**  For a crossed homomorphism
`φ`, the map `Σ c_γ γ ↦ Σ c_γ • φ γ` is `G`-equivariant on `I`, hence restricts to a morphism of
representations `I ⟶ M`. -/
theorem cocycleLin_smul (φ : G → M) (hφ : IsCrossedHom (G := G) (M := M) φ) (d : G) (x : augI G) :
    cocycleLin G M φ (((augI G).ρ d x : augI G) : regRep G) =
      d • cocycleLin G M φ (x : regRep G) := by
  let A : augI G →ₗ[Coeff] M :=
    { toFun := fun y => cocycleLin G M φ (((augI G).ρ d y : augI G) : regRep G)
      map_add' := fun y z => by
        show cocycleLin G M φ (((augI G).ρ d (y + z) : augI G) : regRep G) = _ + _
        rw [map_add, Submodule.coe_add, map_add]
      map_smul' := fun c y => by
        show cocycleLin G M φ (((augI G).ρ d (c • y) : augI G) : regRep G) = c • _
        rw [map_smul, Submodule.coe_smul, map_smul] }
  let B : augI G →ₗ[Coeff] M :=
    { toFun := fun y => d • cocycleLin G M φ ((y : augI G) : regRep G)
      map_add' := fun y z => by
        show d • cocycleLin G M φ ((y + z : augI G) : regRep G) = _ + _
        rw [Submodule.coe_add, map_add, smul_add]
      map_smul' := fun c y => by
        rw [Submodule.coe_smul, LinearMap.map_smul]
        exact smul_comm d c _ }
  have hbase : ∀ γ : G, A (augDiff G γ) = B (augDiff G γ) := by
    intro γ
    simp only [A, B, LinearMap.coe_mk, AddHom.coe_mk]
    rw [regRep_ρ_augDiff, map_sub, cocycleLin_ebas, cocycleLin_ebas]
    rw [show ((augDiff G γ : augI G) : regRep G) = ebas G γ - ebas G 1 from rfl,
      map_sub, cocycleLin_ebas, cocycleLin_ebas,
      (crossedHom_one (G := G) (M := M) φ hφ)]
    simp only [sub_zero, smul_sub, smul_zero]
    rw [sub_eq_iff_eq_add]
    exact (hφ d γ).trans (add_comm _ _)
  have hAB : A = B := by
    have hle : Submodule.span Coeff (Set.range (augDiff G)) ≤ LinearMap.ker (A - B) := by
      rw [Submodule.span_le]
      rintro z ⟨γ, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, hbase γ, sub_self]
    have htop : LinearMap.ker (A - B) = ⊤ :=
      le_antisymm le_top (by rw [← span_augDiff_eq_top G]; exact hle)
    apply LinearMap.ext
    intro y
    have hy : y ∈ LinearMap.ker (A - B) := by rw [htop]; trivial
    rw [LinearMap.mem_ker, LinearMap.sub_apply] at hy
    exact sub_eq_zero.mp hy
  change A x = B x
  rw [hAB]


/-- The subtype map of the augmentation ideal is the coercion. -/
theorem subtypeAugSub_apply (x : augI G) :
    (Submodule.subtype (augSub G)) x = ((x : augI G) : regRep G) := rfl

/-- The morphism `I ⟶ M` viewed as a function `I → M`. -/
noncomputable def homApply (f : augI G ⟶ modRep G M) (y : augI G) : M := f.hom y

/-- The cocycle attached to a morphism `I ⟶ M`: its value on `γ - 1`. -/
noncomputable def derivCochain (f : augI G ⟶ modRep G M) : G → M :=
  fun γ => homApply (G := G) (M := M) f (augDiff G γ)

/-- The cocycle attached to a morphism `I ⟶ M` is a crossed homomorphism. -/
theorem derivCochain_isCrossedHom (f : augI G ⟶ modRep G M) :
    IsCrossedHom (G := G) (M := M) (derivCochain (G := G) (M := M) f) := by
  intro g h
  have hkey : augDiff G (g * h)
      = (augI G).ρ g (augDiff G h) + (augI G).ρ (1 : G) (augDiff G g) := by
    apply Subtype.ext
    show ebas G (g * h) - ebas G 1
      = (regRep G).ρ g (ebas G h - ebas G 1) + (regRep G).ρ (1 : G) (ebas G g - ebas G 1)
    rw [map_sub, map_sub, regRep_ρ_ebas, regRep_ρ_ebas, regRep_ρ_ebas, regRep_ρ_ebas,
      show ebas G (g * h) = ebas G g * ebas G h from by
        rw [show ebas G g = MonoidAlgebra.single g (1 : Coeff) from rfl,
          show ebas G h = MonoidAlgebra.single h (1 : Coeff) from rfl,
          MonoidAlgebra.single_mul_single, mul_one],
      show ebas G (g * 1) = ebas G g from by rw [mul_one],
      show ebas G (1 * g) = ebas G g from by rw [one_mul],
      show ebas G (1 * 1) = ebas G 1 from by rw [mul_one]]
    abel
  have hcomm : ∀ (σ : G) (y : augI G),
      homApply (G := G) (M := M) f ((augI G).ρ σ y)
        = σ • homApply (G := G) (M := M) f y := by
    intro σ y
    rw [homApply, homApply, Rep.hom_comm_apply]
    exact Rep.ofDistribMulAction_ρ_apply_apply (k := Coeff) (G := G) (A := M) σ (f.hom y)
  have hone : ∀ y : augI G, homApply (G := G) (M := M) f ((augI G).ρ (1 : G) y)
      = homApply (G := G) (M := M) f y := by
    intro y
    rw [hcomm, MulAction.one_smul]
  have hadd : ∀ a b : augI G, homApply (G := G) (M := M) f (a + b)
      = homApply (G := G) (M := M) f a + homApply (G := G) (M := M) f b := by
    intro a b
    rw [homApply, homApply, homApply, map_add]
    rfl
  have hgoal : homApply (G := G) (M := M) f (augDiff G (g * h))
      = homApply (G := G) (M := M) f (augDiff G g)
        + g • homApply (G := G) (M := M) f (augDiff G h) := by
    rw [hkey, hadd, hcomm g (augDiff G h), hone (augDiff G g)]
    abel
  exact hgoal

/-- **The derivation bridge (existence part).**  A crossed homomorphism `φ : G → M` defines a
morphism of representations `I ⟶ M`, `γ - 1 ↦ φ γ`. -/
noncomputable def cocycleHom (φ : G → M) (hφ : IsCrossedHom (G := G) (M := M) φ) :
    augI G ⟶ modRep G M :=
  Rep.ofHom
    { toLinearMap := (cocycleLin G M φ).comp (Submodule.subtype (augSub G))
      isIntertwining' := fun d => by
        apply LinearMap.ext
        intro x
        dsimp only [LinearMap.comp_apply]
        rw [subtypeAugSub_apply, cocycleLin_smul G φ hφ d x, subtypeAugSub_apply]
        exact (Rep.ofDistribMulAction_ρ_apply_apply Coeff G M d
          (cocycleLin G M φ ((Submodule.subtype (augSub G)) x))).symm }

/-- The defining property of the derivation bridge. -/
theorem cocycleHom_augDiff (φ : G → M) (hφ : IsCrossedHom (G := G) (M := M) φ) (γ : G) :
    (cocycleHom (G := G) (M := M) φ hφ).hom (augDiff G γ) = φ γ := by
  show cocycleLin G M φ ((Submodule.subtype (augSub G)) (augDiff G γ)) = φ γ
  rw [subtypeAugSub_apply,
    show ((augDiff G γ : augI G) : regRep G) = ebas G γ - ebas G 1 from rfl, cocycleLin_diff,
    (crossedHom_one (G := G) (M := M) φ hφ), sub_zero]

/-- **The derivation bridge is a bijection.**  Recovering the cocycle from a morphism `I ⟶ M`
inverts `cocycleHom`. -/
theorem cocycleHom_derivCochain (f : augI G ⟶ modRep G M) :
    cocycleHom (G := G) (M := M) (derivCochain (G := G) (M := M) f) (derivCochain_isCrossedHom (G := G) (M := M) f) = f := by
  apply hom_ext_augDiff G M
  intro γ
  rw [cocycleHom_augDiff]
  rfl

end Action

end ExtH1
end Work.SSGRoute
