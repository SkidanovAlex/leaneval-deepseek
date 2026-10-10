import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Submission.Work.Tate.DimensionShift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w

namespace Work.Tate

open scoped BigOperators

section TwistedNorm

variable (G : Type u) (A : Type v) [Group G] [AddCommGroup A] [DistribMulAction G A]
  [Fintype G]

/-- The **twisted norm** `φ f = ∑_{x : G} x⁻¹ • f x` on the coinduced module `G → A`.  It is
`G`-equivariant for the coinduced action on `G → A` and the given action on `A`. -/
noncomputable def coindAug : (G → A) →+ A where
  toFun f := ∑ x : G, x⁻¹ • f x
  map_zero' := by simp
  map_add' f f' := by
    simp only [Pi.add_apply, smul_add]
    exact sum_add_distrib_univ (fun x => x⁻¹ • f x) (fun x => x⁻¹ • f' x)

@[simp] theorem coindAug_apply (f : G → A) : coindAug G A f = ∑ x : G, x⁻¹ • f x := rfl

end TwistedNorm

section Equiv

variable {G : Type u} {A : Type v} [Group G] [AddCommGroup A] [DistribMulAction G A]
  [Fintype G]

/-- The twisted norm is `G`-equivariant. -/
theorem coindAug_equiv (γ : G) (f : G → A) :
    coindAug G A (γ • f) = γ • coindAug G A f := by
  rw [coindAug_apply, coindAug_apply]
  rw [show (∑ x : G, x⁻¹ • (γ • f) x) = ∑ y : G, (γ * y⁻¹) • f y from
    Fintype.sum_equiv (Equiv.mulRight γ) (fun x => x⁻¹ • (γ • f) x)
      (fun y => (γ * y⁻¹) • f y) (fun x => by
        rw [coind_smul_eq]
        show x⁻¹ • f (x * γ) = (γ * (x * γ)⁻¹) • f (x * γ)
        have h : γ * (x * γ)⁻¹ = x⁻¹ := by
          rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
        rw [h])]
  rw [smul_sum_univ]
  exact Finset.sum_congr rfl (fun x _ => by rw [mul_smul])

/-- The twisted norm is surjective. -/
theorem coindAug_surjective : Function.Surjective (coindAug G A) := by
  classical
  intro a
  refine ⟨fun x => if x = 1 then a else 0, ?_⟩
  rw [coindAug_apply]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ 1) h

/-- The **`I_G`-twist** `A^♯ ≅ A ⊗ I_G` of a `G`-module, realized as the kernel of the twisted
norm `Coind(A) → A`. -/
noncomputable def coindUp (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : AddSubgroup (G → A) := (coindAug G A).ker

theorem mem_coindUp_iff {f : G → A} :
    f ∈ coindUp G A ↔ (∑ x : G, x⁻¹ • f x) = 0 :=
  AddMonoidHom.mem_ker

/-- The `G`-action on `A^♯ = ker φ`, which is a submodule because `φ` is equivariant. -/
noncomputable instance instSMulCoindUp : SMul G (coindUp G A) where
  smul γ x := ⟨γ • (x : G → A), by
    change coindAug G A (γ • (x : G → A)) = 0
    rw [coindAug_equiv, AddMonoidHom.mem_ker.mp x.2, smul_zero]⟩

@[simp] theorem coe_smul_coindUp (γ : G) (x : coindUp G A) :
    ((γ • x : coindUp G A) : G → A) = γ • (x : G → A) := rfl

noncomputable instance instDistribMulActionCoindUp : DistribMulAction G (coindUp G A) where
  one_smul x := Subtype.ext (coind_one_smul (x : G → A))
  mul_smul γ δ x := Subtype.ext (coind_mul_smul γ δ (x : G → A))
  smul_zero γ := Subtype.ext (coind_smul_zero γ)
  smul_add γ x y := Subtype.ext (coind_smul_add γ (x : G → A) (y : G → A))

/-- The short exact sequence `0 → A^♯ → Coind(A) → A → 0`. -/
noncomputable def coindUpSES (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : SES G (coindUp G A) (G → A) A where
  f := (coindUp G A).subtype
  g := coindAug G A
  f_equiv := fun γ x => rfl
  g_equiv := fun γ f => coindAug_equiv γ f
  f_injective := Subtype.coe_injective
  g_surjective := coindAug_surjective
  range_f_eq_ker_g := AddSubgroup.range_subtype _

/-- **Dimension shifting upwards**: `Ĥ⁻¹(G, A) ≃+ Ĥ⁰(G, A^♯)`, where `A^♯ ≅ A ⊗ I_G`. -/
noncomputable def dimensionShiftCoindUp (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : Hm1 G A ≃+ H0 G (coindUp G A) :=
  (coindUpSES G A).dimensionShift (coind_H0_subsingleton (G := G) (R := A))
    (coind_Hm1_subsingleton (G := G) (R := A))

@[simp] theorem dimensionShiftCoindUp_apply (G : Type u) (A : Type v) [Group G]
    [AddCommGroup A] [DistribMulAction G A] [Fintype G] (c : Hm1 G A) :
    dimensionShiftCoindUp G A c = (coindUpSES G A).delta c := rfl


section Functoriality

variable {G : Type u} {A : Type v} {B : Type w} [Group G] [AddCommGroup A] [AddCommGroup B]
  [DistribMulAction G A] [DistribMulAction G B] [Fintype G]

/-- Postcomposition with an additive map on the coinduced modules. -/
def coindMap (f : A →+ B) : (G → A) →+ (G → B) where
  toFun h := fun x => f (h x)
  map_zero' := by funext x; simp
  map_add' h h' := by funext x; simp [map_add]

@[simp] theorem coindMap_apply (f : A →+ B) (h : G → A) (x : G) : coindMap f h x = f (h x) :=
  rfl

/-- For equivariant `f` the induced map on coinduced modules is equivariant. -/
theorem coindMap_equiv (f : A →+ B) (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a) (γ : G)
    (h : G → A) : coindMap f (γ • h) = γ • coindMap f h := by
  funext x
  show f ((γ • h) x) = (γ • coindMap f h) x
  rw [coind_smul_eq, coind_smul_eq]
  rfl

/-- The twisted norm is natural in the coefficients. -/
theorem coindAug_natural (f : A →+ B) (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a)
    (h : G → A) : coindAug G B (coindMap f h) = f (coindAug G A h) := by
  rw [coindAug_apply, coindAug_apply, map_sum_univ f (fun x => x⁻¹ • h x)]
  exact Finset.sum_congr rfl (fun x _ => (hf x⁻¹ (h x)).symm)

/-- The induced map between the `I_G`-twists `A^♯ → B^♯`. -/
noncomputable def coindUpMap (f : A →+ B) (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a) :
    coindUp G A →+ coindUp G B where
  toFun x := ⟨coindMap f (x : G → A), by
    change coindAug G B (coindMap f (x : G → A)) = 0
    rw [coindAug_natural f hf, AddMonoidHom.mem_ker.mp x.2, map_zero]⟩
  map_zero' := Subtype.ext (by funext x; simp [coindMap_apply])
  map_add' x y := Subtype.ext (by funext x; simp [coindMap_apply, map_add])

@[simp] theorem coindUpMap_apply (f : A →+ B)
    (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a) (x : coindUp G A) (γ : G) :
    ((coindUpMap f hf x : coindUp G B) : G → B) γ = f ((x : G → A) γ) := rfl

/-- The induced map on the twists is equivariant. -/
theorem coindUpMap_equiv (f : A →+ B) (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a)
    (γ : G) (x : coindUp G A) : coindUpMap f hf (γ • x) = γ • coindUpMap f hf x := by
  refine Subtype.ext ?_
  change coindMap f (γ • (x : G → A)) = γ • coindMap f (x : G → A)
  exact coindMap_equiv f hf γ (x : G → A)

end Functoriality

section Hm2

variable {G : Type u} {A : Type v} {B : Type w} [Group G] [AddCommGroup A] [AddCommGroup B]
  [DistribMulAction G A] [DistribMulAction G B] [Fintype G]

/-- **The (−2)-nd Tate group** `Ĥ⁻²(G, A)`, in the paper's convention `A_{-2} = I_G`.

It is *defined* here as `Ĥ⁻¹(G, A^♯)` where `A^♯ ≅ A ⊗ I_G` is the `I_G`-twist of `A`
(`Work.Tate.coindUp`).  The justification is the upward dimension shift
`Ĥⁿ(G,A) ≅ Ĥⁿ⁺¹(G, A ⊗ I_G)`, whose `n = -1` instance is
`Work.Tate.dimensionShiftCoindUp`; applying it with `n = -2` is the statement
`Ĥ⁻²(G,A) ≅ Ĥ⁻¹(G, A ⊗ I_G)`.  The classical identification of `Ĥ⁻²` with the homology group
`H₁(G,A)` is not available in this workspace (there is no homology theory), so this *model* —
which is the `A_{-2} = I_G` twist of the paper — is what is used here.  It is functorial in `A`
(`Hm2Map`), which is what the shrinking argument needs. -/
noncomputable abbrev Hm2 (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] := Hm1 G (coindUp G A)

/-- **The upward dimension shift in degree `−2`**, in the model of `Ĥ⁻²` used here:
`Ĥ⁻²(G, A) ≅ Ĥ⁻¹(G, A^♯)` with `A^♯ ≅ A ⊗ I_G`. -/
noncomputable def dimensionShiftHm2 (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] : Hm2 G A ≃+ Hm1 G (coindUp G A) :=
  AddEquiv.refl _

/-- Functoriality of `Ĥ⁻²` in `G`-equivariant maps of coefficients, transported from `Ĥ⁻¹` of
the `I_G`-twists. -/
noncomputable def Hm2Map (f : A →+ B) (hf : ∀ (γ : G) (a : A), f (γ • a) = γ • f a) :
    Hm2 G A →+ Hm2 G B :=
  Hm1Map G (coindUp G A) (coindUp G B) (coindUpMap f hf) (coindUpMap_equiv f hf)

end Hm2

end Equiv

end Work.Tate
