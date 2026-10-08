import Mathlib
import Submission.Work.Clifford.ResSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.conjSub_isotypicComponent`

For a normal subgroup `N ⊴ G`, a `G`-representation `V`, and `g : G`, conjugation by `g`
(`Work.Clifford.conjSub`) is an order isomorphism of the lattice of `ℂ[N]`-submodules of
`ResMod N V`.  This file shows that it maps the `S`-isotypic component to the
`conjSub V g S`-isotypic component.

## Main result

* `Work.Clifford.conjSub_isotypicComponent` —
  `conjSub V g (isotypicComponent ℂ[N] (ResMod N V) S) = isotypicComponent ℂ[N] (ResMod N V) (conjSub V g S)`.

## Outline

The group element `g` acts on `ResMod N V` by the `ℂ`-linear bijection `resAct N V g`.  It is not
`ℂ[N]`-linear, but it *intertwines* the `ℂ[N]`-action with its twist by the algebra automorphism
`conjAlg g` (`conjAlg_smul_resAct`).  Consequently `conjSub V g` sends `ℂ[N]`-submodules
isomorphic to `S` to `ℂ[N]`-submodules isomorphic to `conjSub V g S`
(`conjSubLinearEquiv`).  Since `conjSub V g` also commutes with `sSup` (`conjSub_sSup`), and
`isotypicComponent R M S` is by definition the `sSup` of the submodules isomorphic to `S`, the
result follows.
-/

noncomputable section

open Classical
open scoped MonoidAlgebra

namespace Work.Clifford

variable {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]

/-! ### Two inverse maps between `W` and `conjSub V g W` -/

/-- Regard an element of `conjSub V g W` as an element of `W` by applying `resAct g⁻¹`. -/
def conjSubToSub (V : FDRep ℂ G) (g : G)
    (W : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) (y : conjSub V g W) : W :=
  ⟨resAct N V g⁻¹ (y : ResMod N V), by
    obtain ⟨w, hw, hw'⟩ := (mem_conjSub V g W (y : ResMod N V)).mp y.2
    rw [← hw', resAct_mul, inv_mul_cancel, resAct_one]
    exact hw⟩

/-- Send `x ∈ W` to `resAct g x ∈ conjSub V g W`. -/
def subToConjSub (V : FDRep ℂ G) (g : G)
    (W : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) (x : W) : conjSub V g W :=
  ⟨resAct N V g (x : ResMod N V), conjSub_apply_mem V g W x.2⟩

@[simp] theorem conjSubToSub_apply (V : FDRep ℂ G) (g : G)
    (W : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) (y : conjSub V g W) :
    ((conjSubToSub V g W y : W) : ResMod N V) = resAct N V g⁻¹ (y : ResMod N V) := rfl

@[simp] theorem subToConjSub_apply (V : FDRep ℂ G) (g : G)
    (W : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) (x : W) :
    ((subToConjSub V g W x : conjSub V g W) : ResMod N V) = resAct N V g (x : ResMod N V) := rfl

@[simp] theorem subToConjSub_conjSubToSub (V : FDRep ℂ G) (g : G)
    (W : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) (y : conjSub V g W) :
    subToConjSub V g W (conjSubToSub V g W y) = y := by
  apply Subtype.ext
  rw [subToConjSub_apply, conjSubToSub_apply, resAct_mul, mul_inv_cancel, resAct_one]

@[simp] theorem conjSubToSub_subToConjSub (V : FDRep ℂ G) (g : G)
    (W : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) (x : W) :
    conjSubToSub V g W (subToConjSub V g W x) = x := by
  apply Subtype.ext
  rw [conjSubToSub_apply, subToConjSub_apply, resAct_mul, inv_mul_cancel, resAct_one]

/-! ### The `g`-conjugation of an isomorphism `W ≃ S` -/

theorem conjSubToSub_add (V : FDRep ℂ G) (g : G)
    (W : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) (y₁ y₂ : conjSub V g W) :
    conjSubToSub V g W (y₁ + y₂) = conjSubToSub V g W y₁ + conjSubToSub V g W y₂ := by
  apply Subtype.ext
  simp only [conjSubToSub_apply, Submodule.coe_add, map_add]

/-- `conjSubToSub` intertwines the `ℂ[N]`-action on `conjSub V g W` with its twist by `conjAlg g`. -/
theorem conjSubToSub_smul (V : FDRep ℂ G) (g : G)
    (W : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) (c : MonoidAlgebra ℂ ↥N)
    (y : conjSub V g W) :
    conjSubToSub V g W (c • y) = conjAlg g c • conjSubToSub V g W y := by
  apply Subtype.ext
  simp only [conjSubToSub_apply, Submodule.coe_smul]
  have hy : resAct N V g (resAct N V g⁻¹ (y : ResMod N V)) = (y : ResMod N V) := by
    rw [resAct_mul, mul_inv_cancel, resAct_one]
  conv_lhs => rw [← hy, conjAlg_smul_resAct, resAct_mul, inv_mul_cancel, resAct_one]

/-- Conjugation by `g` sends an isomorphism `m ≃ₗ[ℂ[N]] S` to an isomorphism
`conjSub V g m ≃ₗ[ℂ[N]] conjSub V g S`. -/
noncomputable def conjSubLinearEquiv (V : FDRep ℂ G) (g : G)
    (m S : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V))
    (φ : m ≃ₗ[MonoidAlgebra ℂ ↥N] ↥S) :
    conjSub V g m ≃ₗ[MonoidAlgebra ℂ ↥N] ↥(conjSub V g S) where
  toFun y := subToConjSub V g S (φ (conjSubToSub V g m y))
  invFun z := subToConjSub V g m (φ.symm (conjSubToSub V g S z))
  left_inv y := by
    simp only [subToConjSub_conjSubToSub, LinearEquiv.symm_apply_apply, conjSubToSub_subToConjSub]
  right_inv z := by
    simp only [conjSubToSub_subToConjSub, LinearEquiv.apply_symm_apply, subToConjSub_conjSubToSub]
  map_add' y₁ y₂ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, subToConjSub_apply, conjSubToSub_add, map_add]
  map_smul' c y := by
    apply Subtype.ext
    rw [conjSubToSub_smul, map_smul]
    simp only [subToConjSub_apply, Submodule.coe_smul]
    rw [← conjAlg_smul_resAct]
    rfl

/-! ### Commutation with `sSup` -/

/-- Conjugation by `g` is an order isomorphism of the lattice of `ℂ[N]`-submodules, hence
commutes with arbitrary suprema. -/
theorem conjSub_sSup (V : FDRep ℂ G) (g : G)
    (T : Set (Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V))) :
    conjSub V g (sSup T) = sSup (conjSub V g '' T) := by
  apply le_antisymm
  · have h : sSup T ≤ conjSub V g⁻¹ (sSup (conjSub V g '' T)) := by
      apply sSup_le
      intro m hm
      have h1 : conjSub V g m ≤ sSup (conjSub V g '' T) := le_sSup ⟨m, hm, rfl⟩
      have h2 := conjSub_mono V g⁻¹ h1
      rwa [conjSub_inv_left] at h2
    have h3 := conjSub_mono V g h
    rwa [conjSub_inv_right] at h3
  · apply sSup_le
    rintro n ⟨m, hm, hmn⟩
    rw [← hmn]
    exact conjSub_mono V g (le_sSup hm)

/-! ### The main result -/

theorem conjSub_isotypicComponent {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    (V : FDRep ℂ G) (g : G) (S : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) :
    conjSub V g (isotypicComponent (MonoidAlgebra ℂ ↥N) (ResMod N V) ↥S) =
      isotypicComponent (MonoidAlgebra ℂ ↥N) (ResMod N V) ↥(conjSub V g S) := by
  have hset : conjSub V g '' {m : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V) |
        Nonempty (m ≃ₗ[MonoidAlgebra ℂ ↥N] ↥S)} =
      {n : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V) |
        Nonempty (n ≃ₗ[MonoidAlgebra ℂ ↥N] ↥(conjSub V g S))} := by
    ext n
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, ⟨φ⟩, hm⟩
      rw [← hm]
      exact ⟨conjSubLinearEquiv V g m S φ⟩
    · rintro ⟨ψ⟩
      refine ⟨conjSub V g⁻¹ n, ?_, ?_⟩
      · have h2 : Nonempty (conjSub V g⁻¹ n ≃ₗ[MonoidAlgebra ℂ ↥N]
            ↥(conjSub V g⁻¹ (conjSub V g S))) :=
          ⟨conjSubLinearEquiv V g⁻¹ n (conjSub V g S) ψ⟩
        rw [show conjSub V g⁻¹ (conjSub V g S) = S from conjSub_inv_left V g S] at h2
        exact h2
      · rw [conjSub_inv_right]
  unfold isotypicComponent
  rw [conjSub_sSup, hset]

end Work.Clifford
