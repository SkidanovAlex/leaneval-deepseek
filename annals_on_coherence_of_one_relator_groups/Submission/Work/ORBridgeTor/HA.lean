/-
# N9's `hA` from the torsion-freeness of Lemma 5.1′ (mismatch (M2))

Node N9 (`Work.ORFlatness.tor1Vanishes_diagonal_jl_right`) consumes the hypothesis

`hA` : for every left `K[G]`-module `M`, the map `(S ⊗[K] M) ⊗_{K[G]} A → (S ⊗[K] M) ⊗_{K[G]} B`
induced by `f : A →ₗ[K[G]] B` is injective, where `S ⊗[K] M` carries the **right** diagonal
`K[G]`-module structure `Work.ORFlatness.diagRightModule`.  In Jaikin-Zapirain--Linton this is the
injectivity of the connecting map `γ̃` of the presentation sequence (their Claim 5.10); its
content is that **the second component of `f` is right multiplication by an element `β` with
`supp β` injective in `G ⧸ N`**, so that `β` acts injectively on `S ⊗[K] M` by Lemma 5.1′ — the
right-module form delivered by `Work.ORBridgeTor.torsionFree_diagRight_of_diagLeft`
(`Submission/Work/ORBridgeTor/Mirror.lean`).

This file proves that bridge: `Work.ORBridgeTor.hA_of_torsion`.

* `Work.ORBridgeTor.balTensor_mk_eq_zero_iff` — `Work.ORFlatness.BalTensor.mk R x a = 0 ↔ (op a) • x = 0`
  (the balanced tensor `X ⊗[R] R` is the regular module `X`).
* `Work.ORBridgeTor.hA_of_torsion` — N9's `hA` from the right-module torsion statement.
-/
import Submission.Work.ORBridgeTor.Defs
import Submission.Work.ORFlatness.leftFlat_iff_isFlatLeft
import Submission.Work.ORHomAlg.TensorIsos.tensorSelfLeft

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open TensorProduct MulOpposite

universe u

namespace Work.ORBridgeTor

/-! ## `Work.ORFlatness.BalTensor.mk x a = 0 ↔ (op a) • x = 0` -/

theorem balTensor_mk_eq_zero_iff (R : Type u) [Ring R] (X : Type u) [AddCommGroup X]
    [Module Rᵐᵒᵖ X] (x : X) (a : R) :
    Work.ORFlatness.BalTensor.mk R x a = 0 ↔ (op a) • x = 0 := by
  constructor
  · intro h
    have h2 : Work.ORHomAlg.BalancedTensor.tmul R x a = 0 := by
      rw [← Work.ORFlatness.baltensorEquiv_mk R X R x a, h, map_zero]
    have h4 : Work.ORHomAlg.BalancedTensor.selfLeftEquiv
        (Work.ORHomAlg.BalancedTensor.tmul R x a) = 0 := by
      rw [h2, map_zero]
    rwa [Work.ORHomAlg.BalancedTensor.selfLeftEquiv_tmul] at h4
  · intro h
    rw [show a = a • (1 : R) from (mul_one a).symm,
      ← Work.ORFlatness.BalTensor.mk_smul_right R x (1 : R) a, h]
    rw [Work.ORFlatness.BalTensor.mk_zero_left]

/-! ## N9's `hA` -/

section HA

variable (K : Type u) [CommRing K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)

/-- **N9's `hA` from Lemma 5.1′ in the right-module form** (mismatch (M2)).

Let `f : A →ₗ[K[G]] B` be the first map of the presentation sequence of JL Claim 5.10, let
`ae ∈ A` generate `A` as a `K[G]`-module, and let `π : B →ₗ[K[G]] K[G]` be the projection onto
the `K[G]`-summand, with `π (f ae) = β`.  If the right diagonal action of `β` on `S ⊗[K] M` is
injective for every left `K[G]`-module `M` (Lemma 5.1′ in the right-module form, delivered for
`S = D(G)` from node N8 by `Work.ORBridgeTor.torsionFree_diagRight_of_diagLeft`), then N9's
`hA` holds:

`Work.ORFlatness.BalTensor.map K[G] (id) f : (S ⊗[K] M) ⊗_{K[G]} A → (S ⊗[K] M) ⊗_{K[G]} B` is injective.

The proof: an element of `(S ⊗[K] M) ⊗_{K[G]} A` is `x ⊗ ae` (`A` is cyclic), and
`(id ⊗ f)(x ⊗ ae) = x ⊗ f(ae)`; applying `id ⊗ π` gives `x ⊗ β = 0`, i.e. `(op β) • x = 0`,
which forces `x = 0` by the torsion statement. -/
theorem hA_of_torsion
    {A : Type u} [AddCommGroup A] [Module (MonoidAlgebra K G) A]
    {B : Type u} [AddCommGroup B] [Module (MonoidAlgebra K G) B]
    (f : A →ₗ[MonoidAlgebra K G] B) (ae : A)
    (hgen : ∀ a : A, ∃ r : MonoidAlgebra K G, a = r • ae)
    (π : B →ₗ[MonoidAlgebra K G] (MonoidAlgebra K G)) (β : MonoidAlgebra K G)
    (hπf : π (f ae) = β)
    (hβ : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      Function.Injective (fun x : S ⊗[K] M => (op β) • x)) :
    ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      Function.Injective (Work.ORFlatness.BalTensor.map (MonoidAlgebra K G)
        (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] (S ⊗[K] M)) f) := by
  intro M _ _ _ _ _
  letI := Work.ORFlatness.diagRightModule K G S φ M
  have key : ∀ z : Work.ORFlatness.BalTensor (MonoidAlgebra K G) (S ⊗[K] M) A,
      Work.ORFlatness.BalTensor.map (MonoidAlgebra K G)
        (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] (S ⊗[K] M)) f z = 0 → z = 0 := by
    intro z hz
    -- every element of the balanced tensor is `x ⊗ ae`
    have hmem : ∀ (x : S ⊗[K] M) (a : A),
        Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) x a ∈
          (Work.ORFlatness.BalTensor.mkLeft (MonoidAlgebra K G) ae).range := by
      intro x a
      obtain ⟨r, rfl⟩ := hgen a
      refine ⟨op r • x, ?_⟩
      show Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) (op r • x) ae
        = Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) x (r • ae)
      rw [Work.ORFlatness.BalTensor.mk_smul_right]
    have hzrange : z ∈ (Work.ORFlatness.BalTensor.mkLeft (MonoidAlgebra K G) ae).range :=
      (AddSubgroup.closure_le _).mpr (by
        rintro y ⟨⟨x, a⟩, rfl⟩
        exact hmem x a)
        (Work.ORFlatness.BalTensor.mem_closure_mk (R := MonoidAlgebra K G) z)
    obtain ⟨x, hx⟩ := hzrange
    -- `hx : mkLeft ae x = z`, i.e. `mk x ae = z`
    have hx' : Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) x ae = z := hx
    -- applying `id ⊗ f` and then `id ⊗ π`
    have h1 : Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) x (f ae) = 0 := by
      rw [← hx'] at hz
      rw [Work.ORFlatness.BalTensor.map_mk] at hz
      simpa using hz
    have h2 : Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) x β = 0 := by
      have h3 : Work.ORFlatness.BalTensor.map (MonoidAlgebra K G)
          (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] (S ⊗[K] M)) π
          (Work.ORFlatness.BalTensor.mk (MonoidAlgebra K G) x (f ae)) = 0 := by
        rw [h1, map_zero]
      rw [Work.ORFlatness.BalTensor.map_mk, LinearMap.id_coe, id_eq, hπf] at h3
      exact h3
    have h4 : (op β) • x = 0 :=
      (balTensor_mk_eq_zero_iff (MonoidAlgebra K G) (S ⊗[K] M) x β).mp h2
    have h5 : x = 0 := hβ M (by simpa using h4)
    rw [← hx', h5]
    exact Work.ORFlatness.BalTensor.mk_zero_left (R := MonoidAlgebra K G) ae
  intro z z' hzz
  have h2 : Work.ORFlatness.BalTensor.map (MonoidAlgebra K G)
      (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] (S ⊗[K] M)) f (z - z') = 0 := by
    rw [map_sub, hzz, sub_self]
  exact sub_eq_zero.mp (key (z - z') h2)

/-- **N9's `hA` from the right-module torsion statement, for the presentation sequence with
`A = K[G]`** (the free-group case of JL §5.2 and the Magnus form of Claim 5.10): here `ae = 1`
generates `A`. -/
theorem hA_of_torsion_regular
    {B : Type u} [AddCommGroup B] [Module (MonoidAlgebra K G) B]
    (f : MonoidAlgebra K G →ₗ[MonoidAlgebra K G] B)
    (π : B →ₗ[MonoidAlgebra K G] (MonoidAlgebra K G)) (β : MonoidAlgebra K G)
    (hπf : π (f 1) = β)
    (hβ : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      Function.Injective (fun x : S ⊗[K] M => (op β) • x)) :
    ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      Function.Injective (Work.ORFlatness.BalTensor.map (MonoidAlgebra K G)
        (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] (S ⊗[K] M)) f) :=
  hA_of_torsion K G S φ f 1 (fun a => ⟨a, by rw [smul_eq_mul, mul_one]⟩) π β hπf hβ

end HA

end Work.ORBridgeTor
