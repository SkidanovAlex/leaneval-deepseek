/-
# `Work.ORBridgeTor`: the bridges (M2) and (M4) of the assembly of Theorem 1.1

This chapter closes the two interface mismatches (M2) and (M4) recorded in
`Submission/Work/ORAssembly/README.md` §3:

* **(M2)** N8's Lemma 5.1′ (`Work.ORTorsion.torsionFree_tensor`) is stated for the *left*
  diagonal action on `V ⊗[K] D(G)`; N9's `hA`
  (`Work.ORFlatness.tor1Vanishes_diagonal_jl_right`) needs the *right* diagonal action
  (`Work.ORFlatness.diagRightModule`) on `S ⊗[K] M`.  The transport is the antipode
  `ι = J ∘ *` of `U(G)`, `Σ a_g g ↦ Σ a_g g⁻¹`, a `K`-linear bijective anti-endomorphism of
  `U(G)` (abstracted here as `Work.ORBridgeTor.AntiAut`) satisfying `ι (gen g) = (gen g)⁻¹`.
  The transport is proved in `Submission/Work/ORBridgeTor/Mirror.lean`; its consequence in
  exactly the shape of N9's `hA` slot is `Work.ORBridgeTor.hA_of_torsion`
  (`Submission/Work/ORBridgeTor/HA.lean`).

* **(M4)** N1's JL Lemma 5.2(2) (`Work.ORHomAlg.JL52.jl_5_2_2`) is stated in the
  `BalancedTensor`/`DualMod` vocabulary of `Submission/Work/ORHomAlg`, while N9's `hswap` is
  stated in the `BalTensor`/`Tor1Vanishes`/`diagRightModule` vocabulary of
  `Submission/Work/ORFlatness`.  The glue is `Work.ORBridgeTor.hswap_of_jl52`
  (`Submission/Work/ORBridgeTor/HSwap.lean`).

## Contents of this file

* `Work.ORBridgeTor.invCoeff` — the antipode `β ↦ β^* = Σ c_g g⁻¹` of the group algebra.

* `Work.ORBridgeTor.AntiAut K S` — a `K`-linear bijective anti-endomorphism of a `K`-algebra
  `S`, with its API.

* `Work.ORBridgeTor.diagLeftModule` — the left diagonal `K[G]`-module structure on
  `V ⊗[K] S`, `g • (v ⊗ s) = (g • v) ⊗ (φ g · s)`, the mirror of
  `Work.ORFlatness.diagRightModule`.
-/
import Mathlib
import Submission.Work.ORFlatness.DiagonalRight
import Submission.Work.ORHomAlg.Dual

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open TensorProduct MulOpposite

universe u

namespace Work.ORBridgeTor

/-! ## The antipode of the group algebra -/

section InvCoeff

variable {K : Type u} [CommSemiring K] {G : Type u} [Group G]

/-- **The antipode of the group algebra**: `β ↦ β^*`, `Σ c_g · g ↦ Σ c_g · g⁻¹`.  It is the
anti-automorphism of `K[G]` induced by the group inversion. -/
noncomputable def invCoeff (β : MonoidAlgebra K G) : MonoidAlgebra K G :=
  β.coeff.sum (fun g c => MonoidAlgebra.single g⁻¹ c)

@[simp] theorem invCoeff_single (g : G) (c : K) :
    invCoeff (MonoidAlgebra.single g c) = MonoidAlgebra.single g⁻¹ c := by
  rw [invCoeff, MonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (MonoidAlgebra.single_zero g⁻¹)

@[simp] theorem invCoeff_zero : invCoeff (0 : MonoidAlgebra K G) = 0 := by
  rw [invCoeff, MonoidAlgebra.coeff_zero, Finsupp.sum_zero_index]

theorem invCoeff_add (β γ : MonoidAlgebra K G) :
    invCoeff (β + γ) = invCoeff β + invCoeff γ := by
  rw [invCoeff, invCoeff, invCoeff, MonoidAlgebra.coeff_add, Finsupp.sum_add_index']
  · intro a; exact MonoidAlgebra.single_zero a⁻¹
  · intro a b₁ b₂; simp

/-- The coefficients of the antipode: `(β^*).coeff x = β.coeff x⁻¹`. -/
@[simp] theorem coeff_invCoeff (β : MonoidAlgebra K G) (x : G) :
    (invCoeff β).coeff x = β.coeff x⁻¹ := by
  classical
  rw [invCoeff, Finsupp.sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  have hterm : ∀ g : G,
      (MonoidAlgebra.single g⁻¹ (β.coeff g)).coeff x = if g = x⁻¹ then β.coeff g else 0 := by
    intro g
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h : g = x⁻¹
    · rw [if_pos (by rw [h, inv_inv]), if_pos h]
    · rw [if_neg (by intro hh; exact h (by rw [← hh, inv_inv])), if_neg h]
  rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_ite_eq']
  by_cases h : x⁻¹ ∈ β.coeff.support
  · rw [if_pos h]
  · rw [if_neg h]
    by_contra hc
    exact h (Finsupp.mem_support_iff.mpr (Ne.symm hc))

theorem mem_support_invCoeff {β : MonoidAlgebra K G} {x : G} :
    x ∈ (invCoeff β).coeff.support ↔ x⁻¹ ∈ β.coeff.support := by
  classical
  rw [Finsupp.mem_support_iff, coeff_invCoeff, Finsupp.mem_support_iff]

theorem invCoeff_involutive : Function.Involutive (invCoeff (K := K) (G := G)) := by
  classical
  intro β
  ext x
  rw [coeff_invCoeff, coeff_invCoeff]
  simp

@[simp] theorem invCoeff_invCoeff (β : MonoidAlgebra K G) : invCoeff (invCoeff β) = β :=
  invCoeff_involutive β

theorem invCoeff_injective : Function.Injective (invCoeff (K := K) (G := G)) :=
  (invCoeff_involutive (K := K) (G := G)).injective

theorem invCoeff_ne_zero {β : MonoidAlgebra K G} : invCoeff β ≠ 0 ↔ β ≠ 0 := by
  rw [← invCoeff_zero (K := K) (G := G)]
  exact (invCoeff_injective (K := K) (G := G)).ne_iff

/-- **The Weinbaum support condition of Lemma 5.1′ is invariant under the antipode**: the images
of `supp β` and of `supp β^*` in `G ⧸ N` are simultaneously pairwise distinct. -/
theorem injOn_mk_support_invCoeff (N : Subgroup G) [N.Normal] (β : MonoidAlgebra K G) :
    Set.InjOn (QuotientGroup.mk (s := N)) (invCoeff β).coeff.support ↔
      Set.InjOn (QuotientGroup.mk (s := N)) β.coeff.support := by
  have key : ∀ a b : G, QuotientGroup.mk (s := N) a = QuotientGroup.mk (s := N) b →
      QuotientGroup.mk (s := N) a⁻¹ = QuotientGroup.mk (s := N) b⁻¹ := by
    intro a b h'
    simpa [QuotientGroup.mk_inv] using congrArg Inv.inv h'
  constructor
  · intro h a ha b hb hab
    have ha' : a⁻¹ ∈ (invCoeff β).coeff.support :=
      (mem_support_invCoeff (β := β)).mpr (by simpa using ha)
    have hb' : b⁻¹ ∈ (invCoeff β).coeff.support :=
      (mem_support_invCoeff (β := β)).mpr (by simpa using hb)
    simpa using congrArg Inv.inv (h ha' hb' (key a b hab))
  · intro h a ha b hb hab
    have ha' : a⁻¹ ∈ β.coeff.support := (mem_support_invCoeff (β := β)).mp ha
    have hb' : b⁻¹ ∈ β.coeff.support := (mem_support_invCoeff (β := β)).mp hb
    simpa using congrArg Inv.inv (h ha' hb' (key a b hab))

end InvCoeff

/-! ## `K`-linear anti-automorphisms of a `K`-algebra -/

/-- **A `K`-linear bijective anti-endomorphism of a `K`-algebra `S`.**

For `S = U(G)` (or `S = D(G)`) the intended instance is the antipode `ι = J ∘ *` of the ring of
affiliated operators: it is `K`-linear, additive, bijective, and satisfies
`ι (s * t) = ι t * ι s`, `ι 1 = 1` and `ι (gen g) = (gen g)⁻¹`.  This is the datum that
transports Lemma 5.1′ from left modules to right modules (mismatch (M2)). -/
structure AntiAut (K : Type u) [CommSemiring K] (S : Type u) [Semiring S] [Algebra K S] where
  /-- the underlying `K`-linear equivalence -/
  toLinearEquiv : S ≃ₗ[K] S
  /-- `ι` reverses products -/
  map_mul' : ∀ a b : S, toLinearEquiv (a * b) = toLinearEquiv b * toLinearEquiv a
  /-- `ι` preserves `1` -/
  map_one' : toLinearEquiv 1 = 1

namespace AntiAut

variable {K : Type u} [CommSemiring K] {S : Type u} [Semiring S] [Algebra K S]

instance instFunLike : FunLike (AntiAut K S) S S where
  coe f := f.toLinearEquiv
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact LinearEquiv.ext fun x => congrFun h x

@[simp] theorem coe_apply (f : AntiAut K S) (x : S) : f x = f.toLinearEquiv x := rfl

theorem map_add (f : AntiAut K S) (a b : S) : f (a + b) = f a + f b :=
  f.toLinearEquiv.map_add a b

theorem map_mul (f : AntiAut K S) (a b : S) : f (a * b) = f b * f a := f.map_mul' a b

theorem map_one (f : AntiAut K S) : f 1 = 1 := f.map_one'

theorem map_zero (f : AntiAut K S) : f 0 = 0 := f.toLinearEquiv.map_zero

theorem map_smul (f : AntiAut K S) (c : K) (a : S) : f (c • a) = c • f a :=
  f.toLinearEquiv.map_smul c a

theorem injective (f : AntiAut K S) : Function.Injective f := f.toLinearEquiv.injective

theorem surjective (f : AntiAut K S) : Function.Surjective f := f.toLinearEquiv.surjective

theorem bijective (f : AntiAut K S) : Function.Bijective f := f.toLinearEquiv.bijective

/-- The inverse of an anti-automorphism is again an anti-automorphism. -/
def symm (f : AntiAut K S) : AntiAut K S where
  toLinearEquiv := f.toLinearEquiv.symm
  map_mul' a b := by
    refine f.injective ?_
    show f.toLinearEquiv (f.toLinearEquiv.symm (a * b)) =
      f.toLinearEquiv (f.toLinearEquiv.symm b * f.toLinearEquiv.symm a)
    rw [f.map_mul', LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
  map_one' := by
    refine f.injective ?_
    show f.toLinearEquiv (f.toLinearEquiv.symm 1) = f.toLinearEquiv 1
    rw [LinearEquiv.apply_symm_apply, f.map_one']

@[simp] theorem symm_apply_apply (f : AntiAut K S) (x : S) : f (f.symm x) = x :=
  f.toLinearEquiv.apply_symm_apply x

@[simp] theorem apply_symm_apply (f : AntiAut K S) (x : S) : f.symm (f x) = x :=
  f.toLinearEquiv.symm_apply_apply x

end AntiAut

/-! ## The left diagonal action on `V ⊗[K] S` -/

section DiagLeft

variable (K : Type u) [CommRing K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
variable (V : Type u) [AddCommGroup V] [Module K V] [Module (MonoidAlgebra K G) V]
variable [IsScalarTower K (MonoidAlgebra K G) V] [SMulCommClass K (MonoidAlgebra K G) V]

/-- The action `v ↦ g • v` of `g` on `V`, as a `K`-linear map. -/
noncomputable def actLinV (g : G) : V →ₗ[K] V where
  toFun v := MonoidAlgebra.single g (1 : K) • v
  map_add' v w := smul_add _ _ _
  map_smul' c v := (smul_comm c (MonoidAlgebra.single g (1 : K)) v).symm

@[simp] theorem actLinV_apply (g : G) (v : V) :
    actLinV K G V g v = MonoidAlgebra.single g (1 : K) • v := rfl

@[simp] theorem actLinV_one : actLinV K G V 1 = LinearMap.id := by
  ext v
  rw [actLinV_apply, ← MonoidAlgebra.one_def]
  simp

theorem actLinV_mul (g h : G) :
    actLinV K G V (g * h) = (actLinV K G V g).comp (actLinV K G V h) := by
  ext v
  rw [actLinV_apply, LinearMap.comp_apply, actLinV_apply, actLinV_apply, ← mul_smul,
    MonoidAlgebra.single_mul_single, one_mul]

/-- Left multiplication by `φ g` on `S`, as a `K`-linear map. -/
noncomputable def mulLinV (g : G) : S →ₗ[K] S :=
  LinearMap.mulLeft K (Work.ORFlatness.gElemR K G S φ g)

@[simp] theorem mulLinV_apply (g : G) (s : S) :
    mulLinV K G S φ g s = Work.ORFlatness.gElemR K G S φ g * s := rfl

@[simp] theorem mulLinV_one : mulLinV K G S φ 1 = LinearMap.id := by
  ext s
  simp [mulLinV_apply, Work.ORFlatness.gElemR_one]

theorem mulLinV_mul (g h : G) :
    mulLinV K G S φ (g * h) = (mulLinV K G S φ g).comp (mulLinV K G S φ h) := by
  ext s
  simp only [mulLinV_apply, LinearMap.comp_apply, Work.ORFlatness.gElemR_mul, mul_assoc]

/-- The `K`-linear map `z ↦ g • z` of the left diagonal action on `V ⊗[K] S`. -/
noncomputable def diagLinV (g : G) : (V ⊗[K] S) →ₗ[K] (V ⊗[K] S) :=
  TensorProduct.map (actLinV K G V g) (mulLinV K G S φ g)

@[simp] theorem diagLinV_tmul (g : G) (v : V) (s : S) :
    diagLinV K G S φ V g (v ⊗ₜ[K] s) =
      (MonoidAlgebra.single g (1 : K) • v) ⊗ₜ[K] (Work.ORFlatness.gElemR K G S φ g * s) := by
  simp [diagLinV, actLinV, mulLinV]

@[simp] theorem diagLinV_one : diagLinV K G S φ V 1 = LinearMap.id := by
  rw [diagLinV, actLinV_one, mulLinV_one, TensorProduct.map_id]

theorem diagLinV_mul (g h : G) :
    diagLinV K G S φ V (g * h) = (diagLinV K G S φ V g).comp (diagLinV K G S φ V h) := by
  rw [diagLinV, diagLinV, diagLinV, actLinV_mul, mulLinV_mul, TensorProduct.map_comp]

/-- The left diagonal action, as a monoid homomorphism `G →* End_K(V ⊗[K] S)`. -/
noncomputable def diagMonoidHomV : G →* Module.End K (V ⊗[K] S) where
  toFun g := diagLinV K G S φ V g
  map_one' := diagLinV_one K G S φ V
  map_mul' g h := diagLinV_mul K G S φ V g h

/-- The left diagonal action of `K[G]` on `V ⊗[K] S`. -/
noncomputable def diagRingHomV : MonoidAlgebra K G →ₐ[K] Module.End K (V ⊗[K] S) :=
  (MonoidAlgebra.lift K (Module.End K (V ⊗[K] S)) G) (diagMonoidHomV K G S φ V)

theorem diagRingHomV_single (g : G) (c : K) :
    diagRingHomV K G S φ V (MonoidAlgebra.single g c) = c • diagLinV K G S φ V g := by
  rw [diagRingHomV, MonoidAlgebra.lift_single]
  rfl

/-- **The left diagonal `K[G]`-module structure on `V ⊗[K] S`**,
`g • (v ⊗ s) = (g • v) ⊗ (φ g · s)`.  This is the structure with respect to which node N8's
Lemma 5.1′ (`Work.ORTorsion.torsionFree_tensor`) is stated. -/
noncomputable def diagLeftModule : Module (MonoidAlgebra K G) (V ⊗[K] S) where
  smul a z := diagRingHomV K G S φ V a z
  one_smul z := by
    show diagRingHomV K G S φ V 1 z = z
    rw [map_one, Module.End.one_apply]
  mul_smul a b z := by
    show diagRingHomV K G S φ V (a * b) z = diagRingHomV K G S φ V a (diagRingHomV K G S φ V b z)
    rw [map_mul, Module.End.mul_apply]
  smul_zero a := map_zero _
  smul_add a x y := map_add _ x y
  add_smul a b z := by
    show diagRingHomV K G S φ V (a + b) z =
      diagRingHomV K G S φ V a z + diagRingHomV K G S φ V b z
    rw [map_add]
    rfl
  zero_smul z := by
    show diagRingHomV K G S φ V 0 z = 0
    rw [map_zero]
    rfl

/-- The computation rule for the left diagonal action, on a pure tensor. -/
theorem diagRingHomV_single_tmul (g : G) (v : V) (s : S) :
    diagRingHomV K G S φ V (MonoidAlgebra.single g (1 : K)) (v ⊗ₜ[K] s) =
      (MonoidAlgebra.single g (1 : K) • v) ⊗ₜ[K] (Work.ORFlatness.gElemR K G S φ g * s) := by
  rw [diagRingHomV_single, one_smul]
  exact diagLinV_tmul K G S φ V g v s

/-- The scalar extraction rule for the left diagonal action. -/
theorem diagRingHomV_single_apply (g : G) (c : K) (z : V ⊗[K] S) :
    diagRingHomV K G S φ V (MonoidAlgebra.single g c) z =
      c • (diagRingHomV K G S φ V (MonoidAlgebra.single g (1 : K)) z) := by
  rw [diagRingHomV_single, diagRingHomV_single, one_smul, LinearMap.smul_apply]

/-- **The left diagonal action on `V ⊗[K] S`**, as a function of the scalar.  This is the
action with respect to which node N8's Lemma 5.1′ (`Work.ORTorsion.torsionFree_tensor`) is
stated; the `•` notation is deliberately avoided because the scalar type `K[G]` is also the
scalar type of `TensorProduct.leftHasSMul`. -/
noncomputable def diagLeftAct (γ : MonoidAlgebra K G) (z : V ⊗[K] S) : V ⊗[K] S :=
  diagRingHomV K G S φ V γ z

theorem diagLeftAct_add (γ γ' : MonoidAlgebra K G) (z : V ⊗[K] S) :
    diagLeftAct K G S φ V (γ + γ') z =
      diagLeftAct K G S φ V γ z + diagLeftAct K G S φ V γ' z := by
  show diagRingHomV K G S φ V (γ + γ') z
    = diagRingHomV K G S φ V γ z + diagRingHomV K G S φ V γ' z
  rw [map_add]
  rfl

theorem diagLeftAct_single (g : G) (c : K) (z : V ⊗[K] S) :
    diagLeftAct K G S φ V (MonoidAlgebra.single g c) z =
      c • (diagLeftAct K G S φ V (MonoidAlgebra.single g (1 : K)) z) :=
  diagRingHomV_single_apply K G S φ V g c z

theorem diagLeftAct_map_add (γ : MonoidAlgebra K G) (z z' : V ⊗[K] S) :
    diagLeftAct K G S φ V γ (z + z') =
      diagLeftAct K G S φ V γ z + diagLeftAct K G S φ V γ z' := by
  show diagRingHomV K G S φ V γ (z + z')
    = diagRingHomV K G S φ V γ z + diagRingHomV K G S φ V γ z'
  exact map_add _ z z'

theorem diagLeftAct_map_zero (γ : MonoidAlgebra K G) :
    diagLeftAct K G S φ V γ 0 = (0 : V ⊗[K] S) := by
  show diagRingHomV K G S φ V γ 0 = (0 : V ⊗[K] S)
  exact map_zero _

theorem diagLeftAct_zero (z : V ⊗[K] S) : diagLeftAct K G S φ V 0 z = 0 := by
  show diagRingHomV K G S φ V 0 z = (0 : V ⊗[K] S)
  rw [map_zero]
  rfl

theorem diagLeftAct_single_tmul (g : G) (v : V) (s : S) :
    diagLeftAct K G S φ V (MonoidAlgebra.single g (1 : K)) (v ⊗ₜ[K] s) =
      (MonoidAlgebra.single g (1 : K) • v) ⊗ₜ[K] (Work.ORFlatness.gElemR K G S φ g * s) :=
  diagRingHomV_single_tmul K G S φ V g v s

end DiagLeft

end Work.ORBridgeTor
