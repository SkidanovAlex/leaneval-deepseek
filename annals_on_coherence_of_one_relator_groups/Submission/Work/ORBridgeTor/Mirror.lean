/-
# The transport of Lemma 5.1′ from left modules to right modules (mismatch (M2))

Node N8 (`Work.ORTorsion.torsionFree_tensor`) proves Lemma 5.1′ for the **left** diagonal action
on `V ⊗[K] S`, `g • (v ⊗ s) = (g • v) ⊗ (φ g · s)`.  Node N9's hypothesis `hA`
(`Work.ORFlatness.tor1Vanishes_diagonal_jl_right`) needs the **right** diagonal action on
`S ⊗[K] X` (`Work.ORFlatness.diagRightModule`), `(s ⊗ x)·g = (s · φ g) ⊗ (g⁻¹ • x)`.

The transport is the paper's antipode `ι = J ∘ *`: the `K`-linear bijective anti-endomorphism of
`S` with `ι (φ g) = φ g⁻¹` (`Work.ORBridgeTor.AntiAut`).  The map

`Ψ : S ⊗[K] X → X ⊗[K] S,  s ⊗ x ↦ x ⊗ ι s`

intertwines the two actions with a twist by inversion:

`Ψ (z · g) = g⁻¹ • Ψ z`,  and hence  `Ψ ((op β) • z) = β^* • Ψ z`  with `β^* = invCoeff β`.

Since `supp β^*` is the inverse of `supp β`, the Weinbaum hypothesis transfers
(`Work.ORBridgeTor.injOn_mk_support_invCoeff`), and injectivity of `β^* • ·` (Lemma 5.1′ at `β^*`)
gives injectivity of `· β` — the right-module form consumed by N9's `hA`.

## Main results

* `Work.ORBridgeTor.mirrorEquiv_diagRightAct` — the intertwining identity
  `Ψ ((op β) • z) = β^* • Ψ z`.
* `Work.ORBridgeTor.torsionFree_diagRight_of_diagLeft` — Lemma 5.1′ in the right-module form,
  from its left-module form.
-/
import Submission.Work.ORBridgeTor.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open TensorProduct MulOpposite

universe u

namespace Work.ORBridgeTor

section RightAct

variable (K : Type u) [CommRing K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
variable (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
variable [IsScalarTower K (MonoidAlgebra K G) X] [SMulCommClass K (MonoidAlgebra K G) X]

/-- The right diagonal action of `(K[G])ᵐᵒᵖ` on `S ⊗[K] X`, made explicit: this is the action of
`Work.ORFlatness.diagRightModule`. -/
noncomputable def diagRightAct (a : (MonoidAlgebra K G)ᵐᵒᵖ) (z : S ⊗[K] X) : S ⊗[K] X :=
  Work.ORFlatness.diagRingHomR K G S φ X (Work.ORFlatness.opRingHom K G a) z

/-- `diagRightAct` is the scalar multiplication of `Work.ORFlatness.diagRightModule`. -/
theorem diagRightModule_smul_eq (a : (MonoidAlgebra K G)ᵐᵒᵖ) (z : S ⊗[K] X) :
    letI := Work.ORFlatness.diagRightModule K G S φ X
    a • z = diagRightAct K G S φ X a z := rfl

theorem diagRightAct_add (a b : (MonoidAlgebra K G)ᵐᵒᵖ) (z : S ⊗[K] X) :
    diagRightAct K G S φ X (a + b) z =
      diagRightAct K G S φ X a z + diagRightAct K G S φ X b z := by
  show Work.ORFlatness.diagRingHomR K G S φ X (Work.ORFlatness.opRingHom K G (a + b)) z = _
  rw [map_add, map_add]
  rfl

theorem diagRightAct_zero (z : S ⊗[K] X) :
    diagRightAct K G S φ X 0 z = (0 : S ⊗[K] X) := by
  show Work.ORFlatness.diagRingHomR K G S φ X (Work.ORFlatness.opRingHom K G 0) z = 0
  rw [map_zero, map_zero]
  rfl

theorem diagRightAct_map_add (a : (MonoidAlgebra K G)ᵐᵒᵖ) (y y' : S ⊗[K] X) :
    diagRightAct K G S φ X a (y + y') =
      diagRightAct K G S φ X a y + diagRightAct K G S φ X a y' :=
  map_add _ y y'

theorem diagRightAct_map_zero (a : (MonoidAlgebra K G)ᵐᵒᵖ) :
    diagRightAct K G S φ X a 0 = (0 : S ⊗[K] X) :=
  map_zero _

/-- The right diagonal action of a monomial, in the form needed to compute with the antipode. -/
theorem diagRightAct_op_single (g : G) (c : K) (z : S ⊗[K] X) :
    diagRightAct K G S φ X (op (MonoidAlgebra.single g c)) z =
      c • (diagRightAct K G S φ X (op (MonoidAlgebra.single g (1 : K))) z) := by
  rw [diagRightAct, diagRightAct, Work.ORFlatness.opRingHom_op_single,
    Work.ORFlatness.opRingHom_op_single, Work.ORFlatness.diagRingHomR_single,
    Work.ORFlatness.diagRingHomR_single]
  simp

/-- The right diagonal action of `op (single g 1)` on a pure tensor. -/
theorem diagRightAct_op_single_one_tmul (g : G) (s : S) (x : X) :
    diagRightAct K G S φ X (op (MonoidAlgebra.single g (1 : K))) (s ⊗ₜ[K] x) =
      (s * Work.ORFlatness.gElemR K G S φ g) ⊗ₜ[K] (MonoidAlgebra.single g⁻¹ (1 : K) • x) := by
  show Work.ORFlatness.diagRingHomR K G S φ X
      (Work.ORFlatness.opRingHom K G (op (MonoidAlgebra.single g (1 : K)))) (s ⊗ₜ[K] x) = _
  rw [Work.ORFlatness.opRingHom_op_single, Work.ORFlatness.diagRingHomR_single]
  simp [Work.ORFlatness.diagLinR_tmul, Work.ORFlatness.gElemR, one_smul]

end RightAct

/-! ## The intertwining map -/

section Mirror

variable (K : Type u) [CommRing K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)

/-- The `K`-linear bijection `Ψ : S ⊗[K] X → X ⊗[K] S`, `s ⊗ x ↦ x ⊗ ι s`, used to transport
Lemma 5.1′ from left to right modules. -/
noncomputable def mirrorEquiv (ι : AntiAut K S) (X : Type u) [AddCommGroup X] [Module K X] :
    (S ⊗[K] X) ≃ₗ[K] (X ⊗[K] S) :=
  (TensorProduct.congr ι.toLinearEquiv (LinearEquiv.refl K X)).trans (TensorProduct.comm K S X)

theorem mirrorEquiv_tmul (ι : AntiAut K S) (X : Type u) [AddCommGroup X] [Module K X]
    (s : S) (x : X) :
    mirrorEquiv K S ι X (s ⊗ₜ[K] x) = x ⊗ₜ[K] ι s := by
  simp [mirrorEquiv]

theorem mirrorEquiv_injective (ι : AntiAut K S) (X : Type u) [AddCommGroup X] [Module K X] :
    Function.Injective (mirrorEquiv K S ι X) :=
  (mirrorEquiv K S ι X).injective

variable (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
variable [IsScalarTower K (MonoidAlgebra K G) X] [SMulCommClass K (MonoidAlgebra K G) X]

/-- The monomial form of the intertwining: `Ψ (z · g) = g⁻¹ • Ψ z`. -/
theorem mirrorEquiv_diagRightAct_single (ι : AntiAut K S)
    (hι : ∀ g : G, ι (Work.ORFlatness.gElemR K G S φ g) =
      Work.ORFlatness.gElemR K G S φ g⁻¹)
    (g : G) (z : S ⊗[K] X) :
    mirrorEquiv K S ι X (diagRightAct K G S φ X (op (MonoidAlgebra.single g (1 : K))) z) =
      diagLeftAct K G S φ X (MonoidAlgebra.single g⁻¹ (1 : K)) (mirrorEquiv K S ι X z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [diagRightAct_map_zero, map_zero, diagLeftAct_map_zero]
  | tmul s x =>
      rw [diagRightAct_op_single_one_tmul, mirrorEquiv_tmul, mirrorEquiv_tmul,
        diagLeftAct_single_tmul, AntiAut.map_mul, hι]
  | add y y' hy hy' =>
      rw [diagRightAct_map_add, map_add, map_add, hy, hy', diagLeftAct_map_add]

/-- **The intertwining identity**: `Ψ ((op β) • z) = β^* • Ψ z` for every `β ∈ K[G]`. -/
theorem mirrorEquiv_diagRightAct (ι : AntiAut K S)
    (hι : ∀ g : G, ι (Work.ORFlatness.gElemR K G S φ g) =
      Work.ORFlatness.gElemR K G S φ g⁻¹)
    (β : MonoidAlgebra K G) (z : S ⊗[K] X) :
    mirrorEquiv K S ι X (diagRightAct K G S φ X (op β) z) =
      diagLeftAct K G S φ X (invCoeff β) (mirrorEquiv K S ι X z) := by
  have key : ∀ (f : G →₀ K) (z : S ⊗[K] X),
      mirrorEquiv K S ι X
        (diagRightAct K G S φ X (op (f.sum MonoidAlgebra.single)) z) =
      diagLeftAct K G S φ X (invCoeff (f.sum MonoidAlgebra.single))
        (mirrorEquiv K S ι X z) := by
    intro f
    refine Finsupp.induction_linear f ?_ ?_ ?_
    · intro z
      rw [Finsupp.sum_zero_index, MulOpposite.op_zero, diagRightAct_zero, map_zero,
        invCoeff_zero, diagLeftAct_zero]
    · intro f₁ f₂ h₁ h₂ z
      have hsum : (f₁ + f₂).sum MonoidAlgebra.single =
          f₁.sum MonoidAlgebra.single + f₂.sum MonoidAlgebra.single :=
        Finsupp.sum_add_index' (fun a => MonoidAlgebra.single_zero a) (fun a b₁ b₂ => by
          simp)
      rw [hsum, MulOpposite.op_add, diagRightAct_add, map_add, h₁ z, h₂ z, invCoeff_add,
        diagLeftAct_add]
    · intro g c z
      rw [Finsupp.sum_single_index (MonoidAlgebra.single_zero g), invCoeff_single,
        diagRightAct_op_single, map_smul, diagLeftAct_single,
        mirrorEquiv_diagRightAct_single (K := K) (G := G) (S := S) (φ := φ) (X := X)
          (ι := ι) (hι := hι) (g := g) z]
  simpa [MonoidAlgebra.sum_coeff_single] using key β.coeff z

end Mirror

/-! ## Lemma 5.1′ in the right-module form -/

section Transfer

variable (K : Type u) [CommRing K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)

/-- **The right-module form of Lemma 5.1′ (mismatch (M2))**, transported from its left-module
form.

`hleft` is the left-module statement — for `S = D(G)` it is node N8's
`Work.ORTorsion.torsionFree_tensor` (`hleft` is asked for all left `K[G]`-modules `V` and all
`γ ∈ K[G]` with `supp γ` injective in `G ⧸ N` and `γ ≠ 0`); `ι` is the antipode of `S`, with
`ι (φ g) = (φ g)⁻¹`.  The conclusion is Lemma 5.1′ for the right diagonal action
`Work.ORFlatness.diagRightModule` on `S ⊗[K] X`, in exactly the form of N9's `hA`. -/
theorem torsionFree_diagRight_of_diagLeft (N : Subgroup G) [N.Normal]
    (hleft : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module (MonoidAlgebra K G) V]
      [IsScalarTower K (MonoidAlgebra K G) V] [SMulCommClass K (MonoidAlgebra K G) V]
      (γ : MonoidAlgebra K G), Set.InjOn (QuotientGroup.mk (s := N)) γ.coeff.support →
      γ ≠ 0 → Function.Injective (fun m : V ⊗[K] S => diagLeftAct K G S φ V γ m))
    (ι : AntiAut K S)
    (hι : ∀ g : G, ι (Work.ORFlatness.gElemR K G S φ g) =
      Work.ORFlatness.gElemR K G S φ g⁻¹)
    (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G) X]
    [IsScalarTower K (MonoidAlgebra K G) X] [SMulCommClass K (MonoidAlgebra K G) X]
    (β : MonoidAlgebra K G)
    (hβ : Set.InjOn (QuotientGroup.mk (s := N)) β.coeff.support) (hβ0 : β ≠ 0) :
    letI := Work.ORFlatness.diagRightModule K G S φ X
    Function.Injective (fun z : S ⊗[K] X => (op β) • z) := by
  letI := Work.ORFlatness.diagRightModule K G S φ X
  have hinj : Function.Injective
      (fun w : X ⊗[K] S => diagLeftAct K G S φ X (invCoeff β) w) :=
    hleft X (invCoeff β) ((injOn_mk_support_invCoeff N β).mpr hβ)
      ((invCoeff_ne_zero (K := K) (G := G)).mpr hβ0)
  intro z z' hzz
  have hzz' : diagRightAct K G S φ X (op β) z = diagRightAct K G S φ X (op β) z' := hzz
  refine (mirrorEquiv K S ι X).injective (hinj ?_)
  show diagLeftAct K G S φ X (invCoeff β) (mirrorEquiv K S ι X z)
    = diagLeftAct K G S φ X (invCoeff β) (mirrorEquiv K S ι X z')
  rw [← mirrorEquiv_diagRightAct (K := K) (G := G) (S := S) (φ := φ) (X := X)
      (ι := ι) (hι := hι) β z,
    ← mirrorEquiv_diagRightAct (K := K) (G := G) (S := S) (φ := φ) (X := X)
      (ι := ι) (hι := hι) β z', hzz']

end Transfer

end Work.ORBridgeTor
