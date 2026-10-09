import Mathlib
import Submission.Work.SSGRoute.EulerSymm.finrank_invariants_diagTensor_regular
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Invariants of `𝔽_p[Q] ⊗ Z` under a group acting through a finite quotient

Lane `Work.SSGRoute.coker_obstruction_pt`.  The local Galois group `D_C = decomp k A ⊓ res⁻¹C`
which acts on the trivial-coefficient local cohomology `H¹_loc(U, 𝔽_p)` is **infinite**, but it
acts through the *finite* quotient `↥((res k K) '' D_C) ≤ Gal(K/k)`.  The existing
`Work.SSGRoute.EulerSymm.finrank_invariants_diagTensor_regular` computes the invariants of
`𝔽_p[Q] ⊗ N` only for a *finite* group `Q` (it sums over `Q` and uses `Fintype Q`).

This file supplies the missing form: for a surjection `φ : G →* Q` onto a finite group `Q`, a
`G`-module `Z` on which `ker φ` acts trivially, and `𝔽_p[Q]` with the left-regular `Q`-action
pulled back along `φ`,

  `dim (𝔽_p[Q] ⊗ Z)^{diag G} = dim Z`.

The proof is the same explicit computation as in the finite-group case, but with the index set `Q`
instead of `G`: with a chosen section `s : Q → G` of `φ` one maps `Z` into the invariants by
`v ↦ ∑_q single q 1 ⊗ (s q • v)`, and the coordinate expansion of `𝔽_p[Q] ⊗ Z` shows that this is
onto.  No group action on `Z` other than the given `G`-action is needed.

## Main result

* `E7Fin.diagTensorInvariants_pullback_regular`
-/

open scoped TensorProduct

namespace Work.SSGRoute.E7Fin

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-- A chosen section of a surjection. -/
noncomputable def pbrSec {G Q : Type} [Group G] [Group Q] (φ : G →* Q)
    (hφ : Function.Surjective φ) (q : Q) : G := Classical.choose (hφ q)

lemma pbrSec_spec {G Q : Type} [Group G] [Group Q] (φ : G →* Q)
    (hφ : Function.Surjective φ) (q : Q) : φ (pbrSec φ hφ q) = q :=
  Classical.choose_spec (hφ q)

/-- The `q`-th coordinate functional on `𝔽_p[Q] ⊗ Z`. -/
noncomputable def pbrKappa (p : ℕ) [Fact p.Prime] (Q : Type) [Group Q] [Fintype Q]
    [DecidableEq Q] (Z : Type) [AddCommGroup Z] [Module (ZMod p) Z] (q : Q) :
    (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) Q) Z) →ₗ[ZMod p] Z :=
  (TensorProduct.lid (ZMod p) Z).comp
    (LinearMap.rTensor Z (Work.SSGRoute.EulerSymm.dtrCoeff p Q q))

lemma pbrKappa_tmul (p : ℕ) [Fact p.Prime] (Q : Type) [Group Q] [Fintype Q] [DecidableEq Q]
    (Z : Type) [AddCommGroup Z] [Module (ZMod p) Z] (q : Q) (a : MonoidAlgebra (ZMod p) Q)
    (z : Z) :
    pbrKappa p Q Z q (a ⊗ₜ[ZMod p] z) = (a.coeff q) • z := by
  rw [pbrKappa, LinearMap.comp_apply, LinearMap.rTensor_tmul,
    Work.SSGRoute.EulerSymm.dtrCoeff_apply]
  exact TensorProduct.lid_tmul z (a.coeff q)

/-- **The coordinate expansion** of a pure tensor. -/
lemma pbr_expand_pure (p : ℕ) [Fact p.Prime] (Q : Type) [Group Q] [Fintype Q] [DecidableEq Q]
    (Z : Type) [AddCommGroup Z] [Module (ZMod p) Z] (a : MonoidAlgebra (ZMod p) Q) (z : Z) :
    (∑ q : Q, MonoidAlgebra.single q (1 : ZMod p) ⊗ₜ[ZMod p] ((a.coeff q) • z))
      = a ⊗ₜ[ZMod p] z := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | single m r =>
      rw [Finset.sum_eq_single m]
      · rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_pos rfl,
          ← TensorProduct.smul_tmul, ← Work.SSGRoute.EulerSymm.dtr_single_eq_smul]
      · intro b _ hb
        rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hb),
          zero_smul, TensorProduct.tmul_zero]
      · intro hm; exact absurd (Finset.mem_univ m) hm
  | add x y hx hy =>
      rw [MonoidAlgebra.coeff_add, TensorProduct.add_tmul]
      simp only [Finsupp.add_apply, add_smul, TensorProduct.tmul_add, Finset.sum_add_distrib,
        hx, hy]

/-- **The coordinate expansion**: every element of `𝔽_p[Q] ⊗ Z` is the sum of its coordinates. -/
theorem pbr_expand (p : ℕ) [Fact p.Prime] (Q : Type) [Group Q] [Fintype Q] [DecidableEq Q]
    (Z : Type) [AddCommGroup Z] [Module (ZMod p) Z]
    (x : TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) Q) Z) :
    (∑ q : Q, MonoidAlgebra.single q (1 : ZMod p) ⊗ₜ[ZMod p] (pbrKappa p Q Z q x)) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a z =>
      simp only [pbrKappa_tmul]
      exact pbr_expand_pure p Q Z a z
  | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

/-- **Equivariance of the coordinates**: the `(φ g * q)`-th coordinate of `g • x` is `g` applied
to the `q`-th coordinate of `x`. -/
lemma pbrKappa_smul (p : ℕ) [Fact p.Prime] {G : Type} [Group G] {Q : Type} [Group Q]
    [Fintype Q] [DecidableEq Q] (φ : G →* Q)
    [DistribMulAction G (MonoidAlgebra (ZMod p) Q)]
    [SMulCommClass G (ZMod p) (MonoidAlgebra (ZMod p) Q)]
    (hact : ∀ (g : G) (a : MonoidAlgebra (ZMod p) Q), g • a = (φ g) • a)
    (Z : Type) [AddCommGroup Z] [Module (ZMod p) Z] [DistribMulAction G Z]
    [SMulCommClass G (ZMod p) Z] (g : G) (q : Q)
    (x : TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) Q) Z) :
    pbrKappa p Q Z (φ g * q) (g • x) = g • pbrKappa p Q Z q x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a z =>
      rw [Work.Shrinking.diagTensor_smul_tmul, pbrKappa_tmul, pbrKappa_tmul, hact g a,
        Work.CohomologicalShrinking.coeff_smul_monoidAlgebra]
      rw [show (φ g)⁻¹ * (φ g * q) = q from by rw [← mul_assoc, inv_mul_cancel, one_mul]]
      exact (smul_comm g (a.coeff q) z).symm
  | add x y hx hy =>
      simp only [map_add, smul_add, hx, hy]

/-- Two elements of `G` with the same image in `Q` act in the same way on `Z`. -/
lemma pbr_smul_eq_of_phi_eq (p : ℕ) [Fact p.Prime] {G : Type} [Group G] {Q : Type} [Group Q]
    (φ : G →* Q) (Z : Type) [AddCommGroup Z] [DistribMulAction G Z]
    (hker : ∀ (g : G), φ g = 1 → ∀ z : Z, g • z = z)
    {g g' : G} (h : φ g = φ g') (z : Z) : g • z = g' • z := by
  have hmem : φ (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have hz : (g⁻¹ * g') • z = z := hker (g⁻¹ * g') hmem z
  calc g • z = g • ((g⁻¹ * g') • z) := by rw [hz]
    _ = (g * (g⁻¹ * g')) • z := (mul_smul g (g⁻¹ * g') z).symm
    _ = g' • z := by rw [mul_inv_cancel_left]

/-- The `G`-equivariant linear map `Z → 𝔽_p[Q] ⊗ Z` whose image is the space of invariants. -/
noncomputable def pbrPhi (p : ℕ) [Fact p.Prime] {G : Type} [Group G] {Q : Type} [Group Q]
    [Fintype Q] [DecidableEq Q] (φ : G →* Q) [DistribMulAction G (MonoidAlgebra (ZMod p) Q)]
    [SMulCommClass G (ZMod p) (MonoidAlgebra (ZMod p) Q)]
    (Z : Type) [AddCommGroup Z] [Module (ZMod p) Z] [DistribMulAction G Z]
    [SMulCommClass G (ZMod p) Z] (hφ : Function.Surjective φ) :
    Z →ₗ[ZMod p] (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) Q) Z) :=
  ∑ q : Q, (TensorProduct.mk (ZMod p) (MonoidAlgebra (ZMod p) Q) Z
      (MonoidAlgebra.single q (1 : ZMod p))).comp
    (Work.Shrinking.actLinear (p := p) (G := G) (pbrSec φ hφ q) : Z →ₗ[ZMod p] Z)

lemma pbrPhi_apply (p : ℕ) [Fact p.Prime] {G : Type} [Group G] {Q : Type} [Group Q]
    [Fintype Q] [DecidableEq Q] (φ : G →* Q) [DistribMulAction G (MonoidAlgebra (ZMod p) Q)]
    [SMulCommClass G (ZMod p) (MonoidAlgebra (ZMod p) Q)]
    (Z : Type) [AddCommGroup Z] [Module (ZMod p) Z] [DistribMulAction G Z]
    [SMulCommClass G (ZMod p) Z] (hφ : Function.Surjective φ) (v : Z) :
    pbrPhi p φ Z hφ v
      = ∑ q : Q, MonoidAlgebra.single q (1 : ZMod p) ⊗ₜ[ZMod p] (pbrSec φ hφ q • v) := by
  simp only [pbrPhi, LinearMap.sum_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
    Work.Shrinking.actLinear_apply]

lemma pbrPhi_invariant (p : ℕ) [Fact p.Prime] {G : Type} [Group G] {Q : Type} [Group Q]
    [Fintype Q] [DecidableEq Q] (φ : G →* Q) [DistribMulAction G (MonoidAlgebra (ZMod p) Q)]
    [SMulCommClass G (ZMod p) (MonoidAlgebra (ZMod p) Q)]
    (hact : ∀ (g : G) (a : MonoidAlgebra (ZMod p) Q), g • a = (φ g) • a)
    (Z : Type) [AddCommGroup Z] [Module (ZMod p) Z] [DistribMulAction G Z]
    [SMulCommClass G (ZMod p) Z] (hφ : Function.Surjective φ)
    (hker : ∀ (g : G), φ g = 1 → ∀ z : Z, g • z = z) (v : Z) (g : G) :
    g • pbrPhi p φ Z hφ v = pbrPhi p φ Z hφ v := by
  rw [pbrPhi_apply, Finset.smul_sum]
  have hterm : ∀ q : Q,
      g • (MonoidAlgebra.single q (1 : ZMod p) ⊗ₜ[ZMod p] (pbrSec φ hφ q • v))
        = MonoidAlgebra.single (φ g * q) (1 : ZMod p) ⊗ₜ[ZMod p]
            (pbrSec φ hφ (φ g * q) • v) := by
    intro q
    have h1 : g • MonoidAlgebra.single q (1 : ZMod p)
        = MonoidAlgebra.single (φ g * q) (1 : ZMod p) := by
      rw [hact g, Work.CohomologicalShrinking.smul_monoidAlgebra,
        MonoidAlgebra.single_mul_single, mul_one]
    have h2 : g • (pbrSec φ hφ q • v) = pbrSec φ hφ (φ g * q) • v := by
      rw [← mul_smul]
      refine pbr_smul_eq_of_phi_eq p φ Z hker ?_ v
      rw [map_mul, pbrSec_spec, pbrSec_spec]
    rw [Work.Shrinking.diagTensor_smul_tmul, h1, h2]
  simp only [hterm]
  exact @Fintype.sum_equiv Q Q (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) Q) Z) _ _ _
    (Equiv.mulLeft (φ g))
    (fun q : Q => MonoidAlgebra.single (φ g * q) (1 : ZMod p) ⊗ₜ[ZMod p]
      (pbrSec φ hφ (φ g * q) • v))
    (fun q : Q => MonoidAlgebra.single q (1 : ZMod p) ⊗ₜ[ZMod p] (pbrSec φ hφ q • v))
    (fun _ => rfl)

lemma pbrKappa_one_phi (p : ℕ) [Fact p.Prime] {G : Type} [Group G] {Q : Type} [Group Q]
    [Fintype Q] [DecidableEq Q] (φ : G →* Q) [DistribMulAction G (MonoidAlgebra (ZMod p) Q)]
    [SMulCommClass G (ZMod p) (MonoidAlgebra (ZMod p) Q)]
    (Z : Type) [AddCommGroup Z] [Module (ZMod p) Z] [DistribMulAction G Z]
    [SMulCommClass G (ZMod p) Z] (hφ : Function.Surjective φ)
    (hker : ∀ (g : G), φ g = 1 → ∀ z : Z, g • z = z) (v : Z) :
    pbrKappa p Q Z 1 (pbrPhi p φ Z hφ v) = v := by
  rw [pbrPhi_apply, map_sum]
  simp only [pbrKappa_tmul]
  rw [Finset.sum_eq_single 1]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_pos rfl, one_smul]
    exact hker (pbrSec φ hφ 1) (by rw [pbrSec_spec]) v
  · intro b _ hb
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hb, zero_smul]
  · intro h1; exact absurd (Finset.mem_univ 1) h1

/-- **The invariant dimension of a pulled-back regular module.**  Let `φ : G →* Q` be a
surjection onto a finite group `Q`, let `G` act on `𝔽_p[Q]` through `φ` by the left-regular
action (`hact`, the canonical action of `Q` on its group algebra), and let `Z` be a finite
`𝔽_p[G]`-module on which `ker φ` acts trivially.  Then

  `dim (𝔽_p[Q] ⊗_{𝔽_p} Z)^{diag G} = dim Z`. -/
theorem diagTensorInvariants_pullback_regular
    (p : ℕ) [Fact p.Prime] {G Q : Type} [Group G] [Group Q] [Fintype Q] [DecidableEq Q]
    (φ : G →* Q) (hφ : Function.Surjective φ)
    [DistribMulAction G (MonoidAlgebra (ZMod p) Q)]
    [SMulCommClass G (ZMod p) (MonoidAlgebra (ZMod p) Q)]
    (hact : ∀ (g : G) (a : MonoidAlgebra (ZMod p) Q), g • a = (φ g) • a)
    (Z : Type) [AddCommGroup Z] [Module (ZMod p) Z] [DistribMulAction G Z]
    [SMulCommClass G (ZMod p) Z] [Finite Z]
    (hker : ∀ (g : G), φ g = 1 → ∀ z : Z, g • z = z) :
    Module.finrank (ZMod p)
      ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
        (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) Q) Z)) =
      Module.finrank (ZMod p) Z := by
  classical
  have hrange : LinearMap.range (pbrPhi p φ Z hφ) =
      Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
        (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) Q) Z) := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨v, rfl⟩
      exact Work.SSGRoute.PTCore.mem_invariantsSubmodule.mpr
        (pbrPhi_invariant p φ hact Z hφ hker v)
    · intro hx
      have hx' : ∀ g : G, g • x = x :=
        Work.SSGRoute.PTCore.mem_invariantsSubmodule.mp hx
      refine ⟨pbrKappa p Q Z 1 x, ?_⟩
      rw [pbrPhi_apply]
      trans ∑ q : Q, MonoidAlgebra.single q (1 : ZMod p) ⊗ₜ[ZMod p]
          (pbrKappa p Q Z q x)
      · apply Finset.sum_congr rfl
        intro q _
        have hh := pbrKappa_smul p φ hact Z (pbrSec φ hφ q) 1 x
        rw [pbrSec_spec, mul_one, hx' (pbrSec φ hφ q)] at hh
        rw [hh]
      · exact pbr_expand p Q Z x
  rw [← hrange]
  have hinj : Function.Injective (pbrPhi p φ Z hφ) := by
    intro u v huv
    have h := congrArg (pbrKappa p Q Z 1) huv
    simp only [pbrKappa_one_phi p φ Z hφ hker] at h
    exact h
  exact (LinearEquiv.ofInjective (pbrPhi p φ Z hφ) hinj).symm.finrank_eq

end Work.SSGRoute.E7Fin
