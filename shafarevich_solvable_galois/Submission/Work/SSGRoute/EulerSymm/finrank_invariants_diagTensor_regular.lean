import Mathlib
import Submission.Work.Shrinking.Basic
import Submission.Work.CohomologicalShrinking.Models
import Submission.Work.CohomologicalShrinking.coeff_smul_monoidAlgebra
import Submission.Work.SSGRoute.PTCore.invariantsSubmodule
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The invariants of `𝔽_p[G] ⊗ N` under the diagonal action of `G` on `𝔽_p[G] ⊗ N`

Let `G` be a finite group, `p` a prime, and `N` an `𝔽_p[G]`-module.  On the tensor product
`𝔽_p[G] ⊗_{𝔽_p} N` the group `G` acts *diagonally*, `g • (a ⊗ n) = (g • a) ⊗ (g • n)`, where
`g • a = single g 1 * a` is the left regular action on the group algebra.

The main result of this file is that the space of invariants of this action is isomorphic to `N`
(hence has the same `𝔽_p`-dimension): the element `v ∈ N` corresponds to `∑_{h : G} h ⊗ (h • v)`,
and the `1`-st coordinate functional `κ_1` is inverse to this map.

Nothing is assumed about `|G|` being invertible in `𝔽_p`, so this is *not* a Maschke-type
statement: it is the elementary computation that the "regular" tensor product has invariants `N`.

## Main result

* `Work.SSGRoute.EulerSymm.finrank_invariants_diagTensor_regular`
-/

open scoped TensorProduct

namespace Work.SSGRoute.EulerSymm

attribute [local instance] Classical.decEq

variable (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]

/-- The `k`-th coefficient functional `𝔽_p[G] → 𝔽_p`, `a ↦ a.coeff k`, as a linear map. -/
noncomputable def dtrCoeff (k : G) : MonoidAlgebra (ZMod p) G →ₗ[ZMod p] ZMod p :=
  (Finsupp.lapply k).comp
    (MonoidAlgebra.coeffLinearEquiv (ZMod p) (S := ZMod p) (M := G)).toLinearMap

lemma dtrCoeff_apply (k : G) (a : MonoidAlgebra (ZMod p) G) :
    dtrCoeff p G k a = a.coeff k := by
  simp [dtrCoeff]

lemma dtrCoeff_single_apply (k h : G) (r : ZMod p) :
    dtrCoeff p G k (MonoidAlgebra.single h r) = if h = k then r else 0 := by
  rw [dtrCoeff_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- The `𝔽_p`-scalar multiple `r • single h 1` is the basis element `single h r`. -/
lemma dtr_single_eq_smul (h : G) (r : ZMod p) :
    MonoidAlgebra.single h r = r • MonoidAlgebra.single h (1 : ZMod p) := by
  rw [MonoidAlgebra.smul_single', mul_one]

variable (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
  [SMulCommClass G (ZMod p) N]

/-- The `k`-th coordinate functional on `𝔽_p[G] ⊗ N`, `a ⊗ n ↦ (a.coeff k) • n`. -/
noncomputable def dtrKappa (k : G) :
    (MonoidAlgebra (ZMod p) G ⊗[ZMod p] N) →ₗ[ZMod p] N :=
  (TensorProduct.lid (ZMod p) N : (ZMod p) ⊗[ZMod p] N →ₗ[ZMod p] N).comp
    (LinearMap.rTensor N (dtrCoeff p G k))

lemma dtrKappa_tmul (k : G) (a : MonoidAlgebra (ZMod p) G) (n : N) :
    dtrKappa p G N k (a ⊗ₜ[ZMod p] n) = (a.coeff k) • n := by
  rw [dtrKappa, LinearMap.comp_apply, LinearMap.rTensor_tmul, dtrCoeff_apply]
  exact TensorProduct.lid_tmul n (a.coeff k)

/-- The degree-zero part of the "coordinate expansion" of `𝔽_p[G] ⊗ N`: for a pure tensor. -/
lemma dtr_expand_pure (a : MonoidAlgebra (ZMod p) G) (n : N) :
    (∑ h : G, MonoidAlgebra.single h (1 : ZMod p) ⊗ₜ[ZMod p] ((a.coeff h) • n))
      = a ⊗ₜ[ZMod p] n := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | single m r =>
      rw [Finset.sum_eq_single m]
      · rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_pos rfl,
          ← TensorProduct.smul_tmul, ← dtr_single_eq_smul]
      · intro b _ hb
        rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hb),
          zero_smul, TensorProduct.tmul_zero]
      · intro hm; exact absurd (Finset.mem_univ m) hm
  | add x y hx hy =>
      rw [MonoidAlgebra.coeff_add, TensorProduct.add_tmul]
      simp only [Finsupp.add_apply, add_smul, TensorProduct.tmul_add, Finset.sum_add_distrib,
        hx, hy]

/-- **The coordinate expansion**: every element of `𝔽_p[G] ⊗ N` is the sum of its coordinates. -/
theorem dtr_expand (x : MonoidAlgebra (ZMod p) G ⊗[ZMod p] N) :
    (∑ h : G, MonoidAlgebra.single h (1 : ZMod p) ⊗ₜ[ZMod p] (dtrKappa p G N h x)) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a n =>
      simp only [dtrKappa_tmul]
      exact dtr_expand_pure p G N a n
  | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

/-- **Equivariance of the coordinates**: the `(g * k)`-th coordinate of `g • x` is `g` applied
to the `k`-th coordinate of `x`. -/
lemma dtrKappa_smul (g k : G) (x : MonoidAlgebra (ZMod p) G ⊗[ZMod p] N) :
    dtrKappa p G N (g * k) (g • x) = g • dtrKappa p G N k x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a n =>
      rw [Work.Shrinking.diagTensor_smul_tmul, dtrKappa_tmul, dtrKappa_tmul,
        Work.CohomologicalShrinking.coeff_smul_monoidAlgebra]
      rw [show g⁻¹ * (g * k) = k from by rw [← mul_assoc, inv_mul_cancel, one_mul]]
      exact (smul_comm g (a.coeff k) n).symm
  | add x y hx hy =>
      simp only [map_add, smul_add, hx, hy]

/-- The `G`-equivariant linear map `N → 𝔽_p[G] ⊗ N`, `v ↦ ∑_{h : G} h ⊗ (h • v)`, whose image
is the space of invariants. -/
noncomputable def dtrPhi : N →ₗ[ZMod p] (MonoidAlgebra (ZMod p) G ⊗[ZMod p] N) :=
  ∑ h : G, (TensorProduct.mk (ZMod p) (MonoidAlgebra (ZMod p) G) N
      (MonoidAlgebra.single h (1 : ZMod p))).comp
    (Work.Shrinking.actLinear (p := p) (G := G) h : N →ₗ[ZMod p] N)

lemma dtrPhi_apply (v : N) :
    dtrPhi p G N v = ∑ h : G, MonoidAlgebra.single h (1 : ZMod p) ⊗ₜ[ZMod p] (h • v) := by
  simp only [dtrPhi, LinearMap.sum_apply, LinearMap.comp_apply, TensorProduct.mk_apply,
    Work.Shrinking.actLinear_apply]

lemma dtrPhi_invariant (v : N) (g : G) : g • dtrPhi p G N v = dtrPhi p G N v := by
  rw [dtrPhi_apply, Finset.smul_sum]
  have hterm : ∀ h : G,
      g • (MonoidAlgebra.single h (1 : ZMod p) ⊗ₜ[ZMod p] (h • v))
        = MonoidAlgebra.single (g * h) (1 : ZMod p) ⊗ₜ[ZMod p] ((g * h) • v) := by
    intro h
    rw [Work.Shrinking.diagTensor_smul_tmul, Work.CohomologicalShrinking.smul_monoidAlgebra,
      MonoidAlgebra.single_mul_single, mul_one, mul_smul]
  simp only [hterm]
  exact @Fintype.sum_equiv G G (MonoidAlgebra (ZMod p) G ⊗[ZMod p] N) _ _ _
    (Equiv.mulLeft g)
    (fun h : G => MonoidAlgebra.single (g * h) (1 : ZMod p) ⊗ₜ[ZMod p] ((g * h) • v))
    (fun k : G => MonoidAlgebra.single k (1 : ZMod p) ⊗ₜ[ZMod p] (k • v))
    (fun _ => rfl)

lemma dtrKappa_one_phi (v : N) : dtrKappa p G N 1 (dtrPhi p G N v) = v := by
  rw [dtrPhi_apply, map_sum]
  simp only [dtrKappa_tmul]
  rw [Finset.sum_eq_single 1]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_pos rfl, one_smul, one_smul]
  · intro b _ hb
    rw [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hb, zero_smul]
  · intro h1; exact absurd (Finset.mem_univ 1) h1

theorem finrank_invariants_diagTensor_regular (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N] :
    Module.finrank (ZMod p)
      ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
        (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) N)) =
      Module.finrank (ZMod p) N := by
  have hrange : LinearMap.range (dtrPhi p G N) =
      Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
        (MonoidAlgebra (ZMod p) G ⊗[ZMod p] N) := by
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨v, rfl⟩
      exact Work.SSGRoute.PTCore.mem_invariantsSubmodule.mpr (dtrPhi_invariant p G N v)
    · intro hx
      have hx' : ∀ g : G, g • x = x := Work.SSGRoute.PTCore.mem_invariantsSubmodule.mp hx
      refine ⟨dtrKappa p G N 1 x, ?_⟩
      rw [dtrPhi_apply]
      trans ∑ h : G, MonoidAlgebra.single h (1 : ZMod p) ⊗ₜ[ZMod p] (dtrKappa p G N h x)
      · apply Finset.sum_congr rfl
        intro h _
        have hh := dtrKappa_smul p G N h 1 x
        rw [mul_one, hx' h] at hh
        rw [hh]
      · exact dtr_expand p G N x
  rw [← hrange]
  have hinj : Function.Injective (dtrPhi p G N) := by
    intro u v huv
    have h := congrArg (dtrKappa p G N 1) huv
    simp only [dtrKappa_one_phi] at h
    exact h
  exact (LinearEquiv.ofInjective (dtrPhi p G N) hinj).symm.finrank_eq

end Work.SSGRoute.EulerSymm
