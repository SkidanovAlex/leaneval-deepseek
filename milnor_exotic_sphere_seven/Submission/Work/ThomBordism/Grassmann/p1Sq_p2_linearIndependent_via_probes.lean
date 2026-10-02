import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.SignatureBordism.Rationalisation
import Submission.Work.Projective.Basic
import Submission.Work.ThomBordism.Grassmann.LowDegree.p1SqProbe
import Submission.Work.ThomBordism.Grassmann.LowDegree.P2Stabilisation
import Submission.Work.ThomBordism.Grassmann.InclCrux.gaugeToProbe
import Submission.Work.ThomBordism.Grassmann.InclCrux.p2GaugeSnap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# `p₁(γ)²` and `p₂(γ)` are linearly independent in `H⁸(G̃r_k(ℝ^{k+m});ℚ)`

Target (`Work.ThomBordism.Grassmann.p1Sq_p2_linearIndependent_via_probes`): for `k, m ≥ 10` the
two classes `p1SqRat k m = 1 ⊗ p₁(γ)²` and `p2Rat k m = 1 ⊗ p₂(γ)` of the rationalised degree-`8`
cohomology of the oriented Grassmannian are linearly independent over `ℚ`.

## The method: two probes

A *probe* is a continuous map `σ : X → G̃r_k(ℝ^{k+m})` from a test space `X`; pulling the classes
`p₁(γ)²`, `p₂(γ)` back along it produces linear functionals on the two-dimensional (in the stable
range) space `H⁸(G;ℚ)`.  Two probes whose pulled-back classes give linearly independent functionals
prove the independence:

* the **`p₁²`-probe**: a rank-`2` oriented bundle on a closed `8`-manifold (so that `p₂` pulls back
  to `0`, the top Pontryagin class of a bundle of rank `< 4` being trivial), whose `p₁`-square pulls
  back to a non-torsion class — it kills the coefficient of `p₁²`.  The witness, over `ℂP⁴`, is
  `Work.ThomBordism.Grassmann.LowDegree.p1SqProbe`;
* the **`p₂`-probe**: a rank-`4` oriented bundle on a closed `8`-manifold whose `p₂` pulls back to a
  non-torsion class — it then kills the coefficient of `p₂`.  The witness is
  `Work.ThomBordism.Grassmann.LowDegree.p2ProbeCP4_of_base` applied to the base case
  `InclCrux.p2ProbeBase8_of_gauge InclCrux.gaugeIso` at `(k,m) = (4,8)`; the `p₂` of the explicit
  rank-`4` bundle is `±c₄((O(1)⊕O(-1))²) ≠ 0` by
  `Work.ThomBordism.Grassmann.c4_tautSum4_CP4_rat_ne_zero`.

## Content of this file

* `ratPullback`, `ratPullback_tmul` — the rationalisation of a pullback as a `ℚ`-linear map and
  its value on the pure tensors `1 ⊗ x`;
* `eq_zero_left_of_probe`, `eq_zero_right_of_probe`, `linearIndependent_of_probes`,
  `linearIndependent_of_probe_pair` — **the assembly**, pure `ℚ`-linear algebra, reducing the
  target to the two probes;
* `p1Sq_p2_linearIndependent_via_probes` — the target, from the two probes above.
-/

namespace Work.ThomBordism.Grassmann

open scoped TensorProduct

noncomputable section

/-! ## A field-scalar helper -/

/-- In a vector space over a field, a multiple of a nonzero vector vanishes only for the zero
scalar.  (Stated by hand to avoid the `NoZeroSMulDivisors` instance search on the tensor product.) -/
theorem smul_eq_zero_of_ne_zero {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {q : F}
    {v : V} (h : q • v = 0) (hv : v ≠ 0) : q = 0 := by
  by_contra hq
  refine hv ?_
  calc v = (q⁻¹ * q) • v := by rw [inv_mul_cancel₀ hq, one_smul]
    _ = q⁻¹ • (q • v) := by rw [mul_smul]
    _ = 0 := by rw [h, smul_zero]

/-! ## The rationalised pullback -/

/-- **The rationalisation of the pullback along a probe** as a `ℚ`-linear map
`H^n(G;ℤ) ⊗ ℚ → H^n(X;ℤ) ⊗ ℚ`. -/
noncomputable def ratPullback {n : ℕ} {X : Type} [TopologicalSpace X] {k m : ℕ}
    (σ : C(X, OG k m)) :
    (ℚ ⊗[ℤ] Work.Thom.Coh ℤ n (OG k m)) →ₗ[ℚ] (ℚ ⊗[ℤ] Work.Thom.Coh ℤ n X) :=
  { toFun := TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) ((Work.Thom.CohMap σ ℤ n).hom)
    map_add' := map_add _
    map_smul' := by
      intro q x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a y =>
          rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
            TensorProduct.smul_tmul']
          simp
      | add x y hx hy => simp only [smul_add, map_add, hx, hy] }

/-- **The value of the rationalised pullback on a pure tensor**: `1 ⊗ x ↦ 1 ⊗ σ^* x`. -/
theorem ratPullback_tmul {n : ℕ} {X : Type} [TopologicalSpace X] {k m : ℕ}
    (σ : C(X, OG k m)) (x : Work.Thom.Coh ℤ n (OG k m)) :
    ratPullback σ ((1 : ℚ) ⊗ₜ[ℤ] x)
      = (1 : ℚ) ⊗ₜ[ℤ] ((Work.Thom.CohMap σ ℤ n).hom x) := by
  show TensorProduct.map (LinearMap.id : ℚ →ₗ[ℤ] ℚ) ((Work.Thom.CohMap σ ℤ n).hom)
      ((1 : ℚ) ⊗ₜ[ℤ] x) = _
  rw [TensorProduct.map_tmul]
  rfl

/-! ## The analytic heart: a pair of probes kills a linear relation -/

/-- **A probe whose `p₁²`-pullback is non-torsion and whose `p₂`-pullback vanishes kills the
coefficient of `p₁²`.** -/
theorem eq_zero_left_of_probe (k m : ℕ) {X : Type} [TopologicalSpace X] (σ : C(X, OG k m))
    (h1 : (1 : ℚ) ⊗ₜ[ℤ] ((Work.Thom.CohMap σ ℤ 8).hom (p1Sq k m)) ≠ 0)
    (h2 : (1 : ℚ) ⊗ₜ[ℤ] ((Work.Thom.CohMap σ ℤ 8).hom (p2 k m)) = 0)
    {a b : ℚ} (h : a • p1SqRat k m + b • p2Rat k m = 0) : a = 0 := by
  have happ : ratPullback σ (a • p1SqRat k m + b • p2Rat k m) = 0 := by
    rw [h, map_zero]
  rw [map_add, map_smul, map_smul] at happ
  rw [show p1SqRat k m = (1 : ℚ) ⊗ₜ[ℤ] (p1Sq k m) from rfl, ratPullback_tmul,
    show p2Rat k m = (1 : ℚ) ⊗ₜ[ℤ] (p2 k m) from rfl, ratPullback_tmul, h2, smul_zero,
    add_zero] at happ
  exact smul_eq_zero_of_ne_zero happ h1

/-- **A probe whose `p₂`-pullback is non-torsion kills the coefficient of `p₂`** — applied after
`eq_zero_left_of_probe` has disposed of the other coefficient. -/
theorem eq_zero_right_of_probe (k m : ℕ) {Y : Type} [TopologicalSpace Y] (τ : C(Y, OG k m))
    (h3 : (1 : ℚ) ⊗ₜ[ℤ] ((Work.Thom.CohMap τ ℤ 8).hom (p2 k m)) ≠ 0)
    {a b : ℚ} (ha : a = 0) (hrel : a • p1SqRat k m + b • p2Rat k m = 0) : b = 0 := by
  have happ : ratPullback τ (a • p1SqRat k m + b • p2Rat k m) = 0 := by
    rw [hrel, map_zero]
  rw [map_add, map_smul, map_smul] at happ
  rw [show p1SqRat k m = (1 : ℚ) ⊗ₜ[ℤ] (p1Sq k m) from rfl, ratPullback_tmul,
    show p2Rat k m = (1 : ℚ) ⊗ₜ[ℤ] (p2 k m) from rfl, ratPullback_tmul, ha, zero_smul,
    zero_add] at happ
  exact smul_eq_zero_of_ne_zero happ h3

/-! ## The assembly -/

/-- **Two probes prove the independence.** -/
theorem linearIndependent_of_probes (k m : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (σ : C(X, OG k m)) (τ : C(Y, OG k m))
    (h1 : (1 : ℚ) ⊗ₜ[ℤ] ((Work.Thom.CohMap σ ℤ 8).hom (p1Sq k m)) ≠ 0)
    (h2 : (1 : ℚ) ⊗ₜ[ℤ] ((Work.Thom.CohMap σ ℤ 8).hom (p2 k m)) = 0)
    (h3 : (1 : ℚ) ⊗ₜ[ℤ] ((Work.Thom.CohMap τ ℤ 8).hom (p2 k m)) ≠ 0) :
    LinearIndependent ℚ ![p1SqRat k m, p2Rat k m] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  have ha : a = 0 := eq_zero_left_of_probe k m σ h1 h2 h
  exact ⟨ha, eq_zero_right_of_probe k m τ h3 ha h⟩

end

end Work.ThomBordism.Grassmann

/-! ## The end-to-end assembly from the two probes

The remaining inputs are the existence of the two probes; they are delegated to sibling modules
(`probeCP4_a_part`, `probeCP4_p2_ne_zero_of_c4`).  The lemma below records the *exact* interface:
what the final proof of `p1Sq_p2_linearIndependent_via_probes` has to supply. -/

namespace Work.ThomBordism.Grassmann

/-- **The end-to-end assembly.**  Given the two probes (a `p₁²`-probe whose `p₂`-pullback vanishes
and a `p₂`-probe), the independence follows. -/
theorem linearIndependent_of_probe_pair (k m : ℕ)
    (hA : ∃ σ : C(Work.Projective.CP 4, OG k m),
      (1 : ℚ) ⊗ₜ[ℤ] ((Work.Thom.CohMap σ ℤ 8).hom (p1Sq k m)) ≠ 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] ((Work.Thom.CohMap σ ℤ 8).hom (p2 k m)) = 0)
    (hB : ∃ τ : C(Work.Projective.CP 4, OG k m),
      (1 : ℚ) ⊗ₜ[ℤ] ((Work.Thom.CohMap τ ℤ 8).hom (p2 k m)) ≠ 0) :
    LinearIndependent ℚ ![p1SqRat k m, p2Rat k m] := by
  obtain ⟨σ, h1, h2⟩ := hA
  obtain ⟨τ, h3⟩ := hB
  exact linearIndependent_of_probes k m σ τ h1 h2 h3

end Work.ThomBordism.Grassmann

/-! ## The target -/

namespace Work.ThomBordism.Grassmann

open scoped TensorProduct

/-- **`p₁(γ)²` and `p₂(γ)` are linearly independent in `H⁸(G̃r_k(ℝ^{k+m});ℚ)` for `k, m ≥ 10`**,
by the two probes of `LowDegree.p1SqProbe` and `LowDegree.p2ProbeCP4_of_base`
(`hA`, the rank-two `ℂP⁴`-probe, and `hB`, the rank-four `ℂP⁴`-probe). -/
theorem p1Sq_p2_linearIndependent_via_probes (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    LinearIndependent ℚ ![Work.ThomBordism.Grassmann.p1SqRat k m,
      Work.ThomBordism.Grassmann.p2Rat k m] := by
  exact linearIndependent_of_probe_pair k m
    (LowDegree.p1SqProbe k m (by omega) (by omega))
    (LowDegree.p2ProbeCP4_of_base
      (InclCrux.p2ProbeBase8_of_gauge InclCrux.gaugeIso) k m (by omega) (by omega))

end Work.ThomBordism.Grassmann
