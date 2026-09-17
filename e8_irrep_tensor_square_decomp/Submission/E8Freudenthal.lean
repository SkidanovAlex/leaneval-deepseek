import Submission.E8Casimir
import Submission.E8WInvariance
import Submission.E8Character
import Submission.Commons.Algebra.Lie.SerreConstruction.killingForm_SerreH
import Submission.Commons.Algebra.Lie.SerreConstruction.killingForm_cartanDual

/-!
# The Freudenthal recursion for the character of `L(ω₁+ω₈) = V ⧸ N`

This file proves hypothesis (d) of `Submission.E8Character.eq_of_freudenthal` for the actual
multiplicity function `mul ν := Module.finrank ℂ ↥(Lwt N ν)` of the irreducible quotient
`L = V ⧸ N` of the Verma module.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators Matrix
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [-instance] Submission.Enveloping.instLieRingModuleE8
attribute [-instance] Submission.Enveloping.instLieModuleE8

namespace Submission.E8Freudenthal

open Submission.E8WeightSpaces Submission.VermaWeight
open Submission.E8WInvariance (endU_smul endU_zsmul endU_pow)
open Submission.E8Casimir
open Commons.Algebra.Lie Commons.Algebra.Lie.SerreConstruction Commons.LinearAlgebra.Matrix.Cartan

/-- The Lie algebra `e₈(ℂ)`. -/
abbrev L8 : Type := LieAlgebra.e₈ ℂ

/-! ## The weight shift for an arbitrary root vector -/

/-- **The weight of `ι x · y` for `x ∈ e8W α` and `y` of weight `μ`.** -/
lemma endU_iota_mem_Lwt (N : Submodule U V) (α : Fin 8 → ℤ) {x : L8} (hx : x ∈ e8W α)
    {μ : Fin 8 → ℤ} {y : V ⧸ N} (hy : y ∈ Lwt N μ) :
    endU N (UniversalEnvelopingAlgebra.ι ℂ x) y ∈ Lwt N (μ + α) := by
  rw [mem_Lwt_iff] at hy ⊢
  intro i
  have hy' : Submission.E8Weights.h i • y = ((μ i : ℤ) : ℂ) • y := by
    simpa only [endU_apply] using hy i
  have hb : ⁅SerreH i, x⁆ = ((α i : ℤ) : ℂ) • x := mem_e8W_iff.mp hx i
  have hrel : Submission.E8Weights.h i * UniversalEnvelopingAlgebra.ι ℂ x
      = UniversalEnvelopingAlgebra.ι ℂ x * Submission.E8Weights.h i
        + UniversalEnvelopingAlgebra.ι ℂ ⁅SerreH i, x⁆ := by
    change UniversalEnvelopingAlgebra.ι ℂ (SerreH i) * UniversalEnvelopingAlgebra.ι ℂ x
      = UniversalEnvelopingAlgebra.ι ℂ x * UniversalEnvelopingAlgebra.ι ℂ (SerreH i)
        + UniversalEnvelopingAlgebra.ι ℂ ⁅SerreH i, x⁆
    rw [← Submission.Enveloping.ι_commutator_eq]
    abel
  rw [endU_apply, endU_apply, ← mul_smul, hrel, add_smul, mul_smul, hy',
    Submission.Enveloping.module_smul_comm_scalar (R := ℂ) (L := LieAlgebra.e₈ ℂ)
      (UniversalEnvelopingAlgebra.ι ℂ x) ((μ i : ℤ) : ℂ) y,
    hb, map_smul, IsScalarTower.smul_assoc, ← add_smul]
  congr 1
  simp only [Pi.add_apply, Int.cast_add]

/-! ## The action of a Cartan element on a weight space -/

/-- **A Cartan element acts on a weight space by the `κ`-dual functional.** -/
theorem endU_iota_cartan_apply (N : Submodule U V) {z : L8} (hz : z ∈ e8W 0)
    (ν : Fin 8 → ℤ) {y : V ⧸ N} (hy : y ∈ Lwt N ν) :
    endU N (UniversalEnvelopingAlgebra.ι ℂ z) y = (K (wdual ν) z) • y := by
  have hspan : z ∈ Submodule.span ℂ (Set.range SerreH) := by
    rw [← e8W_zero_eq_span_SerreH]; exact hz
  have key : ∀ z ∈ Submodule.span ℂ (Set.range SerreH),
      endU N (UniversalEnvelopingAlgebra.ι ℂ z) y = (K (wdual ν) z) • y := by
    intro z hz'
    induction hz' using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        rw [K_wdual_SerreH]
        exact mem_Lwt_iff.mp hy i
    | zero => simp
    | add a b _ _ ha hb =>
        rw [map_add, endU_add, LinearMap.add_apply, ha, hb, map_add, add_smul]
    | smul c a _ ha =>
        rw [map_smul, endU_smul, LinearMap.smul_apply, ha, map_smul, smul_assoc]
  exact key z hspan

/-- **The coroot `(α_k)∨` acts on the weight space `L_ν` by `(ν, α_k)_κ`.** -/
theorem endU_iota_wdual_pR_apply (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ)
    {y : V ⧸ N} (hy : y ∈ Lwt N ν) :
    endU N (UniversalEnvelopingAlgebra.ι ℂ (wdual (pR k))) y
      = (K (wdual ν) (wdual (pR k))) • y :=
  endU_iota_cartan_apply N (wdual_mem_cartan (pR k)) ν hy

/-! ## Cyclicity and the Casimir eigenvalue on the highest weight vector -/

open Submission.E8Character

/-- The Cartan matrix of `E₈`. -/
abbrev A8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

abbrev E8invM : Matrix (Fin 8) (Fin 8) ℤ :=
  Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv

/-- The integral highest weight `ω₁ + ω₈`. -/
abbrev lamZ : Fin 8 → ℤ := fun i => if i = 0 then 1 else if i = 7 then 1 else 0

lemma wtZ_eq (m : Fin 8 → ℕ) :
    wtZ m = lamZ - A8 *ᵥ (fun a => (m a : ℤ)) := by
  funext i
  have h1 : (∑ a : Fin 8, (m a : ℤ) * A8 i a)
      = (∑ a : Fin 8, A8 i a * (m a : ℤ)) :=
    Finset.sum_congr rfl fun a _ => mul_comm _ _
  have h2 : ((if i = 0 then (1 : ℤ) else 0) + (if i = 7 then 1 else 0))
      = (if i = 0 then 1 else if i = 7 then 1 else 0) := by
    by_cases h0 : i = 0
    · subst h0
      have h07 : ¬ ((0 : Fin 8) = 7) := by decide
      simp [h07]
    · by_cases h7 : i = 7
      · subst h7
        have h70 : ¬ ((7 : Fin 8) = 0) := by decide
        simp [h70]
      · simp [h0, h7]
  simp only [wtZ, lamZ, Matrix.mulVec, dotProduct, Pi.sub_apply]
  rw [h1, h2]

lemma wtZ_zero : wtZ (0 : Fin 8 → ℕ) = lamZ := by
  rw [wtZ_eq]
  have h : (fun a : Fin 8 => (((0 : Fin 8 → ℕ) a) : ℤ)) = 0 := by funext a; simp
  rw [h, Matrix.mulVec_zero, sub_zero]

lemma wdual_lamZ (i : Fin 8) :
    ((lamZ i : ℤ) : ℂ) = Submission.E8Weights.omegaOnePlusOmegaEight i := by
  fin_cases i <;> simp [lamZ, Submission.E8Weights.omegaOnePlusOmegaEight]

/-- The highest weight vector `vbar` lies in the `λ`-weight space. -/
lemma vbar_mem_Lwt_lam (N : Submodule U V) : vbar N ∈ Lwt N lamZ := by
  have hv : (mkQc N v) ∈ Lw N 0 :=
    Submodule.mem_map.mpr ⟨v, v_mem_Wm_zero, rfl⟩
  have h := Lw_le_Lwt N 0 hv
  rwa [wtZ_zero] at h

/-- A raising root vector annihilates the highest weight vector of `V ⧸ N`. -/
lemma eRoot_smul_vbar (N : Submodule U V) (k : Fin 120) :
    endU N (UniversalEnvelopingAlgebra.ι ℂ (eRoot k)) (vbar N) = 0 := by
  by_contra hne
  have hmem := endU_iota_mem_Lwt N (pR k) (eRoot_mem k) (vbar_mem_Lwt_lam N)
  obtain ⟨m, hm⟩ := exists_wtZ_of_mem_Lwt N hmem hne
  have hp : pR k = -(A8 *ᵥ (fun a => (m a : ℤ))) := by
    have h := hm
    rw [wtZ_eq] at h
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at hi ⊢
    linarith
  have hneg : (E8invM *ᵥ pR k) = -(fun j => (m j : ℤ)) := by
    rw [hp, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv_mul_E8, Matrix.one_mulVec]
  have hzero : ∀ j, m j = 0 := by
    intro j
    have h1 : 0 ≤ (E8invM *ᵥ pR k) j := posCon_pR k j
    have h2 : 0 ≤ (m j : ℤ) := Int.natCast_nonneg _
    have h3 := congrFun hneg j
    simp only [Pi.neg_apply] at h3
    omega
  exact pR_ne_zero k (by
    rw [← mulVec_coords (pR k)]
    have hz : coords (pR k) = 0 := by
      funext j
      have h3 : coords (pR k) j = -((m j : ℤ)) := congrFun hneg j
      rw [h3, hzero j]
      simp
    rw [hz, Matrix.mulVec_zero])


/-- The quotient `V ⧸ N` is cyclically generated by `vbar`. -/
lemma cyclic_vbar (N : Submodule U V) (m : V ⧸ N) : ∃ u : U, u • vbar N = m := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective N m
  obtain ⟨u, hu⟩ := Submission.VermaNonzero.cyclic_V Submission.VermaWeight.lam z
  exact ⟨u, by rw [vbar, ← Submodule.Quotient.mk_smul]; exact congrArg Submodule.Quotient.mk hu⟩

open UniversalEnvelopingAlgebra in
/-- **The Casimir eigenvalue on the highest weight vector** of `V ⧸ N`. -/
theorem Omega_smul_vbar (N : Submodule U V) :
    Omega • (vbar N) = (K (wdual lamZ) (wdual (lamZ + twoRho))) • (vbar N) := by
  have hv : vbar N ∈ Lwt N lamZ := vbar_mem_Lwt_lam N
  have hH : ∀ i : Fin 8, endU N (ι ℂ (SerreH i)) (vbar N) = ((lamZ i : ℤ) : ℂ) • (vbar N) :=
    fun i => mem_Lwt_iff.mp hv i
  have hcart : ∀ i : Fin 8, endU N (ι ℂ (((hdual i : H) : L8))) (vbar N)
      = (K (wdual lamZ) (((hdual i : H) : L8))) • (vbar N) :=
    fun i => endU_iota_cartan_apply N (hdual_mem_e8W_zero i) lamZ hv
  have hterm : ∀ a : Idx, (ι ℂ (bIdx a) * ι ℂ (bDual a)) • (vbar N)
      = endU N (ι ℂ (bIdx a)) (endU N (ι ℂ (bDual a)) (vbar N)) := by
    intro a
    rw [mul_smul, endU_apply, endU_apply]
  have hΩ : Omega • (vbar N)
      = (∑ i : Fin 8, endU N (ι ℂ (SerreH i)) (endU N (ι ℂ (((hdual i : H) : L8))) (vbar N)))
        + (∑ k : Fin 120, endU N (ι ℂ (eRoot k)) (endU N (ι ℂ (fRoot k)) (vbar N)))
        + (∑ k : Fin 120, endU N (ι ℂ (fRoot k)) (endU N (ι ℂ (eRoot k)) (vbar N))) := by
    rw [Omega, Finset.sum_smul, Finset.sum_congr rfl (fun a _ => hterm a)]
    simp only [bIdx_apply, bFam_inl, bFam_inr_inl, bFam_inr_inr, bDual_inl, bDual_inr_inl,
      bDual_inr_inr, Fintype.sum_sum_type]
    abel
  -- the `H`-block
  have hHblk : (∑ i : Fin 8, endU N (ι ℂ (SerreH i))
        (endU N (ι ℂ (((hdual i : H) : L8))) (vbar N)))
      = (K (wdual lamZ) (wdual lamZ)) • (vbar N) := by
    have h2 : ∀ i : Fin 8, endU N (ι ℂ (SerreH i))
          (endU N (ι ℂ (((hdual i : H) : L8))) (vbar N))
        = (K (wdual lamZ) (((hdual i : H) : L8)) * ((lamZ i : ℤ) : ℂ)) • (vbar N) := by
      intro i
      rw [hcart i, LinearMap.map_smul, hH i, smul_smul]
    have hsum : ∀ z : L8,
        (∑ i : Fin 8, K z (((hdual i : H) : L8)) * ((lamZ i : ℤ) : ℂ)) = K z (wdual lamZ) := by
      intro z
      rw [wdual_eq_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    have hsm : ∀ (c : Fin 8 → ℂ),
        (∑ i : Fin 8, c i • (vbar N)) = (∑ i : Fin 8, c i) • (vbar N) :=
      fun c => Finset.sum_smul.symm
    rw [Finset.sum_congr rfl (fun i _ => h2 i), hsm]
    rw [hsum]
  -- the `e · f`-block
  have hEFblk : (∑ k : Fin 120, endU N (ι ℂ (eRoot k)) (endU N (ι ℂ (fRoot k)) (vbar N)))
      = (K (wdual lamZ) (wdual twoRho)) • (vbar N) := by
    have h1 : ∀ k : Fin 120, endU N (ι ℂ (eRoot k)) (endU N (ι ℂ (fRoot k)) (vbar N))
        = (K (wdual lamZ) (wdual (pR k))) • (vbar N) := by
      intro k
      have hcom : ι ℂ (eRoot k) * ι ℂ (fRoot k)
          = ι ℂ (fRoot k) * ι ℂ (eRoot k) + ι ℂ (wdual (pR k)) := by
        have h := Submission.Enveloping.ι_commutator_eq (R := ℂ) (L := L8) (eRoot k) (fRoot k)
        rw [eRoot_comm_fRoot k] at h
        rw [← h]
        abel
      have h2 : endU N (ι ℂ (fRoot k)) (endU N (ι ℂ (eRoot k)) (vbar N)) = 0 := by
        rw [eRoot_smul_vbar N k, map_zero]
      have h3 : endU N (ι ℂ (wdual (pR k))) (vbar N)
          = (K (wdual lamZ) (wdual (pR k))) • (vbar N) :=
        endU_iota_cartan_apply N (wdual_mem_cartan (pR k)) lamZ hv
      calc endU N (ι ℂ (eRoot k)) (endU N (ι ℂ (fRoot k)) (vbar N))
          = endU N (ι ℂ (eRoot k) * ι ℂ (fRoot k)) (vbar N) := by
            rw [endU_mul, Module.End.mul_apply]
        _ = endU N (ι ℂ (fRoot k) * ι ℂ (eRoot k) + ι ℂ (wdual (pR k))) (vbar N) := by
            rw [hcom]
        _ = endU N (ι ℂ (fRoot k) * ι ℂ (eRoot k)) (vbar N)
              + endU N (ι ℂ (wdual (pR k))) (vbar N) := by
            rw [endU_add, LinearMap.add_apply]
        _ = (K (wdual lamZ) (wdual (pR k))) • (vbar N) := by
            rw [endU_mul, Module.End.mul_apply, h2, h3, zero_add]
    calc ∑ k : Fin 120, endU N (ι ℂ (eRoot k)) (endU N (ι ℂ (fRoot k)) (vbar N))
        = ∑ k : Fin 120, (K (wdual lamZ) (wdual (pR k))) • (vbar N) :=
          Finset.sum_congr rfl fun k _ => h1 k
      _ = (∑ k : Fin 120, K (wdual lamZ) (wdual (pR k))) • (vbar N) := by
          rw [Finset.sum_smul]
      _ = (K (wdual lamZ) (wdual twoRho)) • (vbar N) := by
          congr 1
          rw [← wdual_sum_pR, map_sum]
  -- the `f · e`-block vanishes
  have hFEblk : (∑ k : Fin 120, endU N (ι ℂ (fRoot k)) (endU N (ι ℂ (eRoot k)) (vbar N))) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [eRoot_smul_vbar N k, map_zero]
  rw [hΩ, hHblk, hEFblk, hFEblk, add_zero, ← add_smul]
  congr 1
  rw [wdual_add, map_add]


/-! ## The weight spaces are finite-dimensional -/

/-- Every weight space of `L = V ⧸ N` is finite-dimensional. -/
instance instFiniteLwt (N : Submodule U V) (ν : Fin 8 → ℤ) : Module.Finite ℂ ↥(Lwt N ν) := by
  classical
  by_cases h : Lwt N ν = ⊥
  · rw [h, ← Submodule.span_empty (R := ℂ) (M := V ⧸ N)]
    exact Module.Finite.span_of_finite ℂ (Set.finite_empty)
  · obtain ⟨x, hx, hx0⟩ := (Lwt N ν).ne_bot_iff.mp h
    obtain ⟨m, hm⟩ := exists_wtZ_of_mem_Lwt N hx hx0
    rw [hm, ← Lw_eq_Lwt]
    exact Lw_finite N m


/-! ## The trace of the Casimir on a weight space -/

/-- The multiplicity of the weight `ν` in `L = V ⧸ N`. -/
noncomputable abbrev dmul (N : Submodule U V) (ν : Fin 8 → ℤ) : ℕ :=
  Module.finrank ℂ ↥(Lwt N ν)

/-- The Casimir eigenvalue. -/
noncomputable def cas : ℂ := K (wdual lamZ) (wdual (lamZ + twoRho))

/-- The Casimir acts by the scalar `cas` on all of `R = V ⧸ N`. -/
theorem Omega_smul_eq (N : Submodule U V) (x : V ⧸ N) : Omega • x = cas • x :=
  Omega_smul_of_cyclic (v := vbar N) (cyclic_vbar N) cas (Omega_smul_vbar N) x

open UniversalEnvelopingAlgebra in
/-- The endomorphism of the weight space `Lwt N ν` induced by an element of `U(e₈)`. -/
noncomputable def restU (N : Submodule U V) (ν : Fin 8 → ℤ) (u : U)
    (h : ∀ x ∈ Lwt N ν, endU N u x ∈ Lwt N ν) : ↥(Lwt N ν) →ₗ[ℂ] ↥(Lwt N ν) :=
  LinearMap.restrict (endU N u) h

open UniversalEnvelopingAlgebra in
/-- The restriction of the Casimir to a weight space. -/
noncomputable def restOmega (N : Submodule U V) (ν : Fin 8 → ℤ) : ↥(Lwt N ν) →ₗ[ℂ] ↥(Lwt N ν) :=
  LinearMap.restrict (endU N Omega) (fun _x hx => by
    rw [endU_apply, Omega_smul_eq N _x]
    exact Submodule.smul_mem _ _ hx)

open UniversalEnvelopingAlgebra in
/-- The trace of the Casimir on a weight space. -/
noncomputable def traceOmega (N : Submodule U V) (ν : Fin 8 → ℤ) : ℂ :=
  LinearMap.trace ℂ ↥(Lwt N ν) (restOmega N ν)

open UniversalEnvelopingAlgebra in
lemma traceOmega_eq (N : Submodule U V) (ν : Fin 8 → ℤ) :
    traceOmega N ν = cas * (dmul N ν : ℂ) := by
  have h : restOmega N ν = cas • (1 : Module.End ℂ ↥(Lwt N ν)) := by
    ext x
    rw [LinearMap.smul_apply, Module.End.one_apply]
    show endU N Omega (x : V ⧸ N) = cas • (x : V ⧸ N)
    rw [endU_apply]
    exact Omega_smul_eq N (x : V ⧸ N)
  rw [traceOmega, h, map_smul, LinearMap.trace_one, smul_eq_mul]

/-! ## The restricted root operators and their traces -/

open UniversalEnvelopingAlgebra in
/-- The raising operator `e_α` restricted to the weight spaces. -/
noncomputable def Eop (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) :
    ↥(Lwt N ν) →ₗ[ℂ] ↥(Lwt N (ν + pR k)) :=
  LinearMap.restrict (endU N (ι ℂ (eRoot k)))
    (fun _x hx => endU_iota_mem_Lwt N (pR k) (eRoot_mem k) hx)

open UniversalEnvelopingAlgebra in
/-- The lowering operator `f_α` restricted to the weight spaces. -/
noncomputable def Fop (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) :
    ↥(Lwt N (ν + pR k)) →ₗ[ℂ] ↥(Lwt N ν) :=
  LinearMap.restrict (endU N (ι ℂ (fRoot k)))
    (fun _x hx => by
      have h := endU_iota_mem_Lwt N (-(pR k)) (fRoot_mem k) hx
      rwa [add_assoc, add_neg_cancel, add_zero] at h)

open UniversalEnvelopingAlgebra in
lemma FE_mem (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) {x : V ⧸ N}
    (hx : x ∈ Lwt N ν) :
    ((endU N (ι ℂ (fRoot k))) * (endU N (ι ℂ (eRoot k)))) x ∈ Lwt N ν := by
  rw [Module.End.mul_apply]
  have h := endU_iota_mem_Lwt N (-(pR k)) (fRoot_mem k)
    (endU_iota_mem_Lwt N (pR k) (eRoot_mem k) hx)
  rwa [add_assoc, add_neg_cancel, add_zero] at h

open UniversalEnvelopingAlgebra in
lemma EF_mem (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) {x : V ⧸ N}
    (hx : x ∈ Lwt N ν) :
    ((endU N (ι ℂ (eRoot k))) * (endU N (ι ℂ (fRoot k)))) x ∈ Lwt N ν := by
  rw [Module.End.mul_apply]
  have h := endU_iota_mem_Lwt N (pR k) (eRoot_mem k)
    (endU_iota_mem_Lwt N (-(pR k)) (fRoot_mem k) hx)
  rwa [add_assoc, neg_add_cancel, add_zero] at h

open UniversalEnvelopingAlgebra in
/-- The restriction of `f_α ∘ e_α` to a weight space. -/
noncomputable def FEmap (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) :
    ↥(Lwt N ν) →ₗ[ℂ] ↥(Lwt N ν) :=
  LinearMap.restrict ((endU N (ι ℂ (fRoot k))) * (endU N (ι ℂ (eRoot k))))
    (fun _x hx => FE_mem N k ν hx)

open UniversalEnvelopingAlgebra in
/-- The restriction of `e_α ∘ f_α` to a weight space. -/
noncomputable def EFmap (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) :
    ↥(Lwt N ν) →ₗ[ℂ] ↥(Lwt N ν) :=
  LinearMap.restrict ((endU N (ι ℂ (eRoot k))) * (endU N (ι ℂ (fRoot k))))
    (fun _x hx => EF_mem N k ν hx)

open UniversalEnvelopingAlgebra in
lemma FEmap_eq (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) :
    FEmap N k ν = (Fop N k ν).comp (Eop N k ν) := by
  ext x; rfl

open UniversalEnvelopingAlgebra in
lemma EFmap_eq (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) :
    EFmap N k (ν + pR k) = (Eop N k ν).comp (Fop N k ν) := by
  ext x; rfl

open UniversalEnvelopingAlgebra in
/-- The commutator identity `[e_α, f_α] = (α∨)` on a weight space. -/
lemma EFmap_sub_FEmap (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) :
    EFmap N k ν - FEmap N k ν
      = (K (wdual ν) (wdual (pR k))) • (1 : Module.End ℂ ↥(Lwt N ν)) := by
  have hcomm : (endU N (ι ℂ (eRoot k))) * (endU N (ι ℂ (fRoot k)))
      - (endU N (ι ℂ (fRoot k))) * (endU N (ι ℂ (eRoot k)))
      = endU N (ι ℂ (wdual (pR k))) := by
    rw [← endU_mul, ← endU_mul, ← endU_sub]
    congr 1
    exact (Submission.Enveloping.ι_commutator_eq (R := ℂ) (L := L8) (eRoot k) (fRoot k)).trans
      (by rw [eRoot_comm_fRoot k])
  ext x
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  have hx : (x : V ⧸ N) ∈ Lwt N ν := x.2
  have h := endU_iota_cartan_apply N (wdual_mem_cartan (pR k)) ν hx
  have e1 : (↑((EFmap N k ν) x) : V ⧸ N)
      = ((endU N (ι ℂ (eRoot k))) * (endU N (ι ℂ (fRoot k)))) (x : V ⧸ N) := rfl
  have e2 : (↑((FEmap N k ν) x) : V ⧸ N)
      = ((endU N (ι ℂ (fRoot k))) * (endU N (ι ℂ (eRoot k)))) (x : V ⧸ N) := rfl
  rw [show (↑(EFmap N k ν x - FEmap N k ν x) : V ⧸ N)
        = (↑((EFmap N k ν) x) : V ⧸ N) - ↑((FEmap N k ν) x)
      from map_sub (Submodule.subtype (Lwt N ν)) _ _,
    e1, e2, ← LinearMap.sub_apply, hcomm, endU_apply]
  exact h

open UniversalEnvelopingAlgebra in
/-- The trace of `f_α ∘ e_α` on a weight space. -/
noncomputable def Str (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) : ℂ :=
  LinearMap.trace ℂ ↥(Lwt N ν) (FEmap N k ν)

open UniversalEnvelopingAlgebra in
/-- The trace of `e_α ∘ f_α` on a weight space. -/
noncomputable def Ttr (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) : ℂ :=
  LinearMap.trace ℂ ↥(Lwt N ν) (EFmap N k ν)

open UniversalEnvelopingAlgebra in
/-- The trace-cyclicity identity. -/
lemma Str_eq_Ttr (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) :
    Str N k ν = Ttr N k (ν + pR k) := by
  rw [Str, FEmap_eq, Ttr, EFmap_eq]
  exact LinearMap.trace_comp_comm' (Eop N k ν) (Fop N k ν)

open UniversalEnvelopingAlgebra in
/-- **The step relation for the trace `S`.** -/
lemma Str_step (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) :
    Str N k ν = Str N k (ν + pR k)
      + (K (wdual (ν + pR k)) (wdual (pR k))) * (dmul N (ν + pR k) : ℂ) := by
  have h := EFmap_sub_FEmap N k (ν + pR k)
  have htr : Ttr N k (ν + pR k) - Str N k (ν + pR k)
      = (K (wdual (ν + pR k)) (wdual (pR k))) * (dmul N (ν + pR k) : ℂ) := by
    rw [Ttr, Str, ← map_sub, h, map_smul, LinearMap.trace_one, smul_eq_mul]
  rw [Str_eq_Ttr N k ν]
  rw [sub_eq_iff_eq_add] at htr
  exact htr.trans (by rw [add_comm])


/-- Additivity of `endU` over finite sums. -/
@[simp] lemma endU_zero (N : Submodule U V) : endU N 0 = 0 := by ext _x; simp

lemma endU_sum (N : Submodule U V) {ι : Type*} (s : Finset ι) (f : ι → U) :
    endU N (∑ a ∈ s, f a) = ∑ a ∈ s, endU N (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, endU_add, ih]

/-! ## The vanishing of the weight multiplicities outside the support cone -/

/-- A weight `σ` whose height above `lamZ` is negative is not a weight of `L = V ⧸ N`. -/
lemma lwt_bot_of_htOf_neg (N : Submodule U V) {σ : Fin 8 → ℤ} (h : htOf (lamZ - σ) < 0) :
    Lwt N σ = ⊥ := by
  by_contra hne
  obtain ⟨x, hx, hx0⟩ := (Lwt N σ).ne_bot_iff.mp hne
  obtain ⟨m, hm⟩ := exists_wtZ_of_mem_Lwt N hx hx0
  have h2 : lamZ - σ = A8 *ᵥ (fun a => (m a : ℤ)) := by
    rw [hm, wtZ_eq]; abel
  have h3 : htOf (lamZ - σ) = ∑ i, (m i : ℤ) := by rw [h2, htOf_mulVec]
  have h4 : 0 ≤ ∑ i : Fin 8, (m i : ℤ) := Finset.sum_nonneg fun i _ => Int.natCast_nonneg _
  omega

open UniversalEnvelopingAlgebra in
/-- The trace `S` vanishes on a trivial weight space. -/
lemma Str_eq_zero_of_lwt_bot (N : Submodule U V) (k : Fin 120) {σ : Fin 8 → ℤ}
    (h : Lwt N σ = ⊥) : Str N k σ = 0 := by
  have : Subsingleton ↥(Lwt N σ) := ⟨fun a b => Subtype.ext (by
    have ha : (a : V ⧸ N) = 0 :=
      (Submodule.mem_bot ℂ).mp (show (a : V ⧸ N) ∈ (⊥ : Submodule ℂ (V ⧸ N)) from h ▸ a.2)
    have hb : (b : V ⧸ N) = 0 :=
      (Submodule.mem_bot ℂ).mp (show (b : V ⧸ N) ∈ (⊥ : Submodule ℂ (V ⧸ N)) from h ▸ b.2)
    rw [ha, hb])⟩
  haveI := this
  have hz : FEmap N k σ = 0 := Subsingleton.elim _ _
  rw [Str, hz, map_zero]

/-! ## The decomposition of the Casimir trace -/

open UniversalEnvelopingAlgebra in
/-- The restriction of the Cartan part `HᵢHⁱ` of the Casimir to a weight space. -/
noncomputable def HHmap (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) :
    ↥(Lwt N ν) →ₗ[ℂ] ↥(Lwt N ν) :=
  LinearMap.restrict ((endU N (ι ℂ (SerreH i))) * (endU N (ι ℂ (((hdual i : H) : L8)))))
    (fun _x hx => by
      rw [Module.End.mul_apply,
        endU_iota_cartan_apply N (hdual_mem_e8W_zero i) ν hx, map_smul]
      refine Submodule.smul_mem _ _ ?_
      have h2 := endU_iota_mem_Lwt N 0 (serreH_mem_e8W_zero i) hx
      rwa [add_zero] at h2)

open UniversalEnvelopingAlgebra in
/-- The action of `HHmap` on a weight space. -/
lemma HHmap_apply (N : Submodule U V) (i : Fin 8) (ν : Fin 8 → ℤ) (x : ↥(Lwt N ν)) :
    ((HHmap N i ν) x : V ⧸ N)
      = (((ν i : ℤ) : ℂ) * (K (wdual ν) (((hdual i : H) : L8)))) • (x : V ⧸ N) := by
  have hx : (x : V ⧸ N) ∈ Lwt N ν := x.2
  have h1 := endU_iota_cartan_apply N (hdual_mem_e8W_zero i) ν hx
  have h2 : endU N (ι ℂ (SerreH i)) (x : V ⧸ N) = ((ν i : ℤ) : ℂ) • (x : V ⧸ N) :=
    mem_Lwt_iff.mp hx i
  show (((endU N (ι ℂ (SerreH i))) * (endU N (ι ℂ (((hdual i : H) : L8))))) (x : V ⧸ N))
      = (((ν i : ℤ) : ℂ) * (K (wdual ν) (((hdual i : H) : L8)))) • (x : V ⧸ N)
  rw [Module.End.mul_apply, h1, map_smul, h2, smul_smul]
  congr 1
  ring

open UniversalEnvelopingAlgebra in
/-- **Decomposition of the Casimir trace**: `traceOmega` splits into the Cartan part and the
root parts. -/
lemma restOmega_eq (N : Submodule U V) (ν : Fin 8 → ℤ) :
    restOmega N ν = (∑ i : Fin 8, HHmap N i ν) + (∑ k : Fin 120, EFmap N k ν)
      + (∑ k : Fin 120, FEmap N k ν) := by
  have hΩop : endU N Omega
      = (∑ i : Fin 8, (endU N (ι ℂ (SerreH i))) * (endU N (ι ℂ (((hdual i : H) : L8)))))
        + (∑ k : Fin 120, (endU N (ι ℂ (eRoot k))) * (endU N (ι ℂ (fRoot k))))
        + (∑ k : Fin 120, (endU N (ι ℂ (fRoot k))) * (endU N (ι ℂ (eRoot k)))) := by
    have hhom : endU N Omega
        = ∑ a : Idx, (endU N (ι ℂ (bIdx a))) * (endU N (ι ℂ (bDual a))) := by
      rw [Omega, endU_sum]
      exact Finset.sum_congr rfl fun a _ => endU_mul N _ _
    rw [hhom]
    simp only [bIdx_apply, bFam_inl, bFam_inr_inl, bFam_inr_inr, bDual_inl, bDual_inr_inl,
      bDual_inr_inr, Fintype.sum_sum_type]
    abel
  ext x
  simp only [restOmega, HHmap, EFmap, FEmap, LinearMap.coe_restrict_apply, LinearMap.add_apply,
    LinearMap.sum_apply, Submodule.coe_add, Submodule.coe_sum, Pi.add_apply, hΩop]

open UniversalEnvelopingAlgebra in
/-- **The trace of the Casimir, decomposed.** -/
lemma traceOmega_eq_sum (N : Submodule U V) (ν : Fin 8 → ℤ) :
    traceOmega N ν
      = (∑ i : Fin 8, K (wdual ν) (((hdual i : H) : L8)) * ((ν i : ℤ) : ℂ)) * (dmul N ν : ℂ)
        + (∑ k : Fin 120, Ttr N k ν) + (∑ k : Fin 120, Str N k ν) := by
  have hH : ∀ i : Fin 8, LinearMap.trace ℂ ↥(Lwt N ν) (HHmap N i ν)
      = K (wdual ν) (((hdual i : H) : L8)) * ((ν i : ℤ) : ℂ) * (dmul N ν : ℂ) := by
    intro i
    have h : HHmap N i ν = (K (wdual ν) (((hdual i : H) : L8)) * ((ν i : ℤ) : ℂ))
        • (1 : Module.End ℂ ↥(Lwt N ν)) := by
      ext x
      rw [LinearMap.smul_apply, Module.End.one_apply]
      rw [HHmap_apply, mul_comm]
      rfl
    rw [h, map_smul, LinearMap.trace_one, smul_eq_mul]
  rw [traceOmega, restOmega_eq, map_add, map_add, map_sum, map_sum, map_sum,
    Finset.sum_congr rfl (fun i _ => hH i), Finset.sum_mul]
  rfl


/-! ## The trace recursion for the root operators -/

open UniversalEnvelopingAlgebra in
/-- The trace of `e_α f_α` on a weight space. -/
lemma Ttr_eq (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) :
    Ttr N k ν = Str N k ν + K (wdual ν) (wdual (pR k)) * (dmul N ν : ℂ) := by
  have h := EFmap_sub_FEmap N k ν
  have h2 : Ttr N k ν - Str N k ν = K (wdual ν) (wdual (pR k)) * (dmul N ν : ℂ) := by
    rw [Ttr, Str, ← map_sub, h, map_smul, LinearMap.trace_one, smul_eq_mul]
  rw [sub_eq_iff_eq_add] at h2
  exact h2.trans (add_comm _ _)

open UniversalEnvelopingAlgebra in
/-- The Cartan part of the Casimir trace sums to `⟪ν,ν⟫`. -/
lemma sum_cartan (ν : Fin 8 → ℤ) :
    (∑ i : Fin 8, K (wdual ν) (((hdual i : H) : L8)) * ((ν i : ℤ) : ℂ))
      = K (wdual ν) (wdual ν) := by
  have h : ∀ z : L8,
      (∑ i : Fin 8, K z (((hdual i : H) : L8)) * ((ν i : ℤ) : ℂ)) = K z (wdual ν) := by
    intro z
    rw [wdual_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  exact h (wdual ν)

open UniversalEnvelopingAlgebra in
/-- The sum of the traces `T` in terms of the traces `S`. -/
lemma sum_Ttr_eq (N : Submodule U V) (ν : Fin 8 → ℤ) :
    (∑ k : Fin 120, Ttr N k ν)
      = (∑ k : Fin 120, Str N k ν) + K (wdual ν) (wdual twoRho) * (dmul N ν : ℂ) := by
  have hmul : (∑ k : Fin 120, K (wdual ν) (wdual (pR k)) * (dmul N ν : ℂ))
      = (∑ k : Fin 120, K (wdual ν) (wdual (pR k))) * (dmul N ν : ℂ) :=
    (Finset.sum_mul Finset.univ (fun k : Fin 120 => K (wdual ν) (wdual (pR k)))
      (dmul N ν : ℂ)).symm
  rw [Finset.sum_congr rfl (fun k _ => Ttr_eq N k ν), Finset.sum_add_distrib, hmul]
  congr 1
  rw [← wdual_sum_pR, map_sum]

open UniversalEnvelopingAlgebra in
/-- **The master trace identity**: `2 Σ_α S_α = (c_λ - c_ν) dim L_ν`. -/
lemma two_sum_Str (N : Submodule U V) (ν : Fin 8 → ℤ) :
    2 * (∑ k : Fin 120, Str N k ν)
      = (cas - K (wdual ν) (wdual (ν + twoRho))) * (dmul N ν : ℂ) := by
  have h1 : traceOmega N ν = cas * (dmul N ν : ℂ) := traceOmega_eq N ν
  have h2 : traceOmega N ν
      = K (wdual ν) (wdual ν) * (dmul N ν : ℂ)
        + (∑ k : Fin 120, Ttr N k ν) + (∑ k : Fin 120, Str N k ν) := by
    rw [traceOmega_eq_sum, sum_cartan]
  have h3 := sum_Ttr_eq N ν
  have hK : K (wdual ν) (wdual (ν + twoRho))
      = K (wdual ν) (wdual ν) + K (wdual ν) (wdual twoRho) := by
    rw [wdual_add, map_add]
  have key : cas * (dmul N ν : ℂ)
      = K (wdual ν) (wdual ν) * (dmul N ν : ℂ)
        + ((∑ k : Fin 120, Str N k ν) + K (wdual ν) (wdual twoRho) * (dmul N ν : ℂ))
        + (∑ k : Fin 120, Str N k ν) := by
    rw [← h1, h2, h3]
  rw [sub_mul, key, hK, add_mul]
  ring

/-! ## Unfolding the recursion -/

/-- The weight `ν + s·α` on the `α`-string through `ν`. -/
def sh (k : Fin 120) (ν : Fin 8 → ℤ) (s : ℕ) : Fin 8 → ℤ := ν + (s : ℤ) • pR k

lemma sh_zero (k : Fin 120) (ν : Fin 8 → ℤ) : sh k ν 0 = ν := by
  simp [sh]

lemma sh_succ (k : Fin 120) (ν : Fin 8 → ℤ) (s : ℕ) : sh k ν (s + 1) = sh k ν s + pR k := by
  simp only [sh, Nat.cast_succ, add_smul, one_smul]
  abel

open UniversalEnvelopingAlgebra in
/-- **Unfolding of the trace recursion.** -/
lemma Str_eq_sum (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ) (M : ℕ) :
    Str N k ν = Str N k (sh k ν M)
      + ∑ s ∈ Finset.Icc 1 M,
          K (wdual (sh k ν s)) (wdual (pR k)) * (dmul N (sh k ν s) : ℂ) := by
  induction M with
  | zero =>
      rw [Finset.Icc_eq_empty (by norm_num : ¬ (1 ≤ 0)), Finset.sum_empty, sh_zero, add_zero]
  | succ M ih =>
      have hsplit :
          (∑ s ∈ Finset.Icc 1 (M + 1),
              K (wdual (sh k ν s)) (wdual (pR k)) * (dmul N (sh k ν s) : ℂ))
            = (∑ s ∈ Finset.Icc 1 M,
                K (wdual (sh k ν s)) (wdual (pR k)) * (dmul N (sh k ν s) : ℂ))
              + K (wdual (sh k ν (M + 1))) (wdual (pR k)) * (dmul N (sh k ν (M + 1)) : ℂ) :=
        Finset.sum_Icc_succ_top (M := ℂ) (by omega : 1 ≤ M + 1) _
      rw [ih, hsplit, sh_succ, Str_step N k (sh k ν M)]
      ring

open UniversalEnvelopingAlgebra in
/-- The trace `S` vanishes when the weight lies above `λ`. -/
lemma Str_eq_zero_of_htOf_neg (N : Submodule U V) (k : Fin 120) {σ : Fin 8 → ℤ}
    (h : htOf (lamZ - σ) < 0) : Str N k σ = 0 := by
  have h2 : htOf (lamZ - (σ + pR k)) < 0 := by
    have he : htOf (lamZ - (σ + pR k)) = htOf (lamZ - σ) - htOf (pR k) := by
      simp only [htOf_sub, htOf_add]
      ring
    have hp : 0 < htOf (pR k) := htOf_pR_pos k
    omega
  have hb := lwt_bot_of_htOf_neg N h2
  have hsh : sh k σ 1 = σ + pR k := by rw [sh_succ, sh_zero]
  have hdm : dmul N (σ + pR k) = 0 := by
    show Module.finrank ℂ ↥(Lwt N (σ + pR k)) = 0
    rw [hb]
    exact Module.finrank_zero_of_subsingleton
  rw [Str_eq_sum N k σ 1, hsh, Str_eq_zero_of_lwt_bot N k hb,
    Finset.sum_eq_zero (fun s hs => by
      rw [Finset.mem_Icc] at hs
      have : s = 1 := by omega
      subst this
      rw [hsh, hdm]
      simp), add_zero]


open UniversalEnvelopingAlgebra in
/-- The trace `S` vanishes at the end of the truncated `α`-string. -/
lemma Str_last_zero (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ)
    (hcon : posCon (lamZ - ν)) :
    Str N k (sh k ν ((htOf (lamZ - ν)).toNat)) = 0 := by
  set N' := (htOf (lamZ - ν)).toNat with hN'
  have hle : htOf (lamZ - ν) ≤ (N' : ℤ) := by
    rw [hN', Int.toNat_of_nonneg (htOf_nonneg hcon)]
  have hα : 1 ≤ htOf (pR k) := htOf_pR k
  have hgt : htOf (lamZ - (sh k ν N' + pR k)) < 0 := by
    have he : htOf (lamZ - (sh k ν N' + pR k))
        = htOf (lamZ - ν) - ((N' : ℤ) + 1) * htOf (pR k) := by
      simp only [sh, htOf_sub, htOf_add, htOf_smul_int]
      ring
    rw [he]
    have h1 : ((N' : ℤ) + 1) * htOf (pR k) ≥ (N' : ℤ) + 1 := by nlinarith
    linarith
  have hb := lwt_bot_of_htOf_neg N hgt
  have hdm : dmul N (sh k ν N' + pR k) = 0 := by
    show Module.finrank ℂ ↥(Lwt N (sh k ν N' + pR k)) = 0
    rw [hb]
    exact Module.finrank_zero_of_subsingleton
  have hsh : sh k (sh k ν N') 1 = sh k ν N' + pR k := by rw [sh_succ, sh_zero]
  rw [Str_eq_sum N k (sh k ν N') 1, hsh, Str_eq_zero_of_lwt_bot N k hb,
    Finset.sum_eq_zero (fun s hs => by
      rw [Finset.mem_Icc] at hs
      have hs1 : s = 1 := by omega
      subst hs1
      rw [hsh, hdm]
      simp), add_zero]

/-! ## The Weyl normalisation of the Killing form -/

/-- The bilinear form `⟪μ,ν⟫ = ∑ᵢⱼ μᵢ (A⁻¹)ᵢⱼ νⱼ` on weights. -/
def bil (μ ν : Fin 8 → ℤ) : ℤ := ∑ i, ∑ j, μ i * E8invM i j * ν j

/-- The `ρ` vector `(1,…,1)`. -/
def rhoZ : Fin 8 → ℤ := fun _ => 1

lemma twoRho_eq : twoRho = (2 : ℤ) • rhoZ := rfl

/-- `brk μ k` is the pairing `⟪μ, pR k⟫`. -/
lemma brk_eq_bil (μ : Fin 8 → ℤ) (k : Fin 120) : brk μ k = bil μ (pR k) := by
  simp only [brk, bil, coords]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The inverse Cartan matrix is symmetric. -/
lemma E8invM_symm (i j : Fin 8) : E8invM i j = E8invM j i := by
  fin_cases i <;> fin_cases j <;> norm_num [E8invM,
    Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.E8inv]

/-- The cast of `bil` to `ℂ`. -/
lemma bil_cast (μ ν : Fin 8 → ℤ) :
    ((bil μ ν : ℤ) : ℂ)
      = ∑ i : Fin 8, ∑ j : Fin 8, ((μ i : ℤ) : ℂ) * ((E8invM i j : ℤ) : ℂ) * ((ν j : ℤ) : ℂ) := by
  simp only [bil]
  push_cast
  rfl

/-- `⟪μ, μ + 2ρ⟫ = Bint μ - ⟪ρ,ρ⟫`. -/
lemma bil_twoRho (μ : Fin 8 → ℤ) :
    bil μ (μ + twoRho) = Bint μ - bil rhoZ rhoZ := by
  have h1 : (∑ i : Fin 8, ∑ j : Fin 8, μ j * E8invM i j)
      = (∑ i : Fin 8, ∑ j : Fin 8, μ i * E8invM i j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [E8invM_symm j i]
  have hexp : ∀ i j : Fin 8, μ i * E8invM i j * (μ j + 2)
      = (μ i + 1) * E8invM i j * (μ j + 1) - 1 * E8invM i j * 1
        + (μ i * E8invM i j - μ j * E8invM i j) := by
    intro i j; ring
  simp only [bil, Bint, rhoZ, twoRho, Pi.add_apply, Pi.one_apply]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hexp i j))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, sub_self, add_zero]

/-- The Casimir eigenvalue in the Weyl normalisation. -/
lemma cas_eq : cas = (1 / 60) * ((bil lamZ (lamZ + twoRho) : ℤ) : ℂ) := by
  rw [cas, Commons.Algebra.Lie.SerreConstruction.killingForm_cartanDual lamZ (lamZ + twoRho)
    (wdual lamZ) (wdual (lamZ + twoRho)) (wdual_mem_cartan _) (wdual_mem_cartan _)
    (fun i => K_SerreH_wdual i lamZ) (fun j => K_SerreH_wdual j (lamZ + twoRho)),
    bil_cast]

/-- The `ν`-Casimir eigenvalue in the Weyl normalisation. -/
lemma cnu_eq (ν : Fin 8 → ℤ) :
    K (wdual ν) (wdual (ν + twoRho)) = (1 / 60) * ((bil ν (ν + twoRho) : ℤ) : ℂ) := by
  rw [Commons.Algebra.Lie.SerreConstruction.killingForm_cartanDual ν (ν + twoRho)
    (wdual ν) (wdual (ν + twoRho)) (wdual_mem_cartan _) (wdual_mem_cartan _)
    (fun i => K_SerreH_wdual i ν) (fun j => K_SerreH_wdual j (ν + twoRho)), bil_cast]

/-- The coefficient bridge for the root terms. -/
lemma K_wdual_pR (μ : Fin 8 → ℤ) (k : Fin 120) :
    K (wdual μ) (wdual (pR k)) = (1 / 60) * ((brk μ k : ℤ) : ℂ) := by
  rw [Commons.Algebra.Lie.SerreConstruction.killingForm_cartanDual μ (pR k)
    (wdual μ) (wdual (pR k)) (wdual_mem_cartan _) (wdual_mem_cartan _)
    (fun i => K_SerreH_wdual i μ) (fun j => K_SerreH_wdual j (pR k)), brk_eq_bil, bil_cast]

lemma sum_rhoZ : bil rhoZ rhoZ = Bint (0 : Fin 8 → ℤ) := by
  simp only [bil, Bint, rhoZ, Pi.one_apply, Pi.zero_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `cas - c_ν = (1/60) (Bint λ - Bint ν)`. -/
lemma cas_sub_cnu (ν : Fin 8 → ℤ) :
    cas - K (wdual ν) (wdual (ν + twoRho))
      = (1 / 60) * (((Bint lamZ - Bint ν : ℤ)) : ℂ) := by
  rw [cas_eq, cnu_eq, bil_twoRho lamZ, bil_twoRho ν, sum_rhoZ]
  push_cast
  ring


/-! ## The Freudenthal recursion in the Weyl normalisation -/

/-- The multiplicity of the weight `ν` in `L = V ⧸ N`, as a rational number. -/
noncomputable abbrev mul (N : Submodule U V) (ν : Fin 8 → ℤ) : ℚ := (dmul N ν : ℚ)

open UniversalEnvelopingAlgebra in
/-- `Str` in the Weyl normalisation. -/
lemma Str_eq_bil (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ)
    (hcon : posCon (lamZ - ν)) :
    Str N k ν = (1 / 60) * ∑ s ∈ Finset.Icc 1 (htOf (lamZ - ν)).toNat,
        ((brk (ν + s • pR k) k : ℤ) : ℂ) * (dmul N (ν + s • pR k) : ℂ) := by
  rw [Str_eq_sum N k ν ((htOf (lamZ - ν)).toNat), Str_last_zero N k ν hcon, zero_add,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hsh : sh k ν s = ν + s • pR k := by
    simp only [sh, Nat.cast_smul_eq_nsmul]
  rw [K_wdual_pR, hsh]
  ring

open UniversalEnvelopingAlgebra in
/-- The trace `S` in the Weyl normalisation, multiplied by `60`. -/
lemma sixty_Str_eq (N : Submodule U V) (k : Fin 120) (ν : Fin 8 → ℤ)
    (hcon : posCon (lamZ - ν)) :
    (60 : ℂ) * Str N k ν = ∑ s ∈ Finset.Icc 1 (htOf (lamZ - ν)).toNat,
        ((brk (ν + s • pR k) k : ℤ) : ℂ) * (dmul N (ν + s • pR k) : ℂ) := by
  rw [Str_eq_bil N k ν hcon, ← mul_assoc,
    show (60 : ℂ) * (1 / 60) = 1 by norm_num, one_mul]

/-- The Casimir eigenvalue difference, multiplied by `60`. -/
lemma sixty_cas_sub_cnu (ν : Fin 8 → ℤ) :
    (60 : ℂ) * (cas - K (wdual ν) (wdual (ν + twoRho)))
      = ((Bint lamZ - Bint ν : ℤ) : ℂ) := by
  rw [cas_sub_cnu, ← mul_assoc, show (60 : ℂ) * (1 / 60) = 1 by norm_num, one_mul]

open UniversalEnvelopingAlgebra in
/-- **The Freudenthal recursion** for the multiplicity function of `L = V ⧸ N`,
in the integral (Weyl-normalised) form used by `Submission.E8Character.eq_of_freudenthal`. -/
theorem freudenthal_mul (N : Submodule U V) (ν : Fin 8 → ℤ) (hcon : posCon (lamZ - ν)) :
    ((Bint lamZ - Bint ν : ℤ) : ℚ) * mul N ν
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lamZ - ν)).toNat,
          ((brk (ν + k • pR j) j : ℤ) : ℚ) * mul N (ν + k • pR j) := by
  have hgoal : (((Bint lamZ : ℤ) : ℂ) - ((Bint ν : ℤ) : ℂ)) * (dmul N ν : ℂ)
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lamZ - ν)).toNat,
          ((brk (ν + k • pR j) j : ℤ) : ℂ) * (dmul N (ν + k • pR j) : ℂ) := by
    have hsum : (60 : ℂ) * (∑ k : Fin 120, Str N k ν)
        = ∑ k : Fin 120, ∑ s ∈ Finset.Icc 1 (htOf (lamZ - ν)).toNat,
            ((brk (ν + s • pR k) k : ℤ) : ℂ) * (dmul N (ν + s • pR k) : ℂ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => sixty_Str_eq N k ν hcon)
    have h := congrArg (fun z : ℂ => (60 : ℂ) * z) (two_sum_Str N ν)
    rw [← mul_assoc (60 : ℂ) (2 : ℂ),
      ← mul_assoc (60 : ℂ) (cas - K (wdual ν) (wdual (ν + twoRho))),
      sixty_cas_sub_cnu] at h
    rw [show (60 : ℂ) * 2 * (∑ k : Fin 120, Str N k ν) = 2 * ((60 : ℂ) * ∑ k : Fin 120, Str N k ν)
        from by ring, hsum] at h
    rw [h, Int.cast_sub]
  apply (Rat.cast_injective (α := ℂ))
  push_cast
  exact hgoal


end Submission.E8Freudenthal
