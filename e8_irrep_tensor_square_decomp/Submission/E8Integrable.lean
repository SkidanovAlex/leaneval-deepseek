import Submission.VermaWeight
import Submission.Commons.Algebra.Lie.Sl2.uea_mul_pow

/-!
# The integrability null vector `fᵢ^(λᵢ+1) v` of the Verma module `M(ω₁+ω₈)`

For `λ = ω₁+ω₈` the coordinates `λᵢ` are `1` at the two end nodes of the `E₈` diagram and `0`
elsewhere, so `kI i ∈ {0,1}` with `lam i = (kI i : ℂ)`.  This file proves that the vector

  `xᵢ := fᵢ^(kI i + 1) v = (Lbar i)^(kI i + 1) v`

of the ⋆-model `V = M(λ)` is a **primitive vector** (a highest weight vector): it is killed by
every raising operator `Ebar j`.

This is the first step of the integrability argument: `xᵢ` generates a highest weight submodule of
weight `μ = λ - (λᵢ+1)αᵢ ≺ λ`, which is proper (its weights are all `⪯ μ`, while `λ ⋠ μ`), hence
contained in the unique maximal submodule `N`, so that `fᵢ^(λᵢ+1)` acts by `0` on `L(λ) = V/N`.
The remaining steps (properness of `U(e₈)·xᵢ`, and the submodule of locally-`f`-nilpotent vectors)
are recorded in the SESSION 15 roadmap section of `Submission.lean`.

The key input is the fleet lemma `Commons.Algebra.Lie.Sl2.uea_mul_pow_aux`
(`E * F^(n+1) = F^(n+1) * E + (n+1) • (F^n * (H - n))` for `E F = F E + H` and
`H F = F H - 2 F`), applied to `ι(SerreE i)`, `ι(SerreF i)`, `ι(SerreH i)` in `U(e₈)`, whose
relations are the `U(e₈)`-level Serre relations `E8Weights.commutator_E_F` and
`E8Weights.commutator_H_F` (this avoids the `⁅·,·⁆`-instance diamond on `e₈ ℂ`).
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace Submission.E8Integrable

open Submission.StarModule (FA wordElt wordElt_nil Eop_apply)
open Submission.StarQuotient (Ebar Lbar Hbar Ebar_mk Lbar_mk lie_Ebar_Lbar)
open Submission.VermaWeight

/-- The natural number `kI i` with `lam i = (kI i : ℂ)`. -/
def kI (i : Fin 8) : ℕ := if i = 0 ∨ i = 7 then 1 else 0

lemma lam_eq_kI (i : Fin 8) : lam i = (kI i : ℂ) := by
  fin_cases i <;> simp [kI, lam, Submission.E8Weights.omegaOnePlusOmegaEight]

/-- The highest weight vector is killed by every raising operator. -/
lemma Ebar_v (j : Fin 8) : Ebar E8 lam j v = 0 := by
  show Ebar E8 lam j (Submodule.Quotient.mk (1 : FA (Fin 8))) = 0
  rw [Ebar_mk, ← wordElt_nil, Eop_apply]
  rfl

/-- The highest weight vector is an `Hbar`-eigenvector. -/
lemma Hbar_v (i : Fin 8) : Hbar E8 lam i v = lam i • v := by
  show Hbar E8 lam i (Submodule.Quotient.mk (1 : FA (Fin 8))) = lam i • _
  exact Commons.Algebra.Lie.SerreConstruction.Hbar_mk_one lam i

/-- `Ebar i` and `Lbar j` commute for `i ≠ j`. -/
lemma Ebar_Lbar_comm (i j : Fin 8) (h : i ≠ j) (x : V) :
    Ebar E8 lam i (Lbar E8 j x) = Lbar E8 j (Ebar E8 lam i x) := by
  have hcomm := lie_Ebar_Lbar E8 lam i j
  rw [if_neg h] at hcomm
  have h3 := congrArg (fun f : Module.End ℂ V => f x) hcomm
  rw [LieRing.of_associative_ring_bracket] at h3
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    LinearMap.zero_apply] at h3
  exact sub_eq_zero.mp h3

/-- `Ebar i` commutes with all powers of `Lbar j` when `i ≠ j`. -/
lemma Ebar_Lbar_pow_comm (i j : Fin 8) (h : i ≠ j) (n : ℕ) (x : V) :
    Ebar E8 lam i (((Lbar E8 j) ^ n) x) = ((Lbar E8 j) ^ n) (Ebar E8 lam i x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, Ebar_Lbar_comm i j h, ih, ← Module.End.mul_apply,
        ← pow_succ']

/-- **The null vector is primitive.**  For every `i`, `(Lbar i)^(kI i + 1) v` is killed by every
raising operator `Ebar j`. -/
theorem Ebar_Lbar_pow_v (i j : Fin 8) :
    Ebar E8 lam j (((Lbar E8 i) ^ (kI i + 1)) v) = 0 := by
  by_cases hji : j = i
  · rw [hji]
    -- the 𝔰𝔩₂ commutation relation in `U(e₈)`
    have hEF : (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreE i))
          * (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF i))
        = (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF i))
            * (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreE i))
          + UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreH i) := by
      have h := Submission.E8Weights.commutator_E_F i i
      rw [if_pos rfl] at h
      exact sub_eq_iff_eq_add'.mp h
    have hHF : (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreH i))
          * (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF i))
        = (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF i))
            * (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreH i))
          - (2 : ℂ) • (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF i)) := by
      have hid : CartanMatrix.E₈ i i = 2 := Submission.VermaNonzero.E8_diag i
      have h := Submission.E8Weights.commutator_H_F i i
      rw [hid] at h
      have hc : (-(2 : ℤ)) • (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF i))
          = -(2 : ℂ) • (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF i)) := by
        rw [show (-(2 : ℂ)) = ((-(2 : ℤ) : ℤ) : ℂ) by norm_num, Int.cast_smul_eq_zsmul]
      rw [hc] at h
      have h' := sub_eq_iff_eq_add.mp h
      rw [add_comm, neg_smul, ← sub_eq_add_neg] at h'
      exact h'
    have hp := Commons.Algebra.Lie.Sl2.uea_mul_pow_aux
      (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreE i))
      (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF i))
      (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreH i)) hEF hHF (kI i)
    have happ := congrArg (fun u : U => Submission.VermaNonzero.rho lam u v) hp
    simp only [map_mul, map_pow, map_add, map_smul, map_sub, map_one,
      Module.End.mul_apply] at happ
    rw [show Submission.VermaNonzero.rho lam (UniversalEnvelopingAlgebra.ι ℂ
          (Submission.E8Weights.SerreE i)) = Ebar E8 lam i from
        (Submission.VermaNonzero.rho_iota lam _).trans (Submission.VermaNonzero.act_E lam i),
      show Submission.VermaNonzero.rho lam (UniversalEnvelopingAlgebra.ι ℂ
          (Submission.E8Weights.SerreF i)) = Lbar E8 i from
        Submission.VermaNonzero.rho_F lam i,
      show Submission.VermaNonzero.rho lam (UniversalEnvelopingAlgebra.ι ℂ
          (Submission.E8Weights.SerreH i)) = Hbar E8 lam i from
        Submission.VermaNonzero.rho_H lam i] at happ
    have hval : (((Lbar E8 i) ^ (kI i + 1)) * Ebar E8 lam i
          + ((kI i : ℂ) + 1) • (((Lbar E8 i) ^ (kI i))
              * (Hbar E8 lam i - (kI i : ℂ) • 1))) v = 0 := by
      rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, Module.End.mul_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Hbar_v, Ebar_v i,
        lam_eq_kI]
      simp
    rw [happ, show (((kI i + 1 : ℕ)) : ℂ) = ((kI i : ℂ) + 1) by push_cast; ring]
    exact hval
  · rw [Ebar_Lbar_pow_comm j i hji, Ebar_v]
    simp

end Submission.E8Integrable
