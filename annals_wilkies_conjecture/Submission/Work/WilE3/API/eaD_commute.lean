import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.API.eaD_derivation

namespace Work.WilE3.API

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

variable {k r : ℕ}

/-!
## Commutativity of mixed `eaD`'s

`eaD c i` is the derivation
`∂/∂xᵢ + ∑ⱼ aⱼᵢ ψⱼ ∂/∂ψⱼ` of the EA polynomial ring.  The operators `∂/∂xᵢ` and
`ψⱼ ∂/∂ψⱼ` all commute, and the coefficients `aⱼᵢ` are constants, so the `eaD c i`
themselves commute pairwise.

We prove this derivation-theoretically: `eaD c i` is packaged as a `Derivation`
(`eaDer`), the commutator `⁅eaDer c i, eaDer c j⁆` is again a derivation, and it
vanishes on every variable `X v`; a derivation of a polynomial ring is determined
by its values on the variables (`MvPolynomial.derivation_ext`), so it is zero.
-/

/-- The underlying `ℝ`-linear map of `eaD c i`. -/
noncomputable def eaDlin (c : EAChain k r) (i : Fin k) :
    EAPoly k r →ₗ[ℝ] EAPoly k r where
  toFun := eaD c i
  map_add' := (eaD_derivation c i).1
  map_smul' := (eaD_derivation c i).2.1

@[simp] theorem eaDlin_apply (c : EAChain k r) (i : Fin k) (Q : EAPoly k r) :
    eaDlin c i Q = eaD c i Q := rfl

/-- `eaD c i` packaged as a `Derivation` of the EA polynomial ring. -/
noncomputable def eaDer (c : EAChain k r) (i : Fin k) :
    Derivation ℝ (EAPoly k r) (EAPoly k r) :=
  Derivation.mk' (eaDlin c i) (by
    intro a b
    simp only [eaDlin_apply, smul_eq_mul]
    rw [(eaD_derivation c i).2.2.1 a b]
    ring)

theorem eaDer_apply (c : EAChain k r) (i : Fin k) (Q : EAPoly k r) :
    eaDer c i Q = eaD c i Q := rfl

theorem eaDer_C (c : EAChain k r) (i : Fin k) (a : ℝ) :
    eaDer c i (MvPolynomial.C a) = 0 := by
  rw [eaDer_apply]
  exact (eaD_derivation c i).2.2.2 a

theorem eaDer_X_inl (c : EAChain k r) (i l : Fin k) :
    eaDer c i (MvPolynomial.X (Sum.inl l)) = if i = l then 1 else 0 := by
  rw [eaDer_apply]
  exact Work.WilE2.ESys.d_inl (Work.WilE2.ESys.ofChain c) i l

theorem eaDer_X_inr (c : EAChain k r) (i : Fin k) (l : Fin r) :
    eaDer c i (MvPolynomial.X (Sum.inr l)) =
      MvPolynomial.C (c.a l i) * MvPolynomial.X (Sum.inr l) := by
  rw [eaDer_apply]
  exact Work.WilE2.ESys.d_inr (Work.WilE2.ESys.ofChain c) i l

/-- The commutator `⁅eaDer c i, eaDer c j⁆` vanishes on every variable. -/
theorem eaDer_comm_X (c : EAChain k r) (i j : Fin k) (v : Fin k ⊕ Fin r) :
    ⁅eaDer c i, eaDer c j⁆ (MvPolynomial.X v) = 0 := by
  rw [Derivation.commutator_apply]
  rcases v with l | l
  · rw [eaDer_X_inl c j l, eaDer_X_inl c i l]
    rcases eq_or_ne j l with h | h <;> rcases eq_or_ne i l with h' | h'
    · rw [ite_eq_left h, ite_eq_left h']; simp
    · rw [ite_eq_left h, ite_eq_right h']; simp
    · rw [ite_eq_right h, ite_eq_left h']; simp
    · rw [ite_eq_right h, ite_eq_right h']; simp
  · simp only [eaDer_X_inr, Derivation.leibniz, eaDer_C, smul_zero, smul_eq_mul, mul_zero,
      add_zero] <;> ring

/-- **The `eaD`'s pairwise commute**, as derivations. -/
theorem eaDer_comm (c : EAChain k r) (i j : Fin k) :
    ⁅eaDer c i, eaDer c j⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  intro v
  rw [Derivation.zero_apply]
  exact eaDer_comm_X c i j v

theorem eaD_commute {k r : ℕ} (c : EAChain k r) (i j : Fin k) (Q : EAPoly k r) :
    eaD c i (eaD c j Q) = eaD c j (eaD c i Q) := by
  have h := Derivation.congr_fun (eaDer_comm c i j) Q
  simp only [Derivation.commutator_apply, Derivation.zero_apply, eaDer_apply] at h
  exact sub_eq_zero.mp h

end Work.WilE3.API
