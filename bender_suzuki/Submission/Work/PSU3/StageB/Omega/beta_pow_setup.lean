/-
# `Work.PSU3.StageB.Omega.beta_pow_setup` — setup for Peterfalvi II Ch. VII §2 (11)–(16)

Definitions and elementary (field-theoretic) lemmas for the sequences of §2 (11)–(16) that
enter the proof of `Work.PSU3.StageB.Omega.beta_pow_m_eq_one`:

* `bS β i = β^i + β^{-i}` — the denominator sequence `S_i` of (13);
* `uSeq_eq_div` — `u_i = S_{i-1}/S_i` (the closed form (13));
* `beta_sigma_dichotomy`, `bS_fixed`, `uSeq_fixed`, `wSeq_fixed` — `σE`-invariance;
* `uSeq_rec_alpha`, `wSeq_rec` — the recursions (11)/(13)/(14) in the form used by the
  induction;
* `uSeq_ord_sub_one`, `wSeq_ord_sub_one` — the "stopping" identities of (15)/(16);
* `dSeq_one`, `dSeq_succ`, `dSeq_stop` — the §2 (14) recursion for the exponents `d_i`.

Nothing here has a `hole`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.Seq
import Submission.Work.PSU3.StageB.Omega.uSeq_rec
import Submission.Work.PSU3.StageB.Omega.uSeq_div
import Submission.Work.PSU3.StageB.Omega.uSeq_telescope

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Classical

namespace Work.PSU3.StageB.Omega

open Work.PSU3
open Work.PSU3.StageB

variable {n : ℕ}
variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-! ## The sequence `S_i = β^i + β^{-i}` -/

/-- `S_i = β^i + β^{-i}`, the denominator sequence of §2 (13). -/
noncomputable def bS (β : E n) (i : ℕ) : E n := β ^ i + (β ^ i)⁻¹

@[simp] lemma bS_zero (β : E n) : bS β 0 = 0 := by
  rw [bS, pow_zero, inv_one, CharTwo.add_self_eq_zero]

lemma bS_one (β : E n) : bS β 1 = β + β⁻¹ := by
  rw [bS, pow_one]

/-- In a field of characteristic two, `x * x = 1` forces `x = 1`. -/
lemma eq_one_of_mul_self_eq_one {x : E n} (h : x * x = 1) : x = 1 := by
  have h1 : x ^ 2 = 1 := by rw [pow_two]; exact h
  rcases sq_eq_one_iff.mp h1 with h2 | h2
  · exact h2
  · rwa [CharTwo.neg_eq] at h2

/-- `S_i = 0` exactly when `β^i = 1` (for `β ≠ 0`). -/
lemma bS_eq_zero_iff (β : E n) (hβ : β ≠ 0) (i : ℕ) : bS β i = 0 ↔ β ^ i = 1 := by
  constructor
  · intro h
    have h2 : β ^ i + (β ^ i)⁻¹ = 0 := h
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h2
    have h3 : β ^ i * β ^ i = 1 := by
      have h4 := congrArg (fun z => z * β ^ i) h2
      rw [inv_mul_cancel₀ (pow_ne_zero i hβ)] at h4
      exact h4
    exact eq_one_of_mul_self_eq_one h3
  · intro h
    rw [bS, h, inv_one, CharTwo.add_self_eq_zero]

lemma bS_ne_zero_iff (β : E n) (hβ : β ≠ 0) (i : ℕ) : bS β i ≠ 0 ↔ β ^ i ≠ 1 := by
  rw [← not_iff_not, not_not, not_not, bS_eq_zero_iff β hβ]

/-! ## The dichotomy `σE β = β` or `σE β = β⁻¹` -/

/-- If `β + β⁻¹ = α0` with `α0 ≠ 0` fixed by `σE`, then either `σE β = β` or `σE β = β⁻¹`. -/
theorem beta_sigma_dichotomy {β α0 : E n} (hβ : β ≠ 0) (hβα : β + β⁻¹ = α0)
    (hα0 : α0 ≠ 0) (hα : σE α0 = α0) : σE β = β ∨ σE β = β⁻¹ := by
  have hσβ : σE β ≠ 0 := by
    intro h0
    have h1 : σE α0 = 0 := by rw [← hα, ← hβα, map_add, map_inv₀, h0]; simp
    exact hα0 (by rw [← hα]; exact h1)
  have h : σE β + (σE β)⁻¹ = β + β⁻¹ := by
    have h1 : σE (β + β⁻¹) = σE β + (σE β)⁻¹ := by simp
    rw [← h1, hβα, hα]
  have e1 : (σE β + (σE β)⁻¹) * (β * σE β) = β * (σE β) ^ 2 + β := by field_simp
  have e2 : (β + β⁻¹) * (β * σE β) = β ^ 2 * σE β + σE β := by field_simp
  have h3 : β * (σE β) ^ 2 + β = β ^ 2 * σE β + σE β := by
    rw [← e1, ← e2]; exact congrArg (· * (β * σE β)) h
  have key : (β + σE β) * (β * σE β + 1) = 0 := by
    have hexp : (β + σE β) * (β * σE β + 1)
        = (β ^ 2 * σE β + σE β) + (β * (σE β) ^ 2 + β) := by ring
    rw [hexp, h3, CharTwo.add_self_eq_zero]
  rcases mul_eq_zero.mp key with h1 | h1
  · left
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h1
    exact h1.symm
  · right
    have h2 : β * σE β = 1 := by
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h1
      exact h1
    exact eq_inv_of_mul_eq_one_right h2

/-- `S_i` is fixed by `σE`. -/
lemma bS_fixed {β : E n} (hσ : σE β = β ∨ σE β = β⁻¹) (i : ℕ) :
    σE (bS β i) = bS β i := by
  simp only [bS]
  rw [map_add, map_inv₀, map_pow]
  rcases hσ with h | h
  · rw [h]
  · rw [h, inv_pow, inv_inv, add_comm]

/-! ## `u_i` as the ratio `S_{i-1}/S_i`

This is (13) in its telescoping shape. -/

/-- **(13)**: `u_{i+1} = S_i/S_{i+1}`. -/
lemma uSeq_eq_div (β : E n) (hβ : β ≠ 0) (i : ℕ) :
    uSeq β (i + 1) = bS β i / bS β (i + 1) := by
  rw [uSeq, bS, bS]
  have h1 : β ^ (i + 1) / β = β ^ i := by rw [pow_succ]; field_simp
  have h2 : β / β ^ (i + 1) = (β ^ i)⁻¹ := by rw [pow_succ]; field_simp
  rw [h1, h2]

/-- **(13)**, indexed version. -/
lemma uSeq_eq_div' (β : E n) (hβ : β ≠ 0) {i : ℕ} (hi : 1 ≤ i) :
    uSeq β i = bS β (i - 1) / bS β i := by
  calc uSeq β i = uSeq β ((i - 1) + 1) := by rw [show (i - 1) + 1 = i from by omega]
    _ = bS β (i - 1) / bS β ((i - 1) + 1) := uSeq_eq_div β hβ (i - 1)
    _ = bS β (i - 1) / bS β i := by rw [show (i - 1) + 1 = i from by omega]

lemma uSeq_zero (β : E n) : uSeq β 0 = 0 := by
  have h : ((1 : E n) + 1) = 0 := CharTwo.add_self_eq_zero 1
  simp [uSeq, h]

lemma uSeq_fixed (β : E n) (hβ : β ≠ 0) (hσ : σE β = β ∨ σE β = β⁻¹) :
    ∀ i, σE (uSeq β i) = uSeq β i := by
  intro i
  rcases Nat.eq_zero_or_pos i with hi0 | hi
  · subst hi0
    rw [uSeq_zero]
    exact map_zero σE
  · rw [uSeq_eq_div' β hβ hi, map_div₀, bS_fixed hσ, bS_fixed hσ]

lemma wSeq_eq (α β : E n) (i : ℕ) : wSeq α β i = (bS β i / α) ^ 2 := rfl

lemma wSeq_fixed {α0 β : E n} (hα : σE α0 = α0) (hσ : σE β = β ∨ σE β = β⁻¹) (i : ℕ) :
    σE (wSeq α0 β i) = wSeq α0 β i := by
  rw [wSeq_eq, map_pow, map_div₀, bS_fixed hσ i, hα]

/-- `fval` is injective on `F*`. -/
lemma fval_inj {u v : ↥(FX n)} (h : fval u = fval v) : u = v :=
  Subtype.ext (Units.ext h)

lemma fval_one : fval (1 : ↥(FX n)) = 1 := by simp

lemma fval_eq_one_iff {u : ↥(FX n)} : fval u = 1 ↔ u = 1 :=
  ⟨fun h => fval_inj (by rw [h, fval_one]), fun h => by rw [h, fval_one]⟩

/-- The `Q`-element `zc u_i`. -/
noncomputable def zU (fr : CoarseFrame H Q t n) (β : E n) (hβ : β ≠ 0)
    (hσ : σE β = β ∨ σE β = β⁻¹) (i : ℕ) : ↥Q :=
  zcQ fr (uSeq β i) (uSeq_fixed β hβ hσ i)

@[simp] lemma zU_coe (fr : CoarseFrame H Q t n) (β : E n) (hβ : β ≠ 0)
    (hσ : σE β = β ∨ σE β = β⁻¹) (i : ℕ) :
    ((zU fr β hβ hσ i : Q) : G) = fr.zc (uSeq β i) := zcQ_coe fr _ _

/-! ## The `F*`-coordinate `λ_i` of the exponent `d_i` -/

/-- The family `λ` of `F*`-coordinates of §2 (14): `λ_i = (S_i/α0)^2`. -/
noncomputable def lamSeq (α0 β : E n) (hα : σE α0 = α0) (hσ : σE β = β ∨ σE β = β⁻¹) :
    ℕ → ↥(FX n) :=
  fun i => if h : wSeq α0 β i ≠ 0 then mkFX (wSeq α0 β i) (wSeq_fixed hα hσ i) h else 1

lemma fval_lamSeq (α0 β : E n) (hα : σE α0 = α0) (hσ : σE β = β ∨ σE β = β⁻¹) {i : ℕ}
    (h : wSeq α0 β i ≠ 0) : fval (lamSeq α0 β hα hσ i) = wSeq α0 β i := by
  unfold lamSeq
  rw [dif_pos h]
  rfl

/-! ## Elementary identities on the sequences -/

/-- `u_i ≠ 0` when `S_i ≠ 0` and `S_{i+1} ≠ 0`. -/
lemma uSeq_ne_zero (β : E n) (hβ : β ≠ 0) (i : ℕ) (h1 : bS β i ≠ 0) (h2 : bS β (i + 1) ≠ 0) :
    uSeq β (i + 1) ≠ 0 := by
  rw [uSeq_eq_div β hβ i]
  exact div_ne_zero h1 h2

/-- `wSeq α0 β i ≠ 0` when `S_i ≠ 0`. -/
lemma wSeq_ne_zero (α0 β : E n) (hα0 : α0 ≠ 0) (i : ℕ) (h : bS β i ≠ 0) :
    wSeq α0 β i ≠ 0 := by
  rw [wSeq_eq]
  exact pow_ne_zero _ (div_ne_zero h hα0)

/-- `wSeq α0 β 1 = 1`. -/
lemma wSeq_one {α0 β : E n} (hβα : β + β⁻¹ = α0) (hα0 : α0 ≠ 0) :
    wSeq α0 β 1 = 1 := by
  rw [wSeq_eq, bS_one, hβα, div_self hα0, one_pow]

/-- **(11)**/(13): `α0 + u_{i+1}^{-1} = u_i`, the `fval v = fval α + (fval u)^{-1}`
hypothesis of §2 (10) in the induction (the closed form of `u_{i+1} = 1/(α + u_i)`). -/
lemma uSeq_rec_alpha (α0 β : E n) (hβα : β + β⁻¹ = α0) (hβ : β ≠ 0) {i : ℕ} (hi : 1 ≤ i)
    (h1 : bS β i ≠ 0) (h2 : bS β (i + 1) ≠ 0) :
    α0 + (uSeq β (i + 1))⁻¹ = uSeq β i := by
  have hrec := uSeq_rec α0 β hβα hβ hi h1 h2
  have hkey : α0 + uSeq β i = (uSeq β (i + 1))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hrec)
  rw [← hkey]
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- **(14)**: the recursion for the exponent coordinates, `λ_{i+1} = λ_i · u_{i+1}^{-2}`. -/
lemma wSeq_rec (α0 β : E n) (hβ : β ≠ 0) (hα0 : α0 ≠ 0) (i : ℕ) (h1 : bS β i ≠ 0) :
    wSeq α0 β (i + 1) = wSeq α0 β i * (uSeq β (i + 1))⁻¹ * (uSeq β (i + 1))⁻¹ := by
  rw [wSeq_eq, wSeq_eq, uSeq_eq_div β hβ i, inv_div]
  field_simp

/-- **(15)**: the "stopping" identity for `u_i`. -/
lemma uSeq_ord_sub_one {β α0 : E n} (hβ : β ≠ 0) (hβα : β + β⁻¹ = α0)
    (hα0 : α0 ≠ 0) {j : ℕ} (hj : 2 ≤ j) (hord : β ^ j = 1) :
    uSeq β (j - 1) = α0 := by
  have hj1 : 1 ≤ j - 1 := by omega
  have hS1 : bS β (j - 1) = α0 := by
    have h : β ^ (j - 1) = β⁻¹ := by
      have h2 : β ^ (j - 1) * β = 1 := by
        rw [← pow_succ, show j - 1 + 1 = j from by omega, hord]
      exact eq_inv_of_mul_eq_one_left h2
    rw [bS, h, inv_inv, add_comm]; exact hβα
  have hS2 : bS β (j - 2) = α0 ^ 2 := by
    have h : β ^ (j - 2) = (β⁻¹) ^ 2 := by
      have h2 : β ^ (j - 2) * β ^ 2 = 1 := by
        rw [← pow_add, show j - 2 + 2 = j from by omega, hord]
      rw [eq_inv_of_mul_eq_one_left h2, inv_pow]
    have h' : (β ^ (j - 2))⁻¹ = β ^ 2 := by rw [h, inv_pow, inv_inv]
    rw [bS, h', h, ← add_pow_char, ← hβα, add_comm]
  rw [uSeq_eq_div' β hβ hj1, show j - 1 - 1 = j - 2 from by omega, hS2, hS1]
  field_simp

/-- **(15)**: the `F*`-coordinate at the stopping index is `1`. -/
lemma wSeq_ord_sub_one {β α0 : E n} (hβα : β + β⁻¹ = α0)
    (hα0 : α0 ≠ 0) {j : ℕ} (hj : 2 ≤ j) (hord : β ^ j = 1) :
    wSeq α0 β (j - 1) = 1 := by
  have hS1 : bS β (j - 1) = α0 := by
    have h : β ^ (j - 1) = β⁻¹ := by
      have h2 : β ^ (j - 1) * β = 1 := by
        rw [← pow_succ, show j - 1 + 1 = j from by omega, hord]
      exact eq_inv_of_mul_eq_one_left h2
    rw [bS, h, inv_inv, add_comm]; exact hβα
  rw [wSeq_eq, hS1, div_self hα0, one_pow]

/-! ## The §2 (14) recursion for the exponents `d_i` -/

lemma kElF_one (fr : CoarseFrame H Q t n) : kElF fr (1 : ↥(FX n)) = 1 := by
  apply fr.κ_injective
  rw [kElF_kappa, map_one]
  rfl

/-- `d_1 = ζ` (§2 (11)). -/
lemma dSeq_one (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (lam : ℕ → ↥(FX n))
    (h : fval (lam 1) = 1) : dSeq hS fr lam 1 = fr.ζ := by
  have h1 : lam 1 = 1 := fval_eq_one_iff.mp h
  rw [dSeq, h1, pow_one, map_one, kElF_one, mul_one]

/-- **(14)**, recursion form: `d_{i+1} = d_i · ζ a^{-2} = d_i · zetaExp u_{i+1}`, given the
recursion `λ_{i+1} = λ_i u_{i+1}^{-2}` for the `F*`-coordinates. -/
lemma dSeq_succ (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (lam : ℕ → ↥(FX n))
    (U : ↥(FX n)) (i : ℕ)
    (h : fval (lam (i + 1)) = fval (lam i) * (fval U)⁻¹ * (fval U)⁻¹) :
    dSeq hS fr lam (i + 1) = dSeq hS fr lam i * zetaExp hS fr U := by
  apply fr.κ_injective
  have hlam : lam (i + 1) = lam i * U⁻¹ * U⁻¹ :=
    fval_inj (by rw [h]; simp [fval_mul, fval_inv])
  have htau : tau hS fr (lam (i + 1))
      = tau hS fr (lam i) * (tau hS fr U)⁻¹ * (tau hS fr U)⁻¹ := by
    rw [hlam]; simp only [map_mul, map_inv]
  rw [dSeq_kappa, map_mul, dSeq_kappa]
  unfold zetaExp
  simp only [map_mul, map_inv, kElF_kappa, htau]
  rw [Units.ext_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val]
  ring

/-- The "stopping" form of (14): at an index with `λ = 1` the exponent is the corresponding
power of `ζ`. -/
lemma dSeq_stop (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (lam : ℕ → ↥(FX n))
    {j : ℕ} (h : fval (lam j) = 1) : dSeq hS fr lam j = fr.ζ ^ j := by
  have h1 : lam j = 1 := fval_eq_one_iff.mp h
  rw [dSeq, h1, map_one, kElF_one, mul_one]

end Work.PSU3.StageB.Omega
