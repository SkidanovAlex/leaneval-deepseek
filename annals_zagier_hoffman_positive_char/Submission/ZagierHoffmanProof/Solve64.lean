import Submission.ZagierHoffmanProof.TpTrans
import Submission.ZagierHoffmanProof.Rationality
import Submission.ZagierHoffmanProof.ABPPoly

/-!
# The solvable case `(6.4)` of Ngo Dac's §6: the `q-1` Mahler equation

Dac's equation (6.4) for the surviving pair `(w), (k, q-1)` of Theorem 6.2 reads, in the
`Positive` (Frobenius-twisted) normalisation of the workspace,

  `δ ^{(1)} = (δ + A)·(t - θ^q)^{q-1}`

with `A` a polynomial with `F_q`-coefficients.  Its solutions are exactly
`A = f·(t^q - t)`, `δ = f·(θ^q - t^q)` with `f` again of `F_q`-coefficients, which is what the
final degree comparison of the paper needs.

The key lemma is that a non-zero polynomial cannot satisfy `δ^{(1)} = δ·(t-θ^q)^m` for `m ≥ 1`
(because the Frobenius twist preserves the `t`-degree while the right-hand side is `m` degrees
larger).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The Frobenius power of a linear polynomial -/

lemma X_sub_C_pow_card (a : Ambient F) :
    (Polynomial.X - Polynomial.C a) ^ Nat.card F
      = Polynomial.X ^ Nat.card F - Polynomial.C (a ^ Nat.card F) := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hnprime, hcard⟩ := FiniteField.card (F) (ringChar F)
  have hcard' : Nat.card F = ringChar F ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hcard
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨hnprime⟩
  have h := sub_pow_char_pow (x := Polynomial.X) (y := Polynomial.C a) (n : ℕ)
    (p := ringChar F)
  simpa only [hcard', Polynomial.C_pow] using h

/-! ## §1b. Computation rules for the Frobenius twist -/

section TwistSimp

variable {q : ℕ} [FrobPow (Ambient F) q]

@[simp] lemma polyTwist_zero (k : ℕ) : polyTwist (q := q) k (0 : Polynomial (Ambient F)) = 0 := by
  change polyTwistHom (q := q) k 0 = 0
  exact map_zero _

@[simp] lemma polyTwist_one (k : ℕ) : polyTwist (q := q) k (1 : Polynomial (Ambient F)) = 1 := by
  change polyTwistHom (q := q) k 1 = 1
  exact map_one _

@[simp] lemma polyTwist_add (k : ℕ) (p r : Polynomial (Ambient F)) :
    polyTwist (q := q) k (p + r) = polyTwist (q := q) k p + polyTwist (q := q) k r := by
  change polyTwistHom (q := q) k (p + r) = _
  exact map_add _ _ _

@[simp] lemma polyTwist_sub (k : ℕ) (p r : Polynomial (Ambient F)) :
    polyTwist (q := q) k (p - r) = polyTwist (q := q) k p - polyTwist (q := q) k r := by
  change polyTwistHom (q := q) k (p - r) = _
  exact map_sub _ _ _

@[simp] lemma polyTwist_mul (k : ℕ) (p r : Polynomial (Ambient F)) :
    polyTwist (q := q) k (p * r) = polyTwist (q := q) k p * polyTwist (q := q) k r := by
  change polyTwistHom (q := q) k (p * r) = _
  exact map_mul _ _ _

@[simp] lemma polyTwist_X (k : ℕ) :
    polyTwist (q := q) k (Polynomial.X : Polynomial (Ambient F)) = Polynomial.X := by
  change polyTwistHom (q := q) k Polynomial.X = Polynomial.X
  rw [polyTwistHom_apply, Polynomial.map_X]

@[simp] lemma polyTwist_C (k : ℕ) (a : Ambient F) :
    polyTwist (q := q) k (Polynomial.C a) = Polynomial.C (a ^ (q ^ k)) := by
  change polyTwistHom (q := q) k (Polynomial.C a) = Polynomial.C (a ^ (q ^ k))
  rw [polyTwistHom_apply, Polynomial.map_C, frobPowHom_apply]

@[simp] lemma polyTwist_pow (k : ℕ) (p : Polynomial (Ambient F)) (n : ℕ) :
    polyTwist (q := q) k (p ^ n) = polyTwist (q := q) k p ^ n := by
  change polyTwistHom (q := q) k (p ^ n) = _
  exact map_pow _ _ _

end TwistSimp

/-! ## §2. The Frobenius twist preserves the `t`-degree -/

lemma polyTwist_one_natDegree (p : Polynomial (Ambient F)) :
    (polyTwist (q := Nat.card F) 1 p).natDegree = p.natDegree := by
  rw [polyTwist, polyTwistHom_apply]
  exact Polynomial.natDegree_map_eq_of_injective (frobPowHom_injective (F := F) 1) p

/-- A polynomial is fixed by the Frobenius twist iff its coefficients lie in `F_q`. -/
lemma polyTwist_one_eq_self_iff (p : Polynomial (Ambient F)) :
    polyTwist (q := Nat.card F) 1 p = p ↔ ∀ n, p.coeff n ∈ ambF F := by
  constructor
  · intro h n
    rw [mem_ambF_iff]
    have h1 := congrArg (fun r : Polynomial (Ambient F) => r.coeff n) h
    simpa only [polyTwist, polyTwistHom_apply, Polynomial.coeff_map, frobPowHom_apply,
      pow_one] using h1
  · intro h
    ext n
    rw [polyTwist, polyTwistHom_apply, Polynomial.coeff_map, frobPowHom_apply, pow_one]
    exact (mem_ambF_iff F (p.coeff n)).mp (h n)

/-! ## §3. The Mahler equation `δ^{(1)} = δ·(t-θ^q)^m` has only the trivial solution -/

theorem mahler_eq_zero {δ : Polynomial (Ambient F)} {m : ℕ} (hm : 1 ≤ m)
    (h : polyTwist (q := Nat.card F) 1 δ
      = δ * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F)) ^ m) :
    δ = 0 := by
  by_contra h0
  have hL : (polyTwist (q := Nat.card F) 1 δ).natDegree = δ.natDegree :=
    polyTwist_one_natDegree F δ
  rw [h, Polynomial.natDegree_mul h0 (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)),
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at hL
  omega

/-! ## §4. Coprimality of `t^q - t` and `θ^q - t^q` -/

lemma isCoprime_X_sub_C_theta (q : ℕ) (hq : q = Nat.card F) :
    IsCoprime (Polynomial.X ^ q - Polynomial.X)
      (Polynomial.X - Polynomial.C (ambTheta F)) := by
  subst hq
  have hne : (ambTheta F) ^ Nat.card F - ambTheta F ≠ 0 :=
    sub_ne_zero.mpr (ambTheta_pow_ne_ambTheta F)
  set Q : Polynomial (Ambient F) := (Polynomial.X ^ Nat.card F - Polynomial.X) /ₘ
    (Polynomial.X - Polynomial.C (ambTheta F)) with hQ
  have hmod := Polynomial.modByMonic_add_div (Polynomial.X ^ Nat.card F - Polynomial.X)
    (Polynomial.X - Polynomial.C (ambTheta F))
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at hmod
  have hev : Polynomial.eval (ambTheta F) (Polynomial.X ^ Nat.card F - Polynomial.X)
      = (ambTheta F) ^ Nat.card F - ambTheta F := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  rw [hev, ← hQ] at hmod
  have h2 : Polynomial.C ((ambTheta F) ^ Nat.card F - ambTheta F)
      = (Polynomial.X ^ Nat.card F - Polynomial.X)
        - (Polynomial.X - Polynomial.C (ambTheta F)) * Q := by
    rw [← hmod]; ring
  refine ⟨Polynomial.C (((ambTheta F) ^ Nat.card F - ambTheta F)⁻¹),
    -(Polynomial.C (((ambTheta F) ^ Nat.card F - ambTheta F)⁻¹) * Q), ?_⟩
  have h1 : Polynomial.C (((ambTheta F) ^ Nat.card F - ambTheta F)⁻¹)
      * Polynomial.C ((ambTheta F) ^ Nat.card F - ambTheta F) = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hne, Polynomial.C_1]
  calc Polynomial.C (((ambTheta F) ^ Nat.card F - ambTheta F)⁻¹)
        * (Polynomial.X ^ Nat.card F - Polynomial.X)
        + (-(Polynomial.C (((ambTheta F) ^ Nat.card F - ambTheta F)⁻¹) * Q))
          * (Polynomial.X - Polynomial.C (ambTheta F))
      = Polynomial.C (((ambTheta F) ^ Nat.card F - ambTheta F)⁻¹)
        * ((Polynomial.X ^ Nat.card F - Polynomial.X)
          - (Polynomial.X - Polynomial.C (ambTheta F)) * Q) := by ring
    _ = Polynomial.C (((ambTheta F) ^ Nat.card F - ambTheta F)⁻¹)
        * Polynomial.C ((ambTheta F) ^ Nat.card F - ambTheta F) := by rw [← h2]
    _ = 1 := h1

/-! ## §5. The solution of Dac's (6.4) -/

theorem solve_s2 {δ A : Polynomial (Ambient F)}
    (hA : ∀ n, A.coeff n ∈ ambF F)
    (h : polyTwist (q := Nat.card F) 1 δ
      = (δ + A) * (Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F))
          ^ (Nat.card F - 1)) :
    ∃ f : Polynomial (Ambient F), (∀ n, f.coeff n ∈ ambF F) ∧
      A = f * (Polynomial.X ^ Nat.card F - Polynomial.X) ∧
      δ = f * (Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F) := by
  have hq2 : 2 ≤ Nat.card F := carlitz_card_ge_two F
  set P : Polynomial (Ambient F) := Polynomial.X ^ Nat.card F - Polynomial.X with hP
  set D : Polynomial (Ambient F) :=
    Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X ^ Nat.card F with hD
  set Y : Polynomial (Ambient F) :=
    Polynomial.X - Polynomial.C ((ambTheta F) ^ Nat.card F) with hY
  have hPmem : ∀ n, P.coeff n ∈ ambF F := by
    intro n
    rw [hP, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
    exact (ambF F).sub_mem (ite_one_zero_mem_ambF F _) (ite_one_zero_mem_ambF F _)
  have hPfix : polyTwist (q := Nat.card F) 1 P = P := (polyTwist_one_eq_self_iff F P).mpr hPmem
  have hAf : polyTwist (q := Nat.card F) 1 A = A := (polyTwist_one_eq_self_iff F A).mpr hA
  have hP0 : P ≠ 0 := by
    intro hh
    have h1 := congrArg (fun r : Polynomial (Ambient F) => r.coeff (Nat.card F)) hh
    rw [hP] at h1
    simp only [Polynomial.coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, if_pos rfl] at h1
    have hq1 : ¬ (1 = Nat.card F) := by omega
    simp only [hq1, if_false, sub_zero] at h1
    exact one_ne_zero h1
  -- the auxiliary solution `(P, D)`
  have hD1 : polyTwist (q := Nat.card F) 1 D
      = Polynomial.C ((ambTheta F) ^ (Nat.card F * Nat.card F))
        - Polynomial.X ^ Nat.card F := by
    rw [hD]
    rw [polyTwist_sub, polyTwist_pow, polyTwist_X, polyTwist_C, pow_one, ← pow_mul]
  have hYq : Y ^ Nat.card F
      = Polynomial.X ^ Nat.card F
        - Polynomial.C ((ambTheta F) ^ (Nat.card F * Nat.card F)) := by
    rw [hY]
    have h1 := X_sub_C_pow_card F ((ambTheta F) ^ Nat.card F)
    rw [h1, ← pow_mul]
  have haux : polyTwist (q := Nat.card F) 1 D = (D + P) * Y ^ (Nat.card F - 1) := by
    have hsum : D + P = Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X := by
      rw [hD, hP]; ring
    have hneg : Polynomial.C ((ambTheta F) ^ Nat.card F) - Polynomial.X = -Y := by
      rw [hY]; ring
    calc polyTwist (q := Nat.card F) 1 D
        = Polynomial.C ((ambTheta F) ^ (Nat.card F * Nat.card F))
          - Polynomial.X ^ Nat.card F := hD1
      _ = -(Y ^ Nat.card F) := by rw [hYq]; ring
      _ = -(Y * Y ^ (Nat.card F - 1)) := by
            conv_lhs => rw [show Nat.card F = Nat.card F - 1 + 1 from by omega, pow_succ']
      _ = (D + P) * Y ^ (Nat.card F - 1) := by rw [hsum, hneg]; ring
  -- the auxiliary `δ₀`
  have hδ0 : polyTwist (q := Nat.card F) 1 (P * δ - A * D)
      = (P * δ - A * D) * Y ^ (Nat.card F - 1) := by
    have hmap : polyTwist (q := Nat.card F) 1 (P * δ - A * D)
        = P * polyTwist (q := Nat.card F) 1 δ
          - A * polyTwist (q := Nat.card F) 1 D := by
      rw [polyTwist_sub, polyTwist_mul, polyTwist_mul, hPfix, hAf]
    rw [hmap, h, haux]
    ring
  have hzero : P * δ - A * D = 0 := mahler_eq_zero F (by omega) hδ0
  have hPD : P * δ = A * D := sub_eq_zero.mp hzero
  -- coprimality
  have hcop : IsCoprime P D := by
    have h1 : IsCoprime (Polynomial.X ^ Nat.card F - Polynomial.X)
        (Polynomial.X - Polynomial.C (ambTheta F)) :=
      isCoprime_X_sub_C_theta F (Nat.card F) rfl
    have h2 : IsCoprime (Polynomial.X ^ Nat.card F - Polynomial.X)
        (Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) := by
      have h3 := h1.pow_right (n := Nat.card F)
      rwa [X_sub_C_pow_card F (ambTheta F)] at h3
    have h4 : D = -(Polynomial.X ^ Nat.card F - Polynomial.C ((ambTheta F) ^ Nat.card F)) := by
      rw [hD]; ring
    rw [hP, h4]
    exact h2.neg_right
  obtain ⟨f, hf⟩ := hcop.dvd_of_dvd_mul_right ⟨δ, hPD.symm⟩
  have hfmem : ∀ n, f.coeff n ∈ ambF F := by
    have h1 : polyTwist (q := Nat.card F) 1 A = polyTwist (q := Nat.card F) 1 (P * f) := by
      rw [hf]
    rw [polyTwist_mul, hPfix, hAf, hf] at h1
    have h2 : polyTwist (q := Nat.card F) 1 f = f := (mul_left_cancel₀ hP0 h1).symm
    exact (polyTwist_one_eq_self_iff F f).mp h2
  refine ⟨f, hfmem, ?_, ?_⟩
  · rw [hP] at hf
    exact hf.trans (by ring)
  · have h3 : P * δ = P * (f * D) := by
      calc P * δ = A * D := hPD
        _ = P * f * D := by rw [hf]
        _ = P * (f * D) := by ring
    exact mul_left_cancel₀ hP0 h3
end ZagierHoffmanPositiveChar
