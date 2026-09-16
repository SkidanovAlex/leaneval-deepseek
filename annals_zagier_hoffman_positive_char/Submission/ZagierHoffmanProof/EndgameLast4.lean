import Submission.ZagierHoffmanProof.EndgameLast3

/-!
# SESSION 362 — the last case `w = 2q-2`: the `qℤ`-support of `num`

`PLAN.md` §«SESSION 362».  `num = σ V - N·D`; the `θ`-coefficients of `σ V` live on `qℤ`
(`(σV).coeff n = (V.coeff n)^q`) and those of `N·D` on `{0,q}`, so `num ∈ F_q[θ^q][X]` — the
hypothesis `hnum` of the two reads `D_one_eq`/`D_zero_eq`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial
open scoped WithZero Classical

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The cast of `|F|` into the ambient field vanishes. -/
lemma natCast_card_eq_zero_ambient : ((Nat.card F : ℕ) : Ambient F) = 0 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  rw [← map_natCast (algebraMap F (Ambient F)) (Nat.card F), ← Fintype.card_eq_nat_card,
    Nat.cast_card_eq_zero F, map_zero]

/-- ★★ **The `θ`-support of `x^q` for `x ∈ A_0` lies in `qℤ`.** -/
lemma coeffNu_pow_card_of_mem_ambA_zero {x : Ambient F} (hx : x ∈ ambA F 0) (m : ℕ) :
    coeffNu F 0 m (x ^ Nat.card F)
      = if Nat.card F ∣ m then coeffNu F 0 (m / Nat.card F) x else 0 := by
  obtain ⟨p, hp⟩ := (mem_ambA_iff F 0 x).mp hx
  rw [ambThetaNu_zero F] at hp
  have hq : 0 < Nat.card F := Nat.pos_of_ne_zero (FrobPow.ne_zero (Ambient F) (q := Nat.card F))
  have hxpow : x ^ Nat.card F
      = (Polynomial.expand F (Nat.card F) p).eval₂ (algebraMap F (Ambient F)) (ambTheta F) := by
    rw [Polynomial.expand_eq_comp_X_pow, Polynomial.eval₂_comp, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, ← hp, ← eval₂_theta_pow_card]
  rw [hxpow,
    coeffNu_eq_of_eval F
      ((mem_ambA_iff F 0 _).mpr ⟨Polynomial.expand F (Nat.card F) p,
        by rw [ambThetaNu_zero F]⟩)
      (p := Polynomial.expand F (Nat.card F) p) (by rw [ambThetaNu_zero F]) m,
    coeffNu_eq_of_eval F hx (p := p) hp (m / Nat.card F),
    Polynomial.coeff_expand hq p m]
  by_cases h : Nat.card F ∣ m
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_zero]

lemma coeffNu_polyTwist_one_eq_zero {V : Polynomial (Ambient F)}
    (hV : ∀ n, V.coeff n ∈ ambA F 0) {j : ℕ} (hj : ¬ Nat.card F ∣ j) (n : ℕ) :
    coeffNu F 0 j ((polyTwist (q := Nat.card F) 1 V).coeff n) = 0 := by
  rw [polyTwist_one_coeff F V n, coeffNu_pow_card_of_mem_ambA_zero F (hV n) j, if_neg hj]

lemma coeffNu_mul_eq_zero_of_supp {N D : Polynomial (Ambient F)}
    (hNa : ∀ n, N.coeff n ∈ ambA F 0)
    (hN : ∀ n j, ¬ Nat.card F ∣ j → coeffNu F 0 j (N.coeff n) = 0)
    (hD : ∀ n, D.coeff n ∈ ambF F) (n j : ℕ) (hj : ¬ Nat.card F ∣ j) :
    coeffNu F 0 j ((N * D).coeff n) = 0 := by
  rw [Polynomial.coeff_mul,
    coeffNu_sum F _ (fun b _ => ambA_mul_mem F (hNa b.1) (mem_ambA_zero_of_mem_ambF (hD b.2))) j]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [mul_comm (N.coeff b.1) (D.coeff b.2),
    coeffNu_mul_of_constant F (mem_ambA_zero_of_mem_ambF (hD b.2)) (hNa b.1)
      (fun i hi => coeffNu_eq_zero_of_mem_ambF F (hD b.2) hi) j,
    coeffNu_zero_of_mem_ambF F (hD b.2), hN b.1 j hj, mul_zero]

/-- ★★★★★ **`num ∈ F_q[θ^q][X]`**: every `θ`-coefficient of `num` of degree outside `qℤ` vanishes. -/
theorem tp_num_eq_zero {V num N D : Polynomial (Ambient F)}
    (hV : ∀ n, V.coeff n ∈ ambA F 0) (hnuma : ∀ n, num.coeff n ∈ ambA F 0)
    (hNa : ∀ n, N.coeff n ∈ ambA F 0)
    (hrec : polyTwist (q := Nat.card F) 1 V = num + N * D)
    (hN : ∀ n j, ¬ Nat.card F ∣ j → coeffNu F 0 j (N.coeff n) = 0)
    (hD : ∀ n, D.coeff n ∈ ambF F) :
    ∀ j, ¬ Nat.card F ∣ j → tp F num j = 0 := by
  intro j hj
  ext n
  rw [tp_coeff, Polynomial.coeff_zero]
  have h3 : (polyTwist (q := Nat.card F) 1 V).coeff n = num.coeff n + (N * D).coeff n := by
    rw [hrec, Polynomial.coeff_add]
  have h5 : coeffNu F 0 j (num.coeff n) + coeffNu F 0 j ((N * D).coeff n) = 0 := by
    rw [← coeffNu_add F (hnuma n)
        (coeff_mul_mem_ambA hNa (fun m => mem_ambA_zero_of_mem_ambF (hD m)) n),
      ← h3, coeffNu_polyTwist_one_eq_zero F hV hj n]
  rw [coeffNu_mul_eq_zero_of_supp F hNa hN hD n j hj, add_zero] at h5
  exact h5

end ZagierHoffmanPositiveChar
