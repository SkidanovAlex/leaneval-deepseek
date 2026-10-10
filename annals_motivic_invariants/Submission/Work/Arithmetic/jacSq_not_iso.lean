import Mathlib
import Submission.Work.Arithmetic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Arithmetic

/-
CORE RESULT (Shinder-Zhang, "L-equivalence for degree five elliptic curves",
Lemma 2.7 / `lem:iso`) in the vocabulary of `Work.Arithmetic.Torsor`.

Setup.  `T : Work.Arithmetic.Torsor 𝕜` packages a genus-one curve over `𝕜`: an elliptic
curve `T.E/𝕜` with `j ≠ 1728` (the Jacobian), the Weil-Châtelet group `T.W = H¹(𝕜,T.E)`
written multiplicatively, an action `T.act : Aut 𝕜 T.E →* MulAut T.W`, the class
`T.cls : T.W` of the curve, and the hypothesis `T.order_aut : ∀ σ, orderOf σ ∣ 2 ∨
orderOf σ ∣ 6` (Silverman, AEC, Prop. A.1.2 for `j ≠ 1728`).  `T.jacSq` is the curve whose
class is `T.cls ^ (2 : ℤ)`, i.e. `Jac²C`, and `T.IsIso η := ∃ σ, T.act σ T.cls = η` is the
paper's isomorphism criterion (two genus-one curves with the same Jacobian are isomorphic
iff their classes lie in the same `Aut(E)`-orbit; Silverman, AEC, Exercise 10.4).

Route (all group theory, no geometry):
1. Given `⟨σ, hσ⟩ : T.IsIso T.jacSq.cls`, put `f := T.act σ`, so `f T.cls = T.cls ^ 2`.
2. By induction on `n`, `(f ^ n) T.cls = T.cls ^ (2 ^ n)`.
3. With `k = orderOf σ`: `σ ^ k = 1`, so `f ^ k = 1` (`map_pow`), hence
   `T.cls ^ (2 ^ k) = T.cls`, hence (`pow_sub_one`, `orderOf_dvd_iff_pow_eq_one`)
   `T.period = orderOf T.cls ∣ 2 ^ k - 1`, i.e. `5 ∣ 2 ^ k - 1` by `h5`.
4. `5 ∣ 2 ^ k - 1` gives `(2 : ZMod 5) ^ k = 1`, and `orderOf (2 : ZMod 5) = 4`, so
   `4 ∣ k` (`orderOf_dvd_iff_pow_eq_one`).
5. `k ≠ 0` because `k ∣ 2` or `k ∣ 6` by `T.order_aut σ`.
6. `4 ∣ orderOf σ` together with `T.order_aut σ` gives `4 ∣ 2` or `4 ∣ 6`: contradiction.
-/
theorem jacSq_not_iso {𝕜 : Type} [Field 𝕜] (T : Work.Arithmetic.Torsor 𝕜)
    (h5 : T.period = 5) : ¬ T.IsIso T.jacSq.cls := by
  rintro ⟨σ, hσ⟩
  set f : MulAut T.W := T.act σ with hf
  have hfcls : f T.cls = T.cls ^ 2 := by
    simpa [hf] using hσ
  -- Step 2: `(f ^ n) T.cls = T.cls ^ (2 ^ n)`.
  have hpow : ∀ n : ℕ, (f ^ n) T.cls = T.cls ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (f ^ (n+1)) T.cls = f ((f^n) T.cls) := by rw [pow_succ', MulAut.mul_apply]
        _ = f (T.cls ^ (2^n)) := by rw [ih]
        _ = (f T.cls) ^ (2^n) := by rw [map_pow]
        _ = (T.cls ^ 2) ^ (2^n) := by rw [hfcls]
        _ = T.cls ^ (2 * 2^n) := by rw [pow_mul]
        _ = T.cls ^ (2^(n+1)) := by rw [pow_succ']
  -- Step 3: `f ^ k = 1`, hence `T.cls ^ (2 ^ k) = T.cls`.
  have hfk : f ^ orderOf σ = 1 := by
    have h := map_pow T.act σ (orderOf σ)
    rw [pow_orderOf_eq_one, map_one] at h
    simpa [hf] using h.symm
  have hcls_pow : T.cls ^ (2 ^ orderOf σ) = T.cls := by
    have h := hpow (orderOf σ)
    rw [hfk] at h
    rw [MulAut.one_apply] at h
    exact h.symm
  -- `5 ∣ 2 ^ k - 1`.
  have hdvd : 5 ∣ 2 ^ orderOf σ - 1 := by
    have hone : T.cls ^ (2 ^ orderOf σ - 1) = 1 := by
      have hge : 1 ≤ 2 ^ orderOf σ := Nat.one_le_two_pow
      have hmul : T.cls ^ (2 ^ orderOf σ - 1) * T.cls = T.cls := by
        rw [← pow_succ, Nat.sub_add_cancel hge]
        exact hcls_pow
      exact mul_right_cancel (by rw [one_mul]; exact hmul)
    have h5' : orderOf T.cls = 5 := h5
    have h := (orderOf_dvd_iff_pow_eq_one (x := T.cls) (n := 2 ^ orderOf σ - 1)).mpr hone
    rwa [h5'] at h
  -- Step 4: `(2 : ZMod 5) ^ k = 1`, hence `4 ∣ k`.
  have hzmod : (2 : ZMod 5) ^ orderOf σ = 1 := by
    have h1 : ((2 ^ orderOf σ : ℕ) : ZMod 5) = 1 := by
      have hzero : ((2 ^ orderOf σ - 1 : ℕ) : ZMod 5) = 0 := by
        rw [CharP.cast_eq_zero_iff (ZMod 5) 5]
        exact hdvd
      calc ((2 ^ orderOf σ : ℕ) : ZMod 5)
          = (((2^orderOf σ - 1) + 1 : ℕ) : ZMod 5) := by
            rw [Nat.sub_add_cancel Nat.one_le_two_pow]
        _ = ((2^orderOf σ - 1 : ℕ) : ZMod 5) + 1 := by push_cast; ring
        _ = 0 + 1 := by rw [hzero]
        _ = 1 := by ring
    rwa [Nat.cast_pow] at h1
  have h2ord : orderOf (2 : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (show 0 < 4 by norm_num)]
    refine ⟨by decide, ?_⟩
    intro m hm4 hm0
    interval_cases m <;> decide
  have h4 : 4 ∣ orderOf σ := by
    have h := (orderOf_dvd_iff_pow_eq_one (x := (2 : ZMod 5)) (n := orderOf σ)).mpr hzmod
    rwa [h2ord] at h
  -- Step 6: `4 ∣ orderOf σ` together with `orderOf σ ∣ 2` or `∣ 6` is impossible.
  rcases T.order_aut σ with h | h
  · exact absurd (dvd_trans h4 h) (by norm_num)
  · exact absurd (dvd_trans h4 h) (by norm_num)

end Work.Arithmetic
