import Mathlib
import Submission.Work.LinnikAreas.area1
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_charSum_order_of_cubefree

namespace Work.LinnikAreas.l31free

/-- Burgess/HB Lemma 2.1 with `k = 3`, uniform in the modulus, for **primitive real**
characters (`χ ^ 2 = 1`): `‖Σ_{N<n≤N+H} χ(n)‖ ≤ C · q^{1/9+ε} · H^{2/3}` for `H ≤ q`, with an
absolute constant `C`.  Intended namespace `Work.LinnikAreas.l31free`.  The file should import
`Submission.Work.LinnikAreas.area1` (for `cubefree_charSum_all_k`, sorry-free) and
`Submission.Commons.NumberTheory.DirichletCharacter.burgess_charSum_order_of_cubefree`, both of
which are sorry-free.  Derivation: `cubefree_charSum_all_k ε hε 3 (by norm_num)` (cube-free input;
`((3:ℝ)+1)/(4*(3:ℝ)^2) = 1/9` and `1 - 1/3 = 2/3`) feeds
`burgess_charSum_order_of_cubefree (ε := ε) hε 3 (by norm_num)`, which yields for every modulus
`‖Σ‖ ≤ C₁ · (orderOf χ)^{3/(2·3)} · q^{1/9+ε} · H^{2/3}`; `χ ^ 2 = 1` implies `orderOf χ ∣ 2`
(`orderOf_dvd_iff_pow_eq_one`), hence `orderOf χ ≤ 2`, so `(orderOf χ)^{1/2} ≤ 2^{1/2}` and
`C` may be taken to be `2 * C₁`. -/
theorem hb_real_charSum {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖
          ≤ C * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3) := by
  -- HB Lemma 2.1 for cube-free moduli, every `k` (sorry-free)
  obtain ⟨CB, hCB, hB0⟩ := cubefree_charSum_all_k ε hε 3 (by norm_num)
  -- HB Lemmas 2.3/2.4: the cubeful part contributes `(orderOf χ)^{3/(2k)}`
  obtain ⟨C₁, hC₁, h₁⟩ :=
    Commons.NumberTheory.DirichletCharacter.burgess_charSum_order_of_cubefree (ε := ε) hε 3 (by norm_num) hCB
      (fun {u} _inst ψ hψ hψ1 hcf N H hN hH hHu => hB0 hcf ψ hψ hψ1 hN hH hHu)
  -- at `k = 3` the exponents specialize as `3/(2·3) = 1/2`, `4/(4·9) = 1/9`, `1 - 1/3 = 2/3`
  have hexp1 : 3 / (2 * (((3 : ℕ)) : ℝ)) = (1 : ℝ) / 2 := by norm_num
  have hexp2 : (((((3 : ℕ)) : ℝ) + 1) / (4 * ((((3 : ℕ)) : ℝ)) ^ 2) + ε)
      = (1 : ℝ) / 9 + ε := by norm_num
  have hexp3 : (1 - 1 / (((3 : ℕ)) : ℝ)) = (2 : ℝ) / 3 := by norm_num
  refine ⟨2 * C₁, by positivity, ?_⟩
  intro q _inst χ hp hχ hsq N H hN hH hHq
  -- `χ ^ 2 = 1` forces `orderOf χ ∣ 2`
  have hdvd : orderOf χ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
  have hle : orderOf χ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hleR : (orderOf χ : ℝ) ≤ 2 := by exact_mod_cast hle
  -- hence the order factor is at most `2^(1/2) ≤ 2`
  have hroot : (orderOf χ : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
    calc (orderOf χ : ℝ) ^ ((1 : ℝ) / 2)
        ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hleR (by norm_num)
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hb := h₁ χ hp hχ hN hH hHq
  rw [hexp1, hexp2, hexp3] at hb
  refine hb.trans ?_
  have hqnn : (0 : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 9 + ε) :=
    Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hHnn : (0 : ℝ) ≤ (H : ℝ) ^ ((2 : ℝ) / 3) :=
    Real.rpow_nonneg (Nat.cast_nonneg H) _
  calc C₁ * (orderOf χ : ℝ) ^ ((1 : ℝ) / 2) * (q : ℝ) ^ ((1 : ℝ) / 9 + ε)
        * (H : ℝ) ^ ((2 : ℝ) / 3)
      ≤ C₁ * 2 * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3) := by
        refine mul_le_mul_of_nonneg_right ?_ hHnn
        refine mul_le_mul_of_nonneg_right ?_ hqnn
        exact mul_le_mul_of_nonneg_left hroot (le_of_lt hC₁)
    _ = (2 * C₁) * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3) := by ring

end Work.LinnikAreas.l31free
