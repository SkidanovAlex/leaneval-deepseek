import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.Ulower

/-- Elementary quotient monotonicity: if `0 ≤ a ≤ b` and `0 < q ≤ p` then
`a / p^m ≤ b / q^m` for every `m : ℕ`. -/
private lemma div_pow_le_div_pow_of_le {a b p q : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hp : 0 < p) (hq : 0 < q) (hqp : q ≤ p) (m : ℕ) : a / p ^ m ≤ b / q ^ m := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow, ← inv_pow]
  exact mul_le_mul hab
    (pow_le_pow_left₀ (le_of_lt (inv_pos.mpr hp)) ((inv_le_inv₀ hp hq).mpr hqp) m)
    (pow_nonneg (le_of_lt (inv_pos.mpr hp)) m) (le_trans ha hab)

/-- Multiplying the previous comparison by the (nonnegative) factors `C * E`. -/
private lemma mul_div_pow_le_mul_div_pow {C a b E P Q : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hE : 0 ≤ E) (ha : 0 ≤ a) (hab : a ≤ b) (hP : 0 < P) (hQ : 0 < Q) (hQP : Q ≤ P) :
    C * a * E / P ^ m ≤ C * b * E / Q ^ m := by
  have h := div_pow_le_div_pow_of_le ha hab hP hQ hQP m
  calc C * a * E / P ^ m = (C * E) * (a / P ^ m) := by ring
    _ ≤ (C * E) * (b / Q ^ m) := mul_le_mul_of_nonneg_left h (mul_nonneg hC hE)
    _ = C * b * E / Q ^ m := by ring

/-- **The constant comparison of the `U²`-inverse entry.**  Elementary arithmetic: if
`0 < cmin, δ, D, Ns, L''`, `cmin · δ ≤ η` and `L'' ≤ Amax · Ns`, then for every `K ≥ 1`

`C · cmin^K / Amax^{K-1} · δ^K · (D/Ns)^K · Ns ≤ C · η^K · (D/L'')^K · L''`.

(The ratio of the right to the left side is `(η/(cmin δ))^K · (Amax Ns / L'')^{K-1} ≥ 1`, the two
factors being `≥ 1` because `cmin δ ≤ η` and `L'' ≤ Amax Ns`.)  This is the bookkeeping that
converts the level `cmin·δ` of the `U²`-norm at the support radius `Ns` into the level `η` at the
radius `L''` chosen by the dilation/pigeonhole step. -/
theorem ss_aux_const_compare {K : ℕ} (hK : 1 ≤ K) {C δ η cmin Amax Ns D L'' : ℝ}
    (hC : 0 < C) (hcmin : 0 < cmin) (hAmax : 0 < Amax) (hδ : 0 < δ) (hD : 0 < D)
    (hη : cmin * δ ≤ η) (hNs : 0 < Ns) (hL'' : 0 < L'') (hL''Amax : L'' ≤ Amax * Ns) :
    C * cmin ^ K / Amax ^ (K - 1) * δ ^ K * (D / Ns) ^ K * Ns ≤
      C * η ^ K * (D / L'') ^ K * L'' := by
  -- `K = (K-1) + 1`, so `Ns^K = Ns^(K-1) * Ns` and `L''^K = L''^(K-1) * L''`.
  have hm : K - 1 + 1 = K := Nat.sub_add_cancel hK
  have hNsK : Ns ^ K = Ns ^ (K - 1) * Ns := by rw [← hm]; exact pow_succ Ns (K - 1)
  have hL''K : L'' ^ K = L'' ^ (K - 1) * L'' := by rw [← hm]; exact pow_succ L'' (K - 1)
  have hcd : 0 < cmin * δ := mul_pos hcmin hδ
  -- the two level comparisons
  have hlevel : (cmin * δ) ^ K ≤ η ^ K := pow_le_pow_left₀ (le_of_lt hcd) hη K
  have hP : 0 < Amax * Ns := mul_pos hAmax hNs
  -- both sides in the common normal form `C * (level)^K * D^K / (radius)^(K-1)`
  have hLHS : C * cmin ^ K / Amax ^ (K - 1) * δ ^ K * (D / Ns) ^ K * Ns =
      C * ((cmin * δ) ^ K) * D ^ K / (Amax * Ns) ^ (K - 1) := by
    rw [div_pow, mul_pow, hNsK, mul_pow]
    field_simp
  have hRHS : C * η ^ K * (D / L'') ^ K * L'' = C * η ^ K * D ^ K / L'' ^ (K - 1) := by
    rw [div_pow, hL''K]
    field_simp
  rw [hLHS, hRHS]
  exact mul_div_pow_le_mul_div_pow (le_of_lt hC) (pow_nonneg (le_of_lt hD) K)
    (pow_nonneg (le_of_lt hcd) K) hlevel hP hL'' hL''Amax

end Work.Peluse.Ulower
