import Mathlib
import Submission.Work.Analysis.EndVar.Defs
import Submission.Work.Analysis.IonescuWainger.Pset

/-!
# The "large `N`" bookkeeping of §5 (Krause--Mirek--Tao)

The §5 reduction of the main variational estimate works at a length scale `N` that is large
compared with all the structural parameters: the modulus `Q` of the underlying system, the height
scale `l` of the Ionescu--Wainger frequency set (through its common denominator
`Q_{≤l} = iwQl ρ l`), the degree `d = P.natDegree` of the polynomial, and the accuracy `ε` of the
final `⟨Log N⟩^{-c/ρ}` decay.  This file provides the existence of that threshold `N₀`:

* `BileLargeN` — for `N ≥ N₀` one has `Q ≤ N`, together with

  `2^{-Log N + l} · Q · Q_{≤l} < 1/4`,   `2^{d(-Log N + l)} · Q · Q_{≤l} < 1/4`,
  `⟨Log N⟩^{-c/ρ} ≤ ε`,

  where `Log N = log₂ max(N,2) = Work.Analysis.EndVar.logN N`.

The two ingredients are the elementary estimates

* `logN_ge_of_pow_le` : `2 ^ K ≤ N` implies `K ≤ Log N` (mirror of `logN_le_of_le_pow`),
* `rpow_neg_le_of_le_inv` : since `t ↦ t^{-c/ρ}` is decreasing on `(0,∞)`, a point above the
  threshold `ε^{-ρ/c}` lands below `ε`.

Both bounds on the "geometric" factors are obtained by choosing `K` so large that
`4 · 2^l · Q · Q_{≤l} < 2^K` and then using that `-(Log N) + l ≤ -K + l ≤ 0` once `Log N ≥ l`; for
the second one, `d ≥ 1` and a non-positive exponent forces `2^{dx} ≤ 2^x`.
-/

namespace Work.KMTPlan.A6

/-- The logarithmic scale `Log N = log₂ max(N,2)` dominates `K` as soon as `2 ^ K ≤ N`
(the `max N 2` in the definition of `logN` takes care of the degenerate cases `N ≤ 1`).
Mirror image of `Work.KMTPlan.A6.logN_le_of_le_pow`. -/
theorem logN_ge_of_pow_le {K N : ℕ} (hN : 2 ^ K ≤ N) :
    (K : ℤ) ≤ Work.Analysis.EndVar.logN N := by
  have hle : 2 ^ K ≤ max N 2 := le_trans hN (le_max_left N 2)
  have hne : max N 2 ≠ 0 := by omega
  have hlog : K ≤ Nat.log 2 (max N 2) :=
    (Nat.le_log_iff_pow_le (b := 2) (x := K) (y := max N 2) (by norm_num) hne).mpr hle
  simp only [Work.Analysis.EndVar.logN]
  exact_mod_cast hlog

/-- The function `t ↦ t ^ (-(c/ρ))` is decreasing on the positive half-line: any `x` above the
threshold `ε ^ (-(ρ/c))` (with `ε, c, ρ > 0`) satisfies `x ^ (-(c/ρ)) ≤ ε`. -/
theorem rpow_neg_le_of_le_inv {ε c ρ x : ℝ} (hε : 0 < ε) (hc : 0 < c) (hρ : 0 < ρ)
    (hx : ε ^ (-(ρ / c)) ≤ x) : x ^ (-(c / ρ)) ≤ ε := by
  have hpos : 0 < ε ^ (-(ρ / c)) := Real.rpow_pos_of_pos hε _
  have hexp : -(ρ / c) * (-(c / ρ)) = 1 := by field_simp
  have hz : -(c / ρ) ≤ 0 := by
    have : 0 < c / ρ := div_pos hc hρ
    linarith
  calc x ^ (-(c / ρ)) ≤ (ε ^ (-(ρ / c))) ^ (-(c / ρ)) :=
        Real.rpow_le_rpow_of_nonpos hpos hx hz
    _ = ε ^ ((-(ρ / c)) * (-(c / ρ))) := (Real.rpow_mul hε.le _ _).symm
    _ = ε ^ (1 : ℝ) := by rw [hexp]
    _ = ε := Real.rpow_one ε

/-- **Large `N`**: for all sufficiently large `N` the length scale `N` dominates the modulus `Q`,
the two geometric factors `2^{-Log N + l} · Q · Q_{≤l}` and `2^{d(-Log N + l)} · Q · Q_{≤l}` are
`< 1/4`, and `⟨Log N⟩^{-c/ρ} ≤ ε`. -/
theorem BileLargeN (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree)
    (ρ : ℝ) (hρ : 0 < ρ) (l : ℕ) (c : ℝ) (hc : 0 < c)
    {Q : ℕ} [NeZero Q] (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Q ≤ N ∧
      (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N) + (l : ℤ)) *
          ((Q : ℝ) * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ)) < 1 / 4 ∧
      (2 : ℝ) ^ ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ))) *
          ((Q : ℝ) * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ)) < 1 / 4 ∧
      (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ)) ≤ ε := by
  set M : ℝ := (Q : ℝ) * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ) with hM
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  -- the threshold exponent `K`
  obtain ⟨K₁, hK₁⟩ := exists_nat_ge (max (max (l : ℝ) (ε ^ (-(ρ / c)))) 1)
  obtain ⟨K₂, hK₂⟩ := pow_unbounded_of_one_lt (4 * (2 : ℝ) ^ l * M) (by norm_num : (1 : ℝ) < 2)
  set K : ℕ := max K₁ K₂ with hK
  refine ⟨max Q (2 ^ K), ?_⟩
  intro N hN
  have hQN : Q ≤ N := le_trans (le_max_left _ _) hN
  have hpowN : 2 ^ K ≤ N := le_trans (le_max_right _ _) hN
  have hL : (K : ℤ) ≤ Work.Analysis.EndVar.logN N := logN_ge_of_pow_le hpowN
  have hK1K : K₁ ≤ K := le_max_left _ _
  have hK2K : K₂ ≤ K := le_max_right _ _
  have hlK1 : (l : ℝ) ≤ (K₁ : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hK₁
  have hepsK1 : ε ^ (-(ρ / c)) ≤ (K₁ : ℝ) :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hK₁)
  have hlK1nat : l ≤ K₁ := by exact_mod_cast hlK1
  have hlK : (l : ℤ) ≤ (K : ℤ) := by exact_mod_cast (le_trans hlK1nat hK1K)
  have h2K : 4 * (2 : ℝ) ^ l * M < (2 : ℝ) ^ K :=
    lt_of_lt_of_le hK₂ (pow_le_pow_right₀ (by norm_num) hK2K)
  have hzpowK : (2 : ℝ) ^ (-(K : ℤ) + (l : ℤ)) = (2 : ℝ) ^ l / (2 : ℝ) ^ K := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_neg, zpow_natCast, zpow_natCast,
      div_eq_mul_inv, mul_comm]
  have hkey : (2 : ℝ) ^ (-(K : ℤ) + (l : ℤ)) * M < 1 / 4 := by
    rw [hzpowK, div_mul_eq_mul_div]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ K)]
    linarith
  have hpiece1 : (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N) + (l : ℤ)) * M < 1 / 4 := by
    have hzpow_le : (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N) + (l : ℤ))
        ≤ (2 : ℝ) ^ (-(K : ℤ) + (l : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzpow_le hMnn) hkey
  have hpiece2 : (2 : ℝ) ^ ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ))) * M
      < 1 / 4 := by
    have hxnonpos : -(Work.Analysis.EndVar.logN N) + (l : ℤ) ≤ 0 := by omega
    have hdnat : (1 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd
    have hmul : (P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ))
        ≤ -(Work.Analysis.EndVar.logN N) + (l : ℤ) := by
      nlinarith [hdnat, hxnonpos]
    have hzle : (2 : ℝ) ^ ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ)))
        ≤ (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N) + (l : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hmul
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzle hMnn) hpiece1
  have hpiece3 : (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ)) ≤ ε := by
    refine rpow_neg_le_of_le_inv hε hc hρ ?_
    calc ε ^ (-(ρ / c)) ≤ (K₁ : ℝ) := hepsK1
      _ ≤ (K : ℝ) := Nat.cast_le.mpr hK1K
      _ ≤ (Work.Analysis.EndVar.logN N : ℝ) := by exact_mod_cast hL
  exact ⟨hQN, hpiece1, hpiece2, hpiece3⟩

end Work.KMTPlan.A6
