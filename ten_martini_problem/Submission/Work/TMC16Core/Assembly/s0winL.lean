import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.S0
import Submission.Work.TMC16Core.Assembly.RegWin

namespace Work.TMC16Core.Assembly

/-!
# The mirrored `s = 0` window arithmetic (`s0winL`)

In the `s = 0` branch of AJ Lemma 9.4 the site `y` may lie to the *left* of the multiple
`M = m qₙ` of `qₙ`; the two windows are then the mirror images (`x ↦ -x - (H-2)`) of the
windows `W1s0`/`W2s0` of `Assembly.S0`, namely `W1s0L`/`W2s0L`.

This file proves the purely arithmetic contents of the mirrored windows at `H = K+1`,
`U = c + 1`, `c = ⌈K/40⌉`, `a = k₀ - K - c`:

* `2U ≤ K + 1`, so the two windows fit;
* the union has exactly `K+1 = H` sites (disjointness uses `M ≥ K+1`);
* `W1s0L` sits inside the singular strip `[-(1-δ)K, -δK]` with `δ = 1/40 + 1/K`
  (this is where the hypotheses `k₀ ≥ K/20 + 3` and `k₀ ≤ 95K/100 - 3` are used);
* every site of `W2s0L` witnesses `IsRegularBig`'s distance conditions about `y = M - k₀`.

Both windows are computed in closed form: `W1s0L = [-k₀ - c, -k₀ + c + 1]` and
`W2s0L = [M - k₀ - K + c + 1, M - k₀ - c - 1]`.
-/

theorem s0winL {K : ℕ} {k₀ M : ℤ} {c : ℕ} {a : ℤ} {U : ℕ}
    (hK : 40 ≤ K) (hc : c = (K + 39) / 40) (ha : a = k₀ - (K : ℤ) - (c : ℤ)) (hU : U = c + 1)
    (hM : (K : ℤ) + 1 ≤ M)
    (hlo : (K : ℝ) / 20 + 3 ≤ (k₀ : ℝ)) (hhi : (k₀ : ℝ) ≤ 95 * (K : ℝ) / 100 - 3) :
    2 * U ≤ K + 1 ∧
      (Work.TMC16Core.Assembly.W1s0L a U (K + 1) ∪
        Work.TMC16Core.Assembly.W2s0L a U (K + 1) M).card = K + 1 ∧
      (∀ x ∈ Work.TMC16Core.Assembly.W1s0L a U (K + 1),
        -((1 - (1 / 40 + 1 / (K : ℝ))) * (K : ℝ)) ≤ (x : ℝ) ∧
          (x : ℝ) ≤ -((1 / 40 + 1 / (K : ℝ)) * (K : ℝ))) ∧
      (∀ x ∈ Work.TMC16Core.Assembly.W2s0L a U (K + 1) M,
        x ≤ M - k₀ ∧ M - k₀ ≤ x + (K : ℤ) - 1 ∧
          (K : ℤ) ≤ 40 * ((M - k₀) - x) ∧
          (K : ℤ) ≤ 40 * ((x + (K : ℤ) - 1) - (M - k₀))) := by
  -- ## 1. The two windows fit (`2U ≤ H` with `H = K+1`)
  have h2U : 2 * U ≤ K + 1 := by omega
  -- ## 2. Closed forms of the two windows
  have hW1 : W1s0L a U (K + 1) = Finset.Icc (-k₀ - (c:ℤ)) (-k₀ + (c:ℤ) + 1) := by
    ext x
    simp only [W1s0L, Finset.mem_Icc]
    constructor <;> intro h <;> constructor <;> omega
  have hW2 : W2s0L a U (K + 1) M =
      Finset.Icc (M - k₀ - (K:ℤ) + (c:ℤ) + 1) (M - k₀ - (c:ℤ) - 1) := by
    ext x
    simp only [W2s0L, Finset.mem_Icc]
    constructor <;> intro h <;> constructor <;> omega
  -- ## 3. Arithmetic about `c = ⌈K/40⌉` and the real bookkeeping
  have hKc : (K : ℤ) ≤ 40 * (c : ℤ) := by
    have : K ≤ 40 * c := by omega
    exact_mod_cast this
  have hKpos : (0:ℝ) < (K:ℝ) := by
    have : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
    linarith
  have hcub : (c:ℝ) ≤ ((K:ℝ) + 39)/40 := by
    have h40 : (40:ℝ) * (c:ℝ) ≤ (K:ℝ) + 39 := by
      have : 40 * c ≤ K + 39 := by omega
      exact_mod_cast this
    linarith
  have hA : (1 / 40 + 1 / (K : ℝ)) * (K : ℝ) = (K : ℝ) / 40 + 1 := by
    field_simp
  have hlo' : (K:ℝ)/40 + (c:ℝ) + 2 ≤ (k₀:ℝ) := by linarith
  have hhi' : (k₀:ℝ) + (c:ℝ) ≤ 39 * (K:ℝ)/40 - 1 := by linarith
  refine ⟨h2U, ?_, ?_, ?_⟩
  -- ## 4. The union has exactly `K+1` sites
  · rw [hW1, hW2]
    have hdisj : Disjoint (Finset.Icc (-k₀ - (c:ℤ)) (-k₀ + (c:ℤ) + 1))
        (Finset.Icc (M - k₀ - (K:ℤ) + (c:ℤ) + 1) (M - k₀ - (c:ℤ) - 1)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Icc] at hx1 hx2
      omega
    rw [Finset.card_union_of_disjoint hdisj, Int.card_Icc, Int.card_Icc]
    have e1 : (-k₀ + (c:ℤ) + 1 + 1 - (-k₀ - (c:ℤ)) : ℤ) = ((2 * U : ℕ) : ℤ) := by omega
    have e2 : ((M - k₀ - (c:ℤ) - 1) + 1 - (M - k₀ - (K:ℤ) + (c:ℤ) + 1) : ℤ) =
        ((K + 1 - 2 * U : ℕ) : ℤ) := by omega
    rw [e1, e2, Int.toNat_natCast, Int.toNat_natCast]
    omega
  -- ## 5. `W1s0L` sits in the singular strip `[-(1-δ)K, -δK]`, `δ = 1/40 + 1/K`
  · intro x hx
    rw [hW1, Finset.mem_Icc] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx1R : ((-k₀ - (c:ℤ) : ℤ) : ℝ) ≤ (x:ℝ) := by exact_mod_cast hx1
    have hx2R : (x:ℝ) ≤ ((-k₀ + (c:ℤ) + 1 : ℤ) : ℝ) := by exact_mod_cast hx2
    push_cast at hx1R hx2R
    constructor
    · have key : (1 - (1/40 + 1/(K:ℝ))) * (K:ℝ) = (K:ℝ) - ((K:ℝ)/40 + 1) := by
        rw [sub_mul, one_mul, hA]
      rw [key]
      linarith
    · rw [hA]
      linarith
  -- ## 6. Every site of `W2s0L` sees `y = M - k₀` at distance `≥ K/40`
  · intro x hx
    rw [hW2, Finset.mem_Icc] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have h1 : x ≤ M - k₀ := by omega
    have h2 : M - k₀ ≤ x + (K:ℤ) - 1 := by omega
    have h3 : (c:ℤ) + 1 ≤ M - k₀ - x := by omega
    have h4 : (c:ℤ) ≤ (x + (K:ℤ) - 1) - (M - k₀) := by omega
    refine ⟨h1, h2, ?_, ?_⟩
    · have : 40 * ((c:ℤ) + 1) ≤ 40 * (M - k₀ - x) :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      linarith
    · have : 40 * (c:ℤ) ≤ 40 * ((x + (K:ℤ) - 1) - (M - k₀)) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
      linarith

end Work.TMC16Core.Assembly
