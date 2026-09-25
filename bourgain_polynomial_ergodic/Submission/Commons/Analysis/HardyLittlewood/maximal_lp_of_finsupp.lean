import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.HardyLittlewood

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

/-- The average of `‖u‖ₑ` over the integer interval `[a, b]`. -/
private noncomputable def hlterm (u : ℤ → ℝ) (a b : ℤ) : ℝ≥0∞ :=
  ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖u k‖ₑ

/-- The discrete two-sided maximal function of `g : ℤ → ℝ`, as an `ℝ≥0∞`-valued function. -/
private noncomputable def hlmax (u : ℤ → ℝ) (x : ℤ) : ℝ≥0∞ :=
  ⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b), hlterm u a b

/-- Truncation of `g` to the interval `[-N, N]`. -/
private def hltrunc (g : ℤ → ℝ) (N : ℕ) (k : ℤ) : ℝ :=
  if k.natAbs ≤ N then g k else 0

private lemma hltrunc_support (g : ℤ → ℝ) (N : ℕ) :
    ∃ s : Finset ℤ, ∀ n, n ∉ s → hltrunc g N n = 0 := by
  refine ⟨Finset.Icc (-(N : ℤ)) (N : ℤ), fun n hn => ?_⟩
  by_cases hnab : n.natAbs ≤ N
  · exact absurd (by rw [Finset.mem_Icc]; constructor <;> omega) hn
  · rw [hltrunc, if_neg hnab]

private lemma hl_enorm_trunc_le (g : ℤ → ℝ) (N : ℕ) (k : ℤ) :
    ‖hltrunc g N k‖ₑ ≤ ‖g k‖ₑ := by
  by_cases h : k.natAbs ≤ N
  · rw [hltrunc, if_pos h]
  · rw [hltrunc, if_neg h]
    simp

private lemma hl_enorm_trunc_mono (g : ℤ → ℝ) {N N' : ℕ} (h : N ≤ N') (k : ℤ) :
    ‖hltrunc g N k‖ₑ ≤ ‖hltrunc g N' k‖ₑ := by
  by_cases hk : k.natAbs ≤ N
  · rw [hltrunc, if_pos hk, hltrunc, if_pos (le_trans hk h)]
  · rw [hltrunc, if_neg hk]
    simp

private lemma hlterm_mono {g₁ g₂ : ℤ → ℝ} (h : ∀ k, ‖g₁ k‖ₑ ≤ ‖g₂ k‖ₑ) (a b : ℤ) :
    hlterm g₁ a b ≤ hlterm g₂ a b := by
  unfold hlterm
  gcongr with k
  exact h k

private lemma hlmax_mono {g₁ g₂ : ℤ → ℝ} (h : ∀ k, ‖g₁ k‖ₑ ≤ ‖g₂ k‖ₑ) (x : ℤ) :
    hlmax g₁ x ≤ hlmax g₂ x := by
  unfold hlmax
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hh => ?_
  exact le_trans (hlterm_mono h a b) (le_trans
    (le_trans (le_iSup (fun _ : a ≤ x ∧ x ≤ b => hlterm g₂ a b) hh)
      (le_iSup (fun b' => ⨆ (_ : a ≤ x ∧ x ≤ b'), hlterm g₂ a b') b))
    (le_iSup (fun a' => ⨆ (b' : ℤ) (_ : a' ≤ x ∧ x ≤ b'), hlterm g₂ a' b') a))

private lemma hlmax_le_iSup_trunc (g : ℤ → ℝ) (x : ℤ) :
    hlmax g x ≤ ⨆ N, hlmax (hltrunc g N) x := by
  change (⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b), hlterm g a b)
    ≤ ⨆ N, hlmax (hltrunc g N) x
  refine iSup_le fun a => iSup_le fun b => iSup_le fun hx => ?_
  set N₀ : ℕ := max a.natAbs b.natAbs with hN₀
  have hterm : hlterm g a b = hlterm (hltrunc g N₀) a b := by
    unfold hlterm
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hnat : k.natAbs ≤ N₀ := by rw [hN₀]; omega
    rw [hltrunc, if_pos hnat]
  rw [hterm]
  have hbound : hlterm (hltrunc g N₀) a b ≤ hlmax (hltrunc g N₀) x := by
    change _ ≤ ⨆ (a' : ℤ) (b' : ℤ) (_ : a' ≤ x ∧ x ≤ b'), hlterm (hltrunc g N₀) a' b'
    exact le_trans (le_trans
        (le_iSup (fun _ : a ≤ x ∧ x ≤ b => hlterm (hltrunc g N₀) a b) hx)
        (le_iSup (fun b' => ⨆ (_ : a ≤ x ∧ x ≤ b'), hlterm (hltrunc g N₀) a b') b))
      (le_iSup (fun a' => ⨆ (b' : ℤ) (_ : a' ≤ x ∧ x ≤ b'), hlterm (hltrunc g N₀) a' b') a)
  exact le_trans hbound (le_iSup (fun N => hlmax (hltrunc g N) x) N₀)

private lemma hlmax_eq_iSup_trunc (g : ℤ → ℝ) (x : ℤ) :
    hlmax g x = ⨆ N, hlmax (hltrunc g N) x := by
  refine le_antisymm (hlmax_le_iSup_trunc g x) ?_
  exact iSup_le fun N => hlmax_mono (fun k => hl_enorm_trunc_le g N k) x

/-- Pointwise commutation of `x ↦ x ^ q` (`q ≥ 0`) with a monotone supremum over `ℕ`. -/
private lemma rpow_iSup_of_monotone {q : ℝ} (hq : 0 ≤ q) {F : ℕ → ℝ≥0∞} (hF : Monotone F) :
    (⨆ n, F n) ^ q = ⨆ n, (F n) ^ q := by
  have h1 : Tendsto F atTop (𝓝 (⨆ n, F n)) := tendsto_atTop_iSup hF
  have h2 : Tendsto (fun n => (F n) ^ q) atTop (𝓝 ((⨆ n, F n) ^ q)) :=
    ((ENNReal.continuous_rpow_const (y := q)).tendsto (⨆ n, F n)).comp h1
  have h3 : Tendsto (fun n => (F n) ^ q) atTop (𝓝 (⨆ n, (F n) ^ q)) :=
    tendsto_atTop_iSup (fun i j hij => ENNReal.rpow_le_rpow (hF hij) hq)
  exact tendsto_nhds_unique h2 h3

theorem maximal_lp_of_finsupp {p : ℝ} (hp : 1 < p) {C : ℝ} (hC : 0 < C)
    (hfin : ∀ (g : ℤ → ℝ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ x, (⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
            ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂Measure.count) :
    ∀ (g : ℤ → ℝ),
      ∫⁻ x, (⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
            ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂Measure.count := by
  have hp0 : 0 ≤ p := le_of_lt (lt_trans zero_lt_one hp)
  intro g
  -- `hfin` in terms of the maximal function `hlmax`.
  have hfin' : ∀ (u : ℤ → ℝ), (∃ s : Finset ℤ, ∀ n, n ∉ s → u n = 0) →
      ∫⁻ x, (hlmax u x) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖u x‖ₑ ^ p ∂Measure.count := by
    intro u hu
    simpa only [hlmax, hlterm] using hfin u hu
  -- Pointwise identification of `(hlmax g x)^p` as a monotone supremum.
  have hrpow_sup : ∀ x, (⨆ N, (hlmax (hltrunc g N) x) ^ p) = (hlmax g x) ^ p := by
    intro x
    have hmono_x : Monotone (fun N => hlmax (hltrunc g N) x) :=
      fun i j hij => hlmax_mono (fun k => hl_enorm_trunc_mono g hij k) x
    have h := rpow_iSup_of_monotone hp0 hmono_x
    rw [← h, hlmax_eq_iSup_trunc g x]
  -- Monotone convergence.
  have hmono_f : Monotone (fun N => fun x : ℤ => (hlmax (hltrunc g N) x) ^ p) :=
    fun i j hij x => ENNReal.rpow_le_rpow (hlmax_mono (fun k => hl_enorm_trunc_mono g hij k) x) hp0
  have hMCT : ∫⁻ x, (⨆ N, (hlmax (hltrunc g N) x) ^ p) ∂Measure.count
      = ⨆ N, ∫⁻ x, (hlmax (hltrunc g N) x) ^ p ∂Measure.count :=
    lintegral_iSup (fun N => measurable_of_countable _) hmono_f
  calc ∫⁻ x, (⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
            ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ) ^ p ∂Measure.count
      = ∫⁻ x, (hlmax g x) ^ p ∂Measure.count := by
        apply lintegral_congr; intro x
        simp only [hlmax, hlterm]
    _ = ∫⁻ x, (⨆ N, (hlmax (hltrunc g N) x) ^ p) ∂Measure.count := by
        apply lintegral_congr; intro x; exact (hrpow_sup x).symm
    _ = ⨆ N, ∫⁻ x, (hlmax (hltrunc g N) x) ^ p ∂Measure.count := hMCT
    _ ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂Measure.count := by
        apply iSup_le; intro N
        calc ∫⁻ x, (hlmax (hltrunc g N) x) ^ p ∂Measure.count
            ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖hltrunc g N x‖ₑ ^ p ∂Measure.count :=
              hfin' (hltrunc g N) (hltrunc_support g N)
          _ ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂Measure.count :=
              mul_le_mul_of_nonneg_left
                (lintegral_mono fun x => ENNReal.rpow_le_rpow (hl_enorm_trunc_le g N x) hp0)
                zero_le

end Commons.Analysis.HardyLittlewood