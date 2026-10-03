import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FITop.BformAtilEqXsum
import Submission.Work.FITop.AtilTauPowFourLe
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25
import Submission.Work.FITop.SingleDvdTauSqLe
import Submission.Work.FITop.WindowRangeMarginsChain
import Submission.Work.FITop.BprimeWindowDelta1
import Submission.Work.FITop.RangeCheckChain
import Submission.ASP.S30
import Submission.Work.FITop.WolkeSquarefreeTau
import Submission.Work.FITop.AdTauAggregate
import Submission.Work.FITop.SumIteDivDvd
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FIChain.BpWinAux
import Submission.Work.FIChain.BpWinMain
import Submission.Work.FIChain.Xf_sum_le_BformPi
import Submission.Work.FIChain.Xsum_eq_sum_Xf
import Submission.Work.FIChain.exists_dvd_ProdP_between
import Submission.Work.FIChain.Xf_Bw_le
import Submission.Work.FIChain.Xf_tau_grouping
import Submission.Work.FIChain.Dpi_rankin
import Submission.Work.FIChain.Aw_le_of_PiBig
import Submission.Work.FIChain.window_margin_sharp
import Submission.Work.FIChain.Yc_lower_sharp
import Submission.Work.FIChain.bprime_window_tail_le
-- infrastructure for the `Π`-removal (companion §10, Theorem 3) of this window
-- delegated lemmas (see the proof plan below)

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# The integrated `(B′)`-window (the `Π`-removal of the companion's §10, Theorem 3)

The hypothesis `h : Prop41StatementPiBig` is the `Π`-restricted Proposition 4.1; the target is the
`Π`-free integrated window.  The passage is the companion's §10: write the inner variable as
`b = b₁·b₀` with `b₁ | Π` and `(b₀,Π)=1` (`Xsum_eq_sum_Xf`), split the `b₁`-sum at
`Δπ = ⌈e^{κ(loglog x)³}⌉` (here `κ = 2^40`):

* `b₁ ≤ Δπ` — `Work.FIChain.bprime_window_main_le` (in `BpWinMain.lean`): substitute `u = t/b₁`
  in the integral (making all terms live at the same scale), extend the ranges to `[lo/Δπ, hi]`,
  group by `c = m·b₁` (`Xf_tau_grouping`), apply pointwise Cauchy–Schwarz and the two pointwise
  inputs `Aw ≤ KA·Ã·L^{-2^26}` (`Aw_le_of_PiBig`) and `Bw ≤ CB·Ã·L^{262144}` (`Xf_Bw_le`);
* `b₁ > Δπ` — `Work.FIChain.bprime_window_tail_le`: triangle inequality; every such `b₁` has a
  divisor `d | Π` with `Δπ < d ≤ Δπ·Π` (`exists_dvd_ProdP_between`); summing by `l = m·b₁·n`
  (multiplicity `≤ τ(l)⁴`) and Rankin's trick (`Dpi_rankin`) give `≪ Ã·L^{-κ/2+O(1)}`.

The range conditions come from `window_margin_sharp` (`(x^{1/4+η/2}+2)·Δπ < Yc/Δc`, so that the
`(B*)`-input `Aw_le_of_PiBig` applies on the whole range `[lo/D, hi]`) and from the elementary
fact `hi = e·√x/(log x)^{B+2} ≤ √x` (used for the log-length `log(hi/(lo/D)) ≤ 2 log x`).
-/

def BprimeWindowInt (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (E lo hi : ℝ) : Prop :=
  (∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 N, w m * |Submission.ASP.Xsum a N m t (2 * t)|) / t) ≤ E

theorem BprimeWindowIntegrated (h : Work.FITop4.Prop41StatementPiBig) :
    ∀ η : ℝ, 0 < η → η < 3 / 32 → ∃ B K : ℝ, ∃ x₀ : ℕ, 0 < B ∧ 0 < K ∧ ∀ x : ℕ, x₀ ≤ x →
      BprimeWindowInt Work.FIChain.atilc x Work.FIChain.wc
        (K * Work.FIChain.AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
        (Work.FIChain.Yc x B / (Work.FIChain.Deltac x : ℝ))
        (Work.FIChain.sc x B * (Real.exp 1 * Work.FIChain.Yc x B)) := by
  intro η hη hη32
  -- the four inputs
  obtain ⟨B, KA, xA, hBpos, hKApos, hAwPi⟩ := Aw_le_of_PiBig h η hη hη32
  obtain ⟨CB, hCBpos, xB, hBwAll⟩ := Xf_Bw_le
  have hκ40pos : (0 : ℝ) < (2 : ℝ) ^ (40 : ℕ) := by positivity
  have hκ30 : (2 : ℝ) ^ (30 : ℕ) ≤ (2 : ℝ) ^ (40 : ℕ) := by norm_num
  obtain ⟨KT, xT, hKTpos, htail⟩ := bprime_window_tail_le B ((2 : ℝ) ^ (40 : ℕ)) hBpos hκ30
  -- the range conditions
  have hKEv : ∀ᶠ x : ℕ in Filter.atTop,
      ((x : ℝ) ^ ((1 : ℝ) / 4 + η / 2) + 2) * (Dpi x ((2 : ℝ) ^ (40 : ℕ)) : ℝ)
          < Yc x B / (Deltac x : ℝ)
      ∧ (x : ℝ) ^ ((5 : ℝ) / 16) ≤ Yc x B
      ∧ (1 : ℝ) ≤ Work.FITop.Lam1 x
      ∧ (Deltac x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100)
      ∧ (2 : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 16 - 1 / 100)
      ∧ (Dpi x ((2 : ℝ) ^ (40 : ℕ)) : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2)
      ∧ Real.exp 1 ≤ Real.log (x : ℝ)
      ∧ (1 : ℝ) ≤ Real.log (x : ℝ) := by
    filter_upwards [window_margin_sharp B ((2 : ℝ) ^ (40 : ℕ)) hBpos hκ40pos η hη hη32,
      Yc_lower_sharp B hBpos,
      Work.FITop.FI_ev_Lam1_ge_one,
      Work.FITop.FI_ev_Delta1_le_two_Lam1,
      Work.FITop.FI_ev_rpow_ge_nat ((5 : ℝ) / 16 - 1 / 100) (by norm_num) 2,
      eventually_Dpi_le_rpow ((2 : ℝ) ^ (40 : ℕ)) (1 / 2) hκ40pos (by norm_num),
      Work.FITop.FI_ev_log_ge_nat (Real.exp 1),
      Work.FITop.FI_ev_log_ge_nat 1] with x hwin hYc hLam1 hDel hpow hDle hloge hlog1
    refine ⟨hwin, hYc, hLam1, ?_, hpow, hDle, hloge, hlog1⟩
    simpa only [Deltac, Work.FITop.Delta1, Work.FITop.Lam1] using hDel
  rw [Filter.eventually_atTop] at hKEv
  obtain ⟨xE, hxE⟩ := hKEv
  refine ⟨B, 2 * Real.sqrt (KA * CB) + KT, max (max xA xB) (max xT xE), hBpos,
    by positivity, ?_⟩
  intro x hx
  have hxA : xA ≤ x :=
    le_trans (le_trans (le_max_left xA xB) (le_max_left (max xA xB) (max xT xE))) hx
  have hxB : xB ≤ x :=
    le_trans (le_trans (le_max_right xA xB) (le_max_left (max xA xB) (max xT xE))) hx
  have hxT : xT ≤ x :=
    le_trans (le_trans (le_max_left xT xE) (le_max_right (max xA xB) (max xT xE))) hx
  have hxE' : xE ≤ x :=
    le_trans (le_trans (le_max_right xT xE) (le_max_right (max xA xB) (max xT xE))) hx
  obtain ⟨hwin, hYclow, hLam1, hDelle, hpow2, hDle, hloge, hlog1⟩ := hxE x hxE'
  -- the parameters
  let κ : ℝ := (2 : ℝ) ^ (40 : ℕ)
  let D : ℝ := (Dpi x κ : ℝ)
  let Pz : ℕ := Pzc x
  let lo : ℝ := Yc x B / (Deltac x : ℝ)
  let hi : ℝ := sc x B * (Real.exp 1 * Yc x B)
  let L : ℝ := Real.log (x : ℝ)
  have hxpos : (0 : ℝ) < (x : ℝ) :=
    lt_trans one_pos ((Real.log_pos_iff (Nat.cast_nonneg x)).mp (lt_of_lt_of_le one_pos hlog1))
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hlog1
  have hsc_pos : 0 < sc x B := by rw [sc]; positivity
  have hLp_pos : 0 < L ^ (B + 2) := Real.rpow_pos_of_pos hLpos _
  have hYc_pos : 0 < Yc x B := by
    rw [Yc]
    exact div_pos (Real.sqrt_pos.mpr hxpos) (mul_pos hsc_pos (Real.rpow_pos_of_pos hLpos _))
  have hDel1 : 1 ≤ Deltac x := Nat.ceil_pos.mpr (lt_of_lt_of_le one_pos (by
    simpa only [Deltac, Work.FITop.Delta1] using hLam1))
  have hDeltac_pos : 0 < (Deltac x : ℝ) := by exact_mod_cast (by omega : 0 < Deltac x)
  have hDpi1 : 1 ≤ Dpi x κ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hD1 : 1 ≤ D := by
    rw [show D = (Dpi x κ : ℝ) from rfl]
    exact_mod_cast hDpi1
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hlo_pos : 0 < lo := by
    rw [show lo = Yc x B / (Deltac x : ℝ) from rfl]
    exact div_pos hYc_pos hDeltac_pos
  -- the identity `hi = e·√x/L^{B+2}`
  have hhi_eq : hi = Real.exp 1 * Real.sqrt (x : ℝ) / L ^ (B + 2) := by
    show sc x B * (Real.exp 1 * (Real.sqrt (x : ℝ) / (sc x B * L ^ (B + 2))))
      = Real.exp 1 * Real.sqrt (x : ℝ) / L ^ (B + 2)
    have hscne : sc x B ≠ 0 := ne_of_gt hsc_pos
    have hLpne : L ^ (B + 2) ≠ 0 := ne_of_gt hLp_pos
    field_simp
  have hhi_pos : 0 < hi := by
    rw [hhi_eq]
    exact div_pos (mul_pos (Real.exp_pos 1) (Real.sqrt_pos.mpr hxpos)) hLp_pos
  have hloD_pos : 0 < lo / D := div_pos hlo_pos hDpos
  -- `e ≤ L^{B+2}`, whence `hi ≤ √x`
  have hexp_le : Real.exp 1 ≤ L ^ (B + 2) := by
    have h1 : Real.exp 1 ≤ L ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      nlinarith [hloge, hlog1, Real.exp_pos 1]
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith [hBpos]))
  have hhi_le : hi ≤ Real.sqrt (x : ℝ) := by
    rw [hhi_eq, div_le_iff₀ hLp_pos]
    calc Real.exp 1 * Real.sqrt (x : ℝ) = Real.sqrt (x : ℝ) * Real.exp 1 := by ring
      _ ≤ Real.sqrt (x : ℝ) * L ^ (B + 2) :=
          mul_le_mul_of_nonneg_left hexp_le (Real.sqrt_nonneg _)
  have hD_le : D ≤ Real.sqrt (x : ℝ) := by
    rw [show D = (Dpi x κ : ℝ) from rfl, Real.sqrt_eq_rpow]
    exact hDle
  -- `lo ≥ 1`
  have hDeltac_le : (Deltac x : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 100) := hDelle
  have hx100_le : 2 * (x : ℝ) ^ ((1 : ℝ) / 100) ≤ (x : ℝ) ^ ((5 : ℝ) / 16) := by
    calc 2 * (x : ℝ) ^ ((1 : ℝ) / 100)
        ≤ (x : ℝ) ^ ((5 : ℝ) / 16 - 1 / 100) * (x : ℝ) ^ ((1 : ℝ) / 100) :=
          mul_le_mul_of_nonneg_right hpow2 (Real.rpow_nonneg hxpos.le _)
      _ = (x : ℝ) ^ ((5 : ℝ) / 16) := by
          rw [← Real.rpow_add hxpos]
          norm_num
  have hlo_ge_one : 1 ≤ lo := by
    rw [show lo = Yc x B / (Deltac x : ℝ) from rfl, one_le_div hDeltac_pos]
    exact le_trans (le_trans hDeltac_le hx100_le) hYclow
  -- `lo ≤ hi`
  have hhi_eq2 : hi = Real.exp 1 * lo * (sc x B * (Deltac x : ℝ)) := by
    rw [hhi_eq, show lo = Yc x B / (Deltac x : ℝ) from rfl, Yc]
    have hscne : sc x B ≠ 0 := ne_of_gt hsc_pos
    have hLpne : L ^ (B + 2) ≠ 0 := ne_of_gt hLp_pos
    have hDne : (Deltac x : ℝ) ≠ 0 := ne_of_gt hDeltac_pos
    field_simp
    ring
  have hlo_le_hi : lo ≤ hi := by
    rw [hhi_eq2]
    have hsc1 : (1 : ℝ) ≤ sc x B := by rw [sc]; exact one_le_pow₀ (by norm_num)
    have hDe1 : (1 : ℝ) ≤ (Deltac x : ℝ) := by exact_mod_cast hDel1
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h1 : (1 : ℝ) ≤ Real.exp 1 * (sc x B * (Deltac x : ℝ)) := by
      have h2 : (1 : ℝ) * 1 ≤ sc x B * (Deltac x : ℝ) :=
        mul_le_mul hsc1 hDe1 zero_le_one (le_trans zero_le_one hsc1)
      nlinarith [he1, h2]
    calc lo = lo * 1 := (mul_one lo).symm
      _ ≤ lo * (Real.exp 1 * (sc x B * (Deltac x : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 hlo_pos.le
      _ = Real.exp 1 * lo * (sc x B * (Deltac x : ℝ)) := by ring
  have hloD_le_hi : lo / D ≤ hi :=
    le_trans (div_le_self hlo_pos.le hD1) hlo_le_hi
  -- the `(B*)`-input applies on the whole range `[lo/D, hi]`
  have hloD_gt : (x : ℝ) ^ ((1 : ℝ) / 4 + η / 2) + 2 < lo / D := by
    rw [lt_div_iff₀ hDpos]
    exact hwin
  have hAwr : ∀ u ∈ Set.Icc (lo / D) hi,
      Aw x Pz u ≤ KA * AcountAtilC x * (Real.log (x : ℝ)) ^ (-((2 : ℝ) ^ (26 : ℕ))) := by
    intro u hu
    exact hAwPi x hxA u (lt_of_lt_of_le hloD_gt hu.1) hu.2
  have hBwr : ∀ u ∈ Set.Icc (lo / D) hi,
      Bw x Pz u ≤ CB * AcountAtilC x * (Real.log (x : ℝ)) ^ (262144 : ℕ) :=
    fun u _ => hBwAll x Pz hxB u
  -- the log-length
  have hratio : hi / (lo / D) ≤ (x : ℝ) := by
    have h1 : hi * D ≤ (x : ℝ) := by
      have h2 : hi * D ≤ Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
        mul_le_mul hhi_le hD_le (le_of_lt hDpos) (Real.sqrt_nonneg _)
      rwa [Real.mul_self_sqrt hxpos.le] at h2
    rw [div_div_eq_mul_div, div_le_iff₀ hlo_pos]
    nlinarith [h1, hlo_ge_one, hxpos]
  have hR : Real.log hi - Real.log (lo / D) ≤ 2 * Real.log (x : ℝ) := by
    rw [← Real.log_div hhi_pos.ne' hloD_pos.ne']
    have h2 : Real.log (hi / (lo / D)) ≤ Real.log (x : ℝ) :=
      Real.log_le_log (div_pos hhi_pos hloD_pos) hratio
    linarith [hlog1]
  -- the pointwise split of the `b₁`-sum
  have hunion : s1F Pz D ∪ s2F Pz x κ = (ProdP Pz).divisors := by
    ext b₁
    simp only [s1F, s2F, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hb
      by_cases hle : ((b₁ : ℝ)) ≤ D
      · exact Or.inl ⟨hb, hle⟩
      · exact Or.inr ⟨hb, by
          have hlt : (Dpi x κ : ℝ) < (b₁ : ℝ) := by
            rw [show D = (Dpi x κ : ℝ) from rfl] at hle
            exact lt_of_not_ge hle
          exact_mod_cast hlt⟩
  have hdisj : Disjoint (s1F Pz D) (s2F Pz x κ) := by
    rw [Finset.disjoint_left]
    intro b hb1 hb2
    rw [s1F, Finset.mem_filter] at hb1
    rw [s2F, Finset.mem_filter] at hb2
    have h1 : (b : ℝ) ≤ (Dpi x κ : ℝ) := hb1.2
    have h2 : (Dpi x κ : ℝ) < (b : ℝ) := by exact_mod_cast hb2.2
    exact absurd h1 (not_le.mpr h2)
  have hpt : ∀ t : ℝ, (∑ m ∈ Finset.Icc 1 x, wc m * |Submission.ASP.Xsum atilc x m t (2 * t)|)
      ≤ (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s1F Pz D,
            (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|)
        + (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s2F Pz x κ,
            (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) := by
    intro t
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun m hm => ?_)
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    rw [Xsum_eq_sum_Xf x Pz m hm1 t, ← hunion, Finset.sum_union hdisj]
    refine le_trans (mul_le_mul_of_nonneg_left (abs_add_le _ _) (wc_nonneg m)) (le_of_eq ?_)
    rw [mul_add]
  -- the integral bound
  have hF1int := integrable_G1 x Pz D hlo_pos hlo_le_hi
  have hF2int := integrable_G2 x Pz κ hlo_pos hlo_le_hi
  have hsplit : (∫ t in lo..hi,
        (∑ m ∈ Finset.Icc 1 x, wc m * |Submission.ASP.Xsum atilc x m t (2 * t)|) / t)
      ≤ (∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s1F Pz D,
            (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t)
        + (∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s2F Pz x κ,
            (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t) := by
    refine le_trans (intervalIntegral.integral_mono_on hlo_le_hi
      (integrable_Xsum_sum x hlo_pos hlo_le_hi) (hF1int.add hF2int)
      (fun t ht => ?_)) (le_of_eq (intervalIntegral.integral_add hF1int hF2int))
    refine le_trans (div_le_div_of_nonneg_right (hpt t) (le_trans hlo_pos.le ht.1)) ?_
    rw [add_div]
  have hF1b := bprime_window_main_le x Pz D lo hi hDpos hlo_pos hloD_le_hi hlo_le_hi
    KA CB hKApos.le hCBpos.le hAwr hBwr hlog1 hR
  have hF2b : (∫ t in lo..hi, (∑ m ∈ Finset.Icc 1 x, wc m * |∑ b₁ ∈ s2F Pz x κ,
        (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁)|) / t)
      ≤ KT * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)) := htail x hxT
  have hmain : (∫ t in lo..hi,
        (∑ m ∈ Finset.Icc 1 x, wc m * |Submission.ASP.Xsum atilc x m t (2 * t)|) / t)
      ≤ (2 * Real.sqrt (KA * CB) + KT) * AcountAtilC x * L ^ (-(4 : ℤ)) := by
    refine le_trans hsplit (le_trans (add_le_add hF1b hF2b) (le_of_eq ?_))
    rw [show L = Real.log (x : ℝ) from rfl]
    ring
  rw [BprimeWindowInt]
  exact hmain

end

end Work.FIChain
