import Mathlib
import Submission.Work.LinnikAreas.BGTZ
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.siegelRestHigh
import Submission.Work.LinnikAreas.pairCountHeight_le_famCount
import Submission.Work.LinnikAreas.siegelZeroWeightSummable

/-!
# `Work.LinnikAreas.RestHighFree` — the `λ₁`-*free* bound on the far-height zero mass of AREA 6

`Work.LinnikAreas.Siegel.RestHighFreeSpec e` is the high-zero (`|Im ρ| > 1`) part
`restHighZeroSum χ₁ β₁ (11/2) (3/10)` of the AREA 6 zero sum, bounded **without any reference to
`λ₁ = λ(β₁)`**: there are `C > 0` and `q₀` with
`restHighZeroSum χ₁ β₁ (11/2) (3/10) ≤ C·(log q)^e` for all `q ≥ q₀` and all Siegel data with
`λ₁ ≤ 1/2`.  The present file proves it with `e = -3/2` — and in fact with the whole function
`C·(log q)^{-2}`, which dominates `C·(log q)^{-3/2}` — from the single input

`Work.ZeroDensity.LogFreeFamHeight (5/2) (3/2)`,

i.e. the `λ₁`-free log-free family zero count in the height direction
(Jutila + Huxley; see `Submission/Work/ZeroDensity/Assembly/logFreeFamHeight_of_cores.lean`), which
is a theorem of the literature and is independent of `λ₁`.

## The argument

Fix `q > 1`, the exceptional pair `(χ₁,β₁)` and write `𝓛 = log q`, `λ(ρ) = (1-Re ρ)𝓛`.

1. **Kernel bound** (`high_kernel_le`): on a high zero, `|Im ρ| > 1`,
   `mult·‖Hk (11/2) (3/10) ((1-ρ)𝓛)‖ ≤ 4·mult·e^{-(49/10)λ(ρ)}/(|Im ρ|·𝓛)²`.
2. **The count, `λ₁`-free.**  `pairCountHeight χ₁ β₁ t T ≤ famCount q (1-t/𝓛) (T/𝓛)`
   (`pairCountHeight_le_famCount`), so for `0 < t ≤ 𝓛` and `𝓛 ≤ T`
   `pairCountHeight χ₁ β₁ t T ≤ C₂·𝓛^{-3/2}·e^{(5/2)t}·T^{3/2}`
   (`pairCountHeight_le_famCount_scaled`).
3. **Abel summation in `λ`** (`abel_lam_hi`): with the counting function `≤ C·λ₁·e^{ct}` up to
   height `T₀`, the exponentially weighted mass of a finite set of high zero-pairs of
   `𝓛`-height `≤ T₀` is `≤ C·λ₁·D·T₀^{c'}` as long as `c < 49/10`.  Only the range `T ≥ 𝓛` of the
   count is used, which is exactly what step 2 provides.
4. **Dyadic height layers** (`high_finset_bound_hi`): on the layer `2^j ≤ |Im ρ| < 2^{j+1}` the
   kernel weight is `≤ 4·4^{-j}/𝓛²` and the counting height is `T₀ = 2^{j+1}𝓛`, so the layer
   contributes `≪ 𝓛^{-2}·2^{-j/2}` and the layers sum to `≪ 𝓛^{-2}`; the exponent `c' - 2 = -1/2`
   of `𝓛` from the count times the `𝓛^{-3/2}` of the counting constant is the `𝓛^{-2}`.
5. **The `∑'` step** (`siegelZeroWeightSummable` for the domination of finite sub-sums, then
   `Real.tsum_le_of_sum_le`): `restHighZeroSum` is a `∑'` over pairs, so the uniform finite-set
   bound of step 4 passes to the `tsum`.

No Deuring–Heilbronn repulsion, no `λ₁`-saving count and no Siegel zero is used: the far heights
are controlled by the `λ₁`-free log-free family count alone.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

set_option linter.unusedVariables false

/-- **Abel summation in `lam` for a finite set of zero-pairs of bounded height** — the version of
`Work.LinnikAreas.abel_lam` in which the counting hypothesis is assumed only for the heights
`T ≥ log q` (instead of `T ≥ 1`).  If the height-density count
`pairCountHeight χ₁ β₁ t T ≤ C·lam1·e^{ct}·T^{c'}` holds for `log q ≤ T` (`c < 49/10`), then the
exponentially weighted multiplicity sum over a finite set of zero-pairs of height `≤ T₀` is
`≤ C·lam1·D·T₀^{c'}` with the explicit constant `D = e^{max c 0}/(1 - e^{max c 0 - 49/10})`.
The proof is that of `abel_lam`: the hypothesis is consumed only at `T = T₀`, so weakening
`1 ≤ T₀` to `log q ≤ T₀` costs nothing. -/
lemma abel_lam_hi {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C c c' lam1 : ℝ} (hC : 0 < C) (hlam1 : 0 < lam1) (hc : c < 49 / 10)
    (hcnt : ∀ t T : ℝ, 0 < t → t ≤ Real.log q → Real.log q ≤ T →
        Siegel.pairCountHeight χ₁ β₁ t T ≤ C * lam1 * Real.exp (c * t) * T ^ c')
    {T₀ : ℝ} (hT₀ : Real.log q ≤ T₀)
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log q ≤ T₀) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
      ≤ C * lam1 * (Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹) * T₀ ^ c' := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hT₀pos : 0 < T₀ := lt_of_lt_of_le hlog hT₀
  set cs : ℝ := max c 0 with hcsdef
  have hcs0 : 0 ≤ cs := le_max_right _ _
  have hcslt : cs < 49 / 10 := max_lt hc (by norm_num)
  have hr0 : 0 ≤ Real.exp (cs - 49 / 10) := Real.exp_nonneg _
  have hr1 : Real.exp (cs - 49 / 10) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set K : ℕ := Nat.ceil (Real.log q) + 1 with hKdef
  have hlam0 : ∀ z ∈ S, 0 < lamOf q z.2 := fun z hz => by
    have h1 : z.2.re < 1 := boxMaxZeroAux.zeroMult_re_lt_one z.1 (hzm z hz)
    rw [lamOf]; exact mul_pos (by linarith) hlog
  have hlamlt : ∀ z ∈ S, lamOf q z.2 < Real.log q := fun z hz => by
    have h1 : 0 < z.2.re := zeroMult_re_pos z.1 (hzm z hz)
    rw [lamOf]
    have h2 : 1 - z.2.re < 1 := by linarith
    calc (1 - z.2.re) * Real.log q < 1 * Real.log q :=
          mul_lt_mul_of_pos_right h2 hlog
      _ = Real.log q := by ring
  have hgmem : ∀ z ∈ S, Nat.floor (lamOf q z.2) ∈ Finset.range K := by
    intro z hz
    rw [Finset.mem_range]
    have h1 : (Nat.floor (lamOf q z.2) : ℝ) ≤ lamOf q z.2 :=
      Nat.floor_le (le_of_lt (hlam0 z hz))
    have h2 : (Nat.floor (lamOf q z.2) : ℝ) < (Nat.ceil (Real.log q) : ℝ) := by
      have h3 : lamOf q z.2 < (Nat.ceil (Real.log q) : ℝ) :=
        lt_of_lt_of_le (hlamlt z hz) (Nat.le_ceil _)
      linarith
    have h4 : Nat.floor (lamOf q z.2) < Nat.ceil (Real.log q) := Nat.cast_lt.mp h2
    rw [hKdef]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hgmem
    (fun z => (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))]
  have hfib : ∀ k ∈ Finset.range K,
      (∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
          (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
      ≤ C * lam1 * T₀ ^ c' * (Real.exp (-(49 / 10) * k)
          * Real.exp (c * min ((k : ℝ) + 1) (Real.log q))) := by
    intro k hk
    have htk_pos : 0 < min ((k : ℝ) + 1) (Real.log q) :=
      lt_min (by positivity) hlog
    have htk_le : min ((k : ℝ) + 1) (Real.log q) ≤ Real.log q := min_le_right _ _
    have hstep1 : (∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
          (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
        ≤ Real.exp (-(49 / 10) * k) * (∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
            (zeroMult z.1 z.2 : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun z hz => ?_)
      have hzf : z ∈ S := (Finset.mem_filter.mp hz).1
      have hgk : Nat.floor (lamOf q z.2) = k := (Finset.mem_filter.mp hz).2
      have hkl : (k : ℝ) ≤ lamOf q z.2 := by
        rw [← hgk]; exact Nat.floor_le (le_of_lt (hlam0 z hzf))
      have hexp : Real.exp (-(49 / 10) * lamOf q z.2) ≤ Real.exp (-(49 / 10) * k) := by
        rw [Real.exp_le_exp]; nlinarith
      calc (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)
          ≤ (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * k) :=
            mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)
        _ = Real.exp (-(49 / 10) * k) * (zeroMult z.1 z.2 : ℝ) := by ring
    have hstep2 : (∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
            (zeroMult z.1 z.2 : ℝ))
        ≤ Siegel.pairCountHeight χ₁ β₁ (min ((k : ℝ) + 1) (Real.log q)) T₀ := by
      refine pairCountHeight_dom hq χ₁ β₁ _ ?_ ?_ ?_ ?_
      · intro z hz; exact hzm z (Finset.mem_filter.mp hz).1
      · intro z hz
        have hzf := (Finset.mem_filter.mp hz).1
        have hgk := (Finset.mem_filter.mp hz).2
        have h1 : lamOf q z.2 < (k : ℝ) + 1 := by
          have hh := Nat.lt_floor_add_one (lamOf q z.2)
          rw [hgk] at hh; push_cast at hh ⊢; linarith
        exact le_min h1.le (le_of_lt (hlamlt z hzf))
      · intro z hz; exact him z (Finset.mem_filter.mp hz).1
      · intro z hz; exact hexc z (Finset.mem_filter.mp hz).1
    have hstep3 : Siegel.pairCountHeight χ₁ β₁ (min ((k : ℝ) + 1) (Real.log q)) T₀
        ≤ C * lam1 * Real.exp (c * min ((k : ℝ) + 1) (Real.log q)) * T₀ ^ c' :=
      hcnt _ T₀ htk_pos htk_le hT₀
    calc (∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
          (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
        ≤ Real.exp (-(49 / 10) * k) * (∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
            (zeroMult z.1 z.2 : ℝ)) := hstep1
      _ ≤ Real.exp (-(49 / 10) * k)
            * (C * lam1 * Real.exp (c * min ((k : ℝ) + 1) (Real.log q)) * T₀ ^ c') :=
          mul_le_mul_of_nonneg_left (le_trans hstep2 hstep3) (Real.exp_nonneg _)
      _ = C * lam1 * T₀ ^ c' * (Real.exp (-(49 / 10) * k)
            * Real.exp (c * min ((k : ℝ) + 1) (Real.log q))) := by ring
  have hterm : ∀ k ∈ Finset.range K,
      Real.exp (-(49 / 10) * k) * Real.exp (c * min ((k : ℝ) + 1) (Real.log q))
        ≤ Real.exp cs * (Real.exp (cs - 49 / 10)) ^ k := by
    intro k hk
    have htk_nonneg : 0 ≤ min ((k : ℝ) + 1) (Real.log q) :=
      le_of_lt (lt_min (by positivity) hlog)
    have htk_le' : min ((k : ℝ) + 1) (Real.log q) ≤ (k : ℝ) + 1 := min_le_left _ _
    have hkey : c * min ((k : ℝ) + 1) (Real.log q) ≤ cs * ((k : ℝ) + 1) := by
      rcases lt_or_ge 0 c with hc0 | hc0
      · have hcs_eq : cs = c := max_eq_left (le_of_lt hc0)
        rw [hcs_eq]
        exact mul_le_mul_of_nonneg_left htk_le' (le_of_lt hc0)
      · have hcs_eq : cs = 0 := max_eq_right hc0
        rw [hcs_eq, zero_mul]
        exact mul_nonpos_of_nonpos_of_nonneg hc0 htk_nonneg
    have hpow : Real.exp cs * (Real.exp (cs - 49 / 10)) ^ k
        = Real.exp (cs + ((k : ℝ) * (cs - 49 / 10))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    rw [hpow, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [hkey]
  have hsum : (∑ k ∈ Finset.range K, Real.exp (-(49 / 10) * k)
        * Real.exp (c * min ((k : ℝ) + 1) (Real.log q)))
      ≤ Real.exp cs * (1 - Real.exp (cs - 49 / 10))⁻¹ := by
    calc (∑ k ∈ Finset.range K, Real.exp (-(49 / 10) * k)
            * Real.exp (c * min ((k : ℝ) + 1) (Real.log q)))
        ≤ ∑ k ∈ Finset.range K, Real.exp cs * (Real.exp (cs - 49 / 10)) ^ k :=
          Finset.sum_le_sum hterm
      _ = Real.exp cs * ∑ k ∈ Finset.range K, (Real.exp (cs - 49 / 10)) ^ k := by
          rw [Finset.mul_sum]
      _ ≤ Real.exp cs * (1 - Real.exp (cs - 49 / 10))⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
          rw [← tsum_geometric_of_lt_one hr0 hr1]
          exact Summable.sum_le_tsum (Finset.range K) (fun i _ => by positivity)
            (summable_geometric_of_lt_one hr0 hr1)
  calc (∑ k ∈ Finset.range K, ∑ z ∈ S.filter (fun z => Nat.floor (lamOf q z.2) = k),
          (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
      ≤ ∑ k ∈ Finset.range K, C * lam1 * T₀ ^ c' * (Real.exp (-(49 / 10) * k)
          * Real.exp (c * min ((k : ℝ) + 1) (Real.log q))) := Finset.sum_le_sum hfib
    _ = C * lam1 * T₀ ^ c' * ∑ k ∈ Finset.range K, (Real.exp (-(49 / 10) * k)
          * Real.exp (c * min ((k : ℝ) + 1) (Real.log q))) := by rw [Finset.mul_sum]
    _ ≤ C * lam1 * T₀ ^ c' * (Real.exp cs * (1 - Real.exp (cs - 49 / 10))⁻¹) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (mul_nonneg hC.le hlam1.le)
          (Real.rpow_nonneg hT₀pos.le c'))
    _ = C * lam1 * (Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹) * T₀ ^ c' := by
        rw [← hcsdef]
        ring



/-- Dyadic rpow bookkeeping: `(4^j)^{-1}·2^{j c'} = (2^{c'-2})^j`. -/
private lemma dyadic_key (c' : ℝ) (j : ℕ) :
    ((4 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ ((j : ℝ) * c') = ((2 : ℝ) ^ (c' - 2)) ^ j := by
  rw [show ((4 : ℝ) ^ j)⁻¹ = ((2 : ℝ) ^ (2 * (j : ℝ)))⁻¹ by
        rw [show (4 : ℝ) ^ j = (2 : ℝ) ^ (2 * (j : ℝ)) by
              rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul,
                ← Real.rpow_natCast 2 (2 * j)]
              push_cast; ring]]
  rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [show -(2 * (j : ℝ)) + (j : ℝ) * c' = (c' - 2) * (j : ℝ) by ring]
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

/-- The dyadic height layer index of a pair, `⌊log₂ ⌊|Im ρ|⌋⌋`. -/
private noncomputable def jj {q : ℕ} (z : DirichletCharacter ℂ q × ℂ) : ℕ :=
  Nat.log 2 (Nat.floor |z.2.im|)

/-- **The high-zero (`|Im ρ| > 1`) mass of a finite set of zero-pairs** — the version of
`Work.LinnikAreas.high_finset_bound` in which the height-density count is assumed only for heights
`T ≥ log q`.  With the count `pairCountHeight ≤ C·lam1·e^{ct}·T^{c'}` (`c < 49/10`, `c' < 2`) the
kernel sum over the high zeros is `≤ 4·C·lam1·D·2^{c'}·(1-2^{c'-2})^{-1}·(log q)^{c'-2}` with
`D = e^{max c 0}·(1 - e^{max c 0 - 49/10})^{-1}`.  The dyadic height layers consume the count at
`T₀ = 2^{j+1}·log q ≥ log q` only, which is precisely the range in which the `λ₁`-free log-free
family count is available (the family count needs height `T/log q ≥ 1`). -/
lemma high_finset_bound_hi {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C c c' lam1 : ℝ} (hC : 0 < C) (hlam1 : 0 < lam1) (hc : c < 49 / 10) (hc' : c' < 2)
    (hcnt : ∀ t T : ℝ, 0 < t → t ≤ Real.log q → Real.log q ≤ T →
        Siegel.pairCountHeight χ₁ β₁ t T ≤ C * lam1 * Real.exp (c * t) * T ^ c')
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, zeroMult z.1 z.2 ≠ 0)
    (hhigh : ∀ z ∈ S, 1 < |z.2.im|)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁)) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
      ≤ 4 * C * lam1 * (Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹)
          * ((2 : ℝ) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹) * (Real.log q) ^ (c' - 2) := by
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hrm : (2 : ℝ) ^ (c' - 2) < 1 := by
    have h1 : 1 < (2 : ℝ) ^ (2 - c') := Real.one_lt_rpow (by norm_num) (by linarith)
    rw [show c' - 2 = -(2 - c') by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ h1
  have hrm0 : 0 ≤ (2 : ℝ) ^ (c' - 2) := Real.rpow_nonneg (by norm_num) _
  set D : ℝ := Real.exp (max c 0) * (1 - Real.exp (max c 0 - 49 / 10))⁻¹ with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    have h1 : Real.exp (max c 0 - 49 / 10) < 1 := Real.exp_lt_one_iff.mpr (by
      have := max_lt hc (by norm_num : (0 : ℝ) < 49 / 10); linarith)
    positivity
  -- step 1: kernel bound
  have hker : (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
      ≤ ∑ z ∈ S, 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / (|z.2.im| * Real.log q) ^ 2 :=
    Finset.sum_le_sum (fun z hz => high_kernel_le hq z (hzm z hz) (hhigh z hz))
  -- step 2: per-z bound `4w/(|Im|logq)² ≤ (4/log²q)·(w·(4^{jj})^{-1})`
  have hstep : (∑ z ∈ S, 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          / (|z.2.im| * Real.log q) ^ 2)
      ≤ (4 / (Real.log q) ^ 2) * ∑ z ∈ S,
          ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            * ((4 : ℝ) ^ (jj z))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun z hz => ?_)
    have him1 : 1 < |z.2.im| := hhigh z hz
    have hw0 : 0 ≤ (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2) := by positivity
    have h4 : (4 : ℝ) ^ (jj z) ≤ |z.2.im| ^ 2 := by
      have hle : (2 : ℝ) ^ (jj z) ≤ |z.2.im| := by
        have hn1 : 1 ≤ Nat.floor |z.2.im| := Nat.floor_pos.mpr him1.le
        have hn : Nat.floor |z.2.im| ≠ 0 := by omega
        have hh := Nat.pow_log_le_self 2 hn
        have h1 : (2 : ℝ) ^ (jj z) ≤ (Nat.floor |z.2.im| : ℝ) := by
          have h2 : (((2:ℕ) ^ Nat.log 2 (Nat.floor |z.2.im|) : ℕ) : ℝ)
              ≤ (Nat.floor |z.2.im| : ℝ) := Nat.cast_le.mpr hh
          push_cast at h2
          simpa [jj] using h2
        have h3 : (Nat.floor |z.2.im| : ℝ) ≤ |z.2.im| := Nat.floor_le (abs_nonneg _)
        linarith
      have h3 : (4 : ℝ) ^ (jj z) = ((2 : ℝ) ^ (jj z)) ^ 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
        exact (pow_mul (2 : ℝ) 2 (jj z)).symm.trans (pow_mul' (2 : ℝ) 2 (jj z))
      rw [h3]
      exact pow_le_pow_left₀ (by positivity) hle 2
    have hpos : 0 < (4 : ℝ) ^ (jj z) * (Real.log q) ^ 2 := by positivity
    have hle2 : (4 : ℝ) ^ (jj z) * (Real.log q) ^ 2 ≤ |z.2.im| ^ 2 * (Real.log q) ^ 2 :=
      mul_le_mul_of_nonneg_right h4 (by positivity)
    calc 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            / (|z.2.im| * Real.log q) ^ 2
        = 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            / (|z.2.im| ^ 2 * (Real.log q) ^ 2) := by rw [mul_pow]
      _ ≤ 4 * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            / ((4 : ℝ) ^ (jj z) * (Real.log q) ^ 2) :=
          div_le_div_of_nonneg_left (by positivity) hpos hle2
      _ = (4 / (Real.log q) ^ 2) * (((zeroMult z.1 z.2 : ℝ)
              * Real.exp (-(49 / 10) * lamOf q z.2)) * ((4 : ℝ) ^ (jj z))⁻¹) := by
          field_simp
  refine le_trans hker (le_trans hstep ?_)
  rw [← Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem jj hz)
        (fun z => ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            * ((4 : ℝ) ^ (jj z))⁻¹)]
  have hperj : ∀ j : ℕ,
      ((4 : ℝ) ^ j)⁻¹ * (C * lam1 * D * (((2 : ℝ) ^ (j + 1) * Real.log q) ^ c'))
        = C * lam1 * D * 2 ^ c' * (Real.log q) ^ c' * ((2 : ℝ) ^ (c' - 2)) ^ j := by
    intro j
    rw [Real.mul_rpow (by positivity) hlog.le,
      show (((2 : ℝ) ^ (j + 1)) ^ c') = (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * c') by
        rw [← Real.rpow_natCast 2 (j + 1), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)],
      show ((j + 1 : ℕ) : ℝ) * c' = ((j : ℝ) * c' + c') by push_cast; ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show ((4 : ℝ) ^ j)⁻¹
          * (C * lam1 * D * ((2 : ℝ) ^ ((j : ℝ) * c') * (2 : ℝ) ^ c' * (Real.log q) ^ c'))
        = C * lam1 * D * 2 ^ c' * (Real.log q) ^ c'
          * (((4 : ℝ) ^ j)⁻¹ * (2 : ℝ) ^ ((j : ℝ) * c')) by ring]
    rw [dyadic_key]
  have hfib : ∀ j ∈ S.image jj,
      (∑ z ∈ S.filter (fun z => jj z = j),
          ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            * ((4 : ℝ) ^ (jj z))⁻¹)
      ≤ C * lam1 * D * 2 ^ c' * (Real.log q) ^ c' * ((2 : ℝ) ^ (c' - 2)) ^ j := by
    intro j hj
    have hT0 : Real.log q ≤ (2 : ℝ) ^ (j + 1) * Real.log q := by
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        calc (2 : ℝ) = (2 : ℝ) ^ 1 := by ring
          _ ≤ (2 : ℝ) ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith [h2, hlog]
    have him : ∀ z ∈ S.filter (fun z => jj z = j),
        |z.2.im| * Real.log q ≤ (2 : ℝ) ^ (j + 1) * Real.log q := by
      intro z hz
      have hzf : z ∈ S := (Finset.mem_filter.mp hz).1
      have hjeq : jj z = j := (Finset.mem_filter.mp hz).2
      have him1 : 1 < |z.2.im| := hhigh z hzf
      have hlt : |z.2.im| < (2 : ℝ) ^ (j + 1) := by
        have h1 : Nat.floor |z.2.im| < 2 ^ (Nat.log 2 (Nat.floor |z.2.im|) + 1) :=
          Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Nat.floor |z.2.im|)
        have hjeq' : Nat.log 2 (Nat.floor |z.2.im|) = j := hjeq
        rw [hjeq'] at h1
        have h2 : (Nat.floor |z.2.im| : ℝ) + 1 ≤ (2 : ℝ) ^ (j + 1) := by
          have h3 : Nat.floor |z.2.im| + 1 ≤ 2 ^ (j + 1) := h1
          exact_mod_cast h3
        have h4 : |z.2.im| < (Nat.floor |z.2.im| : ℝ) + 1 := Nat.lt_floor_add_one _
        linarith
      exact mul_le_mul_of_nonneg_right hlt.le hlog.le
    have habel := abel_lam_hi hq χ₁ β₁ hC hlam1 hc hcnt hT0
      (S.filter (fun z => jj z = j))
      (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
      (fun z hz => hexc z (Finset.mem_filter.mp hz).1) him
    calc (∑ z ∈ S.filter (fun z => jj z = j),
          ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
            * ((4 : ℝ) ^ (jj z))⁻¹)
        = (∑ z ∈ S.filter (fun z => jj z = j),
            ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
              * ((4 : ℝ) ^ j)⁻¹) := by
          refine Finset.sum_congr rfl (fun z hz => ?_)
          rw [(Finset.mem_filter.mp hz).2]
      _ = ((4 : ℝ) ^ j)⁻¹ * (∑ z ∈ S.filter (fun z => jj z = j),
            ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun z _ => by ring)
      _ ≤ ((4 : ℝ) ^ j)⁻¹ * (C * lam1 * D * (((2 : ℝ) ^ (j + 1) * Real.log q) ^ c')) :=
          mul_le_mul_of_nonneg_left habel (by positivity)
      _ = C * lam1 * D * 2 ^ c' * (Real.log q) ^ c' * ((2 : ℝ) ^ (c' - 2)) ^ j := hperj j
  have hmid : (∑ j ∈ S.image jj, ∑ z ∈ S.filter (fun z => jj z = j),
        ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          * ((4 : ℝ) ^ (jj z))⁻¹)
      ≤ C * lam1 * D * 2 ^ c' * (Real.log q) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹ := by
    refine le_trans (Finset.sum_le_sum hfib) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← tsum_geometric_of_lt_one hrm0 hrm]
    exact Summable.sum_le_tsum (S.image jj) (fun i _ => by positivity)
      (summable_geometric_of_lt_one hrm0 hrm)
  have hconcl : (4 / (Real.log q) ^ 2)
        * (C * lam1 * D * 2 ^ c' * (Real.log q) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹)
      = 4 * C * lam1 * D * ((2 : ℝ) ^ c' * (1 - (2 : ℝ) ^ (c' - 2))⁻¹)
          * (Real.log q) ^ (c' - 2) := by
    have hrpow : (Real.log q) ^ c' = (Real.log q) ^ (c' - 2) * (Real.log q) ^ 2 := by
      rw [show (Real.log q) ^ 2 = (Real.log q) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast],
        ← Real.rpow_add hlog]
      congr 1; ring
    rw [hrpow]
    field_simp
  exact le_trans (mul_le_mul_of_nonneg_left hmid (by positivity)) (le_of_eq hconcl)




/-- **The `λ₁`-free height pair count.**  If the log-free family count holds in the form
`famCount q σ T ≤ C·e^{c(1-σ)𝓛}·T^{c'}` for `0 ≤ σ ≤ 1`, `T ≥ 1`, then for `0 < t ≤ 𝓛` and
`𝓛 ≤ T` the multiplicity-weighted number of pairs `(χ,ρ) ≠ (χ₁,β₁)` with `λ(ρ) ≤ t` and
`|Im ρ|·𝓛 ≤ T` is at most `C·𝓛^{-c'}·e^{ct}·T^{c'}`.  The proof is
`pairCountHeight_le_famCount` (the pair count is dominated by the family count at the height
`T/𝓛 ≥ 1`) followed by the substitutions `σ = 1 - t/𝓛` and
`(T/𝓛)^{c'} = T^{c'}·𝓛^{-c'}`. -/
lemma pairCountHeight_le_famCount_scaled {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) {C c c' : ℝ}
    (hfam : ∀ σ T : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
        Work.ZeroDensity.famCount q σ T
          ≤ C * Real.exp (c * ((1 - σ) * Real.log q)) * T ^ c')
    {t T : ℝ} (ht : 0 < t) (htL : t ≤ Real.log q) (hT : Real.log q ≤ T) :
    Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T
      ≤ C * (Real.log q) ^ (-c') * Real.exp (c * t) * T ^ c' := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hTpos : 0 < T := lt_of_lt_of_le hlog hT
  have hTdiv : 1 ≤ T / Real.log q := (le_div_iff₀ hlog).mpr (by linarith)
  have hdiv_le : t / Real.log q ≤ 1 := (div_le_iff₀ hlog).mpr (by linarith)
  have hsig0 : 0 ≤ 1 - t / Real.log q := by linarith
  have hsig1 : 1 - t / Real.log q ≤ 1 := by
    have : 0 ≤ t / Real.log q := by positivity
    linarith
  refine le_trans (pairCountHeight_le_famCount (q := q) hq χ₁ β₁ (t := t) (T := T))
    (le_trans (hfam (1 - t / Real.log q) (T / Real.log q) hsig0 hsig1 hTdiv) ?_)
  have hσ : (1 - (1 - t / Real.log q)) * Real.log q = t := by
    rw [sub_sub_cancel]
    exact div_mul_cancel₀ t hlog.ne'
  have hdiv : (T / Real.log q) ^ c' = T ^ c' * (Real.log q) ^ (-c') := by
    rw [Real.div_rpow hTpos.le hlog.le, div_eq_mul_inv, ← Real.rpow_neg hlog.le c']
  rw [hσ, hdiv]
  exact le_of_eq (by ring)

/-- **The `λ₁`-free bound on the far-height zero mass of AREA 6.**  From the `λ₁`-free log-free
family count in the height direction (`LogFreeFamHeight (5/2) (3/2)`) alone, the high-zero
(`|Im ρ| > 1`) part of the AREA 6 zero sum is `≪ 𝓛^{-2}`, hence in particular
`Siegel.RestHighFreeSpec (-3/2)`.

The constants are explicit: with `C₂, q₀` the constants of the family count,
`restHighZeroSum ≤ (4·C₂·D·B + 1)·𝓛^{-3/2}` for `q ≥ max q₀ 3`, where
`D = e^{max (5/2) 0}·(1-e^{max (5/2) 0 - 49/10})^{-1}` and `B = 2^{3/2}·(1-2^{-1/2})^{-1}`; the
true size is `4·C₂·D·B·𝓛^{-2}`, which is smaller than the claimed `𝓛^{-3/2}` because `𝓛 ≥ 1`. -/
theorem RestHighFree (hfam : Work.ZeroDensity.LogFreeFamHeight (5 / 2) (3 / 2)) :
    Work.LinnikAreas.Siegel.RestHighFreeSpec (-3 / 2) := by
  obtain ⟨C₂, hC₂, q₀, hfam₀⟩ := hfam
  refine ⟨4 * C₂ * (Real.exp (max (5 / 2 : ℝ) 0)
        * (1 - Real.exp (max (5 / 2 : ℝ) 0 - 49 / 10))⁻¹)
      * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹) + 1, ?_,
    max (max q₀ 2) 3, ?_⟩
  · -- positivity of the constant
    have hD : 0 < Real.exp (max (5 / 2 : ℝ) 0)
        * (1 - Real.exp (max (5 / 2 : ℝ) 0 - 49 / 10))⁻¹ := by
      have h1 : Real.exp (max (5 / 2 : ℝ) 0 - 49 / 10) < 1 := by
        rw [Real.exp_lt_one_iff]
        norm_num
      positivity
    have hB : 0 < (2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹ := by
      have h1 : (2 : ℝ) ^ ((3 / 2 : ℝ) - 2) < 1 := by
        have h2 : 1 < (2 : ℝ) ^ (2 - (3 / 2 : ℝ)) :=
          Real.one_lt_rpow (by norm_num) (by norm_num)
        rw [show (3 / 2 : ℝ) - 2 = -(2 - 3 / 2) by norm_num, Real.rpow_neg (by norm_num)]
        exact inv_lt_one_of_one_lt₀ h2
      positivity
    exact add_pos (mul_pos (mul_pos (mul_pos (by norm_num) hC₂) hD) hB) (by norm_num)
  · intro q hq hNq χ₁ β₁ hχ hsq hβ hz hlam
    have hq0 : q₀ ≤ q := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq)
    have hq2 : 2 ≤ q := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hq)
    have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
    have hq1 : 1 < q := by omega
    have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
    have hlog1 : 1 ≤ Real.log (q : ℝ) := by
      have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
      have h4 : Real.log 3 ≤ Real.log q := Real.log_le_log (by norm_num) h3
      have h5 : 1 ≤ Real.log 3 := by
        have h6 := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
        rwa [Real.log_exp] at h6
      linarith
    -- (1) the `λ₁`-free counting hypothesis in the shape consumed by the Abel summation
    have hcnt : ∀ t T : ℝ, 0 < t → t ≤ Real.log q → Real.log q ≤ T →
        Work.LinnikAreas.Siegel.pairCountHeight χ₁ β₁ t T
          ≤ C₂ * (Real.log q) ^ (-(3 / 2 : ℝ))
            * Real.exp ((5 / 2) * t) * T ^ (3 / 2 : ℝ) :=
      fun t T ht htL hT => pairCountHeight_le_famCount_scaled (q := q) hq1 χ₁ β₁
        (fun σ T h1 h2 h3 => hfam₀ q hq0 σ T h1 h2 h3) ht htL hT
    have hlam1 : 0 < (Real.log q) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hlog _
    -- (2) the finite-set bound
    let p : DirichletCharacter ℂ q × ℂ → Prop := fun z =>
      Work.LinnikContract.zeroMult z.1 z.2 ≠ 0 ∧ 1 < |z.2.im| ∧ ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))
    let F : DirichletCharacter ℂ q × ℂ → ℝ := fun z =>
      if p z then (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
          * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ else 0
    have hFnn : 0 ≤ F := fun z => by
      simp only [F]; split_ifs with hp
      · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
      · exact le_refl 0
    have hFbound : ∀ u : Finset (DirichletCharacter ℂ q × ℂ), ∑ z ∈ u, F z
        ≤ 4 * C₂ * (Real.log q) ^ (-(3 / 2 : ℝ))
            * (Real.exp (max (5 / 2 : ℝ) 0)
              * (1 - Real.exp (max (5 / 2 : ℝ) 0 - 49 / 10))⁻¹)
            * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
            * (Real.log q) ^ ((3 / 2 : ℝ) - 2) := by
      intro u
      have hsum_eq : ∑ z ∈ u, F z = ∑ z ∈ u.filter p, F z := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro z hz hnotin
        have hp : ¬ p z := fun hpp => hnotin (Finset.mem_filter.mpr ⟨hz, hpp⟩)
        simp only [F]; rw [if_neg hp]
      rw [hsum_eq]
      have hSF : ∑ z ∈ u.filter p, F z = ∑ z ∈ u.filter p,
          (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)
            * ‖Work.LinnikContract.Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ := by
        refine Finset.sum_congr rfl (fun z hz => ?_)
        have hp : p z := (Finset.mem_filter.mp hz).2
        simp only [F]; rw [if_pos hp]
      rw [hSF]
      exact high_finset_bound_hi hq1 χ₁ β₁ (C := C₂) (c := 5 / 2) (c' := 3 / 2)
        (lam1 := (Real.log q) ^ (-(3 / 2 : ℝ))) hC₂ hlam1 (by norm_num) (by norm_num) hcnt
        (u.filter p) (fun z hz => (Finset.mem_filter.mp hz).2.1)
        (fun z hz => (Finset.mem_filter.mp hz).2.2.1)
        (fun z hz => (Finset.mem_filter.mp hz).2.2.2)
    have hsumm : Summable F := summable_of_sum_le hFnn hFbound
    have htsum : ∑' z : DirichletCharacter ℂ q × ℂ, F z
        ≤ 4 * C₂ * (Real.log q) ^ (-(3 / 2 : ℝ))
            * (Real.exp (max (5 / 2 : ℝ) 0)
              * (1 - Real.exp (max (5 / 2 : ℝ) 0 - 49 / 10))⁻¹)
            * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
            * (Real.log q) ^ ((3 / 2 : ℝ) - 2) :=
      Real.tsum_le_of_sum_le hFnn hFbound
    rw [Summable.tsum_prod hsumm] at htsum
    rw [tsum_fintype] at htsum
    have hEq : Siegel.restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
        = ∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, F (χ, ρ) := rfl
    rw [hEq]
    -- the exponent of the target is written `(-3)/2` in the statement, `-(3/2)` here
    rw [show ((-3 : ℝ) / 2) = -(3 / 2 : ℝ) by norm_num]
    refine le_trans htsum ?_
    -- (3) the closing arithmetic: `𝓛^{-3/2}·𝓛^{-1/2} = 𝓛^{-2} ≤ 𝓛^{-3/2}` (as `𝓛 ≥ 1`)
    have hprod : (Real.log q) ^ (-(3 / 2 : ℝ)) * (Real.log q) ^ ((3 / 2 : ℝ) - 2)
        = (Real.log q) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add hlog]
      norm_num
    have hle : (Real.log q) ^ (-(2 : ℝ)) ≤ (Real.log q) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
    have hnn : 0 ≤ 4 * C₂ * (Real.exp (max (5 / 2 : ℝ) 0)
        * (1 - Real.exp (max (5 / 2 : ℝ) 0 - 49 / 10))⁻¹)
        * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹) := by
      have hD : 0 ≤ Real.exp (max (5 / 2 : ℝ) 0)
          * (1 - Real.exp (max (5 / 2 : ℝ) 0 - 49 / 10))⁻¹ := by
        have h1 : Real.exp (max (5 / 2 : ℝ) 0 - 49 / 10) < 1 := by
          rw [Real.exp_lt_one_iff]; norm_num
        positivity
      have hB : 0 ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹ := by
        have h1 : (2 : ℝ) ^ ((3 / 2 : ℝ) - 2) < 1 := by
          have h2 : 1 < (2 : ℝ) ^ (2 - (3 / 2 : ℝ)) :=
            Real.one_lt_rpow (by norm_num) (by norm_num)
          rw [show (3 / 2 : ℝ) - 2 = -(2 - 3 / 2) by norm_num, Real.rpow_neg (by norm_num)]
          exact inv_lt_one_of_one_lt₀ h2
        positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₂.le) hD) hB
    rw [show 4 * C₂ * (Real.log q) ^ (-(3 / 2 : ℝ))
          * (Real.exp (max (5 / 2 : ℝ) 0)
            * (1 - Real.exp (max (5 / 2 : ℝ) 0 - 49 / 10))⁻¹)
          * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
          * (Real.log q) ^ ((3 / 2 : ℝ) - 2)
        = 4 * C₂ * (Real.exp (max (5 / 2 : ℝ) 0)
            * (1 - Real.exp (max (5 / 2 : ℝ) 0 - 49 / 10))⁻¹)
          * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
          * ((Real.log q) ^ (-(3 / 2 : ℝ)) * (Real.log q) ^ ((3 / 2 : ℝ) - 2)) by ring,
      hprod]
    have hscalar : 4 * C₂ * (Real.exp (max (5 / 2 : ℝ) 0)
          * (1 - Real.exp (max (5 / 2 : ℝ) 0 - 49 / 10))⁻¹)
          * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)
        ≤ (4 * C₂ * (Real.exp (max (5 / 2 : ℝ) 0)
            * (1 - Real.exp (max (5 / 2 : ℝ) 0 - 49 / 10))⁻¹)
          * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹)) + 1 :=
      le_add_of_nonneg_right (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hle hnn)
      (mul_le_mul_of_nonneg_right hscalar hlam1.le)

end Work.LinnikAreas
