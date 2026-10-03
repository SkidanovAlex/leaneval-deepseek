/-
# `Submission.Work.FIChain.s3SplitDefs` — the two `(1.7)`-halves of the `λ⁺` level integrand

The `(1.7)`-split of the `λ⁺` level integral (`Work.FIChain.s3InnerInt_eq_split`) writes

    s3InnerInt atilc x ℓ Cm z sz
      = ∫_1^{U_ℓ} (du/u) Σ_{d ≤ ⌊u⌋₊} μ d ·
          ( g̃(ℓd)·(Ã(m₂) − Ã(m₁))  +  r̃(ℓd, m₂) − r̃(ℓd, m₁) ),

with `U_ℓ = min (sz/Cm) (x/(ℓCm))`, `m₂ = ⌊min (ℓ sz) x⌋₊`, `m₁ = ⌊max (ℓ z) (ℓ Cm u)⌋₊`,
whose two summands are the integrands of `Work.FIChain.s3MainPlus` and
`Work.FIChain.s3RemPlus`.  This module fixes the vocabulary (`s3SplitU`, `s3MainI`, `s3RemI`) and
records the elementary facts about them that the assembly
(`Work.FIChain.S3plusC_eq_main_add_rem`) needs:

* `atilc_nonneg`, `AcountAtilC_nonneg`, `AcountAtilC_mono` — the counting function of the
  squarefree-supported sequence is nonnegative and monotone;
* `abs_rtildeFull_le_mul` — the honest remainder obeys
  `|r̃(ℓd, m)| ≤ (1 + |g̃(ℓd)|)·Ã(m)`, which is what makes the REM integrand bounded on `[1, U_ℓ]`.

Definitions only plus `sorry`-free elementary lemmas.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.Ad_atilc_split_real
import Submission.ASP.S9g

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIChain

open Finset
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `u`-cut of the `λ⁺` level integral: `U_ℓ = min (sz/Cm) (x/(ℓ Cm))`. -/
def s3SplitU (x : ℕ) (z sz : ℝ) (Cm : ℕ) (ℓ : ℕ) : ℝ :=
  min (sz / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))

/-- The **MAIN integrand** of the `(1.7)`-split of the `λ⁺` level integral. -/
def s3MainI (x : ℕ) (z sz : ℝ) (Cm : ℕ) (ℓ : ℕ) (u : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
    Submission.ASP.FIgtil (ℓ * d) *
      (AcountAtilC ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
        - AcountAtilC ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)

/-- The **REM integrand** of the `(1.7)`-split of the `λ⁺` level integral. -/
def s3RemI (x : ℕ) (z sz : ℝ) (Cm : ℕ) (ℓ : ℕ) (u : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
    (Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
        Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
        ⌊min ((ℓ : ℝ) * sz) (x : ℝ)⌋₊
      - Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
          Submission.ASP.FIgtil Submission.ASP.FIa (ℓ * d)
          ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)

/-! ## Elementary facts about the counting function `Ã` and the sequence `ã` -/

/-- `ã = μ²·a ≥ 0`. -/
lemma atilc_nonneg (n : ℕ) : 0 ≤ atilc n := by
  rw [Work.FIChain.atilc, Work.FITop.atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
  positivity

/-- `Ã(k) = Σ_{n ≤ k} ã(n) ≥ 0`. -/
lemma AcountAtilC_nonneg (k : ℕ) : 0 ≤ AcountAtilC k := by
  rw [AcountAtilC, Work.FITop.AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]
  exact Finset.sum_nonneg (fun n _ => atilc_nonneg n)

/-- `Ã` is monotone. -/
lemma AcountAtilC_mono : Monotone AcountAtilC := by
  intro a b hab
  rw [AcountAtilC, AcountAtilC, Work.FITop.AcountAtil, Work.FITop.AcountAtil,
    Submission.ASP.Acount, Submission.ASP.Acount, Nat.floor_natCast, Nat.floor_natCast]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun n hn => by rw [Finset.mem_Icc] at hn ⊢; exact ⟨hn.1, le_trans hn.2 hab⟩)
    (fun n _ _ => atilc_nonneg n)

/-- `Ã(m) ≤ Ã(m')` for `m ≤ m'` as reals. -/
lemma AcountAtilC_mono_nat {m m' : ℕ} (h : m ≤ m') : AcountAtilC m ≤ AcountAtilC m' :=
  AcountAtilC_mono h

/-- `Ad ã(d, m) ≤ Ã(m)`: the congruence sum is a subsum of the full count. -/
lemma Ad_atilc_le_Acount (d m : ℕ) :
    Submission.ASP.Ad atilc d (m : ℝ) ≤ AcountAtilC m := by
  rw [AcountAtilC, Work.FITop.AcountAtil, Submission.ASP.Acount, Nat.floor_natCast,
    Submission.ASP.Ad, Nat.floor_natCast]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun n hn => (Finset.mem_filter.mp hn).1)
    (fun n _ _ => atilc_nonneg n)

/-- `Ad ã(d, m) ≥ 0`. -/
lemma Ad_atilc_nonneg (d m : ℕ) : 0 ≤ Submission.ASP.Ad atilc d (m : ℝ) := by
  rw [Submission.ASP.Ad, Nat.floor_natCast]
  exact Finset.sum_nonneg (fun n _ => atilc_nonneg n)

/-- **The REM bound**: `|r̃(ℓd, m)| ≤ (1 + |g̃(ℓd)|)·Ã(m)`.  From `(1.7)`
(`Ad_atilc_split_real`), `r̃(d,m) = Ad ã(d,m) − g̃(d)Ã(m)`, and `0 ≤ Ad ã(d,m) ≤ Ã(m)`. -/
lemma abs_rtildeFull_le_mul (d m : ℕ) :
    |Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
        Submission.ASP.FIgtil Submission.ASP.FIa d m|
      ≤ (1 + |Submission.ASP.FIgtil d|) * AcountAtilC m := by
  have hsplit := Ad_atilc_split_real d (m : ℝ)
  rw [Nat.floor_natCast] at hsplit
  have h1 : Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
        Submission.ASP.FIgtil Submission.ASP.FIa d m
      = Submission.ASP.Ad atilc d (m : ℝ)
        - Submission.ASP.FIgtil d * AcountAtilC m := by
    linarith [hsplit]
  rw [h1]
  have hAdnn := Ad_atilc_nonneg d m
  have hAdle := Ad_atilc_le_Acount d m
  have hAnn := AcountAtilC_nonneg m
  have hFle : Submission.ASP.FIgtil d ≤ |Submission.ASP.FIgtil d| := le_abs_self _
  have hFge : -Submission.ASP.FIgtil d ≤ |Submission.ASP.FIgtil d| := neg_le_abs _
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h : Submission.ASP.FIgtil d * AcountAtilC m
        ≤ |Submission.ASP.FIgtil d| * AcountAtilC m :=
      mul_le_mul_of_nonneg_right hFle hAnn
    nlinarith [h, hAnn, hAdnn]
  · have h : -(|Submission.ASP.FIgtil d| * AcountAtilC m)
        ≤ Submission.ASP.FIgtil d * AcountAtilC m := by
      have h' : -(Submission.ASP.FIgtil d) * AcountAtilC m
          ≤ |Submission.ASP.FIgtil d| * AcountAtilC m :=
        mul_le_mul_of_nonneg_right hFge hAnn
      linarith [h']
    nlinarith [h, hAnn, hAdle, hAdnn]

end

end Work.FIChain
