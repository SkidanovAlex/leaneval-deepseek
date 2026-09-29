import Mathlib
import Submission.Work.TMC16Core.Assembly.Consts
import Submission.Work.TMC16Core.Assembly.NR1
import Submission.Work.TMC16Core.NrFinal.nr_uniform
import Submission.Work.TMC16Core.Core.nr_ablock
import Submission.Work.TMC16Core.Basic.lemma_9_3
import Submission.Work.TMC16Core.NrFinal.nr_regular
import Submission.Work.TMC16Core.Assembly.NrParamsDefs
import Submission.Work.Assembly.nr_params

namespace Work.TMC16Core.Assembly

set_option maxHeartbeats 4000000

open Work.TMC16Core
open Work.TMC16Core.Core

noncomputable section

/-- **The window fit of the non-resonant case.**  If `a' + b' = s` and the window parameter
`δ` satisfies `δ ≤ b' q(n-1)/K` (`K = Knr q n s = 2 s q(n-1) - 1`), then the left window
`I1nr q n s a'` lies in the `δ`-window `[-((1-δ)K), -δK]`.  This is exactly the hypothesis
`hsub` of `Core.nr_ablock` (with the singular point at the origin). -/
theorem nr_i1win {q : ℕ → ℕ} {n s a' b' : ℕ} {δ : ℝ}
    (hs : 1 ≤ s) (hq : 1 ≤ q (n - 1)) (hab : a' + b' = s) (hQ : 0 < (q (n - 1) : ℝ))
    (hδ : δ ≤ (b' : ℝ) * (q (n - 1) : ℝ) / (Knr q n s : ℝ)) :
    ∀ x ∈ I1nr q n s a', -((1 - δ) * (Knr q n s : ℝ)) ≤ (x : ℝ) ∧
      (x : ℝ) ≤ -(δ * (Knr q n s : ℝ)) := by
  intro x hx
  simp only [I1nr, Finset.mem_Icc, Tnr] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hQR : (q (n - 1) : ℝ) ≠ 0 := ne_of_gt hQ
  have hKcast : (Knr q n s : ℝ) = 2 * (s : ℝ) * (q (n - 1) : ℝ) - 1 :=
    knr_castR hs hq
  have hKpos : (0 : ℝ) < (Knr q n s : ℝ) := by
    rw [hKcast]
    have h1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have h2 : (1 : ℝ) ≤ (q (n - 1) : ℝ) := by exact_mod_cast hq
    nlinarith [h1, h2]
  have hx1r : -((s : ℝ) * (q (n - 1) : ℝ)) + 1 - ((a' : ℕ) : ℝ) * (q (n - 1) : ℝ)
      ≤ (x : ℝ) := by
    have h2 : ((-((s : ℤ) * (q (n - 1) : ℤ)) + 1
        - ((a' : ℕ) : ℤ) * (q (n - 1) : ℤ) : ℤ) : ℝ) ≤ ((x : ℤ) : ℝ) := by
      exact_mod_cast hx1
    push_cast at h2
    linarith [h2]
  have hx2r : (x : ℝ) ≤ -((s : ℝ) * (q (n - 1) : ℝ))
      + ((a' : ℕ) : ℝ) * (q (n - 1) : ℝ) := by
    have h2 : ((x : ℤ) : ℝ) ≤ ((-((s : ℤ) * (q (n - 1) : ℤ))
        + ((a' : ℕ) : ℤ) * (q (n - 1) : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hx2
    push_cast at h2
    linarith [h2]
  have hfitQ : ((a' : ℕ) : ℝ) * (q (n - 1) : ℝ)
      ≤ (s : ℝ) * (q (n - 1) : ℝ) * (1 - 2 * δ) + δ := by
    have h1 : δ * (Knr q n s : ℝ) ≤ (b' : ℝ) * (q (n - 1) : ℝ) := by
      rw [le_div_iff₀ hKpos] at hδ
      linarith [hδ]
    rw [hKcast] at h1
    have habR : ((a' : ℕ) : ℝ) + ((b' : ℕ) : ℝ) = (s : ℝ) := by exact_mod_cast hab
    nlinarith [h1, habR, hQ]
  rw [hKcast]
  constructor <;> nlinarith [hfitQ, hx1r, hx2r]

theorem nr_case1_full {α lam L : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    {n s m : ℕ} {y : ℤ} {θ c : ℝ} {E : ℂ}
    (hlam : 1 < lam) (hLlog : L = Real.log lam) (hL : 0 < L)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    (hblk : ∀ (p : ℤ) (ξ : ℝ) (k₀ : ℤ),
      k₀ ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (q (n - 1) : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((q (n - 1) : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (q (n - 1) : ℝ))
    (hn : 2 ≤ n) (hq1 : 1 ≤ q (n - 1)) (hs : 3 ≤ s)
    (hy1 : 1 ≤ y)
    (hyΔ : (y : ℝ) * Δ n ≤ 3 / 4)
    (hym : (m : ℤ) * (q n : ℤ) ≤ y) (hym' : y < ((m : ℤ) + 1) * (q n : ℤ))
    (hnres : ∀ ℓ : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - (ℓ : ℤ) * (q n : ℤ)|)
    (hsL : (2 * (s : ℤ)) * (q (n - 1) : ℤ) < (q n : ℤ))
    (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hθ : ∀ j : ℤ, |j| ≤ 2 * |y| + 6 * (s : ℤ) * (q (n - 1) : ℤ) + 4 →
      c ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α))
    (hεuub : Work.TMC16Core.Assembly.rateNR1 q n s c ≤ L / 8 + L / 100)
    (hsin : Work.TMC16Core.IsSingular α lam θ E (L - Work.TMC16Core.Assembly.csing L)
      (Work.TMC16Core.Core.Knr q n s) 0)
    (hbd : ∀ N : ℕ, Work.TMC16Core.Core.Knr q n s / 40 ≤ N →
      N ≤ Work.TMC16Core.Core.Knr q n s → ∀ ζ : ℝ,
      ‖Work.TMC16Core.pd α lam ζ E (N + 1)‖
        ≤ Real.exp ((N : ℝ) * (L + Work.TMC16Core.Assembly.eps2 L)))
    (hK40 : 40 ≤ Work.TMC16Core.Core.Knr q n s)
    (hKδ : 1 ≤ (Work.TMC16Core.Core.Knr q n s : ℝ) *
      (Work.TMC16Core.Assembly.cdelta L (Work.TMC16Core.Assembly.rateNR1 q n s c) - 1 / 40))
    (hgap : 4 * ((Work.TMC16Core.Core.Knr q n s : ℝ) + 1) *
        Real.exp (L - Work.TMC16Core.Assembly.epsA L (Work.TMC16Core.Assembly.rateNR1 q n s c))
      < Real.exp ((Work.TMC16Core.Core.Knr q n s : ℝ) *
        (Work.TMC16Core.Assembly.epsA L (Work.TMC16Core.Assembly.rateNR1 q n s c)
          - Work.TMC16Core.Assembly.eps2 L))) :
    Work.TMC16Core.IsRegularBig α lam θ E (Work.TMC16Core.Assembly.cL1 L)
      ((Work.TMC16Core.Core.Knr q n s : ℕ) : ℝ) y := by
  -- ## 0. Notations and elementary consequences of the hypotheses
  set Q : ℝ := (q (n - 1) : ℝ) with hQdef
  set K : ℕ := Knr q n s with hKdef
  set bp : ℕ := (s + 2) / 3 with hbdef
  set ap : ℕ := s - bp with hadef
  set r : ℝ := rateNR1 q n s c with hrdef
  have hQpos : 0 < Q := by rw [hQdef]; exact_mod_cast hqpos (n - 1)
  have hQ1 : 1 ≤ Q := by rw [hQdef]; exact_mod_cast hq1
  have hQne : Q ≠ 0 := ne_of_gt hQpos
  have hKcast : (K : ℝ) = 2 * (s : ℝ) * Q - 1 := by
    rw [hKdef, hQdef]
    exact knr_castR (by omega) hq1
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    rw [hKcast]
    have h1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : 1 ≤ s)
    have h2 : (1 : ℝ) ≤ Q := hQ1
    nlinarith [h1, h2]
  have hK1 : 1 ≤ K := by omega
  have hab : ap + bp = s := by omega
  have ha2 : s ≤ 2 * ap := by omega
  -- ## 1. The two available bounds on the uniformity rate `r`
  have hrlow : 200 * (Real.log Q + 1) / Q ≤ r := by
    rw [hrdef, rateNR1, hQdef]
    have hsR : (0 : ℝ) < (s : ℝ) := by
      have : (0 : ℕ) < s := by omega
      exact_mod_cast this
    have hQR : (0 : ℝ) < (q (n - 1) : ℝ) := by rw [← hQdef]; exact hQpos
    have hlog1 : 0 ≤ Real.log ((q n : ℝ) / (s : ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hsR, one_mul]
      have hqns : (s : ℤ) ≤ (q n : ℤ) := by
        have h := hsL
        have h1 : (1 : ℤ) ≤ (q (n - 1) : ℤ) := by exact_mod_cast hq1
        have h2 : (1 : ℤ) ≤ (s : ℤ) := by exact_mod_cast (by omega : 1 ≤ s)
        nlinarith [h]
      exact_mod_cast hqns
    have hlog2 : 0 ≤ Real.log (1 / c) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hc, one_mul]
      linarith [hc2]
    have ht1 : 0 ≤ 2 * Real.log ((q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ) :=
      div_nonneg (by linarith) (le_of_lt hQR)
    have ht2 : 0 ≤ 2 * Real.log (1 / c) / ((s : ℝ) * (q (n - 1) : ℝ)) :=
      div_nonneg (by linarith) (by positivity)
    have hkey : 200 * (Real.log (q (n - 1) : ℝ) + 1) / (q (n - 1) : ℝ)
        = 200 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ)
          + 200 / (q (n - 1) : ℝ) := by
      field_simp
    linarith [ht1, ht2, hkey]
  have hrup : r ≤ L / 8 + L / 100 := hεuub
  -- ## 2. The numerical parameters
  obtain ⟨hδ1, hδ2, hKδ, hεAeq0, hrlt0, heps0, hgapA0, hδfit0, hcram0⟩ :=
    Work.Assembly.nr_params (L := L) (r := r) (Q := Q) (s := s) (K := K) (b' := bp)
      hL hQ1 hs hK40 hKcast hbdef hrlow hrup
  set εA : ℝ := nrEpsA L r K with hεAdef
  set δ : ℝ := nrDelta L r K with hδdef
  have hεAeq : εA = csing L * δ - eps2 L := hεAeq0
  have hrlt : r < εA := hrlt0
  have heps : eps2 L < εA := heps0
  have hgapA : Real.log (4 * ((K : ℝ) + 1)) + L + (K : ℝ) * r < ((K : ℝ) + 1) * εA := hgapA0
  have hδfit : δ ≤ (bp : ℝ) * Q / (K : ℝ) := hδfit0
  have hcram : (L + eps2 L) * ((3 : ℝ) * (K : ℝ) / 4) + (L / 4) * ((K : ℝ) / 4 - 1)
      ≤ ((K : ℝ) + 1) * (L - εA) := hcram0
  have hrpos : 0 < r := by
    rw [hrdef]
    refine rateNR1_pos hq1 ?_ (by omega) hc (by linarith)
    have h := hsL
    have h1 : (1 : ℤ) ≤ (q (n - 1) : ℤ) := by exact_mod_cast hq1
    have h2 : (1 : ℤ) ≤ (s : ℤ) := by exact_mod_cast (by omega : 1 ≤ s)
    have : (s : ℤ) ≤ (q n : ℤ) := by nlinarith [h]
    exact_mod_cast this
  have hεApos : 0 < εA := lt_trans hrpos hrlt
  -- ## 3. The uniformity of the two windows at rate `r`
  have huni := Work.TMC16Core.NrFinal.nr_uniform (α := α) (θ := θ) (c := c) (q := q)
    (Δ := Δ) (n := n) (s := s) (a' := ap) (b' := bp) (m := m) (y := y)
    hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hblk hn hq1 (by omega) hab hy1 hyΔ hym hym'
    hnres hsL hc hc2 hθ
  -- ## 4. The `A`-window on the left window, from the singularity of `0`
  have hsub : ∀ x ∈ I1nr q n s ap,
      -((1 - δ) * (K : ℝ)) ≤ (x : ℝ) ∧ (x : ℝ) ≤ -(δ * (K : ℝ)) :=
    nr_i1win (q := q) (n := n) (s := s) (a' := ap) (b' := bp) (δ := δ)
      (by omega) hq1 hab hQpos hδfit
  have hAraw := Work.TMC16Core.Core.nr_ablock (α := α) (lam := lam) (E := E) (θ := θ)
    (L := L) (ε₁ := eps2 L) (εsing := csing L) (δ := δ) (K := K) (I₁ := I1nr q n s ap)
    hL (eps2_pos hL) (csing_pos hL) (le_of_lt (csing_lt_L hL)) hδ1 hδ2 hK40 hKδ hbd hsin hsub
  have hA : ∀ x ∈ I1nr q n s ap,
      ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖
        ≤ Real.exp (((K : ℝ) + 1) * (L - εA)) := by
    intro x hx
    refine le_trans (hAraw x hx) (Real.exp_le_exp.mpr ?_)
    have h2 : L - csing L * δ + eps2 L = L - εA := by linarith [hεAeq]
    rw [h2]
  -- ## 5. The two windows are disjoint
  have hT1 : Tnr q n s ≤ y := by
    simp only [Tnr]
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := by
      by_contra hc'
      rw [not_le] at hc'
      have h1 : (m : ℤ) + 1 ≤ 0 := by omega
      have h2 : (0 : ℤ) ≤ (q n : ℤ) := by exact_mod_cast Nat.zero_le (q n)
      have h3 : ((m : ℤ) + 1) * (q n : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h1 h2
      linarith [hym', hy1, h3]
    have h4 : (0 : ℤ) ≤ y - (m : ℤ) * (q n : ℤ) := by linarith
    have h5 := hnres m
    rw [abs_of_nonneg h4] at h5
    have h6 : (0 : ℤ) ≤ (m : ℤ) * (q n : ℤ) :=
      mul_nonneg hm0 (by exact_mod_cast Nat.zero_le (q n))
    linarith [h5, h6]
  have hcard : (I1nr q n s ap ∪ I2nr q n s bp y).card = K + 1 := by
    rw [hKdef]
    exact card_union_I1nr_I2nr hab (by omega) hq1 hT1
  -- ## 6. A site of the second window with a large continuant
  have hgap4 : 4 * ((K : ℝ) + 1) * Real.exp (L - εA)
      < Real.exp ((K : ℝ) * (εA - r)) := by
    have hK1ne : ((K : ℝ) + 1) ≠ 0 := by intro hh; linarith [hKpos, hh]
    have epos : (0 : ℝ) < Real.exp (L - εA) := Real.exp_pos _
    have epos2 : (0 : ℝ) < Real.exp ((K : ℝ) * (εA - r)) := Real.exp_pos _
    rw [← Real.log_lt_log_iff (by positivity : (0:ℝ) < 4 * ((K : ℝ) + 1) * Real.exp (L - εA)) epos2]
    rw [Real.log_mul (by positivity : (4 : ℝ) * ((K : ℝ) + 1) ≠ 0) (Real.exp_ne_zero _),
      Real.log_mul (by norm_num) hK1ne, Real.log_exp, Real.log_exp]
    have h := hgapA
    rw [Real.log_mul (by norm_num) hK1ne] at h
    linarith
  have hthr : (K : ℝ) * (((K : ℝ) + 1) * (L - εA) / (K : ℝ))
      ≤ ((K : ℝ) + 1) * (L - εA) := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hKpos)]
  obtain ⟨x₁, hx₁I₂, hbig⟩ :=
    Work.TMC16Core.NrFinal.site_step_gen_c_lt (α := α) (lam := lam) (L := L)
      (εA := εA) (ε₁ := r) (c := ((K : ℝ) + 1) * (L - εA) / (K : ℝ)) (E := E) (θ := θ)
      (K := K) (I₁ := I1nr q n s ap) (I₂ := I2nr q n s bp y)
      (by linarith) hLlog hrpos hrlt hεApos hgap4 hthr hcard huni hA
  have hlarge : Real.exp (((K : ℝ) + 1) * (L - εA))
      < ‖Work.TMC16Core.pd α lam (θ + (x₁ : ℝ) * α) E (K + 1)‖ := by
    have hcK : (((K : ℝ) + 1) * (L - εA) / (K : ℝ)) * (K : ℝ)
        = ((K : ℝ) + 1) * (L - εA) := div_mul_cancel₀ _ (ne_of_gt hKpos)
    rwa [hcK] at hbig
  -- ## 7. The geometry of the second window and the Cramer bookkeeping
  obtain ⟨hx1y, hyx2, hd1, hd2, hlo1, hlo2⟩ :=
    nr_case1_i2geo (q := q) (n := n) (s := s) (a' := ap) (b' := bp) (y := y) (x := x₁)
      hab ha2 (by omega) hq1 hK40 hx₁I₂
  have hn₀ : K / 40 ≤ (y - x₁).toNat := by
    have := hd1
    omega
  have hn₁ : K / 40 ≤ (x₁ + (K : ℤ) - 1 - y).toNat := by
    have := hd2
    omega
  have hsum : ((y - x₁ : ℤ) : ℝ) + (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) = (K : ℝ) - 1 := by
    push_cast
    ring
  have hd1R : (K : ℝ) ≤ 40 * ((y - x₁ : ℤ) : ℝ) := by exact_mod_cast hd1
  have hd2R : (K : ℝ) ≤ 40 * (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by exact_mod_cast hd2
  have hlo1R : (K : ℝ) / 4 - 1 ≤ ((y - x₁ : ℤ) : ℝ) := by
    have h := hlo1
    push_cast at h
    linarith [h]
  have hlo2R : (K : ℝ) / 4 - 1 ≤ (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by
    have h := hlo2
    push_cast at h
    linarith [h]
  have hd2le : (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) ≤ 3 * (K : ℝ) / 4 := by
    linarith [hsum, hlo1R]
  have hd1le : ((y - x₁ : ℤ) : ℝ) ≤ 3 * (K : ℝ) / 4 := by
    linarith [hsum, hlo2R]
  have hdec1 : (L + eps2 L) * (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) - ((K : ℝ) + 1) * (L - εA)
      ≤ -(L / 4) * ((y - x₁ : ℤ) : ℝ) := by
    have hpos : 0 < L + eps2 L - L / 4 := by
      have := eps2_pos hL
      linarith
    have key : (L + eps2 L) * (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ)
        + (L / 4) * ((y - x₁ : ℤ) : ℝ)
        ≤ (L + eps2 L) * (3 * (K : ℝ) / 4) + (L / 4) * ((K : ℝ) / 4 - 1) := by
      nlinarith [hsum, hd2le, hpos]
    linarith [key, hcram]
  have hdec2 : (L + eps2 L) * ((y - x₁ : ℤ) : ℝ) - ((K : ℝ) + 1) * (L - εA)
      ≤ -(L / 4) * (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by
    have hpos : 0 < L + eps2 L - L / 4 := by
      have := eps2_pos hL
      linarith
    have key : (L + eps2 L) * ((y - x₁ : ℤ) : ℝ)
        + (L / 4) * (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ)
        ≤ (L + eps2 L) * (3 * (K : ℝ) / 4) + (L / 4) * ((K : ℝ) / 4 - 1) := by
      nlinarith [hsum, hd1le, hpos]
    linarith [key, hcram]
  -- ## 8. The endgame
  exact Work.TMC16Core.Core.nr_endgame (α := α) (lam := lam) (E := E) (θ := θ) (L := L)
    (ε := εA) (ε₁ := eps2 L) (m := cL1 L) (K := K) (y := y) (j₀ := x₁)
    hL heps (cL1_pos hL) hK1 hx1y hyx2 hd1 hd2 hn₀ hn₁ hlarge hbd hdec1 hdec2

end

end Work.TMC16Core.Assembly
