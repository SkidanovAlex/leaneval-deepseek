import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.irrat_blk_nr
import Submission.Work.TMC16Core.Core.setup
import Submission.Work.TMC16Core.NrFinal.nr_uniform
import Submission.Work.TMC16Core.Assembly.nr_case1_full
import Submission.Work.TMC16Core.Assembly.theta_strand
import Submission.Work.TMC16Core.Assembly.RegWin
import Submission.Work.TMC16Core.Main.pd_glue
import Submission.Work.TMC16Core.Assembly.rate_nr_bound

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

/-- `IsRegularBig` is monotone in the decay rate: the same witnessing interval works, since
both exponents `γ' * d` and `γ * d` occur at nonnegative distances `d`. -/
theorem IsRegularBig_rate_mono {α lam θ γ γ' q : ℝ} {E : ℂ} {y : ℤ}
    (hγ : γ' ≤ γ) (h : IsRegularBig α lam θ E γ q y) :
    IsRegularBig α lam θ E γ' q y := by
  obtain ⟨x₁, x₂, h1, h2, hlen, hd1, hd2, hdet, hg1, hg2⟩ := h
  have hd1' : (0 : ℝ) ≤ ((y - x₁ : ℤ) : ℝ) := by
    exact_mod_cast (by omega : (0 : ℤ) ≤ y - x₁)
  have hd2' : (0 : ℝ) ≤ ((x₂ - y : ℤ) : ℝ) := by
    exact_mod_cast (by omega : (0 : ℤ) ≤ x₂ - y)
  refine ⟨x₁, x₂, h1, h2, hlen, hd1, hd2, hdet, ?_, ?_⟩
  · refine lt_of_lt_of_le hg1 (Real.exp_le_exp.mpr ?_)
    nlinarith [hd1', hγ]
  · refine lt_of_lt_of_le hg2 (Real.exp_le_exp.mpr ?_)
    nlinarith [hd2', hγ]

theorem nr_branch (h4 : Work.TMC16Core.P_LEBasics) (h7 : Work.TMC16Core.P_BJ_dioph)
    {α b₀ lam L : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hα : Irrational α) (hb₀ : 0 < b₀) (hDioph : Work.TMC16Core.DiophBelow α b₀)
    (hL : L = Real.log lam) (hlam : Real.exp (16 * b₀ / 9) < lam)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔpos : ∀ i, 0 < Δ i) (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) →
      Δ i ≤ Work.TMC16Core.fracDist ((j : ℝ) * α))
    {E : ℝ} (hE : E ∈ Work.TMC16Core.amoSpec α lam) {θ : ℝ}
    (hθ : θ ∉ Work.TMC16Core.Theta α) {u : ℤ → ℂ}
    (hu : Work.TMC16Core.IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ s m : ℕ, ∀ y : ℤ,
      3 ≤ s → 1 ≤ y → (y : ℝ) * Δ n ≤ 3 / 4 →
      (y : ℝ) ≤ 100 * (Real.rpow (q (n + 1) : ℝ) (8 / 9) + (q n : ℝ)) →
      (m : ℤ) * (q n : ℤ) ≤ y → y < ((m : ℤ) + 1) * (q n : ℤ) →
      (∀ ℓ : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - ℓ * (q n : ℤ)|) →
      (2 * (s : ℤ)) * (q (n - 1) : ℤ) < (q n : ℤ) →
      Real.rpow (q n : ℝ) (8 / 9) < (((s + 1) * q (n - 1) : ℕ) : ℝ) →
      Work.TMC16Core.IsRegularBig α lam θ (E : ℂ) (L / 100)
        ((Work.TMC16Core.Core.Knr q n s : ℕ) : ℝ) y := by
  -- ## 0. The numeric constants
  have hlam1 : 1 < lam := Core.one_lt_lam (le_of_lt hb₀) hlam
  have hLpos : 0 < L := by rw [hL]; exact Real.log_pos hlam1
  have hLb : 16 * b₀ / 9 < L := by
    rw [hL]
    have h := Real.log_lt_log (Real.exp_pos (16 * b₀ / 9)) hlam
    rwa [Real.log_exp] at h
  -- ## 1. The three eventual inputs
  obtain ⟨Cθ, Nθ, hθch⟩ := theta_strand (q := q) (Δ := Δ) hθ hqpos hmono hΔeq hΔup
  obtain ⟨Nrate, hrate⟩ := rate_nr_bound_gen (α := α) (b₀ := b₀) (L := L) (q := q) (Δ := Δ)
    hb₀ hDioph hLb hqpos hmono hΔeq hΔup Cθ
  obtain ⟨Ns, hsin0⟩ := Work.TMC16Core.Main.sing_zero_at (α := α) (lam := lam) (θ := θ)
    (E := E) (u := u) hu hu0 (m := L - csing L) (by simp only [csing]; linarith)
  obtain ⟨Nb, hbd0⟩ := Work.TMC16Core.Main.pd_bound_at h4 h7 (E := E) hα hb₀ hDioph hlam hE
    (eps2_pos hLpos)
  obtain ⟨Ksd, hside⟩ := Work.TMC16Core.Main.nr_side_conditions (L := L) hLpos
  obtain ⟨NK, hNK⟩ := Work.TMC16Core.Main.knr_ge_of_large (q := q) hqpos hmono
    (max Ns (max (40 * Nb) (max Ksd 2)))
  refine ⟨max (max Nθ Nrate) (max NK 2), ?_⟩
  intro n hn s m y hs3 hy1 hyΔ hyb hym hym' hnres hsL hres
  -- ## 2. Level bookkeeping
  have hn2 : 2 ≤ n := le_trans (le_trans (le_max_right NK 2) (le_max_right _ _)) hn
  have hnθ : Nθ ≤ n := le_trans (le_trans (le_max_left Nθ Nrate) (le_max_left _ _)) hn
  have hnr : Nrate ≤ n := le_trans (le_trans (le_max_right Nθ Nrate) (le_max_left _ _)) hn
  have hnK : NK ≤ n := le_trans (le_trans (le_max_left NK 2) (le_max_right _ _)) hn
  have hKnr : max Ns (max (40 * Nb) (max Ksd 2)) ≤ Core.Knr q n s := hNK n hnK s hs3
  have hKnr_Ns : Ns ≤ Core.Knr q n s := le_trans (le_max_left _ _) hKnr
  have hKnr_40Nb : 40 * Nb ≤ Core.Knr q n s :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hKnr
  have hKnr_Ksd : Ksd ≤ Core.Knr q n s :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hKnr
  have hq1 : 1 ≤ q (n - 1) := by have h := hqpos (n - 1); omega
  -- ## 3. The charge `c` of the θ-factor over the full range of `nr_case1_full`
  have hy0 : (0 : ℤ) ≤ y := by omega
  have hyabs : |y| = y := abs_of_nonneg hy0
  set B : ℤ := 2 * |y| + 6 * (s : ℤ) * (q (n - 1) : ℤ) + 4 with hBdef
  have hB1 : 1 ≤ B := by
    have habs : (1 : ℤ) ≤ |y| := by rw [hyabs]; exact hy1
    have hnn : (0 : ℤ) ≤ 6 * (s : ℤ) * (q (n - 1) : ℤ) := by positivity
    rw [hBdef]; omega
  have hBle : (B : ℝ) ≤ 1000 * (Real.rpow (q (n + 1) : ℝ) (8 / 9) + (q n : ℝ)) := by
    have hcast : (B : ℝ) = 2 * (y : ℝ) + 6 * (s : ℝ) * (q (n - 1) : ℝ) + 4 := by
      rw [hBdef, hyabs]; push_cast; ring
    rw [hcast]
    have hrpow1 : (1 : ℝ) ≤ Real.rpow (q (n + 1) : ℝ) (8 / 9) :=
      Real.one_le_rpow (by exact_mod_cast hqpos (n + 1)) (by norm_num)
    have hqn1 : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqpos n
    have h6s : 6 * (s : ℝ) * (q (n - 1) : ℝ) < 3 * (q n : ℝ) := by
      have h2 : (2 : ℝ) * (s : ℝ) * (q (n - 1) : ℝ) < (q n : ℝ) := by exact_mod_cast hsL
      linarith
    have h4le : (4 : ℝ) ≤ 797 * Real.rpow (q (n + 1) : ℝ) (8 / 9) + 797 * (q n : ℝ) := by
      linarith
    linarith [hyb, h6s, h4le]
  obtain ⟨c, hc0, hc2, hclog, hcrange⟩ := hθch n hnθ B hB1 hBle
  have hθc : ∀ j : ℤ, |j| ≤ 2 * |y| + 6 * (s : ℤ) * (q (n - 1) : ℤ) + 4 →
      c ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α) := by
    intro j hj
    refine hcrange j ?_
    have hjB : |j| ≤ B := by rw [hBdef]; exact hj
    have h1 : ((|j| : ℤ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast hjB
    rwa [Int.cast_abs] at h1
  -- ## 4. The uniformity rate bound
  have hsLnat : 2 * s * q (n - 1) < q n := by exact_mod_cast hsL
  have hεuub : rateNR1 q n s c ≤ L / 8 + L / 100 :=
    hrate n hnr s c hs3 hres hsLnat hc0 hclog
  -- ## 5. The two eventual inputs at scale `Knr q n s`
  have hsin' : IsSingular α lam θ (E : ℂ) (L - csing L) (Core.Knr q n s) 0 :=
    hsin0 _ hKnr_Ns
  have hbd' : ∀ N' : ℕ, Core.Knr q n s / 40 ≤ N' → N' ≤ Core.Knr q n s → ∀ ζ : ℝ,
      ‖pd α lam ζ (E : ℂ) (N' + 1)‖ ≤ Real.exp ((N' : ℝ) * (L + eps2 L)) := by
    intro N' h1 _ ζ
    have hN' : Nb ≤ N' := by omega
    have h := hbd0 N' hN' ζ
    rwa [← hL] at h
  have hblk : ∀ (p : ℤ) (ξ : ℝ) (k₀ : ℤ),
      k₀ ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (q (n - 1) : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((q (n - 1) : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (q (n - 1) : ℝ) :=
    fun p ξ k₀ hk₀ hmin =>
      Core.irrat_blk_nr hqpos hmono hΔpos hΔeq hΔup hΔlo hbest (n := n) (by omega) hk₀ hmin
  -- ## 6. The numerical side conditions at scale `Knr q n s`
  obtain ⟨hK40, hKδ, hgap⟩ := hside (rateNR1 q n s c) hεuub (Core.Knr q n s) hKnr_Ksd
  -- ## 7. The branch
  have hmain := nr_case1_full (E := (E : ℂ))
    (hlam := hlam1) (hLlog := hL) (hL := hLpos) (hqpos := hqpos) (hmono := hmono)
    (hΔpos := hΔpos) (hΔeq := hΔeq) (hΔup := hΔup) (hΔlo := hΔlo) (hbest := hbest)
    (hblk := hblk) (hn := hn2) (hq1 := hq1) (hs := hs3) (hy1 := hy1) (hyΔ := hyΔ)
    (hym := hym) (hym' := hym') (hnres := hnres) (hsL := hsL) (hc := hc0) (hc2 := hc2)
    (hθ := hθc) (hεuub := hεuub) (hsin := hsin') (hbd := hbd')
    (hK40 := hK40) (hKδ := hKδ) (hgap := hgap)
  refine IsRegularBig_rate_mono ?_ hmain
  simp only [cL1]; linarith

end Work.TMC16Core.Assembly
