import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.nr_endgame
import Submission.Work.TMC16Core.NrFinal.nr_regular
import Submission.Work.TMC16Core.Assembly.RegWin
import Submission.Work.TMC16Core.Basic.green_bound_notA_win
import Submission.Work.TMC16Core.Basic.dirMat_det

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

/-- **Generic Cramer endgame with an explicit margin `g`** (lead design C16_CLOSE_LEAD §4.2, L2).

This is the `s = 0` endgame `Assembly.s0_case` stated directly for an *arbitrary* window
family `I₁ ∪ I₂` of `K + 1` sites and an explicit margin `g` (playing the role of the
`⌈K/40⌉` of the weak geometry), with the conclusion `RegWin` — i.e. the witnessing interval
`[x₁, x₁ + K - 1]` is *named* rather than existentially hidden inside `IsRegularBig`.

Steps:
* `NrFinal.site_step_gen_c_lt` produces a site `x₁ ∈ I₂` whose continuant exceeds
  `e^{(K+1)(L-εA)}` (the `A`-deficit hypothesis `hA` is used on `I₁`, `εu`-uniformity on the
  union, and the non-generation gap `hgap`);
* `Basic.green_bound_notA_win` (Cramer) turns that into the two boundary Green's function
  bounds of the window, using the windowed continuant bound `hbd`;
* the `hkey` arithmetic (`d₁ ≥ g`, `d₂ ≤ K - 1 - g`, `L₁ ≤ L + εf`) converts the Cramer
  exponents into the decay rate `L₁`. -/
theorem endgame_g {α lam L εA εu εf L₁ g : ℝ} {E : ℂ} {θ : ℝ} {K : ℕ}
    {I₁ I₂ : Finset ℤ} {y : ℤ}
    (hlam : 1 < lam) (hLlog : L = Real.log lam) (hεu : 0 < εu) (hεf : 0 < εf)
    (hεuA : εu < εA) (hεfA : εf < εA) (hK40 : 40 ≤ K)
    (hgap : 4 * ((K : ℝ) + 1) * Real.exp (L - εA) < Real.exp ((K : ℝ) * (εA - εu)))
    (hcard : (I₁ ∪ I₂).card = K + 1)
    (huni : Work.TMC16Core.Uniform εu
      (fun j : {j : ℤ // j ∈ I₁ ∪ I₂} =>
        θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α))
    (hA : ∀ x ∈ I₁, ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
      Real.exp (((K : ℝ) + 1) * (L - εA)))
    (hg40 : (K : ℝ) ≤ 40 * g)
    (hgeo : ∀ x ∈ I₂, x ≤ y ∧ y ≤ x + (K : ℤ) - 1 ∧
      g ≤ ((y - x : ℤ) : ℝ) ∧ g ≤ ((x + (K : ℤ) - 1 - y : ℤ) : ℝ))
    (hbd : ∀ N : ℕ, K / 40 ≤ N → N ≤ K → ∀ ζ : ℝ,
      ‖Work.TMC16Core.pd α lam ζ E (N + 1)‖ ≤ Real.exp ((N : ℝ) * (L + εf)))
    (hL₁ : 0 < L₁) (hL₁le : L₁ ≤ L + εf)
    (hkey : (L + εf) * ((K : ℝ) - 1 - g) - ((K : ℝ) + 1) * (L - εA) + L₁ * g < 0) :
    Work.TMC16Core.Assembly.RegWin α lam θ E L₁ g K y := by
  have hL : 0 < L := by rw [hLlog]; exact Real.log_pos hlam
  have hεA : 0 < εA := lt_trans hεu hεuA
  have hK1 : 1 ≤ K := by omega
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    linarith
  -- ## 1. A site `x₁ ∈ I₂` with an exponentially large continuant.
  have hthr : (K : ℝ) * (((K : ℝ) + 1) * (L - εA) / (K : ℝ))
      ≤ ((K : ℝ) + 1) * (L - εA) := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hKpos)]
  obtain ⟨x₁, hx₁, hbig⟩ :=
    NrFinal.site_step_gen_c_lt (α := α) (lam := lam) (L := L) (εA := εA) (ε₁ := εu)
      (c := ((K : ℝ) + 1) * (L - εA) / (K : ℝ)) (E := E) (θ := θ) (K := K)
      (I₁ := I₁) (I₂ := I₂)
      (by linarith) hLlog hεu hεuA hεA hgap hthr hcard huni hA
  have hlarge : Real.exp (((K : ℝ) + 1) * (L - εA))
      < ‖pd α lam (θ + (x₁ : ℝ) * α) E (K + 1)‖ := by
    have hcK : (((K : ℝ) + 1) * (L - εA) / (K : ℝ)) * (K : ℝ)
        = ((K : ℝ) + 1) * (L - εA) := div_mul_cancel₀ _ (ne_of_gt hKpos)
    rwa [hcK] at hbig
  -- ## 2. Nonzero determinant (the continuant is nonzero).
  have hpdne : pd α lam (θ + (x₁ : ℝ) * α) E (K + 1) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlarge
    exact absurd hlarge (not_lt.mpr (Real.exp_pos _).le)
  have hdet : (dirMat α lam (θ + (x₁ : ℝ) * α) E K).det ≠ 0 := by
    rw [Basic.dirMat_det]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) hpdne
  -- ## 3. Geometry: `x₁` is at distance `≥ g` from both endpoints of the window.
  obtain ⟨hx1y, hyx2, hgd1, hgd2⟩ := hgeo x₁ hx₁
  have hKd1 : (K : ℤ) ≤ 40 * (y - x₁) := by
    have h1 : (K : ℝ) ≤ 40 * ((y - x₁ : ℤ) : ℝ) := by linarith [hg40, hgd1]
    exact_mod_cast h1
  have hKd2 : (K : ℤ) ≤ 40 * (x₁ + (K : ℤ) - 1 - y) := by
    have h1 : (K : ℝ) ≤ 40 * ((x₁ + (K : ℤ) - 1 - y : ℤ) : ℝ) := by
      linarith [hg40, hgd2]
    exact_mod_cast h1
  have toNat_ge : ∀ d : ℤ, 0 ≤ d → (K : ℤ) ≤ 40 * d → K / 40 ≤ d.toNat := by
    intro d hd hK
    have h3 : K ≤ 40 * d.toNat := by
      have h2 : (K : ℤ) ≤ ((40 * d.toNat : ℕ) : ℤ) := by
        push_cast
        rw [Int.toNat_of_nonneg hd]
        exact hK
      exact_mod_cast h2
    omega
  have hn₀ : K / 40 ≤ (y - x₁).toNat := toNat_ge (y - x₁) (by omega) hKd1
  have hn₁ : K / 40 ≤ (x₁ + (K : ℤ) - 1 - y).toNat :=
    toNat_ge (x₁ + (K : ℤ) - 1 - y) (by omega) hKd2
  -- ## 4. The Cramer bound on the two boundary entries of the Green's function.
  obtain ⟨hG1, hG2⟩ :=
    Basic.green_bound_notA_win (α := α) (lam := lam) (E := E) (θ := θ)
      (r := L - εA) (L := L) (ε₁ := εf) (k := K) (x₁ := x₁)
      (x₂ := x₁ + (K : ℤ) - 1) (y := y) (n₀ := K / 40)
      hbd hn₁ hn₀ rfl hx1y hyx2 hlarge
  -- ## 5. The `hkey` arithmetic.
  have hcoef : L₁ - L - εf ≤ 0 := by linarith [hL₁le]
  have hsum : ((y - x₁ : ℤ) : ℝ) + (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ)
      = (K : ℝ) - 1 := by
    push_cast
    ring
  have hdec1 : (L + εf) * (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) - ((K : ℝ) + 1) * (L - εA)
      ≤ -L₁ * ((y - x₁ : ℤ) : ℝ) := by
    have hd2eq : (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) = (K : ℝ) - 1 - ((y - x₁ : ℤ) : ℝ) := by
      linarith [hsum]
    have h2 : ((y - x₁ : ℤ) : ℝ) * (L₁ - L - εf) ≤ g * (L₁ - L - εf) := by
      simpa only [mul_comm] using mul_le_mul_of_nonpos_left hgd1 hcoef
    rw [hd2eq]
    nlinarith [h2, hkey]
  have hdec2 : (L + εf) * ((y - x₁ : ℤ) : ℝ) - ((K : ℝ) + 1) * (L - εA)
      ≤ -L₁ * (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by
    have hd1eq : ((y - x₁ : ℤ) : ℝ) = (K : ℝ) - 1 - (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by
      linarith [hsum]
    have h2 : (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) * (L₁ - L - εf) ≤ g * (L₁ - L - εf) := by
      simpa only [mul_comm] using mul_le_mul_of_nonpos_left hgd2 hcoef
    rw [hd1eq]
    nlinarith [h2, hkey]
  -- ## 6. Assemble `RegWin`.
  refine ⟨x₁, hx1y, hyx2, hgd1, hgd2, hdet, ?_, ?_⟩
  · refine lt_of_lt_of_le hG1 (Real.exp_le_exp.mpr ?_)
    linarith [hdec1]
  · refine lt_of_lt_of_le hG2 (Real.exp_le_exp.mpr ?_)
    linarith [hdec2]

end Work.TMC16Core.Assembly
