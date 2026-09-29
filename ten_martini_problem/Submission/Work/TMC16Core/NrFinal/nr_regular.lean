import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.green_bound_reg
import Submission.Work.TMC16Core.Basic.dirMat_det
import Submission.Work.TMC16Core.Core.site_step_gen_c

namespace Work.TMC16Core.NrFinal

open Work.TMC16Core

/-- Strict form of `Core.site_step_gen_c`.

`Core.site_step_gen_c` produces a site `x₁ ∈ I₂` whose continuant is `≥ e^{cK}`.  The
underlying non-generation argument (`Basic.lemma_9_3`) actually only uses the `A`-set
membership `‖pd‖ ≤ e^{(K+1)(L-εA)}` of the sites of `I₂`, which follows from
`‖pd‖ ≤ e^{cK}` and the threshold `K c ≤ (K+1)(L-εA)`.  Hence the same proof yields the
strict conclusion `e^{cK} < ‖pd‖`, which is the form consumed by `green_bound_reg`. -/
theorem site_step_gen_c_lt {α lam L εA ε₁ c : ℝ} {E : ℂ} {θ : ℝ} {K : ℕ}
    {I₁ I₂ : Finset ℤ}
    (hlam : 0 < lam) (hLlog : L = Real.log lam)
    (hε₁ : 0 < ε₁) (hδlt : ε₁ < εA) (hεA : 0 < εA)
    (hgap : 4 * ((K : ℝ) + 1) * Real.exp (L - εA) < Real.exp ((K : ℝ) * (εA - ε₁)))
    (hthr : (K : ℝ) * c ≤ ((K : ℝ) + 1) * (L - εA))
    (hcard : (I₁ ∪ I₂).card = K + 1)
    (huni : Work.TMC16Core.Uniform ε₁
      (fun j : {j : ℤ // j ∈ I₁ ∪ I₂} =>
        θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α))
    (hA : ∀ x ∈ I₁, ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
      Real.exp (((K : ℝ) + 1) * (L - εA))) :
    ∃ x₁ ∈ I₂,
      Real.exp (c * (K : ℝ)) < ‖Work.TMC16Core.pd α lam (θ + (x₁ : ℝ) * α) E (K + 1)‖ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨Q, hQdeg, hQ⟩ := Work.TMC16Core.Basic.pd_cheb α lam E K
  obtain ⟨θ₁, hθ₁⟩ := (Work.TMC16Core.Basic.pd_fourier_large α lam E K).2
  have hθ₀ : Real.exp ((K : ℝ) * L) / 4 ≤
      ‖pd α lam (θ₁ + (((K : ℝ) - 1) / 2) * α - (((K : ℝ) - 1) / 2) * α) E (K + 1)‖ := by
    have hEq : θ₁ + (((K : ℝ) - 1) / 2) * α - (((K : ℝ) - 1) / 2) * α = θ₁ := by ring
    rw [hEq]
    have hpow : |lam| ^ K = Real.exp ((K : ℝ) * L) := by
      rw [abs_of_pos hlam, ← Real.exp_log hlam, Real.exp_nat_mul, hLlog]
    rw [← hpow]
    linarith [Real.exp_pos ((K : ℝ) * L)]
  have hAall : ∀ j : {j : ℤ // j ∈ I₁ ∪ I₂},
      θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α ∈ AkSet α lam E K (L - εA) := by
    intro j
    rcases Finset.mem_union.mp j.2 with hj | hj
    · have h := hA j.val hj
      have heq : θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α - (((K : ℝ) - 1) / 2) * α
          = θ + ((j : ℤ) : ℝ) * α := by ring
      show ‖pd α lam (θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α
          - (((K : ℝ) - 1) / 2) * α) E (K + 1)‖ ≤ Real.exp (((K : ℝ) + 1) * (L - εA))
      rw [heq]; exact h
    · have h := hcon j.val hj
      have heq : θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α - (((K : ℝ) - 1) / 2) * α
          = θ + ((j : ℤ) : ℝ) * α := by ring
      show ‖pd α lam (θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α
          - (((K : ℝ) - 1) / 2) * α) E (K + 1)‖ ≤ Real.exp (((K : ℝ) + 1) * (L - εA))
      rw [heq]
      exact le_trans h (Real.exp_le_exp.mpr (by linarith [hthr]))
  exact Work.TMC16Core.Basic.lemma_9_3 hQ hQdeg (by rw [Fintype.card_coe]; exact hcard)
    hAall (θ₁ + (((K : ℝ) - 1) / 2) * α) hθ₀ hδlt hgap huni

theorem nr_regular {α lam L εA ε₁ c L₁ : ℝ} {E : ℂ} {θ : ℝ} {K : ℕ}
    {I₁ I₂ : Finset ℤ} {y : ℤ}
    (hlam : 0 < lam) (hLlog : L = Real.log lam) (hL : 0 < L)
    (hε₁ : 0 < ε₁) (hδlt : ε₁ < εA) (hεA : 0 < εA)
    (hgap : 4 * ((K : ℝ) + 1) * Real.exp (L - εA) < Real.exp ((K : ℝ) * (εA - ε₁)))
    (hthr : (K : ℝ) * c ≤ ((K : ℝ) + 1) * (L - εA))
    (hcard : (I₁ ∪ I₂).card = K + 1)
    (huni : Work.TMC16Core.Uniform ε₁
      (fun j : {j : ℤ // j ∈ I₁ ∪ I₂} =>
        θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α))
    (hA : ∀ x ∈ I₁, ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
      Real.exp (((K : ℝ) + 1) * (L - εA)))
    (hgeo : ∀ x ∈ I₂, x ≤ y ∧ y ≤ x + (K : ℤ) - 1 ∧
      (K : ℤ) ≤ 40 * (y - x) ∧ (K : ℤ) ≤ 40 * ((x + (K : ℤ) - 1) - y))
    (hk40 : 40 ≤ K) (hL₁ : 0 < L₁)
    (hkey : ∀ d₁ d₂ : ℝ, 0 ≤ d₁ → 0 ≤ d₂ → d₁ + d₂ = (K : ℝ) - 1 →
      (K : ℝ) ≤ 40 * d₁ → (K : ℝ) ≤ 40 * d₂ →
        (L + ε₁) * d₂ - c * (K : ℝ) + L₁ * d₁ < 0)
    (hbd : ∀ n : ℕ, K / 40 ≤ n → n ≤ K → ∀ ζ : ℝ,
      ‖Work.TMC16Core.pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁))) :
    Work.TMC16Core.IsRegular α lam θ E L₁ K y := by
  -- A site of `I₂` where the continuant is exponentially large (strictly).
  obtain ⟨x₁, hx₁I₂, hbig⟩ :=
    site_step_gen_c_lt (α := α) (lam := lam) (L := L) (εA := εA) (ε₁ := ε₁) (c := c)
      (E := E) (θ := θ) (K := K) (I₁ := I₁) (I₂ := I₂)
      hlam hLlog hε₁ hδlt hεA hgap hthr hcard huni hA
  -- `y` lies in the window `[x₁, x₁+K-1]` at distance `≥ K/40` from both ends.
  obtain ⟨hx₁y, hyx₂, hd1, hd2⟩ := hgeo x₁ hx₁I₂
  -- The continuant at `x₁` is nonzero, hence so is the Dirichlet determinant.
  have hpd_ne : Work.TMC16Core.pd α lam (θ + (x₁ : ℝ) * α) E (K + 1) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hbig
    exact absurd hbig (not_lt.mpr (Real.exp_pos _).le)
  have hdet : (Work.TMC16Core.dirMat α lam (θ + (x₁ : ℝ) * α) E K).det ≠ 0 := by
    rw [Work.TMC16Core.Basic.dirMat_det]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) hpd_ne
  -- Cramer's bound on the two boundary entries of the Green's function.
  obtain ⟨hG1, hG2⟩ :=
    Work.TMC16Core.Basic.green_bound_reg (α := α) (lam := lam) (E := E) (θ := θ)
      (L := L) (ε₁ := ε₁) (c := c) (k := K) (x₁ := x₁) (y := y)
      hε₁ hk40 hbd hbig hd1 hd2
  -- The two distance-inequalities handed to `hkey`.
  have ha_nn : (0 : ℝ) ≤ ((y - x₁ : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ y - x₁ := by omega
    exact_mod_cast this
  have hb_nn : (0 : ℝ) ≤ (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ (x₁ + (K : ℤ) - 1) - y := by omega
    exact_mod_cast this
  have hsum : ((y - x₁ : ℤ) : ℝ) + (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) = (K : ℝ) - 1 := by
    push_cast
    ring
  have h40a : (K : ℝ) ≤ 40 * ((y - x₁ : ℤ) : ℝ) := by
    exact_mod_cast hd1
  have h40b : (K : ℝ) ≤ 40 * (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by
    exact_mod_cast hd2
  have hk1 := hkey ((y - x₁ : ℤ) : ℝ) (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ)
    ha_nn hb_nn hsum h40a h40b
  have hk2 := hkey (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) ((y - x₁ : ℤ) : ℝ)
    hb_nn ha_nn (by linarith [hsum]) h40b h40a
  refine ⟨x₁, x₁ + (K : ℤ) - 1, rfl, hx₁y, hyx₂, hd1, hd2, hdet, ?_, ?_⟩
  · -- first boundary entry: rate `(L+ε₁)·(x₂-y) - cK < -L₁·(y-x₁)`
    refine lt_trans hG1 (Real.exp_lt_exp.mpr ?_)
    rw [abs_of_nonneg ha_nn]
    linarith [hk1]
  · -- second boundary entry: rate `(L+ε₁)·(y-x₁) - cK < -L₁·(x₂-y)`
    refine lt_trans hG2 (Real.exp_lt_exp.mpr ?_)
    have habs : |((y - (x₁ + (K : ℤ) - 1) : ℤ) : ℝ)| = (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by
      have h1 : (y - (x₁ + (K : ℤ) - 1) : ℤ) = -(((x₁ + (K : ℤ) - 1) - y : ℤ)) := by ring
      rw [h1, Int.cast_neg, abs_neg, abs_of_nonneg hb_nn]
    rw [habs]
    linarith [hk2]

end Work.TMC16Core.NrFinal
