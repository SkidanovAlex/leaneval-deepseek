import Mathlib
import Submission.Work.TMC16Core.Core.geom
import Submission.Work.TMC16Core.Core.ablock
import Submission.Work.TMC16Core.Core.site

/-!
# `pd_step_nr` — the non-resonant assembly step for `pd_window`

This is the *whole* assembly of the non-resonant branch of `pd_window`, with the single
uniformity input (`Uniform ε₁` on the `q m`-block-aligned windows of `Core.geom`) left as a
hypothesis.  Combining

* `Core.geom` (the windows `I1nr`, `I2nr` with their exact difference set, cardinality,
  disjointness, and the containments `I1nr ⊆ A2blk`, `I2nr ⊆ I2set`, whose arithmetic
  hypotheses are the two `hfit` inequalities),
* `Core.Ablock_of_sing_gen` (the singularity of `0` gives the `A`-bound on `I₁`), and
* `Core.site_step_gen` (AJ Lemmas 9.2 + 9.3 + the Fourier lower bound),

it produces a site `x₁ ∈ I2nr q (m+1) s b' y` satisfying the three balanced conditions and
the exponential lower bound of `pd_window`.  The scale is `K = Knr q (m+1) s = 2 s q m - 1`
and the block length is `q m`.
-/

noncomputable section

namespace Work.TMC16Core.Core

open Work.TMC16Core

theorem pd_step_nr {α lam L εA ε₁ m_sing : ℝ} {E : ℂ} {θ : ℝ} {q : ℕ → ℕ}
    {m s a' b' : ℕ} {y : ℤ}
    (hlam : 0 < lam) (hLlog : L = Real.log lam) (hL : 0 < L)
    (hε₁ : 0 < ε₁) (hδlt : ε₁ < εA) (hεA : 0 < εA)
    (hεAub : εA + ε₁ ≤ (3 / 16) * (L - m_sing))
    (hm : 0 < m_sing) (hmL : m_sing < L)
    (hK : 240 ≤ Knr q (m + 1) s)
    (hgap : 4 * (((Knr q (m + 1) s : ℕ) : ℝ) + 1) * Real.exp (L - εA)
      < Real.exp (((Knr q (m + 1) s : ℕ) : ℝ) * (εA - ε₁)))
    (hthr : ((Knr q (m + 1) s : ℕ) : ℝ) * ((23 / 32 : ℝ) * L)
      ≤ (((Knr q (m + 1) s : ℕ) : ℝ) + 1) * (L - εA))
    (hbd : ∀ n : ℕ, Knr q (m + 1) s / 40 ≤ n → n ≤ Knr q (m + 1) s → ∀ ζ : ℝ,
      ‖pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁)))
    (hs : IsSingular α lam θ E m_sing (Knr q (m + 1) s) 0)
    (hs1 : 1 ≤ s) (hqm : 1 ≤ q m)
    (hfit1 : 8 * ((a' : ℤ) * (q m : ℤ)) + 6 ≤ 5 * Tnr q (m + 1) s)
    (hfit2 : 10 * ((b' : ℤ) * (q m : ℤ)) + 37 ≤ 4 * Tnr q (m + 1) s)
    (hab : a' + b' = s) (hT : Tnr q (m + 1) s ≤ y)
    (huni : Uniform ε₁ (fun j : {j : ℤ // j ∈ I1nr q (m + 1) s a' ∪ I2nr q (m + 1) s b' y} =>
      θ + (((j : ℤ) : ℝ) + (((Knr q (m + 1) s : ℕ) : ℝ) - 1) / 2) * α)) :
    ∃ x₁ ∈ I2nr q (m + 1) s b' y,
      3 * (Knr q (m + 1) s : ℤ) ≤ 10 * (y - x₁) ∧
        10 * (y - x₁) ≤ 7 * (Knr q (m + 1) s : ℤ) ∧
        (Knr q (m + 1) s : ℤ) ≤ 40 * ((x₁ + (Knr q (m + 1) s : ℤ) - 1) - y) ∧
        Real.exp ((23 / 32 : ℝ) * L * ((Knr q (m + 1) s : ℕ) : ℝ)) ≤
          ‖pd α lam (θ + (x₁ : ℝ) * α) E ((Knr q (m + 1) s : ℕ) + 1)‖ := by
  -- the `A`-window bound on `I1nr`
  have hsub : I1nr q (m + 1) s a' ⊆ A2blk (Knr q (m + 1) s) :=
    I1nr_subset_A2blk hs1 hqm (by simpa using hfit1)
  have hAraw := Ablock_of_sing_gen (α := α) (lam := lam) (E := E) (θ := θ)
    (L := L) (ε₁ := ε₁) (m := m_sing) (K := Knr q (m + 1) s) (I₁ := I1nr q (m + 1) s a')
    hL (by positivity) hm hmL hK hbd hsub hs
  have hA : ∀ x ∈ I1nr q (m + 1) s a',
      ‖pd α lam (θ + (x : ℝ) * α) E ((Knr q (m + 1) s : ℕ) + 1)‖
        ≤ Real.exp ((((Knr q (m + 1) s : ℕ) : ℝ) + 1) * (L - εA)) := by
    intro x hx
    refine le_trans (hAraw x hx) (Real.exp_le_exp.mpr ?_)
    have hK0 : (0 : ℝ) ≤ ((Knr q (m + 1) s : ℕ) : ℝ) + 1 := by positivity
    nlinarith [hεAub, hK0]
  -- the geometry and the numerics
  have hcard : (I1nr q (m + 1) s a' ∪ I2nr q (m + 1) s b' y).card
      = Knr q (m + 1) s + 1 :=
    card_union_I1nr_I2nr hab hs1 hqm hT
  have hI2 : I2nr q (m + 1) s b' y ⊆ I2set y (Knr q (m + 1) s) :=
    I2nr_subset_I2set hab hs1 hqm (by simpa using hfit2)
  exact site_step_gen (α := α) (lam := lam) (L := L) (εA := εA) (ε₁ := ε₁) (E := E)
    (θ := θ) (K := Knr q (m + 1) s) (I₁ := I1nr q (m + 1) s a')
    (I₂ := I2nr q (m + 1) s b' y) (y := y) hlam hLlog hε₁ hδlt hεA hgap hthr hcard huni
    hA hI2

end Work.TMC16Core.Core
