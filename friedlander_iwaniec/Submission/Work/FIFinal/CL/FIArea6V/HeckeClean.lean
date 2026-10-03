/-
# `Submission.Work.FIArea6V.HeckeClean` — a self-contained clean route to (16.23)/(16.24)

The frozen chain of `Submission/Work/FIArea6Hecke/` reaches the Hecke inverse bound
(16.23)/(16.24) through one `sorry`:

  `heckeLcontInvBound_all` ← `heckeInvBound_all` ← `heckeLSeries_zero_of_re_le_one`
    ← `heckeLam_prime_divergence` ← `heckeLam_sq_prime_recip_divergence` (`:= by sorry`).

That hole is closed inside this lane by `Work.FIArea6V.heckeLam_sq_prime_recip_divergence`
(the Rankin–Selberg second moment along the split primes).  This module threads it through the
same chain, using the *parameterised* steps of the frozen files where they exist
(`heckeLSeries_eq_zero_of_prime_divergence` and `heckeInvBound_all_of` are stated with the
divergence/vanishings as hypotheses, so they can be reused verbatim) and copying only the two
steps whose proofs hard-code the missing lemma:

* `heckeLam_prime_divergence` — the elementary reduction from the degree-`2` divergence to the
  degree-`1` divergence `Σ_{p ≡ 1(4)} ‖λ p‖/p = ∞`;
* `heckeLcontInvBound_re_gt_one` — the identity-theorem half of (16.23) on `re s > 1`.

Every declaration here is proved from `Work.FIArea6V.heckeLam_sq_prime_recip_divergence`, the
`re s > 1` input `R.heckeLSeries_inv_bound_re_gt_one` and the *clean* half
`heckeLcontInvBound_strip`; the resulting `heckeLcontInvBound_all_clean` is the hypothesis the
area-6V contract is assembled from.
-/
import Mathlib
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea6Hecke.heckeLam_prime_divergence
import Submission.Work.FIArea6Hecke.heckeLSeries_zero_of_re_le_one
import Submission.Work.FIFinal.CL.FIArea6Hecke.heckeInvBound_all
import Submission.Work.FIFinal.CL.FIArea6Hecke.heckeLcontInvBound_all
import Submission.Work.FIFinal.CL.FIArea6Hecke.heckeLcontInvBound_strip
import Submission.Work.FIFinal.CL.FIArea6V.heckeLam_sq_prime_recip_divergence

set_option autoImplicit false

namespace Work.FIArea6V

open Finset
open scoped BigOperators
open Work.FIPlan
open Work.FIArea5.S16Hecke

noncomputable section

/-! ## 1. The degree-`1` divergence along the split primes -/

/-- The elementary reduction `Σ ‖λ p‖²/p = ∞ ⇒ Σ ‖λ p‖/p = ∞` of
`Work.FIArea6Hecke.heckeLam_prime_divergence`, run on the divergence lemma of *this* lane. -/
theorem heckeLam_prime_divergence {d : ℕ} (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : IsCharMod4dStrict d chi) (m : ℤ) :
    ¬ Summable (fun n : ℕ =>
      if n.Prime ∧ n % 4 = 1 then ‖heckeLam chi m n‖ / (n : ℝ) else 0) := by
  intro hsumm
  set f1 : ℕ → ℝ :=
    fun n => if n.Prime ∧ n % 4 = 1 then ‖heckeLam chi m n‖ / (n : ℝ) else 0 with hf1
  set f2 : ℕ → ℝ :=
    fun n => if n.Prime ∧ n % 4 = 1 then ‖heckeLam chi m n‖ ^ 2 / (n : ℝ) else 0 with hf2
  have hsumm1 : Summable f1 := hsumm
  have hle : ∀ n : ℕ, f2 n ≤ 2 * f1 n := by
    intro n
    by_cases hn : n.Prime ∧ n % 4 = 1
    · have hb := Work.FIArea6Hecke.heckeLam_prime_norm_le_two hchi m hn.1 hn.2
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1.pos
      have hnn : (0 : ℝ) ≤ ‖heckeLam chi m n‖ := norm_nonneg _
      have key : ‖heckeLam chi m n‖ ^ 2 ≤ 2 * ‖heckeLam chi m n‖ := by
        nlinarith [hnn, hb]
      simp only [hf1, hf2, if_pos hn]
      calc ‖heckeLam chi m n‖ ^ 2 / (n : ℝ)
          ≤ (2 * ‖heckeLam chi m n‖) / (n : ℝ) :=
            div_le_div_of_nonneg_right key (le_of_lt hn0)
        _ = 2 * (‖heckeLam chi m n‖ / (n : ℝ)) := by ring
    · simp only [hf1, hf2, if_neg hn]
      simp
  have hnonneg : ∀ n : ℕ, 0 ≤ f2 n := by
    intro n
    simp only [hf2]
    split_ifs with hn
    · exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)
    · exact le_refl 0
  have h2 : Summable f2 := Summable.of_nonneg_of_le hnonneg hle (hsumm1.mul_left 2)
  exact (heckeLam_sq_prime_recip_divergence hd chi hchi m) h2

/-- The abscissa-of-convergence half of (16.23): `L(s,ψ)` vanishes for `re s ≤ 1`, from the
degree-`1` divergence.  Same statement as `Work.FIArea6Hecke.heckeLSeries_zero_of_re_le_one`, with
the divergence discharged by this lane's lemma. -/
theorem heckeLSeries_zero_of_re_le_one : ∀ {d : ℕ}, 1 ≤ d → ∀ (chi : GaussianInt → ℂ),
    IsCharMod4dStrict d chi → ∀ (m : ℤ) {s : ℂ}, s.re ≤ 1 → heckeLSeries chi m s = 0 := by
  intro d hd chi hchi m s hs
  exact Work.FIArea6Hecke.heckeLSeries_eq_zero_of_prime_divergence chi m
    (heckeLam_prime_divergence hd chi hchi m) hs

/-! ## 2. The two halves of (16.23), then (16.24) -/

/-- `HeckeInvBoundAll ε` from the vanishing half above and the absolutely-convergent half
`R.heckeLSeries_inv_bound_re_gt_one` (the parameterised assembly being
`Work.FIArea6Hecke.heckeInvBound_all_of`). -/
theorem heckeInvBound_allV : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    Work.FITop4.Bridge.HeckeInvBoundAll ε :=
  Work.FIArea6Hecke.heckeInvBound_all_of heckeLSeries_zero_of_re_le_one
    Work.FIArea6Hecke.heckeLSeries_inv_bound_re_gt_one

/-- The `re s > 1` half of (16.23): on the half-plane of absolute convergence the completion
hypothesis determines `Lam / heckeArch` as `heckeLSeries χ m` (identity theorem), so the inverse
bound there is `HeckeInvBoundAll`.  Identical to
`Work.FIArea6Hecke.heckeLcontInvBound_re_gt_one`, with `heckeInvBound_all` replaced by
`heckeInvBound_allV`. -/
theorem heckeLcontInvBound_re_gt_one :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
          IsCharMod4dStrict d chi →
          AnalyticOn ℂ Lam Set.univ →
          (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
            Lam s = Work.FITop4.Bridge.heckeArch d m s *
              heckeLSeries chi m s) →
          ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
            ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
              ≤ C * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by
  intro ε hε0 hε1
  obtain ⟨c, hcpos, hc⟩ := heckeInvBound_allV ε hε0 hε1
  refine ⟨c, c, hcpos, hcpos, ?_⟩
  intro d chi m Lam hd hchi hAn hagree s hs1 hs2
  rw [Work.FIArea6Hecke.Lam_div_heckeArch_eq_LSeries hd chi m hchi hAn hagree hs1]
  refine hc d chi hd hchi m s ?_ hs2
  have hdpos : 0 < (d : ℝ) ^ ε :=
    Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)) ε
  have hlogpos : 0 < Real.log (|(m : ℝ)| + |s.im| + 3) :=
    Real.log_pos (by have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im; linarith)
  have hden : 0 < (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) := mul_pos hdpos hlogpos
  have : 0 < c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) := div_pos hcpos hden
  linarith

/-- **The Hecke inverse bound (16.23)/(16.24), free of `sorryAx`.**  The two halves are the
identity-theorem half above and the *clean* strip half `Work.FIArea6Hecke.heckeLcontInvBound_strip`;
the regions are nested, so `(min c₁ c₂, max C₁ C₂)` works. -/
theorem heckeLcontInvBound_all_clean :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → Work.FITop4.Bridge.HeckeLcontInvBoundAll ε := by
  intro ε hε0 hε1
  obtain ⟨c₁, C₁, hc₁, hC₁, h1⟩ := heckeLcontInvBound_re_gt_one ε hε0 hε1
  obtain ⟨c₂, C₂, hc₂, hC₂, h2⟩ := Work.FIArea6Hecke.heckeLcontInvBound_strip ε hε0 hε1
  refine ⟨min c₁ c₂, max C₁ C₂, lt_min hc₁ hc₂, lt_max_of_lt_left hC₁, ?_⟩
  intro d chi m Lam hd hchi hAn hagree s hregion hs2
  have hdpos : 0 < (d : ℝ) ^ ε :=
    Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)) ε
  have hlogpos : 0 < Real.log (|(m : ℝ)| + |s.im| + 3) :=
    Real.log_pos (by have h1 := abs_nonneg (m : ℝ); have h2 := abs_nonneg s.im; linarith)
  have hden : 0 < (d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3) := mul_pos hdpos hlogpos
  have hlog2 : 0 ≤ (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := by positivity
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  by_cases hcase : 1 < s.re
  · have hb := h1 d chi m Lam hd hchi hAn hagree s hcase hs2
    calc ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
        ≤ C₁ * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := hb
      _ ≤ max C₁ C₂ * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hd0) hlog2
  · have hcase' : s.re ≤ 1 := not_lt.mp hcase
    have hmin_le2 : min c₁ c₂ / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3))
        ≤ c₂ / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) :=
      div_le_div_of_nonneg_right (min_le_right _ _) hden.le
    have hreg2 : 1 - c₂ / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re :=
      lt_of_le_of_lt (sub_le_sub_left hmin_le2 1) hregion
    have hb := h2 d chi m Lam hd hchi hAn hagree s hreg2 hcase'
    calc ‖(Lam s / Work.FITop4.Bridge.heckeArch d m s)⁻¹‖
        ≤ C₂ * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) := hb
      _ ≤ max C₁ C₂ * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hd0) hlog2

end

end Work.FIArea6V
