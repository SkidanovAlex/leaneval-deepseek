import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_RegExport.RXT.cone_induction
import Submission.Work.FTS_RegExport.RXT.step_integrated_fix

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.cone_max_int` — the integrated vector cone maximum principle

The requested lemma `cone_max_int` is the vector Grönwall estimate for an *integrated* linear
transport system: `n` fields `φ k` on `ℝ² × [0,T]` whose `τ`-increments are given by

`φ k s ψ τ₂ - φ k s ψ τ₁ = ∫_{τ₁}^{τ₂} (f k - (a·∂_sφ k + b·∂_ψφ k + c·φ k))`,

with bounded coefficients (`|a|,|b| ≤ A`, `|c| ≤ C`), a source obeying the *coupled* bound
`|f k| ≤ C₀·∑_j |φ j| + F`, and data bounded by `K₀` at `τ = 0`.  The conclusion is

`|φ k s ψ τ| ≤ exp (2·(C + n·C₀)·τ)·(K₀ + τ·F)`.

The first-order terms `a·∂_sφ k`, `b·∂_ψφ k` are not controlled by `|φ|`, so the pointwise
Grönwall lemma does not apply; the whole content is the *cone* maximum principle (the sup over
the backward cone `|s-s₀|,|ψ-ψ₀| ≤ A(τ₀-τ)` obeys the ODE inequality).

## Route

1. `coneStep_two` (proved here): the one-step backward inequality `ConeStep n φ T A (n·C₁+C₂) F`
   for an integrand bound `|R| ≤ C₁·∑_j|φ j| + C₂·|φ k| + F`.  This is the integrated one-step
   argument of `Work.FTS_RegExport.RXT.step_integrated_nonneg`, but with the *two* coefficients
   kept separate: the `C₁`-term is controlled by the sup `B` of `max_j |φ j|` at the new time
   (whence the factor `n`), while the `C₂`-term is controlled directly by `B` through the
   uniform continuity of `φ k` itself.  Keeping them apart is essential: folding the `c·φ k`
   term into the `∑_j|φ j|` bound would give the coefficient `n(C₀+C)`, which is strictly
   larger than `C + n·C₀` and does not suffice.
2. `cone_induction` (`Work.FTS_RegExport.RXT`, already proved): the discrete
   induction over shrinking cones, `ConeStep n φ T A C F` ⟹ `|φ| ≤ exp(2Cτ)(K₀+τF)`.
3. `cone_max_int`: instantiate with `R k := f k - c·φ k`, `C₁ := C₀`, `C₂ := C`.
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The two-coefficient integrated cone step.**  Same statement as
`Work.FTS_RegExport.RXT.step_integrated_nonneg`, except that the source bound is split as
`|R k| ≤ C₁·∑_j |φ j| + C₂·|φ k| + F`; the resulting coefficient is `n·C₁ + C₂`
(the `∑` contributes `n` times via the component count, the single component only once).

Proof: as in `step_integrated_nonneg` — the backward point `(s-Aint, ψ-Bint)` with
`Aint = ∫a`, `Bint = ∫b`, the two spatial mean value theorems at time `τ` producing the frozen
derivative terms which cancel the transport terms up to `A·η_s·h` by uniform continuity of the
spatial derivatives on the compact box, and finally the source term bounded by
`h·((n·C₁+C₂)·B + F) + ε·h` using closeness in `τ` of both `∑_j|φ j|` (`η_G`) and of `φ k`
itself (`η_φ`). -/
theorem coneStep_two {n : ℕ} {φ φs φψ R : Fin n → ℝ → ℝ → ℝ → ℝ}
    {a b : ℝ → ℝ → ℝ → ℝ} {T A C₁ C₂ F : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => φ k p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (hs : ∀ k s ψ, ∀ τ ∈ Set.Icc (0:ℝ) T, HasDerivAt (fun s' => φ k s' ψ τ) (φs k s ψ τ) s)
    (hψ : ∀ k s ψ, ∀ τ ∈ Set.Icc (0:ℝ) T, HasDerivAt (fun ψ' => φ k s ψ' τ) (φψ k s ψ τ) ψ)
    (hcs : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => φs k p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (hcψ : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => φψ k p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc 0 T))
    (hab : ∀ s ψ, ContinuousOn (fun τ => a s ψ τ) (Set.Icc 0 T) ∧
      ContinuousOn (fun τ => b s ψ τ) (Set.Icc 0 T))
    (hA : ∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) T → |a s ψ τ| ≤ A ∧ |b s ψ τ| ≤ A)
    (hRi : ∀ k s ψ, IntervalIntegrable (fun τ => R k s ψ τ) volume 0 T)
    (hRb : ∀ k s ψ τ, τ ∈ Set.Icc (0:ℝ) T →
      |R k s ψ τ| ≤ C₁ * ∑ j, |φ j s ψ τ| + C₂ * |φ k s ψ τ| + F)
    (hId : ∀ k s ψ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ T →
      φ k s ψ τ₂ - φ k s ψ τ₁
        = ∫ σ in τ₁..τ₂, (R k s ψ σ - (a s ψ σ * φs k s ψ σ + b s ψ σ * φψ k s ψ σ))) :
    Work.FTS.RegExportIface.RXT.ConeStep n φ T A (n * C₁ + C₂) F := by
  intro r ε hε
  by_cases hT : T < 0
  · refine ⟨1, one_pos, ?_⟩
    intro τ hτ h hh hhh hle
    exact absurd hτ.2 (not_lt.mpr (le_trans (le_of_lt hT) hτ.1))
  have hT0 : 0 ≤ T := not_lt.mp hT
  have hA0 : 0 ≤ A := le_trans (abs_nonneg (a 0 0 0)) (hA 0 0 0 ⟨le_refl 0, hT0⟩).1
  by_cases hr : r < 0
  · refine ⟨1, one_pos, ?_⟩
    intro τ hτ h hh hhh hle s ψ hbs hbψ
    exact absurd hbs (not_le.mpr (lt_of_lt_of_le hr (abs_nonneg s)))
  rcases n with _ | m
  · refine ⟨1, one_pos, ?_⟩
    intro τ hτ h hh hhh hle s ψ hbs hbψ
    exact ⟨s, ψ, by simpa using mul_nonneg hA0 hh.le, by simpa using mul_nonneg hA0 hh.le,
      fun M B hM hB k => Fin.elim0 k⟩
  set ρ : ℝ := r + A + 1 with hρ
  have hA1 : 0 < A + 1 := by linarith
  set Box : Set (ℝ × ℝ × ℝ) := Set.Icc (-ρ) ρ ×ˢ Set.Icc (-ρ) ρ ×ˢ Set.Icc 0 T with hBox
  have hBoxc : IsCompact Box := by
    rw [hBox]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  set ηs : ℝ := ε / (4 * (A + 1)) with hηs
  set ηG : ℝ := ε / (4 * (((m : ℝ) + 1) * C₁ + 1)) with hηG
  set ηφ : ℝ := ε / (4 * (C₂ + 1)) with hηφ
  have hηs0 : 0 < ηs := by
    rw [hηs]
    exact div_pos hε (by positivity)
  have hηG0 : 0 < ηG := by
    rw [hηG]
    refine div_pos hε ?_
    have h1 : 0 ≤ ((m : ℝ) + 1) * C₁ := mul_nonneg (by positivity) hC₁
    linarith
  have hηφ0 : 0 < ηφ := by
    rw [hηφ]
    exact div_pos hε (by linarith)
  obtain ⟨δs, hδs0, hδs⟩ := rxtStep_exists_uniform_family (f := φs) hBoxc hηs0
    (fun k => (hcs k).mono (fun p hp => ⟨trivial, trivial, hp.2.2⟩))
  obtain ⟨δψ, hδψ0, hδψ⟩ := rxtStep_exists_uniform_family (f := φψ) hBoxc hηs0
    (fun k => (hcψ k).mono (fun p hp => ⟨trivial, trivial, hp.2.2⟩))
  obtain ⟨δG, hδG0, hδG⟩ := rxtStep_exists_uniform_sum (f := φ) hBoxc hηG0
    (fun k => (hcont k).mono (fun p hp => ⟨trivial, trivial, hp.2.2⟩))
  obtain ⟨δφ, hδφ0, hδφ⟩ := rxtStep_exists_uniform_family (f := φ) hBoxc hηφ0
    (fun k => (hcont k).mono (fun p hp => ⟨trivial, trivial, hp.2.2⟩))
  refine ⟨min 1 (min (δs / (A + 1)) (min (δψ / (A + 1)) (min δG δφ))), ?_, ?_⟩
  · exact lt_min one_pos
      (lt_min (div_pos hδs0 hA1) (lt_min (div_pos hδψ0 hA1) (lt_min hδG0 hδφ0)))
  intro τ hτ h hh hhh hle s ψ hbs hbψ
  have hh1 : h ≤ 1 := le_of_lt (lt_of_lt_of_le hhh (min_le_left _ _))
  have hhδs : h < δs / (A + 1) :=
    lt_of_lt_of_le hhh (le_trans (min_le_right _ _) (min_le_left _ _))
  have hhδψ : h < δψ / (A + 1) :=
    lt_of_lt_of_le hhh
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hhδG : h < δG :=
    lt_of_lt_of_le hhh (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hhδφ : h < δφ :=
    lt_of_lt_of_le hhh (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hτmem : τ ∈ Set.Icc (0:ℝ) T := ⟨hτ.1, le_of_lt hτ.2⟩
  have hle' : τ ≤ τ + h := by linarith
  have hmem : ∀ x y σ : ℝ, |x| ≤ r + A → |y| ≤ r + A → σ ∈ Set.Icc (0:ℝ) T →
      (x, y, σ) ∈ Box := by
    intro x y σ hx hy hσ
    rw [hBox]
    have hxρ : |x| ≤ ρ := by rw [hρ]; linarith
    have hyρ : |y| ≤ ρ := by rw [hρ]; linarith
    exact ⟨⟨by linarith [neg_le_abs x], by linarith [le_abs_self x]⟩,
      ⟨by linarith [neg_le_abs y], by linarith [le_abs_self y]⟩, hσ⟩
  have hac : ContinuousOn (fun σ : ℝ => a s ψ σ) (Set.uIcc τ (τ + h)) := by
    rw [uIcc_of_le hle']
    exact (hab s ψ).1.mono (fun x hx => ⟨le_trans hτ.1 hx.1, le_trans hx.2 hle⟩)
  have hbc : ContinuousOn (fun σ : ℝ => b s ψ σ) (Set.uIcc τ (τ + h)) := by
    rw [uIcc_of_le hle']
    exact (hab s ψ).2.mono (fun x hx => ⟨le_trans hτ.1 hx.1, le_trans hx.2 hle⟩)
  have hint_a : IntervalIntegrable (fun σ : ℝ => a s ψ σ) volume τ (τ + h) := hac.intervalIntegrable
  have hint_b : IntervalIntegrable (fun σ : ℝ => b s ψ σ) volume τ (τ + h) := hbc.intervalIntegrable
  set Aint : ℝ := ∫ σ in τ..(τ + h), a s ψ σ with hAint
  set Bint : ℝ := ∫ σ in τ..(τ + h), b s ψ σ with hBint
  have hAint_abs : |Aint| ≤ A * h := by
    rw [hAint]
    calc |∫ σ in τ..(τ + h), a s ψ σ| ≤ ∫ σ in τ..(τ + h), |a s ψ σ| :=
          intervalIntegral.abs_integral_le_integral_abs hle'
      _ ≤ ∫ σ in τ..(τ + h), A := by
          refine intervalIntegral.integral_mono_on hle' hint_a.abs intervalIntegrable_const ?_
          intro x hx
          exact (hA s ψ x ⟨le_trans hτ.1 hx.1, le_trans hx.2 hle⟩).1
      _ = A * h := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hBint_abs : |Bint| ≤ A * h := by
    rw [hBint]
    calc |∫ σ in τ..(τ + h), b s ψ σ| ≤ ∫ σ in τ..(τ + h), |b s ψ σ| :=
          intervalIntegral.abs_integral_le_integral_abs hle'
      _ ≤ ∫ σ in τ..(τ + h), A := by
          refine intervalIntegral.integral_mono_on hle' hint_b.abs intervalIntegrable_const ?_
          intro x hx
          exact (hA s ψ x ⟨le_trans hτ.1 hx.1, le_trans hx.2 hle⟩).2
      _ = A * h := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hAint_leA : |Aint| ≤ A := by
    calc |Aint| ≤ A * h := hAint_abs
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hh1 hA0
      _ = A := by ring
  have hBint_leA : |Bint| ≤ A := by
    calc |Bint| ≤ A * h := hBint_abs
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left hh1 hA0
      _ = A := by ring
  refine ⟨s - Aint, ψ - Bint, ?_, ?_, ?_⟩
  · rw [show (s - Aint) - s = -Aint by ring, abs_neg]
    exact hAint_abs
  · rw [show (ψ - Bint) - ψ = -Bint by ring, abs_neg]
    exact hBint_abs
  intro M B hM hB k
  have hφsc : ContinuousOn (fun σ : ℝ => φs k s ψ σ) (Set.uIcc τ (τ + h)) := by
    rw [uIcc_of_le hle']
    have h1 : ContinuousOn (fun σ : ℝ => ((s, ψ, σ) : ℝ × ℝ × ℝ)) (Set.Icc τ (τ + h)) :=
      (continuousOn_const (c := s)).prodMk
        ((continuousOn_const (c := ψ)).prodMk continuousOn_id)
    have h2 := (hcs k).comp h1 (fun σ hσ =>
      ⟨trivial, trivial, ⟨le_trans hτ.1 hσ.1, le_trans hσ.2 hle⟩⟩)
    exact h2
  have hφψc : ContinuousOn (fun σ : ℝ => φψ k s ψ σ) (Set.uIcc τ (τ + h)) := by
    rw [uIcc_of_le hle']
    have h1 : ContinuousOn (fun σ : ℝ => ((s, ψ, σ) : ℝ × ℝ × ℝ)) (Set.Icc τ (τ + h)) :=
      (continuousOn_const (c := s)).prodMk
        ((continuousOn_const (c := ψ)).prodMk continuousOn_id)
    have h2 := (hcψ k).comp h1 (fun σ hσ =>
      ⟨trivial, trivial, ⟨le_trans hτ.1 hσ.1, le_trans hσ.2 hle⟩⟩)
    exact h2
  set Ia : ℝ := ∫ σ in τ..(τ + h), a s ψ σ * φs k s ψ σ with hIa
  set Ib : ℝ := ∫ σ in τ..(τ + h), b s ψ σ * φψ k s ψ σ with hIb
  set IR : ℝ := ∫ σ in τ..(τ + h), R k s ψ σ with hIR
  obtain ⟨sstar, hsstar, hEq1⟩ := rxtStep_exists_slope_point (g := fun x => φ k x ψ τ)
    (g' := fun x => φs k x ψ τ) (fun x => hs k x ψ τ hτmem) s (s - Aint)
  obtain ⟨ψstar, hψstar, hEq2⟩ := rxtStep_exists_slope_point (g := fun y => φ k (s - Aint) y τ)
    (g' := fun y => φψ k (s - Aint) y τ) (fun y => hψ k (s - Aint) y τ hτmem) ψ (ψ - Bint)
  have hsA_bd : |s - Aint| ≤ r + A := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [le_abs_self s, neg_le_abs Aint, hbs, hAint_leA],
      by linarith [neg_le_abs s, le_abs_self Aint, hbs, hAint_leA]⟩
  have hψB_bd : |ψ - Bint| ≤ r + A := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [le_abs_self ψ, neg_le_abs Bint, hbψ, hBint_leA],
      by linarith [neg_le_abs ψ, le_abs_self Bint, hbψ, hBint_leA]⟩
  have hsstar_bd : |sstar| ≤ r + A :=
    rxtStep_abs_min_max_le hsstar (le_trans hbs (by linarith)) hsA_bd
  have hψstar_bd : |ψstar| ≤ r + A :=
    rxtStep_abs_min_max_le hψstar (le_trans hbψ (by linarith)) hψB_bd
  have hD1 : |Aint * φs k sstar ψ τ - Ia| ≤ A * ηs * h := by
    rw [hAint, hIa]
    have hcorr := rxtStep_correction_le (a := fun σ => a s ψ σ) (F := fun σ => φs k s ψ σ)
      (c := φs k sstar ψ τ) (l := τ) (u := τ + h) (A := A) (η := ηs) hle' hac hφsc
      (fun x hx => (hA s ψ x ⟨le_trans hτ.1 hx.1, le_trans hx.2 hle⟩).1)
      (fun x hx => le_of_lt (hδs (sstar, ψ, τ)
        (hmem sstar ψ τ hsstar_bd (le_trans hbψ (by linarith)) hτmem)
        (s, ψ, x) (hmem s ψ x (le_trans hbs (by linarith)) (le_trans hbψ (by linarith))
          ⟨le_trans hτ.1 hx.1, le_trans hx.2 hle⟩)
        (by
          have h1 : |sstar - s| ≤ (A + 1) * h := by
            have h3 := rxtStep_abs_sub_le_abs_of_mem_Icc hsstar
              (show s ∈ Set.Icc (min s (s - Aint)) (max s (s - Aint)) from
                ⟨min_le_left _ _, le_max_left _ _⟩)
            rw [max_sub_min_eq_abs, abs_abs, show (s - Aint) - s = -Aint by ring, abs_neg] at h3
            have h4 : |Aint| ≤ (A + 1) * h := rxtStep_abs_le_succ_mul hAint_abs hA0 hh.le
            linarith [h3, h4]
          have h2 : |ψ - ψ| ≤ (A + 1) * h := by
            rw [sub_self, abs_zero]
            exact mul_nonneg (by linarith) hh.le
          have h5 : |τ - x| ≤ (A + 1) * h := by
            have hx1 : |τ - x| ≤ h := by
              rw [abs_sub_le_iff]
              exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
            linarith [hx1, rxtStep_le_succ_mul hA0 hh.le]
          refine lt_of_le_of_lt (rxtStep_dist_three_le h1 h2 h5) ?_
          rw [lt_div_iff₀ hA1] at hhδs
          linarith)
        k))
      hA0 hηs0.le
    simpa only [add_sub_cancel_left] using hcorr
  have hD2 : |Bint * φψ k (s - Aint) ψstar τ - Ib| ≤ A * ηs * h := by
    rw [hBint, hIb]
    have hcorr := rxtStep_correction_le (a := fun σ => b s ψ σ) (F := fun σ => φψ k s ψ σ)
      (c := φψ k (s - Aint) ψstar τ) (l := τ) (u := τ + h) (A := A) (η := ηs) hle' hbc hφψc
      (fun x hx => (hA s ψ x ⟨le_trans hτ.1 hx.1, le_trans hx.2 hle⟩).2)
      (fun x hx => le_of_lt (hδψ (s - Aint, ψstar, τ)
        (hmem (s - Aint) ψstar τ hsA_bd hψstar_bd hτmem)
        (s, ψ, x) (hmem s ψ x (le_trans hbs (by linarith)) (le_trans hbψ (by linarith))
          ⟨le_trans hτ.1 hx.1, le_trans hx.2 hle⟩)
        (by
          have h1 : |(s - Aint) - s| ≤ (A + 1) * h := by
            rw [show (s - Aint) - s = -Aint by ring, abs_neg]
            linarith [hAint_abs, hA0, hh.le]
          have h2 : |ψstar - ψ| ≤ (A + 1) * h := by
            have h3 := rxtStep_abs_sub_le_abs_of_mem_Icc hψstar
              (show ψ ∈ Set.Icc (min ψ (ψ - Bint)) (max ψ (ψ - Bint)) from
                ⟨min_le_left _ _, le_max_left _ _⟩)
            rw [max_sub_min_eq_abs, abs_abs, show (ψ - Bint) - ψ = -Bint by ring, abs_neg] at h3
            have h4 : |Bint| ≤ (A + 1) * h := rxtStep_abs_le_succ_mul hBint_abs hA0 hh.le
            linarith [h3, h4]
          have h5 : |τ - x| ≤ (A + 1) * h := by
            have hx1 : |τ - x| ≤ h := by
              rw [abs_sub_le_iff]
              exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
            linarith [hx1, rxtStep_le_succ_mul hA0 hh.le]
          refine lt_of_le_of_lt (rxtStep_dist_three_le h1 h2 h5) ?_
          rw [lt_div_iff₀ hA1] at hhδψ
          linarith)
        k))
      hA0 hηs0.le
    simpa only [add_sub_cancel_left] using hcorr
  have hG_bd : ∀ x ∈ Set.Icc τ (τ + h),
      ∑ j : Fin (m + 1), |φ j s ψ x| ≤ ((m : ℝ) + 1) * B + ηG := by
    intro x hx
    have h1 : |(∑ j : Fin (m + 1), |φ j s ψ x|)
        - (∑ j : Fin (m + 1), |φ j s ψ (τ + h)|)| < ηG := by
      refine hδG (s, ψ, x)
        (hmem s ψ x (le_trans hbs (by linarith)) (le_trans hbψ (by linarith))
          ⟨le_trans hτ.1 hx.1, le_trans hx.2 hle⟩)
        (s, ψ, τ + h)
        (hmem s ψ (τ + h) (le_trans hbs (by linarith)) (le_trans hbψ (by linarith))
          ⟨by linarith [hτ.1, hh.le], hle⟩) ?_
      have hx2 : |x - (τ + h)| ≤ h := by
        rw [abs_sub_le_iff]
        exact ⟨by linarith [hx.1, hx.2, hh.le], by linarith [hx.1]⟩
      refine lt_of_le_of_lt (rxtStep_dist_three_le ?_ ?_ hx2) hhδG
      · rw [sub_self, abs_zero]; exact hh.le
      · rw [sub_self, abs_zero]; exact hh.le
    have h2 : ∑ j : Fin (m + 1), |φ j s ψ (τ + h)| ≤ ((m : ℝ) + 1) * B := by
      calc ∑ j : Fin (m + 1), |φ j s ψ (τ + h)| ≤ ∑ j : Fin (m + 1), B :=
            Finset.sum_le_sum (fun j _ => hB j)
        _ = ((m : ℝ) + 1) * B := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
    have h1' : (∑ j : Fin (m + 1), |φ j s ψ x|) - (∑ j : Fin (m + 1), |φ j s ψ (τ + h)|)
        ≤ ηG := le_trans (le_abs_self _) h1.le
    linarith [h1', h2]
  have hφ_bd : ∀ x ∈ Set.Icc τ (τ + h), |φ k s ψ x| ≤ B + ηφ := by
    intro x hx
    have h1 : |φ k s ψ x - φ k s ψ (τ + h)| < ηφ := by
      refine hδφ (s, ψ, x)
        (hmem s ψ x (le_trans hbs (by linarith)) (le_trans hbψ (by linarith))
          ⟨le_trans hτ.1 hx.1, le_trans hx.2 hle⟩)
        (s, ψ, τ + h)
        (hmem s ψ (τ + h) (le_trans hbs (by linarith)) (le_trans hbψ (by linarith))
          ⟨by linarith [hτ.1, hh.le], hle⟩) ?_ k
      have hx2 : |x - (τ + h)| ≤ h := by
        rw [abs_sub_le_iff]
        exact ⟨by linarith [hx.1, hx.2, hh.le], by linarith [hx.1]⟩
      refine lt_of_le_of_lt (rxtStep_dist_three_le ?_ ?_ hx2) hhδφ
      · rw [sub_self, abs_zero]; exact hh.le
      · rw [sub_self, abs_zero]; exact hh.le
    have h2 : |φ k s ψ (τ + h)| ≤ B := hB k
    have h3 : |φ k s ψ x| - |φ k s ψ (τ + h)| ≤ |φ k s ψ x - φ k s ψ (τ + h)| :=
      abs_sub_abs_le_abs_sub _ _
    linarith [h1.le, h2, h3]
  have hint_R : IntervalIntegrable (fun σ : ℝ => R k s ψ σ) volume τ (τ + h) := by
    refine (hRi k s ψ).mono_set ?_
    rw [uIcc_of_le hle', uIcc_of_le hT0]
    exact fun x hx => ⟨le_trans hτ.1 hx.1, le_trans hx.2 hle⟩
  have hC₁η : C₁ * ηG ≤ ε / 4 := by
    rw [hηG, ← mul_div_assoc, div_le_iff₀ (by positivity : (0:ℝ) < 4 * (((m : ℝ) + 1) * C₁ + 1))]
    have hX : C₁ ≤ ((m : ℝ) + 1) * C₁ + 1 := by
      have := mul_nonneg (by positivity : (0:ℝ) ≤ (m : ℝ)) hC₁
      linarith
    nlinarith [hε.le, mul_le_mul_of_nonneg_right hX hε.le]
  have hC₂η : C₂ * ηφ ≤ ε / 4 := by
    rw [hηφ, ← mul_div_assoc, div_le_iff₀ (by positivity : (0:ℝ) < 4 * (C₂ + 1))]
    have hX : C₂ ≤ C₂ + 1 := by linarith
    nlinarith [hε.le, mul_le_mul_of_nonneg_right hX hε.le]
  have hIR_bd : |IR| ≤ h * ((((m : ℝ) + 1) * C₁ + C₂) * B + F) + ε / 2 * h := by
    rw [hIR]
    have h2 : ∫ σ in τ..(τ + h), |R k s ψ σ|
        ≤ ∫ σ in τ..(τ + h), (C₁ * (((m : ℝ) + 1) * B + ηG) + C₂ * (B + ηφ) + F) := by
      refine intervalIntegral.integral_mono_on hle' hint_R.abs intervalIntegrable_const ?_
      intro x hx
      have hxT : x ∈ Set.Icc (0:ℝ) T := ⟨le_trans hτ.1 hx.1, le_trans hx.2 hle⟩
      have hm1 := mul_le_mul_of_nonneg_left (hG_bd x hx) hC₁
      have hm2 := mul_le_mul_of_nonneg_left (hφ_bd x hx) hC₂
      linarith [hRb k s ψ x hxT, hm1, hm2]
    have h3 : (∫ σ in τ..(τ + h), (C₁ * (((m : ℝ) + 1) * B + ηG) + C₂ * (B + ηφ) + F))
        = (C₁ * (((m : ℝ) + 1) * B + ηG) + C₂ * (B + ηφ) + F) * h := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    calc |∫ σ in τ..(τ + h), R k s ψ σ| ≤ ∫ σ in τ..(τ + h), |R k s ψ σ| :=
          intervalIntegral.abs_integral_le_integral_abs hle'
      _ ≤ ∫ σ in τ..(τ + h), (C₁ * (((m : ℝ) + 1) * B + ηG) + C₂ * (B + ηφ) + F) := h2
      _ = (C₁ * (((m : ℝ) + 1) * B + ηG) + C₂ * (B + ηφ) + F) * h := h3
      _ ≤ h * ((((m : ℝ) + 1) * C₁ + C₂) * B + F) + ε / 2 * h := by
          have h4 : C₁ * ηG * h ≤ ε / 4 * h := mul_le_mul_of_nonneg_right hC₁η hh.le
          have h5 : C₂ * ηφ * h ≤ ε / 4 * h := mul_le_mul_of_nonneg_right hC₂η hh.le
          have e : (C₁ * (((m : ℝ) + 1) * B + ηG) + C₂ * (B + ηφ) + F) * h
              = C₁ * (((m : ℝ) + 1) * B) * h + C₁ * ηG * h + C₂ * B * h + C₂ * ηφ * h
                + F * h := by ring
          have e2 : h * ((((m : ℝ) + 1) * C₁ + C₂) * B + F)
              = C₁ * (((m : ℝ) + 1) * B) * h + C₂ * B * h + F * h := by ring
          rw [e, e2]
          linarith [h4, h5]
  have hid1 : φ k s ψ τ - φ k (s - Aint) ψ τ = Aint * φs k sstar ψ τ := by
    have h := hEq1
    rw [show s - Aint - s = -Aint by ring] at h
    linarith
  have hid2 : φ k (s - Aint) ψ τ - φ k (s - Aint) (ψ - Bint) τ
      = Bint * φψ k (s - Aint) ψstar τ := by
    have h := hEq2
    rw [show ψ - Bint - ψ = -Bint by ring] at h
    linarith
  have hint_aφ : IntervalIntegrable (fun σ : ℝ => a s ψ σ * φs k s ψ σ) volume τ (τ + h) :=
    (hac.mul hφsc).intervalIntegrable
  have hint_bφ : IntervalIntegrable (fun σ : ℝ => b s ψ σ * φψ k s ψ σ) volume τ (τ + h) :=
    (hbc.mul hφψc).intervalIntegrable
  have hidR0 := hId k s ψ τ (τ + h) hτ.1 (by linarith) hle
  have hsplit : (∫ σ in τ..(τ + h),
      (R k s ψ σ - (a s ψ σ * φs k s ψ σ + b s ψ σ * φψ k s ψ σ))) = IR - Ia - Ib := by
    rw [hIR, hIa, hIb]
    rw [intervalIntegral.integral_sub hint_R (hint_aφ.add hint_bφ)]
    rw [intervalIntegral.integral_add hint_aφ hint_bφ]
    ring
  have hmain : φ k s ψ (τ + h) = φ k (s - Aint) (ψ - Bint) τ + (Aint * φs k sstar ψ τ - Ia)
      + (Bint * φψ k (s - Aint) ψstar τ - Ib) + IR := by
    have hR := hidR0
    rw [hsplit] at hR
    linarith [hid1, hid2, hR]
  rw [hmain]
  have h4 := rxtStep_abs_add4_le (φ k (s - Aint) (ψ - Bint) τ) (Aint * φs k sstar ψ τ - Ia)
    (Bint * φψ k (s - Aint) ψstar τ - Ib) IR
  have hb1 : |φ k (s - Aint) (ψ - Bint) τ| ≤ M := hM k
  have hAη : A * ηs ≤ ε / 4 := by
    rw [hηs, ← mul_div_assoc, div_le_iff₀ (by positivity : (0:ℝ) < 4 * (A + 1))]
    nlinarith [hε.le, hA0]
  have e1 : A * ηs * h ≤ ε / 4 * h := mul_le_mul_of_nonneg_right hAη hh.le
  have hcast : ((↑(m + 1) : ℝ) * C₁ + C₂) * B = (((m : ℝ) + 1) * C₁ + C₂) * B := by
    push_cast
    ring
  rw [hcast]
  have hsum : |φ k (s - Aint) (ψ - Bint) τ| + |Aint * φs k sstar ψ τ - Ia|
      + |Bint * φψ k (s - Aint) ψstar τ - Ib| + |IR|
      ≤ M + ε * h + h * ((((m : ℝ) + 1) * C₁ + C₂) * B + F) := by
    nlinarith [hb1, hD1, hD2, hIR_bd, e1, hε.le, hh.le,
      abs_nonneg (φ k (s - Aint) (ψ - Bint) τ), abs_nonneg (Aint * φs k sstar ψ τ - Ia),
      abs_nonneg (Bint * φψ k (s - Aint) ψstar τ - Ib), abs_nonneg IR]
  linarith [h4, hsum]

/-- **The requested lemma.**  The integrated vector cone maximum principle: the `n` coupled
fields obey the Grönwall bound `exp (2·(C + n·C₀)·τ)·(K₀ + τ·F)`. -/
theorem cone_max_int {n : ℕ} {φ φs φψ f : Fin n → ℝ → ℝ → ℝ → ℝ}
    {a b c : ℝ → ℝ → ℝ → ℝ} {T A C C₀ F K₀ : ℝ}
    (hT : 0 < T) (hA : 0 ≤ A) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hF : 0 ≤ F) (hK₀ : 0 ≤ K₀)
    (hφcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => φ k p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) T))
    (hφscont : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => φs k p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) T))
    (hφψcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => φψ k p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) T))
    (hs : ∀ k s ψ τ, τ ∈ Set.Icc (0:ℝ) T →
      HasDerivAt (fun s' => φ k s' ψ τ) (φs k s ψ τ) s)
    (hψ : ∀ k s ψ τ, τ ∈ Set.Icc (0:ℝ) T →
      HasDerivAt (fun ψ' => φ k s ψ' τ) (φψ k s ψ τ) ψ)
    (hab : ∀ s ψ, ContinuousOn (fun τ => a s ψ τ) (Set.Icc (0:ℝ) T) ∧
      ContinuousOn (fun τ => b s ψ τ) (Set.Icc (0:ℝ) T) ∧
      ContinuousOn (fun τ => c s ψ τ) (Set.Icc (0:ℝ) T))
    (ha : ∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) T → |a s ψ τ| ≤ A)
    (hb : ∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) T → |b s ψ τ| ≤ A)
    (hc : ∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) T → |c s ψ τ| ≤ C)
    (hf : ∀ k s ψ τ, τ ∈ Set.Icc (0:ℝ) T → |f k s ψ τ| ≤ C₀ * ∑ j, |φ j s ψ τ| + F)
    (hfi : ∀ k s ψ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ T →
      IntervalIntegrable (fun σ => f k s ψ σ) MeasureTheory.volume τ₁ τ₂)
    (hId : ∀ k s ψ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ T →
      φ k s ψ τ₂ - φ k s ψ τ₁
        = ∫ σ in τ₁..τ₂, (f k s ψ σ - (a s ψ σ * φs k s ψ σ + b s ψ σ * φψ k s ψ σ
            + c s ψ σ * φ k s ψ σ)))
    (h0 : ∀ k s ψ, |φ k s ψ 0| ≤ K₀) :
    ∀ k s ψ τ, τ ∈ Set.Icc (0:ℝ) T →
      |φ k s ψ τ| ≤ Real.exp (2 * (C + n * C₀) * τ) * (K₀ + τ * F) := by
  -- the source of the two-coefficient cone step
  set R : Fin n → ℝ → ℝ → ℝ → ℝ := fun k s ψ σ => f k s ψ σ - c s ψ σ * φ k s ψ σ with hR
  -- continuity in `τ` of each component
  have hcont : ∀ k s ψ, ContinuousOn (fun τ => φ k s ψ τ) (Set.Icc (0:ℝ) T) := by
    intro k s ψ
    have h1 : ContinuousOn (fun σ : ℝ => ((s, ψ, σ) : ℝ × ℝ × ℝ)) (Set.Icc (0:ℝ) T) :=
      (continuousOn_const (c := s)).prodMk ((continuousOn_const (c := ψ)).prodMk continuousOn_id)
    exact (hφcont k).comp h1 (fun σ hσ => ⟨trivial, trivial, hσ⟩)
  -- continuity in `τ` of `c·φ k`
  have hcφcont : ∀ k s ψ, ContinuousOn (fun τ => c s ψ τ * φ k s ψ τ) (Set.Icc (0:ℝ) T) := by
    intro k s ψ
    have h1 : ContinuousOn (fun σ : ℝ => ((s, ψ, σ) : ℝ × ℝ × ℝ)) (Set.Icc (0:ℝ) T) :=
      (continuousOn_const (c := s)).prodMk ((continuousOn_const (c := ψ)).prodMk continuousOn_id)
    exact ((hab s ψ).2.2).mul ((hφcont k).comp h1 (fun σ hσ => ⟨trivial, trivial, hσ⟩))
  -- interval integrability of the modified source
  have hRi : ∀ k s ψ, IntervalIntegrable (fun τ => R k s ψ τ) volume 0 T := by
    intro k s ψ
    have h1 : IntervalIntegrable (fun τ => c s ψ τ * φ k s ψ τ) volume 0 T := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hT.le]
      exact hcφcont k s ψ
    have h2 : IntervalIntegrable (fun τ => f k s ψ τ) volume 0 T :=
      hfi k s ψ 0 T le_rfl hT.le le_rfl
    have h3 : IntervalIntegrable (fun τ => f k s ψ τ - c s ψ τ * φ k s ψ τ) volume 0 T :=
      h2.sub h1
    simpa only [hR] using h3
  -- the two-coefficient source bound
  have hRb : ∀ k s ψ τ, τ ∈ Set.Icc (0:ℝ) T →
      |R k s ψ τ| ≤ C₀ * ∑ j, |φ j s ψ τ| + C * |φ k s ψ τ| + F := by
    intro k s ψ τ hτ
    have h1 : |f k s ψ τ| ≤ C₀ * ∑ j, |φ j s ψ τ| + F := hf k s ψ τ hτ
    have h2 : |c s ψ τ * φ k s ψ τ| ≤ C * |φ k s ψ τ| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hc s ψ τ hτ) (abs_nonneg _)
    have h3 : |R k s ψ τ| ≤ |f k s ψ τ| + |c s ψ τ * φ k s ψ τ| := by
      have h4 := abs_sub_le (f k s ψ τ) 0 (c s ψ τ * φ k s ψ τ)
      simp only [sub_zero, zero_sub, abs_neg] at h4
      linarith
    linarith
  -- the integrated identity for the modified source
  have hIdR : ∀ k s ψ τ₁ τ₂, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ T →
      φ k s ψ τ₂ - φ k s ψ τ₁
        = ∫ σ in τ₁..τ₂, (R k s ψ σ - (a s ψ σ * φs k s ψ σ + b s ψ σ * φψ k s ψ σ)) := by
    intro k s ψ τ₁ τ₂ h1 h2 h3
    have hfun : (fun σ => R k s ψ σ - (a s ψ σ * φs k s ψ σ + b s ψ σ * φψ k s ψ σ))
        = (fun σ => f k s ψ σ - (a s ψ σ * φs k s ψ σ + b s ψ σ * φψ k s ψ σ
            + c s ψ σ * φ k s ψ σ)) := by
      funext σ
      simp only [hR]
      ring
    rw [hfun]
    exact hId k s ψ τ₁ τ₂ h1 h2 h3
  have hstep : Work.FTS.RegExportIface.RXT.ConeStep n φ T A (n * C₀ + C) F :=
    coneStep_two hC₀ hC hφcont (fun k s ψ τ hτ => hs k s ψ τ hτ)
      (fun k s ψ τ hτ => hψ k s ψ τ hτ) hφscont hφψcont
      (fun s ψ => ⟨(hab s ψ).1, (hab s ψ).2.1⟩)
      (fun s ψ τ hτ => ⟨ha s ψ τ hτ, hb s ψ τ hτ⟩) hRi hRb hIdR
  have hcoef : 0 ≤ n * C₀ + C := by
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg hn hC₀, hC]
  have hmain := Work.FTS_RegExport.RXT.cone_induction hT hA hcoef hF hK₀ hcont h0 hstep
  intro k s ψ τ hτ
  have h := hmain k s ψ τ hτ
  rwa [show n * C₀ + C = C + n * C₀ by ring] at h

end Work.FTS_RegExport.RXT.Sys
