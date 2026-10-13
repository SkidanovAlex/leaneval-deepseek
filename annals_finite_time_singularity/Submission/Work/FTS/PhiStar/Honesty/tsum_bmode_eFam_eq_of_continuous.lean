/-
# `Work.FTS.PhiStar.Honesty.tsum_bmode_eFam_eq_of_continuous`

The pointwise eigen-expansion of an angular datum `ψ` under the *weak* hypotheses actually used
by the argument: `ψ` continuous on `Iθ = [0, π/2]`, orthogonal to the kernel `sin θ cos²θ` of
`L₀*`, the eigenfunctions `eFam m` growing at most like `m + 1` on `Iθ`, and the Gegenbauer
coefficients `bmode m ψ` decaying like `(m+1)^{-5/2}`.

This is the same statement as `Work.FTS.PhiStar.Series.sum_bmode_eFam_eq`, with the hypothesis
`AngModel α ψ` replaced by the two ingredients of it that the proof actually consumes:
`ContinuousOn ψ Iθ` and the moment condition `∫_Iθ ψ · sinCos2 = 0`.  (The `AngModel` fields
`smooth`, `bdry0`, `bdry1`, `eq` are never used, and neither is `hα`.)

**Route** (verbatim the route of `sum_bmode_eFam_eq`).

* `hsup` and `hdec` give `|bmode m ψ · eFam m θ| ≤ C (m+1)^{-3/2}` on `Iθ`
  (`abs_bmode_mul_eFam_le`); the `m = 0` term vanishes because the moment condition forces
  `bmode 0 ψ = 0` (`bmode_zero_of_moment`).  Hence the series is summable at every `θ ∈ Iθ`
  (`summable_bmode_eFam`) and, by the Weierstrass M-test, its sum `F` is continuous on `Iθ`
  (`continuousOn_tsum_bmode_eFam`).
* The `e_n`-coefficient of `ψ` in the weight `cos θ dθ` is `bmode n ψ · ⟨e_n, e_n⟩`
  (`Series.bmode_mul_norm`), and the same holds for `F` by termwise integration against `e_n`
  (`integral_series_mul_eFam`).  So `ψ - F` is orthogonal to every eigenfunction.
* Completeness of the Dirichlet family (`eFam_complete`) gives `ψ - F = 0` a.e. on `Iθ`; continuity
  of `ψ - F` on the open interval upgrades this to pointwise equality there
  (`Measure.eqOn_open_of_ae_eq`).

All constants are existential; nothing depends on `α` beyond the hypotheses.
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.PhiStar.Series.sum_bmode_eFam_eq
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## The `m = 0` coefficient vanishes from the moment condition -/

/-- Under the moment condition `∫_Iθ ψ · sinCos2 = 0` the `0`-th Gegenbauer coefficient of `ψ`
vanishes (`eFam 0 · cos = 3 sinCos2`). -/
lemma bmode_zero_of_moment (ψ : ℝ → ℝ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    Work.FTS.PhiStar.Series.bmode 0 ψ = 0 := by
  have hF : Work.Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
    simpa only [Work.Elliptic.Fstar] using hmom
  rw [Work.FTS.PhiStar.Series.bmode_eq_cmode 0 ψ 0]
  exact Work.FTS.PhiStar.Series.eFam_zero_moment (fun _ θ => ψ θ) hF

/-! ## The pointwise bound behind summability, continuity and integration -/

/-- `|bmode m ψ · eFam m θ| ≤ Cd·Cg·(m+1)^{-3/2}` on `Iθ`, from the growth bound on `eFam` and
the decay bound on `bmode` (and the vanishing of the `m = 0` term). -/
lemma abs_bmode_mul_eFam_le (ψ : ℝ → ℝ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    {Cg Cd : ℝ} (hCg : 0 < Cg) (hCd : 0 < Cd)
    (hsup : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * ((m : ℝ) + 1))
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [bmode_zero_of_moment ψ hmom, zero_mul, abs_zero]
    exact le_of_lt (mul_pos (mul_pos hCd hCg) (Real.rpow_pos_of_pos (by norm_num) _))
  · rw [abs_mul]
    have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    calc |Work.FTS.PhiStar.Series.bmode m ψ| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ (Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) * (Cg * ((m : ℝ) + 1)) :=
          mul_le_mul (hdec m hm) (hsup m θ hθ) (abs_nonneg _)
            (le_of_lt (mul_pos hCd (Real.rpow_pos_of_pos hmpos _)))
      _ = Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
          have hp : ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1)
              = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
            calc ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1)
                = ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1) ^ (1 : ℝ) := by
                  rw [Real.rpow_one]
              _ = ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ) + 1) := (Real.rpow_add hmpos _ _).symm
              _ = ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by norm_num
          rw [← hp]
          ring

/-! ## The three series lemmas -/

/-- The mode series is summable at every point of `Iθ`. -/
lemma summable_bmode_eFam (ψ : ℝ → ℝ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) :
    ∀ θ ∈ Work.Spaces.Iθ, Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ *
      Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  obtain ⟨Cg, hCg, hsup⟩ := hsup
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  intro θ hθ
  refine Summable.of_norm_bounded
    ((Work.FTS.PhiStar.Series.summable_one_add_rpow (3 / 2) (by norm_num)).mul_left
      (Cd * Cg)) (fun m => ?_)
  rw [Real.norm_eq_abs]
  exact abs_bmode_mul_eFam_le ψ hmom hCg hCd hsup hdec m hθ

/-- The sum of the mode series is continuous on `Iθ` (Weierstrass M-test). -/
lemma continuousOn_tsum_bmode_eFam (ψ : ℝ → ℝ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (hsum : ∀ θ ∈ Work.Spaces.Iθ, Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ *
      Work.FTS.PhiStar.Gegenbauer.eFam m θ)) :
    ContinuousOn (fun θ : ℝ => ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
      Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ := by
  obtain ⟨Cg, hCg, hsup⟩ := hsup
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  refine continuousOn_tsum
    (fun m => (continuous_const.mul (Work.FTS.PhiStar.Series.continuous_eFam m)).continuousOn)
    ((Work.FTS.PhiStar.Series.summable_one_add_rpow (3 / 2) (by norm_num)).mul_left
      (Cd * Cg)) (fun m θ hθ => ?_)
  rw [Real.norm_eq_abs]
  exact abs_bmode_mul_eFam_le ψ hmom hCg hCd hsup hdec m hθ

/-- The `e_n`-coefficient of the sum of the mode series, computed by dominated convergence. -/
lemma integral_series_mul_eFam (ψ : ℝ → ℝ) (n : ℕ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (hsum : ∀ θ ∈ Work.Spaces.Iθ, Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ *
      Work.FTS.PhiStar.Gegenbauer.eFam m θ)) :
    (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.FTS.PhiStar.Gegenbauer.eFam n θ
        * Real.cos θ)
      = Work.FTS.PhiStar.Series.bmode n ψ *
        (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
  obtain ⟨Cg, hCg, hsup⟩ := hsup
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  have hB : 0 ≤ Cg * ((n : ℝ) + 1) :=
    le_of_lt (mul_pos hCg (by positivity))
  have hmain : HasSum (fun m : ℕ => ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) := by
    refine hasSum_integral_of_dominated_convergence
      (μ := volume.restrict Work.Spaces.Iθ)
      (F := fun m θ => (Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (f := fun θ => (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (fun m _ => (Cd * Cg * (Cg * ((n : ℝ) + 1))) * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)))
      ?_ ?_ ?_ ?_ ?_
    · intro m
      exact ((continuous_const.mul (Work.FTS.PhiStar.Series.continuous_eFam m)).mul
        ((Work.FTS.PhiStar.Series.continuous_eFam n).mul Real.continuous_cos)).aestronglyMeasurable
    · intro m
      simp only [Work.Spaces.Iθ]
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_bmode_mul_eFam_le ψ hmom hCg hCd hsup hdec m ha
      have h2 : |Work.FTS.PhiStar.Gegenbauer.eFam n a * Real.cos a|
          ≤ Cg * ((n : ℝ) + 1) := by
        rw [abs_mul]
        calc |Work.FTS.PhiStar.Gegenbauer.eFam n a| * |Real.cos a|
            ≤ (Cg * ((n : ℝ) + 1)) * 1 :=
              mul_le_mul (hsup n a ha) (Real.abs_cos_le_one a) (abs_nonneg _) hB
          _ = Cg * ((n : ℝ) + 1) := by ring
      have h3 : (0 : ℝ) ≤ Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) :=
        le_of_lt (mul_pos (mul_pos hCd hCg) (Real.rpow_pos_of_pos (by positivity) _))
      calc |Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m a|
            * |Work.FTS.PhiStar.Gegenbauer.eFam n a * Real.cos a|
          ≤ (Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) * (Cg * ((n : ℝ) + 1)) :=
            mul_le_mul h1 h2 (abs_nonneg _) h3
        _ = (Cd * Cg * (Cg * ((n : ℝ) + 1))) * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by ring
    · exact Filter.Eventually.of_forall
        (fun _ => (Work.FTS.PhiStar.Series.summable_one_add_rpow (3 / 2)
          (by norm_num)).mul_left _)
    · exact integrable_const _
    · simp only [Work.Spaces.Iθ]
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      exact ((hsum a ha).hasSum).mul_right _
  -- identify the two sides
  set G : ℕ → ℝ := fun m => ∫ θ in Work.Spaces.Iθ,
    Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.FTS.PhiStar.Gegenbauer.eFam n θ
      * Real.cos θ with hG
  have hterm : ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      = Work.FTS.PhiStar.Series.bmode m ψ * G m := by
    intro m
    have h1 : (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Series.bmode m ψ
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [h1, integral_const_mul, hG]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  have hGzero : ∀ m : ℕ, m ≠ n → G m = 0 := by
    intro m hmn
    show (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
      * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) = 0
    rw [Work.FTS.PhiStar.Series.iota_eq_interval]
    exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn
  have hGn : G n = ∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ := by
    rw [hG]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  calc (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    _ = ∑' m : ℕ, ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := hmain.tsum_eq.symm
    _ = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * G m := tsum_congr hterm
    _ = Work.FTS.PhiStar.Series.bmode n ψ * G n :=
        tsum_eq_single n (fun m hm => by rw [hGzero m hm, mul_zero])
    _ = Work.FTS.PhiStar.Series.bmode n ψ *
        (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
        rw [hGn]

/-! ## The assembly -/

theorem tsum_bmode_eFam_eq_of_continuous (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α)
    (hcont : ContinuousOn ψ Work.Spaces.Iθ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    (hsup : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))) :
    ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ := by
  have hsum := summable_bmode_eFam ψ hmom hsup hdec
  have hcontF := continuousOn_tsum_bmode_eFam ψ hmom hsup hdec hsum
  set F : ℝ → ℝ := fun θ =>
    ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
    with hFdef
  have hFcont : ContinuousOn F Work.Spaces.Iθ := hcontF
  have hcontSub : ContinuousOn (fun θ : ℝ => ψ θ - F θ) Work.Spaces.Iθ :=
    hcont.sub hFcont
  -- the `e_n`-coefficients of `ψ` and of the series
  have hψcoef : ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, ψ θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = Work.FTS.PhiStar.Series.bmode n ψ * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
    intro n
    rw [← Work.FTS.PhiStar.Series.bmode_mul_norm n ψ]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  have hFcoef : ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, F θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = Work.FTS.PhiStar.Series.bmode n ψ * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
    intro n
    rw [← integral_series_mul_eFam ψ n hmom hsup hdec hsum]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  -- orthogonality of the difference against every eigenfunction
  have horth : ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, (ψ θ - F θ) * Work.FTS.PhiStar.Gegenbauer.eFam n θ
        * Real.cos θ) = 0 := by
    intro n
    have hψint : IntegrableOn
        (fun θ : ℝ => ψ θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hcont.mul ((Work.FTS.PhiStar.Series.continuous_eFam n).continuousOn.mul
          Real.continuous_cos.continuousOn))
    have hFint : IntegrableOn
        (fun θ : ℝ => F θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hFcont.mul ((Work.FTS.PhiStar.Series.continuous_eFam n).continuousOn.mul
          Real.continuous_cos.continuousOn))
    have hcongr : (∫ θ in Work.Spaces.Iθ, (ψ θ - F θ)
          * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ,
            (ψ θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
              - F θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [hcongr, integral_sub hψint hFint, hψcoef n, hFcoef n, sub_self]
  -- measurability and integrability of the difference
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => ψ θ - F θ)
      (volume.restrict Work.Spaces.Iθ) :=
    hcontSub.aestronglyMeasurable measurableSet_Icc
  have hint : IntegrableOn (fun θ : ℝ => (ψ θ - F θ) ^ 2 * Real.cos θ)
      Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hcontSub.pow 2).mul Real.continuous_cos.continuousOn)
  have hae : (fun θ : ℝ => ψ θ - F θ) =ᵐ[volume.restrict Work.Spaces.Iθ] 0 :=
    Work.FTS.PhiStar.Gegenbauer.eFam_complete (fun θ : ℝ => ψ θ - F θ) hmeas hint horth
  -- transfer to the open interval and use continuity
  have hsub : Set.Ioo (0 : ℝ) (π / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hae' : (fun θ : ℝ => ψ θ - F θ) =ᵐ[volume.restrict (Set.Ioo 0 (π / 2))] 0 :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have heq : EqOn (fun θ : ℝ => ψ θ - F θ) 0 (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.eqOn_open_of_ae_eq (μ := volume) hae' isOpen_Ioo
      (hcontSub.mono (by intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
      continuousOn_const
  intro θ hθ hθ2
  have h0 : ψ θ - F θ = 0 := heq ⟨hθ, hθ2⟩
  have : F θ = ψ θ := by linarith
  exact this

end Work.FTS.PhiStar.Honesty
