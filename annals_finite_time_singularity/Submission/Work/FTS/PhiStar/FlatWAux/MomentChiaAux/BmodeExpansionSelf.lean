/-
# `Work.FTS.PhiStar.FlatWAux.MomentChiaAux.BmodeExpansionSelf` — the eigenfunction expansion of `ψ`

The Dirichlet eigenfamily `eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)` of `Work.Elliptic.Lzero`
is orthogonal for the weight `cos θ dθ` (`eFam_orthogonal`) and complete (`eFam_complete`).
This file shows that under the decay of the coefficients `bmode m ψ`, the growth of the family,
continuity and boundedness of `ψ` on the open interval and the vanishing `sin θ cos²θ`-moment,

  `Σ_m bmode m ψ · eFam m θ = ψ θ`   for `θ ∈ (0, π/2)`.

The coefficient of the series against `eFam n` is `bmode n ψ` again (termwise integration,
dominated convergence with the summable majorant `mcMajor`), and `bmode n ψ` is also the
`eFam n`-coefficient of `ψ` (`Series.bmode_mul_norm`), so the difference is orthogonal to every
eigenfunction and completeness forces it to vanish a.e.; continuity on the open interval (where
`ψ` is continuous by hypothesis and the series is continuous) upgrades this to pointwise
equality there.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Series.eFam_zero_moment
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.PhiStar.Series.sum_bmode_eFam_eq
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux.MomentChiaAux

set_option autoImplicit false

/-! ## Elementary facts -/

/-- The angular eigenfunctions are continuous. -/
lemma continuous_eFam_aux (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  change Continuous (fun θ : ℝ => Real.cos θ
    * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp Real.continuous_sin)

/-- The vanishing `sin θ cos²θ`-moment kills the kernel coefficient `bmode 0 ψ`. -/
lemma bmode_zero_aux {ψ : ℝ → ℝ}
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    Work.FTS.PhiStar.Series.bmode 0 ψ = 0 := by
  have hF : Work.Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
    simpa only [Work.Elliptic.Fstar] using hmom
  rw [Work.FTS.PhiStar.Series.bmode_eq_cmode 0 ψ 0]
  exact Work.FTS.PhiStar.Series.eFam_zero_moment (fun _ θ => ψ θ) hF

/-- `Icc 0 (π/2)` and `Ioo 0 (π/2)` carry the same restricted Lebesgue measure. -/
lemma restrict_Iθ_eq_restrict_Ioo :
    volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  refine Measure.restrict_congr_set ?_
  rw [MeasureTheory.ae_eq_set]
  constructor
  · have hsub : Work.Spaces.Iθ \ Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ {0} ∪ {Real.pi / 2} := by
      intro x hx
      simp only [Set.mem_sdiff, Work.Spaces.Iθ, Set.mem_Icc, Set.mem_Ioo, Set.mem_union,
        Set.mem_singleton_iff] at hx ⊢
      rcases eq_or_lt_of_le hx.1.1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr (le_antisymm hx.1.2 (le_of_not_gt fun hlt => hx.2 ⟨h, hlt⟩))
    have hfin : ({0} ∪ {Real.pi / 2} : Set ℝ).Finite :=
      (Set.finite_singleton (0 : ℝ)).union (Set.finite_singleton (Real.pi / 2))
    exact measure_mono_null hsub (hfin.measure_zero volume)
  · have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) \ Work.Spaces.Iθ ⊆ (∅ : Set ℝ) := by
      intro x hx
      simp only [Set.mem_sdiff, Work.Spaces.Iθ, Set.mem_Icc, Set.mem_Ioo] at hx
      exact absurd ⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩ hx.2
    exact measure_mono_null hsub measure_empty

/-! ## The majorant -/

/-- The summable majorant of the `m`-th term `bmode m ψ · eFam m θ`: for `m ≥ 1` the term is
bounded by `Cd Cg (2m+1)^{-3/2}`. -/
def mcMajor (Cd Cg : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 0 else Cd * Cg * ((2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ)))

lemma mcMajor_nonneg (Cd Cg : ℝ) (hCd : 0 < Cd) (hCg : 0 < Cg) (m : ℕ) :
    0 ≤ mcMajor Cd Cg m := by
  rw [mcMajor]
  split
  · norm_num
  · positivity

lemma mcMajor_le (Cd Cg : ℝ) (hCd : 0 ≤ Cd) (hCg : 0 ≤ Cg) (m : ℕ) :
    mcMajor Cd Cg m ≤ Cd * Cg * (((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
  rw [mcMajor]
  split
  · exact mul_nonneg (mul_nonneg hCd hCg) (Real.rpow_nonneg (by positivity) _)
  · have hbase : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hpos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
    have hle : (m : ℝ) + 1 ≤ 2 * (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have h1 : ((m : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤ (2 * (m : ℝ) + 1) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow (le_of_lt hbase) hle (by norm_num)
    have h3 : (2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ))
        ≤ ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.rpow_neg (le_of_lt hpos), Real.rpow_neg (le_of_lt hbase), inv_eq_one_div,
        inv_eq_one_div]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hbase _) h1
    exact mul_le_mul_of_nonneg_left h3 (mul_nonneg hCd hCg)

/-- `Σ_m (m+1)^{-3/2}` converges. -/
lemma summable_rpow_neg_three_halves :
    Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    (Real.summable_nat_rpow (p := (-(3 / 2 : ℝ)))).mpr (by norm_num)
  have h1 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) 1).mpr h0
  simpa only [Nat.cast_add, Nat.cast_one] using h1

lemma summable_mcMajor (Cd Cg : ℝ) (hCd : 0 < Cd) (hCg : 0 < Cg) :
    Summable (mcMajor Cd Cg) := by
  refine Summable.of_nonneg_of_le (fun m => mcMajor_nonneg Cd Cg hCd hCg m) (fun m => ?_)
    ((summable_rpow_neg_three_halves).mul_left (Cd * Cg))
  exact mcMajor_le Cd Cg (le_of_lt hCd) (le_of_lt hCg) m

/-! ## The arithmetic of the term bound -/

/-- `(2m+1)² ≤ lam m` for `m ≥ 1`. -/
lemma sq_two_mul_add_one_le_lam {m : ℕ} (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 1) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  rw [Work.FTS.PhiStar.Gegenbauer.lam]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith

lemma one_div_mul_sqrt (t : ℝ) (ht : 0 < t) : 1 / (t * Real.sqrt t) = t ^ (-(3 / 2 : ℝ)) := by
  have h1 : t ^ ((3 : ℝ) / 2) = t * Real.sqrt t := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [← h1, Real.rpow_neg (le_of_lt ht), inv_eq_one_div]

/-- The per-mode arithmetic of the majorant: `(2m+1)/(lam m · √(2m+1)) ≤ (2m+1)^{-3/2}`. -/
lemma div_lam_sqrt_le {m : ℕ} (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ (2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have htpos : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hsqrtpos : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos.mpr htpos
  have hdenpos : 0 < (2 * (m : ℝ) + 1) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) :=
    mul_pos (pow_pos htpos 2) hsqrtpos
  have hsq := sq_two_mul_add_one_le_lam hm
  have hden : (2 * (m : ℝ) + 1) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)
      ≤ Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hsq (le_of_lt hsqrtpos)
  have hinv : (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))⁻¹
      ≤ ((2 * (m : ℝ) + 1) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1))⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hdenpos hden
  have h1 : (2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
        * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ (2 * (m : ℝ) + 1) / ((2 * (m : ℝ) + 1) ^ 2
          * Real.sqrt (2 * (m : ℝ) + 1)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (le_of_lt htpos)
  have h2 : (2 * (m : ℝ) + 1) / ((2 * (m : ℝ) + 1) ^ 2
        * Real.sqrt (2 * (m : ℝ) + 1))
      = (2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    have h3 : (2 * (m : ℝ) + 1) / ((2 * (m : ℝ) + 1) ^ 2
          * Real.sqrt (2 * (m : ℝ) + 1))
        = 1 / ((2 * (m : ℝ) + 1) * Real.sqrt (2 * (m : ℝ) + 1)) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [h3, one_div_mul_sqrt _ htpos]
  exact le_trans h1 (le_of_eq h2)

/-! ## The term bound and its consequences -/

/-- **The per-term bound.** -/
lemma abs_bmode_mul_eFam_le (ψ : ℝ → ℝ) (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    {Cd Cg : ℝ} (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * (2 * (m : ℝ) + 1))
    (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ‖Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
      ≤ mcMajor Cd Cg m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [hb0, zero_mul, norm_zero, mcMajor]
    simp
  · have h1 : ‖Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
        = |Work.FTS.PhiStar.Series.bmode m ψ|
          * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by
      rw [Real.norm_eq_abs, abs_mul]
    have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos (by
        rw [Work.FTS.PhiStar.Gegenbauer.lam]
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith) (Real.sqrt_pos.mpr (by positivity))
    have hstep : |Work.FTS.PhiStar.Series.bmode m ψ|
          * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ Cd * Cg * ((2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
      have hb := hdec m hm
      have he := hgr m θ hθ
      have harith : (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
            * (2 * (m : ℝ) + 1)
          ≤ Cd * ((2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
        have h := div_lam_sqrt_le (m := m) hm
        have hdiv : (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1))) * (2 * (m : ℝ) + 1)
            = Cd * ((2 * (m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m
              * Real.sqrt (2 * (m : ℝ) + 1))) := by
          ring
        rw [hdiv]
        exact mul_le_mul_of_nonneg_left h (le_of_lt hCd)
      calc |Work.FTS.PhiStar.Series.bmode m ψ|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * (Cg * (2 * (m : ℝ) + 1)) :=
            mul_le_mul hb he (abs_nonneg _) (le_of_lt (div_pos hCd hden))
        _ = Cg * ((Cd / (Work.FTS.PhiStar.Gegenbauer.lam m
                * Real.sqrt (2 * (m : ℝ) + 1))) * (2 * (m : ℝ) + 1)) := by ring
        _ ≤ Cg * (Cd * ((2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ)))) :=
            mul_le_mul_of_nonneg_left harith (le_of_lt hCg)
        _ = Cd * Cg * ((2 * (m : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by ring
    rw [h1, mcMajor, if_neg (by omega : ¬ (m = 0))]
    exact hstep

/-- **Pointwise summability** of the mode series on `Iθ`. -/
lemma summable_bmode_eFam_aux (ψ : ℝ → ℝ) (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    {Cd Cg : ℝ} (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * (2 * (m : ℝ) + 1)) :
    ∀ θ ∈ Work.Spaces.Iθ, Summable (fun m : ℕ =>
      Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  intro θ hθ
  refine Summable.of_norm_bounded (summable_mcMajor Cd Cg hCd hCg) (fun m => ?_)
  exact abs_bmode_mul_eFam_le ψ hb0 hCd hCg hdec hgr m hθ

/-- **Continuity** of the mode series on `Iθ`. -/
lemma continuousOn_tsum_bmode_eFam_aux (ψ : ℝ → ℝ)
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    {Cd Cg : ℝ} (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * (2 * (m : ℝ) + 1)) :
    ContinuousOn (fun θ : ℝ => ∑' m : ℕ,
      Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
      Work.Spaces.Iθ :=
  continuousOn_tsum (fun m => ((continuous_eFam_aux m).const_mul _).continuousOn)
    (summable_mcMajor Cd Cg hCd hCg)
    (fun m θ hθ => abs_bmode_mul_eFam_le ψ hb0 hCd hCg hdec hgr m hθ)

/-- **The `eFam n`-coefficient of the series is `bmode n ψ`.** -/
lemma integral_series_mul_eFam_aux (ψ : ℝ → ℝ) (n : ℕ)
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    {Cd Cg : ℝ} (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * (2 * (m : ℝ) + 1)) :
    (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ,
        Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = Work.FTS.PhiStar.Series.bmode n ψ
        * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
  have hB : 0 ≤ Cg * (2 * (n : ℝ) + 1) := by positivity
  have hmain : HasSum (fun m : ℕ => ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ,
        Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) := by
    refine hasSum_integral_of_dominated_convergence
      (μ := volume.restrict Work.Spaces.Iθ)
      (F := fun m θ => (Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (f := fun θ => (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      (fun m _ => mcMajor Cd Cg m * (Cg * (2 * (n : ℝ) + 1))) ?_ ?_ ?_ ?_ ?_
    · intro m
      exact ((continuous_const.mul (continuous_eFam_aux m)).mul
        ((continuous_eFam_aux n).mul Real.continuous_cos)).aestronglyMeasurable
    · intro m
      simp only [Work.Spaces.Iθ]
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_bmode_mul_eFam_le ψ hb0 hCd hCg hdec hgr m ha
      have h2 : |Work.FTS.PhiStar.Gegenbauer.eFam n a * Real.cos a|
          ≤ Cg * (2 * (n : ℝ) + 1) := by
        rw [abs_mul]
        calc |Work.FTS.PhiStar.Gegenbauer.eFam n a| * |Real.cos a|
            ≤ (Cg * (2 * (n : ℝ) + 1)) * 1 :=
              mul_le_mul (hgr n a ha) (Real.abs_cos_le_one a) (abs_nonneg _) hB
          _ = Cg * (2 * (n : ℝ) + 1) := by ring
      exact mul_le_mul h1 h2 (abs_nonneg _) (mcMajor_nonneg Cd Cg hCd hCg m)
    · exact Filter.Eventually.of_forall
        (fun _ => (summable_mcMajor Cd Cg hCd hCg).mul_right _)
    · haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
        constructor
        rw [Work.Spaces.Iθ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2))).measure_lt_top
      have hc : Integrable (fun _ : ℝ =>
          ∑' m : ℕ, mcMajor Cd Cg m * (Cg * (2 * (n : ℝ) + 1)))
          (volume.restrict Work.Spaces.Iθ) := integrable_const _
      simpa using hc
    · simp only [Work.Spaces.Iθ]
      rw [ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      exact ((summable_bmode_eFam_aux ψ hb0 hCd hCg hdec hgr a ha).hasSum).mul_right _
  have hterm : ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
      = Work.FTS.PhiStar.Series.bmode m ψ
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := by
    intro m
    have h1 : (∫ θ in Work.Spaces.Iθ,
          (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Series.bmode m ψ
            * (Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [h1, integral_const_mul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  have hGzero : ∀ m : ℕ, m ≠ n →
      (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) = 0 := by
    intro m hmn
    rw [Work.FTS.PhiStar.Series.iota_eq_interval]
    exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal m n hmn
  have hGn : (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ
      * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ :=
    integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
  calc (∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    _ = ∑' m : ℕ, ∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := hmain.tsum_eq.symm
    _ = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) := tsum_congr hterm
    _ = Work.FTS.PhiStar.Series.bmode n ψ
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ
            * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) :=
        tsum_eq_single n (fun m hm => by rw [hGzero m hm, mul_zero])
    _ = Work.FTS.PhiStar.Series.bmode n ψ
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2
            * Real.cos θ) := by rw [hGn]

/-! ## The expansion -/

theorem BmodeExpansionSelf (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hcont : ContinuousOn ψ (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ| ≤ M)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ := by
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  obtain ⟨M₀, hM₀⟩ := hbdd
  set M : ℝ := |M₀| with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact abs_nonneg _
  have hM : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |ψ θ| ≤ M := by
    intro θ hθ
    rw [hMdef]
    exact le_trans (hM₀ θ hθ) (le_abs_self M₀)
  have hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0 := bmode_zero_aux hmom
  set F : ℝ → ℝ := fun θ => ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
    * Work.FTS.PhiStar.Gegenbauer.eFam m θ with hF
  have hFcont : ContinuousOn F Work.Spaces.Iθ :=
    continuousOn_tsum_bmode_eFam_aux ψ hb0 hCd hCg hdec hgr
  have hFcontIoo : ContinuousOn F (Set.Ioo 0 (Real.pi / 2)) :=
    hFcont.mono Set.Ioo_subset_Icc_self
  have hK : 0 ≤ ∑' m : ℕ, mcMajor Cd Cg m :=
    tsum_nonneg (fun m => mcMajor_nonneg Cd Cg hCd hCg m)
  -- the coefficient of the series against `eFam n`
  have hcoef : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ, F θ
        * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
      = Work.FTS.PhiStar.Series.bmode n ψ
        * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
    intro n
    have h := integral_series_mul_eFam_aux ψ n hb0 hCd hCg hdec hgr
    simpa only [hF] using h
  -- the difference is orthogonal to every eigenfunction
  have horth : ∀ n : ℕ, (∫ θ in Work.Spaces.Iθ, (ψ θ - F θ)
      * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ) = 0 := by
    intro n
    have hψint : IntegrableOn (fun θ : ℝ => ψ θ
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) Work.Spaces.Iθ := by
      refine IntegrableOn.of_bound ?_ ?_ (M * (Cg * (2 * (n : ℝ) + 1))) ?_
      · rw [Work.Spaces.Iθ]
        exact (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2))).measure_lt_top
      · rw [restrict_Iθ_eq_restrict_Ioo]
        exact (hcont.aestronglyMeasurable measurableSet_Ioo).mul
          (((continuous_eFam_aux n).continuousOn.mul Real.continuous_cos.continuousOn).aestronglyMeasurable
            measurableSet_Ioo)
      · rw [restrict_Iθ_eq_restrict_Ioo, ae_restrict_iff' measurableSet_Ioo]
        refine Filter.Eventually.of_forall (fun θ hθ => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |ψ θ| ≤ M := hM θ hθ
        have h2 : |Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ|
            ≤ Cg * (2 * (n : ℝ) + 1) := by
          rw [abs_mul]
          calc |Work.FTS.PhiStar.Gegenbauer.eFam n θ| * |Real.cos θ|
              ≤ (Cg * (2 * (n : ℝ) + 1)) * 1 :=
                mul_le_mul (hgr n θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
                  (Real.abs_cos_le_one θ) (abs_nonneg _) (by positivity)
            _ = Cg * (2 * (n : ℝ) + 1) := by ring
        exact mul_le_mul h1 h2 (abs_nonneg _) hMnn
    have hFint : IntegrableOn (fun θ : ℝ => F θ
        * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hFcont.mul (((continuous_eFam_aux n).mul Real.continuous_cos).continuousOn))
    have hcongr : (∫ θ in Work.Spaces.Iθ, (ψ θ - F θ)
          * Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
        = ∫ θ in Work.Spaces.Iθ, (ψ θ
            * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)
          - F θ * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [hcongr, integral_sub hψint hFint]
    have hψcoef : (∫ θ in Work.Spaces.Iθ, ψ θ
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = Work.FTS.PhiStar.Series.bmode n ψ
          * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
      rw [← Work.FTS.PhiStar.Series.bmode_mul_norm n ψ]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    have hFcoef : (∫ θ in Work.Spaces.Iθ, F θ
          * (Work.FTS.PhiStar.Gegenbauer.eFam n θ * Real.cos θ))
        = Work.FTS.PhiStar.Series.bmode n ψ
          * (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam n θ ^ 2 * Real.cos θ) := by
      rw [← hcoef n]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    rw [hψcoef, hFcoef, sub_self]
  -- measurability of the difference on `Iθ`
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => ψ θ - F θ)
      (volume.restrict Work.Spaces.Iθ) := by
    rw [restrict_Iθ_eq_restrict_Ioo]
    exact (hcont.aestronglyMeasurable measurableSet_Ioo).sub
      (hFcontIoo.aestronglyMeasurable measurableSet_Ioo)
  -- integrability of `(ψ - F)² cos θ` on `Iθ`
  have hbound : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖(ψ θ - F θ) ^ 2 * Real.cos θ‖
        ≤ (M + ∑' m : ℕ, mcMajor Cd Cg m) ^ 2 := by
    intro θ hθ
    have hFb : |F θ| ≤ ∑' m : ℕ, mcMajor Cd Cg m := by
      have hsumRaw : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
        Summable.of_norm_bounded (summable_mcMajor Cd Cg hCd hCg)
          (fun m => abs_bmode_mul_eFam_le ψ hb0 hCd hCg hdec hgr m
            ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      have hsumθ : Summable (fun m : ℕ => ‖Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖) := hsumRaw.norm
      calc |F θ| = ‖F θ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' m : ℕ, ‖Work.FTS.PhiStar.Series.bmode m ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ :=
            norm_tsum_le_tsum_norm hsumθ
        _ ≤ ∑' m : ℕ, mcMajor Cd Cg m :=
            Summable.tsum_le_tsum (fun m => abs_bmode_mul_eFam_le ψ hb0 hCd hCg hdec hgr m
              ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) hsumθ (summable_mcMajor Cd Cg hCd hCg)
    have h1 : |ψ θ - F θ| ≤ M + ∑' m : ℕ, mcMajor Cd Cg m := by
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · have h2 : -F θ ≤ ∑' m : ℕ, mcMajor Cd Cg m :=
          le_trans (neg_le_abs (F θ)) hFb
        have h3 : ψ θ ≤ M := le_trans (le_abs_self (ψ θ)) (hM θ hθ)
        linarith
      · have h2 : F θ ≤ ∑' m : ℕ, mcMajor Cd Cg m :=
          le_trans (le_abs_self (F θ)) hFb
        have h3 : -ψ θ ≤ M := le_trans (neg_le_abs (ψ θ)) (hM θ hθ)
        linarith
    calc ‖(ψ θ - F θ) ^ 2 * Real.cos θ‖
        = |ψ θ - F θ| ^ 2 * |Real.cos θ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), sq_abs]
      _ ≤ (M + ∑' m : ℕ, mcMajor Cd Cg m) ^ 2 * 1 := by
          refine mul_le_mul ?_ (Real.abs_cos_le_one θ) (abs_nonneg _) (by positivity)
          exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (M + ∑' m : ℕ, mcMajor Cd Cg m) ^ 2 := by ring
  have hint : IntegrableOn (fun θ : ℝ => (ψ θ - F θ) ^ 2 * Real.cos θ)
      Work.Spaces.Iθ := by
    refine IntegrableOn.of_bound ?_ ?_ ((M + ∑' m : ℕ, mcMajor Cd Cg m) ^ 2) ?_
    · rw [Work.Spaces.Iθ]
      exact (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2))).measure_lt_top
    · rw [restrict_Iθ_eq_restrict_Ioo]
      exact (((hcont.sub hFcontIoo).aestronglyMeasurable measurableSet_Ioo).pow 2).mul
        (Real.continuous_cos.continuousOn.aestronglyMeasurable measurableSet_Ioo)
    · rw [restrict_Iθ_eq_restrict_Ioo, ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall (fun θ hθ => hbound θ hθ)
  -- completeness
  have hae := Work.FTS.PhiStar.Gegenbauer.eFam_complete (fun θ : ℝ => ψ θ - F θ)
    hmeas hint horth
  have hae' : (fun θ : ℝ => ψ θ - F θ)
      =ᵐ[volume.restrict (Set.Ioo 0 (Real.pi / 2))] 0 := by
    rw [← restrict_Iθ_eq_restrict_Ioo]
    exact hae
  have heq : EqOn (fun θ : ℝ => ψ θ - F θ) 0 (Set.Ioo 0 (Real.pi / 2)) :=
    Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo (hcont.sub hFcontIoo) continuousOn_const
  intro θ hθ
  have h0 : ψ θ - F θ = 0 := heq hθ
  have h1 : F θ = ψ θ := by linarith
  simpa only [hF] using h1

end Work.FTS.PhiStar.FlatWAux.MomentChiaAux
