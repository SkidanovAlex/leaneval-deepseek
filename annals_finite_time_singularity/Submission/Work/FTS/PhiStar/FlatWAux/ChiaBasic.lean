/-
# `Work.FTS.PhiStar.FlatWAux.ChiaBasic`

Basic regularity of the resummed angular profiles `chia ψ j = sin 2θ · Wt ψ j`.

For `j ≥ 1` (`j = k + 1`) the profile is the `eFam`-series

  `chia ψ j θ = Σ_m b_m λ_m^{-j} e_m(θ)`,   `b_m = bmode m ψ`, `λ_m = lam m`,

on `(0, π/2)` (`chia_eq_tsum`), and the two hypotheses `hdec` (decay of `b_m` like
`(λ_m · √(2m+1))^{-1}`) and `hgr` (growth of `e_m` like `2m+1`) make the series converge
absolutely and uniformly: since `λ_m ≥ 4m²` for `m ≥ 1` and `(λ_0)⁻¹ = 0` kills the `m = 0`
term, the `m`-th term is bounded by

  `|b_m| · λ_m^{-j} · |e_m θ| ≤ (λ_m √(2m+1))^{-1} · λ_m^{-1} · (2m+1) ≲ (m+1)^{-3}`,

which is summable.  Hence `chia ψ j` is continuous on `(0, π/2)` and bounded there, and the
series can be integrated termwise; the individual integrals vanish because

  `∫_{Iθ} (λ_m e_m(θ)) · sinθcos²θ dθ = 0`   (`MomentLamEFam`),

so `∫_{Iθ} chia ψ j θ · sinθcos²θ dθ = 0` — the vanishing `sinθcos²θ`-moment, which is exactly
the compatibility condition of the zero-moment inverse `Linv`.

The third hypothesis `hQ` (bounds on the `θ`-derivatives of `Qm m = eFam m / sin 2θ`) is not
needed for these four basic statements; it belongs to the interface of the sibling lemmas
(`AngBound`, `MomentChia`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.FlatWAux.MomentLamEFam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-- The summable majorant of the `m`-th term of the series of `chia ψ (k+1)`: with
`λ_m ≥ 4m²` and `√(2m+1) ≥ 1` the term is bounded by `3 Cd Cg (m+1)^{-3}`. -/
private def chiaMajorant (Cd Cg : ℝ) (m : ℕ) : ℝ :=
  3 * Cd * Cg * (1 / ((m : ℝ) + 1) ^ 3)

private lemma chiaMajorant_nonneg (Cd Cg : ℝ) (hCd : 0 < Cd) (hCg : 0 < Cg) (m : ℕ) :
    0 ≤ chiaMajorant Cd Cg m := by
  rw [chiaMajorant]
  positivity

/-- `eFam m` is continuous (a polynomial in `cos θ` and `sin θ`). -/
private lemma continuous_eFam (m : ℕ) : Continuous (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  change Continuous (fun θ : ℝ =>
    Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
  exact Real.continuous_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous.comp
      Real.continuous_sin)

private lemma continuous_sinCos2 : Continuous Work.Elliptic.sinCos2 := by
  change Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- `e_m(0) = 0`: the odd-indexed Gegenbauer polynomials vanish at the origin. -/
private lemma eFam_apply_zero (m : ℕ) : Work.FTS.PhiStar.Gegenbauer.eFam m 0 = 0 := by
  simp [Work.FTS.PhiStar.Gegenbauer.eFam, Work.FTS.PhiStar.Gegenbauer.gC_odd_zero]

/-- `e_m(π/2) = 0`. -/
private lemma eFam_apply_pi_div_two (m : ℕ) :
    Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2) = 0 := by
  simp [Work.FTS.PhiStar.Gegenbauer.eFam, Real.cos_pi_div_two]

/-- The `sin θ cos² θ`-moment of `e_m` vanishes for `m ≥ 1`: `λ_m e_m` has vanishing moment
(`MomentLamEFam`) and `λ_m ≠ 0` for `m ≥ 1`. -/
private lemma integral_eFam_mul_sinCos2 (m : ℕ) (hm : 1 ≤ m) :
    (∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ) = 0 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlam : Work.FTS.PhiStar.Gegenbauer.lam m ≠ 0 := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]
    positivity
  have hpt : ∀ θ : ℝ,
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ
        = (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹
          * ((Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * Work.Elliptic.sinCos2 θ) := by
    intro θ
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hcongr : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹
          * ((Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              * Work.Elliptic.sinCos2 θ) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt θ)
  rw [hcongr, MeasureTheory.integral_const_mul, (MomentLamEFam m).1, mul_zero]

/-- `Σ_m (m+1)^{-3}` is summable (it is `Σ_m m^{-3}`, shifted). -/
private lemma summable_rpow_neg_three :
    Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(3 : ℝ))) := by
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) :=
    (Real.summable_nat_rpow (p := (-(3 : ℝ)))).mpr (by norm_num)
  have h1 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ))) 1).mpr h0
  simpa only [Nat.cast_add, Nat.cast_one] using h1

/-- `x^{-3} = 1/x³` (the exponent written as a `ℕ`-cast so that `Real.rpow_natCast` applies). -/
private lemma rpow_neg_three {x : ℝ} (hx : 0 ≤ x) : x ^ (-(3 : ℝ)) = 1 / x ^ 3 := by
  rw [show (-(3 : ℝ)) = -(((3 : ℕ)) : ℝ) by norm_num,
    Real.rpow_neg hx (((3 : ℕ)) : ℝ), Real.rpow_natCast, one_div]

/-- The majorant sequences are summable. -/
private lemma summable_chiaMajorant (Cd Cg : ℝ) : Summable (chiaMajorant Cd Cg) := by
  have h : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 3) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      summable_rpow_neg_three
    rw [rpow_neg_three (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  change Summable (fun m : ℕ => 3 * Cd * Cg * (1 / ((m : ℝ) + 1) ^ 3))
  exact h.mul_left (3 * Cd * Cg)

/-- Arithmetic core of the term bound: with `λ ≥ 4M²` (`M = m ≥ 1`) and `√(2M+1) ≥ 1` one has
`(2M+1)/(λ²√(2M+1)) ≤ 3/(M+1)³`. -/
private lemma chia_arith_core (Cd Cg L M : ℝ) (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hM : 1 ≤ M) (hL : 4 * M ^ 2 ≤ L) :
    (Cd / (L * Real.sqrt (2 * M + 1))) * L⁻¹ * (Cg * (2 * M + 1))
      ≤ 3 * Cd * Cg * (1 / (M + 1) ^ 3) := by
  have hLpos : 0 < L := by nlinarith [hL, hM, sq_nonneg M]
  have hMpos : 0 < M + 1 := by linarith
  have hNpos : 0 < 2 * M + 1 := by linarith
  have hspos : 0 < Real.sqrt (2 * M + 1) := Real.sqrt_pos.mpr hNpos
  have hs1 : 1 ≤ Real.sqrt (2 * M + 1) := Real.one_le_sqrt.mpr (by linarith)
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hsne : Real.sqrt (2 * M + 1) ≠ 0 := ne_of_gt hspos
  have hLNne : L * Real.sqrt (2 * M + 1) ≠ 0 := ne_of_gt (mul_pos hLpos hspos)
  have hL2Nne : L ^ 2 * Real.sqrt (2 * M + 1) ≠ 0 :=
    ne_of_gt (mul_pos (pow_pos hLpos 2) hspos)
  -- `16 M⁴ ≤ L²`
  have hLsq : 16 * M ^ 4 ≤ L ^ 2 := by
    have h1 : (4 * M ^ 2) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hL 2
    have h2 : (4 * M ^ 2) ^ 2 = 16 * M ^ 4 := by ring
    rwa [h2] at h1
  -- `(2M+1)(M+1)³ ≤ 3 L²`
  have hfinal : (2 * M + 1) * (M + 1) ^ 3 ≤ 3 * L ^ 2 := by
    have h2M : M + 1 ≤ 2 * M := by linarith
    have hcube : (M + 1) ^ 3 ≤ (2 * M) ^ 3 := pow_le_pow_left₀ (by linarith) h2M 3
    have hN3 : 2 * M + 1 ≤ 3 * (M + 1) := by linarith
    calc (2 * M + 1) * (M + 1) ^ 3
        ≤ (3 * (M + 1)) * (M + 1) ^ 3 := mul_le_mul_of_nonneg_right hN3 (by positivity)
      _ = 3 * ((M + 1) ^ 3 * (M + 1)) := by ring
      _ ≤ 3 * ((2 * M) ^ 3 * (2 * M)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul hcube h2M (by linarith) (by positivity)
      _ = 48 * M ^ 4 := by ring
      _ ≤ 3 * L ^ 2 := by linarith [hLsq]
  have hkey : (2 * M + 1) / L ^ 2 ≤ 3 / (M + 1) ^ 3 := by
    rw [div_le_div_iff₀ (pow_pos hLpos 2) (pow_pos hMpos 3)]
    exact hfinal
  have heq : (Cd / (L * Real.sqrt (2 * M + 1))) * L⁻¹ * (Cg * (2 * M + 1))
      = Cd * Cg * ((2 * M + 1) / (L ^ 2 * Real.sqrt (2 * M + 1))) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    rw [show (L ^ 2 * Real.sqrt (2 * M + 1))⁻¹
        = (L * Real.sqrt (2 * M + 1))⁻¹ * L⁻¹ by
      rw [show L ^ 2 * Real.sqrt (2 * M + 1) = (L * Real.sqrt (2 * M + 1)) * L by ring,
        mul_inv]]
    ring
  have hmono : (2 * M + 1) / (L ^ 2 * Real.sqrt (2 * M + 1)) ≤ (2 * M + 1) / L ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos (pow_pos hLpos 2) hspos) (pow_pos hLpos 2)]
    have hh : L ^ 2 ≤ L ^ 2 * Real.sqrt (2 * M + 1) := by
      simpa using mul_le_mul_of_nonneg_left hs1 (sq_nonneg L)
    exact mul_le_mul_of_nonneg_left hh (by linarith)
  rw [heq]
  calc Cd * Cg * ((2 * M + 1) / (L ^ 2 * Real.sqrt (2 * M + 1)))
      ≤ Cd * Cg * ((2 * M + 1) / L ^ 2) := mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ Cd * Cg * (3 / (M + 1) ^ 3) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 3 * Cd * Cg * (1 / (M + 1) ^ 3) := by ring

/-- Termwise bound for the series of `chia ψ (k+1)`. -/
private lemma chia_term_bound (ψ : ℝ → ℝ) {Cd Cg : ℝ} (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * (2 * (m : ℝ) + 1))
    (k : ℕ) :
    ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      ‖Work.FTS.PhiStar.Series.bmode m ψ * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ ≤ chiaMajorant Cd Cg m := by
  intro m θ hθ
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hzero : Work.FTS.PhiStar.Series.bmode 0 ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam 0)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ = 0 := by
      simp [Work.FTS.PhiStar.Gegenbauer.lam]
    rw [hzero, norm_zero, chiaMajorant]
    positivity
  · have hM : 1 ≤ (m : ℝ) := by exact_mod_cast hm
    have hL4 : 4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
      rw [Work.FTS.PhiStar.Gegenbauer.lam]
      nlinarith [hM]
    have hLam1 : 1 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
      have hM2 : 1 ≤ (m : ℝ) ^ 2 := by nlinarith [hM]
      nlinarith [hL4, hM2]
    have hLampos : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := lt_of_lt_of_le one_pos hLam1
    have hP : |((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)|
        ≤ (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ := by
      rw [abs_of_nonneg (pow_nonneg (le_of_lt (inv_pos.mpr hLampos)) _), inv_pow]
      have hp : (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 1
          ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ (k + 1) :=
        pow_le_pow_right₀ hLam1 (by omega)
      have h' := one_div_le_one_div_of_le
        (show (0 : ℝ) < (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 1 by positivity) hp
      simpa only [one_div, pow_one] using h'
    have hb : |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) := hdec m hm
    have he : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * (2 * (m : ℝ) + 1) := hgr m θ hθ
    have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos hLampos (Real.sqrt_pos.mpr (by linarith))
    have hstep : ‖Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
        ≤ (Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
            * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ * (Cg * (2 * (m : ℝ) + 1)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hb hP (abs_nonneg _) (le_of_lt (div_pos hCd hden))) he
        (abs_nonneg _) (le_of_lt (mul_pos (div_pos hCd hden) (inv_pos.mpr hLampos)))
    refine le_trans hstep ?_
    rw [chiaMajorant]
    exact chia_arith_core Cd Cg (Work.FTS.PhiStar.Gegenbauer.lam m) (m : ℝ) hCd hCg hM hL4

/-- `chia ψ (k+1)` agrees with its defining `eFam`-series on all of `Iθ` (on the open interval
this is `chia_eq_tsum`; at the two endpoints both sides vanish). -/
private lemma chia_eq_tsum_Iθ (ψ : ℝ → ℝ) (k : ℕ) :
    EqOn (chia ψ (k + 1)) (fun θ : ℝ => ∑' m : ℕ,
      Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ := by
  intro θ hθ
  rw [Work.Spaces.Iθ] at hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    have hL : chia ψ (k + 1) 0 = 0 := by
      change Work.Construction.s2 0 * Wt ψ (k + 1) 0 = 0
      rw [Work.Construction.s2_eq]
      simp
    have hR : (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
          * Work.FTS.PhiStar.Gegenbauer.eFam m 0) = 0 := by
      rw [show (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m 0) = (fun _ => (0 : ℝ)) by
        funext m
        simp [eFam_apply_zero m]]
      exact (hasSum_zero (α := ℝ)).tsum_eq
    show chia ψ (k + 1) 0 = (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
          * Work.FTS.PhiStar.Gegenbauer.eFam m 0)
    rw [hL, hR]
  · rcases lt_or_eq_of_le hθ.2 with h2 | h2
    · exact chia_eq_tsum ψ k ⟨h0, h2⟩
    · subst h2
      have hL : chia ψ (k + 1) (Real.pi / 2) = 0 := by
        change Work.Construction.s2 (Real.pi / 2) * Wt ψ (k + 1) (Real.pi / 2) = 0
        rw [Work.Construction.s2_eq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi,
          zero_mul]
      have hR : (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2)) = 0 := by
        rw [show (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2)) = (fun _ => (0 : ℝ)) by
          funext m
          simp [eFam_apply_pi_div_two m]]
        exact (hasSum_zero (α := ℝ)).tsum_eq
      show chia ψ (k + 1) (Real.pi / 2) = (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2))
      rw [hL, hR]

/-- **The basic facts about `chia ψ j` for `j = k+1 ≥ 1`.** -/
private lemma chia_basic_aux (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (k : ℕ) :
    ContinuousOn (chia ψ (k + 1)) (Set.Ioo 0 (Real.pi / 2)) ∧
      (∃ M : ℝ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |chia ψ (k + 1) θ| ≤ M) ∧
      MeasureTheory.IntegrableOn (fun θ : ℝ =>
        chia ψ (k + 1) θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, chia ψ (k + 1) θ * Work.Elliptic.sinCos2 θ) = 0 := by
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  have hsum : Summable (chiaMajorant Cd Cg) := summable_chiaMajorant Cd Cg
  have hterm : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      ‖Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ ≤ chiaMajorant Cd Cg m :=
    fun m θ hθ => chia_term_bound ψ hCd hCg hdec hgr k m θ hθ
  -- the series converges absolutely and uniformly on `Iθ`
  have hGcont : ContinuousOn (fun θ : ℝ => ∑' m : ℕ,
      Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ :=
    continuousOn_tsum (fun m => ((continuous_eFam m).const_mul _).continuousOn) hsum hterm
  have hsub : Set.Ioo 0 (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    exact Set.Ioo_subset_Icc_self
  have hEq : EqOn (chia ψ (k + 1)) (fun θ : ℝ => ∑' m : ℕ,
      Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) Work.Spaces.Iθ :=
    chia_eq_tsum_Iθ ψ k
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- continuity on the open interval
    exact (hGcont.mono hsub).congr (hEq.mono hsub)
  · -- boundedness on the open interval
    refine ⟨∑' m : ℕ, chiaMajorant Cd Cg m, fun θ hθ => ?_⟩
    have hθI : θ ∈ Work.Spaces.Iθ := hsub hθ
    have hEqθ : chia ψ (k + 1) θ = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ := hEq hθI
    rw [hEqθ]
    have hsumθ : Summable (fun m : ℕ => ‖Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖) :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hterm m θ hθI) hsum
    calc |∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        = ‖∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑' m : ℕ, ‖Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ := norm_tsum_le_tsum_norm hsumθ
      _ ≤ ∑' m : ℕ, chiaMajorant Cd Cg m :=
          Summable.tsum_le_tsum (fun m => hterm m θ hθI) hsumθ hsum
  · -- integrability of the integrand on `Iθ`
    have hcont_prod : ContinuousOn (fun θ : ℝ => (∑' m : ℕ,
        Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ :=
      hGcont.mul continuous_sinCos2.continuousOn
    have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ => (∑' m : ℕ,
        Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ :=
      ContinuousOn.integrableOn_compact isCompact_Icc hcont_prod
    refine hInt.congr_fun (fun θ hθ => ?_) measurableSet_Icc
    simp only [hEq hθ]
  · -- the integral vanishes
    have hIntEq : (∫ θ in Work.Spaces.Iθ, chia ψ (k + 1) θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by simp only [hEq hθ])
    rw [hIntEq]
    -- the termwise integrals vanish
    have htermInt : ∀ m : ℕ, (∫ θ in Work.Spaces.Iθ,
        (Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ) = 0 := by
      intro m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        have hzero : (fun θ : ℝ => (Work.FTS.PhiStar.Series.bmode 0 ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam 0)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ) * Work.Elliptic.sinCos2 θ)
            = fun _ => (0 : ℝ) := by
          funext θ
          simp [Work.FTS.PhiStar.Gegenbauer.lam]
        rw [hzero]
        simp
      · have hsplit : (∫ θ in Work.Spaces.Iθ,
            (Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
            = (Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1))
              * (∫ θ in Work.Spaces.Iθ,
                  Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ) := by
          rw [show (∫ θ in Work.Spaces.Iθ,
                (Work.FTS.PhiStar.Series.bmode m ψ
                    * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
                    * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
              = ∫ θ in Work.Spaces.Iθ, (Work.FTS.PhiStar.Series.bmode m ψ
                    * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1))
                  * (Work.FTS.PhiStar.Gegenbauer.eFam m θ * Work.Elliptic.sinCos2 θ) from
            MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
          rw [MeasureTheory.integral_const_mul]
        rw [hsplit, integral_eFam_mul_sinCos2 m hm, mul_zero]
    have hFint : ∀ m : ℕ, MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ := by
      intro m
      exact ContinuousOn.integrableOn_compact isCompact_Icc
        (((continuous_eFam m).const_mul _).mul continuous_sinCos2).continuousOn
    have hpart_cont : ∀ N : ℕ, Continuous (fun θ : ℝ =>
        (∑ m ∈ Finset.range N, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ) :=
      fun N => (continuous_finsetSum (Finset.range N)
        (fun m _ => (continuous_eFam m).const_mul _)).mul continuous_sinCos2
    have hK : 0 ≤ ∑' m : ℕ, chiaMajorant Cd Cg m :=
      tsum_nonneg (fun m => chiaMajorant_nonneg Cd Cg hCd hCg m)
    have hmain : Tendsto (fun N : ℕ => ∫ θ, (∑ m ∈ Finset.range N,
            Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ
          ∂(volume.restrict Work.Spaces.Iθ)) atTop
        (𝓝 (∫ θ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ
            ∂(volume.restrict Work.Spaces.Iθ))) :=
      tendsto_integral_of_dominated_convergence
        (μ := volume.restrict Work.Spaces.Iθ)
        (F := fun (N : ℕ) (θ : ℝ) => (∑ m ∈ Finset.range N,
            Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
        (f := fun (θ : ℝ) => (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
        (fun θ : ℝ => (∑' m : ℕ, chiaMajorant Cd Cg m) * ‖Work.Elliptic.sinCos2 θ‖)
        (fun N => (hpart_cont N).aestronglyMeasurable)
        (ContinuousOn.integrableOn_compact (μ := volume) (K := Work.Spaces.Iθ) isCompact_Icc
          (continuous_const.mul (continuous_norm.comp continuous_sinCos2)).continuousOn)
      (fun N => (MeasureTheory.ae_restrict_mem measurableSet_Icc).mono (fun θ hθ => by
        have h1 : ‖∑ m ∈ Finset.range N, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖
            ≤ ∑ m ∈ Finset.range N, chiaMajorant Cd Cg m :=
          le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun m _ => hterm m θ hθ))
        have h2 : ∑ m ∈ Finset.range N, chiaMajorant Cd Cg m
            ≤ ∑' m : ℕ, chiaMajorant Cd Cg m :=
          Summable.sum_le_tsum (Finset.range N)
            (fun m _ => chiaMajorant_nonneg Cd Cg hCd hCg m) hsum
        rw [norm_mul]
        exact mul_le_mul (le_trans h1 h2) le_rfl (norm_nonneg _) hK))
      ((MeasureTheory.ae_restrict_mem measurableSet_Icc).mono (fun θ hθ => by
        have hsumθ : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
          Summable.of_norm_bounded hsum (fun m => hterm m θ hθ)
        have hpart := hsumθ.hasSum.tendsto_sum_nat
        exact Filter.Tendsto.mul_const (Work.Elliptic.sinCos2 θ) hpart))
    have hzeroN : ∀ N : ℕ, (∫ θ, (∑ m ∈ Finset.range N, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ
          ∂(volume.restrict Work.Spaces.Iθ)) = 0 := by
      intro N
      have h1 : (∫ θ, (∑ m ∈ Finset.range N, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ
            ∂(volume.restrict Work.Spaces.Iθ))
          = ∫ θ, (∑ m ∈ Finset.range N, (Work.FTS.PhiStar.Series.bmode m ψ
                * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ)
              ∂(volume.restrict Work.Spaces.Iθ) := by
        refine integral_congr_ae ?_
        filter_upwards with θ
        rw [Finset.sum_mul]
      rw [h1, MeasureTheory.integral_finsetSum (Finset.range N) (fun m _ => hFint m),
        Finset.sum_eq_zero (fun m _ => htermInt m)]
    have hconst : (fun N : ℕ => (∫ θ, (∑ m ∈ Finset.range N, Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ
          ∂(volume.restrict Work.Spaces.Iθ))) = fun _ => (0 : ℝ) := by
      funext N
      exact hzeroN N
    have hlim0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
        (𝓝 (∫ θ, (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
              * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (k + 1)
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) * Work.Elliptic.sinCos2 θ
            ∂(volume.restrict Work.Spaces.Iθ))) := by
      refine Filter.Tendsto.congr (fun N => ?_) hmain
      exact hzeroN N
    exact (tendsto_nhds_unique tendsto_const_nhds hlim0).symm

theorem ChiaBasic (ψ : ℝ → ℝ)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hQ : ∃ C : ℕ → ℝ, (∀ l : ℕ, 0 ≤ C l) ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ (l : ℕ), l ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |iteratedDeriv l (Work.FTS.PhiStar.FlatWAux.Qm m) θ|
          ≤ C l * (2 * (m : ℝ) + 1) ^ (2 * l + 2)) :
    (∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J →
        ContinuousOn (Work.FTS.PhiStar.FlatWAux.chia ψ j) (Set.Ioo 0 (Real.pi / 2))) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J →
        ∃ M : ℝ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
          |Work.FTS.PhiStar.FlatWAux.chia ψ j θ| ≤ M) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J →
        MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.PhiStar.FlatWAux.chia ψ j θ
          * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J →
        (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.FlatWAux.chia ψ j θ
          * Work.Elliptic.sinCos2 θ) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj _
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
    exact (chia_basic_aux ψ hdec hgr k).1
  · intro j hj _
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
    exact (chia_basic_aux ψ hdec hgr k).2.1
  · intro j hj _
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
    exact (chia_basic_aux ψ hdec hgr k).2.2.1
  · intro j hj _
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
    exact (chia_basic_aux ψ hdec hgr k).2.2.2

end Work.FTS.PhiStar.FlatWAux
