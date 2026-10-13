/-
# `E1Parts/HkMemE1.lean` — `E1 α f ∈ ℋ^n` by domination

`HkMem α n (E1 α f)` for `f ∈ CoerAdm α`, `n ≤ 3`.  The `ℋ^n`-integrand of the *separated*
product `E1 α f = a(θ)·r(z)` (`a = D_θ Γ`, `r = radA α f`) is dominated by a product of an
angular majorant and a radial one: with `G(θ) = Γ(θ)²·sin(2θ)^{-η} + Γ(θ)²·sin(2θ)^{-γ}` and
`Rint(z) = ∑_{j<4} (D_z^j (radA α f)(z))² w(z)²`,

  `HkIntegrand α n (E1 α f) z θ ≤ 10^18 · G(θ) · Rint(z)`  on `Iz × Iθ`,

because every block of a separated product is a product of a block of the angular factor with a
block of the radial one (`dzIter_ang_rad`, `mixed_ang_rad`), the angular blocks of `a = Lop Γ`
are the iterates `Lop^[i+1] Γ ≤ 10^8 Γ` (`AngGam`), and `sin(2θ)^{-η}, sin(2θ)^{-γ}` are the two
angular weights (`light_sq_nn`, `heavy_sq_nn`).

`HkMem_of_majorant` then concludes, using `Rint ∈ L¹` (the radial input `hrad`) and
`G ∈ L¹` (`AngGam`), plus the continuity of the integrand on the open quadrant (from
`BlocksCont`, which is `E1_blocks`). -/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.AngGam
import Submission.Work.FTS.CoercivityFix.Transfer.E1_blocks
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.Nonlinear.Pieces.rowsN0Q
import Submission.Work.FTS.NonlinRows.AuxAngRad.AngRadWeights
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The radial majorant `Rint(z) = ∑_{j<4} (D_z^j r z)² w(z)²`. -/
private noncomputable def radMaj (r : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 4, (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2

/-- The angular majorant `G(θ) = Γ(θ)² sin(2θ)^{-η} + Γ(θ)² sin(2θ)^{-γ}`. -/
private noncomputable def angMaj (α : ℝ) (θ : ℝ) : ℝ :=
  (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
    + (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ

private theorem angMaj_eq (α θ : ℝ) :
    angMaj α θ = (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
      + (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := rfl

private theorem radMaj_eq (r : ℝ → ℝ) (z : ℝ) :
    radMaj r z = ∑ j ∈ Finset.range 4,
      (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2 := rfl

private theorem radMaj_nonneg (r : ℝ → ℝ) (z : ℝ) : 0 ≤ radMaj r z :=
  Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem angMaj_nonneg (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ angMaj α θ := by
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have h1 : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ := by
    rw [Work.FTS.Nonlinear.RadialProd.smE]; exact Real.rpow_nonneg hsin _
  have h2 : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ := by
    rw [Work.FTS.Nonlinear.RadialProd.smG]; exact Real.rpow_nonneg hsin _
  rw [angMaj_eq]
  exact add_nonneg (mul_nonneg (sq_nonneg _) h1) (mul_nonneg (sq_nonneg _) h2)

/-- The Gamman bound `Γ ≥ 0` on `Iθ`. -/
private theorem Gam_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.Gam α θ := by
  rw [show Work.Spaces.Gam α = fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) from rfl]
  exact Real.rpow_nonneg (mul_nonneg
    (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
    (sq_nonneg _)) _

/-! ## The pointwise domination -/

theorem HkIntegrand_E1_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (n : ℕ) (hn : n ≤ 3) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α n (Work.FTS.CoercivityFix.Transfer.E1 α f) z θ
        ≤ 10 ^ 18 * angMaj α θ * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z := by
  obtain ⟨hAng, hAngE, hAngG⟩ := AngGam α hα hα1
  set a : ℝ → ℝ := fun θ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ with ha
  set r : ℝ → ℝ := Work.FTS.CoercivityFix.Transfer.radA α f with hr
  intro z hz θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hE1 : Work.FTS.CoercivityFix.Transfer.E1 α f = fun z θ => a θ * r z := rfl
  have hsmE_nn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ := by
    rw [Work.FTS.Nonlinear.RadialProd.smE]; exact Real.rpow_nonneg hsin _
  have hsmG_nn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ := by
    rw [Work.FTS.Nonlinear.RadialProd.smG]; exact Real.rpow_nonneg hsin _
  have hΓnn : 0 ≤ Work.Spaces.Gam α θ := Gam_nonneg hθ
  have hGnn : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ :=
    mul_nonneg (sq_nonneg _) hsmE_nn
  have hGnn' : 0 ≤ (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ :=
    mul_nonneg (sq_nonneg _) hsmG_nn
  have hAngnn : 0 ≤ angMaj α θ := angMaj_nonneg α hθ
  have hRnn : 0 ≤ radMaj r z := radMaj_nonneg r z
  -- the bound on the angular factor `a = D_θ Γ`
  have ha_lop : a = Work.Spaces.Lop (Work.Spaces.Gam α) := rfl
  have ha_bound : |a θ| ≤ 10 ^ 8 * Work.Spaces.Gam α θ := by
    have h := hAng 1 (by norm_num) (by norm_num) θ hθ
    rw [Function.iterate_one] at h
    rwa [← ha_lop] at h
  have ha_sq : (a θ) ^ 2 ≤ (10 ^ 8 * Work.Spaces.Gam α θ) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg (by norm_num) hΓnn)]
    exact ha_bound
  -- the `D_θ`-blocks of the angular factor
  have hbang_bound : ∀ i : ℕ, i ≤ 3 →
      |Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ| ≤ 10 ^ 8 * Work.Spaces.Gam α θ := by
    intro i hi
    have hconv : Work.Spaces.Lop^[i] (fun θ' : ℝ => a θ')
        = Work.Spaces.Lop^[i + 1] (Work.Spaces.Gam α) := by
      have : (fun θ' : ℝ => a θ') = Work.Spaces.Lop (Work.Spaces.Gam α) := rfl
      rw [this, ← Function.iterate_succ_apply]
    have h1 : Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ
        = (Work.Spaces.Lop^[i + 1] (Work.Spaces.Gam α)) θ := by
      rw [Work.Spaces.DthIter_eq_iterate_Lop]
      show (Work.Spaces.Lop^[i] (fun θ' : ℝ => a θ')) θ = _
      rw [hconv]
    rw [h1]
    exact hAng (i + 1) (by omega) (by omega) θ hθ
  have hbang_sq : ∀ i : ℕ, i ≤ 3 →
      (Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ) ^ 2
        ≤ (10 ^ 8 * Work.Spaces.Gam α θ) ^ 2 := by
    intro i hi
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg (by norm_num) hΓnn)]
    exact hbang_bound i hi
  -- the per-term bounds
  have hterm1 : ∀ i ∈ Finset.range (n + 1),
      (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ 10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
            * radMaj r z := by
    intro i hi
    have hi3 : i ≤ 3 := by
      have := Finset.mem_range.mp hi
      omega
    have hRle : (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ radMaj r z := by
      refine Finset.single_le_sum (f := fun j => (Work.Elliptic.DzdIter j r z) ^ 2
        * (Work.Spaces.w z) ^ 2) (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
      exact Finset.mem_range.mpr (by omega)
    have hwk : 0 ≤ (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [Work.FTS.Nonlinear.Pieces.dzIter_ang_rad a r i z θ,
      Work.FTS.NonlinRows.AuxAngRad.light_sq_nn (a θ * Work.Elliptic.DzdIter i r z) z θ hsin]
    have hkey : (a θ * Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smE θ
        = ((a θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
          * ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      ring
    rw [hkey]
    calc ((a θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
          * ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ((10 ^ 8 * Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
            * radMaj r z :=
          mul_le_mul (mul_le_mul ha_sq le_rfl hsmE_nn (sq_nonneg _)) hRle hwk
            (mul_nonneg (sq_nonneg _) hsmE_nn)
      _ = 10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
            * radMaj r z := by ring
  have hterm2 : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
      (if 1 ≤ i ∧ i + j ≤ n
        then (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
        ≤ 10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
            * radMaj r z := by
    intro i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ n
    · rw [if_pos hc]
      have hi3 : i ≤ 3 := by
        have := Finset.mem_range.mp hi
        omega
      have hj3 : j ≤ 3 := by
        have := Finset.mem_range.mp hj
        omega
      have hRle : (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ radMaj r z := by
        refine Finset.single_le_sum (f := fun j => (Work.Elliptic.DzdIter j r z) ^ 2
          * (Work.Spaces.w z) ^ 2) (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_
        exact Finset.mem_range.mpr (by omega)
      have hwk : 0 ≤ (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
        mul_nonneg (sq_nonneg _) (sq_nonneg _)
      rw [Work.FTS.Nonlinear.Pieces.mixed_ang_rad a r j i z θ,
        Work.FTS.NonlinRows.AuxAngRad.heavy_sq_nn α
          (Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ * Work.Elliptic.DzdIter j r z) z θ hsin]
      have hkey : (Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ
              * Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ
          = ((Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ)
            * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by ring
      rw [hkey]
      calc ((Work.Spaces.DthIter i (fun x θ' => a θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ)
            * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ ((10 ^ 8 * Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
              * radMaj r z :=
            mul_le_mul (mul_le_mul (hbang_sq i hi3) le_rfl hsmG_nn (sq_nonneg _)) hRle hwk
              (mul_nonneg (sq_nonneg _) hsmG_nn)
        _ = 10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
              * radMaj r z := by ring
    · rw [if_neg hc]
      exact mul_nonneg (mul_nonneg (by norm_num) hGnn') hRnn
  -- the two sums
  have hsum1 : (∑ i ∈ Finset.range (n + 1),
      (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
          * radMaj r z) := by
    have h := Finset.sum_le_sum hterm1
    have hcard : (∑ _i ∈ Finset.range (n + 1),
        (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ)
          * radMaj r z))
        = ((n : ℝ) + 1) * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smE θ) * radMaj r z) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [hcard] at h
    have hn4 : ((n : ℝ) + 1) ≤ 4 := by
      have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
      linarith
    refine le_trans h (mul_le_mul_of_nonneg_right hn4 ?_)
    exact mul_nonneg (mul_nonneg (by norm_num) hGnn) hRnn
  have hsum2 : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
      (if 1 ≤ i ∧ i + j ≤ n
        then (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0))
      ≤ 16 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
          * radMaj r z) := by
    have hinner : ∀ i ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.range (n + 1),
          (if 1 ≤ i ∧ i + j ≤ n
            then (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0))
          ≤ 4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
              * radMaj r z) := by
      intro i hi
      have h := Finset.sum_le_sum (fun j hj => hterm2 i hi j hj)
      have hcard : (∑ _j ∈ Finset.range (n + 1),
          (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
            * radMaj r z))
          = ((n : ℝ) + 1) * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ) * radMaj r z) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      rw [hcard] at h
      have hn4 : ((n : ℝ) + 1) ≤ 4 := by
        have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
        linarith
      refine le_trans h (mul_le_mul_of_nonneg_right hn4 ?_)
      exact mul_nonneg (mul_nonneg (by norm_num) hGnn') hRnn
    have h := Finset.sum_le_sum hinner
    have hcard : (∑ _i ∈ Finset.range (n + 1),
        (4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
          * radMaj r z)))
        = ((n : ℝ) + 1) * (4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ) * radMaj r z)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [hcard] at h
    have hn4 : ((n : ℝ) + 1) ≤ 4 := by
      have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
      linarith
    refine le_trans h ?_
    have hb : 0 ≤ 4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smG α θ) * radMaj r z) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hGnn') hRnn)
    calc ((n : ℝ) + 1) * (4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ) * radMaj r z))
        ≤ 4 * (4 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ) * radMaj r z)) :=
          mul_le_mul_of_nonneg_right hn4 hb
      _ = 16 * (10 ^ 16 * ((Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ)
            * radMaj r z) := by ring
  rw [hE1, Work.Spaces.HkIntegrand, angMaj_eq α θ]
  refine le_trans (add_le_add hsum1 hsum2) ?_
  nlinarith [hsum1, hsum2, hGnn, hGnn', hRnn]

/-! ## `HkMem` from the radial input -/

theorem HkMem_E1_of (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (n : ℕ) (hn : n ≤ 3)
    (hcont : Work.FTS.CoercivityFix.Assembly.BlocksCont n
      (Work.FTS.CoercivityFix.Transfer.E1 α f))
    (hrad : ∀ j : ℕ, j ≤ 3 → IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Transfer.E1 α f) := by
  obtain ⟨hAng, hAngE, hAngG⟩ := AngGam α hα hα1
  have hGint : IntegrableOn (fun θ : ℝ => angMaj α θ) Work.Spaces.Iθ := by
    have h := hAngE.add hAngG
    have hfun : (fun θ : ℝ => angMaj α θ) = fun θ : ℝ => (Work.Spaces.Gam α θ) ^ 2
        * Work.FTS.Nonlinear.RadialProd.smE θ
        + (Work.Spaces.Gam α θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
      funext θ; rw [angMaj_eq]
    rw [hfun]
    exact h
  have hRint : IntegrableOn (fun z : ℝ => radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
      Work.Spaces.Iz := by
    have hfun : (fun z : ℝ => radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        = fun z : ℝ => ∑ j ∈ Finset.range 4,
            (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radA α f) z) ^ 2
              * (Work.Spaces.w z) ^ 2 := by
      funext z; rw [radMaj_eq]
    rw [hfun]
    exact MeasureTheory.integrable_finsetSum (Finset.range 4)
      (fun j hj => hrad j (by have := Finset.mem_range.mp hj; omega))
  refine Work.FTS.LocData.HkMem_of_majorant α n
    (f := Work.FTS.CoercivityFix.Transfer.E1 α f)
    (M := fun z θ => 10 ^ 18 * angMaj α θ * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
    ?_ ?_ ?_ ?_
  · exact Work.FTS.CoercivityFix.Transfer.E2pkg.continuousOn_HkIntegrand_of_blocksCont hcont α
  · intro z _
    have hfun : (fun θ : ℝ => 10 ^ 18 * angMaj α θ
        * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        = fun θ : ℝ => (10 ^ 18 * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
            * angMaj α θ := by
      funext θ; ring
    rw [hfun]
    exact hGint.const_mul _
  · have hfun : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        10 ^ 18 * angMaj α θ * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
        = fun z : ℝ => (10 ^ 18 * (∫ θ in Work.Spaces.Iθ, angMaj α θ))
            * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z := by
      funext z
      have h1 : (fun θ : ℝ => 10 ^ 18 * angMaj α θ
          * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
          = fun θ : ℝ => (10 ^ 18 * radMaj (Work.FTS.CoercivityFix.Transfer.radA α f) z)
              * angMaj α θ := by
        funext θ; ring
      rw [h1, MeasureTheory.integral_const_mul]
      ring
    rw [hfun]
    exact hRint.const_mul _
  · intro z hz θ hθ
    exact HkIntegrand_E1_le α hα hα1 n hn z hz θ hθ

end Work.FTS.CoercivityFix.Transfer.E1Parts
