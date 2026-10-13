/-
# `Work.FTS.PhiStar.FlatWAux.MomentChiaAux.SeriesOde`

The Gegenbauer family `eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)` diagonalises `Lzero` with
eigenvalues `lam m = 2m(2m+5)` (`Work.FTS.PhiStar.Gegenbauer.eFam_Lzero`).  This file shows that
a coefficient sequence `c` whose `λ`-weighted version `d m = c m · lam m` is summable builds a
genuine `C²` solution of the model equation:

* `∑_m c_m e_m` is `C²` on `(0, π/2)`;
* `Lzero (∑_m c_m e_m) = ∑_m d_m e_m` there.

**Route.**  `Series.Deleg.psiAngBounds` gives the uniform bounds

  `|e_m| ≤ √(Npsi m)`,  `|e_m'| ≤ 100·Npsi m/cos²θ`,  `|e_m''| ≤ 1000·Npsi m·√(Npsi m)/cos⁴θ`

on `(0,π/2)` (`Npsi m = (2m+2)(2m+3)`), so on each compact subinterval `Ioo ε (π/2 - ε)` of
`(0,π/2)` the mode series is dominated by a summable majorant provided
`∑ |c m|(m+1)² < ∞` (for the first two bounds) and `∑ |c m|(m+1)³ < ∞` (for the second
derivative); the latter follows from `∑ |d m|(m+1) < ∞` and `d m = c m · lam m` since
`lam m ≍ m²`.  Mathlib's `hasDerivAt_tsum_of_isPreconnected` then differentiates termwise twice,
`continuousOn_tsum` gives continuity of the second derivative series, and
`contDiffOn_succ_iff_derivWithin` upgrades `HasDerivAt` data to `ContDiffOn ℝ 2`; the pieces are
glued with `contDiffOn_of_locally_contDiffOn`.  The `Lzero` identity is the termwise eigenrelation
summed against `tsum`-linearity.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Series.Deleg.psiAngBounds
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Lzero_orthogonal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open Filter Set

namespace Work.FTS.PhiStar.FlatWAux.MomentChiaAux

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Work.FTS.PhiStar.Gegenbauer (eFam lam)
open Work.FTS.PhiStar.Series.Deleg (Npsi)

/-! ## 1. Arithmetic of the mode weights -/

lemma Npsi_le_nine (m : ℕ) : Npsi m ≤ 9 * ((m : ℝ) + 1) ^ 2 := by
  rw [Work.FTS.PhiStar.Series.Deleg.Npsi]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

lemma sqrt_Npsi_le_three (m : ℕ) : Real.sqrt (Npsi m) ≤ 3 * ((m : ℝ) + 1) := by
  have h : Npsi m ≤ (3 * ((m : ℝ) + 1)) ^ 2 := by
    have h' := Npsi_le_nine m
    nlinarith
  calc Real.sqrt (Npsi m) ≤ Real.sqrt ((3 * ((m : ℝ) + 1)) ^ 2) := Real.sqrt_le_sqrt h
    _ = 3 * ((m : ℝ) + 1) := Real.sqrt_sq (by positivity)

lemma Npsi_mul_sqrt_le (m : ℕ) : Npsi m * Real.sqrt (Npsi m) ≤ 27 * ((m : ℝ) + 1) ^ 3 := by
  have h1 : Real.sqrt (Npsi m) ≤ 3 * ((m : ℝ) + 1) := sqrt_Npsi_le_three m
  have h3 : Npsi m ≤ 9 * ((m : ℝ) + 1) ^ 2 := Npsi_le_nine m
  calc Npsi m * Real.sqrt (Npsi m) ≤ (9 * ((m : ℝ) + 1) ^ 2) * (3 * ((m : ℝ) + 1)) :=
        mul_le_mul h3 h1 (Real.sqrt_nonneg _) (by positivity)
    _ = 27 * ((m : ℝ) + 1) ^ 3 := by ring

/-! ## 2. Summability of the coefficient-weighted majorants -/

section Summable

variable {c d : ℕ → ℝ}

lemma one_le_cast_add_one (m : ℕ) : (1 : ℝ) ≤ (m : ℝ) + 1 := by
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

lemma summable_abs_c_one (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2)) :
    Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1)) := by
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hc
  have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := one_le_cast_add_one m
  have h2 : (0 : ℝ) ≤ |c m| := abs_nonneg _
  have h3 : ((m : ℝ) + 1) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left h3 h2

lemma summable_abs_c_Npsi (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2)) :
    Summable (fun m : ℕ => |c m| * Npsi m) := by
  refine Summable.of_nonneg_of_le (fun m => by
    exact mul_nonneg (abs_nonneg _) (le_of_lt (Work.FTS.PhiStar.Series.Deleg.Npsi_pos m)))
    (fun m => ?_) (hc.mul_left 9)
  have h := Npsi_le_nine m
  have h2 : (0 : ℝ) ≤ |c m| := abs_nonneg _
  calc |c m| * Npsi m ≤ |c m| * (9 * ((m : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left h h2
    _ = 9 * (|c m| * ((m : ℝ) + 1) ^ 2) := by ring

lemma abs_d_eq (hcd : ∀ m : ℕ, c m * lam m = d m) (m : ℕ) :
    |d m| = |c m| * lam m := by
  have hlam : (0 : ℝ) ≤ lam m := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]; positivity
  rw [← hcd m, abs_mul, abs_of_nonneg hlam]

lemma cube_le_lam (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) + 1) ^ 3 ≤ 4 * lam m * ((m : ℝ) + 1) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hkey : ((m : ℝ) + 1) ^ 2 ≤ 8 * (m : ℝ) * (2 * (m : ℝ) + 5) := by
    nlinarith [sq_nonneg ((m : ℝ))]
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hcube : ((m : ℝ) + 1) ^ 3 = ((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) := by ring
  rw [Work.FTS.PhiStar.Gegenbauer.lam, hcube]
  calc ((m : ℝ) + 1) ^ 2 * ((m : ℝ) + 1)
      ≤ (8 * (m : ℝ) * (2 * (m : ℝ) + 5)) * ((m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hkey (le_of_lt hpos)
    _ = 4 * (2 * (m : ℝ) * (2 * (m : ℝ) + 5)) * ((m : ℝ) + 1) := by ring

lemma cube_le_lam_mul (hcd : ∀ m : ℕ, c m * lam m = d m) {m : ℕ} (hm : 1 ≤ m) :
    |c m| * ((m : ℝ) + 1) ^ 3 ≤ 4 * (|d m| * ((m : ℝ) + 1)) := by
  have hcube := cube_le_lam m hm
  have hc' : (0 : ℝ) ≤ |c m| := abs_nonneg _
  rw [abs_d_eq hcd m]
  calc |c m| * ((m : ℝ) + 1) ^ 3 ≤ |c m| * (4 * lam m * ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hcube hc'
    _ = 4 * (|c m| * lam m * ((m : ℝ) + 1)) := by ring

/-- `Σ_m |c m| (m+1)³` is summable, from `Σ_m |d m| (m+1)` and `d m = c m · lam m`. -/
lemma summable_abs_c_cube (hcd : ∀ m : ℕ, c m * lam m = d m)
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1))) :
    Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 3) := by
  have hshift : Summable (fun k : ℕ => |d (k + 1)| * (((k + 1 : ℕ) : ℝ) + 1)) :=
    (summable_nat_add_iff 1).mpr hd
  have hmain : Summable (fun k : ℕ => |c (k + 1)| * (((k + 1 : ℕ) : ℝ) + 1) ^ 3) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hshift.mul_left 4)
    exact cube_le_lam_mul hcd (Nat.le_add_left 1 k)
  exact (summable_nat_add_iff 1).mp hmain

/-- `Σ_m |c m| (Npsi m)^{3/2}` is summable. -/
lemma summable_abs_c_Npsi32 (hcd : ∀ m : ℕ, c m * lam m = d m)
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1))) :
    Summable (fun m : ℕ => |c m| * (Npsi m * Real.sqrt (Npsi m))) := by
  refine Summable.of_nonneg_of_le (fun m => by
    exact mul_nonneg (abs_nonneg _) (mul_nonneg
      (le_of_lt (Work.FTS.PhiStar.Series.Deleg.Npsi_pos m)) (Real.sqrt_nonneg _)))
    (fun m => ?_) ((summable_abs_c_cube hcd hd).mul_left 27)
  have h := Npsi_mul_sqrt_le m
  have hc' : (0 : ℝ) ≤ |c m| := abs_nonneg _
  calc |c m| * (Npsi m * Real.sqrt (Npsi m)) ≤ |c m| * (27 * ((m : ℝ) + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left h hc'
    _ = 27 * (|c m| * ((m : ℝ) + 1) ^ 3) := by ring

/-- The majorant of the first derivative series is summable. -/
lemma summable_u1 {s : ℝ} (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2)) :
    Summable (fun m : ℕ => 100 * Npsi m / s ^ 2 * |c m|) := by
  have hEq : (fun m : ℕ => 100 * Npsi m / s ^ 2 * |c m|)
      = fun m : ℕ => (100 / s ^ 2) * (|c m| * Npsi m) := by
    funext m; ring
  rw [hEq]
  exact (summable_abs_c_Npsi hc).mul_left _

/-- The majorant of the second derivative series is summable. -/
lemma summable_u2 {s : ℝ} (hcd : ∀ m : ℕ, c m * lam m = d m)
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1))) :
    Summable (fun m : ℕ => 1000 * Npsi m * Real.sqrt (Npsi m) / s ^ 4 * |c m|) := by
  have hEq : (fun m : ℕ => 1000 * Npsi m * Real.sqrt (Npsi m) / s ^ 4 * |c m|)
      = fun m : ℕ => (1000 / s ^ 4) * (|c m| * (Npsi m * Real.sqrt (Npsi m))) := by
    funext m; ring
  rw [hEq]
  exact (summable_abs_c_Npsi32 hcd hd).mul_left _

end Summable

/-! ## 3. The modes and their derivatives -/

lemma contDiff_eFam (m : ℕ) : ContDiff ℝ 3 (eFam m) := by
  show ContDiff ℝ 3 (fun θ : ℝ => Real.cos θ
    * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ))
  exact Real.contDiff_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).comp Real.contDiff_sin)

lemma hasDerivAt_eFam (m : ℕ) (θ : ℝ) : HasDerivAt (eFam m) (deriv (eFam m) θ) θ :=
  ((contDiff_eFam m).differentiable (by norm_num)).differentiableAt.hasDerivAt

lemma hasDerivAt_deriv_eFam (m : ℕ) (θ : ℝ) :
    HasDerivAt (deriv (eFam m)) (iteratedDeriv 2 (eFam m) θ) θ := by
  have h2 : ContDiff ℝ 2 (deriv (eFam m)) := (contDiff_eFam m).deriv'
  have hd : HasDerivAt (deriv (eFam m)) (deriv (deriv (eFam m)) θ) θ :=
    (h2.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hiter : iteratedDeriv 2 (eFam m) = deriv (deriv (eFam m)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rwa [hiter]

lemma contDiff_iteratedDeriv_two_eFam (m : ℕ) : ContDiff ℝ 1 (iteratedDeriv 2 (eFam m)) := by
  have h : iteratedDeriv 2 (eFam m) = deriv (deriv (eFam m)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h]
  exact (contDiff_eFam m).deriv'.deriv'

/-- `deriv tan θ = 1/cos²θ`. -/
lemma hasDerivAt_tan_real {θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := by
  have h := (Real.hasDerivAt_sin θ).div (Real.hasDerivAt_cos θ) hcos
  have htan : Real.tan = Real.sin / Real.cos := funext fun x => Real.tan_eq_sin_div_cos x
  rw [← htan] at h
  have hval : (Real.cos θ * Real.cos θ - Real.sin θ * (-Real.sin θ)) / Real.cos θ ^ 2
      = 1 / Real.cos θ ^ 2 := by
    have h1 : Real.cos θ * Real.cos θ - Real.sin θ * (-Real.sin θ) = 1 := by
      have hs := Real.sin_sq_add_cos_sq θ
      nlinarith
    rw [h1]
  rwa [hval] at h

/-- `Lzero` of a `z`-independent function, in terms of the one-variable derivatives. -/
lemma Lzero_of_one_var (g : ℝ → ℝ) {θ : ℝ} (hcos : Real.cos θ ≠ 0)
    (hg : HasDerivAt g (deriv g θ) θ) :
    Work.Elliptic.Lzero (fun _ θ' => g θ') 0 θ
      = -iteratedDeriv 2 g θ + Real.tan θ * deriv g θ + (1 / Real.cos θ ^ 2) * g θ
        - 6 * g θ := by
  have h2 : iteratedDeriv 2 g = deriv (deriv g) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h3 : deriv (fun θ' : ℝ => Real.tan θ' * g θ') θ
      = 1 / Real.cos θ ^ 2 * g θ + Real.tan θ * deriv g θ :=
    ((hasDerivAt_tan_real hcos).mul hg).deriv
  have hgoal : Work.Elliptic.Lzero (fun _ θ' => g θ') 0 θ
      = -(deriv (deriv g) θ) + deriv (fun θ' : ℝ => Real.tan θ' * g θ') θ - 6 * g θ := by
    rw [Work.Elliptic.Lzero_eq_deriv]
  rw [hgoal, h3, ← h2]
  ring

/-! ## 4. Termwise differentiation on compacts -/

/-- If `Ioo ε (π/2 - ε)` contains a point and `ε > 0`, then `ε < π/2`. -/
lemma eps_lt_pi_half_of_mem {ε θ : ℝ} (hε : 0 < ε) (hθ : θ ∈ Set.Ioo ε (Real.pi / 2 - ε)) :
    ε < Real.pi / 2 := by
  have h2 : ε < Real.pi / 2 - ε := lt_trans hθ.1 hθ.2
  linarith [Real.pi_pos]

/-- If `Ioo ε (π/2 - ε)` contains a point and `ε > 0`, then `0 < sin ε`. -/
lemma sin_pos_of_mem {ε θ : ℝ} (hε : 0 < ε) (hθ : θ ∈ Set.Ioo ε (Real.pi / 2 - ε)) :
    0 < Real.sin ε :=
  Real.sin_pos_of_pos_of_lt_pi hε (by linarith [eps_lt_pi_half_of_mem hε hθ, Real.pi_pos])

/-- Where `y` lies in `Ioo ε (π/2 - ε)` with `ε > 0`, `cos y ≥ sin ε`. -/
lemma cos_ge_sin_of_mem {ε : ℝ} (hε : 0 < ε) (y : ℝ)
    (hy : y ∈ Set.Ioo ε (Real.pi / 2 - ε)) : Real.sin ε ≤ Real.cos y := by
  have hy0 : 0 ≤ y := le_of_lt (lt_trans hε hy.1)
  have hyπ : Real.pi / 2 - ε ≤ Real.pi := by linarith [Real.pi_pos, hε]
  have h := Real.cos_le_cos_of_nonneg_of_le_pi hy0 hyπ (le_of_lt hy.2)
  rwa [Real.cos_pi_div_two_sub] at h

lemma mem_Ioo_pi_half {ε y : ℝ} (hε : 0 < ε) (hy : y ∈ Set.Ioo ε (Real.pi / 2 - ε)) :
    y ∈ Set.Ioo 0 (Real.pi / 2) :=
  ⟨lt_trans hε hy.1, by linarith [hy.2]⟩

/-- Termwise differentiation of the mode series: on `Ioo ε (π/2 - ε)`,
`d/dθ ∑_m c_m e_m(θ) = ∑_m c_m e_m'(θ)`. -/
lemma hasDerivAt_series {c : ℕ → ℝ}
    (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2))
    {ε : ℝ} (hε : 0 < ε) {θ : ℝ} (hθ : θ ∈ Set.Ioo ε (Real.pi / 2 - ε)) :
    HasDerivAt (fun y : ℝ => ∑' m : ℕ, c m * eFam m y)
      (∑' m : ℕ, c m * deriv (eFam m) θ) θ := by
  have hsin : 0 < Real.sin ε := sin_pos_of_mem hε hθ
  have hcos : ∀ y ∈ Set.Ioo ε (Real.pi / 2 - ε), Real.sin ε ≤ Real.cos y :=
    fun y hy => cos_ge_sin_of_mem hε y hy
  refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
    (t := Set.Ioo ε (Real.pi / 2 - ε))
    (u := fun m : ℕ => 100 * Npsi m / (Real.sin ε) ^ 2 * |c m|)
    (g := fun m y => c m * eFam m y) (g' := fun m y => c m * deriv (eFam m) y)
    (summable_u1 (s := Real.sin ε) hc) isOpen_Ioo isPreconnected_Ioo ?_ ?_ hθ ?_ hθ
  · intro m y hy
    exact (hasDerivAt_eFam m y).const_mul (c m)
  · intro m y hy
    rw [Real.norm_eq_abs, abs_mul]
    have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).2.1 m y (mem_Ioo_pi_half hε hy)
    have hcs := hcos y hy
    have hnum : (0 : ℝ) ≤ 100 * Npsi m := by
      have := Work.FTS.PhiStar.Series.Deleg.Npsi_pos m; linarith
    have hcospos : 0 < Real.cos y := lt_of_lt_of_le hsin hcs
    have hsq : (Real.sin ε) ^ 2 ≤ (Real.cos y) ^ 2 := by nlinarith
    have hden : (0 : ℝ) < (Real.sin ε) ^ 2 := by positivity
    have hle : 100 * Npsi m / (Real.cos y) ^ 2 ≤ 100 * Npsi m / (Real.sin ε) ^ 2 :=
      div_le_div_of_nonneg_left hnum hden hsq
    calc |c m| * |deriv (eFam m) y| ≤ |c m| * (100 * Npsi m / (Real.cos y) ^ 2) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |c m| * (100 * Npsi m / (Real.sin ε) ^ 2) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = 100 * Npsi m / (Real.sin ε) ^ 2 * |c m| := by ring
  · refine Summable.of_norm_bounded (f := fun m : ℕ => c m * eFam m θ)
      (g := fun m : ℕ => 3 * (|c m| * ((m : ℝ) + 1))) ?_ (fun m => ?_)
    · exact (summable_abs_c_one hc).mul_left 3
    · rw [Real.norm_eq_abs, abs_mul]
      have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).1 m θ (mem_Ioo_pi_half hε hθ)
      have hb' := sqrt_Npsi_le_three m
      calc |c m| * |eFam m θ| ≤ |c m| * (3 * ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (le_trans hb hb') (abs_nonneg _)
        _ = 3 * (|c m| * ((m : ℝ) + 1)) := by ring

/-- Termwise differentiation, once more: on `Ioo ε (π/2 - ε)`,
`d/dθ ∑_m c_m e_m'(θ) = ∑_m c_m e_m''(θ)`. -/
lemma hasDerivAt_series_deriv {c d : ℕ → ℝ}
    (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2))
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1)))
    (hcd : ∀ m : ℕ, c m * lam m = d m)
    {ε : ℝ} (hε : 0 < ε) {θ : ℝ} (hθ : θ ∈ Set.Ioo ε (Real.pi / 2 - ε)) :
    HasDerivAt (fun y : ℝ => ∑' m : ℕ, c m * deriv (eFam m) y)
      (∑' m : ℕ, c m * iteratedDeriv 2 (eFam m) θ) θ := by
  have hsin : 0 < Real.sin ε := sin_pos_of_mem hε hθ
  have hcos : ∀ y ∈ Set.Ioo ε (Real.pi / 2 - ε), Real.sin ε ≤ Real.cos y :=
    fun y hy => cos_ge_sin_of_mem hε y hy
  refine hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
    (t := Set.Ioo ε (Real.pi / 2 - ε))
    (u := fun m : ℕ => 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4 * |c m|)
    (g := fun m y => c m * deriv (eFam m) y)
    (g' := fun m y => c m * iteratedDeriv 2 (eFam m) y)
    (summable_u2 (s := Real.sin ε) hcd hd) isOpen_Ioo isPreconnected_Ioo ?_ ?_ hθ ?_ hθ
  · intro m y hy
    exact (hasDerivAt_deriv_eFam m y).const_mul (c m)
  · intro m y hy
    rw [Real.norm_eq_abs, abs_mul]
    have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).2.2.1 m y (mem_Ioo_pi_half hε hy)
    have hcs := hcos y hy
    have hnum : (0 : ℝ) ≤ 1000 * Npsi m * Real.sqrt (Npsi m) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (Work.FTS.PhiStar.Series.Deleg.Npsi_pos m)))
        (Real.sqrt_nonneg _)
    have hcospos : 0 < Real.cos y := lt_of_lt_of_le hsin hcs
    have h2 : (Real.sin ε) ^ 2 ≤ (Real.cos y) ^ 2 := by nlinarith
    have hsq : (Real.sin ε) ^ 4 ≤ (Real.cos y) ^ 4 := by
      have hnn : (0 : ℝ) ≤ (Real.sin ε) ^ 2 := by positivity
      have hnn' : (0 : ℝ) ≤ (Real.cos y) ^ 2 := by positivity
      have hmul := mul_le_mul h2 h2 hnn hnn'
      calc (Real.sin ε) ^ 4 = (Real.sin ε) ^ 2 * (Real.sin ε) ^ 2 := by ring
        _ ≤ (Real.cos y) ^ 2 * (Real.cos y) ^ 2 := hmul
        _ = (Real.cos y) ^ 4 := by ring
    have hden : (0 : ℝ) < (Real.sin ε) ^ 4 := by positivity
    have hle : 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos y) ^ 4
        ≤ 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4 :=
      div_le_div_of_nonneg_left hnum hden hsq
    calc |c m| * |iteratedDeriv 2 (eFam m) y|
        ≤ |c m| * (1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos y) ^ 4) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |c m| * (1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4 * |c m| := by ring
  · refine Summable.of_norm_bounded (f := fun m : ℕ => c m * deriv (eFam m) θ)
      (g := fun m : ℕ => (100 / (Real.cos θ) ^ 2) * (|c m| * Npsi m)) ?_ (fun m => ?_)
    · exact (summable_abs_c_Npsi hc).mul_left _
    · rw [Real.norm_eq_abs, abs_mul]
      have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).2.1 m θ (mem_Ioo_pi_half hε hθ)
      have hle : 100 * Npsi m / (Real.cos θ) ^ 2 = (100 / (Real.cos θ) ^ 2) * Npsi m := by ring
      calc |c m| * |deriv (eFam m) θ| ≤ |c m| * (100 * Npsi m / (Real.cos θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = (100 / (Real.cos θ) ^ 2) * (|c m| * Npsi m) := by rw [hle]; ring

/-- The second derivative series is continuous on `Ioo ε (π/2 - ε)`. -/
lemma continuousOn_series'' {c d : ℕ → ℝ}
    (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2))
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1)))
    (hcd : ∀ m : ℕ, c m * lam m = d m) {ε : ℝ} (hε : 0 < ε)
    (hε4 : ε < Real.pi / 2) :
    ContinuousOn (fun y : ℝ => ∑' m : ℕ, c m * iteratedDeriv 2 (eFam m) y)
      (Set.Ioo ε (Real.pi / 2 - ε)) := by
  have hsin : 0 < Real.sin ε :=
    Real.sin_pos_of_pos_of_lt_pi hε (by linarith [hε4, Real.pi_pos])
  have hcos : ∀ y ∈ Set.Ioo ε (Real.pi / 2 - ε), Real.sin ε ≤ Real.cos y :=
    fun y hy => cos_ge_sin_of_mem hε y hy
  refine continuousOn_tsum (f := fun m y => c m * iteratedDeriv 2 (eFam m) y)
    (u := fun m : ℕ => 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4 * |c m|)
    ?_ (summable_u2 (s := Real.sin ε) hcd hd) ?_
  · intro m
    exact (continuous_const.mul (contDiff_iteratedDeriv_two_eFam m).continuous).continuousOn
  · intro m y hy
    rw [Real.norm_eq_abs, abs_mul]
    have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).2.2.1 m y (mem_Ioo_pi_half hε hy)
    have hcs := hcos y hy
    have hnum : (0 : ℝ) ≤ 1000 * Npsi m * Real.sqrt (Npsi m) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (Work.FTS.PhiStar.Series.Deleg.Npsi_pos m)))
        (Real.sqrt_nonneg _)
    have hcospos : 0 < Real.cos y := lt_of_lt_of_le hsin hcs
    have h2 : (Real.sin ε) ^ 2 ≤ (Real.cos y) ^ 2 := by nlinarith
    have hsq : (Real.sin ε) ^ 4 ≤ (Real.cos y) ^ 4 := by
      have hnn : (0 : ℝ) ≤ (Real.sin ε) ^ 2 := by positivity
      have hnn' : (0 : ℝ) ≤ (Real.cos y) ^ 2 := by positivity
      have hmul := mul_le_mul h2 h2 hnn hnn'
      calc (Real.sin ε) ^ 4 = (Real.sin ε) ^ 2 * (Real.sin ε) ^ 2 := by ring
        _ ≤ (Real.cos y) ^ 2 * (Real.cos y) ^ 2 := hmul
        _ = (Real.cos y) ^ 4 := by ring
    have hden : (0 : ℝ) < (Real.sin ε) ^ 4 := by positivity
    have hle : 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos y) ^ 4
        ≤ 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4 :=
      div_le_div_of_nonneg_left hnum hden hsq
    calc |c m| * |iteratedDeriv 2 (eFam m) y|
        ≤ |c m| * (1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos y) ^ 4) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |c m| * (1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4) :=
          mul_le_mul_of_nonneg_left hle (abs_nonneg _)
      _ = 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.sin ε) ^ 4 * |c m| := by ring

/-! ## 5. Assembling `ContDiffOn ℝ 2` -/

/-- `HasDerivAt` data for `f` and for its derivative, plus continuity of the second derivative,
give `ContDiffOn ℝ 2`. -/
lemma contDiffOn_two_of_hasDerivAt {F A A' : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (h1 : ∀ x ∈ s, HasDerivAt F (A x) x) (h2 : ∀ x ∈ s, HasDerivAt A (A' x) x)
    (h3 : ContinuousOn A' s) : ContDiffOn ℝ 2 F s := by
  have hFdiff : DifferentiableOn ℝ F s :=
    fun x hx => (h1 x hx).differentiableAt.differentiableWithinAt
  have hAdiff : DifferentiableOn ℝ A s :=
    fun x hx => (h2 x hx).differentiableAt.differentiableWithinAt
  have hA' : ContinuousOn (derivWithin A s) s :=
    h3.congr (fun x hx => (derivWithin_of_isOpen hs hx).trans (h2 x hx).deriv)
  have hA1 : ContDiffOn ℝ 1 A s :=
    (contDiffOn_one_iff_derivWithin hs.uniqueDiffOn).2 ⟨hAdiff, hA'⟩
  have hderiv : ContDiffOn ℝ 1 (derivWithin F s) s :=
    hA1.congr (fun x hx => (derivWithin_of_isOpen hs hx).trans (h1 x hx).deriv)
  rw [show (2 : WithTop ℕ∞) = (1 : WithTop ℕ∞) + 1 from by norm_num,
    contDiffOn_succ_iff_derivWithin hs.uniqueDiffOn]
  exact ⟨hFdiff, fun h => absurd h (WithTop.natCast_ne_top 1), hderiv⟩

/-- The mode series is `C²` on `(0, π/2)`. -/
lemma contDiffOn_series {c d : ℕ → ℝ}
    (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2))
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1)))
    (hcd : ∀ m : ℕ, c m * lam m = d m) :
    ContDiffOn ℝ 2 (fun θ : ℝ => ∑' m : ℕ, c m * eFam m θ) (Set.Ioo 0 (Real.pi / 2)) := by
  refine contDiffOn_of_locally_contDiffOn (fun θ hθ => ?_)
  obtain ⟨h0, h1⟩ := hθ
  set ε : ℝ := min θ (Real.pi / 2 - θ) / 2 with hεdef
  have hpi : 0 < Real.pi / 2 - θ := by linarith [Real.pi_pos, h1]
  have hε : 0 < ε := by
    rw [hεdef]
    have h2 : (0 : ℝ) < min θ (Real.pi / 2 - θ) := lt_min h0 hpi
    linarith
  have hmem : θ ∈ Set.Ioo ε (Real.pi / 2 - ε) := by
    rw [hεdef]
    constructor
    · have h := min_le_left θ (Real.pi / 2 - θ); linarith
    · have h := min_le_right θ (Real.pi / 2 - θ); linarith
  have hε4 : ε < Real.pi / 2 := eps_lt_pi_half_of_mem hε hmem
  refine ⟨Set.Ioo ε (Real.pi / 2 - ε), isOpen_Ioo, hmem, ?_⟩
  refine (contDiffOn_two_of_hasDerivAt (s := Set.Ioo ε (Real.pi / 2 - ε)) isOpen_Ioo
    (fun x hx => hasDerivAt_series hc hε hx)
    (fun x hx => hasDerivAt_series_deriv hc hd hcd hε hx)
    (continuousOn_series'' hc hd hcd hε hε4)).mono Set.inter_subset_right

/-! ## 6. The `Lzero` identity -/

/-- Linearity of an absolutely convergent series in the four terms coming from the one-variable
form of `Lzero`. -/
lemma tsum_lincomb {a b e : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (he : Summable e)
    (t r : ℝ) :
    -(∑' m : ℕ, a m) + t * (∑' m : ℕ, b m) + r * (∑' m : ℕ, e m) - 6 * (∑' m : ℕ, e m)
      = ∑' m : ℕ, (-(a m) + t * b m + r * e m - 6 * e m) := by
  rw [← tsum_neg, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  rw [← Summable.tsum_add ha.neg (hb.mul_left t)]
  rw [← Summable.tsum_add (ha.neg.add (hb.mul_left t)) (he.mul_left r)]
  rw [← Summable.tsum_sub ((ha.neg.add (hb.mul_left t)).add (he.mul_left r)) (he.mul_left 6)]
  try rfl

/-- The `Lzero` identity of the mode series, on a compact subinterval of `(0, π/2)`. -/
lemma lzero_series {c d : ℕ → ℝ}
    (hcd : ∀ m : ℕ, c m * lam m = d m)
    (hc : Summable (fun m : ℕ => |c m| * ((m : ℝ) + 1) ^ 2))
    (hd : Summable (fun m : ℕ => |d m| * ((m : ℝ) + 1)))
    {ε : ℝ} (hε : 0 < ε) {θ : ℝ} (hθ : θ ∈ Set.Ioo ε (Real.pi / 2 - ε)) :
    Work.Elliptic.Lzero (fun _ θ' => ∑' m : ℕ, c m * eFam m θ') 0 θ
      = ∑' m : ℕ, d m * eFam m θ := by
  have hpi := mem_Ioo_pi_half hε hθ
  have hcos0 : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hpi.1], hpi.2⟩
  have hcosne : Real.cos θ ≠ 0 := ne_of_gt hcos0
  -- the two termwise differentiations
  have hF : HasDerivAt (fun y : ℝ => ∑' m : ℕ, c m * eFam m y)
      (∑' m : ℕ, c m * deriv (eFam m) θ) θ := hasDerivAt_series hc hε hθ
  have hA : HasDerivAt (fun y : ℝ => ∑' m : ℕ, c m * deriv (eFam m) y)
      (∑' m : ℕ, c m * iteratedDeriv 2 (eFam m) θ) θ := hasDerivAt_series_deriv hc hd hcd hε hθ
  have hF' : HasDerivAt (fun y : ℝ => ∑' m : ℕ, c m * eFam m y)
      (deriv (fun y : ℝ => ∑' m : ℕ, c m * eFam m y) θ) θ := by
    rw [hF.deriv]; exact hF
  -- `iteratedDeriv 2` of the series
  have hev : (fun y : ℝ => ∑' m : ℕ, c m * deriv (eFam m) y)
      =ᶠ[𝓝 θ] deriv (fun y : ℝ => ∑' m : ℕ, c m * eFam m y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
    exact ((hasDerivAt_series hc hε hy).deriv).symm
  have hiter : iteratedDeriv 2 (fun y : ℝ => ∑' m : ℕ, c m * eFam m y) θ
      = ∑' m : ℕ, c m * iteratedDeriv 2 (eFam m) θ := by
    have h2 : iteratedDeriv 2 (fun y : ℝ => ∑' m : ℕ, c m * eFam m y)
        = deriv (deriv (fun y : ℝ => ∑' m : ℕ, c m * eFam m y)) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2, ← Filter.EventuallyEq.deriv_eq hev, hA.deriv]
  -- summability of the three coefficient series at `θ`
  have hX : Summable (fun m : ℕ => c m * iteratedDeriv 2 (eFam m) θ) := by
    refine Summable.of_norm_bounded (f := fun m : ℕ => c m * iteratedDeriv 2 (eFam m) θ)
      (g := fun m : ℕ => (1000 / (Real.cos θ) ^ 4)
        * (|c m| * (Npsi m * Real.sqrt (Npsi m)))) ?_ (fun m => ?_)
    · exact (summable_abs_c_Npsi32 hcd hd).mul_left _
    · rw [Real.norm_eq_abs, abs_mul]
      have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).2.2.1 m θ hpi
      calc |c m| * |iteratedDeriv 2 (eFam m) θ|
          ≤ |c m| * (1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos θ) ^ 4) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = (1000 / (Real.cos θ) ^ 4) * (|c m| * (Npsi m * Real.sqrt (Npsi m))) := by ring
  have hY : Summable (fun m : ℕ => c m * deriv (eFam m) θ) := by
    refine Summable.of_norm_bounded (f := fun m : ℕ => c m * deriv (eFam m) θ)
      (g := fun m : ℕ => (100 / (Real.cos θ) ^ 2) * (|c m| * Npsi m)) ?_ (fun m => ?_)
    · exact (summable_abs_c_Npsi hc).mul_left _
    · rw [Real.norm_eq_abs, abs_mul]
      have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).2.1 m θ hpi
      calc |c m| * |deriv (eFam m) θ|
          ≤ |c m| * (100 * Npsi m / (Real.cos θ) ^ 2) :=
            mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = (100 / (Real.cos θ) ^ 2) * (|c m| * Npsi m) := by ring
  have hZ : Summable (fun m : ℕ => c m * eFam m θ) := by
    refine Summable.of_norm_bounded (f := fun m : ℕ => c m * eFam m θ)
      (g := fun m : ℕ => 3 * (|c m| * ((m : ℝ) + 1))) ?_ (fun m => ?_)
    · exact (summable_abs_c_one hc).mul_left 3
    · rw [Real.norm_eq_abs, abs_mul]
      have hb := (Work.FTS.PhiStar.Series.Deleg.psiAngBounds).1 m θ hpi
      calc |c m| * |eFam m θ| ≤ |c m| * (3 * ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left (le_trans hb (sqrt_Npsi_le_three m)) (abs_nonneg _)
        _ = 3 * (|c m| * ((m : ℝ) + 1)) := by ring
  calc Work.Elliptic.Lzero (fun _ θ' => ∑' m : ℕ, c m * eFam m θ') 0 θ
      = -(∑' m : ℕ, c m * iteratedDeriv 2 (eFam m) θ)
        + Real.tan θ * (∑' m : ℕ, c m * deriv (eFam m) θ)
        + (1 / Real.cos θ ^ 2) * (∑' m : ℕ, c m * eFam m θ)
        - 6 * (∑' m : ℕ, c m * eFam m θ) := by
        rw [Lzero_of_one_var (fun y : ℝ => ∑' m : ℕ, c m * eFam m y) hcosne hF']
        rw [hF.deriv, hiter]
    _ = ∑' m : ℕ, (-(c m * iteratedDeriv 2 (eFam m) θ) + Real.tan θ * (c m * deriv (eFam m) θ)
          + (1 / Real.cos θ ^ 2) * (c m * eFam m θ) - 6 * (c m * eFam m θ)) :=
        tsum_lincomb hX hY hZ (Real.tan θ) (1 / Real.cos θ ^ 2)
    _ = ∑' m : ℕ, c m * Work.Elliptic.Lzero (fun _ θ' => eFam m θ') 0 θ := by
        refine tsum_congr fun m => ?_
        rw [Lzero_of_one_var (eFam m) hcosne (hasDerivAt_eFam m θ)]
        ring
    _ = ∑' m : ℕ, d m * eFam m θ := by
        refine tsum_congr fun m => ?_
        rw [Work.FTS.PhiStar.Gegenbauer.eFam_Lzero m hcosne 0, ← hcd m]
        ring

end Work.FTS.PhiStar.FlatWAux.MomentChiaAux
