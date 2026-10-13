/-
Copyright: work module for the Elgindi finite-time singularity project.

# Smooth, compactly supported functions lie in `ℋ^k ∩ 𝒲^{l,∞}`

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkAux
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.pth_integral
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.BoxBounds
import Submission.Work.Spaces.SinMinBounds
import Submission.Work.Spaces.SupportZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## Smoothness of the iterated operators on the neighbourhood `U` -/

theorem SmoothNbhd.pz {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) : SmoothNbhd (pz f) :=
  contDiffOn_uncurry_pz isOpen_U h

theorem SmoothNbhd.pth {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) : SmoothNbhd (pth f) :=
  contDiffOn_uncurry_pth isOpen_U h

theorem smoothNbhd_pzIter {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ∀ k : ℕ, SmoothNbhd (pzIter k f)
  | 0 => h
  | k + 1 => (smoothNbhd_pzIter h k).pz

theorem smoothNbhd_DthIter {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ∀ k : ℕ, SmoothNbhd (DthIter k f)
  | 0 => h
  | k + 1 => SmoothNbhd.Dth (smoothNbhd_DthIter h k)

theorem smoothNbhd_DzIter {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ∀ k : ℕ, SmoothNbhd (DzIter k f)
  | 0 => h
  | k + 1 => SmoothNbhd.Dz (smoothNbhd_DzIter h k)

theorem smoothNbhd_mixed {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) (j i : ℕ) :
    SmoothNbhd (mixed j i f) :=
  smoothNbhd_DzIter (smoothNbhd_DthIter h i) j

theorem smoothNbhd_pzIter_DthIter {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) (k j : ℕ) :
    SmoothNbhd (pzIter k (DthIter j f)) :=
  smoothNbhd_pzIter (smoothNbhd_DthIter h j) k

/-! ## Vanishing at `z = 0` -/

/-- `D_z G` vanishes at `z = 0`. -/
theorem Dz_apply_zero (G : ℝ → ℝ → ℝ) (θ : ℝ) : Dz G 0 θ = 0 := by
  simp [Dz]

/-- `D_z^j G` vanishes at `z = 0` for `j ≥ 1`. -/
theorem DzIter_apply_zero (G : ℝ → ℝ → ℝ) (j : ℕ) (θ : ℝ) : DzIter (j + 1) G 0 θ = 0 :=
  Dz_apply_zero (DzIter j G) θ

/-- The derivative in `z` of `D_z G` at the origin equals `∂_z G` evaluated there. -/
theorem pz_Dz_eq (G : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : DifferentiableAt ℝ (fun t => pz G t θ) z) :
    pz (Dz G) z θ = pz G z θ + z * pz (pz G) z θ := by
  have h1 : HasDerivAt (fun t : ℝ => t * pz G t θ)
      (1 * pz G z θ + z * pz (pz G) z θ) z :=
    (hasDerivAt_id z).mul h.hasDerivAt
  rw [show pz (Dz G) z θ = deriv (fun t : ℝ => t * pz G t θ) z from rfl, h1.deriv]
  ring

/-- `∂_z (D_z^j G)(0,θ) = ∂_z G(0,θ)` for every `j`. -/
theorem pz_DzIter_apply_zero (G : ℝ → ℝ → ℝ) (hG : ContDiffOn ℝ ⊤ (Function.uncurry G) U)
    {θ : ℝ} (hθ : θ ∈ Iθ) (j : ℕ) : pz (DzIter j G) 0 θ = pz G 0 θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hsmj : SmoothNbhd (DzIter j G) := smoothNbhd_DzIter hG j
    have hsmj1 : SmoothNbhd (pz (DzIter j G)) := hsmj.pz
    have hd : DifferentiableAt ℝ (fun t => pz (DzIter j G) t θ) 0 := by
      have h2 : ContDiffAt ℝ ⊤ (Function.uncurry (pz (DzIter j G))) (0, θ) :=
        hsmj1.contDiffAt (isOpen_U.mem_nhds (mem_U_of_dom zero_mem_Iz hθ))
      exact differentiableAt_curry_left (h2.differentiableAt (by norm_num))
    rw [DzIter_succ, pz_Dz_eq _ hd, ih]
    ring

/-! ## Vanishing on the angular boundary -/

/-- If `G` vanishes at `θ = 0` for every `z`, so do all its `z`-derivatives. -/
theorem pzIter_apply_zero_of (G : ℝ → ℝ → ℝ) (hG : ∀ z : ℝ, G z 0 = 0) (k : ℕ) :
    ∀ z : ℝ, pzIter k G z 0 = 0 := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    intro z
    rw [pzIter_succ, pz]
    have hev : (fun z' => pzIter k G z' 0) = fun _ => (0 : ℝ) := funext ih
    rw [hev, deriv_const]

/-- If `G` vanishes at `θ = π/2` for every `z`, so do all its `z`-derivatives. -/
theorem pzIter_apply_pi_half_of (G : ℝ → ℝ → ℝ) (hG : ∀ z : ℝ, G z (π / 2) = 0) (k : ℕ) :
    ∀ z : ℝ, pzIter k G z (π / 2) = 0 := by
  induction k with
  | zero => exact hG
  | succ k ih =>
    intro z
    rw [pzIter_succ, pz]
    have hev : (fun z' => pzIter k G z' (π / 2)) = fun _ => (0 : ℝ) := funext ih
    rw [hev, deriv_const]

/-- If `G` vanishes at `θ = 0` for every `z`, so do all its `D_z`-derivatives. -/
theorem DzIter_apply_zero_of (G : ℝ → ℝ → ℝ) (hG : ∀ z : ℝ, G z 0 = 0) (j : ℕ) :
    ∀ z : ℝ, DzIter j G z 0 = 0 := by
  induction j with
  | zero => exact hG
  | succ j ih =>
    intro z
    rw [DzIter_succ, Dz]
    have hp : pz (DzIter j G) z 0 = 0 := by
      rw [pz]
      have hev : (fun z' => DzIter j G z' 0) = fun _ => (0 : ℝ) := funext ih
      rw [hev, deriv_const]
    rw [hp, mul_zero]

/-- If `G` vanishes at `θ = π/2` for every `z`, so do all its `D_z`-derivatives. -/
theorem DzIter_apply_pi_half_of (G : ℝ → ℝ → ℝ) (hG : ∀ z : ℝ, G z (π / 2) = 0) (j : ℕ) :
    ∀ z : ℝ, DzIter j G z (π / 2) = 0 := by
  induction j with
  | zero => exact hG
  | succ j ih =>
    intro z
    rw [DzIter_succ, Dz]
    have hp : pz (DzIter j G) z (π / 2) = 0 := by
      rw [pz]
      have hev : (fun z' => DzIter j G z' (π / 2)) = fun _ => (0 : ℝ) := funext ih
      rw [hev, deriv_const]
    rw [hp, mul_zero]

/-- `D_θ^i f` vanishes identically at `z = 0`, at interior angles. -/
theorem DthIter_apply_zero_interior (f : ℝ → ℝ → ℝ) (hz0 : ∀ θ ∈ Iθ, f 0 θ = 0) :
    ∀ i : ℕ, ∀ θ ∈ Set.Ioo 0 (π / 2), DthIter i f 0 θ = 0 := by
  intro i
  induction i with
  | zero =>
    intro θ hθ
    exact hz0 θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  | succ i ih =>
    intro θ hθ
    rw [DthIter_succ, Dth, pth]
    have hev : (fun θ' => DthIter i f 0 θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact ih θ' hθ'
    rw [hev.deriv_eq, deriv_const, mul_zero]

/-- `D_θ^i f` vanishes at `z = 0` on the whole angular interval, for `i ≥ 1`. -/
theorem DthIter_apply_zero_Iθ (f : ℝ → ℝ → ℝ) (hz0 : ∀ θ ∈ Iθ, f 0 θ = 0) (i : ℕ)
    {θ : ℝ} (hθ : θ ∈ Iθ) : DthIter (i + 1) f 0 θ = 0 := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0, DthIter_succ, Dth]
    simp
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2
    · rw [h2]
      exact DthIter_apply_pi_half f i 0
    · exact DthIter_apply_zero_interior f hz0 (i + 1) θ ⟨h0, h2⟩

/-- The `z`-derivative of `D_θ G` is `sin(2θ)` times the `z`-derivative of `∂_θ G`. -/
theorem pz_Dth_eq (G : ℝ → ℝ → ℝ) (z θ : ℝ) :
    pz (Dth G) z θ = Real.sin (2 * θ) * pz (pth G) z θ := by
  show deriv (fun t => Dth G t θ) z = Real.sin (2 * θ) * deriv (fun t => pth G t θ) z
  rw [show (fun t => Dth G t θ) = fun t => Real.sin (2 * θ) * pth G t θ from rfl,
    deriv_const_mul_field]

/-- `∂_z D_θ^{i+1} f` vanishes at `z = 0`, at every interior angle. -/
theorem pz_DthIter_interior (f : ℝ → ℝ → ℝ) (hsm : SmoothNbhd f)
    (hpz : ∀ θ ∈ Iθ, pz f 0 θ = 0) :
    ∀ i : ℕ, ∀ θ ∈ Set.Ioo 0 (π / 2), pz (DthIter (i + 1) f) 0 θ = 0 := by
  intro i
  induction i with
  | zero =>
    intro θ hθ
    have hmem : (0, θ) ∈ U := mem_U (by norm_num) (by linarith [hθ.1]) (by linarith [hθ.2])
    have h2 : ContDiffAt ℝ 2 (Function.uncurry f) (0, θ) :=
      (hsm.contDiffAt (isOpen_U.mem_nhds hmem)).of_le (by norm_num)
    have hp2 : pz (pth f) 0 θ = pth (pz f) 0 θ := pz_pth_comm h2
    rw [DthIter_succ, pz_Dth_eq]
    simp only [DthIter_zero]
    rw [hp2, pth]
    have hev : (fun θ' => pz f 0 θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact hpz θ' ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩
    rw [hev.deriv_eq, deriv_const, mul_zero]
  | succ i ih =>
    intro θ hθ
    have hmem : (0, θ) ∈ U := mem_U (by norm_num) (by linarith [hθ.1]) (by linarith [hθ.2])
    have hsmD : SmoothNbhd (DthIter (i + 1) f) := smoothNbhd_DthIter hsm (i + 1)
    have h2 : ContDiffAt ℝ 2 (Function.uncurry (DthIter (i + 1) f)) (0, θ) :=
      (hsmD.contDiffAt (isOpen_U.mem_nhds hmem)).of_le (by norm_num)
    have hp2 : pz (pth (DthIter (i + 1) f)) 0 θ = pth (pz (DthIter (i + 1) f)) 0 θ :=
      pz_pth_comm h2
    rw [DthIter_succ, pz_Dth_eq, hp2, pth]
    have hev : (fun θ' => pz (DthIter (i + 1) f) 0 θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
      exact ih θ' hθ'
    rw [hev.deriv_eq, deriv_const, mul_zero]

/-- `∂_z D_θ^{i+1} f` vanishes at `z = 0` on the whole angular interval. -/
theorem pz_DthIter_Iθ (f : ℝ → ℝ → ℝ) (hsm : SmoothNbhd f)
    (hpz : ∀ θ ∈ Iθ, pz f 0 θ = 0) (i : ℕ)
    {θ : ℝ} (hθ : θ ∈ Iθ) : pz (DthIter (i + 1) f) 0 θ = 0 := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0, DthIter_succ, pz_Dth_eq]
    simp
  · rcases eq_or_lt_of_le hθ.2 with h2 | h2
    · rw [h2, DthIter_succ, pz_Dth_eq]
      have hπ2 : Real.sin (2 * (π / 2)) = 0 := by
        rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
      rw [hπ2, zero_mul]
    · exact pz_DthIter_interior f hsm hpz i θ ⟨h0, h2⟩


/-! ## Absorbing the radial weight `w` into a `z²` bound -/

/-- Absorbing `w` into a `z²` bound. -/
theorem mul_w_le_of_bound {G : ℝ → ℝ → ℝ} {B z θ : ℝ} (hB : 0 ≤ B) (hz : 0 ≤ z)
    (hθ : θ ∈ Iθ) (h : |G z θ| ≤ B * (z ^ 2 * min θ (π / 2 - θ))) :
    |G z θ| * w z ≤ B * min θ (π / 2 - θ) * (1 + z) ^ 2 := by
  rcases eq_or_ne z 0 with hz0 | hz0
  · subst hz0
    have hw0 : w 0 = 0 := by norm_num [w]
    rw [hw0, mul_zero, show ((1 : ℝ) + 0) ^ 2 = 1 by norm_num, mul_one]
    exact mul_nonneg hB (le_min hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  · have hw : w z = (1 + z) ^ 2 / z ^ 2 := rfl
    have hz2 : (0 : ℝ) < z ^ 2 := by positivity
    have hw0 : 0 ≤ w z := by rw [hw]; positivity
    calc |G z θ| * w z ≤ (B * (z ^ 2 * min θ (π / 2 - θ))) * w z :=
          mul_le_mul_of_nonneg_right h hw0
      _ = B * min θ (π / 2 - θ) * (1 + z) ^ 2 * (z ^ 2 / z ^ 2) := by rw [hw]; ring
      _ = B * min θ (π / 2 - θ) * (1 + z) ^ 2 := by
          rw [div_self (ne_of_gt hz2), mul_one]

theorem min_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ min θ (π / 2 - θ) :=
  le_min hθ.1 (by linarith [hθ.2, Real.pi_pos])

/-! ## Vanishing above `R` for the iterated operators -/

/-- A function vanishing above `R` has all its `z`-iterates vanishing above `R`. -/
theorem pzIter_eq_zero_of_gt (f : ℝ → ℝ → ℝ) (R : ℝ)
    (h : ∀ z θ : ℝ, R < z → f z θ = 0) :
    ∀ k : ℕ, ∀ z θ : ℝ, R < z → pzIter k f z θ = 0 := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro z θ hz
    rw [pzIter_succ, pz]
    have hev : (fun z' => pzIter k f z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact ih z' θ hz'
    rw [hev.deriv_eq, deriv_const]

/-- A function vanishing above `R` has all its `D_θ`-iterates vanishing above `R`. -/
theorem DthIter_eq_zero_of_gt (f : ℝ → ℝ → ℝ) (R : ℝ)
    (h : ∀ z θ : ℝ, R < z → f z θ = 0) :
    ∀ k : ℕ, ∀ z θ : ℝ, R < z → DthIter k f z θ = 0 := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro z θ hz
    rw [DthIter_succ, Dth]
    have hp : pth (DthIter k f) z θ = 0 := by
      rw [pth]
      have hev : (fun θ' => DthIter k f z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
        filter_upwards with θ'
        exact ih z θ' hz
      rw [hev.deriv_eq, deriv_const]
    rw [hp, mul_zero]

/-- A function vanishing above `R` has all its `D_z`-iterates vanishing above `R`. -/
theorem DzIter_eq_zero_of_gt (f : ℝ → ℝ → ℝ) (R : ℝ)
    (h : ∀ z θ : ℝ, R < z → f z θ = 0) :
    ∀ k : ℕ, ∀ z θ : ℝ, R < z → DzIter k f z θ = 0 := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro z θ hz
    rw [DzIter_succ, Dz]
    have hp : pz (DzIter k f) z θ = 0 := by
      rw [pz]
      have hev : (fun z' => DzIter k f z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz'
      rw [hev.deriv_eq, deriv_const]
    rw [hp, mul_zero]

/-- A function vanishing above `R` has all its mixed derivatives vanishing above `R`. -/
theorem mixed_eq_zero_of_gt (f : ℝ → ℝ → ℝ) (R : ℝ)
    (h : ∀ z θ : ℝ, R < z → f z θ = 0) :
    ∀ j i : ℕ, ∀ z θ : ℝ, R < z → mixed j i f z θ = 0 :=
  fun j i => DzIter_eq_zero_of_gt (DthIter i f) R (DthIter_eq_zero_of_gt f R h i) j


/-! ## The weighted pointwise bounds -/

theorem sin_two_nonneg_of_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ Real.sin (2 * θ) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith [hθ.1, hθ.2]

/-- The weighted `D_z`-term is bounded by `Bs * (1+R)² K1` on the box. -/
theorem pz_term_bound {Bs K1 R : ℝ} {i : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hBsnn : 0 ≤ Bs) (hK1pos : 0 < K1) (hz : z ∈ Set.Icc 0 R) (hθ : θ ∈ Iθ)
    (hb1 : |DzIter i f z θ| ≤ Bs * (z ^ 2 * min θ (π / 2 - θ)))
    (hK1 : min θ (π / 2 - θ) * (Real.sin (2 * θ)) ^ (-(eta / 2)) ≤ K1) :
    |DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| ≤ Bs * ((1 + R) ^ 2 * K1) := by
  have hsin0 := sin_two_nonneg_of_Iθ hθ
  rcases eq_or_lt_of_le hsin0 with hsin | hsin
  · have hden : (Real.sin (2 * θ)) ^ (eta / 2) = 0 := by
      rw [← hsin, Real.zero_rpow (by norm_num [eta])]
    rw [hden]
    simp only [div_zero, mul_zero, abs_zero]
    exact mul_nonneg hBsnn (mul_nonneg (sq_nonneg (1 + R)) (le_of_lt hK1pos))
  · have hs0 : 0 ≤ Real.sin (2 * θ) := le_of_lt hsin
    have hrw : w z / (Real.sin (2 * θ)) ^ (eta / 2)
        = w z * (Real.sin (2 * θ)) ^ (-(eta / 2)) := by
      rw [Real.rpow_neg hs0, div_eq_mul_inv]
    have hwz : 0 ≤ w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(eta / 2)) := Real.rpow_nonneg hs0 _
    have habs : |DzIter i f z θ * (w z * (Real.sin (2 * θ)) ^ (-(eta / 2)))|
        = |DzIter i f z θ| * (w z * (Real.sin (2 * θ)) ^ (-(eta / 2))) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hwz, abs_of_nonneg h2]
    rw [hrw, habs]
    have h1 : |DzIter i f z θ| * w z ≤ Bs * min θ (π / 2 - θ) * (1 + z) ^ 2 :=
      mul_w_le_of_bound hBsnn hz.1 hθ hb1
    have h4 : 0 ≤ min θ (π / 2 - θ) * (Real.sin (2 * θ)) ^ (-(eta / 2)) :=
      mul_nonneg (min_nonneg_of_mem_Iθ hθ) h2
    have h5 : (1 + z) ^ 2 ≤ (1 + R) ^ 2 := by nlinarith [hz.1, hz.2]
    have hstep : (1 + z) ^ 2 * (min θ (π / 2 - θ) * (Real.sin (2 * θ)) ^ (-(eta / 2)))
        ≤ (1 + R) ^ 2 * K1 := mul_le_mul h5 hK1 h4 (sq_nonneg _)
    calc |DzIter i f z θ| * (w z * (Real.sin (2 * θ)) ^ (-(eta / 2)))
        = (|DzIter i f z θ| * w z) * (Real.sin (2 * θ)) ^ (-(eta / 2)) := by ring
      _ ≤ (Bs * min θ (π / 2 - θ) * (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (-(eta / 2)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = Bs * ((1 + z) ^ 2 * (min θ (π / 2 - θ) * (Real.sin (2 * θ)) ^ (-(eta / 2)))) := by
          ring
      _ ≤ Bs * ((1 + R) ^ 2 * K1) := mul_le_mul_of_nonneg_left hstep hBsnn

/-- The weighted mixed term is bounded by `Cs * (1+R)² K2` on the box. -/
theorem mixed_term_bound {α Cs K2 R : ℝ} {j i : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hα : 0 < α) (hCnn : 0 ≤ Cs) (hK2pos : 0 < K2) (hz : z ∈ Set.Icc 0 R) (hθ : θ ∈ Iθ)
    (hb1 : |mixed j i f z θ| ≤ Cs * (z ^ 2 * min θ (π / 2 - θ)))
    (hK2 : min θ (π / 2 - θ) * (Real.sin (2 * θ)) ^ (-(gam α / 2)) ≤ K2) :
    |mixed j i f z θ * Wt α z θ| ≤ Cs * ((1 + R) ^ 2 * K2) := by
  have hsin0 := sin_two_nonneg_of_Iθ hθ
  rw [Wt, wTheta]
  rcases eq_or_lt_of_le hsin0 with hsin | hsin
  · have hden : (Real.sin (2 * θ)) ^ (-(gam α / 2)) = 0 := by
      rw [← hsin]
      exact Real.zero_rpow (by have := gam_pos hα; intro hc; linarith)
    rw [hden]
    simp only [mul_zero, abs_mul, abs_zero, mul_zero]
    exact mul_nonneg hCnn (mul_nonneg (sq_nonneg (1 + R)) (le_of_lt hK2pos))
  · have hs0 : 0 ≤ Real.sin (2 * θ) := le_of_lt hsin
    have hwz : 0 ≤ w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(gam α / 2)) := Real.rpow_nonneg hs0 _
    have habs : |mixed j i f z θ * (w z * (Real.sin (2 * θ)) ^ (-(gam α / 2)))|
        = |mixed j i f z θ| * (w z * (Real.sin (2 * θ)) ^ (-(gam α / 2))) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hwz, abs_of_nonneg h2]
    rw [habs]
    have h1 : |mixed j i f z θ| * w z ≤ Cs * min θ (π / 2 - θ) * (1 + z) ^ 2 :=
      mul_w_le_of_bound hCnn hz.1 hθ hb1
    have h4 : 0 ≤ min θ (π / 2 - θ) * (Real.sin (2 * θ)) ^ (-(gam α / 2)) :=
      mul_nonneg (min_nonneg_of_mem_Iθ hθ) h2
    have h5 : (1 + z) ^ 2 ≤ (1 + R) ^ 2 := by nlinarith [hz.1, hz.2]
    have hstep : (1 + z) ^ 2 * (min θ (π / 2 - θ) * (Real.sin (2 * θ)) ^ (-(gam α / 2)))
        ≤ (1 + R) ^ 2 * K2 := mul_le_mul h5 hK2 h4 (sq_nonneg _)
    calc |mixed j i f z θ| * (w z * (Real.sin (2 * θ)) ^ (-(gam α / 2)))
        = (|mixed j i f z θ| * w z) * (Real.sin (2 * θ)) ^ (-(gam α / 2)) := by ring
      _ ≤ (Cs * min θ (π / 2 - θ) * (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (-(gam α / 2)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = Cs * ((1 + z) ^ 2 * (min θ (π / 2 - θ) * (Real.sin (2 * θ)) ^ (-(gam α / 2)))) := by
          ring
      _ ≤ Cs * ((1 + R) ^ 2 * K2) := mul_le_mul_of_nonneg_left hstep hCnn

/-! ## The pointwise bound for `HkIntegrand` -/

/-- On the box `[0,R] × [0,π/2]` the integrand of the `ℋ^k`-norm is bounded. -/
theorem HkIntegrand_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : ℝ → ℝ → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hsm : SmoothNbhd f)
    (hf_gt : ∀ z θ : ℝ, R < z → f z θ = 0)
    (hvan : VanishTheta f) (hz0 : ∀ θ ∈ Iθ, f 0 θ = 0 ∧ pz f 0 θ = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Iz, ∀ θ ∈ Iθ, HkIntegrand α k f z θ ≤ M := by
  have hDzIter_gt := DzIter_eq_zero_of_gt f R hf_gt
  have hmixed_gt := mixed_eq_zero_of_gt f R hf_gt
  have hz0f : ∀ θ ∈ Iθ, f 0 θ = 0 := fun θ hθ => (hz0 θ hθ).1
  have hz0pz : ∀ θ ∈ Iθ, pz f 0 θ = 0 := fun θ hθ => (hz0 θ hθ).2
  have hv0 : ∀ z : ℝ, f z 0 = 0 := hvan.1
  have hvs : ∀ z : ℝ, f z (π / 2) = 0 := hvan.2
  obtain ⟨K1, hK1pos, hK1⟩ := SinMinBounds (eta / 2) (by norm_num [eta]) (by norm_num [eta])
  obtain ⟨K2, hK2pos, hK2⟩ := SinMinBounds (gam α / 2) (by linarith [gam_pos hα])
    (by rw [gam]; linarith)
  have hbddDz : ∀ i, BddAbove (boxSet R (pth (pz (pz (DzIter i f))))) := fun i =>
    bddAbove_boxSup_of_continuousOn (continuousOn_box_of_contDiffOn
      ((smoothNbhd_DzIter hsm i).pz.pz.pth))
  have hbddMix : ∀ j i, BddAbove (boxSet R (pth (pz (pz (mixed j i f))))) := fun j i =>
    bddAbove_boxSup_of_continuousOn (continuousOn_box_of_contDiffOn
      ((smoothNbhd_mixed hsm j i).pz.pz.pth))
  let Bs : ℝ := ∑ i ∈ Finset.range (k + 1), boxSup R (pth (pz (pz (DzIter i f))))
  let Cs : ℝ := ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then boxSup R (pth (pz (pz (mixed j i f)))) else 0
  have hBsnn : 0 ≤ Bs := Finset.sum_nonneg fun i _ => boxSup_nonneg hR (hbddDz i)
  have hCsnn : 0 ≤ Cs := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos h]; exact boxSup_nonneg hR (hbddMix j i)
    · rw [if_neg h]
  have hA : ∀ i, ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Iθ,
      |DzIter i f z θ| ≤ boxSup R (pth (pz (pz (DzIter i f)))) * z ^ 2 * min θ (π / 2 - θ) := by
    intro i z hz θ hθ
    refine BoxSqBound (DzIter i f) R hR (smoothNbhd_DzIter hsm i) ?_ ?_ ?_ ?_ z hz θ hθ
    · intro θ' hθ'
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact hz0f θ' hθ'
      · obtain ⟨j', rfl⟩ : ∃ j', i = j' + 1 := ⟨i - 1, by omega⟩
        exact DzIter_apply_zero f j' θ'
    · intro θ' hθ'
      rw [pz_DzIter_apply_zero f hsm hθ' i]
      exact hz0pz θ' hθ'
    · intro z' _
      exact DzIter_apply_zero_of f hv0 i z'
    · intro z' _
      exact DzIter_apply_pi_half_of f hvs i z'
  have hB : ∀ j i, 1 ≤ i → i + j ≤ k → ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Iθ,
      |mixed j i f z θ| ≤ boxSup R (pth (pz (pz (mixed j i f)))) * z ^ 2 * min θ (π / 2 - θ) := by
    intro j i hi hij z hz θ hθ
    refine BoxSqBound (mixed j i f) R hR (smoothNbhd_mixed hsm j i) ?_ ?_ ?_ ?_ z hz θ hθ
    · intro θ' hθ'
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        show DthIter (i' + 1) f 0 θ' = 0
        exact DthIter_apply_zero_Iθ f hz0f i' hθ'
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        show DzIter (j' + 1) (DthIter i f) 0 θ' = 0
        exact DzIter_apply_zero (DthIter i f) j' θ'
    · intro θ' hθ'
      show pz (DzIter j (DthIter i f)) 0 θ' = 0
      rw [pz_DzIter_apply_zero (DthIter i f) (smoothNbhd_DthIter hsm i) hθ' j]
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      exact pz_DthIter_Iθ f hsm hz0pz i' hθ'
    · intro z' _
      show DzIter j (DthIter i f) z' 0 = 0
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      exact DzIter_apply_zero_of (DthIter (i' + 1) f) (fun z => DthIter_apply_zero f i' z) j z'
    · intro z' _
      show DzIter j (DthIter i f) z' (π / 2) = 0
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      exact DzIter_apply_pi_half_of (DthIter (i' + 1) f) (fun z => DthIter_apply_pi_half f i' z) j z'
  have hterm1 : ∀ i, i ≤ k → ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Iθ,
      (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        ≤ ((1 + R) ^ 2 * K1 * Bs) ^ 2 := by
    intro i hi z hz θ hθ
    have hBs : boxSup R (pth (pz (pz (DzIter i f)))) ≤ Bs := by
      refine Finset.single_le_sum (f := fun a => boxSup R (pth (pz (pz (DzIter a f))))) ?_
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      intro a _
      exact boxSup_nonneg hR (hbddDz a)
    have hb1 : |DzIter i f z θ| ≤ Bs * (z ^ 2 * min θ (π / 2 - θ)) := by
      have := hA i z hz θ hθ
      rw [mul_assoc] at this
      exact le_trans this (mul_le_mul_of_nonneg_right hBs
        (mul_nonneg (sq_nonneg z) (min_nonneg_of_mem_Iθ hθ)))
    have hbnd := pz_term_bound hBsnn hK1pos hz hθ hb1 (hK1 θ hθ)
    have hbnd' : |DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|
        ≤ (1 + R) ^ 2 * K1 * Bs := le_trans hbnd (le_of_eq (by ring))
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hbnd' 2
  have hterm2 : ∀ i j, 1 ≤ i → i + j ≤ k → ∀ z ∈ Set.Icc 0 R, ∀ θ ∈ Iθ,
      (mixed j i f z θ * Wt α z θ) ^ 2 ≤ ((1 + R) ^ 2 * K2 * Cs) ^ 2 := by
    intro i j hi1 hij z hz θ hθ
    have hCs : boxSup R (pth (pz (pz (mixed j i f)))) ≤ Cs := by
      have hif : (if 1 ≤ i ∧ i + j ≤ k then boxSup R (pth (pz (pz (mixed j i f)))) else 0)
          = boxSup R (pth (pz (pz (mixed j i f)))) := if_pos ⟨hi1, hij⟩
      rw [← hif]
      have hinner : (if 1 ≤ i ∧ i + j ≤ k then boxSup R (pth (pz (pz (mixed j i f)))) else 0)
          ≤ ∑ b ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + b ≤ k then boxSup R (pth (pz (pz (mixed b i f)))) else 0) := by
        refine Finset.single_le_sum
          (f := fun b => if 1 ≤ i ∧ i + b ≤ k then boxSup R (pth (pz (pz (mixed b i f)))) else 0)
          ?_ (Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega)))
        intro b _
        by_cases h : 1 ≤ i ∧ i + b ≤ k
        · rw [if_pos h]; exact boxSup_nonneg hR (hbddMix b i)
        · rw [if_neg h]
      refine le_trans hinner ?_
      refine Finset.single_le_sum
        (f := fun a => ∑ b ∈ Finset.range (k + 1),
          (if 1 ≤ a ∧ a + b ≤ k then boxSup R (pth (pz (pz (mixed b a f)))) else 0))
        ?_ (Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega)))
      intro a _
      refine Finset.sum_nonneg fun b _ => ?_
      by_cases h : 1 ≤ a ∧ a + b ≤ k
      · rw [if_pos h]; exact boxSup_nonneg hR (hbddMix b a)
      · rw [if_neg h]
    have hb1 : |mixed j i f z θ| ≤ Cs * (z ^ 2 * min θ (π / 2 - θ)) := by
      have := hB j i hi1 hij z hz θ hθ
      rw [mul_assoc] at this
      exact le_trans this (mul_le_mul_of_nonneg_right hCs
        (mul_nonneg (sq_nonneg z) (min_nonneg_of_mem_Iθ hθ)))
    have hbnd := mixed_term_bound hα hCsnn hK2pos hz hθ hb1 (hK2 θ hθ)
    have hbnd' : |mixed j i f z θ * Wt α z θ| ≤ (1 + R) ^ 2 * K2 * Cs :=
      le_trans hbnd (le_of_eq (by ring))
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hbnd' 2
  refine ⟨(k + 1) * ((1 + R) ^ 2 * K1 * Bs) ^ 2
      + (k + 1) * (k + 1) * ((1 + R) ^ 2 * K2 * Cs) ^ 2, by positivity, fun z hz θ hθ => ?_⟩
  rw [HkIntegrand]
  rcases lt_or_ge R z with hzR | hzR
  · have h1 : (∑ i ∈ Finset.range (k + 1),
        (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hDzIter_gt i z θ hzR]; ring
    have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (mixed j i f z θ * Wt α z θ) ^ 2 else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        by_cases h : 1 ≤ i ∧ i + j ≤ k
        · rw [if_pos h, hmixed_gt j i z θ hzR]; ring
        · rw [if_neg h]
    rw [h1, h2, add_zero]
    positivity
  · refine add_le_add ?_ ?_
    · calc (∑ i ∈ Finset.range (k + 1),
            (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
          ≤ ∑ i ∈ Finset.range (k + 1), ((1 + R) ^ 2 * K1 * Bs) ^ 2 :=
            Finset.sum_le_sum fun i hi =>
              hterm1 i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) z ⟨hz, hzR⟩ θ hθ
        _ = (k + 1) * ((1 + R) ^ 2 * K1 * Bs) ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    · calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
          ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              ((1 + R) ^ 2 * K2 * Cs) ^ 2 := by
            refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
            by_cases h : 1 ≤ i ∧ i + j ≤ k
            · rw [if_pos h]
              exact hterm2 i j h.1 h.2 z ⟨hz, hzR⟩ θ hθ
            · rw [if_neg h]; exact sq_nonneg _
        _ = (k + 1) * (k + 1) * ((1 + R) ^ 2 * K2 * Cs) ^ 2 := by
            rw [Finset.sum_congr rfl (fun i _ => by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul])]
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring


/-! ## Membership in `𝒲^{l,∞}` -/

/-- The weighted angular term is bounded by `B * (K3/α)`. -/
theorem pzDth_weighted_bound {F : ℝ → ℝ → ℝ} {α K3 B z θ : ℝ} (hα : 0 < α) (hK3nn : 0 ≤ K3)
    (hK3 : min θ (π / 2 - θ) * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ K3)
    (hθ : θ ∈ Iθ) (hBnn : 0 ≤ B) (hF : |F z θ| ≤ B * min θ (π / 2 - θ)) :
    |F z θ * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))| ≤ B * (K3 / α) := by
  have hsin0 := sin_two_nonneg_of_Iθ hθ
  have hspos : 0 < α + Real.sin (2 * θ) := by linarith [hsin0, hα]
  have hr0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) := Real.rpow_nonneg hsin0 _
  have hdiv0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
    div_nonneg hr0 (le_of_lt hspos)
  rw [abs_mul, abs_of_nonneg hdiv0]
  have h1 : |F z θ| * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ B * K3 := by
    calc |F z θ| * (Real.sin (2 * θ)) ^ (-(α / 5))
        ≤ (B * min θ (π / 2 - θ)) * (Real.sin (2 * θ)) ^ (-(α / 5)) :=
          mul_le_mul_of_nonneg_right hF hr0
      _ = B * (min θ (π / 2 - θ) * (Real.sin (2 * θ)) ^ (-(α / 5))) := by ring
      _ ≤ B * K3 := mul_le_mul_of_nonneg_left hK3 hBnn
  have h2 : |F z θ| * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      = (|F z θ| * (Real.sin (2 * θ)) ^ (-(α / 5))) / (α + Real.sin (2 * θ)) := by ring
  rw [h2]
  calc (|F z θ| * (Real.sin (2 * θ)) ^ (-(α / 5))) / (α + Real.sin (2 * θ))
      ≤ (B * K3) / (α + Real.sin (2 * θ)) :=
        div_le_div_of_nonneg_right h1 (le_of_lt hspos)
    _ ≤ (B * K3) / α :=
        div_le_div_of_nonneg_left (mul_nonneg hBnn hK3nn) hα (by linarith)
    _ = B * (K3 / α) := by ring

/-- Membership of a smooth compactly supported function in `𝒲^{l,∞}`. -/
theorem WlInfSmoothCompact (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (l : ℕ) (f : ℝ → ℝ → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hsm : SmoothNbhd f) (hf_gt : ∀ z θ : ℝ, R < z → f z θ = 0)
    (hvan : VanishTheta f) :
    WlInfMem α l f ∧ ∃ M : ℝ, WlInf α l f ≤ M := by
  have hpzIter_gt := pzIter_eq_zero_of_gt f R hf_gt
  obtain ⟨K3, hK3pos, hK3⟩ := SinMinBounds (α / 5) (by linarith) (by linarith)
  have hbddPz : ∀ k, BddAbove (boxSet R (pzIter k f)) := fun k =>
    bddAbove_boxSup_of_continuousOn (continuousOn_box_of_contDiffOn (smoothNbhd_pzIter hsm k))
  have hbddPzDth : ∀ k j, BddAbove (boxSet R (pth (pzIter k (DthIter j f)))) := fun k j =>
    bddAbove_boxSup_of_continuousOn (continuousOn_box_of_contDiffOn
      (smoothNbhd_pzIter_DthIter hsm k j).pth)
  refine ⟨⟨?_, ?_⟩, ⟨WlInf α l f, le_refl _⟩⟩
  · intro k hk
    refine supFinite_of_pointwise (C := (R + 1) ^ k * boxSup R (pzIter k f)) fun z hz θ hθ => ?_
    have hznn : (0 : ℝ) ≤ z := hz
    by_cases hzR : z ≤ R
    · have h1 := le_boxSup (hbddPz k) ⟨hz, hzR⟩ hθ
      have h2 : (z + 1) ^ k ≤ (R + 1) ^ k :=
        pow_le_pow_left₀ (show (0 : ℝ) ≤ z + 1 by linarith)
          (show z + 1 ≤ R + 1 by linarith) k
      calc |(z + 1) ^ k * pzIter k f z θ| = (z + 1) ^ k * |pzIter k f z θ| := by
            rw [abs_mul, abs_of_nonneg (pow_nonneg (show (0 : ℝ) ≤ z + 1 by linarith) k)]
        _ ≤ (R + 1) ^ k * boxSup R (pzIter k f) :=
            mul_le_mul h2 h1 (abs_nonneg _) (pow_nonneg (show (0 : ℝ) ≤ R + 1 by linarith) k)
    · rw [hpzIter_gt k z θ (not_le.mp hzR), mul_zero, abs_zero]
      exact mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ R + 1 by linarith) k)
        (boxSup_nonneg hR (hbddPz k))
  · intro j hj k hk hj1 hjk
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have h0 : ∀ z ∈ Set.Icc 0 R, pzIter k (DthIter (j' + 1) f) z 0 = 0 :=
      fun z _ => pzIter_apply_zero_of (DthIter (j' + 1) f) (fun z => DthIter_apply_zero f j' z) k z
    have hs : ∀ z ∈ Set.Icc 0 R, pzIter k (DthIter (j' + 1) f) z (π / 2) = 0 :=
      fun z _ => pzIter_apply_pi_half_of (DthIter (j' + 1) f)
        (fun z => DthIter_apply_pi_half f j' z) k z
    have hbdd := hbddPzDth k (j' + 1)
    refine supFinite_of_pointwise
      (C := (R + 1) ^ k * boxSup R (pth (pzIter k (DthIter (j' + 1) f))) * (K3 / α))
      fun z hz θ hθ => ?_
    have hznn : (0 : ℝ) ≤ z := hz
    by_cases hzR : z ≤ R
    · have hB := BoxMinBound (pzIter k (DthIter (j' + 1) f)) R
        (smoothNbhd_pzIter_DthIter hsm k (j' + 1)) h0 hs z ⟨hz, hzR⟩ θ hθ
      have hBnn : 0 ≤ boxSup R (pth (pzIter k (DthIter (j' + 1) f))) := boxSup_nonneg hR hbdd
      have hw := pzDth_weighted_bound (F := pzIter k (DthIter (j' + 1) f))
        hα (le_of_lt hK3pos) (hK3 θ hθ) hθ hBnn hB
      have h2 : (z + 1) ^ k ≤ (R + 1) ^ k :=
        pow_le_pow_left₀ (show (0 : ℝ) ≤ z + 1 by linarith)
          (show z + 1 ≤ R + 1 by linarith) k
      have h3 : 0 ≤ boxSup R (pth (pzIter k (DthIter (j' + 1) f))) * (K3 / α) :=
        mul_nonneg hBnn (div_nonneg (le_of_lt hK3pos) (le_of_lt hα))
      have hpos : 0 ≤ (z + 1) ^ k := pow_nonneg (show (0 : ℝ) ≤ z + 1 by linarith) k
      have h4 : 0 ≤ (R + 1) ^ k := pow_nonneg (show (0 : ℝ) ≤ R + 1 by linarith) k
      calc |(z + 1) ^ k * pzIter k (DthIter (j' + 1) f) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
          = (z + 1) ^ k * |pzIter k (DthIter (j' + 1) f) z θ
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))| := by
            rw [show (z + 1) ^ k * pzIter k (DthIter (j' + 1) f) z θ
                * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
              = (z + 1) ^ k * (pzIter k (DthIter (j' + 1) f) z θ
                * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) from by ring,
              abs_mul, abs_of_nonneg hpos]
        _ ≤ (R + 1) ^ k * (boxSup R (pth (pzIter k (DthIter (j' + 1) f))) * (K3 / α)) :=
            mul_le_mul h2 hw (abs_nonneg _) h4
        _ = (R + 1) ^ k * boxSup R (pth (pzIter k (DthIter (j' + 1) f))) * (K3 / α) := by ring
    · rw [pzIter_eq_zero_of_gt (DthIter (j' + 1) f) R
          (DthIter_eq_zero_of_gt f R hf_gt (j' + 1)) k z θ (not_le.mp hzR)]
      have hzero : (z + 1) ^ k * (0 : ℝ) * (Real.sin (2 * θ)) ^ (-(α / 5))
          / (α + Real.sin (2 * θ)) = 0 := by ring
      rw [hzero, abs_zero]
      exact mul_nonneg (mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ R + 1 by linarith) k)
        (boxSup_nonneg hR hbdd)) (div_nonneg (le_of_lt hK3pos) (le_of_lt hα))


/-! ## Measurability and integrability of the `ℋ^k`-integrand -/

theorem volume_Iθ_lt_top : (volume : Measure ℝ) Iθ < ⊤ := by
  rw [Iθ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

theorem volume_real_Iθ : (volume : Measure ℝ).real Iθ = π / 2 := by
  rw [MeasureTheory.measureReal_def, Iθ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- The integrand vanishes identically at `z = 0`. -/
theorem HkIntegrand_apply_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    HkIntegrand α k f 0 θ = 0 := by
  have hw0 : w 0 = 0 := by norm_num [w]
  have hWt0 : Wt α 0 θ = 0 := by simp [Wt, w]
  rw [HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (DzIter i f 0 θ * (w 0 / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hw0]; ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then (mixed j i f 0 θ * Wt α 0 θ) ^ 2 else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      by_cases h : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos h, hWt0]; ring
      · rw [if_neg h]
  rw [h1, h2, add_zero]

/-- The integrand vanishes above `R`. -/
theorem HkIntegrand_eq_zero_of_gt (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (R z θ : ℝ)
    (h : ∀ z θ : ℝ, R < z → f z θ = 0) (hz : R < z) : HkIntegrand α k f z θ = 0 := by
  have hDz := DzIter_eq_zero_of_gt f R h
  have hmix := mixed_eq_zero_of_gt f R h
  rw [HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hDz i z θ hz]; ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then (mixed j i f z θ * Wt α z θ) ^ 2 else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc, hmix j i z θ hz]; ring
      · rw [if_neg hc]
  rw [h1, h2, add_zero]

end Work.Spaces
