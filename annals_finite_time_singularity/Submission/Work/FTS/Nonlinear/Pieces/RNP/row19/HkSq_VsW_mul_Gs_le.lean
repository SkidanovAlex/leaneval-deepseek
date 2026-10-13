import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Split
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19aux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Gs_bounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.abs_DthIter_four_VsW_le
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.IntegralSubadd
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.HkSq_Vs0_mul_Gs_eq_zero
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.H2.STQ.Basic
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.Gam_mul_weight_le
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Elliptic.WtoH_Angular
import Submission.Work.Elliptic.WtoH_IntZ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Work.FTS.Nonlinear.Pieces.RNP (Vs Gs)

/-- `D_zF_* = Gs α` is `C^∞` on the open quadrant. -/
theorem smoothQuad_Gs (α : ℝ) : Work.FTS.LocData.SmoothQuad (Gs α) :=
  Work.FTS.LocData.smoothQuad_of_contDiffOn_uncurry
    (Work.FTS.LocData.contDiffOn_Dz Work.Spaces.isOpen_quadU
      (Work.FTS.LocData.SmoothQuad_Fstar α))

/-- The angular weight of the `𝒲^{l,∞}`-norm, `sin(2θ)^{-α/5}/(α+sin 2θ)`, is positive on
the open angular interval. -/
theorem dthAuxWt_pos {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) := by
  have hS : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  exact div_pos (Real.rpow_pos_of_pos hS _) (by linarith [hS.le, hα])

/-- The inverse of the angular weight of the `𝒲^{l,∞}`-norm is `(α + sin 2θ)·sin(2θ)^{α/5}`. -/
theorem dthAuxWt_inv {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))⁻¹
      = (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
  have hS : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [div_eq_mul_inv, mul_inv_rev, inv_inv,
    Real.rpow_neg hS.le (α / 5), inv_inv]

/-- **Uniform angular bound for the `D_θ`-iterates of `Γ`.** -/
theorem abs_DthIter_Gam_le : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ}, 0 < α → α ≤ 1 →
    ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
        ≤ K * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  refine ⟨Work.Spaces.tBound 0 0 + Work.Spaces.tBound 1 0 + Work.Spaces.tBound 2 0
    + Work.Spaces.tBound 3 0 + 1 + 1, by
    have h1 := Work.Spaces.tBound_nonneg 0 0
    have h2 := Work.Spaces.tBound_nonneg 1 0
    have h3 := Work.Spaces.tBound_nonneg 2 0
    have h4 := Work.Spaces.tBound_nonneg 3 0
    linarith, ?_⟩
  intro α hα hα1 i hi1 hi4 θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hS : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have htb : Work.Spaces.tBound (i - 1) 0 ≤ Work.Spaces.tBound 0 0
      + Work.Spaces.tBound 1 0 + Work.Spaces.tBound 2 0 + Work.Spaces.tBound 3 0 + 1 := by
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
    · show Work.Spaces.tBound 0 0 ≤ _
      linarith [Work.Spaces.tBound_nonneg 1 0, Work.Spaces.tBound_nonneg 2 0,
        Work.Spaces.tBound_nonneg 3 0]
    · show Work.Spaces.tBound 1 0 ≤ _
      linarith [Work.Spaces.tBound_nonneg 0 0, Work.Spaces.tBound_nonneg 2 0,
        Work.Spaces.tBound_nonneg 3 0]
    · show Work.Spaces.tBound 2 0 ≤ _
      linarith [Work.Spaces.tBound_nonneg 0 0, Work.Spaces.tBound_nonneg 1 0,
        Work.Spaces.tBound_nonneg 3 0]
    · show Work.Spaces.tBound 3 0 ≤ _
      linarith [Work.Spaces.tBound_nonneg 0 0, Work.Spaces.tBound_nonneg 1 0,
        Work.Spaces.tBound_nonneg 2 0]
  have hlen := Work.Spaces.dthU_Gam_le i hi1 α hα hα1 θ hθI
  have hw := Work.Spaces.Gam_mul_weight_le α θ hα hθI
  have hw' : α * Work.Spaces.Gam α θ
      * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 1 := by
    rw [← mul_div_assoc]; exact hw
  have hWpos := dthAuxWt_pos (α := α) hα hθ
  have hKeq := dthAuxWt_inv (α := α) hα hθ
  have hdecomp : Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
      = Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ :=
    Work.FTS.LocData.DthIter_rad_eq i (fun t => Work.Spaces.Gam α t) 0 θ
  rw [hdecomp]
  have hkey : |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ Work.Spaces.tBound 0 0 + Work.Spaces.tBound 1 0 + Work.Spaces.tBound 2 0
        + Work.Spaces.tBound 3 0 + 1 + 1 := by
    have h1 : |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ α * Work.Spaces.tBound (i - 1) 0 * Work.Spaces.Gam α θ
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
      mul_le_mul_of_nonneg_right hlen (le_of_lt hWpos)
    have h2 : α * Work.Spaces.tBound (i - 1) 0 * Work.Spaces.Gam α θ
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = Work.Spaces.tBound (i - 1) 0 * (α * Work.Spaces.Gam α θ
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
    rw [h2] at h1
    have h3 : Work.Spaces.tBound (i - 1) 0 * (α * Work.Spaces.Gam α θ
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
        ≤ Work.Spaces.tBound (i - 1) 0 * 1 :=
      mul_le_mul_of_nonneg_left hw' (Work.Spaces.tBound_nonneg _ _)
    have h4 : Work.Spaces.tBound (i - 1) 0 * 1 ≤ Work.Spaces.tBound 0 0
        + Work.Spaces.tBound 1 0 + Work.Spaces.tBound 2 0 + Work.Spaces.tBound 3 0 + 1 + 1 := by
      linarith [htb]
    linarith [h1, h3, h4]
  calc |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      = |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hWpos), mul_one]
    _ ≤ (Work.Spaces.tBound 0 0 + Work.Spaces.tBound 1 0 + Work.Spaces.tBound 2 0
        + Work.Spaces.tBound 3 0 + 1 + 1)
        * ((Real.sin (2 * θ)) ^ (-(α / 5))
        / (α + Real.sin (2 * θ)))⁻¹ :=
        mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr hWpos.le)
    _ = (Work.Spaces.tBound 0 0 + Work.Spaces.tBound 1 0 + Work.Spaces.tBound 2 0
        + Work.Spaces.tBound 3 0 + 1 + 1)
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
        rw [hKeq]

/-- **`D_z`-derivative bound for the split-off part `W = 𝒱(Φ̃_*) - 𝒱(Φ̃_*)(0,·)`.** -/
theorem abs_DzIter_VsW_le_aux : ∃ C : ℝ, 0 < C ∧ ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    Work.FTS.Nonlin.StarPkg α Cs Φs → 0 < α → α ≤ 1 →
    ∀ b : ℕ, b ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter b (VsW α Φs) z θ| ≤ C * (max Cs 0 * α) * min z 1 := by
  refine ⟨200, by norm_num, ?_⟩
  intro α Cs Φs hs hα hα1 b hb z hz θ hθ
  have hsq : Work.FTS.LocData.SmoothQuad (VsW α Φs) := smoothQuad_VsW hα hs
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    exact Set.mem_Ioi.mpr (by linarith)
  have hmin0 : 0 ≤ min z 1 := le_min hz zero_le_one
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have hle := abs_zpow_pzIter_VsW_le (α := α) (Cs := Cs) (Φs := Φs) hα hs
  rw [Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth (θ := θ) (hsq.curry_z hθ) b z hz1]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (2 * (max Cs 0 * α) * min z 1)
    (fun k => z ^ k * Work.Spaces.pzIter k (VsW α Φs) z θ)
    (fun k hk => hle k (by omega) z hz θ hθ)
  have hbell : ((Work.Spaces.bell b : ℕ) : ℝ) ≤ 100 := by
    exact_mod_cast Work.Spaces.bell_le b hb
  have hbnd0 : 0 ≤ 2 * (max Cs 0 * α) * min z 1 :=
    mul_nonneg (mul_nonneg (by norm_num) hM0) hmin0
  calc |∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ)
        * (z ^ k * Work.Spaces.pzIter k (VsW α Φs) z θ)|
      ≤ (Work.Spaces.bell b : ℝ) * (2 * (max Cs 0 * α) * min z 1) := hsum
    _ ≤ 100 * (2 * (max Cs 0 * α) * min z 1) := mul_le_mul_of_nonneg_right hbell hbnd0
    _ = 200 * (max Cs 0 * α) * min z 1 := by ring

/-- **The mixed `D_z`-`D_θ` derivative bound for `W = 𝒱(Φ̃_*) - 𝒱(Φ̃_*)(0,·)`.** -/
theorem abs_DzIter_DthIter_VsW_le_aux : ∃ C : ℝ, 0 < C ∧
    ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    Work.FTS.Nonlin.StarPkg α Cs Φs → 0 < α → α ≤ 1 →
    ∀ l b : ℕ, 1 ≤ l → l + b ≤ 4 → ∀ z ∈ Work.Spaces.Iz,
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter b (Work.Spaces.DthIter l (VsW α Φs)) z θ|
        ≤ C * (max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := by
  obtain ⟨C4, hC4pos, hC4⟩ := abs_DthIter_four_VsW_le
  refine ⟨100 * (max 2 C4) + 1, by positivity, ?_⟩
  intro α Cs Φs hs hα hα1 l b hl hlb z hz θ hθ
  have hsq : Work.FTS.LocData.SmoothQuad (VsW α Φs) := smoothQuad_VsW hα hs
  have hsqD : Work.FTS.LocData.SmoothQuad (Work.Spaces.DthIter l (VsW α Φs)) :=
    hsq.DthIter l
  have hz1 : z ∈ Set.Ioi (-1 : ℝ) := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz
    exact Set.mem_Ioi.mpr (by linarith)
  have hmin0 : 0 ≤ min z 1 := le_min hz zero_le_one
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have hS0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    angular_weight_nonneg hα hθ
  have hu0 : (0:ℝ) ≤ (max Cs 0 * α)
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 :=
    mul_nonneg (mul_nonneg hM0 hS0) hmin0
  have hC40 : (0:ℝ) ≤ C4 := hC4pos.le
  have hb4 : b ≤ 4 := by omega
  have hbnd : ∀ k ≤ b,
      |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter l (VsW α Φs)) z θ|
        ≤ max 2 C4 * ((max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | hkpos
    · subst h0
      simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero]
      rcases eq_or_lt_of_le (by omega : l ≤ 4) with h4 | hlt
      · subst h4
        have h := hC4 hs hα hα1 z hz θ hθ
        have h2 : C4 ≤ max 2 C4 := le_max_right _ _
        calc |Work.Spaces.DthIter 4 (VsW α Φs) z θ|
            ≤ C4 * (max Cs 0 * α)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := h
          _ ≤ max 2 C4 * (max Cs 0 * α)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hM0) hS0) hmin0
          _ = max 2 C4 * ((max Cs 0 * α)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1) := by ring
      · have h := abs_DthIter_VsW_le_min (α := α) (Cs := Cs) (Φs := Φs) hα hs l hl
          (by omega) z hz θ hθ
        have h2 : (2:ℝ) ≤ max 2 C4 := le_max_left _ _
        calc |Work.Spaces.DthIter l (VsW α Φs) z θ|
            ≤ 2 * (max Cs 0 * α)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := h
          _ ≤ max 2 C4 * (max Cs 0 * α)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hM0) hS0) hmin0
          _ = max 2 C4 * ((max Cs 0 * α)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1) := by ring
    · have h := abs_zpow_pzIter_DthIter_VsW_le (α := α) (Cs := Cs) (Φs := Φs) hα hs
        l k hl hkpos (by omega) z hz θ hθ
      have h2 : (2:ℝ) ≤ max 2 C4 := le_max_left _ _
      calc |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter l (VsW α Φs)) z θ|
          ≤ 2 * (max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := h
        _ ≤ max 2 C4 * (max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hM0) hS0) hmin0
        _ = max 2 C4 * ((max Cs 0 * α)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1) := by ring
  rw [Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth (θ := θ) (hsqD.curry_z hθ) b z hz1]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b
    (max 2 C4 * ((max Cs 0 * α)
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1))
    (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter l (VsW α Φs)) z θ)
    (fun k hk => hbnd k hk)
  have hbell : ((Work.Spaces.bell b : ℕ) : ℝ) ≤ 100 := by
    exact_mod_cast Work.Spaces.bell_le b hb4
  have hv0 : (0:ℝ) ≤ max 2 C4 := le_trans (by norm_num) (le_max_left _ _)
  have hc0 : (0:ℝ) ≤ max 2 C4 * ((max Cs 0 * α)
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1) :=
    mul_nonneg hv0 hu0
  calc |∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ)
        * (z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter l (VsW α Φs)) z θ)|
      ≤ (Work.Spaces.bell b : ℝ) * (max 2 C4 * ((max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1)) := hsum
    _ ≤ 100 * (max 2 C4 * ((max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1)) :=
        mul_le_mul_of_nonneg_right hbell hc0
    _ ≤ (100 * (max 2 C4) + 1) * (max Cs 0 * α)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 := by
        nlinarith [hv0, hu0]

/-- `∑_{b ≤ i} C(i,b) = 2^i ≤ 16` for `i ≤ 4`. -/
theorem sum_range_choose_le_sixteen (i : ℕ) (hi : i ≤ 4) :
    (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)) ≤ 16 := by
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  have h2 : (2 : ℕ) ^ i ≤ 16 := by interval_cases i <;> norm_num
  exact_mod_cast h2

/-- `(∑_{b ≤ i} C(i,b))·(∑_{b ≤ j} C(j,b)) = 2^{i+j} ≤ 16` when `i + j ≤ 4`. -/
theorem sum_range_choose_mul_le_sixteen (i j : ℕ) (hij : i + j ≤ 4) :
    (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ))
      * (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)) ≤ 16 := by
  rw [← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_mul, Nat.sum_range_choose,
    Nat.sum_range_choose, ← pow_add]
  have h2 : (2 : ℕ) ^ (i + j) ≤ 16 := by
    calc (2 : ℕ) ^ (i + j) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hij
      _ = 16 := by norm_num
  exact_mod_cast h2

/-- **The `D_z`-slots of the `ℋ⁴`-integrand of `W · D_zF_*`.** -/
theorem eta_slot_le : ∃ C : ℝ, 0 < C ∧ ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    Work.FTS.Nonlin.StarPkg α Cs Φs → 0 < α → α ≤ 1 →
    ∀ i : ℕ, i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.DzIter i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := abs_DzIter_VsW_le_aux
  obtain ⟨C2, hC2pos, hC2⟩ := Gs_bounds
  refine ⟨(16 * (C1 * C2)) ^ 2 + 1, by positivity, ?_⟩
  intro α Cs Φs hs hα hα1 i hi4 z hz θ hθ
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hS : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsqW : Work.FTS.LocData.SmoothQuad (VsW α Φs) := smoothQuad_VsW hα hs
  have hsqG : Work.FTS.LocData.SmoothQuad (Gs α) := smoothQuad_Gs α
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have hmin0 : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hZ0 : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz.le (by positivity)
  have hw0 : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have hC10 : 0 ≤ C1 := hC1pos.le
  have hC20 : 0 ≤ C2 := hC2pos.le
  have hleib := Work.FTS.H2.STQ.DzIter_mul_quad (j := i) hsqW hsqG hzI hθ
  have hsum : |Work.Spaces.DzIter i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ|
      ≤ 16 * (C1 * C2) * (max Cs 0 * α) * α * (min z 1 * (z / (1 + z) ^ 2)) := by
    rw [hleib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hpt : ∀ b ∈ Finset.range (i + 1),
        |(i.choose b : ℝ) * (Work.Spaces.DzIter b (VsW α Φs) z θ
            * Work.Spaces.DzIter (i - b) (Gs α) z θ)|
          ≤ (i.choose b : ℝ)
            * (C1 * (max Cs 0 * α) * min z 1 * (C2 * α * (z / (1 + z) ^ 2))) := by
      intro b hb
      have hb4 : b ≤ 4 := by have := Finset.mem_range.mp hb; omega
      have hib4 : i - b ≤ 4 := by omega
      have hWb := hC1 hs hα hα1 b hb4 z hzI θ hθ
      have hGb := (hC2 α hα hα1).1 (i - b) hib4 z hzI θ ⟨hθ.1.le, hθ.2.le⟩
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (i.choose b)), abs_mul]
      refine mul_le_mul_of_nonneg_left (mul_le_mul hWb hGb (abs_nonneg _)
        (mul_nonneg (mul_nonneg hC10 hM0) hmin0)) (Nat.cast_nonneg _)
    calc ∑ b ∈ Finset.range (i + 1),
          |(i.choose b : ℝ) * (Work.Spaces.DzIter b (VsW α Φs) z θ
            * Work.Spaces.DzIter (i - b) (Gs α) z θ)|
        ≤ ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (C1 * (max Cs 0 * α) * min z 1 * (C2 * α * (z / (1 + z) ^ 2))) :=
          Finset.sum_le_sum hpt
      _ = (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ))
            * (C1 * (max Cs 0 * α) * min z 1 * (C2 * α * (z / (1 + z) ^ 2))) := by
          rw [Finset.sum_mul]
      _ ≤ 16 * (C1 * (max Cs 0 * α) * min z 1 * (C2 * α * (z / (1 + z) ^ 2))) :=
          mul_le_mul_of_nonneg_right (sum_range_choose_le_sixteen i hi4)
            (mul_nonneg (mul_nonneg (mul_nonneg hC10 hM0) hmin0)
              (mul_nonneg (mul_nonneg hC20 hα.le) hZ0))
      _ = 16 * (C1 * C2) * (max Cs 0 * α) * α * (min z 1 * (z / (1 + z) ^ 2)) := by ring
  have hwf : min z 1 * (z / (1 + z) ^ 2) * Work.Spaces.w z = min z 1 / z := by
    rw [Work.Spaces.w]
    field_simp
  have hmin1 : min z 1 / z = min 1 (1 / z) := by
    rcases le_total z 1 with h1 | h1
    · rw [min_eq_left h1,
        min_eq_left (by rw [le_div_iff₀ hz, one_mul]; exact h1)]
      field_simp
    · rw [min_eq_right h1, min_eq_right (by rw [div_le_one hz]; exact h1)]
  have hminz0 : (0:ℝ) ≤ min 1 (1 / z) := le_min zero_le_one (by positivity)
  have hstep : |Work.Spaces.DzIter i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))|
      ≤ 16 * (C1 * C2) * (max Cs 0 * α) * α * min 1 (1 / z)
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hw0 (Real.rpow_nonneg hS.le _))]
    calc |Work.Spaces.DzIter i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ|
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        ≤ (16 * (C1 * C2) * (max Cs 0 * α) * α * (min z 1 * (z / (1 + z) ^ 2)))
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
          mul_le_mul_of_nonneg_right hsum (div_nonneg hw0 (Real.rpow_nonneg hS.le _))
      _ = 16 * (C1 * C2) * (max Cs 0 * α) * α * min 1 (1 / z)
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
          rw [← hmin1, ← hwf]; ring
  have hY0 : (0:ℝ) ≤ 16 * (C1 * C2) * (max Cs 0 * α) * α * min 1 (1 / z)
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    refine div_nonneg ?_ (Real.rpow_nonneg hS.le _)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg hC10 hC20)) hM0) hα.le) hminz0
  have hsq : (Work.Spaces.DzIter i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (16 * (C1 * C2) * (max Cs 0 * α) * α * min 1 (1 / z)
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [← sq_abs (Work.Spaces.DzIter i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
    exact pow_le_pow_left₀ (abs_nonneg _) hstep 2
  have hpow : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [pow_two, ← Real.rpow_add hS]
    congr 1
    rw [Work.Spaces.eta]; ring
  have hMkey : (16 * (C1 * C2) * (max Cs 0 * α) * α) ^ 2
      = (16 * (C1 * C2)) ^ 2 * (max Cs 0) ^ 2 * α ^ 4 := by ring
  have hX0 : 0 ≤ (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hα.le 4)) (sq_nonneg _))
      (Real.rpow_nonneg hS.le _)
  calc (Work.Spaces.DzIter i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ (16 * (C1 * C2) * (max Cs 0 * α) * α * min 1 (1 / z)
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := hsq
    _ = (16 * (C1 * C2) * (max Cs 0 * α) * α) ^ 2 * (min 1 (1 / z)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        rw [div_pow, hpow, div_eq_mul_inv, ← Real.rpow_neg hS.le]
        ring
    _ = (16 * (C1 * C2)) ^ 2 * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        rw [hMkey]
    _ ≤ ((16 * (C1 * C2)) ^ 2 + 1) * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        nlinarith [hX0]

/-- **The `D_θ`-slots of the `ℋ⁴`-integrand of `W · D_zF_*`.** -/
theorem gam_slot_le : ∃ C : ℝ, 0 < C ∧ ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    Work.FTS.Nonlin.StarPkg α Cs Φs → 0 < α → α ≤ 1 →
    ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z : ℝ, 0 < z →
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.mixed j i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
            * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := abs_DzIter_VsW_le_aux
  obtain ⟨C2, hC2pos, hC2⟩ := abs_DzIter_DthIter_VsW_le_aux
  obtain ⟨C3, hC3pos, hC3⟩ := Gs_bounds
  obtain ⟨C4, hC4pos, hC4⟩ := abs_DthIter_Gam_le
  have hC10 : 0 ≤ C1 := hC1pos.le
  have hC20 : 0 ≤ C2 := hC2pos.le
  have hC30 : 0 ≤ C3 := hC3pos.le
  have hC40 : 0 ≤ C4 := hC4pos.le
  refine ⟨(16 * (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4)) ^ 2 + 1, by positivity, ?_⟩
  intro α Cs Φs hs hα hα1 i j hi hij z hz θ hθ
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hS : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsqW : Work.FTS.LocData.SmoothQuad (VsW α Φs) := smoothQuad_VsW hα hs
  have hsqG : Work.FTS.LocData.SmoothQuad (Gs α) := smoothQuad_Gs α
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have hT0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith [hS.le, hα]) (Real.rpow_nonneg hS.le _)
  have hT2 : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
    have h1 : α + Real.sin (2 * θ) ≤ 2 := by
      have := Real.sin_le_one (2 * θ); linarith
    have h2 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
      Real.rpow_le_one hS.le (Real.sin_le_one _) (by positivity)
    calc (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
        ≤ 2 * 1 := mul_le_mul h1 h2 (Real.rpow_nonneg hS.le _) (by norm_num)
      _ = 2 := by ring
  have hmin0 : 0 ≤ min z 1 := le_min hz.le zero_le_one
  have hZ0 : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz.le (by positivity)
  have hw0 : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have hCt0 : 0 ≤ C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4 := by
    have h1 : 0 ≤ C1 * C3 * C4 := mul_nonneg (mul_nonneg hC10 hC30) hC40
    have h2 : 0 ≤ C2 * C3 := mul_nonneg hC20 hC30
    have h3 : 0 ≤ 2 * C2 * C3 * C4 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC20) hC30) hC40
    linarith
  have hnn : 0 ≤ (max Cs 0 * α) * α * ((α + Real.sin (2 * θ))
        * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1 * (z / (1 + z) ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hM0 hα.le) hT0) hmin0) hZ0
  have hle1 : C1 * C3 * C4 ≤ C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4 := by
    have h2 : 0 ≤ C2 * C3 := mul_nonneg hC20 hC30
    have h3 : 0 ≤ 2 * C2 * C3 * C4 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC20) hC30) hC40
    linarith
  have hle2 : C2 * C3 ≤ C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4 := by
    have h1 : 0 ≤ C1 * C3 * C4 := mul_nonneg (mul_nonneg hC10 hC30) hC40
    have h3 : 0 ≤ 2 * C2 * C3 * C4 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC20) hC30) hC40
    linarith
  have hle3 : 2 * C2 * C3 * C4 ≤ C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4 := by
    have h1 : 0 ≤ C1 * C3 * C4 := mul_nonneg (mul_nonneg hC10 hC30) hC40
    have h2 : 0 ≤ C2 * C3 := mul_nonneg hC20 hC30
    linarith
  -- the pointwise per-term bound
  have hcomb : ∀ a b : ℕ, a ≤ i → b ≤ j →
      |Work.Spaces.mixed b a (VsW α Φs) z θ
        * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ|
        ≤ (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * min z 1 * (z / (1 + z) ^ 2) := by
    intro a b hai hbj
    have hab4 : a + b ≤ 4 := by omega
    have hb4 : b ≤ 4 := by omega
    have hjb4 : j - b ≤ 4 := by omega
    by_cases ha0 : a = 0
    · subst ha0
      have hG4 := hC4 hα hα1 i (by omega) (by omega) θ hθ
      have hG := (hC3 α hα hα1).2 i (j - b) (by omega) (by omega) hjb4 z hzI θ hθI
      have hW := hC1 hs hα hα1 b hb4 z hzI θ hθ
      simp only [Work.Spaces.mixed_zero_right, Nat.sub_zero]
      have hWG : |Work.Spaces.DzIter b (VsW α Φs) z θ
            * Work.Spaces.DzIter (j - b) (Work.Spaces.DthIter i (Gs α)) z θ|
          ≤ (C1 * (max Cs 0 * α) * min z 1)
            * (C3 * α * (C4 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * (z / (1 + z) ^ 2)) := by
        rw [abs_mul]
        refine mul_le_mul hW ?_ (abs_nonneg _) (mul_nonneg (mul_nonneg hC10 hM0) hmin0)
        calc |Work.Spaces.DzIter (j - b) (Work.Spaces.DthIter i (Gs α)) z θ|
            ≤ C3 * α * |Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
                * (z / (1 + z) ^ 2) := hG
          _ ≤ C3 * α * (C4 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * (z / (1 + z) ^ 2) := by
              refine mul_le_mul_of_nonneg_right ?_ hZ0
              exact mul_le_mul_of_nonneg_left hG4 (mul_nonneg hC30 hα.le)
      calc |Work.Spaces.DzIter b (VsW α Φs) z θ
            * Work.Spaces.DzIter (j - b) (Work.Spaces.DthIter i (Gs α)) z θ|
          ≤ (C1 * (max Cs 0 * α) * min z 1)
              * (C3 * α * (C4 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                  * (z / (1 + z) ^ 2)) := hWG
        _ = (C1 * C3 * C4) * ((max Cs 0 * α) * α
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
              * min z 1 * (z / (1 + z) ^ 2)) := by ring
        _ ≤ (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * ((max Cs 0 * α) * α
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
              * min z 1 * (z / (1 + z) ^ 2)) :=
            mul_le_mul_of_nonneg_right hle1 hnn
        _ = (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
              * min z 1 * (z / (1 + z) ^ 2) := by ring
    · have ha1 : 1 ≤ a := by omega
      have hW := hC2 hs hα hα1 a b ha1 hab4 z hzI θ hθ
      have hWa : |Work.Spaces.mixed b a (VsW α Φs) z θ|
          ≤ C2 * (max Cs 0 * α) * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * min z 1 := hW
      by_cases hna : i - a = 0
      · have hG := (hC3 α hα hα1).1 (j - b) hjb4 z hzI θ hθI
        rw [hna]
        simp only [Work.Spaces.mixed_zero_right, Work.Spaces.DthIter_zero]
        have hWG : |Work.Spaces.DzIter b (Work.Spaces.DthIter a (VsW α Φs)) z θ
              * Work.Spaces.DzIter (j - b) (Gs α) z θ|
            ≤ (C2 * (max Cs 0 * α)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1)
              * (C3 * α * (z / (1 + z) ^ 2)) := by
          rw [abs_mul]
          exact mul_le_mul hWa hG (abs_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg hC20 hM0) hT0) hmin0)
        calc |Work.Spaces.DzIter b (Work.Spaces.DthIter a (VsW α Φs)) z θ
              * Work.Spaces.DzIter (j - b) (Gs α) z θ|
            ≤ (C2 * (max Cs 0 * α)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1)
              * (C3 * α * (z / (1 + z) ^ 2)) := hWG
          _ = (C2 * C3) * ((max Cs 0 * α) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * min z 1 * (z / (1 + z) ^ 2)) := by ring
          _ ≤ (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * ((max Cs 0 * α) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * min z 1 * (z / (1 + z) ^ 2)) :=
              mul_le_mul_of_nonneg_right hle2 hnn
          _ = (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * min z 1 * (z / (1 + z) ^ 2) := by ring
      · have hna1 : 1 ≤ i - a := by omega
        have hG4 := hC4 hα hα1 (i - a) hna1 (by omega) θ hθ
        have hG := (hC3 α hα hα1).2 (i - a) (j - b) hna1 (by omega) hjb4 z hzI θ hθI
        have hWG : |Work.Spaces.mixed b a (VsW α Φs) z θ
              * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ|
            ≤ (C2 * (max Cs 0 * α)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1)
              * (C3 * α * (C4 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                  * (z / (1 + z) ^ 2)) := by
          rw [abs_mul]
          refine mul_le_mul hWa ?_ (abs_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg hC20 hM0) hT0) hmin0)
          calc |Work.Spaces.DzIter (j - b) (Work.Spaces.DthIter (i - a) (Gs α)) z θ|
              ≤ C3 * α * |Work.Spaces.DthIter (i - a)
                  (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| * (z / (1 + z) ^ 2) := hG
            _ ≤ C3 * α * (C4 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                  * (z / (1 + z) ^ 2) := by
                refine mul_le_mul_of_nonneg_right ?_ hZ0
                exact mul_le_mul_of_nonneg_left hG4 (mul_nonneg hC30 hα.le)
        have hT2' : ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
            ≤ 2 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
          nlinarith [hT0, hT2]
        have hWG' : (C2 * (max Cs 0 * α)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1)
              * (C3 * α * (C4 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                  * (z / (1 + z) ^ 2))
            ≤ (2 * C2 * C3 * C4) * ((max Cs 0 * α) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * min z 1 * (z / (1 + z) ^ 2)) := by
          have hkey : (max Cs 0 * α) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * min z 1 * (z / (1 + z) ^ 2)
              ≤ (max Cs 0 * α) * α
                * (2 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * min z 1 * (z / (1 + z) ^ 2) := by
            have hX : 0 ≤ (max Cs 0 * α) * α * min z 1 * (z / (1 + z) ^ 2) :=
              mul_nonneg (mul_nonneg (mul_nonneg hM0 hα.le) hmin0) hZ0
            have hY : 0 ≤ (max Cs 0 * α) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * min z 1 * (z / (1 + z) ^ 2) := hnn
            calc (max Cs 0 * α) * α
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  * min z 1 * (z / (1 + z) ^ 2)
                = ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  * ((max Cs 0 * α) * α
                    * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                    * min z 1 * (z / (1 + z) ^ 2)) := by ring
              _ ≤ 2 * ((max Cs 0 * α) * α
                    * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                    * min z 1 * (z / (1 + z) ^ 2)) :=
                  mul_le_mul_of_nonneg_right hT2 hY
              _ = (max Cs 0 * α) * α
                    * (2 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                    * min z 1 * (z / (1 + z) ^ 2) := by ring
          calc (C2 * (max Cs 0 * α)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) * min z 1)
              * (C3 * α * (C4 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                  * (z / (1 + z) ^ 2))
            = (C2 * C3 * C4) * ((max Cs 0 * α) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * min z 1 * (z / (1 + z) ^ 2)) := by ring
            _ ≤ (C2 * C3 * C4) * ((max Cs 0 * α) * α
                * (2 * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * min z 1 * (z / (1 + z) ^ 2)) :=
                mul_le_mul_of_nonneg_left hkey (mul_nonneg (mul_nonneg hC20 hC30) hC40)
            _ = (2 * C2 * C3 * C4) * ((max Cs 0 * α) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * min z 1 * (z / (1 + z) ^ 2)) := by ring
        calc |Work.Spaces.mixed b a (VsW α Φs) z θ
              * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ| ≤ _ := hWG
          _ ≤ (2 * C2 * C3 * C4) * ((max Cs 0 * α) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * min z 1 * (z / (1 + z) ^ 2)) := hWG'
          _ ≤ (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * ((max Cs 0 * α) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * min z 1 * (z / (1 + z) ^ 2)) :=
              mul_le_mul_of_nonneg_right hle3 hnn
          _ = (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * min z 1 * (z / (1 + z) ^ 2) := by ring
  -- the Leibniz expansion and the double-sum bound
  have hleib := Work.FTS.H2.STQ.mixed_mul_quad (j := j) (i := i) hsqW hsqG hzI hθ
  have hsum : |Work.Spaces.mixed j i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ|
      ≤ 16 * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
          * min z 1 * (z / (1 + z) ^ 2)) := by
    rw [hleib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun a ha => Finset.abs_sum_le_sum_abs _ _)) ?_
    have hpt : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
        |((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (VsW α Φs) z θ
                * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)|
          ≤ (i.choose a : ℝ) * (j.choose b : ℝ)
            * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * min z 1 * (z / (1 + z) ^ 2)) := by
      intro a ha b hb
      have hai : a ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
      have hh : |Work.Spaces.mixed b a (VsW α Φs) z θ|
          * |Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ|
          ≤ (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
              * min z 1 * (z / (1 + z) ^ 2) := by
        rw [← abs_mul]; exact hcomb a b hai hbj
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (i.choose a)),
        abs_of_nonneg (Nat.cast_nonneg (j.choose b)), abs_mul]
      exact mul_le_mul_of_nonneg_left hh (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    calc ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          |((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (VsW α Φs) z θ
                * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)|
        ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (i.choose a : ℝ) * (j.choose b : ℝ)
              * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  * min z 1 * (z / (1 + z) ^ 2)) :=
          Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hpt a ha b hb))
      _ = (∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ))
            * ((∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ))
              * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  * min z 1 * (z / (1 + z) ^ 2))) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun b hb => by ring)
      _ = ((∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ))
            * (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)))
          * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
              * min z 1 * (z / (1 + z) ^ 2)) := by ring
      _ ≤ 16 * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            * min z 1 * (z / (1 + z) ^ 2)) :=
          mul_le_mul_of_nonneg_right (sum_range_choose_mul_le_sixteen i j hij)
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCt0 hM0) hα.le) hT0)
              hmin0) hZ0)
  -- multiply by `Wt` and square
  have hwf : min z 1 * (z / (1 + z) ^ 2) * Work.Spaces.w z = min z 1 / z := by
    rw [Work.Spaces.w]
    field_simp
  have hmin1 : min z 1 / z = min 1 (1 / z) := by
    rcases le_total z 1 with h1 | h1
    · rw [min_eq_left h1, min_eq_left (by rw [le_div_iff₀ hz, one_mul]; exact h1)]
      field_simp
    · rw [min_eq_right h1, min_eq_right (by rw [div_le_one hz]; exact h1)]
  have hminz0 : (0:ℝ) ≤ min 1 (1 / z) := le_min zero_le_one (by positivity)
  have hWtval : Work.Spaces.Wt α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
  have hCtT0 : 0 ≤ (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hCt0 hM0) hα.le) hT0
  have hstep : |Work.Spaces.mixed j i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
        * Work.Spaces.Wt α z θ|
      ≤ 16 * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) * min 1 (1 / z)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [abs_mul, hWtval, abs_of_nonneg (mul_nonneg hw0 (Real.rpow_nonneg hS.le _))]
    calc |Work.Spaces.mixed j i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ|
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))
        ≤ (16 * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
              * min z 1 * (z / (1 + z) ^ 2)))
          * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
          mul_le_mul_of_nonneg_right hsum (mul_nonneg hw0 (Real.rpow_nonneg hS.le _))
      _ = 16 * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) * min 1 (1 / z)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
          rw [← hmin1, ← hwf]; ring
  have hY0 : (0:ℝ) ≤ 16 * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) * min 1 (1 / z)
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCtT0) hminz0)
      (Real.rpow_nonneg hS.le _)
  have hsq : (Work.Spaces.mixed j i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      ≤ (16 * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) * min 1 (1 / z)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := by
    rw [← sq_abs (Work.Spaces.mixed j i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
        * Work.Spaces.Wt α z θ)]
    exact pow_le_pow_left₀ (abs_nonneg _) hstep 2
  have hpow1 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [pow_two, ← Real.rpow_add hS]
    congr 1
    ring
  have hpow2 : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
    rw [pow_two, ← Real.rpow_add hS]
    congr 1
    ring
  have hMkey : (16 * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2
      = (16 * (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4)) ^ 2 * (max Cs 0) ^ 2 * α ^ 4
        * ((α + Real.sin (2 * θ)) ^ 2 * ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2) := by ring
  have hX0 : 0 ≤ (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
      * ((α + Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hα.le 4)) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hS.le _))
  calc (Work.Spaces.mixed j i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
        * Work.Spaces.Wt α z θ) ^ 2
      ≤ (16 * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) * min 1 (1 / z)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2 := hsq
    _ = (16 * ((C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4) * (max Cs 0 * α) * α
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) ^ 2 * (min 1 (1 / z)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [mul_pow, mul_pow, hpow1]
    _ = (16 * (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4)) ^ 2 * (max Cs 0) ^ 2 * α ^ 4
          * ((α + Real.sin (2 * θ)) ^ 2 * ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2)
          * (min 1 (1 / z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [hMkey]
    _ = (16 * (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4)) ^ 2 * (max Cs 0) ^ 2 * α ^ 4
          * (min 1 (1 / z)) ^ 2
          * ((α + Real.sin (2 * θ)) ^ 2
              * ((Real.sin (2 * θ)) ^ (2 * α / 5)
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
        rw [hpow2]; ring
    _ = (16 * (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4)) ^ 2 * (max Cs 0) ^ 2 * α ^ 4
          * (min 1 (1 / z)) ^ 2
          * ((α + Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by
        have hg1 : (2:ℝ) * α / 5 - Work.Spaces.gam α = 2 * α / 5 + -(Work.Spaces.gam α) := by
          ring
        rw [hg1, ← Real.rpow_add hS]
    _ ≤ ((16 * (C1 * C3 * C4 + C2 * C3 + 2 * C2 * C3 * C4)) ^ 2 + 1)
          * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
          * ((α + Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) := by
        nlinarith [hX0]

/-- `(min 1 (1/z))^2 ≤ 4/(1+z)^2` for `z > 0`. -/
theorem min_one_inv_sq_le {z : ℝ} (hz : 0 < z) :
    (min 1 (1 / z)) ^ 2 ≤ 4 / (1 + z) ^ 2 := by
  rcases le_total z 1 with h1 | h1
  · rw [min_eq_left (by rw [le_div_iff₀ hz]; linarith)]
    rw [one_pow, le_div_iff₀ (by positivity)]
    nlinarith
  · rw [min_eq_right (by rw [div_le_one hz]; linarith)]
    rw [div_pow, one_pow, div_le_iff₀ (by positivity : (0:ℝ) < z ^ 2),
      show 4 / (1 + z) ^ 2 * z ^ 2 = 4 * z ^ 2 / (1 + z) ^ 2 from by ring,
      le_div_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2)]
    nlinarith

/-- **Pointwise domination of the `ℋ⁴`-integrand of `W · D_zF_*`.** -/
theorem HkIntegrand_VsW_mul_Gs_le : ∃ C : ℝ, 0 < C ∧
    ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    Work.FTS.Nonlin.StarPkg α Cs Φs → 0 < α → α ≤ 1 →
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
        ≤ C * (max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2)
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
  obtain ⟨Cη, hCηpos, hCη⟩ := eta_slot_le
  obtain ⟨Cγ, hCγpos, hCγ⟩ := gam_slot_le
  refine ⟨(5 * Cη + 25 * Cγ) * 4 + 1, by positivity, ?_⟩
  intro α Cs Φs hs hα hα1 z hz θ hθ
  have hCη0 : 0 ≤ Cη := hCηpos.le
  have hCγ0 : 0 ≤ Cγ := hCγpos.le
  have hA20 : 0 ≤ (max Cs 0) ^ 2 * α ^ 4 :=
    mul_nonneg (sq_nonneg _) (pow_nonneg hα.le 4)
  have h460 : 0 ≤ 4 / (1 + z) ^ 2 := div_nonneg (by norm_num) (by positivity)
  have hS0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hW0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + ((α + Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
    add_nonneg (Real.rpow_nonneg hS0 _) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hS0 _))
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ z from hz) with hz0 | hzpos
  · rw [← hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg (max Cs 0)))
      (pow_nonneg hα.le 4)) (by norm_num)) hW0
  by_cases hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · -- interior: sum the two families of slots
    have hInt : Work.Spaces.HkIntegrand α 4 (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
        = (∑ i ∈ Finset.range 5,
            (Work.Spaces.DzIter i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2
              else 0) := by
      rw [Work.Spaces.HkIntegrand]
    have hγnn : 0 ≤ Cγ * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
        * ((α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCγ0 (sq_nonneg (max Cs 0)))
        (pow_nonneg hα.le 4)) (sq_nonneg _))
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hS0 _))
    have hs1 : (∑ i ∈ Finset.range 5,
          (Work.Spaces.DzIter i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 5 * (Cη * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      calc (∑ i ∈ Finset.range 5,
            (Work.Spaces.DzIter i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range 5, (Cη * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
            Finset.sum_le_sum fun i hi =>
              hCη hs hα hα1 i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) z hzpos θ hθi
        _ = 5 * (Cη * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]
    have hs2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2
          else 0))
        ≤ 25 * (Cγ * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
            * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
      calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0))
          ≤ ∑ _i ∈ Finset.range 5, ∑ _j ∈ Finset.range 5,
              (Cγ * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
                * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
            refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ 4
            · rw [if_pos hc]
              exact hCγ hs hα hα1 i j hc.1 hc.2 z hzpos θ hθi
            · rw [if_neg hc]
              exact hγnn
        _ = 25 * (Cγ * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
              * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat]
            ring
    have hK000 : 0 ≤ 5 * Cη + 25 * Cγ := by linarith
    have hmin20 : 0 ≤ (min 1 (1 / z)) ^ 2 := sq_nonneg _
    rw [hInt]
    have hsE0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hS0 _
    have htE0 : 0 ≤ (α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hS0 _)
    have hXX0 : 0 ≤ (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2 := mul_nonneg hA20 hmin20
    calc (∑ i ∈ Finset.range 5,
            (Work.Spaces.DzIter i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => VsW α Φs z θ * Gs α z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2
              else 0))
        ≤ 5 * (Cη * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + 25 * (Cγ * (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
              * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
          add_le_add hs1 hs2
      _ = (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
            * (5 * Cη * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 25 * Cγ * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by ring
      _ ≤ (max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
            * ((5 * Cη + 25 * Cγ)
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                    + ((α + Real.sin (2 * θ)) ^ 2
                        * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hXX0
          nlinarith [hCη0, hCγ0, hsE0, htE0]
      _ = (5 * Cη + 25 * Cγ) * ((max Cs 0) ^ 2 * α ^ 4 * (min 1 (1 / z)) ^ 2
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by ring
      _ ≤ (5 * Cη + 25 * Cγ) * ((max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2)
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hK000
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (min_one_inv_sq_le hzpos) hA20) hW0
      _ ≤ ((5 * Cη + 25 * Cγ) * 4 + 1) * ((max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2)
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by
          have hX0 : 0 ≤ (max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2)
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                  + ((α + Real.sin (2 * θ)) ^ 2
                      * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
            mul_nonneg (mul_nonneg hA20 h460) hW0
          nlinarith [hK000, hX0]
      _ = ((5 * Cη + 25 * Cγ) * 4 + 1) * (max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2)
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by ring
  · -- boundary angle: the integrand vanishes
    have hsin : Real.sin (2 * θ) = 0 := Work.Spaces.sin_two_eq_zero_of_not_Ioo hθ hθi
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 4 _ z θ hsin]
    have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 0 := by
      rw [hsin, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
    have h2 : (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) = 0 := by
      rw [hsin, Real.zero_rpow (by rw [Work.Spaces.gam]; intro hh; linarith)]
    rw [h1, h2]
    simp

/-- The task's lemma. -/
theorem HkSq_VsW_mul_Gs_le : ∃ K : ℝ, 0 < K ∧ ∀ {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    Work.FTS.Nonlin.StarPkg α Cs Φs → 0 < α → α ≤ 1 →
    Work.Spaces.HkSq α 4
      (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.row19.VsW α Φs z θ
        * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ)
      ≤ K * (max Cs 0) ^ 2 * α ^ 4 := by
  obtain ⟨C, hCpos, hC⟩ := HkIntegrand_VsW_mul_Gs_le
  refine ⟨C * (10 ^ 4 + 700) * 8 + 1, by positivity, ?_⟩
  intro α Cs Φs hs hα hα1
  have hC0 : 0 ≤ C := hCpos.le
  have hA20 : 0 ≤ (max Cs 0) ^ 2 * α ^ 4 :=
    mul_nonneg (sq_nonneg _) (pow_nonneg hα.le 4)
  have hIθ1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have hIθ2 : IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    Work.Spaces.integrableOn_angular_weight' hα hα1
  have hang : (∫ θ in Work.Spaces.Iθ, ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + ((α + Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) ≤ 10 ^ 4 + 700 := by
    have h := Work.Elliptic.WtoH_Angular (α := α) (A := 1) (B := 1) hα hα1
      (by norm_num) (by norm_num)
    simpa using h
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => VsW α Φs z θ * Gs α z θ) z θ)
        ≤ C * (max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2) * (10 ^ 4 + 700) := by
    intro z hz
    have hmaj : Integrable (fun θ : ℝ => C * (max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2)
        * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))))
        (volume.restrict Work.Spaces.Iθ) :=
      (hIθ1.add hIθ2).const_mul _
    calc (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z θ => VsW α Φs z θ * Gs α z θ) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C * (max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2)
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun θ =>
              Work.Spaces.HkIntegrand_nonneg α 4 _ z θ) hmaj
            (ae_restrict_of_forall_mem measurableSet_Icc
              (fun θ hθ => hC hs hα hα1 z hz θ hθ))
      _ = C * (max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)))) := by
          rw [MeasureTheory.integral_const_mul]
      _ ≤ C * (max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2) * (10 ^ 4 + 700) :=
          mul_le_mul_of_nonneg_left hang
            (mul_nonneg (mul_nonneg (mul_nonneg hC0 (sq_nonneg (max Cs 0)))
              (pow_nonneg hα.le 4)) (div_nonneg (by norm_num) (by positivity)))
  have hI : IntegrableOn (fun z : ℝ =>
      C * (max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2) * (10 ^ 4 + 700)) Work.Spaces.Iz := by
    refine (Work.Elliptic.WtoH_IntZ.1.const_mul
      (4 * (C * (max Cs 0) ^ 2 * α ^ 4 * (10 ^ 4 + 700)))).congr ?_
    filter_upwards with z
    ring
  have hint4 : (∫ z in Work.Spaces.Iz, 4 / (1 + z) ^ 2) ≤ 8 := by
    have h : (∫ z in Work.Spaces.Iz, 4 / (1 + z) ^ 2)
        = 4 * (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      ring
    rw [h]
    nlinarith [Work.Elliptic.WtoH_IntZ.2]
  rw [Work.Spaces.HkSq]
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => VsW α Φs z θ * Gs α z θ) z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          C * (max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2) * (10 ^ 4 + 700) :=
        integral_mono_of_nonneg
          (Eventually.of_forall fun z =>
            integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
          hI (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hinner z hz))
    _ = (C * (max Cs 0) ^ 2 * α ^ 4 * (10 ^ 4 + 700))
          * (∫ z in Work.Spaces.Iz, 4 / (1 + z) ^ 2) := by
        rw [show (fun z : ℝ => C * (max Cs 0) ^ 2 * α ^ 4 * (4 / (1 + z) ^ 2)
              * (10 ^ 4 + 700))
            = fun z : ℝ => (C * (max Cs 0) ^ 2 * α ^ 4 * (10 ^ 4 + 700))
              * (4 / (1 + z) ^ 2) from by
          funext z; ring]
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (C * (max Cs 0) ^ 2 * α ^ 4 * (10 ^ 4 + 700)) * 8 :=
        mul_le_mul_of_nonneg_left hint4
          (mul_nonneg (mul_nonneg (mul_nonneg hC0 (sq_nonneg (max Cs 0)))
            (pow_nonneg hα.le 4)) (by norm_num))
    _ = (C * (10 ^ 4 + 700) * 8) * (max Cs 0) ^ 2 * α ^ 4 := by ring
    _ ≤ (C * (10 ^ 4 + 700) * 8 + 1) * (max Cs 0) ^ 2 * α ^ 4 := by
        nlinarith [hA20]

end Work.FTS.Nonlinear.Pieces.RNP.row19
