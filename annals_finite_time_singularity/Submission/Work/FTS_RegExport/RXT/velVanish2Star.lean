import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.Rop_pointwiseW
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.OpenPkg.ScoefOpen
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.VsFields

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `ℛ`-slot of the star residual (part of `velVanish2`)

`|D_z^jD_θ^i (Rop α (PhiTs α Φs))| ≤ 2·10⁴·(max Cs 1·α)·min z 1` for `j + i ≤ 2` on the open
quadrant, from the `𝒲^{4,∞}`-field `RW` of `StarPkgo2` via the *proved*
`Work.FTS.NonlinRows.Rop_pointwiseW_aux` and the Stirling expansion of `D_z`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

theorem v2_zdiv_one_add_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ z / (1 + z) := by
  have h : 0 < 1 + z := by linarith
  exact div_nonneg hz h.le

theorem v2_zdiv_one_add_le_min {z : ℝ} (hz : 0 < z) : z / (1 + z) ≤ min z 1 := by
  have h1 : 0 < 1 + z := by linarith
  rcases le_total z 1 with h | h
  · rw [min_eq_left h, div_le_iff₀ h1]
    nlinarith
  · rw [min_eq_right h, div_le_one h1]
    linarith

/-- `σ(θ)·Λ(θ) = 1`, the de-weighting identity of the angular factors of `WlInf`. -/
theorem v2_sig_mul_lam {α θ : ℝ} (hs : 0 < Real.sin (2 * θ)) (ht : 0 < α + Real.sin (2 * θ)) :
    ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) = 1 := by
  have h1 : (Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5) = 1 := by
    rw [← Real.rpow_add hs, show -(α / 5) + α / 5 = 0 by ring, Real.rpow_zero]
  calc ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
      = (((Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5))
          * (α + Real.sin (2 * θ))) / (α + Real.sin (2 * θ)) := by ring
    _ = 1 := by
        rw [h1, one_mul]
        exact div_self (ne_of_gt ht)

/-! ## The `Rop`-slot of the star residual -/

/-- The four pointwise bounds for `ℛ(Φ̃_*)` produced by `Rop_pointwiseW_aux`, converted into the
form consumed below: for `i + j ≤ 2`, every `z^k ∂_z^k D_θ^i ℛ(Φ̃_*)` is bounded by
`200·(max Cs 1 · α)·z/(1+z)` on the open quadrant. -/
theorem v2_starRop_aux {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hS : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    (∀ k ≤ 4, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |z ^ k * Work.Spaces.pzIter k
          (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ 200 * (max Cs 1 * α) * (z / (1 + z))) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 2 → ∀ k : ℕ, i + k ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ →
      θ < Real.pi / 2 →
      |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i
          (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        ≤ 200 * (max Cs 1 * α) * (z / (1 + z))) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen Φs := hS.smooth
  obtain ⟨h1, h2, h3, h4⟩ := Work.FTS.NonlinRows.Rop_pointwiseW_aux hα hα1
    (Work.FTS.NonlinRows.RopW_smoothOpen_local hα hα1 hsm) hS.RW.1 hS.RW.2
  have hK0 : (0 : ℝ) ≤ max Cs 1 * α :=
    mul_nonneg (le_trans zero_le_one (le_max_right Cs 1)) hα.le
  have hh100 : (0 : ℝ) ≤ 100 * (max Cs 1 * α) := by positivity
  have hA : ∀ k ≤ 4, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |z ^ k * Work.Spaces.pzIter k (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ| ≤ 200 * (max Cs 1 * α) * (z / (1 + z)) := by
    intro k hk z θ hz hθ hθ2
    have hzk : (0 : ℝ) ≤ z ^ k := by positivity
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero]
      have h := h1 z hz θ ⟨hθ, hθ2⟩
      have he : 100 * (max Cs 1 * α) * z / (1 + z)
          = 100 * (max Cs 1 * α) * (z / (1 + z)) := by ring
      rw [he] at h
      have h0 : 0 ≤ z / (1 + z) := v2_zdiv_one_add_nonneg hz.le
      have h' : 100 * (max Cs 1 * α) * (z / (1 + z))
          ≤ 200 * (max Cs 1 * α) * (z / (1 + z)) := by
        have hk : 0 ≤ (max Cs 1 * α) * (z / (1 + z)) := mul_nonneg hK0 h0
        linarith
      exact le_trans h h'
    · have h := h2 k (by omega) z hz θ ⟨hθ, hθ2⟩
      have hpow : z ^ k * (100 * (max Cs 1 * α) / (1 + z) ^ k)
          = 100 * (max Cs 1 * α) * (z / (1 + z)) ^ k := by
        rw [div_pow]; field_simp
      have hr0 : 0 ≤ z / (1 + z) := v2_zdiv_one_add_nonneg hz.le
      have hr1 : z / (1 + z) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have hle : (z / (1 + z)) ^ k ≤ z / (1 + z) := pow_le_of_le_one hr0 hr1 (by omega : k ≠ 0)
      calc |z ^ k * Work.Spaces.pzIter k (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ| = z ^ k * |Work.Spaces.pzIter k (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ| := by
            rw [abs_mul, abs_of_nonneg hzk]
        _ ≤ z ^ k * (100 * (max Cs 1 * α) / (1 + z) ^ k) :=
            mul_le_mul_of_nonneg_left h hzk
        _ = 100 * (max Cs 1 * α) * (z / (1 + z)) ^ k := hpow
        _ ≤ 100 * (max Cs 1 * α) * (z / (1 + z)) :=
            mul_le_mul_of_nonneg_left hle hh100
        _ = 100 * ((max Cs 1 * α) * (z / (1 + z))) := by ring
        _ ≤ 200 * ((max Cs 1 * α) * (z / (1 + z))) := by
            have hk : 0 ≤ (max Cs 1 * α) * (z / (1 + z)) :=
              mul_nonneg hK0 (v2_zdiv_one_add_nonneg hz.le)
            linarith
        _ = 200 * (max Cs 1 * α) * (z / (1 + z)) := by ring
  refine ⟨hA, ?_⟩
  intro i hi hi2 k hik z θ hz hθ hθ2
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have ht : 0 < α + Real.sin (2 * θ) := by linarith
  have hΛ : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 :=
    Work.FTS.Nonlinear.Pieces.RNP.row19.lam_le_two hα hα1
      (Set.mem_Icc.mpr ⟨hθ.le, hθ2.le⟩)
  have hL0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    le_of_lt (mul_pos ht (Real.rpow_pos_of_pos hs _))
  have hzk : (0 : ℝ) ≤ z ^ k := by positivity
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero]
    have h := h4 i hi (by omega) z hz θ ⟨hθ, hθ2⟩
    have he : 100 * (max Cs 1 * α) * z / (1 + z)
        = 100 * (max Cs 1 * α) * (z / (1 + z)) := by ring
    rw [he] at h
    rw [show |Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
          = (|Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        from by rw [mul_assoc, v2_sig_mul_lam hs ht, mul_one]]
    calc (|Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        ≤ (100 * (max Cs 1 * α) * (z / (1 + z)))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_le_mul_of_nonneg_right h hL0
      _ ≤ (100 * (max Cs 1 * α) * (z / (1 + z))) * 2 :=
          mul_le_mul_of_nonneg_left hΛ (by positivity)
      _ = 200 * (max Cs 1 * α) * (z / (1 + z)) := by ring
  · have h := h3 i k hi (by omega) z hz θ ⟨hθ, hθ2⟩
    have hpow : z ^ k * (100 * (max Cs 1 * α) / (1 + z) ^ k)
        = 100 * (max Cs 1 * α) * (z / (1 + z)) ^ k := by
      rw [div_pow]; field_simp
    have hr0 : 0 ≤ z / (1 + z) := v2_zdiv_one_add_nonneg hz.le
    have hr1 : z / (1 + z) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hle : (z / (1 + z)) ^ k ≤ z / (1 + z) := pow_le_of_le_one hr0 hr1 (by omega : k ≠ 0)
    have hkey : z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        = (z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|)
          * (((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
      rw [v2_sig_mul_lam hs ht, mul_one]
    rw [abs_mul, abs_of_nonneg hzk, hkey]
    calc (z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|)
          * (((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
        = (z ^ k * (|Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
              * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
      _ ≤ (z ^ k * (100 * (max Cs 1 * α) / (1 + z) ^ k))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hzk) hL0
      _ = (100 * (max Cs 1 * α) * (z / (1 + z)) ^ k)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by rw [hpow]
      _ ≤ (100 * (max Cs 1 * α) * (z / (1 + z)))
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hh100) hL0
      _ ≤ (100 * (max Cs 1 * α) * (z / (1 + z))) * 2 :=
          mul_le_mul_of_nonneg_left hΛ (mul_nonneg hh100 hr0)
      _ = 200 * (max Cs 1 * α) * (z / (1 + z)) := by ring

/-- **The star half for the `ℛ`-slot**: every mixed derivative of order `≤ 2` of `ℛ(Φ̃_*)` is
bounded by `2·10⁴·(max Cs 1·α)·min z 1` on the open quadrant. -/
theorem v2_starRop_mixed {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hS : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i
          (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ 2 * 10 ^ 4 * (max Cs 1 * α) * min z 1 := by
  obtain ⟨hA, hB⟩ := v2_starRop_aux hα hα1 hS
  have hsm : Work.FTS.EllipticEst.SmoothOpen Φs := hS.smooth
  have hΘ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    Work.FTS.NonlinRows.RopW_ThetaFstar hα hα1
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.RopW_sub hsm hΘ
  have hRsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.RopW_Rop (α := α) hPhi
  have hM0 : (0 : ℝ) ≤ 200 * (max Cs 1 * α) := by positivity
  have hK0 : (0 : ℝ) ≤ max Cs 1 * α :=
    mul_nonneg (le_trans zero_le_one (le_max_right Cs 1)) hα.le
  intro j i hji z θ hz hθ hθ2
  have hzmin : z / (1 + z) ≤ min z 1 := v2_zdiv_one_add_le_min hz
  have hmm : (0 : ℝ) ≤ min z 1 := le_min hz.le zero_le_one
  have hle : 200 * (max Cs 1 * α) * (z / (1 + z))
      ≤ 200 * (max Cs 1 * α) * min z 1 := mul_le_mul_of_nonneg_left hzmin hM0
  have hfin : 200 * (max Cs 1 * α) * min z 1 ≤ 2 * 10 ^ 4 * (max Cs 1 * α) * min z 1 := by
    have hk : 0 ≤ (max Cs 1 * α) * min z 1 := mul_nonneg hK0 hmm
    linarith
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    rw [Work.Spaces.mixed_zero_left]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have h := hA 0 (by norm_num) z θ hz hθ hθ2
      simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero, Work.Spaces.DthIter_zero] at h
      exact le_trans (le_trans h hle) hfin
    · have h := hB i hipos (by omega) 0 (by omega) z θ hz hθ hθ2
      simp only [pow_zero, one_mul, Work.Spaces.pzIter_zero] at h
      exact le_trans (le_trans h hle) hfin
  · rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [Work.Spaces.mixed_zero_right]
      have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z' θ) (Set.Ioi 0) :=
        hRsm.curry_z ⟨hθ, hθ2⟩
      rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (h := (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) (θ := θ) hsmooth j z
        (Set.mem_Ioi.mpr hz)]
      refine le_trans (Work.Spaces.abs_sum_scoef_mul_le j
        (200 * (max Cs 1 * α) * min z 1) (fun k => z ^ k * Work.Spaces.pzIter k (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ) ?_) ?_
      · intro k hk
        exact le_trans (hA k (by omega) z θ hz hθ hθ2) hle
      · have hbell : (Work.Spaces.bell j : ℝ) ≤ 100 := by
          exact_mod_cast Work.Spaces.bell_le j (by omega)
        have h0 : 0 ≤ 200 * (max Cs 1 * α) * min z 1 := mul_nonneg hM0 hmm
        calc (Work.Spaces.bell j : ℝ) * (200 * (max Cs 1 * α) * min z 1)
            ≤ 100 * (200 * (max Cs 1 * α) * min z 1) :=
              mul_le_mul_of_nonneg_right hbell h0
          _ = 2 * 10 ^ 4 * (max Cs 1 * α) * min z 1 := by ring
    · rw [Work.Spaces.mixed]
      have hZsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) := hRsm.DthIter i
      have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
          (fun z' => Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z' θ) (Set.Ioi 0) :=
        hZsm.curry_z ⟨hθ, hθ2⟩
      rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (h := Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) (θ := θ)
        hsmooth j z (Set.mem_Ioi.mpr hz)]
      refine le_trans (Work.Spaces.abs_sum_scoef_mul_le j
        (200 * (max Cs 1 * α) * min z 1)
        (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter i (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ) ?_) ?_
      · intro k hk
        exact le_trans (hB i hipos (by omega) k (by omega) z θ hz hθ hθ2) hle
      · have hbell : (Work.Spaces.bell j : ℝ) ≤ 100 := by
          exact_mod_cast Work.Spaces.bell_le j (by omega)
        have h0 : 0 ≤ 200 * (max Cs 1 * α) * min z 1 := mul_nonneg hM0 hmm
        calc (Work.Spaces.bell j : ℝ) * (200 * (max Cs 1 * α) * min z 1)
            ≤ 100 * (200 * (max Cs 1 * α) * min z 1) :=
              mul_le_mul_of_nonneg_right hbell h0
          _ = 2 * 10 ^ 4 * (max Cs 1 * α) * min z 1 := by ring


end Work.FTS_RegExport.RXT
