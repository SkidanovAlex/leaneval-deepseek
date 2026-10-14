import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.HkSq_Vs0_mul_Gs_eq_zero
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.HkSq_VsW_mul_Gs_le =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.FbEHDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The coefficients and their `θ`-derivatives -/

/-- `sin²θ` as a function on the quadrant. -/
def EhPhi1 : ℝ → ℝ → ℝ := fun _ θ => Real.sin θ ^ 2

/-- `sin(2θ)` as a function on the quadrant. -/
def EhSin2 : ℝ → ℝ → ℝ := fun _ θ => Real.sin (2 * θ)

/-- `cos(2θ)` as a function on the quadrant. -/
def EhCos2 : ℝ → ℝ → ℝ := fun _ θ => Real.cos (2 * θ)

/-- `z/(1+z)` as a function on the quadrant. -/
def EhRho : ℝ → ℝ → ℝ := fun z _ => z / (1 + z)

/-- `(1+z)⁻¹` as a function on the quadrant. -/
def EhRhoInv : ℝ → ℝ → ℝ := fun z _ => (1 + z)⁻¹

/-- `z` as a function on the quadrant. -/
def EhZ : ℝ → ℝ → ℝ := fun z _ => z

/-- `∂_θ(sin²θ) = 2 sinθ cosθ = sin 2θ`. -/
def EhDSinSq : ℝ → ℝ → ℝ := fun _ θ => 2 * Real.sin θ * Real.cos θ

/-- `∂_θ(sin 2θ) = 2 cos 2θ`. -/
def EhDSin2 : ℝ → ℝ → ℝ := fun _ θ => 2 * Real.cos (2 * θ)

/-- `EhSin2 = EhDSinSq`, i.e. `sin 2θ = 2 sinθ cosθ`. -/
theorem eh_sin2_eq_dsinsq (z θ : ℝ) : EhSin2 z θ = EhDSinSq z θ := by
  simp only [EhSin2, EhDSinSq, Real.sin_two_mul]


/-! ## Smoothness of the coefficients -/

theorem eh_smooth_ph1 : Work.FTS.EllipticEst.SmoothOpen EhPhi1 := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h : ContDiff ℝ n (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) :=
    (Real.contDiff_sin.comp contDiff_snd).pow 2
  exact h.contDiffOn

theorem eh_smooth_sin2 : Work.FTS.EllipticEst.SmoothOpen EhSin2 := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h1 : ContDiff ℝ n (fun p : ℝ × ℝ => (2 : ℝ) * p.2) := contDiff_const.mul contDiff_snd
  have h : ContDiff ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) := Real.contDiff_sin.comp h1
  exact h.contDiffOn

theorem eh_smooth_cos2 : Work.FTS.EllipticEst.SmoothOpen EhCos2 := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h1 : ContDiff ℝ n (fun p : ℝ × ℝ => (2 : ℝ) * p.2) := contDiff_const.mul contDiff_snd
  have h : ContDiff ℝ n (fun p : ℝ × ℝ => Real.cos (2 * p.2)) := Real.contDiff_cos.comp h1
  exact h.contDiffOn

theorem eh_smooth_z : Work.FTS.EllipticEst.SmoothOpen EhZ := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have h : ContDiff ℝ n (fun p : ℝ × ℝ => p.1) := contDiff_fst
  exact h.contDiffOn

theorem eh_smooth_dsinsq : Work.FTS.EllipticEst.SmoothOpen EhDSinSq :=
  Work.FTS.PhiStar.CoreAux.SmoothOpen.congr eh_smooth_sin2
    (fun z θ _ _ _ => eh_sin2_eq_dsinsq z θ)

theorem eh_smooth_dsin2 : Work.FTS.EllipticEst.SmoothOpen EhDSin2 :=
  Work.FTS.PhiStar.CoreAux.SmoothOpen.congr
    (Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul (f := EhCos2) eh_smooth_cos2 2)
    (fun z θ _ _ _ => rfl)

theorem eh_smooth_rhoinv : Work.FTS.EllipticEst.SmoothOpen EhRhoInv := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have hfull : ContDiffOn ℝ n (fun p : ℝ × ℝ => ((1 : ℝ) + p.1)⁻¹)
      (Work.FTS.EllipticEst.Q0) := by
    have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (1 : ℝ) + p.1) (Work.FTS.EllipticEst.Q0) :=
      (contDiff_const.add contDiff_fst).contDiffOn
    refine h1.inv fun p hp => ?_
    have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    intro h
    linarith
  refine hfull.congr fun p hp => ?_
  show ((1 : ℝ) + p.1)⁻¹ = Function.uncurry EhRhoInv p
  simp only [EhRhoInv, Function.uncurry]

theorem eh_smooth_rho : Work.FTS.EllipticEst.SmoothOpen EhRho := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun n => ?_
  have hfull : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 * ((1 : ℝ) + p.1)⁻¹)
      (Work.FTS.EllipticEst.Q0) := by
    have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (1 : ℝ) + p.1) (Work.FTS.EllipticEst.Q0) :=
      (contDiff_const.add contDiff_fst).contDiffOn
    have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => ((1 : ℝ) + p.1)⁻¹)
        (Work.FTS.EllipticEst.Q0) := h1.inv fun p hp => by
      have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      intro h
      linarith
    exact contDiffOn_fst.mul h2
  refine hfull.congr fun p hp => ?_
  show p.1 * ((1 : ℝ) + p.1)⁻¹ = Function.uncurry EhRho p
  simp only [EhRho, Function.uncurry]
  rw [div_eq_mul_inv]

/-! ## The `θ`-derivatives of the coefficients -/

theorem eh_pth_ph1 (z θ : ℝ) : Work.Spaces.pth EhPhi1 z θ = EhSin2 z θ := by
  show deriv (fun θ' : ℝ => Real.sin θ' ^ 2) θ = Real.sin (2 * θ)
  have h : HasDerivAt (fun θ' : ℝ => Real.sin θ' ^ 2)
      (2 * Real.sin θ ^ (2 - 1) * Real.cos θ) θ := (Real.hasDerivAt_sin θ).pow 2
  rw [h.deriv, Real.sin_two_mul]
  ring

theorem eh_pth_sin2 (z θ : ℝ) : Work.Spaces.pth EhSin2 z θ = EhDSin2 z θ := by
  show deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ)
  have h1 : HasDerivAt (fun θ' : ℝ => (2 : ℝ) * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  rw [h2.deriv]
  ring


theorem eh_pth_rhoinv (z θ : ℝ) : Work.Spaces.pth EhRhoInv z θ = 0 := by
  show deriv (fun _ : ℝ => (1 + z)⁻¹) θ = 0
  rw [deriv_const]


/-! ## `F0`-bounds for the two angular derivatives -/

theorem eh_F0_dsinsq {m : ℕ} {A : ℝ} (h : Work.FTS.PhiStar.F0 m A EhSin2) :
    Work.FTS.PhiStar.F0 m A EhDSinSq :=
  F0_congr (f := EhDSinSq) (g := EhSin2) (fun z θ _ _ _ => (eh_sin2_eq_dsinsq z θ).symm) h


/-! ## The body, its `θ`-derivative, and the two canonical forms -/

/-- `X = Y/(z+1) + z∂_zY`, the bracket multiplying `2α sin²θ` in `EH`. -/
def EhX (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Y z θ * EhRhoInv z θ + Yblk Y z θ

/-- `∂_θX = ∂_θY/(z+1) + z∂_z(∂_θY)`. -/
def EhDX (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ + Yblk (Work.Spaces.pth Y) z θ

/-- **The canonical form of `EH α Y`**, a sum of products of the bounded coefficients with the
blocks `Y`, `z∂_zY`, `∂_θY`. -/
def EhC (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    2 * Y z θ
      + ((2 * α) * (EhPhi1 z θ * EhX Y z θ)
          + EhSin2 z θ * Work.Spaces.pth Y z θ)

/-- **The canonical form of `∂_θ(EH α Y)`**: the Leibniz expansion, a sum of products of the
coefficients with the blocks `∂_θY`, `z∂_z(∂_θY)`, `D_θ(∂_θY)`. -/
def EhD (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    2 * Work.Spaces.pth Y z θ
      + ((2 * α) * (EhDSinSq z θ * EhX Y z θ + EhPhi1 z θ * EhDX Y z θ)
          + (EhDSin2 z θ * Work.Spaces.pth Y z θ
              + Work.Spaces.Dth (Work.Spaces.pth Y) z θ))

/-! ## Smoothness of the pieces -/

theorem eh_smooth_yblk {Y : ℝ → ℝ → ℝ} (hY : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (Yblk Y) := by
  have h : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Y z θ) :=
    Fbq_smoothOpen_mul (f := fun z _ : ℝ => z) (g := Work.Spaces.pz Y) eh_smooth_z hY.pz
  exact h

theorem eh_smooth_EhX {Y : ℝ → ℝ → ℝ} (hY : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (EhX Y) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Y z θ * EhRhoInv z θ) :=
    Fbq_smoothOpen_mul (f := Y) (g := EhRhoInv) hY eh_smooth_rhoinv
  have h2 : Work.FTS.EllipticEst.SmoothOpen (Yblk Y) := eh_smooth_yblk hY
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Y z θ * EhRhoInv z θ + Yblk Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add (f := fun z θ => Y z θ * EhRhoInv z θ)
      (g := Yblk Y) h1 h2
  exact h3

theorem eh_smooth_EhDX {Y : ℝ → ℝ → ℝ} (hY : Work.FTS.EllipticEst.SmoothOpen Y) :
    Work.FTS.EllipticEst.SmoothOpen (EhDX Y) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ) :=
    Fbq_smoothOpen_mul (f := Work.Spaces.pth Y) (g := EhRhoInv) hY.pth eh_smooth_rhoinv
  have h2 : Work.FTS.EllipticEst.SmoothOpen (Yblk (Work.Spaces.pth Y)) := eh_smooth_yblk hY.pth
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ + Yblk (Work.Spaces.pth Y) z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add
      (f := fun z θ => Work.Spaces.pth Y z θ * EhRhoInv z θ)
      (g := Yblk (Work.Spaces.pth Y)) h1 h2
  exact h3



/-! ## Scalar multiples in the shifted class -/

theorem Fb_const_mul {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (c : ℝ)
    (hf : Work.FTS.PhiStar.Fb n K f) :
    Work.FTS.PhiStar.Fb n (|c| * K) (fun z θ => c * f z θ) := by
  have h2 : Work.FTS.PhiStar.F0 n (|c| * K)
      (Work.Spaces.pth (fun z θ => c * f z θ)) := by
    simpa only [pth_const_mul] using F0_const_mul c hf.fd
  exact ⟨F0_const_mul c hf.f0, h2⟩

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.CoreAux.Fb_EV_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.FTS.PhiStar.CoreAux


/-! ## The coefficient package -/

private theorem EVCoef_local {A : ℝ} (hA : 1 ≤ A) (hphi : F0 6 A EVphi)
    (hsin : F0 6 A EVsin) (hrho : F0 6 A EVrho) : EVCoef A := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have sPhi : EllipticEst.SmoothOpen EVphi := by
    refine EllipticEst.smoothOpen_of_forall fun n => ?_
    have h : Function.uncurry EVphi
        = fun p : ℝ × ℝ => Real.cos p.2 ^ 2 - 2 * Real.sin p.2 ^ 2 := rfl
    rw [h]
    fun_prop
  have sSin : EllipticEst.SmoothOpen EVsin := by
    refine EllipticEst.smoothOpen_of_forall fun n => ?_
    have h : Function.uncurry EVsin = fun p : ℝ × ℝ => Real.sin (2 * p.2) := rfl
    rw [h]
    fun_prop
  have sCos2 : EllipticEst.SmoothOpen (fun _ θ => Real.cos (2 * θ)) := by
    refine EllipticEst.smoothOpen_of_forall fun n => ?_
    have h : Function.uncurry (fun _ θ : ℝ => Real.cos (2 * θ))
        = fun p : ℝ × ℝ => Real.cos (2 * p.2) := rfl
    rw [h]
    fun_prop
  have sRho : EllipticEst.SmoothOpen EVrho := by
    refine EllipticEst.smoothOpen_of_forall fun n => ?_
    have h : Function.uncurry EVrho = fun p : ℝ × ℝ => p.1 / (1 + p.1) := rfl
    rw [h]
    exact ContDiffOn.div contDiffOn_fst (contDiffOn_const.add contDiffOn_fst)
      (fun p hp => by have h1 := (EllipticEst.mem_Q0.mp hp).1; positivity)
  have hdPhi : ∀ z θ : ℝ, Work.Spaces.pth EVphi z θ = -3 * Real.sin (2 * θ) := by
    intro z θ
    show deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ
      = -3 * Real.sin (2 * θ)
    have h1 : HasDerivAt (fun θ' : ℝ => Real.cos θ' ^ 2)
        (2 * Real.cos θ * (-Real.sin θ)) θ := by
      refine ((Real.hasDerivAt_cos θ).pow 2).congr_deriv ?_
      norm_num
    have h2 : HasDerivAt (fun θ' : ℝ => 2 * Real.sin θ' ^ 2)
        (2 * (2 * Real.sin θ * Real.cos θ)) θ := by
      refine (((Real.hasDerivAt_sin θ).pow 2).const_mul (2 : ℝ)).congr_deriv ?_
      norm_num
    have h3 : HasDerivAt (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2)
        (2 * Real.cos θ * (-Real.sin θ) - 2 * (2 * Real.sin θ * Real.cos θ)) θ :=
      h1.sub h2
    rw [h3.deriv, Real.sin_two_mul]
    ring
  have hdSin : ∀ z θ : ℝ, Work.Spaces.pth EVsin z θ = 2 * Real.cos (2 * θ) := by
    intro z θ
    show deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ)
    have hinner : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ hinner
    rw [h.deriv]
    ring
  have hdRho : ∀ z θ : ℝ, Work.Spaces.pth EVrho z θ = 0 := by
    intro z θ
    show deriv (fun _ : ℝ => z / (1 + z)) θ = 0
    exact deriv_const θ (z / (1 + z))
  have sdPhi : EllipticEst.SmoothOpen (Work.Spaces.pth EVphi) := by
    refine SmoothOpen.congr (f := fun _ θ : ℝ => -3 * Real.sin (2 * θ)) ?_ ?_
    · refine EllipticEst.smoothOpen_of_forall fun n => ?_
      have h : Function.uncurry (fun _ θ : ℝ => -3 * Real.sin (2 * θ))
          = fun p : ℝ × ℝ => -3 * Real.sin (2 * p.2) := rfl
      rw [h]
      fun_prop
    · intro z θ _ _ _
      exact (hdPhi z θ).symm
  have sdSin : EllipticEst.SmoothOpen (Work.Spaces.pth EVsin) := by
    refine SmoothOpen.congr (f := fun _ θ : ℝ => 2 * Real.cos (2 * θ)) ?_ ?_
    · exact SmoothOpen.const_mul sCos2 2
    · intro z θ _ _ _
      exact (hdSin z θ).symm
  have h2phi : F0 6 (2 * A) (fun z θ => 2 * EVphi z θ) := by
    have h := F0_const_mul (2 : ℝ) hphi
    simpa using h
  have h3 : F0 6 (2 * A + 1) (fun z θ => 2 * EVphi z θ + 1) := by
    have h := F0_add (SmoothOpen.const_mul sPhi 2) (SmoothOpen.const 1) h2phi (F0.const 6 1)
    simpa using h
  have h4 : F0 6 ((1 / 3) * (2 * A + 1)) (fun z θ => (1 / 3) * (2 * EVphi z θ + 1)) := by
    have h := F0_const_mul ((1 / 3 : ℝ)) h3
    simpa using h
  have hCos2 : F0 6 A (fun _ θ => Real.cos (2 * θ)) := by
    refine (F0_congr (fun z θ _ _ _ => ?_) h4).mono le_rfl ?_
    · simp only [EVphi]
      rw [Real.cos_two_mul]
      have hs := Real.sin_sq_add_cos_sq θ
      nlinarith [hs]
    · linarith
  exact ⟨sPhi, sSin, sRho, sCos2, sdPhi, sdSin, hphi, hsin, hrho, hCos2, hdPhi, hdSin,
    hdRho⟩

/-! ## The assembly -/

private theorem absorb {A K c : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) {p : ℕ} (hp : p ≤ 4)
    (hc : c ≤ EVC) : c * A ^ p * (K + 1) ≤ EVC * A ^ 4 * (K + 1) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hK1 : (0 : ℝ) ≤ K + 1 := by linarith
  have hp4 : A ^ p ≤ A ^ 4 := pow_le_pow_right₀ hA hp
  have h1 : c * A ^ p ≤ EVC * A ^ 4 :=
    calc c * A ^ p ≤ EVC * A ^ p := mul_le_mul_of_nonneg_right hc (pow_nonneg hA0 p)
      _ ≤ EVC * A ^ 4 := mul_le_mul_of_nonneg_left hp4 (by norm_num [EVC])
  exact mul_le_mul_of_nonneg_right h1 hK1

theorem Fb_EV_bound_aux {A K : ℝ} {Y : ℝ → ℝ → ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hYs : EllipticEst.SmoothOpen Y) (hC : EVCoef A) (hY : Fb 6 (A * (K + 1)) Y) :
    Fb 4 (EVC * A ^ 4 * (K + 1)) (EVz Y) ∧ Fb 4 (EVC * A ^ 4 * (K + 1)) (EV Y) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hM : (0 : ℝ) ≤ A * (K + 1) := mul_nonneg hA0 (by linarith)
  have hY4 : Fb 4 (A * (K + 1)) Y := hY.mono (by norm_num) le_rfl
  have hphi4 : F0 4 A EVphi := hC.f0Phi.mono (by norm_num) le_rfl
  have hsin4 : F0 4 A EVsin := hC.f0Sin.mono (by norm_num) le_rfl
  have hrho4 : F0 4 A EVrho := hC.f0Rho.mono (by norm_num) le_rfl
  have hcos4 : F0 4 A (fun _ θ => Real.cos (2 * θ)) := hC.f0Cos2.mono (by norm_num) le_rfl
  have h2phi : F0 4 (2 * A) (fun z θ => 2 * EVphi z θ) := by
    have h := F0_const_mul (2 : ℝ) hphi4
    simpa using h
  have h6sin : F0 4 (6 * A) (fun z θ => -6 * EVsin z θ) := by
    have h := F0_const_mul (-6 : ℝ) hsin4
    simpa using h
  have h2cos : F0 4 (2 * A) (fun z θ => 2 * Real.cos (2 * θ)) := by
    have h := F0_const_mul (2 : ℝ) hcos4
    simpa using h
  have h2A : (0 : ℝ) ≤ 2 * A := by linarith
  have h6A : (0 : ℝ) ≤ 6 * A := by linarith
  have hK1 : (0 : ℝ) ≤ K + 1 := by linarith
  have h200 : (0 : ℝ) ≤ 200 * A ^ 2 * (K + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg A)) hK1
  have s2phi : EllipticEst.SmoothOpen (fun z θ => 2 * EVphi z θ) :=
    SmoothOpen.const_mul hC.smoothPhi 2
  have s6sin : EllipticEst.SmoothOpen (fun z θ => -6 * EVsin z θ) :=
    SmoothOpen.const_mul hC.smoothSin (-6)
  have s2cos : EllipticEst.SmoothOpen (fun z θ => 2 * Real.cos (2 * θ)) :=
    SmoothOpen.const_mul hC.smoothCos2 2
  have spY : EllipticEst.SmoothOpen (Work.Spaces.pth Y) := hYs.pth
  have sppY : EllipticEst.SmoothOpen (Work.Spaces.pth (Work.Spaces.pth Y)) :=
    EllipticEst.SmoothOpen.pth spY
  have s2phiY : EllipticEst.SmoothOpen ((fun z θ => 2 * EVphi z θ) * Y) :=
    Fbq_smoothOpen_mul s2phi hYs
  have ssinpY : EllipticEst.SmoothOpen (EVsin * Work.Spaces.pth Y) :=
    Fbq_smoothOpen_mul hC.smoothSin spY
  have hsplit : EVz Y = (fun z θ => 2 * EVphi z θ) * Y + EVsin * Work.Spaces.pth Y := by
    funext a b
    simp only [EVz, Tblk, EVsin, EVphi, Work.Construction.s2, Pi.add_apply, Pi.mul_apply]
  have sEvz : EllipticEst.SmoothOpen (EVz Y) := by
    rw [hsplit]
    exact SmoothOpen.add s2phiY ssinpY
  -- ## the `F0`-half for `EVz`
  have t1 : F0 4 (32 * A ^ 2 * (K + 1)) ((fun z θ => 2 * EVphi z θ) * Y) := by
    have h := F0_mul h2A hM s2phi hYs h2phi hY4.f0
    have hc : (2 : ℝ) ^ 4 * (2 * A) * (A * (K + 1)) = 32 * A ^ 2 * (K + 1) := by ring
    rwa [hc] at h
  have t2 : F0 4 (16 * A ^ 2 * (K + 1)) (EVsin * Work.Spaces.pth Y) := by
    have h := F0_mul hA0 hM hC.smoothSin spY hsin4 hY4.fd
    have hc : (2 : ℝ) ^ 4 * A * (A * (K + 1)) = 16 * A ^ 2 * (K + 1) := by ring
    rwa [hc] at h
  have hsumz : F0 4 (48 * A ^ 2 * (K + 1))
      ((fun z θ => 2 * EVphi z θ) * Y + EVsin * Work.Spaces.pth Y) := by
    have h := F0_add s2phiY ssinpY t1 t2
    have hc : 32 * A ^ 2 * (K + 1) + 16 * A ^ 2 * (K + 1) = 48 * A ^ 2 * (K + 1) := by ring
    rwa [hc] at h
  have hF0z : F0 4 (48 * A ^ 2 * (K + 1)) (EVz Y) := by
    refine F0_congr (fun z θ _ _ _ => ?_) hsumz
    rw [hsplit]
  -- ## the `∂_θ`-half for `EVz`
  let A1 : ℝ → ℝ → ℝ := fun z θ => 2 * EVphi z θ * Y z θ
  let A2 : ℝ → ℝ → ℝ := fun z θ => EVsin z θ * Work.Spaces.pth Y z θ
  let T1 : ℝ → ℝ → ℝ := fun z θ => -6 * EVsin z θ * Y z θ
  let T2 : ℝ → ℝ → ℝ := fun z θ => 2 * EVphi z θ * Work.Spaces.pth Y z θ
  let T3 : ℝ → ℝ → ℝ := fun z θ => 2 * Real.cos (2 * θ) * Work.Spaces.pth Y z θ
  let T4 : ℝ → ℝ → ℝ := fun z θ => EVsin z θ * Work.Spaces.pth (Work.Spaces.pth Y) z θ
  have hT1 : F0 4 (96 * A ^ 2 * (K + 1)) T1 := by
    have h := F0_mul h6A hM s6sin hYs h6sin hY4.f0
    have hc : (2 : ℝ) ^ 4 * (6 * A) * (A * (K + 1)) = 96 * A ^ 2 * (K + 1) := by ring
    rw [hc] at h
    simpa only [T1, Pi.mul_apply] using h
  have hT2 : F0 4 (32 * A ^ 2 * (K + 1)) T2 := by
    have h := F0_mul h2A hM s2phi spY h2phi hY4.fd
    have hc : (2 : ℝ) ^ 4 * (2 * A) * (A * (K + 1)) = 32 * A ^ 2 * (K + 1) := by ring
    rw [hc] at h
    simpa only [T2, Pi.mul_apply] using h
  have hT3 : F0 4 (32 * A ^ 2 * (K + 1)) T3 := by
    have h := F0_mul h2A hM s2cos spY h2cos hY4.fd
    have hc : (2 : ℝ) ^ 4 * (2 * A) * (A * (K + 1)) = 32 * A ^ 2 * (K + 1) := by ring
    rw [hc] at h
    simpa only [T3, Pi.mul_apply] using h
  have hT4 : F0 4 (A * (K + 1)) T4 := by
    have hpm : F0 5 (A * (K + 1)) (Work.Spaces.pth Y) := hY.fd.mono (by norm_num) le_rfl
    refine F0_congr (f := T4) (g := Work.Spaces.Dth (Work.Spaces.pth Y)) (fun z θ _ _ _ => ?_)
      (F0_Dth hpm)
    simp only [T4, Work.Spaces.Dth, EVsin]
  have hid : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EVz Y) z θ = ((T1 + T2) + (T3 + T4)) z θ := by
    intro z θ hz hθ hθ'
    have h4 : Work.Spaces.pth (fun z θ => 2 * EVphi z θ) z θ = -6 * EVsin z θ := by
      have h2 := congrFun (congrFun (pth_const_mul (2 : ℝ) EVphi) z) θ
      rw [h2, hC.dPhi z θ]
      simp only [EVsin]
      ring
    have h5 : Work.Spaces.pth (fun z θ => EVsin z θ) z θ = 2 * Real.cos (2 * θ) := by
      simpa only [] using hC.dSin z θ
    have hA1 : Work.Spaces.pth A1 z θ = -6 * EVsin z θ * Y z θ
        + 2 * EVphi z θ * Work.Spaces.pth Y z θ := by
      have h := Fbq_pth_mul (f := fun z θ => 2 * EVphi z θ) (g := Y) s2phi hYs z θ hz hθ hθ'
      simp only [A1] at h ⊢
      simpa only [Pi.mul_apply, h4] using h
    have hA2 : Work.Spaces.pth A2 z θ = 2 * Real.cos (2 * θ) * Work.Spaces.pth Y z θ
        + EVsin z θ * Work.Spaces.pth (Work.Spaces.pth Y) z θ := by
      have h := Fbq_pth_mul (f := fun z θ => EVsin z θ) (g := Work.Spaces.pth Y)
        hC.smoothSin spY z θ hz hθ hθ'
      simp only [A2] at h ⊢
      simpa only [Pi.mul_apply, h5] using h
    have hEq : EVz Y = fun z θ => A1 z θ + A2 z θ := by
      funext a b
      simp only [EVz, Tblk, A1, A2, EVsin, EVphi, Work.Construction.s2]
    have hsum : Work.Spaces.pth (EVz Y) z θ = Work.Spaces.pth A1 z θ + Work.Spaces.pth A2 z θ := by
      have h := pth_add_Q0 (f := A1) (g := A2)
        (SmoothOpen.congr s2phiY (fun a b _ _ _ => by simp only [A1, Pi.mul_apply]))
        (SmoothOpen.congr ssinpY (fun a b _ _ _ => by simp only [A2, Pi.mul_apply]))
        z θ hz hθ hθ'
      simpa only [hEq] using h
    rw [hsum, hA1, hA2]
    simp only [T1, T2, T3, T4, Pi.add_apply, EVsin]
  have hsumd : F0 4 ((96 * A ^ 2 * (K + 1) + 32 * A ^ 2 * (K + 1))
      + (32 * A ^ 2 * (K + 1) + A * (K + 1))) ((T1 + T2) + (T3 + T4)) :=
    F0_add (SmoothOpen.add (Fbq_smoothOpen_mul s6sin hYs) (Fbq_smoothOpen_mul s2phi spY))
      (SmoothOpen.add (Fbq_smoothOpen_mul s2cos spY) (Fbq_smoothOpen_mul hC.smoothSin sppY))
      (F0_add (Fbq_smoothOpen_mul s6sin hYs) (Fbq_smoothOpen_mul s2phi spY) hT1 hT2)
      (F0_add (Fbq_smoothOpen_mul s2cos spY) (Fbq_smoothOpen_mul hC.smoothSin sppY) hT3 hT4)
  have hF0d : F0 4 (200 * A ^ 2 * (K + 1)) (Work.Spaces.pth (EVz Y)) := by
    refine (F0_congr hid hsumd).mono le_rfl ?_
    have hx : (0 : ℝ) ≤ A ^ 2 * (K + 1) := mul_nonneg (pow_nonneg hA0 2) hK1
    have hy : A * (K + 1) ≤ A ^ 2 * (K + 1) := by
      refine mul_le_mul_of_nonneg_right ?_ hK1
      nlinarith [hA]
    linarith
  have hEVz : Fb 4 (200 * A ^ 2 * (K + 1)) (EVz Y) :=
    ⟨hF0z.mono le_rfl (by
        have hx : (0 : ℝ) ≤ A ^ 2 * (K + 1) := mul_nonneg (pow_nonneg hA0 2) hK1
        linarith), hF0d⟩
  -- ## the two halves for `EV`
  have hEVfun : ∀ z θ : ℝ, EV Y z θ = (EVrho * EVz Y) z θ := by
    intro z θ
    simp only [EV, EVrho, Pi.mul_apply]
    rw [add_comm 1 z]
  have hF0ev : F0 4 (3200 * A ^ 3 * (K + 1)) (EV Y) := by
    have h := F0_mul hA0 h200 hC.smoothRho sEvz hrho4 hEVz.f0
    have hc : (2 : ℝ) ^ 4 * A * (200 * A ^ 2 * (K + 1)) = 3200 * A ^ 3 * (K + 1) := by ring
    rw [hc] at h
    exact F0_congr (fun z θ _ _ _ => hEVfun z θ) h
  have hpthEV : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EV Y) z θ = (EVrho * Work.Spaces.pth (EVz Y)) z θ := by
    intro z θ hz hθ hθ'
    have h1 : Work.Spaces.pth (EV Y) z θ
        = Work.Spaces.pth (fun z θ => EVrho z θ * EVz Y z θ) z θ :=
      pth_congr_Q0 (fun a b _ _ _ => hEVfun a b) z θ hz hθ hθ'
    rw [h1, Fbq_pth_mul (f := EVrho) (g := EVz Y) hC.smoothRho sEvz z θ hz hθ hθ',
      hC.dRho z θ]
    simp only [Pi.mul_apply, zero_mul, zero_add]
  have hFdev : F0 4 (3200 * A ^ 3 * (K + 1)) (Work.Spaces.pth (EV Y)) := by
    have h := F0_mul hA0 h200 hC.smoothRho sEvz.pth hrho4 hEVz.fd
    have hc : (2 : ℝ) ^ 4 * A * (200 * A ^ 2 * (K + 1)) = 3200 * A ^ 3 * (K + 1) := by ring
    rw [hc] at h
    exact F0_congr (fun z θ hz hθ hθ' => hpthEV z θ hz hθ hθ') h
  refine ⟨hEVz.mono le_rfl (absorb hA hK (p := 2) (by norm_num) (by norm_num [EVC])),
    hF0ev.mono le_rfl (absorb hA hK (p := 3) (by norm_num) (by norm_num [EVC])),
    hFdev.mono le_rfl (absorb hA hK (p := 3) (by norm_num) (by norm_num [EVC]))⟩

theorem Fb_EV_bound : ∃ C : ℝ, 0 < C ∧ ∀ (K A : ℝ) (Y : ℝ → ℝ → ℝ), 0 ≤ K → 1 ≤ A → Work.FTS.EllipticEst.SmoothOpen Y → Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) → Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) → Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) → Work.FTS.PhiStar.Fb 6 (A * (K + 1)) Y → Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * (K + 1)) (Work.FTS.PhiStar.EVz Y) ∧ Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * (K + 1)) (Work.FTS.PhiStar.EV Y) := by
  refine ⟨EVC, by norm_num [EVC], ?_⟩
  intro K A Y hK hA hYs hphi hsin hrho hY
  exact Fb_EV_bound_aux hA hK hYs (EVCoef_local hA hphi hsin hrho) hY

end Work.FTS.PhiStar.CoreAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWApi.FlatW_ycheckSmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWApi

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Monotonicity of the flat class in its constant -/

lemma flatW_mono {l : ℕ} {f : ℝ → ℝ → ℝ} {K K' : ℝ}
    (h : Work.FTS.VocabO2.FlatW l f K) (hle : K ≤ K') : Work.FTS.VocabO2.FlatW l f K' := by
  intro z θ hz hθ hπ
  obtain ⟨h1, h2⟩ := h z θ hz hθ hπ
  exact ⟨fun k hk => le_trans (h1 k hk) hle, fun k i hki => le_trans (h2 k i hki) hle⟩

/-! ## Closure of `SmoothOpen` under the operations used below -/

lemma smoothOpen_of_radial {g : ℝ → ℝ} (hg : ∀ n : ℕ, ContDiffOn ℝ n g (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => g z) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hfun : Function.uncurry (fun z _ : ℝ => g z) = fun p : ℝ × ℝ => g p.1 := rfl
  rw [hfun]
  exact (hg n).comp contDiffOn_fst (fun p hp => (Set.mem_prod.mp hp).1)

lemma smoothOpen_of_angular {g : ℝ → ℝ} (hg : ∀ n : ℕ, ContDiffOn ℝ n g (Set.Ioo 0 (π/2))) :
    Work.FTS.EllipticEst.SmoothOpen (fun _ θ => g θ) := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hfun : Function.uncurry (fun _ θ : ℝ => g θ) = fun p : ℝ × ℝ => g p.2 := rfl
  rw [hfun]
  exact (hg n).comp contDiffOn_snd (fun p hp => (Set.mem_prod.mp hp).2)

lemma smoothOpen_mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) := by
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ * g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p * Function.uncurry g p := rfl
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ * g z θ)) Work.FTS.EllipticEst.Q0
  rw [hfun]
  exact (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) _
      from hf).mul (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) _ from hg)

lemma smoothOpen_add {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) := by
  have hfun : Function.uncurry (fun z θ : ℝ => f z θ + g z θ)
      = fun p : ℝ × ℝ => Function.uncurry f p + Function.uncurry g p := rfl
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ : ℝ => f z θ + g z θ)) Work.FTS.EllipticEst.Q0
  rw [hfun]
  exact (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) _
      from hf).add (show ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) _ from hg)

lemma smoothOpen_congr {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π/2 → f z θ = g z θ) :
    Work.FTS.EllipticEst.SmoothOpen g := by
  refine Work.FTS.EllipticEst.smoothOpen_of_forall (fun n => ?_)
  have hf' := (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf n
  refine hf'.congr (fun p hp => ?_)
  obtain ⟨hz, hθ, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact (h p.1 p.2 hz hθ hθ2).symm

/-! ## The one-variable smoothness facts -/

lemma contDiffOn_zdiv (n : ℕ) : ContDiffOn ℝ n (fun z : ℝ => (z + 1) / z) (Set.Ioi 0) := by
  refine ContDiffOn.div (contDiffOn_id.add contDiffOn_const) contDiffOn_id ?_
  intro z hz; exact ne_of_gt hz

lemma contDiffOn_two_div_one_add (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun z : ℝ => α * (2 / (1 + z))) (Set.Ioi 0) := by
  have heq : (fun z : ℝ => α * (2 / (1 + z))) = fun z : ℝ => (2 * α) / (1 + z) := by
    funext z; ring
  rw [heq]
  refine ContDiffOn.div contDiffOn_const (contDiffOn_const.add contDiffOn_id) ?_
  intro z hz
  have hz' : (0:ℝ) < z := hz
  exact ne_of_gt (by linarith : (0:ℝ) < 1 + z)

lemma contDiffOn_inv_s2 (n : ℕ) :
    ContDiffOn ℝ n (fun θ : ℝ => (1:ℝ) / Work.Construction.s2 θ) (Set.Ioo 0 (π/2)) := by
  have h : (fun θ : ℝ => (1:ℝ) / Work.Construction.s2 θ)
      = fun θ : ℝ => (1:ℝ) / Real.sin (2*θ) := by
    funext θ; rw [show Work.Construction.s2 θ = Real.sin (2*θ) from rfl]
  rw [h]
  refine ContDiffOn.div contDiffOn_const ?_ ?_
  · fun_prop
  · intro θ hθ
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

lemma contDiffOn_psiDiv (α : ℝ) (ψ : ℝ → ℝ) (hang : Work.FTS.PhiStar.AngModel α ψ) (n : ℕ) :
    ContDiffOn ℝ n (fun θ : ℝ => ψ θ / Work.Construction.s2 θ) (Set.Ioo 0 (π/2)) := by
  refine ContDiffOn.div ?_ ?_ ?_
  · exact hang.smooth.of_le (by
      rw [show Work.Stability.smoothOrder = ((⊤:ℕ∞):WithTop ℕ∞) from rfl]
      exact_mod_cast le_top)
  · rw [show Work.Construction.s2 = fun θ : ℝ => Real.sin (2 * θ) from rfl]
    fun_prop
  · intro θ hθ
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))

lemma contDiffOn_aprof (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1/4) (n : ℕ) :
    ContDiffOn ℝ n (Work.FTS.PhiStar.Aprof α) (Set.Ioi 0) := by
  unfold Work.FTS.PhiStar.Aprof
  refine ContDiffOn.sub (Work.FTS.PhiStar.GzProfile_smooth hα hα4 n) ?_
  unfold Work.FTS.PhiStar.ThetaProfile
  refine ContDiffOn.div contDiffOn_const (contDiffOn_const.mul (contDiffOn_const.add contDiffOn_id)) ?_
  intro z hz
  have hz' : (0:ℝ) < z := hz
  exact ne_of_gt (by linarith : (0:ℝ) < 2 * (1 + z))

/-! ## The flat estimate for the radial factor `α·2/(1+z)` -/

/-- `∂_z (c/(1+z)^n) = -c·n/(1+z)^{n+1}`. -/
lemma deriv_const_div_pow (c : ℝ) (n : ℕ) (z : ℝ) (hz : (1 : ℝ) + z ≠ 0) :
    deriv (fun w : ℝ => c / (1 + w) ^ n) z = -c * (n : ℝ) / (1 + z) ^ (n + 1) := by
  have h1 : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
    simpa using (hasDerivAt_id z).const_add 1
  have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ n) ((n : ℝ) * (1 + z) ^ (n - 1) * 1) z :=
    h1.pow n
  have h3 : HasDerivAt (fun w : ℝ => c / (1 + w) ^ n)
      ((0 * (1 + z) ^ n - c * ((n : ℝ) * (1 + z) ^ (n - 1) * 1)) / ((1 + z) ^ n) ^ 2) z :=
    (hasDerivAt_const z c).div h2 (by positivity)
  rw [h3.deriv]
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; norm_num
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hpow : (1 + z) ^ (n - 1) * (1 + z) ^ (n + 1) = (1 + z) ^ (2 * n) := by
      rw [← pow_add]; congr 1; omega
    have hsq : ((1 + z) ^ n) ^ 2 = (1 + z) ^ (2 * n) := by
      rw [show 2 * n = n + n from by ring, pow_add, pow_two]
    rw [hsq]
    rw [show (0 * (1 + z) ^ n - c * ((n : ℝ) * (1 + z) ^ (n - 1) * 1)) / (1 + z) ^ (2 * n)
        = -(c * (n : ℝ) * (1 + z) ^ (n - 1)) / (1 + z) ^ (2 * n) from by ring]
    rw [div_eq_iff (by positivity : (1 + z) ^ (2 * n) ≠ 0)]
    rw [show -c * (n : ℝ) / (1 + z) ^ (n + 1) * (1 + z) ^ (2 * n)
        = (-c * (n : ℝ)) * ((1 + z) ^ (2 * n) / (1 + z) ^ (n + 1)) from by ring]
    rw [show (1 + z) ^ (2 * n) / (1 + z) ^ (n + 1) = (1 + z) ^ (n - 1) from by
      rw [div_eq_iff (by positivity : (1 + z) ^ (n + 1) ≠ 0), ← hpow]]
    ring

/-- The iterated derivatives of `w ↦ c/(1+w)`. -/
lemma iter_deriv_const_div_one_add (c : ℝ) :
    ∀ k : ℕ, ∀ z : ℝ, (1 : ℝ) + z ≠ 0 →
      deriv^[k] (fun w : ℝ => c / (1 + w)) z
        = (-1 : ℝ) ^ k * c * ((k.factorial : ℕ) : ℝ) / (1 + z) ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro z hz; norm_num
  | succ k ih =>
      intro z hz
      rw [Function.iterate_succ_apply']
      have hset : IsOpen {w : ℝ | (1 : ℝ) + w ≠ 0} := isOpen_ne.preimage (by continuity)
      have hev : deriv^[k] (fun w : ℝ => c / (1 + w))
          =ᶠ[𝓝 z] fun w => (-1 : ℝ) ^ k * c * ((k.factorial : ℕ) : ℝ) / (1 + w) ^ (k + 1) := by
        filter_upwards [hset.mem_nhds (show (1 : ℝ) + z ≠ 0 from hz)] with w hw
        exact ih w hw
      rw [hev.deriv_eq, deriv_const_div_pow _ _ z hz]
      have hsign : (-1:ℝ)^(k+1) = (-1)^k * (-1) := by rw [pow_succ]
      rw [hsign, Nat.factorial_succ]
      push_cast
      ring

/-- **The flat bound for the radial factor `α·2/(1+z)`**: for `k ≤ 7` and `z > 0`,
`|(z+1)^k ∂_z^k (α·2/(1+·))| ≤ α·10080` (`10080 = 2·7!`). -/
lemma radial_alpha_bound (α : ℝ) (hα : 0 < α) :
    ∀ k : ℕ, k ≤ 7 → ∀ z : ℝ, 0 < z →
      |(z + 1) ^ k * iteratedDeriv k (fun w : ℝ => α * (2 / (1 + w))) z| ≤ α * 10080 := by
  intro k hk z hz
  have hz1 : (0:ℝ) < 1 + z := by linarith
  have hzne : (1:ℝ) + z ≠ 0 := ne_of_gt hz1
  have h1 : iteratedDeriv k (fun w : ℝ => α * (2 / (1 + w))) z
      = α * deriv^[k] (fun w : ℝ => 2 / (1 + w)) z := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate]
  rw [h1, iter_deriv_const_div_one_add 2 k z hzne]
  have hbase : (z + 1) ^ k = (1 + z) ^ k := by ring
  rw [hbase]
  have hprod : (1 + z) ^ k * (α * ((-1 : ℝ) ^ k * 2 * ↑k.factorial / (1 + z) ^ (k + 1)))
      = α * (2 * ↑k.factorial / (1 + z)) * (-1:ℝ)^k := by
    have hpow : (1 + z) ^ k / (1 + z) ^ (k + 1) = 1 / (1 + z) := by
      have hk0 : (1 + z) ^ k ≠ 0 := pow_ne_zero _ hzne
      field_simp
      ring
    rw [show (1 + z) ^ k * (α * ((-1 : ℝ) ^ k * 2 * ↑k.factorial / (1 + z) ^ (k + 1)))
        = α * ((-1:ℝ)^k * (2 * ↑k.factorial)) * ((1 + z) ^ k / (1 + z) ^ (k + 1)) from by ring]
    rw [hpow]
    ring
  rw [hprod]
  have hA : ((k.factorial : ℕ) : ℝ) ≤ 5040 := by
    have h : k.factorial ≤ 5040 := by interval_cases k <;> norm_num
    exact_mod_cast h
  rw [abs_mul, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow, mul_one,
    abs_of_nonneg (le_of_lt hα), abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ↑k.factorial),
    abs_of_pos hz1]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hα)
  rw [div_le_iff₀ hz1]
  nlinarith [hA, hz1]

/-! ## The main theorem -/

theorem FlatW_ycheckSmooth : ∃ C : ℝ, 0 < C ∧
  ∀ (α : ℝ) (ψ : ℝ → ℝ) (R : Work.FTS.Galerkin.Fn) (K : ℝ),
    0 < α → α ≤ 1 / 5 → Work.FTS.PhiStar.AngModel α ψ → 0 ≤ K →
    Work.FTS.EllipticEst.SmoothOpen R →
    Work.FTS.VocabO2.FlatW 7 (fun z θ => (z + 1) / z * R z θ / Work.Construction.s2 θ) K →
    Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z
        + α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ)
        + (z + 1) / z * R z θ / Work.Construction.s2 θ) (C * (α + K)) := by
  obtain ⟨C₁, hC₁, hA⟩ := Work.FTS.PhiStar.FlatW_aprof
  obtain ⟨C₂, hC₂, hP⟩ := Work.FTS.PhiStar.FlatW_psiDiv
  obtain ⟨Cm, hCmpos, hRadMul⟩ := FlatW_theta_radial_mul
  obtain ⟨Ca, hCapos, hAdd⟩ := FlatW_add
  refine ⟨max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro α ψ R K hα hα5 hang hK hR hRflat
  have hα4 : α ≤ 1/4 := by linarith
  have hα1 : α ≤ 1 := by linarith
  have hC₂0 : (0:ℝ) ≤ C₂ := le_of_lt hC₂
  have hA0 : (0:ℝ) ≤ α * 10080 := by positivity
  -- the three summands
  have hf1 : Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z) (C₁ * α) := hA α hα hα1
  have hf2 : Work.FTS.VocabO2.FlatW 7
      (fun z θ => α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ))
      (Cm * ((α * 10080) * C₂)) := by
    have h := hRadMul 7 (fun z => α * (2 / (1 + z))) (fun θ => ψ θ / Work.Construction.s2 θ)
      (α * 10080) C₂ hA0 hC₂0 (radial_alpha_bound α hα) (hP α ψ hα hα4 hang)
    simpa using h
  have hf3 : Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z * R z θ / Work.Construction.s2 θ) K := hRflat
  -- smoothness of the summands
  have hs1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z) :=
    smoothOpen_of_radial (fun n => ContDiffOn.mul (contDiffOn_zdiv n)
      (contDiffOn_aprof α hα hα4 n))
  have hs2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ)) :=
    smoothOpen_mul (smoothOpen_of_radial (fun n => contDiffOn_two_div_one_add α n))
      (smoothOpen_of_angular (fun n => contDiffOn_psiDiv α ψ hang n))
  have hs3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (z + 1) / z * R z θ / Work.Construction.s2 θ) := by
    have hp : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => ((z + 1) / z * R z θ) * (1 / Work.Construction.s2 θ)) :=
      smoothOpen_mul (smoothOpen_mul (smoothOpen_of_radial contDiffOn_zdiv) hR)
        (smoothOpen_of_angular contDiffOn_inv_s2)
    refine smoothOpen_congr hp (fun z θ hz hθ hπ => ?_)
    ring
  -- add the pieces
  have h12 : Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z
        + α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ))
      (Ca * ((C₁ * α) + (Cm * ((α * 10080) * C₂)))) :=
    hAdd 7 (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z)
      (fun z θ => α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ))
      (C₁ * α) (Cm * ((α * 10080) * C₂)) (by positivity) (by positivity) hs1 hs2 hf1 hf2
  have hfull : Work.FTS.VocabO2.FlatW 7
      (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z
        + α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ)
        + (z + 1) / z * R z θ / Work.Construction.s2 θ)
      (Ca * ((Ca * ((C₁ * α) + (Cm * ((α * 10080) * C₂)))) + K)) :=
    hAdd 7 (fun z θ => (z + 1) / z * Work.FTS.PhiStar.Aprof α z
        + α * (2 / (1 + z)) * (ψ θ / Work.Construction.s2 θ))
      (fun z θ => (z + 1) / z * R z θ / Work.Construction.s2 θ)
      (Ca * ((C₁ * α) + (Cm * ((α * 10080) * C₂)))) K
      (by positivity) hK (smoothOpen_add hs1 hs2) hs3 h12 hf3
  -- the assembled constant is dominated by `max (Ca·(Ca·(C₁ + Cm·10080·C₂) + 1)) 1 · (α + K)`
  have hbound : Ca * ((Ca * ((C₁ * α) + (Cm * ((α * 10080) * C₂)))) + K)
      ≤ max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 * (α + K) := by
    have hexp : Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)
        = Ca * (Ca * C₁) + Ca * (Ca * (Cm * (10080 * C₂))) + Ca := by ring
    have hXY : Ca * (Ca * C₁) + Ca * (Ca * (Cm * (10080 * C₂)))
        ≤ max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 := by
      have h1 : Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)
          ≤ max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 := le_max_left _ _
      have h2 : Ca * (Ca * C₁) + Ca * (Ca * (Cm * (10080 * C₂)))
          ≤ Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1) := by
        rw [hexp]
        exact le_add_of_nonneg_right (le_of_lt hCapos)
      exact le_trans h2 h1
    have hb3 : Ca ≤ max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 := by
      have h1 : Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)
          ≤ max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 := le_max_left _ _
      have h2 : Ca ≤ Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1) := by
        have h3 : (1:ℝ) ≤ Ca * (C₁ + Cm * (10080 * C₂)) + 1 :=
          le_add_of_nonneg_left (by positivity)
        have h4 : Ca * 1 ≤ Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1) :=
          mul_le_mul_of_nonneg_left h3 (le_of_lt hCapos)
        simpa using h4
      exact le_trans h2 h1
    have hLHS : Ca * ((Ca * ((C₁ * α) + (Cm * ((α * 10080) * C₂)))) + K)
        = (Ca * (Ca * C₁) + Ca * (Ca * (Cm * (10080 * C₂)))) * α + Ca * K := by ring
    rw [hLHS]
    calc (Ca * (Ca * C₁) + Ca * (Ca * (Cm * (10080 * C₂)))) * α + Ca * K
          ≤ max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 * α
            + max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 * K :=
          add_le_add (mul_le_mul_of_nonneg_right hXY (le_of_lt hα))
            (mul_le_mul_of_nonneg_right hb3 hK)
      _ = max (Ca * (Ca * (C₁ + Cm * (10080 * C₂)) + 1)) 1 * (α + K) := by ring
  exact flatW_mono hfull hbound

end Work.FTS.PhiStar.FlatWApi
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.StarPkgo2Aux.FbEU =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.StarPkgo2Aux

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Smoothness of the elementary radial factors -/

private theorem smoothOpen_fst_pk : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z _ : ℝ => z)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z _ : ℝ => z) = fun p : ℝ × ℝ => p.1 := rfl
  rw [h]
  exact contDiffOn_fst

private theorem smoothOpen_inv_one_add_pk :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (z + 1)⁻¹) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z _ : ℝ => (z + 1)⁻¹)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z _ : ℝ => (z + 1)⁻¹)
      = fun p : ℝ × ℝ => (p.1 + 1)⁻¹ := rfl
  rw [h]
  refine ContDiffOn.inv (contDiffOn_fst.add contDiffOn_const) ?_
  intro p hp
  have hp1 : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  linarith

private theorem smoothOpen_z_div_one_add_pk :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (z + 1)) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z _ : ℝ => z / (z + 1))) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z _ : ℝ => z / (z + 1))
      = fun p : ℝ × ℝ => p.1 / (p.1 + 1) := rfl
  rw [h]
  refine ContDiffOn.div contDiffOn_fst (contDiffOn_fst.add contDiffOn_const) ?_
  intro p hp
  have hp1 : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  linarith

/-! ## Flat-calculus closure of `Fb` -/

/-- `Fb` only sees the values on the open quadrant. -/
private theorem Fb_congr_pk {n : ℕ} {K : ℝ} {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ)
    (hg : Work.FTS.PhiStar.Fb n K g) : Work.FTS.PhiStar.Fb n K f :=
  ⟨Work.FTS.PhiStar.CoreAux.F0_congr h hg.f0,
    Work.FTS.PhiStar.CoreAux.F0_congr (Work.FTS.PhiStar.CoreAux.pth_congr_Q0 h) hg.fd⟩

/-- **Scalar multiples in `Fb`**: the constant is `|c|·K` (no loss, via the exact identities
`D_θ^i(c·f) = c·D_θ^i f` and `∂_θ(c·f) = c·∂_θ f`). -/
private theorem Fb_const_mul_pk {n : ℕ} {K c : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.PhiStar.Fb n K f) :
    Work.FTS.PhiStar.Fb n (|c| * K) (fun z θ => c * f z θ) :=
  ⟨Work.FTS.PhiStar.CoreAux.F0_const_mul c hf.f0, by
    rw [Work.FTS.PhiStar.CoreAux.pth_const_mul c f]
    exact Work.FTS.PhiStar.CoreAux.F0_const_mul c hf.fd⟩

/-- **Multiplication by a factor depending on `z` alone.**  If `g` is independent of `θ` and
`C^∞` on the open quadrant with `F0 n A g`, and `f` has `Fb n K`, then `g·f` has `Fb n`
with constant `2ⁿ·A·K`.  Only the `F0`-half of `Fb` is used for `g`: on `Q0`,
`∂_θ(g·f) = g·∂_θf` because the `θ`-slice of `g` is constant. -/
private theorem Fb_mul_theta_only_pk {n : ℕ} {A K : ℝ} {g f : ℝ → ℝ → ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hgθ : ∀ z θ θ' : ℝ, g z θ = g z θ')
    (hgs : Work.FTS.EllipticEst.SmoothOpen g) (hfs : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.PhiStar.F0 n A g) (hf : Work.FTS.PhiStar.Fb n K f) :
    Work.FTS.PhiStar.Fb n ((2 : ℝ) ^ n * A * K) (fun z θ => g z θ * f z θ) := by
  refine ⟨Work.FTS.PhiStar.CoreAux.F0_mul hA hK hgs hfs hg hf.f0, ?_⟩
  have h2 : Work.FTS.PhiStar.F0 n ((2 : ℝ) ^ n * A * K)
      (fun z θ => g z θ * Work.Spaces.pth f z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul hA hK hgs hfs.pth hg hf.fd
  refine Work.FTS.PhiStar.CoreAux.F0_congr ?_ h2
  intro z θ hz hθ hθ'
  show Work.Spaces.pth (fun z θ => g z θ * f z θ) z θ = g z θ * Work.Spaces.pth f z θ
  have hfun : (fun θ' => g z θ' * f z θ') = (fun θ' => g z θ * f z θ') := by
    funext θ'
    rw [hgθ z θ' θ]
  simp only [Work.Spaces.pth]
  rw [hfun, deriv_const_mul_field]

/-! ## The arithmetic of the constants -/

/-- The constant of the two bounds. -/
private def CUS : ℝ := 1024

private theorem pow_le_four_pk {A : ℝ} (hA : 1 ≤ A) {p : ℕ} (hp : p ≤ 4) : A ^ p ≤ A ^ 4 :=
  pow_le_pow_right₀ hA hp

private theorem base_le_pk {A K α : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α) {p : ℕ}
    (hp : p ≤ 4) : A ^ p * K ≤ A ^ 4 * K * (α + 1) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have h1 : A ^ p * K ≤ A ^ 4 * K := mul_le_mul_of_nonneg_right (pow_le_four_pk hA hp) hK
  have h2 : A ^ 4 * K * 1 ≤ A ^ 4 * K * (α + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (pow_nonneg hA0 4) hK)
  calc A ^ p * K ≤ A ^ 4 * K := h1
    _ = A ^ 4 * K * 1 := by ring
    _ ≤ A ^ 4 * K * (α + 1) := h2

private theorem alpha_base_le_pk {A K α : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α) {p : ℕ}
    (hp : p ≤ 4) : α * (A ^ p * K) ≤ A ^ 4 * K * (α + 1) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have h1 : A ^ p * K ≤ A ^ 4 * K := mul_le_mul_of_nonneg_right (pow_le_four_pk hA hp) hK
  have h2 : α * (A ^ p * K) ≤ α * (A ^ 4 * K) := mul_le_mul_of_nonneg_left h1 hα
  have h3 : α * (A ^ 4 * K) ≤ (α + 1) * (A ^ 4 * K) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (pow_nonneg hA0 4) hK)
  calc α * (A ^ p * K) ≤ α * (A ^ 4 * K) := h2
    _ ≤ (α + 1) * (A ^ 4 * K) := h3
    _ = A ^ 4 * K * (α + 1) := by ring

private theorem coeff_base_le_pk {A K α c : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hc : 0 ≤ c) {p : ℕ} (hp : p ≤ 4) : c * A ^ p * K ≤ c * (A ^ 4 * K * (α + 1)) := by
  calc c * A ^ p * K = c * (A ^ p * K) := by ring
    _ ≤ c * (A ^ 4 * K * (α + 1)) :=
        mul_le_mul_of_nonneg_left (base_le_pk hA hK hα hp) hc

private theorem coeff_alpha_le_pk {A K α c : ℝ} (hA : 1 ≤ A) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hc : 0 ≤ c) {p : ℕ} (hp : p ≤ 4) : c * α * A ^ p * K ≤ c * (A ^ 4 * K * (α + 1)) := by
  calc c * α * A ^ p * K = c * (α * (A ^ p * K)) := by ring
    _ ≤ c * (A ^ 4 * K * (α + 1)) :=
        mul_le_mul_of_nonneg_left (alpha_base_le_pk hA hK hα hp) hc

/-! ## The main theorem -/

theorem FbEU : ∃ C : ℝ, 0 < C ∧ ∀ (α K A : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 1 ≤ A →
    Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.cos (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun _ θ => Real.sin (2 * θ)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => z / (1 + z)) →
    Work.FTS.PhiStar.F0 6 A (fun z _ => (1 + z)⁻¹) →
    Work.FTS.PhiStar.Fb 6 (A * K) Y →
    Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * K * (α + 1)) (Work.FTS.PhiStar.EUz α Y) ∧
    Work.FTS.PhiStar.Fb 4 (C * A ^ 4 * K * (α + 1)) (Work.FTS.PhiStar.EU α Y) := by
  refine ⟨CUS, by norm_num [CUS], ?_⟩
  intro α K A Y hα hK hA hYs _hs1 _hs2 _hs3 _hs4 hzd hzi hY
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have hS : (0 : ℝ) ≤ A * K := mul_nonneg hA0 hK
  -- the two radial coefficients, in the `z + 1` form matching `Wone`/`Yblk`
  have hzi' : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => (z + 1)⁻¹) :=
    Work.FTS.PhiStar.CoreAux.F0_congr
      (f := fun z _ : ℝ => (z + 1)⁻¹) (g := fun z _ : ℝ => (1 + z)⁻¹)
      (fun z θ _ _ _ => by rw [add_comm (1 : ℝ) z]) hzi
  have hzd' : Work.FTS.PhiStar.F0 6 A (fun z _ : ℝ => z / (z + 1)) :=
    Work.FTS.PhiStar.CoreAux.F0_congr
      (f := fun z _ : ℝ => z / (z + 1)) (g := fun z _ : ℝ => z / (1 + z))
      (fun z θ _ _ _ => by rw [add_comm (1 : ℝ) z]) hzd
  have hzi4 : Work.FTS.PhiStar.F0 4 A (fun z _ : ℝ => (z + 1)⁻¹) :=
    hzi'.mono (by norm_num) le_rfl
  have hzd4 : Work.FTS.PhiStar.F0 4 A (fun z _ : ℝ => z / (z + 1)) :=
    hzd'.mono (by norm_num) le_rfl
  have sFst : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z) := smoothOpen_fst_pk
  have sInv : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => (z + 1)⁻¹) :=
    smoothOpen_inv_one_add_pk
  have sRho : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (z + 1)) :=
    smoothOpen_z_div_one_add_pk
  -- the `Fb`-chain
  have hY4 : Work.FTS.PhiStar.Fb 4 (A * K) Y := hY.mono (by norm_num) le_rfl
  -- (a) `3·Y`
  have t3Y : Work.FTS.PhiStar.Fb 4 (3 * (A * K)) (fun z θ => 3 * Y z θ) := by
    have h := Fb_const_mul_pk (c := (3 : ℝ)) hY4
    rwa [show |(3 : ℝ)| = 3 by norm_num] at h
  -- (b) `Y·(z+1)⁻¹`
  have tInv : Work.FTS.PhiStar.Fb 4 (16 * A ^ 2 * K) (fun z θ => Y z θ * (z + 1)⁻¹) := by
    have h1 : Work.FTS.PhiStar.Fb 4 ((2 : ℝ) ^ 4 * A * (A * K))
        (fun z θ => (z + 1)⁻¹ * Y z θ) :=
      Fb_mul_theta_only_pk hA0 hS (fun z θ θ' => rfl) sInv hYs hzi4 hY4
    have h2 : Work.FTS.PhiStar.Fb 4 (16 * A ^ 2 * K) (fun z θ => (z + 1)⁻¹ * Y z θ) :=
      h1.mono le_rfl (le_of_eq (by ring))
    exact Fb_congr_pk (fun z θ _ _ _ => by ring) h2
  -- (c) `D_z Y = z·∂_z Y`
  have tZ : Work.FTS.PhiStar.Fb 4 (6 * (A * K)) (fun z θ => z * Work.Spaces.pz Y z θ) := by
    have h := (Work.FTS.PhiStar.CoreAux.Fb_zpz (n := 5) hS hYs hY).mono
      (show 4 ≤ 5 by norm_num) le_rfl
    have hc : (((5 : ℕ) : ℝ) + 1) * (A * K) = 6 * (A * K) := by norm_num
    rwa [hc] at h
  -- (d) the sum `Y·(z+1)⁻¹ + D_z Y`
  have sInvY : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Y z θ * (z + 1)⁻¹) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul hYs sInv
  have sZpY : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z * Work.Spaces.pz Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul sFst hYs.pz
  have tSum : Work.FTS.PhiStar.Fb 4 (16 * A ^ 2 * K + 6 * (A * K))
      (fun z θ => Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fb_add sInvY sZpY tInv tZ
  -- (e) `α·(Y·(z+1)⁻¹ + D_z Y)`
  have tAlpha : Work.FTS.PhiStar.Fb 4 (α * (16 * A ^ 2 * K + 6 * (A * K)))
      (fun z θ => α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ)) := by
    have h := Fb_const_mul_pk (c := α) tSum
    rwa [show |α| = α by exact abs_of_nonneg hα] at h
  -- (f) `W₁ = 3Y + α·(Y·(z+1)⁻¹ + D_z Y)`
  have s3Y : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 3 * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hYs 3
  have sAlpha : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul
      (Work.FTS.PhiStar.CoreAux.SmoothOpen.add sInvY sZpY) α
  have tW : Work.FTS.PhiStar.Fb 4 (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K)))
      (fun z θ => 3 * Y z θ + α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ)) :=
    Work.FTS.PhiStar.CoreAux.Fb_add s3Y sAlpha t3Y tAlpha
  -- (g) `EUz α Y = -W₁`
  have hKW0 : (0 : ℝ) ≤ 3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K)) := by
    have h1 : (0 : ℝ) ≤ 16 * A ^ 2 * K + 6 * (A * K) := by positivity
    nlinarith [mul_nonneg hα h1, mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hS]
  have tNeg : Work.FTS.PhiStar.Fb 4 (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K)))
      (fun z θ => -(3 * Y z θ + α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ))) := by
    have h := Fb_const_mul_pk (c := (-1 : ℝ)) tW
    simpa only [abs_neg, abs_one, one_mul, neg_one_mul] using h
  have tEUz : Work.FTS.PhiStar.Fb 4 (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K)))
      (Work.FTS.PhiStar.EUz α Y) :=
    Fb_congr_pk (fun z θ _ _ _ => by
      simp only [Work.FTS.PhiStar.EUz, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk,
        div_eq_mul_inv]) tNeg
  -- (h) `EU α Y = (z/(z+1))·(-W₁)`
  have sNegW : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(3 * Y z θ + α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ))) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.congr
      (Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul
        (Work.FTS.PhiStar.CoreAux.SmoothOpen.add s3Y sAlpha) (-1))
      (fun z θ _ _ _ => by ring)
  have tEU : Work.FTS.PhiStar.Fb 4
      ((2 : ℝ) ^ 4 * A * (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K))))
      (fun z θ => (z / (z + 1)) *
        (-(3 * Y z θ + α * (Y z θ * (z + 1)⁻¹ + z * Work.Spaces.pz Y z θ)))) :=
    Fb_mul_theta_only_pk hA0 hKW0 (fun z θ θ' => rfl) sRho sNegW hzd4 tNeg
  have tEU' : Work.FTS.PhiStar.Fb 4
      ((2 : ℝ) ^ 4 * A * (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K))))
      (Work.FTS.PhiStar.EU α Y) :=
    Fb_congr_pk (fun z θ _ _ _ => by
      simp only [Work.FTS.PhiStar.EU, Work.FTS.PhiStar.Wone, Work.FTS.PhiStar.Yblk,
        div_eq_mul_inv]
      ring) tEU
  -- the arithmetic
  have hT0 : (0 : ℝ) ≤ A ^ 4 * K * (α + 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hA0 4) hK) (by linarith)
  have hAbs : CUS * A ^ 4 * K * (α + 1) = CUS * (A ^ 4 * K * (α + 1)) := by ring
  have hKW : 3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K))
      ≤ CUS * A ^ 4 * K * (α + 1) := by
    have e1 : 3 * (A * K) ≤ 3 * (A ^ 4 * K * (α + 1)) := by
      have h := coeff_base_le_pk (A := A) (K := K) (α := α) (c := 3) hA hK hα
        (by norm_num) (p := 1) (by norm_num)
      calc 3 * (A * K) = 3 * A ^ 1 * K := by ring
        _ ≤ 3 * (A ^ 4 * K * (α + 1)) := h
    have e2 : α * (16 * A ^ 2 * K) ≤ 16 * (A ^ 4 * K * (α + 1)) := by
      have h := coeff_alpha_le_pk (A := A) (K := K) (α := α) (c := 16) hA hK hα
        (by norm_num) (p := 2) (by norm_num)
      calc α * (16 * A ^ 2 * K) = 16 * α * A ^ 2 * K := by ring
        _ ≤ 16 * (A ^ 4 * K * (α + 1)) := h
    have e3 : α * (6 * (A * K)) ≤ 6 * (A ^ 4 * K * (α + 1)) := by
      have h := coeff_alpha_le_pk (A := A) (K := K) (α := α) (c := 6) hA hK hα
        (by norm_num) (p := 1) (by norm_num)
      calc α * (6 * (A * K)) = 6 * α * A ^ 1 * K := by ring
        _ ≤ 6 * (A ^ 4 * K * (α + 1)) := h
    have step1 : 3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K))
        ≤ 25 * (A ^ 4 * K * (α + 1)) := by
      rw [mul_add]
      linarith [e1, e2, e3]
    have step2 : (25 : ℝ) * (A ^ 4 * K * (α + 1)) ≤ CUS * A ^ 4 * K * (α + 1) := by
      rw [hAbs]
      exact mul_le_mul_of_nonneg_right (by norm_num [CUS]) hT0
    linarith [step1, step2]
  have hKEU : (2 : ℝ) ^ 4 * A * (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K)))
      ≤ CUS * A ^ 4 * K * (α + 1) := by
    have hb : (2 : ℝ) ^ 4 * A * (3 * (A * K) + α * (16 * A ^ 2 * K + 6 * (A * K)))
        = 48 * A ^ 2 * K + 256 * α * A ^ 3 * K + 96 * α * A ^ 2 * K := by ring
    rw [hb]
    have e1 : 48 * A ^ 2 * K ≤ 48 * (A ^ 4 * K * (α + 1)) :=
      coeff_base_le_pk (A := A) (K := K) (α := α) (c := 48) hA hK hα
        (by norm_num) (p := 2) (by norm_num)
    have e2 : 256 * α * A ^ 3 * K ≤ 256 * (A ^ 4 * K * (α + 1)) :=
      coeff_alpha_le_pk (A := A) (K := K) (α := α) (c := 256) hA hK hα
        (by norm_num) (p := 3) (by norm_num)
    have e3 : 96 * α * A ^ 2 * K ≤ 96 * (A ^ 4 * K * (α + 1)) :=
      coeff_alpha_le_pk (A := A) (K := K) (α := α) (c := 96) hA hK hα
        (by norm_num) (p := 2) (by norm_num)
    have step1 : 48 * A ^ 2 * K + 256 * α * A ^ 3 * K + 96 * α * A ^ 2 * K
        ≤ 400 * (A ^ 4 * K * (α + 1)) := by linarith [e1, e2, e3]
    have step2 : (400 : ℝ) * (A ^ 4 * K * (α + 1)) ≤ CUS * A ^ 4 * K * (α + 1) := by
      rw [hAbs]
      exact mul_le_mul_of_nonneg_right (by norm_num [CUS]) hT0
    linarith [step1, step2]
  exact ⟨tEUz.mono le_rfl hKW, tEU'.mono le_rfl hKEU⟩

end

end Work.FTS.PhiStar.StarPkgo2Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.T5bZeroAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

set_option maxHeartbeats 1600000

noncomputable section

/-! ## Helpers -/

/-- The product measure of the two restricted measures. -/
def Lprod : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)

theorem abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  have hs : |Real.sin θ ^ 2| ≤ 1 := by rw [abs_sq]; nlinarith [Real.sin_sq_le_one θ]
  have hc : |Real.cos (2*θ)| ≤ 1 := Real.abs_cos_le_one _
  have h : Work.Construction.c2m θ = Real.cos (2*θ) - Real.sin θ ^ 2 := rfl
  rw [h]
  calc |Real.cos (2*θ) - Real.sin θ ^ 2| ≤ |Real.cos (2*θ)| + |Real.sin θ ^ 2| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add hc hs
    _ = 2 := by norm_num

theorem continuousOn_c2m_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Construction.c2m p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) := by
  have h : ContinuousOn (fun p : ℝ × ℝ => Real.cos (2 * p.2) - Real.sin p.2 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)) :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn).sub
      ((Real.continuous_sin.comp continuous_snd).continuousOn.pow 2)
  exact h.congr (fun p _ => rfl)


theorem aemeasurable_c2m_Iθ :
    AEMeasurable (fun θ : ℝ => Work.Construction.c2m θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
  (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).sub
    (Real.continuous_sin.pow 2)).aemeasurable.restrict)

/-- Integrability of a slot with angular weight `σ` from integrability with the dominating
`sin(2θ)^{-q}`-weight. -/
theorem slot_sigma_integrable {X : ℝ → ℝ → ℝ} {σ : ℝ → ℝ} {q : ℝ}
    (hσcont : ContinuousOn (fun p : ℝ × ℝ => σ p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)))
    (hσnn : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ σ θ)
    (hσle : ∀ θ ∈ Set.Ioo 0 (π / 2), σ θ ≤ (Real.sin (2*θ)) ^ (-q))
    (hXc : ContinuousOn (Function.uncurry X)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)))
    (hbig : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * (Real.sin (2*p.2)) ^ (-q) * (X p.1 p.2)^2) Lprod) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1)^2 * σ p.2 * (X p.1 p.2)^2) Lprod := by
  refine hbig.mono' ?_ ?_
  · have hw : AEStronglyMeasurable (fun p : ℝ × ℝ => (Work.Spaces.w p.1)^2) Lprod :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0
    have hσ : AEStronglyMeasurable (fun p : ℝ × ℝ => σ p.2) Lprod :=
      Work.Spaces.aesm_of_continuousOn_Qd _ hσcont
    have hX : AEStronglyMeasurable (fun p : ℝ × ℝ => (X p.1 p.2)^2) Lprod :=
      (Work.Spaces.aesm_of_continuousOn_Qd _ hXc).pow 2
    exact (hw.mul hσ).mul hX
  · have hpt : ∀ θ ∈ Set.Ioo (0:ℝ) (π/2), ∀ z ∈ Set.Ioi (0:ℝ),
        ‖(Work.Spaces.w z)^2 * σ θ * (X z θ)^2‖
          ≤ (Work.Spaces.w z)^2 * (Real.sin (2*θ)) ^ (-q) * (X z θ)^2 := by
      intro θ hθ z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hσnn θ hθ))
        (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hσle θ hθ) (sq_nonneg _)) (sq_nonneg _)
    exact Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo hpt

/-- The Cauchy–Schwarz input `|θw θ| ≤ 2 σ θ` when `θw = σ · c2m` and `|c2m| ≤ 2`. -/
theorem thetaW_abs_le (σ : ℝ → ℝ) (θ : ℝ) (hσ : 0 ≤ σ θ) :
    |σ θ * Work.Construction.c2m θ| ≤ 2 * σ θ := by
  rw [abs_mul, abs_of_nonneg hσ]
  nlinarith [abs_c2m_le_two θ, hσ]


end

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.RowDzTerms =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The per-term bound of the `A · D_z f` flat row

Leibniz expands `D_z^bD_θ^a(A·D_zf)` into the terms `C·(D_z^{j}D_θ^{i}A)·(D_z^{b-j+1}D_θ^{a-i}f)`.
This module bounds one such term against the `ℋ⁶`-integrand (plus the angular Hardy slot `HH`),
pricing the coefficient slot by the `𝒲^{6,∞}`-norm and the flat bounds on `∂_θA`.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg)

theorem rowDz_term_bound : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : ℝ → ℝ → ℝ) (K Kf : ℝ) (a b : ℕ) (q : ℝ) (HH : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.WlInfMem α 6 A →
      Work.Spaces.WlInf α 6 A ≤ K → 0 ≤ Kf →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ Kf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.Dz (Work.Spaces.pth A) z θ| ≤ Kf) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.Dth (Work.Spaces.pth A) z θ| ≤ Kf) →
      a + b ≤ 6 → 0 ≤ q → q ≤ Work.Spaces.gam α → (a = 0 → q ≤ Work.Spaces.eta) →
      (q = Work.Spaces.eta ∨ q = 0 ∨ q = Work.Spaces.gam α) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → ∀ k : ℕ, k ≤ 5 →
        canonW (1 - α / 10) z θ * (Work.Spaces.DzIter k f z θ) ^ 2 ≤ HH z θ) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ HH z θ) →
      ∀ (i j : ℕ), i ≤ a → j ≤ b → 1 ≤ i + j → ∀ z θ : ℝ,
        0 < z → 0 < θ → θ < Real.pi / 2 →
        canonW q z θ * |Work.Spaces.mixed j i A z θ|
            * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ| * |Work.Spaces.mixed b a f z θ|
          ≤ C * (1 + K + Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ) := by
  obtain ⟨C1f, hC1fpos, hflat⟩ := Work.FTS.TransportS.flat_mixed_le 1
  refine ⟨4000 * (1 + C1f) + 1, by positivity, ?_⟩
  intro α hα A f K Kf a b q HH hAsm hAwl hAK hKfnn hKf0 hKf1 hKf2 hab hq0 hqγ hqη0
    hqcases hHH hHHnn i j hi hj hij z θ hz hθ hθ2
  have hα0 : 0 < α := hα.1
  have hKnn : 0 ≤ K :=
    le_trans (Work.FTS.StrongPersist.N6Trans.L6FBound.WlInf6_nonneg hAwl) hAK
  have hCBnn : 0 ≤ 4000 * (1 + C1f) * (1 + K + Kf) := by positivity
  -- ## the pricing of the coefficient slots
  have hAz : ∀ (j : ℕ), j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j 0 A z θ| ≤ 1000 * K := by
    intro j hj z θ hz hθ hθ2
    have h := Work.FTS.StrongPersist.N6Trans.dzIter_le_WlInf6 hAsm hAwl hj hz ⟨hθ, hθ2⟩
    calc |Work.Spaces.mixed j 0 A z θ| = |Work.Spaces.DzIter j A z θ| := rfl
      _ ≤ 1000 * Work.Spaces.WlInf α 6 A := h
      _ ≤ 1000 * K := by linarith
  have hAm : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A z θ|
        ≤ 1000 * K * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
    intro i j hi hij z θ hz hθ hθ2
    have h := Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6 hα0 hAsm hAwl hi hij hz
      ⟨hθ, hθ2⟩
    have hYnn : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by
      have h0 : 0 ≤ Real.sin (2 * θ) := le_of_lt (rowDz_sin2_pos ⟨hθ, hθ2⟩)
      exact mul_nonneg (by linarith) (Real.rpow_nonneg h0 _)
    calc |Work.Spaces.mixed j i A z θ|
        ≤ 1000 * (Work.Spaces.WlInf α 6 A
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := h
      _ ≤ 1000 * (K * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAK hYnn) (by norm_num)
      _ = 1000 * K * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
  have hAf : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i A z θ| ≤ C1f * Real.sin (2 * θ) * Kf := by
    intro i j hi hij z θ hz hθ hθ2
    refine hflat A hAsm Kf hKfnn ?_ i j hi (by omega) z θ hz hθ hθ2
    intro b₁ i₁ hbi z' θ' hz' hθ' hθ''
    have hb : b₁ = 0 ∨ b₁ = 1 := by omega
    have hi' : i₁ = 0 ∨ i₁ = 1 := by omega
    rcases hb with rfl | rfl <;> rcases hi' with rfl | rfl
    · simpa using hKf0 z' θ' hz' hθ' hθ''
    · simpa using hKf2 z' θ' hz' hθ' hθ''
    · simpa using hKf1 z' θ' hz' hθ' hθ''
    · omega
  -- ## the slot domination of the datum's own slot
  have hZc : ∀ e : ℝ, e ≤ Work.Spaces.gam α → (a = 0 → e ≤ Work.Spaces.eta) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        canonW e z θ * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
    intro e he heη z θ hz hθ hθ2
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
    rcases Nat.eq_zero_or_pos a with ha0 | ha
    · subst ha0
      simpa only [Work.Spaces.mixed_zero_right] using
        Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_z_le_int (α := α) (q := e)
          (h := f) (heη rfl) hθI b (by omega)
    · exact Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_mixed_le_int (α := α) (q := e)
        (h := f) he hθI b a ha (by omega)
  -- ## the case analysis
  have hmain : canonW q z θ * |Work.Spaces.mixed j i A z θ|
        * |Work.Spaces.mixed (b - j + 1) (a - i) f z θ| * |Work.Spaces.mixed b a f z θ|
      ≤ (4000 * (1 + C1f) * (1 + K + Kf))
        * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
    by_cases hi0 : i = 0
    · -- ### Case A: `i = 0`
      have hYb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          canonW q z θ * (Work.Spaces.mixed (b - j + 1) (a - i) f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
        intro z θ hz hθ hθ2
        have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
        subst hi0
        rw [Nat.sub_zero]
        rcases Nat.eq_zero_or_pos a with ha0 | ha
        · subst ha0
          simpa only [Work.Spaces.mixed_zero_right] using
            Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_z_le_int (α := α) (q := q)
              (h := f) (hqη0 rfl) hθI (b - j + 1) (by omega)
        · exact Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_mixed_le_int (α := α) (q := q)
            (h := f) hqγ hθI (b - j + 1) a ha (by omega)
      have hXb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          canonW q z θ * |Work.Spaces.mixed j i A z θ| ≤ 1000 * K * canonW q z θ := by
        intro z θ hz hθ hθ2
        subst hi0
        have h := hAz j (by omega) z θ hz hθ hθ2
        have h2 : canonW q z θ * |Work.Spaces.mixed j 0 A z θ| ≤ canonW q z θ * (1000 * K) :=
          mul_le_mul_of_nonneg_left h (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩)
        linarith [h2]
      have hres := rowDz_term_le (α := α) (q := q) (e := q) (M := 1000 * K)
        (X := Work.Spaces.mixed j i A)
        (Y := Work.Spaces.mixed (b - j + 1) (a - i) f) (Z := Work.Spaces.mixed b a f)
        (A₁ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
        (A₂ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
        (by positivity) hXb hYb (hZc q hqγ hqη0) z θ hz hθ hθ2
      refine le_trans hres ?_
      have hMle := rowDz_const1 hC1fpos hKnn hKfnn
      calc (1000 * K) * (Work.Spaces.HkIntegrand α 6 f z θ + Work.Spaces.HkIntegrand α 6 f z θ)
          = (2 * (1000 * K)) * Work.Spaces.HkIntegrand α 6 f z θ := by ring
        _ ≤ (4000 * (1 + C1f) * (1 + K + Kf)) * Work.Spaces.HkIntegrand α 6 f z θ :=
            mul_le_mul_of_nonneg_right hMle (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
        _ ≤ (4000 * (1 + C1f) * (1 + K + Kf)) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
            mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_left (hHHnn z θ hz hθ hθ2)) hCBnn
    · -- ### Case B/C: `1 ≤ i`
      have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have ha0 : ¬ (a = 0) := by omega
      by_cases hle : i + j ≤ 2
      · -- ### Case B: the flat σ-gain
        have heη : q - 1 ≤ Work.Spaces.eta := by
          rcases hqcases with h | h | h
          · rw [h]; linarith [Work.Spaces.eta_pos]
          · rw [h]; rw [Work.Spaces.eta]; norm_num
          · rw [h, Work.Spaces.gam, Work.Spaces.eta]; linarith [hα.2]
        have heγ : q - 1 ≤ Work.Spaces.gam α := by linarith [hqγ]
        have hYc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW (q - 1) z θ * (Work.Spaces.mixed (b - j + 1) (a - i) f z θ) ^ 2
              ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
          intro z θ hz hθ hθ2
          have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
          rcases Nat.eq_zero_or_pos (a - i) with h0 | hpos
          · rw [h0, Work.Spaces.mixed_zero_right]
            exact Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_z_le_int (α := α)
              (q := q - 1) (h := f) heη hθI (b - j + 1) (by omega)
          · exact Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_mixed_le_int (α := α)
              (q := q - 1) (h := f) heγ hθI (b - j + 1) (a - i) hpos (by omega)
        have hXs : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW q z θ * |Work.Spaces.mixed j i A z θ| ≤ (C1f * Kf) * canonW (q - 1) z θ := by
          intro z θ hz hθ hθ2
          have hσp : 0 < Real.sin (2 * θ) := rowDz_sin2_pos ⟨hθ, hθ2⟩
          have h2 : canonW q z θ * (Real.sin (2 * θ)) = canonW (q - 1) z θ := by
            have h3 := rowDz_canonW_mul_sigma (q := q) (t := 1) (z := z) (θ := θ) hσp
            simpa using h3
          rw [← h2]
          calc canonW q z θ * |Work.Spaces.mixed j i A z θ|
              ≤ canonW q z θ * (C1f * Real.sin (2 * θ) * Kf) :=
                mul_le_mul_of_nonneg_left (hAf i j hi1 hle z θ hz hθ hθ2)
                  (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩)
            _ = (C1f * Kf) * (canonW q z θ * Real.sin (2 * θ)) := by ring
        have hres := rowDz_term_le (α := α) (q := q) (e := q - 1) (M := C1f * Kf)
          (X := Work.Spaces.mixed j i A)
          (Y := Work.Spaces.mixed (b - j + 1) (a - i) f) (Z := Work.Spaces.mixed b a f)
          (A₁ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
          (A₂ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
          (mul_nonneg hC1fpos.le hKfnn) hXs hYc
          (hZc (q - 1) heγ (fun h => absurd h ha0)) z θ hz hθ hθ2
        refine le_trans hres ?_
        have hMle := rowDz_const2 hC1fpos hKnn hKfnn
        calc (C1f * Kf) * (Work.Spaces.HkIntegrand α 6 f z θ + Work.Spaces.HkIntegrand α 6 f z θ)
            = (2 * (C1f * Kf)) * Work.Spaces.HkIntegrand α 6 f z θ := by ring
          _ ≤ (4000 * (1 + C1f) * (1 + K + Kf)) * Work.Spaces.HkIntegrand α 6 f z θ :=
              mul_le_mul_of_nonneg_right hMle (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
          _ ≤ (4000 * (1 + C1f) * (1 + K + Kf)) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
              mul_le_mul_of_nonneg_left
                (le_add_of_nonneg_left (hHHnn z θ hz hθ hθ2)) hCBnn
      · -- ### Case C: `3 ≤ i + j`
        have heγ : q - α / 5 ≤ Work.Spaces.gam α := by linarith [hqγ]
        have hXs : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
            canonW q z θ * |Work.Spaces.mixed j i A z θ| ≤ (2000 * K) * canonW (q - α / 5) z θ := by
          intro z θ hz hθ hθ2
          have hασ : α + Real.sin (2 * θ) ≤ 2 := by
            have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
            linarith [hα.2]
          have hσp : 0 < Real.sin (2 * θ) := rowDz_sin2_pos ⟨hθ, hθ2⟩
          have h2 : canonW q z θ * (Real.sin (2 * θ)) ^ (α / 5) = canonW (q - α / 5) z θ :=
            rowDz_canonW_mul_sigma (q := q) (t := α / 5) hσp
          have h1 : canonW q z θ * |Work.Spaces.mixed j i A z θ|
              ≤ canonW q z θ * (1000 * K
                * ((α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5))) :=
            mul_le_mul_of_nonneg_left (hAm i j hi1 (by omega) z θ hz hθ hθ2)
              (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩)
          have h3 : canonW q z θ * (1000 * K
                * ((α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5)))
              = 1000 * K * (α + Real.sin (2 * θ)) * canonW (q - α / 5) z θ := by
            rw [← h2]; ring
          have h5 : 0 ≤ 1000 * K * canonW (q - α / 5) z θ :=
            mul_nonneg (by positivity) (canonW_nonneg ⟨le_of_lt hθ, le_of_lt hθ2⟩)
          have h6 : (1000 * K * canonW (q - α / 5) z θ) * (α + Real.sin (2 * θ))
              ≤ (1000 * K * canonW (q - α / 5) z θ) * 2 :=
            mul_le_mul_of_nonneg_left hασ h5
          calc canonW q z θ * |Work.Spaces.mixed j i A z θ|
              ≤ canonW q z θ * (1000 * K
                * ((α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5))) := h1
            _ = 1000 * K * (α + Real.sin (2 * θ)) * canonW (q - α / 5) z θ := h3
            _ = (1000 * K * canonW (q - α / 5) z θ) * (α + Real.sin (2 * θ)) := by ring
            _ ≤ (1000 * K * canonW (q - α / 5) z θ) * 2 := h6
            _ = (2000 * K) * canonW (q - α / 5) z θ := by ring
        rcases Nat.eq_zero_or_pos (a - i) with hai0 | haipos
        · -- the middle slot is pure
          rw [hai0, Work.Spaces.mixed_zero_right]
          have hYpure : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
              canonW (q - α / 5) z θ * (Work.Spaces.DzIter (b - j + 1) f z θ) ^ 2
                ≤ Work.Spaces.HkIntegrand α 6 f z θ + HH z θ := by
            intro z θ hz hθ hθ2
            have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
            by_cases hqη : q ≤ Work.Spaces.eta
            · have he : q - α / 5 ≤ Work.Spaces.eta := by linarith
              exact le_trans
                (Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_z_le_int (α := α)
                  (q := q - α / 5) (h := f) he hθI (b - j + 1) (by omega))
                (le_add_of_nonneg_right (hHHnn z θ hz hθ hθ2))
            · have hqg : q = Work.Spaces.gam α := by
                rcases hqcases with h | h | h
                · exact absurd (le_of_eq h) hqη
                · rw [h] at hqη; exact absurd (Work.Spaces.eta_pos.le) hqη
                · exact h
              have he : q - α / 5 = 1 - α / 10 := by rw [hqg]; rw [Work.Spaces.gam]; ring
              rw [he]
              have hmem : b - j + 1 ≤ 5 := by omega
              exact le_trans (hHH z θ hz hθ hθ2 (b - j + 1) hmem)
                (le_add_of_nonneg_left (Work.Spaces.HkIntegrand_nonneg α 6 f z θ))
          have hres := rowDz_term_le (α := α) (q := q) (e := q - α / 5) (M := 2000 * K)
            (X := Work.Spaces.mixed j i A) (Y := Work.Spaces.DzIter (b - j + 1) f)
            (Z := Work.Spaces.mixed b a f)
            (A₁ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ + HH z θ)
            (A₂ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
            (by positivity) hXs hYpure (hZc (q - α / 5) heγ (fun h => absurd h ha0))
            z θ hz hθ hθ2
          refine le_trans hres ?_
          have hMle := rowDz_const3 hC1fpos hKnn hKfnn
          have hsum : Work.Spaces.HkIntegrand α 6 f z θ + HH z θ
                + Work.Spaces.HkIntegrand α 6 f z θ
              ≤ 2 * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by
            linarith [hHHnn z θ hz hθ hθ2, Work.Spaces.HkIntegrand_nonneg α 6 f z θ]
          calc (2000 * K) * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ
                + Work.Spaces.HkIntegrand α 6 f z θ)
              ≤ (2000 * K) * (2 * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ)) :=
                mul_le_mul_of_nonneg_left hsum (by positivity)
            _ = (2 * (2000 * K)) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) := by ring
            _ ≤ (4000 * (1 + C1f) * (1 + K + Kf))
                * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
                mul_le_mul_of_nonneg_right hMle
                  (by linarith [Work.Spaces.HkIntegrand_nonneg α 6 f z θ, hHHnn z θ hz hθ hθ2])
        · -- the middle slot is mixed
          have hYc : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
              canonW (q - α / 5) z θ * (Work.Spaces.mixed (b - j + 1) (a - i) f z θ) ^ 2
                ≤ Work.Spaces.HkIntegrand α 6 f z θ := by
            intro z θ hz hθ hθ2
            have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
            exact Work.FTS.StrongPersist.N6Trans.T1SlotZ.canonW_mul_mixed_le_int (α := α)
              (q := q - α / 5) (h := f) heγ hθI (b - j + 1) (a - i) haipos (by omega)
          have hres := rowDz_term_le (α := α) (q := q) (e := q - α / 5) (M := 2000 * K)
            (X := Work.Spaces.mixed j i A)
            (Y := Work.Spaces.mixed (b - j + 1) (a - i) f) (Z := Work.Spaces.mixed b a f)
            (A₁ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
            (A₂ := fun z θ => Work.Spaces.HkIntegrand α 6 f z θ)
            (by positivity) hXs hYc (hZc (q - α / 5) heγ (fun h => absurd h ha0))
            z θ hz hθ hθ2
          refine le_trans hres ?_
          have hMle := rowDz_const3 hC1fpos hKnn hKfnn
          calc (2000 * K) * (Work.Spaces.HkIntegrand α 6 f z θ + Work.Spaces.HkIntegrand α 6 f z θ)
              = (2 * (2000 * K)) * Work.Spaces.HkIntegrand α 6 f z θ := by ring
            _ ≤ (4000 * (1 + C1f) * (1 + K + Kf)) * Work.Spaces.HkIntegrand α 6 f z θ :=
                mul_le_mul_of_nonneg_right hMle (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)
            _ ≤ (4000 * (1 + C1f) * (1 + K + Kf))
                * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
                mul_le_mul_of_nonneg_left
                  (le_add_of_nonneg_left (hHHnn z θ hz hθ hθ2)) hCBnn
  -- ## the constant
  refine le_trans hmain ?_
  have hX : 0 ≤ (1 + K + Kf) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ) :=
    mul_nonneg (by linarith)
      (add_nonneg (hHHnn z θ hz hθ hθ2) (Work.Spaces.HkIntegrand_nonneg α 6 f z θ))
  calc 4000 * (1 + C1f) * (1 + K + Kf) * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ)
      = 4000 * (1 + C1f) * ((1 + K + Kf)
          * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ)) := by ring
    _ ≤ (4000 * (1 + C1f) + 1) * ((1 + K + Kf)
          * (HH z θ + Work.Spaces.HkIntegrand α 6 f z θ)) :=
        mul_le_mul_of_nonneg_right (by linarith) hX
    _ = (4000 * (1 + C1f) + 1) * (1 + K + Kf)
          * (Work.Spaces.HkIntegrand α 6 f z θ + HH z θ) := by ring

end

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.SlicePrep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.FTS.TransportS.SlotT2 (canonW)

set_option autoImplicit false

/-! ## The exponent range -/

theorem eta_le_gam {α : ℝ} (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam]
  have := Work.Spaces.eta_lt_one
  linarith

theorem gam_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam]; linarith

/-! ## The exact canonical exponent of a leaf weight -/

/-- **Every leaf weight is a canonical weight at an admissible exponent.**  The exponent is
`η` for `leafEta`, `0` for `leafOne` and `γ` for `leafGam α`, and the range conditions
`0 ≤ q`, `q ≤ γ`, `a = 0 → q ≤ η` are exactly what the per-term estimates need (a mixed
slot may be priced up to `γ`, a pure `D_z`-slot only up to `η`). -/
theorem leafW_canon_cases {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∃ q : ℝ, ρ = canonW q ∧ 0 ≤ q ∧ q ≤ Work.Spaces.gam α
      ∧ (a = 0 → q ≤ Work.Spaces.eta) := by
  rcases hρ with rfl | rfl | ⟨ha1, rfl⟩
  · exact ⟨Work.Spaces.eta, Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.1,
      Work.Spaces.eta_pos.le, eta_le_gam hα, fun _ => le_rfl⟩
  · exact ⟨0, Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.1, le_rfl,
      gam_nonneg hα, fun _ => Work.Spaces.eta_pos.le⟩
  · exact ⟨Work.Spaces.gam α, Work.FTS.TransportS.T2Sup.leafWeight_eq_canon.2.2 α,
      gam_nonneg hα, le_rfl, fun ha0 => absurd ha0 (by omega)⟩

/-! ## The Leibniz rule in `D_θ`-form -/

/-- `mixed j i (Dth h) = mixed j (i+1) h`: the `D_θ`-iterate of a `D_θ`-derivative is the next
`D_θ`-iterate. -/
theorem mixed_Dth_shift (j i : ℕ) (h : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth h) = Work.Spaces.mixed j (i + 1) h := by
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.DthIter 1 h))
      = Work.Spaces.DzIter j (Work.Spaces.DthIter (i + 1) h)
  congr 1
  exact Work.Spaces.DthIter_add_right i 1 h

/-- **The Leibniz rule for `mixed b a (f · D_θ g)`**, on the open quadrant: the `D_θ`-derivative
of `g` produces the `(i,j) = (0,0)` summand `f · D_θ (mixed b a g)` (the transport term) and
`(a+1)(b+1) - 1` further summands. -/
theorem leibniz_Dth {f g : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen f)
    (hG : Work.FTS.EllipticEst.SmoothOpen g) (b a : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dth g z θ) z θ
        = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ))
              * (Work.Spaces.mixed j i f z θ
                  * Work.Spaces.mixed (b - j) (a - i + 1) g z θ) := by
  intro z θ hz hθ0 hθ1
  rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed b a f (Work.Spaces.Dth g) hF hG.Dth
    z θ hz hθ0 hθ1]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [mixed_Dth_shift]

end Work.FTS.StrongPersist.N6Trans.T1SixAux
end
end
-- ===== merged: Submission.Work.FTS_MuLamOK.Rows.SsRowsEnv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLamOK.Rows

theorem SsRowsEnv (Cs : ℝ) : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f Φs : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.VocabO.StarPkgo α Cs Φs →
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1ss α Φs)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2ss α Φs)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3ss α Φs)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4ss α)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5ss α)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) := by
  -- The five `ss` pieces do not involve the datum, so no `GalClass`/`HkMem` hypothesis is
  -- needed: only the pointwise bounds `Rl1.ss_N1_pt … ss_N5_pt`, the abstract `r`-step
  -- `rl1Pieces.rowStep` and the `𝒰(Φ̃_*)`-bound `Rl1.starUopBound`.  The five constants
  -- `480·max Cs 0`, `320·CU·max Cs 0`, `480·max Cs 0`, `160`, `480` (at `α²`, resp. `α³ ≤ α²`)
  -- are all `≤ (480 + 320·CU)·(1 + max Cs 0) =: K`, and `α² ≤ Env α f` always.
  obtain ⟨CU, hCUpos, hCUb⟩ := Work.FTS.NonlinRows.Rl1.starUopBound
  have hCU0 : (0 : ℝ) ≤ CU := hCUpos.le
  have hm : (0 : ℝ) ≤ max Cs 0 := le_max_right Cs 0
  have h1m : (0 : ℝ) ≤ 1 + max Cs 0 := by linarith
  refine ⟨(480 + 320 * CU) * (1 + max Cs 0),
    mul_pos (by linarith) (by linarith), ?_⟩
  intro α f Φs hα hα1 hs
  have hKnn : (0 : ℝ) ≤ (480 + 320 * CU) * (1 + max Cs 0) :=
    mul_nonneg (by linarith) h1m
  -- `α² ≤ Env α f`
  have hEnv : α ^ 2 ≤ Work.FTS.NonlinRows.Rl1.Env α f := by
    rw [Work.FTS.NonlinRows.Rl1.Env]
    have h1 : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α f :=
      mul_nonneg (Real.sqrt_nonneg α) (Work.Spaces.HkNorm_nonneg α 4 f)
    have h2 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
    linarith
  have hα3 : α ^ 3 ≤ α ^ 2 := pow_le_pow_of_le_one hα.le hα1 (by norm_num : 2 ≤ 3)
  -- the two generic comparisons `C·α² ≤ K·Env`, `C·α³ ≤ K·Env`
  have key : ∀ {C : ℝ}, 0 ≤ C → C ≤ (480 + 320 * CU) * (1 + max Cs 0) →
      C * α ^ 2 ≤ (480 + 320 * CU) * (1 + max Cs 0)
        * Work.FTS.NonlinRows.Rl1.Env α f := by
    intro C _ hCle
    have h1 : C * α ^ 2 ≤ (480 + 320 * CU) * (1 + max Cs 0) * α ^ 2 :=
      mul_le_mul_of_nonneg_right hCle (sq_nonneg α)
    have h2 : (480 + 320 * CU) * (1 + max Cs 0) * α ^ 2
        ≤ (480 + 320 * CU) * (1 + max Cs 0) * Work.FTS.NonlinRows.Rl1.Env α f :=
      mul_le_mul_of_nonneg_left hEnv hKnn
    linarith
  have key3 : ∀ {C : ℝ}, 0 ≤ C → C ≤ (480 + 320 * CU) * (1 + max Cs 0) →
      C * α ^ 3 ≤ (480 + 320 * CU) * (1 + max Cs 0)
        * Work.FTS.NonlinRows.Rl1.Env α f := by
    intro C _ hCle
    have h1 : C * α ^ 3 ≤ (480 + 320 * CU) * (1 + max Cs 0) * α ^ 3 :=
      mul_le_mul_of_nonneg_right hCle (pow_nonneg hα.le 3)
    have h2 : (480 + 320 * CU) * (1 + max Cs 0) * α ^ 3
        ≤ (480 + 320 * CU) * (1 + max Cs 0) * α ^ 2 :=
      mul_le_mul_of_nonneg_left hα3 hKnn
    have h3 : (480 + 320 * CU) * (1 + max Cs 0) * α ^ 2
        ≤ (480 + 320 * CU) * (1 + max Cs 0) * Work.FTS.NonlinRows.Rl1.Env α f :=
      mul_le_mul_of_nonneg_left hEnv hKnn
    linarith
  -- coefficient comparisons
  have hcoef1 : (480 : ℝ) * max Cs 0 ≤ (480 + 320 * CU) * (1 + max Cs 0) :=
    mul_le_mul (by linarith) (by linarith) hm (by linarith)
  have hcoef2 : (320 : ℝ) * CU * max Cs 0 ≤ (480 + 320 * CU) * (1 + max Cs 0) := by
    have h1 : (320 : ℝ) * CU ≤ 480 + 320 * CU := by linarith
    have h2' : (320 : ℝ) * CU * max Cs 0 ≤ (320 * CU) * (1 + max Cs 0) :=
      mul_le_mul_of_nonneg_left (by linarith : max Cs 0 ≤ 1 + max Cs 0)
        (by linarith : (0 : ℝ) ≤ 320 * CU)
    have h3 : (320 : ℝ) * CU * (1 + max Cs 0)
        ≤ (480 + 320 * CU) * (1 + max Cs 0) :=
      mul_le_mul_of_nonneg_right h1 h1m
    linarith
  have hcoef4 : (160 : ℝ) ≤ (480 + 320 * CU) * (1 + max Cs 0) := by
    have h1 : (160 : ℝ) ≤ 480 + 320 * CU := by linarith
    have h2 : (160 : ℝ) * 1 ≤ 160 * (1 + max Cs 0) :=
      mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 1 + max Cs 0) (by norm_num)
    have h3 : (160 : ℝ) * (1 + max Cs 0) ≤ (480 + 320 * CU) * (1 + max Cs 0) :=
      mul_le_mul_of_nonneg_right h1 h1m
    linarith
  have hcoef5 : (480 : ℝ) ≤ (480 + 320 * CU) * (1 + max Cs 0) := by
    have h1 : (480 : ℝ) ≤ 480 + 320 * CU := by linarith
    have h2 : (480 : ℝ) * 1 ≤ 480 * (1 + max Cs 0) :=
      mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 1 + max Cs 0) (by norm_num)
    have h3 : (480 : ℝ) * (1 + max Cs 0) ≤ (480 + 320 * CU) * (1 + max Cs 0) :=
      mul_le_mul_of_nonneg_right h1 h1m
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `N₁^{ss} = 2ℛ(Φ̃_*)F_*`
    have hC1 : (0 : ℝ) ≤ 120 * max Cs 0 * α ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hm) (sq_nonneg α)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N1ss α Φs) (C := 120 * max Cs 0 * α ^ 2) hC1
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => Work.FTS.NonlinRows.Rl1.ss_N1_pt hα hα1 hs r hr θ hθ))
    have h1 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1ss α Φs)
        ≤ ENNReal.ofReal (4 * (120 * max Cs 0 * α ^ 2)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have he : (4 : ℝ) * (120 * max Cs 0 * α ^ 2) = 480 * max Cs 0 * α ^ 2 := by ring
    rw [he]
    exact key (mul_nonneg (by norm_num) hm) hcoef1
  · -- `N₂^{ss} = -2𝒰(Φ̃_*)∂_θF_*`
    have hMU : (0 : ℝ) ≤ CU * max Cs 0 * α :=
      mul_nonneg (mul_nonneg hCU0 hm) hα.le
    have hU : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
        |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
          ≤ CU * max Cs 0 * α :=
      fun z θ hz hθI => hCUb (α := α) (Cs := Cs) (Φs := Φs) hα hα1 hs z hz θ hθI
    have hC2 : (0 : ℝ) ≤ 80 * (CU * max Cs 0 * α) * α ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hMU) (sq_nonneg α)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N2ss α Φs) (C := 80 * (CU * max Cs 0 * α) * α ^ 2) hC2
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => Work.FTS.NonlinRows.Rl1.ss_N2_pt (Cs := Cs) hα hα1 hMU hU r hr θ hθ))
    have h2 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2ss α Φs)
        ≤ ENNReal.ofReal (4 * (80 * (CU * max Cs 0 * α) * α ^ 2)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    have he : (4 : ℝ) * (80 * (CU * max Cs 0 * α) * α ^ 2)
        = 320 * CU * max Cs 0 * α ^ 3 := by ring
    rw [he]
    exact key3 (mul_nonneg (mul_nonneg (by norm_num) hCU0) hm) hcoef2
  · -- `N₃^{ss} = -2α𝒱(Φ̃_*)D_zF_*`
    have hC3 : (0 : ℝ) ≤ 120 * max Cs 0 * α ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) hm) (pow_nonneg hα.le 3)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N3ss α Φs) (C := 120 * max Cs 0 * α ^ 3) hC3
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => Work.FTS.NonlinRows.Rl1.ss_N3_pt hα hα1 hs r hr θ hθ))
    have h3 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3ss α Φs)
        ≤ ENNReal.ofReal (4 * (120 * max Cs 0 * α ^ 3)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
    have he : (4 : ℝ) * (120 * max Cs 0 * α ^ 3) = 480 * max Cs 0 * α ^ 3 := by ring
    rw [he]
    exact key3 (mul_nonneg (by norm_num) hm) hcoef1
  · -- `N₄^{ss} = -(1/2)sin2θ FK(F_*) ∂_θF_*`
    have hC4 : (0 : ℝ) ≤ 40 * α ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hα.le 3)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N4ss α) (C := 40 * α ^ 3) hC4
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => Work.FTS.NonlinRows.Rl1.ss_N4_pt hα hα1 r hr θ hθ))
    have h4 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N4ss α)
        ≤ ENNReal.ofReal (4 * (40 * α ^ 3)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h4.trans (ENNReal.ofReal_le_ofReal ?_)
    have he : (4 : ℝ) * (40 * α ^ 3) = 160 * α ^ 3 := by ring
    rw [he]
    exact key3 (by norm_num) hcoef4
  · -- `N₅^{ss} = -sin²θ FK(F_*) F_*`
    have hC5 : (0 : ℝ) ≤ 120 * α ^ 2 := mul_nonneg (by norm_num) (sq_nonneg α)
    have hred := Work.FTS.Nonlinear.Pieces.rl1Pieces.rowStep
      (N := Work.FTS.Nonlin.N5ss α) (C := 120 * α ^ 2) hC5
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.ae_Iθ_of_forall_Ioo
        (fun θ hθ => Work.FTS.NonlinRows.Rl1.ss_N5_pt hα hα1 r hr θ hθ))
    have h5 : Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N5ss α)
        ≤ ENNReal.ofReal (4 * (120 * α ^ 2)) := by
      simpa only [Work.FTS.Nonlinear.Pieces.Fa] using hred
    refine h5.trans (ENNReal.ofReal_le_ofReal ?_)
    have he : (4 : ℝ) * (120 * α ^ 2) = 480 * α ^ 2 := by ring
    rw [he]
    exact key (by norm_num) hcoef5

end Work.FTS_MuLamOK.Rows
end
-- ===== merged: Submission.Work.FTS_MuLipC.RowN.PvAesmOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLipC.RowN

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin Work.Construction Work.Spaces
open Work.FTS.Nonlinear.Pieces.rl1Tools (aesm_congr aesm_mul aesm_const_mul aesm_neg
  aesm_s2_mul aesm_sinsq_mul aesm_FK aesm_Uop_of_div aesm_of_contOn_Qd
  aesm_F_ops QdMeas pv)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem PvAesmOpen {α Ce Cs : ℝ} {g Φs Ξg : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hα1 : α ≤ 1) (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Ξg) :
    ∀ k : Fin 20, MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun r θ => Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Ξg k r θ))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  obtain ⟨hg', hpthg, hDzg, hDthg⟩ :=
    Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.aesm_f_ops_open hg
  obtain ⟨hF, hpthF, hDzF⟩ := aesm_F_ops α
  obtain ⟨hRopTg, hUopTg, hVopTg⟩ := Work.FTS.NonlinRows.Rl1.aesm_Tg_ops_open hell
  have hFKg : AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Construction.FK g z)) QdMeas := aesm_FK hg'
  have hFKF : AEStronglyMeasurable
      (Function.uncurry (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z))
      QdMeas := aesm_FK hF
  obtain ⟨hRopTs, hUopTs, hVopTs⟩ :=
    Work.FTS.NonlinRows.Rl1.aesm_star_ops_open hα hα1 hs
  -- the twenty pieces of `pv`
  have hpiece : ∀ k : Fin 20, AEStronglyMeasurable (Function.uncurry (fun r θ =>
      Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Ξg k r θ)) QdMeas := by
    intro k
    fin_cases k
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α g Ξg) z θ * g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hg')) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTg α g Ξg) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTg hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hg')) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        2 * Rop α (PhiTs α Φs) z θ * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_const_mul 2 (aesm_mul hRopTs hF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α g Ξg) z θ * pth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTg α g Ξg) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTg hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * Uop α (PhiTs α Φs) z θ * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2) (aesm_mul hUopTs hpthF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α g Ξg) z θ * Dz g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTg α g Ξg) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTg hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -2 * α * Vop (PhiTs α Φs) z θ * Dz (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-2 * α) (aesm_mul hVopTs hDzF)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK g z * Dth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKg hDthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK g z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKg hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * FK (Fstar α) z * Dth g z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_mul hFKF hDthg)) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(1 / 2) * s2 θ * FK (Fstar α) z * pth (Fstar α) z θ)) QdMeas
      refine aesm_congr (aesm_const_mul (-(1 / 2)) (aesm_s2_mul (aesm_mul hFKF hpthF)))
        (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK g z * g z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKg hg'))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK g z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKg hF))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * g z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hg'))) (fun z θ => ?_)
      ring
    · show AEStronglyMeasurable (Function.uncurry (fun z θ =>
        -(Real.sin θ) ^ 2 * FK (Fstar α) z * Fstar α z θ)) QdMeas
      refine aesm_congr (aesm_neg (aesm_sinsq_mul (aesm_mul hFKF hF))) (fun z θ => ?_)
      ring
  exact hpiece

end

end Work.FTS_MuLipC.RowN
end
