import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadAZop
import Submission.Work.FTS_RegExport.RXT.Slots.v2_Prelim
import Submission.Work.FTS_RegExport.RXT.Slots.v2_Mine
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic
import Submission.Work.FTS_RegExport.RXT.L12Iter.Tower
import Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved
import Submission.Work.FTS_RegExport.RXT.L12_Fstar_add_c4
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar
import Submission.Work.FTS.GalFields.Tail.FK_Fstar_add
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.FTS_StreamBdry.Inputs.L12_slice_jets_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

noncomputable section

open MeasureTheory Set Filter

open scoped Topology

/-- **The `D_z`-jets of `L₁₂(F_τ)` and of `𝔽K(F_τ)` for the profile `F_τ = F_* + slice g τ`.**

For a family `g` of the strong route (`DynOK'`) and every fake time `τ ≥ 0` there is a constant
`CL > 0` such that

* `|D_z^k (L₁₂ F_τ)(z)| ≤ CL` for `k ≤ 3` and `z > 0`,
* `|D_z^j (𝔽K F_τ)(z)| ≤ CL` for `j ≤ 2` and `z > 0`,
* the iterates `D_z^c (L₁₂ F_τ)` (`c ≤ 2`) and `D_z^b (𝔽K F_τ)` (`b ≤ 1`) are differentiable on
  `(0,∞)`, and
* the level-one identity `z ∂_z (L₁₂ F_τ)(z) = -(𝔽K F_τ)(z)` holds for `z > 0`. -/
theorem theta_part_l12 {a C₀ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g) :
    ∀ τ, 0 ≤ τ → ∃ CL : ℝ, 0 < CL ∧
      (∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z) z| ≤ CL) ∧
      (∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
        |Work.Elliptic.DzdIter j (fun z => Work.Construction.FK
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z) z| ≤ CL) ∧
      (∀ c : ℕ, c ≤ 2 → ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Elliptic.DzdIter c
        (fun z => Work.Construction.L12 (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp a) g τ) z)) z) ∧
      (∀ b : ℕ, b ≤ 1 → ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z => Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp a) g τ) z)) z) ∧
      (∀ z : ℝ, 0 < z → z * deriv (fun z' => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z') z
          = -Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ) z) := by
  intro τ hτ
  set α : ℝ := Work.FTS.Regularity.pExp a with hαdef
  have hαG : 0 < α := by rw [hαdef]; exact Work.FTS.Regularity.pExp_pos ha
  have hαG1 : α ≤ 1 := by rw [hαdef]; exact Work.FTS.Regularity.pExp_le_one ha13
  set h : ℝ → ℝ → ℝ := Work.FTS.Galerkin.slice g τ with hh
  have h4 : ContDiffOn ℝ 4 (Function.uncurry h) Work.FTS.EllipticEst.Q0 := by
    rw [hh]; exact hOK.1.1.c4 τ hτ
  have hHk : Work.Spaces.HkMem α 4 h := by rw [hh]; exact hOK.1.1.mem4 τ hτ
  ---------------------------------------------------------------------------------------------
  -- the weighted jet bound for the slice
  ---------------------------------------------------------------------------------------------
  obtain ⟨Cw, hCw0, hCw⟩ := Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved hαG hαG1
    hOK.2 (max τ 1) (lt_of_lt_of_le zero_lt_one (le_max_right τ 1))
  have hτT : τ ∈ Set.Icc (0 : ℝ) (max τ 1) := ⟨hτ, le_max_left τ 1⟩
  have hJet : Work.FTS_RegExport.RXT.Slots.JetBnd Cw h :=
    fun b a hab z θ hz hθ0 hθ1 => hCw τ hτT b a hab z θ hz hθ0 hθ1
  have hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k h z θ| ≤ Cw * Work.FTS_RegExport.RXT.L12Iter.Rwt z :=
    fun k hk z θ hz hθ0 hθ1 => hJet k 0 (by omega) z θ hz hθ0 hθ1
  ---------------------------------------------------------------------------------------------
  -- the two `Qang`-derivatives and the tower for the slice
  ---------------------------------------------------------------------------------------------
  have hQA0 : ∀ w : ℝ, 0 < w →
      HasDerivAt (Work.Elliptic.Qang h 0) (Work.Elliptic.Qang h 1 w / w) w :=
    fun w hw => Work.FTS_RegExport.RXT.Slots.QangZeroDeriv_jet hCw0 h4 hJet hw
  have hQA1 : ∀ w : ℝ, 0 < w →
      HasDerivAt (Work.Elliptic.Qang h 1) (Work.Elliptic.Qang h 2 w / w) w :=
    fun w hw => Work.FTS_RegExport.RXT.Slots.QangOneDeriv_jet hCw0 h4 hJet hw
  have hTower_h : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 h z) z
        = -Work.Elliptic.Qang h (j - 1) z := by
    intro j hj1 hj3 z hz
    refine Work.FTS_RegExport.RXT.L12Iter.DzdIter_L12_eq_neg_Qang hCw0 h4 hbd ?_ hj1 hj3 hz
    exact fun {k : ℕ} hk {w : ℝ} hw => by
      interval_cases k
      · exact hQA0 w hw
      · exact hQA1 w hw
  have hL12h_level1 : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 h z) z
        = -Work.Elliptic.Qang h 0 z := fun z hz => hTower_h 1 le_rfl (by norm_num) z hz
  ---------------------------------------------------------------------------------------------
  -- value additivity of `L₁₂` and the `F_*`-identity
  ---------------------------------------------------------------------------------------------
  have hval : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Ftau α g τ) w
        = Work.Construction.L12 (Work.Construction.Fstar α) w + Work.Construction.L12 h w := by
    intro w hw
    rw [hh]
    exact Work.FTS_RegExport.RXT.L12_Fstar_add_c4 hαG hαG1 h4 hHk hw.le
  have hFstar_eq : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Construction.L12 (Work.Construction.Fstar α) w = 2 * α / (1 + w) :=
    fun w hw => Work.Construction.L12_Fstar_eq hαG hαG1 hw.le
  ---------------------------------------------------------------------------------------------
  -- differentiability of the iterates of the two pieces
  ---------------------------------------------------------------------------------------------
  have hcdFstar : ContDiffOn ℝ 3
      (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) (Set.Ioi 0) := by
    have hinv : ContDiffOn ℝ 3 (fun z : ℝ => (1 + z)⁻¹) (Set.Ioi 0) := by
      refine ContDiffOn.inv (by fun_prop) ?_
      intro z hz
      simp only [Set.mem_Ioi] at hz
      positivity
    have hmain : ContDiffOn ℝ 3 (fun z : ℝ => 2 * α / (1 + z)) (Set.Ioi 0) := by
      refine ((contDiffOn_const (c := 2 * α)).mul hinv).congr (fun z _ => ?_)
      rw [div_eq_mul_inv]
    exact hmain.congr (fun z hz => hFstar_eq z hz)
  have hFstar_diff : ∀ c : ℕ, c ≤ 2 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c
        (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)) z := by
    intro c hc z hz
    rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter c]
    exact Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
      (hcdFstar.of_le (Nat.cast_le.mpr (by omega : c + 1 ≤ 3))) hz
  have hL12h_diff : ∀ c : ℕ, c ≤ 2 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c (fun z => Work.Construction.L12 h z)) z := by
    intro c hc z hz
    interval_cases c
    · exact (Work.FTS_RegExport.RXT.L12Iter.Construction_L12_hasDerivAt hCw0 h4 hbd hz).differentiableAt
    · have hev : (fun w => Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 h z) w)
          =ᶠ[𝓝 z] fun w => -(Work.Elliptic.Qang h 0 w) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        simpa using hL12h_level1 w hw
      rw [hev.differentiableAt_iff]
      exact (hQA0 z hz).differentiableAt.neg
    · have hev : (fun w => Work.Elliptic.DzdIter 2 (fun z => Work.Construction.L12 h z) w)
          =ᶠ[𝓝 z] fun w => -(Work.Elliptic.Qang h 1 w) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
        simpa using hTower_h 2 (by norm_num) (by norm_num) w hw
      rw [hev.differentiableAt_iff]
      exact (hQA1 z hz).differentiableAt.neg
  have hL12F_diff : ∀ c : ℕ, c ≤ 2 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter c
        (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z)) z := by
    intro c hc z hz
    have hev1 : (fun w => Work.Elliptic.DzdIter c
          (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) w)
        =ᶠ[𝓝 z] fun w => Work.Elliptic.DzdIter c ((fun z => Work.Construction.L12
            (Work.Construction.Fstar α) z) + (fun z => Work.Construction.L12 h z)) w := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hval c w hw
    have hev2 : (fun w => Work.Elliptic.DzdIter c ((fun z => Work.Construction.L12
            (Work.Construction.Fstar α) z) + (fun z => Work.Construction.L12 h z)) w)
        =ᶠ[𝓝 z] fun w => Work.Elliptic.DzdIter c (fun z => Work.Construction.L12
              (Work.Construction.Fstar α) z) w
            + Work.Elliptic.DzdIter c (fun z => Work.Construction.L12 h z) w := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff c _ _
        (fun b hb z' hz' => hFstar_diff b (by omega) z' hz')
        (fun b hb z' hz' => hL12h_diff b (by omega) z' hz') w hw
    rw [hev1.differentiableAt_iff, hev2.differentiableAt_iff]
    exact (hFstar_diff c (by omega) z hz).add (hL12h_diff c hc z hz)
  ---------------------------------------------------------------------------------------------
  -- the jet bounds
  ---------------------------------------------------------------------------------------------
  obtain ⟨Cfs, hCfs0, hCfs⟩ := L12Fstar_jets'
  obtain ⟨Cmaj, hCmajpos, hmajall⟩ := majorant_sqrt_tail'
  have hmaj : ∀ z : ℝ, 0 < z →
      ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ Cmaj :=
    fun z hz => (hmajall z hz).2
  obtain ⟨Ch, hCh0, hCh⟩ := L12_slice_jets_le (Cw := Cw) (Cmaj := Cmaj) hCw0 hCmajpos.le h4 hJet hmaj
  set CL : ℝ := Cfs * α + Ch with hCL
  have hCLpos : 0 < CL := by rw [hCL]; have := mul_pos hCfs0 hαG; linarith
  have hFstar_jet : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z|
        ≤ Cfs * α := by
    intro k hk z hz
    have hj := hCfs α hαG hαG1 k hk z hz
    rw [Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) k z 0] at hj
    exact hj
  have hh_jet : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 h z) z| ≤ Ch := by
    intro k hk z hz
    have hj := hCh k hk z hz
    rw [Work.Elliptic.DzIter_rad (fun z => Work.Construction.L12 h z) k z 0] at hj
    exact hj
  have hL12F_jetD : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) z|
        ≤ CL := by
    intro k hk z hz
    have h1 : Work.Elliptic.DzdIter k (fun z => Work.Construction.L12
          (Work.Construction.Ftau α g τ) z) z
        = Work.Elliptic.DzdIter k ((fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
            + (fun z => Work.Construction.L12 h z)) z :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hval k z hz
    have h2 : Work.Elliptic.DzdIter k ((fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
            + (fun z => Work.Construction.L12 h z)) z
        = Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z
          + Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 h z) z :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff k _ _
        (fun b hb z' hz' => hFstar_diff b (by omega) z' hz')
        (fun b hb z' hz' => hL12h_diff b (by omega) z' hz') z hz
    rw [h1, h2]
    calc |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z
          + Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 h z) z|
        ≤ |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z|
          + |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 h z) z| := abs_add_le _ _
      _ ≤ CL := by rw [hCL]; linarith [hFstar_jet k hk z hz, hh_jet k hk z hz]
  ---------------------------------------------------------------------------------------------
  -- the level-one identity for the full profile and the `𝔽K`-jets
  ---------------------------------------------------------------------------------------------
  have hL12Fstar_level1 : ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) z
        = -(2 * α) * z / (1 + z) ^ 2 := by
    intro z hz
    have hev : (fun w => Work.Construction.L12 (Work.Construction.Fstar α) w)
        =ᶠ[𝓝 z] fun w => 2 * α / (1 + w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact hFstar_eq w hw
    show z * deriv (fun w => Work.Construction.L12 (Work.Construction.Fstar α) w) z
      = -(2 * α) * z / (1 + z) ^ 2
    rw [hev.deriv_eq, deriv_const_div_one_add (2 * α) z (by
      have hz' : (0 : ℝ) < z := hz
      linarith)]
    ring
  have hFK_split : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Construction.FK (Work.Construction.Ftau α g τ) w
        = Work.Construction.FK (Work.Construction.Fstar α) w + Work.Construction.FK h w := by
    intro w hw
    rw [hh]
    refine Work.FTS.GalFields.Tail.FK_Fstar_add (α := α) (u := Work.FTS.Galerkin.slice g τ) ?_ hw
    intro z hz
    have hint : Integrable (fun θ => Work.Elliptic.Ktheta θ * h z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      Work.FTS_RegExport.RXT.L12Iter.integrable_Ktheta_mul_DzIter hCw0 h4 hbd (k := 0)
        (by norm_num) hz
    have h2 : Integrable (fun θ => h z θ * Work.Spaces.K θ) (volume.restrict Work.Spaces.Iθ) :=
      hint.congr (Filter.Eventually.of_forall (fun θ => by
        rw [Work.Elliptic.Ktheta_eq_K]; ring))
    rw [hh] at h2
    exact h2
  have hFK_eq_neg : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Construction.FK (Work.Construction.Ftau α g τ) w
        = -(Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12
          (Work.Construction.Ftau α g τ) z) w) := by
    intro w hw
    have h1 : Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12
          (Work.Construction.Ftau α g τ) z) w
        = Work.Elliptic.DzdIter 1 ((fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
            + (fun z => Work.Construction.L12 h z)) w :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hval 1 w hw
    have h2 : Work.Elliptic.DzdIter 1 ((fun z => Work.Construction.L12 (Work.Construction.Fstar α) z)
            + (fun z => Work.Construction.L12 h z)) w
        = Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 (Work.Construction.Fstar α) z) w
          + Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12 h z) w :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff 1 _ _
        (fun b hb z' hz' => hFstar_diff b (by omega) z' hz')
        (fun b hb z' hz' => hL12h_diff b (by omega) z' hz') w hw
    rw [h1, h2, hL12Fstar_level1 w hw, hL12h_level1 w hw, hFK_split w hw,
      Work.FTS.Nonlinear.FstarPkg.FK_Fstar hαG hαG1, Qang_zero_eq_FK h w]
    ring
  have hL12d : ∀ z : ℝ, 0 < z → z * deriv (fun z' => Work.Construction.L12
      (Work.Construction.Ftau α g τ) z') z = -Work.Construction.FK
        (Work.Construction.Ftau α g τ) z := by
    intro z hz
    have h := hFK_eq_neg z hz
    rw [show Work.Elliptic.DzdIter 1 (fun z => Work.Construction.L12
        (Work.Construction.Ftau α g τ) z) z
      = z * deriv (fun z' => Work.Construction.L12 (Work.Construction.Ftau α g τ) z') z from rfl] at h
    linarith [h]
  have hFK_jet : ∀ j : ℕ, j ≤ 2 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.FK
        (Work.Construction.Ftau α g τ) z) z| ≤ CL := by
    intro j hj z hz
    have h1 : Work.Elliptic.DzdIter j (fun z => Work.Construction.FK
          (Work.Construction.Ftau α g τ) z) z
        = Work.Elliptic.DzdIter j (fun z => -(Work.Elliptic.DzdIter 1
            (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) z)) z :=
      Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hFK_eq_neg j z hz
    rw [h1, DzdIter_neg j (fun z => Work.Elliptic.DzdIter 1
      (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) z)]
    rw [← DzdIter_succ_eq j (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z)]
    rw [abs_neg]
    exact hL12F_jetD (j + 1) (by omega) z hz
  have hFK_diff : ∀ b : ℕ, b ≤ 1 → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b (fun z => Work.Construction.FK
        (Work.Construction.Ftau α g τ) z)) z := by
    intro b hb z hz
    have hev : (fun w => Work.Elliptic.DzdIter b (fun z => Work.Construction.FK
          (Work.Construction.Ftau α g τ) z) w)
        =ᶠ[𝓝 z] fun w => -(Work.Elliptic.DzdIter (b + 1)
            (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      have h1 : Work.Elliptic.DzdIter b (fun z => Work.Construction.FK
            (Work.Construction.Ftau α g τ) z) w
          = Work.Elliptic.DzdIter b (fun z => -(Work.Elliptic.DzdIter 1
              (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) z)) w :=
        Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_congr_of_eqOn _ _ hFK_eq_neg b w hw
      have h2 : Work.Elliptic.DzdIter b (fun z => -(Work.Elliptic.DzdIter 1
              (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) z)) w
          = -(Work.Elliptic.DzdIter b (Work.Elliptic.DzdIter 1
              (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z)) w) :=
        congrFun (DzdIter_neg b (fun z => Work.Elliptic.DzdIter 1
          (fun z => Work.Construction.L12 (Work.Construction.Ftau α g τ) z) z)) w
      rw [h1, h2]
      exact congrArg Neg.neg (congrFun (DzdIter_succ_eq b (fun z => Work.Construction.L12
        (Work.Construction.Ftau α g τ) z)) w).symm
    rw [hev.differentiableAt_iff]
    exact (hL12F_diff (b + 1) (by omega) z hz).neg
  exact ⟨CL, hCLpos, hL12F_jetD, hFK_jet, hL12F_diff, hFK_diff, hL12d⟩

end

end Work.FTS_StreamBdry.Inputs
