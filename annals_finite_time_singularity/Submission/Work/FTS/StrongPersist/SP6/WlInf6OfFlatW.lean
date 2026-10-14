import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_MuLamOK.Defs
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.zderiv_LGammaT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Helper lemmas -/

/-- **Monotonicity of the `Jet`-constant.** -/
theorem jet_mono_N {α S M N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (hMN : M ≤ N)
    (H : Work.FTS.Regularity.Jet α S M h) : Work.FTS.Regularity.Jet α S N h := by
  refine ⟨le_trans H.1 hMN, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    exact le_trans (H.2.1 z θ τ hz hθ hτ) hMN
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    refine le_trans (H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ') ?_
    exact mul_le_mul_of_nonneg_right hMN (Real.rpow_nonneg (by positivity) α)

/-- `z ↦ c/(1+z)` has derivative `-c/(1+z)²`. -/
theorem hasDerivAt_const_div_one_add (c : ℝ) {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (fun z' : ℝ => c / (1 + z')) (-(c / (1 + z) ^ 2)) z := by
  have hd : HasDerivAt (fun z' : ℝ => (1 : ℝ) + z') 1 z := by
    simpa [Pi.add_apply] using (hasDerivAt_id z).const_add (1 : ℝ)
  have hne : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  have h := (hasDerivAt_const (x := z) c).div hd hne
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `z ↦ 2z/(1+z)²` has derivative `2(1-z)/(1+z)³`. -/
theorem hasDerivAt_two_div_sq {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (fun z' : ℝ => 2 * z' / (1 + z') ^ 2) (2 * (1 - z) / (1 + z) ^ 3) z := by
  have h3 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by intro h; exact hz (by linarith))
  have h2 : HasDerivAt (fun w : ℝ => (1 + w) ^ 2) (2 * (1 + z)) z := by
    have h := Work.FTS.NonlinRows.AkRhoJetBasic.hasDerivAt_one_add_pow 2 z
    simpa using h
  have h := ((hasDerivAt_id z).const_mul 2).div h2 h3
  refine h.congr_deriv ?_
  simp only [id_eq]
  have h1z : (1 : ℝ) + z ≠ 0 := by intro h; exact hz (by linarith)
  field_simp
  ring

/-- The `L₁₂`-coefficient `2zΓ(θ)/(c(1+z)²)` of `𝓛_Γ^T` has derivative
`(Γ(θ)/c)·2(1-z)/(1+z)³`. -/
theorem hasDerivAt_L12coef {α : ℝ} {θ z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (fun w : ℝ => 2 * w * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + w) ^ 2))
      ((Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * (1 - z) / (1 + z) ^ 3)) z := by
  have hbase := hasDerivAt_two_div_sq hz
  have hc := hbase.const_mul (Work.Spaces.Gam α θ / Work.Spaces.c α)
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards with w
  rw [div_mul_div_comm]
  ring

/-- `|2(1-z)/(1+z)³| ≤ 2` for `z ≥ 0`. -/
theorem abs_deriv_two_div_sq_le {z : ℝ} (hz : 0 ≤ z) :
    |2 * (1 - z) / (1 + z) ^ 3| ≤ 2 := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have habs : |1 - z| ≤ 1 + z := by rw [abs_le]; constructor <;> linarith
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ 3), div_le_iff₀ (by positivity)]
  have h2 : |2 * (1 - z)| ≤ 2 * (1 + z) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; linarith
  calc |2 * (1 - z)| ≤ 2 * (1 + z) := h2
    _ ≤ 2 * (1 + z) ^ 3 := by
        have h3 : (1 + z) ≤ (1 + z) ^ 3 := by
          have := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + z) (by norm_num : 1 ≤ 3)
          simpa using this
        linarith

/-- The six-term triangle inequality, in the left-nested association produced by
`HasDerivAt.add`/`HasDerivAt.sub`. -/
theorem abs_sum_six_le (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 := abs_add_le (a + b + c + d + e) f
  have h2 := abs_add_le (a + b + c + d) e
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b) c
  have h5 := abs_add_le a b
  have n1 := abs_nonneg a; have n2 := abs_nonneg b; have n3 := abs_nonneg c
  have n4 := abs_nonneg d; have n5 := abs_nonneg e; have n6 := abs_nonneg f
  calc |a + b + c + d + e + f| ≤ |a + b + c + d + e| + |f| := h1
    _ ≤ (|a + b + c + d| + |e|) + |f| := by linarith
    _ ≤ ((|a + b + c| + |d|) + |e|) + |f| := by linarith
    _ ≤ (((|a + b| + |c|) + |d|) + |e|) + |f| := by linarith
    _ ≤ ((((|a| + |b|) + |c|) + |d|) + |e|) + |f| := by linarith

/-! ## The `z`-derivative half -/

/-- **The `z`-derivative of `𝓛_Γ^T(g(·,·,τ))`.**  From the five `C1Jet` data of the datum `g`
(value, `D_z g`, `D_θ g`, `L₁₂(g)`, `L₁₂(Transport g)(0)`, each with its own `z`-derivative
bound) the slice `z ↦ 𝓛_Γ^T(g(·,·,τ))(z,θ)` is differentiable on `z > 0` with a derivative
bounded by `100·(N₁ + N₂ + N₃ + N₄ + N₅)`. -/
theorem zderiv_LGammaT_aux {α S N₁ N₂ N₃ N₄ N₅ : ℝ} {g : Work.FTS.RegPkgGal.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hg : Work.FTS.RegPkgGal.C1Jet α S N₁ g)
    (hDzg : Work.FTS.RegPkgGal.C1Jet α S N₂ (fun z θ τ => Work.Spaces.Dz (fun z θ => g z θ τ) z θ))
    (hDthg : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ => Work.Spaces.Dth (fun z θ => g z θ τ) z θ))
    (hL12 : Work.FTS.RegPkgGal.C1Jet α S N₄ (fun z θ τ => Work.Coercivity.L12f
      (Work.FTS.Regularity.gSlice g τ) z))
    (hL12T : Work.FTS.RegPkgGal.C1Jet α S N₅ (fun z θ τ => Work.Coercivity.L12f
      (fun z θ' => 3 * Work.Spaces.Dth (fun z θ => g z θ τ) z θ' / (1 + z)) 0)) :
    ∃ Nc : ℝ, 0 ≤ Nc ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d z ∧ |d| ≤ Nc := by
  have hgam := jca_gam_div_c_bdd (α := α) hα hα13
  have hcbb := (jca_zgam_facts (α := α) hα hα13).1
  have hAKb := (rhsJet_ak_bounds (α := α) hα hα13).1
  refine ⟨100 * (N₁ + N₂ + N₃ + N₄ + N₅),
    by linarith [hg.1.1, hDzg.1.1, hDthg.1.1, hL12.1.1, hL12T.1.1], ?_⟩
  intro τ hτ θ hθ z hz
  have hz0 : 0 < z := hz
  have hzn1 : z ≠ -1 := by intro h; linarith
  -- the five `z`-differentiability hypotheses and the five value bounds at `(z,θ,τ)`
  obtain ⟨d1, hd1, hb1⟩ := hg.2 τ hτ θ hθ z hz
  obtain ⟨d2, hd2, hb2⟩ := hDzg.2 τ hτ θ hθ z hz
  obtain ⟨d3, hd3, hb3⟩ := hDthg.2 τ hτ θ hθ z hz
  obtain ⟨d4, hd4, hb4⟩ := hL12.2 τ hτ θ hθ z hz
  have hG1 : |Work.FTS.Regularity.gSlice g τ z θ| ≤ N₁ := hg.1.2.1 z θ τ hz0.le hθ hτ
  have hG2 : |Work.Spaces.Dz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ N₂ :=
    hDzg.1.2.1 z θ τ hz0.le hθ hτ
  have hG3 : |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ| ≤ N₃ :=
    hDthg.1.2.1 z θ τ hz0.le hθ hτ
  have hG4 : |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z| ≤ N₄ :=
    hL12.1.2.1 z θ τ hz0.le hθ hτ
  have hG5 : |Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Regularity.gSlice g τ)) 0|
      ≤ N₅ := hL12T.1.2.1 z θ τ hz0.le hθ hτ
  -- the two coefficients whose derivatives occur in the expansion of `𝓛_Γ^T`
  set fc : ℝ := Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
    / Work.Spaces.c (Work.FTS.Regularity.pExp α) with hfc
  set cc : ℝ → ℝ := fun w => 2 * w * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
      / (Work.Spaces.c (Work.FTS.Regularity.pExp α) * (1 + w) ^ 2) with hcc
  set ca : ℝ → ℝ := fun w => (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
      / Work.Spaces.c (Work.FTS.Regularity.pExp α)) * (2 * w ^ 2 / (1 + w) ^ 3) with hca
  have hfcb : |fc| ≤ 10 := by rw [hfc]; exact hgam θ hθ
  have hccb : |cc z| ≤ 10 := by rw [hcc]; exact hcbb z hz0.le θ hθ
  have hcab : |ca z| ≤ 10 := by rw [hca]; exact hAKb z hz0.le θ hθ
  have hccdb : |fc * (2 * (1 - z) / (1 + z) ^ 3)| ≤ 20 := by
    rw [abs_mul]
    calc |fc| * |2 * (1 - z) / (1 + z) ^ 3| ≤ 10 * 2 :=
          mul_le_mul hfcb (abs_deriv_two_div_sq_le hz0.le) (abs_nonneg _) (by norm_num)
      _ = 20 := by norm_num
  have hcadb : |fc * (2 * z * (2 - z) / (1 + z) ^ 4)| ≤ 20 := by
    rw [abs_mul]
    calc |fc| * |2 * z * (2 - z) / (1 + z) ^ 4| ≤ 10 * 2 :=
          mul_le_mul hfcb (abs_akPsi_deriv_le_two hz0) (abs_nonneg _) (by norm_num)
      _ = 20 := by norm_num
  have hφb : |-(2 / (1 + z) ^ 2)| ≤ 2 := by
    rw [abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [hz0]
  have hφvb : |2 / (1 + z)| ≤ 2 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
    linarith
  have hψb : |-(3 / (1 + z) ^ 2)| ≤ 3 := by
    rw [abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [hz0]
  have hψvb : |3 / (1 + z)| ≤ 3 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
    linarith
  -- the derivatives of the two coefficients
  have hccd : HasDerivAt cc (fc * (2 * (1 - z) / (1 + z) ^ 3)) z := by
    rw [hcc, hfc]
    exact hasDerivAt_L12coef (α := Work.FTS.Regularity.pExp α) (θ := θ) hzn1
  have hcad : HasDerivAt ca (fc * (2 * z * (2 - z) / (1 + z) ^ 4)) z := by
    rw [hca, hfc]
    exact (Work.FTS.NonlinRows.AkRhoJetBasic.hasDerivAt_akPsi hzn1).const_mul
      (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ / Work.Spaces.c (Work.FTS.Regularity.pExp α))
  -- the five slice derivatives
  have h1 : HasDerivAt (fun w : ℝ => Work.FTS.Regularity.gSlice g τ w θ) d1 z := hd1
  have h2 : HasDerivAt (fun w : ℝ => Work.Spaces.Dz (Work.FTS.Regularity.gSlice g τ) w θ) d2 z :=
    hd2
  have h3 : HasDerivAt (fun w : ℝ => Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) w θ) d3 z :=
    hd3
  have h4 : HasDerivAt (fun w : ℝ => Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) w) d4 z :=
    hd4
  have hP : HasDerivAt (fun w : ℝ => 2 / (1 + w)) (-(2 / (1 + z) ^ 2)) z :=
    hasDerivAt_const_div_one_add 2 hzn1
  have hQ : HasDerivAt (fun w : ℝ => 3 / (1 + w)) (-(3 / (1 + z) ^ 2)) z :=
    hasDerivAt_const_div_one_add 3 hzn1
  have hAa := hP.mul h1
  have hBb := hccd.mul h4
  have hCc := hQ.mul h3
  have hDd := hcad.mul (hasDerivAt_const (x := z)
    (Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Regularity.gSlice g τ)) 0))
  have hbig := ((((h1.add h2).sub hAa).sub hBb).sub hCc).add hDd
  -- the derivative, split into five blocks whose absolute values are bounded separately
  set A : ℝ := -(2 / (1 + z) ^ 2) * Work.FTS.Regularity.gSlice g τ z θ + 2 / (1 + z) * d1
    with hAdef
  set B : ℝ := fc * (2 * (1 - z) / (1 + z) ^ 3)
    * Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z + cc z * d4 with hBdef
  set C : ℝ := -(3 / (1 + z) ^ 2) * Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ
    + 3 / (1 + z) * d3 with hCdef
  set Dv : ℝ := fc * (2 * z * (2 - z) / (1 + z) ^ 4)
    * Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Regularity.gSlice g τ)) 0
    + ca z * 0 with hDvdef
  have hbA : |A| ≤ 2 * N₁ + 2 * N₁ := by
    rw [hAdef]
    calc |-(2 / (1 + z) ^ 2) * Work.FTS.Regularity.gSlice g τ z θ + 2 / (1 + z) * d1|
        ≤ |-(2 / (1 + z) ^ 2) * Work.FTS.Regularity.gSlice g τ z θ| + |2 / (1 + z) * d1| :=
          abs_add_le _ _
      _ = |-(2 / (1 + z) ^ 2)| * |Work.FTS.Regularity.gSlice g τ z θ| + |2 / (1 + z)| * |d1| := by
          simp only [abs_mul]
      _ ≤ 2 * N₁ + 2 * N₁ := add_le_add
          (mul_le_mul hφb hG1 (abs_nonneg _) (by norm_num))
          (mul_le_mul hφvb hb1 (abs_nonneg _) (by norm_num))
  have hbB : |B| ≤ 20 * N₄ + 10 * N₄ := by
    rw [hBdef]
    calc |fc * (2 * (1 - z) / (1 + z) ^ 3)
          * Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z + cc z * d4|
        ≤ |fc * (2 * (1 - z) / (1 + z) ^ 3)
            * Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z| + |cc z * d4| :=
          abs_add_le _ _
      _ = |fc * (2 * (1 - z) / (1 + z) ^ 3)|
            * |Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z| + |cc z| * |d4| := by
          simp only [abs_mul]
      _ ≤ 20 * N₄ + 10 * N₄ := add_le_add
          (mul_le_mul hccdb hG4 (abs_nonneg _) (by norm_num))
          (mul_le_mul hccb hb4 (abs_nonneg _) (by norm_num))
  have hbC : |C| ≤ 3 * N₃ + 3 * N₃ := by
    rw [hCdef]
    calc |-(3 / (1 + z) ^ 2) * Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ
          + 3 / (1 + z) * d3|
        ≤ |-(3 / (1 + z) ^ 2) * Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
            + |3 / (1 + z) * d3| := abs_add_le _ _
      _ = |-(3 / (1 + z) ^ 2)| * |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
            + |3 / (1 + z)| * |d3| := by simp only [abs_mul]
      _ ≤ 3 * N₃ + 3 * N₃ := add_le_add
          (mul_le_mul hψb hG3 (abs_nonneg _) (by norm_num))
          (mul_le_mul hψvb hb3 (abs_nonneg _) (by norm_num))
  have hbDv : |Dv| ≤ 20 * N₅ := by
    have h0 : Dv = fc * (2 * z * (2 - z) / (1 + z) ^ 4)
        * Work.Coercivity.L12f (Work.Coercivity.Transport (Work.FTS.Regularity.gSlice g τ)) 0 := by
      rw [hDvdef]; ring
    rw [h0, abs_mul]
    exact mul_le_mul hcadb hG5 (abs_nonneg _) (by norm_num)
  refine ⟨d1 + d2 - A - B - C + Dv, ?_, ?_⟩
  · -- the target function is exactly the sum of the five blocks
    refine hbig.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => ?_))
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    rw [LGammaT_eq_expansion]
  · -- the bound on the derivative
    have htri : |d1 + d2 - A - B - C + Dv| ≤ |d1| + |d2| + |A| + |B| + |C| + |Dv| := by
      have he : d1 + d2 - A - B - C + Dv = d1 + d2 + (-A) + (-B) + (-C) + Dv := by ring
      rw [he]
      simpa [abs_neg] using abs_sum_six_le d1 d2 (-A) (-B) (-C) Dv
    have h1' : 0 ≤ N₁ := hg.1.1
    have h2' : 0 ≤ N₂ := hDzg.1.1
    have h3' : 0 ≤ N₃ := hDthg.1.1
    have h4' : 0 ≤ N₄ := hL12.1.1
    have h5' : 0 ≤ N₅ := hL12T.1.1
    linarith [htri, hbA, hbB, hbC, hbDv, abs_nonneg d1, abs_nonneg d2, hb1, hb2]

/-! ## The requested theorem -/

theorem zderiv_LGammaT {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {N₁ N₂ N₃ N₄ N₅ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hg : Work.FTS.RegPkgGal.C1Jet α S N₁ g)
    (hDzg : Work.FTS.RegPkgGal.C1Jet α S N₂ (fun z θ τ => Work.Spaces.Dz (fun z θ => g z θ τ) z θ))
    (hDthg : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ => Work.Spaces.Dth (fun z θ => g z θ τ) z θ))
    (hL12 : Work.FTS.RegPkgGal.C1Jet α S N₄ (fun z θ τ => Work.Coercivity.L12f
      (Work.FTS.Regularity.gSlice g τ) z))
    (hL12T : Work.FTS.RegPkgGal.C1Jet α S N₅ (fun z θ τ => Work.Coercivity.L12f
      (fun z θ' => 3 * Work.Spaces.Dth (fun z θ => g z θ τ) z θ' / (1 + z)) 0)) :
    ∃ Nc : ℝ, Work.FTS.RegPkgGal.C1Jet α S Nc
      (fun z θ τ => Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) z θ) := by
  -- the `Jet` half — the five-term expansion with the coefficient estimates of `jet_coeff_all`
  obtain ⟨Nc₁, hJ⟩ := jet_LGammaT hα hα13 hS hg.1 hDzg.1 hDthg.1 hL12.1 hL12T.1
  -- the `z`-derivative half
  obtain ⟨Nc₂, -, hZ⟩ := zderiv_LGammaT_aux hα hα13 hS hg hDzg hDthg hL12 hL12T
  refine ⟨max Nc₁ Nc₂, ⟨jet_mono_N (le_max_left _ _) hJ, ?_⟩⟩
  intro τ hτ θ hθ z hz
  obtain ⟨d, hd, hb⟩ := hZ τ hτ θ hθ z hz
  exact ⟨d, hd, le_trans hb (le_max_right _ _)⟩

end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.zderiv_N =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.zderiv_N` — the `z`-derivative bound for `N`

`Work.FTS.RegPkgGal.C1Jet α S N h` bundles the two facts needed to differentiate the
constituents of the right-hand side of the fake-time equation in `z`:

* the joint `Jet` data (`Work.FTS.Regularity.Jet`: a uniform bound and a joint `α`-Hölder
  modulus on the strip `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]`), and
* the `z`-differentiability of every slice `z ↦ h z θ τ` on `z > 0` with derivative bounded
  by `N`, uniformly in `(θ,τ)`.

The target statement below (the `C1Jet` counterpart of `Der.jet_N`) says that the term

  `N αp F Φ = 2·ℛ(Φ̃)F - 2·U(Φ̃)∂_θF - 2αp·V(Φ̃)D_zF - (1/2)·sin2θ·(F,K)∂_θF - sin²θ·(F,K)F`

is a `C1Jet` whenever its seven constituents are (here `αp = pExp α = 3α`, `F = F_τ = F_* + g(τ)`
and `Φ̃ = ΦTil αp F Φ`).

## The contents of this file

Six closure lemmas for `C1Jet` (nothing else is needed — `N` is a sum of products of the
seven inputs, each scaled by a constant):

* `C1Jet.neg`, `C1Jet.add`, `C1Jet.mul`, `C1Jet.const_mul`, `C1Jet.congr`,
* `C1Jet.sin_sq` (the angular factor `sin²θ`, whose `z`-derivative vanishes),

and then `zderiv_N` itself, whose proof replicates the bookkeeping of `Der.jet_N`
(the `Jet`-closure of `N`) through the `z`-derivative clause.

**Trap (re-confirmed here).** Inside the proof of the closure lemmas, one must match
`HasDerivAt`-terms obtained from `C1Jet.zderiv` (elaborated in `Der.Defs`) against freshly
elaborated goals: `simpa only [Pi.add_apply]` / `Pi.neg_apply` fails on the (diamond) instance
arguments of `HasDerivAt`, while the plain `exact hda.add hdb` (`exact hd.neg`, …) works, the
two `Pi`-instances being definitionally equal on the nose.  Also
`HasDerivAt.congr_of_eventuallyEq` expects the eventual equality in the direction
`g =ᶠ f` (i.e. the *new* function on the left).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.FTS.RegPkgGal

/-- **`C1Jet` is closed under addition**, with the sum of the constants. -/
theorem C1Jet.add {α S N₁ N₂ : ℝ} {a b : ℝ → ℝ → ℝ → ℝ} (Ha : C1Jet α S N₁ a)
    (Hb : C1Jet α S N₂ b) :
    C1Jet α S (N₁ + N₂) (fun z θ τ => a z θ τ + b z θ τ) := by
  refine ⟨Ha.jet.add Hb.jet, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨da, hda, hdab⟩ := Ha.zderiv τ hτ θ hθ z hz
  obtain ⟨db, hdb, hdbb⟩ := Hb.zderiv τ hτ θ hθ z hz
  exact ⟨da + db, hda.add hdb, by
    calc |da + db| ≤ |da| + |db| := abs_add_le _ _
      _ ≤ N₁ + N₂ := add_le_add hdab hdbb⟩

/-- **`C1Jet` is closed under negation**, with the same constant. -/
theorem C1Jet.neg {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : C1Jet α S N h) :
    C1Jet α S N (fun z θ τ => -h z θ τ) := by
  refine ⟨H.jet.neg, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨d, hd, hdb⟩ := H.zderiv τ hτ θ hθ z hz
  exact ⟨-d, hd.neg, by simpa using hdb⟩

/-- **`C1Jet` is closed under multiplication**: the value bound is `2N₁N₂` (the `Jet.mul`
constant) and the derivative bound is *also* `2N₁N₂`, since the product rule
`(ab)' = a'b + ab'` is bounded by `N₁N₂ + N₁N₂`. -/
theorem C1Jet.mul {α S N₁ N₂ : ℝ} {a b : ℝ → ℝ → ℝ → ℝ} (Ha : C1Jet α S N₁ a)
    (Hb : C1Jet α S N₂ b) :
    C1Jet α S (2 * N₁ * N₂) (fun z θ τ => a z θ τ * b z θ τ) := by
  refine ⟨Ha.jet.mul Hb.jet, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨da, hda, hdab⟩ := Ha.zderiv τ hτ θ hθ z hz
  obtain ⟨db, hdb, hdbb⟩ := Hb.zderiv τ hτ θ hθ z hz
  have hza : 0 ≤ z := hz.le
  have hba : |a z θ τ| ≤ N₁ := Ha.jet.abs_le hza hθ hτ
  have hbb : |b z θ τ| ≤ N₂ := Hb.jet.abs_le hza hθ hτ
  exact ⟨da * b z θ τ + a z θ τ * db, hda.mul hdb, by
    calc |da * b z θ τ + a z θ τ * db|
        ≤ |da * b z θ τ| + |a z θ τ * db| := abs_add_le _ _
      _ = |da| * |b z θ τ| + |a z θ τ| * |db| := by rw [abs_mul, abs_mul]
      _ ≤ N₁ * N₂ + N₁ * N₂ := by
          exact add_le_add (mul_le_mul hdab hbb (abs_nonneg _) Ha.jet.nonneg)
            (mul_le_mul hba hdbb (abs_nonneg _) Ha.jet.nonneg)
      _ = 2 * N₁ * N₂ := by ring⟩

/-- **`C1Jet` is closed under scalar multiplication**, with constant `|c|·N` (the `Jet`
part is `Der.jetN_const_mul`). -/
theorem C1Jet.const_mul {α S N c : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : C1Jet α S N h) :
    C1Jet α S (|c| * N) (fun z θ τ => c * h z θ τ) := by
  refine ⟨Work.FTS.RegPkgGal.Der.jetN_const_mul H.jet, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨d, hd, hdb⟩ := H.zderiv τ hτ θ hθ z hz
  exact ⟨c * d, by simpa using hd.const_mul c, by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hdb (abs_nonneg c)⟩

/-- **`C1Jet` transports along a pointwise equality on the strip** (the `z`-derivative clause
by `HasDerivAt.congr_of_eventuallyEq`, using that `Ioi 0` is a neighbourhood of each of its
points). -/
theorem C1Jet.congr {α S N : ℝ} {a b : ℝ → ℝ → ℝ → ℝ} (Ha : C1Jet α S N a)
    (h : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → a z θ τ = b z θ τ) :
    C1Jet α S N b := by
  refine ⟨Ha.jet.congr h, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨d, hd, hdb⟩ := Ha.zderiv τ hτ θ hθ z hz
  refine ⟨d, hd.congr_of_eventuallyEq ?_, hdb⟩
  filter_upwards [IsOpen.mem_nhds isOpen_Ioi hz] with z' hz'
  exact (h z' θ τ hz'.le hθ hτ).symm

/-- The angular factor `θ ↦ sin²θ` is a `C1Jet` of constant `4` (`z`-independent, so the
derivative bound is trivial and the `Jet` part is `Der.jetN_sin_sq`). -/
theorem C1Jet.sin_sq {α S : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    C1Jet α S 4 (fun _ θ _ => Real.sin θ ^ 2) := by
  refine ⟨Work.FTS.RegPkgGal.Der.jetN_sin_sq hα hα1, ?_⟩
  intro τ hτ θ hθ z hz
  exact ⟨0, hasDerivAt_const z (Real.sin θ ^ 2), by norm_num⟩

end Work.FTS.RegPkgGal

namespace Work.FTS.RegPkgGal.Der


end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.HkNorm_triangle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The iterated `L²`-Minkowski step

For nonnegative `a`, `b` with the honest slicewise/integrated `L²` certificates, and any
nonnegative `c` dominated pointwise by `(a+b)²` on the domain,

`∫_z ∫_θ c ≤ (√(∫_z ∫_θ a²) + √(∫_z ∫_θ b²))²`

whenever the iterated integral of `c` is the honest one.  The proof applies the
one-dimensional `L²`-Minkowski inequality `integral_sq_add_le` in the variable `θ` (slicewise)
and then in the variable `z`, so that only the *angular* slices of `a`, `b` and the two
`z`-integrals `z ↦ ∫_θ a²`, `z ↦ ∫_θ b²` have to be measurable — the joint measurability of
`(a+b)²` is never needed. -/
theorem iterated_sq_integral_add_le {a b c : ℝ → ℝ → ℝ}
    (han : ∀ z θ, 0 ≤ a z θ) (hbn : ∀ z θ, 0 ≤ b z θ)
    (hsa : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => a z θ) (volume.restrict Work.Spaces.Iθ))
    (hsb : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => b z θ) (volume.restrict Work.Spaces.Iθ))
    (h2a : ∀ z ∈ Work.Spaces.Iz,
      Integrable (fun θ => a z θ ^ 2) (volume.restrict Work.Spaces.Iθ))
    (h2b : ∀ z ∈ Work.Spaces.Iz,
      Integrable (fun θ => b z θ ^ 2) (volume.restrict Work.Spaces.Iθ))
    (hAa : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
      (volume.restrict Work.Spaces.Iz))
    (hAb : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, b z θ ^ 2)
      (volume.restrict Work.Spaces.Iz))
    (hIa : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
      (volume.restrict Work.Spaces.Iz))
    (hIb : Integrable (fun z => ∫ θ in Work.Spaces.Iθ, b z θ ^ 2)
      (volume.restrict Work.Spaces.Iz))
    (hc : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, c z θ ≤ (a z θ + b z θ) ^ 2)
    (hcn : ∀ z θ, 0 ≤ c z θ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, c z θ)
      ≤ (Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
          + Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, b z θ ^ 2)) ^ 2 := by
  -- the angular slice of `(a+b)²` is integrable, being dominated by `2a² + 2b²`
  have hint_θ : ∀ z ∈ Work.Spaces.Iz,
      Integrable (fun θ => (a z θ + b z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    refine Integrable.mono' (((h2a z hz).const_mul 2).add ((h2b z hz).const_mul 2))
      (((hsa z hz).add (hsb z hz)).pow 2) (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    linarith [add_sq_le (a := a z θ) (b := b z θ)]
  -- slicewise: `∫_θ c ≤ (√∫_θ a² + √∫_θ b²)²`
  have hinner : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, c z θ)
      ≤ (Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
          + Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2)) ^ 2 := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, c z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (a z θ + b z θ) ^ 2 :=
      integral_mono_of_nonneg (Eventually.of_forall (fun θ => hcn z θ)) (hint_θ z hz)
        (ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hc z hz θ hθ))
    have h2 := integral_sq_add_le (μ := volume.restrict Work.Spaces.Iθ)
      (a := fun θ => a z θ) (b := fun θ => b z θ)
      (han z) (hbn z) (hsa z hz) (hsb z hz) (h2a z hz) (h2b z hz)
    linarith
  -- the `z`-integrand `(√∫_θ a² + √∫_θ b²)²` is integrable, being dominated by
  -- `2 ∫_θ a² + 2 ∫_θ b²`
  have hRHSint : Integrable (fun z => (Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
      + Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2)) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    refine Integrable.mono' ((hIa.const_mul 2).add (hIb.const_mul 2)) ?_
      (Eventually.of_forall fun z => ?_)
    · exact ((Real.continuous_sqrt.comp_aestronglyMeasurable hAa).add
        (Real.continuous_sqrt.comp_aestronglyMeasurable hAb)).pow 2
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      simp only [Pi.add_apply]
      have e1 : Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2) ^ 2
          = ∫ θ in Work.Spaces.Iθ, a z θ ^ 2 :=
        Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg _)
      have e2 : Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2) ^ 2
          = ∫ θ in Work.Spaces.Iθ, b z θ ^ 2 :=
        Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg _)
      linarith [add_sq_le (a := Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2))
        (b := Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2))]
  -- integrate the slicewise bound in `z`
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, c z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          (Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
            + Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2)) ^ 2 :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ => hcn z θ) hRHSint
      (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hinner z hz))
  have hIa' : Integrable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz) :=
    hIa.congr (Eventually.of_forall fun z =>
      (Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg _)).symm)
  have hIb' : Integrable (fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2) ^ 2)
      (volume.restrict Work.Spaces.Iz) :=
    hIb.congr (Eventually.of_forall fun z =>
      (Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg _)).symm)
  -- `L²`-Minkowski in the variable `z`
  have hz2 := integral_sq_add_le (μ := volume.restrict Work.Spaces.Iz)
    (a := fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2))
    (b := fun z => Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2))
    (fun z => Real.sqrt_nonneg _) (fun z => Real.sqrt_nonneg _)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hAa)
    (Real.continuous_sqrt.comp_aestronglyMeasurable hAb) hIa' hIb'
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, c z θ)
      ≤ ∫ z in Work.Spaces.Iz,
          (Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
            + Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2)) ^ 2 := houter
    _ ≤ (Real.sqrt (∫ z in Work.Spaces.Iz,
            Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2) ^ 2)
          + Real.sqrt (∫ z in Work.Spaces.Iz,
              Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2) ^ 2)) ^ 2 := hz2
    _ = (Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, a z θ ^ 2)
          + Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, b z θ ^ 2)) ^ 2 := by
        have e1 : (∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, a z θ ^ 2) ^ 2)
            = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, a z θ ^ 2 :=
          integral_congr_ae (Eventually.of_forall fun z =>
            Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg _))
        have e2 : (∫ z in Work.Spaces.Iz, Real.sqrt (∫ θ in Work.Spaces.Iθ, b z θ ^ 2) ^ 2)
            = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, b z θ ^ 2 :=
          integral_congr_ae (Eventually.of_forall fun z =>
            Real.sq_sqrt (integral_nonneg fun θ => sq_nonneg _))
        rw [e1, e2]

/-! ## The triangle inequality -/

theorem HkNorm_triangle (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      ≤ Work.Spaces.HkNorm α k f + Work.Spaces.HkNorm α k g := by
  -- the angular slices of `√(HkIntegrand ·)` are a.e. strongly measurable
  have hsa : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α k f z θ))
        (volume.restrict Work.Spaces.Iθ) := fun z hz =>
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (Work.FTS.StrongEps.aesm_slice_HkIntegrand_of_contDiffOn α k f (hf k) z hz)
  have hsb : ∀ z ∈ Work.Spaces.Iz,
      AEStronglyMeasurable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α k g z θ))
        (volume.restrict Work.Spaces.Iθ) := fun z hz =>
    Real.continuous_sqrt.comp_aestronglyMeasurable
      (Work.FTS.StrongEps.aesm_slice_HkIntegrand_of_contDiffOn α k g (hg k) z hz)
  -- their squares are integrable on each angular slice (`HkMem`)
  have h2a : ∀ z ∈ Work.Spaces.Iz,
      Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α k f z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := fun z hz =>
    (hmf.1 z hz).congr (Eventually.of_forall fun θ =>
      (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k f z θ)).symm)
  have h2b : ∀ z ∈ Work.Spaces.Iz,
      Integrable (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := fun z hz =>
    (hmg.1 z hz).congr (Eventually.of_forall fun θ =>
      (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k g z θ)).symm)
  -- the `z`-integrated squares are a.e. strongly measurable ...
  have hAa : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      Real.sqrt (Work.Spaces.HkIntegrand α k f z θ) ^ 2) (volume.restrict Work.Spaces.Iz) := by
    refine (Work.FTS.StrongEps.aesm_integral_HkIntegrand_of_contDiffOn α k f (hf k)).congr
      (Eventually.of_forall fun z => ?_)
    exact integral_congr_ae (Eventually.of_forall fun θ =>
      (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k f z θ)).symm)
  have hAb : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
      Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) ^ 2) (volume.restrict Work.Spaces.Iz) := by
    refine (Work.FTS.StrongEps.aesm_integral_HkIntegrand_of_contDiffOn α k g (hg k)).congr
      (Eventually.of_forall fun z => ?_)
    exact integral_congr_ae (Eventually.of_forall fun θ =>
      (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k g z θ)).symm)
  -- ... and integrable (`HkMem` again)
  have hIa : Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Real.sqrt (Work.Spaces.HkIntegrand α k f z θ) ^ 2) (volume.restrict Work.Spaces.Iz) :=
    hmf.2.congr (Eventually.of_forall fun z => integral_congr_ae
      (Eventually.of_forall fun θ =>
        (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k f z θ)).symm))
  have hIb : Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) ^ 2) (volume.restrict Work.Spaces.Iz) :=
    hmg.2.congr (Eventually.of_forall fun z => integral_congr_ae
      (Eventually.of_forall fun θ =>
        (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k g z θ)).symm))
  -- the pointwise bound `HkIntegrand (f+g) ≤ (√(HkIntegrand f) + √(HkIntegrand g))²`
  have hc : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ (Real.sqrt (Work.Spaces.HkIntegrand α k f z θ)
            + Real.sqrt (Work.Spaces.HkIntegrand α k g z θ)) ^ 2 := by
    intro z hz θ hθ
    have h1 := HkIntegrand_sqrt_add_le α k hf hg z hz θ hθ
    have h2 : Real.sqrt (Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ) ^ 2
        ≤ (Real.sqrt (Work.Spaces.HkIntegrand α k f z θ)
            + Real.sqrt (Work.Spaces.HkIntegrand α k g z θ)) ^ 2 := by
      nlinarith [h1, Real.sqrt_nonneg (Work.Spaces.HkIntegrand α k
        (fun z θ => f z θ + g z θ) z θ)]
    rwa [Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k _ z θ)] at h2
  have hcore := iterated_sq_integral_add_le
    (a := fun z θ => Real.sqrt (Work.Spaces.HkIntegrand α k f z θ))
    (b := fun z θ => Real.sqrt (Work.Spaces.HkIntegrand α k g z θ))
    (c := fun z θ => Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
    (fun z θ => Real.sqrt_nonneg _) (fun z θ => Real.sqrt_nonneg _)
    hsa hsb h2a h2b hAa hAb hIa hIb hc
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ)
  -- identify the two integrals with `HkSq`
  have hSqf : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Real.sqrt (Work.Spaces.HkIntegrand α k f z θ) ^ 2) = Work.Spaces.HkSq α k f := by
    rw [Work.Spaces.HkSq]
    exact integral_congr_ae (Eventually.of_forall fun z => integral_congr_ae
      (Eventually.of_forall fun θ => Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k f z θ)))
  have hSqg : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) ^ 2) = Work.Spaces.HkSq α k g := by
    rw [Work.Spaces.HkSq]
    exact integral_congr_ae (Eventually.of_forall fun z => integral_congr_ae
      (Eventually.of_forall fun θ => Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α k g z θ)))
  rw [hSqf, hSqg] at hcore
  -- take square roots
  have hgoal : Work.Spaces.HkNorm α k (fun z θ => f z θ + g z θ)
      = Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ) := rfl
  rw [hgoal]
  refine (Real.sqrt_le_sqrt hcore).trans (le_of_eq ?_)
  rw [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt (Work.Spaces.HkSq α k f)
      + Real.sqrt (Work.Spaces.HkSq α k g))]
  rfl

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.SP6.WlInf6OfFlatW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The assembly

`WlInf6_of_bounds` isolates the bookkeeping: given the two pointwise families of bounds
(the angular slot bound and the radial slot bound) it produces the `WlInfMem`-honesty and the
numerical estimate.  Both inputs are supplied by the two companion modules
`FTS/StrongPersist/SP6/AngSlot6.lean` and `FTS/StrongPersist/SP6/RadialSlot6.lean`. -/

/-- **The `𝒲^{6,∞}`-transfer, conditional on the two pointwise slot bounds.** -/
theorem WlInf6_of_bounds
    (hAng : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (K : ℝ),
      0 < α → α ≤ 1 → 0 ≤ K →
      (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 6 f K →
      ∀ (j k : ℕ), 1 ≤ j → k + j ≤ 6 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * K)
    (hRad : ∀ (f : ℝ → ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 6 f K →
      ∀ k : ℕ, k ≤ 6 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        |(z + 1) ^ k * Work.Spaces.pzIter k f z θ| ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (K : ℝ),
      0 < α → α ≤ 1 → (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 6 f K →
      Work.Spaces.WlInfMem α 6 f ∧ Work.Spaces.WlInf α 6 f ≤ C * K := by
  obtain ⟨Ca, hCa, hAng'⟩ := hAng
  refine ⟨7 + 49 * Ca, by positivity, ?_⟩
  intro α f K hα0 hα1 hzero hf hF
  -- `K ≥ 0`: the flat bound at the interior point `(1,1)` bounds `|f 1 1|`.
  have hK : 0 ≤ K := by
    have h := (hF 1 1 (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_three])).1 0 (by norm_num)
    have h' : |f 1 1| ≤ K := by simpa using h
    exact le_trans (abs_nonneg _) h'
  have hCaK : 0 ≤ Ca * K := mul_nonneg hCa.le hK
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- radial slots of `WlInfMem`
    intro k hk
    exact Work.Spaces.supFinite_of_pointwise
      (fun z hz θ hθ => hRad f K hK hzero hf hF k hk z hz θ hθ)
  · -- angular slots of `WlInfMem`
    intro j hj k hk hj1 hkj
    exact Work.Spaces.supFinite_of_pointwise
      (fun z hz θ hθ => hAng' α f K hα0 hα1 hK hzero hf hF j k hj1 hkj z hz θ hθ)
  · -- the numerical bound
    rw [Work.Spaces.WlInf]
    have h1 : (∑ k ∈ Finset.range (6 + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ))
        ≤ ((6 : ℝ) + 1) * K := by
      calc _ ≤ ∑ _k ∈ Finset.range (6 + 1), K := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk6 : k ≤ 6 := by rw [Finset.mem_range] at hk; omega
            exact Work.Spaces.supAbs_le
              (fun z hz θ hθ => hRad f K hK hzero hf hF k hk6 z hz θ hθ)
        _ = ((6 : ℝ) + 1) * K := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
    have h2 : (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
        if 1 ≤ j ∧ k + j ≤ 6 then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0) ≤ ((6 : ℝ) + 1) * ((6 : ℝ) + 1) * (Ca * K) := by
      calc _ ≤ ∑ _j ∈ Finset.range (6 + 1), ∑ _k ∈ Finset.range (6 + 1), (Ca * K) := by
            refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
            split_ifs with hcond
            · exact Work.Spaces.supAbs_le (fun z hz θ hθ =>
                hAng' α f K hα0 hα1 hK hzero hf hF j k hcond.1 hcond.2 z hz θ hθ)
            · exact hCaK
        _ = ((6 : ℝ) + 1) * ((6 : ℝ) + 1) * (Ca * K) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
              Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    calc (∑ k ∈ Finset.range (6 + 1),
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ))
          + (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
              if 1 ≤ j ∧ k + j ≤ 6 then
                Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                  * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
                  * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
              else 0)
        ≤ ((6 : ℝ) + 1) * K + ((6 : ℝ) + 1) * ((6 : ℝ) + 1) * (Ca * K) :=
          add_le_add h1 h2
      _ = (7 + 49 * Ca) * K := by ring

theorem WlInf6OfFlatW : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (K : ℝ),
    0 < α → α ≤ 1 → (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 6 f K →
    Work.Spaces.WlInfMem α 6 f ∧ Work.Spaces.WlInf α 6 f ≤ C * K := by
  refine WlInf6_of_bounds Work.FTS.StrongPersist.SP6.AngSlot6 ?_
  intro f K hK hzero hf hF k hk z hz θ hθ
  exact Work.FTS.StrongPersist.SP6.RadialSlot6 (l := 6) (k := k) hK hf hzero hF hk z hz θ hθ

end Work.FTS.StrongPersist.SP6
end
end
