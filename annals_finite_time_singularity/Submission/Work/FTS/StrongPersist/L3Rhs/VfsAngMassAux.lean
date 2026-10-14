import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Psi0Est.exists_ZClass
import Submission.Work.FTS.StrongPersist.L3Rhs.CoupledVfs
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS_RegExport.RXT.jc3_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Nonnegativity and smoothness -/

/-- `VfsAngMaj` is nonnegative on `Iθ`. -/
theorem VfsAngMaj_nonneg_d8f28c (α : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ VfsAngMaj α θ := by
  rw [VfsAngMaj]
  exact add_nonneg (angMaj_nonneg α (VfsA1 α) hθ) (angMaj_nonneg α (VfsA2 α) hθ)

lemma contDiffOn_VfsGc (α : ℝ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (VfsGc α) (Set.Ioo 0 (π / 2)) :=
  (Work.FTS.CoercivityFix.Transfer.Gam_contDiffOn_infty α).div_const (Work.Spaces.c α)

/-! ## 1. The jets of `VfsA1` are shifted jets of `Γ/c` -/

lemma dthU_iter_VfsA1_of_mem {α : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (i : ℕ) :
    Work.Spaces.dthU^[i] (VfsA1 α) θ = (3 / 2) * Work.Spaces.dthU^[i + 1] (VfsGc α) θ := by
  have hU : IsOpen (Set.Ioo (0 : ℝ) (π / 2)) := isOpen_Ioo
  have hY : ContDiffOn ℝ (∞ : ℕ∞ω) (Work.Spaces.dthU (VfsGc α))
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    Work.FTS.PhiStar.Psi0Est.dthU_iter_contDiffOn hU (contDiffOn_VfsGc α) 1
  have h := Work.FTS.PhiStar.Psi0Est.dthU_iter_const_mul_eqOn hU (3 / 2) hY i
  have h1 : Work.Spaces.dthU^[i] (fun x : ℝ => (3 / 2) * Work.Spaces.dthU (VfsGc α) x) θ
      = (3 / 2) * Work.Spaces.dthU^[i] (Work.Spaces.dthU (VfsGc α)) θ := h hθ
  have h2 : Work.Spaces.dthU^[i] (Work.Spaces.dthU (VfsGc α))
      = Work.Spaces.dthU^[i + 1] (VfsGc α) :=
    (Function.iterate_succ_apply Work.Spaces.dthU i (VfsGc α)).symm
  have h3 : VfsA1 α = fun x : ℝ => (3 / 2) * Work.Spaces.dthU (VfsGc α) x := rfl
  rw [h3, h1, h2]

/-! ## 2. The four-term expansion of `angMaj` -/

lemma angMaj_explicit (α : ℝ) (C : ℝ → ℝ) (θ : ℝ) :
    angMaj α C θ
      = (C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + (Work.Spaces.dthU^[1] C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + (Work.Spaces.dthU^[2] C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + (Work.Spaces.dthU^[3] C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [angMaj]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  ring

/-! ## 3. The `VfsA1` half -/

lemma angMaj_VfsA1_le {α : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hα : 0 ≤ α) :
    angMaj α (VfsA1 α) θ ≤ 9 * VfsJetMaj α θ := by
  have hmem : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hTp : 0 < Real.sin (2 * θ) := sin_two_pos_Ioo hθ
  have hstep : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := sin_two_rpow_eta_le_gam hα hθ
  have h1 : (Work.Spaces.dthU^[1] (VfsGc α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ VfsJetMaj α θ :=
    le_trans (mul_le_mul_of_nonneg_left hstep (sq_nonneg _))
      (VfsJetMaj_ge_gam α hmem (by norm_num) (by norm_num))
  have h2 : (Work.Spaces.dthU^[2] (VfsGc α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ VfsJetMaj α θ := VfsJetMaj_ge_gam α hmem (by norm_num) (by norm_num)
  have h3 : (Work.Spaces.dthU^[3] (VfsGc α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ VfsJetMaj α θ := VfsJetMaj_ge_gam α hmem (by norm_num) (by norm_num)
  have h4 : (Work.Spaces.dthU^[4] (VfsGc α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ VfsJetMaj α θ := VfsJetMaj_ge_gam α hmem (by norm_num) (by norm_num)
  have h0 : VfsA1 α θ = (3 / 2) * Work.Spaces.dthU^[1] (VfsGc α) θ := by
    have h := dthU_iter_VfsA1_of_mem (α := α) hθ 0
    simpa only [Function.iterate_zero_apply] using h
  rw [angMaj_explicit, dthU_iter_VfsA1_of_mem hθ 1, dthU_iter_VfsA1_of_mem hθ 2,
    dthU_iter_VfsA1_of_mem hθ 3, h0]
  nlinarith [h1, h2, h3, h4, sq_nonneg (Work.Spaces.dthU^[1] (VfsGc α) θ),
    sq_nonneg (Work.Spaces.dthU^[4] (VfsGc α) θ)]

/-! ## 4. Splitting sums over `range 5` at `0` -/

/-- The `range 5`-sum splits off its first term: `range 5 = insert 0 (Icc 1 4)`. -/
lemma sum_range_five_split (f : ℕ → ℝ) :
    ∑ m ∈ Finset.range 5, f m = f 0 + ∑ m ∈ Finset.Icc 1 4, f m := by
  have hset : Finset.range 5 = insert 0 (Finset.Icc 1 4) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by simp [Finset.mem_Icc])]

/-- The `Icc 1 4`-sum of the absolute values of the jets of `Γ/c`, together with the
`m = 0` term, is the `range 5`-sum. -/
lemma abs_jet_sum_eq (α : ℝ) (θ : ℝ) :
    |VfsGc α θ| + ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ|
      = ∑ m ∈ Finset.range 5, |Work.Spaces.dthU^[m] (VfsGc α) θ| := by
  rw [sum_range_five_split (fun m => |Work.Spaces.dthU^[m] (VfsGc α) θ|)]
  simp only [Function.iterate_zero_apply]

/-! ## 5. The `VfsA2` half -/

lemma angMaj_VfsA2_le {α : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hα0 : 0 < α)
    (hα1 : α ≤ 1) {B C2 : ℝ} (hB : 0 < B) (hC2pos : 0 < C2)
    (hc2 : ∀ j ≤ 4, |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ B)
    (hjet : ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
      |Work.Spaces.dthU^[i] (VfsA2 α) θ| ≤ C2 * B * α
        * (|VfsGc α θ| + ∑ m ∈ Finset.Icc 1 4,
            |Work.Spaces.dthU^[m] (VfsGc α) θ|)) :
    angMaj α (VfsA2 α) θ ≤ 100 * (B ^ 2 + C2 ^ 2 * B ^ 2) * VfsJetMaj α θ := by
  have hmem : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hTp : 0 < Real.sin (2 * θ) := sin_two_pos_Ioo hθ
  have hTη : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hTp.le _
  have hTγ : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hTp.le _
  have hα2 : α ^ 2 ≤ 1 := pow_le_one₀ hα0.le hα1
  have hc2θ : |Work.Construction.c2m θ| ≤ B := by
    have h := hc2 0 (by norm_num)
    simpa using h
  -- (i) the `η`-term
  have hη : (VfsA2 α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ B ^ 2 * VfsJetMaj α θ := by
    have hsq : (VfsA2 α θ) ^ 2
        = α ^ 2 * (VfsGc α θ) ^ 2 * (Work.Construction.c2m θ) ^ 2 := by
      rw [VfsA2]; ring
    rw [hsq]
    have h2 : α ^ 2 * (Work.Construction.c2m θ) ^ 2 ≤ B ^ 2 := by
      have h3 : (Work.Construction.c2m θ) ^ 2 ≤ B ^ 2 := by
        nlinarith [abs_le.mp hc2θ, sq_abs (Work.Construction.c2m θ)]
      calc α ^ 2 * (Work.Construction.c2m θ) ^ 2 ≤ 1 * B ^ 2 :=
            mul_le_mul hα2 h3 (sq_nonneg _) zero_le_one
        _ = B ^ 2 := one_mul _
    calc α ^ 2 * (VfsGc α θ) ^ 2 * (Work.Construction.c2m θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        = (α ^ 2 * (Work.Construction.c2m θ) ^ 2)
            * ((VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
      _ ≤ B ^ 2 * ((VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_right h2 (mul_nonneg (sq_nonneg _) hTη)
      _ ≤ B ^ 2 * VfsJetMaj α θ :=
          mul_le_mul_of_nonneg_left (VfsJetMaj_ge_eta α hmem) (sq_nonneg B)
  -- (ii) the three `γ`-terms
  have hγ : ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
      (Work.Spaces.dthU^[i] (VfsA2 α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 25 * C2 ^ 2 * B ^ 2 * VfsJetMaj α θ := by
    intro i hi1 hi3
    set S : ℝ := |VfsGc α θ| + ∑ m ∈ Finset.Icc 1 4,
      |Work.Spaces.dthU^[m] (VfsGc α) θ| with hSdef
    have hjeti : |Work.Spaces.dthU^[i] (VfsA2 α) θ| ≤ C2 * B * α * S := by
      have h := hjet i hi1 hi3
      rwa [hSdef]
    have hsq : (Work.Spaces.dthU^[i] (VfsA2 α) θ) ^ 2 ≤ (C2 * B * α) ^ 2 * S ^ 2 := by
      rw [← sq_abs]
      calc |Work.Spaces.dthU^[i] (VfsA2 α) θ| ^ 2 ≤ (C2 * B * α * S) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hjeti 2
        _ = (C2 * B * α) ^ 2 * S ^ 2 := by ring
    have hSsq : S ^ 2 ≤ 5 * ∑ m ∈ Finset.range 5,
        (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2 := by
      have h1 : S = ∑ m ∈ Finset.range 5, |Work.Spaces.dthU^[m] (VfsGc α) θ| := by
        rw [hSdef, abs_jet_sum_eq]
      rw [h1]
      simpa only [sq_abs] using
        sum_five_sq_le (fun m => |Work.Spaces.dthU^[m] (VfsGc α) θ|)
    -- the termwise domination by `VfsJetMaj`
    have hpart0 : α ^ 2 * ((VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ VfsJetMaj α θ := by
      have h := VfsJetMaj_ge_alpha α hmem
      rwa [mul_assoc] at h
    have hpartm : ∀ m ∈ Finset.Icc 1 4,
        α ^ 2 * ((Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ VfsJetMaj α θ := by
      intro m hm
      obtain ⟨hm1, hm4⟩ := Finset.mem_Icc.mp hm
      have h := VfsJetMaj_ge_gam α hmem hm1 hm4
      calc α ^ 2 * ((Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ 1 * ((Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
            mul_le_mul_of_nonneg_right hα2 (mul_nonneg (sq_nonneg _) hTγ)
        _ = (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := one_mul _
        _ ≤ VfsJetMaj α θ := h
    have hkey : ∀ m : ℕ, m < 5 → α ^ 2 * ((Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ VfsJetMaj α θ := by
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · exact hpart0
      · exact hpartm m (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hsum5 : (∑ m ∈ Finset.range 5, α ^ 2 * ((Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) ≤ 5 * VfsJetMaj α θ := by
      calc (∑ m ∈ Finset.range 5, α ^ 2 * ((Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
          ≤ ∑ _m ∈ Finset.range 5, VfsJetMaj α θ :=
            Finset.sum_le_sum (fun m hm => hkey m (Finset.mem_range.mp hm))
        _ = 5 * VfsJetMaj α θ := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
            norm_num
    have hsumEq : α ^ 2 * (∑ m ∈ Finset.range 5, (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = ∑ m ∈ Finset.range 5, α ^ 2 * ((Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    calc (Work.Spaces.dthU^[i] (VfsA2 α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ (C2 * B * α) ^ 2 * S ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hsq hTγ
      _ ≤ (C2 * B * α) ^ 2 * (5 * ∑ m ∈ Finset.range 5,
            (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
          refine mul_le_mul_of_nonneg_right ?_ hTγ
          exact mul_le_mul_of_nonneg_left hSsq (sq_nonneg _)
      _ = 5 * C2 ^ 2 * B ^ 2 * (α ^ 2 * (∑ m ∈ Finset.range 5,
            (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
      _ = 5 * C2 ^ 2 * B ^ 2 * (∑ m ∈ Finset.range 5, α ^ 2
            * ((Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by rw [hsumEq]
      _ ≤ 5 * C2 ^ 2 * B ^ 2 * (5 * VfsJetMaj α θ) :=
          mul_le_mul_of_nonneg_left hsum5 (by positivity)
      _ = 25 * C2 ^ 2 * B ^ 2 * VfsJetMaj α θ := by ring
  rw [angMaj_explicit]
  nlinarith [hη, hγ 1 (by norm_num) (by norm_num), hγ 2 (by norm_num) (by norm_num),
    hγ 3 (by norm_num) (by norm_num), sq_nonneg B, sq_nonneg C2, VfsJetMaj_nonneg α hmem]

/-! ## 6. Measurability -/

lemma measurable_dthU_iter (g : ℝ → ℝ) (hg : Measurable g) :
    ∀ m : ℕ, Measurable (Work.Spaces.dthU^[m] g) := by
  intro m
  induction m with
  | zero => simpa using hg
  | succ m _ =>
      rw [Function.iterate_succ_apply']
      show Measurable (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[m] g) θ)
      exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).mul
        (measurable_deriv _)

lemma measurable_angMaj (α : ℝ) (C : ℝ → ℝ) (hC : Measurable C) :
    Measurable (fun θ => angMaj α C θ) := by
  have hrpowE : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    fun_prop
  have hrpowG : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    fun_prop
  rw [funext (fun θ => angMaj_explicit α C θ)]
  have h1 : Measurable (fun θ : ℝ => (C θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := (hC.pow_const 2).mul hrpowE
  have h2 : Measurable (fun θ : ℝ => (Work.Spaces.dthU^[1] C θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    ((measurable_dthU_iter C hC 1).pow_const 2).mul hrpowG
  have h3 : Measurable (fun θ : ℝ => (Work.Spaces.dthU^[2] C θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    ((measurable_dthU_iter C hC 2).pow_const 2).mul hrpowG
  have h4 : Measurable (fun θ : ℝ => (Work.Spaces.dthU^[3] C θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    ((measurable_dthU_iter C hC 3).pow_const 2).mul hrpowG
  exact ((h1.add h2).add h3).add h4

lemma measurable_VfsGc (α : ℝ) : Measurable (VfsGc α) := by
  unfold VfsGc Work.Spaces.Gam
  fun_prop

lemma measurable_VfsJetMaj (α : ℝ) : Measurable (VfsJetMaj α) := by
  have hX : Measurable (VfsGc α) := measurable_VfsGc α
  have hrpowE : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
    fun_prop
  have hrpowG : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    fun_prop
  have hsum : Measurable (fun θ : ℝ => ∑ m ∈ Finset.Icc 1 4,
      (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    Finset.measurable_sum _ (fun m _ =>
      (((measurable_dthU_iter (VfsGc α) hX m)).pow_const 2).mul hrpowG)
  have hfun : VfsJetMaj α = fun θ : ℝ =>
      (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + ∑ m ∈ Finset.Icc 1 4, (Work.Spaces.dthU^[m] (VfsGc α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    funext θ
    rw [VfsJetMaj, VfsJetSum]
  rw [hfun]
  exact (((hX.pow_const 2).mul hrpowE).add
    (((hX.pow_const 2).const_mul (α ^ 2)).mul hrpowG)).add hsum

lemma measurable_VfsAngMaj (α : ℝ) : Measurable (VfsAngMaj α) := by
  have hX : Measurable (VfsGc α) := measurable_VfsGc α
  have hA1 : Measurable (VfsA1 α) := by
    show Measurable (fun θ : ℝ => (3 / 2) * Work.Spaces.dthU (VfsGc α) θ)
    exact measurable_const.mul (measurable_dthU_iter (VfsGc α) hX 1)
  have hA2 : Measurable (VfsA2 α) := by
    show Measurable (fun θ : ℝ => -α * Work.Construction.c2m θ * VfsGc α θ)
    refine (measurable_const.mul ?_).mul hX
    unfold Work.Construction.c2m
    fun_prop
  rw [show VfsAngMaj α = fun θ : ℝ => angMaj α (VfsA1 α) θ + angMaj α (VfsA2 α) θ from rfl]
  exact (measurable_angMaj α (VfsA1 α) hA1).add (measurable_angMaj α (VfsA2 α) hA2)

/-! ## 7. Assembly -/

theorem VfsAngMass_of_pieces
    (hMaj : ∀ α : ℝ, 0 < α → α ≤ 1 →
      MeasureTheory.IntegrableOn (VfsJetMaj α) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, VfsJetMaj α θ) ≤ 10 ^ 16)
    (hC2 : ∃ B : ℝ, 0 < B ∧ ∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ B)
    (hA2 : ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ), 0 < B →
      (∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ B) →
      ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        |Work.Spaces.dthU^[i] (VfsA2 α) θ|
          ≤ C * B * α * (|VfsGc α θ| + ∑ m ∈ Finset.Icc 1 4,
              |Work.Spaces.dthU^[m] (VfsGc α) θ|)) :
    ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc 0 1,
      MeasureTheory.IntegrableOn (VfsAngMaj α) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, VfsAngMaj α θ) ≤ K := by
  obtain ⟨B, hBpos, hc2⟩ := hC2
  obtain ⟨C2, hC2pos, hA2'⟩ := hA2
  have hK0 : 0 < 10 + 100 * (B ^ 2 + C2 ^ 2 * B ^ 2) := by positivity
  refine ⟨(10 + 100 * (B ^ 2 + C2 ^ 2 * B ^ 2)) * 10 ^ 16 + 1, by nlinarith, ?_⟩
  intro α hα
  obtain ⟨hα0, hα1⟩ := hα
  obtain ⟨hDint, hDmass⟩ := hMaj α hα0 hα1
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      VfsAngMaj α θ ≤ (10 + 100 * (B ^ 2 + C2 ^ 2 * B ^ 2)) * VfsJetMaj α θ := by
    intro θ hθ
    have hmem : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h1 : angMaj α (VfsA1 α) θ ≤ 9 * VfsJetMaj α θ := angMaj_VfsA1_le hθ hα0.le
    have h2 : angMaj α (VfsA2 α) θ ≤ 100 * (B ^ 2 + C2 ^ 2 * B ^ 2) * VfsJetMaj α θ :=
      angMaj_VfsA2_le hθ hα0 hα1 hBpos hC2pos
        (fun j hj => hc2 j hj θ hmem)
        (fun i hi1 hi3 => hA2' B hBpos hc2 α hα0 hα1 i hi1 hi3 θ hθ)
    rw [VfsAngMaj]
    nlinarith [h1, h2, sq_nonneg B, sq_nonneg C2, VfsJetMaj_nonneg α hmem]
  have hAmeas : MeasurableSet {θ : ℝ | ¬ (VfsAngMaj α θ
      ≤ (10 + 100 * (B ^ 2 + C2 ^ 2 * B ^ 2)) * VfsJetMaj α θ)} := by
    have heq : {θ : ℝ | ¬ (VfsAngMaj α θ
        ≤ (10 + 100 * (B ^ 2 + C2 ^ 2 * B ^ 2)) * VfsJetMaj α θ)}
        = {θ : ℝ | (10 + 100 * (B ^ 2 + C2 ^ 2 * B ^ 2)) * VfsJetMaj α θ
            < VfsAngMaj α θ} := by
      ext θ
      exact not_le
    rw [heq]
    exact measurableSet_lt ((measurable_VfsJetMaj α).const_mul _) (measurable_VfsAngMaj α)
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), VfsAngMaj α θ
      ≤ (10 + 100 * (B ^ 2 + C2 ^ 2 * B ^ 2)) * VfsJetMaj α θ := by
    rw [MeasureTheory.ae_iff, MeasureTheory.Measure.restrict_apply hAmeas]
    refine measure_mono_null ?_
      (((Set.finite_singleton (Real.pi / 2)).insert (0 : ℝ)).measure_zero volume)
    intro θ hθ
    rw [Set.mem_inter_iff] at hθ
    obtain ⟨hneg, hIθ⟩ := hθ
    by_contra hcon
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hcon
    push Not at hcon
    exact hneg (hpt θ ⟨lt_of_le_of_ne hIθ.1 (Ne.symm hcon.1),
      lt_of_le_of_ne hIθ.2 hcon.2⟩)
  have hnn : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ VfsAngMaj α θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact VfsAngMaj_nonneg_d8f28c α hθ
  have hIntg : MeasureTheory.Integrable
      (fun θ => (10 + 100 * (B ^ 2 + C2 ^ 2 * B ^ 2)) * VfsJetMaj α θ)
      (volume.restrict Work.Spaces.Iθ) := hDint.const_mul _
  have hInt : MeasureTheory.Integrable (VfsAngMaj α) (volume.restrict Work.Spaces.Iθ) :=
    hIntg.mono' (measurable_VfsAngMaj α).aestronglyMeasurable (by
      filter_upwards [hae, hnn] with θ h1 h2
      rwa [Real.norm_of_nonneg h2])
  refine ⟨hInt, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hInt hIntg hae
  rw [MeasureTheory.integral_const_mul] at hmono
  nlinarith [hmono, hDmass, hK0]

end Work.FTS.StrongPersist.L3Rhs
