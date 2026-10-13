/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pure `D_z` summand of the `H^4` product rule

For `f g` in the weighted space `H^4` of the paper, the "`Z`-summand"
`D_z^i (f·g) · w / sin(2θ)^{η/2}` of the `H^4`-integrand of the product is square
integrable with

`|D_z^i (f · g) · w/sin(2θ)^{η/2}|²_{L²} ≤ 10^{12}/(γ-1) · |f|²_{H⁴} · |g|²_{H⁴}`

for every `i ≤ 4`.

The proof expands `D_z^i (f·g)` by Leibniz, splits every resulting product
`D_z^b f · D_z^{i-b} g` into the factor carrying a large index (controlled in `L²`
with the light weight `w/sin(2θ)^{η/2}`, i.e. by a summand of the `H⁴`-norm) and
the factor with the complementary index at most `2` (controlled pointwise by the
`L^∞`-estimate `MixedSqPointwiseBound`), and sums.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.T2Aesm
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.HardyTheta
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.HkSq_mixed_le
import Submission.Work.Spaces.HkMem_mixed_le
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.MixedSqPointwiseBound
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.bt_aux

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
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! Everything below (except the final theorem) is auxiliary and lives in its own
namespace so that it cannot clash with colleagues' names. -/

namespace HPRZ

/-! ## The auxiliary data of the `Z`-summand

For the Leibniz expansion `D_z^i (f·g) = ∑_b C(i,b) D_z^b f · D_z^{i-b} g` we keep,
for each `b ≤ i`, the factor with index `> 2` (in `L²`, with the light weight) and
bound the other factor pointwise.  The following definitions record the retained
factor (`zsFun`, `zsIdx`), its `L^∞`-square (`zsGam`), the product with the weight
(`zsFb`), the coefficient (`zsAA`) and the assembled majorant `zsV`. -/

/-- The square of the `L^∞`-bound of the factor kept by the pointwise estimate:
`100/(γ-1)·|f|²_{H⁴}` when `b ≤ 2` (the factor `D_z^b f` is bounded by it) and
`100/(γ-1)·|g|²_{H⁴}` otherwise (the factor `D_z^{i-b} g` is bounded, `i - b ≤ 2`). -/
def zsGam (α : ℝ) (f g : ℝ → ℝ → ℝ) (b : ℕ) : ℝ :=
  if b ≤ 2 then (100 / (gam α - 1)) * HkSq α 4 f else (100 / (gam α - 1)) * HkSq α 4 g

/-- The function whose weighted `D_z`-iterate is kept in the `L²`-norm. -/
def zsFun (f g : ℝ → ℝ → ℝ) (b : ℕ) : ℝ → ℝ → ℝ := if b ≤ 2 then g else f

/-- The order of the weighted `D_z`-iterate kept in the `L²`-norm. -/
def zsIdx (i b : ℕ) : ℕ := if b ≤ 2 then i - b else b

/-- The summand of the majorant: the absolute value of the retained weighted
derivative. -/
def zsFb (f g : ℝ → ℝ → ℝ) (i b : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => |DzIter (zsIdx i b) (zsFun f g b) z θ
    * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|

/-- The coefficient of the summand `zsFb f g i b` in the majorant. -/
def zsAA (α : ℝ) (f g : ℝ → ℝ → ℝ) (i b : ℕ) : ℝ :=
  |(i.choose b : ℝ)| * Real.sqrt (zsGam α f g b)

/-- The majorant: the value of the pointwise estimate for the Leibniz expansion. -/
def zsV (α : ℝ) (f g : ℝ → ℝ → ℝ) (i : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ∑ b ∈ Finset.range (i + 1), zsAA α f g i b * zsFb f g i b z θ

theorem zsGam_apply (α : ℝ) (f g : ℝ → ℝ → ℝ) (b : ℕ) :
    zsGam α f g b = if b ≤ 2 then (100 / (gam α - 1)) * HkSq α 4 f
      else (100 / (gam α - 1)) * HkSq α 4 g := rfl

theorem zsFun_apply (f g : ℝ → ℝ → ℝ) (b : ℕ) :
    zsFun f g b = if b ≤ 2 then g else f := rfl

theorem zsIdx_apply (i b : ℕ) : zsIdx i b = if b ≤ 2 then i - b else b := rfl

theorem zsAA_apply (α : ℝ) (f g : ℝ → ℝ → ℝ) (i b : ℕ) :
    zsAA α f g i b = |(i.choose b : ℝ)| * Real.sqrt (zsGam α f g b) := rfl

theorem zsFb_apply (f g : ℝ → ℝ → ℝ) (i b : ℕ) (z θ : ℝ) :
    zsFb f g i b z θ = |DzIter (zsIdx i b) (zsFun f g b) z θ
      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := rfl

theorem zsV_apply (α : ℝ) (f g : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    zsV α f g i z θ
      = ∑ b ∈ Finset.range (i + 1), zsAA α f g i b * zsFb f g i b z θ := rfl

theorem zsGam_nonneg (α : ℝ) (hγ : 0 < gam α - 1) (f g : ℝ → ℝ → ℝ) (b : ℕ) :
    0 ≤ zsGam α f g b := by
  rw [zsGam_apply]
  split_ifs with h
  · exact mul_nonneg (div_nonneg (by norm_num) hγ.le) (HkSq_nonneg α 4 f)
  · exact mul_nonneg (div_nonneg (by norm_num) hγ.le) (HkSq_nonneg α 4 g)

theorem zsAA_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (i b : ℕ) : 0 ≤ zsAA α f g i b := by
  rw [zsAA_apply]
  exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

theorem zsFb_nonneg (f g : ℝ → ℝ → ℝ) (i b : ℕ) (z θ : ℝ) :
    0 ≤ zsFb f g i b z θ := by
  rw [zsFb_apply]
  exact abs_nonneg _

theorem zsGam_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (b : ℕ) (hb2 : b ≤ 2) :
    zsGam α f g b = (100 / (gam α - 1)) * HkSq α 4 f := by
  rw [zsGam_apply]; exact if_pos hb2

theorem zsGam_eq' (α : ℝ) (f g : ℝ → ℝ → ℝ) (b : ℕ) (hb2 : ¬ b ≤ 2) :
    zsGam α f g b = (100 / (gam α - 1)) * HkSq α 4 g := by
  rw [zsGam_apply]; exact if_neg hb2

theorem zsFun_eq (f g : ℝ → ℝ → ℝ) (b : ℕ) (hb2 : b ≤ 2) : zsFun f g b = g := by
  rw [zsFun_apply]; exact if_pos hb2

theorem zsFun_eq' (f g : ℝ → ℝ → ℝ) (b : ℕ) (hb2 : ¬ b ≤ 2) : zsFun f g b = f := by
  rw [zsFun_apply]; exact if_neg hb2

theorem zsIdx_eq (i b : ℕ) (hb2 : b ≤ 2) : zsIdx i b = i - b := by
  rw [zsIdx_apply]; exact if_pos hb2

theorem zsIdx_eq' (i b : ℕ) (hb2 : ¬ b ≤ 2) : zsIdx i b = b := by
  rw [zsIdx_apply]; exact if_neg hb2

theorem zsFb_eq (f g : ℝ → ℝ → ℝ) (i b : ℕ) (hb2 : b ≤ 2) :
    zsFb f g i b = fun z θ => |DzIter (i - b) g z θ
      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
  funext z θ
  simp only [zsFb_apply, zsIdx_eq i b hb2, zsFun_eq f g b hb2]

theorem zsFb_eq' (f g : ℝ → ℝ → ℝ) (i b : ℕ) (hb2 : ¬ b ≤ 2) :
    zsFb f g i b = fun z θ => |DzIter b f z θ
      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
  funext z θ
  simp only [zsFb_apply, zsIdx_eq' i b hb2, zsFun_eq' f g b hb2]

theorem zsAA_mul_zsFb_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (i b : ℕ) (z θ : ℝ) (hb2 : b ≤ 2) :
    zsAA α f g i b * zsFb f g i b z θ
      = |(i.choose b : ℝ)| * Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 f)
        * |DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
  simp only [zsAA_apply, zsGam_eq α f g b hb2, zsFb_apply, zsIdx_eq i b hb2,
    zsFun_eq f g b hb2]

theorem zsAA_mul_zsFb_eq' (α : ℝ) (f g : ℝ → ℝ → ℝ) (i b : ℕ) (z θ : ℝ) (hb2 : ¬ b ≤ 2) :
    zsAA α f g i b * zsFb f g i b z θ
      = |(i.choose b : ℝ)| * Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 g)
        * |DzIter b f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
  simp only [zsAA_apply, zsGam_eq' α f g b hb2, zsFb_apply, zsIdx_eq' i b hb2,
    zsFun_eq' f g b hb2]

/-! ## Measurability and membership of the retained factors -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

lemma Qd_subset_nbhU : Qd ⊆ nbhU := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  exact mem_nbhU (Set.mem_Ici.mpr (le_of_lt hz))
    (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

lemma sin_two_pos_Qd {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

lemma contOn_Hw_Qd :
    ContinuousOn (fun p : ℝ × ℝ => w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2)) Qd := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (eta / 2)) Qd :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
      (fun p hp => Or.inl (ne_of_gt (sin_two_pos_Qd hp.2)))
  have hw : ContinuousOn (fun p : ℝ × ℝ => w p.1) Qd := by
    simp only [w]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
  exact hw.div hsin (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Qd hp.2) _))

lemma contOn_DzIter_Qd (h : ℝ → ℝ → ℝ) (hsm : SmoothNbhd h) (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => DzIter m h p.1 p.2) Qd :=
  ((SmoothNbhd.DzIter hsm m).continuousOn).mono (fun p hp => Qd_subset_nbhU hp)

/-- A.e. strong measurability of the pure `D_z` summand of `HkIntegrand` on the
product measure. -/
theorem aesm_DzIter_H_weight_prod (h : ℝ → ℝ → ℝ) (hsm : SmoothNbhd h) (m : ℕ) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => DzIter m h p.1 p.2 * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2)))
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
  aesm_of_continuousOn_Qd _ ((contOn_DzIter_Qd h hsm m).mul contOn_Hw_Qd)

/-- A.e. strong measurability of the angular slice of the pure `D_z` summand. -/
theorem aesm_DzIter_H_weight_slice (h : ℝ → ℝ → ℝ) (hsm : SmoothNbhd h)
    (m : ℕ) {z : ℝ} (hz : z ∈ Iz) :
    AEStronglyMeasurable
      (fun θ : ℝ => DzIter m h z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2)))
      (volume.restrict Iθ) := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hpos
  · subst h0
    have hz0 : (fun θ : ℝ => DzIter m h 0 θ * (w 0 / (Real.sin (2 * θ)) ^ (eta / 2)))
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      simp [w]
    rw [hz0]
    exact aestronglyMeasurable_const
  · exact aesm_slice_of_continuousOn_Qd _
      ((contOn_DzIter_Qd h hsm m).mul contOn_Hw_Qd) hpos

/-- `L2Mem` for the pure `D_z` summand of the `H⁴`-integrand. -/
theorem L2Mem_DzIter_H_weight (α : ℝ) (h : ℝ → ℝ → ℝ) (hsm : SmoothNbhd h)
    (hmem : HkMem α 4 h) (b : ℕ) (hb : b ≤ 4) :
    L2Mem (fun z θ => DzIter b h z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) := by
  constructor
  · intro z hz
    refine Integrable.mono' (hmem.1 z hz) ((aesm_DzIter_H_weight_slice h hsm b hz).pow 2) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact sq_le_HkIntegrand_z α 4 h z θ b hb
  · have hjoint : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (DzIter b h p.1 p.2 * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))) ^ 2)
        ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
      (aesm_DzIter_H_weight_prod h hsm b).pow 2
    refine Integrable.mono' hmem.2 hjoint.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hmem.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ hθ => sq_le_HkIntegrand_z α 4 h z θ b hb))

/-! ## Elementary closure properties of `L2Mem` -/

theorem aesm_abs_of {γ : Type*} [MeasurableSpace γ] {μ : Measure γ} {F : γ → ℝ}
    (h : AEStronglyMeasurable F μ) : AEStronglyMeasurable (fun x => |F x|) μ := by
  simpa only [Real.norm_eq_abs] using h.norm

/-- A finite sum of a.e. strongly measurable functions is a.e. strongly measurable
(in the pointwise presentation, not the `Pi`-sum one). -/
theorem aesm_finset_sum {ι γ : Type*} [MeasurableSpace γ] {μ : Measure γ} (s : Finset ι)
    {f : ι → γ → ℝ} (h : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x => ∑ i ∈ s, f i x) μ := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h : AEStronglyMeasurable (fun _ : γ => (0 : ℝ)) μ := aestronglyMeasurable_const
      simpa only [Finset.sum_empty] using h
  | insert a s ha ih =>
      have hfun : (fun x => ∑ i ∈ insert a s, f i x) = (fun x => f a x + ∑ i ∈ s, f i x) := by
        funext x; rw [Finset.sum_insert ha]
      rw [hfun]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem L2Mem_abs {F : ℝ → ℝ → ℝ} (hF : L2Mem F) : L2Mem (fun z θ => |F z θ|) := by
  constructor
  · intro z hz
    simpa only [sq_abs] using hF.1 z hz
  · simpa only [sq_abs] using hF.2

theorem L2Sq_abs (F : ℝ → ℝ → ℝ) : L2Sq (fun z θ => |F z θ|) = L2Sq F := by
  simp only [L2Sq, sq_abs]

/-- Domination of `F` by an `L2Mem` function `U` transfers `L2Mem`, provided the
squares of `F` are measurable in the two required senses. -/
theorem L2Mem_of_abs_le {F U : ℝ → ℝ → ℝ} (hU : L2Mem U)
    (hFs : ∀ z ∈ Iz, AEStronglyMeasurable (fun θ => (F z θ) ^ 2) (volume.restrict Iθ))
    (hFo : AEStronglyMeasurable
      (fun z => ∫ θ, (F z θ) ^ 2 ∂(volume.restrict Iθ)) (volume.restrict Iz))
    (h : ∀ z ∈ Iz, ∀ θ ∈ Iθ, |F z θ| ≤ |U z θ|) : L2Mem F := by
  have hsq : ∀ z ∈ Iz, ∀ θ ∈ Iθ, (F z θ) ^ 2 ≤ (U z θ) ^ 2 := fun z hz θ hθ => by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h z hz θ hθ) 2
  constructor
  · intro z hz
    refine Integrable.mono' (hU.1 z hz) (hFs z hz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hsq z hz θ hθ
  · refine Integrable.mono' hU.2 hFo ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hU.1 z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ hθ => hsq z hz θ hθ))

/-! ## Finite sums of `L2Mem` functions -/

/-- A finite linear combination of `L2Mem` functions is `L2Mem`, and its squared `L²`
norm obeys the Cauchy–Schwarz estimate.  The two measurability hypotheses are what
the slices and the outer partial integral need; they are available in the application
below from `aesm_DzIter_H_weight_slice`/`_prod`. -/
theorem L2Mem_L2Sq_finset_sum_le {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℝ) (C : ι → ℝ)
    (hF : ∀ b ∈ s, L2Mem (F b))
    (hAE1 : ∀ z ∈ Iz, AEStronglyMeasurable
      (fun θ : ℝ => (∑ b ∈ s, C b * F b z θ) ^ 2) (volume.restrict Iθ))
    (hAE2 : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, (∑ b ∈ s, C b * F b z θ) ^ 2 ∂(volume.restrict Iθ))
      (volume.restrict Iz)) :
    L2Mem (fun z θ => ∑ b ∈ s, C b * F b z θ)
      ∧ L2Sq (fun z θ => ∑ b ∈ s, C b * F b z θ)
        ≤ (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * L2Sq (F b) := by
  have hpt : ∀ z θ : ℝ, (∑ b ∈ s, C b * F b z θ) ^ 2
      ≤ (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2 := by
    intro z θ
    refine le_trans (sq_sum_le_card_mul_sum_sq (s := s) (f := fun b => C b * F b z θ)) ?_
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun b hb => le_of_eq (by ring)) (Nat.cast_nonneg _)
  have hmaj_i : ∀ z ∈ Iz, Integrable
      (fun θ : ℝ => (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2)
      (volume.restrict Iθ) := by
    intro z hz
    exact (integrable_finsetSum s (fun b hb => (hF b hb).1 z hz |>.const_mul _)).const_mul _
  have hae_maj : (fun z : ℝ => (s.card : ℝ) * ∑ b ∈ s,
        (C b) ^ 2 * (∫ θ, (F b z θ) ^ 2 ∂(volume.restrict Iθ)))
      =ᵐ[volume.restrict Iz]
      (fun z : ℝ => ∫ θ, (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2
        ∂(volume.restrict Iθ)) := by
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    show (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (∫ θ, (F b z θ) ^ 2 ∂(volume.restrict Iθ))
      = ∫ θ, (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2 ∂(volume.restrict Iθ)
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum s
      (f := fun b θ => (C b) ^ 2 * (F b z θ) ^ 2) (fun b hb => (hF b hb).1 z hz |>.const_mul _)]
    exact Finset.sum_congr rfl fun b hb => (integral_const_mul _ _).symm
  have hmaj_z : Integrable
      (fun z : ℝ => ∫ θ, (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2
        ∂(volume.restrict Iθ)) (volume.restrict Iz) := by
    have hg : Integrable (fun z : ℝ => (s.card : ℝ) * ∑ b ∈ s,
        (C b) ^ 2 * (∫ θ, (F b z θ) ^ 2 ∂(volume.restrict Iθ))) (volume.restrict Iz) :=
      (integrable_finsetSum s (fun b hb => (hF b hb).2.const_mul _)).const_mul _
    exact hg.congr hae_maj
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    refine Integrable.mono' (hmaj_i z hz) (hAE1 z hz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt z θ
  · refine Integrable.mono' hmaj_z hAE2 ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _))
      (hmaj_i z hz)
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => hpt z θ))
  · rw [L2Sq]
    have hmain : ∫ z in Iz, ∫ θ in Iθ, (∑ b ∈ s, C b * F b z θ) ^ 2
        ≤ ∫ z in Iz, ∫ θ in Iθ, (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2 := by
      refine integral_mono_of_nonneg
        (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hmaj_z ?_
      filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
      refine integral_mono_of_nonneg
        (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
          (fun θ _ => sq_nonneg _))
        (hmaj_i z hz) ?_
      filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
      exact hpt z θ
    have hval : ∫ z in Iz, ∫ θ in Iθ, (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * (F b z θ) ^ 2
        = (s.card : ℝ) * ∑ b ∈ s, (C b) ^ 2 * L2Sq (F b) := by
      rw [← integral_congr_ae hae_maj]
      rw [integral_const_mul,
        integral_finsetSum s
          (f := fun b z => (C b) ^ 2 * (∫ θ, (F b z θ) ^ 2 ∂(volume.restrict Iθ)))
          (fun b hb => (hF b hb).2.const_mul _)]
      congr 1
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [integral_const_mul]
      simp only [L2Sq]
    exact le_trans hmain (le_of_eq hval)

/-! ## The coefficient estimate -/

theorem zs_coeff_bound (i : ℕ) (hi : i ≤ 4) :
    ((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2) * 100 ≤ 10 ^ 12 := by
  have hterm : ∀ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2 ≤ 256 := by
    intro b hb
    have hb' : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
    have h2 : (2 : ℕ) ^ i ≤ 16 := by interval_cases i <;> norm_num
    have h3 : i.choose b ≤ 16 := le_trans h1 h2
    have h4 : ((i.choose b : ℕ) : ℝ) ≤ 16 := by exact_mod_cast h3
    nlinarith [h4, Nat.cast_nonneg (α := ℝ) (i.choose b)]
  have hsum : (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2) ≤ 1280 := by
    have h := Finset.sum_le_card_nsmul (Finset.range (i + 1))
      (fun b => (i.choose b : ℝ) ^ 2) 256 hterm
    simp only [nsmul_eq_mul] at h
    have hcard : ((Finset.range (i + 1)).card : ℝ) ≤ 5 := by
      simp only [Finset.card_range]
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_succ_of_le hi)
    nlinarith [h, hcard]
  have h0 : (0 : ℝ) ≤ ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hi5 : ((i : ℝ) + 1) ≤ 5 := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_succ_of_le hi)
  nlinarith [hsum, h0, hi5]

end HPRZ

open HPRZ

/-! ## The theorem -/

theorem HProductRule_Zsummand (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (hsmf : Work.Spaces.SmoothNbhd f) (hsimg : Work.Spaces.SmoothNbhd g)
    (hvtf : Work.Spaces.VanishTheta f) (hvtg : Work.Spaces.VanishTheta g)
    (hdecf : Work.Spaces.DecayMixed 2 f) (hdecg : Work.Spaces.DecayMixed 2 g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (i : ℕ) (hi : i ≤ 4) :
    Work.Spaces.L2Mem (fun z θ => Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      ∧ Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter i (fun z θ => f z θ * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        ≤ (10 ^ 12 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g := by
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hsmFG : SmoothNbhd (fun z θ => f z θ * g z θ) := by
    show ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ => f z θ * g z θ)) nbhU
    have he : Function.uncurry (fun z θ => f z θ * g z θ)
        = Function.uncurry f * Function.uncurry g := rfl
    rw [he]
    exact hsmf.mul hsimg
  -- ## Step 1: the pointwise bound by the majorant
  have hpt : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      |DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| ≤ zsV α f g i z θ := by
    intro z hz θ hθ
    have hL := DzIter_mul i f g hz (hardyZ_contDiffOn_slice f hsmf hθ)
      (hardyZ_contDiffOn_slice g hsimg hθ)
    have hX : DzIter i (fun z θ => f z θ * g z θ) z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))
        = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
            * (DzIter b f z θ * DzIter (i - b) g z θ)
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2)) := by
      rw [hL, Finset.sum_mul]
    rw [hX, zsV_apply α f g i z θ]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun b hb => ?_)
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    by_cases hb2 : b ≤ 2
    · have hbnd : (DzIter b f z θ) ^ 2 ≤ (100 / (gam α - 1)) * HkSq α 4 f :=
        MixedSqPointwiseBound α hα hα1 f hsmf hvtf hdecf hmemf b 0 (by omega) z hz θ hθ
      have habs : |DzIter b f z θ| ≤ Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 f) :=
        Real.abs_le_sqrt hbnd
      rw [zsAA_mul_zsFb_eq α f g i b z θ hb2]
      calc |(i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ)
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|
          = (|(i.choose b : ℝ)| * |DzIter b f z θ|)
              * (|DzIter (i - b) g z θ| * |w z / (Real.sin (2 * θ)) ^ (eta / 2)|) := by
            simp only [abs_mul]; ring
        _ ≤ (|(i.choose b : ℝ)| * Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 f))
              * (|DzIter (i - b) g z θ| * |w z / (Real.sin (2 * θ)) ^ (eta / 2)|) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left habs (abs_nonneg _))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = |(i.choose b : ℝ)| * Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 f)
              * |DzIter (i - b) g z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
            rw [abs_mul] <;> ring
    · have hbnd : (DzIter (i - b) g z θ) ^ 2 ≤ (100 / (gam α - 1)) * HkSq α 4 g :=
        MixedSqPointwiseBound α hα hα1 g hsimg hvtg hdecg hmemg (i - b) 0 (by omega) z hz θ hθ
      have habs : |DzIter (i - b) g z θ| ≤ Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 g) :=
        Real.abs_le_sqrt hbnd
      rw [zsAA_mul_zsFb_eq' α f g i b z θ hb2]
      calc |(i.choose b : ℝ) * (DzIter b f z θ * DzIter (i - b) g z θ)
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|
          = (|(i.choose b : ℝ)| * |DzIter b f z θ|)
              * (|DzIter (i - b) g z θ| * |w z / (Real.sin (2 * θ)) ^ (eta / 2)|) := by
            simp only [abs_mul]; ring
        _ ≤ (|(i.choose b : ℝ)| * |DzIter b f z θ|)
              * (Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 g)
                * |w z / (Real.sin (2 * θ)) ^ (eta / 2)|) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right habs (abs_nonneg _))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = |(i.choose b : ℝ)| * Real.sqrt ((100 / (gam α - 1)) * HkSq α 4 g)
              * |DzIter b f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| := by
            rw [abs_mul] <;> ring
  -- the majorant dominates `|X|`
  have hXle : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      |DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|
        ≤ |∑ b ∈ Finset.range (i + 1), zsAA α f g i b * zsFb f g i b z θ| := by
    intro z hz θ hθ
    have h1 : |DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))| ≤ zsV α f g i z θ := hpt z hz θ hθ
    rw [zsV_apply α f g i z θ] at h1
    have h2 : (0 : ℝ) ≤ ∑ b ∈ Finset.range (i + 1), zsAA α f g i b * zsFb f g i b z θ :=
      Finset.sum_nonneg fun b hb => mul_nonneg (zsAA_nonneg α f g i b) (zsFb_nonneg f g i b z θ)
    rwa [abs_of_nonneg h2]
  -- ## Step 2: membership of the summands and of the majorant
  have hpiece : ∀ b ∈ Finset.range (i + 1), L2Mem (zsFb f g i b) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    by_cases hb2 : b ≤ 2
    · have h := L2Mem_DzIter_H_weight α g hsimg hmemg (i - b) (by omega)
      rw [zsFb_eq f g i b hb2]
      exact L2Mem_abs h
    · have h := L2Mem_DzIter_H_weight α f hsmf hmemf b (by omega)
      rw [zsFb_eq' f g i b hb2]
      exact L2Mem_abs h
  have hV_slice_aesm : ∀ z ∈ Iz, AEStronglyMeasurable
      (fun θ : ℝ => (∑ b ∈ Finset.range (i + 1), zsAA α f g i b * zsFb f g i b z θ) ^ 2)
      (volume.restrict Iθ) := by
    intro z hz
    have h1 : AEStronglyMeasurable
        (fun θ : ℝ => ∑ b ∈ Finset.range (i + 1), zsAA α f g i b * zsFb f g i b z θ)
        (volume.restrict Iθ) :=
      aesm_finset_sum _ (fun b hb => by
        by_cases hb2 : b ≤ 2
        · have h : AEStronglyMeasurable (fun θ : ℝ => |DzIter (i - b) g z θ
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|) (volume.restrict Iθ) :=
            aesm_abs_of (aesm_DzIter_H_weight_slice g hsimg (i - b) hz)
          rw [zsFb_eq f g i b hb2]
          exact h.const_mul (zsAA α f g i b)
        · have h : AEStronglyMeasurable (fun θ : ℝ => |DzIter b f z θ
              * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|) (volume.restrict Iθ) :=
            aesm_abs_of (aesm_DzIter_H_weight_slice f hsmf b hz)
          rw [zsFb_eq' f g i b hb2]
          exact h.const_mul (zsAA α f g i b))
    exact h1.pow 2
  have hV_outer_aesm : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, (∑ b ∈ Finset.range (i + 1), zsAA α f g i b * zsFb f g i b z θ) ^ 2
        ∂(volume.restrict Iθ)) (volume.restrict Iz) := by
    have hj : AEStronglyMeasurable
        (fun p : ℝ × ℝ => ∑ b ∈ Finset.range (i + 1), zsAA α f g i b * zsFb f g i b p.1 p.2)
        ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
      aesm_finset_sum _ (fun b hb => by
        by_cases hb2 : b ≤ 2
        · have h : AEStronglyMeasurable (fun p : ℝ × ℝ => |DzIter (i - b) g p.1 p.2
              * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))|)
              ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
            aesm_abs_of (aesm_DzIter_H_weight_prod g hsimg (i - b))
          rw [zsFb_eq f g i b hb2]
          exact h.const_mul (zsAA α f g i b)
        · have h : AEStronglyMeasurable (fun p : ℝ × ℝ => |DzIter b f p.1 p.2
              * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))|)
              ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
            aesm_abs_of (aesm_DzIter_H_weight_prod f hsmf b)
          rw [zsFb_eq' f g i b hb2]
          exact h.const_mul (zsAA α f g i b))
    exact (hj.pow 2).integral_prod_right'
  have hV := L2Mem_L2Sq_finset_sum_le (Finset.range (i + 1)) (zsFb f g i) (zsAA α f g i)
    hpiece hV_slice_aesm hV_outer_aesm
  have hVmem : L2Mem (fun z θ => ∑ b ∈ Finset.range (i + 1),
      zsAA α f g i b * zsFb f g i b z θ) := hV.1
  have hVbd : L2Sq (fun z θ => ∑ b ∈ Finset.range (i + 1), zsAA α f g i b * zsFb f g i b z θ)
      ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (zsAA α f g i b) ^ 2 * L2Sq (zsFb f g i b) := by
    simpa using hV.2
  have hXmem : L2Mem (fun z θ => DzIter i (fun z θ => f z θ * g z θ) z θ
      * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) := by
    refine L2Mem_of_abs_le hVmem ?_ ?_ ?_
    · intro z hz
      exact (aesm_DzIter_H_weight_slice (fun z θ => f z θ * g z θ) hsmFG i hz).pow 2
    · exact ((aesm_DzIter_H_weight_prod (fun z θ => f z θ * g z θ) hsmFG i).pow 2)
        |>.integral_prod_right'
    · intro z hz θ hθ
      exact hXle z hz θ hθ
  -- ## Step 3: the squared `L²` bounds
  have hmono : L2Sq (fun z θ => DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2)))
      ≤ L2Sq (fun z θ => ∑ b ∈ Finset.range (i + 1), zsAA α f g i b * zsFb f g i b z θ) := by
    rw [L2Sq, L2Sq]
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hVmem.2 ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iz from measurableSet_Ici)] with z hz
    refine integral_mono_of_nonneg
      (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc)
        (fun θ _ => sq_nonneg _)) (hVmem.1 z hz) ?_
    filter_upwards [ae_restrict_mem (show MeasurableSet Iθ from measurableSet_Icc)] with θ hθ
    have h := pow_le_pow_left₀ (abs_nonneg _) (hXle z hz θ hθ) 2
    simpa only [sq_abs] using h
  have hpiecebd : ∀ b ∈ Finset.range (i + 1),
      (zsAA α f g i b) ^ 2 * L2Sq (zsFb f g i b)
        ≤ (i.choose b : ℝ) ^ 2 * ((100 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have haa : (zsAA α f g i b) ^ 2 = (i.choose b : ℝ) ^ 2 * zsGam α f g b := by
      rw [zsAA_apply, mul_pow, sq_abs]
      congr 1
      exact Real.sq_sqrt (zsGam_nonneg α hγ f g b)
    have hL2 : L2Sq (zsFb f g i b) ≤ HkSq α 4 (zsFun f g b) := by
      by_cases hb2 : b ≤ 2
      · have h := L2Sq_DzIter_le_HkSq α 4 g hmemg (i - b) (by omega)
        have h' : L2Sq (fun z θ => |DzIter (i - b) g z θ
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|) ≤ HkSq α 4 g := by
          rw [L2Sq_abs]; exact h
        rw [zsFb_eq f g i b hb2, zsFun_eq f g b hb2]
        exact h'
      · have h := L2Sq_DzIter_le_HkSq α 4 f hmemf b (by omega)
        have h' : L2Sq (fun z θ => |DzIter b f z θ
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|) ≤ HkSq α 4 f := by
          rw [L2Sq_abs]; exact h
        rw [zsFb_eq' f g i b hb2, zsFun_eq' f g b hb2]
        exact h'
    have hΓHk : zsGam α f g b * HkSq α 4 (zsFun f g b)
        = (100 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g := by
      by_cases hb2 : b ≤ 2
      · rw [zsGam_eq α f g b hb2, zsFun_eq f g b hb2] <;> ring
      · rw [zsGam_eq' α f g b hb2, zsFun_eq' f g b hb2] <;> ring
    calc (zsAA α f g i b) ^ 2 * L2Sq (zsFb f g i b)
        ≤ ((i.choose b : ℝ) ^ 2 * zsGam α f g b) * HkSq α 4 (zsFun f g b) := by
          rw [haa]
          exact mul_le_mul_of_nonneg_left hL2
            (mul_nonneg (sq_nonneg _) (zsGam_nonneg α hγ f g b))
      _ = (i.choose b : ℝ) ^ 2 * ((100 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g) := by
          rw [show ((i.choose b : ℝ) ^ 2 * zsGam α f g b) * HkSq α 4 (zsFun f g b)
              = (i.choose b : ℝ) ^ 2 * (zsGam α f g b * HkSq α 4 (zsFun f g b)) from by ring,
            hΓHk]
  have hsum : (∑ b ∈ Finset.range (i + 1), (zsAA α f g i b) ^ 2 * L2Sq (zsFb f g i b))
      ≤ (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
        * ((100 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g) := by
    calc (∑ b ∈ Finset.range (i + 1), (zsAA α f g i b) ^ 2 * L2Sq (zsFb f g i b))
        ≤ ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2
            * ((100 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g) :=
          Finset.sum_le_sum hpiecebd
      _ = (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
            * ((100 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g) :=
          (Finset.sum_mul ..).symm
  have hfinal : ((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
        * ((100 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g)
      ≤ (10 ^ 12 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g := by
    have hstep : ((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
          * (100 / (gam α - 1)) ≤ 10 ^ 12 / (gam α - 1) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (zs_coeff_bound i hi) hγ.le
    calc ((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
          * ((100 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g)
        = (((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
            * (100 / (gam α - 1))) * (HkSq α 4 f * HkSq α 4 g) := by ring
      _ ≤ (10 ^ 12 / (gam α - 1)) * (HkSq α 4 f * HkSq α 4 g) :=
          mul_le_mul_of_nonneg_right hstep
            (mul_nonneg (HkSq_nonneg α 4 f) (HkSq_nonneg α 4 g))
      _ = (10 ^ 12 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g := by ring
  refine ⟨hXmem, ?_⟩
  calc L2Sq (fun z θ => DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2)))
      ≤ L2Sq (fun z θ => ∑ b ∈ Finset.range (i + 1), zsAA α f g i b * zsFb f g i b z θ) := hmono
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (zsAA α f g i b) ^ 2 * L2Sq (zsFb f g i b) := hVbd
    _ ≤ ((i : ℝ) + 1) * ((∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
          * ((100 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g)) := by
        refine mul_le_mul_of_nonneg_left hsum ?_
        positivity
    _ = ((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
          * ((100 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g) := by ring
    _ ≤ (10 ^ 12 / (gam α - 1)) * HkSq α 4 f * HkSq α 4 g := hfinal

end Work.Spaces
