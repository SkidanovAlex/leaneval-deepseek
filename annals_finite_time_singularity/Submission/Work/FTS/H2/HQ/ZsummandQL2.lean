import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.HQ.ZsummandQDefs
import Submission.Work.Spaces.HProductRule_Zsummand

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.HQ

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-- The majorant `zsVQ` of the `Z`-summand is square integrable, with

`|zsVQ|²_{L²} ≤ 10¹²/(γ-1)·(Cf+Cg)·|f|²_{ℋ⁴}·|g|²_{ℋ⁴}`.

Each summand of `zsVQ` is `|C(i,b)|·√(zsGamQ b)·|D_z^{zsIdxQ i b}(zsFunQ f g b)·w/sin(2θ)^{η/2}|`:
its `L²`-norm is bounded by `HkSq` of the retained factor (`L2Sq_DzIter_le_HkSq`) and the finitely
many summands are combined with the Cauchy–Schwarz estimate of
`Work.Spaces.HPRZ.L2Mem_L2Sq_finset_sum_le`. -/
theorem ZsummandQL2 (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ) (hγ : 0 < Work.Spaces.gam α - 1)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (i : ℕ) (hi : i ≤ 4)
    (hf : Work.FTS.LocData.SmoothQuad f) (hg : Work.FTS.LocData.SmoothQuad g)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g) :
    Work.Spaces.L2Mem (Work.FTS.H2.HQ.zsVQ α f g Cf Cg i)
      ∧ Work.Spaces.L2Sq (Work.FTS.H2.HQ.zsVQ α f g Cf Cg i)
        ≤ 10 ^ 12 / (Work.Spaces.gam α - 1) * (Cf + Cg) * Work.Spaces.HkSq α 4 f
            * Work.Spaces.HkSq α 4 g := by
  -- ## Step 1: membership of the retained pieces
  have hpiece : ∀ b ∈ Finset.range (i + 1), L2Mem (zsFbQ f g i b) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    by_cases hb2 : b ≤ 2
    · have h := L2Mem_light_quad α g hg hmg (i - b) (by omega)
      rw [zsFbQ_eq f g i b hb2]
      exact Work.Spaces.HPRZ.L2Mem_abs h
    · have h := L2Mem_light_quad α f hf hmf b (by omega)
      rw [zsFbQ_eq' f g i b hb2]
      exact Work.Spaces.HPRZ.L2Mem_abs h
  -- ## Step 2: the two a.e. strong measurability hypotheses for the sum
  have hslice_aesm : ∀ z ∈ Iz, AEStronglyMeasurable
      (fun θ : ℝ => (∑ b ∈ Finset.range (i + 1),
        zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ) ^ 2) (volume.restrict Iθ) := by
    intro z hz
    have h1 : AEStronglyMeasurable
        (fun θ : ℝ => ∑ b ∈ Finset.range (i + 1),
          zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ) (volume.restrict Iθ) :=
      Work.Spaces.HPRZ.aesm_finset_sum (Finset.range (i + 1))
        (f := fun b (θ : ℝ) => zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ)
        (fun b _ => by
          by_cases hb2 : b ≤ 2
          · have h : AEStronglyMeasurable (fun θ : ℝ => |DzIter (i - b) g z θ
                * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|) (volume.restrict Iθ) :=
              Work.Spaces.HPRZ.aesm_abs_of (aesm_light_slice g hg (i - b) hz)
            rw [zsFbQ_eq f g i b hb2]
            exact h.const_mul (zsAAQ α f g Cf Cg i b)
          · have h : AEStronglyMeasurable (fun θ : ℝ => |DzIter b f z θ
                * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|) (volume.restrict Iθ) :=
              Work.Spaces.HPRZ.aesm_abs_of (aesm_light_slice f hf b hz)
            rw [zsFbQ_eq' f g i b hb2]
            exact h.const_mul (zsAAQ α f g Cf Cg i b))
    exact h1.pow 2
  have houter_aesm : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, (∑ b ∈ Finset.range (i + 1),
        zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ) ^ 2 ∂(volume.restrict Iθ))
      (volume.restrict Iz) := by
    have hj : AEStronglyMeasurable
        (fun p : ℝ × ℝ => ∑ b ∈ Finset.range (i + 1),
          zsAAQ α f g Cf Cg i b * zsFbQ f g i b p.1 p.2)
        ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
      Work.Spaces.HPRZ.aesm_finset_sum (Finset.range (i + 1))
        (f := fun b (p : ℝ × ℝ) => zsAAQ α f g Cf Cg i b * zsFbQ f g i b p.1 p.2)
        (fun b _ => by
          by_cases hb2 : b ≤ 2
          · have h : AEStronglyMeasurable (fun p : ℝ × ℝ => |DzIter (i - b) g p.1 p.2
                * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))|)
                ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
              Work.Spaces.HPRZ.aesm_abs_of (aesm_light_prod g hg (i - b))
            rw [zsFbQ_eq f g i b hb2]
            exact h.const_mul (zsAAQ α f g Cf Cg i b)
          · have h : AEStronglyMeasurable (fun p : ℝ × ℝ => |DzIter b f p.1 p.2
                * (w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2))|)
                ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
              Work.Spaces.HPRZ.aesm_abs_of (aesm_light_prod f hf b)
            rw [zsFbQ_eq' f g i b hb2]
            exact h.const_mul (zsAAQ α f g Cf Cg i b))
    exact (hj.pow 2).integral_prod_right'
  -- ## Step 3: the Cauchy–Schwarz assembly
  have hV := Work.Spaces.HPRZ.L2Mem_L2Sq_finset_sum_le (Finset.range (i + 1))
    (zsFbQ f g i) (zsAAQ α f g Cf Cg i) hpiece hslice_aesm houter_aesm
  -- ## Step 4: the squared `L²`-norm of each piece
  have hpiecebd : ∀ b ∈ Finset.range (i + 1),
      (zsAAQ α f g Cf Cg i b) ^ 2 * L2Sq (zsFbQ f g i b)
        ≤ (i.choose b : ℝ) ^ 2
          * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have haa : (zsAAQ α f g Cf Cg i b) ^ 2
        = (i.choose b : ℝ) ^ 2 * zsGamQ α f g Cf Cg b := by
      rw [zsAAQ_apply, mul_pow, sq_abs]
      congr 1
      exact Real.sq_sqrt (zsGamQ_nonneg α f g Cf Cg hγ hCf hCg b)
    have hL2 : L2Sq (zsFbQ f g i b) ≤ HkSq α 4 (zsFunQ f g b) := by
      by_cases hb2 : b ≤ 2
      · have h := L2Sq_DzIter_le_HkSq α 4 g hmg (i - b) (by omega)
        have h' : L2Sq (fun z θ => |DzIter (i - b) g z θ
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|) ≤ HkSq α 4 g := by
          rw [Work.Spaces.HPRZ.L2Sq_abs]; exact h
        rw [zsFbQ_eq f g i b hb2, zsFunQ_eq f g b hb2]
        exact h'
      · have h := L2Sq_DzIter_le_HkSq α 4 f hmf b (by omega)
        have h' : L2Sq (fun z θ => |DzIter b f z θ
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2))|) ≤ HkSq α 4 f := by
          rw [Work.Spaces.HPRZ.L2Sq_abs]; exact h
        rw [zsFbQ_eq' f g i b hb2, zsFunQ_eq' f g b hb2]
        exact h'
    have hΓHk : zsGamQ α f g Cf Cg b * HkSq α 4 (zsFunQ f g b)
        ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
      by_cases hb2 : b ≤ 2
      · rw [zsGamQ_eq α f g Cf Cg b hb2, zsFunQ_eq f g b hb2]
        have hle : Cf / (gam α - 1) ≤ (Cf + Cg) / (gam α - 1) :=
          div_le_div_of_nonneg_right (by linarith) hγ.le
        calc Cf / (gam α - 1) * HkSq α 4 f * HkSq α 4 g
            ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hle (HkSq_nonneg α 4 f))
                (HkSq_nonneg α 4 g)
          _ = (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := rfl
      · rw [zsGamQ_eq' α f g Cf Cg b hb2, zsFunQ_eq' f g b hb2]
        have hle : Cg / (gam α - 1) ≤ (Cf + Cg) / (gam α - 1) :=
          div_le_div_of_nonneg_right (by linarith) hγ.le
        calc Cg / (gam α - 1) * HkSq α 4 g * HkSq α 4 f
            ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 g * HkSq α 4 f :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hle (HkSq_nonneg α 4 g))
                (HkSq_nonneg α 4 f)
          _ = (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring
    calc (zsAAQ α f g Cf Cg i b) ^ 2 * L2Sq (zsFbQ f g i b)
        ≤ ((i.choose b : ℝ) ^ 2 * zsGamQ α f g Cf Cg b) * HkSq α 4 (zsFunQ f g b) := by
          rw [haa]
          exact mul_le_mul_of_nonneg_left hL2
            (mul_nonneg (sq_nonneg _) (zsGamQ_nonneg α f g Cf Cg hγ hCf hCg b))
      _ = (i.choose b : ℝ) ^ 2
            * (zsGamQ α f g Cf Cg b * HkSq α 4 (zsFunQ f g b)) := by ring
      _ ≤ (i.choose b : ℝ) ^ 2
            * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) :=
          mul_le_mul_of_nonneg_left hΓHk (sq_nonneg _)
  have hsum : (∑ b ∈ Finset.range (i + 1),
        (zsAAQ α f g Cf Cg i b) ^ 2 * L2Sq (zsFbQ f g i b))
      ≤ (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
        * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) := by
    calc (∑ b ∈ Finset.range (i + 1),
          (zsAAQ α f g Cf Cg i b) ^ 2 * L2Sq (zsFbQ f g i b))
        ≤ ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2
            * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) :=
          Finset.sum_le_sum hpiecebd
      _ = (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
            * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) :=
          (Finset.sum_mul ..).symm
  -- ## Step 5: the numerical coefficient
  have hcoef : ((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
      ≤ 10 ^ 12 := by
    have h := Work.Spaces.HPRZ.zs_coeff_bound i hi
    linarith [h]
  have hMnn : 0 ≤ (Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g :=
    mul_nonneg (mul_nonneg (div_nonneg (by linarith) hγ.le) (HkSq_nonneg α 4 f))
      (HkSq_nonneg α 4 g)
  refine ⟨?_, ?_⟩
  · show L2Mem (fun z θ => ∑ b ∈ Finset.range (i + 1),
      zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ)
    exact hV.1
  · show L2Sq (fun z θ => ∑ b ∈ Finset.range (i + 1),
        zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ)
      ≤ 10 ^ 12 / (gam α - 1) * (Cf + Cg) * HkSq α 4 f * HkSq α 4 g
    calc L2Sq (fun z θ => ∑ b ∈ Finset.range (i + 1),
          zsAAQ α f g Cf Cg i b * zsFbQ f g i b z θ)
        ≤ ((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1),
            (zsAAQ α f g Cf Cg i b) ^ 2 * L2Sq (zsFbQ f g i b)) := by
          simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using hV.2
      _ ≤ ((i : ℝ) + 1) * ((∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2)
            * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (((i : ℝ) + 1) * (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ) ^ 2))
            * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) := by ring
      _ ≤ 10 ^ 12 * ((Cf + Cg) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) :=
          mul_le_mul_of_nonneg_right hcoef hMnn
      _ = 10 ^ 12 / (gam α - 1) * (Cf + Cg) * HkSq α 4 f * HkSq α 4 g := by ring

end Work.FTS.H2.HQ
