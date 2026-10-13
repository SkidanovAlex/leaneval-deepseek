import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.H2.DivQ.sliceBoundEta
import Submission.Work.FTS.EllSol.DivSinOpenAux
import Submission.Work.FTS.EllSol.PkgK5.mixedSlotAll

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllSol

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- `w(z) ≠ 0` for `z > 0`. -/
private lemma w_ne_zero_of_pos {z : ℝ} (hz : 0 < z) : Work.Spaces.w z ≠ 0 := by
  rw [Work.Spaces.w]
  exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))

/-- **The comparison of the `j`-th slice group.**  For `z > 0` the `θ`-integral of the `j`-th
slice group of the quotient `Φ/sin 2θ` is integrable and bounded by a universal multiple of the
`θ`-integral of the `j`-th slice group of `∂_θΦ`. -/
theorem groupCmpK (k : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (Φ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen Φ →
    (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) (Set.Ioo 0 (Real.pi / 2))) →
    (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
    (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → Filter.Tendsto
      (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
    Work.Spaces.HkMem α k (Work.Spaces.pth Φ) →
    ∀ z : ℝ, 0 < z → z ∈ Work.Spaces.Iz → ∀ j : ℕ, j ≤ k →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.sliceGroup α k j
          (fun z' θ' => Φ z' θ' / Real.sin (2 * θ')) z θ) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j
            (fun z' θ' => Φ z' θ' / Real.sin (2 * θ')) z θ)
          ≤ K * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j
              (Work.Spaces.pth Φ) z θ) := by
  obtain ⟨Cη, hCηpos, hetab⟩ := Work.FTS.H2.DivQ.sliceBoundEta
  obtain ⟨Cm, hCmpos, hmixb⟩ := mixedSlotBoundGenK k
  refine ⟨Cη + Cm * (k : ℝ), ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg hCηpos (mul_nonneg hCmpos.le (Nat.cast_nonneg k))
  · intro α Φ hα hα1 hSO hsl ht0 ht1 hmem z hzpos hz j hj
    have hwz : Work.Spaces.w z ≠ 0 := w_ne_zero_of_pos hzpos
    have hwz2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    obtain ⟨hsmj, ht0j, ht1j, hDenηj, hDenγj⟩ := sliceData hSO hsl ht0 ht1 hmem hα hz hzpos j hj
    set U : ℝ → ℝ → ℝ := fun z' θ' => Φ z' θ' / Real.sin (2 * θ') with hUdef
    -- ## the pure summand
    have hPint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter j U z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ := by
      obtain ⟨hI, -⟩ := hetab (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) hsmj ht0j ht1j hDenηj
      refine (hI.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
      filter_upwards [ae_Iθ_of_forall_Ioo (fun θ hθ => Pslot_eq j Φ hθ)] with θ hθ
      exact hθ.symm
    have hPbnd : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j U z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ Cη * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      obtain ⟨-, hB⟩ := hetab (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) hsmj ht0j ht1j hDenηj
      have hae : (fun θ : ℝ => (Work.Spaces.DzIter j U z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.DzIter j Φ z θ / Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
        filter_upwards [ae_Iθ_of_forall_Ioo (fun θ hθ => Pslot_eq j Φ hθ)] with θ hθ
        exact hθ
      have hze : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
            ((deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
        filter_upwards [ae_Iθ_of_forall_Ioo
          (fun θ hθ => Zdata_eq j Φ hSO hzpos hθ hwz)] with θ hθ
        rw [hθ]
        field_simp
      rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]
      calc (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter j Φ z θ / Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ (Work.Spaces.w z) ^ 2 * (Cη * (∫ θ in Work.Spaces.Iθ,
              (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) :=
            mul_le_mul_of_nonneg_left hB hwz2
        _ = Cη * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by ring
        _ = Cη * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
              ((deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
            rw [MeasureTheory.integral_const_mul]
        _ = Cη * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
            rw [MeasureTheory.integral_congr_ae hze]
    -- ## the mixed summands
    have hMint : ∀ i ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2)
        Work.Spaces.Iθ := by
      intro i hi
      obtain ⟨hi1, hikj⟩ := Finset.mem_Icc.mp hi
      have hik : i ≤ k := by omega
      obtain ⟨hI, -⟩ := hmixb α (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) hα hα1 hsmj ht0j ht1j
        hDenηj i hi1 hik (fun m hm1 hmi => hDenγj m hm1 (by omega))
      refine (hI.const_mul ((Work.Spaces.w z) ^ 2)).congr ?_
      filter_upwards [ae_Iθ_of_forall_Ioo (fun θ hθ => Mslot_eq α hα i j Φ hSO hzpos hθ)]
        with θ hθ
      exact hθ.symm
    have hMbnd : ∀ i ∈ Finset.Icc 1 (k - j),
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2)
          ≤ Cm * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
      intro i hi
      obtain ⟨hi1, hikj⟩ := Finset.mem_Icc.mp hi
      have hik : i ≤ k := by omega
      obtain ⟨-, hB⟩ := hmixb α (fun θ : ℝ => Work.Spaces.DzIter j Φ z θ) hα hα1 hsmj ht0j ht1j
        hDenηj i hi1 hik (fun m hm1 hmi => hDenγj m hm1 (by omega))
      have hae : (fun θ : ℝ => (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2)
          =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
          (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
            ((Work.Elliptic.Dth1Iter i
                (fun θ' => Work.Spaces.DzIter j Φ z θ' / Real.sin (2 * θ')) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
        filter_upwards [ae_Iθ_of_forall_Ioo (fun θ hθ => Mslot_eq α hα i j Φ hSO hzpos hθ)]
          with θ hθ
        exact hθ
      have hZ : (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          = ((Work.Spaces.w z) ^ 2)⁻¹ * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [ae_Iθ_of_forall_Ioo
          (fun θ hθ => Zdata_eq j Φ hSO hzpos hθ hwz)] with θ hθ
        exact hθ
      have hM : ∀ m ∈ Finset.Icc 1 i,
          (∫ θ in Work.Spaces.Iθ, (Work.Elliptic.Dth1Iter m (fun θ' : ℝ =>
              deriv (fun θ'' : ℝ => Work.Spaces.DzIter j Φ z θ'') θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            = ((Work.Spaces.w z) ^ 2)⁻¹ * (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2) := by
        intro m hm
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards [ae_Iθ_of_forall_Ioo
          (fun θ hθ => Mdata_eq α hα m j Φ hSO hzpos hθ hwz)] with θ hθ
        exact hθ
      have hsum : (∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter m (fun θ' : ℝ => deriv (fun θ'' : ℝ =>
              Work.Spaces.DzIter j Φ z θ'') θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
          = ((Work.Spaces.w z) ^ 2)⁻¹ * ∑ m ∈ Finset.Icc 1 i,
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
              * Work.Spaces.Wt α z θ) ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun m hm => hM m hm)
      have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwz
      rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul]
      refine le_trans (mul_le_mul_of_nonneg_left hB hwz2) ?_
      have hgoal : (Work.Spaces.w z) ^ 2 * (Cm *
            ((∫ θ in Work.Spaces.Iθ, (deriv (fun θ' : ℝ => Work.Spaces.DzIter j Φ z θ') θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter m (fun θ' : ℝ => deriv (fun θ'' : ℝ =>
                    Work.Spaces.DzIter j Φ z θ'') θ') θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))))
          = Cm * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                    * Work.Spaces.Wt α z θ) ^ 2)) := by
        rw [hZ, hsum]
        refine mul_left_cancel₀ (ne_of_gt hCmpos) ?_
        field_simp
      exact hgoal.le
    -- ## the slice group comparison
    -- ## the slice group comparison
    have hZint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Work.Spaces.DzIter j
        (Work.Spaces.pth Φ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.integrableOn_zSummand α k hSO.pth hmem j hj hz
    have hMintR : ∀ i ∈ Finset.Icc 1 (k - j), MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ
          * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ := by
      intro i hi
      obtain ⟨hi1, hikj⟩ := Finset.mem_Icc.mp hi
      exact Work.FTS.EllipticEst.integrableOn_mixedSummand α k hSO.pth hmem i j hi1
        (by omega) hz
    have hvalL : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sliceGroup α k j U z θ)
        = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j U z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m U z θ * Work.Spaces.Wt α z θ) ^ 2) := by
      have hsg : (fun θ : ℝ => Work.FTS.EllipticEst.sliceGroup α k j U z θ)
          = fun θ : ℝ => (Work.Spaces.DzIter j U z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + ∑ i ∈ Finset.Icc 1 (k - j),
                  (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        funext θ
        simp only [Work.FTS.EllipticEst.sliceGroup]
      rw [hsg, MeasureTheory.integral_add hPint (MeasureTheory.integrable_finsetSum _ hMint),
        MeasureTheory.integral_finsetSum _ hMint]
    have hvalR : (∫ θ in Work.Spaces.Iθ,
          Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth Φ) z θ)
        = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2) := by
      have hsg : (fun θ : ℝ => Work.FTS.EllipticEst.sliceGroup α k j
            (Work.Spaces.pth Φ) z θ)
          = fun θ : ℝ => (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + ∑ i ∈ Finset.Icc 1 (k - j),
                  (Work.Spaces.mixed j i (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        funext θ
        simp only [Work.FTS.EllipticEst.sliceGroup]
      rw [hsg, MeasureTheory.integral_add hZint (MeasureTheory.integrable_finsetSum _ hMintR),
        MeasureTheory.integral_finsetSum _ hMintR]
    have h2 : (∑ i ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2))
        ≤ Cm * (k : ℝ) * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
      have hZnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
        MeasureTheory.integral_nonneg fun θ => sq_nonneg _
      have hMnn : ∀ m ∈ Finset.Icc 1 (k - j), 0 ≤ (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2) :=
        fun m _ => MeasureTheory.integral_nonneg fun θ => sq_nonneg _
      have hinner : ∀ i ∈ Finset.Icc 1 (k - j),
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2)
            ≤ Cm * ((∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                    * Work.Spaces.Wt α z θ) ^ 2)) := by
        intro i hi
        have h3 := hMbnd i hi
        have hsub : Finset.Icc 1 i ⊆ Finset.Icc 1 (k - j) := fun m hm => by
          obtain ⟨hm1, hmi⟩ := Finset.mem_Icc.mp hm
          exact Finset.mem_Icc.mpr ⟨hm1, by have := (Finset.mem_Icc.mp hi).2; omega⟩
        have h4 : (∑ m ∈ Finset.Icc 1 i, (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2))
            ≤ ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => hMnn m ‹_›)
        exact h3.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl h4) hCmpos.le)
      calc (∑ i ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i U z θ * Work.Spaces.Wt α z θ) ^ 2))
          ≤ ∑ _i ∈ Finset.Icc 1 (k - j), Cm * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                    * Work.Spaces.Wt α z θ) ^ 2)) := Finset.sum_le_sum hinner
        _ = ((Finset.Icc 1 (k - j)).card : ℝ) * (Cm * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                    * Work.Spaces.Wt α z θ) ^ 2))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Cm * (k : ℝ) * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                    * Work.Spaces.Wt α z θ) ^ 2)) := by
            have hXnn : 0 ≤ (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
                + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                    (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                      * Work.Spaces.Wt α z θ) ^ 2) := add_nonneg hZnn (Finset.sum_nonneg hMnn)
            have hcard : ((Finset.Icc 1 (k - j)).card : ℝ) ≤ (k : ℝ) := by
              have h1 : (Finset.Icc 1 (k - j)).card ≤ k := by
                rw [Nat.card_Icc]
                omega
              exact_mod_cast h1
            have hstep : ((Finset.Icc 1 (k - j)).card : ℝ) * Cm ≤ Cm * (k : ℝ) := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left hcard hCmpos.le
            nlinarith [hstep, hXnn]
    refine ⟨hPint.add (MeasureTheory.integrable_finsetSum _ hMint), ?_⟩
    rw [hvalL, hvalR]
    have hZnn : 0 ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
      MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    have hMnn : 0 ≤ ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2) :=
      Finset.sum_nonneg fun m _ => MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    have hK' : Cη * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + Cm * (k : ℝ) * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2))
        ≤ (Cη + Cm * (k : ℝ)) * ((∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
      nlinarith [hZnn, hMnn, hCηpos, hCmpos, Nat.cast_nonneg (α := ℝ) k]
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j U z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m U z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ Cη * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + Cm * (k : ℝ) * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2)) := add_le_add hPbnd h2
      _ ≤ (Cη + Cm * (k : ℝ)) * ((∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter j (Work.Spaces.pth Φ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + ∑ m ∈ Finset.Icc 1 (k - j), (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed j m (Work.Spaces.pth Φ) z θ * Work.Spaces.Wt α z θ) ^ 2)) := hK'
end Work.FTS.EllSol.PkgK5
