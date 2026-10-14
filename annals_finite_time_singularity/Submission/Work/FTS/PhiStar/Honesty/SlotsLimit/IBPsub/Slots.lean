import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.Spaces.HProductRule_Badsummand
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Decay.hasDerivAt_biotSavart
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.thMollSliceL2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Work.FTS.EllSol.PkgK5.K5c

local notation "Iθ" => Work.Spaces.Iθ
local notation "σθ" => Work.FTS.EllipticEst.thEta

/-! ## Small auxiliary lemmas about set integrals

Three tools used by the fold of the doubly odd extension:

* set integrals over a.e.-equal sets agree (`tsl_setIntegral_congr_set_ae`);
* the reflections `x ↦ -x` and `x ↦ π - x` preserve Lebesgue measure, so they transport
  set integrals (`tsl_setIntegral_image_neg`, `tsl_setIntegral_image_pi_sub`);
* a bounded continuous factor preserves integrability on `Iθ` (`tsl_integrableOn_mul_continuous`).
-/

theorem tsl_setIntegral_congr_set_ae {f : ℝ → ℝ} {s t : Set ℝ} (h : s =ᵐ[volume] t) :
    ∫ x in s, f x = ∫ x in t, f x := by
  rw [MeasureTheory.Measure.restrict_congr_set h]

theorem tsl_setIntegral_image_neg (f : ℝ → ℝ) (s : Set ℝ) :
    ∫ x in (Neg.neg '' s), f x = ∫ x in s, f (-x) :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_image_emb
    (Homeomorph.neg ℝ).measurableEmbedding f s

/-- The reflection `t ↦ π - t` of the real line. -/
def tslPiSubHomeo : ℝ ≃ₜ ℝ where
  toFun := fun t => Real.pi - t
  invFun := fun t => Real.pi - t
  left_inv := fun t => by ring
  right_inv := fun t => by ring
  continuous_toFun := continuous_const.sub continuous_id
  continuous_invFun := continuous_const.sub continuous_id

theorem tsl_setIntegral_image_pi_sub (f : ℝ → ℝ) (s : Set ℝ) :
    ∫ x in (fun t : ℝ => Real.pi - t) '' s, f x = ∫ x in s, f (Real.pi - x) :=
  (Measure.measurePreserving_sub_left (volume : Measure ℝ) Real.pi).setIntegral_image_emb
    tslPiSubHomeo.measurableEmbedding f s

theorem tsl_integrableOn_mul_continuous {g : ℝ → ℝ} (hg : IntegrableOn g Iθ) {c : ℝ → ℝ}
    (hc : Continuous c) : IntegrableOn (fun t => c t * g t) Iθ :=
  (IntegrableOn.mul_continuousOn hg hc.continuousOn isCompact_Icc).congr_fun
    (fun t _ => mul_comm (g t) (c t)) measurableSet_Icc

/-! ## The fold of the doubly odd extension

For `0 < ε ≤ 1/2` and `θ ∈ Iθ`, the angular mollification `thMoll u ε z θ`
(`= ∫_ℝ sKer ε (θ - s) · Qext u z s ds`) is dominated by the integral over `Iθ` against the
three-image kernel `KJ` of the *modulus* of the datum:

  `|thMoll u ε z θ| ≤ ∫_{Iθ} KJ ε θ s · |u z s| ds`.

Indeed `|thMoll| ≤ ∫_ℝ sKer ε (θ - s) · |Qext u z s| ds`, and the reflections `s ↦ -s` (about
`0`) and `s ↦ π - s` (about `π/2`), together with the oddness of `Qext`
(`Qext_neg_of_pos`, `Qext_pihalf_odd`), turn the three pieces `(-π/2, 0)`, `(0, π/2)`,
`(π/2, π)` of that integral into the three terms of the kernel `KJ` evaluated on `Iθ`. -/
theorem thMoll_abs_le (u : ℝ → ℝ → ℝ) {ε z θ : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hu : IntegrableOn (fun s : ℝ => u z s) Iθ) (hθ : θ ∈ Iθ) :
    |thMoll u ε z θ| ≤ ∫ s in Iθ, KJ ε θ s * |u z s| := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ2 : θ ≤ Real.pi / 2 := hθ.2
  have hεpi : ε ≤ Real.pi / 2 := by linarith [hε2, Real.pi_gt_three]
  -- the three pieces of the folded kernel
  set K1 : ℝ → ℝ := fun t => sKer ε (θ - t) * |u z t| with hK1def
  set K2 : ℝ → ℝ := fun t => sKer ε (θ + t) * |u z t| with hK2def
  set K3 : ℝ → ℝ := fun t => sKer ε (θ + t - Real.pi) * |u z t| with hK3def
  set F : ℝ → ℝ := fun s => sKer ε (θ - s) * |Qext u z s| with hFdef
  -- ## Step 1: the crude bound by the integral of the modulus
  have hbase : |thMoll u ε z θ| ≤ ∫ s : ℝ, F s := by
    have h1 := MeasureTheory.norm_integral_le_integral_norm (μ := volume)
      (f := fun s : ℝ => sKer ε (θ - s) * Qext u z s)
    rw [Real.norm_eq_abs] at h1
    have h2 : (∫ s : ℝ, ‖sKer ε (θ - s) * Qext u z s‖) = ∫ s : ℝ, F s := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      show ‖sKer ε (θ - s) * Qext u z s‖ = F s
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sKer_nonneg hε (θ - s)), hFdef]
    rw [h2] at h1
    have h3 : thMoll u ε z θ = ∫ s : ℝ, sKer ε (θ - s) * Qext u z s := rfl
    rw [h3]
    exact h1
  -- ## Step 2: the pointwise evaluations of `Qext`
  have hQmid : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Qext u z t = u z t :=
    fun t ht => Qext_of_mem u z t ⟨ht.1.le, ht.2.le⟩
  have hQneg : ∀ t ∈ Set.Ioi (0 : ℝ), Qext u z (-t) = -u z t :=
    fun t ht => Qext_neg_of_pos u z t ht
  have hQpi : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Qext u z (Real.pi - t) = -u z t := by
    intro t ht
    have hs1 : 0 < Real.pi / 2 - t := by linarith [ht.2]
    have hs2 : Real.pi / 2 - t ≤ Real.pi / 2 := by linarith [ht.1]
    have hodd := Qext_pihalf_odd u z (Real.pi / 2 - t) hs1 hs2
    have e1 : Real.pi / 2 - (Real.pi / 2 - t) = t := by ring
    have e2 : Real.pi / 2 + (Real.pi / 2 - t) = Real.pi - t := by ring
    rw [e1, e2] at hodd
    have hQt : Qext u z t = u z t := Qext_of_mem u z t ⟨ht.1.le, ht.2.le⟩
    rw [hQt] at hodd
    linarith [hodd]
  -- ## Step 3: pointwise identifications of `F` with `K1`, `K2`, `K3`
  have hFmidI : EqOn K1 F Iθ := by
    intro t ht
    simp only [hK1def, hFdef]
    rw [Qext_of_mem u z t ht]
  have hFneg : EqOn K2 (F ∘ Neg.neg) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    simp only [hK2def, Function.comp_apply, hFdef]
    rw [show θ - -t = θ + t from by ring, hQneg t ht, abs_neg]
  have hFright : EqOn K3 (F ∘ fun t : ℝ => Real.pi - t) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro t ht
    simp only [hK3def, Function.comp_apply, hFdef]
    rw [show θ - (Real.pi - t) = θ + t - Real.pi from by ring, hQpi t ht, abs_neg]
  -- ## Step 4: vanishing of `K2`, `K3` and `F ∘ (π - ·)` on the outer pieces
  have hK2zero : ∀ x ∈ Set.Ici (Real.pi / 2), K2 x = 0 := by
    intro x hx
    have hx' : Real.pi / 2 ≤ x := hx
    have h1 : (0 : ℝ) ≤ θ + x := by linarith [hθ0, hx']
    have h2 : ε ≤ |θ + x| := by rw [abs_of_nonneg h1]; linarith [hθ0, hx', hεpi]
    simp only [hK2def]
    rw [sKer_eq_zero_of_le_abs hε h2, zero_mul]
  have hK3zero : ∀ x ∈ Set.Iic (0 : ℝ), K3 x = 0 := by
    intro x hx
    have hx' : x ≤ 0 := hx
    have h1 : θ + x - Real.pi ≤ 0 := by linarith [hθ2, hx']
    have h2 : ε ≤ |θ + x - Real.pi| := by rw [abs_of_nonpos h1]; linarith [hθ2, hx', hεpi]
    simp only [hK3def]
    rw [sKer_eq_zero_of_le_abs hε h2, zero_mul]
  have hFczero : ∀ x ∈ Set.Iic (0 : ℝ), (F ∘ fun t : ℝ => Real.pi - t) x = 0 := by
    intro x hx
    have hx' : x ≤ 0 := hx
    have h1 : θ + x - Real.pi ≤ 0 := by linarith [hθ2, hx']
    have h2 : ε ≤ |θ + x - Real.pi| := by rw [abs_of_nonpos h1]; linarith [hθ2, hx', hεpi]
    simp only [Function.comp_apply, hFdef]
    rw [show θ - (Real.pi - x) = θ + x - Real.pi from by ring,
      sKer_eq_zero_of_le_abs hε h2, zero_mul]
  -- ## Step 5: integrability of the pieces
  have huabs : IntegrableOn (fun s : ℝ => |u z s|) Iθ :=
    (show Integrable (fun s : ℝ => u z s) (volume.restrict Iθ) from hu).abs
  have hcont1 : Continuous (fun t : ℝ => sKer ε (θ - t)) :=
    (Work.FTS.EllSol.K5cAux.continuous_sKer ε).comp (continuous_const.sub continuous_id)
  have hcont2 : Continuous (fun t : ℝ => sKer ε (θ + t)) :=
    (Work.FTS.EllSol.K5cAux.continuous_sKer ε).comp (continuous_const.add continuous_id)
  have hcont3 : Continuous (fun t : ℝ => sKer ε (θ + t - Real.pi)) :=
    (Work.FTS.EllSol.K5cAux.continuous_sKer ε).comp
      ((continuous_const.add continuous_id).sub continuous_const)
  have hK1I : IntegrableOn K1 Iθ := by
    rw [hK1def]
    exact tsl_integrableOn_mul_continuous huabs hcont1
  have hK2I : IntegrableOn K2 Iθ := by
    rw [hK2def]
    exact tsl_integrableOn_mul_continuous huabs hcont2
  have hK3I : IntegrableOn K3 Iθ := by
    rw [hK3def]
    exact tsl_integrableOn_mul_continuous huabs hcont3
  have hK2Ioo : IntegrableOn K2 (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hK2I.mono_set Set.Ioo_subset_Icc_self
  have hK3Ioo : IntegrableOn K3 (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hK3I.mono_set Set.Ioo_subset_Icc_self
  have hK2ci : IntegrableOn K2 (Set.Ici (Real.pi / 2)) :=
    (MeasureTheory.integrableOn_zero (μ := (volume : Measure ℝ))
        (s := Set.Ici (Real.pi / 2)) :
        IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ici (Real.pi / 2)) volume).congr_fun
      (fun x hx => (hK2zero x hx).symm) measurableSet_Ici
  have hK3ic : IntegrableOn K3 (Set.Iic (0 : ℝ)) :=
    (MeasureTheory.integrableOn_zero (μ := (volume : Measure ℝ))
        (s := Set.Iic (0 : ℝ)) :
        IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Iic (0 : ℝ)) volume).congr_fun
      (fun x hx => (hK3zero x hx).symm) measurableSet_Iic
  have hcov1 : Set.Ioo (0 : ℝ) (Real.pi / 2) ∪ Set.Ici (Real.pi / 2) = Set.Ioi (0 : ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact lt_of_lt_of_le (by linarith [Real.pi_pos]) h
    · intro hx
      rcases lt_or_ge x (Real.pi / 2) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
  have hcov2 : Set.Iic (0 : ℝ) ∪ Set.Ioo (0 : ℝ) (Real.pi / 2) = Set.Iio (Real.pi / 2) := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioo, Set.mem_Iio]
    constructor
    · rintro (h | h)
      · linarith
      · exact h.2
    · intro hx
      by_cases h : x ≤ 0
      · exact Or.inl h
      · push_neg at h
        exact Or.inr ⟨h, hx⟩
  have hK2Ioi : IntegrableOn K2 (Set.Ioi (0 : ℝ)) := by
    rw [← hcov1]
    exact hK2Ioo.union hK2ci
  have hK3Iiohalf : IntegrableOn K3 (Set.Iio (Real.pi / 2)) := by
    rw [← hcov2]
    exact hK3ic.union hK3Ioo
  have hFnegint : IntegrableOn (F ∘ Neg.neg) (Set.Ioi (0 : ℝ)) :=
    hK2Ioi.congr_fun hFneg measurableSet_Ioi
  have hFcIic : IntegrableOn (F ∘ fun t : ℝ => Real.pi - t) (Set.Iic (0 : ℝ)) :=
    (MeasureTheory.integrableOn_zero (μ := (volume : Measure ℝ)) (s := Set.Iic (0 : ℝ)) :
        IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Iic (0 : ℝ)) volume).congr_fun
      (fun x hx => (hFczero x hx).symm) measurableSet_Iic
  have hFcIoo : IntegrableOn (F ∘ fun t : ℝ => Real.pi - t)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hK3Ioo.congr_fun hFright measurableSet_Ioo
  have hFcIiohalf : IntegrableOn (F ∘ fun t : ℝ => Real.pi - t) (Set.Iio (Real.pi / 2)) := by
    rw [← hcov2]
    exact hFcIic.union hFcIoo
  have hnegIoi : Neg.neg '' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by
    ext x
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · rintro ⟨t, ht, rfl⟩
      linarith
    · intro hx
      exact ⟨-x, by linarith, by ring⟩
  have hpiIio : (fun t : ℝ => Real.pi - t) '' Set.Iio (Real.pi / 2) = Set.Ioi (Real.pi / 2) := by
    ext x
    simp only [Set.mem_image, Set.mem_Iio, Set.mem_Ioi]
    constructor
    · rintro ⟨t, ht, rfl⟩
      linarith
    · intro hx
      exact ⟨Real.pi - x, by linarith, by ring⟩
  have hF_A : IntegrableOn F (Set.Iio (0 : ℝ)) := by
    rw [← hnegIoi]
    exact ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_image
      (Homeomorph.neg ℝ).measurableEmbedding (f := F) (s := Set.Ioi (0 : ℝ))).mpr hFnegint
  have hF_B : IntegrableOn F Iθ :=
    hK1I.congr_fun hFmidI measurableSet_Icc
  have hF_C : IntegrableOn F (Set.Ioi (Real.pi / 2)) := by
    rw [← hpiIio]
    exact ((Measure.measurePreserving_sub_left (volume : Measure ℝ) Real.pi).integrableOn_image
      tslPiSubHomeo.measurableEmbedding (f := F) (s := Set.Iio (Real.pi / 2))).mpr hFcIiohalf
  -- ## Step 6: the pairwise disjoint cover of `ℝ` and the splitting of `∫_ℝ F`
  have hdisjAB : Disjoint (Set.Iio (0 : ℝ)) Iθ := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : x < 0 := hx1
    have h2 : (0 : ℝ) ≤ x := hx2.1
    linarith
  have hdisjABC : Disjoint (Set.Iio (0 : ℝ) ∪ Iθ) (Set.Ioi (Real.pi / 2)) := by
    rw [Set.disjoint_left]
    intro x hx hx3
    have h3 : Real.pi / 2 < x := hx3
    rcases hx with hx | hx
    · have h1 : x < 0 := hx
      linarith
    · have h2 : x ≤ Real.pi / 2 := hx.2
      linarith
  have hcover : Set.Iio (0 : ℝ) ∪ Iθ ∪ Set.Ioi (Real.pi / 2) = (Set.univ : Set ℝ) := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      rcases lt_or_ge x 0 with h | h
      · exact Or.inl (Or.inl h)
      · by_cases h2 : x ≤ Real.pi / 2
        · exact Or.inl (Or.inr ⟨h, h2⟩)
        · exact Or.inr (lt_of_not_ge h2)
  have hAB : (∫ s in Set.Iio (0 : ℝ) ∪ Iθ, F s)
      = (∫ s in Set.Iio (0 : ℝ), F s) + ∫ s in Iθ, F s :=
    MeasureTheory.setIntegral_union hdisjAB measurableSet_Icc hF_A hF_B
  have hABC : (∫ s in Set.Iio (0 : ℝ) ∪ Iθ ∪ Set.Ioi (Real.pi / 2), F s)
      = (∫ s in Set.Iio (0 : ℝ) ∪ Iθ, F s) + ∫ s in Set.Ioi (Real.pi / 2), F s :=
    MeasureTheory.setIntegral_union hdisjABC measurableSet_Ioi (hF_A.union hF_B) hF_C
  have hsplit : (∫ s : ℝ, F s)
      = (∫ s in Set.Iio (0 : ℝ), F s) + (∫ s in Iθ, F s)
        + ∫ s in Set.Ioi (Real.pi / 2), F s := by
    rw [← MeasureTheory.setIntegral_univ, ← hcover, hABC, hAB]
  -- ## Step 7: the three pieces, transported to integrals over `Iθ`
  have hpiece2 : (∫ s in Iθ, F s) = ∫ t in Iθ, K1 t := by
    refine MeasureTheory.integral_congr_ae ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => (hFmidI ht).symm)
  have hpiece1 : (∫ s in Set.Iio (0 : ℝ), F s) = ∫ t in Iθ, K2 t := by
    have e1 : (∫ x in Set.Ioi (0 : ℝ), F (-x)) = ∫ x in Set.Ioi (0 : ℝ), K2 x := by
      refine MeasureTheory.integral_congr_ae ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun x hx => (hFneg hx).symm)
    have e2 : (∫ x in Set.Ioi (0 : ℝ), K2 x)
        = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), K2 x :=
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (f := K2)
        measurableSet_Ioi (fun x hx => hx.1) (fun x hx => hK2zero x (by
          have hx1 : (0 : ℝ) < x := hx.1
          have hx2 : ¬ (x < Real.pi / 2) := fun hlt => hx.2 ⟨hx1, hlt⟩
          exact le_of_not_gt hx2))
    have e3 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), K2 x) = ∫ x in Iθ, K2 x :=
      tsl_setIntegral_congr_set_ae (f := K2) (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (t := Iθ)
        MeasureTheory.Ioo_ae_eq_Icc
    calc (∫ s in Set.Iio (0 : ℝ), F s)
        = ∫ s in Neg.neg '' Set.Ioi (0 : ℝ), F s := by rw [hnegIoi]
      _ = ∫ x in Set.Ioi (0 : ℝ), F (-x) := tsl_setIntegral_image_neg F (Set.Ioi (0 : ℝ))
      _ = ∫ x in Set.Ioi (0 : ℝ), K2 x := e1
      _ = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), K2 x := e2
      _ = ∫ x in Iθ, K2 x := e3
  have hpiece3 : (∫ s in Set.Ioi (Real.pi / 2), F s) = ∫ t in Iθ, K3 t := by
    have e4 : (∫ x in Set.Iio (Real.pi / 2), F (Real.pi - x))
        = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), F (Real.pi - x) :=
      MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (f := fun x => F (Real.pi - x)) measurableSet_Iio
        (fun x hx => hx.2) (fun x hx => hFczero x (by
          have hx1 : x < Real.pi / 2 := hx.1
          have hx2 : ¬ (0 < x) := fun hlt => hx.2 ⟨hlt, hx1⟩
          exact le_of_not_gt hx2))
    have e5 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), F (Real.pi - x))
        = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), K3 x := by
      refine MeasureTheory.integral_congr_ae ?_
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun x hx => (hFright hx).symm)
    have e6 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), K3 x) = ∫ x in Iθ, K3 x :=
      tsl_setIntegral_congr_set_ae (f := K3) (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (t := Iθ)
        MeasureTheory.Ioo_ae_eq_Icc
    calc (∫ s in Set.Ioi (Real.pi / 2), F s)
        = ∫ s in (fun t : ℝ => Real.pi - t) '' Set.Iio (Real.pi / 2), F s := by rw [hpiIio]
      _ = ∫ x in Set.Iio (Real.pi / 2), F (Real.pi - x) :=
            tsl_setIntegral_image_pi_sub F (Set.Iio (Real.pi / 2))
      _ = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), F (Real.pi - x) := e4
      _ = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), K3 x := e5
      _ = ∫ x in Iθ, K3 x := e6
  -- ## Step 8: reassembling
  have hadd : (∫ t in Iθ, K1 t + K2 t + K3 t)
      = (∫ t in Iθ, K1 t) + (∫ t in Iθ, K2 t) + ∫ t in Iθ, K3 t := by
    have h1 : (∫ t in Iθ, K1 t + K2 t) = (∫ t in Iθ, K1 t) + ∫ t in Iθ, K2 t :=
      MeasureTheory.integral_add hK1I hK2I
    have h2 : (∫ t in Iθ, (K1 t + K2 t) + K3 t)
        = (∫ t in Iθ, K1 t + K2 t) + ∫ t in Iθ, K3 t :=
      MeasureTheory.integral_add (hK1I.add hK2I) hK3I
    rw [h2, h1]
  have hsum : (∫ t in Iθ, K1 t + K2 t + K3 t) = ∫ t in Iθ, KJ ε θ t * |u z t| := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hK1def, hK2def, hK3def, KJ]
    ring
  have heq : (∫ s : ℝ, F s) = ∫ t in Iθ, KJ ε θ t * |u z t| := by
    calc (∫ s : ℝ, F s)
        = (∫ s in Set.Iio (0 : ℝ), F s) + (∫ s in Iθ, F s)
            + ∫ s in Set.Ioi (Real.pi / 2), F s := hsplit
      _ = (∫ t in Iθ, K1 t) + (∫ t in Iθ, K2 t) + ∫ t in Iθ, K3 t := by
            rw [hpiece1, hpiece2, hpiece3]
            ring
      _ = ∫ t in Iθ, K1 t + K2 t + K3 t := hadd.symm
      _ = ∫ t in Iθ, KJ ε θ t * |u z t| := hsum
  exact hbase.trans (le_of_eq heq)


end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Prop.l0_second_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000
/-- **The quadratic solve.**  From `0 ≤ K`, `0 ≤ N` and `X ^ 2 ≤ K * (N ^ 2 + N * X)` one gets
`X ≤ (K + 1) * N`. -/
private theorem quad_solve' {K X N : ℝ} (hK : 0 ≤ K) (hN : 0 ≤ N)
    (h : X ^ 2 ≤ K * (N ^ 2 + N * X)) : X ≤ (K + 1) * N := by
  by_contra hc
  rw [not_le] at hc
  have hXpos : 0 < X := by
    have : 0 ≤ (K + 1) * N := by positivity
    linarith
  have hXN : 0 < X + N := by linarith
  have hprod : 0 < (X - (K + 1) * N) * (X + N) := mul_pos (by linarith) hXN
  have hid : (X - (K + 1) * N) * (X + N) = X ^ 2 - K * (N * X) - K * N ^ 2 - N ^ 2 := by ring
  nlinarith [hprod, hid, h, sq_nonneg N, hK]

/-- **The assembly of Step 2 in the weak class from the honest `I₁` lower bound.**

Assuming the `I₁` coercivity in the a.e. class *with the two first-order honesties* — i.e. exactly
the statement of `Prop.i1_bare_hh`, which the strengthened weak class `TT.EllWeakPos` supplies
through its tenth conjunct `EllWeakPos.memZPth2` — and the first-order estimate `hfirst`, the
second-order angular estimate holds.

The proof is the paper's Step 2: pair the equation with `-∂_θθΨ·w²σ`
(`AngAWeak.I_identity_weak`), bound the five pieces (`I₁` by hypothesis, `I₂`/`I₅`/the source by
Cauchy–Schwarz, `I₄` by `H2W.AeWAux.aeI4Of` applied to `H2W.AeWAux.i4SliceIneq`), and solve the
resulting quadratic inequality with the Step-1 data supplied by `hfirst`. -/
theorem l0_second_of_i1hh (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hI1 : ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) →
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) →
        - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz u z θ)
              (fun z θ => z * Work.Spaces.pz u z θ)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz u z θ)
                  (fun z θ => z * Work.Spaces.pz u z θ))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                  (Work.Spaces.pthIter 2 u)))
          ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u))
    (hfirst : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Work.Spaces.HkMem α 0 Ψ ∧
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) ∧
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
      Real.sqrt (Work.Spaces.HkSq α 0 Ψ)
        + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))
        + Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => Ψ z θ / Real.cos θ))
        ≤ C₁ * Real.sqrt (Work.Spaces.HkSq α 0 F)) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 0 F Ψ →
      Real.sqrt (Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 Ψ))
        ≤ C * (Real.sqrt (Work.Spaces.HkSq α 0 F)
            + α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ))) := by
  obtain ⟨C₂, hC₂pos, hI1'⟩ := hI1
  obtain ⟨C₃, hC₃pos, hI4'⟩ := Work.FTS.EllipticEst.H2W.AeWAux.aeI4Of
    Work.FTS.EllipticEst.H2W.AeWAux.i4SliceIneq
  refine ⟨max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hW
  -- ## the Step-1 data supplied by the first-order estimate
  obtain ⟨hmemΨ, hmemU, hmemPb, hstep1⟩ := hfirst α F Ψ hα hα4 hW
  -- ## the six honesty pairings of the Step-2 identity
  obtain ⟨hFB, hQB, hUB, hG₁B, hΨB, hBB⟩ :=
    Work.FTS.EllipticEst.TT.weakIPMems α F Ψ hα hα4 hW hmemΨ hmemU
  -- ## the almost-everywhere class
  have haeΨ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar Ψ z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun z hz => hW.orthPsi z hz
  have haeF : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar F z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun z hz => hW.orthF z hz
  have hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F :=
    ⟨hα, hα4, fun z hz θ h0 h1 => hW.eq z hz θ h0 h1, hW.zero, hW.pi_half, hW.smooth,
      hW.memF, hW.memA, hW.memB, haeΨ, haeF⟩
  -- ## abbreviations
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hB
  set Q : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hQ
  set U : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Ψ z θ with hU
  set G₁ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ with hG₁
  set PbF : ℝ → ℝ → ℝ := fun z θ => Ψ z θ / Real.cos θ with hPbF
  set f : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 F) with hf
  set b : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 U) with hb
  set X : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 B) with hX
  set Pb : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 PbF) with hPb
  set m : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 Ψ) with hm
  have hf0 : 0 ≤ f := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have hPb0 : 0 ≤ Pb := Real.sqrt_nonneg _
  -- ## `HkSq` versus the honest pairing `IP`
  have hb2 : b ^ 2 = Work.FTS.EllipticEst.AngSecond.IP U U := by
    rw [hb, hU, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hX2 : X ^ 2 = Work.FTS.EllipticEst.AngSecond.IP B B := by
    rw [hX, hB, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hPb2 : Pb ^ 2 = Work.FTS.EllipticEst.AngSecond.IP PbF PbF := by
    rw [hPb, hPbF, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hm2 : m ^ 2 = Work.FTS.EllipticEst.AngSecond.IP Ψ Ψ := by
    rw [hm, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
    exact Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α _)
  have hbX : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U) = b := by
    rw [← hb2]; exact Real.sqrt_sq hb0
  have hXX : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) = X := by
    rw [← hX2]; exact Real.sqrt_sq hX0
  have hmX : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP Ψ Ψ) = m := by
    rw [← hm2]; exact Real.sqrt_sq hm0
  have hHkPbF : Work.Spaces.HkSq α 0 PbF = Pb ^ 2 := by
    rw [hPb2, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
  have hHkB : Work.Spaces.HkSq α 0 B = X ^ 2 := by
    rw [hX2, Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq]
  have hHkF : Work.Spaces.HkSq α 0 F = f ^ 2 := by
    rw [hf, Real.sq_sqrt (Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α F)]
  -- ## the two deep inputs, in the notation of the assembly
  have hI1b : -C₂ * α ^ 2
      * (Work.FTS.EllipticEst.AngSecond.IP U U
        + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U)
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B))
      ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B :=
    hI1' α Ψ F hAe hmemU (Work.FTS.EllipticEst.TT.EllWeakPos.memZPth2 hW)
  have hI4b : Work.FTS.EllipticEst.AngSecond.IP G₁ B
      ≤ C₃ * (Work.Spaces.HkSq α 0 PbF
        + Real.sqrt (Work.Spaces.HkSq α 0 PbF) * Real.sqrt (Work.Spaces.HkSq α 0 B)) :=
    hI4' α Ψ hW.smooth hmemPb hW.memB
  -- ## the Step-2 pairing identity
  have hid : α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B
        + α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP U B
        + Work.FTS.EllipticEst.AngSecond.IP B B
        - Work.FTS.EllipticEst.AngSecond.IP G₁ B
        + 6 * Work.FTS.EllipticEst.AngSecond.IP Ψ B
      = -Work.FTS.EllipticEst.AngSecond.IP F B :=
    Work.FTS.EllipticEst.AngAWeak.I_identity_weak α F Ψ
      (fun z hz θ h0 h1 => hW.eq z hz θ h0 h1) hFB hQB hUB hG₁B hΨB hBB
  -- ## Cauchy–Schwarz for the `I₂`, `I₅` and source slots
  have hcsU : |Work.FTS.EllipticEst.AngSecond.IP U B|
      ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U)
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) :=
    Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemU)
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hW.memB) hUB
  have hcsΨ : |Work.FTS.EllipticEst.AngSecond.IP Ψ B|
      ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP Ψ Ψ)
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) :=
    Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hmemΨ)
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hW.memB) hΨB
  have hcsF : |Work.FTS.EllipticEst.AngSecond.IP F B|
      ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP F F)
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) :=
    Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hW.memF)
      (Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem hW.memB) hFB
  -- ## the bounds of the individual pieces
  have hI1b' : -C₂ * α ^ 2 * (b ^ 2 + b * X) ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B := by
    have h := hI1b
    rw [← hb2, hXX, Real.sqrt_sq hb0] at h
    exact h
  have e1 : -α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B
      ≤ C₂ * (α ^ 2 * (b ^ 2 + b * X)) := by
    linarith only [hI1b']
  have e2 : -α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP U B
      ≤ (5 + α) * ((α * b) * X) := by
    have h := (abs_le.mp hcsU).1
    rw [hbX, hXX] at h
    have h5 : 0 ≤ α * (5 + α) := by nlinarith only [hα]
    nlinarith only [h, h5, hb0, hX0]
  have e3 : Work.FTS.EllipticEst.AngSecond.IP G₁ B ≤ C₃ * (Pb ^ 2 + Pb * X) := by
    have h := hI4b
    rw [hHkPbF, hHkB, Real.sqrt_sq hPb0, Real.sqrt_sq hX0] at h
    exact h
  have e4 : -6 * Work.FTS.EllipticEst.AngSecond.IP Ψ B ≤ 6 * (m * X) := by
    have h := (abs_le.mp hcsΨ).1
    rw [hXX, hmX] at h
    linarith only [h]
  have heqF : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP F F) = f := by
    rw [Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq α F, hf]
  have e5 : -Work.FTS.EllipticEst.AngSecond.IP F B ≤ f * X := by
    have h := (abs_le.mp hcsF).1
    rw [hXX, heqF] at h
    linarith only [h]
  -- ## the identity, solved for the self-pairing of `∂_θθΨ`
  have hid' : Work.FTS.EllipticEst.AngSecond.IP B B
      = -α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B
        - α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP U B
        + Work.FTS.EllipticEst.AngSecond.IP G₁ B
        - 6 * Work.FTS.EllipticEst.AngSecond.IP Ψ B
        - Work.FTS.EllipticEst.AngSecond.IP F B := by
    linarith only [hid]
  -- ## the identity, solved for the self-pairing of `∂_θθΨ`
  have hid' : Work.FTS.EllipticEst.AngSecond.IP B B
      = -α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B
        - α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP U B
        + Work.FTS.EllipticEst.AngSecond.IP G₁ B
        - 6 * Work.FTS.EllipticEst.AngSecond.IP Ψ B
        - Work.FTS.EllipticEst.AngSecond.IP F B := by
    linarith only [hid]
  -- ## the Step-1 bounds
  have hstep1' : m + α * b + Pb ≤ C₁ * f := by
    have h := hstep1
    rw [hm, hb, hPb, hf] at h
    exact h
  have hm_le : m ≤ C₁ * f := by
    have h2 : 0 ≤ α * b := mul_nonneg hα.le hb0
    linarith only [hstep1', h2, hPb0]
  have hPb_le : Pb ≤ C₁ * f := by
    have h2 : 0 ≤ α * b := mul_nonneg hα.le hb0
    linarith only [hstep1', h2, hm0]
  -- ## the collected bound
  set N : ℝ := f + α * b with hN
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have hNf : f ≤ N := by rw [hN]; nlinarith only [hb0, hα.le]
  have hNb : α * b ≤ N := by rw [hN]; nlinarith only [hf0]
  have hαb2 : α ^ 2 * b ^ 2 ≤ N ^ 2 := by
    have h1 : α ^ 2 * b ^ 2 = (α * b) ^ 2 := by ring
    rw [h1]
    exact pow_le_pow_left₀ (mul_nonneg hα.le hb0) hNb 2
  have hαbX : α ^ 2 * b * X ≤ N * X := by
    have h1 : α ^ 2 * b ≤ N := by
      have h2 : α ^ 2 * b = α * (α * b) := by ring
      rw [h2]
      have h3 : α * (α * b) ≤ α * N := mul_le_mul_of_nonneg_left hNb hα.le
      have h4 : α * N ≤ 1 * N := mul_le_mul_of_nonneg_right (by linarith) hN0
      linarith only [h3, h4]
    exact mul_le_mul_of_nonneg_right h1 hX0
  have h5bX : (5 + α) * ((α * b) * X) ≤ 6 * (N * X) := by
    have h1 : 5 + α ≤ 6 := by linarith
    have h2 : 0 ≤ (α * b) * X := by positivity
    have h3 : (α * b) * X ≤ N * X := mul_le_mul_of_nonneg_right hNb hX0
    calc (5 + α) * ((α * b) * X) ≤ 6 * ((α * b) * X) := mul_le_mul_of_nonneg_right h1 h2
      _ ≤ 6 * (N * X) := by linarith only [h3]
  have hPb2_le : Pb ^ 2 ≤ C₁ ^ 2 * N ^ 2 := by
    have h1 : Pb ^ 2 ≤ (C₁ * f) ^ 2 := pow_le_pow_left₀ hPb0 hPb_le 2
    have h3 : 0 ≤ C₁ := hC₁.le
    have h4 : C₁ * f ≤ C₁ * N := mul_le_mul_of_nonneg_left hNf h3
    have h2 : (C₁ * f) ^ 2 ≤ (C₁ * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg h3 hf0) h4 2
    have h5 : (C₁ * N) ^ 2 = C₁ ^ 2 * N ^ 2 := by ring
    linarith only [h1, h2, h5.le, h5.ge]
  have hPbX_le : Pb * X ≤ C₁ * (N * X) := by
    have h1 : Pb * X ≤ (C₁ * f) * X := mul_le_mul_of_nonneg_right hPb_le hX0
    have h2 : (C₁ * f) * X ≤ (C₁ * N) * X := by
      nlinarith only [mul_le_mul_of_nonneg_right hNf hC₁.le, hX0]
    have h4 : (C₁ * N) * X = C₁ * (N * X) := by ring
    linarith only [h1, h2, h4.le, h4.ge]
  have hmX_le : m * X ≤ C₁ * (N * X) := by
    have h1 : m * X ≤ (C₁ * f) * X := mul_le_mul_of_nonneg_right hm_le hX0
    have h2 : (C₁ * f) * X ≤ (C₁ * N) * X := by
      nlinarith only [mul_le_mul_of_nonneg_right hNf hC₁.le, hX0]
    have h4 : (C₁ * N) * X = C₁ * (N * X) := by ring
    linarith only [h1, h2, h4.le, h4.ge]
  have hbase : X ^ 2 ≤ C₂ * (α ^ 2 * (b ^ 2 + b * X)) + (5 + α) * ((α * b) * X)
      + C₃ * (Pb ^ 2 + Pb * X) + 6 * (m * X) + f * X := by
    have h2 : X ^ 2 = -α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP Q B
        - α * (5 + α) * Work.FTS.EllipticEst.AngSecond.IP U B
        + Work.FTS.EllipticEst.AngSecond.IP G₁ B
        - 6 * Work.FTS.EllipticEst.AngSecond.IP Ψ B
        - Work.FTS.EllipticEst.AngSecond.IP F B := by
      rw [hX2, hid']
    linarith only [h2, e1, e2, e3, e4, e5]
  have p1 : C₂ * (α ^ 2 * (b ^ 2 + b * X)) ≤ C₂ * (N ^ 2 + N * X) := by
    have h1 : α ^ 2 * (b ^ 2 + b * X) ≤ N ^ 2 + N * X := by linarith only [hαb2, hαbX]
    exact mul_le_mul_of_nonneg_left h1 hC₂pos.le
  have p3 : C₃ * (Pb ^ 2 + Pb * X) ≤ C₃ * (C₁ ^ 2 * N ^ 2 + C₁ * (N * X)) := by
    have h1 : Pb ^ 2 + Pb * X ≤ C₁ ^ 2 * N ^ 2 + C₁ * (N * X) := by
      linarith only [hPb2_le, hPbX_le]
    exact mul_le_mul_of_nonneg_left h1 hC₃pos.le
  have p4 : 6 * (m * X) ≤ 6 * (C₁ * (N * X)) := by linarith only [hmX_le]
  have p5 : f * X ≤ N * X := mul_le_mul_of_nonneg_right hNf hX0
  have hkey : X ^ 2 ≤ max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) * (N ^ 2 + N * X) := by
    have hNX0 : 0 ≤ N * X := mul_nonneg hN0 hX0
    have hN20 : 0 ≤ N ^ 2 := sq_nonneg N
    have hsum : X ^ 2 ≤ (C₂ + C₃ * C₁ ^ 2) * N ^ 2
        + (C₂ + C₃ * C₁ + 6 * C₁ + 7) * (N * X) := by
      nlinarith only [hbase, p1, h5bX, p3, p4, p5]
    have hle1 : (C₂ + C₃ * C₁ ^ 2) * N ^ 2
        ≤ max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) * N ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hN20
    have hle2 : (C₂ + C₃ * C₁ + 6 * C₁ + 7) * (N * X)
        ≤ max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) * (N * X) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hNX0
    have hgoal : max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) * (N ^ 2 + N * X)
        = max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) * N ^ 2
          + max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) * (N * X) := by ring
    linarith only [hsum, hle1, hle2, hgoal.le, hgoal.ge]
  have hK0 : 0 ≤ max (C₂ + C₃ * C₁ ^ 2) (C₂ + C₃ * C₁ + 6 * C₁ + 7) := by
    have h1 : 0 ≤ C₂ + C₃ * C₁ ^ 2 := by positivity
    exact le_trans h1 (le_max_left _ _)
  have hfin := quad_solve' hK0 hN0 hkey
  rw [hX, hN, hf, hb] at hfin
  exact hfin

end Work.FTS.EllipticEst.Prop
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.IBPsub.Slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

set_option autoImplicit false
set_option maxHeartbeats 2000000

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-! ## Closure of `SmoothOpen` and `TestQ0` for the slot operators -/

/-- Multiplication by a power of `z` preserves smoothness on the open quadrant. -/
theorem smoothOpen_zpow_mul (k : ℕ) {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ k * f z θ) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ k) Q0 :=
    (contDiff_fst.pow k).contDiffOn
  exact h.mul hf

/-- The slot operators preserve smoothness on the open quadrant. -/
theorem smoothOpen_slot {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (r : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (slot r f) := by
  rcases r with _ | _ | r
  · show Work.FTS.EllipticEst.SmoothOpen (slot1 f)
    exact smoothOpen_zpow_mul 2 (Work.FTS.EllipticEst.SmoothOpen.pzIter hf 2)
  · show Work.FTS.EllipticEst.SmoothOpen (slot2 f)
    exact smoothOpen_pthIter hf 2
  · show Work.FTS.EllipticEst.SmoothOpen (slot3 f)
    exact Work.FTS.EllipticEst.SmoothOpen.Dz (smoothOpen_pthIter hf 2)

/-- The transpose of the first slot preserves the class of test functions. -/
theorem testQ0_slot1Star {ψ : ℝ → ℝ → ℝ} (h : TestQ0 ψ) : TestQ0 (slot1Star ψ) :=
  testQ0_pzIterStar (testQ0_zpow_mul 2 h) 2

/-- The transpose of the second slot preserves the class of test functions. -/
theorem testQ0_slot2Star {ψ : ℝ → ℝ → ℝ} (h : TestQ0 ψ) : TestQ0 (slot2Star ψ) :=
  testQ0_pthIterStar h 2

/-- The transpose of the third slot preserves the class of test functions. -/
theorem testQ0_slot3Star {ψ : ℝ → ℝ → ℝ} (h : TestQ0 ψ) : TestQ0 (slot3Star ψ) :=
  testQ0_pthIterStar (testQ0_DzStar h) 2

/-! ## The transposes of the three slots -/

/-- **The transpose of `slot1 f = z² ∂_z² f`.** -/
theorem integral_slot1_mul_eq {f ψ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, slot1 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, f p.1 p.2 * pzIterStar 2 (fun z θ => z ^ 2 * ψ z θ) p.1 p.2 := by
  have hz2 : TestQ0 (fun z θ => z ^ 2 * ψ z θ) := testQ0_zpow_mul 2 hψ
  have hstep : ∫ p : ℝ × ℝ,
        Work.Spaces.pzIter 2 f p.1 p.2 * (p.1 ^ 2 * ψ p.1 p.2)
      = (-1 : ℝ) ^ 2 * ∫ p : ℝ × ℝ,
          f p.1 p.2 * Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * ψ z θ) p.1 p.2 :=
    integral_pzIter_mul_eq 2 hf hz2
  calc ∫ p : ℝ × ℝ, slot1 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, Work.Spaces.pzIter 2 f p.1 p.2 * (p.1 ^ 2 * ψ p.1 p.2) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp only [slot1]; ring
    _ = ∫ p : ℝ × ℝ,
          f p.1 p.2 * Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * ψ z θ) p.1 p.2 := by
        rw [hstep]
        rw [show (-1 : ℝ) ^ 2 = 1 by norm_num, one_mul]
    _ = ∫ p : ℝ × ℝ,
          f p.1 p.2 * pzIterStar 2 (fun z θ => z ^ 2 * ψ z θ) p.1 p.2 := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp [pzIterStar]

/-- **The transpose of `slot2 f = ∂_θ² f`.** -/
theorem integral_slot2_mul_eq {f ψ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, slot2 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, f p.1 p.2 * pthIterStar 2 ψ p.1 p.2 := by
  have hstep := integral_pthIter_mul_eq 2 hf hψ
  calc ∫ p : ℝ × ℝ, slot2 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, Work.Spaces.pthIter 2 f p.1 p.2 * ψ p.1 p.2 := rfl
    _ = (-1 : ℝ) ^ 2 * ∫ p : ℝ × ℝ,
          f p.1 p.2 * Work.Spaces.pthIter 2 ψ p.1 p.2 := hstep
    _ = ∫ p : ℝ × ℝ, f p.1 p.2 * pthIterStar 2 ψ p.1 p.2 := by
        rw [show (-1 : ℝ) ^ 2 = 1 by norm_num, one_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp [pthIterStar]

/-- **The transpose of `slot3 f = D_z ∂_θ² f`.** -/
theorem integral_slot3_mul_eq {f ψ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hψ : TestQ0 ψ) :
    ∫ p : ℝ × ℝ, slot3 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, f p.1 p.2 * pthIterStar 2 (DzStar ψ) p.1 p.2 := by
  have h1 : ∫ p : ℝ × ℝ, slot3 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, Work.Spaces.pthIter 2 f p.1 p.2 * DzStar ψ p.1 p.2 :=
    integral_Dz_mul_eq (g := Work.Spaces.pthIter 2 f) (ψ := ψ)
      (smoothOpen_pthIter hf 2) hψ
  have h2 := integral_pthIter_mul_eq 2 (g := f) (ψ := DzStar ψ) hf (testQ0_DzStar hψ)
  calc ∫ p : ℝ × ℝ, slot3 f p.1 p.2 * ψ p.1 p.2
      = ∫ p : ℝ × ℝ, Work.Spaces.pthIter 2 f p.1 p.2 * DzStar ψ p.1 p.2 := h1
    _ = (-1 : ℝ) ^ 2 * ∫ p : ℝ × ℝ,
          f p.1 p.2 * Work.Spaces.pthIter 2 (DzStar ψ) p.1 p.2 := h2
    _ = ∫ p : ℝ × ℝ, f p.1 p.2 * pthIterStar 2 (DzStar ψ) p.1 p.2 := by
        rw [show (-1 : ℝ) ^ 2 = 1 by norm_num, one_mul]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
        simp [pthIterStar]

/-! ## The sub-slot transposition on `ℝ²` -/

/-- The transposition of the `(j,i)`-sub-slot of the `r`-th slot, as an identity of integrals
over `ℝ²` (which is where the integration by parts lives). -/
theorem integral_mixed_subSlot (r j i : ℕ) {f φ : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hφ : TestQ0 φ) :
    ∫ p : ℝ × ℝ, Work.Spaces.mixed j i (slot r f) p.1 p.2 * φ p.1 p.2
      = ∫ p : ℝ × ℝ, f p.1 p.2 * subSlotStar r j i φ p.1 p.2 := by
  rw [integral_mixed_mul_eq j i (hg := smoothOpen_slot hf r) (hψ := hφ)]
  rcases r with _ | _ | r
  · show ∫ p : ℝ × ℝ, slot1 f p.1 p.2 * mixedStar j i φ p.1 p.2
        = ∫ p : ℝ × ℝ, f p.1 p.2 * slot1Star (mixedStar j i φ) p.1 p.2
    exact integral_slot1_mul_eq hf (testQ0_mixedStar hφ j i)
  · show ∫ p : ℝ × ℝ, slot2 f p.1 p.2 * mixedStar j i φ p.1 p.2
        = ∫ p : ℝ × ℝ, f p.1 p.2 * slot2Star (mixedStar j i φ) p.1 p.2
    exact integral_slot2_mul_eq hf (testQ0_mixedStar hφ j i)
  · show ∫ p : ℝ × ℝ, slot3 f p.1 p.2 * mixedStar j i φ p.1 p.2
        = ∫ p : ℝ × ℝ, f p.1 p.2 * slot3Star (mixedStar j i φ) p.1 p.2
    exact integral_slot3_mul_eq hf (testQ0_mixedStar hφ j i)

end Work.FTS.PhiStar.Honesty.SlotsLimit
end
end
