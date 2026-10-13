import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.thMollTransfer
import Submission.Work.FTS.EllSol.EllPkgAux.kernelJensen

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

theorem thMollSliceL2 : ∃ K : ℝ, 0 < K ∧ ∀ (u : ℝ → ℝ → ℝ) {ε z : ℝ}, 0 < ε → ε ≤ 1 / 2 → 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ) Work.Spaces.Iθ → MeasureTheory.IntegrableOn (fun θ : ℝ => (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ → (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllSol.PkgK5.K5c.thMoll u ε z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) ≤ K * ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Work.FTS.EllSol.K5cAux.thWeightCmp
  refine ⟨3 * K₁, by positivity, ?_⟩
  intro u ε z hε hε2 hz hu hu2
  set g : ℝ → ℝ := fun s => |u z s| with hgdef
  have hgint : IntegrableOn (fun s : ℝ => g s ^ 2 * σθ s) Iθ := by
    rw [hgdef]
    refine hu2.congr_fun (fun s _ => ?_) measurableSet_Icc
    show (u z s) ^ 2 * σθ s = |u z s| ^ 2 * σθ s
    rw [sq_abs]
  have hg2int : IntegrableOn (fun s : ℝ => g s ^ 2) Iθ :=
    integrableOn_sq_of_integrableOn hgint
  obtain ⟨hswap_eq, hswap_i1, hswap_i2⟩ := kernelSwap (g := g) hε hg2int
  have hA : IntegrableOn (fun θ : ℝ => 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2)) Iθ :=
    hswap_i1.const_mul 3
  have hmono : (∫ θ in Iθ, σθ θ * (thMoll u ε z θ) ^ 2)
      ≤ ∫ θ in Iθ, 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (f := fun θ : ℝ => σθ θ * (thMoll u ε z θ) ^ 2)
      (g := fun θ : ℝ => 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2)) ?_ hA ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (Work.FTS.EllipticEst.thEta_nonneg hθ) (sq_nonneg _))
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        have hpt : |thMoll u ε z θ| ≤ ∫ s in Iθ, KJ ε θ s * g s := by
          simpa only [hgdef] using thMoll_abs_le u hε hε2 hu hθ
        have hKg : (∫ s in Iθ, KJ ε θ s * g s) ^ 2 ≤ 3 * ∫ s in Iθ, KJ ε θ s * g s ^ 2 :=
          KJ_pointwise hε hgint hθ
        have habs := abs_le.mp hpt
        have h2 : (thMoll u ε z θ) ^ 2 ≤ (∫ s in Iθ, KJ ε θ s * g s) ^ 2 :=
          sq_le_sq' habs.1 habs.2
        have hσ : 0 ≤ σθ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
        calc σθ θ * (thMoll u ε z θ) ^ 2
            ≤ σθ θ * (∫ s in Iθ, KJ ε θ s * g s) ^ 2 := mul_le_mul_of_nonneg_left h2 hσ
          _ ≤ σθ θ * (3 * ∫ s in Iθ, KJ ε θ s * g s ^ 2) :=
              mul_le_mul_of_nonneg_left hKg hσ
          _ = 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2) := by ring)
  have hc1 : (∫ θ in Iθ, 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2))
      = 3 * ∫ θ in Iθ, σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2 :=
    MeasureTheory.integral_const_mul 3 _
  have hschur : ∀ᵐ s ∂(volume.restrict Iθ), (∫ θ in Iθ, σθ θ * KJ ε θ s) ≤ K₁ * σθ s :=
    KJ_schur_ae (K₁ := K₁) (ε := ε) (fun u' hu' => hK₁ ε u' hε hε2 hu')
  have hKσ_int : IntegrableOn (fun s : ℝ => g s ^ 2 * (K₁ * σθ s)) Iθ :=
    MeasureTheory.Integrable.congr (hgint.const_mul K₁) (Filter.Eventually.of_forall (fun s => by
      show K₁ * (g s ^ 2 * σθ s) = g s ^ 2 * (K₁ * σθ s)
      ring))
  have hmono2 : (∫ s in Iθ, g s ^ 2 * (∫ θ in Iθ, σθ θ * KJ ε θ s))
      ≤ ∫ s in Iθ, g s ^ 2 * (K₁ * σθ s) := by
    refine MeasureTheory.integral_mono_ae hswap_i2 hKσ_int ?_
    filter_upwards [hschur] with s hs
    exact mul_le_mul_of_nonneg_left hs (sq_nonneg (g s))
  have hKσ_eq : (∫ s in Iθ, g s ^ 2 * (K₁ * σθ s)) = K₁ * ∫ s in Iθ, g s ^ 2 * σθ s := by
    have he : (fun s : ℝ => g s ^ 2 * (K₁ * σθ s)) = fun s : ℝ => K₁ * (g s ^ 2 * σθ s) := by
      funext s
      ring
    rw [he, MeasureTheory.integral_const_mul]
  calc (∫ θ in Iθ, (thMoll u ε z θ) ^ 2 * σθ θ)
      = ∫ θ in Iθ, σθ θ * (thMoll u ε z θ) ^ 2 := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    _ ≤ ∫ θ in Iθ, 3 * (σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2) := hmono
    _ = 3 * ∫ θ in Iθ, σθ θ * ∫ s in Iθ, KJ ε θ s * g s ^ 2 := hc1
    _ = 3 * ∫ s in Iθ, g s ^ 2 * (∫ θ in Iθ, σθ θ * KJ ε θ s) := by rw [hswap_eq]
    _ ≤ 3 * ∫ s in Iθ, g s ^ 2 * (K₁ * σθ s) :=
          mul_le_mul_of_nonneg_left hmono2 (by norm_num)
    _ = 3 * (K₁ * ∫ s in Iθ, g s ^ 2 * σθ s) := by rw [hKσ_eq]
    _ = (3 * K₁) * ∫ s in Iθ, g s ^ 2 * σθ s := by ring
    _ = (3 * K₁) * ∫ s in Iθ, (u z s) ^ 2 * σθ s := by
        congr 1
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
        simp only [hgdef, sq_abs]

end Work.FTS.EllSol.EllPkgAux
