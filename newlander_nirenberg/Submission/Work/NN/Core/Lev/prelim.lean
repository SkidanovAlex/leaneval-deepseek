import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.Lcoef_uniform_estimate_on
import Submission.Work.NN.Core.holderNorm_fderiv_apply_le
import Submission.Work.NN.Core.holderNorm_const_mul_le

set_option maxHeartbeats 4000000

namespace Work.NN.Core.Lev

open scoped NNReal ENNReal ContDiff
open Set

noncomputable section

variable {n : ℕ}

lemma ofReal_norm_le_iDN_zero {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {f : (Fin n → ℂ) → A} {S : Set (Fin n → ℂ)} {x : Fin n → ℂ} (hx : x ∈ S) :
    ENNReal.ofReal ‖f x‖ ≤ Work.CR.Flat.Holder.iDN 0 f S := by
  have h := Work.CR.Flat.Holder.le_iDN (A := A) 0 (f := f) (Ω := S) hx
  simpa only [norm_iteratedFDerivWithin_zero] using h

lemma ofReal_div_le_hSN_zero {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {f : (Fin n → ℂ) → A} {α : ℝ} {S : Set (Fin n → ℂ)} {x y : Fin n → ℂ}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ENNReal.ofReal (‖f x - f y‖ / ‖x - y‖ ^ α) ≤ Work.CR.Flat.Holder.hSN 0 α f S := by
  have h := Work.CR.Flat.Holder.le_hSN (A := A) 0 α (f := f) (Ω := S) hx hy hxy
  simpa only [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub] using h

lemma ofReal_div_le_mul_add {α : ℝ} {Ω S : Set (Fin n → ℂ)} {u g : (Fin n → ℂ) → ℂ}
    {A B Cc D : ℝ≥0∞}
    (hA : ∀ z ∈ S, ENNReal.ofReal ‖u z‖ ≤ A)
    (hB : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ENNReal.ofReal (‖u x - u y‖ / ‖x - y‖ ^ α) ≤ B)
    (hC : ∀ z ∈ Ω, ENNReal.ofReal ‖g z‖ ≤ Cc)
    (hD : ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) ≤ D)
    (hsupp : ∀ z ∈ Ω, g z ≠ 0 → z ∈ S)
    {x y : Fin n → ℂ} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ENNReal.ofReal (‖u x * g x - u y * g y‖ / ‖x - y‖ ^ α) ≤ A * D + B * Cc := by
  have hd : (0:ℝ) < ‖x - y‖ ^ α :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
  by_cases hxS : x ∈ S
  · by_cases hyS : y ∈ S
    · have hdec : u x * g x - u y * g y = u x * (g x - g y) + (u x - u y) * g y := by ring
      have hbound : ‖u x * g x - u y * g y‖ / ‖x - y‖ ^ α
          ≤ ‖u x‖ * (‖g x - g y‖ / ‖x - y‖ ^ α)
            + (‖u x - u y‖ / ‖x - y‖ ^ α) * ‖g y‖ := by
        rw [hdec]
        have h0 : ‖u x * (g x - g y) + (u x - u y) * g y‖
            ≤ ‖u x‖ * ‖g x - g y‖ + ‖u x - u y‖ * ‖g y‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        calc (‖u x * (g x - g y) + (u x - u y) * g y‖) * (‖x - y‖ ^ α)⁻¹
            ≤ (‖u x‖ * ‖g x - g y‖ + ‖u x - u y‖ * ‖g y‖) * (‖x - y‖ ^ α)⁻¹ :=
              mul_le_mul_of_nonneg_right h0 (inv_nonneg.mpr hd.le)
          _ = ‖u x‖ * (‖g x - g y‖ * (‖x - y‖ ^ α)⁻¹)
                + (‖u x - u y‖ * (‖x - y‖ ^ α)⁻¹) * ‖g y‖ := by ring
      calc ENNReal.ofReal (‖u x * g x - u y * g y‖ / ‖x - y‖ ^ α)
          ≤ ENNReal.ofReal (‖u x‖ * (‖g x - g y‖ / ‖x - y‖ ^ α)
              + (‖u x - u y‖ / ‖x - y‖ ^ α) * ‖g y‖) := ENNReal.ofReal_le_ofReal hbound
        _ = ENNReal.ofReal ‖u x‖ * ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α)
              + ENNReal.ofReal (‖u x - u y‖ / ‖x - y‖ ^ α) * ENNReal.ofReal ‖g y‖ := by
            rw [ENNReal.ofReal_add
                (mul_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) hd.le))
                (mul_nonneg (div_nonneg (norm_nonneg _) hd.le) (norm_nonneg _)),
              ENNReal.ofReal_mul (norm_nonneg _),
              ENNReal.ofReal_mul (div_nonneg (norm_nonneg _) hd.le)]
        _ ≤ A * D + B * Cc :=
            add_le_add (mul_le_mul' (hA x hxS) (hD x hx y hy hxy))
              (mul_le_mul' (hB x hxS y hyS hxy) (hC y hy))
    · have hgy : g y = 0 := by by_contra hcon; exact hyS (hsupp y hy hcon)
      have hdec : u x * g x - u y * g y = u x * (g x - g y) := by rw [hgy, mul_zero]; ring
      have hbound : ‖u x * g x - u y * g y‖ / ‖x - y‖ ^ α
          ≤ ‖u x‖ * (‖g x - g y‖ / ‖x - y‖ ^ α) := by
        rw [hdec, norm_mul, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      calc ENNReal.ofReal (‖u x * g x - u y * g y‖ / ‖x - y‖ ^ α)
          ≤ ENNReal.ofReal (‖u x‖ * (‖g x - g y‖ / ‖x - y‖ ^ α)) := ENNReal.ofReal_le_ofReal hbound
        _ = ENNReal.ofReal ‖u x‖ * ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) :=
            ENNReal.ofReal_mul (norm_nonneg _)
        _ ≤ A * D + B * Cc :=
            le_trans (mul_le_mul' (hA x hxS) (hD x hx y hy hxy)) (le_add_right le_rfl)
  · have hgx : g x = 0 := by by_contra hcon; exact hxS (hsupp x hx hcon)
    by_cases hyS : y ∈ S
    · have hdec : u x * g x - u y * g y = -(u y * (g y - g x)) := by rw [hgx, mul_zero]; ring
      have hbound : ‖u x * g x - u y * g y‖ / ‖x - y‖ ^ α
          ≤ ‖u y‖ * (‖g y - g x‖ / ‖x - y‖ ^ α) := by
        rw [hdec, norm_neg, norm_mul, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      calc ENNReal.ofReal (‖u x * g x - u y * g y‖ / ‖x - y‖ ^ α)
          ≤ ENNReal.ofReal (‖u y‖ * (‖g y - g x‖ / ‖x - y‖ ^ α)) := ENNReal.ofReal_le_ofReal hbound
        _ = ENNReal.ofReal ‖u y‖ * ENNReal.ofReal (‖g y - g x‖ / ‖x - y‖ ^ α) :=
            ENNReal.ofReal_mul (norm_nonneg _)
        _ ≤ A * D + B * Cc := by
            refine le_trans (mul_le_mul' (hA y hyS) ?_) (le_add_right le_rfl)
            simpa only [norm_sub_rev] using hD y hy x hx (Ne.symm hxy)
    · have hgy : g y = 0 := by by_contra hcon; exact hyS (hsupp y hy hcon)
      rw [hgx, hgy, mul_zero, mul_zero, sub_self, norm_zero, zero_div, ENNReal.ofReal_zero]
      exact bot_le


/-- **Localised level-`0` product estimate.** -/
theorem holderNorm_zero_mul_le_support {α : ℝ} {Ω S : Set (Fin n → ℂ)} {u g : (Fin n → ℂ) → ℂ}
    (hsupp : ∀ z ∈ Ω, g z ≠ 0 → z ∈ S) :
    Work.CR.Flat.holderNorm 0 α (fun z => u z * g z) Ω
      ≤ (Work.CR.Flat.Holder.iDN 0 u S + Work.CR.Flat.Holder.hSN 0 α u S)
        * (Work.CR.Flat.Holder.iDN 0 g Ω + Work.CR.Flat.Holder.hSN 0 α g Ω) := by
  have hL : Work.CR.Flat.holderNorm 0 α (fun z => u z * g z) Ω
      = Work.CR.Flat.Holder.iDN 0 (fun z => u z * g z) Ω
        + Work.CR.Flat.Holder.hSN 0 α (fun z => u z * g z) Ω := by
    rw [Work.CR.Flat.Holder.iDN_complex_eq, Work.CR.Flat.Holder.hSN_complex_eq,
      Work.CR.Flat.holderNorm, Finset.range_one, Finset.sum_singleton]
  have h1 : Work.CR.Flat.Holder.iDN 0 (fun z => u z * g z) Ω
      ≤ Work.CR.Flat.Holder.iDN 0 u S * Work.CR.Flat.Holder.iDN 0 g Ω := by
    rw [Work.CR.Flat.Holder.iDN_zero_deriv, Work.CR.Flat.Holder.iDN_zero_deriv,
      Work.CR.Flat.Holder.iDN_zero_deriv]
    refine iSup₂_le fun z hz => ?_
    by_cases hg : g z = 0
    · rw [hg, mul_zero, norm_zero, ENNReal.ofReal_zero]; exact bot_le
    · have hzS : z ∈ S := hsupp z hz hg
      calc ENNReal.ofReal ‖u z * g z‖
          = ENNReal.ofReal ‖u z‖ * ENNReal.ofReal ‖g z‖ := by
            rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
        _ ≤ (⨆ x ∈ S, ENNReal.ofReal ‖u x‖) * ⨆ x ∈ Ω, ENNReal.ofReal ‖g x‖ :=
            mul_le_mul' (le_iSup₂_of_le z hzS le_rfl) (le_iSup₂_of_le z hz le_rfl)
  have h2 : Work.CR.Flat.Holder.hSN 0 α (fun z => u z * g z) Ω
      ≤ Work.CR.Flat.Holder.iDN 0 u S * Work.CR.Flat.Holder.hSN 0 α g Ω
        + Work.CR.Flat.Holder.hSN 0 α u S * Work.CR.Flat.Holder.iDN 0 g Ω := by
    rw [Work.CR.Flat.Holder.hSN_zero_deriv]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    exact ofReal_div_le_mul_add
      (fun z hz => ofReal_norm_le_iDN_zero hz)
      (fun x hx y hy hxy => ofReal_div_le_hSN_zero hx hy hxy)
      (fun z hz => ofReal_norm_le_iDN_zero hz)
      (fun x hx y hy hxy => ofReal_div_le_hSN_zero hx hy hxy)
      hsupp hx hy hxy
  rw [hL]
  refine le_trans (add_le_add h1 h2) ?_
  rw [add_mul, mul_add, mul_add]
  calc Work.CR.Flat.Holder.iDN 0 u S * Work.CR.Flat.Holder.iDN 0 g Ω
        + (Work.CR.Flat.Holder.iDN 0 u S * Work.CR.Flat.Holder.hSN 0 α g Ω
          + Work.CR.Flat.Holder.hSN 0 α u S * Work.CR.Flat.Holder.iDN 0 g Ω)
      = Work.CR.Flat.Holder.iDN 0 u S * Work.CR.Flat.Holder.iDN 0 g Ω
        + Work.CR.Flat.Holder.iDN 0 u S * Work.CR.Flat.Holder.hSN 0 α g Ω
        + Work.CR.Flat.Holder.hSN 0 α u S * Work.CR.Flat.Holder.iDN 0 g Ω := by
          rw [add_assoc]
    _ ≤ Work.CR.Flat.Holder.iDN 0 u S * Work.CR.Flat.Holder.iDN 0 g Ω
        + Work.CR.Flat.Holder.iDN 0 u S * Work.CR.Flat.Holder.hSN 0 α g Ω
        + (Work.CR.Flat.Holder.hSN 0 α u S * Work.CR.Flat.Holder.iDN 0 g Ω
          + Work.CR.Flat.Holder.hSN 0 α u S * Work.CR.Flat.Holder.hSN 0 α g Ω) :=
        add_le_add (le_refl _) (le_self_add (a := Work.CR.Flat.Holder.hSN 0 α u S
          * Work.CR.Flat.Holder.iDN 0 g Ω) (b := Work.CR.Flat.Holder.hSN 0 α u S
          * Work.CR.Flat.Holder.hSN 0 α g Ω))



lemma pi_norm_le_sum {n : ℕ} (z : Fin n → ℂ) : ‖z‖ ≤ ∑ j, ‖z j‖ := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr fun j => ?_
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem pertField_small {n : ℕ} {α ε : ℝ} (hε : 0 ≤ ε) {ρ : Fin n → ℝ} {Ω : Set (Fin n → ℂ)}
    (hΩopen : IsOpen Ω) (hΩρ : Ω ⊆ Work.CR.Flat.polydisc 0 ρ)
    {A : Cn n → Cn n →L[ℝ] Cn n}
    (hA : ∀ i j : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single i 1) j)
        (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) :
    ∀ i : Fin n,
      Work.CR.Flat.Holder.iDN 0 (fun z => A z (Pi.single i 1)) Ω
          ≤ ENNReal.ofReal ((n : ℝ) * ε) ∧
      Work.CR.Flat.Holder.hSN 0 α (fun z => A z (Pi.single i 1)) Ω
          ≤ ENNReal.ofReal ((n : ℝ) * ε) := by
  intro i
  set g : (Fin n → ℂ) → Fin n → ℂ := fun z => A z (Pi.single i 1) with hg
  have hcomp : ∀ j : Fin n,
      Work.CR.Flat.Holder.iDN 0 (fun z => g z j) Ω ≤ ENNReal.ofReal ε ∧
      Work.CR.Flat.Holder.hSN 0 α (fun z => g z j) Ω ≤ ENNReal.ofReal ε := by
    intro j
    have hA' : Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single i 1) j)
        (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε := hA i j
    have hkey : Work.CR.Flat.holderNorm 0 α (fun z => g z j) Ω ≤ ENNReal.ofReal ε := by
      refine (Work.CR.Flat.holderNorm_mono_k (k := 0) (k' := 1) (by norm_num) α
        (fun z => g z j) Ω).trans ?_
      exact (Work.CR.Flat.holderNorm_mono_set (Ω := Work.CR.Flat.polydisc 0 ρ) (Ω' := Ω)
        (Work.CR.Flat.isOpen_polydisc 0 ρ) hΩopen hΩρ 1 α (fun z => g z j)).trans hA'
    exact ⟨(Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α (fun z => g z j) Ω
        (le_refl 0)).trans hkey,
      (Work.CR.Flat.holderSeminorm_le_holderNorm 0 α (fun z => g z j) Ω
        (le_refl 0)).trans hkey⟩
  have hsum : ENNReal.ofReal ((n : ℝ) * ε) = ∑ _j : Fin n, ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hε), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  constructor
  · rw [Work.CR.Flat.Holder.iDN_zero_deriv]
    refine iSup₂_le fun z hz => ?_
    calc ENNReal.ofReal ‖g z‖
        ≤ ENNReal.ofReal (∑ j : Fin n, ‖g z j‖) := ENNReal.ofReal_le_ofReal (pi_norm_le_sum _)
      _ = ∑ j : Fin n, ENNReal.ofReal ‖g z j‖ :=
          ENNReal.ofReal_sum_of_nonneg (fun j _ => norm_nonneg _)
      _ ≤ ∑ j : Fin n, ENNReal.ofReal ε := Finset.sum_le_sum fun j _ =>
          (ofReal_norm_le_iDN_zero (f := fun z => g z j) (S := Ω) hz).trans (hcomp j).1
      _ = ENNReal.ofReal ((n : ℝ) * ε) := hsum.symm
  · rw [Work.CR.Flat.Holder.hSN_zero_deriv]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    have hd : (0:ℝ) < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    calc ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal ((∑ j : Fin n, ‖g x j - g y j‖) / ‖x - y‖ ^ α) := by
          refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ hd.le)
          simpa only [Pi.sub_apply] using pi_norm_le_sum (g x - g y)
      _ = ENNReal.ofReal (∑ j : Fin n, ‖g x j - g y j‖ / ‖x - y‖ ^ α) := by rw [Finset.sum_div]
      _ = ∑ j : Fin n, ENNReal.ofReal (‖g x j - g y j‖ / ‖x - y‖ ^ α) :=
          ENNReal.ofReal_sum_of_nonneg (fun j _ => div_nonneg (norm_nonneg _) hd.le)
      _ ≤ ∑ j : Fin n, ENNReal.ofReal ε := Finset.sum_le_sum fun j _ =>
          (ofReal_div_le_hSN_zero (f := fun z => g z j) (S := Ω) hx hy hxy).trans (hcomp j).2
      _ = ENNReal.ofReal ((n : ℝ) * ε) := hsum.symm


lemma holderNorm_zero_const_le_one {α : ℝ} {Ω : Set (Fin n → ℂ)} {c : ℂ} (hc : ‖c‖ ≤ 1) :
    Work.CR.Flat.holderNorm 0 α (fun _ : Fin n → ℂ => c) Ω ≤ ENNReal.ofReal 1 := by
  have h1 : Work.CR.Flat.iterDerivNorm 0 (fun _ : Fin n → ℂ => c) Ω ≤ ENNReal.ofReal 1 := by
    rw [Work.CR.Flat.iterDerivNorm_zero]
    refine iSup₂_le fun z _ => ENNReal.ofReal_le_ofReal hc
  have h2 : Work.CR.Flat.holderSeminorm 0 α (fun _ : Fin n → ℂ => c) Ω ≤ 0 := by
    unfold Work.CR.Flat.holderSeminorm
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
    rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub]
    have hzero : (fun _ : Fin n → ℂ => c) x - (fun _ : Fin n → ℂ => c) y = 0 := by simp
    rw [hzero, norm_zero, zero_div, ENNReal.ofReal_zero]
  calc Work.CR.Flat.holderNorm 0 α (fun _ : Fin n → ℂ => c) Ω
      = Work.CR.Flat.iterDerivNorm 0 (fun _ : Fin n → ℂ => c) Ω
        + Work.CR.Flat.holderSeminorm 0 α (fun _ : Fin n → ℂ => c) Ω := by
        rw [Work.CR.Flat.holderNorm, Finset.range_one, Finset.sum_singleton]
    _ ≤ ENNReal.ofReal 1 + 0 := add_le_add h1 h2
    _ = ENNReal.ofReal 1 := add_zero _

lemma holderNorm_zero_add_le {α : ℝ} {Ω : Set (Fin n → ℂ)} {f g : (Fin n → ℂ) → ℂ} :
    Work.CR.Flat.holderNorm 0 α (f + g) Ω
      ≤ Work.CR.Flat.holderNorm 0 α f Ω + Work.CR.Flat.holderNorm 0 α g Ω := by
  have hL : Work.CR.Flat.holderNorm 0 α (f + g) Ω
      = Work.CR.Flat.Holder.iDN 0 (f + g) Ω + Work.CR.Flat.Holder.hSN 0 α (f + g) Ω := by
    rw [Work.CR.Flat.Holder.iDN_complex_eq, Work.CR.Flat.Holder.hSN_complex_eq,
      Work.CR.Flat.holderNorm, Finset.range_one, Finset.sum_singleton]
  have hf : Work.CR.Flat.holderNorm 0 α f Ω
      = Work.CR.Flat.Holder.iDN 0 f Ω + Work.CR.Flat.Holder.hSN 0 α f Ω := by
    rw [Work.CR.Flat.Holder.iDN_complex_eq, Work.CR.Flat.Holder.hSN_complex_eq,
      Work.CR.Flat.holderNorm, Finset.range_one, Finset.sum_singleton]
  have hg : Work.CR.Flat.holderNorm 0 α g Ω
      = Work.CR.Flat.Holder.iDN 0 g Ω + Work.CR.Flat.Holder.hSN 0 α g Ω := by
    rw [Work.CR.Flat.Holder.iDN_complex_eq, Work.CR.Flat.Holder.hSN_complex_eq,
      Work.CR.Flat.holderNorm, Finset.range_one, Finset.sum_singleton]
  rw [hL, hf, hg]
  have h1 : Work.CR.Flat.Holder.iDN 0 (f + g) Ω
      ≤ Work.CR.Flat.Holder.iDN 0 f Ω + Work.CR.Flat.Holder.iDN 0 g Ω := by
    rw [Work.CR.Flat.Holder.iDN_zero_deriv, Work.CR.Flat.Holder.iDN_zero_deriv,
      Work.CR.Flat.Holder.iDN_zero_deriv]
    refine iSup₂_le fun x hx => ?_
    refine le_trans (ENNReal.ofReal_le_ofReal (norm_add_le (f x) (g x))) ?_
    rw [ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact add_le_add (le_iSup₂_of_le x hx le_rfl) (le_iSup₂_of_le x hx le_rfl)
  have h2 : Work.CR.Flat.Holder.hSN 0 α (f + g) Ω
      ≤ Work.CR.Flat.Holder.hSN 0 α f Ω + Work.CR.Flat.Holder.hSN 0 α g Ω := by
    rw [Work.CR.Flat.Holder.hSN_zero_deriv, Work.CR.Flat.Holder.hSN_zero_deriv,
      Work.CR.Flat.Holder.hSN_zero_deriv]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    have hd : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    have hsub : (f + g) x - (f + g) y = (f x - f y) + (g x - g y) := by
      simp only [Pi.add_apply]; abel
    have hreal : ‖(f + g) x - (f + g) y‖ / ‖x - y‖ ^ α
        ≤ ‖f x - f y‖ / ‖x - y‖ ^ α + ‖g x - g y‖ / ‖x - y‖ ^ α := by
      rw [hsub]
      refine le_trans (div_le_div_of_nonneg_right (norm_add_le _ _) hd) ?_
      rw [add_div]
    refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
    rw [ENNReal.ofReal_add (div_nonneg (norm_nonneg _) hd) (div_nonneg (norm_nonneg _) hd)]
    exact add_le_add (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl)))
      (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl)))
  calc Work.CR.Flat.Holder.iDN 0 (f + g) Ω + Work.CR.Flat.Holder.hSN 0 α (f + g) Ω
      ≤ (Work.CR.Flat.Holder.iDN 0 f Ω + Work.CR.Flat.Holder.iDN 0 g Ω)
        + (Work.CR.Flat.Holder.hSN 0 α f Ω + Work.CR.Flat.Holder.hSN 0 α g Ω) :=
        add_le_add h1 h2
    _ = (Work.CR.Flat.Holder.iDN 0 f Ω + Work.CR.Flat.Holder.hSN 0 α f Ω)
        + (Work.CR.Flat.Holder.iDN 0 g Ω + Work.CR.Flat.Holder.hSN 0 α g Ω) := by
        rw [add_add_add_comm]

/-- **The `(0,1)`-datum of a `C¹` function for a perturbed structure, in terms of the size of the
perturbation.** -/
theorem dbarCn_data_le {n : ℕ} {α : ℝ} (hα0 : 0 < α) {Ω : Set (Cn n)} (hΩ : IsOpen Ω) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {u : Cn n → ℂ} (hu : ContDiffOn ℝ 1 u Ω)
        {B : Cn n → Cn n →L[ℝ] Cn n} {ε : ℝ} (hε : 0 ≤ ε)
        (hBsm : ∀ i l : Fin n,
          Work.CR.Flat.holderNorm 0 α (fun z => B z (Pi.single i 1) l) Ω ≤ ENNReal.ofReal ε)
        (hBc : ∀ i l : Fin n, ContDiffOn ℝ 0 (fun z => B z (Pi.single i 1) l) Ω)
        (j : Fin n),
      Work.CR.Flat.holderNorm 0 α (fun z => dbarCn (JstdCn n + B) u z (Pi.single j 1)) Ω
        ≤ ENNReal.ofReal C * (ENNReal.ofReal (1 + ε) * Work.CR.Flat.holderNorm 1 α u Ω) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Work.NN.Core.holderNorm_fderiv_apply_le (n := n) hα0 hΩ (k := 1) (le_refl 1)
  refine ⟨2 * C₀ + 1, by linarith, ?_⟩
  intro u hu B ε hε hBsm hBc j
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  -- the three directional-derivative factors
  set F₁ : Cn n → ℂ := fun z => fderiv ℝ u z (Pi.single j 1) with hF₁
  set F₂ : Cn n → ℂ := fun z => fderiv ℝ u z ((Complex.I : ℂ) • Pi.single j 1) with hF₂
  set F₃ : Cn n → ℂ := fun z => fderiv ℝ u z (B z (Pi.single j 1)) with hF₃
  have hdec : (fun z => dbarCn (JstdCn n + B) u z (Pi.single j 1))
      = fun z => (1 / 2 : ℂ) * F₁ z + (Complex.I / 2) * F₂ z + (Complex.I / 2) * F₃ z := by
    funext z
    have h1 : (JstdCn n + B) z (Pi.single j 1)
        = (Complex.I : ℂ) • Pi.single j 1 + B z (Pi.single j 1) := by
      rw [Pi.add_apply, add_apply, Work.NN.Core.JstdCn_apply]
    rw [Work.NN.Core.dbarCn_apply, h1, map_add]
    simp only [hF₁, hF₂, hF₃]
    ring
  -- the three estimates
  have hb1 : ∀ l : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun _ : Cn n => (Pi.single j 1 : Cn n) l) Ω ≤ ENNReal.ofReal (1:ℝ) := by
    intro l
    have hc : ‖(Pi.single j 1 : Cn n) l‖ ≤ 1 := by
      by_cases hl : l = j
      · subst hl; simp
      · simp [Pi.single_eq_of_ne hl]
    simpa using holderNorm_zero_const_le_one (n := n) (Ω := Ω) hc
  have hc1 : ∀ l : Fin n, ContDiffOn ℝ (0 : ℕ∞) (fun _ : Cn n => (Pi.single j 1 : Cn n) l) Ω :=
    fun l => contDiffOn_const
  have hF1le : Work.CR.Flat.holderNorm 0 α F₁ Ω
      ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal (1:ℝ) * Work.CR.Flat.holderNorm 1 α u Ω) :=
    hC₀ hu hc1 (by norm_num) (by simpa using hb1)
  have hb2 : ∀ l : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun _ : Cn n => ((Complex.I : ℂ) • Pi.single j 1) l) Ω ≤ ENNReal.ofReal (1:ℝ) := by
    intro l
    have hc : ‖((Complex.I : ℂ) • Pi.single j 1 : Cn n) l‖ ≤ 1 := by
      by_cases hl : l = j
      · subst hl; simp
      · simp [Pi.single_eq_of_ne hl]
    simpa using holderNorm_zero_const_le_one (n := n) (Ω := Ω) hc
  have hc2 : ∀ l : Fin n, ContDiffOn ℝ (0 : ℕ∞)
      (fun _ : Cn n => ((Complex.I : ℂ) • Pi.single j 1) l) Ω := fun l => contDiffOn_const
  have hF2le : Work.CR.Flat.holderNorm 0 α F₂ Ω
      ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal (1:ℝ) * Work.CR.Flat.holderNorm 1 α u Ω) :=
    hC₀ hu hc2 (by norm_num) (by simpa using hb2)
  have hF3le : Work.CR.Flat.holderNorm 0 α F₃ Ω
      ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal ε * Work.CR.Flat.holderNorm 1 α u Ω) :=
    hC₀ hu (fun l => hBc j l) hε (fun l => hBsm j l)
  -- combine
  rw [hdec]
  have hsm1 : Work.CR.Flat.holderNorm 0 α (fun z => (1 / 2 : ℂ) * F₁ z) Ω
      ≤ ENNReal.ofReal (1/2) * Work.CR.Flat.holderNorm 0 α F₁ Ω := by
    have h := Work.NN.Core.holderNorm_const_mul_le (k := 0) (α := α) hΩu (1/2 : ℂ) F₁
    have hnorm : ‖(1 / 2 : ℂ)‖ = 1/2 := by norm_num
    rwa [hnorm] at h
  have hsm2 : Work.CR.Flat.holderNorm 0 α (fun z => (Complex.I / 2) * F₂ z) Ω
      ≤ ENNReal.ofReal (1/2) * Work.CR.Flat.holderNorm 0 α F₂ Ω := by
    have h := Work.NN.Core.holderNorm_const_mul_le (k := 0) (α := α) hΩu (Complex.I / 2) F₂
    have hnorm : ‖(Complex.I / 2 : ℂ)‖ = 1/2 := by
      rw [norm_div, Complex.norm_I]; norm_num
    rwa [hnorm] at h
  have hsm3 : Work.CR.Flat.holderNorm 0 α (fun z => (Complex.I / 2) * F₃ z) Ω
      ≤ ENNReal.ofReal (1/2) * Work.CR.Flat.holderNorm 0 α F₃ Ω := by
    have h := Work.NN.Core.holderNorm_const_mul_le (k := 0) (α := α) hΩu (Complex.I / 2) F₃
    have hnorm : ‖(Complex.I / 2 : ℂ)‖ = 1/2 := by
      rw [norm_div, Complex.norm_I]; norm_num
    rwa [hnorm] at h
  have hadd1 := holderNorm_zero_add_le (n := n) (α := α) (Ω := Ω)
    (f := fun z => (1 / 2 : ℂ) * F₁ z) (g := fun z => (Complex.I / 2) * F₂ z)
  have hadd2 := holderNorm_zero_add_le (n := n) (α := α) (Ω := Ω)
    (f := fun z => (1 / 2 : ℂ) * F₁ z + (Complex.I / 2) * F₂ z)
    (g := fun z => (Complex.I / 2) * F₃ z)
  have hfun : (fun z => (1 / 2 : ℂ) * F₁ z + (Complex.I / 2) * F₂ z + (Complex.I / 2) * F₃ z)
      = (fun z => (1 / 2 : ℂ) * F₁ z + (Complex.I / 2) * F₂ z)
        + (fun z => (Complex.I / 2) * F₃ z) := by
    funext z; simp only [Pi.add_apply]
  rw [hfun]
  have hsm1 : Work.CR.Flat.holderNorm 0 α (fun z => (1 / 2 : ℂ) * F₁ z) Ω
      ≤ ENNReal.ofReal (1/2) * Work.CR.Flat.holderNorm 0 α F₁ Ω := by
    have h := Work.NN.Core.holderNorm_const_mul_le (k := 0) (α := α) hΩu (1/2 : ℂ) F₁
    have hnorm : ‖(1 / 2 : ℂ)‖ = 1/2 := by norm_num
    rwa [hnorm] at h
  have hsm2 : Work.CR.Flat.holderNorm 0 α (fun z => (Complex.I / 2) * F₂ z) Ω
      ≤ ENNReal.ofReal (1/2) * Work.CR.Flat.holderNorm 0 α F₂ Ω := by
    have h := Work.NN.Core.holderNorm_const_mul_le (k := 0) (α := α) hΩu (Complex.I / 2) F₂
    have hnorm : ‖(Complex.I / 2 : ℂ)‖ = 1/2 := by
      rw [norm_div, Complex.norm_I]; norm_num
    rwa [hnorm] at h
  have hsm3 : Work.CR.Flat.holderNorm 0 α (fun z => (Complex.I / 2) * F₃ z) Ω
      ≤ ENNReal.ofReal (1/2) * Work.CR.Flat.holderNorm 0 α F₃ Ω := by
    have h := Work.NN.Core.holderNorm_const_mul_le (k := 0) (α := α) hΩu (Complex.I / 2) F₃
    have hnorm : ‖(Complex.I / 2 : ℂ)‖ = 1/2 := by
      rw [norm_div, Complex.norm_I]; norm_num
    rwa [hnorm] at h
  have e1 : ENNReal.ofReal (1/2) * Work.CR.Flat.holderNorm 0 α F₁ Ω
      ≤ ENNReal.ofReal (C₀/2) * Work.CR.Flat.holderNorm 1 α u Ω := by
    refine (mul_le_mul le_rfl hF1le bot_le bot_le).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_one, one_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
      show (1/2 : ℝ) * C₀ = C₀ / 2 by ring]
  have e2 : ENNReal.ofReal (1/2) * Work.CR.Flat.holderNorm 0 α F₂ Ω
      ≤ ENNReal.ofReal (C₀/2) * Work.CR.Flat.holderNorm 1 α u Ω := by
    refine (mul_le_mul le_rfl hF2le bot_le bot_le).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_one, one_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
      show (1/2 : ℝ) * C₀ = C₀ / 2 by ring]
  have e3 : ENNReal.ofReal (1/2) * Work.CR.Flat.holderNorm 0 α F₃ Ω
      ≤ ENNReal.ofReal (C₀/2) * (ENNReal.ofReal ε * Work.CR.Flat.holderNorm 1 α u Ω) :=
    (mul_le_mul le_rfl hF3le bot_le bot_le).trans (le_of_eq (by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
        show (1/2 : ℝ) * C₀ = C₀ / 2 by ring]))
  refine le_trans hadd2 ?_
  refine le_trans (add_le_add hadd1 le_rfl) ?_
  refine le_trans (add_le_add (add_le_add hsm1 hsm2) hsm3) ?_
  refine le_trans (add_le_add (add_le_add e1 e2) e3) ?_
  -- pure ENNReal arithmetic
  set A : ℝ≥0∞ := ENNReal.ofReal (C₀/2) with hA
  set Hu : ℝ≥0∞ := Work.CR.Flat.holderNorm 1 α u Ω with hHu
  have hkey : (A + A) + A * ENNReal.ofReal ε
      ≤ ENNReal.ofReal (2*C₀+1) * ENNReal.ofReal (1+ε) := by
    have h1 : A + A = ENNReal.ofReal C₀ := by
      rw [hA, ← ENNReal.ofReal_add (by linarith) (by linarith)]
      norm_num
    have h2 : A * ENNReal.ofReal ε = ENNReal.ofReal (C₀/2 * ε) := by
      rw [hA]; exact (ENNReal.ofReal_mul (by linarith)).symm
    rw [h1, h2, ← ENNReal.ofReal_add (by linarith) (mul_nonneg (by linarith) hε),
      ← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ 2*C₀+1)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [hC₀pos, hε])
  have hgoal : (A * Hu + A * Hu) + A * (ENNReal.ofReal ε * Hu)
      ≤ ENNReal.ofReal (2*C₀+1) * (ENNReal.ofReal (1+ε) * Hu) := by
    calc (A * Hu + A * Hu) + A * (ENNReal.ofReal ε * Hu)
        = ((A + A) + A * ENNReal.ofReal ε) * Hu := by
          rw [add_mul, mul_assoc, add_mul]
      _ ≤ (ENNReal.ofReal (2*C₀+1) * ENNReal.ofReal (1+ε)) * Hu :=
          mul_le_mul hkey le_rfl bot_le bot_le
      _ = ENNReal.ofReal (2*C₀+1) * (ENNReal.ofReal (1+ε) * Hu) := by rw [mul_assoc]
  simpa only [hA, hHu] using hgoal



/-- The Leibniz rule for `∂̄_{J_std+A}`. -/
lemma dbarCn_mul_leibniz {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n} {χ : Cn n → ℝ}
    {u : Cn n → ℂ} {z : Cn n}
    (hχ : DifferentiableAt ℝ (fun w => (χ w : ℂ)) z) (hu : DifferentiableAt ℝ u z)
    (j : Fin n) :
    dbarCn (JstdCn n + A) (fun w => (χ w : ℂ) * u w) z (Pi.single j 1)
      = (χ z : ℂ) * (dbarCn (JstdCn n + A) u z (Pi.single j 1))
        + u z * (dbarCn (JstdCn n + A) (fun w => (χ w : ℂ)) z (Pi.single j 1)) := by
  have hmul : fderiv ℝ (fun w => (χ w : ℂ) * u w) z
      = (χ z : ℂ) • fderiv ℝ u z + u z • fderiv ℝ (fun w => (χ w : ℂ)) z :=
    fderiv_fun_mul hχ hu
  rw [dbarCn_apply, dbarCn_apply, dbarCn_apply, hmul]
  simp only [add_apply, smul_apply, map_add]
  ring

/-- The `C^{0,α}`-seminorm of a bounded function with a bounded derivative. -/
lemma hSN_zero_le_of_deriv_bound {α M Z : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hM : 0 ≤ M) (hZ : 0 ≤ Z)
    {χ : (Fin n → ℂ) → ℂ} {Ω : Set (Fin n → ℂ)}
    (hdiff : ∀ z, DifferentiableAt ℝ χ z)
    (hdsup : ∀ x, ‖fderiv ℝ χ x‖ ≤ M)
    (hsup : ∀ x, ‖χ x‖ ≤ Z) :
    Work.CR.Flat.Holder.hSN 0 α χ Ω ≤ ENNReal.ofReal (max (2 * Z) M) := by
  rw [Work.CR.Flat.Holder.hSN_zero_deriv]
  refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
  have hxypos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hd : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hxypos α
  have hmvt : ‖χ x - χ y‖ ≤ M * ‖x - y‖ := by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := χ) (s := Set.univ)
      (fun z _ => hdiff z) (fun z _ => hdsup z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
    simpa [norm_sub_rev] using h
  rcases lt_or_ge ‖x - y‖ 1 with h1 | h1
  · have h3 : ‖x - y‖ ^ (1 - α) ≤ 1 :=
      Real.rpow_le_one hxypos.le (le_of_lt h1) (by linarith)
    have h4 : M * ‖x - y‖ / ‖x - y‖ ^ α = M * ‖x - y‖ ^ (1 - α) := by
      rw [mul_div_assoc, Real.rpow_sub hxypos (1:ℝ) α, Real.rpow_one]
    calc ENNReal.ofReal (‖χ x - χ y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal (M * ‖x - y‖ / ‖x - y‖ ^ α) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hmvt hd.le)
      _ = ENNReal.ofReal (M * ‖x - y‖ ^ (1 - α)) := by rw [h4]
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hM h3)
      _ ≤ ENNReal.ofReal (max (2 * Z) M) := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  · have h2 : ‖χ x - χ y‖ ≤ 2 * Z := by
      have hx := hsup x; have hy := hsup y
      calc ‖χ x - χ y‖ ≤ ‖χ x‖ + ‖χ y‖ := norm_sub_le _ _
        _ ≤ 2 * Z := by linarith
    have h3 : (1:ℝ) ≤ ‖x - y‖ ^ α := by
      have h := Real.one_le_rpow h1 hα0.le
      simpa using h
    calc ENNReal.ofReal (‖χ x - χ y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal (2 * Z / ‖x - y‖ ^ α) :=
          ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h2 hd.le)
      _ ≤ ENNReal.ofReal (2 * Z) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_le_iff₀ hd]
          nlinarith [h3, hZ]
      _ ≤ ENNReal.ofReal (max (2 * Z) M) := ENNReal.ofReal_le_ofReal (le_max_left _ _)



/-! ## 3. ENNReal form of the sup bound -/

lemma iDN_zero_le_sup {u : Cn n → ℂ} {S T : Set (Cn n)} (hST : S ⊆ T) :
    Work.CR.Flat.Holder.iDN 0 u S ≤ ⨆ z ∈ T, ENNReal.ofReal ‖u z‖ := by
  rw [Work.CR.Flat.Holder.iDN_zero_deriv]
  exact iSup₂_le fun z hz => le_iSup₂_of_le z (hST hz) le_rfl

lemma holderNorm_zero_le_self {α : ℝ} {u : Cn n → ℂ} {S : Set (Cn n)} :
    Work.CR.Flat.holderNorm 0 α u S
      = Work.CR.Flat.Holder.iDN 0 u S + Work.CR.Flat.Holder.hSN 0 α u S := by
  rw [Work.CR.Flat.Holder.iDN_complex_eq, Work.CR.Flat.Holder.hSN_complex_eq,
    Work.CR.Flat.holderNorm, Finset.range_one, Finset.sum_singleton]


end

end Work.NN.Core.Lev
