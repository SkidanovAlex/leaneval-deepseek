import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.CS.highSlot_bound_of_pos
import Submission.Work.BoseFixB3.CS.highSlot_sq_le_of_nonpos
import Submission.Work.BoseFixB3.CS.highSlot_stronglyMeasurable
import Submission.Work.BoseFixB3.Conv.conv3_chiScale_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Conv.abox_peel_pair`

The **pair peel** of FS's convolution step (`lem:Convolution`, `final_v2.tex` ~l. 845): the
pair integrand `χ_Λ(x_i) f(x_i − x_j) χ_Λ(x_j)` is replaced, inside the `n`-particle box
integral, by `χ_Λ(x_j) (f ⋆ χ_Λ)(x_j)` divided by `ℓ³`.  The weight multiplying the pair
kernel — `highSlot fc κ ℓ j (P_iΦ) · P_j P_i Φ` — is *independent of the slot-`i`
coordinate* (both factors are: `P_i` averages over the slot `i`, and `highSlot`/`lowMult`
only see the slot-`j` fibre), which is exactly what makes the peel possible: the `x_i`
integral of the left-hand integrand collapses onto the one-variable identity

  `∫_{acube ℓ} χ_Λ(y) f(y − z) dy = (f ⋆ χ_Λ)(z)`

(`Work.BoseFixB3.Conv.conv3_chiScale_peel`), obtained from the support of `χ_Λ` inside the
cube and the evenness of `f`.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real

namespace Work.BoseFixB3.Conv

open Submission.BoseGases
open Work.BoseBoxFix

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-! ## 1. `highSlot` of a function independent of the distinguished slot -/

/-- If `Ψ` is invariant under changes of the slot-`i` coordinate and `i ≠ j`, then
`highSlot fc κ ℓ j Ψ` is invariant as well: both `Ψ` itself and the slot-`j` fibre
`w ↦ Ψ(xⱼ←w)` (hence `lowSlot`, hence `highSlot`) are unchanged. -/
lemma highSlot_update_eq {fc : LowCut} {κ ℓ : ℝ} {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Ψ : X n → ℝ} (hΨinv : ∀ (x : X n) (z : E3), Ψ (Function.update x i z) = Ψ x)
    (x : X n) (z : E3) :
    highSlot fc κ ℓ j Ψ (Function.update x i z) = highSlot fc κ ℓ j Ψ x := by
  have h2 : lowSlot fc κ ℓ j Ψ (Function.update x i z) = lowSlot fc κ ℓ j Ψ x := by
    simp only [lowSlot]
    have hfun : (fun w : E3 => Ψ (Function.update (Function.update x i z) j w))
        = (fun w : E3 => Ψ (Function.update x j w)) := by
      funext w
      rw [Function.update_comm hij z w x]
      exact hΨinv (Function.update x j w) z
    rw [hfun, Function.update_of_ne (Ne.symm hij) z x]
  simp only [highSlot]
  rw [h2, hΨinv x z]


/-! ## 1b. Integrability of `x ↦ f (x i − x j)` on the box -/

/-- The centred boxes are monotone in the side length. -/
private lemma abox_subset_abox_of_le {n : ℕ} {ℓ ℓ' : ℝ} (h : ℓ ≤ ℓ') :
    Submission.BoseGases.abox n ℓ ⊆ Submission.BoseGases.abox n ℓ' := by
  intro x hx i
  have hxi : x i ∈ Submission.BoseGases.acube ℓ := hx i
  rw [Submission.BoseGases.mem_acube_iff] at hxi
  rw [Submission.BoseGases.mem_acube_iff]
  intro m
  obtain ⟨h1, h2⟩ := hxi m
  exact ⟨by linarith, by linarith⟩

/-- If `v =ᵐ w` on `ℝ³` then `x ↦ v (x i − x j)` and `x ↦ w (x i − x j)` agree a.e. on the
`n`-particle box (the subtraction profile of a null set is null, `abox_null_preimage_pair`). -/
private lemma abox_ae_pair_of_ae {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v w : E3 → ℝ}
    (hvw : v =ᵐ[volume] w) (i j : Fin n) (hij : i ≠ j) :
    (fun x : Submission.BoseGases.X n => v (x i - x j))
      =ᵐ[volume.restrict (Submission.BoseGases.abox n ℓ)]
      (fun x : Submission.BoseGases.X n => w (x i - x j)) := by
  have hN : volume {y : E3 | v y ≠ w y} = 0 := by
    rw [← ae_iff]
    exact hvw
  rcases exists_measurable_superset_of_null (μ := (volume : Measure E3)) hN with
    ⟨t, hNt, htm, ht0⟩
  have hpre : (volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ) {x : Submission.BoseGases.X n | x i - x j ∈ t} = 0 :=
    Submission.BoseGases.abox_null_preimage_pair hℓ htm ht0 i j hij
  have hfail : (volume : Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ)
      {x : Submission.BoseGases.X n | v (x i - x j) ≠ w (x i - x j)} = 0 := by
    exact measure_mono_null (fun x hx => hNt hx) hpre
  rw [show ((fun x : Submission.BoseGases.X n => v (x i - x j))
        =ᵐ[volume.restrict (Submission.BoseGases.abox n ℓ)]
        (fun x : Submission.BoseGases.X n => w (x i - x j)))
      ↔ {x : Submission.BoseGases.X n | v (x i - x j) = w (x i - x j)}
          ∈ ae (volume.restrict (Submission.BoseGases.abox n ℓ)) from Iff.rfl]
  rw [mem_ae_iff,
    show ({x : Submission.BoseGases.X n | v (x i - x j) = w (x i - x j)})ᶜ
      = {x : Submission.BoseGases.X n | v (x i - x j) ≠ w (x i - x j)} by
        ext x; simp]
  exact hfail

/-- `x ↦ f (x i − x j)` is integrable on the `n`-particle box for `f ∈ L¹(ℝ³)`. -/
private lemma integrableOn_sub_coord_abox {n : ℕ} {ℓ : ℝ} {i j : Fin n} (hij : i ≠ j)
    {f : E3 → ℝ} (hf : MeasureTheory.Integrable f) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => f (x i - x j))
      (Submission.BoseGases.abox n ℓ) volume := by
  have hmain : ∀ {ℓ' : ℝ}, 0 < ℓ' → MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => f (x i - x j)) (Submission.BoseGases.abox n ℓ') volume := by
    intro ℓ' hℓ'
    set w : E3 → ℝ := hf.aemeasurable.mk with hw
    have hwm : Measurable w := hf.aemeasurable.measurable_mk
    have hwae : f =ᵐ[volume] w := hf.aemeasurable.ae_eq_mk
    have hwInt : MeasureTheory.Integrable w := hf.congr hwae
    have hwa : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => |w (x i - x j)|)
        (volume.restrict (Submission.BoseGases.abox n ℓ')) :=
      Submission.BoseGases.integrableOn_abs_sub_abox hℓ' hwInt i j hij
    have hwaesm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n => w (x i - x j))
        (volume.restrict (Submission.BoseGases.abox n ℓ')) :=
      (hwm.comp (by fun_prop : Measurable fun x : Submission.BoseGases.X n => x i - x j)).aestronglyMeasurable
    have hwsub : MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => w (x i - x j))
        (volume.restrict (Submission.BoseGases.abox n ℓ')) := by
      refine hwa.mono' hwaesm ?_
      filter_upwards with x
      rw [Real.norm_eq_abs]
    have hae := abox_ae_pair_of_ae hℓ' hwae i j hij
    exact hwsub.congr hae.symm
  by_cases hℓ : 0 < ℓ
  · exact hmain hℓ
  · exact (hmain one_pos).mono_set
      (abox_subset_abox_of_le (le_trans (le_of_not_gt hℓ) (by norm_num)))

/-! ## 2. The pair peel -/

theorem abox_peel_pair {n : ℕ} {ℓ κ : ℝ} (fc : Work.BoseBoxFix.LowCut) (hℓ : 0 < ℓ)
    {i j : Fin n} (hij : i ≠ j) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : MeasureTheory.Integrable f)
    (hfeven : ∀ x : EuclideanSpace ℝ (Fin 3), f (-x) = f x) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
          * (Submission.BoseGases.chiScale ℓ (x i) * f (x i - x j) * Submission.BoseGases.chiScale ℓ (x j)))
      = (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseFixB3.highSlot fc κ ℓ j (Submission.BoseGases.aP ℓ i Φ) x
            * Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
            * (Submission.BoseGases.chiScale ℓ (x j)
                * Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) (x j)) := by
  -- A box needs at least one particle
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fin.pos i))
  -- Notations
  set Ψ : X (m + 1) → ℝ := Submission.BoseGases.aP ℓ i Φ with hΨ
  have hΨc : Continuous Ψ := by rw [hΨ]; exact Submission.BoseGases.aP_continuous hℓ i hΦ
  set H : X (m + 1) → ℝ := fun x => Work.BoseFixB3.highSlot fc κ ℓ j Ψ x * Submission.BoseGases.aP ℓ j Ψ x
    with hH
  set G₁ : X (m + 1) → ℝ := fun x =>
    Submission.BoseGases.chiScale ℓ (x i) * f (x i - x j) * Submission.BoseGases.chiScale ℓ (x j)
    with hG₁
  set G₂ : X (m + 1) → ℝ := fun x => Submission.BoseGases.chiScale ℓ (x j)
    * Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) (x j) with hG₂
  change (∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x * G₁ x)
    = (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x * G₂ x
  -- Index bookkeeping: `j` is the image of some `k : Fin m` under `i.succAbove`
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
  have hcoord : ∀ (y : E3) (r : X m), (Submission.BoseGases.kcInsN m i (y, r)) j = r k := by
    intro y r
    rw [← hk]
    exact Submission.BoseGases.kc_insN_apply_succ m i y r k
  have hcoord0 : ∀ r : X m, (Submission.BoseGases.kcInsN m i (0, r)) j = r k := fun r => hcoord 0 r
  -- Invariance of `H` and of `G₂` in the slot `i`
  have hHinv : ∀ (x : X (m + 1)) (z : E3), H (Function.update x i z) = H x := by
    intro x z
    have h1 : Work.BoseFixB3.highSlot fc κ ℓ j Ψ (Function.update x i z)
        = Work.BoseFixB3.highSlot fc κ ℓ j Ψ x :=
      highSlot_update_eq (Ψ := Ψ) hij
        (fun x z => Submission.BoseGases.aP_const_in_coord hℓ i hΦ x z) x z
    have h2 : Submission.BoseGases.aP ℓ j Ψ (Function.update x i z)
        = Submission.BoseGases.aP ℓ j Ψ x :=
      Submission.BoseGases.aP_pair_const_in_j (ℓ := ℓ) hℓ (i := j) (j := i) (Ne.symm hij) hΦ x z
    rw [hH]
    simp only
    rw [h1, h2]
  have hHins : ∀ (y : E3) (r : X m),
      H (Submission.BoseGases.kcInsN m i (y, r)) = H (Submission.BoseGases.kcInsN m i (0, r)) := by
    intro y r
    rw [Submission.BoseGases.kcInsN_update_zero i y r]
    exact hHinv (Submission.BoseGases.kcInsN m i (0, r)) y
  have hG₂ins : ∀ (y : E3) (r : X m),
      G₂ (Submission.BoseGases.kcInsN m i (y, r)) = G₂ (Submission.BoseGases.kcInsN m i (0, r)) := by
    intro y r
    simp only [hG₂]
    rw [Submission.BoseGases.kc_insN_other_indep m i y 0 r j (Ne.symm hij),
      Submission.BoseGases.kc_insN_other_indep m i 0 0 r j (Ne.symm hij)]
  -- The peel at the slot `i`
  set μ' : Measure E3 := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ) with hμ'
  set ν : Measure (X m) := (volume : Measure (X m)).restrict (Submission.BoseGases.abox m ℓ) with hν
  have hmp : MeasurePreserving (⇑(Submission.BoseGases.kcInsN m i)) (μ'.prod ν)
      ((volume : Measure (X (m + 1))).restrict (Submission.BoseGases.abox (m + 1) ℓ)) := by
    have h := MeasurePreserving.symm
      (e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E3) i)
      (Submission.BoseGases.abox_peel_mp m ℓ i)
    simpa [Submission.BoseGases.kcInsN, hμ', hν] using h
  have hpeel : ∀ F : X (m + 1) → ℝ, (∫ x in Submission.BoseGases.abox (m + 1) ℓ, F x)
      = ∫ p : E3 × X m, F (Submission.BoseGases.kcInsN m i p) ∂(μ'.prod ν) := by
    intro F
    exact (hmp.integral_comp' F).symm
  -- A uniform bound for `Ψ` and for `P_jΨ` on the box
  obtain ⟨C₀, hC₀⟩ :=
    (Work.UBBInputs9.B.abox_isCompact (m + 1) ℓ).exists_bound_of_continuousOn hΨc.continuousOn
  set M : ℝ := max C₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hΨb : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |Ψ x| ≤ M := by
    intro x hx
    have h := hC₀ x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  have haPb : ∀ x ∈ Submission.BoseGases.abox (m + 1) ℓ, |Submission.BoseGases.aP ℓ j Ψ x| ≤ M :=
    Submission.BoseGases.aP_abs_le hℓ j hΨc hM0 hΨb
  -- The a.e. bound on `highSlot` (the two signs of `κ`)
  have hhs : ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ x ∂((volume : Measure (X (m + 1))).restrict
      (Submission.BoseGases.abox (m + 1) ℓ)),
      |Work.BoseFixB3.highSlot fc κ ℓ j Ψ x| ≤ K := by
    by_cases hκ : 0 < κ
    · obtain ⟨C, hC0, hC⟩ := Work.BoseFixB3.CS.highSlot_bound_of_pos (fc := fc) hκ hℓ j hΨc
      exact ⟨C, hC0, (ae_restrict_iff' (Submission.BoseGases.abox_measurable (m + 1) ℓ)).mpr
        (ae_of_all _ (fun x hx => hC x hx))⟩
    · have h := Work.BoseFixB3.CS.highSlot_sq_le_of_nonpos (fc := fc) (κ := κ) (ℓ := ℓ)
        (le_of_not_gt hκ) j hΨc
      refine ⟨2 * M, by positivity, ?_⟩
      filter_upwards [h, self_mem_ae_restrict (Submission.BoseGases.abox_measurable (m + 1) ℓ)]
        with x hx hxmem
      have hΨM : (Ψ x) ^ 2 ≤ M ^ 2 := by
        have h1 : |Ψ x| ≤ M := hΨb x hxmem
        calc (Ψ x) ^ 2 = |Ψ x| ^ 2 := (sq_abs _).symm
          _ ≤ |M| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (by simpa [abs_of_nonneg hM0] using h1) 2
          _ = M ^ 2 := by rw [abs_of_nonneg hM0]
      have hsq : |Work.BoseFixB3.highSlot fc κ ℓ j Ψ x| ^ 2 ≤ (2 * M) ^ 2 := by
        calc |Work.BoseFixB3.highSlot fc κ ℓ j Ψ x| ^ 2
            = (Work.BoseFixB3.highSlot fc κ ℓ j Ψ x) ^ 2 := by rw [sq_abs]
          _ ≤ 4 * (Ψ x) ^ 2 := hx
          _ ≤ 4 * M ^ 2 := by linarith
          _ = (2 * M) ^ 2 := by ring
      have h2M0 : (0 : ℝ) ≤ 2 * M := by positivity
      have hfin := sq_le_sq.mp hsq
      rw [abs_of_nonneg h2M0] at hfin
      simpa using hfin
  obtain ⟨K, hK0, hK⟩ := hhs
  -- A.e. bound on `H`
  have hHK : ∀ᵐ x ∂((volume : Measure (X (m + 1))).restrict
      (Submission.BoseGases.abox (m + 1) ℓ)), |H x| ≤ K * M := by
    filter_upwards [hK, self_mem_ae_restrict (Submission.BoseGases.abox_measurable (m + 1) ℓ)]
      with x hx hxmem
    have haP := haPb x hxmem
    have h1 : H x = Work.BoseFixB3.highSlot fc κ ℓ j Ψ x * Submission.BoseGases.aP ℓ j Ψ x := by
      rw [hH]
    rw [h1, abs_mul]
    exact mul_le_mul hx haP (abs_nonneg _) hK0
  -- Integrability of `G₁` and of `H * G₁` on the box
  have hfsub : IntegrableOn (fun x : X (m + 1) => f (x i - x j))
      (Submission.BoseGases.abox (m + 1) ℓ) volume :=
    integrableOn_sub_coord_abox hij hf
  have hchi_ae : AEStronglyMeasurable
      (fun x : X (m + 1) => Submission.BoseGases.chiScale ℓ (x i) * Submission.BoseGases.chiScale ℓ (x j))
      (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) :=
    (((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)).mul
      ((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply j))).aestronglyMeasurable
  have hchi_bdd : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)),
      ‖Submission.BoseGases.chiScale ℓ (x i) * Submission.BoseGases.chiScale ℓ (x j)‖
        ≤ ((Real.sqrt Submission.BoseGases.chiNormSq)⁻¹) ^ 2 := by
    refine ae_of_all _ (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have hc : (0 : ℝ) ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    calc |Submission.BoseGases.chiScale ℓ (x i)| * |Submission.BoseGases.chiScale ℓ (x j)|
        ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
          * (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ :=
          mul_le_mul (Submission.BoseGases.abs_chiScale_le ℓ (x i))
            (Submission.BoseGases.abs_chiScale_le ℓ (x j)) (abs_nonneg _) hc
      _ = ((Real.sqrt Submission.BoseGases.chiNormSq)⁻¹) ^ 2 := by ring
  have hG₁int : Integrable (fun x : X (m + 1) => G₁ x)
      (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) := by
    rw [hG₁]
    have h := hfsub.mul_bdd hchi_ae hchi_bdd
    simpa only [Pi.mul_apply, mul_assoc, mul_comm, mul_left_comm] using h
  have hHae : AEStronglyMeasurable H (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) := by
    rw [hH]
    exact (StronglyMeasurable.mul
      (Work.BoseFixB3.CS.highSlot_stronglyMeasurable (fc := fc) (κ := κ) (ℓ := ℓ) j hΨc)
      (Submission.BoseGases.aP_continuous hℓ j hΨc).stronglyMeasurable).aestronglyMeasurable
  have hFG : Integrable (fun x : X (m + 1) => H x * G₁ x)
      (volume.restrict (Submission.BoseGases.abox (m + 1) ℓ)) := by
    refine Integrable.mono' ((hG₁int.norm).const_mul (K * M)) (hHae.mul hG₁int.aestronglyMeasurable) ?_
    filter_upwards [hHK] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hFGint : Integrable (fun p : E3 × X m =>
      H (Submission.BoseGases.kcInsN m i p) * G₁ (Submission.BoseGases.kcInsN m i p)) (μ'.prod ν) :=
    (hmp.integrable_comp (g := fun x => H x * G₁ x) (hHae.mul hG₁int.aestronglyMeasurable)).mpr hFG
  -- The peeled form of the left-hand side
  have hkey : (∫ p : E3 × X m,
        H (Submission.BoseGases.kcInsN m i p) * G₁ (Submission.BoseGases.kcInsN m i p) ∂(μ'.prod ν))
      = ∫ r : X m, H (Submission.BoseGases.kcInsN m i (0, r)) * G₂ (Submission.BoseGases.kcInsN m i (0, r)) ∂ν := by
    rw [MeasureTheory.integral_prod_symm _ hFGint]
    apply integral_congr_ae
    filter_upwards with r
    have hinner : (∫ y : E3, H (Submission.BoseGases.kcInsN m i (y, r))
          * G₁ (Submission.BoseGases.kcInsN m i (y, r)) ∂μ')
        = H (Submission.BoseGases.kcInsN m i (0, r)) * G₂ (Submission.BoseGases.kcInsN m i (0, r)) := by
      have h1 : (∫ y : E3, H (Submission.BoseGases.kcInsN m i (y, r))
            * G₁ (Submission.BoseGases.kcInsN m i (y, r)) ∂μ')
          = ∫ y : E3, H (Submission.BoseGases.kcInsN m i (0, r))
            * G₁ (Submission.BoseGases.kcInsN m i (y, r)) ∂μ' := by
        apply integral_congr_ae
        filter_upwards with y
        rw [hHins y r]
      rw [h1, MeasureTheory.integral_const_mul]
      congr 1
      -- the one-variable identity, on the fibre
      have hG₁eq : ∀ y : E3, G₁ (Submission.BoseGases.kcInsN m i (y, r))
          = Submission.BoseGases.chiScale ℓ y * f (y - r k) * Submission.BoseGases.chiScale ℓ (r k) := by
        intro y
        simp only [hG₁, Submission.BoseGases.kc_insN_apply_same m i y r, hcoord y r]
      have hstep : (∫ y : E3, Submission.BoseGases.chiScale ℓ y * f (y - r k)
            * Submission.BoseGases.chiScale ℓ (r k) ∂μ')
          = Submission.BoseGases.chiScale ℓ (r k)
            * Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) (r k) := by
        rw [MeasureTheory.integral_mul_const, conv3_chiScale_peel hℓ hf hfeven (r k), mul_comm]
      calc (∫ y : E3, G₁ (Submission.BoseGases.kcInsN m i (y, r)) ∂μ')
          = ∫ y : E3, Submission.BoseGases.chiScale ℓ y * f (y - r k)
              * Submission.BoseGases.chiScale ℓ (r k) ∂μ' := by
            apply integral_congr_ae
            filter_upwards with y
            exact hG₁eq y
        _ = Submission.BoseGases.chiScale ℓ (r k)
              * Submission.BoseGases.conv3 f (fun z => Submission.BoseGases.chi ((ℓ⁻¹) • z)) (r k) := hstep
        _ = G₂ (Submission.BoseGases.kcInsN m i (0, r)) := by
            simp only [hG₂, hcoord0 r]
    rw [hinner]
  -- The peeled form of the right-hand side
  have hrhs : (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x * G₂ x
      = ∫ r : X m, H (Submission.BoseGases.kcInsN m i (0, r))
          * G₂ (Submission.BoseGases.kcInsN m i (0, r)) ∂ν := by
    rw [hpeel (fun x => H x * G₂ x)]
    have h1 : (∫ p : E3 × X m, H (Submission.BoseGases.kcInsN m i p)
          * G₂ (Submission.BoseGases.kcInsN m i p) ∂(μ'.prod ν))
        = ∫ p : E3 × X m, H (Submission.BoseGases.kcInsN m i (0, p.2))
          * G₂ (Submission.BoseGases.kcInsN m i (0, p.2)) ∂(μ'.prod ν) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hHins p.1 p.2, hG₂ins p.1 p.2]
    rw [h1]
    have h2 : (∫ p : E3 × X m, H (Submission.BoseGases.kcInsN m i (0, p.2))
          * G₂ (Submission.BoseGases.kcInsN m i (0, p.2)) ∂(μ'.prod ν))
        = ∫ p : E3 × X m, (1 : ℝ) * (H (Submission.BoseGases.kcInsN m i (0, p.2))
          * G₂ (Submission.BoseGases.kcInsN m i (0, p.2))) ∂(μ'.prod ν) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [one_mul]
    rw [h2]
    have hprod := MeasureTheory.integral_prod_mul (μ := μ') (ν := ν)
      (f := fun _ : E3 => (1 : ℝ))
      (g := fun r : X m => H (Submission.BoseGases.kcInsN m i (0, r))
        * G₂ (Submission.BoseGases.kcInsN m i (0, r)))
    rw [hprod]
    rw [show (∫ y : E3, (1 : ℝ) ∂μ') = ℓ ^ 3 from by
      rw [show (∫ y : E3, (1 : ℝ) ∂μ') = ∫ y in Submission.BoseGases.acube ℓ, (1 : ℝ) from rfl,
        Submission.BoseGases.integral_const_acube ℓ hℓ 1]
      ring]
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (ℓ : ℝ) ^ 3 ≠ 0), one_mul]
  rw [hpeel (fun x => H x * G₁ x), hrhs]
  exact hkey

end Work.BoseFixB3.Conv
