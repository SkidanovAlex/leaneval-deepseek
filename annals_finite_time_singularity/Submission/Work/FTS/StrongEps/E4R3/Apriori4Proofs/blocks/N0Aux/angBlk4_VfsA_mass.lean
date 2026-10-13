import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4SepDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMass
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMassDefs
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.c2mJets
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.vfs4_VfsA2_jet
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.vfs4_A1_slot4
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.vfs4_maj_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux (AngBlk4 AngBlk4_eq_angMaj_add AngBlk4_nonneg)
open Work.FTS.StrongPersist.L3Rhs (VfsA1 VfsA2 VfsGc VfsJetMaj VfsJetMajMass angMaj
  angMaj_VfsA1_le angMaj_VfsA2_le measurable_VfsGc measurable_VfsJetMaj measurable_angMaj
  measurable_dthU_iter sin_two_pos_Ioo)
open Work.FTS.StrongPersist.H6Pair6Aux.T5bAux (c2mJets)

/-! ## Elementary exponent arithmetic

`Γ(θ)² sin(2θ)^{-γ(α)} ≤ sin(2θ)^{-(1-17α/30)}`: the exponent `1 - 17α/30` is exactly what is
left of `2α/3 - γ(α)` after the `Γ(θ)² ≤ sin(2θ)^{2α/3}` of `Coercivity.Gam_sq_le_sin_two`
is spent. -/

private lemma gam_sq_mul_rpow_le {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
  have hsp : 0 < Real.sin (2 * θ) := sin_two_pos_Ioo hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := hsp.le
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hG := Work.Coercivity.Gam_sq_le_sin_two α hα θ hθI
  have hexp : 2 * α / 3 + -(Work.Spaces.gam α) = -(1 - 17 * α / 30) := by
    rw [Work.Spaces.gam]; ring
  calc (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (2 * α / 3) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_right hG (Real.rpow_nonneg hs0 _)
    _ = (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
        rw [← Real.rpow_add hsp (2 * α / 3) (-(Work.Spaces.gam α)), hexp]

/-! ## The jets of `Γ/c`

Every `dthU`-jet of `Γ/c` of order at most four is dominated by `10⁶·Γ`: the angular jet bound
`|dthU^m Γ| ≤ 10⁵·Γ` (`LocData6.DthIter_Gam_abs_le6`, via `LocData.DthIter_rad_eq`) and
`1/c ≤ 10` (`Spaces.c_bounds`). -/

private lemma gamGc_jet {m : ℕ} (hm : m ≤ 4) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[m] (VfsGc α) θ| ≤ 10 ^ 6 * Work.Spaces.Gam α θ := by
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hfe : VfsGc α = fun θ' : ℝ => (1 / Work.Spaces.c α) * Work.Spaces.Gam α θ' := by
    funext θ'
    rw [VfsGc]
    ring
  rw [hfe, Work.Spaces.dthU_iter_const_mul]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Work.Spaces.c α)]
  have hjet : |Work.Spaces.dthU^[m] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
    have hkey := Work.FTS.LocData6.DthIter_Gam_abs_le6 m (by omega) α hα hα1 hθ
    rwa [Work.FTS.LocData.DthIter_rad_eq m (fun t : ℝ => Work.Spaces.Gam α t) 0 θ] at hkey
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hinv : 1 / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hcpos]
    linarith
  calc (1 / Work.Spaces.c α)
        * |Work.Spaces.dthU^[m] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ (1 / Work.Spaces.c α) * (100000 * Work.Spaces.Gam α θ) :=
        mul_le_mul_of_nonneg_left hjet (by positivity)
    _ ≤ 10 * (100000 * Work.Spaces.Gam α θ) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = 10 ^ 6 * Work.Spaces.Gam α θ := by ring

/-! ## Measurability -/

private lemma measurable_VfsA1' (α : ℝ) : Measurable (VfsA1 α) := by
  have hX : Measurable (VfsGc α) := measurable_VfsGc α
  show Measurable (fun θ : ℝ => (3 / 2) * Work.Spaces.dthU (VfsGc α) θ)
  exact measurable_const.mul (measurable_dthU_iter _ hX 1)

private lemma measurable_VfsA2' (α : ℝ) : Measurable (VfsA2 α) := by
  have hX : Measurable (VfsGc α) := measurable_VfsGc α
  have hc2 : Measurable Work.Construction.c2m := by
    rw [show Work.Construction.c2m
        = fun θ : ℝ => Real.cos (2 * θ) - Real.sin θ ^ 2 from
      funext (fun θ => Work.Construction.c2m_eq θ)]
    fun_prop
  show Measurable (fun θ : ℝ => -α * Work.Construction.c2m θ * VfsGc α θ)
  exact (measurable_const.mul hc2).mul hX

private lemma measurable_AngBlk4' (α : ℝ) {C : ℝ → ℝ} (hC : Measurable C) :
    Measurable (AngBlk4 α C) := by
  have h1 : Measurable (fun θ : ℝ => angMaj α C θ) := measurable_angMaj α C hC
  have h2 : Measurable (fun θ : ℝ =>
      (Work.Spaces.dthU^[4] C θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
    ((measurable_dthU_iter C hC 4).pow_const 2).mul (by fun_prop)
  rw [funext (fun θ => AngBlk4_eq_angMaj_add α C θ)]
  exact h1.add h2

/-! ## From the open quadrant to `Iθ` a.e. -/

private lemma angBlk4_ae_le {α : ℝ} {C M : ℝ → ℝ} (hC : Measurable C) (hM : Measurable M)
    (hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), AngBlk4 α C θ ≤ M θ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), AngBlk4 α C θ ≤ M θ := by
  have hAmeas : MeasurableSet {θ : ℝ | ¬ (AngBlk4 α C θ ≤ M θ)} := by
    have heq : {θ : ℝ | ¬ (AngBlk4 α C θ ≤ M θ)}
        = {θ : ℝ | M θ < AngBlk4 α C θ} := by
      ext θ
      exact not_le
    rw [heq]
    exact measurableSet_lt hM (measurable_AngBlk4' α hC)
  rw [MeasureTheory.ae_iff, MeasureTheory.Measure.restrict_apply hAmeas]
  refine MeasureTheory.measure_mono_null ?_
    (((Set.finite_singleton (Real.pi / 2)).insert (0 : ℝ)).measure_zero volume)
  intro θ hθ
  rw [Set.mem_inter_iff] at hθ
  obtain ⟨hneg, hIθ⟩ := hθ
  by_contra hcon
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hcon
  push Not at hcon
  exact hneg (hpt θ ⟨lt_of_le_of_ne hIθ.1 (Ne.symm hcon.1),
    lt_of_le_of_ne hIθ.2 hcon.2⟩)

/-! ## Integrability and the integral bound from a pointwise majorant -/

private lemma angBlk4_integral_le {α : ℝ} {C X : ℝ → ℝ} (hC : Measurable C) (hX : Measurable X)
    (hXint : Integrable X (volume.restrict Work.Spaces.Iθ))
    (hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), AngBlk4 α C θ ≤ X θ) :
    Integrable (AngBlk4 α C) (volume.restrict Work.Spaces.Iθ) ∧
      (∫ θ in Work.Spaces.Iθ, AngBlk4 α C θ) ≤ ∫ θ in Work.Spaces.Iθ, X θ := by
  have hae := angBlk4_ae_le hC hX hpt
  have hInt : Integrable (AngBlk4 α C) (volume.restrict Work.Spaces.Iθ) := by
    refine hXint.mono' (measurable_AngBlk4' α hC).aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc, hae] with θ hθ hle
    rw [Real.norm_of_nonneg (AngBlk4_nonneg (α := α) (C := C) hθ)]
    exact hle
  exact ⟨hInt, MeasureTheory.integral_mono_ae hInt hXint hae⟩

/-! ## The `VfsA1` half -/

private lemma massA1 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hslot : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      (Work.Spaces.dthU^[4] (VfsA1 α) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))) :
    MeasureTheory.IntegrableOn (AngBlk4 α (VfsA1 α)) Work.Spaces.Iθ ∧
      α * (∫ θ in Work.Spaces.Iθ, AngBlk4 α (VfsA1 α) θ) ≤ 10 ^ 17 := by
  obtain ⟨hVJMint, hVJMbd⟩ := VfsJetMajMass α hα hα1
  have hq0 : 0 < 1 - 17 * α / 30 := by linarith
  have hq1 : 1 - 17 * α / 30 < 1 := by linarith
  have hQ := Work.Coercivity.integral_sin_two_neg_rpow_le (1 - 17 * α / 30) hq0 hq1
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), AngBlk4 α (VfsA1 α) θ
      ≤ 9 * VfsJetMaj α θ + 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
    intro θ hθ
    have h1 := angMaj_VfsA1_le (α := α) hθ hα.le
    have h2 := hslot θ hθ
    rw [AngBlk4_eq_angMaj_add]
    linarith
  have hXmeas : Measurable (fun θ : ℝ => 9 * VfsJetMaj α θ
      + 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))) :=
    (measurable_VfsJetMaj α).const_mul 9 |>.add (by fun_prop)
  have hXint : Integrable (fun θ : ℝ => 9 * VfsJetMaj α θ
      + 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
      (volume.restrict Work.Spaces.Iθ) :=
    (hVJMint.const_mul 9).add (hQ.1.const_mul (2250000000000 : ℝ))
  obtain ⟨hInt, hIle⟩ := angBlk4_integral_le (measurable_VfsA1' α) hXmeas hXint hpt
  refine ⟨hInt, ?_⟩
  have hb : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
      ≤ 120 / (17 * α) := by
    have h := (vfs4_maj_integral (A := 0) (Bm := 1) (α := α)
      (by norm_num) (by norm_num) hα hα1).2
    simpa using h
  have hval : (∫ θ in Work.Spaces.Iθ, (9 * VfsJetMaj α θ
        + 2250000000000 * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))))
      ≤ 9 * 10 ^ 16 + 2250000000000 * (120 / (17 * α)) := by
    rw [MeasureTheory.integral_add (hVJMint.const_mul 9) (hQ.1.const_mul (2250000000000 : ℝ)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have h1 : (9 : ℝ) * (∫ θ in Work.Spaces.Iθ, VfsJetMaj α θ) ≤ 9 * 10 ^ 16 :=
      mul_le_mul_of_nonneg_left hVJMbd (by norm_num)
    have h2 : (2250000000000 : ℝ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
        ≤ 2250000000000 * (120 / (17 * α)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    linarith
  have hmid : α * (∫ θ in Work.Spaces.Iθ, AngBlk4 α (VfsA1 α) θ)
      ≤ α * (9 * 10 ^ 16 + 2250000000000 * (120 / (17 * α))) :=
    mul_le_mul_of_nonneg_left (le_trans hIle hval) hα.le
  have hkey : α * (2250000000000 * (120 / (17 * α))) = 2250000000000 * (120 / 17) := by
    have hαne : α ≠ 0 := ne_of_gt hα
    field_simp
  have hfin : α * (9 * 10 ^ 16 + 2250000000000 * (120 / (17 * α))) ≤ 10 ^ 17 := by
    have hA : α * (9 * 10 ^ 16) ≤ 9 * 10 ^ 16 := by
      have h0 : (0 : ℝ) ≤ 9 * 10 ^ 16 := by norm_num
      exact mul_le_of_le_one_left h0 hα1
    have hB : (2250000000000 : ℝ) * (120 / 17) ≤ 10 ^ 16 := by norm_num
    rw [mul_add, hkey]
    linarith
  exact le_trans hmid hfin

/-! ## The `VfsA2` half -/

private lemma massA2 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {B Cj : ℝ} (hB : 0 < B)
    (hCj : 0 < Cj)
    (hc2 : ∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ B)
    (hjet : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.dthU^[i] (VfsA2 α) θ|
        ≤ Cj * B * α
          * (|VfsGc α θ| + ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ|))
    (hΓ : ∀ m ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (VfsGc α) θ| ≤ 10 ^ 6 * Work.Spaces.Gam α θ) :
    MeasureTheory.IntegrableOn (AngBlk4 α (VfsA2 α)) Work.Spaces.Iθ ∧
      α * (∫ θ in Work.Spaces.Iθ, AngBlk4 α (VfsA2 α) θ)
        ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16
          + (Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17) := by
  obtain ⟨hVJMint, hVJMbd⟩ := VfsJetMajMass α hα hα1
  have hq0 : 0 < 1 - 17 * α / 30 := by linarith
  have hq1 : 1 - 17 * α / 30 < 1 := by linarith
  have hQ := Work.Coercivity.integral_sin_two_neg_rpow_le (1 - 17 * α / 30) hq0 hq1
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), AngBlk4 α (VfsA2 α) θ
      ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * VfsJetMaj α θ
        + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsp : 0 < Real.sin (2 * θ) := sin_two_pos_Ioo hθ
    have h1 := angMaj_VfsA2_le (α := α) hθ hα hα1 hB hCj
      (fun j hj => hc2 j hj θ hθI)
      (fun i hi1 hi3 => hjet i hi1 (by omega) θ hθ)
    have h2 : (Work.Spaces.dthU^[4] (VfsA2 α) θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by
      have hinner : |VfsGc α θ|
          + ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ|
          ≤ 5 * 10 ^ 6 * Work.Spaces.Gam α θ := by
        have h0 : |VfsGc α θ| ≤ 10 ^ 6 * Work.Spaces.Gam α θ := by
          simpa only [Function.iterate_zero, id_eq] using hΓ 0 (by norm_num) θ hθI
        have hs : ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ|
            ≤ 4 * (10 ^ 6 * Work.Spaces.Gam α θ) := by
          refine le_trans (Finset.sum_le_sum
            (fun m hm => hΓ m (Finset.mem_Icc.mp hm).2 θ hθI)) ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          norm_num
        linarith
      have hj4 := hjet 4 (by norm_num) (le_refl 4) θ hθ
      have h4 : |Work.Spaces.dthU^[4] (VfsA2 α) θ|
          ≤ Cj * B * α * (5 * 10 ^ 6 * Work.Spaces.Gam α θ) :=
        le_trans hj4 (mul_le_mul_of_nonneg_left hinner (by positivity))
      calc (Work.Spaces.dthU^[4] (VfsA2 α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          = |Work.Spaces.dthU^[4] (VfsA2 α) θ| ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by rw [sq_abs]
        _ ≤ (Cj * B * α * (5 * 10 ^ 6 * Work.Spaces.Gam α θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h4 2)
              (Real.rpow_nonneg hsp.le _)
        _ = (Cj * B * α * 5000000) ^ 2
            * ((Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
            ring
        _ ≤ (Cj * B * α * 5000000) ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) :=
            mul_le_mul_of_nonneg_left (gam_sq_mul_rpow_le hα hθ) (sq_nonneg _)
        _ = (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)) := by ring
    rw [AngBlk4_eq_angMaj_add]
    linarith
  have hXmeas : Measurable (fun θ : ℝ => 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * VfsJetMaj α θ
      + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
          * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))) :=
    (measurable_VfsJetMaj α).const_mul _ |>.add (by fun_prop)
  have hXint : Integrable (fun θ : ℝ => 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * VfsJetMaj α θ
      + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
          * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
      (volume.restrict Work.Spaces.Iθ) :=
    (hVJMint.const_mul _).add (hQ.1.const_mul _)
  obtain ⟨hInt, hIle⟩ := angBlk4_integral_le (measurable_VfsA2' α) hXmeas hXint hpt
  refine ⟨hInt, ?_⟩
  have hb : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
      ≤ 120 / (17 * α) := by
    have h := (vfs4_maj_integral (A := 0) (Bm := 1) (α := α)
      (by norm_num) (by norm_num) hα hα1).2
    simpa using h
  have hval : (∫ θ in Work.Spaces.Iθ, (100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * VfsJetMaj α θ
        + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30))))
      ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16
        + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / (17 * α)) := by
    rw [MeasureTheory.integral_add (hVJMint.const_mul _) (hQ.1.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have h1 : 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * (∫ θ in Work.Spaces.Iθ, VfsJetMaj α θ)
        ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16 :=
      mul_le_mul_of_nonneg_left hVJMbd (by positivity)
    have h2 : (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(1 - 17 * α / 30)))
        ≤ (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / (17 * α)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    linarith
  have hkey : α * ((Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / (17 * α)))
      = (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / 17) := by
    have hαne : α ≠ 0 := ne_of_gt hα
    field_simp
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
  have hA : α * (100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16)
      ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16 := by
    have h0 : (0 : ℝ) ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16 := by positivity
    exact mul_le_of_le_one_left h0 hα1
  have hBc : (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / 17)
      ≤ (Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17) := by
    have h0 : (0 : ℝ) ≤ (Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17) := by positivity
    calc (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / 17)
        = ((Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17)) * α ^ 2 := by ring
      _ ≤ ((Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17)) * 1 :=
          mul_le_mul_of_nonneg_left hα2 h0
      _ = (Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17) := by ring
  calc α * (∫ θ in Work.Spaces.Iθ, AngBlk4 α (VfsA2 α) θ)
      ≤ α * (100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16
          + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / (17 * α))) :=
        mul_le_mul_of_nonneg_left (le_trans hIle hval) hα.le
    _ = α * (100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16)
          + (Cj * 5000000) ^ 2 * B ^ 2 * α ^ 2 * (120 / 17) := by rw [mul_add, hkey]
    _ ≤ 100 * (B ^ 2 + Cj ^ 2 * B ^ 2) * 10 ^ 16
          + (Cj * 5000000) ^ 2 * B ^ 2 * (120 / 17) := add_le_add hA hBc

/-! ## The main theorem -/

-- `α`-uniform angular masses of the two angular profiles `VfsA1 α θ = (3/2)·dthU(Γ/c) θ`
-- and `VfsA2 α θ = -α·c2m θ·Γ(θ)/c(α)` of the separated star part `Vfs α`
-- (`Work.FTS.StrongPersist.L3Rhs.VfsA1`, `VfsA2`), for the level-four angular block
-- `AngBlk4 α C θ = (C θ)² sin(2θ)^{-η} + Σ_{1 ≤ i ≤ 4} (dthU^i C θ)² sin(2θ)^{-γ(α)}`
-- of `...blocks/N0Aux/B4SepDefs.lean`.
-- The integrals are `O(1/α)`, stated as `α · ∫ ≤ K` with an `α`-independent constant.
-- Route (crude is fine: the `α^{-1}` loss is later absorbed by `HkSq α 4 w ≤ C₀²α⁴`):
-- `LocData.DthIter_rad_eq` identifies `DthIter m (fun _ θ' => φ θ') z θ` with `dthU^[m] φ θ`;
-- `LocData6.DthIter_Gam_abs_le6` gives `|dthU^m Γ| ≤ 10^5·Γ` for `m ≤ 6`, `Gam_bounds` gives
-- `Γ ≤ 1` and `Coercivity.Gam_sq_le_sin_two` gives `Γ² ≤ sin(2θ)^{2α/3}`; with `c_bounds`
-- (`1/10 ≤ c ≤ 10`) and `Coercivity.integral_sin_two_neg_rpow_le` for the exponent
-- `q = 1 - 17α/30 ∈ (0,1)` (`∫_Iθ sin(2θ)^{-q} ≤ 4/(1-q) = 120/(17α)`) the `γ`-slots of
-- `VfsA1` are `≤ (10^5/c)²·Γ²·sin^{-γ} = (10^5/c)²·sin^{-q}`, and the `η`-slot is `≤ 10^6`
-- (`∫_Iθ sin(2θ)^{-η} ≤ 10^4`).  For `VfsA2` expand `dthU^i(c2m·Γ/c)` by Leibniz and use
-- `c2mJets` (`|DthIter r c2m| ≤ C·sin 2θ ≤ C` for `r ≤ 8`), so every jet term carries a factor
-- `α²` and is bounded by `α²·C·sin^{-q}`.
theorem angBlk4_VfsA_mass : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    MeasureTheory.IntegrableOn
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α
          (Work.FTS.StrongPersist.L3Rhs.VfsA1 α)) Work.Spaces.Iθ ∧
    α * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α
          (Work.FTS.StrongPersist.L3Rhs.VfsA1 α) θ) ≤ K ∧
    MeasureTheory.IntegrableOn
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α
          (Work.FTS.StrongPersist.L3Rhs.VfsA2 α)) Work.Spaces.Iθ ∧
    α * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α
          (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ) ≤ K := by
  obtain ⟨C2c, hC2cpos, -, hC2cabs, hC2cjet⟩ := c2mJets
  obtain ⟨Cj, hCjpos, hCj⟩ := vfs4_VfsA2_jet
  refine ⟨10 ^ 22 * (C2c ^ 2 + Cj ^ 2 * C2c ^ 2 + 1), by positivity, ?_⟩
  intro α hαIoc
  obtain ⟨hα, hα1⟩ := hαIoc
  -- the `c2m` jet bound in the form required by the `VfsA2` machinery
  have hc2 : ∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ C2c := by
    intro j hj θ hθ
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      simpa using hC2cabs θ hθ
    · have hkey := hC2cjet j hpos (by omega) 0 θ hθ
      rw [Work.FTS.LocData.DthIter_rad_eq j Work.Construction.c2m 0 θ] at hkey
      refine le_trans hkey ?_
      have hs : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      nlinarith [hC2cpos]
  have hΓ : ∀ m ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[m] (VfsGc α) θ| ≤ 10 ^ 6 * Work.Spaces.Gam α θ :=
    fun m hm θ hθ => gamGc_jet hm hα hα1 hθ
  have hjet : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.dthU^[i] (VfsA2 α) θ|
        ≤ Cj * C2c * α
          * (|VfsGc α θ| + ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ|) :=
    fun i hi1 hi4 θ hθ => hCj C2c hC2cpos hc2 α hα hα1 i hi1 hi4 θ hθ
  obtain ⟨hA1int, hA1bd⟩ := massA1 hα hα1 (vfs4_A1_slot4 α hα hα1)
  obtain ⟨hA2int, hA2bd⟩ := massA2 (B := C2c) (Cj := Cj) hα hα1 hC2cpos hCjpos hc2 hjet hΓ
  have hK1 : (10 : ℝ) ^ 17 ≤ 10 ^ 22 * (C2c ^ 2 + Cj ^ 2 * C2c ^ 2 + 1) := by
    nlinarith [sq_nonneg C2c, sq_nonneg Cj, mul_nonneg (sq_nonneg Cj) (sq_nonneg C2c)]
  have hK2 : 100 * (C2c ^ 2 + Cj ^ 2 * C2c ^ 2) * 10 ^ 16
        + (Cj * 5000000) ^ 2 * C2c ^ 2 * (120 / 17)
      ≤ 10 ^ 22 * (C2c ^ 2 + Cj ^ 2 * C2c ^ 2 + 1) := by
    have hXY : Cj ^ 2 * C2c ^ 2 ≤ C2c ^ 2 + Cj ^ 2 * C2c ^ 2 := by
      linarith [sq_nonneg C2c]
    have hY0 : (0 : ℝ) ≤ Cj ^ 2 * C2c ^ 2 := by positivity
    have hexp : (Cj * 5000000) ^ 2 * C2c ^ 2 * (120 / 17)
        = (25000000000000 * (120 / 17)) * (Cj ^ 2 * C2c ^ 2) := by ring
    rw [hexp]
    nlinarith [hXY, hY0, sq_nonneg C2c, sq_nonneg Cj]
  exact ⟨hA1int, le_trans hA1bd hK1, hA2int, le_trans hA2bd hK2⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
