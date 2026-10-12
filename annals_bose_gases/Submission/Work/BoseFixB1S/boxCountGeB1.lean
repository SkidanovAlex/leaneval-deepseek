import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-! ## 1. The projection algebra of `boxPInd` -/

/-- `Pᵢ · Pᵢ = Pᵢ`. -/
private theorem boxPInd_idem {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (i : Fin N) (x : X N) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i Φ) x
      = Work.UBBInputs8.boxPInd volA A i Φ x := by
  have hupd : ∀ u : E3, Work.UBBInputs8.boxPInd volA A i Φ (Function.update x i u)
      = (1 / volA) * (∫ z in A, Φ (Function.update x i z))
        * A.indicator (fun _ => (1 : ℝ)) u := by
    intro u
    simp only [Work.UBBInputs8.boxPInd, Function.update_idem, Function.update_self]
  rw [show Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A i Φ) x
      = (1 / volA) * (∫ u in A, Work.UBBInputs8.boxPInd volA A i Φ (Function.update x i u))
        * A.indicator (fun _ => (1 : ℝ)) (x i) from rfl]
  rw [show (∫ u in A, Work.UBBInputs8.boxPInd volA A i Φ (Function.update x i u))
      = ∫ u in A, ((1 / volA) * (∫ z in A, Φ (Function.update x i z))
          * A.indicator (fun _ => (1 : ℝ)) u) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hupd)]
  rw [MeasureTheory.integral_const_mul]
  have h1A : (∫ u in A, A.indicator (fun _ => (1 : ℝ)) u) = volA := by
    have hpt : ∀ᵐ u ∂(MeasureTheory.volume.restrict A),
        A.indicator (fun _ => (1 : ℝ)) u = (1 : ℝ) := by
      rw [MeasureTheory.ae_restrict_iff' hA]
      exact Filter.Eventually.of_forall (fun u hu => Set.indicator_of_mem hu _)
    rw [MeasureTheory.integral_congr_ae hpt, MeasureTheory.setIntegral_const, smul_eq_mul,
      mul_one]
    exact hvolA.symm
  rw [h1A]
  rw [show Work.UBBInputs8.boxPInd volA A i Φ x
      = (1 / volA) * (∫ z in A, Φ (Function.update x i z))
        * A.indicator (fun _ => (1 : ℝ)) (x i) from rfl]
  have hvolne : volA ≠ 0 := ne_of_gt hvol
  field_simp

/-- `Pᵢ` and `Pⱼ` commute for `i ≠ j`. -/
private theorem boxPInd_comm {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ)
    {Φ : X N → ℝ} (hΦc : Continuous Φ) {i j : Fin N} (hij : i ≠ j) (x : X N) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      = Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x := by
  let μ' : Measure E3 := (MeasureTheory.volume : Measure E3).restrict A
  let G : E3 → E3 → ℝ := fun y z => Φ (Function.update (Function.update x i y) j z)
  have hGsymm : ∀ y z : E3, G y z = Φ (Function.update (Function.update x j z) i y) := by
    intro y z
    dsimp only [G]
    congr 1
    exact Function.update_comm hij y z x
  have hGc : Continuous (fun p : E3 × E3 => G p.1 p.2) := by
    dsimp only [G]
    fun_prop
  have hGint : Integrable (fun p : E3 × E3 => G p.1 p.2) (μ'.prod μ') := by
    obtain ⟨C₀, hC₀⟩ := ((acube_compact hℓ).prod (acube_compact hℓ)).exists_bound_of_continuousOn
      hGc.continuousOn
    have hfin : (MeasureTheory.volume : Measure (E3 × E3)) (A ×ˢ A) < ∞ := by
      rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
      exact ENNReal.mul_lt_top (volume_A_lt_top hℓ hAc) (volume_A_lt_top hℓ hAc)
    have hon : IntegrableOn (fun p : E3 × E3 => G p.1 p.2) (A ×ˢ A) MeasureTheory.volume := by
      refine IntegrableOn.of_bound hfin hGc.aestronglyMeasurable.restrict C₀ ?_
      rw [MeasureTheory.ae_restrict_iff' (hA.prod hA)]
      exact Filter.Eventually.of_forall (fun p hp =>
        hC₀ p (Set.mem_prod.mpr ⟨hAc hp.1, hAc hp.2⟩))
    rw [show μ'.prod μ' = (MeasureTheory.volume : Measure (E3 × E3)).restrict (A ×ˢ A) from by
      rw [show μ' = (MeasureTheory.volume : Measure E3).restrict A from rfl,
        MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]]
    exact hon
  have hswap : (∫ y : E3, ∫ z : E3, G y z ∂μ' ∂μ')
      = (∫ z : E3, ∫ y : E3, G y z ∂μ' ∂μ') :=
    MeasureTheory.integral_integral_swap hGint
  have hL : Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      = (1 / volA) * (1 / volA)
        * (A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j))
        * (∫ y : E3, ∫ z : E3, G y z ∂μ' ∂μ') := by
    rw [show Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
        = (1 / volA) * (∫ y in A, Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i y))
          * A.indicator (fun _ => (1 : ℝ)) (x i) from rfl]
    have hkey : ∀ y : E3, Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i y)
        = (1 / volA) * (∫ z in A, Φ (Function.update (Function.update x i y) j z))
          * A.indicator (fun _ => (1 : ℝ)) (x j) := by
      intro y
      rw [show Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i y)
          = (1 / volA) * (∫ z in A, Φ (Function.update (Function.update x i y) j z))
            * A.indicator (fun _ => (1 : ℝ)) ((Function.update x i y) j) from rfl]
      rw [Function.update_of_ne hij.symm y x]
    rw [show (∫ y in A, Work.UBBInputs8.boxPInd volA A j Φ (Function.update x i y))
        = ∫ y in A, ((1 / volA) * (∫ z in A, Φ (Function.update (Function.update x i y) j z))
            * A.indicator (fun _ => (1 : ℝ)) (x j)) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hkey)]
    rw [MeasureTheory.integral_mul_const]
    rw [MeasureTheory.integral_const_mul]
    rw [show (∫ y in A, (∫ z in A, Φ (Function.update (Function.update x i y) j z)))
        = ∫ y : E3, ∫ z : E3, G y z ∂μ' ∂μ' from rfl]
    ring
  have hR : Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
      = (1 / volA) * (1 / volA)
        * (A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j))
        * (∫ y : E3, ∫ z : E3, G z y ∂μ' ∂μ') := by
    rw [show Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
        = (1 / volA) * (∫ y in A, Work.UBBInputs8.boxPInd volA A i Φ (Function.update x j y))
          * A.indicator (fun _ => (1 : ℝ)) (x j) from rfl]
    have hkey : ∀ y : E3, Work.UBBInputs8.boxPInd volA A i Φ (Function.update x j y)
        = (1 / volA) * (∫ z in A, Φ (Function.update (Function.update x j y) i z))
          * A.indicator (fun _ => (1 : ℝ)) (x i) := by
      intro y
      rw [show Work.UBBInputs8.boxPInd volA A i Φ (Function.update x j y)
          = (1 / volA) * (∫ z in A, Φ (Function.update (Function.update x j y) i z))
            * A.indicator (fun _ => (1 : ℝ)) ((Function.update x j y) i) from rfl]
      rw [Function.update_of_ne hij y x]
    rw [show (∫ y in A, Work.UBBInputs8.boxPInd volA A i Φ (Function.update x j y))
        = ∫ y in A, ((1 / volA) * (∫ z in A, Φ (Function.update (Function.update x j y) i z))
            * A.indicator (fun _ => (1 : ℝ)) (x i)) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hkey)]
    rw [MeasureTheory.integral_mul_const]
    rw [MeasureTheory.integral_const_mul]
    rw [show (∫ y in A, (∫ z in A, Φ (Function.update (Function.update x j y) i z)))
        = ∫ y : E3, ∫ z : E3, G z y ∂μ' ∂μ' from by
      apply integral_congr_ae
      filter_upwards with y
      apply integral_congr_ae
      filter_upwards with z
      exact (hGsymm z y).symm]
    ring
  have hren : (∫ z : E3, ∫ y : E3, G y z ∂μ' ∂μ')
      = (∫ y : E3, ∫ z : E3, G z y ∂μ' ∂μ') := rfl
  rw [hL, hR, hswap, hren]

/-- Self-adjointness of `Pᵢ` on `L²(abox N ℓ)`. -/
private theorem boxPInd_sym {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Φ Ψ : X N → ℝ}
    (hΦm : Measurable Φ) {CΦ : ℝ} (hΦb : ∀ x ∈ abox N ℓ, |Φ x| ≤ CΦ)
    (hΨm : Measurable Ψ) {CΨ : ℝ} (hΨb : ∀ x ∈ abox N ℓ, |Ψ x| ≤ CΨ) :
    (∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x)
      = ∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x := by
  have hI1 : IntegrableOn (fun x : X N => Work.UBBInputs8.boxPInd volA A i Ψ x * Φ x)
      (abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ (measurable_boxPInd volA A hA i hΨm) hΦm
      (abs_boxPInd_le hℓ hvol hA hvolA hAc i hΨb) hΦb
  have hI2 : IntegrableOn (fun x : X N => Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x)
      (abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ (measurable_boxPInd volA A hA i hΦm) hΨm
      (abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb) hΨb
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    have hP1 := abox_integral_peel (i := i)
      (F := fun x : X (n + 1) => Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x) hI2
    have hP2 := abox_integral_peel (i := i)
      (F := fun x : X (n + 1) => Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x)
      (by simpa only [mul_comm] using hI1)
    have hpoint : ∀ r : X n,
        (∫ y in acube ℓ,
            Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) * Ψ (kcInsN n i (y, r)))
          = ∫ y in acube ℓ,
            Φ (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (y, r)) := by
      intro r
      have hL : (∫ y in acube ℓ,
            Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) * Ψ (kcInsN n i (y, r)))
          = (1 / volA) * (∫ z in A, Φ (kcInsN n i (z, r)))
            * (∫ z in A, Ψ (kcInsN n i (z, r))) := by
        have hcongr : (∫ y in acube ℓ,
              Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) * Ψ (kcInsN n i (y, r)))
            = ∫ y in acube ℓ, ((1 / volA) * (∫ z in A, Φ (kcInsN n i (z, r))))
                * (A.indicator (fun _ => (1 : ℝ)) y * Ψ (kcInsN n i (y, r))) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          rw [boxPInd_kcInsN]
          ring
        rw [hcongr, MeasureTheory.integral_const_mul,
          setIntegral_indicator_one_mul hA hAc (fun z : E3 => Ψ (kcInsN n i (z, r)))]
        try ring
      have hR : (∫ y in acube ℓ,
            Φ (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (y, r)))
          = (1 / volA) * (∫ z in A, Φ (kcInsN n i (z, r)))
            * (∫ z in A, Ψ (kcInsN n i (z, r))) := by
        have hcongr : (∫ y in acube ℓ,
              Φ (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (y, r)))
            = ∫ y in acube ℓ, ((1 / volA) * (∫ z in A, Ψ (kcInsN n i (z, r))))
                * (A.indicator (fun _ => (1 : ℝ)) y * Φ (kcInsN n i (y, r))) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          rw [boxPInd_kcInsN]
          ring
        rw [hcongr, MeasureTheory.integral_const_mul,
          setIntegral_indicator_one_mul hA hAc (fun z : E3 => Φ (kcInsN n i (z, r)))]
        ring
      rw [hL, hR]
    calc
      (∫ x in abox (n + 1) ℓ, Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x)
          = ∫ r : X n, (∫ y in acube ℓ,
              Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) * Ψ (kcInsN n i (y, r)))
            ∂((MeasureTheory.volume : Measure (X n)).restrict (abox n ℓ)) := hP1
      _ = ∫ r : X n, (∫ y in acube ℓ,
              Φ (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (y, r)))
            ∂((MeasureTheory.volume : Measure (X n)).restrict (abox n ℓ)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with r
            exact hpoint r
      _ = (∫ x in abox (n + 1) ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x) := hP2.symm

/-! ## 2. The two projection identities -/

/-- `∫(PᵢΦ)² = ∫ Φ·PᵢΦ`. -/
private theorem boxPInd_sq_integral {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) {Φ : X N → ℝ} (hΦm : Measurable Φ) {C : ℝ}
    (hΦb : ∀ x ∈ abox N ℓ, |Φ x| ≤ C) :
    (∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      = ∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Φ x := by
  have hPm : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    measurable_boxPInd volA A hA i hΦm
  have hPb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb
  have hs := boxPInd_sym hℓ hvol hA hvolA hAc i (Φ := Φ)
    (Ψ := Work.UBBInputs8.boxPInd volA A i Φ) hΦm hΦb hPm hPb
  rw [show (fun x : X N => (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      = fun x => Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A i Φ x from
    funext fun x => by ring]
  rw [hs]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [boxPInd_idem hℓ hvol hA hvolA hAc i x]

/-- For `i ≠ j`: `∫(PᵢPⱼΦ)² = ∫ (PᵢΦ)·(PⱼΦ)`. -/
private theorem boxPInd_pair_integral {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ)
    {C : ℝ} (hΦb : ∀ x ∈ abox N ℓ, |Φ x| ≤ C) :
    (∫ x in abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
      = ∫ x in abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x := by
  have hPim : Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    measurable_boxPInd volA A hA i hΦc.measurable
  have hPjm : Measurable (Work.UBBInputs8.boxPInd volA A j Φ) :=
    measurable_boxPInd volA A hA j hΦc.measurable
  have hPijm : Measurable
      (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ)) :=
    measurable_boxPInd volA A hA i hPjm
  have hPib : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ C :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb
  have hPjb : ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A j Φ x| ≤ C :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc j hΦb
  have hPijb : ∀ x ∈ abox N ℓ,
      |Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x| ≤ C :=
    abs_boxPInd_le hℓ hvol hA hvolA hAc i hPjb
  -- `∫ (PᵢPⱼΦ)² = ∫ (PⱼΦ)·(PᵢPⱼΦ)`
  have hstep1 : (∫ x in abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
      = ∫ x in abox N ℓ,
        Work.UBBInputs8.boxPInd volA A j Φ x
          * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x := by
    have hs := boxPInd_sym hℓ hvol hA hvolA hAc i
      (Φ := Work.UBBInputs8.boxPInd volA A j Φ)
      (Ψ := Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ))
      hPjm hPjb hPijm hPijb
    rw [show (fun x : X N =>
          (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
        = fun x => Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
            * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x from
      funext fun x => by ring]
    rw [hs]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [boxPInd_idem hℓ hvol hA hvolA hAc i x]
  -- `∫ (PⱼPᵢΦ)·(PⱼΦ) = ∫ (PᵢΦ)·(PⱼΦ)`
  have hstep2 : (∫ x in abox N ℓ,
        Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
          * Work.UBBInputs8.boxPInd volA A j Φ x)
      = ∫ x in abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x := by
    have hs := boxPInd_sym hℓ hvol hA hvolA hAc j (Φ := Work.UBBInputs8.boxPInd volA A i Φ)
      (Ψ := Work.UBBInputs8.boxPInd volA A j Φ) hPim hPib hPjm hPjb
    rw [hs]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [boxPInd_idem hℓ hvol hA hvolA hAc j x]
  calc
    (∫ x in abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2)
        = ∫ x in abox N ℓ,
          Work.UBBInputs8.boxPInd volA A j Φ x
            * Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x := hstep1
    _ = ∫ x in abox N ℓ,
          Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
            * Work.UBBInputs8.boxPInd volA A j Φ x := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          ring
    _ = ∫ x in abox N ℓ,
          Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
            * Work.UBBInputs8.boxPInd volA A j Φ x := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          rw [boxPInd_comm hℓ hvol hA hvolA hAc (Φ := Φ) hΦc hij x]
    _ = ∫ x in abox N ℓ,
          Work.UBBInputs8.boxPInd volA A i Φ x * Work.UBBInputs8.boxPInd volA A j Φ x := hstep2

/-! ## 3. The count inequality -/

theorem boxCountGeB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1) :
    Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ^ 2 - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
      ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := abox N ℓ) (f := Φ) hΦc.continuousOn
  have hCb : ∀ x ∈ abox N ℓ, |Φ x| ≤ |B| := by
    intro x hx
    have h1 : |Φ x| ≤ B := by
      have h2 := hB x hx
      rwa [Real.norm_eq_abs] at h2
    exact le_trans h1 (le_abs_self B)
  have hmP : ∀ i : Fin N, Measurable (Work.UBBInputs8.boxPInd volA A i Φ) :=
    fun i => measurable_boxPInd volA A hA i hΦc.measurable
  have hbP : ∀ i : Fin N, ∀ x ∈ abox N ℓ, |Work.UBBInputs8.boxPInd volA A i Φ x| ≤ |B| :=
    fun i => abs_boxPInd_le hℓ hvol hA hvolA hAc i hCb
  set V : X N → ℝ := fun x => ∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x with hV
  have hVm : Measurable V := by
    rw [hV]
    exact Finset.measurable_sum _ (fun i _ => hmP i)
  have hVb : ∀ x ∈ abox N ℓ, |V x| ≤ ∑ _i : Fin N, |B| := by
    intro x hx
    rw [hV]
    calc |∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x|
        ≤ ∑ i : Fin N, |Work.UBBInputs8.boxPInd volA A i Φ x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, |B| := Finset.sum_le_sum (fun i _ => hbP i x hx)
  have hEint : ∀ i j : Fin N, IntegrableOn
      (fun x : X N => Work.UBBInputs8.boxPInd volA A i Φ x
        * Work.UBBInputs8.boxPInd volA A j Φ x) (abox N ℓ) MeasureTheory.volume :=
    fun i j => integrableOn_mul_of_bound hℓ (hmP i) (hmP j) (hbP i) (hbP j)
  -- (i) `∫ Φ·V = F`
  have hflat : boxFlatCount volA ℓ A Φ = ∫ x in abox N ℓ, Φ x * V x := by
    rw [boxFlatCount]
    rw [show (∑ i : Fin N, ∫ x in abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
        = ∑ i : Fin N, ∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Φ x from
      Finset.sum_congr rfl (fun i _ =>
        boxPInd_sq_integral hℓ hvol hA hvolA hAc i hΦc.measurable hCb)]
    rw [← MeasureTheory.integral_finsetSum]
    · apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [hV, Finset.mul_sum]
    · intro i _
      exact integrableOn_mul_of_bound hℓ hΦc.measurable (hmP i) hCb (hbP i)
  -- (ii) the expansion of `∫V²`
  have hsum : (∫ x in abox N ℓ, (V x) ^ 2)
      = ∑ p : Fin N × Fin N, ∫ x in abox N ℓ,
          Work.UBBInputs8.boxPInd volA A p.1 Φ x * Work.UBBInputs8.boxPInd volA A p.2 Φ x := by
    have hexp : (fun x : X N => (V x) ^ 2)
        = fun x => ∑ p : Fin N × Fin N,
            Work.UBBInputs8.boxPInd volA A p.1 Φ x * Work.UBBInputs8.boxPInd volA A p.2 Φ x := by
      funext x
      rw [hV]
      rw [show (∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
          = (∑ i : Fin N, Work.UBBInputs8.boxPInd volA A i Φ x)
            * (∑ j : Fin N, Work.UBBInputs8.boxPInd volA A j Φ x) from by ring]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
      rw [← Fintype.sum_prod_type (fun p : Fin N × Fin N =>
        Work.UBBInputs8.boxPInd volA A p.1 Φ x * Work.UBBInputs8.boxPInd volA A p.2 Φ x)]
    rw [hexp, MeasureTheory.integral_finsetSum]
    intro p _
    exact hEint p.1 p.2
  -- (iii) the pair count
  have hpair : boxPairCount volA ℓ A Φ
      = ∑ p : Fin N × Fin N, (if p.1 = p.2 then 0 else
          ∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A p.1 Φ x
            * Work.UBBInputs8.boxPInd volA A p.2 Φ x) := by
    rw [boxPairCount, pairSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : p.1 = p.2
    · simp [h]
    · have hB' := boxPInd_pair_integral hℓ hvol hA hvolA hAc h hΦc hCb
      rw [if_pos h, if_neg h, hB']
  -- (iv) the diagonal
  have hdiag1 : (∑ p : Fin N × Fin N, (if p.1 = p.2 then
        ∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A p.1 Φ x
          * Work.UBBInputs8.boxPInd volA A p.2 Φ x else 0)) = boxFlatCount volA ℓ A Φ := by
    rw [Fintype.sum_prod_type]
    rw [boxFlatCount]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  -- (v) assemble
  have hdiag : (∑ p : Fin N × Fin N, ∫ x in abox N ℓ,
        Work.UBBInputs8.boxPInd volA A p.1 Φ x * Work.UBBInputs8.boxPInd volA A p.2 Φ x)
      = boxFlatCount volA ℓ A Φ + boxPairCount volA ℓ A Φ := by
    have hsplit : (∑ p : Fin N × Fin N, (if p.1 = p.2 then
          ∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A p.1 Φ x
            * Work.UBBInputs8.boxPInd volA A p.2 Φ x else 0))
        + (∑ p : Fin N × Fin N, (if p.1 = p.2 then 0 else
          ∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A p.1 Φ x
            * Work.UBBInputs8.boxPInd volA A p.2 Φ x))
        = ∑ p : Fin N × Fin N, ∫ x in abox N ℓ,
            Work.UBBInputs8.boxPInd volA A p.1 Φ x * Work.UBBInputs8.boxPInd volA A p.2 Φ x := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : p.1 = p.2 <;> simp [h]
    rw [← hsplit, hdiag1, hpair]
  -- Cauchy–Schwarz
  haveI : IsFiniteMeasure ((MeasureTheory.volume : Measure (X N)).restrict (abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top N ℓ hℓ.le⟩
  have hMemΦ : MemLp (fun x : X N => Φ x) 2
      ((MeasureTheory.volume : Measure (X N)).restrict (abox N ℓ)) :=
    MemLp.of_bound hΦc.aestronglyMeasurable.restrict |B| (by
      rw [MeasureTheory.ae_restrict_iff' (abox_measurable N ℓ)]
      exact Filter.Eventually.of_forall (fun x hx => by
        rw [Real.norm_eq_abs]; exact hCb x hx))
  have hMemV : MemLp V 2 ((MeasureTheory.volume : Measure (X N)).restrict (abox N ℓ)) :=
    MemLp.of_bound hVm.aestronglyMeasurable.restrict (∑ _i : Fin N, |B|) (by
      rw [MeasureTheory.ae_restrict_iff' (abox_measurable N ℓ)]
      exact Filter.Eventually.of_forall (fun x hx => by
        rw [Real.norm_eq_abs]; exact hVb x hx))
  have hcs := Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt hMemV hMemΦ
  have hFV : (∫ x in abox N ℓ, V x * Φ x) = boxFlatCount volA ℓ A Φ := by
    rw [hflat]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  rw [hFV, hnorm, Real.sqrt_one, mul_one] at hcs
  have hF0 : 0 ≤ boxFlatCount volA ℓ A Φ := by
    rw [boxFlatCount]
    exact Finset.sum_nonneg (fun i _ =>
      MeasureTheory.integral_nonneg (fun x => sq_nonneg _))
  have hV2nn : 0 ≤ ∫ x in abox N ℓ, (V x) ^ 2 :=
    MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have habs : boxFlatCount volA ℓ A Φ ≤ Real.sqrt (∫ x in abox N ℓ, (V x) ^ 2) := by
    rw [← abs_of_nonneg hF0]
    exact hcs
  have hsqle : boxFlatCount volA ℓ A Φ ^ 2 ≤ ∫ x in abox N ℓ, (V x) ^ 2 := by
    have h2 := pow_le_pow_left₀ hF0 habs 2
    rwa [Real.sq_sqrt hV2nn] at h2
  rw [hsum, hdiag] at hsqle
  linarith

end Work.BoseFixB1S
