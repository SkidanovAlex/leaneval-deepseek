import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped ENNReal

namespace Work.BW

/-- Prékopa–Leindler inequality for a measure `μ` on a `ℝ`-module, a.e.-measurable version. -/
def PL {X : Type*} [MeasurableSpace X] [Add X] [SMul ℝ X] (μ : Measure X) : Prop :=
  ∀ (f g m : X → ℝ≥0∞), AEMeasurable f μ → AEMeasurable g μ → AEMeasurable m μ →
    ∀ ⦃lam : ℝ⦄, 0 < lam → lam < 1 →
      (∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ m (lam • x + (1 - lam) • y)) →
      (∫⁻ x, f x ∂μ) ^ lam * (∫⁻ x, g x ∂μ) ^ (1 - lam) ≤ ∫⁻ x, m x ∂μ

/-- Prékopa–Leindler inequality for a measure `μ` on a `ℝ`-module, measurable version. -/
def PLm {X : Type*} [MeasurableSpace X] [Add X] [SMul ℝ X] (μ : Measure X) : Prop :=
  ∀ (f g m : X → ℝ≥0∞), Measurable f → Measurable g → Measurable m →
    ∀ ⦃lam : ℝ⦄, 0 < lam → lam < 1 →
      (∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ m (lam • x + (1 - lam) • y)) →
      (∫⁻ x, f x ∂μ) ^ lam * (∫⁻ x, g x ∂μ) ^ (1 - lam) ≤ ∫⁻ x, m x ∂μ

/-- The a.e.-measurable version of Prékopa–Leindler follows from the measurable version:
patch the a.e.-measurable functions on a measurable null set, putting `∞` on that null set
for the majorant. -/
theorem PLm.to_PL {X : Type*} [MeasurableSpace X] [Add X] [SMul ℝ X] {μ : Measure X}
    (h : PLm μ) : PL μ := by
  intro f g m hf hg hm lam h0 h1 hhyp
  obtain ⟨Nf, hNf, hNf_meas, hNf_zero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hf.ae_eq_mk)
  obtain ⟨Ng, hNg, hNg_meas, hNg_zero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hg.ae_eq_mk)
  obtain ⟨Nm, hNm, hNm_meas, hNm_zero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hm.ae_eq_mk)
  set N : Set X := Nf ∪ Ng ∪ Nm with hNdef
  have hN_meas : MeasurableSet N := (hNf_meas.union hNg_meas).union hNm_meas
  have hN_zero : μ N = 0 := by
    rw [hNdef]
    exact measure_union_null (measure_union_null hNf_zero hNg_zero) hNm_zero
  have hNfN : Nf ⊆ N := fun x hx => Or.inl (Or.inl hx)
  have hNgN : Ng ⊆ N := fun x hx => Or.inl (Or.inr hx)
  have hNmN : Nm ⊆ N := fun x hx => Or.inr hx
  have hcompl_ae : ∀ᵐ x ∂μ, x ∉ N := by
    rw [ae_iff]
    simpa using hN_zero
  set F : X → ℝ≥0∞ := Nᶜ.indicator (AEMeasurable.mk f hf) with hFdef
  set G : X → ℝ≥0∞ := Nᶜ.indicator (AEMeasurable.mk g hg) with hGdef
  set M : X → ℝ≥0∞ := Nᶜ.indicator (AEMeasurable.mk m hm) + N.indicator (fun _ => ∞) with hMdef
  have hNc : MeasurableSet Nᶜ := MeasurableSet.compl hN_meas
  have hFm : Measurable F := (hf.measurable_mk).indicator hNc
  have hGm : Measurable G := (hg.measurable_mk).indicator hNc
  have hMm : Measurable M :=
    ((hm.measurable_mk).indicator hNc).add
      ((measurable_const : Measurable fun _ : X => (∞ : ℝ≥0∞)).indicator hN_meas)
  have hFeq : F =ᵐ[μ] f := by
    filter_upwards [hf.ae_eq_mk, hcompl_ae] with x hx hxN
    rw [hFdef, Set.indicator_of_mem (by simpa using hxN)]
    exact hx.symm
  have hGeq : G =ᵐ[μ] g := by
    filter_upwards [hg.ae_eq_mk, hcompl_ae] with x hx hxN
    rw [hGdef, Set.indicator_of_mem (by simpa using hxN)]
    exact hx.symm
  have hMeq : M =ᵐ[μ] m := by
    filter_upwards [hm.ae_eq_mk, hcompl_ae] with x hx hxN
    rw [hMdef, Pi.add_apply, Set.indicator_of_mem (by simpa using hxN),
      Set.indicator_of_notMem hxN, add_zero]
    exact hx.symm
  have hhyp' : ∀ x y, F x ^ lam * G y ^ (1 - lam) ≤ M (lam • x + (1 - lam) • y) := by
    intro x y
    by_cases hx : x ∈ N
    · have hFx : F x = 0 := by simp [hFdef, hx]
      rw [hFx, ENNReal.rpow_eq_zero_iff.mpr (Or.inl ⟨rfl, h0⟩), zero_mul]
      exact bot_le
    · have hmkx : AEMeasurable.mk f hf x = f x := by
        by_contra hc
        exact hx (hNfN (hNf (fun hh => hc hh.symm)))
      have hFx : F x = f x := by simp [hFdef, hx, hmkx]
      rw [hFx]
      by_cases hy : y ∈ N
      · have hGy : G y = 0 := by simp [hGdef, hy]
        rw [hGy, ENNReal.rpow_eq_zero_iff.mpr (Or.inl ⟨rfl, sub_pos.mpr h1⟩), mul_zero]
        exact bot_le
      · have hmky : AEMeasurable.mk g hg y = g y := by
          by_contra hc
          exact hy (hNgN (hNg (fun hh => hc hh.symm)))
        have hGy : G y = g y := by simp [hGdef, hy, hmky]
        rw [hGy]
        by_cases hz : lam • x + (1 - lam) • y ∈ N
        · have hMz : M (lam • x + (1 - lam) • y) = ∞ := by simp [hMdef, hz]
          rw [hMz]
          exact le_top
        · have hmkz : AEMeasurable.mk m hm (lam • x + (1 - lam) • y)
              = m (lam • x + (1 - lam) • y) := by
            by_contra hc
            exact hz (hNmN (hNm (fun hh => hc hh.symm)))
          have hMz : M (lam • x + (1 - lam) • y) = m (lam • x + (1 - lam) • y) := by
            simp [hMdef, hz, hmkz]
          rw [hMz]
          exact hhyp x y
  have hres := h F G M hFm hGm hMm h0 h1 hhyp'
  rwa [lintegral_congr_ae hFeq, lintegral_congr_ae hGeq, lintegral_congr_ae hMeq] at hres

end Work.BW
