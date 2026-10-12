import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseDict.bomb_dGamma_slot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-! ## Auxiliary lemmas for the binary (real/imaginary) selection

The complex box state `Θ = u + i v` is expanded against a `ℂ`-linear operator `A`:
the cross terms do not cancel, but they are *imaginary*, so the real part of the pairing is the
sum of the two real pairings at `u` and at `v`.  The two elementary lemmas below formalise that,
and the third is the two-element selection itself. -/

/-- The real part of a Bochner integral of a complex-valued function. -/
lemma re_integral {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → ℂ}
    (hf : MeasureTheory.Integrable f μ) :
    (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := by
  have h := Complex.reCLM.integral_comp_comm hf
  simp only [Complex.reCLM_apply] at h
  exact h.symm

/-- **The complex pairing is additive over the real/imaginary splitting.**  For a `ℂ`-linear `A`
and functions `u`, `v`, the pairing of `u + i v` with `A (u + i v)` is the sum of the two
diagonal pairings plus the explicit cross term `i (⟪u, A v⟫ - ⟪v, A u⟫)`.  (This is a purely
sesquilinear statement; the integrability hypotheses are what is needed to split the integral.) -/
lemma cIPn_add_I_smul {n : ℕ}
    (A : (Work.BoseDict.Xn n → ℂ) →ₗ[ℂ] (Work.BoseDict.Xn n → ℂ))
    (u v : Work.BoseDict.Xn n → ℂ)
    (h1 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (u x) * (A u) x)
    (h2 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (u x) * (A v) x)
    (h3 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (v x) * (A u) x)
    (h4 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (v x) * (A v) x) :
    Work.BoseDict.cIPn n (u + Complex.I • v) (A (u + Complex.I • v))
      = Work.BoseDict.cIPn n u (A u) + Work.BoseDict.cIPn n v (A v)
        + Complex.I * (Work.BoseDict.cIPn n u (A v) - Work.BoseDict.cIPn n v (A u)) := by
  rw [map_add, map_smul]
  simp only [Work.BoseDict.cIPn]
  have hF : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n =>
      (starRingEnd ℂ) (u x) * (A u) x + (starRingEnd ℂ) (v x) * (A v) x) := h1.add h4
  have hG : MeasureTheory.Integrable (fun x : Work.BoseDict.Xn n =>
      Complex.I * ((starRingEnd ℂ) (u x) * (A v) x - (starRingEnd ℂ) (v x) * (A u) x)) :=
    (h2.sub h3).const_mul Complex.I
  have hpt : ∀ x : Work.BoseDict.Xn n,
      (starRingEnd ℂ) ((u + Complex.I • v) x) * (A u + Complex.I • A v) x
      = (starRingEnd ℂ) (u x) * (A u) x + (starRingEnd ℂ) (v x) * (A v) x
        + Complex.I * ((starRingEnd ℂ) (u x) * (A v) x - (starRingEnd ℂ) (v x) * (A u) x) := by
    intro x
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Complex.conj_I]
    linear_combination -((starRingEnd ℂ) (v x) * (A v) x) * hI
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_add hF hG]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_sub h2 h3]
  rw [MeasureTheory.integral_add h1 h4]

/-- The same expansion at the identity operator (the norm/energy denominator):
`⟪u + i v, u + i v⟫ = ⟪u,u⟫ + ⟪v,v⟫ + i (⟪u,v⟫ - ⟪v,u⟫)`. -/
lemma cIPn_add_I_smul_self {n : ℕ} (u v : Work.BoseDict.Xn n → ℂ)
    (h1 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (u x) * u x)
    (h2 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (u x) * v x)
    (h3 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (v x) * u x)
    (h4 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (v x) * v x) :
    Work.BoseDict.cIPn n (u + Complex.I • v) (u + Complex.I • v)
      = Work.BoseDict.cIPn n u u + Work.BoseDict.cIPn n v v
        + Complex.I * (Work.BoseDict.cIPn n u v - Work.BoseDict.cIPn n v u) := by
  simpa using cIPn_add_I_smul
    (LinearMap.id : (Work.BoseDict.Xn n → ℂ) →ₗ[ℂ] (Work.BoseDict.Xn n → ℂ))
    u v h1 h2 h3 h4

/-- **The two-element (binary) selection.**  If `ν₁, ν₂ ≥ 0` are not both zero, `q₁ + q₂ ≤ c (ν₁ +
ν₂)`, and the quadratic form vanishes on the kernel of the norm form
(`νᵢ = 0 → qᵢ = 0`), then one of the two indices satisfies both `νᵢ > 0` and `qᵢ ≤ c νᵢ`. -/
lemma binary_le {ν₁ ν₂ q₁ q₂ c : ℝ} (hν₁ : 0 ≤ ν₁) (hν₂ : 0 ≤ ν₂)
    (hν : 0 < ν₁ + ν₂) (h : q₁ + q₂ ≤ c * (ν₁ + ν₂))
    (hq₁ : ν₁ = 0 → q₁ = 0) (hq₂ : ν₂ = 0 → q₂ = 0) :
    (0 < ν₁ ∧ q₁ ≤ c * ν₁) ∨ (0 < ν₂ ∧ q₂ ≤ c * ν₂) := by
  by_cases h1 : ν₁ = 0
  · right
    refine ⟨by rw [h1, zero_add] at hν; exact hν, ?_⟩
    have hq := hq₁ h1
    rw [h1, hq, zero_add, zero_add] at h
    exact h
  · have hν₁pos : 0 < ν₁ := lt_of_le_of_ne' hν₁ h1
    by_cases h2 : ν₂ = 0
    · left
      refine ⟨hν₁pos, ?_⟩
      have hq := hq₂ h2
      rw [h2, add_zero, hq, add_zero] at h
      exact h
    · have hν₂pos : 0 < ν₂ := lt_of_le_of_ne' hν₂ h2
      rcases le_or_gt q₁ (c * ν₁) with hle | hgt
      · exact Or.inl ⟨hν₁pos, hle⟩
      · exact Or.inr ⟨hν₂pos, by nlinarith [h]⟩

/-- **The binary (real/imaginary) selection of the BF3c fibre argument.**
`Θ = boxRealise Ψ₁ + I • boxRealise Ψ₂` is a complex model-representable box state (the slice
of a `V`-sector); `A_V` is the `ℂ`-linear box-side realisation of the model operator `A_H`
(the dictionary rows `bomb Ψ (A_H Ψ') = cIPn (boxRealise Ψ) (A_V (boxRealise Ψ'))`), and `hiso`
is the isometry `cIPn (boxRealise Ψ) (boxRealise Ψ') = bomb Ψ Ψ'` (`boxRealise_cIPn_gen`).
Then a ratio bound at the *complex* vector `Θ` produces a *real* model vector
`Ψ₁` or `Ψ₂` with the same (or better) ratio. -/
theorem exists_binary_le {m d : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (A_V : (Work.BoseDict.Xn d → ℂ) →ₗ[ℂ] (Work.BoseDict.Xn d → ℂ))
    (A_H : Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m)
    (hdict : ∀ Ψ Ψ' : Work.BoseB4.RealFock m,
      (∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) →
      (∀ α ∈ Ψ'.support, α.sum (fun _ k => k) = d) →
      Work.BoseDict.cIPn d (Work.BoseDict.boxRealise e d Ψ)
        (A_V (Work.BoseDict.boxRealise e d Ψ'))
        = ((Work.BoseB4.bomb m Ψ (A_H Ψ') : ℝ) : ℂ))
    (hiso : ∀ Ψ Ψ' : Work.BoseB4.RealFock m,
      (∀ α ∈ Ψ.support, α.sum (fun _ k => k) = d) →
      (∀ α ∈ Ψ'.support, α.sum (fun _ k => k) = d) →
      Work.BoseDict.cIPn d (Work.BoseDict.boxRealise e d Ψ)
        (Work.BoseDict.boxRealise e d Ψ') = ((Work.BoseB4.bomb m Ψ Ψ' : ℝ) : ℂ))
    (Ψ₁ Ψ₂ : Work.BoseB4.RealFock m)
    (hdeg₁ : ∀ α ∈ Ψ₁.support, α.sum (fun _ k => k) = d)
    (hdeg₂ : ∀ α ∈ Ψ₂.support, α.sum (fun _ k => k) = d)
    (hintA : ∀ i j : Fin 2, MeasureTheory.Integrable
      (fun x : Work.BoseDict.Xn d =>
        (starRingEnd ℂ) (![Work.BoseDict.boxRealise e d Ψ₁,
            Work.BoseDict.boxRealise e d Ψ₂] i x)
          * A_V (![Work.BoseDict.boxRealise e d Ψ₁,
            Work.BoseDict.boxRealise e d Ψ₂] j) x))
    (hintN : ∀ i j : Fin 2, MeasureTheory.Integrable
      (fun x : Work.BoseDict.Xn d =>
        (starRingEnd ℂ) (![Work.BoseDict.boxRealise e d Ψ₁,
            Work.BoseDict.boxRealise e d Ψ₂] i x)
          * ![Work.BoseDict.boxRealise e d Ψ₁, Work.BoseDict.boxRealise e d Ψ₂] j x))
    (Θ : Work.BoseDict.Xn d → ℂ)
    (hΘ : Θ = Work.BoseDict.boxRealise e d Ψ₁
      + Complex.I • Work.BoseDict.boxRealise e d Ψ₂)
    (c : ℝ) (hν : 0 < (Work.BoseDict.cIPn d Θ Θ).re)
    (h : (Work.BoseDict.cIPn d Θ (A_V Θ)).re ≤ c * (Work.BoseDict.cIPn d Θ Θ).re) :
    (0 < Work.BoseB4.bomb m Ψ₁ Ψ₁ ∧
        Work.BoseB4.bomb m Ψ₁ (A_H Ψ₁) ≤ c * Work.BoseB4.bomb m Ψ₁ Ψ₁)
      ∨ (0 < Work.BoseB4.bomb m Ψ₂ Ψ₂ ∧
        Work.BoseB4.bomb m Ψ₂ (A_H Ψ₂) ≤ c * Work.BoseB4.bomb m Ψ₂ Ψ₂) := by
  -- the four pairings against `A_V`
  have hA00 : MeasureTheory.Integrable fun x : Work.BoseDict.Xn d =>
      (starRingEnd ℂ) ((Work.BoseDict.boxRealise e d Ψ₁) x)
        * (A_V (Work.BoseDict.boxRealise e d Ψ₁)) x := by
    simpa using hintA 0 0
  have hA01 : MeasureTheory.Integrable fun x : Work.BoseDict.Xn d =>
      (starRingEnd ℂ) ((Work.BoseDict.boxRealise e d Ψ₁) x)
        * (A_V (Work.BoseDict.boxRealise e d Ψ₂)) x := by
    simpa using hintA 0 1
  have hA10 : MeasureTheory.Integrable fun x : Work.BoseDict.Xn d =>
      (starRingEnd ℂ) ((Work.BoseDict.boxRealise e d Ψ₂) x)
        * (A_V (Work.BoseDict.boxRealise e d Ψ₁)) x := by
    simpa using hintA 1 0
  have hA11 : MeasureTheory.Integrable fun x : Work.BoseDict.Xn d =>
      (starRingEnd ℂ) ((Work.BoseDict.boxRealise e d Ψ₂) x)
        * (A_V (Work.BoseDict.boxRealise e d Ψ₂)) x := by
    simpa using hintA 1 1
  -- the four pairings against the identity
  have hN00 : MeasureTheory.Integrable fun x : Work.BoseDict.Xn d =>
      (starRingEnd ℂ) ((Work.BoseDict.boxRealise e d Ψ₁) x)
        * (Work.BoseDict.boxRealise e d Ψ₁) x := by
    simpa using hintN 0 0
  have hN01 : MeasureTheory.Integrable fun x : Work.BoseDict.Xn d =>
      (starRingEnd ℂ) ((Work.BoseDict.boxRealise e d Ψ₁) x)
        * (Work.BoseDict.boxRealise e d Ψ₂) x := by
    simpa using hintN 0 1
  have hN10 : MeasureTheory.Integrable fun x : Work.BoseDict.Xn d =>
      (starRingEnd ℂ) ((Work.BoseDict.boxRealise e d Ψ₂) x)
        * (Work.BoseDict.boxRealise e d Ψ₁) x := by
    simpa using hintN 1 0
  have hN11 : MeasureTheory.Integrable fun x : Work.BoseDict.Xn d =>
      (starRingEnd ℂ) ((Work.BoseDict.boxRealise e d Ψ₂) x)
        * (Work.BoseDict.boxRealise e d Ψ₂) x := by
    simpa using hintN 1 1
  -- the splitting of the two pairings
  have hnum : (Work.BoseDict.cIPn d Θ (A_V Θ)).re
      = Work.BoseB4.bomb m Ψ₁ (A_H Ψ₁) + Work.BoseB4.bomb m Ψ₂ (A_H Ψ₂) := by
    have hgen := cIPn_add_I_smul (n := d) A_V
      (Work.BoseDict.boxRealise e d Ψ₁) (Work.BoseDict.boxRealise e d Ψ₂)
      hA00 hA01 hA10 hA11
    rw [hΘ, hgen, hdict Ψ₁ Ψ₁ hdeg₁ hdeg₁, hdict Ψ₂ Ψ₂ hdeg₂ hdeg₂,
      hdict Ψ₁ Ψ₂ hdeg₁ hdeg₂, hdict Ψ₂ Ψ₁ hdeg₂ hdeg₁]
    simp [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hden : (Work.BoseDict.cIPn d Θ Θ).re
      = Work.BoseB4.bomb m Ψ₁ Ψ₁ + Work.BoseB4.bomb m Ψ₂ Ψ₂ := by
    have hgen := cIPn_add_I_smul_self (n := d)
      (Work.BoseDict.boxRealise e d Ψ₁) (Work.BoseDict.boxRealise e d Ψ₂)
      hN00 hN01 hN10 hN11
    rw [hΘ, hgen, hiso Ψ₁ Ψ₁ hdeg₁ hdeg₁, hiso Ψ₂ Ψ₂ hdeg₂ hdeg₂,
      hiso Ψ₁ Ψ₂ hdeg₁ hdeg₂, hiso Ψ₂ Ψ₁ hdeg₂ hdeg₁]
    simp [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  -- the two real numbers entering the selection, and the vanishing on the kernel
  have hq₁ : Work.BoseB4.bomb m Ψ₁ Ψ₁ = 0 → Work.BoseB4.bomb m Ψ₁ (A_H Ψ₁) = 0 := by
    intro h0
    have hz : Ψ₁ = 0 := Work.BoseB4.Bomb_self_eq_zero h0
    simp [hz]
  have hq₂ : Work.BoseB4.bomb m Ψ₂ Ψ₂ = 0 → Work.BoseB4.bomb m Ψ₂ (A_H Ψ₂) = 0 := by
    intro h0
    have hz : Ψ₂ = 0 := Work.BoseB4.Bomb_self_eq_zero h0
    simp [hz]
  refine binary_le (Work.BoseB4.Bomb_self_nonneg Ψ₁) (Work.BoseB4.Bomb_self_nonneg Ψ₂)
    (by rw [← hden]; exact hν) ?_ hq₁ hq₂
  rw [← hnum, ← hden]
  exact h

end Work.BoseBoxFock
