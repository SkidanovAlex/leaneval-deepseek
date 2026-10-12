import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.exists_binary_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The complex pairing expansion for a *plain-function* operator.**
This is `Work.BoseBoxFock.cIPn_add_I_smul` with the `ℂ`-linearity of `A` replaced by the single
additivity statement `A (u + I • v) = A u + I • A v` at the two given vectors — the only property
of `A` that its proof used, through `rw [map_add, map_smul]`. -/
lemma cIPn_add_I_smul_fn {n : ℕ}
    (A : (Work.BoseDict.Xn n → ℂ) → (Work.BoseDict.Xn n → ℂ))
    (u v : Work.BoseDict.Xn n → ℂ)
    (hAF : A (u + Complex.I • v) = A u + Complex.I • A v)
    (h1 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (u x) * (A u) x)
    (h2 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (u x) * (A v) x)
    (h3 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (v x) * (A u) x)
    (h4 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (v x) * (A v) x) :
    Work.BoseDict.cIPn n (u + Complex.I • v) (A (u + Complex.I • v))
      = Work.BoseDict.cIPn n u (A u) + Work.BoseDict.cIPn n v (A v)
        + Complex.I * (Work.BoseDict.cIPn n u (A v) - Work.BoseDict.cIPn n v (A u)) := by
  rw [hAF]
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
lemma cIPn_add_I_smul_self_fn {n : ℕ} (u v : Work.BoseDict.Xn n → ℂ)
    (h1 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (u x) * u x)
    (h2 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (u x) * v x)
    (h3 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (v x) * u x)
    (h4 : MeasureTheory.Integrable fun x => (starRingEnd ℂ) (v x) * v x) :
    Work.BoseDict.cIPn n (u + Complex.I • v) (u + Complex.I • v)
      = Work.BoseDict.cIPn n u u + Work.BoseDict.cIPn n v v
        + Complex.I * (Work.BoseDict.cIPn n u v - Work.BoseDict.cIPn n v u) :=
  cIPn_add_I_smul_fn (fun w => w) u v rfl h1 h2 h3 h4

/-- **The binary (real/imaginary) selection with a *plain-function* box operator.**  This is
`Work.BoseBoxFock.exists_binary_le` with the hypothesis that `A_V` is a `→ₗ[ℂ]` weakened to the
single additivity statement that its proof actually uses,
`A_V (u + I • v) = A_V u + I • A_V v` at the two specific vectors `u = boxRealise e d Ψ₁`,
`v = boxRealise e d Ψ₂`.  Needed because `boxSlotSum e T` (`= A_V` in the application) is
`ℂ`-linear only on a.e. bounded compactly supported states (its Bochner-integral definition makes
it *not* additive on arbitrary functions), so it cannot be packaged as a `→ₗ[ℂ]`.  The proof is the
proof of `Work.BoseBoxFock.exists_binary_le` with `rw [map_add, map_smul]` replaced by `hAF`; the
auxiliary complex expansion `Work.BoseBoxFock.cIPn_add_I_smul` is re-proved here for a plain
function (see that file for `binary_le`, `cIPn_add_I_smul_self`, `re_integral`). -/
theorem exists_binary_le_apply {m d : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (A_V : (Work.BoseDict.Xn d → ℂ) → (Work.BoseDict.Xn d → ℂ))
    (A_H : Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m)
    (Ψ₁ Ψ₂ : Work.BoseB4.RealFock m)
    (hAF : A_V (Work.BoseDict.boxRealise e d Ψ₁ + Complex.I • Work.BoseDict.boxRealise e d Ψ₂)
      = A_V (Work.BoseDict.boxRealise e d Ψ₁)
        + Complex.I • A_V (Work.BoseDict.boxRealise e d Ψ₂))
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
    (c : ℝ)
    (hν : 0 < (Work.BoseDict.cIPn d
        (Work.BoseDict.boxRealise e d Ψ₁ + Complex.I • Work.BoseDict.boxRealise e d Ψ₂)
        (Work.BoseDict.boxRealise e d Ψ₁ + Complex.I • Work.BoseDict.boxRealise e d Ψ₂)).re)
    (h : (Work.BoseDict.cIPn d
        (Work.BoseDict.boxRealise e d Ψ₁ + Complex.I • Work.BoseDict.boxRealise e d Ψ₂)
        (A_V (Work.BoseDict.boxRealise e d Ψ₁ + Complex.I • Work.BoseDict.boxRealise e d Ψ₂))).re
      ≤ c * (Work.BoseDict.cIPn d
        (Work.BoseDict.boxRealise e d Ψ₁ + Complex.I • Work.BoseDict.boxRealise e d Ψ₂)
        (Work.BoseDict.boxRealise e d Ψ₁ + Complex.I • Work.BoseDict.boxRealise e d Ψ₂)).re) :
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
  have hnum : (Work.BoseDict.cIPn d
      (Work.BoseDict.boxRealise e d Ψ₁ + Complex.I • Work.BoseDict.boxRealise e d Ψ₂)
      (A_V (Work.BoseDict.boxRealise e d Ψ₁
        + Complex.I • Work.BoseDict.boxRealise e d Ψ₂))).re
      = Work.BoseB4.bomb m Ψ₁ (A_H Ψ₁) + Work.BoseB4.bomb m Ψ₂ (A_H Ψ₂) := by
    have hgen := cIPn_add_I_smul_fn (n := d) A_V
      (Work.BoseDict.boxRealise e d Ψ₁) (Work.BoseDict.boxRealise e d Ψ₂) hAF
      hA00 hA01 hA10 hA11
    rw [hgen, hdict Ψ₁ Ψ₁ hdeg₁ hdeg₁, hdict Ψ₂ Ψ₂ hdeg₂ hdeg₂,
      hdict Ψ₁ Ψ₂ hdeg₁ hdeg₂, hdict Ψ₂ Ψ₁ hdeg₂ hdeg₁]
    simp [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hden : (Work.BoseDict.cIPn d
      (Work.BoseDict.boxRealise e d Ψ₁ + Complex.I • Work.BoseDict.boxRealise e d Ψ₂)
      (Work.BoseDict.boxRealise e d Ψ₁ + Complex.I • Work.BoseDict.boxRealise e d Ψ₂)).re
      = Work.BoseB4.bomb m Ψ₁ Ψ₁ + Work.BoseB4.bomb m Ψ₂ Ψ₂ := by
    have hgen := cIPn_add_I_smul_self_fn (n := d)
      (Work.BoseDict.boxRealise e d Ψ₁) (Work.BoseDict.boxRealise e d Ψ₂)
      hN00 hN01 hN10 hN11
    rw [hgen, hiso Ψ₁ Ψ₁ hdeg₁ hdeg₁, hiso Ψ₂ Ψ₂ hdeg₂ hdeg₂,
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
