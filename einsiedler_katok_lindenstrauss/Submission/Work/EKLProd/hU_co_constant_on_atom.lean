import Mathlib
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.ProdFlowerLemmas
import Submission.Work.EKLProd.prodFlower_slice_avg

namespace Work.EKLProd

open MeasureTheory Work.EKLContract
open scoped ENNReal Pointwise

set_option linter.unusedVariables false

noncomputable section

/-- Uniqueness of the `U`-part of a `T`-`U` decomposition when `T ⊓ U = 1`. -/
theorem hU_unique_of_decomp {T U : Subgroup SL3}
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1) {a a' b b' : SL3}
    (ha : a ∈ T) (hb : b ∈ U) (ha' : a' ∈ T) (hb' : b' ∈ U) (h : a * b = a' * b') :
    b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ U := by rw [h1]; exact U.mul_mem hb' (U.inv_mem hb)
  have h3 : a'⁻¹ * a = 1 := hdisj _ (T.mul_mem (T.inv_mem ha') ha) h2
  have haa : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' * 1 := by rw [h3]
      _ = a' := by rw [mul_one]
  rw [haa] at h
  exact mul_left_cancel h

/-- If `w = a * b` with `a ∈ T`, `b ∈ U` and `T ⊓ U = 1`, then the `U`-part of `w` is `b`. -/
theorem hU_eq_of_factor {T U : Subgroup SL3}
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1) {w a b : SL3}
    (ha : a ∈ T) (hb : b ∈ U) (h : a * b = w) : hU T U w = b := by
  have hex : ∃ a ∈ T, ∃ b ∈ U, w = a * b := ⟨a, ha, b, hb, h.symm⟩
  have hdec : hT T U w * hU T U w = w := hT_mul_hU hex
  exact hU_unique_of_decomp hdisj (hT_mem hex) (hU_mem hex) ha hb
    (by rw [hdec]; exact h.symm)

/-- **The `U`-part of the coordinate is constant on the atoms of the `T`-strip algebra**: the
`T`-atom of a point `x` is the orbit `(T-shape) • x`, along which the coordinate changes by left
multiplication with a `T`-element, and the `U`-part of a `T`-left-multiple coincides with the
`U`-part of the coordinate. -/
theorem hU_co_constant_on_atom {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ)
    (n : ℕ) {x : Work.EKLContract.X3} (hx : x ∈ hf.Z n) {y : Work.EKLContract.X3}
    (hy : y ∈ Work.EKLContract.atom (hf.mT n) x) :
    Work.EKLProd.hU T U (hf.co n y) = Work.EKLProd.hU T U (hf.co n x) := by
  have hsub : atom (hf.mT n) x ⊆ (fun u : SL3 => u • x) '' (T : Set SL3) :=
    ((hf.plaqT n).2.2.2 x hx).2.1
  obtain ⟨t, htT, htx⟩ := hsub hy
  have htx' : t • x = y := htx
  have htH : t ∈ H := hTH htT
  have htShape : t ∈ shape (hf.mT n) T x := ⟨htT, by rw [htx']; exact hy⟩
  have hprod : t * hf.co n x ∈ prodBox T U hf.R := by
    have h := htShape
    rw [hf.shapeT n x hx] at h
    exact h.2
  have htxH : t • x ∈ atom (hf.mH n) x := by
    rw [htx']
    exact atom_subset (hf.alignT n) x hy
  have hco : hf.co n y = t * hf.co n x := by
    rw [← htx']
    exact hf.co_smul n x hx t htH htxH
  obtain ⟨a, ha, b, hb, hab⟩ := hprod
  have hab' : a * b = t * hf.co n x := hab
  obtain ⟨a₀, ha₀, b₀, hb₀, hb₀eq⟩ := hf.co_mem n x hx
  have hb₀eq' : a₀ * b₀ = hf.co n x := hb₀eq
  have hu1 : hU T U (t * hf.co n x) = b := hU_eq_of_factor hdisj ha.2 hb.2 hab'
  have hu0 : hU T U (hf.co n x) = b₀ := hU_eq_of_factor hdisj ha₀.2 hb₀.2 hb₀eq'
  have hbb : b = b₀ := hU_unique_of_decomp hdisj ha.2 hb.2 (T.mul_mem htT ha₀.2) hb₀.2
    (by rw [hab', ← hb₀eq']; group)
  rw [hco, hu1, hbb, hu0]

end

end Work.EKLProd
