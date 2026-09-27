import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.ProdFlowerLemmas

/-!
# `hT` determines the `mU`-atom inside an `mH`-atom (C5b, fibre independence)

`Work.EKLRelProduct.hT_atom_determines_mU`.  Two points `y, y'` of the same atom of the
`H`-plaque algebra of a product-box flower which have the same `T`-part of their plaque
coordinate lie in the same atom of the `U`-strip algebra: on `atom (mH n) y` the coordinate
changes by left multiplication with an element `h ∈ H`, and the cancellation identity
`Work.EKLProd.prodFlower_tpart_cancel` shows that equality of the `T`-parts forces `hT h = 1`,
i.e. `h ∈ U`; membership in `atom (mU n) y` then follows from the description
`shape (mU n) U y = {u ∈ U : u * co n y ∈ prodBox T U R}` of the `U`-shape.
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelProduct

open Work.EKLContract

/-- Two points of the same atom (of an arbitrary σ-algebra) determine the same atom. -/
theorem atom_eq_of_mem_atom_plaque {m : MeasurableSpace X3} {x y : X3}
    (hy : y ∈ atom m x) : atom m y = atom m x := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rw [atom, Set.mem_sInter] at hz ⊢
    intro s hs
    exact hz s ⟨hs.1, hy s hs⟩
  · intro z hz
    rw [atom, Set.mem_sInter] at hz ⊢
    intro s hs
    have hxs : x ∈ s := by
      by_contra hcon
      exact (hy sᶜ ⟨hs.1.compl, hcon⟩) hs.2
    exact hz s ⟨hs.1, hxs⟩

/-- **The `T`-part of the coordinate determines the `U`-atom.**  If `y, y'` lie in the same
`H`-atom of the `n`-th product-box flower and have the same `T`-part of the plaque coordinate,
then `y'` lies in the `U`-atom of `y`. -/
theorem hT_atom_determines_mU {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u) (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ) {x : Work.EKLContract.X3} (hx : x ∈ hf.Z n)
    {y y' : Work.EKLContract.X3} (hy : y ∈ Work.EKLContract.atom (hf.mH n) x)
    (hy' : y' ∈ Work.EKLContract.atom (hf.mH n) x)
    (hφ : Work.EKLProd.hT T U (hf.co n y) = Work.EKLProd.hT T U (hf.co n y')) :
    y' ∈ Work.EKLContract.atom (hf.mU n) y := by
  classical
  -- both points lie in the domain of the flower
  have hyZ : y ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hx).1 hy
  have hy'Z : y' ∈ hf.Z n := ((hf.plaqH n).2.2.2 x hx).1 hy'
  have hatom : atom (hf.mH n) y = atom (hf.mH n) x := atom_eq_of_mem_atom_plaque hy
  have hy'atom : y' ∈ atom (hf.mH n) y := by rw [hatom]; exact hy'
  -- write `y' = h • y` with `h ∈ H`
  obtain ⟨h, hhH, hhy₀⟩ := ((hf.plaqH n).2.2.2 y hyZ).2.1 hy'atom
  have hhy : h • y = y' := hhy₀
  have hatom_hy : h • y ∈ atom (hf.mH n) y := by rw [hhy]; exact hy'atom
  -- the coordinate is multiplicative along the plaque
  have hco : hf.co n y' = h * hf.co n y := by
    have h := hf.co_smul n y hyZ h hhH hatom_hy
    rwa [hhy] at h
  have hhShape : h ∈ shape (hf.mH n) H y := ⟨hhH, hatom_hy⟩
  -- the `T`-part cancellation
  have hcancel :=
    Work.EKLProd.prodFlower_tpart_cancel hTH hUH hnorm hcop hdisj hf n hyZ hhShape
  rw [← hco, hφ] at hcancel
  have hthin : (Work.EKLProd.hT T U h)⁻¹ = 1 := by
    have h1 : (Work.EKLProd.hT T U h)⁻¹ * Work.EKLProd.hT T U (hf.co n y')
        = 1 * Work.EKLProd.hT T U (hf.co n y') := by
      rw [one_mul]
      exact hcancel
    exact mul_right_cancel h1
  have hth : Work.EKLProd.hT T U h = 1 := by
    rw [← inv_inv (Work.EKLProd.hT T U h), hthin, inv_one]
  -- hence `h ∈ U`
  obtain ⟨g, hgT, u, huU, hgu⟩ := hcop h hhH
  have hdecomp : ∃ a ∈ T, ∃ b ∈ U, h = a * b := ⟨g, hgT, u, huU, hgu⟩
  have hhU : h ∈ U := by
    have hdec : Work.EKLProd.hT T U h * Work.EKLProd.hU T U h = h :=
      Work.EKLProd.hT_mul_hU hdecomp
    rw [← hdec, hth, one_mul]
    exact Work.EKLProd.hU_mem hdecomp
  -- so `h` lies in the `U`-shape of `y`, whence `y' = h • y` is in the `U`-atom of `y`
  have hhShapeU : h ∈ shape (hf.mU n) U y := by
    rw [hf.shapeU n y hyZ]
    exact ⟨hhU, by rw [← hco]; exact hf.co_mem n y' hy'Z⟩
  have hy'atomU : h • y ∈ atom (hf.mU n) y := hhShapeU.2
  rwa [hhy] at hy'atomU

end Work.EKLRelProduct
