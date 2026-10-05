import Mathlib
import Submission.Work.RPCore.Chain.C4Defs
import Submission.Work.RPCore.Chain.BvForm_lin

/-!
# `BvForm_radical_quotient`

The diagonal direction `diagVec n` spans the radical of `BvForm n N δ` (both arguments), so
`BvForm` descends to the quotient `ChainSp n ⧸ ℝ ∙ diagVec n`.  This is the "shift invariance"
form of that fact: translating either argument by a multiple of `diagVec n` changes nothing.

The proof is pure bilinearity: `BvForm n N δ` is symmetric, additive and homogeneous in its second
argument and vanishes on `diagVec n` (`BvForm_lin`); symmetry upgrades those to the first
argument and the claim follows by algebra.
-/

namespace Work.RPCore.Chain

open Work.RPV
open scoped BigOperators

noncomputable section

theorem BvForm_radical_quotient (n N : ℕ) (δ : ℝ) (a b : ℝ) (y y' : ChainSp n) :
    BvForm n N δ (a • diagVec n + y) (b • diagVec n + y') = BvForm n N δ y y' := by
  obtain ⟨hsym, hadd, hsmul, hdiag⟩ := BvForm_lin n N δ
  -- additivity in the *first* argument, obtained from symmetry
  have hadd₁ : ∀ z z' z'' : ChainSp n,
      BvForm n N δ (z + z') z'' = BvForm n N δ z z'' + BvForm n N δ z' z'' :=
    fun z z' z'' => by rw [hsym (z + z') z'', hadd z'' z z', hsym z'' z, hsym z'' z']
  -- homogeneity in the *first* argument, obtained from symmetry
  have hsmul₁ : ∀ (c : ℝ) (z z' : ChainSp n),
      BvForm n N δ (c • z) z' = c * BvForm n N δ z z' :=
    fun c z z' => by rw [hsym (c • z) z', hsmul c z' z, hsym z' z]
  -- vanishing on the diagonal in the *first* argument, obtained from symmetry
  have hdiag₁ : ∀ z : ChainSp n, BvForm n N δ (diagVec n) z = 0 :=
    fun z => by rw [hsym (diagVec n) z, hdiag z]
  rw [hadd₁ (a • diagVec n) y (b • diagVec n + y'),
      hsmul₁ a (diagVec n) (b • diagVec n + y'), hdiag₁ (b • diagVec n + y'),
      hadd y (b • diagVec n) y', hsmul b y (diagVec n), hdiag y]
  ring

end

end Work.RPCore.Chain
