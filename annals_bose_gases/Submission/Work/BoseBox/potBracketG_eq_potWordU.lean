import ChallengeDeps
import Submission.Work.BoseBox.potAmbAux
import Submission.Work.BoseBox.rayl_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.potBracketG_eq_potWordU`

The two spellings of the localised potential word agree:

* `potBracketG N ℓ μ v g u x` — the bracket of `potAmb` in its full-space form: the one-body
  fibre integrals run over **all** of `ℝ³` (`potBr`) and the pair sum runs over the
  *unordered* index set `pairSet N = {(i,j) | i ≠ j}` with the prefactor `1/2`;
* `potWordU N v g ℓ μ u x` — FS `eq:Def_HB`'s multiplicative part: the same fibre integrals
  and the pair sum over the *ordered* index set `{ij : Fin N × Fin N | ij.1 < ij.2}`.

The two differences are exactly:

* `potBr ℓ g u a` **is** `∫_y wLoc ℓ g u a y` (definitional), and
* `(1/2) Σ_{p ∈ pairSet N} w(x_{p.1},x_{p.2}) = Σ_{i<j} w(x_i,x_j)`, which is the
  `pairSet`/`{i<j}` bookkeeping of `sum_pairSet_eq_two_mul_sum_lt` (`rayl_decomp`) applied to
  the **symmetric** kernel `w = wLoc ℓ v u`.  Symmetry of the localised kernel
  (`wLoc_pair_symm`) comes from evenness of the numerator `v` — `v` is *radial*
  (`Submission.BoseGases.radial_even`) — together with evenness of the convolution factor
  `convScale` (`KernelSym.convScale_symm`).  This is the only place where `hvrad` is used.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators

namespace Work.BoseBox

open _root_.BoseGases
open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `wScaled ℓ h` is even when the numerator `h` is even. -/
lemma wScaled_eq_of_neg {h : ℝ³ → ℝ} (hh : ∀ z : ℝ³, h (-z) = h z) (ℓ : ℝ) (z : ℝ³) :
    wScaled ℓ h (-z) = wScaled ℓ h z := by
  unfold wScaled
  rw [hh z, convScale_symm ℓ z]

/-- The localised kernel `wLoc ℓ h u` is symmetric in its two space arguments when the
numerator `h` is even. -/
lemma wLoc_pair_symm {h : ℝ³ → ℝ} (hh : ∀ z : ℝ³, h (-z) = h z) (ℓ : ℝ) (u a b : ℝ³) :
    wLoc ℓ h u a b = wLoc ℓ h u b a := by
  unfold wLoc
  have h1 : wScaled ℓ h (a - b) = wScaled ℓ h (b - a) := by
    rw [show a - b = -(b - a) by abel]
    exact wScaled_eq_of_neg hh ℓ (b - a)
  rw [h1]
  ring

theorem potBracketG_eq_potWordU {N : ℕ} {ℓ μ : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} (hvrad : BoseGases.IsRadial v)
    (u : EuclideanSpace ℝ (Fin 3)) (x : Submission.BoseGases.X N) :
    Work.BoseBox.potBracketG N ℓ μ v (Submission.BoseGases.g0 v h) u x
      = Work.BoseKinLoc.potWordU N v (Submission.BoseGases.g0 v h) ℓ μ u x := by
  have hsym : ∀ i j : Fin N, wLoc ℓ v u (x i) (x j) = wLoc ℓ v u (x j) (x i) :=
    fun i j => wLoc_pair_symm (Submission.BoseGases.radial_even hvrad) ℓ u (x i) (x j)
  have hpair :
      (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N, wLoc ℓ v u (x p.1) (x p.2))
        = ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, wLoc ℓ v u (x ij.1.1) (x ij.1.2) := by
    -- the symmetric `pairSet` sum is twice the sum over the ordered index set `{i < j}`
    have h1 : (∑ p ∈ Submission.BoseGases.pairSet N, wLoc ℓ v u (x p.1) (x p.2))
        = 2 * ∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
            wLoc ℓ v u (x p.1) (x p.2) :=
      sum_pairSet_eq_two_mul_sum_lt (fun i j : Fin N => wLoc ℓ v u (x i) (x j)) hsym
    -- the `Finset`-filtered sum is the sum over the corresponding subtype
    have h2 : (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
            wLoc ℓ v u (x p.1) (x p.2))
        = ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, wLoc ℓ v u (x ij.1.1) (x ij.1.2) :=
      Finset.sum_subtype (s := Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2))
        (p := fun p : Fin N × Fin N => p.1 < p.2)
        (f := fun p : Fin N × Fin N => wLoc ℓ v u (x p.1) (x p.2)) (by intro a; simp)
    rw [h1, h2]
    ring
  simp only [potBracketG, Work.BoseKinLoc.potWordU, potBr]
  rw [hpair]

end Work.BoseBox
