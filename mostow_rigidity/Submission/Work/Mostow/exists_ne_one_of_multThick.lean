import Mathlib
import Submission.Work.Mostow.thickDefs

/-!
# `MultThickProp Γ` forces `Γ` to be nontrivial

`MultThickProp Γ` says that the multiplicity-`N` thick part of `Γ` is cocompact, for
every radius `δ > 0` and every bound `N`.  Taking `δ = 1`, `N = 1`: the hypothesis
`{γ : Γ | hdist u (γ • u) < 1}.ncard ≤ 1` must fail to hold for every `u` outside a fixed
compact set.  If `Γ` were trivial, the set in question would be `{1}` (of cardinality `1`)
for **every** `u`, so the cocompactness would force the compact set to contain all of `E n`,
which is impossible as soon as `E n` is non-compact, i.e. `n ≥ 1`.

Hence `Γ` cannot be the trivial group, i.e. it has a nontrivial element.
-/

set_option linter.unusedVariables false

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

theorem exists_ne_one_of_multThick {n : ℕ} (hn : 1 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hmult : Submission.Mostow.MultThickProp Γ) :
    ∃ γ : Γ, γ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ γ : Γ, γ = 1`, i.e. `Γ` is the trivial group
  have hone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  obtain ⟨K, hKc, hKp⟩ := hmult 1 one_pos 1
  -- the multiplicities are bounded by `1` for every point
  have hcond : ∀ u : E n,
      ({γ : Γ | hdist u ((γ : PO n 1) • u) < 1}).Finite ∧
      ({γ : Γ | hdist u ((γ : PO n 1) • u) < 1}).ncard ≤ 1 := by
    intro u
    have hs : ({γ : Γ | hdist u ((γ : PO n 1) • u) < 1} : Set Γ).Subsingleton := by
      intro a _ b _
      rw [hcon a, hcon b]
    exact ⟨hs.finite, (Set.ncard_le_one hs.finite).mpr hs⟩
  -- every element of `Γ` acts trivially
  have hcoe : ∀ γ : Γ, (γ : PO n 1) = 1 := by
    intro γ
    have hh : γ = 1 := hcon γ
    simpa using congrArg (fun x : Γ => (x : PO n 1)) hh
  have h0K : (0 : E n) ∈ K := by
    obtain ⟨γ, hγ⟩ := hKp 0 (hcond 0)
    rw [hcoe γ, hone 0] at hγ
    exact hγ
  -- `K` is bounded, so `E n ⊆ K` is impossible when `n ≥ 1`
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hKc.isBounded
  set a : ℝ := |C| + 1 with ha
  have hapos : 0 < a := by rw [ha]; positivity
  let i : Fin n := ⟨0, by omega⟩
  set u : E n := EuclideanSpace.single i a with hu
  have huK : u ∈ K := by
    obtain ⟨γ, hγ⟩ := hKp u (hcond u)
    rw [hcoe γ, hone u] at hγ
    exact hγ
  have hd : dist u 0 = |C| + 1 := by
    rw [dist_zero_right, hu, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos hapos, ha]
  have hle := hC huK h0K
  rw [hd] at hle
  linarith [le_abs_self C]

end Work.Mostow
