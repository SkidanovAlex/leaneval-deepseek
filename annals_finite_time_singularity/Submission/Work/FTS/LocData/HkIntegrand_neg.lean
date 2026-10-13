/-
# `Work.FTS.LocData.HkIntegrand_neg` — sign invariance of the `ℋ^k`-integrand

The `ℋ^k`-integrand of `Work.Spaces` is a sum of *squares* of weighted `D`-derivatives of `f`,

  `HkIntegrand α k f z θ = ∑ᵢ (D_z^i f · w/sin(2θ)^{η/2})²
     + ∑ᵢ ∑ⱼ [1 ≤ i, i+j ≤ k] (D_z^j D_θ^i f · W)²`,

and the totalised derivative `deriv` is *odd* (`deriv.neg`), so `D_z` and `D_θ` — and therefore
every iterate `D_z^j D_θ^i` — commute with pointwise negation.  Each square is consequently
invariant, and with it the whole integrand:

  `HkIntegrand α k (fun z θ => -f z θ) z θ = HkIntegrand α k f z θ`.

This is the pointwise-integrand form of the sign invariance of the `ℋ^k`-seminorm used by
`Work.FTS.LocData.HkSq_neg`/`HkMem_neg`: the localised datum `locG = - zfar L F_* + β h` of the
chapter is obtained by *subtracting* the profile, so all its `ℋ^k` data are those of the profile
together with those of the perturbation, and the estimates must be insensitive to the overall
sign.

All the operator-negation lemmas are proved here, privately, so that this module depends on
nothing but `Work.Spaces.Defs` (in particular it inherits no unfinished sub-proof from a
sibling development).
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The calculus of pointwise negation

`deriv` is odd, hence so is each of the operators `pz`, `pth`, `Dz`, `Dth` and each of their
iterates; `mixed j i = D_z^j D_θ^i` then inherits the property. -/

/-- `(fun z θ => -f z θ)` is the pointwise negation of `f`, definitionally. -/
private lemma neg_fun_eq (f : ℝ → ℝ → ℝ) : (fun z θ => -f z θ) = -f := rfl

private lemma pz_neg_fun (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => -f z θ) = fun z θ => -(Work.Spaces.pz f z θ) := by
  funext z θ
  simp only [Work.Spaces.pz]
  exact deriv.neg

private lemma pth_neg_fun (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => -f z θ) = fun z θ => -(Work.Spaces.pth f z θ) := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv.neg

private lemma Dz_neg_fun (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => -f z θ) = fun z θ => -(Work.Spaces.Dz f z θ) := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_neg_fun]
  ring

private lemma Dth_neg_fun (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => -f z θ) = fun z θ => -(Work.Spaces.Dth f z θ) := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_neg_fun]
  ring

private lemma DzIter_neg_fun (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DzIter n (fun z θ => -f z θ)
      = fun z θ => -(Work.Spaces.DzIter n f z θ) := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      exact Dz_neg_fun (Work.Spaces.DzIter n f)

private lemma DthIter_neg_fun (f : ℝ → ℝ → ℝ) (n : ℕ) :
    Work.Spaces.DthIter n (fun z θ => -f z θ)
      = fun z θ => -(Work.Spaces.DthIter n f z θ) := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      exact Dth_neg_fun (Work.Spaces.DthIter n f)

private lemma mixed_neg_fun (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => -f z θ)
      = fun z θ => -(Work.Spaces.mixed j i f z θ) := by
  have h1 := DthIter_neg_fun f i
  have h2 := DzIter_neg_fun (Work.Spaces.DthIter i f) j
  simp only [Work.Spaces.mixed]
  rw [h1]
  exact h2

/-! ## The integrand -/

/-- **Sign invariance of the `ℋ^k`-integrand**: replacing `f` by `-f` changes none of the
squares of weighted derivatives out of which `HkIntegrand` is built. -/
theorem HkIntegrand_neg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => -f z θ) z θ
      = Work.Spaces.HkIntegrand α k f z θ := by
  simp only [Work.Spaces.HkIntegrand]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  · rw [DzIter_neg_fun]
    ring
  · split_ifs
    · simp only [mixed_neg_fun]; ring
    · ring

end

end Work.FTS.LocData
