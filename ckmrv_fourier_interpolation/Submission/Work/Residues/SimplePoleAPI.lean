/-
# The API of `Work.Kernels.HasSimplePoleWithResidue`

`Work.Kernels.HasSimplePoleWithResidue f z c` is the `MDifferentiableAt`-based notion of an
(at most) simple pole with residue `c`: the function `τ ↦ f τ - c (τ - z)⁻¹` is holomorphic at
`z`.  It is the notion in which the pole/annihilation bookkeeping of CKMRV Section 5 is
phrased, and this file provides its elementary API:

* sums, scalar multiples, negatives, differences and additive constants;
* uniqueness of the residue;
* the behaviour of the model function `τ ↦ (τ - z)⁻¹` ("behaviour under `τ ↦ z`");
* the bridge to the limit-based `Work.Residues.HasResidue`, and the resulting residue
  calculus (`Work.Residues.HasResidue.sum`).

A word of warning, established by direct computation (and reported by the reviewers of this
chapter): because Lean evaluates `0⁻¹ = 0`, the *definable* kernel value `KPlus d z z` is `0`,
while the limit of `KPlus d τ z` as `τ → z`, `τ ≠ z`, is a nonzero multiple of `Δ(z)^{-1}`
(`Work.Residues.hasResidue_slash_KPlus`).  Hence `Work.Kernels.HasSimplePoleWithResidue` is
*false* (for every `c`) for the diagonal function `z ↦ K z z`; the theorems of this chapter
are therefore stated with `Work.Residues.HasResidue` (a limit statement, insensitive to the
value at the point).  The API below is nevertheless the interface that the Section 5
bookkeeping expects, and is provided for that reason.
-/
import Mathlib
import Submission.Work.Residues.Poles

noncomputable section

open UpperHalfPlane
open Filter
open scoped Topology Manifold

namespace Work.Residues

open Work.Kernels

/-! ## The model function `τ ↦ (τ - z)⁻¹` -/

/-- The constant function has a removable (i.e. no) pole with residue `0`. -/
lemma hasSimplePoleWithResidue_const (z : ℍ) (a : ℂ) :
    HasSimplePoleWithResidue (fun _ : ℍ => a) z 0 := by
  rw [HasSimplePoleWithResidue]
  have h : (fun τ : ℍ => a - (0 : ℂ) * (((τ : ℂ) - (z : ℂ)))⁻¹)
      = fun _ : ℍ => a := by
    funext τ; ring
  rw [h]
  exact mdifferentiableAt_const

/-- The model function `τ ↦ (τ - z)⁻¹` has a simple pole with residue `1` at `z`. -/
lemma hasSimplePoleWithResidue_inv_sub (z : ℍ) :
    HasSimplePoleWithResidue (fun τ : ℍ => (((τ : ℂ) - (z : ℂ)))⁻¹) z 1 := by
  rw [HasSimplePoleWithResidue]
  have h : (fun τ : ℍ => (((τ : ℂ) - (z : ℂ)))⁻¹ - (1 : ℂ) * (((τ : ℂ) - (z : ℂ)))⁻¹)
      = fun _ : ℍ => (0 : ℂ) := by
    funext τ; ring
  rw [h]
  exact mdifferentiableAt_const

/-- The model function `τ ↦ (τ - z)⁻¹` has residue `1` at `z` in the limit sense. -/
lemma hasResidue_inv_sub (z : ℍ) :
    HasResidue (fun τ : ℍ => (((τ : ℂ) - (z : ℂ)))⁻¹) z 1 := by
  rw [HasResidue]
  have h : (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * (((τ : ℂ) - (z : ℂ)))⁻¹)
      =ᶠ[𝓝[≠] z] fun _ : ℍ => (1 : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hτ
    have hτ' : ((τ : ℂ) - (z : ℂ)) ≠ 0 :=
      sub_ne_zero.mpr (fun hh => hτ (UpperHalfPlane.ext hh))
    exact mul_inv_cancel₀ hτ'
  exact Tendsto.congr' h.symm tendsto_const_nhds

/-! ## Algebraic operations -/

lemma HasSimplePoleWithResidue.add {f g : ℍ → ℂ} {z : ℍ} {c d : ℂ}
    (hf : HasSimplePoleWithResidue f z c) (hg : HasSimplePoleWithResidue g z d) :
    HasSimplePoleWithResidue (fun τ => f τ + g τ) z (c + d) := by
  rw [HasSimplePoleWithResidue] at hf hg ⊢
  have h : (fun τ : ℍ => f τ + g τ - (c + d) * (((τ : ℂ) - (z : ℂ)))⁻¹)
      = (fun τ : ℍ => f τ - c * (((τ : ℂ) - (z : ℂ)))⁻¹)
        + (fun τ : ℍ => g τ - d * (((τ : ℂ) - (z : ℂ)))⁻¹) := by
    funext τ; simp only [Pi.add_apply]; ring
  rw [h]
  exact hf.add hg

lemma HasSimplePoleWithResidue.neg {f : ℍ → ℂ} {z : ℍ} {c : ℂ}
    (hf : HasSimplePoleWithResidue f z c) :
    HasSimplePoleWithResidue (fun τ => - f τ) z (-c) := by
  rw [HasSimplePoleWithResidue] at hf ⊢
  have h : (fun τ : ℍ => - f τ - (-c) * (((τ : ℂ) - (z : ℂ)))⁻¹)
      = fun τ : ℍ => - (f τ - c * (((τ : ℂ) - (z : ℂ)))⁻¹) := by
    funext τ; ring
  rw [h]
  exact hf.neg

lemma HasSimplePoleWithResidue.const_mul {f : ℍ → ℂ} {z : ℍ} {c : ℂ} (a : ℂ)
    (hf : HasSimplePoleWithResidue f z c) :
    HasSimplePoleWithResidue (fun τ => a * f τ) z (a * c) := by
  rw [HasSimplePoleWithResidue] at hf ⊢
  have h : (fun τ : ℍ => a * f τ - (a * c) * (((τ : ℂ) - (z : ℂ)))⁻¹)
      = fun τ : ℍ => a * (f τ - c * (((τ : ℂ) - (z : ℂ)))⁻¹) := by
    funext τ; ring
  rw [h]
  exact (mdifferentiableAt_const (c := a) (x := z)).mul hf

lemma HasSimplePoleWithResidue.sub {f g : ℍ → ℂ} {z : ℍ} {c d : ℂ}
    (hf : HasSimplePoleWithResidue f z c) (hg : HasSimplePoleWithResidue g z d) :
    HasSimplePoleWithResidue (fun τ => f τ - g τ) z (c - d) := by
  rw [HasSimplePoleWithResidue] at hf hg ⊢
  have h : (fun τ : ℍ => f τ - g τ - (c - d) * (((τ : ℂ) - (z : ℂ)))⁻¹)
      = (fun τ : ℍ => f τ - c * (((τ : ℂ) - (z : ℂ)))⁻¹)
        - (fun τ : ℍ => g τ - d * (((τ : ℂ) - (z : ℂ)))⁻¹) := by
    funext τ; simp only [Pi.sub_apply]; ring
  rw [h]
  exact hf.sub hg

lemma HasSimplePoleWithResidue.add_const {f : ℍ → ℂ} {z : ℍ} {c : ℂ} (a : ℂ)
    (hf : HasSimplePoleWithResidue f z c) :
    HasSimplePoleWithResidue (fun τ => f τ + a) z c := by
  rw [HasSimplePoleWithResidue] at hf ⊢
  have h : (fun τ : ℍ => f τ + a - c * (((τ : ℂ) - (z : ℂ)))⁻¹)
      = (fun τ : ℍ => f τ - c * (((τ : ℂ) - (z : ℂ)))⁻¹)
        + (fun τ : ℍ => a - (0 : ℂ) * (((τ : ℂ) - (z : ℂ)))⁻¹) := by
    funext τ; simp only [Pi.add_apply]; ring
  rw [h]
  exact hf.add (hasSimplePoleWithResidue_const z a)

/-- Residues of `HasSimplePoleWithResidue` are unique. -/
lemma HasSimplePoleWithResidue.unique {f : ℍ → ℂ} {z : ℍ} {c c' : ℂ}
    (hf : HasSimplePoleWithResidue f z c) (hf' : HasSimplePoleWithResidue f z c') :
    c = c' :=
  (hasResidue_of_hasSimplePoleWithResidue hf).unique
    (hasResidue_of_hasSimplePoleWithResidue hf')

/-! ## The residue calculus for `HasResidue` -/

/-- Residues add over finite sums. -/
lemma HasResidue.sum {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) (c : ι → ℂ) (z : ℍ)
    (h : ∀ i ∈ s, HasResidue (F i) z (c i)) :
    HasResidue (∑ i ∈ s, F i) z (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact hasResidue_zero z
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Work.Residues
