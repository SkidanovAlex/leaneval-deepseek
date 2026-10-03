/-
# `Work.FIArea6Hecke.R.DiscDefs` — the vocabulary of the disc-sum bound

Objects used by `Work.FIArea6Hecke.R.heckeDiscSum_bound_mean0`.

The key structural facts (all proved in `Work.FIArea6Hecke.R.primaryParam` /
`Work.FIArea6Hecke.R.classDecomposition`) are:

* `IsPrimary z ↔ ∃ w, z = 1 + (2+2i)w` (`pshift`), i.e. the primary elements of `ℤ[i]`
  (paper (5.3)) are exactly one coset `1 + (2+2i)ℤ[i]` of the index-`8` ideal `(2+2i)`;
* `gnorm (pshift w) = 8·(|w + (1-i)/4|²)`, so the disc `{z primary : |z|² ≤ X}` becomes the
  disc `{w : |w + (1-i)/4|² ≤ X/8}` of radius `√(X/8)`;
* for a character `χ` of modulus `4d` vanishing off the units (`IsCharMod4dStrict d χ`),
  `χ` is constant on the classes `z mod 4d`, so the primary disc sum splits as

    `∑_{z primary, |z|² ≤ X} χ(z) = ∑_{p ∈ Pset d} χ(p) · classCount d p X`,

  where `Pset d` is the set of primary residues mod `4d` (a complete residue system for the
  primary coset) and `classCount d p X = #{z : 4d ∣ z - p, |z|² ≤ X}`.

The hypothesis `hmean` of the target is exactly `∑_{p ∈ Pset d} χ(p) = 0`
(`hmean_eq_Pset_sum`), which makes the "main term" `π R² · ∑_p χ(p)` of the class
decomposition vanish.  What is left is the *lattice discrepancy*

  `classCount d p X = π R² + O(R^{1-δ})`,   `R = √X/(4d)`,

which is the classical Gauss-circle bound for a shifted lattice, stated in the
self-contained form `Work.FIArea6Hecke.R.discDiscrepancy_saving`.
-/
import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `2 + 2i ∈ ℤ[i]`: the generator of the ideal `(2+2i) = (1+i)³` whose coset `1 + (2+2i)ℤ[i]`
is the set of primary elements (paper (5.3)). -/
def c2 : GaussianInt := (⟨2, 2⟩ : GaussianInt)

/-- The primary parametrization of `ℤ[i]`: `w ↦ 1 + (2+2i)w`.  By
`isPrimary_iff_pshift` this maps `ℤ[i]` bijectively onto the set of primary elements. -/
def pshift (w : GaussianInt) : GaussianInt := 1 + c2 * w

/-- The square `{0,…,N-1}² ⊆ ℤ[i]`, as a `Finset`. -/
def gsBox (N : ℕ) : Finset GaussianInt :=
  ((Finset.range N).product (Finset.range N)).image
    (fun p : ℕ × ℕ => (⟨(p.1 : ℤ), (p.2 : ℤ)⟩ : GaussianInt))

/-- The primary residues modulo `4d`: the primary elements of the complete residue system
`{0,…,4d-1}² ⊆ ℤ[i]`.  These are exactly the classes modulo `4d` of the primary elements of
`ℤ[i]`, and they form a complete set of representatives for the primary monoid modulo `4d`. -/
def Pset (d : ℕ) : Finset GaussianInt := (gsBox (4 * d)).filter Work.FIPlan.IsPrimary

/-- `classCount d p X = #{z ∈ ℤ[i] : z ≡ p (mod 4d), gnorm z ≤ X}`.  Every such `z` is
automatically primary (since `4d ∈ (2+2i)`). -/
def classCount (d : ℕ) (p : GaussianInt) (X : ℝ) : ℕ :=
  {z : GaussianInt |
      (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (z - p) ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X}.ncard

/-- `shiftCount d p X = #{w ∈ ℤ² : |w + p/(4d)|² ≤ X/(16d²)}`, the count of a shifted lattice
`(p/(4d)) + ℤ²` in the disc of radius `R = √X/(4d)`.  This is `classCount d p X` after the
change of variable `z = p + 4d·w`. -/
def shiftCount (d : ℕ) (p : GaussianInt) (X : ℝ) : ℕ :=
  {w : ℤ × ℤ |
      ((w.1 : ℝ) + (p.re : ℝ) / (4 * (d : ℝ))) ^ 2
        + ((w.2 : ℝ) + (p.im : ℝ) / (4 * (d : ℝ))) ^ 2
      ≤ X / (16 * (d : ℝ) ^ 2)}.ncard

/-- The sum appearing in the hypothesis `hmean` of `heckeDiscSum_bound_mean0`: the character sum
over the primary elements of the complete residue system `{0,…,4d-1}²` modulo `4d`. -/
def hmeanSum (d : ℕ) (chi : GaussianInt → ℂ) : ℂ := by
  classical
  exact ∑ z ∈ (Work.FIPlan.gBox (((4 * d : ℕ) : ℤ) - 1)).filter
      (fun z => Work.FIPlan.IsPrimary z ∧ 0 ≤ z.re ∧ 0 ≤ z.im), chi z

/-- The primary disc sum `∑_{z primary, |z|² ≤ X} χ(z)`, written as a sum over the box
`gBox ⌈X⌉₊` (which contains every `z` with `gnorm z ≤ X` as soon as `X ≥ 1`). -/
def discSum (X : ℝ) (chi : GaussianInt → ℂ) : ℂ := by
  classical
  exact ∑ z ∈ Work.FIPlan.gBox ⌈X⌉₊,
      (if Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X then chi z else 0)

end

end Work.FIArea6Hecke.R
