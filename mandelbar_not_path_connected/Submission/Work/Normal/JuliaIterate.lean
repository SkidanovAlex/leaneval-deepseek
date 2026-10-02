import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.JuliaBasics
import Submission.Work.Normal.FilledJulia
import Submission.Work.Normal.juliaSet_comp_self
import Submission.Work.Normal.isCoerciveContinuous_of_isPolynomialMapOfDegree

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Julia set of a polynomial map equals that of each of its iterates

For a polynomial map `f` of degree `d ≥ 1` and `m ≥ 1`, `JuliaSet (f^[m]) = JuliaSet f`.  The
`m`-th iterates of `f` are the iterates of `f^[m]`, which gives one inclusion directly; for the
other one, every iterate of `f` is `f^[j]` applied to an iterate of `f^[m]` for some `0 ≤ j < m`,
and pushing a normal family forward along the coercive continuous map `f^[j]` preserves normality.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial
open Polynomial

/-- Iterates of a polynomial map of degree `d` are again polynomial maps, of degree `d ^ m`. -/
theorem isPolynomialMapOfDegree_iterate {d : ℕ} {f : ℂ → ℂ} (hf : IsPolynomialMapOfDegree d f)
    (m : ℕ) : IsPolynomialMapOfDegree (d ^ m) (f^[m]) := by
  obtain ⟨P, hP, hPf⟩ := hf
  induction m with
  | zero => exact ⟨X, by simp, fun z => by simp⟩
  | succ m ih =>
    obtain ⟨Q, hQ, hQf⟩ := ih
    refine ⟨P.comp Q, ?_, ?_⟩
    · rw [Polynomial.natDegree_comp, hP, hQ, pow_succ']
    · intro z
      rw [Function.iterate_succ_apply', hQf, hPf, Polynomial.eval_comp]

/-- **The Julia set of a polynomial map equals that of each of its positive iterates.** -/
theorem juliaSet_iterate {d : ℕ} {f : ℂ → ℂ} (hd : 1 ≤ d) (hf : IsPolynomialMapOfDegree d f)
    {m : ℕ} (hm : 1 ≤ m) : JuliaSet (f^[m]) = JuliaSet f := by
  have hpoly : ∀ j : ℕ, IsPolynomialMapOfDegree (d ^ j) (f^[j]) :=
    fun j => isPolynomialMapOfDegree_iterate hf j
  have hcoer : ∀ j : ℕ, IsCoerciveContinuous (f^[j]) := fun j =>
    isCoerciveContinuous_of_isPolynomialMapOfDegree (Nat.one_le_pow j d hd) (hpoly j)
  have hcont : ∀ j : ℕ, Continuous (f^[j]) := fun j =>
    continuous_of_isPolynomialMapOfDegree (hpoly j)
  -- `Fatou f ⊆ Fatou (f^[m])`
  have h1 : FatouSet f ⊆ FatouSet (f^[m]) := by
    intro z hz
    obtain ⟨U, hU, hUo, hnorm⟩ := hz
    refine fatouSet_of_mem_nhds hU hUo (hnorm.mono_family ?_)
    rintro g ⟨n, rfl⟩
    exact ⟨m * n, by simpa using Function.iterate_mul f m n⟩
  -- `Fatou (f^[m]) ⊆ Fatou f`
  have h2 : FatouSet (f^[m]) ⊆ FatouSet f := by
    intro z hz
    obtain ⟨U, hU, hUo, hnorm⟩ := hz
    let Fam : ℕ → Set (ℂ → ℂ) := fun j => (fun g => (f^[j]) ∘ g) '' iterateFamily (f^[m])
    have hcomp : ∀ j : ℕ, IsNormalFamily (Fam j) U := by
      intro j
      refine isNormalFamily_image_comp (hcoer j) hUo ?_ hnorm
      intro g hg
      obtain ⟨n, rfl⟩ := hg
      exact (hcont m).iterate n
    -- finite unions of normal families are normal
    have hunion : ∀ s : Finset ℕ, IsNormalFamily (⋃ j ∈ s, Fam j) U := by
      intro s
      induction s using Finset.induction with
      | empty => intro u hu; exact absurd (hu 0) (by simp)
      | insert a s ha ih =>
        have hset : (⋃ j ∈ insert a s, Fam j) = Fam a ∪ ⋃ j ∈ s, Fam j := by
          ext g
          simp only [mem_iUnion, mem_union, Finset.mem_insert]
          constructor
          · rintro ⟨i, rfl | hi, hg⟩
            · exact Or.inl hg
            · exact Or.inr ⟨i, hi, hg⟩
          · rintro (hg | ⟨i, hi, hg⟩)
            · exact ⟨a, Or.inl rfl, hg⟩
            · exact ⟨i, Or.inr hi, hg⟩
        rw [hset]
        exact isNormalFamily_union (hcomp a) ih
    refine fatouSet_of_mem_nhds hU hUo ((hunion (Finset.range m)).mono_family ?_)
    rintro g ⟨n, rfl⟩
    refine mem_iUnion.mpr ⟨n % m, mem_iUnion.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hm),
      (f^[m])^[n / m], ⟨n / m, rfl⟩, ?_⟩⟩
    funext z
    show f^[n % m] ((f^[m])^[n / m] z) = f^[n] z
    rw [← Function.iterate_mul, ← Function.iterate_add_apply, Nat.mod_add_div]
  rw [JuliaSet, JuliaSet, compl_inj_iff]
  exact Subset.antisymm h2 h1

end Work.Normal
