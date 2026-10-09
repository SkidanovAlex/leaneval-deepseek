/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Grünwald's theorem in degree `2` (weak approximation for square classes)

For every finite set of places `S` of `ℚ`, the map `ℚˣ/(ℚˣ)² → ∏_{v ∈ S} ℚ_vˣ/(ℚ_vˣ)²` is
surjective.  Because `S` may contain the archimedean place, whose local square class is the sign,
the statement is formulated with a prescribed sign `ε`; the finite places are indexed by an
injective family of primes (`Function.Injective q` is what makes the indexing a *set* of primes).
-/
import Submission.Work.QuadraticLocalGlobal.Defs
import Submission.Work.QuadraticLocalGlobal.grunwald_degree_two_with_sign
import Submission.Work.QuadraticLocalGlobal.isSquare_padic_rat_iff
import Submission.Work.QuadraticLocalGlobal.isSquare_padic_two_rat_iff
import Submission.Work.QuadraticLocalGlobal.isSquare_rat_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.QuadraticLocalGlobal

open Work.HilbertSymbol

/-- **Grünwald's theorem in degree `2`**: every system of prescribed local square classes over a
finite set of primes is realised by a global square class. -/
theorem grunwald_degree_two {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    (hq : Function.Injective q) (c : ∀ i, (ℚ_[q i])ˣ) :
    ∃ d : ℚˣ, ∀ i, SameSquare ((d : ℚ_[q i])) ((c i : (ℚ_[q i])ˣ) : ℚ_[q i]) := by
  obtain ⟨d, -, hloc⟩ := grunwald_degree_two_with_sign q hq c 1
  exact ⟨d, hloc⟩

/-- **Grünwald's theorem in degree `2`, with the archimedean sign.**  The prescribed sign is the
`∞`-component of the local data (locally at `ℝ` a square is a positive number, so the sign is the
only invariant); since multiplying a solution by a negative element that is a local square at all
the prescribed primes flips the sign without changing the finite local classes, the sign is free. -/
theorem grunwald_degree_two' {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    (hq : Function.Injective q) (c : ∀ i, (ℚ_[q i])ˣ) (ε : ℚˣ) :
    ∃ d : ℚˣ, (0 < (d : ℚ) * (ε : ℚ)) ∧
      ∀ i, SameSquare ((d : ℚ_[q i])) ((c i : (ℚ_[q i])ˣ) : ℚ_[q i]) :=
  grunwald_degree_two_with_sign q hq c ε


/-- A consequence in the language of the completions of `ℚ(√d)`: for finitely many odd primes
`q i` there is a positive `d : ℚˣ` which is a square in every `ℚ_[q i]`; equivalently, the
quadratic extension `ℚ_[q i](√d)` is trivial, i.e. `q i` splits completely in `ℚ(√d)`. -/
theorem exists_sqclass_local_square_at_primes {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [∀ i, Fact (q i).Prime] (hq : Function.Injective q) :
    ∃ d : ℚˣ, 0 < (d : ℚ) ∧ ∀ i, ∃ z : (ℚ_[q i])ˣ, z ^ 2 * (d : ℚ_[q i]) = 1 := by
  obtain ⟨d, hpos, hloc⟩ := grunwald_degree_two_with_sign q hq (fun i => 1) 1
  refine ⟨d, by simpa using hpos, fun i => ?_⟩
  obtain ⟨z, hz⟩ := hloc i
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [SameSquare, zero_pow (by norm_num : 2 ≠ 0), zero_mul] at hz
    exact one_ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, by rw [Units.val_mk0]; exact hz⟩


/-- The companion *injectivity* statement of Grünwald's theorem in degree `2`: a rational number
which is a square in `ℝ` and in every `ℚ_p` is a square in `ℚ`.  Together with
`grunwald_degree_two_with_sign` this says that the local square classes are exactly the global
ones subject to the single reciprocity-free condition that the archimedean place sees the sign. -/
theorem isSquare_rat_of_isSquare_padic (x : ℚˣ) (hpos : 0 < (x : ℚ))
    (h : ∀ (p : ℕ) [Fact p.Prime], IsSquare ((x : ℚ_[p]))) : IsSquare ((x : ℚ)) := by
  rw [isSquare_rat_iff]
  refine ⟨hpos, fun p hp => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 2 with rfl | hp2
  · exact ((isSquare_padic_two_rat_iff x).mp (h 2)).1
  · exact ((isSquare_padic_rat_iff hp2 x).mp (h p)).1

end Work.QuadraticLocalGlobal
