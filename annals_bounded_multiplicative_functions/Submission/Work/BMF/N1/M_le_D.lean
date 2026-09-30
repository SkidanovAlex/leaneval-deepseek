import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N1: `M f Y Q ≤ 𝔻 f (χ · n^{it}) Y`

`M f Y Q` is the infimum of `𝔻 f (n ↦ χ(n) n^{it}) Y` over all `|t| ≤ Y` and all Dirichlet
characters `χ` of modulus `q ≤ Q`.  Hence `M f Y Q` is at most the value at any admissible
triple `(t, q, χ)` — this is the elementary "infimum is a lower bound" step used to pass from a
concrete pretentious distance to `M` in node N1 of the MRTTZ pipeline.

The one point that needs care is that the nested `⨅` in the definition of `M` range over
subtypes of `ℝ`, `ℕ+` and `DirichletCharacter ℂ q`, and the ambient order on `ℝ` is only a
conditionally complete linear order: each application of `ciInf_le` therefore demands a lower
bound for the range of the corresponding family.  We supply the uniform lower bound `0`, which is
available because `𝔻 f g Y = √(∑ …) = (∑ …)^{1/2}` is a square root and hence nonnegative.
-/

namespace Work.BMF.N1

open Polynomial Finset Real Complex BoundedMultiplicativeFunctions
open Work.BMF

/-- The pretentious distance `𝔻` is always nonnegative: it is the square root of the
(possibly negative) finite sum `∑_{p ≤ Y} (1 - Re(f(p) conj(g(p)))) / p`, and `y ↦ y^{1/2}`
agrees with `Real.sqrt` there. -/
lemma Ds_nonneg (f g : ℕ → ℂ) (Y : ℝ) : 0 ≤ 𝔻 f g Y := by
  rw [𝔻, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_nonneg _

theorem M_le_D (f : ℕ → ℂ) (Y : ℝ) (Q : ℕ+) (q : ℕ) (hq : 0 < q) (hqQ : q ≤ Q)
    (χ : DirichletCharacter ℂ q) (t : ℝ) (ht : |t| ≤ Y) :
    M f Y Q ≤ 𝔻 f (fun n ↦ χ n * (n : ℂ) ^ (Complex.I * t)) Y := by
  -- The index type of the middle infimum is nonempty, as `q` itself witnesses.
  have hne : Nonempty {r : ℕ+ // r ≤ Q} := ⟨⟨Q, le_rfl⟩⟩
  unfold M
  -- Lower bounds for the three ranges, all given by `0 ≤ 𝔻`.
  have hbdd₁ : BddBelow (Set.range fun s : {s : ℝ // |s| ≤ Y} =>
      ⨅ (r : {r : ℕ+ // r ≤ Q}), ⨅ (ψ : DirichletCharacter ℂ (r : ℕ)),
        𝔻 f (fun n ↦ ψ n * (n : ℂ) ^ (Complex.I * (s : ℝ))) Y) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact le_ciInf fun r => le_ciInf fun ψ => Ds_nonneg f _ Y
  have hbdd₂ : BddBelow (Set.range fun r : {r : ℕ+ // r ≤ Q} =>
      ⨅ (ψ : DirichletCharacter ℂ (r : ℕ)),
        𝔻 f (fun n ↦ ψ n * (n : ℂ) ^ (Complex.I * t)) Y) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact le_ciInf fun ψ => Ds_nonneg f _ Y
  have hbdd₃ : BddBelow (Set.range fun ψ : DirichletCharacter ℂ q =>
      𝔻 f (fun n ↦ ψ n * (n : ℂ) ^ (Complex.I * t)) Y) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨ψ, rfl⟩
    exact Ds_nonneg f _ Y
  -- Evaluate the nested infimum at the admissible triple `(t, q, χ)`.
  exact (ciInf_le hbdd₁ (⟨t, ht⟩ : {t : ℝ // |t| ≤ Y})).trans
    ((ciInf_le hbdd₂ (⟨⟨q, hq⟩, hqQ⟩ : {q : ℕ+ // q ≤ Q})).trans (ciInf_le hbdd₃ χ))

end Work.BMF.N1
