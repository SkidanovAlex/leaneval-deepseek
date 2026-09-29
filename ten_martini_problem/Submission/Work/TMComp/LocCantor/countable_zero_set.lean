import Mathlib

namespace Work.TMComp.LocCantor

open Set Filter

/-- The zero set of a function `ℝ → ℂ` which is real-analytic on all of `ℝ` and not
identically zero is countable.

This is the *principle of isolated zeros*: a nonzero analytic function cannot vanish on a set
with an accumulation point.  Concretely, if `Z = f ⁻¹' {0}`, then the complement of `Z` is
codiscrete, which shows that `Z` is discrete; since `f` is continuous, `Z` is also closed.
A closed discrete subset of `ℝ` meets every compact set in a finite set, whence `Z`, being a
countable union of `Z ∩ [-n, n]`, is countable. -/
theorem countable_zero_set (f : ℝ → ℂ) (hf : AnalyticOnNhd ℝ f univ) (hne : f ≠ 0) :
    {x : ℝ | f x = 0}.Countable := by
  set Z : Set ℝ := {x : ℝ | f x = 0} with hZ
  -- The principle of isolated zeros: outside a codiscrete set of points, `f` does not vanish.
  have hcod : ∀ᶠ x in Filter.codiscreteWithin (univ : Set ℝ), f x ≠ 0 := by
    rcases AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected
      (𝕜 := ℝ) (E := ℂ) hf isPreconnected_univ with h | h
    · exact absurd (funext fun x => h (mem_univ x)) hne
    · exact h
  -- Hence the zero set is discrete.
  have hdis : IsDiscrete Z := by
    have h2 := isDiscrete_of_codiscreteWithin (U := (univ : Set ℝ)) (s := Z)
      (show Zᶜ ∈ Filter.codiscreteWithin (univ : Set ℝ) from hcod)
    simpa using h2
  -- And, being the zero set of a continuous function, it is closed.
  have hclosed : IsClosed Z := by
    rw [hZ]
    exact isClosed_eq (continuousOn_univ.mp hf.continuousOn) continuous_const
  -- A closed discrete set meets each compact set in finitely many points.
  have hT : Filter.Tendsto ((↑) : Z → ℝ) Filter.cofinite (Filter.cocompact ℝ) :=
    IsClosed.tendsto_coe_cofinite_of_isDiscrete hclosed hdis
  have hfin : ∀ n : ℕ, Set.Finite (Z ∩ Set.Icc (-(n:ℝ)) (n:ℝ)) := by
    intro n
    have hK : IsCompact (Set.Icc (-(n:ℝ)) (n:ℝ)) := isCompact_Icc
    have h1 := (tendsto_cofinite_cocompact_iff.mp hT) _ hK
    have h2 := Set.Finite.image (Subtype.val : Z → ℝ) h1
    have h3 : (Subtype.val '' (Subtype.val ⁻¹' Set.Icc (-(n:ℝ)) (n:ℝ)))
        = Z ∩ Set.Icc (-(n:ℝ)) (n:ℝ) := Subtype.image_preimage_coe Z _
    rwa [h3] at h2
  -- Finally `Z` is the countable union of the finite sets `Z ∩ [-n, n]`.
  refine Set.Countable.mono ?_ (Set.countable_iUnion fun n => (hfin n).countable)
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_ge |x|
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_inter hx (Set.mem_Icc.mpr (abs_le.mp hn))⟩

end Work.TMComp.LocCantor
