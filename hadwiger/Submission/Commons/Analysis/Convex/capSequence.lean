import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Submission.Commons.Analysis.Convex.exists_separating_halfplane

open Set

namespace Commons.Analysis.Convex

/-- Every compact convex set in a finite-dimensional real inner product space is the
intersection of countably many closed half-spaces, each of which strictly contains the set.

Concretely: there are sequences `u : ℕ → V` and `c : ℕ → ℝ` such that each half-space
`{x | c n ≤ ⟪u n, x⟫}` contains `D` strictly (`c n < ⟪u n, x⟫` for all `x ∈ D`), while the
intersection of all these half-spaces is contained in `D`.

The complement `Dᶜ` is covered by the open half-planes
`{x | ⟪u_y, x⟫ < c_y}` strictly avoiding `D` (one for each exterior point `y`, obtained from
strong separation).  Since `V` is finite-dimensional over `ℝ` it is second-countable, hence
hereditarily Lindelöf, so countably many of these half-planes already cover `Dᶜ`. -/
theorem capSequence
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] (D : Set V)
    (hDconv : Convex ℝ D) (hDcpt : IsCompact D) (hDne : D.Nonempty) :
    ∃ u : ℕ → V, ∃ c : ℕ → ℝ,
      (∀ n : ℕ, ∀ x ∈ D, c n < inner ℝ (u n) x) ∧
      ((⋂ n : ℕ, {x : V | c n ≤ inner ℝ (u n) x}) ⊆ D) := by
  classical
  -- Separation, repackaged: for each exterior point `y` we get a pair `(u, c)` with a strict
  -- margin on `D` and with `y` strictly inside the open half-plane `{x | ⟪u, x⟫ < c}`.
  have hsepPair : ∀ y : V, y ∉ D →
      ∃ p : V × ℝ, (∀ x ∈ D, p.2 < inner ℝ p.1 x) ∧ inner ℝ p.1 y < p.2 := by
    intro y hy
    rcases exists_separating_halfplane (D := D) hDconv hDcpt hDne hy with ⟨u, c, hu, hyc⟩
    exact ⟨(u, c), hu, hyc⟩
  -- Selection function: genuine separating pair if `y ∉ D`, junk `(0, -1)` otherwise (this
  -- keeps the strict-margin condition valid for *every* index).
  let sel : V → V × ℝ := fun y =>
    if h : y ∈ D then (0, -1) else Classical.choose (hsepPair y h)
  have sel_margin : ∀ y : V, ∀ x ∈ D, (sel y).2 < inner ℝ (sel y).1 x := by
    intro y x hx
    by_cases hyD : y ∈ D
    · simp [sel, hyD]
    · have hs := Classical.choose_spec (hsepPair y hyD)
      dsimp [sel]
      rw [dif_neg hyD]
      exact hs.1 x hx
  have sel_contains : ∀ y : V, y ∉ D → inner ℝ (sel y).1 y < (sel y).2 := by
    intro y hyD
    have hs := Classical.choose_spec (hsepPair y hyD)
    dsimp [sel]
    rw [dif_neg hyD]
    exact hs.2
  -- The family of open half-planes `H y = {x | ⟪(sel y).1, x⟫ < (sel y).2}`.
  let H : V → Set V := fun y => {x : V | inner ℝ (sel y).1 x < (sel y).2}
  have hHopen : ∀ y : V, IsOpen (H y) := by
    intro y
    dsimp [H]
    refine isOpen_lt (f := fun x : V => inner ℝ (sel y).1 x) (g := fun _ : V => (sel y).2) ?_ ?_
    · exact Continuous.inner continuous_const continuous_id
    · exact continuous_const
  -- Every exterior point lies in its own half-plane, so `Dᶜ` is covered.
  have hcover : (Dᶜ : Set V) ⊆ ⋃ y : V, H y := by
    intro x hx
    have hxD : x ∉ D := by simpa using hx
    refine mem_iUnion.mpr ⟨x, ?_⟩
    exact sel_contains x hxD
  -- `V` is second-countable (finite-dimensional over `ℝ`), hence hereditarily Lindelöf:
  -- `Dᶜ` has a countable subcover by these half-planes.
  have hLind : IsLindelof (Dᶜ : Set V) := HereditarilyLindelofSpace.isLindelof (Dᶜ : Set V)
  obtain ⟨f, hfcover⟩ := IsLindelof.indexed_countable_subcover hLind H hHopen hcover
  -- The countably many selected half-planes give the desired sequences.
  refine ⟨fun n => (sel (f n)).1, fun n => (sel (f n)).2, ?_, ?_⟩
  · intro n x hx
    exact sel_margin (f n) x hx
  · intro x hx
    by_contra hxD
    have hxDc : x ∈ (Dᶜ : Set V) := by simpa using hxD
    have hxU : x ∈ ⋃ n : ℕ, H (f n) := hfcover hxDc
    rcases mem_iUnion.mp hxU with ⟨n, hn⟩
    have hle : (sel (f n)).2 ≤ inner ℝ (sel (f n)).1 x := by
      have := mem_iInter.mp hx n
      simpa using this
    have hlt : inner ℝ (sel (f n)).1 x < (sel (f n)).2 := by
      simpa [H] using hn
    linarith

end Commons.Analysis.Convex