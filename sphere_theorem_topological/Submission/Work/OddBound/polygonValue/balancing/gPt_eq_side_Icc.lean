import Mathlib
import Submission.Work.OddBound.polygonValue.balancing.Defs
import Submission.Work.OddBound.polygonValue.balancing.Book
import Submission.Work.OddBound.polygonValue.balancing.gLoop_pieces

namespace Work.OddBound.polygonValue.balancing

/-- **The point of the balanced broken geodesic on the (closed) side `i`.**  If the arclength
`y` lies between the breakpoints `cumLen τ i` and `cumLen τ (i+1)`, the balanced broken geodesic
of the slice `τ` sits on the side curve `S i · τ`, at the side parameter
`(y - cumLen τ i)/sideLen τ i`.

This is `gPt_eq_side` with the positivity hypothesis on the side length dropped: when the side
`i` has zero length the arclength is forced to be the breakpoint `cumLen τ i`, and both sides of
the identity reduce to the vertex `gonVert p (w τ) i` (`gPt_cumLen_eq_gonVert` on the left,
`hS0` and `zero_div` on the right). -/
theorem gPt_eq_side_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (WithTop.some (⊤ : ENat)) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (WithTop.some (⊤ : ENat)) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {p : M} {N : ℕ} (hN : 0 < N) {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn (modelWithCornersSelf ℝ ℝ) I 1 (fun r : ℝ => S i r τ)
        (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ)) :
    ∀ (i : Fin N) (y : ℝ), y ∈ Set.Icc
        (Work.OddBound.polygonValue.cumLen (I := I) p w τ (i : ℕ))
        (Work.OddBound.polygonValue.cumLen (I := I) p w τ ((i : ℕ) + 1)) →
      Work.OddBound.polygonValue.gPt (I := I) p hN w S τ y
        = S i ((y - Work.OddBound.polygonValue.cumLen (I := I) p w τ (i : ℕ))
            / Work.OddBound.polygonValue.sideLen (I := I) p w τ (i : ℕ)) τ := by
  intro i y hy
  obtain ⟨hy1, hy2⟩ := hy
  have hiN : (i : ℕ) < N := i.isLt
  -- the cumulative length of the next breakpoint is the arclength plus the side length
  have hsucc := cumLen_succ (I := I) p w τ (i : ℕ)
  rcases eq_or_lt_of_le (sideLen_nonneg (I := I) p w τ (i : ℕ)) with hzero | hpos
  · -- degenerate side: the arclength is forced to be the breakpoint itself
    have hyy : y = cumLen (I := I) p w τ (i : ℕ) := by linarith
    subst hyy
    rw [gPt_cumLen_eq_gonVert (I := I) hτ hSsm hS0 hS1 hSlen hN (le_of_lt hiN),
      sub_self, zero_div, hS0 i τ hτ]
  · -- genuine side: `gPt_eq_side`, and the side parameter already lies in `[0,1]`
    have hside := gPt_eq_side (I := I) (p := p) (w := w) (S := S) (τ := τ)
      hτ hSsm hS0 hS1 hSlen hN hiN hpos hy1 hy2
    have hclamp : clamp01 ((y - cumLen (I := I) p w τ (i : ℕ))
        / sideLen (I := I) p w τ (i : ℕ))
        = (y - cumLen (I := I) p w τ (i : ℕ)) / sideLen (I := I) p w τ (i : ℕ) := by
      refine clamp01_eq_self (div_nonneg (by linarith) (le_of_lt hpos)) ?_
      rw [div_le_one hpos]
      linarith
    rw [hside, hclamp]

end Work.OddBound.polygonValue.balancing
