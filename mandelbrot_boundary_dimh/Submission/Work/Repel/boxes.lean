import Mathlib
import Submission.Work.Repel.counting
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.chain
import Submission.Work.Repel.box_window_count
import Submission.Work.Repel.triple_cells

/-!
# The cells of Shishikura §6, Step 3

Given the Lemma-6.2 chain `W` (the discs `W_j` in the `ψ_g`-plane) marching to the end indicated
by `sgn`, this file produces a finite family `S` of *cells* `q = (j, k, n)`:

* the fibre `W j + k` lies in the perturbative disc `closedBall (±iη') (η'/4)` of the level-1
  coordinate (`η' = e^{2πη}`) — these are the components of `π₁⁻¹(W_j)` inside `D(η')`
  counted by `Work.Repel.chain_count_copies`;
* the box `box η n` of the level-0 coordinate lies in `Dflat η` — the `π`-preimages of
  `D'(η)` counted by `Work.Repel.box_window_count`;

and with at least `η η'²/(320 (C₀+1))` cells.  The two counting lemmas multiply because the
level-0 and level-1 data are independent: `Work.Repel.triple_cells` combines them.
-/

namespace Work.Repel

/-- **Shishikura §6, Step 3 (the cells).**  If the Lemma-6.2 chain `W` marches to the end
indicated by `sgn` at speed `< C₀ + 1` and one disc lies below the counting region
(`hanchor`), then there are at least `η η'²/(320 (C₀+1))` cells `(j,k,n)` such that the
translate `W j + k` is contained in the perturbative disc `closedBall (±iη') (η'/4)` and the
box `box η n` is contained in `Dflat η` (and non-empty).  Here `η' = e^{2πη}`. -/
theorem boxes {R : ℂ → ℂ} {DR : Set ℂ} {β : ℂ} {ζa ζb : ℂ} {ρ sgn C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W)
    {η : ℝ} (hC : 0 < C₀) (hη : 100 ≤ η)
    (hY : 64 * (C₀ + 1) ≤ Real.exp (2 * Real.pi * η))
    (hanchor : ∃ j₀ : ℕ, ∃ w ∈ W j₀, sgn * w.im < Real.exp (2 * Real.pi * η) / 4) :
    ∃ S : Finset (ℕ × ℤ × ℤ),
      η * (Real.exp (2 * Real.pi * η)) ^ 2 / (320 * (C₀ + 1)) ≤ (S.card : ℝ) ∧
      (∀ q ∈ S, (fun w : ℂ => w + ((q.2.1 : ℤ) : ℂ)) '' W q.1 ⊆
        (if sgn = 1 then Metric.closedBall (Complex.I * Real.exp (2 * Real.pi * η))
            (Real.exp (2 * Real.pi * η) / 4)
          else Metric.closedBall (-Complex.I * Real.exp (2 * Real.pi * η))
            (Real.exp (2 * Real.pi * η) / 4))) ∧
      (∀ q ∈ S, Work.Repel.box η q.2.2 ⊆ Work.Repel.Dflat η ∧ (Work.Repel.box η q.2.2).Nonempty) := by
  -- the level-1 count: at least `η'²/(64(C₀+1))` fibres `W j + k` in `closedBall (±iη') (η'/4)`
  obtain ⟨S₂, hS₂card, hS₂sub⟩ := chain_count_copies h hC hY hanchor
  -- the level-0 count: at least `η/5` boxes `box η n ⊆ Dflat η`
  obtain ⟨T, hTcard, hTbox⟩ := box_window_count η hη
  -- the product of the two independent families
  obtain ⟨S, hScard, hSmem⟩ :=
    triple_cells (B := η / 5) (by linarith) hS₂card hTcard
  refine ⟨S, ?_, ?_, ?_⟩
  · have hC1 : (0 : ℝ) < C₀ + 1 := by linarith
    have heq : (Real.exp (2 * Real.pi * η)) ^ 2 / (64 * (C₀ + 1)) * (η / 5)
        = η * (Real.exp (2 * Real.pi * η)) ^ 2 / (320 * (C₀ + 1)) := by
      field_simp
      ring
    calc η * (Real.exp (2 * Real.pi * η)) ^ 2 / (320 * (C₀ + 1))
        = (Real.exp (2 * Real.pi * η)) ^ 2 / (64 * (C₀ + 1)) * (η / 5) := heq.symm
      _ ≤ (S.card : ℝ) := hScard
  · intro q hq
    exact hS₂sub (q.1, q.2.1) (hSmem q hq).1
  · intro q hq
    exact hTbox q.2.2 (hSmem q hq).2

end Work.Repel
