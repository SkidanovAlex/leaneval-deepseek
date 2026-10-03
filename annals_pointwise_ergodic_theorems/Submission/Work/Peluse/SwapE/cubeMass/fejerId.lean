import Mathlib
import Submission.Work.Peluse.SwapE.cubeMass.Defs
import Submission.Work.Peluse.Concat.ofReal_tsum_normSq_eq_pairSum
import Submission.Work.Peluse.TransferUp.arithIcc_pairSum

namespace Work.Peluse.SwapE.cubeMass

/-- The weight `Ncard Card v` is the triangular weight `Card - |v|`. -/
private lemma Ncard_eq (Card : ℕ) (v : ℤ) : Work.Peluse.SwapE.Ncard Card v = Card - v.natAbs := rfl

/-- The conjugation of the lag-`δ` autocorrelation is the autocorrelation with the two factors
exchanged. -/
private lemma star_autocorr_tsum (g : ℤ → ℂ) (δ : ℤ) :
    star (∑' x : ℤ, g x * star (g (x + δ))) = ∑' y : ℤ, star (g y) * g (y + δ) := by
  rw [tsum_star]
  refine tsum_congr (fun x => ?_)
  rw [star_mul, star_star, mul_comm]

theorem fejerId (Card : ℕ) (hC : 1 ≤ Card) (g : ℤ → ℂ) (hg : Work.Peluse.FinSuppZ g) :
    (∑ δ ∈ Work.Peluse.SwapE.sCard Card,
        ((Work.Peluse.SwapE.Ncard Card δ : ℕ) : ℂ) * (∑' x : ℤ, g x * star (g (x + δ))))
      = ((∑' z : ℤ, ‖∑ v ∈ Work.Peluse.arithIcc 1 Card, g (z + v)‖ ^ 2 : ℝ) : ℂ) := by
  classical
  obtain ⟨N, hN⟩ := hg
  -- The pair-sum expansion of the `ℓ²`-mass of the window sums.
  have hpair : ((∑' z : ℤ, ‖∑ v ∈ Work.Peluse.arithIcc 1 Card, g (z + v)‖ ^ 2 : ℝ) : ℂ)
      = ∑ a ∈ Work.Peluse.arithIcc 1 Card, ∑ b ∈ Work.Peluse.arithIcc 1 Card,
          ∑' y : ℤ, star (g y) * g (y + (a - b)) :=
    Work.Peluse.Concat.ofReal_tsum_normSq_eq_pairSum (N := N)
      (Q := Work.Peluse.arithIcc 1 Card) (f := g) hN
  -- Grouping the pairs of the window by their difference.
  have hgroup : (∑ a ∈ Work.Peluse.arithIcc 1 Card,
        ∑ b ∈ Work.Peluse.arithIcc 1 Card, ∑' y : ℤ, star (g y) * g (y + (a - b)))
      = ∑ m ∈ Finset.Icc (-(Card : ℤ) + 1) ((Card : ℤ) - 1),
          (((Card - m.natAbs : ℕ)) : ℂ) * (∑' y : ℤ, star (g y) * g (y + m)) := by
    rw [Finset.sum_comm]
    simpa using Work.Peluse.TransferUp.arithIcc_pairSum (c := 1) one_ne_zero Card
      (fun δ : ℤ => ∑' y : ℤ, star (g y) * g (y + δ))
  -- The index set of the target is the range of the pair-sum grouping.
  have hsCard : Work.Peluse.SwapE.sCard Card
      = Finset.Icc (-(Card : ℤ) + 1) ((Card : ℤ) - 1) := by
    show Finset.Icc (1 - (Card : ℤ)) ((Card : ℤ) - 1) = _
    rw [show (1 : ℤ) - (Card : ℤ) = -(Card : ℤ) + 1 by ring]
  -- Conjugating the left-hand side turns it into the grouped pair sum.
  have hstar : star (∑ δ ∈ Work.Peluse.SwapE.sCard Card,
        ((Work.Peluse.SwapE.Ncard Card δ : ℕ) : ℂ) * (∑' x : ℤ, g x * star (g (x + δ))))
      = ∑ m ∈ Finset.Icc (-(Card : ℤ) + 1) ((Card : ℤ) - 1),
          (((Card - m.natAbs : ℕ)) : ℂ) * (∑' y : ℤ, star (g y) * g (y + m)) := by
    rw [star_sum, hsCard]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Ncard_eq, star_mul, star_natCast, star_autocorr_tsum, mul_comm]
  have hstarL : star (∑ δ ∈ Work.Peluse.SwapE.sCard Card,
        ((Work.Peluse.SwapE.Ncard Card δ : ℕ) : ℂ) * (∑' x : ℤ, g x * star (g (x + δ))))
      = ((∑' z : ℤ, ‖∑ v ∈ Work.Peluse.arithIcc 1 Card, g (z + v)‖ ^ 2 : ℝ) : ℂ) := by
    rw [hstar, ← hgroup, hpair]
  calc (∑ δ ∈ Work.Peluse.SwapE.sCard Card,
        ((Work.Peluse.SwapE.Ncard Card δ : ℕ) : ℂ) * (∑' x : ℤ, g x * star (g (x + δ))))
      = star (star (∑ δ ∈ Work.Peluse.SwapE.sCard Card,
          ((Work.Peluse.SwapE.Ncard Card δ : ℕ) : ℂ) * (∑' x : ℤ, g x * star (g (x + δ))))) :=
        (star_star _).symm
    _ = star ((∑' z : ℤ, ‖∑ v ∈ Work.Peluse.arithIcc 1 Card, g (z + v)‖ ^ 2 : ℝ) : ℂ) := by
        rw [hstarL]
    _ = ((∑' z : ℤ, ‖∑ v ∈ Work.Peluse.arithIcc 1 Card, g (z + v)‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.conj_ofReal]

end Work.Peluse.SwapE.cubeMass
