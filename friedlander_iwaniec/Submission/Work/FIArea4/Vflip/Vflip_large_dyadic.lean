import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.Vflip.VflipAux
import Submission.Work.FIArea4.Vflip.Vfd.VfdMain
import Submission.Work.FIArea4.Vflip.Vfd.Vflip_dyadic_of_class

namespace Work.FIArea4.Vflip

/-- **Friedlander–Iwaniec Proposition 12.1 (12.3)–(12.4), dyadic box, `D > √(RS)`.**
The variance over the dyadic range of moduli `D < d ≤ 2D` of a vector supported in the box
`(R,2R] × (S,2S]` with `(r,2s) = 1` is bounded by `p14T12 D R S ε` times the `τ`-weighted energy.

The proof is the "flipping of moduli" of FI §12: the smooth majorant `bump (d/D)`, the
near/far separation with the cutoff `nearCut a b` (`a = 2S/(HR)`, `b = 2S/R`,
`H = (RS/D)^{1/3}`), the reciprocity flip `pairWeight_flip` of the Jacobi weight, the
Fourier–Mellin separation `separation_ineq_nearCut`, the large sieve at the *flipped* modulus
(`pairSum_large_sieve`, from the hypothesis `h11`), the ν-count `near_count_multi` for the
near-diagonal part, and finally the numerical bookkeeping `numerics_dyadic_logs`. The mod-8
splitting `Vvar_mod8` removes the single-residue-class hypothesis needed by the reciprocity law. -/
theorem Vflip_large_dyadic (ε : ℝ) (hε : 0 < ε) (h11 : Work.FIArea4.p14Prop111All) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      D ≤ R * S → R * S < D * D →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
        Work.FIPlan.Vvar R S D α ≤ C * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α := by
  obtain ⟨C, _hCpos, hC⟩ := Vvar_class_bound h11 ε hε
  exact Vfd.Vflip_dyadic_of_class ε C hC

end Work.FIArea4.Vflip
