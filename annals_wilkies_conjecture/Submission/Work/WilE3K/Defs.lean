/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the corrected separable Khovanskii
  bound for exp/tan chains (`Work.WilE3K.SepKhovanskiiET`), and its derivation from the frozen
  `E2_khovanskii`.

  `Work.WilE3.SepKhovanskiiLocal` (with a *bounded* domain `D`) is FALSE, see
  `sources/wilkiesE3E9/wilkies_E3E9_gaps.md` §GAP 1.  The corrected statement below is the design
  file `sources/wilkiesE3E9/wilkies_E3E9_gaps.lean`'s `WilkiesDesign.E.Gaps.SepKhovanskiiET`, with
  the body unchanged.  Area E3 imports THIS definition and carries `SepKhovanskiiET F` as the
  hypothesis `hK` of `Work.WilE3.MultiplicityBound` (node K4).  This definition is frozen: never
  change it.

  Conventions of the statement (see the design's §GAP 1 for proofs):
  * `D` is *convex*, so `ℓ_j '' D` is an interval inside `dom j`; since `hderiv` forces `dom j` to
    miss the poles of `tan`, a `tan` chain function lives on ONE branch of `tan`.
  * only the chain types E3 uses are allowed: `exp` (`R = X`) and `tan` (`R = 1 + X²`).
  * the right-hand side is the same as in `SepKhovanskiiLocal`.
-/
import Submission.Work.WilE3.Sep
import Submission.Work.WilE3.Defs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

set_option linter.unusedVariables false

/-- **The corrected separable Khovanskii bound** (this replaces `Work.WilE3.SepKhovanskiiLocal`).
* `D` is *convex*, so every `ℓ_j '' D` is an interval inside `dom j`.  Since `hderiv` forces `dom j`
  to miss the poles of `tan`, a `tan` chain function lives on ONE branch.
* Only the chain types E3 uses are allowed: `exp` (`R = X`) and `tan` (`R = 1 + X²`).
The right-hand side is the same as in `SepKhovanskiiLocal`, so E3's `MultiplicityBound_proved`
only changes in one place. -/
def SepKhovanskiiET (F : ℕ) : Prop :=
  ∃ p : Polynomial ℕ, ∀ (n r : ℕ) (S : Work.WilE3.SepChainLocal n r)
      (f : Fin n → EAPoly n r) (D : Set (Fin n → ℝ)) (s : Finset (Fin n → ℝ)), n + r ≤ F →
    (∀ j, (S.phi j = Real.exp ∧ S.R j = MvPolynomial.X 0) ∨
          (S.phi j = Real.tan ∧ S.R j = 1 + MvPolynomial.X 0 ^ 2)) →
    Convex ℝ D →
    (∀ x ∈ D, ∀ j, (∑ i, S.a j i * x i + S.b j) ∈ S.dom j) →
    (↑s : Set (Fin n → ℝ)) ⊆ D →
    (∀ x ∈ s, S.Nondegen f x) →
    s.card ≤ p.eval (∑ i, atomDeg (f i) + ∑ j, (S.R j).totalDegree)

end Work.WilE3K
