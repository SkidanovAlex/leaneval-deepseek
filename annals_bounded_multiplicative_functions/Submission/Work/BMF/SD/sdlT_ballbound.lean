import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.SD.sd3_defs
import Submission.Work.BMF.SD.window_helpers
import Submission.Work.BMF.primesIn_card_le_pi0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- Ball bound for the scaling-down grid: a sub-family `S` of `fam ×ˢ primesIn a b` (with `fam` a
`500H`-separated source set, `b ≤ 7a/5`) meets a ball of radius `3H/(2a)` in at most
`Cp π₀(a) + 1` pairs, where `Cp` is any Chebyshev-type constant for `#(primesIn P (2P)) ≤ Cp π₀(P)`. -/
lemma sdlT_ballbound {Cp Pp : ℝ}
    (hpi : ∀ P : ℝ, Pp ≤ P →
      ((Work.BMF.primesIn P (2 * P)).card : ℝ) ≤ Cp * Work.BMF.pi0 P)
    {fam : Finset ℝ} {S : Finset (ℝ × ℕ)} {x H a b : ℝ}
    (hS : S ⊆ fam ×ˢ Work.BMF.primesIn a b)
    (hH : 0 < H) (ha : 0 < a) (hbpos : 0 < b) (hb : b ≤ 7 * a / 5)
    (hsep : ∀ y ∈ fam, ∀ y' ∈ fam, y ≠ y' → 500 * H ≤ |y - y'|) (hPpa : Pp ≤ a) :
    ((Work.BMF.ballPairs S x (3 * H / (2 * a))).card : ℝ) ≤ Cp * Work.BMF.pi0 a + 1 := by
  -- `S` lies in the full grid `fam ×ˢ primesIn a b`, so its ball is contained in the full ball.
  have hsub : Work.BMF.ballPairs S x (3 * H / (2 * a)) ⊆
      Work.BMF.ballPairs (fam ×ˢ Work.BMF.primesIn a b) x (3 * H / (2 * a)) :=
    Work.BMF.ballPairs_mono hS
  have hcard1 : (Work.BMF.ballPairs S x (3 * H / (2 * a))).card ≤
      (Work.BMF.ballPairs (fam ×ˢ Work.BMF.primesIn a b) x (3 * H / (2 * a))).card :=
    Finset.card_le_card hsub
  -- At most one source per prime in the ball.
  have hcard2 := Work.BMF.ball_card_le (fam := fam) (a := a) (b := b) (x := x)
    hH ha hbpos hb hsep
  -- `primesIn a b ⊆ primesIn a (2a)`, since `b ≤ 7a/5 ≤ 2a`.
  have hb2a : b ≤ 2 * a := by linarith
  have hsub2 : Work.BMF.primesIn a b ⊆ Work.BMF.primesIn a (2 * a) :=
    primesIn_mono le_rfl hb2a
  have hcard3 : ((Work.BMF.primesIn a b).card : ℝ) ≤
      ((Work.BMF.primesIn a (2 * a)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub2
  have hcard4 : ((Work.BMF.primesIn a (2 * a)).card : ℝ) ≤ Cp * Work.BMF.pi0 a := hpi a hPpa
  have h1 : ((Work.BMF.ballPairs S x (3 * H / (2 * a))).card : ℝ) ≤
      ((Work.BMF.ballPairs (fam ×ˢ Work.BMF.primesIn a b) x (3 * H / (2 * a))).card : ℝ) := by
    exact_mod_cast hcard1
  have h2 : ((Work.BMF.ballPairs (fam ×ˢ Work.BMF.primesIn a b) x
      (3 * H / (2 * a))).card : ℝ) ≤ ((Work.BMF.primesIn a b).card : ℝ) := by
    exact_mod_cast hcard2
  linarith

end Work.BMF.SD
