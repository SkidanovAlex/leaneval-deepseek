import Submission.ZagierHoffmanProof.StepL120
set_option autoImplicit false
set_option maxHeartbeats 200000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L121: the type-2/3 tail prefix bound at the (k₁,j)-chain — first tail
statement (SESSION 258k)

Paper (2.13): the iterated b-fiber tails satisfy
  t_{i₁…i_{k₁−j}} ≤ (q{k₁−j−1}, s_{k₁}−1, s_{k₁+1}, …)
— in the library this is the BCq_fiber_prefix_X instance at the (k₁,j)-chain
data (n := k₁−j−1 iterates, level-0 b-tail bound X from hbndB):
  psum (expTail ((BCqIter n (toData R0)).cB i)) m ≤ n·q + X (m − n),
  X(m) := psumSeq (tupPadSum (single qMinusExp) (consVec (w1Of-at-k₁)
    (sTail-at-k₁))) m   (the (q−1, s_{k₁}−q, s_{k₁+1},…)-prefix, and
    (q−1) + (s_{k₁}−q) = s_{k₁}−1 is the identity matching the paper's
    s_{k₁}−1 entry).  These expTail(level-n .cB) tuples ARE the type-2/3
  member tails after the (front, v, 1)-prefix, so this named fact is the
  type-2/3 counterpart of StepL120's type-1 tail facts.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The type-2/3 iterated b-fiber tail prefix bound at the input's first-bad
index k₁ (paper (2.13), first form): from the level-0 b-tail bound (hbndB) the
n = k₁−j−1-iterate fiber tails satisfy psum (expTail) m ≤ n·q + X (m−n). -/
theorem type23_tail_prefix (k₁ r j : ℕ) (s : Fin r → ℕ+) (hk1 : 1 ≤ k₁) (hkr : k₁ ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k₁ - 1, by omega⟩ : ℕ))
    (hj1 : 1 ≤ j) (hjk : j ≤ k₁ - 1) :
    ∃ (R0 : BinaryRel F) (u : R0.ιA),
      R0.aA u = 1 ∧
      (∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) ∧
      ∀ i : (RelData.BCqIter F (k₁ - j - 1) (toData F R0)).ιB, ∀ m : ℕ,
        psum (expTail ((RelData.BCqIter F (k₁ - j - 1) (toData F R0)).cB i)) m ≤
          (k₁ - j - 1) * Nat.card F +
          psumSeq (tupPadSum (single (qMinusExp F))
            (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr))) (m - (k₁ - j - 1)) := by
  classical
  rcases maink_config_full F k₁ r s hk1 hkr hbig with
    ⟨R0, u, hdepu, hau, hc0, hbhd, hwtA, hhead, hXw, hbndB, hpref, _⟩
  refine ⟨R0, u, hau, hbhd, ?_⟩
  intro i m
  exact BCq_fiber_prefix_X F (k₁ - j - 1) R0 hbhd
    (fun mm : ℕ => psumSeq (tupPadSum (single (qMinusExp F))
      (consVec (w1Of F r s k₁ hk1 hkr hbig) (sTail r s k₁ hkr))) mm)
    hbndB i m

end ZagierHoffmanPositiveChar
