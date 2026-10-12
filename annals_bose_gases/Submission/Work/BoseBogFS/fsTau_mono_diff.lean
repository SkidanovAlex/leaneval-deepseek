import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.BoseB6.Scaled
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Monotonicity and a Lipschitz-type bound for FS's scaled kinetic symbol `τ̃`

`Work.BoseB6.fsTau εT c₁ c₂ r = (1−εT)[|r|−c₁]₊² + εT[|r|−c₂]₊²`
(`Submission/Work/BoseB6/Scaled.lean`) is nondecreasing in `|r|`, and on the positive
half-line it grows at most like `2r`:

`0 ≤ r' ≤ r  ⟹  τ̃(r') ≤ τ̃(r)`  and  `τ̃(r) − τ̃(r') ≤ 2r(r − r')`.

Both statements are consequences of the elementary inequality for a single clamp
`c ≥ 0`: with `s = [r−c]₊`, `s' = [r'−c]₊` one has `0 ≤ s' ≤ s`, `s ≤ r`, `s' ≤ r'`
and `s − s' ≤ r − r'`, whence

`s² − s'² = (s−s')(s+s') ≤ (r−r')(r+r') ≤ (r−r')·2r`.

The two clamps are then combined with the weights `1−εT ≥ 0` and `εT ≥ 0`, whose sum
is `1`; this is exactly why the constant `2r` carries no dependence on `c₁`, `c₂` or `εT`.
-/

noncomputable section

namespace Work.BoseBogFS

/-- Monotonicity of a single clamp: `r' ≤ r` gives `[r'−c]₊² ≤ [r−c]₊²`. -/
private lemma sq_max_mono {c r r' : ℝ} (hrr : r' ≤ r) :
    (max (r' - c) 0) ^ 2 ≤ (max (r - c) 0) ^ 2 :=
  pow_le_pow_left₀ (le_max_right _ _) (max_le_max (by linarith) le_rfl) 2

/-- The Lipschitz-type bound for a single clamp, `c ≥ 0`, `0 ≤ r' ≤ r`:
`[r−c]₊² − [r'−c]₊² ≤ 2r(r−r')`. -/
private lemma sq_max_sub_le {c r r' : ℝ} (hc : 0 ≤ c) (hr' : 0 ≤ r') (hrr : r' ≤ r) :
    (max (r - c) 0) ^ 2 - (max (r' - c) 0) ^ 2 ≤ 2 * r * (r - r') := by
  have hr : 0 ≤ r := le_trans hr' hrr
  have hrr0 : 0 ≤ r - r' := by linarith
  -- facts about `s = [r−c]₊` and `s' = [r'−c]₊`
  have hs0 : 0 ≤ max (r - c) 0 := le_max_right _ _
  have hs'0 : 0 ≤ max (r' - c) 0 := le_max_right _ _
  have hsr : max (r - c) 0 ≤ r := max_le (by linarith) hr
  have hs'r : max (r' - c) 0 ≤ r' := max_le (by linarith) hr'
  -- the key difference bound `s − s' ≤ r − r'`
  have hdiff : max (r - c) 0 - max (r' - c) 0 ≤ r - r' := by
    have h1 : r - c ≤ max (r' - c) 0 + (r - r') := by
      have := le_max_left (r' - c) (0 : ℝ); linarith
    have h2 : (0 : ℝ) ≤ max (r' - c) 0 + (r - r') := by
      have := le_max_right (r' - c) (0 : ℝ); linarith
    have h3 : max (r - c) 0 ≤ max (r' - c) 0 + (r - r') := max_le h1 h2
    linarith
  have key : (max (r - c) 0) ^ 2 - (max (r' - c) 0) ^ 2
      = (max (r - c) 0 - max (r' - c) 0) * (max (r - c) 0 + max (r' - c) 0) := by
    ring
  rw [key]
  have h1 : (max (r - c) 0 - max (r' - c) 0) * (max (r - c) 0 + max (r' - c) 0)
      ≤ (r - r') * (max (r - c) 0 + max (r' - c) 0) :=
    mul_le_mul_of_nonneg_right hdiff (by linarith)
  have h2 : (r - r') * (max (r - c) 0 + max (r' - c) 0) ≤ (r - r') * (r + r') :=
    mul_le_mul_of_nonneg_left (by linarith) hrr0
  have h3 : (r - r') * (r + r') ≤ (r - r') * (2 * r) :=
    mul_le_mul_of_nonneg_left (by linarith) hrr0
  linarith

theorem fsTau_mono_diff {εT c1 c2 r r' : ℝ} (hε0 : 0 ≤ εT) (hε1 : εT ≤ 1)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hr' : 0 ≤ r') (hrr : r' ≤ r) :
    Work.BoseB6.fsTau εT c1 c2 r' ≤ Work.BoseB6.fsTau εT c1 c2 r ∧
      Work.BoseB6.fsTau εT c1 c2 r - Work.BoseB6.fsTau εT c1 c2 r' ≤ 2 * r * (r - r') := by
  have hr : 0 ≤ r := le_trans hr' hrr
  have h1mε : 0 ≤ 1 - εT := by linarith
  rw [Work.BoseB6.fsTau, Work.BoseB6.fsTau, abs_of_nonneg hr, abs_of_nonneg hr']
  refine ⟨?_, ?_⟩
  · -- monotonicity, clamp by clamp
    have hm1 : (max (r' - c1) 0) ^ 2 ≤ (max (r - c1) 0) ^ 2 := sq_max_mono hrr
    have hm2 : (max (r' - c2) 0) ^ 2 ≤ (max (r - c2) 0) ^ 2 := sq_max_mono hrr
    have e1 := mul_le_mul_of_nonneg_left hm1 h1mε
    have e2 := mul_le_mul_of_nonneg_left hm2 hε0
    linarith
  · -- the `2r`-Lipschitz bound
    have hd1 := sq_max_sub_le hc1 hr' hrr
    have hd2 := sq_max_sub_le hc2 hr' hrr
    have e1 := mul_le_mul_of_nonneg_left hd1 h1mε
    have e2 := mul_le_mul_of_nonneg_left hd2 hε0
    have key : (1 - εT) * (2 * r * (r - r')) + εT * (2 * r * (r - r')) = 2 * r * (r - r') := by
      ring
    nlinarith [e1, e2, key]

end Work.BoseBogFS
