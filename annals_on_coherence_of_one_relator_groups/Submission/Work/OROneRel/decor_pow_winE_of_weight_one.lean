import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.coverShift
import Submission.Work.OROneRel.decor_winE_of_red
import Submission.Work.OROneRel.decor_winE_shift
import Submission.Work.OROneRel.winE_mono
import Submission.Work.OROneRel.red_flatten_replicate_wordOf

/-!
# The window of the decorated walk of a power of a weight-one word

Let `c : α → ℤ` be a weight with `cohom c v = ofAdd 1`, i.e. the reduced word `w = wordOf v` has
total weight `lsig c w = 1`.  Suppose moreover that the decorated walk of `v` (the list
`decor c 0 w` of traversals of edges of the `ℤ`-cover) lies in the window `[0, L]`: every decorated
letter `e` has both its endpoints `e.1.2` and `e.1.2 + c e.1.1` in `[0, L]` (this is the content of
the hypotheses `hv` and `hLmax`, the first supplying the lower bounds `0 ≤ ·` — the upper bound `hi`
of `hv` is not needed — and the second the upper bounds `· ≤ L`).

The theorem says that then the decorated walk of the *power* `v ^ n` lies in the window `[0, hi]` as
soon as `hi ≥ L + n - 1`.

The mechanism is the `ℤ`-translation invariance of the window conditions.  The raw `n`-fold
concatenation `W = w ^ n` of the reduced word has, by additivity of `decor` along concatenation
(`decor_append`) and the vanishing of the running increment (`lsig c w = 1` per copy), the decorated
walk

  `decor c 0 W = decor c 0 w ++ decor c 1 w ++ ⋯ ++ decor c (n-1) w`,

and `decor c k w` is the level shift by `k` of `decor c 0 w` (`decor_shift`), so its decorated
letters have both endpoints in `[k, k+L] ⊆ [0, L + n - 1]` (uses `decor_winE_shift` and `winE_mono`).
Finally the reduced word `wordOf (v^n)` is obtained from `W` by a chain of cancellations of adjacent
inverse pairs, and the decoration of a reduction is a sublist of the decoration of the original word
(`decor_sublist_of_red`, transported to the window condition by `decor_winE_of_red`), which concludes.

This is the step that turns a window for the walk of a relator `v` of `c`-weight `1` into a window
for the walk of any power `v ^ n` — the band at level `n` of the `ℤ`-cover of `⟨α | v ^ n⟩`.
-/

namespace Work.OROneRel

theorem decor_pow_winE_of_weight_one {α : Type*} (c : α → ℤ) {v : FreeGroup α} {hi L : ℤ}
    (hL0 : 0 ≤ L)
    (hv : ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf v),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c 0 hi)
    (hLmax : ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf v),
      e.1.2 ≤ L ∧ e.1.2 + c e.1.1 ≤ L)
    (hw : Work.OROneRel.cohom c v = Multiplicative.ofAdd 1)
    (n : ℕ) (hn : L + (n : ℤ) - 1 ≤ hi) :
    ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (v ^ n)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c 0 hi := by
  classical
  -- The reduced word of `v` has total weight `1`.
  have hlsig : Work.OROneRel.lsig c (Work.OROneRel.wordOf v) = 1 := by
    have h1 : Work.OROneRel.cohom c (FreeGroup.mk (Work.OROneRel.wordOf v)) =
        Multiplicative.ofAdd (Work.OROneRel.lsig c (Work.OROneRel.wordOf v)) :=
      Work.OROneRel.cohom_mk c (Work.OROneRel.wordOf v)
    rw [Work.OROneRel.mk_wordOf] at h1
    have h2 : (Multiplicative.ofAdd (Work.OROneRel.lsig c (Work.OROneRel.wordOf v)) :
        Multiplicative ℤ) = Multiplicative.ofAdd 1 := by
      rw [← h1]; exact hw
    exact Multiplicative.ofAdd.injective (by simpa using h2)
  -- The decorated walk of `v` lies in the window `[0, L]`.
  have hwin : ∀ e ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf v),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c 0 L := by
    intro e he
    have h1 := hv e he
    have h2 := hLmax e he
    rw [Work.OROneRel.mem_winE] at h1 ⊢
    exact ⟨h1.1, h2.1, h1.2.2.1, h2.2⟩
  -- The decorated walk of the raw `m`-fold concatenation of `wordOf v` lies in `[0, L + m - 1]`.
  have hflat : ∀ m : ℕ, ∀ e ∈ Work.OROneRel.decor c 0
        (List.flatten (List.replicate m (Work.OROneRel.wordOf v))),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c 0 (L + (m : ℤ) - 1) := by
    intro m
    induction m with
    | zero => intro e he; simp [Work.OROneRel.decor] at he
    | succ m ih =>
      intro e he
      rw [List.replicate_succ, List.flatten_cons, Work.OROneRel.decor_append] at he
      rw [hlsig] at he
      simp only [zero_add] at he
      rcases List.mem_append.mp he with he | he
      · exact Work.OROneRel.winE_mono c (le_refl 0) (by push_cast; omega) (hwin e he)
      · have h2 := Work.OROneRel.decor_winE_shift c 0 1 0 (L + (m : ℤ) - 1)
          (List.flatten (List.replicate m (Work.OROneRel.wordOf v))) ih e he
        refine Work.OROneRel.winE_mono c (by norm_num) ?_ h2
        push_cast; omega
  -- Enlarge the window from `[0, L + n - 1]` to `[0, hi]`.
  have hfin : ∀ e ∈ Work.OROneRel.decor c 0
        (List.flatten (List.replicate n (Work.OROneRel.wordOf v))),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE c 0 hi :=
    fun e he => Work.OROneRel.winE_mono c (le_refl 0) hn (hflat n e he)
  -- Transport from the concatenation to its reduction `wordOf (v ^ n)`.
  exact Work.OROneRel.decor_winE_of_red c 0 hi
    (Work.OROneRel.red_flatten_replicate_wordOf v n) hfin

end Work.OROneRel
