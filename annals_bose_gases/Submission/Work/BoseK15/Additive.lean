import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.Guarded
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.Additive` — the label arithmetic at the pairs §10 uses

`Work.BoseK15.Obstruction` shows that the **global** `Q3Kernel.hasKernel`
identity has no honest instance: on a finite mode system it forces the unguarded
label additivity `kmom (i - j) = kmom i - kmom j` for *all* `i, j`, hence
`kmom ≡ 0` (and `P_H^q = ∅`).  The identity at a pair `(i,j)` is *equivalent* to
that additivity at that pair, so the honest interface must guard it.

This module records the guard as a predicate

    `NoWrap kmom i j  :=  kmom (i - j) = kmom i - kmom j`,

proves the identity on NoWrap pairs (`hasKernel_of_noWrap`), and shows that the
**two** guarded additivities of `K15Input` (`kmom_add`, on `(s, k)` with
`s ∈ supp f_L`, `k ∈ P_H`; and `kmom_add_inner`, on pairs of modes both in
`supp f_L`) imply NoWrap at the four pair families that the §10 estimates
actually rewrite with:

* `(s - k, -k)` and `(k, k - s)` — `Work.BoseB7A.Q3fourT_eq_weight_sum`,
  `Work.BoseB7A.Est1.Algebra`;
* `(s - k, s' - k)` and `(k - s, k - s')` — `Work.BoseB7A.Est1.estT2sum_defs`.

So replacing the global `Q3Kernel.hasKernel` by its NoWrap form costs nothing in
the §10 chain: every application is covered by these four families.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The pair `(i,j)` whose momentum difference does not wrap** in the truncated
mode lattice: the label of the difference is the difference of the labels.  This
is the guard on which FS's `eq:Commutator_general` holds at a finite cutoff
(design §5). -/
def NoWrap {Mode : Type*} [AddCommGroup Mode] (kmom : Mode → ℝ³) (i j : Mode) : Prop :=
  kmom (i - j) = kmom i - kmom j

/-- **The box identity on NoWrap pairs.**  If the commutator kernel of the mode
system is the box kernel at `kmom i - kmom j` and `E`'s `χ̂`, `χ̂²` are read off
the corpus χ at `E.ell • kmom`, then FS `eq:Commutator_general` holds at every
pair whose label arithmetic does not wrap. -/
theorem hasKernel_of_noWrap {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] {F : FockData Mode} {E : Q3Env Mode} (kmom : Mode → ℝ³)
    (hF : ∀ i j : Mode, F.ccrK i j
      = corpusBox.hatChiSq (E.ell • (kmom i - kmom j))
        - corpusBox.hatChi (E.ell • kmom i) * corpusBox.hatChi (E.ell • kmom j))
    (hχ : ∀ k : Mode, E.hatChiSq k = corpusBox.hatChiSq (E.ell • kmom k))
    (hχ1 : ∀ k : Mode, E.hatChi k = corpusBox.hatChi (E.ell • kmom k))
    {i j : Mode} (h : NoWrap kmom i j) :
    F.ccrK i j = E.hatChiSq (i - j) - E.hatChi i * E.hatChi j := by
  rw [hF i j, hχ (i - j), hχ1 i, hχ1 j, h]

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- **The four NoWrap families of §10**, from the two guarded additivities of the
bundle: for `s, s'` localised (`f_L ≠ 0`) and `k ∈ P_H`,

* `(s−k, −k)` and `(k, k−s)` — the pairs rewritten in
  `Work.BoseB7A.Q3fourT_eq_weight_sum` and `Work.BoseB7A.Est1.Algebra`;
* `(s−k, s'−k)` and `(k−s, k−s')` — the pairs rewritten in
  `Work.BoseB7A.Est1.estT2sum_defs` (these also use the *inner* additivity
  `kmom_add_inner`, as both labels are in `supp f_L`). -/
theorem noWrap_used_pairs {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (h : K15Input K₀ F T E) :
    (∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E →
        NoWrap h.kmom (s - k) (-k)) ∧
    (∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E →
        NoWrap h.kmom k (k - s)) ∧
    (∀ s s' k : Mode, E.fL s ≠ 0 → E.fL s' ≠ 0 → k ∈ F.PHset E →
        NoWrap h.kmom (s - k) (s' - k)) ∧
    (∀ s s' k : Mode, E.fL s ≠ 0 → E.fL s' ≠ 0 → k ∈ F.PHset E →
        NoWrap h.kmom (k - s) (k - s')) := by
  have key : ∀ s s' : Mode, E.fL s ≠ 0 → E.fL s' ≠ 0 →
      h.kmom (s - s') = h.kmom s - h.kmom s' := h.kmom_add_inner
  have key2 : ∀ s k : Mode, E.fL s ≠ 0 → k ∈ F.PHset E →
      h.kmom (s - k) = h.kmom s - h.kmom k := h.kmom_add
  have hneg : ∀ i : Mode, h.kmom (-i) = -h.kmom i := h.kmom_neg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s k hs hk
    show h.kmom ((s - k) - (-k)) = h.kmom (s - k) - h.kmom (-k)
    rw [show (s - k) - (-k) = s by abel, key2 s k hs hk, hneg k]
    abel
  · intro s k hs hk
    have hks : h.kmom (k - s) = h.kmom k - h.kmom s := by
      have h1 : h.kmom (-(s - k)) = -h.kmom (s - k) := hneg (s - k)
      rw [show k - s = -(s - k) by abel, h1, key2 s k hs hk]
      abel
    show h.kmom (k - (k - s)) = h.kmom k - h.kmom (k - s)
    rw [show k - (k - s) = s by abel, hks]
    abel
  · intro s s' k hs hs' hk
    show h.kmom ((s - k) - (s' - k)) = h.kmom (s - k) - h.kmom (s' - k)
    rw [show (s - k) - (s' - k) = s - s' by abel, key s s' hs hs',
      key2 s k hs hk, key2 s' k hs' hk]
    abel
  · intro s s' k hs hs' hk
    have hks : ∀ u : Mode, E.fL u ≠ 0 → h.kmom (k - u) = h.kmom k - h.kmom u := by
      intro u hu
      have h1 : h.kmom (-(u - k)) = -h.kmom (u - k) := hneg (u - k)
      rw [show k - u = -(u - k) by abel, h1, key2 u k hu hk]
      abel
    show h.kmom ((k - s) - (k - s')) = h.kmom (k - s) - h.kmom (k - s')
    rw [show (k - s) - (k - s') = s' - s by abel, hks s hs, hks s' hs',
      key s' s hs' hs]
    abel

end Work.BoseK15
