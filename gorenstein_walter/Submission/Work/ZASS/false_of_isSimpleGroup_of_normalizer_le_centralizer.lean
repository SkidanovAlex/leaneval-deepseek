/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# Simplicity versus `N_G(Q) ≤ C_G(Q)` (Burnside's normal `p`-complement)

Let `G` be a finite group, `q` a prime and `Q` a **nontrivial** Sylow `q`-subgroup.  If
`N_G(Q) ≤ C_G(Q)`, then Burnside's normal `p`-complement theorem (Mathlib's
`MonoidHom.ker_transferSylow_isComplement'`) produces a normal `q`-complement `N ⊴ G` with
`N.IsComplement' Q`.  Since `G` is simple, `N` is `⊥` or `⊤`:

* `N = ⊥` forces `Q = ⊤`, so `G = Q` is a `q`-group — contradicting `¬ IsPGroup q G`;
* `N = ⊤` forces `Q = ⊥` — contradicting nontriviality of `Q`.

Hence a finite simple group that is not a `q`-group cannot have `N_G(Q) ≤ C_G(Q)` for any
nontrivial Sylow `q`-subgroup.

## Note on the formalisation (read this before using the lemmas below)

`Bot (Sylow p G)` does not and cannot exist in Mathlib in any meaningful way — Sylow subgroups
are maximal `p`-subgroups, so when `p ∣ |G|` there are (at least two) nontrivial, pairwise
conjugate ones and the inclusion order has no bottom.  The requested hypothesis
`hQ : Q ≠ ⊥` (with `Q : Sylow q G`), however, needs such an instance to typecheck at all.  It is
therefore supplied below **as a device**: `instBotSylow` is an arbitrary (noncomputable) choice of
Sylow `p`-subgroup.  With it, `hQ : Q ≠ ⊥` reads "`Q` is not the distinguished Sylow".

* `false_of_isSimpleGroup_of_normalizer_le_centralizer` is the statement **exactly as requested**
  and is proved below (it is a genuine "no such configuration" lemma; the conclusion is `False`,
  and the hypothesis is *stronger* than the intended nontriviality, so it is not vacuous in the
  harmful sense — it is the same refutation).
* `false_of_isSimpleGroup_of_normalizer_le_centralizer_subgroup` is the **intended** statement
  (the one the two reviewers of this lemma asked for): nontriviality spelled on the underlying
  subgroup, `(Q : Subgroup G) ≠ ⊥`.  *This* is the usable form and the one callers should use.
-/

namespace Work.ZASS

/-- The `Bot` instance on `Sylow p G` needed to typecheck the literally requested hypothesis
`Q ≠ ⊥`.  It is an arbitrary choice of Sylow `p`-subgroup (noncomputable).  There is no
mathematically canonical bottom Sylow subgroup, so this is an artifact of the statement's
phrasing — see the module docstring. -/
noncomputable instance instBotSylow {p : ℕ} {G : Type*} [Group G] : Bot (Sylow p G) :=
  ⟨Classical.choice (Sylow.nonempty (p := p) (G := G))⟩

/-- **Burnside + simplicity** (intended form): a finite simple group that is not a `q`-group has
no nontrivial Sylow `q`-subgroup `Q` with `N_G(Q) ≤ C_G(Q)`. -/
theorem false_of_isSimpleGroup_of_normalizer_le_centralizer_subgroup {G : Type} [Group G]
    [Finite G] (hs : IsSimpleGroup G) {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hnq : ¬ IsPGroup q G)
    (Q : Sylow q G) (hQ : (Q : Subgroup G) ≠ ⊥)
    (h : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.centralizer ((Q : Subgroup G) : Set G)) : False := by
  classical
  haveI : IsSimpleGroup G := hs
  -- Burnside's normal `q`-complement theorem: `N_G(Q) ≤ C_G(Q)` yields a normal complement.
  let N : Subgroup G := (MonoidHom.transferSylow Q h).ker
  have hNnormal : N.Normal := MonoidHom.normal_ker _
  have hcomp : N.IsComplement' (Q : Subgroup G) := by
    simpa [N] using MonoidHom.ker_transferSylow_isComplement' Q h
  -- `N` is normal in the simple group `G`, hence `⊥` or `⊤`.
  rcases hNnormal.eq_bot_or_eq_top with hNbot | hNtop
  · -- `N = ⊥`, so the complement condition gives `Q = ⊤`: `G` is a `q`-group.
    have hQtop : (Q : Subgroup G) = ⊤ := by
      have h' := hcomp
      rw [hNbot] at h'
      exact Subgroup.isComplement'_bot_left.mp h'
    have htop : IsPGroup q (⊤ : Subgroup G) := by
      rw [← hQtop]; exact Q.isPGroup'
    exact hnq (htop.of_equiv Subgroup.topEquiv)
  · -- `N = ⊤`, so the complement condition gives `Q = ⊥`, contradicting `hQ`.
    have hQbot : (Q : Subgroup G) = ⊥ := by
      have h' := hcomp
      rw [hNtop] at h'
      exact Subgroup.isComplement'_top_left.mp h'
    exact hQ hQbot

theorem false_of_isSimpleGroup_of_normalizer_le_centralizer {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G) {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (hnq : ¬ IsPGroup q G) (Q : Sylow q G) (hQ : Q ≠ ⊥) (h : Subgroup.normalizer (Q : Set G) ≤ Subgroup.centralizer ((Q : Subgroup G) : Set G)) : False := by
  classical
  rcases eq_or_ne (Q : Subgroup G) ⊥ with hQbot | hQne
  · -- The underlying subgroup of `Q` is trivial. All Sylow `q`-subgroups are then trivial
    -- (their common order is `q ^ (Nat.card G).factorization q = 1`), so `Q` equals the
    -- distinguished Sylow `⊥`, contradicting `hQ`.
    have hsize : ∀ S : Sylow q G, (S : Subgroup G) = ⊥ := by
      intro S
      rw [← Subgroup.card_eq_one, Sylow.card_eq_multiplicity]
      have hQ1 : q ^ (Nat.card G).factorization q = 1 := by
        rw [← Sylow.card_eq_multiplicity Q, hQbot, Subgroup.card_bot]
      exact hQ1
    exact hQ (Sylow.ext (by rw [hsize ⊥, hsize Q]))
  · exact false_of_isSimpleGroup_of_normalizer_le_centralizer_subgroup hs hq hnq Q hQne h

end Work.ZASS
