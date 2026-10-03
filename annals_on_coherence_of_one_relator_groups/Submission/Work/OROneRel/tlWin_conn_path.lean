import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.interval_connected_of_wide
import Submission.Work.OROneRel.steps_of_chain
import Submission.Work.OROneRel.exists_word_of_confined_steps
import Submission.Work.OROneRel.decor_winE_shift

namespace Work.OROneRel

/-- The weight of the first generator of the two-letter band. -/
private theorem conn_tlW_zero (p q : ℕ) : tlW p q 0 = (q : ℤ) := by simp [tlW]

/-- The weight of the second generator of the two-letter band. -/
private theorem conn_tlW_one (p q : ℕ) : tlW p q 1 = -(p : ℤ) := by simp [tlW]

/-!
# Connectivity of the two-letter window: a path from level `1` to the level `t`

`Work.OROneRel.tlWin_conn_path`: for coprime `p, q ≥ 1`, `p + q - 1 ≤ m` and `1 ≤ t ≤ m` there is a
word `R` in the free group on two generators with

* `lsig (tlW p q) R = t - 1`, i.e. the walk of `R` started at the level `1` ends at the level `t`,
* every edge of the decorated walk `decor (tlW p q) 1 R` lies in the window `winE (tlW p q) 1 m`,
  i.e. the walk stays inside the band `[1, m]`.

The weight is `tlW p q : a = 0 ↦ q`, `b = 1 ↦ -p`, so the level graph on `ℤ` has steps `±q`
(the letter `a`) and `±p` (the letter `b`), and an edge of the window `winE c 1 m` is exactly a step
both of whose endpoints lie in `[1, m]`.

The proof is the "arithmetic route", shifted so that the walk starts at the level `1`:

* the coprime pair `p, q` satisfies a Bézout relation, so `interval_connected_of_wide` connects the
  level `0` to the level `t - 1` inside the band `[0, m - 1]` (which is `[lo + 1, hi - 1]` for
  `lo = -1`, `hi = m`, and is wide enough precisely because `p + q - 1 ≤ m`);
* `steps_of_chain` turns that chain into a list `ss` of signed steps `±p`, `±q` whose partial sums
  from `0` stay in `[0, m - 1]` and whose total is `t - 1`;
* `exists_word_of_confined_steps` realises the steps by a word `L` whose decorated edges at the
  level `0` are edges of the window `winE (tlW p q) 0 (m - 1)`;
* `decor_winE_shift` shifts the walk by `1`, turning that window into `winE (tlW p q) 1 m`.
-/

theorem tlWin_conn_path (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    {m t : ℤ} (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m) (hm2 : m + 1 ≤ (p : ℤ) * (q : ℤ))
    (ht1 : 1 ≤ t) (ht2 : t ≤ m) :
    ∃ R : List (Fin 2 × Bool), Work.OROneRel.lsig (Work.OROneRel.tlW p q) R = t - 1 ∧
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 1 R,
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 1 m := by
  classical
  -- coprimality gives a Bézout relation for the steps `p` and `q`
  have hc : IsCoprime ((p : ℤ)) ((q : ℤ)) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hcop
  obtain ⟨a, b, hab⟩ := hc
  have hpz : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hqz : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hm : (1 : ℤ) ≤ m := by linarith
  -- the band `[0, m - 1]` is `[lo + 1, hi - 1]` for `lo = -1`, `hi = m`, and wide enough
  have hwide : (p : ℤ) + (q : ℤ) ≤ m - (-1 : ℤ) := by linarith
  have hconn := interval_connected_of_wide (A := (p : ℤ)) (B := (q : ℤ)) hpz hqz ⟨a, b, hab⟩
    (-1) m hwide 0 (t - 1) (by linarith) (by linarith) (by linarith) (by linarith)
  -- forget the conditions on the sources of the steps
  have hstep_to : ∀ x y : ℤ,
      ((-1 : ℤ) + 1 ≤ x ∧ x ≤ m - 1 ∧ (-1 : ℤ) + 1 ≤ y ∧ y ≤ m - 1 ∧
        (y = x + (p : ℤ) ∨ y = x - (p : ℤ) ∨ y = x + (q : ℤ) ∨ y = x - (q : ℤ))) →
      ((0 : ℤ) ≤ y ∧ y ≤ m - 1 ∧
        (y = x + (p : ℤ) ∨ y = x - (p : ℤ) ∨ y = x + (q : ℤ) ∨ y = x - (q : ℤ))) :=
    fun x y h => ⟨by linarith [h.2.2.1], h.2.2.2.1, h.2.2.2.2⟩
  have hchain : Relation.ReflTransGen (fun x y : ℤ => (0 : ℤ) ≤ y ∧ y ≤ m - 1 ∧
      (y = x + (p : ℤ) ∨ y = x - (p : ℤ) ∨ y = x + (q : ℤ) ∨ y = x - (q : ℤ))) 0 (t - 1) := by
    suffices ∀ z : ℤ, Relation.ReflTransGen (fun x y : ℤ => (-1 : ℤ) + 1 ≤ x ∧ x ≤ m - 1 ∧
        (-1 : ℤ) + 1 ≤ y ∧ y ≤ m - 1 ∧
        (y = x + (p : ℤ) ∨ y = x - (p : ℤ) ∨ y = x + (q : ℤ) ∨ y = x - (q : ℤ))) 0 z →
        Relation.ReflTransGen (fun x y : ℤ => (0 : ℤ) ≤ y ∧ y ≤ m - 1 ∧
        (y = x + (p : ℤ) ∨ y = x - (p : ℤ) ∨ y = x + (q : ℤ) ∨ y = x - (q : ℤ))) 0 z from
      this (t - 1) hconn
    intro z hz
    induction hz with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih => exact ih.tail (hstep_to _ _ hbc)
  obtain ⟨ss, hst, hsum, hscan⟩ := steps_of_chain hchain ⟨le_refl 0, by linarith⟩
  -- realise the steps by letters; the weight of the letter `a` is `q`, that of `b` is `-p`
  obtain ⟨L, hLsig, hLwin⟩ := exists_word_of_confined_steps (tlW p q) (0 : Fin 2) (1 : Fin 2)
    (q : ℤ) (-(p : ℤ)) (by omega) (by omega) (by omega)
    (Or.inl (conn_tlW_zero p q)) (Or.inl (conn_tlW_one p q))
    ss (by
      intro s hs
      rcases hst s hs with h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (by rw [h]; ring)))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)) 0 (m - 1) hscan
  refine ⟨L, ?_, ?_⟩
  · rw [hLsig, hsum]; ring
  · -- shift the decorated walk from the level `0` to the level `1`
    have hsh := decor_winE_shift (tlW p q) 0 1 0 (m - 1) L hLwin
    intro e he
    have h2 := hsh e (by simpa using he)
    simpa using h2

end Work.OROneRel
