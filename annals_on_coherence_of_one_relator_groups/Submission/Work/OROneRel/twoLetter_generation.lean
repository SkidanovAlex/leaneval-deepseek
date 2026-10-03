/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# The generation plank of the two-letter band (`c = tlW p q`, band window `[0, p q]`)

For the two-letter relator `u = tlU p q = a ^ p * b ^ q` (coprime exponents) and the band window of
the weight `tlW p q` (`a ↦ q`, `b ↦ -p`, the window is the band `[0, p q]`), this file provides the
**generation plank** of the `Z`-domain (Magnus--Moldavanskii) splitting:

  `winVertex Wt (tlW p q) 0 (p q) (tlU p q) l ⊔ ⟪mk τ⟫ = ⊤`

for a suitable deck element `τ` of weight one -- namely the *low* deck element `tlLowTau p q` whose
walk stays inside `[0, L]` with `L + max p q - 1 ≤ p q` (`Work.OROneRel.twoLetterLowTauBound`).

The point of the `low` deck element: the walks of `τ ^ q` and `τ ^ p` are then *confined to the
band*, so that the level factors `mk (τ ^ i) * (mk τ) ^ (-i)` at the two levels used for each
generator (`0`, `q` for `a` and `p`, `0` for `b`) are visible inside the window vertex by the
in-band-walk criterion; this is `Work.OROneRel.decor_pow_winE_of_weight_one` fed into
`Work.OROneRel.winVertex_generation_of_walk_containment_at_levels`.  No pin (and hence no
`Z`-domain splitting) is needed for the generation.

## Contents

* `tlLowTau`, `tlLowTauL` and their interface (`tlLowTau_cohom`, `tlLowTau_walk`,
  `tlLowTau_levels`, `tlLowTauL_bound`): the low deck element of the band;
* `cohom_tlW_tlU_local`: `cohom (tlW p q) (tlU p q) = 1`;
* `tlLowTau_pow_walk`: the walks of the powers `τ ^ n`, `n ≤ max p q`, stay in the band;
* `twoLetter_generation`: the generation plank itself.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.twoLetterLowTauBound
import Submission.Work.OROneRel.decor_pow_winE_of_weight_one
import Submission.Work.OROneRel.winVertex_generation_of_walk_containment_at_levels

namespace Work.OROneRel

/-! ## The deck element of the band window

`tlLowTau p q` is the deck element produced by `Work.OROneRel.twoLetterLowTauBound`: a word of
weight one whose walk in the `Z`-cover of the band stays inside `[0, L]` with
`L + max p q - 1 ≤ p q`.  Everything below only uses the interface of that lemma. -/

/-- **The deck element of the two-letter band.**  A word of weight `1` for the weight `tlW p q`
whose walk lies in the band `[0, 1]`-wise low: see `tlLowTau_cohom`, `tlLowTau_walk`,
`tlLowTau_levels` and `tlLowTauL_bound` for its properties. -/
noncomputable def tlLowTau (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    FreeGroup (Fin 2) :=
  (twoLetterLowTauBound p q hp hq hcop).choose

/-- **The top level of the walk of `tlLowTau`.** -/
noncomputable def tlLowTauL (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) : ℤ :=
  (twoLetterLowTauBound p q hp hq hcop).choose_spec.choose

theorem tlLowTau_cohom (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    cohom (tlW p q) (tlLowTau p q hp hq hcop) = Multiplicative.ofAdd 1 :=
  (twoLetterLowTauBound p q hp hq hcop).choose_spec.choose_spec.1

theorem tlLowTauL_nonneg (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    0 ≤ tlLowTauL p q hp hq hcop :=
  (twoLetterLowTauBound p q hp hq hcop).choose_spec.choose_spec.2.1

theorem tlLowTauL_bound (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    tlLowTauL p q hp hq hcop + max (p : ℤ) (q : ℤ) - 1 ≤ (p : ℤ) * (q : ℤ) :=
  (twoLetterLowTauBound p q hp hq hcop).choose_spec.choose_spec.2.2.1

theorem tlLowTau_walk (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    ∀ e ∈ decor (tlW p q) 0 (wordOf (tlLowTau p q hp hq hcop)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)) :=
  (twoLetterLowTauBound p q hp hq hcop).choose_spec.choose_spec.2.2.2.1

theorem tlLowTau_levels (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q) :
    ∀ e ∈ decor (tlW p q) 0 (wordOf (tlLowTau p q hp hq hcop)),
      e.1.2 ≤ tlLowTauL p q hp hq hcop ∧
        e.1.2 + tlW p q e.1.1 ≤ tlLowTauL p q hp hq hcop :=
  (twoLetterLowTauBound p q hp hq hcop).choose_spec.choose_spec.2.2.2.2

/-! ## The generation plank of the two-letter band -/

/-- `cohom (tlW p q) (tlU p q) = 1`: the weight of the two-letter relator, by `p * q + q * (-p) = 0`. -/
theorem cohom_tlW_tlU_local (p q : ℕ) : cohom (tlW p q) (tlU p q) = 1 := by
  have h0 : tlW p q (0 : Fin 2) = (q : ℤ) := by simp [tlW]
  have h1 : tlW p q (1 : Fin 2) = -(p : ℤ) := by
    simp [tlW, show (1 : Fin 2) ≠ 0 from by decide]
  rw [tlU, map_mul, map_pow, map_pow, cohom_of, cohom_of, h0, h1]
  rw [← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add]
  congr 1
  simp only [nsmul_eq_mul]
  ring

/-- **The walk of `τ ^ n` stays in the band, for `n ≤ max p q`.**  This is
`Work.OROneRel.decor_pow_winE_of_weight_one` applied to the deck element of the band, using the
level bound `tlLowTauL_bound`. -/
theorem tlLowTau_pow_walk (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (hn : n ≤ max p q) :
    ∀ e ∈ decor (tlW p q) 0 (wordOf (tlLowTau p q hp hq hcop ^ n)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
  refine decor_pow_winE_of_weight_one (c := tlW p q) (v := tlLowTau p q hp hq hcop)
    (hi := (p : ℤ) * (q : ℤ)) (L := tlLowTauL p q hp hq hcop)
    (tlLowTauL_nonneg p q hp hq hcop) (tlLowTau_walk p q hp hq hcop)
    (tlLowTau_levels p q hp hq hcop) (tlLowTau_cohom p q hp hq hcop) n ?_
  have hn' : (n : ℤ) ≤ max (p : ℤ) (q : ℤ) := by exact_mod_cast hn
  linarith [tlLowTauL_bound p q hp hq hcop]

/-- The reduced word of the trivial element is empty.  Stated generically so that the
`DecidableEq` instance hidden inside `wordOf` does not clash with the one used by
`FreeGroup.toWord_one`. -/
private theorem wordOf_one_of {α : Type*} : wordOf (1 : FreeGroup α) = [] := by
  classical
  simp [wordOf]

/-- **The generation plank of the two-letter band.**  For the band window data `(c = tlW p q,
lo = 0, hi = p q, Wt)` of `Work.OROneRel.twoLetterWindowData_tlW` and the deck element of the band,
the window vertex together with the class of the deck element generates `⟨a, b | (a ^ p * b ^ q) ^ l⟩`.

At the level of the two generators this only needs the *level factors* at the levels `0`, `p`, `q`:
for the generator `a = of 0` (of weight `q`) one uses the levels `0` and `q`, and for `b = of 1` (of
weight `-p`) the levels `p` and `0`.  The level factor at `0` is trivial, and at `q` and `p` the walk
of the deck element's powers `τ ^ q`, `τ ^ p` is confined to the band, which is
`Work.OROneRel.tlLowTau_pow_walk`. -/
theorem twoLetter_generation (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hl : 1 ≤ l)
    (hcop : Nat.Coprime p q) {Wt : ℤ → FreeGroup (Fin 2)}
    (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, cohom (tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ decor (tlW p q) 0 (wordOf (tlU p q)),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ))) :
    winVertex Wt (tlW p q) 0 ((p : ℤ) * (q : ℤ)) (tlU p q) l ⊔
      Subgroup.closure (singleton (PresentedGroup.mk ({tlU p q ^ l} : Set (FreeGroup (Fin 2)))
        (tlLowTau p q hp hq hcop))) = ⊤ := by
  refine winVertex_generation_of_walk_containment_at_levels (u := tlU p q) (l := l)
    (c := tlW p q) (Wt := Wt) (lo := 0) (hi := (p : ℤ) * (q : ℤ))
    (τ := tlLowTau p q hp hq hcop) hW0 (cohom_tlW_tlU_local p q) hwin
    (tlLowTau_cohom p q hp hq hcop) ?_
  -- the weights of the two generators
  have htl0 : tlW p q (0 : Fin 2) = (q : ℤ) := by simp [tlW]
  have htl1 : tlW p q (1 : Fin 2) = -(p : ℤ) := by
    simp [tlW, show (1 : Fin 2) ≠ 0 from by decide]
  have hp0 : (0 : ℤ) ≤ (p : ℤ) := by
    have : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
    linarith
  have hq0 : (0 : ℤ) ≤ (q : ℤ) := by positivity
  have hpq0 : (0 : ℤ) ≤ (p : ℤ) * (q : ℤ) := by positivity
  -- the empty walk of the trivial word
  have hempty : ∀ e ∈ decor (tlW p q) 0 (wordOf (1 : FreeGroup (Fin 2))),
      coverEdge e ∈ winE (tlW p q) 0 ((p : ℤ) * (q : ℤ)) := by
    intro e he
    rw [wordOf_one_of] at he
    exact absurd he (List.not_mem_nil)
  intro x
  have hx : x = (0 : Fin 2) ∨ x = (1 : Fin 2) := by fin_cases x <;> simp
  rcases hx with rfl | rfl
  · -- the generator `a = of 0`, of weight `q`: the levels `0` and `0 + q = q`
    refine ⟨0, ?_, ?_, ?_⟩
    · -- the edge `(0, 0)` lies in the window
      rw [mem_winE]
      refine ⟨le_rfl, hpq0, ?_, ?_⟩
      · have h : (0 : ℤ) + tlW p q (0 : Fin 2) = (q : ℤ) := by rw [zero_add, htl0]
        rw [h]
        exact hq0
      · rw [htl0]
        nlinarith [hpq0]
    · -- the walk of `τ ^ 0 = 1` is empty
      have hz : tlLowTau p q hp hq hcop ^ (0 : ℤ) = 1 := zpow_zero _
      intro e he
      rw [hz] at he
      exact hempty e he
    · -- the walk of `τ ^ q` (the level `0 + tlW p q 0 = q`)
      have h := tlLowTau_pow_walk p q q hp hq hcop (le_max_right p q)
      have hq' : (0 : ℤ) + tlW p q (0 : Fin 2) = ((q : ℕ) : ℤ) := by rw [zero_add, htl0]
      intro e he
      rw [hq', zpow_natCast] at he
      exact h e he
  · -- the generator `b = of 1`, of weight `-p`: the levels `p` and `p + (-p) = 0`
    refine ⟨(p : ℤ), ?_, ?_, ?_⟩
    · -- the edge `(1, p)` lies in the window
      rw [mem_winE]
      refine ⟨hp0, ?_, ?_, ?_⟩
      · nlinarith [hpq0]
      · rw [htl1]
        linarith
      · rw [htl1]
        linarith
    · -- the walk of `τ ^ p` stays in the band
      have h := tlLowTau_pow_walk p q p hp hq hcop (le_max_left p q)
      intro e he
      rw [zpow_natCast] at he
      exact h e he
    · -- the walk of `τ ^ (p + (-p)) = τ ^ 0 = 1` is empty
      have hpv : (p : ℤ) + tlW p q (1 : Fin 2) = 0 := by rw [htl1]; ring
      have hz : tlLowTau p q hp hq hcop ^ (0 : ℤ) = 1 := zpow_zero _
      intro e he
      rw [hpv, hz] at he
      exact hempty e he


end Work.OROneRel
