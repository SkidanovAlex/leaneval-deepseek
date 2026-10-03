import Mathlib
import Submission.Work.Peluse.SwapE.cubeMass.Defs

/-!
# `cubeMass.fiberSum` — the fibre identity of the double tuple sum

The double sum `∑_{h,h' : [1,Card]^t} Φ (h - h')` is the sum of `Φ` over the differences `u` of
tuples, each weighted by the number of pairs `(h,h')` with `h - h' = u`; that multiplicity is the
product over the coordinates of the one-dimensional count `Ncard Card (u i) = Card - |u i|`, i.e.
the weight `Wt Card t u`.  Only differences in `Tdir Card t = (sCard Card)^t` occur.

The proof is a change of variables: the double sum is the sum over the product type
`[1,Card]^t × [1,Card]^t`, grouped by the value of the difference map
(`Finset.sum_fiberwise_of_maps_to`, whose target set is the *finite* set `Tdir Card t`), and the
fibre cardinalities are computed coordinatewise (`Fintype.card_piFinset` + the one-dimensional
count).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.SwapE.cubeMass

noncomputable section

open Work.Peluse
open Work.Peluse.SwapE

/-- The difference of a pair of tuples `p = (h, h')` of `[1,Card]^t`, as a function `Fin t → ℤ`. -/
def diffFun (Card t : ℕ)
    (p : ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) ×
      ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card))) :
    Fin t → ℤ :=
  fun i => (p.1 i : ℤ) - (p.2 i : ℤ)

/-- `arithIcc 1 Card` is the interval of integers `[1, Card]`. -/
lemma arithIcc_one_eq_Icc (Card : ℕ) :
    Work.Peluse.arithIcc 1 Card = Finset.Icc (1 : ℤ) (Card : ℤ) := by
  rw [Work.Peluse.arithIcc]
  ext n
  simp only [Finset.mem_image, Finset.mem_Icc, one_mul]
  constructor
  · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · intro h
    refine ⟨n.toNat, ⟨?_, ?_⟩, ?_⟩ <;> omega

/-- Membership in `arithIcc 1 Card`, in the form `1 ≤ a ≤ Card`. -/
lemma mem_arithIcc_one (Card : ℕ) (a : ℤ) :
    a ∈ Work.Peluse.arithIcc 1 Card ↔ (1 : ℤ) ≤ a ∧ a ≤ (Card : ℤ) := by
  rw [arithIcc_one_eq_Icc, Finset.mem_Icc]

/-- The pairs `(a, b) ∈ [1,Card]²` with `a - b = v`. -/
def fiber1 (Card : ℕ) (v : ℤ) :
    Finset (↥(Work.Peluse.arithIcc 1 Card) × ↥(Work.Peluse.arithIcc 1 Card)) :=
  Finset.univ.filter (fun w => (w.1 : ℤ) - (w.2 : ℤ) = v)

/-- The fibre of the difference map over a value `v`, as the set of the *first* coordinates `a`
whose translate `a - v` still lies in `Q`. -/
lemma fiberQ_card (Q : Finset ℤ) (v : ℤ) :
    (Finset.univ.filter (fun w : ↥Q × ↥Q => (w.1 : ℤ) - (w.2 : ℤ) = v)).card
      = (Q.filter (fun a => a - v ∈ Q)).card := by
  refine Finset.card_bij (fun (w : ↥Q × ↥Q)
      (_ : w ∈ Finset.univ.filter (fun w : ↥Q × ↥Q => (w.1 : ℤ) - (w.2 : ℤ) = v)) => (w.1 : ℤ))
    ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨w.1.2, ?_⟩
    have hh : (w.1 : ℤ) - v = (w.2 : ℤ) := by omega
    rw [hh]
    exact w.2.2
  · intro w1 hw1 w2 hw2 heq
    rw [Finset.mem_filter] at hw1 hw2
    have h1 : w1.1 = w2.1 := Subtype.ext (by exact_mod_cast heq)
    have h2 : w1.2 = w2.2 := by
      apply Subtype.ext
      have e1 := hw1.2; have e2 := hw2.2
      omega
    exact Prod.ext h1 h2
  · intro b hb
    rw [Finset.mem_filter] at hb
    refine ⟨(⟨b, hb.1⟩, ⟨b - v, hb.2⟩), ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by push_cast; ring⟩
    · simp

/-- The elementary count `#{(a,b) ∈ [1,Card]² : a - b = v} = Card - |v|`. -/
lemma filter_card_Icc (Card : ℕ) (v : ℤ) :
    ((Finset.Icc (1 : ℤ) (Card : ℤ)).filter
        (fun a => a - v ∈ (Finset.Icc (1 : ℤ) (Card : ℤ)))).card
      = Ncard Card v := by
  by_cases hv : 0 ≤ v
  · have hset : (Finset.Icc (1 : ℤ) (Card : ℤ)).filter
          (fun a => a - v ∈ (Finset.Icc (1 : ℤ) (Card : ℤ)))
        = Finset.Icc (1 + v) (Card : ℤ) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, hh1, hh2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨by omega, h2⟩, by omega, by omega⟩
    rw [hset, Int.card_Icc]
    simp only [Ncard]
    omega
  · have hset : (Finset.Icc (1 : ℤ) (Card : ℤ)).filter
          (fun a => a - v ∈ (Finset.Icc (1 : ℤ) (Card : ℤ)))
        = Finset.Icc (1 : ℤ) (Card + v) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, hh1, hh2⟩
        exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, by omega⟩, by omega, by omega⟩
    rw [hset, Int.card_Icc]
    simp only [Ncard]
    omega

/-- The one-dimensional fibre count: `#{(a,b) ∈ arithIcc 1 Card² : a - b = v} = Ncard Card v`. -/
lemma fiber1_card (Card : ℕ) (v : ℤ) : (fiber1 Card v).card = Ncard Card v := by
  rw [fiber1, fiberQ_card]
  rw [arithIcc_one_eq_Icc]
  exact filter_card_Icc Card v

/-- The coordinatewise fibre count: the tuples `p : Fin t → arithIcc 1 Card × arithIcc 1 Card`
with prescribed coordinatewise differences `u` are counted by `Wt Card t u = ∏ i, Ncard Card (u i)`. -/
lemma fiberT_card (Card t : ℕ) (u : Fin t → ℤ) :
    (Finset.univ.filter
        (fun p : (i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card) × ↥(Work.Peluse.arithIcc 1 Card) =>
          ∀ i, (p i).1 - (p i).2 = u i)).card
      = Wt Card t u := by
  have h2 : (Finset.univ.filter
        (fun p : (i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card) × ↥(Work.Peluse.arithIcc 1 Card) =>
          ∀ i, (p i).1 - (p i).2 = u i))
      = Fintype.piFinset (fun i => fiber1 Card (u i)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, fiber1]
  rw [h2, Fintype.card_piFinset]
  simp only [fiber1_card, Wt]

/-- The multiplicity of a difference `u` among pairs of tuples of `[1,Card]^t`. -/
lemma fiberPair_card (Card t : ℕ) (u : Fin t → ℤ) :
    (Finset.univ.filter (fun p : ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) ×
        ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) =>
      diffFun Card t p = u)).card = Wt Card t u := by
  have hbij : (Finset.univ.filter (fun p : ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) ×
        ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) =>
      diffFun Card t p = u)).card
      = (Finset.univ.filter
          (fun q : (i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card) × ↥(Work.Peluse.arithIcc 1 Card) =>
            ∀ i, (q i).1 - (q i).2 = u i)).card := by
    refine Finset.card_bij (fun (p : _ × _) _ => fun i => (p.1 i, p.2 i)) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_univ _, fun i => congr_fun hp.2 i⟩
    · intro p1 hp1 p2 hp2 heq
      have h1 : p1.1 = p2.1 := by funext i; exact congr_arg Prod.fst (congr_fun heq i)
      have h2 : p1.2 = p2.2 := by funext i; exact congr_arg Prod.snd (congr_fun heq i)
      exact Prod.ext h1 h2
    · intro q hq
      rw [Finset.mem_filter] at hq
      refine ⟨(fun i => (q i).1, fun i => (q i).2), ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, funext (fun i => hq.2 i)⟩
      · rfl
  rw [hbij, fiberT_card]

/-- Every difference of two tuples of `[1,Card]^t` lies in `Tdir Card t`. -/
lemma diffFun_mem_Tdir (Card t : ℕ)
    (p : ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) ×
      ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card))) :
    diffFun Card t p ∈ Tdir Card t := by
  rw [mem_Tdir]
  intro i
  rw [mem_sCard]
  have h1 := (mem_arithIcc_one Card _).mp (p.1 i).2
  have h2 := (mem_arithIcc_one Card _).mp (p.2 i).2
  simp only [diffFun]
  constructor <;> omega

/-- The fibre identity of the double tuple sum: grouping the pairs `(h,h')` of `[1,Card]^t` by
their difference `u = h - h'` exhibits the multiplicity `Wt Card t u` of each difference. -/
theorem fiberSum (Card t : ℕ) (hC : 1 ≤ Card) (Φ : (Fin t → ℤ) → ℂ) :
    (∑ h : (i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card),
       ∑ h' : (i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card),
         Φ (fun i => (h i : ℤ) - (h' i : ℤ)))
      = ∑ u ∈ Work.Peluse.SwapE.Tdir Card t,
          ((Work.Peluse.SwapE.Wt Card t u : ℕ) : ℂ) * Φ u := by
  classical
  have h1 : (∑ h : (i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card),
       ∑ h' : (i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card),
         Φ (fun i => (h i : ℤ) - (h' i : ℤ)))
      = ∑ p : ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) ×
          ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)),
          Φ (diffFun Card t p) :=
    (Fintype.sum_prod_type (fun p : ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) ×
        ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) => Φ (diffFun Card t p))).symm
  rw [h1]
  have h2 : ∀ u : Fin t → ℤ,
      (∑ p ∈ Finset.univ.filter (fun p : ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) ×
          ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) => diffFun Card t p = u),
          Φ (diffFun Card t p))
      = ((Finset.univ.filter (fun p : ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) ×
          ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) => diffFun Card t p = u)).card : ℂ)
        * Φ u := by
    intro u
    have hc : (Finset.univ.filter (fun p : ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) ×
          ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) => diffFun Card t p = u)).sum
          (fun p => Φ (diffFun Card t p))
        = (Finset.univ.filter (fun p : ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) ×
          ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) => diffFun Card t p = u)).sum
          (fun _ => Φ u) :=
      Finset.sum_congr rfl (fun p hp => by rw [Finset.mem_filter] at hp; rw [hp.2])
    rw [hc, Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)) ×
        ((i : Fin t) → ↥(Work.Peluse.arithIcc 1 Card)))))
      (t := Tdir Card t) (g := diffFun Card t)
      (fun p _ => diffFun_mem_Tdir Card t p) (fun p => Φ (diffFun Card t p))]
  simp_rw [h2]
  simp_rw [fiberPair_card]

end

end Work.Peluse.SwapE.cubeMass
