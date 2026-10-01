import Mathlib
import Submission.Work.LinnikBurgess.DdBits
import Submission.Commons.Combinatorics.Counting.card_functions_fin_six_small_range

/-!
# The trivial (combinatorial) bound for the non-singleton part of the sixth-moment sum

We bound, with no cancellation whatsoever, the part of the double sum
`∑_f ∑_g corr6 q χ f g` coming from pairs `(f, g)` that are *not* singletons
(i.e. whose six shifts `f l + 1, g l + 1` have no value occurring exactly once).

The point is that a non-singleton pair takes at most three distinct values among
its six shifts (each occurring value occurs at least twice and `2 · 3 = 6`), so
there are at most `3^6 H^3 = 729 H^3` of them
(`Commons.Combinatorics.Counting.card_functions_fin_six_small_range`), while each
individual correlation is trivially bounded by `q`.  Hence the total is at most
`729 · H^3 · q`.
-/

open scoped BigOperators

namespace Work.LinnikBurgess

/-- The six shifts of a pair `(f, g)` packaged as a function `Fin 6 → Fin H`. -/
def valMap {H : ℕ} (p : (Fin 3 → Fin H) × (Fin 3 → Fin H)) : Fin 6 → Fin H :=
  ![p.1 0, p.1 1, p.1 2, p.2 0, p.2 1, p.2 2]

/-- `shift6` is `valMap` shifted by one. -/
lemma valMap_fin {H : ℕ} (p : (Fin 3 → Fin H) × (Fin 3 → Fin H)) (i : Fin 6) :
    shift6 p i = ((valMap p i : ℕ) + 1) := by
  fin_cases i <;> rfl

/-- Equal shifts give equal values. -/
lemma valMap_eq_of_shift_eq {H : ℕ} {p : (Fin 3 → Fin H) × (Fin 3 → Fin H)} {i i' : Fin 6}
    (h : shift6 p i = shift6 p i') : valMap p i = valMap p i' := by
  have h1 := valMap_fin p i
  have h2 := valMap_fin p i'
  have : ((valMap p i : ℕ) + 1) = ((valMap p i' : ℕ) + 1) := by rw [← h1, h, h2]
  exact Fin.ext (Nat.add_right_cancel this)

/-- The pair `(f, g)` is recovered from `valMap`. -/
lemma valMap_injective (H : ℕ) :
    Function.Injective (valMap : (Fin 3 → Fin H) × (Fin 3 → Fin H) → (Fin 6 → Fin H)) := by
  intro p p' h
  have h0 : p.1 0 = p'.1 0 := congrFun h (0 : Fin 6)
  have h1 : p.1 1 = p'.1 1 := congrFun h (1 : Fin 6)
  have h2 : p.1 2 = p'.1 2 := congrFun h (2 : Fin 6)
  have h3 : p.2 0 = p'.2 0 := congrFun h (3 : Fin 6)
  have h4 : p.2 1 = p'.2 1 := congrFun h (4 : Fin 6)
  have h5 : p.2 2 = p'.2 2 := congrFun h (5 : Fin 6)
  have hf : p.1 = p'.1 := by
    funext l
    fin_cases l
    · exact h0
    · exact h1
    · exact h2
  have hg : p.2 = p'.2 := by
    funext l
    fin_cases l
    · exact h3
    · exact h4
    · exact h5
  exact Prod.ext hf hg

/-- A non-singleton pair has no value occurring exactly once among its six shifts,
so every value of `valMap` occurs at least twice. -/
lemma not_singleton_fiber {H : ℕ} (p : (Fin 3 → Fin H) × (Fin 3 → Fin H))
    (hp : ¬ IsSingleton6 p) (i : Fin 6) :
    ∃ i' : Fin 6, i' ≠ i ∧ valMap p i' = valMap p i := by
  simp only [IsSingleton6, not_exists, not_forall, not_not] at hp
  obtain ⟨i', hi', heq⟩ := hp i
  exact ⟨i', hi', (valMap_eq_of_shift_eq heq).symm⟩

/-- The range of `valMap` of a non-singleton pair has at most `3` elements. -/
lemma card_image_valMap_le_three {H : ℕ} (p : (Fin 3 → Fin H) × (Fin 3 → Fin H))
    (hp : ¬ IsSingleton6 p) : (Finset.univ.image (valMap p)).card ≤ 3 := by
  have hfiber : ∀ b ∈ (Finset.univ : Finset (Fin 6)).image (valMap p),
      2 ≤ ((Finset.univ : Finset (Fin 6)).filter (fun a => valMap p a = b)).card := by
    intro b hb
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hb
    obtain ⟨i', hi', heq⟩ := not_singleton_fiber p hp i
    have hmem_i : i ∈ (Finset.univ : Finset (Fin 6)).filter (fun a => valMap p a = b) := by
      simp [hi]
    have hmem_i' : i' ∈ (Finset.univ : Finset (Fin 6)).filter (fun a => valMap p a = b) := by
      simp [heq, hi]
    have h1 : 1 < ((Finset.univ : Finset (Fin 6)).filter (fun a => valMap p a = b)).card :=
      Finset.one_lt_card.mpr ⟨i, hmem_i, i', hmem_i', fun h => hi' h.symm⟩
    omega
  have h2 := Finset.mul_card_image_le_card (s := (Finset.univ : Finset (Fin 6)))
      (n := 2) (f := valMap p) hfiber
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega

/-- The finset of *non-singleton* pairs. -/
noncomputable def nsPairs (H : ℕ) : Finset ((Fin 3 → Fin H) × (Fin 3 → Fin H)) := by
  classical
  exact Finset.univ.filter (fun p => ¬ IsSingleton6 p)

/-- The number of non-singleton pairs is at most `3^6 H^3`. -/
lemma card_nsPairs_le (H : ℕ) : (nsPairs H).card ≤ 3 ^ 6 * H ^ 3 := by
  classical
  have hle : (nsPairs H).card ≤ ((Finset.univ : Finset (Fin 6 → Fin H)).filter
      (fun v => (Finset.univ.image v).card ≤ 3)).card := by
    unfold nsPairs
    refine Finset.card_le_card_of_injOn (fun p => valMap p) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact card_image_valMap_le_three p hp
    · intro a _ b _ hab
      exact valMap_injective H hab
  exact le_trans hle (Commons.Combinatorics.Counting.card_functions_fin_six_small_range H)

/-- The non-singleton part of a sum written as a sum over `nsPairs`. -/
lemma nsPairs_sum {M : Type*} [AddCommMonoid M] (H : ℕ)
    (F : ((Fin 3 → Fin H) × (Fin 3 → Fin H)) → M) :
    ∑ p : (Fin 3 → Fin H) × (Fin 3 → Fin H), (if IsSingleton6 p then 0 else F p)
      = ∑ p ∈ nsPairs H, F p := by
  classical
  unfold nsPairs
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun p _ => by by_cases hp : IsSingleton6 p <;> simp [hp]

/-- Trivial bound for a single cubic correlation: it is a sum of `q` complex numbers
of modulus at most `1`. -/
lemma norm_corr6_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {H : ℕ}
    (f g : Fin 3 → Fin H) : ‖corr6 q χ f g‖ ≤ (q : ℝ) := by
  unfold corr6
  calc ‖∑ x : ZMod q, χ (∏ l : Fin 3, (x + ((((f l : ℕ) + 1 : ℕ)) : ZMod q)))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + ((((g l : ℕ) + 1 : ℕ)) : ZMod q))))‖
      ≤ ∑ x : ZMod q, ‖χ (∏ l : Fin 3, (x + ((((f l : ℕ) + 1 : ℕ)) : ZMod q)))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + ((((g l : ℕ) + 1 : ℕ)) : ZMod q))))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x : ZMod q, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        rw [norm_mul]
        have h1 : ‖χ (∏ l : Fin 3, (x + ((((f l : ℕ) + 1 : ℕ)) : ZMod q)))‖ ≤ 1 :=
          DirichletCharacter.norm_le_one χ _
        have h2 : ‖(starRingEnd ℂ)
            (χ (∏ l : Fin 3, (x + ((((g l : ℕ) + 1 : ℕ)) : ZMod q))))‖ ≤ 1 := by
          rw [show ‖(starRingEnd ℂ)
              (χ (∏ l : Fin 3, (x + ((((g l : ℕ) + 1 : ℕ)) : ZMod q))))‖
                = ‖χ (∏ l : Fin 3, (x + ((((g l : ℕ) + 1 : ℕ)) : ZMod q)))‖ from norm_star _]
          exact DirichletCharacter.norm_le_one χ _
        calc ‖χ (∏ l : Fin 3, (x + ((((f l : ℕ) + 1 : ℕ)) : ZMod q)))‖
              * ‖(starRingEnd ℂ)
                  (χ (∏ l : Fin 3, (x + ((((g l : ℕ) + 1 : ℕ)) : ZMod q))))‖
            ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
    _ = (q : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card q, nsmul_eq_mul]
        norm_num

theorem nosingleton_sum_bound {q : ℕ} [NeZero q] (H : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
        (if IsSingleton6 (f, g) then 0 else corr6 q χ f g)‖
      ≤ 729 * ((H : ℝ) ^ 3 * (q : ℝ)) := by
  classical
  have hSCard : ((nsPairs H).card : ℝ) ≤ 729 * (H : ℝ) ^ 3 := by
    have h := card_nsPairs_le H
    have h' : ((nsPairs H).card : ℝ) ≤ ((729 * H ^ 3 : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'
  -- Rewrite the double sum as a single sum over pairs.
  have hsum : (∑ f : Fin 3 → Fin H, ∑ g : Fin 3 → Fin H,
        (if IsSingleton6 (f, g) then 0 else corr6 q χ f g))
      = ∑ p : (Fin 3 → Fin H) × (Fin 3 → Fin H),
          (if IsSingleton6 p then 0 else corr6 q χ p.1 p.2) := by
    rw [← Finset.sum_product (s := (Finset.univ : Finset (Fin 3 → Fin H)))
          (t := (Finset.univ : Finset (Fin 3 → Fin H)))
          (f := fun p : (Fin 3 → Fin H) × (Fin 3 → Fin H) =>
            if IsSingleton6 p then 0 else corr6 q χ p.1 p.2)]
    rw [Finset.univ_product_univ]
  rw [hsum]
  calc ‖∑ p : (Fin 3 → Fin H) × (Fin 3 → Fin H),
          (if IsSingleton6 p then 0 else corr6 q χ p.1 p.2)‖
      ≤ ∑ p : (Fin 3 → Fin H) × (Fin 3 → Fin H),
          ‖(if IsSingleton6 p then 0 else corr6 q χ p.1 p.2)‖ := norm_sum_le _ _
    _ = ∑ p ∈ nsPairs H, ‖corr6 q χ p.1 p.2‖ := by
        rw [← nsPairs_sum H (fun p => ‖corr6 q χ p.1 p.2‖)]
        exact Finset.sum_congr rfl fun p _ => by
          by_cases hp : IsSingleton6 p <;> simp [hp]
    _ ≤ ∑ _p ∈ nsPairs H, (q : ℝ) :=
        Finset.sum_le_sum fun p _ => norm_corr6_le χ p.1 p.2
    _ = ((nsPairs H).card : ℝ) * (q : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 729 * ((H : ℝ) ^ 3 * (q : ℝ)) := by
        have h2 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
        calc ((nsPairs H).card : ℝ) * (q : ℝ) ≤ (729 * (H : ℝ) ^ 3) * (q : ℝ) :=
              mul_le_mul_of_nonneg_right hSCard h2
          _ = 729 * ((H : ℝ) ^ 3 * (q : ℝ)) := by ring

end Work.LinnikBurgess
