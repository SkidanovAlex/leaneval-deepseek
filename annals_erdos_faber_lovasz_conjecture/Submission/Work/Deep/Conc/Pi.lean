/-
# Work.Deep.Conc.Pi

The uniform probability space on a product of finite coordinate spaces,
`Ω = ∀ i : ι, π i`, which is the only space this development uses:

* `π = fun _ => Fin k` gives the uniformly random colouring `ι → Fin k`;
* `π = fun _ => Fin 2` (or the fibre `{v // v ∈ e}`) gives the orientation coin flips of the
  naive colouring procedure.

The main theorems are the *coordinate independence* facts
`expect_prod_coord`, `prob_all_eq` (`expect` of a product of coordinate functions factorises;
the coordinates on a finite set `S` are independent and uniform) and the two marginal laws
`expect_comp_restrict` (a function of the restriction to `S` sees a uniform point of
`∀ i : S, π i`) and `prob_iUnion_eq_sum_of_disjoint`.
-/
import Submission.Work.Deep.Conc.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped BigOperators
open Finset

namespace Work.Deep.Conc

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {π : ι → Type*} [∀ i, Fintype (π i)]

/-- A nonempty coordinate has a positive cardinality. -/
theorem card_pos_of_nonempty {i : ι} (h : Nonempty (π i)) : 0 < Fintype.card (π i) :=
  Fintype.card_pos_iff.mpr h

/-- The product of a two-branch choice over all indices splits at `S`. -/
lemma prod_ite_mem_mul {M : Type*} [CommMonoid M] (S : Finset ι) (a b : ι → M) :
    (∏ i, (if i ∈ S then a i else b i)) = (∏ i ∈ S, a i) * ∏ i ∈ Sᶜ, b i := by
  classical
  have h1 : (∏ i, (if i ∈ S then a i else b i))
      = ∏ i, ((if i ∈ S then a i else 1) * (if i ∈ Sᶜ then b i else (1 : M))) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S <;> simp [hi]
  rw [h1, Finset.prod_mul_distrib, Finset.prod_ite_mem Finset.univ S a, Finset.univ_inter,
    Finset.prod_ite_mem Finset.univ Sᶜ b, Finset.univ_inter]

/-- The unnormalised sum over a product space of a product of coordinate functions. -/
lemma sum_prod_coord (S : Finset ι) (f : ∀ i, π i → ℝ) :
    (∑ ξ : ∀ i, π i, ∏ i ∈ S, f i (ξ i))
      = (∏ i ∈ S, ∑ a, f i a) * ∏ i ∈ Sᶜ, (Fintype.card (π i) : ℝ) := by
  classical
  have key := Fintype.prod_sum (κ := π) (fun i a => if i ∈ S then f i a else (1 : ℝ))
  have hL : (∏ i, ∑ a, (if i ∈ S then f i a else (1 : ℝ)))
      = ∏ i, (if i ∈ S then (∑ a, f i a) else (Fintype.card (π i) : ℝ)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi]
  have hR : ∀ ξ : ∀ i, π i, (∏ i, (if i ∈ S then f i (ξ i) else (1 : ℝ)))
      = ∏ i ∈ S, f i (ξ i) := by
    intro ξ
    simpa using Finset.prod_ite_mem (Finset.univ : Finset ι) S (fun i => f i (ξ i))
  calc (∑ ξ : ∀ i, π i, ∏ i ∈ S, f i (ξ i))
      = ∑ ξ : ∀ i, π i, ∏ i, (if i ∈ S then f i (ξ i) else (1 : ℝ)) :=
        Finset.sum_congr rfl fun ξ _ => (hR ξ).symm
    _ = ∏ i, ∑ a, (if i ∈ S then f i a else (1 : ℝ)) := key.symm
    _ = ∏ i, (if i ∈ S then (∑ a, f i a) else (Fintype.card (π i) : ℝ)) := hL
    _ = (∏ i ∈ S, ∑ a, f i a) * ∏ i ∈ Sᶜ, (Fintype.card (π i) : ℝ) :=
        prod_ite_mem_mul S (fun i => ∑ a, f i a) (fun i => (Fintype.card (π i) : ℝ))

/-- **Independence of the coordinates**: the expectation of a product of functions of the
coordinates in `S` factorises, each coordinate contributing its average. -/
theorem expect_prod_coord (S : Finset ι) (f : ∀ i, π i → ℝ) (hne : ∀ i, Nonempty (π i)) :
    expect (fun ξ : ∀ i, π i => ∏ i ∈ S, f i (ξ i))
      = ∏ i ∈ S, ((∑ a, f i a) / (Fintype.card (π i) : ℝ)) := by
  have hC : (∏ i ∈ Sᶜ, (Fintype.card (π i) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ =>
      Nat.cast_ne_zero.mpr (ne_of_gt (card_pos_of_nonempty (hne i)))
  rw [expect, Fintype.card_pi, Nat.cast_prod, sum_prod_coord S f,
    ← Finset.prod_mul_prod_compl S (fun i => (Fintype.card (π i) : ℝ)),
    mul_div_mul_right _ _ hC, Finset.prod_div_distrib]

/-- The single-coordinate case of independence. -/
theorem expect_coord (i : ι) (f : π i → ℝ) (hne : ∀ i, Nonempty (π i)) :
    expect (fun ξ : ∀ i, π i => f (ξ i)) = (∑ a, f a) / (Fintype.card (π i) : ℝ) := by
  have hsum : (∑ a : π i, (if h : i = i then f (h ▸ a) else 1)) = ∑ a, f a :=
    Finset.sum_congr rfl fun a _ => by rw [dif_pos rfl]
  have h := expect_prod_coord (π := π) ({i} : Finset ι)
    (fun j a => if h : j = i then f (h ▸ a) else 1) hne
  rw [Finset.prod_singleton] at h
  rw [hsum] at h
  rw [← h]
  refine expect_congr fun ξ => ?_
  rw [Finset.prod_singleton, dif_pos rfl]

/-- **The law of a set of coordinates**: prescribing the values of the coordinates in `S` has
probability `∏_{i ∈ S} 1 / #(π i)`. -/
theorem prob_all_eq (S : Finset ι) (g : ∀ i, π i) (hne : ∀ i, Nonempty (π i)) :
    prob {ξ : ∀ i, π i | ∀ i ∈ S, ξ i = g i}
      = ∏ i ∈ S, (1 / (Fintype.card (π i) : ℝ)) := by
  classical
  have hpt : ({ξ : ∀ i, π i | ∀ i ∈ S, ξ i = g i} : Set (∀ i, π i)).indicator
        (fun _ => (1 : ℝ))
      = fun ξ : ∀ i, π i => ∏ i ∈ S, (if ξ i = g i then (1 : ℝ) else 0) := by
    funext ξ
    by_cases h : ∀ i ∈ S, ξ i = g i
    · rw [Set.indicator_of_mem (s := {ξ : ∀ i, π i | ∀ i ∈ S, ξ i = g i}) h]
      rw [Finset.prod_eq_one fun i hi => if_pos (h i hi)]
    · rw [Set.indicator_of_notMem (s := {ξ : ∀ i, π i | ∀ i ∈ S, ξ i = g i}) h]
      push_neg at h
      obtain ⟨i, hi, hne'⟩ := h
      rw [Finset.prod_eq_zero hi (if_neg hne')]
  rw [prob, hpt, expect_prod_coord S (fun i a => if a = g i then (1 : ℝ) else 0) hne]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ (g i) (fun _ => (1 : ℝ)),
    if_pos (Finset.mem_univ (g i))]

/-- The single-coordinate case of the law of coordinates. -/
theorem prob_coord_eq (i : ι) (a : π i) (hne : ∀ i, Nonempty (π i)) :
    prob {ξ : ∀ i, π i | ξ i = a} = 1 / (Fintype.card (π i) : ℝ) := by
  classical
  haveI := hne
  obtain ⟨g, hg⟩ : ∃ g : ∀ j, π j, g i = a :=
    ⟨Function.update (Classical.choice (inferInstance : Nonempty (∀ j, π j))) i a,
      Function.update_self i a _⟩
  have h := prob_all_eq (π := π) ({i} : Finset ι) g hne
  rw [Finset.prod_singleton] at h
  have hset : {ξ : ∀ i, π i | ξ i = a}
      = {ξ : ∀ i, π i | ∀ j ∈ ({i} : Finset ι), ξ j = g j} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Finset.mem_singleton, forall_eq]
    rw [hg]
  rw [hset, h]

/-! ## A disjoint union of events -/

/-- The probability of a finite disjoint union is the sum of the probabilities. -/
theorem prob_iUnion_eq_sum_of_disjoint {Ω : Type*} [Fintype Ω] {ι' : Type*} [Fintype ι']
    (A : ι' → Set Ω)
    (h : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    prob (⋃ i, A i) = ∑ i, prob (A i) := by
  classical
  have hpt : (⋃ i, A i).indicator (fun _ => (1 : ℝ))
      = fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    by_cases hmem : ω ∈ ⋃ i, A i
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hmem
      have hgoal : (∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω)
          = (A j).indicator (fun _ => (1 : ℝ)) ω :=
        Finset.sum_eq_single (s := Finset.univ)
          (f := fun i => (A i).indicator (fun _ => (1 : ℝ)) ω) j
          (fun i _ hij => by
            rw [Set.indicator_of_notMem]
            intro hi
            exact absurd (Set.disjoint_left.mp (h i j hij) hi hj) (by simp))
          (fun hj' => absurd (Finset.mem_univ j) hj')
      rw [Set.indicator_of_mem hmem, hgoal, Set.indicator_of_mem hj]
    · have hgoal : (∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [Set.indicator_of_notMem]
        intro hi
        exact hmem (Set.mem_iUnion.mpr ⟨i, hi⟩)
      rw [Set.indicator_of_notMem hmem, hgoal]
  have h1 : prob (⋃ i, A i)
      = expect (fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω) :=
    congrArg expect hpt
  rw [h1, expect_sum]
  rfl

/-! ## Product spaces -/

/-- **Fubini for a product of two uniform spaces.** -/
theorem expect_prod_tensor {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (f : Ω₁ → ℝ) (g : Ω₂ → ℝ) :
    expect (fun p : Ω₁ × Ω₂ => f p.1 * g p.2) = expect f * expect g := by
  rw [expect, expect, expect, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  have h1 : (∑ a : Ω₁, ∑ b : Ω₂, f a * g b) = (∑ a, f a) * ∑ b, g b := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum ..).symm
  rw [h1, ← div_mul_div_comm]

/-- **Fubini for two uniform spaces**: the probability of an event in a product is the
expectation over the first factor of the conditional probability in the second. -/
theorem prob_prod_eq_expect_prob {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (E : Set (Ω₁ × Ω₂)) :
    prob E = expect (fun a : Ω₁ => prob {b : Ω₂ | (a, b) ∈ E}) := by
  have hpt : ∀ (a : Ω₁) (b : Ω₂), E.indicator (fun _ => (1 : ℝ)) (a, b)
      = ({b' : Ω₂ | (a, b') ∈ E} : Set Ω₂).indicator (fun _ => (1 : ℝ)) b := by
    intro a b
    by_cases h : (a, b) ∈ E
    · have h1 : E.indicator (fun _ => (1 : ℝ)) (a, b) = 1 := by
        rw [Set.indicator_of_mem h]
      have h2 : ({b' : Ω₂ | (a, b') ∈ E} : Set Ω₂).indicator (fun _ => (1 : ℝ)) b = 1 :=
        Set.indicator_of_mem (s := {b' : Ω₂ | (a, b') ∈ E}) h (fun _ => (1 : ℝ))
      rw [h1, h2]
    · have h1 : E.indicator (fun _ => (1 : ℝ)) (a, b) = 0 := Set.indicator_of_notMem h _
      have h2 : ({b' : Ω₂ | (a, b') ∈ E} : Set Ω₂).indicator (fun _ => (1 : ℝ)) b = 0 :=
        Set.indicator_of_notMem (s := {b' : Ω₂ | (a, b') ∈ E}) h (fun _ => (1 : ℝ))
      rw [h1, h2]
  have hinner : ∀ a : Ω₁, prob {b : Ω₂ | (a, b) ∈ E}
      = (∑ b : Ω₂, E.indicator (fun _ => (1 : ℝ)) (a, b)) / (Fintype.card Ω₂ : ℝ) := by
    intro a
    rw [prob, expect]
    exact congrArg (fun x => x / (Fintype.card Ω₂ : ℝ))
      (Finset.sum_congr rfl fun b _ => (hpt a b).symm)
  have hL : prob E = (∑ a : Ω₁, ∑ b : Ω₂, E.indicator (fun _ => (1 : ℝ)) (a, b))
      / ((Fintype.card Ω₁ : ℝ) * (Fintype.card Ω₂ : ℝ)) := by
    rw [prob, expect, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
  have hR : expect (fun a : Ω₁ => prob {b : Ω₂ | (a, b) ∈ E})
      = (∑ a : Ω₁, ∑ b : Ω₂, E.indicator (fun _ => (1 : ℝ)) (a, b))
        / ((Fintype.card Ω₁ : ℝ) * (Fintype.card Ω₂ : ℝ)) := by
    rw [expect]
    simp only [hinner]
    rw [← Finset.sum_div, div_div, mul_comm (Fintype.card Ω₂ : ℝ) (Fintype.card Ω₁ : ℝ)]
  rw [hL, hR]

end Work.Deep.Conc
