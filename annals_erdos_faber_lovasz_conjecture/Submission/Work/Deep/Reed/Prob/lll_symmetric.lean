import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.Deep.Reed.Prob.Basic

/-!
# The Lovász Local Lemma (general and symmetric forms)

This file proves the symmetric Lovász Local Lemma for finite probability
spaces, in the form requested by `Work.Deep.Reed.Prob.lll_symmetric`.

The proof goes through the general (asymmetric) lemma `lll_general`: for a
family of events `A i`, a dependency set `dep i` for each `i`, and witnesses
`x i ∈ [0,1)` with `P(A i) ≤ x i * ∏_{j ∈ dep i} (1 - x j)`, we have
`∏ i, (1 - x i) ≤ P(⋂ i, (A i)ᶜ)`.

The general lemma is proved by the standard induction on `|U| + |V|` for the
strengthened statement

`P(⋂_{j ∈ U ∪ V} A jᶜ) ≥ (∏_{j ∈ U} (1 - x j)) * P(⋂_{j ∈ V} A jᶜ)`  (`U ∩ V = ∅`),

whose inductive step rests on the key estimate
`P(A i ∩ ⋂_{j ∈ T} A jᶜ) ≤ x i * P(⋂_{j ∈ T} A jᶜ)` for `i ∉ T`.

The symmetric form follows with the constant witness `x = 1/(d+2)`; the
hypothesis `e * p * (d+1) ≤ 1` is exactly what converts into the witness
condition, via `(1 + 1/(d+1))^(d+1) ≤ e`.
-/

open scoped BigOperators

namespace Work.Deep.Reed.Prob

/-! ## Two elementary lemmas -/

/-- `P(Aᶜ ∩ B) = P(B) - P(A ∩ B)`. -/
private lemma prob_compl_inter {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (A B : Set Ω) :
    μ.prob (Aᶜ ∩ B) = μ.prob B - μ.prob (A ∩ B) := by
  have hcompl : Aᶜ ∩ B = B \ A := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]; tauto
  have hdisj : (A ∩ B) ∪ (B \ A) = B := by
    ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]; tauto
  have h0 : (A ∩ B) ∩ (B \ A) = ∅ := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
    tauto
  have hsum : μ.prob B = μ.prob (A ∩ B) + μ.prob (B \ A) := by
    have h := FinProb.prob_union_add_inter μ (A ∩ B) (B \ A)
    rw [hdisj, h0, FinProb.prob_empty] at h
    linarith
  rw [hcompl, hsum]; ring

/-- A larger index set gives a smaller intersection of complements. -/
private lemma biInter_compl_mono {Ω ι : Type*} (A : ι → Set Ω) {S T : Finset ι}
    (h : S ⊆ T) : (⋂ j ∈ T, (A j)ᶜ) ⊆ (⋂ j ∈ S, (A j)ᶜ) := by
  intro x hx
  rw [Set.mem_iInter₂] at hx ⊢
  exact fun j hj => hx j (h hj)

/-! ## The arithmetic input for the symmetric form -/

/-- `(1 + 1/n)^n ≤ e`. -/
private lemma one_add_inv_pow_le_exp (n : ℕ) : (1 + 1/(n:ℝ))^n ≤ Real.exp 1 := by
  simpa [one_div] using Real.one_add_inv_pow_le_exp (n := n)

/-- The arithmetic bridge from the symmetric hypothesis `e·p·(d+1) ≤ 1` to the
witness condition at `x = 1/(d+2)`: `1/(e(d+1)) ≤ (1/(d+2))·(1 - 1/(d+2))^d`. -/
private lemma key_ineq (d : ℕ) :
    1/(Real.exp 1 * ((d:ℝ)+1)) ≤ (1/((d:ℝ)+2)) * (1 - 1/((d:ℝ)+2))^d := by
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hd1 : (0:ℝ) < (d:ℝ)+1 := by positivity
  have hd2 : (0:ℝ) < (d:ℝ)+2 := by positivity
  have hb0 : (0:ℝ) ≤ 1 - 1/((d:ℝ)+2) := by
    have h : 1/((d:ℝ)+2) ≤ 1 := by rw [div_le_one hd2]; linarith [Nat.cast_nonneg (α := ℝ) d]
    linarith
  -- `((d+2)/(d+1))^(d+1) ≤ e`
  have h1 : (((d:ℝ)+2)/((d:ℝ)+1))^(d+1) ≤ Real.exp 1 := by
    have hb : ((d:ℝ)+2)/((d:ℝ)+1) = 1 + 1/(((d+1 : ℕ) : ℝ)) := by
      have h2 : ((d:ℝ)+2) = ((d:ℝ)+1) + 1 := by ring
      rw [h2, add_div, div_self (ne_of_gt hd1)]
      push_cast
      ring
    rw [hb]
    exact one_add_inv_pow_le_exp (d+1)
  have hbinv : (((d:ℝ)+2)/((d:ℝ)+1)) * (1 - 1/((d:ℝ)+2)) = 1 := by
    field_simp; ring
  have hkey1 : (1:ℝ) ≤ Real.exp 1 * (1 - 1/((d:ℝ)+2))^(d+1) := by
    have hmul : (((d:ℝ)+2)/((d:ℝ)+1))^(d+1) * (1 - 1/((d:ℝ)+2))^(d+1) = 1 := by
      rw [← mul_pow, hbinv, one_pow]
    calc (1:ℝ) = (((d:ℝ)+2)/((d:ℝ)+1))^(d+1) * (1 - 1/((d:ℝ)+2))^(d+1) := hmul.symm
      _ ≤ Real.exp 1 * (1 - 1/((d:ℝ)+2))^(d+1) :=
            mul_le_mul_of_nonneg_right h1 (pow_nonneg hb0 _)
  have hdc : (1 - 1/((d:ℝ)+2)) * ((d:ℝ)+2) = (d:ℝ)+1 := by
    field_simp; ring
  have hkey2 : (d:ℝ)+2 ≤ (1 - 1/((d:ℝ)+2))^d * (Real.exp 1 * ((d:ℝ)+1)) := by
    calc (d:ℝ)+2 = 1 * ((d:ℝ)+2) := by ring
      _ ≤ (Real.exp 1 * (1 - 1/((d:ℝ)+2))^(d+1)) * ((d:ℝ)+2) :=
            mul_le_mul_of_nonneg_right hkey1 (le_of_lt hd2)
      _ = (1 - 1/((d:ℝ)+2))^d * (Real.exp 1 * ((d:ℝ)+1)) := by
            rw [pow_succ, ← hdc]; ring
  rw [div_le_iff₀ (mul_pos he hd1)]
  have hconv : (1/((d:ℝ)+2) * (1 - 1/((d:ℝ)+2))^d) * (Real.exp 1 * ((d:ℝ)+1))
      = ((1 - 1/((d:ℝ)+2))^d * (Real.exp 1 * ((d:ℝ)+1)))/((d:ℝ)+2) := by
    field_simp
  rw [hconv, le_div_iff₀ hd2]
  linarith [hkey2]

/-! ## The general form of the Lovász Local Lemma -/

private theorem lll_aux {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Set Ω) (dep : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hfar : ∀ i (S : Finset ι), (∀ j ∈ S, j ∉ dep i ∧ j ≠ i) →
      μ.Indep (A i) (⋂ j ∈ S, (A j)ᶜ))
    (hbound : ∀ i, μ.prob (A i) ≤ x i * ∏ j ∈ dep i, (1 - x j)) :
    ∀ (N : ℕ) (U V : Finset ι), Disjoint U V → U.card + V.card ≤ N →
      (∏ j ∈ U, (1 - x j)) * μ.prob (⋂ j ∈ V, (A j)ᶜ)
        ≤ μ.prob (⋂ j ∈ U ∪ V, (A j)ᶜ) := by
  intro N
  induction N with
  | zero =>
    intro U V _ hc
    have hU : U = ∅ := Finset.card_eq_zero.mp (by omega)
    have hV : V = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hU; subst hV
    have hb : (⋂ j ∈ (∅ : Finset ι), (A j)ᶜ) = Set.univ := by ext x; simp
    simp [hb, FinProb.prob_univ]
  | succ N ih =>
    intro U V hUV hc
    rcases eq_or_ne U ∅ with hU | hU
    · subst hU
      rw [Finset.prod_empty, Finset.empty_union]
      simp
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hU
      have hnotin : i ∉ U.erase i := Finset.notMem_erase i U
      have hUeq : U = insert i (U.erase i) := (Finset.insert_erase hi).symm
      have hU'card : (U.erase i).card + 1 = U.card := Finset.card_erase_add_one hi
      have hUV' : Disjoint (insert i (U.erase i)) V := by rw [← hUeq]; exact hUV
      have hiV : i ∉ V := (Finset.disjoint_left.mp hUV') (Finset.mem_insert_self i (U.erase i))
      have hU'V : Disjoint (U.erase i) V := Finset.disjoint_left.mpr fun a ha =>
        (Finset.disjoint_left.mp hUV') (Finset.mem_insert_of_mem ha)
      have hiUV' : i ∉ (U.erase i) ∪ V := by
        simp only [Finset.mem_union, not_or]
        exact ⟨hnotin, hiV⟩
      have hcardUV' : ((U.erase i) ∪ V).card ≤ N := by
        rw [Finset.card_union_of_disjoint hU'V]; omega
      -- the key estimate for a single event
      have hkey : μ.prob (A i ∩ ⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ)
          ≤ x i * μ.prob (⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ) := by
        have hfar2 : ∀ j ∈ ((U.erase i) ∪ V) \ dep i, j ∉ dep i ∧ j ≠ i := by
          intro j hj
          rw [Finset.mem_sdiff] at hj
          exact ⟨hj.2, fun hji => hiUV' (hji ▸ hj.1)⟩
        have hind : μ.prob (A i ∩ ⋂ j ∈ ((U.erase i) ∪ V) \ dep i, (A j)ᶜ)
            = μ.prob (A i) * μ.prob (⋂ j ∈ ((U.erase i) ∪ V) \ dep i, (A j)ᶜ) :=
          hfar i _ hfar2
        have hmono : μ.prob (A i ∩ ⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ)
            ≤ μ.prob (A i ∩ ⋂ j ∈ ((U.erase i) ∪ V) \ dep i, (A j)ᶜ) :=
          FinProb.prob_mono μ (Set.inter_subset_inter (Set.Subset.refl _)
            (biInter_compl_mono A Finset.sdiff_subset))
        have hprod : (∏ j ∈ dep i, (1 - x j))
            ≤ ∏ j ∈ ((U.erase i) ∪ V) ∩ dep i, (1 - x j) :=
          Finset.prod_le_prod_of_subset_of_le_one₀ Finset.inter_subset_right
            (fun j _ => by linarith [hx1 j]) (fun j _ _ => by linarith [hx0 j])
        have hdis : Disjoint (((U.erase i) ∪ V) ∩ dep i) (((U.erase i) ∪ V) \ dep i) :=
          Finset.disjoint_left.mpr fun _ ha hb =>
            (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mp ha).2
        have huni : ((U.erase i) ∪ V) ∩ dep i ∪ ((U.erase i) ∪ V) \ dep i
            = (U.erase i) ∪ V := by
          rw [Finset.union_comm, Finset.sdiff_union_inter]
        have hcardIH : (((U.erase i) ∪ V) ∩ dep i).card
            + (((U.erase i) ∪ V) \ dep i).card ≤ N := by
          have h1 : (((U.erase i) ∪ V) ∩ dep i).card
              + (((U.erase i) ∪ V) \ dep i).card = ((U.erase i) ∪ V).card := by
            rw [← Finset.card_union_of_disjoint hdis, huni]
          omega
        have hIHkey : (∏ j ∈ ((U.erase i) ∪ V) ∩ dep i, (1 - x j))
              * μ.prob (⋂ j ∈ ((U.erase i) ∪ V) \ dep i, (A j)ᶜ)
            ≤ μ.prob (⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ) := by
          have h := ih (((U.erase i) ∪ V) ∩ dep i) (((U.erase i) ∪ V) \ dep i) hdis hcardIH
          rwa [huni] at h
        calc μ.prob (A i ∩ ⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ)
            ≤ μ.prob (A i ∩ ⋂ j ∈ ((U.erase i) ∪ V) \ dep i, (A j)ᶜ) := hmono
          _ = μ.prob (A i) * μ.prob (⋂ j ∈ ((U.erase i) ∪ V) \ dep i, (A j)ᶜ) := hind
          _ ≤ (x i * ∏ j ∈ dep i, (1 - x j))
                * μ.prob (⋂ j ∈ ((U.erase i) ∪ V) \ dep i, (A j)ᶜ) :=
                mul_le_mul_of_nonneg_right (hbound i) (FinProb.prob_nonneg μ _)
          _ ≤ (x i * ∏ j ∈ ((U.erase i) ∪ V) ∩ dep i, (1 - x j))
                * μ.prob (⋂ j ∈ ((U.erase i) ∪ V) \ dep i, (A j)ᶜ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (hx0 i))
                  (FinProb.prob_nonneg μ _)
          _ = x i * ((∏ j ∈ ((U.erase i) ∪ V) ∩ dep i, (1 - x j))
                * μ.prob (⋂ j ∈ ((U.erase i) ∪ V) \ dep i, (A j)ᶜ)) := by ring
          _ ≤ x i * μ.prob (⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ) :=
                mul_le_mul_of_nonneg_left hIHkey (hx0 i)
      have hIHmain : (∏ j ∈ U.erase i, (1 - x j)) * μ.prob (⋂ j ∈ V, (A j)ᶜ)
          ≤ μ.prob (⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ) :=
        ih (U.erase i) V hU'V (by omega)
      have hUVu : U ∪ V = insert i ((U.erase i) ∪ V) :=
        (congrArg (fun s => s ∪ V) hUeq).trans (Finset.insert_union i (U.erase i) V)
      have hinter : (⋂ j ∈ U ∪ V, (A j)ᶜ) = (A i)ᶜ ∩ ⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ := by
        rw [hUVu, Finset.set_biInter_insert]
      have hpc := prob_compl_inter μ (A i) (⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ)
      have hprodU : (∏ j ∈ U, (1 - x j)) = (1 - x i) * (∏ j ∈ U.erase i, (1 - x j)) := by
        conv_lhs => rw [hUeq]
        exact Finset.prod_insert hnotin
      calc (∏ j ∈ U, (1 - x j)) * μ.prob (⋂ j ∈ V, (A j)ᶜ)
          = (1 - x i) * ((∏ j ∈ U.erase i, (1 - x j)) * μ.prob (⋂ j ∈ V, (A j)ᶜ)) := by
            rw [hprodU]; ring
        _ ≤ (1 - x i) * μ.prob (⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ) :=
            mul_le_mul_of_nonneg_left hIHmain (by linarith [hx1 i])
        _ ≤ μ.prob (⋂ j ∈ U ∪ V, (A j)ᶜ) := by
            rw [hinter, hpc]
            linarith [hkey]

/-- **Lovász Local Lemma, general (asymmetric) form.** If `x i ∈ [0,1)` and
`P(A i) ≤ x i * ∏_{j ∈ dep i} (1 - x j)` for every `i`, and each `A i` is
independent of every intersection of complements of events with indices outside
`dep i ∪ {i}`, then `∏ i, (1 - x i) ≤ P(⋂ i, (A i)ᶜ)`. -/
theorem lll_general {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Set Ω) (dep : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hfar : ∀ i (S : Finset ι), (∀ j ∈ S, j ∉ dep i ∧ j ≠ i) →
      μ.Indep (A i) (⋂ j ∈ S, (A j)ᶜ))
    (hbound : ∀ i, μ.prob (A i) ≤ x i * ∏ j ∈ dep i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ μ.prob (⋂ i, (A i)ᶜ) := by
  have h1 : (∏ j ∈ (Finset.univ : Finset ι), (1 - x j))
        * μ.prob (⋂ j ∈ (∅ : Finset ι), (A j)ᶜ)
      ≤ μ.prob (⋂ j ∈ (Finset.univ : Finset ι) ∪ ∅, (A j)ᶜ) :=
    lll_aux μ A dep x hx0 hx1 hfar hbound (Fintype.card ι) Finset.univ ∅
      (by rw [Finset.disjoint_iff_inter_eq_empty]; simp) (by simp)
  have h2 : μ.prob (⋂ j ∈ (∅ : Finset ι), (A j)ᶜ) = 1 := by
    have hb : (⋂ j ∈ (∅ : Finset ι), (A j)ᶜ) = Set.univ := by ext x; simp
    rw [hb, FinProb.prob_univ]
  have h3 : (⋂ j ∈ (Finset.univ : Finset ι), (A j)ᶜ) = ⋂ j, (A j)ᶜ := by
    ext x; simp
  rw [Finset.union_empty, h2, mul_one, h3] at h1
  exact h1

/-! ## The symmetric form -/

/-- **Symmetric Lovász Local Lemma**: if each event `A i` is independent of the
family of events whose indices lie outside `dep i`, each `A i` has probability
at most `p`, and each `dep i` has at most `d` elements, then `e·p·(d+1) ≤ 1`
implies that with positive probability none of the events occur:
`P(⋂ i, (A i)ᶜ) > 0`. -/
theorem lll_symmetric {Ω : Type*} [Fintype Ω] (μ : FinProb Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → Set Ω) (dep : ι → Finset ι) (d : ℕ) (p : ℝ)
    (hcard : ∀ i, (dep i).card ≤ d)
    (hfar : ∀ i (S : Finset ι), (∀ j ∈ S, j ∉ dep i ∧ j ≠ i) →
      μ.Indep (A i) (⋂ j ∈ S, (A j)ᶜ))
    (hp0 : 0 ≤ p) (hp : ∀ i, μ.prob (A i) ≤ p)
    (hpp : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) :
    0 < μ.prob (⋂ i, (A i)ᶜ) := by
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hd1 : (0:ℝ) < (d:ℝ)+1 := by positivity
  have hd2 : (0:ℝ) < (d:ℝ)+2 := by positivity
  have hc0 : (0:ℝ) ≤ 1/((d:ℝ)+2) := by positivity
  have hc1 : 1/((d:ℝ)+2) < 1 := by
    rw [div_lt_one hd2]
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hb0 : (0:ℝ) ≤ 1 - 1/((d:ℝ)+2) := by linarith
  have hb1 : 1 - 1/((d:ℝ)+2) ≤ 1 := by linarith
  have hbound : ∀ i : ι, μ.prob (A i)
      ≤ (1/((d:ℝ)+2)) * ∏ j ∈ dep i, (1 - 1/((d:ℝ)+2)) := by
    intro i
    have hp1 : p ≤ 1/(Real.exp 1 * ((d:ℝ)+1)) := by
      rw [le_div_iff₀ (mul_pos he hd1)]
      linarith [hpp]
    have hpow : (1 - 1/((d:ℝ)+2))^d ≤ (1 - 1/((d:ℝ)+2))^((dep i).card) :=
      pow_le_pow_of_le_one hb0 hb1 (hcard i)
    calc μ.prob (A i) ≤ p := hp i
      _ ≤ 1/(Real.exp 1 * ((d:ℝ)+1)) := hp1
      _ ≤ (1/((d:ℝ)+2)) * (1 - 1/((d:ℝ)+2))^d := key_ineq d
      _ ≤ (1/((d:ℝ)+2)) * (1 - 1/((d:ℝ)+2))^((dep i).card) :=
            mul_le_mul_of_nonneg_left hpow hc0
      _ = (1/((d:ℝ)+2)) * ∏ j ∈ dep i, (1 - 1/((d:ℝ)+2)) := by rw [Finset.prod_const]
  have hgen := lll_general μ A dep (fun _ : ι => 1/((d:ℝ)+2))
    (fun _ => hc0) (fun _ => hc1) hfar hbound
  have hpos : 0 < ∏ i : ι, (1 - 1/((d:ℝ)+2)) :=
    Finset.prod_pos fun _ _ => by linarith
  exact lt_of_lt_of_le hpos hgen

end Work.Deep.Reed.Prob
