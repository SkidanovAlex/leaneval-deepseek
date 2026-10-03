import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.layer_sunflower_bound
import Submission.Work.BourgainPlan.IonescuWainger.powerset_subtype_bridge

open Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.BourgainPlan.IonescuWainger

variable {S : Finset ℕ}

/-! ## The three "core" sums -/

/-- The value attached to a tuple `B` of petals for a fixed core `D`: `Σ_x ∏_i ‖f_{D ∪ B_i}(x)‖²`,
killed unless the petals are pairwise disjoint. -/
noncomputable def petalValue (r : ℕ) (f : Finset ℕ → ℤ → ℂ) (D : Finset ↥S)
    (B : Fin r → Finset ↥S) : ℝ :=
  if (∀ i j : Fin r, i ≠ j → Disjoint (B i) (B j))
  then ∑' x : ℤ, ∏ i, ‖f (phiSet S (D ∪ B i)) x‖ ^ 2 else 0

/-- The inner sum of the single-layer sunflower bound (`tsum_sq_pow_le_sunflower`) for the layer of
sets of cardinality `k'` and a core `D ⊆ ↥S`. -/
noncomputable def layerCore (r : ℕ) (f : Finset ℕ → ℤ → ℂ) (k' : ℕ) (D : Finset ↥S) : ℝ :=
  ∑ B : Fin r → Finset ↥S,
    (if (∀ i, B i ⊆ (Finset.univ : Finset ↥S) \ D) ∧ (∀ i, (B i).card = k' - D.card) ∧
        (∀ i j : Fin r, i ≠ j → Disjoint (B i) (B j))
     then ∑' x : ℤ, ∏ i, ‖f (phiSet S (D ∪ B i)) x‖ ^ 2 else 0)

/-- The right-hand side of the layer-wise sunflower bound for a fixed core `D` on the `↥S`-side. -/
noncomputable def mergedCore (k r : ℕ) (f : Finset ℕ → ℤ → ℂ) (D : Finset ↥S) : ℝ :=
  ∑ B : (i : Fin r) → ↥(((Finset.univ : Finset ↥S) \ D).powerset.filter
      (fun B => B.card ≤ k - D.card)),
    petalValue r f D (fun i => (B i).1)

/-- The right-hand side of the layer-wise sunflower bound for a fixed core `A₀` on the `ℕ`-side
(this is the form consumed by `comp_sum_bound`). -/
noncomputable def targetCore (k r : ℕ) (f : Finset ℕ → ℤ → ℂ) (A₀ : Finset ℕ) : ℝ :=
  ∑ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
    (if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
     then ∑' x : ℤ, ∏ i, ‖f (A₀ ∪ (A i).1) x‖ ^ 2 else 0)

lemma petalValue_nonneg {r : ℕ} (f : Finset ℕ → ℤ → ℂ) (D : Finset ↥S)
    (B : Fin r → Finset ↥S) : 0 ≤ petalValue r f D B := by
  rw [petalValue]
  by_cases hd : (∀ i j : Fin r, i ≠ j → Disjoint (B i) (B j))
  · rw [if_pos hd]
    exact tsum_nonneg (fun x => Finset.prod_nonneg (fun i _ => sq_nonneg _))
  · rw [if_neg hd]

/-! ## Step 1: the layer decomposition and the power mean -/

lemma tsum_layer_pow_mean {k r : ℕ} (hr : 1 ≤ r) (f : Finset ℕ → ℤ → ℂ)
    (hf : ∀ A, Memℓp (f A) 2) :
    ∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun A => A.card ≤ k),
        ‖f (phiSet S A) x‖ ^ 2) ^ r
      ≤ (k + 1 : ℝ) ^ (r - 1) * ∑ k' ∈ Finset.range (k + 1),
          ∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun A => A.card = k'),
            ‖f (phiSet S A) x‖ ^ 2) ^ r := by
  classical
  have hsum : ∀ k' ∈ Finset.range (k + 1),
      Summable (fun x : ℤ => ∑ A ∈ (Finset.univ : Finset (Finset ↥S)).filter
        (fun A => A.card = k'), ‖f (phiSet S A) x‖ ^ 2) :=
    fun k' _ => summable_finset_sum (fun A _ => summable_norm_sq_of_memℓp (hf (phiSet S A)))
  rw [show (∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ↥S)).filter
        (fun A => A.card ≤ k), ‖f (phiSet S A) x‖ ^ 2) ^ r)
      = ∑' x : ℤ, (∑ k' ∈ Finset.range (k + 1),
          ∑ A ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun A => A.card = k'),
            ‖f (phiSet S A) x‖ ^ 2) ^ r from
    tsum_congr (fun x => by rw [sum_filter_card_le_eq_sum_layers])]
  have h := tsum_pow_sum_le_mul_sum_tsum_pow (s := Finset.range (k + 1)) (r := r) hr
    (u := fun k' x => ∑ A ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun A => A.card = k'),
      ‖f (phiSet S A) x‖ ^ 2)
    (fun k' _ x => Finset.sum_nonneg (fun A _ => sq_nonneg _)) hsum
  simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using h

/-! ## Step 2: the single-layer sunflower bound -/

lemma layer_core_bound {k k' r M : ℕ} (hr : 2 ≤ r) (hM : 2 ≤ M) (hk' : k' ≤ k)
    (hsun : ∀ T : Finset (Finset ℕ), (∀ A ∈ T, A ⊆ S) → (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
      ∃ A : Fin r → Finset ℕ, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A)
    (f : Finset ℕ → ℤ → ℂ) (hf : ∀ A, Memℓp (f A) 2) :
    ∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun A => A.card = k'),
        ‖f (phiSet S A) x‖ ^ 2) ^ r
      ≤ (4 * M : ℝ) ^ r * ∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter
          (fun D => D.card ≤ k'), layerCore r f k' D := by
  have h := tsum_sq_pow_le_sunflower (α := ↥S) (r := r) (k := k') (M := M) hr hM
    (hsun_subtype (S := S) hk' hsun) (fun A => f (phiSet S A)) (fun A => hf (phiSet S A))
  simpa only [layerCore] using h

/-! ## Step 3: the layer merge -/

/-- For a common petal universe `U` and a nonnegative function `H` of tuples of petals, the sum over
the layers of common petal cardinality is at most the sum over all tuples of petals of cardinality at
most `m`. -/
lemma merge_layers {r m : ℕ} (hr : 1 ≤ r) (U : Finset ↥S) (H : (Fin r → Finset ↥S) → ℝ)
    (hH : ∀ B, 0 ≤ H B) :
    (∑ c ∈ Finset.range (m + 1), ∑ B : (i : Fin r) → ↥U.powerset,
        (if (∀ i, ((B i).1).card = c) then H (fun i => (B i).1) else 0))
      ≤ ∑ B : (i : Fin r) → ↥U.powerset,
        (if (∀ i, ((B i).1).card ≤ m) then H (fun i => (B i).1) else 0) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun B _ => ?_)
  by_cases hle : ∀ i, ((B i).1).card ≤ m
  · have hcard : ((B ⟨0, hr⟩).1).card ≤ m := hle ⟨0, hr⟩
    by_cases hall : ∃ c, ∀ i, ((B i).1).card = c
    · obtain ⟨c0, hc0⟩ := hall
      have hmem : c0 ∈ Finset.range (m + 1) :=
        Finset.mem_range.mpr (by rw [← hc0 ⟨0, hr⟩]; exact Nat.lt_succ_of_le hcard)
      rw [Finset.sum_eq_single c0 ?_ ?_, if_pos hc0, if_pos hle]
      · intro c _ hne
        exact if_neg (fun hc => hne (by rw [← hc ⟨0, hr⟩, hc0 ⟨0, hr⟩]))
      · intro hc; exact absurd hmem hc
    · rw [Finset.sum_eq_zero (fun c _ => if_neg (fun hc => hall ⟨c, hc⟩)), if_pos hle]
      exact hH _
  · rw [if_neg hle]
    refine le_of_eq (Finset.sum_eq_zero (fun c hc => if_neg (fun hc' => ?_)))
    obtain ⟨i, hi⟩ := not_forall.mp hle
    rw [not_le] at hi
    have hcm : c ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
    have : ((B i).1).card ≤ m := by rw [hc' i]; exact hcm
    exact absurd hi (not_lt.mpr this)

/-- **The exact-cardinality layer as a sum over petals with an indicator.** -/
lemma layerCore_eq {r : ℕ} (f : Finset ℕ → ℤ → ℂ) (D : Finset ↥S) {k' c : ℕ}
    (hk : k' - D.card = c) :
    layerCore r f k' D
      = ∑ B : (i : Fin r) → ↥(((Finset.univ : Finset ↥S) \ D).powerset),
          (if (∀ i, ((B i).1).card = c) then petalValue r f D (fun i => (B i).1) else 0) := by
  classical
  rw [layerCore]
  have h1 : (∑ B : Fin r → Finset ↥S,
        (if (∀ i, B i ⊆ (Finset.univ : Finset ↥S) \ D) ∧
            (∀ i, (B i).card = k' - D.card) ∧
            (∀ i j : Fin r, i ≠ j → Disjoint (B i) (B j))
         then ∑' x : ℤ, ∏ i, ‖f (phiSet S (D ∪ B i)) x‖ ^ 2 else 0))
      = ∑ B : Fin r → Finset ↥S,
        (if (∀ i, B i ∈ ((Finset.univ : Finset ↥S) \ D).powerset) then
          (if (∀ i, (B i).card = c) then petalValue r f D B else 0) else 0) := by
    refine Finset.sum_congr rfl (fun B _ => ?_)
    rw [petalValue]
    by_cases h1 : (∀ i, B i ⊆ (Finset.univ : Finset ↥S) \ D) ∧
        (∀ i, (B i).card = k' - D.card) ∧ (∀ i j : Fin r, i ≠ j → Disjoint (B i) (B j))
    · rw [if_pos h1, if_pos ((by simp only [Finset.mem_powerset]; exact h1.1)),
        if_pos (by rw [← hk]; exact h1.2.1), if_pos h1.2.2]
    · rw [if_neg h1]
      by_cases h2 : (∀ i, B i ∈ ((Finset.univ : Finset ↥S) \ D).powerset)
      · rw [if_pos h2]
        by_cases h3 : (∀ i, (B i).card = c)
        · rw [if_pos h3, if_neg (fun hd => h1 ⟨(by simp only [Finset.mem_powerset] at h2; exact h2),
            by rw [hk]; exact h3, hd⟩)]
        · rw [if_neg h3]
      · rw [if_neg h2]
  rw [h1, sum_all_tuples_ite_piFinset, sum_piFinset_eq_sum_tuple_subtype]

/-! ## Step 4: the transport of the merged core sum -/

/-- **`mergedCore` in the `ℕ`-parameterisation.** -/
lemma mergedCore_eq_targetCore {k r : ℕ} (f : Finset ℕ → ℤ → ℂ) (D : Finset ↥S) :
    mergedCore (S := S) k r f D = targetCore (S := S) k r f (phiSet S D) := by
  classical
  have key : ∀ B : Fin r → Finset ↥S,
      petalValue r f D B
      = (if (∀ i j : Fin r, i ≠ j → Disjoint (phiSet S (B i)) (phiSet S (B j)))
         then ∑' x : ℤ, ∏ i, ‖f (phiSet S D ∪ phiSet S (B i)) x‖ ^ 2 else 0) := by
    intro B
    rw [petalValue]
    by_cases hd : ∀ i j : Fin r, i ≠ j → Disjoint (B i) (B j)
    · rw [if_pos hd, if_pos (fun i j hij => (phiSet_disjoint (B i) (B j)).mp (hd i j hij))]
      refine tsum_congr (fun x => ?_)
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [phiSet_union]
    · rw [if_neg hd, if_neg (fun hd' => hd (fun i j hij =>
        (phiSet_disjoint (B i) (B j)).mpr (hd' i j hij)))]
  rw [mergedCore, targetCore, phiSet_card]
  rw [← sum_tuple_subtype_ite ((Finset.univ : Finset ↥S) \ D).powerset
    (fun B => B.card ≤ k - D.card) (petalValue r f D)]
  rw [show (∑ B : (i : Fin r) → ↥(((Finset.univ : Finset ↥S) \ D).powerset),
        (if (∀ i, ((B i).1).card ≤ k - D.card) then petalValue r f D (fun i => (B i).1) else 0))
      = ∑ B : (i : Fin r) → ↥(((Finset.univ : Finset ↥S) \ D).powerset),
        (if (∀ i, ((B i).1).card ≤ k - D.card) then
          (if (∀ i j : Fin r, i ≠ j → Disjoint (phiSet S ((B i).1)) (phiSet S ((B j).1)))
           then ∑' x : ℤ, ∏ i, ‖f (phiSet S D ∪ phiSet S ((B i).1)) x‖ ^ 2 else 0) else 0)
      from Finset.sum_congr rfl (fun B _ => by rw [key (fun i => (B i).1)])]
  rw [sum_tuple_subtype_ite ((Finset.univ : Finset ↥S) \ D).powerset
    (fun B => B.card ≤ k - D.card)
    (fun B => (if (∀ i j : Fin r, i ≠ j → Disjoint (phiSet S (B i)) (phiSet S (B j)))
       then ∑' x : ℤ, ∏ i, ‖f (phiSet S D ∪ phiSet S (B i)) x‖ ^ 2 else 0))]
  exact sum_tuples_powerset_eq_sum_tuples_powerset (S := S) D
    (fun T => (if (∀ i j : Fin r, i ≠ j → Disjoint (T i) (T j))
       then ∑' x : ℤ, ∏ i, ‖f (phiSet S D ∪ T i) x‖ ^ 2 else 0))

/-! ## Step 5: the reindexing of the layers -/

lemma layer_reindex {k r : ℕ} (f : Finset ℕ → ℤ → ℂ) :
    (∑ k' ∈ Finset.range (k + 1), ∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter
        (fun D => D.card ≤ k'), layerCore r f k' D)
      = ∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun D => D.card ≤ k),
          ∑ c ∈ Finset.range (k - D.card + 1), layerCore r f (D.card + c) D := by
  classical
  have hA : ∀ k' ∈ Finset.range (k + 1),
      (∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun D => D.card ≤ k'),
          layerCore r f k' D)
      = ∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun D => D.card ≤ k),
          (if D.card ≤ k' then layerCore r f k' D else 0) := by
    intro k' hk'
    have hk'le : k' ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk')
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun D _ => rfl)
    ext D
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨le_trans h hk'le, h⟩, fun h => h.2⟩
  have hA' : (∑ k' ∈ Finset.range (k + 1), ∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter
        (fun D => D.card ≤ k'), layerCore r f k' D)
      = ∑ k' ∈ Finset.range (k + 1), ∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter
        (fun D => D.card ≤ k), (if D.card ≤ k' then layerCore r f k' D else 0) :=
    Finset.sum_congr rfl hA
  rw [hA', Finset.sum_comm]
  refine Finset.sum_congr rfl (fun D hD => ?_)
  have hDk : D.card ≤ k := (Finset.mem_filter.mp hD).2
  rw [← Finset.sum_filter]
  have hset : (Finset.range (k + 1)).filter (fun k' => D.card ≤ k') = Finset.Ico D.card (k + 1) := by
    ext k'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have hidx : k + 1 - D.card = k - D.card + 1 := by omega
  rw [hidx]

/-! ## Step 6: the per-core merge -/

/-- **The per-core merge.**  For a fixed core `D` of cardinality at most `k`, the sum over the
petal cardinalities `c ≤ k - |D|` of the layer bounds is at most the merged bound. -/
lemma layerCore_sum_le_mergedCore {k r : ℕ} (hr : 1 ≤ r) (f : Finset ℕ → ℤ → ℂ)
    (D : Finset ↥S) (_hD : D.card ≤ k) :
    (∑ c ∈ Finset.range (k - D.card + 1), layerCore r f (D.card + c) D)
      ≤ mergedCore (S := S) k r f D := by
  classical
  have hstep1 : (∑ c ∈ Finset.range (k - D.card + 1), layerCore r f (D.card + c) D)
      = ∑ c ∈ Finset.range (k - D.card + 1), ∑ B : (i : Fin r) →
            ↥(((Finset.univ : Finset ↥S) \ D).powerset),
          (if (∀ i, ((B i).1).card = c) then petalValue r f D (fun i => (B i).1) else 0) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    exact layerCore_eq (S := S) f D (k' := D.card + c) (c := c) (Nat.add_sub_cancel_left _ _)
  have hstep2 := merge_layers (S := S) (r := r) (m := k - D.card) hr
    ((Finset.univ : Finset ↥S) \ D) (petalValue r f D) (fun B => petalValue_nonneg f D B)
  have hstep3 : (∑ B : (i : Fin r) → ↥(((Finset.univ : Finset ↥S) \ D).powerset),
        (if (∀ i, ((B i).1).card ≤ k - D.card) then petalValue r f D (fun i => (B i).1)
         else 0))
      = mergedCore (S := S) k r f D := by
    rw [mergedCore]
    rw [← sum_tuple_subtype_ite ((Finset.univ : Finset ↥S) \ D).powerset
      (fun B => B.card ≤ k - D.card) (petalValue r f D)]
  calc (∑ c ∈ Finset.range (k - D.card + 1), layerCore r f (D.card + c) D)
      = ∑ c ∈ Finset.range (k - D.card + 1), ∑ B : (i : Fin r) →
            ↥(((Finset.univ : Finset ↥S) \ D).powerset),
          (if (∀ i, ((B i).1).card = c) then petalValue r f D (fun i => (B i).1) else 0) := hstep1
    _ ≤ ∑ B : (i : Fin r) → ↥(((Finset.univ : Finset ↥S) \ D).powerset),
          (if (∀ i, ((B i).1).card ≤ k - D.card) then petalValue r f D (fun i => (B i).1)
           else 0) := hstep2
    _ = mergedCore (S := S) k r f D := hstep3

/-! ## The target theorem -/

/-- **The layer-wise sunflower bound in the `S.powerset` parameterisation** (the form consumed by
`comp_sum_bound`).  Splitting `Σ_{|A| ≤ k}` into its `k'`-layers (`k' ≤ k`), applying Tao's sunflower
bound `tsum_sq_pow_le_sunflower` at each layer and merging the layers (for a fixed core `A₀` of
cardinality `a`, the layers `k' = a, …, k` run through the petal cardinalities `k' - a`, i.e. over
`≤ k - a`) gives

`Σ_x (Σ_{A ⊆ S, |A| ≤ k} ‖f_A(x)‖²)^r ≤ (k+1)^{r-1} (4M)^r
   Σ_{A₀ ⊆ S, |A₀| ≤ k} Σ^{**}_{A₁,…,A_r} Σ_x ∏_i ‖f_{A₀∪A_i}(x)‖²`,

the inner sum running over tuples of pairwise disjoint `A_i ⊆ S ∖ A₀` with `|A_i| ≤ k - |A₀|`. -/
theorem layer_sunflower_bound_powerset {S : Finset ℕ} {k r M : ℕ} (hr : 2 ≤ r) (hM : 2 ≤ M)
    (hsun : ∀ T : Finset (Finset ℕ), (∀ A ∈ T, A ⊆ S) → (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
      ∃ A : Fin r → Finset ℕ, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A)
    (f : Finset ℕ → ℤ → ℂ) (hf : ∀ A, Memℓp (f A) 2) :
    ∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), ‖f A x‖ ^ 2) ^ r
      ≤ (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
              (if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
               then ∑' x : ℤ, ∏ i, ‖f (A₀ ∪ (A i).1) x‖ ^ 2 else 0) := by
  classical
  have hr1 : 1 ≤ r := by omega
  have hL : (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), ‖f A x‖ ^ 2) ^ r)
      = ∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun A => A.card ≤ k),
          ‖f (phiSet S A) x‖ ^ 2) ^ r :=
    tsum_congr (fun x => by rw [sum_powerset_eq_sum_subtype (S := S) (P := fun c => c ≤ k) f x])
  have h1 := tsum_layer_pow_mean (S := S) (k := k) (r := r) hr1 f hf
  have h2 : (∑ k' ∈ Finset.range (k + 1),
        ∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun A => A.card = k'),
          ‖f (phiSet S A) x‖ ^ 2) ^ r)
      ≤ ∑ k' ∈ Finset.range (k + 1), (4 * M : ℝ) ^ r *
          ∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun D => D.card ≤ k'),
            layerCore r f k' D :=
    Finset.sum_le_sum (fun k' hk' => layer_core_bound (S := S) (k := k) (k' := k') (r := r)
      (M := M) hr hM (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk')) hsun f hf)
  have h3 : (∑ k' ∈ Finset.range (k + 1), ∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter
        (fun D => D.card ≤ k'), layerCore r f k' D)
      ≤ ∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun D => D.card ≤ k),
          mergedCore (S := S) k r f D := by
    rw [layer_reindex (S := S) (k := k) (r := r) f]
    exact Finset.sum_le_sum (fun D hD => layerCore_sum_le_mergedCore (S := S) (k := k) (r := r)
      hr1 f D (Finset.mem_filter.mp hD).2)
  have hout : (∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun D => D.card ≤ k),
        mergedCore (S := S) k r f D)
      = ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k), targetCore (S := S) k r f A₀ := by
    rw [← sum_powerset_filter_eq_sum_subtype (S := S) (P := fun c => c ≤ k)
      (F := fun D => mergedCore (S := S) k r f D)]
    refine Finset.sum_congr rfl (fun A₀ hA₀ => ?_)
    rw [mergedCore_eq_targetCore (S := S) (k := k) (r := r) f (psiSet S A₀),
      phiSet_psiSet (S := S) (Finset.mem_powerset.mp (Finset.mem_filter.mp hA₀).1)]
  rw [hL]
  calc ∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun A => A.card ≤ k),
        ‖f (phiSet S A) x‖ ^ 2) ^ r
      ≤ (k + 1 : ℝ) ^ (r - 1) * ∑ k' ∈ Finset.range (k + 1),
          ∑' x : ℤ, (∑ A ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun A => A.card = k'),
            ‖f (phiSet S A) x‖ ^ 2) ^ r := h1
    _ ≤ (k + 1 : ℝ) ^ (r - 1) * ∑ k' ∈ Finset.range (k + 1), (4 * M : ℝ) ^ r *
          ∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun D => D.card ≤ k'),
            layerCore r f k' D := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r * ∑ k' ∈ Finset.range (k + 1),
          ∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun D => D.card ≤ k'),
            layerCore r f k' D := by
        rw [← Finset.mul_sum, mul_assoc]
    _ ≤ (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ D ∈ (Finset.univ : Finset (Finset ↥S)).filter (fun D => D.card ≤ k),
            mergedCore (S := S) k r f D := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            targetCore (S := S) k r f A₀ := by rw [hout]
    _ = (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
              (if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
               then ∑' x : ℤ, ∏ i, ‖f (A₀ ∪ (A i).1) x‖ ^ 2 else 0) := rfl

end Work.BourgainPlan.IonescuWainger
