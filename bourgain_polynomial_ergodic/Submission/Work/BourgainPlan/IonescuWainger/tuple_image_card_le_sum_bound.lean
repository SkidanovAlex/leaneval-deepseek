import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.binom_partial_sum_succ
import Submission.Work.BourgainPlan.IonescuWainger.sum_insert_card_le

namespace Work.BourgainPlan.IonescuWainger
open Finset

variable {β : Type*} [Fintype β] [DecidableEq β]


lemma image_univ_snoc {n : ℕ} (g : Fin n → β) (a : β) :
    Finset.univ.image (Fin.snoc g a) = insert a (Finset.univ.image g) := by
  ext b
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.lastCases with
    | last => exact Or.inl (by simpa [Fin.snoc_last] using hi.symm)
    | cast j => exact Or.inr ⟨j, by simpa [Fin.snoc_castSucc] using hi⟩
  · rintro (rfl | ⟨j, hj⟩)
    · exact ⟨Fin.last n, by rw [Fin.snoc_last]⟩
    · exact ⟨j.castSucc, by rw [Fin.snoc_castSucc, hj]⟩

lemma prod_snoc (p : β → NNReal) {n : ℕ} (g : Fin n → β) (a : β) :
    ∏ i : Fin (n+1), p ((Fin.snoc g a : Fin (n+1) → β) i) = (∏ i : Fin n, p (g i)) * p a := by
  rw [Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

noncomputable def F (p : β → NNReal) (n k : ℕ) : NNReal :=
  ∑ g : Fin n → β, if (Finset.univ.image g).card ≤ k then ∏ i : Fin n, p (g i) else 0

noncomputable def B (P c : NNReal) (n k : ℕ) : NNReal :=
  ∑ m ∈ Finset.range (k+1), (n.choose m : NNReal) * c^(n-m) * P^m

lemma B_succ (P c : NNReal) (m K : ℕ) (hK : 1 ≤ K) :
    B P c (m+1) K = P * B P c m (K-1) + c * B P c m K := by
  unfold B
  rw [Nat.sub_add_cancel hK]
  exact binom_partial_sum_succ P c m K

lemma F_succ_le (p : β → NNReal) (c : NNReal) (n k : ℕ) (hk : 1 ≤ k)
    (hck : ∀ T : Finset β, T.card ≤ k → ∑ A ∈ T, p A ≤ c) :
    F p (n+1) k ≤ (∑ A : β, p A) * F p n (k-1) + c * F p n k := by
  have h1 : F p (n+1) k
      = ∑ x : β × (Fin n → β),
          (if (Finset.univ.image (Fin.snoc x.2 x.1)).card ≤ k
            then ∏ i : Fin (n+1), p ((Fin.snoc x.2 x.1 : Fin (n+1) → β) i) else 0) := by
    unfold F
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (n+1) => β))
        (fun g : Fin (n+1) → β => (if (Finset.univ.image g).card ≤ k then ∏ i : Fin (n+1), p (g i) else 0))]
    apply Finset.sum_congr rfl
    intro x _
    rw [show (Fin.snocEquiv (fun _ : Fin (n+1) => β)) x = Fin.snoc x.2 x.1 from
        funext (fun i => by rw [Fin.snocEquiv_apply])]
  rw [h1]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have h2 : ∀ g' : Fin n → β,
      (∑ a : β, (if (Finset.univ.image (Fin.snoc g' a)).card ≤ k
            then ∏ i : Fin (n+1), p ((Fin.snoc g' a : Fin (n+1) → β) i) else 0))
      = (∏ i : Fin n, p (g' i))
          * (∑ a : β, (if (insert a (Finset.univ.image g')).card ≤ k then p a else 0)) := by
    intro g'
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [image_univ_snoc, prod_snoc]
    by_cases hC : (insert a (Finset.univ.image g')).card ≤ k <;> simp [hC]
  rw [Finset.sum_congr rfl (fun g' _ => h2 g')]
  have h3 : ∀ g' : Fin n → β,
      (∏ i : Fin n, p (g' i)) * (∑ a : β, (if (insert a (Finset.univ.image g')).card ≤ k then p a else 0))
      ≤ (∏ i : Fin n, p (g' i))
          * ((∑ A : β, p A) * (if (Finset.univ.image g').card ≤ k-1 then (1:NNReal) else 0)
              + c * (if (Finset.univ.image g').card = k then 1 else 0)) := by
    intro g'
    exact mul_le_mul_of_nonneg_left (sum_insert_card_le p c k hk hck (Finset.univ.image g')) zero_le
  refine le_trans (Finset.sum_le_sum (fun g' _ => h3 g')) ?_
  have e1 : (∑ g' : Fin n → β, (∏ i : Fin n, p (g' i))
        * (if (Finset.univ.image g').card ≤ k-1 then (1:NNReal) else 0)) = F p n (k-1) := by
    unfold F
    apply Finset.sum_congr rfl
    intro g' _
    by_cases h : (Finset.univ.image g').card ≤ k-1 <;> simp [h]
  have e2 : (∑ g' : Fin n → β, (∏ i : Fin n, p (g' i))
        * (if (Finset.univ.image g').card = k then (1:NNReal) else 0)) ≤ F p n k := by
    unfold F
    apply Finset.sum_le_sum
    intro g' _
    by_cases h : (Finset.univ.image g').card = k
    · rw [h]; simp
    · simp [h]
  have hsplit : (∑ g' : Fin n → β, (∏ i : Fin n, p (g' i))
        * ((∑ A : β, p A) * (if (Finset.univ.image g').card ≤ k-1 then (1:NNReal) else 0)
            + c * (if (Finset.univ.image g').card = k then 1 else 0)))
      = (∑ A : β, p A) * (∑ g' : Fin n → β, (∏ i : Fin n, p (g' i))
            * (if (Finset.univ.image g').card ≤ k-1 then (1:NNReal) else 0))
        + c * (∑ g' : Fin n → β, (∏ i : Fin n, p (g' i))
            * (if (Finset.univ.image g').card = k then (1:NNReal) else 0)) := by
    rw [Finset.sum_congr rfl (fun g' _ => by rw [mul_add])]
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g' _
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g' _
      ring
  rw [hsplit, e1]
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left e2 zero_le)

theorem tuple_image_card_le_sum_bound {β : Type*} [Fintype β] [DecidableEq β]
    (p : β → NNReal) (n K : ℕ) (c : NNReal)
    (hc : ∀ T : Finset β, T.card ≤ K → ∑ A ∈ T, p A ≤ c) :
    (∑ g : Fin n → β, if (Finset.univ.image g).card ≤ K then ∏ i : Fin n, p (g i) else 0)
      ≤ ∑ m ∈ Finset.range (K + 1), (n.choose m : NNReal) * c ^ (n - m) * (∑ A : β, p A) ^ m := by
  have key : ∀ n' K', (∀ T : Finset β, T.card ≤ K' → ∑ A ∈ T, p A ≤ c) →
      F p n' K' ≤ B (∑ A : β, p A) c n' K' := by
    intro n'
    induction n' using Nat.strong_induction_on with
    | h n' ih =>
      intro K' hcK'
      rcases n' with _ | m
      · have hF0 : F p 0 K' = 1 := by
          unfold F
          rw [Finset.sum_eq_single (Fin.elim0 : Fin 0 → β)
              (by intro b _ hb; exact (hb (funext (fun i => i.elim0))).elim)
              (by intro h; exact (h (Finset.mem_univ _)).elim)]
          simp
        rw [hF0]
        have hB0 : B (∑ A : β, p A) c 0 K' = 1 := by
          unfold B
          refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
          · intro m hm hne
            rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hne)]
            simp
          · intro h
            exact absurd (Finset.mem_range.mpr (Nat.succ_pos K')) h
          · simp
        rw [hB0]
      · rcases K' with _ | K''
        · have hF0 : F p (m+1) 0 = 0 := by
            unfold F
            apply Finset.sum_eq_zero
            intro g _
            rw [if_neg]
            intro hcon
            have hz : (Finset.univ.image g).card = 0 := Nat.le_zero.mp hcon
            have hempty : Finset.univ.image g = ∅ := Finset.card_eq_zero.mp hz
            have hmem : g (0 : Fin (m+1)) ∈ Finset.univ.image g :=
              Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
            rw [hempty] at hmem
            exact Finset.notMem_empty _ hmem
          rw [hF0]
          exact zero_le
        · have hrec := F_succ_le p c m (K''+1) (Nat.succ_le_succ (Nat.zero_le K'')) hcK'
          have ih1 := ih m (Nat.lt_succ_self m) (K''+1-1)
              (fun T hT => hcK' T (le_trans hT (Nat.sub_le _ 1)))
          have ih2 := ih m (Nat.lt_succ_self m) (K''+1) hcK'
          calc F p (m+1) (K''+1)
              ≤ (∑ A : β, p A) * F p m (K''+1-1) + c * F p m (K''+1) := hrec
            _ ≤ (∑ A : β, p A) * B (∑ A : β, p A) c m (K''+1-1)
                  + c * B (∑ A : β, p A) c m (K''+1) :=
                add_le_add (mul_le_mul_of_nonneg_left ih1 zero_le)
                  (mul_le_mul_of_nonneg_left ih2 zero_le)
            _ = B (∑ A : β, p A) c (m+1) (K''+1) :=
                (B_succ (∑ A : β, p A) c m (K''+1) (Nat.succ_le_succ (Nat.zero_le K''))).symm
  simpa only [F, B] using key n K hc

end Work.BourgainPlan.IonescuWainger
