import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card

open scoped BigOperators

namespace Finset

lemma card_le_card_image_mul {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) (M : ℕ)
    (h : ∀ b, (s.filter (fun a => f a = b)).card ≤ M) :
    s.card ≤ (s.image f).card * M := by
  rw [Finset.card_eq_sum_card_image f]
  calc ∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card
      ≤ ∑ _b ∈ s.image f, M := Finset.sum_le_sum (fun b _ => h b)
    _ = (s.image f).card * M := by rw [Finset.sum_const, smul_eq_mul]

end Finset

namespace Commons.Data.Set

/-- The Finset of `k`-prefixes of the elements of `A`. -/
def restrictFinset {m : ℕ} (A : Finset (Fin m → ℤ)) (k : ℕ) (hk : k ≤ m) : Finset (Fin k → ℤ) :=
  A.image (fun a => fun i : Fin k => a (Fin.castLE hk i))

theorem ncard_le_prod_of_chain {n : ℕ} (S : Set (Fin n → ℤ)) (hS : S.Finite) (K : ℕ → ℕ)
    (h : ∀ (k : ℕ) (hk : k < n) (x : Fin k → ℤ),
      ({y : ℤ | ∃ a ∈ S, (∀ i : Fin k, a (Fin.castLE (Nat.le_of_lt hk) i) = x i) ∧
        a ⟨k, hk⟩ = y}).ncard ≤ K k) :
    S.ncard ≤ ∏ k ∈ Finset.range n, K k := by
  classical
  set A : Finset (Fin n → ℤ) := hS.toFinset with hA
  have hAmem : ∀ a : Fin n → ℤ, a ∈ A ↔ a ∈ S := by
    intro a; rw [hA, Set.Finite.mem_toFinset]
  have hAcard : S.ncard = A.card := by rw [hA, Set.ncard_eq_toFinset_card S hS]
  have hkey : ∀ (k : ℕ) (hk : k ≤ n), (restrictFinset A k hk).card ≤ ∏ j ∈ Finset.range k, K j := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h1 : (restrictFinset A 0 hk).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a _ b _
        funext i
        exact Fin.elim0 i
      simpa using h1
    | succ k ih =>
      intro hk
      have hk0 : k ≤ n := Nat.le_of_succ_le hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      have hfiber : ∀ x : Fin k → ℤ,
          ((restrictFinset A (k+1) hk).filter
            (fun z : Fin (k+1) → ℤ => Fin.init z = x)).card ≤ K k := by
        intro x
        set T : Finset (Fin (k+1) → ℤ) :=
          (restrictFinset A (k+1) hk).filter (fun z : Fin (k+1) → ℤ => Fin.init z = x) with hT
        set Bx : Set ℤ := {y : ℤ | ∃ a ∈ S,
          (∀ i : Fin k, a (Fin.castLE (Nat.le_of_lt hkn) i) = x i) ∧ a ⟨k, hkn⟩ = y} with hBx
        have hBxcard : Bx.ncard ≤ K k := by rw [hBx]; exact h k hkn x
        have hBxfin : Bx.Finite := by
          refine Set.Finite.subset (hS.image (fun a : Fin n → ℤ => a ⟨k, hkn⟩)) ?_
          intro y hy
          rw [hBx] at hy
          obtain ⟨a, haS, _, hay⟩ := hy
          exact ⟨a, haS, hay⟩
        have hinj : Set.InjOn (fun z : Fin (k+1) → ℤ => z (Fin.last k))
            (T : Set (Fin (k+1) → ℤ)) := by
          intro z hz z' hz' heq
          simp only [hT, Finset.mem_coe, Finset.mem_filter] at hz hz'
          have hinit : Fin.init z = Fin.init z' := by rw [hz.2, hz'.2]
          funext i
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · exact congrFun hinit j
          · exact heq
        have hmap : ∀ z ∈ (T : Set (Fin (k+1) → ℤ)), z (Fin.last k) ∈ Bx := by
          intro z hz
          simp only [hT, Finset.mem_coe, Finset.mem_filter] at hz
          obtain ⟨hzL, hzx⟩ := hz
          simp only [restrictFinset, Finset.mem_image] at hzL
          obtain ⟨a, haA, haz⟩ := hzL
          rw [hBx]
          refine ⟨a, (hAmem a).mp haA, ?_, ?_⟩
          · intro i
            have h1 : a (Fin.castLE hk0 i) = z i.castSucc := by
              have hcast : Fin.castLE hk0 i = Fin.castLE hk i.castSucc := Fin.ext rfl
              rw [hcast]; exact congrFun haz i.castSucc
            have h2 : z i.castSucc = x i := by
              have := congrFun hzx i
              simpa [Fin.init] using this
            exact h1.trans h2
          · have hcast : (⟨k, hkn⟩ : Fin n) = Fin.castLE hk (Fin.last k) := Fin.ext rfl
            rw [hcast]
            exact congrFun haz (Fin.last k)
        calc T.card = (T : Set (Fin (k+1) → ℤ)).ncard := (Set.ncard_coe_finset T).symm
          _ ≤ Bx.ncard := Set.ncard_le_ncard_of_injOn
              (fun z : Fin (k+1) → ℤ => z (Fin.last k)) hmap hinj hBxfin
          _ ≤ K k := hBxcard
      have stepA := Finset.card_le_card_image_mul (restrictFinset A (k+1) hk)
        (fun z : Fin (k+1) → ℤ => Fin.init z) (K k) hfiber
      have stepB : ((restrictFinset A (k+1) hk).image (fun z : Fin (k+1) → ℤ => Fin.init z)).card
          ≤ (restrictFinset A k hk0).card := by
        apply Finset.card_le_card
        intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨z, hzL, rfl⟩ := hy
        simp only [restrictFinset, Finset.mem_image] at hzL ⊢
        obtain ⟨a, haA, haz⟩ := hzL
        refine ⟨a, haA, ?_⟩
        funext i
        have hcast : Fin.castLE hk0 i = Fin.castLE hk i.castSucc := Fin.ext rfl
        rw [hcast, ← haz]
        simp [Fin.init]
      have step : (restrictFinset A (k+1) hk).card ≤ (restrictFinset A k hk0).card * K k :=
        le_trans stepA (Nat.mul_le_mul_right _ stepB)
      calc (restrictFinset A (k+1) hk).card ≤ (restrictFinset A k hk0).card * K k := step
        _ ≤ (∏ j ∈ Finset.range k, K j) * K k := Nat.mul_le_mul_right _ (ih hk0)
        _ = ∏ j ∈ Finset.range (k+1), K j := by rw [Finset.prod_range_succ]
  have htop : A.card ≤ (restrictFinset A n (le_refl n)).card := by
    apply Finset.card_le_card
    intro a ha
    simp only [restrictFinset, Finset.mem_image]
    refine ⟨a, ha, ?_⟩
    funext i
    rw [Fin.castLE_refl]
  rw [hAcard]
  exact le_trans htop (hkey n (le_refl n))

end Commons.Data.Set