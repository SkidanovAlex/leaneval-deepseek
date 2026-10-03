import Mathlib
import Submission.Work.OROneRel.interval_defs
import Submission.Work.OROneRel.orbit_arith
import Submission.Work.OROneRel.residue_chain
import Submission.Work.OROneRel.ic_translated

namespace Work.OROneRel

/-!
## Connectivity of `±A, ±B`-intervals

We prove that on the integer interval `[lo,hi]` with `hi - lo ≥ A + B - 2`, the graph whose
edges join integers differing by `± A` or `± B` is connected (for `A, B ≥ 2` coprime).

The main steps are:

* `base_connected` : the minimal interval `[0, A+B-2]` is connected.  The residue classes
  modulo `A` are internally connected (`residue_chain`), so it suffices to connect the
  representatives `0, …, A-1`.  Each representative `r ≤ A-2` admits the step
  `r ↦ (r + B) % A` (up by `B`, then down by `A`'s), and the orbit `n ↦ (n*B) % A` of `0`
  is the whole cyclic group; `orbit_arith` supplies the required modular facts.
* `step_extend` : connectivity of `[lo,hi]` upgrades to `[lo,hi+1]` because `hi+1 ↦ hi+1-A`
  lands back in `[lo,hi]`.
* `ic_translated` : translation invariance, importing the `[0,M]` result to any interval.
-/

/-- A single upward step by `B`. -/
lemma S_add_B {lo hi A B x : ℤ} (hx : lo ≤ x) (h : x + B ≤ hi) (hB : 0 ≤ B) :
    S lo hi A B x (x + B) :=
  ⟨hx, by omega, by omega, h, Or.inr (Or.inr (Or.inl rfl))⟩

/-- A single downward step by `A`. -/
lemma S_sub_A {lo hi A B x : ℤ} (hx : x ≤ hi) (h : lo ≤ x - A) (hA : 0 ≤ A) :
    S lo hi A B x (x - A) :=
  ⟨by omega, hx, h, by omega, Or.inr (Or.inl rfl)⟩

/-- Monotonicity of `S` in the upper endpoint. -/
lemma S_mono_hi {lo hi hi' A B : ℤ} (h : hi ≤ hi') : S lo hi A B ≤ S lo hi' A B := by
  intro x y hab
  obtain ⟨h1, h2, h3, h4, h5⟩ := hab
  exact ⟨h1, by omega, h3, by omega, h5⟩

/-- Transport of reachability along a relation inclusion. -/
lemma rtg_mono {α : Type*} {r p : α → α → Prop} (h : r ≤ p) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact ih.tail (h _ _ hbc)

/-- The minimal interval `[0, A+B-2]` is connected. -/
lemma base_connected {A B : ℤ} (hA : 2 ≤ A) (hB : 2 ≤ B)
    (hbez : ∃ p q : ℤ, p * A + q * B = 1) :
    ∀ x y : ℤ, 0 ≤ x → x ≤ A + B - 2 → 0 ≤ y → y ≤ A + B - 2 →
      Relation.ReflTransGen (S 0 (A + B - 2) A B) x y := by
  obtain ⟨p, q, hpq⟩ := hbez
  obtain ⟨horb_range, horb_succ, horb_A, ⟨j0, hj0le, hj0val, hj0uniq⟩, horb_surj⟩ :=
    orbit_arith (A := A) (B := B) hA hpq
  have hA1 : (1 : ℤ) ≤ A := by omega
  have hB0 : (0 : ℤ) ≤ B := by omega
  -- a single step `orb n ↦ orb (n+1)` for `orb n ≠ A-1`
  have hstep : ∀ n : ℕ, orb A B n ≠ A - 1 →
      Relation.ReflTransGen (S 0 (A + B - 2) A B) (orb A B n) (orb A B (n + 1)) := by
    intro n hn
    have hrn := horb_range n
    have hle : orb A B n + B ≤ A + B - 2 := by
      have : orb A B n ≤ A - 2 := by omega
      omega
    have hs1 : S 0 (A + B - 2) A B (orb A B n) (orb A B n + B) :=
      S_add_B (by omega) hle hB0
    have hs2 := residue_chain (A := A) (B := B) hA1 (A + B - 2) (orb A B n + B)
      (by omega) hle
    have hs2' : Relation.ReflTransGen (S 0 (A + B - 2) A B) (orb A B n + B)
        (orb A B (n + 1)) := by
      rw [horb_succ n]; exact hs2
    exact (Relation.ReflTransGen.single hs1).trans hs2'
  have horb0 : orb A B 0 = 0 := by simp [orb]
  -- the chain `orb 0 → orb 1 → … → orb j0`
  have chain_le : ∀ n : ℕ, n ≤ j0 →
      Relation.ReflTransGen (S 0 (A + B - 2) A B) (orb A B 0) (orb A B n) := by
    intro n
    induction n with
    | zero => intro _; exact Relation.ReflTransGen.refl
    | succ n ih =>
      intro hn
      have hn' : n ≤ j0 := by omega
      have hnj : (n : ℤ) ≤ A - 1 := by
        have : (j0 : ℤ) ≤ A - 1 := hj0le
        omega
      have hne : orb A B n ≠ A - 1 := by
        intro hc
        have hnj0 : n = j0 := hj0uniq n hnj hc
        omega
      exact (ih hn').trans (hstep n hne)
  -- the chain `orb n → … → orb A.toNat` for `n > j0`
  have chain_gt : ∀ d : ℕ, ∀ n : ℕ, n + d = A.toNat → j0 < n →
      Relation.ReflTransGen (S 0 (A + B - 2) A B) (orb A B n) (orb A B A.toNat) := by
    intro d
    induction d with
    | zero =>
      intro n hn _
      have hna : n = A.toNat := by omega
      rw [hna]
    | succ d ih =>
      intro n hn hj
      have hnA : (n + 1) + d = A.toNat := by omega
      have hnlt : (n : ℤ) ≤ A - 1 := by
        have hnat : ((A.toNat : ℤ)) = A := Int.toNat_of_nonneg (by omega)
        have : (n : ℤ) < (A.toNat : ℤ) := by omega
        omega
      have hne : orb A B n ≠ A - 1 := by
        intro hc
        have hnj0 : n = j0 := hj0uniq n hnlt hc
        omega
      exact (hstep n hne).trans (ih (n + 1) hnA (by omega))
  -- every representative reached by `orb` reaches `0`
  have hreach : ∀ n : ℕ, (n : ℤ) ≤ A - 1 →
      Relation.ReflTransGen (S 0 (A + B - 2) A B) (orb A B n) 0 := by
    intro n hn
    by_cases hle : n ≤ j0
    · have h1 := chain_le n hle
      rw [horb0] at h1
      exact rtg_symm h1
    · push_neg at hle
      have hnA : n ≤ A.toNat := by
        have hnat : ((A.toNat : ℤ)) = A := Int.toNat_of_nonneg (by omega)
        have : (n : ℤ) < (A.toNat : ℤ) := by omega
        omega
      have h3 := chain_gt (A.toNat - n) n (Nat.add_sub_of_le hnA) hle
      rw [horb_A] at h3
      exact h3
  have hmain : ∀ x : ℤ, 0 ≤ x → x ≤ A + B - 2 →
      Relation.ReflTransGen (S 0 (A + B - 2) A B) x 0 := by
    intro x hx0 hxM
    have h1 := residue_chain (A := A) (B := B) hA1 (A + B - 2) x hx0 hxM
    have hxr0 : 0 ≤ x % A := Int.emod_nonneg x (by omega)
    have hxrA : x % A ≤ A - 1 := by
      have := Int.emod_lt_of_pos x (by omega : (0 : ℤ) < A)
      omega
    obtain ⟨n, hnle, hnval⟩ := horb_surj (x % A) hxr0 hxrA
    have h2 : Relation.ReflTransGen (S 0 (A + B - 2) A B) (x % A) 0 := by
      rw [← hnval]
      exact hreach n hnle
    exact h1.trans h2
  intro x y hx0 hxM hy0 hyM
  exact (hmain x hx0 hxM).trans (rtg_symm (hmain y hy0 hyM))

/-- Connectivity of `[lo,hi]` upgrades to `[lo,hi+1]`. -/
lemma step_extend {A B lo hi : ℤ} (hA : (1 : ℤ) ≤ A) (hloA : lo ≤ hi + 1 - A)
    (h : ∀ x y : ℤ, lo ≤ x → x ≤ hi → lo ≤ y → y ≤ hi →
      Relation.ReflTransGen (S lo hi A B) x y) :
    ∀ x y : ℤ, lo ≤ x → x ≤ hi + 1 → lo ≤ y → y ≤ hi + 1 →
      Relation.ReflTransGen (S lo (hi + 1) A B) x y := by
  have hmono : S lo hi A B ≤ S lo (hi + 1) A B := S_mono_hi (by omega)
  have key : ∀ z : ℤ, lo ≤ z → z ≤ hi + 1 →
      Relation.ReflTransGen (S lo (hi + 1) A B) z lo := by
    intro z hz hz'
    by_cases hzh : z ≤ hi
    · exact rtg_mono hmono
        (h z lo hz hzh (le_refl lo) (by omega))
    · push_neg at hzh
      have hz_eq : z = hi + 1 := by omega
      subst hz_eq
      have hst : S lo (hi + 1) A B (hi + 1) (hi + 1 - A) :=
        S_sub_A (by omega) (by omega) (by omega)
      have hrest : Relation.ReflTransGen (S lo hi A B) (hi + 1 - A) lo :=
        h (hi + 1 - A) lo (by omega) (by omega) (le_refl lo) (by omega)
      exact (Relation.ReflTransGen.single hst).trans (rtg_mono hmono hrest)
  intro x y hx hx' hy hy'
  exact (key x hx hx').trans (rtg_symm (key y hy hy'))

theorem interval_connected {A B : ℤ} (hA : 2 ≤ A) (hB : 2 ≤ B)
    (hbez : ∃ p q : ℤ, p * A + q * B = 1)
    (lo hi : ℤ) (hband : A + B - 2 ≤ hi - lo) :
    ∀ x y : ℤ, lo ≤ x → x ≤ hi → lo ≤ y → y ≤ hi →
      Relation.ReflTransGen (fun x y : ℤ => lo ≤ y ∧ y ≤ hi ∧
        (y = x + A ∨ y = x - A ∨ y = x + B ∨ y = x - B)) x y := by
  have hbase := base_connected hA hB hbez
  have htrans := ic_translated (A := A) (B := B) (M := A + B - 2) hbase lo
  have hA1 : (1 : ℤ) ≤ A := by omega
  -- upgrade the minimal interval to `[lo, hi]`
  have ext : ∀ k : ℕ, ∀ hi : ℤ, hi = lo + (A + B - 2) + (k : ℤ) →
      ∀ x y : ℤ, lo ≤ x → x ≤ hi → lo ≤ y → y ≤ hi →
        Relation.ReflTransGen (S lo hi A B) x y := by
    intro k
    induction k with
    | zero =>
      intro hi hhi x y hx hx' hy hy'
      have hhi' : hi = lo + (A + B - 2) := by omega
      subst hhi'
      exact htrans x y hx hx' hy hy'
    | succ k ih =>
      intro hi hhi x y hx hx' hy hy'
      set hi' : ℤ := lo + (A + B - 2) + (k : ℤ) with hhi'
      have hhi_eq : hi = hi' + 1 := by omega
      subst hhi_eq
      have hih := ih hi' hhi'
      have hlog : lo ≤ hi' + 1 - A := by omega
      have hstep := step_extend (A := A) (B := B) (lo := lo) (hi := hi') hA1 hlog hih
      exact hstep x y hx hx' hy hy'
  intro x y hx hx' hy hy'
  have hk : 0 ≤ hi - (lo + (A + B - 2)) := by linarith
  have hhieq : hi = lo + (A + B - 2) + ((hi - (lo + (A + B - 2))).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hk]; ring
  have hres := ext ((hi - (lo + (A + B - 2))).toNat) hi hhieq x y hx hx' hy hy'
  show Relation.ReflTransGen (IRel lo hi A B) x y
  exact rtg_mono S_le_IRel hres

end Work.OROneRel
