import Mathlib

open Finsupp
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.Combinatorics.MvPolynomial

namespace SymmetricExchange

noncomputable section

abbrev e {σ : Type*} (i : σ) : σ →₀ ℕ := Finsupp.single i 1

/-! ## Basic coordinate arithmetic for the unit-vector moves -/

lemma sub_add_at_i {σ : Type*} (x : σ →₀ ℕ) (i j : σ) (hij : i ≠ j) :
    (x - e i + e j) i = x i - 1 := by
  simp [e, hij]

lemma sub_add_at_j {σ : Type*} (x : σ →₀ ℕ) (i j : σ) (hij : i ≠ j) :
    (x - e i + e j) j = x j + 1 := by
  simp [e, hij]

lemma sub_add_at_other {σ : Type*} (x : σ →₀ ℕ) (i j k : σ) (hki : k ≠ i) (hkj : k ≠ j) :
    (x - e i + e j) k = x k := by
  simp [e, hki, hkj]

lemma add_sub_at_i {σ : Type*} (x : σ →₀ ℕ) (i j : σ) (hij : i ≠ j) :
    (x + e i - e j) i = x i + 1 := by
  simp [e, hij]

lemma add_sub_at_j {σ : Type*} (x : σ →₀ ℕ) (i j : σ) (hij : i ≠ j) :
    (x + e i - e j) j = x j - 1 := by
  simp [e, hij]

lemma add_sub_at_other {σ : Type*} (x : σ →₀ ℕ) (i j k : σ) (hki : k ≠ i) (hkj : k ≠ j) :
    (x + e i - e j) k = x k := by
  simp [e, hki, hkj]

/-- If `x i ≥ 1` then `x - e i + e i = x` -/
lemma sub_single_add_self {σ : Type*} (x : σ →₀ ℕ) (i : σ) (hi : x i ≠ 0) :
    (x - e i) + e i = x := by
  classical
  ext k
  by_cases hk : k = i
  · subst k
    simp [e]
    omega
  · simp [e, hk]

lemma add_single_sub_self {σ : Type*} (x : σ →₀ ℕ) (i : σ) : (x + e i) - e i = x := by
  classical
  ext k
  by_cases hk : k = i
  · subst k
    simp [e]
  · simp [e, hk]

/-! ## Sums and the total-degree bound -/

/-- coordinate is bounded by the total sum (nonnegative coefficients) -/
lemma coord_le_sum {σ : Type*} [Fintype σ] (m : σ →₀ ℕ) (i : σ) :
    m i ≤ ∑ k : σ, m k := by
  classical
  have hu : i ∈ (Finset.univ : Finset σ) := Finset.mem_univ i
  have hsplit : (∑ k : σ, m k) = (∑ k ∈ (Finset.univ : Finset σ).erase i, m k) + m i := by
    exact (Finset.sum_erase_add (Finset.univ : Finset σ) (fun k : σ => m k) hu).symm
  rw [hsplit]
  omega

/-- elements of total degree `d` have each coordinate `≤ d` -/
lemma coord_le_of_sum {n : ℕ} {d : ℕ} {α : Fin n →₀ ℕ}
    (hα : (∑ k : Fin n, α k) = d) (k : Fin n) : α k ≤ d := by
  rw [← hα]
  exact coord_le_sum α k

/-- `e i` has total degree one -/
lemma sum_single {σ : Type*} [Fintype σ] (i : σ) : (∑ k : σ, (e k : σ →₀ ℕ) i) = 1 := by
  classical
  rw [Finset.sum_eq_single i]
  · simp [e]
  · intro b hb hbi
    simp [e, hbi]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-! ## The `L¹`-distance measure and its decrease under exchanges -/

/-- `L¹`-like distance between two exponent vectors -/
def mu {n : ℕ} (x y : Fin n →₀ ℕ) : ℕ :=
  ∑ k : Fin n, ((x k - y k) + (y k - x k))

lemma mu_coord_term {n : ℕ} (x y : Fin n →₀ ℕ) (k : Fin n) :
    ((x k - y k) + (y k - x k)) ≤ mu x y := by
  unfold mu
  exact Finset.single_le_sum (f := fun a : Fin n => (x a - y a) + (y a - x a))
    (s := Finset.univ) (by intro b hb; exact Nat.zero_le _) (Finset.mem_univ k)

lemma mu_zero_iff_eq {n : ℕ} (x y : Fin n →₀ ℕ) : mu x y = 0 ↔ x = y := by
  constructor
  · intro h
    ext k
    have hk : (x k - y k) + (y k - x k) = 0 := by
      have hle : (x k - y k) + (y k - x k) ≤ mu x y := mu_coord_term x y k
      omega
    have hxy : x k ≤ y k := by
      have := Nat.le_of_sub_eq_zero (by omega : x k - y k = 0)
      exact this
    have hyx : y k ≤ x k := by
      have h2 : (y k - x k) = 0 := by
        -- from hk: (x k - y k) + (y k - x k) = 0 and x k - y k = 0 (shown); then y k - x k = 0
        have hsub : (y k - x k) ≤ (x k - y k) + (y k - x k) := by omega
        omega
      exact Nat.le_of_sub_eq_zero h2
    omega
  · intro h
    subst y
    unfold mu
    simp

/-- the L1-distance measure is symmetric -/
lemma mu_symm {n : ℕ} (x y : Fin n →₀ ℕ) : mu x y = mu y x := by
  unfold mu
  apply Finset.sum_congr rfl
  intro k hk
  omega

lemma sum_two_erase {σ : Type*} [Fintype σ] [DecidableEq σ] (f : σ → ℕ) (u v : σ)
    (huv : u ≠ v) :
    (∑ k : σ, f k) =
      (∑ k ∈ ((Finset.univ : Finset σ).erase u).erase v, f k) + f u + f v := by
  have hu : u ∈ (Finset.univ : Finset σ) := Finset.mem_univ u
  have hv' : v ∈ (Finset.univ : Finset σ).erase u := by
    rw [Finset.mem_erase]
    exact ⟨Ne.symm huv, Finset.mem_univ v⟩
  have h1 : (∑ k : σ, f k) = (∑ k ∈ (Finset.univ : Finset σ).erase u, f k) + f u :=
    (Finset.sum_erase_add (Finset.univ : Finset σ) (fun k => f k) hu).symm
  have h2 : (∑ k ∈ (Finset.univ : Finset σ).erase u, f k) =
      (∑ k ∈ ((Finset.univ : Finset σ).erase u).erase v, f k) + f v :=
    (Finset.sum_erase_add ((Finset.univ : Finset σ).erase u) (fun k => f k) hv').symm
  rw [h1, h2]
  ring

/-- moving `x` one unit from `u` to `v` (towards `y`) lowers the distance by two -/
lemma mu_sub_add_decrease {n : ℕ} (x y : Fin n →₀ ℕ) (u v : Fin n)
    (hxyu : y u < x u) (hxyv : x v < y v) (huv : u ≠ v) :
    mu (x - e u + e v) y + 2 = mu x y := by
  classical
  let f (z : Fin n →₀ ℕ) (k : Fin n) : ℕ := (z k - y k) + (y k - z k)
  have hdecomp (z : Fin n →₀ ℕ) :
      (∑ k : Fin n, f z k) = (∑ k ∈ (((Finset.univ : Finset (Fin n)).erase u).erase v), f z k) + f z u + f z v :=
    sum_two_erase (f := fun k : Fin n => f z k) u v huv
  unfold mu
  rw [hdecomp x, hdecomp (x - e u + e v)]
  -- term at u decreases by one, at v decreases by one, elsewhere equal
  have hu_term : f x u = f (x - e u + e v) u + 1 := by
    have hcoor : (x - e u + e v) u = x u - 1 := sub_add_at_i x u v huv
    unfold f
    rw [hcoor]
    omega
  have hv_term : f x v = f (x - e u + e v) v + 1 := by
    have hcoor : (x - e u + e v) v = x v + 1 := sub_add_at_j x u v huv
    unfold f
    rw [hcoor]
    omega
  have ho_term : ∀ k : Fin n, k ≠ u → k ≠ v → f x k = f (x - e u + e v) k := by
    intro k hku hkv
    have hcoor : (x - e u + e v) k = x k := sub_add_at_other x u v k hku hkv
    unfold f
    rw [hcoor]
  -- rewrite the sums over the erased set (all remaining coordinates are `u`- and `v`-free)
  have hsum : (∑ k ∈ (((Finset.univ : Finset (Fin n)).erase u).erase v), f (x - e u + e v) k) =
      (∑ k ∈ (((Finset.univ : Finset (Fin n)).erase u).erase v), f x k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact (ho_term k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      (Finset.mem_erase.mp hk).1).symm
  rw [hu_term, hv_term, hsum]
  ring

/-- moving `y` one unit from `v` to `u` (towards `x`) lowers the distance by two -/
lemma mu_add_sub_decrease {n : ℕ} (x y : Fin n →₀ ℕ) (u v : Fin n)
    (hxyu : y u < x u) (hxyv : x v < y v) (huv : u ≠ v) :
    mu x (y - e v + e u) + 2 = mu x y := by
  -- mu is symmetric and the previous lemma applies with roles swapped
  have hmain := mu_sub_add_decrease y x v u hxyv hxyu (Ne.symm huv)
  -- mu_sub_add_decrease y x v u gives mu (y - e v + e u) x + 2 = mu y x
  rw [mu_symm x (y - e v + e u), mu_symm x y]
  exact hmain

/-! ## sums of pointwise differences and the auxiliary index -/

/-- `∑ (b-a) = ∑ b - ∑ a` when `a ≤ b` pointwise -/
lemma sum_sub_of_le {σ : Type*} [Fintype σ] (a b : σ → ℕ) (h : ∀ k : σ, a k ≤ b k) :
    (∑ k : σ, (b k - a k)) = (∑ k : σ, b k) - (∑ k : σ, a k) := by
  have hle : (∑ k : σ, a k) ≤ (∑ k : σ, b k) := by
    exact Finset.sum_le_sum (by intro k hk; exact h k)
  have h1 : (∑ k : σ, a k) + (∑ k : σ, (b k - a k)) = ∑ k : σ, b k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact Nat.add_sub_of_le (h k)
  omega

/-- if a sum of natural numbers equals one, exactly one summand is one -/
lemma sum_eq_one_unique {σ : Type*} [Fintype σ] [DecidableEq σ] (f : σ → ℕ)
    (h : (∑ k : σ, f k) = 1) : ∃ v : σ, f v = 1 ∧ ∀ w : σ, w ≠ v → f w = 0 := by
  classical
  have hne : (∑ k : σ, f k) ≠ 0 := by omega
  have ⟨v, hfv⟩ : ∃ v : σ, f v ≠ 0 := by
    by_contra hno
    push_neg at hno
    have hsum0 : (∑ k : σ, f k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact hno k
    omega
  refine ⟨v, ?_, ?_⟩
  · have hfv1 : f v ≥ 1 := by omega
    have hle : f v ≤ (∑ k : σ, f k) := by
      exact Finset.single_le_sum (f := f) (s := Finset.univ) (by intro b hb; exact Nat.zero_le _) (Finset.mem_univ v)
    omega
  · intro w hwv
    by_contra hw0
    have hw1 : f w ≥ 1 := by omega
    have hsplit : (∑ k : σ, f k) = (∑ k ∈ (Finset.univ.erase v).erase w, f k) + f v + f w := by
      exact sum_two_erase f v w (Ne.symm hwv)
    rw [hsplit] at h
    omega

/-- if `x = y + eᵤ* - eᵥ` (the degenerate shape), the exchange is two-sided with `v` -/
lemma degenerate_witness {n d : ℕ} {A : Set (Fin n →₀ ℕ)}
    (hdeg : ∀ α ∈ A, (∑ k : Fin n, α k) = d)
    {x y : Fin n →₀ ℕ} (hx : x ∈ A) (hy : y ∈ A) (us : Fin n)
    (hu : y us < x us) (hxuy : x us = y us + 1)
    (hno : ∀ u0 : Fin n, u0 ≠ us → y u0 < x u0 → False) :
    ∃ v : Fin n, x v < y v ∧ x - e us + e v = y := by
  classical
  have hle : ∀ k : Fin n, x k ≤ y k + (if k = us then 1 else 0) := by
    intro k
    by_cases hk : k = us
    · subst k
      simp [hxuy]
    · by_cases hxy : x k ≤ y k
      · simp [hk]
        omega
      · have hlt : y k < x k := Nat.lt_of_not_ge hxy
        exact False.elim (hno k hk hlt)
  let g : Fin n → ℕ := fun k => (y k + (if k = us then 1 else 0)) - x k
  have hgsum : (∑ k : Fin n, g k) = 1 := by
    unfold g
    rw [sum_sub_of_le (fun k => x k) (fun k => y k + (if k = us then 1 else 0)) hle]
    have hsumx : (∑ k : Fin n, x k) = d := hdeg x hx
    have hsumy : (∑ k : Fin n, (y k + (if k = us then 1 else 0))) = d + 1 := by
      have hy1 : (∑ k : Fin n, y k) = d := hdeg y hy
      calc
        (∑ k : Fin n, (y k + (if k = us then 1 else 0))) =
            (∑ k : Fin n, y k) + (∑ k : Fin n, (if k = us then 1 else 0)) := by
          rw [Finset.sum_add_distrib]
        _ = d + (∑ k : Fin n, (if k = us then 1 else 0)) := by rw [hy1]
        _ = d + 1 := by
          congr 1
          rw [Finset.sum_eq_single us]
          · simp
          · intro b hb hbus
            simp [hbus]
          · intro hmem
            exact False.elim (hmem (Finset.mem_univ us))
    omega
  have ⟨v, hgv, hgother⟩ := sum_eq_one_unique g hgsum
  have hvus : v ≠ us := by
    intro hv
    subst v
    have hgvus : (y us + 1) - x us = 1 := by simpa [g] using hgv
    rw [hxuy] at hgvus
    omega
  have hgv2 : (y v + 0) - x v = 1 := by simpa [g, hvus] using hgv
  have hxyv : x v < y v := by omega
  refine ⟨v, hxyv, ?_⟩
  ext k
  by_cases hkv : k = v
  · subst k
    simp [e, hvus]
    have : y v - x v = 1 := hgv2
    omega
  · by_cases hkus : k = us
    · subst k
      simp [e, hvus]
      omega
    · simp [e, hkv, hkus]
      have hgk : (y k) - x k = 0 := by
        simpa [g, hkus] using hgother k hkv
      have hxy : x k ≤ y k := by
        have := hle k
        simpa [hkus] using this
      omega

/-- the index `u0` of the Murota descent exists -/
lemma exists_u0 {n d : ℕ} {A : Set (Fin n →₀ ℕ)}
    (hdeg : ∀ α ∈ A, (∑ k : Fin n, α k) = d)
    {x y : Fin n →₀ ℕ} (hx : x ∈ A) (hy : y ∈ A) (us : Fin n)
    (hu : y us < x us)
    (hfail : ∀ v : Fin n, x v < y v → ¬ (x - e us + e v ∈ A ∧ y - e v + e us ∈ A)) :
    ∃ u0 : Fin n, y u0 < x u0 ∧ (u0 ≠ us ∨ y us + 2 ≤ x us) := by
  classical
  by_cases hslack : y us + 2 ≤ x us
  · exact ⟨us, hu, Or.inr hslack⟩
  · have hxuy : x us = y us + 1 := by omega
    by_cases hother : ∃ u0 : Fin n, u0 ≠ us ∧ y u0 < x u0
    · rcases hother with ⟨u0, h0, hgt⟩
      exact ⟨u0, hgt, Or.inl h0⟩
    · have hno : ∀ u0 : Fin n, u0 ≠ us → y u0 < x u0 → False := by
        intro u0 h0 hlt
        exact hother ⟨u0, h0, hlt⟩
      rcases degenerate_witness (A := A) hdeg hx hy us hu hxuy hno with ⟨v, hv, heq⟩
      have hmem1 : x - e us + e v ∈ A := by simpa [heq] using hy
      have hmem2 : y - e v + e us ∈ A := by
        have hsub : x us ≠ 0 := by omega
        have : y - e v + e us = x := by
          calc
            y - e v + e us = (x - e us + e v) - e v + e us := by rw [heq]
            _ = (x - e us) + e us := by
              congr 1
              exact add_single_sub_self (x - e us) v
            _ = x := by
              exact sub_single_add_self x us hsub
        simpa [this] using hx
      exact False.elim (hfail v hv ⟨hmem1, hmem2⟩)


/-! ## vector algebra for the exchange moves -/

/-- `(a + e i) - e j = (a - e j) + e i` for `i ≠ j` (valid over `ℕ`) -/
lemma add_sub_swap {σ : Type*} (a : σ →₀ ℕ) (i j : σ) (hij : i ≠ j) :
    (a + e i) - e j = (a - e j) + e i := by
  ext k
  by_cases hk : k = j
  · subst j
    simp [e, hij]
  · by_cases hki : k = i
    · subst i
      simp [e, hk]
    · simp [e, hk, hki]

/-- double subtraction commutes -/
lemma sub_sub_comm {σ : Type*} (m : σ →₀ ℕ) (a b : σ) :
    (m - e a) - e b = (m - e b) - e a := by
  ext k
  by_cases hka : k = a
  · subst a
    by_cases hkb : k = b
    · subst b
      simp [e]
    · simp [e, hkb]
  · by_cases hkb : k = b
    · subst b
      simp [e, hka]
    · simp [e, hka, hkb]

/-- rearrangement used in Murota's second exchange case, `w = u0` -/
lemma eq1 {σ : Type*} (y : σ →₀ ℕ) (us u0 v0 v : σ)
    (hvu0 : v ≠ u0) (hvv0 : v ≠ v0) (hvus : v ≠ us)
    (hv0u0 : v0 ≠ u0) (hv0us : v0 ≠ us) (hv0v : v0 ≠ v)
    (hyv : y v ≠ 0) (hyv0 : y v0 ≠ 0) :
    (((y - e v0 + e u0) - e v + e us) - e u0) + e v0 = y - e v + e us := by
  let t : σ →₀ ℕ := (y - e v) - e v0
  have hsub : (y - e v0) - e v = t := by
    unfold t
    exact sub_sub_comm y v0 v
  have h1 : ((y - e v0 + e u0) - e v) = t + e u0 := by
    calc
      (y - e v0 + e u0) - e v = ((y - e v0) + e u0) - e v := by ac_rfl
      _ = ((y - e v0) - e v) + e u0 := add_sub_swap (y - e v0) u0 v (Ne.symm hvu0)
      _ = t + e u0 := by rw [hsub]
  have h2 : (((y - e v0 + e u0) - e v) + e us) - e u0 = t + e us := by
    calc
      (((y - e v0 + e u0) - e v) + e us) - e u0 = ((t + e u0) + e us) - e u0 := by rw [h1]
      _ = ((t + e us) + e u0) - e u0 := by
        congr 1
        ac_rfl
      _ = t + e us := add_single_sub_self (t + e us) u0
  have h3 : ((t + e us) + e v0) = y - e v + e us := by
    have hswap : (t + e us) = ((y - e v) + e us) - e v0 := by
      unfold t
      exact (add_sub_swap (y - e v) us v0 (Ne.symm hv0us)).symm
    calc
      (t + e us) + e v0 = (((y - e v) + e us) - e v0) + e v0 := by rw [hswap]
      _ = (y - e v) + e us := by
        exact sub_single_add_self ((y - e v) + e us) v0 (by
          have : ((y - e v) + e us) v0 = y v0 := by simp [e, hv0v, hv0us]
          rw [this]
          exact hyv0)
  calc
    (((y - e v0 + e u0) - e v + e us) - e u0) + e v0
        = ((((y - e v0 + e u0) - e v) + e us) - e u0) + e v0 := by rfl
    _ = (t + e us) + e v0 := by rw [h2]
    _ = y - e v + e us := h3

/-- rearrangement used in Murota's second exchange case, `w = us` -/
lemma eq2 {σ : Type*} (y : σ →₀ ℕ) (us u0 v0 v : σ)
    (hvu0 : v ≠ u0) (hvv0 : v ≠ v0) (hvus : v ≠ us)
    (hv0u0 : v0 ≠ u0) (hv0us : v0 ≠ us) (hv0v : v0 ≠ v)
    (hyv : y v ≠ 0) (hyv0 : y v0 ≠ 0) :
    (((y - e v0 + e u0) - e v + e us) - e us) + e v0 = y - e v + e u0 := by
  let t : σ →₀ ℕ := (y - e v) - e v0
  have hsub : (y - e v0) - e v = t := by
    unfold t
    exact sub_sub_comm y v0 v
  have h1 : ((y - e v0 + e u0) - e v) = t + e u0 := by
    calc
      (y - e v0 + e u0) - e v = ((y - e v0) + e u0) - e v := by ac_rfl
      _ = ((y - e v0) - e v) + e u0 := add_sub_swap (y - e v0) u0 v (Ne.symm hvu0)
      _ = t + e u0 := by rw [hsub]
  have h2 : (((y - e v0 + e u0) - e v) + e us) - e us = t + e u0 := by
    calc
      (((y - e v0 + e u0) - e v) + e us) - e us = ((y - e v0 + e u0) - e v) :=
        add_single_sub_self ((y - e v0 + e u0) - e v) us
      _ = t + e u0 := h1
  have h3 : ((t + e u0) + e v0) = y - e v + e u0 := by
    calc
      (t + e u0) + e v0 = ((y - e v) - e v0) + e u0 + e v0 := by
        unfold t
        ac_rfl
      _ = ((y - e v) - e v0) + e v0 + e u0 := by
        ac_rfl
      _ = (y - e v) + e u0 := by
        congr 1
        exact sub_single_add_self (y - e v) v0 (by
          have : (y - e v) v0 = y v0 := by simp [e, hv0v]
          rw [this]
          exact hyv0)
  calc
    (((y - e v0 + e u0) - e v + e us) - e us) + e v0
        = ((((y - e v0 + e u0) - e v) + e us) - e us) + e v0 := by rfl
    _ = (t + e u0) + e v0 := by rw [h2]
    _ = y - e v + e u0 := h3



/-- the y-side ("target-side") one-sided exchange axiom implies the symmetric
  exchange property for constant-degree families -/
theorem coreE2 {n d : ℕ} (A : Set (Fin n →₀ ℕ))
    (hdeg : ∀ α ∈ A, (∑ k : Fin n, α k) = d)
    (hE2 : ∀ x ∈ A, ∀ y ∈ A, ∀ i : Fin n, x i > y i →
      ∃ j : Fin n, x j < y j ∧ y - e j + e i ∈ A) :
    ∀ x ∈ A, ∀ y ∈ A, ∀ u : Fin n, x u > y u →
      ∃ v : Fin n, x v < y v ∧ x - e u + e v ∈ A ∧ y - e v + e u ∈ A := by
  classical
  let P (k : ℕ) : Prop :=
    ∀ x y : Fin n →₀ ℕ, x ∈ A → y ∈ A → mu x y = k →
      ∀ u : Fin n, x u > y u →
        ∃ v : Fin n, x v < y v ∧ x - e u + e v ∈ A ∧ y - e v + e u ∈ A
  have hP : ∀ k : ℕ, P k := by
    intro k
    induction' k using Nat.strong_induction_on with k ih
    intro x y hx hy hk us hus
    by_cases hgood : ∃ v : Fin n, x v < y v ∧ x - e us + e v ∈ A ∧ y - e v + e us ∈ A
    · exact hgood
    · have hfail : ∀ v : Fin n, x v < y v → ¬ (x - e us + e v ∈ A ∧ y - e v + e us ∈ A) := by
        intro v hv hboth
        exact hgood ⟨v, hv, hboth⟩
      rcases exists_u0 (A := A) hdeg hx hy us hus hfail with ⟨u0, hu0gt, hu0s⟩
      -- hu0gt : y u0 < x u0 ;  hu0s : u0 ≠ us ∨ y us + 2 ≤ x us
      rcases hE2 x hx y hy u0 hu0gt with ⟨v0i, hv0lt_i, hyv0A_i⟩
      -- hv0lt_i : x v0i < y v0i ;  hyv0A_i : y - e v0i + e u0 ∈ A
      let X (v : Fin n) : Prop := x v < y v ∧ x - e us + e v ∈ A
      let Y (v : Fin n) : Prop := x v < y v ∧ y - e v + e u0 ∈ A
      have hYne : ∃ v0 : Fin n, Y v0 := ⟨v0i, hv0lt_i, hyv0A_i⟩
      have hmain0 : ∃ v0 : Fin n, Y v0 ∧ (X v0 → ∃ v0' : Fin n, X v0' ∧ Y v0') ∧
          ((∃ v0' : Fin n, X v0' ∧ Y v0') → X v0) := by
        by_cases hXY : ∃ v0 : Fin n, X v0 ∧ Y v0
        · refine ⟨Classical.choose hXY, ?_, ?_, ?_⟩
          · exact (Classical.choose_spec hXY).2
          · intro _; exact hXY
          · intro _; exact (Classical.choose_spec hXY).1
        · refine ⟨Classical.choose hYne, ?_, ?_, ?_⟩
          · exact Classical.choose_spec hYne
          · intro hxX
            exact False.elim (hXY ⟨Classical.choose hYne, hxX, (Classical.choose_spec hYne)⟩)
          · intro h; exact False.elim (hXY h)
      rcases hmain0 with ⟨v0, hv0Y, hv0X_imp, hXYimp⟩
      have hv0lt : x v0 < y v0 := hv0Y.1
      have hyv0A : y - e v0 + e u0 ∈ A := hv0Y.2
      have hv0ne_u0 : v0 ≠ u0 := by
        intro h
        have hxu0 : x u0 < y u0 := by simpa [h] using hv0lt
        omega
      have hv0ne_us : v0 ≠ us := by
        intro h
        have hxv0 : x us < y us := by simpa [h] using hv0lt
        omega
      have hyv0 : y v0 ≠ 0 := by
        have : 0 < y v0 := by omega
        exact Nat.ne_of_gt this
      let yp : Fin n →₀ ℕ := y - e v0 + e u0
      have hyyp : yp ∈ A := by simpa [yp] using hyv0A
      have hmuyp : mu x yp = k - 2 := by
        have hm : mu x yp + 2 = mu x y := by
          simpa [yp] using (mu_add_sub_decrease x y u0 v0 hu0gt hv0lt (Ne.symm hv0ne_u0))
        omega
      have hmu_yp_k : mu x yp + 2 = k := by
        rw [← hk]
        simpa [yp] using (mu_add_sub_decrease x y u0 v0 hu0gt hv0lt (Ne.symm hv0ne_u0))
      have hkge : 2 ≤ k := by omega
      have hklt : k - 2 < k := by omega
      have hypus_eq (h : u0 = us) : yp us = y us + 1 := by
        subst us
        simp [yp, e, hv0ne_u0]
      have hypus_ne (h : u0 ≠ us) : yp us = y us := by
        simp [yp, e, hv0ne_us, h]
      have hus_yp : yp us < x us := by
        by_cases hu0us : u0 = us
        · have hslack : y us + 2 ≤ x us := by
            rcases hu0s with h1 | h2
            · exact False.elim (h1 hu0us)
            · exact h2
          have : yp us = y us + 1 := hypus_eq hu0us
          omega
        · have : yp us = y us := hypus_ne hu0us
          omega
      -- claim: (x, yp, us) admits no symmetric witness either
      have hnoWit_yp : ∀ v : Fin n, x v < yp v →
          ¬ (x - e us + e v ∈ A ∧ yp - e v + e us ∈ A) := by
        intro v hvxy hboth
        rcases hboth with ⟨hmemx, hmemypv⟩
        have hvne_u0 : v ≠ u0 := by
          intro h
          have hyy : yp u0 = y u0 + 1 := by
            simp [yp, e, hv0ne_u0]
          have hxu0 : x u0 < y u0 + 1 := by simpa [h, hyy] using hvxy
          omega
        have hvlt : x v < y v := by
          by_cases hvv0 : v = v0
          · have hyy : yp v0 = y v0 - 1 := by
              simp [yp, e, hv0ne_u0]
            have hxv0 : x v0 < y v0 - 1 := by simpa [hvv0, hyy] using hvxy
            rw [hvv0]
            exact lt_of_lt_of_le hxv0 (Nat.sub_le (y v0) 1)
          · have hyy : yp v = y v := by
              simp [yp, e, hvne_u0, hvv0]
            simpa [hyy] using hvxy
        have hvus_ne : v ≠ us := by
          intro h
          have hbad : x us < yp us := by simpa [h] using hvxy
          omega
        have hyv : y v ≠ 0 := by
          have : 0 < y v := by omega
          exact Nat.ne_of_gt this
        have hvX : X v := ⟨hvlt, hmemx⟩
        have hybad_us : ¬ (y - e v + e us ∈ A) := by
          intro hm
          exact hfail v hvlt ⟨hmemx, hm⟩
        let ypp : Fin n →₀ ℕ := yp - e v + e us
        have hyppA : ypp ∈ A := by simpa [ypp] using hmemypv
        by_cases hv0X : X v0
        · -- Case A: v0 is x-good at us
          have hybad_v0 : ¬ (y - e v0 + e us ∈ A) := by
            intro hm
            exact hfail v0 hv0lt ⟨hv0X.2, hm⟩
          have hyppus_gt : y us < ypp us := by
            have hyle_yp : y us ≤ yp us := by
              by_cases hu0us : u0 = us
              · have : yp us = y us + 1 := hypus_eq hu0us
                omega
              · have : yp us = y us := hypus_ne hu0us
                omega
            have hypp_ge : yp us + 1 ≤ ypp us := by
              simp [ypp, e, hvus_ne]
            omega
          rcases hE2 ypp hyppA y hy us hyppus_gt with ⟨w, hwlt_ypp, hmemw⟩
          have hw_cases : w = v0 ∨ w = v := by
            by_cases hwv0 : w = v0
            · exact Or.inl hwv0
            · by_cases hwv : w = v
              · exact Or.inr hwv
              · exfalso
                have hy_le_ypp : y w ≤ ypp w := by
                  by_cases hwu0 : w = u0
                  · subst w
                    by_cases hwusu0 : us = u0
                    · subst us
                      have hval : ypp u0 = y u0 + 2 := by
                        simp [ypp, yp, e, hvne_u0, hv0ne_u0]
                      omega
                    · have hval : ypp u0 = y u0 + 1 := by
                        simp [ypp, yp, e, hvne_u0, hv0ne_u0, hwusu0]
                      omega
                  · by_cases hwus : w = us
                    · subst w
                      have hyle : y us ≤ yp us := by
                        by_cases hu0us : u0 = us
                        · have : yp us = y us + 1 := hypus_eq hu0us
                          omega
                        · have : yp us = y us := hypus_ne hu0us
                          omega
                      have hval : ypp us = yp us + 1 := by
                        simp [ypp, e, hvus_ne]
                      omega
                    · have hval : ypp w = y w := by
                        simp [ypp, yp, e, hvne_u0, hvus_ne, hwu0, hwus, hwv0, hwv]
                      omega
                omega
          rcases hw_cases with hwv0 | hwv
          · rw [hwv0] at hmemw
            exact hybad_v0 hmemw
          · rw [hwv] at hmemw
            exact hybad_us hmemw
        · -- Case B: v0 is not x-good at us
          have hvne_v0 : v ≠ v0 := by
            intro h
            subst v
            exact hv0X hvX
          have hXYempty : ¬ ∃ v0' : Fin n, X v0' ∧ Y v0' := by
            intro h
            exact hv0X (hXYimp h)
          have hybad_u0 : ¬ (y - e v + e u0 ∈ A) := by
            intro hm
            exact hXYempty ⟨v, hvX, ⟨hvlt, hm⟩⟩
          have hppv0 : ypp v0 < y v0 := by
            have hval : ypp v0 = y v0 - 1 := by
              simp [ypp, yp, e, hvne_v0, hv0ne_u0, hv0ne_us]
            omega
          rcases hE2 y hy ypp hyppA v0 hppv0 with ⟨w, hwgt_ypp, hmemw⟩
          have hw_cases : w = u0 ∨ w = us := by
            by_cases hwu0 : w = u0
            · exact Or.inl hwu0
            · by_cases hwus : w = us
              · exact Or.inr hwus
              · exfalso
                have hypp_le_y : ypp w ≤ y w := by
                  by_cases hwv0 : w = v0
                  · subst w
                    have hval : ypp v0 = y v0 - 1 := by
                      simp [ypp, yp, e, hvne_v0, hv0ne_u0, hv0ne_us]
                    omega
                  · by_cases hwv : w = v
                    · subst w
                      have hval : ypp v = y v - 1 := by
                        simp [ypp, yp, e, hvne_u0, hvus_ne, hwv0]
                      omega
                    · have hval : ypp w = y w := by
                        simp [ypp, yp, e, hvne_u0, hvus_ne, hwu0, hwus, hwv0, hwv]
                      omega
                omega
          rcases hw_cases with hwu0w | hwusw
          · have heq1 : ypp - e u0 + e v0 = y - e v + e us := by
              simpa [ypp, yp] using
                (eq1 y us u0 v0 v hvne_u0 hvne_v0 hvus_ne hv0ne_u0 hv0ne_us
                  (Ne.symm hvne_v0) hyv hyv0)
            have hm1 : y - e v + e us ∈ A := by
              simpa [hwu0w, heq1] using hmemw
            exact hybad_us hm1
          · have heq2 : ypp - e us + e v0 = y - e v + e u0 := by
              simpa [ypp, yp] using
                (eq2 y us u0 v0 v hvne_u0 hvne_v0 hvus_ne hv0ne_u0 hv0ne_us
                  (Ne.symm hvne_v0) hyv hyv0)
            have hm2 : y - e v + e u0 ∈ A := by
              simpa [hwusw, heq2] using hmemw
            exact hybad_u0 hm2
      -- contradiction with the induction hypothesis on the closer pair (x, yp)
      have hwit := ih (k - 2) hklt x yp hx hyyp hmuyp us hus_yp
      rcases hwit with ⟨v, hv1, hb1, hb2⟩
      exact False.elim (hnoWit_yp v hv1 ⟨hb1, hb2⟩)
  intro x hx y hy u hu
  exact hP (mu x y) x y hx hy rfl u hu

end
end SymmetricExchange

namespace CompExch

noncomputable section

abbrev e {σ : Type*} (i : σ) : σ →₀ ℕ := Finsupp.single i 1

def cw {n : ℕ} (w : ℕ) (b : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  (Finsupp.equivFunOnFinite (α := Fin n) (M := ℕ)).symm (fun k => w - b k)

lemma cw_apply {n : ℕ} (w : ℕ) (b : Fin n →₀ ℕ) (k : Fin n) : cw w b k = w - b k := by
  unfold cw
  have h1 : (Finsupp.equivFunOnFinite (α := Fin n) (M := ℕ))
      ((Finsupp.equivFunOnFinite (α := Fin n) (M := ℕ)).symm (fun k => w - b k)) =
      (fun k => w - b k) := by
    exact Equiv.apply_symm_apply (Finsupp.equivFunOnFinite (α := Fin n) (M := ℕ)) (fun k => w - b k)
  have h2 : (Finsupp.equivFunOnFinite (α := Fin n) (M := ℕ))
      ((Finsupp.equivFunOnFinite (α := Fin n) (M := ℕ)).symm (fun k => w - b k)) k =
      (Finsupp.equivFunOnFinite (α := Fin n) (M := ℕ)).symm (fun k => w - b k) k := by
    exact Finsupp.equivFunOnFinite_apply _ k
  rw [← h2, h1]

lemma cw_cw {n : ℕ} (w : ℕ) (b : Fin n →₀ ℕ) (hb : ∀ k : Fin n, b k ≤ w) :
    cw w (cw w b) = b := by
  ext k
  rw [cw_apply, cw_apply]
  exact Nat.sub_sub_self (hb k)

lemma cw_sub_add {n : ℕ} (w : ℕ) (b : Fin n →₀ ℕ) (i j : Fin n) (hij : i ≠ j) (hbi : 1 ≤ b i)
    (hbw : b i ≤ w) :
    cw w (b - e i + e j) = cw w b - e j + e i := by
  ext k
  rw [cw_apply]
  by_cases hki : k = i
  · subst k
    have hL : (b - e i + e j) i = b i - 1 := by simp [e, Finsupp.single_apply, hij]
    have hR : (cw w b - e j + e i) i = w - b i + 1 := by
      simp [e, Finsupp.single_apply, hij, cw_apply]
    rw [hL, hR]
    omega
  · by_cases hkj : k = j
    · subst k
      have hL : (b - e i + e j) j = b j + 1 := by simp [e, Finsupp.single_apply, hij]
      have hR : (cw w b - e j + e i) j = w - b j - 1 := by
        simp [e, Finsupp.single_apply, hij, cw_apply]
      rw [hL, hR]
      exact (Nat.sub_sub w (b j) 1).symm
    · have hL : (b - e i + e j) k = b k := by simp [e, Finsupp.single_apply, hki, hkj]
      have hR : (cw w b - e j + e i) k = w - b k := by
        simp [e, Finsupp.single_apply, hki, hkj, cw_apply]
      rw [hL, hR]

def complSet {n : ℕ} (w : ℕ) (J : Set (Fin n →₀ ℕ)) : Set (Fin n →₀ ℕ) :=
  {c | ∃ b ∈ J, c = cw w b}

lemma cw_mem_complSet {n : ℕ} {w : ℕ} {J : Set (Fin n →₀ ℕ)} {b : Fin n →₀ ℕ}
    (hb : b ∈ J) : cw w b ∈ complSet w J :=
  ⟨b, hb, rfl⟩

lemma coord_le_of_degree {n w : ℕ} {b : Fin n →₀ ℕ} (hb : Finsupp.degree b = w) (k : Fin n) :
    b k ≤ w := by
  have hsum : (∑ i : Fin n, b i) = w := by
    rw [← hb]
    exact (Finsupp.degree_eq_sum b).symm
  rw [← hsum]
  exact Finset.single_le_sum (f := fun i : Fin n => b i) (by intro i hi; exact Nat.zero_le _) (Finset.mem_univ k)

lemma sum_cw {n : ℕ} (w : ℕ) (b : Fin n →₀ ℕ) (hb : ∀ k : Fin n, b k ≤ w) :
    (∑ k : Fin n, cw w b k) = n * w - (∑ k : Fin n, b k) := by
  have hsum : (∑ k : Fin n, (w - b k)) + (∑ k : Fin n, b k) = n * w := by
    rw [← Finset.sum_add_distrib]
    simp [Nat.sub_add_cancel, hb]
  calc
    (∑ k : Fin n, cw w b k) = (∑ k : Fin n, (w - b k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [cw_apply]
    _ = n * w - (∑ k : Fin n, b k) := by omega

lemma complSet_equisum {n w : ℕ} {J : Set (Fin n →₀ ℕ)}
    (hdeg : ∀ b ∈ J, Finsupp.degree b = w) (c : Fin n →₀ ℕ) (hc : c ∈ complSet w J) :
    (∑ k : Fin n, c k) = n * w - w := by
  rcases hc with ⟨b, hb, hbc⟩
  subst c
  have hbw : Finsupp.degree b = w := hdeg b hb
  have hbsum : (∑ i : Fin n, b i) = w := by
    rw [← hbw]
    exact (Finsupp.degree_eq_sum b).symm
  rw [sum_cw]
  · rw [hbsum]
  · intro k
    exact coord_le_of_degree hbw k


/-- extracting an element of J from a complement membership of an exchange move -/
lemma preimage_mem {n w : ℕ} {J : Set (Fin n →₀ ℕ)}
    (hdeg : ∀ b ∈ J, Finsupp.degree b = w)
    {b : Fin n →₀ ℕ} (hb : b ∈ J) {u v : Fin n}
    (huv : u ≠ v) (hbv : 1 ≤ b v) (hbu_safe : b u + 1 ≤ w)
    (hmem : cw w b - e u + e v ∈ complSet w J) :
    b - e v + e u ∈ J := by
  rcases hmem with ⟨z, hzJ, hz_eq⟩
  have hz : z = b - e v + e u := by
    have hid : cw w (b - e v + e u) = cw w b - e u + e v := by
      simpa using (cw_sub_add w b v u (Ne.symm huv) hbv (coord_le_of_degree (hdeg b hb) v))
    have hcw_eq : cw w z = cw w (b - e v + e u) := by
      rw [← hz_eq, ← hid]
    have hzb : ∀ k : Fin n, z k ≤ w := fun k => coord_le_of_degree (hdeg z hzJ) k
    have htb : ∀ k : Fin n, (b - e v + e u) k ≤ w := by
      intro k
      by_cases hku : k = u
      · subst k
        have hv : (b - e v + e u) u = b u + 1 := by
          simp [e, Finsupp.single_apply, Ne.symm huv]
        rw [hv]
        exact hbu_safe
      · by_cases hkv : k = v
        · subst k
          have hv : (b - e v + e u) v = b v - 1 := by
            simp [e, Finsupp.single_apply, huv]
          rw [hv]
          exact le_trans (Nat.sub_le (b v) 1) (coord_le_of_degree (hdeg b hb) v)
        · have hv : (b - e v + e u) k = b k := by
            simp [e, Finsupp.single_apply, hkv, hku]
          rw [hv]
          exact coord_le_of_degree (hdeg b hb) k
    calc
      z = cw w (cw w z) := (cw_cw w z hzb).symm
      _ = cw w (cw w (b - e v + e u)) := by rw [hcw_eq]
      _ = b - e v + e u := cw_cw w (b - e v + e u) htb
  simpa [hz] using hzJ

/-- the source-side one-sided exchange of J gives the target-side one-sided
    exchange of the complement family -/
lemma E2_compl {n w : ℕ} {J : Set (Fin n →₀ ℕ)}
    (hdeg : ∀ b ∈ J, Finsupp.degree b = w)
    (hE1 : ∀ x ∈ J, ∀ y ∈ J, ∀ i : Fin n, x i > y i →
      ∃ j : Fin n, x j < y j ∧ x - e i + e j ∈ J) :
    ∀ p ∈ complSet w J, ∀ q ∈ complSet w J, ∀ i : Fin n, p i > q i →
      ∃ j : Fin n, p j < q j ∧ q - e j + e i ∈ complSet w J := by
  intro p hp q hq i hgt
  rcases hp with ⟨a, haJ, hpa⟩
  rcases hq with ⟨b, hbJ, hqb⟩
  have haw : Finsupp.degree a = w := hdeg a haJ
  have hbw : Finsupp.degree b = w := hdeg b hbJ
  have hab : a i < b i := by
    have h1 : (cw w a) i > (cw w b) i := by simpa [hpa, hqb] using hgt
    simp [cw_apply] at h1
    have hai : a i ≤ w := coord_le_of_degree haw i
    have hbi : b i ≤ w := coord_le_of_degree hbw i
    omega
  have hba : b i > a i := hab
  rcases hE1 b hbJ a haJ i hba with ⟨j, hbj, hbji⟩
  refine ⟨j, ?_, ?_⟩
  · have h1 : w - a j < w - b j := by
      have haj : a j ≤ w := coord_le_of_degree haw j
      have hbj2 : b j ≤ w := coord_le_of_degree hbw j
      omega
    simpa [hpa, hqb, cw_apply] using h1
  · have hji : j ≠ i := by
      intro hji0
      have h1 : b i < a i := by simpa [hji0] using hbj
      omega
    have hbige : 1 ≤ b i := by omega
    refine ⟨b - e i + e j, hbji, ?_⟩
    rw [hqb, cw_sub_add w b i j (Ne.symm hji) hbige (coord_le_of_degree hbw i)]

/-- the symmetric exchange of the complement family gives the symmetric
    exchange of J -/
lemma sym_compl {n w : ℕ} {J : Set (Fin n →₀ ℕ)}
    (hdeg : ∀ b ∈ J, Finsupp.degree b = w)
    (hSE : ∀ p ∈ complSet w J, ∀ q ∈ complSet w J, ∀ i : Fin n, p i > q i →
      ∃ j : Fin n, p j < q j ∧ p - e i + e j ∈ complSet w J ∧
        q - e j + e i ∈ complSet w J) :
    ∀ x ∈ J, ∀ y ∈ J, ∀ i : Fin n, x i > y i →
      ∃ j : Fin n, x j < y j ∧ x - e i + e j ∈ J ∧ y - e j + e i ∈ J := by
  intro x hx y hy i hgt
  have hxw : Finsupp.degree x = w := hdeg x hx
  have hyw : Finsupp.degree y = w := hdeg y hy
  have hgt' : (cw w y) i > (cw w x) i := by
    have hxi : x i ≤ w := coord_le_of_degree hxw i
    have hyi : y i ≤ w := coord_le_of_degree hyw i
    simp [cw_apply]
    omega
  rcases hSE (cw w y) (cw_mem_complSet hy) (cw w x) (cw_mem_complSet hx) i hgt' with ⟨j, h1, h2, h3⟩
  have hxyj : x j < y j := by
    have hxj : x j ≤ w := coord_le_of_degree hxw j
    have hyj : y j ≤ w := coord_le_of_degree hyw j
    simp [cw_apply] at h1
    omega
  have hij : i ≠ j := by
    intro hij0
    have : x i < y i := by simpa [hij0] using hxyj
    omega
  have hyjge : 1 ≤ y j := by omega
  have hysafe : y i + 1 ≤ w := by
    have hxi : x i ≤ w := coord_le_of_degree hxw i
    omega
  have h2J : y - e j + e i ∈ J := by
    exact preimage_mem (hdeg := hdeg) (hb := hy) (u := i) (v := j) hij hyjge hysafe h2
  have hxige : 1 ≤ x i := by omega
  have hxsafe : x j + 1 ≤ w := by
    have hyj : y j ≤ w := coord_le_of_degree hyw j
    omega
  have h3J : x - e i + e j ∈ J := by
    exact preimage_mem (hdeg := hdeg) (hb := hx) (u := j) (v := i) (Ne.symm hij) hxige hxsafe h3
  exact ⟨j, hxyj, h3J, h2J⟩

end
end CompExch



/-- Symmetric (two-sided) exchange for constant-weight M-convex families.

A set `J ⊆ (Fin n →₀ ℕ)` satisfying the one-sided exchange axiom
(`∀ x ∈ J, ∀ y ∈ J, ∀ i, x i > y i → ∃ j, x j < y j ∧ x - single i 1 + single j 1 ∈ J`)
whose elements all have the same total degree `w` (`∀ x ∈ J, Finsupp.degree x = w`)
satisfies the symmetric exchange axiom: whenever `x, y ∈ J` and `x i > y i`, there
is `j` with `x j < y j` and both `x - single i 1 + single j 1 ∈ J` and
`y - single j 1 + single i 1 ∈ J`. -/
theorem symmetric_exchange_const_weight {n w : ℕ} (J : Set (Fin n →₀ ℕ))
    (hJ : ∀ x ∈ J, ∀ y ∈ J, ∀ i : Fin n, x i > y i →
      ∃ j : Fin n, x j < y j ∧ x - Finsupp.single i 1 + Finsupp.single j 1 ∈ J)
    (hcw : ∀ x ∈ J, Finsupp.degree x = w)
    (x : Fin n →₀ ℕ) (hx : x ∈ J) (y : Fin n →₀ ℕ) (hy : y ∈ J)
    (i : Fin n) (hgt : x i > y i) :
    ∃ j : Fin n, x j < y j ∧
      x - Finsupp.single i 1 + Finsupp.single j 1 ∈ J ∧
      y - Finsupp.single j 1 + Finsupp.single i 1 ∈ J := by
  classical
  have hdegC : ∀ c ∈ CompExch.complSet w J, (∑ k : Fin n, c k) = n * w - w :=
    fun c hc => CompExch.complSet_equisum hcw c hc
  have hE2C : ∀ p ∈ CompExch.complSet w J, ∀ q ∈ CompExch.complSet w J,
      ∀ i : Fin n, p i > q i →
        ∃ j : Fin n, p j < q j ∧
          q - SymmetricExchange.e j + SymmetricExchange.e i ∈ CompExch.complSet w J :=
    CompExch.E2_compl hcw hJ
  have hSE : ∀ p ∈ CompExch.complSet w J, ∀ q ∈ CompExch.complSet w J,
      ∀ i : Fin n, p i > q i →
        ∃ j : Fin n, p j < q j ∧
          p - SymmetricExchange.e i + SymmetricExchange.e j ∈ CompExch.complSet w J ∧
          q - SymmetricExchange.e j + SymmetricExchange.e i ∈ CompExch.complSet w J :=
    SymmetricExchange.coreE2 (A := CompExch.complSet w J) (d := n * w - w) hdegC hE2C
  exact CompExch.sym_compl hcw hSE x hx y hy i hgt

end Commons.Combinatorics.MvPolynomial
