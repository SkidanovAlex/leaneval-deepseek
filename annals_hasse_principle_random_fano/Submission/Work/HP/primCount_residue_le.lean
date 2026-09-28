import Mathlib
import Submission.Work.HP.Defs

/-!
# Residue-class bound for the height ball

The number of primitive coefficient vectors of height `≤ A` in a fixed congruence class
modulo `q` is at most `(2A/q + 1)^N`, where `N = N_{d,n}` is the number of degree-`d`
monomials in `n+1` variables.

Route:
* a vector of height `≤ A` has every coordinate of absolute value `≤ A` (the Euclidean
  norm dominates each coordinate);
* for a single coordinate the integers in `[-A, A]` lying in a fixed residue class modulo
  `q` form a progression of step `q`, so there are at most `2A/q + 1` of them;
* the vectors of the ball are then contained in the product, over the `N` coordinates, of
  these per-coordinate sets, so the box count is the product of the `N` factors.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP

variable {d n : ℕ}

/-- Every coordinate of an integer vector is bounded by its Euclidean norm. -/
private lemma abs_coord_le_eNorm (a : Mon d n → ℤ) (m : Mon d n) :
    |(a m : ℝ)| ≤ eNorm a := by
  have h1 : ((a m : ℝ)) ^ 2 ≤ ∑ i, ((a i : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg ((a i : ℝ))) (Finset.mem_univ m)
  calc |(a m : ℝ)| = Real.sqrt (((a m : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ i, ((a i : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = eNorm a := rfl

/-- The integers in a real interval of length `b - a` number at most `b - a + 1`. -/
private lemma ncard_int_Icc_le (a b : ℝ) (hab : a ≤ b) :
    ((({k : ℤ | a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b}).ncard : ℕ) : ℝ) ≤ b - a + 1 := by
  have hsub : {k : ℤ | a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b} ⊆ ↑(Finset.Icc ⌈a⌉ ⌊b⌋) := by
    intro k hk
    simp only [Set.mem_ofPred_eq] at hk
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr hk.1, Int.le_floor.mpr hk.2⟩
  have hcard : ({k : ℤ | a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b}).ncard ≤ (Finset.Icc ⌈a⌉ ⌊b⌋).card := by
    have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rwa [Set.ncard_coe_finset] at h
  rw [Int.card_Icc] at hcard
  set ς : ℤ := ⌊b⌋ + 1 - ⌈a⌉ with hς
  have hςle : (ς : ℝ) ≤ b - a + 1 := by
    rw [hς]; push_cast; linarith [Int.floor_le b, Int.le_ceil a]
  have hnat : ((ς.toNat : ℕ) : ℝ) ≤ b - a + 1 := by
    by_cases h : 0 ≤ ς
    · have h' : ((ς.toNat : ℕ) : ℝ) = (ς : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg h : ((ς.toNat : ℕ) : ℤ) = ς)
      rw [h']; exact hςle
    · have hlt : ς ≤ 0 := by omega
      have h' : ς.toNat = 0 := by rw [Int.toNat_eq_zero]; exact hlt
      rw [h']; simp only [Nat.cast_zero]; linarith
  calc ((({k : ℤ | a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b}).ncard : ℕ) : ℝ)
      ≤ ((ς.toNat : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ b - a + 1 := hnat

/-- **Single-coordinate residue count.** The integers `x` of absolute value at most `A`
that are congruent to `c` modulo `q ≥ 1` number at most `2A/q + 1`. -/
private lemma ncard_residue_le (A : ℝ) (hA : 0 ≤ A) (q : ℕ) (hq : 1 ≤ q) (c : ℤ) :
    ((({x : ℤ | |(x : ℝ)| ≤ A ∧ (q : ℤ) ∣ x - c}).ncard : ℕ) : ℝ) ≤ 2 * A / (q : ℝ) + 1 := by
  set r : ℤ := c % (q : ℤ) with hr
  have hqpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  -- `r` is congruent to `c` modulo `q`, so `q ∣ c - r`
  have hcmod : (q : ℤ) ∣ c - r := by
    rw [hr]
    exact Int.modEq_iff_dvd.mp (Int.mod_modEq c (q : ℤ))
  have hdvd : ∀ x : ℤ, (q : ℤ) ∣ x - c → (q : ℤ) ∣ x - r := fun x hx => by
    have h : x - r = (x - c) + (c - r) := by ring
    rw [h]; exact dvd_add hx hcmod
  -- the map `x ↦ (x - r) / q` is injective on the residue class
  have hinj : Set.InjOn (fun x : ℤ => (x - r) / (q : ℤ))
      {x : ℤ | |(x : ℝ)| ≤ A ∧ (q : ℤ) ∣ x - c} := by
    intro x hx y hy hxy
    have hx' := hdvd x hx.2
    have hy' := hdvd y hy.2
    have h1 : (x - r) / (q : ℤ) * (q : ℤ) = x - r := Int.ediv_mul_cancel hx'
    have h2 : (y - r) / (q : ℤ) * (q : ℤ) = y - r := Int.ediv_mul_cancel hy'
    have hxy' : (x - r) / (q : ℤ) = (y - r) / (q : ℤ) := hxy
    have h : x - r = y - r := by rw [← h1, ← h2, hxy']
    linarith
  -- the image lies in an interval of length `2A/q`
  have hsubimg : (fun x : ℤ => (x - r) / (q : ℤ)) ''
        {x : ℤ | |(x : ℝ)| ≤ A ∧ (q : ℤ) ∣ x - c} ⊆
      {k : ℤ | (-A - (r : ℝ)) / (q : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ (A - (r : ℝ)) / (q : ℝ)} := by
    rintro k ⟨x, hx, rfl⟩
    have hxd := hdvd x hx.2
    have hcast : (((x - r) / (q : ℤ) : ℤ) : ℝ) * (q : ℝ) = (x : ℝ) - (r : ℝ) := by
      have h1 : (x - r) / (q : ℤ) * (q : ℤ) = x - r := Int.ediv_mul_cancel hxd
      have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
      push_cast at h2
      linarith
    obtain ⟨hxge, hxle⟩ := abs_le.mp hx.1
    constructor
    · rw [div_le_iff₀ hqR, hcast]; linarith
    · rw [le_div_iff₀ hqR, hcast]; linarith
  have hVfin :
      ({k : ℤ | (-A - (r : ℝ)) / (q : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ (A - (r : ℝ)) / (q : ℝ)}).Finite :=
    (Finset.finite_toSet _).subset (by
      intro k hk
      simp only [Set.mem_ofPred_eq] at hk
      rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨Int.ceil_le.mpr hk.1, Int.le_floor.mpr hk.2⟩)
  have hVbound :
      ((({k : ℤ | (-A - (r : ℝ)) / (q : ℝ) ≤ (k : ℝ) ∧
          (k : ℝ) ≤ (A - (r : ℝ)) / (q : ℝ)}).ncard : ℕ) : ℝ)
        ≤ (A - (r : ℝ)) / (q : ℝ) - ((-A - (r : ℝ)) / (q : ℝ)) + 1 :=
    ncard_int_Icc_le _ _
      (div_le_div_of_nonneg_right (by linarith : -A - (r : ℝ) ≤ A - (r : ℝ)) (le_of_lt hqR))
  calc ((({x : ℤ | |(x : ℝ)| ≤ A ∧ (q : ℤ) ∣ x - c}).ncard : ℕ) : ℝ)
      = ((((fun x : ℤ => (x - r) / (q : ℤ)) ''
          {x : ℤ | |(x : ℝ)| ≤ A ∧ (q : ℤ) ∣ x - c}).ncard : ℕ) : ℝ) := by
        rw [Set.InjOn.ncard_image hinj]
    _ ≤ ((({k : ℤ | (-A - (r : ℝ)) / (q : ℝ) ≤ (k : ℝ) ∧
          (k : ℝ) ≤ (A - (r : ℝ)) / (q : ℝ)}).ncard : ℕ) : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hsubimg hVfin
    _ ≤ (A - (r : ℝ)) / (q : ℝ) - ((-A - (r : ℝ)) / (q : ℝ)) + 1 := hVbound
    _ = 2 * A / (q : ℝ) + 1 := by ring

/-- Residue-class upper bound for the height ball: the number of primitive coefficient vectors of height `≤ A` lying in a fixed congruence class modulo `q ≥ 1` is at most `(2A/q + 1)^N`, where `N = N_{d,n}` is the number of degree-`d` monomials in `n+1` variables.  Route: a vector of height `≤ A` has every coordinate of absolute value `≤ A`; for one coordinate the integers in `[-A, A]` in a fixed residue class modulo `q` form a progression with step `q`, so there are at most `2A/q + 1` of them, and the box count is the product over the `N` coordinates. -/
theorem primCount_residue_le (d n : ℕ) (A : ℝ) (hA : 0 ≤ A) (q : ℕ) (hq : 1 ≤ q)
    (b : Mon d n → ℤ) :
    primCount d n A (fun a => ∀ m, (q : ℤ) ∣ a m - b m) ≤ (2 * A / (q : ℝ) + 1) ^ NN d n := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  -- the per-coordinate sets are finite (bounded subsets of `ℤ`)
  have hUfin : ∀ m : Mon d n,
      ({x : ℤ | |(x : ℝ)| ≤ A ∧ (q : ℤ) ∣ x - b m}).Finite := by
    intro m
    refine (Finset.finite_toSet (Finset.Icc (-(Nat.ceil A : ℤ)) (Nat.ceil A : ℤ))).subset ?_
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rw [Finset.mem_coe, Finset.mem_Icc]
    have h : |(x : ℝ)| ≤ (Nat.ceil A : ℝ) := le_trans hx.1 (Nat.le_ceil A)
    have h' : |x| ≤ (Nat.ceil A : ℤ) := by exact_mod_cast h
    exact abs_le.mp h'
  -- the height ball is contained in the product of the per-coordinate sets
  have hsub : primSet d n A (fun a => ∀ m, (q : ℤ) ∣ a m - b m) ⊆
      ↑(Fintype.piFinset (fun m : Mon d n => (hUfin m).toFinset)) := by
    intro a ha
    rw [primSet] at ha
    simp only [Set.mem_ofPred_eq] at ha
    obtain ⟨-, hnorm, hres⟩ := ha
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro m
    rw [Set.Finite.mem_toFinset]
    exact ⟨le_trans (abs_coord_le_eNorm a m) hnorm, hres m⟩
  have hcard : (primSet d n A (fun a => ∀ m, (q : ℤ) ∣ a m - b m)).ncard ≤
      (Fintype.piFinset (fun m : Mon d n => (hUfin m).toFinset)).card := by
    have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rwa [Set.ncard_coe_finset] at h
  calc primCount d n A (fun a => ∀ m, (q : ℤ) ∣ a m - b m)
      = ((primSet d n A (fun a => ∀ m, (q : ℤ) ∣ a m - b m)).ncard : ℝ) := rfl
    _ ≤ ((Fintype.piFinset (fun m : Mon d n => (hUfin m).toFinset)).card : ℝ) := by
        exact_mod_cast hcard
    _ = ∏ m : Mon d n, (((hUfin m).toFinset).card : ℝ) := by
        rw [Fintype.card_piFinset, Nat.cast_prod]
    _ = ∏ m : Mon d n, ((({x : ℤ | |(x : ℝ)| ≤ A ∧ (q : ℤ) ∣ x - b m}).ncard : ℕ) : ℝ) := by
        refine Finset.prod_congr rfl (fun m _ => ?_)
        rw [Set.ncard_eq_toFinset_card _ (hUfin m)]
    _ ≤ ∏ _m : Mon d n, (2 * A / (q : ℝ) + 1) :=
        Finset.prod_le_prod₀ (fun m _ => Nat.cast_nonneg _)
          (fun m _ => ncard_residue_le A hA q hq (b m))
    _ = (2 * A / (q : ℝ) + 1) ^ NN d n := by
        rw [Finset.prod_const, Finset.card_univ]

end Work.HP
