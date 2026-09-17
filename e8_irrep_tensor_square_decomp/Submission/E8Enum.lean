import Submission.E8Orbit

/-!
# Enumerating the dominant weights below a dominant weight

For a dominant weight `λ` the set `{ν : ν dominant, λ - ν ∈ ℕΦ⁺}` is finite, and it is needed
*explicitly*: for the Freudenthal recursion (determining the dominant multiplicities) and for the
bound `≤ 40` on the number of isotypic components of the tensor square.

The key observation that makes the enumeration a *small computation* is the following.  `E₈` is
simply laced with an integral inverse Cartan matrix `E8inv = A⁻¹`, whose entries are non-negative
and whose last row has all entries `≥ 2`.  If `ν` is dominant (`ν i ≥ 0`) and `λ - ν ∈ ℕΦ⁺`, then

  `0 ≤ (A⁻¹(λ - ν))₇ = (A⁻¹λ)₇ - ∑ j (A⁻¹)₇ⱼ ν j ≤ 4 - 2 ∑ j ν j`,

hence **`∑ j ν j ≤ 2`** (and `≤ 4` when `λ` is replaced by `2λ`).  So only the vectors with
non-negative entries and small coordinate sum have to be inspected.

`levelL k` lists all `v : Fin 8 → ℤ` with non-negative entries and `∑ v i = k`, built recursively
(possibly with repetitions); `candL k` is the union over `m ≤ k`.  `mem_levelL` proves completeness
(every non-negative vector of sum `k` occurs).  The enumerations are then certified by a `decide`
computation over these short lists.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 200000

namespace Submission.E8Enum

open Submission.WeylReflect Submission.E8Character

/-- The `i`-th standard basis vector of `Fin 8 → ℤ`. -/
def e (i : Fin 8) : Fin 8 → ℤ := fun j => if j = i then 1 else 0

lemma e_nonneg (i : Fin 8) : ∀ j, 0 ≤ e i j := by
  intro j; by_cases h : j = i <;> simp [e, h]

lemma sum_e (i : Fin 8) : ∑ j, e i j = 1 := by simp [e]

/-- All non-negative vectors with coordinate sum `k` (with repetitions). -/
def levelL : ℕ → List (Fin 8 → ℤ)
  | 0 => [0]
  | (k+1) => (levelL k).flatMap fun v => (List.finRange 8).map fun i => v + e i

/-- All non-negative vectors with coordinate sum `≤ k` (with repetitions). -/
def candL (k : ℕ) : List (Fin 8 → ℤ) := (List.range (k+1)).flatMap levelL

/-- A non-negative vector of coordinate sum zero is zero. -/
lemma eq_zero_of_sum_eq_zero {v : Fin 8 → ℤ} (h : ∀ i, 0 ≤ v i) (hs : ∑ i, v i = 0) :
    v = 0 := by
  funext i
  have h1 : v i ≤ ∑ j, v j := Finset.single_le_sum (fun j _ => h j) (Finset.mem_univ i)
  rw [hs] at h1
  exact le_antisymm h1 (h i)

/-- **Completeness of `levelL`.** -/
lemma mem_levelL : ∀ (k : ℕ) (v : Fin 8 → ℤ), (∀ i, 0 ≤ v i) → ∑ i, v i = (k : ℤ) →
    v ∈ levelL k := by
  intro k
  induction k with
  | zero =>
    intro v h hs
    have hv : v = 0 := eq_zero_of_sum_eq_zero h (by simpa using hs)
    rw [hv]
    simp [levelL]
  | succ k ih =>
    intro v h hs
    by_cases hv : v = 0
    · rw [hv] at hs
      simp only [Pi.zero_apply, Finset.sum_const_zero] at hs
      exact absurd hs (by omega)
    · have hex : ∃ i, 0 < v i := by
        by_contra hc
        push Not at hc
        exact hv (funext fun i => le_antisymm (hc i) (h i))
      obtain ⟨i, hi⟩ := hex
      have hsub : ∀ j, 0 ≤ (v - e i) j := by
        intro j
        have h1 : (e i) j ≤ v j := by
          by_cases hji : j = i
          · rw [hji]; simp [e]; omega
          · simp [e, hji]; exact h j
        simp only [Pi.sub_apply]
        omega
      have hsum : ∑ j, (v - e i) j = (k : ℤ) := by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_e, hs]
        simp
      have hmem := ih (v - e i) hsub hsum
      have hvadd : v = (v - e i) + e i := by
        funext j
        by_cases hji : j = i <;> simp [e, hji]
      rw [hvadd, levelL]
      exact List.mem_flatMap.mpr ⟨v - e i, hmem, by
        rw [List.mem_map]
        exact ⟨i, List.mem_finRange i, rfl⟩⟩

/-- **Completeness of `candL`.** -/
lemma mem_candL {k : ℕ} {v : Fin 8 → ℤ} (h : ∀ i, 0 ≤ v i) (hs : ∑ i, v i ≤ (k : ℤ)) :
    v ∈ candL k := by
  have h0 : 0 ≤ ∑ i, v i := Finset.sum_nonneg fun i _ => h i
  have hmk : (∑ i, v i).toNat ≤ k := by
    have := Int.toNat_le.mpr hs
    simpa [h0] using this
  refine List.mem_flatMap.mpr ⟨(∑ i, v i).toNat, List.mem_range.mpr (Nat.lt_succ_of_le hmk), ?_⟩
  exact mem_levelL _ v h (Int.toNat_of_nonneg h0).symm

/-- Decidable "all entries are non-negative". -/
def allNonneg (v : Fin 8 → ℤ) : Bool := (List.finRange 8).all fun i => decide (0 ≤ v i)

/-- Decidable "in the positive cone". -/
def posB (γ : Fin 8 → ℤ) : Bool := (List.finRange 8).all fun i => decide (0 ≤ coords γ i)

lemma allNonneg_true {v : Fin 8 → ℤ} : allNonneg v = true ↔ ∀ i, 0 ≤ v i := by
  simp only [allNonneg, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

lemma posB_true {γ : Fin 8 → ℤ} : posB γ = true ↔ posCon γ := by
  simp only [posB, posCon, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq]

/-! ## The two enumerations -/

/-- `λ = ω₁ + ω₈` in `ω`-coordinates. -/
def lam : Fin 8 → ℤ := fun i => if i = 0 then 1 else if i = 7 then 1 else 0

lemma coords_sub (γ δ : Fin 8 → ℤ) : coords (γ - δ) = coords γ - coords δ := by
  simp only [coords_eq, Matrix.mulVec_sub]

lemma E8inv_row7_ge_two : ∀ j : Fin 8, 2 ≤ E8inv 7 j := by decide

lemma row7_bound {ν : Fin 8 → ℤ} (hd : ∀ i, 0 ≤ ν i) (M : ℤ)
    (h : ∑ j, E8inv 7 j * ν j ≤ M) : 2 * (∑ j, ν j) ≤ M := by
  refine le_trans ?_ h
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := hd j
  have h2 := E8inv_row7_ge_two j
  nlinarith

/-- If `ν` is dominant and `λ - ν ∈ ℕΦ⁺` then `∑ ν j ≤ 2`. -/
lemma sum_le_two_lam {ν : Fin 8 → ℤ} (hd : ∀ i, 0 ≤ ν i) (hp : posCon (lam - ν)) :
    ∑ j, ν j ≤ 2 := by
  have h := hp 7
  have hrow : coords ν 7 = ∑ j, E8inv 7 j * ν j := rfl
  have hlam : coords lam 7 = 4 := by decide
  have h' : 0 ≤ coords lam 7 - coords ν 7 := by
    have h2 : 0 ≤ coords (lam - ν) 7 := h
    rwa [coords_sub, Pi.sub_apply] at h2
  rw [hrow, hlam] at h'
  have h2 := row7_bound hd 4 (by linarith)
  omega

/-- If `ν` is dominant and `2λ - ν ∈ ℕΦ⁺` then `∑ ν j ≤ 4`. -/
lemma sum_le_four_lam {ν : Fin 8 → ℤ} (hd : ∀ i, 0 ≤ ν i) (hp : posCon (2 • lam - ν)) :
    ∑ j, ν j ≤ 4 := by
  have h := hp 7
  have hrow : coords ν 7 = ∑ j, E8inv 7 j * ν j := rfl
  have hlam : coords (2 • lam) 7 = 8 := by decide
  have h' : 0 ≤ coords (2 • lam) 7 - coords ν 7 := by
    have h2 : 0 ≤ coords (2 • lam - ν) 7 := h
    rwa [coords_sub, Pi.sub_apply] at h2
  rw [hrow, hlam] at h'
  have h2 := row7_bound hd 8 (by linarith)
  omega

/-- The seven dominant weights `⪯ λ`. -/
def the7 : List (Fin 8 → ℤ) := [lam, e 1, 2 • e 7, e 6, e 0, e 7, 0]

/-- The forty dominant weights `⪯ 2λ`. -/
def the40 : List (Fin 8 → ℤ) :=
  [2 • e 0 + 2 • e 7, e 2 + 2 • e 7, 2 • e 0 + e 6, e 2 + e 6, e 0 + e 1 + e 7,
   e 5 + 2 • e 7, e 5 + e 6, e 4 + e 7, 3 • e 0, e 0 + e 2, 2 • e 1, e 3,
   e 0 + 3 • e 7, e 0 + e 6 + e 7, e 0 + e 5, e 1 + 2 • e 7, e 1 + e 6, 2 • e 0 + e 7,
   e 2 + e 7, 4 • e 7, e 6 + 2 • e 7, 2 • e 6, e 0 + e 1, e 5 + e 7, e 4,
   e 0 + 2 • e 7, e 0 + e 6, e 1 + e 7, 2 • e 0, e 2, 3 • e 7, e 6 + e 7, e 5,
   e 0 + e 7, e 1, 2 • e 7, e 6, e 0, e 7, 0]

lemma the7_nodup : the7.Nodup := by decide

lemma the40_nodup : the40.Nodup := by decide

lemma the7_length : the7.length = 7 := rfl

lemma the40_length : the40.length = 40 := rfl

/-- **The enumeration check for `λ`**: the only vectors in `candL 2` that are dominant and in the
cone below `λ` are the seven listed ones. -/
theorem verify7 :
    (candL 2).all (fun v => (!(allNonneg v && posB (lam - v))) || (v ∈ the7)) = true := by
  decide

/-- **The enumeration check for `2λ`**: the only vectors in `candL 4` that are dominant and in the
cone below `2λ` are the forty listed ones. -/
theorem verify40 :
    (candL 4).all (fun v => (!(allNonneg v && posB (2 • lam - v))) || (v ∈ the40)) = true := by
  decide

/-- Every dominant weight in the cone below `λ` is one of the seven. -/
theorem mem_the7 {ν : Fin 8 → ℤ} (h1 : allNonneg ν = true) (h2 : posB (lam - ν) = true) :
    ν ∈ the7 := by
  have hd : ∀ i, 0 ≤ ν i := (allNonneg_true).mp h1
  have hp : posCon (lam - ν) := (posB_true).mp h2
  have hmem : ν ∈ candL 2 := mem_candL hd (sum_le_two_lam hd hp)
  have hall := (List.all_eq_true).mp verify7 ν hmem
  have hab : (allNonneg ν && posB (lam - ν)) = true := (Bool.and_eq_true_iff).mpr ⟨h1, h2⟩
  rw [hab] at hall
  simpa using hall

/-- Every dominant weight in the cone below `2λ` is one of the forty. -/
theorem mem_the40 {ν : Fin 8 → ℤ} (h1 : allNonneg ν = true) (h2 : posB (2 • lam - ν) = true) :
    ν ∈ the40 := by
  have hd : ∀ i, 0 ≤ ν i := (allNonneg_true).mp h1
  have hp : posCon (2 • lam - ν) := (posB_true).mp h2
  have hmem : ν ∈ candL 4 := mem_candL hd (sum_le_four_lam hd hp)
  have hall := (List.all_eq_true).mp verify40 ν hmem
  have hab : (allNonneg ν && posB (2 • lam - ν)) = true := (Bool.and_eq_true_iff).mpr ⟨h1, h2⟩
  rw [hab] at hall
  simpa using hall

/-- The case analysis over the dominant weights below `λ`. -/
theorem mem_the7_cases {ν : Fin 8 → ℤ} (h : ν ∈ the7) :
    ν = lam ∨ ν = e 1 ∨ ν = 2 • e 7 ∨ ν = e 6 ∨ ν = e 0 ∨ ν = e 7 ∨ ν = 0 := by
  simp only [the7, List.mem_cons, List.not_mem_nil, or_false] at h
  tauto

end Submission.E8Enum
