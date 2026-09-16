import Submission.ZagierHoffmanProof.StepB6

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Step B7: level-zero power sums (diagonal-expansion ground work)

`P_0(n) = 1`: over the single monic constant polynomial.  This handles the `ℓ = 0`
term in the equal-degree diagonal of the `S_<d` product recursion, where
`thakur_prod_one` (which needs `hd : 1 ≤ ℓ`) is not available.
-/

namespace ZagierHoffmanPositiveChar
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Monic degree-0 polynomials are the constant 1. -/
lemma head_zero_eq_one (p : HeadD F 0) : p.1 = 1 := by
  have hdeg : p.1.natDegree = 0 := p.2.2
  have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  rw [hC]
  have hc : p.1.coeff 0 = 1 := by
    have hmon := p.2.1.coeff_natDegree
    simpa [hdeg] using hmon
  rw [hc]
  simp

/-- `P_0(n) = 1`: over the single monic constant polynomial. -/
lemma P_zero_eq_one (n : ℕ+) : P F 0 n = 1 := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  rw [P_eq_sum F 0 n]
  have hterm : ∀ p : HeadD F 0, ((((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (n : ℕ))⁻¹) =
      (1 : RatFunc.CompletionAtInfty F) := by
    intro p
    have hp : p.1 = 1 := head_zero_eq_one F p
    rw [hp]
    change ((((1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (n : ℕ))⁻¹ = 1
    rw [show (((1 : F[X]) : RatFunc F) : RatFunc.CompletionAtInfty F) = 1 by
      change (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) ((1 : F[X]) : RatFunc F) = 1
      simpa using (map_one (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)))]
    simp
  have hcard : Fintype.card (HeadD F 0) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, ?_⟩, ?_⟩
    · change (1 : F[X]).Monic ∧ (1 : F[X]).natDegree = 0
      simp
    · intro y
      apply Subtype.ext
      exact head_zero_eq_one F y
  calc
    (∑ p : HeadD F 0, ((((p.1 : RatFunc F) : RatFunc.CompletionAtInfty F) ^ (n : ℕ))⁻¹))
        = (∑ p : HeadD F 0, (1 : RatFunc.CompletionAtInfty F)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hterm p
    _ = (Fintype.card (HeadD F 0) : RatFunc.CompletionAtInfty F) := by simp
    _ = 1 := by rw [hcard]; norm_num

/-- The level-0 depth-two blocks are empty: a degree-0 head forces its strict tail to
have negative degree. -/
lemma S_two_zero (𝔰 : Fin 2 → ℕ+) : S F 2 (by omega) 𝔰 0 = 0 := by
  classical
  let A := {a : monicStrictAntiNatDegree F 2 // a ∈ blockSet F 2 (by omega : 0 < 2) 0}
  have hBempty : ∀ a : A, False := by
    intro a
    have hdeg0 : (a.1.val ⟨0, (by omega : 0 < 2)⟩).natDegree = 0 := by
      exact a.2
    have hs := a.1.2.1
    have h01 : (⟨0, (by omega : 0 < 2)⟩ : Fin 2) < ⟨1, (by omega : 1 < 2)⟩ := by
      change (0 : ℕ) < 1
      omega
    have hlt := hs h01
    change (a.1.val ⟨1, (by omega : 1 < 2)⟩).natDegree < (a.1.val ⟨0, (by omega : 0 < 2)⟩).natDegree at hlt
    rw [hdeg0] at hlt
    omega
  haveI hfin : Finite A := by
    dsimp [A]
    exact finite_block F (by omega) 0
  letI : Fintype A := Fintype.ofFinite (α := A)
  change (∑' a : A, zetaTerm F 𝔰 a.1) = 0
  rw [tsum_fintype]
  apply Finset.sum_eq_zero
  intro a ha
  exact False.elim (hBempty a)


/-- The level-0 diagonal identity: `P_0(x)·P_0(y) = P_0(x+y) + Σ_j Δ^j·S F 2 … 0`
(the depth-two terms all vanish at level 0). -/
lemma P_zero_mul (x y : ℕ+) :
    P F 0 x * P F 0 y =
      P F 0 ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩ +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
        (ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) 0 := by
  classical
  rw [P_zero_eq_one F x, P_zero_eq_one F y,
    P_zero_eq_one F ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩]
  have hsum : (∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
      (ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
      S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [S_two_zero F (thakurExp (x : ℕ) (y : ℕ) i)]
    simp
  rw [hsum]
  simp


/-- The per-level diagonal identity: at every level ℓ (including ℓ = 0),
`P_ℓ(x)·P_ℓ(y) = P_ℓ(x+y) + Σ_j Δ^j · S F 2 (x+y−j, j) ℓ`. -/
lemma diag_level (ℓ : ℕ) (x y : ℕ+) :
    P F ℓ x * P F ℓ y =
      P F ℓ ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩ +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
        (ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) ℓ := by
  classical
  by_cases hℓ : ℓ = 0
  · subst ℓ
    exact P_zero_mul F x y
  · have hℓ1 : 1 ≤ ℓ := by omega
    exact thakur_prod_one F ℓ hℓ1 x y

/-- Expanding the equal-degree diagonal of the `S_<d` depth-1 product: the depth-1
stuffle. -/
lemma diag_stuffle (d : ℕ) (x y : ℕ+) :
    (∑ ℓ ∈ Finset.range d, S F 1 (by omega) (fun _ : Fin 1 => x) ℓ *
      S F 1 (by omega) (fun _ : Fin 1 => y) ℓ) =
      S_lt F 1 (by omega) (fun _ : Fin 1 =>
        ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
        (ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        S_lt F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) d := by
  classical
  let 𝔰x : Fin 1 → ℕ+ := fun _ => x
  let 𝔰y : Fin 1 → ℕ+ := fun _ => y
  let 𝔰xy : Fin 1 → ℕ+ := fun _ => ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩
  have hxy : (fun _ : Fin 1 => ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) = 𝔰xy := rfl
  calc
    (∑ ℓ ∈ Finset.range d, S F 1 (by omega) 𝔰x ℓ * S F 1 (by omega) 𝔰y ℓ)
        = ∑ ℓ ∈ Finset.range d, P F ℓ x * P F ℓ y := by
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          rw [S_one_eq_P F ℓ (by omega) 𝔰x, S_one_eq_P F ℓ (by omega) 𝔰y]
    _ = ∑ ℓ ∈ Finset.range d, (P F ℓ ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩ +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
            (ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) ℓ) := by
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          exact diag_level F ℓ x y
    _ = S_lt F 1 (by omega) 𝔰xy d +
        ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
          (ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
          S_lt F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) d := by
          -- split Σ_ℓ (Aℓ + Bℓ) = Σ A + Σ B
          rw [Finset.sum_add_distrib]
          -- first sum: Σ_ℓ P F ℓ⟨x+y⟩ = S_lt F 1 𝔰xy d
          have hA : (∑ ℓ ∈ Finset.range d, P F ℓ ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) =
              S_lt F 1 (by omega) 𝔰xy d := by
            calc
              (∑ ℓ ∈ Finset.range d, P F ℓ ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩)
                  = ∑ ℓ ∈ Finset.range d, S F 1 (by omega) 𝔰xy ℓ := by
                    apply Finset.sum_congr rfl
                    intro ℓ hℓ
                    exact (S_one_eq_P F ℓ (by omega) 𝔰xy).symm
              _ = S_lt F 1 (by omega) 𝔰xy d := by
                    exact (S_lt_eq_sum_levels F 1 (by omega) 𝔰xy d).symm
          rw [hA]
          -- second sum: Σ_ℓ Σ_i Δ·S F2 ℓ = Σ_i Δ·S_lt F 2 d
          have hB : (∑ ℓ ∈ Finset.range d,
                ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
                  (ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
                  S F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) ℓ) =
              ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
                (ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
                S_lt F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) d := by
            rw [Finset.sum_comm (s := (Finset.range d))
              (t := (Finset.univ : Finset {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)}))]
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.mul_sum]
            rw [← S_lt_eq_sum_levels F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) d]
          rw [hB]

/-- The depth-(1,1) `S_<d` stuffle: `S_<d(x)·S_<d(y)` expands into the two ordered
depth-two sums, the merged depth-one sum and Chen's `Δ`-combination. -/
lemma S_lt_one_stuffle (d : ℕ) (x y : ℕ+) :
    S_lt F 1 (by omega) (fun _ : Fin 1 => x) d * S_lt F 1 (by omega) (fun _ : Fin 1 => y) d =
      S_lt F 2 (by omega) (fun j : Fin 2 => if (j : ℕ) = 0 then x else y) d +
      S_lt F 2 (by omega) (fun j : Fin 2 => if (j : ℕ) = 0 then y else x) d +
      S_lt F 1 (by omega) (fun _ : Fin 1 =>
        ⟨(x : ℕ) + (y : ℕ), Nat.add_pos_left (PNat.pos x) (y : ℕ)⟩) d +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((x : ℕ) + (y : ℕ) - 1)},
        (ChenDeltaZ F (x : ℕ) (y : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        S_lt F 2 (by omega) (thakurExp (x : ℕ) (y : ℕ) i) d := by
  classical
  rw [S_lt_one_mul_one F d x y]
  rw [diag_stuffle F d x y]
  ring

/-- `P F d v * S F 2 (t1,t2) d` first shuffle step: merge `v` into `t1`, leaving the
`S_<d`-product `S_lt1[i]·S_lt1[t2]` intact. -/
lemma S_two_mul_P_first (d : ℕ) (hd : 1 ≤ d) (v t1 t2 : ℕ+) :
    P F d v * S F 2 (by omega) (fun j : Fin 2 => if (j : ℕ) = 0 then t1 else t2) d =
      S F 2 (by omega) (fun j : Fin 2 =>
        if (j : ℕ) = 0 then
          ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ else t2) d +
      ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (t1 : ℕ) - 1)},
        (ChenDeltaZ F (v : ℕ) (t1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        (P F d ⟨(v : ℕ) + (t1 : ℕ) - i.1, by
            have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
            have hin : i.1 ≤ (v : ℕ) + (t1 : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
            omega⟩ *
          S_lt F 1 (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d *
          S_lt F 1 (by omega) (fun _ : Fin 1 => t2) d) := by
  classical
  let 𝔱12 : Fin 2 → ℕ+ := fun j => if (j : ℕ) = 0 then t1 else t2
  let 𝔱m : Fin 2 → ℕ+ := fun j => if (j : ℕ) = 0 then
      ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ else t2
  let c : RatFunc.CompletionAtInfty F := S_lt F 1 (by omega) (fun _ : Fin 1 => t2) d
  have hrec12 : S F 2 (by omega) 𝔱12 d = P F d t1 * c := by
    rw [S_d_recursion F 2 (by omega) (by omega) (by omega) 𝔱12 d]
    congr 1
  have hrecM : S F 2 (by omega) 𝔱m d = P F d ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ * c := by
    rw [S_d_recursion F 2 (by omega) (by omega) (by omega) 𝔱m d]
    congr 1
  have hthak := thakur_prod_one F d hd v t1
  calc
    P F d v * S F 2 (by omega) 𝔱12 d
        = P F d v * (P F d t1 * c) := by
          rw [hrec12]
    _ = (P F d v * P F d t1) * c := by ring
    _ = (P F d ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (t1 : ℕ) - 1)},
            (ChenDeltaZ F (v : ℕ) (t1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            S F 2 (by omega) (thakurExp (v : ℕ) (t1 : ℕ) i) d) *
          c := by
          rw [← hthak]
    _ = S F 2 (by omega) 𝔱m d +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (t1 : ℕ) - 1)},
            (ChenDeltaZ F (v : ℕ) (t1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            (P F d ⟨(v : ℕ) + (t1 : ℕ) - i.1, by
                have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
                have hin : i.1 ≤ (v : ℕ) + (t1 : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
                omega⟩ *
              S_lt F 1 (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d *
              c) := by
          rw [add_mul]
          rw [Finset.sum_mul]
          rw [← hrecM]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [thakur_S_two_eq F d (v : ℕ) (t1 : ℕ) i]
          ring
    _ = S F 2 (by omega) (fun j : Fin 2 =>
          if (j : ℕ) = 0 then
            ⟨(v : ℕ) + (t1 : ℕ), Nat.add_pos_left (PNat.pos v) (t1 : ℕ)⟩ else t2) d +
          ∑ i : {i : ℕ // i ∈ Finset.Icc 1 ((v : ℕ) + (t1 : ℕ) - 1)},
            (ChenDeltaZ F (v : ℕ) (t1 : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            (P F d ⟨(v : ℕ) + (t1 : ℕ) - i.1, by
                have hi1 : 1 ≤ i.1 := (Finset.mem_Icc.mp i.2).1
                have hin : i.1 ≤ (v : ℕ) + (t1 : ℕ) - 1 := (Finset.mem_Icc.mp i.2).2
                omega⟩ *
              S_lt F 1 (by omega) (fun _ : Fin 1 => ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩) d *
              S_lt F 1 (by omega) (fun _ : Fin 1 => t2) d) := by
          congr 2

end ZagierHoffmanPositiveChar
