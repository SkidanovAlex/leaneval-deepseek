import Mathlib
import Submission.Work.HP.BCSDefs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.BCS.sRank_map_projU_add_one_le
import Submission.Work.HP.BCS.sMin_succ_le_two_mul_sMin_proj
import Submission.Work.HP.BCS.sCnt_le_proj
import Submission.Work.HP.rk_le_card

/-!
# Schmidt's bound for lattice points in a ball (`Work.HP.ball_count_schmidt`)

Main result: there is a constant `K > 0` such that for every lattice `L ⊆ ℤ^ι` and every
`T ≥ 1`,
`#{x ∈ L : ‖x‖ ≤ T} ≤ K * Σ_{i=0}^{rk L} T^{rk L - i} / (λ_1 ⋯ λ_{rk L - i})`,
where `λ_1 ≤ λ_2 ≤ ⋯` are the successive minima of `L`.

The proof is an induction on the rank of the lattice: peel off a shortest vector `u`, project
orthogonally to `u^⊥` and count the fibres (cosets of `ℤu`).  The auxiliary lattice bookkeeping
lives in `Work.HP.BCS.*`; the definitions in `Submission/Work/HP/BCSDefs.lean`.

The constant is `B ^ (card ι + 1)` with `B = 2 ^ (card ι + 4)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! Private copies of the ℤ-valued `toE` family (moved from `BCSDefs` to `BCSToE` on
2026-09-28 because `MMDefs` defines a different `Work.HP.toE`; this file sits in the import
closure of `MMDefs` users, so it cannot import `BCSToE`). -/

private def toE (v : ι → ℤ) : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => (v i : ℝ))

@[simp] private lemma toE_apply (v : ι → ℤ) (i : ι) : (toE v).ofLp i = (v i : ℝ) := rfl

private lemma toE_injective : Function.Injective (toE : (ι → ℤ) → EuclideanSpace ℝ ι) := by
  intro v w h
  ext i
  have := congrArg (fun z : EuclideanSpace ℝ ι => z.ofLp i) h
  simpa using this

private def toEHom : (ι → ℤ) →ₗ[ℤ] EuclideanSpace ℝ ι where
  toFun := toE
  map_add' v w := by ext i; simp [toE]
  map_smul' n v := by ext i; simp [toE]

@[simp] private lemma toEHom_apply (v : ι → ℤ) : toEHom v = toE v := rfl

private lemma norm_toE (v : ι → ℤ) : ‖toE v‖ = eNorm v := by
  rw [eNorm, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toE_apply, Real.norm_eq_abs, sq_abs]

/-- The constant base used in the induction. -/
def bcsB (ι : Type*) [Fintype ι] : ℝ := (2 : ℝ) ^ (Fintype.card ι + 4)

lemma one_le_bcsB (ι : Type*) [Fintype ι] : (1 : ℝ) ≤ bcsB ι :=
  one_le_pow₀ (by norm_num)

lemma bcsB_pos (ι : Type*) [Fintype ι] : (0 : ℝ) < bcsB ι :=
  lt_of_lt_of_le one_pos (one_le_bcsB ι)

/-! ## Auxiliary lemmas proved by the fleet

`Work.HP.BCSAux` collects the lemmas that the induction needs.  They are stated (and, once
available, imported) from `Submission/Work/HP/BCS/*`. -/

namespace BCSAux

/-- A nonzero lattice has a shortest vector, whose norm is `sMin Λ 1`. -/
theorem sMin_one_attained' (Λ : Submodule ℤ (EuclideanSpace ℝ ι))
    (hfin : ∀ T : ℝ, {x | x ∈ Λ ∧ ‖x‖ ≤ T}.Finite) (h : Λ ≠ ⊥) :
    ∃ u ∈ Λ, u ≠ 0 ∧ ‖u‖ = sMin Λ 1 ∧ ∀ x ∈ Λ, x ≠ 0 → ‖u‖ ≤ ‖x‖ := by
  classical
  obtain ⟨v, hvΛ, hvne⟩ := (Submodule.ne_bot_iff Λ).mp h
  have hS'fin : {x : EuclideanSpace ℝ ι | x ∈ Λ ∧ x ≠ 0 ∧ ‖x‖ ≤ ‖v‖}.Finite :=
    (hfin ‖v‖).subset (fun x hx => ⟨hx.1, hx.2.2⟩)
  have hS'ne : ({x : EuclideanSpace ℝ ι | x ∈ Λ ∧ x ≠ 0 ∧ ‖x‖ ≤ ‖v‖} : Set _).Nonempty :=
    ⟨v, hvΛ, hvne, le_refl _⟩
  obtain ⟨u, huS', hminS'⟩ :=
    Set.exists_min_image {x : EuclideanSpace ℝ ι | x ∈ Λ ∧ x ≠ 0 ∧ ‖x‖ ≤ ‖v‖}
      (fun x => ‖x‖) hS'fin hS'ne
  have huΛ : u ∈ Λ := huS'.1
  have hune : u ≠ 0 := huS'.2.1
  have hmin : ∀ x ∈ Λ, x ≠ 0 → ‖u‖ ≤ ‖x‖ := by
    intro x hxΛ hxne
    by_cases hxc : ‖x‖ ≤ ‖v‖
    · exact hminS' x ⟨hxΛ, hxne, hxc⟩
    · push Not at hxc
      exact (hminS' v ⟨hvΛ, hvne, le_refl _⟩).trans hxc.le
  refine ⟨u, huΛ, hune, ?_, hmin⟩
  have hLI : LinearIndependent ℤ (fun _ : Fin 1 => u) := by
    rw [linearIndependent_unique_iff]
    simpa using hune
  have hle1 : sMin Λ 1 ≤ ‖u‖ :=
    sMin_le (norm_nonneg u) ⟨fun _ => u, fun _ => huΛ, hLI, fun _ => le_refl _⟩
  have hB : ‖u‖ ≤ sMin Λ 1 := by
    rw [sMin_eq_sInf]
    refine le_csInf ⟨‖u‖, norm_nonneg u, fun _ => u, fun _ => huΛ, hLI,
      fun _ => le_refl _⟩ ?_
    intro r hr
    obtain ⟨hr0, f, hfΛ, hfind, hfr⟩ := hr
    exact (hmin (f 0) (hfΛ 0) (hfind.ne_zero 0)).trans (hfr 0)
  exact le_antisymm hB hle1

/-- Arithmetic comparison of the two sums in the induction step. -/
theorem sum_proj_bound' {lam mu : ℕ → ℝ} {T : ℝ} {R R' : ℕ}
    (hlampos : ∀ j, 1 ≤ j → j ≤ R + 1 → 0 < lam j)
    (hmupos : ∀ j, 1 ≤ j → j ≤ R' → 0 < mu j)
    (hT1 : 1 ≤ T) (hTlam : lam 1 ≤ T) (hR' : R' ≤ R)
    (hcmp : ∀ j, 1 ≤ j → j ≤ R' → lam (j + 1) ≤ 2 * mu j) :
    (2 * (⌈T / lam 1⌉₊ : ℝ) + 3) * (∑ i ∈ Finset.range (R' + 1), T ^ (R' - i) /
        ∏ j ∈ Finset.range (R' - i), mu (j + 1))
      ≤ (2:ℝ)^(R + 4) * (∑ i ∈ Finset.range (R + 1 + 1), T ^ (R + 1 - i) /
        ∏ j ∈ Finset.range (R + 1 - i), lam (j + 1)) := by
    have hT0 : (0:ℝ) ≤ T := le_trans zero_le_one hT1
    have hl1 : 0 < lam 1 := hlampos 1 le_rfl (by omega)
    set A : ℕ → ℝ := fun k => T ^ k / ∏ j ∈ Finset.range k, mu (j + 1) with hA
    set B : ℕ → ℝ := fun k => T ^ k / ∏ j ∈ Finset.range k, lam (j + 1) with hB
    have hSA : (∑ i ∈ Finset.range (R' + 1), T ^ (R' - i) /
        ∏ j ∈ Finset.range (R' - i), mu (j + 1)) = ∑ k ∈ Finset.range (R' + 1), A k := by
      rw [hA]
      exact Finset.sum_range_reflect (fun k => T ^ k / ∏ j ∈ Finset.range k, mu (j + 1)) (R' + 1)
    have hSB : (∑ i ∈ Finset.range (R + 1 + 1), T ^ (R + 1 - i) /
        ∏ j ∈ Finset.range (R + 1 - i), lam (j + 1)) = ∑ k ∈ Finset.range (R + 1 + 1), B k := by
      rw [hB]
      exact Finset.sum_range_reflect (fun k => T ^ k / ∏ j ∈ Finset.range k, lam (j + 1)) (R + 1 + 1)
    have hAnn : ∀ k, k ≤ R' → 0 ≤ A k := by
      intro k hk
      rw [hA]
      exact div_nonneg (pow_nonneg hT0 k) (Finset.prod_nonneg fun j hj =>
        le_of_lt (hmupos (j+1) (by omega) (by simp only [Finset.mem_range] at hj; omega)))
    have hBnn : ∀ k, k ≤ R + 1 → 0 ≤ B k := by
      intro k hk
      rw [hB]
      exact div_nonneg (pow_nonneg hT0 k) (Finset.prod_nonneg fun j hj =>
        le_of_lt (hlampos (j+1) (by omega) (by simp only [Finset.mem_range] at hj; omega)))
    have hBsucc : ∀ k ≤ R', B (k + 1) =
        T ^ (k+1) / (lam 1 * ∏ j ∈ Finset.range k, lam (j + 2)) := by
      intro k hk
      have h1 : (∏ j ∈ Finset.range (k + 1), lam (j + 1)) =
          (∏ j ∈ Finset.range k, lam (j + 2)) * lam 1 := by
        rw [Finset.prod_range_succ']
      simp only [hB]
      rw [h1, mul_comm]
    have hprod : ∀ k ≤ R',
        (∏ j ∈ Finset.range k, lam (j + 2)) ≤ 2^k * ∏ j ∈ Finset.range k, mu (j + 1) := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have hk' : k ≤ R' := by omega
        have ih' := ih hk'
        rw [Finset.prod_range_succ, Finset.prod_range_succ, pow_succ]
        have hstep : lam (k + 2) ≤ 2 * mu (k + 1) :=
          hcmp (k+1) (by omega) (by omega)
        have h1 : (∏ j ∈ Finset.range k, lam (j + 2)) * lam (k + 2) ≤
            (2^k * ∏ j ∈ Finset.range k, mu (j + 1)) * (2 * mu (k + 1)) :=
          mul_le_mul ih' hstep (le_of_lt (hlampos (k+2) (by omega) (by omega)))
            (mul_nonneg (by positivity) (Finset.prod_nonneg fun j hj =>
              le_of_lt (hmupos (j+1) (by omega)
                (by simp only [Finset.mem_range] at hj; omega))))
        calc (∏ j ∈ Finset.range k, lam (j + 2)) * lam (k + 2)
            ≤ (2^k * (∏ j ∈ Finset.range k, mu (j + 1))) * (2 * mu (k + 1)) := h1
          _ = 2 ^ (k + 1) * ((∏ j ∈ Finset.range k, mu (j + 1)) * mu (k + 1)) := by ring
    have htermA : ∀ k ≤ R', A k ≤ (2:ℝ)^k * B (k + 1) := by
      intro k hk
      have hmu_pos : 0 < ∏ j ∈ Finset.range k, mu (j + 1) :=
        Finset.prod_pos fun j hj => hmupos (j+1) (by omega) (by simp only [Finset.mem_range] at hj; omega)
      have hlam_pos : 0 < ∏ j ∈ Finset.range k, lam (j + 2) :=
        Finset.prod_pos fun j hj => hlampos (j+2) (by omega) (by simp only [Finset.mem_range] at hj; omega)
      have hDpos : (0:ℝ) < lam 1 * ∏ j ∈ Finset.range k, lam (j + 2) := mul_pos hl1 hlam_pos
      have hrhs : (2:ℝ)^k * (T ^ (k+1) / (lam 1 * ∏ j ∈ Finset.range k, lam (j + 2)))
          = (2^k * T^(k+1)) / (lam 1 * ∏ j ∈ Finset.range k, lam (j + 2)) := by ring
      rw [hA, hBsucc k hk, hrhs, div_le_div_iff₀ hmu_pos hDpos]
      have hpow : T ^ (k+1) = T^k * T := pow_succ T k
      have hk2 : (0:ℝ) ≤ (2:ℝ)^k := by positivity
      have hstepA : T^k * (lam 1 * ∏ j ∈ Finset.range k, lam (j + 2)) ≤
          T^k * (lam 1 * (2^k * ∏ j ∈ Finset.range k, mu (j + 1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hprod k hk) hl1.le) (pow_nonneg hT0 k)
      have hstepB : T^k * (lam 1 * (2^k * ∏ j ∈ Finset.range k, mu (j + 1))) ≤
          (2^k * T^(k+1)) * ∏ j ∈ Finset.range k, mu (j + 1) := by
        have h1 : T^k * lam 1 ≤ T^k * T := mul_le_mul_of_nonneg_left hTlam (pow_nonneg hT0 k)
        have h2 : (T^k * lam 1) * (2^k * ∏ j ∈ Finset.range k, mu (j + 1)) ≤
            (T^k * T) * (2^k * ∏ j ∈ Finset.range k, mu (j + 1)) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hk2 hmu_pos.le)
        rw [hpow]
        nlinarith [h2]
      linarith [hstepA, hstepB]
    have htermA2 : ∀ k ≤ R', (T / lam 1) * A k ≤ (2:ℝ)^k * B (k + 1) := by
      intro k hk
      have hmu_pos : 0 < ∏ j ∈ Finset.range k, mu (j + 1) :=
        Finset.prod_pos fun j hj => hmupos (j+1) (by omega) (by simp only [Finset.mem_range] at hj; omega)
      have hlam_pos : 0 < ∏ j ∈ Finset.range k, lam (j + 2) :=
        Finset.prod_pos fun j hj => hlampos (j+2) (by omega) (by simp only [Finset.mem_range] at hj; omega)
      have hDpos : (0:ℝ) < lam 1 * ∏ j ∈ Finset.range k, lam (j + 2) := mul_pos hl1 hlam_pos
      have h1 : T / lam 1 * A k = T^(k+1) / (lam 1 * ∏ j ∈ Finset.range k, mu (j + 1)) := by
        rw [hA, pow_succ]
        field_simp
        try ring
      have h2 : (2:ℝ)^k * B (k + 1)
          = (2^k * T^(k+1)) / (lam 1 * ∏ j ∈ Finset.range k, lam (j + 2)) := by
        rw [hBsucc k hk]
        ring
      rw [h1, h2, div_le_div_iff₀ (mul_pos hl1 hmu_pos) hDpos]
      have hk2 : (0:ℝ) ≤ (2:ℝ)^k := by positivity
      have hstepA : T^(k+1) * (lam 1 * ∏ j ∈ Finset.range k, lam (j + 2)) ≤
          T^(k+1) * (lam 1 * (2^k * ∏ j ∈ Finset.range k, mu (j + 1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hprod k hk) hl1.le) (pow_nonneg hT0 (k+1))
      have hstepB : T^(k+1) * (lam 1 * (2^k * ∏ j ∈ Finset.range k, mu (j + 1))) ≤
          (2^k * T^(k+1)) * (lam 1 * ∏ j ∈ Finset.range k, mu (j + 1)) := by
        nlinarith [mul_nonneg hk2 (mul_nonneg hl1.le hmu_pos.le), pow_nonneg hT0 (k+1)]
      linarith [hstepA, hstepB]
    have hshift0 : ∀ n : ℕ, (∑ k ∈ Finset.range n, B (k + 1)) ≤
        ∑ k' ∈ Finset.range (n + 1), B k' := by
      intro n
      induction n with
      | zero =>
        rw [Finset.sum_range_zero, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        exact hBnn 0 (by omega)
      | succ n ih =>
        have h1 : (∑ k ∈ Finset.range (n+1), B (k + 1)) =
            (∑ k ∈ Finset.range n, B (k + 1)) + B (n + 1) := Finset.sum_range_succ _ _
        have h2 : (∑ k' ∈ Finset.range (n+1+1), B k') =
            (∑ k' ∈ Finset.range (n+1), B k') + B (n + 1) := Finset.sum_range_succ _ _
        rw [h1, h2]
        linarith [ih]
    have hshift : (∑ k ∈ Finset.range (R' + 1), B (k + 1)) ≤
        ∑ k' ∈ Finset.range (R + 1 + 1), B k' := by
      refine le_trans (hshift0 (R' + 1)) ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · refine Finset.range_subset.mpr fun x hx => ?_
        simp only [Finset.mem_range] at hx ⊢
        omega
      · intro x hx1 hx2
        exact hBnn x (by simp only [Finset.mem_range] at hx1; omega)
    have hSumA : (∑ k ∈ Finset.range (R' + 1), A k) ≤
        (2:ℝ)^R' * ∑ k' ∈ Finset.range (R + 1 + 1), B k' := by
      calc (∑ k ∈ Finset.range (R' + 1), A k)
          ≤ ∑ k ∈ Finset.range (R' + 1), (2:ℝ)^k * B (k + 1) :=
            Finset.sum_le_sum fun k hk => htermA k (by simp only [Finset.mem_range] at hk; omega)
        _ ≤ ∑ k ∈ Finset.range (R' + 1), (2:ℝ)^R' * B (k + 1) :=
            Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ (by norm_num) (by simp only [Finset.mem_range] at hk; omega))
              (hBnn (k + 1) (by simp only [Finset.mem_range] at hk; omega))
        _ = (2:ℝ)^R' * ∑ k ∈ Finset.range (R' + 1), B (k + 1) := by rw [Finset.mul_sum]
        _ ≤ (2:ℝ)^R' * ∑ k' ∈ Finset.range (R + 1 + 1), B k' :=
            mul_le_mul_of_nonneg_left hshift (by positivity)
    have hSumA2 : (T / lam 1) * (∑ k ∈ Finset.range (R' + 1), A k) ≤
        (2:ℝ)^R' * ∑ k' ∈ Finset.range (R + 1 + 1), B k' := by
      calc (T / lam 1) * (∑ k ∈ Finset.range (R' + 1), A k)
          = ∑ k ∈ Finset.range (R' + 1), (T / lam 1) * A k := by rw [Finset.mul_sum]
        _ ≤ ∑ k ∈ Finset.range (R' + 1), (2:ℝ)^k * B (k + 1) :=
            Finset.sum_le_sum fun k hk => htermA2 k (by simp only [Finset.mem_range] at hk; omega)
        _ ≤ ∑ k ∈ Finset.range (R' + 1), (2:ℝ)^R' * B (k + 1) :=
            Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ (by norm_num) (by simp only [Finset.mem_range] at hk; omega))
              (hBnn (k + 1) (by simp only [Finset.mem_range] at hk; omega))
        _ = (2:ℝ)^R' * ∑ k ∈ Finset.range (R' + 1), B (k + 1) := by rw [Finset.mul_sum]
        _ ≤ (2:ℝ)^R' * ∑ k' ∈ Finset.range (R + 1 + 1), B k' :=
            mul_le_mul_of_nonneg_left hshift (by positivity)
    have hceil : 2 * (⌈T / lam 1⌉₊ : ℝ) + 3 ≤ 2 * (T / lam 1) + 5 := by
      have h1 : (⌈T / lam 1⌉₊ : ℝ) < T / lam 1 + 1 :=
        Nat.ceil_lt_add_one (div_nonneg hT0 hl1.le)
      linarith
    have h7 : (7:ℝ) * 2^R' ≤ 2^(R+4) := by
      have h16 : (7:ℝ) ≤ 16 := by norm_num
      have h1 : (7:ℝ) * 2^R' ≤ 2^4 * 2^R' := by
        nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) R']
      calc (7:ℝ) * 2^R' ≤ 2^4 * 2^R' := h1
        _ = 2^(4 + R') := by rw [pow_add]
        _ ≤ 2^(R+4) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hSBnn : 0 ≤ ∑ k' ∈ Finset.range (R + 1 + 1), B k' :=
      Finset.sum_nonneg fun k hk => hBnn k (by simp only [Finset.mem_range] at hk; omega)
    have hsumA0 : 0 ≤ ∑ k ∈ Finset.range (R' + 1), A k :=
      Finset.sum_nonneg fun k hk => hAnn k (by simp only [Finset.mem_range] at hk; omega)
    have hmain : (2 * (T / lam 1) + 5) * (∑ k ∈ Finset.range (R' + 1), A k) ≤
        (2:ℝ)^(R+4) * ∑ k' ∈ Finset.range (R + 1 + 1), B k' := by
      have h7b : 7 * ((2:ℝ)^R' * ∑ k' ∈ Finset.range (R + 1 + 1), B k') ≤
          (2:ℝ)^(R+4) * ∑ k' ∈ Finset.range (R + 1 + 1), B k' :=
        (by nlinarith [mul_le_mul_of_nonneg_right h7 hSBnn])
      have h2A : 2 * ((T / lam 1) * (∑ k ∈ Finset.range (R' + 1), A k)) ≤
          2 * ((2:ℝ)^R' * ∑ k' ∈ Finset.range (R + 1 + 1), B k') :=
        mul_le_mul_of_nonneg_left hSumA2 (by norm_num)
      have h5A : 5 * (∑ k ∈ Finset.range (R' + 1), A k) ≤
          5 * ((2:ℝ)^R' * ∑ k' ∈ Finset.range (R + 1 + 1), B k') :=
        mul_le_mul_of_nonneg_left hSumA (by norm_num)
      have hsplit : (2 * (T / lam 1) + 5) * (∑ k ∈ Finset.range (R' + 1), A k) =
          2 * ((T / lam 1) * (∑ k ∈ Finset.range (R' + 1), A k)) +
            5 * (∑ k ∈ Finset.range (R' + 1), A k) := by ring
      rw [hsplit]
      linarith [h2A, h5A, h7b]
    rw [hSA, hSB]
    exact le_trans (mul_le_mul_of_nonneg_right hceil hsumA0) hmain

end BCSAux

/-! ## Elementary consequences of the definitions -/

/-- A lattice of rank zero is trivial. -/
lemma eq_bot_of_sRank_eq_zero (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) [Module.Finite ℤ Λ]
    [Module.IsTorsionFree ℤ Λ] (h : sRank Λ = 0) : Λ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := ↥Λ)
  have hn : n = 0 := by
    have h1 : n = Module.finrank ℤ ↥Λ := by
      simpa using (Module.finrank_eq_card_basis b).symm
    rw [h1]
    exact h
  subst hn
  have hsum := congrArg (Subtype.val) (b.sum_repr (⟨x, hx⟩ : ↥Λ))
  simpa using hsum.symm

/-- A lattice of rank `≥ i` has `i` independent elements. -/
lemma sMinSet_nonempty_of_le_sRank (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) [Module.Finite ℤ Λ]
    [Module.IsTorsionFree ℤ Λ] {i : ℕ} (hi : i ≤ sRank Λ) : (sMinSet Λ i).Nonempty := by
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := ↥Λ)
  have hn : sRank Λ = n := (Module.finrank_eq_card_basis b).trans (by simp)
  rw [hn] at hi
  let g : Fin i → EuclideanSpace ℝ ι := fun k => (b (Fin.castLE hi k) : ↥Λ)
  have hg : LinearIndependent ℤ g := by
    have hli : LinearIndependent ℤ (fun k : Fin n => ((b k : ↥Λ) : EuclideanSpace ℝ ι)) :=
      b.linearIndependent.map' (Submodule.subtype Λ) (by
        rw [LinearMap.ker_eq_bot]
        exact Subtype.val_injective)
    exact hli.comp (Fin.castLE hi) (Fin.castLE_injective hi)
  refine ⟨∑ k, ‖g k‖, Finset.sum_nonneg fun k _ => norm_nonneg _, g, ?_, hg,
    fun k => Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ k)⟩
  intro k
  exact (b (Fin.castLE hi k)).2

/-- `sMin_mono` with the non-emptiness hypothesis in the form produced by
`sMinSet_nonempty_of_le_sRank`. -/
lemma sMin_le_sMin_of_nonempty {Λ : Submodule ℤ (EuclideanSpace ℝ ι)} {i j : ℕ} (hij : i ≤ j)
    (h : (sMinSet Λ j).Nonempty) : sMin Λ i ≤ sMin Λ j := by
  obtain ⟨r, -, f, hfΛ, hfind, -⟩ := h
  exact sMin_mono hij ⟨f, hfΛ, hfind⟩

/-- The successive minima are positive up to the rank. -/
lemma sMin_pos_of_le_sRank (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) [Module.Finite ℤ Λ]
    [Module.IsTorsionFree ℤ Λ] (hfin : ∀ T : ℝ, {x | x ∈ Λ ∧ ‖x‖ ≤ T}.Finite)
    (hne : Λ ≠ ⊥) {i : ℕ} (hi : 1 ≤ i) (hiR : i ≤ sRank Λ) : 0 < sMin Λ i := by
  obtain ⟨u, -, hu0, hmin_norm, hmin⟩ := BCSAux.sMin_one_attained' Λ hfin hne
  have h1 : sMin Λ 1 ≤ sMin Λ i :=
    sMin_le_sMin_of_nonempty hi (sMinSet_nonempty_of_le_sRank Λ hiR)
  rw [← hmin_norm] at h1
  exact lt_of_lt_of_le (norm_pos_iff.mpr hu0) h1

/-- Below the first successive minimum only the origin is counted. -/
lemma sCnt_eq_one_of_lt {Λ : Submodule ℤ (EuclideanSpace ℝ ι)} {u : EuclideanSpace ℝ ι}
    (huΛ : u ∈ Λ) (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖u‖ ≤ ‖x‖) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : T < ‖u‖) : sCnt Λ T = 1 := by
  have hset : {x : EuclideanSpace ℝ ι | x ∈ Λ ∧ ‖x‖ ≤ T} = {0} := by
    ext x
    constructor
    · rintro ⟨hx, hxT⟩
      by_contra hx0
      exact absurd (lt_of_lt_of_le hT (hmin x hx hx0)) (not_lt.mpr hxT)
    · rintro rfl
      exact ⟨Submodule.zero_mem _, by simpa using hT0⟩
  rw [sCnt, hset, Set.ncard_singleton]

/-- The sum in the target bound is at least `1` (the term with `i = R`). -/
lemma one_le_sum_gen (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) (R : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (1 : ℝ) ≤ ∑ i ∈ Finset.range (R + 1), T ^ (R - i) /
      ∏ j ∈ Finset.range (R - i), sMin Λ (j + 1) := by
  have hmem : R ∈ Finset.range (R + 1) := Finset.mem_range.mpr (Nat.lt_succ_self _)
  have hterm : T ^ (R - R) / ∏ j ∈ Finset.range (R - R), sMin Λ (j + 1) = 1 := by simp
  rw [← hterm]
  exact Finset.single_le_sum
    (f := fun i => T ^ (R - i) / ∏ j ∈ Finset.range (R - i), sMin Λ (j + 1))
    (fun i _ => div_nonneg (pow_nonneg hT _) (Finset.prod_nonneg fun j _ => sMin_nonneg _))
    hmem

lemma one_le_sum (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) {T : ℝ} (hT : 0 ≤ T) :
    (1 : ℝ) ≤ ∑ i ∈ Finset.range (sRank Λ + 1), T ^ (sRank Λ - i) /
      ∏ j ∈ Finset.range (sRank Λ - i), sMin Λ (j + 1) :=
  one_le_sum_gen Λ (sRank Λ) hT

/-! ## The induction -/

/-- Schmidt's bound for lattices of rank at most `R` in `ℝ^ι`. -/
theorem sCnt_bound_aux : ∀ R : ℕ, R ≤ Fintype.card ι →
    ∀ (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) (hF : Module.Finite ℤ Λ)
      (hTF : Module.IsTorsionFree ℤ Λ),
      (∀ T : ℝ, {x | x ∈ Λ ∧ ‖x‖ ≤ T}.Finite) → sRank Λ ≤ R → ∀ T : ℝ, 1 ≤ T →
      (sCnt Λ T : ℝ) ≤ bcsB ι ^ (R + 1) *
        ∑ i ∈ Finset.range (sRank Λ + 1),
          T ^ (sRank Λ - i) / ∏ j ∈ Finset.range (sRank Λ - i), sMin Λ (j + 1) := by
  intro R
  induction R with
  | zero =>
    intro hRc Λ hF hTF hfin hR T hT
    haveI := hF
    haveI := hTF
    have hbot : Λ = ⊥ := eq_bot_of_sRank_eq_zero Λ (Nat.le_zero.mp hR)
    subst hbot
    rw [sCnt_bot (le_trans zero_le_one hT)]
    have hS1 : (1 : ℝ) ≤ ∑ i ∈ Finset.range (sRank (⊥ : Submodule ℤ (EuclideanSpace ℝ ι)) + 1),
        T ^ (sRank (⊥ : Submodule ℤ (EuclideanSpace ℝ ι)) - i) /
          ∏ j ∈ Finset.range (sRank (⊥ : Submodule ℤ (EuclideanSpace ℝ ι)) - i),
            sMin (⊥ : Submodule ℤ (EuclideanSpace ℝ ι)) (j + 1) :=
      one_le_sum (⊥ : Submodule ℤ (EuclideanSpace ℝ ι)) (le_trans zero_le_one hT)
    have hB1 : (1 : ℝ) ≤ bcsB ι ^ (0 + 1) := by simpa using one_le_bcsB ι
    have hmul := mul_le_mul hB1 hS1 zero_le_one (by positivity : (0 : ℝ) ≤ bcsB ι ^ (0 + 1))
    simpa using hmul
  | succ R ih =>
    intro hRc Λ hF hTF hfin hR T hT
    haveI := hF
    haveI := hTF
    by_cases hsmall : sRank Λ ≤ R
    · have hih := ih (Nat.le_of_succ_le hRc) Λ hF hTF hfin hsmall T hT
      have hnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (sRank Λ + 1),
          T ^ (sRank Λ - i) / ∏ j ∈ Finset.range (sRank Λ - i), sMin Λ (j + 1) :=
        Finset.sum_nonneg fun i _ => div_nonneg (pow_nonneg (by linarith) _)
          (Finset.prod_nonneg fun j _ => sMin_nonneg _)
      exact hih.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (one_le_bcsB ι) (by omega)) hnn)
    · push_neg at hsmall
      have hRank : sRank Λ = R + 1 := by omega
      rw [hRank]
      have hne : Λ ≠ ⊥ := by
        intro hbot
        rw [hbot] at hRank
        have h0 : sRank (⊥ : Submodule ℤ (EuclideanSpace ℝ ι)) = 0 := by simp [sRank]
        omega
      obtain ⟨u, huΛ, hu0, hnrm, hmin⟩ := BCSAux.sMin_one_attained' Λ hfin hne
      set Λ' : Submodule ℤ (EuclideanSpace ℝ ι) := Λ.map (projUZ u) with hΛ'def
      have hproj := BCS.sCnt_le_proj ι Λ hfin huΛ hu0 hmin (le_trans zero_le_one hT)
      rw [← hΛ'def] at hproj
      have hfin' : ∀ T' : ℝ, {y | y ∈ Λ' ∧ ‖y‖ ≤ T'}.Finite := by
        intro T'
        by_cases h0 : 0 ≤ T'
        · have h := (BCS.sCnt_le_proj ι Λ hfin huΛ hu0 hmin h0).1
          rwa [← hΛ'def] at h
        · exact Set.Finite.subset Set.finite_empty (fun y hy =>
            h0 (le_trans (norm_nonneg y) hy.2))
      haveI : Module.Finite ℤ ↥Λ' := Module.Finite.map Λ (projUZ u)
      haveI : Module.IsTorsionFree ℤ ↥Λ' := inferInstance
      have hcnt : (sCnt Λ T : ℝ) ≤ (2 * (⌈T / ‖u‖⌉₊ : ℝ) + 3) * (sCnt Λ' T : ℝ) := hproj.2
      have hrank' : sRank Λ' ≤ R := by
        have h1 := BCS.sRank_map_projU_add_one_le ι Λ huΛ hu0
        rw [← hΛ'def] at h1
        omega
      have hih := ih (Nat.le_of_succ_le hRc) Λ' ‹Module.Finite ℤ ↥Λ'›
        ‹Module.IsTorsionFree ℤ ↥Λ'› hfin' hrank' T hT
      by_cases hTlt : T < ‖u‖
      · have hc1 : sCnt Λ T = 1 := sCnt_eq_one_of_lt huΛ hmin (le_trans zero_le_one hT) hTlt
        rw [hc1]
        have hS1 : (1 : ℝ) ≤ ∑ i ∈ Finset.range (R + 1 + 1), T ^ (R + 1 - i) /
            ∏ j ∈ Finset.range (R + 1 - i), sMin Λ (j + 1) :=
          one_le_sum_gen Λ (R + 1) (le_trans zero_le_one hT)
        have hB1 : (1 : ℝ) ≤ bcsB ι ^ (R + 1 + 1) := one_le_pow₀ (one_le_bcsB ι)
        have hmul := mul_le_mul hB1 hS1 zero_le_one
          (pow_nonneg (le_of_lt (bcsB_pos ι)) (R + 1 + 1))
        simpa using hmul
      · push_neg at hTlt
        set S := ∑ i ∈ Finset.range (R + 1 + 1), T ^ (R + 1 - i) /
          ∏ j ∈ Finset.range (R + 1 - i), sMin Λ (j + 1) with hS
        set S' := ∑ i ∈ Finset.range (sRank Λ' + 1), T ^ (sRank Λ' - i) /
          ∏ j ∈ Finset.range (sRank Λ' - i), sMin Λ' (j + 1) with hS'
        have hD : ∀ j, 1 ≤ j → j ≤ sRank Λ' → sMin Λ (j + 1) ≤ 2 * sMin Λ' j := by
          intro j hj1 hjR
          exact BCS.sMin_succ_le_two_mul_sMin_proj ι Λ huΛ hu0 hmin hj1
            (sMinSet_nonempty_of_le_sRank Λ' hjR)
        have hlampos : ∀ j, 1 ≤ j → j ≤ R + 1 → 0 < sMin Λ j := by
          intro j hj1 hjR
          refine sMin_pos_of_le_sRank Λ hfin hne hj1 ?_
          rw [hRank]
          exact hjR
        have hmupos : ∀ j, 1 ≤ j → j ≤ sRank Λ' → 0 < sMin Λ' j := by
          intro j hj1 hjR
          have h1 := hD j hj1 hjR
          have h2 : 0 < sMin Λ (j + 1) := hlampos (j + 1) (by omega) (by omega)
          linarith
        have harith := BCSAux.sum_proj_bound' (lam := fun j => sMin Λ j)
          (mu := fun j => sMin Λ' j) (T := T) (R := R) (R' := sRank Λ')
          hlampos hmupos hT (by rw [← hnrm]; exact hTlt) hrank' hD
        have hB : (2:ℝ) ^ (R + 4) ≤ bcsB ι := by
          rw [bcsB]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        have hSnn : (0 : ℝ) ≤ S := by
          rw [hS]
          exact Finset.sum_nonneg fun i _ => div_nonneg (pow_nonneg (by linarith) _)
            (Finset.prod_nonneg fun j _ => sMin_nonneg _)
        have h3 : bcsB ι ^ (R + 1) * (2:ℝ) ^ (R + 4) ≤ bcsB ι ^ (R + 1 + 1) := by
          have h4 := mul_le_mul_of_nonneg_left hB (pow_nonneg (le_of_lt (bcsB_pos ι)) (R + 1))
          rwa [pow_succ] at h4
        calc (sCnt Λ T : ℝ)
            ≤ (2 * (⌈T / ‖u‖⌉₊ : ℝ) + 3) * (sCnt Λ' T : ℝ) := hcnt
          _ ≤ (2 * (⌈T / ‖u‖⌉₊ : ℝ) + 3) * (bcsB ι ^ (R + 1) * S') :=
              mul_le_mul_of_nonneg_left hih
                (by have h1 : (0 : ℝ) ≤ (⌈T / ‖u‖⌉₊ : ℝ) := Nat.cast_nonneg _; linarith)
          _ = bcsB ι ^ (R + 1) * ((2 * (⌈T / ‖u‖⌉₊ : ℝ) + 3) * S') := by ring
          _ ≤ bcsB ι ^ (R + 1) * ((2:ℝ) ^ (R + 4) * S) := by
              refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (le_of_lt (bcsB_pos ι)) (R + 1))
              rw [← hnrm] at harith
              rw [← hS] at harith
              exact harith
          _ = (bcsB ι ^ (R + 1) * (2:ℝ) ^ (R + 4)) * S := by ring
          _ ≤ bcsB ι ^ (R + 1 + 1) * S := mul_le_mul_of_nonneg_right h3 hSnn

/-! ## The bridge from `L ⊆ ℤ^ι` to a lattice in `ℝ^ι` -/

/-- The rank over `ℤ` is unchanged by the embedding into Euclidean space. -/
lemma sRank_map_toEHom (L : Submodule ℤ (ι → ℤ)) : sRank (L.map toEHom) = rk L := by
  let F : ↥L →ₗ[ℤ] ↥(L.map toEHom) :=
    { toFun := fun x => ⟨toEHom x.1, Submodule.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (toEHom.map_add a.1 b.1)
      map_smul' := fun n a => Subtype.ext (toEHom.map_smul n a.1) }
  have hbij : Function.Bijective F := by
    constructor
    · intro a b h
      have h1 : toE (a : ι → ℤ) = toE (b : ι → ℤ) := congrArg Subtype.val h
      exact Subtype.ext (toE_injective h1)
    · rintro ⟨y, hy⟩
      obtain ⟨x, hxL, hxy⟩ := Submodule.mem_map.mp hy
      exact ⟨⟨x, hxL⟩, Subtype.ext hxy⟩
  show Module.finrank ℤ ↥(L.map toEHom) = Module.finrank ℤ ↥L
  rw [← LinearEquiv.finrank_eq (LinearEquiv.ofBijective F hbij)]

/-- Ball counts agree under the embedding. -/
lemma ballCount_eq_sCnt (L : Submodule ℤ (ι → ℤ)) (T : ℝ) :
    ballCount L T = sCnt (L.map toEHom) T := by
  have hset : {y : EuclideanSpace ℝ ι | y ∈ L.map toEHom ∧ ‖y‖ ≤ T} =
      toE '' {v : ι → ℤ | v ∈ L ∧ eNorm v ≤ T} := by
    ext y
    constructor
    · rintro ⟨hy, hyT⟩
      obtain ⟨v, hvL, rfl⟩ := Submodule.mem_map.mp hy
      exact ⟨v, ⟨hvL, by rw [← norm_toE v]; exact hyT⟩, rfl⟩
    · rintro ⟨v, ⟨hvL, hvT⟩, rfl⟩
      exact ⟨Submodule.mem_map.mpr ⟨v, hvL, rfl⟩, by rw [norm_toE v]; exact hvT⟩
  rw [sCnt, ballCount, hset, Set.ncard_image_of_injective _ toE_injective]

/-- Successive minima agree under the embedding. -/
lemma lam_eq_sMin (L : Submodule ℤ (ι → ℤ)) (i : ℕ) : lam L i = sMin (L.map toEHom) i := by
  unfold lam sMin
  congr 1
  ext r
  constructor
  · rintro ⟨hr0, f, hfL, hfind, hfn⟩
    exact ⟨hr0, fun k => toE (f k), fun k => Submodule.mem_map.mpr ⟨f k, hfL k, rfl⟩,
      hfind.map' toEHom (by rw [LinearMap.ker_eq_bot]; exact toE_injective),
      fun k => by rw [norm_toE]; exact hfn k⟩
  · rintro ⟨hr0, g, hgΛ, hgind, hgn⟩
    choose f hfL hfg using fun k => Submodule.mem_map.mp (hgΛ k)
    have h2 : LinearIndependent ℤ (fun k => toE (f k)) := by
      rw [show (fun k => toE (f k)) = g from funext fun k => hfg k]
      exact hgind
    have h3 : LinearIndependent ℤ f := LinearIndependent.of_comp toEHom h2
    refine ⟨hr0, f, fun k => hfL k, h3, ?_⟩
    intro k
    have hk : eNorm (f k) = ‖g k‖ := by
      rw [← norm_toE (f k)]
      exact congrArg (fun z => ‖z‖) (hfg k)
    rw [hk]
    exact hgn k

/-- The target sum rewritten in terms of the embedded lattice. -/
lemma sum_sRank_eq (L : Submodule ℤ (ι → ℤ)) (T : ℝ) :
    (∑ i ∈ Finset.range (sRank (L.map toEHom) + 1),
        T ^ (sRank (L.map toEHom) - i) /
          ∏ j ∈ Finset.range (sRank (L.map toEHom) - i), sMin (L.map toEHom) (j + 1))
      = ∑ i ∈ Finset.range (rk L + 1),
          T ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1) := by
  rw [sRank_map_toEHom L]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hprod : (∏ j ∈ Finset.range (rk L - i), sMin (L.map toEHom) (j + 1))
      = ∏ j ∈ Finset.range (rk L - i), lam L (j + 1) :=
    Finset.prod_congr rfl fun j _ => (lam_eq_sMin L (j + 1)).symm
  rw [hprod]

/-- Finiteness of the ball for the embedded lattice. -/
lemma finite_ball_map_toEHom (L : Submodule ℤ (ι → ℤ)) (T : ℝ) :
    {x : EuclideanSpace ℝ ι | x ∈ L.map toEHom ∧ ‖x‖ ≤ T}.Finite := by
  refine Set.Finite.subset ((MDBasic.finite_eNorm_le (ι := ι) T).image toE) ?_
  rintro y ⟨hy, hyT⟩
  obtain ⟨v, hvL, rfl⟩ := Submodule.mem_map.mp hy
  refine ⟨v, ?_, rfl⟩
  show eNorm v ≤ T
  rw [← norm_toE v]
  exact hyT

/-! ## The main theorem -/

theorem ball_count_schmidt (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), 1 ≤ T →
      (ballCount L T : ℝ)
        ≤ K * ∑ i ∈ Finset.range (rk L + 1),
            T ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1) := by
  classical
  refine ⟨bcsB ι ^ (Fintype.card ι + 1), pow_pos (bcsB_pos ι) _, ?_⟩
  intro L T hT
  haveI : Module.Finite ℤ ↥(L.map toEHom) := Module.Finite.map L toEHom
  haveI : Module.IsTorsionFree ℤ ↥(L.map toEHom) := inferInstance
  have haux := sCnt_bound_aux (Fintype.card ι) le_rfl (L.map toEHom)
    ‹Module.Finite ℤ ↥(L.map toEHom)› ‹Module.IsTorsionFree ℤ ↥(L.map toEHom)›
    (fun T' => finite_ball_map_toEHom L T')
    (by rw [sRank_map_toEHom L]; exact rk_le_card L) T hT
  rw [ballCount_eq_sCnt L T, ← sum_sRank_eq L T]
  exact haux

end Work.HP
