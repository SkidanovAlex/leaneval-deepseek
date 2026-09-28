import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.lam_basic
import Submission.Work.HP.box_card
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.FM4.card_le_ball
import Submission.Work.HP.FM4.inv_pow_le_dyadic
import Submission.Work.HP.FM4.two_pow_between

/-!
# `∑_{x ∈ Ξ_{d,n}(B)} 1/‖ν_{d,n}(x)‖ ≪ B`

Browning--Le Boudec--Sawin need the bound `Σ_{x ∈ Ξ_{d,n}(B)} ‖ν_{d,n}(x)‖^{-1} ≪ B`, where
`Ξ_{d,n}(B)` is the set of *primitive* integer vectors of norm at most `B^{1/(n+1-d)}`.

Two elementary inputs give it:

* `eNorm_veronese_bounds`: `‖ν_{d,n}(x)‖ ≫ ‖x‖^d`, so the summand is at most `C/‖x‖^d`;
* the classical dyadic shell estimate: each shell `{2^{j-1} < ‖x‖ ≤ 2^j}` contains `≪ 2^{j(n+1)}`
  lattice points and contributes `≪ 2^{j(n+1-d)}`; the geometric series converges because
  `d ≤ n`, giving `≪ X^{n+1-d}` for the ball of radius `X`.

Specialising `X = B^{1/(n+1-d)}` gives `X^{n+1-d} = B`.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.FM4

open Work.HP

/-! ## Elementary facts about `eNorm` -/

/-- The Euclidean norm of an integer vector is nonnegative. -/
lemma eNorm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℤ) : 0 ≤ eNorm v := Real.sqrt_nonneg _

/-- `IsPrim x` implies `x ≠ 0`: the zero vector has gcd `0`, not `1`. -/
lemma isPrim_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℤ} (h : IsPrim v) : v ≠ 0 := by
  rintro rfl
  have h0 : Finset.univ.gcd (0 : ι → ℤ) = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun x _ => rfl)
  have h1 : Finset.univ.gcd (0 : ι → ℤ) = 1 := h
  rw [h0] at h1
  exact one_ne_zero h1.symm

/-! ## Dyadic tools

The three statements `card_le_ball` (point count in a ball), `inv_pow_le_dyadic` (pointwise
dyadic majorant) and `two_pow_between` (dyadic rounding of a real radius) are the pieces of the
dyadic shell argument; they are proved in the sibling files imported above.
-/

/-! ## The geometric series

`∑_{j ≤ K} q^j ≤ 2 q^K` for `q ≥ 2`. -/

lemma geom_sum_le_two (q : ℝ) (hq : 2 ≤ q) : ∀ K : ℕ,
    ∑ j ∈ Finset.range (K + 1), q ^ j ≤ 2 * q ^ K
  | 0 => by simp
  | K + 1 => by
      rw [Finset.sum_range_succ]
      have ih := geom_sum_le_two q hq K
      have hq0 : (0 : ℝ) < q := by linarith
      have hqK : (0 : ℝ) < q ^ K := pow_pos hq0 K
      have h2 : 2 * q ^ K ≤ q ^ (K + 1) := by
        rw [pow_succ]; nlinarith
      calc ∑ j ∈ Finset.range (K + 1), q ^ j + q ^ (K + 1)
          ≤ 2 * q ^ K + q ^ (K + 1) := by linarith
        _ ≤ q ^ (K + 1) + q ^ (K + 1) := by linarith
        _ = 2 * q ^ (K + 1) := by ring

/-! ## The dyadic summand -/

/-- One dyadic shell contributes
`(1/2)^{jd} (3·2^j)^{n+1} = 3^{n+1} (2^{n+1-d})^j`. -/
lemma dyadic_term_eq (n d j : ℕ) (hdn : d ≤ n + 1) :
    ((1 / 2 : ℝ) ^ (j * d)) * (3 * (2 : ℝ) ^ j) ^ (n + 1)
      = (3 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (n + 1 - d)) ^ j := by
  have h1 : (3 * (2 : ℝ) ^ j) ^ (n + 1) = (3 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ j) ^ (n + 1) :=
    mul_pow 3 ((2 : ℝ) ^ j) (n + 1)
  have h2 : ((2 : ℝ) ^ j) ^ (n + 1) = (2 : ℝ) ^ (j * (n + 1)) := (pow_mul 2 j (n + 1)).symm
  have hmain : ((1 / 2 : ℝ) ^ (j * d)) * (2 : ℝ) ^ (j * (n + 1)) = (2 : ℝ) ^ (j * (n + 1 - d)) := by
    have hpos : (2 : ℝ) ^ (j * d) ≠ 0 := by positivity
    rw [one_div, inv_pow, inv_mul_eq_div, div_eq_iff hpos, ← pow_add]
    congr 1
    rw [← Nat.mul_add]
    congr 1
    omega
  calc ((1 / 2 : ℝ) ^ (j * d)) * (3 * (2 : ℝ) ^ j) ^ (n + 1)
      = ((1 / 2 : ℝ) ^ (j * d)) * ((3 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (j * (n + 1))) := by
        rw [h1, h2]
    _ = (3 : ℝ) ^ (n + 1) * (((1 / 2 : ℝ) ^ (j * d)) * (2 : ℝ) ^ (j * (n + 1))) := by ring
    _ = (3 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (j * (n + 1 - d)) := by rw [hmain]
    _ = (3 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (n + 1 - d)) ^ j := by
        rw [mul_comm j (n + 1 - d), pow_mul]

/-! ## The main dyadic estimate -/

/-- `∑_{x ∈ s} ‖x‖^{-d} ≪ (2^K)^{n+1-d}` for a finset of nonzero integer vectors of norm at
most `2^K`.  This is the classical dyadic shell estimate. -/
lemma dyadic_sum_finset (n d K : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) (s : Finset (Fin (n + 1) → ℤ))
    (hs : ∀ x ∈ s, x ≠ 0 ∧ eNorm x ≤ (2 : ℝ) ^ K) :
    ∑ x ∈ s, 1 / (eNorm x) ^ d ≤
      (2 : ℝ) ^ d * (3 : ℝ) ^ (n + 1) * 2 * ((2 : ℝ) ^ K) ^ (n + 1 - d) := by
  have hd1 : d ≤ n + 1 := by omega
  have hq2 : (2 : ℝ) ≤ (2 : ℝ) ^ (n + 1 - d) := by
    have h : 1 ≤ n + 1 - d := by omega
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ (n + 1 - d) := pow_le_pow_right₀ (by norm_num) h
  have hstep1 : ∑ x ∈ s, 1 / (eNorm x) ^ d ≤
      ∑ x ∈ s, (2 : ℝ) ^ d * ∑ j ∈ Finset.range (K + 1),
        (if eNorm x ≤ (2 : ℝ) ^ j then ((1 / 2 : ℝ) ^ (j * d)) else 0) := by
    refine Finset.sum_le_sum (fun x hx => ?_)
    exact inv_pow_le_dyadic d K hd (one_le_eNorm (hs x hx).1) (hs x hx).2
  have hstep2 : ∑ x ∈ s, (2 : ℝ) ^ d * ∑ j ∈ Finset.range (K + 1),
        (if eNorm x ≤ (2 : ℝ) ^ j then ((1 / 2 : ℝ) ^ (j * d)) else 0)
      = (2 : ℝ) ^ d * ∑ j ∈ Finset.range (K + 1),
          ((1 / 2 : ℝ) ^ (j * d)) *
            ((s.filter (fun x => eNorm x ≤ (2 : ℝ) ^ j)).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun x _ => Finset.mul_sum (Finset.range (K + 1))
      (fun j => (if eNorm x ≤ (2 : ℝ) ^ j then ((1 / 2 : ℝ) ^ (j * d)) else 0))
      ((2 : ℝ) ^ d))]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hstep3 : ∑ j ∈ Finset.range (K + 1),
        ((1 / 2 : ℝ) ^ (j * d)) * ((s.filter (fun x => eNorm x ≤ (2 : ℝ) ^ j)).card : ℝ)
      ≤ ∑ j ∈ Finset.range (K + 1), (3 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (n + 1 - d)) ^ j := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hcard : ((s.filter (fun x => eNorm x ≤ (2 : ℝ) ^ j)).card : ℝ)
        ≤ (2 * (2 : ℝ) ^ j + 1) ^ (n + 1) := by
      have h := card_le_ball ((2 : ℝ) ^ j) (by positivity)
        (s.filter (fun x => eNorm x ≤ (2 : ℝ) ^ j)) (fun v hv => (Finset.mem_filter.mp hv).2)
      simpa using h
    have hbase : 2 * (2 : ℝ) ^ j + 1 ≤ 3 * (2 : ℝ) ^ j := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := by
        simpa using pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (Nat.zero_le j)
      linarith
    calc ((1 / 2 : ℝ) ^ (j * d)) * ((s.filter (fun x => eNorm x ≤ (2 : ℝ) ^ j)).card : ℝ)
        ≤ ((1 / 2 : ℝ) ^ (j * d)) * (2 * (2 : ℝ) ^ j + 1) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left hcard (by positivity)
      _ ≤ ((1 / 2 : ℝ) ^ (j * d)) * (3 * (2 : ℝ) ^ j) ^ (n + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase (n + 1)) (by positivity)
      _ = (3 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (n + 1 - d)) ^ j := dyadic_term_eq n d j hd1
  have hstep4 : ∑ j ∈ Finset.range (K + 1), (3 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (n + 1 - d)) ^ j
      ≤ (3 : ℝ) ^ (n + 1) * (2 * ((2 : ℝ) ^ (n + 1 - d)) ^ K) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (geom_sum_le_two ((2 : ℝ) ^ (n + 1 - d)) hq2 K) (by positivity)
  have hpow : ((2 : ℝ) ^ (n + 1 - d)) ^ K = ((2 : ℝ) ^ K) ^ (n + 1 - d) := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  calc ∑ x ∈ s, 1 / (eNorm x) ^ d
      ≤ ∑ x ∈ s, (2 : ℝ) ^ d * ∑ j ∈ Finset.range (K + 1),
          (if eNorm x ≤ (2 : ℝ) ^ j then ((1 / 2 : ℝ) ^ (j * d)) else 0) := hstep1
    _ = (2 : ℝ) ^ d * ∑ j ∈ Finset.range (K + 1),
          ((1 / 2 : ℝ) ^ (j * d)) *
            ((s.filter (fun x => eNorm x ≤ (2 : ℝ) ^ j)).card : ℝ) := hstep2
    _ ≤ (2 : ℝ) ^ d * ∑ j ∈ Finset.range (K + 1),
          (3 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (n + 1 - d)) ^ j :=
        mul_le_mul_of_nonneg_left hstep3 (by positivity)
    _ ≤ (2 : ℝ) ^ d * ((3 : ℝ) ^ (n + 1) * (2 * ((2 : ℝ) ^ (n + 1 - d)) ^ K)) :=
        mul_le_mul_of_nonneg_left hstep4 (by positivity)
    _ = (2 : ℝ) ^ d * (3 : ℝ) ^ (n + 1) * 2 * ((2 : ℝ) ^ K) ^ (n + 1 - d) := by
        rw [hpow]; ring

/-! ## The Veronese reduction -/

/-- `1/‖ν_{d,n}(x)‖ ≤ C/‖x‖^d` for `x ≠ 0`, with `C` depending only on `d, n`. -/
lemma one_div_eNorm_veronese_le (d n : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Fin (n + 1) → ℤ, x ≠ 0 →
      1 / eNorm (veronese d n x) ≤ C * (1 / (eNorm x) ^ d) := by
  obtain ⟨c₁, _c₂, hc1, _hc2, hvb⟩ := eNorm_veronese_bounds d n hd
  refine ⟨1 / c₁, one_div_pos.mpr hc1, ?_⟩
  intro x hx
  have hxe : 0 < eNorm x := lt_of_lt_of_le one_pos (one_le_eNorm hx)
  have hmono : c₁ * (eNorm x) ^ d ≤ eNorm (veronese d n x) := (hvb x).1
  have hpos : 0 < c₁ * (eNorm x) ^ d := mul_pos hc1 (pow_pos hxe d)
  have h1 : 1 / eNorm (veronese d n x) ≤ 1 / (c₁ * (eNorm x) ^ d) :=
    one_div_le_one_div_of_le hpos hmono
  have h2 : (1 : ℝ) / (c₁ * (eNorm x) ^ d) = (1 / c₁) * (1 / (eNorm x) ^ d) := by
    simp only [one_div, mul_inv]
  rwa [h2] at h1

/-! ## The target -/

theorem xi_sum_vero (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ C B₀ : ℝ, 0 < C ∧ 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x)) ≤ C * B := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₁, hC1, hpt⟩ := one_div_eNorm_veronese_le d n hd1
  refine ⟨C₁ * ((2 : ℝ) ^ d * (3 : ℝ) ^ (n + 1) * 2 * (4 : ℝ) ^ (n + 1 - d)),
    1, by positivity, one_pos, ?_⟩
  intro B hB
  have hB1 : (1 : ℝ) ≤ B := hB
  have hepos : 0 < (n : ℝ) + 1 - d := by
    have : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    linarith
  set X : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hXdef
  have hX1 : 1 ≤ X := by
    rw [hXdef]
    exact Real.one_le_rpow hB1 (le_of_lt (one_div_pos.mpr hepos))
  have hXe : X ^ (n + 1 - d) = B := by
    have hdcast : ((n + 1 - d : ℕ) : ℝ) = (n : ℝ) + 1 - d := by
      rw [Nat.cast_sub (by omega : d ≤ n + 1)]
      push_cast
      ring
    rw [← Real.rpow_natCast X (n + 1 - d), hXdef,
      ← Real.rpow_mul (le_trans zero_le_one hB1) (1 / ((n : ℝ) + 1 - d))
        (((n + 1 - d : ℕ)) : ℝ),
      hdcast, one_div, inv_mul_cancel₀ (ne_of_gt hepos), Real.rpow_one]
  obtain ⟨K, hK1, hK2⟩ := two_pow_between X hX1
  have hXifin : (Xi d n B).Finite :=
    (MDBasic.finite_eNorm_le (B ^ (1 / ((n : ℝ) + 1 - d)))).subset (fun x hx => hx.2)
  have hSfin : (Xi d n B ∩
      Function.support (fun x : Fin (n + 1) → ℤ => 1 / eNorm (veronese d n x))).Finite :=
    hXifin.subset Set.inter_subset_left
  have hTfin : (({x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ (2 : ℝ) ^ K} : Set (Fin (n + 1) → ℤ)) ∩
      Function.support (fun x : Fin (n + 1) → ℤ => 1 / eNorm (veronese d n x))).Finite :=
    ((MDBasic.finite_eNorm_le ((2 : ℝ) ^ K)).subset (fun x hx => hx.2)).subset
      Set.inter_subset_left
  have hsubSet : (Xi d n B ∩
        Function.support (fun x : Fin (n + 1) → ℤ => 1 / eNorm (veronese d n x)))
      ⊆ ({x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ (2 : ℝ) ^ K} ∩
        Function.support (fun x : Fin (n + 1) → ℤ => 1 / eNorm (veronese d n x))) := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨⟨isPrim_ne_zero hx1.1, le_trans hx1.2 hK1⟩, hx2⟩
  have hsubFin : hSfin.toFinset ⊆ hTfin.toFinset :=
    (Set.Finite.toFinset_subset_toFinset).2 hsubSet
  have hball : ((2 : ℝ) ^ K) ^ (n + 1 - d) ≤ (4 : ℝ) ^ (n + 1 - d) * X ^ (n + 1 - d) := by
    calc ((2 : ℝ) ^ K) ^ (n + 1 - d) ≤ (4 * X) ^ (n + 1 - d) :=
          pow_le_pow_left₀ (by positivity) hK2 (n + 1 - d)
      _ = (4 : ℝ) ^ (n + 1 - d) * X ^ (n + 1 - d) := mul_pow 4 X (n + 1 - d)
  calc (∑ᶠ x ∈ Xi d n B, 1 / eNorm (veronese d n x))
      = ∑ x ∈ hSfin.toFinset, 1 / eNorm (veronese d n x) := by
        rw [finsum_mem_eq_sum (fun x : Fin (n + 1) → ℤ => 1 / eNorm (veronese d n x)) hSfin]
    _ ≤ ∑ x ∈ hTfin.toFinset, 1 / eNorm (veronese d n x) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubFin (fun x _ _ => ?_)
        exact div_nonneg zero_le_one (eNorm_nonneg _)
    _ ≤ ∑ x ∈ hTfin.toFinset, C₁ * (1 / (eNorm x) ^ d) := by
        refine Finset.sum_le_sum (fun x hx => ?_)
        exact hpt x ((Set.Finite.mem_toFinset hTfin).1 hx).1.1
    _ = C₁ * ∑ x ∈ hTfin.toFinset, 1 / (eNorm x) ^ d := (Finset.mul_sum _ _ _).symm
    _ ≤ C₁ * ((2 : ℝ) ^ d * (3 : ℝ) ^ (n + 1) * 2 * ((2 : ℝ) ^ K) ^ (n + 1 - d)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC1.le
        exact dyadic_sum_finset n d K hd1 hdn hTfin.toFinset
          (fun x hx => ((Set.Finite.mem_toFinset hTfin).1 hx).1)
    _ ≤ C₁ * ((2 : ℝ) ^ d * (3 : ℝ) ^ (n + 1) * 2 *
          ((4 : ℝ) ^ (n + 1 - d) * X ^ (n + 1 - d))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC1.le
        exact mul_le_mul_of_nonneg_left hball (by positivity)
    _ = (C₁ * ((2 : ℝ) ^ d * (3 : ℝ) ^ (n + 1) * 2 * (4 : ℝ) ^ (n + 1 - d))) * B := by
        rw [hXe]; ring

end Work.HP.FM4
