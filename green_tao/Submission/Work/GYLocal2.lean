import Submission.Work.GYLocal
import Submission.Commons.Data.Int.card_residue_window_le
import Submission.Commons.Data.Nat.card_mod_window_le

/-!
# The localisation step of Green–Tao §9, part 2: the lower bound and the bad-box count

This file continues `Submission/Work/GYLocal.lean`.  It supplies

* `box_product_ge` / `boxsump_ge_good`: the *lower* bound companions of `box_product_le` /
  `boxsump_le_good` (Green–Tao's box-average asymptotic is two-sided, and the linear forms
  condition needs both sides);
* `BadBox` and `bad_box_count`: the *bad-box count* of Green–Tao's proof of Proposition 9.8 —
  a mixed box forces the box index into a slab modulo `Q`, and the slab count is
  `O(Q^{t-1})`;
* the assembly `int_lfc_nuGT` of the reduction (`BoxAvgGood` ⟹ integer-coefficient linear
  forms condition) and the wrap-up `linFormsCond_nuGT` with the commons clearing-denominators
  lemma.
-/

open Finset
open scoped BigOperators

open Commons.NumberTheory.Sieve (LambdaR)

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace GYMaj
namespace Local

variable {m t p Q : ℕ}

/-! ## The lower bound for one box and one subset of the forms -/

/-- **One box, one subset of the forms, lower bound**: the box average of `∏_{i ∈ J} Λ_R(θ_i)²`
is at least `(1 - ε_box)(W log R/φ(W))^{|J|}` by the lower half of `BoxAvgGood`. -/
theorem box_product_ge {p Q k R W m t : ℕ} {ε_box : ℝ} {A : Fin m → Fin t → ℤ}
    {c ks : Fin m → ℤ} {u : Fin t → Fin Q} {J : Finset (Fin m)}
    (hQ : 0 < Q) (hBox : BoxAvgGood k R W ε_box) (hR1 : 1 ≤ R) (hW : 0 < W) (hε0 : 0 ≤ ε_box)
    (hε1 : ε_box ≤ 1)
    (hJ1 : 1 ≤ J.card) (hJm : J.card ≤ k * 2 ^ (k - 1)) (hm : J.card ≤ m)
    (ht1 : 0 < t) (ht2 : t ≤ 3 * k - 4)
    (hne : ∀ i ∈ J, ∃ j, A i j ≠ 0)
    (hprop : ∀ i ∈ J, ∀ i' ∈ J, i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ))
    (hAmax : ∀ i j, (A i j).natAbs ≤ k.factorial * k)
    (hside : ∀ j, (R : ℤ) ^ (10 * m) ≤ ((sideLen p Q u j : ℕ) : ℤ))
    (hpos : ∀ x ∈ boxInt p Q u, ∀ i ∈ J,
        0 < (W : ℤ) * (Lint A c x i - ks i * p) + 1) :
    (1 - ε_box)
        * ((W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ)) ^ J.card
        * (∏ j, ((sideLen p Q u j : ℕ) : ℝ))
      ≤ ∑ x ∈ boxInt p Q u,
        ∏ i ∈ J,
          (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A i j * x j) + cshift p ks c i) + 1))) ^ 2 := by
  classical
  set e := J.equivFin with he
  set A' : Fin J.card → Fin t → ℤ := fun i' j => A (e.symm i').1 j with hA'
  set b' : Fin J.card → ℤ := fun i' => cshift p ks c (e.symm i').1 with hb'
  have hcast : ∀ j, (((bhi p Q u j : ℕ) : ℤ) - ((blo p Q u j : ℕ) : ℤ)) = ((sideLen p Q u j : ℕ) : ℤ) := by
    intro j
    rw [sideLen, Nat.cast_sub (blo_le_bhi (p := p) (Q := Q) hQ (u := u) j)]
  have hboxI := boxInt_eq_Icc p Q u
  have hside' : ∀ j, (R : ℤ) ^ (10 * J.card) ≤ ((sideLen p Q u j : ℕ) : ℤ) := by
    intro j
    refine le_trans ?_ (hside j)
    refine pow_le_pow_right₀ ?_ (by omega)
    exact_mod_cast hR1
  have hneA : ∀ i' : Fin J.card, ∃ j, A' i' j ≠ 0 := by
    intro i'
    exact hne (e.symm i').1 (e.symm i').2
  have hpropA : ∀ i' i'' : Fin J.card, i' ≠ i'' → ¬ ∃ lam : ℚ, ∀ j, (A' i'' j : ℚ) = lam * (A' i' j : ℚ) := by
    intro i' i'' hne' h
    have h1 : (e.symm i').1 ≠ (e.symm i'').1 := by
      intro hh
      exact hne' (e.symm.injective (Subtype.ext hh))
    exact hprop (e.symm i').1 (e.symm i').2 (e.symm i'').1 (e.symm i'').2 h1 h
  have hsideA : ∀ j, (R : ℤ) ^ (10 * J.card)
      ≤ (((bhi p Q u j : ℕ) : ℤ)) - (((blo p Q u j : ℕ) : ℤ)) := by
    intro j
    have h1 := hside' j
    have h2 := hcast j
    rw [h2]
    exact h1
  have hposA : ∀ x ∈ Fintype.piFinset
        (fun j => Finset.Icc (((blo p Q u j : ℕ) : ℤ)) ((((bhi p Q u j : ℕ) : ℤ)) - 1)),
      ∀ i' : Fin J.card, 0 < (W : ℤ) * ((∑ j, A' i' j * x j) + b' i') + 1 := by
    intro x hx i'
    rw [← hboxI] at hx
    have h := hpos x hx (e.symm i').1 (e.symm i').2
    have hident : (W : ℤ) * ((∑ j, A' i' j * x j) + b' i') + 1
        = (W : ℤ) * (Lint A c x (e.symm i').1 - ks (e.symm i').1 * p) + 1 := by
      simp only [hA', hb', Lint, cshift]
      ring
    rw [hident]
    exact h
  have happ := hBox J.card t A' b'
    (fun j => (((blo p Q u j : ℕ) : ℤ))) (fun j => (((bhi p Q u j : ℕ) : ℤ)))
    hJ1 hJm ht1 ht2 hneA hpropA (fun i' j => hAmax (e.symm i').1 j) hsideA hposA
  have hsummand : ∀ x : Fin t → ℤ,
      (∏ i : Fin J.card,
          (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A' i j * x j) + b' i) + 1))) ^ 2)
        = ∏ i ∈ J,
          (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A i j * x j) + cshift p ks c i) + 1))) ^ 2 := by
    intro x
    rw [prod_subset_eq J (fun i =>
      (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A i j * x j) + cshift p ks c i) + 1))) ^ 2)]
  have hSPeq : (∏ j, (((((bhi p Q u j : ℕ) : ℤ)) - (((blo p Q u j : ℕ) : ℤ)) : ℤ) : ℝ))
      = (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) := by
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [hcast j]
    norm_num
  have hSeq : (∑ x ∈ Fintype.piFinset
        (fun j => Finset.Icc (((blo p Q u j : ℕ) : ℤ)) ((((bhi p Q u j : ℕ) : ℤ)) - 1)),
        ∏ i : Fin J.card,
          (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A' i j * x j) + b' i) + 1))) ^ 2)
      = ∑ x ∈ boxInt p Q u,
          ∏ i ∈ J,
            (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A i j * x j) + cshift p ks c i) + 1))) ^ 2 := by
    rw [hboxI]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact hsummand x
  rw [hSPeq, hSeq] at happ
  have happ' := happ
  have hprodpos : 0 < ∏ j, ((sideLen p Q u j : ℕ) : ℝ) := by
    refine Finset.prod_pos (fun j _ => ?_)
    have h1 : (1 : ℤ) ≤ ((sideLen p Q u j : ℕ) : ℤ) := by
      have h3 : (1:ℤ) ≤ (R : ℤ) := by exact_mod_cast hR1
      have h2 : (1 : ℤ) ≤ (R : ℤ) ^ (10 * J.card) := one_le_pow₀ h3
      linarith [hside' j]
    exact_mod_cast h1
  have h2 := (abs_le.mp happ').1
  have h2' := mul_le_mul_of_nonneg_left h2 (le_of_lt hprodpos)
  rw [mul_sub, mul_inv_cancel_left₀ (ne_of_gt hprodpos)] at h2'
  -- h2' : -(∏ sideLen * (ε_box * X^J)) ≤ ∑ - ∏ sideLen * X^J
  set X : ℝ := (W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ) with hX
  have hstep : (1 - ε_box) * ((∏ j, ((sideLen p Q u j : ℕ) : ℝ)) * X ^ J.card)
      ≤ ∑ x ∈ boxInt p Q u,
          ∏ i ∈ J,
            (LambdaR R (Int.toNat ((W : ℤ) * ((∑ j, A i j * x j) + cshift p ks c i) + 1))) ^ 2 := by
    nlinarith [h2']
  calc (1 - ε_box) * X ^ J.card * (∏ j, ((sideLen p Q u j : ℕ) : ℝ))
      = (1 - ε_box) * ((∏ j, ((sideLen p Q u j : ℕ) : ℝ)) * X ^ J.card) := by ring
    _ ≤ _ := hstep


/-! ## The lower bound for a good box -/

/-- **The sharp lower bound for a *good* box**: if the indices outside `S` are all completely out
of the window and those inside `S` are all completely in it, then the box sum is at least
`(1 - ε_box)^{|S|}` times the volume. -/
theorem boxsump_ge_good {p Q k R W m t : ℕ} [NeZero p] {ε_box εw : ℝ} {A : Fin m → Fin t → ℤ}
    {c ks : Fin m → ℤ} {u : Fin t → Fin Q} (S : Finset (Fin m))
    (hQ : 0 < Q) (hR1 : 1 ≤ R) (hR : 1 < R) (hW : 0 < W) (hε0 : 0 ≤ ε_box) (hε1 : ε_box ≤ 1)
    (hBox : BoxAvgGood k R W ε_box)
    (hm : m ≤ k * 2 ^ (k - 1)) (ht1 : 0 < t) (ht2 : t ≤ 3 * k - 4)
    (hne : ∀ i ∈ S, ∃ j, A i j ≠ 0)
    (hprop : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ))
    (hAmax : ∀ i j, (A i j).natAbs ≤ k.factorial * k)
    (hside : ∀ j, (R : ℤ) ^ (10 * m) ≤ ((sideLen p Q u j : ℕ) : ℤ))
    (hSout : ∀ i, i ∉ S → AllOut p A c εw u i)
    (hSin : ∀ i ∈ S, ∀ x ∈ boxInt p Q u, Clip εw p (((psi p A c x i).val : ℝ)))
    (hstab : ∀ i ∈ S, StableAt p Q A c u i (ks i))
    (hpos : ∀ x ∈ boxInt p Q u, ∀ i ∈ S,
        0 < (W : ℤ) * (Lint A c x i - ks i * p) + 1) :
    (1 - ε_box) ^ S.card * (∏ j, ((sideLen p Q u j : ℕ) : ℝ))
      ≤ boxsump p Q R W εw A c u := by
  classical
  set X : ℝ := (W : ℝ) * Real.log (R : ℝ) / (Nat.totient W : ℝ) with hX
  have hXnn : 0 ≤ X := hX ▸ div_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by exact_mod_cast hR1))) (Nat.cast_nonneg _)
  have hprod : ∀ x ∈ boxInt p Q u, ∏ i, GYMaj.nuGT R W p εw (psi p A c x i)
      = ∏ i ∈ S, c0 R W * (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 := by
    intro x hx
    have h1 : (∏ i : Fin m, GYMaj.nuGT R W p εw (psi p A c x i))
        = ∏ i ∈ S, GYMaj.nuGT R W p εw (psi p A c x i) := by
      rw [Finset.prod_subset (s₁ := S) (s₂ := Finset.univ)
        (f := fun i => GYMaj.nuGT R W p εw (psi p A c x i)) (Finset.subset_univ S)
        (fun i _ hi => nuGT_psi_eq_one_of_notClip' (hSout i hi x hx))]
    rw [h1]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hv : ((psi p A c x i).val : ℝ) = ((Lint A c x i - ks i * p : ℤ) : ℝ) := by
      rw [psi_val_of_stable (hstab i hi) hx]
      exact_mod_cast (Int.toNat_of_nonneg (by linarith [((hstab i hi) x hx).1]))
    exact nuGT_psi_eq_of_clip hW hR (hstab i hi) hx (hv ▸ hSin i hi x hx)
  rw [boxsump]
  rw [Finset.sum_congr rfl hprod]
  have hsplit : ∀ x : Fin t → ℤ,
      (∏ i ∈ S, c0 R W *
          (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2)
        = c0 R W ^ S.card * ∏ i ∈ S,
            (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hcard : S.card ≤ m := by
    have h := Finset.card_le_univ S
    simpa using h
  by_cases hS0 : S.card = 0
  · have hSe : S = ∅ := Finset.card_eq_zero.mp hS0
    subst hSe
    simp only [Finset.card_empty, pow_zero, one_mul, Finset.prod_empty, Finset.sum_const,
      nsmul_eq_mul]
    rw [card_boxInt hQ, Nat.cast_prod]
    simp
  · have hS1 : 1 ≤ S.card := by omega
    have hSm : S.card ≤ k * 2 ^ (k - 1) := le_trans hcard hm
    have hb := box_product_ge (p := p) (Q := Q) (k := k) (R := R) (W := W) (m := m) (t := t)
      (ε_box := ε_box) (A := A) (c := c) (ks := ks) (u := u) (J := S)
      hQ hBox hR1 hW hε0 hε1 hS1 hSm hcard ht1 ht2 hne hprop hAmax hside hpos
    have hcx : c0 R W ^ S.card * X ^ S.card = 1 := by
      rw [← mul_pow, c0_mul_eq_one hW hR, one_pow]
    have h2 : (∑ x ∈ boxInt p Q u, ∏ i ∈ S,
          c0 R W * (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2)
        = c0 R W ^ S.card * ∑ x ∈ boxInt p Q u, ∏ i ∈ S,
            (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      exact hsplit x
    rw [h2]
    have hbase : 0 ≤ 1 - ε_box := by linarith
    have hone : (1 - ε_box) ≤ 1 := by linarith
    have hpow : (1 - ε_box) ^ S.card ≤ (1 - ε_box) := by
      calc (1 - ε_box) ^ S.card ≤ (1 - ε_box) ^ 1 :=
            pow_le_pow_of_le_one hbase hone hS1
        _ = (1 - ε_box) := pow_one _
    have hvol : 0 ≤ (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) := by positivity
    calc (1 - ε_box) ^ S.card * (∏ j, ((sideLen p Q u j : ℕ) : ℝ))
        ≤ (1 - ε_box) * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hpow hvol
      _ = c0 R W ^ S.card
            * ((1 - ε_box) * X ^ S.card * (∏ j, ((sideLen p Q u j : ℕ) : ℝ))) := by
          rw [show c0 R W ^ S.card * ((1 - ε_box) * X ^ S.card * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)))
              = (1 - ε_box) * (c0 R W ^ S.card * X ^ S.card)
                * (∏ j, ((sideLen p Q u j : ℕ) : ℝ)) by ring, hcx]
          ring
      _ ≤ c0 R W ^ S.card * (∑ x ∈ boxInt p Q u, ∏ i ∈ S,
            (LambdaR R (Int.toNat (BoxAvg.theta W A (cshift p ks c) x i))) ^ 2) :=
          mul_le_mul_of_nonneg_left hb (pow_nonneg (c0_nonneg hR) _)

/-! ## Step B: the bad-box count -/

/-- **The left-corner modular identity.**  Multiplying the value of `Lint` at the left corner of a
box by `Q` splits the box index: `Q · Lint(corner) = p · Σ(u) + Q c_i - Σ_j A_ij r_j`, where
`r_j = (u_j p) mod Q` is the remainder of the box corner. -/
lemma corner_mod_identity {p Q : ℕ} (hQ : 0 < Q) {m t : ℕ} (A : Fin m → Fin t → ℤ)
    (c : Fin m → ℤ) (u : Fin t → Fin Q) (i : Fin m) :
    (Q : ℤ) * Lint A c (corner p Q u) i
      = (p : ℤ) * (∑ j, A i j * ((u j).val : ℤ)) + (Q : ℤ) * c i
        - ∑ j, A i j * ((((u j).val * p) % Q : ℕ) : ℤ) := by
  have hqr : ∀ j, ((u j).val : ℤ) * (p : ℤ)
      = (Q : ℤ) * ((blo p Q u j : ℕ) : ℤ) + ((((u j).val * p) % Q : ℕ) : ℤ) := by
    intro j
    have h := Nat.div_add_mod ((u j).val * p) Q
    have h' : ((u j).val * p : ℕ) = ((u j).val * p / Q) * Q + (u j).val * p % Q := by
      rw [Nat.mul_comm] at h; exact h.symm
    have h2 : (((u j).val * p : ℕ) : ℤ)
        = (((u j).val * p / Q : ℕ) : ℤ) * (Q : ℤ) + ((((u j).val * p) % Q : ℕ) : ℤ) := by
      have h'' : (((u j).val * p : ℕ) : ℤ)
          = ((((u j).val * p / Q) * Q + (u j).val * p % Q : ℕ) : ℤ) := by
        conv_lhs => rw [h']
      rw [h'', Nat.cast_add, Nat.cast_mul]
    have h3 : (((u j).val * p : ℕ) : ℤ) = ((u j).val : ℤ) * (p : ℤ) := by push_cast; ring
    rw [h3] at h2
    rw [h2, blo]; ring
  have hL : Lint A c (corner p Q u) i = ∑ j, A i j * ((blo p Q u j : ℕ) : ℤ) + c i := by
    simp only [Lint, corner]
  have hterm : ∀ j, (Q : ℤ) * (A i j * ((blo p Q u j : ℕ) : ℤ))
      = (p : ℤ) * (A i j * ((u j).val : ℤ)) - A i j * ((((u j).val * p) % Q : ℕ) : ℤ) := by
    intro j
    have h := hqr j
    have key : (Q : ℤ) * ((blo p Q u j : ℕ) : ℤ)
        = ((u j).val : ℤ) * (p : ℤ) - ((((u j).val * p) % Q : ℕ) : ℤ) := by
      linarith [h]
    calc (Q : ℤ) * (A i j * ((blo p Q u j : ℕ) : ℤ))
        = A i j * ((Q : ℤ) * ((blo p Q u j : ℕ) : ℤ)) := by ring
      _ = A i j * (((u j).val : ℤ) * (p : ℤ) - ((((u j).val * p) % Q : ℕ) : ℤ)) := by
            rw [key]
      _ = (p : ℤ) * (A i j * ((u j).val : ℤ))
            - A i j * ((((u j).val * p) % Q : ℕ) : ℤ) := by ring
  rw [hL, mul_add, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **Transport of the near-boundary condition to a slab condition on the box index.**  If the
value of the form at the left corner of the box is within `2Δ` of `α` (after subtracting the
shift), then the box index `Σ(u) = ∑_j A_ij u_j` lies within `K` of `(Q/p)(α - c_i)` modulo `Q`,
with `K = (2Δ + t·Amax)·Q/p`. -/
theorem corner_mod_transport {p Q : ℕ} (hQ : 0 < Q) (hp : 0 < p) {m t : ℕ}
    (A : Fin m → Fin t → ℤ) (c : Fin m → ℤ) (u : Fin t → Fin Q) (i : Fin m)
    {α : ℝ} {ks : ℤ} {Δ : ℤ} {Amax : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ Amax)
    (h : |(((Lint A c (corner p Q u) i - ks * (p : ℤ) : ℤ)) : ℝ) - α| ≤ 2 * (Δ : ℝ)) :
    ∃ z : ℤ, |((∑ j, A i j * ((u j).val : ℤ) : ℤ) : ℝ) - (z : ℝ) * (Q : ℝ)
        - ((Q : ℝ) / (p : ℝ) * (α - (c i : ℝ)))|
      ≤ (2 * (Δ : ℝ) + (t : ℝ) * (Amax : ℝ)) * (Q : ℝ) / (p : ℝ) := by
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  set S : ℤ := ∑ j, A i j * ((u j).val : ℤ) with hS
  set Rr : ℤ := ∑ j, A i j * ((((u j).val * p) % Q : ℕ) : ℤ) with hRrdef
  have hkey : (Q : ℤ) * Lint A c (corner p Q u) i
      = (p : ℤ) * S + (Q : ℤ) * c i - Rr := by
    rw [corner_mod_identity hQ A c u i, hS, hRrdef]
  have hRr : |Rr| ≤ (t : ℤ) * (Amax : ℤ) * (Q : ℤ) := by
    calc |Rr| ≤ ∑ j, |A i j * ((((u j).val * p) % Q : ℕ) : ℤ)| := by
          rw [hRrdef]; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin t, (Amax : ℤ) * (Q : ℤ) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          rw [abs_mul]
          have h1 : |A i j| ≤ (Amax : ℤ) := by
            have hh := hA i j
            have h2 : (((A i j).natAbs : ℕ) : ℤ) ≤ (Amax : ℤ) := by exact_mod_cast hh
            rwa [Int.natCast_natAbs] at h2
          have h5 : (0 : ℤ) ≤ ((((u j).val * p) % Q : ℕ) : ℤ) := Int.natCast_nonneg _
          have h3 : |((((u j).val * p) % Q : ℕ) : ℤ)| ≤ (Q : ℤ) := by
            have h4 : ((u j).val * p) % Q < Q := Nat.mod_lt _ hQ
            rw [abs_of_nonneg h5]
            exact_mod_cast Nat.le_of_lt h4
          exact mul_le_mul h1 h3 (abs_nonneg _) (Int.natCast_nonneg _)
      _ = (t : ℤ) * (Amax : ℤ) * (Q : ℤ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hcast : (p : ℝ) * (S : ℝ)
      = (Q : ℝ) * ((Lint A c (corner p Q u) i : ℤ) : ℝ) - (Q : ℝ) * ((c i : ℤ) : ℝ)
        + (Rr : ℝ) := by
    have h2 := congrArg (fun x : ℤ => (x : ℝ)) hkey
    push_cast at h2
    linarith [h2]
  have hpθ : (p : ℝ) * ((Q : ℝ) / (p : ℝ) * (α - ((c i : ℤ) : ℝ)))
      = (Q : ℝ) * (α - ((c i : ℤ) : ℝ)) := by
    field_simp
  have hid : (p : ℝ) * ((S : ℝ) - (ks : ℝ) * (Q : ℝ)
        - ((Q : ℝ) / (p : ℝ) * (α - ((c i : ℤ) : ℝ))))
      = (Q : ℝ) * ((((Lint A c (corner p Q u) i : ℤ) : ℝ) - (ks : ℝ) * (p : ℝ)) - α)
        + (Rr : ℝ) := by
    rw [show (p : ℝ) * ((S : ℝ) - (ks : ℝ) * (Q : ℝ)
          - ((Q : ℝ) / (p : ℝ) * (α - ((c i : ℤ) : ℝ))))
        = (p : ℝ) * (S : ℝ) - (p : ℝ) * ((ks : ℝ) * (Q : ℝ))
          - (p : ℝ) * ((Q : ℝ) / (p : ℝ) * (α - ((c i : ℤ) : ℝ))) by ring, hcast, hpθ]
    ring
  refine ⟨ks, ?_⟩
  have hLHS : |(p : ℝ) * ((S : ℝ) - (ks : ℝ) * (Q : ℝ)
        - ((Q : ℝ) / (p : ℝ) * (α - ((c i : ℤ) : ℝ))))|
      ≤ (2 * (Δ : ℝ) + (t : ℝ) * (Amax : ℝ)) * (Q : ℝ) := by
    rw [hid]
    have hRrR : |(Rr : ℝ)| ≤ (t : ℝ) * (Amax : ℝ) * (Q : ℝ) := by
      calc |(Rr : ℝ)| = (((|Rr| : ℤ)) : ℝ) := by rw [Int.cast_abs]
        _ ≤ (((t : ℤ) * (Amax : ℤ) * (Q : ℤ) : ℤ) : ℝ) := by exact_mod_cast hRr
        _ = (t : ℝ) * (Amax : ℝ) * (Q : ℝ) := by push_cast; ring
    calc |(Q : ℝ) * ((((Lint A c (corner p Q u) i : ℤ) : ℝ) - (ks : ℝ) * (p : ℝ)) - α)
          + (Rr : ℝ)|
        ≤ |(Q : ℝ) * ((((Lint A c (corner p Q u) i : ℤ) : ℝ) - (ks : ℝ) * (p : ℝ)) - α)|
          + |(Rr : ℝ)| := abs_add_le _ _
      _ ≤ (Q : ℝ) * (2 * (Δ : ℝ)) + (t : ℝ) * (Amax : ℝ) * (Q : ℝ) := by
          refine add_le_add ?_ hRrR
          rw [abs_mul, abs_of_nonneg (le_of_lt hQR)]
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hQR)
          have hh : |(((Lint A c (corner p Q u) i : ℤ) : ℝ) - (ks : ℝ) * (p : ℝ)) - α|
              ≤ 2 * (Δ : ℝ) := by
            convert h using 2
            push_cast
            ring
          exact hh
      _ = (2 * (Δ : ℝ) + (t : ℝ) * (Amax : ℝ)) * (Q : ℝ) := by ring
  have hfin : |(S : ℝ) - (ks : ℝ) * (Q : ℝ)
        - ((Q : ℝ) / (p : ℝ) * (α - ((c i : ℤ) : ℝ)))|
      ≤ (2 * (Δ : ℝ) + (t : ℝ) * (Amax : ℝ)) * (Q : ℝ) / (p : ℝ) := by
    rw [le_div_iff₀ hpR]
    have habs : |(S : ℝ) - (ks : ℝ) * (Q : ℝ)
          - ((Q : ℝ) / (p : ℝ) * (α - ((c i : ℤ) : ℝ)))| * (p : ℝ)
        = |(p : ℝ) * ((S : ℝ) - (ks : ℝ) * (Q : ℝ)
          - ((Q : ℝ) / (p : ℝ) * (α - ((c i : ℤ) : ℝ))))| := by
      rw [abs_mul, abs_of_pos hpR]
      ring
    rw [habs]
    exact hLHS
  have hgoal : |((∑ j, A i j * ((u j).val : ℤ) : ℤ) : ℝ) - (ks : ℝ) * (Q : ℝ)
        - ((Q : ℝ) / (p : ℝ) * (α - ((c i : ℤ) : ℝ)))|
      = |(S : ℝ) - (ks : ℝ) * (Q : ℝ) - ((Q : ℝ) / (p : ℝ) * (α - ((c i : ℤ) : ℝ)))| := by
    rw [hS]
  rw [hgoal]
  exact hfin

/-- **Counting the residues in a window, without normalising `θ`.**  The number of integers
`r ∈ [0,Q)` with `dist(r - θ, Qℤ) ≤ K` is at most `⌈2K⌉₊ + 1`, for *any* real `θ`.  (The condition
only depends on `θ mod Q`, and shifting `θ` by a multiple of `Q` is absorbed by the multiplier.) -/
lemma card_residue_window_le_gen {Q : ℕ} (hQ : 0 < Q) (θ K : ℝ) (hK : 0 ≤ K) :
    Set.ncard {r : ℤ | 0 ≤ r ∧ r < (Q : ℤ) ∧
        ∃ z : ℤ, |(r : ℝ) - θ - (z : ℝ) * (Q : ℝ)| ≤ K} ≤ ⌈2 * K⌉₊ + 1 := by
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  set m : ℤ := ⌊θ / (Q : ℝ)⌋ with hm
  set θ' : ℝ := θ - (m : ℝ) * (Q : ℝ) with hθ'
  have hθ0 : 0 ≤ θ' := by
    have h1 : (m : ℝ) * (Q : ℝ) ≤ θ := by
      have h := Int.floor_le (θ / (Q : ℝ))
      rw [← hm] at h
      rw [le_div_iff₀ hQR] at h
      linarith [h]
    rw [hθ']; linarith
  have hθQ : θ' < (Q : ℝ) := by
    have h1 : θ < ((m : ℝ) + 1) * (Q : ℝ) := by
      have h := Int.lt_floor_add_one (θ / (Q : ℝ))
      rw [← hm] at h
      rw [div_lt_iff₀ hQR] at h
      linarith [h]
    rw [hθ']; linarith
  have hset : {r : ℤ | 0 ≤ r ∧ r < (Q : ℤ) ∧
        ∃ z : ℤ, |(r : ℝ) - θ - (z : ℝ) * (Q : ℝ)| ≤ K}
      = {r : ℤ | 0 ≤ r ∧ r < (Q : ℤ) ∧
        ∃ z : ℤ, |(r : ℝ) - θ' - (z : ℝ) * (Q : ℝ)| ≤ K} := by
    ext r
    constructor
    · rintro ⟨h1, h2, z, hz⟩
      refine ⟨h1, h2, z + m, ?_⟩
      have heq : (r : ℝ) - θ' - ((z + m : ℤ) : ℝ) * (Q : ℝ)
          = (r : ℝ) - θ - (z : ℝ) * (Q : ℝ) := by
        rw [hθ']; push_cast; ring
      rwa [heq]
    · rintro ⟨h1, h2, z, hz⟩
      refine ⟨h1, h2, z - m, ?_⟩
      have heq : (r : ℝ) - θ - ((z - m : ℤ) : ℝ) * (Q : ℝ)
          = (r : ℝ) - θ' - (z : ℝ) * (Q : ℝ) := by
        rw [hθ']; push_cast; ring
      rwa [heq]
  rw [hset]
  exact Commons.Data.Int.card_residue_window_le hQ hθ0 hθQ hK

/-- **The constant `K` of the slab condition** in the bad-box count:
`K = (2Δ + t·Amax)·Q/p`. -/
noncomputable def Kbad (p Q : ℕ) (Δ : ℤ) (Amax t : ℕ) : ℝ :=
  (2 * (Δ : ℝ) + (t : ℝ) * (Amax : ℝ)) * (Q : ℝ) / (p : ℝ)

/-- A box `u` is **bad** (for the system `(A,c)`) if for some index `i` it is neither completely
outside the window nor completely inside it. -/
def AllBad (p Q : ℕ) (εw : ℝ) {m t : ℕ} (A : Fin m → Fin t → ℤ) (c : Fin m → ℤ)
    (u : Fin t → Fin Q) : Prop :=
  ∃ i, ¬ AllOut p A c εw u i ∧ ¬ AllIn p A c εw u i

/-- **The range bound on a box**, isolated from `boxShift_spec`. -/
lemma range_le_of_bounds {p Q : ℕ} {m t : ℕ} (hQ : 0 < Q) {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ}
    {u : Fin t → Fin Q} {i : Fin m} {Amax : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ Amax)
    {D Δ : ℤ} (hD : ∀ (u : Fin t → Fin Q) (j : Fin t), ((sideLen p Q u j : ℕ) : ℤ) ≤ D)
    (hD0 : 0 ≤ D) (hΔ : (t : ℤ) * (Amax : ℤ) * D ≤ Δ) :
    ∀ x ∈ boxInt p Q u, ∀ y ∈ boxInt p Q u, |Lint A c x i - Lint A c y i| ≤ Δ := by
  intro x hx y hy
  refine le_trans (abs_Lint_sub_le (p := p) (Q := Q) hQ hx hy i) ?_
  have h1 : ∀ j : Fin t, |A i j| * ((sideLen p Q u j : ℕ) : ℤ) ≤ (Amax : ℤ) * D := by
    intro j
    have h2 : |A i j| ≤ (Amax : ℤ) := by
      have h := hA i j
      have h' : (((A i j).natAbs : ℕ) : ℤ) ≤ (Amax : ℤ) := by exact_mod_cast h
      rwa [Int.natCast_natAbs] at h'
    have h3 : ((sideLen p Q u j : ℕ) : ℤ) ≤ D := hD u j
    have h4 : (0 : ℤ) ≤ ((sideLen p Q u j : ℕ) : ℤ) := Int.natCast_nonneg _
    have h5 : (0 : ℤ) ≤ |A i j| := abs_nonneg _
    nlinarith [h2, h3, h4, h5, hD0]
  calc ∑ j, |A i j| * ((sideLen p Q u j : ℕ) : ℤ)
      ≤ ∑ _j : Fin t, ((Amax : ℤ) * D) := Finset.sum_le_sum (fun j _ => h1 j)
    _ = (t : ℤ) * ((Amax : ℤ) * D) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (t : ℤ) * (Amax : ℤ) * D := by ring
    _ ≤ Δ := hΔ


open Classical in
/-- The **slab** of box indices: those `u` whose linear-form value `Σ(u) = ∑_j A_ij u_j` lies within
`Kbad` of `(Q/p)(α - c_i)` modulo `Q`.  These are the boxes that can be bad for the form `i` at
window boundary `α`. -/
noncomputable def Slab (p Q : ℕ) (Δ : ℤ) (Amax t : ℕ) {m : ℕ} (A : Fin m → Fin t → ℤ)
    (c : Fin m → ℤ) (i : Fin m) (α : ℝ) : Finset (Fin t → Fin Q) :=
  Finset.univ.filter (fun u : Fin t → Fin Q => ∃ z : ℤ,
    |((∑ j, A i j * ((u j).val : ℤ) : ℤ) : ℝ) - (z : ℝ) * (Q : ℝ)
      - ((Q : ℝ) / (p : ℝ) * (α - (c i : ℝ)))| ≤ Kbad p Q Δ Amax t)

/-- **The bad-box count (Green–Tao's proof of Proposition 9.8).**  The number of boxes which are
neither completely inside nor completely outside the window for some form is `O(Q^{t-1})`: such a
box forces its index into one of the `2m` slabs. -/
theorem bad_box_count {p Q : ℕ} [NeZero p] {m t : ℕ} (A : Fin m → Fin t → ℤ) (c : Fin m → ℤ)
    (hQ : 0 < Q) (hQp : Q ≤ p) {εw : ℝ} (hεw : 0 < εw) {Amax : ℕ}
    (hA : ∀ i j, (A i j).natAbs ≤ Amax) (hne : ∀ i, ∃ j, A i j ≠ 0)
    {Kout : ℤ} {Δ D : ℤ}
    (hD : ∀ (u : Fin t → Fin Q) (j : Fin t), ((sideLen p Q u j : ℕ) : ℤ) ≤ D)
    (hD0 : 0 ≤ D) (hΔ : (t : ℤ) * (Amax : ℤ) * D ≤ Δ) (hΔε : (Δ : ℝ) ≤ εw * (p : ℝ))
    (hΔp : (Δ : ℝ) + 2 * εw * (p : ℝ) < (p : ℝ)) (hc : ∀ i, (c i).natAbs ≤ (p : ℤ))
    (hKout : Kout ≤ -((t : ℤ) * (Amax : ℤ) + 2)) :
    Set.ncard {u : Fin t → Fin Q | AllBad p Q εw A c u}
      ≤ 2 * m * (Q ^ (t - 1) * ((⌈2 * Kbad p Q Δ Amax t⌉₊ + 1) * Amax)) := by
  classical
  have hp : 0 < p := NeZero.pos p
  have hBadEq : Set.ncard {u : Fin t → Fin Q | AllBad p Q εw A c u}
      = (Finset.univ.filter (fun u : Fin t → Fin Q => AllBad p Q εw A c u)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext u
    simp
  rw [hBadEq]
  have hΔ0z : (0 : ℤ) ≤ Δ := by
    have h1 : (0 : ℤ) ≤ (t : ℤ) * (Amax : ℤ) * D :=
      mul_nonneg (mul_nonneg (Int.natCast_nonneg t) (Int.natCast_nonneg Amax)) hD0
    linarith [hΔ]
  have hΔ0 : (0 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ0z
  have hKbad0 : 0 ≤ Kbad p Q Δ Amax t := by
    rw [Kbad]
    have h1 : (0 : ℝ) ≤ 2 * (Δ : ℝ) + (t : ℝ) * (Amax : ℝ) := by positivity
    exact div_nonneg (mul_nonneg h1 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  -- the per-slab bound
  have hslab : ∀ (i : Fin m) (α : ℝ),
      (Slab p Q Δ Amax t A c i α).card
        ≤ Q ^ (t - 1) * ((⌈2 * Kbad p Q Δ Amax t⌉₊ + 1) * Amax) := by
    intro i α
    rw [Slab]
    obtain ⟨j₀, hj₀⟩ := hne i
    set θ : ℝ := (Q : ℝ) / (p : ℝ) * (α - (c i : ℝ)) with hθ
    set K : ℝ := Kbad p Q Δ Amax t with hK
    set W : Finset ℤ := (Finset.Icc 0 ((Q : ℤ) - 1)).filter
      (fun r => ∃ z : ℤ, |(r : ℝ) - θ - (z : ℝ) * (Q : ℝ)| ≤ K) with hW
    have hWmem : ∀ r ∈ W, 0 ≤ r ∧ r < (Q : ℤ) := by
      intro r hr
      rw [hW, Finset.mem_filter, Finset.mem_Icc] at hr
      exact ⟨hr.1.1, by omega⟩
    have hcond : ∀ r : ℤ, 0 ≤ r → r < (Q : ℤ) →
        (∃ z : ℤ, |(r : ℝ) - (z : ℝ) * (Q : ℝ) - θ| ≤ K) → r ∈ W := by
      intro r h1 h2 h
      rw [hW, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨h1, by omega⟩, ?_⟩
      obtain ⟨z, hz⟩ := h
      exact ⟨z, by convert hz using 2; ring⟩
    have hcard := Commons.Data.Nat.card_mod_window_le (L := fun j => A i j) j₀ hj₀ hQ W hWmem θ K
      hcond
    have hWeq : (↑W : Set ℤ)
        = {r : ℤ | 0 ≤ r ∧ r < (Q : ℤ) ∧
            ∃ z : ℤ, |(r : ℝ) - θ - (z : ℝ) * (Q : ℝ)| ≤ K} := by
      ext r
      rw [hW, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, by omega⟩, h3⟩
    have hWcard : W.card ≤ ⌈2 * K⌉₊ + 1 := by
      have hgen := card_residue_window_le_gen hQ θ K (by rw [hK]; exact hKbad0)
      rw [← Set.ncard_coe_finset (s := W), hWeq]
      exact hgen
    have hncard_eq : Set.ncard {u : Fin t → Fin Q | ∃ z : ℤ,
        |((∑ j, A i j * ((u j).val : ℤ) : ℤ) : ℝ) - (z : ℝ) * (Q : ℝ) - θ| ≤ K}
        = (Finset.univ.filter (fun u : Fin t → Fin Q => ∃ z : ℤ,
        |((∑ j, A i j * ((u j).val : ℤ) : ℤ) : ℝ) - (z : ℝ) * (Q : ℝ) - θ| ≤ K)).card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext u
      simp
    rw [hncard_eq] at hcard
    calc (Finset.univ.filter (fun u : Fin t → Fin Q => ∃ z : ℤ,
          |((∑ j, A i j * ((u j).val : ℤ) : ℤ) : ℝ) - (z : ℝ) * (Q : ℝ) - θ| ≤ K)).card
        ≤ Q ^ (t - 1) * (W.card * (A i j₀).natAbs) := hcard
      _ ≤ Q ^ (t - 1) * ((⌈2 * K⌉₊ + 1) * Amax) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hWcard (hA i j₀))
      _ = Q ^ (t - 1) * ((⌈2 * Kbad p Q Δ Amax t⌉₊ + 1) * Amax) := by rw [hK]
  -- every bad box lands in one of the `2m` slabs
  have hsub : ∀ u : Fin t → Fin Q, AllBad p Q εw A c u →
      u ∈ Finset.univ.biUnion (fun i : Fin m =>
          Slab p Q Δ Amax t A c i (εw * (p : ℝ)) ∪ Slab p Q Δ Amax t A c i (2 * εw * (p : ℝ))) := by
    intro u ⟨i, h1, h2⟩
    have hspec := boxShift_spec A c hQ hQp εw hεw Amax hA Kout Δ D hD hD0 hΔ hΔε hΔp u i
    have hstab : StableAt p Q A c u i (boxShift p Q εw Kout A c u i) := by
      rcases hspec with h | h
      · exact absurd h h1
      · exact h
    have hrange := range_le_of_bounds (A := A) (c := c) (u := u) (i := i) (Amax := Amax)
      (D := D) (Δ := Δ) hQ hA hD hD0 hΔ
    have hin : ∃ x ∈ boxInt p Q u, Clip εw p (((psi p A c x i).val : ℝ)) := by
      by_contra hc'
      apply h1
      intro x hx hnc
      exact hc' ⟨x, hx, hnc⟩
    have hout : ∃ x ∈ boxInt p Q u, ¬ Clip εw p (((psi p A c x i).val : ℝ)) := by
      by_contra hc'
      apply h2
      intro x hx
      by_contra hnc
      exact hc' ⟨x, hx, hnc⟩
    obtain ⟨x, hx, α, hα, hnear⟩ := exists_near_boundary hstab hout hin Δ hrange hΔ0
    obtain ⟨z, hz⟩ := corner_mod_transport hQ hp A c u i hA
      (corner_near hQ hQp hrange hΔ0 hx hnear)
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rcases hα with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hz⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, hz⟩)
  have hsub' : (Finset.univ.filter (fun u : Fin t → Fin Q => AllBad p Q εw A c u))
      ⊆ Finset.univ.biUnion (fun i : Fin m =>
          Slab p Q Δ Amax t A c i (εw * (p : ℝ))
            ∪ Slab p Q Δ Amax t A c i (2 * εw * (p : ℝ))) := by
    intro u hu
    exact hsub u (Finset.mem_filter.mp hu).2
  calc (Finset.univ.filter (fun u : Fin t → Fin Q => AllBad p Q εw A c u)).card
      ≤ (Finset.univ.biUnion (fun i : Fin m =>
          Slab p Q Δ Amax t A c i (εw * (p : ℝ))
            ∪ Slab p Q Δ Amax t A c i (2 * εw * (p : ℝ)))).card := Finset.card_le_card hsub'
    _ ≤ ∑ i : Fin m, (Slab p Q Δ Amax t A c i (εw * (p : ℝ))
          ∪ Slab p Q Δ Amax t A c i (2 * εw * (p : ℝ))).card := Finset.card_biUnion_le
    _ ≤ ∑ i : Fin m, ((Slab p Q Δ Amax t A c i (εw * (p : ℝ))).card
          + (Slab p Q Δ Amax t A c i (2 * εw * (p : ℝ))).card) :=
        Finset.sum_le_sum (fun i _ => Finset.card_union_le _ _)
    _ ≤ ∑ _i : Fin m, (2 * (Q ^ (t - 1) * ((⌈2 * Kbad p Q Δ Amax t⌉₊ + 1) * Amax))) :=
        Finset.sum_le_sum (fun i _ => by
          have h := add_le_add (hslab i (εw * (p : ℝ))) (hslab i (2 * εw * (p : ℝ)))
          linarith [h])
    _ = m * (2 * (Q ^ (t - 1) * ((⌈2 * Kbad p Q Δ Amax t⌉₊ + 1) * Amax))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    _ = 2 * m * (Q ^ (t - 1) * ((⌈2 * Kbad p Q Δ Amax t⌉₊ + 1) * Amax)) := by
        ring

end Local
end GYMaj
