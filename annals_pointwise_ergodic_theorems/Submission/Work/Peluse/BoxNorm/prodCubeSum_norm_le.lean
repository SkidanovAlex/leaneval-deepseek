/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.BoxNorm.genHolder
import Submission.Work.Peluse.BoxNorm.winForm_succ_cs

/-!
# Peluse's Lemma 2.3: the multilinear Gowers box-norm inequality

This file proves

`‖prodCubeSum t Q S f‖ ≤ ∏_ω boxNorm t Q S (f ω)`

(Peluse, *Bounds for sets with no polynomial progressions*, Lemma 2.3), i.e. the
Gowers--Cauchy--Schwarz inequality for the Gowers box norm of `Submission/Work/Peluse/Basic.lean`.

The proof is the standard induction on the dimension `t` of the cube, carried out for the
*box form* `winForm t Q W φ` (`WinDefs`) over a window `W`:

* `winForm_norm_le` : the Gowers--Cauchy--Schwarz inequality
  `‖winForm t Q W φ‖ ≤ ∏_ω winNorm t Q W (φ ω)`;
* the base case `t = 1` is the classical Cauchy--Schwarz inequality (`winForm_norm_le_one`);
* the induction step (`winForm_norm_succ_step`) splits off the first coordinate
  (`winForm_succ`), applies Cauchy--Schwarz over the remaining cube
  (`winForm_succ_cs`), applies the induction hypothesis to each piece and recombines the
  pieces with the generalized Hölder inequality `genHolder` and the single-function recursion
  `winForm_const_norm_succ`;
* finally `prodCubeSum_eq_const_mul_winForm` rewrites `prodCubeSum` as a constant times a box
  form over a large enough window, and the `tsum` over `ℤ` becomes a finite sum
  (`cubeTerm_tsum_window`).
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.BoxNorm

noncomputable section

open Work.Peluse

lemma winNorm_nonneg {n : ℕ} (Q : Fin n → Finset ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    0 ≤ winNorm n Q W g :=
  Real.rpow_nonneg (norm_nonneg _) _

lemma sum_prod_swap {A M : Type*} [Fintype A] [AddCommMonoid M] (F : A → A → M) :
    (∑ a : A, ∑ a' : A, F a a') = ∑ a : A, ∑ a' : A, F a' a := by
  have h1 : (∑ a : A, ∑ a' : A, F a a') = ∑ p : A × A, F p.1 p.2 :=
    (Fintype.sum_prod_type (f := fun p : A × A => F p.1 p.2)).symm
  have h2 : (∑ p : A × A, F p.1 p.2) = ∑ p : A × A, F p.2 p.1 :=
    Fintype.sum_equiv (Equiv.prodComm A A) (fun p : A × A => F p.1 p.2)
      (fun p : A × A => F p.2 p.1) (fun p => rfl)
  have h3 : (∑ p : A × A, F p.2 p.1) = ∑ a : A, ∑ a' : A, F a' a :=
    Fintype.sum_prod_type (f := fun p : A × A => F p.2 p.1)
  rw [h1, h2, h3]

lemma rpow_pow_root {y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    (y ^ (2^(n+1) : ℕ)) ^ (1 / (2:ℝ)^n) = y ^ 2 := by
  rw [← Real.rpow_natCast y (2^(n+1)), ← Real.rpow_natCast y 2, ← Real.rpow_mul hy]
  congr 1
  rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  field_simp

/-- The `2^t`-fold product over `Fin t → Bool` reindexed by the first coordinate. -/
lemma prod_fin_succ_bool {m : ℕ} {M : Type*} [CommMonoid M] (F : (Fin (m+1) → Bool) → M) :
    (∏ ω : Fin (m+1) → Bool, F ω)
      = (∏ ω : Fin m → Bool, F (Fin.cases false ω))
        * (∏ ω : Fin m → Bool, F (Fin.cases true ω)) := by
  have h := Fintype.prod_equiv
    { toFun := fun p : Bool × (Fin m → Bool) => (Fin.cases p.1 p.2 : Fin (m+1) → Bool)
      invFun := fun ω => (ω 0, fun i => ω i.succ)
      left_inv := by
        rintro ⟨b, w⟩
        refine Prod.ext ?_ ?_
        · show (Fin.cases b w : Fin (m+1) → Bool) 0 = b
          exact Fin.cases_zero
        · show (fun i : Fin m => (Fin.cases b w : Fin (m+1) → Bool) i.succ) = w
          funext i; exact Fin.cases_succ i
      right_inv := by
        intro ω
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j; rfl }
    (fun p : Bool × (Fin m → Bool) => F (Fin.cases p.1 p.2)) F (fun p => rfl)
  rw [← h, Fintype.prod_prod_type, Fintype.prod_bool, mul_comm]

def boolEquivFin1 : Bool ≃ (Fin 1 → Bool) where
  toFun b := fun _ => b
  invFun ω := ω 0
  left_inv b := rfl
  right_inv ω := by funext i; fin_cases i; rfl

lemma prod_fin_one_bool {M : Type*} [CommMonoid M] (F : (Fin 1 → Bool) → M) :
    (∏ ω : Fin 1 → Bool, F ω) = F (fun _ => true) * F (fun _ => false) := by
  have h := Fintype.prod_equiv boolEquivFin1 (fun b : Bool => F (fun _ => b)) F
    (fun b => by rw [show boolEquivFin1 b = (fun _ => b) from rfl])
  rw [← h, Fintype.prod_bool]

lemma winNorm_one_sq (Q : Fin 1 → Finset ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    winNorm 1 Q W g ^ 2 = ‖winForm 1 Q W (fun _ => g)‖ := by
  have h : (1 / (2:ℝ)^1) * ((2:ℕ):ℝ) = 1 := by norm_num
  rw [winNorm, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), h, Real.rpow_one]

/-- The `t = 1` case of the Gowers--Cauchy--Schwarz inequality. -/
theorem winForm_norm_le_one (Q : Fin 1 → Finset ℤ) (W : Finset ℤ)
    (φ : (Fin 1 → Bool) → ℤ → ℂ) :
    ‖winForm 1 Q W φ‖ ≤ ∏ ω : Fin 1 → Bool, winNorm 1 Q W (φ ω) := by
  have hPf : 0 ≤ ∏ ω : Fin 1 → Bool, winNorm 1 Q W (φ ω) :=
    Finset.prod_nonneg fun ω _ => winNorm_nonneg _ _ _
  have hcs := cauchySchwarzC W
    (fun x => ∑ a' : {x : ℤ // x ∈ Q 0}, φ (fun _ => false) (x + a'.1))
    (fun x => ∑ a : {x : ℤ // x ∈ Q 0}, φ (fun _ => true) (x + a.1))
  have hsq : ‖winForm 1 Q W φ‖ ^ 2 ≤ (∏ ω : Fin 1 → Bool, winNorm 1 Q W (φ ω)) ^ 2 := by
    rw [prod_fin_one_bool, mul_pow, winNorm_one_sq, winNorm_one_sq,
      winForm_const_one_norm, winForm_const_one_norm]
    rw [winForm_one]
    exact le_trans hcs (le_of_eq (mul_comm _ _))
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hPf] at h

theorem sum_winForm_le {n : ℕ} (hn : 1 ≤ n)
    (ih : ∀ (Q : Fin n → Finset ℤ) (W : Finset ℤ) (ψ : (Fin n → Bool) → ℤ → ℂ),
      ‖winForm n Q W ψ‖ ≤ ∏ ω, winNorm n Q W (ψ ω))
    (Q : Fin (n+1) → Finset ℤ) (W : Finset ℤ) (g : (Fin n → Bool) → ℤ → ℂ) :
    ‖(∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
        winForm n (fun i : Fin n => Q i.succ) W
          (fun ω y => g ω (y + a.1) * star (g ω (y + a'.1))))‖
      ≤ (∏ ω : Fin n → Bool, winNorm (n+1) Q W (g ω)) ^ 2 := by
  classical
  have h1 : ‖(∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
        winForm n (fun i : Fin n => Q i.succ) W
          (fun ω y => g ω (y + a.1) * star (g ω (y + a'.1))))‖
      ≤ ∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          ‖winForm n (fun i : Fin n => Q i.succ) W
            (fun ω y => g ω (y + a.1) * star (g ω (y + a'.1)))‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun a _ => norm_sum_le _ _
  have h2 : (∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
        ‖winForm n (fun i : Fin n => Q i.succ) W
          (fun ω y => g ω (y + a.1) * star (g ω (y + a'.1)))‖)
      ≤ ∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          ∏ ω : Fin n → Bool, winNorm n (fun i : Fin n => Q i.succ) W
            (fun y => g ω (y + a.1) * star (g ω (y + a'.1))) :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun a' _ => ih _ _ _
  have h3 : (∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
        ∏ ω : Fin n → Bool, winNorm n (fun i : Fin n => Q i.succ) W
          (fun y => g ω (y + a.1) * star (g ω (y + a'.1))))
      ≤ ∏ ω : Fin n → Bool, (∑ p : {x : ℤ // x ∈ Q 0} × {x : ℤ // x ∈ Q 0},
          (winNorm n (fun i : Fin n => Q i.succ) W
            (fun y => g ω (y + p.1.1) * star (g ω (y + p.2.1)))) ^ (2^n))
          ^ (1 / (2:ℝ)^n) := by
    have hgen := genHolder (t := n) (X := {x : ℤ // x ∈ Q 0} × {x : ℤ // x ∈ Q 0})
      (fun ω p => winNorm n (fun i : Fin n => Q i.succ) W
        (fun y => g ω (y + p.1.1) * star (g ω (y + p.2.1))))
      (fun ω p => Real.rpow_nonneg (norm_nonneg _) _)
    rw [Fintype.sum_prod_type] at hgen
    exact hgen
  have h4 : (∏ ω : Fin n → Bool, (∑ p : {x : ℤ // x ∈ Q 0} × {x : ℤ // x ∈ Q 0},
          (winNorm n (fun i : Fin n => Q i.succ) W
            (fun y => g ω (y + p.1.1) * star (g ω (y + p.2.1)))) ^ (2^n))
          ^ (1 / (2:ℝ)^n))
      ≤ ∏ ω : Fin n → Bool, winNorm (n+1) Q W (g ω) ^ 2 := by
    refine Finset.prod_le_prod₀
      (fun ω _ => Real.rpow_nonneg (Finset.sum_nonneg fun p _ =>
        pow_nonneg (Real.rpow_nonneg (norm_nonneg _) _) _) _)
      fun ω _ => ?_
    have hsum : (∑ p : {x : ℤ // x ∈ Q 0} × {x : ℤ // x ∈ Q 0},
          (winNorm n (fun i : Fin n => Q i.succ) W
            (fun y => g ω (y + p.1.1) * star (g ω (y + p.2.1)))) ^ (2^n))
        = ‖winForm (n+1) Q W (fun _ => g ω)‖ := by
      rw [Fintype.sum_prod_type]
      have h1' : ∀ a a' : {x : ℤ // x ∈ Q 0},
          (winNorm n (fun i : Fin n => Q i.succ) W
            (fun y => g ω (y + a.1) * star (g ω (y + a'.1)))) ^ (2^n)
          = ‖winForm n (fun i : Fin n => Q i.succ) W
              (fun _ y => g ω (y + a.1) * star (g ω (y + a'.1)))‖ :=
        fun a a' => winNorm_pow n _ W _
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a' _ => h1' a a'))]
      have hswap := sum_prod_swap (A := {x : ℤ // x ∈ Q 0})
        (fun a a' => ‖winForm n (fun i : Fin n => Q i.succ) W
              (fun _ y => g ω (y + a.1) * star (g ω (y + a'.1)))‖)
      rw [hswap, ← winForm_const_norm_succ (n := n) hn Q W (g ω)]
    rw [hsum, ← winNorm_pow (n+1) Q W (g ω)]
    exact le_of_eq (rpow_pow_root (Real.rpow_nonneg (norm_nonneg _) _) n)
  have h4' : (∏ ω : Fin n → Bool, (∑ p : {x : ℤ // x ∈ Q 0} × {x : ℤ // x ∈ Q 0},
          (winNorm n (fun i : Fin n => Q i.succ) W
            (fun y => g ω (y + p.1.1) * star (g ω (y + p.2.1)))) ^ (2^n))
          ^ (1 / (2:ℝ)^n))
      ≤ (∏ ω : Fin n → Bool, winNorm (n+1) Q W (g ω)) ^ 2 := by
    rw [← Finset.prod_pow]
    exact h4
  exact le_trans h1 (le_trans h2 (le_trans h3 h4'))

/-- The induction step of the Gowers--Cauchy--Schwarz inequality. -/
theorem winForm_norm_succ_step {n : ℕ} (hn : 1 ≤ n)
    (ih : ∀ (Q : Fin n → Finset ℤ) (W : Finset ℤ) (ψ : (Fin n → Bool) → ℤ → ℂ),
      ‖winForm n Q W ψ‖ ≤ ∏ ω, winNorm n Q W (ψ ω))
    (Q : Fin (n+1) → Finset ℤ) (W : Finset ℤ) (φ : (Fin (n+1) → Bool) → ℤ → ℂ) :
    ‖winForm (n+1) Q W φ‖
      ≤ (∏ ω : Fin n → Bool, winNorm (n+1) Q W (φ (Fin.cases false ω)))
        * (∏ ω : Fin n → Bool, winNorm (n+1) Q W (φ (Fin.cases true ω))) := by
  have hcs := winForm_succ_cs (n := n) Q W φ
  have hf := sum_winForm_le hn ih Q W (fun ω y => φ (Fin.cases false ω) y)
  have ht := sum_winForm_le hn ih Q W (fun ω y => φ (Fin.cases true ω) y)
  have hPf : 0 ≤ ∏ ω : Fin n → Bool, winNorm (n+1) Q W (φ (Fin.cases false ω)) :=
    Finset.prod_nonneg fun ω _ => winNorm_nonneg _ _ _
  have hPt : 0 ≤ ∏ ω : Fin n → Bool, winNorm (n+1) Q W (φ (Fin.cases true ω)) :=
    Finset.prod_nonneg fun ω _ => winNorm_nonneg _ _ _
  have hsq : ‖winForm (n+1) Q W φ‖ ^ 2
      ≤ ((∏ ω : Fin n → Bool, winNorm (n+1) Q W (φ (Fin.cases false ω)))
        * (∏ ω : Fin n → Bool, winNorm (n+1) Q W (φ (Fin.cases true ω)))) ^ 2 := by
    refine le_trans hcs ?_
    calc ‖(∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
              winForm n (fun i : Fin n => Q i.succ) W
                (fun ω y => φ (Fin.cases false ω) (y + a.1)
                  * star (φ (Fin.cases false ω) (y + a'.1))))‖
          * ‖(∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
              winForm n (fun i : Fin n => Q i.succ) W
                (fun ω y => φ (Fin.cases true ω) (y + a.1)
                  * star (φ (Fin.cases true ω) (y + a'.1))))‖
        ≤ (∏ ω : Fin n → Bool, winNorm (n+1) Q W (φ (Fin.cases false ω))) ^ 2
          * (∏ ω : Fin n → Bool, winNorm (n+1) Q W (φ (Fin.cases true ω))) ^ 2 :=
          mul_le_mul hf ht (norm_nonneg _) (sq_nonneg _)
      _ = ((∏ ω : Fin n → Bool, winNorm (n+1) Q W (φ (Fin.cases false ω)))
          * (∏ ω : Fin n → Bool, winNorm (n+1) Q W (φ (Fin.cases true ω)))) ^ 2 := by
          ring
  have hsq2 : ‖winForm (n+1) Q W φ‖ ^ 2
      ≤ ((∏ ω : Fin n → Bool, winNorm (n+1) Q W (φ (Fin.cases false ω)))
        * (∏ ω : Fin n → Bool, winNorm (n+1) Q W (φ (Fin.cases true ω)))) ^ 2 := hsq
  have h := sq_le_sq.mp hsq2
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg hPf hPt)] at h

/-- **Gowers--Cauchy--Schwarz inequality for the box form.** -/
theorem winForm_norm_le : ∀ (t : ℕ) (_ : 1 ≤ t) (Q : Fin t → Finset ℤ) (W : Finset ℤ)
    (φ : (Fin t → Bool) → ℤ → ℂ),
    ‖winForm t Q W φ‖ ≤ ∏ ω : Fin t → Bool, winNorm t Q W (φ ω) := by
  intro t
  induction t with
  | zero => intro ht; omega
  | succ n ih =>
    intro hn Q W φ
    cases n with
    | zero => exact winForm_norm_le_one Q W φ
    | succ k =>
      have hstep := winForm_norm_succ_step (n := k+1) (by omega)
        (fun Q' W' ψ => ih (by omega) Q' W' ψ) Q W φ
      rw [prod_fin_succ_bool (m := k+1) (F := fun ω => winNorm (k+2) Q W (φ ω))]
      exact hstep

def cubeConst (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) : ℂ :=
  ((S.card : ℂ))⁻¹ * (∏ i : Fin t, ((Q i).card : ℂ)⁻¹) * (∏ i : Fin t, ((Q i).card : ℂ)⁻¹)

def winWindow (t : ℕ) (Q : Fin t → Finset ℤ) (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(((N + ∑ i, (Q i).sum (fun a => a.natAbs)) : ℕ) : ℤ))
    ((((N + ∑ i, (Q i).sum (fun a => a.natAbs)) : ℕ) : ℤ))

lemma rpow_root_pow {x : ℝ} (hx : 0 ≤ x) (t : ℕ) :
    (x ^ (1 / (2 : ℝ) ^ t)) ^ (2 ^ t) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have h2 : (1 / (2 : ℝ) ^ t) * ((2 ^ t : ℕ) : ℝ) = 1 := by
    push_cast
    field_simp
  rw [h2, Real.rpow_one]

lemma natAbs_sum_le {ι : Type*} (s : Finset ι) (g : ι → ℤ) :
    (∑ i ∈ s, g i).natAbs ≤ ∑ i ∈ s, (g i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)

lemma total_corner_natAbs_le {t : ℕ} (Q : Fin t → Finset ℤ) (z z' : Tuple t Q)
    (ω : Fin t → Bool) :
    (Tuple.total (Tuple.corner z z' ω)).natAbs ≤ ∑ i, (Q i).sum (fun a => a.natAbs) := by
  rw [Tuple.total]
  refine le_trans (natAbs_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  by_cases h : ω i
  · have : Tuple.corner z z' ω i = z i := by simp [Tuple.corner, h]
    rw [this]
    exact Finset.single_le_sum (fun a _ => Nat.zero_le _) (z i).2
  · have : Tuple.corner z z' ω i = z' i := by simp [Tuple.corner, h]
    rw [this]
    exact Finset.single_le_sum (fun a _ => Nat.zero_le _) (z' i).2

lemma star_pow_zero (k : ℕ) : (star^[k]) (0 : ℂ) = 0 := by
  induction k with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; simp

lemma cubeTerm_tsum_window {t : ℕ} (Q : Fin t → Finset ℤ) (f : (Fin t → Bool) → ℤ → ℂ)
    {N : ℕ} (hN : ∀ ω, SupportIn (f ω) N) (z z' : Tuple t Q) :
    (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
        (f ω (x + Tuple.total (Tuple.corner z z' ω))))
      = ∑ x ∈ winWindow t Q N,
          ∏ ω : Fin t → Bool, (star^[weight ω])
            (f ω (x + Tuple.total (Tuple.corner z z' ω))) := by
  rw [winWindow]
  set M : ℕ := ∑ i, (Q i).sum (fun a => a.natAbs) with hM
  set K : ℕ := N + M with hK
  refine tsum_eq_sum (fun x hx => ?_)
  have hxK : K < x.natAbs := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hx
    omega
  set ω₀ : Fin t → Bool := fun _ => false with hω
  have hc : (Tuple.total (Tuple.corner z z' ω₀)).natAbs ≤ M := by
    rw [hM]
    exact total_corner_natAbs_le Q z z' ω₀
  have htri : x.natAbs ≤ (x + Tuple.total (Tuple.corner z z' ω₀)).natAbs
      + (Tuple.total (Tuple.corner z z' ω₀)).natAbs := by
    have h := Int.natAbs_add_le (x + Tuple.total (Tuple.corner z z' ω₀))
      (-(Tuple.total (Tuple.corner z z' ω₀)))
    simpa using h
  have hlt : N < (x + Tuple.total (Tuple.corner z z' ω₀)).natAbs := by omega
  refine Finset.prod_eq_zero (Finset.mem_univ ω₀) ?_
  rw [hN ω₀ _ hlt]
  exact star_pow_zero _

lemma prodCubeSum_eq_const_mul_winForm {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (f : (Fin t → Bool) → ℤ → ℂ) {N : ℕ} (hN : ∀ ω, SupportIn (f ω) N) :
    prodCubeSum t Q S f = cubeConst t Q S * winForm t Q (winWindow t Q N) f := by
  rw [winForm]
  have h : prodCubeSum t Q S f = cubeConst t Q S *
      (∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
          (f ω (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) := rfl
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  have hcw : (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
        (f ω (x + cornerShift (fun i => (z i).1) (fun i => (z' i).1) ω)))
      = (∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
        (f ω (x + Tuple.total (Tuple.corner z z' ω)))) := by
    refine tsum_congr fun x => Finset.prod_congr rfl fun ω _ => ?_
    rw [cornerShift_eq_total]
  rw [hcw, cubeTerm_tsum_window Q f hN z z']

lemma boxNorm_eq_win {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (g : ℤ → ℂ) {N : ℕ}
    (hN : SupportIn g N) :
    boxNorm t Q S g
      = ‖cubeConst t Q S‖ ^ (1 / (2 : ℝ) ^ t) * winNorm t Q (winWindow t Q N) g := by
  unfold boxNorm boxNormPow boxSumPow winNorm
  rw [prodCubeSum_eq_const_mul_winForm Q S (fun _ => g) (fun _ => hN), norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

/-- **Peluse's Lemma 2.3**: the multilinear average over a `t`-dimensional box of `2^t` possibly
different functions is bounded by the product of their Gowers box norms. -/
theorem prodCubeSum_norm_le {t : ℕ} (ht : 1 ≤ t) (Q : Fin t → Finset ℤ) (S : Finset ℤ)
    (f : (Fin t → Bool) → ℤ → ℂ) (hf : ∀ ω : Fin t → Bool, Work.Peluse.FinSuppZ (f ω)) :
    ‖Work.Peluse.prodCubeSum t Q S f‖ ≤ ∏ ω : Fin t → Bool, Work.Peluse.boxNorm t Q S (f ω) := by
  classical
  choose N hN using hf
  set N₀ : ℕ := ∑ ω : Fin t → Bool, N ω with hN₀
  have hsupp : ∀ ω : Fin t → Bool, SupportIn (f ω) N₀ := by
    intro ω
    refine (hN ω).mono ?_
    rw [hN₀]
    exact Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ ω)
  have hsplit := prodCubeSum_eq_const_mul_winForm Q S f hsupp
  have hnorm : ‖prodCubeSum t Q S f‖
      = ‖cubeConst t Q S‖ * ‖winForm t Q (winWindow t Q N₀) f‖ := by
    rw [hsplit, norm_mul]
  rw [hnorm]
  refine le_trans (mul_le_mul_of_nonneg_left
    (winForm_norm_le t ht Q (winWindow t Q N₀) f) (norm_nonneg _)) ?_
  have hbox : (∏ ω : Fin t → Bool, boxNorm t Q S (f ω))
      = ∏ ω : Fin t → Bool,
          (‖cubeConst t Q S‖ ^ (1 / (2 : ℝ) ^ t)
            * winNorm t Q (winWindow t Q N₀) (f ω)) :=
    Finset.prod_congr rfl fun ω _ => boxNorm_eq_win Q S (f ω) (hsupp ω)
  rw [hbox, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, rpow_root_pow (norm_nonneg _) t]

end

end Work.Peluse.BoxNorm
