/-
# The polynomial bounds for the odd representation and the twisted carries

This file collects the ingredients of the final assembly of
`Work.Asymptotics.carry_twist_odd`:

* `frob6` is the entry-sum norm on `M₆(ℂ)`; it is submultiplicative and dominates the matrix
  entries, which turns the block factorization of `Work.Asymptotics.block_factorization` into
  the polynomial growth bound `sigmaHom_entry_bound` for the odd representation `σ`
  (`Work.Asymptotics.sigmaHom (T^n) = oddMT^n`, `sigmaHom (T^{-n}) = oddMTi^n`,
  `sigmaHom S = oddMS`);
* `Tblock_spec`/`Tblock_bound`, `STblock_spec`/`STblock_bound`: the twisted carries of the
  blocks `T^k` (`k : ℤ`) and `S T^k` (`Work.Asymptotics.TwistOddBlocks`);
* `base_carry_spec`: the twisted carries of the four base elements `1, -1, S, -S`;
* `block_letters_data`: the per-letter bounds consumed by `Work.Asymptotics.bAcc_spec` and
  `Work.Asymptotics.bAcc_bound` of `Work.Asymptotics.TwistOddLetters`;
* `carry_twist_odd_aux`: the assembly.
-/
import Mathlib
import Submission.Work.Asymptotics.TwistOddTpow
import Submission.Work.Asymptotics.TwistOddLetters
import Submission.Work.Asymptotics.twist_atomS_odd
import Submission.Work.Asymptotics.block_factorization
import Submission.Work.Asymptotics.CarryBoundBasic

set_option maxHeartbeats 1600000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm

namespace Work.Asymptotics

open Work.Kernels

/-! ## The entry-sum norm `frob6` on `M₆(ℂ)` -/

/-- Sum of the absolute values of the entries of a `6 × 6` complex matrix. -/
def frob6 (A : Matrix (Fin 6) (Fin 6) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖

lemma frob6_nonneg (A : Matrix (Fin 6) (Fin 6) ℂ) : 0 ≤ frob6 A :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _

lemma entry_le_frob6 (A : Matrix (Fin 6) (Fin 6) ℂ) (i j : Fin 6) : ‖A i j‖ ≤ frob6 A := by
  have h1 : ‖A i j‖ ≤ ∑ j : Fin 6, ‖A i j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ j)
  have h2 : (∑ j : Fin 6, ‖A i j‖) ≤ frob6 A := by
    simp only [frob6]
    exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)
      (Finset.mem_univ i)
  linarith

/-- `frob6` dominates the entries up to the factor `36`; the converse bound used below. -/
lemma frob6_le_of_entry_le (A : Matrix (Fin 6) (Fin 6) ℂ) {B : ℝ} (h : ∀ i j, ‖A i j‖ ≤ B) :
    frob6 A ≤ 36 * B := by
  rw [frob6]
  calc ∑ i, ∑ j, ‖A i j‖ ≤ ∑ _i : Fin 6, ∑ _j : Fin 6, B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = 36 * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

lemma frob6_mul_le (A B : Matrix (Fin 6) (Fin 6) ℂ) : frob6 (A * B) ≤ frob6 A * frob6 B := by
  have h1 : frob6 (A * B) ≤ ∑ i, ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ := by
    rw [frob6]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    calc ‖(A * B) i j‖ = ‖∑ k, A i k * B k j‖ := by rw [Matrix.mul_apply]
      _ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
      _ = ∑ k, ‖A i k‖ * ‖B k j‖ := by simp only [norm_mul]
  have hswap : (∑ i, ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖)
      = ∑ i, ∑ k, ∑ j, ‖A i k‖ * ‖B k j‖ := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have h2 : (∑ i, ∑ k, ∑ j, ‖A i k‖ * ‖B k j‖)
      ≤ (∑ i, ∑ k, ‖A i k‖) * (∑ k, ∑ j, ‖B k j‖) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    calc ∑ j, ‖A i k‖ * ‖B k j‖ = ‖A i k‖ * (∑ j, ‖B k j‖) := (Finset.mul_sum _ _ _).symm
      _ ≤ ‖A i k‖ * (∑ k', ∑ j, ‖B k' j‖) :=
          mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (fun k' _ => Finset.sum_nonneg fun j _ => norm_nonneg _)
              (Finset.mem_univ k)) (norm_nonneg _)
  have hAB : frob6 (A * B) = ∑ i, ∑ j, ‖(A * B) i j‖ := rfl
  have hA : frob6 A = ∑ i, ∑ k, ‖A i k‖ := rfl
  have hB : frob6 B = ∑ k, ∑ j, ‖B k j‖ := rfl
  rw [hAB, hA, hB]
  exact le_trans h1 (hswap ▸ h2)

/-- Entrywise domination of the entry-sum norm. -/
lemma frob6_le_of_entry_le' (A B : Matrix (Fin 6) (Fin 6) ℂ)
    (h : ∀ i j, ‖A i j‖ ≤ ‖B i j‖) : frob6 A ≤ frob6 B := by
  have hA : frob6 A = ∑ i, ∑ j, ‖A i j‖ := rfl
  have hB : frob6 B = ∑ i, ∑ j, ‖B i j‖ := rfl
  rw [hA, hB]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j

lemma frob6_neg_le (A : Matrix (Fin 6) (Fin 6) ℂ) : frob6 (-A) ≤ frob6 A :=
  frob6_le_of_entry_le' _ _ fun i j => by simp [Matrix.neg_apply]

lemma frob6_smul_le (c : ℂ) (A : Matrix (Fin 6) (Fin 6) ℂ) : frob6 (c • A) ≤ ‖c‖ * frob6 A := by
  have hA : frob6 A = ∑ i, ∑ j, ‖A i j‖ := rfl
  have hc : frob6 (c • A) = ∑ i, ∑ j, ‖(c • A) i j‖ := rfl
  rw [hc, hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  simp [Matrix.smul_apply]

lemma frob6_one_le : frob6 (1 : Matrix (Fin 6) (Fin 6) ℂ) ≤ 200 := by
  have h : ∀ i j : Fin 6, ‖(1 : Matrix (Fin 6) (Fin 6) ℂ) i j‖ ≤ (1 : ℝ) := by
    intro i j
    rw [Matrix.one_apply]
    split
    · simp
    · simp
  have hh := frob6_le_of_entry_le (1 : Matrix (Fin 6) (Fin 6) ℂ) h
  linarith

/-- `frob6` of the matrix `σ(S) = oddMS` is an absolute constant. -/
lemma frob6_oddMS_le : frob6 oddMS ≤ 200 := by
  have h : ∀ i j : Fin 6, ‖oddMS i j‖ ≤ (4 : ℝ) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [oddMS] <;> norm_num
  have hh := frob6_le_of_entry_le oddMS h
  linarith

/-! ## The growth of the odd representation `σ` -/

/-- The entrywise growth of the powers of `oddMTi`, with natural constant and exponent. -/
lemma oddMTi_entry_bound_nat :
    ∃ C N : ℕ, ∀ m : ℕ, ∀ i j : Fin 6,
      ‖((oddMTi ^ m) i j)‖ ≤ C * (2 + (m : ℝ)) ^ N := by
  obtain ⟨C0, N0, hC0, hN0, -, h⟩ := oddMT_pow_entry_bound
  obtain ⟨C1, N1, h1⟩ := rpow_to_pow hC0 hN0
  refine ⟨C1, N1, fun m i j => ?_⟩
  have hm : (1 : ℝ) ≤ 2 + (m : ℝ) := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  calc ‖((oddMTi ^ m) i j)‖ ≤ C0 * (1 + (m : ℝ)) ^ N0 := h m i j
    _ ≤ C0 * (2 + (m : ℝ)) ^ N0 :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) (by linarith) hN0) hC0
    _ ≤ C1 * (2 + (m : ℝ)) ^ N1 := h1 _ hm

/-! ### Elementary list bookkeeping -/

private lemma cf_prod_map_nonneg {α : Type*} :
    ∀ (L : List α) (f : α → ℝ), (∀ a ∈ L, 0 ≤ f a) → 0 ≤ (L.map f).prod
  | [], _, _ => by simp
  | a :: t, f, h => by
      have h1 := h a (by simp)
      have h2 := cf_prod_map_nonneg t f fun x hx => h x (by simp [hx])
      rw [List.map_cons, List.prod_cons]
      exact mul_nonneg h1 h2

private lemma cf_prod_map_le {α : Type*} :
    ∀ (L : List α) (f g : α → ℝ), (∀ a ∈ L, f a ≤ g a) → (∀ a ∈ L, 0 ≤ f a) →
      (L.map f).prod ≤ (L.map g).prod
  | [], _, _, _, _ => by simp
  | a :: t, f, g, h, h0 => by
      have ha : f a ≤ g a := h a (by simp)
      have h0a : 0 ≤ f a := h0 a (by simp)
      have ht : ∀ x ∈ t, f x ≤ g x := fun x hx => h x (by simp [hx])
      have h0t : ∀ x ∈ t, 0 ≤ f x := fun x hx => h0 x (by simp [hx])
      have hgt : ∀ x ∈ t, 0 ≤ g x := fun x hx => le_trans (h0t x hx) (ht x hx)
      have h1 : 0 ≤ (t.map f).prod := cf_prod_map_nonneg t f h0t
      have h2 : 0 ≤ (t.map g).prod := cf_prod_map_nonneg t g hgt
      calc (List.map f (a :: t)).prod = f a * (t.map f).prod := rfl
        _ ≤ g a * (t.map g).prod := mul_le_mul ha (cf_prod_map_le t f g ht h0t) h1 (le_trans h0a ha)
        _ = (List.map g (a :: t)).prod := rfl

private lemma cf_prod_map_mul_pow {α : Type*} (L : List α) (f : α → ℝ) (K : ℝ) (M : ℕ) :
    (L.map (fun a => K * f a ^ M)).prod = K ^ L.length * (L.map f).prod ^ M := by
  induction L with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ih, List.length_cons,
        pow_succ, mul_pow]
      ring

private lemma cf_two_pow_length_le_prod {α : Type*} (L : List α) (f : α → ℝ)
    (h : ∀ a ∈ L, 2 ≤ f a) : (2 : ℝ) ^ L.length ≤ (L.map f).prod := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have h1 : (2 : ℝ) ≤ f a := h a (by simp)
      have h3 : (2 : ℝ) ^ t.length ≤ (t.map f).prod :=
        ih fun x hx => h x (by simp [hx])
      rw [List.length_cons, List.map_cons, List.prod_cons]
      calc (2 : ℝ) ^ (t.length + 1) = 2 * (2 : ℝ) ^ t.length := by rw [pow_succ]; ring
        _ ≤ f a * (t.map f).prod := mul_le_mul h1 h3 (by positivity) (by linarith)

private lemma frob6_list_prod_le {α : Type*} (L : List α) (f : α → Matrix (Fin 6) (Fin 6) ℂ) :
    frob6 ((L.map f).prod) ≤ 200 * (L.map (fun a => frob6 (f a))).prod := by
  induction L with
  | nil => simpa using frob6_one_le
  | cons a t ih =>
      have h1 : 0 ≤ frob6 (f a) := frob6_nonneg _
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
      calc frob6 (f a * (t.map f).prod)
          ≤ frob6 (f a) * frob6 ((t.map f).prod) := frob6_mul_le _ _
        _ ≤ frob6 (f a) * (200 * (t.map (fun a => frob6 (f a))).prod) :=
            mul_le_mul_of_nonneg_left ih h1
        _ = 200 * (frob6 (f a) * (t.map (fun a => frob6 (f a))).prod) := by ring

/-! ### The product form of the amplitude -/

/-- `∏_{l ∈ L} (1 + Frob (wblk l))`, i.e. `bAmp L / 2`; it is the product of the per-letter
growth factors. -/
def letterProd (L : List (Bool × ℤ)) : ℝ := (L.map (fun l => 1 + Frob (wblk l))).prod

lemma letterProd_eq (L : List (Bool × ℤ)) :
    letterProd L = (L.map (fun l => 1 + Frob (wblk l))).prod := rfl

lemma letterProd_nonneg (L : List (Bool × ℤ)) : 0 ≤ letterProd L :=
  cf_prod_map_nonneg L _ fun l _ => by have := Frob_nonneg (wblk l); linarith

lemma bAmp_eq_letterProd (L : List (Bool × ℤ)) : bAmp L = letterProd L * 2 := by
  rw [bAmp, letterProd]

lemma one_le_letterProd (L : List (Bool × ℤ)) : 1 ≤ letterProd L := by
  calc (1 : ℝ) = 2 ^ (0 : ℕ) := (pow_zero 2).symm
    _ ≤ 2 ^ L.length := pow_le_pow_right₀ (by norm_num) (Nat.zero_le _)
    _ ≤ letterProd L := cf_two_pow_length_le_prod L _
        (fun l _ => by have := one_le_Frob_blk l; linarith)

lemma letterProd_le_bAmp (L : List (Bool × ℤ)) : letterProd L ≤ bAmp L := by
  rw [bAmp_eq_letterProd]
  have := letterProd_nonneg L
  linarith

/-! ### The bounds for the letters -/

/-- `1 + Frob (wblk l)` is nonnegative (indeed at least `2`). -/
lemma one_add_Frob_wblk_nonneg (l : Bool × ℤ) : (0 : ℝ) ≤ 1 + Frob (wblk l) := by
  have := Frob_nonneg (wblk l); linarith

/-- `frob6 (σ (T^k))` grows at most polynomially in `1 + Frob (T^k)`. -/
lemma frob6_sigmaHom_T_zpow_le {Cm Nm : ℕ}
    (hCm : ∀ m : ℕ, ∀ i j : Fin 6, ‖((oddMT ^ m) i j)‖ ≤ Cm * (2 + (m : ℝ)) ^ Nm)
    (hCmi : ∀ m : ℕ, ∀ i j : Fin 6, ‖((oddMTi ^ m) i j)‖ ≤ Cm * (2 + (m : ℝ)) ^ Nm)
    (k : ℤ) :
    frob6 (sigmaHom (ModularGroup.T ^ k))
      ≤ (36 * (Cm : ℝ) * 2 ^ Nm) * (1 + Frob (ModularGroup.T ^ k)) ^ Nm := by
  by_cases hk : 0 ≤ k
  · have hk1 : (ModularGroup.T : SL(2,ℤ)) ^ k = ModularGroup.T ^ (((k.toNat : ℕ)) : ℤ) := by
      rw [Int.toNat_of_nonneg hk]
    have hfrob : frob6 (sigmaHom (ModularGroup.T ^ k)) = frob6 (oddMT ^ k.toNat) := by
      rw [hk1, sigmaHom_T_zpow k.toNat]
    have hle : (2 : ℝ) + (k.toNat : ℝ) ≤ 2 * (1 + Frob (ModularGroup.T ^ k)) := by
      have hcast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
        have h : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
        exact_mod_cast h
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have h1 := abs_le_Frob_T_zpow k
      rw [abs_of_nonneg hk0] at h1
      linarith
    rw [hfrob]
    calc frob6 (oddMT ^ k.toNat)
        ≤ 36 * ((Cm : ℝ) * (2 + (k.toNat : ℝ)) ^ Nm) :=
          frob6_le_of_entry_le _ fun i j => hCm k.toNat i j
      _ ≤ 36 * ((Cm : ℝ) * (2 * (1 + Frob (ModularGroup.T ^ k))) ^ Nm) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hle Nm) (Nat.cast_nonneg Cm)
      _ = (36 * (Cm : ℝ) * 2 ^ Nm) * (1 + Frob (ModularGroup.T ^ k)) ^ Nm := by
          rw [mul_pow]; ring
  · have hk1 : (ModularGroup.T : SL(2,ℤ)) ^ k
        = ModularGroup.T ^ (-((((-k).toNat : ℕ)) : ℤ)) := by
      rw [show (((-k).toNat : ℕ) : ℤ) = -k from Int.toNat_of_nonneg (by omega), neg_neg]
    have hfrob : frob6 (sigmaHom (ModularGroup.T ^ k)) = frob6 (oddMTi ^ (-k).toNat) := by
      rw [hk1, sigmaHom_T_zpow_neg (-k).toNat]
    have hle : (2 : ℝ) + (((-k).toNat : ℕ) : ℝ) ≤ 2 * (1 + Frob (ModularGroup.T ^ k)) := by
      have hcast : ((((-k).toNat : ℕ)) : ℝ) ≤ Frob (ModularGroup.T ^ k) := by
        have h1 : ((((-k).toNat : ℕ)) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
        have h2 : ((((-k).toNat : ℕ)) : ℝ) = ((-k : ℤ) : ℝ) := by exact_mod_cast h1
        rw [h2]
        push_cast
        calc -((k : ℝ)) ≤ |(k : ℝ)| := neg_le_abs _
          _ ≤ Frob (ModularGroup.T ^ k) := abs_le_Frob_T_zpow k
      linarith
    rw [hfrob]
    calc frob6 (oddMTi ^ (-k).toNat)
        ≤ 36 * ((Cm : ℝ) * (2 + (((-k).toNat : ℕ) : ℝ)) ^ Nm) :=
          frob6_le_of_entry_le _ fun i j => hCmi (-k).toNat i j
      _ ≤ 36 * ((Cm : ℝ) * (2 * (1 + Frob (ModularGroup.T ^ k))) ^ Nm) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hle Nm) (Nat.cast_nonneg Cm)
      _ = (36 * (Cm : ℝ) * 2 ^ Nm) * (1 + Frob (ModularGroup.T ^ k)) ^ Nm := by
          rw [mul_pow]; ring

/-- `frob6 (σ δ) ≤ 200` for the four base elements `δ = ±1, ±S`. -/
lemma frob6_sigmaHom_base_le (δ : SL(2,ℤ))
    (hδ : δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) :
    frob6 (sigmaHom δ) ≤ 200 := by
  rcases hδ with h | h | h | h
  · rw [h, map_one]; exact frob6_one_le
  · rw [h, sigmaHom_neg_one]; exact le_trans (frob6_neg_le _) frob6_one_le
  · rw [h, sigmaHom_S]; exact frob6_oddMS_le
  · have hneg : (-ModularGroup.S : SL(2,ℤ)) = (-1 : SL(2,ℤ)) * ModularGroup.S := by
      rw [neg_one_mul]
    have hS : sigmaHom ModularGroup.S = oddMS := sigmaHom_S
    rw [h, hneg, map_mul, sigmaHom_neg_one, hS, neg_one_mul]
    exact le_trans (frob6_neg_le _) frob6_oddMS_le

/-- The per-letter bound for `frob6` of the odd representation. -/
lemma frob6_sigmaHom_wblk_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ M : ℕ,
      ∀ l : Bool × ℤ, frob6 (sigmaHom (wblk l)) ≤ K * (1 + Frob (wblk l)) ^ M := by
  obtain ⟨Cm, Nm, hCm⟩ := oddMT_entry_bound_nat
  obtain ⟨Cmi, Nmi, hCmi⟩ := oddMTi_entry_bound_nat
  have hCM : ∀ m : ℕ, ∀ i j : Fin 6,
      ‖((oddMT ^ m) i j)‖ ≤ max Cm Cmi * (2 + (m : ℝ)) ^ max Nm Nmi := by
    intro m i j
    have h2 : (Cm : ℝ) ≤ ((max Cm Cmi : ℕ) : ℝ) := by exact_mod_cast le_max_left Cm Cmi
    have h3 : (2 + (m : ℝ)) ^ Nm ≤ (2 + (m : ℝ)) ^ max Nm Nmi :=
      pow_le_pow_right₀ (by linarith) (le_max_left _ _)
    calc ‖((oddMT ^ m) i j)‖ ≤ (Cm : ℝ) * (2 + (m : ℝ)) ^ Nm := hCm m i j
      _ ≤ ((max Cm Cmi : ℕ) : ℝ) * (2 + (m : ℝ)) ^ Nm :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ ((max Cm Cmi : ℕ) : ℝ) * (2 + (m : ℝ)) ^ max Nm Nmi :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have hCMi : ∀ m : ℕ, ∀ i j : Fin 6,
      ‖((oddMTi ^ m) i j)‖ ≤ max Cm Cmi * (2 + (m : ℝ)) ^ max Nm Nmi := by
    intro m i j
    have h2 : (Cmi : ℝ) ≤ ((max Cm Cmi : ℕ) : ℝ) := by exact_mod_cast le_max_right Cm Cmi
    have h3 : (2 + (m : ℝ)) ^ Nmi ≤ (2 + (m : ℝ)) ^ max Nm Nmi :=
      pow_le_pow_right₀ (by linarith) (le_max_right _ _)
    calc ‖((oddMTi ^ m) i j)‖ ≤ (Cmi : ℝ) * (2 + (m : ℝ)) ^ Nmi := hCmi m i j
      _ ≤ ((max Cm Cmi : ℕ) : ℝ) * (2 + (m : ℝ)) ^ Nmi :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ ((max Cm Cmi : ℕ) : ℝ) * (2 + (m : ℝ)) ^ max Nm Nmi :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  refine ⟨200 * (36 * ((max Cm Cmi : ℕ) : ℝ) * 2 ^ max Nm Nmi), by positivity, max Nm Nmi, ?_⟩
  intro l
  rcases l with ⟨b, k⟩
  cases b
  · have hX0 : (0 : ℝ) ≤ 36 * ((max Cm Cmi : ℕ) : ℝ) * 2 ^ max Nm Nmi := by positivity
    have hy : (0 : ℝ) ≤ (1 + Frob (wblk (false, k))) ^ max Nm Nmi :=
      pow_nonneg (one_add_Frob_wblk_nonneg _) _
    have h1 : frob6 (sigmaHom (wblk (false, k)))
        ≤ (36 * ((max Cm Cmi : ℕ) : ℝ) * 2 ^ max Nm Nmi)
            * (1 + Frob (wblk (false, k))) ^ max Nm Nmi := by
      rw [show wblk (false, k) = ModularGroup.T ^ k from rfl]
      exact frob6_sigmaHom_T_zpow_le hCM hCMi k
    calc frob6 (sigmaHom (wblk (false, k)))
        ≤ (36 * ((max Cm Cmi : ℕ) : ℝ) * 2 ^ max Nm Nmi)
            * (1 + Frob (wblk (false, k))) ^ max Nm Nmi := h1
      _ ≤ (200 * (36 * ((max Cm Cmi : ℕ) : ℝ) * 2 ^ max Nm Nmi))
            * (1 + Frob (wblk (false, k))) ^ max Nm Nmi := by
          refine mul_le_mul_of_nonneg_right ?_ hy
          nlinarith [hX0]
  · have hX0 : (0 : ℝ) ≤ 36 * ((max Cm Cmi : ℕ) : ℝ) * 2 ^ max Nm Nmi := by positivity
    have hy : (0 : ℝ) ≤ (1 + Frob (wblk (true, k))) ^ max Nm Nmi :=
      pow_nonneg (one_add_Frob_wblk_nonneg _) _
    have hS : frob6 (sigmaHom ModularGroup.S) ≤ 200 := by
      rw [sigmaHom_S]; exact frob6_oddMS_le
    have hT := frob6_sigmaHom_T_zpow_le hCM hCMi k
    have h1 : frob6 (sigmaHom (wblk (true, k)))
        ≤ 200 * ((36 * ((max Cm Cmi : ℕ) : ℝ) * 2 ^ max Nm Nmi)
            * (1 + Frob (wblk (true, k))) ^ max Nm Nmi) := by
      rw [show wblk (true, k) = ModularGroup.S * ModularGroup.T ^ k from rfl, map_mul,
        show Frob (ModularGroup.S * ModularGroup.T ^ k) = Frob (ModularGroup.T ^ k) from
          (Frob_ST_zpow k).trans (Frob_T_zpow k).symm]
      calc frob6 (sigmaHom ModularGroup.S * sigmaHom (ModularGroup.T ^ k))
          ≤ frob6 (sigmaHom ModularGroup.S) * frob6 (sigmaHom (ModularGroup.T ^ k)) :=
            frob6_mul_le _ _
        _ ≤ 200 * ((36 * ((max Cm Cmi : ℕ) : ℝ) * 2 ^ max Nm Nmi)
              * (1 + Frob (ModularGroup.T ^ k)) ^ max Nm Nmi) :=
            mul_le_mul hS hT (frob6_nonneg _) (by norm_num)
    calc frob6 (sigmaHom (wblk (true, k)))
        ≤ 200 * ((36 * ((max Cm Cmi : ℕ) : ℝ) * 2 ^ max Nm Nmi)
            * (1 + Frob (wblk (true, k))) ^ max Nm Nmi) := h1
      _ ≤ (200 * (36 * ((max Cm Cmi : ℕ) : ℝ) * 2 ^ max Nm Nmi))
            * (1 + Frob (wblk (true, k))) ^ max Nm Nmi := le_of_eq (by ring)

/-- The product `letterProd` of a list of letters agrees with the product of `1 + Frob (w i)`
for a factorization `w = wblk ∘ L`. -/
lemma letterProd_eq_prod {n : ℕ} (w : Fin n → SL(2,ℤ)) (L : List (Bool × ℤ))
    (hLmap : L.map wblk = List.ofFn w) :
    letterProd L = ∏ i : Fin n, (1 + Frob (w i)) := by
  have h1 : L.map (fun l => 1 + Frob (wblk l)) = (L.map wblk).map (fun γ => 1 + Frob γ) :=
    (List.map_map (f := wblk) (g := fun γ => 1 + Frob γ)).symm
  rw [letterProd, h1, hLmap, List.map_ofFn, List.prod_ofFn]
  rfl

/-- **CKMRV, Lemma `lem:polynomiallybounded`, for the odd representation.**  The entries of
`σ(γ)` grow at most polynomially in the Frobenius norm of `γ`.  The proof factors `γ` into
blocks `T^k` and `S T^k` (`Work.Asymptotics.block_factorization`), bounds `frob6` of the
individual blocks through the explicit powers `oddMT^k`, `oddMTi^k`
(`Work.Asymptotics.oddMT_pow_entry_bound`) and uses the submultiplicativity of `frob6`; the
number of blocks is `O(log (1 + Frob γ))`, so the exponential `K^n` is again polynomial. -/
theorem sigmaHom_entry_bound :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∀ i j : Fin 6,
        ‖sigmaHom γ i j‖ ≤ C * (1 + Frob γ) ^ N := by
  obtain ⟨K, hK0, M, hletter⟩ := frob6_sigmaHom_wblk_bound
  obtain ⟨K0, hK0'⟩ : ∃ K0 : ℕ, K ≤ 2 ^ K0 := by
    obtain ⟨m, hm⟩ := exists_nat_gt K
    exact ⟨m, le_of_lt (lt_of_lt_of_le hm (by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le))⟩
  obtain ⟨Cb, Nb, hCb0, hNb0, hbf⟩ := block_factorization
  obtain ⟨Cb', Nb', hCb'⟩ := rpow_to_pow (le_of_lt hCb0) hNb0
  refine ⟨40000 * (2 * (Cb' : ℝ)) ^ (K0 + M), ((Nb' * (K0 + M) : ℕ) : ℝ),
    by positivity, by positivity, ?_⟩
  intro γ i j
  obtain ⟨n, w, δ, hδ, hw, hprod, hn, hprodFrob⟩ := hbf γ
  -- choose the list of letters
  have hblk : ∀ i : Fin n, ∃ p : Bool × ℤ, wblk p = w i := by
    intro i
    obtain ⟨k, hk⟩ := hw i
    rcases hk with hk | hk
    · exact ⟨(false, k), by rw [show wblk (false, k) = ModularGroup.T ^ k from rfl, hk]⟩
    · exact ⟨(true, k), by rw [show wblk (true, k) = ModularGroup.S * ModularGroup.T ^ k from rfl, hk]⟩
  set L : List (Bool × ℤ) := List.ofFn (fun i : Fin n => Classical.choose (hblk i)) with hLdef
  have hLget : ∀ i : Fin n, wblk (Classical.choose (hblk i)) = w i :=
    fun i => Classical.choose_spec (hblk i)
  have hLmap : L.map wblk = List.ofFn w := by
    rw [hLdef, List.map_ofFn]
    congr 1
    funext i
    exact hLget i
  have hx1 : (1 : ℝ) ≤ 1 + Frob γ := by linarith [Frob_nonneg γ]
  -- the product of the letters
  have hPle : letterProd L ≤ (Cb' : ℝ) * (1 + Frob γ) ^ Nb' := by
    rw [letterProd_eq_prod w L hLmap]
    exact le_trans hprodFrob (hCb' _ hx1)
  have hPm : letterProd L ≤ 2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb' := by
    have h2 : (0 : ℝ) ≤ (Cb' : ℝ) * (1 + Frob γ) ^ Nb' := by positivity
    linarith [hPle, h2]
  -- the growth of the whole product
  have hsig : sigmaHom γ = ((L.map (fun l => sigmaHom (wblk l))).prod) * sigmaHom δ := by
    rw [← hprod, map_mul]
    congr 1
    rw [← hLmap, map_list_prod, List.map_map]
    rfl
  have hstep1 : frob6 (sigmaHom γ) ≤ (K ^ L.length * (letterProd L) ^ M) * 40000 := by
    rw [hsig]
    have h1 : frob6 ((L.map (fun l => sigmaHom (wblk l))).prod * sigmaHom δ)
        ≤ frob6 ((L.map (fun l => sigmaHom (wblk l))).prod) * 200 :=
      le_trans (frob6_mul_le _ _)
        (mul_le_mul_of_nonneg_left (frob6_sigmaHom_base_le δ hδ) (frob6_nonneg _))
    have h2 : frob6 ((L.map (fun l => sigmaHom (wblk l))).prod)
        ≤ 200 * (L.map (fun l => frob6 (sigmaHom (wblk l)))).prod := frob6_list_prod_le L _
    have h3 : (L.map (fun l => frob6 (sigmaHom (wblk l)))).prod
        ≤ (L.map (fun l => K * (1 + Frob (wblk l)) ^ M)).prod :=
      cf_prod_map_le L _ _ (fun l _ => hletter l) (fun l _ => frob6_nonneg _)
    have h4 : (L.map (fun l => K * (1 + Frob (wblk l)) ^ M)).prod
        = K ^ L.length * (letterProd L) ^ M := by
      rw [cf_prod_map_mul_pow, letterProd]
    have h5 : (L.map (fun l => frob6 (sigmaHom (wblk l)))).prod * 40000
        ≤ (K ^ L.length * (letterProd L) ^ M) * 40000 :=
      mul_le_mul_of_nonneg_right (le_trans h3 (le_of_eq h4)) (by norm_num)
    calc frob6 ((L.map (fun l => sigmaHom (wblk l))).prod * sigmaHom δ)
        ≤ frob6 ((L.map (fun l => sigmaHom (wblk l))).prod) * 200 := h1
      _ ≤ (200 * (L.map (fun l => frob6 (sigmaHom (wblk l)))).prod) * 200 :=
          mul_le_mul_of_nonneg_right h2 (by norm_num)
      _ = (L.map (fun l => frob6 (sigmaHom (wblk l)))).prod * 40000 := by ring
      _ ≤ (K ^ L.length * (letterProd L) ^ M) * 40000 := h5
  -- absorption of the number of blocks
  have hKl : K ^ L.length ≤ (letterProd L) ^ K0 := by
    have h2n : (2 : ℝ) ^ L.length ≤ letterProd L :=
      cf_two_pow_length_le_prod L _ fun l _ => by have := one_le_Frob_blk l; linarith
    have h1 : K ^ L.length ≤ ((2 : ℝ) ^ K0) ^ L.length := pow_le_pow_left₀ hK0 hK0' _
    have h2 : ((2 : ℝ) ^ K0) ^ L.length = ((2 : ℝ) ^ L.length) ^ K0 := by
      rw [← pow_mul, ← pow_mul]; ring_nf
    have h3 : ((2 : ℝ) ^ L.length) ^ K0 ≤ (letterProd L) ^ K0 :=
      pow_le_pow_left₀ (by positivity) h2n K0
    rw [h2] at h1
    exact le_trans h1 h3
  have hstep2 : (K ^ L.length * (letterProd L) ^ M) * 40000
      ≤ 40000 * (letterProd L) ^ (K0 + M) := by
    have h4 : (0 : ℝ) ≤ (letterProd L) ^ M := pow_nonneg (letterProd_nonneg L) M
    have h5 : (0 : ℝ) ≤ (letterProd L) ^ (K0 + M) := pow_nonneg (letterProd_nonneg L) _
    calc (K ^ L.length * (letterProd L) ^ M) * 40000
        ≤ ((letterProd L) ^ K0 * (letterProd L) ^ M) * 40000 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKl h4) (by norm_num)
      _ = (letterProd L) ^ (K0 + M) * 40000 := by rw [← pow_add]
      _ ≤ 40000 * (letterProd L) ^ (K0 + M) := by linarith
  have hstep3 : 40000 * (letterProd L) ^ (K0 + M)
      ≤ 40000 * (2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb') ^ (K0 + M) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (letterProd_nonneg L) hPm _) (by norm_num)
  have hfin : 40000 * (2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb') ^ (K0 + M)
      = (40000 * (2 * (Cb' : ℝ)) ^ (K0 + M)) * (1 + Frob γ) ^ (Nb' * (K0 + M)) := by
    have h2 : (2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb')
        = (2 * (Cb' : ℝ)) * (1 + Frob γ) ^ Nb' := by ring
    rw [h2, mul_pow, ← pow_mul, ← mul_assoc]
  calc ‖sigmaHom γ i j‖ ≤ frob6 (sigmaHom γ) := entry_le_frob6 _ i j
    _ ≤ (K ^ L.length * (letterProd L) ^ M) * 40000 := hstep1
    _ ≤ 40000 * (letterProd L) ^ (K0 + M) := hstep2
    _ ≤ 40000 * (2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb') ^ (K0 + M) := hstep3
    _ = (40000 * (2 * (Cb' : ℝ)) ^ (K0 + M)) * (1 + Frob γ) ^ (Nb' * (K0 + M)) := hfin
    _ = (40000 * (2 * (Cb' : ℝ)) ^ (K0 + M)) * (1 + Frob γ) ^ ((Nb' * (K0 + M) : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]


/-! ## The twisted carries of the blocks `T^k` (`k : ℤ`) and `S T^k` -/

lemma Frob_T_zpow_neg (k : ℤ) :
    Frob (ModularGroup.T ^ (-k)) = Frob (ModularGroup.T ^ k) := by
  rw [Frob_T_zpow, Frob_T_zpow]
  congr 1
  push_cast
  ring

/-- Monotonicity of a polynomial bound for `coeffNorm` in the constant and the exponent. -/
lemma coeffNorm_le_of_pow {X : R} {C C' y : ℝ} {N N' : ℕ} (hC : C ≤ C') (hC0 : 0 ≤ C)
    (hy : 1 ≤ y) (hN : N ≤ N') (h : coeffNorm X ≤ C * y ^ N) :
    coeffNorm X ≤ C' * y ^ N' := by
  refine le_trans h ?_
  calc C * y ^ N ≤ C' * y ^ N := mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ C' * y ^ N' := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy hN) (le_trans hC0 hC)

/-- Monotonicity of a polynomial bound for `supportFrobLe` in the constant and the exponent. -/
lemma supportFrobLe_le_of_pow {X : R} {C C' y : ℝ} {N N' : ℕ} (hC : C ≤ C') (hC0 : 0 ≤ C)
    (hy : 1 ≤ y) (hN : N ≤ N') (h : supportFrobLe X (C * y ^ N)) :
    supportFrobLe X (C' * y ^ N') :=
  supportFrobLe_mono h (by
    calc C * y ^ N ≤ C' * y ^ N := mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ C' * y ^ N' := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy hN) (le_trans hC0 hC))

lemma one_le_one_add_Frob_T (k : ℤ) : (1 : ℝ) ≤ 1 + Frob (ModularGroup.T ^ k) := by
  linarith [Frob_nonneg (ModularGroup.T ^ k)]

/-- **The twisted carries of the blocks `T^k`** (`k : ℤ`), by the inversion law. -/
theorem Tblock_spec : ∀ (k : ℤ) (i : Fin 6),
    carryCombOdd (TblockA k i) (TblockB k i) = twist (ModularGroup.T ^ k) i := by
  intro k i
  by_cases hk : 0 ≤ k
  · have hk1 : (ModularGroup.T : SL(2,ℤ)) ^ (((k.toNat : ℕ)) : ℤ) = ModularGroup.T ^ k := by
      rw [Int.toNat_of_nonneg hk]
    rw [TblockA, TblockB, if_pos hk, if_pos hk, Tpow_spec k.toNat i, hk1]
  · have hnorm : ¬ (0 ≤ k) := hk
    have hm : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    set m : ℕ := (-k).toNat with hmdef
    have hcast : ((m : ℕ) : ℤ) = -k := hm
    -- the inversion law for `T^m`
    have hA : twist (ModularGroup.T ^ (-((m : ℕ) : ℤ))) i
        = - (∑ j : Fin 6, (oddMTi ^ m) i j • carryCombOdd (TpowA m j) (TpowB m j))
          * ofSL (ModularGroup.T ^ (-((m : ℕ) : ℤ))) := by
      have h := twist_inv (ModularGroup.T ^ ((m : ℕ) : ℤ)) i
      rw [← _root_.zpow_neg] at h
      rw [sigmaHom_T_zpow_neg m] at h
      have h1 : ∀ j : Fin 6, twist (ModularGroup.T ^ ((m : ℕ) : ℤ)) j
          = carryCombOdd (TpowA m j) (TpowB m j) := fun j => (Tpow_spec m j).symm
      simp only [h1] at h
      exact h
    have hTk : (ModularGroup.T : SL(2,ℤ)) ^ (-((m : ℕ) : ℤ)) = ModularGroup.T ^ k := by
      rw [hcast, neg_neg]
    rw [hTk] at hA
    rw [← carryCombOdd_sum_univ] at hA
    rw [← neg_one_smul ℂ (carryCombOdd _ _), ← carryCombOdd_smul, ← carryCombOdd_mul_of,
      neg_one_smul ℂ (∑ j : Fin 6, (oddMTi ^ m) i j • TpowA m j),
      neg_one_smul ℂ (∑ j : Fin 6, (oddMTi ^ m) i j • TpowB m j)] at hA
    have hR : (R_Tinv : R) ^ m = ofSL (ModularGroup.T ^ k) := by
      rw [R_Tinv_pow, hTk]
    rw [TblockA, TblockB, if_neg hnorm, if_neg hnorm, hR]
    exact hA.symm

/-- **Polynomial bounds for the twisted carries of the blocks `T^k`.** -/
theorem Tblock_bound : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ (k : ℤ) (i : Fin 6),
    coeffNorm (TblockA k i) ≤ C * (1 + Frob (ModularGroup.T ^ k)) ^ N ∧
    coeffNorm (TblockB k i) ≤ C * (1 + Frob (ModularGroup.T ^ k)) ^ N ∧
    supportFrobLe (TblockA k i) (C * (1 + Frob (ModularGroup.T ^ k)) ^ N) ∧
    supportFrobLe (TblockB k i) (C * (1 + Frob (ModularGroup.T ^ k)) ^ N) := by
  obtain ⟨Ct, hCt, Nt, ht⟩ := Tpow_bound_Frob
  obtain ⟨Cm, Nm, hCm⟩ := oddMTi_entry_bound_nat
  have hCm0 : (0 : ℝ) ≤ (Cm : ℝ) := Nat.cast_nonneg Cm
  refine ⟨max (6 * (Cm : ℝ) * 2 ^ Nm * Ct) Ct, by positivity, max (Nm + Nt) (Nt + 1), ?_⟩
  intro k i
  set y : ℝ := 1 + Frob (ModularGroup.T ^ k) with hy
  have hy1 : (1 : ℝ) ≤ y := by rw [hy]; exact one_le_one_add_Frob_T k
  have hy0 : (0 : ℝ) ≤ y := le_trans zero_le_one hy1
  have hCle : Ct ≤ max (6 * (Cm : ℝ) * 2 ^ Nm * Ct) Ct := le_max_right _ _
  have hCle2 : 6 * (Cm : ℝ) * 2 ^ Nm * Ct ≤ max (6 * (Cm : ℝ) * 2 ^ Nm * Ct) Ct :=
    le_max_left _ _
  have hCle2' : (0 : ℝ) ≤ 6 * (Cm : ℝ) * 2 ^ Nm * Ct := by positivity
  have hNle : Nt ≤ max (Nm + Nt) (Nt + 1) := le_trans (Nat.le_add_left _ _) (le_max_left _ _)
  have hNle2 : Nm + Nt ≤ max (Nm + Nt) (Nt + 1) := le_max_left _ _
  have hNle3 : Nt + 1 ≤ max (Nm + Nt) (Nt + 1) := le_max_right _ _
  by_cases hk : 0 ≤ k
  · have hk1 : (ModularGroup.T : SL(2,ℤ)) ^ (((k.toNat : ℕ)) : ℤ) = ModularGroup.T ^ k := by
      rw [Int.toNat_of_nonneg hk]
    have hcoeA : coeffNorm (TblockA k i) ≤ Ct * y ^ Nt := by
      rw [TblockA, if_pos hk, hy, ← hk1]
      exact (ht k.toNat i).1
    have hcoeB : coeffNorm (TblockB k i) ≤ Ct * y ^ Nt := by
      rw [TblockB, if_pos hk, hy, ← hk1]
      exact (ht k.toNat i).2.1
    have hsupA : supportFrobLe (TblockA k i) (Ct * y ^ Nt) := by
      rw [TblockA, if_pos hk, hy, ← hk1]
      exact (ht k.toNat i).2.2.1
    have hsupB : supportFrobLe (TblockB k i) (Ct * y ^ Nt) := by
      rw [TblockB, if_pos hk, hy, ← hk1]
      exact (ht k.toNat i).2.2.2
    exact ⟨coeffNorm_le_of_pow hCle hCt hy1 hNle hcoeA,
      coeffNorm_le_of_pow hCle hCt hy1 hNle hcoeB,
      supportFrobLe_le_of_pow hCle hCt hy1 hNle hsupA,
      supportFrobLe_le_of_pow hCle hCt hy1 hNle hsupB⟩
  · have hnorm : ¬ (0 ≤ k) := hk
    have hm : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have hcast : ((((-k).toNat : ℕ)) : ℝ) = ((-k : ℤ) : ℝ) := by exact_mod_cast hm
    have hmFrob : ((((-k).toNat : ℕ)) : ℝ) ≤ Frob (ModularGroup.T ^ k) := by
      rw [hcast, Int.cast_neg]
      calc -((k : ℝ)) ≤ |(k : ℝ)| := neg_le_abs _
        _ ≤ Frob (ModularGroup.T ^ k) := abs_le_Frob_T_zpow k
    have hbase2 : (2 : ℝ) + ((((-k).toNat : ℕ)) : ℝ) ≤ 2 * y := by rw [hy]; linarith
    have hpow2 : (2 + ((((-k).toNat : ℕ)) : ℝ)) ^ Nm ≤ 2 ^ Nm * y ^ Nm := by
      have h := pow_le_pow_left₀ (by linarith) hbase2 Nm
      rwa [mul_pow] at h
    have hFeq : Frob (ModularGroup.T ^ (((-k).toNat : ℕ) : ℤ)) = Frob (ModularGroup.T ^ k) := by
      rw [show (((-k).toNat : ℕ) : ℤ) = -k from hm, Frob_T_zpow_neg]
    have hTA : ∀ j : Fin 6, coeffNorm (TpowA (-k).toNat j) ≤ Ct * y ^ Nt := by
      intro j; rw [hy, ← hFeq]; exact (ht (-k).toNat j).1
    have hTB : ∀ j : Fin 6, coeffNorm (TpowB (-k).toNat j) ≤ Ct * y ^ Nt := by
      intro j; rw [hy, ← hFeq]; exact (ht (-k).toNat j).2.1
    have hSA : ∀ j : Fin 6, supportFrobLe (TpowA (-k).toNat j) (Ct * y ^ Nt) := by
      intro j; rw [hy, ← hFeq]; exact (ht (-k).toNat j).2.2.1
    have hSB : ∀ j : Fin 6, supportFrobLe (TpowB (-k).toNat j) (Ct * y ^ Nt) := by
      intro j; rw [hy, ← hFeq]; exact (ht (-k).toNat j).2.2.2
    have hcoeA : coeffNorm (TblockA k i) ≤ (6 * (Cm : ℝ) * 2 ^ Nm * Ct) * y ^ (Nm + Nt) := by
      rw [TblockA, if_neg hnorm, neg_mul, R_Tinv_pow]
      refine le_trans (coeffNorm_neg_le _) ?_
      refine le_trans (coeffNorm_mul_of_le _ _) ?_
      calc coeffNorm (∑ j : Fin 6, (oddMTi ^ (-k).toNat) i j • TpowA (-k).toNat j)
          ≤ ∑ j : Fin 6, ‖(oddMTi ^ (-k).toNat) i j‖ * coeffNorm (TpowA (-k).toNat j) :=
            coeffNorm_smul_sum_le _ _ _
        _ ≤ ∑ _j : Fin 6, ((Cm : ℝ) * 2 ^ Nm * y ^ Nm) * (Ct * y ^ Nt) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h1 : ‖(oddMTi ^ (-k).toNat) i j‖ ≤ ((Cm : ℝ) * 2 ^ Nm) * y ^ Nm := by
              calc ‖(oddMTi ^ (-k).toNat) i j‖
                  ≤ (Cm : ℝ) * (2 + ((((-k).toNat : ℕ)) : ℝ)) ^ Nm := hCm (-k).toNat i j
                _ ≤ (Cm : ℝ) * (2 ^ Nm * y ^ Nm) := mul_le_mul_of_nonneg_left hpow2 hCm0
                _ = ((Cm : ℝ) * 2 ^ Nm) * y ^ Nm := by ring
            exact mul_le_mul h1 (hTA j) (coeffNorm_nonneg _) (by positivity)
        _ = 6 * (((Cm : ℝ) * 2 ^ Nm * y ^ Nm) * (Ct * y ^ Nt)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            norm_num
        _ = (6 * (Cm : ℝ) * 2 ^ Nm * Ct) * y ^ (Nm + Nt) := by rw [pow_add]; ring
    have hcoeB : coeffNorm (TblockB k i) ≤ (6 * (Cm : ℝ) * 2 ^ Nm * Ct) * y ^ (Nm + Nt) := by
      rw [TblockB, if_neg hnorm, neg_mul, R_Tinv_pow]
      refine le_trans (coeffNorm_neg_le _) ?_
      refine le_trans (coeffNorm_mul_of_le _ _) ?_
      calc coeffNorm (∑ j : Fin 6, (oddMTi ^ (-k).toNat) i j • TpowB (-k).toNat j)
          ≤ ∑ j : Fin 6, ‖(oddMTi ^ (-k).toNat) i j‖ * coeffNorm (TpowB (-k).toNat j) :=
            coeffNorm_smul_sum_le _ _ _
        _ ≤ ∑ _j : Fin 6, ((Cm : ℝ) * 2 ^ Nm * y ^ Nm) * (Ct * y ^ Nt) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h1 : ‖(oddMTi ^ (-k).toNat) i j‖ ≤ ((Cm : ℝ) * 2 ^ Nm) * y ^ Nm := by
              calc ‖(oddMTi ^ (-k).toNat) i j‖
                  ≤ (Cm : ℝ) * (2 + ((((-k).toNat : ℕ)) : ℝ)) ^ Nm := hCm (-k).toNat i j
                _ ≤ (Cm : ℝ) * (2 ^ Nm * y ^ Nm) := mul_le_mul_of_nonneg_left hpow2 hCm0
                _ = ((Cm : ℝ) * 2 ^ Nm) * y ^ Nm := by ring
            exact mul_le_mul h1 (hTB j) (coeffNorm_nonneg _) (by positivity)
        _ = 6 * (((Cm : ℝ) * 2 ^ Nm * y ^ Nm) * (Ct * y ^ Nt)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            norm_num
        _ = (6 * (Cm : ℝ) * 2 ^ Nm * Ct) * y ^ (Nm + Nt) := by rw [pow_add]; ring
    have hsupA : supportFrobLe (TblockA k i) (Ct * y ^ (Nt + 1)) := by
      rw [TblockA, if_neg hnorm, neg_mul, R_Tinv_pow]
      refine supportFrobLe_neg ?_
      refine supportFrobLe_mono (supportFrobLe_mul_of
        (supportFrobLe_smul_sum Finset.univ _ _ (fun j _ => hSA j))
        (ModularGroup.T ^ (-((((-k).toNat : ℕ)) : ℤ)))) ?_
      calc Ct * y ^ Nt * Frob (ModularGroup.T ^ (-((((-k).toNat : ℕ)) : ℤ)))
          = Ct * y ^ Nt * Frob (ModularGroup.T ^ k) := by
            rw [show (-((((-k).toNat : ℕ)) : ℤ)) = k from by
                rw [show (((-k).toNat : ℕ) : ℤ) = -k from hm]; ring]
        _ ≤ Ct * y ^ Nt * y := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hy]; linarith [Frob_nonneg (ModularGroup.T ^ k)]
        _ = Ct * y ^ (Nt + 1) := by rw [pow_succ]; ring
    have hsupB : supportFrobLe (TblockB k i) (Ct * y ^ (Nt + 1)) := by
      rw [TblockB, if_neg hnorm, neg_mul, R_Tinv_pow]
      refine supportFrobLe_neg ?_
      refine supportFrobLe_mono (supportFrobLe_mul_of
        (supportFrobLe_smul_sum Finset.univ _ _ (fun j _ => hSB j))
        (ModularGroup.T ^ (-((((-k).toNat : ℕ)) : ℤ)))) ?_
      calc Ct * y ^ Nt * Frob (ModularGroup.T ^ (-((((-k).toNat : ℕ)) : ℤ)))
          = Ct * y ^ Nt * Frob (ModularGroup.T ^ k) := by
            rw [show (-((((-k).toNat : ℕ)) : ℤ)) = k from by
                rw [show (((-k).toNat : ℕ) : ℤ) = -k from hm]; ring]
        _ ≤ Ct * y ^ Nt * y := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hy]; linarith [Frob_nonneg (ModularGroup.T ^ k)]
        _ = Ct * y ^ (Nt + 1) := by rw [pow_succ]; ring
    exact ⟨coeffNorm_le_of_pow hCle2 hCle2' hy1 hNle2 hcoeA,
      coeffNorm_le_of_pow hCle2 hCle2' hy1 hNle2 hcoeB,
      supportFrobLe_le_of_pow hCle hCt hy1 hNle3 hsupA,
      supportFrobLe_le_of_pow hCle hCt hy1 hNle3 hsupB⟩


/-! ## The twisted carries of the blocks `S T^k` -/

/-- **The twisted carries of the blocks `S T^k`**, by the cocycle with the atom `S`. -/
theorem STblock_spec : ∀ (k : ℤ) (i : Fin 6),
    carryCombOdd (STblockA k i) (STblockB k i) = twist (ModularGroup.S * ModularGroup.T ^ k) i := by
  intro k i
  rw [twist_cocycle ModularGroup.S (ModularGroup.T ^ k) i]
  rw [STblockA, STblockB, carryCombOdd_add, carryCombOdd_sum_univ, carryCombOdd_mul_of]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Tblock_spec k j, sigmaHom_S]
  · rw [twist_atomS_odd.1 i]

/-- **Polynomial bounds for the twisted carries of the blocks `S T^k`.** -/
theorem STblock_bound : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ (k : ℤ) (i : Fin 6),
    coeffNorm (STblockA k i) ≤ C * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ N ∧
    coeffNorm (STblockB k i) ≤ C * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ N ∧
    supportFrobLe (STblockA k i) (C * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ N) ∧
    supportFrobLe (STblockB k i) (C * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ N) := by
  obtain ⟨Ct, hCt, Nt, ht⟩ := Tblock_bound
  have hA4 : ∀ i : Fin 6, coeffNorm (atomSA i) ≤ (4 : ℝ) := fun i => (twist_atomS_odd.2 i).1
  have hB4 : ∀ i : Fin 6, coeffNorm (atomSB i) ≤ (4 : ℝ) := fun i => (twist_atomS_odd.2 i).2.1
  have hA8 : ∀ i : Fin 6, supportFrobLe (atomSA i) (8 : ℝ) := fun i => (twist_atomS_odd.2 i).2.2.1
  have hB8 : ∀ i : Fin 6, supportFrobLe (atomSB i) (8 : ℝ) := fun i => (twist_atomS_odd.2 i).2.2.2
  refine ⟨12 * Ct + 8, by positivity, max Nt 1, fun k i => ?_⟩
  set y : ℝ := 1 + Frob (ModularGroup.S * ModularGroup.T ^ k) with hy
  have hys : (1 : ℝ) ≤ 1 + Frob (ModularGroup.S * ModularGroup.T ^ k) := by
    rw [Frob_ST_zpow]
    linarith [Real.sqrt_nonneg ((k : ℝ) ^ 2 + 2)]
  have hy1 : (1 : ℝ) ≤ y := by rw [hy]; exact hys
  have hTblock : ∀ j : Fin 6,
      coeffNorm (TblockA k j) ≤ Ct * y ^ Nt ∧ coeffNorm (TblockB k j) ≤ Ct * y ^ Nt ∧
      supportFrobLe (TblockA k j) (Ct * y ^ Nt) ∧
      supportFrobLe (TblockB k j) (Ct * y ^ Nt) := by
    intro j
    have hF : Frob (ModularGroup.S * ModularGroup.T ^ k) = Frob (ModularGroup.T ^ k) :=
      (Frob_ST_zpow k).trans (Frob_T_zpow k).symm
    have h1 := ht k j
    rw [hy, hF]
    exact h1
  have hCt0 : (0 : ℝ) ≤ Ct := hCt
  have hC1200 : (0 : ℝ) ≤ 12 * Ct := by positivity
  have hle1200 : Ct ≤ 12 * Ct + 8 := by linarith
  have hNle : Nt ≤ max Nt 1 := le_max_left _ _
  have hkey : ∀ B : ℝ, 0 ≤ B → B ≤ Ct * y ^ Nt →
      B ≤ (12 * Ct + 8) * y ^ (max Nt 1) := by
    intro B hB0 hB
    have h4 : y ^ Nt ≤ y ^ (max Nt 1) := pow_le_pow_right₀ hy1 hNle
    calc B ≤ Ct * y ^ Nt := hB
      _ ≤ Ct * y ^ (max Nt 1) := mul_le_mul_of_nonneg_left h4 hCt0
      _ ≤ (12 * Ct + 8) * y ^ (max Nt 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hy0 : (0 : ℝ) ≤ y := le_trans zero_le_one hy1
  have hyN0 : (0 : ℝ) ≤ y ^ Nt := pow_nonneg hy0 Nt
  have hyM0 : (0 : ℝ) ≤ y ^ (max Nt 1) := pow_nonneg hy0 _
  have hfinal : ∀ B : ℝ, 0 ≤ B → B ≤ 6 * (2 * (Ct * y ^ Nt)) + 4 →
      B ≤ (12 * Ct + 8) * y ^ (max Nt 1) := by
    intro B hB0 hB
    have h5 : 6 * (2 * (Ct * y ^ Nt)) ≤ (12 * Ct) * y ^ (max Nt 1) := by
      calc 6 * (2 * (Ct * y ^ Nt)) = (12 * Ct) * y ^ Nt := by ring
        _ ≤ (12 * Ct) * y ^ (max Nt 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy1 hNle) hC1200
    have h6 : (4 : ℝ) ≤ 8 * y ^ (max Nt 1) := by
      have h3 : (1 : ℝ) ≤ y ^ (max Nt 1) := one_le_pow₀ hy1
      linarith
    have h8 : (12 * Ct) * y ^ (max Nt 1) + 8 * y ^ (max Nt 1)
        = (12 * Ct + 8) * y ^ (max Nt 1) := by ring
    linarith
  have hcoeA : coeffNorm (STblockA k i) ≤ (12 * Ct + 8) * y ^ (max Nt 1) := by
    rw [STblockA]
    refine hfinal _ (coeffNorm_nonneg _) ?_
    refine le_trans (coeffNorm_add_le _ _) ?_
    have h1 : coeffNorm (∑ j : Fin 6, oddMS i j • TblockA k j)
        ≤ 6 * (2 * (Ct * y ^ Nt)) := by
      refine le_trans (coeffNorm_smul_sum_le _ _ _) ?_
      calc ∑ j : Fin 6, ‖oddMS i j‖ * coeffNorm (TblockA k j)
          ≤ ∑ _j : Fin 6, 2 * (Ct * y ^ Nt) := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul (oddMS_entry_le i j) (hTblock j).1 (coeffNorm_nonneg _)
              (by norm_num)
        _ = 6 * (2 * (Ct * y ^ Nt)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            norm_num
    have h2 : coeffNorm (atomSA i * ofSL (ModularGroup.T ^ k)) ≤ (4 : ℝ) :=
      le_trans (coeffNorm_mul_of_le _ _) (hA4 i)
    linarith
  have hcoeB : coeffNorm (STblockB k i) ≤ (12 * Ct + 8) * y ^ (max Nt 1) := by
    rw [STblockB]
    refine hfinal _ (coeffNorm_nonneg _) ?_
    refine le_trans (coeffNorm_add_le _ _) ?_
    have h1 : coeffNorm (∑ j : Fin 6, oddMS i j • TblockB k j)
        ≤ 6 * (2 * (Ct * y ^ Nt)) := by
      refine le_trans (coeffNorm_smul_sum_le _ _ _) ?_
      calc ∑ j : Fin 6, ‖oddMS i j‖ * coeffNorm (TblockB k j)
          ≤ ∑ _j : Fin 6, 2 * (Ct * y ^ Nt) := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul (oddMS_entry_le i j) (hTblock j).2.1 (coeffNorm_nonneg _)
              (by norm_num)
        _ = 6 * (2 * (Ct * y ^ Nt)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            norm_num
    have h2 : coeffNorm (atomSB i * ofSL (ModularGroup.T ^ k)) ≤ (4 : ℝ) :=
      le_trans (coeffNorm_mul_of_le _ _) (hB4 i)
    linarith
  have hsupA : supportFrobLe (STblockA k i) ((12 * Ct + 8) * y ^ (max Nt 1)) := by
    have h1 : supportFrobLe (∑ j : Fin 6, oddMS i j • TblockA k j) (Ct * y ^ Nt) :=
      supportFrobLe_smul_sum Finset.univ _ _ (fun j _ => (hTblock j).2.2.1)
    have h2 : supportFrobLe (atomSA i * ofSL (ModularGroup.T ^ k)) (8 * y) := by
      refine supportFrobLe_mono (supportFrobLe_mul_of (hA8 i) (ModularGroup.T ^ k)) ?_
      have hF : Frob (ModularGroup.T ^ k) = Frob (ModularGroup.S * ModularGroup.T ^ k) :=
        (Frob_T_zpow k).trans (Frob_ST_zpow k).symm
      rw [hF, hy]
      linarith [Frob_nonneg (ModularGroup.S * ModularGroup.T ^ k)]
    have h3 : Ct * y ^ Nt ≤ (12 * Ct + 8) * y ^ (max Nt 1) :=
      hkey _ (mul_nonneg hCt0 hyN0) (le_refl _)
    have h4 : 8 * y ≤ (12 * Ct + 8) * y ^ (max Nt 1) := by
      have h5 : (1 : ℝ) ≤ y ^ (max Nt 1) := one_le_pow₀ hy1
      calc 8 * y ≤ 8 * y ^ (max Nt 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            calc y = y ^ 1 := (pow_one _).symm
              _ ≤ y ^ (max Nt 1) := pow_le_pow_right₀ hy1 (by omega)
        _ ≤ (12 * Ct + 8) * y ^ (max Nt 1) := by nlinarith [h5, hCt0]
    rw [STblockA]
    exact supportFrobLe_mono (supportFrobLe_add h1 h2) (max_le h3 h4)
  have hsupB : supportFrobLe (STblockB k i) ((12 * Ct + 8) * y ^ (max Nt 1)) := by
    have h1 : supportFrobLe (∑ j : Fin 6, oddMS i j • TblockB k j) (Ct * y ^ Nt) :=
      supportFrobLe_smul_sum Finset.univ _ _ (fun j _ => (hTblock j).2.2.2)
    have h2 : supportFrobLe (atomSB i * ofSL (ModularGroup.T ^ k)) (8 * y) := by
      refine supportFrobLe_mono (supportFrobLe_mul_of (hB8 i) (ModularGroup.T ^ k)) ?_
      have hF : Frob (ModularGroup.T ^ k) = Frob (ModularGroup.S * ModularGroup.T ^ k) :=
        (Frob_T_zpow k).trans (Frob_ST_zpow k).symm
      rw [hF, hy]
      linarith [Frob_nonneg (ModularGroup.S * ModularGroup.T ^ k)]
    have h3 : Ct * y ^ Nt ≤ (12 * Ct + 8) * y ^ (max Nt 1) :=
      hkey _ (mul_nonneg hCt0 hyN0) (le_refl _)
    have h4 : 8 * y ≤ (12 * Ct + 8) * y ^ (max Nt 1) := by
      have h5 : (1 : ℝ) ≤ y ^ (max Nt 1) := one_le_pow₀ hy1
      calc 8 * y ≤ 8 * y ^ (max Nt 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            calc y = y ^ 1 := (pow_one _).symm
              _ ≤ y ^ (max Nt 1) := pow_le_pow_right₀ hy1 (by omega)
        _ ≤ (12 * Ct + 8) * y ^ (max Nt 1) := by nlinarith [h5, hCt0]
    rw [STblockB]
    exact supportFrobLe_mono (supportFrobLe_add h1 h2) (max_le h3 h4)
  exact ⟨hcoeA, hcoeB, hsupA, hsupB⟩


/-! ## The twisted carries of the base elements `1, -1, S, -S` -/

theorem base_carry_spec :
    ∀ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) →
      ∃ dA dB : Fin 6 → R,
        (∀ j : Fin 6, twist δ j = carryCombOdd (dA j) (dB j)) ∧
        (∀ j : Fin 6, coeffNorm (dA j) ≤ 4 ∧
          coeffNorm (dB j) ≤ 4 ∧
          supportFrobLe (dA j) 8 ∧
          supportFrobLe (dB j) 8) := by
  intro δ hδ
  have hz : ∀ j : Fin 6, coeffNorm ((0 : Fin 6 → R) j) ≤ 4 ∧
      coeffNorm ((0 : Fin 6 → R) j) ≤ 4 ∧
      supportFrobLe ((0 : Fin 6 → R) j) 8 ∧ supportFrobLe ((0 : Fin 6 → R) j) 8 := by
    intro j
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Pi.zero_apply] <;>
      first
        | rw [coeffNorm_zero]; norm_num
        | exact supportFrobLe_zero 8
  rcases hδ with h | h | h | h
  · subst h
    refine ⟨fun _ => 0, fun _ => 0, fun j => ?_, hz⟩
    rw [twist_one, carryCombOdd_zero]
  · subst h
    refine ⟨fun _ => 0, fun _ => 0, fun j => ?_, hz⟩
    rw [twist_neg_one, carryCombOdd_zero]
  · subst h
    exact ⟨atomSA, atomSB, fun j => (twist_atomS_odd.1 j).symm, fun j => twist_atomS_odd.2 j⟩
  · subst h
    refine ⟨fun j => -atomSA j, fun j => -atomSB j, fun j => ?_, fun j => ?_⟩
    · rw [twist_neg, ← twist_atomS_odd.1 j]
      rw [show -(carryCombOdd (atomSA j) (atomSB j))
          = carryCombOdd (-atomSA j) (-atomSB j) from by
        rw [← neg_one_smul ℂ (carryCombOdd (atomSA j) (atomSB j)), ← carryCombOdd_smul,
          neg_one_smul ℂ (atomSA j), neg_one_smul ℂ (atomSB j)]]
    · exact ⟨le_trans (coeffNorm_neg_le _) (twist_atomS_odd.2 j).1,
        le_trans (coeffNorm_neg_le _) (twist_atomS_odd.2 j).2.1,
        supportFrobLe_neg (twist_atomS_odd.2 j).2.2.1,
        supportFrobLe_neg (twist_atomS_odd.2 j).2.2.2⟩

/-! ## The per-letter data for the accumulated carries -/

lemma two_term_le {x : ℝ} (hx : 1 ≤ x) {K1 K2 C : ℝ} (hK : K1 + K2 ≤ C)
    (h1 : 0 ≤ K1) (h2 : 0 ≤ K2) {e1 e2 N : ℕ} (he1 : e1 ≤ N) (he2 : e2 ≤ N) :
    K1 * x ^ e1 + K2 * x ^ e2 ≤ C * x ^ N := by
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  calc K1 * x ^ e1 + K2 * x ^ e2 ≤ K1 * x ^ N + K2 * x ^ N :=
        add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx he1) h1)
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx he2) h2)
    _ = (K1 + K2) * x ^ N := by ring
    _ ≤ C * x ^ N := mul_le_mul_of_nonneg_right hK (pow_nonneg hx0 N)

lemma one_term_le {x : ℝ} (hx : 1 ≤ x) {K C : ℝ} (hK : K ≤ C) (h1 : 0 ≤ K) {e N : ℕ}
    (he : e ≤ N) : K * x ^ e ≤ C * x ^ N := by
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  calc K * x ^ e ≤ K * x ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx he) h1
    _ ≤ C * x ^ N := mul_le_mul_of_nonneg_right hK (pow_nonneg hx0 N)

lemma block_letters_data :
    ∃ Nsig Ncar : ℕ, Nsig ≤ Ncar ∧
      (∀ (l : Bool × ℤ) (i j : Fin 6),
        6 * ‖sigmaHom (wblk l) i j‖ ≤ (1 + Frob (wblk l)) ^ Nsig) ∧
      (∀ (l : Bool × ℤ) (i : Fin 6),
        coeffNorm (wblkA l i) ≤ (1 + Frob (wblk l)) ^ Ncar ∧
        coeffNorm (wblkB l i) ≤ (1 + Frob (wblk l)) ^ Ncar ∧
        supportFrobLe (wblkA l i) ((1 + Frob (wblk l)) ^ Ncar) ∧
        supportFrobLe (wblkB l i) ((1 + Frob (wblk l)) ^ Ncar)) := by
  obtain ⟨Cσ, Nσ, hCσ, hNσ, hσ⟩ := sigmaHom_entry_bound
  obtain ⟨Ct, hCt, Nt, ht⟩ := Tblock_bound
  obtain ⟨Cs, hCs, Ns, hs⟩ := STblock_bound
  obtain ⟨C1, N1, h1⟩ := rpow_to_pow (by positivity : 0 ≤ 6 * Cσ) hNσ
  obtain ⟨K1, hK1⟩ : ∃ K : ℕ, C1 ≤ 2 ^ K := ⟨C1, le_of_lt Nat.lt_two_pow_self⟩
  have hCW0 : (0 : ℝ) ≤ max Ct Cs := le_trans hCt (le_max_left _ _)
  obtain ⟨Kw, hKw⟩ : ∃ K : ℕ, max Ct Cs ≤ 2 ^ K := by
    obtain ⟨m, hm⟩ := exists_nat_gt (max Ct Cs)
    exact ⟨m, le_of_lt (lt_of_lt_of_le hm (by exact_mod_cast (Nat.lt_two_pow_self (n := m)).le))⟩
  have hstep : ∀ y : ℝ, 2 ≤ y → max Ct Cs * y ^ max Nt Ns ≤ y ^ (Kw + max Nt Ns) := by
    intro y hy2
    have hy1 : (1 : ℝ) ≤ y := by linarith
    have hy0 : (0 : ℝ) ≤ y := by linarith
    calc max Ct Cs * y ^ max Nt Ns ≤ 2 ^ Kw * y ^ max Nt Ns :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hKw) (pow_nonneg hy0 _)
      _ ≤ y ^ Kw * y ^ max Nt Ns :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hy2 Kw) (pow_nonneg hy0 _)
      _ = y ^ (Kw + max Nt Ns) := (pow_add _ _ _).symm
  refine ⟨K1 + N1, max (K1 + N1) (Kw + max Nt Ns), le_max_left _ _, ?_, ?_⟩
  · intro l i j
    have hx : (2 : ℝ) ≤ 1 + Frob (wblk l) := by
      have := one_le_Frob_blk l; linarith
    have hx1 : (1 : ℝ) ≤ 1 + Frob (wblk l) := by linarith
    have hx0 : (0 : ℝ) ≤ 1 + Frob (wblk l) := by linarith
    calc 6 * ‖sigmaHom (wblk l) i j‖ ≤ 6 * (Cσ * (1 + Frob (wblk l)) ^ Nσ) :=
          mul_le_mul_of_nonneg_left (hσ (wblk l) i j) (by norm_num)
      _ = (6 * Cσ) * (1 + Frob (wblk l)) ^ Nσ := by ring
      _ ≤ (C1 : ℝ) * (1 + Frob (wblk l)) ^ N1 := h1 _ hx1
      _ ≤ 2 ^ K1 * (1 + Frob (wblk l)) ^ N1 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hK1) (pow_nonneg hx0 _)
      _ ≤ (1 + Frob (wblk l)) ^ K1 * (1 + Frob (wblk l)) ^ N1 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hx K1) (pow_nonneg hx0 _)
      _ = (1 + Frob (wblk l)) ^ (K1 + N1) := (pow_add _ _ _).symm
  · intro l i
    rcases l with ⟨b, k⟩
    have hwF : wblk (false, k) = ModularGroup.T ^ k := by simp [wblk]
    have hwT : wblk (true, k) = ModularGroup.S * ModularGroup.T ^ k := by simp [wblk]
    have hAF : wblkA (false, k) i = TblockA k i := by simp [wblkA]
    have hBF : wblkB (false, k) i = TblockB k i := by simp [wblkB]
    have hAT : wblkA (true, k) i = STblockA k i := by simp [wblkA]
    have hBT : wblkB (true, k) i = STblockB k i := by simp [wblkB]
    have hF : Frob (ModularGroup.S * ModularGroup.T ^ k) = Frob (ModularGroup.T ^ k) :=
      (Frob_ST_zpow k).trans (Frob_T_zpow k).symm
    have hey : (1 : ℝ) ≤ 1 + Frob (ModularGroup.T ^ k) := by
      linarith [Frob_nonneg (ModularGroup.T ^ k)]
    have he2 : (2 : ℝ) ≤ 1 + Frob (ModularGroup.T ^ k) := by
      have h := one_le_Frob_blk (false, k); rw [hwF] at h; linarith
    have he2T : (2 : ℝ) ≤ 1 + Frob (ModularGroup.S * ModularGroup.T ^ k) := by
      rw [hF]; exact he2
    cases b
    · obtain ⟨hA, hB, sA, sB⟩ := ht k i
      have hA' : coeffNorm (TblockA k i) ≤ (1 + Frob (ModularGroup.T ^ k)) ^ (Kw + max Nt Ns) :=
        le_trans (coeffNorm_le_of_pow (le_max_left _ _) hCt hey (le_max_left _ _) hA)
          (hstep _ he2)
      have hB' : coeffNorm (TblockB k i) ≤ (1 + Frob (ModularGroup.T ^ k)) ^ (Kw + max Nt Ns) :=
        le_trans (coeffNorm_le_of_pow (le_max_left _ _) hCt hey (le_max_left _ _) hB)
          (hstep _ he2)
      have sA' : supportFrobLe (TblockA k i) ((1 + Frob (ModularGroup.T ^ k)) ^ (Kw + max Nt Ns)) :=
        supportFrobLe_mono (supportFrobLe_le_of_pow (le_max_left _ _) hCt hey (le_max_left _ _) sA)
          (hstep _ he2)
      have sB' : supportFrobLe (TblockB k i) ((1 + Frob (ModularGroup.T ^ k)) ^ (Kw + max Nt Ns)) :=
        supportFrobLe_mono (supportFrobLe_le_of_pow (le_max_left _ _) hCt hey (le_max_left _ _) sB)
          (hstep _ he2)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hAF, hwF]; exact le_trans hA' (pow_le_pow_right₀ hey (le_max_right _ _))
      · rw [hBF, hwF]; exact le_trans hB' (pow_le_pow_right₀ hey (le_max_right _ _))
      · rw [hAF, hwF]; exact supportFrobLe_mono sA' (pow_le_pow_right₀ hey (le_max_right _ _))
      · rw [hBF, hwF]; exact supportFrobLe_mono sB' (pow_le_pow_right₀ hey (le_max_right _ _))
    · obtain ⟨hA, hB, sA, sB⟩ := hs k i
      have hA' : coeffNorm (STblockA k i) ≤ (1 + Frob (ModularGroup.T ^ k)) ^ (Kw + max Nt Ns) :=
        le_trans (coeffNorm_le_of_pow (le_max_right _ _) hCs hey
          (le_max_right _ _) (by rw [← hF]; exact hA)) (hstep _ he2)
      have hB' : coeffNorm (STblockB k i) ≤ (1 + Frob (ModularGroup.T ^ k)) ^ (Kw + max Nt Ns) :=
        le_trans (coeffNorm_le_of_pow (le_max_right _ _) hCs hey
          (le_max_right _ _) (by rw [← hF]; exact hB)) (hstep _ he2)
      have sA' : supportFrobLe (STblockA k i) ((1 + Frob (ModularGroup.T ^ k)) ^ (Kw + max Nt Ns)) :=
        supportFrobLe_mono (supportFrobLe_le_of_pow (le_max_right _ _) hCs hey
          (le_max_right _ _) (by rw [← hF]; exact sA)) (hstep _ he2)
      have sB' : supportFrobLe (STblockB k i) ((1 + Frob (ModularGroup.T ^ k)) ^ (Kw + max Nt Ns)) :=
        supportFrobLe_mono (supportFrobLe_le_of_pow (le_max_right _ _) hCs hey
          (le_max_right _ _) (by rw [← hF]; exact sB)) (hstep _ he2)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hAT, hwT, hF]; exact le_trans hA' (pow_le_pow_right₀ hey (le_max_right _ _))
      · rw [hBT, hwT, hF]; exact le_trans hB' (pow_le_pow_right₀ hey (le_max_right _ _))
      · rw [hAT, hwT, hF]; exact supportFrobLe_mono sA' (pow_le_pow_right₀ hey (le_max_right _ _))
      · rw [hBT, hwT, hF]; exact supportFrobLe_mono sB' (pow_le_pow_right₀ hey (le_max_right _ _))


/-! ## The assembly: the twisted carries of `γ` modulo the odd ideal

Everything is reduced to the pair of `(T-1)²`- and `S(T-1)²`-components `A`, `B` of the twisted
carry `(1-z)·rowDiffOdd γ 0`, which are built from the per-block data by the cocycle. -/

theorem carry_twist_odd_aux :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (∀ i j : Fin 6, ‖sigmaHom γ i j‖ ≤ C * (1 + Frob γ) ^ N) ∧
      ∃ A B : R,
        (1 - Rneg) * (ofSL γ - ∑ j : Fin 6, (sigmaHom γ) 0 j • MpElem j)
          = (R_T - 1) ^ 2 * A + R_S * (R_T - 1) ^ 2 * B ∧
        coeffNorm A ≤ C * (1 + Frob γ) ^ N ∧
        coeffNorm B ≤ C * (1 + Frob γ) ^ N ∧
        supportFrobLe A (C * (1 + Frob γ) ^ N) ∧
        supportFrobLe B (C * (1 + Frob γ) ^ N) := by
  obtain ⟨Cσ, Nσ, hCσ, hNσ, hσ⟩ := sigmaHom_entry_bound
  obtain ⟨Nsig, Ncar, hNsig, hSig, hCar⟩ := block_letters_data
  obtain ⟨Cb, Nb, hCb0, hNb0, hbf⟩ := block_factorization
  obtain ⟨Cb', Nb', hCb'⟩ := rpow_to_pow (le_of_lt hCb0) hNb0
  obtain ⟨Cσ', Nσ', hσ'⟩ := rpow_to_pow hCσ hNσ
  have hCσ'0 : (0 : ℝ) ≤ (Cσ' : ℝ) := Nat.cast_nonneg _
  set Nb'' : ℕ := max Nb' 1 with hNb''
  have hNb''1 : 1 ≤ Nb'' := by rw [hNb'']; exact le_max_right _ _
  have hNb'le : Nb' ≤ Nb'' := by rw [hNb'']; exact le_max_left _ _
  have hCb'0 : (0 : ℝ) ≤ (Cb' : ℝ) := Nat.cast_nonneg _
  set Cfin : ℝ := 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ')
      + ((Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar)
        + (2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1) + (8 + (Cσ' : ℝ)))) with hCfin
  set Nfin : ℕ := max (max (Nb'' * Nσ') (Nb'' + 2 * Nb'' * Ncar))
      (max (Nb'' * (Ncar + 1)) (max 1 Nσ')) with hNfin
  have hCfin0 : (0 : ℝ) ≤ Cfin := by
    rw [hCfin]
    have h1 : (0 : ℝ) ≤ 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ') := by positivity
    have h2 : (0 : ℝ) ≤ (Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar) := by positivity
    have h3 : (0 : ℝ) ≤ 2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1) := by positivity
    have h4 : (0 : ℝ) ≤ (Cσ' : ℝ) := hCσ'0
    linarith
  refine ⟨Cfin, (Nfin : ℝ), hCfin0, Nat.cast_nonneg _, fun γ => ?_⟩
  have hx1 : (1 : ℝ) ≤ 1 + Frob γ := by linarith [Frob_nonneg γ]
  have hx0 : (0 : ℝ) ≤ 1 + Frob γ := le_trans zero_le_one hx1
  obtain ⟨n, w, δ, hδ, hw, hprod, hn, hprodFrob⟩ := hbf γ
  -- the list of letters of the block factorization
  have hblk : ∀ i : Fin n, ∃ p : Bool × ℤ, wblk p = w i := by
    intro i
    obtain ⟨k, hk⟩ := hw i
    rcases hk with hk | hk
    · exact ⟨(false, k), by rw [show wblk (false, k) = ModularGroup.T ^ k from by simp [wblk], hk]⟩
    · exact ⟨(true, k), by rw [show wblk (true, k) = ModularGroup.S * ModularGroup.T ^ k from by
          simp [wblk], hk]⟩
  set L : List (Bool × ℤ) := List.ofFn (fun i : Fin n => Classical.choose (hblk i)) with hLdef
  have hLget : ∀ i : Fin n, wblk (Classical.choose (hblk i)) = w i :=
    fun i => Classical.choose_spec (hblk i)
  have hLmap : L.map wblk = List.ofFn w := by
    rw [hLdef, List.map_ofFn]
    congr 1
    funext i
    exact hLget i
  have hLlen : L.length = n := by simp [hLdef]
  -- the amplitude of the word
  have hprodL : letterProd L ≤ (Cb' : ℝ) * (1 + Frob γ) ^ Nb' := by
    rw [letterProd_eq_prod w L hLmap]
    exact le_trans hprodFrob (hCb' _ hx1)
  have hprodL' : letterProd L ≤ (Cb' : ℝ) * (1 + Frob γ) ^ Nb'' := by
    refine le_trans hprodL ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 hNb'le) hCb'0
  have h1le : (1 : ℝ) ≤ letterProd L := one_le_letterProd L
  have hamp : bAmp L ≤ 2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb'' := by
    rw [bAmp_eq_letterProd]
    calc letterProd L * 2 ≤ ((Cb' : ℝ) * (1 + Frob γ) ^ Nb'') * 2 :=
          mul_le_mul_of_nonneg_right hprodL' (by norm_num)
      _ = 2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb'' := by ring
  have hamp1 : (1 : ℝ) ≤ bAmp L := one_le_bAmp L
  -- the number of blocks
  have hn1 : (n : ℝ) + 1 ≤ (Cb + 1) * (1 + Frob γ) ^ Nb'' := by
    have hlogle : Real.log (1 + Frob γ) ≤ Frob γ := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + Frob γ)
      linarith
    have hn' : (n : ℝ) ≤ Cb * (1 + Frob γ) :=
      le_trans hn (mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hCb0))
    have hpow : (1 + Frob γ) ≤ (1 + Frob γ) ^ Nb'' := by
      calc (1 + Frob γ) = (1 + Frob γ) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ (1 + Frob γ) ^ Nb'' := pow_le_pow_right₀ hx1 hNb''1
    have hCbx : Cb * (1 + Frob γ) ≤ Cb * (1 + Frob γ) ^ Nb'' :=
      mul_le_mul_of_nonneg_left hpow (le_of_lt hCb0)
    nlinarith [hn', hCbx, hpow, hx1, le_of_lt hCb0]
  -- the accumulated carry
  have hblkspec : ∀ (l : Bool × ℤ) (i : Fin 6),
      carryCombOdd (wblkA l i) (wblkB l i) = twist (wblk l) i := by
    intro l i
    rcases l with ⟨b, k⟩
    cases b
    · have h1 : wblkA (false, k) i = TblockA k i := by simp [wblkA]
      have h2 : wblkB (false, k) i = TblockB k i := by simp [wblkB]
      have h3 : wblk (false, k) = ModularGroup.T ^ k := by simp [wblk]
      rw [h1, h2, h3, Tblock_spec]
    · have h1 : wblkA (true, k) i = STblockA k i := by simp [wblkA]
      have h2 : wblkB (true, k) i = STblockB k i := by simp [wblkB]
      have h3 : wblk (true, k) = ModularGroup.S * ModularGroup.T ^ k := by simp [wblk]
      rw [h1, h2, h3, STblock_spec]
  have hacc_spec : carryCombOdd (bAcc L 0).1 (bAcc L 0).2 = twist ((List.ofFn w).prod) 0 := by
    rw [bAcc_spec hblkspec L 0, hLmap]
  have hacc_bnd := bAcc_bound Nsig Ncar hNsig hSig hCar L 0
  have hacc1 : coeffNorm (bAcc L 0).1 ≤ (n + 1) * (bAmp L) ^ (2 * Ncar) := by
    rw [← hLlen]; exact hacc_bnd.1
  have hacc2 : coeffNorm (bAcc L 0).2 ≤ (n + 1) * (bAmp L) ^ (2 * Ncar) := by
    rw [← hLlen]; exact hacc_bnd.2.1
  have haccs1 : supportFrobLe (bAcc L 0).1 ((bAmp L) ^ (Ncar + 1)) := hacc_bnd.2.2.1
  have haccs2 : supportFrobLe (bAcc L 0).2 ((bAmp L) ^ (Ncar + 1)) := hacc_bnd.2.2.2
  -- the base element
  obtain ⟨dA, dB, hbase_spec, hbase_bnd⟩ := base_carry_spec δ hδ
  -- the entry bound and the two components
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Real.rpow_natCast]
    have hK : (Cσ' : ℝ) ≤ Cfin := by
      rw [hCfin]
      have h2 : (0 : ℝ) ≤ (Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar) := by positivity
      have h3 : (0 : ℝ) ≤ 2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1) := by positivity
      have h5 : (0 : ℝ) ≤ 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ') := by positivity
      linarith
    have hN : Nσ' ≤ Nfin := by
      rw [hNfin]
      exact le_trans (le_trans (le_max_right 1 Nσ') (le_max_right _ _)) (le_max_right _ _)
    exact le_trans (le_trans (hσ γ i j) (hσ' _ hx1)) (one_term_le hx1 hK hCσ'0 hN)
  · refine ⟨(∑ j : Fin 6, (sigmaHom ((List.ofFn w).prod)) 0 j • dA j) + (bAcc L 0).1 * ofSL δ,
      (∑ j : Fin 6, (sigmaHom ((List.ofFn w).prod)) 0 j • dB j) + (bAcc L 0).2 * ofSL δ,
      ?_, ?_, ?_, ?_, ?_⟩
    · -- the main identity
      have hrow : (1 - Rneg) * (ofSL γ - ∑ j : Fin 6, (sigmaHom γ) 0 j • MpElem j)
          = twist γ 0 := by
        rw [show twist γ 0 = (1 - Rneg) * rowDiffOdd γ 0 from rfl, rowDiffOdd, MpElem_zero, one_mul]
      rw [hrow, ← hprod, twist_cocycle]
      have h1 : twist ((List.ofFn w).prod) 0 = carryCombOdd (bAcc L 0).1 (bAcc L 0).2 := hacc_spec.symm
      rw [h1]
      rw [show (∑ j : Fin 6, (sigmaHom ((List.ofFn w).prod)) 0 j • twist δ j)
          = ∑ j : Fin 6, (sigmaHom ((List.ofFn w).prod)) 0 j • carryCombOdd (dA j) (dB j) from by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hbase_spec j]]
      rw [← carryCombOdd_sum_univ, ← carryCombOdd_mul_of, ← carryCombOdd_add]
      rfl
    · -- the coefficient bound for `A`
      rw [Real.rpow_natCast]
      have hsigA : coeffNorm (∑ j : Fin 6, (sigmaHom ((List.ofFn w).prod)) 0 j • dA j)
          ≤ 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ') * (1 + Frob γ) ^ (Nb'' * Nσ') := by
        have hFp : Frob ((List.ofFn w).prod) ≤ bAmp L := by
          rw [← hLmap]; exact Frob_blk_prod_le L
        have hbase1 : 1 + Frob ((List.ofFn w).prod) ≤ 1 + bAmp L := by linarith
        have hstep1 : 1 + bAmp L ≤ (1 + 2 * (Cb' : ℝ)) * (1 + Frob γ) ^ Nb'' := by
          have h2 : (1 : ℝ) ≤ (1 + Frob γ) ^ Nb'' := one_le_pow₀ hx1
          nlinarith [hamp, h2, hCb'0, le_trans zero_le_one hx1]
        have hstep2 : (1 + Frob ((List.ofFn w).prod)) ^ Nσ'
            ≤ (1 + 2 * (Cb' : ℝ)) ^ Nσ' * (1 + Frob γ) ^ (Nb'' * Nσ') := by
          calc (1 + Frob ((List.ofFn w).prod)) ^ Nσ' ≤ (1 + bAmp L) ^ Nσ' :=
                pow_le_pow_left₀ (by linarith [Frob_nonneg ((List.ofFn w).prod)]) hbase1 Nσ'
            _ ≤ ((1 + 2 * (Cb' : ℝ)) * (1 + Frob γ) ^ Nb'') ^ Nσ' :=
                pow_le_pow_left₀ (by linarith [hamp1]) hstep1 Nσ'
            _ = (1 + 2 * (Cb' : ℝ)) ^ Nσ' * (1 + Frob γ) ^ (Nb'' * Nσ') := by
                rw [mul_pow, ← pow_mul]
        refine le_trans (coeffNorm_smul_sum_le _ _ _) ?_
        calc ∑ j : Fin 6, ‖(sigmaHom ((List.ofFn w).prod)) 0 j‖ * coeffNorm (dA j)
            ≤ ∑ _j : Fin 6, (Cσ' : ℝ) * (1 + Frob ((List.ofFn w).prod)) ^ Nσ' * 4 := by
              refine Finset.sum_le_sum fun j _ => ?_
              exact mul_le_mul (le_trans (hσ ((List.ofFn w).prod) 0 j)
                (hσ' _ (by linarith [Frob_nonneg ((List.ofFn w).prod)])))
                ((hbase_bnd j).1) (coeffNorm_nonneg _)
                (mul_nonneg hCσ'0 (pow_nonneg (by linarith [Frob_nonneg ((List.ofFn w).prod)]) _))
          _ = 24 * ((Cσ' : ℝ) * (1 + Frob ((List.ofFn w).prod)) ^ Nσ') := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              norm_num
              ring
          _ ≤ 24 * ((Cσ' : ℝ) * ((1 + 2 * (Cb' : ℝ)) ^ Nσ' * (1 + Frob γ) ^ (Nb'' * Nσ'))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact mul_le_mul_of_nonneg_left hstep2 hCσ'0
          _ = 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ') * (1 + Frob γ) ^ (Nb'' * Nσ') := by ring
      have hcarA : coeffNorm ((bAcc L 0).1 * ofSL δ)
          ≤ ((Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar)) * (1 + Frob γ) ^ (Nb'' + 2 * Nb'' * Ncar) := by
        refine le_trans (coeffNorm_mul_of_le _ _) (le_trans hacc1 ?_)
        have h3 : (bAmp L) ^ (2 * Ncar) ≤ (2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb'') ^ (2 * Ncar) :=
          pow_le_pow_left₀ (le_trans zero_le_one hamp1) hamp _
        calc (n + 1) * (bAmp L) ^ (2 * Ncar)
            ≤ ((Cb + 1) * (1 + Frob γ) ^ Nb'') * (2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb'') ^ (2 * Ncar) :=
              mul_le_mul hn1 h3 (by positivity) (by linarith [hx0, le_of_lt hCb0, hCb'0])
          _ = ((Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar)) * (1 + Frob γ) ^ (Nb'' + 2 * Nb'' * Ncar) := by
              have h1 : (2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb'') ^ (2 * Ncar)
                  = (2 * (Cb' : ℝ)) ^ (2 * Ncar) * (1 + Frob γ) ^ (2 * Nb'' * Ncar) := by
                rw [mul_pow, ← pow_mul]
                congr 1
                ring
              have h2 : (1 + Frob γ) ^ Nb'' * (1 + Frob γ) ^ (2 * Nb'' * Ncar)
                  = (1 + Frob γ) ^ (Nb'' + 2 * Nb'' * Ncar) := (pow_add _ _ _).symm
              rw [h1, ← h2]
              ring
      have hCsum : 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ')
          + ((Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar)) ≤ Cfin := by
        rw [hCfin]
        have h2 : (0 : ℝ) ≤ (Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar) := by positivity
        have h3 : (0 : ℝ) ≤ 2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1) := by positivity
        have h4 : (0 : ℝ) ≤ (8 : ℝ) := by norm_num
        have h5 : (0 : ℝ) ≤ (Cσ' : ℝ) := hCσ'0
        linarith
      have hN1 : Nb'' * Nσ' ≤ Nfin := by
        rw [hNfin]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      have hN2 : Nb'' + 2 * Nb'' * Ncar ≤ Nfin := by
        rw [hNfin]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      exact le_trans (coeffNorm_add_le _ _) (le_trans (add_le_add hsigA hcarA)
        (two_term_le hx1 hCsum (by positivity) (by positivity) hN1 hN2))
    · -- the coefficient bound for `B`
      rw [Real.rpow_natCast]
      have hsigA : coeffNorm (∑ j : Fin 6, (sigmaHom ((List.ofFn w).prod)) 0 j • dB j)
          ≤ 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ') * (1 + Frob γ) ^ (Nb'' * Nσ') := by
        have hFp : Frob ((List.ofFn w).prod) ≤ bAmp L := by
          rw [← hLmap]; exact Frob_blk_prod_le L
        have hbase1 : 1 + Frob ((List.ofFn w).prod) ≤ 1 + bAmp L := by linarith
        have hstep1 : 1 + bAmp L ≤ (1 + 2 * (Cb' : ℝ)) * (1 + Frob γ) ^ Nb'' := by
          have h2 : (1 : ℝ) ≤ (1 + Frob γ) ^ Nb'' := one_le_pow₀ hx1
          nlinarith [hamp, h2, hCb'0, le_trans zero_le_one hx1]
        have hstep2 : (1 + Frob ((List.ofFn w).prod)) ^ Nσ'
            ≤ (1 + 2 * (Cb' : ℝ)) ^ Nσ' * (1 + Frob γ) ^ (Nb'' * Nσ') := by
          calc (1 + Frob ((List.ofFn w).prod)) ^ Nσ' ≤ (1 + bAmp L) ^ Nσ' :=
                pow_le_pow_left₀ (by linarith [Frob_nonneg ((List.ofFn w).prod)]) hbase1 Nσ'
            _ ≤ ((1 + 2 * (Cb' : ℝ)) * (1 + Frob γ) ^ Nb'') ^ Nσ' :=
                pow_le_pow_left₀ (by linarith [hamp1]) hstep1 Nσ'
            _ = (1 + 2 * (Cb' : ℝ)) ^ Nσ' * (1 + Frob γ) ^ (Nb'' * Nσ') := by
                rw [mul_pow, ← pow_mul]
        refine le_trans (coeffNorm_smul_sum_le _ _ _) ?_
        calc ∑ j : Fin 6, ‖(sigmaHom ((List.ofFn w).prod)) 0 j‖ * coeffNorm (dB j)
            ≤ ∑ _j : Fin 6, (Cσ' : ℝ) * (1 + Frob ((List.ofFn w).prod)) ^ Nσ' * 4 := by
              refine Finset.sum_le_sum fun j _ => ?_
              exact mul_le_mul (le_trans (hσ ((List.ofFn w).prod) 0 j)
                (hσ' _ (by linarith [Frob_nonneg ((List.ofFn w).prod)])))
                ((hbase_bnd j).2.1) (coeffNorm_nonneg _)
                (mul_nonneg hCσ'0 (pow_nonneg (by linarith [Frob_nonneg ((List.ofFn w).prod)]) _))
          _ = 24 * ((Cσ' : ℝ) * (1 + Frob ((List.ofFn w).prod)) ^ Nσ') := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              norm_num
              ring
          _ ≤ 24 * ((Cσ' : ℝ) * ((1 + 2 * (Cb' : ℝ)) ^ Nσ' * (1 + Frob γ) ^ (Nb'' * Nσ'))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact mul_le_mul_of_nonneg_left hstep2 hCσ'0
          _ = 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ') * (1 + Frob γ) ^ (Nb'' * Nσ') := by ring
      have hcarA : coeffNorm ((bAcc L 0).2 * ofSL δ)
          ≤ ((Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar)) * (1 + Frob γ) ^ (Nb'' + 2 * Nb'' * Ncar) := by
        refine le_trans (coeffNorm_mul_of_le _ _) (le_trans hacc2 ?_)
        have h3 : (bAmp L) ^ (2 * Ncar) ≤ (2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb'') ^ (2 * Ncar) :=
          pow_le_pow_left₀ (le_trans zero_le_one hamp1) hamp _
        calc (n + 1) * (bAmp L) ^ (2 * Ncar)
            ≤ ((Cb + 1) * (1 + Frob γ) ^ Nb'') * (2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb'') ^ (2 * Ncar) :=
              mul_le_mul hn1 h3 (by positivity) (by linarith [hx0, le_of_lt hCb0, hCb'0])
          _ = ((Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar)) * (1 + Frob γ) ^ (Nb'' + 2 * Nb'' * Ncar) := by
              have h1 : (2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb'') ^ (2 * Ncar)
                  = (2 * (Cb' : ℝ)) ^ (2 * Ncar) * (1 + Frob γ) ^ (2 * Nb'' * Ncar) := by
                rw [mul_pow, ← pow_mul]
                congr 1
                ring
              have h2 : (1 + Frob γ) ^ Nb'' * (1 + Frob γ) ^ (2 * Nb'' * Ncar)
                  = (1 + Frob γ) ^ (Nb'' + 2 * Nb'' * Ncar) := (pow_add _ _ _).symm
              rw [h1, ← h2]
              ring
      have hCsum : 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ')
          + ((Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar)) ≤ Cfin := by
        rw [hCfin]
        have h2 : (0 : ℝ) ≤ (Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar) := by positivity
        have h3 : (0 : ℝ) ≤ 2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1) := by positivity
        have h4 : (0 : ℝ) ≤ (8 : ℝ) := by norm_num
        have h5 : (0 : ℝ) ≤ (Cσ' : ℝ) := hCσ'0
        linarith
      have hN1 : Nb'' * Nσ' ≤ Nfin := by
        rw [hNfin]
        exact le_trans (le_max_left _ _) (le_max_left _ _)
      have hN2 : Nb'' + 2 * Nb'' * Ncar ≤ Nfin := by
        rw [hNfin]
        exact le_trans (le_max_right _ _) (le_max_left _ _)
      exact le_trans (coeffNorm_add_le _ _) (le_trans (add_le_add hsigA hcarA)
        (two_term_le hx1 hCsum (by positivity) (by positivity) hN1 hN2))
    · -- the support bound for `A`
      rw [Real.rpow_natCast]
      have hsigA : supportFrobLe (∑ j : Fin 6, (sigmaHom ((List.ofFn w).prod)) 0 j • dA j) (8 : ℝ) :=
        supportFrobLe_smul_sum Finset.univ _ _ (fun j _ => (hbase_bnd j).2.2.1)
      have hcarA : supportFrobLe ((bAcc L 0).1 * ofSL δ)
          ((2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1)) * (1 + Frob γ) ^ (Nb'' * (Ncar + 1))) := by
        refine supportFrobLe_mono (supportFrobLe_mul_of haccs1 δ) ?_
        have hFd : Frob δ ≤ 2 := by
          rcases hδ with h | h | h | h
          · rw [h]; exact le_trans Frob_one_le (by norm_num)
          · rw [h, Frob_neg_eq]; exact le_trans Frob_one_le (by norm_num)
          · rw [h]; rw [Frob_S]; norm_num
          · rw [h, Frob_neg_eq]; rw [Frob_S]; norm_num
        calc (bAmp L) ^ (Ncar + 1) * Frob δ ≤ (bAmp L) ^ (Ncar + 1) * 2 :=
              mul_le_mul_of_nonneg_left hFd (by positivity)
          _ ≤ (2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb'') ^ (Ncar + 1) * 2 :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_trans zero_le_one hamp1) hamp _)
                (by norm_num)
          _ = (2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1)) * (1 + Frob γ) ^ (Nb'' * (Ncar + 1)) := by
              rw [mul_pow, ← pow_mul]
              ring
      have hC8 : (8 : ℝ) ≤ Cfin := by
        rw [hCfin]
        have h2 : (0 : ℝ) ≤ (Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar) := by positivity
        have h3 : (0 : ℝ) ≤ 2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1) := by positivity
        have h5 : (0 : ℝ) ≤ 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ') := by positivity
        have h4 : (0 : ℝ) ≤ (Cσ' : ℝ) := hCσ'0
        linarith
      have hC2 : 2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1) ≤ Cfin := by
        rw [hCfin]
        have h2 : (0 : ℝ) ≤ (Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar) := by positivity
        have h5 : (0 : ℝ) ≤ 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ') := by positivity
        have h4 : (0 : ℝ) ≤ (Cσ' : ℝ) := hCσ'0
        have h8 : (0 : ℝ) ≤ (8 : ℝ) := by norm_num
        linarith
      have hN2 : Nb'' * (Ncar + 1) ≤ Nfin := by
        rw [hNfin]
        exact le_trans (le_max_left _ _) (le_max_right _ _)
      have h8 : (8 : ℝ) ≤ Cfin * (1 + Frob γ) ^ Nfin := by
        have h := one_term_le hx1 hC8 (by norm_num) (Nat.zero_le Nfin)
        simpa using h
      have hK2 : (2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1)) * (1 + Frob γ) ^ (Nb'' * (Ncar + 1))
          ≤ Cfin * (1 + Frob γ) ^ Nfin :=
        one_term_le hx1 hC2 (by positivity) hN2
      exact supportFrobLe_mono (supportFrobLe_add hsigA hcarA) (max_le h8 hK2)
    · -- the support bound for `B`
      rw [Real.rpow_natCast]
      have hsigA : supportFrobLe (∑ j : Fin 6, (sigmaHom ((List.ofFn w).prod)) 0 j • dB j) (8 : ℝ) :=
        supportFrobLe_smul_sum Finset.univ _ _ (fun j _ => (hbase_bnd j).2.2.2)
      have hcarA : supportFrobLe ((bAcc L 0).2 * ofSL δ)
          ((2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1)) * (1 + Frob γ) ^ (Nb'' * (Ncar + 1))) := by
        refine supportFrobLe_mono (supportFrobLe_mul_of haccs2 δ) ?_
        have hFd : Frob δ ≤ 2 := by
          rcases hδ with h | h | h | h
          · rw [h]; exact le_trans Frob_one_le (by norm_num)
          · rw [h, Frob_neg_eq]; exact le_trans Frob_one_le (by norm_num)
          · rw [h]; rw [Frob_S]; norm_num
          · rw [h, Frob_neg_eq]; rw [Frob_S]; norm_num
        calc (bAmp L) ^ (Ncar + 1) * Frob δ ≤ (bAmp L) ^ (Ncar + 1) * 2 :=
              mul_le_mul_of_nonneg_left hFd (by positivity)
          _ ≤ (2 * (Cb' : ℝ) * (1 + Frob γ) ^ Nb'') ^ (Ncar + 1) * 2 :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_trans zero_le_one hamp1) hamp _)
                (by norm_num)
          _ = (2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1)) * (1 + Frob γ) ^ (Nb'' * (Ncar + 1)) := by
              rw [mul_pow, ← pow_mul]
              ring
      have hC8 : (8 : ℝ) ≤ Cfin := by
        rw [hCfin]
        have h2 : (0 : ℝ) ≤ (Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar) := by positivity
        have h3 : (0 : ℝ) ≤ 2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1) := by positivity
        have h5 : (0 : ℝ) ≤ 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ') := by positivity
        have h4 : (0 : ℝ) ≤ (Cσ' : ℝ) := hCσ'0
        linarith
      have hC2 : 2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1) ≤ Cfin := by
        rw [hCfin]
        have h2 : (0 : ℝ) ≤ (Cb + 1) * (2 * (Cb' : ℝ)) ^ (2 * Ncar) := by positivity
        have h5 : (0 : ℝ) ≤ 24 * ((Cσ' : ℝ) * (1 + 2 * (Cb' : ℝ)) ^ Nσ') := by positivity
        have h4 : (0 : ℝ) ≤ (Cσ' : ℝ) := hCσ'0
        have h8 : (0 : ℝ) ≤ (8 : ℝ) := by norm_num
        linarith
      have hN2 : Nb'' * (Ncar + 1) ≤ Nfin := by
        rw [hNfin]
        exact le_trans (le_max_left _ _) (le_max_right _ _)
      have h8 : (8 : ℝ) ≤ Cfin * (1 + Frob γ) ^ Nfin := by
        have h := one_term_le hx1 hC8 (by norm_num) (Nat.zero_le Nfin)
        simpa using h
      have hK2 : (2 * (2 * (Cb' : ℝ)) ^ (Ncar + 1)) * (1 + Frob γ) ^ (Nb'' * (Ncar + 1))
          ≤ Cfin * (1 + Frob γ) ^ Nfin :=
        one_term_le hx1 hC2 (by positivity) hN2
      exact supportFrobLe_mono (supportFrobLe_add hsigA hcarA) (max_le h8 hK2)

end Work.Asymptotics
