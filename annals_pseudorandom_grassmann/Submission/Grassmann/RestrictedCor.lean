import Submission.Grassmann.XNormSum
import Submission.Grassmann.RestrictionFourier
import Submission.Grassmann.HybridLift
import Submission.Commons.LinearAlgebra.Matrix.card_rank_poset_upset_fiber_le_pow

/-!
# The restricted `cor:getting rid of D_X 4-norms`

Session 26/27 of this project found that the paper's identity
`‖D_X f‖₂² = Σ_{Y ≥ X} |f̂(Y)|²` is **false** for the *restricted* form
`D_X f = restr (Qp (range X)) (Ip (ker X)) (L_X f)`: several characters `u_Z`, `Z ≥ X`, can have
the *same* compression `Z ↦ Qp (range X) * Z * Ip (ker X)`, and their coefficients then add.

This file proves the replacement used in the endgame.  By `l2sq_restr_eq_sum_fiber` the squared
norm of the restricted function is the sum, over the fibres of the compression, of the squared
modulus of the sum of the coefficients in the fibre:

`l2sq (D_X h) = Σ_φ ‖Σ_{Z ∈ φ ∩ S_X} ĥ(Z)‖²`,  `S_X = {Z : plLE X Z}`.

Cauchy–Schwarz in each fibre gives `l2sq (D_X h) ≤ N_X(d) · l2sq (L_X h)` whenever `DegLe d h`,
where `N_X(d)` bounds the fibres of the compression intersected with `{plLE X ·, rank ≤ d}`; this
`N_X(d)` is the hypothesis `fib` (a combinatorial statement about the rank poset of
`𝔽₂`-matrices, `Commons.LinearAlgebra.Matrix.card_rank_poset_upset_fiber_le_pow`).

Combining with the (proven) multiplier version `XNormSum.sum_inv_pow_sq_l2sq_plLE_le` gives the
restricted 4-norm corollary `restricted_cor_4`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## An abstract Cauchy–Schwarz bound for the squares of fibre sums -/

/-- **Cauchy–Schwarz for the fibres of a map.**  If every fibre of `π : α → β` intersected with
the support of `f` has at most `N` elements, then `Σ_Y ‖Σ_{π x = Y} f x‖² ≤ N Σ_x ‖f x‖²`. -/
lemma sum_fiber_normSq_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (π : α → β) (f : α → ℂ) (N : ℕ)
    (hN : ∀ Y : β, (Finset.univ.filter (fun x => π x = Y ∧ f x ≠ 0)).card ≤ N) :
    ∑ Y : β, ‖∑ x ∈ Finset.univ.filter (fun x => π x = Y), f x‖ ^ 2 ≤
      (N : ℝ) * ∑ x, ‖f x‖ ^ 2 := by
  classical
  have hGsub : ∀ Y : β, Finset.univ.filter (fun x => π x = Y ∧ f x ≠ 0) ⊆
      Finset.univ.filter (fun x => π x = Y) := by
    intro Y x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1
  have hsum_eq : ∀ Y : β, (∑ x ∈ Finset.univ.filter (fun x => π x = Y), f x) =
      ∑ x ∈ Finset.univ.filter (fun x => π x = Y ∧ f x ≠ 0), f x := by
    intro Y
    symm
    refine Finset.sum_subset (hGsub Y) ?_
    intro x hxs hx
    by_contra hf
    refine hx ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hxs), hf⟩
  have hCS : ∀ Y : β,
      ‖∑ x ∈ Finset.univ.filter (fun x => π x = Y ∧ f x ≠ 0), f x‖ ^ 2 ≤
        (N : ℝ) * ∑ x ∈ Finset.univ.filter (fun x => π x = Y ∧ f x ≠ 0), ‖f x‖ ^ 2 := by
    intro Y
    set s := Finset.univ.filter (fun x => π x = Y ∧ f x ≠ 0) with hs
    have h1 : ‖∑ x ∈ s, f x‖ ≤ ∑ x ∈ s, ‖f x‖ := norm_sum_le _ _
    have h2 : (∑ x ∈ s, ‖f x‖) ^ 2 ≤ ((s.card : ℕ) : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ((s.card : ℕ) : ℝ) ≤ (N : ℝ) := by
      rw [hs]; exact_mod_cast hN Y
    have h4 : 0 ≤ ∑ x ∈ s, ‖f x‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    calc ‖∑ x ∈ s, f x‖ ^ 2 ≤ (∑ x ∈ s, ‖f x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ ((s.card : ℕ) : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := h2
      _ ≤ (N : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := mul_le_mul_of_nonneg_right h3 h4
  have hinner : ∀ Y : β, (∑ x ∈ Finset.univ.filter (fun x => π x = Y ∧ f x ≠ 0), ‖f x‖ ^ 2) ≤
      ∑ x ∈ Finset.univ.filter (fun x => π x = Y), ‖f x‖ ^ 2 :=
    fun Y => Finset.sum_le_sum_of_subset_of_nonneg (hGsub Y) (fun _ _ _ => by positivity)
  have hcover : ∑ Y : β, ∑ x ∈ Finset.univ.filter (fun x => π x = Y), ‖f x‖ ^ 2 =
      ∑ x, ‖f x‖ ^ 2 := by
    have h1 : ∀ Y : β, (∑ x ∈ Finset.univ.filter (fun x => π x = Y), ‖f x‖ ^ 2)
        = ∑ x : α, (if π x = Y then ‖f x‖ ^ 2 else 0) := by
      intro Y
      rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl (fun Y _ => h1 Y), Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single (π x)]
    · simp
    · intro Y _ hY
      rw [if_neg (fun h => hY h.symm)]
    · intro h
      exact absurd (Finset.mem_univ (π x)) h
  calc ∑ Y : β, ‖∑ x ∈ Finset.univ.filter (fun x => π x = Y), f x‖ ^ 2
      = ∑ Y : β, ‖∑ x ∈ Finset.univ.filter (fun x => π x = Y ∧ f x ≠ 0), f x‖ ^ 2 := by
        refine Finset.sum_congr rfl fun Y _ => ?_
        rw [hsum_eq Y]
    _ ≤ ∑ Y : β, (N : ℝ) *
          ∑ x ∈ Finset.univ.filter (fun x => π x = Y ∧ f x ≠ 0), ‖f x‖ ^ 2 :=
        Finset.sum_le_sum fun Y _ => hCS Y
    _ = (N : ℝ) * ∑ Y : β,
          ∑ x ∈ Finset.univ.filter (fun x => π x = Y ∧ f x ≠ 0), ‖f x‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (N : ℝ) * ∑ Y : β, ∑ x ∈ Finset.univ.filter (fun x => π x = Y), ‖f x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun Y _ => hinner Y) (by positivity)
    _ = (N : ℝ) * ∑ x, ‖f x‖ ^ 2 := by rw [hcover]

/-! ## Parseval for a restriction, in terms of the fibres of the compression -/

/-- **The squared norm of a restriction is the sum over the fibres of the compression**:
`l2sq (restr Q ι g) = Σ_Y ‖Σ_{X : Q * X * ι = Y} ĝ(X)‖²`. -/
lemma l2sq_restr_eq_sum_fiber {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (restr Q ι g) =
      ∑ Y : Matrix (Fin n') (Fin m') 𝔽₂,
        ‖∑ X ∈ Finset.univ.filter (fun X : Matrix (Fin n) (Fin m) 𝔽₂ => Q * X * ι = Y),
          fcoeff g X‖ ^ 2 := by
  rw [← sum_normSq_fcoeff (restr Q ι g)]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [fcoeff_restr]

/-! ## The restricted `X`-derivative is dominated by its multiplier form -/

/-- **The main comparison.**  Let `DegLe d h` and let `N` bound the fibres of the compression
`Z ↦ Qp (range X) * Z * Ip (ker X)` restricted to `{Z : plLE X Z, Z.rank ≤ d}`.  Then
`l2sq (D_X h) ≤ N · l2sq (L_X h)`, where `D_X h` is the *restricted* derivative
`restr (Qp (range X)) (Ip (ker X)) (L_X h)`. -/
theorem l2sq_restr_lapMulN_le {m n d : ℕ} {h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hh : DegLe d h) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (fib : ∀ Z₀ : Matrix (Fin n) (Fin m) 𝔽₂, plLE X Z₀ → Z₀.rank ≤ d →
      Nat.card {Z : Matrix (Fin n) (Fin m) 𝔽₂ //
        plLE X Z ∧ Z.rank ≤ d ∧
          Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin)
            = Qp (LinearMap.range X.mulVecLin) * Z₀ * Ip (LinearMap.ker X.mulVecLin)}
        ≤ 2 ^ (2 * X.rank * d)) :
    l2sq (restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
        (lapMulN (plLE X) h)) ≤ (2 : ℝ) ^ (2 * X.rank * d) * l2sq (lapMulN (plLE X) h) := by
  classical
  have hkey : ∀ X' : Matrix (Fin n) (Fin m) 𝔽₂,
      fcoeff (lapMulN (plLE X) h) X' ≠ 0 → plLE X X' ∧ X'.rank ≤ d := by
    intro X' hX'
    rw [fcoeff_lapMulN] at hX'
    by_cases hp : plLE X X'
    · refine ⟨hp, ?_⟩
      by_contra hr
      exact hX' (by rw [if_pos hp, fcoeff_eq, hh X' (by omega)]; ring)
    · exact absurd (by rw [if_neg hp, zero_mul]) hX'
  have hN : ∀ Y : Matrix (Fin (n - Module.finrank 𝔽₂ (LinearMap.range X.mulVecLin)))
        (Fin (Module.finrank 𝔽₂ (LinearMap.ker X.mulVecLin))) 𝔽₂,
      (Finset.univ.filter (fun X' : Matrix (Fin n) (Fin m) 𝔽₂ =>
        Qp (LinearMap.range X.mulVecLin) * X' * Ip (LinearMap.ker X.mulVecLin) = Y ∧
          fcoeff (lapMulN (plLE X) h) X' ≠ 0)).card ≤ 2 ^ (2 * X.rank * d) := by
    intro Y
    set F := Finset.univ.filter (fun X' : Matrix (Fin n) (Fin m) 𝔽₂ =>
      Qp (LinearMap.range X.mulVecLin) * X' * Ip (LinearMap.ker X.mulVecLin) = Y ∧
        fcoeff (lapMulN (plLE X) h) X' ≠ 0) with hF
    set S := Finset.univ.filter (fun X' : Matrix (Fin n) (Fin m) 𝔽₂ =>
      plLE X X' ∧ X'.rank ≤ d ∧
        Qp (LinearMap.range X.mulVecLin) * X' * Ip (LinearMap.ker X.mulVecLin) = Y) with hS
    have hFS : F ⊆ S := by
      intro X' hX'
      simp only [hF, hS, Finset.mem_filter, Finset.mem_univ, true_and] at hX' ⊢
      exact ⟨(hkey X' hX'.2).1, (hkey X' hX'.2).2, hX'.1⟩
    have hcard : S.card = Nat.card {Z : Matrix (Fin n) (Fin m) 𝔽₂ //
        plLE X Z ∧ Z.rank ≤ d ∧
          Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin) = Y} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · refine le_trans (Finset.card_le_card hFS) ?_
      rw [h0]
      exact Nat.zero_le _
    · obtain ⟨Z₀, hZ₀⟩ := Finset.card_pos.mp hpos
      obtain ⟨hplLE, hrank, hY⟩ := (Finset.mem_filter.mp hZ₀).2
      calc F.card ≤ S.card := Finset.card_le_card hFS
        _ = Nat.card {Z : Matrix (Fin n) (Fin m) 𝔽₂ // plLE X Z ∧ Z.rank ≤ d ∧
              Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin) = Y} := hcard
        _ = Nat.card {Z : Matrix (Fin n) (Fin m) 𝔽₂ // plLE X Z ∧ Z.rank ≤ d ∧
              Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin)
                = Qp (LinearMap.range X.mulVecLin) * Z₀ * Ip (LinearMap.ker X.mulVecLin)} :=
            Nat.card_congr (Equiv.subtypeEquivRight (fun Z => by rw [hY]))
        _ ≤ 2 ^ (2 * X.rank * d) := fib Z₀ hplLE hrank
  rw [l2sq_restr_eq_sum_fiber]
  refine (sum_fiber_normSq_le
    (fun X' : Matrix (Fin n) (Fin m) 𝔽₂ =>
      Qp (LinearMap.range X.mulVecLin) * X' * Ip (LinearMap.ker X.mulVecLin))
    (fun X' => fcoeff (lapMulN (plLE X) h) X') (2 ^ (2 * X.rank * d)) hN).trans ?_
  rw [sum_normSq_fcoeff]
  push_cast
  exact le_refl _

/-! ## The restricted 4-norm corollary -/

/-- **`cor:getting rid of D_X 4-norms`, restricted form.**  If the fibres of the compression
`Z ↦ Qp (range X) * Z * Ip (ker X)` intersected with `{plLE X ·, rank ≤ d}` have at most
`2 ^ (2 * X.rank * d)` elements (hypothesis `fib`), then for `DegLe d h`

`Σ_X q^{-4d·rank X} (l2sq (D_X h))² ≤ q^{4d²} · 2 (l2sq h)²`.

This is the statement the endgame of §8 needs (`SwTerm`'s inner `l2sq` is such a `D_X`, see
`RoleTransfer.l2sq_restr_eq_DopRole`); the paper's own proof uses the false identity
`‖D_X h‖₂² = Σ_{Y ≥ X} |ĥ(Y)|²`. -/
theorem restricted_cor_4 {m n d : ℕ} {h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hh : DegLe d h)
    (fib : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂, X.rank ≤ d →
      ∀ Z₀ : Matrix (Fin n) (Fin m) 𝔽₂, plLE X Z₀ → Z₀.rank ≤ d →
      Nat.card {Z : Matrix (Fin n) (Fin m) 𝔽₂ //
        plLE X Z ∧ Z.rank ≤ d ∧
          Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin)
            = Qp (LinearMap.range X.mulVecLin) * Z₀ * Ip (LinearMap.ker X.mulVecLin)}
        ≤ 2 ^ (2 * X.rank * d)) :
    (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ *
          (l2sq (restr (Qp (LinearMap.range X.mulVecLin))
            (Ip (LinearMap.ker X.mulVecLin)) (lapMulN (plLE X) h))) ^ 2)
      ≤ (2 : ℝ) ^ (4 * d * d) * (2 * (l2sq h) ^ 2) := by
  classical
  have hzero : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂, d < X.rank →
      l2sq (restr (Qp (LinearMap.range X.mulVecLin)) (Ip (LinearMap.ker X.mulVecLin))
        (lapMulN (plLE X) h)) = 0 := by
    intro X hX
    have h1 : lapMulN (plLE X) h = 0 := by
      refine eq_of_fcoeff_eq fun Y => ?_
      rw [fcoeff_lapMulN, fcoeff_zero]
      by_cases hp : plLE X Y
      · rw [if_pos hp]
        have := plLE_rank_le hp
        rw [fcoeff_eq, hh Y (by omega), mul_zero, one_mul]
      · rw [if_neg hp, zero_mul]
    rw [h1, restr_zero]
    simp [l2sq]
  have hstep : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂,
      ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ *
          (l2sq (restr (Qp (LinearMap.range X.mulVecLin))
            (Ip (LinearMap.ker X.mulVecLin)) (lapMulN (plLE X) h))) ^ 2
        ≤ (2 : ℝ) ^ (4 * d * d) *
          (((2 : ℝ) ^ (4 * d * X.rank))⁻¹ *
            (l2sq (lapMulN (plLE X) h)) ^ 2) := by
    intro X
    by_cases hX : X.rank ≤ d
    · have hpt := l2sq_restr_lapMulN_le hh X (fib X hX)
      have hsq : (l2sq (restr (Qp (LinearMap.range X.mulVecLin))
            (Ip (LinearMap.ker X.mulVecLin)) (lapMulN (plLE X) h))) ^ 2
          ≤ ((2 : ℝ) ^ (2 * X.rank * d)) ^ 2 * (l2sq (lapMulN (plLE X) h)) ^ 2 := by
        have h := pow_le_pow_left₀ (l2sq_nonneg _) hpt 2
        rwa [mul_pow] at h
      have hpoweq : ((2 : ℝ) ^ (2 * X.rank * d)) ^ 2 = (2 : ℝ) ^ (4 * d * X.rank) := by
        rw [← pow_mul]; congr 1; ring
      have hw : ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ * (2 : ℝ) ^ (4 * d * X.rank) = 1 :=
        inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
      have hwd : ((2 : ℝ) ^ (4 * d * d))⁻¹ * (2 : ℝ) ^ (4 * d * d) = 1 :=
        inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))
      have h2d : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * d * d) := one_le_pow₀ (by norm_num)
      have hwpos : 0 < ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ := by positivity
      have hL2 : 0 ≤ (l2sq (lapMulN (plLE X) h)) ^ 2 := by positivity
      calc ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ *
              (l2sq (restr (Qp (LinearMap.range X.mulVecLin))
                (Ip (LinearMap.ker X.mulVecLin)) (lapMulN (plLE X) h))) ^ 2
          ≤ ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ *
              (((2 : ℝ) ^ (2 * X.rank * d)) ^ 2 * (l2sq (lapMulN (plLE X) h)) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (le_of_lt hwpos)
        _ = (l2sq (lapMulN (plLE X) h)) ^ 2 := by
            rw [hpoweq, ← mul_assoc, hw, one_mul]
        _ ≤ (2 : ℝ) ^ (4 * d * d) *
              (((2 : ℝ) ^ (4 * d * X.rank))⁻¹ * (l2sq (lapMulN (plLE X) h)) ^ 2) := by
            have hwle : (2 : ℝ) ^ (4 * d * X.rank) ≤ (2 : ℝ) ^ (4 * d * d) :=
              pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left (4 * d) hX)
            have hwpos : 0 < ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ := by positivity
            have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * d * d) *
                ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ := by
              have h2 := mul_le_mul_of_nonneg_right hwle hwpos.le
              rwa [mul_comm ((2 : ℝ) ^ (4 * d * X.rank)),
                inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))] at h2
            calc (l2sq (lapMulN (plLE X) h)) ^ 2
                = 1 * (l2sq (lapMulN (plLE X) h)) ^ 2 := (one_mul _).symm
              _ ≤ ((2 : ℝ) ^ (4 * d * d) * ((2 : ℝ) ^ (4 * d * X.rank))⁻¹) *
                    (l2sq (lapMulN (plLE X) h)) ^ 2 :=
                  mul_le_mul_of_nonneg_right h1 hL2
              _ = (2 : ℝ) ^ (4 * d * d) *
                    (((2 : ℝ) ^ (4 * d * X.rank))⁻¹ * (l2sq (lapMulN (plLE X) h)) ^ 2) := by
                  ring
    · have hX' : d < X.rank := not_le.mp hX
      rw [hzero X hX', zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero]
      positivity
  calc (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ *
          (l2sq (restr (Qp (LinearMap.range X.mulVecLin))
            (Ip (LinearMap.ker X.mulVecLin)) (lapMulN (plLE X) h))) ^ 2)
      ≤ ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, (2 : ℝ) ^ (4 * d * d) *
          (((2 : ℝ) ^ (4 * d * X.rank))⁻¹ * (l2sq (lapMulN (plLE X) h)) ^ 2) :=
        Finset.sum_le_sum fun X _ => hstep X
    _ = (2 : ℝ) ^ (4 * d * d) * ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
          ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ * (l2sq (lapMulN (plLE X) h)) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (4 * d * d) * (2 * (l2sq h) ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_inv_pow_sq_l2sq_plLE_le hh) (by positivity)


/-! ## The bridge to the commons fibre bound, and the unconditional corollary -/

/-- `Qp V₁ * D * Ip W₁ = 0` iff `D` maps `W₁` into `V₁`. -/
lemma Qp_mul_Ip_eq_zero_iff {N m : ℕ} (V₁ : Submodule 𝔽₂ (Fin N → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (D : Matrix (Fin N) (Fin m) 𝔽₂) :
    Qp V₁ * D * Ip W₁ = 0 ↔ ∀ w ∈ W₁, D.mulVec w ∈ V₁ := by
  constructor
  · intro h w hw
    obtain ⟨A, hA⟩ := (show w ∈ LinearMap.range (Ip W₁).mulVecLin from by
      rw [range_Ip]; exact hw)
    have hA' : (Ip W₁).mulVec A = w := by rwa [Matrix.mulVecLin_apply] at hA
    have h0 : (Qp V₁ * D * Ip W₁).mulVec A = 0 := by rw [h, Matrix.zero_mulVec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA'] at h0
    rw [← Matrix.mulVecLin_apply] at h0
    rw [← LinearMap.mem_ker (f := (Qp V₁).mulVecLin), ker_Qp V₁] at h0
    exact h0
  · intro h
    ext i j
    have h1 : (Qp V₁ * D * Ip W₁).mulVec (Pi.single j 1) = 0 := by
      have hmem : (Qp V₁).mulVec (D.mulVec ((Ip W₁).mulVec (Pi.single j 1))) = 0 := by
        rw [← Matrix.mulVecLin_apply]
        rw [← LinearMap.mem_ker (f := (Qp V₁).mulVecLin), ker_Qp V₁]
        refine h _ ?_
        have hr : (Ip W₁).mulVec (Pi.single j 1) ∈ LinearMap.range (Ip W₁).mulVecLin :=
          ⟨Pi.single j 1, by rw [Matrix.mulVecLin_apply]⟩
        rwa [range_Ip] at hr
      rwa [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h2 := congrFun h1 i
    rw [Matrix.mulVec_single_one] at h2
    simpa using h2

/-- **`cor:getting rid of D_X 4-norms`, restricted form, unconditional.**  For `DegLe d h`,

`Σ_X q^{-4d·rank X} (l2sq (D_X h))² ≤ q^{4d²} · 2 (l2sq h)²`,

where `D_X h = restr (Qp (range X)) (Ip (ker X)) (L_X h)` is the restricted `X`-derivative. -/
theorem restricted_cor_4' {m n d : ℕ} {h : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hh : DegLe d h) :
    (∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
        ((2 : ℝ) ^ (4 * d * X.rank))⁻¹ *
          (l2sq (restr (Qp (LinearMap.range X.mulVecLin))
            (Ip (LinearMap.ker X.mulVecLin)) (lapMulN (plLE X) h))) ^ 2)
      ≤ (2 : ℝ) ^ (4 * d * d) * (2 * (l2sq h) ^ 2) := by
  refine restricted_cor_4 hh fun X hX Z₀ hpl hrank => ?_
  have hiff : ∀ Z : Matrix (Fin n) (Fin m) 𝔽₂,
      (plLE X Z ∧ Z.rank ≤ d ∧
        Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin)
          = Qp (LinearMap.range X.mulVecLin) * Z₀ * Ip (LinearMap.ker X.mulVecLin))
        ↔ (Z.rank = X.rank + (Z - X).rank ∧ Z.rank ≤ d ∧
          ∀ w : Fin m → 𝔽₂, w ∈ LinearMap.ker X.mulVecLin →
            (Z - Z₀).mulVec w ∈ LinearMap.range X.mulVecLin) := by
    intro Z
    have hsub : Qp (LinearMap.range X.mulVecLin) * (Z - Z₀) * Ip (LinearMap.ker X.mulVecLin)
        = Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin)
          - Qp (LinearMap.range X.mulVecLin) * Z₀ * Ip (LinearMap.ker X.mulVecLin) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    have h3iff : (Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin)
        = Qp (LinearMap.range X.mulVecLin) * Z₀ * Ip (LinearMap.ker X.mulVecLin))
        ↔ (Qp (LinearMap.range X.mulVecLin) * (Z - Z₀) * Ip (LinearMap.ker X.mulVecLin) = 0) := by
      rw [hsub, sub_eq_zero]
    rw [plLE, h3iff, Qp_mul_Ip_eq_zero_iff]
  calc Nat.card {Z : Matrix (Fin n) (Fin m) 𝔽₂ //
        plLE X Z ∧ Z.rank ≤ d ∧
          Qp (LinearMap.range X.mulVecLin) * Z * Ip (LinearMap.ker X.mulVecLin)
            = Qp (LinearMap.range X.mulVecLin) * Z₀ * Ip (LinearMap.ker X.mulVecLin)}
      = Nat.card {Z : Matrix (Fin n) (Fin m) 𝔽₂ //
          Z.rank = X.rank + (Z - X).rank ∧ Z.rank ≤ d ∧
          ∀ w : Fin m → 𝔽₂, w ∈ LinearMap.ker X.mulVecLin →
            (Z - Z₀).mulVec w ∈ LinearMap.range X.mulVecLin} :=
        Nat.card_congr (Equiv.subtypeEquivRight hiff)
    _ ≤ 2 ^ (2 * X.rank * d) :=
        Commons.LinearAlgebra.Matrix.card_rank_poset_upset_fiber_le_pow n m d X Z₀ hX hpl


end

end Submission.Grassmann
