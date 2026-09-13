import Submission.Grassmann.Influence
import Submission.Grassmann.CombinatorialLaplacian
import Submission.Grassmann.DualLaplacian
import Submission.Grassmann.TauOp
import Submission.Grassmann.Homogeneous

/-!
# The convexity step of the inductive (degree-reduction) lemma

arXiv:2209.04243, §7 (`lem:inductive step`).  The paper shows that if `f` is
`(d,ε)`-restriction global then the function `f' = (𝒯_{d,U}[f])_{(U,W)→0}` is
`(d-1, O(q^{4d})ε)`-restriction global.

The proof is a convexity argument: `𝓔_U[-]` is an average of shifts `Δ_B`, and restricting
and shifting commute, so every restriction of `𝓔_U[g]` is *the average of the restrictions
of shifts of `g`*.  Since each such restriction is a `d`-restriction of `f`, its normalised
`L²` norm is at most `ε`, and by Jensen neither `𝓔_U[g]` nor `𝓔_U²[g]` can be worse.

This file formalises

* the generic **Jensen lemma** for the normalised `L²` norm over a finite average
  (`l2sq_avg_le`),
* the **commutation identity** `restr ∘ shift ∘ eOp = average of restr ∘ shift`
  (`restr_shift_eOp`, `restr_shift_eOpV`),
* the resulting **globalness preservation** `GlobalBS d ε f → GlobalBS d ε (eOpV v f)`
  and the **`𝒯`-bound** `l2sq (restr Q ι (shift T (TOp v d f))) ≤ C(q,d)·ε`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

/-! ## A Cauchy–Schwarz/Jensen toolkit for the normalised `L²` norm -/

/-- Cauchy–Schwarz for a finite sum of complex numbers. -/
lemma norm_sum_sq_le {ι : Type*} (s : Finset ι) (g : ι → ℂ) :
    ‖∑ i ∈ s, g i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖g i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖g i‖ := norm_sum_le _ _
  calc ‖∑ i ∈ s, g i‖ ^ 2 ≤ (∑ i ∈ s, ‖g i‖) ^ 2 :=
        sq_le_sq' (by linarith [norm_nonneg (∑ i ∈ s, g i)]) h1
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖g i‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖g i‖)

/-- `l2sq` of the zero function. -/
lemma l2sq_zero {m n : ℕ} :
    l2sq (m := m) (n := n) (0 : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) = 0 := by
  simp [l2sq]

/-- Homogeneity of `l2sq` under scalar multiplication. -/
lemma l2sq_smul {m n : ℕ} (c : ℂ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (c • f) = ‖c‖ ^ 2 * l2sq f := by
  rw [l2sq, l2sq]
  have h : ∑ A, ‖(c • f) A‖ ^ 2 = ‖c‖ ^ 2 * ∑ A, ‖f A‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [h]; ring

/-- `l2sq` is monotone in the pointwise norm. -/
lemma l2sq_le_of_norm_le {m n : ℕ} {f g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (h : ∀ A, ‖f A‖ ≤ ‖g A‖) : l2sq f ≤ l2sq g := by
  rw [l2sq, l2sq]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun A _ => ?_) (by positivity)
  exact pow_le_pow_left₀ (norm_nonneg _) (h A) 2

/-- `l2sq` of a finite sum, Cauchy–Schwarz form. -/
lemma l2sq_sum_le {m n : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l2sq (fun A => ∑ i ∈ s, g i A) ≤ (s.card : ℝ) * ∑ i ∈ s, l2sq (g i) := by
  rw [l2sq]
  have key : ∑ A, ((s.card : ℝ) * ∑ i ∈ s, ‖g i A‖ ^ 2) =
      (s.card : ℝ) * ∑ i ∈ s, ∑ A, ‖g i A‖ ^ 2 := by
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_comm
  calc ((2:ℝ) ^ (m * n))⁻¹ * ∑ A, ‖∑ i ∈ s, g i A‖ ^ 2
      ≤ ((2:ℝ) ^ (m * n))⁻¹ * ∑ A, ((s.card : ℝ) * ∑ i ∈ s, ‖g i A‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun A _ => norm_sum_sq_le s (fun i => g i A)) (by positivity)
    _ = (s.card : ℝ) * ∑ i ∈ s, l2sq (g i) := by
        rw [key]
        have hh : ∑ i ∈ s, l2sq (g i) = ((2:ℝ) ^ (m * n))⁻¹ * ∑ i ∈ s, ∑ A, ‖g i A‖ ^ 2 := by
          simp only [l2sq]
          rw [Finset.mul_sum]
        rw [hh]; ring

/-- **Jensen for the normalised `L²` norm**: the normalised `L²` norm of a finite average of
functions is at most the average of their normalised `L²` norms. -/
lemma l2sq_avg_le {m n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ι → Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (δ : ℝ) (h : ∀ i, l2sq (g i) ≤ δ) :
    l2sq (fun A => ((Nat.card ι : ℂ))⁻¹ * ∑ i, g i A) ≤ δ := by
  rw [show Nat.card ι = Fintype.card ι from Nat.card_eq_fintype_card]
  set N : ℕ := Fintype.card ι with hN
  have hNpos : 0 < N := by
    rw [hN]; exact Fintype.card_pos_iff.mpr inferInstance
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hstep : ∀ A : Matrix (Fin m) (Fin n) 𝔽₂,
      ‖((N : ℂ))⁻¹ * ∑ i, g i A‖ ^ 2 ≤ (N : ℝ)⁻¹ * ∑ i, ‖g i A‖ ^ 2 := by
    intro A
    have h1 : ‖∑ i, g i A‖ ^ 2 ≤ (N : ℝ) * ∑ i, ‖g i A‖ ^ 2 := by
      simpa [hN] using norm_sum_sq_le (Finset.univ : Finset ι) (fun i => g i A)
    calc ‖((N : ℂ))⁻¹ * ∑ i, g i A‖ ^ 2
        = ‖((N : ℂ))⁻¹‖ ^ 2 * ‖∑ i, g i A‖ ^ 2 := by rw [norm_mul, mul_pow]
      _ ≤ ‖((N : ℂ))⁻¹‖ ^ 2 * ((N : ℝ) * ∑ i, ‖g i A‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (N : ℝ)⁻¹ * ∑ i, ‖g i A‖ ^ 2 := by
          rw [norm_inv, norm_natCast, inv_pow]
          field_simp
  rw [l2sq]
  have hsum : ∑ A, ‖((N : ℂ))⁻¹ * ∑ i, g i A‖ ^ 2 ≤ (N : ℝ)⁻¹ * ∑ i, ∑ A, ‖g i A‖ ^ 2 := by
    calc ∑ A, ‖((N : ℂ))⁻¹ * ∑ i, g i A‖ ^ 2
        ≤ ∑ A, (N : ℝ)⁻¹ * ∑ i, ‖g i A‖ ^ 2 := Finset.sum_le_sum fun A _ => hstep A
      _ = (N : ℝ)⁻¹ * ∑ i, ∑ A, ‖g i A‖ ^ 2 := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_comm
  calc ((2:ℝ) ^ (m * n))⁻¹ * ∑ A, ‖((N : ℂ))⁻¹ * ∑ i, g i A‖ ^ 2
      ≤ ((2:ℝ) ^ (m * n))⁻¹ * ((N : ℝ)⁻¹ * ∑ i, ∑ A, ‖g i A‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (N : ℝ)⁻¹ * ∑ i, l2sq (g i) := by
        have hh : ∑ i, l2sq (g i) = ((2:ℝ) ^ (m * n))⁻¹ * ∑ i, ∑ A, ‖g i A‖ ^ 2 := by
          simp only [l2sq]
          rw [Finset.mul_sum]
        rw [hh]; ring
    _ ≤ (N : ℝ)⁻¹ * ∑ i, δ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i)
          (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = δ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN]
        field_simp

/-- The elementary `3`-term Cauchy–Schwarz bound. -/
lemma norm_add3_sq_le (x y z : ℂ) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h1 : ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    have h2 := norm_add_le (x + y) z
    have h3 := norm_add_le x y
    linarith [norm_nonneg (x + y)]
  calc ‖x + y + z‖ ^ 2 ≤ (‖x‖ + ‖y‖ + ‖z‖) ^ 2 :=
        sq_le_sq' (by linarith [norm_nonneg (x + y + z)]) h1
    _ ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
        nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖y‖ - ‖z‖), sq_nonneg (‖x‖ - ‖z‖)]

/-- The `L²` bound for a three-term combination `g₁ - a•g₂ + b•g₃`. -/
lemma l2sq_sub_smul_add_smul_le {m n : ℕ} {g₁ g₂ g₃ : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (a b : ℂ) :
    l2sq (fun A => g₁ A - a * g₂ A + b * g₃ A) ≤
      3 * (l2sq g₁ + ‖a‖ ^ 2 * l2sq g₂ + ‖b‖ ^ 2 * l2sq g₃) := by
  have hpt : ∀ A, ‖g₁ A - a * g₂ A + b * g₃ A‖ ^ 2 ≤
      3 * (‖g₁ A‖ ^ 2 + ‖a‖ ^ 2 * ‖g₂ A‖ ^ 2 + ‖b‖ ^ 2 * ‖g₃ A‖ ^ 2) := by
    intro A
    have h2 : ‖-a * g₂ A‖ = ‖a‖ * ‖g₂ A‖ := by rw [norm_mul, norm_neg]
    have h3 : ‖b * g₃ A‖ = ‖b‖ * ‖g₃ A‖ := norm_mul _ _
    have h4 : g₁ A - a * g₂ A + b * g₃ A = g₁ A + (-a * g₂ A) + (b * g₃ A) := by ring
    rw [h4]
    calc ‖g₁ A + (-a * g₂ A) + (b * g₃ A)‖ ^ 2
        ≤ 3 * (‖g₁ A‖ ^ 2 + ‖-a * g₂ A‖ ^ 2 + ‖b * g₃ A‖ ^ 2) := norm_add3_sq_le _ _ _
      _ = 3 * (‖g₁ A‖ ^ 2 + ‖a‖ ^ 2 * ‖g₂ A‖ ^ 2 + ‖b‖ ^ 2 * ‖g₃ A‖ ^ 2) := by
          rw [h2, h3]; ring
  have hsum : ∑ A, (‖g₁ A‖ ^ 2 + ‖a‖ ^ 2 * ‖g₂ A‖ ^ 2 + ‖b‖ ^ 2 * ‖g₃ A‖ ^ 2) =
      (∑ A, ‖g₁ A‖ ^ 2) + ‖a‖ ^ 2 * (∑ A, ‖g₂ A‖ ^ 2)
        + ‖b‖ ^ 2 * (∑ A, ‖g₃ A‖ ^ 2) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [l2sq, l2sq, l2sq, l2sq]
  calc ((2:ℝ) ^ (m * n))⁻¹ * ∑ A, ‖g₁ A - a * g₂ A + b * g₃ A‖ ^ 2
      ≤ ((2:ℝ) ^ (m * n))⁻¹ *
          ∑ A, 3 * (‖g₁ A‖ ^ 2 + ‖a‖ ^ 2 * ‖g₂ A‖ ^ 2 + ‖b‖ ^ 2 * ‖g₃ A‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun A _ => hpt A) (by positivity)
    _ = ((2:ℝ) ^ (m * n))⁻¹ *
          (3 * ∑ A, (‖g₁ A‖ ^ 2 + ‖a‖ ^ 2 * ‖g₂ A‖ ^ 2 + ‖b‖ ^ 2 * ‖g₃ A‖ ^ 2)) := by
        rw [← Finset.mul_sum]
    _ = 3 * (((2:ℝ) ^ (m * n))⁻¹ * ∑ A, ‖g₁ A‖ ^ 2
          + ‖a‖ ^ 2 * (((2:ℝ) ^ (m * n))⁻¹ * ∑ A, ‖g₂ A‖ ^ 2)
          + ‖b‖ ^ 2 * (((2:ℝ) ^ (m * n))⁻¹ * ∑ A, ‖g₃ A‖ ^ 2)) := by
        rw [hsum]; ring

/-! ## The restriction of an average of shifts is the average of the restrictions -/

/-- **Restrictions commute with averages of shifts.** -/
lemma restr_shift_eOp {m n m' n' n'' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (Q' : Matrix (Fin n'') (Fin n) 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    restr Q ι (shift T (eOp Q' f)) =
      fun A => ((Nat.card (Matrix (Fin m) (Fin n'') 𝔽₂) : ℂ))⁻¹ *
        ∑ B : Matrix (Fin m) (Fin n'') 𝔽₂, restr Q ι (shift (T + B * Q') f) A := by
  funext A
  simp only [restr, shift, eOp]
  congr 1
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [add_assoc]

/-- **Globalness survives the averaging operator `𝔢`**. -/
theorem l2sq_restr_shift_eOp_le {m n m' n' n'' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (Q' : Matrix (Fin n'') (Fin n) 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) {d : ℕ} {ε : ℝ}
    (h : GlobalBS d ε f) (hord : hybridOrder Q ι ≤ d) :
    l2sq (restr Q ι (shift T (eOp Q' f))) ≤ ε := by
  rw [restr_shift_eOp]
  exact l2sq_avg_le _ ε fun B => h Q ι hord (T + B * Q')

/-- The subtype of functionals with `φ v = 1` is nonempty for `v ≠ 0`. -/
lemma nonempty_dual_apply_eq_one {n : ℕ} {v : Fin n → 𝔽₂} (hv : v ≠ 0) :
    Nonempty {φ : Module.Dual 𝔽₂ (Fin n → 𝔽₂) // φ v = 1} :=
  let ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one 𝔽₂ hv
  ⟨⟨f, hf⟩⟩

/-- **Restrictions commute with the combinatorial Laplacian `𝓔_v`.** -/
lemma restr_shift_eOpV {m n m' n' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (v : Fin n → 𝔽₂) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    restr Q ι (shift T (eOpV v f)) =
      fun A => ((Nat.card {φ : Module.Dual 𝔽₂ (Fin n → 𝔽₂) // φ v = 1} : ℂ))⁻¹ *
        ∑ φ : {φ : Module.Dual 𝔽₂ (Fin n → 𝔽₂) // φ v = 1},
          ((Nat.card (Matrix (Fin m) (Fin 1) 𝔽₂) : ℂ))⁻¹ *
            ∑ B : Matrix (Fin m) (Fin 1) 𝔽₂,
              restr Q ι (shift (T + B * linRow φ.1) f) A := by
  funext A
  simp only [restr, shift, eOpV, eOp, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun φ _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [add_assoc]

/-- **Globalness survives the combinatorial Laplacian `𝓔_v`**. -/
theorem l2sq_restr_shift_eOpV_le {m n m' n' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (v : Fin n → 𝔽₂) (hv : v ≠ 0) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) {d : ℕ} {ε : ℝ}
    (h : GlobalBS d ε f) (hord : hybridOrder Q ι ≤ d) :
    l2sq (restr Q ι (shift T (eOpV v f))) ≤ ε := by
  haveI := nonempty_dual_apply_eq_one hv
  rw [restr_shift_eOpV]
  exact l2sq_avg_le _ ε fun φ => l2sq_avg_le _ ε fun B => h Q ι hord (T + B * linRow φ.1)

/-- **Globalness is preserved by `𝓔_v`.** -/
theorem GlobalBS_eOpV {m n : ℕ} {v : Fin n → 𝔽₂} (hv : v ≠ 0) {d : ℕ} {ε : ℝ}
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (h : GlobalBS d ε f) :
    GlobalBS d ε (eOpV v f) :=
  fun _ _ hord _ => l2sq_restr_shift_eOpV_le _ _ v hv _ f h hord

/-! ## The `𝒯`-bound: the convexity step of `lem:inductive step` -/

/-- **The analytic content of `lem:inductive step`.**  If `f` is `(d,ε)`-restriction global
and `(Q,ι)` presents a restriction of order at most `d`, then every restriction of
`𝒯_{d,U}[f]` (where `U = span v`) has normalised `L²` norm at most `100 · 2^{4d} · ε`. -/
theorem l2sq_restr_shift_TOp_le {m n m' n' : ℕ}
    (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (v : Fin n → 𝔽₂) (hv : v ≠ 0) (d : ℕ) (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : GlobalBS d ε f) (hord : hybridOrder Q ι ≤ d) :
    l2sq (restr Q ι (shift T (TOp v d f))) ≤ 100 * (2:ℝ) ^ (4 * d) * ε := by
  set a : ℂ := (2:ℂ) ^ d + (2:ℂ) ^ (d - 1) with ha
  set b : ℂ := (2:ℂ) ^ (2 * d - 1) with hb
  have heq : restr Q ι (shift T (TOp v d f)) =
      fun A => restr Q ι (shift T f) A - a * restr Q ι (shift T (eOpV v f)) A
        + b * restr Q ι (shift T (eOpV v (eOpV v f))) A := by
    funext A
    simp only [restr, shift, TOp, ha, hb, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    try ring
  rw [heq]
  have h1 : l2sq (restr Q ι (shift T f)) ≤ ε := h Q ι hord T
  have h2 : l2sq (restr Q ι (shift T (eOpV v f))) ≤ ε :=
    l2sq_restr_shift_eOpV_le Q ι v hv T f h hord
  have h3 : l2sq (restr Q ι (shift T (eOpV v (eOpV v f)))) ≤ ε :=
    l2sq_restr_shift_eOpV_le Q ι v hv T (eOpV v f) (GlobalBS_eOpV hv h) hord
  have hna : ‖a‖ ^ 2 ≤ (2:ℝ) ^ (2 * d + 2) := by
    have h2d : ‖(2:ℂ) ^ d‖ = (2:ℝ) ^ d := by rw [norm_pow, Complex.norm_ofNat]
    have h2d1 : ‖(2:ℂ) ^ (d - 1)‖ ≤ (2:ℝ) ^ d := by
      rw [norm_pow, Complex.norm_ofNat]
      exact pow_le_pow_right₀ (a := (2:ℝ)) (by norm_num) (by omega)
    have hle : ‖a‖ ≤ (2:ℝ) ^ (d + 1) := by
      rw [ha]
      calc ‖(2:ℂ) ^ d + (2:ℂ) ^ (d - 1)‖ ≤ ‖(2:ℂ) ^ d‖ + ‖(2:ℂ) ^ (d - 1)‖ := norm_add_le _ _
        _ ≤ (2:ℝ) ^ d + (2:ℝ) ^ d := add_le_add h2d.le h2d1
        _ = (2:ℝ) ^ (d + 1) := by rw [pow_succ]; ring
    calc ‖a‖ ^ 2 ≤ ((2:ℝ) ^ (d + 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = (2:ℝ) ^ (2 * d + 2) := by
          rw [← pow_mul, show (d + 1) * 2 = 2 * d + 2 by ring]
  have hnb : ‖b‖ ^ 2 ≤ (2:ℝ) ^ (4 * d) := by
    rw [hb, norm_pow, Complex.norm_ofNat]
    calc ((2:ℝ) ^ (2 * d - 1)) ^ 2 = (2:ℝ) ^ ((2 * d - 1) * 2) := by rw [pow_mul]
      _ ≤ (2:ℝ) ^ (4 * d) :=
          pow_le_pow_right₀ (a := (2:ℝ)) (by norm_num) (by omega)
  refine (l2sq_sub_smul_add_smul_le a b).trans ?_
  have hmain : 3 * (l2sq (restr Q ι (shift T f)) +
        ‖a‖ ^ 2 * l2sq (restr Q ι (shift T (eOpV v f))) +
        ‖b‖ ^ 2 * l2sq (restr Q ι (shift T (eOpV v (eOpV v f))))) ≤
      3 * (ε + (2:ℝ) ^ (2 * d + 2) * ε + (2:ℝ) ^ (4 * d) * ε) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have ha' : ‖a‖ ^ 2 * l2sq (restr Q ι (shift T (eOpV v f))) ≤
        (2:ℝ) ^ (2 * d + 2) * ε :=
      mul_le_mul hna h2 (l2sq_nonneg _) (by positivity)
    have hb' : ‖b‖ ^ 2 * l2sq (restr Q ι (shift T (eOpV v (eOpV v f)))) ≤
        (2:ℝ) ^ (4 * d) * ε := by
      calc ‖b‖ ^ 2 * _ ≤ (2:ℝ) ^ (4 * d) * l2sq (restr Q ι (shift T (eOpV v (eOpV v f)))) :=
            mul_le_mul_of_nonneg_right hnb (l2sq_nonneg _)
        _ ≤ (2:ℝ) ^ (4 * d) * ε := mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  refine hmain.trans ?_
  have h6 : (1:ℝ) + (2:ℝ) ^ (2 * d + 2) + (2:ℝ) ^ (4 * d) ≤ 6 * (2:ℝ) ^ (4 * d) := by
    have hp : (1:ℝ) ≤ (2:ℝ) ^ (4 * d) := one_le_pow₀ (by norm_num)
    by_cases hd : d = 0
    · subst hd; norm_num
    · have h2 : (2:ℝ) ^ (2 * d + 2) ≤ (2:ℝ) ^ (4 * d) :=
        pow_le_pow_right₀ (a := (2:ℝ)) (by norm_num) (by omega)
      nlinarith
  have hfin : 3 * (ε + (2:ℝ) ^ (2 * d + 2) * ε + (2:ℝ) ^ (4 * d) * ε) ≤
      100 * (2:ℝ) ^ (4 * d) * ε := by
    nlinarith [hε, h6, mul_nonneg hε (mul_nonneg (by norm_num : (0:ℝ) ≤ 6)
      (by positivity : (0:ℝ) ≤ (2:ℝ) ^ (4 * d)))]
  exact hfin

/-- **Globalness is preserved by `𝒯_{d,U}`** (with the constant loss of the convexity step):
if `f` is `(d,ε)`-restriction global then so is `𝒯_{d,U}[f]` with radius `O(2^{4d})ε`. -/
theorem GlobalBS_TOp {m n : ℕ} {v : Fin n → 𝔽₂} (hv : v ≠ 0) {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (h : GlobalBS d ε f) :
    GlobalBS d (100 * (2:ℝ) ^ (4 * d) * ε) (TOp v d f) :=
  fun Q ι hord T => l2sq_restr_shift_TOp_le Q ι v hv d T f hε h hord

end

end Submission.Grassmann
