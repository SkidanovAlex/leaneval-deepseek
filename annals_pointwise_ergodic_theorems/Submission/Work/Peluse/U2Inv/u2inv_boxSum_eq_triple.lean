import Mathlib
import Submission.Work.Peluse.U2Inv.u2inv_tsum_DeltaZ
import Submission.Work.Peluse.U2Inv.u2inv_cubeTermZ_two
import Submission.Work.Peluse.U2Inv.u2inv_muL_fiber

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.U2Inv

noncomputable section

open Finset

/-- The pair `(a, b)` packaged as a function `Fin 2 → α`. -/
def finTwo {α : Type*} (a b : α) : Fin 2 → α := fun i => if i = (0 : Fin 2) then a else b

@[simp] lemma finTwo_zero {α : Type*} (a b : α) : finTwo a b (0 : Fin 2) = a := by
  simp [finTwo]

@[simp] lemma finTwo_one {α : Type*} (a b : α) : finTwo a b (1 : Fin 2) = b := by
  simp [finTwo]

/-- Summing over the two shift coordinates of a `t = 2` box norm. -/
lemma sum_finTwo {α M : Type*} [Fintype α] [AddCommMonoid M] (F : (Fin 2 → α) → M) :
    (∑ z : Fin 2 → α, F z) = ∑ a : α, ∑ b : α, F (finTwo a b) := by
  let e : (Fin 2 → α) ≃ α × α :=
    { toFun := fun z => (z 0, z 1)
      invFun := fun p => finTwo p.1 p.2
      left_inv := by
        intro z
        funext i
        fin_cases i <;> simp [finTwo]
      right_inv := by
        intro p
        obtain ⟨a, b⟩ := p
        simp [finTwo] }
  have hsymm : ∀ p : α × α, e.symm p = finTwo p.1 p.2 := fun p => rfl
  calc ∑ z : Fin 2 → α, F z
      = ∑ p : α × α, F (e.symm p) := (Equiv.sum_comp e.symm F).symm
    _ = ∑ a : α, ∑ b : α, F (finTwo a b) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by rw [hsymm]))

/-! ## The `t = 2` box sum is a `muL`-weighted average of difference operators -/

/-- The `t = 2` box sum, expanded into the second difference operators `DeltaZ`:
the whole content of the "change of variables" `x ↦ x - h₁' - h₂'` in Peluse's proof of
Lemma 2.4. -/
lemma rawSum_two_eq (Q0 : Finset ℤ) (L : ℕ) (f : ℤ → ℂ) (hf : Work.Peluse.SupportIn f L) :
    Work.Peluse.BoxNorm.rawSum 2 (fun _ : Fin 2 => Q0) f
      = ∑ a ∈ Q0, ∑ b ∈ Q0, ∑ a' ∈ Q0, ∑ b' ∈ Q0,
          ∑ x ∈ Work.Peluse.symIcc L, DeltaZ (a - a') (b - b') f x := by
  rw [Work.Peluse.BoxNorm.rawSum]
  change (∑ z : Fin 2 → {x : ℤ // x ∈ Q0}, ∑ z' : Fin 2 → {x : ℤ // x ∈ Q0},
      ∑' x : ℤ, Work.Peluse.BoxNorm.cubeTermZ (fun _ : Fin 2 => Q0) f z z' x) = _
  simp only [Finset.sum_subtype Q0 (p := fun x => x ∈ Q0) (fun x => Iff.rfl)]
  rw [sum_finTwo]
  simp_rw [sum_finTwo]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
    Finset.sum_congr rfl (fun a' _ => Finset.sum_congr rfl (fun b' _ => ?_))))
  rw [show (∑' x : ℤ, Work.Peluse.BoxNorm.cubeTermZ (fun _ : Fin 2 => Q0) f
        (finTwo a b) (finTwo a' b') x)
      = ∑' x : ℤ, DeltaZ (a.1 - a'.1) (b.1 - b'.1) f (x + (a'.1 + b'.1)) from by
    refine tsum_congr (fun x => ?_)
    rw [u2inv_cubeTermZ_two]
    simp only [finTwo_zero, finTwo_one]
    rw [add_assoc]]
  exact u2inv_tsum_DeltaZ L f hf (a.1 - a'.1) (b.1 - b'.1) (a'.1 + b'.1)

/-- Regrouping the two pairs of shift sums by differences: this is the two-dimensional
form of the fibre identity for Peluse's weight `muL`. -/
lemma fiber_two (m : ℕ) (W : ℤ → ℤ → ℂ) :
    (∑ a ∈ Work.Peluse.arithIcc 1 m, ∑ a' ∈ Work.Peluse.arithIcc 1 m,
        ∑ b ∈ Work.Peluse.arithIcc 1 m, ∑ b' ∈ Work.Peluse.arithIcc 1 m,
          W (a - a') (b - b'))
      = ((m : ℂ) ^ 2) ^ 2 *
          ∑ α ∈ Work.Peluse.symIcc (m - 1), ∑ β ∈ Work.Peluse.symIcc (m - 1),
            (Work.Peluse.muL m α : ℂ) * (Work.Peluse.muL m β : ℂ) * W α β := by
  have h : (∑ a ∈ Work.Peluse.arithIcc 1 m, ∑ a' ∈ Work.Peluse.arithIcc 1 m,
        ∑ b ∈ Work.Peluse.arithIcc 1 m, ∑ b' ∈ Work.Peluse.arithIcc 1 m,
          W (a - a') (b - b'))
      = ((m : ℂ) ^ 2) * ∑ α ∈ Work.Peluse.symIcc (m - 1), (Work.Peluse.muL m α : ℂ) *
          (∑ b ∈ Work.Peluse.arithIcc 1 m, ∑ b' ∈ Work.Peluse.arithIcc 1 m, W α (b - b')) :=
    u2inv_muL_fiber m (fun α => ∑ b ∈ Work.Peluse.arithIcc 1 m,
      ∑ b' ∈ Work.Peluse.arithIcc 1 m, W α (b - b'))
  have h2 : ∀ α : ℤ, (∑ b ∈ Work.Peluse.arithIcc 1 m,
        ∑ b' ∈ Work.Peluse.arithIcc 1 m, W α (b - b'))
      = ((m : ℂ) ^ 2) * ∑ β ∈ Work.Peluse.symIcc (m - 1),
          (Work.Peluse.muL m β : ℂ) * W α β :=
    fun α => u2inv_muL_fiber m (fun β => W α β)
  rw [h]
  simp only [h2]
  rw [show ((m : ℂ) ^ 2) ^ 2 = ((m : ℂ) ^ 2) * ((m : ℂ) ^ 2) from by ring]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
  ring

/-- The normalising constant of the box norm in the case at hand. -/
lemma boxScaling_two (L m : ℕ) :
    Work.Peluse.BoxNorm.boxScaling 2 (fun _ : Fin 2 => Work.Peluse.arithIcc 1 m)
        (Work.Peluse.symIcc L)
      = ((2 * L + 1 : ℕ) : ℝ)⁻¹ * (((m : ℝ) ^ 2)⁻¹) * (((m : ℝ) ^ 2)⁻¹) := by
  unfold Work.Peluse.BoxNorm.boxScaling
  simp only [Fin.prod_univ_two, Work.Peluse.U2Inv.card_symIcc,
    Work.Peluse.U2Inv.card_arithIcc_one]
  simp_rw [show ((m : ℝ)⁻¹ * (m : ℝ)⁻¹) = (((m : ℝ) ^ 2)⁻¹) from by
    rw [← inv_pow, pow_two]]

/-- The (complex) normalising constant, with all the casts pushed inside. -/
lemma boxScaling_two_cast (L m : ℕ) :
    (((Work.Peluse.BoxNorm.boxScaling 2 (fun _ : Fin 2 => Work.Peluse.arithIcc 1 m)
        (Work.Peluse.symIcc L) : ℝ)) : ℂ)
      = ((Work.Peluse.symIcc L).card : ℂ)⁻¹ * (((m : ℂ) ^ 2)⁻¹) * (((m : ℂ) ^ 2)⁻¹) := by
  rw [boxScaling_two, Work.Peluse.U2Inv.card_symIcc]
  push_cast
  ring

/-- Cancellation of the two reciprocal factors of `a` against `a * a` (the regime `a ≠ 0`). -/
lemma mul_inv_sq_cancel (c a Z : ℂ) (ha : a ≠ 0) :
    c * a⁻¹ * a⁻¹ * ((a * a) * Z) = c * Z := by
  calc c * a⁻¹ * a⁻¹ * ((a * a) * Z)
      = c * (a⁻¹ * a⁻¹) * ((a * a) * Z) := by ring
    _ = c * ((a * a)⁻¹) * ((a * a) * Z) := by
        conv_lhs => rw [← mul_inv]
    _ = c * (((a * a)⁻¹) * ((a * a) * Z)) := by ring
    _ = c * ((((a * a)⁻¹) * (a * a)) * Z) := by ring
    _ = c * (1 * Z) := by rw [inv_mul_cancel₀ (mul_ne_zero ha ha)]
    _ = c * Z := by ring

theorem u2inv_boxSum_eq_triple (L m : ℕ) (f : ℤ → ℂ) (hf : Work.Peluse.SupportIn f L) :
    Work.Peluse.boxSumPow 2 (fun _ : Fin 2 => Work.Peluse.arithIcc 1 m)
        (Work.Peluse.symIcc L) f
      = ((Work.Peluse.symIcc L).card : ℂ)⁻¹ * Work.Peluse.U2Inv.T3 L m f := by
  rcases eq_or_ne m 0 with hm0 | hm0
  · subst m
    have hempty : Work.Peluse.arithIcc 1 0 = ∅ :=
      Finset.card_eq_zero.mp (Work.Peluse.U2Inv.card_arithIcc_one 0)
    rw [Work.Peluse.BoxNorm.boxSumPow_eq_scaling,
      rawSum_two_eq (Work.Peluse.arithIcc 1 0) L f hf, hempty]
    simp [Work.Peluse.U2Inv.T3, Work.Peluse.muL]
  · set Z : ℂ := ∑ α ∈ Work.Peluse.symIcc (m - 1), ∑ β ∈ Work.Peluse.symIcc (m - 1),
        (Work.Peluse.muL m α : ℂ) * (Work.Peluse.muL m β : ℂ) *
          ∑ x ∈ Work.Peluse.symIcc L, DeltaZ α β f x with hZ
    have hfib : (∑ a ∈ Work.Peluse.arithIcc 1 m, ∑ a' ∈ Work.Peluse.arithIcc 1 m,
          ∑ b ∈ Work.Peluse.arithIcc 1 m, ∑ b' ∈ Work.Peluse.arithIcc 1 m,
            ∑ x ∈ Work.Peluse.symIcc L, DeltaZ (a - a') (b - b') f x)
        = (((m : ℂ) ^ 2) ^ 2) * Z := by
      rw [show (∑ a ∈ Work.Peluse.arithIcc 1 m, ∑ a' ∈ Work.Peluse.arithIcc 1 m,
            ∑ b ∈ Work.Peluse.arithIcc 1 m, ∑ b' ∈ Work.Peluse.arithIcc 1 m,
              ∑ x ∈ Work.Peluse.symIcc L, DeltaZ (a - a') (b - b') f x)
          = (((m : ℂ) ^ 2) ^ 2) * ∑ α ∈ Work.Peluse.symIcc (m - 1),
              ∑ β ∈ Work.Peluse.symIcc (m - 1),
                (Work.Peluse.muL m α : ℂ) * (Work.Peluse.muL m β : ℂ) *
                  ∑ x ∈ Work.Peluse.symIcc L, DeltaZ α β f x from
          fiber_two m (fun α β => ∑ x ∈ Work.Peluse.symIcc L, DeltaZ α β f x)]
    have hT3 : Work.Peluse.U2Inv.T3 L m f = Z := by
      rw [hZ]
      unfold Work.Peluse.U2Inv.T3
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      exact (Finset.mul_sum (Work.Peluse.symIcc L) (fun x => DeltaZ a b f x)
        ((Work.Peluse.muL m a : ℂ) * (Work.Peluse.muL m b : ℂ))).symm
    have hswap : (∑ a ∈ Work.Peluse.arithIcc 1 m, ∑ b ∈ Work.Peluse.arithIcc 1 m,
          ∑ a' ∈ Work.Peluse.arithIcc 1 m, ∑ b' ∈ Work.Peluse.arithIcc 1 m,
            ∑ x ∈ Work.Peluse.symIcc L, DeltaZ (a - a') (b - b') f x)
        = (∑ a ∈ Work.Peluse.arithIcc 1 m, ∑ a' ∈ Work.Peluse.arithIcc 1 m,
            ∑ b ∈ Work.Peluse.arithIcc 1 m, ∑ b' ∈ Work.Peluse.arithIcc 1 m,
              ∑ x ∈ Work.Peluse.symIcc L, DeltaZ (a - a') (b - b') f x) :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    rw [Work.Peluse.BoxNorm.boxSumPow_eq_scaling,
      rawSum_two_eq (Work.Peluse.arithIcc 1 m) L f hf, hswap, hfib, hT3, boxScaling_two_cast]
    rw [show ((m : ℂ) ^ 2) ^ 2 = ((m : ℂ) ^ 2) * ((m : ℂ) ^ 2) from by ring]
    exact mul_inv_sq_cancel (((Work.Peluse.symIcc L).card : ℂ)⁻¹) ((m : ℂ) ^ 2) Z
      (pow_ne_zero 2 (by exact_mod_cast hm0))

end

end Work.Peluse.U2Inv
