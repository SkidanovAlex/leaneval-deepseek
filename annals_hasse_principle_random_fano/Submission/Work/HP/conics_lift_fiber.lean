import Mathlib
import Submission.Work.HP.ConicsDefs

/-!
# The number of coefficient vectors with a prescribed value at a fixed nonzero point

For a prime `p`, a nonzero vector `v : Fin 3 → ZMod p` and any `c : ZMod p`, the number of
coefficient vectors `B : Mon 2 2 → ZMod p` of ternary quadratic forms with `qf B v = c` is
`p ^ 5`.

This is the elementary counting ingredient used when lifting forms mod `p^2`: the map
`B ↦ qf B v` is a nonzero `ZMod p`-linear functional on the `6`-dimensional space
`Mon 2 2 → ZMod p`, so each of its fibres has `p ^ (6 - 1) = p ^ 5` elements.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP

/-! ## Fibres of a linear functional `B ↦ ∑ i, B i * a i` on a function space -/

/-- The fibre of the linear functional `B ↦ ∑ i, B i * a i` over `c` is in bijection with the
functions on the coordinates other than `j`, provided `a j ≠ 0`: the `j`-th coordinate is
uniquely determined by the remaining ones. -/
private def fiberEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [Field R] (a : ι → R) {j : ι} (hj : a j ≠ 0) (c : R) :
    {B : ι → R // ∑ i, B i * a i = c} ≃ ({i : ι // i ≠ j} → R) where
  toFun B := fun k => B.1 k.1
  invFun g := ⟨fun i => if h : i = j
      then (c - ∑ k : {i : ι // i ≠ j}, g k * a k.1) * (a j)⁻¹
      else g ⟨i, h⟩, by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
        (fun i => (if h : i = j then (c - ∑ k : {i : ι // i ≠ j}, g k * a k.1) * (a j)⁻¹
          else g ⟨i, h⟩) * a i) (Finset.mem_univ j)
    rw [Finset.sum_subtype (p := fun x => x ≠ j) (F := inferInstance) (Finset.univ.erase j)
        (by intro x; simp [Finset.mem_erase])
        (fun i => (if h : i = j then (c - ∑ k : {i : ι // i ≠ j}, g k * a k.1) * (a j)⁻¹
          else g ⟨i, h⟩) * a i)] at hsplit
    rw [← hsplit]
    have hs : (∑ k : {i : ι // i ≠ j},
        (fun i => (if h : i = j then (c - ∑ k : {i : ι // i ≠ j}, g k * a k.1) * (a j)⁻¹
          else g ⟨i, h⟩) * a i) k.1)
        = ∑ k : {i : ι // i ≠ j}, g k * a k.1 := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [dif_neg k.2]
    rw [hs]
    have hj' : (if h : j = j then (c - ∑ k : {i : ι // i ≠ j}, g k * a k.1) * (a j)⁻¹
          else g ⟨j, h⟩) * a j = c - ∑ k : {i : ι // i ≠ j}, g k * a k.1 := by
      rw [dif_pos rfl, mul_assoc, inv_mul_cancel₀ hj, mul_one]
    rw [hj']
    ring⟩
  left_inv := by
    intro B
    apply Subtype.ext
    funext i
    by_cases h : i = j
    · simp only [dif_pos h]
      rw [h]
      have hsplit := Finset.sum_erase_add (Finset.univ : Finset ι)
          (fun i => B.1 i * a i) (Finset.mem_univ j)
      rw [Finset.sum_subtype (p := fun x => x ≠ j) (F := inferInstance) (Finset.univ.erase j)
          (by intro x; simp [Finset.mem_erase]) (fun i => B.1 i * a i)] at hsplit
      have hS : (∑ k : {i : ι // i ≠ j}, B.1 k.1 * a k.1) + B.1 j * a j = c := by
        rw [hsplit]; exact B.2
      have hkey : B.1 j * a j = c - ∑ k : {i : ι // i ≠ j}, B.1 k.1 * a k.1 :=
        eq_sub_of_add_eq' hS
      rw [← hkey, mul_assoc, mul_inv_cancel₀ hj, mul_one]
    · simp only [dif_neg h]
  right_inv := by
    intro g
    funext k
    simp only [dif_neg k.2]

/-- The number of functions `B : ι → R` with `∑ i, B i * a i = c` equals
`|R| ^ (|ι| - 1)`, provided some coefficient `a j` is nonzero. -/
private lemma card_fiber_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [Field R] [Fintype R] [DecidableEq R] (a : ι → R) {j : ι}
    (hj : a j ≠ 0) (c : R) :
    Fintype.card {B : ι → R // ∑ i, B i * a i = c} = Fintype.card R ^ (Fintype.card ι - 1) := by
  rw [Fintype.card_congr (fiberEquiv a hj c), Fintype.card_fun]
  congr 1
  have h := Fintype.card_subtype_compl (α := ι) (p := fun i => i = j)
  simp only [Fintype.card_subtype_eq] at h
  exact h

/-! ## A monomial detecting a nonzero coordinate -/

/-- The monomial `x_i ^ 2`, for `i : Fin 3`. -/
private def diagMon (i : Fin 3) : Mon 2 2 :=
  ⟨fun k => if k = i then 2 else 0, by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact absurd (Finset.mem_univ i) h⟩

/-- Evaluating the Veronese coordinate attached to `diagMon i` gives `v i ^ 2`. -/
private lemma prod_diagMon {R : Type*} [CommMonoid R] (i : Fin 3) (v : Fin 3 → R) :
    (∏ k, v k ^ ((diagMon i).1 k : ℕ)) = v i ^ 2 := by
  simp only [diagMon]
  rw [Finset.prod_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- For a prime `p`, a nonzero vector `v : Fin 3 → ZMod p` and any `c : ZMod p`, exactly `p ^ 5`
coefficient vectors `B : Mon 2 2 → ZMod p` satisfy `qf B v = c`. -/
theorem conics_lift_fiber (p : ℕ) [Fact p.Prime] (v : Fin 3 → ZMod p) (hv : v ≠ 0)
    (c : ZMod p) :
    Fintype.card {B : Work.HP.Mon 2 2 → ZMod p // Work.HP.Conics.qf B v = c} = p ^ 5 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, v i ≠ 0 := by
    by_contra h; push_neg at h; exact hv (funext h)
  have hcard := card_fiber_sum (R := ZMod p) (fun m => ∏ i, v i ^ (m.1 i : ℕ))
      (j := diagMon i) (by rw [prod_diagMon]; exact pow_ne_zero 2 hi) c
  change Fintype.card {B : Mon 2 2 → ZMod p // (∑ m, B m * ∏ i, v i ^ (m.1 i : ℕ)) = c}
      = p ^ 5
  rw [hcard, ZMod.card p, Conics.card_mon]

end Work.HP
