import Mathlib
import Submission.Commons.Combinatorics.Transference.Unorm_le_of_cube_lfc
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_mean
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_data

namespace Commons.NumberTheory.Sieve

open Finset
open scoped BigOperators

/-!
# Gowers `U^{k-1}` norm of `ν - 1` for a `k`-pseudorandom measure

Green–Tao's transference principle needs the bound
`‖ν - 1‖_{U^{k-1}} ≤ 2 ε^{1/2^{k-1}}` on the Gowers norm of the "correction"
`ν - 1` of a `k`-pseudorandom measure `ν`.  This is a direct consequence of

* the cube form of the linear forms condition (`KPseudorandom.1`), applied to the
  *full* family of cube forms `x ↦ x₀ + ω·h` (all `2^{k-1}` of them, including
  `ω = 0`, for which the form is `x₀`, still nonzero and pairwise
  non-proportional), and
* the multilinear (Möbius) expansion `Unorm_le_of_cube_lfc`.

The helper `cube_lfc_full` below performs the first step: it rewrites the cube
linear forms condition, which lives over `Fin k → ZMod p`, into the `(z,h)`
coordinates `ZMod p × (Fin (k-1) → ZMod p)` used by `Unorm_le_of_cube_lfc`.
-/

/-- The coefficient tuple of the cube form `y₀ + ω·h`, where `y₀` is the extra
`0`-th variable: the tuple `(1, if ω 0 then 1 else 0, …, if ω (d-1) then 1 else 0)`. -/
def gtCubeCoeff (d : ℕ) (ω : Fin d → Bool) : Fin (d + 1) → ℚ :=
  Fin.cons 1 (fun j => if ω j then 1 else 0)

lemma isSmallRat_gtCubeCoeff {d L₀ : ℕ} (h : d + 1 ≤ L₀) (ω : Fin d → Bool)
    (j : Fin (d + 1)) : IsSmallRat L₀ (gtCubeCoeff d ω j) := by
  rcases Fin.eq_zero_or_eq_succ j with h0 | ⟨i, rfl⟩
  · subst h0
    exact isSmallRat_one (by omega)
  · simp only [gtCubeCoeff, Fin.cons_succ]
    split
    · exact isSmallRat_one (by omega)
    · exact isSmallRat_zero (by omega)

lemma nonzeroTuple_gtCubeCoeff (d : ℕ) (ω : Fin d → Bool) :
    NonzeroTuple (gtCubeCoeff d ω) :=
  ⟨0, by simp [gtCubeCoeff]⟩

lemma notProp_gtCubeCoeff {d : ℕ} {ω ω' : Fin d → Bool} (h : ω ≠ ω') :
    NotProp (gtCubeCoeff d ω) (gtCubeCoeff d ω') := by
  rintro ⟨lam, hlam⟩
  have h0 := hlam 0
  simp only [gtCubeCoeff, Fin.cons_zero, mul_one] at h0
  have hlam1 : lam = 1 := h0.symm
  subst hlam1
  apply h
  funext j
  have hj := hlam j.succ
  simp only [gtCubeCoeff, Fin.cons_succ, one_mul] at hj
  cases hb : ω j <;> cases hb' : ω' j <;> simp_all

lemma linForm_gtCubeCoeff {p : ℕ} [Fact p.Prime] (d : ℕ) (ω : Fin d → Bool)
    (y : Fin (d + 1) → ZMod p) :
    linForm p (gtCubeCoeff d ω) 0 y
      = y 0 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y j.succ := by
  rw [linForm, add_zero, Fin.sum_univ_succ]
  have h0 : qmod p (gtCubeCoeff d ω 0) * y 0 = y 0 := by
    rw [show gtCubeCoeff d ω 0 = 1 by simp [gtCubeCoeff], qmod_one, one_mul]
  rw [h0]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show gtCubeCoeff d ω j.succ = (if ω j then 1 else 0) by simp [gtCubeCoeff]]
  split <;> simp [qmod_one, qmod_zero]

/-- The cube linear forms condition at scale `d`, in the `(z,h)` coordinates used by
`Unorm_le_of_cube_lfc`: every nonempty set of cube forms `ω ↦ (z ↦ z + ω·h)` has
average within `ε` of `1`. -/
theorem cube_lfc_full {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) {ν : ZMod p → ℝ}
    {ε : ℝ} (hLFC : LinFormsCond p ν ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1) ε)
    (A : Finset (Fin d → Bool)) (hA : A.Nonempty) :
    |((Fintype.card (ZMod p) : ℝ) ^ (d + 1))⁻¹ *
      (∑ z : ZMod p, ∑ h : Fin d → ZMod p,
        ∏ ω ∈ A, ν (z + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1| ≤ ε := by
  have hcard1 : 1 ≤ Fintype.card {ω : Fin d → Bool // ω ∈ A} := by
    rw [Fintype.card_coe]
    have := Finset.card_pos.mpr hA
    omega
  have hcard2 : Fintype.card {ω : Fin d → Bool // ω ∈ A} ≤ (d + 1) * 2 ^ d := by
    rw [Fintype.card_coe]
    calc A.card ≤ (Finset.univ : Finset (Fin d → Bool)).card :=
          Finset.card_le_card (by intro a _; simp)
      _ = 2 ^ d := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      _ ≤ (d + 1) * 2 ^ d := Nat.le_mul_of_pos_left _ (by omega)
  have ht1 : 1 ≤ d + 1 := by omega
  have ht2 : d + 1 ≤ 3 * (d + 1) - 4 := by omega
  have h := hLFC {ω : Fin d → Bool // ω ∈ A} hcard1 hcard2 (d + 1) ht1 ht2
    (fun i => gtCubeCoeff d i.1) (fun i j => isSmallRat_gtCubeCoeff (by omega) i.1 j)
    (fun i => nonzeroTuple_gtCubeCoeff d i.1)
    (fun i i' hii => notProp_gtCubeCoeff (fun hc => hii (Subtype.ext hc)))
    (fun _ => 0)
  simp only [linForm_gtCubeCoeff] at h
  have hcardR : ((Fintype.card (Fin (d + 1) → ZMod p) : ℝ))
      = (Fintype.card (ZMod p) : ℝ) ^ (d + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  have hprod : ∀ y : Fin (d + 1) → ZMod p,
      (∏ i : {ω : Fin d → Bool // ω ∈ A},
          ν (y 0 + ∑ j : Fin d, (if (i : Fin d → Bool) j then (1 : ZMod p) else 0) * y j.succ))
        = ∏ ω ∈ A, ν (y 0 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y j.succ) := by
    intro y
    rw [← Finset.prod_attach A
      (fun ω => ν (y 0 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y j.succ)),
      Finset.attach_eq_univ]
  rw [Finset.sum_congr rfl (fun y _ => hprod y)] at h
  have hsum : (∑ z : ZMod p, ∑ h : Fin d → ZMod p,
        ∏ ω ∈ A, ν (z + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j))
      = ∑ y : Fin (d + 1) → ZMod p,
        ∏ ω ∈ A, ν (y 0 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y j.succ) := by
    rw [← Fintype.sum_prod_type (α₁ := ZMod p) (α₂ := Fin d → ZMod p)
        (f := fun q : ZMod p × (Fin d → ZMod p) =>
          ∏ ω ∈ A, ν (q.1 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * q.2 j)),
      ← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => ZMod p))
        (fun y : Fin (d + 1) → ZMod p =>
          ∏ ω ∈ A, ν (y 0 + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * y j.succ))]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show Fin.consEquiv (fun _ : Fin (d + 1) => ZMod p) q = Fin.cons q.1 q.2 from rfl]
    simp only [Fin.cons_zero, Fin.cons_succ]
  rw [hsum, ← hcardR]
  exact h

/-- **Gowers norm bound for a `k`-pseudorandom measure.**  If `ν` satisfies the
`k`-pseudorandomness conditions (`KPseudorandom`) with error `εp`, then the
correction `ν - 1` has Gowers `U^{k-1}` norm at most `2 εp^{1/2^{k-1}}`. -/
theorem Unorm_sub_one_le_of_KPseudorandom {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 2 ≤ k)
    {ν : ZMod p → ℝ} {C₀ : ℕ → ℕ → ℝ} {εp : ℝ}
    (hP : Commons.NumberTheory.Sieve.KPseudorandom p k ν C₀ εp) :
    Commons.Combinatorics.Transference.Unorm (k - 1) (fun x => ν x - 1)
      ≤ 2 * εp ^ (((2 ^ (k - 1) : ℕ) : ℝ)⁻¹) := by
  have hd : 1 ≤ k - 1 := by omega
  have hεp : 0 ≤ εp := le_trans (abs_nonneg _) (KPseudorandom_mean hk hP)
  have hmono : LinFormsCond p ν (((k - 1) + 1) * 2 ^ (k - 1))
      (3 * ((k - 1) + 1) - 4) ((k - 1) + 1) εp := by
    have h1 : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    rw [h1]
    exact hP.1
  exact Commons.Combinatorics.Transference.Unorm_le_of_cube_lfc hd hεp (fun A hA => cube_lfc_full (d := k - 1) hd hmono A hA)

end Commons.NumberTheory.Sieve
