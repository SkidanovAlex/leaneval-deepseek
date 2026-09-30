import Mathlib
import Submission.Work.BMF.vkford51_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `Usum`--`Tker` extraction : shared vocabulary

This file collects the elementary facts used by the proof that
`‖Usum k M₁ M₂ γ‖ ^ (2*r*s)` is bounded by
`(M₂)^(2rs-2s) * (M₁)^(r(2s-2)) * J r k M₁ * Tker r s M₁ M₂ k γ ε`
(Ford, *Vinogradov's integral...*, Lemma 5.1, display (5.3)).

Contents:

* the additive character `eZ` is multiplicative under sums, and has modulus `1`;
* `psVec k r M₁ a` is the vector of power sums `Σᵢ aᵢ ^ (j+1)` of a tuple
  `a : Fin r → [1,M₁]`, and `psNat` its `ℕ`-valued version;
* every such power-sum vector lies in the frequency box `Cbox r M₁ k`, and the
  fibers of `psVec` have cardinality `ncount`;
* consequently `∑_{c ∈ Cbox} ncount c = M₁ ^ r`, and for any test function `φ`
  one may replace the weighted box-sum `∑_c ncount c * φ c` by the sum over all
  tuples of `φ (psVec a)`.
-/

namespace Work.BMF.Uspt

open Finset
open scoped BigOperators

noncomputable section

/-! ## The character `eZ` -/

lemma eZ_zero : eZ 0 = 1 := by
  unfold eZ
  simp

lemma eZ_add (x y : ℝ) : eZ (x + y) = eZ x * eZ y := by
  unfold eZ
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma eZ_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    eZ (∑ i ∈ s, f i) = ∏ i ∈ s, eZ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp [eZ_zero]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, eZ_add, ih]

lemma eZ_norm (t : ℝ) : ‖eZ t‖ = 1 := by
  rw [eZ, Complex.norm_exp]
  have h : (2 * Real.pi * Complex.I * (t : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [h, Real.exp_zero]

lemma eZ_norm_le (t : ℝ) : ‖eZ t‖ ≤ 1 := le_of_eq (eZ_norm t)

/-! ## Power sums and the frequency box -/

/-- The `ℕ`-valued vector of power sums `(Σᵢ aᵢ ^ (j+1))_j` of a tuple `a : Fin r → [1, M₁]`. -/
def psNat (k r M₁ : ℕ) (a : Fin r → Finset.Icc 1 M₁) : Fin k → ℕ :=
  fun j => ∑ i, (a i).1 ^ ((j : ℕ) + 1)

/-- The `ℤ`-valued vector of power sums of a tuple `a : Fin r → [1, M₁]`. -/
def psVec (k r M₁ : ℕ) (a : Fin r → Finset.Icc 1 M₁) : Fin k → ℤ :=
  fun j => ∑ i, (((a i).1 : ℤ) ^ ((j : ℕ) + 1))

lemma psVec_eq_psNat (k r M₁ : ℕ) (a : Fin r → Finset.Icc 1 M₁) :
    psVec k r M₁ a = fun j => (psNat k r M₁ a j : ℤ) := by
  funext j
  rw [psVec, psNat]
  push_cast
  simp

lemma psNat_mem_Icc {k r M₁ : ℕ} (hr : 1 ≤ r) (hM₁ : 1 ≤ M₁)
    (a : Fin r → Finset.Icc 1 M₁) (j : Fin k) :
    psNat k r M₁ a j ∈ Finset.Icc 1 (r * M₁ ^ ((j : ℕ) + 1)) := by
  rw [Finset.mem_Icc]
  have hge : ∀ i : Fin r, 1 ≤ (a i).1 ^ ((j : ℕ) + 1) := by
    intro i
    exact one_le_pow₀ (Finset.mem_Icc.mp (a i).2).1
  have hle : ∀ i : Fin r, (a i).1 ^ ((j : ℕ) + 1) ≤ M₁ ^ ((j : ℕ) + 1) := by
    intro i
    exact Nat.pow_le_pow_left (Finset.mem_Icc.mp (a i).2).2 _
  constructor
  · calc 1 ≤ r := hr
      _ = ∑ _i : Fin r, 1 := by simp
      _ ≤ ∑ i : Fin r, (a i).1 ^ ((j : ℕ) + 1) := Finset.sum_le_sum (fun i _ => hge i)
  · calc psNat k r M₁ a j = ∑ i : Fin r, (a i).1 ^ ((j : ℕ) + 1) := rfl
      _ ≤ ∑ _i : Fin r, M₁ ^ ((j : ℕ) + 1) := Finset.sum_le_sum (fun i _ => hle i)
      _ = r * M₁ ^ ((j : ℕ) + 1) := by simp [Finset.sum_const]

lemma psVec_mem_Cbox {k r M₁ : ℕ} (hr : 1 ≤ r) (hM₁ : 1 ≤ M₁)
    (a : Fin r → Finset.Icc 1 M₁) : psVec k r M₁ a ∈ Cbox r M₁ k := by
  rw [Cbox, Finset.mem_image]
  refine ⟨fun j _ => psNat k r M₁ a j, ?_, ?_⟩
  · rw [Finset.mem_pi]
    intro j _
    exact psNat_mem_Icc hr hM₁ a j
  · rw [psVec_eq_psNat]

lemma ncount_eq_card_filter (r k M₁ : ℕ) (c : Fin k → ℤ) :
    ncount r k M₁ c = ((Finset.univ : Finset (Fin r → Finset.Icc 1 M₁)).filter
      (fun a => psVec k r M₁ a = c)).card := by
  unfold ncount psVec
  congr 1
  apply Finset.filter_congr
  intro a _
  simp [funext_iff]

lemma ncount_eq_zero_of_not_mem {k r M₁ : ℕ} (hr : 1 ≤ r) (hM₁ : 1 ≤ M₁) {c : Fin k → ℤ}
    (hc : c ∉ Cbox r M₁ k) : ncount r k M₁ c = 0 := by
  rw [ncount_eq_card_filter, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ ha
  exact hc (ha ▸ psVec_mem_Cbox hr hM₁ a)

/-- The weighted box sum of a test function only sees the tuples: summing `ncount c * φ c`
over the box is the same as summing `φ (psVec a)` over all tuples. -/
theorem sum_ncount_mul {k r M₁ : ℕ} (hr : 1 ≤ r) (hM₁ : 1 ≤ M₁) (φ : (Fin k → ℤ) → ℂ) :
    ∑ c ∈ Cbox r M₁ k, (ncount r k M₁ c : ℂ) * φ c
      = ∑ a : Fin r → Finset.Icc 1 M₁, φ (psVec k r M₁ a) := by
  have hmaps : ∀ a ∈ (Finset.univ : Finset (Fin r → Finset.Icc 1 M₁)),
      psVec k r M₁ a ∈ Cbox r M₁ k := fun a _ => psVec_mem_Cbox hr hM₁ a
  have hfib := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin r → Finset.Icc 1 M₁)))
    (t := Cbox r M₁ k) (g := psVec k r M₁) hmaps (fun i => φ (psVec k r M₁ i))
  rw [← hfib]
  apply Finset.sum_congr rfl
  intro c _
  rw [ncount_eq_card_filter]
  rw [show (∑ a ∈ (Finset.univ : Finset (Fin r → Finset.Icc 1 M₁)).filter
        (fun a => psVec k r M₁ a = c), φ (psVec k r M₁ a))
      = ∑ _a ∈ (Finset.univ : Finset (Fin r → Finset.Icc 1 M₁)).filter
        (fun a => psVec k r M₁ a = c), φ c from
    Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.mp ha).2])]
  rw [Finset.sum_const, nsmul_eq_mul]

theorem sum_ncount_eq {k r M₁ : ℕ} (hr : 1 ≤ r) (hM₁ : 1 ≤ M₁) :
    ∑ c ∈ Cbox r M₁ k, ncount r k M₁ c = M₁ ^ r := by
  have hmaps : ∀ a ∈ (Finset.univ : Finset (Fin r → Finset.Icc 1 M₁)),
      psVec k r M₁ a ∈ Cbox r M₁ k := fun a _ => psVec_mem_Cbox hr hM₁ a
  have hfib := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin r → Finset.Icc 1 M₁)))
    (t := Cbox r M₁ k) (g := psVec k r M₁) hmaps (fun _ => (1 : ℕ))
  have hcard : (∑ _a : Fin r → Finset.Icc 1 M₁, (1 : ℕ)) = M₁ ^ r := by
    simp [Fintype.card_coe]
  rw [← hcard, ← hfib]
  apply Finset.sum_congr rfl
  intro c _
  rw [ncount_eq_card_filter, Finset.card_eq_sum_ones]

end

end Work.BMF.Uspt
