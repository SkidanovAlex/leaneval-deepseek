
import Mathlib
import Submission.Commons.Combinatorics.Transference.gcs_fold
import Submission.Commons.Combinatorics.Transference.Unorm_pow
import Submission.Commons.Combinatorics.Transference.Unorm_nonneg

set_option linter.style.haveILetI false

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- Elementary algebraic identity: if `s.card + 1 = n` then
`(a ^ n * N) * ∏_{i ∈ s} (A i ^ n * N) = (N * a * ∏_{i ∈ s} A i) ^ n`. -/
lemma mul_prod_pow_eq {ι : Type*} (s : Finset ι) (n : ℕ) (A : ι → ℝ) (a N : ℝ)
    (hcard : s.card + 1 = n) :
    (a ^ n * N) * ∏ i ∈ s, (A i ^ n * N) = (N * a * (∏ i ∈ s, A i)) ^ n := by
  have h1 : ∏ i ∈ s, (A i ^ n * N) = (∏ i ∈ s, A i) ^ n * N ^ s.card := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const]
  rw [h1]
  have hNn : N * N ^ s.card = N ^ n := by rw [← pow_succ', hcard]
  calc (a ^ n * N) * ((∏ i ∈ s, A i) ^ n * N ^ s.card)
      = a ^ n * (∏ i ∈ s, A i) ^ n * (N * N ^ s.card) := by ring
    _ = a ^ n * (∏ i ∈ s, A i) ^ n * N ^ n := by rw [hNn]
    _ = (a * (∏ i ∈ s, A i) * N) ^ n := by rw [← mul_pow, ← mul_pow]
    _ = (N * a * (∏ i ∈ s, A i)) ^ n := by ring

/-- Rewriting the product of the Gowers cube sums in terms of the `U^d` norms: if
`s.card + 1 = 2 ^ d` then
`cubeSum d f * ∏_{ω ∈ s} cubeSum d (g ω) = (|G|^{d+1} · Unorm d f · ∏_{ω ∈ s} Unorm d (g ω))^{2^d}`. -/
lemma cubeSum_mul_prod_eq_pow {G : Type*} [AddCommGroup G] [Fintype G] (d : ℕ) (hd : 1 ≤ d)
    (f : G → ℝ) (s : Finset (Fin d → Bool)) (g : (Fin d → Bool) → G → ℝ)
    (hs : s.card + 1 = 2 ^ d) :
    cubeSum d f * ∏ ω ∈ s, cubeSum d (g ω)
      = ((Fintype.card G : ℝ) ^ (d + 1) * Unorm d f * ∏ ω ∈ s, Unorm d (g ω)) ^ (2 ^ d) := by
  classical
  haveI : Nonempty G := ⟨0⟩
  have hMne : (Fintype.card G : ℝ) ^ (d + 1) ≠ 0 := by positivity
  have hUf : cubeSum d f = Unorm d f ^ (2 ^ d) * (Fintype.card G : ℝ) ^ (d + 1) := by
    rw [Unorm_pow d hd f, div_mul_cancel₀ _ hMne]
  have hUg : ∀ ω : Fin d → Bool, cubeSum d (g ω)
      = Unorm d (g ω) ^ (2 ^ d) * (Fintype.card G : ℝ) ^ (d + 1) := by
    intro ω
    rw [Unorm_pow d hd (g ω), div_mul_cancel₀ _ hMne]
  have hprodeq : ∏ ω ∈ s, cubeSum d (g ω)
      = ∏ ω ∈ s, Unorm d (g ω) ^ (2 ^ d) * (Fintype.card G : ℝ) ^ (d + 1) :=
    Finset.prod_congr rfl (fun ω _ => hUg ω)
  rw [hUf, hprodeq]
  exact mul_prod_pow_eq s (2 ^ d) (fun ω => Unorm d (g ω)) (Unorm d f)
    ((Fintype.card G : ℝ) ^ (d + 1)) hs

/-- `gcs_fold` expressed in terms of the Gowers `U^d` norm: the inner pairing at the shift
`H` is bounded by `|G|^{d+1} ‖f‖_{U^d}` times the product of the `U^d` norms of the
functions `g_{ω·H}(x) = ∏_j F_j (x + ω·H_j)`. -/
theorem gcs_fold_Unorm {G : Type*} [AddCommGroup G] [Fintype G] (d : ℕ) (hd : 1 ≤ d)
    (f : G → ℝ) {K : ℕ} (F : Fin K → G → ℝ) (H : Fin K → Fin d → G) :
    |∑ h : Fin d → G, ∑ x : G, f x * ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
        ∏ j : Fin K,
          F j (x + (∑ i, if ω i then h i else 0) + (∑ i, if ω i then H j i else 0))|
      ≤ ((Fintype.card G : ℝ) ^ (d+1)) * Unorm d f *
          ∏ ω ∈ (Finset.univ.erase (0 : Fin d → Bool)),
            Unorm d (fun x => ∏ j : Fin K, F j (x + ∑ i, if ω i then H j i else 0)) := by
  classical
  haveI : Nonempty G := ⟨0⟩
  let g : (Fin d → Bool) → G → ℝ :=
    fun ω x => ∏ j : Fin K, F j (x + ∑ i, if ω i then H j i else 0)
  let s : Finset (Fin d → Bool) := Finset.univ.erase (0 : Fin d → Bool)
  let B : ℝ := ∑ h : Fin d → G, ∑ x : G, f x * ∏ ω ∈ s, ∏ j : Fin K,
        F j (x + (∑ i, if ω i then h i else 0) + (∑ i, if ω i then H j i else 0))
  let C : ℝ := (Fintype.card G : ℝ) ^ (d + 1) * Unorm d f * ∏ ω ∈ s, Unorm d (g ω)
  have hcard : s.card + 1 = 2 ^ d := by
    change (Finset.univ.erase (0 : Fin d → Bool)).card + 1 = 2 ^ d
    rw [Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  have hgcs := Commons.Combinatorics.Transference.gcs_fold d f F H
  have hprod := cubeSum_mul_prod_eq_pow d hd f s g hcard
  have hkey : B ^ (2 ^ d) ≤ C ^ (2 ^ d) := by
    rw [← hprod]
    exact hgcs
  have hCnonneg : 0 ≤ C := by
    simp only [C]
    exact mul_nonneg (mul_nonneg (by positivity) (Unorm_nonneg d hd f))
      (Finset.prod_nonneg (fun ω _ => Unorm_nonneg d hd (g ω)))
  have hBnonneg : 0 ≤ B ^ (2 ^ d) :=
    Even.pow_nonneg (Nat.even_pow.mpr ⟨even_two, by positivity⟩) B
  have hle : |B| ^ (2 ^ d) ≤ C ^ (2 ^ d) := by
    rw [← abs_pow, abs_le]
    exact ⟨by linarith [hBnonneg, pow_nonneg hCnonneg (2 ^ d)], hkey⟩
  exact (pow_le_pow_iff_left₀ (abs_nonneg B) hCnonneg (by positivity : (2 : ℕ) ^ d ≠ 0)).mp hle

end Commons.Combinatorics.Transference
