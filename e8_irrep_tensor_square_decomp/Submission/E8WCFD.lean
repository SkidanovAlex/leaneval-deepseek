import Submission.E8WCFC
import Submission.E8Kostant
import Submission.E8Rec
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_Kostant_freudenthal

/-!
# The Freudenthal recursion for the Euler characteristic of the Verma modules

`Submission/E8WCFC.lean` defines `euler Λ`, the Euler characteristic
`Σ_{N ∈ W} ε(N) · chV(N · Λ)` of the Verma modules on the dot-orbit of `Λ`, and proves
`A_ρ · euler Λ = A_{Λ+ρ}`.

This file adds the remaining structural input, the **Freudenthal recursion** for `euler Λ`, which is
linear in the function: it suffices that each Verma character `chV ν` satisfies

  `(Bint ν - Bint μ) chV ν μ = 2 ∑_j ∑_k brk(μ+kα_j, j) chV ν (μ+kα_j)`,

which is the commons theorem `Commons.LinearAlgebra.Matrix.Cartan.E8_Kostant_freudenthal`
(`K(ν-μ) = dim M(ν)_μ`) transported from the `↥E8posRoots.P`-indexed statement to the
`Fin 120`-indexed one used by `Submission.E8Character.eq_of_freudenthal`.

Since `Bint (N · Λ) = Bint Λ` (`qq` is `W`-invariant and `(N·Λ) + ρ = N(Λ+ρ)`), the recursion
descends to `euler Λ`.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

noncomputable section
open scoped BigOperators

namespace Submission.E8WCFD

open Commons.LinearAlgebra.Matrix.Cartan
open Submission.WCFSetup
open Submission.E8Character
open Submission.E8WCFC
open Submission.E8Casimir

/-! ## The bracket in `P`-indexed form -/

/-- The pairing `⟪x, α⟫ = ∑ᵢ xᵢ (A⁻¹α)ᵢ`. -/
def brkP (x α : Fin 8 → ℤ) : ℤ := ∑ i, x i * E8NormTwo.E8inv.mulVec α i

lemma brk_eq_brkP (x : Fin 8 → ℤ) (j : Fin 120) : brk x j = brkP x (pR j) := by
  rw [brk, brkP]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : E8Character.coords (pR j) i = E8NormTwo.E8inv.mulVec (pR j) i := rfl
  rw [this]

lemma brkP_add (a b α : Fin 8 → ℤ) : brkP (a + b) α = brkP a α + brkP b α := by
  rw [brkP, brkP, brkP, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.add_apply]
  ring

lemma brkP_smul (c : ℤ) (a α : Fin 8 → ℤ) : brkP (c • a) α = c * brkP a α := by
  rw [brkP, brkP, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma brkP_self (α : Fin 8 → ℤ) (hα : α ∈ (E8posRoots.P : Finset (Fin 8 → ℤ))) :
    brkP α α = 2 := by
  rw [brkP]
  have h : (∑ i, α i * E8NormTwo.E8inv.mulVec α i)
      = ∑ i, ∑ l, α i * E8NormTwo.E8inv i l * α l := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [h]
  have hq : E8NormTwo.qZ α = 2 := ((E8posRoots.memP α).mp hα).1
  rw [E8NormTwo.qZ] at hq
  exact hq

lemma brkP_add_nsmul (μ α : Fin 8 → ℤ) (k : ℕ)
    (hα : α ∈ (E8posRoots.P : Finset (Fin 8 → ℤ))) :
    brkP (μ + k • α) α = brkP μ α + 2 * (k : ℤ) := by
  have h1 : brkP (μ + k • α) α = brkP μ α + brkP (k • α) α := brkP_add μ (k • α) α
  have h2 : brkP (k • α) α = (k : ℤ) * brkP α α := by
    rw [show k • α = (k : ℤ) • α from (zsmul_eq_nsmul k α).symm]
    exact brkP_smul (k : ℤ) α α
  rw [h1, h2, brkP_self α hα]
  ring

/-! ## The cardinality of the set of positive roots -/

lemma card_P : (E8posRoots.P : Finset (Fin 8 → ℤ)).card = 120 := by
  obtain ⟨s, hs, hcard⟩ := E8_posRoots_finset
  have hps : s = (E8posRoots.P : Finset (Fin 8 → ℤ)) := by
    apply Finset.ext
    intro v
    rw [hs v, E8posRoots.memP, E8posRoots.IsPosRoot]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2, h1, h3⟩
  rw [← hps]
  exact hcard

lemma pR_mem (j : Fin 120) : pR j ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)) :=
  Submission.E8Star.pR_memP j

/-- **The `Fin 120`-indexed and the `↥P`-indexed sums agree.** -/
lemma sum_pR_eq_sum_P {M : Type*} [AddCommMonoid M] (F : (Fin 8 → ℤ) → M) :
    (∑ j : Fin 120, F (pR j)) = ∑ α ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)), F α := by
  have h : (Finset.univ : Finset (Fin 120)).image pR
      = (E8posRoots.P : Finset (Fin 8 → ℤ)) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · exact Finset.image_subset_iff.mpr (fun j _ => pR_mem j)
    · rw [Finset.card_image_of_injective _ Submission.E8Casimir.pR_injective,
        Finset.card_univ, Fintype.card_fin, card_P]
  rw [← h, Finset.sum_image (Submission.E8Casimir.pR_injective.injOn)]

/-! ## The Kostant count and `Bint` -/

lemma KP_eq_Kbd (γ : Fin 8 → ℤ) : KP γ = Kbd γ := by
  change Commons.Algebra.Lie.E8KostantId.KcountP γ = Kbd γ
  rw [Kbd_eq_KcountP]

/-- `Bint` is the squared length of `ν + ρ`. -/
lemma Bint_eq_qZ (ν : Fin 8 → ℤ) : Bint ν = E8NormTwo.qZ (ν + rhoZ) := by
  simp only [Bint, E8NormTwo.qZ, Pi.add_apply, rhoZ, Pi.one_apply]

/-- A scalar times a doubled sum. -/
lemma mul_two_sum {ι : Type*} (c : ℚ) (s : Finset ι) (f : ι → ℚ) :
    c * (2 * ∑ i ∈ s, f i) = 2 * ∑ i ∈ s, c * f i := by
  rw [← Finset.mul_sum]
  ring

/-! ## The Freudenthal recursion -/

/-- `Bint` is invariant under the dot action (word form). -/
lemma Bint_dot' (L : List (Fin 8)) (ν : Fin 8 → ℤ) : Bint (dot (wactMat L) ν) = Bint ν := by
  rw [Bint_eq_qZ, Bint_eq_qZ]
  have h : dot (wactMat L) ν + rhoZ = wact L (ν + rhoZ) := by
    rw [dot, rhoV_eq, wactMat_ap]
    abel
  rw [h]
  exact qZ_wact L (ν + rhoZ)

/-- **The Freudenthal recursion for the Verma character**, in the `↥E8posRoots.P`-indexed form:
a direct transcription of the commons theorem `E8_Kostant_freudenthal`. -/
lemma chV_freudenthal_P (ν μ : Fin 8 → ℤ) :
    (E8NormTwo.qZ (ν + rhoZ) - E8NormTwo.qZ (μ + rhoZ)) * (Kbd (ν - μ) : ℚ)
      = 2 * ∑ α ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)),
          ∑ k ∈ Finset.Icc 1 ((E8NormTwo.e8ht (ν - μ)).toNat),
          (((brkP μ α + 2 * (k : ℤ) : ℤ)) : ℚ) * (Kbd (ν - μ - k • α) : ℚ) := by
  have h := congrArg (fun z : ℤ => (z : ℚ)) (E8_Kostant_freudenthal ν μ)
  simp only [brkP, Kbd] at h ⊢
  push_cast at h
  rw [h]
  push_cast
  ring_nf

/-- **The Freudenthal recursion for the Verma character `chV ν`** (in the `Fin 120`-indexed form
used by `eq_of_freudenthal`). -/
theorem chV_freudenthal (ν μ : Fin 8 → ℤ) :
    (Bint ν - Bint μ) * chV ν μ
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (ν - μ)).toNat,
          (brk (μ + k • pR j) j : ℚ) * chV ν (μ + k • pR j) := by
  have hch : ∀ x : Fin 8 → ℤ, chV ν x = (Kbd (ν - x) : ℚ) := by
    intro x
    rw [chV, KP_eq_Kbd]
  have hB : ((Bint ν : ℚ) - (Bint μ : ℚ))
      = E8NormTwo.qZ (ν + rhoZ) - E8NormTwo.qZ (μ + rhoZ) := by
    rw [← Int.cast_sub, Bint_eq_qZ, Bint_eq_qZ, Int.cast_sub]
  have htoNat : (htOf (ν - μ)).toNat = (E8NormTwo.e8ht (ν - μ)).toNat := by
    rw [Submission.E8NoKernel.ht_eq_e8ht]
  have hconv : (∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (ν - μ)).toNat,
        (brk (μ + k • pR j) j : ℚ) * chV ν (μ + k • pR j))
      = ∑ α ∈ (E8posRoots.P : Finset (Fin 8 → ℤ)),
          ∑ k ∈ Finset.Icc 1 ((E8NormTwo.e8ht (ν - μ)).toNat),
          (((brkP μ α + 2 * (k : ℤ) : ℤ)) : ℚ) * (Kbd (ν - μ - k • α) : ℚ) := by
    have hstep1 : (∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (ν - μ)).toNat,
          (brk (μ + k • pR j) j : ℚ) * chV ν (μ + k • pR j))
        = ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 ((E8NormTwo.e8ht (ν - μ)).toNat),
            (brkP (μ + k • pR j) (pR j) : ℚ) * (Kbd (ν - μ - k • pR j) : ℚ) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      refine Finset.sum_congr ?_ (fun k _ => ?_)
      · rw [htoNat]
      · rw [brk_eq_brkP, hch]
        rw [show ν - (μ + k • pR j) = ν - μ - k • pR j from by abel]
    rw [hstep1, sum_pR_eq_sum_P (fun α => ∑ k ∈ Finset.Icc 1
      ((E8NormTwo.e8ht (ν - μ)).toNat), (brkP (μ + k • α) α : ℚ) * (Kbd (ν - μ - k • α) : ℚ))]
    refine Finset.sum_congr rfl (fun α hα => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [brkP_add_nsmul μ α k hα]
  rw [hB, hch μ, hconv]
  exact chV_freudenthal_P ν μ

end Submission.E8WCFD
