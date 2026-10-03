/-
# Shared definitions for the proof of `siv-second` from `struct-iii-second`

This module holds the partition of `ℤ` into blocks of length `L = N ^ deg P` and the windows
`suppWin` (containing the support of the second dual function of a function supported in the `i`-th
block) and `hWin` (containing the part of `h` which that dual function can see), together with
their elementary arithmetic properties.  It is shared by the file
`Submission/Work/KMTAreas/A4Z/sivSecondClaim_of_structIiiSecondClaim.lean` and by the auxiliary
lemmas delegated for it.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.Defs
import Submission.Work.KMTAreas.A4.kmtProj_reflect
import Submission.Work.KMTAreas.A4.two_pow_logN_le

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.InverseTheory

namespace Work.KMTAreas.A4Z

/-! ## The partition of `ℤ` into blocks of length `L` -/

/-- The `i`-th block-piece of `f`: `x ↦ f x` if `x / L = i`, and `0` otherwise. -/
def zPiece (L : ℤ) (f : ℤ → ℂ) (i : ℤ) : ℤ → ℂ := fun x => if i = x / L then f x else 0

theorem zPiece_apply (L : ℤ) (f : ℤ → ℂ) (i x : ℤ) :
    zPiece L f i x = if i = x / L then f x else 0 := rfl

theorem zPiece_eq_zero {L : ℤ} {f : ℤ → ℂ} {i x : ℤ} (h : i ≠ x / L) : zPiece L f i x = 0 :=
  if_neg h

theorem zPiece_eq_self {L : ℤ} {f : ℤ → ℂ} {i x : ℤ} (h : i = x / L) : zPiece L f i x = f x :=
  if_pos h

theorem tsum_zPiece {L : ℤ} (hL : 0 < L) (f : ℤ → ℂ) (x : ℤ) :
    (∑' i : ℤ, zPiece L f i x) = f x := by
  rw [tsum_eq_single (x / L)]
  · exact zPiece_eq_self rfl
  · intro i hi
    exact zPiece_eq_zero hi

/-- The arithmetic core of the partition: `x ∈ [iL, (i+1)L)` is equivalent to `x / L = i`. -/
theorem ediv_eq_of_mem_Ico {L : ℤ} (hL : 0 < L) {i x : ℤ}
    (h1 : i * L ≤ x) (h2 : x < (i + 1) * L) : i = x / L := by
  have hx : L * (x / L) + x % L = x := Int.mul_ediv_add_emod x L
  have hem1 : x % L < L := Int.emod_lt_of_pos x hL
  have hlt : x < ((x / L) + 1) * L := by
    have hsplit : ((x / L) + 1) * L = L * (x / L) + L := by ring
    rw [hsplit]; omega
  have hle : i ≤ x / L := by
    by_contra hc
    push_neg at hc
    have h3 : ((x / L) + 1) * L ≤ i * L := by
      have h4 : x / L + 1 ≤ i := by omega
      exact Int.mul_le_mul_of_nonneg_right h4 hL.le
    omega
  have hlt' : x / L < i + 1 := Int.ediv_lt_of_lt_mul hL h2
  omega

/-- The support of the `i`-th piece. -/
theorem zPiece_support {L : ℤ} (hL : 0 < L) {f : ℤ → ℂ} {i x : ℤ}
    (h : zPiece L f i x ≠ 0) : i * L ≤ x ∧ x < (i + 1) * L := by
  have hi : i = x / L := by
    by_contra hc
    exact h (zPiece_eq_zero hc)
  constructor
  · rw [hi]; exact Int.ediv_mul_le x hL.ne'
  · rw [hi]
    have hx : L * (x / L) + x % L = x := Int.mul_ediv_add_emod x L
    have hem1 : x % L < L := Int.emod_lt_of_pos x hL
    have hsplit : ((x / L) + 1) * L = L * (x / L) + L := by ring
    rw [hsplit]; omega

/-- Each piece has finite support. -/
theorem zPiece_finSupp {L : ℤ} (hL : 0 < L) (f : ℤ → ℂ) (i : ℤ) :
    FinSupp (zPiece L f i) := by
  refine ⟨Finset.Ico (i * L) ((i + 1) * L), fun x hx => ?_⟩
  by_contra hne
  exact hx (Finset.mem_Ico.mpr (zPiece_support hL hne))

theorem zPiece_eq_zero_of_not_mem {L : ℤ} (hL : 0 < L) {f : ℤ → ℂ} {i x : ℤ}
    (hx : x ∉ Finset.Ico (i * L) ((i + 1) * L)) : zPiece L f i x = 0 := by
  by_contra hne
  exact hx (Finset.mem_Ico.mpr (zPiece_support hL hne))

/-! ## The geometry of the second dual function -/

/-- The block length `N ^ deg P`, as an integer. -/
def blockLen (P : Polynomial ℤ) (N : ℕ) : ℤ := ((N ^ P.natDegree : ℕ) : ℤ)

/-- The sum of the absolute values of the coefficients of `P`. -/
def coeffSum (P : Polynomial ℤ) : ℤ := ∑ j ∈ P.support, |P.coeff j|

/-- A bound for the shifts `P(n) - n`, `n ∈ (N/2, N]`. -/
def shiftBd (P : Polynomial ℤ) (N : ℕ) : ℤ := (coeffSum P + 1) * blockLen P N

/-- The window containing the support of `Ã_N^{**}(f,h)` when `f` is supported in the `i`-th
block. -/
def suppWin (P : Polynomial ℤ) (N : ℕ) (i : ℤ) : Set ℤ :=
  Set.Icc (i * blockLen P N - shiftBd P N) ((i + 1) * blockLen P N + shiftBd P N)

/-- The window of `h` which `Ã_N^{**}(f,h)` can see when `f` is supported in the `i`-th block. -/
def hWin (P : Polynomial ℤ) (N : ℕ) (i : ℤ) : Set ℤ :=
  Set.Icc (i * blockLen P N - (N : ℤ)) ((i + 1) * blockLen P N)

/-- The `i`-th local second dual function. -/
def dPiece (P : Polynomial ℤ) (N : ℕ) (f h : ℤ → ℂ) (i : ℤ) : ℤ → ℂ :=
  AhalfTranspose₂ N P (zPiece (blockLen P N) f i) ((hWin P N i).indicator h)

/-- The relation between the height scale `2^k` of the projection and the block length `N^d`:
`2^k · N^d ≥ 2^{-d}`, where `k = d (l - Log N)`. -/
theorem two_pow_k_mul_blockLen_ge (P : Polynomial ℤ) {N l : ℕ} (hN : 1 ≤ N) :
    (2 : ℝ) ^ (-(P.natDegree : ℝ))
      ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)))
          * (blockLen P N : ℝ) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hx2 : (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ)) : ℝ) ≤ 2 * (N : ℝ) := by
    rw [Real.rpow_intCast (2 : ℝ) (Work.Analysis.EndVar.logN N)]
    exact Work.KMTAreas.A4.two_pow_logN_le hN
  have hxpos : (0 : ℝ) < (2 : ℝ) ^ (((Work.Analysis.EndVar.logN N : ℤ)) : ℝ) :=
    Real.rpow_pos_of_pos h2pos _
  have hN1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((l : ℝ)) :=
    Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by positivity)
  have hLcast : (blockLen P N : ℝ) = (N : ℝ) ^ (P.natDegree : ℝ) := by
    rw [blockLen]
    push_cast
    exact (Real.rpow_natCast (N : ℝ) P.natDegree).symm
  have hq : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
      * (N : ℝ) := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), div_mul_eq_mul_div, le_div_iff₀ hxpos]
    nlinarith [hx2, hN1, hNpos]
  have hfirst : ((1 : ℝ) / 2) ^ ((P.natDegree : ℝ))
      = (2 : ℝ) ^ (-(P.natDegree : ℝ)) := by
    rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [← hfirst]
  calc ((1 : ℝ) / 2) ^ ((P.natDegree : ℝ))
      ≤ ((2 : ℝ) ^ ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) * (N : ℝ))
          ^ ((P.natDegree : ℝ)) := Real.rpow_le_rpow (by norm_num) hq (by positivity)
    _ = (2 : ℝ) ^ ((P.natDegree : ℝ) * ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)))
          * (N : ℝ) ^ (P.natDegree : ℝ) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring
    _ = (2 : ℝ) ^ ((P.natDegree : ℝ) * ((l : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)))
          * (blockLen P N : ℝ) := by rw [hLcast]


/-! ## The block decomposition of a sum over `ℤ` -/

/-- **Decomposition of a summable series over `ℤ` into the sums over the blocks of length `L`.** -/
theorem mem_Ico_ediv {L : ℤ} (hL : 0 < L) {m x : ℤ} (h : m = x / L) :
    x ∈ Finset.Ico (m * L) ((m + 1) * L) := by
  rw [Finset.mem_Ico, h]
  refine ⟨Int.ediv_mul_le x hL.ne', ?_⟩
  have hxsplit : L * (x / L) + x % L = x := Int.mul_ediv_add_emod x L
  have hem : x % L < L := Int.emod_lt_of_pos x hL
  have hsplit : ((x / L) + 1) * L = L * (x / L) + L := by ring
  rw [hsplit]; omega

theorem tsum_eq_sum_blocks {L : ℤ} (hL : 0 < L) {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] {g : ℤ → E} (hg : Summable (fun x : ℤ => ‖g x‖)) :
    (∑' x : ℤ, g x) = ∑' m : ℤ, ∑ x ∈ Finset.Ico (m * L) ((m + 1) * L), g x := by
  let ff : ℤ → ℤ → E := fun x m => if m = x / L then g x else 0
  have hblock : ∀ m : ℤ, (∑' x : ℤ, ff x m)
      = ∑ x ∈ Finset.Ico (m * L) ((m + 1) * L), g x := by
    intro m
    rw [tsum_eq_sum (s := Finset.Ico (m * L) ((m + 1) * L))]
    · refine Finset.sum_congr rfl fun x hx => ?_
      show (if m = x / L then g x else 0) = g x
      rw [if_pos (ediv_eq_of_mem_Ico hL (Finset.mem_Ico.mp hx).1 (Finset.mem_Ico.mp hx).2)]
    · intro x hx
      show (if m = x / L then g x else 0) = 0
      rw [if_neg]
      intro hcon
      exact hx (mem_Ico_ediv hL hcon)
  have hsum : Summable (fun p : ℤ × ℤ => if p.2 = p.1 / L then g p.1 else 0) := by
    have hinj : Function.Injective (fun x : ℤ => (x, x / L)) :=
      fun a b h => (Prod.ext_iff.mp h).1
    refine (Function.Injective.summable_iff hinj ?_).mp ?_
    · intro p hp
      rw [if_neg]
      intro hcon
      exact hp ⟨p.1, Prod.ext rfl hcon.symm⟩
    · have hcomp : ((fun p : ℤ × ℤ => if p.2 = p.1 / L then g p.1 else 0)
          ∘ fun x : ℤ => (x, x / L)) = g := by
        funext x
        simp [Function.comp]
      rw [hcomp]
      exact hg.of_norm
  have hff : Summable (Function.uncurry ff) := hsum
  have hcomm : (∑' x : ℤ, ∑' m : ℤ, ff x m) = ∑' m : ℤ, ∑' x : ℤ, ff x m :=
    (Summable.tsum_comm (f := ff) hff).symm
  have hsingle2 : ∀ x : ℤ, (∑' m : ℤ, ff x m) = g x := by
    intro x
    rw [tsum_eq_single (x / L)]
    · simp [ff]
    · intro m hm; simp [ff, hm]
  calc (∑' x : ℤ, g x)
      = ∑' x : ℤ, ∑' m : ℤ, ff x m := tsum_congr fun x => (hsingle2 x).symm
    _ = ∑' m : ℤ, ∑' x : ℤ, ff x m := hcomm
    _ = ∑' m : ℤ, ∑ x ∈ Finset.Ico (m * L) ((m + 1) * L), g x := tsum_congr hblock

end Work.KMTAreas.A4Z
