import Mathlib
import Submission.Work.Analysis.EndVar.VarpAux

/-!
# Tools for the §5 assembly of the major arc part

This module contains the elementary tools used by `majorArcVarEstimate_of_varp`:

* the bilinearity of the halved average `Ã` in its two function arguments, in the form of sums
  (`AhalfR_sum_sum`);
* the `ℕ`-indexed telescoping of the continuous dyadic pieces
  (`sum_piece_zero_range`, `sum_Fpiece_range`, `sum_Gpiece_range`);
* the resulting single-scale decomposition of the major arc part
  (`majorArcPartR_eq_sum_varpPiece`): the major arc part of the halved average at scale `N` is the
  quadruple sum of the pieces `varpPiece Pj P d N f g l₁ l₂ k₁ k₂`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Analysis.EndVar

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.Paraproduct (IWProjections)

/-! ## Bilinearity of the halved average -/

lemma AhalfR_add_left' (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f₁ f₂ g : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ (f₁ + f₂) g = AhalfR TZ N P₁ P₂ f₁ g + AhalfR TZ N P₁ P₂ f₂ g := by
  funext x
  simp only [AhalfR, Ahalf, Ablock, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

lemma AhalfR_add_right' (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f g₁ g₂ : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ f (g₁ + g₂) = AhalfR TZ N P₁ P₂ f g₁ + AhalfR TZ N P₁ P₂ f g₂ := by
  funext x
  simp only [AhalfR, Ahalf, Ablock, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma AhalfR_coe_nat_floor' (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f g : ℤ → ℂ) :
    AhalfR TZ (Nat.floor N : ℝ≥0) P₁ P₂ f g = AhalfR TZ N P₁ P₂ f g := by
  funext x
  rw [AhalfR_eq, AhalfR_eq, Nat.floor_natCast]

lemma AhalfR_zero_left (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (g : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ (0 : ℤ → ℂ) g = 0 := by
  funext x
  simp only [AhalfR, Ahalf, Ablock, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero]

lemma AhalfR_zero_right (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ f (0 : ℤ → ℂ) = 0 := by
  funext x
  simp only [AhalfR, Ahalf, Ablock, Pi.zero_apply, mul_zero, Finset.sum_const_zero, mul_zero]

/-- Bilinearity of `Ã` against a finite sum in the first argument. -/
lemma AhalfR_sum_left {ι : Type*} (s : Finset ι) (N : ℝ≥0) (P₁ P₂ : ℤ[X])
    (F : ι → ℤ → ℂ) (g : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ (∑ i ∈ s, F i) g
      = ∑ i ∈ s, AhalfR TZ N P₁ P₂ (F i) g := by
  classical
  induction s using Finset.induction with
  | empty => simp [AhalfR_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AhalfR_add_left', ih]

/-- Bilinearity of `Ã` against a finite sum in the second argument. -/
lemma AhalfR_sum_right {ι : Type*} (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (f : ℤ → ℂ)
    (s : Finset ι) (G : ι → ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ f (∑ i ∈ s, G i)
      = ∑ i ∈ s, AhalfR TZ N P₁ P₂ f (G i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [AhalfR_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, AhalfR_add_right', ih]

/-- Bilinearity of `Ã` against finite sums in both arguments. -/
lemma AhalfR_sum_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (N : ℝ≥0) (P₁ P₂ : ℤ[X])
    (F : ι → ℤ → ℂ) (G : κ → ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ (∑ i ∈ s, F i) (∑ j ∈ t, G j)
      = ∑ i ∈ s, ∑ j ∈ t, AhalfR TZ N P₁ P₂ (F i) (G j) := by
  rw [AhalfR_sum_left]
  exact Finset.sum_congr rfl (fun i _ => AhalfR_sum_right N P₁ P₂ (F i) t G)

/-! ## The `ℕ`-indexed telescoping of the continuous pieces -/

/-- **Telescoping of the continuous pieces with bottom scale `0`**, indexed by `ℕ`: the sum of the
pieces `piece Pj l κ 0 s f` for `0 ≤ s ≤ M` is `Π_{l,≤κ M} f`. -/
lemma sum_piece_zero_range (Pj : IWProjections) (l : ℕ) (κ : ℤ → ℤ) (M N : ℕ) (f : ℤ → ℂ) :
    ∑ s ∈ Finset.range (M + 1), piece Pj l κ 0 (s : ℤ) f = piExact Pj l (κ (M : ℤ)) f := by
  induction M with
  | zero => simp [piece_self]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih,
        piece_of_ne (Pj := Pj) (κ := κ) (a := 0) (s := ((M + 1 : ℕ) : ℤ)) (f := f)
          (by omega : (((M + 1 : ℕ) : ℤ)) ≠ 0)]
      have hcast : (((M + 1 : ℕ) : ℤ) - 1) = (M : ℤ) := by push_cast; ring
      rw [hcast]
      abel

/-- The `F`-pieces telescope to `Π_{l,≤-Log N+M}`. -/
lemma sum_Fpiece_range (Pj : IWProjections) (l M N : ℕ) (f : ℤ → ℂ) :
    ∑ s ∈ Finset.range (M + 1), Fpiece Pj 0 l (s : ℤ) N f
      = piExact Pj l (-(logN N) + (M : ℤ)) f := by
  have h := sum_piece_zero_range Pj l (fun s => -(logN N) + s) M N f
  simpa only [Fpiece, Nat.cast_zero, neg_zero] using h

/-- The `G`-pieces telescope to `Π_{l,≤d(-Log N+M)}`. -/
lemma sum_Gpiece_range (Pj : IWProjections) (d : ℤ) (l M N : ℕ) (g : ℤ → ℂ) :
    ∑ s ∈ Finset.range (M + 1), Gpiece Pj d 0 l (s : ℤ) N g
      = piExact Pj l (d * (-(logN N) + (M : ℤ))) g := by
  have h := sum_piece_zero_range Pj l (fun s => d * (-(logN N) + s)) M N g
  simpa only [Gpiece, Nat.cast_zero, neg_zero] using h

/-! ## The single-scale decomposition -/

/-- **The §5 decomposition of the major arc part.**  The major arc part of the halved average at
scale `N` is the quadruple sum of the pieces `varpPiece`, the continuous frequencies `k₁, k₂`
running over `0, …, l_{(N)}` (bottom scale `u = 0`). -/
theorem majorArcPartR_eq_sum_varpPiece (Pj : IWProjections) (P : ℤ[X]) (d C₀ : ℕ)
    (N : ℝ≥0) (f g : ℤ → ℂ) :
    majorArcPartR Pj P d C₀ N f g
      = fun x => ∑ l₁ ∈ Finset.range (heightScale C₀ (Nat.floor N) + 1),
          ∑ l₂ ∈ Finset.range (heightScale C₀ (Nat.floor N) + 1),
          ∑ k₁ ∈ Finset.range (heightScale C₀ (Nat.floor N) + 1),
          ∑ k₂ ∈ Finset.range (heightScale C₀ (Nat.floor N) + 1),
            varpPiece Pj P d N f g l₁ l₂ k₁ k₂ x := by
  set L : ℕ := heightScale C₀ (Nat.floor N) with hL
  have hproj₁ :
      Pj.proj L (-(logN (Nat.floor N)) + (L : ℤ)) f
        = ∑ l₁ ∈ Finset.range (L + 1), ∑ k₁ ∈ Finset.range (L + 1),
            Fpiece Pj 0 l₁ (k₁ : ℤ) (Nat.floor N) f := by
    rw [piLe_eq_sum_piExact]
    exact Finset.sum_congr rfl (fun l₁ _ => (sum_Fpiece_range Pj l₁ L (Nat.floor N) f).symm)
  have hproj₂ :
      Pj.proj L (-((d : ℤ) * logN (Nat.floor N)) + (d : ℤ) * (L : ℤ)) g
        = ∑ l₂ ∈ Finset.range (L + 1), ∑ k₂ ∈ Finset.range (L + 1),
            Gpiece Pj (d : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor N) g := by
    rw [piLe_eq_sum_piExact]
    refine Finset.sum_congr rfl (fun l₂ _ => ?_)
    have hk : (d : ℤ) * (-(logN (Nat.floor N)) + (L : ℤ))
        = -((d : ℤ) * logN (Nat.floor N)) + (d : ℤ) * (L : ℤ) := by ring
    rw [← hk]
    exact (sum_Gpiece_range Pj (d : ℤ) l₂ L (Nat.floor N) g).symm
  have hstart : majorArcPartR Pj P d C₀ N f g
      = AhalfR TZ N X P
          (Pj.proj L (-(logN (Nat.floor N)) + (L : ℤ)) f)
          (Pj.proj L (-((d : ℤ) * logN (Nat.floor N)) + (d : ℤ) * (L : ℤ)) g) := by
    rw [majorArcPartR, majorArcPart, AhalfR_coe_nat_floor']
  rw [hstart, hproj₁, hproj₂, AhalfR_sum_sum]
  funext x
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl (fun l₁ _ => ?_)
  refine Finset.sum_congr rfl (fun l₂ _ => ?_)
  rw [AhalfR_sum_sum]
  simp only [Finset.sum_apply, varpPiece]

end

end Work.Analysis.EndVar
