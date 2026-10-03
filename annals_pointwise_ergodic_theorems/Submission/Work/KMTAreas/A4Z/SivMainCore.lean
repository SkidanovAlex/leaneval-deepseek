/-
# The assembly of `siv-second` from `struct-iii-second` and the off-diagonal decay

Krause--Mirek--Tao, §5.2, Corollary `siv-second`.  This module contains the *assembly*: given
Corollary `struct-iii-second` (the local `ℓ²` bound for the pieces), the almost-orthogonality
`PairingFarBd` of the minor-arc parts of two blocks, the linearity of the operator
`T = (1-Π)Ã_N^{**}(·,h)` over block sums, and the fact that the `ℓ²`-norm of the block remainder
tends to zero, it produces `SivSecondHyp`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.SivLocal

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.InverseTheory
open Work.Analysis.EndVar
open Work.KMTAreas.A5 (BoundedZ boundedZ_of_memLp)

namespace Work.KMTAreas.A4Z

/-- The threshold beyond which two blocks are "far apart" for the almost-orthogonality. -/
def thr (P : Polynomial ℤ) : ℤ := 2 * coeffSum P + 5 + 2 ^ (P.natDegree + 1)

theorem thr_nonneg (P : Polynomial ℤ) : 0 ≤ thr P := by
  rw [thr]
  have h1 : 0 ≤ coeffSum P := coeffSum_nonneg P
  have h2 : (0 : ℤ) ≤ 2 ^ (P.natDegree + 1) := by positivity
  linarith

theorem blockLen_pos (P : Polynomial ℤ) {N : ℕ} (hN : 1 ≤ N) : 0 < blockLen P N :=
  lt_of_lt_of_le zero_lt_one (one_le_blockLen P hN)

/-! ## The real-valued `ℓ²` calculus -/

theorem l2sq_neg' (g : ℤ → ℂ) : l2sq (-g) = l2sq g := by
  simp only [l2sq]
  refine tsum_congr fun x => ?_
  rw [Pi.neg_apply, norm_neg]

theorem l2norm_neg' (g : ℤ → ℂ) : l2norm (-g) = l2norm g := by
  simp only [l2norm, l2sq_neg']

theorem l2norm_add_le {g g' : ℤ → ℂ} (hg : MemLp g 2 Measure.count)
    (hg' : MemLp g' 2 Measure.count) :
    l2norm (g + g') ≤ l2norm g + l2norm g' := by
  have h1 : eLpNorm (g + g') 2 Measure.count = ENNReal.ofReal (l2norm (g + g')) :=
    eLpNorm_two_eq_ofReal_l2norm (Work.KMTAreas.A4.memLp_two_count_summable_norm_sq (hg.add hg'))
  have h2 : eLpNorm g 2 Measure.count = ENNReal.ofReal (l2norm g) :=
    eLpNorm_two_eq_ofReal_l2norm (Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hg)
  have h3 : eLpNorm g' 2 Measure.count = ENNReal.ofReal (l2norm g') :=
    eLpNorm_two_eq_ofReal_l2norm (Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hg')
  have h4 := MeasureTheory.eLpNorm_add_le (μ := Measure.count) (p := 2) (f := g) (g := g') (by norm_num)
  rw [h1, h2, h3, ← ENNReal.ofReal_add (l2norm_nonneg _) (l2norm_nonneg _)] at h4
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (l2norm_nonneg _) (l2norm_nonneg _))).mp h4

theorem l2norm_sub_le {g g' : ℤ → ℂ} (hg : MemLp g 2 Measure.count)
    (hg' : MemLp g' 2 Measure.count) :
    l2norm (g - g') ≤ l2norm g + l2norm g' := by
  have h := l2norm_add_le hg (hg'.neg)
  rw [l2norm_neg'] at h
  simpa only [sub_eq_add_neg] using h

theorem l2norm_mono {g g' : ℤ → ℂ} (h : ∀ x : ℤ, ‖g x‖ ≤ ‖g' x‖)
    (hg : Summable (fun x : ℤ => ‖g x‖ ^ 2)) (hg' : Summable (fun x : ℤ => ‖g' x‖ ^ 2)) :
    l2norm g ≤ l2norm g' := by
  have hle : l2sq g ≤ l2sq g' := hg.tsum_le_tsum (fun x => by
    have h0 : (0 : ℝ) ≤ ‖g x‖ := norm_nonneg _
    exact pow_le_pow_left₀ h0 (h x) 2) hg'
  simp only [l2norm]
  exact Real.sqrt_le_sqrt hle

theorem memLp_finset_sum (S : Finset ℤ) (u : ℤ → ℤ → ℂ)
    (hu : ∀ i ∈ S, MemLp (u i) 2 Measure.count) :
    MemLp (∑ i ∈ S, u i) 2 Measure.count := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (MemLp.zero : MemLp (0 : ℤ → ℂ) 2 Measure.count)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hu a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

/-- The sum of block pieces, as a function. -/
theorem blockSum_apply (L : ℤ) (f : ℤ → ℂ) (S : Finset ℤ) :
    (∑ i ∈ S, zPiece L f i) = fun x : ℤ => ∑ i ∈ S, zPiece L f i x := by
  funext x
  rw [Finset.sum_apply]

theorem memLp_blockSum {L : ℤ} {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) (S : Finset ℤ) :
    MemLp (fun x : ℤ => ∑ i ∈ S, zPiece L f i x) 2 Measure.count := by
  rw [← blockSum_apply L f S]
  exact memLp_finset_sum S (fun i x => zPiece L f i x) fun i _ => zPiece_memLp hf i

theorem memLp_blockRemainder {L : ℤ} {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count) (S : Finset ℤ) :
    MemLp (blockRemainder L f S) 2 Measure.count := by
  have h1 : blockRemainder L f S
      = fun x : ℤ => f x - ∑ i ∈ S, zPiece L f i x := rfl
  rw [h1]
  exact hf.sub (memLp_blockSum hf S)

theorem memLp_minorSum (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) {f h : ℤ → ℂ} (hN : 1 ≤ N)
    (hf : MemLp f 2 Measure.count) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (S : Finset ℤ) :
    MemLp (fun x : ℤ => ∑ i ∈ S, minorPart P ρ N l f h i x) 2 Measure.count := by
  have hbridge : (∑ i ∈ S, (fun x : ℤ => minorPart P ρ N l f h i x))
      = fun x : ℤ => ∑ i ∈ S, minorPart P ρ N l f h i x := by
    funext x
    rw [Finset.sum_apply]
  rw [← hbridge]
  exact memLp_finset_sum S (fun i x => minorPart P ρ N l f h i x)
    fun i _ => memLp_minorPart P ρ N l hN hf hh i

/-- **The operator `T` is bounded on `ℓ²`, in real-valued form.** -/
theorem l2norm_transOp_le (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) {h : ℤ → ℂ}
    (hN : 1 ≤ N) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ g : ℤ → ℂ, MemLp g 2 Measure.count →
      l2norm (transOp P ρ N l g h) ≤ M * l2norm g := by
  obtain ⟨Md, hMd, hMbd⟩ := eLpNorm_transOp_le P ρ N l hN hh
  refine ⟨Md.toReal, ENNReal.toReal_nonneg, fun g hg => ?_⟩
  have hle := hMbd g
  have hMeq : Md = ENNReal.ofReal Md.toReal := (ENNReal.ofReal_toReal hMd).symm
  rw [hMeq] at hle
  have hgN : eLpNorm g 2 Measure.count = ENNReal.ofReal (l2norm g) :=
    eLpNorm_two_eq_ofReal_l2norm (Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hg)
  rw [hgN] at hle
  have hle' : eLpNorm (transOp P ρ N l g h) 2 Measure.count
      ≤ ENNReal.ofReal (Md.toReal * l2norm g) := by
    rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at hle
    exact hle
  have hTmem : MemLp (transOp P ρ N l g h) 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hle' ENNReal.ofReal_lt_top)
  have hT : eLpNorm (transOp P ρ N l g h) 2 Measure.count
      = ENNReal.ofReal (l2norm (transOp P ρ N l g h)) :=
    eLpNorm_two_eq_ofReal_l2norm
      (Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hTmem)
  rw [hT] at hle'
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg ENNReal.toReal_nonneg (l2norm_nonneg _))).mp hle'

theorem memLp_transOp (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) {g h : ℤ → ℂ}
    (hN : 1 ≤ N) (hg : MemLp g 2 Measure.count) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) :
    MemLp (transOp P ρ N l g h) 2 Measure.count := by
  obtain ⟨Md, hMd, hMbd⟩ := eLpNorm_transOp_le P ρ N l hN hh
  refine MeasureTheory.memLp_iff.mpr ?_
  rw [lt_top_iff_ne_top]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hMd hg.eLpNorm_lt_top.ne) (hMbd g)

/-- The second dual function of an `ℓ²` function is bounded. -/
theorem boundedZ_ahalfTransposeTwo' (P : Polynomial ℤ) (N l : ℕ) {g h : ℤ → ℂ} (hN : 1 ≤ N)
    (hg : MemLp g 2 Measure.count) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) :
    BoundedZ (AhalfTranspose₂ N P g h) :=
  boundedZ_of_memLp (by norm_num : (1 : ℝ≥0∞) < 2)
    (memLp_ahalfTransposeTwo_of_bdd N P hN hg hh).1

/-! ## The Schur kernel and its mass -/

/-- The total mass of the Schur kernel `A^2 1_{|m| ≤ D} + (A^2 + Λ)(1+|m|)^{-8}` is at most
`A^2 (2D+1) + (A^2+Λ) kern8Mass`. -/
theorem kappa_tsum_le {A Λ : ℝ} {D : ℤ} (hA : 0 ≤ A) (hΛ : 0 ≤ Λ) (hD : 0 ≤ D) :
    (∑' m : ℤ, (A ^ 2 * (if |(((m : ℤ) : ℝ))| ≤ (D : ℝ) then (1 : ℝ) else 0)
        + (A ^ 2 + Λ) * (1 + |(((m : ℤ) : ℝ))|) ^ (-(8 : ℝ))))
      ≤ A ^ 2 * (2 * (D : ℝ) + 1) + (A ^ 2 + Λ) * kern8Mass := by
  have hmem : ∀ m : ℤ, |(((m : ℤ) : ℝ))| ≤ (D : ℝ) → -D ≤ m ∧ m ≤ D := by
    intro m hm
    have h := abs_le.mp hm
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have hsupp : ∀ m : ℤ, m ∉ Finset.Icc (-D) D →
      (if |(((m : ℤ) : ℝ))| ≤ (D : ℝ) then (1 : ℝ) else 0) = 0 := by
    intro m hm
    rw [if_neg]
    exact fun hcon => hm (Finset.mem_Icc.mpr (hmem m hcon))
  have hf1 : Summable (fun m : ℤ =>
      A ^ 2 * (if |(((m : ℤ) : ℝ))| ≤ (D : ℝ) then (1 : ℝ) else 0)) :=
    summable_of_ne_finset_zero (s := Finset.Icc (-D) D) fun m hm => by
      rw [hsupp m hm, mul_zero]
  have hf2 : Summable (fun m : ℤ => (A ^ 2 + Λ) * (1 + |(((m : ℤ) : ℝ))|) ^ (-(8 : ℝ))) :=
    summable_pow8.mul_left (A ^ 2 + Λ)
  rw [Summable.tsum_add hf1 hf2, tsum_mul_left, tsum_mul_left]
  have hind : (∑' m : ℤ, (if |(((m : ℤ) : ℝ))| ≤ (D : ℝ) then (1 : ℝ) else 0))
      = ∑ m ∈ Finset.Icc (-D) D, (1 : ℝ) := by
    rw [tsum_eq_sum (s := Finset.Icc (-D) D) hsupp]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [if_pos]
    have h := Finset.mem_Icc.mp hb
    rw [abs_le]
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have hcard : (∑ m ∈ Finset.Icc (-D) D, (1 : ℝ)) ≤ 2 * (D : ℝ) + 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Int.card_Icc]
    have h2D : (0 : ℤ) ≤ D + 1 - -D := by linarith
    have hnat : (((D + 1 - -D).toNat : ℤ)) ≤ 2 * D + 1 := by
      rw [Int.toNat_of_nonneg h2D]
      linarith
    exact_mod_cast hnat
  have hkern : (∑' m : ℤ, (1 + |(((m : ℤ) : ℝ))|) ^ (-(8 : ℝ))) = kern8Mass := rfl
  rw [hind, hkern]
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
  have h1 : A ^ 2 * (∑ m ∈ Finset.Icc (-D) D, (1 : ℝ)) ≤ A ^ 2 * (2 * (D : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hcard hA2
  linarith

/-! ## The Schur step for a finite union of blocks -/

/-- **The `ℓ²` bound for a finite sum of minor-arc pieces**, by Schur's test. -/
theorem l2norm_minorSum_le (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) {ρ c₀ Cρ_st : ℝ}
    {C : ℝ≥0} (hS : StructIiiSecondHyp P c₀ ρ Cρ_st C)
    {Cρ₀ K : ℝ} (hfar : PairingFarBd P ρ Cρ₀ K) (hK0 : 0 ≤ K)
    {N l : ℕ} (hN : 1 ≤ N)
    (hgood : GoodMajorArcs ρ (max Cρ_st Cρ₀) l ((P.natDegree : ℤ) * ((l : ℤ) - logN N)))
    {f h : ℤ → ℂ} (hf : MemLp f 2 Measure.count) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (S : Finset ℤ) :
    l2norm (fun x : ℤ => ∑ i ∈ S, minorPart P ρ N l f h i x)
      ≤ Real.sqrt (((C : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) ^ 2 * (2 * ((thr P : ℤ) : ℝ) + 1)
          + (((C : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) ^ 2
              + K * (max ((l : ℝ)) 1) ^ 2 * (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))))
            * kern8Mass) * l2norm f := by
  set A : ℝ := (C : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ))) with hAdef
  set Λ : ℝ := K * (max ((l : ℝ)) 1) ^ 2
    * (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))) with hΛdef
  set κ : ℤ → ℝ := fun m =>
    A ^ 2 * (if |(((m : ℤ) : ℝ))| ≤ ((thr P : ℤ) : ℝ) then 1 else 0)
      + (A ^ 2 + Λ) * (1 + |(((m : ℤ) : ℝ))|) ^ (-(8 : ℝ)) with hκdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (NNReal.coe_nonneg C) (Real.rpow_nonneg (by norm_num) _)
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛdef]
    refine mul_nonneg (mul_nonneg hK0 (pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _)) ?_
    exact Real.rpow_nonneg (by norm_num) _
  have hthr : 0 ≤ ((thr P : ℤ) : ℝ) := by exact_mod_cast thr_nonneg P
  have hκ0 : ∀ m, 0 ≤ κ m := by
    intro m
    have hsplit : (0 : ℝ) ≤ A ^ 2 * (if |(((m : ℤ) : ℝ))| ≤ ((thr P : ℤ) : ℝ) then 1 else 0) := by
      refine mul_nonneg (sq_nonneg A) ?_
      split_ifs with h
      · norm_num
      · norm_num
    rw [hκdef]
    exact add_nonneg hsplit (mul_nonneg (add_nonneg (sq_nonneg A) hΛ0)
      (Real.rpow_nonneg (by positivity) _))
  have hκsum : Summable κ := by
    rw [hκdef]
    refine Summable.add ?_ (summable_pow8.mul_left _)
    refine summable_of_ne_finset_zero (s := Finset.Icc (-(thr P)) (thr P)) fun m hm => ?_
    rw [if_neg, mul_zero]
    intro hcon
    have h := abs_le.mp hcon
    refine hm (Finset.mem_Icc.mpr ⟨?_, ?_⟩)
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  have hloc : ∀ i : ℤ, eLpNorm (minorPart P ρ N l f h i) 2 Measure.count
      ≤ ENNReal.ofReal (A * l2norm (zPiece (blockLen P N) f i)) := by
    intro i
    have h1 := localBoundAll P hP hS hN (GoodMajorArcs.mono hgood (le_max_left _ _)) hf hh i
    rw [hAdef]
    exact h1
  have hpair : ∀ i ∈ S, ∀ j ∈ S,
      ‖∑' x : ℤ, minorPart P ρ N l f h i x * star (minorPart P ρ N l f h j x)‖
        ≤ κ (i - j) * l2norm (zPiece (blockLen P N) f i)
          * l2norm (zPiece (blockLen P N) f j) := by
    intro i _ j _
    by_cases hcase : 2 * coeffSum P + 5 + 2 ^ (P.natDegree + 1) ≤ |i - j|
    · have hfar' := hfar N l (max Cρ_st Cρ₀) hN (le_max_right _ _) hgood f h i j A hf hh hA0
        hcase (hloc i) (hloc j)
      have hκge : (A ^ 2 + Λ) * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)) ≤ κ (i - j) := by
        have hk : κ (i - j) = (A ^ 2 * (if |(((i - j : ℤ) : ℝ))| ≤ ((thr P : ℤ) : ℝ) then 1 else 0)
            + (A ^ 2 + Λ) * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) := by
          simp only [hκdef]
        rw [hk]
        have hnn : 0 ≤ A ^ 2 * (if |(((i - j : ℤ) : ℝ))| ≤ ((thr P : ℤ) : ℝ) then 1 else 0) := by
          refine mul_nonneg (sq_nonneg A) ?_
          split_ifs <;> norm_num
        linarith
      calc ‖∑' x : ℤ, minorPart P ρ N l f h i x * star (minorPart P ρ N l f h j x)‖
          ≤ (A ^ 2 + K * (max ((l : ℝ)) 1) ^ 2
                * (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))))
            * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))
            * l2norm (zPiece (blockLen P N) f i) * l2norm (zPiece (blockLen P N) f j) := hfar'
        _ = ((A ^ 2 + Λ) * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)))
            * l2norm (zPiece (blockLen P N) f i) * l2norm (zPiece (blockLen P N) f j) := by
            rw [hΛdef]
        _ ≤ κ (i - j) * l2norm (zPiece (blockLen P N) f i) * l2norm (zPiece (blockLen P N) f j) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hκge (l2norm_nonneg _))
              (l2norm_nonneg _)
    · push_neg at hcase
      have hbase := enorm_pairing_le_mul (A := A * l2norm (zPiece (blockLen P N) f i))
        (A' := A * l2norm (zPiece (blockLen P N) f j))
        (mul_nonneg hA0 (l2norm_nonneg _)) (mul_nonneg hA0 (l2norm_nonneg _))
        (hloc i) (hloc j)
      have hif : |(((i - j : ℤ) : ℝ))| ≤ ((thr P : ℤ) : ℝ) := by
        rw [thr, ← Int.cast_abs]
        exact_mod_cast le_of_lt hcase
      have hκge : A ^ 2 ≤ κ (i - j) := by
        have hk : κ (i - j) = (A ^ 2 * (if |(((i - j : ℤ) : ℝ))| ≤ ((thr P : ℤ) : ℝ) then 1 else 0)
            + (A ^ 2 + Λ) * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ))) := by
          simp only [hκdef]
        rw [hk, if_pos hif]
        have h2 : 0 ≤ (A ^ 2 + Λ) * (1 + |(((i - j : ℤ) : ℝ))|) ^ (-(8 : ℝ)) :=
          mul_nonneg (add_nonneg (sq_nonneg A) hΛ0) (Real.rpow_nonneg (by positivity) _)
        nlinarith [sq_nonneg A]
      have hgoal : κ (i - j) * l2norm (zPiece (blockLen P N) f i)
            * l2norm (zPiece (blockLen P N) f j)
          = κ (i - j) * (l2norm (zPiece (blockLen P N) f i)
              * l2norm (zPiece (blockLen P N) f j)) := by ring
      rw [hgoal]
      refine hbase.trans ?_
      rw [show (A * l2norm (zPiece (blockLen P N) f i)) * (A * l2norm (zPiece (blockLen P N) f j))
          = A ^ 2 * (l2norm (zPiece (blockLen P N) f i) * l2norm (zPiece (blockLen P N) f j))
        from by ring]
      exact mul_le_mul_of_nonneg_right hκge (mul_nonneg (l2norm_nonneg _) (l2norm_nonneg _))
  have hSch := schur_finite S (fun i x => minorPart P ρ N l f h i x)
    (fun i => l2norm (zPiece (blockLen P N) f i)) κ
    (fun i => l2norm_nonneg _) hκ0 hκsum
    (fun i _ => summable_norm_sq_minorPart P ρ N l hN hf hh i) hpair
  have hsquares : (∑ i ∈ S, (l2norm (zPiece (blockLen P N) f i)) ^ 2) ≤ l2sq f := by
    rw [Finset.sum_congr rfl
      (fun i _ => (sq_l2norm (summable_norm_sq_zPiece (blockLen_pos P hN) f i)))]
    exact sum_l2sq_zPiece_le (blockLen_pos P hN)
      (Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hf) S
  have hκmass : (∑' m : ℤ, κ m)
      ≤ A ^ 2 * (2 * ((thr P : ℤ) : ℝ) + 1) + (A ^ 2 + Λ) * kern8Mass := by
    rw [hκdef]
    exact kappa_tsum_le hA0 hΛ0 (by exact_mod_cast thr_nonneg P)
  calc l2norm (fun x : ℤ => ∑ i ∈ S, minorPart P ρ N l f h i x)
      = Real.sqrt (l2sq (fun x : ℤ => ∑ i ∈ S, minorPart P ρ N l f h i x)) := rfl
    _ ≤ Real.sqrt ((∑' m : ℤ, κ m) * ∑ i ∈ S, (l2norm (zPiece (blockLen P N) f i)) ^ 2) :=
        Real.sqrt_le_sqrt hSch
    _ = Real.sqrt (∑' m : ℤ, κ m)
          * Real.sqrt (∑ i ∈ S, (l2norm (zPiece (blockLen P N) f i)) ^ 2) :=
        Real.sqrt_mul (tsum_nonneg hκ0) _
    _ ≤ Real.sqrt (∑' m : ℤ, κ m) * Real.sqrt (l2sq f) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsquares) (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑' m : ℤ, κ m) * l2norm f := by rw [l2norm]
    _ ≤ Real.sqrt (A ^ 2 * (2 * ((thr P : ℤ) : ℝ) + 1) + (A ^ 2 + Λ) * kern8Mass) * l2norm f :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hκmass) (l2norm_nonneg _)
    _ = Real.sqrt (((C : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) ^ 2 * (2 * ((thr P : ℤ) : ℝ) + 1)
          + (((C : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) ^ 2
              + K * (max ((l : ℝ)) 1) ^ 2 * (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))))
            * kern8Mass) * l2norm f := by
        rw [hAdef, hΛdef]


/-! ## The final assembly -/

/-- **`SivSecondHyp` from the local bound, the almost-orthogonality, the linearity over block sums
and the exhaustion.** -/
theorem sivSecondHyp_of_core (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) {ρ c₀ Cρ_st : ℝ}
    {C : ℝ≥0} (hS : StructIiiSecondHyp P c₀ ρ Cρ_st C) (hc₀ : 0 < c₀)
    {Cρ₀ K : ℝ} (hfar : PairingFarBd P ρ Cρ₀ K) (hK0 : 0 ≤ K)
    (hsum : ∀ (N l : ℕ) {f h : ℤ → ℂ}, 1 ≤ N → MemLp f 2 Measure.count →
      (∀ x : ℤ, ‖h x‖ ≤ 1) → ∀ S : Finset ℤ,
      transOp P ρ N l (fun x : ℤ => ∑ i ∈ S, zPiece (blockLen P N) f i x) h
        = fun x : ℤ => ∑ i ∈ S, minorPart P ρ N l f h i x)
    (htend : ∀ {L : ℤ}, 0 < L → ∀ {f : ℤ → ℂ}, MemLp f 2 Measure.count →
      Tendsto (fun S : Finset ℤ => l2norm (blockRemainder L f S)) atTop (𝓝 0))
    {C'' : ℝ} (hC'' : 0 < C'')
    (hsqrt : ∀ l : ℕ,
      Real.sqrt (((C : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) ^ 2 * (2 * ((thr P : ℤ) : ℝ) + 1)
          + (((C : ℝ) * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) ^ 2
              + K * (max ((l : ℝ)) 1) ^ 2 * (2 : ℝ) ^ (-(16 * (P.natDegree : ℝ) * (l : ℝ))))
            * kern8Mass)
        ≤ C'' * (2 : ℝ) ^ (-(min (c₀ / 2) 1 * (l : ℝ)))) :
    SivSecondHyp P (min (c₀ / 2) 1) ρ (max Cρ_st Cρ₀) ⟨C'', hC''.le⟩ := by
  intro N l f h₂ hN hf hh hgood
  have hfinite : ∀ S : Finset ℤ,
      l2norm (transOp P ρ N l (fun x : ℤ => ∑ i ∈ S, zPiece (blockLen P N) f i x) h₂)
        ≤ C'' * (2 : ℝ) ^ (-(min (c₀ / 2) 1 * (l : ℝ))) * l2norm f := by
    intro S
    rw [hsum N l hN hf hh S]
    exact (l2norm_minorSum_le P hP hS hfar hK0 hN hgood hf hh S).trans
      (mul_le_mul_of_nonneg_right (hsqrt l) (l2norm_nonneg _))
  have hsplit : ∀ S : Finset ℤ,
      f = (fun x : ℤ => ∑ i ∈ S, zPiece (blockLen P N) f i x)
        + blockRemainder (blockLen P N) f S := by
    intro S
    funext x
    simp only [Pi.add_apply, blockRemainder]
    ring
  have hbound : l2norm (transOp P ρ N l f h₂)
      ≤ C'' * (2 : ℝ) ^ (-(min (c₀ / 2) 1 * (l : ℝ))) * l2norm f := by
    obtain ⟨M, hM0, hMbd⟩ := l2norm_transOp_le P ρ N l hN hh
    have hconv : Tendsto (fun S : Finset ℤ =>
        M * l2norm (blockRemainder (blockLen P N) f S)
          + C'' * (2 : ℝ) ^ (-(min (c₀ / 2) 1 * (l : ℝ))) * l2norm f)
        atTop (𝓝 (C'' * (2 : ℝ) ^ (-(min (c₀ / 2) 1 * (l : ℝ))) * l2norm f)) := by
      have h1 : Tendsto (fun S : Finset ℤ => M * l2norm (blockRemainder (blockLen P N) f S))
          atTop (𝓝 (M * 0)) := tendsto_const_nhds.mul (htend (blockLen_pos P hN) hf)
      have h2 := h1.add (tendsto_const_nhds :
        Tendsto (fun _ : Finset ℤ => C'' * (2 : ℝ) ^ (-(min (c₀ / 2) 1 * (l : ℝ))) * l2norm f)
          atTop (𝓝 (C'' * (2 : ℝ) ^ (-(min (c₀ / 2) 1 * (l : ℝ))) * l2norm f)))
      simpa using h2
    refine ge_of_tendsto hconv ?_
    filter_upwards with S
    have hFS : MemLp (fun x : ℤ => ∑ i ∈ S, zPiece (blockLen P N) f i x) 2 Measure.count :=
      memLp_blockSum hf S
    have hrem : MemLp (blockRemainder (blockLen P N) f S) 2 Measure.count :=
      memLp_blockRemainder hf S
    have hadd : transOp P ρ N l f h₂
        = transOp P ρ N l (fun x : ℤ => ∑ i ∈ S, zPiece (blockLen P N) f i x) h₂
          + transOp P ρ N l (blockRemainder (blockLen P N) f S) h₂ := by
      have h := transOp_add_of_bdd (P := P) (ρ := ρ) (N := N) (l := l)
        (f := fun x : ℤ => ∑ i ∈ S, zPiece (blockLen P N) f i x)
        (g := blockRemainder (blockLen P N) f S) (h := h₂)
        (boundedZ_ahalfTransposeTwo' P N l hN hFS hh)
        (boundedZ_ahalfTransposeTwo' P N l hN hrem hh)
      rw [← hsplit S] at h
      exact h
    calc l2norm (transOp P ρ N l f h₂)
        = l2norm (transOp P ρ N l (fun x : ℤ => ∑ i ∈ S, zPiece (blockLen P N) f i x) h₂
            + transOp P ρ N l (blockRemainder (blockLen P N) f S) h₂) := by rw [hadd]
      _ ≤ l2norm (transOp P ρ N l (fun x : ℤ => ∑ i ∈ S, zPiece (blockLen P N) f i x) h₂)
            + l2norm (transOp P ρ N l (blockRemainder (blockLen P N) f S) h₂) :=
          l2norm_add_le (memLp_transOp P ρ N l hN hFS hh) (memLp_transOp P ρ N l hN hrem hh)
      _ ≤ C'' * (2 : ℝ) ^ (-(min (c₀ / 2) 1 * (l : ℝ))) * l2norm f
            + M * l2norm (blockRemainder (blockLen P N) f S) :=
          add_le_add (hfinite S) (hMbd _ hrem)
      _ = M * l2norm (blockRemainder (blockLen P N) f S)
            + C'' * (2 : ℝ) ^ (-(min (c₀ / 2) 1 * (l : ℝ))) * l2norm f := by ring
  have hTmem : MemLp (transOp P ρ N l f h₂) 2 Measure.count := memLp_transOp P ρ N l hN hf hh
  have hT : eLpNorm (fun x : ℤ => AhalfTranspose₂ N P f h₂ x
        - projTwo P ρ N l (AhalfTranspose₂ N P f h₂) x) 2 Measure.count
      = ENNReal.ofReal (l2norm (transOp P ρ N l f h₂)) := by
    rw [show (fun x : ℤ => AhalfTranspose₂ N P f h₂ x
        - projTwo P ρ N l (AhalfTranspose₂ N P f h₂) x) = transOp P ρ N l f h₂ from rfl]
    exact eLpNorm_two_eq_ofReal_l2norm
      (Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hTmem)
  have hF : eLpNorm f 2 Measure.count = ENNReal.ofReal (l2norm f) :=
    eLpNorm_two_eq_ofReal_l2norm (Work.KMTAreas.A4.memLp_two_count_summable_norm_sq hf)
  rw [hT, hF]
  rw [← ofReal_coe_mul_mul (C := ⟨C'', hC''.le⟩)
    (x := (2 : ℝ) ^ (-(min (c₀ / 2) 1 * (l : ℝ))))
    (y := l2norm f) (Real.rpow_nonneg (by norm_num) _)]
  refine (ENNReal.ofReal_le_ofReal_iff ?_).mpr hbound
  exact mul_nonneg (mul_nonneg hC''.le (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
    (l2norm_nonneg _)


/-- **`SivSecondClaim` from the children's lemmas** (the five inputs are stated as hypotheses, so
that this file can be checked independently of their proofs). -/
theorem sivSecondClaim_of_children (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree)
    (h : StructIiiSecondClaim P)
    (hsum : ∀ (ρ : ℝ) (N l : ℕ) {f h : ℤ → ℂ}, 1 ≤ N → MemLp f 2 Measure.count →
      (∀ x : ℤ, ‖h x‖ ≤ 1) → ∀ S : Finset ℤ,
      transOp P ρ N l (fun x : ℤ => ∑ i ∈ S, zPiece (blockLen P N) f i x) h
        = fun x : ℤ => ∑ i ∈ S, minorPart P ρ N l f h i x)
    (htend : ∀ {L : ℤ}, 0 < L → ∀ {f : ℤ → ℂ}, MemLp f 2 Measure.count →
      Tendsto (fun S : Finset ℤ => l2norm (blockRemainder L f S)) atTop (𝓝 0))
    (hBd : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ Cρ₀ : ℝ, 0 < Cρ₀ ∧ ∃ Koff : ℝ, 0 < Koff ∧
      OffBlockBd P ρ Cρ₀ Koff)
    (hPair : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ Cρ₀ Koff : ℝ, 0 ≤ Koff → OffBlockBd P ρ Cρ₀ Koff →
      ∃ K : ℝ, 0 < K ∧ PairingFarBd P ρ Cρ₀ K)
    (hSqrt : ∀ (K Cc : ℝ), 0 < K → 0 < Cc → (d : ℕ) → 2 ≤ d → (D : ℤ) → 0 ≤ D →
      ∀ (c₀ c : ℝ), 0 < c → 0 < c₀ → c ≤ c₀ → c ≤ 1 →
      ∃ C'' : ℝ, 0 < C'' ∧ ∀ l : ℕ,
        Real.sqrt ((Cc * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) ^ 2 * (2 * (D : ℝ) + 1)
            + ((Cc * (2 : ℝ) ^ (-(c₀ * (l : ℝ)))) ^ 2
                + K * (max ((l : ℝ)) 1) ^ 2 * (2 : ℝ) ^ (-(16 * (d : ℝ) * (l : ℝ))))
              * kern8Mass)
          ≤ C'' * (2 : ℝ) ^ (-(c * (l : ℝ)))) :
    SivSecondClaim P := by
  obtain ⟨c₀, hc₀, hρ⟩ := h
  refine ⟨min (c₀ / 2) 1, lt_min (by linarith) one_pos, fun ρ hρ0 hρ1 => ?_⟩
  obtain ⟨Cρ_st, hCρ_st, C, hC, hS⟩ := hρ ρ hρ0 hρ1
  obtain ⟨Cρ₀, hCρ₀, Koff, hKoff, hBd'⟩ := hBd ρ hρ0 hρ1
  obtain ⟨K, hK, hPF⟩ := hPair ρ hρ0 hρ1 Cρ₀ Koff hKoff.le hBd'
  obtain ⟨C'', hC'', hsq⟩ := hSqrt K (C : ℝ) hK (by positivity) P.natDegree hP (thr P)
    (thr_nonneg P) c₀ (min (c₀ / 2) 1) (lt_min (by linarith) one_pos) hc₀
    (le_trans (min_le_left _ _) (by linarith)) (min_le_right _ _)
  refine ⟨max Cρ_st Cρ₀, lt_of_lt_of_le hCρ_st (le_max_left _ _), ⟨C'', hC''.le⟩, ?_, ?_⟩
  · exact_mod_cast hC''
  · exact sivSecondHyp_of_core P hP hS hc₀ hPF hK.le
      (fun N l f h hN hf hh S => hsum ρ N l hN hf hh S) htend hC'' hsq

end Work.KMTAreas.A4Z
