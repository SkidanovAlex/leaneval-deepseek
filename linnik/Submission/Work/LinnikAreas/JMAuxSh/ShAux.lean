
import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.LinnikAreas.JMAux.CellLayerKsum
import Submission.Work.LinnikAreas.JMAux.CellMultLeBoundJM
import Submission.Work.LinnikAreas.JMAux.MsumExpLe

/-!
# The weakened middle branch of the far-zero assembly

`Work.LinnikAreas.cellBoundJMsh` differs from `Work.LinnikAreas.cellBoundJM` only in the middle
branch `L/5 < (m+1) ≤ 5L/12`, where the density coefficient `2.451` is replaced by `2.551`.
This file re-proves the three auxiliary estimates that mention the coefficient: the geometric
`m`-sum (`≤ 400·q^{-23/50}`, uniform in `L`), the branch-2 double sum
(`≤ 30000·CM/(R^{9/10}·q^{23/50})`), and the per-cell comparison against `cellBoundJMsh`.
-/

namespace Work.LinnikAreas.JMAuxSh

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- **Family count of a finite set of zero-pairs**, from a family density hypothesis available
only on the range `σlo ≤ σ ≤ σhi` (a copy of `JMAux.finset_sum_le_fam_ge` with a two-sided
range, needed because the mesh hypothesis `FamilyZeroDensityMesh` is only available on
`[7/12, 4/5]`). -/
lemma finsetSumLeFamLe {q : ℕ} [NeZero q] (C A σlo σhi : ℝ)
    (hfam : ∀ σ T : ℝ, σlo ≤ σ → σ ≤ σhi → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T
        ≤ C * ((q:ℝ) * T) ^ (A * (1 - σ)))
    (hσlo0 : 0 ≤ σlo) (hσhi1 : σhi ≤ 1)
    {σ T : ℝ} (hσlo : σlo ≤ σ) (hσhi : σ ≤ σhi) (hT : 1 ≤ T)
    {S : Finset (DirichletCharacter ℂ q × ℂ)}
    (h1 : ∀ z ∈ S, z.1 ≠ 1) (hre : ∀ z ∈ S, σ ≤ z.2.re) (him : ∀ z ∈ S, |z.2.im| ≤ T) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)) ≤ C * ((q:ℝ) * T) ^ (A * (1 - σ)) := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.univ) (g := fun z : DirichletCharacter ℂ q × ℂ => z.1)
    (f := fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)) (fun z _ => Finset.mem_univ _)
  rw [← hfib]
  refine le_trans (Finset.sum_le_sum (fun χ _ => ?_)) (hfam σ T hσlo hσhi hT)
  by_cases hχ : χ = 1
  · have hempty : S.filter (fun z => z.1 = χ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro z hz hc
      exact h1 z hz (by rw [hc, hχ])
    rw [hempty, Finset.sum_empty]
    exact Work.LinnikAreas.zeroCountIn_nonneg χ σ T
  · refine Work.LinnikAreas.fiber_sum_le_zeroCountIn χ hχ ?_ ?_ _ ?_ ?_ ?_
    · linarith
    · linarith
    · exact fun z hz => (Finset.mem_filter.mp hz).2
    · exact fun z hz => hre z (Finset.mem_filter.mp hz).1
    · exact fun z hz => him z (Finset.mem_filter.mp hz).1

/-- **Family count of a finite set of non-principal zero-pairs, from a family density hypothesis
stated for the *non-principal* characters only.**  This is the version of `finsetSumLeFamLe` that
the far-zero argument consumes: the fibre decomposition runs over `Finset.univ.erase 1`, and since
every pair of `S` is non-principal the `χ = 1` fibre is empty — so no term is lost and the
`χ = 1` case of the all-character version disappears. -/
lemma finsetSumLeFamGeNP {q : ℕ} [NeZero q] (C A σlo σhi : ℝ)
    (hfam : ∀ σ T : ℝ, σlo ≤ σ → σ ≤ σhi → 1 ≤ T →
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          Work.LinnikAreas.zeroCountIn χ σ T
        ≤ C * ((q:ℝ) * T) ^ (A * (1 - σ)))
    (hσlo0 : 0 ≤ σlo) (hσhi1 : σhi ≤ 1)
    {σ T : ℝ} (hσlo : σlo ≤ σ) (hσhi : σ ≤ σhi) (hT : 1 ≤ T)
    {S : Finset (DirichletCharacter ℂ q × ℂ)}
    (h1 : ∀ z ∈ S, z.1 ≠ 1) (hre : ∀ z ∈ S, σ ≤ z.2.re) (him : ∀ z ∈ S, |z.2.im| ≤ T) :
    (∑ z ∈ S, (Work.LinnikContract.zeroMult z.1 z.2 : ℝ)) ≤ C * ((q:ℝ) * T) ^ (A * (1 - σ)) := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.univ.erase (1 : DirichletCharacter ℂ q))
    (g := fun z : DirichletCharacter ℂ q × ℂ => z.1)
    (f := fun z => (Work.LinnikContract.zeroMult z.1 z.2 : ℝ))
    (fun z hz => Finset.mem_erase.mpr ⟨h1 z hz, Finset.mem_univ _⟩)
  rw [← hfib]
  refine le_trans (Finset.sum_le_sum (fun χ hχ => ?_)) (hfam σ T hσlo hσhi hT)
  have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
  refine Work.LinnikAreas.fiber_sum_le_zeroCountIn χ hχ1 ?_ ?_ _ ?_ ?_ ?_
  · linarith
  · linarith
  · exact fun z hz => (Finset.mem_filter.mp hz).2
  · exact fun z hz => hre z (Finset.mem_filter.mp hz).1
  · exact fun z hz => him z (Finset.mem_filter.mp hz).1

/-- The `m`-sum of branch 2 with the coefficient `2551/1000`. -/
lemma msumExpLeSh (q : ℕ) (hq : 2 ≤ q) {L : ℝ} (hLp : 0 < L)
    (hLdef : L = Real.log (q:ℝ)) {s : Finset ℕ} (hs1 : ∀ m ∈ s, L/5 < (m:ℝ)+1) :
    (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * (q:ℝ) ^ ((2551/1000) * (((m:ℝ)+1)/L)))
      ≤ 400 * (q:ℝ)^(-(23/50:ℝ)) := by
  have hqpos : (0:ℝ) < (q:ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hterm : ∀ m : ℕ, Real.exp (-(49/10) * (m:ℝ)) *
        (q:ℝ) ^ ((2551/1000) * (((m:ℝ)+1)/L))
      = Real.exp (2551/1000) * (Real.exp (-(2349/1000)))^m := by
    intro m
    have key : (q:ℝ) ^ ((2551/1000) * (((m:ℝ)+1)/L))
        = Real.exp ((2551/1000)*((m:ℝ)+1)) := by
      rw [Real.rpow_def_of_pos hqpos]
      congr 1
      rw [← hLdef]
      field_simp
    rw [key, ← Real.exp_add]
    rw [show -(49/10) * (m:ℝ) + (2551/1000)*((m:ℝ)+1)
        = (2551/1000) + (m:ℝ)*(-(2349/1000)) by ring]
    rw [Real.exp_add, Real.exp_nat_mul]
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  rw [← Finset.mul_sum]
  have hr0 : 0 ≤ Real.exp (-(2349/1000)) := le_of_lt (Real.exp_pos _)
  have hr1 : Real.exp (-(2349/1000)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num)
  have hr14 : Real.exp (-(2349/1000)) ≤ 1/4 := by
    have hexp : (4:ℝ) ≤ Real.exp (2349/1000) := by
      have h4 : (4:ℝ) < Real.exp 2 := by
        have h : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        rw [h]; nlinarith [Real.exp_one_gt_two, Real.exp_pos 1]
      exact le_of_lt (lt_of_lt_of_le h4 (Real.exp_le_exp.mpr (by norm_num)))
    have h4inv : ((4:ℝ))⁻¹ = 1/4 := by norm_num
    rw [Real.exp_neg, ← h4inv]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 4)).mpr hexp
  have hrpos : (0:ℝ) < 1 - Real.exp (-(2349/1000)) := by linarith
  have hr_inv_le : (1 - Real.exp (-(2349/1000)))⁻¹ ≤ 4/3 := by
    have h34 : (3/4:ℝ) ≤ 1 - Real.exp (-(2349/1000)) := by linarith
    have h := (inv_le_inv₀ hrpos (by norm_num : (0:ℝ) < 3/4)).mpr h34
    have : ((3/4:ℝ))⁻¹ = 4/3 := by norm_num
    linarith [h, this]
  have h49 : Real.exp (49/10) ≤ 243 := by
    have h1 : Real.exp (49/10) ≤ Real.exp 5 := Real.exp_le_exp.mpr (by norm_num)
    have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2] at h1
    have h3 : Real.exp 1 ^ 5 < 3 ^ 5 :=
      pow_lt_pow_left₀ Real.exp_one_lt_three (le_of_lt (Real.exp_pos 1)) (by norm_num)
    have h4 : (3:ℝ)^5 = 243 := by norm_num
    linarith [h1, h3, h4, Real.exp_pos (49/10)]
  have htle : ∀ m ∈ s, Nat.ceil (L/5 - 1) ≤ m := by
    intro m hm
    apply Nat.ceil_le.mpr
    have h := hs1 m hm
    linarith
  have htce : (L/5 - 1 : ℝ) ≤ (Nat.ceil (L/5 - 1) : ℝ) := Nat.le_ceil _
  have hbound1 : Real.exp (2551/1000) * (Real.exp (-(2349/1000)))^(Nat.ceil (L/5-1))
      ≤ Real.exp (49/10 - 2349*L/5000) := by
    rw [← Real.exp_nat_mul (x := (-(2349/1000))) (n := Nat.ceil (L/5-1)), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [htce, hLp]
  have hbound2 : Real.exp (49/10 - 2349*L/5000) ≤ 243 * Real.exp (-(23/50)*L) := by
    calc Real.exp (49/10 - 2349*L/5000)
        = Real.exp (49/10) * Real.exp (-(2349*L/5000)) := by
            rw [show 49/10 - 2349*L/5000 = 49/10 + (-(2349*L/5000)) by ring, Real.exp_add]
      _ ≤ 243 * Real.exp (-(2349*L/5000)) :=
            mul_le_mul_of_nonneg_right h49 (le_of_lt (Real.exp_pos _))
      _ ≤ 243 * Real.exp (-(23/50)*L) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply Real.exp_le_exp.mpr
            nlinarith [hLp]
  have hmain : Real.exp (2551/1000) * (∑ m ∈ s, (Real.exp (-(2349/1000)))^m)
      ≤ 400 * Real.exp (-(23/50)*L) := by
    have hsumb : ∑ m ∈ s, (Real.exp (-(2349/1000)))^m
        ≤ (Real.exp (-(2349/1000)))^(Nat.ceil (L/5-1)) * (1 - Real.exp (-(2349/1000)))⁻¹ :=
      Work.LinnikAreas.JMAux.geom_finset_shift_le hr0 hr1 htle
    have hA0 : (0:ℝ) ≤ Real.exp (2551/1000) := le_of_lt (Real.exp_pos _)
    have hinv0 : (0:ℝ) ≤ (1 - Real.exp (-(2349/1000)))⁻¹ := le_of_lt (inv_pos.mpr hrpos)
    have he0 : (0:ℝ) ≤ Real.exp (-(23/50)*L) := le_of_lt (Real.exp_pos _)
    calc Real.exp (2551/1000) * (∑ m ∈ s, (Real.exp (-(2349/1000)))^m)
        ≤ Real.exp (2551/1000) * ((Real.exp (-(2349/1000)))^(Nat.ceil (L/5-1))
            * (1 - Real.exp (-(2349/1000)))⁻¹) := mul_le_mul_of_nonneg_left hsumb hA0
      _ = (Real.exp (2551/1000) * (Real.exp (-(2349/1000)))^(Nat.ceil (L/5-1)))
            * (1 - Real.exp (-(2349/1000)))⁻¹ := by ring
      _ ≤ Real.exp (49/10 - 2349*L/5000) * (1 - Real.exp (-(2349/1000)))⁻¹ :=
            mul_le_mul_of_nonneg_right hbound1 hinv0
      _ ≤ Real.exp (49/10 - 2349*L/5000) * (4/3) :=
            mul_le_mul_of_nonneg_left hr_inv_le (le_of_lt (Real.exp_pos _))
      _ = (4/3) * Real.exp (49/10 - 2349*L/5000) := by ring
      _ ≤ (4/3) * (243 * Real.exp (-(23/50)*L)) :=
            mul_le_mul_of_nonneg_left hbound2 (by norm_num)
      _ ≤ 400 * Real.exp (-(23/50)*L) := by
            have h400 : (4/3 : ℝ) * 243 ≤ 400 := by norm_num
            nlinarith [he0]
  have hqpow : (q:ℝ)^(-(23/50:ℝ)) = Real.exp (-(23/50)*L) := by
    rw [Real.rpow_def_of_pos hqpos, hLdef]
    congr 1
    ring
  rw [hqpow]
  exact hmain

/-- **Branch 2** of the `m`-sum, with the coefficient `2551/1000`. -/
lemma MsumBranch2sh (q : ℕ) (hq2 : 2 ≤ q) {L : ℝ} (hLp : 0 < L)
    (hLdef : L = Real.log (q:ℝ)) (R : ℕ) (hR1 : 1 ≤ R) {CM : ℝ} (hCM : 0 < CM)
    (Mmax N : ℕ) {s : Finset ℕ} (hs1 : ∀ m ∈ s, L/5 < (m:ℝ)+1)
    (hs2 : ∀ m ∈ s, (m:ℝ)+1 ≤ (5/12)*L) :
    (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * (CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2551/1000) * (((m:ℝ) + 1)/L))))
      ≤ 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ)) := by
  classical
  have hq0 : (0:ℝ) ≤ (q:ℝ) := by positivity
  have hR0 : (0:ℝ) < (R:ℝ) := by positivity
  have hθm : ∀ m ∈ s, (2551/1000) * (((m:ℝ) + 1)/L) ≤ 11/10 := by
    intro m hm
    have h1 : ((m:ℝ)+1)/L ≤ 5/12 := by rw [div_le_iff₀ hLp]; linarith [hs2 m hm]
    calc (2551/1000) * (((m:ℝ)+1)/L) ≤ (2551/1000) * (5/12) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ ≤ 11/10 := by norm_num
  have hstep1 : ∀ m ∈ s, (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
        * (CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2551/1000) * (((m:ℝ) + 1)/L))))
      ≤ CM * (4 * (q:ℝ) ^ ((2551/1000) * (((m:ℝ) + 1)/L)) * (R:ℝ)^(-(9/10:ℝ))) := by
    intro m hm
    have hA := Work.LinnikAreas.JMAux.CellLayerKsum q R N m hR1 (Nat.zero_le q) (hθm m hm)
    have heq : (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
          * (CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2551/1000) * (((m:ℝ) + 1)/L))))
        = CM * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * ((q:ℝ) * (2:ℝ)^k) ^ ((2551/1000) * (((m:ℝ) + 1)/L)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [heq]
    exact mul_le_mul_of_nonneg_left hA (le_of_lt hCM)
  have hstep2 : (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * (∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * (CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2551/1000) * (((m:ℝ) + 1)/L)))))
      ≤ ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
          * (CM * (4 * (q:ℝ) ^ ((2551/1000) * (((m:ℝ) + 1)/L)) * (R:ℝ)^(-(9/10:ℝ)))) :=
    Finset.sum_le_sum (fun m hm => mul_le_mul_of_nonneg_left (hstep1 m hm) (Real.exp_nonneg _))
  have hsplit : (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * (CM * (4 * (q:ℝ) ^ ((2551/1000) * (((m:ℝ) + 1)/L)) * (R:ℝ)^(-(9/10:ℝ)))))
      = 4 * CM * (R:ℝ)^(-(9/10:ℝ))
        * (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * (q:ℝ)^((2551/1000) * (((m:ℝ)+1)/L))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have hstep3 := msumExpLeSh q hq2 hLp hLdef hs1
  have hnonneg : (0:ℝ) ≤ 4 * CM * (R:ℝ)^(-(9/10:ℝ)) := by positivity
  have hfin : 1600 * CM * (R:ℝ)^(-(9/10:ℝ)) * (q:ℝ)^(-(23/50:ℝ))
      ≤ 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ)) := by
    have hY : (0:ℝ) ≤ CM * ((R:ℝ)^(9/10:ℝ))⁻¹ * ((q:ℝ)^(23/50:ℝ))⁻¹ := by positivity
    have e1 : (R:ℝ)^(-(9/10:ℝ)) = ((R:ℝ)^(9/10:ℝ))⁻¹ := Real.rpow_neg hR0.le (9/10)
    have e2 : (q:ℝ)^(-(23/50:ℝ)) = ((q:ℝ)^(23/50:ℝ))⁻¹ := Real.rpow_neg hq0 (23/50)
    have e3 : 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ))
        = 30000 * (CM * ((R:ℝ)^(9/10:ℝ))⁻¹ * ((q:ℝ)^(23/50:ℝ))⁻¹) := by
      rw [div_eq_mul_inv, mul_inv]; ring
    rw [e1, e2, e3]
    calc 1600 * CM * ((R:ℝ)^(9/10:ℝ))⁻¹ * ((q:ℝ)^(23/50:ℝ))⁻¹
        = 1600 * (CM * ((R:ℝ)^(9/10:ℝ))⁻¹ * ((q:ℝ)^(23/50:ℝ))⁻¹) := by ring
      _ ≤ 30000 * (CM * ((R:ℝ)^(9/10:ℝ))⁻¹ * ((q:ℝ)^(23/50:ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_right (by norm_num) hY
  calc (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range N, (1/4:ℝ)^k * Work.LinnikAreas.cellLayer R m k
            * (CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2551/1000) * (((m:ℝ) + 1)/L))))
      ≤ ∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ))
          * (CM * (4 * (q:ℝ) ^ ((2551/1000) * (((m:ℝ) + 1)/L)) * (R:ℝ)^(-(9/10:ℝ)))) := hstep2
    _ = 4 * CM * (R:ℝ)^(-(9/10:ℝ))
        * (∑ m ∈ s, Real.exp (-(49/10) * (m:ℝ)) * (q:ℝ)^((2551/1000) * (((m:ℝ)+1)/L))) := hsplit
    _ ≤ 4 * CM * (R:ℝ)^(-(9/10:ℝ)) * (400 * (q:ℝ)^(-(23/50:ℝ))) :=
        mul_le_mul_of_nonneg_left hstep3 hnonneg
    _ = 1600 * CM * (R:ℝ)^(-(9/10:ℝ)) * (q:ℝ)^(-(23/50:ℝ)) := by ring
    _ ≤ 30000 * CM / ((R:ℝ)^(9/10:ℝ) * (q:ℝ)^(23/50:ℝ)) := hfin

/-- **The per-cell comparison against `cellBoundJMsh`.** -/
lemma CellMultLeBoundJMsh {q : ℕ} [NeZero q] (hq : 2 ≤ q) {L : ℝ} (hLp : 0 < L) (hL1 : 1 ≤ L)
    {CJ CM c0 : ℝ} (hCJ : 0 < CJ) (hCM : 0 < CM) (hc0 : 0 < c0)
    (hfamJ : ∀ σ T : ℝ, (4:ℝ)/5 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          Work.LinnikAreas.zeroCountIn χ σ T
        ≤ CJ * ((q:ℝ) * T) ^ ((2 + 1/1000) * (1 - σ)))
    (hfams : ∀ σ T : ℝ, (1:ℝ) - 1021/5000 ≤ σ → σ ≤ (4:ℝ)/5 → 1 ≤ T →
      ∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T
        ≤ CM * ((q:ℝ) * T) ^ ((2551/1000) * (1 - σ)))
    (hball : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ c0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N:ℝ) + 2))
    {S : Finset (DirichletCharacter ℂ q × ℂ)}
    (hS : ∀ z ∈ S, z.1 ≠ 1 ∧ Work.LinnikContract.zeroMult z.1 z.2 ≠ 0) (m k : ℕ) :
    Work.LinnikAreas.cellMult L S m k ≤ Work.LinnikAreas.cellBoundJMsh q CJ CM c0 L m k := by
  classical
  rw [Work.LinnikAreas.cellMult, Work.LinnikAreas.cellBoundJMsh]
  set σ : ℝ := 1 - ((m:ℝ)+1)/L with hσdef
  have hσ1 : σ ≤ 1 := by
    rw [hσdef]
    have h0 : (0:ℝ) ≤ ((m:ℝ)+1)/L := div_nonneg (by positivity) hLp.le
    linarith
  have hT1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  have hT0 : (0:ℝ) ≤ (2:ℝ)^k := pow_nonneg (by norm_num) k
  set S' : Finset (DirichletCharacter ℂ q × ℂ) :=
    S.filter (fun z => Work.LinnikAreas.farM L z = m ∧ Work.LinnikAreas.farY L z ≤ (2:ℝ)^k)
  have h1 : ∀ z ∈ S', z.1 ≠ 1 := fun z hz => (hS z (Finset.mem_filter.mp hz).1).1
  have hreS : ∀ z ∈ S', σ ≤ z.2.re := by
    intro z hz
    obtain ⟨hzS, hzm, hzy⟩ := Finset.mem_filter.mp hz
    have hmlt : (1 - z.2.re) * L < (m:ℝ) + 1 := by
      have hh : (1 - z.2.re) * L < ((Work.LinnikAreas.farM L z : ℕ) : ℝ) + 1 := by
        simp only [Work.LinnikAreas.farM]; exact Nat.lt_floor_add_one _
      rw [hzm] at hh; linarith
    have h2 : 1 - z.2.re < ((m:ℝ)+1)/L := by rw [lt_div_iff₀ hLp]; linarith
    rw [hσdef]; linarith
  have hre0 : ∀ z ∈ S', 0 ≤ z.2.re := by
    intro z hz
    exact le_of_lt (Work.LinnikAreas.zeroMult_re z.1 (hS z (Finset.mem_filter.mp hz).1).1
      (hS z (Finset.mem_filter.mp hz).1).2).1
  have himS : ∀ z ∈ S', |z.2.im| ≤ (2:ℝ)^k := by
    intro z hz
    obtain ⟨hzS, hzm, hzy⟩ := Finset.mem_filter.mp hz
    have hz' : Work.LinnikAreas.farY L z = |z.2.im| * L := rfl
    rw [hz'] at hzy
    have h3 : |z.2.im| ≤ (2:ℝ)^k / L := by rw [le_div_iff₀ hLp]; linarith
    have h4 : (2:ℝ)^k / L ≤ (2:ℝ)^k := by
      rw [div_le_iff₀ hLp]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) k]
    linarith
  have himS' : ∀ z ∈ S', |z.2.im| ≤ (2:ℝ)^k / L := by
    intro z hz
    obtain ⟨hzS, hzm, hzy⟩ := Finset.mem_filter.mp hz
    have hz' : Work.LinnikAreas.farY L z = |z.2.im| * L := rfl
    rw [hz'] at hzy
    rw [le_div_iff₀ hLp]; linarith
  by_cases hJ : ((m:ℝ)+1) ≤ L/5
  · rw [if_pos hJ]
    have hσ45 : (4:ℝ)/5 ≤ σ := by
      rw [hσdef]
      have h1' : ((m:ℝ)+1)/L ≤ 1/5 := by rw [div_le_iff₀ hLp]; linarith
      linarith
    have hmain := finsetSumLeFamGeNP (q := q) CJ (2+1/1000) (4/5) 1 hfamJ
      (by norm_num : (0:ℝ) ≤ 4/5) (by norm_num : (1:ℝ) ≤ 1) hσ45 hσ1 hT1 h1 hreS himS
    have heq : (2 + 1/1000 : ℝ) * (1 - σ) = (2 + 1/1000) * (((m:ℝ)+1)/L) := by
      rw [hσdef]; ring
    rw [heq] at hmain
    exact hmain
  · rw [if_neg hJ]
    by_cases hM : ((m:ℝ)+1) ≤ (1021/5000)*L
    · rw [if_pos hM]
      have hσ0 : (1:ℝ) - 1021/5000 ≤ σ := by
        rw [hσdef]
        have h1' : ((m:ℝ)+1)/L ≤ 1021/5000 := by rw [div_le_iff₀ hLp]; linarith
        linarith
      have hσ45 : σ ≤ (4:ℝ)/5 := by
        rw [hσdef]
        have h1' : (1:ℝ)/5 ≤ ((m:ℝ)+1)/L := by
          rw [le_div_iff₀ hLp]
          have := lt_of_not_ge hJ
          linarith
        linarith
      have hmain := finsetSumLeFamLe (q := q) CM (2551/1000) (1 - 1021/5000) (4/5) hfams
        (by norm_num : (0:ℝ) ≤ 1 - 1021/5000) (by norm_num : (4:ℝ)/5 ≤ 1) hσ0 hσ45 hT1 h1 hreS himS
      have heq : (2551/1000 : ℝ) * (1 - σ) = (2551/1000) * (((m:ℝ)+1)/L) := by
        rw [hσdef]; ring
      rw [heq] at hmain
      exact hmain
    · rw [if_neg hM]
      have hTs : (0:ℝ) ≤ (2:ℝ)^k / L := by positivity
      exact Work.LinnikAreas.finset_sum_le_trivial (q := q) hc0 hball (T := (2:ℝ)^k / L) hTs
        h1 hre0 himS'


end Work.LinnikAreas.JMAuxSh
