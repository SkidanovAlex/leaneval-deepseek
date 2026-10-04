import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.GN.tools
import Submission.Work.Diff.STE.GN.holder2_int
import Submission.Work.Diff.STE.GN.integral_normMul_le_U_mul
import Submission.Work.Diff.STE.GN.holder_pd_order2
import Submission.Work.Diff.STE.GN.sum_rpow_le_of_each
import Submission.Work.Diff.STE.GN.rpow_le_of_le_mul_rpow
import Submission.Work.Diff.STE.GN.level2_secondDeriv_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.GN

open MeasureTheory BigOperators

/-- **The `k = 1` Nirenberg step, clean form.**

With the levels `gnLev m f k` of `Work.Diff.STE.GN.tools` and `‖f‖_∞ ≤ U`, the integration by parts
inequality `hibp` for the first derivatives gives

`(gnLev m f 1)^2 ≤ gnC m 1 * U * gnLev m f 2`.

Write `p := gnP m 1 = 2m` and, for the single tuple `l : Fin 1 → ι`, let `i := l 0` and
`A := ∫_{cube} ‖∂ᵢf‖^p`.  Then

* `hibp i` bounds `A` by `(p-1) ∫ ‖f‖ ‖∂ᵢf‖^{p-2} ‖∂ᵢ∂ᵢf‖`;
* pulling out `‖f‖ ≤ U` (`integral_normMul_le_U_mul`) and applying Hölder with the conjugate
  exponents `(p-2)/p` and `1/m` (`holder_pd_order2`) turns the second factor into
  `A^{(p-2)/p} · (∫ ‖∂ᵢ∂ᵢf‖^m)^{1/m}`, and the last factor is at most `gnLev m f 2`
  (`level2_secondDeriv_le`);
* so `A ≤ C · A^{(p-2)/p}` with `C := (p-1) U gnLev m f 2`, and `rpow_le_of_le_mul_rpow`
  gives `A^{2/p} ≤ C`;
* `sum_rpow_le_of_each` sums this over the `Fintype.card (Fin 1 → ι)` tuples, and
  `(gnLev m f 1)^2 = (∑_l A_l)^{2/p}` is the defining identity of the level-1 norm. -/
theorem gnLevStepOneClean {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (hm : 2 ≤ m)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : Work.Diff.STE.Periodic1 f)
    (U : ℝ) (hU0 : 0 ≤ U) (hU : ∀ x : ι → ℝ, ‖f x‖ ≤ U)
    (hibp : ∀ i : ι,
      ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pd i f x‖ ^ Work.Diff.STE.gnP m 1
        ≤ (Work.Diff.STE.gnP m 1 - 1) * ∫ x in Work.Diff.STE.unitCube (ι := ι),
            ‖f x‖ * ‖Work.Diff.STE.pd i f x‖ ^ (Work.Diff.STE.gnP m 1 - 2)
              * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i f) x‖) :
    (Work.Diff.STE.gnLev (ι := ι) m f 1) ^ 2
      ≤ Work.Diff.STE.gnC (ι := ι) m 1 * U * Work.Diff.STE.gnLev (ι := ι) m f 2 := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hp2 : 2 ≤ Work.Diff.STE.gnP m 1 := Work.Diff.STE.gnP_two_le (m := m) (k := 1) le_rfl hm1
  have hp0 : 0 < Work.Diff.STE.gnP m 1 := by linarith
  have hp1 : 0 ≤ Work.Diff.STE.gnP m 1 - 1 := by linarith
  set L : ℝ := Work.Diff.STE.gnLev (ι := ι) m f 2 with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; exact Work.Diff.STE.gnLev_nonneg m f 2
  set Cc : ℝ := (Work.Diff.STE.gnP m 1 - 1) * U * L with hCdef
  have hC0 : 0 ≤ Cc := by
    rw [hCdef]; exact mul_nonneg (mul_nonneg hp1 hU0) hL0
  have hkey : ∀ l : Fin 1 → ι,
      (∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec 1 l f x‖ ^ Work.Diff.STE.gnP m 1)
        ^ (2 / Work.Diff.STE.gnP m 1) ≤ Cc := by
    intro l
    set i : ι := l 0 with hidef
    have hpdvec : Work.Diff.STE.pdVec 1 l f = Work.Diff.STE.pd i f := by
      rw [hidef]
      simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_succ, List.ofFn_zero,
        List.foldr_cons, List.foldr_nil]
    have hAeq : (∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec 1 l f x‖ ^ Work.Diff.STE.gnP m 1)
        = ∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pd i f x‖ ^ Work.Diff.STE.gnP m 1 := by
      rw [hpdvec]
    have hA0 : 0 ≤ ∫ x in Work.Diff.STE.unitCube,
        ‖Work.Diff.STE.pd i f x‖ ^ Work.Diff.STE.gnP m 1 :=
      integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
    have hpdcont : Continuous (Work.Diff.STE.pd i f) := by
      have h1 := Work.Diff.STE.contDiff_pdVec_top (k := 1) (l := fun _ : Fin 1 => i) f hf
      have h2 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd i f) := by
        simpa only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_succ, List.ofFn_zero,
          List.foldr_cons, List.foldr_nil] using h1
      exact h2.continuous
    have hpd2cont : Continuous (Work.Diff.STE.pd i (Work.Diff.STE.pd i f)) := by
      have h1 := Work.Diff.STE.contDiff_pdVec_top (k := 2) (l := fun _ : Fin 2 => i) f hf
      have h2 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd i (Work.Diff.STE.pd i f)) := by
        simpa only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_succ, List.ofFn_zero,
          List.foldr_cons, List.foldr_nil] using h1
      exact h2.continuous
    set psi : (ι → ℝ) → ℝ := fun x => ‖Work.Diff.STE.pd i f x‖ ^ (Work.Diff.STE.gnP m 1 - 2)
        * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i f) x‖ with hpsidef
    set J : ℝ := ∫ x in Work.Diff.STE.unitCube, psi x with hJdef
    have hpsicont : Continuous psi := by
      rw [hpsidef]
      exact (hpdcont.norm.rpow_const (fun x =>
        Or.inr (by linarith : 0 ≤ Work.Diff.STE.gnP m 1 - 2))).mul hpd2cont.norm
    have hpsi0 : ∀ x : ι → ℝ, 0 ≤ psi x := by
      rw [hpsidef]; intro x
      exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    have hJ0 : 0 ≤ J := by rw [hJdef]; exact integral_nonneg hpsi0
    have hcong : (∫ x in Work.Diff.STE.unitCube, ‖f x‖ * psi x)
        = ∫ x in Work.Diff.STE.unitCube,
            ‖f x‖ * ‖Work.Diff.STE.pd i f x‖ ^ (Work.Diff.STE.gnP m 1 - 2)
              * ‖Work.Diff.STE.pd i (Work.Diff.STE.pd i f) x‖ := by
      rw [hpsidef]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
    have h1 : (∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pd i f x‖ ^ Work.Diff.STE.gnP m 1)
        ≤ (Work.Diff.STE.gnP m 1 - 1) * ∫ x in Work.Diff.STE.unitCube, ‖f x‖ * psi x := by
      rw [hcong]
      exact hibp i
    have h2 : (∫ x in Work.Diff.STE.unitCube, ‖f x‖ * psi x) ≤ U * J := by
      rw [hJdef]
      exact integral_normMul_le_U_mul f psi U hU hf.continuous hpsicont hpsi0
    have h3 : J ≤ (∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pd i f x‖ ^ Work.Diff.STE.gnP m 1)
        ^ ((Work.Diff.STE.gnP m 1 - 2) / Work.Diff.STE.gnP m 1) * L := by
      rw [hJdef, hpsidef, hLdef]
      have hH := holder_pd_order2 (ι := ι) m hm f hf i
      have hL2 := level2_secondDeriv_le (ι := ι) m hm f i
      exact le_trans hH (mul_le_mul_of_nonneg_left hL2 (Real.rpow_nonneg hA0 _))
    have hbd : (∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pd i f x‖ ^ Work.Diff.STE.gnP m 1)
        ≤ Cc * (∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pd i f x‖ ^ Work.Diff.STE.gnP m 1)
          ^ ((Work.Diff.STE.gnP m 1 - 2) / Work.Diff.STE.gnP m 1) := by
      calc (∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pd i f x‖ ^ Work.Diff.STE.gnP m 1)
          ≤ (Work.Diff.STE.gnP m 1 - 1) * ∫ x in Work.Diff.STE.unitCube, ‖f x‖ * psi x := h1
        _ ≤ (Work.Diff.STE.gnP m 1 - 1) * (U * J) := mul_le_mul_of_nonneg_left h2 hp1
        _ ≤ (Work.Diff.STE.gnP m 1 - 1) * (U * ((∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pd i f x‖ ^ Work.Diff.STE.gnP m 1)
              ^ ((Work.Diff.STE.gnP m 1 - 2) / Work.Diff.STE.gnP m 1) * L)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hU0) hp1
        _ = Cc * (∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pd i f x‖ ^ Work.Diff.STE.gnP m 1)
              ^ ((Work.Diff.STE.gnP m 1 - 2) / Work.Diff.STE.gnP m 1) := by
            rw [hCdef]; ring
    have hp5 := rpow_le_of_le_mul_rpow hA0 hC0 hp2 hbd
    rw [hAeq]
    exact hp5
  have hsum : (∑ l : Fin 1 → ι, ∫ x in Work.Diff.STE.unitCube,
        ‖Work.Diff.STE.pdVec 1 l f x‖ ^ Work.Diff.STE.gnP m 1)
      ^ (2 / Work.Diff.STE.gnP m 1)
      ≤ (Fintype.card (Fin 1 → ι) : ℝ) ^ (2 / Work.Diff.STE.gnP m 1) * Cc := by
    refine sum_rpow_le_of_each (fun l : Fin 1 → ι => ∫ x in Work.Diff.STE.unitCube,
      ‖Work.Diff.STE.pdVec 1 l f x‖ ^ Work.Diff.STE.gnP m 1) Cc
      (2 / Work.Diff.STE.gnP m 1) ?_ hC0 ?_ hkey
    · intro l
      exact integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
    · exact div_pos (by norm_num) hp0
  have hLHS : (Work.Diff.STE.gnLev (ι := ι) m f 1) ^ 2
      = (∑ l : Fin 1 → ι, ∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec 1 l f x‖ ^ Work.Diff.STE.gnP m 1)
          ^ (2 / Work.Diff.STE.gnP m 1) := by
    have hS : 0 ≤ ∑ l : Fin 1 → ι, ∫ x in Work.Diff.STE.unitCube,
        ‖Work.Diff.STE.pdVec 1 l f x‖ ^ Work.Diff.STE.gnP m 1 :=
      Finset.sum_nonneg (fun l _ => integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))
    rw [Work.Diff.STE.gnLev]
    rw [← Real.rpow_natCast _ 2]
    simp only [Nat.cast_ofNat]
    rw [← Real.rpow_mul hS (1 / Work.Diff.STE.gnP m 1) 2]
    congr 1
    ring
  have hfin : (Fintype.card (Fin 1 → ι) : ℝ) ^ (2 / Work.Diff.STE.gnP m 1) * Cc
      ≤ Work.Diff.STE.gnC (ι := ι) m 1 * U * L := by
    rw [hCdef]
    have hUL : 0 ≤ U * L := mul_nonneg hU0 hL0
    have hstep : (Fintype.card (Fin 1 → ι) : ℝ) ^ (2 / Work.Diff.STE.gnP m 1)
        * (Work.Diff.STE.gnP m 1 - 1) ≤ Work.Diff.STE.gnC (ι := ι) m 1 := by
      rw [Work.Diff.STE.gnC]
      exact le_max_right 0 _
    calc (Fintype.card (Fin 1 → ι) : ℝ) ^ (2 / Work.Diff.STE.gnP m 1)
          * ((Work.Diff.STE.gnP m 1 - 1) * U * L)
        = ((Fintype.card (Fin 1 → ι) : ℝ) ^ (2 / Work.Diff.STE.gnP m 1)
            * (Work.Diff.STE.gnP m 1 - 1)) * (U * L) := by ring
      _ ≤ Work.Diff.STE.gnC (ι := ι) m 1 * (U * L) := mul_le_mul_of_nonneg_right hstep hUL
      _ = Work.Diff.STE.gnC (ι := ι) m 1 * U * L := by ring
  calc (Work.Diff.STE.gnLev (ι := ι) m f 1) ^ 2
      = (∑ l : Fin 1 → ι, ∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec 1 l f x‖ ^ Work.Diff.STE.gnP m 1)
          ^ (2 / Work.Diff.STE.gnP m 1) := hLHS
    _ ≤ (Fintype.card (Fin 1 → ι) : ℝ) ^ (2 / Work.Diff.STE.gnP m 1) * Cc := hsum
    _ ≤ Work.Diff.STE.gnC (ι := ι) m 1 * U * L := hfin

end Work.Diff.STE.GN
