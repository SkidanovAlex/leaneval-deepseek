import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.Commons.RingTheory.PowerSeries.iterate_derivative_coeff
import Submission.Commons.RingTheory.PowerSeries.coeff_mul_X

/-!
# Denominator types of the 17 functions of Theorem C (`CDenoms`)

The seven pure rows come from `PureFacts`; the `G`-rows come from
`Submission.CDT.logP_symm_denomType` (denominator type `[1..2N]²` for the
symmetrised unlikely `G`-function), together with the elementary bookkeeping
that taking derivatives lowers the index by one (costing a factor `2` on the
`lcm` argument), while integration/truncation raises it.
-/

namespace Work.CDen

open Submission.CDTPlan

noncomputable section

/-! ## Arithmetic of `lcmUpto` -/

lemma lcmUpto_dvd_of_le {m n : ℕ} (h : m ≤ n) : lcmUpto m ∣ lcmUpto n := by
  unfold lcmUpto
  exact Finset.lcm_mono (fun x hx => by simp only [Finset.mem_Icc] at hx ⊢; omega)

lemma lcmUpto_eq_lcmRange (N : ℕ) : lcmUpto N = Submission.CDT.lcmRange N :=
  (Submission.CDT.lcmRange_eq_Icc_lcm N).symm

/-! ## The denominator predicate on the `G`-side

`SDT c f` says `[1..2N+c]²·coeff N f ∈ ℤ` for every `N`. -/

def SDT (c : ℕ) (f : PowerSeries ℚ) : Prop :=
  ∀ N : ℕ, ∃ z : ℤ, ((lcmUpto (2 * N + c) : ℚ)) ^ 2 * PowerSeries.coeff N f = z

lemma SDT.mono {c : ℕ} {f : PowerSeries ℚ} (h : SDT c f) {j N c' : ℕ}
    (hj : 2 * j + c ≤ 2 * N + c') :
    ∃ z : ℤ, ((lcmUpto (2 * N + c') : ℚ)) ^ 2 * PowerSeries.coeff j f = z := by
  obtain ⟨z, hz⟩ := h j
  obtain ⟨q, hq⟩ := lcmUpto_dvd_of_le hj
  refine ⟨(q : ℤ) ^ 2 * z, ?_⟩
  have hL : ((lcmUpto (2 * N + c') : ℚ)) = (lcmUpto (2 * j + c) : ℚ) * (q : ℚ) := by
    rw [hq, Nat.cast_mul]
  rw [hL]
  calc ((lcmUpto (2 * j + c) : ℚ) * (q : ℚ)) ^ 2 * PowerSeries.coeff j f
      = (q : ℚ) ^ 2 * (((lcmUpto (2 * j + c) : ℚ)) ^ 2 * PowerSeries.coeff j f) := by ring
    _ = (q : ℚ) ^ 2 * (z : ℚ) := by rw [hz]
    _ = ((q ^ 2 * z : ℤ) : ℚ) := by push_cast; ring

lemma SDT.dYstep {c : ℕ} {f : PowerSeries ℚ} (h : SDT c f) : SDT (c + 2) (dY f) := by
  intro N
  obtain ⟨z, hz⟩ := h (N + 1)
  rw [show 2 * N + (c + 2) = 2 * (N + 1) + c from by ring]
  refine ⟨((N + 1 : ℕ) : ℤ) * z, ?_⟩
  have hc : PowerSeries.coeff N (dY f)
      = ((N + 1 : ℕ) : ℚ) * PowerSeries.coeff (N + 1) f := by
    have h := PowerSeries.coeff_iterate_derivative (R := ℚ) f 1 N
    rw [dY]
    simpa [Nat.ascFactorial] using h
  rw [hc]
  calc ((lcmUpto (2 * (N + 1) + c) : ℚ)) ^ 2
        * (((N + 1 : ℕ) : ℚ) * PowerSeries.coeff (N + 1) f)
      = ((N + 1 : ℕ) : ℚ)
        * (((lcmUpto (2 * (N + 1) + c) : ℚ)) ^ 2 * PowerSeries.coeff (N + 1) f) := by ring
    _ = ((N + 1 : ℕ) : ℚ) * (z : ℚ) := by rw [hz]
    _ = ((((N + 1 : ℕ) : ℤ) * z : ℤ) : ℚ) := by push_cast; ring

/-! ## Coefficient formulas for `intY`, `tq`, and `X *` -/

lemma coeff_tq (k N : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff N (tq k f) = PowerSeries.coeff (N + k) f := by
  rw [tq, PowerSeries.coeff_mk]

lemma coeff_intY (N : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff N (intY f)
      = if N = 0 then 0 else PowerSeries.coeff (N - 1) f / (N : ℚ) := by
  rw [intY, PowerSeries.coeff_mk]

lemma coeff_X_mul (N : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff N (PowerSeries.X * f)
      = if 1 ≤ N then PowerSeries.coeff (N - 1) f else 0 := by
  rw [mul_comm PowerSeries.X f, Commons.RingTheory.PowerSeries.coeff_mul_X]

lemma mul_coeff_intY (N : ℕ) (f : PowerSeries ℚ) (hN : 1 ≤ N) :
    (N : ℚ) * PowerSeries.coeff N (intY f) = PowerSeries.coeff (N - 1) f := by
  have hN0 : N ≠ 0 := by omega
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  rw [coeff_intY, if_neg hN0]
  rw [mul_comm, div_mul_cancel₀ _ hNq]

/-! ## From `SDT` to `HasDenomType` -/

/-- The two-fold product `∏_{j:Fin 2} lcmUpto (b j · N + c)` for `b = ![2,2]`. -/
lemma prod_bC_22 (N c : ℕ) :
    (∏ j : Fin 2, (lcmUpto ((![2, 2] : Fin 2 → ℕ) j * N + c) : ℚ))
      = ((lcmUpto (2 * N + c) : ℚ)) ^ 2 := by
  rw [Fin.prod_univ_two]
  norm_num
  ring

lemma denom_of_SDT (c : ℕ) (f : PowerSeries ℚ) (h : SDT c f) :
    HasDenomType 0 ![2,2] f := by
  refine ⟨1, c, by norm_num, ?_⟩
  intro N hN
  obtain ⟨z, hz⟩ := h N
  refine ⟨z, ?_⟩
  rw [prod_bC_22]
  simpa using hz

lemma denom_intY (f : PowerSeries ℚ) (h : SDT 0 f) :
    HasDenomType 1 ![2,2] (intY f) := by
  refine ⟨1, 0, by norm_num, ?_⟩
  intro N hN
  obtain ⟨z, hz⟩ := h.mono (j := N - 1) (N := N) (c' := 0) (by omega)
  refine ⟨z, ?_⟩
  rw [prod_bC_22]
  have hmul := mul_coeff_intY N f hN
  calc (1 : ℚ) * (N : ℚ) ^ 1 * (lcmUpto (2 * N + 0) : ℚ) ^ 2 * PowerSeries.coeff N (intY f)
      = (lcmUpto (2 * N + 0) : ℚ) ^ 2
          * ((N : ℚ) * PowerSeries.coeff N (intY f)) := by ring
    _ = (lcmUpto (2 * N + 0) : ℚ) ^ 2 * PowerSeries.coeff (N - 1) f := by rw [hmul]
    _ = (z : ℚ) := hz

lemma denom_intY_tq (k : ℕ) (f : PowerSeries ℚ) (h : SDT 0 f) :
    HasDenomType 1 ![2,2] (intY (tq k f)) := by
  refine ⟨1, 2 * k, by norm_num, ?_⟩
  intro N hN
  obtain ⟨z, hz⟩ := h.mono (j := N + k - 1) (N := N) (c' := 2 * k) (by omega)
  refine ⟨z, ?_⟩
  rw [prod_bC_22]
  have hN0 : N ≠ 0 := by omega
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  have hcoe : PowerSeries.coeff N (intY (tq k f))
      = PowerSeries.coeff (N + k - 1) f / (N : ℚ) := by
    have hidx : N - 1 + k = N + k - 1 := by omega
    rw [coeff_intY, if_neg hN0, coeff_tq, hidx]
  rw [hcoe]
  have hfrac : ((1 : ℕ) : ℚ) * (N : ℚ) ^ 1 * (lcmUpto (2 * N + 2 * k) : ℚ) ^ 2
        * (PowerSeries.coeff (N + k - 1) f / (N : ℚ))
      = (lcmUpto (2 * N + 2 * k) : ℚ) ^ 2 * PowerSeries.coeff (N + k - 1) f := by
    field_simp
    ring
  rw [hfrac]
  exact hz

lemma denom_intY_X_mul (f : PowerSeries ℚ) (h : SDT 0 f) :
    HasDenomType 1 ![2,2] (intY (PowerSeries.X * f)) := by
  refine ⟨1, 0, by norm_num, ?_⟩
  intro N hN
  rw [prod_bC_22]
  have hN0 : N ≠ 0 := by omega
  by_cases hN1 : N = 1
  · subst hN1
    refine ⟨0, ?_⟩
    have hc : PowerSeries.coeff 1 (intY (PowerSeries.X * f)) = 0 := by
      rw [coeff_intY, if_neg (by norm_num : (1 : ℕ) ≠ 0), coeff_X_mul]
      norm_num
    rw [hc]
    norm_num
  · have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
    obtain ⟨z, hz⟩ := h.mono (j := N - 2) (N := N) (c' := 0) (by omega)
    refine ⟨z, ?_⟩
    have hcoe : PowerSeries.coeff N (intY (PowerSeries.X * f))
        = PowerSeries.coeff (N - 2) f / (N : ℚ) := by
      have hidx : N - 1 - 1 = N - 2 := by omega
      rw [coeff_intY, if_neg hN0, coeff_X_mul, if_pos (by omega : 1 ≤ N - 1), hidx]
    rw [hcoe]
    have hfrac : ((1 : ℕ) : ℚ) * (N : ℚ) ^ 1 * (lcmUpto (2 * N + 0) : ℚ) ^ 2
          * (PowerSeries.coeff (N - 2) f / (N : ℚ))
        = (lcmUpto (2 * N + 0) : ℚ) ^ 2 * PowerSeries.coeff (N - 2) f := by
      field_simp
      ring
    rw [hfrac]
    exact hz

/-! ## The symmetrised unlikely `G`-function has `SDT 0` -/

lemma odd_two_mul_add_one (m : ℕ) : Odd (2 * (m : ℤ) + 1) := ⟨(m : ℤ), by ring⟩

lemma GC_SDT (m n : ℕ) (ra rb rab r0 : ℤ) : SDT 0 (GC m n ra rb rab r0) := by
  intro N
  have hcast1 : ((2 * (m : ℤ) + 1 : ℤ) : ℚ) = 2 * (m : ℚ) + 1 := by push_cast; ring
  have hcast2 : ((2 * (n : ℤ) + 1 : ℤ) : ℚ) = 2 * (n : ℚ) + 1 := by push_cast; ring
  obtain ⟨z, hz⟩ := (Submission.CDT.logP_symm_denomType (2 * (m : ℤ) + 1) (2 * (n : ℤ) + 1)
      (odd_two_mul_add_one m) (odd_two_mul_add_one n) ra rb rab r0).1 N
  refine ⟨z, ?_⟩
  have hmain : ((Submission.CDT.lcmRange (2 * N) : ℚ)) ^ 2
      * PowerSeries.coeff N (GC m n ra rb rab r0) = (z : ℚ) := by
    rw [GC, PC, ← hcast1, ← hcast2]
    exact hz
  rw [show 2 * N + 0 = 2 * N from by ring, lcmUpto_eq_lcmRange]
  exact hmain

end

open Submission.CDTPlan in
theorem c_denoms (hP : PureFacts) : CDenoms := by
  intro m n ra rb rab r0 i
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, hD⟩ := hP
  have hG : SDT 0 (GC m n ra rb rab r0) := GC_SDT m n ra rb rab r0
  fin_cases i
  · simpa [seventeen, show eC 0 = 0 by decide, show bC 0 = ![0,0] by decide] using h1
  · simpa [seventeen, show eC 1 = 0 by decide, show bC 1 = ![2,0] by decide] using h2
  · simpa [seventeen, show eC 2 = 1 by decide, show bC 2 = ![2,0] by decide] using h3
  · simpa [seventeen, show eC 3 = 0 by decide, show bC 3 = ![2,2] by decide] using h4
  · simpa [seventeen, show eC 4 = 0 by decide, show bC 4 = ![2,2] by decide] using h5
  · simpa [seventeen, show eC 5 = 0 by decide, show bC 5 = ![2,2] by decide]
      using denom_of_SDT 0 (GC m n ra rb rab r0) hG
  · simpa [seventeen, show eC 6 = 0 by decide, show bC 6 = ![2,2] by decide]
      using denom_of_SDT 2 (dY (GC m n ra rb rab r0)) hG.dYstep
  · simpa [seventeen, show eC 7 = 0 by decide, show bC 7 = ![2,2] by decide]
      using denom_of_SDT 4 (dY (dY (GC m n ra rb rab r0))) hG.dYstep.dYstep
  · simpa [seventeen, show eC 8 = 0 by decide, show bC 8 = ![2,2] by decide]
      using denom_of_SDT 6 (dY (dY (dY (GC m n ra rb rab r0)))) hG.dYstep.dYstep.dYstep
  · simpa [seventeen, show eC 9 = 1 by decide, show bC 9 = ![2,2] by decide] using h6
  · simpa [seventeen, show eC 10 = 1 by decide, show bC 10 = ![2,2] by decide] using h7
  · simpa [seventeen, show eC 11 = 1 by decide, show bC 11 = ![2,2] by decide]
      using denom_intY_X_mul (GC m n ra rb rab r0) hG
  · simpa [seventeen, show eC 12 = 1 by decide, show bC 12 = ![2,2] by decide]
      using denom_intY (GC m n ra rb rab r0) hG
  · simpa [seventeen, show eC 13 = 1 by decide, show bC 13 = ![2,2] by decide]
      using denom_intY_tq 1 (GC m n ra rb rab r0) hG
  · simpa [seventeen, show eC 14 = 1 by decide, show bC 14 = ![2,2] by decide]
      using denom_intY_tq 2 (GC m n ra rb rab r0) hG
  · simpa [seventeen, show eC 15 = 1 by decide, show bC 15 = ![2,2] by decide]
      using denom_intY_tq 3 (GC m n ra rb rab r0) hG
  · simpa [seventeen, show eC 16 = 1 by decide, show bC 16 = ![2,2] by decide]
      using denom_intY_tq 4 (GC m n ra rb rab r0) hG

end Work.CDen
