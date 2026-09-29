import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.CDT.SympDenom
import Submission.Work.CDen.c_denoms

/-! Guidance from the project lead (the requester):

# Area ADen — denominators of the 14 functions (`ADenoms`)
Mirror `Work.CDen.c_denoms` (Theorem C, proved).
-/

namespace Work.ADen

open Submission.CDTPlan
open PowerSeries

noncomputable section

/-! ## Denominators up to a fixed integer factor -/

/-- `SDTK K c f`: `K · [1..2N+c]² · coeff N f ∈ ℤ` for every `N`.  This is the
`Work.CDen.SDT` predicate with an extra fixed integer factor `K`. -/
def SDTK (K c : ℕ) (f : PowerSeries ℚ) : Prop :=
  ∀ N : ℕ, ∃ z : ℤ,
    (K : ℚ) * (lcmUpto (2 * N + c) : ℚ) ^ 2 * PowerSeries.coeff N f = z

lemma SDTK.mono {K c : ℕ} {f : PowerSeries ℚ} (h : SDTK K c f) {j N c' : ℕ}
    (hj : 2 * j + c ≤ 2 * N + c') :
    ∃ z : ℤ, (K : ℚ) * (lcmUpto (2 * N + c') : ℚ) ^ 2 * PowerSeries.coeff j f = z := by
  obtain ⟨z, hz⟩ := h j
  obtain ⟨q, hq⟩ := Work.CDen.lcmUpto_dvd_of_le hj
  refine ⟨(q : ℤ) ^ 2 * z, ?_⟩
  have hL : ((lcmUpto (2 * N + c') : ℚ)) = (lcmUpto (2 * j + c) : ℚ) * (q : ℚ) := by
    rw [hq, Nat.cast_mul]
  rw [hL]
  calc (K : ℚ) * ((lcmUpto (2 * j + c) : ℚ) * (q : ℚ)) ^ 2 * PowerSeries.coeff j f
      = (q : ℚ) ^ 2
        * ((K : ℚ) * ((lcmUpto (2 * j + c) : ℚ)) ^ 2 * PowerSeries.coeff j f) := by ring
    _ = (q : ℚ) ^ 2 * (z : ℚ) := by rw [hz]
    _ = ((q ^ 2 * z : ℤ) : ℚ) := by push_cast; ring

lemma SDTK.dYstep {K c : ℕ} {f : PowerSeries ℚ} (h : SDTK K c f) :
    SDTK K (c + 2) (dY f) := by
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
  calc (K : ℚ) * (lcmUpto (2 * (N + 1) + c) : ℚ) ^ 2
        * (((N + 1 : ℕ) : ℚ) * PowerSeries.coeff (N + 1) f)
      = ((N + 1 : ℕ) : ℚ)
        * ((K : ℚ) * (lcmUpto (2 * (N + 1) + c) : ℚ) ^ 2
            * PowerSeries.coeff (N + 1) f) := by ring
    _ = ((N + 1 : ℕ) : ℚ) * (z : ℚ) := by rw [hz]
    _ = ((((N + 1 : ℕ) : ℤ) * z : ℤ) : ℚ) := by push_cast; ring

/-! ## From `SDTK` to `HasDenomType` -/

lemma denom_of_SDTK {K c : ℕ} (hK : 0 < K) (f : PowerSeries ℚ) (h : SDTK K c f) :
    HasDenomType 0 ![2,2] f := by
  refine ⟨K, c, hK, ?_⟩
  intro N hN
  obtain ⟨z, hz⟩ := h N
  refine ⟨z, ?_⟩
  rw [Work.CDen.prod_bC_22]
  simpa using hz

lemma denom_intY {K c : ℕ} (hK : 0 < K) (f : PowerSeries ℚ) (h : SDTK K c f) :
    HasDenomType 1 ![2,2] (intY f) := by
  refine ⟨K, c, hK, ?_⟩
  intro N hN
  obtain ⟨z, hz⟩ := h.mono (j := N - 1) (N := N) (c' := c) (by omega)
  refine ⟨z, ?_⟩
  rw [Work.CDen.prod_bC_22]
  have hmul := Work.CDen.mul_coeff_intY N f hN
  calc (K : ℚ) * (N : ℚ) ^ 1 * (lcmUpto (2 * N + c) : ℚ) ^ 2 * PowerSeries.coeff N (intY f)
      = (K : ℚ) * (lcmUpto (2 * N + c) : ℚ) ^ 2
          * ((N : ℚ) * PowerSeries.coeff N (intY f)) := by ring
    _ = (K : ℚ) * (lcmUpto (2 * N + c) : ℚ) ^ 2 * PowerSeries.coeff (N - 1) f := by rw [hmul]
    _ = (z : ℚ) := hz

lemma denom_intY_tq {K c : ℕ} (hK : 0 < K) (k : ℕ) (f : PowerSeries ℚ) (h : SDTK K c f) :
    HasDenomType 1 ![2,2] (intY (tq k f)) := by
  refine ⟨K, c + 2 * k, hK, ?_⟩
  intro N hN
  obtain ⟨z, hz⟩ := h.mono (j := N + k - 1) (N := N) (c' := c + 2 * k) (by omega)
  refine ⟨z, ?_⟩
  rw [Work.CDen.prod_bC_22]
  have hN0 : N ≠ 0 := by omega
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  have hcoe : PowerSeries.coeff N (intY (tq k f))
      = PowerSeries.coeff (N + k - 1) f / (N : ℚ) := by
    have hidx : N - 1 + k = N + k - 1 := by omega
    rw [Work.CDen.coeff_intY, if_neg hN0, Work.CDen.coeff_tq, hidx]
  rw [hcoe]
  have hfrac : (K : ℚ) * (N : ℚ) ^ 1 * (lcmUpto (2 * N + (c + 2 * k)) : ℚ) ^ 2
        * (PowerSeries.coeff (N + k - 1) f / (N : ℚ))
      = (K : ℚ) * (lcmUpto (2 * N + (c + 2 * k)) : ℚ) ^ 2
          * PowerSeries.coeff (N + k - 1) f := by
    field_simp
  rw [hfrac]
  exact hz

/-! ## Denominators in the `[1..n]²` normalisation, with a factor -/

/-- `HDT M f`: `M · [1..n]² · coeff n f ∈ ℤ` for every `n` (the `HasDenomTypeSq`
normalisation, up to the factor `M`). -/
def HDT (M : ℕ) (f : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, (M : ℚ) * (lcmUpto n : ℚ) ^ 2 * PowerSeries.coeff n f = z

lemma HDT.int_mul {M : ℕ} {f : PowerSeries ℚ} (h : HDT M f) (k : ℤ) :
    HDT M (PowerSeries.C (k : ℚ) * f) := by
  intro n
  obtain ⟨z, hz⟩ := h n
  rw [PowerSeries.coeff_C_mul]
  refine ⟨k * z, ?_⟩
  calc (M : ℚ) * (lcmUpto n : ℚ) ^ 2 * ((k : ℚ) * PowerSeries.coeff n f)
      = (k : ℚ) * ((M : ℚ) * (lcmUpto n : ℚ) ^ 2 * PowerSeries.coeff n f) := by ring
    _ = (k : ℚ) * (z : ℚ) := by rw [hz]
    _ = ((k * z : ℤ) : ℚ) := by push_cast; ring

lemma HDT.add {M : ℕ} {f g : PowerSeries ℚ} (hf : HDT M f) (hg : HDT M g) :
    HDT M (f + g) := by
  intro n
  obtain ⟨zf, hzf⟩ := hf n
  obtain ⟨zg, hzg⟩ := hg n
  rw [map_add]
  refine ⟨zf + zg, ?_⟩
  calc (M : ℚ) * (lcmUpto n : ℚ) ^ 2 * (PowerSeries.coeff n f + PowerSeries.coeff n g)
      = (M : ℚ) * (lcmUpto n : ℚ) ^ 2 * PowerSeries.coeff n f
        + (M : ℚ) * (lcmUpto n : ℚ) ^ 2 * PowerSeries.coeff n g := by ring
    _ = (zf : ℚ) + (zg : ℚ) := by rw [hzf, hzg]
    _ = ((zf + zg : ℤ) : ℚ) := by push_cast; ring

lemma HDT.mul_factor {M K : ℕ} {f : PowerSeries ℚ} (h : HDT M f) : HDT (M * K) f := by
  intro n
  obtain ⟨z, hz⟩ := h n
  refine ⟨(K : ℤ) * z, ?_⟩
  calc (M * K : ℕ) * (lcmUpto n : ℚ) ^ 2 * PowerSeries.coeff n f
      = (K : ℚ) * ((M : ℚ) * (lcmUpto n : ℚ) ^ 2 * PowerSeries.coeff n f) := by
        push_cast; ring
    _ = (K : ℚ) * (z : ℚ) := by rw [hz]
    _ = (((K : ℤ) * z : ℤ) : ℚ) := by push_cast; ring

lemma HDT.to_HasDenomTypeSq {M : ℕ} {f : PowerSeries ℚ} (h : HDT M f) :
    Submission.CDT.HasDenomTypeSq
      (fun n => PowerSeries.coeff n (PowerSeries.C (M : ℚ) * f)) := by
  intro n
  obtain ⟨z, hz⟩ := h n
  refine ⟨z, ?_⟩
  have hL : (Submission.CDT.lcmRange n : ℚ) = (lcmUpto n : ℚ) := by
    simp [Work.CDen.lcmUpto_eq_lcmRange]
  rw [hL]
  show (lcmUpto n : ℚ) ^ 2 * PowerSeries.coeff n (PowerSeries.C (M : ℚ) * f) = (z : ℚ)
  rw [PowerSeries.coeff_C_mul]
  calc ((lcmUpto n : ℚ)) ^ 2 * ((M : ℚ) * PowerSeries.coeff n f)
      = (M : ℚ) * (lcmUpto n : ℚ) ^ 2 * PowerSeries.coeff n f := by ring
    _ = (z : ℚ) := hz


/-! ## `H = aH_A + bH_B + cH_C` has `[1..n]²`-denominators up to the factor `8K` -/

lemma HA_HDT_one : HDT 1 Submission.CDT.HA := by
  intro n
  refine ⟨((lcmUpto n) ^ 2 * Submission.CDT.HA_coeffZ n : ℤ), ?_⟩
  rw [Submission.CDT.coeff_HA, Submission.CDT.HA_coeff_eq_cast]
  push_cast
  ring

lemma HB_HDT_K (K : ℕ)
    (hB : ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ,
      (K : ℚ) * (lcmUpto n : ℚ) ^ 2 * Submission.CDT.HB_coeff n = z) :
    HDT K Submission.CDT.HB := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, ?_⟩
    rw [Submission.CDT.coeff_HB, Submission.CDT.HB_coeff_zero]
    simp
  · obtain ⟨z, hz⟩ := hB n hn
    exact ⟨z, by rw [Submission.CDT.coeff_HB]; exact hz⟩

lemma HC_HDT_eight
    (hC : ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ,
      (8 : ℚ) * (lcmUpto n : ℚ) ^ 2 * Submission.CDT.HC_coeff n = z) :
    HDT 8 Submission.CDT.HC := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, ?_⟩
    rw [Submission.CDT.coeff_HC, Submission.CDT.HC_coeff_zero]
    simp
  · obtain ⟨z, hz⟩ := hC n hn
    exact ⟨z, by rw [Submission.CDT.coeff_HC]; exact hz⟩

lemma HZ_HDT (a b c : ℤ) (K : ℕ)
    (hB : ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ,
      (K : ℚ) * (lcmUpto n : ℚ) ^ 2 * Submission.CDT.HB_coeff n = z)
    (hC : ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ,
      (8 : ℚ) * (lcmUpto n : ℚ) ^ 2 * Submission.CDT.HC_coeff n = z) :
    HDT (K * 8) (Submission.CDT.ZagierH (a : ℚ) (b : ℚ) (c : ℚ)) := by
  have hHA : HDT (K * 8) (PowerSeries.C (a : ℚ) * Submission.CDT.HA) := by
    have h := HA_HDT_one.mul_factor (K := K * 8)
    rw [Nat.one_mul] at h
    exact h.int_mul a
  have hHB : HDT (K * 8) (PowerSeries.C (b : ℚ) * Submission.CDT.HB) :=
    (HB_HDT_K K hB).mul_factor (K := 8) |>.int_mul b
  have hHC : HDT (K * 8) (PowerSeries.C (c : ℚ) * Submission.CDT.HC) := by
    have h := (HC_HDT_eight hC).mul_factor (K := K)
    rw [Nat.mul_comm] at h
    exact h.int_mul c
  have hsum := (hHA.add hHB).add hHC
  simpa only [Submission.CDT.ZagierH] using hsum

/-! ## The symmetrised `G = Sym⁺H` has `SDTK`-denominators -/

lemma GZ_SDTK (a b c : ℤ) (K : ℕ) (_hK : 0 < K)
    (hB : ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ,
      (K : ℚ) * (lcmUpto n : ℚ) ^ 2 * Submission.CDT.HB_coeff n = z)
    (hC : ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ,
      (8 : ℚ) * (lcmUpto n : ℚ) ^ 2 * Submission.CDT.HC_coeff n = z) :
    SDTK (K * 8) 0 (GZ a b c) := by
  have hHDT : HDT (K * 8) (Submission.CDT.ZagierH (a : ℚ) (b : ℚ) (c : ℚ)) :=
    HZ_HDT a b c K hB hC
  have hsq : Submission.CDT.HasDenomTypeSq (fun n => PowerSeries.coeff n
      (PowerSeries.C ((K * 8 : ℕ) : ℚ) * Submission.CDT.ZagierH (a : ℚ) (b : ℚ) (c : ℚ))) :=
    hHDT.to_HasDenomTypeSq
  have hsym := Submission.CDT.sympSym_denomType _ hsq
  intro N
  obtain ⟨z, hz⟩ := hsym N
  refine ⟨z, ?_⟩
  have hlin := Submission.CDT.sympSym_C_mul (((K * 8 : ℕ) : ℚ))
      (Submission.CDT.ZagierH (a : ℚ) (b : ℚ) (c : ℚ))
  rw [hlin] at hz
  rw [PowerSeries.coeff_C_mul] at hz
  have hL : (Submission.CDT.lcmRange (2 * N) : ℚ) = (lcmUpto (2 * N) : ℚ) := by
    simp [Work.CDen.lcmUpto_eq_lcmRange]
  rw [hL] at hz
  rw [Nat.add_zero]
  have hGZ : GZ a b c
      = Submission.CDT.sympSym (Submission.CDT.ZagierH (a : ℚ) (b : ℚ) (c : ℚ)) := rfl
  rw [hGZ]
  calc ((K * 8 : ℕ) : ℚ) * (lcmUpto (2 * N) : ℚ) ^ 2
        * PowerSeries.coeff N
            (Submission.CDT.sympSym (Submission.CDT.ZagierH (a : ℚ) (b : ℚ) (c : ℚ)))
      = (lcmUpto (2 * N) : ℚ) ^ 2 * (((K * 8 : ℕ) : ℚ)
          * PowerSeries.coeff N
              (Submission.CDT.sympSym (Submission.CDT.ZagierH (a : ℚ) (b : ℚ) (c : ℚ)))) := by
        ring
    _ = (z : ℚ) := hz


/-- **Area ADen**: the 14 functions `B1,...,B5, G, G', G'', G''', B6, B7, intG,
int (G-G(0))/y, int (G-G(0)-G'(0)y)/y^2` have the denominator types recorded by
the arrays `eA`/`bA` - the pure rows from `PureFacts` and the `G`-rows from the
`[1..2n]^2`-integrality of `Sym+H` (`sympSym_denomType`), with the fixed factor
`8K` absorbed into `HasDenomType`'s `K`. -/
theorem a_denoms (hP : PureFacts) (hB : ZagierBIntegrality) (hC : ZagierCIntegrality) :
    ADenoms := by
  intro a b c i
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _hD⟩ := hP
  obtain ⟨K, hKpos, hBK⟩ := hB
  have hG : SDTK (K * 8) 0 (GZ a b c) := GZ_SDTK a b c K hKpos hBK hC
  have hK8 : 0 < K * 8 := Nat.mul_pos hKpos (by norm_num)
  fin_cases i
  · simpa [fourteen, show eA 0 = 0 by decide, show bA 0 = ![0,0] by decide] using h1
  · simpa [fourteen, show eA 1 = 0 by decide, show bA 1 = ![2,0] by decide] using h2
  · simpa [fourteen, show eA 2 = 1 by decide, show bA 2 = ![2,0] by decide] using h3
  · simpa [fourteen, show eA 3 = 0 by decide, show bA 3 = ![2,2] by decide] using h4
  · simpa [fourteen, show eA 4 = 0 by decide, show bA 4 = ![2,2] by decide] using h5
  · simpa [fourteen, show eA 5 = 0 by decide, show bA 5 = ![2,2] by decide]
      using denom_of_SDTK hK8 (GZ a b c) hG
  · simpa [fourteen, show eA 6 = 0 by decide, show bA 6 = ![2,2] by decide]
      using denom_of_SDTK hK8 (dY (GZ a b c)) hG.dYstep
  · simpa [fourteen, show eA 7 = 0 by decide, show bA 7 = ![2,2] by decide]
      using denom_of_SDTK hK8 (dY (dY (GZ a b c))) hG.dYstep.dYstep
  · simpa [fourteen, show eA 8 = 0 by decide, show bA 8 = ![2,2] by decide]
      using denom_of_SDTK hK8 (dY (dY (dY (GZ a b c)))) hG.dYstep.dYstep.dYstep
  · simpa [fourteen, show eA 9 = 1 by decide, show bA 9 = ![2,2] by decide] using h6
  · simpa [fourteen, show eA 10 = 1 by decide, show bA 10 = ![2,2] by decide] using h7
  · simpa [fourteen, show eA 11 = 1 by decide, show bA 11 = ![2,2] by decide]
      using denom_intY hK8 (GZ a b c) hG
  · simpa [fourteen, show eA 12 = 1 by decide, show bA 12 = ![2,2] by decide]
      using denom_intY_tq hK8 1 (GZ a b c) hG
  · simpa [fourteen, show eA 13 = 1 by decide, show bA 13 = ![2,2] by decide]
      using denom_intY_tq hK8 2 (GZ a b c) hG

end

end Work.ADen
