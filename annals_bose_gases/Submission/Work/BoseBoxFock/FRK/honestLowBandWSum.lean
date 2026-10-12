import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBoxFock.FRK.lowBandAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.FRK

open Work.BoseBoxFock

set_option maxHeartbeats 800000

/-!
# `Work.BoseBoxFock.FRK.honestLowBandWSum`

The low-band sum of the `Ŵ₁`-row: the labels `k` that are *excited* and *outside* FS's
high-momentum region `P_H = {1/(2K_H a) ≤ ‖k‖}` number at most the number of integer
vectors with `|n_i| ≤ ℓ/(4πK_H a)`, namely `(2⌈x⌉+1)³ ≤ 27(1+4π)³x³` for
`x = ℓ/(4πK_H a) ≥ 1/(4π)`.  With `|Ŵ₁ k| ≤ C a` (the hypothesis `hW1`) this bounds the
whole low-band sum by `C a · 27(1+4π)³x³`.

The proof is elementary: `abs_labVec_le` bounds the centred integer coordinates of a label
by `ℓ‖kmomLab ℓ N k‖/(2π)`, so below the `P_H` threshold they are all `< x`, and
`card_labVec_lt` counts the labels in the cube.
-/

/-- **The lattice count of the low band.**  The labels of `Lab N` that are excited and whose
momentum lies below the `P_H` threshold `1/(2K_H a)` number at most
`27(1+4π)³(ℓ/(4πK_H a))³` when `ℓ/(4πK_H a) ≥ 1/(4π)`. -/
theorem lowBand_card_le (N : ℕ) (F : Work.BoseB7.FockData (Lab N)) (E : Work.BoseB7.Q3Env (Lab N))
    (hℓ : 0 < E.ell) (hkm : ∀ k : Lab N, F.kmom k = kmomLab E.ell N k)
    (hy : 1 / (4 * Real.pi) ≤ E.ell / (4 * Real.pi * E.KH * E.aScat)) :
    ((((Work.BoseB7.excited (Lab N)) \ F.PHset E).card : ℕ) : ℝ)
      ≤ 27 * (1 + 4 * Real.pi) ^ 3 * (E.ell / (4 * Real.pi * E.KH * E.aScat)) ^ 3 := by
  have hx0 : 0 < E.ell / (4 * Real.pi * E.KH * E.aScat) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (4 * Real.pi)) hy
  have hKHa : 0 < E.KH * E.aScat := by
    have h4 : 0 < 4 * Real.pi * E.KH * E.aScat := by
      rcases div_pos_iff.mp hx0 with h | h
      · exact h.2
      · exact absurd h.1 (not_lt.mpr hℓ.le)
    have h4' : 0 < (4 * Real.pi) * (E.KH * E.aScat) := by nlinarith [h4]
    exact pos_of_mul_pos_right h4' (by positivity)
  have hmem : ∀ k : Lab N, k ∈ F.PHset E ↔
      (k ∈ Work.BoseB7.excited (Lab N)
        ∧ 1 / (2 * E.KH * E.aScat) ≤ ‖kmomLab E.ell N k‖) := by
    intro k
    rw [Work.BoseB7.FockData.PHset, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa only [Work.BoseB7.FockData.PH, hkm k] using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa only [Work.BoseB7.FockData.PH, hkm k] using h2⟩
  set x := E.ell / (4 * Real.pi * E.KH * E.aScat) with hxdef
  set M := Nat.ceil x with hMdef
  have hxpos : 0 < x := hx0
  have hyx : 1 / (4 * Real.pi) ≤ x := hy
  have hxM : x ≤ (M : ℝ) := Nat.le_ceil x
  have hMx : (M : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
  -- the low band is contained in the centred integer cube of radius `x`
  have hsub : ((Work.BoseB7.excited (Lab N)) \ F.PHset E)
      ⊆ (Finset.univ.filter (fun k : Lab N => ∀ i : Fin 3, |labVec N k i| < (M : ℤ))) := by
    intro k hk
    rw [Finset.mem_sdiff] at hk
    obtain ⟨hk1, hk2⟩ := hk
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun i => ?_⟩
    have hlt : ‖kmomLab E.ell N k‖ < 1 / (2 * E.KH * E.aScat) := by
      have hnot : ¬ (1 / (2 * E.KH * E.aScat) ≤ ‖kmomLab E.ell N k‖) :=
        fun hP => hk2 ((hmem k).mpr ⟨hk1, hP⟩)
      exact not_le.mp hnot
    have h1i : |(labVec N k i : ℝ)| ≤ E.ell * ‖kmomLab E.ell N k‖ / (2 * Real.pi) :=
      abs_labVec_le E.ell hℓ N k i
    have h2i : E.ell * ‖kmomLab E.ell N k‖ / (2 * Real.pi) < x := by
      have hmul : E.ell * ‖kmomLab E.ell N k‖ < E.ell * (1 / (2 * E.KH * E.aScat)) :=
        mul_lt_mul_of_pos_left hlt hℓ
      have h3 : E.ell * (1 / (2 * E.KH * E.aScat)) / (2 * Real.pi) = x := by
        rw [hxdef]
        field_simp
        ring
      rw [← h3]
      exact div_lt_div_of_pos_right hmul (by positivity)
    have h4i : |(labVec N k i : ℝ)| < (M : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt h1i h2i) hxM
    have h5i : ((|labVec N k i| : ℤ) : ℝ) < (M : ℝ) := by
      rw [Int.cast_abs]
      exact h4i
    exact_mod_cast h5i
  have hcard : ((Work.BoseB7.excited (Lab N)) \ F.PHset E).card ≤ (2 * M + 1) ^ 3 :=
    le_trans (Finset.card_le_card hsub) (card_labVec_lt N M)
  have harith : (((2 * M + 1 : ℕ) : ℝ)) ^ 3 ≤ 27 * (1 + 4 * Real.pi) ^ 3 * x ^ 3 := by
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    have hx4 : 1 ≤ 4 * Real.pi * x := by
      have h := mul_le_mul_of_nonneg_left hyx (show (0 : ℝ) ≤ 4 * Real.pi by positivity)
      have h' : 4 * Real.pi * (1 / (4 * Real.pi)) = 1 := by
        rw [mul_one_div, div_self (by positivity : (4 : ℝ) * Real.pi ≠ 0)]
      linarith [h, h'.le, h'.ge]
    have hA : ((2 * M + 1 : ℕ) : ℝ) ≤ 3 * (1 + 4 * Real.pi) * x := by
      have hcast : ((2 * M + 1 : ℕ) : ℝ) = 2 * (M : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      nlinarith [hMx, hxpos.le, hx4, hπ]
    have hA0 : (0 : ℝ) ≤ ((2 * M + 1 : ℕ) : ℝ) := by positivity
    have hB0 : (0 : ℝ) ≤ 3 * (1 + 4 * Real.pi) * x := by positivity
    have h4 := pow_le_pow_left₀ hA0 hA 3
    have hcube : (3 * (1 + 4 * Real.pi) * x) ^ 3 = 27 * (1 + 4 * Real.pi) ^ 3 * x ^ 3 := by ring
    linarith [h4, hcube.le, hcube.ge]
  have hcardR : ((((Work.BoseB7.excited (Lab N)) \ F.PHset E).card : ℕ) : ℝ)
      ≤ 27 * (1 + 4 * Real.pi) ^ 3 * x ^ 3 := by
    have h1 : ((((Work.BoseB7.excited (Lab N)) \ F.PHset E).card : ℕ) : ℝ)
        ≤ (((2 * M + 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcard
    have h2 : ((((2 * M + 1) ^ 3 : ℕ)) : ℝ) = (((2 * M + 1 : ℕ) : ℝ)) ^ 3 := by push_cast; ring
    linarith [h1, h2.le, h2.ge, harith]
  rw [hxdef] at hcardR
  exact hcardR

theorem honestLowBandWSum {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ C : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (hC : 0 ≤ C)
    (hW1 : ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ C * BoseGases.a v)
    (hy : 1 / (4 * Real.pi) ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell
        / (4 * Real.pi * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KH * BoseGases.a v)) :
    (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)
        \ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.PHset
            (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k|)
      ≤ C * BoseGases.a v * 27 * (1 + 4 * Real.pi) ^ 3
          * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.ell
              / (4 * Real.pi * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KH
                * BoseGases.a v)) ^ 3 := by
  let E := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E
  let F := (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
  have hell : Work.BoseBoxFock.ellH v μ = E.ell := by
    rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
    rfl
  have hkm : ∀ k : Work.BoseBoxFock.Lab (HM μ).N, F.kmom k = kmomLab E.ell (HM μ).N k :=
    fun k => by rw [← hell]; rfl
  have hℓ : 0 < E.ell := by rw [← hell]; exact Work.BoseBoxFock.ellH_pos v μ
  have hcard := lowBand_card_le (HM μ).N F E hℓ hkm hy
  have hsum : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N) \ F.PHset E, |E.W1 k|)
      ≤ ((((Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)) \ F.PHset E).card : ℕ) : ℝ)
          * (C * E.aScat) := by
    have h1 : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N) \ F.PHset E, |E.W1 k|)
        ≤ ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N) \ F.PHset E, (C * E.aScat) :=
      Finset.sum_le_sum (fun k _ => hW1 k)
    rwa [Finset.sum_const, nsmul_eq_mul] at h1
  have hfin : (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N) \ F.PHset E, |E.W1 k|)
      ≤ C * E.aScat * 27 * (1 + 4 * Real.pi) ^ 3
          * (E.ell / (4 * Real.pi * E.KH * E.aScat)) ^ 3 := by
    have hCa : 0 ≤ C * E.aScat := mul_nonneg hC hav.le
    calc (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N) \ F.PHset E, |E.W1 k|)
        ≤ ((((Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)) \ F.PHset E).card : ℕ) : ℝ)
            * (C * E.aScat) := hsum
      _ ≤ (27 * (1 + 4 * Real.pi) ^ 3 * (E.ell / (4 * Real.pi * E.KH * E.aScat)) ^ 3)
            * (C * E.aScat) := mul_le_mul_of_nonneg_right hcard hCa
      _ = C * E.aScat * 27 * (1 + 4 * Real.pi) ^ 3
            * (E.ell / (4 * Real.pi * E.KH * E.aScat)) ^ 3 := by ring
  exact hfin

end Work.BoseBoxFock.FRK
