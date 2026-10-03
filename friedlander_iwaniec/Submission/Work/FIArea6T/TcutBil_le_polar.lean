import Mathlib
import Submission.Work.FIArea6T.Defs
import Submission.Work.FIArea6T.Support
import Submission.Work.FIArea6.pair_phi_helpers
import Submission.Work.FIArea6.sum_d_bound
import Submission.Work.FIArea6T.InnerSum_le
import Submission.Work.FIArea6T.InnerSum_zero
import Submission.Work.FIArea4.absDelta_le_sector
import Submission.Work.FIArea4.A6Crude

namespace Work.FIArea6T

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 0. The Schur (Cauchy–Schwarz) pair-sum bound -/

/-- **The Schur (Cauchy–Schwarz) pair-sum bound.**  For a nonnegative kernel `K` on a finite set `s`
whose rows are bounded by `R` wherever `a ≠ 0` and whose columns are bounded by `R` wherever
`b ≠ 0`, the `K`-weighted pair sum of two nonnegative functions is at most
`R √(Σ a²) √(Σ b²)`. -/
theorem pair_sum_schur {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ)
    (K : ι → ι → ℝ) (R : ℝ)
    (hK : ∀ x y, 0 ≤ K x y) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (hR : 0 ≤ R)
    (hrow : ∀ x ∈ s, a x ≠ 0 → ∑ y ∈ s, K x y ≤ R)
    (hcol : ∀ y ∈ s, b y ≠ 0 → ∑ x ∈ s, K x y ≤ R) :
    ∑ x ∈ s, ∑ y ∈ s, a x * b y * K x y
      ≤ R * Real.sqrt (∑ x ∈ s, a x ^ 2) * Real.sqrt (∑ x ∈ s, b x ^ 2) := by
  classical
  have hSa : 0 ≤ ∑ x ∈ s, a x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hSb : 0 ≤ ∑ x ∈ s, b x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hA : (∑ x ∈ s, ∑ y ∈ s, a x ^ 2 * K x y) ≤ R * (∑ x ∈ s, a x ^ 2) := by
    calc (∑ x ∈ s, ∑ y ∈ s, a x ^ 2 * K x y)
        = ∑ x ∈ s, a x ^ 2 * (∑ y ∈ s, K x y) := by
          apply Finset.sum_congr rfl; intro x _
          rw [Finset.mul_sum]
      _ ≤ ∑ x ∈ s, a x ^ 2 * R := by
          apply Finset.sum_le_sum; intro x hx
          by_cases hax : a x = 0
          · simp [hax]
          · exact mul_le_mul_of_nonneg_left (hrow x hx hax) (sq_nonneg _)
      _ = (∑ x ∈ s, a x ^ 2) * R := by rw [Finset.sum_mul]
      _ = R * (∑ x ∈ s, a x ^ 2) := by ring
  have hB : (∑ x ∈ s, ∑ y ∈ s, b y ^ 2 * K x y) ≤ R * (∑ x ∈ s, b x ^ 2) := by
    rw [Finset.sum_comm]
    calc (∑ y ∈ s, ∑ x ∈ s, b y ^ 2 * K x y)
        = ∑ y ∈ s, b y ^ 2 * (∑ x ∈ s, K x y) := by
          apply Finset.sum_congr rfl; intro y _
          rw [Finset.mul_sum]
      _ ≤ ∑ y ∈ s, b y ^ 2 * R := by
          apply Finset.sum_le_sum; intro y hy
          by_cases hby : b y = 0
          · simp [hby]
          · exact mul_le_mul_of_nonneg_left (hcol y hy hby) (sq_nonneg _)
      _ = (∑ y ∈ s, b y ^ 2) * R := by rw [Finset.sum_mul]
      _ = R * (∑ y ∈ s, b y ^ 2) := by ring
  have hAnn : 0 ≤ ∑ x ∈ s, ∑ y ∈ s, a x ^ 2 * K x y :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hK x y)
  have hBnn : 0 ≤ ∑ x ∈ s, ∑ y ∈ s, b y ^ 2 * K x y :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (sq_nonneg _) (hK x y)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (s.product s)
    (fun p : ι × ι => Real.sqrt (K p.1 p.2) * a p.1)
    (fun p : ι × ι => Real.sqrt (K p.1 p.2) * b p.2)
  have hflat : (∑ p ∈ s.product s, (Real.sqrt (K p.1 p.2) * a p.1)
        * (Real.sqrt (K p.1 p.2) * b p.2))
      = ∑ x ∈ s, ∑ y ∈ s, a x * b y * K x y := by
    trans ∑ x ∈ s, ∑ y ∈ s,
        (Real.sqrt (K x y) * a x) * (Real.sqrt (K x y) * b y)
    · exact Finset.sum_product s s _
    · apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      rw [show Real.sqrt (K x y) * a x * (Real.sqrt (K x y) * b y)
            = (Real.sqrt (K x y)) ^ 2 * (a x * b y) by ring, Real.sq_sqrt (hK x y)]
      ring
  have hF2 : (∑ p ∈ s.product s, (Real.sqrt (K p.1 p.2) * a p.1) ^ 2)
      = ∑ x ∈ s, ∑ y ∈ s, a x ^ 2 * K x y := by
    trans ∑ x ∈ s, ∑ y ∈ s, (Real.sqrt (K x y) * a x) ^ 2
    · exact Finset.sum_product s s _
    · apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      rw [mul_pow, Real.sq_sqrt (hK x y)]; ring
  have hG2 : (∑ p ∈ s.product s, (Real.sqrt (K p.1 p.2) * b p.2) ^ 2)
      = ∑ x ∈ s, ∑ y ∈ s, b y ^ 2 * K x y := by
    trans ∑ x ∈ s, ∑ y ∈ s, (Real.sqrt (K x y) * b y) ^ 2
    · exact Finset.sum_product s s _
    · apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      rw [mul_pow, Real.sq_sqrt (hK x y)]; ring
  have hLnn : 0 ≤ ∑ x ∈ s, ∑ y ∈ s, a x * b y * K x y :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (ha x) (hb y)) (hK x y)
  have hWnn : 0 ≤ R * Real.sqrt (∑ x ∈ s, a x ^ 2) * Real.sqrt (∑ x ∈ s, b x ^ 2) :=
    mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hsq : ((∑ x ∈ s, ∑ y ∈ s, a x * b y * K x y)) ^ 2
      ≤ (R * Real.sqrt (∑ x ∈ s, a x ^ 2) * Real.sqrt (∑ x ∈ s, b x ^ 2)) ^ 2 := by
    have h1 : (R * Real.sqrt (∑ x ∈ s, a x ^ 2) * Real.sqrt (∑ x ∈ s, b x ^ 2)) ^ 2
        = R ^ 2 * (∑ x ∈ s, a x ^ 2) * (∑ x ∈ s, b x ^ 2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hSa, Real.sq_sqrt hSb]
    rw [h1]
    calc ((∑ x ∈ s, ∑ y ∈ s, a x * b y * K x y)) ^ 2
        = (∑ p ∈ s.product s, (Real.sqrt (K p.1 p.2) * a p.1)
            * (Real.sqrt (K p.1 p.2) * b p.2)) ^ 2 := by rw [hflat]
      _ ≤ (∑ p ∈ s.product s, (Real.sqrt (K p.1 p.2) * a p.1) ^ 2)
            * (∑ p ∈ s.product s, (Real.sqrt (K p.1 p.2) * b p.2) ^ 2) := hCS
      _ = (∑ x ∈ s, ∑ y ∈ s, a x ^ 2 * K x y) * (∑ x ∈ s, ∑ y ∈ s, b y ^ 2 * K x y) := by
          rw [hF2, hG2]
      _ ≤ (R * (∑ x ∈ s, a x ^ 2)) * (R * (∑ x ∈ s, b x ^ 2)) :=
          mul_le_mul hA hB hBnn (mul_nonneg hR hSa)
      _ = R ^ 2 * (∑ x ∈ s, a x ^ 2) * (∑ x ∈ s, b x ^ 2) := by ring
  calc ∑ x ∈ s, ∑ y ∈ s, a x * b y * K x y
      = Real.sqrt ((∑ x ∈ s, ∑ y ∈ s, a x * b y * K x y) ^ 2) := (Real.sqrt_sq hLnn).symm
    _ ≤ Real.sqrt ((R * Real.sqrt (∑ x ∈ s, a x ^ 2) * Real.sqrt (∑ x ∈ s, b x ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = R * Real.sqrt (∑ x ∈ s, a x ^ 2) * Real.sqrt (∑ x ∈ s, b x ^ 2) := Real.sqrt_sq hWnn

/-! ## 1. The row/column count for the polar box -/

/-- For a fixed polar squarefree-norm `z₁` and modulus `d ≥ 1`, at most
`3(2(⌈4πθN⌉₊/(4d)+1)+1)` points `z₂` of the inner box satisfy `InPolarBox z₂ ∧ 4d ∣ |Δ(z₁,z₂)|`:
the values of `Δ(z₁,·)` are the multiples of `4d` inside `[-⌈4πθN⌉₊, ⌈4πθN⌉₊]`, and each such
value is taken at most three times (`polar_fibre_card`). -/
lemma polar_count_dvd_le (Pa : Work.FITop.Params) (φ : ℝ) {z1 : GaussianInt}
    (h1 : Work.FITop4.InPolarBox Pa φ z1) (hsf : Squarefree (Work.FIPlan.gnorm z1))
    (d : ℕ) (hd : 1 ≤ d) :
    (((Work.FITop.boxN Pa).filter (fun z2 => Work.FITop4.InPolarBox Pa φ z2
        ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2)).card : ℝ)
      ≤ 3 * (2 * ((⌈4 * Real.pi * Pa.θ * Pa.N⌉₊ : ℝ) / (4 * (d : ℝ)) + 1) + 1) := by
  classical
  set M : ℕ := ⌈4 * Real.pi * Pa.θ * Pa.N⌉₊ with hM
  set T : Finset ℤ := (Finset.Icc (-(M:ℤ)) (M:ℤ)).filter (fun m => (4*(d:ℤ)) ∣ m) with hT
  have hsubset :
      (Work.FITop.boxN Pa).filter (fun z2 => Work.FITop4.InPolarBox Pa φ z2
          ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2)
        ⊆ T.biUnion (fun m => (Work.FITop.boxN Pa).filter
            (fun z2 => Work.FITop4.InPolarBox Pa φ z2 ∧ Work.FIPlan.Delta z1 z2 = m)) := by
    intro z2 hz2
    rw [Finset.mem_filter] at hz2
    obtain ⟨hz2box, hb2, hdvd⟩ := hz2
    have hbnd := polar_absDelta_le Pa φ h1 hb2
    have hMb : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ (M : ℝ) := by
      rw [hM]; exact le_trans hbnd (Nat.le_ceil _)
    have hdvdZ : (4*(d:ℤ)) ∣ Work.FIPlan.Delta z1 z2 := by
      rw [← Int.dvd_natAbs]; exact_mod_cast hdvd
    have hAbs : ((Work.FIPlan.Delta z1 z2).natAbs : ℤ) ≤ (M:ℤ) := by
      have : ((Work.FIPlan.Delta z1 z2).natAbs : ℝ) ≤ (M:ℝ) := by
        rw [show (Work.FIPlan.Delta z1 z2).natAbs = Work.FIPlan.absDelta z1 z2 from rfl]
        exact hMb
      exact_mod_cast this
    have hmem : Work.FIPlan.Delta z1 z2 ∈ T := by
      rw [hT, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, hdvdZ⟩
      · rw [Int.natCast_natAbs] at hAbs; exact (abs_le.mp hAbs).1
      · rw [Int.natCast_natAbs] at hAbs; exact (abs_le.mp hAbs).2
    rw [Finset.mem_biUnion]
    exact ⟨_, hmem, by rw [Finset.mem_filter]; exact ⟨hz2box, hb2, rfl⟩⟩
  have hdisj : (T : Set ℤ).PairwiseDisjoint
      (fun m => (Work.FITop.boxN Pa).filter (fun z2 => Work.FITop4.InPolarBox Pa φ z2
          ∧ Work.FIPlan.Delta z1 z2 = m)) := by
    intro m _ m' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro z2 hz hz'
    rw [Finset.mem_filter] at hz hz'
    exact hne (hz.2.2.symm.trans hz'.2.2)
  have hfiber : ∀ m ∈ T, (((Work.FITop.boxN Pa).filter
      (fun z2 => Work.FITop4.InPolarBox Pa φ z2 ∧ Work.FIPlan.Delta z1 z2 = m)).card : ℝ) ≤ 3 :=
    fun m _ => polar_fibre_card Pa φ h1 hsf m
  have hcardT : ((T.card : ℕ) : ℝ) ≤ 2 * ((M:ℝ) / (4*(d:ℝ)) + 1) + 1 := by
    set K : ℕ := ⌈(M:ℝ) / (4*(d:ℝ))⌉₊ with hK
    have hceil : (K:ℝ) ≤ (M:ℝ)/(4*(d:ℝ)) + 1 := by
      rw [hK]; exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
    have hsub : T ⊆ (Finset.Icc (-(K:ℤ)) (K:ℤ)).image (fun k : ℤ => (4*(d:ℤ)) * k) := by
      intro m hm
      rw [hT, Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨hlo, hhi⟩, hdvd⟩ := hm
      obtain ⟨k, hk⟩ := hdvd
      refine Finset.mem_image.mpr ⟨k, ?_, hk.symm⟩
      rw [Finset.mem_Icc]
      have hmabs : (m.natAbs : ℝ) ≤ (M:ℝ) := by
        have h1' : |m| ≤ (M:ℤ) := by rw [abs_le]; exact ⟨hlo, hhi⟩
        have h3 : (m.natAbs : ℤ) ≤ (M:ℤ) := by rw [Int.natCast_natAbs]; exact h1'
        exact_mod_cast h3
      have hkabs : ((k.natAbs : ℕ) : ℝ) * (4*(d:ℝ)) ≤ (M:ℝ) := by
        have h4 : m.natAbs = (4*d) * k.natAbs := by
          have hh : m = ((4*d : ℕ) : ℤ) * k := by rw [hk]; push_cast; ring
          rw [hh, Int.natAbs_mul, Int.natAbs_natCast]
        have h5 : ((m.natAbs : ℕ) : ℝ) ≤ (M:ℝ) := hmabs
        rw [h4] at h5; push_cast at h5; nlinarith [h5]
      have hkK : k.natAbs ≤ K := by
        rw [hK]
        have h5 : ((k.natAbs : ℕ) : ℝ) ≤ (M:ℝ) / (4*(d:ℝ)) := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < 4*(d:ℝ))]
          nlinarith [hkabs]
        exact_mod_cast le_trans h5 (Nat.le_ceil _)
      constructor <;> omega
    have hcardIcc : ((Finset.Icc (-(K:ℤ)) (K:ℤ)).card : ℝ) = 2*(K:ℝ)+1 := by
      rw [Int.card_Icc]
      have h0 : (0:ℤ) ≤ 2*(K:ℤ)+1 := by omega
      have h7 : (((K:ℤ) + 1 - (-(K:ℤ))).toNat : ℤ) = 2*(K:ℤ)+1 := by
        rw [show ((K:ℤ) + 1 - (-(K:ℤ))) = 2*(K:ℤ)+1 from by ring, Int.toNat_of_nonneg h0]
      exact_mod_cast h7
    calc ((T.card:ℕ):ℝ)
        ≤ ((((Finset.Icc (-(K:ℤ)) (K:ℤ)).image (fun k : ℤ => (4*(d:ℤ)) * k)).card:ℕ):ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((((Finset.Icc (-(K:ℤ)) (K:ℤ))).card:ℕ):ℝ) := by
          exact_mod_cast Finset.card_image_le
      _ = 2*(K:ℝ)+1 := hcardIcc
      _ ≤ 2*((M:ℝ)/(4*(d:ℝ))+1)+1 := by linarith [hceil]
  calc (((Work.FITop.boxN Pa).filter (fun z2 => Work.FITop4.InPolarBox Pa φ z2
        ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2)).card : ℝ)
      ≤ ((T.biUnion (fun m => (Work.FITop.boxN Pa).filter
          (fun z2 => Work.FITop4.InPolarBox Pa φ z2
            ∧ Work.FIPlan.Delta z1 z2 = m))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
    _ = ∑ m ∈ T, (((Work.FITop.boxN Pa).filter (fun z2 => Work.FITop4.InPolarBox Pa φ z2
          ∧ Work.FIPlan.Delta z1 z2 = m)).card : ℝ) := by
        rw [Finset.card_biUnion hdisj]; push_cast; ring
    _ ≤ ∑ _m ∈ T, (3:ℝ) := Finset.sum_le_sum hfiber
    _ = 3 * (T.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 3 * (2 * ((M:ℝ) / (4*(d:ℝ)) + 1) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith [hcardT]
    _ = 3 * (2 * ((⌈4 * Real.pi * Pa.θ * Pa.N⌉₊ : ℝ) / (4*(d:ℝ)) + 1) + 1) := by rw [hM]

/-- `PhiLocC` is symmetric in its two arguments. -/
lemma PhiLocC_comm (x y : GaussianInt) :
    Work.FIArea6.PhiLocC x y = Work.FIArea6.PhiLocC y x := by
  rw [Work.FIArea6.PhiLocC, Work.FIArea6.PhiLocC, Work.FIArea6.absDelta_comm x y]

/-- **The row bound of the L²-Schur argument.**  For `z₁` in the polar box with squarefree norm,
the `PhiLocC`-weighted row over the inner box is at most `105 (θN + 1) log(2+N)`. -/
theorem row_phi_le_polar (Pa : Work.FITop.Params) (φ : ℝ) {z1 : GaussianInt}
    (h1 : Work.FITop4.InPolarBox Pa φ z1) (hsf : Squarefree (Work.FIPlan.gnorm z1)) :
    ∑ z2 ∈ Work.FITop.boxN Pa,
        (if Work.FITop4.InPolarBox Pa φ z2 then Work.FIArea6.PhiLocC z1 z2 else 0)
      ≤ 105 * (Pa.θ * Pa.N + 1) * Real.log (2 + Pa.N) := by
  classical
  have hD1 : 1 ≤ Work.FIArea6.Dmod Pa := by
    rw [Work.FIArea6.Dmod]; omega
  -- the modulus `d` of a polar pair is at most `Dmod Pa`
  have hpt : ∀ z2 ∈ Work.FITop.boxN Pa,
      (if Work.FITop4.InPolarBox Pa φ z2 then Work.FIArea6.PhiLocC z1 z2 else 0)
        ≤ ∑ d ∈ Finset.Icc 1 (Work.FIArea6.Dmod Pa),
            (if Work.FITop4.InPolarBox Pa φ z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
              then ((Nat.totient d : ℝ) / (d : ℝ)) else 0) := by
    intro z2 _
    by_cases hb2 : Work.FITop4.InPolarBox Pa φ z2
    · rw [if_pos hb2]
      have hsub : Work.FITop4.Sset z1 z2
          ⊆ (Finset.Icc 1 (Work.FIArea6.Dmod Pa)).filter
              (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2) := by
        intro d hd
        rw [Work.FITop4.Sset, Finset.mem_filter, Finset.mem_Icc] at hd
        obtain ⟨⟨hd1, hd2⟩, hdvd⟩ := hd
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨hd1, ?_⟩, hdvd⟩
        rcases Nat.eq_zero_or_pos (Work.FIPlan.absDelta z1 z2) with h0 | hpos
        · have hI : Work.FIPlan.absDelta z1 z2 / 4 + 1 = 1 := by omega
          rw [hI] at hd2
          have hd_eq : d = 1 := by omega
          rw [hd_eq]; exact hD1
        · have h4d : 4 * d ≤ Work.FIPlan.absDelta z1 z2 := Nat.le_of_dvd hpos hdvd
          have hbnd := polar_absDelta_le Pa φ h1 hb2
          have hle : ((d : ℕ) : ℝ) ≤ Real.pi * Pa.θ * Pa.N := by
            have h4 : ((4 * d : ℕ) : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
              exact_mod_cast h4d
            push_cast at h4
            linarith
          have hceil : d ≤ ⌈Real.pi * Pa.θ * Pa.N⌉₊ := by
            exact_mod_cast le_trans hle (Nat.le_ceil _)
          rw [Work.FIArea6.Dmod]
          omega
      calc (∑ d ∈ Work.FITop4.Sset z1 z2, ((Nat.totient d : ℝ) / (d : ℝ)))
          ≤ ∑ d ∈ (Finset.Icc 1 (Work.FIArea6.Dmod Pa)).filter
              (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
              ((Nat.totient d : ℝ) / (d : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
        _ = ∑ d ∈ Finset.Icc 1 (Work.FIArea6.Dmod Pa),
              (if 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
                ((Nat.totient d : ℝ) / (d : ℝ)) else 0) := by
            rw [Finset.sum_filter]
        _ = ∑ d ∈ Finset.Icc 1 (Work.FIArea6.Dmod Pa),
              (if Work.FITop4.InPolarBox Pa φ z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
                then ((Nat.totient d : ℝ) / (d : ℝ)) else 0) := by
            apply Finset.sum_congr rfl; intro d _
            by_cases hc : Work.FITop4.InPolarBox Pa φ z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
            · rw [if_pos hc, if_pos hc.2]
            · rw [if_neg hc, if_neg (fun h => hc ⟨hb2, h⟩)]
    · rw [if_neg hb2]
      refine Finset.sum_nonneg (fun d _ => ?_)
      by_cases hc : Work.FITop4.InPolarBox Pa φ z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
      · exact absurd hc.1 hb2
      · rw [if_neg hc]
  calc (∑ z2 ∈ Work.FITop.boxN Pa,
        (if Work.FITop4.InPolarBox Pa φ z2 then Work.FIArea6.PhiLocC z1 z2 else 0))
      ≤ ∑ z2 ∈ Work.FITop.boxN Pa, ∑ d ∈ Finset.Icc 1 (Work.FIArea6.Dmod Pa),
            (if Work.FITop4.InPolarBox Pa φ z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
              then ((Nat.totient d : ℝ) / (d : ℝ)) else 0) := Finset.sum_le_sum hpt
    _ = ∑ d ∈ Finset.Icc 1 (Work.FIArea6.Dmod Pa), ∑ z2 ∈ Work.FITop.boxN Pa,
            (if Work.FITop4.InPolarBox Pa φ z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
              then ((Nat.totient d : ℝ) / (d : ℝ)) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 (Work.FIArea6.Dmod Pa), ((Nat.totient d : ℝ) / (d : ℝ)) *
            (((Work.FITop.boxN Pa).filter (fun z2 => Work.FITop4.InPolarBox Pa φ z2
              ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2)).card : ℝ) := by
          apply Finset.sum_congr rfl; intro d _
          have hkey : (∑ z2 ∈ Work.FITop.boxN Pa,
                  (if Work.FITop4.InPolarBox Pa φ z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
                    then ((Nat.totient d : ℝ) / (d : ℝ)) else 0))
              = (∑ z2 ∈ Work.FITop.boxN Pa,
                  (if Work.FITop4.InPolarBox Pa φ z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
                    then (1 : ℝ) else 0)) * ((Nat.totient d : ℝ) / (d : ℝ)) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro z2 _
            by_cases h : Work.FITop4.InPolarBox Pa φ z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
            · rw [if_pos h, if_pos h]; ring
            · rw [if_neg h, if_neg h]; ring
          rw [hkey, Finset.sum_boole]
          ring
    _ ≤ ∑ d ∈ Finset.Icc 1 (Work.FIArea6.Dmod Pa), ((Nat.totient d : ℝ) / (d : ℝ)) *
            (3 * (2 * ((⌈4 * Real.pi * Pa.θ * Pa.N⌉₊ : ℝ) / (4 * (d : ℝ)) + 1) + 1)) := by
          apply Finset.sum_le_sum; intro d hd
          exact mul_le_mul_of_nonneg_left
            (polar_count_dvd_le Pa φ h1 hsf d (Finset.mem_Icc.mp hd).1) (by positivity)
    _ ≤ 105 * (Pa.θ * Pa.N + 1) * Real.log (2 + Pa.N) := Work.FIArea6.sum_d_bound Pa

/-- The column analogue of `row_phi_le_polar`, by symmetry of `absDelta`. -/
theorem col_phi_le_polar (Pa : Work.FITop.Params) (φ : ℝ) {z2 : GaussianInt}
    (h2 : Work.FITop4.InPolarBox Pa φ z2) (hsf : Squarefree (Work.FIPlan.gnorm z2)) :
    ∑ z1 ∈ Work.FITop.boxN Pa,
        (if Work.FITop4.InPolarBox Pa φ z1 then Work.FIArea6.PhiLocC z1 z2 else 0)
      ≤ 105 * (Pa.θ * Pa.N + 1) * Real.log (2 + Pa.N) := by
  have hsym : (∑ z1 ∈ Work.FITop.boxN Pa,
        (if Work.FITop4.InPolarBox Pa φ z1 then Work.FIArea6.PhiLocC z1 z2 else 0))
      = ∑ z1 ∈ Work.FITop.boxN Pa,
        (if Work.FITop4.InPolarBox Pa φ z1 then Work.FIArea6.PhiLocC z2 z1 else 0) := by
    apply Finset.sum_congr rfl; intro z1 _
    by_cases h : Work.FITop4.InPolarBox Pa φ z1
    · rw [if_pos h, if_pos h]; exact PhiLocC_comm z1 z2
    · rw [if_neg h, if_neg h]
  rw [hsym]
  exact row_phi_le_polar Pa φ h2 hsf

/-- The nonnegative kernel of the Schur argument: the indicator of the polar box times `PhiLocC`. -/
def TcutKernel (Pa : Work.FITop.Params) (φ : ℝ) (z1 z2 : GaussianInt) : ℝ :=
  if Work.FITop4.InPolarBox Pa φ z1 ∧ Work.FITop4.InPolarBox Pa φ z2 then
    Work.FIArea6.PhiLocC z1 z2 else 0

lemma TcutKernel_nonneg (Pa : Work.FITop.Params) (φ : ℝ) (z1 z2 : GaussianInt) :
    0 ≤ TcutKernel Pa φ z1 z2 := by
  rw [TcutKernel]; split_ifs with h
  · exact Work.FIArea6.PhiLocC_nonneg z1 z2
  · norm_num

lemma TcutKernel_symm (Pa : Work.FITop.Params) (φ : ℝ) (z1 z2 : GaussianInt) :
    TcutKernel Pa φ z1 z2 = TcutKernel Pa φ z2 z1 := by
  rw [TcutKernel, TcutKernel]
  by_cases h : Work.FITop4.InPolarBox Pa φ z1 ∧ Work.FITop4.InPolarBox Pa φ z2
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩, PhiLocC_comm]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩)]

/-- **The pointwise bound for a single summand of the (10.13) form.** -/
lemma summand_norm_le (Pa : Work.FITop.Params)
    (cut : GaussianInt → GaussianInt → ℕ → ℝ) (u v : GaussianInt → ℂ) (φ : ℝ)
    (hcut : ∀ z1 z2 d, |cut z1 z2 d| ≤ 1) (hθ : Pa.θ ≤ 1) (hN : 1 ≤ Pa.N)
    (hu : ∀ z, u z ≠ 0 → Work.FITop4.InPolarBox Pa φ z ∧ Squarefree (Work.FIPlan.gnorm z))
    (hv : ∀ z, v z ≠ 0 → Work.FITop4.InPolarBox Pa φ z ∧ Squarefree (Work.FIPlan.gnorm z))
    (z1 z2 : GaussianInt) :
    ‖(if Work.FIPlan.GaussCoprime z1 z2 then
        (u z1 * star (v z2)) *
          ((∑ d ∈ Work.FITop4.Sset z1 z2,
              ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
      else 0)‖
      ≤ ‖u z1‖ * ‖v z2‖ * TcutKernel Pa φ z1 z2 * (4 * Real.log (2 + Pa.N)) := by
  classical
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos hc]
    by_cases hb : Work.FITop4.InPolarBox Pa φ z1 ∧ Work.FITop4.InPolarBox Pa φ z2
    · rw [TcutKernel, if_pos hb]
      rw [norm_mul, norm_mul, norm_star]
      have hinner := InnerSum_le Pa φ cut hcut hθ hN hb.1 hb.2
      calc ‖u z1‖ * ‖v z2‖ * ‖(∑ d ∈ Work.FITop4.Sset z1 z2,
              ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℂ)‖
          ≤ ‖u z1‖ * ‖v z2‖ * (Work.FIArea6.PhiLocC z1 z2 * (4 * Real.log (2 + Pa.N))) :=
            mul_le_mul_of_nonneg_left hinner (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = ‖u z1‖ * ‖v z2‖ * Work.FIArea6.PhiLocC z1 z2 * (4 * Real.log (2 + Pa.N)) := by ring
    · rw [TcutKernel, if_neg hb]
      have hz : u z1 = 0 ∨ v z2 = 0 := by
        by_contra hcon
        rw [not_or] at hcon
        exact hb ⟨(hu z1 hcon.1).1, (hv z2 hcon.2).1⟩
      rcases hz with h0 | h0
      · rw [h0]; simp
      · rw [h0]; simp
  · rw [if_neg hc]
    simp only [norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (TcutKernel_nonneg Pa φ z1 z2))
      (by have h := Real.log_nonneg (by linarith [hN] : (1:ℝ) ≤ 2 + Pa.N); linarith)

/-- **T2 — the L² Schur bound for the cut form on the polar box (the heart of the τ-removal).**

Let `u, v` vanish off the polar box (5.14) and off the squarefree-norm points, let the cut satisfy
`|cut| ≤ 1`, `θ ≤ 1`, `N ≥ 3`.  Then the sesquilinear form `Work.FIArea6T.TcutBil` of the
(10.13) expansion (design `FIArea6/AREA6_CONTRACT_LEAD.md` §3.2, T2) is bounded by
`10^4 · θN · log²(2+N) · ‖u‖₂ ‖v‖₂` over the inner box `boxN Pa`.

(The design quotes the constant `400`; its own arithmetic for the row bound
(`2·8·6π·2.4 ≈ 724`) is inconsistent with that, and `400` is reachable only with a tight split of
the small-`θ` regime.  Since the constant is absorbed by `Pa.θ ≤ 1` in the final
`Work.FITop4.TauRemoval6`, this statement uses the safe explicit constant `10^4`.)

Auxiliary facts are in `Submission.Work.FIArea6T.Support` (**do not** import
`Submission.Work.FIArea6.Ucut_elem_bound6`/`fibre_bound`: `Submission.Work.FIArea6.PolarCoeff` is
currently unbuildable, and the four facts needed are restated in `Support`):
`Work.FIArea6T.polar_absDelta_le`, `Work.FIArea6T.polar_fibre_card`,
`Work.FIArea6T.logFac6_abs_le`, `Work.FIArea6T.ratioSym_abs_le_one`.

Proof plan.
1. *Pointwise.*  For a pair, `|Σ_{d ∈ Sset z₁ z₂} (φ(d)/d)·cut·χ·logFac6| ≤ |logFac6|·c(z₁,z₂)`
   where `c z₁ z₂ := (Work.FITop4.Sset z₁ z₂).card` (`φ(d)/d ≤ 1`, `|χ| ≤ 1`), and
   `|logFac6 z₁ z₂| ≤ 4 log(2+N)` (`logFac6_abs_le`, using `|z|² ≤ (1+θ)N ≤ 2N` from the polar
   box and `θ ≤ 1`).
2. *Row/column count.*  For `z₁` in the polar box with squarefree norm, split at `Δ = 0`: the
   `Δ = 0` fibre has at most `3` points (`polar_fibre_card`, `m = 0`), each contributing `c = 1`;
   for `Δ ≠ 0` one has `d ≤ πθN` (as `4d ≤ |Δ| ≤ 4πθN`), and for fixed `d` the number of `z₂` with
   `4d ∣ Δ ≠ 0` is at most `3 · 2⌊πθN/d⌋` (fibre bound at each nonzero multiple of `4d`).  A
   convenient form of the resulting row bound is
   `Σ_{z₂ ∈ boxN} K z₁ z₂ ≤ 3 + 6πθN(1 + log(1+πθN))` for the nonnegative kernel
   `K z₁ z₂ = 1[InPolarBox z₁]·1[InPolarBox z₂]·c(z₁,z₂)`; a slightly weaker explicit bound
   (e.g. `10 + 18πθN·(1+log(1+πθN))`) is also enough for the constant `10^4`.  By
   `Work.FIArea4.absDelta_comm` the same bound holds for columns.
3. *Schur.*  Cauchy–Schwarz (flatten the double sum over `(boxN).product (boxN)`):
   `Σ K‖u‖‖v‖ ≤ √(Σ K‖u‖²)·√(Σ K‖v‖²) ≤ rowmax·‖u‖₂‖v‖₂`; each quadratic form is bounded by the
   row bound, `Σ_{z₁} ‖u z₁‖² (Σ_{z₂} K z₁ z₂) ≤ rowmax·Σ‖u‖²`.  The symmetric AM–GM template is
   `Work.FIArea6.Rw_pair_sum_le`.
4. *Constant.*  If `πθN < 1` then for every polar pair `|Δ| ≤ 4πθN < 4`, so `4d ∣ |Δ|` forces
   `Δ = 0`, whence `logFac6 = 0` and `TcutBil = 0`: the bound is trivial.  Otherwise
   `θN ≥ 1/π`, and `1 + log(1+πθN) ≤ 3 log(2+N)` (as `πθN ≤ (2+N)²` and `log(2+N) ≥ 1`), so
   the row bound is at most `3·(πθN) + 18πθN log(2+N) ≤ 60θN log(2+N)`, and
   `2·4·log(2+N)·60θN log(2+N) = 480θN log²(2+N) < 10^4 θN log²(2+N)`.

Suggested namespace: `Work.FIArea6T`. -/
theorem TcutBil_le_polar (Pa : Work.FITop.Params)
    (cut : GaussianInt → GaussianInt → ℕ → ℝ) (u v : GaussianInt → ℂ) (φ : ℝ)
    (hcut : ∀ z1 z2 d, |cut z1 z2 d| ≤ 1)
    (hu : ∀ z, u z ≠ 0 → Work.FITop4.InPolarBox Pa φ z ∧ Squarefree (Work.FIPlan.gnorm z))
    (hv : ∀ z, v z ≠ 0 → Work.FITop4.InPolarBox Pa φ z ∧ Squarefree (Work.FIPlan.gnorm z))
    (hθ : Pa.θ ≤ 1) (hN : 3 ≤ Pa.N) :
    ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut u v‖
      ≤ 10 ^ 4 * Pa.θ * Pa.N * (Real.log (2 + Pa.N)) ^ 2
          * Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖u z‖ ^ 2)
          * Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖v z‖ ^ 2) := by
  classical
  set L : ℝ := Real.log (2 + Pa.N) with hLdef
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hN0 : (0 : ℝ) ≤ Pa.N := le_trans zero_le_one hN1
  have hθ0 : (0 : ℝ) ≤ Pa.θ := Pa.hθ0.le
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    have h3 : (3:ℝ) ≤ 2 + Pa.N := by linarith
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 3) h3
    have h2 : (1:ℝ) < Real.log 3 := by
      have hh := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at hh
    linarith
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL1
  set Rw : ℝ := 105 * (Pa.θ * Pa.N + 1) * L with hRwdef
  have hRw0 : 0 ≤ Rw := by
    rw [hRwdef]
    have h1 : 0 ≤ Pa.θ * Pa.N + 1 := by linarith [mul_nonneg hθ0 hN0]
    exact mul_nonneg (mul_nonneg (by norm_num) h1) hL0
  -- ## Step 1: the trivial small-`θ` regime
  by_cases hcase : (1 : ℝ) ≤ Real.pi * Pa.θ * Pa.N
  · -- ## Step 2: the main chain
    -- the pointwise bound on the whole double sum
    have hstep : ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut u v‖
        ≤ 2 * (4 * L) * (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
              ‖u z1‖ * ‖v z2‖ * TcutKernel Pa φ z1 z2) := by
      have hEq : Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut u v
          = 2 * ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
              (if Work.FIPlan.GaussCoprime z1 z2 then
                (u z1 * star (v z2)) *
                  ((∑ d ∈ Work.FITop4.Sset z1 z2,
                      ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                        * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
              else 0) := rfl
      rw [hEq, norm_mul]
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2]
      have hsum1 : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            ‖u z1‖ * ‖v z2‖ * TcutKernel Pa φ z1 z2 * (4 * L))
          = (4 * L) * ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
              (‖u z1‖ * ‖v z2‖ * TcutKernel Pa φ z1 z2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro z1 _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro z2 _; ring
      calc 2 * ‖∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
              (if Work.FIPlan.GaussCoprime z1 z2 then
                (u z1 * star (v z2)) *
                  ((∑ d ∈ Work.FITop4.Sset z1 z2,
                      ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                        * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
              else 0)‖
          ≤ 2 * ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
              ‖u z1‖ * ‖v z2‖ * TcutKernel Pa φ z1 z2 * (4 * L) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            calc ‖∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
                  (if Work.FIPlan.GaussCoprime z1 z2 then
                    (u z1 * star (v z2)) *
                      ((∑ d ∈ Work.FITop4.Sset z1 z2,
                          ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                            * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
                  else 0)‖
                ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ‖∑ z2 ∈ Work.FITop.boxN Pa,
                    (if Work.FIPlan.GaussCoprime z1 z2 then
                      (u z1 * star (v z2)) *
                        ((∑ d ∈ Work.FITop4.Sset z1 z2,
                            ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                              * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
                    else 0)‖ := norm_sum_le _ _
              _ ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
                    ‖u z1‖ * ‖v z2‖ * TcutKernel Pa φ z1 z2 * (4 * L) := by
                  apply Finset.sum_le_sum; intro z1 _
                  apply le_trans (norm_sum_le _ _)
                  apply Finset.sum_le_sum; intro z2 _
                  exact summand_norm_le Pa cut u v φ hcut hθ Pa.hN1 hu hv z1 z2
        _ = 2 * ((4 * L) * ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
              (‖u z1‖ * ‖v z2‖ * TcutKernel Pa φ z1 z2)) := by rw [hsum1]
        _ = 2 * (4 * L) * (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
              ‖u z1‖ * ‖v z2‖ * TcutKernel Pa φ z1 z2) := by ring
    -- the Schur bound
    have hschur : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          ‖u z1‖ * ‖v z2‖ * TcutKernel Pa φ z1 z2)
        ≤ Rw * Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖u z‖ ^ 2)
            * Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖v z‖ ^ 2) := by
      refine pair_sum_schur (Work.FITop.boxN Pa) (fun z => ‖u z‖) (fun z => ‖v z‖)
        (TcutKernel Pa φ) Rw (fun x y => TcutKernel_nonneg Pa φ x y)
        (fun x => norm_nonneg _) (fun x => norm_nonneg _) hRw0 ?_ ?_
      · intro x _ hax
        have hux : u x ≠ 0 := fun h0 => hax (by rw [h0]; simp)
        obtain ⟨hbx, hsfx⟩ := hu x hux
        have hker : ∑ y ∈ Work.FITop.boxN Pa, TcutKernel Pa φ x y
            = ∑ y ∈ Work.FITop.boxN Pa,
                (if Work.FITop4.InPolarBox Pa φ y then Work.FIArea6.PhiLocC x y else 0) := by
          apply Finset.sum_congr rfl; intro y _
          rw [TcutKernel]
          by_cases hy : Work.FITop4.InPolarBox Pa φ y
          · rw [if_pos ⟨hbx, hy⟩, if_pos hy]
          · rw [if_neg (fun h => hy h.2), if_neg hy]
        rw [hker]
        exact row_phi_le_polar Pa φ hbx hsfx
      · intro y _ hby
        have hvy : v y ≠ 0 := fun h0 => hby (by rw [h0]; simp)
        obtain ⟨hby', hsfy⟩ := hv y hvy
        have hker : ∑ x ∈ Work.FITop.boxN Pa, TcutKernel Pa φ x y
            = ∑ x ∈ Work.FITop.boxN Pa,
                (if Work.FITop4.InPolarBox Pa φ x then Work.FIArea6.PhiLocC x y else 0) := by
          apply Finset.sum_congr rfl; intro x _
          rw [TcutKernel]
          by_cases hx : Work.FITop4.InPolarBox Pa φ x
          · rw [if_pos ⟨hx, hby'⟩, if_pos hx]
          · rw [if_neg (fun h => hx h.1), if_neg hx]
        rw [hker]
        exact col_phi_le_polar Pa φ hby' hsfy
    -- the constant
    have hθN0 : 0 ≤ Pa.θ * Pa.N := mul_nonneg hθ0 hN0
    have hθN : Pa.θ * Pa.N + 1 ≤ 5 * (Pa.θ * Pa.N) := by
      have hpi4 : Real.pi ≤ 4 := Real.pi_lt_four.le
      have h4 : Real.pi * (Pa.θ * Pa.N) ≤ 4 * (Pa.θ * Pa.N) :=
        mul_le_mul_of_nonneg_right hpi4 hθN0
      linarith
    have hkey : 2 * (4 * L) * Rw ≤ 10 ^ 4 * Pa.θ * Pa.N * L ^ 2 := by
      rw [hRwdef]
      have h840 : 2 * (4 * L) * (105 * (Pa.θ * Pa.N + 1) * L)
          = 840 * (Pa.θ * Pa.N + 1) * L ^ 2 := by ring
      rw [h840]
      have hθN0 : 0 ≤ Pa.θ * Pa.N := mul_nonneg hθ0 hN0
      nlinarith [hθN, hL0, hθN0, sq_nonneg L]
    calc ‖Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut u v‖
        ≤ 2 * (4 * L) * (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
              ‖u z1‖ * ‖v z2‖ * TcutKernel Pa φ z1 z2) := hstep
      _ ≤ 2 * (4 * L) * (Rw * Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖u z‖ ^ 2)
              * Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖v z‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left hschur (by nlinarith [hL0])
      _ = (2 * (4 * L) * Rw) * (Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖u z‖ ^ 2)
              * Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖v z‖ ^ 2)) := by ring
      _ ≤ (10 ^ 4 * Pa.θ * Pa.N * L ^ 2) * (Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖u z‖ ^ 2)
              * Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖v z‖ ^ 2)) :=
            mul_le_mul_of_nonneg_right hkey
              (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = 10 ^ 4 * Pa.θ * Pa.N * L ^ 2
            * Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖u z‖ ^ 2)
            * Real.sqrt (∑ z ∈ Work.FITop.boxN Pa, ‖v z‖ ^ 2) := by ring
  · -- ## Step 3: the small-`θ` regime: `TcutBil` vanishes
    have hsmall : Real.pi * Pa.θ * Pa.N < 1 := lt_of_not_ge hcase
    have hzero : Work.FIArea6T.TcutBil (Work.FITop.radN Pa) cut u v = 0 := by
      rw [Work.FIArea6T.TcutBil]
      have h0 : (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              (if Work.FIPlan.GaussCoprime z1 z2 then
                (u z1 * star (v z2)) *
                  ((∑ d ∈ Work.FITop4.Sset z1 z2,
                      ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                        * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℂ)
              else 0)) = 0 := by
        apply Finset.sum_eq_zero; intro z1 _
        apply Finset.sum_eq_zero; intro z2 _
        by_cases hc : Work.FIPlan.GaussCoprime z1 z2
        · rw [if_pos hc]
          by_cases hb : Work.FITop4.InPolarBox Pa φ z1 ∧ Work.FITop4.InPolarBox Pa φ z2
          · have hlt : Work.FIPlan.absDelta z1 z2 < 4 := by
              have hbnd := polar_absDelta_le Pa φ hb.1 hb.2
              have : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) < 4 := by
                nlinarith [hbnd, hsmall]
              exact_mod_cast this
            rw [InnerSum_zero Pa cut hlt, mul_zero]
          · have hz : u z1 = 0 ∨ v z2 = 0 := by
              by_contra hcon
              rw [not_or] at hcon
              exact hb ⟨(hu z1 hcon.1).1, (hv z2 hcon.2).1⟩
            rcases hz with h00 | h00
            · rw [h00]; simp
            · rw [h00]; simp
        · rw [if_neg hc]
      rw [h0, mul_zero]
    rw [hzero, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθ0) hN0)
      (sq_nonneg L)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end

end Work.FIArea6T
