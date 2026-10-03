import Mathlib
import Submission.Work.FIArea6.elem_helpers
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea4.absDelta_le_sector
import Submission.Work.FIArea6.fiber_card_le


/-!
# `Work.FIArea6.pair_phi_average` — the `Φ`-weighted pair average

The pair sum

`Σ_{z₁,z₂ ∈ boxN} [coprime] ‖β z₁‖‖β z₂‖ · Σ_{4d ∣ |Δ(z₁,z₂)|, d ≤ |Δ|/4+1} φ(d)/d`

is bounded by `1.25·10⁶ (θ²N² + N)(log(2+N))⁴`.  The proof has three ingredients:

* **the modular exchange**: the inner `d`-sum is dominated by `Σ_{d ≤ D} [4d ∣ |Δ|] φ(d)/d`
  with `D = ⌈πθN⌉₊ + 1` (the hypothesis `IsBetaCoeff` confines the support to the polar box, so
  `|Δ| ≤ 4πθN` for supported pairs, `absDelta_le_sector`);
* **the row/column bound**: for each modulus `d` and each fixed `z₁` at most
  `3(2⌈4πθN/(4d)⌉+1)` supported `z₂` satisfy `4d ∣ Δ(z₁,z₂)`, because the fibre of
  `z₂ ↦ Δ(z₁,z₂)` is a coset of `ℤ·z₁` (the norm of `z₁` is squarefree on the support) and the
  annulus cuts it in at most three points (`fiber_card_le`);
* **the weighted second moment** `Σ_{z ∈ boxN}‖β z‖² ≤ C(θN+√N+1)(log(2+N))³`
  (`beta_sq_mass_tight`).
-/

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The `Φ`-weight attached to a natural number `m`: `Σ_{4d ∣ m, d ≤ m/4+1} φ(d)/d`. -/
def PhiNat (m : ℕ) : ℝ :=
  ((Finset.Icc 1 (m / 4 + 1)).filter (fun d => 4 * d ∣ m)).sum
    (fun d => ((Nat.totient d : ℝ) / (d : ℝ)))

/-- The `Φ`-weight of a pair, the inner `d`-sum of the statement. -/
def PhiLocC (z1 z2 : GaussianInt) : ℝ :=
  ((Finset.filter (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2)
      (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1))).sum
    (fun d => ((Nat.totient d : ℝ) / (d : ℝ))))

lemma PhiLocC_nonneg (z1 z2 : GaussianInt) : 0 ≤ PhiLocC z1 z2 := by
  rw [PhiLocC]
  exact Finset.sum_nonneg (fun d _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- `‖β z‖ ≤ |γ(|z|²;C)|` on the support — the explicit formula of `IsBetaCoeff`. -/
lemma beta_le_gammaTrunc {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) (z : GaussianInt) :
    ‖β z‖ ≤ |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)| := by
  obtain ⟨q, p, hq0, hq1, -, -, -, hp0, hp1, -, -, -, hform⟩ := hβ
  rw [hform z]
  split_ifs with _
  · have hqp : ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 _) (hp0 _))]
      have h2 : q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) ≤ 1 * 1 :=
        mul_le_mul (hq1 _) (hp1 _) (hp0 _) (by norm_num)
      linarith
    have hmu : ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖ ≤ 1 :=
      Work.FITop3.norm_moebius_le_one _
    have hgn : ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
        = |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    calc ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)
            * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
            * ((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
        = ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ)) : ℂ)‖
            * ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖
            * ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)| := by
          rw [hgn]; gcongr
      _ = |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)| := by ring
  · simp

/-- `γ(n;C) = Σ_{d ∣ n, d ≤ C} μ(d)` is bounded by the divisor count. -/
lemma abs_gammaTrunc_le_tau (C : ℝ) (n : ℕ) :
    |Work.FIPlan.gammaTrunc C n| ≤ ((n.divisors.card : ℕ) : ℝ) :=
  Work.FITop3.abs_gammaTrunc_le C n

/-- `|S| ≤ 200(θ²N + θ√N + 1)`: the support of `β` sits in the polar box. -/
lemma card_support_le (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) :
    (((Work.FITop.boxN Pa).filter (fun z => β z ≠ 0)).card : ℝ)
      ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) := by
  have hsub : (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0)
      ⊆ (Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, (beta_support hβ hz.2).1⟩
  have h1 : (((Work.FITop.boxN Pa).filter (fun z => β z ≠ 0)).card : ℝ)
      ≤ ((Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z)).card := by
    exact_mod_cast Finset.card_le_card hsub
  set A : Finset GaussianInt :=
    (Work.FITop.boxN Pa).filter (fun z => Work.FITop3.InPolarBox Pa φ z) with hA
  set c : ℂ := (Real.sqrt Pa.N : ℂ)
    * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I) with hc
  set ρ : ℝ := 5 * Pa.θ * Real.sqrt Pa.N with hρ
  have hρ0 : 0 ≤ ρ := by
    rw [hρ]
    exact mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le) (Real.sqrt_nonneg _)
  have hdist : ∀ z ∈ A, ‖z.toComplex - c‖ ≤ ρ := by
    intro z hz
    have hbox : Work.FITop3.InPolarBox Pa φ z := by
      rw [hA] at hz
      exact (Finset.mem_filter.mp hz).2
    rw [hc, hρ]
    exact Work.FIArea4.dist_polarBox_le Pa φ z hbox
  have hcard := Work.FIArea4.card_le_of_dist_le A c hρ0 hdist
  have hs0 : 0 ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have hts : 0 ≤ Pa.θ * Real.sqrt Pa.N := mul_nonneg Pa.hθ0.le hs0
  have hsq : (Real.sqrt Pa.N) ^ 2 = Pa.N := Real.sq_sqrt (by linarith [Pa.hN1])
  have hexpand : (2 * ρ + 1) ^ 2
      ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) := by
    rw [hρ]
    nlinarith [sq_nonneg Pa.θ, hs0, hsq, Pa.hθ0.le, hts]
  exact le_trans h1 (le_trans hcard hexpand)

lemma gnorm_mul' (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

/-- **The sector bound**, for supported pairs: `|Δ(z₁,z₂)| ≤ 4πθN`. -/
lemma absDelta_le_sector' (Pa : Work.FITop.Params) {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) (hθ : Pa.θ ≤ 1) {z1 z2 : GaussianInt}
    (h1 : β z1 ≠ 0) (h2 : β z2 ≠ 0) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ 4 * Real.pi * Pa.θ * Pa.N := by
  have hs1 := beta_support hβ h1
  have hs2 := beta_support hβ h2
  have hn1 := beta_support_norm hβ h1
  have hn2 := beta_support_norm hβ h2
  have hsec := Work.FIArea4.absDelta_le_sector Pa φ hs1.1 hs2.1
  have hN1 : (1:ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hN0 : (0:ℝ) ≤ Pa.N := le_trans zero_le_one hN1
  have hθn : (0:ℝ) ≤ Pa.θ := Pa.hθ0.le
  have hg1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := hn1.2
  have hg2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := hn2.2
  have hgn2 : (0:ℝ) ≤ ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hM0 : (0:ℝ) ≤ (1 + Pa.θ) * Pa.N := mul_nonneg (by linarith) hN0
  have hsq : Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)
      * Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul, ← gnorm_mul']
    have hle : ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ≤ ((1 + Pa.θ) * Pa.N) ^ 2 := by
      rw [gnorm_mul', Nat.cast_mul, pow_two]
      exact mul_le_mul hg1 hg2 hgn2 hM0
    calc Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))
        ≤ Real.sqrt (((1 + Pa.θ) * Pa.N) ^ 2) := Real.sqrt_le_sqrt hle
      _ = (1 + Pa.θ) * Pa.N := Real.sqrt_sq hM0
  have h2π : 0 ≤ 2 * Real.pi * Pa.θ :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hθn
  have h2πN : 0 ≤ 2 * Real.pi * Pa.θ * Pa.N := mul_nonneg h2π hN0
  calc ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      ≤ 2 * Real.pi * Pa.θ * Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)
          * Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := hsec
    _ = 2 * Real.pi * Pa.θ * (Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)
          * Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by ring
    _ ≤ 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) := mul_le_mul_of_nonneg_left hsq h2π
    _ ≤ 4 * Real.pi * Pa.θ * Pa.N := by
        have h1θ : (1 + Pa.θ) ≤ 2 := by linarith
        calc 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N)
            = (2 * Real.pi * Pa.θ * Pa.N) * (1 + Pa.θ) := by ring
          _ ≤ (2 * Real.pi * Pa.θ * Pa.N) * 2 := mul_le_mul_of_nonneg_left h1θ h2πN
          _ = 4 * Real.pi * Pa.θ * Pa.N := by ring

/-- The size of the support is at most `200(θ²N+θ√N+1)` (restated as a `Nat` bound). -/
def suppN (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℕ :=
  ((Work.FITop.boxN Pa).filter (fun z => β z ≠ 0)).card

/-- **The row bound.**  For fixed `z₁` in the support and modulus `d`, at most
`3·(2·(⌈4πθN⌉/(4d) + 1) + 1)` supported `z₂` satisfy `4d ∣ |Δ(z₁,z₂)|`. -/
lemma row_le (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) (d : ℕ)
    {z1 : GaussianInt} (hz1 : z1 ∈ Work.FITop.boxN Pa) (hb1 : β z1 ≠ 0) :
    (((Work.FITop.boxN Pa).filter (fun z2 => β z2 ≠ 0 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2)).card : ℝ)
      ≤ 3 * (2 * ((⌈4 * Real.pi * Pa.θ * Pa.N⌉₊ : ℝ) / (4*(d:ℝ)) + 1) + 1) := by
  classical
  have hθ : Pa.θ ≤ 1 := theta_le_one Pa
  set M : ℕ := ⌈4 * Real.pi * Pa.θ * Pa.N⌉₊ with hM
  set T : Finset ℤ := (Finset.Icc (-(M:ℤ)) (M:ℤ)).filter (fun m => (4*(d:ℤ)) ∣ m) with hT
  have hsubset :
      (Work.FITop.boxN Pa).filter (fun z2 => β z2 ≠ 0 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2)
        ⊆ T.biUnion (fun m => (Work.FITop.boxN Pa).filter
            (fun z2 => β z2 ≠ 0 ∧ Work.FIPlan.Delta z1 z2 = m)) := by
    intro z2 hz2
    rw [Finset.mem_filter] at hz2
    obtain ⟨hz2box, hb2, hdvd⟩ := hz2
    have hbnd := absDelta_le_sector' Pa hβ hθ hb1 hb2
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
      (fun m => (Work.FITop.boxN Pa).filter (fun z2 => β z2 ≠ 0 ∧ Work.FIPlan.Delta z1 z2 = m)) := by
    intro m _ m' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro z2 hz hz'
    rw [Finset.mem_filter] at hz hz'
    exact hne (hz.2.2.symm.trans hz'.2.2)
  have hfiber : ∀ m ∈ T, (((Work.FITop.boxN Pa).filter
      (fun z2 => β z2 ≠ 0 ∧ Work.FIPlan.Delta z1 z2 = m)).card : ℝ) ≤ 3 :=
    fun m _ => fiber_card_le Pa φ β hβ z1 hz1 hb1 m
  have hcardT : ((T.card : ℕ) : ℝ) ≤ 2 * ((M:ℝ) / (4*(d:ℝ)) + 1) + 1 := by
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      have hsub : T ⊆ ({0} : Finset ℤ) := by
        intro m hm
        rw [hT, Finset.mem_filter] at hm
        simp only [Finset.mem_singleton, mul_zero] at hm ⊢
        simpa using hm.2
      have h1 : T.card ≤ 1 := by simpa using Finset.card_le_card hsub
      have h2 : ((T.card:ℕ):ℝ) ≤ 1 := by exact_mod_cast h1
      have h4 : (2 * ((M:ℝ) / (4*((0:ℕ):ℝ)) + 1) + 1) = 3 := by norm_num
      rw [h4]; linarith
    · set K : ℕ := ⌈(M:ℝ) / (4*(d:ℝ))⌉₊ with hK
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
          have h1 : |m| ≤ (M:ℤ) := by rw [abs_le]; exact ⟨hlo, hhi⟩
          have h3 : (m.natAbs : ℤ) ≤ (M:ℤ) := by rw [Int.natCast_natAbs]; exact h1
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
  calc (((Work.FITop.boxN Pa).filter
        (fun z2 => β z2 ≠ 0 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2)).card : ℝ)
      ≤ ((T.biUnion (fun m => (Work.FITop.boxN Pa).filter
          (fun z2 => β z2 ≠ 0 ∧ Work.FIPlan.Delta z1 z2 = m))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
    _ = ∑ m ∈ T, (((Work.FITop.boxN Pa).filter
          (fun z2 => β z2 ≠ 0 ∧ Work.FIPlan.Delta z1 z2 = m)).card : ℝ) := by
        rw [Finset.card_biUnion hdisj]; push_cast; ring
    _ ≤ ∑ _m ∈ T, (3:ℝ) := Finset.sum_le_sum hfiber
    _ = 3 * (T.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 3 * (2 * ((M:ℝ) / (4*(d:ℝ)) + 1) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith [hcardT]
    _ = 3 * (2 * ((⌈4 * Real.pi * Pa.θ * Pa.N⌉₊ : ℝ) / (4*(d:ℝ)) + 1) + 1) := by rw [hM]

/-- The modulus weight of the `d`-exchange. -/
def Rw (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) (d : ℕ) : ℝ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    ‖β z1‖ * ‖β z2‖ *
      (if 4 * d ∣ Work.FIPlan.absDelta z1 z2 then (1:ℝ) else 0)

/-- The weighted second moment of `β` over the box. -/
def Vsq (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2

/-- The weighted per-pair `d`-exchange. -/
lemma weighted_PhiLocC_le_dsum (Pa : Work.FITop.Params) {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) (z1 z2 : GaussianInt) :
    ‖β z1‖ * ‖β z2‖ * PhiLocC z1 z2
      ≤ ‖β z1‖ * ‖β z2‖ *
          (∑ d ∈ Finset.Icc 1 (⌈Real.pi * Pa.θ * Pa.N⌉₊ + 1),
            (if 4 * d ∣ Work.FIPlan.absDelta z1 z2 then (Nat.totient d : ℝ) / (d : ℝ) else 0)) := by
  rcases eq_or_ne (β z1) 0 with h1 | h1
  · rw [h1]; simp
  rcases eq_or_ne (β z2) 0 with h2 | h2
  · rw [h2]; simp
  · have hθ : Pa.θ ≤ 1 := theta_le_one Pa
    have hbnd := absDelta_le_sector' Pa hβ hθ h1 h2
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    set D : ℕ := ⌈Real.pi * Pa.θ * Pa.N⌉₊ + 1 with hD
    have hDle : (Work.FIPlan.absDelta z1 z2 / 4 + 1) ≤ D := by
      rw [hD]
      have h1' : (Work.FIPlan.absDelta z1 z2 : ℝ) / 4 ≤ Real.pi * Pa.θ * Pa.N := by linarith
      have h2' : ((Work.FIPlan.absDelta z1 z2 / 4 : ℕ) : ℝ) ≤ Real.pi * Pa.θ * Pa.N :=
        le_trans (Nat.cast_div_le) h1'
      have h3' : Work.FIPlan.absDelta z1 z2 / 4 ≤ ⌈Real.pi * Pa.θ * Pa.N⌉₊ := by
        exact_mod_cast le_trans h2' (Nat.le_ceil _)
      omega
    rw [PhiLocC, ← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun d hd1 hd2 => ?_)
    · simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
      exact ⟨⟨hd.1.1, le_trans hd.1.2 hDle⟩, hd.2⟩
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- `|Δ|` is symmetric. -/
lemma absDelta_comm (z1 z2 : GaussianInt) :
    Work.FIPlan.absDelta z1 z2 = Work.FIPlan.absDelta z2 z1 := by
  have h : Work.FIPlan.Delta z1 z2 = - Work.FIPlan.Delta z2 z1 := by
    rw [Work.FIPlan.Delta, Work.FIPlan.Delta, Zsqrtd.im_mul, Zsqrtd.im_mul]
    simp only [Zsqrtd.re_star, Zsqrtd.im_star]
    ring
  rw [Work.FIPlan.absDelta, Work.FIPlan.absDelta, h, Int.natAbs_neg]

/-- The number of moduli in the `d`-exchange: `⌈πθN⌉₊ + 1`. -/
def Dmod (Pa : Work.FITop.Params) : ℕ := ⌈Real.pi * Pa.θ * Pa.N⌉₊ + 1

end

end Work.FIArea6
