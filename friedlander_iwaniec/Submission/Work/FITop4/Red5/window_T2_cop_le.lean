import Mathlib
import Submission.Work.FITop4.Red5.noncoprime_count_rat
import Submission.Work.FITop4.Red5.sum_Zint_annM_prim_le
import Submission.Work.FITop4.Red5.assembly_helpers
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FIArea6b.sector_tau_sum
import Submission.Work.FITop4.Red5.window_T2_cop_arith

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Local vocabulary

`NoSmallP Pz z` is the predicate "`z` is free of rational primes `≤ Pz`" (the paper's (5.8)
condition).  `t2core`, `t2Bnd`, `t2Phi` are the local shapes in which the `T2`-cop sum and its
per-`z` majorant are organised. -/

/-- `z` is free of rational primes `≤ Pz`. -/
def NoSmallP (Pz : ℕ) (z : GaussianInt) : Prop :=
  ∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ Work.FIPlan.gnorm z

lemma noSmallP_iff (Pa : Work.FITop.Params) (Pz : ℕ) (h : Pa.Pz = Pz) (z : GaussianInt) :
    Work.FITop3.NoSmallPrimes Pa z ↔ NoSmallP Pz z := by
  simp only [Work.FITop3.NoSmallPrimes, NoSmallP, h]

/-- The angular/`Z`-part of the `T2`-cop majorant. -/
def t2core (z : GaussianInt) (mm : ℕ) (w : GaussianInt) : ℝ :=
  2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0:ℝ) else 1)
    * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)

/-- The arithmetic part of the `T2`-cop majorant: `(Π)-freeness · |μ| · τ`. -/
def t2G (Pz : ℕ) (z : GaussianInt) : ℝ :=
  (if NoSmallP Pz z then (1:ℝ) else 0)
    * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
    * ((Work.FIPlan.gnorm z).divisors.card : ℝ)

/-- The full `T2`-cop majorant of a single summand. -/
def t2Bnd (Pz : ℕ) (z : GaussianInt) (mm : ℕ) (w : GaussianInt) : ℝ :=
  t2core z mm w * t2G Pz z

/-- The `(mm,w)`-sum of `t2core`, i.e. the per-`z` count of non-coprime `w`'s weighted by `Z`. -/
def t2Phi (s3 : Finset ℕ) (z : GaussianInt) : ℝ :=
  ∑ mm ∈ s3, ∑ w ∈ wSph mm, t2core z mm w

lemma t2core_nonneg (z : GaussianInt) (mm : ℕ) (w : GaussianInt) : 0 ≤ t2core z mm w := by
  simp only [t2core]
  split_ifs <;> positivity

lemma t2G_nonneg (Pz : ℕ) (z : GaussianInt) : 0 ≤ t2G Pz z := by
  simp only [t2G]
  have h1 : (0:ℝ) ≤ (if NoSmallP Pz z then (1:ℝ) else 0) := by split_ifs <;> norm_num
  have h2 : (0:ℝ) ≤ |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)| := abs_nonneg _
  have h3 : (0:ℝ) ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  exact mul_nonneg (mul_nonneg h1 h2) h3

lemma t2Bnd_nonneg (Pz : ℕ) (z : GaussianInt) (mm : ℕ) (w : GaussianInt) :
    0 ≤ t2Bnd Pz z mm w :=
  mul_nonneg (t2core_nonneg z mm w) (t2G_nonneg Pz z)

/-- Membership in `primAnn R`, unfolded. -/
lemma mem_primAnn_iff {R : ℕ} {z : GaussianInt} :
    z ∈ primAnn R ↔ z ∈ Work.FIPlan.gBox ((R:ℕ):ℤ) ∧ 1 ≤ Work.FIPlan.gnorm z
      ∧ Work.FIPlan.gnorm z ≤ R ∧ Work.FIPlan.IsPrimary z := by
  simp only [primAnn, Finset.mem_filter]
  tauto

/-! ## 1. The `k`-sum of the cell coefficients -/

/-- `pcInd (Pa i k) (φ k) z` is bounded by the indicator of `(Pa i k)`-freeness of `z`. -/
lemma pcInd_le_noSmallP (Pz : ℕ) (Pa : Work.FITop.Params) (hPz : Pa.Pz = Pz)
    (φ : ℝ) (z : GaussianInt) :
    pcInd Pa φ z ≤ (if NoSmallP Pz z then (1:ℝ) else 0) := by
  rw [pcInd, pcCond]
  by_cases hNS : NoSmallP Pz z
  · rw [if_pos hNS]; split_ifs <;> norm_num
  · have hnc : ¬ (InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z
        ∧ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ) := by
      intro hc
      exact hNS ((noSmallP_iff Pa Pz hPz z).mp hc.2.1)
    rw [if_neg hNS, if_neg hnc]

/-- `|cfVal|` of a cell coefficient, bounded by the `T2`-cop arithmetic factor. -/
lemma abs_cfVal_le {Pz : ℕ} (φ : ℝ) (q : ℝ → ℝ)
    (p : ℝ → ℝ) (Pa : Work.FITop.Params) (hPz : Pa.Pz = Pz)
    (hq0 : ∀ α, 0 ≤ q α) (hp0 : ∀ u, 0 ≤ p u) (z : GaussianInt) :
    |cfVal Pa φ q p z| ≤ (if NoSmallP Pz z then (1:ℝ) else 0)
      * (q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
        * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) := by
  have hNS : (0:ℝ) ≤ (if NoSmallP Pz z then (1:ℝ) else 0) := by split_ifs <;> norm_num
  have hpc : pcInd Pa φ z ≤ (if NoSmallP Pz z then (1:ℝ) else 0) := by
    rw [pcInd, pcCond]
    by_cases h : NoSmallP Pz z
    · rw [if_pos h]; split_ifs <;> norm_num
    · have hnc : ¬ (InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z
          ∧ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ) :=
        fun hc => h ((noSmallP_iff Pa Pz hPz z).mp hc.2.1)
      rw [if_neg h, if_neg hnc]
  have hμ0 : (0:ℝ) ≤ |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)| := abs_nonneg _
  have hτ0 : (0:ℝ) ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_cfVal _ _ _ _ _ (hq0 _) (hp0 _)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hpc (mul_nonneg (mul_nonneg (mul_nonneg (hq0 _) (hp0 _)) hμ0) hτ0))
  apply mul_le_mul_of_nonneg_left _ (pcInd_nonneg _ _ _)
  exact mul_le_mul_of_nonneg_left (abs_gammaTrunc_le _ _)
    (mul_nonneg (mul_nonneg (hq0 _) (hp0 _)) hμ0)

/-- **The termwise bound of the `T2`-cop summand.** -/
lemma t2_summand_le {K K' : ℕ} (Pz : ℕ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (p : Fin K → ℝ → ℝ) (Pa : Fin K → Fin K' → Work.FITop.Params)
    (hPz : ∀ i k, (Pa i k).Pz = Pz)
    (hp0 : ∀ i u, 0 ≤ p i u) (hq0 : ∀ k α, 0 ≤ q k α)
    (i : Fin K) (k : Fin K') (mm : ℕ) (w z : GaussianInt) :
    2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0:ℝ) else 1)
        * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
      ≤ t2Bnd Pz z mm w * p i (Work.FIPlan.gnorm z) * q k (Complex.arg z.toComplex - φ k) := by
  have hZ0 : (0:ℝ) ≤ (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := Nat.cast_nonneg _
  have hc0 : (0:ℝ) ≤ 2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0:ℝ) else 1) := by
    split_ifs <;> norm_num
  have hcf := abs_cfVal_le (φ k) (q k) (p i) (Pa i k) (hPz i k) (hq0 k) (hp0 i) z
  rw [norm_pieceCoeff_mul_Zc]
  have hstep : |cfVal (Pa i k) (φ k) (q k) (p i) z| * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
      ≤ ((if NoSmallP Pz z then (1:ℝ) else 0)
          * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)))
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) :=
    mul_le_mul_of_nonneg_right hcf hZ0
  calc 2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0:ℝ) else 1)
        * (|cfVal (Pa i k) (φ k) (q k) (p i) z| * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      ≤ 2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0:ℝ) else 1)
        * (((if NoSmallP Pz z then (1:ℝ) else 0)
            * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
              * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
              * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)))
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep hc0
    _ = t2Bnd Pz z mm w * p i (Work.FIPlan.gnorm z) * q k (Complex.arg z.toComplex - φ k) := by
        simp only [t2Bnd, t2G, t2core]; ring

/-! ## 2. Reorderings -/

/-- Push the `i`,`k` sums inside the `(mm,w,z)` sums. -/
lemma reorder_ik {K K' : ℕ} (s3 : Finset ℕ) (u : Finset GaussianInt)
    (G : Fin K → Fin K' → ℕ → GaussianInt → GaussianInt → ℝ) :
    (∑ i : Fin K, ∑ k : Fin K', ∑ mm ∈ s3, ∑ w ∈ wSph mm, ∑ z ∈ u, G i k mm w z)
      = ∑ mm ∈ s3, ∑ w ∈ wSph mm, ∑ z ∈ u, ∑ i : Fin K, ∑ k : Fin K', G i k mm w z := by
  have h1 : (∑ i : Fin K, ∑ k : Fin K', ∑ mm ∈ s3, ∑ w ∈ wSph mm, ∑ z ∈ u, G i k mm w z)
      = ∑ i : Fin K, ∑ mm ∈ s3, ∑ k : Fin K', ∑ w ∈ wSph mm, ∑ z ∈ u, G i k mm w z := by
    apply Finset.sum_congr rfl; intro i _
    exact Finset.sum_comm
  rw [h1]
  have h2 : (∑ i : Fin K, ∑ mm ∈ s3, ∑ k : Fin K', ∑ w ∈ wSph mm, ∑ z ∈ u, G i k mm w z)
      = ∑ mm ∈ s3, ∑ i : Fin K, ∑ k : Fin K', ∑ w ∈ wSph mm, ∑ z ∈ u, G i k mm w z :=
    Finset.sum_comm
  rw [h2]
  apply Finset.sum_congr rfl; intro mm _
  have h3 : (∑ i : Fin K, ∑ k : Fin K', ∑ w ∈ wSph mm, ∑ z ∈ u, G i k mm w z)
      = ∑ i : Fin K, ∑ w ∈ wSph mm, ∑ k : Fin K', ∑ z ∈ u, G i k mm w z := by
    apply Finset.sum_congr rfl; intro i _
    exact Finset.sum_comm
  rw [h3]
  have h4 : (∑ i : Fin K, ∑ w ∈ wSph mm, ∑ k : Fin K', ∑ z ∈ u, G i k mm w z)
      = ∑ w ∈ wSph mm, ∑ i : Fin K, ∑ k : Fin K', ∑ z ∈ u, G i k mm w z :=
    Finset.sum_comm
  rw [h4]
  apply Finset.sum_congr rfl; intro w _
  have h5 : (∑ i : Fin K, ∑ k : Fin K', ∑ z ∈ u, G i k mm w z)
      = ∑ i : Fin K, ∑ z ∈ u, ∑ k : Fin K', G i k mm w z := by
    apply Finset.sum_congr rfl; intro i _
    exact Finset.sum_comm
  rw [h5]
  exact Finset.sum_comm

/-- Swap the `z`-sum with the dependent `(mm,w)`-sum. -/
lemma swap_z_blk (s3 : Finset ℕ) (u : Finset GaussianInt) (F : ℕ → GaussianInt → GaussianInt → ℝ) :
    (∑ mm ∈ s3, ∑ w ∈ wSph mm, ∑ z ∈ u, F mm w z)
      = ∑ z ∈ u, ∑ mm ∈ s3, ∑ w ∈ wSph mm, F mm w z := by
  have h1 : (∑ mm ∈ s3, ∑ w ∈ wSph mm, ∑ z ∈ u, F mm w z)
      = ∑ mm ∈ s3, ∑ z ∈ u, ∑ w ∈ wSph mm, F mm w z := by
    apply Finset.sum_congr rfl; intro mm _
    exact Finset.sum_comm
  rw [h1]
  exact Finset.sum_comm

/-- `(Σ_m Σ_w f) * c = Σ_m Σ_w (f * c)`. -/
lemma sum_sum_mul (s : Finset ℕ) (t : ℕ → Finset GaussianInt) (f : ℕ → GaussianInt → ℝ) (c : ℝ) :
    (∑ mm ∈ s, ∑ w ∈ t mm, f mm w * c) = (∑ mm ∈ s, ∑ w ∈ t mm, f mm w) * c := by
  have h1 : ∀ mm : ℕ, (∑ w ∈ t mm, f mm w * c) = (∑ w ∈ t mm, f mm w) * c := by
    intro mm
    exact (Finset.sum_mul (s := t mm) (f := f mm) (a := c)).symm
  rw [Finset.sum_congr rfl (fun mm _ => h1 mm)]
  exact (Finset.sum_mul (s := s) (f := fun mm => ∑ w ∈ t mm, f mm w) (a := c)).symm

/-- `Σ_i Σ_k (B · p_i · q_k) = B · (Σ_i p_i) · (Σ_k q_k)`. -/
lemma sum_ik_factor {K K' : ℕ} (B : ℝ) (pp : Fin K → ℝ) (qq : Fin K' → ℝ) :
    (∑ i, ∑ k, B * pp i * qq k) = B * (∑ i, pp i) * (∑ k, qq k) := by
  have h1 : ∀ i : Fin K, (∑ k : Fin K', B * pp i * qq k)
      = (B * pp i) * (∑ k : Fin K', qq k) := by
    intro i; rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [(Finset.sum_mul (s := Finset.univ) (f := fun i : Fin K => B * pp i) (a := ∑ k : Fin K', qq k)).symm]
  rw [show (∑ i : Fin K, B * pp i) = B * (∑ i, pp i) from by rw [Finset.mul_sum]]


/-! ## 4. Elementary helpers for the assembly -/

lemma sum_p_nonneg {K : ℕ} (p : Fin K → ℝ → ℝ) (hp0 : ∀ i u, 0 ≤ p i u) (u : ℝ) :
    0 ≤ (∑ i, p i u) := Finset.sum_nonneg (fun i _ => hp0 i u)

lemma sum_p_eq_zero_of_le {K : ℕ} (N : ℕ) (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ)
    (ha : ∀ i, (N:ℝ) ≤ a i) (hpsup : ∀ i u, p i u ≠ 0 → a i < u) (u : ℝ)
    (hu : u ≤ (N:ℝ)) : (∑ i, p i u) = 0 := by
  apply Finset.sum_eq_zero; intro i _
  by_contra h
  have h1 := hpsup i u h
  have h2 := ha i
  linarith

lemma sum_p_le_one {K : ℕ} (N : ℕ) (θ : ℝ) (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ)
    (ha : ∀ i, (N:ℝ) ≤ a i)
    (hpsup : ∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1+θ)*a i)
    (hsum_le : ∀ u, (N:ℝ) < u → u ≤ 2*(N:ℝ) → (∑ i, p i u) ≤ 1)
    (u : ℝ) (hu : u ≤ 2*(N:ℝ)) : (∑ i, p i u) ≤ 1 := by
  by_cases h : (N:ℝ) < u
  · exact hsum_le u h hu
  · rw [sum_p_eq_zero_of_le N a p ha (fun i u h => (hpsup i u h).1) u (le_of_not_gt h)]
    norm_num

/-- `ω(u)·log 2 ≤ log u ≤ log M`. -/
lemma card_primeFactors_le_log (u : ℕ) (M : ℝ) (hu : 1 ≤ u) (huM : (u:ℝ) ≤ M) :
    ((u.primeFactors.card : ℕ) : ℝ) ≤ Real.log M / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdvd : ∏ p ∈ u.primeFactors, p ∣ u := Nat.prod_primeFactors_dvd u
  have hle : ∏ p ∈ u.primeFactors, p ≤ u := Nat.le_of_dvd hu hdvd
  have h2 : (2:ℕ)^(u.primeFactors.card) ≤ ∏ p ∈ u.primeFactors, p := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod₀
    · intro p hp; norm_num
    · intro p hp; exact (Nat.prime_of_mem_primeFactors hp).two_le
  have h3 : (2:ℕ)^(u.primeFactors.card) ≤ u := le_trans h2 hle
  have h3r : (2:ℝ)^(u.primeFactors.card) ≤ (u:ℝ) := by exact_mod_cast h3
  have hpos : (0:ℝ) < (2:ℝ)^(u.primeFactors.card) := by positivity
  have hlog : ((u.primeFactors.card : ℕ) : ℝ) * Real.log 2
      = Real.log ((2:ℝ)^(u.primeFactors.card)) := by
    rw [Real.log_pow]
  have hstep : ((u.primeFactors.card : ℕ) : ℝ) * Real.log 2 ≤ Real.log M := by
    rw [hlog]
    exact le_trans (Real.log_le_log hpos h3r)
      (Real.log_le_log (by exact_mod_cast hu) huM)
  rw [le_div_iff₀ hlog2]
  linarith

/-- The tau-sum of the primary annulus `primAnn (2N)`, from the sector tau-sum. -/
lemma primAnn_tau_sum_le (N : ℕ) (hN : 1 ≤ N) (C : ℝ)
    (hCtau : ∀ (N' θ φ : ℝ), 1 ≤ N' → 0 ≤ θ → θ ≤ 1 →
      ∑ z ∈ (Work.FIPlan.gBox (⌈Real.sqrt (4 * N' * (1 + θ))⌉₊ : ℤ)).filter
          (fun z => N' < ((Work.FIPlan.gnorm z : ℕ) : ℝ) ∧
                    ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + θ) * N' ∧
                    φ < Complex.arg z.toComplex ∧ Complex.arg z.toComplex ≤ φ + 2 * Real.pi * θ ∧
                    Squarefree (Work.FIPlan.gnorm z)),
        (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
      ≤ C * (Real.sqrt N' + θ * N') * (Real.log (2 + N')) ^ 9) :
    (∑ z ∈ primAnn (2*N), (if (N:ℝ) < (Work.FIPlan.gnorm z : ℝ) ∧ Squarefree (Work.FIPlan.gnorm z)
        then (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) else 0))
      ≤ C * (Real.sqrt (N:ℝ) + (N:ℝ)) * (Real.log (2 + (N:ℝ))) ^ 9 := by
  have h := hCtau (N:ℝ) 1 (-Real.pi) (by exact_mod_cast hN) (by norm_num) (by norm_num)
  have hNN : (1 + (1:ℝ)) * (N:ℝ) = 2 * (N:ℝ) := by ring
  have hpi : -Real.pi + 2 * Real.pi * 1 = Real.pi := by ring
  simp only [hNN, hpi, one_mul] at h
  refine le_trans ?_ h
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    obtain ⟨hzp, hlt, hsf⟩ := hz
    obtain ⟨hbox, hlow, hhi, -⟩ := mem_primAnn_iff.mp hzp
    have hmem : z ∈ Work.FIPlan.gBox ((⌈Real.sqrt (4 * (N:ℝ) * (1+1))⌉₊ : ℕ) : ℤ) := by
      apply mem_gBox_of_norm_sq (m := Work.FIPlan.gnorm z) rfl
      have h1 : ((Work.FIPlan.gnorm z : ℕ) : ℝ)
          ≤ ((⌈Real.sqrt (4 * (N:ℝ) * (1+1))⌉₊ : ℕ) : ℝ)^2 := by
        have h2N : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * (N:ℝ) := by exact_mod_cast hhi
        have h3 : (2 * (N:ℝ)) ≤ ((⌈Real.sqrt (4 * (N:ℝ) * (1+1))⌉₊ : ℕ) : ℝ)^2 := by
          have hc := Nat.le_ceil (Real.sqrt (4 * (N:ℝ) * (1+1)))
          have h4 : (0:ℝ) ≤ 4*(N:ℝ)*(1+1) := by positivity
          have hsq := Real.sq_sqrt h4
          have harg : 4 * (N:ℝ) * (1+1) = 8 * (N:ℝ) := by ring
          nlinarith [hc, Real.sqrt_nonneg (4*(N:ℝ)*(1+1)), hsq, harg]
        linarith
      exact_mod_cast h1
    refine ⟨hmem, ?_, ?_, ?_, ?_, hsf⟩
    · exact_mod_cast hlt
    · have : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * (N:ℝ) := by exact_mod_cast hhi
      linarith
    · exact Complex.neg_pi_lt_arg _
    · have := Complex.arg_le_pi z.toComplex
      linarith
  · intro x _ _; positivity

/-! ## 3. The per-`z` count of non-coprime `w`'s -/

/-- The non-coprime pairs of the `|w|²`-sphere contribute only `ω(|z|²)·(MN)^{1/4}`-many weighted
points, by `noncoprime_count_rat`. -/
lemma annM_noncop_sum_le (Pa : Work.FITop.Params) (z : GaussianInt)
    (hlo : Pa.N < (Work.FIPlan.gnorm z : ℝ)) (hhi : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N)
    (hsf : Squarefree (Work.FIPlan.gnorm z))
    (hnsp : ∀ p : ℕ, p.Prime → p ≤ Pa.Pz → ¬ p ∣ Work.FIPlan.gnorm z) :
    2 * (∑ w ∈ Work.FITop3.annM Pa,
        (if Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) then (0:ℝ) else 1)
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      ≤ 1600 * (Pa.M * Pa.N) ^ ((1:ℝ)/4)
          * (1 + Real.sqrt Pa.M / ((Pa.Pz : ℝ) * Real.sqrt Pa.N))
          * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) := by
  have hcard := noncoprime_count_rat Pa z hlo hhi hsf hnsp
  have hterm : ∀ w ∈ Work.FITop3.annM Pa,
      (if Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) then (0:ℝ) else 1)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
      ≤ 2 * (if (¬ Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z)
            ∧ 0 < Work.FIPlan.Zint (Work.FIPlan.cForm w z)) then (1:ℝ) else 0) := by
    intro w _
    by_cases hc : Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z)
    · rw [if_pos hc]; split_ifs <;> norm_num
    · rw [if_neg hc]
      have hZ2 : (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) ≤ 2 := by
        exact_mod_cast Zint_le_two _
      by_cases hZ : 0 < Work.FIPlan.Zint (Work.FIPlan.cForm w z)
      · rw [if_pos ⟨hc, hZ⟩]; linarith
      · rw [if_neg (fun h => hZ h.2)]
        have h0 : Work.FIPlan.Zint (Work.FIPlan.cForm w z) = 0 := by omega
        simp [h0]
  have hsum : (∑ w ∈ Work.FITop3.annM Pa,
        (if Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) then (0:ℝ) else 1)
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      ≤ 2 * (((Work.FITop3.annM Pa).filter (fun w =>
            ¬ Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z)
            ∧ 0 < Work.FIPlan.Zint (Work.FIPlan.cForm w z))).card : ℝ) := by
    calc _ ≤ ∑ w ∈ Work.FITop3.annM Pa, 2 * (if (¬ Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z)
            ∧ 0 < Work.FIPlan.Zint (Work.FIPlan.cForm w z)) then (1:ℝ) else 0) :=
          Finset.sum_le_sum hterm
      _ = 2 * (((Work.FITop3.annM Pa).filter (fun w =>
            ¬ Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z)
            ∧ 0 < Work.FIPlan.Zint (Work.FIPlan.cForm w z))).card : ℝ) := by
          rw [← Finset.mul_sum]; congr 1; exact Finset.sum_boole _ _
  have hnn : (0:ℝ) ≤ (((Work.FITop3.annM Pa).filter (fun w =>
      ¬ Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z)
      ∧ 0 < Work.FIPlan.Zint (Work.FIPlan.cForm w z))).card : ℝ) := by positivity
  nlinarith [hcard, hsum, hnn]

/-- **The per-`z` count bound**: `t2Phi` is bounded by `(MN)^{1/4}(1+√M/(P√N))·ω(|z|²)`. -/
lemma t2Phi_le (Pz Mn : ℕ) (Pa : Work.FITop.Params) (z : GaussianInt)
    (hPM : Pa.M = (Mn:ℝ)) (hPPz : Pa.Pz = Pz) (hMn : 1 ≤ Mn)
    (hlo : Pa.N < (Work.FIPlan.gnorm z : ℝ)) (hhi : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N)
    (hsf : Squarefree (Work.FIPlan.gnorm z)) (hNS : NoSmallP Pz z) :
    t2Phi (Finset.Icc (Mn+1) (2*Mn)) z ≤ 1600 * (Pa.M * Pa.N) ^ ((1:ℝ)/4)
      * (1 + Real.sqrt Pa.M / ((Pa.Pz:ℝ) * Real.sqrt Pa.N))
      * (((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ) := by
  have hnsp : ∀ p : ℕ, p.Prime → p ≤ Pa.Pz → ¬ p ∣ Work.FIPlan.gnorm z := by
    intro p hp hple
    exact hNS p hp (hPPz ▸ hple)
  have hconv : t2Phi (Finset.Icc (Mn+1) (2*Mn)) z
      = ∑ mm ∈ Finset.Icc (Mn+1) (2*Mn), ∑ w ∈ wSph mm,
          2 * (if Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) then (0:ℝ) else 1)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
    rw [t2Phi]
    apply Finset.sum_congr rfl; intro mm _
    apply Finset.sum_congr rfl; intro w hw
    have hgw : Work.FIPlan.gnorm w = mm := (Finset.mem_filter.mp hw).2
    simp only [t2core, hgw]
  rw [hconv]
  rw [← fiber_sum_annM (A := Mn)
    (F := fun w => 2 * (if Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) then (0:ℝ) else 1)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) hPM hMn]
  have hmul : (∑ w ∈ Work.FITop3.annM Pa, 2 * (if Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) then (0:ℝ) else 1)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      = 2 * (∑ w ∈ Work.FITop3.annM Pa,
          (if Nat.Coprime (Work.FIPlan.gnorm w) (Work.FIPlan.gnorm z) then (0:ℝ) else 1)
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro w _; ring
  rw [hmul]
  exact annM_noncop_sum_le Pa z hlo hhi hsf hnsp

/-! ## 5. The window bound -/

theorem window_T2_cop_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (x N Mn Pz : ℕ) (τ θ : ℝ) (K K' : ℕ)
      (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
      (Pa : Fin K → Fin K' → Work.FITop.Params),
      (4 ≤ x) → (1 ≤ Mn) → (1 ≤ N) → (2 ≤ Pz) → (0 < θ) → (θ ≤ 1 / 4) →
      ((N : ℝ) ^ (2 : ℕ) ≤ (x : ℝ)) →
      (∀ i k, (Pa i k).M = (Mn : ℝ)) → (∀ i k, (Pa i k).N = a i) →
      (∀ i k, (Pa i k).Pz = Pz) → (∀ i k, (Pa i k).τ = τ) →
      (∀ i, (N : ℝ) ≤ a i) → (∀ i, a i ≤ 2 * (N : ℝ)) →
      (∀ i u, 0 ≤ p i u) → (∀ i u, p i u ≤ 1) →
      (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) →
      (∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1) →
      (∀ k α, 0 ≤ q k α) → (∀ k α, q k α ≤ 1) → (∀ k, q k 0 = 0) →
      (∀ k α, q k α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) →
      (∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1) →
      ((N : ℝ) ≤ (Mn : ℝ)) →
      (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ Work.FITop4.Red5.wSph mm, ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
            2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0 : ℝ) else 1)
              * ‖Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        ≤ c * ((Mn : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((5 : ℝ) / 4)
              + (Pz : ℝ)⁻¹ * (Mn : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ ((3 : ℝ) / 4))
            * (Real.log (x : ℝ)) ^ (100 : ℕ) := by
  obtain ⟨C, hCpos, hCtau⟩ := Work.FIArea6b.sector_tau_sum
  refine ⟨3200 * C * (2 : ℝ) ^ ((1:ℝ)/4) * 3 ^ (10:ℕ) / Real.log 2 + 1, ?_, ?_⟩
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  intro x N Mn Pz τ θ K K' a p φ q Pa hx hMn hN hPz hθ0 hθ14 hN2 hPaM hPaN hPaPz hPaTau
    ha_le ha_hi hp0 hp1 hpsup hsum_le hq0 hq1 hq0z hqsup hang hNMn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases Nat.eq_zero_or_pos K' with hK'0 | hK'pos
  · subst hK'0
    have h0 : (∑ i : Fin K, ∑ k : Fin 0,
        ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
          ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
            2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0 : ℝ) else 1)
              * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖) = 0 := by
      simp
    rw [h0]
    have hb : (0:ℝ) ≤ (Mn : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((5:ℝ) / 4)
        + (Pz : ℝ)⁻¹ * (Mn : ℝ) ^ ((3:ℝ) / 4) * (N : ℝ) ^ ((3:ℝ) / 4) := by
      have h1 : (0:ℝ) ≤ (Mn : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((5:ℝ) / 4) := by positivity
      have h2 : (0:ℝ) ≤ (Pz : ℝ)⁻¹ * (Mn : ℝ) ^ ((3:ℝ) / 4) * (N : ℝ) ^ ((3:ℝ) / 4) := by positivity
      linarith
    have hl : (0:ℝ) ≤ (Real.log (x : ℝ)) ^ (100:ℕ) :=
      pow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))) 100
    have hc : (0:ℝ) < 3200 * C * (2 : ℝ) ^ ((1:ℝ)/4) * 3 ^ (10:ℕ) / Real.log 2 + 1 := by
      positivity
    exact mul_nonneg (mul_nonneg (le_of_lt hc) hb) hl
  · -- main case: `K' ≥ 1`
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hNpos : (0:ℝ) < (N:ℝ) := by linarith
    have hMn1 : (1:ℝ) ≤ (Mn:ℝ) := by exact_mod_cast hMn
    have hPz2 : (2:ℝ) ≤ (Pz:ℝ) := by exact_mod_cast hPz
    have hPz0 : (0:ℝ) < (Pz:ℝ) := by linarith
    have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
    set k0 : Fin K' := ⟨0, hK'pos⟩ with hk0
    have hule : ∀ z ∈ primAnn (2*N), (Work.FIPlan.gnorm z : ℝ) ≤ 2*(N:ℝ) :=
      fun z hz => by exact_mod_cast (mem_primAnn_iff.mp hz).2.2.1
    -- main estimate
    have hmain : (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
        ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
          2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0 : ℝ) else 1)
            * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
      ≤ 1600 * (2 * (Mn : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4)
          * (1 + Real.sqrt (Mn : ℝ) / ((Pz : ℝ) * Real.sqrt (N : ℝ)))
          * (Real.log (2 * (N : ℝ)) / Real.log 2)
          * (C * (Real.sqrt (N : ℝ) + (N : ℝ)) * (Real.log (2 + (N : ℝ))) ^ (9:ℕ)) := by
      -- (a) termwise bound and enlargement of the `mm`-range
      have step1 : (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
            ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
              2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0 : ℝ) else 1)
                * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
          ≤ ∑ i, ∑ k, ∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
              t2Bnd Pz z mm w * p i (Work.FIPlan.gnorm z) * q k (Complex.arg z.toComplex - φ k) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro k _
        refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)) _) ?_)
        · apply Finset.sum_le_sum; intro mm _
          apply Finset.sum_le_sum; intro w _
          apply Finset.sum_le_sum; intro z _
          exact t2_summand_le Pz φ q p Pa hPaPz hp0 hq0 i k mm w z
        · intro mm _ _
          apply Finset.sum_nonneg; intro w _
          apply Finset.sum_nonneg; intro z _
          exact mul_nonneg (mul_nonneg (t2Bnd_nonneg Pz z mm w) (hp0 i _)) (hq0 k _)
      -- (b) reorder
      have step2 : (∑ i, ∑ k, ∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
              t2Bnd Pz z mm w * p i (Work.FIPlan.gnorm z) * q k (Complex.arg z.toComplex - φ k))
          = ∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N), ∑ i, ∑ k,
              t2Bnd Pz z mm w * p i (Work.FIPlan.gnorm z) * q k (Complex.arg z.toComplex - φ k) :=
        reorder_ik (Finset.Icc (Mn + 1) (2 * Mn)) (primAnn (2 * N))
          (fun i k mm w z => t2Bnd Pz z mm w * p i (Work.FIPlan.gnorm z) * q k (Complex.arg z.toComplex - φ k))
      -- (c) the `q`-partition of unity
      have step3 : (∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N), ∑ i, ∑ k,
              t2Bnd Pz z mm w * p i (Work.FIPlan.gnorm z) * q k (Complex.arg z.toComplex - φ k))
          = ∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
              t2Bnd Pz z mm w * (∑ i, p i (Work.FIPlan.gnorm z))
                * (∑ k, q k (Complex.arg z.toComplex - φ k)) := by
        apply Finset.sum_congr rfl; intro mm _
        apply Finset.sum_congr rfl; intro w _
        apply Finset.sum_congr rfl; intro z _
        exact sum_ik_factor (t2Bnd Pz z mm w) (fun i => p i (Work.FIPlan.gnorm z))
          (fun k => q k (Complex.arg z.toComplex - φ k))
      -- (d) `Σ_k q_k = 1`
      have step4 : (∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
              t2Bnd Pz z mm w * (∑ i, p i (Work.FIPlan.gnorm z))
                * (∑ k, q k (Complex.arg z.toComplex - φ k)))
          = ∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
              t2Bnd Pz z mm w * (∑ i, p i (Work.FIPlan.gnorm z)) * 1 := by
        apply Finset.sum_congr rfl; intro mm _
        apply Finset.sum_congr rfl; intro w _
        apply Finset.sum_congr rfl; intro z _
        rw [hang _ (le_of_lt (Complex.neg_pi_lt_arg _)) (Complex.arg_le_pi _)]
      -- (e) reassemble into `t2G · t2Phi`
      have step5 : (∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
              t2Bnd Pz z mm w * (∑ i, p i (Work.FIPlan.gnorm z)) * 1)
          = ∑ z ∈ primAnn (2 * N),
              t2G Pz z * ((∑ i, p i (Work.FIPlan.gnorm z)) * t2Phi (Finset.Icc (Mn+1) (2*Mn)) z) := by
        rw [swap_z_blk]
        apply Finset.sum_congr rfl; intro z _
        have h1 : (∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm,
              t2Bnd Pz z mm w * (∑ i, p i (Work.FIPlan.gnorm z)) * 1)
            = (∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm, t2Bnd Pz z mm w)
              * (∑ i, p i (Work.FIPlan.gnorm z)) := by
          have h0 : (∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm,
                t2Bnd Pz z mm w * (∑ i, p i (Work.FIPlan.gnorm z)) * 1)
              = ∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm,
                t2Bnd Pz z mm w * (∑ i, p i (Work.FIPlan.gnorm z)) := by
            apply Finset.sum_congr rfl; intro mm _
            apply Finset.sum_congr rfl; intro w _
            rw [mul_one]
          rw [h0]
          exact sum_sum_mul (Finset.Icc (Mn + 1) (2 * Mn)) wSph
            (fun mm w => t2Bnd Pz z mm w) (∑ i, p i (Work.FIPlan.gnorm z))
        rw [h1]
        have h2 : (∑ mm ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph mm, t2Bnd Pz z mm w)
            = t2G Pz z * t2Phi (Finset.Icc (Mn+1) (2*Mn)) z := by
          have hA1 := sum_sum_mul (Finset.Icc (Mn + 1) (2 * Mn)) wSph
            (fun mm w => t2core z mm w) (t2G Pz z)
          simp only [t2Bnd, t2Phi]
          rw [hA1]
          ring
        rw [h2]
        ring
      -- (f) the per-`z` count
      have step6 : (∑ z ∈ primAnn (2 * N),
              t2G Pz z * ((∑ i, p i (Work.FIPlan.gnorm z)) * t2Phi (Finset.Icc (Mn+1) (2*Mn)) z))
          ≤ ∑ z ∈ primAnn (2 * N),
              t2G Pz z * ((1600 * (2 * (Mn : ℝ) * (N : ℝ)) ^ ((1:ℝ)/4)
                  * (1 + Real.sqrt (Mn : ℝ) / ((Pz : ℝ) * Real.sqrt (N : ℝ))))
                * ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
                * (∑ i, p i (Work.FIPlan.gnorm z))) := by
        apply Finset.sum_le_sum; intro z hz
        by_cases hG : t2G Pz z = 0
        · simp [hG]
        · have hNS : NoSmallP Pz z := by
            by_contra h
            exact hG (by simp only [t2G]; rw [if_neg h]; ring)
          have hμ : (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ) ≠ 0 := by
            intro h0
            exact hG (by simp only [t2G]; rw [if_pos hNS, h0]; norm_num)
          have hsf : Squarefree (Work.FIPlan.gnorm z) :=
            ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp (Int.cast_ne_zero.mp hμ)
          have huz : (Work.FIPlan.gnorm z : ℝ) ≤ 2*(N:ℝ) := hule z hz
          by_cases hP : (∑ i, p i (Work.FIPlan.gnorm z)) = 0
          · simp [hP]
          · obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
            have hai : a i < (Work.FIPlan.gnorm z : ℝ) := (hpsup i _ hi).1
            have hali : (N:ℝ) ≤ a i := ha_le i
            have hu2ai : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * a i := by linarith
            have hcount := t2Phi_le Pz Mn (Pa i k0) z (hPaM i k0) (hPaPz i k0) hMn
              (by rw [hPaN i k0]; exact hai) (by rw [hPaN i k0]; exact hu2ai) hsf hNS
            rw [hPaM i k0, hPaN i k0, hPaPz i k0] at hcount
            -- monotone comparison with `a i ∈ [N, 2N]`
            have hmono : 1600 * ((Mn:ℝ) * a i) ^ ((1:ℝ)/4)
                  * (1 + Real.sqrt (Mn:ℝ) / ((Pz:ℝ) * Real.sqrt (a i)))
                ≤ 1600 * (2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4)
                  * (1 + Real.sqrt (Mn:ℝ) / ((Pz:ℝ) * Real.sqrt (N:ℝ))) := by
              have ha0 : 0 ≤ a i := le_trans (le_of_lt hNpos) hali
              have hX : ((Mn:ℝ) * a i) ^ ((1:ℝ)/4) ≤ (2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4) := by
                apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
                nlinarith [ha_hi i]
              have hY : (1 + Real.sqrt (Mn:ℝ) / ((Pz:ℝ) * Real.sqrt (a i)))
                  ≤ (1 + Real.sqrt (Mn:ℝ) / ((Pz:ℝ) * Real.sqrt (N:ℝ))) := by
                apply add_le_add le_rfl
                apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
                exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hali) (le_of_lt hPz0)
              have hY0 : (0:ℝ) ≤ 1 + Real.sqrt (Mn:ℝ) / ((Pz:ℝ) * Real.sqrt (a i)) := by positivity
              have hX0 : (0:ℝ) ≤ (2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4) := by positivity
              calc 1600 * ((Mn:ℝ) * a i) ^ ((1:ℝ)/4)
                    * (1 + Real.sqrt (Mn:ℝ) / ((Pz:ℝ) * Real.sqrt (a i)))
                  = 1600 * (((Mn:ℝ) * a i) ^ ((1:ℝ)/4)
                      * (1 + Real.sqrt (Mn:ℝ) / ((Pz:ℝ) * Real.sqrt (a i)))) := by ring
                _ ≤ 1600 * ((2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4)
                      * (1 + Real.sqrt (Mn:ℝ) / ((Pz:ℝ) * Real.sqrt (N:ℝ)))) := by
                    apply mul_le_mul_of_nonneg_left _ (by norm_num)
                    exact mul_le_mul hX hY hY0 hX0
                _ = 1600 * (2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4)
                      * (1 + Real.sqrt (Mn:ℝ) / ((Pz:ℝ) * Real.sqrt (N:ℝ))) := by ring
            have hω0 : (0:ℝ) ≤ ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)) := Nat.cast_nonneg _
            have hfin := le_trans hcount (mul_le_mul_of_nonneg_right hmono hω0)
            have hPnn : (0:ℝ) ≤ (∑ i, p i (Work.FIPlan.gnorm z)) := sum_p_nonneg p hp0 _
            have hGnn : (0:ℝ) ≤ t2G Pz z := t2G_nonneg Pz z
            calc t2G Pz z * ((∑ i, p i (Work.FIPlan.gnorm z))
                  * t2Phi (Finset.Icc (Mn+1) (2*Mn)) z)
                ≤ t2G Pz z * ((∑ i, p i (Work.FIPlan.gnorm z))
                    * (1600 * (2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4)
                      * (1 + Real.sqrt (Mn:ℝ) / ((Pz:ℝ) * Real.sqrt (N:ℝ)))
                      * ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)))) := by
                  apply mul_le_mul_of_nonneg_left _ hGnn
                  apply mul_le_mul_of_nonneg_left hfin hPnn
              _ = t2G Pz z * (1600 * (2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4)
                      * (1 + Real.sqrt (Mn:ℝ) / ((Pz:ℝ) * Real.sqrt (N:ℝ)))
                    * ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
                    * (∑ i, p i (Work.FIPlan.gnorm z))) := by ring
      -- (g) the tau sum
      have step7 : (∑ z ∈ primAnn (2 * N),
              t2G Pz z * ((1600 * (2 * (Mn : ℝ) * (N : ℝ)) ^ ((1:ℝ)/4)
                  * (1 + Real.sqrt (Mn : ℝ) / ((Pz : ℝ) * Real.sqrt (N : ℝ))))
                * ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
                * (∑ i, p i (Work.FIPlan.gnorm z))))
          = (1600 * (2 * (Mn : ℝ) * (N : ℝ)) ^ ((1:ℝ)/4)
                * (1 + Real.sqrt (Mn : ℝ) / ((Pz : ℝ) * Real.sqrt (N : ℝ))))
            * (∑ z ∈ primAnn (2 * N),
                t2G Pz z * ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
                  * (∑ i, p i (Work.FIPlan.gnorm z))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro z _; ring
      have step8 : (∑ z ∈ primAnn (2 * N),
              t2G Pz z * ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
                * (∑ i, p i (Work.FIPlan.gnorm z)))
          ≤ (Real.log (2 * (N : ℝ)) / Real.log 2)
            * (C * (Real.sqrt (N : ℝ) + (N : ℝ)) * (Real.log (2 + (N : ℝ))) ^ (9:ℕ)) := by
        have hA : ∀ z ∈ primAnn (2*N),
            t2G Pz z * ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
                * (∑ i, p i (Work.FIPlan.gnorm z))
              ≤ (Real.log (2 * (N : ℝ)) / Real.log 2)
                * (if (N:ℝ) < (Work.FIPlan.gnorm z : ℝ) ∧ Squarefree (Work.FIPlan.gnorm z)
                    then (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) else 0) := by
          intro z hz
          have huz : (Work.FIPlan.gnorm z : ℝ) ≤ 2*(N:ℝ) := hule z hz
          by_cases hsq : Squarefree (Work.FIPlan.gnorm z)
          · by_cases hlt : (N:ℝ) < (Work.FIPlan.gnorm z)
            · rw [if_pos ⟨hlt, hsq⟩]
              have huzN : Work.FIPlan.gnorm z ≤ 2*N := (mem_primAnn_iff.mp hz).2.2.1
              have hω := card_primeFactors_le_log (Work.FIPlan.gnorm z) (2 * (N:ℝ))
                (mem_primAnn_iff.mp hz).2.1 (by exact_mod_cast huzN)
              have hGle : t2G Pz z ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
                simp only [t2G]
                have h1 : (if NoSmallP Pz z then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
                have h2 : |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)| ≤ 1 := by
                  have := ArithmeticFunction.abs_moebius_le_one (n := Work.FIPlan.gnorm z)
                  exact_mod_cast this
                have hτ0 : (0:ℝ) ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
                have hμ0 : (0:ℝ) ≤ |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)| := abs_nonneg _
                calc (if NoSmallP Pz z then (1:ℝ) else 0)
                      * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
                      * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
                    ≤ 1 * 1 * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
                      apply mul_le_mul (mul_le_mul h1 h2 hμ0 (by norm_num)) le_rfl hτ0 (by positivity)
                  _ = (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by ring
              have hP : (∑ i, p i (Work.FIPlan.gnorm z)) ≤ 1 := sum_p_le_one N θ a p ha_le hpsup hsum_le _ huz
              have hP0 : (0:ℝ) ≤ (∑ i, p i (Work.FIPlan.gnorm z)) := sum_p_nonneg p hp0 _
              have hω0 : (0:ℝ) ≤ ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ)) := Nat.cast_nonneg _
              have hτ0 : (0:ℝ) ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
              have hlog0 : (0:ℝ) ≤ Real.log (2 * (N:ℝ)) / Real.log 2 := by
                apply div_nonneg
                · exact Real.log_nonneg (by linarith)
                · exact le_of_lt hlog2
              have hGω : t2G Pz z * ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
                    ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
                      * (Real.log (2 * (N:ℝ)) / Real.log 2) :=
                mul_le_mul hGle hω hω0 hτ0
              calc t2G Pz z * ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
                    * (∑ i, p i (Work.FIPlan.gnorm z))
                  ≤ ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
                      * (Real.log (2 * (N:ℝ)) / Real.log 2)) * 1 := by
                    apply mul_le_mul hGω hP hP0
                    exact mul_nonneg hτ0 hlog0
                _ = (Real.log (2 * (N : ℝ)) / Real.log 2)
                      * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by ring
            · rw [if_neg (fun h => hlt h.1)]
              have hP : (∑ i, p i (Work.FIPlan.gnorm z)) = 0 :=
                sum_p_eq_zero_of_le N a p ha_le (fun i u h => (hpsup i u h).1) _
                  (le_of_not_gt hlt)
              simp [hP]
          · rw [if_neg (fun h => hsq h.2)]
            have hμ0 : ArithmeticFunction.moebius (Work.FIPlan.gnorm z) = 0 :=
              ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
            have hG0 : t2G Pz z = 0 := by simp only [t2G]; rw [hμ0]; simp
            simp [hG0]
        calc (∑ z ∈ primAnn (2 * N),
                t2G Pz z * ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
                  * (∑ i, p i (Work.FIPlan.gnorm z)))
            ≤ ∑ z ∈ primAnn (2 * N), (Real.log (2 * (N : ℝ)) / Real.log 2)
                * (if (N:ℝ) < (Work.FIPlan.gnorm z : ℝ) ∧ Squarefree (Work.FIPlan.gnorm z)
                    then (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) else 0) :=
              Finset.sum_le_sum hA
          _ = (Real.log (2 * (N : ℝ)) / Real.log 2)
                * (∑ z ∈ primAnn (2 * N),
                    (if (N:ℝ) < (Work.FIPlan.gnorm z : ℝ) ∧ Squarefree (Work.FIPlan.gnorm z)
                      then (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) else 0)) := by
              rw [Finset.mul_sum]
          _ ≤ (Real.log (2 * (N : ℝ)) / Real.log 2)
                * (C * (Real.sqrt (N : ℝ) + (N : ℝ)) * (Real.log (2 + (N : ℝ))) ^ (9:ℕ)) := by
              apply mul_le_mul_of_nonneg_left (primAnn_tau_sum_le N hN C hCtau)
              apply div_nonneg
              · exact Real.log_nonneg (by linarith)
              · exact le_of_lt hlog2
      calc (∑ i, ∑ k, ∑ mm ∈ (Finset.Icc (Mn + 1) (2 * Mn)).filter (fun m : ℕ => (m : ℝ) * a i < (x : ℝ)),
            ∑ w ∈ wSph mm, ∑ z ∈ primAnn (2 * N),
              2 * (if Nat.Coprime mm (Work.FIPlan.gnorm z) then (0 : ℝ) else 1)
                * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
          ≤ _ := step1
        _ = _ := step2
        _ = _ := step3
        _ = _ := step4
        _ = _ := step5
        _ ≤ ∑ z ∈ primAnn (2 * N),
              t2G Pz z * ((1600 * (2 * (Mn : ℝ) * (N : ℝ)) ^ ((1:ℝ)/4)
                  * (1 + Real.sqrt (Mn : ℝ) / ((Pz : ℝ) * Real.sqrt (N : ℝ))))
                * ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
                * (∑ i, p i (Work.FIPlan.gnorm z))) := step6
        _ = (1600 * (2 * (Mn : ℝ) * (N : ℝ)) ^ ((1:ℝ)/4)
                * (1 + Real.sqrt (Mn : ℝ) / ((Pz : ℝ) * Real.sqrt (N : ℝ))))
            * (∑ z ∈ primAnn (2 * N),
                t2G Pz z * ((((Work.FIPlan.gnorm z).primeFactors.card : ℕ) : ℝ))
                  * (∑ i, p i (Work.FIPlan.gnorm z))) := step7
        _ ≤ (1600 * (2 * (Mn : ℝ) * (N : ℝ)) ^ ((1:ℝ)/4)
                * (1 + Real.sqrt (Mn : ℝ) / ((Pz : ℝ) * Real.sqrt (N : ℝ))))
            * ((Real.log (2 * (N : ℝ)) / Real.log 2)
              * (C * (Real.sqrt (N : ℝ) + (N : ℝ)) * (Real.log (2 + (N : ℝ))) ^ (9:ℕ))) := by
              apply mul_le_mul_of_nonneg_left step8 (by positivity)
        _ = 1600 * (2 * (Mn : ℝ) * (N : ℝ)) ^ ((1 : ℝ) / 4)
              * (1 + Real.sqrt (Mn : ℝ) / ((Pz : ℝ) * Real.sqrt (N : ℝ)))
              * (Real.log (2 * (N : ℝ)) / Real.log 2)
              * (C * (Real.sqrt (N : ℝ) + (N : ℝ)) * (Real.log (2 + (N : ℝ))) ^ (9:ℕ)) := by ring
    refine le_trans hmain ?_
    exact window_T2_cop_arith C hCpos x N Mn Pz hx hN hMn hPz hN2

end

end Work.FITop4.Red5
