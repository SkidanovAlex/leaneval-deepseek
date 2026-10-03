import Mathlib
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FITop4.Red5.anFI_sum_eq_gauss
import Submission.Work.FITop4.Red5.radial_partition_le
import Submission.Work.FITop4.Red5.angular_partition_le
import Submission.Work.FITop4.Defs4

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# `Work.FITop4.Red5.sieve_step`

The §5.2 "sieve step" of the Friedlander–Iwaniec reduction.
-/

/-! ## The weight and the Gaussian coefficients -/

/-- The sieve weight `μ(n)γ(n;C)` restricted to `N < n`, `(n,Π) = 1` and `τ(n) ≤ τ`. -/
def sieveWeight (N Pz : ℕ) (C τ : ℝ) : ℕ → ℝ :=
  fun n => if N < n ∧ PiCond Pz n ∧ TauCond τ n then
    (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n else 0

/-- The complex coefficient `μ(|z|²)γ(|z|²;C)·Z(Re wz)` on the support
`(|z|²,m) = 1`, `(|z|²,Π) = 1`, `τ(|z|²) ≤ τ`. -/
def ccoef (m Pz : ℕ) (C τ : ℝ) (w z : GaussianInt) : ℂ :=
  if (Nat.Coprime (Work.FIPlan.gnorm z) m ∧ PiCond Pz (Work.FIPlan.gnorm z)
      ∧ TauCond τ (Work.FIPlan.gnorm z)) then
    (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
      * (Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z) : ℂ) * Work.FITop3.Zc w z
  else 0

/-- The real integrand of the `anFI_sum_eq_gauss` right-hand side. -/
def hhcoef (m N Pz : ℕ) (C τ : ℝ) (w z : GaussianInt) : ℝ :=
  if Nat.Coprime m (Work.FIPlan.gnorm z) then
    sieveWeight N Pz C τ (Work.FIPlan.gnorm z)
      * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℕ) : ℝ)
  else 0

/-! ## Elementary lemmas -/

lemma sieveWeight_apply (N Pz : ℕ) (C τ : ℝ) (n : ℕ) :
    sieveWeight N Pz C τ n = if N < n ∧ PiCond Pz n ∧ TauCond τ n then
      (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n else 0 := rfl

lemma atilFIa_eq (n : ℕ) :
    Work.FITop.atilFIa n = ((ArithmeticFunction.moebius n : ℝ))^2 * (Work.FIPlan.anFI n : ℝ) := by
  rw [Work.FITop.atilFIa, Submission.ASP.atil, Submission.ASP.FIa, Submission.an,
    Work.FIPlan.anFI]

lemma moebius_cube (n : ℕ) :
    (ArithmeticFunction.moebius n : ℝ)^3 = (ArithmeticFunction.moebius n : ℝ) := by
  by_cases hs : Squarefree n
  · rw [show (ArithmeticFunction.moebius n : ℝ)^3
        = ((ArithmeticFunction.moebius n : ℝ))^2 * (ArithmeticFunction.moebius n : ℝ) by ring]
    rw [Submission.ASP.moebius_sq_cast n, if_pos hs]; ring
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]; ring

/-- The product of the angular and radial partitions with the coefficient. -/
lemma integrand_eq (m Pz : ℕ) (C τ : ℝ) (α : ℝ) (w z : GaussianInt) :
    (if (Nat.Coprime (Work.FIPlan.gnorm z) m ∧ PiCond Pz (Work.FIPlan.gnorm z)
        ∧ TauCond τ (Work.FIPlan.gnorm z)) then
        ((α : ℂ) * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
          * (Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z) : ℂ) * Work.FITop3.Zc w z)
      else 0)
      = (α : ℂ) * ccoef m Pz C τ w z := by
  rw [ccoef]
  by_cases h : (Nat.Coprime (Work.FIPlan.gnorm z) m ∧ PiCond Pz (Work.FIPlan.gnorm z)
      ∧ TauCond τ (Work.FIPlan.gnorm z))
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h]; ring

/-! ## The abstract per-`w` partition bound -/

/-- Splitting the coefficient sum by the two pieces of the annulus. -/
lemma norm_sum_le_of_partition {ι : Type*} [DecidableEq ι] {K K' : ℕ}
    (Zall Zsm : Finset ι) (hsub : Zsm ⊆ Zall)
    (cc : ι → ℂ) (α : Fin K' → Fin K → ι → ℝ)
    (hbg : ∀ z ∈ Zall, z ∉ Zsm → ∑ k, ∑ i, α k i z = 1)
    (hsm0 : ∀ z ∈ Zsm, 0 ≤ ∑ k, ∑ i, α k i z)
    (hsm1 : ∀ z ∈ Zsm, ∑ k, ∑ i, α k i z ≤ 1) :
    ‖∑ z ∈ Zall, cc z‖
      ≤ (∑ k, ∑ i, ‖∑ z ∈ Zall, (((α k i z : ℝ)) : ℂ) * cc z‖)
      + ∑ z ∈ Zsm, ‖cc z‖ := by
  set M : ℂ := ∑ z ∈ Zall, (((∑ k, ∑ i, α k i z : ℝ)) : ℂ) * cc z with hMdef
  have hR : M = ∑ k : Fin K', ∑ i : Fin K, ∑ z ∈ Zall, (((α k i z : ℝ)) : ℂ) * cc z := by
    rw [hMdef]
    have hf : ∀ z, (((∑ k : Fin K', ∑ i : Fin K, α k i z : ℝ)) : ℂ)
        = ∑ k : Fin K', ∑ i : Fin K, (((α k i z : ℝ)) : ℂ) := by
      intro z; push_cast; rfl
    have step : ∀ z, (∑ k : Fin K', ∑ i : Fin K, (((α k i z : ℝ)) : ℂ)) * cc z
        = ∑ k : Fin K', ∑ i : Fin K, (((α k i z : ℝ)) : ℂ) * cc z := by
      intro z
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_mul]
    simp only [hf, step]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro k _
    exact Finset.sum_comm
  have hMle : ‖M‖ ≤ ∑ k, ∑ i, ‖∑ z ∈ Zall, (((α k i z : ℝ)) : ℂ) * cc z‖ := by
    rw [hR]
    refine (norm_sum_le Finset.univ (fun k : Fin K' => ∑ i : Fin K,
      ∑ z ∈ Zall, (((α k i z : ℝ)) : ℂ) * cc z)).trans ?_
    apply Finset.sum_le_sum; intro k _
    exact norm_sum_le Finset.univ (fun i : Fin K =>
      ∑ z ∈ Zall, (((α k i z : ℝ)) : ℂ) * cc z)
  have hLM : ‖(∑ z ∈ Zall, cc z) - M‖ ≤ ∑ z ∈ Zsm, ‖cc z‖ := by
    have hdiff : (∑ z ∈ Zall, cc z) - M
        = ∑ z ∈ Zall, (((1:ℝ) - (∑ k, ∑ i, α k i z : ℝ) : ℝ) : ℂ) * cc z := by
      rw [hMdef, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro z _
      push_cast
      ring
    have h0 : ∀ z ∈ Zall, z ∉ Zsm →
        (((1:ℝ) - (∑ k, ∑ i, α k i z : ℝ) : ℝ) : ℂ) * cc z = 0 := by
      intro z hz hzns
      rw [hbg z hz hzns]
      simp
    rw [hdiff, (Finset.sum_subset hsub h0).symm]
    calc ‖∑ z ∈ Zsm, (((1:ℝ) - (∑ k, ∑ i, α k i z : ℝ) : ℝ) : ℂ) * cc z‖
        ≤ ∑ z ∈ Zsm, ‖(((1:ℝ) - (∑ k, ∑ i, α k i z : ℝ) : ℝ) : ℂ) * cc z‖ :=
          norm_sum_le _ _
      _ = ∑ z ∈ Zsm, ‖(((1:ℝ) - (∑ k, ∑ i, α k i z : ℝ) : ℝ) : ℂ)‖ * ‖cc z‖ := by
          apply Finset.sum_congr rfl; intro z _; rw [norm_mul]
      _ ≤ ∑ z ∈ Zsm, 1 * ‖cc z‖ := by
          apply Finset.sum_le_sum; intro z hz
          have h1 := hsm0 z hz
          have h2 := hsm1 z hz
          have h3 : ‖(((1:ℝ) - (∑ k, ∑ i, α k i z : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
            constructor <;> linarith
          exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = ∑ z ∈ Zsm, ‖cc z‖ := by simp
  have htri : ‖∑ z ∈ Zall, cc z‖ ≤ ‖M‖ + ‖(∑ z ∈ Zall, cc z) - M‖ := by
    have h := norm_add_le M ((∑ z ∈ Zall, cc z) - M)
    have h2 : M + ((∑ z ∈ Zall, cc z) - M) = ∑ z ∈ Zall, cc z := by abel
    rw [h2] at h
    exact h
  linarith [hMle, hLM]

/-! ## The Gaussian reduction (the `m` squarefree case) -/

/-- **The Gaussian identity for the sieve step.** -/
lemma gauss_reduction (m N Pz : ℕ) (C τ : ℝ) (hm : 1 ≤ m) (hN : 1 ≤ N)
    (hsf : Squarefree m) :
    (∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0))
      = (1 / 4) *
        (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m),
          ∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
                (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ)
                  ∧ Work.FIPlan.gnorm z ≤ 2 * N),
            ccoef m Pz C τ w z).re := by
  set Wset := (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m)
    with hWset
  set Zl := (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
    (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ 2 * N) with hZl
  set Zall := (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
    (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ) ∧ Work.FIPlan.gnorm z ≤ 2 * N) with hZall
  -- (1) rewrite the atilFIa-sum as an anFI-sum
  have hT1 : (∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0))
      = ∑ n ∈ Finset.Icc 1 (2 * N),
        (if Nat.Coprime m n then
          sieveWeight N Pz C τ n * (Work.FIPlan.anFI (m * n) : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [sieveWeight_apply]
    by_cases hc : N < n ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
    · obtain ⟨hNn, hcop, hpi, htau⟩ := hc
      rw [if_pos ⟨hNn, hcop, hpi, htau⟩, if_pos hcop.symm, if_pos ⟨hNn, hpi, htau⟩]
      have hatil : Work.FITop.atilFIa (m * n)
          = ((ArithmeticFunction.moebius n : ℝ))^2 * (Work.FIPlan.anFI (m * n) : ℝ) := by
        rw [atilFIa_eq]
        congr 1
        rw [Submission.ASP.moebius_sq_cast (m * n), Submission.ASP.moebius_sq_cast n]
        have hsfeq : Squarefree (m * n) ↔ Squarefree n := by
          rw [Nat.squarefree_mul hcop.symm]; exact and_iff_right hsf
        by_cases hsn : Squarefree n
        · rw [if_pos (hsfeq.mpr hsn), if_pos hsn]
        · rw [if_neg (fun h => hsn (hsfeq.mp h)), if_neg hsn]
      rw [hatil]
      have hsq : (ArithmeticFunction.moebius n : ℝ) * (ArithmeticFunction.moebius n : ℝ)^2
          = (ArithmeticFunction.moebius n : ℝ) := by
        rw [show (ArithmeticFunction.moebius n : ℝ) * (ArithmeticFunction.moebius n : ℝ)^2
            = (ArithmeticFunction.moebius n : ℝ)^3 by ring, moebius_cube]
      rw [show (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * (((ArithmeticFunction.moebius n : ℝ))^2 * (Work.FIPlan.anFI (m * n) : ℝ))
          = ((ArithmeticFunction.moebius n : ℝ) * (ArithmeticFunction.moebius n : ℝ)^2)
            * (Work.FIPlan.gammaTrunc C n * (Work.FIPlan.anFI (m * n) : ℝ)) by ring,
          hsq]
      ring
    · rw [if_neg hc]
      by_cases hcop : Nat.Coprime m n
      · rw [if_pos hcop]
        have hnot : ¬(N < n ∧ PiCond Pz n ∧ TauCond τ n) := by
          intro h; exact hc ⟨h.1, hcop.symm, h.2.1, h.2.2⟩
        simp [hnot]
      · rw [if_neg hcop]
  rw [hT1]
  -- (2) the Gaussian identity
  have hgauss := anFI_sum_eq_gauss m N hm hN (sieveWeight N Pz C τ)
  rw [hgauss, ← hWset, ← hZl]
  -- (3) restrict the inner `z`-range from `(1,2N]` to `(N,2N]`, and cast to `ℂ`
  have hZallZl : Zall ⊆ Zl := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    obtain ⟨hzbox, hNlt, hle⟩ := hz
    have h1 : 1 ≤ Work.FIPlan.gnorm z := by
      have : (1:ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by
        have hNr : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
        linarith
      exact_mod_cast this
    exact ⟨hzbox, h1, hle⟩
  have hzero : ∀ w ∈ Wset, ∀ z ∈ Zl, z ∉ Zall → hhcoef m N Pz C τ w z = 0 := by
    intro w _ z hz hzns
    obtain ⟨hzbox, -, hle⟩ := Finset.mem_filter.mp hz
    have hleN : (Work.FIPlan.gnorm z : ℝ) ≤ (N:ℝ) := by
      by_contra h
      exact hzns (Finset.mem_filter.mpr ⟨hzbox, not_le.mp h, hle⟩)
    rw [hhcoef, sieveWeight_apply]
    by_cases hcop : Nat.Coprime m (Work.FIPlan.gnorm z)
    · rw [if_pos hcop]
      have hnot : ¬(N < Work.FIPlan.gnorm z ∧ PiCond Pz (Work.FIPlan.gnorm z)
          ∧ TauCond τ (Work.FIPlan.gnorm z)) := by
        intro h
        have : (N:ℝ) < (Work.FIPlan.gnorm z : ℝ) := by exact_mod_cast h.1
        linarith
      rw [if_neg hnot]; ring
    · rw [if_neg hcop]
  have hcast : ∀ w z, z ∈ Zall → ((hhcoef m N Pz C τ w z : ℝ) : ℂ) = ccoef m Pz C τ w z := by
    intro w z hz
    obtain ⟨-, hNlt, -⟩ := Finset.mem_filter.mp hz
    rw [hhcoef, sieveWeight_apply, ccoef]
    by_cases hcop : Nat.Coprime m (Work.FIPlan.gnorm z)
    · rw [if_pos hcop]
      by_cases hpt : PiCond Pz (Work.FIPlan.gnorm z) ∧ TauCond τ (Work.FIPlan.gnorm z)
      · rw [if_pos ⟨Nat.cast_lt.mp hNlt, hpt.1, hpt.2⟩,
          if_pos ⟨hcop.symm, hpt.1, hpt.2⟩]
        rw [Work.FITop3.Zc]
        push_cast
        ring
      · rw [if_neg (fun h => hpt ⟨h.2.1, h.2.2⟩),
          if_neg (fun h => hpt ⟨h.2.1, h.2.2⟩)]
        simp
    · rw [if_neg hcop, if_neg (fun h => hcop h.1.symm)]; simp
  have hgoal : (∑ w ∈ Wset, ∑ z ∈ Zl, hhcoef m N Pz C τ w z)
      = (∑ w ∈ Wset, ∑ z ∈ Zall, ccoef m Pz C τ w z).re := by
    have hrange : (∑ w ∈ Wset, ∑ z ∈ Zl, hhcoef m N Pz C τ w z)
        = (∑ w ∈ Wset, ∑ z ∈ Zall, hhcoef m N Pz C τ w z) := by
      apply Finset.sum_congr rfl; intro w hw
      exact (Finset.sum_subset hZallZl (fun z hz hzns => hzero w hw z hz hzns)).symm
    rw [hrange]
    have hcast2 : (((∑ w ∈ Wset, ∑ z ∈ Zall, hhcoef m N Pz C τ w z) : ℝ) : ℂ)
        = (∑ w ∈ Wset, ∑ z ∈ Zall, ccoef m Pz C τ w z) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl; intro w _
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl; intro z hz
      exact hcast w z hz
    rw [← hcast2, Complex.ofReal_re]
  change (1 / 4) * (∑ w ∈ Wset, ∑ z ∈ Zl, hhcoef m N Pz C τ w z)
      = (1 / 4) * (∑ w ∈ Wset, ∑ z ∈ Zall, ccoef m Pz C τ w z).re
  rw [hgoal]


/-! ## The bilinear bound -/

/-- **The bilinear bound of the sieve step.**  The Gaussian double sum of `ccoef` on the annulus
`N < |z|² ≤ 2N` is bounded by the two pieces of the radial/angular partition. -/
lemma ccoef_bound (m N Pz : ℕ) (C τ θ : ℝ) (hN : 1 ≤ N) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    {K K' : ℕ} (p : Fin K → ℝ → ℝ) (q : Fin K' → ℝ → ℝ) (φ : Fin K' → ℝ)
    (hp0 : ∀ i u, 0 ≤ p i u)
    (hple : ∀ u : ℝ, (N : ℝ) < u → u ≤ (N : ℝ) + θ * (N : ℝ) / 2 →
      (∑ i, p i u) ≤ 1)
    (hpart : ∀ u : ℝ, (N : ℝ) + θ * (N : ℝ) / 2 < u → u ≤ 2 * (N : ℝ) →
      (∑ i, p i u) = 1)
    (hq0 : ∀ k α, 0 ≤ q k α)
    (hang : ∀ α : ℝ, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1) :
    ‖∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m),
        ∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
              (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ)
                ∧ Work.FIPlan.gnorm z ≤ 2 * N),
          ccoef m Pz C τ w z‖
      ≤ (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
            (fun w => Work.FIPlan.gnorm w = m),
          ∑ k : Fin K', ∑ i : Fin K,
            ‖∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
                  (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ)
                    ∧ Work.FIPlan.gnorm z ≤ 2 * N),
                (if Nat.Coprime (Work.FIPlan.gnorm z) m ∧ PiCond Pz (Work.FIPlan.gnorm z)
                    ∧ TauCond τ (Work.FIPlan.gnorm z) then
                    (((q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z) : ℝ) : ℂ)
                    * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
                    * (Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z) : ℂ)
                    * Work.FITop3.Zc w z)
                  else 0)‖)
        + (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
            (fun w => Work.FIPlan.gnorm w = m),
          ∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
                (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ)
                  ∧ (Work.FIPlan.gnorm z : ℝ) ≤ (N : ℝ) + θ * (N : ℝ) / 2),
            ‖(if Nat.Coprime (Work.FIPlan.gnorm z) m ∧ PiCond Pz (Work.FIPlan.gnorm z)
                ∧ TauCond τ (Work.FIPlan.gnorm z) then
                (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
                * (Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z) : ℂ)
                * Work.FITop3.Zc w z
              else 0)‖) := by
  set Wset := (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m)
    with hWset
  set Zall := (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
    (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ) ∧ Work.FIPlan.gnorm z ≤ 2 * N) with hZall
  set Zsm := (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
    (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ)
      ∧ (Work.FIPlan.gnorm z : ℝ) ≤ (N : ℝ) + θ * (N : ℝ) / 2) with hZsm
  set R1raw := (∑ w ∈ Wset, ∑ k : Fin K', ∑ i : Fin K,
        ‖∑ z ∈ Zall,
            (if Nat.Coprime (Work.FIPlan.gnorm z) m ∧ PiCond Pz (Work.FIPlan.gnorm z)
                ∧ TauCond τ (Work.FIPlan.gnorm z) then
                (((q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z) : ℝ) : ℂ)
                * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
                * (Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z) : ℂ)
                * Work.FITop3.Zc w z)
              else 0)‖) with hR1raw
  set R2raw := (∑ w ∈ Wset, ∑ z ∈ Zsm,
        ‖(if Nat.Coprime (Work.FIPlan.gnorm z) m ∧ PiCond Pz (Work.FIPlan.gnorm z)
            ∧ TauCond τ (Work.FIPlan.gnorm z) then
            (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
            * (Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z) : ℂ)
            * Work.FITop3.Zc w z
          else 0)‖) with hR2raw
  set R1 := (∑ w ∈ Wset, ∑ k : Fin K', ∑ i : Fin K,
      ‖∑ z ∈ Zall, (((q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z) : ℝ) : ℂ)
        * ccoef m Pz C τ w z)‖) with hR1
  set R2 := (∑ w ∈ Wset, ∑ z ∈ Zsm, ‖ccoef m Pz C τ w z‖) with hR2
  have hZsmZall : Zsm ⊆ Zall := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    obtain ⟨hzbox, hNlt, hle⟩ := hz
    refine ⟨hzbox, hNlt, ?_⟩
    have hNr : (0:ℝ) ≤ (N:ℝ) := by positivity
    have hth : θ * (N:ℝ) / 2 ≤ (N:ℝ) := by
      have h2 : θ / 2 ≤ 1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h2 hNr]
    have : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * (N:ℝ) := by linarith
    exact_mod_cast this
  have hbg : ∀ z ∈ Zall, z ∉ Zsm →
      (∑ k : Fin K', ∑ i : Fin K,
        q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)) = 1 := by
    intro z hz hzns
    obtain ⟨hzbox, hNlt, hle2N⟩ := Finset.mem_filter.mp hz
    have hgt : (N:ℝ) + θ * (N:ℝ) / 2 < (Work.FIPlan.gnorm z : ℝ) := by
      by_contra h
      exact hzns (Finset.mem_filter.mpr ⟨hzbox, hNlt, le_of_not_gt h⟩)
    have hle2Nr : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * (N:ℝ) := by exact_mod_cast hle2N
    have hpsum := hpart (Work.FIPlan.gnorm z) hgt hle2Nr
    have hqsum := hang (Complex.arg z.toComplex)
      (le_of_lt (Complex.neg_pi_lt_arg _)) (Complex.arg_le_pi _)
    rw [← Finset.sum_mul_sum, hqsum, hpsum]; ring
  have hsm0 : ∀ z ∈ Zsm,
      0 ≤ (∑ k : Fin K', ∑ i : Fin K,
        q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)) := by
    intro z _
    apply Finset.sum_nonneg; intro k _
    apply Finset.sum_nonneg; intro i _
    exact mul_nonneg (hq0 _ _) (hp0 _ _)
  have hsm1 : ∀ z ∈ Zsm,
      (∑ k : Fin K', ∑ i : Fin K,
        q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)) ≤ 1 := by
    intro z hz
    obtain ⟨-, hNlt, hle⟩ := Finset.mem_filter.mp hz
    have hpsum := hple (Work.FIPlan.gnorm z) hNlt hle
    have hqsum := hang (Complex.arg z.toComplex)
      (le_of_lt (Complex.neg_pi_lt_arg _)) (Complex.arg_le_pi _)
    rw [← Finset.sum_mul_sum, hqsum, one_mul]
    exact hpsum
  have hbound : ‖∑ w ∈ Wset, ∑ z ∈ Zall, ccoef m Pz C τ w z‖ ≤ R1 + R2 := by
    rw [hR1, hR2]
    calc ‖∑ w ∈ Wset, ∑ z ∈ Zall, ccoef m Pz C τ w z‖
        ≤ ∑ w ∈ Wset, ‖∑ z ∈ Zall, ccoef m Pz C τ w z‖ := norm_sum_le Wset _
      _ ≤ ∑ w ∈ Wset, ((∑ k : Fin K', ∑ i : Fin K,
            ‖∑ z ∈ Zall, (((q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * ccoef m Pz C τ w z)‖)
          + ∑ z ∈ Zsm, ‖ccoef m Pz C τ w z‖) := by
          apply Finset.sum_le_sum; intro w _
          exact norm_sum_le_of_partition Zall Zsm hZsmZall (ccoef m Pz C τ w)
            (fun k i z => q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z))
            hbg hsm0 hsm1
      _ = (∑ w ∈ Wset, ∑ k : Fin K', ∑ i : Fin K,
            ‖∑ z ∈ Zall, (((q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * ccoef m Pz C τ w z)‖)
          + ∑ w ∈ Wset, ∑ z ∈ Zsm, ‖ccoef m Pz C τ w z‖ := by
          rw [Finset.sum_add_distrib]
  have hA : R1raw = R1 := by
    rw [hR1raw, hR1]
    apply Finset.sum_congr rfl; intro w _
    apply Finset.sum_congr rfl; intro k _
    apply Finset.sum_congr rfl; intro i _
    congr 1
    apply Finset.sum_congr rfl; intro z _
    exact integrand_eq m Pz C τ _ w z
  have hB : R2raw = R2 := by
    rw [hR2raw, hR2]
    apply Finset.sum_congr rfl; intro w _
    apply Finset.sum_congr rfl; intro z _
    rw [ccoef]
  rw [hA, hB]
  exact hbound



/-! ## The sieve step -/

theorem sieve_step (m N Pz : ℕ) (C τ θ : ℝ)
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    {K K' : ℕ} (p : Fin K → ℝ → ℝ) (q : Fin K' → ℝ → ℝ) (φ : Fin K' → ℝ)
    (hp0 : ∀ i u, 0 ≤ p i u) (hp1 : ∀ i u, p i u ≤ 1)
    (hple : ∀ u : ℝ, (N : ℝ) < u → u ≤ (N : ℝ) + θ * (N : ℝ) / 2 → (∑ i, p i u) ≤ 1)
    (hpart : ∀ u : ℝ, (N : ℝ) + θ * (N : ℝ) / 2 < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) = 1)
    (hq0 : ∀ k α, 0 ≤ q k α) (hq1 : ∀ k α, q k α ≤ 1)
    (hqs : ∀ k α, q k α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hang : ∀ α : ℝ, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1) :
    |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
      ≤ (1 / 4) * ∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
            (fun w => Work.FIPlan.gnorm w = m),
          ∑ k : Fin K', ∑ i : Fin K,
            ‖∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
                  (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ) ∧ Work.FIPlan.gnorm z ≤ 2 * N),
                (if Nat.Coprime (Work.FIPlan.gnorm z) m ∧ PiCond Pz (Work.FIPlan.gnorm z)
                    ∧ TauCond τ (Work.FIPlan.gnorm z) then (((q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z) : ℝ) : ℂ)
                    * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
                    * (Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z) : ℂ)
                    * Work.FITop3.Zc w z)
                  else 0)‖
        + (1 / 4) * ∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
            (fun w => Work.FIPlan.gnorm w = m),
          ∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
                (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ)
                  ∧ (Work.FIPlan.gnorm z : ℝ) ≤ (N : ℝ) + θ * (N : ℝ) / 2),
            ‖(if Nat.Coprime (Work.FIPlan.gnorm z) m ∧ PiCond Pz (Work.FIPlan.gnorm z)
                ∧ TauCond τ (Work.FIPlan.gnorm z) then (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
                * (Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z) : ℂ)
                * Work.FITop3.Zc w z
              else 0)‖ := by
  classical
  set RHS1 := ∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
            (fun w => Work.FIPlan.gnorm w = m),
          ∑ k : Fin K', ∑ i : Fin K,
            ‖∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
                  (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ) ∧ Work.FIPlan.gnorm z ≤ 2 * N),
                (if Nat.Coprime (Work.FIPlan.gnorm z) m ∧ PiCond Pz (Work.FIPlan.gnorm z)
                    ∧ TauCond τ (Work.FIPlan.gnorm z) then (((q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z) : ℝ) : ℂ)
                    * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
                    * (Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z) : ℂ)
                    * Work.FITop3.Zc w z)
                  else 0)‖ with hRHS1def
  set RHS2 := ∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter
            (fun w => Work.FIPlan.gnorm w = m),
          ∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
                (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ)
                  ∧ (Work.FIPlan.gnorm z : ℝ) ≤ (N : ℝ) + θ * (N : ℝ) / 2),
            ‖(if Nat.Coprime (Work.FIPlan.gnorm z) m ∧ PiCond Pz (Work.FIPlan.gnorm z)
                ∧ TauCond τ (Work.FIPlan.gnorm z) then (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
                * (Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z) : ℂ)
                * Work.FITop3.Zc w z
              else 0)‖ with hRHS2def
  set Lc := ∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m),
          ∑ z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
                (fun z => (N : ℝ) < (Work.FIPlan.gnorm z : ℝ)
                  ∧ Work.FIPlan.gnorm z ≤ 2 * N),
            ccoef m Pz C τ w z with hLcdef
  by_cases hsf : Squarefree m
  · have hred := gauss_reduction m N Pz C τ hm hN hsf
    rw [← hLcdef] at hred
    have hbound := ccoef_bound m N Pz C τ θ hN hθ hθ1 p q φ hp0 hple hpart hq0 hang
    rw [← hLcdef] at hbound
    rw [← hRHS1def, ← hRHS2def] at hbound
    calc |(∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0))|
        = |(1 / 4) * Lc.re| := by rw [hred]
      _ = (1 / 4) * |Lc.re| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/4)]
      _ ≤ (1 / 4) * ‖Lc‖ := by
          have h4 : (0:ℝ) ≤ 1/4 := by norm_num
          nlinarith [mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm Lc) h4]
      _ ≤ (1 / 4) * (RHS1 + RHS2) := by
          have h4 : (0:ℝ) ≤ 1/4 := by norm_num
          nlinarith [mul_le_mul_of_nonneg_left hbound h4]
      _ = (1 / 4) * RHS1 + (1 / 4) * RHS2 := by ring
  · have hT0 : (∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro n _
      by_cases hc : N < n ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
      · rw [if_pos hc]
        have hatil0 : Work.FITop.atilFIa (m * n) = 0 := by
          rw [atilFIa_eq, Submission.ASP.moebius_sq_cast (m * n),
            if_neg (fun h => hsf (Squarefree.of_mul_left h))]
          ring
        rw [hatil0]; ring
      · rw [if_neg hc]
    rw [hT0, abs_zero]
    have hR1 : 0 ≤ RHS1 := by
      apply Finset.sum_nonneg; intro w _
      apply Finset.sum_nonneg; intro k _
      apply Finset.sum_nonneg; intro i _
      exact norm_nonneg _
    have hR2 : 0 ≤ RHS2 := by
      apply Finset.sum_nonneg; intro w _
      apply Finset.sum_nonneg; intro z _
      exact norm_nonneg _
    have h4 : (0:ℝ) ≤ 1/4 := by norm_num
    nlinarith [mul_nonneg h4 hR1, mul_nonneg h4 hR2]

end

end Work.FITop4.Red5
