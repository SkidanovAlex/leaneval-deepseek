import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.window_sharp_count_sqfree

set_option maxHeartbeats 2000000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Helper lemmas for the `T3` assembly -/

/-- Membership in `primAnn R`, unfolded. -/
lemma mem_primAnn_assembly {R : ℕ} {z : GaussianInt} :
    z ∈ primAnn R ↔ z ∈ Work.FIPlan.gBox ((R : ℕ) : ℤ) ∧ 1 ≤ Work.FIPlan.gnorm z
      ∧ Work.FIPlan.gnorm z ≤ R ∧ Work.FIPlan.IsPrimary z := by
  simp only [primAnn, Finset.mem_filter]
  tauto

lemma gnorm_le_primAnn_assembly {R : ℕ} {z : GaussianInt} (h : z ∈ primAnn R) :
    Work.FIPlan.gnorm z ≤ R := (mem_primAnn_assembly.mp h).2.2.1

lemma one_le_gnorm_primAnn_assembly {R : ℕ} {z : GaussianInt} (h : z ∈ primAnn R) :
    1 ≤ Work.FIPlan.gnorm z := (mem_primAnn_assembly.mp h).2.1

/-- `cGInd` is dominated by the indicator of `N < n`. -/
lemma cGInd_le_ite_indicator {m N x Pz : ℕ} {τ : ℝ} {n : ℕ} :
    cGInd m N x Pz τ n ≤ (if (N:ℝ) < (n:ℝ) then (1:ℝ) else 0) := by
  by_cases h : cGPred m N x Pz τ n
  · have hNn : N < n := ((cGPred_iff' m N x Pz τ n).mp h).2.1
    have hNn' : (N:ℝ) < (n:ℝ) := by exact_mod_cast hNn
    rw [cGInd, if_pos h, if_pos hNn']
  · rw [cGInd, if_neg h]
    split_ifs <;> norm_num

/-- `∑_i p_i u ≤ 1` for every `u`, from the support and packing hypotheses. -/
lemma sum_p_le_one_all {K : ℕ} (N : ℕ) (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ)
    (ha : ∀ i, (N:ℝ) ≤ a i)
    (hpsup : ∀ i u, p i u ≠ 0 → a i < u)
    (hpsup2 : ∀ i u, p i u ≠ 0 → u ≤ 2*(N:ℝ))
    (hsum_le : ∀ u, (N:ℝ) < u → u ≤ 2*(N:ℝ) → (∑ i, p i u) ≤ 1)
    (u : ℝ) : (∑ i, p i u) ≤ 1 := by
  by_cases h2 : u ≤ 2*(N:ℝ)
  · by_cases h : (N:ℝ) < u
    · exact hsum_le u h h2
    · have h0 : ∀ i, p i u = 0 := by
        intro i
        by_contra hpi
        have h1 := hpsup i u hpi
        have h3 := ha i
        simp only [not_lt] at h
        linarith
      simp [h0]
  · have h0 : ∀ i, p i u = 0 := by
      intro i
      by_contra hpi
      exact h2 (hpsup2 i u hpi)
    simp [h0]

/-- The quarter-power ratio bound: for `1 ≤ N ≤ M`,
`(M^{3/4} N^{-1/4} + (2MN)^{1/4}) N ≤ 3 (MN)^{3/4}`. -/
lemma rpow_quarter_ratio {M N : ℝ} (hM : 0 < M) (hN : 0 < N) (hNM : N ≤ M) :
    (M ^ ((3:ℝ)/4) * N ^ (-(1:ℝ)/4) + (2 * M * N) ^ ((1:ℝ)/4)) * N
      ≤ 3 * (M * N) ^ ((3:ℝ)/4) := by
  have hM0 : 0 ≤ M := le_of_lt hM
  have hN0 : 0 ≤ N := le_of_lt hN
  have hN1 : N ^ (-(1:ℝ)/4) * N = N ^ ((3:ℝ)/4) := by
    have h := Real.rpow_add hN (-(1:ℝ)/4) (1:ℝ)
    rw [Real.rpow_one] at h
    rw [← h]; congr 1; norm_num
  have hMNeq : M ^ ((3:ℝ)/4) * N ^ ((3:ℝ)/4) = (M * N) ^ ((3:ℝ)/4) :=
    (Real.mul_rpow hM0 hN0).symm
  have h2split : (2 * M * N) ^ ((1:ℝ)/4)
      = (2:ℝ) ^ ((1:ℝ)/4) * M ^ ((1:ℝ)/4) * N ^ ((1:ℝ)/4) := by
    rw [show (2:ℝ) * M * N = 2 * (M * N) by ring, Real.mul_rpow (by norm_num) (by positivity),
        Real.mul_rpow hM0 hN0]
    ring
  have hN2 : N ^ ((1:ℝ)/4) * N = N ^ ((5:ℝ)/4) := by
    have h := Real.rpow_add hN ((1:ℝ)/4) (1:ℝ)
    rw [Real.rpow_one] at h
    rw [← h]; congr 1; norm_num
  have hu1 : M ^ ((3:ℝ)/4) * N ^ (-(1:ℝ)/4) * N = (M*N) ^ ((3:ℝ)/4) := by
    rw [mul_assoc, hN1, hMNeq]
  have hN52 : N ^ ((5:ℝ)/4) = N ^ ((1:ℝ)/2) * N ^ ((3:ℝ)/4) := by
    have h := Real.rpow_add hN ((1:ℝ)/2) ((3:ℝ)/4)
    rw [show ((1:ℝ)/2 + (3:ℝ)/4) = (5:ℝ)/4 by norm_num] at h
    exact h
  have hM31 : M ^ ((1:ℝ)/4) * M ^ ((1:ℝ)/2) = M ^ ((3:ℝ)/4) := by
    have h := Real.rpow_add hM ((1:ℝ)/4) ((1:ℝ)/2)
    rw [show ((1:ℝ)/4 + (1:ℝ)/2) = (3:ℝ)/4 by norm_num] at h
    exact h.symm
  have hs : N ^ ((1:ℝ)/2) ≤ M ^ ((1:ℝ)/2) := Real.rpow_le_rpow hN0 hNM (by norm_num)
  have hr2 : (2:ℝ) ^ ((1:ℝ)/4) ≤ 2 := by
    have h4 : ((2:ℝ) ^ ((1:ℝ)/4))^4 = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    rw [← pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
      (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (4:ℕ) ≠ 0)]
    rw [h4]; norm_num
  have hu2 : (2 * M * N) ^ ((1:ℝ)/4) * N ≤ 2 * (M*N) ^ ((3:ℝ)/4) := by
    rw [h2split, mul_assoc, hN2, hN52]
    have hkey : M ^ ((1:ℝ)/4) * N ^ ((1:ℝ)/2) ≤ M ^ ((3:ℝ)/4) := by
      calc M ^ ((1:ℝ)/4) * N ^ ((1:ℝ)/2) ≤ M ^ ((1:ℝ)/4) * M ^ ((1:ℝ)/2) :=
            mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hM0 _)
        _ = M ^ ((3:ℝ)/4) := hM31
    have hN34 : 0 ≤ N ^ ((3:ℝ)/4) := Real.rpow_nonneg hN0 _
    have hM34 : 0 ≤ M ^ ((3:ℝ)/4) := Real.rpow_nonneg hM0 _
    calc (2:ℝ) ^ ((1:ℝ)/4) * M ^ ((1:ℝ)/4) * (N ^ ((1:ℝ)/2) * N ^ ((3:ℝ)/4))
        = (2:ℝ) ^ ((1:ℝ)/4) * (M ^ ((1:ℝ)/4) * N ^ ((1:ℝ)/2)) * N ^ ((3:ℝ)/4) := by ring
      _ ≤ (2:ℝ) ^ ((1:ℝ)/4) * M ^ ((3:ℝ)/4) * N ^ ((3:ℝ)/4) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg (by norm_num) _)) hN34
      _ = (2:ℝ) ^ ((1:ℝ)/4) * (M ^ ((3:ℝ)/4) * N ^ ((3:ℝ)/4)) := by ring
      _ ≤ 2 * (M ^ ((3:ℝ)/4) * N ^ ((3:ℝ)/4)) :=
            mul_le_mul_of_nonneg_right hr2 (mul_nonneg hM34 hN34)
      _ = 2 * (M * N) ^ ((3:ℝ)/4) := by rw [hMNeq]
  calc (M ^ ((3:ℝ)/4) * N ^ (-(1:ℝ)/4) + (2 * M * N) ^ ((1:ℝ)/4)) * N
      = (M ^ ((3:ℝ)/4) * N ^ (-(1:ℝ)/4)) * N + (2 * M * N) ^ ((1:ℝ)/4) * N := by ring
    _ ≤ (M*N) ^ ((3:ℝ)/4) + 2 * (M*N)^((3:ℝ)/4) := add_le_add (le_of_eq hu1) hu2
    _ = 3 * (M*N)^((3:ℝ)/4) := by ring

theorem window_T3_assembly :
      ∀ (c1 C2 : ℝ), 0 < c1 → 0 < C2 →
      (∀ (Mn : ℕ) (z : GaussianInt), 1 ≤ Mn → z ≠ 0 → Squarefree (Work.FIPlan.gnorm z) →
        1 ≤ Work.FIPlan.gnorm z →
        (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ Work.FITop4.Red5.wSph m,
            (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
          ≤ c1 * ((Mn : ℝ) ^ ((3:ℝ)/4) * ((Work.FIPlan.gnorm z : ℝ)) ^ (-(1:ℝ)/4)
              + ((Mn : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1:ℝ)/4))) →
      (∀ (N : ℕ) (θ : ℝ) (K : ℕ) (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ),
        (1 ≤ N) → (0 < θ) → (θ ≤ 1/4) → (1 ≤ θ * (N:ℝ)^((1:ℝ)/2)) →
        (∀ i, (N:ℝ) ≤ a i) → (∀ i u, 0 ≤ p i u) →
        (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) →
        (∀ u, (N:ℝ) < u → u ≤ 2*(N:ℝ) → (∑ i, p i u) ≤ 1) →
        (∀ u, (N:ℝ) + θ*(N:ℝ)/2 < u → u ≤ 2*(N:ℝ) - 2*θ*(N:ℝ) → (∑ i, p i u) = 1) →
        (∑ z ∈ Work.FITop4.Red5.primAnn (2*N),
          (if (N:ℝ) < (Work.FIPlan.gnorm z : ℝ) then (1:ℝ) else 0)
            * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
          ≤ C2 * θ * (N:ℝ) * (Real.log (2*(N:ℝ) + 2))^(100:ℕ)) →
      ∃ c : ℝ, 0 < c ∧
      ∀ (x N Mn Pz : ℕ) (τ θ : ℝ) (K : ℕ)
        (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (Pa : Fin K → Work.FITop.Params),
        (2 ≤ x) → (1 ≤ Mn) → (1 ≤ N) → (2 ≤ Pz) → (0 < θ) → (θ ≤ 1/4) →
        (∀ i, (Pa i).M = (Mn:ℝ)) → (∀ i, (Pa i).N = a i) → (∀ i, (N:ℝ) ≤ a i) →
        (∀ i, (N:ℝ) ≤ (Pa i).N) →
        (∀ i u, 0 ≤ p i u) → (∀ i u, p i u ≤ 1) →
        (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) →
        (∀ i u, p i u ≠ 0 → u ≤ 2*(N:ℝ)) →
        (∀ u, (N:ℝ) < u → u ≤ 2*(N:ℝ) → (∑ i, p i u) ≤ 1) →
        (∀ u, (N:ℝ) + θ*(N:ℝ)/2 < u → u ≤ 2*(N:ℝ) - 2*θ*(N:ℝ) → (∑ i, p i u) = 1) →
        (1 ≤ θ * (N:ℝ)^((1:ℝ)/2)) → ((N:ℝ) ≤ (Mn:ℝ)) →
        (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ Work.FITop4.Red5.wSph m,
            ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
          cGInd m N x Pz τ (Work.FIPlan.gnorm z) * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        ≤ c * θ * ((Mn:ℝ) * (N:ℝ)) ^ ((3:ℝ)/4) * (Real.log (x:ℝ)) ^ (100:ℕ) := by
  intro c1 C2 hc1 hC2 hsharp hwei
  refine ⟨(2:ℝ)^(102:ℕ) * c1 * C2, by positivity, ?_⟩
  intro x N Mn Pz τ θ K a p Pa
    hx hMn hN hPz hθ0 hθ14 hPaM hPaN haN hPaN2 hp0 hp1 hpsup hpsup2 hsum_le hsum_eq hθsq hNMn
  have hMr1 : (1:ℝ) ≤ (Mn:ℝ) := by exact_mod_cast hMn
  have hMr0 : (0:ℝ) < (Mn:ℝ) := by linarith
  have hNr1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNr0 : (0:ℝ) < (N:ℝ) := by linarith
  have hx1 : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  let T : ℕ → GaussianInt → GaussianInt → ℝ := fun m w z =>
      cGInd m N x Pz τ (Work.FIPlan.gnorm z) * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
        * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
  let g : GaussianInt → ℝ := fun z =>
      (if (N:ℝ) < (Work.FIPlan.gnorm z : ℝ) then (1:ℝ) else 0)
        * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
        * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
  let F : GaussianInt → ℝ := fun z =>
      ∑ m ∈ Finset.Icc (Mn+1) (2*Mn), ∑ w ∈ wSph m, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
  change (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N), T m w z)
      ≤ (2:ℝ)^(102:ℕ) * c1 * C2 * θ * ((Mn:ℝ) * (N:ℝ)) ^ ((3:ℝ)/4) * (Real.log (x:ℝ)) ^ (100:ℕ)
  -- `A(z) = 1 - ∑ p_i(|z|²) ≥ 0`
  have hA0 : ∀ z, 0 ≤ 1 - ∑ i, p i (Work.FIPlan.gnorm z) := by
    intro z
    have h := sum_p_le_one_all (K := K) N a p haN (fun i u h => (hpsup i u h).1) hpsup2 hsum_le
      (Work.FIPlan.gnorm z : ℝ)
    linarith
  have hg0 : ∀ z, 0 ≤ g z := by
    intro z
    simp only [g]
    have hind : 0 ≤ (if (N:ℝ) < (Work.FIPlan.gnorm z : ℝ) then (1:ℝ) else 0) := by
      split_ifs <;> norm_num
    have hmuz : 0 ≤ |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)| := abs_nonneg _
    have hd : 0 ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hind (hA0 z)) hmuz) hd
  have hF0 : ∀ z, 0 ≤ F z := by
    intro z
    simp only [F]
    apply Finset.sum_nonneg; intro m _
    apply Finset.sum_nonneg; intro w _
    exact Zint_nonneg _
  -- termwise comparison
  have hterm : ∀ m w z, T m w z ≤ g z * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
    intro m w z
    have hcg := cGInd_le_ite_indicator (m := m) (N := N) (x := x) (Pz := Pz) (τ := τ)
      (n := Work.FIPlan.gnorm z)
    have hZ : 0 ≤ (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := Zint_nonneg _
    have hmuz : 0 ≤ |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)| := abs_nonneg _
    have hd : 0 ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by positivity
    simp only [T, g]
    apply mul_le_mul_of_nonneg_right _ hZ
    apply mul_le_mul_of_nonneg_right _ hd
    apply mul_le_mul_of_nonneg_right _ hmuz
    exact mul_le_mul_of_nonneg_right hcg (hA0 z)
  -- the uniform majorant `B'`
  set B' : ℝ := c1 * ((Mn:ℝ) ^ ((3:ℝ)/4) * (N:ℝ) ^ (-(1:ℝ)/4)
      + (2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4)) with hB'
  have hB'0 : 0 ≤ B' := by
    rw [hB']
    have h1 : 0 ≤ (Mn:ℝ) ^ ((3:ℝ)/4) * (N:ℝ) ^ (-(1:ℝ)/4) := by positivity
    have h2 : 0 ≤ (2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4) := by positivity
    nlinarith [hc1]
  -- per-`z` bound
  have hFB : ∀ z ∈ primAnn (2*N), g z * F z ≤ g z * B' := by
    intro z hz
    by_cases hsf : Squarefree (Work.FIPlan.gnorm z)
    · by_cases hind : (N:ℝ) < (Work.FIPlan.gnorm z : ℝ)
      · have hz1 : 1 ≤ Work.FIPlan.gnorm z := one_le_gnorm_primAnn_assembly hz
        have hzne : z ≠ 0 := by
          intro h0; rw [h0] at hz1; simp [Work.FIPlan.gnorm] at hz1
        have hFz : F z ≤ c1 * ((Mn:ℝ) ^ ((3:ℝ)/4) * (Work.FIPlan.gnorm z : ℝ) ^ (-(1:ℝ)/4)
            + ((Mn:ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1:ℝ)/4)) := by
          have h := hsharp Mn z hMn hzne hsf hz1
          simpa only [F] using h
        have huz : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * (N:ℝ) := by
          have h := gnorm_le_primAnn_assembly hz
          exact_mod_cast h
        have hBB : c1 * ((Mn:ℝ) ^ ((3:ℝ)/4) * (Work.FIPlan.gnorm z : ℝ) ^ (-(1:ℝ)/4)
              + ((Mn:ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1:ℝ)/4)) ≤ B' := by
          rw [hB']
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hc1)
          have h1 : (Work.FIPlan.gnorm z : ℝ) ^ (-(1:ℝ)/4) ≤ (N:ℝ) ^ (-(1:ℝ)/4) :=
            Real.rpow_le_rpow_of_nonpos hNr0 (le_of_lt hind) (by norm_num)
          have h2 : ((Mn:ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1:ℝ)/4)
              ≤ (2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4) := by
            apply Real.rpow_le_rpow _ _ (by norm_num)
            · positivity
            · calc (Mn:ℝ) * (Work.FIPlan.gnorm z : ℝ) ≤ (Mn:ℝ) * (2 * (N:ℝ)) :=
                    mul_le_mul_of_nonneg_left huz (le_of_lt hMr0)
                _ = 2 * (Mn:ℝ) * (N:ℝ) := by ring
          have h3 : (Mn:ℝ) ^ ((3:ℝ)/4) * (Work.FIPlan.gnorm z : ℝ) ^ (-(1:ℝ)/4)
              ≤ (Mn:ℝ) ^ ((3:ℝ)/4) * (N:ℝ) ^ (-(1:ℝ)/4) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
          linarith [h2, h3]
        calc g z * F z ≤ g z * (c1 * ((Mn:ℝ) ^ ((3:ℝ)/4) * (Work.FIPlan.gnorm z : ℝ) ^ (-(1:ℝ)/4)
                + ((Mn:ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1:ℝ)/4))) :=
              mul_le_mul_of_nonneg_left hFz (hg0 z)
          _ ≤ g z * B' := mul_le_mul_of_nonneg_left hBB (hg0 z)
      · have hgz : g z = 0 := by
          simp only [g]
          rw [if_neg hind]
          ring
        rw [hgz]; simp
    · have hmu0 : ArithmeticFunction.moebius (Work.FIPlan.gnorm z) = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
      have hgz : g z = 0 := by
        simp only [g]
        rw [hmu0]
        simp
      rw [hgz]; simp
  -- the main estimate
  have hmain : (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N), T m w z)
      ≤ 3 * c1 * C2 * θ * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4)
          * (Real.log (2*(N:ℝ)+2)) ^ (100:ℕ) := by
    have h1 : (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N), T m w z)
        = ∑ z ∈ primAnn (2*N), ∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m, T m w z := by
      rw [Finset.sum_congr rfl (fun m _ => Finset.sum_comm), Finset.sum_comm]
    rw [h1]
    have hB'Nr : B' * (N:ℝ) ≤ 3 * c1 * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4) := by
      rw [hB']
      have hratio := rpow_quarter_ratio hMr0 hNr0 hNMn
      have : c1 * ((Mn:ℝ) ^ ((3:ℝ)/4) * (N:ℝ) ^ (-(1:ℝ)/4) + (2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4))
            * (N:ℝ)
          = c1 * (((Mn:ℝ) ^ ((3:ℝ)/4) * (N:ℝ) ^ (-(1:ℝ)/4)
              + (2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4)) * (N:ℝ)) := by ring
      rw [this]
      calc c1 * (((Mn:ℝ) ^ ((3:ℝ)/4) * (N:ℝ) ^ (-(1:ℝ)/4)
                + (2 * (Mn:ℝ) * (N:ℝ)) ^ ((1:ℝ)/4)) * (N:ℝ))
          ≤ c1 * (3 * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4)) := mul_le_mul_of_nonneg_left hratio (le_of_lt hc1)
        _ = 3 * c1 * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4) := by ring
    have hlog2N0 : 0 ≤ Real.log (2*(N:ℝ)+2) := Real.log_nonneg (by linarith)
    have hL0 : 0 ≤ (Real.log (2*(N:ℝ)+2)) ^ (100:ℕ) := pow_nonneg hlog2N0 100
    have hC2θL0 : 0 ≤ C2 * θ * (Real.log (2*(N:ℝ)+2)) ^ (100:ℕ) :=
      mul_nonneg (mul_nonneg (le_of_lt hC2) (le_of_lt hθ0)) hL0
    calc ∑ z ∈ primAnn (2*N), ∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m, T m w z
        ≤ ∑ z ∈ primAnn (2*N), g z * F z := by
          apply Finset.sum_le_sum; intro z hz
          calc ∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m, T m w z
              ≤ ∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m,
                  g z * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) :=
                Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun w _ => hterm m w z))
            _ = g z * F z := by
                simp only [F]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl; intro m hm
                rw [Finset.mul_sum]
      _ ≤ ∑ z ∈ primAnn (2*N), g z * B' := Finset.sum_le_sum (fun z hz => hFB z hz)
      _ = B' * (∑ z ∈ primAnn (2*N), g z) := by
          rw [← Finset.sum_mul]; ring
      _ ≤ B' * (C2 * θ * (N:ℝ) * (Real.log (2*(N:ℝ)+2)) ^ (100:ℕ)) := by
          apply mul_le_mul_of_nonneg_left _ hB'0
          simpa only [g] using hwei N θ K a p hN hθ0 hθ14 hθsq haN hp0 hpsup hsum_le hsum_eq
      _ ≤ 3 * c1 * C2 * θ * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4) * (Real.log (2*(N:ℝ)+2)) ^ (100:ℕ) := by
          calc B' * (C2 * θ * (N:ℝ) * (Real.log (2*(N:ℝ)+2)) ^ (100:ℕ))
              = (B' * (N:ℝ)) * (C2 * θ * (Real.log (2*(N:ℝ)+2)) ^ (100:ℕ)) := by ring
            _ ≤ (3 * c1 * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4))
                  * (C2 * θ * (Real.log (2*(N:ℝ)+2)) ^ (100:ℕ)) :=
                mul_le_mul_of_nonneg_right hB'Nr hC2θL0
            _ = 3 * c1 * C2 * θ * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4)
                  * (Real.log (2*(N:ℝ)+2)) ^ (100:ℕ) := by ring
  -- assemble with the logarithm comparison
  have hMN0 : 0 ≤ ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4) := Real.rpow_nonneg (by positivity) _
  by_cases hcase : N < x
  · have h2N2x : 2 * N + 2 ≤ 2 * x := by omega
    have hlog_le : Real.log (2*(N:ℝ)+2) ≤ 2 * Real.log (x:ℝ) := by
      have h1 : Real.log (2*(N:ℝ)+2) ≤ Real.log (2*(x:ℝ)) := by
        apply Real.log_le_log (by positivity)
        have hcast : ((2*N+2 : ℕ) : ℝ) ≤ ((2*x : ℕ) : ℝ) := by exact_mod_cast h2N2x
        push_cast at hcast ⊢
        linarith
      have h2 : Real.log (2*(x:ℝ)) = Real.log 2 + Real.log (x:ℝ) :=
        Real.log_mul (by norm_num) (by positivity)
      have h3 : Real.log 2 ≤ Real.log (x:ℝ) := by
        apply Real.log_le_log (by norm_num)
        exact_mod_cast hx
      linarith
    have hLbound : (Real.log (2*(N:ℝ)+2)) ^ (100:ℕ)
        ≤ (2:ℝ)^(100:ℕ) * (Real.log (x:ℝ)) ^ (100:ℕ) := by
      have h0 : 0 ≤ Real.log (2*(N:ℝ)+2) := Real.log_nonneg (by linarith)
      calc (Real.log (2*(N:ℝ)+2)) ^ (100:ℕ) ≤ (2 * Real.log (x:ℝ)) ^ (100:ℕ) :=
            pow_le_pow_left₀ h0 hlog_le 100
        _ = (2:ℝ)^(100:ℕ) * (Real.log (x:ℝ)) ^ (100:ℕ) := by rw [mul_pow]
    have hlogx0 : 0 ≤ (Real.log (x:ℝ)) ^ (100:ℕ) := pow_nonneg (Real.log_nonneg hx1) 100
    have hcoef0 : 0 ≤ c1 * C2 * θ * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4) * (Real.log (x:ℝ)) ^ (100:ℕ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hc1) (le_of_lt hC2)) (le_of_lt hθ0))
        hMN0) hlogx0
    have hcoef : (3:ℝ) * (2:ℝ)^(100:ℕ) ≤ (2:ℝ)^(102:ℕ) := by
      have h2pow : (2:ℝ)^(102:ℕ) = (2:ℝ)^(100:ℕ) * 4 := by
        rw [show (102:ℕ) = 100 + 2 by norm_num, pow_add]; norm_num
      have h2p : 0 < (2:ℝ)^(100:ℕ) := pow_pos (by norm_num) 100
      rw [h2pow]; nlinarith
    calc (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N), T m w z)
        ≤ 3 * c1 * C2 * θ * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4)
            * (Real.log (2*(N:ℝ)+2)) ^ (100:ℕ) := hmain
      _ ≤ 3 * c1 * C2 * θ * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4)
            * ((2:ℝ)^(100:ℕ) * (Real.log (x:ℝ)) ^ (100:ℕ)) := by
          apply mul_le_mul_of_nonneg_left hLbound
          exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hc1))
            (le_of_lt hC2)) (le_of_lt hθ0)) hMN0
      _ = ((3:ℝ) * (2:ℝ)^(100:ℕ))
            * (c1 * C2 * θ * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4) * (Real.log (x:ℝ)) ^ (100:ℕ)) := by ring
      _ ≤ (2:ℝ)^(102:ℕ)
            * (c1 * C2 * θ * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4) * (Real.log (x:ℝ)) ^ (100:ℕ)) :=
          mul_le_mul_of_nonneg_right hcoef hcoef0
      _ = (2:ℝ)^(102:ℕ) * c1 * C2 * θ * ((Mn:ℝ)*(N:ℝ)) ^ ((3:ℝ)/4)
            * (Real.log (x:ℝ)) ^ (100:ℕ) := by ring
  · have hxN : x ≤ N := by omega
    have hS0 : (∑ m ∈ Finset.Icc (Mn + 1) (2 * Mn), ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N), T m w z) = 0 := by
      apply Finset.sum_eq_zero; intro m hm
      apply Finset.sum_eq_zero; intro w hw
      apply Finset.sum_eq_zero; intro z hz
      have hm1 : 1 ≤ m := by have h := (Finset.mem_Icc.mp hm).1; omega
      have hpred : ¬ cGPred m N x Pz τ (Work.FIPlan.gnorm z) := by
        intro hpred
        have h1 : N < Work.FIPlan.gnorm z :=
          ((cGPred_iff' m N x Pz τ (Work.FIPlan.gnorm z)).mp hpred).2.1
        have h2 : m * Work.FIPlan.gnorm z ≤ x :=
          ((cGPred_iff' m N x Pz τ (Work.FIPlan.gnorm z)).mp hpred).2.2.1
        have h3 : Work.FIPlan.gnorm z ≤ m * Work.FIPlan.gnorm z := by
          calc Work.FIPlan.gnorm z = 1 * Work.FIPlan.gnorm z := by ring
            _ ≤ m * Work.FIPlan.gnorm z := Nat.mul_le_mul_right _ hm1
        omega
      simp only [T, cGInd, if_neg hpred]
      ring
    rw [hS0]
    have hlogx0 : 0 ≤ (Real.log (x:ℝ)) ^ (100:ℕ) := pow_nonneg (Real.log_nonneg hx1) 100
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (le_of_lt hc1))
      (le_of_lt hC2)) (le_of_lt hθ0)) hMN0) hlogx0

end

end Work.FITop4.Red5
