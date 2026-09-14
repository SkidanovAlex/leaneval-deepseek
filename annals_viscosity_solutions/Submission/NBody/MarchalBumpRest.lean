import Submission.NBody.MarchalBumpTransfer

/-!
# The interaction-potential (`U_rest`) difference of the symmetric bump

Part of the assembly of Marchal's theorem (`Submission/ROADMAP.md`, SESSION 30): the symmetric bump
moves only the bodies of the colliding cluster `k`, and moves each of them by at most
`λ^{2/3}‖δ‖`.  Since the cluster is `ν`-separated from the other bodies, the interaction potential
`U_rest` changes by at most `(∑ mᵢmⱼ)·2λ^{2/3}‖δ‖/ν²` — which, multiplied by `λ`, is the
`O(λ^{5/3}‖δ‖)` term of the transfer identity.

All results in this file are fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- The elementary bound for one cross pair of the interaction potential. -/
lemma cross_term_le {k : Finset (Fin N)} {x y : EN E N} {ν ρ : ℝ}
    {i j : Fin N} (hsep : ClusterSeparatedWeak k x ν) (hi : i ∈ k) (hj : j ∉ k)
    (hν : 0 < ν) (hρ : 0 ≤ ρ) (hρν : 2 * ρ ≤ ν)
    (hpert : ‖(x i - x j) - (y i - y j)‖ ≤ ρ) :
    (r y i j)⁻¹ - (r x i j)⁻¹ ≤ 2 * ρ / ν ^ 2 := by
  have hbx : ν ≤ r x i j := hsep i hi j hj
  have hbxpos : (0:ℝ) < r x i j := lt_of_lt_of_le hν hbx
  have hnum : r x i j - r y i j ≤ ρ := by
    have h := (abs_le.mp (abs_norm_sub_norm_le (x i - x j) (y i - y j))).2
    rw [r_eq_norm_sub, r_eq_norm_sub]
    linarith
  have hay : ν / 2 ≤ r y i j := by linarith
  have haypos : (0:ℝ) < r y i j := by linarith
  have hid : (r y i j)⁻¹ - (r x i j)⁻¹ = (r x i j - r y i j) / (r y i j * r x i j) := by
    field_simp
  have hden : (ν / 2) * ν ≤ r y i j * r x i j :=
    mul_le_mul hay hbx hν.le haypos.le
  have hνhalf : (0:ℝ) < (ν / 2) * ν := mul_pos (by linarith) hν
  rw [hid]
  calc (r x i j - r y i j) / (r y i j * r x i j)
      ≤ ρ / (r y i j * r x i j) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ ρ / ((ν / 2) * ν) := div_le_div_of_nonneg_left hρ hνhalf hden
    _ = 2 * ρ / ν ^ 2 := by field_simp

/-- The mirrored form of `cross_term_le`: the body of the pair which lies in `k` is the second one. -/
lemma cross_term_le_swap {k : Finset (Fin N)} {x y : EN E N} {ν ρ : ℝ}
    {i j : Fin N} (hsep : ClusterSeparatedWeak k x ν) (hj : j ∈ k) (hi : i ∉ k)
    (hν : 0 < ν) (hρ : 0 ≤ ρ) (hρν : 2 * ρ ≤ ν)
    (hpert : ‖(x i - x j) - (y i - y j)‖ ≤ ρ) :
    (r y i j)⁻¹ - (r x i j)⁻¹ ≤ 2 * ρ / ν ^ 2 := by
  have hsym1 : r y i j = r y j i := by
    rw [r_eq_norm_sub, r_eq_norm_sub, norm_sub_rev]
  have hsym2 : r x i j = r x j i := by
    rw [r_eq_norm_sub, r_eq_norm_sub, norm_sub_rev]
  have hpert' : ‖(x j - x i) - (y j - y i)‖ ≤ ρ := by
    have he : (x j - x i) - (y j - y i) = -((x i - x j) - (y i - y j)) := by abel
    rw [he, norm_neg]
    exact hpert
  rw [hsym1, hsym2]
  exact cross_term_le (k := k) (x := x) (y := y) (ν := ν) (ρ := ρ) (i := j) (j := i)
    hsep hj hi hν hρ hρν hpert'

/-- **The interaction-potential difference of a small perturbation.**  A perturbation which moves
only the bodies of `k`, and moves each of them by at most `ρ`, changes the interaction potential
`U_rest` by at most `(∑ mᵢmⱼ)·2ρ/ν²` as long as the cluster stays `ν`-separated. -/
lemma clusterPotentialRest_diff_le {m : Fin N → ℝ} (hm : ∀ i, 0 ≤ m i) {k : Finset (Fin N)}
    {x y : EN E N} {ν ρ : ℝ} (hν : 0 < ν) (hρ : 0 ≤ ρ) (hρν : 2 * ρ ≤ ν)
    (hsep : ClusterSeparatedWeak k x ν) (hclose : ∀ j ∉ k, y j = x j)
    (hclose' : ∀ j ∈ k, ‖y j - x j‖ ≤ ρ) :
    clusterPotentialRest m k y - clusterPotentialRest m k x
      ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
            m p.1 * m p.2) * (2 * ρ / ν ^ 2) := by
  classical
  have hν2 : (0:ℝ) < (ν / 2) * ν := mul_pos (by linarith) hν
  have hdivnn : 0 ≤ 2 * ρ / ν ^ 2 := div_nonneg (by linarith) (sq_nonneg ν)
  rw [clusterPotentialRest, clusterPotentialRest, ← Finset.sum_sub_distrib]
  have hterm : ∀ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
      m p.1 * m p.2 * (r y p.1 p.2)⁻¹ - m p.1 * m p.2 * (r x p.1 p.2)⁻¹
        ≤ m p.1 * m p.2 * (2 * ρ / ν ^ 2) := by
    intro p hp
    have hpmem : ¬ (p.1 ∈ k ∧ p.2 ∈ k) := (Finset.mem_filter.mp hp).2
    have hlt : p.1 ≠ p.2 := by
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      omega
    have hmm : 0 ≤ m p.1 * m p.2 := mul_nonneg (hm p.1) (hm p.2)
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ hmm
    by_cases h1 : p.1 ∈ k
    · by_cases h2 : p.2 ∈ k
      · exact absurd ⟨h1, h2⟩ hpmem
      · -- p.1 ∈ k, p.2 ∉ k : only body `p.1` moves
        have hy2 : y p.2 = x p.2 := hclose p.2 h2
        have hpert : ‖(x p.1 - x p.2) - (y p.1 - y p.2)‖ ≤ ρ := by
          have he : (x p.1 - x p.2) - (y p.1 - y p.2) = x p.1 - y p.1 := by
            first
              | rw [← hy2]; abel
              | rw [← hy2, sub_sub_sub_cancel_right]
          rw [he, norm_sub_rev]
          exact hclose' p.1 h1
        exact cross_term_le hsep h1 h2 hν hρ hρν hpert
    · by_cases h2 : p.2 ∈ k
      · -- p.2 ∈ k, p.1 ∉ k : only body `p.2` moves
        have hy1 : y p.1 = x p.1 := hclose p.1 h1
        have hpert : ‖(x p.1 - x p.2) - (y p.1 - y p.2)‖ ≤ ρ := by
          have he : (x p.1 - x p.2) - (y p.1 - y p.2) = -(x p.2 - y p.2) := by
            first
              | rw [← hy1]; abel
              | rw [← hy1]; ring
          rw [he, norm_neg, norm_sub_rev]
          exact hclose' p.2 h2
        exact cross_term_le_swap hsep h2 h1 hν hρ hρν hpert
      · -- neither body in `k` : the pair is unchanged
        have hyx1 : y p.1 = x p.1 := hclose p.1 h1
        have hyx2 : y p.2 = x p.2 := hclose p.2 h2
        have heq : r y p.1 p.2 = r x p.1 p.2 := by
          rw [r_eq_norm_sub, r_eq_norm_sub, hyx1, hyx2]
        rw [heq, sub_self]
        exact hdivnn
  calc ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
        (m p.1 * m p.2 * (r y p.1 p.2)⁻¹ - m p.1 * m p.2 * (r x p.1 p.2)⁻¹)
      ≤ ∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
          m p.1 * m p.2 * (2 * ρ / ν ^ 2) := Finset.sum_le_sum hterm
    _ = (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
            m p.1 * m p.2) * (2 * ρ / ν ^ 2) := by rw [Finset.sum_mul]

end Submission.NBody

namespace Submission.NBody

/-- The perturbed configuration agrees with `γ` outside `k`. -/
lemma bumpCurve_eq_of_notMem {m : Fin N → ℝ} {k : Finset (Fin N)} {i₀ : Fin N} {δ : E}
    {lam T t₀ : ℝ} (hlam : 0 < lam) {γ : ℝ → EN E N} {s : ℝ} (hs : 0 ≤ s) {j : Fin N}
    (hj : j ∉ k) :
    bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j = γ (t₀ + lam * s) j := by
  rw [bumpCurve_shift hlam hs]
  simp only [PiLp.add_apply, PiLp.smul_apply, stdVarVec, PiLp.smul_apply,
    stdPertVec_apply_of_notMem hj, smul_zero, add_zero]

/-- The perturbation of a body of `k` is bounded by `λ^{2/3}‖δ‖`. -/
lemma bumpCurve_pert_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)} {i₀ : Fin N}
    (hi₀ : i₀ ∈ k) {δ : E} {lam T t₀ : ℝ} (hlam : 0 < lam) {γ : ℝ → EN E N} {s : ℝ}
    (hs : 0 ≤ s) {j : Fin N} (hj : j ∈ k) :
    ‖bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s) j - γ (t₀ + lam * s) j‖
      ≤ lam ^ ((2:ℝ)/3) * ‖δ‖ := by
  rw [bumpCurve_shift hlam hs]
  have h1 : (γ (t₀ + lam * s) + lam ^ ((2:ℝ)/3) • stdVarVec m k i₀ δ T s) j
      - γ (t₀ + lam * s) j
      = lam ^ ((2:ℝ)/3) • (stdCoef δ T s • (stdPertVec m k i₀ δ j)) := by
    rw [PiLp.add_apply, PiLp.smul_apply, stdVarVec, PiLp.smul_apply, add_sub_cancel_left]
  rw [h1, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hcoef : |stdCoef δ T s| ≤ 1 := by
    rw [abs_of_nonneg (stdCoef_nonneg δ T s)]; exact stdCoef_le_one δ T s
  have h2 : |lam ^ ((2:ℝ)/3)| = lam ^ ((2:ℝ)/3) :=
    abs_of_pos (Real.rpow_pos_of_pos hlam _)
  rw [h2]
  calc lam ^ ((2:ℝ)/3) * (|stdCoef δ T s| * ‖stdPertVec m k i₀ δ j‖)
      ≤ lam ^ ((2:ℝ)/3) * (1 * ‖δ‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hcoef (norm_stdPertVec_apply_le hm hi₀ δ j) (norm_nonneg _) zero_le_one)
          (Real.rpow_nonneg hlam.le _)
    _ = lam ^ ((2:ℝ)/3) * ‖δ‖ := by ring

/-- **The interaction-potential difference of the bump is `O(λ^{5/3}‖δ‖)`.** -/
theorem clusterPotentialRest_bump_le {m : Fin N → ℝ} (hm : ∀ i, 0 < m i) {k : Finset (Fin N)}
    {i₀ : Fin N} (hi₀ : i₀ ∈ k) {δ : E} {lam T t₀ ν : ℝ} {γ : ℝ → EN E N}
    (hν : 0 < ν) (hlam : 0 < lam) (hT : 0 < T)
    (hsep : ∀ s ∈ Ioc (0:ℝ) T, ClusterSeparatedWeak k (γ (t₀ + lam * s)) ν)
    (hsmall : 2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) ≤ ν) {s : ℝ} (hs : s ∈ Ioc (0:ℝ) T) :
    clusterPotentialRest m k (bumpCurve m k i₀ δ T lam t₀ γ (t₀ + lam * s))
        - clusterPotentialRest m k (γ (t₀ + lam * s))
      ≤ (∑ p ∈ (pairFinset N).filter (fun p : Fin N × Fin N => ¬ (p.1 ∈ k ∧ p.2 ∈ k)),
          m p.1 * m p.2) * (2 * (lam ^ ((2:ℝ)/3) * ‖δ‖) / ν ^ 2) :=
  clusterPotentialRest_diff_le (fun i => (hm i).le) hν (by positivity) hsmall (hsep s hs)
    (fun j hj => bumpCurve_eq_of_notMem hlam hs.1.le hj)
    (fun j hj => bumpCurve_pert_le hm hi₀ hlam hs.1.le hj)

end Submission.NBody

