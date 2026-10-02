import Submission.Work.PTGeometric.RieszProj.Proj

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The trace of `Phi S` for `S` near a rank-`k` projection
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped ContDiff
open Set Function MeasureTheory

namespace Work.PTGeometric

noncomputable section

variable {n k : ℕ}

/-! ## The spectral bound -/

/-- The eigenvalue bound: an eigenvalue of `S` is within `‖S - P‖` of `0` or `1`. -/
lemma eigenvalue_dist_le {P S : EndOp n} (hP : P ∈ Gr n k) (mu : ℝ)
    (hm : Module.End.HasEigenvalue (S : Amb n →ₗ[ℝ] Amb n) mu) :
    min |mu| |mu - 1| ≤ ‖S - P‖ := by
  obtain ⟨v, hv, hv0⟩ := hm.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hv
  have hv' : S v = mu • v := hv
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  -- `⟪P v, v⟫ = ‖P v‖²`
  have key : inner ℝ (P v) (P v) = inner ℝ (P v) v := by
    have h2 : inner ℝ (P v) (ContinuousLinearMap.adjoint P v) = inner ℝ (P (P v)) v :=
      ContinuousLinearMap.adjoint_inner_right P (P v) v
    rw [hP.1] at h2
    rw [← ContinuousLinearMap.mul_apply, hP.2.1] at h2
    exact h2
  have ht0 : 0 ≤ inner ℝ (P v) v := by
    rw [← key]; exact real_inner_self_nonneg
  have hnormP : ‖P v‖ ≤ ‖v‖ := by
    have h3 : ‖P v‖ ^ 2 = inner ℝ (P v) v := by
      rw [← real_inner_self_eq_norm_sq]
      exact key
    by_cases h4 : P v = 0
    · simp [h4]
    · have h5 : ‖P v‖ ^ 2 ≤ ‖P v‖ * ‖v‖ := by
        rw [h3]
        exact real_inner_le_norm (P v) v
      have h6 : 0 < ‖P v‖ := norm_pos_iff.mpr h4
      nlinarith [h5, h6, norm_nonneg v]
  have ht1 : inner ℝ (P v) v ≤ ‖v‖ ^ 2 := by
    rw [← key, real_inner_self_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) hnormP 2
  have hkey : ‖(S - P) v‖ ^ 2
      = mu ^ 2 * ‖v‖ ^ 2 + (inner ℝ (P v) v) * (1 - 2 * mu) := by
    have hv' : S v = mu • v := hv
    have h1 : (S - P) v = mu • v - P v := by rw [sub_apply, hv']
    have h2 : ‖mu • v - P v‖ ^ 2
        = mu ^ 2 * ‖v‖ ^ 2 - 2 * mu * inner ℝ (P v) v + ‖P v‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      have h3 : inner ℝ (mu • v) (P v) = mu * inner ℝ (P v) v := by
        rw [real_inner_smul_left]
        exact congrArg (fun z => mu * z) (real_inner_comm (P v) v)
      rw [h3]
      ring
    have h3 : ‖P v‖ ^ 2 = inner ℝ (P v) v := by
      rw [← real_inner_self_eq_norm_sq]
      exact key
    rw [h1, h2, h3]
    ring
  have hb : ‖(S - P) v‖ ≤ ‖S - P‖ * ‖v‖ := (S - P).le_opNorm v
  have hbound : min (mu ^ 2) ((mu - 1) ^ 2) * ‖v‖ ^ 2 ≤ ‖S - P‖ ^ 2 * ‖v‖ ^ 2 := by
    have h1 : min (mu ^ 2) ((mu - 1) ^ 2) * ‖v‖ ^ 2 ≤ ‖(S - P) v‖ ^ 2 := by
      rw [hkey]
      rcases le_total mu (1/2) with h2 | h2
      · have h3 : 0 ≤ 1 - 2 * mu := by linarith
        have h4 : 0 ≤ (inner ℝ (P v) v) * (1 - 2 * mu) := mul_nonneg ht0 h3
        have h5 : min (mu ^ 2) ((mu - 1) ^ 2) ≤ mu ^ 2 := min_le_left _ _
        have h6 := mul_le_mul_of_nonneg_right h5 (sq_nonneg ‖v‖)
        linarith
      · have h3 : 1 - 2 * mu ≤ 0 := by linarith
        have h4 : (inner ℝ (P v) v) * (1 - 2 * mu) ≥ ‖v‖ ^ 2 * (1 - 2 * mu) := by
          nlinarith [ht1, h3, ht0, sq_nonneg ‖v‖]
        have h5 : mu ^ 2 * ‖v‖ ^ 2 + ‖v‖ ^ 2 * (1 - 2 * mu) = (mu - 1) ^ 2 * ‖v‖ ^ 2 := by ring
        have h7 : min (mu ^ 2) ((mu - 1) ^ 2) ≤ (mu - 1) ^ 2 := min_le_right _ _
        have h8 := mul_le_mul_of_nonneg_right h7 (sq_nonneg ‖v‖)
        linarith
    have h6 : ‖(S - P) v‖ ^ 2 ≤ ‖S - P‖ ^ 2 * ‖v‖ ^ 2 := by
      nlinarith [hb, norm_nonneg ((S - P) v), norm_nonneg v, norm_nonneg (S - P)]
    linarith
  have hv2 : 0 < ‖v‖ ^ 2 := pow_pos hvnorm 2
  have h5 : min (mu ^ 2) ((mu - 1) ^ 2) ≤ ‖S - P‖ ^ 2 := by nlinarith [hbound, hv2]
  have h7 : min (mu ^ 2) ((mu - 1) ^ 2) = (min |mu| |mu - 1|) ^ 2 := by
    rcases le_total |mu| |mu - 1| with h8 | h8
    · have h9 : mu ^ 2 ≤ (mu - 1) ^ 2 := by
        rw [← sq_abs mu, ← sq_abs (mu - 1)]
        exact pow_le_pow_left₀ (abs_nonneg _) h8 2
      rw [min_eq_left h9, min_eq_left h8]
      exact (sq_abs mu).symm
    · have h9 : (mu - 1) ^ 2 ≤ mu ^ 2 := by
        rw [← sq_abs mu, ← sq_abs (mu - 1)]
        exact pow_le_pow_left₀ (abs_nonneg _) h8 2
      rw [min_eq_right h9, min_eq_right h8]
      exact (sq_abs (mu - 1)).symm
  rw [h7] at h5
  nlinarith [h5, abs_nonneg mu, abs_nonneg (mu - 1), norm_nonneg (S - P),
    le_min (abs_nonneg mu) (abs_nonneg (mu - 1))]

/-- A self-adjoint operator within `1/4` of a rank-`k` projection satisfies the cluster condition. -/
lemma Cluster.of_dist {P S : EndOp n} (hP : P ∈ Gr n k) (h : ‖S - P‖ < 1/4) : Cluster S :=
  fun mu hm => lt_of_le_of_lt (eigenvalue_dist_le hP mu hm) h




/-! ## The quadratic form in the eigenbasis -/

variable {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)

lemma inner_basis_self (hn : Module.finrank ℝ (Amb n) = n) (i : Fin n) :
    inner ℝ (hSsym.eigenvectorBasis hn i) (hSsym.eigenvectorBasis hn i) = 1 := by
  rw [real_inner_self_eq_norm_sq, (hSsym.eigenvectorBasis hn).orthonormal.1 i, one_pow]

/-- The quadratic form of a self-adjoint operator that is diagonal in the eigenbasis. -/
lemma inner_eq_sum (hn : Module.finrank ℝ (Amb n) = n) (T : EndOp n)
    (hTsym : (T : Amb n →ₗ[ℝ] Amb n).IsSymmetric) (f : Fin n → ℝ)
    (hT : ∀ i, T (hSsym.eigenvectorBasis hn i) = f i • hSsym.eigenvectorBasis hn i) (x : Amb n) :
    inner ℝ (T x) x
      = ∑ i, f i * (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2 := by
  have hstep : ∀ j, inner ℝ (T x) (hSsym.eigenvectorBasis hn j)
      = f j * inner ℝ (hSsym.eigenvectorBasis hn j) x := by
    intro j
    have h1 : inner ℝ (T x) (hSsym.eigenvectorBasis hn j)
        = inner ℝ x (T (hSsym.eigenvectorBasis hn j)) := hTsym x (hSsym.eigenvectorBasis hn j)
    rw [h1, hT j, real_inner_smul_right]
    exact congrArg (fun z => f j * z) (real_inner_comm (hSsym.eigenvectorBasis hn j) x)
  calc inner ℝ (T x) x
      = inner ℝ (T x) (∑ j, inner ℝ (hSsym.eigenvectorBasis hn j) x
            • hSsym.eigenvectorBasis hn j) := by rw [sum_repr_inner hSsym hn x]
    _ = ∑ j, inner ℝ (hSsym.eigenvectorBasis hn j) x * inner ℝ (T x)
          (hSsym.eigenvectorBasis hn j) := by
        rw [inner_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [real_inner_smul_right]
    _ = ∑ j, f j * (inner ℝ (hSsym.eigenvectorBasis hn j) x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hstep j]
        ring





section Middle

/-- The norm identity in the eigenbasis. -/
lemma norm_sq_eq_sum {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hn : Module.finrank ℝ (Amb n) = n) (x : Amb n) :
    ‖x‖ ^ 2 = ∑ i, (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2 := by
  have h := inner_eq_sum hSsym hn (1 : EndOp n) (by intro x y; simp) (fun _ => 1)
    (fun i => by rw [one_apply_eq_self, one_smul]) x
  simpa [real_inner_self_eq_norm_sq] using h

/-- The quadratic form of `Phi S` in the eigenbasis. -/
lemma inner_Phi_eq_sum {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hS : Cluster S) (hn : Module.finrank ℝ (Amb n) = n) (x : Amb n) :
    inner ℝ (Phi S x) x
      = ∑ i, chi (hSsym.eigenvalues hn i) * (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2 :=
  inner_eq_sum hSsym hn (Phi S) (Phi_isSymmetric hSsym hS hn)
    (fun i => chi (hSsym.eigenvalues hn i)) (fun i => Phi_apply_eigenbasis hSsym hS hn i) x

/-- The quadratic form of `S` in the eigenbasis. -/
lemma inner_S_eq_sum {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hn : Module.finrank ℝ (Amb n) = n) (x : Amb n) :
    inner ℝ (S x) x
      = ∑ i, hSsym.eigenvalues hn i * (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2 :=
  inner_eq_sum hSsym hn S hSsym (fun i => hSsym.eigenvalues hn i)
    (fun i => hSsym.apply_eigenvectorBasis hn i) x

/-- For `x` with `Phi S x = x`, the coefficients outside the top cluster vanish. -/
lemma coeff_eq_zero_of_Phi_eq_self {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hS : Cluster S) (hn : Module.finrank ℝ (Amb n) = n) {x : Amb n}
    (hx : Phi S x = x) {i : Fin n} (hi : chi (hSsym.eigenvalues hn i) = 0) :
    inner ℝ (hSsym.eigenvectorBasis hn i) x = 0 := by
  have h1 : inner ℝ (hSsym.eigenvectorBasis hn i) (Phi S x)
      = inner ℝ (Phi S (hSsym.eigenvectorBasis hn i)) x :=
    (Phi_isSymmetric hSsym hS hn (hSsym.eigenvectorBasis hn i) x).symm
  rw [Phi_apply_eigenbasis hSsym hS hn i, real_inner_smul_left] at h1
  rw [← hx, h1, hi, zero_mul]

/-- For `x` with `Phi S x = 0`, the coefficients in the top cluster vanish. -/
lemma coeff_eq_zero_of_Phi_eq_zero {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hS : Cluster S) (hn : Module.finrank ℝ (Amb n) = n) {x : Amb n}
    (hx : Phi S x = 0) {i : Fin n} (hi : chi (hSsym.eigenvalues hn i) = 1) :
    inner ℝ (hSsym.eigenvectorBasis hn i) x = 0 := by
  have h1 : inner ℝ (hSsym.eigenvectorBasis hn i) x
      = inner ℝ (Phi S (hSsym.eigenvectorBasis hn i)) x := by
    rw [Phi_apply_eigenbasis hSsym hS hn i, hi, one_smul]
  have h2 : inner ℝ (Phi S (hSsym.eigenvectorBasis hn i)) x
      = inner ℝ (hSsym.eigenvectorBasis hn i) (Phi S x) :=
    Phi_isSymmetric hSsym hS hn (hSsym.eigenvectorBasis hn i) x
  rw [h1, h2, hx, inner_zero_right]

/-- Eigenvalues in the top cluster exceed `3/4`. -/
lemma three_quarters_lt_of_chi {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hS : Cluster S) (hn : Module.finrank ℝ (Amb n) = n) {i : Fin n}
    (hi : chi (hSsym.eigenvalues hn i) = 1) : (3/4 : ℝ) < hSsym.eigenvalues hn i := by
  have h1 : |hSsym.eigenvalues hn i - 1| < 1/2 := by
    by_contra hc
    rw [chi, if_neg hc] at hi
    norm_num at hi
  have h2 := (hS.eigen_mem (hSsym.hasEigenvalue_eigenvalues hn i)).resolve_left (by
    intro hh
    rw [abs_lt] at h1
    have hh2 : hSsym.eigenvalues hn i < 1/4 := hh.2
    linarith [hh2, h1.1])
  exact h2.1

/-- Eigenvalues outside the top cluster are below `1/4`. -/
lemma lt_quarter_of_chi {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hS : Cluster S) (hn : Module.finrank ℝ (Amb n) = n) {i : Fin n}
    (hi : chi (hSsym.eigenvalues hn i) = 0) : hSsym.eigenvalues hn i < (1/4 : ℝ) := by
  have h1 : ¬ |hSsym.eigenvalues hn i - 1| < 1/2 := by
    intro hc
    rw [chi, if_pos hc] at hi
    norm_num at hi
  have h2 := (hS.eigen_mem (hSsym.hasEigenvalue_eigenvalues hn i)).resolve_right (by
    intro hh
    have hh1 : (3/4 : ℝ) < hSsym.eigenvalues hn i := hh.1
    have hh2 : hSsym.eigenvalues hn i < (5/4 : ℝ) := hh.2
    exact h1 (by rw [abs_lt]; exact ⟨by linarith [hh1], by linarith [hh2]⟩))
  exact h2.2



section Last

/-- The number of eigenvalues in the top cluster, counted with multiplicity. -/
def topCard (S : EndOp n) (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hn : Module.finrank ℝ (Amb n) = n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => 1/2 < hSsym.eigenvalues hn i)).card


/-- `⟪P x, x⟫ = ‖P x‖²` for the orthogonal projection `P`. -/
lemma inner_P_eq_norm_sq {P : EndOp n} (hP : P ∈ Gr n k) (x : Amb n) :
    inner ℝ (P x) x = ‖P x‖ ^ 2 := by
  have key : inner ℝ (P x) (P x) = inner ℝ (P x) x := by
    have h2 : inner ℝ (P x) (ContinuousLinearMap.adjoint P x) = inner ℝ (P (P x)) x :=
      ContinuousLinearMap.adjoint_inner_right P (P x) x
    rw [hP.1] at h2
    rw [← ContinuousLinearMap.mul_apply, hP.2.1] at h2
    exact h2
  rw [← key, real_inner_self_eq_norm_sq]

/-- The upper bound for the quadratic form of `S` on the range of `Phi S`. -/
lemma three_quarters_mul_le_of_Phi_eq_self {S : EndOp n}
    (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric) (hS : Cluster S)
    (hn : Module.finrank ℝ (Amb n) = n) {x : Amb n} (hx : Phi S x = x) :
    (3/4) * ‖x‖ ^ 2 ≤ inner ℝ (S x) x := by
  have hpt : ∀ i : Fin n, (3/4) * (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2
      ≤ hSsym.eigenvalues hn i * (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2 := by
    intro i
    by_cases hc : chi (hSsym.eigenvalues hn i) = 1
    · have h1 := three_quarters_lt_of_chi hSsym hS hn hc
      nlinarith [sq_nonneg (inner ℝ (hSsym.eigenvectorBasis hn i) x)]
    · have hc0 : chi (hSsym.eigenvalues hn i) = 0 := (chi_eq_zero_or_one _).resolve_right hc
      have hz := coeff_eq_zero_of_Phi_eq_self hSsym hS hn hx hc0
      simp [hz]
  calc (3/4) * ‖x‖ ^ 2
      = (3/4) * ∑ i, (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2 := by
        rw [norm_sq_eq_sum hSsym hn x]
    _ = ∑ i, (3/4) * (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i, hSsym.eigenvalues hn i * (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hpt i)
    _ = inner ℝ (S x) x := (inner_S_eq_sum hSsym hn x).symm

/-- The lower bound for the quadratic form of `S` on the kernel of `Phi S`. -/
lemma le_quarter_mul_of_Phi_eq_zero {S : EndOp n}
    (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric) (hS : Cluster S)
    (hn : Module.finrank ℝ (Amb n) = n) {x : Amb n} (hx : Phi S x = 0) :
    inner ℝ (S x) x ≤ (1/4) * ‖x‖ ^ 2 := by
  have hpt : ∀ i : Fin n, hSsym.eigenvalues hn i * (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2
      ≤ (1/4) * (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2 := by
    intro i
    by_cases hc : chi (hSsym.eigenvalues hn i) = 1
    · have hz := coeff_eq_zero_of_Phi_eq_zero hSsym hS hn hx hc
      simp [hz]
    · have hc0 : chi (hSsym.eigenvalues hn i) = 0 := (chi_eq_zero_or_one _).resolve_right hc
      have h1 := lt_quarter_of_chi hSsym hS hn hc0
      nlinarith [sq_nonneg (inner ℝ (hSsym.eigenvectorBasis hn i) x)]
  calc inner ℝ (S x) x
      = ∑ i, hSsym.eigenvalues hn i * (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2 :=
        inner_S_eq_sum hSsym hn x
    _ ≤ ∑ i, (1/4) * (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hpt i)
    _ = (1/4) * ∑ i, (inner ℝ (hSsym.eigenvectorBasis hn i) x) ^ 2 := by
        rw [Finset.mul_sum]
    _ = (1/4) * ‖x‖ ^ 2 := by rw [norm_sq_eq_sum hSsym hn x]

/-- The trace of `Phi S` is the sum of the top-cluster indicators. -/
lemma trace_Phi {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric) (hS : Cluster S)
    (hn : Module.finrank ℝ (Amb n) = n) :
    LinearMap.trace ℝ (Amb n) (Phi S : Amb n →ₗ[ℝ] Amb n)
      = ∑ i, chi (hSsym.eigenvalues hn i) := by
  rw [LinearMap.trace_eq_sum_inner (Phi S : Amb n →ₗ[ℝ] Amb n) (hSsym.eigenvectorBasis hn)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (Phi S : Amb n →ₗ[ℝ] Amb n) (hSsym.eigenvectorBasis hn i)
      = chi (hSsym.eigenvalues hn i) • hSsym.eigenvectorBasis hn i from
    Phi_apply_eigenbasis hSsym hS hn i, real_inner_smul_right, inner_basis_self hSsym hn i,
    mul_one]

/-- `chi` is the indicator of the top cluster. -/
lemma chi_eq_one_iff {S : EndOp n} (hS : Cluster S)
    (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric) (hn : Module.finrank ℝ (Amb n) = n)
    (i : Fin n) : chi (hSsym.eigenvalues hn i) = 1 ↔ 1/2 < hSsym.eigenvalues hn i := by
  have hk := Cluster.half_lt_iff hS (hSsym.hasEigenvalue_eigenvalues hn i)
  by_cases hc : |hSsym.eigenvalues hn i - 1| < 1/2
  · have h1 : (1/2 : ℝ) < hSsym.eigenvalues hn i := hk.mpr hc
    rw [chi, if_pos hc]
    exact ⟨fun _ => h1, fun _ => rfl⟩
  · have h1 : ¬ ((1/2 : ℝ) < hSsym.eigenvalues hn i) := fun h => hc (hk.mp h)
    rw [chi, if_neg hc]
    exact ⟨fun h => absurd h (by norm_num), fun h => absurd h h1⟩

lemma trace_Phi_eq_topCard {S : EndOp n} (hSsym : (S : Amb n →ₗ[ℝ] Amb n).IsSymmetric)
    (hS : Cluster S) (hn : Module.finrank ℝ (Amb n) = n) :
    LinearMap.trace ℝ (Amb n) (Phi S : Amb n →ₗ[ℝ] Amb n) = (topCard S hSsym hn : ℝ) := by
  rw [trace_Phi hSsym hS hn]
  have h1 : ∑ i : Fin n, chi (hSsym.eigenvalues hn i)
      = ∑ i : Fin n, (if chi (hSsym.eigenvalues hn i) = 1 then (1:ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hc : chi (hSsym.eigenvalues hn i) = 1
    · rw [if_pos hc, hc]
    · have hc0 : chi (hSsym.eigenvalues hn i) = 0 := (chi_eq_zero_or_one _).resolve_right hc
      rw [if_neg hc, hc0]
  rw [h1, Finset.sum_boole, topCard]
  have h2 : (Finset.univ.filter (fun i : Fin n => chi (hSsym.eigenvalues hn i) = 1))
      = (Finset.univ.filter (fun i : Fin n => 1/2 < hSsym.eigenvalues hn i)) :=
    Finset.filter_congr (fun i _ => chi_eq_one_iff hS hSsym hn i)
  rw [h2]

end Last

end Middle

end

end Work.PTGeometric
