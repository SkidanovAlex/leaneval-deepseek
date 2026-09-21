import Mathlib
import Submission.Work.OddVolterra.Swept.ksSmooth

/-!
# Estimates for the Leibniz expansion `ks` and for the shifted kernel `kt`, `tkt`

Elementary bounds (each term of the finite Leibniz sum is bounded by a power of `σ - u` resp. of
`τ`), the continuity of the uncurried `tkt` on the region `τ > 0`, and the derivative of the
shifted kernel along the curve `x' ↦ (x', (b-x')τ)`.  These feed the differentiation under the
integral sign for the swept integral.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Swept

open Work.OddVolterra
open Work.OddVolterra.Swept.Smooth

/-- Bound of one term of `ks`. -/
lemma ks_term_le {p : ℝ} {j i : ℕ} {A : ℝ → ℝ → ℝ} {L M B : ℝ}
    {u σ : ℝ} (h : u < σ) (hij : i ≤ j) (hB : σ - u ≤ B) (h1B : 1 ≤ B)
    (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hlc : |lcoef j i p| ≤ L) (hbd : |pder A (j - i) u σ| ≤ M) :
    |lcoef j i p * (σ - u) ^ (p - i) * pder A (j - i) u σ|
      ≤ L * M * B ^ j * (σ - u) ^ (p - j) := by
  have ht : 0 < σ - u := sub_pos.mpr h
  have ht0 : 0 ≤ σ - u := le_of_lt ht
  have htB : 0 ≤ B := le_trans ht0 hB
  have hexp : p - (i : ℝ) = (p - (j : ℝ)) + ((j - i : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hij]; ring
  have hpw : (σ - u) ^ (p - i) = (σ - u) ^ (p - j) * (σ - u) ^ ((j - i : ℕ) : ℝ) := by
    rw [hexp, Real.rpow_add ht]
  have h6 : (σ - u) ^ ((j - i : ℕ) : ℝ) ≤ B ^ j := by
    refine le_trans (Real.rpow_le_rpow ht0 hB (Nat.cast_nonneg _)) ?_
    rw [Real.rpow_natCast]
    exact pow_le_pow_right₀ h1B (Nat.sub_le j i)
  rw [hpw, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht0 (p - (j : ℝ))),
    abs_of_nonneg (Real.rpow_nonneg ht0 ((j - i : ℕ) : ℝ))]
  have hkey : |lcoef j i p| * (σ - u) ^ ((j - i : ℕ) : ℝ) * |pder A (j - i) u σ| ≤ L * M * B ^ j := by
    have h1 : |lcoef j i p| * (σ - u) ^ ((j - i : ℕ) : ℝ) ≤ L * B ^ j :=
      le_trans (mul_le_mul hlc h6 (Real.rpow_nonneg ht0 _) hL)
        (le_of_eq (by ring))
    calc |lcoef j i p| * (σ - u) ^ ((j - i : ℕ) : ℝ) * |pder A (j - i) u σ|
        ≤ (L * B ^ j) * M := mul_le_mul h1 hbd (abs_nonneg _) (mul_nonneg hL (pow_nonneg htB j))
      _ = L * M * B ^ j := by ring
  calc |lcoef j i p| * ((σ - u) ^ (p - j) * (σ - u) ^ ((j - i : ℕ) : ℝ)) * |pder A (j - i) u σ|
      = (|lcoef j i p| * (σ - u) ^ ((j - i : ℕ) : ℝ) * |pder A (j - i) u σ|)
          * (σ - u) ^ (p - j) := by ring
    _ ≤ (L * M * B ^ j) * (σ - u) ^ (p - j) :=
        mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg ht0 _)
    _ = L * M * B ^ j * (σ - u) ^ (p - j) := by ring

/-- Bound of `ks` by `(σ-u)^(p-j)`. -/
lemma abs_ks_le {p : ℝ} {j : ℕ} {A : ℝ → ℝ → ℝ} {L M B : ℝ}
    {u σ : ℝ} (h : u < σ) (hB : σ - u ≤ B) (h1B : 1 ≤ B) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hlc : ∀ i ∈ Finset.range (j + 1), |lcoef j i p| ≤ L)
    (hbd : ∀ i ∈ Finset.range (j + 1), |pder A (j - i) u σ| ≤ M) :
    |ks A p j u σ| ≤ (((j + 1 : ℕ) : ℝ) * L * M * B ^ j) * (σ - u) ^ (p - j) := by
  have ht0 : 0 ≤ σ - u := le_of_lt (sub_pos.mpr h)
  rw [ks]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ Finset.range (j + 1), |lcoef j i p * (σ - u) ^ (p - i) * pder A (j - i) u σ|
      ≤ ∑ _i ∈ Finset.range (j + 1), L * M * B ^ j * (σ - u) ^ (p - j) :=
        Finset.sum_le_sum fun i hi =>
          ks_term_le h (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hB h1B hL hM
            (hlc i hi) (hbd i hi)
    _ = (((j + 1 : ℕ) : ℝ) * L * M * B ^ j) * (σ - u) ^ (p - j) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- Bound of `kt` by `τ^(p-j)`. -/
lemma abs_kt_le {p : ℝ} {j : ℕ} {A : ℝ → ℝ → ℝ} {L M B : ℝ}
    {u τ : ℝ} (hτ : 0 < τ) (hB : τ ≤ B) (h1B : 1 ≤ B) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hlc : ∀ i ∈ Finset.range (j + 1), |lcoef j i p| ≤ L)
    (hbd : ∀ i ∈ Finset.range (j + 1), |pder A (j - i) u (u + τ)| ≤ M) :
    |kt A p j u τ| ≤ (((j + 1 : ℕ) : ℝ) * L * M * B ^ (j + 1)) * τ ^ (p - j) := by
  rw [kt_eq_ks]
  have hσ : u < u + τ := by linarith
  have hB' : u + τ - u ≤ B := by simpa using hB
  have h := abs_ks_le (p := p) (j := j) (A := A) (L := L) (M := M) (B := B)
    (u := u) (σ := u + τ) hσ hB' h1B hL hM hlc (fun i hi => by simpa using hbd i hi)
  rw [show u + τ - u = τ from by ring] at h
  refine le_trans h ?_
  have hpow : B ^ j ≤ B ^ (j + 1) := pow_le_pow_right₀ h1B (by omega)
  have h0 : 0 ≤ ((j + 1 : ℕ) : ℝ) * L * M := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow h0)
    (Real.rpow_nonneg (le_of_lt hτ) _)


/-- Continuity of the uncurried shifted `tkt` on the region `τ > 0`. -/
theorem continuousOn_uncurried_tkt {p : ℝ} {j : ℕ} {A : ℝ → ℝ → ℝ} {O : Set (ℝ × ℝ)}
    (hO : IsOpen O) (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O) :
    ContinuousOn (fun q : ℝ × ℝ => tkt A p j q.1 q.2)
      {q : ℝ × ℝ | 0 < q.2 ∧ (q.1, q.1 + q.2) ∈ O} := by
  intro q hq
  obtain ⟨hq2, hqO⟩ := hq
  have key : ContinuousAt (fun q : ℝ × ℝ => tkt A p j q.1 q.2) q := by
    show Tendsto (fun q : ℝ × ℝ => tkt A p j q.1 q.2) (𝓝 q) (𝓝 (tkt A p j q.1 q.2))
    simp only [tkt]
    refine tendsto_finsetSum _ fun i hi => ?_
    have hpow1 : Tendsto (fun q : ℝ × ℝ => q.2 ^ (p - i - 1)) (𝓝 q) (𝓝 (q.2 ^ (p - i - 1))) :=
      (continuousAt_snd.rpow_const (Or.inl (ne_of_gt hq2))).tendsto
    have hpow2 : Tendsto (fun q : ℝ × ℝ => q.2 ^ (p - i)) (𝓝 q) (𝓝 (q.2 ^ (p - i))) :=
      (continuousAt_snd.rpow_const (Or.inl (ne_of_gt hq2))).tendsto
    have hpder : Tendsto (fun q : ℝ × ℝ => pder A (j - i) q.1 (q.1 + q.2)) (𝓝 q)
        (𝓝 (pder A (j - i) q.1 (q.1 + q.2))) := by
      have h1 : ContinuousAt (fun q : ℝ × ℝ => pder A (j - i) q.1 q.2) (q.1, q.1 + q.2) :=
        ((contDiffOn_uncurried_pder_smooth hO hA (j - i)).continuousOn).continuousAt
          (hO.mem_nhds hqO)
      have h2 : Tendsto (fun q : ℝ × ℝ => (q.1, q.1 + q.2)) (𝓝 q) (𝓝 (q.1, q.1 + q.2)) :=
        (by fun_prop : ContinuousAt (fun q : ℝ × ℝ => (q.1, q.1 + q.2)) q).tendsto
      exact h1.tendsto.comp h2
    have hqder : Tendsto (fun q : ℝ × ℝ => qder A (j - i) q.1 (q.1 + q.2)) (𝓝 q)
        (𝓝 (qder A (j - i) q.1 (q.1 + q.2))) := by
      have h1 : ContinuousAt (fun q : ℝ × ℝ => qder A (j - i) q.1 q.2) (q.1, q.1 + q.2) :=
        ((contDiffOn_uncurried_qder_smooth hO hA (j - i)).continuousOn).continuousAt
          (hO.mem_nhds hqO)
      have h2 : Tendsto (fun q : ℝ × ℝ => (q.1, q.1 + q.2)) (𝓝 q) (𝓝 (q.1, q.1 + q.2)) :=
        (by fun_prop : ContinuousAt (fun q : ℝ × ℝ => (q.1, q.1 + q.2)) q).tendsto
      exact h1.tendsto.comp h2
    have ht1 : Tendsto (fun q : ℝ × ℝ => (p - i) * q.2 ^ (p - i - 1) * pder A (j - i) q.1 (q.1 + q.2))
        (𝓝 q) (𝓝 ((p - i) * q.2 ^ (p - i - 1) * pder A (j - i) q.1 (q.1 + q.2))) :=
      (tendsto_const_nhds.mul hpow1).mul hpder
    have ht2 : Tendsto (fun q : ℝ × ℝ => q.2 ^ (p - i) * qder A (j - i) q.1 (q.1 + q.2))
        (𝓝 q) (𝓝 (q.2 ^ (p - i) * qder A (j - i) q.1 (q.1 + q.2))) := hpow2.mul hqder
    exact tendsto_const_nhds.mul (ht1.add ht2)
  exact key.continuousWithinAt

/-- Derivative along the curve `x' ↦ (x', (b-x')τ)` of the shifted kernel. -/
lemma hasDerivAt_kt_curve {p : ℝ} {j : ℕ} {A : ℝ → ℝ → ℝ} {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (hA : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => A q.1 q.2) O)
    {b x τ : ℝ} (hxO : (x, x + (b - x) * τ) ∈ O) (hτ : 0 < τ) (hbx : 0 < b - x) :
    HasDerivAt (fun x' : ℝ => kt A p j x' ((b - x') * τ))
      (ks A p (j + 1) x (x + (b - x) * τ) + (1 - τ) * tkt A p j x ((b - x) * τ)) x := by
  have hτ' : 0 < (b - x) * τ := mul_pos hbx hτ
  have hK := hasFDerivAt_uncurried_kt_smooth (p := p) (j := j) hO hA hxO hτ'
  have h2 : HasDerivAt (fun x' : ℝ => (b - x') * τ) (-τ) x := by
    have h1 : HasDerivAt (fun x' : ℝ => b - x') (-1) x := (hasDerivAt_id x).const_sub b
    have := h1.mul_const τ
    simpa using this
  have hcurve : HasDerivAt (fun x' : ℝ => (x', (b - x') * τ)) (1, -τ) x :=
    (hasDerivAt_id x).prodMk h2
  have hcomp := hK.comp_hasDerivAt x hcurve
  have hval : (((ks A p (j + 1) x (x + (b - x) * τ) + tkt A p j x ((b - x) * τ))
        • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (tkt A p j x ((b - x) * τ)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, -τ))
      = ks A p (j + 1) x (x + (b - x) * τ) + (1 - τ) * tkt A p j x ((b - x) * τ) := by
    simp [smul_eq_mul]
    ring
  simpa [Function.comp_def, hval] using hcomp



/-- For `0 < t0 ≤ t ≤ T` and any real exponent `e`, `t^e` is bounded by the endpoint powers. -/
lemma rpow_le_max_of_mem_Icc {t0 T e t : ℝ} (h0 : 0 < t0) (ht : t ∈ Set.Icc t0 T) :
    t ^ e ≤ max (t0 ^ e) (T ^ e) := by
  by_cases he : 0 ≤ e
  · exact le_trans (Real.rpow_le_rpow (le_of_lt (lt_of_lt_of_le h0 ht.1)) ht.2 he)
      (le_max_right _ _)
  · push_neg at he
    have ht0 : 0 < t := lt_of_lt_of_le h0 ht.1
    have h1 : t0 ^ (-e) ≤ t ^ (-e) := Real.rpow_le_rpow (le_of_lt h0) ht.1 (by linarith)
    have h2 : t ^ e ≤ t0 ^ e := by
      rw [show e = -(-e) by ring, Real.rpow_neg (le_of_lt ht0), Real.rpow_neg (le_of_lt h0)]
      exact (inv_le_inv₀ (Real.rpow_pos_of_pos ht0 (-e))
        (Real.rpow_pos_of_pos h0 (-e))).2 h1
    exact le_trans h2 (le_max_left _ _)

end Work.OddVolterra.Swept
