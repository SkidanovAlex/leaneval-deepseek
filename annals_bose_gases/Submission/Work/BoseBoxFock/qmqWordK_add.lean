import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.qmqDefs
import Submission.Work.BoseFixB1S.integrableOn_cont_mul_pairComp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.qmqWordK_add` — additivity of the two pair words in the kernel

The two words `q1WordK ℓ k Φ`, `q4WordK ℓ k Φ` of `qmqDefs` are **linear in the kernel `k`**:
both are finite sums over `pairSet n` of box integrals whose integrand is a state-dependent factor
times `k (x p.1) (x p.2)`.  Hence

    q1WordK ℓ (k+κ) Φ + q4WordK ℓ (k'+κ') Φ
      = q1WordK ℓ k Φ + q1WordK ℓ κ Φ + q4WordK ℓ k' Φ + q4WordK ℓ κ' Φ .

## Route

* The pointwise factorisation `G x * (w + w') = G x * w + G x * w'` reduces the problem to the
  additivity `MeasureTheory.integral_add` of the box integral — but that needs **integrability**
  of both pieces, which is *not* automatic (the Bochner integral of a non-integrable function is
  `0`, so additivity genuinely fails without it).
* Integrability of `x ↦ G x * w (x i, x j)` over `abox N ℓ` for a **continuous** `G` and a merely
  integrable pair kernel `w` is exactly the colleague's lemma
  `Work.BoseFixB1S.integrableOn_cont_mul_pairComp` (bounded factor `×` the a.e.-measurable
  double-insertion `AeValue.integrableOn_pair_comp_ae`).
* The weights `aP ℓ i (aQ ℓ j Φ)`, `aP ℓ i (aP ℓ j Φ)`, `aQ ℓ i (aQ ℓ j Φ)` are continuous by
  `aP_continuous` / `aQ_continuous`, so the continuity hypothesis is met.
* The two hypotheses on `k` in the *statement* are integrability on the **full** space
  `E3 × E3`; the box version is `Integrable.integrableOn`.
* The degenerate case `ℓ ≤ 0` needs no analysis: `aP ℓ i Ψ x = 0` for every `i, Ψ, x` (for
  `ℓ < 0` the cube `acube ℓ` is empty, for `ℓ = 0` the prefactor `ℓ⁻³` vanishes), so all six
  words are `0`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Additivity of the box integral of a continuous weight times a pair kernel -/

/-- For a continuous weight `G` on the configuration space and two pair kernels `w`, `w'`
integrable on `acube ℓ ×ˢ acube ℓ`, the box integral of `G · (w (xᵢ,xⱼ) + w' (xᵢ,xⱼ))` splits. -/
theorem setIntegral_mul_pair_add {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {G : Submission.BoseGases.X N → ℝ} (hG : Continuous G)
    {w w' : E3 × E3 → ℝ}
    (hw : IntegrableOn w (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) volume)
    (hw' : IntegrableOn w' (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) volume) :
    (∫ x in Submission.BoseGases.abox N ℓ, G x * (w (x i, x j) + w' (x i, x j)))
      = (∫ x in Submission.BoseGases.abox N ℓ, G x * w (x i, x j))
        + (∫ x in Submission.BoseGases.abox N ℓ, G x * w' (x i, x j)) := by
  have hwI : IntegrableOn (fun x : Submission.BoseGases.X N => G x * w (x i, x j))
      (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_cont_mul_pairComp hℓ hij hG hw
  have hw'I : IntegrableOn (fun x : Submission.BoseGases.X N => G x * w' (x i, x j))
      (Submission.BoseGases.abox N ℓ) volume :=
    Work.BoseFixB1S.integrableOn_cont_mul_pairComp hℓ hij hG hw'
  have hcongr : (∫ x in Submission.BoseGases.abox N ℓ,
        G x * (w (x i, x j) + w' (x i, x j)))
      = ∫ x in Submission.BoseGases.abox N ℓ,
        (G x * w (x i, x j) + G x * w' (x i, x j)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  rw [hcongr]
  exact MeasureTheory.integral_add hwI hw'I

/-! ## The degenerate case `ℓ ≤ 0` -/

/-- For `ℓ ≤ 0` the box mean `aP` vanishes identically: for `ℓ < 0` the cube `acube ℓ` is empty,
for `ℓ = 0` the prefactor `(ℓ^3)⁻¹` is `0`. -/
theorem aP_eq_zero_of_nonpos {N : ℕ} {ℓ : ℝ} (hℓ : ℓ ≤ 0) (i : Fin N)
    (Ψ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Submission.BoseGases.aP ℓ i Ψ x = 0 := by
  rw [Submission.BoseGases.aP]
  rcases lt_or_eq_of_le hℓ with hlt | heq
  · have hempty : Submission.BoseGases.acube ℓ = (∅ : Set E3) := by
      rw [← Set.subset_empty_iff]
      intro y hy
      have h0 : y (0 : Fin 3) ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hy (0 : Fin 3)
      have hlt' : ℓ / 2 < -ℓ / 2 := by linarith
      exact absurd h0.2 (not_le.mpr (lt_of_lt_of_le hlt' h0.1))
    rw [show (∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update x i y)) = 0 from by
      rw [hempty]
      exact MeasureTheory.setIntegral_empty]
    rw [mul_zero]
  · rw [heq]
    simp

/-- For `ℓ ≤ 0` the `T₁` word vanishes for every kernel. -/
theorem q1WordK_eq_zero_of_nonpos {n : ℕ} {ℓ : ℝ} (hℓ : ℓ ≤ 0)
    (k : E3 → E3 → ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    q1WordK ℓ k Φ = 0 := by
  rw [q1WordK]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  have hf : (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x
        * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
        * k (x p.1) (x p.2))
      = fun _ : Submission.BoseGases.X n => (0 : ℝ) := by
    funext x
    rw [aP_eq_zero_of_nonpos hℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x]
    ring
  rw [hf]
  simp

/-- For `ℓ ≤ 0` the `T₄` word vanishes for every kernel. -/
theorem q4WordK_eq_zero_of_nonpos {n : ℕ} {ℓ : ℝ} (hℓ : ℓ ≤ 0)
    (k : E3 → E3 → ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    q4WordK ℓ k Φ = 0 := by
  rw [q4WordK]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  have hf : (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x
        * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
        * k (x p.1) (x p.2))
      = fun _ : Submission.BoseGases.X n => (0 : ℝ) := by
    funext x
    rw [aP_eq_zero_of_nonpos hℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x]
    ring
  rw [hf]
  simp

/-! ## Additivity at `0 < ℓ` -/

/-- `q1WordK` is additive in the pair kernel (for `0 < ℓ`). -/
theorem q1WordK_add_of_pos {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {k κ : E3 → E3 → ℝ} (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ)
    (hk : Integrable (Function.uncurry k) volume)
    (hκ : Integrable (Function.uncurry κ) volume) :
    q1WordK ℓ (fun a b => k a b + κ a b) Φ = q1WordK ℓ k Φ + q1WordK ℓ κ Φ := by
  have hG : ∀ p : Fin n × Fin n, Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x
        * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x) :=
    fun p => (Submission.BoseGases.aP_continuous hℓ p.1
        (Submission.BoseGases.aQ_continuous hℓ p.2 hΦc)).mul
      (Submission.BoseGases.aP_continuous hℓ p.2
        (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc))
  have hkOn : IntegrableOn (Function.uncurry k)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) volume :=
    hk.integrableOn
  have hκOn : IntegrableOn (Function.uncurry κ)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) volume :=
    hκ.integrableOn
  rw [q1WordK, q1WordK, q1WordK, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  exact setIntegral_mul_pair_add (w := Function.uncurry k) (w' := Function.uncurry κ)
    hℓ hne (hG p) hkOn hκOn

/-- `q4WordK` is additive in the pair kernel (for `0 < ℓ`). -/
theorem q4WordK_add_of_pos {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {k κ : E3 → E3 → ℝ} (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ)
    (hk : Integrable (Function.uncurry k) volume)
    (hκ : Integrable (Function.uncurry κ) volume) :
    q4WordK ℓ (fun a b => k a b + κ a b) Φ = q4WordK ℓ k Φ + q4WordK ℓ κ Φ := by
  have hG : ∀ p : Fin n × Fin n, Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x
        * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x) :=
    fun p => (Submission.BoseGases.aP_continuous hℓ p.1
        (Submission.BoseGases.aP_continuous hℓ p.2 hΦc)).mul
      (Submission.BoseGases.aQ_continuous hℓ p.2
        (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc))
  have hkOn : IntegrableOn (Function.uncurry k)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) volume :=
    hk.integrableOn
  have hκOn : IntegrableOn (Function.uncurry κ)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) volume :=
    hκ.integrableOn
  rw [q4WordK, q4WordK, q4WordK, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  exact setIntegral_mul_pair_add (w := Function.uncurry k) (w' := Function.uncurry κ)
    hℓ hne (hG p) hkOn hκOn

/-! ## The target -/

theorem qmqWordK_add {n : ℕ} {ℓ : ℝ} {k k' κ κ' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ)
    (hk : MeasureTheory.Integrable (Function.uncurry k) MeasureTheory.volume)
    (hκ : MeasureTheory.Integrable (Function.uncurry κ) MeasureTheory.volume)
    (hk' : MeasureTheory.Integrable (Function.uncurry k') MeasureTheory.volume)
    (hκ' : MeasureTheory.Integrable (Function.uncurry κ') MeasureTheory.volume) :
    Work.BoseBoxFock.q1WordK ℓ (fun a b => k a b + κ a b) Φ
        + Work.BoseBoxFock.q4WordK ℓ (fun a b => k' a b + κ' a b) Φ
      = Work.BoseBoxFock.q1WordK ℓ k Φ + Work.BoseBoxFock.q1WordK ℓ κ Φ
        + Work.BoseBoxFock.q4WordK ℓ k' Φ + Work.BoseBoxFock.q4WordK ℓ κ' Φ := by
  by_cases hℓ : 0 < ℓ
  · rw [q1WordK_add_of_pos hℓ Φ hΦc hk hκ,
        q4WordK_add_of_pos hℓ Φ hΦc hk' hκ']
    ring
  · have hle : ℓ ≤ 0 := not_lt.mp hℓ
    rw [q1WordK_eq_zero_of_nonpos hle (fun a b => k a b + κ a b) Φ,
        q1WordK_eq_zero_of_nonpos hle k Φ,
        q1WordK_eq_zero_of_nonpos hle κ Φ,
        q4WordK_eq_zero_of_nonpos hle (fun a b => k' a b + κ' a b) Φ,
        q4WordK_eq_zero_of_nonpos hle k' Φ,
        q4WordK_eq_zero_of_nonpos hle κ' Φ]
    ring

end Work.BoseBoxFock
