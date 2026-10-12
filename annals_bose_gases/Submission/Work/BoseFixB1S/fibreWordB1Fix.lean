import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.PerBoxFibreB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

set_option maxHeartbeats 1000000

/-! ## 1. The measure-theoretic splitting lemmas for the localised word bound

`Submission.BoseGases.qLHSword ℓ μ w w₁ Φ` is *definitionally* the integral of
`Φ² · qLHSden ℓ μ w w₁` over the box, and
`qLHSden x = −μ Σᵢ w₁-fibre(xᵢ) + ½ Σ_{p∈pairSet} w(x_p)` is the parenthesised density of
FS's potential word.  The two lemmas below are the pure measure-theoretic content of the
per-box word bound: the split of that integral into the one-body sum and the two-body sum,
followed by the pointwise comparison supplied by the one-body fibre bound. -/

/-- **The configuration-integral split of `qLHSword` plus the fibre monotonicity.**

For an arbitrary state `Φ`, cutoff `χ`, one-body fibre profile `U`, two-body profile `W`,
chemical potential `μ ≥ 0` and fibre coefficient `κ`, if `U i x ≤ κ·χ i x` holds pointwise
for every `i` and `x`, then

    −(μκ)·Σ_i ∫ Φ²χ(i) + ½·Σ_{p∈s₂} ∫ Φ²W(p)  ≤  ∫ Φ²·(−μ Σ_i U(i) + ½ Σ_{p∈s₂} W(p)) ,

i.e. the LHS is bounded by the integral of the *true* diagonal density.  The integral
hypotheses are exactly the ones the split and the `integral_mono` step consume. -/
theorem wordLeOfFibre {E : Type*} [MeasurableSpace E] {ν : Measure E}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₂]
    {Φ : E → ℝ} {χ U : ι₁ → E → ℝ} {W : ι₂ → E → ℝ} {μ κ : ℝ} (s₂ : Finset ι₂)
    (hμ : 0 ≤ μ)
    (hfib : ∀ i : ι₁, ∀ x : E, U i x ≤ κ * χ i x)
    (hIχ : ∀ i : ι₁, Integrable (fun x : E => (Φ x) ^ 2 * χ i x) ν)
    (hIW : ∀ p ∈ s₂, Integrable (fun x : E => (Φ x) ^ 2 * W p x) ν)
    (hIden : Integrable (fun x : E =>
        (Φ x) ^ 2 * (-μ * (∑ i : ι₁, U i x) + (1 / 2) * (∑ p ∈ s₂, W p x))) ν) :
    -(μ * κ) * (∑ i : ι₁, ∫ x : E, (Φ x) ^ 2 * χ i x ∂ν)
      + (1 / 2) * (∑ p ∈ s₂, ∫ x : E, (Φ x) ^ 2 * W p x ∂ν)
    ≤ ∫ x : E, (Φ x) ^ 2 * (-μ * (∑ i : ι₁, U i x) + (1 / 2) * (∑ p ∈ s₂, W p x)) ∂ν := by
  have hχ : Integrable (fun x : E => ∑ i : ι₁, (Φ x) ^ 2 * χ i x) ν :=
    integrable_finsetSum Finset.univ (fun i _ => hIχ i)
  have hW : Integrable (fun x : E => ∑ p ∈ s₂, (Φ x) ^ 2 * W p x) ν :=
    integrable_finsetSum s₂ (fun p hp => hIW p hp)
  have pt : ∀ x : E, (Φ x) ^ 2 * (-(μ * κ) * (∑ i : ι₁, χ i x) + (1 / 2) * (∑ p ∈ s₂, W p x))
      = -(μ * κ) * (∑ i : ι₁, (Φ x) ^ 2 * χ i x)
        + (1 / 2) * (∑ p ∈ s₂, (Φ x) ^ 2 * W p x) := by
    intro x
    have eχ : (∑ i : ι₁, (Φ x) ^ 2 * χ i x) = (Φ x) ^ 2 * (∑ i : ι₁, χ i x) := by
      rw [Finset.mul_sum]
    have eW : (∑ p ∈ s₂, (Φ x) ^ 2 * W p x) = (Φ x) ^ 2 * (∑ p ∈ s₂, W p x) := by
      rw [Finset.mul_sum]
    rw [eχ, eW]
    ring
  have hAint : Integrable (fun x : E => (Φ x) ^ 2 *
      (-(μ * κ) * (∑ i : ι₁, χ i x) + (1 / 2) * (∑ p ∈ s₂, W p x))) ν :=
    ((hχ.const_mul (-(μ * κ))).add (hW.const_mul (1 / 2))).congr
      (Filter.Eventually.of_forall (fun x => (pt x).symm))
  have hsplit : (∫ x : E, (Φ x) ^ 2 *
        (-(μ * κ) * (∑ i : ι₁, χ i x) + (1 / 2) * (∑ p ∈ s₂, W p x)) ∂ν)
      = -(μ * κ) * (∑ i : ι₁, ∫ x : E, (Φ x) ^ 2 * χ i x ∂ν)
        + (1 / 2) * (∑ p ∈ s₂, ∫ x : E, (Φ x) ^ 2 * W p x ∂ν) := by
    have h1 : (∫ x : E, (Φ x) ^ 2 *
          (-(μ * κ) * (∑ i : ι₁, χ i x) + (1 / 2) * (∑ p ∈ s₂, W p x)) ∂ν)
        = ∫ x : E, (-(μ * κ) * (∑ i : ι₁, (Φ x) ^ 2 * χ i x)
            + (1 / 2) * (∑ p ∈ s₂, (Φ x) ^ 2 * W p x)) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall pt)
    have h2 : (∫ x : E, (-(μ * κ) * (∑ i : ι₁, (Φ x) ^ 2 * χ i x)
            + (1 / 2) * (∑ p ∈ s₂, (Φ x) ^ 2 * W p x)) ∂ν)
        = (∫ x : E, -(μ * κ) * (∑ i : ι₁, (Φ x) ^ 2 * χ i x) ∂ν)
          + (∫ x : E, (1 / 2) * (∑ p ∈ s₂, (Φ x) ^ 2 * W p x) ∂ν) :=
      integral_add (hχ.const_mul _) (hW.const_mul _)
    have h3a : (∫ x : E, -(μ * κ) * (∑ i : ι₁, (Φ x) ^ 2 * χ i x) ∂ν)
        = -(μ * κ) * (∫ x : E, (∑ i : ι₁, (Φ x) ^ 2 * χ i x) ∂ν) :=
      integral_const_mul _ _
    have h3b : (∫ x : E, (1 / 2) * (∑ p ∈ s₂, (Φ x) ^ 2 * W p x) ∂ν)
        = (1 / 2) * (∫ x : E, (∑ p ∈ s₂, (Φ x) ^ 2 * W p x) ∂ν) :=
      integral_const_mul _ _
    have h4a : (∫ x : E, (∑ i : ι₁, (Φ x) ^ 2 * χ i x) ∂ν)
        = ∑ i : ι₁, ∫ x : E, (Φ x) ^ 2 * χ i x ∂ν :=
      integral_finsetSum Finset.univ (fun i _ => hIχ i)
    have h4b : (∫ x : E, (∑ p ∈ s₂, (Φ x) ^ 2 * W p x) ∂ν)
        = ∑ p ∈ s₂, ∫ x : E, (Φ x) ^ 2 * W p x ∂ν :=
      integral_finsetSum s₂ (fun p hp => hIW p hp)
    rw [h1, h2, h3a, h3b, h4a, h4b]
  have hle : (fun x : E => (Φ x) ^ 2 *
        (-(μ * κ) * (∑ i : ι₁, χ i x) + (1 / 2) * (∑ p ∈ s₂, W p x)))
      ≤ (fun x : E => (Φ x) ^ 2 *
        (-μ * (∑ i : ι₁, U i x) + (1 / 2) * (∑ p ∈ s₂, W p x))) := by
    intro x
    change Φ x ^ 2 * (-(μ * κ) * (∑ i : ι₁, χ i x) + (1 / 2) * (∑ p ∈ s₂, W p x))
      ≤ Φ x ^ 2 * (-μ * (∑ i : ι₁, U i x) + (1 / 2) * (∑ p ∈ s₂, W p x))
    have hsum : (∑ i : ι₁, U i x) ≤ κ * (∑ i : ι₁, χ i x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => hfib i x)
    have h2' : μ * (∑ i : ι₁, U i x) ≤ μ * κ * (∑ i : ι₁, χ i x) := by
      have h3 := mul_le_mul_of_nonneg_left hsum hμ
      calc μ * (∑ i : ι₁, U i x) ≤ μ * (κ * (∑ i : ι₁, χ i x)) := h3
        _ = μ * κ * (∑ i : ι₁, χ i x) := by ring
    have h4 : -(μ * κ) * (∑ i : ι₁, χ i x) ≤ -μ * (∑ i : ι₁, U i x) := by
      have h := neg_le_neg h2'
      linarith [h]
    have h5 := mul_le_mul_of_nonneg_left h4 (sq_nonneg (Φ x))
    have e1 : (Φ x) ^ 2 * (-(μ * κ) * (∑ i : ι₁, χ i x) + (1 / 2) * (∑ p ∈ s₂, W p x))
        = (Φ x) ^ 2 * (-(μ * κ) * (∑ i : ι₁, χ i x))
          + (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ s₂, W p x)) := by ring
    have e2 : (Φ x) ^ 2 * (-μ * (∑ i : ι₁, U i x) + (1 / 2) * (∑ p ∈ s₂, W p x))
        = (Φ x) ^ 2 * (-μ * (∑ i : ι₁, U i x))
          + (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ s₂, W p x)) := by ring
    rw [e1, e2]
    linarith [h5]
  rw [← hsplit]
  exact integral_mono hAint hIden hle

/-- **Integrability of the `qLHSden`-weighted integrand** from the integrability of its
finitely many pieces: the sum of the one-body terms `Φ²·U` and the two-body terms `Φ²·W`. -/
theorem integrableSqSplit {E : Type*} [MeasurableSpace E] {ν : Measure E}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₂]
    {Φ : E → ℝ} {U : ι₁ → E → ℝ} {W : ι₂ → E → ℝ} {μ : ℝ} (s₂ : Finset ι₂)
    (hI1 : ∀ i : ι₁, Integrable (fun x : E => (Φ x) ^ 2 * U i x) ν)
    (hIW : ∀ p ∈ s₂, Integrable (fun x : E => (Φ x) ^ 2 * W p x) ν) :
    Integrable (fun x : E => (Φ x) ^ 2 *
      (-μ * (∑ i : ι₁, U i x) + (1 / 2) * (∑ p ∈ s₂, W p x))) ν := by
  have h1 : Integrable (fun x : E => -μ * (∑ i : ι₁, (Φ x) ^ 2 * U i x)) ν :=
    (integrable_finsetSum Finset.univ (fun i _ => hI1 i)).const_mul (-μ)
  have h2 : Integrable (fun x : E => (1 / 2) * (∑ p ∈ s₂, (Φ x) ^ 2 * W p x)) ν :=
    (integrable_finsetSum s₂ (fun p hp => hIW p hp)).const_mul (1 / 2)
  refine (h1.add h2).congr (Filter.Eventually.of_forall (fun x => ?_))
  change -μ * (∑ i : ι₁, (Φ x) ^ 2 * U i x) + (1 / 2) * (∑ p ∈ s₂, (Φ x) ^ 2 * W p x)
    = (Φ x) ^ 2 * (-μ * (∑ i : ι₁, U i x) + (1 / 2) * (∑ p ∈ s₂, W p x))
  have e1 : (∑ i : ι₁, (Φ x) ^ 2 * U i x) = (Φ x) ^ 2 * (∑ i : ι₁, U i x) := by
    rw [Finset.mul_sum]
  have e2 : (∑ p ∈ s₂, (Φ x) ^ 2 * W p x) = (Φ x) ^ 2 * (∑ p ∈ s₂, W p x) := by
    rw [Finset.mul_sum]
  rw [e1, e2]
  ring

/-! ## 2. The word bound at abstract parameters -/

/-- **The localised potential word bound** at abstract parameters `M`, `ℓ`, `dd`, `μ` and the
fixed fibre coefficient `K`: from the *pointwise* one-body fibre bound
`|w₁-fibre(z)| ≤ K·(a v)·χ_{B(u)}(z)` (which is exactly the first conjunct of the target, at
the same `K`) and the integrability of the finitely many pieces, the localised potential word
`qLHSwordB` dominates `−(K·μ·(a v))·Σᵢ∫Φ²χ + ½·Σ_{p}∫Φ²w_B`.

The chemical potential cancels between the fibre coefficient and the count coefficient, which
is why the *linear* fibre constant `K·(a v)` (and not `K·μ·(a v)`) is the right one. -/
theorem wordBound_of_fibre {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} {ℓ dd μ K : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    {u : EuclideanSpace ℝ (Fin 3)} (hμ : 0 < μ)
    (hfib : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ dd u) z
        ≤ (K * _root_.BoseGases.a v) * Submission.BoseGases.chiSmallB M ℓ dd u z)
    (hIχ : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ dd u (x i))
        (Submission.BoseGases.abox n ℓ))
    (hIw : ∀ p ∈ Submission.BoseGases.pairSet n, IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * Submission.BoseGases.wSmallPair M ℓ dd u v (x p.1) (x p.2))
        (Submission.BoseGases.abox n ℓ))
    (hI1 : ∀ i : Fin n, IntegrableOn (fun x : Submission.BoseGases.X n =>
        (Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ dd u) (x i))
        (Submission.BoseGases.abox n ℓ)) :
    -(K * (μ * _root_.BoseGases.a v))
        * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ dd u (x i))
      + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * Submission.BoseGases.wSmallPair M ℓ dd u v (x p.1) (x p.2))
      ≤ Work.SmallBoxSliding.qLHSwordB h M ℓ dd μ u Φ := by
  have hIden : Integrable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * (-μ * (∑ i : Fin n,
            Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ dd u) (x i))
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
            Submission.BoseGases.wSmallPair M ℓ dd u v (x p.1) (x p.2))))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    have hint := integrableSqSplit
      (ν := (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))
      (s₂ := Submission.BoseGases.pairSet n) (μ := μ)
      (U := fun (i : Fin n) (x : Submission.BoseGases.X n) =>
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ dd u) (x i))
      (W := fun (p : Fin n × Fin n) (x : Submission.BoseGases.X n) =>
        Submission.BoseGases.wSmallPair M ℓ dd u v (x p.1) (x p.2)) hI1 hIw
    simpa only using hint
  have hmain := wordLeOfFibre
    (ν := (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ))
    (s₂ := Submission.BoseGases.pairSet n)
    (χ := fun (i : Fin n) (x : Submission.BoseGases.X n) =>
      Submission.BoseGases.chiSmallB M ℓ dd u (x i))
    (U := fun (i : Fin n) (x : Submission.BoseGases.X n) =>
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ dd u) (x i))
    (W := fun (p : Fin n × Fin n) (x : Submission.BoseGases.X n) =>
      Submission.BoseGases.wSmallPair M ℓ dd u v (x p.1) (x p.2))
    (Φ := Φ) (μ := μ) (κ := K * _root_.BoseGases.a v)
    hμ.le (fun i x => hfib (x i)) hIχ hIw hIden
  rw [show K * (μ * _root_.BoseGases.a v) = μ * (K * _root_.BoseGases.a v) from by ring]
  rw [Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword_eq_integral_qLHSden]
  simp only [Submission.BoseGases.qLHSden]
  exact hmain

theorem fibreWordB1Fix {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ ξ : ℝ, 0 < ε₀ ∧ 0 ≤ ξ ∧
      (∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ (u x : EuclideanSpace ℝ (Fin 3)),
        |Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) x|
          ≤ ξ * (_root_.BoseGases.a v)
              * Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x) ∧
      (∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          -(ξ * (μ * (_root_.BoseGases.a v)))
                * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                    (Φ x) ^ 2 * Submission.BoseGases.chiSmallB
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (x i))
            + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
                ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                  (Φ x) ^ 2 * Submission.BoseGases.wSmallPair
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v (x p.1) (x p.2))
          ≤ Work.SmallBoxSliding.qLHSwordB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u
              (Φ : Submission.BoseGases.X n → ℝ)) := by
  classical
  obtain ⟨ε₀f, K, hε₀f, hK, hfibre⟩ := PerBoxFibreB1 (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₀r, hε₀r, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min ε₀f ε₀r, K, lt_min hε₀f hε₀r, hK, ?_, ?_⟩
  · intro μ hAdm u x
    have hAdmF : Work.BoseBoxFix.Adm v ε₀f μ :=
      ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
    have hb := hfibre μ hAdmF u x
    simpa only [Submission.BoseGases.w1Fibre] using hb
  · intro μ hAdm n Φ u
    have hμpos : 0 < μ := hAdm.1
    have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
    have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
    have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
      norm_num [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
    have hAdmF : Work.BoseBoxFix.Adm v ε₀f μ :=
      ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
    have hAdmR : Work.BoseBoxFix.Adm v ε₀r μ :=
      ⟨hAdm.1, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
    obtain ⟨hR16, hRχ⟩ := hreg μ hμpos (Work.BoseFixB1.adm_dilute hAdmR)
    have hvint : Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
    have hvsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → v z = 0 :=
      fun z hz => Work.SmallBoxSliding.eq_zero_of_tsupport_subset_ball hv_supp hz
    have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
    refine wordBound_of_fibre (h := h) (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (dd := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μ) (K := K) hμpos ?_ ?_ ?_ ?_
    · intro z
      have hb := hfibre μ hAdmF u z
      calc Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) z
          = ∫ y in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z y := rfl
        _ ≤ |∫ y in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z y| := le_abs_self _
        _ ≤ (K * _root_.BoseGases.a v)
              * Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z := hb
    · intro i
      refine Submission.BoseGases.integrableOn_abox_of_continuous hℓ ?_
      exact (hΦc.pow 2).mul
        ((Work.BoseFixB1.continuous_chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).comp (continuous_apply i))
    · intro p hp
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      obtain ⟨B, hB⟩ :=
        (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
          (s := Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (f := fun x : Submission.BoseGases.X n => (Φ x) ^ 2) ((hΦc.pow 2).continuousOn)
      have hB0 : 0 ≤ B := by
        have hb0 := hB 0 (Submission.BoseGases.zero_mem_abox hℓ.le)
        exact le_trans (norm_nonneg _) hb0
      have hSb : ∀ᵐ x ∂(volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          |(Φ x) ^ 2| ≤ B := by
        rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n _)]
        exact ae_of_all _ (fun x hx => by simpa [Real.norm_eq_abs] using hB x hx)
      have hint := Work.BoseFixB1.integrableOn_slot_wSmallPair (N := n)
        (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (R := R)
        hℓ hd hvint hvsupp hM1 hR16 hRχ u hne
        (S := fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
        ((hΦc.pow 2).aestronglyMeasurable) hB0 hSb
      simpa using hint
    · intro i
      have hg0 : Integrable (Submission.BoseGases.g0 v h) :=
        Submission.BoseGases.g0_integrable hR hv_supp h
      have hFm : AEStronglyMeasurable
          (fun z : EuclideanSpace ℝ (Fin 3) =>
            ∫ y in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                (Submission.BoseGases.g0 v h) z y)
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
            (Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) :=
        Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre _ u hg0.aestronglyMeasurable.aemeasurable
      have hbnd := Work.BoseFixB1.wSmall1Pair_fibre_abs_le hv_supp hR hv hvrad h hM1 hℓ hd hR16 hRχ u
      have hC : ∀ z ∈ Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          |∫ y in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                (Submission.BoseGases.g0 v h) z y|
            ≤ max 0 (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M *
                (2 * (Submission.BoseGases.chiSupAbs
                    * Submission.BoseGases.chiSmallDecay (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) /
                  Work.SmallBoxSliding.smallConvLower (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  * (8 * Real.pi * _root_.BoseGases.a v))) :=
        fun z _ => le_trans (hbnd z) (le_max_right _ _)
      have hint := Submission.BoseGases.integrableOn_slot_fibre hℓ i hFm hC
        (S := fun x : Submission.BoseGases.X n => (Φ x) ^ 2) (hΦc.pow 2)
      simpa [Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair] using hint

end Work.BoseFixB1S
