import Mathlib
import Submission.Work.BoseBoxFock.pairGBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.BoseBoxFock.pairGc23_continuous` — joint continuity of the clean `pairGc23` fibre

The clean fibre `pairGc23 ℓ p hp Θ₀ A B` of `Work.BoseBoxFock.pairGCore` is the *set* integral

    ∫ z in (boxPiSet ({k // k ≠ p.1 ∧ k ≠ p.2}) ℓ) ×ˢ (boxL ℓ ×ˢ boxL ℓ),
        star (Θ₀ (insertCoord2 p w₀ w₁ z.1)) * star (A z.2.1) * star (B z.2.2)
          * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)

over the compact product box `K`.  The dependence on the parameters `(w₀, w₁)` sits **only** in the
factor `star (Θ₀ (insertCoord2 p w₀ w₁ z.1))`, which is smooth; the remaining three factors are
fixed in the parameter and only *measurable and bounded* (`A`, `B` carry no continuity hypothesis,
only `Measurable` plus a pointwise bound).  Hence this is a *weighted* parametric integral, and it
is not reachable from `contDiff_setIntegral_compact_gen` (which needs joint continuity of the whole
integrand).  The appropriate tool is the dominated convergence theorem for filters with a countable
basis, which is what the general brick `continuousAt_setIntegral_mul_of_compact` below provides:

* the weight `z ↦ star (A z.2.1) * star (B z.2.2) * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)` is
  measurable and bounded by `cA·cB·M` on the compact box `K` (`M` a bound for `Θ₀` on the image of
  `K` under `insertCoord2`, obtained from `exists_bound_on_abox`);
* the parametric factor `(q, z) ↦ star (Θ₀ (insertCoord2 p q.1 q.2 z.1))` is jointly continuous;
* `K` has finite measure, so a *constant* dominating function is integrable on `K`, and the
  pointwise convergence of the parametric factor gives continuity of the integral.

`sorry`-free.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- **Continuity at a point of a parametric integral over a compact set with a measurable weight.**
For a compact `k`, a measurable weight `h` which is bounded on `k`, and a jointly continuous
`g : P → Z → ℂ`, the map `p ↦ ∫ z in k, h z * g p z` is continuous at every point `p₀`.

(Only continuity of `g` is used; no continuity of `h` is assumed.  This is the `ContinuousAt` form
of the general brick; `Continuous (fun p => ∫ z in k, h z * g p z)` follows from
`continuous_iff_continuousAt`.) -/
theorem continuousAt_setIntegral_mul_of_compact
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasureSpace Z] [BorelSpace Z]
    [IsFiniteMeasureOnCompacts (volume : Measure Z)]
    {P : Type*} [PseudoMetricSpace P] [ProperSpace P]
    {k : Set Z} (hk : IsCompact k)
    {h : Z → ℂ} (hh : Measurable h) (hb : ∃ C : ℝ, ∀ z ∈ k, ‖h z‖ ≤ C)
    {g : P → Z → ℂ} (hg : Continuous (Function.uncurry g)) (p₀ : P) :
    ContinuousAt (fun p => ∫ z in k, h z * g p z) p₀ := by
  haveI : IsFiniteMeasure (volume.restrict k) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hk.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hb
  -- local uniform bound for the continuous factor, on the compact `closedBall p₀ 1 ×ˢ k`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ q ∈ Metric.closedBall p₀ 1 ×ˢ k, ‖Function.uncurry g q‖ ≤ M :=
    ((isCompact_closedBall p₀ 1).prod hk).exists_bound_of_continuousOn hg.continuousOn
  have hmeas : ∀ᶠ p in 𝓝 p₀, AEStronglyMeasurable (fun z => h z * g p z) (volume.restrict k) := by
    filter_upwards with p
    have hgp : Continuous (fun z => g p z) := hg.comp (continuous_const.prodMk continuous_id)
    exact (hh.mul hgp.measurable).aestronglyMeasurable
  have hbnd : ∃ C' : ℝ, ∀ᶠ p in 𝓝 p₀,
      ∀ᵐ z ∂(volume.restrict k), ‖h z * g p z‖ ≤ C' := by
    refine ⟨max C 0 * max M 0, ?_⟩
    filter_upwards [Metric.closedBall_mem_nhds p₀ (by norm_num : (0 : ℝ) < 1)] with p hp
    filter_upwards [self_mem_ae_restrict hk.isClosed.measurableSet] with z hz
    rw [norm_mul]
    exact mul_le_mul (le_max_of_le_left (hC z hz)) (le_max_of_le_left (hM (p, z) ⟨hp, hz⟩))
      (norm_nonneg _) (le_max_right _ _)
  have hlim : ∀ᵐ z ∂(volume.restrict k),
      Tendsto (fun p => h z * g p z) (𝓝 p₀) (𝓝 (h z * g p₀ z)) := by
    filter_upwards with z
    have hgp : Continuous (fun p : P => g p z) :=
      hg.comp (continuous_id.prodMk continuous_const)
    exact (continuous_const.mul hgp).continuousAt
  exact MeasureTheory.tendsto_integral_filter_of_norm_le_const hmeas hbnd hlim

/-! ## The two factors of the integrand -/

/-- **The weight of the `pairGc23` fibre is measurable.**  It is the parameter-free part of the
integrand: `z ↦ star (A z.2.1) * star (B z.2.2) * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)`. -/
private theorem pairGc23Weight_measurable_aux {n : ℕ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    {A B : E3 → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun z : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3) =>
      star (A z.2.1) * star (B z.2.2) * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)) := by
  have hπ : Measurable (fun z : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3) =>
      insertCoord2 p z.2.1 z.2.2 z.1) := by
    rw [measurable_pi_iff]
    intro k
    by_cases h1 : k = p.1
    · have : (fun z : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3) =>
          insertCoord2 p z.2.1 z.2.2 z.1 k) = fun z => z.2.1 := by
        funext z; simp only [insertCoord2_eq, dif_pos h1]
      rw [this]; exact (continuous_snd.fst).measurable
    · by_cases h2 : k = p.2
      · have : (fun z : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3) =>
            insertCoord2 p z.2.1 z.2.2 z.1 k) = fun z => z.2.2 := by
          funext z; simp only [insertCoord2_eq, dif_neg h1, dif_pos h2]
        rw [this]; exact (continuous_snd.snd).measurable
      · have : (fun z : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3) =>
            insertCoord2 p z.2.1 z.2.2 z.1 k) = fun z => z.1 ⟨k, h1, h2⟩ := by
          funext z; simp only [insertCoord2_eq, dif_neg h1, dif_neg h2]
        rw [this]
        exact ((continuous_apply (A := fun _ : {i : Fin n // i ≠ p.1 ∧ i ≠ p.2} => E3)
          ⟨k, h1, h2⟩).comp continuous_fst).measurable
  exact ((continuous_star.measurable.comp (hA.comp (continuous_snd.fst).measurable)).mul
    (continuous_star.measurable.comp (hB.comp (continuous_snd.snd).measurable))).mul
    (hΘ₀.continuous.measurable.comp hπ)

/-- **The weight of the `pairGc23` fibre is bounded on the box.** -/
private theorem pairGc23Weight_bounded_aux {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {Θ₀ : Xn n → ℂ} {A B : E3 → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) :
    ∃ C : ℝ, ∀ z ∈ boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ
        ×ˢ (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ),
      ‖star (A z.2.1) * star (B z.2.2) * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_abox hℓ hΘ₀.continuous
  refine ⟨cA * cB * M, fun z hz => ?_⟩
  obtain ⟨hz1, hz2, hz3⟩ := Set.mem_prod.mp hz
  have hz2' : z.2.1 ∈ Work.BoseK15.corpusBox.boxL ℓ := hz2
  have hz3' : z.2.2 ∈ Work.BoseK15.corpusBox.boxL ℓ := hz3
  have hab : insertCoord2 p z.2.1 z.2.2 z.1 ∈ Submission.BoseGases.abox n ℓ :=
    (insertCoord2_mem_abox_iff hℓ hz2' hz3' z.1).mpr hz1
  calc ‖star (A z.2.1) * star (B z.2.2) * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖
      = ‖A z.2.1‖ * ‖B z.2.2‖ * ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ := by
        rw [norm_mul, norm_mul, norm_star, norm_star]
    _ ≤ cA * cB * M := by
        have h1 : ‖A z.2.1‖ ≤ cA := hAb _
        have h2 : ‖B z.2.2‖ ≤ cB := hBb _
        have h3 : ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ ≤ M := hM _ hab
        have h1' : 0 ≤ ‖A z.2.1‖ := norm_nonneg _
        have h2' : 0 ≤ ‖B z.2.2‖ := norm_nonneg _
        have h3' : 0 ≤ ‖Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1)‖ := norm_nonneg _
        have hcA' : 0 ≤ cA := le_trans h1' h1
        have hcB' : 0 ≤ cB := le_trans h2' h2
        have hAB : ‖A z.2.1‖ * ‖B z.2.2‖ ≤ cA * cB := mul_le_mul h1 h2 h2' hcA'
        exact mul_le_mul hAB h3 h3' (mul_nonneg hcA' hcB')

/-- **The parametric factor of the `pairGc23` fibre is jointly smooth.**  Only the first factor
`star (Θ₀ (insertCoord2 p q.1 q.2 z.1))` of the integrand depends on the parameters `q = (w₀, w₁)`;
it is the composition of the smooth `Θ₀` with the smooth insertion map. -/
private theorem pairGc23Kernel_contDiff_aux {n : ℕ} (p : Fin n × Fin n) {Θ₀ : Xn n → ℂ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (fun (q : E3 × E3)
      (z : ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3)) =>
      star (Θ₀ (insertCoord2 p q.1 q.2 z.1)))) := by
  have hw₀ : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : (E3 × E3) × (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3)) => s.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hw₁ : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : (E3 × E3) × (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3)) => s.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hx : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : (E3 × E3) × (({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) × (E3 × E3)) => s.2.1) :=
    contDiff_fst.comp contDiff_snd
  exact contDiff_starC.comp (hΘ₀.comp (contDiff_insertCoord2_comp p hw₀ hw₁ hx))

/-! ## The main theorem -/

theorem pairGc23_continuous {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {cA cB : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀)
    (hA : Measurable A) (hB : Measurable B)
    (hAb : ∀ x, ‖A x‖ ≤ cA) (hBb : ∀ x, ‖B x‖ ≤ cB) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) :
    Continuous (Function.uncurry (Work.BoseBoxFock.pairGc23 ℓ p hp Θ₀ A B)) := by
  classical
  -- the box `K` of the fibre is compact
  have hKc : IsCompact (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ
      ×ˢ (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)) :=
    (isCompact_boxPiSet hℓ).prod
      ((Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).prod
        (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ))
  -- the fibre is the weighted parametric integral of the lemma above
  have hrew : ∀ q : E3 × E3, pairGc23 ℓ p hp Θ₀ A B q.1 q.2
      = ∫ z in (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ
          ×ˢ (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)),
        (star (A z.2.1) * star (B z.2.2) * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1))
          * star (Θ₀ (insertCoord2 p q.1 q.2 z.1)) := by
    intro q
    simp only [pairGc23]
    congr 1
    funext z
    ring
  rw [show Function.uncurry (pairGc23 ℓ p hp Θ₀ A B)
      = fun q : E3 × E3 => ∫ z in (boxPiSet ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) ℓ
          ×ˢ (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ)),
        (star (A z.2.1) * star (B z.2.2) * Θ₀ (insertCoord2 p z.2.1 z.2.2 z.1))
          * star (Θ₀ (insertCoord2 p q.1 q.2 z.1)) from by
    funext q
    exact hrew q]
  refine continuous_iff_continuousAt.mpr (fun q₀ => ?_)
  exact continuousAt_setIntegral_mul_of_compact hKc
    (pairGc23Weight_measurable_aux p hΘ₀ hA hB)
    (pairGc23Weight_bounded_aux hℓ p hΘ₀ hAb hBb)
    (pairGc23Kernel_contDiff_aux p hΘ₀).continuous q₀

end Work.BoseBoxFock
