import ChallengeDeps
import Submission.Work.BoseFixB3.Split.ellKapDichotomy
import Submission.Work.BoseFixB3.Split.integrableOn_abox_of_prod
import Submission.Work.BoseFixB3.Split.integrable_chi_wScaled_chi_local
import Submission.Work.BoseFixB3.Split.lowSlotBound
import Submission.Work.BoseFixB3.Split.lowSlotStronglyMeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB3.Split.b3SplitRoot_holds` — FS §7 Step 1 (`eq:ReduceQ3`, the splitting)

`Work.BoseFixB3.B3SplitRoot` is the identity

`q3word = q3lowWord + q3barWord`

at `ℓ = ellAt μ (a v)`, `κ = kapAt μ (a v)`, `w1 = w1At μ (a v) v h`.  Pointwise in the
configuration `x` the two sides differ only in their first factor:

`P_i(Q_jΦ) = lowSlot_j(Q_j P_i Φ) + highSlot_j(P_i Q_j Φ)`

(the two `lowSlot`s agree because `P_i` and `Q_j` commute across distinct slots, i.e. because
the two slot-`j` fibres `z ↦ Q_jP_iΦ(x_{j↦z})` and `z ↦ P_iQ_jΦ(x_{j↦z})` are equal).  So the
identity reduces to the additivity of the box integral, for which the three integrands must be
shown integrable; that is done by bounding the `lowSlot` factor (a `p`-integral with compactly
supported symbol, hence finite) and by the `L¹`-integrability of the kernel factor
`χ(x_i) W₁(x_i−x_j) χ(x_j)` (where the division defining `W₁ = g₀/(χ⋆χ)_ℓ` is compensated by the
`χ⋆χ`-factor, so that local `L¹` of `g₀` suffices).

The degenerate case `ellAt μ (a v) = 0` makes every word vanish.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Split

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Pointwise helpers -/

/-- `lowMult` of the zero function is zero. -/
lemma lowMult_zero (fc : LowCut) (κ ℓ : ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    lowMult fc κ ℓ (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) y = 0 := by
  have hbuf : (fun z : EuclideanSpace ℝ (Fin 3) =>
        (((acube ℓ).indicator (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) z : ℝ) : ℂ))
      = fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℂ) := by
    funext z
    by_cases hz : z ∈ acube ℓ <;> simp [Set.indicator, hz]
  have hkin : ∀ p : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
        (((acube ℓ).indicator (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) z : ℝ) : ℂ)) p = 0 := by
    intro p
    rw [show (fun z : EuclideanSpace ℝ (Fin 3) =>
        (((acube ℓ).indicator (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) z : ℝ) : ℂ))
        = fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℂ) from hbuf]
    simp [Submission.BoseGases.kinFT]
  unfold Work.BoseBoxFix.lowMult
  simp only [hkin, mul_zero]
  simp

/-- `lowSlot` vanishes on a pointwise-zero function. -/
lemma lowSlot_eq_zero {fc : LowCut} {κ ℓ : ℝ} {n : ℕ} (j : Fin n) {Ψ : X n → ℝ}
    (h : ∀ y, Ψ y = 0) (x : X n) :
    lowSlot fc κ ℓ j Ψ x = 0 := by
  have hfib : (fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Function.update x j z))
      = fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ) := by
    funext z; exact h _
  simp only [Work.BoseBoxFix.lowSlot]
  rw [hfib]
  exact lowMult_zero fc κ ℓ (x j)

/-- `highSlot` vanishes on a pointwise-zero function. -/
lemma highSlot_eq_zero {fc : LowCut} {κ ℓ : ℝ} {n : ℕ} (j : Fin n) {Ψ : X n → ℝ}
    (h : ∀ y, Ψ y = 0) (x : X n) :
    highSlot fc κ ℓ j Ψ x = 0 := by
  rw [Work.BoseFixB3.highSlot, h x, lowSlot_eq_zero j h x]
  ring

/-- The two slot-`j` fibres of `Q_j(P_iΦ)` and `P_i(Q_jΦ)` agree (the corpus's `aP_aQ_comm`
across distinct slots), hence the two `lowSlot`s agree — the fibre agreement behind the
splitting `Q₃ = Q̃₃ + Q̄₃`. -/
lemma lowSlot_aP_aQ {fc : LowCut} {κ ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    {Φ : X n → ℝ} (hΦ : Continuous Φ) (x : X n) :
    lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i Φ)) x = lowSlot fc κ ℓ j (aP ℓ i (aQ ℓ j Φ)) x := by
  have hfib : (fun z : EuclideanSpace ℝ (Fin 3) => (aQ ℓ j (aP ℓ i Φ)) (Function.update x j z))
      = fun z : EuclideanSpace ℝ (Fin 3) => (aP ℓ i (aQ ℓ j Φ)) (Function.update x j z) := by
    funext z
    exact (Submission.BoseGases.aP_aQ_comm hℓ hij hΦ (Function.update x j z)).symm
  simp only [Work.BoseBoxFix.lowSlot]
  rw [hfib]

/-- The pointwise splitting of the `3Q` first factor: `P_i(Q_jΦ)` is the sum of the low part
(of the `Q_jP_iΦ` fibre) and the high part. -/
lemma highSlot_aP_aQ {fc : LowCut} {κ ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    {Φ : X n → ℝ} (hΦ : Continuous Φ) (x : X n) :
    lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i Φ)) x + highSlot fc κ ℓ j (aP ℓ i (aQ ℓ j Φ)) x
      = aP ℓ i (aQ ℓ j Φ) x := by
  rw [lowSlot_aP_aQ hℓ i j hij hΦ x]
  rw [Work.BoseFixB3.highSlot]
  ring

/-- `wLoc ℓ g 0` is the `χ(x)W₁(x−y)χ(y)` kernel. -/
lemma wLoc_zero_eq (ℓ : ℝ) (g : ℝ³ → ℝ) (a b : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.wLoc ℓ g 0 a b
      = Submission.BoseGases.chiScale ℓ a * Submission.BoseGases.wScaled ℓ g (a - b)
        * Submission.BoseGases.chiScale ℓ b := by
  simp [Submission.BoseGases.wLoc, Submission.BoseGases.chiU, Submission.BoseGases.chiScale]

theorem b3SplitRoot_holds (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : Work.UBB.ScatSol v) (fc : Work.BoseBoxFix.LowCut) :
    Work.BoseFixB3.B3SplitRoot v h fc := by
  intro μ n Φ
  classical
  let Ψ : X n → ℝ := (Φ : X n → ℝ)
  by_cases hℓ0 : Work.BoseFixB3.ellAt μ (a v) = 0
  · -- ============ degenerate case: `ℓ = 0`, every word vanishes
    change q3word (Work.BoseFixB3.ellAt μ (a v)) (Work.BoseFixB3.w1At μ (a v) v h) Ψ
        = q3lowWord fc (Work.BoseFixB3.kapAt μ (a v)) (Work.BoseFixB3.ellAt μ (a v))
            (Work.BoseFixB3.w1At μ (a v) v h) Ψ
          + q3barWord fc (Work.BoseFixB3.kapAt μ (a v)) (Work.BoseFixB3.ellAt μ (a v))
            (Work.BoseFixB3.w1At μ (a v) v h) Ψ
    rw [hℓ0]
    have hA : ∀ {m : ℕ} (i : Fin m) (F : X m → ℝ) (x : X m), aP 0 i F x = 0 := by
      intro m i F x
      simp [Submission.BoseGases.aP]
    have hQ : ∀ {m : ℕ} (i : Fin m) (F : X m → ℝ) (x : X m), aQ 0 i F x = F x := by
      intro m i F x
      simp [Submission.BoseGases.aQ, hA i F x]
    have hq3 : q3word 0 (Work.BoseFixB3.w1At μ (a v) v h) Ψ = 0 := by
      simp only [Submission.BoseGases.q3word]
      have hsum : (∑ p ∈ pairSet n, (∫ x in abox n 0,
            aP 0 p.1 (aQ 0 p.2 Ψ) x * aQ 0 p.2 (aQ 0 p.1 Ψ) x
              * Work.BoseFixB3.w1At μ (a v) v h (x p.1) (x p.2))) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hz : (fun x : X n => aP 0 p.1 (aQ 0 p.2 Ψ) x * aQ 0 p.2 (aQ 0 p.1 Ψ) x
              * Work.BoseFixB3.w1At μ (a v) v h (x p.1) (x p.2)) = 0 := by
          funext x
          rw [hA p.1 (aQ 0 p.2 Ψ) x]
          simp
        rw [hz]
        simp
      rw [hsum, mul_zero]
    have hql : q3lowWord fc (Work.BoseFixB3.kapAt μ (a v)) 0
        (Work.BoseFixB3.w1At μ (a v) v h) Ψ = 0 := by
      simp only [Work.BoseBoxFix.q3lowWord]
      have hsum : (∑ p ∈ pairSet n, (∫ x in abox n 0,
            lowSlot fc (Work.BoseFixB3.kapAt μ (a v)) 0 p.2 (aQ 0 p.2 (aP 0 p.1 Ψ)) x
              * aQ 0 p.2 (aQ 0 p.1 Ψ) x
              * Work.BoseFixB3.w1At μ (a v) v h (x p.1) (x p.2))) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hz : (fun x : X n => lowSlot fc (Work.BoseFixB3.kapAt μ (a v)) 0 p.2
                (aQ 0 p.2 (aP 0 p.1 Ψ)) x * aQ 0 p.2 (aQ 0 p.1 Ψ) x
              * Work.BoseFixB3.w1At μ (a v) v h (x p.1) (x p.2)) = 0 := by
          funext x
          rw [lowSlot_eq_zero p.2 (fun y => by rw [hQ p.2 (aP 0 p.1 Ψ) y, hA p.1 Ψ y]) x]
          simp
        rw [hz]
        simp
      rw [hsum, mul_zero]
    have hqb : q3barWord fc (Work.BoseFixB3.kapAt μ (a v)) 0
        (Work.BoseFixB3.w1At μ (a v) v h) Ψ = 0 := by
      simp only [Work.BoseFixB3.q3barWord]
      have hsum : (∑ p ∈ pairSet n, (∫ x in abox n 0,
            highSlot fc (Work.BoseFixB3.kapAt μ (a v)) 0 p.2 (aP 0 p.1 (aQ 0 p.2 Ψ)) x
              * aQ 0 p.2 (aQ 0 p.1 Ψ) x
              * Work.BoseFixB3.w1At μ (a v) v h (x p.1) (x p.2))) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        have hz : (fun x : X n => highSlot fc (Work.BoseFixB3.kapAt μ (a v)) 0 p.2
                (aP 0 p.1 (aQ 0 p.2 Ψ)) x * aQ 0 p.2 (aQ 0 p.1 Ψ) x
              * Work.BoseFixB3.w1At μ (a v) v h (x p.1) (x p.2)) = 0 := by
          funext x
          rw [highSlot_eq_zero p.2 (fun y => by rw [hA p.1 (aQ 0 p.2 Ψ) y]) x]
          simp
        rw [hz]
        simp
      rw [hsum, mul_zero]
    rw [hq3, hql, hqb]
    ring
  · -- ============ main case: `ℓ ≠ 0`
    let ℓ : ℝ := Work.BoseFixB3.ellAt μ (a v)
    let κ : ℝ := Work.BoseFixB3.kapAt μ (a v)
    let W : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
      Work.BoseFixB3.w1At μ (a v) v h
    change q3word ℓ W Ψ = q3lowWord fc κ ℓ W Ψ + q3barWord fc κ ℓ W Ψ
    have hpos : 0 < ℓ ∧ 0 < κ := (ellKapDichotomy v h μ).resolve_left hℓ0
    have hℓ : 0 < ℓ := hpos.1
    have hκ : 0 < κ := hpos.2
    have hΦc : Continuous Ψ := Φ.contDiff.continuous
    -- TEMPORARY child facts (to be replaced by imports)
    have hg0li : LocallyIntegrable (Submission.BoseGases.g0 v h) volume := by
      have hw0 : IsScatteringSolution (Classical.choose h) v := (Classical.choose_spec h).2
      exact hw0.rhs_integrable
    have hKern : ∀ {m : ℕ} (i j : Fin m), i ≠ j →
        IntegrableOn (fun x : X m => Submission.BoseGases.chiScale ℓ (x i)
            * Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) (x i - x j)
            * Submission.BoseGases.chiScale ℓ (x j)) (abox m ℓ) volume :=
      fun i j hij => integrableOn_abox_of_prod hℓ
        (integrable_chi_wScaled_chi_local hℓ hg0li) i j hij
    have hLowBd : ∀ {m : ℕ} (j : Fin m) (F : X m → ℝ), Continuous F →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ abox m ℓ, |lowSlot fc κ ℓ j F x| ≤ C :=
      fun j F hF => lowSlotBound (fc := fc) (κ := κ) (ℓ := ℓ) hκ hℓ j hF
    have hLowMes : ∀ {m : ℕ} (j : Fin m) (F : X m → ℝ), Continuous F →
        StronglyMeasurable (fun x : X m => lowSlot fc κ ℓ j F x) :=
      fun j F hF => lowSlotStronglyMeasurable (fc := fc) (κ := κ) (ℓ := ℓ) j hF
    -- bound of the state on the box
    obtain ⟨B0, hB0⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn hΦc.continuousOn
    have h0cube : (0 : EuclideanSpace ℝ (Fin 3)) ∈ acube ℓ := by
      refine mem_acube_of_norm_le hℓ.le ?_
      rw [norm_zero]; linarith
    have habox_ne : (abox n ℓ).Nonempty := ⟨0, fun i => by simpa using h0cube⟩
    have hB0nn : 0 ≤ B0 := le_trans (norm_nonneg _) (hB0 habox_ne.some habox_ne.some_mem)
    have hB0' : ∀ x ∈ abox n ℓ, |Ψ x| ≤ B0 := fun x hx => by
      simpa [Real.norm_eq_abs] using hB0 x hx
    have hPbd : ∀ (i : Fin n), ∀ x ∈ abox n ℓ, |aP ℓ i Ψ x| ≤ B0 :=
      fun i x hx => aP_abs_le hℓ i hΦc hB0nn hB0' x hx
    have hQbd : ∀ (i : Fin n), ∀ x ∈ abox n ℓ, |aQ ℓ i Ψ x| ≤ 2 * B0 := by
      intro i x hx
      rw [Submission.BoseGases.aQ]
      calc |Ψ x - aP ℓ i Ψ x| ≤ |Ψ x| + |aP ℓ i Ψ x| := abs_sub _ _
        _ ≤ B0 + B0 := add_le_add (hB0' x hx) (hPbd i x hx)
        _ = 2 * B0 := by ring
    -- the per-pair term identity
    have hterm : ∀ p ∈ pairSet n,
        (∫ x in abox n ℓ, lowSlot fc κ ℓ p.2 (aQ ℓ p.2 (aP ℓ p.1 Ψ)) x
              * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2))
          + (∫ x in abox n ℓ, highSlot fc κ ℓ p.2 (aP ℓ p.1 (aQ ℓ p.2 Ψ)) x
              * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2))
          = ∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Ψ) x
              * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2) := by
      intro p hp
      have hpne : p.1 ≠ p.2 := by simpa [pairSet] using hp
      -- the kernel factor is integrable on the box
      have hKint : IntegrableOn (fun x : X n => W (x p.1) (x p.2)) (abox n ℓ) volume := by
        refine (hKern p.1 p.2 hpne).congr ?_
        filter_upwards with x
        exact (wLoc_zero_eq ℓ (Submission.BoseGases.g0 v h) (x p.1) (x p.2)).symm
      -- the coefficient `Q_jQ_iΨ` is bounded
      have hQ2bd : ∀ x ∈ abox n ℓ, |aQ ℓ p.2 (aQ ℓ p.1 Ψ) x| ≤ 4 * B0 := by
        intro x hx
        rw [Submission.BoseGases.aQ]
        calc |aQ ℓ p.1 Ψ x - aP ℓ p.2 (aQ ℓ p.1 Ψ) x|
            ≤ |aQ ℓ p.1 Ψ x| + |aP ℓ p.2 (aQ ℓ p.1 Ψ) x| := abs_sub _ _
          _ ≤ 2 * B0 + 2 * B0 :=
              add_le_add (hQbd p.1 x hx)
                (aP_abs_le hℓ p.2 (aQ_continuous hℓ p.1 hΦc) (by positivity) (hQbd p.1) x hx)
          _ = 4 * B0 := by ring
      have hAbd : ∀ x ∈ abox n ℓ, |aP ℓ p.1 (aQ ℓ p.2 Ψ) x| ≤ 2 * B0 :=
        fun x hx => aP_abs_le hℓ p.1 (aQ_continuous hℓ p.2 hΦc) (by positivity) (hQbd p.2) x hx
      -- the coefficient times the kernel is integrable
      have hBc : Continuous (aQ ℓ p.2 (aQ ℓ p.1 Ψ)) :=
        aQ_continuous hℓ p.2 (aQ_continuous hℓ p.1 hΦc)
      have hBK : IntegrableOn (fun x : X n => aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2))
          (abox n ℓ) volume := by
        refine Integrable.bdd_mul (c := 4 * B0) hKint hBc.aestronglyMeasurable ?_
        filter_upwards [MeasureTheory.self_mem_ae_restrict (abox_measurable n ℓ)] with x hx
        simpa [Real.norm_eq_abs] using hQ2bd x hx
      -- any bounded, a.e.-measurable factor can be put in front of it
      have key : ∀ {f : X n → ℝ} {Cf : ℝ},
          AEStronglyMeasurable f (volume.restrict (abox n ℓ)) →
          (∀ x ∈ abox n ℓ, ‖f x‖ ≤ Cf) →
          IntegrableOn (fun x : X n => f x * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2))
            (abox n ℓ) volume := by
        intro f Cf hf hfbd
        have h1 : Integrable (fun x : X n =>
            f x * (aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)))
            (volume.restrict (abox n ℓ)) := by
          refine Integrable.bdd_mul (c := Cf) hBK hf ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict (abox_measurable n ℓ)] with x hx
          exact hfbd x hx
        exact h1.congr (Filter.Eventually.of_forall (fun x => by ring))
      -- the low part
      have hLow : IntegrableOn (fun x : X n => lowSlot fc κ ℓ p.2 (aQ ℓ p.2 (aP ℓ p.1 Ψ)) x
            * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)) (abox n ℓ) volume := by
        have hcont : Continuous (aQ ℓ p.2 (aP ℓ p.1 Ψ)) :=
          aQ_continuous hℓ p.2 (aP_continuous hℓ p.1 hΦc)
        obtain ⟨C, hCnn, hC⟩ := hLowBd p.2 (aQ ℓ p.2 (aP ℓ p.1 Ψ)) hcont
        refine key (Cf := C) ?_ ?_
        · exact (hLowMes p.2 (aQ ℓ p.2 (aP ℓ p.1 Ψ)) hcont).aestronglyMeasurable
        · intro x hx
          simpa [Real.norm_eq_abs] using hC x hx
      -- the high part
      have hHigh : IntegrableOn (fun x : X n => highSlot fc κ ℓ p.2 (aP ℓ p.1 (aQ ℓ p.2 Ψ)) x
            * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)) (abox n ℓ) volume := by
        have hcont : Continuous (aP ℓ p.1 (aQ ℓ p.2 Ψ)) :=
          aP_continuous hℓ p.1 (aQ_continuous hℓ p.2 hΦc)
        obtain ⟨C, hCnn, hC⟩ := hLowBd p.2 (aP ℓ p.1 (aQ ℓ p.2 Ψ)) hcont
        refine key (Cf := 2 * B0 + C) ?_ ?_
        · refine ((hcont.aestronglyMeasurable).sub
              ((hLowMes p.2 (aP ℓ p.1 (aQ ℓ p.2 Ψ)) hcont).aestronglyMeasurable)).congr ?_
          filter_upwards with x
          simp [Work.BoseFixB3.highSlot]
        · intro x hx
          rw [Work.BoseFixB3.highSlot, Real.norm_eq_abs]
          calc |aP ℓ p.1 (aQ ℓ p.2 Ψ) x - lowSlot fc κ ℓ p.2 (aP ℓ p.1 (aQ ℓ p.2 Ψ)) x|
              ≤ |aP ℓ p.1 (aQ ℓ p.2 Ψ) x| + |lowSlot fc κ ℓ p.2 (aP ℓ p.1 (aQ ℓ p.2 Ψ)) x| :=
                abs_sub _ _
            _ ≤ 2 * B0 + C := add_le_add (hAbd x hx) (hC x hx)
      -- the pointwise identity of the integrands
      have hpoint : ∀ x : X n,
          lowSlot fc κ ℓ p.2 (aQ ℓ p.2 (aP ℓ p.1 Ψ)) x
              * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)
            + highSlot fc κ ℓ p.2 (aP ℓ p.1 (aQ ℓ p.2 Ψ)) x
              * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)
          = aP ℓ p.1 (aQ ℓ p.2 Ψ) x
              * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2) := by
        intro x
        have hsplit := highSlot_aP_aQ (fc := fc) (κ := κ) (ℓ := ℓ) hℓ p.1 p.2 hpne hΦc x
        calc lowSlot fc κ ℓ p.2 (aQ ℓ p.2 (aP ℓ p.1 Ψ)) x
                * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)
              + highSlot fc κ ℓ p.2 (aP ℓ p.1 (aQ ℓ p.2 Ψ)) x
                * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)
            = (lowSlot fc κ ℓ p.2 (aQ ℓ p.2 (aP ℓ p.1 Ψ)) x
                + highSlot fc κ ℓ p.2 (aP ℓ p.1 (aQ ℓ p.2 Ψ)) x)
              * (aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)) := by ring
          _ = aP ℓ p.1 (aQ ℓ p.2 Ψ) x
              * (aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)) := by rw [hsplit]
          _ = aP ℓ p.1 (aQ ℓ p.2 Ψ) x
              * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2) := by ring
      rw [← integral_add hLow hHigh]
      exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    -- ---- assembly
    have hsum : (∑ p ∈ pairSet n,
          ((∫ x in abox n ℓ, lowSlot fc κ ℓ p.2 (aQ ℓ p.2 (aP ℓ p.1 Ψ)) x
              * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2))
          + (∫ x in abox n ℓ, highSlot fc κ ℓ p.2 (aP ℓ p.1 (aQ ℓ p.2 Ψ)) x
              * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2))))
        = ∑ p ∈ pairSet n, (∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Ψ) x
              * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)) :=
      Finset.sum_congr rfl hterm
    calc q3word ℓ W Ψ
        = 2 * ∑ p ∈ pairSet n, (∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Ψ) x
              * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)) := rfl
      _ = 2 * ∑ p ∈ pairSet n,
            ((∫ x in abox n ℓ, lowSlot fc κ ℓ p.2 (aQ ℓ p.2 (aP ℓ p.1 Ψ)) x
                * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2))
            + (∫ x in abox n ℓ, highSlot fc κ ℓ p.2 (aP ℓ p.1 (aQ ℓ p.2 Ψ)) x
                * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2))) := by
            rw [← hsum]
      _ = 2 * ((∑ p ∈ pairSet n, (∫ x in abox n ℓ, lowSlot fc κ ℓ p.2
                (aQ ℓ p.2 (aP ℓ p.1 Ψ)) x
                * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)))
            + (∑ p ∈ pairSet n, (∫ x in abox n ℓ, highSlot fc κ ℓ p.2
                (aP ℓ p.1 (aQ ℓ p.2 Ψ)) x
                * aQ ℓ p.2 (aQ ℓ p.1 Ψ) x * W (x p.1) (x p.2)))) := by
            rw [Finset.sum_add_distrib]
      _ = q3lowWord fc κ ℓ W Ψ + q3barWord fc κ ℓ W Ψ := by
            rw [Work.BoseBoxFix.q3lowWord, Work.BoseFixB3.q3barWord]
            ring

end Work.BoseFixB3.Split
