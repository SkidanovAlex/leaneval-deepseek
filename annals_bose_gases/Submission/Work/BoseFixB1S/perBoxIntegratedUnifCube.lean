import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1S.LowCountWindowAllJCube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.perBoxIntegratedUnifCube` - the matched-window integrated per-box node

The **cube-cutoff twin** of the PROVED `Work.BoseFixB1S.perBoxIntegratedUnif`.  That node is the
*integral over the interior set* `I₋` of the per-`u` per-box bound `Work.BoseFixB1.PerBoxF`,
collected into a single FS-scale error term `C·μ²(a v)ℓ³K_B³(μ(a v)³)^{1/2}‖Φ‖²`.  Here exactly the
same is done at the **matched (single cube cutoff) vocabulary** of
`Submission/Work/BoseFixB1B/matchedWindowDefs.lean`: the pointwise input is
`Work.BoseFixB1S.PerBoxFCube` and the word slot is `Work.BoseFixB1B.sbWordCube`.

The passage is *bookkeeping*: the demand side (`Work.BoseFixB1.RPsi`), the mass law for the
mean-field background, the `|I₋|` volume term and the FS error scale do not involve the window at
all — only the two `sbWord` slots change.  Hence the proof is the proof of
`Submission/Work/BoseFixB1S/perBoxIntegratedUnif.lean` with `sbWord ↦ sbWordCube` and
`PerBoxF ↦ PerBoxFCube`, verbatim:

* `ipw_le_rearrange_cube` - the pointwise rearrangement of `PerBoxFCube` into the shape that is
  integrated (the cube twin of `Work.BoseFixB1B.ipw_le_rearrange`);
* `integratedPerBoxUnifCube` - the integration over `I₋` with the *uncollected* FS error terms
  (the cube twin of `Work.BoseFixB1S.integratedPerBoxUnif`); its hypotheses are the `u`-marginal
  integrability of `sbWordCube` (`hsbInt`) and the one-body mass bound
  `w1MassB ≤ C·(a v)·chiMass` (`hw1le`, the PROVED
  `Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime`);
* the private arithmetic/facts `collect_coeff_cube`, `chiMass_interior_le_cube`, `inv_d_cube_le`,
  `volume_interiorSet_le_cube` - verbatim copies of the private helpers of
  `perBoxIntegratedUnif.lean`;
* the target `perBoxIntegratedUnifCube` - the collection node, a copy of `perBoxIntegratedUnif`
  with the same substitutions.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. The pointwise rearrangement at the matched window -/

/-- **`Work.BoseFixB1S.PerBoxFCube` rearranged** into the "`u`-wise inequality between the two
integrands" shape that is integrated over `I₋`: the cube twin of
`Work.BoseFixB1B.ipw_le_rearrange`.  Pure unfolding plus `linarith`. -/
lemma ipw_le_rearrange_cube {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R c₁ C μ : ℝ} {n : ℕ} {Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))}
    {u : EuclideanSpace ℝ (Fin 3)} (hper : Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u) :
    c₁ * (w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), (Φ x) ^ 2 *
          psiWeight 1 μ (nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x /
            chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u)))
      ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)
        + (1 / 2) * μ ^ 2 * w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
            (paramsAt μ (a v)).d u * normB v μ n (Φ : X n → ℝ)
        + C * (μ ^ 2 * (a v) * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
              * chiMass (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u
              * normB v μ n (Φ : X n → ℝ)
            + μ * (a v) * normB v μ n (Φ : X n → ℝ)) := by
  rw [Work.BoseFixB1S.PerBoxFCube] at hper
  linarith

/-! ## 1. The `J`-free integrated per-box bound at the matched window -/

theorem integratedPerBoxUnifCube {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hper : ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          ∀ (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u)
    (hsbInt : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ {n : ℕ}
      (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
      MeasureTheory.IntegrableOn
        (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
        (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ))
    (hw1le : ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      ≤ C * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
            c₁ * Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ)
              ≤ (∫ u in Work.SmallBoxSliding.interiorSet
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                    Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
                + (1 / 2) * μ ^ 2
                    * (∫ u in Work.SmallBoxSliding.interiorSet
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                        Work.BoseFixB1.w1MassB h
                          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                + C * (μ ^ 2 * (_root_.BoseGases.a v)
                          * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                                    * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                              + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                          * (∫ u in Work.SmallBoxSliding.interiorSet
                              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                              Work.SmallBoxSliding.chiMass
                                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                        + μ * (_root_.BoseGases.a v)
                          * (MeasureTheory.volume (Work.SmallBoxSliding.interiorSet
                              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨ε₀, c₁, C, hε₀, hc₁, hC, hmain⟩ := hper
  obtain ⟨ε₀s, hε₀s, hsbInt⟩ := hsbInt
  obtain ⟨ε₀w, Cw, hε₀w, hCw0, hCw⟩ := hw1le
  refine ⟨min ε₀ (min ε₀s ε₀w), c₁, C, lt_min hε₀ (lt_min hε₀s hε₀w), hc₁, hC, ?_⟩
  intro μ hAdm n Φ
  have hAdm₀ : Work.BoseBoxFix.Adm v ε₀ μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdms : Work.BoseBoxFix.Adm v ε₀s μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdmw : Work.BoseBoxFix.Adm v ε₀w μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
  have hμ : 0 < μ := hAdm.1
  -- local abbreviations (definitional, so all the rewrites below are defeq-compatible)
  let ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  let dd : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
  let MM : ℕ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
  let av : ℝ := _root_.BoseGases.a v
  let KB : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB
  let G : ℝ := (R / (ℓ * dd)) ^ 2 + KB ^ 3 * (μ * av ^ 3) ^ (1 / 2 : ℝ)
  let nB : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
  let I : Set (EuclideanSpace ℝ (Fin 3)) := Work.SmallBoxSliding.interiorSet ℓ dd μ
  let AA : EuclideanSpace ℝ (Fin 3) → ℝ := fun u =>
    ∫ x in abox n ℓ, (Φ x) ^ 2 *
      Work.SmallBoxSliding.psiWeight 1 μ
        (Work.BoseFixB1.nCountB MM ℓ dd u x / Work.SmallBoxSliding.chiMass MM ℓ dd u)
  let ff : EuclideanSpace ℝ (Fin 3) → ℝ := fun u =>
    c₁ * (Work.BoseFixB1.w1MassB h MM ℓ dd u * AA u)
  let gg : EuclideanSpace ℝ (Fin 3) → ℝ := fun u =>
    Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ)
      + (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB
      + C * (μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB + μ * av * nB)
  have hℓpos : 0 < ℓ := Work.BoseFixB1.adm_ell_pos hAdm
  have hdpos : 0 < dd := Work.BoseFixB1.adm_d_pos hAdm
  have hImeas : MeasurableSet I := Work.SmallBoxSliding.measurableSet_interiorSet ℓ dd μ
  have hIvol : MeasureTheory.volume I ≠ ⊤ :=
    Work.BoseFixB1.volume_interiorSet_ne_top hℓpos hdpos
  -- (1) the pointwise inequality on `I₋ ⊆ goodSet`
  have hpt : ∀ u ∈ I, ff u ≤ gg u := by
    intro u hu
    have hmem : u ∈ Work.SmallBoxSliding.interiorSet ℓ dd μ := hu
    have hp : Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u := hmain μ hAdm₀ n Φ u hmem
    exact ipw_le_rearrange_cube hp
  -- (2) the right-hand side is integrable on `I₋`
  have hM1 : 1 ≤ MM := by
    simp [MM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
  have hchiOn : IntegrableOn (fun u => Work.SmallBoxSliding.chiMass MM ℓ dd u) I :=
    ((Work.SmallBoxSliding.integrable_chiSmallB_mass hM1 hℓpos hdpos).congr
      (Filter.Eventually.of_forall fun u =>
        (Work.SmallBoxSliding.chiMass_def MM ℓ dd u).symm)).integrableOn
  have hw1Measc : AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.w1MassB h MM ℓ dd u) volume :=
    Work.BoseFixB1B.aeStronglyMeasurable_w1MassB_global (v := v) h hv hvrad hR hv_supp hℓpos hdpos
  have hw1On : IntegrableOn (fun u => Work.BoseFixB1.w1MassB h MM ℓ dd u) I := by
    refine Integrable.mono' (hchiOn.const_mul (Cw * av)) hw1Measc.restrict ?_
    filter_upwards with u
    have h1 : 0 ≤ Work.BoseFixB1.w1MassB h MM ℓ dd u :=
      Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓpos hdpos u
    have h3 := hCw μ hAdmw u
    rw [Real.norm_of_nonneg h1]
    simpa only [MM, ℓ, dd, av] using h3
  have hsbOn : IntegrableOn
      (fun u => Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ)) I :=
    hsbInt μ hAdms (Φ := Φ)
  have hYint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => μ * av * nB) I :=
    integrableOn_const hIvol enorm_ne_top
  have hXint : IntegrableOn
      (fun u => μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB) I :=
    ((hchiOn.const_mul (μ ^ 2 * av * G)).const_mul nB).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have h2 : IntegrableOn
      (fun u => (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB) I :=
    ((hw1On.const_mul ((1 / 2) * μ ^ 2)).const_mul nB).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have h3 : IntegrableOn
      (fun u => C * (μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB
        + μ * av * nB)) I :=
    (hXint.add hYint).const_mul C
  have h12 : IntegrableOn
      (fun u => Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ)
        + (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB) I := hsbOn.add h2
  have hggOn : IntegrableOn gg I := by
    have hsum : IntegrableOn
        (fun u => (Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ)
          + (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB)
          + C * (μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB
            + μ * av * nB)) I := h12.add h3
    simpa only [gg] using hsum
  -- (3) the left-hand side is nonnegative
  have hffnn : 0 ≤ᵐ[MeasureTheory.volume.restrict I] ff := by
    filter_upwards with u
    refine mul_nonneg hc₁.le (mul_nonneg ?_ ?_)
    · exact Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓpos hdpos u
    · exact Work.BoseFixB1B.ipw_inner_nonneg (ℓ := ℓ) (d := dd) (M := MM) (n := n)
        (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hμ u
  -- (4) integrate the pointwise inequality over `I₋`
  have hptae : ff ≤ᵐ[MeasureTheory.volume.restrict I] gg :=
    (ae_restrict_iff' hImeas).2 (Filter.Eventually.of_forall fun u hu => hpt u hu)
  have hmono : ∫ u in I, ff u ≤ ∫ u in I, gg u :=
    integral_mono_of_nonneg hffnn hggOn hptae
  -- (5) identify the two integrals
  have hff_eq : ∫ u in I, ff u = c₁ * RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ) := by
    show ∫ u in I, c₁ * (Work.BoseFixB1.w1MassB h MM ℓ dd u * AA u) = _
    rw [integral_const_mul]
    rfl
  have hgg_eq : ∫ u in I, gg u =
      (∫ u in Work.SmallBoxSliding.interiorSet
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
              Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
        + (1 / 2) * μ ^ 2
            * (∫ u in Work.SmallBoxSliding.interiorSet
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.BoseFixB1.w1MassB h
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        + C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                      + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                  * (∫ u in Work.SmallBoxSliding.interiorSet
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                      Work.SmallBoxSliding.chiMass
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                + μ * (_root_.BoseGases.a v)
                  * (MeasureTheory.volume (Work.SmallBoxSliding.interiorSet
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have step1 : ∫ u in I, gg u
        = (∫ u in I, Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
          + (∫ u in I, (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB)
          + (∫ u in I, C * (μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB
              + μ * av * nB)) := by
      simp only [gg]
      rw [integral_add h12 h3, integral_add hsbOn h2]
    have e1 : ∫ u in I, (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB
        = ((1 / 2) * μ ^ 2 * (∫ u in I, Work.BoseFixB1.w1MassB h MM ℓ dd u)) * nB := by
      rw [integral_mul_const, integral_const_mul]
    have e2 : ∫ u in I, C * (μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB
          + μ * av * nB)
        = C * ((μ ^ 2 * av * G
              * (∫ u in I, Work.SmallBoxSliding.chiMass MM ℓ dd u)) * nB
            + MeasureTheory.Measure.real MeasureTheory.volume I * (μ * av * nB)) := by
      rw [integral_const_mul, integral_add hXint hYint, integral_mul_const,
        integral_const_mul, setIntegral_const, smul_eq_mul]
    calc ∫ u in I, gg u
        = (∫ u in I, Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
          + (∫ u in I, (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h MM ℓ dd u * nB)
          + (∫ u in I, C * (μ ^ 2 * av * G * Work.SmallBoxSliding.chiMass MM ℓ dd u * nB
              + μ * av * nB)) := step1
      _ = (∫ u in I, Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
          + (((1 / 2) * μ ^ 2 * (∫ u in I, Work.BoseFixB1.w1MassB h MM ℓ dd u)) * nB)
          + (C * ((μ ^ 2 * av * G
                * (∫ u in I, Work.SmallBoxSliding.chiMass MM ℓ dd u)) * nB
              + MeasureTheory.Measure.real MeasureTheory.volume I * (μ * av * nB))) := by
          rw [e1, e2]
      _ = (∫ u in Work.SmallBoxSliding.interiorSet
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
              Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
        + (1 / 2) * μ ^ 2
            * (∫ u in Work.SmallBoxSliding.interiorSet
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.BoseFixB1.w1MassB h
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        + C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                      + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                  * (∫ u in Work.SmallBoxSliding.interiorSet
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                      Work.SmallBoxSliding.chiMass
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                + μ * (_root_.BoseGases.a v)
                  * (MeasureTheory.volume (Work.SmallBoxSliding.interiorSet
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
          dsimp only [MeasureTheory.Measure.real, I, ℓ, dd, MM, av, KB, G, nB]
          ring_nf
  rw [← hff_eq, ← hgg_eq]
  exact hmono

/-! ## 2. The pure arithmetic of the constant collection -/

/-- **The constant collection.**  At FS's parameters, with `X := ∫_{I₋}χ_{B(u)}²`,
`Y := |I₋|`, `Γ := (R/(dℓ))² + K_B³t^{1/2}`, `κ := K_B³t^{1/2}` and
`t = μ(a v)³`:

    X ≤ ℓ³,   Γ ≤ 2κ,   Y ≤ 8μℓ³κ    ⟹
    C·(μ²(a v)Γ·X + μ(a v)·Y)·‖Φ‖² ≤ (10C)·μ²(a v)ℓ³κ·‖Φ‖² .

(The cube twin of the private helper `collect_coeff` of
`Submission/Work/BoseFixB1S/perBoxIntegratedUnif.lean`.) -/
private lemma collect_coeff_cube {C μ av ℓ G X Y kap nB : ℝ}
    (hC : 0 ≤ C) (hμ : 0 ≤ μ) (hav : 0 ≤ av) (hℓ : 0 ≤ ℓ) (hnB : 0 ≤ nB)
    (hG : 0 ≤ G) (hX : 0 ≤ X) (hkap : 0 ≤ kap)
    (hXle : X ≤ ℓ ^ 3) (hGle : G ≤ 2 * kap) (hYle : Y ≤ 8 * (μ * ℓ ^ 3 * kap)) :
    C * (μ ^ 2 * av * G * X + μ * av * Y) * nB
      ≤ (10 * C) * (μ ^ 2 * av * ℓ ^ 3 * kap) * nB := by
  have hGX : G * X ≤ (2 * kap) * ℓ ^ 3 := by
    calc G * X ≤ (2 * kap) * X := mul_le_mul_of_nonneg_right hGle hX
      _ ≤ (2 * kap) * ℓ ^ 3 := mul_le_mul_of_nonneg_left hXle (by linarith)
  have h1 : μ ^ 2 * av * G * X ≤ μ ^ 2 * av * (2 * kap) * ℓ ^ 3 := by
    have hpos : (0 : ℝ) ≤ μ ^ 2 * av := by positivity
    calc μ ^ 2 * av * G * X = μ ^ 2 * av * (G * X) := by ring
      _ ≤ μ ^ 2 * av * ((2 * kap) * ℓ ^ 3) := mul_le_mul_of_nonneg_left hGX hpos
      _ = μ ^ 2 * av * (2 * kap) * ℓ ^ 3 := by ring
  have h2 : μ * av * Y ≤ μ * av * (8 * (μ * ℓ ^ 3 * kap)) :=
    mul_le_mul_of_nonneg_left hYle (by positivity)
  have hkey : μ ^ 2 * av * (2 * kap) * ℓ ^ 3 + μ * av * (8 * (μ * ℓ ^ 3 * kap))
      = 10 * (μ ^ 2 * av * ℓ ^ 3 * kap) := by ring
  have h4 : μ ^ 2 * av * G * X + μ * av * Y ≤ 10 * (μ ^ 2 * av * ℓ ^ 3 * kap) := by
    linarith [h1, h2, hkey.le, hkey.ge]
  calc C * (μ ^ 2 * av * G * X + μ * av * Y) * nB
      ≤ C * (10 * (μ ^ 2 * av * ℓ ^ 3 * kap)) * nB :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hC) hnB
    _ = (10 * C) * (μ ^ 2 * av * ℓ ^ 3 * kap) * nB := by ring

/-! ## 3. The three factual inputs of the collection, at FS's parameters -/

/-- **`∫_{I₋} χ_{B(u)}² ≤ ℓ³`.**  The full `u`-mass of the `χ_{B(u)}²`-cutoff is
`∫_{ℝ³}χ_{B(u)}² du = ℓ³` (`Work.SmallBoxSliding.integral_chiMass_eq`), and the
integrand is nonnegative, so restricting to the interior can only lower it. -/
private lemma chiMass_interior_le_cube {M : ℕ} (hM : 1 ≤ M) {ℓ d μ : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) :
    (∫ u in interiorSet ℓ d μ, chiMass M ℓ d u) ≤ ℓ ^ 3 := by
  have hint : Integrable (fun u : EuclideanSpace ℝ (Fin 3) => chiMass M ℓ d u) volume :=
    (integrable_chiSmallB_mass hM hℓ hd).congr
      (Filter.Eventually.of_forall fun u => (chiMass_def M ℓ d u).symm)
  calc (∫ u in interiorSet ℓ d μ, chiMass M ℓ d u)
      ≤ ∫ u : EuclideanSpace ℝ (Fin 3), chiMass M ℓ d u :=
        setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun u => Work.SmallBoxSliding.chiMass_nonneg M ℓ d u)
    _ = ℓ ^ 3 := integral_chiMass_eq hM hℓ hd

/-- **`d^{-3} ≤ μℓ³K_B³(μa³)^{1/2}`** at FS's parameters (`μa³ = t ≤ 1`).  Both
sides are closed monomials in `t` (`Work.BoseFixB1.RegimeAux`): `d³ = t^{18/323}`
and `μℓ³K_B³t^{1/2} = t^{-45/646}`, and the exponent `-45/646 ≤ -18/323`. -/
private lemma inv_d_cube_le {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) (ht : μ * A ^ 3 ≤ 1) :
    ((paramsAt μ A).d ^ 3)⁻¹
      ≤ μ * sideAt μ A ^ 3 * (paramsAt μ A).KB ^ 3 * (μ * A ^ 3) ^ (1 / 2 : ℝ) := by
  have ht0 : 0 < μ * A ^ 3 := mul_pos hμ (pow_pos hA 3)
  rw [Work.BoseFixB1.d_cube_eq hA hμ, Work.BoseFixB1.mu_ell_cube_KB3_half_eq hA hμ,
    Work.BoseBox.fsXp_inv ht0]
  exact Work.BoseBox.fsXp_le_fsXp ht0 ht (by norm_num)

/-- **The volume of the interior.**  `I₋ ⊆ acube ((1+d)/d)` — the constraint
`|((ℓd)•u)_j| ≤ ½ℓ(1+d)` is `|u_j| ≤ (1+d)/(2d)` — and
`|acube L| = L³ ≤ 8d^{-3}` for `0 < d ≤ 1`. -/
private lemma volume_interiorSet_le_cube {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hμ : 0 < μ) :
    volume (interiorSet ℓ d μ) ≤ ENNReal.ofReal (8 * (d ^ 3)⁻¹) := by
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd0
  have hsub : interiorSet ℓ d μ ⊆ Submission.BoseGases.acube ((1 + d) / d) := by
    intro u hu
    rw [mem_interiorSet_iff] at hu
    rw [Submission.BoseGases.mem_acube_iff]
    intro j
    have hb : (ℓ * d) * |u.ofLp j| ≤ (1 / 2) * ℓ * (1 + d) := by
      have h := hu j
      have h2μ : 0 ≤ 2 * μ ^ (-(1 / 3) : ℝ) :=
        (mul_pos two_pos (Real.rpow_pos_of_pos hμ _)).le
      rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hℓd] at h
      linarith
    have huj : |u.ofLp j| ≤ ((1 + d) / d) / 2 := by
      have h1 : |u.ofLp j| ≤ (ℓ * (1 + d) / 2) / (ℓ * d) := by
        rw [le_div_iff₀ hℓd]
        nlinarith [hb]
      have h2 : (ℓ * (1 + d) / 2) / (ℓ * d) = ((1 + d) / d) / 2 := by
        field_simp
      linarith [h1, h2.le, h2.ge]
    have hmem := abs_le.mp huj
    exact ⟨by linarith [hmem.1], hmem.2⟩
  calc volume (interiorSet ℓ d μ)
      ≤ volume (Submission.BoseGases.acube ((1 + d) / d)) := measure_mono hsub
    _ = ENNReal.ofReal (((1 + d) / d) ^ 3) :=
        Submission.BoseGases.acube_volume _ (by positivity)
    _ ≤ ENNReal.ofReal (8 * (d ^ 3)⁻¹) := by
        apply ENNReal.ofReal_le_ofReal
        have hd3 : 0 < d ^ 3 := by positivity
        have h2 : (1 + d) ^ 3 ≤ 8 := by
          have h1 : 1 + d ≤ 2 := by linarith
          have h0 : 0 ≤ 1 + d := by linarith
          calc (1 + d) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ h0 h1 3
            _ = 8 := by norm_num
        rw [div_pow, div_le_iff₀ hd3]
        calc (1 + d) ^ 3 ≤ 8 := h2
          _ = 8 * (d ^ 3)⁻¹ * d ^ 3 := by
              rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hd3), mul_one]

/-! ## 4. The target: constant collection -/

theorem perBoxIntegratedUnifCube {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hperI : ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          ∀ (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u)
    (hsbInt : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ {n : ℕ}
      (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
      MeasureTheory.IntegrableOn
        (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
        (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ c₁ ≤ 1 ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
            c₁ * Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ)
              ≤ (∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                    Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
                + (1 / 2) * μ ^ 2
                    * (∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                        Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                + C * (μ ^ 2 * (_root_.BoseGases.a v)
                          * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  -- the integrated per-box bound, with the *uncollected* FS error terms
  obtain ⟨ε₁, c₁, C₁, hε₁, hc₁, hC₁, hcore⟩ :=
    integratedPerBoxUnifCube (v := v) h hv hv1 hvrad hR hv_supp hav
      hperI
      hsbInt
      (Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp)
  -- the diluteness threshold of `(R/(dℓ))² ≤ K_B³(μa³)^{1/2}` (FS `eq:appRassumption`)
  have hTpos : 0 < ((_root_.BoseGases.a v) ^ 2 / R ^ 2) ^ (646 / 341 : ℝ) :=
    Real.rpow_pos_of_pos (by positivity) _
  refine ⟨min ε₁ (min 1 (((_root_.BoseGases.a v) ^ 2 / R ^ 2) ^ (646 / 341 : ℝ))),
    min c₁ 1, 10 * C₁, lt_min hε₁ (lt_min one_pos hTpos), lt_min hc₁ one_pos,
    min_le_right _ _, by linarith, ?_⟩
  intro μ hAdm n Φ
  -- ## the ambient data
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hdil : μ * (_root_.BoseGases.a v) ^ 3
      ≤ min ε₁ (min 1 (((_root_.BoseGases.a v) ^ 2 / R ^ 2) ^ (646 / 341 : ℝ))) :=
    Work.BoseFixB1.adm_dilute hAdm
  have ht_one : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 :=
    le_trans hdil (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht_T : μ * (_root_.BoseGases.a v) ^ 3
      ≤ ((_root_.BoseGases.a v) ^ 2 / R ^ 2) ^ (646 / 341 : ℝ) :=
    le_trans hdil (le_trans (min_le_right _ _) (min_le_right _ _))
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hd1 : (paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 :=
    Work.BoseBox.fsXp_le_one (mul_pos hμ (pow_pos hav 3)) ht_one (by norm_num)
  have hKB : 0 < (paramsAt μ (_root_.BoseGases.a v)).KB := Work.BoseFixB1.paramsAt_KB_pos hAdm
  have hM1 : 1 ≤ (paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hκ : 0 ≤ (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
    mul_nonneg (pow_nonneg hKB.le 3)
      (Real.rpow_nonneg (mul_nonneg hμ.le (pow_nonneg hav.le 3)) _)
  -- ## the three collection facts
  have hGle : (R / (sideAt μ (_root_.BoseGases.a v)
        * (paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
      + (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)
      ≤ 2 * ((paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    have hRsb := Work.BoseFixB1B.RsbSide_sq_le_holds (A := _root_.BoseGases.a v) (R := R)
      (μ := μ) hav hR hμ ht_T
    have heq : (R / (sideAt μ (_root_.BoseGases.a v)
          * (paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
        = (R / ((paramsAt μ (_root_.BoseGases.a v)).d * sideAt μ (_root_.BoseGases.a v))) ^ 2 := by
      ring_nf
    rw [heq]
    linarith
  have hXle : (∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
          (paramsAt μ (_root_.BoseGases.a v)).d μ,
        chiMass (paramsAt μ (_root_.BoseGases.a v)).M (sideAt μ (_root_.BoseGases.a v))
          (paramsAt μ (_root_.BoseGases.a v)).d u)
      ≤ (sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
    chiMass_interior_le_cube hM1 hℓ hd
  have hYle : (volume (interiorSet (sideAt μ (_root_.BoseGases.a v))
          (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal
      ≤ 8 * (μ * (sideAt μ (_root_.BoseGases.a v)) ^ 3
          * ((paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))) := by
    have h1 : (volume (interiorSet (sideAt μ (_root_.BoseGases.a v))
            (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal
        ≤ 8 * ((paramsAt μ (_root_.BoseGases.a v)).d ^ 3)⁻¹ := by
      have hvol := volume_interiorSet_le_cube hℓ hd hd1 hμ
      calc (volume (interiorSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal
          ≤ (ENNReal.ofReal (8 * ((paramsAt μ (_root_.BoseGases.a v)).d ^ 3)⁻¹)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
        _ = 8 * ((paramsAt μ (_root_.BoseGases.a v)).d ^ 3)⁻¹ :=
            ENNReal.toReal_ofReal (by positivity)
    have h2 : 8 * ((paramsAt μ (_root_.BoseGases.a v)).d ^ 3)⁻¹
        ≤ 8 * (μ * (sideAt μ (_root_.BoseGases.a v)) ^ 3
            * ((paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))) := by
      have hinv := inv_d_cube_le (A := _root_.BoseGases.a v) (μ := μ) hav hμ ht_one
      linarith [hinv]
    linarith [h1, h2]
  -- ## the nonnegativity of the two integrals
  have hXnn : 0 ≤ ∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
          (paramsAt μ (_root_.BoseGases.a v)).d μ,
        chiMass (paramsAt μ (_root_.BoseGases.a v)).M (sideAt μ (_root_.BoseGases.a v))
          (paramsAt μ (_root_.BoseGases.a v)).d u :=
    setIntegral_nonneg
      (Work.SmallBoxSliding.measurableSet_interiorSet
        (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ)
      (fun u _ => Work.SmallBoxSliding.chiMass_nonneg _ _ _ _)
  have hGnn : 0 ≤ (R / (sideAt μ (_root_.BoseGases.a v)
        * (paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
      + (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
    add_nonneg (sq_nonneg _) hκ
  have hnb : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.normB_nonneg _
  have hRnn : 0 ≤ Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ) :=
    Work.BoseFixB1.rPsiB_nonneg (v := v) (h := h) (μ := μ)
      (M := (paramsAt μ (_root_.BoseGases.a v)).M) (c := 1) (ℓ := sideAt μ (_root_.BoseGases.a v))
      (d := (paramsAt μ (_root_.BoseGases.a v)).d) (n := n) hv hv1 hvrad hR hv_supp
      hμ hM1 (by norm_num) hℓ hd (Φ : Submission.BoseGases.X n → ℝ)
  -- ## the coefficient inequality and the assembly
  have hcoef := collect_coeff_cube (C := C₁) (μ := μ) (av := _root_.BoseGases.a v)
    (ℓ := sideAt μ (_root_.BoseGases.a v))
    (G := (R / (sideAt μ (_root_.BoseGases.a v)
            * (paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
          + (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
    (X := ∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
            (paramsAt μ (_root_.BoseGases.a v)).d μ,
          chiMass (paramsAt μ (_root_.BoseGases.a v)).M (sideAt μ (_root_.BoseGases.a v))
            (paramsAt μ (_root_.BoseGases.a v)).d u)
    (Y := (volume (interiorSet (sideAt μ (_root_.BoseGases.a v))
            (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
    (kap := (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
    (nB := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
    hC₁ hμ.le hav.le hℓ.le hnb hGnn hXnn hκ hXle hGle hYle
  have hstep := hcore μ hAdm₁ n Φ
  calc (min c₁ 1) * Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ)
      ≤ c₁ * Work.BoseFixB1.RPsi v h μ (Φ : Submission.BoseGases.X n → ℝ) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hRnn
    _ ≤ (∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ,
              Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
          + (1 / 2) * μ ^ 2
              * (∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
                  (paramsAt μ (_root_.BoseGases.a v)).d μ,
                  Work.BoseFixB1.w1MassB h (paramsAt μ (_root_.BoseGases.a v)).M
                    (sideAt μ (_root_.BoseGases.a v))
                    (paramsAt μ (_root_.BoseGases.a v)).d u)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          + C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
                    * ((R / (sideAt μ (_root_.BoseGases.a v)
                              * (paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                        + (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                    * (∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
                        (paramsAt μ (_root_.BoseGases.a v)).d μ,
                        chiMass (paramsAt μ (_root_.BoseGases.a v)).M
                          (sideAt μ (_root_.BoseGases.a v))
                          (paramsAt μ (_root_.BoseGases.a v)).d u)
                  + μ * (_root_.BoseGases.a v)
                    * (volume (interiorSet (sideAt μ (_root_.BoseGases.a v))
                        (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := hstep
    _ ≤ (∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ,
              Work.BoseFixB1B.sbWordCube v h μ u (Φ : Submission.BoseGases.X n → ℝ))
          + (1 / 2) * μ ^ 2
              * (∫ u in interiorSet (sideAt μ (_root_.BoseGases.a v))
                  (paramsAt μ (_root_.BoseGases.a v)).d μ,
                  Work.BoseFixB1.w1MassB h (paramsAt μ (_root_.BoseGases.a v)).M
                    (sideAt μ (_root_.BoseGases.a v))
                    (paramsAt μ (_root_.BoseGases.a v)).d u)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          + (10 * C₁) * (μ ^ 2 * (_root_.BoseGases.a v)
                    * sideAt μ (_root_.BoseGases.a v) ^ 3
                    * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                    * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
        linarith [hcoef]

end Work.BoseFixB1S
