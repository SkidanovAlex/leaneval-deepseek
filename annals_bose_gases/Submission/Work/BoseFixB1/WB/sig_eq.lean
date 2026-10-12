import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.WB.boxState_sq_bound
import Submission.Work.BoseFixB1.WB.chiSmallB_sq_le
import Submission.Work.BoseFixB1.WB.dilute_pos_of_sideAt_pos
import Submission.Work.BoseFixB1.WB.integral_abox_eq_zero_of_nonpos
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.sig_eq` — the `U`-identity of FS's step 4

`wbSig v h μ n Φ = ∫_{I₋} wbMass(u)·dens_Φ(u) du` is the state-averaged local density
against the localised one-body mass.  The identity proved here rewrites it as the
`Σᵢ U(xᵢ)`-expectation:

    `wbSig v h μ n Φ = (∫ x, Φ x² · Σᵢ wbU(xᵢ)) / ‖Φ‖²`,

with `wbU(z) = ∫_{I₋} (wbMass(u)/chiMass(u))·χ_{B(u)}(z)² du`.  The proof is the exchange
of the `u`- and box-`x`-integrals (Fubini; the `L¹` input comes from the mass hypotheses
`hmassU`/`hmassL` — which bound `wbMass/chiMass` uniformly — the uniform cutoff bound, and
the finiteness of the box and of `I₋`), the interchange of the finite particle sum with the
`u`-integral, and unfolding `wbU`.  In the degenerate case `ℓ = sideAt μ (a v) ≤ 0` the box
`abox n ℓ` is a null set (or the sums are empty) and both sides vanish.

## Auxiliary facts proved here

* `interiorSet_volume_lt_top` — `volume (interiorSet ℓ d μ) < ⊤` for `ℓ, d > 0`
  (the interior set is bounded);
* `continuous_chiSmallB_pair` — joint continuity of `χ_{B(u)}(z)` in `(u,z)`;
* `aesm_uncurry_wSmall1Pair`, `aestronglyMeasurable_wbMass` — strong measurability of the
  localised one-body kernel and of `u ↦ wbMass v h μ u`, which are the measurability inputs
  of the Fubini step (the kernel is `a.e.` measurable in the relative coordinate `x - y`,
  and the parametric integral of an a.e. strongly measurable function is a.e. strongly
  measurable).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WB

open Work.BoseBoxFix Work.BoseBox Work.SmallBoxSliding Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)


/-! ## The interior set has finite volume -/

open MeasureTheory in
theorem interiorSet_volume_lt_top {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
      (Work.SmallBoxSliding.interiorSet ℓ d μ) < ⊤ := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  -- the outer coordinate bound and the resulting box radius
  set C : ℝ := (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) with hCdef
  set R : ℝ := max C 0 / (ℓ * d) with hRdef
  have hRnn : 0 ≤ R := by
    rw [hRdef]
    exact div_nonneg (le_max_right _ _) hld.le
  -- `I₋` is contained in the centred cube `acube (2R)`
  have hsub : Work.SmallBoxSliding.interiorSet ℓ d μ ⊆ Submission.BoseGases.acube (2 * R) := by
    intro u hu
    rw [Work.SmallBoxSliding.mem_interiorSet_iff] at hu
    rw [Submission.BoseGases.mem_acube_iff]
    intro j
    -- coordinate bound: `(ℓd)·|u_j| ≤ C`
    have h1 : (ℓ * d) * |u.ofLp j| ≤ C := by
      have h := hu j
      rw [hCdef]
      simpa [abs_of_pos hℓ, abs_of_pos hd] using h
    -- hence `|u_j| ≤ R`
    have h2 : |u.ofLp j| ≤ R := by
      rw [hRdef, le_div_iff₀ hld]
      calc |u.ofLp j| * (ℓ * d) = (ℓ * d) * |u.ofLp j| := by ring
        _ ≤ C := h1
        _ ≤ max C 0 := le_max_left _ _
    have h3 := abs_le.mp h2
    simp only [Set.mem_Icc]
    constructor <;> linarith [h3.1, h3.2]
  exact lt_of_le_of_lt (MeasureTheory.measure_mono hsub)
    (Submission.BoseGases.acube_lt_top (2 * R) (by linarith))



/-! ## The ratio bound -/

/-- If `0 ≤ m` and `m ≤ c * g` then `|m / g| ≤ |c|` (the division convention makes the
case `g = 0` trivial). -/
lemma div_abs_le_of_le_mul {m c g : ℝ} (hL : 0 ≤ m) (hU : m ≤ c * g) : |m / g| ≤ |c| := by
  rcases lt_trichotomy g 0 with hg | hg | hg
  · have h1 : m / g ≤ 0 := div_nonpos_of_nonneg_of_nonpos hL hg.le
    have h2 : c ≤ m / g := by
      rw [le_div_iff_of_neg hg]
      exact hU
    rw [abs_of_nonpos h1, abs_of_nonpos (h2.trans h1)]
    linarith
  · rw [hg, div_zero, abs_zero]
    exact abs_nonneg c
  · have h1 : 0 ≤ m / g := div_nonneg hL hg.le
    have h2 : m / g ≤ c := by
      rw [div_le_iff₀ hg]
      exact hU
    rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact h2

/-- The pointwise algebra of the `wbMass`/`wbDens` product. -/
private lemma mul_div_eq_inv_mul (m a N c : ℝ) : m * (a / (N * c)) = N⁻¹ * ((m / c) * a) := by
  by_cases hN : N = 0
  · simp [hN]
  · by_cases hc : c = 0
    · simp [hc]
    · field_simp


/-! ## Measurability of the localised kernel and of `wbMass` -/

/-- Joint continuity of `χ_{B(u)}(z)` in `(u,z)`. -/
lemma continuous_chiSmallB_pair (M : ℕ) (ℓ d : ℝ) :
    Continuous (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d p.1 p.2) := by
  have hsm : Continuous (fun z : E3 => Submission.BoseGases.chiSmall M z) :=
    Work.SmallBoxSliding.chiSmall_continuous_all M
  have hsc : Continuous (fun p : E3 × E3 => Submission.BoseGases.chiScale ℓ p.2) :=
    (Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd
  have h2 : Continuous (fun p : E3 × E3 =>
      Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
    hsm.comp (((continuous_snd).const_smul ((ℓ * d)⁻¹)).sub continuous_fst)
  have heq : (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d p.1 p.2)
      = fun p : E3 × E3 => Submission.BoseGases.chiScale ℓ p.2 *
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1) := rfl
  rw [heq]
  exact hsc.mul h2

/-- A.e. strong measurability of the uncurried localised one-body kernel. -/
lemma aesm_uncurry_wSmall1Pair {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ}
    (hM : 1 ≤ M) (ℓ d : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : (E3 × E3) × E3 => Submission.BoseGases.wSmall1Pair h M ℓ d p.1.1 p.1.2 p.2)
      (((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3)).prod
        (MeasureTheory.volume : Measure E3)) := by
  have hg0 : MeasureTheory.AEStronglyMeasurable (Submission.BoseGases.g0 v h)
      (MeasureTheory.volume : Measure E3) :=
    (Classical.choose_spec h).2.rhs_integrable.aestronglyMeasurable
  -- the relative coordinate `((u,x),y) ↦ x - y` is quasi-measure-preserving
  have hproj : Measure.QuasiMeasurePreserving (fun p : (E3 × E3) × E3 => (p.1.2, p.2))
      (((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3)).prod
        (MeasureTheory.volume : Measure E3))
      ((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3)) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      (Measure.quasiMeasurePreserving_snd (μ := (MeasureTheory.volume : Measure E3))
        (ν := (MeasureTheory.volume : Measure E3)))
      (Measure.QuasiMeasurePreserving.id (MeasureTheory.volume : Measure E3))
  have hqmp : Measure.QuasiMeasurePreserving (fun p : (E3 × E3) × E3 => p.1.2 - p.2)
      (((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3)).prod
        (MeasureTheory.volume : Measure E3))
      (MeasureTheory.volume : Measure E3) :=
    (MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant
      (μ := (MeasureTheory.volume : Measure E3)) (ν := (MeasureTheory.volume : Measure E3))).comp hproj
  have hgsub : MeasureTheory.AEStronglyMeasurable
      (fun p : (E3 × E3) × E3 => Submission.BoseGases.g0 v h (p.1.2 - p.2))
      (((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3)).prod
        (MeasureTheory.volume : Measure E3)) :=
    hg0.comp_quasiMeasurePreserving hqmp
  -- the denominator `(χ_M ⋆ χ_M)((x-y)/(ℓd))·(χ⋆χ)((x-y)/ℓ)`
  have hden : MeasureTheory.AEStronglyMeasurable
      (fun p : (E3 × E3) × E3 => Submission.BoseGases.convScaleSmall M (ℓ * d) (p.1.2 - p.2)
        * Submission.BoseGases.convScale ℓ (p.1.2 - p.2))
      (((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3)).prod
        (MeasureTheory.volume : Measure E3)) :=
    (((Submission.BoseGases.conv3Small_continuous hM).comp
        ((by fun_prop : Continuous (fun p : (E3 × E3) × E3 => p.1.2 - p.2)).const_smul ((ℓ * d)⁻¹))).aestronglyMeasurable.mul
      (((Submission.BoseGases.convScale_continuous ℓ).comp
        (by fun_prop : Continuous (fun p : (E3 × E3) × E3 => p.1.2 - p.2)))).aestronglyMeasurable)
  have hmain : MeasureTheory.AEStronglyMeasurable
      (fun p : (E3 × E3) × E3 =>
        Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (p.1.2 - p.2)
          / Submission.BoseGases.convScale ℓ (p.1.2 - p.2))
      (((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3)).prod
        (MeasureTheory.volume : Measure E3)) :=
    (hgsub.div₀ (((Submission.BoseGases.conv3Small_continuous hM).comp
        ((by fun_prop : Continuous (fun p : (E3 × E3) × E3 => p.1.2 - p.2)).const_smul ((ℓ * d)⁻¹))).aestronglyMeasurable)).div₀
      (((Submission.BoseGases.convScale_continuous ℓ).comp
        (by fun_prop : Continuous (fun p : (E3 × E3) × E3 => p.1.2 - p.2)))).aestronglyMeasurable
  have hchi1 : MeasureTheory.AEStronglyMeasurable
      (fun p : (E3 × E3) × E3 => Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.1.2)
      (((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3)).prod
        (MeasureTheory.volume : Measure E3)) :=
    ((continuous_chiSmallB_pair M ℓ d).comp continuous_fst).aestronglyMeasurable
  have hchi2 : MeasureTheory.AEStronglyMeasurable
      (fun p : (E3 × E3) × E3 => Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.2)
      (((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3)).prod
        (MeasureTheory.volume : Measure E3)) := by
    have huy : Continuous (fun p : (E3 × E3) × E3 => (p.1.1, p.2)) := by fun_prop
    exact ((continuous_chiSmallB_pair M ℓ d).comp huy).aestronglyMeasurable
  have hfull : MeasureTheory.AEStronglyMeasurable
      (fun p : (E3 × E3) × E3 =>
        Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.1.2
          * (Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (p.1.2 - p.2)
              / Submission.BoseGases.convScale ℓ (p.1.2 - p.2))
          * Submission.BoseGases.chiSmallB M ℓ d p.1.1 p.2)
      (((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3)).prod
        (MeasureTheory.volume : Measure E3)) :=
    (hchi1.mul hmain).mul hchi2
  refine hfull.congr ?_
  filter_upwards with p
  simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
    Submission.BoseGases.wSmallScaled]

/-- **A.e. strong measurability of `wbMass v h μ`** (the backup for the delegated lemma). -/
theorem aestronglyMeasurable_wbMass_aux {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} :
    MeasureTheory.AEStronglyMeasurable (fun u : E3 => Work.BoseFixB1.wbMass v h μ u)
      (MeasureTheory.volume : Measure E3) := by
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseBox.paramsAt]
    simp [Work.BoseBox.fsParams, Work.BoseBox.mValue]
  have hstep1 : MeasureTheory.AEStronglyMeasurable
      (fun q : E3 × E3 => ∫ y : E3, Submission.BoseGases.wSmall1Pair h
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d q.1 q.2 y)
      ((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3)) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (f := fun p : (E3 × E3) × E3 => Submission.BoseGases.wSmall1Pair h
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d p.1.1 p.1.2 p.2)
      (aesm_uncurry_wSmall1Pair hM1 _ _)
  have hstep2 : MeasureTheory.AEStronglyMeasurable
      (fun u : E3 => ∫ x : E3, ∫ y : E3, Submission.BoseGases.wSmall1Pair h
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x y)
      (MeasureTheory.volume : Measure E3) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (f := fun q : E3 × E3 => ∫ y : E3, Submission.BoseGases.wSmall1Pair h
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d q.1 q.2 y)
      hstep1
  simpa only [Work.BoseFixB1.wbMass, Work.BoseFixB1.w1MassB] using hstep2



/-! ## The main theorem -/

theorem sig_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} {C : ℝ}
    (hmassU : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.wbMass v h μ u ≤ C * _root_.BoseGases.a v *
      Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (hmassL : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseFixB1.wbMass v h μ u)
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    Work.BoseFixB1.wbSig v h μ n (Φ : Submission.BoseGases.X n → ℝ)
      = (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Φ x) ^ 2 * (∑ i : Fin n, Work.BoseFixB1.wbU v h μ (x i)))
          / Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  simp only [Work.BoseFixB1.wbSig, Work.BoseFixB1.wbDens]
  obtain ⟨P, hP0, hP⟩ := boxState_sq_bound Φ
  obtain ⟨toFun, hcd, hsym, hne⟩ := Φ
  set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓ_def
  set M : ℕ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M with hM_def
  set d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hd_def
  set I : Set E3 := Work.SmallBoxSliding.interiorSet ℓ d μ with hI_def
  dsimp only [Work.BoseKinLoc.BoxState.toFun] at *
  have hU : ∀ z : E3, Work.BoseFixB1.wbU v h μ z
      = ∫ u in I, (Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
          * (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2 := by
    intro z
    rw [Work.BoseFixB1.wbU, ← hℓ_def, ← hM_def, ← hd_def, hI_def.symm]
  by_cases hℓ0 : ℓ ≤ 0
  · -- degenerate case: the box is a null set (or the sums are empty)
    have hA : ∀ u : E3, (∫ x in Submission.BoseGases.abox n ℓ,
        toFun x ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x) = 0 := by
      intro u
      cases n with
      | zero =>
        have : (fun x : Submission.BoseGases.X 0 =>
            toFun x ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x) = fun _ => (0 : ℝ) := by
          funext x
          simp [Work.BoseFixB1.nCountB]
        rw [this, MeasureTheory.integral_zero]
      | succ k => exact integral_abox_eq_zero_of_nonpos (Nat.succ_pos k) hℓ0 _
    have hB : (∫ x in Submission.BoseGases.abox n ℓ,
        toFun x ^ 2 * (∑ i : Fin n, Work.BoseFixB1.wbU v h μ (x i))) = 0 := by
      cases n with
      | zero => simp
      | succ k => exact integral_abox_eq_zero_of_nonpos (Nat.succ_pos k) hℓ0 _
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => by
          rw [hA u, zero_div, mul_zero])),
      MeasureTheory.integral_zero, hB, zero_div]
  · push_neg at hℓ0
    have hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
      rw [← hℓ_def]; exact hℓ0
    have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := dilute_pos_of_sideAt_pos hside
    have hd : 0 < d := by
      rw [hd_def]
      exact Work.BoseBox.fsXp_pos ht
    have hM : 1 ≤ M := by
      rw [hM_def]
      simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
    -- the uniform bound on the cutoff
    have hK2nn : 0 ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
        * (1 / 2) ^ M) ^ 2 := sq_nonneg _
    have hchi : ∀ u z : E3, (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2
        ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
            * (1 / 2) ^ M) ^ 2 := fun u z => chiSmallB_sq_le hM ℓ d u z
    have hIlt : (MeasureTheory.volume : Measure E3) I < ⊤ := by
      rw [hI_def]
      exact interiorSet_volume_lt_top hℓ0 hd
    have hBlt : (MeasureTheory.volume : Measure (Submission.BoseGases.X n))
        (Submission.BoseGases.abox n ℓ) < ⊤ :=
      Submission.BoseGases.abox_lt_top n ℓ hℓ0.le
    haveI : IsFiniteMeasure ((MeasureTheory.volume : Measure E3).restrict I) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hIlt⟩
    haveI : IsFiniteMeasure ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hBlt⟩
    have hratio : ∀ u : E3, |Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u|
        ≤ |C * _root_.BoseGases.a v| := fun u => div_abs_le_of_le_mul (hmassL u) (hmassU u)
    have hgmeas : MeasureTheory.AEStronglyMeasurable
        (fun u : E3 => Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
        ((MeasureTheory.volume : Measure E3).restrict I) := by
      have h1 : MeasureTheory.AEStronglyMeasurable (fun u : E3 => Work.BoseFixB1.wbMass v h μ u)
          (MeasureTheory.volume : Measure E3) := aestronglyMeasurable_wbMass_aux
      have h2 : MeasureTheory.AEStronglyMeasurable
          (fun u : E3 => Work.SmallBoxSliding.chiMass M ℓ d u)
          (MeasureTheory.volume : Measure E3) :=
        Submission.BoseGases.chiSmallB_partial_integral_aestronglyMeasurable (M := M) hM hℓ0 hd
      exact (h1.div₀ h2).mono_measure Measure.restrict_le_self
    -- continuity of the one-dimensional slices of the cutoff
    have hchiCont : ∀ (x : Submission.BoseGases.X n) (i : Fin n),
        Continuous (fun u : E3 => Submission.BoseGases.chiSmallB M ℓ d u (x i)) := by
      intro x i
      exact (Work.SmallBoxSliding.chiSmallB_continuous_joint M ℓ d i).comp
        (continuous_id.prodMk continuous_const)
    -- integrability of the `u`-summands
    have hint : ∀ (x : Submission.BoseGases.X n) (i : Fin n),
        MeasureTheory.Integrable (fun u : E3 =>
          (Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
            * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
          ((MeasureTheory.volume : Measure E3).restrict I) := by
      intro x i
      refine MeasureTheory.Integrable.of_bound ?_ (|C * _root_.BoseGases.a v|
        * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M * (1 / 2) ^ M) ^ 2) ?_
      · exact hgmeas.mul (((hchiCont x i).aestronglyMeasurable).pow 2)
      · filter_upwards with u
        have h1 := hratio u
        have h2 : (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2
            ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                * (1 / 2) ^ M) ^ 2 := hchi u (x i)
        have h3 : 0 ≤ (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := sq_nonneg _
        calc ‖(Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
              * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2‖
            = |Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u|
              * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2 := by
                rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h3]
          _ ≤ |C * _root_.BoseGases.a v|
              * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                  * (1 / 2) ^ M) ^ 2 := mul_le_mul h1 h2 h3 (abs_nonneg _)
    -- the joint integrand
    have hFmeas : MeasureTheory.AEStronglyMeasurable
        (fun p : E3 × Submission.BoseGases.X n =>
          (Work.BoseFixB1.wbMass v h μ p.1 / Work.SmallBoxSliding.chiMass M ℓ d p.1)
            * ((toFun p.2) ^ 2 * Work.BoseFixB1.nCountB M ℓ d p.1 p.2))
        (((MeasureTheory.volume : Measure E3).restrict I).prod
          ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))) := by
      have h1 : MeasureTheory.AEStronglyMeasurable
          (fun p : E3 × Submission.BoseGases.X n =>
            Work.BoseFixB1.wbMass v h μ p.1 / Work.SmallBoxSliding.chiMass M ℓ d p.1)
          (((MeasureTheory.volume : Measure E3).restrict I).prod
            ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ))) :=
        hgmeas.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_fst
            (μ := (MeasureTheory.volume : Measure E3).restrict I)
            (ν := (MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ)))
      have h2 : MeasureTheory.AEStronglyMeasurable
          (fun p : E3 × Submission.BoseGases.X n => (toFun p.2) ^ 2)
          (((MeasureTheory.volume : Measure E3).restrict I).prod
            ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ))) :=
        (((hcd.continuous).comp continuous_snd).pow 2).aestronglyMeasurable
      have h3 : MeasureTheory.AEStronglyMeasurable
          (fun p : E3 × Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d p.1 p.2)
          (((MeasureTheory.volume : Measure E3).restrict I).prod
            ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ))) := by
        have hcont : Continuous (fun p : E3 × Submission.BoseGases.X n =>
            Work.BoseFixB1.nCountB M ℓ d p.1 p.2) := by
          simp only [Work.BoseFixB1.nCountB]
          exact continuous_finset_sum Finset.univ
            (fun i _ => (Work.SmallBoxSliding.chiSmallB_continuous_joint M ℓ d i).pow 2)
        exact hcont.aestronglyMeasurable
      exact h1.mul (h2.mul h3)
    have hFint : MeasureTheory.Integrable
        (fun p : E3 × Submission.BoseGases.X n =>
          (Work.BoseFixB1.wbMass v h μ p.1 / Work.SmallBoxSliding.chiMass M ℓ d p.1)
            * ((toFun p.2) ^ 2 * Work.BoseFixB1.nCountB M ℓ d p.1 p.2))
        (((MeasureTheory.volume : Measure E3).restrict I).prod
          ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))) := by
      refine MeasureTheory.Integrable.of_bound hFmeas
        (|C * _root_.BoseGases.a v| * P * ((n : ℝ)
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
              * (1 / 2) ^ M) ^ 2)) ?_
      have hbox : ∀ᵐ p ∂(((MeasureTheory.volume : Measure E3).restrict I).prod
          ((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))), p.2 ∈ Submission.BoseGases.abox n ℓ := by
        refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
          (s := {p : E3 × Submission.BoseGases.X n | p.2 ∈ Submission.BoseGases.abox n ℓ})
          ((Submission.BoseGases.abox_measurable n ℓ).preimage measurable_snd)).mpr
          (Filter.Eventually.of_forall (fun _ =>
            MeasureTheory.ae_restrict_of_forall_mem (Submission.BoseGases.abox_measurable n ℓ)
              (fun x hx => hx)))
      filter_upwards [hbox] with p hp
      have h1 := hratio p.1
      have h2 : (toFun p.2) ^ 2 ≤ P := hP p.2 hp
      have h2' : 0 ≤ (toFun p.2) ^ 2 := sq_nonneg _
      have h3 : Work.BoseFixB1.nCountB M ℓ d p.1 p.2
          ≤ (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
              * (1 / 2) ^ M) ^ 2 := by
        simp only [Work.BoseFixB1.nCountB]
        calc ∑ i : Fin n, (Submission.BoseGases.chiSmallB M ℓ d p.1 (p.2 i)) ^ 2
            ≤ ∑ _i : Fin n, (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                * (1 / 2) ^ M) ^ 2 :=
              Finset.sum_le_sum (fun i _ => hchi p.1 (p.2 i))
          _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                * (1 / 2) ^ M) ^ 2 := by
              simp [Finset.card_univ, nsmul_eq_mul]
      have h3' : 0 ≤ Work.BoseFixB1.nCountB M ℓ d p.1 p.2 := by
        simp only [Work.BoseFixB1.nCountB]
        exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
      calc ‖(Work.BoseFixB1.wbMass v h μ p.1 / Work.SmallBoxSliding.chiMass M ℓ d p.1)
              * ((toFun p.2) ^ 2 * Work.BoseFixB1.nCountB M ℓ d p.1 p.2)‖
          = |Work.BoseFixB1.wbMass v h μ p.1 / Work.SmallBoxSliding.chiMass M ℓ d p.1|
              * ((toFun p.2) ^ 2 * Work.BoseFixB1.nCountB M ℓ d p.1 p.2) := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg h2' h3')]
        _ ≤ |C * _root_.BoseGases.a v| * (P * ((n : ℝ)
              * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                  * (1 / 2) ^ M) ^ 2)) :=
              mul_le_mul h1 (mul_le_mul h2 h3 h3' hP0) (mul_nonneg h2' h3') (abs_nonneg _)
        _ = |C * _root_.BoseGases.a v| * P * ((n : ℝ)
              * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
                  * (1 / 2) ^ M) ^ 2) := by ring
    -- Fubini
    have hFubini : (∫ u in I, ∫ x in Submission.BoseGases.abox n ℓ,
          (Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
            * ((toFun x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x))
        = ∫ x in Submission.BoseGases.abox n ℓ, ∫ u in I,
          (Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
            * ((toFun x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x) :=
      MeasureTheory.integral_integral_swap
        (μ := (MeasureTheory.volume : Measure E3).restrict I)
        (ν := (MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))
        (f := fun u x => (Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
            * ((toFun x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x))
        hFint
    -- the pointwise-in-`x` identity
    have hpt : ∀ x : Submission.BoseGases.X n,
        (∫ u in I, (Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
            * ((toFun x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x))
          = (toFun x) ^ 2 * (∑ i : Fin n, Work.BoseFixB1.wbU v h μ (x i)) := by
      intro x
      simp only [hU]
      have hcongr : (∫ u in I, (Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
            * ((toFun x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x))
          = ∫ u in I, ∑ i : Fin n, (toFun x) ^ 2
              * ((Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
                * (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        simp only [Work.BoseFixB1.nCountB, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hcongr, MeasureTheory.integral_finsetSum Finset.univ
          (fun i _ => (hint x i).const_mul ((toFun x) ^ 2)), Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => MeasureTheory.integral_const_mul _ _)
    -- assembly
    have hstep1 : (∫ u in I, Work.BoseFixB1.wbMass v h μ u *
          ((∫ x in Submission.BoseGases.abox n ℓ,
              (toFun x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x)
            / (Work.BoseBoxFix.normB v μ n toFun
              * Work.SmallBoxSliding.chiMass M ℓ d u)))
        = (Work.BoseBoxFix.normB v μ n toFun)⁻¹ *
          (∫ u in I, ∫ x in Submission.BoseGases.abox n ℓ,
            (Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
              * ((toFun x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x)) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      simp only [MeasureTheory.integral_const_mul]
      exact mul_div_eq_inv_mul _ _ _ _
    have hstep3 : (∫ x in Submission.BoseGases.abox n ℓ, ∫ u in I,
          (Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
            * ((toFun x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x))
        = ∫ x in Submission.BoseGases.abox n ℓ,
            (toFun x) ^ 2 * (∑ i : Fin n, Work.BoseFixB1.wbU v h μ (x i)) :=
      MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
        (fun x _ => hpt x)
    calc
      (∫ u in I, Work.BoseFixB1.wbMass v h μ u *
          ((∫ x in Submission.BoseGases.abox n ℓ,
              (toFun x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x)
            / (Work.BoseBoxFix.normB v μ n toFun
              * Work.SmallBoxSliding.chiMass M ℓ d u)))
          = (Work.BoseBoxFix.normB v μ n toFun)⁻¹ *
            (∫ u in I, ∫ x in Submission.BoseGases.abox n ℓ,
              (Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
                * ((toFun x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x)) := hstep1
      _ = (Work.BoseBoxFix.normB v μ n toFun)⁻¹ *
            (∫ x in Submission.BoseGases.abox n ℓ, ∫ u in I,
              (Work.BoseFixB1.wbMass v h μ u / Work.SmallBoxSliding.chiMass M ℓ d u)
                * ((toFun x) ^ 2 * Work.BoseFixB1.nCountB M ℓ d u x)) := by rw [hFubini]
      _ = (Work.BoseBoxFix.normB v μ n toFun)⁻¹ *
            (∫ x in Submission.BoseGases.abox n ℓ,
              (toFun x) ^ 2 * (∑ i : Fin n, Work.BoseFixB1.wbU v h μ (x i))) := by rw [hstep3]
      _ = (∫ x in Submission.BoseGases.abox n ℓ,
              (toFun x) ^ 2 * (∑ i : Fin n, Work.BoseFixB1.wbU v h μ (x i)))
            / Work.BoseBoxFix.normB v μ n toFun := by
          rw [div_eq_mul_inv]
          exact mul_comm _ _

end Work.BoseFixB1.WB
