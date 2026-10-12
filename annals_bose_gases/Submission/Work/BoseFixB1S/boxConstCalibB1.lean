import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.sectorPassageB1Support
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.boxConstCalibB1` — the box-constant calibration of the localised kernels

This module is the **thick/box-constant calibration** input of the flat branch of `PerBoxF`
(the residual of `Submission/Work/BoseFixB1S/perBoxFWeightB1.lean`); see
`Submission/Work/BoseFixB1S/FINDING_perBoxFWeightB1.md` §3 item 2.

The localised cutoffs are supported in the sliding box: `chiSmallB M ℓ d u x ≠ 0` forces
`x ∈ dlBox ℓ d u` (`chiSmallB_mem_dlBox_B1S`), hence both the one-body and the two-body localised
kernels are supported in `dlBox ℓ d u × dlBox ℓ d u`
(`wSmallPair_eq_zero_of_notMem_B1S` and its `wSmall1Pair` companion).  Consequently the `χ`-mass,
the per-box kernel mass and the pair mass can be computed with the integration *restricted to the
small box*:

* `chiMass_eq_setIntegral_dlBox`  : `∫_{B(u)} χ_{B(u)}² = chiMass M ℓ d u`;
* `fibreMass_eq_w1MassB`          : `∫_{B(u)} (∫_y w_{1,B(u)}(x,y) dy) = w1MassB h M ℓ d u`
  (the fibre's total mass is the kernel mass — the input that turns FS's chemical-potential loss
  `μ·Σᵢ∫Φ²∫_y w_{1,B}(xᵢ,y)dy` into `μ·(N/|B|)·w1MassB` at the box-constant state);
* `pairMass_eq_setIntegral`       : `∫_{B(u)}∫_{B(u)} w_{B(u)} = ∬w_{B(u)}` (any numerator);
* `w1MassB_eq_setIntegral_dlBox`  : `∫_{B(u)}∫_{B(u)} w_{1,B(u)} = w1MassB h M ℓ d u`.

All four are support-collapses (`MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero`):
they need no thickness hypothesis and no positivity of the numerator, only `1 ≤ M`, `0 < ℓ`,
`0 < d` — so they are valid on *every* box of the interior, thick or thin.

The companions for the *slot* integrals over `B(u)^n` (which is the form the flat-branch
assembly consumes) follow from these by Fubini over the `n` slots; that Fubini step is the
content of the ANOVA module `Submission/Work/BoseFixB1S/anovaLeCnPlusB1.lean` (statement recorded
in the FINDING).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped BigOperators ENNReal Real Topology

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Left support of the localised kernels.**  If `x ∉ B(u) = dlBox ℓ d u` then the sliding
cutoff at `x` vanishes, hence `wSmallPair M ℓ d u f x y = 0` for every `y` (and every numerator
`f`). -/
theorem wSmallPair_eq_zero_of_notMem_left {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (y : EuclideanSpace ℝ (Fin 3)) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∉ dlBox ℓ d u) :
    wSmallPair M ℓ d u f x y = 0 := by
  have hchi : chiSmallB M ℓ d u x = 0 := by
    by_contra hne
    exact hx (chiSmallB_mem_dlBox_B1S hM hℓ hd u x hne)
  simp only [Submission.BoseGases.wSmallPair, hchi, zero_mul]

/-- **Left support of the localised one-body kernel** (`wSmall1Pair` is `wSmallPair` with the
numerator `g₀ = v(1−ω)`, definitionally). -/
theorem wSmall1Pair_eq_zero_of_notMem_left {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (y : EuclideanSpace ℝ (Fin 3))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∉ dlBox ℓ d u) :
    wSmall1Pair h M ℓ d u x y = 0 := by
  rw [Submission.BoseGases.wSmall1Pair]
  exact wSmallPair_eq_zero_of_notMem_left hM hℓ hd u (g0 v h) y hx

/-- **Right support of the localised kernels**: `y ∉ B(u)` kills `wSmallPair M ℓ d u f x y`. -/
theorem wSmallPair_eq_zero_of_notMem_right {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∉ dlBox ℓ d u) :
    wSmallPair M ℓ d u f x y = 0 := by
  have hchi : chiSmallB M ℓ d u y = 0 := by
    by_contra hne
    exact hy (chiSmallB_mem_dlBox_B1S hM hℓ hd u y hne)
  simp only [Submission.BoseGases.wSmallPair, hchi, mul_zero]

/-- **Right support of the localised one-body kernel.** -/
theorem wSmall1Pair_eq_zero_of_notMem_right {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (x : EuclideanSpace ℝ (Fin 3))
    {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∉ dlBox ℓ d u) :
    wSmall1Pair h M ℓ d u x y = 0 := by
  rw [Submission.BoseGases.wSmall1Pair]
  exact wSmallPair_eq_zero_of_notMem_right hM hℓ hd u (g0 v h) x hy

/-- **The `χ_{B(u)}²`-mass is the integral over the small box** (the cutoff is supported in
`dlBox ℓ d u`). -/
theorem chiMass_eq_setIntegral_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∫ x in dlBox ℓ d u, (chiSmallB M ℓ d u x) ^ 2 = Work.SmallBoxSliding.chiMass M ℓ d u := by
  rw [Work.SmallBoxSliding.chiMass_def]
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have h0 : chiSmallB M ℓ d u x = 0 := by
    by_contra hne
    exact hx (chiSmallB_mem_dlBox_B1S hM hℓ hd u x hne)
  rw [h0]
  norm_num

/-- **The total mass of the localised one-body fibre is the kernel mass.**
`∫_{B(u)} (∫_y w_{1,B(u)}(x,y) dy) dx = ∬ w_{1,B(u)} = w1MassB h M ℓ d u`. -/
theorem fibreMass_eq_w1MassB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) :
    ∫ x in dlBox ℓ d u,
        (∫ y : EuclideanSpace ℝ (Fin 3), wSmall1Pair h M ℓ d u x y)
      = Work.BoseFixB1.w1MassB h M ℓ d u := by
  rw [Work.BoseFixB1.w1MassB]
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have hz : ∀ y : EuclideanSpace ℝ (Fin 3), wSmall1Pair h M ℓ d u x y = 0 :=
    fun y => wSmall1Pair_eq_zero_of_notMem_left hM hℓ hd u y hx
  simp only [hz]
  simp

/-- **The localised two-body kernel integrates over `B(u) × B(u)` to its full mass**, for an
arbitrary numerator `f`. -/
theorem pairMass_eq_setIntegral_calib {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (f : EuclideanSpace ℝ (Fin 3) → ℝ) :
    ∫ x in dlBox ℓ d u, ∫ y in dlBox ℓ d u, wSmallPair M ℓ d u f x y
      = ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
          wSmallPair M ℓ d u f x y := by
  have hinner : ∀ x : EuclideanSpace ℝ (Fin 3),
      (∫ y in dlBox ℓ d u, wSmallPair M ℓ d u f x y)
        = ∫ y : EuclideanSpace ℝ (Fin 3), wSmallPair M ℓ d u f x y := fun x =>
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => wSmallPair_eq_zero_of_notMem_right hM hℓ hd u f x hy)
  simp only [hinner]
  refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have hz : ∀ y : EuclideanSpace ℝ (Fin 3), wSmallPair M ℓ d u f x y = 0 :=
    fun y => wSmallPair_eq_zero_of_notMem_left hM hℓ hd u f y hx
  simp only [hz]
  simp

/-- **The mass of the localised one-body kernel is the double integral over `B(u) × B(u)`.** -/
theorem w1MassB_eq_setIntegral_dlBox {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∫ x in dlBox ℓ d u, ∫ y in dlBox ℓ d u, wSmall1Pair h M ℓ d u x y
      = Work.BoseFixB1.w1MassB h M ℓ d u := by
  have hinner : ∀ x : EuclideanSpace ℝ (Fin 3),
      (∫ y in dlBox ℓ d u, wSmall1Pair h M ℓ d u x y)
        = ∫ y : EuclideanSpace ℝ (Fin 3), wSmall1Pair h M ℓ d u x y := fun x =>
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => wSmall1Pair_eq_zero_of_notMem_right hM hℓ hd u x hy)
  simp only [hinner]
  exact fibreMass_eq_w1MassB hM hℓ hd u

/-- **The `χ_{B(u)}²`-mass is also the integral over the centred cube** (the support
`supp χ_{B(u)} ⊆ acube ℓ` of FS's ball bump). -/
theorem chiMass_eq_setIntegral_acube {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∫ y in Submission.BoseGases.acube ℓ, (chiSmallB M ℓ d u y) ^ 2
      = Work.SmallBoxSliding.chiMass M ℓ d u := by
  have h0 : ∀ y ∉ Submission.BoseGases.acube ℓ, (chiSmallB M ℓ d u y) ^ 2 = 0 := by
    intro y hy
    have hz : chiSmallB M ℓ d u y = 0 := by
      by_contra hne
      have hmem : y ∈ Submission.BoseGases.acube ℓ := by
        rw [Submission.BoseGases.mem_acube_iff]
        intro j
        have h := Submission.BoseGases.chiSmallB_support_big_box hM hℓ hne j
        rw [abs_le] at h
        exact ⟨by linarith [h.1], h.2⟩
      exact hy hmem
    rw [hz]
    norm_num
  have h1 : ∀ y ∉ Submission.BoseGases.dlBox ℓ d u, (chiSmallB M ℓ d u y) ^ 2 = 0 := by
    intro y hy
    have hz : chiSmallB M ℓ d u y = 0 := by
      by_contra hne
      exact hy (chiSmallB_mem_dlBox_B1S hM hℓ hd u y hne)
    rw [hz]
    norm_num
  rw [← chiMass_eq_setIntegral_dlBox hM hℓ hd u]
  exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h0).trans
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h1).symm

/-- **The smooth count calibration**: over the centred `N`-particle box the smooth count
`nCountB M ℓ d u = Σᵢ χ_{B(u)}(xᵢ)²` integrates to `N·(ℓ³)^{N−1}·chiMass` (the box-constant
value of the count, which is what the flat branch's `F`-slot is calibrated against). -/
theorem integral_nCountB_abox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {N : ℕ} (u : EuclideanSpace ℝ (Fin 3)) :
    ∫ x in Submission.BoseGases.abox N ℓ, Work.BoseFixB1.nCountB M ℓ d u x
      = (N : ℝ) * (ℓ ^ 3) ^ (N - 1) * Work.SmallBoxSliding.chiMass M ℓ d u := by
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 3) => (chiSmallB M ℓ d u y) ^ 2) :=
    (chiSmallB_continuous hM hℓ hd u).pow 2
  have hint : MeasureTheory.IntegrableOn (fun y : EuclideanSpace ℝ (Fin 3) => (chiSmallB M ℓ d u y) ^ 2)
      (Submission.BoseGases.acube ℓ) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      hcont.continuousOn
  have hstep : ∀ i : Fin N,
      ∫ x in Submission.BoseGases.abox N ℓ, (chiSmallB M ℓ d u (x i)) ^ 2
        = (ℓ ^ 3) ^ (N - 1) * Work.SmallBoxSliding.chiMass M ℓ d u := by
    intro i
    rw [Work.UBBInputs8.A.integral_abox_comp_apply hℓ.le i hint,
      chiMass_eq_setIntegral_acube hM hℓ hd u]
  have hterm : ∀ i : Fin N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N => (chiSmallB M ℓ d u (x i)) ^ 2)
      (Submission.BoseGases.abox N ℓ) := fun i =>
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact N hℓ)
      ((hcont.comp (continuous_apply i)).continuousOn)
  change ∫ x in Submission.BoseGases.abox N ℓ,
      (∑ i : Fin N, (chiSmallB M ℓ d u (x i)) ^ 2) = _
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hterm i)]
  rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The fibre-slot calibration**: over the centred `N`-particle box, one slot of the
localised fibre integrates to `(ℓ³)^{N−1}·w1MassB` — the box-constant value of FS's
chemical-potential loss `μ·Σᵢ∫Φ²∫_y w_{1,B}(xᵢ,y)dy` (namely `μ·(N/|B|)·w1MassB`).

The integrability of the fibre over `acube ℓ` is carried as a hypothesis (it follows from the
corpus's uniform fibre bound `Work.BoseFixB1.wSmall1Pair_fibre_abs_le` plus joint measurability of
the kernel); this is the same `IntegrableOn` discipline the corpus's per-box statements use. -/
theorem integral_fibre_slot_abox {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {N : ℕ} (i : Fin N)
    (u : EuclideanSpace ℝ (Fin 3))
    (hint : MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        ∫ y in Submission.BoseGases.acube ℓ, wSmall1Pair h M ℓ d u z y)
      (Submission.BoseGases.acube ℓ)) :
    ∫ x in Submission.BoseGases.abox N ℓ,
        (∫ y : EuclideanSpace ℝ (Fin 3), wSmall1Pair h M ℓ d u (x i) y)
      = (ℓ ^ 3) ^ (N - 1) * Work.BoseFixB1.w1MassB h M ℓ d u := by
  -- the `y`-support of the kernel is inside `dlBox ⊆ acube ℓ`, so the full `y`-integral is the
  -- integral over `acube ℓ`
  have hfib : ∀ z : EuclideanSpace ℝ (Fin 3),
      (∫ y : EuclideanSpace ℝ (Fin 3), wSmall1Pair h M ℓ d u z y)
        = ∫ y in Submission.BoseGases.acube ℓ, wSmall1Pair h M ℓ d u z y := fun z =>
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      refine wSmall1Pair_eq_zero_of_notMem_right hM hℓ hd u z ?_
      intro hyd
      exact hy ((Submission.BoseGases.mem_dlBox_iff ℓ d u y).mp hyd).1)).symm
  -- the `z`-support of the fibre is inside `dlBox ⊆ acube ℓ`, so the `acube ℓ`-integral of the
  -- fibre is its full integral
  have hfz : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ Submission.BoseGases.acube ℓ →
      (∫ y in Submission.BoseGases.acube ℓ, wSmall1Pair h M ℓ d u z y) = 0 := by
    intro z hz
    have hz' : z ∉ Submission.BoseGases.dlBox ℓ d u := fun hd' =>
      hz ((Submission.BoseGases.mem_dlBox_iff ℓ d u z).mp hd').1
    have hzero : ∀ y : EuclideanSpace ℝ (Fin 3), wSmall1Pair h M ℓ d u z y = 0 :=
      fun y => wSmall1Pair_eq_zero_of_notMem_left hM hℓ hd u y hz'
    simp only [hzero]
    simp
  calc ∫ x in Submission.BoseGases.abox N ℓ,
        (∫ y : EuclideanSpace ℝ (Fin 3), wSmall1Pair h M ℓ d u (x i) y)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (∫ y in Submission.BoseGases.acube ℓ, wSmall1Pair h M ℓ d u (x i) y) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun x => hfib (x i)))
    _ = (ℓ ^ 3) ^ (N - 1)
          * ∫ z in Submission.BoseGases.acube ℓ,
              (∫ y in Submission.BoseGases.acube ℓ, wSmall1Pair h M ℓ d u z y) :=
        Work.UBBInputs8.A.integral_abox_comp_apply hℓ.le i hint
    _ = (ℓ ^ 3) ^ (N - 1) * Work.BoseFixB1.w1MassB h M ℓ d u := by
        congr 1
        rw [Work.BoseFixB1.w1MassB]
        rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hfz]
        exact integral_congr_ae (Filter.Eventually.of_forall (fun z => (hfib z).symm))

end Work.BoseFixB1S
