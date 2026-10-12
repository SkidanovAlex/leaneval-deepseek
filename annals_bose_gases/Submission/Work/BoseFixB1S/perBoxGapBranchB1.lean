import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.boxM1Info
import Submission.Work.BoseFixB1S.fibreWordB1Fix
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.perBoxGapBranchB1` — the gap branch of FS `thm:smallbox` at the sliding box

The target is the branch of FS `thm:smallbox` (`final_v2.tex` l.3907) at the sliding box
`B(u)` in which the box-excited count `n₊(B(u)) = cnPlusBoxInd ℓ (dlBox ℓ d u) (boxMass ℓ d u) Φ`
dominates the condensate count `n·‖Φ‖²`:

    n‖Φ‖² ≤ n₊(B(u))   ⟹   the target's inequality.

## The mathematics

On this branch *no* mean-field analysis is needed: the state is (essentially) fully excited and
the whole content is FS `eq:appgapestimate`, `sbKin ≥ c'²μ(a v)·n₊(B)`, with a *freely chosen*
constant `c'` whose smallness only constrains the diluteness threshold `ε₀`
(`Work.BoseFixB1.gapRegime_of_adm`; `ε₀ ≤ (2(1+π⁻²)c'²+1)^{-1292/13}`, so any finite `c'` is
allowed at a correspondingly small `ε₀`).

The two losses of the left-hand side are then paid as follows, writing `V := boxMass ℓ d u`,
`W := ∬w_{1,B(u)}`, `N := ‖Φ‖²`, `Q := n₊(B(u))`:

* `F(t) ≤ μ(t+μ)` (`Work.BoseFixB1.psiWeight_le_mu_mul_add`, `t = n/V`) kills the background:
  `½F(n/V)·W·N − ½μ²W·N ≤ ½·(n/V)·W·N = ½(μ/V)W·(nN)`.  No division by `V` is needed: the
  comparison uses only `(n/V)·V ≤ n` for `V ≥ 0` and the *upper* mass law `W ≤ K₁(a v)V`
  (`w1MassB_le_const_mul_boxMass` below, from the corpus `w1MassB_le_const_mul_chiMass_regime`
  plus `chiMass ≤ (χ·D_M)²·boxMass`);
* the chemical-potential loss of the potential word is paid by the *linear* fibre bound
  `|w₁-fibre(z)| ≤ ξ(a v)χ_{B(u)}(z)` (`Work.BoseFixB1S.PerBoxFibreB1`, via
  `qLHSwordB_ge_neg_fibreUniform` below): `qLHSwordB ≥ −ξ(a v)D_M·μ·n·N ≥ −ξD_Mμ(a v)·Q`.

Since `Q ≥ nN`, both losses are dominated by multiples of `μ(a v)Q`, and `sbKin ≥ c'²μ(a v)Q`
absorbs them once `c'² ≥ K₁/2 + ξD_M`.  The `C`-term of the target is *not* needed: `C = 0`
works (the left-hand side is antitone in `C`), and the box-support hypothesis and the
interiority of `u` are not used at all.
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

/-! ## 1. The `χ_{B(u)}²`-mass is dominated by the box volume

`χ_{B(u)} = χ(x/ℓ)·χ_M(x/(ℓd) − u)` is bounded by the absolute constant
`chiSupAbs·chiSmallDecay M` and supported in `dlBox ℓ d u` (the corpus
`chiSmallB_eq_zero_of_notMem_dlBox`), so its `L²`-mass `chiMass` is at most that constant
squared times the box volume `boxMass ℓ d u = ∫1_{dlBox}`.  This is the `χ_B ≤ 1`-shaped fact
that turns the corpus's *smooth* mass law `∬w_{1,B} ≤ C(a v)χ-mass` into a bound by the
*indicator* box mass used in the target's density `n/boxMass`. -/

theorem chiMass_le_const_mul_boxMass {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.SmallBoxSliding.chiMass M ℓ d u
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
          * Work.SmallBoxSliding.boxMass ℓ d u := by
  have hχD : ∀ x : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiSmallB M ℓ d u x
        ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    intro x
    have h1 := Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u x
    have h2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
        ≤ Submission.BoseGases.chiSmallDecay M := by
      have h3 := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • x - u)
      rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at h3
    calc Submission.BoseGases.chiSmallB M ℓ d u x
        ≤ |Submission.BoseGases.chiSmallB M ℓ d u x| := le_abs_self _
      _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) := h1
      _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
          mul_le_mul_of_nonneg_left h2 Submission.BoseGases.chiSupAbs_nonneg
  have hboxnn : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.SmallBoxSliding.boxInd ℓ d u x := by
    intro x
    simp only [Work.SmallBoxSliding.boxInd]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3),
      (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2
        ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
            * Work.SmallBoxSliding.boxInd ℓ d u x := by
    intro x
    by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
    · have hbi : Work.SmallBoxSliding.boxInd ℓ d u x = 1 := by
        simp only [Work.SmallBoxSliding.boxInd]
        exact Set.indicator_of_mem hx _
      rw [hbi, mul_one]
      exact pow_le_pow_left₀ (Submission.BoseGases.chiSmallB_nonneg M ℓ d u x) (hχD x) 2
    · have h0 : Submission.BoseGases.chiSmallB M ℓ d u x = 0 :=
        chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd u hx
      rw [h0]
      have h1 : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h1]
      exact mul_nonneg (sq_nonneg _) (hboxnn x)
  have hboxint : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      Work.SmallBoxSliding.boxInd ℓ d u x) MeasureTheory.volume := by
    simp only [Work.SmallBoxSliding.boxInd]
    rw [MeasureTheory.integrable_indicator_iff (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)]
    exact MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
      (s := Submission.BoseGases.dlBox ℓ d u) (C := (1 : ℝ))
      (hs := ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u))
  calc Work.SmallBoxSliding.chiMass M ℓ d u
      = ∫ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2 :=
        Work.SmallBoxSliding.chiMass_def M ℓ d u
    _ ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
            * Work.SmallBoxSliding.boxInd ℓ d u x :=
        MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => sq_nonneg _))
          (hboxint.const_mul _) (Filter.Eventually.of_forall hpt)
    _ = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) ^ 2
          * Work.SmallBoxSliding.boxMass ℓ d u := by
        rw [Work.SmallBoxSliding.boxMass, MeasureTheory.integral_const_mul]

/-! ## 2. The upper mass law against the *box* volume

Composing the corpus `w1MassB_le_const_mul_chiMass_regime` with §1 (the regularity `M` is the
fixed `mValue`). -/

theorem w1MassB_le_const_mul_boxMass {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ K : ℝ, 0 < ε₀ ∧ 0 ≤ K ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          ≤ K * (_root_.BoseGases.a v) * Work.SmallBoxSliding.boxMass
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := by
  obtain ⟨ε₀, C, hε₀, hC, hmass⟩ :=
    Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) h hv hvrad hR hv_supp
  refine ⟨ε₀, C * (Submission.BoseGases.chiSupAbs
    * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2, hε₀,
    mul_nonneg hC (sq_nonneg _), ?_⟩
  intro μ hAdm u
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hW := hmass μ hAdm u
  have hchi := chiMass_le_const_mul_boxMass (M := (Work.BoseBox.paramsAt μ
    (_root_.BoseGases.a v)).M) hM1 hℓ hd u
  have hMD : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = Work.BoseBox.mValue := rfl
  rw [hMD] at hchi
  calc Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      ≤ C * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := hW
    _ ≤ C * (_root_.BoseGases.a v) * ((Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2
            * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :=
        mul_le_mul_of_nonneg_left hchi (mul_nonneg hC hav.le)
    _ = (C * (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue) ^ 2)
          * (_root_.BoseGases.a v) * Work.SmallBoxSliding.boxMass
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := by ring

/-! ## 3. The potential word dominates `−ξ(a v)D_M·μ·n·‖Φ‖²`

The linear fibre bound `|w₁-fibre| ≤ K(a v)χ_{B(u)}` is turned into the *integrated* word bound
by the (already proved) purely measure-theoretic lemma `wordBound_of_fibre`
(`Submission/Work/BoseFixB1S/fibreWordB1Fix.lean`), and the `χ_{B(u)}`-count is then bounded by
`(chiSupAbs·chiSmallDecay M)·n·‖Φ‖²`.  This is the band lemma
`Work.BoseFixB1.qLHSwordB_ge_neg_bandS` with the *uniform* fibre bound in place of the band
supremum (so it holds at every `u`, in particular on the interior). -/

theorem qLHSwordB_ge_neg_fibreUniform {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d μ K : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (ha : 0 < _root_.BoseGases.a v) (hK : 0 ≤ K)
    (hreg : R ≤ ℓ * d / 16) (hregχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ)
    (u : EuclideanSpace ℝ (Fin 3))
    (hfib : ∀ z : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z|
        ≤ (K * _root_.BoseGases.a v) * Submission.BoseGases.chiSmallB M ℓ d u z) :
    -(K * _root_.BoseGases.a v * μ)
        * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
      ≤ Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ := by
  classical
  have hA0 : 0 ≤ K * _root_.BoseGases.a v := mul_nonneg hK ha.le
  have hD0 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  -- the cutoff is bounded by the universal constant
  have hχD : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiSmallB M ℓ d u z
        ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    intro z
    have h1 := Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u z
    have h2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u)
        ≤ Submission.BoseGases.chiSmallDecay M := by
      have h3 := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • z - u)
      rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at h3
    calc Submission.BoseGases.chiSmallB M ℓ d u z
        ≤ |Submission.BoseGases.chiSmallB M ℓ d u z| := le_abs_self _
      _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u) := h1
      _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
          mul_le_mul_of_nonneg_left h2 Submission.BoseGases.chiSupAbs_nonneg
  -- the fibre bound, in the shape consumed by `wordBound_of_fibre`
  have hfib' : ∀ z : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) z
        ≤ (K * _root_.BoseGases.a v) * Submission.BoseGases.chiSmallB M ℓ d u z :=
    fun z => le_trans (le_abs_self _) (hfib z)
  -- the support condition on `v`
  have hvsupp' : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → v z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ tsupport v := subset_closure (Function.mem_support.mpr hne)
    have hz' := hv_supp hmem
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz'
    exact absurd hz' (not_lt.mpr hz)
  -- ### integrability of the three slot families
  have hvint : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hFm : MeasureTheory.AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y)
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)) :=
    Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d)
      (f := Submission.BoseGases.g0 v h) M u
      (Submission.BoseGases.g0_integrable hR hv_supp h).aestronglyMeasurable.aemeasurable
  have hI1 : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2
        * Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
    intro i
    have hbnd : ∀ z ∈ Submission.BoseGases.acube ℓ,
        |∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y|
          ≤ K * _root_.BoseGases.a v
              * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) := by
      intro z _
      calc |∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y|
          ≤ (K * _root_.BoseGases.a v) * Submission.BoseGases.chiSmallB M ℓ d u z := by
            simpa only [Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair] using hfib z
        _ ≤ (K * _root_.BoseGases.a v)
              * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :=
            mul_le_mul_of_nonneg_left (hχD z) hA0
    have hres := Submission.BoseGases.integrableOn_slot_fibre (N := n) (ℓ := ℓ) hℓ i hFm hbnd
      (S := fun x : Submission.BoseGases.XN n => (Φ x) ^ 2) (hΦc.pow 2)
    simpa only [Submission.BoseGases.w1Fibre, Submission.BoseGases.wSmall1Pair] using hres
  have hchiFm : MeasureTheory.AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiScale ℓ z
        * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))).aestronglyMeasurable
  have hIχ : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2
        * Submission.BoseGases.chiSmallB M ℓ d u (x i))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
    intro i
    have hbnd : ∀ z ∈ Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.chiScale ℓ z
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u)|
          ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
      intro z _
      rw [abs_of_nonneg (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ z)
        (Submission.BoseGases.chiSmall_nonneg M _))]
      exact hχD z
    have hres := Submission.BoseGases.integrableOn_slot_fibre (N := n) (ℓ := ℓ) hℓ i hchiFm hbnd
      (S := fun x : Submission.BoseGases.XN n => (Φ x) ^ 2) (hΦc.pow 2)
    simpa only [Submission.BoseGases.chiSmallB] using hres
  have hIw : ∀ p ∈ Submission.BoseGases.pairSet n, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2
        * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by simpa [Submission.BoseGases.pairSet] using hp
    obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox n ℓ) (f := fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      (hΦc.pow 2).continuousOn
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (Submission.BoseGases.zero_mem_abox hℓ.le))
    exact Work.BoseFixB1.integrableOn_slot_wSmallPair (N := n) (ℓ := ℓ) (d := d) (R := R) hℓ hd
      hvint hvsupp' hM hreg hregχ u hpne
      (S := fun x : Submission.BoseGases.X n => (Φ x) ^ 2) (hΦc.pow 2).aestronglyMeasurable hB0 (by
        rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
        exact ae_of_all _ (fun x hx => by simpa [Real.norm_eq_abs] using hB x hx))
  -- ### the word bound
  have hmain := wordBound_of_fibre (v := v) (h := h) (M := M) (ℓ := ℓ) (dd := d) (μ := μ)
    (K := K) (n := n) (Φ := Φ) (u := u) hμ hfib' hIχ hIw hI1
  -- ### the count bound and the pair term
  have hΦ2int : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
    obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox n ℓ) (f := fun x : Submission.BoseGases.X n => (Φ x) ^ 2)
      (hΦc.pow 2).continuousOn
    refine MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      (hΦc.pow 2).aestronglyMeasurable B ?_
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
    exact ae_of_all _ (fun x hx => by simpa [Real.norm_eq_abs] using hB x hx)
  have hsum : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
    have hone : ∀ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i)
        ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by
      intro i
      have hmaj := hΦ2int.const_mul
        (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
      calc ∫ x in Submission.BoseGases.abox n ℓ,
            (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i)
          ≤ ∫ x in Submission.BoseGases.abox n ℓ,
              (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                * (Φ x) ^ 2 :=
            MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _)
                (Submission.BoseGases.chiSmallB_nonneg M ℓ d u (x i))))
              hmaj (Filter.Eventually.of_forall (fun x => by
                have hx := hχD (x i)
                nlinarith [hx, sq_nonneg (Φ x)]))
        _ = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :=
            MeasureTheory.integral_const_mul _ _
    calc (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i))
        ≤ ∑ _i : Fin n, (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmallDecay M)
              * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :=
          Finset.sum_le_sum (fun i _ => hone i)
      _ = (n : ℝ) * ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = (n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) := by ring
  have hpair : 0 ≤ (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
      ∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)) := by
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg (fun p _ => ?_))
    refine integral_nonneg (fun x => mul_nonneg (sq_nonneg _) ?_)
    rw [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled,
      Submission.BoseGases.convScaleSmall]
    refine mul_nonneg (mul_nonneg (Submission.BoseGases.chiSmallB_nonneg M ℓ d u _) ?_)
      (Submission.BoseGases.chiSmallB_nonneg M ℓ d u _)
    refine div_nonneg (div_nonneg (hv _) ?_) (Submission.BoseGases.convScale_nonneg ℓ _)
    rw [Submission.BoseGases.conv3Small]
    exact integral_nonneg (fun z => mul_nonneg (Submission.BoseGases.chiSmall_nonneg M z)
      (Submission.BoseGases.chiSmall_nonneg M (_ - z)))
  -- ### assembly
  have hX0 : 0 ≤ K * (μ * _root_.BoseGases.a v) := mul_nonneg hK (mul_nonneg hμ.le ha.le)
  have h1 : K * (μ * _root_.BoseGases.a v) * (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i))
      ≤ K * (μ * _root_.BoseGases.a v)
          * ((n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)) :=
    mul_le_mul_of_nonneg_left hsum hX0
  have h2 : -(K * _root_.BoseGases.a v * μ)
        * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
      = -(K * (μ * _root_.BoseGases.a v)
          * ((n : ℝ) * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2))) := by ring
  rw [h2]
  linarith [h1, hpair, hmain]

/-! ## 4. The arithmetic of the gap branch -/

/-- `(n/V)·V ≤ n` for `n ≥ 0`, `V ≥ 0` (no division hypothesis: for `V = 0` both sides
degenerate correctly). -/
private lemma div_mul_le_self {n V : ℝ} (hn : 0 ≤ n) (hV : 0 ≤ V) : n / V * V ≤ n := by
  rcases eq_or_lt_of_le hV with h | h
  · rw [← h, div_zero, zero_mul]
    exact hn
  · rw [div_mul_cancel₀ n (ne_of_gt h)]

/-- **The pure arithmetic of the gap branch.**  From the two quantitative inputs
`W ≤ K₁(a v)V`, `sbKin ≥ c'²μ(a v)Q`, `qLHSwordB ≥ −(KD·μ(a v))·n‖Φ‖²`, the count domination
`n‖Φ‖² ≤ Q` and `K₁/2 + KD ≤ c'²`, the target's left-hand side is dominated by
`sbKin + qLHSwordB`. -/
private lemma gapArith {μ a V W N Q F SB QL K₁ KD c' : ℝ} {n : ℕ}
    (hn : (0 : ℝ) ≤ (n : ℝ)) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hV : 0 ≤ V) (hW : 0 ≤ W) (hN : 0 ≤ N)
    (hQ : 0 ≤ Q) (hF : F ≤ μ * ((n : ℝ) / V + μ)) (hpay : (n : ℝ) * N ≤ Q)
    (hWV : W ≤ K₁ * a * V) (hK₁ : 0 ≤ K₁)
    (hc' : K₁ / 2 + KD ≤ c' ^ 2) (hKD : 0 ≤ KD)
    (hsb : c' ^ 2 * μ * a * Q ≤ SB) (hql : -(KD * μ * a) * (n : ℝ) * N ≤ QL) :
    (1 / 2) * F * W * N - (1 / 2) * μ ^ 2 * W * N ≤ SB + QL := by
  have hdiv0 : 0 ≤ (n : ℝ) / V := div_nonneg hn hV
  -- step 1: the `F`-weight kills the background
  have hstep1 : (1 / 2) * F * W * N - (1 / 2) * μ ^ 2 * W * N
      ≤ (1 / 2) * μ * ((n : ℝ) / V) * W * N := by
    have hWN : 0 ≤ W * N := mul_nonneg hW hN
    have h2 : F * (W * N) ≤ (μ * ((n : ℝ) / V + μ)) * (W * N) :=
      mul_le_mul_of_nonneg_right hF hWN
    nlinarith [h2]
  -- step 2: the mass law `W ≤ K₁(a v)V` and `(n/V)V ≤ n` bound the `F`-term by `K₁μ(a v)Q`
  have hstep2 : (1 / 2) * μ * ((n : ℝ) / V) * W * N ≤ (1 / 2) * K₁ * μ * a * Q := by
    have hWV' : (n : ℝ) / V * W ≤ (n : ℝ) / V * (K₁ * a * V) :=
      mul_le_mul_of_nonneg_left hWV hdiv0
    have hcoll : (n : ℝ) / V * (K₁ * a * V) = K₁ * a * ((n : ℝ) / V * V) := by ring
    have hle1 : (n : ℝ) / V * W ≤ K₁ * a * (n : ℝ) := by
      rw [hcoll] at hWV'
      have h3 := div_mul_le_self hn hV
      nlinarith [hWV', h3, mul_nonneg hK₁ ha]
    have h5 : (n : ℝ) / V * W * N ≤ K₁ * a * ((n : ℝ) * N) := by
      nlinarith [hle1, hN, mul_nonneg hK₁ ha]
    have h6 : (1 / 2) * K₁ * μ * a * ((n : ℝ) * N) ≤ (1 / 2) * K₁ * μ * a * Q :=
      mul_le_mul_of_nonneg_left hpay (by positivity)
    nlinarith [h5, h6]
  -- step 3: `c' ^ 2 ≥ K₁/2 + KD` and `nN ≤ Q` give the payment by `sbKin + qLHSwordB`
  have hstep3 : (1 / 2) * K₁ * μ * a * Q ≤ SB + QL := by
    have hQd : 0 ≤ μ * a * Q := by positivity
    have h7 : (1 / 2) * K₁ * μ * a * Q ≤ c' ^ 2 * μ * a * Q - KD * μ * a * Q := by
      have h8 : K₁ / 2 ≤ c' ^ 2 - KD := by linarith
      nlinarith [h8, hQd]
    have h9 : -(KD * μ * a) * Q ≤ QL := by
      have h10 : 0 ≤ KD * μ * a := by positivity
      have h11 : -(KD * μ * a) * Q ≤ -(KD * μ * a) * ((n : ℝ) * N) :=
        mul_le_mul_of_nonpos_left hpay (by linarith)
      linarith [hql]
    linarith [h7, h9, hsb]
  linarith [hstep1, hstep2, hstep3]

/-! ## 5. The target -/

theorem perBoxGapBranchB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
          Continuous Φ →
          (∀ᵐ x ∂(MeasureTheory.volume.restrict
              (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
            Φ x ≠ 0 → ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
          (n : ℝ) * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
            ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Φ →
          (1 / 2) * (Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / Work.SmallBoxSliding.boxMass
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u))
              * Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
            - (1 / 2) * μ ^ 2 * Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
            - C * (μ ^ 2 * (_root_.BoseGases.a v)
                    * (R ^ 2 * μ ^ (2 / 3 : ℝ) + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                    * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  + μ * (_root_.BoseGases.a v))
              * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
          ≤ Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u Φ
            + Work.SmallBoxSliding.qLHSwordB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u Φ := by
  obtain ⟨ε₁, K₁, hε₁, hK₁0, hmass⟩ :=
    w1MassB_le_const_mul_boxMass (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₂, ξ, hε₂, hξ, hfib⟩ := PerBoxFibreB1 (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εr, hεr, hregr⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  set D : ℝ := Submission.BoseGases.chiSupAbs
    * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue with hDdef
  have hD0 : 0 ≤ D := mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
    (Submission.BoseGases.chiSmallDecay_nonneg Work.BoseBox.mValue)
  have hKD0 : 0 ≤ ξ * D := mul_nonneg hξ hD0
  set c' : ℝ := K₁ / 2 + ξ * D + 1 with hc'def
  have hc'0 : 0 ≤ c' := by rw [hc'def]; linarith
  have hc'ge : K₁ / 2 + ξ * D ≤ c' ^ 2 := by
    have h1 : 1 ≤ c' := by rw [hc'def]; linarith
    have h2 : c' ≤ c' ^ 2 := by
      have h3 : 0 ≤ c' * (c' - 1) := mul_nonneg (by linarith) (by linarith)
      nlinarith [h3]
    rw [hc'def] at h2
    rw [hc'def]
    linarith
  obtain ⟨ε₃, hε₃, hreg3⟩ := Work.BoseFixB1.gapRegime_of_adm (v := v) hav (c' := c') hc'0
  refine ⟨min (min ε₁ ε₂) (min ε₃ εr), 0,
    lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hεr), le_refl 0, ?_⟩
  intro μ hAdm n Φ u hu hΦc hsupp hpay
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  have hAdm₁ : Work.BoseBoxFix.Adm v ε₁ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hAdm₂ : Work.BoseBoxFix.Adm v ε₂ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hAdm₃ : Work.BoseBoxFix.Adm v ε₃ μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdmr : Work.BoseBoxFix.Adm v εr μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
  have hdilr : μ * (_root_.BoseGases.a v) ^ 3 ≤ εr :=
    le_trans (Work.BoseFixB1.adm_dilute hAdm) (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hR16, hRχ⟩ := hregr μ hμ hdilr
  -- the abbreviations of the target
  set V : ℝ := Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hVdef
  set W : ℝ := Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u with hWdef
  set N : ℝ := ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
    (Φ x) ^ 2 with hNdef
  set Q : ℝ := Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) V Φ with hQdef
  have hV0 : 0 ≤ V := by
    rw [hVdef]
    simp only [Work.SmallBoxSliding.boxMass]
    exact integral_nonneg (fun x => by
      simp only [Work.SmallBoxSliding.boxInd]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  have hW0 : 0 ≤ W := by
    rw [hWdef]
    exact Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓ hd u
  have hN0 : 0 ≤ N := by
    rw [hNdef]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    simp only [Work.UBBInputs8.cnPlusBoxInd]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  -- the quantitative inputs
  have hpay' : (n : ℝ) * N ≤ Q := by
    simpa only [hNdef, hQdef, hVdef] using hpay
  have hF : Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / V) ≤ μ * ((n : ℝ) / V + μ) :=
    Work.BoseFixB1.psiWeight_le_mu_mul_add hμ (div_nonneg (Nat.cast_nonneg n) hV0)
  have hWV : W ≤ K₁ * (_root_.BoseGases.a v) * V := by
    have hm := hmass μ hAdm₁ u
    simpa only [hWdef, hVdef] using hm
  have hsb : c' ^ 2 * μ * (_root_.BoseGases.a v) * Q
      ≤ Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u Φ := by
    have hres := Work.BoseFixB1.sbKin_ge_mu_av_cnPlus (v := v) (μ := μ) (c' := c')
      (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) (u := u) (n := n) Φ
      hav.le hμ.le hc'0 (mul_pos hd hℓ) (Work.BoseFixB1.adm_eT_pos hAdm)
      (hreg3 μ hAdm₃) (Work.BoseFixB1.tBwordKinInd_nonneg _)
    simpa only [hQdef, hVdef] using hres
  have hql : -(ξ * D * μ * (_root_.BoseGases.a v)) * (n : ℝ) * N
      ≤ Work.SmallBoxSliding.qLHSwordB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u Φ := by
    have hfibμ := hfib μ hAdm₂ u
    have hres := qLHSwordB_ge_neg_fibreUniform (v := v) h hv hv1 hR hv_supp hM1 hℓ hd hμ hav
      hξ hR16 hRχ Φ hΦc u hfibμ
    have heq : -(ξ * D * μ * (_root_.BoseGases.a v)) * (n : ℝ) * N
        = -(ξ * _root_.BoseGases.a v * μ)
            * (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
            * (n : ℝ)
            * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Φ x) ^ 2) := by
      rw [hDdef, hNdef, Work.BoseFixB1.M_eq_mValue μ (_root_.BoseGases.a v)]
      ring
    rw [heq]
    exact hres
  -- the assembly
  have hkey := gapArith (n := n) (Nat.cast_nonneg n) hμ.le hav.le hV0 hW0 hN0 hQ0 hF hpay'
    hWV hK₁0 hc'ge hKD0 hsb hql
  simp only [zero_mul, sub_zero]
  exact hkey

end Work.BoseFixB1S
