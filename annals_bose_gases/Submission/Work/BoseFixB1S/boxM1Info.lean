import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixB1S.perBoxCrudeLowerB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxM1Info` — the two-sided mass bound for `boxM1`

`boxM1 ℓ (dlBox ℓ d u) w₁ = ∫_{B(u)} (∫_{Λ} w₁(z,y) dy) dz` is the localised
one-body mass of the sliding box `B(u) = dlBox ℓ d u`; the target says that for the
localised kernels `w₁ = wSmall1Pair` (and the two-body kernel `wSmallPair (g₂)`), the
mass is nonnegative, is `≤ K · (a v) · χ_{B(u)}²`-mass, and is dominated by the
localised two-body mass.

The mathematical content is entirely in the three corpus lemmas

* `Work.BoseFixB1.w1MassB_nonneg` (nonnegativity),
* `Work.BoseFixB1.WB.mass_upper` (the sharp `≤ C(a v)·chiMass` bound),
* `Work.BoseFixB1.w1MassB_le_w2MassB_localised` (`w₁ ≤ w₂`, FS `lm:w2>w1`),

all of which are stated for the *global* mass `w1MassB h M ℓ d u = ∫∫ wSmall1Pair`
(nested full-space integrals) resp. for pair integrals over the big box
`acube ℓ ×ˢ acube ℓ`.  The work here is the (purely measure-theoretic) transport
between those forms:

* the smooth cutoff is supported in the sliding box,
  `chiSmallB M ℓ d u z ≠ 0 → z ∈ dlBox ℓ d u` (proved below), so every localised
  kernel vanishes off `dlBox ℓ d u` in each variable;
* hence `boxM1 ℓ (dlBox ℓ d u) w = ∫ x, ∫ y, w x y` (`boxM1_eq_nested`) and, using
  Fubini (`MeasureTheory.setIntegral_prod`) plus the integrability of the localised
  one-body kernel (`Work.BoseFixB1.integrableOn_wSmallPair_cube`),
  `boxM1 ℓ (dlBox ℓ d u) w = ∫ p in acube ℓ ×ˢ acube ℓ, w p.1 p.2`
  (`boxM1_eq_acubePair`);
* likewise `boxM2 volA (dlBox ℓ d u) w = ∫ p in acube ℓ ×ˢ acube ℓ, w p.1 p.2`
  (`boxM2_eq_acubePair`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option linter.unusedVariables false

/-! ## 0. The localised cutoff is supported in the sliding box -/

/-- `chiSmallB M ℓ d u z ≠ 0` forces `z ∈ dlBox ℓ d u`: the `ℓ`-scale factor confines
`z` to `acube ℓ` (the bump `χ` is supported in the ball of radius `1/2`) and the
`ℓd`-scale cosine factor confines `z - (ℓd)•u` to `acube (ℓd)`. -/
lemma chiSmallB_eq_zero_of_notMem_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : ℝ³) {x : ℝ³} (hx : x ∉ dlBox ℓ d u) :
    chiSmallB M ℓ d u x = 0 := by
  by_contra hne
  have hfac : chiSmallB M ℓ d u x = chiScale ℓ x * chiSmall M ((ℓ * d)⁻¹ • x - u) := rfl
  have h1 : chiScale ℓ x ≠ 0 := fun h => hne (by rw [hfac, h, zero_mul])
  have h2 : chiSmall M ((ℓ * d)⁻¹ • x - u) ≠ 0 := fun h => hne (by rw [hfac, h, mul_zero])
  have hbase : chiSmallBase M ((ℓ * d)⁻¹ • x - u) ≠ 0 := by
    intro hb
    exact h2 (by rw [chiSmall, hb]; simp)
  have hcoord : ∀ j : Fin 3, |(((ℓ * d)⁻¹ • x - u).ofLp j)| ≤ 1 / 2 :=
    fun j => chiSmallBase_support_mem_abs_le hM hbase j
  refine hx ⟨chiScale_mem_acube hℓ h1, ?_⟩
  change x - (ℓ * d) • u ∈ acube (ℓ * d)
  rw [mem_acube_iff]
  intro j
  rw [Set.mem_Icc]
  have h := hcoord j
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hrew2 : ((ℓ * d)⁻¹ • x - u) = (ℓ * d)⁻¹ • (x - (ℓ * d) • u) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hld), one_smul]
  have hrew : ((ℓ * d)⁻¹ • x - u).ofLp j = (ℓ * d)⁻¹ * (x - (ℓ * d) • u).ofLp j := by
    rw [hrew2]; simp [PiLp.smul_apply]
  rw [hrew, abs_mul, abs_of_pos (inv_pos.mpr hld)] at h
  have h2' : |(x - (ℓ * d) • u).ofLp j| ≤ ℓ * d / 2 := by
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hld)
    have hsimp : ℓ * d * ((ℓ * d)⁻¹ * |(x - (ℓ * d) • u).ofLp j|)
        = |(x - (ℓ * d) • u).ofLp j| := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hld), one_mul]
    rw [hsimp] at hmul
    linarith [hmul]
  exact ⟨by linarith [(abs_le.mp h2').1], by linarith [(abs_le.mp h2').2]⟩

/-- Every localised kernel (`wSmallPair M ℓ d u f` for any numerator `f`) vanishes as
soon as one of its arguments leaves the sliding box. -/
lemma wSmallPair_eq_zero_of_notMem_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : ℝ³) {f : ℝ³ → ℝ} {x y : ℝ³}
    (h : x ∉ dlBox ℓ d u ∨ y ∉ dlBox ℓ d u) :
    wSmallPair M ℓ d u f x y = 0 := by
  rcases h with hx | hy
  · have hz : chiSmallB M ℓ d u x = 0 := chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd u hx
    simp [wSmallPair, hz]
  · have hz : chiSmallB M ℓ d u y = 0 := chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd u hy
    simp [wSmallPair, hz]

/-! ## 1. Transport of `boxM1` / `boxM2` to the global and big-box forms -/

/-- `boxM1` at a kernel supported in the sliding box is the *global* nested integral. -/
lemma boxM1_eq_nested {ℓ d : ℝ} (u : ℝ³) {w : ℝ³ → ℝ³ → ℝ}
    (hvan : ∀ x y : ℝ³, (x ∉ dlBox ℓ d u ∨ y ∉ dlBox ℓ d u) → w x y = 0) :
    boxM1 ℓ (dlBox ℓ d u) w = ∫ x : ℝ³, ∫ y : ℝ³, w x y := by
  have h1 : boxM1 ℓ (dlBox ℓ d u) w = ∫ z in dlBox ℓ d u, ∫ y : ℝ³, w z y := by
    rw [boxM1]
    refine setIntegral_congr_fun (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
      (fun z _ => ?_)
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => hvan z y (Or.inr (fun hmem => hy (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u hmem))))
  have h2 : (∫ z in dlBox ℓ d u, ∫ y : ℝ³, w z y) = ∫ z : ℝ³, ∫ y : ℝ³, w z y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      have hz0 : (fun y : ℝ³ => w z y) = fun _ => (0 : ℝ) := funext (fun y => hvan z y (Or.inl hz))
      rw [hz0, integral_zero])
  rw [h1, h2]

/-- The pair integral over `acube ℓ × acube ℓ` of a kernel supported in the sliding box
equals the global nested integral (Fubini, `MeasureTheory.setIntegral_prod`). -/
lemma acubePair_eq_nested {ℓ d : ℝ} (u : ℝ³) {w : ℝ³ → ℝ³ → ℝ}
    (hvan : ∀ x y : ℝ³, (x ∉ dlBox ℓ d u ∨ y ∉ dlBox ℓ d u) → w x y = 0)
    (hInt : IntegrableOn (fun p : ℝ³ × ℝ³ => w p.1 p.2) (acube ℓ ×ˢ acube ℓ)) :
    (∫ p in acube ℓ ×ˢ acube ℓ, w p.1 p.2) = ∫ x : ℝ³, ∫ y : ℝ³, w x y := by
  have h1 : (∫ p in acube ℓ ×ˢ acube ℓ, w p.1 p.2)
      = ∫ x in acube ℓ, ∫ y in acube ℓ, w x y :=
    MeasureTheory.setIntegral_prod (fun p : ℝ³ × ℝ³ => w p.1 p.2) hInt
  have h2 : (∫ x in acube ℓ, ∫ y in acube ℓ, w x y) = ∫ x in acube ℓ, ∫ y : ℝ³, w x y := by
    refine setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) (fun x _ => ?_)
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => hvan x y (Or.inr (fun hmem => hy (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u hmem))))
  have h3 : (∫ x in acube ℓ, ∫ y : ℝ³, w x y) = ∫ x : ℝ³, ∫ y : ℝ³, w x y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hx0 : (fun y : ℝ³ => w x y) = fun _ => (0 : ℝ) :=
        funext (fun y => hvan x y (Or.inl (fun hmem => hx (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u hmem))))
      rw [hx0, integral_zero])
  rw [h1, h2, h3]

/-- `boxM1` at a kernel supported in the sliding box is the pair integral over the big box. -/
lemma boxM1_eq_acubePair {ℓ d : ℝ} (u : ℝ³) {w : ℝ³ → ℝ³ → ℝ}
    (hvan : ∀ x y : ℝ³, (x ∉ dlBox ℓ d u ∨ y ∉ dlBox ℓ d u) → w x y = 0)
    (hInt : IntegrableOn (fun p : ℝ³ × ℝ³ => w p.1 p.2) (acube ℓ ×ˢ acube ℓ)) :
    boxM1 ℓ (dlBox ℓ d u) w = ∫ p in acube ℓ ×ˢ acube ℓ, w p.1 p.2 :=
  (boxM1_eq_nested u hvan).trans (acubePair_eq_nested u hvan hInt).symm

/-- `boxM2` at a kernel supported in the sliding box is the pair integral over the big box. -/
lemma boxM2_eq_acubePair {ℓ d : ℝ} (u : ℝ³) {volA : ℝ} {w : ℝ³ → ℝ³ → ℝ}
    (hvan : ∀ x y : ℝ³, (x ∉ dlBox ℓ d u ∨ y ∉ dlBox ℓ d u) → w x y = 0) :
    boxM2 volA (dlBox ℓ d u) w = ∫ p in acube ℓ ×ˢ acube ℓ, w p.1 p.2 := by
  have h1 : boxM2 volA (dlBox ℓ d u) w = ∫ p in dlBox ℓ d u ×ˢ dlBox ℓ d u, w p.1 p.2 := rfl
  have h2 : (∫ p in dlBox ℓ d u ×ˢ dlBox ℓ d u, w p.1 p.2) = ∫ p : ℝ³ × ℝ³, w p.1 p.2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      by_cases h1 : p.1 ∈ dlBox ℓ d u
      · exact hvan p.1 p.2 (Or.inr (fun h2 => hp ⟨h1, h2⟩))
      · exact hvan p.1 p.2 (Or.inl h1))
  have h3 : (∫ p in acube ℓ ×ˢ acube ℓ, w p.1 p.2) = ∫ p : ℝ³ × ℝ³, w p.1 p.2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      by_cases h1 : p.1 ∈ acube ℓ
      · exact hvan p.1 p.2 (Or.inr (fun h2 => hp ⟨h1, Work.SmallBoxSliding.dlBox_subset_acube ℓ d u h2⟩))
      · exact hvan p.1 p.2 (Or.inl (fun h2 => h1 (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u h2))))
  rw [h1, h2, h3]

/-! ## 2. The target -/

theorem boxM1Info {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ K : ℝ, 0 < ε₀ ∧ 0 ≤ K ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : EuclideanSpace ℝ (Fin 3),
        0 ≤ Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        ∧ Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          ≤ K * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        ∧ Work.BoseFixB1S.boxM1 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
          ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h)) := by
  -- FS's regularity parameter is the fixed `M = mValue`
  have hmv : 1 ≤ Work.BoseBox.mValue := by decide
  -- the sharp one-body mass bound for `w_{1,B(u)}`, at the fixed regularity `mValue`
  obtain ⟨C, hC0, hCb⟩ := Work.BoseFixB1.WB.mass_upper (v := v) (h := h) (R0 := R)
    (M := Work.BoseBox.mValue) hv hvrad hv_supp hR hmv
  -- the diluteness threshold at which the two regime conditions hold
  obtain ⟨εreg, hεreg, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨εreg, C, hεreg, hC0, ?_⟩
  intro μ hAdm u
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hR16, hRχ⟩ := hreg μ (Work.BoseFixB1.adm_mu_pos hAdm) (Work.BoseFixB1.adm_dilute hAdm)
  -- rewrite the regularity parameter to the fixed value `mValue`
  have hMv : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = Work.BoseBox.mValue :=
    Work.BoseFixB1.M_eq_mValue μ (_root_.BoseGases.a v)
  rw [hMv]
  -- the vanishing of the localised kernels off the sliding box
  have hvan1 : ∀ x y : ℝ³,
      (x ∉ Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        ∨ y ∉ Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x y = 0 :=
    fun x y hxy => wSmallPair_eq_zero_of_notMem_dlBox hmv hℓ hd u hxy
  have hvan2 : ∀ x y : ℝ³,
      (x ∉ Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        ∨ y ∉ Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      Submission.BoseGases.wSmallPair Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Submission.BoseGases.g2 v h) x y = 0 :=
    fun x y hxy => wSmallPair_eq_zero_of_notMem_dlBox hmv hℓ hd u hxy
  -- integrability of the localised one-body kernel on the big box
  have hInt : IntegrableOn
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.wSmall1Pair h Work.BoseBox.mValue
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u p.1 p.2)
      (Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        ×ˢ Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :=
    Work.BoseFixB1.integrableOn_wSmallPair_cube (f := Submission.BoseGases.g0 v h)
      (Submission.BoseGases.g0_integrable (R := R) hR hv_supp h)
      (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h)
      hmv hℓ hd hR16 hRχ u
  refine ⟨?_, ?_, ?_⟩
  · rw [boxM1_eq_nested u hvan1]
    exact Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓ hd u
  · rw [boxM1_eq_nested u hvan1]
    exact hCb hℓ hd hR16 hRχ u
  · rw [boxM1_eq_acubePair u hvan1 hInt, boxM2_eq_acubePair u hvan2]
    exact Work.BoseFixB1.w1MassB_le_w2MassB_localised (v := v) (R0 := R)
      hv_supp hR hv hvrad hv1 h hmv hℓ hd hR16 hRχ u

end Work.BoseFixB1S
