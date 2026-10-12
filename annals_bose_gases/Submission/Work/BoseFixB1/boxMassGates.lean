import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixB1.w1MassB_le_w2MassB_localised
import Submission.Work.BoseFixB1.w1MassB_nonneg
import Submission.Work.BoseFixB1S.BoxQWords
import Submission.Work.SlotWord.chiSmallB_support_mem_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxMassGates` — the four per-box mass facts

`boxM1 ℓ (dlBox ℓ d u) w₁ = ∫_{B(u)} ∫_{Λ} w₁` is the *localised* one-body mass of the
sliding small box `B(u) = dlBox ℓ d u`, `boxM2 |B(u)| (dlBox ℓ d u) w₂` the localised
pair mass, and `Work.BoseFixB1.w1MassB h M ℓ d u = ∫∫ w_{1,B(u)}` is the *global* nested
integral of the same localised kernel.  Because every localised kernel is supported in
`B(u)` in each variable (`chiSmallB M ℓ d u z ≠ 0 → z ∈ dlBox ℓ d u`), all these objects
coincide, and the four gates of the target become

* `boxM1 … = w1MassB …`            (the localised mass is the global mass),
* `boxM2 … = ∫_{acube ℓ × acube ℓ} w₂` (Fubini + support),
* `0 ≤ boxM1 …`                     (`Work.BoseFixB1.w1MassB_nonneg`, FS's `∬w_{1,B} ≥ 0`),
* `boxM1 … ≤ boxM2 …`               (`Work.BoseFixB1.w1MassB_le_w2MassB_localised`, FS `lm:w2>w1`).

The transport lemmas below are the same measure-theoretic bookkeeping as in
`Submission/Work/BoseFixB1S/boxM1Info.lean`, restated here (with `f`-generic support
vanishing) so that this file depends only on fully closed modules.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real

namespace Work.BoseFixB1

-- (`ℝ³` is the *global* corpus notation `EuclideanSpace ℝ (Fin 3)` of
-- `Submission/Work/BoseKinLoc/Defs.lean`, in the import cone of this file; do not
-- redeclare it locally, the token would become ambiguous.)

set_option linter.unusedVariables false

/-! ## 1. Vanishing of the localised kernels off the sliding box -/

/-- `chiSmallB M ℓ d u z ≠ 0` forces `z ∈ dlBox ℓ d u` (the support of the sliding
small-box cutoff). -/
lemma chiSmallB_eq_zero_of_notMem_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : ℝ³) {x : ℝ³} (hx : x ∉ Submission.BoseGases.dlBox ℓ d u) :
    Submission.BoseGases.chiSmallB M ℓ d u x = 0 := by
  by_contra hne
  exact hx (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hne)

/-- Every localised kernel `wSmallPair M ℓ d u f` vanishes as soon as one argument
leaves the sliding box. -/
lemma wSmallPair_eq_zero_of_notMem_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : ℝ³) {f : ℝ³ → ℝ} {x y : ℝ³}
    (h : x ∉ Submission.BoseGases.dlBox ℓ d u ∨ y ∉ Submission.BoseGases.dlBox ℓ d u) :
    Submission.BoseGases.wSmallPair M ℓ d u f x y = 0 := by
  rcases h with hx | hy
  · rw [Submission.BoseGases.wSmallPair,
      chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd u hx, zero_mul, zero_mul]
  · rw [Submission.BoseGases.wSmallPair,
      chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd u hy, mul_zero]

/-! ## 2. Transport of `boxM1` / `boxM2` to the global and big-box forms -/

/-- `boxM1` at a kernel supported in the sliding box is the *global* nested integral. -/
lemma boxM1_eq_nested {ℓ d : ℝ} (u : ℝ³) {w : ℝ³ → ℝ³ → ℝ}
    (hvan : ∀ x y : ℝ³, (x ∉ Submission.BoseGases.dlBox ℓ d u
      ∨ y ∉ Submission.BoseGases.dlBox ℓ d u) → w x y = 0) :
    Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u) w
      = ∫ x : ℝ³, ∫ y : ℝ³, w x y := by
  have h1 : Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u) w
      = ∫ z in Submission.BoseGases.dlBox ℓ d u, ∫ y : ℝ³, w z y := by
    rw [Work.BoseFixB1S.boxM1]
    refine setIntegral_congr_fun (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
      (fun z _ => ?_)
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => hvan z y (Or.inr (fun hmem =>
        hy (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u hmem))))
  have h2 : (∫ z in Submission.BoseGases.dlBox ℓ d u, ∫ y : ℝ³, w z y)
      = ∫ z : ℝ³, ∫ y : ℝ³, w z y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      have hz0 : (fun y : ℝ³ => w z y) = fun _ => (0 : ℝ) :=
        funext (fun y => hvan z y (Or.inl hz))
      rw [hz0, integral_zero])
  rw [h1, h2]

/-- The pair integral over `acube ℓ × acube ℓ` of a kernel supported in the sliding box
equals the global nested integral (Fubini). -/
lemma acubePair_eq_nested {ℓ d : ℝ} (u : ℝ³) {w : ℝ³ → ℝ³ → ℝ}
    (hvan : ∀ x y : ℝ³, (x ∉ Submission.BoseGases.dlBox ℓ d u
      ∨ y ∉ Submission.BoseGases.dlBox ℓ d u) → w x y = 0)
    (hInt : IntegrableOn (fun p : ℝ³ × ℝ³ => w p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, w p.1 p.2)
      = ∫ x : ℝ³, ∫ y : ℝ³, w x y := by
  have h1 : (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
        w p.1 p.2)
      = ∫ x in Submission.BoseGases.acube ℓ, ∫ y in Submission.BoseGases.acube ℓ, w x y :=
    MeasureTheory.setIntegral_prod (fun p : ℝ³ × ℝ³ => w p.1 p.2) hInt
  have h2 : (∫ x in Submission.BoseGases.acube ℓ,
        ∫ y in Submission.BoseGases.acube ℓ, w x y)
      = ∫ x in Submission.BoseGases.acube ℓ, ∫ y : ℝ³, w x y := by
    refine setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) (fun x _ => ?_)
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => hvan x y (Or.inr (fun hmem =>
        hy (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u hmem))))
  have h3 : (∫ x in Submission.BoseGases.acube ℓ, ∫ y : ℝ³, w x y)
      = ∫ x : ℝ³, ∫ y : ℝ³, w x y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hx0 : (fun y : ℝ³ => w x y) = fun _ => (0 : ℝ) :=
        funext (fun y => hvan x y (Or.inl (fun hmem =>
          hx (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u hmem))))
      rw [hx0, integral_zero])
  rw [h1, h2, h3]

/-- `boxM1` at a kernel supported in the sliding box is the pair integral over the big box. -/
lemma boxM1_eq_acubePair {ℓ d : ℝ} (u : ℝ³) {w : ℝ³ → ℝ³ → ℝ}
    (hvan : ∀ x y : ℝ³, (x ∉ Submission.BoseGases.dlBox ℓ d u
      ∨ y ∉ Submission.BoseGases.dlBox ℓ d u) → w x y = 0)
    (hInt : IntegrableOn (fun p : ℝ³ × ℝ³ => w p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :
    Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u) w
      = ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, w p.1 p.2 :=
  (boxM1_eq_nested u hvan).trans (acubePair_eq_nested u hvan hInt).symm

/-- `boxM2` at a kernel supported in the sliding box is the pair integral over the big box. -/
lemma boxM2_eq_acubePair {ℓ d : ℝ} (u : ℝ³) {volA : ℝ} {w : ℝ³ → ℝ³ → ℝ}
    (hvan : ∀ x y : ℝ³, (x ∉ Submission.BoseGases.dlBox ℓ d u
      ∨ y ∉ Submission.BoseGases.dlBox ℓ d u) → w x y = 0) :
    Work.BoseFixB1S.boxM2 volA (Submission.BoseGases.dlBox ℓ d u) w
      = ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, w p.1 p.2 := by
  have h1 : Work.BoseFixB1S.boxM2 volA (Submission.BoseGases.dlBox ℓ d u) w
      = ∫ p in Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u,
          w p.1 p.2 := rfl
  have h2 : (∫ p in Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u,
        w p.1 p.2) = ∫ p : ℝ³ × ℝ³, w p.1 p.2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      by_cases h1 : p.1 ∈ Submission.BoseGases.dlBox ℓ d u
      · exact hvan p.1 p.2 (Or.inr (fun h2 => hp ⟨h1, h2⟩))
      · exact hvan p.1 p.2 (Or.inl h1))
  have h3 : (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, w p.1 p.2)
      = ∫ p : ℝ³ × ℝ³, w p.1 p.2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      by_cases h1 : p.1 ∈ Submission.BoseGases.acube ℓ
      · exact hvan p.1 p.2 (Or.inr (fun h2 =>
          hp ⟨h1, Work.SmallBoxSliding.dlBox_subset_acube ℓ d u h2⟩))
      · exact hvan p.1 p.2 (Or.inl (fun h2 =>
          h1 (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u h2))))
  rw [h1, h2, h3]

/-! ## 3. The target -/

theorem boxMassGates {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
      = Work.BoseFixB1.w1MassB h M ℓ d u
    ∧ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
      = ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2
    ∧ 0 ≤ Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
    ∧ Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
      ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) := by
  -- the one-body kernel vanishes off the sliding box
  have hvan1 : ∀ x y : ℝ³,
      (x ∉ Submission.BoseGases.dlBox ℓ d u ∨ y ∉ Submission.BoseGases.dlBox ℓ d u) →
      Submission.BoseGases.wSmall1Pair h M ℓ d u x y = 0 :=
    fun x y hxy => wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy
  -- the two-body kernel vanishes off the sliding box
  have hvan2 : ∀ x y : ℝ³,
      (x ∉ Submission.BoseGases.dlBox ℓ d u ∨ y ∉ Submission.BoseGases.dlBox ℓ d u) →
      Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) x y = 0 :=
    fun x y hxy => wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u hxy
  -- integrability of the localised one-body kernel on the big box
  have hInt : IntegrableOn
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :=
    integrableOn_wSmallPair_cube (f := Submission.BoseGases.g0 v h)
      (Submission.BoseGases.g0_integrable (R := R0) hR0 hv_supp h)
      (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h)
      hM hℓ hd hR hRχ u
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [boxM1_eq_nested u hvan1]
    rfl
  · exact boxM2_eq_acubePair u hvan2
  · rw [boxM1_eq_nested u hvan1]
    exact w1MassB_nonneg (v := v) h hv hvrad hR0 hv_supp hℓ hd u
  · rw [boxM1_eq_acubePair u hvan1 hInt, boxM2_eq_acubePair u hvan2]
    exact w1MassB_le_w2MassB_localised (v := v) (R0 := R0)
      hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u

end Work.BoseFixB1
