import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxPairIntGenC2.EvenC2Factor
import Submission.Work.BoseFixB1.BoxPairIntGenC2.EvenC2Peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.BoxPairIntGenC2.boxPairDensSum_evenC2`

The summed box pair density `Work.BoseFixB1.boxPairDensSum` is an even function of the relative
coordinate: `boxPairDensSum (-u) = boxPairDensSum u`.

The route is per ordered pair `(i,j)` of distinct slots.  Writing

    `boxPairDens i j u = ∫_{z ∈ A} χ (z+u) χ z · F_{ij}(z+u, z)`

with `F` the peeled box pair fibre `Work.BoseFixB1.boxPairFibreFun`, the two box-projection
identities of `Work.BoseFixB1S.BoxPotOper` factor `F` as

    `F_{ij}(y,z) = 1_A(y)·1_A(z)·G_{ij}(y,z)`,

with `G = evenC2Free` the *indicator-free* fibre, which is continuous in `(y,z)`
(`EvenC2Cont`).  The two-slot peel `Submission.BoseGases.peel_pair_kernel` applied to the free
integrand at the two parametrisations of the slice (`EvenC2Peel`) shows that the weighted
integrals of the two free fibres agree for every continuous weight; taking the weight
`G_{ij}(y,z) − G_{ji}(z,y)` and using the continuity of the difference (upgrading an a.e.
vanishing to an identity on the cube) yields `G_{ij}(y,z) = G_{ji}(z,y)`, hence
`F_{ij}(y,z) = F_{ji}(z,y)`.  A translation of the `z`-integration in the whole-space form of
`boxPairDens` then gives `boxPairDens i j u = boxPairDens j i (-u)`; summing over the ordered
pairs and reindexing by the coordinate swap gives the claim.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.BoxPairIntGenC2

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Elementary topological and integrability facts for the cube -/

/-- The centred cube is contained in the closure of its interior. -/
lemma acube_subset_closure_interior {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Submission.BoseGases.acube ℓ ⊆ closure (interior (Submission.BoseGases.acube ℓ)) := by
  intro y hy
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hyabs : ∀ m : Fin 3, |y m| ≤ ℓ / 2 := fun m => by
    have h := hy m
    rw [Set.mem_Icc] at h
    exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
  have hopen : IsOpen {z : E3 | ∀ m : Fin 3, |z m| < ℓ / 2} := by
    have h : {z : E3 | ∀ m : Fin 3, |z m| < ℓ / 2}
        = ⋂ m : Fin 3, {z : E3 | |z m| < ℓ / 2} := by
      ext z; simp
    rw [h]
    exact isOpen_iInter_of_finite fun m => isOpen_lt (by fun_prop) continuous_const
  have hsub : {z : E3 | ∀ m : Fin 3, |z m| < ℓ / 2} ⊆ Submission.BoseGases.acube ℓ := by
    intro z hz m
    rw [Set.mem_Icc]
    have h := abs_lt.mp (hz m)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  set t : ℝ := min (1 / 2) (ε / (2 * (‖y‖ + 1))) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨(1 - t) • y, ?_, ?_⟩
  · refine interior_maximal hsub hopen fun m => ?_
    rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (by linarith : (0:ℝ) < 1 - t)]
    have h1 : (1 - t) * |y m| ≤ (1 - t) * (ℓ / 2) :=
      mul_le_mul_of_nonneg_left (hyabs m) (by linarith)
    have h2 : (1 - t) * (ℓ / 2) < 1 * (ℓ / 2) :=
      mul_lt_mul_of_pos_right (by linarith) (by linarith)
    linarith
  · have hsub2 : y - (1 - t) • y = t • y := by
      have h1 : (1 : ℝ) • y - (1 - t) • y = (1 - (1 - t)) • y := (sub_smul 1 (1 - t) y).symm
      rw [one_smul] at h1
      rw [h1]
      congr 1
      ring
    rw [dist_eq_norm, hsub2, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    have hle : t ≤ ε / (2 * (‖y‖ + 1)) := min_le_right _ _
    have hpos : (0:ℝ) < 2 * (‖y‖ + 1) := by positivity
    have h3 : t * (2 * (‖y‖ + 1)) ≤ ε := by
      calc t * (2 * (‖y‖ + 1)) ≤ ε / (2 * (‖y‖ + 1)) * (2 * (‖y‖ + 1)) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = ε := by field_simp
    nlinarith [norm_nonneg y]

/-- A continuous function on the square of the cube is integrable for the product of the
restricted measures. -/
lemma integrableOn_cube_prod {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 × E3 → ℝ} (hf : Continuous f) :
    Integrable f (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
      ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]
  exact ContinuousOn.integrableOn_compact ((Submission.BoseGases.acube_compact hℓ).prod
    (Submission.BoseGases.acube_compact hℓ)) hf.continuousOn

/-- The same for the measure restricted to the square of the cube. -/
lemma integrableOn_cube_sq {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 × E3 → ℝ} (hf : Continuous f) :
    Integrable f ((volume : Measure (E3 × E3)).restrict
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :=
  ContinuousOn.integrableOn_compact ((Submission.BoseGases.acube_compact hℓ).prod
    (Submission.BoseGases.acube_compact hℓ)) hf.continuousOn

/-- Set and iterated integrals of a continuous function over the square of the cube agree. -/
lemma cube_setIntegral_eq_iterated {ℓ : ℝ} (hℓ : 0 < ℓ) {f : E3 → E3 → ℝ}
    (hf : Continuous (Function.uncurry f)) :
    (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, f p.1 p.2)
      = ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ, f a b := by
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict]
  exact MeasureTheory.integral_prod (fun p : E3 × E3 => f p.1 p.2)
    (integrableOn_cube_prod hℓ hf)

/-! ## The symmetry of the indicator-free fibre -/

/-- **The free fibre is symmetric under the interchange of the two parametrisations.** -/
theorem evenC2Free_symm {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) :
    ∀ y ∈ Submission.BoseGases.acube ℓ, ∀ z ∈ Submission.BoseGases.acube ℓ,
      evenC2Free volA ℓ A Φ i j' y z
        = evenC2Free volA ℓ A Φ (i.succAbove j')
            (Submission.BoseGases.sucAboveInv (i.succAbove j') i (Fin.ne_succAbove i j').symm)
            z y := by
  intro y hy z hz
  have hij' : i.succAbove j' ≠ i := (Fin.ne_succAbove i j').symm
  set j'' := Submission.BoseGases.sucAboveInv (i.succAbove j') i hij' with hj''
  have hF1c : Continuous (fun q : E3 × E3 => evenC2Free volA ℓ A Φ i j' q.1 q.2) :=
    continuous_evenC2Free hA hℓ hAc hΦc i j'
  have hF2c : Continuous (fun q : E3 × E3 => evenC2Free volA ℓ A Φ (i.succAbove j') j'' q.1 q.2) :=
    continuous_evenC2Free hA hℓ hAc hΦc (i.succAbove j') j''
  set G : E3 → E3 → ℝ := fun a b =>
    evenC2Free volA ℓ A Φ i j' a b - evenC2Free volA ℓ A Φ (i.succAbove j') j'' b a with hG
  have hGc : Continuous (fun p : E3 × E3 => G p.1 p.2) := by
    have heq : (fun p : E3 × E3 => G p.1 p.2)
        = fun p => evenC2Free volA ℓ A Φ i j' p.1 p.2
            - evenC2Free volA ℓ A Φ (i.succAbove j') j'' p.2 p.1 := by
      funext p
      rw [hG]
    rw [heq]
    exact hF1c.sub (hF2c.comp continuous_swap)
  -- the peel identity with the weight `G`
  have hpeel : (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
        G a b * evenC2Free volA ℓ A Φ i j' a b)
      = ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
          G b a * evenC2Free volA ℓ A Φ (i.succAbove j') j'' a b :=
    evenC2Free_peel (volA := volA) hA hℓ hAc hΦc i j' G hGc
  -- the Fubini swap converting the right-hand side
  have hF2sw : Continuous (fun q : E3 × E3 =>
      G q.2 q.1 * evenC2Free volA ℓ A Φ (i.succAbove j') j'' q.1 q.2) :=
    (hGc.comp continuous_swap).mul hF2c
  have hsw : (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
        G b a * evenC2Free volA ℓ A Φ (i.succAbove j') j'' a b)
      = ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
          G a b * evenC2Free volA ℓ A Φ (i.succAbove j') j'' b a := by
    calc _ = ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
            (fun p q : E3 => G q p * evenC2Free volA ℓ A Φ (i.succAbove j') j'' p q) a b := rfl
      _ = ∫ b in Submission.BoseGases.acube ℓ, ∫ a in Submission.BoseGases.acube ℓ,
            (fun p q : E3 => G q p * evenC2Free volA ℓ A Φ (i.succAbove j') j'' p q) a b :=
          MeasureTheory.integral_integral_swap (integrableOn_cube_prod hℓ hF2sw)
      _ = ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
            (fun p q : E3 => G q p * evenC2Free volA ℓ A Φ (i.succAbove j') j'' p q) b a := rfl
      _ = ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
            G a b * evenC2Free volA ℓ A Φ (i.succAbove j') j'' b a := rfl
  have hgoal : (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
        G a b * evenC2Free volA ℓ A Φ i j' a b)
      = ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
          G a b * evenC2Free volA ℓ A Φ (i.succAbove j') j'' b a := hpeel.trans hsw
  -- the difference of the two fibres is the square of `G`, so the square has vanishing integral
  have hcont1 : Continuous (fun p : E3 × E3 => (G p.1 p.2) ^ 2) := hGc.pow 2
  have hcont2 : Continuous (fun p : E3 × E3 =>
      G p.1 p.2 * evenC2Free volA ℓ A Φ (i.succAbove j') j'' p.2 p.1) :=
    hGc.mul (hF2c.comp continuous_swap)
  have hcontA : Continuous (fun p : E3 × E3 =>
      G p.1 p.2 * evenC2Free volA ℓ A Φ i j' p.1 p.2) := hGc.mul hF1c
  have hiter1 : (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
        G a b * evenC2Free volA ℓ A Φ i j' a b)
      = ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
          G p.1 p.2 * evenC2Free volA ℓ A Φ i j' p.1 p.2 :=
    (cube_setIntegral_eq_iterated (f := fun a b => G a b * evenC2Free volA ℓ A Φ i j' a b)
      hℓ hcontA).symm
  have hiter2 : (∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
        G a b * evenC2Free volA ℓ A Φ (i.succAbove j') j'' b a)
      = ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
          G p.1 p.2 * evenC2Free volA ℓ A Φ (i.succAbove j') j'' p.2 p.1 :=
    (cube_setIntegral_eq_iterated (f := fun a b => G a b
      * evenC2Free volA ℓ A Φ (i.succAbove j') j'' b a) hℓ hcont2).symm
  have hprod : (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
        G p.1 p.2 * evenC2Free volA ℓ A Φ i j' p.1 p.2)
      = ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
          G p.1 p.2 * evenC2Free volA ℓ A Φ (i.succAbove j') j'' p.2 p.1 := by
    rw [← hiter1, ← hiter2]
    exact hgoal
  have hpoint : ∀ p ∈ Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
      G p.1 p.2 * evenC2Free volA ℓ A Φ i j' p.1 p.2
        = (G p.1 p.2) ^ 2
          + G p.1 p.2 * evenC2Free volA ℓ A Φ (i.succAbove j') j'' p.2 p.1 := by
    intro p hp
    rw [hG]
    ring
  have hcongr : (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
        G p.1 p.2 * evenC2Free volA ℓ A Φ i j' p.1 p.2)
      = ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
          ((G p.1 p.2) ^ 2 + G p.1 p.2
            * evenC2Free volA ℓ A Φ (i.succAbove j') j'' p.2 p.1) :=
    setIntegral_congr_fun ((Submission.BoseGases.acube_measurable ℓ).prod
      (Submission.BoseGases.acube_measurable ℓ)) hpoint
  have hsum : (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
        ((G p.1 p.2) ^ 2 + G p.1 p.2
          * evenC2Free volA ℓ A Φ (i.succAbove j') j'' p.2 p.1))
      = (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ, (G p.1 p.2) ^ 2)
        + ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
            G p.1 p.2 * evenC2Free volA ℓ A Φ (i.succAbove j') j'' p.2 p.1 :=
    MeasureTheory.integral_add (integrableOn_cube_sq hℓ hcont1)
      (integrableOn_cube_sq hℓ hcont2)
  have hsq : (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
      (G p.1 p.2) ^ 2) = 0 := by
    have h1 : (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
          (G p.1 p.2) ^ 2)
        + (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
            G p.1 p.2 * evenC2Free volA ℓ A Φ (i.succAbove j') j'' p.2 p.1)
        = ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
            G p.1 p.2 * evenC2Free volA ℓ A Φ (i.succAbove j') j'' p.2 p.1 := by
      rw [← hsum, ← hcongr, hprod]
    linarith
  have hae : (fun p : E3 × E3 => (G p.1 p.2) ^ 2)
      =ᵐ[volume.restrict (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg _)
      (integrableOn_cube_sq hℓ hcont1)).mp hsq
  have hU : Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ
      ⊆ closure (interior (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) := by
    rw [interior_prod_eq, closure_prod_eq]
    exact Set.prod_mono (acube_subset_closure_interior hℓ) (acube_subset_closure_interior hℓ)
  have hEq := MeasureTheory.Measure.eqOn_of_ae_eq (μ := (volume : Measure (E3 × E3))) hae
    hcont1.continuousOn continuousOn_const hU
  have hzero : G y z = 0 := by
    have := hEq (Set.mk_mem_prod hy hz)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hfibre : evenC2Free volA ℓ A Φ i j' y z
      = evenC2Free volA ℓ A Φ (i.succAbove j') j'' z y := by
    have h := hzero
    rw [hG] at h
    linarith
  rw [show j'' = Submission.BoseGases.sucAboveInv (i.succAbove j') i
      (Fin.ne_succAbove i j').symm from by rw [hj'']] at hfibre
  exact hfibre

/-! ## The peeled fibre depends only on the two slots -/

/-- The peeled fibre depends only on the two *slots*, not on the enumeration of the rest. -/
lemma boxPairFibreFun_slot_congr {N : ℕ} (volA ℓ : ℝ) {A : Set E3}
    (Φ : Submission.BoseGases.X (N + 2) → ℝ) {a a' : Fin (N + 2)} {β β' : Fin (N + 1)}
    (h1 : a = a') (h2 : a.succAbove β = a'.succAbove β') (y z : E3) :
    Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ a (a.succAbove β) y z
      = Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ a' (a'.succAbove β') y z := by
  subst h1
  exact congrArg (fun X => Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ a X y z) h2

/-- The fibre at the slots `(a,b)` is the fibre at the parametrisation `(a, a.succAbove β)`. -/
lemma boxPairFibreFun_eq_succAbove {N : ℕ} (volA ℓ : ℝ) {A : Set E3}
    (Φ : Submission.BoseGases.X (N + 2) → ℝ) {a b : Fin (N + 2)}
    {β : Fin (N + 1)} (hβ : a.succAbove β = b) (y z : E3) :
    Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ a b y z
      = Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ a (a.succAbove β) y z :=
  (congrArg (fun X => Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ a X y z) hβ).symm

/-! ## The symmetry of the peeled fibre -/

/-- **The peeled fibre is symmetric under the interchange of the two slots** (in the
`(i, i.succAbove j')` parametrisation). -/
theorem boxPairFibreFun_swap_succAbove {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (volume A).toReal) (hvolpos : 0 < volA)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    (i : Fin (N + 2)) (j' : Fin (N + 1)) {y z : E3}
    (hy : y ∈ Submission.BoseGases.acube ℓ) (hz : z ∈ Submission.BoseGases.acube ℓ) :
    Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i (i.succAbove j') y z
      = Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ (i.succAbove j')
          ((i.succAbove j').succAbove (Submission.BoseGases.sucAboveInv (i.succAbove j') i
            (Fin.ne_succAbove i j').symm)) z y := by
  have h1 := evenC2_factorization hA hℓ hAc hvolA hvolpos hΦc i j' hy hz
  have h3 := evenC2_factorization hA hℓ hAc hvolA hvolpos hΦc (i.succAbove j')
    (Submission.BoseGases.sucAboveInv (i.succAbove j') i (Fin.ne_succAbove i j').symm) hz hy
  rw [h1, h3, evenC2Free_symm hA hℓ hAc hΦc i j' y hy z hz]
  ring

/-- **The peeled fibre is symmetric under the interchange of the two slots.** -/
theorem boxPairFibreFun_swap {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (volume A).toReal) (hvolpos : 0 < volA)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    {i j : Fin (N + 2)} (hij : i ≠ j) {y z : E3}
    (hy : y ∈ Submission.BoseGases.acube ℓ) (hz : z ∈ Submission.BoseGases.acube ℓ) :
    Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j y z
      = Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ j i z y := by
  set j' := Submission.BoseGases.sucAboveInv i j hij with hj'
  have hjj' : i.succAbove j' = j := Submission.BoseGases.succAbove_sucAboveInv i j hij
  have hij' : j ≠ i := hij.symm
  set j₂ := Submission.BoseGases.sucAboveInv j i hij' with hj₂
  have hjj₂ : j.succAbove j₂ = i := Submission.BoseGases.succAbove_sucAboveInv j i hij'
  have hX : (i.succAbove j').succAbove (Submission.BoseGases.sucAboveInv (i.succAbove j') i
      (Fin.ne_succAbove i j').symm) = j.succAbove j₂ :=
    (Submission.BoseGases.succAbove_sucAboveInv (i.succAbove j') i
      (Fin.ne_succAbove i j').symm).trans hjj₂.symm
  calc Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j y z
      = Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i (i.succAbove j') y z :=
        boxPairFibreFun_eq_succAbove volA ℓ Φ hjj' y z
    _ = Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ (i.succAbove j')
          ((i.succAbove j').succAbove (Submission.BoseGases.sucAboveInv (i.succAbove j') i
            (Fin.ne_succAbove i j').symm)) z y :=
        boxPairFibreFun_swap_succAbove hA hℓ hAc hvolA hvolpos hΦc i j' hy hz
    _ = Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ j (j.succAbove j₂) z y :=
        boxPairFibreFun_slot_congr volA ℓ Φ hjj' hX z y
    _ = Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ j i z y :=
        (boxPairFibreFun_eq_succAbove volA ℓ Φ hjj₂ z y).symm

/-! ## The per-pair identity -/

/-- **The box pair density of the pair `(i,j)` at `u` is that of the pair `(j,i)` at `-u`.** -/
theorem boxPairDens_swap {N : ℕ} {ℓ volA : ℝ} {A : Set E3}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (volume A).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Φ : Submission.BoseGases.X (N + 2) → ℝ} (hΦc : Continuous Φ)
    {i j : Fin (N + 2)} (hij : i ≠ j) (u : E3) :
    Work.BoseFixB1.boxPairDens volA ℓ A χ Φ i j u
      = Work.BoseFixB1.boxPairDens volA ℓ A χ Φ j i (-u) := by
  rw [Work.BoseFixB1.boxPairDens, Work.BoseFixB1.boxPairDens]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (f := fun z : E3 => χ (z + u) * χ z
      * Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j (z + u) z) (fun z hz => by
        rw [hχsupp z hz]; ring)]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (f := fun z : E3 => χ (z + -u) * χ z
      * Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ j i (z + -u) z) (fun z hz => by
        rw [hχsupp z hz]; ring)]
  rw [← MeasureTheory.integral_add_right_eq_self
    (f := fun z : E3 => χ (z + -u) * χ z
      * Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ j i (z + -u) z) u]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show χ (z + u) * χ z * Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j (z + u) z
      = χ (z + u + -u) * χ (z + u)
        * Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ j i (z + u + -u) (z + u)
  have hzu : z + u + -u = z := by abel
  rw [hzu]
  by_cases h0 : χ z * χ (z + u) = 0
  · rw [show χ (z + u) * χ z
        * Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ i j (z + u) z = 0 from by
          rw [mul_comm (χ (z + u)) (χ z), h0, zero_mul],
      show χ z * χ (z + u)
        * Work.BoseFixB1.boxPairFibreFun volA ℓ A Φ j i z (z + u) = 0 from by
          rw [h0, zero_mul]]
  · have hz : z ∈ A := by
      by_contra hzA
      exact h0 (by rw [hχsupp z hzA]; ring)
    have hzu' : z + u ∈ A := by
      by_contra hzuA
      exact h0 (by rw [hχsupp (z + u) hzuA]; ring)
    rw [boxPairFibreFun_swap hA hℓ hAc hvolA hvolpos hΦc hij (hAc hzu') (hAc hz)]
    ring

/-! ## The assembly -/

/-- The coordinate-swap reindexing of a `pairSet`-sum (real version). -/
lemma pairSet_swap_sum {N : ℕ} (g : Fin N × Fin N → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, g (p.2, p.1))
      = ∑ p ∈ Submission.BoseGases.pairSet N, g p := by
  refine Finset.sum_bij' (i := fun p _ => (p.2, p.1)) (j := fun p _ => (p.2, p.1))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp [Submission.BoseGases.pairSet] at hp ⊢
    intro h
    exact hp (by simpa using h.symm)
  · intro p hp
    simp [Submission.BoseGases.pairSet] at hp ⊢
    intro h
    exact hp (by simpa using h.symm)
  · intro p hp; rfl
  · intro p hp; rfl
  · intro p hp; rfl

theorem boxPairDensSum_evenC2 {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hvolpos : 0 < volA)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ)
    (hχsupp : ∀ z, z ∉ A → χ z = 0)
    {Ψ : Submission.BoseGases.X (N + 2) → ℝ} (hΨ : Continuous Ψ) :
    ∀ u, Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ (-u)
        = Work.BoseFixB1.boxPairDensSum volA ℓ A χ Ψ u := by
  intro u
  have hterm : ∀ p ∈ Submission.BoseGases.pairSet (N + 2),
      Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ p.1 p.2 (-u)
        = Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ p.2 p.1 u := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by simpa [Submission.BoseGases.pairSet] using hp
    have h := boxPairDens_swap hA hℓ hAc hvolA hvolpos hχsupp hΨ (i := p.1) (j := p.2) hpne (-u)
    simpa using h
  rw [Work.BoseFixB1.boxPairDensSum, Work.BoseFixB1.boxPairDensSum]
  rw [Finset.sum_congr rfl hterm]
  exact pairSet_swap_sum (N := N + 2)
    (fun p => Work.BoseFixB1.boxPairDens volA ℓ A χ Ψ p.1 p.2 u)

end Work.BoseFixB1.BoxPairIntGenC2
