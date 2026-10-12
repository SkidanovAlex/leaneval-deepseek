import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Analysis.BoseBand.NeuBilIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.neuWord_fibre_offdiag`

The off-diagonal vanishing of FS `eq:DefT`'s first kinetic term (`neuWord`) between two
different joint sectors `E_S`, `E_T` (`S ≠ T`, both containing the slot `j`):

`∫_{abox n ℓ} 1_{Λ}(x_j)·[neuWord(fibre_j(E_SΦ + E_TΦ)) − neuWord(fibre_j(E_SΦ − E_TΦ))] = 0`.

The content is the FS §6 "band" mechanism: some slot `i ∈ S △ T` (`i ≠ j`) carries the mean
projection `P_i` on one side and the mean-free projection `Q_i` on the other, so the slot-`j`
kinetic matrix element between the two sectors vanishes.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators ENNReal

namespace Work.Analysis.BoseBand

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Submission.BoseGases

/-- `z ↦ Function.update x j z` is continuous in `z` (the other coordinates are frozen). -/
lemma continuous_update_const' {n : ℕ} (j : Fin n) (x : Submission.BoseGases.X n) :
    Continuous fun z : EuclideanSpace ℝ (Fin 3) => Function.update x j z := by
  have h2 : Continuous fun p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3) =>
      Function.update p.1 j p.2 := continuous_update j
  exact h2.comp (continuous_const.prodMk continuous_id)

/-- `z ↦ Ψ(x with xᵢ = z)` is smooth when `Ψ` is. -/
lemma contDiff_fibre_update {n : ℕ} (j : Fin n) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (x : Submission.BoseGases.X n) :
    ContDiff ℝ (⊤ : ℕ∞) fun z : EuclideanSpace ℝ (Fin 3) => Ψ (Function.update x j z) :=
  hΨ.comp (contDiff_update (⊤ : ℕ∞) x j)

/-- The fibre is additive in the state. -/
lemma fibre_add_fun {n : ℕ} (j : Fin n) (Ψ₁ Ψ₂ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    (Work.BoseKinLoc.fibre n j (fun y => Ψ₁ y + Ψ₂ y) x)
      = fun z => Work.BoseKinLoc.fibre n j Ψ₁ x z + Work.BoseKinLoc.fibre n j Ψ₂ x z := rfl

/-- The fibre is additive (subtraction). -/
lemma fibre_sub_fun {n : ℕ} (j : Fin n) (Ψ₁ Ψ₂ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    (Work.BoseKinLoc.fibre n j (fun y => Ψ₁ y - Ψ₂ y) x)
      = fun z => Work.BoseKinLoc.fibre n j Ψ₁ x z - Work.BoseKinLoc.fibre n j Ψ₂ x z := rfl

/-- The box mean is additive. -/
lemma bsMean_add'' {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Work.BSKinetic.bsMean ℓ u (fun z => f z + g z)
      = Work.BSKinetic.bsMean ℓ u f + Work.BSKinetic.bsMean ℓ u g := by
  have hfI : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => f (ℓ • u + z))
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    Submission.BoseGases.integrableOn_acube_of_continuous hℓ (hf.comp (by fun_prop))
  have hgI : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => g (ℓ • u + z))
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    Submission.BoseGases.integrableOn_acube_of_continuous hℓ (hg.comp (by fun_prop))
  show (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ, (f (ℓ • u + z) + g (ℓ • u + z))
      = (ℓ ^ 3)⁻¹ * (∫ z in Submission.BoseGases.acube ℓ, f (ℓ • u + z))
        + (ℓ ^ 3)⁻¹ * (∫ z in Submission.BoseGases.acube ℓ, g (ℓ • u + z))
  rw [MeasureTheory.integral_add hfI hgI]
  ring

/-- The box mean is additive (subtraction). -/
lemma bsMean_sub'' {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Work.BSKinetic.bsMean ℓ u (fun z => f z - g z)
      = Work.BSKinetic.bsMean ℓ u f - Work.BSKinetic.bsMean ℓ u g := by
  have hfI : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => f (ℓ • u + z))
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    Submission.BoseGases.integrableOn_acube_of_continuous hℓ (hf.comp (by fun_prop))
  have hgI : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => g (ℓ • u + z))
      (volume.restrict (Submission.BoseGases.acube ℓ)) :=
    Submission.BoseGases.integrableOn_acube_of_continuous hℓ (hg.comp (by fun_prop))
  show (ℓ ^ 3)⁻¹ * ∫ z in Submission.BoseGases.acube ℓ, (f (ℓ • u + z) - g (ℓ • u + z))
      = (ℓ ^ 3)⁻¹ * (∫ z in Submission.BoseGases.acube ℓ, f (ℓ • u + z))
        - (ℓ ^ 3)⁻¹ * (∫ z in Submission.BoseGases.acube ℓ, g (ℓ • u + z))
  rw [MeasureTheory.integral_sub hfI hgI]
  ring

/-- The box mean-free projection is additive. -/
lemma Qfree_add' {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Work.BoseKinLoc.Qfree ℓ u (fun z => f z + g z)
      = fun z => Work.BoseKinLoc.Qfree ℓ u f z + Work.BoseKinLoc.Qfree ℓ u g z := by
  funext z
  simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, bsMean_add'' hℓ u hf hg]
  ring

/-- The box mean-free projection is additive (subtraction). -/
lemma Qfree_sub' {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Work.BoseKinLoc.Qfree ℓ u (fun z => f z - g z)
      = fun z => Work.BoseKinLoc.Qfree ℓ u f z - Work.BoseKinLoc.Qfree ℓ u g z := by
  funext z
  simp only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, bsMean_sub'' hℓ u hf hg]
  ring

/-- `Qfree` commutes with taking a fibre (no smoothness needed). -/
lemma Qfree_fibre_eq' {ℓ : ℝ} {n : ℕ} (j : Fin n) (Ψ : Submission.BoseGases.X n → ℝ)
    (x : Submission.BoseGases.X n) :
    Work.BoseKinLoc.Qfree ℓ 0 (Work.BoseKinLoc.fibre n j Ψ x)
      = Work.BoseKinLoc.fibre n j (Submission.BoseGases.aQ ℓ j Ψ) x := by
  funext z
  simp only [Work.BoseKinLoc.Qfree, Work.BoseKinLoc.fibre, Work.BSKinetic.bsQ,
    Work.BSKinetic.bsMean, Submission.BoseGases.aQ, Submission.BoseGases.aP,
    Function.update_idem, smul_zero, zero_add, one_div]

/-- `aQ` is the identity on slot-`j` mean-free states. -/
lemma aQ_eq_self_of_aP_eq_zero {n : ℕ} {ℓ : ℝ} (j : Fin n) {Ψ : Submission.BoseGases.X n → ℝ}
    (h : Submission.BoseGases.aP ℓ j Ψ = 0) : Submission.BoseGases.aQ ℓ j Ψ = Ψ := by
  funext x
  simp only [Submission.BoseGases.aQ, h, Pi.zero_apply, sub_zero]

/-- `aQ` is additive (pointwise form). -/
lemma aQ_add_apply {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) {Ψ Ψ' : Submission.BoseGases.X n → ℝ}
    (hΨ : Continuous Ψ) (hΨ' : Continuous Ψ') (x : Submission.BoseGases.X n) :
    Submission.BoseGases.aQ ℓ j (fun y => Ψ y + Ψ' y) x
      = Submission.BoseGases.aQ ℓ j Ψ x + Submission.BoseGases.aQ ℓ j Ψ' x := by
  change Ψ x + Ψ' x - Submission.BoseGases.aP ℓ j (Ψ + Ψ') x
    = (Ψ x - Submission.BoseGases.aP ℓ j Ψ x) + (Ψ' x - Submission.BoseGases.aP ℓ j Ψ' x)
  rw [Submission.BoseGases.aP_add hℓ j hΨ hΨ' x]
  ring

/-- `aQ` is additive (subtraction, pointwise form). -/
lemma aQ_sub_apply {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) {Ψ Ψ' : Submission.BoseGases.X n → ℝ}
    (hΨ : Continuous Ψ) (hΨ' : Continuous Ψ') (x : Submission.BoseGases.X n) :
    Submission.BoseGases.aQ ℓ j (fun y => Ψ y - Ψ' y) x
      = Submission.BoseGases.aQ ℓ j Ψ x - Submission.BoseGases.aQ ℓ j Ψ' x := by
  change Ψ x - Ψ' x - Submission.BoseGases.aP ℓ j (Ψ - Ψ') x
    = (Ψ x - Submission.BoseGases.aP ℓ j Ψ x) - (Ψ' x - Submission.BoseGases.aP ℓ j Ψ' x)
  rw [Submission.BoseGases.aP_sub hℓ j hΨ hΨ' x]
  ring

/-- `aQ` is additive (function form). -/
lemma aQ_add_fun {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) {Ψ Ψ' : Submission.BoseGases.X n → ℝ}
    (hΨ : Continuous Ψ) (hΨ' : Continuous Ψ') :
    Submission.BoseGases.aQ ℓ j (fun y => Ψ y + Ψ' y)
      = fun y => Submission.BoseGases.aQ ℓ j Ψ y + Submission.BoseGases.aQ ℓ j Ψ' y :=
  funext fun x => aQ_add_apply hℓ j hΨ hΨ' x

/-- `aQ` is additive (subtraction, function form). -/
lemma aQ_sub_fun {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) {Ψ Ψ' : Submission.BoseGases.X n → ℝ}
    (hΨ : Continuous Ψ) (hΨ' : Continuous Ψ') :
    Submission.BoseGases.aQ ℓ j (fun y => Ψ y - Ψ' y)
      = fun y => Submission.BoseGases.aQ ℓ j Ψ y - Submission.BoseGases.aQ ℓ j Ψ' y :=
  funext fun x => aQ_sub_apply hℓ j hΨ hΨ' x

/-- **`neuWord` is the coefficient times the Neumann fraction of the mean-free part.** -/
lemma neuWord_eq {ℓ d εT : ℝ} (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseKinLoc.neuWord ℓ d εT 0 ψ
      = ((1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ))
        * Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0 (Work.BoseKinLoc.Qfree ℓ 0 ψ) := rfl

/-- **The anchored box word as a combination of the four unit-parameter words.**  At the
anchored box `u = 0`, the localised kinetic word `fsT` is linear in `ε_T` through `neuWord`,
linear in `b` through `gapWord`, bilinear through `momWord`, and affine in `ε_T` through
`mainWord`. -/
lemma fsT_decompose' (ℓ d s eT bp : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseKinLoc.fsT ℓ d s eT bp 0 ψ
      = eT * Work.BoseKinLoc.neuWord ℓ d 1 0 ψ
        + bp * Work.BoseKinLoc.gapWord ℓ 1 0 ψ
        + (eT * bp) * Work.BoseKinLoc.momWord ℓ d 1 1 0 ψ
        + (1 - eT) * Work.BoseKinLoc.mainWord ℓ d s 0 0 ψ
        + eT * Work.BoseKinLoc.mainWord ℓ d s 1 0 ψ := by
  rw [Work.BoseKinLoc.fsT_eq_sum]
  simp only [Work.BoseKinLoc.neuWord, Work.BoseKinLoc.gapWord, Work.BoseKinLoc.momWord,
    Work.BoseKinLoc.mainWord]
  ring

/-- The `mainWord` atom at `ε_T = 0` with the parameter `d·s` is the atom at `ε_T = 1` with
the parameter `s`: both are the one-body form with the second cut-off `½(dsℓ)⁻¹`. -/
lemma mainWord_at_d_mul (ℓ d s : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseKinLoc.mainWord ℓ d (d * s) 0 0 ψ = Work.BoseKinLoc.mainWord ℓ d s 1 0 ψ := by
  simp only [Work.BoseKinLoc.mainWord]
  ring

/-- `IntegrableOn` is closed under left multiplication by a constant. -/
private lemma integrableOn_const_mul' {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f : α → ℝ} (h : IntegrableOn f s μ) (c : ℝ) :
    IntegrableOn (fun x => c * f x) s μ :=
  (show Integrable f (μ.restrict s) from h).const_mul c

/-- **Integrability of the slot-`j` `neuWord` integrand of a smooth state.**

The whole localised kinetic word `fsT` is integrable for *every* value of its parameters
(`Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth`), and the anchored word is the explicit
combination of `fsT_decompose'`; solving that combination for the `neuWord` atom gives
`N = S(1,0) − S(0,0) − B₂ + B₁`, a combination of integrable functions.  (No measurability or
boundedness argument is needed.) -/
lemma integrableOn_indU_mul_neuWord_fibre {ℓ d εT : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) volume := by
  classical
  have hs : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_measurable n ℓ
  -- the whole parametrised integrand is integrable for every value of the parameters
  have hInt : ∀ s' e b : ℝ, IntegrableOn
      (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.fsT ℓ d s' e b 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := fun s' e b =>
    Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (ℓ := ℓ) (d := d) (s := s')
      (εT := e) (b := b) hℓ j hΦ
  -- ## the two `mainWord` atoms
  have hB1 : IntegrableOn
      (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.mainWord ℓ d 1 0 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
    refine (hInt 1 0 0).congr_fun ?_ hs
    intro x _
    show Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.fsT ℓ d 1 0 0 0 (Work.BoseKinLoc.fibre n j Φ x)
      = Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.mainWord ℓ d 1 0 0 (Work.BoseKinLoc.fibre n j Φ x)
    rw [fsT_decompose' (ℓ := ℓ) (d := d) (s := 1) (eT := 0) (bp := 0)]
    ring
  have hB2 : IntegrableOn
      (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.mainWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
    refine (hInt (d * 1) 0 0).congr_fun ?_ hs
    intro x _
    show Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.fsT ℓ d (d * 1) 0 0 0 (Work.BoseKinLoc.fibre n j Φ x)
      = Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.mainWord ℓ d 1 1 0 (Work.BoseKinLoc.fibre n j Φ x)
    rw [fsT_decompose' (ℓ := ℓ) (d := d) (s := d * 1) (eT := 0) (bp := 0),
      mainWord_at_d_mul ℓ d 1 (Work.BoseKinLoc.fibre n j Φ x)]
    ring
  -- ## the `neuWord` atom: `N = S(1,0) − S(0,0) − B₂ + B₁`
  have hN : IntegrableOn
      (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
        Work.BoseKinLoc.neuWord ℓ d 1 0 (Work.BoseKinLoc.fibre n j Φ x))
      (Submission.BoseGases.abox n ℓ) := by
    have hcomb := (((hInt 1 1 0).sub (hInt 1 0 0)).sub hB2).add hB1
    refine hcomb.congr_fun ?_ hs
    intro x _
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [fsT_decompose' (ℓ := ℓ) (d := d) (s := 1) (eT := 1) (bp := 0),
      fsT_decompose' (ℓ := ℓ) (d := d) (s := 1) (eT := 0) (bp := 0)]
    ring
  -- ## multiply the `ε_T = 1` atom by `ε_T`
  refine (integrableOn_const_mul' hN εT).congr_fun ?_ hs
  intro x _
  show εT * (Work.BoseKinLoc.indU ℓ 0 (x j) *
      Work.BoseKinLoc.neuWord ℓ d 1 0 (Work.BoseKinLoc.fibre n j Φ x))
    = Work.BoseKinLoc.indU ℓ 0 (x j) *
      Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n j Φ x)
  rw [Work.BoseKinLoc.neuWord, Work.BoseKinLoc.neuWord]
  ring


/-- `0` lies in the centred cube. -/
lemma zero_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (0 : EuclideanSpace ℝ (Fin 3)) ∈ Submission.BoseGases.acube ℓ := by
  have h := (Submission.BoseGases.mem_abox_iff 1 ℓ (0 : Submission.BoseGases.X 1)).mp
    (Submission.BoseGases.zero_mem_abox (N := 1) hℓ.le) (0 : Fin 1)
  simpa using h

/-- Inserting `z` at slot `j` of `kcInsN m i (0, r)` keeps the configuration in the box. -/
lemma mem_abox_update_insert {m : ℕ} {i j : Fin (m + 1)} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {r : Submission.BoseGases.X m} (hr : r ∈ Submission.BoseGases.abox m ℓ)
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ Submission.BoseGases.acube ℓ) :
    Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z
      ∈ Submission.BoseGases.abox (m + 1) ℓ := by
  intro k
  by_cases hk : k = j
  · subst hk; rwa [Function.update_self]
  · rw [Function.update_of_ne hk]
    by_cases hk' : k = i
    · subst hk'; rw [Submission.BoseGases.kc_insN_apply_same]; exact zero_mem_acube hℓ
    · obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hk'
      rw [← hj', Submission.BoseGases.kc_insN_apply_succ]; exact hr j'

/-- Inserting `y` at slot `i` of the previous configuration keeps it in the box. -/
lemma mem_abox_update_insert_insert {m : ℕ} {i j : Fin (m + 1)} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {r : Submission.BoseGases.X m} (hr : r ∈ Submission.BoseGases.abox m ℓ)
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ Submission.BoseGases.acube ℓ)
    {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ Submission.BoseGases.acube ℓ) :
    Function.update (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z) i y
      ∈ Submission.BoseGases.abox (m + 1) ℓ := by
  intro k
  by_cases hk : k = i
  · subst hk; rwa [Function.update_self]
  · rw [Function.update_of_ne hk]
    exact mem_abox_update_insert hℓ hr hz k

/-- Updating the slot `i` of `kcInsN m i (0, r)` to `y` gives `kcInsN m i (y, r)`. -/
lemma update_insert_self {m : ℕ} (i : Fin (m + 1)) (r : Submission.BoseGases.X m)
    (y : EuclideanSpace ℝ (Fin 3)) :
    Function.update (Submission.BoseGases.kcInsN m i (0, r)) i y
      = Submission.BoseGases.kcInsN m i (y, r) := by
  ext k
  by_cases hk : k = i
  · subst hk
    rw [Function.update_self, Submission.BoseGases.kc_insN_apply_same]
  · rw [Function.update_of_ne hk]
    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hk
    rw [← hj', Submission.BoseGases.kc_insN_apply_succ, Submission.BoseGases.kc_insN_apply_succ]

/-- Updating the slot `j` of `kcInsN m j p` to `z` gives `kcInsN m j (z, p.2)`. -/
lemma update_kcInsN_self {m : ℕ} (j : Fin (m + 1))
    (p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X m)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Function.update (Submission.BoseGases.kcInsN m j p) j z
      = Submission.BoseGases.kcInsN m j (z, p.2) := by
  ext k
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self, Submission.BoseGases.kc_insN_apply_same]
  · rw [Function.update_of_ne hk]
    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hk
    rw [← hj', Submission.BoseGases.kc_insN_apply_succ, Submission.BoseGases.kc_insN_apply_succ]


/-- **The core off-diagonal identity.**  Two states `Ψc`, `Ψg` whose slot-`j` fibres are
mean-free, with `Ψc` independent of the slot-`i` coordinate (`i ≠ j`) and the slot-`i` fibre of
`Ψg` mean-free, give a vanishing slot-`j` `neuWord` off-diagonal integral. -/
lemma neuWord_offdiag_core {ℓ d εT : ℝ} (hℓ : 0 < ℓ) {m : ℕ} {j i : Fin (m + 1)}
    (hij : i ≠ j) {Ψc Ψg : Submission.BoseGases.X (m + 1) → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) Ψc) (hg : ContDiff ℝ (⊤ : ℕ∞) Ψg)
    (hjc : Submission.BoseGases.aP ℓ j Ψc = 0) (hjg : Submission.BoseGases.aP ℓ j Ψg = 0)
    (hic : Work.BoseFixB2.Sector.ConstIn i Ψc)
    (hig : Submission.BoseGases.aP ℓ i Ψg = 0) :
    (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
      (Work.BoseKinLoc.neuWord ℓ d εT 0
          (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y + Ψg y) x)
       - Work.BoseKinLoc.neuWord ℓ d εT 0
          (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y - Ψg y) x))) = 0 := by
  classical
  set a2 : ℝ := (d * ℓ) ^ (-2 : ℤ) with ha2def
  set Cc : ℝ := (1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ) with hCcdef
  have hcoef : (1 / 2) * εT * (d * ℓ) ^ (-2 : ℤ) = Cc := hCcdef.symm
  rcases eq_or_ne Cc 0 with hC0 | hCne
  · have hzero : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, Work.BoseKinLoc.neuWord ℓ d εT 0 ψ = 0 := by
      intro ψ
      rw [neuWord_eq ψ, hcoef, hC0, zero_mul]
    simp only [hzero, sub_self, mul_zero]
    simp
  · -- the coefficient does not vanish
    have ha2ne : a2 ≠ 0 := by
      intro h
      apply hCne
      rw [hCcdef, ← ha2def, h, mul_zero]
    have ha2nonneg : 0 ≤ a2 := by
      have h1 : (d * ℓ) ^ (-2 : ℤ) = (((d * ℓ) ^ 2)⁻¹) := by
        rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
      rw [ha2def, h1, inv_nonneg]
      exact sq_nonneg _
    have ha2pos : 0 < a2 := lt_of_le_of_ne ha2nonneg (Ne.symm ha2ne)
    -- (i) the pointwise reduction of the bracket
    have hstep : ∀ x : Submission.BoseGases.X (m + 1),
        (Work.BoseKinLoc.neuWord ℓ d εT 0
            (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y + Ψg y) x)
          - Work.BoseKinLoc.neuWord ℓ d εT 0
            (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y - Ψg y) x))
        = Cc * (Work.BoseKinLoc.neuFrac ℓ a2 0
              (fun z => Ψc (Function.update x j z) + Ψg (Function.update x j z))
            - Work.BoseKinLoc.neuFrac ℓ a2 0
              (fun z => Ψc (Function.update x j z) - Ψg (Function.update x j z))) := by
      intro x
      have hcw : Continuous (Work.BoseKinLoc.fibre (m + 1) j Ψc x) :=
        hc.continuous.comp (continuous_update_const' j x)
      have hgw : Continuous (Work.BoseKinLoc.fibre (m + 1) j Ψg x) :=
        hg.continuous.comp (continuous_update_const' j x)
      have hplus : Work.BoseKinLoc.Qfree ℓ 0
            (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y + Ψg y) x)
          = fun z => Ψc (Function.update x j z) + Ψg (Function.update x j z) := by
        rw [Qfree_fibre_eq', aQ_add_fun hℓ j hc.continuous hg.continuous,
          aQ_eq_self_of_aP_eq_zero j hjc, aQ_eq_self_of_aP_eq_zero j hjg]
        rfl
      have hminus : Work.BoseKinLoc.Qfree ℓ 0
            (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y - Ψg y) x)
          = fun z => Ψc (Function.update x j z) - Ψg (Function.update x j z) := by
        rw [Qfree_fibre_eq', aQ_sub_fun hℓ j hc.continuous hg.continuous,
          aQ_eq_self_of_aP_eq_zero j hjc, aQ_eq_self_of_aP_eq_zero j hjg]
        rfl
      rw [neuWord_eq, neuWord_eq, hplus, hminus, ← ha2def, ← hCcdef]
      ring
    -- (ii) the bound for the transfer lemma, and elementary box-membership helpers
    obtain ⟨Mc, hMc⟩ := (Submission.BoseGases.abox_compact (m + 1) hℓ).exists_bound_of_continuousOn
      hc.continuous.continuousOn
    obtain ⟨Mg, hMg⟩ := (Submission.BoseGases.abox_compact (m + 1) hℓ).exists_bound_of_continuousOn
      hg.continuous.continuousOn
    set R : ℝ := 1 + |Mc| + |Mg| with hRdef
    have hRpos : 0 < R := by rw [hRdef]; positivity
    -- (iii) helpers: the coordinate independence of the weight and of the `Ψc`-fibre
    have hweight : ∀ r : Submission.BoseGases.X m, ∀ y : EuclideanSpace ℝ (Fin 3),
        Work.BoseKinLoc.indU ℓ 0 ((Submission.BoseGases.kcInsN m i (y, r)) j)
          = Work.BoseKinLoc.indU ℓ 0 ((Submission.BoseGases.kcInsN m i (0, r)) j) := by
      intro r y
      obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
      rw [← hj', Submission.BoseGases.kc_insN_apply_succ, Submission.BoseGases.kc_insN_apply_succ]
    have hconstant : ∀ r : Submission.BoseGases.X m, ∀ y z : EuclideanSpace ℝ (Fin 3),
        Ψc (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)
          = Ψc (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z) := by
      intro r y z
      have h := hic (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z) y
      have hcomm : Function.update (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z) i y
          = Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z := by
        rw [← Function.update_comm hij y z (Submission.BoseGases.kcInsN m i (0, r)),
          update_insert_self i r y]
      rwa [hcomm] at h
    have hcommg : ∀ r : Submission.BoseGases.X m, ∀ z y : EuclideanSpace ℝ (Fin 3),
        Ψg (Function.update (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z) i y)
          = Ψg (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z) := by
      intro r z y
      congr 1
      rw [← Function.update_comm hij y z (Submission.BoseGases.kcInsN m i (0, r)),
        update_insert_self i r y]
    -- (iv) the integrability of the integrand
    have hFint : IntegrableOn
        (fun x : Submission.BoseGases.X (m + 1) => Work.BoseKinLoc.indU ℓ 0 (x j) *
          (Work.BoseKinLoc.neuWord ℓ d εT 0
              (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y + Ψg y) x)
           - Work.BoseKinLoc.neuWord ℓ d εT 0
              (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y - Ψg y) x)))
        (Submission.BoseGases.abox (m + 1) ℓ) volume := by
      rw [show (fun x : Submission.BoseGases.X (m + 1) => Work.BoseKinLoc.indU ℓ 0 (x j) *
            (Work.BoseKinLoc.neuWord ℓ d εT 0
                (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y + Ψg y) x)
             - Work.BoseKinLoc.neuWord ℓ d εT 0
                (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y - Ψg y) x)))
          = fun x => Work.BoseKinLoc.indU ℓ 0 (x j) *
                Work.BoseKinLoc.neuWord ℓ d εT 0
                  (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y + Ψg y) x)
              - Work.BoseKinLoc.indU ℓ 0 (x j) *
                Work.BoseKinLoc.neuWord ℓ d εT 0
                  (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y - Ψg y) x)
          from by funext x; ring]
      exact (integrableOn_indU_mul_neuWord_fibre (ℓ := ℓ) (d := d) (εT := εT) hℓ j
          (hc.add hg)).sub
        (integrableOn_indU_mul_neuWord_fibre (ℓ := ℓ) (d := d) (εT := εT) hℓ j (hc.sub hg))
    -- (v) the inner integral vanishes, by the transfer lemma
    have hinner : ∀ r : Submission.BoseGases.X m, r ∈ Submission.BoseGases.abox m ℓ →
        (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
          Work.BoseKinLoc.indU ℓ 0 ((Submission.BoseGases.kcInsN m i (y, r)) j) *
            (Cc * (Work.BoseKinLoc.neuFrac ℓ a2 0
                  (fun z => Ψc (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)
                    + Ψg (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z))
              - Work.BoseKinLoc.neuFrac ℓ a2 0
                  (fun z => Ψc (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)
                    - Ψg (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z))))) = 0 := by
      intro r hr
      set cF : EuclideanSpace ℝ (Fin 3) → ℝ := fun z =>
        Ψc (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z) with hcFdef
      set gF : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ := fun z y =>
        Ψg (Function.update (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z) i y)
        with hgFdef
      set w0 : ℝ := Work.BoseKinLoc.indU ℓ 0 ((Submission.BoseGases.kcInsN m i (0, r)) j) with hw0def
      set H : EuclideanSpace ℝ (Fin 3) → ℝ := fun y =>
        Work.BoseKinLoc.neuFrac ℓ a2 0 (fun z => cF z + gF z y)
          - Work.BoseKinLoc.neuFrac ℓ a2 0 (fun z => cF z - gF z y) with hHdef
      have htr : (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ, H y) = 0 :=
        neuFrac_offdiag_integral (ℓ := ℓ) (a2 := a2) (R := R) hℓ ha2pos hRpos
          (c := cF) (G := gF)
          (by rw [hcFdef]; exact contDiff_fibre_update j hc (Submission.BoseGases.kcInsN m i (0, r)))
          (by rw [hgFdef]; exact hg.continuous.comp (by fun_prop))
          (by
            intro z hz
            rw [hcFdef]
            have h1 : |Ψc (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z)| ≤ Mc := by
              have h2 := hMc (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z)
                (mem_abox_update_insert hℓ hr hz)
              rwa [Real.norm_eq_abs] at h2
            exact le_trans h1 (le_trans (le_abs_self Mc) (by rw [hRdef]; linarith [abs_nonneg Mg]))
          )
          (by
            intro z hz y hy
            rw [hgFdef]
            have h1 : |Ψg (Function.update (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z) i y)| ≤ Mg := by
              have h2 := hMg (Function.update (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z) i y)
                (mem_abox_update_insert_insert hℓ hr hz hy)
              rwa [Real.norm_eq_abs] at h2
            exact le_trans h1 (le_trans (le_abs_self Mg) (by rw [hRdef]; linarith [abs_nonneg Mc]))
          )
          (by
            intro z
            have h := congrFun hig (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j z)
            simp only [Submission.BoseGases.aP] at h
            have hne : (1 / ℓ ^ 3 : ℝ) ≠ 0 := by positivity
            rw [hgFdef]
            exact (mul_eq_zero.mp h).resolve_left hne)
      -- pull the constants out of the inner integral and apply the transfer identity
      have hplusfun : ∀ y : EuclideanSpace ℝ (Fin 3),
          (fun z => Ψc (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)
              + Ψg (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z))
            = (fun z => cF z + gF z y) := by
        intro y
        funext z
        rw [hcFdef, hgFdef, hconstant r y z, ← hcommg r z y]
      have hminusfun : ∀ y : EuclideanSpace ℝ (Fin 3),
          (fun z => Ψc (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)
              - Ψg (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z))
            = (fun z => cF z - gF z y) := by
        intro y
        funext z
        rw [hcFdef, hgFdef, hconstant r y z, ← hcommg r z y]
      have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
          Work.BoseKinLoc.indU ℓ 0 ((Submission.BoseGases.kcInsN m i (y, r)) j) *
            (Cc * (Work.BoseKinLoc.neuFrac ℓ a2 0
                  (fun z => Ψc (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)
                    + Ψg (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z))
              - Work.BoseKinLoc.neuFrac ℓ a2 0
                  (fun z => Ψc (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)
                    - Ψg (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z))))
          = w0 * (Cc * H y) := by
        intro y
        rw [hweight r y, ← hw0def, hplusfun y, hminusfun y]
      rw [show (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
            Work.BoseKinLoc.indU ℓ 0 ((Submission.BoseGases.kcInsN m i (y, r)) j) *
              (Cc * (Work.BoseKinLoc.neuFrac ℓ a2 0
                    (fun z => Ψc (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)
                      + Ψg (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z))
                - Work.BoseKinLoc.neuFrac ℓ a2 0
                    (fun z => Ψc (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)
                      - Ψg (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)))))
          = ∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ, w0 * (Cc * H y)
          from integral_congr_ae (Filter.Eventually.of_forall hpt)]
      have h1 : (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
            w0 * (Cc * H y))
          = w0 * (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ, Cc * H y) := by
        rw [← MeasureTheory.integral_const_mul]
      have h2 : (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ, Cc * H y)
          = Cc * (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ, H y) := by
        rw [← MeasureTheory.integral_const_mul]
      rw [h1, h2, htr]
      ring
    -- (vi) the peel
    rw [show (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          (Work.BoseKinLoc.neuWord ℓ d εT 0
              (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y + Ψg y) x)
           - Work.BoseKinLoc.neuWord ℓ d εT 0
              (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y - Ψg y) x)))
        = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
            (Cc * (Work.BoseKinLoc.neuFrac ℓ a2 0
                  (fun z => Ψc (Function.update x j z) + Ψg (Function.update x j z))
                - Work.BoseKinLoc.neuFrac ℓ a2 0
                  (fun z => Ψc (Function.update x j z) - Ψg (Function.update x j z))))
        from integral_congr_ae (Filter.Eventually.of_forall (fun x => by
          show Work.BoseKinLoc.indU ℓ 0 (x j) *
                (Work.BoseKinLoc.neuWord ℓ d εT 0
                    (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y + Ψg y) x)
                 - Work.BoseKinLoc.neuWord ℓ d εT 0
                    (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y - Ψg y) x))
              = Work.BoseKinLoc.indU ℓ 0 (x j) *
                (Cc * (Work.BoseKinLoc.neuFrac ℓ a2 0
                      (fun z => Ψc (Function.update x j z) + Ψg (Function.update x j z))
                    - Work.BoseKinLoc.neuFrac ℓ a2 0
                      (fun z => Ψc (Function.update x j z) - Ψg (Function.update x j z))))
          rw [hstep x]))]
    have hFint' : IntegrableOn
        (fun x : Submission.BoseGases.X (m + 1) => Work.BoseKinLoc.indU ℓ 0 (x j) *
          (Cc * (Work.BoseKinLoc.neuFrac ℓ a2 0
                (fun z => Ψc (Function.update x j z) + Ψg (Function.update x j z))
              - Work.BoseKinLoc.neuFrac ℓ a2 0
                (fun z => Ψc (Function.update x j z) - Ψg (Function.update x j z)))))
        (Submission.BoseGases.abox (m + 1) ℓ) volume := by
      refine hFint.congr_fun ?_ (Submission.BoseGases.abox_measurable (m + 1) ℓ)
      intro x _
      show Work.BoseKinLoc.indU ℓ 0 (x j) *
            (Work.BoseKinLoc.neuWord ℓ d εT 0
                (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y + Ψg y) x)
             - Work.BoseKinLoc.neuWord ℓ d εT 0
                (Work.BoseKinLoc.fibre (m + 1) j (fun y => Ψc y - Ψg y) x))
        = Work.BoseKinLoc.indU ℓ 0 (x j) *
            (Cc * (Work.BoseKinLoc.neuFrac ℓ a2 0
                  (fun z => Ψc (Function.update x j z) + Ψg (Function.update x j z))
                - Work.BoseKinLoc.neuFrac ℓ a2 0
                  (fun z => Ψc (Function.update x j z) - Ψg (Function.update x j z))))
      rw [hstep x]
    rw [Submission.BoseGases.abox_integral_peel (i := i) (F := fun x : Submission.BoseGases.X (m + 1) =>
          Work.BoseKinLoc.indU ℓ 0 (x j) *
            (Cc * (Work.BoseKinLoc.neuFrac ℓ a2 0
                  (fun z => Ψc (Function.update x j z) + Ψg (Function.update x j z))
                - Work.BoseKinLoc.neuFrac ℓ a2 0
                  (fun z => Ψc (Function.update x j z) - Ψg (Function.update x j z))))) hFint']
    -- the outer integral of the (a.e.) zero function
    rw [show (∫ r : Submission.BoseGases.X m,
          (∫ y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube ℓ,
            Work.BoseKinLoc.indU ℓ 0 ((Submission.BoseGases.kcInsN m i (y, r)) j) *
              (Cc * (Work.BoseKinLoc.neuFrac ℓ a2 0
                    (fun z => Ψc (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)
                      + Ψg (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z))
                - Work.BoseKinLoc.neuFrac ℓ a2 0
                    (fun z => Ψc (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)
                      - Ψg (Function.update (Submission.BoseGases.kcInsN m i (y, r)) j z)))))
          ∂(volume.restrict (Submission.BoseGases.abox m ℓ))) = 0 from by
      rw [MeasureTheory.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff'
          (Submission.BoseGases.abox_measurable m ℓ)]
        exact Filter.Eventually.of_forall (fun r hr => hinner r hr)]

/-- **The `neuWord` off-diagonal integral vanishes between two different joint sectors.** -/
theorem neuWord_fibre_offdiag {ℓ d εT : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n) (hjS : (j : ℕ) ∈ S) (hjT : (j : ℕ) ∈ T) (hST : S ≠ T) : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) * (Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x) - Work.BoseKinLoc.neuWord ℓ d εT 0 (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0 := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ m =>
    -- some slot `i` lies in exactly one of `S`, `T`
    have hSD : ∃ i : ℕ, (i ∈ S ∧ i ∉ T) ∨ (i ∈ T ∧ i ∉ S) := by
      by_cases hsub : S ⊆ T
      · obtain ⟨k, hkT, hkS⟩ :=
          Finset.not_subset.mp (fun h : T ⊆ S => hST (Finset.Subset.antisymm hsub h))
        exact ⟨k, Or.inr ⟨hkT, hkS⟩⟩
      · obtain ⟨k, hkS, hkT⟩ := Finset.not_subset.mp hsub
        exact ⟨k, Or.inl ⟨hkS, hkT⟩⟩
    obtain ⟨i, ⟨hiS, hiT⟩ | ⟨hiT, hiS⟩⟩ := hSD
    · -- `i ∈ S \ T`: `E_SΦ` is the slot-`i` mean-free state, `E_TΦ` the slot-`i` constant one
      have hi_lt : i < m + 1 := Finset.mem_range.mp (hS hiS)
      have hji : (⟨i, hi_lt⟩ : Fin (m + 1)) ≠ j := by
        intro h
        have hval : i = (j : ℕ) := congrArg Fin.val h
        exact hiT (hval ▸ hjT)
      have hcore := neuWord_offdiag_core (ℓ := ℓ) (d := d) (εT := εT) hℓ (m := m)
        (j := j) (i := ⟨i, hi_lt⟩) hji
        (Ψc := Work.BoseFixB2.jointProj ℓ T Φ) (Ψg := Work.BoseFixB2.jointProj ℓ S Φ)
        (Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ)
        (Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ)
        (Work.BoseFixB2.Sector.jointProj_aP_eq_zero hℓ hjT j.isLt hΦ)
        (Work.BoseFixB2.Sector.jointProj_aP_eq_zero hℓ hjS j.isLt hΦ)
        (Work.BoseFixB2.Sector.constIn_jointProj hℓ hi_lt hiT hΦ.continuous)
        (Work.BoseFixB2.Sector.aP_blockOp_eq_zero hℓ hi_lt hiS hΦ.continuous)
      have hBA : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
            (Work.BoseKinLoc.neuWord ℓ d εT 0
                (Work.BoseKinLoc.fibre (m + 1) j
                  (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
             - Work.BoseKinLoc.neuWord ℓ d εT 0
                (Work.BoseKinLoc.fibre (m + 1) j
                  (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x)))
          = (∫ x in Submission.BoseGases.abox (m + 1) ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
            (Work.BoseKinLoc.neuWord ℓ d εT 0
                (Work.BoseKinLoc.fibre (m + 1) j
                  (Work.BoseFixB2.jointProj ℓ T Φ + Work.BoseFixB2.jointProj ℓ S Φ) x)
             - Work.BoseKinLoc.neuWord ℓ d εT 0
                (Work.BoseKinLoc.fibre (m + 1) j
                  (Work.BoseFixB2.jointProj ℓ T Φ - Work.BoseFixB2.jointProj ℓ S Φ) x))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        show Work.BoseKinLoc.indU ℓ 0 (x j) *
              (Work.BoseKinLoc.neuWord ℓ d εT 0
                  (Work.BoseKinLoc.fibre (m + 1) j
                    (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x)
               - Work.BoseKinLoc.neuWord ℓ d εT 0
                  (Work.BoseKinLoc.fibre (m + 1) j
                    (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))
            = Work.BoseKinLoc.indU ℓ 0 (x j) *
              (Work.BoseKinLoc.neuWord ℓ d εT 0
                  (Work.BoseKinLoc.fibre (m + 1) j
                    (Work.BoseFixB2.jointProj ℓ T Φ + Work.BoseFixB2.jointProj ℓ S Φ) x)
               - Work.BoseKinLoc.neuWord ℓ d εT 0
                  (Work.BoseKinLoc.fibre (m + 1) j
                    (Work.BoseFixB2.jointProj ℓ T Φ - Work.BoseFixB2.jointProj ℓ S Φ) x))
        have h1 : Work.BoseKinLoc.fibre (m + 1) j
              (Work.BoseFixB2.jointProj ℓ T Φ + Work.BoseFixB2.jointProj ℓ S Φ) x
            = Work.BoseKinLoc.fibre (m + 1) j
              (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x := by
          funext z
          simp only [Work.BoseKinLoc.fibre, Pi.add_apply]
          ring
        have h2 : Work.BoseKinLoc.fibre (m + 1) j
              (Work.BoseFixB2.jointProj ℓ T Φ - Work.BoseFixB2.jointProj ℓ S Φ) x
            = fun z => -(Work.BoseKinLoc.fibre (m + 1) j
              (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x z) := by
          funext z
          simp only [Work.BoseKinLoc.fibre, Pi.sub_apply]
          ring
        rw [h1, h2, Work.BoseFixB2.Polar.PolB.neuWord_neg]
      rw [hBA]
      exact hcore
    · -- `i ∈ T \ S`: `E_SΦ` is the slot-`i` constant state, `E_TΦ` the slot-`i` mean-free one
      have hi_lt : i < m + 1 := Finset.mem_range.mp (hT hiT)
      have hji : (⟨i, hi_lt⟩ : Fin (m + 1)) ≠ j := by
        intro h
        have hval : i = (j : ℕ) := congrArg Fin.val h
        exact hiS (hval ▸ hjS)
      exact neuWord_offdiag_core (ℓ := ℓ) (d := d) (εT := εT) hℓ (m := m)
        (j := j) (i := ⟨i, hi_lt⟩) hji
        (Ψc := Work.BoseFixB2.jointProj ℓ S Φ) (Ψg := Work.BoseFixB2.jointProj ℓ T Φ)
        (Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ)
        (Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ)
        (Work.BoseFixB2.Sector.jointProj_aP_eq_zero hℓ hjS j.isLt hΦ)
        (Work.BoseFixB2.Sector.jointProj_aP_eq_zero hℓ hjT j.isLt hΦ)
        (Work.BoseFixB2.Sector.constIn_jointProj hℓ hi_lt hiS hΦ.continuous)
        (Work.BoseFixB2.Sector.aP_blockOp_eq_zero hℓ hi_lt hiT hΦ.continuous)

end Work.Analysis.BoseBand
