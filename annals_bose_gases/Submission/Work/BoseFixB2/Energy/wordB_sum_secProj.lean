import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB2.Energy.bsOneBody_hpol
import Submission.Work.BoseFixB2.Energy.gapBare_hpol
import Submission.Work.BoseFixB2.Energy.hpol_of_par_nonneg
import Submission.Work.BoseFixB2.Energy.momForm_hpol
import Submission.Work.BoseFixB2.Energy.neuFrac_nonneg_smooth
import Submission.Work.BoseFixB2.Polar.boxFormB_parallelogram
import Submission.Work.BoseFixB2.Polar.boxFormB_smul
import Submission.Work.BoseFixB2.Polar.par_polarisation_hpol
import Submission.Work.BoseFixB2.Polar.wordB_box_local
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
noncomputable section
namespace Work.BoseFixB2.Energy

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix Work.UBB Work.BoseFixB2

/-! ## 0. The submodules of smooth states -/

/-- The smooth `n`-body states as a submodule of all states.  The abstract polarisation
identity `Polar.par_polarisation_hpol` is applied with `V` this submodule, so that its
hypotheses only have to hold on smooth states — where the box words are understood. -/
def SmSub (n : ℕ) : Submodule ℝ (Submission.BoseGases.X n → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f}
  zero_mem' := show ContDiff ℝ (⊤ : ℕ∞) (0 : Submission.BoseGases.X n → ℝ) from contDiff_const
  add_mem' := by
    intro f g hf hg
    rw [Set.mem_ofPred_eq] at hf hg ⊢
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    rw [Set.mem_ofPred_eq] at hf ⊢
    exact hf.const_smul c

/-- The smooth *one-body* states as a submodule of all one-body states. -/
def SmSub1 : Submodule ℝ (EuclideanSpace ℝ (Fin 3) → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f}
  zero_mem' := show ContDiff ℝ (⊤ : ℕ∞) (0 : EuclideanSpace ℝ (Fin 3) → ℝ) from contDiff_const
  add_mem' := by
    intro f g hf hg
    rw [Set.mem_ofPred_eq] at hf hg ⊢
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    rw [Set.mem_ofPred_eq] at hf ⊢
    exact hf.const_smul c

lemma SmSub.contDiff {n : ℕ} (x : ↥(SmSub n)) :
    ContDiff ℝ (⊤ : ℕ∞) (x : Submission.BoseGases.X n → ℝ) := by
  have h : (x : Submission.BoseGases.X n → ℝ) ∈ (SmSub n).carrier := x.2
  change (x : Submission.BoseGases.X n → ℝ) ∈ {f | ContDiff ℝ (⊤ : ℕ∞) f} at h
  exact h

lemma SmSub1.contDiff (x : ↥(SmSub1)) :
    ContDiff ℝ (⊤ : ℕ∞) (x : EuclideanSpace ℝ (Fin 3) → ℝ) := by
  have h : (x : EuclideanSpace ℝ (Fin 3) → ℝ) ∈ (SmSub1).carrier := x.2
  change (x : EuclideanSpace ℝ (Fin 3) → ℝ) ∈ {f | ContDiff ℝ (⊤ : ℕ∞) f} at h
  exact h

lemma SmSub.mem {n : ℕ} {f : Submission.BoseGases.X n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : f ∈ SmSub n := by
  change ContDiff ℝ (⊤ : ℕ∞) f
  exact hf

lemma SmSub1.mem {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : f ∈ SmSub1 := by
  change ContDiff ℝ (⊤ : ℕ∞) f
  exact hf

/-! ## 1. Positivity of FS's parameters in the non-degenerate case -/

/-- `x ^ (-(1/2)) = 0` for `x ≤ 0`: the box side `(μa)^{-1/2}` collapses. -/
lemma rpow_neg_half_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : x ^ (-(1/2) : ℝ) = 0 := by
  rcases lt_or_eq_of_le hx with h | h
  · rw [Real.rpow_def_of_neg h]
    have h2 : (-(1/2) : ℝ) * Real.pi = -(Real.pi / 2) := by ring
    rw [h2, Real.cos_neg, Real.cos_pi_div_two, mul_zero]
  · subst h; rw [Real.zero_rpow]; norm_num

/-- If the box side `ℓ = fsSide v μ` is positive, then `μ·a v > 0` and hence every FS parameter
(except the universal `b = 1/16`) is positive. -/
lemma param_pos_of_side_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hpos : 0 < fsSide v μ) :
    0 < (paramsAt μ (_root_.BoseGases.a v)).d ∧
    0 < (paramsAt μ (_root_.BoseGases.a v)).s ∧
    0 < (paramsAt μ (_root_.BoseGases.a v)).eT ∧
    0 < (paramsAt μ (_root_.BoseGases.a v)).b := by
  have ha : 0 < μ * _root_.BoseGases.a v := by
    have hside : fsSide v μ
        = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(3/2))
          * (μ * _root_.BoseGases.a v) ^ (-(1/2) : ℝ) := rfl
    by_contra hle
    rw [not_lt] at hle
    have h0 : (μ * _root_.BoseGases.a v) ^ (-(1/2) : ℝ) = 0 :=
      rpow_neg_half_eq_zero_of_nonpos hle
    rw [hside, h0, mul_zero] at hpos
    exact lt_irrefl 0 hpos
  have ha0 : _root_.BoseGases.a v ≠ 0 := by
    intro h; rw [h, mul_zero] at ha; exact lt_irrefl 0 ha
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by
    have h2 : (0:ℝ) < (_root_.BoseGases.a v) ^ 2 := by positivity
    have h3 : μ * (_root_.BoseGases.a v) ^ 3
        = (μ * _root_.BoseGases.a v) * (_root_.BoseGases.a v)^2 := by ring
    rw [h3]; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · show 0 < Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 6
    exact Real.rpow_pos_of_pos ht _
  · show 0 < Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) 1
    exact Real.rpow_pos_of_pos ht _
  · show 0 < Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (23/4)
    exact Real.rpow_pos_of_pos ht _
  · show 0 < (1/16 : ℝ)
    norm_num

/-! ## 2. The parallelogram law and the `2`-homogeneity of `wordB` -/

/-- The parallelogram law of the frozen box word, from `Polar.boxFormB_parallelogram` at FS's
parameters. -/
theorem wordB_parallelogram {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ}
    (hpos : 0 < fsSide v μ)
    (hw : IntegrableOn (fun x : X n => potWordU n v (g0 v h) (fsSide v μ) μ 0 x)
      (abox n (fsSide v μ)))
    {Φ Ψ : X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    Work.BoseBoxFix.wordB v h μ n (fun x => Φ x + Ψ x)
        + Work.BoseBoxFix.wordB v h μ n (fun x => Φ x - Ψ x)
      = 2 * Work.BoseBoxFix.wordB v h μ n Φ + 2 * Work.BoseBoxFix.wordB v h μ n Ψ := by
  obtain ⟨hd, hs, heT, hb⟩ := param_pos_of_side_pos (v := v) (μ := μ) hpos
  exact Work.BoseFixB2.Polar.boxFormB_parallelogram (v := v) (g := g0 v h) (ℓ := fsSide v μ)
    (μ := μ) (d := (paramsAt μ (_root_.BoseGases.a v)).d) (s := (paramsAt μ (_root_.BoseGases.a v)).s)
    (εT := (paramsAt μ (_root_.BoseGases.a v)).eT) (b := (paramsAt μ (_root_.BoseGases.a v)).b)
    hpos hd hs heT hb hΦ hΨ hw

/-- `2`-homogeneity of the frozen box word, from the corpus's two scaling lemmas for its kinetic
and its potential part. -/
theorem wordB_smul {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ} (t : ℝ)
    {Φ : X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.BoseBoxFix.wordB v h μ n (fun x => t * Φ x) = t ^ 2 * Work.BoseBoxFix.wordB v h μ n Φ := by
  show Work.BoseKinLoc.boxFormB n v (g0 v h) (fsSide v μ) μ (paramsAt μ (_root_.BoseGases.a v)).d
      (paramsAt μ (_root_.BoseGases.a v)).s (paramsAt μ (_root_.BoseGases.a v)).eT
      (paramsAt μ (_root_.BoseGases.a v)).b (fun x => t * Φ x)
    = t ^ 2 * Work.BoseKinLoc.boxFormB n v (g0 v h) (fsSide v μ) μ
      (paramsAt μ (_root_.BoseGases.a v)).d (paramsAt μ (_root_.BoseGases.a v)).s
      (paramsAt μ (_root_.BoseGases.a v)).eT (paramsAt μ (_root_.BoseGases.a v)).b Φ
  rw [Work.BoseKinLoc.boxFormB, Work.BoseKinLoc.boxFormB]
  have hk := Work.BoseFixB2.Polar.SmulAux.kinFormB_const_mul n (fsSide v μ)
    (paramsAt μ (_root_.BoseGases.a v)).d (paramsAt μ (_root_.BoseGases.a v)).s
    (paramsAt μ (_root_.BoseGases.a v)).eT (paramsAt μ (_root_.BoseGases.a v)).b t Φ
  have hp := Work.BoseFixB2.Polar.SmulAux.potIntB_const_mul n v (g0 v h) (fsSide v μ) μ t Φ
  rw [hk, hp]; ring

/-! ## 3. `hpol` for the potential part of the box word -/

/-- `hpol` for `∫_{abox} Φ²·potWordU`: the pointwise identity `(tΦ+Ψ)² − (tΦ−Ψ)² = 4t·ΦΨ`
together with the linearity of the box integral. -/
theorem potInt_hpol {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    (hw : IntegrableOn (fun x : X n => potWordU n v g ℓ μ 0 x) (abox n ℓ))
    (t : ℝ) {Φ Ψ : X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    (∫ x in abox n ℓ, (t * Φ x + Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)
      - (∫ x in abox n ℓ, (t * Φ x - Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)
    = t * ((∫ x in abox n ℓ, (Φ x + Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)
      - (∫ x in abox n ℓ, (Φ x - Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)) := by
  have hK : IsCompact (abox n ℓ) := abox_compact n hℓ
  have hI : ∀ Ξ : X n → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ξ →
      IntegrableOn (fun x : X n => (Ξ x) ^ 2 * potWordU n v g ℓ μ 0 x) (abox n ℓ) :=
    fun Ξ hΞ => IntegrableOn.continuousOn_mul (hΞ.continuous.continuousOn.pow 2) hw hK
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : X n => t * Φ x + Ψ x) := (hΦ.const_smul t).add hΨ
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x : X n => t * Φ x - Ψ x) := (hΦ.const_smul t).sub hΨ
  have hsp : ContDiff ℝ (⊤ : ℕ∞) (fun x : X n => Φ x + Ψ x) := hΦ.add hΨ
  have hdp : ContDiff ℝ (⊤ : ℕ∞) (fun x : X n => Φ x - Ψ x) := hΦ.sub hΨ
  have e1 : (∫ x in abox n ℓ, (t * Φ x + Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)
        - (∫ x in abox n ℓ, (t * Φ x - Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)
      = 4 * t * (∫ x in abox n ℓ, Φ x * Ψ x * potWordU n v g ℓ μ 0 x) := by
    rw [← MeasureTheory.integral_sub (hI _ hs) (hI _ hd)]
    rw [show (fun x : X n => (t * Φ x + Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x
          - (t * Φ x - Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)
        = fun x : X n => (4 * t) * (Φ x * Ψ x * potWordU n v g ℓ μ 0 x) from by
      funext x; ring]
    rw [MeasureTheory.integral_const_mul]
  have e2 : (∫ x in abox n ℓ, (Φ x + Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)
        - (∫ x in abox n ℓ, (Φ x - Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)
      = 4 * (∫ x in abox n ℓ, Φ x * Ψ x * potWordU n v g ℓ μ 0 x) := by
    rw [← MeasureTheory.integral_sub (hI _ hsp) (hI _ hdp)]
    rw [show (fun x : X n => (Φ x + Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x
          - (Φ x - Ψ x) ^ 2 * potWordU n v g ℓ μ 0 x)
        = fun x : X n => (4 : ℝ) * (Φ x * Ψ x * potWordU n v g ℓ μ 0 x) from by
      funext x; ring]
    rw [MeasureTheory.integral_const_mul]
  rw [e1, e2]; ring

/-! ## 4. Lifting a one-body `hpol` to the slot integrals -/

/-- The slot-`i` box integral of a one-body word with `hpol` satisfies `hpol`. -/
theorem slot_hpol_of {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i : Fin n)
    {q : (EuclideanSpace ℝ (Fin 3) → ℝ) → ℝ}
    (hq : ∀ (t : ℝ) (f g : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) g →
      q (fun z => t * f z + g z) - q (fun z => t * f z - g z)
        = t * (q (fun z => f z + g z) - q (fun z => f z - g z)))
    (hint : ∀ (Ξ : X n → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ξ →
      IntegrableOn (fun x : X n => indU ℓ 0 (x i) * q (fibre n i Ξ x)) (abox n ℓ))
    (t : ℝ) {Φ Ψ : X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    (∫ x in abox n ℓ, indU ℓ 0 (x i) * q (fibre n i (fun y => t * Φ y + Ψ y) x))
      - (∫ x in abox n ℓ, indU ℓ 0 (x i) * q (fibre n i (fun y => t * Φ y - Ψ y) x))
    = t * ((∫ x in abox n ℓ, indU ℓ 0 (x i) * q (fibre n i (fun y => Φ y + Ψ y) x))
      - (∫ x in abox n ℓ, indU ℓ 0 (x i) * q (fibre n i (fun y => Φ y - Ψ y) x))) := by
  have hΦs : ContDiff ℝ (⊤ : ℕ∞) (fun y : X n => t * Φ y + Ψ y) := (hΦ.const_smul t).add hΨ
  have hΦd : ContDiff ℝ (⊤ : ℕ∞) (fun y : X n => t * Φ y - Ψ y) := (hΦ.const_smul t).sub hΨ
  have hΦp : ContDiff ℝ (⊤ : ℕ∞) (fun y : X n => Φ y + Ψ y) := hΦ.add hΨ
  have hΦm : ContDiff ℝ (⊤ : ℕ∞) (fun y : X n => Φ y - Ψ y) := hΦ.sub hΨ
  have I1 := hint _ hΦs
  have I2 := hint _ hΦd
  have I3 := hint _ hΦp
  have I4 := hint _ hΦm
  have hpt : ∀ x : X n,
      indU ℓ 0 (x i) * q (fibre n i (fun y => t * Φ y + Ψ y) x)
        - indU ℓ 0 (x i) * q (fibre n i (fun y => t * Φ y - Ψ y) x)
      = t * (indU ℓ 0 (x i) * q (fibre n i (fun y => Φ y + Ψ y) x)
        - indU ℓ 0 (x i) * q (fibre n i (fun y => Φ y - Ψ y) x)) := by
    intro x
    have h1 : fibre n i (fun y : X n => t * Φ y + Ψ y) x
        = fun z => t * (fibre n i Φ x z) + (fibre n i Ψ x z) := by
      funext z; rfl
    have h2 : fibre n i (fun y : X n => t * Φ y - Ψ y) x
        = fun z => t * (fibre n i Φ x z) - (fibre n i Ψ x z) := by
      funext z; rfl
    have h3 : fibre n i (fun y : X n => Φ y + Ψ y) x
        = fun z => (fibre n i Φ x z) + (fibre n i Ψ x z) := by
      funext z; rfl
    have h4 : fibre n i (fun y : X n => Φ y - Ψ y) x
        = fun z => (fibre n i Φ x z) - (fibre n i Ψ x z) := by
      funext z; rfl
    rw [h1, h2, h3, h4, ← mul_sub, ← mul_sub,
      hq t _ _ (Work.BoseFixB2.Polar.contDiff_fibre hΦ i x)
        (Work.BoseFixB2.Polar.contDiff_fibre hΨ i x)]
    ring
  rw [← MeasureTheory.integral_sub I1 I2, ← MeasureTheory.integral_sub I3 I4]
  rw [show (fun x : X n => indU ℓ 0 (x i) * q (fibre n i (fun y => t * Φ y + Ψ y) x)
        - indU ℓ 0 (x i) * q (fibre n i (fun y => t * Φ y - Ψ y) x))
      = fun x : X n => t * (indU ℓ 0 (x i) * q (fibre n i (fun y => Φ y + Ψ y) x)
        - indU ℓ 0 (x i) * q (fibre n i (fun y => Φ y - Ψ y) x)) from funext hpt]
  rw [MeasureTheory.integral_const_mul]

/-- The slot sum of a one-body word with `hpol` satisfies `hpol`. -/
theorem kinForm_slot_hpol {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {q : (EuclideanSpace ℝ (Fin 3) → ℝ) → ℝ}
    (hq : ∀ (t : ℝ) (f g : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) g →
      q (fun z => t * f z + g z) - q (fun z => t * f z - g z)
        = t * (q (fun z => f z + g z) - q (fun z => f z - g z)))
    (hint : ∀ (i : Fin n) (Ξ : X n → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ξ →
      IntegrableOn (fun x : X n => indU ℓ 0 (x i) * q (fibre n i Ξ x)) (abox n ℓ))
    (t : ℝ) {Φ Ψ : X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    (∑ i : Fin n, ∫ x in abox n ℓ, indU ℓ 0 (x i) * q (fibre n i (fun y => t * Φ y + Ψ y) x))
      - (∑ i : Fin n, ∫ x in abox n ℓ, indU ℓ 0 (x i) * q (fibre n i (fun y => t * Φ y - Ψ y) x))
    = t * ((∑ i : Fin n, ∫ x in abox n ℓ, indU ℓ 0 (x i) * q (fibre n i (fun y => Φ y + Ψ y) x))
      - (∑ i : Fin n, ∫ x in abox n ℓ, indU ℓ 0 (x i) * q (fibre n i (fun y => Φ y - Ψ y) x))) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => slot_hpol_of hℓ i hq (hint i) t hΦ hΨ)

/-! ## 5. `hpol` for the one-body word `fsT` -/

/-- `hpol` for `neuFrac`, from the abstract `hpol_of_par_nonneg` applied to the smooth states:
the parallelogram law is `Polar.FsTAux.neuFrac_parallelogram_aux`, `2`-homogeneity is
`NeuFrac.neuFrac_const_mul` and nonnegativity is `neuFrac_nonneg_smooth`. -/
theorem neuFrac_hpol {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2)
    (u : EuclideanSpace ℝ (Fin 3)) (t : ℝ) {f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => t * f z + g z)
      - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => t * f z - g z)
    = t * (Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => f z + g z)
      - Work.BoseKinLoc.neuFrac ℓ a2 u (fun z => f z - g z)) := by
  have hf' : f ∈ SmSub1 := SmSub1.mem hf
  have hg' : g ∈ SmSub1 := SmSub1.mem hg
  have hpar : ∀ x y : ↥(SmSub1),
      Work.BoseKinLoc.neuFrac ℓ a2 u ((x + y : ↥(SmSub1)) : EuclideanSpace ℝ (Fin 3) → ℝ)
        + Work.BoseKinLoc.neuFrac ℓ a2 u ((x - y : ↥(SmSub1)) : EuclideanSpace ℝ (Fin 3) → ℝ)
      = 2 * Work.BoseKinLoc.neuFrac ℓ a2 u (x : EuclideanSpace ℝ (Fin 3) → ℝ)
        + 2 * Work.BoseKinLoc.neuFrac ℓ a2 u (y : EuclideanSpace ℝ (Fin 3) → ℝ) := by
    intro x y
    rw [show ((x + y : ↥(SmSub1)) : EuclideanSpace ℝ (Fin 3) → ℝ)
          = fun z => (x : EuclideanSpace ℝ (Fin 3) → ℝ) z + (y : EuclideanSpace ℝ (Fin 3) → ℝ) z
        from rfl,
      show ((x - y : ↥(SmSub1)) : EuclideanSpace ℝ (Fin 3) → ℝ)
          = fun z => (x : EuclideanSpace ℝ (Fin 3) → ℝ) z - (y : EuclideanSpace ℝ (Fin 3) → ℝ) z
        from rfl]
    exact Work.BoseFixB2.Polar.FsTAux.neuFrac_parallelogram_aux hℓ ha2 u
      (SmSub1.contDiff x) (SmSub1.contDiff y)
  have hhom : ∀ (t : ℝ) (x : ↥(SmSub1)),
      Work.BoseKinLoc.neuFrac ℓ a2 u ((t • x : ↥(SmSub1)) : EuclideanSpace ℝ (Fin 3) → ℝ)
        = t ^ 2 * Work.BoseKinLoc.neuFrac ℓ a2 u (x : EuclideanSpace ℝ (Fin 3) → ℝ) := by
    intro t x
    rw [show ((t • x : ↥(SmSub1)) : EuclideanSpace ℝ (Fin 3) → ℝ)
        = fun z => t * (x : EuclideanSpace ℝ (Fin 3) → ℝ) z from rfl]
    exact Work.BoseKinLoc.NeuFrac.neuFrac_const_mul (le_of_lt ha2) u _
  have hnn : ∀ x : ↥(SmSub1),
      0 ≤ Work.BoseKinLoc.neuFrac ℓ a2 u (x : EuclideanSpace ℝ (Fin 3) → ℝ) :=
    fun x => neuFrac_nonneg_smooth hℓ (le_of_lt ha2) u (SmSub1.contDiff x)
  have key := hpol_of_par_nonneg (V := ↥(SmSub1))
    (Q := fun x : ↥(SmSub1) =>
      Work.BoseKinLoc.neuFrac ℓ a2 u (x : EuclideanSpace ℝ (Fin 3) → ℝ))
    hpar hhom hnn t (⟨f, hf'⟩ : ↥(SmSub1)) (⟨g, hg'⟩ : ↥(SmSub1))
  rw [show ((t • (⟨f, hf'⟩ : ↥(SmSub1)) + (⟨g, hg'⟩ : ↥(SmSub1)) : ↥(SmSub1))
          : EuclideanSpace ℝ (Fin 3) → ℝ) = fun z => t * f z + g z from rfl,
      show ((t • (⟨f, hf'⟩ : ↥(SmSub1)) - (⟨g, hg'⟩ : ↥(SmSub1)) : ↥(SmSub1))
          : EuclideanSpace ℝ (Fin 3) → ℝ) = fun z => t * f z - g z from rfl,
      show (((⟨f, hf'⟩ : ↥(SmSub1)) + (⟨g, hg'⟩ : ↥(SmSub1)) : ↥(SmSub1))
          : EuclideanSpace ℝ (Fin 3) → ℝ) = fun z => f z + g z from rfl,
      show (((⟨f, hf'⟩ : ↥(SmSub1)) - (⟨g, hg'⟩ : ↥(SmSub1)) : ↥(SmSub1))
          : EuclideanSpace ℝ (Fin 3) → ℝ) = fun z => f z - g z from rfl] at key
  exact key

/-- `hpol` for the one-body word `fsT ℓ d s εT b u`, assembled from the four summands. -/
theorem fsT_hpol {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) (t : ℝ)
    {f g : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => t * f z + g z)
      - Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => t * f z - g z)
    = t * (Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => f z + g z)
      - Work.BoseKinLoc.fsT ℓ d s εT b u (fun z => f z - g z)) := by
  have hft : Continuous (fun z : EuclideanSpace ℝ (Fin 3) => t * f z) :=
    continuous_const.mul hf.continuous
  have hQts : Work.BoseKinLoc.Qfree ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => t * f z + g z)
      = fun z => t * Work.BoseKinLoc.Qfree ℓ u f z + Work.BoseKinLoc.Qfree ℓ u g z := by
    rw [Work.BoseFixB2.Polar.FsTAux.Qfree_add hℓ u hft hg.continuous,
      Work.BoseKinLoc.Word.FsTAux.Qfree_const_mul ℓ u t f]
  have hQtd : Work.BoseKinLoc.Qfree ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => t * f z - g z)
      = fun z => t * Work.BoseKinLoc.Qfree ℓ u f z - Work.BoseKinLoc.Qfree ℓ u g z := by
    rw [Work.BoseFixB2.Polar.FsTAux.Qfree_sub hℓ u hft hg.continuous,
      Work.BoseKinLoc.Word.FsTAux.Qfree_const_mul ℓ u t f]
  have hQps : Work.BoseKinLoc.Qfree ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => f z + g z)
      = fun z => Work.BoseKinLoc.Qfree ℓ u f z + Work.BoseKinLoc.Qfree ℓ u g z :=
    Work.BoseFixB2.Polar.FsTAux.Qfree_add hℓ u hf.continuous hg.continuous
  have hQpd : Work.BoseKinLoc.Qfree ℓ u (fun z : EuclideanSpace ℝ (Fin 3) => f z - g z)
      = fun z => Work.BoseKinLoc.Qfree ℓ u f z - Work.BoseKinLoc.Qfree ℓ u g z :=
    Work.BoseFixB2.Polar.FsTAux.Qfree_sub hℓ u hf.continuous hg.continuous
  have hQfs : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.Qfree ℓ u f) := by
    have h' : Work.BoseKinLoc.Qfree ℓ u f = fun z => f z - Work.BSKinetic.bsMean ℓ u f := rfl
    rw [h']; exact hf.sub contDiff_const
  have hQgs : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseKinLoc.Qfree ℓ u g) := by
    have h' : Work.BoseKinLoc.Qfree ℓ u g = fun z => g z - Work.BSKinetic.bsMean ℓ u g := rfl
    rw [h']; exact hg.sub contDiff_const
  have hgap : Work.BoseKinLoc.gapWord ℓ b u (fun z => t * f z + g z)
        - Work.BoseKinLoc.gapWord ℓ b u (fun z => t * f z - g z)
      = t * (Work.BoseKinLoc.gapWord ℓ b u (fun z => f z + g z)
        - Work.BoseKinLoc.gapWord ℓ b u (fun z => f z - g z)) := by
    unfold Work.BoseKinLoc.gapWord
    rw [← mul_sub, ← mul_sub, gapBare_hpol hℓ u t hf hg]
    ring
  have hmom : Work.BoseKinLoc.momWord ℓ d εT b u (fun z => t * f z + g z)
        - Work.BoseKinLoc.momWord ℓ d εT b u (fun z => t * f z - g z)
      = t * (Work.BoseKinLoc.momWord ℓ d εT b u (fun z => f z + g z)
        - Work.BoseKinLoc.momWord ℓ d εT b u (fun z => f z - g z)) := by
    unfold Work.BoseKinLoc.momWord
    rw [← mul_sub, ← mul_sub, momForm_hpol (d := d) hℓ u t hf hg]
    ring
  have hmain : Work.BoseKinLoc.mainWord ℓ d s εT u (fun z => t * f z + g z)
        - Work.BoseKinLoc.mainWord ℓ d s εT u (fun z => t * f z - g z)
      = t * (Work.BoseKinLoc.mainWord ℓ d s εT u (fun z => f z + g z)
        - Work.BoseKinLoc.mainWord ℓ d s εT u (fun z => f z - g z)) := by
    have h1 := bsOneBody_hpol (ℓ := ℓ) (c := (2 * (s * ℓ))⁻¹) hℓ u t hf hg
    have h2 := bsOneBody_hpol (ℓ := ℓ) (c := (2 * (d * s * ℓ))⁻¹) hℓ u t hf hg
    unfold Work.BoseKinLoc.mainWord
    linear_combination (1 - εT) * h1 + εT * h2
  by_cases hd : d = 0
  · -- the two `(dℓ)⁻²`-weighted words vanish
    have hneu0 : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, Work.BoseKinLoc.neuWord ℓ d εT u ψ = 0 := by
      intro ψ
      simp only [Work.BoseKinLoc.neuWord, hd, zero_mul]
      rw [zero_zpow]
      · ring
      · norm_num
    have hmom0 : ∀ ψ : EuclideanSpace ℝ (Fin 3) → ℝ, Work.BoseKinLoc.momWord ℓ d εT b u ψ = 0 := by
      intro ψ
      simp only [Work.BoseKinLoc.momWord, hd, zero_mul]
      rw [zero_zpow]
      · ring
      · norm_num
    unfold Work.BoseKinLoc.fsT
    rw [hneu0 (fun z => t * f z + g z), hneu0 (fun z => t * f z - g z),
      hneu0 (fun z => f z + g z), hneu0 (fun z => f z - g z),
      hmom0 (fun z => t * f z + g z), hmom0 (fun z => t * f z - g z),
      hmom0 (fun z => f z + g z), hmom0 (fun z => f z - g z)]
    linarith [hgap, hmain]
  · have ha2 : 0 < (d * ℓ) ^ (-2 : ℤ) := by
      rw [zpow_neg]
      exact inv_pos.mpr (sq_pos_of_ne_zero (mul_ne_zero hd (ne_of_gt hℓ)))
    have hneu : Work.BoseKinLoc.neuWord ℓ d εT u (fun z => t * f z + g z)
          - Work.BoseKinLoc.neuWord ℓ d εT u (fun z => t * f z - g z)
        = t * (Work.BoseKinLoc.neuWord ℓ d εT u (fun z => f z + g z)
          - Work.BoseKinLoc.neuWord ℓ d εT u (fun z => f z - g z)) := by
      unfold Work.BoseKinLoc.neuWord
      rw [hQts, hQtd, hQps, hQpd, ← mul_sub, ← mul_sub,
        neuFrac_hpol hℓ ha2 u t hQfs hQgs]
      ring
    unfold Work.BoseKinLoc.fsT
    linarith [hneu, hgap, hmom, hmain]

/-! ## 6. `hpol` for the box word -/

/-- `hpol` for the kinetic part of the box word, obtained from `fsT_hpol` by the slot lift. -/
theorem kinFormB_hpol {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (t : ℝ)
    {Φ Ψ : X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    Work.BoseKinLoc.kinFormB n ℓ d s εT b (fun x => t * Φ x + Ψ x)
      - Work.BoseKinLoc.kinFormB n ℓ d s εT b (fun x => t * Φ x - Ψ x)
    = t * (Work.BoseKinLoc.kinFormB n ℓ d s εT b (fun x => Φ x + Ψ x)
      - Work.BoseKinLoc.kinFormB n ℓ d s εT b (fun x => Φ x - Ψ x)) := by
  have h := kinForm_slot_hpol (ℓ := ℓ) hℓ (q := fun ψ => Work.BoseKinLoc.fsT ℓ d s εT b 0 ψ)
    (fun t f g hf hg => fsT_hpol (u := 0) hℓ t hf hg)
    (fun i Ξ hΞ => Work.BoseFixB2.Sector.integrableOn_fsT_fibre_smooth (d := d) (s := s)
      (εT := εT) (b := b) hℓ i hΞ)
    t hΦ hΨ
  unfold Work.BoseKinLoc.kinFormB
  rw [← mul_sub, h]; ring

/-- **`hpol` for the frozen box word**: `wordB (t·Φ+Ψ) − wordB (t·Φ−Ψ) = t·(wordB (Φ+Ψ) − wordB (Φ−Ψ))`
on smooth states. -/
theorem wordB_hpol {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {μ : ℝ} {n : ℕ}
    (hpos : 0 < fsSide v μ)
    (hw : IntegrableOn (fun x : X n => potWordU n v (g0 v h) (fsSide v μ) μ 0 x)
      (abox n (fsSide v μ)))
    (t : ℝ) {Φ Ψ : X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    Work.BoseBoxFix.wordB v h μ n (fun x => t * Φ x + Ψ x)
        - Work.BoseBoxFix.wordB v h μ n (fun x => t * Φ x - Ψ x)
      = t * (Work.BoseBoxFix.wordB v h μ n (fun x => Φ x + Ψ x)
        - Work.BoseBoxFix.wordB v h μ n (fun x => Φ x - Ψ x)) := by
  have h1 := kinFormB_hpol (ℓ := fsSide v μ) (d := (paramsAt μ (_root_.BoseGases.a v)).d)
    (s := (paramsAt μ (_root_.BoseGases.a v)).s) (εT := (paramsAt μ (_root_.BoseGases.a v)).eT)
    (b := (paramsAt μ (_root_.BoseGases.a v)).b) hpos t hΦ hΨ
  have h2 := potInt_hpol (v := v) (g := g0 v h) (ℓ := fsSide v μ) (μ := μ) hpos hw t hΦ hΨ
  have hbf : ∀ X : X n → ℝ, Work.BoseBoxFix.wordB v h μ n X
      = Work.BoseKinLoc.kinFormB n (fsSide v μ) (paramsAt μ (_root_.BoseGases.a v)).d
          (paramsAt μ (_root_.BoseGases.a v)).s (paramsAt μ (_root_.BoseGases.a v)).eT
          (paramsAt μ (_root_.BoseGases.a v)).b X
        + ∫ x in abox n (fsSide v μ), (X x) ^ 2 * potWordU n v (g0 v h) (fsSide v μ) μ 0 x :=
    fun _ => rfl
  rw [hbf (fun x => t * Φ x + Ψ x), hbf (fun x => t * Φ x - Ψ x),
    hbf (fun x => Φ x + Ψ x), hbf (fun x => Φ x - Ψ x)]
  linarith [h1, h2]

/-! ## 7. The polarisation identity for a finite combination of sectors -/

theorem wordB_sum_secProj {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) (Work.BoseFixB2.fsSide v μ) μ 0 x) (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ))) (c : ℕ → ℝ) : Work.BoseBoxFix.wordB v h μ n (fun x => ∑ k ∈ Finset.range (n + 1), c k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x) = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), c k * c l * Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ) := by
  by_cases hpos : 0 < Work.BoseFixB2.fsSide v μ
  · -- non-degenerate box: the abstract polarisation identity on the smooth states
    have hsec : ∀ k : ℕ,
        ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ) := by
      intro k
      have hsum : ContDiff ℝ (⊤ : ℕ∞)
          (fun x => ∑ S ∈ (Finset.range n).powersetCard k,
            Work.BoseFixB2.jointProj (Work.BoseFixB2.fsSide v μ) S Φ x) :=
        ContDiff.sum (fun S _ => Work.BoseFixB2.Sector.jointProj_contDiff (n := n) hpos S hΦ)
      rw [Work.BoseFixB2.secProj, Finset.sum_fn]
      exact hsum
    have hmem : ∀ k : ℕ,
        Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ ∈ SmSub n :=
      fun k => SmSub.mem (hsec k)
    have hpar : ∀ x y : ↥(SmSub n),
        Work.BoseBoxFix.wordB v h μ n ((x + y : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
          + Work.BoseBoxFix.wordB v h μ n ((x - y : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
        = 2 * Work.BoseBoxFix.wordB v h μ n (x : Submission.BoseGases.X n → ℝ)
          + 2 * Work.BoseBoxFix.wordB v h μ n (y : Submission.BoseGases.X n → ℝ) := by
      intro x y
      rw [show ((x + y : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
            = fun z => (x : Submission.BoseGases.X n → ℝ) z
              + (y : Submission.BoseGases.X n → ℝ) z from rfl,
          show ((x - y : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
            = fun z => (x : Submission.BoseGases.X n → ℝ) z
              - (y : Submission.BoseGases.X n → ℝ) z from rfl]
      exact wordB_parallelogram hpos hw (SmSub.contDiff x) (SmSub.contDiff y)
    have hhom : ∀ (t : ℝ) (x : ↥(SmSub n)),
        Work.BoseBoxFix.wordB v h μ n ((t • x : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
          = t ^ 2 * Work.BoseBoxFix.wordB v h μ n (x : Submission.BoseGases.X n → ℝ) := by
      intro t x
      rw [show ((t • x : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
          = fun z => t * (x : Submission.BoseGases.X n → ℝ) z from rfl]
      exact wordB_smul t (SmSub.contDiff x)
    have hpol : ∀ (t : ℝ) (x y : ↥(SmSub n)),
        Work.BoseBoxFix.wordB v h μ n ((t • x + y : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
          - Work.BoseBoxFix.wordB v h μ n ((t • x - y : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
        = t * (Work.BoseBoxFix.wordB v h μ n ((x + y : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
          - Work.BoseBoxFix.wordB v h μ n
              ((x - y : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)) := by
      intro t x y
      rw [show ((t • x + y : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
            = fun z => t * (x : Submission.BoseGases.X n → ℝ) z
              + (y : Submission.BoseGases.X n → ℝ) z from rfl,
          show ((t • x - y : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
            = fun z => t * (x : Submission.BoseGases.X n → ℝ) z
              - (y : Submission.BoseGases.X n → ℝ) z from rfl,
          show ((x + y : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
            = fun z => (x : Submission.BoseGases.X n → ℝ) z
              + (y : Submission.BoseGases.X n → ℝ) z from rfl,
          show ((x - y : ↥(SmSub n)) : Submission.BoseGases.X n → ℝ)
            = fun z => (x : Submission.BoseGases.X n → ℝ) z
              - (y : Submission.BoseGases.X n → ℝ) z from rfl]
      exact wordB_hpol hpos hw t (SmSub.contDiff x) (SmSub.contDiff y)
    have key := Work.BoseFixB2.Polar.par_polarisation_hpol (V := ↥(SmSub n))
      (Q := fun x : ↥(SmSub n) =>
        Work.BoseBoxFix.wordB v h μ n (x : Submission.BoseGases.X n → ℝ))
      hpar hhom hpol (fun k : Fin (n + 1) => c k)
      (fun k : Fin (n + 1) =>
        (⟨Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ, hmem k⟩ : ↥(SmSub n)))
    -- convert the statement's sums to the `Fin (n+1)`-indexed form used by `key`
    have hgoalL : Work.BoseBoxFix.wordB v h μ n
          (fun x => ∑ k ∈ Finset.range (n + 1),
            c k * Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ x)
        = Work.BoseBoxFix.wordB v h μ n
          (∑ k : Fin (n + 1), c k •
            ((⟨Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ, hmem k⟩ : ↥(SmSub n))
              : Submission.BoseGases.X n → ℝ)) := by
      congr 1
      funext x
      rw [Finset.sum_apply]
      rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (c k •
        ((⟨Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ, hmem k⟩ : ↥(SmSub n))
          : Submission.BoseGases.X n → ℝ)) x)]
      refine Finset.sum_congr rfl (fun k _ => rfl)
    have hgoalR : (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), c k * c l *
          Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ))
        = ∑ k : Fin (n + 1), ∑ l : Fin (n + 1), c k * c l *
          ((Work.BoseBoxFix.wordB v h μ n
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ
              + Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ)
            - Work.BoseBoxFix.wordB v h μ n
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ
              - Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ)) / 4) := by
      have key' : (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), c k * c l *
            Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ))
          = ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1), c k * c l *
            ((Work.BoseBoxFix.wordB v h μ n
                (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ
                  + Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ)
              - Work.BoseBoxFix.wordB v h μ n
                (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ
                  - Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ)) / 4) := by
        refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
        rw [Work.BoseFixB2.polB]
        congr 1 <;>
          exact congrArg (fun F => Work.BoseBoxFix.wordB v h μ n F) (by funext x; rfl)
      rw [key']
      rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => (∑ l ∈ Finset.range (n + 1), c k * c l *
        ((Work.BoseBoxFix.wordB v h μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ
              + Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ)
          - Work.BoseBoxFix.wordB v h μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ
              - Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ)) / 4))) (n + 1)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← Fin.sum_univ_eq_sum_range (fun l : ℕ => (c k * c l *
        ((Work.BoseBoxFix.wordB v h μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ
              + Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ)
          - Work.BoseBoxFix.wordB v h μ n
            (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ
              - Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ)) / 4))) (n + 1)]
    rw [hgoalL, hgoalR]
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_mk, Submodule.coe_add,
      Submodule.coe_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using key
  · -- degenerate box: `wordB` (and hence `polB`) vanishes identically
    have hzero : ∀ Ξ : Submission.BoseGases.X n → ℝ, Work.BoseBoxFix.wordB v h μ n Ξ = 0 :=
      fun Ξ => Work.BoseFixB2.Polar.boxFormB_eq_zero_of_nonpos (le_of_not_gt hpos) Ξ
    rw [hzero]
    symm
    refine Finset.sum_eq_zero (fun k _ => ?_)
    refine Finset.sum_eq_zero (fun l _ => ?_)
    have hpol0 : Work.BoseFixB2.polB v h μ n
        (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
        (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) l Φ) = 0 := by
      rw [Work.BoseFixB2.polB, hzero, hzero]; ring
    rw [hpol0]; ring

end Work.BoseFixB2.Energy
