import Mathlib
import ChallengeDeps
import Submission.Work.RPB.Port.Geometry
import Submission.Work.RPB.Port.Collision
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.RPB.Port.Commons.Analysis.Complex.continuousOn_arg_div_pi_coe

open Manifold Real MeasureTheory
open scoped ContDiff ENNReal

set_option autoImplicit false
noncomputable section

namespace Work.RPB.Port.Configuration

open Work.RPB.Port.Collision
open Work.RPB.Port.Geometry

/-- The ambient space for the configuration-collision relation: an angle together with two
ordered pairs of points of the circle. -/
abbrev ConfSpace : Type := UnitAddCircle × (Circle × Circle) × (Circle × Circle)

/-- The vector joining the two curve points of an (ordered) pair. -/
def pairVec (γ : Circle → ℝ × ℝ) (p : Circle × Circle) : ℝ × ℝ := γ p.1 - γ p.2

/-- The length of the chord. -/
def lenPair (γ : Circle → ℝ × ℝ) (p : Circle × Circle) : ℝ := eucNorm (pairVec γ p)

/-- The midpoint of the chord. -/
def midPair (γ : Circle → ℝ × ℝ) (p : Circle × Circle) : ℝ × ℝ := (γ p.1 + γ p.2) / 2

/-- The doubled direction of the chord. -/
def dirPair (γ : Circle → ℝ × ℝ) (p : Circle × Circle) : UnitAddCircle := dirC (pairVec γ p)

/-- The scaling factor `1 / (n+1)`. -/
def cs (n : ℕ) : ℝ := (1 : ℝ) / ((n : ℝ) + 1)

lemma cs_pos (n : ℕ) : 0 < cs n := by
  rw [cs]; positivity

@[simp] lemma eucNorm_zero' : eucNorm (0 : ℝ × ℝ) = 0 := eucNorm_eq_zero.mpr rfl

/-! ### Continuity of the pieces -/

theorem continuous_eucNorm : Continuous eucNorm := by
  unfold eucNorm eucDot
  fun_prop

lemma continuous_pairVec {γ : Circle → ℝ × ℝ} (hγ : Continuous γ) : Continuous (pairVec γ) :=
  (hγ.comp continuous_fst).sub (hγ.comp continuous_snd)

lemma continuous_lenPair {γ : Circle → ℝ × ℝ} (hγ : Continuous γ) : Continuous (lenPair γ) :=
  continuous_eucNorm.comp (continuous_pairVec hγ)

lemma continuous_midPair {γ : Circle → ℝ × ℝ} (hγ : Continuous γ) : Continuous (midPair γ) := by
  unfold midPair
  exact ((hγ.comp continuous_fst).add (hγ.comp continuous_snd)).div_const 2

/-- The map `z ↦ arg z / π` into `ℝ/ℤ` is continuous away from the origin; hence so is the
doubled direction. -/
lemma continuousOn_dirC : ContinuousOn dirC {x : ℝ × ℝ | x ≠ 0} := by
  have hg : ContinuousOn (fun z : ℂ => ((z.arg / Real.pi : ℝ) : UnitAddCircle))
      {z : ℂ | z ≠ 0} :=
    Work.RPB.Port.Commons.Analysis.Complex.continuousOn_arg_div_pi_coe
  have hφ : Continuous (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) :=
    Complex.equivRealProdCLM.symm.continuous
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))
      {x : ℝ × ℝ | x ≠ 0} {z : ℂ | z ≠ 0} := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    intro h
    refine hp (Prod.ext ?_ ?_)
    · have := congrArg Complex.re h; simpa using this
    · have := congrArg Complex.im h; simpa using this
  have hcomp := hg.comp hφ.continuousOn hmaps
  have hfun : ((fun z : ℂ => ((z.arg / Real.pi : ℝ) : UnitAddCircle)) ∘
      (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))) = dirC := rfl
  rwa [hfun] at hcomp

lemma continuousOn_dirPair {γ : Circle → ℝ × ℝ} (hγ : Continuous γ) :
    ContinuousOn (dirPair γ) {p : Circle × Circle | pairVec γ p ≠ 0} :=
  continuousOn_dirC.comp (continuous_pairVec hγ).continuousOn (fun _ hp => hp)

/-- The auxiliary (closed) set whose `n`-th instance collects configuration collisions witnessed
by chords of length `≥ 1/(n+1)`. -/
def Sset (γ : Circle → ℝ × ℝ) (n : ℕ) : Set ConfSpace :=
  ((({t | cs n ≤ lenPair γ t.2.1} ∩ {t | cs n ≤ lenPair γ t.2.2}) ∩
      {t | dirPair γ t.2.1 - (dirPair γ t.2.2 + t.1) = 0}) ∩
    {t | midPair γ t.2.1 = midPair γ t.2.2}) ∩
    {t | lenPair γ t.2.1 = lenPair γ t.2.2}

theorem isClosed_Sset (γ : Circle → ℝ × ℝ) (hγ : Continuous γ) (n : ℕ) :
    IsClosed (Sset γ n) := by
  have hlen1 : Continuous (fun t : ConfSpace => lenPair γ t.2.1) :=
    (continuous_lenPair hγ).comp (continuous_fst.comp continuous_snd)
  have hlen2 : Continuous (fun t : ConfSpace => lenPair γ t.2.2) :=
    (continuous_lenPair hγ).comp (continuous_snd.comp continuous_snd)
  have hmid1 : Continuous (fun t : ConfSpace => midPair γ t.2.1) :=
    (continuous_midPair hγ).comp (continuous_fst.comp continuous_snd)
  have hmid2 : Continuous (fun t : ConfSpace => midPair γ t.2.2) :=
    (continuous_midPair hγ).comp (continuous_snd.comp continuous_snd)
  have hF1 : Continuous (fun t : ConfSpace => t.2.1) := continuous_fst.comp continuous_snd
  have hF2 : Continuous (fun t : ConfSpace => t.2.2) := continuous_snd.comp continuous_snd
  have hF1s : ContinuousOn (fun t : ConfSpace => t.2.1) {t | cs n ≤ lenPair γ t.2.1} :=
    hF1.continuousOn.mono (fun _ _ => trivial)
  have hF2s : ContinuousOn (fun t : ConfSpace => t.2.2) {t | cs n ≤ lenPair γ t.2.2} :=
    hF2.continuousOn.mono (fun _ _ => trivial)
  have hA : IsClosed ({t : ConfSpace | cs n ≤ lenPair γ t.2.1} ∩
      {t | cs n ≤ lenPair γ t.2.2}) :=
    (isClosed_le continuous_const hlen1).inter (isClosed_le continuous_const hlen2)
  have hdir1 : ContinuousOn (fun t : ConfSpace => dirPair γ t.2.1) {t | cs n ≤ lenPair γ t.2.1} := by
    have hmaps : Set.MapsTo (fun t : ConfSpace => t.2.1) {t | cs n ≤ lenPair γ t.2.1}
        {p : Circle × Circle | pairVec γ p ≠ 0} := by
      intro t ht
      simp only [Set.mem_setOf_eq] at ht ⊢
      intro h0
      have hpos : 0 < lenPair γ t.2.1 := lt_of_lt_of_le (cs_pos n) ht
      rw [lenPair, h0, eucNorm_zero'] at hpos
      exact lt_irrefl 0 hpos
    exact (continuousOn_dirPair hγ).comp hF1s hmaps
  have hdir2 : ContinuousOn (fun t : ConfSpace => dirPair γ t.2.2) {t | cs n ≤ lenPair γ t.2.2} := by
    have hmaps : Set.MapsTo (fun t : ConfSpace => t.2.2) {t | cs n ≤ lenPair γ t.2.2}
        {p : Circle × Circle | pairVec γ p ≠ 0} := by
      intro t ht
      simp only [Set.mem_setOf_eq] at ht ⊢
      intro h0
      have hpos : 0 < lenPair γ t.2.2 := lt_of_lt_of_le (cs_pos n) ht
      rw [lenPair, h0, eucNorm_zero'] at hpos
      exact lt_irrefl 0 hpos
    exact (continuousOn_dirPair hγ).comp hF2s hmaps
  have hsub : ContinuousOn (fun t : ConfSpace =>
      dirPair γ t.2.1 - (dirPair γ t.2.2 + t.1))
      ({t | cs n ≤ lenPair γ t.2.1} ∩ {t | cs n ≤ lenPair γ t.2.2}) :=
    (hdir1.mono Set.inter_subset_left).sub
      ((hdir2.mono Set.inter_subset_right).add continuous_fst.continuousOn)
  have hC3 : IsClosed (({t : ConfSpace | cs n ≤ lenPair γ t.2.1} ∩
      {t | cs n ≤ lenPair γ t.2.2}) ∩
      {t | dirPair γ t.2.1 - (dirPair γ t.2.2 + t.1) = 0}) := by
    have h := hsub.preimage_isClosed_of_isClosed hA (isClosed_singleton (x := (0 : UnitAddCircle)))
    simpa only [Set.preimage, Set.mem_setOf_eq, Set.mem_singleton_iff] using h
  have hC1 : IsClosed {t : ConfSpace | midPair γ t.2.1 = midPair γ t.2.2} := isClosed_eq hmid1 hmid2
  have hC2 : IsClosed {t : ConfSpace | lenPair γ t.2.1 = lenPair γ t.2.2} := isClosed_eq hlen1 hlen2
  exact (hC3.inter hC1).inter hC2

end Work.RPB.Port.Configuration
