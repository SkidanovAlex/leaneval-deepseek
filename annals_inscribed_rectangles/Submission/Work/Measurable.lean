import Mathlib
import ChallengeDeps
import Submission.Work.Configuration
import Submission.Commons.Analysis.Complex.continuousOn_arg_div_pi_coe

open InscribedRectangles
open Manifold Real MeasureTheory
open scoped ContDiff ENNReal

set_option autoImplicit false
noncomputable section

namespace Submission.Configuration

open Submission.Collision
open Submission.Geometry

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

lemma muOrd_eq (γ : Circle → ℝ × ℝ) (p : Circle × Circle) :
    muOrd γ p = (midPair γ p, dirPair γ p, lenPair γ p) := rfl

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
    Commons.Analysis.Complex.continuousOn_arg_div_pi_coe
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

/-- `GoodC γ` is the countable union of the (compact) images of the `Sset`. -/
theorem goodC_eq_iUnion (γ : Circle → ℝ × ℝ) (hγ : Continuous γ) (hinj : Function.Injective γ) :
    GoodC γ = ⋃ n, Prod.fst '' (Sset γ n) := by
  ext u
  constructor
  · rintro ⟨x, y, x', y', hxy, hx'y', heq⟩
    have hp : 0 < lenPair γ (x, y) := by
      rw [lenPair]
      refine eucNorm_pos ?_
      rw [pairVec, sub_ne_zero]
      exact fun h => hxy (hinj h)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hp
    have hlen_eq : lenPair γ (x, y) = lenPair γ (x', y') := by
      have h := congrArg (fun z : (ℝ × ℝ) × UnitAddCircle × ℝ => z.2.2) heq
      simpa only [muOrd_eq, actC] using h
    have hmid_eq : midPair γ (x, y) = midPair γ (x', y') := by
      have h := congrArg (fun z : (ℝ × ℝ) × UnitAddCircle × ℝ => z.1) heq
      simpa only [muOrd_eq, actC] using h
    have hdir_eq : dirPair γ (x, y) = dirPair γ (x', y') + u := by
      have h := congrArg (fun z : (ℝ × ℝ) × UnitAddCircle × ℝ => z.2.1) heq
      simpa only [muOrd_eq, actC] using h
    refine Set.mem_iUnion.mpr ⟨n, (u, (x, y), (x', y')), ?_, rfl⟩
    simp only [Sset, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨⟨⟨⟨by rw [cs]; exact le_of_lt hn, by rw [cs]; exact le_of_lt (hlen_eq ▸ hn)⟩,
      sub_eq_zero.mpr hdir_eq⟩, hmid_eq⟩, hlen_eq⟩
  · intro hu
    obtain ⟨n, ht⟩ := Set.mem_iUnion.mp hu
    obtain ⟨t, htS, ht1⟩ := ht
    rw [← ht1]
    simp only [Sset, Set.mem_inter_iff, Set.mem_setOf_eq] at htS
    obtain ⟨⟨⟨⟨hA1, hA2⟩, hB3⟩, hB1⟩, hB2⟩ := htS
    have hp1 : 0 < lenPair γ t.2.1 := lt_of_lt_of_le (cs_pos n) hA1
    have hz1 : pairVec γ t.2.1 ≠ 0 := by
      intro h0
      rw [lenPair, h0, eucNorm_zero'] at hp1
      exact lt_irrefl 0 hp1
    have hp2 : 0 < lenPair γ t.2.2 := lt_of_lt_of_le (cs_pos n) hA2
    have hz2 : pairVec γ t.2.2 ≠ 0 := by
      intro h0
      rw [lenPair, h0, eucNorm_zero'] at hp2
      exact lt_irrefl 0 hp2
    have hxy : t.2.1.1 ≠ t.2.1.2 := fun h => hz1 (by rw [pairVec, h, sub_self])
    have hx'y' : t.2.2.1 ≠ t.2.2.2 := fun h => hz2 (by rw [pairVec, h, sub_self])
    have hdir : dirPair γ t.2.1 = dirPair γ t.2.2 + Prod.fst t := sub_eq_zero.mp hB3
    refine ⟨t.2.1.1, t.2.1.2, t.2.2.1, t.2.2.2, hxy, hx'y', ?_⟩
    rw [muOrd_eq, muOrd_eq, actC]
    exact Prod.ext hB1 (Prod.ext hdir hB2)

/-- **Measurability of `GoodC γ`**: it is a countable union of compact sets. -/
theorem measurableSet_GoodC (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) : MeasurableSet (GoodC γ) := by
  have hγc : Continuous γ := hγ.isImmersion.contMDiff.continuous
  have hinj : Function.Injective γ := hγ.isEmbedding.injective
  rw [goodC_eq_iUnion γ hγc hinj]
  refine MeasurableSet.iUnion fun n => ?_
  exact ((isClosed_Sset γ hγc n).isCompact.image continuous_fst).isClosed.measurableSet

/-- **Theorem 1 now reduces to the single measure bound** `μ(GoodC γ) ≥ 1/3` (the paper's
Theorem 3).  Measurability of `GoodC γ` is now a theorem, not a hypothesis. -/
theorem theorem_1_of_GoodC_measure (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (h : (1 / 3 : ℝ) ≤ volume.real (GoodC γ)) : volume (X γ) ≥ 1 / 3 :=
  theorem_1_of_GoodC hγ (measurableSet_GoodC γ hγ) h

end Submission.Configuration
