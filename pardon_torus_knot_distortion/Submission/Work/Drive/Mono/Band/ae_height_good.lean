import Mathlib
import Submission.Work.Drive.EpsForm.goodHeight_exists
import Submission.Work.Drive.Generic.ae_height_morse
import Submission.Work.Smooth.Morse.Immersion.isImmersion
import Submission.Work.Drive.Mono.Band.critBranch_euclid
import Submission.Work.Drive.Mono.Band.fderiv_branchHeight_euclid
import Submission.Work.Drive.Mono.Band.volume_zeroSet_eq_zero
import Submission.Work.Drive.Mono.Band.finite_critSet_isCompact
import Submission.Work.Drive.Mono.Band.no_crit_off_isCompact

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped Topology RealInnerProductSpace
open MeasureTheory Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Drive.Mono.Band
namespace Aeh

noncomputable section

/-! ## Definitions -/

/-- The height in direction `n`. -/
abbrev hgt (ψ : Submission.Diffeo) (n : R3) : ℝ × ℝ → ℝ := Work.Drive.EpsForm.heightOf ψ n

/-- `n` is *Morse*: every critical point of the height is nondegenerate. -/
def MorseAt (ψ : Submission.Diffeo) (n : R3) : Prop :=
  ∀ p : ℝ × ℝ, fderiv ℝ (hgt ψ n) p = 0 →
    Function.Injective (fderiv ℝ (fderiv ℝ (hgt ψ n)) p)

/-- `n` is *bad*: two distinct points of the surface are critical points of the height with the same
value. -/
def BadAt (ψ : Submission.Diffeo) (n : R3) : Prop :=
  ∃ p p' : ℝ × ℝ, fderiv ℝ (hgt ψ n) p = 0 ∧ fderiv ℝ (hgt ψ n) p' = 0 ∧
    hgt ψ n p = hgt ψ n p' ∧ Work.BoxShrink.Pinch.par ψ p ≠ Work.BoxShrink.Pinch.par ψ p'

lemma hgt_contDiff_two (ψ : Submission.Diffeo) (n : R3) : ContDiff ℝ 2 (hgt ψ n) :=
  Work.Drive.EpsForm.heightOf_contDiff_two ψ n

/-! ## Periodicity -/

lemma hgt_periodic (ψ : Submission.Diffeo) (n : R3) (k m : ℤ) (p : ℝ × ℝ) :
    hgt ψ n (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) = hgt ψ n p := by
  have h := Work.Drive.EpsForm.heightOf_add_shift ψ n (-k) (-m) p
  have hargs : p + (((-k : ℤ) : ℝ) * (2 * Real.pi), ((-m : ℤ) : ℝ) * (2 * Real.pi))
      = (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> push_cast <;> ring
  rw [← hargs]
  exact h

lemma fderiv_hgt_periodic (ψ : Submission.Diffeo) (n : R3) (k m : ℤ) (p : ℝ × ℝ) :
    fderiv ℝ (hgt ψ n) (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
      = fderiv ℝ (hgt ψ n) p :=
  Work.Drive.EpsForm.fderiv_heightOf_periodic ψ n k m p

lemma fderiv_fderiv_hgt_periodic (ψ : Submission.Diffeo) (n : R3) (k m : ℤ) (p : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (hgt ψ n))
        (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
      = fderiv ℝ (fderiv ℝ (hgt ψ n)) p :=
  Work.Drive.EpsForm.fderiv_fderiv_heightOf_periodic ψ n k m p

lemma par_periodic_sub (ψ : Submission.Diffeo) (k m : ℤ) (p : ℝ × ℝ) :
    Work.BoxShrink.Pinch.par ψ (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
      = Work.BoxShrink.Pinch.par ψ p :=
  Work.Drive.EpsForm.par_periodic ψ k m p

lemma par_eq_iff' (ψ : Submission.Diffeo) (x x' : ℝ × ℝ) :
    Work.BoxShrink.Pinch.par ψ x = Work.BoxShrink.Pinch.par ψ x' ↔
      ∃ k m : ℤ, x.1 = x'.1 + (k : ℝ) * (2 * Real.pi) ∧
        x.2 = x'.2 + (m : ℝ) * (2 * Real.pi) :=
  Work.Drive.EpsForm.par_eq_iff ψ x x'

/-! ## The fundamental box -/

/-- The translate `[a, a + 2π] × [b, b + 2π]` of the standard fundamental square. -/
def boxK (a b : ℝ) : Set (ℝ × ℝ) := Set.Icc a (a + 2 * Real.pi) ×ˢ Set.Icc b (b + 2 * Real.pi)

lemma isCompact_boxK (a b : ℝ) : IsCompact (boxK a b) := isCompact_Icc.prod isCompact_Icc

/-- Every real number has a translate into `[a, a + 2π]` by an integer multiple of `2π`. -/
lemma exists_int_sub_mem_Icc (x a : ℝ) :
    ∃ k : ℤ, x - (k : ℝ) * (2 * Real.pi) ∈ Set.Icc a (a + 2 * Real.pi) := by
  have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨⌊(x - a) / (2 * Real.pi)⌋, ?_, ?_⟩
  · have h : ((⌊(x - a) / (2 * Real.pi)⌋ : ℤ) : ℝ) ≤ (x - a) / (2 * Real.pi) := Int.floor_le _
    have h' := (le_div_iff₀ h2).mp h
    linarith
  · have h : (x - a) / (2 * Real.pi) < ((⌊(x - a) / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have h' := (div_lt_iff₀ h2).mp h
    linarith

/-- Every point of the plane has a translate in the box `boxK a b`. -/
lemma exists_sub_mem_boxK (a b : ℝ) (p : ℝ × ℝ) :
    ∃ k m : ℤ, (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) ∈ boxK a b := by
  obtain ⟨k, hk⟩ := exists_int_sub_mem_Icc p.1 a
  obtain ⟨m, hm⟩ := exists_int_sub_mem_Icc p.2 b
  exact ⟨k, m, hk, hm⟩

/-- There is a point of `(0, 2π)` avoiding a finite set. -/
lemma exists_mem_Ioo_notMem_finset (S : Finset ℝ) :
    ∃ a : ℝ, a ∈ Set.Ioo 0 (2 * Real.pi) ∧ ∀ x ∈ S, x ≠ a := by
  by_contra h
  push Not at h
  have hsub : Set.Ioo (0 : ℝ) (2 * Real.pi) ⊆ (S : Set ℝ) := by
    intro x hx
    obtain ⟨s, hs, hsa⟩ := h x hx
    exact Finset.mem_coe.mpr (hsa ▸ hs)
  exact Set.Ioo_infinite (by positivity : (0 : ℝ) < 2 * Real.pi)
    (Set.Finite.subset S.finite_toSet hsub)

/-- The first coordinate of a critical point is never congruent to `a` modulo `2π`. -/
lemma crit_coord_ne {g : ℝ × ℝ → ℝ} {a : ℝ} (ha : a ∈ Set.Ioo 0 (2 * Real.pi))
    (X0 : Finset (ℝ × ℝ))
    (hX0 : ∀ p : ℝ × ℝ, p ∈ X0 ↔ p ∈ boxK 0 0 ∧ fderiv ℝ g p = 0)
    (hper : ∀ k m : ℤ, ∀ p : ℝ × ℝ,
      fderiv ℝ g (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
        = fderiv ℝ g p)
    (havoid : ∀ x ∈ X0.image Prod.fst, x ≠ a) :
    ∀ p : ℝ × ℝ, fderiv ℝ g p = 0 → ∀ j : ℤ, p.1 ≠ a + (j : ℝ) * (2 * Real.pi) := by
  intro p hp j hpj
  obtain ⟨k, m, hk⟩ := exists_sub_mem_boxK 0 0 p
  have hcrit : fderiv ℝ g (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) = 0 := by
    rw [hper]; exact hp
  have hmem : (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) ∈ X0 :=
    (hX0 _).mpr ⟨hk, hcrit⟩
  have h1 : p.1 - (k : ℝ) * (2 * Real.pi) = a + ((j - k : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hpj]; push_cast; ring
  have h2 : (0 : ℝ) ≤ p.1 - (k : ℝ) * (2 * Real.pi) ∧
      p.1 - (k : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by
    refine ⟨hk.1.1, ?_⟩
    simpa using hk.1.2
  have hjk : (j - k : ℤ) = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (j - k : ℤ) ≤ -1 := by omega
      have hle' : ((j - k : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hle
      nlinarith [ha.1, ha.2, h2.1, h2.2, h1]
    · have hge : (1 : ℤ) ≤ j - k := by omega
      have hge' : (1 : ℝ) ≤ ((j - k : ℤ) : ℝ) := by exact_mod_cast hge
      nlinarith [ha.1, ha.2, h2.1, h2.2, h1]
  have hcoord : (p.1 - (k : ℝ) * (2 * Real.pi)) = a := by
    rw [h1, hjk]; push_cast; ring
  exact (havoid a (Finset.mem_image.mpr ⟨_, hmem, hcoord⟩)) rfl

lemma crit_coord_ne' {g : ℝ × ℝ → ℝ} {b : ℝ} (hb : b ∈ Set.Ioo 0 (2 * Real.pi))
    (X0 : Finset (ℝ × ℝ))
    (hX0 : ∀ p : ℝ × ℝ, p ∈ X0 ↔ p ∈ boxK 0 0 ∧ fderiv ℝ g p = 0)
    (hper : ∀ k m : ℤ, ∀ p : ℝ × ℝ,
      fderiv ℝ g (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
        = fderiv ℝ g p)
    (havoid : ∀ x ∈ X0.image Prod.snd, x ≠ b) :
    ∀ p : ℝ × ℝ, fderiv ℝ g p = 0 → ∀ j : ℤ, p.2 ≠ b + (j : ℝ) * (2 * Real.pi) := by
  intro p hp j hpj
  obtain ⟨k, m, hk⟩ := exists_sub_mem_boxK 0 0 p
  have hcrit : fderiv ℝ g (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) = 0 := by
    rw [hper]; exact hp
  have hmem : (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) ∈ X0 :=
    (hX0 _).mpr ⟨hk, hcrit⟩
  have h1 : p.2 - (m : ℝ) * (2 * Real.pi) = b + ((j - m : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hpj]; push_cast; ring
  have h2 : (0 : ℝ) ≤ p.2 - (m : ℝ) * (2 * Real.pi) ∧
      p.2 - (m : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by
    refine ⟨hk.2.1, ?_⟩
    simpa using hk.2.2
  have hjk : (j - m : ℤ) = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (j - m : ℤ) ≤ -1 := by omega
      have hle' : ((j - m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast hle
      nlinarith [hb.1, hb.2, h2.1, h2.2, h1]
    · have hge : (1 : ℤ) ≤ j - m := by omega
      have hge' : (1 : ℝ) ≤ ((j - m : ℤ) : ℝ) := by exact_mod_cast hge
      nlinarith [hb.1, hb.2, h2.1, h2.2, h1]
  have hcoord : (p.2 - (m : ℝ) * (2 * Real.pi)) = b := by
    rw [h1, hjk]; push_cast; ring
  exact (havoid b (Finset.mem_image.mpr ⟨_, hmem, hcoord⟩)) rfl

/-- Distinct points in the interior of the box are not lattice translates, hence have distinct
images on the surface. -/
lemma par_ne_of_mem_Ioo (ψ : Submission.Diffeo) {a b : ℝ} {x y : ℝ × ℝ}
    (hx : x.1 ∈ Set.Ioo a (a + 2 * Real.pi)) (hx' : x.2 ∈ Set.Ioo b (b + 2 * Real.pi))
    (hy : y.1 ∈ Set.Ioo a (a + 2 * Real.pi)) (hy' : y.2 ∈ Set.Ioo b (b + 2 * Real.pi))
    (hne : x ≠ y) : Work.BoxShrink.Pinch.par ψ x ≠ Work.BoxShrink.Pinch.par ψ y := by
  intro hpar
  obtain ⟨k, m, hk1, hk2⟩ := (par_eq_iff' ψ x y).mp hpar
  have hk : k = 0 := by
    have h1 : x.1 - y.1 = (k : ℝ) * (2 * Real.pi) := by linarith
    have h2 : |x.1 - y.1| < 2 * Real.pi := by
      rw [abs_lt]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have h3 : |(k : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
      rw [h1, abs_mul, abs_of_pos (show (0:ℝ) < 2 * Real.pi by positivity)] at h2
      simpa using h2
    have h4 : |(k : ℝ)| < 1 := by nlinarith [Real.pi_pos]
    rw [abs_lt] at h4
    have h6 : (-1 : ℤ) < k := by exact_mod_cast h4.1
    have h7 : k < (1 : ℤ) := by exact_mod_cast h4.2
    omega
  have hm : m = 0 := by
    have h1 : x.2 - y.2 = (m : ℝ) * (2 * Real.pi) := by linarith
    have h2 : |x.2 - y.2| < 2 * Real.pi := by
      rw [abs_lt]; constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
    have h3 : |(m : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
      rw [h1, abs_mul, abs_of_pos (show (0:ℝ) < 2 * Real.pi by positivity)] at h2
      simpa using h2
    have h4 : |(m : ℝ)| < 1 := by nlinarith [Real.pi_pos]
    rw [abs_lt] at h4
    have h6 : (-1 : ℤ) < m := by exact_mod_cast h4.1
    have h7 : m < (1 : ℤ) := by exact_mod_cast h4.2
    omega
  rw [hk] at hk1; rw [hm] at hk2
  simp only [Int.cast_zero, zero_mul, add_zero] at hk1 hk2
  exact hne (Prod.ext hk1 hk2)


/-! ## The box adapted to a Morse direction -/

lemma mem_Ioo_of_mem_boxK {g : ℝ × ℝ → ℝ} {a b : ℝ}
    (hnoa : ∀ p : ℝ × ℝ, fderiv ℝ g p = 0 → ∀ j : ℤ, p.1 ≠ a + (j : ℝ) * (2 * Real.pi))
    (hbno : ∀ p : ℝ × ℝ, fderiv ℝ g p = 0 → ∀ j : ℤ, p.2 ≠ b + (j : ℝ) * (2 * Real.pi))
    {x : ℝ × ℝ} (hx : x ∈ boxK a b) (hxc : fderiv ℝ g x = 0) :
    x.1 ∈ Set.Ioo a (a + 2 * Real.pi) ∧ x.2 ∈ Set.Ioo b (b + 2 * Real.pi) := by
  refine ⟨⟨lt_of_le_of_ne hx.1.1 (Ne.symm ?_), lt_of_le_of_ne hx.1.2 ?_⟩,
    ⟨lt_of_le_of_ne hx.2.1 (Ne.symm ?_), lt_of_le_of_ne hx.2.2 ?_⟩⟩
  · simpa using hnoa x hxc 0
  · simpa using hnoa x hxc 1
  · simpa using hbno x hxc 0
  · simpa using hbno x hxc 1

lemma exists_box_data (ψ : Submission.Diffeo) {n₀ : R3} (hM : MorseAt ψ n₀) :
    ∃ (a b : ℝ) (X : Finset (ℝ × ℝ)),
      (∀ x ∈ X, x.1 ∈ Set.Ioo a (a + 2 * Real.pi) ∧ x.2 ∈ Set.Ioo b (b + 2 * Real.pi)) ∧
      (∀ p : ℝ × ℝ, p ∈ X ↔ p ∈ boxK a b ∧ fderiv ℝ (hgt ψ n₀) p = 0) ∧
      (∀ x ∈ X, ∀ x' ∈ X, x ≠ x' →
        Work.BoxShrink.Pinch.par ψ x ≠ Work.BoxShrink.Pinch.par ψ x') := by
  classical
  have hcd : ContDiff ℝ 2 (hgt ψ n₀) := hgt_contDiff_two ψ n₀
  have hfin0 : (boxK 0 0 ∩ {p : ℝ × ℝ | fderiv ℝ (hgt ψ n₀) p = 0}).Finite :=
    finite_critSet_isCompact hcd hM (isCompact_boxK 0 0)
  let X0 : Finset (ℝ × ℝ) := hfin0.toFinset
  have hX0 : ∀ p : ℝ × ℝ, p ∈ X0 ↔ p ∈ boxK 0 0 ∧ fderiv ℝ (hgt ψ n₀) p = 0 := by
    intro p
    simp only [X0, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_ofPred_eq]
  obtain ⟨a, ha, haavoid⟩ := exists_mem_Ioo_notMem_finset (X0.image Prod.fst)
  obtain ⟨b, hb, hbavoid⟩ := exists_mem_Ioo_notMem_finset (X0.image Prod.snd)
  have hnoa := crit_coord_ne ha X0 hX0 (fun k m p => fderiv_hgt_periodic ψ n₀ k m p) haavoid
  have hbno := crit_coord_ne' hb X0 hX0 (fun k m p => fderiv_hgt_periodic ψ n₀ k m p) hbavoid
  have hfinK : (boxK a b ∩ {p : ℝ × ℝ | fderiv ℝ (hgt ψ n₀) p = 0}).Finite :=
    finite_critSet_isCompact hcd hM (isCompact_boxK a b)
  let X : Finset (ℝ × ℝ) := hfinK.toFinset
  have hXmem : ∀ p : ℝ × ℝ, p ∈ X ↔ p ∈ boxK a b ∧ fderiv ℝ (hgt ψ n₀) p = 0 := by
    intro p
    simp only [X, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_ofPred_eq]
  refine ⟨a, b, X, ?_, hXmem, ?_⟩
  · intro x hx
    exact mem_Ioo_of_mem_boxK hnoa hbno ((hXmem x).mp hx).1 ((hXmem x).mp hx).2
  · intro x hx x' hx' hne hpar
    obtain ⟨hxK, hxc⟩ := (hXmem x).mp hx
    obtain ⟨hx'K, hx'c⟩ := (hXmem x').mp hx'
    obtain ⟨h1, h2⟩ := mem_Ioo_of_mem_boxK hnoa hbno hxK hxc
    obtain ⟨h3, h4⟩ := mem_Ioo_of_mem_boxK hnoa hbno hx'K hx'c
    exact par_ne_of_mem_Ioo ψ h1 h2 h3 h4 hne hpar

/-! ## The local nullity of the bad set -/

/-- The joint height `(n, q) ↦ ⟪n, par ψ q⟫`. -/
def jHeight (ψ : Submission.Diffeo) : R3 × (ℝ × ℝ) → ℝ :=
  fun w => inner ℝ w.1 (Work.BoxShrink.Pinch.par ψ w.2)

lemma jHeight_contDiff (ψ : Submission.Diffeo) :
    ContDiff ℝ (1 : WithTop ℕ∞) (jHeight ψ) := by
  have h1 : ContDiff ℝ (1 : WithTop ℕ∞)
      (fun w : R3 × (ℝ × ℝ) => (innerSL ℝ) w.1) :=
    (ContinuousLinearMap.contDiff (innerSL ℝ)).comp contDiff_fst
  have h2 : ContDiff ℝ (1 : WithTop ℕ∞)
      (fun w : R3 × (ℝ × ℝ) => Work.BoxShrink.Pinch.par ψ w.2) :=
    (((Work.Smooth.Morse.param_contDiff ψ)).of_le (WithTop.coe_le_coe.mpr le_top)).comp
      contDiff_snd
  exact h1.clm_apply h2

lemma contDiffOn_pair_comp {F : R3 × (ℝ × ℝ) → ℝ} (hF : ContDiff ℝ 1 F) {V : Set R3}
    {yy : R3 → ℝ × ℝ} (hcd : ContDiffOn ℝ 1 yy V) :
    ContDiffOn ℝ 1 (fun n : R3 => F (n, yy n)) V :=
  hF.comp_contDiffOn (contDiffOn_id.prodMk hcd)

/-- The height along a branch of critical points is `C¹` in the direction. -/
lemma contDiffOn_branchHeight (ψ : Submission.Diffeo) {V : Set R3} {yy : R3 → ℝ × ℝ}
    (hcd : ContDiffOn ℝ 1 yy V) :
    ContDiffOn ℝ 1 (fun n : R3 => hgt ψ n (yy n)) V :=
  contDiffOn_pair_comp (jHeight_contDiff ψ) hcd

lemma innerSL_eq_zero {v : R3} (h : (innerSL ℝ) v = 0) : v = 0 := by
  have h1 : inner ℝ v v = 0 := by
    have h' := congrArg (fun L : R3 →L[ℝ] ℝ => L v) h
    simpa [innerSL_apply_apply] using h'
  have h2 : ‖v‖ ^ 2 = 0 := by rw [← real_inner_self_eq_norm_sq]; exact h1
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h2)

lemma innerSL_injective : Function.Injective (fun v : R3 => (innerSL ℝ) v) := by
  intro v w h
  have h' : (innerSL ℝ) v = (innerSL ℝ) w := h
  have h0 : (innerSL ℝ) (v - w) = 0 := by rw [map_sub, h', sub_self]
  have h1 := innerSL_eq_zero h0
  rwa [sub_eq_zero] at h1

theorem badSet_locally_null (ψ : Submission.Diffeo) {n₀ : R3} (hM : MorseAt ψ n₀) :
    ∃ U : Set R3, U ∈ 𝓝 n₀ ∧ (volume : Measure R3) (U ∩ {n | BadAt ψ n}) = 0 := by
  classical
  obtain ⟨a, b, X, hXint, hXmem, hXne⟩ := exists_box_data ψ hM
  -- ## 1. branches of critical points through the elements of `X`
  have hbr : ∀ z : {x // x ∈ X}, ∃ (V : Set R3) (yy : R3 → ℝ × ℝ) (r : ℝ),
      IsOpen V ∧ n₀ ∈ V ∧ 0 < r ∧ yy n₀ = z.1 ∧ ContDiffOn ℝ 1 yy V ∧
      (∀ n ∈ V, fderiv ℝ (hgt ψ n) (yy n) = 0) ∧
      (∀ n ∈ V, ∀ p : ℝ × ℝ, ‖p - z.1‖ < r →
        fderiv ℝ (hgt ψ n) p = 0 → p = yy n) := by
    intro z
    have hz : fderiv ℝ (hgt ψ n₀) z.1 = 0 := ((hXmem z.1).mp z.2).2
    exact critBranch_euclid ψ n₀ hz (hM z.1 hz)
  choose V yy rr hVopen hVmem hrrpos hyy0 hyycd hyycrit hyyuniq using hbr
  -- ## 2. the branches stay in the interior of the box
  have hint : ∀ z : {x // x ∈ X}, ∃ W : Set R3, IsOpen W ∧ n₀ ∈ W ∧
      ∀ n ∈ W, (yy z n).1 ∈ Set.Ioo a (a + 2 * Real.pi) ∧
        (yy z n).2 ∈ Set.Ioo b (b + 2 * Real.pi) := by
    intro z
    have hzint := hXint z.1 z.2
    have hcont : ContinuousAt (yy z) n₀ :=
      (((hyycd z).continuousOn).continuousAt ((hVopen z).mem_nhds (hVmem z)))
    set ε : ℝ := min (min (z.1.1 - a) (a + 2 * Real.pi - z.1.1))
      (min (z.1.2 - b) (b + 2 * Real.pi - z.1.2)) with hεdef
    have hε : 0 < ε := by
      rw [hεdef]
      exact lt_min (lt_min (by linarith [hzint.1.1]) (by linarith [hzint.1.2]))
        (lt_min (by linarith [hzint.2.1]) (by linarith [hzint.2.2]))
    have hε1 : ε ≤ z.1.1 - a := le_trans (min_le_left _ _) (min_le_left _ _)
    have hε2 : ε ≤ a + 2 * Real.pi - z.1.1 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hε3 : ε ≤ z.1.2 - b := le_trans (min_le_right _ _) (min_le_left _ _)
    have hε4 : ε ≤ b + 2 * Real.pi - z.1.2 := le_trans (min_le_right _ _) (min_le_right _ _)
    have hball : ∀ y : ℝ × ℝ, ‖y - z.1‖ < ε →
        y.1 ∈ Set.Ioo a (a + 2 * Real.pi) ∧ y.2 ∈ Set.Ioo b (b + 2 * Real.pi) := by
      intro y hy
      have h1 : |y.1 - z.1.1| < ε := by
        have h3 : dist y.1 z.1.1 ≤ dist y z.1 := by
          rw [Prod.dist_eq]; exact le_max_left _ _
        rw [dist_eq_norm, Real.norm_eq_abs, dist_eq_norm] at h3
        linarith
      have h2 : |y.2 - z.1.2| < ε := by
        have h3 : dist y.2 z.1.2 ≤ dist y z.1 := by
          rw [Prod.dist_eq]; exact le_max_right _ _
        rw [dist_eq_norm, Real.norm_eq_abs, dist_eq_norm] at h3
        linarith
      rw [abs_lt] at h1 h2
      exact ⟨⟨by linarith [h1.1, hε1], by linarith [h1.2, hε2]⟩,
             ⟨by linarith [h2.1, hε3], by linarith [h2.2, hε4]⟩⟩
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
    refine ⟨Metric.ball n₀ δ, Metric.isOpen_ball, Metric.mem_ball_self hδpos, ?_⟩
    intro n hn
    have hd : dist (yy z n) (yy z n₀) < ε := hδ hn
    rw [hyy0 z, dist_eq_norm] at hd
    exact hball (yy z n) hd
  choose W hWopen hWmem hWint using hint
  rcases X.eq_empty_or_nonempty with hXe | hXne0
  · -- ## no critical points in the box
    rw [hXe] at hXmem
    have hX' : ∀ p ∈ boxK a b, fderiv ℝ (hgt ψ n₀) p = 0 → p ∈ (∅ : Finset (ℝ × ℝ)) := by
      intro p hp hpc
      exact (hXmem p).mpr ⟨hp, hpc⟩
    obtain ⟨UE, hUEopen, hUEmem, hUE⟩ := no_crit_off_isCompact ψ n₀ (isCompact_boxK a b)
      (∅ : Finset (ℝ × ℝ)) hX' one_pos
    refine ⟨UE, hUEopen.mem_nhds hUEmem, ?_⟩
    have hempty : UE ∩ {n : R3 | BadAt ψ n} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro n ⟨hnU, hbad⟩
      obtain ⟨p, p', hp, _hp', _hval, _hne⟩ := hbad
      obtain ⟨k, m, hk⟩ := exists_sub_mem_boxK a b p
      have hcrit : fderiv ℝ (hgt ψ n)
          (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) = 0 := by
        rw [fderiv_hgt_periodic]; exact hp
      obtain ⟨x, hx, -⟩ := hUE n hnU _ hk hcrit
      exact (Finset.notMem_empty x) hx
    rw [hempty, measure_empty]
  · -- ## the general case
    have hatt : X.attach.Nonempty := Finset.attach_nonempty_iff.mpr hXne0
    set R : ℝ := X.attach.inf' hatt rr with hRdef
    have hRpos : 0 < R := by
      rw [Finset.lt_inf'_iff]
      intro z _
      exact hrrpos z
    have hRle : ∀ z : {x // x ∈ X}, R ≤ rr z := fun z => Finset.inf'_le rr (Finset.mem_attach X z)
    obtain ⟨UE, hUEopen, hUEmem, hUE⟩ := no_crit_off_isCompact ψ n₀ (isCompact_boxK a b) X
      (fun p hp hpc => (hXmem p).mpr ⟨hp, hpc⟩) hRpos
    set U1 : Set R3 := ⋂ z : {x // x ∈ X}, (V z ∩ W z) with hU1def
    have hU1open : IsOpen U1 := by
      rw [hU1def]
      exact isOpen_iInter_of_finite (fun z => (hVopen z).inter (hWopen z))
    have hU1mem : n₀ ∈ U1 := by
      rw [hU1def, Set.mem_iInter]
      exact fun z => ⟨hVmem z, hWmem z⟩
    set G : {x // x ∈ X} → {x // x ∈ X} → R3 → ℝ :=
      fun z z' n => hgt ψ n (yy z n) - hgt ψ n (yy z' n) with hGdef
    -- ## the gradient of a pair function
    have hgrad : ∀ (z z' : {x // x ∈ X}) (n : R3), n ∈ V z → n ∈ V z' →
        fderiv ℝ (G z z') n
          = (innerSL ℝ) (Work.BoxShrink.Pinch.par ψ (yy z n))
            - (innerSL ℝ) (Work.BoxShrink.Pinch.par ψ (yy z' n)) := by
      intro z z' n hnV hnV'
      have hdy1 : DifferentiableAt ℝ (yy z) n := by
        have h : DifferentiableOn ℝ (yy z) (V z) := (hyycd z).differentiableOn (by norm_num)
        exact h.differentiableAt ((hVopen z).mem_nhds hnV)
      have hdy2 : DifferentiableAt ℝ (yy z') n := by
        have h : DifferentiableOn ℝ (yy z') (V z') := (hyycd z').differentiableOn (by norm_num)
        exact h.differentiableAt ((hVopen z').mem_nhds hnV')
      have hd1 : DifferentiableAt ℝ (fun m : R3 => hgt ψ m (yy z m)) n := by
        have h : DifferentiableOn ℝ (fun m : R3 => hgt ψ m (yy z m)) (V z) :=
          (contDiffOn_branchHeight ψ (hyycd z)).differentiableOn (by norm_num)
        exact h.differentiableAt ((hVopen z).mem_nhds hnV)
      have hd2 : DifferentiableAt ℝ (fun m : R3 => hgt ψ m (yy z' m)) n := by
        have h : DifferentiableOn ℝ (fun m : R3 => hgt ψ m (yy z' m)) (V z') :=
          (contDiffOn_branchHeight ψ (hyycd z')).differentiableOn (by norm_num)
        exact h.differentiableAt ((hVopen z').mem_nhds hnV')
      have hfun : G z z'
          = (fun m : R3 => hgt ψ m (yy z m)) - (fun m : R3 => hgt ψ m (yy z' m)) := rfl
      rw [hfun, fderiv_sub hd1 hd2, fderiv_branchHeight_euclid ψ hdy1 (hyycrit z n hnV),
        fderiv_branchHeight_euclid ψ hdy2 (hyycrit z' n hnV')]
    -- ## every pair function is null on its open set
    have hnull : ∀ z z' : {x // x ∈ X},
        (volume : Measure R3) ((((V z ∩ V z') ∩ (W z ∩ W z'))
          ∩ {n : R3 | yy z n ≠ yy z' n}) ∩ {n : R3 | G z z' n = 0}) = 0 := by
      intro z z'
      have hUopen : IsOpen (((V z ∩ V z') ∩ (W z ∩ W z'))
          ∩ {n : R3 | yy z n ≠ yy z' n}) := by
        rw [isOpen_iff_mem_nhds]
        intro n hn
        have hnV : n ∈ V z := hn.1.1.1
        have hnV' : n ∈ V z' := hn.1.1.2
        have hnne : yy z n ≠ yy z' n := hn.2
        refine Filter.inter_mem
          ((((hVopen z).inter (hVopen z')).inter ((hWopen z).inter (hWopen z'))).mem_nhds hn.1) ?_
        have hcont : ContinuousAt (fun m : R3 => yy z m - yy z' m) n :=
          (((hyycd z).continuousOn).continuousAt ((hVopen z).mem_nhds hnV)).sub
            (((hyycd z').continuousOn).continuousAt ((hVopen z').mem_nhds hnV'))
        exact (hcont.eventually_ne (sub_ne_zero.mpr hnne)).mono (fun m hm => sub_ne_zero.mp hm)
      refine volume_zeroSet_eq_zero hUopen ?_ ?_
      · have h1 : ContDiffOn ℝ 1 (fun n : R3 => hgt ψ n (yy z n)) (V z) :=
          contDiffOn_branchHeight ψ (hyycd z)
        have h2 : ContDiffOn ℝ 1 (fun n : R3 => hgt ψ n (yy z' n)) (V z') :=
          contDiffOn_branchHeight ψ (hyycd z')
        have h3 : ContDiffOn ℝ 1 (G z z') (V z ∩ V z') := by
          show ContDiffOn ℝ 1 (fun n : R3 => hgt ψ n (yy z n) - hgt ψ n (yy z' n))
            (V z ∩ V z')
          exact (h1.mono Set.inter_subset_left).sub (h2.mono Set.inter_subset_right)
        exact h3.mono (fun n hn => hn.1.1)
      · intro n hn hG0
        have hnne : yy z n ≠ yy z' n := hn.2
        have hnV : n ∈ V z := hn.1.1.1
        have hnV' : n ∈ V z' := hn.1.1.2
        have hnW : n ∈ W z := hn.1.2.1
        have hnW' : n ∈ W z' := hn.1.2.2
        rw [hgrad z z' n hnV hnV', ← map_sub]
        intro h0
        have hpar : Work.BoxShrink.Pinch.par ψ (yy z n)
            = Work.BoxShrink.Pinch.par ψ (yy z' n) :=
          sub_eq_zero.mp (innerSL_eq_zero h0)
        exact absurd hpar (par_ne_of_mem_Ioo ψ (hWint z n hnW).1 (hWint z n hnW).2
          (hWint z' n hnW').1 (hWint z' n hnW').2 hnne)
    -- ## the containment
    have hsub : (UE ∩ U1) ∩ {n : R3 | BadAt ψ n} ⊆
        ⋃ z : {x // x ∈ X}, ⋃ z' : {x // x ∈ X},
          ((((V z ∩ V z') ∩ (W z ∩ W z')) ∩ {n : R3 | yy z n ≠ yy z' n})
            ∩ {n : R3 | G z z' n = 0}) := by
      rintro n ⟨⟨hnUE, hnU1⟩, hbad⟩
      obtain ⟨p, p', hp, hp', hval, hpar⟩ := hbad
      obtain ⟨k, m, hk⟩ := exists_sub_mem_boxK a b p
      obtain ⟨k', m', hk'⟩ := exists_sub_mem_boxK a b p'
      have hnU1z : ∀ z : {x // x ∈ X}, n ∈ V z ∩ W z := by
        intro z
        rw [hU1def] at hnU1
        exact Set.mem_iInter.mp hnU1 z
      have hp1 : fderiv ℝ (hgt ψ n)
          (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) = 0 := by
        rw [fderiv_hgt_periodic]; exact hp
      have hp2 : fderiv ℝ (hgt ψ n)
          (p'.1 - (k' : ℝ) * (2 * Real.pi), p'.2 - (m' : ℝ) * (2 * Real.pi)) = 0 := by
        rw [fderiv_hgt_periodic]; exact hp'
      have hval1 : hgt ψ n (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
          = hgt ψ n p := hgt_periodic ψ n k m p
      have hval2 : hgt ψ n (p'.1 - (k' : ℝ) * (2 * Real.pi), p'.2 - (m' : ℝ) * (2 * Real.pi))
          = hgt ψ n p' := hgt_periodic ψ n k' m' p'
      have hpar1 : Work.BoxShrink.Pinch.par ψ
            (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
          = Work.BoxShrink.Pinch.par ψ p := par_periodic_sub ψ k m p
      have hpar2 : Work.BoxShrink.Pinch.par ψ
            (p'.1 - (k' : ℝ) * (2 * Real.pi), p'.2 - (m' : ℝ) * (2 * Real.pi))
          = Work.BoxShrink.Pinch.par ψ p' := par_periodic_sub ψ k' m' p'
      obtain ⟨x, hxX, hxd⟩ := hUE n hnUE
        (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) hk hp1
      obtain ⟨x', hx'X, hx'd⟩ := hUE n hnUE
        (p'.1 - (k' : ℝ) * (2 * Real.pi), p'.2 - (m' : ℝ) * (2 * Real.pi)) hk' hp2
      have hp1eq : (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
          = yy ⟨x, hxX⟩ n :=
        hyyuniq ⟨x, hxX⟩ n (hnU1z ⟨x, hxX⟩).1
          (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
          (lt_of_lt_of_le hxd (hRle ⟨x, hxX⟩)) hp1
      have hp2eq : (p'.1 - (k' : ℝ) * (2 * Real.pi), p'.2 - (m' : ℝ) * (2 * Real.pi))
          = yy ⟨x', hx'X⟩ n :=
        hyyuniq ⟨x', hx'X⟩ n (hnU1z ⟨x', hx'X⟩).1
          (p'.1 - (k' : ℝ) * (2 * Real.pi), p'.2 - (m' : ℝ) * (2 * Real.pi))
          (lt_of_lt_of_le hx'd (hRle ⟨x', hx'X⟩)) hp2
      have hne : yy ⟨x, hxX⟩ n ≠ yy ⟨x', hx'X⟩ n := by
        rintro heq
        apply hpar
        calc Work.BoxShrink.Pinch.par ψ p
            = Work.BoxShrink.Pinch.par ψ
                (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) := hpar1.symm
          _ = Work.BoxShrink.Pinch.par ψ (yy ⟨x, hxX⟩ n) := by rw [hp1eq]
          _ = Work.BoxShrink.Pinch.par ψ (yy ⟨x', hx'X⟩ n) := by rw [heq]
          _ = Work.BoxShrink.Pinch.par ψ
                (p'.1 - (k' : ℝ) * (2 * Real.pi), p'.2 - (m' : ℝ) * (2 * Real.pi)) := by
                rw [hp2eq]
          _ = Work.BoxShrink.Pinch.par ψ p' := hpar2
      have hG0 : G ⟨x, hxX⟩ ⟨x', hx'X⟩ n = 0 := by
        show hgt ψ n (yy ⟨x, hxX⟩ n) - hgt ψ n (yy ⟨x', hx'X⟩ n) = 0
        rw [← hp1eq, ← hp2eq, hval1, hval2, hval, sub_self]
      refine Set.mem_iUnion.mpr ⟨⟨x, hxX⟩, Set.mem_iUnion.mpr ⟨⟨x', hx'X⟩, ?_⟩⟩
      exact ⟨⟨⟨⟨(hnU1z ⟨x, hxX⟩).1, (hnU1z ⟨x', hx'X⟩).1⟩,
        ⟨(hnU1z ⟨x, hxX⟩).2, (hnU1z ⟨x', hx'X⟩).2⟩⟩, hne⟩, hG0⟩
    refine ⟨UE ∩ U1, (hUEopen.inter hU1open).mem_nhds ⟨hUEmem, hU1mem⟩, ?_⟩
    refine measure_mono_null hsub ?_
    rw [measure_iUnion_null_iff]
    intro z
    rw [measure_iUnion_null_iff]
    intro z'
    exact hnull z z'

/-! ## The Morse property holds almost everywhere -/

theorem ae_morse (ψ : Submission.Diffeo) :
    ∀ᵐ n ∂(MeasureTheory.volume : MeasureTheory.Measure R3), MorseAt ψ n := by
  have key : ∀ᵐ n ∂(MeasureTheory.volume : MeasureTheory.Measure R3),
      ∀ p : ℝ × ℝ,
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
        Function.Injective (fderiv ℝ (fderiv ℝ
          (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q))) p) := by
    have hΦ3 : ContDiff ℝ 3 (Work.BoxShrink.Pinch.par ψ) :=
      (Work.Smooth.Morse.param_contDiff ψ).of_le (WithTop.coe_le_coe.mpr le_top)
    have himm : ∀ p : ℝ × ℝ, Function.Injective (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) p) :=
      Work.Smooth.Morse.Immersion.isImmersion ψ
    filter_upwards [Work.Drive.Generic.ae_height_morse hΦ3 himm] with n hn
    intro p hp a b hab
    have h0 : (fderiv ℝ (fderiv ℝ
        (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q))) p) (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hn p hp (a - b) (fun w' => by rw [h0]; rfl))
  exact key

/-! ## The bad set has measure zero -/

theorem badSet_null (ψ : Submission.Diffeo) :
    (MeasureTheory.volume : MeasureTheory.Measure R3) {n : R3 | BadAt ψ n} = 0 := by
  classical
  have hMc : (MeasureTheory.volume : MeasureTheory.Measure R3)
      {n : R3 | ¬ MorseAt ψ n} = 0 := by
    rw [← MeasureTheory.ae_iff]
    exact ae_morse ψ
  have hloc : ∀ n : R3, MorseAt ψ n → ∃ U : Set R3, U ∈ 𝓝 n ∧
      (MeasureTheory.volume : MeasureTheory.Measure R3)
        (U ∩ {m : R3 | BadAt ψ m}) = 0 :=
    fun n hn => badSet_locally_null ψ hn
  choose U hUnhds hUnull using hloc
  let U' : R3 → Set R3 := fun n => if h : MorseAt ψ n then U n h else Set.univ
  have hU'nhds : ∀ n ∈ {n : R3 | MorseAt ψ n}, U' n ∈ 𝓝 n := by
    intro n hn
    rw [show U' n = U n hn from dif_pos hn]
    exact hUnhds n hn
  have hU'null : ∀ n ∈ {n : R3 | MorseAt ψ n},
      (MeasureTheory.volume : MeasureTheory.Measure R3)
        (U' n ∩ {m : R3 | BadAt ψ m}) = 0 := by
    intro n hn
    rw [show U' n = U n hn from dif_pos hn]
    exact hUnull n hn
  obtain ⟨t, htc, htsub, htcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof ({n : R3 | MorseAt ψ n})).elim_nhds_subcover U' hU'nhds
  have h2 : (MeasureTheory.volume : MeasureTheory.Measure R3)
      (⋃ n ∈ t, (U' n ∩ {m : R3 | BadAt ψ m})) = 0 := by
    rw [measure_biUnion_null_iff htc]
    intro n hn
    exact hU'null n (htsub n hn)
  have hsub : {n : R3 | BadAt ψ n} ⊆ {n : R3 | ¬ MorseAt ψ n} ∪
      ⋃ n ∈ t, (U' n ∩ {m : R3 | BadAt ψ m}) := by
    intro n hn
    by_cases h : MorseAt ψ n
    · right
      have hmem : n ∈ ⋃ n ∈ t, U' n := htcover h
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨hat, han⟩ := Set.mem_iUnion.mp ha
      exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨hat, ⟨han, hn⟩⟩⟩
    · exact Or.inl h
  refine le_antisymm ?_ bot_le
  calc (MeasureTheory.volume : MeasureTheory.Measure R3) {n : R3 | BadAt ψ n}
      ≤ (MeasureTheory.volume : MeasureTheory.Measure R3)
          ({n : R3 | ¬ MorseAt ψ n} ∪ ⋃ n ∈ t, (U' n ∩ {m : R3 | BadAt ψ m})) :=
        measure_mono hsub
    _ ≤ (MeasureTheory.volume : MeasureTheory.Measure R3) {n : R3 | ¬ MorseAt ψ n} +
        (MeasureTheory.volume : MeasureTheory.Measure R3)
          (⋃ n ∈ t, (U' n ∩ {m : R3 | BadAt ψ m})) := measure_union_le _ _
    _ = 0 := by rw [hMc, h2, add_zero]

/-! ## The main statement -/

theorem ae_good (ψ : Submission.Diffeo) :
    ∀ᵐ n ∂(MeasureTheory.volume : MeasureTheory.Measure R3),
      (∀ p : ℝ × ℝ, fderiv ℝ (hgt ψ n) p = 0 →
        Function.Injective (fderiv ℝ (fderiv ℝ (hgt ψ n)) p)) ∧
      (∀ p p' : ℝ × ℝ, fderiv ℝ (hgt ψ n) p = 0 → fderiv ℝ (hgt ψ n) p' = 0 →
        hgt ψ n p = hgt ψ n p' →
        Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p') := by
  have hbad : ∀ᵐ n ∂(MeasureTheory.volume : MeasureTheory.Measure R3), ¬ BadAt ψ n := by
    rw [MeasureTheory.ae_iff]
    simpa using badSet_null ψ
  filter_upwards [ae_morse ψ, hbad] with n hn1 hn2
  refine ⟨hn1, ?_⟩
  intro p p' hp hp' hval
  by_contra hne
  exact hn2 ⟨p, p', hp, hp', hval, hne⟩

end

end Aeh

end Work.Drive.Mono.Band

namespace Work.Drive.Mono.Band

/-- **Almost every direction gives a height with nondegenerate critical points and distinct
critical values on the surface.** -/
theorem ae_height_good (ψ : Submission.Diffeo) :
    ∀ᵐ n ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      (∀ p : ℝ × ℝ,
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
        Function.Injective
          (fderiv ℝ (fderiv ℝ
            (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q))) p)) ∧
      (∀ p p' : ℝ × ℝ,
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p' = 0 →
        inner ℝ n (Work.BoxShrink.Pinch.par ψ p) = inner ℝ n (Work.BoxShrink.Pinch.par ψ p') →
        Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p') := by
  filter_upwards [Aeh.ae_good ψ] with n hn
  exact hn

end Work.Drive.Mono.Band
