import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.basisRed_succMinL_mono
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.Minkowski2.slicing_scaleFirst
import Submission.Work.BW.Minkowski2.volume_scaleLast
import Submission.Work.BW.KWM.basic
import Submission.Work.BW.KWM.coord_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Minkowski's second theorem in the coordinate case
-/

namespace Work.BW.KWM

open MeasureTheory
open scoped Pointwise
open scoped ENNReal

variable {n : ℕ}

noncomputable def Vset (F : (Fin n → ℝ) → ℝ) (j : ℕ) : Set (Fin n → ℝ) :=
  (Work.BW.succMinL F j / 2) • uBall F

theorem Vset_convex (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F) (j : ℕ) :
    Convex ℝ (Vset F j) := (uBall_convex hF).smul _

theorem Vset_eq (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F) {j : ℕ}
    (hj : 0 < Work.BW.succMinL F j) :
    Vset F j = {x : Fin n → ℝ | F x ≤ Work.BW.succMinL F j / 2} :=
  smul_uBall_eq hF (by positivity)

theorem Vset_measurable (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F) {j : ℕ}
    (hj : 0 < Work.BW.succMinL F j) : MeasurableSet (Vset F j) := by
  rw [Vset_eq F hF hj]
  exact (isClosed_le (norm_continuous hF) continuous_const).measurableSet

theorem Vset_sub_lt (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F) {j : ℕ}
    (hj : 0 < Work.BW.succMinL F j) {x : Fin n → ℝ} (hx : x ∈ interior (Vset F j)) :
    F x < Work.BW.succMinL F j / 2 :=
  F_lt_of_mem_interior_smul hF (by linarith) hx

theorem uBall_measure_ne_top (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F) :
    volume (uBall F) ≠ ∞ := (uBall_bounded hF).measure_lt_top.ne

theorem Vset_measure_ne_top (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F) {j : ℕ}
    (hj : 0 < Work.BW.succMinL F j) : volume (Vset F j) ≠ ∞ := by
  rw [Vset, MeasureTheory.Measure.addHaar_smul_of_nonneg volume (by linarith)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (uBall_measure_ne_top F hF)

theorem volume_vadd (c : Fin n → ℝ) (A : Set (Fin n → ℝ)) :
    volume (c +ᵥ A) = volume A := volume_shift c A

theorem shift_inter_eq {c c' : Fin n → ℝ} {A : Set (Fin n → ℝ)} :
    ((fun x => c + x) '' A) ∩ ((fun x => c' + x) '' A)
      = (fun x => c + x) '' (A ∩ (fun x => (c' - c) + x) '' A) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_image]
  constructor
  · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
    refine ⟨a, ⟨ha, ?_⟩, h1⟩
    refine ⟨b, hb, ?_⟩
    rw [show (c' - c) + b = (c' + b) - c by abel, h2, ← h1]
    abel
  · rintro ⟨a, ⟨ha, b, hb, h3⟩, h4⟩
    refine ⟨⟨a, ha, h4⟩, ⟨b, hb, ?_⟩⟩
    have h5 : c' + b = c + a := by
      rw [show (c' - c) + b = (c' + b) - c by abel] at h3
      have h6 : (c' + b) - c = a := h3
      have h7 := congrArg (fun t : Fin n → ℝ => t + c) h6
      simpa [add_assoc, add_comm, add_left_comm] using h7
    rw [h5, h4]

/-- The translates of the level body by the "high" part of the cube are a.e. disjoint. -/
theorem aedisjoint_stage (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F)
    (hflag : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) (x : Fin n → ℤ),
      F (cvec x) < Work.BW.succMinL F j → cvec x ∈ cflag n (j - 1))
    {q i j : ℕ} (hj1 : 1 ≤ j) (hjn : j ≤ n) (hji : j ≤ i + 1)
    {w w' : Fin n → ℝ} (hw : w ∈ rcubeHi n q i) (hw' : w' ∈ rcubeHi n q i) (hne : w ≠ w')
    {m m' : Fin n → ℝ} (hm : m ∈ rcubeLo n q i) (hm' : m' ∈ rcubeLo n q i) :
    AEDisjoint volume
      ((fun x => (w + m) + x) '' (Vset F j))
      ((fun x => (w' + m') + x) '' (Vset F j)) := by
  have hLj : 0 < Work.BW.succMinL F j := succMinL_pos_of_le hF hj1 hjn
  obtain ⟨vw, hwv⟩ := exists_int_of_mem_rcubeHi hw
  obtain ⟨vw', hwv'⟩ := exists_int_of_mem_rcubeHi hw'
  obtain ⟨vm, hmv⟩ := exists_int_of_mem_rcubeLo hm
  obtain ⟨vm', hmv'⟩ := exists_int_of_mem_rcubeLo hm'
  have hvw : cvec vw ∈ rcubeHi n q i := by rw [← hwv]; exact hw
  have hvw' : cvec vw' ∈ rcubeHi n q i := by rw [← hwv']; exact hw'
  have hvm : cvec vm ∈ rcubeLo n q i := by rw [← hmv]; exact hm
  have hvm' : cvec vm' ∈ rcubeLo n q i := by rw [← hmv']; exact hm'
  rw [hwv, hwv', hmv, hmv', AEDisjoint]
  set uZ : Fin n → ℤ := vw' + vm' - (vw + vm) with huZ
  have hucvec : cvec uZ = (cvec vw' + cvec vm') - (cvec vw + cvec vm) := by
    rw [huZ]; ext k; simp [cvec]
  rw [shift_inter_eq, volume_shift, ← hucvec]
  have hconv : Convex ℝ (Vset F j ∩ (fun x => cvec uZ + x) '' (Vset F j)) :=
    (Vset_convex F hF j).inter ((Vset_convex F hF j).translate _)
  rw [measure_eq_zero_of_convex_interior_empty hconv]
  by_contra hneint
  obtain ⟨y, hy⟩ : (interior (Vset F j ∩ (fun x => cvec uZ + x) '' (Vset F j))).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hneint
  have hy1 : y ∈ interior (Vset F j) := interior_mono Set.inter_subset_left hy
  have hy2 : y ∈ interior ((fun x => cvec uZ + x) '' (Vset F j)) :=
    interior_mono Set.inter_subset_right hy
  have h1 : F y < Work.BW.succMinL F j / 2 := Vset_sub_lt F hF hLj hy1
  have h2 : F (y - cvec uZ) < Work.BW.succMinL F j / 2 :=
    Vset_sub_lt F hF hLj (sub_mem_interior_of_mem_interior_shift hy2)
  have h3 : F (cvec uZ) ≤ F y + F (y - cvec uZ) := by
    have h := hF.add_le y (-(y - cvec uZ))
    have he : y + (-(y - cvec uZ)) = cvec uZ := by abel
    rw [he, latticeNorm_neg hF] at h
    exact h
  have h4 : F (cvec uZ) < Work.BW.succMinL F j := by linarith
  have hUmem : ∀ k : Fin n, j - 1 ≤ (k : ℕ) → (cvec uZ) k = 0 := (mem_cflag).mp (hflag j hj1 hjn uZ h4)
  have hvwne : vw ≠ vw' := by
    intro h
    exact hne (by rw [hwv, hwv', h])
  have hveq : vw' = vw := by
    funext k
    by_cases hk : (k : ℕ) < i
    · have hv1 : (cvec vw) k = 0 := mem_rcubeHi_apply hvw k hk
      have hv2 : (cvec vw') k = 0 := mem_rcubeHi_apply hvw' k hk
      have h1 : vw k = 0 := by
        have hh := hv1; simp only [cvec_apply] at hh; exact_mod_cast hh
      have h2 : vw' k = 0 := by
        have hh := hv2; simp only [cvec_apply] at hh; exact_mod_cast hh
      rw [h1, h2]
    · have hu0 : (cvec uZ) k = 0 := hUmem k (by omega)
      have hm1 : (cvec vm) k = 0 := mem_rcubeLo_apply hvm k (not_lt.mp hk)
      have hm2 : (cvec vm') k = 0 := mem_rcubeLo_apply hvm' k (not_lt.mp hk)
      have hvm1 : vm k = 0 := by
        have : ((vm k : ℤ) : ℝ) = 0 := hm1
        exact_mod_cast this
      have hvm2 : vm' k = 0 := by
        have : ((vm' k : ℤ) : ℝ) = 0 := hm2
        exact_mod_cast this
      have huZk : uZ k = 0 := by
        have : ((uZ k : ℤ) : ℝ) = 0 := hu0
        exact_mod_cast this
      rw [huZ] at huZk
      rw [Pi.sub_apply, Pi.add_apply, Pi.add_apply, hvm1, hvm2] at huZk
      omega
  exact hvwne hveq.symm

/-- The cube is the sum of its low and high parts. -/
theorem addSet_rcube_split {q i : ℕ} (A : Set (Fin n → ℝ)) :
    Work.BW.addSet ((rcubeHi n q i : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
        (Work.BW.addSet ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) A)
      = Work.BW.addSet ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) A := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw, m, hm, hx1⟩ := Work.BW.mem_addSet.mp hx
    obtain ⟨m0, hm0, a, ha, hm1⟩ := Work.BW.mem_addSet.mp hm
    refine Work.BW.mem_addSet.mpr
      ⟨w + m0, (mem_rcube_iff q i _).mpr ⟨w, hw, m0, hm0, rfl⟩, a, ha, ?_⟩
    rw [hx1, hm1]; abel
  · intro hx
    obtain ⟨v, hv, a, ha, hx1⟩ := Work.BW.mem_addSet.mp hx
    obtain ⟨w, hw, m0, hm0, hv1⟩ := (mem_rcube_iff q i v).mp hv
    refine Work.BW.mem_addSet.mpr ⟨w, hw, m0 + a, ⟨m0, hm0, a, ha, rfl⟩, ?_⟩
    rw [hx1, hv1]; abel

/-- Decomposition of the measure along the low/high splitting of the cube. -/
theorem stage_decomp (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F)
    (hflag : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) (x : Fin n → ℤ),
      F (cvec x) < Work.BW.succMinL F j → cvec x ∈ cflag n (j - 1))
    (q i j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) (hi : i ≤ n) (hji : j ≤ i + 1) :
    volume.real (Work.BW.addSet ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) (Vset F j))
      = (rcubeHi n q i).card *
        volume.real (Work.BW.addSet ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
          (Vset F j)) := by
  have hLj : 0 < Work.BW.succMinL F j := succMinL_pos_of_le hF hj1 hjn
  rw [← addSet_rcube_split (q := q) (i := i) (Vset F j)]
  rw [addSet_eq_iUnion]
  have hAmeas : MeasurableSet (Work.BW.addSet ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set _)
      (Vset F j)) := by
    rw [addSet_eq_iUnion]
    exact Finset.measurableSet_biUnion _ (fun m _ => measurableSet_shift (Vset_measurable F hF hLj) m)
  have hAfin : volume (Work.BW.addSet ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set _)
      (Vset F j)) ≠ ∞ := by
    rw [addSet_eq_iUnion]
    have h1 : volume (⋃ m ∈ rcubeLo n q i, (fun x => m + x) '' (Vset F j))
        ≤ ∑ m ∈ rcubeLo n q i, volume ((fun x => m + x) '' (Vset F j)) :=
      MeasureTheory.measure_biUnion_finset_le (μ := volume) _ _
    rw [Finset.sum_congr rfl (fun m _ => volume_shift m (Vset F j)), Finset.sum_const,
      nsmul_eq_mul] at h1
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (Vset_measure_ne_top F hF hLj)) h1
  have hdisj : ∀ w ∈ rcubeHi n q i, ∀ w' ∈ rcubeHi n q i, w ≠ w' →
      AEDisjoint volume
        ((fun x => w + x) '' (Work.BW.addSet ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set _)
          (Vset F j)))
        ((fun x => w' + x) '' (Work.BW.addSet ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set _)
          (Vset F j))) := by
    intro w hw w' hw' hne
    rw [AEDisjoint]
    refine le_antisymm ?_ (by simp)
    have hsub : ((fun x => w + x) '' (Work.BW.addSet ((rcubeLo n q i : Finset _) : Set _)
          (Vset F j))) ∩
        ((fun x => w' + x) '' (Work.BW.addSet ((rcubeLo n q i : Finset _) : Set _) (Vset F j)))
        ⊆ ⋃ mm ∈ rcubeLo n q i, ⋃ mm' ∈ rcubeLo n q i,
          (((fun x => (w + mm) + x) '' (Vset F j)) ∩
            ((fun x => (w' + mm') + x) '' (Vset F j))) := by
      rintro x ⟨hx1, hx2⟩
      rw [Set.mem_image] at hx1 hx2
      obtain ⟨s, hs, hsx⟩ := hx1
      obtain ⟨s', hs', hs'x⟩ := hx2
      obtain ⟨mm, hmm, a, ha, hsa⟩ := Work.BW.mem_addSet.mp hs
      obtain ⟨mm', hmm', b, hb, hsb⟩ := Work.BW.mem_addSet.mp hs'
      have hEq : x = w + (mm + a) := by rw [← hsx, hsa]
      have hEq2 : x = w' + (mm' + b) := by rw [← hs'x, hsb]
      refine Set.mem_iUnion₂.mpr ⟨mm, hmm, Set.mem_iUnion₂.mpr ⟨mm', hmm', ?_⟩⟩
      refine ⟨⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩⟩
      · rw [hEq]; abel
      · rw [hEq2]; abel
    have h1 : volume (⋃ mm ∈ rcubeLo n q i, ⋃ mm' ∈ rcubeLo n q i,
        (((fun x => (w + mm) + x) '' (Vset F j)) ∩
          ((fun x => (w' + mm') + x) '' (Vset F j))))
        ≤ ∑ mm ∈ rcubeLo n q i, ∑ mm' ∈ rcubeLo n q i,
          volume (((fun x => (w + mm) + x) '' (Vset F j)) ∩
            ((fun x => (w' + mm') + x) '' (Vset F j))) := by
      refine le_trans (MeasureTheory.measure_biUnion_finset_le (μ := volume) _ _) ?_
      exact Finset.sum_le_sum (fun mm _ =>
        MeasureTheory.measure_biUnion_finset_le (μ := volume) _ _)
    have h2 : ∑ mm ∈ rcubeLo n q i, ∑ mm' ∈ rcubeLo n q i,
        volume (((fun x => (w + mm) + x) '' (Vset F j)) ∩
          ((fun x => (w' + mm') + x) '' (Vset F j))) = 0 := by
      refine Finset.sum_eq_zero (fun mm hmm => ?_)
      refine Finset.sum_eq_zero (fun mm' hmm' => ?_)
      exact (aedisjoint_stage F hF hflag hj1 hjn hji hw hw' hne hmm hmm').eq
    exact le_trans (measure_mono hsub) (le_trans h1 (le_of_eq h2))
  rw [volume_real_biUnion_of_aedisjoint _ _ hAmeas hAfin hdisj]

end Work.BW.KWM
