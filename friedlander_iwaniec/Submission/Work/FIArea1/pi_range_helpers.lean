/-
# `Submission.Work.FIArea1.pi_range_helpers` — auxiliary facts for the assembly of *FI* (5.22)

Small lemmas about `gnorm`, `cForm`, `Delta` and the boxes `Qbim X`, `Yset X`, `KR`, used by the
final assembly of `Work.FIArea1.offdiag_pi_range_le`.
-/
import Mathlib
import Submission.Work.FIArea1.L51Defs
import Submission.Work.FIArea1.Basic
import Submission.Work.FIArea1.QboxDefs

set_option maxHeartbeats 800000

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

lemma neg_re (z : GaussianInt) : (-z).re = -z.re := rfl

lemma neg_im (z : GaussianInt) : (-z).im = -z.im := rfl

lemma gnorm_neg (z : GaussianInt) : Work.FIPlan.gnorm (-z) = Work.FIPlan.gnorm z := by
  have h1 : (Work.FIPlan.gnorm (-z) : ℤ) = (Work.FIPlan.gnorm z : ℤ) := by
    rw [Work.FIArea1.gnorm_int (-z), Work.FIArea1.gnorm_int z, neg_re, neg_im]
    ring
  exact_mod_cast h1

lemma cForm_neg_left (W y : GaussianInt) :
    Work.FIPlan.cForm (-W) y = -Work.FIPlan.cForm W y := by
  show ((-W) * y).re = -(W * y).re
  rw [show (-W : GaussianInt) = ⟨-W.re, -W.im⟩ from rfl]
  simp only [Zsqrtd.re_mul]
  ring

lemma cForm_neg_right (W y : GaussianInt) :
    Work.FIPlan.cForm W (-y) = -Work.FIPlan.cForm W y := by
  show (W * (-y)).re = -(W * y).re
  rw [show (-y : GaussianInt) = ⟨-y.re, -y.im⟩ from rfl]
  simp only [Zsqrtd.re_mul]
  ring

lemma Qbim_neg_mem {X : ℝ} {y : GaussianInt} (hy : y ∈ Qbim X) : -y ∈ Qbim X := by
  obtain ⟨h0, h1, h2⟩ := mem_Qbim_iff.mp hy
  refine mem_Qbim_iff.mpr ⟨neg_ne_zero.mpr h0, ?_, ?_⟩
  · rwa [gnorm_neg]
  · simpa using h2

/-- The inner sum over `Qbim X` is invariant under `W ↦ -W` (the summand `Z(Re Wy)` is indexed by
`y ↦ -y`, and `Qbim X` is stable under negation). -/
lemma Qbim_A_neg (X : ℝ) (W : GaussianInt) :
    (∑ y ∈ Qbim X, (Work.FIPlan.Zint (Work.FIPlan.cForm (-W) y) : ℝ))
      = ∑ y ∈ Qbim X, (Work.FIPlan.Zint (Work.FIPlan.cForm W y) : ℝ) := by
  have hterm : ∀ y : GaussianInt,
      (Work.FIPlan.Zint (Work.FIPlan.cForm (-W) y) : ℝ)
        = (Work.FIPlan.Zint (Work.FIPlan.cForm W (-y)) : ℝ) := by
    intro y
    rw [cForm_neg_left, cForm_neg_right]
  rw [Finset.sum_congr rfl (fun y _ => hterm y)]
  have hinj : Set.InjOn (fun y : GaussianInt => -y) ↑(Qbim X) :=
    fun a _ b _ h => neg_injective h
  have himg : (Qbim X).image (fun y => -y) = Qbim X := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact Qbim_neg_mem hy
    · intro z hz
      exact Finset.mem_image.mpr ⟨-z, Qbim_neg_mem hz, neg_neg z⟩
  calc (∑ y ∈ Qbim X, (Work.FIPlan.Zint (Work.FIPlan.cForm W (-y)) : ℝ))
      = ∑ z ∈ (Qbim X).image (fun y => -y),
          (Work.FIPlan.Zint (Work.FIPlan.cForm W z) : ℝ) :=
        (Finset.sum_image (s := Qbim X) (g := fun y : GaussianInt => -y)
          (f := fun z : GaussianInt => (Work.FIPlan.Zint (Work.FIPlan.cForm W z) : ℝ))
          hinj).symm
    _ = ∑ z ∈ Qbim X, (Work.FIPlan.Zint (Work.FIPlan.cForm W z) : ℝ) := by rw [himg]

lemma gBox_neg_mem {R : ℤ} {z : GaussianInt} (hz : z ∈ Work.FIPlan.gBox R) :
    -z ∈ Work.FIPlan.gBox R := by
  rw [Work.FIArea2.mem_gBox_iff] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.mp h1
  obtain ⟨h2a, h2b⟩ := Finset.mem_Icc.mp h2
  exact ⟨Finset.mem_Icc.mpr ⟨by rw [neg_re]; linarith, by rw [neg_re]; linarith⟩,
         Finset.mem_Icc.mpr ⟨by rw [neg_im]; linarith, by rw [neg_im]; linarith⟩⟩

/-- The box `(gBox R).erase 0` is stable under negation. -/
lemma erase_gBox_neg_image (R : ℤ) :
    ((Work.FIPlan.gBox R).erase 0).image (fun z => -z) = (Work.FIPlan.gBox R).erase 0 := by
  refine Finset.Subset.antisymm ?_ ?_
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.mem_erase] at hy ⊢
    exact ⟨neg_ne_zero.mpr hy.1, gBox_neg_mem hy.2⟩
  · intro z hz
    rw [Finset.mem_erase] at hz
    exact Finset.mem_image.mpr ⟨-z, by
      rw [Finset.mem_erase]
      exact ⟨neg_ne_zero.mpr hz.1, gBox_neg_mem hz.2⟩, neg_neg z⟩

/-- Monotonicity of `KR = ⌈√(4·)⌉` in its real argument. -/
lemma KR_mono {r s : ℝ} (h : r ≤ s) : KR r ≤ KR s := by
  rw [KR, KR]
  exact_mod_cast Nat.ceil_mono (Real.sqrt_le_sqrt (by linarith))

/-- `1 ≤ KR (16Mq)` for `M ≥ 1`, `q ≥ 1`. -/
lemma one_le_KR (M q : ℝ) (hM : 1 ≤ M) (hq : 1 ≤ q) : (1 : ℤ) ≤ KR (16 * M * q) := by
  have h4 : (2 : ℝ) ^ 2 ≤ 2 ^ 2 * (16 * M * q) := by nlinarith
  have hsqrt : (2 : ℝ) ≤ Real.sqrt (4 * (16 * M * q)) := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.le_sqrt (by norm_num) (by nlinarith)]
    exact h4
  have hceil : (2 : ℝ) ≤ ((KR (16 * M * q)).natAbs : ℝ) := by
    rw [KR, Int.natAbs_natCast]
    exact le_trans hsqrt (Nat.le_ceil _)
  have : (2 : ℤ) ≤ KR (16 * M * q) := by
    rw [← Int.natAbs_of_nonneg (Work.FIArea1.KR_nonneg _)]
    exact_mod_cast hceil
  omega


/-! ## Box containment and cardinality monotonicity -/

lemma KZ_mono {r s : ℝ} (h : r ≤ s) : KZ r ≤ KZ s := by
  rw [KZ, KZ]
  exact_mod_cast Nat.ceil_mono (Real.sqrt_le_sqrt (by linarith))

lemma gBox_mono {R S : ℤ} (h : R ≤ S) : Work.FIPlan.gBox R ⊆ Work.FIPlan.gBox S := by
  intro z hz
  rw [Work.FIArea2.mem_gBox_iff] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.mp h1
  obtain ⟨h2a, h2b⟩ := Finset.mem_Icc.mp h2
  exact ⟨Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩,
         Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩

lemma PiDvd_mono {q N N' : ℝ} (h : N ≤ N') (W : GaussianInt) :
    PiDvd q N W ⊆ PiDvd q N' W := by
  intro π hπ
  rw [PiDvd] at hπ ⊢
  obtain ⟨hmem, hrest⟩ := Finset.mem_filter.mp hπ
  exact Finset.mem_filter.mpr ⟨gBox_mono (KZ_mono h) hmem, hrest⟩

/-- **The norm bound on the big box** `gBox (KR (16Mq))`: `|W|² ≤ 256Mq`. -/
lemma piRange_gnorm_le_of_mem_gBox_KR (M q : ℝ) (hM : 1 ≤ M) (hq : 1 ≤ q) {W : GaussianInt}
    (hW : W ∈ Work.FIPlan.gBox (KR (16 * M * q))) :
    (Work.FIPlan.gnorm W : ℝ) ≤ 256 * M * q := by
  have hMq : 1 ≤ M * q := by nlinarith
  have hsq : Real.sqrt (M * q) ^ 2 = M * q := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt (M * q) := Real.one_le_sqrt.mpr hMq
  have h1 : Work.FIPlan.gnorm W ≤ 2 * (KR (16 * M * q)).natAbs ^ 2 :=
    Work.FIArea2.gnorm_le_of_mem_gBox (KR_nonneg _) hW
  have hcast : (Work.FIPlan.gnorm W : ℝ) ≤ 2 * ((KR (16 * M * q)).natAbs : ℝ) ^ 2 := by
    exact_mod_cast h1
  have h2 : ((KR (16 * M * q)).natAbs : ℝ) ≤ 8 * Real.sqrt (M * q) + 1 := by
    rw [KR, Int.natAbs_natCast]
    have h3 : Real.sqrt (4 * (16 * M * q)) = 8 * Real.sqrt (M * q) := by
      have h64 : (4 : ℝ) * (16 * M * q) = 8 ^ 2 * (M * q) := by ring
      rw [h64, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8 ^ 2), Real.sqrt_sq (by norm_num)]
    calc (⌈Real.sqrt (4 * (16 * M * q))⌉₊ : ℝ)
        ≤ Real.sqrt (4 * (16 * M * q)) + 1 := (Nat.ceil_lt_add_one (Real.sqrt_nonneg _)).le
      _ = 8 * Real.sqrt (M * q) + 1 := by rw [h3]
  have h4 : 2 * (8 * Real.sqrt (M * q) + 1) ^ 2 ≤ 256 * M * q := by
    nlinarith [hsq, hs1, sq_nonneg (Real.sqrt (M * q) - 1)]
  calc (Work.FIPlan.gnorm W : ℝ) ≤ 2 * ((KR (16 * M * q)).natAbs : ℝ) ^ 2 := hcast
    _ ≤ 2 * (8 * Real.sqrt (M * q) + 1) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pow_le_pow_left₀ (by linarith [hcast]) h2 2
    _ ≤ 256 * M * q := h4

/-- `2√(max (N/q) 2) ≤ KR (16Mq)`. -/
lemma two_sqrt_max_le_KR (M N q : ℝ) (hq : 1 ≤ q) (hN : 2 ≤ N) (hNM : N ≤ M) :
    2 * Real.sqrt (max (N / q) 2) ≤ ((KR (16 * M * q)).natAbs : ℝ) := by
  have hqpos : 0 < q := by linarith
  have hMq : 1 ≤ M * q := by nlinarith
  have hKR : 8 * Real.sqrt (M * q) ≤ ((KR (16 * M * q)).natAbs : ℝ) := by
    rw [KR, Int.natAbs_natCast]
    have h3 : Real.sqrt (4 * (16 * M * q)) = 8 * Real.sqrt (M * q) := by
      have h64 : (4 : ℝ) * (16 * M * q) = 8 ^ 2 * (M * q) := by ring
      rw [h64, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8 ^ 2), Real.sqrt_sq (by norm_num)]
    rw [← h3]
    exact Nat.le_ceil _
  have hmax : max (N / q) 2 ≤ 16 * M * q := by
    refine max_le ?_ ?_
    · rw [div_le_iff₀ hqpos]
      nlinarith [hNM, hMq, hq]
    · nlinarith [hMq, hq]
  have hsqrt : Real.sqrt (max (N / q) 2) ≤ 4 * Real.sqrt (M * q) := by
    calc Real.sqrt (max (N / q) 2) ≤ Real.sqrt (16 * M * q) := Real.sqrt_le_sqrt hmax
      _ = 4 * Real.sqrt (M * q) := by
          rw [show (16 : ℝ) * M * q = 4 ^ 2 * (M * q) from by ring,
            Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4^2), Real.sqrt_sq (by norm_num)]
  linarith

lemma two_sqrt_max_le_KR_cast (M N q : ℝ) (hq : 1 ≤ q) (hN : 2 ≤ N) (hNM : N ≤ M) :
    2 * Real.sqrt (max (N / q) 2) ≤ ((KR (16 * M * q) : ℤ) : ℝ) := by
  have h := two_sqrt_max_le_KR M N q hq hN hNM
  have hcast : ((KR (16 * M * q) : ℤ) : ℝ) = ((KR (16 * M * q)).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast KR_nonneg (16 * M * q))]
  rwa [hcast]

end

end Work.FIArea1
