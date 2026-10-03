import Mathlib
import Submission.Work.FIArea1.QboxDefs
import Submission.Work.FIArea1.cross_helpers
import Submission.Work.FIArea2.area2_r3
import Submission.Work.FIArea1.sum_Zint_ap_le
import Submission.Work.FIArea1.Qbim_sqrt_im_sum_le

set_option maxHeartbeats 4000000

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The inner sum `∑_{y ∈ Qbim X} Z(Re (W y))` of the crude cross count. -/
def crossInner (X : ℝ) (W : GaussianInt) : ℝ :=
  ∑ y ∈ Work.FIArea1.Qbim X, (Work.FIPlan.Zint (Work.FIPlan.cForm W y) : ℝ)

lemma crossInner_nonneg (X : ℝ) (W : GaussianInt) : 0 ≤ crossInner X W :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- `cForm` of `⟨a, s⟩`, in coordinates. -/
lemma cForm_mk (a s : ℤ) (y : GaussianInt) :
    Work.FIPlan.cForm (⟨a, s⟩ : GaussianInt) y = a * y.re - s * y.im := by
  rw [Work.FIPlan.cForm, Zsqrtd.re_mul]
  ring

/-- **The crude cross count**, given the two delegated inputs (the arithmetic-progression
square count `hAP` and the size of the substituted ball `hQ`). -/
lemma cross_bound (C3 : ℝ) (hC3 : 0 < C3)
    (hAP : ∀ (R : ℤ), 0 ≤ R → ∀ A m : ℤ, m ≠ 0 →
      (∑ s ∈ Finset.Icc (-R) R, (Work.FIPlan.Zint (A - s * m) : ℝ))
        ≤ 2 * Real.sqrt (2 * (R : ℝ) * |(m : ℝ)|) + 2)
    (hQ : ∀ X : ℝ, 1 ≤ X →
      (∑ y ∈ Work.FIArea1.Qbim X, (Real.sqrt |(y.im : ℝ)| + 1)) ≤ C3 * X ^ ((5 : ℝ) / 4))
    (R : ℤ) (X : ℝ) (hR : 1 ≤ R) (hX : 1 ≤ X) :
    (∑ W ∈ (Work.FIPlan.gBox R).erase 0,
        (Work.FIPlan.Zint W.re : ℝ) * crossInner X W)
      ≤ (12 * Real.sqrt 2 * C3 + 1) * ((R.natAbs : ℝ) * X ^ ((3 : ℝ) / 2)) := by
  classical
  have hR0 : (0 : ℤ) ≤ R := by omega
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := by linarith
  have hRn : (R.natAbs : ℝ) = (R : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hRnn]
  set n : ℕ := Nat.sqrt R.natAbs with hn
  set C1 : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ) with hC1
  set B : Finset GaussianInt :=
    (Work.FIPlan.gBox R).filter (fun W => ∃ c : ℤ, W.re = c ^ 2) with hB
  -- ### Step 1: drop `Zint (Re W)` down to the box of square real parts.
  have step1 : (∑ W ∈ (Work.FIPlan.gBox R).erase 0,
        (Work.FIPlan.Zint W.re : ℝ) * crossInner X W)
      ≤ 2 * ∑ W ∈ B, crossInner X W := by
    have h1 : (∑ W ∈ (Work.FIPlan.gBox R).erase 0,
          (Work.FIPlan.Zint W.re : ℝ) * crossInner X W)
        ≤ ∑ W ∈ Work.FIPlan.gBox R, (Work.FIPlan.Zint W.re : ℝ) * crossInner X W := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro W _ _
      exact mul_nonneg (Nat.cast_nonneg _) (crossInner_nonneg X W)
    have h2 : (∑ W ∈ Work.FIPlan.gBox R, (Work.FIPlan.Zint W.re : ℝ) * crossInner X W)
        = ∑ W ∈ B, (Work.FIPlan.Zint W.re : ℝ) * crossInner X W := by
      rw [hB, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro W _
      by_cases hp : ∃ c : ℤ, W.re = c ^ 2
      · rw [if_pos hp]
      · have hz : Work.FIPlan.Zint W.re = 0 := by
          by_contra h
          exact hp (Zint_ne_zero_imp_sq _ h)
        rw [if_neg hp, hz]; ring
    have h3 : (∑ W ∈ B, (Work.FIPlan.Zint W.re : ℝ) * crossInner X W)
        ≤ ∑ W ∈ B, 2 * crossInner X W := by
      apply Finset.sum_le_sum
      intro W _
      have hle : (Work.FIPlan.Zint W.re : ℝ) ≤ 2 := by
        exact_mod_cast Work.FIArea2.Zint_le_two W.re
      exact mul_le_mul_of_nonneg_right hle (crossInner_nonneg X W)
    calc (∑ W ∈ (Work.FIPlan.gBox R).erase 0,
          (Work.FIPlan.Zint W.re : ℝ) * crossInner X W)
        ≤ ∑ W ∈ Work.FIPlan.gBox R, (Work.FIPlan.Zint W.re : ℝ) * crossInner X W := h1
      _ = ∑ W ∈ B, (Work.FIPlan.Zint W.re : ℝ) * crossInner X W := h2
      _ ≤ ∑ W ∈ B, 2 * crossInner X W := h3
      _ = 2 * ∑ W ∈ B, crossInner X W := (Finset.mul_sum B _ 2).symm
  -- ### Step 2: replace the box by the `2√R+1` vertical lines `Re W = c₁²`.
  have step2 : (∑ W ∈ B, crossInner X W)
      ≤ ∑ c₁ ∈ C1, ∑ s ∈ Finset.Icc (-R) R, crossInner X (⟨c₁ ^ 2, s⟩ : GaussianInt) := by
    have hBsub : B ⊆ (C1 ×ˢ Finset.Icc (-R) R).image
        (fun p : ℤ × ℤ => (⟨p.1 ^ 2, p.2⟩ : GaussianInt)) := by
      intro W hW
      rw [hB, Finset.mem_filter] at hW
      obtain ⟨hWbox, c, hc⟩ := hW
      rw [Work.FIArea2.mem_gBox_iff] at hWbox
      obtain ⟨hre, him⟩ := hWbox
      rw [Finset.mem_Icc] at hre
      have hcabs : c.natAbs ≤ n := by
        rw [hn, Nat.le_sqrt]
        have h : ((c.natAbs : ℤ)) ^ 2 ≤ (R.natAbs : ℤ) := by
          rw [Int.natAbs_sq, ← hc, Int.natAbs_of_nonneg hR0]
          exact hre.2
        have h2 : c.natAbs ^ 2 ≤ R.natAbs := by exact_mod_cast h
        simpa [pow_two] using h2
      have hcC1 : c ∈ C1 := by
        rw [hC1, Finset.mem_Icc]
        have h2 : |c| ≤ (n : ℤ) := by
          rw [Int.abs_eq_natAbs]
          exact_mod_cast hcabs
        exact abs_le.mp h2
      refine Finset.mem_image.mpr ⟨(c, W.im), Finset.mem_product.mpr ⟨hcC1, him⟩, ?_⟩
      apply Zsqrtd.ext
      · simpa using hc.symm
      · rfl
    calc ∑ W ∈ B, crossInner X W
        ≤ ∑ W ∈ (C1 ×ˢ Finset.Icc (-R) R).image
            (fun p : ℤ × ℤ => (⟨p.1 ^ 2, p.2⟩ : GaussianInt)), crossInner X W :=
          Finset.sum_le_sum_of_subset_of_nonneg hBsub (fun W _ _ => crossInner_nonneg X W)
      _ ≤ ∑ p ∈ C1 ×ˢ Finset.Icc (-R) R, crossInner X (⟨p.1 ^ 2, p.2⟩ : GaussianInt) :=
          sum_image_le' _ _ _ (fun p _ => crossInner_nonneg X _)
      _ = ∑ c₁ ∈ C1, ∑ s ∈ Finset.Icc (-R) R, crossInner X (⟨c₁ ^ 2, s⟩ : GaussianInt) := by
          rw [Finset.sum_product]
  -- ### Step 3: the arithmetic-progression square count on each vertical line.
  have step3 : (∑ c₁ ∈ C1, ∑ s ∈ Finset.Icc (-R) R, crossInner X (⟨c₁ ^ 2, s⟩ : GaussianInt))
      ≤ ∑ c₁ ∈ C1, ∑ y ∈ Work.FIArea1.Qbim X,
          (2 * Real.sqrt (2 * (R : ℝ) * |(y.im : ℝ)|) + 2) := by
    apply Finset.sum_le_sum
    intro c₁ _
    unfold crossInner
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro y hy
    have hym : y.im ≠ 0 := (mem_Qbim_iff.mp hy).2.2
    calc (∑ s ∈ Finset.Icc (-R) R,
          (Work.FIPlan.Zint (Work.FIPlan.cForm (⟨c₁ ^ 2, s⟩ : GaussianInt) y) : ℝ))
        = ∑ s ∈ Finset.Icc (-R) R, (Work.FIPlan.Zint (c₁ ^ 2 * y.re - s * y.im) : ℝ) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [cForm_mk]
      _ ≤ 2 * Real.sqrt (2 * (R : ℝ) * |(y.im : ℝ)|) + 2 := hAP R hR0 (c₁ ^ 2 * y.re) y.im hym
  -- ### Step 4: sum the bound over `y`.
  have step4 : (∑ c₁ ∈ C1, ∑ y ∈ Work.FIArea1.Qbim X,
          (2 * Real.sqrt (2 * (R : ℝ) * |(y.im : ℝ)|) + 2))
      ≤ (2 * (n : ℝ) + 1) * (2 * Real.sqrt (2 * (R : ℝ)) * (C3 * X ^ ((5 : ℝ) / 4))) := by
    have hcard : (C1.card : ℝ) = 2 * (n : ℝ) + 1 := by
      rw [hC1, Int.card_Icc]
      have h0 : (n : ℤ) + 1 - (-(n : ℤ)) = ((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h0, Int.toNat_natCast]
      push_cast; ring
    have hinner : (∑ y ∈ Work.FIArea1.Qbim X,
          (2 * Real.sqrt (2 * (R : ℝ) * |(y.im : ℝ)|) + 2))
        ≤ 2 * Real.sqrt (2 * (R : ℝ)) * (C3 * X ^ ((5 : ℝ) / 4)) := by
      have hpoint : ∀ y ∈ Work.FIArea1.Qbim X,
          (2 * Real.sqrt (2 * (R : ℝ) * |(y.im : ℝ)|) + 2)
            ≤ 2 * Real.sqrt (2 * (R : ℝ)) * (Real.sqrt |(y.im : ℝ)| + 1) := by
        intro y _
        have hsq : Real.sqrt (2 * (R : ℝ) * |(y.im : ℝ)|)
            = Real.sqrt (2 * (R : ℝ)) * Real.sqrt |(y.im : ℝ)| :=
          Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * (R : ℝ)) _
        have h1 : (1 : ℝ) ≤ Real.sqrt (2 * (R : ℝ)) :=
          Real.one_le_sqrt.mpr (by linarith)
        rw [hsq]
        nlinarith [h1]
      calc (∑ y ∈ Work.FIArea1.Qbim X,
              (2 * Real.sqrt (2 * (R : ℝ) * |(y.im : ℝ)|) + 2))
          ≤ ∑ y ∈ Work.FIArea1.Qbim X,
              2 * Real.sqrt (2 * (R : ℝ)) * (Real.sqrt |(y.im : ℝ)| + 1) :=
            Finset.sum_le_sum hpoint
        _ = 2 * Real.sqrt (2 * (R : ℝ))
              * (∑ y ∈ Work.FIArea1.Qbim X, (Real.sqrt |(y.im : ℝ)| + 1)) := by
            rw [Finset.mul_sum]
        _ ≤ 2 * Real.sqrt (2 * (R : ℝ)) * (C3 * X ^ ((5 : ℝ) / 4)) :=
            mul_le_mul_of_nonneg_left (hQ X hX) (by positivity)
    calc (∑ c₁ ∈ C1, ∑ y ∈ Work.FIArea1.Qbim X,
            (2 * Real.sqrt (2 * (R : ℝ) * |(y.im : ℝ)|) + 2))
        = (C1.card : ℝ) * (∑ y ∈ Work.FIArea1.Qbim X,
            (2 * Real.sqrt (2 * (R : ℝ) * |(y.im : ℝ)|) + 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (2 * (n : ℝ) + 1) * (∑ y ∈ Work.FIArea1.Qbim X,
            (2 * Real.sqrt (2 * (R : ℝ) * |(y.im : ℝ)|) + 2)) := by rw [hcard]
      _ ≤ (2 * (n : ℝ) + 1) * (2 * Real.sqrt (2 * (R : ℝ)) * (C3 * X ^ ((5 : ℝ) / 4))) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
  -- ### Step 5: arithmetic.
  have hRsq : Real.sqrt (R : ℝ) * Real.sqrt (R : ℝ) = (R : ℝ) := by
    rw [← pow_two, Real.sq_sqrt hRnn]
  have hA : 2 * (n : ℝ) + 1 ≤ 3 * Real.sqrt (R : ℝ) := by
    have hn2n : n ^ 2 ≤ R.natAbs := by
      have hh := Nat.sqrt_le R.natAbs
      rw [← hn] at hh
      simpa [pow_two] using hh
    have hn2R : (n : ℝ) ^ 2 ≤ (R : ℝ) := by
      have h1 : ((n ^ 2 : ℕ) : ℝ) ≤ ((R.natAbs : ℕ) : ℝ) := by exact_mod_cast hn2n
      push_cast at h1
      rwa [hRn] at h1
    have hnR : (n : ℝ) ≤ Real.sqrt (R : ℝ) := by
      rw [← Real.sqrt_sq (Nat.cast_nonneg n)]
      exact Real.sqrt_le_sqrt hn2R
    have h1R : (1 : ℝ) ≤ Real.sqrt (R : ℝ) := Real.one_le_sqrt.mpr hR1
    linarith
  have h1' : (2 * (n : ℝ) + 1) * Real.sqrt (R : ℝ) ≤ 3 * (R : ℝ) := by
    have hsn : (0 : ℝ) ≤ Real.sqrt (R : ℝ) := Real.sqrt_nonneg _
    have hstep : (2 * (n : ℝ) + 1) * Real.sqrt (R : ℝ)
        ≤ (3 * Real.sqrt (R : ℝ)) * Real.sqrt (R : ℝ) :=
      mul_le_mul_of_nonneg_right hA hsn
    rw [show (3 * Real.sqrt (R : ℝ)) * Real.sqrt (R : ℝ)
          = 3 * (Real.sqrt (R : ℝ) * Real.sqrt (R : ℝ)) by ring, hRsq] at hstep
    exact hstep
  have hstepA : 2 * ((2 * (n : ℝ) + 1)
        * (2 * Real.sqrt (2 * (R : ℝ)) * (C3 * X ^ ((5 : ℝ) / 4))))
      ≤ 12 * Real.sqrt 2 * C3 * ((R : ℝ) * X ^ ((5 : ℝ) / 4)) := by
    have hsqrt2R : Real.sqrt (2 * (R : ℝ)) = Real.sqrt 2 * Real.sqrt (R : ℝ) :=
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
    rw [hsqrt2R]
    have hfac : (0 : ℝ) ≤ 4 * Real.sqrt 2 * C3 * X ^ ((5 : ℝ) / 4) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2)) (le_of_lt hC3))
        (Real.rpow_nonneg (by linarith) _)
    have hmain := mul_le_mul_of_nonneg_left h1' hfac
    nlinarith [hmain]
  have hX5 : X ^ ((5 : ℝ) / 4) ≤ X ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have hX32 : (0 : ℝ) ≤ X ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have hKnn : (0 : ℝ) ≤ 12 * Real.sqrt 2 * C3 := by positivity
  have hstepB : 12 * Real.sqrt 2 * C3 * ((R : ℝ) * X ^ ((5 : ℝ) / 4))
      ≤ (12 * Real.sqrt 2 * C3 + 1) * ((R.natAbs : ℝ) * X ^ ((3 : ℝ) / 2)) := by
    have h1 : 12 * Real.sqrt 2 * C3 * ((R : ℝ) * X ^ ((5 : ℝ) / 4))
        ≤ 12 * Real.sqrt 2 * C3 * ((R : ℝ) * X ^ ((3 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX5 hRnn) hKnn
    have h2 : 12 * Real.sqrt 2 * C3 * ((R : ℝ) * X ^ ((3 : ℝ) / 2))
        ≤ (12 * Real.sqrt 2 * C3 + 1) * ((R : ℝ) * X ^ ((3 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hRnn hX32)
    rw [hRn]
    linarith [h1, h2]
  calc (∑ W ∈ (Work.FIPlan.gBox R).erase 0,
        (Work.FIPlan.Zint W.re : ℝ) * crossInner X W)
      ≤ 2 * ∑ W ∈ B, crossInner X W := step1
    _ ≤ 2 * (∑ c₁ ∈ C1, ∑ s ∈ Finset.Icc (-R) R,
          crossInner X (⟨c₁ ^ 2, s⟩ : GaussianInt)) :=
        mul_le_mul_of_nonneg_left step2 (by norm_num)
    _ ≤ 2 * (∑ c₁ ∈ C1, ∑ y ∈ Work.FIArea1.Qbim X,
          (2 * Real.sqrt (2 * (R : ℝ) * |(y.im : ℝ)|) + 2)) :=
        mul_le_mul_of_nonneg_left step3 (by norm_num)
    _ ≤ 2 * ((2 * (n : ℝ) + 1)
          * (2 * Real.sqrt (2 * (R : ℝ)) * (C3 * X ^ ((5 : ℝ) / 4)))) :=
        mul_le_mul_of_nonneg_left step4 (by norm_num)
    _ ≤ 12 * Real.sqrt 2 * C3 * ((R : ℝ) * X ^ ((5 : ℝ) / 4)) := hstepA
    _ ≤ (12 * Real.sqrt 2 * C3 + 1) * ((R.natAbs : ℝ) * X ^ ((3 : ℝ) / 2)) := hstepB

/-- **The crude cross count with the real part of the substituted ball.**  (Route: `Qbim X` is the
non-real part of the ball `|z|² ≤ 2X`; the sum counts the quadruples `(W,c₁,y,c₂)` with `W` in the
box, `c₁² = Re W`, `y ∈ Qbim X` and `c₂² = Re(Wy)`.  Group by `(c₁,y)`: for fixed `c₁` (there are
`≤ 2√R+1` of them, since `|c₁| ≤ √R`) and fixed `y` (with `y.im ≠ 0`), the values
`Re((c₁²,W.im)·y) = c₁²y.re − W.im·y.im` as `W.im` runs over `[−R,R]` form an arithmetic
progression with difference `y.im`, so they hit a square at most `#{squares in an interval of
length 2R|y.im|} ≤ √(2R|y.im|) + 1` times.  With `Σ_{y∈Qbim X} √|y.im| ≤ C X^{5/4}` this gives
`≪ √R·√R·X^{5/4} = R X^{5/4} ≤ R X^{3/2}` for `X ≥ 1`.  No logarithm is lost.) -/
theorem offdiag_count_Qre_cross :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℤ) (X : ℝ), 1 ≤ R → 1 ≤ X →
      (∑ W ∈ (Work.FIPlan.gBox R).erase 0,
        (Work.FIPlan.Zint W.re : ℝ)
          * (∑ y ∈ Work.FIArea1.Qbim X, (Work.FIPlan.Zint (Work.FIPlan.cForm W y) : ℝ)))
        ≤ C * ((R.natAbs : ℝ) * X ^ ((3 : ℝ) / 2)) := by
  obtain ⟨C3, hC3, hQ⟩ := Qbim_sqrt_im_sum_le
  refine ⟨12 * Real.sqrt 2 * C3 + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith
  · intro R X hR hX
    exact cross_bound C3 hC3 sum_Zint_ap_le hQ R X hR hX

end

end Work.FIArea1
