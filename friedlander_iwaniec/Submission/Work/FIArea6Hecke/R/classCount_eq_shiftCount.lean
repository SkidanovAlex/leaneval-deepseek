/-
# `Submission.Work.FIArea6Hecke.R.classCount_eq_shiftCount`

The change of variable `z = p + 4d·w` identifies the Gaussian integers in the residue class of
`p` modulo `4d` with the shifted lattice `p/(4d) + ℤ²`, and it multiplies the squared modulus by
`(4d)²`: `|p + 4d·w|² = (4d)²·|w + p/(4d)|²`.  Hence the two counts defining `classCount` and
`shiftCount` coincide.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.DiscDefs

namespace Work.FIArea6Hecke.R

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The Gaussian norm is the squared complex modulus: `(gnorm z : ℝ) = z.re² + z.im²`. -/
lemma gnorm_eq_re_sq_add_im_sq (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
  rw [Work.FIPlan.gnorm, GaussianInt.natCast_natAbs_norm, GaussianInt.intCast_real_norm]
  simp [Complex.normSq_apply, GaussianInt.intCast_re, GaussianInt.intCast_im, sq]

/-- `(a, b) ∈ ℤ²` read as the Gaussian integer `a + bi`. -/
def gPair (w : ℤ × ℤ) : GaussianInt := ⟨w.1, w.2⟩

lemma gPair_injective : Function.Injective gPair := by
  intro a b h
  exact Prod.ext (by simpa [gPair] using congrArg Zsqrtd.re h)
    (by simpa [gPair] using congrArg Zsqrtd.im h)

lemma gPair_reim (u : GaussianInt) : gPair (u.re, u.im) = u := by
  ext <;> rfl

/-- The substitution `w ↦ p + 4d·w`, the inverse of `z ↦ (z - p)/(4d)`. -/
def discShiftMap (d : ℕ) (p : GaussianInt) (w : ℤ × ℤ) : GaussianInt :=
  p + (((4 * d : ℕ) : ℤ) : GaussianInt) * gPair w

lemma discShiftMap_re (d : ℕ) (p : GaussianInt) (w : ℤ × ℤ) :
    (discShiftMap d p w).re = p.re + ((4 * d : ℕ) : ℤ) * w.1 := by
  simp [discShiftMap, gPair]

lemma discShiftMap_im (d : ℕ) (p : GaussianInt) (w : ℤ × ℤ) :
    (discShiftMap d p w).im = p.im + ((4 * d : ℕ) : ℤ) * w.2 := by
  simp [discShiftMap, gPair]

lemma discShiftMap_sub (d : ℕ) (p : GaussianInt) (w : ℤ × ℤ) :
    discShiftMap d p w - p = (((4 * d : ℕ) : ℤ) : GaussianInt) * gPair w := by
  simp [discShiftMap]

lemma discShiftMap_re_coe (d : ℕ) (p : GaussianInt) (w : ℤ × ℤ) :
    ((discShiftMap d p w).re : ℝ) = (p.re : ℝ) + 4 * (d : ℝ) * (w.1 : ℝ) := by
  rw [discShiftMap_re]; push_cast; ring

lemma discShiftMap_im_coe (d : ℕ) (p : GaussianInt) (w : ℤ × ℤ) :
    ((discShiftMap d p w).im : ℝ) = (p.im : ℝ) + 4 * (d : ℝ) * (w.2 : ℝ) := by
  rw [discShiftMap_im]; push_cast; ring

/-- The substitution `w ↦ p + 4d·w` multiplies the squared modulus by `(4d)²`. -/
lemma gnorm_discShiftMap (d : ℕ) (hd : (d : ℝ) ≠ 0) (p : GaussianInt) (w : ℤ × ℤ) :
    (Work.FIPlan.gnorm (discShiftMap d p w) : ℝ)
      = (4 * (d : ℝ)) ^ 2 *
        (((w.1 : ℝ) + (p.re : ℝ) / (4 * (d : ℝ))) ^ 2
          + ((w.2 : ℝ) + (p.im : ℝ) / (4 * (d : ℝ))) ^ 2) := by
  rw [gnorm_eq_re_sq_add_im_sq, discShiftMap_re_coe, discShiftMap_im_coe, mul_add]
  rw [show (4 * (d : ℝ)) ^ 2 * ((w.1 : ℝ) + (p.re : ℝ) / (4 * (d : ℝ))) ^ 2
        = ((p.re : ℝ) + 4 * (d : ℝ) * (w.1 : ℝ)) ^ 2 from by field_simp; ring]
  rw [show (4 * (d : ℝ)) ^ 2 * ((w.2 : ℝ) + (p.im : ℝ) / (4 * (d : ℝ))) ^ 2
        = ((p.im : ℝ) + 4 * (d : ℝ) * (w.2 : ℝ)) ^ 2 from by field_simp; ring]

theorem classCount_eq_shiftCount {d : ℕ} (hd : 1 ≤ d) (p : GaussianInt) (X : ℝ) :
    Work.FIArea6Hecke.R.classCount d p X = Work.FIArea6Hecke.R.shiftCount d p X := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hdR : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hc_ne : (((4 * d : ℕ) : ℤ) : GaussianInt) ≠ 0 := by
    have hnat : (4 * d : ℕ) ≠ 0 := by omega
    have hint : (((4 * d : ℕ)) : ℤ) ≠ 0 := by exact_mod_cast hnat
    exact_mod_cast hint
  unfold classCount shiftCount
  refine (Set.BijOn.ncard_eq (f := fun w : ℤ × ℤ => discShiftMap d p w) ?_).symm
  refine ⟨?_, ?_, ?_⟩
  · -- `MapsTo`: `w ↦ p + 4d·w` lands in the class of `p` modulo `4d`
    intro w hw
    refine ⟨?_, ?_⟩
    · exact ⟨gPair w, discShiftMap_sub d p w⟩
    · have hg := gnorm_discShiftMap d hdR p w
      rw [hg]
      have h16 : (4 * (d : ℝ)) ^ 2 = 16 * (d : ℝ) ^ 2 := by ring
      have hX : (4 * (d : ℝ)) ^ 2 * (X / (16 * (d : ℝ) ^ 2)) = X := by
        rw [h16]; field_simp
      calc (4 * (d : ℝ)) ^ 2 * (((w.1 : ℝ) + (p.re : ℝ) / (4 * (d : ℝ))) ^ 2
              + ((w.2 : ℝ) + (p.im : ℝ) / (4 * (d : ℝ))) ^ 2)
          ≤ (4 * (d : ℝ)) ^ 2 * (X / (16 * (d : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hw (by positivity)
        _ = X := hX
  · -- `InjOn`
    intro w _ w' _ h
    have hmul : (((4 * d : ℕ) : ℤ) : GaussianInt) * gPair w
        = (((4 * d : ℕ) : ℤ) : GaussianInt) * gPair w' := by
      have h' : p + (((4 * d : ℕ) : ℤ) : GaussianInt) * gPair w
          = p + (((4 * d : ℕ) : ℤ) : GaussianInt) * gPair w' := by
        simpa only [discShiftMap] using h
      exact add_left_cancel h'
    exact gPair_injective (mul_left_cancel₀ hc_ne hmul)
  · -- `SurjOn`
    intro z hz
    obtain ⟨u, hu⟩ := hz.1
    refine ⟨(u.re, u.im), ?_, ?_⟩
    · change ((u.re : ℝ) + (p.re : ℝ) / (4 * (d : ℝ))) ^ 2
          + ((u.im : ℝ) + (p.im : ℝ) / (4 * (d : ℝ))) ^ 2 ≤ X / (16 * (d : ℝ) ^ 2)
      have hzeq : discShiftMap d p (u.re, u.im) = z := by
        show p + (((4 * d : ℕ) : ℤ) : GaussianInt) * gPair (u.re, u.im) = z
        rw [gPair_reim, ← hu]
        ring
      have hg := gnorm_discShiftMap d hdR p (u.re, u.im)
      rw [hzeq] at hg
      have h16 : (4 * (d : ℝ)) ^ 2 = 16 * (d : ℝ) ^ 2 := by ring
      have hX : (4 * (d : ℝ)) ^ 2 *
          (((u.re : ℝ) + (p.re : ℝ) / (4 * (d : ℝ))) ^ 2
            + ((u.im : ℝ) + (p.im : ℝ) / (4 * (d : ℝ))) ^ 2) ≤ X := by
        rw [← hg]; exact hz.2
      have hpos : 0 < 16 * (d : ℝ) ^ 2 := by positivity
      rw [le_div_iff₀ hpos, ← h16, mul_comm _ ((4 * (d : ℝ)) ^ 2)]
      exact hX
    · show p + (((4 * d : ℕ) : ℤ) : GaussianInt) * gPair (u.re, u.im) = z
      rw [gPair_reim, ← hu]
      ring

end

end Work.FIArea6Hecke.R
