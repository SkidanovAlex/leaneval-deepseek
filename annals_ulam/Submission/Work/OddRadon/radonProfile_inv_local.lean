import Mathlib
import Submission.Work.OddRadon.RadonInversion
import Submission.Work.OddCurve.LowSlope.Datum
import Submission.Work.OddRadon.abelInvert_comp_mul_left
import Submission.Work.OddRadon.abelReduceIter_comp_mul_left

/-!
# Locality of the Radon inversion in the profile variable (`Work.OddRadon`)

`radonProfile_inv` inverts the one-variable Radon transform `radonProfile (2n+1)` on an even
profile of class `C¹` on the **whole** interval `[-1,1]`.  The low-slope step of the
odd-dimensional case only knows the profile `γ` on a smaller interval `[-c₁,c₁]`, `c₁ < 1`
(typically `c₁ = cos(arctan a)` for the anchor's slope range), and needs the inversion on the
cap `(0,c₀)`, `c₀ < c₁`, where the Radon datum only sees `γ` on `[-c₀,c₀]`.

The reduction to `radonProfile_inv` is by **rescaling the profile**:

  `G := γ (c₁ ·)`

is even and `C¹` on `[-1,1]` (the map `t ↦ c₁ t` sends `[-1,1]` into `[-c₁,c₁]`), so
`radonProfile_inv` applies to `G` at the point `u/c₁ ∈ (0,1)`:

  `γ u = G (u/c₁) = radonInverse n (radonProfile (2n+1) G) (u/c₁)`,

and `radonProfile (2n+1) G = (radonProfile (2n+1) γ) ∘ (c₁ ·)`.  The elementary scaling law
of the inverse operator,

  `radonInverse n (F (b ·)) (u/b) = radonInverse n F u`   (`b > 0`, `u > 0`),

then turns this into the desired `γ u = radonInverse n (radonProfile (2n+1) γ) u`.  The scaling
law is proved from its two halves:

* `abelReduceIter_comp_mul_left` — one dilation of the argument gains `b²` at each of the
  `n-1` exponent-reduction steps, i.e. `b^(2(n-1))`, which exactly cancels the factor
  `b^(-(2n-2))` relating the two Abel data;
* `abelInvert_comp_mul_left` — the change of variable `c = t/b` in the classical Abel
  inversion.
-/

noncomputable section

open MeasureTheory Set

open scoped Topology ContDiff Interval

namespace Work.OddRadon

/-- **Scaling of the Radon profile in the profile variable** (no regularity needed): the profile
`t ↦ γ (b t)` has Radon profile the rescaled datum `c ↦ radonProfile d γ (b c)`. -/
lemma radonProfile_comp_mul_left (d : ℕ) (γ : ℝ → ℝ) (b c : ℝ) :
    radonProfile d (fun t => γ (b * t)) c = radonProfile d γ (b * c) := by
  simp only [radonProfile]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  beta_reduce
  rw [mul_assoc b c s]

/-- The iterated exponent reduction is linear in a constant factor. -/
private lemma abelReduceIter_const_mul (α C : ℝ) (k : ℕ) (F : ℝ → ℝ) :
    abelReduceIter α k (fun c => C * F c) = fun c => C * abelReduceIter α k F c := by
  induction k generalizing α C F with
  | zero => rfl
  | succ k ih =>
      rw [abelReduceIter_succ, abelReduceIter_succ, abelReduce_const_mul]
      exact ih (α - 1) C (abelReduce α F)

/-- **Scaling law of the inverse Radon operator**: dilating the datum by `b > 0` dilates the
argument of `radonInverse` by `b`.  Both the prefactor `c^(2n-2)` of the Abel datum (which
contributes `b^(-(2n-2))`) and the `n-1` exponent reductions (which contribute `b^(2(n-1))`)
are taken into account; the two powers cancel. -/
private lemma radonInverse_dilate (n : ℕ) {F : ℝ → ℝ} {b u : ℝ}
    (hb : 0 < b) (hu : 0 < u) :
    radonInverse n (fun c : ℝ => F (b * c)) (u / b) = radonInverse n F u := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hpow : 2 * (n - 1) = 2 * n - 2 := by omega
  set Φ : ℝ → ℝ := fun c => (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * F c with hΦ
  set Φb : ℝ → ℝ := fun c => (2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * F (b * c)
    with hΦb
  -- the dilated datum is the old one, dilated and multiplied by `(b^(2n-2))⁻¹`
  have hdil : Φb = fun c : ℝ => (b ^ (2 * n - 2))⁻¹ * Φ (b * c) := by
    funext c
    simp only [hΦb, hΦ, mul_pow]
    rw [show (2 * sphereArea (2 * n - 2))⁻¹ * (b ^ (2 * n - 2) * c ^ (2 * n - 2)) * F (b * c)
        = b ^ (2 * n - 2) * ((2 * sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2) * F (b * c))
        by ring]
    rw [inv_mul_cancel_left₀ (pow_ne_zero _ hbne)]
  have hred : abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) Φb
      = fun y : ℝ => abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) Φ (b * y) := by
    rw [hdil, abelReduceIter_const_mul]
    funext y
    rw [abelReduceIter_comp_mul_left hbne, hpow,
      inv_mul_cancel_left₀ (pow_ne_zero (2 * n - 2) hbne)]
  show abelInvert (abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) Φb) (u / b)
      = abelInvert (abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) Φ) u
  rw [hred]
  exact abelInvert_comp_mul_left hb hu

/-- **Inversion of the one-variable Radon transform, locally in the profile.**

For `d = 2n+1` (`n ≥ 1`), an even profile `γ` of class `C¹` on `[-c₁,c₁]` with `c₁ < 1` is
recovered by `radonInverse n` from its Radon profile at every `u ∈ (0,c₀)`, `c₀ < c₁`.  This is
`radonProfile_inv` with the regularity hypothesis weakened from `[-1,1]` to `[-c₁,c₁]`, which is
the only form available in the low-slope step of the odd case. -/
theorem radonProfile_inv_local (n : ℕ) (hn : 1 ≤ n) {γ : ℝ → ℝ} {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₀₁ : c₀ < c₁) (hc₁ : c₁ < 1)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc (-c₁) c₁)) (heven : ∀ t, γ (-t) = γ t)
    {u : ℝ} (hu : u ∈ Set.Ioo (0 : ℝ) c₀) :
    γ u = Work.OddRadon.radonInverse n
      (Work.OddRadon.radonProfile (2 * n + 1) γ) u := by
  have hc₁pos : (0 : ℝ) < c₁ := lt_trans hc₀ hc₀₁
  have hc₁ne : c₁ ≠ 0 := ne_of_gt hc₁pos
  -- the rescaled profile `G = γ (c₁ ·)` is even and `C¹` on `[-1,1]`
  have hGsm : ContDiffOn ℝ 1 (fun t : ℝ => γ (c₁ * t)) (Set.Icc (-1 : ℝ) 1) := by
    refine hγ.comp ?_ ?_
    · fun_prop
    · intro t ht
      rw [Set.mem_Icc] at ht ⊢
      constructor <;> nlinarith [ht.1, ht.2, hc₁pos]
  have hGeven : ∀ t : ℝ, (fun t : ℝ => γ (c₁ * t)) (-t) = (fun t : ℝ => γ (c₁ * t)) t := by
    intro t
    simp only []
    rw [show c₁ * -t = -(c₁ * t) by ring, heven]
  have hu1 : u / c₁ ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos hu.1 hc₁pos, ?_⟩
    rw [div_lt_one hc₁pos]
    exact lt_trans hu.2 hc₀₁
  -- its Radon profile is the datum of `γ`, rescaled in the `c` variable
  have hprof : radonProfile (2 * n + 1) (fun t : ℝ => γ (c₁ * t))
      = fun c : ℝ => radonProfile (2 * n + 1) γ (c₁ * c) := by
    funext c
    exact radonProfile_comp_mul_left (2 * n + 1) γ c₁ c
  have hGu : γ (c₁ * (u / c₁)) = γ u := by rw [mul_div_cancel₀ u hc₁ne]
  have hkey := radonProfile_inv n hn hGsm hGeven hu1
  rw [hprof] at hkey
  rw [hGu] at hkey
  rw [hkey]
  exact radonInverse_dilate n hc₁pos hu.1

end Work.OddRadon
