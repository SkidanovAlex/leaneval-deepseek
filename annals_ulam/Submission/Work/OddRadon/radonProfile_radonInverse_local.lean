import Mathlib
import Submission.Work.OddRadon.radonProfile_radonInverse
import Submission.Work.OddRadon.radonInverse_comp_mul_left

/-!
# Inversion of the Radon profile on a local interval: `radonProfile (2n+1) ∘ radonInverse n`

`radonProfile_radonInverse` says that for an even `C^∞` datum `F` on the **whole** interval
`[0,1]` the inverse operator `radonInverse n` reproduces `F`:

  `radonProfile (2n+1) (fun u => radonInverse n F |u|) c = F c`   (`c ∈ (0,1)`).

Here we localise this to a datum `F` that is only smooth on `[0,b]`, `b ≤ 1` (the form in
which the data occur in the low-slope step of the odd-dimensional case): the identity then
holds on `(0,b)`.

The reduction is by rescaling the datum, `F_b t = F (b t)`, which is even and `C^∞` on
`[0,1]`.  Two scaling laws transfer the statement for `F_b` back to `F`:

* `radonProfile (2n+1) (γ ∘ (b ·)) c = radonProfile (2n+1) γ (b c)`
  (`radonProfile_comp_mul_left_local`), and
* `radonInverse n (F ∘ (b ·)) v = radonInverse n F (b v)` for `v > 0`
  (`radonInverse_comp_mul_left`).

Applying `radonProfile_radonInverse` to `F_b` at `c/b ∈ (0,1)` and rewriting both sides with
these laws gives the claim at `b * (c/b) = c`.
-/

namespace Work.OddRadon

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

/-- **Locality of `radonProfile` in the profile variable**: changing the profile at the single
point `0` does not change the Radon profile, since the defining interval integral ignores
sets of measure zero. -/
lemma radonProfile_congr_zero {d : ℕ} {γ₁ γ₂ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ x : ℝ, x ≠ 0 → γ₁ x = γ₂ x) : radonProfile d γ₁ c = radonProfile d γ₂ c := by
  simp only [radonProfile]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hcompl : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({0} : Set ℝ) :=
    MeasureTheory.compl_mem_ae_iff.mpr ((Set.finite_singleton (0 : ℝ)).measure_zero volume)
  filter_upwards [hcompl] with s hs _
  rw [h (c * s) (mul_ne_zero (ne_of_gt hc) (by simpa using hs))]

/-- **Scaling of the Radon profile in the profile variable** (no regularity needed): the
profile `t ↦ γ (b t)` has Radon profile the rescaled datum `c ↦ radonProfile d γ (b c)`. -/
lemma radonProfile_comp_mul_left_local (d : ℕ) (γ : ℝ → ℝ) (b c : ℝ) :
    radonProfile d (fun t : ℝ => γ (b * t)) c = radonProfile d γ (b * c) := by
  simp only [radonProfile]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  beta_reduce
  rw [mul_assoc b c s]

/-- **Inversion of the Radon profile for data that are smooth only on `[0,b]`** (`b ≤ 1`):
for an even `F` of class `C^∞` on `[0,b]`, the inverse operator `radonInverse n` reproduces
`F` on `(0,b)`,

  `radonProfile (2n+1) (fun u => radonInverse n F |u|) c = F c`   (`c ∈ (0,b)`). -/
theorem radonProfile_radonInverse_local (n : ℕ) (hn : 1 ≤ n) {F : ℝ → ℝ} {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Set.Icc (0 : ℝ) b))
    (heven : ∀ t : ℝ, F (-t) = F t) :
    ∀ c ∈ Set.Ioo (0 : ℝ) b,
      Work.OddRadon.radonProfile (2 * n + 1)
        (fun u : ℝ => Work.OddRadon.radonInverse n F |u|) c = F c := by
  intro c hc
  have hbne : b ≠ 0 := ne_of_gt hb
  set Fb : ℝ → ℝ := fun t : ℝ => F (b * t) with hFb
  -- the rescaled datum is even and `C^∞` on `[0,1]`
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fb (Set.Icc (0 : ℝ) 1) := by
    rw [hFb]
    refine hF.comp ?_ ?_
    · exact (((contDiff_const (c := b)).mul contDiff_id).contDiffOn).mono (Set.subset_univ _)
    · intro t ht
      rw [Set.mem_Icc] at ht ⊢
      exact ⟨mul_nonneg hb.le ht.1, by nlinarith [ht.2, hb.le]⟩
  have hev : ∀ t : ℝ, Fb (-t) = Fb t := by
    intro t
    simp only [hFb]
    rw [show b * -t = -(b * t) by ring, heven]
  -- the theorem for the rescaled datum, evaluated at `c / b`
  have hs : c / b ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨div_pos hc.1 hb, (div_lt_one hb).mpr hc.2⟩
  have hmain := radonProfile_radonInverse n hn hsm hev (c / b) hs
  -- `radonInverse n Fb` and `radonInverse n F (b ·)` agree away from `0`
  have hcongr : radonProfile (2 * n + 1) (fun u : ℝ => radonInverse n Fb |u|) (c / b)
      = radonProfile (2 * n + 1) (fun u : ℝ => radonInverse n F |b * u|) (c / b) := by
    refine radonProfile_congr_zero (div_pos hc.1 hb) ?_
    intro x hx
    simp only [hFb]
    have hd := radonInverse_comp_mul_left (n := n) (F := F) (b := b) (u := b * |x|) hb
      (mul_pos hb (abs_pos.mpr hx))
    rw [mul_div_cancel_left₀ |x| hbne] at hd
    rw [hd, abs_mul, abs_of_pos hb]
  -- the two scaling laws
  have hstep : radonProfile (2 * n + 1) (fun u : ℝ => radonInverse n F |b * u|) (c / b)
      = radonProfile (2 * n + 1) (fun u : ℝ => radonInverse n F |u|) (b * (c / b)) :=
    radonProfile_comp_mul_left_local (2 * n + 1) (fun u : ℝ => radonInverse n F |u|) b (c / b)
  have hbd : b * (c / b) = c := mul_div_cancel₀ c hbne
  have hgoal : radonProfile (2 * n + 1) (fun u : ℝ => radonInverse n F |u|) (b * (c / b))
      = F c := by
    rw [← hstep, ← hcongr, hmain]
    simp only [hFb]
    rw [hbd]
  simpa [hbd] using hgoal

end

end Work.OddRadon
