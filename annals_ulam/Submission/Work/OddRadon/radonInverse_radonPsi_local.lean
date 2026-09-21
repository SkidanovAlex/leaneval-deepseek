import Mathlib
import Submission.Work.OddCurve.LowSlope.radonInverse_radonPhi
import Submission.Work.OddRadon.radonProfile_inv_local
import Submission.Work.OddCurve.LowSlope.Datum

/-!
# The local inverse of the second Radon datum of a low-slope profile

`Work.OddCurve.LowSlope.radonInverse_radonPsi` computes `radonInverse n (radonPsi n ρ) u` for
`u ∈ (0,1)` from two *global* hypotheses on the weight `u ↦ u ρ(u)^{2n+1}`: that it extends
continuously to `[-1,1]`, and that the even profile
`u ↦ u/2 (ρ u^{2n+1} - ρ(-u)^{2n+1})` is `C¹` on `[-1,1]`.

In the low-slope step of the odd-dimensional case only the values of `ρ` on `(-c₁,c₁)`,
`c₁ < 1`, are known (the anchor's data determine `ρ` on the cap `|u| ≤ c₁` only), so both global
hypotheses are unavailable.  This file proves the same identity with **only** the locality that
the low-slope step supplies:

  `ρ` is `C^∞` on `(-1,1)`, and `0 < u < c₁ < 1`.

Two points make the local form true:

* the even profile `γ u = u/2 (ρ u^{2n+1} - ρ(-u)^{2n+1})` is `C¹` on `[-c₁,c₁]`, because
  `u ↦ ±u` maps `[-c₁,c₁]` into the open interval `(-1,1)` on which `ρ` is smooth;
* the Radon datum `radonPsi n ρ` only sees `γ` on `[-c,c]` for `c` below the point `u` at which
  it is inverted, and `c < c₁`, so the integrands `s ↦ (c s) ρ (c s)^{2n+1}` are continuous on
  `[-1,1]` (they are the smooth weight composed with `s ↦ c s`, which maps `[-1,1]` into
  `(-c₁,c₁) ⊆ (-1,1)`) — no control of `ρ` near `±1` is needed.

The proof then follows `radonInverse_radonPsi` verbatim, with `radonProfile_inv_local` in place
of `radonProfile_inv` and with `b = (u+c₁)/2` as the locality threshold, using
`radonInverse_congr_of_eqOn`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddRadon

/-- **The odd weight composed with a dilation is continuous on `[-1,1]`** as soon as the
dilation factor has modulus `< 1` and the profile is smooth on `(-1,1)`.  This is the local form
of `Work.OddCurve.LowSlope.continuousOn_weight_comp_mul`, which assumes the *global* continuity
of the weight on `[-1,1]`: here only `s ↦ c s`, `|c| < 1`, is composed. -/
lemma continuousOn_weight_comp_mul_of_contDiffOn (n : ℕ) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    {a : ℝ} (ha : |a| < 1) :
    ContinuousOn (fun s : ℝ => (a * s) * ρ (a * s) ^ (2 * n + 1)) (Set.uIcc (-1 : ℝ) 1) := by
  have hγ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => u * ρ u ^ (2 * n + 1)) (Set.Ioo (-1 : ℝ) 1) :=
    contDiffOn_id.mul (hρ.pow (2 * n + 1))
  have hlin : ContinuousOn (fun s : ℝ => a * s) (Set.uIcc (-1 : ℝ) 1) := by fun_prop
  have hmaps : Set.MapsTo (fun s : ℝ => a * s) (Set.uIcc (-1 : ℝ) 1) (Set.Ioo (-1 : ℝ) 1) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.mem_Icc] at hs
    have hsabs : |s| ≤ 1 := abs_le.mpr ⟨hs.1, hs.2⟩
    have hle : |a * s| ≤ |a| := by
      rw [abs_mul]
      calc |a| * |s| ≤ |a| * 1 := mul_le_mul_of_nonneg_left hsabs (abs_nonneg a)
        _ = |a| := mul_one _
    exact abs_lt.mp (lt_of_le_of_lt hle ha)
  exact hγ.continuousOn.comp hlin hmaps

/-- **The second Radon datum of a low-slope profile inverts to the odd (even-part) weight,
locally in the profile.**  Only the smoothness of `ρ` on the *open* interval `(-1,1)` is needed,
because the inversion at `u` uses the datum only on `(0,(u+c₁)/2) ⊆ (0,c₁)` and the profile `ρ`
only on `[-(u+c₁)/2, (u+c₁)/2]`. -/
lemma radonInverse_radonPsi_local (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ} {c₁ u : ℝ}
    (hc₁ : c₁ < 1) (hρsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    (hu : 0 < u) (huc : u < c₁) :
    Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.radonPsi n ρ) u
      = u / 2 * (ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)) := by
  set γ : ℝ → ℝ := fun v => v / 2 * (ρ v ^ (2 * n + 1) - ρ (-v) ^ (2 * n + 1)) with hγdef
  change radonInverse n (Work.OddCurve.LowSlope.radonPsi n ρ) u = γ u
  have hγeven : ∀ t : ℝ, γ (-t) = γ t := by
    intro t
    rw [hγdef]
    simp only []
    ring_nf
  -- `γ` is `C¹` on `[-c₁,c₁]`: both `v ↦ ρ v ^ (2n+1)` and `v ↦ ρ (-v) ^ (2n+1)` are
  -- smooth there, because `±v` stays in the open interval `(-1,1)` on which `ρ` is smooth.
  have hγsm : ContDiffOn ℝ 1 γ (Set.Icc (-c₁) c₁) := by
    rw [hγdef]
    have hmapid : Set.MapsTo (fun v : ℝ => v) (Set.Icc (-c₁) c₁) (Set.Ioo (-1 : ℝ) 1) := by
      intro v hv
      rw [Set.mem_Icc] at hv
      exact ⟨by linarith [hv.1], by linarith [hv.2, hc₁]⟩
    have hmapneg : Set.MapsTo (fun v : ℝ => -v) (Set.Icc (-c₁) c₁) (Set.Ioo (-1 : ℝ) 1) := by
      intro v hv
      rw [Set.mem_Icc] at hv
      exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
    have h1 : ContDiffOn ℝ 1 (fun v : ℝ => ρ v ^ (2 * n + 1)) (Set.Icc (-c₁) c₁) :=
      ((hρsm.of_le (by simp)).comp contDiffOn_id hmapid).pow _
    have h2 : ContDiffOn ℝ 1 (fun v : ℝ => ρ (-v) ^ (2 * n + 1)) (Set.Icc (-c₁) c₁) :=
      ((hρsm.of_le (by simp)).comp (by fun_prop) hmapneg).pow _
    exact (contDiffOn_id.div_const 2).mul (h1.sub h2)
  -- inversion of the even profile `γ` on the cap `(0,c₁)`, at the interior threshold `(u+c₁)/2`
  have hleft := Work.OddRadon.radonProfile_inv_local n hn (γ := γ) (c₀ := (u + c₁) / 2) (c₁ := c₁)
    (by linarith) (by linarith) hc₁ hγsm hγeven (u := u) ⟨hu, by linarith⟩
  rw [hleft]
  -- it remains to identify `radonPsi n ρ` with `radonProfile (2n+1) γ` below `(u+c₁)/2`
  refine Work.OddCurve.LowSlope.radonInverse_congr_of_eqOn n hu (b := (u + c₁) / 2) (by linarith) ?_
  intro c hc
  have hcabs : |c| < 1 := abs_lt.mpr ⟨by linarith [hc.1], by linarith [hc.2, hc₁]⟩
  have hG₁ : ContinuousOn (fun s : ℝ => (c * s) * ρ (c * s) ^ (2 * n + 1))
      (Set.uIcc (-1 : ℝ) 1) :=
    continuousOn_weight_comp_mul_of_contDiffOn n hρsm hcabs
  have hG₂ : ContinuousOn (fun s : ℝ => (-(c * s)) * ρ (-(c * s)) ^ (2 * n + 1))
      (Set.uIcc (-1 : ℝ) 1) := by
    have := continuousOn_weight_comp_mul_of_contDiffOn n hρsm (a := -c) (by simpa using hcabs)
    simpa only [neg_mul] using this
  have hf := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hG₁
  have hg := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hG₂
  -- `radonProfile` sees only the even part of the weight `v ↦ v ρ v^{2n+1}`
  have h1 : Work.OddCurve.LowSlope.radonPsi n ρ c
      = Work.OddRadon.radonProfile (2 * n + 1)
          (fun v : ℝ => (v * ρ v ^ (2 * n + 1)
            + (fun w : ℝ => w * ρ w ^ (2 * n + 1)) (-v)) / 2) c := by
    unfold Work.OddCurve.LowSlope.radonPsi
    exact Work.OddCurve.LowSlope.radonProfile_evenPart (2 * n + 1) hf hg
  have h2 : (fun v : ℝ => (v * ρ v ^ (2 * n + 1)
      + (fun w : ℝ => w * ρ w ^ (2 * n + 1)) (-v)) / 2) = γ := by
    funext v
    rw [hγdef]
    simp only []
    ring
  rw [h1, h2]

end Work.OddRadon
