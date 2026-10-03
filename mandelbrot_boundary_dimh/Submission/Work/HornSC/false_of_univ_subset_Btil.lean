import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Parab.basinEnters.zero_not_mem_basin
import Submission.Work.FatouCH.injEntireAffineGrowth
import Submission.Work.Horn.basic
import Submission.Work.HornSC.differentiable_E_of_univ_subset

namespace Work.HornSC

open MandelDim Filter Set Metric
open scoped Topology

noncomputable section

/-!
# `B̃ = φ⁻¹(B)` is a proper subset of the plane

`B̃ = Btil d B = {w | w ∈ d.Dφ ∧ d.φ w ∈ B}` is the back-transport of the immediate parabolic
basin `B` by the Fatou coordinate `φ`.  It is never all of `ℂ`: if `d.Dφ = ℂ` and `φ` maps all
of `ℂ` into `B`, then

* the lifted horn map `E w = Φ (φ w)` is entire, `T`-equivariant (`E (w+1) = E w + 1`) and
  satisfies `E w - w → 0` at the upper end `Im w → +∞` and `E w - w → cl` at the lower end;
* hence `g w = E w - w` is entire, `1`-periodic and bounded at both ends, so it is constant
  (`periodic_entire_const_aux`, Liouville), say `E w = w + c₀`;
* consequently `φ` is injective (`φ w = φ w' ⇒ w = w'` via `Φ ∘ φ`), and `φ` is entire and
  injective, hence affine with nonzero slope (`Work.FatouCH.injEntire_affine_growth`), hence
  surjective onto `ℂ`, so `0 ∈ φ '' ℂ ⊆ B`;
* but `0 ∉ B` (`Work.Parab.basinEnters.zero_not_mem_parabolicBasin`), a contradiction.
-/

/-- An entire `1`-periodic function tending to a finite limit at both ends of the cylinder
(`Im w → ±∞`) is constant.  Interval `[R₂, R₁]` of imaginary parts is handled by reducing to the
compact fundamental domain `{0 ≤ Re w ≤ 1, R₂ ≤ Im w ≤ R₁}` via periodicity, and Liouville
finishes. -/
private lemma periodic_entire_const_aux (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hper : ∀ w : ℂ, g (w + 1) = g w)
    (hup : Filter.Tendsto g MandelDim.upperEnd (nhds (0 : ℂ)))
    {c : ℂ} (hlow : Filter.Tendsto g MandelDim.lowerEnd (nhds c)) :
    ∃ c₀ : ℂ, ∀ w : ℂ, g w = c₀ := by
  -- the period is preserved by all integer shifts
  have hperZ : ∀ (n : ℤ) (w : ℂ), g (w + (n : ℂ)) = g w := by
    have hnat : ∀ (m : ℕ) (w : ℂ), g (w + ((m : ℤ) : ℂ)) = g w := by
      intro m
      induction m with
      | zero => intro w; simp
      | succ k ih =>
          intro w
          have h : w + (((k + 1 : ℕ) : ℤ) : ℂ) = w + ((k : ℤ) : ℂ) + 1 := by push_cast; ring
          rw [h, hper, ih]
    have hneg : ∀ (m : ℕ) (w : ℂ), g (w - ((m : ℤ) : ℂ)) = g w := by
      intro m
      induction m with
      | zero => intro w; simp
      | succ k ih =>
          intro w
          have h : w - (((k + 1 : ℕ) : ℤ) : ℂ) = w - ((k : ℤ) : ℂ) - 1 := by push_cast; ring
          rw [h]
          have h2 : g (w - ((k : ℤ) : ℂ) - 1) = g (w - ((k : ℤ) : ℂ)) := by
            have hh := hper (w - ((k : ℤ) : ℂ) - 1)
            rw [sub_add_cancel] at hh
            exact hh.symm
          rw [h2, ih]
    intro n w
    obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg n
    · subst hm
      exact hnat m w
    · subst hm
      have hc : ((-(↑m) : ℤ) : ℂ) = -(((m : ℤ)) : ℂ) := by push_cast; ring
      rw [hc]
      simpa [sub_eq_add_neg] using hneg m w
  have hperZs : ∀ (n : ℤ) (w : ℂ), g (w - (n : ℂ)) = g w := by
    intro n w
    have h : w - (n : ℂ) = w + ((-n : ℤ) : ℂ) := by push_cast; ring
    rw [h, hperZ]
  -- bound near the upper end
  obtain ⟨R₁, hR₁⟩ : ∃ R : ℝ, ∀ w : ℂ, R ≤ w.im → ‖g w‖ < 1 := by
    have hb : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) := Metric.ball_mem_nhds 0 one_pos
    have hmem : ∀ᶠ w in MandelDim.upperEnd, g w ∈ Metric.ball (0:ℂ) 1 := hup hb
    simp only [MandelDim.upperEnd] at hmem
    obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (Filter.eventually_comap.mp hmem)
    refine ⟨a, fun w hw => ?_⟩
    have h := ha w.im hw w rfl
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h
  -- bound near the lower end
  obtain ⟨R₂, hR₂⟩ : ∃ R : ℝ, ∀ w : ℂ, w.im ≤ R → ‖g w‖ ≤ 2 * ‖c‖ + 1 := by
    have hb : Metric.ball c (‖c‖ + 1) ∈ nhds c := Metric.ball_mem_nhds c (by positivity)
    have hmem : ∀ᶠ w in MandelDim.lowerEnd, g w ∈ Metric.ball c (‖c‖ + 1) := hlow hb
    simp only [MandelDim.lowerEnd] at hmem
    obtain ⟨a, ha⟩ := Filter.eventually_atBot.mp (Filter.eventually_comap.mp hmem)
    refine ⟨a, fun w hw => ?_⟩
    have h := ha w.im hw w rfl
    rw [Metric.mem_ball, dist_eq_norm] at h
    have htri : ‖g w‖ ≤ ‖g w - c‖ + ‖c‖ := by
      have := norm_add_le (g w - c) c
      rwa [show (g w - c) + c = g w by ring] at this
    linarith
  -- a compact fundamental domain
  set K : Set ℂ := {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 ∧ R₂ ≤ w.im ∧ w.im ≤ R₁} with hKdef
  have hKclosed : IsClosed K := by
    rw [show K = Complex.re ⁻¹' (Set.Icc (0:ℝ) 1) ∩ Complex.im ⁻¹' (Set.Icc R₂ R₁) by
      ext w; simp [hKdef, Set.mem_Icc, and_assoc]]
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  have hKbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mpr ⟨1 + |R₁| + |R₂|, fun w hw => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := Complex.norm_le_abs_re_add_abs_im w
    have hre : |w.re| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [hw.1], hw.2.1⟩
    have him : |w.im| ≤ |R₁| + |R₂| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le R₁, neg_abs_le R₂, abs_nonneg R₁, abs_nonneg R₂,
                hw.2.2.1, hw.2.2.2],
             by linarith [le_abs_self R₁, le_abs_self R₂, abs_nonneg R₁, abs_nonneg R₂,
                hw.2.2.1, hw.2.2.2]⟩
    linarith
  have hK : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKclosed, hKbdd⟩
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (hg.continuous.norm.continuousOn)
  set B₀ : ℝ := max (max 1 (2 * ‖c‖ + 1)) M₀ with hB₀
  have hB₁ : (1:ℝ) ≤ B₀ := le_trans (le_max_left 1 (2 * ‖c‖ + 1)) (le_max_left _ _)
  have hBc : 2 * ‖c‖ + 1 ≤ B₀ := le_trans (le_max_right 1 (2 * ‖c‖ + 1)) (le_max_left _ _)
  have hBM : M₀ ≤ B₀ := le_max_right _ _
  -- the global bound
  have hbddall : ∀ w : ℂ, ‖g w‖ ≤ B₀ := by
    intro w
    rcases le_or_gt R₁ w.im with h1 | h1
    · exact le_trans (le_of_lt (hR₁ w h1)) hB₁
    rcases le_or_gt w.im R₂ with h2 | h2
    · exact le_trans (hR₂ w h2) hBc
    have hmem : w - ((⌊w.re⌋ : ℤ) : ℂ) ∈ K := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hh : (w - ((⌊w.re⌋ : ℤ) : ℂ)).re = Int.fract w.re := by
          have h : (((⌊w.re⌋ : ℤ)) : ℂ).re = (⌊w.re⌋ : ℝ) := by simp
          rw [Complex.sub_re, h]; rfl
        rw [hh]; exact Int.fract_nonneg w.re
      · have hh : (w - ((⌊w.re⌋ : ℤ) : ℂ)).re = Int.fract w.re := by
          have h : (((⌊w.re⌋ : ℤ)) : ℂ).re = (⌊w.re⌋ : ℝ) := by simp
          rw [Complex.sub_re, h]; rfl
        rw [hh]; exact le_of_lt (Int.fract_lt_one w.re)
      · have hh : (w - ((⌊w.re⌋ : ℤ) : ℂ)).im = w.im := by
          have h : (((⌊w.re⌋ : ℤ)) : ℂ).im = 0 := by simp
          rw [Complex.sub_im, h, sub_zero]
        rw [hh]; exact le_of_lt h2
      · have hh : (w - ((⌊w.re⌋ : ℤ) : ℂ)).im = w.im := by
          have h : (((⌊w.re⌋ : ℤ)) : ℂ).im = 0 := by simp
          rw [Complex.sub_im, h, sub_zero]
        rw [hh]; exact le_of_lt h1
    have h1' : ‖g (w - ((⌊w.re⌋ : ℤ) : ℂ))‖ ≤ M₀ := by simpa using hM₀ _ hmem
    rw [hperZs ⌊w.re⌋ w] at h1'
    exact le_trans h1' hBM
  have hbounded : Bornology.IsBounded (Set.range g) := by
    refine (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mpr ⟨B₀, fun y hy => ?_⟩
    obtain ⟨w, rfl⟩ := hy
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbddall w
  obtain ⟨c₀, hc₀⟩ := hg.exists_eq_const_of_bounded hbounded
  exact ⟨c₀, fun w => congrFun hc₀ w⟩

theorem false_of_univ_subset_Btil {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (d : MandelDim.ParabData f₀ D₀) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (h : Set.univ ⊆ MandelDim.Btil d B) : False := by
  have hgerm : MandelDim.IsParabolicGerm f₀ D₀ := hsetup.1
  have hbas : MandelDim.IsImmediateBasin f₀ D₀ B := hsetup.2.1
  have hBsub : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := hbas.2.2.1
  have h0B : (0 : ℂ) ∉ B := fun h0 =>
    Work.Parab.basinEnters.zero_not_mem_parabolicBasin hgerm (hBsub h0)
  have hφB : ∀ w : ℂ, d.φ w ∈ B := fun w => (h trivial).2
  obtain ⟨hφdiff, hEdiff, hEeq⟩ := differentiable_E_of_univ_subset d h hBsub
  have hgdiff : Differentiable ℂ (fun w : ℂ => d.Φ (d.φ w) - w) := hEdiff.sub differentiable_id
  have hper : ∀ w : ℂ, (fun w : ℂ => d.Φ (d.φ w) - w) (w + 1)
      = (fun w : ℂ => d.Φ (d.φ w) - w) w := by
    intro w
    simp only
    rw [hEeq w]
    ring
  obtain ⟨cl, hcl⟩ := d.E_lower
  obtain ⟨c₀, hc₀⟩ := periodic_entire_const_aux (fun w : ℂ => d.Φ (d.φ w) - w)
    hgdiff hper d.E_upper hcl
  have hφinj : Function.Injective d.φ := by
    intro w w' hww
    have h4 : d.Φ (d.φ w) - w = d.Φ (d.φ w') - w' := by rw [hc₀ w, hc₀ w']
    rw [hww] at h4
    exact sub_right_inj.mp h4
  obtain ⟨a, b, ha, hab⟩ := Work.FatouCH.injEntire_affine_growth hφdiff hφinj
  have hz : d.φ (-(b / a)) = 0 := by
    rw [hab]
    field_simp
    ring
  exact h0B (by rw [← hz]; exact hφB _)

end

end Work.HornSC
