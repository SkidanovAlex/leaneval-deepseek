import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B1.exp_I_eq_one_const
import Submission.Work.RPB.B5.exp_chordPhase_zero_sub

open scoped ContDiff Topology

set_option linter.style.haveILetI false

namespace Work.RPB.B5

/-- If `|k * 2π| < π` for an integer `k`, then `k = 0`. -/
private lemma int_cast_mul_two_pi_eq_zero {k : ℤ}
    (h : |(k : ℝ) * (2 * Real.pi)| < Real.pi) : k = 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hk1 : (k : ℝ) ≤ -1 := by
      have : k ≤ -1 := by omega
      exact_mod_cast this
    have hle : (k : ℝ) * (2 * Real.pi) ≤ -2 * Real.pi := by nlinarith
    have hlt := (abs_lt.mp h).1
    nlinarith
  · exact hk
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have : (1 : ℤ) ≤ k := by omega
      exact_mod_cast this
    have hle : 2 * Real.pi ≤ (k : ℝ) * (2 * Real.pi) := by nlinarith
    have hlt := (abs_lt.mp h).2
    nlinarith

/-- A continuous real function on a preconnected space with `exp (f x * I) = 1` everywhere
is constant.  Every value of `f` is an integer multiple of `2π`, so `f` is locally constant:
near any point the difference of two values is an integer multiple of `2π` of absolute value
`< π`, hence `0`. -/
private theorem continuous_exp_I_eq_one_const {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {f : X → ℝ} (hf : Continuous f)
    (h : ∀ x, Complex.exp ((f x : ℝ) * Complex.I) = 1) : ∀ x y, f x = f y := by
  have hmem : ∀ x, ∃ n : ℤ, f x = (n : ℝ) * (2 * Real.pi) := by
    intro x
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (h x)
    refine ⟨n, ?_⟩
    have h2 : (f x : ℂ) * Complex.I = ((n : ℂ) * (2 * Real.pi)) * Complex.I := by
      rw [hn]; ring
    have h3 : (f x : ℂ) = (n : ℂ) * (2 * Real.pi) :=
      mul_right_cancel₀ Complex.I_ne_zero h2
    have h4 : (f x : ℂ) = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
      rw [h3]; push_cast; ring
    exact Complex.ofReal_injective h4
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨n, hn⟩ := hmem x
    have hnb : {y : X | dist (f y) (f x) < Real.pi} ∈ 𝓝 x :=
      hf.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (f x) Real.pi_pos)
    filter_upwards [hnb] with y hy
    obtain ⟨m, hm⟩ := hmem y
    have hdist : |f y - f x| < Real.pi := by
      rw [Real.dist_eq] at hy; exact hy
    have hkey : |((m - n : ℤ) : ℝ) * (2 * Real.pi)| < Real.pi := by
      have hdiff : f y - f x = ((m - n : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [hm, hn]; push_cast; ring
      rwa [hdiff] at hdist
    have hzero : m - n = 0 := int_cast_mul_two_pi_eq_zero hkey
    have hmn : m = n := by omega
    rw [hm, hn, hmn]
  intro x y
  exact hloc.apply_eq_of_preconnectedSpace x y

/-- At time `τ = 0` the curve is the unit circle, so the chord `(c 0 (t+r), c 0 (t-r))` has
direction `t + π/2` for every `r`; hence `a 0 t r - (t + π/2)` is a *single* integer multiple of
`2π`, independent of `t` and of `r ∈ [0, π]`.

The offset `δ t r = a 0 t r - (t + π/2)` is continuous on the strip `ℝ × [0, π]`, and
`exp (δ t r * I) = 1` there: on the two open intervals `0 < r < π/2` and `π/2 < r < π` this is
`exp_chordPhase_zero_sub` (for `r > π/2` combined with the chord-swap monodromy, which relates
`(t, r)` to `(t + π, π - r)`), and at the endpoints and at `r = π/2` it follows by continuity
(closedness of the zero set plus density of the two open intervals in the strip).  The strip is
preconnected, so `δ` is constant there; its value at `(0,0)` is an integer multiple of `2π`,
which is the required `k`. -/
theorem chordPhase_zero_eq (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) :
    ∃ k : ℤ, ∀ t : ℝ, ∀ r ∈ Set.Icc (0:ℝ) Real.pi,
      a 0 t r = t + Real.pi/2 + 2*Real.pi*k := by
  -- continuity of the phase at `τ = 0` on the strip
  have hcont_a : ContinuousOn (fun x : ℝ × ℝ => a 0 x.1 x.2)
      (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi) := by
    have hmaps : Set.MapsTo (fun x : ℝ × ℝ => ((0:ℝ), x.1, x.2))
        (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi)
        (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi) := by
      rintro ⟨t, r⟩ ⟨-, hr⟩
      exact ⟨⟨le_refl 0, by norm_num⟩, trivial, hr⟩
    have hg : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => ((0:ℝ), x.1, x.2))
        (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi) := ContDiff.contDiffOn (by fun_prop)
    exact (ha.1.comp hg hmaps).continuousOn
  -- the phase offset
  let δ : ℝ × ℝ → ℝ := fun x => a 0 x.1 x.2 - (x.1 + Real.pi/2)
  have hδ_cont : ContinuousOn δ (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi) := by
    change ContinuousOn (fun x : ℝ × ℝ => a 0 x.1 x.2 - (x.1 + Real.pi/2))
      (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi)
    exact hcont_a.sub ((continuous_fst.add continuous_const).continuousOn)
  -- `exp (δ * I) = 1` on the two open `r`-intervals
  have hD1 : ∀ t r, r ∈ Set.Ioo (0:ℝ) (Real.pi/2) →
      Complex.exp ((δ (t, r) : ℂ) * Complex.I) = 1 := by
    intro t r hr
    exact Work.RPB.B5.exp_chordPhase_zero_sub CI a ha hr
  have hD2 : ∀ t r, r ∈ Set.Ioo (Real.pi/2) Real.pi →
      Complex.exp ((δ (t, r) : ℂ) * Complex.I) = 1 := by
    intro t r hr
    have hr0 : r ∈ Set.Ioo (0:ℝ) Real.pi := ⟨by linarith [hr.1, Real.pi_pos], hr.2⟩
    have hswap := ha.2.2.2 0 (by norm_num) t r hr0
    have hr' : Real.pi - r ∈ Set.Ioo (0:ℝ) (Real.pi/2) :=
      ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have h := Work.RPB.B5.exp_chordPhase_zero_sub (CI := CI) (a := a) (ha := ha)
      (t := t + Real.pi) hr'
    have hEq : δ (t, r) = δ (t + Real.pi, Real.pi - r) := by
      change a 0 t r - (t + Real.pi/2)
        = a 0 (t + Real.pi) (Real.pi - r) - ((t + Real.pi) + Real.pi/2)
      rw [hswap]; ring
    rw [hEq]; exact h
  -- `exp (δ * I) = 1` on the whole strip, by density
  have hg_eq_one : ∀ x ∈ (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi),
      Complex.exp ((δ x : ℂ) * Complex.I) = 1 := by
    have hcont_g : ContinuousOn (fun x : ℝ × ℝ => Complex.exp ((δ x : ℂ) * Complex.I))
        (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi) := by
      have h1 : ContinuousOn (fun x : ℝ × ℝ => (δ x : ℂ))
          (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi) :=
        Complex.continuous_ofReal.comp_continuousOn hδ_cont
      exact (h1.mul continuousOn_const).cexp
    have hclosed : IsClosed ((Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi : Set (ℝ × ℝ)) ∩
        (fun x : ℝ × ℝ => Complex.exp ((δ x : ℂ) * Complex.I)) ⁻¹' {1}) :=
      hcont_g.preimage_isClosed_of_isClosed (isClosed_univ.prod isClosed_Icc) isClosed_singleton
    have hDsub : ((Set.univ ×ˢ Set.Ioo (0:ℝ) (Real.pi/2) : Set (ℝ × ℝ))
        ∪ (Set.univ ×ˢ Set.Ioo (Real.pi/2) Real.pi))
        ⊆ (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi : Set (ℝ × ℝ)) ∩
          (fun x : ℝ × ℝ => Complex.exp ((δ x : ℂ) * Complex.I)) ⁻¹' {1} := by
      rintro ⟨t, r⟩ (⟨-, hr⟩ | ⟨-, hr⟩)
      · exact ⟨⟨trivial, ⟨le_of_lt hr.1, by linarith [hr.2, Real.pi_pos]⟩⟩, hD1 t r hr⟩
      · exact ⟨⟨trivial, ⟨by linarith [hr.1, Real.pi_pos], le_of_lt hr.2⟩⟩, hD2 t r hr⟩
    have hcl : closure ((Set.univ ×ˢ Set.Ioo (0:ℝ) (Real.pi/2) : Set (ℝ × ℝ))
        ∪ (Set.univ ×ˢ Set.Ioo (Real.pi/2) Real.pi))
        = (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi : Set (ℝ × ℝ)) := by
      rw [closure_union, closure_prod_eq, closure_prod_eq, closure_univ,
        closure_Ioo (by linarith [Real.pi_pos] : (0:ℝ) ≠ Real.pi/2),
        closure_Ioo (by linarith [Real.pi_pos] : Real.pi/2 ≠ Real.pi),
        ← Set.prod_union,
        Set.Icc_union_Icc_eq_Icc (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
    have hsub : (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi : Set (ℝ × ℝ)) ⊆
        (fun x : ℝ × ℝ => Complex.exp ((δ x : ℂ) * Complex.I)) ⁻¹' {1} := by
      have := hclosed.closure_subset_iff.mpr hDsub
      rw [hcl] at this
      exact fun x hx => (this hx).2
    exact fun x hx => hsub hx
  -- `δ` is constant on the preconnected strip
  have hpre : IsPreconnected (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi : Set (ℝ × ℝ)) :=
    (isPreconnected_univ (α := ℝ)).prod isPreconnected_Icc
  haveI : PreconnectedSpace ↥(Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi : Set (ℝ × ℝ)) :=
    isPreconnected_iff_preconnectedSpace.mp hpre
  have hcont_S : Continuous (Set.domRestrict (Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi) δ) := by
    rw [← continuousOn_iff_continuous_domRestrict]
    exact hδ_cont
  have hconst := continuous_exp_I_eq_one_const hcont_S (fun x => hg_eq_one x.1 x.2)
  -- the value at the base point `(0, 0)` is an integer multiple of `2π`
  have hx0 : ((0:ℝ), (0:ℝ)) ∈ Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi :=
    ⟨trivial, ⟨le_refl 0, Real.pi_nonneg⟩⟩
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hg_eq_one (0, 0) hx0)
  have hδ0 : δ (0, 0) = (n : ℝ) * (2 * Real.pi) := by
    have h2 : (δ (0, 0) : ℂ) * Complex.I = ((n : ℂ) * (2 * Real.pi)) * Complex.I := by
      rw [hn]; ring
    have h3 : (δ (0, 0) : ℂ) = (n : ℂ) * (2 * Real.pi) :=
      mul_right_cancel₀ Complex.I_ne_zero h2
    have h4 : (δ (0, 0) : ℂ) = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
      rw [h3]; push_cast; ring
    exact Complex.ofReal_injective h4
  refine ⟨n, ?_⟩
  intro t r hr
  have hy : (t, r) ∈ Set.univ ×ˢ Set.Icc (0:ℝ) Real.pi := ⟨trivial, hr⟩
  have hEq : δ (t, r) = δ (0, 0) := hconst ⟨(t, r), hy⟩ ⟨(0, 0), hx0⟩
  have hda : a 0 t r = (t + Real.pi/2) + (n : ℝ) * (2 * Real.pi) := by
    have hd : δ (t, r) = (n : ℝ) * (2 * Real.pi) := by rw [hEq, hδ0]
    change a 0 t r - (t + Real.pi/2) = (n : ℝ) * (2 * Real.pi) at hd
    linarith
  rw [hda]; ring

end Work.RPB.B5
