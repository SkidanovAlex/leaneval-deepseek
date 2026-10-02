import Mathlib
import Submission.Work.GATE.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.GATE.Segment

open LeanEval.ComplexAnalysis (Mandelbar)

/-- **Crossing of the two leak lattices.**  A continuous real function `f` on `[a, b]` which
starts at `A₀ = f a` and drops below `A₀ - 2` somewhere crosses both the lattice `x + ℤ` and the
shifted lattice `x + 1/2 + ℤ`: there are `μ₁ μ₂ ∈ [a, b]` and `k l : ℤ` with `f μ₁ = x + k` and
`f μ₂ = x + 1/2 + l`. -/
theorem crossing_lattice {f : ℝ → ℝ} {a b A₀ x : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hfa : f a = A₀) (hfb : f b < A₀ - 2) :
    ∃ μ₁ ∈ Set.Icc a b, ∃ μ₂ ∈ Set.Icc a b, ∃ k l : ℤ,
      f μ₁ = x + (k : ℝ) ∧ f μ₂ = x + 1 / 2 + (l : ℝ) := by
  have hab' : a ≤ b := le_of_lt hab
  -- the two levels, in the image interval `[f b, f a]` of length `> 2`
  have hv₁ : x + ((⌊A₀ - x⌋ : ℤ) : ℝ) ∈ Set.Icc (f b) (f a) := by
    constructor
    · have h1 : A₀ - x - 1 < ((⌊A₀ - x⌋ : ℤ) : ℝ) := by
        have := Int.lt_floor_add_one (A₀ - x); linarith
      linarith
    · rw [hfa]; have := Int.floor_le (A₀ - x); linarith
  have hv₂ : x + 1 / 2 + ((⌊A₀ - x - 1 / 2⌋ : ℤ) : ℝ) ∈ Set.Icc (f b) (f a) := by
    constructor
    · have h1 : A₀ - x - 1 / 2 - 1 < ((⌊A₀ - x - 1 / 2⌋ : ℤ) : ℝ) := by
        have := Int.lt_floor_add_one (A₀ - x - 1 / 2); linarith
      linarith
    · rw [hfa]; have := Int.floor_le (A₀ - x - 1 / 2); linarith
  obtain ⟨μ₁, hμ₁, hfμ₁⟩ := intermediate_value_Icc' hab' hf hv₁
  obtain ⟨μ₂, hμ₂, hfμ₂⟩ := intermediate_value_Icc' hab' hf hv₂
  exact ⟨μ₁, hμ₁, μ₂, hμ₂, ⌊A₀ - x⌋, ⌊A₀ - x - 1 / 2⌋, hfμ₁, hfμ₂⟩

/-- **The transit coordinate drops below `A₀ - 2` near a frontier point.**  If the phase of the
transit coordinate blows up (`Re trans → -∞`) at `p` inside `Nm`, and the straight path to `p`
stays in `Nm` up to `p`, then there is `μ₀ ∈ (0, 1)` at which the real part of the transit
coordinate along the path is `< A₀ - 2`. -/
theorem exists_mu_re_lt {y p : ℂ} {trans : ℂ → ℂ} {Nm : Set ℂ} {A₀ : ℝ}
    (hblow : Tendsto (fun c => (trans c).re) (𝓝[Nm] p) atBot)
    (hseg : ∀ μ ∈ Set.Ico (0 : ℝ) 1, y + ((μ : ℝ) : ℂ) * (p - y) ∈ Nm) :
    ∃ μ₀ ∈ Set.Ioo (0 : ℝ) 1, (trans (y + ((μ₀ : ℝ) : ℂ) * (p - y))).re < A₀ - 2 := by
  rw [tendsto_atBot] at hblow
  have hb : ∀ᶠ c in 𝓝[Nm] p, (trans c).re ≤ A₀ - 3 := hblow (A₀ - 3)
  rw [eventually_nhdsWithin_iff] at hb
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hb
  have hcont : Continuous (fun μ : ℝ => y + ((μ : ℝ) : ℂ) * (p - y)) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hp1 : y + (((1 : ℝ) : ℂ)) * (p - y) = p := by simp
  obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.mp hcont.continuousAt δ hδpos
  set t : ℝ := min η (1 / 2) with htdef
  have htpos : 0 < t := by rw [htdef]; exact lt_min hηpos (by norm_num)
  have htle : t ≤ 1 / 2 := by rw [htdef]; exact min_le_right _ _
  have htle' : t ≤ η := by rw [htdef]; exact min_le_left _ _
  refine ⟨1 - t / 2, ⟨by linarith, by linarith⟩, ?_⟩
  have hd : dist (1 - t / 2) (1 : ℝ) < η := by
    rw [Real.dist_eq]
    have hsplit : 1 - t / 2 - 1 = -(t / 2) := by ring
    rw [hsplit, abs_neg, abs_of_nonneg (by linarith)]
    linarith
  have hdist := hη hd
  rw [hp1] at hdist
  have hmem : y + (((1 - t / 2 : ℝ)) : ℂ) * (p - y) ∈ Nm :=
    hseg _ ⟨by linarith, by linarith⟩
  have hball : y + (((1 - t / 2 : ℝ)) : ℂ) * (p - y) ∈ Metric.ball p δ := hdist
  have hbound : (trans (y + (((1 - t / 2 : ℝ)) : ℂ) * (p - y))).re ≤ A₀ - 3 :=
    (hδ hball) hmem
  linarith

/-- **Crossing of the two tongues.**  A straight segment in the implosion side `Nm`, running from
an interior point `y` to a frontier point `p`, sweeps the transit coordinate by more than two
turns at height `≈ 0`; hence it carries a parameter of the `b`-tongue and a parameter of the
`ι b`-tongue, both of which are escaping (outside the Mandelbar set). -/
theorem crossing_two_tongues {c₀ : ℂ} {Nm : Set ℂ} (TD : Work.GATE.TransitData c₀ Nm) {y p : ℂ}
    (hy : y ∈ Nm ∩ Metric.ball c₀ TD.ρ) (hp : p ∈ frontier Nm ∩ Metric.ball c₀ TD.ρ)
    (hseg : ∀ μ ∈ Set.Ico (0 : ℝ) 1,
      y + ((μ : ℝ) : ℂ) * (p - y) ∈ Nm ∩ Metric.ball c₀ TD.ρ) :
    ∃ e₁ e₂ : ℂ, e₁ ∈ segment ℝ y p ∧ e₂ ∈ segment ℝ y p ∧
      Work.GATE.bTongue TD.trans TD.xLeak TD.r₀ e₁ ∧
      Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀ e₂ ∧
      e₁ ∉ LeanEval.ComplexAnalysis.Mandelbar ∧ e₂ ∉ LeanEval.ComplexAnalysis.Mandelbar := by
  have hsegN : ∀ μ ∈ Set.Ico (0 : ℝ) 1, y + ((μ : ℝ) : ℂ) * (p - y) ∈ Nm :=
    fun μ hμ => (hseg μ hμ).1
  -- the transit coordinate drops by more than `2` near `p`
  obtain ⟨μ₀, hμ₀, hμ₀'⟩ := exists_mu_re_lt (trans := TD.trans) (A₀ := (TD.trans y).re)
    (TD.blowup p hp) hsegN
  -- continuity of the transit coordinate along the path on `[0, μ₀]`
  have hmaps : MapsTo (fun μ : ℝ => y + ((μ : ℝ) : ℂ) * (p - y)) (Set.Icc (0 : ℝ) μ₀)
      (Nm ∩ Metric.ball c₀ TD.ρ) :=
    fun μ hμ => hseg μ ⟨hμ.1, lt_of_le_of_lt hμ.2 hμ₀.2⟩
  have hcontφ : ContinuousOn (fun μ : ℝ => y + ((μ : ℝ) : ℂ) * (p - y))
      (Set.Icc (0 : ℝ) μ₀) :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
  have hcomp : ContinuousOn (TD.trans ∘ fun μ : ℝ => y + ((μ : ℝ) : ℂ) * (p - y))
      (Set.Icc (0 : ℝ) μ₀) := TD.cont.comp hcontφ hmaps
  have hf : ContinuousOn (fun μ : ℝ => (TD.trans (y + ((μ : ℝ) : ℂ) * (p - y))).re)
      (Set.Icc (0 : ℝ) μ₀) :=
    Complex.continuous_re.comp_continuousOn hcomp
  have hfa : (fun μ : ℝ => (TD.trans (y + ((μ : ℝ) : ℂ) * (p - y))).re) 0 =
      (TD.trans y).re := by simp
  -- the two lattice hits on `[0, μ₀]`
  obtain ⟨μ₁, hμ₁, μ₂, hμ₂, k, l, hk, hl⟩ :=
    crossing_lattice (a := 0) (A₀ := (TD.trans y).re) (x := TD.xLeak) hμ₀.1 hf hfa hμ₀'
  -- the witnesses and their membership in `Nm ∩ ball`
  have hm₁ : y + ((μ₁ : ℝ) : ℂ) * (p - y) ∈ Nm ∩ Metric.ball c₀ TD.ρ :=
    hseg μ₁ ⟨hμ₁.1, lt_of_le_of_lt hμ₁.2 hμ₀.2⟩
  have hm₂ : y + ((μ₂ : ℝ) : ℂ) * (p - y) ∈ Nm ∩ Metric.ball c₀ TD.ρ :=
    hseg μ₂ ⟨hμ₂.1, lt_of_le_of_lt hμ₂.2 hμ₀.2⟩
  -- the height bound makes the two hits lands in the tongues
  have him₁ : |(TD.trans (y + ((μ₁ : ℝ) : ℂ) * (p - y))).im| < TD.r₀ / 2 :=
    lt_of_le_of_lt (TD.height _ hm₁) (by linarith [TD.hr₀])
  have him₂ : |(TD.trans (y + ((μ₂ : ℝ) : ℂ) * (p - y))).im| < TD.r₀ / 2 :=
    lt_of_le_of_lt (TD.height _ hm₂) (by linarith [TD.hr₀])
  have hb₁ : Work.GATE.bTongue TD.trans TD.xLeak TD.r₀
      (y + ((μ₁ : ℝ) : ℂ) * (p - y)) :=
    Work.GATE.bTongue_of_re_eq hk him₁
  have hi₂ : Work.GATE.iotaTongue TD.trans TD.xLeak TD.r₀
      (y + ((μ₂ : ℝ) : ℂ) * (p - y)) :=
    Work.GATE.iotaTongue_of_re_eq hl him₂
  refine ⟨y + ((μ₁ : ℝ) : ℂ) * (p - y), y + ((μ₂ : ℝ) : ℂ) * (p - y),
    ?_, ?_, hb₁, hi₂, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨μ₁, ⟨hμ₁.1, le_of_lt (lt_of_le_of_lt hμ₁.2 hμ₀.2)⟩, by simp⟩
  · rw [segment_eq_image']
    exact ⟨μ₂, ⟨hμ₂.1, le_of_lt (lt_of_le_of_lt hμ₂.2 hμ₀.2)⟩, by simp⟩
  · exact TD.escape_b _ hm₁ hb₁
  · exact TD.escape_iota _ hm₂ hi₂

end Work.GATE.Segment
