import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.argChangeLift
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy

/-!
# The local side determination at a free straight chord

If a closed plane curve contains a straight segment as a piece of its trace, then the winding
numbers of the curve about points on the two sides of that segment differ.  This is the elementary
"local jump" across a straight piece of the curve, and it is the tool that turns a *free straight
chord* (a chord of the curve whose open interior misses the trace) into an index computation.

The key computation is `loopIndex_ne_zero_of_crossOnce`: a nowhere vanishing closed loop which
crosses the closed negative real axis exactly once, and transversally, has non-zero index.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## Elementary sine facts -/

/-- In a fundamental interval `(2πk, 2πk + 2π)`, a negative value of `sin` lies in the second
half. -/
theorem sin_neg_imp_gt {k : ℤ} {x : ℝ} (h1 : (k : ℝ) * (2 * Real.pi) < x)
    (h2 : x < (k : ℝ) * (2 * Real.pi) + 2 * Real.pi) (h3 : Real.sin x < 0) :
    (k : ℝ) * (2 * Real.pi) + Real.pi < x := by
  by_contra hcon
  push_neg at hcon
  set y : ℝ := x - (k : ℝ) * (2 * Real.pi) with hy
  have hy0 : 0 < y := by rw [hy]; linarith
  have hypi : y ≤ Real.pi := by rw [hy]; linarith
  have hsin : Real.sin x = Real.sin y := by
    have h := Real.sin_add_int_mul_two_pi y k
    rw [show y + (k : ℝ) * (2 * Real.pi) = x by rw [hy]; ring] at h
    exact h
  have hnn : 0 ≤ Real.sin y := Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hy0, hypi⟩
  rw [← hsin] at hnn
  linarith

/-- In a fundamental interval `(2πk, 2πk + 2π)`, a positive value of `sin` lies in the first
half. -/
theorem sin_pos_imp_lt {k : ℤ} {x : ℝ} (h1 : (k : ℝ) * (2 * Real.pi) < x)
    (h2 : x < (k : ℝ) * (2 * Real.pi) + 2 * Real.pi) (h3 : 0 < Real.sin x) :
    x < (k : ℝ) * (2 * Real.pi) + Real.pi := by
  by_contra hcon
  push_neg at hcon
  set y : ℝ := x - ((k : ℝ) * (2 * Real.pi) + Real.pi) with hy
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have hypi : y < Real.pi := by rw [hy]; linarith
  have hsin : Real.sin x = - Real.sin y := by
    have h := Real.sin_add_int_mul_two_pi (y + Real.pi) k
    rw [show (y + Real.pi) + (k : ℝ) * (2 * Real.pi) = x by rw [hy]; ring] at h
    rw [h, Real.sin_add_pi]
  have hnn : 0 ≤ Real.sin y := Real.sin_nonneg_of_mem_Icc ⟨hy0, le_of_lt hypi⟩
  rw [hsin] at h3
  linarith

/-- **A loop crossing the closed negative real axis exactly once, transversally, has non-zero
index.**

`c` is a closed nowhere vanishing loop; the parameters at which `c` meets the closed negative real
axis `(-∞, 0]` are exactly `{t₀}`, and the crossing is transversal in the sense that near `t₀` the
imaginary part of `c` is negative below `t₀` and positive above it.  Then `loopIndex c ≠ 0`.

The proof lifts the loop, `c = exp ∘ Λ`, and looks at `θ = Im ∘ Λ`: the negative real axis
corresponds to the level set `θ ∈ π + 2πℤ`, which is met exactly at `t₀`; the sign condition forces
`θ` to move from above that level to below it across `t₀`, so `θ` does not return to its initial
value and the increment `Λ 1 - Λ 0` is non-zero. -/
theorem loopIndex_ne_zero_of_crossOnce {c : C(unitInterval, ℂ)} (hc : ∀ t, c t ≠ 0)
    (hloop : c 0 = c 1) {t₀ : unitInterval} (ht₀ : (t₀ : ℝ) ∈ Set.Ioo 0 1)
    (ht₀mem : (c t₀).im = 0) (ht₀neg : (c t₀).re < 0)
    (hreal : ∀ t : unitInterval, (c t).im = 0 → (c t).re ≤ 0 → t = t₀)
    (hsign : ∃ δ : ℝ, 0 < δ ∧ ∀ s : unitInterval,
      |(s : ℝ) - (t₀ : ℝ)| < δ → (s : ℝ) ≠ (t₀ : ℝ) →
      (((s : ℝ) < (t₀ : ℝ)) ↔ (c s).im < 0) ∧
      (((t₀ : ℝ) < (s : ℝ)) ↔ 0 < (c s).im)) :
    loopIndex c ≠ 0 := by
  obtain ⟨Λ, hΛ, -, -⟩ := argChangeLift c hc
  set θ : unitInterval → ℝ := fun t => (Λ t).im with hθdef
  have hθcont : Continuous θ := hθdef ▸ Complex.continuous_im.comp Λ.continuous
  have hcim : ∀ t, (c t).im = Real.exp ((Λ t).re) * Real.sin (θ t) := fun t => by
    rw [hθdef, ← hΛ t, Complex.exp_im]
  have hcre : ∀ t, (c t).re = Real.exp ((Λ t).re) * Real.cos (θ t) := fun t => by
    rw [hθdef, ← hΛ t, Complex.exp_re]
  have hexppos : ∀ t, 0 < Real.exp ((Λ t).re) := fun t => Real.exp_pos _
  -- ### the level set of `θ` over the grid `π + 2πℤ`
  have hlev : ∀ t : unitInterval, (∃ k : ℤ, θ t = Real.pi + (k : ℝ) * (2 * Real.pi)) ↔ t = t₀ := by
    intro t
    constructor
    · rintro ⟨k, hk⟩
      refine hreal t ?_ ?_
      · rw [hcim t, hk, Real.sin_add_int_mul_two_pi, Real.sin_pi, mul_zero]
      · rw [hcre t, hk, Real.cos_add_int_mul_two_pi, Real.cos_pi]
        have := hexppos t
        linarith
    · intro ht
      rw [ht]
      have hsin0 : Real.sin (θ t₀) = 0 := by
        have h := ht₀mem
        rw [hcim t₀] at h
        exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (hexppos t₀))
      obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin0
      have hn' : θ t₀ = (n : ℝ) * Real.pi := hn.symm
      have hcosneg : Real.cos ((n : ℝ) * Real.pi) < 0 := by
        have h := ht₀neg
        rw [hcre t₀, hn'] at h
        nlinarith [hexppos t₀]
      have hodd : ∃ k : ℤ, n = 2 * k + 1 := by
        by_contra hcon
        have hev : Even n := by
          rcases Int.even_or_odd n with he | ho
          · exact he
          · exact absurd ho hcon
        obtain ⟨j, hj⟩ := hev
        have h1 : Real.cos ((n : ℝ) * Real.pi) = 1 := by
          rw [hj]
          have h2 : (((j + j : ℤ)) : ℝ) * Real.pi = (j : ℝ) * (2 * Real.pi) := by
            push_cast; ring
          rw [h2, Real.cos_int_mul_two_pi]
        rw [h1] at hcosneg
        norm_num at hcosneg
      obtain ⟨k, hk⟩ := hodd
      refine ⟨k, ?_⟩
      rw [hn', hk]
      push_cast
      ring
  -- θ t₀ is a grid point
  obtain ⟨k₀, hk₀⟩ : ∃ k : ℤ, θ t₀ = Real.pi + (k : ℝ) * (2 * Real.pi) := (hlev t₀).mpr rfl
  have htk : θ t₀ = ((1 + 2 * k₀ : ℤ) : ℝ) * Real.pi := by
    rw [hk₀]; push_cast; ring
  -- ### two points, just below and just above `t₀`
  obtain ⟨δ, hδpos, hδ⟩ := hsign
  have ht₀pos : (0 : ℝ) < (t₀ : ℝ) := ht₀.1
  have ht₀lt1 : (t₀ : ℝ) < 1 := ht₀.2
  have hcont_at : ∀ ε > 0, ∃ η > 0, ∀ s : unitInterval,
      |(s : ℝ) - (t₀ : ℝ)| < η → |θ s - θ t₀| < ε := by
    intro ε hε
    have h : ContinuousAt θ t₀ := hθcont.continuousAt
    rw [Metric.continuousAt_iff] at h
    obtain ⟨η, hη, hη'⟩ := h ε hε
    refine ⟨η, hη, fun s hs => ?_⟩
    have h2 : dist s t₀ < η := by rw [Subtype.dist_eq]; exact hs
    have := hη' h2
    rwa [Real.dist_eq] at this
  obtain ⟨η, hηpos, hη⟩ := hcont_at Real.pi Real.pi_pos
  set δ' : ℝ := min δ (min η (min (t₀ : ℝ) (1 - (t₀ : ℝ)))) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδpos (lt_min hηpos (lt_min ht₀pos (by linarith)))
  have hδ'le_δ : δ' ≤ δ := le_trans (min_le_left _ _) le_rfl
  have hδ'le_η : δ' ≤ η := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ'le_t₀ : δ' ≤ (t₀ : ℝ) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ'le_1mt : δ' ≤ 1 - (t₀ : ℝ) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the point just below `t₀`
  have hsmmem : (t₀ : ℝ) - δ' / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  set sm : unitInterval := ⟨(t₀ : ℝ) - δ' / 2, hsmmem⟩ with hsmdef
  have hsmlt : (sm : ℝ) < (t₀ : ℝ) := by rw [hsmdef]; linarith
  have hsmne : (sm : ℝ) ≠ (t₀ : ℝ) := ne_of_lt hsmlt
  have hsmabs : |(sm : ℝ) - (t₀ : ℝ)| = δ' / 2 := by
    rw [hsmdef, show (t₀ : ℝ) - δ' / 2 - (t₀ : ℝ) = -(δ' / 2) by ring,
      abs_of_neg (by linarith)]
    ring
  have hsmclose : |(sm : ℝ) - (t₀ : ℝ)| < δ := by
    rw [hsmabs]; nlinarith [hδ'le_δ, hδpos]
  have hsmcloseη : |(sm : ℝ) - (t₀ : ℝ)| < η := by
    rw [hsmabs]; nlinarith [hδ'le_η, hηpos]
  have himm : (c sm).im < 0 := ((hδ sm hsmclose hsmne).1).mp hsmlt
  have hsinm : Real.sin (θ sm) < 0 := by
    have h := himm
    rw [hcim sm] at h
    nlinarith [hexppos sm]
  have hnearm : |θ sm - θ t₀| < Real.pi := hη sm hsmcloseη
  have hgtm : θ t₀ < θ sm := by
    have h1 : (k₀ : ℝ) * (2 * Real.pi) < θ sm := by
      have := (abs_lt.mp hnearm).1; rw [hk₀] at this; linarith
    have h2 : θ sm < (k₀ : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
      have := (abs_lt.mp hnearm).2; rw [hk₀] at this; linarith
    have := sin_neg_imp_gt h1 h2 hsinm
    rw [hk₀]; linarith
  -- the point just above `t₀`
  have hspmem : (t₀ : ℝ) + δ' / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  set sp : unitInterval := ⟨(t₀ : ℝ) + δ' / 2, hspmem⟩ with hspdef
  have hspgt : (t₀ : ℝ) < (sp : ℝ) := by rw [hspdef]; linarith
  have hspne : (sp : ℝ) ≠ (t₀ : ℝ) := ne_of_gt hspgt
  have hspabs : |(sp : ℝ) - (t₀ : ℝ)| = δ' / 2 := by
    rw [hspdef, show (t₀ : ℝ) + δ' / 2 - (t₀ : ℝ) = δ' / 2 by ring,
      abs_of_pos (by linarith)]
  have hspclose : |(sp : ℝ) - (t₀ : ℝ)| < δ := by
    rw [hspabs]; nlinarith [hδ'le_δ, hδpos]
  have hspcloseη : |(sp : ℝ) - (t₀ : ℝ)| < η := by
    rw [hspabs]; nlinarith [hδ'le_η, hηpos]
  have himp : 0 < (c sp).im := ((hδ sp hspclose hspne).2).mp hspgt
  have hsinp : 0 < Real.sin (θ sp) := by
    have h := himp
    rw [hcim sp] at h
    nlinarith [hexppos sp]
  have hnearp : |θ sp - θ t₀| < Real.pi := hη sp hspcloseη
  have hltp : θ sp < θ t₀ := by
    have h1 : (k₀ : ℝ) * (2 * Real.pi) < θ sp := by
      have := (abs_lt.mp hnearp).1; rw [hk₀] at this; linarith
    have h2 : θ sp < (k₀ : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
      have := (abs_lt.mp hnearp).2; rw [hk₀] at this; linarith
    have := sin_pos_imp_lt h1 h2 hsinp
    rw [hk₀]; linarith
  -- ### the sign is constant on each side
  have hne_of_ne : ∀ t : unitInterval, t ≠ t₀ → θ t ≠ θ t₀ := by
    intro t ht hcon
    exact ht ((hlev t).mp ⟨k₀, by rw [hcon, hk₀]⟩)
  have hmono : ∀ t : unitInterval, (t : ℝ) < (t₀ : ℝ) → θ t₀ < θ t := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    have hne : t ≠ t₀ := fun h => by rw [h] at ht; exact absurd ht (not_lt.mpr le_rfl)
    have hlt2 : θ t < θ t₀ := lt_of_le_of_ne hcon (hne_of_ne t hne)
    have hord : (θ '' Set.Icc (min t sm) (max t sm)).OrdConnected :=
      isPreconnected_iff_ordConnected.mp ((isPreconnected_Icc).image θ hθcont.continuousOn)
    have ht_mem : θ t ∈ θ '' Set.Icc (min t sm) (max t sm) :=
      ⟨t, ⟨min_le_left t sm, le_max_left t sm⟩, rfl⟩
    have hsm_mem : θ sm ∈ θ '' Set.Icc (min t sm) (max t sm) :=
      ⟨sm, ⟨min_le_right t sm, le_max_right t sm⟩, rfl⟩
    obtain ⟨u, hu, huθ⟩ := hord.out ht_mem hsm_mem ⟨le_of_lt hlt2, le_of_lt hgtm⟩
    have hut : u = t₀ := (hlev u).mp ⟨k₀, huθ ▸ hk₀⟩
    have hmaxlt : (max t sm : ℝ) < (t₀ : ℝ) := max_lt ht hsmlt
    have hle : (t₀ : ℝ) ≤ (max t sm : ℝ) := by rw [← hut]; exact hu.2
    linarith
  have hanti : ∀ t : unitInterval, (t₀ : ℝ) < (t : ℝ) → θ t < θ t₀ := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    have hne : t ≠ t₀ := fun h => by rw [h] at ht; exact absurd ht (not_lt.mpr le_rfl)
    have hgt2 : θ t₀ < θ t := lt_of_le_of_ne hcon (Ne.symm (hne_of_ne t hne))
    have hord : (θ '' Set.Icc (min t sp) (max t sp)).OrdConnected :=
      isPreconnected_iff_ordConnected.mp ((isPreconnected_Icc).image θ hθcont.continuousOn)
    have ht_mem : θ t ∈ θ '' Set.Icc (min t sp) (max t sp) :=
      ⟨t, ⟨min_le_left t sp, le_max_left t sp⟩, rfl⟩
    have hsp_mem : θ sp ∈ θ '' Set.Icc (min t sp) (max t sp) :=
      ⟨sp, ⟨min_le_right t sp, le_max_right t sp⟩, rfl⟩
    obtain ⟨u, hu, huθ⟩ := hord.out hsp_mem ht_mem ⟨le_of_lt hltp, le_of_lt hgt2⟩
    have hut : u = t₀ := (hlev u).mp ⟨k₀, huθ ▸ hk₀⟩
    have hltmin : (t₀ : ℝ) < (min t sp : ℝ) := lt_min ht hspgt
    have hle : (min t sp : ℝ) ≤ (t₀ : ℝ) := by
      exact_mod_cast (show (min t sp : unitInterval) ≤ t₀ from hu.1.trans_eq hut)
    linarith
  -- ### conclusion
  have h01 : θ (0 : unitInterval) ≠ θ (1 : unitInterval) := by
    have h0 : θ t₀ < θ (0 : unitInterval) := hmono 0 (by simpa using ht₀pos)
    have h1 : θ (1 : unitInterval) < θ t₀ := hanti 1 (by simpa using ht₀lt1)
    linarith
  have hincr : Λ 1 - Λ 0 ≠ 0 := by
    intro h
    apply h01
    have him : (Λ 1).im = (Λ 0).im := by
      have h2 := congrArg Complex.im h
      rw [Complex.sub_im] at h2
      simp only [Complex.zero_im, sub_eq_zero] at h2
      exact h2
    simpa [hθdef] using him.symm
  intro hk
  have hspec := loopIndex_spec c hc hloop Λ hΛ
  rw [hk] at hspec
  simp only [Int.cast_zero, zero_mul] at hspec
  exact hincr hspec

/-! ## Shift invariance of the winding number -/

/-- **Shifting the parameter of a periodic curve does not change the winding number** (the
explicit homotopy `(t,s) ↦ γ (2π t + s θ) - z`). -/
theorem loopIndex_shiftCurve {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (θ : ℝ) {z : ℂ} (hz : ∀ t : ℝ, γ t ≠ z) :
    loopIndex (curveLoop (fun t => γ (t + θ) - z)
        ((hγ.comp (continuous_id.add continuous_const)).sub continuous_const))
      = windNumber γ hγ z := by
  have hγθ : Continuous fun t : ℝ => γ (t + θ) := hγ.comp (continuous_id.add continuous_const)
  set c₀ : C(unitInterval, ℂ) := curveLoop (fun t => γ t - z) (hγ.sub continuous_const) with hc₀
  set c₁ : C(unitInterval, ℂ) := curveLoop (fun t => γ (t + θ) - z) (hγθ.sub continuous_const)
    with hc₁
  have hc₀app : ∀ t : unitInterval, c₀ t = γ (2 * Real.pi * (t : ℝ)) - z := fun t => rfl
  have hc₁app : ∀ t : unitInterval, c₁ t = γ (2 * Real.pi * (t : ℝ) + θ) - z := fun t => rfl
  have hne₀ : ∀ t : unitInterval, c₀ t ≠ 0 := by
    intro t; rw [hc₀app]; exact sub_ne_zero.mpr (hz _)
  have hne₁ : ∀ t : unitInterval, c₁ t ≠ 0 := by
    intro t; rw [hc₁app]; exact sub_ne_zero.mpr (hz _)
  set H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => γ (2 * Real.pi * (p.1 : ℝ) + (p.2 : ℝ) * θ) - z, by fun_prop⟩ with hH
  have hHapp : ∀ p : unitInterval × unitInterval,
      H p = γ (2 * Real.pi * (p.1 : ℝ) + (p.2 : ℝ) * θ) - z := fun p => rfl
  have hHne : ∀ p : unitInterval × unitInterval, H p ≠ 0 := by
    intro p; rw [hHapp]; exact sub_ne_zero.mpr (hz _)
  have hH0 : ∀ t : unitInterval, H (t, 0) = c₀ t := by
    intro t; rw [hHapp, hc₀app]; norm_num
  have hH1 : ∀ t : unitInterval, H (t, 1) = c₁ t := by
    intro t; rw [hHapp, hc₁app]; norm_num
  have hHloop : ∀ s : unitInterval, H (0, s) = H (1, s) := by
    intro s
    rw [hHapp, hHapp]
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by norm_num
    have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by norm_num
    rw [h0, h1, zero_add]
    congr 1
    rw [add_comm (2 * Real.pi) ((s : ℝ) * θ)]
    exact (hper ((s : ℝ) * θ)).symm
  have hmain := loopIndex_eq_of_homotopy hne₀ hne₁ H hHne hH0 hH1 hHloop
  rw [show windNumber γ hγ z = loopIndex c₀ from rfl]
  exact hmain.symm


end

end Work.Smooth.SphereJordan
