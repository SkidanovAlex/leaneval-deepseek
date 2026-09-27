import Mathlib
import Submission.Work.EQ.SymDefs

/-!
# Structure of a normalised two-point equichordal curve

From the definition `NormEqCurve a ρ₁ ρ₂` alone we assemble the elementary structural facts
about a normalised equichordal curve used by the heteroclinic-connection route
(`Submission/Work/EQ/DESIGN.md`): injectivity of the polar parametrisation modulo `2π`, the
chord involution, `2π`-periodicity of the radial functions, the chord identities for the
one-step maps through `O₁`, `O₂`, the description of the real-axis points, and the behaviour of
Rychlik's map `eqT a` on the curve (it maps the curve to itself, is injective on it, and its
fixed points lie on the real axis).
-/

namespace Work.EQ

open Complex

/-- Norm of `1 - 1/↑r` for `0 < r < 1`. -/
lemma nec_norm_one_sub_inv {r : ℝ} (hr : 0 < r) (hrlt : r < 1) :
    ‖(1 - 1/((r:ℝ):ℂ) : ℂ)‖ = 1/r - 1 := by
  have hcast : (1 - 1/((r:ℝ):ℂ) : ℂ) = (((1 - 1/r : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast]
  rw [show ‖(((1 - 1/r : ℝ)) : ℂ)‖ = |1 - 1/r| from RCLike.norm_ofReal (1 - 1/r)]
  rw [abs_of_neg]
  · ring
  · rw [sub_neg, one_lt_div hr]; exact hrlt

/-- Imaginary part of `polarPt`. -/
lemma nec_polarPt_im {c r θ : ℝ} : (polarPt c r θ).im = r * Real.sin θ := by
  rw [polarPt, Complex.exp_ofReal_mul_I]
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re,
    Complex.add_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, mul_one,
    Complex.ofReal_re]

/-- `polarPt` at angle `0`. -/
lemma nec_polarPt_zero (c r : ℝ) : polarPt c r 0 = ((c + r : ℝ) : ℂ) := by
  simp only [polarPt, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [Complex.ofReal_add]

/-- `polarPt` at angle `π`. -/
lemma nec_polarPt_pi (c r : ℝ) : polarPt c r Real.pi = ((c - r : ℝ) : ℂ) := by
  rw [polarPt, Complex.exp_ofReal_mul_I, Real.cos_pi, Real.sin_pi]
  simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero]
  rw [Complex.ofReal_sub]
  ring

/-- `‖polarPt c r θ - c‖ = r`. -/
lemma nec_norm_polarPt_sub {c r θ : ℝ} (hr : 0 < r) :
    ‖polarPt c r θ - (c:ℂ)‖ = r := by
  have hsub : polarPt c r θ - (c:ℂ) = (r:ℂ) * Complex.exp ((θ:ℂ)*Complex.I) := by
    simp only [polarPt]; ring
  rw [hsub, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [show ‖((r:ℝ):ℂ)‖ = |r| from RCLike.norm_ofReal r, abs_of_pos hr]

/-- Injectivity of the polar parametrisation modulo `2π`. -/
lemma nec_polarPt_inj_mod_two_pi {c : ℝ} {f : ℝ → ℝ} (hf : ∀ θ, 0 < f θ) {θ θ' : ℝ}
    (h : polarPt c (f θ) θ = polarPt c (f θ') θ') :
    ∃ k : ℤ, θ' = θ + k * (2 * Real.pi) := by
  have hraw : (f θ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
      = (f θ' : ℂ) * Complex.exp ((θ' : ℂ) * Complex.I) := by
    have hc := h
    simp only [polarPt] at hc
    exact add_left_cancel hc
  have hn : f θ = f θ' := by
    have h2 := congrArg norm hraw
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I,
      mul_one, mul_one] at h2
    simpa [abs_of_pos (hf θ), abs_of_pos (hf θ')] using h2
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp ((θ' : ℂ) * Complex.I) := by
    have hne : (f θ' : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hf θ')
    rw [hn] at hraw
    exact mul_left_cancel₀ hne hraw
  obtain ⟨n, hn'⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨-n, ?_⟩
  have key3 : ((θ - θ' : ℝ) : ℂ) = (n : ℂ) * (2 * ↑Real.pi) := by
    have key : ((θ : ℂ) * Complex.I) - ((θ' : ℂ) * Complex.I) =
        ((n : ℂ) * (2 * ↑Real.pi)) * Complex.I := by
      rw [hn']; ring
    have key2 : ((θ - θ' : ℝ) : ℂ) * Complex.I = ((n : ℂ) * (2 * ↑Real.pi)) * Complex.I := by
      rw [← key]; push_cast; ring
    exact mul_right_cancel₀ Complex.I_ne_zero key2
  have key4 : θ - θ' = (n : ℝ) * (2 * Real.pi) := by
    apply Complex.ofReal_inj.mp
    rw [key3]
    simp only [Complex.ofReal_intCast, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have : θ' = θ + ((-n : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    linarith
  exact this

/-- `chordMap` applied to a point `c + r·u` with `‖u‖ = 1`, `r > 0`. -/
lemma nec_chordMap_add_unit {c u : ℂ} (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 < r) :
    chordMap c (c + (r:ℂ)*u) = c + ((r - 1 : ℝ):ℂ)*u := by
  have hnr : ‖(r:ℂ)*u‖ = r := by
    rw [norm_mul, hu, mul_one]
    rw [show ‖(r:ℂ)‖ = |r| from RCLike.norm_ofReal r, abs_of_pos hr]
  have hrc : (↑r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  simp only [chordMap]
  rw [add_sub_cancel_left, hnr]
  push_cast
  field_simp
  ring

/-- `chordMap` on the polar graph of a positive radius function. -/
lemma nec_chordMap_polarPt {c r θ : ℝ} (hr : 0 < r) :
    chordMap c (polarPt c r θ) = (c:ℂ) + ((r-1:ℝ):ℂ)*Complex.exp ((θ:ℂ)*Complex.I) := by
  have hu : ‖Complex.exp ((θ:ℂ)*Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  simpa [polarPt] using nec_chordMap_add_unit hu hr

/-- `chordMap c P - c` as a real multiple of `P - c` (for an arbitrary complex centre). -/
lemma nec_chordMap_sub (c P : ℂ) :
    chordMap c P - c = ((1 - 1/‖P - c‖ : ℝ):ℂ) * (P - c) := by
  have h1 : chordMap c P - c = (1 - 1/((‖P-c‖:ℝ):ℂ)) * (P - c) := by
    simp only [chordMap]; field_simp; ring
  rw [h1]
  congr 1
  push_cast; ring

/-- The chord involution: `chordMap c` is an involution on the annulus `0 < ‖P-c‖ < 1`. -/
lemma nec_chordMap_involutive {c P : ℂ} (h1 : 0 < ‖P - c‖) (h2 : ‖P - c‖ < 1) :
    chordMap c (chordMap c P) = P := by
  set r : ℝ := ‖P - c‖ with hr
  have hrpos : 0 < r := by rw [hr]; exact h1
  have hrlt : r < 1 := by rw [hr]; exact h2
  have hQc : chordMap c P - c = (1 - 1/((r:ℝ):ℂ)) * (P - c) := by
    have htmp : chordMap c P - c = (1 - 1/((‖P-c‖:ℝ):ℂ)) * (P - c) := by
      simp only [chordMap]; field_simp; ring
    rw [← hr] at htmp
    exact htmp
  have hQnorm : ‖chordMap c P - c‖ = 1 - r := by
    rw [hQc, norm_mul, nec_norm_one_sub_inv hrpos hrlt, ← hr]
    field_simp
  have hQ : chordMap c P = c + (1 - 1/((r:ℝ):ℂ)) * (P - c) := by rw [← hQc]; ring
  have hr1c : ((↑(1-r):ℝ):ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : (0:ℝ) < 1 - r))
  have hfinal :
      c + (1 - 1/((r:ℝ):ℂ)) * (P - c) - (1 - 1/((r:ℝ):ℂ)) * (P - c) / (((1-r:ℝ)):ℂ) = P := by
    have hrc : ((r:ℝ):ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos
    have hrc1 : (((1-r:ℝ)):ℂ) = 1 - (r:ℂ) := by push_cast; ring
    rw [hrc1]
    have h1r : (1 - (r:ℂ) : ℂ) ≠ 0 := by rw [← hrc1]; exact hr1c
    field_simp
    ring
  have step1 : chordMap c (chordMap c P) = chordMap c P - (chordMap c P - c) / (((1-r:ℝ)):ℂ) := by
    show chordMap c P - (chordMap c P - c) / ((‖chordMap c P - c‖:ℝ):ℂ) = _
    rw [hQnorm]
  rw [step1, hQc, hQ]
  exact hfinal

/-- `chordMap c` has no fixed points among the points with `0 < ‖P - c‖`. -/
lemma nec_chordMap_ne_self {c P : ℂ} (h : 0 < ‖P - c‖) : chordMap c P ≠ P := by
  intro hh
  have hX : (P - c) / ((‖P-c‖:ℝ):ℂ) = 0 := by
    have h2 := hh
    simp only [chordMap] at h2
    exact sub_eq_self.mp h2
  have hne : ((‖P-c‖:ℝ):ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt h
  have hPc : P - c = 0 := by
    rcases div_eq_zero_iff.mp hX with h|h
    · exact h
    · exact absurd h hne
  exact (norm_ne_zero_iff.mp (ne_of_gt h)) hPc

/-- Imaginary part of `chordMap c P` for a centre `c` on the real axis. -/
lemma nec_im_chordMap {c : ℂ} (hc : c.im = 0) (P : ℂ) :
    (chordMap c P).im = (1 - 1/‖P - c‖) * P.im := by
  have h := congrArg Complex.im (nec_chordMap_sub c P)
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, sub_zero, hc] at h
  exact h

/-- If `sin θ = 0` then `θ` is an integer multiple of `2π` or `π` plus one. -/
lemma nec_sin_eq_zero_iff_int_mul {θ : ℝ} (h : Real.sin θ = 0) :
    (∃ k : ℤ, θ = k * (2*Real.pi)) ∨ (∃ k : ℤ, θ = Real.pi + k*(2*Real.pi)) := by
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
  rcases Int.even_or_odd n with hev | hod
  · left; rcases hev with ⟨m, hm⟩; rw [hm] at hn; exact ⟨m, by rw [← hn]; push_cast; ring⟩
  · right; rcases hod with ⟨m, hm⟩; rw [hm] at hn; exact ⟨m, by rw [← hn]; push_cast; ring⟩

/-- The real-axis points of the polar graph of a `1`-chord function are the two endpoints. -/
lemma nec_real_pt_of_chord {c : ℝ} {ρ : ℝ → ℝ} (hpos : ∀ θ, 0 < ρ θ)
    (hchord : ∀ θ, ρ θ + ρ (θ + Real.pi) = 1) {P : ℂ}
    (hP : P ∈ Set.range (fun θ => polarPt c (ρ θ) θ)) (him : P.im = 0) :
    P = polarPt c (ρ 0) 0 ∨ P = polarPt c (ρ Real.pi) Real.pi := by
  obtain ⟨θ, rfl⟩ := hP
  have hsin : Real.sin θ = 0 := by
    have h := nec_polarPt_im (c := c) (r := ρ θ) (θ := θ)
    rw [h] at him
    exact (mul_eq_zero.mp him).resolve_left (ne_of_gt (hpos θ))
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have hper : Function.Periodic ρ (2 * Real.pi) := by
    intro θ; have h1 := hchord θ; have h2 := hchord (θ + Real.pi)
    have harg : θ + Real.pi + Real.pi = θ + 2*Real.pi := by ring
    rw [harg] at h2; linarith
  have hPper : Function.Periodic (fun θ => polarPt c (ρ θ) θ) (2*Real.pi) := by
    intro θ
    have hexp : Complex.exp ((↑(θ + 2*Real.pi) : ℂ) * Complex.I)
        = Complex.exp ((↑θ : ℂ) * Complex.I) := by
      rw [show ((↑(θ + 2*Real.pi) : ℂ)) * Complex.I
          = ((↑θ : ℂ) * Complex.I) + (2 * ↑Real.pi * Complex.I) by push_cast; ring]
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    simp only [polarPt]
    rw [hper θ, hexp]
  rcases Int.even_or_odd n with hev | hod
  · left
    rcases hev with ⟨m, hm⟩
    rw [hm] at hn
    have hθ : θ = 0 + (m:ℤ) * (2*Real.pi) := by rw [← hn]; push_cast; ring
    rw [hθ, (hPper.int_mul m) 0]
  · right
    rcases hod with ⟨m, hm⟩
    rw [hm] at hn
    have hθ : θ = Real.pi + (m:ℤ) * (2*Real.pi) := by rw [← hn]; push_cast; ring
    rw [hθ, (hPper.int_mul m) Real.pi]

/-- One-step map through `O₁` on the polar graph of a `1`-chord function. -/
lemma nec_chordMap_polarPt_O1 {a : ℝ} {ρ₁ : ℝ → ℝ} (hpos₁ : ∀ θ, 0 < ρ₁ θ)
    (hchord₁ : ∀ θ, ρ₁ θ + ρ₁ (θ + Real.pi) = 1) (θ : ℝ) :
    chordMap (O1_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ)
      = polarPt (-(a/2)) (ρ₁ (θ + Real.pi)) (θ + Real.pi) := by
  have hO1val : O1_sym a = ((-(a/2) : ℝ) : ℂ) := by simp only [O1_sym]; push_cast; ring
  rw [hO1val, nec_chordMap_polarPt (hpos₁ θ)]
  rw [polarPt]
  have hval : ρ₁ (θ + Real.pi) = 1 - ρ₁ θ := by have := hchord₁ θ; linarith
  rw [hval]
  have hexp : Complex.exp ((↑(θ + Real.pi) : ℂ) * Complex.I)
      = - Complex.exp ((↑θ : ℂ) * Complex.I) := by
    rw [show ((↑(θ + Real.pi) : ℂ)) * Complex.I
        = ((↑θ : ℂ) * Complex.I) + (↑Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [hexp]
  push_cast
  ring

/-- One-step map through `O₂` on the polar graph of a `1`-chord function. -/
lemma nec_chordMap_polarPt_O2 {a : ℝ} {ρ₂ : ℝ → ℝ} (hpos₂ : ∀ θ, 0 < ρ₂ θ)
    (hchord₂ : ∀ θ, ρ₂ θ + ρ₂ (θ + Real.pi) = 1) (θ : ℝ) :
    chordMap (O2_sym a) (polarPt (a/2) (ρ₂ θ) θ)
      = polarPt (a/2) (ρ₂ (θ + Real.pi)) (θ + Real.pi) := by
  have hO2val : O2_sym a = (((a/2) : ℝ) : ℂ) := by rw [O2_sym]
  rw [hO2val, nec_chordMap_polarPt (hpos₂ θ)]
  rw [polarPt]
  have hval : ρ₂ (θ + Real.pi) = 1 - ρ₂ θ := by have := hchord₂ θ; linarith
  rw [hval]
  have hexp : Complex.exp ((↑(θ + Real.pi) : ℂ) * Complex.I)
      = - Complex.exp ((↑θ : ℂ) * Complex.I) := by
    rw [show ((↑(θ + Real.pi) : ℂ)) * Complex.I
        = ((↑θ : ℂ) * Complex.I) + (↑Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [hexp]
  push_cast
  ring

/-- The two real-axis points computed about `O₁` and about `O₂` coincide. -/
lemma nec_axis_points_eq {a : ℝ} (ha0 : 0 < a) {ρ₁ ρ₂ : ℝ → ℝ}
    (hpos₁ : ∀ θ, 0 < ρ₁ θ) (hpos₂ : ∀ θ, 0 < ρ₂ θ)
    (hchord₁ : ∀ θ, ρ₁ θ + ρ₁ (θ + Real.pi) = 1)
    (hchord₂ : ∀ θ, ρ₂ θ + ρ₂ (θ + Real.pi) = 1)
    (hrange : Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) =
      Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ)) :
    polarPt (-(a/2)) (ρ₁ 0) 0 = polarPt (a/2) (ρ₂ 0) 0 ∧
      polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi = polarPt (a/2) (ρ₂ Real.pi) Real.pi := by
  have hA1 : polarPt (-(a/2)) (ρ₁ 0) 0 ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) :=
    Set.mem_range_self 0
  have hB1 : polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi
      ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) := Set.mem_range_self Real.pi
  have hA2 : polarPt (-(a/2)) (ρ₁ 0) 0 ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) := by
    rw [← hrange]; exact hA1
  have hB2 : polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi
      ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) := by rw [← hrange]; exact hB1
  have hAim : (polarPt (-(a/2)) (ρ₁ 0) 0).im = 0 := by
    rw [nec_polarPt_im, Real.sin_zero, mul_zero]
  have hBim : (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).im = 0 := by
    rw [nec_polarPt_im, Real.sin_pi, mul_zero]
  have hAc := nec_real_pt_of_chord (c := a/2) hpos₂ hchord₂ hA2 hAim
  have hBc := nec_real_pt_of_chord (c := a/2) hpos₂ hchord₂ hB2 hBim
  have hABne : polarPt (-(a/2)) (ρ₁ 0) 0 ≠ polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi := by
    intro h
    rw [nec_polarPt_zero, nec_polarPt_pi] at h
    have hre : -(a/2) + ρ₁ 0 = -(a/2) - ρ₁ Real.pi := Complex.ofReal_inj.mp h
    have hc := hchord₁ 0
    linarith [hpos₁ 0, hpos₁ Real.pi]
  have hcontra : -(a/2) - ρ₁ Real.pi = a/2 + ρ₂ 0 → False := by
    intro hre
    linarith [hpos₁ Real.pi, hpos₂ 0, ha0]
  refine ⟨?_, ?_⟩
  · rcases hAc with h1 | h1
    · exact h1
    · exfalso
      rcases hBc with h2 | h2
      · have hre : -(a/2) - ρ₁ Real.pi = a/2 + ρ₂ 0 := by
          have h := congrArg Complex.re h2
          rw [nec_polarPt_pi, nec_polarPt_zero] at h
          simpa using h
        exact hcontra hre
      · exact hABne (h1.trans h2.symm)
  · rcases hBc with h2 | h2
    · exfalso
      rcases hAc with h1 | h1
      · exact hABne (h1.trans h2.symm)
      · have hre : -(a/2) - ρ₁ Real.pi = a/2 + ρ₂ 0 := by
          have h := congrArg Complex.re h2
          rw [nec_polarPt_pi, nec_polarPt_zero] at h
          simpa using h
        exact hcontra hre
    · exact h2

/-- Fixed points of `eqT a` on the curve lie on the real axis. -/
lemma nec_eqT_fixed_im {a : ℝ} (ha0 : 0 < a) {ρ₁ ρ₂ : ℝ → ℝ}
    (hpos₁ : ∀ θ, 0 < ρ₁ θ) (hpos₂ : ∀ θ, 0 < ρ₂ θ)
    (hchord₁ : ∀ θ, ρ₁ θ + ρ₁ (θ + Real.pi) = 1)
    (hchord₂ : ∀ θ, ρ₂ θ + ρ₂ (θ + Real.pi) = 1)
    (hrange : Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) =
      Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ))
    {P : ℂ}
    (hP : P ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ))
    (hfix : eqT a P = P) : P.im = 0 := by
  have hO1val : O1_sym a = ((-(a/2) : ℝ) : ℂ) := by simp only [O1_sym]; push_cast; ring
  have hO2val : O2_sym a = (((a/2) : ℝ) : ℂ) := by rw [O2_sym]
  have hO1im : (O1_sym a).im = 0 := by rw [hO1val]; simp
  have hO2im : (O2_sym a).im = 0 := by rw [hO2val]; simp
  -- distance from a curve point to `O₁`
  have bound1 : ∀ X ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ),
      0 < ‖X - O1_sym a‖ ∧ ‖X - O1_sym a‖ < 1 := by
    intro X hX
    obtain ⟨θ, rfl⟩ := hX
    have hval : ‖polarPt (-(a/2)) (ρ₁ θ) θ - O1_sym a‖ = ρ₁ θ := by
      rw [hO1val]; exact nec_norm_polarPt_sub (hpos₁ θ)
    rw [hval]
    exact ⟨hpos₁ θ, by have := hchord₁ θ; linarith [hpos₁ (θ + Real.pi)]⟩
  -- the two-step map through `O₂` maps the curve into itself
  have mapsO2 : ∀ X ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ),
      chordMap (O2_sym a) X ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) := by
    intro X hX
    obtain ⟨φ, hφ'⟩ := (show X ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) from by
      rw [← hrange]; exact hX)
    have hφ : polarPt (a/2) (ρ₂ φ) φ = X := hφ'
    rw [← hφ, nec_chordMap_polarPt_O2 (a := a) hpos₂ hchord₂ φ]
    rw [hrange]
    exact Set.mem_range_self (φ + Real.pi)
  have hposP : 0 < ‖P - O1_sym a‖ := (bound1 P hP).1
  have hQ := mapsO2 P hP
  have hQpos : 0 < ‖chordMap (O2_sym a) P - O1_sym a‖ := (bound1 _ hQ).1
  have hQlt : ‖chordMap (O2_sym a) P - O1_sym a‖ < 1 := (bound1 _ hQ).2
  have hQeq : chordMap (O1_sym a) (chordMap (O2_sym a) P) = P := by
    show eqT a P = P
    exact hfix
  have hinv := nec_chordMap_involutive hQpos hQlt
  rw [hQeq] at hinv
  -- `hinv : chordMap (O1_sym a) P = chordMap (O2_sym a) P`
  by_contra hPim
  have e1 := nec_chordMap_sub (O1_sym a) P
  have e2 := nec_chordMap_sub (O2_sym a) P
  have him1 := nec_im_chordMap hO1im P
  have him2 := nec_im_chordMap hO2im P
  have hr_eq : (1 - 1/‖P - O1_sym a‖) = (1 - 1/‖P - O2_sym a‖) := by
    have h : (1 - 1/‖P - O1_sym a‖) * P.im = (1 - 1/‖P - O2_sym a‖) * P.im := by
      rw [him1.symm, hinv, him2]
    exact mul_right_cancel₀ hPim h
  have hla_eq : ((1 - 1/‖P - O2_sym a‖:ℝ):ℂ) = ((1 - 1/‖P - O1_sym a‖:ℝ):ℂ) := by rw [hr_eq]
  have e2' : chordMap (O2_sym a) P - O2_sym a = ((1 - 1/‖P - O1_sym a‖:ℝ):ℂ) * (P - O2_sym a) := by
    rw [e2, hla_eq]
  have h1' : chordMap (O1_sym a) P = O1_sym a + ((1 - 1/‖P - O1_sym a‖:ℝ):ℂ) * (P - O1_sym a) := by
    rw [← e1]; ring
  have h2'' : chordMap (O2_sym a) P = O2_sym a + ((1 - 1/‖P - O1_sym a‖:ℝ):ℂ) * (P - O2_sym a) := by
    rw [← e2']; ring
  have hdiff : (O1_sym a + ((1 - 1/‖P - O1_sym a‖:ℝ):ℂ) * (P - O1_sym a))
      - (O2_sym a + ((1 - 1/‖P - O1_sym a‖:ℝ):ℂ) * (P - O2_sym a)) = 0 := by
    rw [← h1', ← h2'', hinv, sub_self]
  have hsub : O1_sym a - O2_sym a = ((1 - 1/‖P - O1_sym a‖:ℝ):ℂ) * (O1_sym a - O2_sym a) := by
    have hexpand : (O1_sym a + ((1 - 1/‖P - O1_sym a‖:ℝ):ℂ) * (P - O1_sym a))
        - (O2_sym a + ((1 - 1/‖P - O1_sym a‖:ℝ):ℂ) * (P - O2_sym a))
        = (O1_sym a - O2_sym a) - ((1 - 1/‖P - O1_sym a‖:ℝ):ℂ) * (O1_sym a - O2_sym a) := by ring
    rw [hexpand] at hdiff
    exact sub_eq_zero.mp hdiff
  have hO12ne : O1_sym a - O2_sym a ≠ 0 := by
    rw [hO1val, hO2val]
    have hh : ((-(a/2) : ℝ) : ℂ) - (((a/2) : ℝ) : ℂ) = ((-a : ℝ) : ℂ) := by push_cast; ring
    rw [hh, ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hla1 : ((1 - 1/‖P - O1_sym a‖:ℝ):ℂ) = 1 := by
    have hsub1 : (1:ℂ) * (O1_sym a - O2_sym a) = ((1 - 1/‖P - O1_sym a‖:ℝ):ℂ) * (O1_sym a - O2_sym a) := by
      rw [one_mul]
      exact hsub
    exact (mul_right_cancel₀ hO12ne hsub1).symm
  have hfix1 : chordMap (O1_sym a) P = P := by
    have h := e1
    rw [hla1, one_mul] at h
    exact sub_left_inj.mp h
  exact nec_chordMap_ne_self hposP hfix1

/-- **Structure of a normalised equichordal curve.** -/
theorem normEqCurve_structure {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) :
    (∀ (c : ℝ) (f : ℝ → ℝ), (∀ θ, 0 < f θ) → ∀ θ θ' : ℝ,
        polarPt c (f θ) θ = polarPt c (f θ') θ' → ∃ k : ℤ, θ' = θ + k * (2 * Real.pi)) ∧
    (∀ (c : ℝ) (P : ℂ), 0 < ‖P - c‖ → ‖P - c‖ < 1 → chordMap c (chordMap c P) = P) ∧
    (∀ θ, ρ₁ (θ + 2 * Real.pi) = ρ₁ θ) ∧
    (∀ θ, ρ₂ (θ + 2 * Real.pi) = ρ₂ θ) ∧
    (∀ θ, chordMap (O1_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) =
        polarPt (-(a/2)) (ρ₁ (θ + Real.pi)) (θ + Real.pi)) ∧
    (∀ θ, chordMap (O2_sym a) (polarPt (a/2) (ρ₂ θ) θ) =
        polarPt (a/2) (ρ₂ (θ + Real.pi)) (θ + Real.pi)) ∧
    (∀ θ, chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) ∈
        Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) ∧
    (polarPt (-(a/2)) (ρ₁ 0) 0 = polarPt (a/2) (ρ₂ 0) 0) ∧
    (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi = polarPt (a/2) (ρ₂ Real.pi) Real.pi) ∧
    ((polarPt (-(a/2)) (ρ₁ 0) 0).im = 0) ∧
    ((polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).im = 0) ∧
    ((polarPt (-(a/2)) (ρ₁ 0) 0).re - (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re = 1) ∧
    ((polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re < -(a/2)) ∧
    (a/2 < (polarPt (-(a/2)) (ρ₁ 0) 0).re) ∧
    (∀ θ, (polarPt (-(a/2)) (ρ₁ θ) θ).im = 0 →
      (∃ k : ℤ, θ = k * (2 * Real.pi)) ∨ (∃ k : ℤ, θ = Real.pi + k * (2 * Real.pi))) ∧
    Set.MapsTo (eqT a) (Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ))
      (Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) ∧
    Set.InjOn (eqT a) (Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) ∧
    (∀ P ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ), eqT a P = P → P.im = 0) := by
  obtain ⟨hcont₁, hcont₂, hpos₁, hpos₂, hchord₁, hchord₂, hrange⟩ := hC
  have hO1val : O1_sym a = ((-(a/2) : ℝ) : ℂ) := by simp only [O1_sym]; push_cast; ring
  have hO2val : O2_sym a = (((a/2) : ℝ) : ℂ) := by rw [O2_sym]
  -- `2π`-periodicity of the radius functions, from the chord identity
  have hper₁ : Function.Periodic ρ₁ (2 * Real.pi) := by
    intro θ
    have h1 := hchord₁ θ
    have h2 := hchord₁ (θ + Real.pi)
    have harg : θ + Real.pi + Real.pi = θ + 2 * Real.pi := by ring
    rw [harg] at h2
    linarith
  have hper₂ : Function.Periodic ρ₂ (2 * Real.pi) := by
    intro θ
    have h1 := hchord₂ θ
    have h2 := hchord₂ (θ + Real.pi)
    have harg : θ + Real.pi + Real.pi = θ + 2 * Real.pi := by ring
    rw [harg] at h2
    linarith
  have c5 := nec_chordMap_polarPt_O1 (a := a) hpos₁ hchord₁
  have c6 := nec_chordMap_polarPt_O2 (a := a) hpos₂ hchord₂
  -- distance from a curve point to `O₁` / `O₂`
  have bound1 : ∀ X ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ),
      0 < ‖X - O1_sym a‖ ∧ ‖X - O1_sym a‖ < 1 := by
    intro X hX
    obtain ⟨θ, rfl⟩ := hX
    have hval : ‖polarPt (-(a/2)) (ρ₁ θ) θ - O1_sym a‖ = ρ₁ θ := by
      rw [hO1val]; exact nec_norm_polarPt_sub (hpos₁ θ)
    rw [hval]
    exact ⟨hpos₁ θ, by have := hchord₁ θ; linarith [hpos₁ (θ + Real.pi)]⟩
  have bound2 : ∀ X ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ),
      0 < ‖X - O2_sym a‖ ∧ ‖X - O2_sym a‖ < 1 := by
    intro X hX
    obtain ⟨θ, rfl⟩ := hX
    have hval : ‖polarPt (a/2) (ρ₂ θ) θ - O2_sym a‖ = ρ₂ θ := by
      rw [hO2val]; exact nec_norm_polarPt_sub (hpos₂ θ)
    rw [hval]
    exact ⟨hpos₂ θ, by have := hchord₂ θ; linarith [hpos₂ (θ + Real.pi)]⟩
  -- the two-step map through `O₂` sends the curve into itself
  have mapsO2 : ∀ X ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ),
      chordMap (O2_sym a) X ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) := by
    intro X hX
    obtain ⟨φ, hφ'⟩ := (show X ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) from by
      rw [← hrange]; exact hX)
    have hφ : polarPt (a/2) (ρ₂ φ) φ = X := hφ'
    rw [← hφ, c6 φ]
    rw [hrange]
    exact Set.mem_range_self (φ + Real.pi)
  -- injectivity of the one-step maps on the curve
  have injO1 : Set.InjOn (chordMap (O1_sym a)) (Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) := by
    intro X hX Y hY hXY
    have bX := bound1 X hX
    have bY := bound1 Y hY
    have h1 := nec_chordMap_involutive bX.1 bX.2
    have h2 := nec_chordMap_involutive bY.1 bY.2
    rw [← h1, hXY, h2]
  have injO2 : Set.InjOn (chordMap (O2_sym a)) (Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ)) := by
    intro X hX Y hY hXY
    have bX := bound2 X hX
    have h1 := nec_chordMap_involutive bX.1 bX.2
    have bY := bound2 Y hY
    have h2 := nec_chordMap_involutive bY.1 bY.2
    rw [← h1, hXY, h2]
  have hax := nec_axis_points_eq ha0 hpos₁ hpos₂ hchord₁ hchord₂ hrange
  -- assemble
  have hc1 : (∀ (c : ℝ) (f : ℝ → ℝ), (∀ θ, 0 < f θ) → ∀ θ θ' : ℝ,
      polarPt c (f θ) θ = polarPt c (f θ') θ' → ∃ k : ℤ, θ' = θ + k * (2 * Real.pi)) :=
    fun c f hf θ θ' h => nec_polarPt_inj_mod_two_pi hf h
  have hc2 : (∀ (c : ℝ) (P : ℂ), 0 < ‖P - c‖ → ‖P - c‖ < 1 → chordMap c (chordMap c P) = P) :=
    fun c P h1 h2 => nec_chordMap_involutive h1 h2
  have hc3 : (∀ θ, ρ₁ (θ + 2 * Real.pi) = ρ₁ θ) := hper₁
  have hc4 : (∀ θ, ρ₂ (θ + 2 * Real.pi) = ρ₂ θ) := hper₂
  have hc5 : (∀ θ, chordMap (O1_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) =
      polarPt (-(a/2)) (ρ₁ (θ + Real.pi)) (θ + Real.pi)) := c5
  have hc6 : (∀ θ, chordMap (O2_sym a) (polarPt (a/2) (ρ₂ θ) θ) =
      polarPt (a/2) (ρ₂ (θ + Real.pi)) (θ + Real.pi)) := c6
  have hc7 : (∀ θ, chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) ∈
      Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) :=
    fun θ => mapsO2 _ (Set.mem_range_self θ)
  have hc8 : polarPt (-(a/2)) (ρ₁ 0) 0 = polarPt (a/2) (ρ₂ 0) 0 := hax.1
  have hc9 : polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi = polarPt (a/2) (ρ₂ Real.pi) Real.pi := hax.2
  have hc10 : (polarPt (-(a/2)) (ρ₁ 0) 0).im = 0 := by
    rw [nec_polarPt_im, Real.sin_zero, mul_zero]
  have hc11 : (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).im = 0 := by
    rw [nec_polarPt_im, Real.sin_pi, mul_zero]
  have hc12 : (polarPt (-(a/2)) (ρ₁ 0) 0).re - (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re = 1 := by
    rw [nec_polarPt_zero, nec_polarPt_pi]
    simp only [Complex.ofReal_re]
    have hc0 : ρ₁ 0 + ρ₁ Real.pi = 1 := by simpa using hchord₁ 0
    linarith
  have hc13 : (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re < -(a/2) := by
    rw [nec_polarPt_pi]
    simp only [Complex.ofReal_re]
    linarith [hpos₁ Real.pi]
  have hc14 : a/2 < (polarPt (-(a/2)) (ρ₁ 0) 0).re := by
    have hre := congrArg Complex.re hc8
    rw [nec_polarPt_zero, nec_polarPt_zero] at hre
    simp only [Complex.ofReal_re] at hre
    rw [nec_polarPt_zero]
    simp only [Complex.ofReal_re]
    linarith [hpos₂ 0]
  have hc15 : (∀ θ, (polarPt (-(a/2)) (ρ₁ θ) θ).im = 0 →
      (∃ k : ℤ, θ = k * (2 * Real.pi)) ∨ (∃ k : ℤ, θ = Real.pi + k * (2 * Real.pi))) := by
    intro θ h
    rw [nec_polarPt_im] at h
    exact nec_sin_eq_zero_iff_int_mul ((mul_eq_zero.mp h).resolve_left (ne_of_gt (hpos₁ θ)))
  have hc16 : Set.MapsTo (eqT a) (Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ))
      (Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) := by
    intro P hP
    obtain ⟨ψ, hψ'⟩ := mapsO2 P hP
    have hψ : polarPt (-(a/2)) (ρ₁ ψ) ψ = chordMap (O2_sym a) P := hψ'
    show chordMap (O1_sym a) (chordMap (O2_sym a) P) ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)
    rw [← hψ, c5 ψ]
    exact Set.mem_range_self (ψ + Real.pi)
  have hc17 : Set.InjOn (eqT a) (Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) := by
    intro P hP P' hP' heq
    have hYP := mapsO2 P hP
    have hYP' := mapsO2 P' hP'
    have h1 : chordMap (O2_sym a) P = chordMap (O2_sym a) P' :=
      injO1 hYP hYP' (by simpa only [eqT] using heq)
    exact injO2 (by rw [← hrange]; exact hP) (by rw [← hrange]; exact hP') h1
  have hc18 : (∀ P ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ), eqT a P = P → P.im = 0) :=
    fun P hP hfix => nec_eqT_fixed_im ha0 hpos₁ hpos₂ hchord₁ hchord₂ hrange hP hfix
  exact ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18⟩

end Work.EQ
