import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea3.card_polarBox_filter_dvd_absDelta_gcd
import Submission.Work.FIArea7.card_gBox_filter_dvd_absDelta
import Submission.Commons.NumberTheory.Int.ncard_int_residue_class_sq_le

namespace Work.FIArea3

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/-- **Real arithmetic for the box count.**  If `hh ≥ 1`, `dp ≥ 1`, `d > 0`, `u ≥ 0` and
`hh * dp * k = d`, then

  `(20u/hh + 1)(20u/dp + 1) ≤ 401(u²k/d + u + 1)`.

The relation `hh*dp*k = d` is what converts the product `(20u/hh)(20u/dp) = (20u)²/(hh·dp)` into
`(20u)²·k/d`; the two linear terms are each at most `20u` because `hh, dp ≥ 1`. -/
lemma arith_bound (u hh dp k d : ℝ) (hu : 0 ≤ u) (hh1 : 1 ≤ hh) (dp1 : 1 ≤ dp)
    (hd : 0 < d) (hrel : hh * dp * k = d) :
    (20 * u / hh + 1) * (20 * u / dp + 1) ≤ 401 * (u ^ 2 * k / d + u + 1) := by
  have hhpos : 0 < hh := lt_of_lt_of_le zero_lt_one hh1
  have dppos : 0 < dp := lt_of_lt_of_le zero_lt_one dp1
  have hhdp : 0 < hh * dp := mul_pos hhpos dppos
  have hkpos : 0 < k := by
    rcases lt_or_ge 0 k with h | h
    · exact h
    · have : hh * dp * k ≤ 0 := by nlinarith [hhdp, h]
      rw [hrel] at this
      linarith
  have hAhh : 20 * u / hh ≤ 20 * u := by
    rw [div_le_iff₀ hhpos]; nlinarith [hu]
  have hAdp : 20 * u / dp ≤ 20 * u := by
    rw [div_le_iff₀ dppos]; nlinarith [hu]
  have hkey : 20 * u / hh * (20 * u / dp) = (20 * u) ^ 2 * k / d := by
    have h1 : hh ≠ 0 := ne_of_gt hhpos
    have h2 : dp ≠ 0 := ne_of_gt dppos
    have h3 : k ≠ 0 := ne_of_gt hkpos
    rw [div_mul_div_comm, ← hrel]
    field_simp
  have hmain : (20 * u / hh + 1) * (20 * u / dp + 1)
      = 20 * u / hh * (20 * u / dp) + 20 * u / hh + 20 * u / dp + 1 := by ring
  rw [hmain, hkey]
  have hkey2 : (20 * u) ^ 2 * k / d = 400 * (u ^ 2 * k / d) := by ring
  rw [hkey2]
  have h2 : 0 ≤ u ^ 2 * k / d :=
    div_nonneg (mul_nonneg (sq_nonneg u) hkpos.le) hd.le
  nlinarith [hAhh, hAdp, h2, hu]

/-
# `Work.FIArea3.card_polarBox_filter_dvd_absDelta_noBox` — the per-`z₁` `Δ`-count of the polar
box, with **no** hypothesis on `z₁`

For *any* Gaussian integer `z₁` (in particular NOT assumed to lie in the polar box, which is the
case needed by `Work.FIArea3.polarBox_delta_tau_sum_le`) and any `d ≥ 1`,

  `#{z ∈ polarBoxFinset Pa φ : d ∣ |Δ(z₁,z)|} ≤ 401·(u²·g/d + u + 1)`

where `u = θ√N` and `g = gcd (gcd z₁.re.natAbs z₁.im.natAbs) d`.

This is a rebase of the proved `Work.FIArea3.card_polarBox_filter_dvd_absDelta_gcd`, which needs
`z₁ ∈ polarBoxFinset Pa φ`; there the whole box is squeezed into the disc of radius `5u` around
`z₁`, whereas here `z₁` is unrelated to the box, so the two coordinates are treated separately:

* `Work.FIArea4.dist_polarBox_le` gives for every `z` in the box `‖z.toComplex - c₀‖ ≤ 5u` with
  `c₀ = (√N : ℂ)·exp(I(φ+πθ))`; hence `|(z.re:ℝ) - c₀.re| ≤ 5u` and `|(z.im:ℝ) - c₀.im| ≤ 5u`.
  (No `z₁` here.)
* Fibre `S := (polarBoxFinset Pa φ).filter (fun z => d ∣ absDelta z₁ z)` over `z.re`:
  `#S = Σ_{b ∈ S.image (fun z => z.re)} #(S.filter (fun z => z.re = b))`
  (`Finset.card_eq_sum_card_fiberwise`).
* Rows: every `b ∈ B := S.image (fun z => z.re)` satisfies `|b - c₀.re| ≤ 5u`; and if `z ∈ S` has
  `z.re = b` then `d ∣ absDelta z₁ z` gives `d ∣ Delta z₁ z = z₁.re·z.im - z₁.im·b`
  (`Work.FIArea7.dvd_Delta_of_dvd_absDelta`, `Work.FIArea4.Delta_eq`), hence, with
  `g' := gcd z₁.re.natAbs d`, `g' ∣ z₁.im·b`, i.e. `h ∣ b` for `h := g'/gcd g' z₁.im.natAbs`.
  So `B` lies in the multiples of `h` inside an interval of length `10u`, whence, applying
  `Commons.NumberTheory.Int.card_le_of_modEq_abs_le` to the shift `b - b₀` (`b₀ ∈ B`),
  `#B ≤ 20u/h + 1`.
* One row: two points `z, z'` of a row satisfy `(d/g') ∣ (im z - im z')` (subtract the two
  divisibilities and use `Work.FIArea3.dvd_div_gcd_of_dvd_mul`), and the `im`-values of a row lie
  in an interval of length `10u`; so a row has `≤ 20u·g'/d + 1` points.
* Arithmetic: `g'/h = gcd (gcd z₁.re.natAbs z₁.im.natAbs) d`, `h ≥ 1`, `g' ≤ d`, hence
  `(20u/h+1)(20u·g'/d+1) = 400u²(g'/h)/d + 20u/h + 20u·g'/d + 1 ≤ 400u²·g/d + 40u + 1`,
  which is `≤ 401(u²·g/d + u + 1)` since `u ≥ 0`.
-/
theorem card_polarBox_filter_dvd_absDelta_noBox (Pa : Work.FITop.Params) (φ : ℝ)
    (z₁ : GaussianInt) (d : ℕ) (hd : 1 ≤ d) :
    (((Work.FIArea3.polarBoxFinset Pa φ).filter
        (fun z => d ∣ Work.FIPlan.absDelta z₁ z)).card : ℝ)
      ≤ 401 * ((Pa.θ * Real.sqrt Pa.N) ^ 2
            * ((Nat.gcd (Nat.gcd z₁.re.natAbs z₁.im.natAbs) d : ℝ) / (d : ℝ))
          + Pa.θ * Real.sqrt Pa.N + 1) := by
  classical
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hu
  have hu0 : 0 ≤ u := by rw [hu]; exact mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  set c₀ : ℂ := (Real.sqrt Pa.N : ℂ)
    * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I) with hc₀
  set gr : ℕ := Nat.gcd z₁.re.natAbs d with hgr
  set k : ℕ := Nat.gcd z₁.im.natAbs gr with hk
  set hh : ℕ := gr / k with hhh
  set dp : ℕ := d / gr with hdp
  set gfull : ℕ := Nat.gcd (Nat.gcd z₁.re.natAbs z₁.im.natAbs) d with hgfull
  -- basic size facts
  have hd0 : 0 < d := hd
  have hgrpos : 0 < gr := Nat.gcd_pos_of_pos_right z₁.re.natAbs hd0
  have hkpos : 0 < k := Nat.gcd_pos_of_pos_right z₁.im.natAbs hgrpos
  have hkleq : k ≤ gr := Nat.gcd_le_right z₁.im.natAbs hgrpos
  have hgrleq : gr ≤ d := Nat.gcd_le_right z₁.re.natAbs hd0
  have hkdvd : k ∣ gr := Nat.gcd_dvd_right z₁.im.natAbs gr
  have hgrdvd : gr ∣ d := Nat.gcd_dvd_right z₁.re.natAbs d
  have hhhpos : 0 < hh := by rw [hhh]; exact Nat.div_pos hkleq hkpos
  have hdppos : 0 < dp := by rw [hdp]; exact Nat.div_pos hgrleq hgrpos
  have hhh1 : 1 ≤ hh := hhhpos
  have hdp1 : 1 ≤ dp := hdppos
  -- the `re`-image `B` and its `hh`-divisibility
  set S : Finset GaussianInt :=
    (polarBoxFinset Pa φ).filter (fun z => d ∣ Work.FIPlan.absDelta z₁ z) with hS
  set B : Finset ℤ := S.image (fun z => z.re) with hB
  -- the box is in the disc of radius `5u` around `c₀`
  have hdist : ∀ z ∈ S, ‖z.toComplex - c₀‖ ≤ 5 * u := by
    intro z hz
    have hz' : z ∈ S := hz
    rw [hS, Finset.mem_filter] at hz'
    have hbox : Work.FITop3.InPolarBox Pa φ z := (mem_polarBoxFinset.mp hz'.1).2
    have h := Work.FIArea4.dist_polarBox_le Pa φ z hbox
    have h5 : 5 * u = 5 * Pa.θ * Real.sqrt Pa.N := by rw [hu]; ring
    rw [h5]; exact h
  have hre : ∀ z ∈ S, |((z.re : ℤ) : ℝ) - c₀.re| ≤ 5 * u := by
    intro z hz
    have h1 : |((z.re : ℤ) : ℝ) - c₀.re| ≤ ‖z.toComplex - c₀‖ := by
      have hsub : ((z.re : ℤ) : ℝ) - c₀.re = (z.toComplex - c₀).re := by
        rw [Work.FIArea4.ofReal_re_eq_re z, Complex.sub_re]
      rw [hsub]
      exact Complex.abs_re_le_norm _
    linarith [hdist z hz]
  have him : ∀ z ∈ S, |((z.im : ℤ) : ℝ) - c₀.im| ≤ 5 * u := by
    intro z hz
    have h1 : |((z.im : ℤ) : ℝ) - c₀.im| ≤ ‖z.toComplex - c₀‖ := by
      have hsub : ((z.im : ℤ) : ℝ) - c₀.im = (z.toComplex - c₀).im := by
        rw [Work.FIArea4.ofReal_im_eq_im z, Complex.sub_im]
      rw [hsub]
      exact Complex.abs_im_le_norm _
    linarith [hdist z hz]
  -- `re`-values of `B` lie within `5u` of `c₀.re`
  have hB_re : ∀ b ∈ B, |((b : ℤ) : ℝ) - c₀.re| ≤ 5 * u := by
    intro b hb
    rw [hB, Finset.mem_image] at hb
    obtain ⟨z, hz, rfl⟩ := hb
    exact hre z hz
  -- every `b ∈ B` is divisible by `hh`
  have hB_dvd : ∀ b ∈ B, (hh : ℤ) ∣ b := by
    intro b hb
    rw [hB, Finset.mem_image] at hb
    obtain ⟨z, hzS, rfl⟩ := hb
    have hd1 : d ∣ Work.FIPlan.absDelta z₁ z := (Finset.mem_filter.mp hzS).2
    have hDz : (d : ℤ) ∣ Work.FIPlan.Delta z₁ z :=
      Work.FIArea7.dvd_Delta_of_dvd_absDelta hd1
    rw [Work.FIArea7.Delta_eq] at hDz
    have hgrz : (gr : ℤ) ∣ (d : ℤ) := Int.ofNat_dvd.mpr hgrdvd
    have hgrre : (gr : ℤ) ∣ z₁.re := by
      rw [← Int.dvd_natAbs]
      exact Int.ofNat_dvd.mpr (Nat.gcd_dvd_left z₁.re.natAbs d)
    have hDz' : (gr : ℤ) ∣ z₁.re * z.im - z₁.im * z.re := hgrz.trans hDz
    have hreim : (gr : ℤ) ∣ z₁.re * z.im := dvd_mul_of_dvd_left hgrre z.im
    have himre : (gr : ℤ) ∣ z₁.im * z.re := by
      have h := dvd_sub hreim hDz'
      have he : z₁.re * z.im - (z₁.re * z.im - z₁.im * z.re) = z₁.im * z.re := by ring
      rwa [he] at h
    have hmain := dvd_div_gcd_of_dvd_mul hgrpos himre
    have h1 : ((hh : ℕ) : ℤ) = ((gr / Nat.gcd z₁.im.natAbs gr : ℕ) : ℤ) := by
      rw [hhh, hk]
    rw [h1]
    exact hmain
  -- the number of rows is bounded
  have hBcard : (B.card : ℝ) ≤ 20 * u / (hh : ℝ) + 1 := by
    rcases B.eq_empty_or_nonempty with hem | hne
    · rw [hem]
      simp only [Finset.card_empty, Nat.cast_zero]
      have h0 : (0 : ℝ) ≤ 20 * u / (hh : ℝ) := by positivity
      linarith
    · obtain ⟨b₀, hb₀⟩ := hne
      set V : Finset ℤ := B.image (fun b => b - b₀) with hV
      have hVcard : V.card = B.card := by
        rw [hV]
        refine Finset.card_image_of_injOn ?_
        intro x _ y _ hxy
        linarith [hxy]
      have hcong : ∀ a ∈ V, a ≡ (0 : ℤ) [ZMOD (hh : ℤ)] := by
        intro a ha
        rw [hV, Finset.mem_image] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        rw [Int.modEq_zero_iff_dvd]
        exact dvd_sub (hB_dvd b hb) (hB_dvd b₀ hb₀)
      have habs : ∀ a ∈ V, |(a : ℝ)| ≤ 10 * u := by
        intro a ha
        rw [hV, Finset.mem_image] at ha
        obtain ⟨b, hb, rfl⟩ := ha
        have h1 : (((b - b₀ : ℤ)) : ℝ) = ((b : ℤ) : ℝ) - ((b₀ : ℤ) : ℝ) := by push_cast; ring
        rw [h1]
        have hb1 := hB_re b hb
        have hb01 := hB_re b₀ hb₀
        calc |((b : ℤ) : ℝ) - ((b₀ : ℤ) : ℝ)|
            ≤ |((b : ℤ) : ℝ) - c₀.re| + |c₀.re - ((b₀ : ℤ) : ℝ)| := abs_sub_le _ _ _
          _ = |((b : ℤ) : ℝ) - c₀.re| + |((b₀ : ℤ) : ℝ) - c₀.re| := by
                rw [abs_sub_comm c₀.re ((b₀ : ℤ) : ℝ)]
          _ ≤ 10 * u := by linarith
      have hA0 : (0 : ℝ) ≤ 10 * u := by positivity
      have h := Commons.NumberTheory.Int.card_le_of_modEq_abs_le (d := hh) hhh1 (s := V)
        (r := (0 : ℤ)) (A := 10 * u) hA0 hcong habs
      have h' : (V.card : ℝ) ≤ 20 * u / (hh : ℝ) + 1 := by
        have he : 2 * (10 * u) / (hh : ℝ) = 20 * u / (hh : ℝ) := by ring
        linarith [h, he]
      rwa [hVcard] at h'
  -- each row is bounded
  have hrow_le : ∀ b ∈ B,
      ((S.filter (fun z => z.re = b)).card : ℝ) ≤ 20 * u / (dp : ℝ) + 1 := by
    intro b hb
    set F : Finset GaussianInt := S.filter (fun z => z.re = b) with hF
    rcases F.eq_empty_or_nonempty with hem | hne
    · rw [hem]
      simp only [Finset.card_empty, Nat.cast_zero]
      have h0 : (0 : ℝ) ≤ 20 * u / (dp : ℝ) := by positivity
      linarith
    · obtain ⟨z₀, hz₀⟩ := hne
      set U : Finset ℤ := F.image (fun z => z.im - z₀.im) with hU
      have hUF : U.card = F.card := by
        rw [hU]
        refine Finset.card_image_of_injOn ?_
        intro x hx y hy hxy
        have hxF : x ∈ F := hx
        have hyF : y ∈ F := hy
        rw [hF, Finset.mem_filter] at hxF hyF
        exact Zsqrtd.ext (by rw [hxF.2, hyF.2]) (by linarith [hxy])
      have hcong : ∀ a ∈ U, a ≡ (0 : ℤ) [ZMOD (dp : ℤ)] := by
        intro a ha
        rw [hU, Finset.mem_image] at ha
        obtain ⟨z, hzF, rfl⟩ := ha
        have hzF' : z ∈ F := hzF
        have hz0' : z₀ ∈ F := hz₀
        rw [hF, Finset.mem_filter] at hzF' hz0'
        have hd1 : d ∣ Work.FIPlan.absDelta z₁ z := (Finset.mem_filter.mp hzF'.1).2
        have hdivz0 : d ∣ Work.FIPlan.absDelta z₁ z₀ := (Finset.mem_filter.mp hz0'.1).2
        have hDz : (d : ℤ) ∣ Work.FIPlan.Delta z₁ z :=
          Work.FIArea7.dvd_Delta_of_dvd_absDelta hd1
        have hD0 : (d : ℤ) ∣ Work.FIPlan.Delta z₁ z₀ :=
          Work.FIArea7.dvd_Delta_of_dvd_absDelta hdivz0
        rw [Work.FIArea7.Delta_eq] at hDz hD0
        have hsub : (d : ℤ) ∣ z₁.re * z.im - z₁.im * z.re
            - (z₁.re * z₀.im - z₁.im * z₀.re) := dvd_sub hDz hD0
        have hre_eq : z₁.re * z.im - z₁.im * z.re - (z₁.re * z₀.im - z₁.im * z₀.re)
            = z₁.re * (z.im - z₀.im) := by rw [hzF'.2, hz0'.2]; ring
        rw [hre_eq] at hsub
        have hmain := dvd_div_gcd_of_dvd_mul hd0 hsub
        rw [Int.modEq_zero_iff_dvd]
        have h1 : ((dp : ℕ) : ℤ) = ((d / Nat.gcd z₁.re.natAbs d : ℕ) : ℤ) := by rw [hdp, hgr]
        rw [h1]
        exact hmain
      have habs : ∀ a ∈ U, |(a : ℝ)| ≤ 10 * u := by
        intro a ha
        rw [hU, Finset.mem_image] at ha
        obtain ⟨z, hzF, rfl⟩ := ha
        have hzF' : z ∈ F := hzF
        rw [hF, Finset.mem_filter] at hzF'
        have hz0S : z₀ ∈ S := (Finset.mem_filter.mp hz₀).1
        have h1 : (((z.im - z₀.im : ℤ)) : ℝ) = ((z.im : ℤ) : ℝ) - ((z₀.im : ℤ) : ℝ) := by
          push_cast; ring
        rw [h1]
        have hz2 := him z hzF'.1
        have h02 := him z₀ hz0S
        calc |((z.im : ℤ) : ℝ) - ((z₀.im : ℤ) : ℝ)|
            ≤ |((z.im : ℤ) : ℝ) - c₀.im| + |c₀.im - ((z₀.im : ℤ) : ℝ)| := abs_sub_le _ _ _
          _ = |((z.im : ℤ) : ℝ) - c₀.im| + |((z₀.im : ℤ) : ℝ) - c₀.im| := by
                rw [abs_sub_comm c₀.im ((z₀.im : ℤ) : ℝ)]
          _ ≤ 10 * u := by linarith
      have hA0 : (0 : ℝ) ≤ 10 * u := by positivity
      have h := Commons.NumberTheory.Int.card_le_of_modEq_abs_le (d := dp) hdp1 (s := U)
        (r := (0 : ℤ)) (A := 10 * u) hA0 hcong habs
      have h' : (U.card : ℝ) ≤ 20 * u / (dp : ℝ) + 1 := by
        have he : 2 * (10 * u) / (dp : ℝ) = 20 * u / (dp : ℝ) := by ring
        linarith [h, he]
      rwa [hUF] at h'
  -- assemble
  have hrow_sum : (S.card : ℝ) ≤ (B.card : ℝ) * (20 * u / (dp : ℝ) + 1) := by
    have hmapsto : Set.MapsTo (fun z : GaussianInt => z.re) (↑S : Set GaussianInt)
        (↑B : Set ℤ) := fun z hz => Finset.mem_image_of_mem _ hz
    have hfib := Finset.card_eq_sum_card_fiberwise hmapsto
    have hble := Finset.sum_le_sum hrow_le
    rw [hfib, Nat.cast_sum]
    calc ∑ b ∈ B, ((S.filter (fun z => z.re = b)).card : ℝ)
        ≤ ∑ _b ∈ B, (20 * u / (dp : ℝ) + 1) := hble
      _ = (B.card : ℝ) * (20 * u / (dp : ℝ) + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hdpnn : (0 : ℝ) ≤ 20 * u / (dp : ℝ) + 1 := by positivity
  have step : (B.card : ℝ) * (20 * u / (dp : ℝ) + 1)
      ≤ (20 * u / (hh : ℝ) + 1) * (20 * u / (dp : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hBcard hdpnn
  -- the arithmetic
  have hrelN : hh * dp * k = d := by
    have hhgr : hh * k = gr := by rw [hhh]; exact Nat.div_mul_cancel hkdvd
    have hgrd : gr * dp = d := by rw [hdp]; rw [mul_comm]; exact Nat.div_mul_cancel hgrdvd
    calc hh * dp * k = dp * (hh * k) := by ring
      _ = dp * gr := by rw [hhgr]
      _ = d := by rw [mul_comm dp gr]; exact hgrd
  have hrelR : (hh : ℝ) * (dp : ℝ) * (k : ℝ) = (d : ℝ) := by exact_mod_cast hrelN
  have hhh1R : (1 : ℝ) ≤ hh := by exact_mod_cast hhh1
  have hdp1R : (1 : ℝ) ≤ dp := by exact_mod_cast hdp1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have harith := arith_bound u (hh : ℝ) (dp : ℝ) (k : ℝ) (d : ℝ) hu0 hhh1R hdp1R hdR hrelR
  -- identify `k` with the requested gcd
  have hkfull : k = gfull := by
    rw [hk, hgr, hgfull]
    rw [Nat.gcd_comm z₁.im.natAbs (Nat.gcd z₁.re.natAbs d)]
    rw [Nat.gcd_comm z₁.re.natAbs d]
    rw [Nat.gcd_assoc]
    rw [Nat.gcd_comm d (Nat.gcd z₁.re.natAbs z₁.im.natAbs)]
  have hkg : (k : ℝ) = (gfull : ℝ) := by rw [hkfull]
  have hSk : (S.card : ℝ) ≤ 401 * (u ^ 2 * ((k : ℝ) / (d : ℝ)) + u + 1) := by
    calc (S.card : ℝ) ≤ (B.card : ℝ) * (20 * u / (dp : ℝ) + 1) := hrow_sum
      _ ≤ (20 * u / (hh : ℝ) + 1) * (20 * u / (dp : ℝ) + 1) := step
      _ ≤ 401 * (u ^ 2 * (k : ℝ) / (d : ℝ) + u + 1) := harith
      _ = 401 * (u ^ 2 * ((k : ℝ) / (d : ℝ)) + u + 1) := by ring
  rw [hkg] at hSk
  exact hSk

end

end Work.FIArea3
