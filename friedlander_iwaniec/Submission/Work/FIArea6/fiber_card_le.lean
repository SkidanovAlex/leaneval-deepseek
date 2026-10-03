import Mathlib
import Submission.Work.FIArea6.elem_helpers

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Elementary facts about the Gaussian integers -/

/-- `|z|² = re² + im²` for a Gaussian integer. -/
lemma gnorm_cast_int (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  show ((Zsqrtd.norm z).natAbs : ℤ) = z.re ^ 2 + z.im ^ 2
  rw [GaussianInt.abs_natCast_norm, Zsqrtd.norm_def]
  ring

lemma gnorm_cast_real (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
  have h : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := gnorm_cast_int z
  exact_mod_cast h

/-- `Δ(z₁,z₂) = re z₁ · im z₂ − im z₁ · re z₂`. -/
lemma delta_eq (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z1.im * z2.re := by
  rw [Work.FIPlan.Delta, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-! ### `θ ≤ 1` -/

lemma theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hlog : 1 ≤ Real.log (Pa.x : ℝ) := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h
    exact le_of_lt (lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) hx3))
  have hA'0 : (0 : ℝ) ≤ Pa.A' := by
    have h2 : (0 : ℝ) < 2 * Pa.A + 2 ^ (20 : ℕ) := by
      have := Pa.hA; positivity
    linarith [Pa.hA']
  exact Real.rpow_le_one_of_one_le_of_nonpos hlog (by linarith)

/-! ### Squarefreeness of the norm on the support of `β` -/

lemma squarefree_of_beta_ne_zero {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) {z : GaussianInt} (hz : β z ≠ 0) :
    Squarefree (Work.FIPlan.gnorm z) := by
  obtain ⟨q, p, _hq0, _hq1, _hqsupp, -, -, _hp0, _hp1, _hpsupp, -, -, hform⟩ := hβ
  rw [hform z] at hz
  have hcond : Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) := by
    by_contra hc
    rw [if_neg hc] at hz
    exact hz rfl
  rw [if_pos hcond] at hz
  have hmu : (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1).2
  have hmuZ : ArithmeticFunction.moebius (Work.FIPlan.gnorm z) ≠ 0 := by
    intro h0
    exact hmu (by rw [h0]; norm_num)
  exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuZ

/-! ### `gcd(re z, im z) = 1` on squarefree norms -/

lemma isCoprime_re_im_of_squarefree {z : GaussianInt}
    (hsq : Squarefree (Work.FIPlan.gnorm z)) : IsCoprime z.re z.im := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  set g : ℕ := z.re.gcd z.im with hg
  have hgpos : 0 < g := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    have h0' : z.re.gcd z.im = 0 := by rw [← hg]; exact h0
    have hz : z = 0 := by
      have h := Int.gcd_eq_zero_iff.mp h0'
      exact Zsqrtd.ext h.1 h.2
    have hz0 : Work.FIPlan.gnorm (0 : GaussianInt) = 0 := by
      simp [Work.FIPlan.gnorm]
    rw [hz, hz0] at hsq
    exact not_squarefree_zero hsq
  have hdiv : g ^ 2 ∣ Work.FIPlan.gnorm z := by
    have h1 : ((g : ℕ) : ℤ) ∣ z.re := by rw [hg]; exact Int.gcd_dvd_left z.re z.im
    have h2 : ((g : ℕ) : ℤ) ∣ z.im := by rw [hg]; exact Int.gcd_dvd_right z.re z.im
    obtain ⟨u, hu⟩ := h1
    obtain ⟨v, hv⟩ := h2
    have key : (Work.FIPlan.gnorm z : ℤ) = ((g ^ 2 : ℕ) : ℤ) * (u ^ 2 + v ^ 2) := by
      rw [gnorm_cast_int, hu, hv]; push_cast; ring
    exact Int.natCast_dvd_natCast.mp ⟨u ^ 2 + v ^ 2, key⟩
  have hg2 : g ^ 2 ∣ g := Squarefree.pow_dvd_of_pow_dvd hsq hdiv
  obtain ⟨cc, hcc⟩ := hg2
  have hcancel : g = g * (g * cc) := hcc.trans (by ring)
  have hone : 1 = g * cc := Nat.mul_left_cancel hgpos (by rw [mul_one]; exact hcancel)
  exact Nat.dvd_one.mp ⟨cc, hone⟩

/-! ### The kernel of `w ↦ Δ(z₁,w)` -/

lemma eq_mul_of_coprime_mul {a b x y : ℤ} (ha : a ≠ 0) (hcop : IsCoprime a b)
    (h : a * y = b * x) : ∃ t : ℤ, x = a * t ∧ y = b * t := by
  have hdiv : a ∣ b * x := ⟨y, h.symm⟩
  obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_left hdiv
  refine ⟨t, ht, ?_⟩
  have : a * y = a * (b * t) := by rw [h, ht]; ring
  exact mul_left_cancel₀ ha this

lemma eq_mul_of_delta_eq_zero {z1 w : GaussianInt} (ha : z1.re ≠ 0)
    (hcop : IsCoprime z1.re z1.im) (h : Work.FIPlan.Delta z1 w = 0) :
    ∃ t : ℤ, w = (t : GaussianInt) * z1 := by
  have hlin : z1.re * w.im = z1.im * w.re := by
    rw [delta_eq] at h; linarith
  obtain ⟨t, ht1, ht2⟩ := eq_mul_of_coprime_mul ha hcop hlin
  refine ⟨t, ?_⟩
  apply Zsqrtd.ext
  · rw [Zsqrtd.re_smul, ht1]; ring
  · rw [Zsqrtd.im_smul, ht2]; ring

/-! ### The quadratic identity for the norm along the line `{Δ(z₁,·)=m}` -/

lemma quad_norm (z1 z0 : GaussianInt) (s : ℤ) :
    (Work.FIPlan.gnorm (z0 + (s : GaussianInt) * z1) : ℝ)
      = (Work.FIPlan.gnorm z1 : ℝ) * (s : ℝ) ^ 2
        + 2 * ((z1.re * z0.re + z1.im * z0.im : ℤ) : ℝ) * (s : ℝ)
        + (Work.FIPlan.gnorm z0 : ℝ) := by
  have hre : (z0 + (s : GaussianInt) * z1).re = z0.re + s * z1.re := by
    rw [Zsqrtd.re_add, Zsqrtd.re_smul]
  have him : (z0 + (s : GaussianInt) * z1).im = z0.im + s * z1.im := by
    rw [Zsqrtd.im_add, Zsqrtd.im_smul]
  rw [gnorm_cast_real (z0 + (s : GaussianInt) * z1), hre, him,
    gnorm_cast_real z1, gnorm_cast_real z0]
  push_cast
  ring

lemma cf_sub_e_sq (z1 z0 : GaussianInt) :
    (Work.FIPlan.gnorm z1 : ℝ) * (Work.FIPlan.gnorm z0 : ℝ)
      - ((z1.re * z0.re + z1.im * z0.im : ℤ) : ℝ) ^ 2
      = ((Work.FIPlan.Delta z1 z0 : ℤ) : ℝ) ^ 2 := by
  have hZ : (Work.FIPlan.gnorm z1 : ℤ) * (Work.FIPlan.gnorm z0 : ℤ)
      - (z1.re * z0.re + z1.im * z0.im) ^ 2 = (Work.FIPlan.Delta z1 z0) ^ 2 := by
    rw [gnorm_cast_int z1, gnorm_cast_int z0, delta_eq]
    ring
  exact_mod_cast hZ

/-! ### Two integers in a short quadratic window are close -/

lemma sq_sub_le_seven_of_quad {c e f B : ℝ} (hc : 0 < c) (hce : 0 ≤ c * f - e ^ 2)
    (hB : B < 2 * c) {s t : ℤ}
    (hs : c * (s : ℝ) ^ 2 + 2 * e * (s : ℝ) + f ≤ B)
    (ht : c * (t : ℝ) ^ 2 + 2 * e * (t : ℝ) + f ≤ B) :
    (s - t) ^ 2 ≤ 7 := by
  have key : ∀ u : ℤ, (c * (u : ℝ) + e) ^ 2
      ≤ c * (c * (u : ℝ) ^ 2 + 2 * e * (u : ℝ) + f) := by
    intro u; nlinarith [hce]
  have hs' : (c * (s : ℝ) + e) ^ 2 ≤ c * B := by
    have := key s; nlinarith [this, hs, hc]
  have ht' : (c * (t : ℝ) + e) ^ 2 ≤ c * B := by
    have := key t; nlinarith [this, ht, hc]
  have h3 : (c * ((s : ℝ) - (t : ℝ))) ^ 2 ≤ 4 * c * B := by
    have hid : c * ((s : ℝ) - (t : ℝ)) = (c * (s : ℝ) + e) - (c * (t : ℝ) + e) := by ring
    rw [hid]; nlinarith [hs', ht']
  have h4 : c * ((s : ℝ) - (t : ℝ)) ^ 2 ≤ 4 * B := by
    have hh : c * (c * ((s : ℝ) - (t : ℝ)) ^ 2) ≤ c * (4 * B) := by nlinarith [h3]
    exact le_of_mul_le_mul_left hh hc
  have h5 : ((s : ℝ) - (t : ℝ)) ^ 2 < 8 := by
    have hh : c * ((s : ℝ) - (t : ℝ)) ^ 2 < c * 8 := by nlinarith [h4, hB, hc]
    exact lt_of_mul_lt_mul_left hh (le_of_lt hc)
  have h6 : ((s - t : ℤ) : ℝ) ^ 2 < 8 := by push_cast; exact h5
  have h7 : (s - t) ^ 2 < 8 := by exact_mod_cast h6
  have := Int.lt_iff_add_one_le.mp h7
  omega

/-! ### A `Finset ℤ` whose elements are pairwise within distance `2` has at most `3` elements -/

lemma card_le_three_of_pairwise {T : Finset ℤ}
    (h : ∀ a ∈ T, ∀ b ∈ T, (a - b) ^ 2 ≤ 7) : T.card ≤ 3 := by
  rcases T.eq_empty_or_nonempty with hT | hne
  · rw [hT]; simp
  · have hsub : T ⊆ Finset.Icc (T.min' hne) (T.max' hne) := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le T x hx, Finset.le_max' T x hx⟩
    have hcard : T.card ≤ (T.max' hne + 1 - T.min' hne).toNat := by
      have := Finset.card_le_card hsub
      rwa [Int.card_Icc] at this
    have hmin := Finset.min'_mem T hne
    have hmax := Finset.max'_mem T hne
    have hx := h (T.max' hne) hmax (T.min' hne) hmin
    have hle : T.max' hne - T.min' hne ≤ 2 := by
      by_contra hc
      have h3 : 3 ≤ T.max' hne - T.min' hne := by omega
      have h0 : 0 ≤ T.max' hne - T.min' hne := sub_nonneg.mpr (Finset.min'_le T _ hmax)
      nlinarith [hx, h3, h0]
    have htoNat : (T.max' hne + 1 - T.min' hne).toNat ≤ 3 := by
      have h1 : T.max' hne + 1 - T.min' hne ≤ (3 : ℤ) := by linarith
      have := Int.toNat_le_toNat h1
      simpa using this
    exact le_trans hcard htoNat

theorem fiber_card_le (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ)
    (hβ : Work.FITop3.IsBetaCoeff Pa φ β) :
    ∀ z1 ∈ Work.FITop.boxN Pa, β z1 ≠ 0 → ∀ m : ℤ,
      (((Work.FITop.boxN Pa).filter
        (fun z2 => β z2 ≠ 0 ∧ Work.FIPlan.Delta z1 z2 = m)).card : ℝ) ≤ 3 := by
  intro z1 _hz1mem hz1 m
  set S := (Work.FITop.boxN Pa).filter
      (fun z2 => β z2 ≠ 0 ∧ Work.FIPlan.Delta z1 z2 = m) with hSdef
  rcases S.eq_empty_or_nonempty with hS | hSne
  · rw [hS]; simp
  · obtain ⟨z0, hz0S⟩ := hSne
    have hz0delta : Work.FIPlan.Delta z1 z0 = m := (Finset.mem_filter.mp hz0S).2.2
    have hsq1 : Squarefree (Work.FIPlan.gnorm z1) := squarefree_of_beta_ne_zero hβ hz1
    have hcop : IsCoprime z1.re z1.im := isCoprime_re_im_of_squarefree hsq1
    have hre1 : z1.re ≠ 0 := by
      have hodd : Odd z1.re := (beta_support hβ hz1).1.1.1
      intro h0
      obtain ⟨k, hk⟩ := hodd
      omega
    let P : GaussianInt → Prop := fun z2 => ∃ t : ℤ, z2 = z0 + (t : GaussianInt) * z1
    let tfun : GaussianInt → ℤ := fun z2 => if h : P z2 then h.choose else 0
    have hP : ∀ z2 ∈ S, z2 = z0 + (tfun z2 : GaussianInt) * z1 := by
      intro z2 hz2
      have hz2d : Work.FIPlan.Delta z1 z2 = m := (Finset.mem_filter.mp hz2).2.2
      have hd : Work.FIPlan.Delta z1 (z2 - z0) = 0 := by
        rw [delta_eq] at hz2d hz0delta ⊢
        simp only [Zsqrtd.re_sub, Zsqrtd.im_sub]
        linarith
      have hPz : P z2 := by
        obtain ⟨t, ht⟩ := eq_mul_of_delta_eq_zero hre1 hcop hd
        exact ⟨t, by rw [← ht]; abel⟩
      have htfun : tfun z2 = hPz.choose := by
        simp only [tfun]
        rw [dif_pos hPz]
      rw [htfun]
      exact hPz.choose_spec
    have hinj : Set.InjOn tfun ↑S := by
      intro z2 hz2 z2' hz2' heq
      rw [Finset.mem_coe] at hz2 hz2'
      rw [hP z2 hz2, hP z2' hz2', heq]
    have hmap : Set.MapsTo tfun ↑S ↑(S.image tfun) := by
      intro z2 hz2
      rw [Finset.mem_coe] at hz2
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨z2, hz2, rfl⟩)
    have hcard_le : S.card ≤ (S.image tfun).card :=
      Finset.card_le_card_of_injOn tfun hmap hinj
    have hT : (S.image tfun).card ≤ 3 := by
      refine card_le_three_of_pairwise ?_
      intro a ha b hb
      rw [Finset.mem_image] at ha hb
      obtain ⟨z2, hz2S, rfl⟩ := ha
      obtain ⟨z2', hz2'S, rfl⟩ := hb
      have hb2 : β z2 ≠ 0 := (Finset.mem_filter.mp hz2S).2.1
      have hb2' : β z2' ≠ 0 := (Finset.mem_filter.mp hz2'S).2.1
      have hn2 := beta_support_norm hβ hb2
      have hn2' := beta_support_norm hβ hb2'
      have hn1 := (beta_support_norm hβ hz1).1
      refine sq_sub_le_seven_of_quad (c := (Work.FIPlan.gnorm z1 : ℝ))
        (e := ((z1.re * z0.re + z1.im * z0.im : ℤ) : ℝ))
        (f := (Work.FIPlan.gnorm z0 : ℝ)) (B := (1 + Pa.θ) * Pa.N) ?_ ?_ ?_ ?_ ?_
      · have hNpos : (0 : ℝ) < Pa.N := by
          have : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
          linarith
        linarith
      · rw [cf_sub_e_sq z1 z0]; positivity
      · have hθ := theta_le_one Pa
        have hNnn : (0 : ℝ) ≤ Pa.N := by
          have : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
          linarith
        have h1 : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by nlinarith [hθ, hNnn]
        have h2 : 2 * Pa.N < 2 * (Work.FIPlan.gnorm z1 : ℝ) := by linarith
        linarith
      · have hgn : (Work.FIPlan.gnorm z2 : ℝ)
            = (Work.FIPlan.gnorm (z0 + (tfun z2 : GaussianInt) * z1) : ℝ) :=
          congrArg (fun w => (Work.FIPlan.gnorm w : ℝ)) (hP z2 hz2S)
        have hq : (Work.FIPlan.gnorm z2 : ℝ)
            = (Work.FIPlan.gnorm z1 : ℝ) * (tfun z2 : ℝ) ^ 2
              + 2 * ((z1.re * z0.re + z1.im * z0.im : ℤ) : ℝ) * (tfun z2 : ℝ)
              + (Work.FIPlan.gnorm z0 : ℝ) := hgn.trans (quad_norm z1 z0 (tfun z2))
        rw [← hq]
        exact hn2.2
      · have hgn : (Work.FIPlan.gnorm z2' : ℝ)
            = (Work.FIPlan.gnorm (z0 + (tfun z2' : GaussianInt) * z1) : ℝ) :=
          congrArg (fun w => (Work.FIPlan.gnorm w : ℝ)) (hP z2' hz2'S)
        have hq : (Work.FIPlan.gnorm z2' : ℝ)
            = (Work.FIPlan.gnorm z1 : ℝ) * (tfun z2' : ℝ) ^ 2
              + 2 * ((z1.re * z0.re + z1.im * z0.im : ℤ) : ℝ) * (tfun z2' : ℝ)
              + (Work.FIPlan.gnorm z0 : ℝ) := hgn.trans (quad_norm z1 z0 (tfun z2'))
        rw [← hq]
        exact hn2'.2
    exact_mod_cast le_trans hcard_le hT

end

end Work.FIArea6
