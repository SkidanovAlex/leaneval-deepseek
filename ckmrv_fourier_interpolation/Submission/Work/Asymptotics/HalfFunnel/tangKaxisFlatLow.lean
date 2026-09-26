import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs
import Submission.Work.Asymptotics.HalfFunnel.tangOrbitRectCl
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.Asymptotics.HalfFunnel.exists_bound_Kfun_off_coincidence
import Submission.Work.Asymptotics.HalfFunnel.tangOrbitHeight
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

namespace Work.Asymptotics.HalfFunnel

open UpperHalfPlane

noncomputable section

/-! ## The contour point `t ↦ i t`

We record the point `i t` as a *total* function of `t` so that the set of contour points over
an interval is the continuous image of a compact interval. -/

/-- The contour point `i t`; its value off `t > 0` is irrelevant. -/
def ctFun (t : ℝ) : ℍ := UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))

lemma continuousOn_ctFun : ContinuousOn ctFun (Set.Ioi 0) :=
  UpperHalfPlane.continuousOn_ofComplex_I_mul

lemma ctFun_eq_imagAxis {t : ℝ} (ht : 0 < t) : ctFun t = Work.Kernels.imagAxis t ht := by
  apply UpperHalfPlane.ext
  rw [ctFun, UpperHalfPlane.ofComplex_apply_of_im_pos (z := Complex.I * (t : ℂ))
    (by simpa [Complex.mul_im] using ht)]
  show Complex.I * (t : ℂ) = ((Work.Kernels.imagAxis t ht : ℍ) : ℂ)
  rw [Work.Kernels.imagAxis]
  exact mul_comm Complex.I (t : ℂ)

/-! ## The `j`-invariant separates `ctanCl` from the contour below height `1/2` -/

/-- **No point of `ctanCl` is `SL(2,ℤ)`-equivalent to a contour point `i t` with
`0 < t ≤ 1/2`.**  Equivalently, the `j`-invariant separates the closed tangency region from the
low part of the contour: this is what makes the middle-range kernel estimate available on
`ctanCl × [δ, 1/2]`.

Proof: if `γ • (i t) = τ` with `γ = !![a,b;c,d]`, the imaginary part of the Möbius relation
reads `τ.im (d² + (c t)²) = t`.  If `d = 0` then `c = ±1` (from the determinant) and `τ.im = 1/t ≥ 2`,
contradicting `τ.im ≤ 5/8`.  If `d ≠ 0`, then `τ.im d² ≤ t ≤ 1/2 ≤ τ.im`, forcing `d² = 1`,
`τ.im = t = 1/2` and `c = 0`; then `τ.re = b d` is an integer, contradicting
`3/8 ≤ |τ.re| ≤ 5/8`. -/
lemma jInvariantFun_ne_imagAxis_of_mem_ctanCl_le_half {τ : ℍ} (hτ : τ ∈ ctanCl) {t : ℝ}
    (ht : 0 < t) (ht2 : t ≤ 1 / 2) :
    Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro hj
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hj
  have hcoe : ((γ • Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (τ : ℂ) := by rw [hγ]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at hcoe
  have hcast : ∀ m : ℤ, ((algebraMap ℤ ℝ m : ℂ)) = (m : ℂ) := fun m => by simp
  simp only [hcast] at hcoe
  have hw : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  rw [hw] at hcoe
  -- the denominator does not vanish
  have hden : ((γ 1 0 : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im,
      mul_zero, sub_zero, zero_mul, add_zero, mul_one] at hre him
    have h11 : γ 1 1 = 0 := by
      have hh : ((γ 1 1 : ℤ) : ℝ) = 0 := by simpa using hre
      exact_mod_cast hh
    have h10 : γ 1 0 = 0 := by
      have ht0 : (t : ℝ) ≠ 0 := ne_of_gt ht
      have hh : ((γ 1 0 : ℤ) : ℝ) * t = 0 := by simpa using him
      have : ((γ 1 0 : ℤ) : ℝ) = 0 := (mul_eq_zero.mp hh).resolve_right ht0
      exact_mod_cast this
    have hdet := γ.2
    rw [Matrix.det_fin_two] at hdet
    rw [h10, h11] at hdet
    norm_num at hdet
  have hmain : ((γ 0 0 : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((γ 0 1 : ℤ) : ℂ) =
      (τ : ℂ) * (((γ 1 0 : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((γ 1 1 : ℤ) : ℂ)) :=
    (div_eq_iff hden).mp hcoe
  have hre : (γ 0 1 : ℝ) = τ.re * (γ 1 1 : ℝ) - τ.im * ((γ 1 0 : ℝ) * t) := by
    have h := congrArg Complex.re hmain
    simp at h
    linarith [h]
  have him : (γ 0 0 : ℝ) * t = τ.re * ((γ 1 0 : ℝ) * t) + τ.im * (γ 1 1 : ℝ) := by
    have h := congrArg Complex.im hmain
    simp at h
    linarith [h]
  have hdetZ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have hh := γ.2
    rwa [Matrix.det_fin_two] at hh
  have hdetR : (γ 0 0 : ℝ) * (γ 1 1 : ℝ) - (γ 0 1 : ℝ) * (γ 1 0 : ℝ) = 1 := by
    exact_mod_cast hdetZ
  -- the key relation
  have hkey : τ.im * ((γ 1 1 : ℝ) ^ 2 + ((γ 1 0 : ℝ) * t) ^ 2) = t := by
    linear_combination -(γ 1 1 : ℝ) * him + ((γ 1 0 : ℝ) * t) * hre + t * hdetR
  obtain ⟨hY1, hY2⟩ := ctanCl_im_bounds τ hτ
  obtain ⟨hX1, hX2⟩ := ctanCl_abs_re_bounds τ hτ
  rcases eq_or_ne (γ 1 1) 0 with hd0 | hdne
  · -- `d = 0`
    have hbc : γ 0 1 * γ 1 0 = -1 := by
      rw [hd0] at hdetZ
      omega
    have hc : γ 1 0 = 1 ∨ γ 1 0 = -1 :=
      Int.eq_one_or_neg_one_of_mul_eq_neg_one' hbc |>.elim
        (fun h => Or.inr h.2) (fun h => Or.inl h.2)
    have hc2 : ((γ 1 0 : ℝ)) ^ 2 = 1 := by
      rcases hc with h | h <;> rw [h] <;> norm_num
    have himt : τ.im * t = 1 := by
      have h := hkey
      rw [hd0] at h
      push_cast at h
      have h2 : τ.im * ((γ 1 0 : ℝ) ^ 2 * t ^ 2) = t := by linear_combination h
      rw [hc2, one_mul] at h2
      have ht0 : t ≠ 0 := ne_of_gt ht
      field_simp at h2 ⊢
      linarith [h2]
    have : τ.im * t ≤ (5 / 8 : ℝ) * (1 / 2) :=
      mul_le_mul hY2 ht2 ht.le (by norm_num)
    linarith
  · -- `d ≠ 0`
    have hd2ge : (1 : ℝ) ≤ (γ 1 1 : ℝ) ^ 2 := by
      have hge : (1 : ℝ) ≤ |(γ 1 1 : ℝ)| := by
        have h : (1 : ℤ) ≤ |γ 1 1| := Int.one_le_abs hdne
        exact_mod_cast h
      nlinarith [hge, abs_nonneg (γ 1 1 : ℝ), sq_abs (γ 1 1 : ℝ)]
    have hkey' : τ.im * (γ 1 1 : ℝ) ^ 2 ≤ t := by
      have hnonneg : 0 ≤ τ.im * ((γ 1 0 : ℝ) * t) ^ 2 :=
        mul_nonneg (le_of_lt τ.im_pos) (sq_nonneg _)
      nlinarith [hkey]
    have htle : t ≤ 1 / 2 := ht2
    have hY1' : (1 : ℝ) / 2 ≤ τ.im := hY1
    have hd2le : (γ 1 1 : ℝ) ^ 2 ≤ 1 := by
      nlinarith [hkey', hY1', htle, sq_nonneg (γ 1 1 : ℝ)]
    have hd2 : (γ 1 1 : ℝ) ^ 2 = 1 := le_antisymm hd2le hd2ge
    have him_eq : τ.im = 1 / 2 ∧ t = 1 / 2 := by
      constructor <;> nlinarith [hkey', hY1', htle, hd2, ht]
    have hc0R : (γ 1 0 : ℝ) = 0 := by
      have h := hkey
      rw [hd2, him_eq.1, him_eq.2] at h
      nlinarith [sq_nonneg ((γ 1 0 : ℝ) * (1 / 2 : ℝ))]
    have hc0 : γ 1 0 = 0 := by exact_mod_cast hc0R
    have hreI : ∃ n : ℤ, τ.re = n := by
      refine ⟨γ 0 1 * γ 1 1, ?_⟩
      have h := hre
      rw [hc0] at h
      have h' : (γ 0 1 : ℝ) = τ.re * (γ 1 1 : ℝ) := by simpa using h
      have : τ.re = (γ 0 1 : ℝ) * (γ 1 1 : ℝ) := by
        have hmul : τ.re * (γ 1 1 : ℝ) * (γ 1 1 : ℝ) = (γ 0 1 : ℝ) * (γ 1 1 : ℝ) := by
          rw [← h']
        have h1 : τ.re * (γ 1 1 : ℝ) * (γ 1 1 : ℝ) = τ.re := by
          rw [show τ.re * (γ 1 1 : ℝ) * (γ 1 1 : ℝ) = τ.re * ((γ 1 1 : ℝ) ^ 2) by ring,
            hd2, mul_one]
        rw [h1] at hmul
        exact hmul
      rw [this]
      push_cast
      ring
    obtain ⟨n, hn⟩ := hreI
    have habs : 3 / 8 ≤ |(n : ℝ)| := by
      have := hX1
      rw [hn] at this
      exact this
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0] at habs
      norm_num at habs
    have h1n : (1 : ℝ) ≤ |(n : ℝ)| := by
      have := Int.one_le_abs hn0
      exact_mod_cast this
    have hub : |(n : ℝ)| ≤ 5 / 8 := by
      have := hX2
      rw [hn] at this
      exact this
    linarith

/-! ## The flatness of the kernel at the cusp on `ctanCl` -/

theorem tangKaxisFlatLow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.HalfFunnel.ctanCl → 0 < t → t ≤ 1 / 2 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N := by
  intro N hN
  obtain ⟨δ, hδpos, hcusp⟩ := Kaxis_cusp_of_bounded ℓ d hd isBounded_ctanCl
  obtain ⟨cuspC, hcuspCpos, hcuspB⟩ := hcusp N hN
  set T : Set ℍ := ctFun '' Set.Icc δ (1 / 2) with hT
  have hTcompact : IsCompact T :=
    isCompact_Icc.image_of_continuousOn (continuousOn_ctFun.mono (by
      intro s hs
      exact lt_of_lt_of_le hδpos hs.1))
  have hsep : ∀ (τ : ℍ), τ ∈ ctanCl → ∀ (z : ℍ), z ∈ T →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    rintro τ hτ z ⟨s, hs, rfl⟩
    have hspos : 0 < s := lt_of_lt_of_le hδpos hs.1
    rw [ctFun_eq_imagAxis hspos]
    exact jInvariantFun_ne_imagAxis_of_mem_ctanCl_le_half hτ hspos hs.2
  obtain ⟨CK, hCKpos, hCK⟩ :=
    exists_bound_Kfun_off_coincidence ℓ d hd isCompact_ctanCl hTcompact hsep
  refine ⟨max cuspC (CK * δ ^ (-N)), lt_of_lt_of_le hcuspCpos (le_max_left _ _), ?_⟩
  intro τ t hτ ht ht2
  have hpow : δ ^ (-N) * δ ^ N = 1 := by
    rw [← Real.rpow_add hδpos (-N) N, show -N + N = 0 from by ring, Real.rpow_zero]
  have htNnonneg : (0 : ℝ) ≤ t ^ N := Real.rpow_nonneg ht.le N
  by_cases hle : t ≤ δ
  · have h := hcuspB τ t hτ ht hle
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ cuspC * t ^ N := h
      _ ≤ max cuspC (CK * δ ^ (-N)) * t ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) htNnonneg
  · have hlt : δ < t := not_le.mp hle
    have hz : Work.Kernels.imagAxis t ht ∈ T :=
      ⟨t, ⟨le_of_lt hlt, ht2⟩, ctFun_eq_imagAxis ht⟩
    have hK : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ CK := by
      rw [Work.Kernels.Kaxis, dif_pos ht]
      exact hCK τ hτ (Work.Kernels.imagAxis t ht) hz
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ CK := hK
      _ = CK * δ ^ (-N) * δ ^ N := by rw [mul_assoc, hpow, mul_one]
      _ ≤ CK * δ ^ (-N) * t ^ N := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow hδpos.le (le_of_lt hlt) hN
      _ ≤ max cuspC (CK * δ ^ (-N)) * t ^ N :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) htNnonneg

end

end Work.Asymptotics.HalfFunnel
