import Mathlib
import Submission.Work.Asymptotics.contourLeftDefs
import Submission.Work.Asymptotics.exists_jprime_lower_near_imagAxis
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Asymptotics.euclid_near_imagAxis_of_hyperbolic_ball

namespace Work.Asymptotics

open UpperHalfPlane

/-! ## Non-vanishing of `E₄` and `E₆` near the elliptic point `i`

The translate pole `z = τ - 1` of the CKMRV kernel is `j'`-non-degenerate unless it hits an
elliptic point.  When `s₀ = 1` the centre of the ball maps to `i`, where `j'` does vanish
(`E₆(i) = 0`), so the argument has to exclude the whole orbit of `i` off the real part `1`.
-/

/-- `S` fixes `i`, hence (weight-`6` automorphy of `E₆`) `E₆(i) = 0`. -/
private lemma E6Fun_I_eq_zero : Work.Kernels.E6Fun UpperHalfPlane.I = 0 := by
  have hS : ModularGroup.S • (UpperHalfPlane.I : UpperHalfPlane) = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_S_smul]
    change (-(UpperHalfPlane.I : ℂ))⁻¹ = (UpperHalfPlane.I : ℂ)
    rw [UpperHalfPlane.coe_I]
    rw [show (-(Complex.I) : ℂ)⁻¹ = Complex.I by rw [inv_neg, Complex.inv_I]; ring]
  have h := Work.Residues.E6Fun_S_smul UpperHalfPlane.I
  rw [hS] at h
  have hI6 : (UpperHalfPlane.I : ℂ) ^ 6 = -1 := by
    rw [UpperHalfPlane.coe_I, show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Complex.I_sq]
    norm_num
  rw [hI6, neg_one_mul] at h
  have h2 : (2 : ℂ) * Work.Kernels.E6Fun UpperHalfPlane.I = 0 := by linear_combination h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- If `E₆` vanishes at `z` then `j z = 1728`. -/
private lemma jInvariantFun_eq_1728_of_E6Fun_eq_zero {z : UpperHalfPlane}
    (h : Work.Kernels.E6Fun z = 0) : Work.Kernels.jInvariantFun z = 1728 := by
  have h1 : Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun z = Work.Kernels.E4Fun z ^ 3 :=
    Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z
  have h2 : (1728 : ℂ) * Work.Kernels.DeltaFun z
      = Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E6Fun z ^ 2 :=
    Work.Residues.KMinusClearTS.disc_eq z
  have h3 : Work.Kernels.E4Fun z ^ 3 = 1728 * Work.Kernels.DeltaFun z := by rw [h2, h]; ring
  have hD : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  rw [h3] at h1
  exact mul_left_cancel₀ hD (by rw [h1]; ring)

/-- `E₄(i) ≠ 0`, from `E₆(i) = 0`, `Δ(i) ≠ 0` and `1728Δ = E₄³ - E₆²`. -/
private lemma E4Fun_I_ne_zero : Work.Kernels.E4Fun UpperHalfPlane.I ≠ 0 := by
  have h2 : (1728 : ℂ) * Work.Kernels.DeltaFun UpperHalfPlane.I
      = Work.Kernels.E4Fun UpperHalfPlane.I ^ 3 - Work.Kernels.E6Fun UpperHalfPlane.I ^ 2 :=
    Work.Residues.KMinusClearTS.disc_eq _
  have hcube : Work.Kernels.E4Fun UpperHalfPlane.I ^ 3
      = 1728 * Work.Kernels.DeltaFun UpperHalfPlane.I := by rw [h2, E6Fun_I_eq_zero]; ring
  intro h4
  rw [h4] at hcube
  have : (1728 : ℂ) * Work.Kernels.DeltaFun UpperHalfPlane.I = 0 := by rw [← hcube]; norm_num
  exact Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _
    ((mul_eq_zero.mp this).resolve_left (by norm_num))

/-- `E₄` is non-zero on a Euclidean neighbourhood of `i` (continuity). -/
private lemma exists_E4Fun_ne_zero_near_I :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ζ : UpperHalfPlane,
      ‖(ζ : ℂ) - Complex.I‖ < δ → Work.Kernels.E4Fun ζ ≠ 0 := by
  have hcont : Continuous (Work.Kernels.E4Fun) :=
    MDifferentiable.continuous (ModularFormClass.holo ModularForm.E₄)
  have hopen : IsOpen {ζ : UpperHalfPlane | Work.Kernels.E4Fun ζ ≠ 0} := by
    show IsOpen (Work.Kernels.E4Fun ⁻¹' {0}ᶜ)
    exact IsOpen.preimage hcont isOpen_compl_singleton
  obtain ⟨U, hUopen, hUeq⟩ := isOpen_induced_iff.mp hopen
  have hiU : (UpperHalfPlane.I : ℂ) ∈ U := by
    have : UpperHalfPlane.I ∈ UpperHalfPlane.coe ⁻¹' U := by rw [hUeq]; exact E4Fun_I_ne_zero
    exact this
  obtain ⟨δ, hδpos, hball⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hiU)
  refine ⟨δ, hδpos, fun ζ hζ => ?_⟩
  have hmemU : (ζ : ℂ) ∈ U := hball (by
    rw [Metric.mem_ball, Complex.dist_eq, UpperHalfPlane.coe_I]
    exact hζ)
  have : ζ ∈ {ζ : UpperHalfPlane | Work.Kernels.E4Fun ζ ≠ 0} := by
    rw [← hUeq]
    exact hmemU
  exact this

/-- **`E₆` does not vanish just to the left of the elliptic point `i`.**  The zeros of `E₆` are
the `SL(2,ℤ)`-orbit of `i`; on the half-strip `-1 < Re < 0` close to `i` this orbit is empty. -/
private lemma E6Fun_ne_zero_left_near_I :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ζ : UpperHalfPlane,
      ‖(ζ : ℂ) - Complex.I‖ < δ → -1 < ζ.re → ζ.re < 0 →
        Work.Kernels.E6Fun ζ ≠ 0 := by
  refine ⟨1 / 2, by norm_num, fun ζ hζ hgt hlt hE6 => ?_⟩
  have hjz : Work.Kernels.jInvariantFun ζ = 1728 := jInvariantFun_eq_1728_of_E6Fun_eq_zero hE6
  have hjI : Work.Kernels.jInvariantFun UpperHalfPlane.I = 1728 :=
    jInvariantFun_eq_1728_of_E6Fun_eq_zero E6Fun_I_eq_zero
  obtain ⟨γ, hγ⟩ := jInvariantFun_eq_smul_of_eq (show
    Work.Kernels.jInvariantFun ζ = Work.Kernels.jInvariantFun UpperHalfPlane.I by
      rw [hjz, hjI])
  have h01 : (0 : ℝ) < 1 := by norm_num
  have hIeq : Work.Kernels.imagAxis 1 h01 = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_I]
    simp [Work.Kernels.imagAxis]
  rw [← hIeq] at hγ
  obtain ⟨him, hre⟩ := web_re_im γ 1 h01
  rw [hγ] at him hre
  set D : ℝ := ((γ 1 0 : ℤ) : ℝ) ^ 2 * 1 ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2 with hD
  -- imaginary part of `ζ`
  have him_bd : |(ζ : ℂ).im - 1| < 1 / 2 := by
    have h := Complex.abs_im_le_norm ((ζ : ℂ) - Complex.I)
    rw [Complex.sub_im, Complex.I_im] at h
    linarith
  have him_gt : 1 / 2 < (ζ : ℂ).im := by
    have := (abs_lt.mp him_bd).1
    linarith
  have hDinv_gt : 1 / 2 < 1 / D := by rw [← him]; exact him_gt
  have hDcast : D = (((γ 1 0 : ℤ) ^ 2 + (γ 1 1 : ℤ) ^ 2 : ℤ) : ℝ) := by
    rw [hD]; push_cast; ring
  have hDpos : (0 : ℝ) < D := by
    have : (0 : ℝ) < 1 / D := by linarith
    exact one_div_pos.mp this
  have hDlt2 : D < 2 := by
    have h := mul_lt_mul_of_pos_left hDinv_gt hDpos
    have h2 : D * (1 / D) = 1 := by rw [mul_one_div, div_self (ne_of_gt hDpos)]
    rw [h2] at h
    linarith
  have hDz : (γ 1 0 : ℤ) ^ 2 + (γ 1 1 : ℤ) ^ 2 = 1 := by
    have hDzpos : (0 : ℤ) < (γ 1 0 : ℤ) ^ 2 + (γ 1 1 : ℤ) ^ 2 := by
      have : (0 : ℝ) < (((γ 1 0 : ℤ) ^ 2 + (γ 1 1 : ℤ) ^ 2 : ℤ) : ℝ) := by
        rw [← hDcast]; exact hDpos
      exact_mod_cast this
    have h3 : (((γ 1 0 : ℤ) ^ 2 + (γ 1 1 : ℤ) ^ 2 : ℤ) : ℝ) < 2 := by
      rw [← hDcast]; exact hDlt2
    have h3' : (γ 1 0 : ℤ) ^ 2 + (γ 1 1 : ℤ) ^ 2 < 2 := by exact_mod_cast h3
    omega
  have hD_eq_one : D = 1 := by rw [hDcast, hDz]; norm_num
  -- real part of `ζ`
  have hre' : (ζ : ℂ).re =
      ((((γ 0 0 : ℤ) : ℝ) - ((γ 1 0 : ℤ) : ℝ)) * ((γ 1 0 : ℤ) : ℝ) * 1 ^ 2
        + (((γ 0 1 : ℤ) : ℝ) - ((γ 1 1 : ℤ) : ℝ)) * ((γ 1 1 : ℤ) : ℝ)) / D + 1 := by
    rw [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hre_int : ζ.re = ((γ 0 0 * γ 1 0 + γ 0 1 * γ 1 1 : ℤ) : ℝ) := by
    rw [← UpperHalfPlane.coe_re, hre', hD_eq_one, div_one]
    have hA : ((((γ 0 0 : ℤ) : ℝ) - ((γ 1 0 : ℤ) : ℝ)) * ((γ 1 0 : ℤ) : ℝ) * 1 ^ 2
        + (((γ 0 1 : ℤ) : ℝ) - ((γ 1 1 : ℤ) : ℝ)) * ((γ 1 1 : ℤ) : ℝ))
        = (((γ 0 0 * γ 1 0 + γ 0 1 * γ 1 1 : ℤ) : ℝ)
            - (((γ 1 0 : ℤ) ^ 2 + (γ 1 1 : ℤ) ^ 2 : ℤ) : ℝ)) := by push_cast; ring
    rw [hA, hDz]; ring
  have hA_int : (-1 : ℤ) < γ 0 0 * γ 1 0 + γ 0 1 * γ 1 1 := by
    have := hgt; rw [hre_int] at this; exact_mod_cast this
  have hA_neg : γ 0 0 * γ 1 0 + γ 0 1 * γ 1 1 < 0 := by
    have := hlt; rw [hre_int] at this; exact_mod_cast this
  omega

/-! ## The two regimes of `s₀` -/

/-- **`s₀ ≠ 1`.**  The centre `i s₀` of the translated ball is not an elliptic point, so `j'` is
bounded away from `0` on a Euclidean ball around it (`exists_jprime_lower_near_imagAxis`), and
the hyperbolic ball is contained in that Euclidean ball for small enough radius
(`euclid_near_imagAxis_of_hyperbolic_ball`). -/
private lemma jprime_tauSubOne_ne_zero_of_ne_one (s₀ : ℝ) (hs₀ : 0 < s₀) (hne : s₀ ≠ 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ τ : UpperHalfPlane,
      dist τ (onePlusI s₀ hs₀) < ε₀ → Work.Residues.jprime (tauSubOne τ) ≠ 0 := by
  obtain ⟨η, c, hη, hc, hb⟩ := exists_jprime_lower_near_imagAxis hs₀ hne
  obtain ⟨ε₀, hε₀, hball⟩ := euclid_near_imagAxis_of_hyperbolic_ball s₀ hs₀ η hη
  refine ⟨ε₀, hε₀, fun τ hτ => ?_⟩
  have h1 : ‖(tauSubOne τ : ℂ) - Complex.I * (s₀ : ℂ)‖ < η := by
    rw [mul_comm]; exact hball τ hτ
  have h2 : c ≤ ‖Work.Residues.jprime (tauSubOne τ)‖ := hb (tauSubOne τ) h1
  intro h0
  rw [h0, norm_zero] at h2
  linarith

/-- **`s₀ = 1`.**  The translate `τ - 1` lies near the elliptic point `i`, but strictly to its
left.  On that half-strip near `i` neither factor of `j' = -2πiE₄²E₆/Δ` vanishes:
`E₄ ≠ 0` by continuity and `E₆ ≠ 0` because the zeros of `E₆` are the `SL(2,ℤ)`-orbit of `i`. -/
private lemma jprime_tauSubOne_ne_zero_at_one (hs1 : (0 : ℝ) < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ τ : UpperHalfPlane,
      dist τ (onePlusI 1 hs1) < ε₀ → τ.re < 1 →
        Work.Residues.jprime (tauSubOne τ) ≠ 0 := by
  obtain ⟨δ₆, hδ₆, hE6⟩ := E6Fun_ne_zero_left_near_I
  obtain ⟨δ₄, hδ₄, hE4⟩ := exists_E4Fun_ne_zero_near_I
  have hcenter : onePlusI 1 hs1 = onePlusI 1 (by norm_num : (0 : ℝ) < 1) := by
    apply UpperHalfPlane.ext
    simp [onePlusI]
  have hη : 0 < min δ₆ (min δ₄ 1) := lt_min hδ₆ (lt_min hδ₄ one_pos)
  obtain ⟨ε₀, hε₀, hball⟩ :=
    euclid_near_imagAxis_of_hyperbolic_ball 1 (by norm_num : (0 : ℝ) < 1)
      (min δ₆ (min δ₄ 1)) hη
  refine ⟨ε₀, hε₀, fun τ hτ hre => ?_⟩
  have hτ' : dist τ (onePlusI 1 (by norm_num : (0 : ℝ) < 1)) < ε₀ := by
    rw [← hcenter]; exact hτ
  have hz : ‖(tauSubOne τ : ℂ) - Complex.I‖ < min δ₆ (min δ₄ 1) := by
    have h := hball τ hτ'
    simpa only [Complex.ofReal_one, one_mul] using h
  have hreζ : (tauSubOne τ).re = τ.re - 1 := by
    rw [← UpperHalfPlane.coe_re, tauSubOne_coe]
    simp
  have hlt0 : (tauSubOne τ).re < 0 := by rw [hreζ]; linarith
  have hgt1 : -1 < (tauSubOne τ).re := by
    have hb : |(tauSubOne τ).re| ≤ ‖(tauSubOne τ : ℂ) - Complex.I‖ := by
      have h := Complex.abs_re_le_norm ((tauSubOne τ : ℂ) - Complex.I)
      rw [Complex.sub_re, Complex.I_re, sub_zero] at h
      rwa [UpperHalfPlane.coe_re] at h
    have h2 : |(tauSubOne τ).re| < 1 := by
      have h3 : |(tauSubOne τ).re| < min δ₆ (min δ₄ 1) := lt_of_le_of_lt hb hz
      have h4 : min δ₆ (min δ₄ 1) ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
    exact (abs_lt.mp h2).1
  have hzδ₄ : ‖(tauSubOne τ : ℂ) - Complex.I‖ < δ₄ :=
    lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
  have hzδ₆ : ‖(tauSubOne τ : ℂ) - Complex.I‖ < δ₆ := lt_of_lt_of_le hz (min_le_left _ _)
  have hp : Work.Kernels.E4Fun (tauSubOne τ) * Work.Kernels.E6Fun (tauSubOne τ) ≠ 0 :=
    mul_ne_zero (hE4 _ hzδ₄) (hE6 _ hzδ₆ hgt1 hlt0)
  exact (Work.Residues.jprime_ne_zero_iff (tauSubOne τ)).mpr hp

/-! ## The statement -/

/-- **`j'` does not vanish at the translate pole `τ - 1`.**  A hyperbolic ball around `1 + i s₀`
such that for every `τ` in it with `Re τ < 1` the derivative `j'(τ-1)` is nonzero (equivalently
`E₄(τ-1)·E₆(τ-1) ≠ 0`, by `Work.Residues.jprime_ne_zero_iff`).  This is the non-degeneracy which
makes `τ - 1` a *simple* pole of `z ↦ K(τ,z)`, and hence makes the residue at the pole the finite
limit `1/(2π)`. -/
theorem jprime_tauSubOne_ne_zero (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ τ : UpperHalfPlane,
      dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε₀ → τ.re < 1 →
        Work.Residues.jprime (Work.Asymptotics.tauSubOne τ) ≠ 0 := by
  by_cases h : s₀ = 1
  · subst h
    exact jprime_tauSubOne_ne_zero_at_one hs₀
  · obtain ⟨ε₀, hε₀, hb⟩ := jprime_tauSubOne_ne_zero_of_ne_one s₀ hs₀ h
    exact ⟨ε₀, hε₀, fun τ hτ _ => hb τ hτ⟩

end Work.Asymptotics
