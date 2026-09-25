import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs
import Submission.Work.BourgainPlan.IonescuWainger.ArcFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.ZModArcs

/-!
# The Fourier coefficients of the torsion-arc symbol (Tao's `Op_{φ;α+Σ_{⊆A}}`)

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4
(Theorem `ortho-apply`(ii), the `ℓ^{2r}` estimate for the modulated multipliers
`Op_{φ; α + Σ_{⊆ A}}`); see `ARC_ARITH_STATUS.md`.

This file computes the *coefficients* of the (modulated) torsion-arc symbol.  If `φ` has Fourier
coefficients `K m = ∫ φ(ξ) conj (e^{2πi m ξ}) dξ` and `E = Σ_{⊆ A} = 𝕋[Q_A]` is the `Q_A`-torsion
subgroup of the circle, then the symbol `Σ_{β ∈ E} φ(· - (β + α))` has coefficients supported on
the multiples of `Q_A`, where they equal `conj (e^{2πi m α}) · Q_A · K m`.

The proof is the elementary one:

* the Haar measure of the circle is translation invariant, so the `(β+α)`-translate of `φ` has
  coefficients `conj (e^{2πi m (β + α)}) K m` (`kernelArc_fourierCoeff_arcTranslate`);
* the character `fourier m` is multiplicative in its argument, so
  `conj (e^{2πi m (β+α)}) = conj (e^{2πi m α}) · conj (e^{2πi m β})`;
* the character sum over the torsion subgroup `𝕋[Q_A]` is `Q_A` on the multiples of `Q_A` and `0`
  elsewhere (`kernelArc_charSum_sigmaSubAFinset`, proved from the geometric sum over the `Q_A`-th
  roots of unity).
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

open AddCircle

/-! ## Characters on the circle -/

/-- `fourier` is multiplicative in its *argument*. -/
private theorem kernelArc_fourier_add_arg (n : ℤ) (x y : Circle) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- A multiple of a point of the circle: `e^{2πi n (k • x)} = (e^{2πi n x})^k`. -/
private theorem kernelArc_fourier_nsmul_arg (n : ℤ) (x : Circle) (k : ℕ) :
    fourier n (k • x) = (fourier n x) ^ k := by
  induction k with
  | zero => simp
  | succ j ih => rw [succ_nsmul, kernelArc_fourier_add_arg, ih, pow_succ]

/-- `conj (e^{2πi m y}) = e^{-2πi m y}`. -/
private theorem kernelArc_star_fourier (m : ℤ) (y : Circle) :
    star (fourier m y) = fourier (-m) y := by
  rw [fourier_neg]; rfl

/-- The points `a/Q`, `a < Q`, are the multiples of `1/Q` in the circle. -/
private theorem kernelArc_arcPt_nsmul_one (Q : ℕ) (a : ℕ) :
    arcPt Q (a : ℤ) = a • arcPt Q 1 := by
  rw [arcPt, arcPt, ← QuotientAddGroup.mk_nsmul]
  congr 1
  push_cast
  ring

/-- The integer multiples of `1/Q` in the circle. -/
private theorem kernelArc_zsmul_arcPt_one (Q : ℕ) (k : ℤ) :
    k • arcPt Q 1 = arcPt Q k := by
  rw [zsmul_arcPt]
  congr 1
  ring

/-- **The character at a torsion point is the `a`-th power of the character at `1/Q`.** -/
theorem kernelArc_star_fourier_arcPt_pow (Q : ℕ) (m : ℤ) (a : ℕ) :
    star (fourier m (arcPt Q (a : ℤ))) = (star (fourier m (arcPt Q 1))) ^ a := by
  rw [kernelArc_star_fourier, kernelArc_arcPt_nsmul_one, kernelArc_fourier_nsmul_arg,
    ← kernelArc_star_fourier]

/-- `Q • (1/Q) = 0` in the circle. -/
private theorem kernelArc_nsmul_arcPt_one {Q : ℕ} (hQ : Q ≠ 0) : Q • arcPt Q 1 = 0 := by
  rw [← natCast_zsmul (arcPt Q 1) Q, zsmul_arcPt]
  have h : (((Q : ℤ) : ℝ) * ((1 : ℤ) : ℝ) / (Q : ℝ)) = ((1 : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [h]
  exact coe_int_circle_eq_zero 1

/-- **The character `e^{2πi m /Q}` is `1` exactly on the multiples of `Q`.** -/
theorem kernelArc_star_fourier_arcPt_one_eq_one_iff {Q : ℕ} (hQ : Q ≠ 0) (m : ℤ) :
    star (fourier m (arcPt Q 1)) = 1 ↔ (Q : ℤ) ∣ m := by
  have hinj := AddCircle.injective_toCircle (T := 1) (by norm_num : (1 : ℝ) ≠ 0)
  have h1 : star (fourier m (arcPt Q 1)) = 1 ↔ fourier m (arcPt Q 1) = 1 :=
    ⟨fun h => by simpa using congrArg star h, fun h => by rw [h]; simp⟩
  rw [h1, fourier_apply, kernelArc_zsmul_arcPt_one Q m]
  have hcoe : ((toCircle (arcPt Q m) : _root_.Circle) : ℂ) = 1 ↔ toCircle (arcPt Q m) = 1 := by
    constructor
    · intro h; exact Subtype.coe_injective (by simpa using h)
    · intro h; rw [h]; simp
  rw [hcoe, ← AddCircle.toCircle_zero (T := 1), hinj.eq_iff, arcPt_eq_zero_iff_dvd hQ m]

/-- The geometric sum over the `Q`-th roots of unity: if `ζ^Q = 1` then `Σ_{a<Q} ζ^a` is `Q` when
`ζ = 1` and `0` otherwise. -/
private theorem kernelArc_sum_pow_range (ζ : ℂ) (Q : ℕ) (hζQ : ζ ^ Q = 1) :
    ∑ a ∈ Finset.range Q, ζ ^ a = if ζ = 1 then (Q : ℂ) else 0 := by
  rcases eq_or_ne ζ 1 with h | h
  · subst h; simp
  · rw [if_neg h]
    have hgeom := geom_sum_mul ζ Q
    rw [hζQ, sub_self] at hgeom
    rcases mul_eq_zero.mp hgeom with h' | h'
    · exact h'
    · exact absurd h' (sub_ne_zero.mpr h)

/-! ## The character sum over the torsion subgroup -/

/-- **The character sum over `Σ_{⊆ A} = 𝕋[Q_A]`.**  Summing `star (fourier m ·)` over the
`Q_A`-torsion points of the circle gives `Q_A` when `Q_A ∣ m` and `0` otherwise. -/
theorem kernelArc_charSum_sigmaSubAFinset (A : Finset ℕ) (m : ℤ) :
    ∑ β ∈ sigmaSubAFinset A, star (fourier m β)
      = if (QA A : ℤ) ∣ m then (QA A : ℂ) else 0 := by
  rcases eq_or_ne (QA A) 0 with hQ0 | hQ
  · rw [hQ0]
    rw [show sigmaSubAFinset A = ∅ by simp [sigmaSubAFinset, hQ0], Finset.sum_empty]
    simp only [Nat.cast_zero]
    by_cases h : (0 : ℤ) ∣ m
    · rw [if_pos h]
    · rw [if_neg h]
  · have hinj : Set.InjOn (fun a : ℕ => arcPt (QA A) (a : ℤ)) ↑(Finset.range (QA A)) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_range] at ha hb
      have hdvd : ((QA A : ℕ) : ℤ) ∣ ((a : ℤ) - (b : ℤ)) :=
        (arcPt_eq_arcPt_iff_dvd hQ a b).mp hab
      have hlt : |((a : ℤ) - (b : ℤ))| < ((QA A : ℕ) : ℤ) := by
        rw [abs_lt]; constructor <;> omega
      have h0 : (a : ℤ) - (b : ℤ) = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
      omega
    rw [sigmaSubAFinset, Finset.sum_image hinj]
    have hζQ : (star (fourier m (arcPt (QA A) 1))) ^ (QA A) = 1 := by
      rw [← star_pow, ← kernelArc_fourier_nsmul_arg (n := m) (x := arcPt (QA A) 1)
        (k := QA A), kernelArc_nsmul_arcPt_one hQ]
      simp
    rw [Finset.sum_congr rfl (fun a _ => kernelArc_star_fourier_arcPt_pow (QA A) m a)]
    rw [kernelArc_sum_pow_range _ _ hζQ]
    by_cases h : star (fourier m (arcPt (QA A) 1)) = 1
    · rw [if_pos h, if_pos ((kernelArc_star_fourier_arcPt_one_eq_one_iff hQ m).mp h)]
    · rw [if_neg h,
        if_neg (fun hd => h ((kernelArc_star_fourier_arcPt_one_eq_one_iff hQ m).mpr hd))]

/-! ## The Fourier coefficients of a translate -/

/-- **The Fourier coefficients of a translate.**  Translating a circle function by `β` multiplies
its `m`-th Fourier coefficient by `star (fourier m β)`. -/
theorem kernelArc_fourierCoeff_arcTranslate (φ : Circle → ℂ) (β : Circle) (m : ℤ) :
    ∫ ξ, φ (ξ - β) * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1))
      = star (fourier m β) * ∫ ξ, φ ξ * star (fourier m ξ)
          ∂(AddCircle.haarAddCircle (T := 1)) := by
  have hpt : ∀ x : Circle, star (fourier m (x + β)) = star (fourier m x) * star (fourier m β) := by
    intro x
    rw [kernelArc_fourier_add_arg, star_mul, mul_comm]
  have hshift : ∫ ξ, φ (ξ - β) * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1))
      = ∫ η, φ η * star (fourier m (η + β)) ∂(AddCircle.haarAddCircle (T := 1)) := by
    have h := integral_add_right_eq_self (μ := AddCircle.haarAddCircle (T := 1))
      (fun ξ : Circle => φ (ξ - β) * star (fourier m ξ)) β
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards with ξ
    simp only [add_sub_cancel_right]
  rw [hshift]
  simp_rw [hpt]
  rw [show (fun η : Circle => φ η * (star (fourier m η) * star (fourier m β)))
      = fun η : Circle => (φ η * star (fourier m η)) * star (fourier m β) by
    funext η; ring]
  rw [integral_mul_const, mul_comm]

/-! ## Integrability of the summands -/

/-- The summands of the torsion-arc symbol are integrable: `φ` is a.e. bounded on the probability
space `𝕋`, and `star (fourier m ·)` has modulus `1`. -/
theorem kernelArc_integrable_translate_mul (φ : Circle → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) (c : Circle) (m : ℤ) :
    Integrable (fun ξ => φ (ξ - c) * star (fourier m ξ)) (AddCircle.haarAddCircle (T := 1)) := by
  have hmp : MeasurePreserving (fun ξ : Circle => ξ + (-c))
      (AddCircle.haarAddCircle (T := 1)) (AddCircle.haarAddCircle (T := 1)) :=
    measurePreserving_add_right _ (-c)
  have hφ' : MemLp (fun ξ : Circle => φ (ξ - c)) ⊤ (AddCircle.haarAddCircle (T := 1)) := by
    have h := hφ.comp_measurePreserving hmp
    have heq : (φ ∘ fun ξ : Circle => ξ + (-c)) = fun ξ : Circle => φ (ξ - c) := by
      funext ξ; simp [Function.comp, sub_eq_add_neg]
    rwa [heq] at h
  refine Integrable.congr (f := fun ξ : Circle => star (fourier m ξ) * φ (ξ - c)) ?_ ?_
  · refine Integrable.bdd_mul (f := fun ξ : Circle => star (fourier m ξ))
      (g := fun ξ : Circle => φ (ξ - c)) (c := 1) (hφ'.integrable le_top)
      (continuous_star.comp (fourier m).continuous).aestronglyMeasurable ?_
    filter_upwards with ξ
    rw [norm_star, norm_fourier_apply']
  · filter_upwards with ξ
    ring

/-! ## The main computation -/

/-- **The Fourier coefficients of the torsion-arc symbol.**  If `K` is the sequence of Fourier
coefficients of `φ`, then the coefficients of the symbol `Σ_{β ∈ 𝕋[Q_A]} φ(· - (β + α))` (Tao's
`Op_{φ;α+Σ_{⊆ A}}`) are supported on the multiples of `Q_A`, where they equal
`star (fourier m α) · Q_A · K m`. -/
theorem kernel_arcSymbol_torsion {A : Finset ℕ} (α : Circle) (φ : Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {K : ℤ → ℂ}
    (hK : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    (m : ℤ) :
    ∫ ξ, arcSymbol φ (arcShift (sigmaSubAFinset A) α) ξ * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1))
      = star (fourier m α) * (if (QA A : ℤ) ∣ m then (QA A : ℂ) else 0) * K m := by
  rw [arcSymbol_arcShift]
  have hdist : ∀ ξ : Circle, (∑ β ∈ sigmaSubAFinset A, φ (ξ - (β + α))) * star (fourier m ξ)
      = ∑ β ∈ sigmaSubAFinset A, φ (ξ - (β + α)) * star (fourier m ξ) :=
    fun ξ => Finset.sum_mul ..
  simp_rw [hdist]
  rw [integral_finsetSum (s := sigmaSubAFinset A) (f := fun β ξ =>
    φ (ξ - (β + α)) * star (fourier m ξ))
    (fun β _ => kernelArc_integrable_translate_mul φ hφ (β + α) m)]
  have hterm : ∀ β ∈ sigmaSubAFinset A,
      ∫ ξ, φ (ξ - (β + α)) * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1))
        = star (fourier m α) * star (fourier m β) * K m := by
    intro β _
    rw [kernelArc_fourierCoeff_arcTranslate φ (β + α) m, hK m, kernelArc_fourier_add_arg,
      star_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.mul_sum,
    kernelArc_charSum_sigmaSubAFinset A m]

end

end Work.BourgainPlan.IonescuWainger
