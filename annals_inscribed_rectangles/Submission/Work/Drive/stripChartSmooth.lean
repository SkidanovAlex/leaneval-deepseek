import Mathlib
import Submission.Work.Drive.contMDiffAt_cappingSpace_configPiece
import Submission.Work.Drive.contDiffOn_chordUnitDir
import Submission.Work.Drive.stripConfigInterface
import Submission.Work.Configuration

/-!
# The configuration strip of a smooth plane curve is a smooth chart of the capping space

Hugelmeyer's capping (`Submission/Work/Drive/CAPPING_ANALYSIS.md`) presents the configuration Möbius
strip `M` of a smooth plane curve `γ` inside the glued space `CappingSpace`.  The chain route of the
total-order chapter needs the strip as a **smooth** chain: the parity engine is stated for `C^∞` maps.

The obstruction (recorded in `CAPPING_ANALYSIS.md` §2) is that the capping coordinate of the
configuration piece is the *doubled* chord direction `η = dirC (γ x - γ y)`, while the chart of
`LensSpace ≅ ℝP³` needs a **square root** of `circleOf η` — a smooth halving of the `S¹`-coordinate,
which is not a function of `η` alone.  For the strip the halving is available from the curve: the
*undoubled* chord direction `Work.Drive.chordUnitDir γ` (`= (γ x - γ y)/‖γ x - γ y‖`, smooth off the
diagonal, `Work.Drive.contDiffOn_chordUnitDir`).

## Content

* `Work.Drive.stripData`, `stripMid`, `stripChord`, `stripA`, `stripR`, `stripD`, `stripHalf` — the
  configuration data of the chord with parameters `(w 0, w 1)` in the capping coordinates, together
  with the explicit formulas `(confOf (muOrd γ _)).1 = stripR γ w` and
  `(confOf (muOrd γ _)).2.1 = stripD γ w` that make the two coordinate functions smooth;
* `Work.Drive.stripHalf_norm`, `circOf_stripHalf_sq` — the halving `stripHalf γ w` of the doubled
  direction: `‖stripHalf γ w‖ = 1` and `circOf (stripHalf γ w ^ 2) = (stripData γ w).2.2`;
* `Work.Drive.circOf_mul`, `circOf_circleOf` — the multiplicativity of `circOf` on the unit circle
  (the group isomorphism `S¹ ≅ ℝ/ℤ`), used to shift the direction by the rotation parameter `v`;
* `Work.Drive.stripChart` — the strip of `γ` (rotated by `v`) as a map into `CappingSpace`;
* **`Work.Drive.contMDiffOn_stripChart`** — it is `C^∞` (for the transparent smooth structure
  `Work.Drive.cappingCharted`) on the open set where the two parameters are distinct.

The last statement is the *strip half* of "the disk presentation of the capped plane is smooth on the
interior".
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology
open Classical
open Submission.Configuration Submission.Geometry Submission.Collision

noncomputable section

variable {γ : Circle → ℝ × ℝ}

/-! ## 1. The configuration data of a chord in capping coordinates -/

/-- The capping coordinates `(r, d, η)` of the configuration point of the chord with parameters
`(w 0, w 1)`: the radial coordinate `r = ‖(midpoint, length)‖`, the normalised midpoint/length vector
`d` in the closed unit disk, and the doubled chord direction `η = dirC (γ (exp (w 0)) - γ (exp (w 1)))`
of the configuration piece. -/
def stripData (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℝ × ℂ × UnitAddCircle :=
  confOf (muOrd γ (Circle.exp (w 0), Circle.exp (w 1)))

/-- The midpoint of the chord with parameters `(w 0, w 1)`. -/
def stripMid (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ :=
  (γ (Circle.exp (w 0)) + γ (Circle.exp (w 1))) / 2

/-- The chord with parameters `(w 0, w 1)` read as a complex number, so that `‖·‖` is the Euclidean
norm of the chord (see `Work.Drive.chordC`). -/
def stripChord (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  chordC γ (w 0, w 1)

/-- The square of the capping radius: `midpoint.1 ^ 2 + midpoint.2 ^ 2 + length ^ 2`. -/
def stripA (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (stripMid γ w).1 ^ 2 + (stripMid γ w).2 ^ 2 + Complex.normSq (stripChord γ w)

/-- The capping radius of the chord. -/
def stripR (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.sqrt (stripA γ w)

/-- The disk coordinate of the configuration piece of the chord, in complex form. -/
def stripD (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (((stripMid γ w).1 : ℂ) + ((stripMid γ w).2 : ℂ) * Complex.I) / (((stripR γ w : ℝ)) : ℂ)

/-- `(a + a) / 2 = a` in `ℝ × ℝ` (Mathlib's `add_self_div_two` does not apply to the product). -/
lemma add_self_div_two_prod (a : ℝ × ℝ) : (a + a) / 2 = a := by
  refine Prod.ext ?_ ?_
  · change ((a.1 + a.1) / 2 : ℝ) = a.1
    ring
  · change ((a.2 + a.2) / 2 : ℝ) = a.2
    ring

/-- `⟨a, b⟩ = a + b * I`, the bridge between the coordinate formula of `confOf` and the smooth
complex expressions used below. -/
lemma complex_mk_eq_add_mul_I (a b : ℝ) :
    (⟨a, b⟩ : ℂ) = (a : ℂ) + (b : ℂ) * Complex.I := by
  nth_rewrite 1 [← Complex.re_add_im (⟨a, b⟩ : ℂ)]
  simp

/-- **The radial coordinate of the configuration point.** -/
lemma stripData_fst (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    (stripData γ w).1 = stripR γ w := by
  have h : eucNorm (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1))) ^ 2
      = Complex.normSq (stripChord γ w) := by
    rw [← normC_eq_eucNorm, Complex.normSq_eq_norm_sq, stripChord, chordC]
  simp only [stripData, stripR, stripA, stripMid, confOf, muOrd]
  rw [h]

/-- **The disk coordinate of the configuration point.** -/
lemma stripData_snd (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    (stripData γ w).2.1 = stripD γ w := by
  have h : eucNorm (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1))) ^ 2
      = Complex.normSq (stripChord γ w) := by
    rw [← normC_eq_eucNorm, Complex.normSq_eq_norm_sq, stripChord, chordC]
  rw [stripData, stripD, stripR, stripA, stripMid, confOf, muOrd]
  rw [h, complex_mk_eq_add_mul_I]
  push_cast
  ring

/-- **The doubled direction of the configuration point.** -/
lemma stripData_thd (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) :
    (stripData γ w).2.2 = dirC (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1))) := by
  simp [stripData, confOf, muOrd]

/-- **The capping radius of a chord is positive as soon as the curve avoids the origin.** -/
lemma stripData_pos (hγne : ∀ x : Circle, γ x ≠ 0) (w : EuclideanSpace ℝ (Fin 2)) :
    0 < (stripData γ w).1 := by
  rw [stripData, confOf_pos_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hzero : γ (Circle.exp (w 0)) - γ (Circle.exp (w 1)) = 0 :=
    eucNorm_eq_zero.mp (by simpa only [muOrd] using h3)
  have heq : γ (Circle.exp (w 0)) = γ (Circle.exp (w 1)) := sub_eq_zero.mp hzero
  have hγ0 : γ (Circle.exp (w 0)) = 0 := by
    have h₁ : ((γ (Circle.exp (w 0)) + γ (Circle.exp (w 0))) / 2).1 = 0 := by
      simpa only [muOrd, heq] using h1
    have h₂ : ((γ (Circle.exp (w 0)) + γ (Circle.exp (w 0))) / 2).2 = 0 := by
      simpa only [muOrd, heq] using h2
    rw [add_self_div_two_prod] at h₁ h₂
    exact Prod.ext h₁ h₂
  exact hγne _ hγ0

/-! ## 2. The halving of the doubled chord direction -/

/-- **The smooth halving of the doubled chord direction.**  Off the diagonal this is the undoubled
chord direction `chordUnitDir γ` (the curve data of `Work.Drive.contDiffOn_chordUnitDir`); on the
diagonal — where the chord vanishes and `dirC 0 = 0` — it is set to the constant `1`, a square root of
`circleOf 0 = 1`. -/
def stripHalf (γ : Circle → ℝ × ℝ) (w : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  if Circle.exp (w 0) = Circle.exp (w 1) then 1 else chordUnitDir γ (w 0, w 1)

lemma stripHalf_of_ne {w : EuclideanSpace ℝ (Fin 2)}
    (h : Circle.exp (w 0) ≠ Circle.exp (w 1)) : stripHalf γ w = chordUnitDir γ (w 0, w 1) := by
  unfold stripHalf
  rw [if_neg h]

lemma stripHalf_of_eq {w : EuclideanSpace ℝ (Fin 2)}
    (h : Circle.exp (w 0) = Circle.exp (w 1)) : stripHalf γ w = 1 := by
  unfold stripHalf
  rw [if_pos h]

/-- The halving has unit norm, *globally*. -/
lemma stripHalf_norm (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (w : EuclideanSpace ℝ (Fin 2)) : ‖stripHalf γ w‖ = 1 := by
  unfold stripHalf
  split_ifs with h
  · simp
  · exact (contDiffOn_chordUnitDir γ hγ).2.2 (w 0, w 1) h

/-- `circOf (circleOf a) = a`: the two coordinates of the circle are inverse. -/
lemma circOf_circleOf (a : UnitAddCircle) : circOf (circleOf a) (norm_circleOf a) = a := by
  have h : (⟨circleOf a, mem_unitSphere_of_norm (norm_circleOf a)⟩ : Circle) =
      (AddCircle.homeomorphCircle (T := 1) one_ne_zero) a := Subtype.ext rfl
  rw [circOf, h]
  exact (AddCircle.homeomorphCircle (T := 1) one_ne_zero).symm_apply_apply a

/-- `circleOf 0 = 1`: the class of the angle `0` is the unit complex number `1`. -/
lemma circleOf_zero : circleOf (0 : UnitAddCircle) = 1 := by
  have h : (0 : UnitAddCircle) = (((0 : ℝ)) : UnitAddCircle) := by
    rw [AddCircle.coe_zero]
  rw [h]
  refine Complex.ext ?_ ?_
  · rw [circleOf_coe_re]; norm_num
  · rw [circleOf_coe_im]; norm_num

/-- `dirC 0 = 0`: the doubled direction of the zero vector is the class of the angle `0`. -/
lemma dirC_zero : dirC (0 : ℝ × ℝ) = 0 := by
  have h : (⟨(0 : ℝ), (0 : ℝ)⟩ : ℂ) = 0 := by
    refine Complex.ext ?_ ?_ <;> simp
  unfold dirC
  rw [Prod.fst_zero, Prod.snd_zero, h]
  simp

/-- `circOf 1 = 0` (the class of the angle `0`), for an arbitrary proof argument. -/
lemma circOf_one (h : ‖(1 : ℂ)‖ = 1) : circOf (1 : ℂ) h = 0 := by
  refine circleOf_injective ?_
  rw [circleOf_circOf, circleOf_zero]

/-- **`circOf` is multiplicative** (it is the group isomorphism `S¹ ≅ ℝ/ℤ`). -/
lemma circOf_mul {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    circOf (z * w) (by rw [norm_mul, hz, hw, one_mul]) = circOf z hz + circOf w hw := by
  refine circleOf_injective ?_
  rw [circleOf_add, circleOf_circOf, circleOf_circOf, circleOf_circOf]

/-- **The square of the halving is the doubled direction of the configuration point.** -/
lemma circOf_stripHalf_sq (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (w : EuclideanSpace ℝ (Fin 2)) :
    circOf (stripHalf γ w ^ 2) (by rw [norm_pow, stripHalf_norm hγ w]; norm_num)
      = (stripData γ w).2.2 := by
  refine circleOf_injective ?_
  rw [circleOf_circOf, stripData_thd]
  unfold stripHalf
  split_ifs with h
  · -- the diagonal: the chord vanishes, and both sides are `0`
    have hdir : dirC (γ (Circle.exp (w 0)) - γ (Circle.exp (w 1))) = 0 := by
      rw [sub_eq_zero.mpr (congrArg γ h), dirC_zero]
    rw [hdir, circleOf_zero]
    norm_num
  · -- off the diagonal: `chordUnitDir` is the undoubled direction
    exact ((contDiffOn_chordUnitDir γ hγ).2.1 (w 0, w 1) h).symm

/-! ## 3. Smoothness of the two coordinate functions -/

lemma contDiff_stripMid (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (stripMid γ) := by
  have hbase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => γ (Circle.exp t)) :=
    (hγ.contMDiff.comp contMDiff_circleExp).contDiff
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 2) => γ (Circle.exp (w 0))) :=
    hbase.comp (by fun_prop)
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 2) => γ (Circle.exp (w 1))) :=
    hbase.comp (by fun_prop)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 2) =>
        (1 / 2 : ℝ) • (γ (Circle.exp (w 0)) + γ (Circle.exp (w 1)))) :=
    ContDiff.const_smul (1 / 2 : ℝ) (hA.add hB)
  refine contDiffOn_univ.mp (hc.contDiffOn.congr (fun w _ => ?_))
  refine Prod.ext ?_ ?_
  · change ((γ (Circle.exp (w 0)) + γ (Circle.exp (w 1))).1 / 2 : ℝ)
      = (1 / 2) * ((γ (Circle.exp (w 0)) + γ (Circle.exp (w 1))).1)
    ring
  · change ((γ (Circle.exp (w 0)) + γ (Circle.exp (w 1))).2 / 2 : ℝ)
      = (1 / 2) * ((γ (Circle.exp (w 0)) + γ (Circle.exp (w 1))).2)
    ring

lemma contDiff_stripChord_re
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : EuclideanSpace ℝ (Fin 2) => (stripChord γ w).re) := by
  have hbase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => γ (Circle.exp t)) :=
    (hγ.contMDiff.comp contMDiff_circleExp).contDiff
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 2) => γ (Circle.exp (w 0))) :=
    hbase.comp (by fun_prop)
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 2) => γ (Circle.exp (w 1))) :=
    hbase.comp (by fun_prop)
  refine contDiffOn_univ.mp (((hA.sub hB).fst).contDiffOn.congr (fun w _ => ?_))
  simp only [stripChord, chordC]

lemma contDiff_stripChord_im
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : EuclideanSpace ℝ (Fin 2) => (stripChord γ w).im) := by
  have hbase : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => γ (Circle.exp t)) :=
    (hγ.contMDiff.comp contMDiff_circleExp).contDiff
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 2) => γ (Circle.exp (w 0))) :=
    hbase.comp (by fun_prop)
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 2) => γ (Circle.exp (w 1))) :=
    hbase.comp (by fun_prop)
  refine contDiffOn_univ.mp (((hA.sub hB).snd).contDiffOn.congr (fun w _ => ?_))
  simp only [stripChord, chordC]

/-- The squared capping radius is smooth (a polynomial in the smooth midpoint and chord). -/
lemma contDiffAt_stripA (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (w₀ : EuclideanSpace ℝ (Fin 2)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (stripA γ) w₀ := by
  have hmid := contDiff_stripMid hγ
  have hre := contDiff_stripChord_re hγ
  have him := contDiff_stripChord_im hγ
  have hsum : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (stripMid γ w).1 ^ 2 + (stripMid γ w).2 ^ 2 +
        ((stripChord γ w).re * (stripChord γ w).re
          + (stripChord γ w).im * (stripChord γ w).im)) w₀ :=
    (((hmid.fst.pow 2).contDiffAt).add (hmid.snd.pow 2).contDiffAt).add
      (((hre.mul hre).contDiffAt).add ((him.mul him).contDiffAt))
  refine hsum.congr_of_eventuallyEq
    (Filter.EventuallyEq.of_eq (funext (fun w => ?_)))
  simp only [stripA, Complex.normSq_apply]

/-- **Smoothness of the radial coordinate `stripR = sqrt ∘ stripA`.** -/
lemma contMDiffAt_stripData_fst
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {w₀ : EuclideanSpace ℝ (Fin 2)} (hpos : stripA γ w₀ ≠ 0) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (stripData γ w).1) w₀ := by
  have hsqrt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (stripR γ) w₀ :=
    (Real.contDiffAt_sqrt hpos).comp w₀ (contDiffAt_stripA hγ w₀)
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (stripData γ w).1) w₀ :=
    hsqrt.congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq (funext (fun w => stripData_fst γ w)))
  exact contMDiffAt_iff_contDiffAt.mpr hcd

/-- **Smoothness of the disk coordinate `stripD`.** -/
lemma contMDiffAt_stripData_snd
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {w₀ : EuclideanSpace ℝ (Fin 2)} (hpos : stripA γ w₀ ≠ 0) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (stripData γ w).2.1) w₀ := by
  have hmid := contDiff_stripMid hγ
  have hnum : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => ((stripMid γ w).1 : ℂ) + ((stripMid γ w).2 : ℂ) * Complex.I) w₀ :=
    (((Complex.ofRealCLM.contDiff.comp hmid.fst).contDiffAt).add
      (((Complex.ofRealCLM.contDiff.comp hmid.snd).contDiffAt).mul contDiffAt_const))
  have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (((stripR γ w : ℝ)) : ℂ)) w₀ :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp w₀
      ((Real.contDiffAt_sqrt hpos).comp w₀ (contDiffAt_stripA hγ w₀))
  have hne : (((stripR γ w₀ : ℝ)) : ℂ) ≠ 0 := by
    have h : stripR γ w₀ ≠ 0 := by
      intro hh
      apply hpos
      have hA0 : (0 : ℝ) ≤ stripA γ w₀ := by
        rw [stripA, Complex.normSq_apply]
        nlinarith [sq_nonneg (stripMid γ w₀).1, sq_nonneg (stripMid γ w₀).2,
          sq_nonneg (stripChord γ w₀).re, sq_nonneg (stripChord γ w₀).im]
      have h2 : (stripR γ w₀) ^ 2 = 0 := by rw [hh]; ring
      unfold stripR at h2
      rwa [Real.sq_sqrt hA0] at h2
    simpa [Complex.ofReal_eq_zero] using h
  have hdiv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (stripD γ) w₀ := by
    refine (hnum.mul (hden.inv hne)).congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq (funext (fun w => ?_)))
    simp only [stripD, div_eq_mul_inv, Pi.inv_apply]
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (stripData γ w).2.1) w₀ :=
    hdiv.congr_of_eventuallyEq
      (Filter.EventuallyEq.of_eq (funext (fun w => stripData_snd γ w)))
  exact contMDiffAt_iff_contDiffAt.mpr hcd

/-- **Smoothness of the halving `stripHalf`** (in the real-analysis form `ContDiffAt`, which avoids
the manifold instances of the target). -/
lemma contDiffAt_stripHalf
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {w₀ : EuclideanSpace ℝ (Fin 2)} (hw₀ : Circle.exp (w₀ 0) ≠ Circle.exp (w₀ 1)) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (stripHalf γ) w₀ := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      ((Circle.exp p.1 : Circle) : ℂ) - ((Circle.exp p.2 : Circle) : ℂ)) :=
    (continuous_subtype_val.comp (Circle.exp.continuous.comp continuous_fst)).sub
      (continuous_subtype_val.comp (Circle.exp.continuous.comp continuous_snd))
  have hset : {p : ℝ × ℝ | Circle.exp p.1 ≠ Circle.exp p.2} =
      {p : ℝ × ℝ | ((Circle.exp p.1 : Circle) : ℂ) - ((Circle.exp p.2 : Circle) : ℂ) ≠ 0} := by
    ext p
    simp only [Set.mem_ofPred_eq, sub_ne_zero]
    exact ⟨fun h hh => h (Subtype.coe_inj.mp hh), fun h hh => h (congrArg Subtype.val hh)⟩
  have hopen : {p : ℝ × ℝ | Circle.exp p.1 ≠ Circle.exp p.2} ∈ 𝓝 (w₀ 0, w₀ 1) := by
    rw [hset]
    refine (isOpen_compl_singleton.preimage hcont).mem_nhds ?_
    intro hh
    exact hw₀ (Subtype.coe_inj.mp (sub_eq_zero.mp hh))
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chordUnitDir γ) (w₀ 0, w₀ 1) :=
    (contDiffOn_chordUnitDir γ hγ).1.contDiffAt hopen
  have hpair : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 2) => (w 0, w 1)) w₀ := by fun_prop
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 2) => chordUnitDir γ (w 0, w 1)) w₀ :=
    (h1.comp w₀ hpair).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq rfl)
  have hopen2 : {p : EuclideanSpace ℝ (Fin 2) | Circle.exp (p 0) ≠ Circle.exp (p 1)} ∈ 𝓝 w₀ :=
    hpair.continuousAt.preimage_mem_nhds hopen
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [hopen2] with p hp
  exact stripHalf_of_ne hp

/-! ## 4. The strip chart -/

/-- **The configuration strip of `γ`, rotated by `v`, as a chart of the capping space.**  At the
parameter `w` it is the class in `CappingSpace` of the configuration point of the chord with parameters
`(w 0, w 1)`, with the doubled direction shifted by `v` — i.e. the rotation of the strip `M` by `v`
(`Work.Drive.rotCapping`, through `Work.Drive.rotConfig`).  The two side conditions are the proven
`stripData_pos` and `Work.Drive.confOf_snd_norm_le_one`. -/
def stripChart (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0) (v : UnitAddCircle)
    (w : EuclideanSpace ℝ (Fin 2)) : CappingSpace :=
  Quotient.mk'' (Sum.inl (rotConfig v (confPiece (muOrd γ (Circle.exp (w 0), Circle.exp (w 1)))
    (stripData_pos hγne w) (confOf_snd_norm_le_one _))))

/-- **The halving identity for the rotated chart**: `stripHalf γ w * w_v` is a square root of the
rotated doubled direction, where `w_v` is a square root of `circleOf v`. -/
lemma circOf_stripHalf_mul_sq
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {v : UnitAddCircle} {w_v : ℂ} (hv : w_v ^ 2 = circleOf v) (hv1 : ‖w_v‖ = 1)
    (w : EuclideanSpace ℝ (Fin 2)) :
    circOf ((stripHalf γ w * w_v) ^ 2)
        (by rw [norm_pow, norm_mul, stripHalf_norm hγ w, hv1, one_mul, one_pow])
      = (stripData γ w).2.2 + v := by
  refine circleOf_injective ?_
  rw [circleOf_circOf, circleOf_add, ← hv, mul_pow, ← circOf_stripHalf_sq hγ w, circleOf_circOf]

/-- **The rotated strip chart is the `contMDiffAt_cappingSpace_configPiece` normal form.** -/
lemma stripChart_eq_piece
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) {v : UnitAddCircle} {w_v : ℂ}
    (hv : w_v ^ 2 = circleOf v) (hv1 : ‖w_v‖ = 1) (w : EuclideanSpace ℝ (Fin 2)) :
    stripChart γ hγne v w =
      Quotient.mk'' (Sum.inl ⟨((stripData γ w).1, (stripData γ w).2.1,
        circOf ((stripHalf γ w * w_v) ^ 2)
          (by rw [norm_pow, norm_mul, stripHalf_norm hγ w, hv1, one_mul, one_pow])),
        stripData_pos hγne w, confOf_snd_norm_le_one _⟩) := by
  refine Quotient.sound (Or.inl (congrArg Sum.inl (Subtype.ext ?_)))
  change ((stripData γ w).1, (stripData γ w).2.1, (stripData γ w).2.2 + v)
      = ((stripData γ w).1, (stripData γ w).2.1, circOf ((stripHalf γ w * w_v) ^ 2) _)
  rw [circOf_stripHalf_mul_sq hγ hv hv1 w]

/-- **The configuration strip of a smooth plane curve avoiding the origin is a smooth chart of the
capping space.**  For the rotation parameter `v` and a chosen square root `w_v` of `circleOf v`
(carried as data: no continuous choice exists), the rotated strip `v · M` is `C^∞` — for the
transparent smooth structure `Work.Drive.cappingCharted` — on the open set where the two parameters of
the chord are distinct, i.e. off the diagonal. -/
theorem contMDiffOn_stripChart (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (v : UnitAddCircle) {w_v : ℂ}
    (hv : w_v ^ 2 = circleOf v) (hv1 : ‖w_v‖ = 1) :
    letI := Work.Drive.cappingCharted
    ContMDiffOn (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (stripChart γ hγne v)
      {w : EuclideanSpace ℝ (Fin 2) | Circle.exp (w 0) ≠ Circle.exp (w 1)} := by
  letI := Work.Drive.cappingCharted
  intro w₀ hw₀
  have hA : stripA γ w₀ ≠ 0 := by
    have h : 0 < (stripData γ w₀).1 := stripData_pos hγne w₀
    rw [stripData_fst, stripR] at h
    intro hh
    rw [hh, Real.sqrt_zero] at h
    exact absurd h (lt_irrefl (0 : ℝ))
  have hR := contMDiffAt_stripData_fst hγ hA
  have hD := contMDiffAt_stripData_snd hγ hA
  have hH := contDiffAt_stripHalf hγ hw₀
  have hv1' : ‖w_v‖ = 1 := hv1
  have hZ : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => stripHalf γ w * w_v) w₀ :=
    contMDiffAt_iff_contDiffAt.mpr (hH.mul contDiffAt_const)
  have hpiece := contMDiffAt_cappingSpace_configPiece (k := 2)
    (fun w : EuclideanSpace ℝ (Fin 2) => (stripData γ w).1)
    (fun w => (stripData γ w).2.1)
    (fun w => stripHalf γ w * w_v) w₀
    (fun w => stripData_pos hγne w) (fun w => confOf_snd_norm_le_one _)
    (fun w => by rw [norm_mul, stripHalf_norm hγ w, hv1', one_mul])
    hR hD hZ
  refine (hpiece.contMDiffWithinAt).congr_of_eventuallyEq ?_ ?_
  · exact Filter.EventuallyEq.of_eq (funext (fun w => stripChart_eq_piece hγ hγne hv hv1 w))
  · exact stripChart_eq_piece hγ hγne hv hv1 w₀

end

end Work.Drive
