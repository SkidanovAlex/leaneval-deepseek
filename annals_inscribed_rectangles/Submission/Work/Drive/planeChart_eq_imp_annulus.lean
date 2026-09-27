import Mathlib
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.essential_loop
import Submission.Work.Drive.cappedPlaneCharts

namespace Work.Drive

open Submission.Configuration (muOrd)
open Submission.Geometry (eucNorm eucNorm_nonneg)

noncomputable section

/-!
# The annulus injectivity of a plane chart

`Work.Drive.IsPlaneChart` constrains the chart `Q` of the capped plane on the annulus
`1/2 < ‖z‖ ≤ 1` to be the *strip chart* `Work.Drive.stripChart γ hγne 0` at the strip parameter
`mk2 (arg z + √(π²(‖z‖ - 1/2)/2)) (arg z - √(π²(‖z‖ - 1/2)/2))`.  Equivalently: on the annulus the
chart classifies the chord of `γ` whose midpoint is the point of `γ` at parameter `arg z` and whose
half-length is `√(π²(‖z‖ - 1/2)/2)` — the *symmetric* chord around `γ (arg z)`.

This file proves that this reading classifies `z` up to the boundary identification: two points of the
closed annulus have the same chart value only if they are equal, or are the two antipodal points of the
outer boundary circle `‖z‖ = 1` (where the annulus runs out of room and the chart degenerates to the
diameters of `γ`).

The two halves of the argument are:

* the configuration map `muOrd γ` is injective on *unordered* pairs of points of `γ`
  (`Work.Drive.muOrd_injective_unordered`, restated here with only the injectivity of `γ` as
  hypothesis: `Work.Drive.muOrd_injective_unordered_of_injective`);
* elementary trigonometry with `Complex.arg` and `Circle.exp`: the two strip parameters of `z` are
  `arg z ± s` with `s ∈ (0, π/2]`, so the two possible matchings of the exponentiated parameters force
  either `s = s'` and `arg z = arg z'` (hence `z = z'`), or `s = s' = π/2` and
  `arg z ≡ arg z' + π (mod 2π)` (hence `‖z‖ = ‖z'‖ = 1` and `z' = -z`).
-/

/-! ## Helpers -/

/-- `rotConfig 0` is the identity on the configuration piece. -/
lemma rotConfig_zero (p : ConfigPiece) : rotConfig 0 p = p := by
  apply Subtype.ext
  simp [rotConfig]

/-- **Unfolding `stripChart` at rotation zero.**  Two equal strip chart values at rotation zero have
the same capping coordinates of their chords. -/
lemma stripChart_zero_confOf_eq {γ : Circle → ℝ × ℝ} (hγne : ∀ x : Circle, γ x ≠ 0)
    {w w' : EuclideanSpace ℝ (Fin 2)}
    (h : stripChart γ hγne 0 w = stripChart γ hγne 0 w') :
    confOf (muOrd γ (Circle.exp (w 0), Circle.exp (w 1)))
      = confOf (muOrd γ (Circle.exp (w' 0), Circle.exp (w' 1))) := by
  simp only [stripChart] at h
  rw [rotConfig_zero, rotConfig_zero] at h
  have hA : confPiece (muOrd γ (Circle.exp (w 0), Circle.exp (w 1)))
      (stripData_pos hγne w) (confOf_snd_norm_le_one _)
      = confPiece (muOrd γ (Circle.exp (w' 0), Circle.exp (w' 1)))
        (stripData_pos hγne w') (confOf_snd_norm_le_one _) := mk_inl_inj.mp h
  exact congrArg Subtype.val hA

/-- **Two chords with the same configuration are the same unordered pair of points of `γ`.**  This is
`Work.Drive.muOrd_injective_unordered` with only injectivity of `γ` assumed (its proof uses nothing
else). -/
theorem muOrd_injective_unordered_of_injective {γ : Circle → ℝ × ℝ} (hγinj : Function.Injective γ)
    {x y x' y' : Circle} (h : muOrd γ (x, y) = muOrd γ (x', y')) :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  have hmid : (γ x + γ y) / 2 = (γ x' + γ y') / 2 := by
    have := congrArg (fun q : (ℝ × ℝ) × UnitAddCircle × ℝ => q.1) h
    simpa [muOrd] using this
  have hdir : Submission.Collision.dirC (γ x - γ y) =
      Submission.Collision.dirC (γ x' - γ y') := by
    have := congrArg (fun q : (ℝ × ℝ) × UnitAddCircle × ℝ => q.2.1) h
    simpa [muOrd] using this
  have hlen : eucNorm (γ x - γ y) = eucNorm (γ x' - γ y') := by
    have := congrArg (fun q : (ℝ × ℝ) × UnitAddCircle × ℝ => q.2.2) h
    simpa [muOrd] using this
  have hsum : γ x + γ y = γ x' + γ y' := muOrd_halve_inj hmid
  have hn : ‖(⟨(γ x - γ y).1, (γ x - γ y).2⟩ : ℂ)‖ =
      ‖(⟨(γ x' - γ y').1, (γ x' - γ y').2⟩ : ℂ)‖ := by
    rw [Submission.Collision.normC_eq_eucNorm, Submission.Collision.normC_eq_eucNorm, hlen]
  have hdir' : Submission.Collision.dirC (γ x' - γ y') =
      Submission.Collision.dirC (γ x - γ y) + ((0 / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
    simp [hdir]
  obtain ⟨φ, hwφ, hvφ⟩ := Submission.Collision.exists_angle_of_dir_eq
    (v := γ x - γ y) (w := γ x' - γ y') hn hdir'
  rcases hvφ with hvφ | hvφ
  · have hsub : γ x - γ y = γ x' - γ y' := by
      rw [hvφ, hwφ]; simp only [zero_div, sub_zero]
    obtain ⟨hx, hy⟩ := muOrd_add_sub_inj hsum hsub
    exact Or.inl ⟨hγinj hx, hγinj hy⟩
  · have hneg : -(γ x - γ y) = γ x' - γ y' := by
      rw [hvφ, hwφ]; simp only [zero_div, sub_zero]
    have hsub : γ x' - γ y' = γ y - γ x := by rw [← hneg]; abel
    have hsum' : γ x' + γ y' = γ y + γ x := hsum.symm.trans (add_comm (γ x) (γ y))
    obtain ⟨hx, hy⟩ := muOrd_add_sub_inj hsum' hsub
    exact Or.inr ⟨(hγinj hy).symm, (hγinj hx).symm⟩

/-! ## The strip parameter of an annulus point -/

/-- The opening of the strip parameter of the plane chart at `z`: `√(π²(‖z‖ - 1/2)/2)`. -/
def annS (z : ℂ) : ℝ := Real.sqrt (Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2)

/-- The strip parameter of the plane chart at a point of the annulus `1/2 < ‖z‖ ≤ 1`: the chord
symmetric around `γ (arg z)` with half-opening `annS z`. -/
def annW (z : ℂ) : EuclideanSpace ℝ (Fin 2) :=
  mk2 (Complex.arg z + annS z) (Complex.arg z - annS z)

@[simp] lemma annW_apply_zero (z : ℂ) : (annW z) 0 = Complex.arg z + annS z := by
  simp [annW, mk2]

@[simp] lemma annW_apply_one (z : ℂ) : (annW z) 1 = Complex.arg z - annS z := by
  simp [annW, mk2]

lemma annS_pos {z : ℂ} (hz : 1 / 2 < ‖z‖) : 0 < annS z := by
  rw [annS]
  refine Real.sqrt_pos.mpr ?_
  have h : 0 < ‖z‖ - 1 / 2 := by linarith
  exact div_pos (mul_pos (pow_pos Real.pi_pos 2) h) (by norm_num)

lemma annS_le {z : ℂ} (hz1 : ‖z‖ ≤ 1) : annS z ≤ Real.pi / 2 := by
  rw [annS]
  calc Real.sqrt (Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2) ≤ Real.sqrt ((Real.pi / 2) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [hz1, Real.pi_pos]
    _ = Real.pi / 2 := Real.sqrt_sq (by positivity)

lemma annS_sq {z : ℂ} (hz : 1 / 2 < ‖z‖) :
    (annS z) ^ 2 = Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2 := by
  rw [annS]
  have h : 0 < ‖z‖ - 1 / 2 := by linarith
  exact Real.sq_sqrt (le_of_lt (div_pos (mul_pos (pow_pos Real.pi_pos 2) h) (by norm_num)))

lemma annS_eq_imp_norm_eq {z z' : ℂ} (hz : 1 / 2 < ‖z‖) (hz' : 1 / 2 < ‖z'‖)
    (h : annS z = annS z') : ‖z‖ = ‖z'‖ := by
  have h4 : Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2 = Real.pi ^ 2 * (‖z'‖ - 1 / 2) / 2 := by
    rw [← annS_sq hz, ← annS_sq hz', h]
  have hp : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt Real.pi_pos)
  have h5 : ‖z‖ - 1 / 2 = ‖z'‖ - 1 / 2 :=
    mul_left_cancel₀ hp
      (by linarith [h4] : Real.pi ^ 2 * (‖z‖ - 1 / 2) = Real.pi ^ 2 * (‖z'‖ - 1 / 2))
  linarith

lemma annS_eq_pi_div_two_imp_norm_eq_one {z : ℂ} (hz : 1 / 2 < ‖z‖)
    (h : annS z = Real.pi / 2) : ‖z‖ = 1 := by
  have h4 : Real.pi ^ 2 * (‖z‖ - 1 / 2) / 2 = (Real.pi / 2) ^ 2 := by rw [← annS_sq hz, h]
  have hp : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt Real.pi_pos)
  have h5 : ‖z‖ - 1 / 2 = 1 / 2 := by
    refine mul_left_cancel₀ hp ?_
    nlinarith [h4]
  linarith

/-! ## The classification of the strip parameter -/

/-- **The strip parameter of the plane chart classifies the point of the annulus** up to the antipodal
identification of the boundary circle. -/
theorem stripChart_annW_eq_imp {γ : Circle → ℝ × ℝ} (hγne : ∀ x : Circle, γ x ≠ 0)
    (hγinj : Function.Injective γ) {z z' : ℂ}
    (hz : 1 / 2 < ‖z‖) (hz1 : ‖z‖ ≤ 1) (hz' : 1 / 2 < ‖z'‖) (hz1' : ‖z'‖ ≤ 1)
    (h : stripChart γ hγne 0 (annW z) = stripChart γ hγne 0 (annW z')) :
    z = z' ∨ (‖z‖ = 1 ∧ ‖z'‖ = 1 ∧ z' = -z) := by
  have hza : 0 < annS z := annS_pos hz
  have hzb : annS z ≤ Real.pi / 2 := annS_le hz1
  have hza' : 0 < annS z' := annS_pos hz'
  have hzb' : annS z' ≤ Real.pi / 2 := annS_le hz1'
  -- the capping coordinates of the two chords agree
  have hconf : confOf (muOrd γ (Circle.exp (Complex.arg z + annS z),
        Circle.exp (Complex.arg z - annS z)))
      = confOf (muOrd γ (Circle.exp (Complex.arg z' + annS z'),
        Circle.exp (Complex.arg z' - annS z'))) := by
    have h' := stripChart_zero_confOf_eq (γ := γ) hγne (w := annW z) (w' := annW z') h
    rwa [annW_apply_zero, annW_apply_one, annW_apply_zero, annW_apply_one] at h'
  have hlen1 : 0 ≤ (muOrd γ (Circle.exp (Complex.arg z + annS z),
      Circle.exp (Complex.arg z - annS z))).2.2 := by
    simp only [muOrd]; exact eucNorm_nonneg _
  have hlen2 : 0 ≤ (muOrd γ (Circle.exp (Complex.arg z' + annS z'),
      Circle.exp (Complex.arg z' - annS z'))).2.2 := by
    simp only [muOrd]; exact eucNorm_nonneg _
  have hmu := confOf_injective_of_nonneg hlen1 hlen2 hconf
  have hunord := muOrd_injective_unordered_of_injective hγinj hmu
  rcases hunord with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- the two strip parameters exponentiate to the same values in the same order
    obtain ⟨k, hk⟩ := circle_exp_eq_iff_exists_int.mp h1
    obtain ⟨l, hl⟩ := circle_exp_eq_iff_exists_int.mp h2
    have hsdiff : annS z - annS z' = Real.pi * ((k : ℝ) - (l : ℝ)) := by linarith [hk, hl]
    have hbound : |(k : ℝ) - (l : ℝ)| < 1 := by
      rw [abs_lt]
      refine ⟨?_, ?_⟩ <;>
        nlinarith [hsdiff, hza, hzb, hza', hzb', Real.pi_pos]
    have hkl : k = l := by
      have h8 : ((|k - l| : ℤ) : ℝ) < 1 := by
        rw [Int.cast_abs, Int.cast_sub]; exact hbound
      have h9 : |k - l| < 1 := by exact_mod_cast h8
      exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp h9)
    have hss : annS z = annS z' := by
      have hs' := hsdiff
      rw [hkl] at hs'
      simp only [sub_self, mul_zero] at hs'
      linarith
    have hnorm : ‖z‖ = ‖z'‖ := annS_eq_imp_norm_eq hz hz' hss
    have hexp : Circle.exp (Complex.arg z) = Circle.exp (Complex.arg z') := by
      refine circle_exp_eq_iff_exists_int.mpr ⟨k, ?_⟩
      have hk' := hk
      rw [hss] at hk'
      linarith
    left
    have hexpC : Complex.exp (Complex.arg z * Complex.I)
        = Complex.exp (Complex.arg z' * Complex.I) := by
      simpa only [Circle.coe_exp] using congrArg (fun w : Circle => (w : ℂ)) hexp
    rw [← Complex.norm_mul_exp_arg_mul_I z, ← Complex.norm_mul_exp_arg_mul_I z', hexpC, hnorm]
  · -- the two strip parameters exponentiate to exchanged values
    obtain ⟨k, hk⟩ := circle_exp_eq_iff_exists_int.mp h1
    obtain ⟨l, hl⟩ := circle_exp_eq_iff_exists_int.mp h2
    have hsum : annS z + annS z' = Real.pi * ((k : ℝ) - (l : ℝ)) := by linarith [hk, hl]
    have hgt : 0 < Real.pi * ((k : ℝ) - (l : ℝ)) := by
      nlinarith [hsum, hza, hza', Real.pi_pos]
    have hle : Real.pi * ((k : ℝ) - (l : ℝ)) ≤ Real.pi := by
      nlinarith [hsum, hzb, hzb', Real.pi_pos]
    have hkl : k - l = 1 := by
      have hxpos : (0 : ℝ) < (k : ℝ) - (l : ℝ) := by nlinarith [hgt, Real.pi_pos]
      have hxle : (k : ℝ) - (l : ℝ) ≤ 1 := by nlinarith [hle, Real.pi_pos]
      have h1a : (0 : ℤ) < k - l := by
        have h' : ((0 : ℤ) : ℝ) < ((k - l : ℤ) : ℝ) := by push_cast; exact hxpos
        exact_mod_cast h'
      have h2a : k - l ≤ (1 : ℤ) := by
        have h' : ((k - l : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by push_cast; exact hxle
        exact_mod_cast h'
      omega
    have hss : annS z + annS z' = Real.pi := by
      have hkml : ((k : ℝ) - (l : ℝ)) = 1 := by rw [← Int.cast_sub, hkl]; norm_num
      rw [hsum, hkml, mul_one]
    have hnorm : ‖z‖ = 1 := by
      have hπ : annS z = Real.pi / 2 := by linarith [hss, hzb, hzb']
      exact annS_eq_pi_div_two_imp_norm_eq_one hz hπ
    have hnorm' : ‖z'‖ = 1 := by
      have hπ : annS z' = Real.pi / 2 := by linarith [hss, hzb, hzb']
      exact annS_eq_pi_div_two_imp_norm_eq_one hz' hπ
    have hargdiff : Complex.arg z - Complex.arg z' = Real.pi * ((k : ℝ) + (l : ℝ)) := by
      linarith [hk, hl]
    have hexp : Circle.exp (Complex.arg z') = - Circle.exp (Complex.arg z) := by
      have hkml : ((k : ℝ) - (l : ℝ)) = 1 := by rw [← Int.cast_sub, hkl]; norm_num
      have hksum : ((k : ℝ) + (l : ℝ)) = 2 * (l : ℝ) + 1 := by linarith [hkml]
      have harg : Complex.arg z' = Complex.arg z - Real.pi * ((k : ℝ) + (l : ℝ)) := by
        linarith [hargdiff]
      rw [harg, hksum]
      have h2 : Circle.exp (Real.pi * (2 * (l : ℝ) + 1)) = -1 := by
        rw [show Real.pi * (2 * (l : ℝ) + 1) = 2 * Real.pi * (l : ℝ) + Real.pi by ring,
          Circle.exp_add]
        have h4 : Circle.exp (2 * Real.pi * (l : ℝ)) = 1 := by
          refine Circle.exp_eq_one.mpr ⟨l, ?_⟩
          push_cast
          ring
        rw [h4, one_mul, circle_exp_pi]
      rw [Circle.exp_sub, h2, div_neg, div_one]
    right
    refine ⟨hnorm, hnorm', ?_⟩
    have hexpC : Complex.exp (Complex.arg z' * Complex.I)
        = - Complex.exp (Complex.arg z * Complex.I) := by
      simpa only [Circle.coe_exp, Circle.coe_neg] using
        congrArg (fun w : Circle => (w : ℂ)) hexp
    rw [← Complex.norm_mul_exp_arg_mul_I z', ← Complex.norm_mul_exp_arg_mul_I z, hnorm', hnorm]
    simpa using hexpC

/-- **The exterior of the plane chart's outer boundary circle is classified by the chart**: two points
of the closed disk of radius `1` that both lie outside the inner disk of radius `1/2` have the same
chart value only if they are equal, or are the two antipodal points of the boundary circle. -/
theorem planeChart_eq_imp_annulus {γ : Circle → ℝ × ℝ}
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    {z z' : ℂ} (hz : 1 / 2 < ‖z‖) (hz1 : ‖z‖ ≤ 1) (hz' : 1 / 2 < ‖z'‖) (hz1' : ‖z'‖ ≤ 1)
    (h : Q z = Q z') : z = z' ∨ (‖z‖ = 1 ∧ ‖z'‖ = 1 ∧ z' = -z) := by
  have hval : Q z = stripChart γ hγne 0 (annW z) := hQ.2.1 z hz hz1
  have hval' : Q z' = stripChart γ hγne 0 (annW z') := hQ.2.1 z' hz' hz1'
  have hstrip : stripChart γ hγne 0 (annW z) = stripChart γ hγne 0 (annW z') := by
    rw [← hval, ← hval', h]
  exact stripChart_annW_eq_imp hγne hγinj hz hz1 hz' hz1' hstrip

end

end Work.Drive
