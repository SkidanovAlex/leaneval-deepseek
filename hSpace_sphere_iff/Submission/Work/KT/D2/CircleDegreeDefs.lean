import Mathlib

/-!
# Winding numbers of loops in `ℂˣ`: basic definitions

This file sets up the vocabulary for `Work.KT.D2.circle_degree`: the exponential covering
`expSub : ℂ → {z : ℂ // z ≠ 0}` with its period `W = 2πi`, the standard parametrisation
`stdLoop : I → S¹` (`S¹ = Metric.sphere (0 : ℂ) 1`), the loop `loopOf f : I → ℂ \ {0}` induced by
a loop `f : S¹ → ℂˣ`, and the winding number `deg f`, obtained by lifting `loopOf f` through the
exponential covering.  The main results `canLift_spec`, `canLift_zero`, `canLift_unique` and
`deg_spec` are the interface used by later files.
-/

namespace Work.KT.D2

noncomputable section

/-- The unit circle `S¹ = {z : ℂ // ‖z‖ = 1}`. -/
abbrev S1 : Type := Metric.sphere (0 : ℂ) 1

/-- The punctured plane, as the base of the exponential covering. -/
abbrev nzC : Type := {z : ℂ // z ≠ 0}

/-- The period `W = 2πi` of the exponential function. -/
def W : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem W_ne_zero : W ≠ 0 := Complex.two_pi_I_ne_zero

/-- `Complex.exp` as a map onto the punctured plane. -/
def expSub (z : ℂ) : nzC := ⟨Complex.exp z, Complex.exp_ne_zero z⟩

/-- The exponential map `ℂ → ℂ \ {0}` is a covering map. -/
theorem isCoveringMap_expSub : IsCoveringMap expSub := Complex.isCoveringMap_exp

@[simp] theorem expSub_coe (z : ℂ) : ((expSub z : nzC) : ℂ) = Complex.exp z := rfl

theorem expSub_surjective : Function.Surjective expSub := fun u =>
  ⟨Complex.log u, Subtype.ext (Complex.exp_log u.2)⟩

theorem expSub_eq_iff_aux (b : ℂ) (n : ℤ) : expSub (b + n * W) = expSub b := by
  apply Subtype.ext
  rw [expSub_coe, expSub_coe, Complex.exp_add, Complex.exp_int_mul,
    show Complex.exp W = 1 from Complex.exp_two_pi_mul_I]
  simp

/-- `expSub a = expSub b` iff `a` and `b` differ by an integral multiple of `W`. -/
theorem expSub_eq_iff {a b : ℂ} : expSub a = expSub b ↔ ∃ n : ℤ, a = b + n * W := by
  constructor
  · intro h
    exact Complex.exp_eq_exp_iff_exists_int.mp (Subtype.ext_iff.mp h)
  · rintro ⟨n, rfl⟩
    exact expSub_eq_iff_aux b n

theorem expSub_zsmul_W (n : ℤ) : expSub (n * W) = expSub 0 := by
  simpa using expSub_eq_iff_aux 0 n

/-- The standard parametrisation `t ↦ e^{2πit}` of the circle. -/
def stdLoop : C(unitInterval, S1) :=
  ⟨fun t => ⟨Complex.exp ((2 * (Real.pi : ℝ) * (t : ℝ) : ℂ) * Complex.I), by
      rw [Metric.mem_sphere, dist_zero_right, Complex.norm_exp]
      simp⟩,
   Continuous.subtype_mk (Complex.continuous_exp.comp (by fun_prop))
     (fun t => by
       rw [Metric.mem_sphere, dist_zero_right, Function.comp_apply, Complex.norm_exp]
       simp)⟩

theorem stdLoop_apply (t : unitInterval) :
    ((stdLoop t : S1) : ℂ) =
      Complex.exp ((2 * (Real.pi : ℝ) * (t : ℝ) : ℂ) * Complex.I) := rfl

theorem stdLoop_apply_W (t : unitInterval) :
    ((stdLoop t : S1) : ℂ) = Complex.exp ((t : ℝ) * W) := by
  rw [stdLoop_apply]
  congr 1
  simp only [W]
  ring

theorem stdLoop_zero_eq_one : stdLoop 0 = stdLoop 1 := by
  apply Subtype.ext
  rw [stdLoop_apply_W, stdLoop_apply_W]
  rw [show ((0 : unitInterval) : ℝ) * W = 0 by simp,
    show ((1 : unitInterval) : ℝ) * W = W by simp, Complex.exp_zero]
  exact Complex.exp_two_pi_mul_I.symm

theorem S1_coe_ne_zero (z : S1) : (z : ℂ) ≠ 0 := by
  intro h
  have hz := z.2
  rw [Metric.mem_sphere, dist_zero_right, h] at hz
  simp at hz

/-- The punctured-plane valued version of a loop in `ℂˣ`. -/
def nzOf (f : C(S1, ℂˣ)) : C(S1, nzC) :=
  ⟨fun z => ⟨(f z : ℂ), Units.ne_zero (f z)⟩,
   Continuous.subtype_mk (Units.continuous_val.comp f.continuous)
     (fun z => Units.ne_zero (f z))⟩

theorem nzOf_apply (f : C(S1, ℂˣ)) (z : S1) : ((nzOf f z : nzC) : ℂ) = (f z : ℂ) := rfl

/-- The loop `t ↦ f (e^{2πit})` in the punctured plane. -/
def loopOf (f : C(S1, ℂˣ)) : C(unitInterval, nzC) := (nzOf f).comp stdLoop

theorem loopOf_apply (f : C(S1, ℂˣ)) (t : unitInterval) :
    ((loopOf f t : nzC) : ℂ) = (f (stdLoop t) : ℂ) := rfl

/-- The chosen basepoint of the lift of `loopOf f`. -/
def base (f : C(S1, ℂˣ)) : ℂ := Complex.log ((loopOf f 0 : nzC) : ℂ)

theorem expSub_base (f : C(S1, ℂˣ)) : expSub (base f) = loopOf f 0 := by
  apply Subtype.ext
  rw [expSub_coe, base]
  exact Complex.exp_log (loopOf f 0).2

theorem loopOf_one_eq (f : C(S1, ℂˣ)) : loopOf f 1 = loopOf f 0 := by
  simp only [loopOf, ContinuousMap.comp_apply]
  rw [stdLoop_zero_eq_one]

/-- The canonical lift of `loopOf f` through the exponential covering, based at `base f`. -/
noncomputable def canLift (f : C(S1, ℂˣ)) : C(unitInterval, ℂ) :=
  isCoveringMap_expSub.liftPath (loopOf f) (base f) (expSub_base f).symm

theorem canLift_spec (f : C(S1, ℂˣ)) (t : unitInterval) : expSub (canLift f t) = loopOf f t :=
  congr_fun (isCoveringMap_expSub.liftPath_lifts (loopOf f) (base f) (expSub_base f).symm) t

theorem canLift_zero (f : C(S1, ℂˣ)) : canLift f 0 = base f :=
  isCoveringMap_expSub.liftPath_zero (loopOf f) (base f) (expSub_base f).symm

/-- Uniqueness of the lift: a lift of `loopOf f` based at `base f` is `canLift f`. -/
theorem canLift_unique (f : C(S1, ℂˣ)) (G : C(unitInterval, ℂ))
    (hG : expSub ∘ G = loopOf f) (h0 : G 0 = base f) : G = canLift f := by
  have h := (IsCoveringMap.eq_liftPath_iff' isCoveringMap_expSub (γ := loopOf f)
    (e := base f) (γ_0 := (expSub_base f).symm) (Γ := G)).mpr ⟨hG, h0⟩
  simpa only [canLift] using h

theorem deg_exists (f : C(S1, ℂˣ)) : ∃ k : ℤ, canLift f 1 = base f + k * W := by
  have h1 : expSub (canLift f 1) = expSub (base f) := by
    rw [canLift_spec, loopOf_one_eq, expSub_base]
  exact Complex.exp_eq_exp_iff_exists_int.mp (Subtype.ext_iff.mp h1)

/-- **The winding number** of a loop `f : S¹ → ℂˣ`: the endpoint of a lift of `loopOf f` through
the exponential covering, measured in units of `W = 2πi`. -/
noncomputable def deg (f : C(S1, ℂˣ)) : ℤ := Classical.choose (deg_exists f)

theorem deg_spec (f : C(S1, ℂˣ)) : canLift f 1 = base f + deg f * W :=
  Classical.choose_spec (deg_exists f)

end

end Work.KT.D2
