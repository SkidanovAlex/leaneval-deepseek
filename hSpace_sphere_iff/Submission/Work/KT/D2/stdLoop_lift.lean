import Mathlib
import Submission.Work.KT.D2.CircleDegreeDefs

/-!
# The standard parametrisation `t ↦ e^{2πit}` of the circle

`stdLoop : I → S¹` (`S¹ = Metric.sphere (0 : ℂ) 1`) is the standard parametrisation of the unit
circle.  It is a quotient map onto `S¹` whose only non-trivial fibre is `{0, 1}`: two parameters
`a b ∈ [0,1]` give the same point of `S¹` iff `a = b` or `{a,b} = {0,1}`.  Consequently every
continuous loop `G : I → ℂ` with `G 0 = G 1` descends through `stdLoop`, i.e. is the restriction of
a continuous map `S¹ → ℂ` along `stdLoop`.

These are exactly the four conjuncts of `stdLoop_lift` below.
-/

namespace Work.KT.D2

/-! ## Preliminaries -/

/-- The value of `stdLoop`, with the exponent written in the form `2πi·t` (`t` read in `ℂ`). -/
private lemma stdLoop_val (t : unitInterval) :
    ((stdLoop t : S1) : ℂ)
      = Complex.exp ((2 * (Real.pi : ℂ) * (t : ℂ)) * Complex.I) :=
  stdLoop_apply t

/-- Shifting the parameter by an integer does not change the value of the exponential: this is the
periodicity of `t ↦ e^{2πit}` with period `1`. -/
private lemma exp_shift_real (u : ℝ) (m : ℤ) :
    Complex.exp ((2 * (Real.pi : ℂ) * ((u + m : ℝ) : ℂ)) * Complex.I)
      = Complex.exp ((2 * (Real.pi : ℂ) * (u : ℂ)) * Complex.I) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m, ?_⟩
  push_cast
  ring

/-- A real number in `[0,1]` differing from another by an integer is either equal to it or the two
are the endpoints `0` and `1`. -/
private lemma eq_or_endpoints_of_sub_int {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) {n : ℤ} (h : a = b + (n : ℝ)) :
    a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  have hn_le : n ≤ 1 := by exact_mod_cast (show (n : ℝ) ≤ 1 by linarith)
  have hn_ge : (-1 : ℤ) ≤ n := by exact_mod_cast (show (-1 : ℝ) ≤ (n : ℝ) by linarith)
  have hcases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
  rcases hcases with h1 | h0 | h1
  · rw [h1] at h; push_cast at h; right; left; constructor <;> linarith
  · rw [h0] at h; push_cast at h; left; linarith
  · rw [h1] at h; push_cast at h; right; right; constructor <;> linarith

/-! ## The four conjuncts -/

/-- `stdLoop` is surjective: every point of the unit circle is `e^{2πit}` for some `t ∈ [0,1]`. -/
lemma stdLoop_surjective : Function.Surjective (⇑stdLoop) := by
  intro z
  have hz : ‖(z : ℂ)‖ = 1 := by
    have h := z.2
    rw [Metric.mem_sphere, dist_zero_right] at h
    exact h
  have hexp : Complex.exp (((z : ℂ).arg : ℂ) * Complex.I) = (z : ℂ) := by
    have h := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
    rw [hz] at h
    simpa using h
  set θ : ℝ := (z : ℂ).arg with hθ
  have hexp' : Complex.exp ((θ : ℂ) * Complex.I) = (z : ℂ) := by
    rw [hθ]; exact hexp
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hθlo : -Real.pi < θ := by rw [hθ]; exact Complex.neg_pi_lt_arg _
  have hθhi : θ ≤ Real.pi := by rw [hθ]; exact Complex.arg_le_pi _
  set t : ℝ := θ / (2 * Real.pi) with ht
  have htt : 2 * Real.pi * t = θ := by rw [ht]; field_simp
  have ht_hi : t ≤ 1 := by nlinarith [htt, hθhi, h2π]
  have ht_lo : -1 < t := by nlinarith [htt, hθlo, h2π]
  have hkey : Complex.exp ((2 * (Real.pi : ℂ) * (t : ℂ)) * Complex.I) = (z : ℂ) := by
    have hc : 2 * (Real.pi : ℂ) * (t : ℂ) = (θ : ℂ) := by exact_mod_cast htt
    rw [hc]; exact hexp'
  rcases lt_or_ge t 0 with ht0 | ht0
  · -- `t < 0`: shift the parameter by `1`, using the periodicity of `stdLoop`
    refine ⟨⟨t + (1 : ℤ), by push_cast; linarith, by push_cast; linarith⟩, ?_⟩
    apply Subtype.ext
    rw [stdLoop_val, exp_shift_real t 1]
    exact hkey
  · refine ⟨⟨t, ht0, ht_hi⟩, ?_⟩
    apply Subtype.ext
    rw [stdLoop_val]
    exact hkey

/-- `stdLoop` is a quotient map: it is a continuous surjection from the compact space `I` onto the
Hausdorff space `S¹`. -/
lemma stdLoop_isQuotientMap : Topology.IsQuotientMap (⇑stdLoop) :=
  Topology.IsQuotientMap.of_surjective_continuous stdLoop_surjective stdLoop.continuous

/-- The fibres of `stdLoop`: two parameters in `[0,1]` give the same point of `S¹` iff they are
equal, or they are the two endpoints `0` and `1` (in either order). -/
lemma stdLoop_fiber (a b : unitInterval) :
    stdLoop a = stdLoop b ↔ a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
  constructor
  · intro h
    have hc : Complex.exp ((a : ℝ) * W) = Complex.exp ((b : ℝ) * W) := by
      have := congrArg (fun x : S1 => (x : ℂ)) h
      simpa only [stdLoop_apply_W] using this
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hc
    have hn' : (a : ℂ) * W = (b : ℂ) * W + (n : ℂ) * W := by
      simpa only [W] using hn
    have h0 : ((a : ℂ) - (b : ℂ) - (n : ℂ)) * W = 0 := by
      rw [sub_mul, sub_mul, hn']; ring
    have hx : (a : ℂ) - (b : ℂ) - (n : ℂ) = 0 := (mul_eq_zero.mp h0).resolve_right W_ne_zero
    have hreℂ : (a : ℂ) = (b : ℂ) + (n : ℂ) := by linear_combination hx
    have hre : (a : ℝ) = (b : ℝ) + (n : ℝ) := by exact_mod_cast hreℂ
    rcases eq_or_endpoints_of_sub_int a.2.1 a.2.2 b.2.1 b.2.2 hre with hab | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl (Subtype.ext hab)
    · exact Or.inr (Or.inl ⟨Subtype.ext (by simpa using ha), Subtype.ext (by simpa using hb)⟩)
    · exact Or.inr (Or.inr ⟨Subtype.ext (by simpa using ha), Subtype.ext (by simpa using hb)⟩)
  · rintro (h | ⟨ha, hb⟩ | ⟨ha, hb⟩)
    · rw [h]
    · rw [ha, hb]; exact stdLoop_zero_eq_one
    · rw [ha, hb]; exact stdLoop_zero_eq_one.symm

/-- A continuous loop `I → ℂ` whose endpoints agree descends to the circle along `stdLoop`. -/
lemma stdLoop_lift_exists (G : C(unitInterval, ℂ)) (hG : G 0 = G 1) :
    ∃ F : C(S1, ℂ), F.comp stdLoop = G := by
  have hfac : Function.FactorsThrough G (⇑stdLoop) := by
    intro a b hab
    rcases (stdLoop_fiber a b).mp hab with hab' | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [hab']
    · rw [ha, hb, hG]
    · rw [ha, hb, hG]
  exact ⟨stdLoop_isQuotientMap.lift G hfac, stdLoop_isQuotientMap.lift_comp G hfac⟩

/-! ## The main statement -/

theorem stdLoop_lift :
    (Function.Surjective (⇑Work.KT.D2.stdLoop) ∧
      Topology.IsQuotientMap (⇑Work.KT.D2.stdLoop) ∧
      (∀ a b : unitInterval,
        Work.KT.D2.stdLoop a = Work.KT.D2.stdLoop b ↔
          a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0))) ∧
    (∀ G : C(unitInterval, ℂ), G 0 = G 1 →
      ∃ F : C(Work.KT.D2.S1, ℂ), F.comp Work.KT.D2.stdLoop = G) :=
  ⟨⟨stdLoop_surjective, stdLoop_isQuotientMap, stdLoop_fiber⟩, stdLoop_lift_exists⟩

end Work.KT.D2
