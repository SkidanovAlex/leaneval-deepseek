import Submission.Work.Smooth.JordanSeparation.curve_arg_continuous

open Set
open Work.Smooth.Jordan

/-!
# Transfer of an injective disc filling along an embedded cylinder

**(E) — "the curve is the boundary circle of an injective map of the disc" — is invariant under
"pushing the curve along an embedded cylinder".**  If `Φ : S¹ × [0,1] → ℂ` is an embedded cylinder
(`Φ` continuous, `2π`-periodic in the first variable, injective modulo the period) with
`Φ (·,0) = γ₀` and `Φ (·,1) = γ₁`, and if `γ₁` bounds an injectively parametrised disc `F₁` *and the
cylinder at heights `< 1` avoids the image of `F₁`*, then `γ₀` also bounds an injectively
parametrised disc.

This is the mechanism by which the Schoenflies problem can be moved along a collar, along an
isotopy, or along any explicit "sweep": the new filling is

`F₀ (w) = F₁ (2w)` for `‖w‖ ≤ 1/2`,   `F₀ (w) = Φ (arg w, 2 - 2‖w‖)` for `1/2 ≤ ‖w‖ ≤ 1`,

which is injective because the inner disc fills `V (γ₁)` and the cylinder shell stays outside it.
No hypothesis on the image of `F₁` is needed beyond injectivity (`range_eq_closure_V_of_injective_extension`
identifies it with `closure V (γ₁)`).

## Main declarations

* `DiscExtension γ` — statement **(E)** for a plane curve `γ`;
* `discExtension_of_cylinder` — the transfer;
* `continuousAt_arg_lift`, `continuousOn_arg_lift` — the joint continuity of `(w, s) ↦ Φ (arg w, s)`
  for a `2π`-periodic `Φ` (the analytic plumbing of the annular part);
* `clamp`, `clampDisc` — the radial clamp to the unit disc, used to make the inner piece total.
-/

namespace Work.Smooth.JordanSeparation

noncomputable section

/-! ## The joint lift of a cylinder along the argument -/

theorem continuousAt_arg_lift {Φ : ℝ × ℝ → ℂ} (hcont : Continuous Φ)
    (hper : ∀ t s : ℝ, Φ (t + 2 * Real.pi, s) = Φ (t, s)) {w : ℂ} {s : ℝ} (hw : w ≠ 0) :
    ContinuousAt (fun p : ℂ × ℝ => Φ (Complex.arg p.1, p.2)) (w, s) := by
  by_cases hslit : w ∈ Complex.slitPlane
  · have h1 : ContinuousAt (fun p : ℂ × ℝ => Complex.arg p.1) (w, s) :=
      ContinuousAt.comp (g := Complex.arg) (f := fun p : ℂ × ℝ => p.1)
        (Complex.continuousAt_arg hslit) continuousAt_fst
    have h2 : ContinuousAt (fun p : ℂ × ℝ => (Complex.arg p.1, p.2)) (w, s) :=
      h1.prodMk continuousAt_snd
    exact hcont.continuousAt.comp h2
  · have hle : w.re ≤ 0 := by
      by_contra h
      exact hslit (Or.inl (by simpa using not_le.mp h))
    have him : w.im = 0 := by
      by_contra h
      exact hslit (Or.inr h)
    have hlt : w.re < 0 := by
      rcases lt_or_eq_of_le hle with h' | h'
      · exact h'
      · refine absurd h' ?_
        intro h0
        exact hw (Complex.ext h0 him)
    have hneg : -w ∈ Complex.slitPlane := Or.inl (by rw [Complex.neg_re]; linarith)
    have h1 : ContinuousAt (fun p : ℂ × ℝ => Complex.arg (-p.1) + Real.pi) (w, s) :=
      ContinuousAt.comp (g := fun z : ℂ => Complex.arg z + Real.pi)
        (f := fun p : ℂ × ℝ => -p.1)
        ((Complex.continuousAt_arg hneg).add_const Real.pi) continuousAt_fst.neg
    have h2 : ContinuousAt (fun p : ℂ × ℝ => (Complex.arg (-p.1) + Real.pi, p.2)) (w, s) :=
      h1.prodMk continuousAt_snd
    have hcomp : ContinuousAt (fun p : ℂ × ℝ => Φ (Complex.arg (-p.1) + Real.pi, p.2)) (w, s) :=
      hcont.continuousAt.comp h2
    refine hcomp.congr ?_
    have hnb : {p : ℂ × ℝ | p.1 ≠ 0} ∈ nhds (w, s) :=
      (isOpen_ne.preimage continuous_fst).mem_nhds hw
    filter_upwards [hnb] with p hp
    exact (curve_arg_neg_periodic (γ := fun t => Φ (t, p.2)) (fun t => hper t p.2) hp).symm

/-! ## The radial clamp -/

noncomputable def clamp (x : ℂ) : ℂ := x / ((max 1 ‖x‖ : ℝ) : ℂ)

theorem clamp_eq_self {x : ℂ} (h : ‖x‖ ≤ 1) : clamp x = x := by
  rw [clamp, max_eq_left h, Complex.ofReal_one, div_one]

theorem norm_clamp_le (x : ℂ) : ‖clamp x‖ ≤ 1 := by
  have hpos : (0 : ℝ) < max 1 ‖x‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [clamp, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
    div_le_one hpos]
  exact le_max_right _ _

theorem continuous_clamp : Continuous clamp := by
  unfold clamp
  refine Continuous.div continuous_id
    (Complex.continuous_ofReal.comp (continuous_const.max continuous_norm)) (fun x => ?_)
  have hpos : (0 : ℝ) < max 1 ‖x‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
  simpa using hpos.ne'

noncomputable def clampDisc (x : ℂ) : Disc :=
  ⟨clamp x, by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_clamp_le x⟩

@[simp] theorem coe_clampDisc (x : ℂ) : ((clampDisc x : Disc) : ℂ) = clamp x := rfl

theorem continuous_clampDisc : Continuous clampDisc :=
  continuous_clamp.subtype_mk (fun x => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_clamp_le x)

/-! ## The transfer -/

def DiscExtension (γ : PlaneCurve) : Prop :=
  ∃ F : C(Disc, ℂ), Function.Injective F ∧ ∀ θ : ℝ, F (circlePoint θ) = γ θ

theorem norm_circlePoint (θ : ℝ) : ‖((circlePoint θ : Disc) : ℂ)‖ = 1 := by
  rw [circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

/-- The **transfer of an injective disc filling along an embedded cylinder**. -/
theorem discExtension_of_cylinder (γ₀ γ₁ : PlaneCurve)
    (Φ : ℝ × ℝ → ℂ) (hcont : Continuous Φ)
    (hper : ∀ t s : ℝ, Φ (t + 2 * Real.pi, s) = Φ (t, s))
    (hzero : ∀ t : ℝ, Φ (t, 0) = γ₀ t)
    (hone : ∀ t : ℝ, Φ (t, 1) = γ₁ t)
    (hinj : ∀ t s t' s' : ℝ, s ∈ Set.Icc 0 1 → s' ∈ Set.Icc 0 1 →
        Φ (t, s) = Φ (t', s') → s = s' ∧ ∃ k : ℤ, t' = t + k * (2 * Real.pi))
    (F₁ : C(Disc, ℂ)) (hF₁ : Function.Injective F₁)
    (hF₁bd : ∀ θ : ℝ, F₁ (circlePoint θ) = γ₁ θ)
    (havoid : ∀ t s : ℝ, s ∈ Set.Icc 0 1 → s < 1 → Φ (t, s) ∉ Set.range F₁) :
    DiscExtension γ₀ := by
  classical
  set f : Disc → ℂ := fun w => F₁ (clampDisc (2 * (w : ℂ))) with hf
  set g : Disc → ℂ := fun w => Φ (Complex.arg (w : ℂ), 2 - 2 * ‖(w : ℂ)‖) with hg
  have hfcont : Continuous f := by
    rw [hf]
    exact F₁.continuous.comp (continuous_clampDisc.comp
      (continuous_const.mul continuous_subtype_val))
  have hmem1 : ∀ u : Disc, ‖(u : ℂ)‖ ≤ 1 := by
    intro u
    have := Metric.mem_closedBall.mp u.2
    rwa [dist_zero_right] at this
  have hgcont : ContinuousOn g {w : Disc | (1:ℝ)/2 ≤ ‖(w : ℂ)‖} := by
    intro w hw
    have hw' : (1:ℝ)/2 ≤ ‖(w : ℂ)‖ := by simpa using hw
    have hw0 : (w : ℂ) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hw'; norm_num at hw'
    have h1 : ContinuousAt (fun w : Disc => ((w : ℂ), 2 - 2 * ‖(w : ℂ)‖)) w :=
      continuous_subtype_val.continuousAt.prodMk
        ((continuous_const.sub (continuous_const.mul continuous_subtype_val.norm)).continuousAt)
    have h2 : ContinuousAt (fun p : ℂ × ℝ => Φ (Complex.arg p.1, p.2))
        ((w : ℂ), 2 - 2 * ‖(w : ℂ)‖) :=
      continuousAt_arg_lift hcont hper hw0
    exact (h2.comp (x := w) (f := fun w : Disc => ((w : ℂ), 2 - 2 * ‖(w : ℂ)‖)) h1).continuousWithinAt
  have hfmono : ContinuousOn f (closure {w : Disc | ‖(w : ℂ)‖ ≤ (1:ℝ)/2}) :=
    hfcont.continuousOn
  have hgclos : ContinuousOn g (closure {w : Disc | ¬ ‖(w : ℂ)‖ ≤ (1:ℝ)/2}) := by
    refine hgcont.mono (closure_minimal ?_
      (isClosed_le continuous_const continuous_subtype_val.norm))
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    exact le_of_lt (not_le.mp hw)
  have hfront : ∀ a ∈ frontier {w : Disc | ‖(w : ℂ)‖ ≤ (1:ℝ)/2}, f a = g a := by
    intro a ha
    have hclosed : IsClosed {w : Disc | ‖(w : ℂ)‖ ≤ (1:ℝ)/2} :=
      isClosed_le continuous_subtype_val.norm continuous_const
    have hle : ‖(a : ℂ)‖ ≤ (1:ℝ)/2 := by
      have h1 : a ∈ closure {w : Disc | ‖(w : ℂ)‖ ≤ (1:ℝ)/2} := ha.1
      rwa [hclosed.closure_eq] at h1
    have hnotlt : ¬ ‖(a : ℂ)‖ < (1:ℝ)/2 := by
      intro hlt
      have hopen : IsOpen {w : Disc | ‖(w : ℂ)‖ < (1:ℝ)/2} :=
        isOpen_lt continuous_subtype_val.norm continuous_const
      have hsub : {w : Disc | ‖(w : ℂ)‖ < (1:ℝ)/2}
          ⊆ interior {w : Disc | ‖(w : ℂ)‖ ≤ (1:ℝ)/2} :=
        interior_maximal (fun w hw => by
          simp only [Set.mem_ofPred_eq] at hw ⊢
          exact le_of_lt hw) hopen
      exact ha.2 (hsub hlt)
    have hnorm : ‖(a : ℂ)‖ = (1:ℝ)/2 := le_antisymm hle (not_lt.mp hnotlt)
    have ha0 : (a : ℂ) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hnorm; norm_num at hnorm
    have h3 : clampDisc (2 * (a : ℂ)) = circlePoint (Complex.arg (a : ℂ)) := by
      refine Subtype.ext ?_
      rw [coe_clampDisc, clamp_eq_self (by rw [norm_mul, Complex.norm_ofNat, hnorm]; norm_num),
        circlePoint_coe]
      rw [exp_arg_mul_I_eq (a : ℂ) ha0, hnorm]
      norm_num
      ring
    rw [hf, hg]
    change F₁ (clampDisc (2 * (a : ℂ))) = Φ (Complex.arg (a : ℂ), 2 - 2 * ‖(a : ℂ)‖)
    rw [h3, hF₁bd, ← hone (Complex.arg (a : ℂ))]
    congr 1
    rw [hnorm]
    norm_num
  have hcontF : Continuous fun w : Disc =>
      if ‖(w : ℂ)‖ ≤ (1:ℝ)/2 then f w else g w :=
    continuous_if hfront hfmono hgclos
  refine ⟨⟨fun w : Disc => if ‖(w : ℂ)‖ ≤ (1:ℝ)/2 then f w else g w, hcontF⟩, ?_, ?_⟩
  · intro u v huv
    change (if ‖(u : ℂ)‖ ≤ (1:ℝ)/2 then f u else g u) =
      (if ‖(v : ℂ)‖ ≤ (1:ℝ)/2 then f v else g v) at huv
    rcases le_or_gt ‖(u : ℂ)‖ ((1:ℝ)/2) with hu | hu <;>
      rcases le_or_gt ‖(v : ℂ)‖ ((1:ℝ)/2) with hv | hv
    · -- both inner
      rw [if_pos hu, if_pos hv] at huv
      have h1 : clampDisc (2 * (u : ℂ)) = clampDisc (2 * (v : ℂ)) := hF₁ huv
      have hcu : ‖(2 : ℂ) * (u : ℂ)‖ ≤ 1 := by
        rw [norm_mul]; norm_num; linarith
      have hcv : ‖(2 : ℂ) * (v : ℂ)‖ ≤ 1 := by
        rw [norm_mul]; norm_num; linarith
      have h2 : (2 : ℂ) * (u : ℂ) = 2 * (v : ℂ) := by
        have h1' := congrArg (fun z : Disc => (z : ℂ)) h1
        rw [coe_clampDisc, coe_clampDisc, clamp_eq_self hcu, clamp_eq_self hcv] at h1'
        exact h1'
      exact Subtype.ext (mul_left_cancel₀ (two_ne_zero) h2)
    · -- `u` inner, `v` outer
      rw [if_pos hu, if_neg (not_le.mpr hv)] at huv
      have huv' : F₁ (clampDisc (2 * (u : ℂ))) = Φ (Complex.arg (v : ℂ), 2 - 2 * ‖(v : ℂ)‖) := huv
      refine absurd ?_ (havoid (Complex.arg (v : ℂ)) (2 - 2 * ‖(v : ℂ)‖)
        ⟨by linarith [hmem1 v], by linarith⟩ ?_)
      · exact ⟨clampDisc (2 * (u : ℂ)), huv'⟩
      · linarith
    · -- `u` outer, `v` inner
      rw [if_neg (not_le.mpr hu), if_pos hv] at huv
      have huv' : F₁ (clampDisc (2 * (v : ℂ))) = Φ (Complex.arg (u : ℂ), 2 - 2 * ‖(u : ℂ)‖) := huv.symm
      refine absurd ?_ (havoid (Complex.arg (u : ℂ)) (2 - 2 * ‖(u : ℂ)‖)
        ⟨by linarith [hmem1 u], by linarith⟩ ?_)
      · exact ⟨clampDisc (2 * (v : ℂ)), huv'⟩
      · linarith
    · -- both outer
      rw [if_neg (not_le.mpr hu), if_neg (not_le.mpr hv)] at huv
      have hs : (2 - 2 * ‖(u : ℂ)‖) ∈ Set.Icc 0 1 :=
        ⟨by linarith [hmem1 u], by linarith⟩
      have hs' : (2 - 2 * ‖(v : ℂ)‖) ∈ Set.Icc 0 1 :=
        ⟨by linarith [hmem1 v], by linarith⟩
      obtain ⟨hss, k, hk⟩ := hinj _ _ _ _ hs hs' huv
      have hu0 : (u : ℂ) ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hu; norm_num at hu
      have hv0 : (v : ℂ) ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hv; norm_num at hv
      have hnorm : ‖(u : ℂ)‖ = ‖(v : ℂ)‖ := by linarith
      have hexp : Complex.exp ((Complex.arg (v : ℂ) : ℝ) * Complex.I)
          = Complex.exp ((Complex.arg (u : ℂ) : ℝ) * Complex.I) := by
        rw [hk]
        have h2 : (((Complex.arg (u : ℂ) : ℝ) + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
            = (Complex.arg (u : ℂ) : ℂ) * Complex.I
              + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
          push_cast; ring
        rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      have hq : (u : ℂ) = (v : ℂ) := by
        calc (u : ℂ)
            = (‖(u : ℂ)‖ : ℂ) * Complex.exp ((Complex.arg (u : ℂ) : ℝ) * Complex.I) :=
              (Complex.norm_mul_exp_arg_mul_I (u : ℂ)).symm
          _ = (‖(v : ℂ)‖ : ℂ) * Complex.exp ((Complex.arg (v : ℂ) : ℝ) * Complex.I) := by
              rw [hnorm, ← hexp]
          _ = (v : ℂ) := Complex.norm_mul_exp_arg_mul_I (v : ℂ)
      exact Subtype.ext hq
  · intro θ
    have hnorm : ‖((circlePoint θ : Disc) : ℂ)‖ = 1 := norm_circlePoint θ
    have hgt : ¬ ‖((circlePoint θ : Disc) : ℂ)‖ ≤ (1:ℝ)/2 := by rw [hnorm]; norm_num
    change (if ‖((circlePoint θ : Disc) : ℂ)‖ ≤ (1:ℝ)/2 then f (circlePoint θ)
      else g (circlePoint θ)) = γ₀ θ
    rw [if_neg hgt, hg]
    change Φ (Complex.arg (((circlePoint θ : Disc) : ℂ)),
      2 - 2 * ‖((circlePoint θ : Disc) : ℂ)‖) = γ₀ θ
    have h0 : (2 : ℝ) - 2 * ‖((circlePoint θ : Disc) : ℂ)‖ = 0 := by rw [hnorm]; norm_num
    rw [h0, hzero]
    refine eq_of_exp_eq_periodic γ₀.periodic ?_
    rw [exp_arg_mul_I_eq (((circlePoint θ : Disc) : ℂ)) (Complex.exp_ne_zero _), hnorm,
      Complex.ofReal_one, div_one, circlePoint_coe]

end
end Work.Smooth.JordanSeparation
