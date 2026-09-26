import Mathlib
import Submission.Work.Smooth.SphereJordan.annulusInterpolation
import Submission.Work.Smooth.SphereJordan.PCopy.annulusCuts
import Submission.Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic
import Submission.Work.Smooth.SphereJordan.injOn_circlePoint

namespace Work.SphereJordan

open Set

noncomputable section

/-!
# The reparametrisation of the inner circle of the model disc

The lemma `Work.SphereJordan.pcannulusInnerReparam` of Pardon's cut-and-paste: if a continuous
injection `pcG` of the model disc `𝔻` fixes the boundary circle pointwise and maps the inner circle
of radius `1/2` into the trace of a simple closed plane curve `γ` (which lies in the open unit
disc), then — after reparametrising the disc by a homeomorphism fixing `∂𝔻` pointwise — the inner
circle parametrises `γ` itself, up to one of the two orientations.

Everything is reduced to two statements that are already available in the workspace:

* `Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic`: a simple closed curve whose trace is
  contained in the trace of another has the same trace;
* `Work.Smooth.SphereJordan.exists_continuous_lift_periodic` and the sign lemma
  `Work.Smooth.SphereJordan.lift_shift_eq_pm_one`: a continuous periodic curve whose trace is
  contained in the trace of a simple closed curve lifts to the parameter, with shift `±2π` over a
  period (`pcexists_monotone_lift` below, which also records that the lift is strictly monotone with
  that sign);
* `Work.Smooth.SphereJordan.annulusInterpolation`: the interpolation homeomorphism of the disc
  which fixes `∂𝔻` pointwise and acts on the inner circle by a prescribed strictly increasing
  lift of a circle homeomorphism.

The reparametrisation is then simply `F := pcG ∘ Φ`, where `Φ` is the interpolation homeomorphism
built from the (re-oriented) lift.
-/

/-! ## Elementary facts about the inner circle of the model disc -/

/-- The parametrisation of the inner circle of `𝔻` is `2π`-periodic. -/
theorem pchalfCirclePoint_add_two_pi (θ : ℝ) :
    Work.Smooth.SphereJordan.halfCirclePoint (θ + 2 * Real.pi) =
      Work.Smooth.SphereJordan.halfCirclePoint θ := by
  apply Subtype.ext
  rw [Work.Smooth.SphereJordan.halfCirclePoint_coe, Work.Smooth.SphereJordan.halfCirclePoint_coe,
    Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  congr 1
  rw [show ((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I
      = (θ : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The parametrisation of the inner circle of `𝔻` is continuous. -/
theorem pccontinuous_halfCirclePoint :
    Continuous (Work.Smooth.SphereJordan.halfCirclePoint : ℝ → Work.Smooth.SphereJordan.Disc) := by
  have hcoe : Continuous fun θ : ℝ =>
      ((Work.Smooth.SphereJordan.halfCirclePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ) := by
    have h : (fun θ : ℝ =>
        ((Work.Smooth.SphereJordan.halfCirclePoint θ : Work.Smooth.SphereJordan.Disc) : ℂ))
        = fun θ : ℝ => (1 / 2 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      funext θ
      rw [Work.Smooth.SphereJordan.halfCirclePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
    rw [h]
    fun_prop
  exact Continuous.subtype_mk hcoe (fun θ => (Work.Smooth.SphereJordan.halfCirclePoint θ).2)

/-- The parametrisation of the inner circle of `𝔻` is injective on one period. -/
theorem pchalfCirclePoint_injOn_Ico :
    Set.InjOn (Work.Smooth.SphereJordan.halfCirclePoint : ℝ → Work.Smooth.SphereJordan.Disc)
      (Set.Ico 0 (2 * Real.pi)) := by
  intro a ha b hb hab
  have hc : ((Work.Smooth.Jordan.circlePoint a : Work.Smooth.Jordan.Disc) : ℂ) =
      ((Work.Smooth.Jordan.circlePoint b : Work.Smooth.Jordan.Disc) : ℂ) := by
    have h' := congrArg
      (fun z : Work.Smooth.SphereJordan.Disc => ((z : Work.Smooth.SphereJordan.Disc) : ℂ)) hab
    simp only [Work.Smooth.SphereJordan.halfCirclePoint_coe] at h'
    exact mul_left_cancel₀ (by norm_num : ((1 / 2 : ℂ)) ≠ 0) h'
  exact Work.Smooth.SphereJordan.injOn_circlePoint ha hb (Subtype.ext hc)

/-! ## The monotone lift of a periodic curve through a simple closed curve -/

/-- **The monotone lift of a periodic curve through a simple closed curve.**

Let `f, g : ℝ → ℂ` be continuous `2π`-periodic curves, both injective on one period, with the trace
of `f` contained in the trace of `g`.  Then `f` lifts to the parameter of `g` through a continuous
strictly monotone `Ψ`, whose shift over one period is `d * 2π` with `d = 1` (and `Ψ` strictly
increasing) or `d = -1` (and `Ψ` strictly decreasing).

The lift itself is `Work.Smooth.SphereJordan.exists_continuous_lift_periodic`; the shift over one
period is an integer multiple of `2π` by injectivity of `g`, it is constant because it is a
continuous function into the discrete set `2πℤ`, the integer `d` is `±1` by
`Work.Smooth.SphereJordan.lift_shift_eq_pm_one`, and the sign of `d` forces the orientation of the
(continuous, injective) lift `Ψ`. -/
theorem pcexists_monotone_lift {f g : ℝ → ℂ} (hf : Continuous f)
    (hfp : Function.Periodic f (2 * Real.pi)) (hfi : Set.InjOn f (Set.Ico 0 (2 * Real.pi)))
    (hg : Continuous g) (hgp : Function.Periodic g (2 * Real.pi))
    (hgi : Set.InjOn g (Set.Ico 0 (2 * Real.pi))) (hsub : Set.range f ⊆ Set.range g) :
    ∃ (Ψ : ℝ → ℝ) (d : ℤ), Continuous Ψ ∧ (∀ x : ℝ, g (Ψ x) = f x) ∧
      (∀ θ : ℝ, Ψ (θ + 2 * Real.pi) = Ψ θ + (d : ℝ) * (2 * Real.pi)) ∧
      ((d = 1 ∧ StrictMono Ψ) ∨ (d = -1 ∧ StrictAnti Ψ)) := by
  obtain ⟨Ψ, hΨc, hΨspec⟩ :=
    Work.Smooth.SphereJordan.exists_continuous_lift_periodic hf hfp hfi hg hgp hgi hsub
  have hL : (0 : ℝ) < 2 * Real.pi := by positivity
  -- the shift over one period lies in the period lattice
  have hmem : ∀ θ : ℝ, Ψ (θ + 2 * Real.pi) - Ψ θ ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
    intro θ
    have hge : g (Ψ (θ + 2 * Real.pi)) = g (Ψ θ) := by
      rw [hΨspec, hΨspec, hfp θ]
    obtain ⟨k, hk⟩ := Work.Smooth.SphereJordan.exists_int_sub_eq_of_periodic_injOn hgp hgi hge
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by rw [zsmul_eq_mul]; exact hk.symm⟩
  -- ... hence it is constant, being a continuous map into a discrete group
  have hconst : ∀ x : ℝ, Ψ (x + 2 * Real.pi) - Ψ x = Ψ (2 * Real.pi) - Ψ 0 := by
    let δ : ℝ → AddSubgroup.zmultiples (2 * Real.pi) :=
      fun x => ⟨Ψ (x + 2 * Real.pi) - Ψ x, hmem x⟩
    have hδc : Continuous δ :=
      Continuous.subtype_mk ((hΨc.comp (continuous_id.add continuous_const)).sub hΨc) hmem
    have hlc : IsLocallyConstant δ := (IsLocallyConstant.iff_continuous δ).mpr hδc
    intro x
    have h2 := hlc.apply_eq_of_isPreconnected (s := Set.univ) isPreconnected_univ
      (Set.mem_univ (0 : ℝ)) (Set.mem_univ x)
    have h3 : (δ 0 : ℝ) = (δ x : ℝ) := congrArg Subtype.val h2
    simp only [δ, zero_add] at h3
    rw [← h3]
  obtain ⟨d, hd⟩ := AddSubgroup.mem_zmultiples_iff.mp (by
    have h := hmem 0
    rw [hconst 0] at h
    exact h)
  have hd' : (d : ℝ) * (2 * Real.pi) = Ψ (2 * Real.pi) - Ψ 0 := by rw [← hd, zsmul_eq_mul]
  have hshift : ∀ θ : ℝ, Ψ (θ + 2 * Real.pi) = Ψ θ + (d : ℝ) * (2 * Real.pi) := by
    intro θ
    have h := hconst θ
    linarith
  -- the lift is injective modulo the period of `f`
  have hmod : ∀ x y : ℝ, (∃ k : ℤ, Ψ x - Ψ y = (k : ℝ) * (2 * Real.pi)) →
      ∃ k : ℤ, x - y = (k : ℝ) * (2 * Real.pi) := by
    intro x y hk
    obtain ⟨k, hk⟩ := hk
    have hgy : g (Ψ x) = g (Ψ y) := by
      have hΨxy : Ψ x = Ψ y + (k : ℝ) * (2 * Real.pi) := by linarith
      rw [hΨxy]
      exact hgp.int_mul k (Ψ y)
    rw [hΨspec, hΨspec] at hgy
    exact Work.Smooth.SphereJordan.exists_int_sub_eq_of_periodic_injOn hfp hfi hgy
  have hdpm : d = 1 ∨ d = -1 :=
    Work.Smooth.SphereJordan.lift_shift_eq_pm_one Ψ hΨc d hshift hmod
  -- `Ψ` is injective: a repeated value would repeat it at two different parameters of `f`
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    obtain ⟨k, hk⟩ := hmod x y ⟨0, by rw [hxy]; ring⟩
    have hy : y = x + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
      have h2 : ((-k : ℤ) : ℝ) = -(k : ℝ) := by push_cast; ring
      rw [h2]
      linarith
    have hsh := Work.Smooth.SphereJordan.shift_int_two_pi Ψ d hshift x (-k)
    have hshy : Ψ y = Ψ x + ((-k : ℤ) : ℝ) * (d : ℝ) * (2 * Real.pi) := by
      rw [hy]
      exact hsh
    rcases eq_or_ne k 0 with hk0 | hk0
    · have hk0' : ((-k : ℤ) : ℝ) = 0 := by rw [hk0]; norm_num
      rw [hy, hk0']
      ring
    · exfalso
      have hzero : ((-k : ℤ) : ℝ) * (d : ℝ) * (2 * Real.pi) = 0 := by
        rw [hshy] at hxy
        linarith
      have hdne : (d : ℝ) ≠ 0 := by
        rcases hdpm with h | h <;> rw [h] <;> norm_num
      have hkne : ((-k : ℤ) : ℝ) ≠ 0 := by
        have h': (-k : ℤ) ≠ 0 := by omega
        exact_mod_cast h'
      exact (mul_ne_zero (mul_ne_zero hkne hdne) (ne_of_gt hL)) hzero
  have hmono : StrictMono Ψ ∨ StrictAnti Ψ := hΨc.strictMono_of_inj hΨinj
  rcases hdpm with hd1 | hdm1
  · refine ⟨Ψ, d, hΨc, hΨspec, hshift, Or.inl ⟨hd1, ?_⟩⟩
    rcases hmono with h | h
    · exact h
    · exfalso
      have h0 := hshift 0
      rw [hd1] at h0
      simp only [zero_add, Int.cast_one, one_mul] at h0
      have := h hL
      linarith
  · refine ⟨Ψ, d, hΨc, hΨspec, hshift, Or.inr ⟨hdm1, ?_⟩⟩
    rcases hmono with h | h
    · exfalso
      have h0 := hshift 0
      rw [hdm1] at h0
      simp only [zero_add, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h0
      have := h hL
      linarith
    · exact h

/-! ## The requested lemma -/

theorem pcannulusInnerReparam {γ : Work.Smooth.Jordan.PlaneCurve}
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (pcG : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc))
    (hGinj : Function.Injective pcG)
    (hGbd : ∀ θ : ℝ, pcG (Work.Smooth.SphereJordan.circlePoint θ) =
      Work.Smooth.SphereJordan.circlePoint θ)
    (hGim : ∀ θ : ℝ, ∃ θ' : ℝ,
      ((pcG (Work.Smooth.SphereJordan.halfCirclePoint θ) : Work.Smooth.SphereJordan.Disc) : ℂ) =
        γ.γ θ') :
    ∃ (F : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc)) (s : ℝ),
      (s = 1 ∨ s = -1) ∧ Function.Injective F ∧
      (∀ θ : ℝ, F (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ θ : ℝ, ((F (Work.Smooth.SphereJordan.halfCirclePoint (s * θ)) :
          Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ) := by
  -- the curve traced by `pcG` on the inner circle
  set β : ℝ → ℂ := fun θ =>
    ((pcG (Work.Smooth.SphereJordan.halfCirclePoint θ) : Work.Smooth.SphereJordan.Disc) : ℂ)
    with hβdef
  have hβc : Continuous β := by
    rw [hβdef]
    exact continuous_subtype_val.comp (pcG.continuous.comp pccontinuous_halfCirclePoint)
  have hβp : Function.Periodic β (2 * Real.pi) := by
    intro θ
    show ((pcG (Work.Smooth.SphereJordan.halfCirclePoint (θ + 2 * Real.pi)) :
      Work.Smooth.SphereJordan.Disc) : ℂ) =
      ((pcG (Work.Smooth.SphereJordan.halfCirclePoint θ) : Work.Smooth.SphereJordan.Disc) : ℂ)
    rw [pchalfCirclePoint_add_two_pi]
  have hβinj : Set.InjOn β (Set.Ico 0 (2 * Real.pi)) := by
    intro a ha b hb hab
    apply pchalfCirclePoint_injOn_Ico ha hb
    apply hGinj
    exact Subtype.ext hab
  have hβsub : Set.range β ⊆ Set.range γ.γ := by
    rintro _ ⟨θ, rfl⟩
    obtain ⟨θ', hθ'⟩ := hGim θ
    exact ⟨θ', hθ'.symm⟩
  -- the traces of `β` and `γ` agree
  have hreq : Set.range β = Set.range γ.γ :=
    Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic hβc hβp hβinj
      γ.cont γ.periodic S.simple hβsub
  -- lift `γ` through `β`
  obtain ⟨χ, d, hχc, hχspec, hχshift, hχmono⟩ :=
    pcexists_monotone_lift γ.cont γ.periodic S.simple hβc hβp hβinj
      (by rw [hreq])
  set e : ℝ := (d : ℝ) with he
  have hepm : e = 1 ∨ e = -1 := by
    rcases hχmono with ⟨h1, -⟩ | ⟨hm1, -⟩
    · left; rw [he, h1]; norm_num
    · right; rw [he, hm1]; norm_num
  have hee : e * e = 1 := by
    rcases hepm with h | h <;> rw [h] <;> norm_num
  -- re-orient the lift so that it is strictly increasing
  set χt : ℝ → ℝ := fun θ => χ (e * θ) with hχt
  have hχtc : Continuous χt := by
    rw [hχt]
    exact hχc.comp (continuous_const.mul continuous_id)
  have hχtshift : ∀ θ : ℝ, χt (θ + 2 * Real.pi) = χt θ + 2 * Real.pi := by
    intro θ
    have harg : e * (θ + 2 * Real.pi) = e * θ + (d : ℝ) * (2 * Real.pi) := by
      rw [he]; ring
    show χ (e * (θ + 2 * Real.pi)) = χ (e * θ) + 2 * Real.pi
    rw [harg, Work.Smooth.SphereJordan.shift_int_two_pi χ d hχshift (e * θ) d]
    have hdd : (d : ℝ) * (d : ℝ) = 1 := by rw [← he]; exact hee
    rw [hdd]; ring
  have hχtmono : StrictMono χt := by
    rcases hχmono with ⟨hd1, hm⟩ | ⟨hdm1, ha⟩
    · have he1 : e = 1 := by rw [he, hd1]; norm_num
      intro x y hxy
      show χ (e * x) < χ (e * y)
      rw [he1, one_mul, one_mul]
      exact hm hxy
    · have hem1 : e = -1 := by rw [he, hdm1]; norm_num
      intro x y hxy
      show χ (e * x) < χ (e * y)
      rw [hem1, neg_one_mul, neg_one_mul]
      exact ha (neg_lt_neg_iff.mpr hxy)
  -- the interpolation homeomorphism of the disc
  obtain ⟨Φ, hΦbd, hΦhalf, -⟩ :=
    Work.Smooth.SphereJordan.annulusInterpolation χt hχtc hχtmono hχtshift
  refine ⟨pcG.comp ⟨Φ, Φ.continuous⟩, e, hepm, ?_, ?_, ?_⟩
  · intro a b hab
    exact Φ.injective (hGinj (by simpa using hab))
  · intro θ
    show pcG (Φ (Work.Smooth.SphereJordan.circlePoint θ)) = Work.Smooth.SphereJordan.circlePoint θ
    rw [hΦbd θ, hGbd θ]
  · intro θ
    show ((pcG (Φ (Work.Smooth.SphereJordan.halfCirclePoint (e * θ))) :
      Work.Smooth.SphereJordan.Disc) : ℂ) = γ.γ θ
    rw [hΦhalf (e * θ)]
    have harg : χt (e * θ) = χ θ := by
      show χ (e * (e * θ)) = χ θ
      congr 1
      rw [← mul_assoc, hee, one_mul]
    rw [harg]
    show β (χ θ) = γ.γ θ
    exact hχspec θ

end

end Work.SphereJordan
