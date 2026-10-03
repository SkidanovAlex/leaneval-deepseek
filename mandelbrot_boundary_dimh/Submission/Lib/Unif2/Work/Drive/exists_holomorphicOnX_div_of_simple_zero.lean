import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.exists_holomorphic_div_of_logPole
import Submission.Lib.Unif2.Work.Mori.holomorphicOnX_div

/-!
# Dividing a vanishing holomorphic function by a function with a simple zero

Let `A` be holomorphic on a Riemann surface `X` and vanish at `q`, and let `B` be holomorphic on `X`,
have a *simple* zero at `q` (`Submission.HasLogPoleAt q B`) and no other zero.  Then the quotient
`A / B`, a priori defined only on `X \ {q}`, is the restriction of a function holomorphic on all
of `X`: the singularity at `q` is removable because the zero of `A` at `q` has order at least one
while that of `B` has order exactly one.

This is the same statement as `Work.SimplyConnected.ABS.exists_holomorphic_div_of_logPole`, except
that the numerator is an *arbitrary* holomorphic function vanishing at `q` (not a member of the
extremal family, hence not required to be bounded by one), and, correspondingly, no hypothesis of
connectedness or second countability of `X` is needed.  Consequently the local removable-singularity
argument is reproduced here (`analyticAt_update_div_of_simple_zero`), since the copy in
`Work.SimplyConnected.ABS` carries the extra typeclass assumptions in its signature.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
set_option linter.unusedSectionVars false
noncomputable section
open Filter Set Classical

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The local removable singularity.**  If `f` is analytic at `a := (chartAt ℂ x₀) x₀` in the
chart at `x₀` and `f x₀ = 0`, and if `Φ` has a simple zero at `x₀` in the same chart, then
`w ↦ f (c.symm w) / Φ (c.symm w)` agrees near `a` with a function analytic at `a`; equivalently,
some `Function.update` of it at `a` is analytic there. -/
theorem analyticAt_update_div_of_simple_zero {x₀ : X} {f Φ : X → ℂ}
    (hf : AnalyticAt ℂ (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀))
    (hf0 : f x₀ = 0) (hΦsimple : Submission.HasLogPoleAt x₀ Φ) :
    ∃ V : ℂ, AnalyticAt ℂ (Function.update
        (fun w => f ((chartAt ℂ x₀).symm w) / Φ ((chartAt ℂ x₀).symm w))
          ((chartAt ℂ x₀) x₀) V) ((chartAt ℂ x₀) x₀) := by
  classical
  obtain ⟨H, hHana, hHne, hHeq⟩ := hΦsimple
  have hHev : ∀ᶠ w in nhds ((chartAt ℂ x₀) x₀), H w ≠ 0 :=
    hHana.continuousAt.eventually_ne hHne
  by_cases hZ : ∀ᶠ w in nhds ((chartAt ℂ x₀) x₀), (f ∘ (chartAt ℂ x₀).symm) w = 0
  · -- `f` vanishes identically near the base point: the quotient extends by `0`
    refine ⟨0, ?_⟩
    have heq : (fun _ : ℂ => (0 : ℂ)) =ᶠ[nhds ((chartAt ℂ x₀) x₀)]
        Function.update (fun w => f ((chartAt ℂ x₀).symm w) / Φ ((chartAt ℂ x₀).symm w))
          ((chartAt ℂ x₀) x₀) 0 := by
      filter_upwards [hZ, hHeq, hHev] with w hfw hΦw hHw
      by_cases hw : w = (chartAt ℂ x₀) x₀
      · rw [hw, Function.update_self]
      · rw [Function.update_apply, if_neg hw]
        have hfw' : f ((chartAt ℂ x₀).symm w) = 0 := by
          simpa only [Function.comp_apply] using hfw
        have hΦw' : Φ ((chartAt ℂ x₀).symm w) = (w - (chartAt ℂ x₀) x₀) * H w := by
          simpa only [Function.comp_apply] using hΦw
        rw [hfw', hΦw']
        simp
    exact analyticAt_const.congr heq
  · -- general case: factor `f ∘ c.symm = (w - a)^k • u` with `k ≥ 1`
    obtain ⟨k, u, huana, hune, hueq⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hZ
    have hk1 : 1 ≤ k := by
      by_contra h
      rw [not_le] at h
      have hk0 : k = 0 := Nat.lt_one_iff.mp h
      have h0 : (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) = 0 := by
        simp [Function.comp_apply, (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀), hf0]
      have h1 := hueq.self_of_nhds
      rw [h0, hk0, pow_zero, one_smul] at h1
      exact hune h1.symm
    set F₁ : ℂ → ℂ := fun w => (w - (chartAt ℂ x₀) x₀) ^ (k - 1) * u w with hF₁
    have hF₁ana : AnalyticAt ℂ F₁ ((chartAt ℂ x₀) x₀) :=
      ((analyticAt_id.sub analyticAt_const).pow _).mul huana
    have hfeq : (f ∘ (chartAt ℂ x₀).symm) =ᶠ[nhds ((chartAt ℂ x₀) x₀)]
        fun w => (w - (chartAt ℂ x₀) x₀) * F₁ w := by
      filter_upwards [hueq] with w hw
      rw [hw, hF₁, smul_eq_mul]
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [hj]
      simp only [Nat.succ_eq_add_one]
      rw [show j + 1 - 1 = j from by omega, pow_succ]
      ring
    refine ⟨F₁ ((chartAt ℂ x₀) x₀) / H ((chartAt ℂ x₀) x₀), ?_⟩
    have hHF : AnalyticAt ℂ (fun w => F₁ w / H w) ((chartAt ℂ x₀) x₀) :=
      hF₁ana.div hHana hHne
    refine hHF.congr ?_
    have hsub : ∀ᶠ w in nhds ((chartAt ℂ x₀) x₀),
        w - (chartAt ℂ x₀) x₀ ≠ 0 ∨ w = (chartAt ℂ x₀) x₀ := by
      filter_upwards with w
      by_cases h : w = (chartAt ℂ x₀) x₀
      · exact Or.inr h
      · exact Or.inl (sub_ne_zero.mpr h)
    filter_upwards [hHev, hHeq, hfeq, hsub] with w hHw hΦw hfw hsub
    by_cases hw : w = (chartAt ℂ x₀) x₀
    · subst hw
      rw [Function.update_self]
    · have hsub' : w - (chartAt ℂ x₀) x₀ ≠ 0 := sub_ne_zero.mpr hw
      rw [Function.update_apply, if_neg hw]
      rw [show f ((chartAt ℂ x₀).symm w) = (w - (chartAt ℂ x₀) x₀) * F₁ w from
          by simpa only [Function.comp_apply] using hfw,
        show Φ ((chartAt ℂ x₀).symm w) = (w - (chartAt ℂ x₀) x₀) * H w from
          by simpa only [Function.comp_apply] using hΦw]
      field_simp

/-- **Division of a holomorphic function vanishing at `q` by a function with a single simple zero at
`q`.**  The quotient on `X \ {q}` extends to a holomorphic function on all of `X`. -/
theorem exists_holomorphicOnX_div_of_simple_zero {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {q : X} {A B : X → ℂ}
    (hA : Submission.HolomorphicOnX A Set.univ) (hB : Submission.HolomorphicOnX B Set.univ)
    (hBpole : Submission.HasLogPoleAt q B) (hB0 : ∀ x : X, x ≠ q → B x ≠ 0) (hAq : A q = 0) :
    ∃ R : X → ℂ, Submission.HolomorphicOnX R Set.univ ∧ ∀ x : X, x ≠ q → R x = A x / B x := by
  classical
  have hAc : AnalyticAt ℂ (A ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q) := hA q (mem_univ q)
  obtain ⟨V, hVana⟩ := analyticAt_update_div_of_simple_zero (x₀ := q) hAc hAq hBpole
  let R : X → ℂ := fun x => if x = q then V else A x / B x
  have hRval : ∀ x : X, x ≠ q → R x = A x / B x := fun x hx => by
    simp only [R, if_neg hx]
  -- off the pole the quotient is holomorphic by the quotient rule
  have hdiv : Submission.HolomorphicOnX (fun y : X => A y / B y) ({q}ᶜ : Set X) :=
    Work.Mori.holomorphicOnX_div (hA.mono (Set.subset_univ _)) (hB.mono (Set.subset_univ _))
      (fun y hy => hB0 y (by simpa using hy))
  refine ⟨R, ?_, hRval⟩
  intro x _
  rw [Submission.HolomorphicOnXAt]
  by_cases hxq : x = q
  · -- at the pole: `R ∘ c.symm` agrees near `a` with the update of the chart quotient
    rw [hxq]
    set c : OpenPartialHomeomorph X ℂ := chartAt ℂ q with hc
    have hsrc : q ∈ c.source := mem_chart_source ℂ q
    have hRc : (R ∘ c.symm) =ᶠ[nhds (c q)]
        Function.update (fun w => A (c.symm w) / B (c.symm w)) (c q) V := by
      have hball : ∀ᶠ w in nhds (c q), w ∈ c.target :=
        c.open_target.mem_nhds (c.map_source hsrc)
      filter_upwards [hball] with w hw
      by_cases hwz : w = c q
      · rw [hwz, Function.comp_apply, Function.update_self]
        have hs : c.symm (c q) = q := c.left_inv hsrc
        rw [hs]
        simp only [R, if_pos rfl]
      · have hne : c.symm w ≠ q := by
          intro h
          have h2 : c (c.symm w) = c q := by rw [h]
          rw [c.right_inv hw] at h2
          exact hwz h2
        rw [Function.comp_apply, Function.update_apply, if_neg hwz, hRval _ hne]
    exact hVana.congr hRc.symm
  · -- off the pole: `R` agrees near `x` with `A / B`
    have hxq' : x ∈ ({q}ᶜ : Set X) := by simpa using hxq
    have h1 : AnalyticAt ℂ ((fun y : X => A y / B y) ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := hdiv x hxq'
    refine h1.congr ?_
    have hcont : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
      (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
    have hval : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
      (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
    have hmem : (chartAt ℂ x).symm ((chartAt ℂ x) x) ∈ ({q}ᶜ : Set X) := by
      rw [hval]; exact hxq'
    have hev : ∀ᶠ w in nhds ((chartAt ℂ x) x), (chartAt ℂ x).symm w ≠ q :=
      hcont.eventually (isOpen_compl_singleton.mem_nhds hmem)
    filter_upwards [hev] with w hw
    simp only [Function.comp_apply]
    rw [hRval _ hw]

end Work.Drive
