import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Lib.Unif2.Work.UnitGreen.Defs

/-!
# The quotient of a vanishing holomorphic function by a function with a simple zero

Let `g` be holomorphic on `X` and vanish at `x₀`, and let `Φ` have a *simple* zero at `x₀`
(`HasLogPoleAt x₀ Φ`) and no other zero.  Then the quotient `g / Φ`, which is a priori only
defined on `X \ {x₀}`, is the restriction of a holomorphic function on all of `X`: the singularity
at `x₀` is removable because `g` vanishes there to order at least one while `Φ` vanishes to order
exactly one.

The proof is completely local.  In the preferred chart at `x₀` we distinguish two cases:

* `g ∘ c.symm` vanishes identically near `a = c x₀`: then the quotient is identically zero on a
  punctured neighbourhood of `a`, so it extends by `0`;
* otherwise `g ∘ c.symm = (w - a)^k · u(w)` with `k ≥ 1`, `u` analytic at `a` and `u a ≠ 0`
  (`AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`), while `Φ ∘ c.symm = (w - a) · H(w)`
  with `H a ≠ 0`; hence the quotient equals `(w - a)^{k-1} u(w) / H(w)` on a punctured
  neighbourhood of `a`, which is analytic at `a`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
set_option linter.unusedSectionVars false
noncomputable section
open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The local removable singularity.**  If `f` is analytic at `a := (chartAt ℂ x₀) x₀` in the
chart at `x₀` and `f x₀ = 0`, and if `Φ` has a simple zero at `x₀` in the same chart, then
`w ↦ f (c.symm w) / Φ (c.symm w)` agrees near `a` with a function analytic at `a`; equivalently,
some `Function.update` of it at `a` is analytic there. -/
theorem analyticAt_quotient_update_of_simple_zero {x₀ : X} {f Φ : X → ℂ}
    (hf : AnalyticAt ℂ (f ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀))
    (hf0 : f x₀ = 0)
    (hΦsimple : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧ H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
      Filter.EventuallyEq (nhds ((chartAt ℂ x₀) x₀)) (Φ ∘ (chartAt ℂ x₀).symm)
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * H w)) :
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

/-- **Divisibility by a function with a single simple zero.**  Let `g` be a member of the extremal
family at `x₀` (holomorphic on `X`, bounded by one, vanishing at `x₀`), and let `Φ` be holomorphic
on `X`, with a *simple* zero at `x₀` and no other zero.  Then `g / Φ` on `X \ {x₀}` extends to a
holomorphic function on all of `X`. -/
theorem exists_holomorphic_div_of_logPole {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X} {g Φ : X → ℂ}
    (hg : g ∈ Submission.extremalFamily x₀)
    (hΦ : Submission.HolomorphicOnX Φ Set.univ) (hpole : Submission.HasLogPoleAt x₀ Φ)
    (hΦ0 : ∀ x : X, x ≠ x₀ → Φ x ≠ 0) :
    ∃ R : X → ℂ, Submission.HolomorphicOnX R Set.univ ∧
      ∀ x : X, x ≠ x₀ → R x = g x / Φ x := by
  classical
  have hgc : AnalyticAt ℂ (g ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) :=
    hg.1 x₀ (mem_univ x₀)
  have hsimple : ∃ H : ℂ → ℂ, AnalyticAt ℂ H ((chartAt ℂ x₀) x₀) ∧
      H ((chartAt ℂ x₀) x₀) ≠ 0 ∧
      Filter.EventuallyEq (nhds ((chartAt ℂ x₀) x₀)) (Φ ∘ (chartAt ℂ x₀).symm)
        (fun w : ℂ => (w - (chartAt ℂ x₀) x₀) * H w) := hpole
  obtain ⟨V, hVana⟩ := analyticAt_quotient_update_of_simple_zero (x₀ := x₀) (f := g) (Φ := Φ)
    hgc hg.2.2 hsimple
  let R : X → ℂ := fun x => if x = x₀ then V else g x / Φ x
  have hRval : ∀ x : X, x ≠ x₀ → R x = g x / Φ x := fun x hx => by
    simp only [R, if_neg hx]
  have hRc : (R ∘ (chartAt ℂ x₀).symm) =ᶠ[nhds ((chartAt ℂ x₀) x₀)]
      Function.update (fun w => g ((chartAt ℂ x₀).symm w) / Φ ((chartAt ℂ x₀).symm w))
        ((chartAt ℂ x₀) x₀) V := by
    have hball : ∀ᶠ w in nhds ((chartAt ℂ x₀) x₀), w ∈ (chartAt ℂ x₀).target :=
      (chartAt ℂ x₀).open_target.mem_nhds ((chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀))
    filter_upwards [hball] with w hw
    by_cases hwz : w = (chartAt ℂ x₀) x₀
    · rw [hwz]
      simp only [Function.comp_apply, R, (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀),
        ↓reduceIte, Function.update_self]
    · have hne : (chartAt ℂ x₀).symm w ≠ x₀ := by
        intro h
        have h2 : (chartAt ℂ x₀) ((chartAt ℂ x₀).symm w) = (chartAt ℂ x₀) x₀ := by rw [h]
        rw [(chartAt ℂ x₀).right_inv hw] at h2
        exact hwz h2
      rw [Function.comp_apply, Function.update_apply, if_neg hwz, hRval _ hne]
  have hRana₀ : AnalyticAt ℂ (R ∘ (chartAt ℂ x₀).symm) ((chartAt ℂ x₀) x₀) :=
    hVana.congr hRc.symm
  refine ⟨R, ?_, hRval⟩
  intro x hx
  rw [Submission.HolomorphicOnXAt]
  by_cases hxx : x = x₀
  · rw [hxx]
    exact hRana₀
  · have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
    have hΦne : (Φ ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := by
      have hval : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x := (chartAt ℂ x).left_inv hxsrc
      have hx0 : Φ x ≠ 0 := hΦ0 x hxx
      simpa only [Function.comp_apply, hval] using hx0
    have han : AnalyticAt ℂ ((g / Φ) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
      (hg.1 x (mem_univ x)).div (hΦ x (mem_univ x)) hΦne
    refine han.congr ?_
    have hopen : IsOpen ({x₀}ᶜ : Set X) := isClosed_singleton.isOpen_compl
    have hev1 : ∀ᶠ w in nhds ((chartAt ℂ x) x), (chartAt ℂ x).symm w ≠ x₀ := by
      have hcont : ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
        (chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hxsrc)
      have hval : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x := (chartAt ℂ x).left_inv hxsrc
      have hmem : (chartAt ℂ x).symm ((chartAt ℂ x) x) ∈ ({x₀}ᶜ : Set X) := by
        rw [hval]; exact hxx
      exact hcont.eventually (hopen.mem_nhds hmem)
    filter_upwards [hev1] with w hw
    show (g / Φ) ((chartAt ℂ x).symm w) = R ((chartAt ℂ x).symm w)
    rw [hRval _ hw, Pi.div_apply]

end Work.SimplyConnected.ABS
