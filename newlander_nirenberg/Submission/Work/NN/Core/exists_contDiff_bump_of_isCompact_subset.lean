import Mathlib
import Submission.Work.NN.Core.CnPert

namespace Work.NN.Core

open scoped ContDiff
open Set

/-- **Existence of a smooth bump on `ℂⁿ`.**

Given a compact set `K` contained in an open set `U` in the finite-dimensional space
`ℂⁿ = Fin n → ℂ`, there is a smooth `ℂ`-valued function `χ` with compact support,
whose topological support is contained in `U`, and which equals `1` on an open
neighbourhood `V` of `K`.

The construction is the standard one: shrink `U` twice. First choose an open `V₀` with
`K ⊆ V₀` and `closure V₀` compact and contained in `U` (intersecting `U` with a large
ball). Then choose an open `V` with `K ⊆ V` and `closure V ⊆ V₀`. Finally apply
`exists_contDiff_support_eq_eq_one_iff` to the open `V₀` and the closed `closure V`,
obtaining a smooth `f : ℂⁿ → ℝ` supported exactly on `V₀` and equal to `1` exactly on
`closure V`; the function `χ = f` viewed in `ℂ` is the required bump. -/
theorem exists_contDiff_bump_of_isCompact_subset {n : ℕ} {K U : Set (Cn n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : Cn n → ℂ) (V : Set (Cn n)), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ IsOpen V ∧ K ⊆ V ∧ ∀ y ∈ V, χ y = 1 := by
  -- A large ball containing `K`, so that we can later shrink `U` to a set with compact
  -- closure.
  obtain ⟨R, _hRpos, hRle⟩ := hK.isBounded.exists_pos_norm_le
  have hball : K ⊆ Metric.ball (0 : Cn n) (R + 1) := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (hRle x hx) (lt_add_one R)
  have hU' : IsOpen (U ∩ Metric.ball (0 : Cn n) (R + 1)) := hU.inter Metric.isOpen_ball
  have hKU' : K ⊆ U ∩ Metric.ball (0 : Cn n) (R + 1) := fun x hx => ⟨hKU hx, hball hx⟩
  -- First shrinking: an open `V₀ ⊇ K` whose closure is compact and contained in `U`.
  obtain ⟨V₀, hV₀o, hKV₀, hclV₀⟩ := hK.exists_isOpen_closure_subset (hU'.mem_nhdsSet.mpr hKU')
  have hclV₀U : closure V₀ ⊆ U := hclV₀.trans inter_subset_left
  have hclV₀cpt : IsCompact (closure V₀) :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Cn n) (R + 1)) isClosed_closure
      (hclV₀.trans (inter_subset_right.trans Metric.ball_subset_closedBall))
  -- Second shrinking: an open `V ⊇ K` with `closure V ⊆ V₀`.
  obtain ⟨V, hVo, hKV, hclV⟩ := hK.exists_isOpen_closure_subset (hV₀o.mem_nhdsSet.mpr hKV₀)
  -- A smooth function supported exactly on `V₀` and equal to `1` exactly on `closure V`.
  obtain ⟨f, hfdiff, _hfrange, hfsupp, hfone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₀o isClosed_closure hclV
  have htsuppf : tsupport f = closure V₀ := by rw [tsupport, hfsupp]
  have hsuppχ : Function.support (fun y : Cn n => (f y : ℂ)) = Function.support f := by
    ext y; simp [Function.mem_support, Complex.ofReal_eq_zero]
  have htsuppχ : tsupport (fun y : Cn n => (f y : ℂ)) = tsupport f := by
    rw [tsupport, tsupport, hsuppχ]
  refine ⟨fun y => (f y : ℂ), V, ?_, ?_, ?_, hVo, hKV, ?_⟩
  · have hcomp : (fun y : Cn n => (f y : ℂ)) = Complex.ofRealCLM ∘ f := rfl
    rw [hcomp]
    exact Complex.ofRealCLM.contDiff.comp hfdiff
  · change IsCompact (tsupport (fun y : Cn n => (f y : ℂ)))
    rw [htsuppχ, htsuppf]
    exact hclV₀cpt
  · rw [htsuppχ, htsuppf]
    exact hclV₀U
  · intro y hy
    have : f y = 1 := (hfone y).mp (subset_closure hy)
    simp [this]

end Work.NN.Core
