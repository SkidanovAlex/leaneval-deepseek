import Mathlib
import Submission.Work.LayerCont.GapSetCompact
import Submission.Work.Asymptotics.continuousOn_Kfun_clean

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

/-- The point `i · max t 1` of `ℍ`, defined and continuous **in this module**: for `t ≥ 1` it is
`Work.Kernels.imagAxis t _`, and — unlike `imagAxis`, which carries a proof of `0 < t` — it is a
globally defined, globally continuous function of `t`.

It is a copy of `Work.Asymptotics.HalfFunnel.iAxisFun` (and of `Work.Asymptotics.BlLow.iAxisFun`)
deliberately kept file-local: the continuity proof below routes through
`continuous_induced_rng (f := UpperHalfPlane.coe)` + `fun_prop`, which is also how the library's
copies prove it (the `Continuous.subtype_mk` route fails on the definitional body of the
subtype point).  Keeping it local avoids the cross-module unification of the imported type with
`Prod.mk`-image sets, which is where the elaboration of the two-variable `.comp` used to blow up. -/
def axisPt (t : ℝ) : UpperHalfPlane :=
  ⟨((max t 1 : ℝ) : ℂ) * Complex.I, by simp [Complex.mul_im]⟩

lemma axisPt_coe (t : ℝ) : ((axisPt t : UpperHalfPlane) : ℂ) = ((max t 1 : ℝ) : ℂ) * Complex.I :=
  rfl

lemma axisPt_im (t : ℝ) : (axisPt t).im = max t 1 := by
  rw [← UpperHalfPlane.coe_im, axisPt_coe, Complex.mul_im]; simp

lemma continuous_axisPt : Continuous axisPt := by
  rw [continuous_induced_rng (f := UpperHalfPlane.coe)]
  show Continuous (fun t : ℝ => UpperHalfPlane.coe (axisPt t))
  simp only [axisPt_coe]
  fun_prop

lemma axisPt_eq_imagAxis {t : ℝ} (ht : 1 ≤ t) :
    axisPt t = Work.Kernels.imagAxis t (lt_of_lt_of_le one_pos ht) := by
  apply UpperHalfPlane.ext
  rw [axisPt_coe, show ((max t 1 : ℝ) : ℂ) = (t : ℂ) from by rw [max_eq_left ht]]
  rfl

/-- **The two-variable kernel is continuous on `gapSet K T A`** — now with the file-local
`axisPt`.  Composition of the *two-variable* `Work.Asymptotics.continuousOn_Kfun_clean` with
`(τ,t) ↦ (τ, axisPt t)`, then transfer to the `Kaxis` form by an `EqOn` (never by defeq: the
`Kaxis`-form and the `Kfun`-form are *not* globally equal — `Kaxis` is `0` for `t ≤ 0` — and the
defeq search between them must unfold the `dif` past the subtype coercions of `ℍ`, where it
diverges). -/
theorem continuousOn_gapSet (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} {T A : ℝ}
    (hclean : ∀ (τ : UpperHalfPlane), τ ∈ K → ∀ t : ℝ, 1 ≤ t → t ≤ T →
      A ≤ |t - τ.im| → Work.Kernels.jInvariantFun τ
        ≠ Work.Kernels.jInvariantFun (axisPt t)) :
    ContinuousOn (fun p : UpperHalfPlane × ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) p.1 p.2) (gapSet K T A) := by
  -- NOTE: every composition below is given its `f` and `g` explicitly.  Without them the
  -- unification against the *imported* statements (whose types contain big abstractions) is what
  -- made this declaration blow up; with them it elaborates immediately.  Same lesson as the `EqOn`
  -- route below: hand the elaborator the answers instead of letting it search.
  have hΨ : Continuous (fun p : UpperHalfPlane × ℝ => (p.1, axisPt p.2)) :=
    continuous_fst.prodMk (continuous_axisPt.comp continuous_snd)
  have hA : Continuous (fun p : UpperHalfPlane × ℝ =>
      Work.Asymptotics.AfunFun ℓ d p.1 (axisPt p.2)) :=
    Continuous.comp (f := fun p : UpperHalfPlane × ℝ => (p.1, axisPt p.2))
      (g := fun q : UpperHalfPlane × UpperHalfPlane => Work.Asymptotics.AfunFun ℓ d q.1 q.2)
      (Work.Asymptotics.continuous_AfunFun ℓ d) hΨ
  have hj1 : Continuous (fun p : UpperHalfPlane × ℝ => Work.Kernels.jInvariantFun p.1) :=
    Continuous.comp (f := fun p : UpperHalfPlane × ℝ => p.1)
      (g := fun τ : UpperHalfPlane => Work.Kernels.jInvariantFun τ)
      Work.Asymptotics.continuous_jInvariantFun' continuous_fst
  have hj2 : Continuous (fun p : UpperHalfPlane × ℝ => Work.Kernels.jInvariantFun (axisPt p.2)) :=
    Continuous.comp (f := fun p : UpperHalfPlane × ℝ => axisPt p.2)
      (g := fun τ : UpperHalfPlane => Work.Kernels.jInvariantFun τ)
      Work.Asymptotics.continuous_jInvariantFun'
      (continuous_axisPt.comp continuous_snd)
  have hj : Continuous (fun p : UpperHalfPlane × ℝ =>
      Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (axisPt p.2)) := hj1.sub hj2
  have hne : ∀ p ∈ gapSet K T A,
      Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (axisPt p.2) ≠ 0 := by
    intro p hp
    obtain ⟨hp1, hpg⟩ := hp
    exact sub_ne_zero.mpr (hclean p.1 hp1.1 p.2 hp1.2.1 hp1.2.2 hpg)
  have hdiv : ContinuousOn (fun p : UpperHalfPlane × ℝ =>
      Work.Asymptotics.AfunFun ℓ d p.1 (axisPt p.2)
        / (Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (axisPt p.2)))
      (gapSet K T A) :=
    hA.continuousOn.div hj.continuousOn hne
  have hKfun : ContinuousOn (fun p : UpperHalfPlane × ℝ =>
      Work.Kernels.Kfun ℓ d p.1 (axisPt p.2)) (gapSet K T A) := by
    refine hdiv.congr (fun p hp => ?_)
    rw [eq_div_iff (hne p hp)]
    exact Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd p.1 (axisPt p.2)
      (sub_ne_zero.mp (hne p hp))
  have hEqOn : Set.EqOn
      (fun p : UpperHalfPlane × ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) p.1 p.2)
      (fun p : UpperHalfPlane × ℝ => Work.Kernels.Kfun ℓ d p.1 (axisPt p.2)) (gapSet K T A) := by
    intro p hp
    obtain ⟨hp1, _⟩ := hp
    simp only [Work.Kernels.Kaxis,
      dif_pos (show (0 : ℝ) < p.2 by linarith [hp1.2.1])]
    rw [axisPt_eq_imagAxis hp1.2.1]
  exact hKfun.congr hEqOn

/-- **The gap-closer: a two-variable compactness bound for `Kaxis`.**

On a compact `K`, for `1 ≤ t ≤ T`, with cleanliness (`j τ ≠ j (i t)` — exactly what the trunc
mirror supplies on the retained set `E = Ici 1 \ Ioo (t₀-A) (t₀+A)`) and the guard
`A ≤ |t - τ.im|` making the exclusion quantitative, the kernel is bounded.

Pure compactness: `Work.LayerCont.gapSet K T A` is compact (`isCompact_gapSet`) and the kernel is
continuous on it (`continuousOn_gapSet`), so `IsCompact.exists_bound_of_continuousOn` applies.  No
pole analysis enters, so the bound is general in `T` and `A`: it covers the gap
`lowT < t < Tk` between `Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound_aux` (capped at
`t ≤ lowT = 3`) and `Work.Asymptotics.kernel_axis_bound` (starting at its internal cut), and can
also replace the former whenever cleanliness is available, as it is for the trunc mirror. -/
theorem GapBoundKaxis (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) {T A : ℝ}
    (hclean : ∀ (τ : UpperHalfPlane), τ ∈ K → ∀ t : ℝ, 1 ≤ t → t ≤ T →
      A ≤ |t - τ.im| → Work.Kernels.jInvariantFun τ
        ≠ Work.Kernels.jInvariantFun (axisPt t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ K → 1 ≤ t → t ≤ T →
      A ≤ |t - τ.im| → ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_gapSet hK T A).exists_bound_of_continuousOn
    (continuousOn_gapSet ℓ d hd hclean)
  exact ⟨max C 0, le_max_right _ _, fun τ t hτ ht htT hsep =>
    le_trans (hC (τ, t) ⟨⟨hτ, ⟨ht, htT⟩⟩, hsep⟩) (le_max_left C 0)⟩

end Work.LayerCont
