import Mathlib
import Submission.Work.NN.Assemble.Setup
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
import Submission.Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport
import Submission.Work.CR.Flat.Polydisc

namespace Work.NN.Assemble

open scoped ContDiff
open Set Filter

/-!
# `proj02_integrable_local`: the integrability identity is a local statement

The integrability of an almost complex structure is expressed (in the flat model `ℂⁿ`) by the
identity `proj02 J (dOne (dbarCn J w)) = 0` for every *globally* smooth function `w`.  For the
assembly it is needed for functions which are only smooth on an open set `U`; the passage from the
global to the local form is a purely local statement, and this file supplies it.

The two ingredients are

* `dbarCn` (hence `dOne (dbarCn J ·)` and `proj02`) depends only on the *germ* of `w` — this is
  `proj02_dbarCn_congr` below, built from `Filter.EventuallyEq.fderiv_eq`;
* a smooth function on `U` agrees near any point of `U` with a globally smooth function, obtained
  by multiplying it by a smooth bump whose topological support is contained in `U`
  (`Work.NN.Core.exists_contDiff_bump_of_isCompact_subset` and
  `Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport`).
-/

/-- **`dbarCn` depends only on the germ.**  If `f` and `g` agree in a neighbourhood of `z`, then
the `(0,1)`-derivatives `dbarCn J f z` and `dbarCn J g z` (which are real-linear forms) coincide. -/
lemma dbarCn_congr_of_eventuallyEq {n : ℕ} {J : Cn n → Cn n →L[ℝ] Cn n} {f g : Cn n → ℂ}
    {z : Cn n} (h : f =ᶠ[nhds z] g) : Work.NN.Core.dbarCn J f z = Work.NN.Core.dbarCn J g z := by
  simp only [Work.NN.Core.dbarCn, h.fderiv_eq]

/-- The same statement one function level up: the germs of `z ↦ dbarCn J f z` and
`z ↦ dbarCn J g z` agree. -/
lemma dbarCn_eventuallyEq {n : ℕ} {J : Cn n → Cn n →L[ℝ] Cn n} {f g : Cn n → ℂ}
    {z : Cn n} (h : f =ᶠ[nhds z] g) :
    (fun z' => Work.NN.Core.dbarCn J f z') =ᶠ[nhds z] (fun z' => Work.NN.Core.dbarCn J g z') :=
  h.eventuallyEq_nhds.mono fun _ hy => dbarCn_congr_of_eventuallyEq hy

/-- **The integrability expression is a germ-local functional.**  If `f` and `g` agree in a
neighbourhood of `z`, then the `(0,2)`-projection of `dOne (dbarCn J ·)` at `z` is the same for
`f` and for `g`.  Indeed `dbarCn J ·` involves one derivative, so `dbarCn J f` and `dbarCn J g`
agree near `z`; `dOne` involves one further derivative evaluated at `z`, so the two `2`-forms agree
at `z`; and `proj02` at `z` only reads the `2`-form at `z` and the structure at `z`. -/
lemma proj02_dbarCn_congr {n : ℕ} {J : Cn n → Cn n →L[ℝ] Cn n} {f g : Cn n → ℂ} {z : Cn n}
    (h : f =ᶠ[nhds z] g) (V W : Cn n) :
    Work.NN.Final.proj02 J
        (fun z' => Work.NN.Final.dOne (fun z'' => Work.NN.Core.dbarCn J f z'') z') z V W
      = Work.NN.Final.proj02 J
        (fun z' => Work.NN.Final.dOne (fun z'' => Work.NN.Core.dbarCn J g z'') z') z V W := by
  have hα : (fun z' => Work.NN.Core.dbarCn J f z')
      =ᶠ[nhds z] (fun z' => Work.NN.Core.dbarCn J g z') := dbarCn_eventuallyEq h
  have hvec : ∀ P : Cn n, (fun z' => Work.NN.Core.dbarCn J f z' P)
      =ᶠ[nhds z] (fun z' => Work.NN.Core.dbarCn J g z' P) :=
    fun P => hα.mono fun _ hy => congrArg (fun L : Cn n →L[ℝ] ℂ => L P) hy
  have hΩ : (fun z' => Work.NN.Final.dOne (fun z'' => Work.NN.Core.dbarCn J f z'') z') z
      = (fun z' => Work.NN.Final.dOne (fun z'' => Work.NN.Core.dbarCn J g z'') z') z := by
    funext X Y
    simp only [Work.NN.Final.dOne]
    rw [(hvec Y).fderiv_eq, (hvec X).fderiv_eq]
  simp only [Work.NN.Final.proj02, hΩ]

theorem proj02_integrable_local {n : ℕ} (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (hint : ∀ w : Work.NN.Core.Cn n → ℂ, (∀ m : ℕ, ContDiff ℝ m w) → ∀ z V W : Work.NN.Core.Cn n, Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A) (fun z' => Work.NN.Final.dOne (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) w z'') z') z V W = 0) : ∀ (U : Set (Work.NN.Core.Cn n)), IsOpen U → ∀ (v : Work.NN.Core.Cn n → ℂ), (∀ m : ℕ, ContDiffOn ℝ m v U) → ∀ z ∈ U, ∀ V W : Work.NN.Core.Cn n, Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A) (fun z' => Work.NN.Final.dOne (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) v z'') z') z V W = 0 := by
  intro U hU v hv z hz V W
  -- a smooth bump `χ`, supported in `U` and equal to `1` on an open neighbourhood `V₀ ∋ z`
  obtain ⟨χ, V₀, hχsm, _hχcpt, hχts, hV₀open, hzV₀, hχone⟩ :=
    Work.NN.Core.exists_contDiff_bump_of_isCompact_subset (K := {z}) (U := U)
      isCompact_singleton hU (by simpa using hz)
  set f : Cn n → ℂ := fun y => χ y * v y with hf
  -- `f` is globally smooth
  have hfsm : ∀ m : ℕ, ContDiff ℝ m f := fun m => by
    rw [hf]
    exact Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport hU hχsm hχts (hv m)
  -- and it agrees with `v` near `z`
  have hev : f =ᶠ[nhds z] v := by
    filter_upwards [hV₀open.mem_nhds (hzV₀ (Set.mem_singleton z))] with y hy
    rw [hf]
    simp [hχone y hy]
  -- the integrability expression is germ-local, so `hint` applies to `v`
  rw [← proj02_dbarCn_congr hev V W]
  exact hint f hfsm z V W

end Work.NN.Assemble
