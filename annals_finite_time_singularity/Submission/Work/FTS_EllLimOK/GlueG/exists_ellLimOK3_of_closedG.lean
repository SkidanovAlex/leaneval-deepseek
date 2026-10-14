import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_EllLimOK.FatouG
import Submission.Work.FTS_EllLimOK.Glue
import Submission.Work.FTS_EllLimOK.exists_ellLimOK3_of_closed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter Set

namespace Work.FTS_EllLimOK.GlueG

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The order-`3` jet limit is independent of the sequence, over `ClosedE3G` -/

/-- **The `C³`-jet limit does not depend on the sequence** (repaired-package form): under
`ClosedE3G`, if the `C³`-jets of `E (fn n)` converge to those of `Ψ` along one `LimSeq4` to `f`,
they do so along every `LimSeq4` to `f`.

This is `Work.FTS_EllLimOK.jconv3_transfer` with the hypothesis `ClosedE3` relaxed to
`ClosedE3G`: the interleaved sequence `ilv fn hn` is a `LimSeq4` again (`limSeq4_ilv`), and
`ClosedE3G` supplies a limit `Ψ'` together with `JConv3 (fun n => E (ilv fn hn n)) Ψ'`; the even
and the odd subsequence of that convergence are the two convergences at hand, and the jet limit is
unique in `𝓝`-limits. -/
theorem jconv3_transferG {α : ℝ} {E : Fn → Fn} (hcl : Work.FTS_EllLimOK.ClosedE3G α E)
    {fn hn : ℕ → Fn} {f Ψ : Fn}
    (hf : Work.FTS_EllLimOK.LimSeq4 α fn f) (hh : Work.FTS_EllLimOK.LimSeq4 α hn f)
    (hΨ : Work.FTS_EllLimOK.JConv3 (fun n => E (fn n)) Ψ) :
    Work.FTS_EllLimOK.JConv3 (fun n => E (hn n)) Ψ := by
  obtain ⟨Ψ', -, hJ'⟩ := hcl _ f (Work.FTS_EllLimOK.limSeq4_ilv hf hh)
  intro j i hji z θ hz
  have hlim := hJ' j i hji z θ hz
  have hev : Tendsto (fun n => Work.Spaces.mixed j i (E (fn n)) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i Ψ' z θ)) :=
    Tendsto.congr (fun n => by simp only [Function.comp, Work.FTS_EllLimOK.ilv_even])
      (hlim.comp Work.FTS_EllLimOK.tendsto_two_mul)
  have hod : Tendsto (fun n => Work.Spaces.mixed j i (E (hn n)) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i Ψ' z θ)) :=
    Tendsto.congr (fun n => by simp only [Function.comp, Work.FTS_EllLimOK.ilv_odd])
      (hlim.comp Work.FTS_EllLimOK.tendsto_two_mul_add_one)
  rw [tendsto_nhds_unique (hΨ j i hji z θ hz) hev]
  exact hod

/-! ## The main theorem -/

theorem exists_ellLimOK3_of_closedG {α : ℝ}
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (hsol : ∀ g, Work.FTS.ClassC.ClassC α g → Work.FTS.StrongGlobal.IsBslSolPos α g (E g))
    (hsm : ∀ g, Work.FTS.ClassC.ClassC α g →
      ContDiffOn ℝ 3 (Function.uncurry (E g)) Work.Construction.Qd)
    (hcl : Work.FTS_EllLimOK.ClosedE3G α E) :
    ∃ E' : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn,
      (∀ g, Work.FTS.ClassC.ClassC α g → E' g = E g) ∧ Work.FTS_EllLimOK.EllLimOK3 α E' := by
  have hC : ∀ g ∈ Work.FTS_EllLimOK.classCSub α,
      (g, E g) ∈ Work.FTS_EllLimOK.graphG3 α E hsm := by
    intro g hg
    exact ⟨⟨fun _ => g, Work.FTS_EllLimOK.limSeq4_const hg,
        fun _ _ _ _ _ _ => tendsto_const_nhds⟩, hsol g hg, hsm g hg⟩
  obtain ⟨E', hE'C, hE'G⟩ :=
    Work.FTS_EllLimOK.exists_section_extend (Work.FTS_EllLimOK.classCSub α)
      (Work.FTS_EllLimOK.graphG3 α E hsm) E hC
  refine ⟨E', fun g hg => hE'C g hg, ?_⟩
  intro fn f B h1 h2 h4 h3
  have hL : Work.FTS_EllLimOK.LimSeq4 α fn f := ⟨h1, ⟨B, h2⟩, h4, h3⟩
  obtain ⟨Ψ, hfat, hJ⟩ := hcl fn f hL
  have hfL : f ∈ (Work.FTS_EllLimOK.graphG3 α E hsm).map (LinearMap.fst ℝ Fn Fn) :=
    Submodule.mem_map.mpr
      ⟨(f, Ψ), ⟨⟨fn, hL, hJ⟩, hfat.sol, hfat.smooth⟩, rfl⟩
  obtain ⟨⟨kn, hkn, hJk⟩, hlaw, hsmooth⟩ := hE'G f hfL
  refine ⟨hlaw, hsmooth, fun j i hji z θ hz => ?_⟩
  have := jconv3_transferG hcl hkn hL hJk j i hji z θ hz
  refine Tendsto.congr (fun n => ?_) this
  simp only [hE'C (fn n) (h1 n)]

end Work.FTS_EllLimOK.GlueG
