/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.exists_ellLimOK3_of_closed` — the order-3 glue

This is the order-`3` analogue of `Work.FTS_EllLimOK.exists_ellLimOK_of_closed` (`Glue.lean`):
a linear `E` that solves the elliptic law on the class `C`, is `C³` on `Qd` there, and is
*order-`3` closed* (`ClosedE3`), can be modified **off the class `C`** into a linear operator
satisfying the order-`3` limit closure (1a′) `EllLimOK3 α E'`.

The proof is the same abstract linear-algebra argument as at order `2`
(`exists_section_extend` applied to the graph of the limit process), the only changes being

* the graph submodule `graphG3` carries `C³`-regularity instead of `C²`, and its witness of
  convergence is `JConv3` (all mixed jets of total order `≤ 3`) instead of `JConv`;
* the jet limit of `E` along a `LimSeq4` is independent of the sequence (`jconv3_transfer`,
  the order-`3` form of `Glue.jconv_transfer`, proved by interleaving the two sequences and
  applying `ClosedE3`).

The remaining ingredients (`exists_section_extend`, `limSeq4_add`, `limSeq4_smul`,
`limSeq4_const`, `mixed_add_Qd`, `IsBslSolPos_add`, `isBslSolPos_smul'`, `isBslSolPos_zero`)
are imported verbatim from `Glue.lean`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.Closed3
import Submission.Work.FTS_EllLimOK.Glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter Set

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## `JConv3` is closed under the vector space operations -/

/-- `JConv3` is additive (the two limits are `C³` on the open quadrant, so the Leibniz-free
additivity of the mixed blocks is available). -/
theorem jconv3_add {Ψn Φn : ℕ → Fn} {Ψ Φ : Fn}
    (hΨ : JConv3 Ψn Ψ) (hΦ : JConv3 Φn Φ)
    (hΨn : ∀ n, ContDiffOn ℝ 3 (Function.uncurry (Ψn n)) Work.Construction.Qd)
    (hΦn : ∀ n, ContDiffOn ℝ 3 (Function.uncurry (Φn n)) Work.Construction.Qd)
    (hΨc : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hΦc : ContDiffOn ℝ 3 (Function.uncurry Φ) Work.Construction.Qd) :
    JConv3 (fun n => Ψn n + Φn n) (Ψ + Φ) := by
  intro j i hji z θ hz
  have hseq : (fun n => Work.Spaces.mixed j i (Ψn n + Φn n) z θ)
      = fun n => Work.Spaces.mixed j i (Ψn n) z θ + Work.Spaces.mixed j i (Φn n) z θ := by
    funext n
    exact mixed_add_Qd (hΨn n) (hΦn n) hji hz
  rw [hseq, mixed_add_Qd hΨc hΦc hji hz]
  exact (hΨ j i hji z θ hz).add (hΦ j i hji z θ hz)

/-- `JConv3` is homogeneous. -/
theorem jconv3_smul (c : ℝ) {Ψn : ℕ → Fn} {Ψ : Fn} (hΨ : JConv3 Ψn Ψ) :
    JConv3 (fun n => c • Ψn n) (c • Ψ) := by
  intro j i hji z θ hz
  show Tendsto (fun n => Work.Spaces.mixed j i (c • Ψn n) z θ) atTop
    (𝓝 (Work.Spaces.mixed j i (c • Ψ) z θ))
  simp only [Work.FTS.EllipticEst.mixed_smul, Pi.smul_apply, smul_eq_mul]
  exact (hΨ j i hji z θ hz).const_mul c

/-- `JConv3` holds for the constant zero sequence. -/
theorem jconv3_zero : JConv3 (fun _ : ℕ => (0 : Fn)) (0 : Fn) := by
  intro j i _ z θ _
  exact tendsto_const_nhds

/-! ## The order-`3` jet limit does not depend on the sequence -/

/-- **The `C³`-jet limit does not depend on the sequence**: under `ClosedE3`, if the jets of
`E (fn n)` converge to those of `Ψ` along one `LimSeq4` to `f`, they do so along every `LimSeq4`
to `f`.  (The order-`3` form of `Glue.jconv_transfer`; the interleaved sequence is a `LimSeq4`
again — `limSeq4_ilv` — and `ClosedE3` supplies its jet limit, to which the even and the odd
subsequence both converge.) -/
theorem jconv3_transfer {α : ℝ} {E : Fn → Fn} (hcl : ClosedE3 α E) {fn hn : ℕ → Fn} {f Ψ : Fn}
    (hf : LimSeq4 α fn f) (hh : LimSeq4 α hn f) (hΨ : JConv3 (fun n => E (fn n)) Ψ) :
    JConv3 (fun n => E (hn n)) Ψ := by
  obtain ⟨Ψ', -, hJ'⟩ := hcl _ f (limSeq4_ilv hf hh)
  intro j i hji z θ hz
  have hlim := hJ' j i hji z θ hz
  have hev : Tendsto (fun n => Work.Spaces.mixed j i (E (fn n)) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i Ψ' z θ)) :=
    Tendsto.congr (fun n => by simp only [Function.comp, ilv_even]) (hlim.comp tendsto_two_mul)
  have hod : Tendsto (fun n => Work.Spaces.mixed j i (E (hn n)) z θ) atTop
      (𝓝 (Work.Spaces.mixed j i Ψ' z θ)) :=
    Tendsto.congr (fun n => by simp only [Function.comp, ilv_odd])
      (hlim.comp tendsto_two_mul_add_one)
  rw [tendsto_nhds_unique (hΨ j i hji z θ hz) hev]
  exact hod

/-! ## The order-`3` graph submodule -/

/-- **The order-`3` graph**: pairs `(f, Ψ)` where `Ψ` is a `C³` solution for `f` and the
`C³`-jets of `E (fn n)` converge to those of `Ψ` along some (hence every) `LimSeq4` to `f`.
This is `Glue.graphG` with `2` replaced by `3`. -/
def graphG3 (α : ℝ) (E : Fn →ₗ[ℝ] Fn)
    (hsm : ∀ g, Work.FTS.ClassC.ClassC α g →
      ContDiffOn ℝ 3 (Function.uncurry (E g)) Work.Construction.Qd) :
    Submodule ℝ (Fn × Fn) where
  carrier := {p | (∃ fn : ℕ → Fn, LimSeq4 α fn p.1 ∧ JConv3 (fun n => E (fn n)) p.2) ∧
    Work.FTS.StrongGlobal.IsBslSolPos α p.1 p.2 ∧
    ContDiffOn ℝ 3 (Function.uncurry p.2) Work.Construction.Qd}
  zero_mem' := by
    refine ⟨⟨fun _ => 0, limSeq4_const (Work.FTS.ClassC.classC_zero α), ?_⟩,
      isBslSolPos_zero α, contDiffOn_const⟩
    intro j i _ z θ _
    simp only [map_zero]
    exact tendsto_const_nhds
  add_mem' := by
    rintro ⟨f, Ψ⟩ ⟨h, Φ⟩ ⟨⟨fn, hfn, hJf⟩, hlf, hsf⟩ ⟨⟨hn, hhn, hJh⟩, hlh, hsh⟩
    refine ⟨⟨fun n => fn n + hn n, limSeq4_add hfn hhn, ?_⟩,
      IsBslSolPos_add hlf hlh (hsf.of_le (by norm_num)) (hsh.of_le (by norm_num)), hsf.add hsh⟩
    have hmap : (fun n => E (fn n + hn n)) = fun n => E (fn n) + E (hn n) := by
      funext n
      rw [map_add]
    rw [hmap]
    exact jconv3_add hJf hJh (fun n => hsm _ (hfn.classC n)) (fun n => hsm _ (hhn.classC n))
      hsf hsh
  smul_mem' := by
    rintro c ⟨f, Ψ⟩ ⟨⟨fn, hfn, hJf⟩, hlf, hsf⟩
    refine ⟨⟨fun n => c • fn n, limSeq4_smul c hfn, ?_⟩, isBslSolPos_smul' hlf,
      hsf.const_smul c⟩
    have hmap : (fun n => E (c • fn n)) = fun n => c • E (fn n) := by
      funext n
      rw [map_smul]
    rw [hmap]
    exact jconv3_smul c hJf

/-! ## The main theorem -/

theorem exists_ellLimOK3_of_closed {α : ℝ} (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (hsol : ∀ g, Work.FTS.ClassC.ClassC α g → Work.FTS.StrongGlobal.IsBslSolPos α g (E g))
    (hsm : ∀ g, Work.FTS.ClassC.ClassC α g →
      ContDiffOn ℝ 3 (Function.uncurry (E g)) Work.Construction.Qd)
    (hcl : Work.FTS_EllLimOK.ClosedE3 α E) :
    ∃ E' : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn,
      (∀ g, Work.FTS.ClassC.ClassC α g → E' g = E g) ∧ Work.FTS_EllLimOK.EllLimOK3 α E' := by
  have hC : ∀ g ∈ classCSub α, (g, E g) ∈ graphG3 α E hsm := by
    intro g hg
    exact ⟨⟨fun _ => g, limSeq4_const hg, fun _ _ _ _ _ _ => tendsto_const_nhds⟩, hsol g hg,
      hsm g hg⟩
  obtain ⟨E', hE'C, hE'G⟩ := exists_section_extend (classCSub α) (graphG3 α E hsm) E hC
  refine ⟨E', fun g hg => hE'C g hg, ?_⟩
  intro fn f B h1 h2 h4 h3
  have hL : LimSeq4 α fn f := ⟨h1, ⟨B, h2⟩, h4, h3⟩
  obtain ⟨Ψ, hfat, hJ⟩ := hcl fn f hL
  have hfL : f ∈ (graphG3 α E hsm).map (LinearMap.fst ℝ Fn Fn) :=
    Submodule.mem_map.mpr
      ⟨(f, Ψ), ⟨⟨fn, hL, hJ⟩, hfat.sol, hfat.contDiffOn⟩, rfl⟩
  obtain ⟨⟨kn, hkn, hJk⟩, hlaw, hsmooth⟩ := hE'G f hfL
  refine ⟨hlaw, hsmooth, fun j i hji z θ hz => ?_⟩
  have := jconv3_transfer hcl hkn hL hJk j i hji z θ hz
  refine Tendsto.congr (fun n => ?_) this
  simp only [hE'C (fn n) (h1 n)]

end Work.FTS_EllLimOK
