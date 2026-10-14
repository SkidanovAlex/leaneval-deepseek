import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongEps.L12.linPart_tendsto
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.PkgJets.boxDataD_uniform
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_RegExport.RXT.cone_induction
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.uncurry_partial_c1
-- ===== merged: Submission.Work.FTS.StrongEps.EpsWPLim.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsWPLim

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false


end Work.FTS.StrongEps.EpsWPLim
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.FatouG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The repaired hypothesis `HasPkgF`

`HasPkgE` (`PkgRepair`) is the frozen two packages plus the five fields they provably lack
(`PkgCos`, `PkgDecay`, `PkgStrip`, `PkgCorner`, `PkgSlice`).  The last missing piece for the
sequence-level Fatou step is a **quantitative** version of the pinning membership: `HkMem` alone
says that `HkSq α 0 (E g)` is *finite*, not that it is bounded by a constant times the source norm,
and the Fatou step needs one constant working for a whole sequence (`LimSeq4.bound` bounds
`Xn6 α (fn n)` but nothing else).  `PkgMemSq` is exactly that bound, for the two memberships the
uniqueness consumes.  (It is the level-`0` case of the paper's a priori estimate `prop:L2`; the
`∃C`-form of `phiTil_bundle_of_hasPkgD` cannot supply it.) -/

/-- **The quantitative `ℋ⁰`-membership field**, in the form the sequence-level Fatou step
consumes: for the two quantities `E g` and `E g/cos θ`, the `ℋ⁰`-membership, the *quantitative*
`HkSq` bound, and the *uniform-in-`z`* `θ`-slice bound, all relative to the source's `ℋ⁶`-norm.

The third clause is genuinely needed: `HkMem_fatou` bounds the `θ`-slice of the limit's integrand
by the `liminf` of the slices of the members, which is finite only under a bound that is uniform in
the sequence index; `HkMem` alone gives one finite value *per member*.  (The uniform-in-`z`
`θ`-slice form is the shape of the already-assumed `PkgSlice` field, so this is the same kind of
object, now for the solution itself.) -/
def PkgMemSq (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  ∀ g, Work.FTS.ClassC.ClassC α g →
    (Work.Spaces.HkMem α 0 (E g) ∧
        Work.Spaces.HkSq α 0 (E g) ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g ∧
        (∀ z ∈ Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (E g) z θ)
            ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g)) ∧
      (Work.Spaces.HkMem α 0 (fun z θ => E g z θ / Real.cos θ) ∧
        Work.Spaces.HkSq α 0 (fun z θ => E g z θ / Real.cos θ)
          ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g ∧
        (∀ z ∈ Work.Spaces.Iz,
          (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (fun z θ => E g z θ / Real.cos θ) z θ)
              ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g))

/-- **The fully repaired hypothesis**: the frozen packages plus `PkgCos`, `PkgDecay`, `PkgStrip`,
`PkgCorner`, `PkgSlice` (the five fields of `HasPkgE`) plus the quantitative membership field
`PkgMemSq`. -/
def HasPkgF (α Ce : ℝ) (E : Fn →ₗ[ℝ] Fn) : Prop :=
  HasPkg α Ce E ∧ PkgCos α E ∧ PkgDecay α E ∧ PkgStrip α E ∧
    PkgCorner α Ce E ∧ PkgSlice α Ce E ∧ PkgMemSq α Ce E

theorem HasPkgF.toHasPkg {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgF α Ce E) :
    HasPkg α Ce E := h.1



theorem HasPkgF.memSq {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn} (h : HasPkgF α Ce E) :
    PkgMemSq α Ce E := h.2.2.2.2.2.2





/-! ## The limit package and the order-`3` vocabulary -/


/-- **The limit package (minimal form).**  What the closure chain proves of a cluster limit, and
what the uniqueness argument consumes: the law, `C³`-regularity on the open quadrant, the two
`ℋ⁰`-memberships (`Ψ` and `Ψ/cos θ`) and the closed-box regularity. -/
structure FatouPkgG (α : ℝ) (f Ψ : Fn) : Prop where
  sol : Work.FTS.StrongGlobal.IsBslSolPos α f Ψ
  smooth : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd
  mem : Work.Spaces.HkMem α 0 Ψ
  memCos : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ)
  box : BoxReg Ψ

/-- **Order-`3` jet-cluster-limit over the repaired package.** -/
def IsJetLimit3G (α : ℝ) (E : Fn → Fn) (fn : ℕ → Fn) (f Ψ : Fn) : Prop :=
  FatouPkgG α f Ψ ∧
    ∃ σ : ℕ → ℕ, Tendsto σ atTop atTop ∧ JConv3 (fun n => E (fn (σ n))) Ψ

/-- **Order-`3` jet uniqueness over the repaired package**: two order-`3` jet-cluster-limits of the
same operator along the same sequence have the same `C³`-jets on the open quadrant.  (No package
hypothesis on `E` is needed.) -/
def ClosedUniq3G (α : ℝ) : Prop :=
  ∀ (E : Fn → Fn) (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∀ Ψ Ψ' : Fn, IsJetLimit3G α E fn f Ψ → IsJetLimit3G α E fn f Ψ' →
      ∀ j i : ℕ, j + i ≤ 3 → ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
        Work.Spaces.mixed j i Ψ z θ = Work.Spaces.mixed j i Ψ' z θ

/-- **Order-`3` closure over the repaired package**: along every `LimSeq4` the `C³`-jets of
`E (fn n)` converge, without reindexing, to the jets of a limit in `FatouPkgG`. -/
def ClosedE3G (α : ℝ) (E : Fn → Fn) : Prop :=
  ∀ (fn : ℕ → Fn) (f : Fn), LimSeq4 α fn f →
    ∃ Ψ : Fn, FatouPkgG α f Ψ ∧ JConv3 (fun n => E (fn n)) Ψ




/-! ## The sequence-level Fatou data over the repaired hypothesis -/



/-! ## The derivation of the sequence-level data from the field

`PkgMemSq` gives the two memberships with `HkSq ≤ Ce·Xn6 α g` *per source* `g`; along a `LimSeq4`
the source norms are bounded by `B` (`LimSeq4.bound`), so one constant works for the whole
sequence.  `BoxDataD` is the box clause (`PkgJets.boxDataD_uniform`). -/



end Work.FTS_EllLimOK
end
end
