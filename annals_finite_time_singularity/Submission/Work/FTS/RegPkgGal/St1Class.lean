/-
# `Work.FTS.RegPkgGal.St1Class` — the class data of the physical bridge as ONE named conjunct

The reviewer of the last report and the lead's NOTES §9 both point at the same gap: the input bundle
`GalMin` carries four *class-data* fields (`StData`, `StData2` and the two angular moduli `hhθ`,
`hhθp`) which are **not** derivable from `RegPkgMin` + the `ℋ⁴`-bound (machine-checked witnesses in
`NOTES_RegPkgGal.md` §2, §8, §11.4) and which therefore have to be *exported* by the
strong-solution/persistence side.  Shipping them as four separate fields makes the export awkward to
state; this file bundles them into the single `Prop` `St1Class α S g`, which can be adopted verbatim
as one conjunct (e.g. added to the lead's `DynOK`-shaped hypothesis).

The four fields, verbatim:

* `hSt` — `StData α S (extG g)`: `|D_θ g̃| ≤ Cθ z²Γ(θ)` and the Taylor data at `z = 0`
  (`|g̃| ≤ Kz²`, `|∂_z g̃| ≤ Qz` for `z ≤ 2`);
* `hSt2` — `StData2 α S (extG g)`: `|∂_z²g̃| ≤ Q₂` on `0 < z ≤ 2`;
* `hhθ` — the `α`-Hölder modulus of `g̃` in `θ`, uniform in `(z,τ)`;
* `hhθp` — the `α`-Hölder modulus of `∂_zg̃` in `θ`, uniform in `(z,τ)`.

The two `∃`-constants are *inside* the fields (`∃ Lθ, …`), so `St1Class` is a `Prop` and no
constant has to be chosen by the caller.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.Der.Defs
import Submission.Work.FTS.RegPkgGal.RVocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

/-- **THE `St1`-CLASS EXPORT.**  The class data of the perturbation `g̃` which the paper's
construction provides and which the physical bridge consumes (see the module docstring). -/
structure St1Class (α S : ℝ) (g : Fam) : Prop where
  /-- the `Γ`-vanishing of the angular derivative together with the Taylor data at `z = 0` -/
  hSt : StData α S (extG g)
  /-- the second-order `z`-bound at the origin -/
  hSt2 : StData2 α S (extG g)
  /-- the `θ`-modulus of `g̃` (`α`-Hölder, uniform in `(z,τ)`) -/
  hhθ : ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
    ∀ θ' ∈ Work.Spaces.Iθ, |extG g z θ τ - extG g z θ' τ| ≤ Lθ * |θ - θ'| ^ α
  /-- the `θ`-modulus of `∂_zg̃` (`α`-Hölder, uniform in `(z,τ)`) -/
  hhθp : ∃ Nθ : ℝ, 0 ≤ Nθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
    ∀ θ' ∈ Work.Spaces.Iθ,
    |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => extG g z θ τ) z θ'| ≤ Nθ * |θ - θ'| ^ α

theorem St1Class.stData {α S : ℝ} {g : Fam} (H : St1Class α S g) : StData α S (extG g) := H.hSt

theorem St1Class.stData2 {α S : ℝ} {g : Fam} (H : St1Class α S g) : StData2 α S (extG g) := H.hSt2

/-- The `Γ`-vanishing clause of the class, in the shape the derivations consume. -/
theorem St1Class.dthvan {α S : ℝ} {g : Fam} (H : St1Class α S g) :
    ∃ Cθ : ℝ, 0 ≤ Cθ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (gSlice (extG g) τ) z θ| ≤ Cθ * z ^ 2 * Gamma α θ := H.hSt.dthvan

/-- The Taylor clause at `z = 0` of the class, in the shape the derivations consume. -/
theorem St1Class.quad {α S : ℝ} {g : Fam} (H : St1Class α S g) :
    ∃ K Q : ℝ, 0 ≤ K ∧ 0 ≤ Q ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |extG g z θ τ| ≤ K * z ^ 2) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |Work.Spaces.pz (gSlice (extG g) τ) z θ| ≤ Q * z) := H.hSt.quad

/-- The second-order clause of the class, in the shape the derivations consume. -/
theorem St1Class.quad2 {α S : ℝ} {g : Fam} (H : St1Class α S g) :
    ∃ Q₂ : ℝ, 0 ≤ Q₂ ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z → z ≤ 2 →
      |Work.Spaces.pz (Work.Spaces.pz (gSlice (extG g) τ)) z θ| ≤ Q₂ := H.hSt2.quad2

end Work.FTS.RegPkgGal
