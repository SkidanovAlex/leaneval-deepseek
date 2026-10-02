/-
# `Work.FQCInputs.SimpleTransfer` — the simplicity of the transferred parabolic point

`Work.FQC.SimpleTransfer d fl P t` (module `Submission/Work/FQC/Flower.lean`) is the
*petal-direction* input of the deformation: for the conjugacy
`θ = principal (muQC d fl P t)` produced by the quasiconformal deformation, the transported
parabolic point `θ z₁` of `T_{c₂}` is again **simple**:

`iteratedDeriv 2 (F c₂) (θ z₁) ≠ 0`.

## Status

The area states this input in the *shift-invariant* form needed by the phase normalisation of
`Defs.lean` — `Work.FQCInputs.SimpleTransferPetal d`: the transported parabolic point is simple for
*every* flower of `d` equipped with a petal input (in particular for the renormalised flower) —
and proves the surrounding transfer lemmas that any proof of it will need (`deriv_F_transfer`,
`not_eventuallyEq_id_F`, `exists_poly_F`).

What this area does **not** do is *reduce* that input to the classical Leau–Fatou flower theorem
via the topology of the basin.  A first version did, through the predicate `HasOnePetal`
(the punctured basin having at most one component accumulating at the parabolic point), and used
two fields: "simple ⟹ one petal" and "one petal ⟹ simple".  The *second* field is **false**:
for a parabolic point of multiplicity `k ≥ 3` the `k - 1` petals need not lie in distinct
components of the punctured basin (they may be joined outside a neighbourhood of the point), so
"one component" does not force multiplicity `2`.  The naive route is therefore withdrawn; see
`NOTES.md` §6 for the refutations and for precisely what remains.  The route now followed instead is *continuation in
the deformation parameter* `t`: `N = {t | iteratedDeriv 2 (F (θ_t c)) (θ_t z₁) = 0}` misses `0`,
is closed and open, hence empty — see `NOTES.md` §6 and the lead's design note
`Submission/Work/NOTES_LEAD_mandelbar_simple.md` §3.

The material of this file is:

* `iterate_five_Tsq`, `deriv_F_transfer`, `not_eventuallyEq_id_F`,
  `not_eventuallyEq_id_F_transfer` — transport lemmas for the transferred parabolic point;
* `SimpleTransferPetal` — the petal-direction input in the shift-invariant form (the form in
  which the phase normalisation is free of charge).
-/
import Mathlib
import Submission.Work.FQC.transfer_parabolic_aux
import Submission.Work.FQCInputs.Defs
import Submission.Work.FQCInputs.Poly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.FQCInputs

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## 2. The transformed parabolic point of `F c₂` -/

/-- `F c = (Tsq c)^[5]`, i.e. the tenth iterate of `T_c` is the fifth iterate of the holomorphic
second iterate. -/
theorem iterate_five_Tsq (c : ℂ) : (Work.Landing.Tsq c)^[5] = F c := by
  rw [Work.FQC.tsq_eq_iterate_local, Work.FQC.elF_eq_iterate_local, ← Function.iterate_mul]

/-- **The multiplier of the transferred parabolic point is `1`**, in the form of `deriv`:
`deriv (F c₂) (θ z₁) = 1` for any topological conjugacy `θ` of `T_c` to `T_{c₂}` which is
asymptotically the identity at `∞`. -/
theorem deriv_F_transfer {c : ℂ} (d : RootParabolic c) {c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z))
    (hdecay : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖) :
    deriv (F c₂) (θ d.z₁) = 1 := by
  have h := Work.FQC.multiplier_transfer d θ hconj hdecay
  rw [← iterate_five_Tsq c₂]
  simpa only [Work.Landing.multiplier2] using h

/-- `F c` is not the identity germ at the parabolic point: the second derivative would vanish. -/
theorem not_eventuallyEq_id_F {c : ℂ} (d : RootParabolic c) :
    ¬ ((F c) =ᶠ[𝓝 d.z₁] id) := by
  intro h
  have h2 : iteratedDeriv 2 (F c) d.z₁ = iteratedDeriv 2 (id : ℂ → ℂ) d.z₁ :=
    h.iteratedDeriv_eq 2
  rw [iteratedDeriv_id] at h2
  simp at h2
  exact d.simple h2

/-- The same for the transferred parabolic point. -/
theorem not_eventuallyEq_id_F_transfer {c : ℂ} (d : RootParabolic c) {c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) :
    ¬ ((F c₂) =ᶠ[𝓝 (θ d.z₁)] id) := by
  intro h
  have hF : ∀ z : ℂ, θ (F c z) = F c₂ (θ z) := Work.FQC.conj_F θ hconj
  apply not_eventuallyEq_id_F d
  have hset : {w : ℂ | F c₂ w = w} ∈ 𝓝 (θ d.z₁) :=
    h.mono (fun w hw => by simpa using hw)
  have hmem : θ ⁻¹' {w : ℂ | F c₂ w = w} ∈ 𝓝 d.z₁ :=
    θ.continuous.continuousAt.preimage_mem_nhds hset
  filter_upwards [hmem] with z hz
  have hz' : F c₂ (θ z) = θ z := hz
  have : θ (F c z) = θ z := by rw [hF z, hz']
  simpa using θ.injective this

/-! ## 3. The petal-direction input, in shift-invariant form -/

/-- **The petal-direction input of `Work.FQC`, in the form stable under the renormalisation of the
phase.**  For every flower of `d` *equipped with a petal input* — in particular for the
renormalised flower `Work.FQCInputs.shiftFlower s fl` with `petalShift hpetal s` — the parabolic
point transported by the deformation is again simple:

`∀ c₂ : ℂ, ∀ θ : ℂ ≃ₜ ℂ, θ = principal (muQC d fl' hpetal'.Pg t) ⟹
  θ ∘ T_c = T_{c₂} ∘ θ ⟹ iteratedDeriv 2 (F c₂) (θ z₁) ≠ 0`.

This is the exact form in which `Work.FQC.heightShift` consumes its `hsimple` hypothesis, made
uniform in the choice of Fatou coordinate; it is what makes the phase normalisation of `Defs.lean`
free of charge (see `heightShift_normalised`). -/
structure SimpleTransferPetal {c : ℂ} (d : RootParabolic c) : Prop where
  transfer : ∀ (fl' : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal' : Work.FQC.PetalInput d fl') (t : ℝ),
    Work.FQC.SimpleTransfer d fl' hpetal'.Pg t

/-- The petal-direction input for a single flower, in the form of FQC's `hsimple` hypothesis. -/
theorem SimpleTransferPetal.forFlower {c : ℂ} {d : RootParabolic c} (h : SimpleTransferPetal d)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (hpetal : Work.FQC.PetalInput d fl) : ∀ t : ℝ, Work.FQC.SimpleTransfer d fl hpetal.Pg t :=
  fun t => h.transfer fl hpetal t

end Work.FQCInputs

end
