/-
# `Work.FTS_RegExport.RXR5L.DzFtau_C1Jet` — the `D_z`-slot of the fake-time profile

`F_τ = F_* + g(τ)` splits as the **static** profile `F_* = Fstar (pExp α)` plus the (sanitised)
family `SG α g = gS α (tauExt g)`, and `D_z` is linear (`Work.Spaces.Dz f = z ∂_z f`), so the
`z`-derivative of the fake-time profile is the sum of two pieces that are *already available*
in the tree:

* `C1Jet` of `D_z F_*` — `Work.FTS_RegExport.RXR5.C1Jet_Dz_Fstar` (via the global factorisation
  `D_z F_* = pzCoeff α θ · (z F̂'(z))` and the `C1Jet`-closure of products `c1jet_prod`);
* `C1Jet` of `D_z (SG α g)` — the hypothesis `hO1` (this is the slot whose *producer* is the
  `O1`-obstruction documented in `FTS_RegExport/NOTES_area_state.md` §2(c): the `Jet` clause of
  `C1Jet` forces a `z`-uniform angular modulus of `z ∂_z g̃` which `St1Class` does not supply;
  the re-cut therefore *takes it as a hypothesis*).

So the content of this file is the **linearity step**: `C1Jet` is closed under the `D_z` of a sum
of two families (`C1Jet_dz_add`), provided both slices are differentiable at `z > 0` (there the
pointwise product rule `deriv (f + g) = deriv f + deriv g` applies; at `z = 0` both sides of
`D_z` vanish identically).  The differentiability of the two slices comes from
`Work.Stability.differentiableAt_Fstar_slice` (the profile's `z`-slice `2z/(1+z)²` has its only
pole at `z = -1`) and from the `z`-derivative half of `SG_C1Jet` (`St1Class` + `DynOK'`).

Everything is a constant-existential statement, so the losses in the constants
(`N₆ = N₁₁ + N₂`) are harmless.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.SG_C1Jet

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 Linearity of `D_z` at the level of `C1Jet`s -/

/-- **`D_z` of a sum of two families is a `C1Jet`.**  If the `D_z`-slots of `a` and `b` are
`C1Jet`s and both families have differentiable `z`-slices at every `z > 0` (uniformly in
`(θ,τ) ∈ Iθ × [0,S]`), then so is the `D_z`-slot of the pointwise sum `a + b`.

The only pointwise input is `deriv (f + g) = deriv f + deriv g` on `z > 0`; at `z = 0` both
sides of `D_z` vanish (`D_z f 0 θ = 0 · ∂_z f`), so the identity holds on the whole closed half
line `z ≥ 0` on which the `Jet` clause of `C1Jet` is stated. -/
theorem C1Jet_dz_add {α S N₁ N₂ : ℝ} {a b : ℝ → ℝ → ℝ → ℝ}
    (Ha : Work.FTS.RegPkgGal.C1Jet α S N₁
      (fun z θ τ => Work.Spaces.Dz (fun z θ => a z θ τ) z θ))
    (Hb : Work.FTS.RegPkgGal.C1Jet α S N₂
      (fun z θ τ => Work.Spaces.Dz (fun z θ => b z θ τ) z θ))
    (had : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => a z' θ τ) z)
    (hbd : ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => b z' θ τ) z) :
    Work.FTS.RegPkgGal.C1Jet α S (N₁ + N₂)
      (fun z θ τ => Work.Spaces.Dz (fun z θ => a z θ τ + b z θ τ) z θ) := by
  refine (Work.FTS.RegPkgGal.C1Jet.add Ha Hb).congr ?_
  intro z θ τ hz hθ hτ
  rcases eq_or_lt_of_le hz with h | h
  · -- `z = 0`: every `D_z` vanishes
    rw [← h]
    simp only [Work.Spaces.Dz]
    ring
  · -- `z > 0`: the pointwise product rule
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [show (fun z' : ℝ => a z' θ τ + b z' θ τ)
        = (fun z' : ℝ => a z' θ τ) + (fun z' => b z' θ τ) from rfl,
      deriv_add (had τ hτ θ hθ z h) (hbd τ hτ θ hθ z h), mul_add]

/-! ## §2 The `D_z`-slot of the fake-time profile -/

theorem DzFtau_C1Jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hO1 : ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂
        (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃
        (fun z θ τ => Work.Spaces.Dth (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ)) :
    ∃ N₆ : ℝ, 0 ≤ N₆ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₆
        (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α)
          (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) z θ) := by
  -- the `D_z`-slot of the (sanitised) family, from the hypothesis `hO1`
  obtain ⟨N₂, _, hN₂0, _, hDzSG, _⟩ := hO1
  -- the `D_z`-slot of the static profile `F_*`
  obtain ⟨N₁₁, hN₁₁0, hDzFs⟩ :=
    Work.FTS_RegExport.RXR5.C1Jet_Dz_Fstar (α := α) (S := S) hα hα13
  -- the `z`-derivative of the slices of the sanitised family, from `SG_C1Jet`
  obtain ⟨_, _, hC1G⟩ := SG_C1Jet hα hα13 hOK hS hSt1
  refine ⟨N₁₁ + N₂, by linarith, ?_⟩
  -- `F_τ = F_* + g(τ)`, and `D_z` is additive
  refine (C1Jet_dz_add
    (a := fun z θ _ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
    (b := fun z θ τ => Work.FTS_RegExport.RXR5.SG α g z θ τ)
    hDzFs hDzSG ?_ ?_).congr ?_
  · intro τ _hτ θ _hθ z hz
    exact Work.Stability.differentiableAt_Fstar_slice (Work.FTS.Regularity.pExp α) θ z
      (by linarith [Set.mem_Ioi.mp hz])
  · intro τ hτ θ hθ z hz
    obtain ⟨d, hd, _⟩ := hC1G.2 τ hτ θ hθ z hz
    exact hd.differentiableAt
  · -- `Ftau α g τ = Fstar α + g τ` by definition
    intro z θ τ _hz _hθ _hτ
    simp only [Work.Construction.Ftau]

end Work.FTS_RegExport.RXR5L
