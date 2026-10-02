import Mathlib
import Submission.Work.FQC.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Transfer of dynamic rays along a homeomorphism of the dynamical plane

If `θ : ℂ ≃ₜ ℂ` carries the escaping set of `T_c = z̄² + c` onto the escaping set of
`T_{c₂} = z̄² + c₂` (hypothesis `hesc`), and `φ` is a Böttcher coordinate of `T_c` while
`φ ∘ θ.symm` is a Böttcher coordinate of `T_{c₂}`, then `θ` carries the dynamic ray `R_c(ϑ)`
onto the dynamic ray `R_{c₂}(ϑ)`, and it carries the landing point of `R_c(ϑ)` to the landing
point of `R_{c₂}(ϑ)`.

This is the ray bookkeeping of the quasiconformal deformation in Hubbard–Schleicher,
*Multicorns are not Path Connected*: the deformation `θ` is a homeomorphism of the plane,
it preserves the external angle, and the landing statement is transported along it.

The only two inputs used are

* the definition of the dynamic ray, which is phrased with the escaping set (`hesc` transfers
  membership, `θ` transfers the Böttcher value because `φ (θ.symm w) = (φ ∘ θ.symm) w`);
* the uniqueness of the Böttcher coordinate `Work.ParamRays.isDynBottcher_unique`, which makes
  the accumulation set `rayAccum c φ ϑ` — and hence `landsAt c ϑ`, which existentially
  quantifies over the choice of Böttcher coordinate — independent of that choice.
-/

open Work.Landing
open Work.ParamRays (IsDynBottcher Escaping escapingSet)

namespace Work.FQC

/-- Two functions agreeing on the escaping set define the same dynamic ray. -/
lemma dynRay_congr {c : ℂ} {φ ψ : ℂ → ℂ}
    (h : ∀ z : ℂ, Escaping c z → φ z = ψ z) (ϑ : ℝ) :
    dynRay c φ ϑ = dynRay c ψ ϑ := by
  ext z
  constructor
  · rintro ⟨hz, hzray⟩
    exact ⟨hz, by rwa [h z hz] at hzray⟩
  · rintro ⟨hz, hzray⟩
    exact ⟨hz, by rwa [h z hz]⟩

/-- Two functions agreeing on the escaping set define the same accumulation set, hence the same
landing statement.  (The truncated rays entering `rayAccum` consist of escaping points only, so
the agreement on the escaping set is all that is needed.) -/
lemma rayAccum_congr {c : ℂ} {φ ψ : ℂ → ℂ}
    (h : ∀ z : ℂ, Escaping c z → φ z = ψ z) (ϑ : ℝ) :
    rayAccum c φ ϑ = rayAccum c ψ ϑ := by
  have hdyn := dynRay_congr h ϑ
  have htrunc : ∀ ρ : ℝ, {z : ℂ | z ∈ dynRay c φ ϑ ∧ ‖φ z‖ ≤ ρ}
      = {z : ℂ | z ∈ dynRay c ψ ϑ ∧ ‖ψ z‖ ≤ ρ} := by
    intro ρ
    ext z
    constructor
    · rintro ⟨hz, hle⟩
      have hz' : z ∈ dynRay c ψ ϑ := by rwa [hdyn] at hz
      have hφψ : φ z = ψ z := h z hz.1
      exact ⟨hz', by rwa [← hφψ]⟩
    · rintro ⟨hz, hle⟩
      have hz' : z ∈ dynRay c φ ϑ := by rwa [← hdyn] at hz
      have hφψ : φ z = ψ z := h z hz.1
      exact ⟨hz', by rwa [hφψ]⟩
  ext x
  simp only [rayAccum, Set.mem_ofPred_eq]
  constructor
  · intro hx ρ hρ
    rw [← htrunc ρ]
    exact hx ρ hρ
  · intro hx ρ hρ
    rw [htrunc ρ]
    exact hx ρ hρ

/-- **Transfer of dynamic rays and of landing along a homeomorphism of the plane.**

Let `θ` be a homeomorphism of `ℂ`, `hb` a Böttcher coordinate of `T_c` and `hb₂` a Böttcher
coordinate of `T_{c₂}` of the form `φ ∘ θ.symm`; assume moreover that `θ` maps the escaping set of
`T_c` onto that of `T_{c₂}` (`hesc`).  Then for every angle `ϑ`

* the dynamic ray of `T_{c₂}` at angle `ϑ` is the image under `θ` of the dynamic ray of `T_c` at
  angle `ϑ`, and
* the ray of `T_c` at angle `ϑ` lands at `z` if and only if the ray of `T_{c₂}` at angle `ϑ` lands
  at `θ z`.

The second statement uses `Work.ParamRays.isDynBottcher_unique` twice: the property `RayLands` is
independent of the chosen Böttcher coordinate, both at `c` and at `c₂`. -/
theorem transfer_rays {c c₂ : ℂ} {φ : ℂ → ℂ} (θ : ℂ ≃ₜ ℂ) (hb : Work.ParamRays.IsDynBottcher c φ) (hb₂ : Work.ParamRays.IsDynBottcher c₂ (φ ∘ (θ.symm : ℂ → ℂ))) (hesc : ∀ z : ℂ, Work.ParamRays.Escaping c₂ (θ z) ↔ Work.ParamRays.Escaping c z) (ϑ : ℝ) : Work.Landing.dynRay c₂ (φ ∘ (θ.symm : ℂ → ℂ)) ϑ = θ '' Work.Landing.dynRay c φ ϑ ∧ (∀ z : ℂ, Work.Landing.landsAt c ϑ z ↔ Work.Landing.landsAt c₂ ϑ (θ z)) := by
  have hdyn : dynRay c₂ (φ ∘ (θ.symm : ℂ → ℂ)) ϑ = θ '' dynRay c φ ϑ := by
    ext w
    constructor
    · rintro ⟨hwesc, hwray⟩
      refine ⟨θ.symm w, ⟨(hesc (θ.symm w)).mp (by simpa using hwesc), ?_⟩,
        θ.apply_symm_apply w⟩
      simpa using hwray
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(hesc z).mpr hz.1, by simpa using hz.2⟩
  have hacc : rayAccum c₂ (φ ∘ (θ.symm : ℂ → ℂ)) ϑ = θ '' rayAccum c φ ϑ := by
    have htrunc : ∀ ρ : ℝ,
        {w : ℂ | w ∈ dynRay c₂ (φ ∘ (θ.symm : ℂ → ℂ)) ϑ ∧
            ‖(φ ∘ (θ.symm : ℂ → ℂ)) w‖ ≤ ρ}
          = θ '' {z : ℂ | z ∈ dynRay c φ ϑ ∧ ‖φ z‖ ≤ ρ} := by
      intro ρ
      rw [hdyn]
      ext w
      constructor
      · rintro ⟨hw, hle⟩
        obtain ⟨z, hz, hzw⟩ := hw
        refine ⟨z, ⟨hz, ?_⟩, hzw⟩
        rw [← hzw] at hle
        simpa using hle
      · rintro ⟨z, hz, hzw⟩
        refine ⟨⟨z, hz.1, hzw⟩, ?_⟩
        rw [← hzw]
        simpa using hz.2
    ext x
    constructor
    · intro hx
      refine ⟨θ.symm x, ?_, θ.apply_symm_apply x⟩
      intro ρ hρ
      have h1 : x ∈ closure (θ '' {z : ℂ | z ∈ dynRay c φ ϑ ∧ ‖φ z‖ ≤ ρ}) := by
        rw [← htrunc ρ]
        exact hx ρ hρ
      rw [← θ.image_closure] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      rw [← hyx, θ.symm_apply_apply]
      exact hy
    · rintro ⟨y, hy, rfl⟩
      intro ρ hρ
      have h1 : y ∈ closure {z : ℂ | z ∈ dynRay c φ ϑ ∧ ‖φ z‖ ≤ ρ} := hy ρ hρ
      have h2 : θ y ∈ closure (θ '' {z : ℂ | z ∈ dynRay c φ ϑ ∧ ‖φ z‖ ≤ ρ}) := by
        rw [← θ.image_closure]
        exact ⟨y, h1, rfl⟩
      rw [htrunc ρ]
      exact h2
  refine ⟨hdyn, ?_⟩
  intro z
  constructor
  · rintro ⟨ψ, hbψ, hland⟩
    have hcongr : rayAccum c ψ ϑ = rayAccum c φ ϑ :=
      rayAccum_congr (fun w hw => Work.ParamRays.isDynBottcher_unique hbψ hb hw) ϑ
    have hφ : rayAccum c φ ϑ = {z} := by
      rw [← hcongr]
      exact hland
    exact ⟨φ ∘ (θ.symm : ℂ → ℂ), hb₂, by
      show rayAccum c₂ (φ ∘ (θ.symm : ℂ → ℂ)) ϑ = {θ z}
      rw [hacc, hφ, Set.image_singleton]⟩
  · rintro ⟨ψ₂, hbψ₂, hland₂⟩
    have hcongr : rayAccum c₂ ψ₂ ϑ = rayAccum c₂ (φ ∘ (θ.symm : ℂ → ℂ)) ϑ :=
      rayAccum_congr (fun w hw => Work.ParamRays.isDynBottcher_unique hbψ₂ hb₂ hw) ϑ
    have hφ : θ '' rayAccum c φ ϑ = {θ z} := by
      rw [← hacc, ← hcongr]
      exact hland₂
    have hfin : rayAccum c φ ϑ = {z} := by
      refine Set.Subset.antisymm ?_ ?_
      · intro y hy
        have hy' : θ y ∈ ({θ z} : Set ℂ) := by
          rw [← hφ]
          exact ⟨y, hy, rfl⟩
        rw [Set.mem_singleton_iff] at hy'
        exact Set.mem_singleton_iff.mpr (θ.injective hy')
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        have hz' : θ y ∈ θ '' rayAccum c φ ϑ := by
          rw [hφ]
          exact Set.mem_singleton_iff.mpr (congrArg θ hy)
        obtain ⟨a, ha, hay⟩ := hz'
        rw [← θ.injective hay]
        exact ha
    exact ⟨φ, hb, hfin⟩

end Work.FQC
