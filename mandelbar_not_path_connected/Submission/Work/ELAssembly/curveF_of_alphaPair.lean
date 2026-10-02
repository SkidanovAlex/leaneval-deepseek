/-
# `curveF_of_alphaPair`: the `α`-pair curve is invariant under `F c = (T_c)^{10}`

This file discharges the `curveF` field of `Work.ELAssembly.AssemblyInputs`
(`Submission/Work/ELAssembly/Defs.lean`), i.e. it *derives* from `d : Work.EL.RootParabolic c`
alone the statement

  `Work.EL.F c '' Work.EL.pairCurve (alphaPairOf d) = Work.EL.pairCurve (alphaPairOf d)`,

where `alphaPairOf d` is the pair of root rays of angles `α₁ = 371/1023`, `α₂ = 404/1023`
co-landing at the parabolic point `z₁ = d.z₁`.

The mathematics is the usual Böttcher equivariance, in three steps.

* **The image of a ray.**  For a dynamical Böttcher coordinate `φ` satisfying the Böttcher
  equation `φ (T_c z) = conj (φ z)²` and the interface `hN : Work.EL.DynB c φ`, the map
  `T_c` carries the ray of angle `θ` *onto* the ray of angle `T θ = -2θ mod 1`:
  `Tantibar_image_paramRay`.  The forward inclusion is `Work.ELTop.rayPt_T` (the ray point of
  angle `θ` at level `t` goes to the ray point of angle `T θ` at level `t²`); the reverse
  inclusion uses that `t ↦ t²` is onto `(1, ∞)` and the injectivity of `φ` off `K c`.  This is
  an *equality* of sets — unlike the inclusion `image_paramRay_subset` of ELPull — which is
  what the invariance of the curve needs.
* **Iterating.**  `iterate_image_paramRay`: `(T_c)^[n] '' R(θ) = R(T^[n] θ)`.
* **The angle arithmetic.**  `T^[10] θ = fract (1024 θ)`, and `1024 αᵢ = αᵢ + 371` resp.
  `αᵢ + 404`, so `T^[10] αᵢ = αᵢ` (`T_ten_alpha1`, `T_ten_alpha2`).  This is exactly the
  `T^[10] αᵢ ≡ αᵢ` of the certificate.

Since `F c = (T_c)^[10]` and `F c z₁ = z₁` (`d.per_half`, `z₁` being fixed by `T_c^5`), the image
of `paramRay α₁ ∪ {z₁} ∪ paramRay α₂` is itself.
-/
import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELPull.polyPullback
import Submission.Work.ELTop.landsN_map

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The image of an external ray under `T_c` -/

/-- **`T_c` maps the ray of angle `θ` onto the ray of angle `T θ`.**  For `hN` the dynamical
Böttcher interface of a genuine Böttcher coordinate `φ` (`hφ`), the image of `paramRay θ`
under `Tantibar c` is exactly `paramRay (T θ)`:

* `⊆` at the level of ray points this is `Work.ELTop.rayPt_T`, the equivariance
  `φ (T_c z) = conj (φ z)²` read on the level sets of `‖φ‖`;
* `⊇` because `t ↦ t²` surjects `(1,∞)` onto itself, so every ray point of angle `T θ` at
  level `s²` is the image of the ray point of angle `θ` at level `s`. -/
theorem Tantibar_image_paramRay {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (θ : ℝ) :
    Tantibar c '' Work.EL.paramRay hN θ = Work.EL.paramRay hN (Work.EL.T θ) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    change Tantibar c z ∈ Work.Top.NakaneData.paramRay hN (Work.EL.T θ)
    change z ∈ Work.Top.NakaneData.paramRay hN θ at hz
    rw [Work.Top.NakaneData.paramRay_eq_range] at hz ⊢
    obtain ⟨t, rfl⟩ := hz
    exact ⟨⟨t.1 ^ 2, by nlinarith [t.2]⟩, Work.ELTop.rayPt_T hN hφ t.2⟩
  · intro hw
    change w ∈ Work.Top.NakaneData.paramRay hN (Work.EL.T θ) at hw
    rw [Work.Top.NakaneData.paramRay_eq_range] at hw
    obtain ⟨t, rfl⟩ := hw
    have ht : 1 < Real.sqrt t.1 := Work.ELTop.one_lt_sqrt t.2
    refine ⟨Work.EL.rayPt hN θ (Real.sqrt t.1), Work.EL.rayPt_mem_paramRay hN ht, ?_⟩
    rw [← Work.ELTop.rayPt_T hN hφ ht, Real.sq_sqrt (le_of_lt (lt_trans zero_lt_one t.2))]

/-- **The iterated form**: `(T_c)^[n]` maps the ray of angle `θ` onto the ray of angle
`T^[n] θ`. -/
theorem iterate_image_paramRay {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (n : ℕ) (θ : ℝ) :
    (Tantibar c)^[n] '' Work.EL.paramRay hN θ
      = Work.EL.paramRay hN ((Work.EL.T^[n]) θ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (Tantibar c)^[n + 1] '' Work.EL.paramRay hN θ
        = Tantibar c '' ((Tantibar c)^[n] '' Work.EL.paramRay hN θ) := by
      rw [Function.iterate_succ']
      exact (Set.image_image (Tantibar c) ((Tantibar c)^[n]) (Work.EL.paramRay hN θ)).symm
    rw [h1, ih, Tantibar_image_paramRay hN hφ]
    exact congrArg (fun t => Work.EL.paramRay hN t)
      (Function.iterate_succ_apply' Work.EL.T n θ).symm

/-! ## The angle arithmetic of the root portrait -/

/-- `T^[10] α₁ = α₁`: `T^[10] θ = fract (1024 θ)` and `1024 · 371/1023 = 371 + 371/1023`. -/
theorem T_ten_alpha1 : (Work.EL.T^[10]) Work.EL.alpha1 = Work.EL.alpha1 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2, Int.fract,
    Function.iterate_succ_apply', Function.iterate_zero]

/-- `T^[10] α₂ = α₂`: `1024 · 404/1023 = 404 + 404/1023`. -/
theorem T_ten_alpha2 : (Work.EL.T^[10]) Work.EL.alpha2 = Work.EL.alpha2 := by
  norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2, Int.fract,
    Function.iterate_succ_apply', Function.iterate_zero]

/-! ## The invariance of the `α`-pair curve -/

theorem curveF_of_alphaPair {c : ℂ} (d : Work.EL.RootParabolic c) : Work.EL.F c '' Work.EL.pairCurve (Work.ELAssembly.alphaPairOf d) = Work.EL.pairCurve (Work.ELAssembly.alphaPairOf d) := by
  have hF : Work.EL.F c = (Tantibar c)^[10] := Work.EL.F_eq_tantibar c
  -- `z₁` is fixed by `F c = (T_c)^[10]`, because it is fixed by `T_c^5` (`d.per_half`).
  have hz1 : Work.EL.F c d.z₁ = d.z₁ := by
    rw [hF, show (10 : ℕ) = 5 + 5 from rfl, Function.iterate_add_apply, d.per_half, d.per_half]
  -- the curve of the `α`-pair, as the two rays together with the landing point
  have hcurve : Work.EL.pairCurve (alphaPairOf d)
      = Work.EL.paramRay d.hN Work.EL.alpha1 ∪ {d.z₁}
        ∪ Work.EL.paramRay d.hN Work.EL.alpha2 := by
    simp only [Work.EL.pairCurve, Work.EL.RawPair.curve, alphaPairOf_a, alphaPairOf_b,
      alphaPairOf_y]
  -- the two rays are invariant under `F c`
  have hFa : Work.EL.F c '' Work.EL.paramRay d.hN Work.EL.alpha1
      = Work.EL.paramRay d.hN Work.EL.alpha1 := by
    rw [hF, iterate_image_paramRay d.hN d.bottcher 10 Work.EL.alpha1, T_ten_alpha1]
  have hFb : Work.EL.F c '' Work.EL.paramRay d.hN Work.EL.alpha2
      = Work.EL.paramRay d.hN Work.EL.alpha2 := by
    rw [hF, iterate_image_paramRay d.hN d.bottcher 10 Work.EL.alpha2, T_ten_alpha2]
  rw [hcurve, Set.image_union, Set.image_union, hFa, hFb, Set.image_singleton, hz1]

end Work.ELAssembly
