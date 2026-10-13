import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.Vz7Split
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.Vz7Wire` — `vz0` for the wire family from TWO quantitative clauses

`Vz7Split.lean` reduces the frozen field `VelPkg.vz0` to the sharp identity

    Vz7 = (1 − μτ) + 2·αG·V(Φ̃_*) + (2·αG/(1+z))·c2m(θ) + 2·αG·V(u),    u = E (slice (tauExt g) τ),

together with the criterion `4αG + 2·Cs·αG² + 2·CE·αG² ≤ 1/2` for the two slot bounds
`|V(Φ̃_*)| ≤ Cs·αG`, `|V(u)| ≤ CE·αG`.  This file proves the missing *step structure* for the
concrete family `Φ = psiR α Φs E (tauExt g)`, `G = gS α (tauExt g)`:

* `vz7_eq_of_phiTil` — the *closed form of `Vz7`* (`Vz7 = (1−μτ) + 2·αG·V(slice Φ τ)`) proved
  **directly from the defining formula**, with **no** integrability/continuity hypotheses on
  `L₁₂dens` (unlike `RXDiag.closedFormOpen`, whose `hint`/`hcont` are only needed for the `cs7`
  half): the `Θ`-part is absorbed by the exact identity `2αG·V(Θ αG F) = L₁₂(F)·c2m`;
* `vop_slice_eq_star_add_E_q` — the sharp split in its **quadrant-restricted** form (the form in
  which it applies to `psiR`, which agrees with `PsiCan` only on the open quadrant), via the
  proved congruence `Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0`;
* `vz7_nonneg_wire` — **`vz0` for the wire family**, i.e. the pointwise sign condition
  `0 ≤ Vz7 αG μ G Φ z θ τ` for every `τ ≥ 0` and every point of the open quadrant, from exactly:
  the star slot (`hVstar`; *derivable* from the frozen `hStar.VW` by
  `Vz7Split.starVop_pointwise_le`), the `E`-slot (`hVeu`) and the tie (`htie`), plus the
  differentiability data of the three `θ`-slices;
* `vz7_nonneg_wire_of_star` — the same with the star slot **discharged from `StarPkgo2.VW`**.

So the whole remaining content of `vz0` is the two quantitative clauses

    hVeu : ∀ τ z θ, 0 ≤ τ → quadrant → |V(E (slice (tauExt g) τ)) z θ| ≤ CE·αG      (E-slot)
    htie : 4·αG + 2·Cs·αG² + 2·CE·αG² ≤ 1/2                                        (the tie)

— both *satisfiable* by the construction (the E-slot is the elliptic `V`-slot of `EllPkgK` with
its `αG`-factor kept; the tie holds whenever `αG ≲ 1/8` and the two constants are not
astronomically large, which is exactly what the wire's `Inputs'`-style normalisations give), and
neither equivalent to `vz0`.  See `NOTES_FINAL.md` §18–§20.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## 1. The closed form of `Vz7`, from the definition only -/

/-- **`Vz7 = (1 − μτ) + 2·αG·V(slice Φ τ)`**, proved directly from the defining formula of `Vz7`
(`(1−μ) + L₁₂(F_τ)·c2m + 2αG·V(Φ̃_τ)`) by absorbing the `Θ`-part with the identity
`2αG·V(Θ αG F) = L₁₂(F)·c2m`.  No integrability or continuity hypothesis on `L₁₂dens` is used —
only the differentiability of the `θ`-slice of `slice Φ τ`. -/
theorem vz7_eq_of_phiTil {αG : ℝ} (hαG : 0 < αG) {μ : ℝ → ℝ} {G Φ : Fam} {τ z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hdΦ : DifferentiableAt ℝ (fun θ' => slice Φ τ z θ') θ) :
    Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ
      = (1 - μ τ) + 2 * αG * Work.Construction.Vop (slice Φ τ) z θ := by
  -- `phiTil = slice Φ τ − Θ(F_τ)` has a differentiable `θ`-slice
  have hdΘ : DifferentiableAt ℝ
      (fun θ' => Work.Construction.Theta αG (Work.Construction.Ftau αG G τ) z θ') θ :=
    differentiableAt_thetaslice_Theta z θ
  have hdTil : DifferentiableAt ℝ
      (fun θ' => Work.FTS.RegExportIface.phiTil αG G Φ τ z θ') θ := by
    show DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil αG
      (Work.Construction.Ftau αG G τ) (slice Φ τ) z θ') θ
    simp only [Work.Construction.PhiTil]
    exact hdΦ.sub hdΘ
  -- the additive split `V(Φ) = V(Φ̃) + V(Θ)`
  have hadd := Vop_add_point (A := Work.FTS.RegExportIface.phiTil αG G Φ τ)
    (B := Work.Construction.Theta αG (Work.Construction.Ftau αG G τ)) hdTil hdΘ
  -- the `Θ`-identity
  have hVΘ := two_mul_Vop_Theta (αG := αG) hαG (F := Work.Construction.Ftau αG G τ)
    (z := z) (θ := θ) hθ hθ2
  -- `V(slice Φ τ) = V(Φ̃) + V(Θ)` by the quadrant congruence
  have hcongr : Work.Construction.Vop (slice Φ τ) z θ
      = Work.Construction.Vop (fun z θ => Work.FTS.RegExportIface.phiTil αG G Φ τ z θ
          + Work.Construction.Theta αG (Work.Construction.Ftau αG G τ) z θ) z θ := by
    refine Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0 ?_ z θ hz hθ hθ2
    intro z θ hz hθ hθ2
    simp only [Work.FTS.RegExportIface.phiTil, Work.Construction.PhiTil]
    ring
  -- assemble
  have hkey : 2 * αG * Work.Construction.Vop (slice Φ τ) z θ
      = 2 * αG * Work.Construction.Vop (Work.FTS.RegExportIface.phiTil αG G Φ τ) z θ
        + Work.Construction.L12 (Work.Construction.Ftau αG G τ) z * Work.Construction.c2m θ := by
    rw [hcongr, hadd]
    linear_combination hVΘ
  show (1 - μ τ) + Work.Construction.L12 (Work.Construction.Ftau αG G τ) z
      * Work.Construction.c2m θ
      + 2 * αG * Work.Construction.Vop (Work.FTS.RegExportIface.phiTil αG G Φ τ) z θ
    = (1 - μ τ) + 2 * αG * Work.Construction.Vop (slice Φ τ) z θ
  linarith [hkey]

/-! ## 2. The sharp split, quadrant-restricted -/

/-- **The sharp split on the open quadrant.**  If `Φ = Φs + E u` pointwise on the quadrant and the
two `θ`-slices are differentiable there, then

    V(Φ) = V(Φ̃_*) + c2m(θ)/(1+z) + V(E u),      Φ̃_* = Φs − Θ(F_*).

This is the form that applies to `Φ = slice (psiR α Φs E G) τ`, for which the pointwise identity
holds only on the open quadrant (`psiR_of_mem`). -/
theorem vop_slice_eq_star_add_E_q {αG : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {Φs : Fn} {E : Fn → Fn} {u Φ : Fn} {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ)
    (hθ2 : θ < Real.pi / 2)
    (hslice : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 → Φ z θ = Φs z θ + E u z θ)
    (hdΦs : DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hdE : DifferentiableAt ℝ (fun θ' => E u z θ') θ) :
    Work.Construction.Vop Φ z θ
      = Work.Construction.Vop
          (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ
        + Work.Construction.c2m θ / (1 + z)
        + Work.Construction.Vop (E u) z θ := by
  -- `Φ` agrees on the quadrant with `(Φ̃_* + Θ(F_*)) + E u`
  have hcongr : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Φ z θ = (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs z θ
        + Work.Construction.Theta αG (Work.Construction.Fstar αG) z θ) + E u z θ := by
    intro z θ hz hθ hθ2
    rw [hslice z θ hz hθ hθ2]
    simp only [Work.Construction.PhiTil]
    ring
  rw [Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0 hcongr z θ hz hθ hθ2]
  -- differentiability of the three `θ`-slices
  have hdΘs : DifferentiableAt ℝ
      (fun θ' => Work.Construction.Theta αG (Work.Construction.Fstar αG) z θ') θ :=
    differentiableAt_thetaslice_Theta z θ
  have hdTil : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs z θ') θ := by
    simp only [Work.Construction.PhiTil]
    exact hdΦs.sub hdΘs
  have hdSum : DifferentiableAt ℝ
      (fun θ' => (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs z θ'
        + Work.Construction.Theta αG (Work.Construction.Fstar αG) z θ')) θ :=
    hdTil.add hdΘs
  have hV1 := Vop_add_point (A := fun z θ => Work.Construction.PhiTil αG
      (Work.Construction.Fstar αG) Φs z θ
      + Work.Construction.Theta αG (Work.Construction.Fstar αG) z θ) (B := E u) hdSum hdE
  have hV2 := Vop_add_point (A := Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)
    (B := Work.Construction.Theta αG (Work.Construction.Fstar αG)) hdTil hdΘs
  -- the `Θ`-identity, divided by `2 αG`
  have hVΘ := two_mul_Vop_Theta (αG := αG) hαG (F := Work.Construction.Fstar αG)
    (z := z) (θ := θ) hθ hθ2
  rw [Work.Construction.L12_Fstar_eq (α := αG) hαG hαG1 hz.le] at hVΘ
  have hVΘ' : Work.Construction.Vop
        (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
      = Work.Construction.c2m θ / (1 + z) := by
    have h3 : 2 * αG * Work.Construction.Vop
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
        = 2 * αG * (Work.Construction.c2m θ / (1 + z)) := by
      rw [hVΘ]
      field_simp
    exact mul_left_cancel₀ (by positivity : (2 : ℝ) * αG ≠ 0) h3
  rw [hV1, hV2, hVΘ']

/-! ## 3. `vz0` for the wire family from the two quantitative clauses -/

/-- **`vz0` for the wire family.**  For `Φ = psiR α Φs E (tauExt g)` (so that
`slice Φ τ = Φs + E (slice (tauExt g) τ)` on the open quadrant) and any clock `μ` with
`|μ τ| ≤ 1/2`, the sign condition `0 ≤ Vz7 αG μ G Φ z θ τ` holds for **every** `τ ≥ 0` and every
point of the open quadrant, from the two quantitative clauses

* `hVstar : |V(Φ̃_*)| ≤ Cs·αG` (the star slot — provable from the frozen `hStar.VW`, see
  `vz7_nonneg_wire_of_star`),
* `hVeu : |V(u τ)| ≤ CE·αG` (the elliptic slot, with its `αG` factor kept),

together with the tie `4·αG + 2·Cs·αG² + 2·CE·αG² ≤ 1/2`. -/
theorem vz7_nonneg_wire {αG Cs CE : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {μ : ℝ → ℝ} {G Φ : Fam} {Φs : Fn} {u : ℝ → Fn}
    (hmu : ∀ τ : ℝ, 0 ≤ τ → |μ τ| ≤ 1 / 2)
    (hslice : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      slice Φ τ z θ = Φs z θ + u τ z θ)
    (hdΦ : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => slice Φ τ z θ') θ)
    (hdΦs : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hdu : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => u τ z θ') θ)
    (hVstar : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop
        (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ| ≤ Cs * αG)
    (hVeu : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (u τ) z θ| ≤ CE * αG)
    (htie : 4 * αG + 2 * Cs * αG ^ 2 + 2 * CE * αG ^ 2 ≤ 1 / 2) :
    ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      0 ≤ Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ := by
  intro τ z θ hτ hz hθ hθ2
  -- the closed form at `(z,θ,τ)`
  have hclosed := vz7_eq_of_phiTil (αG := αG) hαG (μ := μ) (G := G) (Φ := Φ) (τ := τ)
    hz hθ hθ2 (hdΦ τ z θ hτ hz hθ hθ2)
  -- the sharp split at `(z,θ,τ)`
  have hsplit := vop_slice_eq_star_add_E_q (αG := αG) hαG hαG1 (Φs := Φs)
    (E := fun _ : Fn => u τ) (u := 0) (Φ := slice Φ τ) (z := z) (θ := θ) hz hθ hθ2
    (fun a b ha hb hb2 => by
      rw [hslice τ a b hτ ha hb hb2])
    (hdΦs z θ hz hθ hθ2) (hdu τ z θ hτ hz hθ hθ2)
  exact vz7_nonneg_of_sharp (αG := αG) hαG hz (hmu τ hτ) hsplit
    (hVstar z θ hz hθ hθ2) (hVeu τ z θ hτ hz hθ hθ2) hclosed htie

/-- **The same, with the star slot discharged from the frozen `StarPkgo2.VW`.**  The hypotheses are
those of `velPkg` for the star part, the `E`-slot clause, the tie, and the differentiability data. -/
theorem vz7_nonneg_wire_of_star {αG Cs CE : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {μ : ℝ → ℝ} {G Φ : Fam} {Φs : Fn} {u : ℝ → Fn}
    (hVWmem : Work.Spaces.WlInfMem αG 4 (Work.Construction.Vop
      (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)))
    (hVWbnd : Work.Spaces.WlInf αG 4 (Work.Construction.Vop
      (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)) ≤ Cs * αG)
    (hmu : ∀ τ : ℝ, 0 ≤ τ → |μ τ| ≤ 1 / 2)
    (hslice : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      slice Φ τ z θ = Φs z θ + u τ z θ)
    (hdΦ : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => slice Φ τ z θ') θ)
    (hdΦs : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hdu : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun θ' => u τ z θ') θ)
    (hVeu : ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (u τ) z θ| ≤ CE * αG)
    (htie : 4 * αG + 2 * Cs * αG ^ 2 + 2 * CE * αG ^ 2 ≤ 1 / 2) :
    ∀ τ z θ : ℝ, 0 ≤ τ → 0 < z → 0 < θ → θ < Real.pi / 2 →
      0 ≤ Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ :=
  vz7_nonneg_wire (αG := αG) (Cs := Cs) (CE := CE) hαG hαG1 hmu hslice hdΦ hdΦs hdu
    (starVop_pointwise_le hVWmem hVWbnd) hVeu htie

end Work.FTS_RegExport
