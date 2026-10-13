import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.RXDiag.closedFormOpen
import Submission.Work.FTS_RegExport.RXVP.vz7_nonneg_of_bounds
import Submission.Work.Construction.L12_Fstar_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.Vz7Split` — the sharp decomposition of `Vz7` and the exact smallness
criterion for `VelPkg.vz0`

**Why this file exists.**  The frozen producer `RX-VP` (`velPkg`) concludes, among other fields,
the sign condition `VelPkg.vz0 : 0 ≤ Vz7 αG μ G Φ z θ τ`.  By
`Work.FTS_RegExport.RXDiag.closedFormOpen` this reads, on the open quadrant,

    Vz7 = (1 − μτ) + 2·αG·V(Φ̃),

so the whole difficulty of `vz0` is a *lower* bound on `V(Φ̃)`.  This file isolates that
difficulty in the sharpest form:

* `Vop_add_point` — `V` is additive at a point where the two `θ`-slices are differentiable;
* `two_mul_Vop_Theta` — the exact `Θ`-identity `2 αG·V(Θ αG F) = L₁₂(F)·c2m`;
* `differentiableAt_thetaslice_Theta` — the `θ`-slice of `Θ` is differentiable;
* `vop_slice_eq_star_add_E` — **the sharp split**

      V(Φ) = V(Φ̃_*) + c2m(θ)/(1+z) + V(E u),      Φ = Φs + E u,  Φ̃_* = Φs − Θ(F_*),

  in which the singular `Θ`-parts and the `L₁₂(F_*)·c2m` term cancel *exactly* (using
  `L₁₂(F_*) = 2αG/(1+z)`), so that only the *star* slot `V(Φ̃_*)` and the *elliptic* slot
  `V(E u)` survive — with an extra factor `αG` in the smallness;
* `vz7_nonneg_of_sharp` — the resulting criterion
  `4·αG + 2·Cs·αG² + 2·CE·αG² ≤ 1/2  ⟹  Vz7 ≥ 0` when `|V(Φ̃_*)| ≤ Cs·αG` and `|V(E u)| ≤ CE·αG`;
* `vz7_nonneg_of_vop_split` — the same with the split and the closed form discharged.

**What the criterion says (and why the frozen statement cannot be proved as written).**  The
binding term is `2·αG·c2m(θ)/(1+z) ≥ −4·αG/(1+z) ≥ −4·αG`, coming from
`L₁₂(F_*)·c2m(θ) = (2αG/(1+z))·c2m(θ)`.  Since `pExp α = 3α` and the frozen hypothesis is only
`α ≤ 1/3` (i.e. `αG ≤ 1`), even the *best case* `V(Φ̃_*) = V(E u) = 0` fails at `αG ≥ 1/8`:
`1 − μτ − 4·αG/(1+z) < 0`.  And no fixed threshold in `α` can be *proved*, because the available
slot bounds are `|V(Φ̃_*)| ≤ Cs·αG` (from `StarPkgo2.VW`) and
`|V(E u)| ≤ Ce·HkNorm αG 6 u + |L₁₂(u)|/αG`, where `Cs, Ce, C₀` are *free* binders of the
producers, so the required threshold is `αG ≲ min(1/8, 1/(2Cs), 2/(C·C₀), …)`.  This is the
machine-checked form of the diagnosis in `NOTES_FINAL.md` §9/§16.

Everything here is stated for the frozen definitions; nothing outside this file is modified.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## 1. The additivity of `V` at a point -/

/-- `V(A + B) = V(A) + V(B)` at a point where both `θ`-slices are differentiable. -/
theorem Vop_add_point {A B : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun θ' => A z θ') θ)
    (hB : DifferentiableAt ℝ (fun θ' => B z θ') θ) :
    Work.Construction.Vop (fun z θ => A z θ + B z θ) z θ
      = Work.Construction.Vop A z θ + Work.Construction.Vop B z θ := by
  have hderiv : deriv (fun θ' => A z θ' + B z θ') θ
      = deriv (fun θ' => A z θ') θ + deriv (fun θ' => B z θ') θ :=
    deriv_add hA hB
  simp only [Work.Construction.Vop, Work.Spaces.pth]
  rw [hderiv]
  ring

/-! ## 2. The closed form of the `Θ` part of `V` -/

/-- `2 αG·V(Θ αG F) = L₁₂(F)·c2m` on the open quadrant — the identity that makes the `Θ` parts
cancel against the `L₁₂(F)·c2m` term of `Vz7`. -/
theorem two_mul_Vop_Theta {αG : ℝ} (hαG : 0 < αG) {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    2 * αG * Work.Construction.Vop (Work.Construction.Theta αG F) z θ
      = Work.Construction.L12 F z * Work.Construction.c2m θ := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hα0 : αG ≠ 0 := ne_of_gt hαG
  have hpth : Work.Spaces.pth (Work.Construction.Theta αG F) z θ
      = (1 / (2 * αG)) * Real.cos (2 * θ) * Work.Construction.L12 F z :=
    Work.Construction.pth_Theta_eq hαG z θ
  simp only [Work.Construction.Vop, hpth, Work.Construction.Theta, Work.Construction.s2,
    Work.Construction.c2m, Real.tan_eq_sin_div_cos]
  rw [Real.sin_two_mul, Real.cos_two_mul']
  field_simp
  rw [Real.sin_sq]
  ring

/-- The `θ`-slice of `Θ αG F` is differentiable everywhere. -/
theorem differentiableAt_thetaslice_Theta {αG : ℝ} {F : ℝ → ℝ → ℝ} (z θ : ℝ) :
    DifferentiableAt ℝ (fun θ' => Work.Construction.Theta αG F z θ') θ := by
  have hfun : (fun θ' => Work.Construction.Theta αG F z θ')
      = fun θ' => ((1 / (4 * αG)) * Work.Construction.L12 F z) * Real.sin (2 * θ') := by
    funext θ'
    simp only [Work.Construction.Theta, Work.Construction.s2]
    ring
  rw [hfun]
  exact (differentiableAt_const _).mul
    ((Real.differentiableAt_sin).comp θ ((differentiableAt_id (x := θ)).const_mul (2 : ℝ)))

/-! ## 3. The sharp split of `V(Φ)` -/

/-- **The sharp split.**  If `Φ = Φs + E u` pointwise and the two `θ`-slices are differentiable,
then at `z ≥ 0`, `0 < θ < π/2`,

    V(Φ) = V(Φ̃_*) + c2m(θ)/(1+z) + V(E u),      Φ̃_* = Φs − Θ(F_*).

The two `Θ`-parts of `Φs` and `Φ` cancel against `L₁₂(F_*)·c2m/(2αG) = c2m/(1+z)`, leaving only
the *star* slot and the *elliptic* slot: this is exactly what makes the smallness criterion
`2·Cs·αG² + 2·CE·αG²` (and not `O(αG)`) appear in `vz7_nonneg_of_sharp`. -/
theorem vop_slice_eq_star_add_E {αG : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {Φs : Fn} {E : Fn → Fn} {u Φ : Fn} {z θ : ℝ} (hz : 0 ≤ z)
    (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2)
    (hslice : ∀ z θ, Φ z θ = Φs z θ + E u z θ)
    (hdΦs : DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hdE : DifferentiableAt ℝ (fun θ' => E u z θ') θ) :
    Work.Construction.Vop Φ z θ
      = Work.Construction.Vop
          (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ
        + Work.Construction.c2m θ / (1 + z)
        + Work.Construction.Vop (E u) z θ := by
  -- `Φ = (Φ̃_* + Θ(F_*)) + E u` as functions
  have hΦeq : Φ = fun z θ => (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs z θ
      + Work.Construction.Theta αG (Work.Construction.Fstar αG) z θ) + E u z θ := by
    funext a b
    rw [hslice a b]
    simp only [Work.Construction.PhiTil]
    ring
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
  -- the two additive splits
  have hV1 := Vop_add_point (A := fun z θ => Work.Construction.PhiTil αG
      (Work.Construction.Fstar αG) Φs z θ
      + Work.Construction.Theta αG (Work.Construction.Fstar αG) z θ) (B := E u) hdSum hdE
  have hV2 := Vop_add_point (A := Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)
    (B := Work.Construction.Theta αG (Work.Construction.Fstar αG)) hdTil hdΘs
  -- the `Θ`-identity, divided by `2 αG`
  have hVΘ := two_mul_Vop_Theta (αG := αG) hαG (F := Work.Construction.Fstar αG)
    (z := z) (θ := θ) hθ hθ2
  rw [Work.Construction.L12_Fstar_eq (α := αG) hαG hαG1 hz] at hVΘ
  have hVΘ' : Work.Construction.Vop
        (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
      = Work.Construction.c2m θ / (1 + z) := by
    have h3 : 2 * αG * Work.Construction.Vop
          (Work.Construction.Theta αG (Work.Construction.Fstar αG)) z θ
        = 2 * αG * (Work.Construction.c2m θ / (1 + z)) := by
      rw [hVΘ]
      field_simp
    exact mul_left_cancel₀ (by positivity : (2 : ℝ) * αG ≠ 0) h3
  rw [hΦeq, hV1, hV2, hVΘ']

/-! ## 4. The criterion -/

/-- **The criterion.**  If `V(Φ) = A + c2m(θ)/(1+z) + B` at a point of the open quadrant with
`|A| ≤ Cs·αG`, `|B| ≤ CE·αG` and `|μ τ| ≤ 1/2`, then

    Vz7 = (1 − μτ) + 2·αG·V(Φ) ≥ 0

as soon as `4·αG + 2·Cs·αG² + 2·CE·αG² ≤ 1/2`.  (No positivity of `Cs, CE` is needed, and the
angular variable enters only through `c2m θ`.) -/
theorem vz7_nonneg_of_sharp {αG Cs CE : ℝ} (hαG : 0 < αG)
    {μ : ℝ → ℝ} {G Φ : Fam} {A B : Fn} {τ z θ : ℝ}
    (hz : 0 < z) (hmu : |μ τ| ≤ 1 / 2)
    (hsplit : Work.Construction.Vop (slice Φ τ) z θ
      = A z θ + Work.Construction.c2m θ / (1 + z) + B z θ)
    (hA : |A z θ| ≤ Cs * αG) (hB : |B z θ| ≤ CE * αG)
    (hclosed : Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ
      = (1 - μ τ) + 2 * αG * Work.Construction.Vop (slice Φ τ) z θ)
    (hnum : 4 * αG + 2 * Cs * αG ^ 2 + 2 * CE * αG ^ 2 ≤ 1 / 2) :
    0 ≤ Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ := by
  rw [hclosed, hsplit]
  have hden : (0 : ℝ) < 1 + z := by linarith
  have hc2m : -(2 : ℝ) ≤ Work.Construction.c2m θ := by
    have h := Work.FTS_RegExport.RXVP.abs_c2m_le_two θ
    linarith [neg_abs_le (Work.Construction.c2m θ)]
  have hmu1 : (1 : ℝ) / 2 ≤ 1 - μ τ := by
    have h := (abs_le.mp hmu).2
    linarith
  -- the three lower bounds, scaled by `2 αG > 0`
  have hA' : -(2 * Cs * αG ^ 2) ≤ 2 * αG * A z θ := by
    have h1 : -Cs * αG ≤ A z θ := by
      have h := (abs_le.mp hA).1
      linarith
    nlinarith [hαG, h1]
  have hc2m' : -(4 * αG) ≤ 2 * αG * (Work.Construction.c2m θ / (1 + z)) := by
    have h1 : (0 : ℝ) < 2 * αG / (1 + z) := by positivity
    have h3 : (2 * αG / (1 + z)) * (-2) ≤ (2 * αG / (1 + z)) * Work.Construction.c2m θ :=
      mul_le_mul_of_nonneg_left hc2m h1.le
    have h4 : (2 * αG / (1 + z)) * Work.Construction.c2m θ
        = 2 * αG * (Work.Construction.c2m θ / (1 + z)) := by ring
    have h5 : (2 * αG / (1 + z)) * (-2) = -(4 * αG) + (4 * αG) * z / (1 + z) := by
      field_simp
      ring
    have h6 : 0 ≤ (4 * αG) * z / (1 + z) := by positivity
    linarith [h3, h4, h5, h6]
  have hB' : -(2 * CE * αG ^ 2) ≤ 2 * αG * B z θ := by
    have h1 : -CE * αG ≤ B z θ := by
      have h := (abs_le.mp hB).1
      linarith
    nlinarith [hαG, h1]
  have hsum : 2 * αG * (A z θ + Work.Construction.c2m θ / (1 + z) + B z θ)
      = 2 * αG * A z θ + 2 * αG * (Work.Construction.c2m θ / (1 + z)) + 2 * αG * B z θ := by
    ring
  rw [hsum]
  nlinarith [hA', hc2m', hB', hmu1, hnum]

/-- **The criterion, with the split and the closed form discharged.**  For
`Φ = psiR α Φs E (tauExt g)` (so that `slice Φ τ = Φs + E (slice (tauExt g) τ)` on the open
quadrant) and `u = slice (tauExt g) τ`, `vz0` holds at `(z,θ,τ)` as soon as the two slot bounds
`|V(Φ̃_*)| ≤ Cs αG`, `|V(E u)| ≤ CE αG` hold and `4·αG + 2·Cs·αG² + 2·CE·αG² ≤ 1/2`. -/
theorem vz7_nonneg_of_vop_split {αG : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {μ : ℝ → ℝ} {G Φ : Fam} {Φs : Fn} {E : Fn → Fn} {u : Fn} {τ z θ : ℝ}
    {Cs CE : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) (hmu : |μ τ| ≤ 1 / 2)
    (hslice : ∀ z θ, slice Φ τ z θ = Φs z θ + E u z θ)
    (hdθΦ : DifferentiableAt ℝ (fun θ' => slice Φ τ z θ') θ)
    (hdzΦ : DifferentiableAt ℝ (fun z' => slice Φ τ z' θ) z)
    (hint : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Construction.Ftau αG G τ)) (Set.Ioi 0))
    (hcont : ContinuousAt
      (Work.Construction.L12dens (Work.Construction.Ftau αG G τ)) z)
    (hdΦs : DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hdE : DifferentiableAt ℝ (fun θ' => E u z θ') θ)
    (hA : |Work.Construction.Vop
      (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs) z θ| ≤ Cs * αG)
    (hB : |Work.Construction.Vop (E u) z θ| ≤ CE * αG)
    (hnum : 4 * αG + 2 * Cs * αG ^ 2 + 2 * CE * αG ^ 2 ≤ 1 / 2) :
    0 ≤ Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ := by
  have hclosed := (Work.FTS_RegExport.RXDiag.closedFormOpen (αG := αG) hαG
    (μ := μ) (G := G) (Φ := Φ) (τ := τ) (z := z) (θ := θ) hz hθ hθ2 hdθΦ hdzΦ hint hcont).1
  have hsplit := vop_slice_eq_star_add_E (αG := αG) hαG hαG1 (Φs := Φs) (E := E) (u := u)
    (Φ := slice Φ τ) (z := z) (θ := θ) hz.le hθ hθ2 hslice hdΦs hdE
  exact vz7_nonneg_of_sharp (αG := αG) hαG hz hmu hsplit hA hB hclosed hnum

/-! ## 5. Discharging the star slot from `StarPkgo2.VW` -/

/-- The `VW` field of `StarPkgo2` (`WlInf α 4 (V(Φ̃_*)) ≤ Cs·α`, plus its `WlInfMem`) gives the
pointwise bound `|V(Φ̃_*)(z,θ)| ≤ Cs·α` on the closed quadrant.  This is the *first* of the two
inputs of `vz7_nonneg_of_sharp`, and it is a *field* of the frozen `hStar`. -/
theorem starVop_pointwise_le {α Cs : ℝ} {Φs : Fn}
    (hmem : Work.Spaces.WlInfMem α 4 (Work.Construction.Vop
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)))
    (hbnd : Work.Spaces.WlInf α 4 (Work.Construction.Vop
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) ≤ Cs * α) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ Cs * α := by
  intro z θ hz hθ hθ2
  have h1 : |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
        z θ|
      ≤ Work.Spaces.WlInf α 4 (Work.Construction.Vop
          (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) := by
    have h := Work.Spaces.WlInf_z_bound α 4 _ hmem 0 (by norm_num) z θ
      (show z ∈ Work.Spaces.Iz from Set.mem_Ici.mpr hz.le)
      (show θ ∈ Work.Spaces.Iθ from Set.mem_Icc.mpr ⟨hθ.le, hθ2.le⟩)
    simpa using h
  exact le_trans h1 hbnd

/-- **The complete chain from the frozen `hStar` to `vz0`.**  With `hStar.VW` discharging the star
slot and a single bound `|V(E u)| ≤ CE·αG` for the elliptic slot, `vz0` holds at `(z,θ,τ)` as soon
as `4·αG + 2·Cs·αG² + 2·CE·αG² ≤ 1/2` — the two slot constants now enter *quadratically*.  This is
the form in which the wire's `α ≤ 8·10⁻⁹` makes the criterion constant-free. -/
theorem vz7_nonneg_of_starVW_E {αG : ℝ} (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    {μ : ℝ → ℝ} {G Φ : Fam} {Φs : Fn} {E : Fn → Fn} {u : Fn} {τ z θ : ℝ} {Cs CE : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) (hmu : |μ τ| ≤ 1 / 2)
    (hslice : ∀ z θ, slice Φ τ z θ = Φs z θ + E u z θ)
    (hdθΦ : DifferentiableAt ℝ (fun θ' => slice Φ τ z θ') θ)
    (hdzΦ : DifferentiableAt ℝ (fun z' => slice Φ τ z' θ) z)
    (hint : MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Construction.Ftau αG G τ)) (Set.Ioi 0))
    (hcont : ContinuousAt
      (Work.Construction.L12dens (Work.Construction.Ftau αG G τ)) z)
    (hdΦs : DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hdE : DifferentiableAt ℝ (fun θ' => E u z θ') θ)
    (hVWmem : Work.Spaces.WlInfMem αG 4 (Work.Construction.Vop
      (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)))
    (hVWbnd : Work.Spaces.WlInf αG 4 (Work.Construction.Vop
      (Work.Construction.PhiTil αG (Work.Construction.Fstar αG) Φs)) ≤ Cs * αG)
    (hB : |Work.Construction.Vop (E u) z θ| ≤ CE * αG)
    (hnum : 4 * αG + 2 * Cs * αG ^ 2 + 2 * CE * αG ^ 2 ≤ 1 / 2) :
    0 ≤ Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ :=
  vz7_nonneg_of_vop_split (αG := αG) hαG hαG1 hz hθ hθ2 hmu hslice hdθΦ hdzΦ hint hcont
    hdΦs hdE (starVop_pointwise_le hVWmem hVWbnd z θ hz hθ hθ2) hB hnum

end Work.FTS_RegExport
