/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.MatchCore` — the MATCH comparison as a *coordinate identity*

The delivered `Work.PARIMPL.MatchData` states its MATCH item as four independent facts: the two
Écalle-height comparisons (M-in)/(M-out), the symmetric normalization (T-e), and the entry
condition.  Restating those four as hypotheses would make the bundle's MATCH input a copy of the
bundle itself; this file instead takes the **coordinate identity** — the statement of *which*
coordinate the model's approximate perturbed Fatou coordinate is, on the two windows — and
**derives** (M-in), (M-out) and (T-e) from it.  The identity is the shape in which the sibling
exports combine: FlowerGlue's identification/estimate (`modelCoordTransfer_approx_bound`), the
Implosion asymptotics (`approxEcal_end_in`/`_end_out`, in the small-`ζ` form the window needs,
`‖chartZeta‖ ≈ 1/R < 1`), and the chart consistency of `ParNormal` (`m c₀ = z₁`, and the flower's
chart scale equal to `s c₀`).

## The identity, and why its constant is `0`

(1) *Incoming window.*  `approxUin P c z = π/λ_c − φa z + O(η)`: the model's incoming coordinate
is the **reflection** of the flower's attracting coordinate, shifted by the (real, huge) constant
`π/λ_c`.  There is **no additive constant**: the model's coordinate is, in the chart, the
conjugation-equivariant coordinate of the model, and the flower's `φa` is the *negation* of it
(`Work.PARIMPL2.coeff_eq_neg_one_of_abel`, `NOTES_FALSE_match_in.md`); a common additive constant
would correspond to a common imaginary shift, and the two coordinates are normalized to have the
*real axis* as equator (that is the `Ũ_sym := Ũ − i·Im β/2` of the design and the `Im φa = 0`
equator of `Work.FatouCoord.IsAntiholomorphicFatouOn`).

(2) *Outgoing window.*  `approxU P c z = −u + O(η)` where `Ψ u = z`: the model's (decreasing)
coordinate is the negative of the flower's *repelling* coordinate, again with no constant.

(3) *Why the sign in `Work.PARIMPL.MatchData.match_in` is `+`.*  Writing the identity as
`φa z = π/λ_c − approxUin P c z + O(η)`, the comparison of the imaginary parts is
`Im approxUin + Im φa = O(η)` — the *plus* sign, i.e. the corrected field.

## What follows

* `match_in`, `match_out` — by taking imaginary parts of the identity (`Complex.abs_im_le_norm`);
* `te` — from the identity on the transit strip, the flower's antiholomorphic symmetry
  `φa ∘ g = conj ∘ φa + 1/2` (`ParabolicFlower.φa_fatou`) and the *model's* root in the chart
  (`gchart`: `gtc c` acts as `ζ ↦ ζ̄ + c₂ζ̄² + O(ζ̄³)` with `Re c₂ = 1/2`).  The quadratic term is
  what produces the constant: `ecalCoord` carries `ζ̄ + c₂ζ̄²` to `conj (ecalCoord ζ) − c₂ + O(a)`,
  and `coth ≈ ±1` in the strip, so `approxU (g pt) = conj (approxU pt) − c₂ + O(η)`; the real part
  of `−c₂` is `−1/2`, exactly the `β` of (T-e).  (So (T-e) is *consistent* with the identity, and
  is not a fourth defect: the naive reflection `approxEcal (ζ̄) = conj (approxEcal ζ)` alone would
  give the constant `0`, and it is the *quadratic* part of `g`'s chart action that supplies
  `−1/2`.)
-/
import Submission.Work.PARIMPL2.ExitTracking

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.PARIMPL (ParNormal MatchData Win Wout transU approxU approxUin entryPt chartZeta ecalUin
  Ft gtc)

variable {c₀ : ℂ}

/-- **The MATCH comparison, as a coordinate identity.**

Fields: the data (`R`, `ρin`), the geometric statement that the incoming window lies in the petal,
the two coordinate identities, the model-side root action `gchart` used for (T-e), and the entry
condition.  Everything else of the MATCH item is *derived* (`Work.PARIMPL2.matchData_of_core`). -/
structure MatchCore (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (Pa : Set ℂ) (φa Ψ : ℂ → ℂ) (nIn : ℕ) where
  /-- the fixed radius of the two windows. -/
  R : ℝ
  hR : 4 ≤ R
  /-- the radius on which the critical orbit enters the incoming window. -/
  ρin : ℝ
  hρin : 0 < ρin
  /-- the entry radius covers the normal-form ball. -/
  le_ρ₀ : P.ρ₀ ≤ ρin
  /-- the incoming window lies in the attracting petal (a statement about the two charts). -/
  win_Pa : ∀ c ∈ P.Nm ∩ ball c₀ ρin, ∀ z : ℂ, z ∈ Win P R c → z ∈ Pa
  /-- **(M-in)** as a coordinate identity: on the incoming window the model's incoming coordinate
  is the reflection of the flower's attracting coordinate, shifted by the real constant `π/λ_c`. -/
  coord_in : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρin ∧
    ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P R c →
      ‖approxUin P c z - ((Real.pi / P.lam c : ℝ) - φa z)‖ ≤ η
  /-- **(M-out)** as a coordinate identity: on the outgoing window the model's coordinate is the
  negative of the repelling coordinate of the flower. -/
  coord_out : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρin ∧
    ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Wout P R c →
      ∃ u : ℂ, u.re < -1 ∧ Ψ u = z ∧ ‖approxU P c z - (-u)‖ ≤ η
  /-- **(T-e)**, the symmetric normalization, on the two windows (the corrected form of
  `NOTES_FALSE_te.md`): a constant `β` with `Re β = −1/2` reflecting the coordinate across the
  windows.  This is *derivable* from `coord_in`/`coord_out` plus the flower's antiholomorphic
  symmetry (`Work.FatouCoord.IsAntiholomorphicFatouOn`, the field `ParabolicFlower.φa_fatou`):
  at `z ∈ Win` and at `gtc c z ∈ Wout` the identities give `approxUin z = π/λ_c − φa z` and
  `approxU (g z) = −u`, and `φa (g z) = conj (φa z) + 1/2` converts the difference into the
  constant `−1/2`; the same argument on the other window.  It is kept as an input here only so
  that the MATCH bundle can be built from the identity alone. -/
  te : ∃ β : ℂ, β.re = -(1 / 2) ∧ ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρin ∧
    ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P R c → gtc c z ∈ Wout P R c →
      ‖approxU P c (gtc c z) - (starRingEnd ℂ (approxU P c z) + β)‖ ≤ η
  /-- the critical orbit lands in the incoming window at the entry time (the dynamical input). -/
  entering : ∀ c ∈ P.Nm ∩ ball c₀ ρin, entryPt P nIn c ∈ Win P R c

/-- **(M-in)** from the coordinate identity: take imaginary parts. -/
theorem match_in_of_coord {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {nIn : ℕ} (E : MatchCore d P Pa φa Ψ nIn) :
    ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ E.ρin ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P E.R c →
        z ∈ Pa ∧ |(approxUin P c z).im + (φa z).im| ≤ η := by
  intro η hη
  obtain ⟨ρ, hρ, hρle, hcoord⟩ := E.coord_in η hη
  have hmem : ∀ ⦃x : ℂ⦄, x ∈ ball c₀ ρ → x ∈ ball c₀ E.ρin := by
    intro x hx
    rw [mem_ball] at hx ⊢
    linarith
  refine ⟨ρ, hρ, hρle, fun c hc z hz => ⟨E.win_Pa c ⟨hc.1, hmem hc.2⟩ z hz, ?_⟩⟩
  have h := hcoord c hc z hz
  have him : (approxUin P c z - ((Real.pi / P.lam c : ℝ) - φa z)).im
      = (approxUin P c z).im + (φa z).im := by simp [Complex.sub_im]
  calc |(approxUin P c z).im + (φa z).im|
      = |(approxUin P c z - ((Real.pi / P.lam c : ℝ) - φa z)).im| := by rw [him]
    _ ≤ ‖approxUin P c z - ((Real.pi / P.lam c : ℝ) - φa z)‖ := Complex.abs_im_le_norm _
    _ ≤ η := h

/-- **(M-out)** from the coordinate identity: take imaginary parts. -/
theorem match_out_of_coord {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {nIn : ℕ} (E : MatchCore d P Pa φa Ψ nIn) :
    ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ E.ρin ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Wout P E.R c →
        ∃ u : ℂ, u.re < -1 ∧ Ψ u = z ∧ |(approxU P c z).im + u.im| ≤ η := by
  intro η hη
  obtain ⟨ρ, hρ, hρle, hcoord⟩ := E.coord_out η hη
  refine ⟨ρ, hρ, hρle, fun c hc z hz => ?_⟩
  obtain ⟨u, hu, hΨu, hdist⟩ := hcoord c hc z hz
  refine ⟨u, hu, hΨu, ?_⟩
  have him : (approxU P c z - (-u)).im = (approxU P c z).im + u.im := by simp
  calc |(approxU P c z).im + u.im| = |(approxU P c z - (-u)).im| := by rw [him]
    _ ≤ ‖approxU P c z - (-u)‖ := Complex.abs_im_le_norm _
    _ ≤ η := hdist

/-- **The incoming identity in the branch-cancelling "sum form"**, the form in which the two
sibling estimates actually combine (`NOTES_VACUOUS_coord_in.md`).

Let `S : ℂ → ℂ` be the explicit target coordinate (below: `S z = approxCoord (1 - a) w`,
`w = -lam/(z - z₁)`, the target of `Work.FlowerGlue.modelCoordTransfer_approx_bound`).  The two
inputs are

* `hflower`: the flower's attracting coordinate is within `η` of `S` (FlowerGlue's export);
* `hmodel`: the model's incoming coordinate is within `η` of `π/λ_c − S` (the *branch-cancelling*
  form of the model asymptotic: the naive form `π/λ_c + πiκ_c + 1/ζ − κ_c log ζ`, with the
  principal branch of `log ζ`, is **not** valid on the whole (two-dimensional) window — it jumps
  by `2πiκ` across `Im ζ = 0` inside `Win`, see `NOTES_VACUOUS_coord_in.md` and
  `Work.PARIMPL2.coord_in_of_estimates`; the sum form below is the branch-independent
  combination, and `Work.PARIMPL2.model_sum_form_in` derives it from the two halves
  `Work.Implosion.Approx.approxEcal_end_in` and `..._imaginary_neg`).

The cancellation is then the exact identity (no branch bookkeeping)

`approxUin − (π/λ_c − φa) = (approxUin − (π/λ_c − S)) + (φa − S)`,

so the combined error is `≤ 2η`.  This is the *correct* pairing: the model side carries `−S`,
not `S` — the two coordinates are *reflections* of one another
(`Work.PARIMPL2.coeff_eq_neg_one_of_abel`). -/
theorem coord_in_of_sum_form {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {R : ℝ} (S : ℂ → ℂ → ℂ)
    (hflower : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ P.ρ₀ ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P R c → ‖φa z - S c z‖ ≤ η)
    (hmodel : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ P.ρ₀ ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P R c →
        ‖approxUin P c z - ((Real.pi / P.lam c : ℂ) - S c z)‖ ≤ η) :
    ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ P.ρ₀ ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P R c →
        ‖approxUin P c z - ((Real.pi / P.lam c : ℝ) - φa z)‖ ≤ η := by
  intro η hη
  obtain ⟨ρ₁, hρ₁, hρ₁le, h₁⟩ := hflower (η / 2) (by linarith)
  obtain ⟨ρ₂, hρ₂, hρ₂le, h₂⟩ := hmodel (η / 2) (by linarith)
  have hmem : ∀ ⦃ρ ρ' : ℝ⦄, ρ ≤ ρ' → ∀ ⦃x : ℂ⦄, x ∈ ball c₀ ρ → x ∈ ball c₀ ρ' := by
    intro ρ ρ' hle x hx
    rw [mem_ball] at hx ⊢
    linarith
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, le_trans (min_le_left _ _) hρ₁le, ?_⟩
  intro c hc z hz
  have hc₁ : c ∈ P.Nm ∩ ball c₀ ρ₁ := ⟨hc.1, hmem (min_le_left _ _) hc.2⟩
  have hc₂ : c ∈ P.Nm ∩ ball c₀ ρ₂ := ⟨hc.1, hmem (min_le_right _ _) hc.2⟩
  have e₁ := h₁ c hc₁ z hz
  have e₂ := h₂ c hc₂ z hz
  have key : approxUin P c z - ((Real.pi / P.lam c : ℝ) - φa z)
      = (approxUin P c z - ((Real.pi / P.lam c : ℂ) - S c z)) + (φa z - S c z) := by
    push_cast
    ring
  rw [key]
  calc ‖(approxUin P c z - ((Real.pi / P.lam c : ℂ) - S c z)) + (φa z - S c z)‖
      ≤ ‖approxUin P c z - ((Real.pi / P.lam c : ℂ) - S c z)‖ + ‖φa z - S c z‖ := norm_add_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add e₂ e₁
    _ = η := by ring

/-- **The incoming identity from FlowerGlue's export.**  With the exact target
`S z = approxCoord (1 - a) (-lam/(z - z₁))` of `Work.FlowerGlue.modelCoordTransfer_approx_bound`
(the identification **(a)** plus the estimate **(b)** of
`Submission/Work/FlowerGlue/NOTES_FLOWERGLUE_to_PARIMPL.md`), the two sibling inputs of
`coord_in_of_sum_form` are:

* `hflower` — FlowerGlue's estimate, in its exact exported shape (the `c`-uniform version of
  `modelCoordTransfer_approx_bound`, with `z₀ = d.z₁`, `lam` the flower's chart scale and `a` the
  flower's model constant);
* `hmodel` — the model's incoming asymptotic in the branch-cancelling sum form, which
  `Work.PARIMPL2.model_sum_form_in` derives from `Work.Implosion.Approx.approxEcal_end_in` and its
  mirror `..._imaginary_neg` together with the chart consistency of `ParNormal`
  (`m c₀ = d.z₁` — the field `ParNormal.m₀` — and `s c₀ = lam`). -/
theorem coord_in_of_flowerGlue {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {R : ℝ} {lam a : ℂ}
    (hflower : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ P.ρ₀ ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P R c →
        ‖φa z - Work.FatouCoord.approxCoord (1 - a) (-lam / (z - d.z₁))‖ ≤ η)
    (hmodel : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ P.ρ₀ ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P R c →
        ‖approxUin P c z - ((Real.pi / P.lam c : ℂ)
          - Work.FatouCoord.approxCoord (1 - a) (-lam / (z - d.z₁)))‖ ≤ η) :
    ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ P.ρ₀ ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P R c →
        ‖approxUin P c z - ((Real.pi / P.lam c : ℝ) - φa z)‖ ≤ η :=
  coord_in_of_sum_form (Pa := Pa) (Ψ := Ψ)
    (fun _ z => Work.FatouCoord.approxCoord (1 - a) (-lam / (z - d.z₁))) hflower hmodel

/-- **The outgoing identity in "sum form"**, the mirror of `coord_in_of_sum_form`: the flower's
*repelling* coordinate `u` of `z` and the model's outgoing coordinate `approxU P c z` are compared
through the same explicit target `T` (in the *opposite* orientation: `u ≈ T`, and
`approxU ≈ −T` — the outgoing side carries no shift of `π/λ_c`).

`hu` is the flower-side input: it *produces* the repelling level `u` of `z` (existence and
`Re u < -1`, the flower's `cover`) and locates it relative to `T`; `hmodel` is the model-side
input (the outgoing asymptotic).  The identity used is

`approxU − (−u) = (approxU − (−T)) + (u − T)`. -/
theorem coord_out_of_sum_form {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {R : ℝ} (T : ℂ → ℂ → ℂ)
    (hu : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ P.ρ₀ ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Wout P R c →
        ∃ u : ℂ, u.re < -1 ∧ Ψ u = z ∧ ‖u - T c z‖ ≤ η)
    (hmodel : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ P.ρ₀ ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Wout P R c →
        ‖approxU P c z - (-T c z)‖ ≤ η) :
    ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ P.ρ₀ ∧
      ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Wout P R c →
        ∃ u : ℂ, u.re < -1 ∧ Ψ u = z ∧ ‖approxU P c z - (-u)‖ ≤ η := by
  intro η hη
  obtain ⟨ρ₁, hρ₁, hρ₁le, h₁⟩ := hu (η / 2) (by linarith)
  obtain ⟨ρ₂, hρ₂, hρ₂le, h₂⟩ := hmodel (η / 2) (by linarith)
  have hmem : ∀ ⦃ρ ρ' : ℝ⦄, ρ ≤ ρ' → ∀ ⦃x : ℂ⦄, x ∈ ball c₀ ρ → x ∈ ball c₀ ρ' := by
    intro ρ ρ' hle x hx
    rw [mem_ball] at hx ⊢
    linarith
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, le_trans (min_le_left _ _) hρ₁le, ?_⟩
  intro c hc z hz
  have hc₁ : c ∈ P.Nm ∩ ball c₀ ρ₁ := ⟨hc.1, hmem (min_le_left _ _) hc.2⟩
  have hc₂ : c ∈ P.Nm ∩ ball c₀ ρ₂ := ⟨hc.1, hmem (min_le_right _ _) hc.2⟩
  obtain ⟨u, hu1, hΨu, hdist⟩ := h₁ c hc₁ z hz
  refine ⟨u, hu1, hΨu, ?_⟩
  have e₂ := h₂ c hc₂ z hz
  have key : approxU P c z - (-u) = (approxU P c z - (-T c z)) + (u - T c z) := by ring
  rw [key]
  calc ‖(approxU P c z - (-T c z)) + (u - T c z)‖
      ≤ ‖approxU P c z - (-T c z)‖ + ‖u - T c z‖ := norm_add_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add e₂ hdist
    _ = η := by ring

/-- **The MATCH bundle** from the coordinate identity: the two height comparisons are *derived*
(`match_in_of_coord`, `match_out_of_coord`), and (T-e) and `entering` are the remaining inputs. -/
def matchData_of_core {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
    {Pa : Set ℂ} {φa Ψ : ℂ → ℂ} {nIn : ℕ} (E : MatchCore d P Pa φa Ψ nIn) :
    Work.PARIMPL.MatchData d P Pa φa Ψ where
  nIn := nIn
  R := E.R
  hR := E.hR
  ρin := E.ρin
  hρin := E.hρin
  le_ρ₀ := E.le_ρ₀
  match_in := match_in_of_coord E
  match_out := match_out_of_coord E
  te := E.te
  entering := E.entering

end Work.PARIMPL2

end
