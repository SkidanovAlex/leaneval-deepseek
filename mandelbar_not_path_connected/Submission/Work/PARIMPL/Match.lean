/-
Copyright: subproject `Submission/Work/PARIMPL/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.Match` — MATCH: the approximate coordinate meets the `c₀`-flower

Item §1.2 of `Submission/Work/NOTES_LEAD_mandelbar_residuals.md`: the comparison of the local
model of `Work.PARIMPL.ParNormal` (the chart `z = m c + s c·ζ`, the approximate perturbed Fatou
coordinate `Ũ_c = approxEcal (a c) (κ c) ·`) with the **Leau–Fatou flower** of the characteristic
parabolic point `z₁` of the second return map `F c₀ = (T_{c₀})^10` at the root arc parameter `c₀`
(`Work.FatouCoord.ParabolicFlower`).

## The three items of §1.2

* **(M-in)** — the *incoming* window
  `Win R c = {z | Re Ũ_c(u_c z) ∈ [π/λ_c − 2R, π/λ_c − R]}` is inside the attracting petal `Pa`
  of the flower and carries the same **Écalle height** as the flower's Fatou coordinate `φa`;
* **(M-out)** — the *outgoing* window `Wout R c = {R ≤ Re Ũ_c ≤ R + 1}` lies in the repelling
  region of the flower (`Ψ u = z` with `Re u < −1`) and carries the same Écalle height as the
  repelling coordinate `u`;
* **(T-e)** — the *symmetric normalization*: on the transit region the approximate coordinate
  reflects the antiholomorphic square root `G = (T_{c₀})^5` up to a constant `β` whose real part
  is `−1/2` (the `w ↦ w̄ + 1/2` of Hubbard–Schleicher Lemma 2.3); the real shift by `Im β / 2` is
  what makes `Ũ` **equator-symmetric**.

## Encoding remark (read this before changing the signatures)

A `structure` whose *parameter* or *field type* mentions the Leau–Fatou flower
`Work.FatouCoord.ParabolicFlower (Ft c₀) (gtc c₀) z₁` — or any abbreviation of it — makes the
elaborator diverge on the smart unfolding of the iterate `(T_{c₀})^[5]` (`isDefEq` heartbeat
timeout).  The same phenomenon is documented in `Submission/Work/Final/Defs.lean`.  Hence the
structures below take only *plain* data as parameters: the petal `Pa`, the two coordinates
`φa`, `Ψ` and the antiholomorphic root `G` are parameters of type `Set ℂ`, `ℂ → ℂ`, `ℂ → ℂ`; the
caller instantiates them with `fl.Pa`, `fl.φa`, `fl.Ψ`, `gtc c₀`.  *Statements* (as opposed to
structure declarations) may mention the flower freely, as in
`Work.PARIMPL.MatchData.ofFlower` below.

## Main results

* `Work.PARIMPL.nEnter`, `Work.PARIMPL.critHeight` — the entry time of the critical orbit into
  the petal and the critical Écalle height (matching `Work.Final.RootArc.nEnter`/`critHeight`);
* `Work.PARIMPL.ecalU`, `Work.PARIMPL.approxU`, `Work.PARIMPL.Win`, `Work.PARIMPL.Wout` — the
  model coordinates and the two windows;
* `Work.PARIMPL.MatchData` — the holder structure for (M-in), (M-out), (T-e);
* `Work.PARIMPL.FlowerFix`, `Work.PARIMPL.ZDecay` — the two named `FatouCoord` inputs.
-/
import Submission.Work.PARIMPL.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c₀ : ℂ}

/-! ## The entry time and the critical height -/

/-- The **entry time** of the critical orbit of `Ft c₀ = (T_{c₀})^10` into the attracting petal
of the flower: the first time at which the critical orbit lands in `Pa`.  This is exactly
`Work.Final.RootArc.nEnter` for the root-arc data built from `d` and `fl`. -/
noncomputable def nEnter (d : Work.EL.RootParabolic c₀)
    (fl : Work.FatouCoord.ParabolicFlower (Ft c₀) (gtc c₀) d.z₁) : ℕ :=
  Nat.find (fl.enters_Pa c₀ d.crit.1 d.crit.2)

theorem nEnter_spec (d : Work.EL.RootParabolic c₀)
    (fl : Work.FatouCoord.ParabolicFlower (Ft c₀) (gtc c₀) d.z₁) :
    (Ft c₀)^[nEnter d fl] c₀ ∈ fl.Pa :=
  Nat.find_spec (fl.enters_Pa c₀ d.crit.1 d.crit.2)

/-- The critical orbit of `Ft c₀` never lands in the petal before the entry time. -/
theorem not_mem_Pa_of_lt_nEnter (d : Work.EL.RootParabolic c₀)
    (fl : Work.FatouCoord.ParabolicFlower (Ft c₀) (gtc c₀) d.z₁) {n : ℕ}
    (hn : n < nEnter d fl) : (Ft c₀)^[n] c₀ ∉ fl.Pa :=
  Nat.find_min (fl.enters_Pa c₀ d.crit.1 d.crit.2) hn

/-- The critical orbit of `Ft c₀` never hits `z₁` (`Work.EL.RootParabolic.crit`). -/
theorem critOrbit_ne (d : Work.EL.RootParabolic c₀) (n : ℕ) :
    (Ft c₀)^[n] c₀ ≠ d.z₁ :=
  d.crit.2 n

/-- The **critical Écalle height**: the imaginary part of the attracting Fatou coordinate of the
transited critical value at the entry time.  This is verbatim `Work.Final.RootArc.critHeight`
(its normalisation is `NOTES_LEAD_mandelbar_EL_F_contracts.md` §7.1). -/
noncomputable def critHeight (d : Work.EL.RootParabolic c₀)
    (fl : Work.FatouCoord.ParabolicFlower (Ft c₀) (gtc c₀) d.z₁) : ℝ :=
  (fl.φa ((Ft c₀)^[nEnter d fl] c₀)).im

/-- The critical value sits on the equator of the attracting Fatou coordinate. -/
theorem critHeight_eq_zero_iff_mem_equator (d : Work.EL.RootParabolic c₀)
    (fl : Work.FatouCoord.ParabolicFlower (Ft c₀) (gtc c₀) d.z₁) :
    critHeight d fl = 0 ↔
      (Ft c₀)^[nEnter d fl] c₀ ∈ Work.FatouCoord.equator fl.φa :=
  Iff.rfl

/-! ## The coordinates and the two windows -/

/-- The critical-orbit point at time `n` for the parameter `c`. -/
noncomputable def entryPt {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (n : ℕ) (c : ℂ) : ℂ :=
  (Ft c)^[n] c

/-- The chart coordinate of the local model at `c`: `z = m c + s c·ζ`. -/
noncomputable def chartZeta {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (c z : ℂ) : ℂ :=
  (z - P.m c) / P.s c

/-- The lifted Écalle coordinate of the local model at `c`, evaluated at the point `z`. -/
noncomputable def ecalU {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (c z : ℂ) : ℂ :=
  Work.Implosion.ecalCoord (P.a c) (chartZeta P c z)

/-- The **approximate perturbed Fatou coordinate** `Ũ_c` of the local model, evaluated at the
point `z`: `approxEcal (a c) (κ c)` of the principal Écalle coordinate.  This is the coordinate of
the **outgoing** (repelling) end of the transit: `approxEcal_end_out` identifies it with
`1/ζ − κ log ζ`, whose real part is `≈ R` at `ζ ≈ 1/R`. -/
noncomputable def approxU {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (c z : ℂ) : ℂ :=
  Work.Implosion.approxEcal (P.a c) (P.κ c) (ecalU P c z)

/-- The **incoming** lifted Écalle coordinate: the principal Écalle coordinate shifted by the
half-period `πi/a = π/λ_c`.  The incoming end of the transit (the petal side, `ζ` near `−1/R`)
sits at `Re = π/λ_c` in *this* coordinate, which is why the incoming window must be described with
it: the principal coordinate only ranges over `(−π/2λ_c, π/2λ_c]`, so a window at
`π/λ_c − O(1)` would be **empty** there.  This is the shift used by
`Work.Implosion.Approx.approxEcal_end_in`. -/
noncomputable def ecalUin {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (c z : ℂ) : ℂ :=
  ecalU P c z + Real.pi * Complex.I / (P.a c)

/-- The **approximate coordinate at the incoming end**: `approxEcal (a c) (κ c)` of the incoming
lifted Écalle coordinate `ecalUin`.  `approxEcal_end_in` identifies it with
`πi/a + πiκ + (1/ζ − κ log ζ)`, whose real part is `≈ π/λ_c + Re(1/ζ)` — i.e. `≈ π/λ_c − R` at
`ζ ≈ −1/R`, exactly the level of the incoming window `Win`. -/
noncomputable def approxUin {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (c z : ℂ) : ℂ :=
  Work.Implosion.approxEcal (P.a c) (P.κ c) (ecalUin P c z)

/-- The **transit coordinate**: minus the *incoming* approximate coordinate `approxUin` of the
critical-orbit point at the entry time `n`.  Its real part is `−(π/λ_c − O(1)) → −∞` as `c`
approaches the parabolic locus along the implosion side (the "phase blow-up" of HS §4 /
`NOTES_LEAD_mandelbar_residuals.md` §1.3), and its class modulo `ℤ` is the position at which the
critical orbit leaves the transit (§1.4). -/
noncomputable def transU {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (n : ℕ) (c : ℂ) : ℂ :=
  -approxUin P c (entryPt P n c)

/-- The **incoming window** of the transit at `c` at radius `R`: the points whose approximate
coordinate has real part in `[π/λ_c − 2R, π/λ_c − R]`, i.e. at distance between `R` and `2R`
from the upper end of the transit strip. -/
def Win {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d) (R : ℝ) (c : ℂ) : Set ℂ :=
  {z : ℂ | (approxUin P c z).re ∈ Set.Icc (Real.pi / P.lam c - 2 * R) (Real.pi / P.lam c - R)}

/-- The **outgoing window** of the transit at `c` at radius `R`: the points whose approximate
coordinate has real part in `[R, R + 1]`. -/
def Wout {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d) (R : ℝ) (c : ℂ) : Set ℂ :=
  {z : ℂ | (approxU P c z).re ∈ Set.Icc R (R + 1)}

theorem mem_Win {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d) (R : ℝ) (c z : ℂ) :
    z ∈ Win P R c ↔
      (approxUin P c z).re ∈ Set.Icc (Real.pi / P.lam c - 2 * R) (Real.pi / P.lam c - R) :=
  Iff.rfl

theorem mem_Wout {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d) (R : ℝ) (c z : ℂ) :
    z ∈ Wout P R c ↔ (approxU P c z).re ∈ Set.Icc R (R + 1) := Iff.rfl

/-- The real part of the transit coordinate is bounded above by `2R − π/λ_c` when the entry
point lies in the incoming window — the quantitative form of the **phase blow-up**. -/
theorem transU_re_le_of_mem_Win {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : ParNormal d)
    (n : ℕ) {R : ℝ} {c : ℂ} (hw : entryPt P n c ∈ Win P R c) :
    (transU P n c).re ≤ 2 * R - Real.pi / P.lam c := by
  simp only [transU, Complex.neg_re, mem_Win] at hw ⊢
  linarith [hw.1]

/-! ## The two named `FatouCoord` inputs of the residual note -/

/-- **The `FatouCoord` fix** of `NOTES_LEAD_mandelbar_residuals.md` §3.1: the attracting Fatou
coordinate of the flower is *shift-equivariant* on the petal, `φa ∘ F = φa + 1`, and there is a
`g`-invariant, `F`-invariant open sub-petal `Pg ⊆ Pa` on which `φa` is defined.

Not a field of `Work.FatouCoord.ParabolicFlower` yet; it is true for the constructed flower
(`φa = orbitCoord` on `Pa`, with `orbitCoord_shift`), and the two consumers of §3.1 are the
`phi_*` lemmas of `Work.Final.RootArc` and the `PetalInput` of `Work.FQC`. -/
structure FlowerFix {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    (F G : ℂ → ℂ) (z₀ : ℂ) (Pa : Set ℂ) (φa : ℂ → ℂ) where
  /-- the attracting Fatou coordinate advances by `1` per iterate of `F`. -/
  shift : ∀ z : ℂ, z ∈ Pa → φa (F z) = φa z + 1
  /-- the invariant half-plane sub-petal. -/
  Pg : Set ℂ
  Pg_sub : Pg ⊆ Pa
  isOpen_Pg : IsOpen Pg
  mapsTo_F_Pg : ∀ z : ℂ, z ∈ Pg → F z ∈ Pg
  mapsTo_G_Pg : ∀ z : ℂ, z ∈ Pg → G z ∈ Pg

/-- **The `Z`-decay of the repelling side** (`NOTES_LEAD_mandelbar_flower.md` §A.7): the defect
`Z` of the repelling conjugacy `V w = w + (1−a)Λ w + Z w` vanishes at the far repelling end.  At
the level of the flower this says that the repelling coordinate `Ψ` is **asymptotically
`z₁ + A/w`**, `w·(Ψ w − z₁) = A + O((1 + log ‖w‖)/‖w‖)`; it is what makes (M-out) hold. -/
structure ZDecay {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (Ψ : ℂ → ℂ) where
  /-- the asymptotic constant (the scale ratio of the two charts). -/
  A : ℂ
  A_ne : A ≠ 0
  /-- the decay constant. -/
  K : ℝ
  /-- the decay of the defect at the far repelling end. -/
  decay : ∀ w : ℂ, w.re < -1 → ‖w * (Ψ w - d.z₁) - A‖ ≤ K * (1 + Real.log ‖w‖) / ‖w‖

/-! ## MATCH -/

/-- **MATCH** — the comparison of the approximate perturbed Fatou coordinate of the local model
with the `c₀`-flower (items (M-in), (M-out), (T-e) of
`NOTES_LEAD_mandelbar_residuals.md` §1.2), at a root arc `d`, a parameter normal form `P`, the
petal `Pa`, the two coordinates `φa` (attracting) and `Ψ` (repelling), the antiholomorphic root
`G = (T_{c₀})^5`, and the entry time `nIn` (intended: `nEnter d fl`).

The radius `R` of the two windows is fixed by the data, and the entry radius `ρin` covers the
whole normal-form ball (`ρ₀ ≤ ρin`). -/
structure MatchData {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : ParNormal d)
    (Pa : Set ℂ) (φa : ℂ → ℂ) (Ψ : ℂ → ℂ) where
  /-- the entry time of the critical orbit into the petal. -/
  nIn : ℕ
  /-- the (fixed) radius of the incoming/outgoing windows. -/
  R : ℝ
  hR : 4 ≤ R
  /-- the radius on which the critical orbit enters the incoming window. -/
  ρin : ℝ
  hρin : 0 < ρin
  /-- the entry radius covers the normal-form ball. -/
  le_ρ₀ : P.ρ₀ ≤ ρin
  /-- **(M-in)**: the incoming window (described in the *lifted* incoming coordinate
  `approxUin`) is inside the attracting petal and its Écalle height is the **negative** of the
  flower's Fatou-coordinate height:

  `Im approxUin + Im φa ≤ η`.

  *Correction* (`Submission/Work/PARIMPL2/NOTES_FALSE_match_in.md`): the comparison was stated
  with `-`.  The model's `approxEcal` is a **decreasing** Abel coordinate of the local model
  (`Work.PARIMPL.approxEcal_step_rot`: one iterate moves it by `−τ`, `Re τ > 0`), while the
  flower's `φa` and `Ψ` are **increasing**; two Abel coordinates of the same map with opposite
  step signs are *reflections* of one another
  (`Work.PARIMPL2.coeff_eq_neg_one_of_abel`), so the heights compare with opposite signs.  The
  (T-e) field below records the same thing: `Re β = −1/2` is the reflection constant of the
  flower's `+1/2` (`Work.FatouCoord.IsAntiholomorphicFatouOn`).  With the old `-` the field forces
  `Im φa` to be constant on the window (`Work.PARIMPL2.im_const_of_im_eq_of_coeff`), which it is
  not.  The downstream uses (`TransitData.height`, hence `noPath`) are unaffected: `height` uses
  `(transU).im = -(approxUin).im` and a triangle inequality, which reads the same with `+`. -/
  match_in : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρin ∧
    ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P R c →
      z ∈ Pa ∧ |(approxUin P c z).im + (φa z).im| ≤ η
  /-- **(M-out)**: the outgoing window lies in the repelling region of the flower and its Écalle
  height is the **negative** of the repelling coordinate's:

  `Im approxU + Im u ≤ η`.

  Same correction as `match_in` (`Submission/Work/PARIMPL2/NOTES_FALSE_match_out.md`): `approxU`
  is the reflection of the repelling coordinate `u` (which is an *increasing* Abel coordinate,
  `ParabolicFlower.Ψ_shift`), so the heights are opposite up to the additive constant.  The
  uniform lock-step transit `UT` below is stated with `transU = -approxUin`, i.e. already in the
  corrected orientation. -/
  match_out : ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρin ∧
    ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Wout P R c →
      ∃ u : ℂ, u.re < -1 ∧ Ψ u = z ∧ |(approxU P c z).im + u.im| ≤ η
  /-- **(T-e)**, the symmetric normalization: on the two **windows** the approximate coordinate
  reflects the antiholomorphic square root up to a constant of real part `−1/2`.

  *Correction* (`Submission/Work/PARIMPL2/NOTES_FALSE_te.md`).  As first stated the domain was
  the whole **transit strip**, and the field required a *constant* `β` there.  That is not
  satisfiable: the discrepancy `D = approxU (g pt) − conj (approxU pt)` is driven by the
  derivative `1 + κ a coth (a u)` of `approxEcal`, which is `≈ −1/2` at the two ends of the strip
  (the two windows) and `→ 0` at its midpoint `u = π/(2λ_c)` (where `pt = m c`, `ζ = 0` and the
  chart centre is fixed by `g`), so no single `β` works on a domain containing both.  With the
  domain restricted to the two windows the statement is exactly the symmetric normalization the
  MATCH comparison uses, and it *follows* from the coordinate identity plus the flower's
  antiholomorphic symmetry (`φa ∘ g = conj ∘ φa + 1/2`, `Work.FatouCoord.IsAntiholomorphicFatouOn`)
  as in `Work.PARIMPL2.MatchCore`.  The field has no user in the workspace, so the repair is
  inert. -/
  te : ∃ β : ℂ, β.re = -(1 / 2) ∧ ∀ η > 0, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ρin ∧
    ∀ c ∈ P.Nm ∩ ball c₀ ρ, ∀ z : ℂ, z ∈ Win P R c → gtc c z ∈ Wout P R c →
      ‖approxU P c (gtc c z) - (starRingEnd ℂ (approxU P c z) + β)‖ ≤ η
  /-- the critical orbit lands in the incoming window at the entry time. -/
  entering : ∀ c ∈ P.Nm ∩ ball c₀ ρin, entryPt P nIn c ∈ Win P R c

namespace MatchData

variable {d : Work.EL.RootParabolic c₀} {P : ParNormal d}
  {Pa : Set ℂ} {φa : ℂ → ℂ} {Ψ : ℂ → ℂ}

/-- The transit coordinate evaluated with `nIn = M.nIn`. -/
theorem transU_eq (M : MatchData d P Pa φa Ψ) (c : ℂ) :
    transU P M.nIn c = -approxUin P c (entryPt P M.nIn c) := rfl

end MatchData

end Work.PARIMPL
