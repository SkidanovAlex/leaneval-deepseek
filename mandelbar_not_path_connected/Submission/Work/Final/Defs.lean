/-
# The final assembly of `mandelbar_not_path_connected`: vocabulary

Area `Submission/Work/Final/` — the **final wiring** of
`theorem mandelbar_not_path_connected : ¬ IsPathConnected Mandelbar`, following
`Submission/Work/NOTES_LEAD_mandelbar_arc_top.md` §2 (the endgame `Top` and the glue §2.3).

The endgame itself is delivered and unconditional:

* `Work.Top.not_isPathConnected_of_twoSidedPinch` (pure plane topology + the abstract parameter
  Böttcher interface `Work.Top.NakaneData`),
* `Work.TopJordan.not_isPathConnected_of_twoSidedPinch` and
  `Work.TopJordan.mandelbar_not_isPathConnected_of_twoSidedPinch` (the same, with the Jordan curve
  theorem `Work.Top.JordanForm` discharged by `Work.TopJordan.jordanForm`).

What the endgame consumes at one parabolic parameter `c₀` is exactly the triple of §2.3:

* `hθ`   — the parameter ray of the window angle `θ = 23/63` does not accumulate at `c₀`;
* `hLB`  — no path in the connectedness locus approaches `c₀` through the implosion side `Nm`;
* `hX`   — at every scale a straight segment in `Nm` near `c₀` carries escaping parameters whose
  external angles lie in the two windows around `α₁ = 371/1023` and `α₂ = 404/1023`.

This file fixes the vocabulary in which those three statements, and the data they rest on, are
phrased.  See `Submission/Work/Final/NOTES.md` for the map from the areas
(`ParamRays`, `Landing`, `FatouCoord`, `Escape`, `FSeed`, `FQC`, `FBif`, `ELRig`/`ELNest`/`ELPull`,
`Implosion`) to the fields of the holder structure `Work.Final.FinalInputs`
(`Submission/Work/Final/Main.lean`).

## Contents

* the numerical data of the root portrait: `alpha1`, `alpha2`, `windowAngle`, `windowEps`;
* `RootArc c` — the **root-arc data**: a `Work.EL.RootParabolic c` (FSeed) together with the
  Leau–Fatou flower of its characteristic parabolic point (FatouCoord), with the *derived*
  critical Écalle height `RootArc.critHeight`;
* `RootArc.EquatorLeak` — the conclusion of the equator-curve rigidity (`Work.EL.equatorLeak`);
* `ParamAngleRepelling c` — the Landing input of `hθ`;
* `BifSide c z₁` — the FBif output (the bifurcation side of the root arc);
* `ImplosionSide c z₁ Nm` — the implosion side of §2.3 (I1).

## Implementation note

`RootArc` is deliberately a `Sigma`-*type* rather than a `structure`: elaborating a structure
whose field type mentions the *function* `(Tantibar c)^[5]` or `Work.EL.F c` (as opposed to its
value at a point) makes the elaborator diverge on the smart-unfolding of the iterate.  The `Sigma`
encoding carries exactly the same data, and `RootArc.d` / `RootArc.fl` give the projections.
-/
import Submission.Work.ELRig.Defs
import Submission.Work.Landing
import Submission.Work.FSeed.Main
import Submission.Work.ParamRaysCrit.All
import Submission.Work.TopJordan.Main
import Submission.Work.FatouCoord.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Final

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The numerical data of the root portrait -/

/-- The first root angle of the non-real period-`5` component: `371/1023`
(`Work.EL.alpha1 = Work.Landing.rootAngle1`). -/
abbrev alpha1 : ℝ := Work.EL.alpha1

/-- The second root angle: `404/1023`. -/
abbrev alpha2 : ℝ := Work.EL.alpha2

/-- The window (parameter) angle of the endgame: `θ = 23/63`, of exact period `6` under
`θ ↦ -2θ mod 1`. -/
abbrev windowAngle : ℝ := Work.Landing.paramAngle

/-- The half-width of the two angle windows: `ε = 1/2048`. -/
abbrev windowEps : ℝ := Work.Landing.windowEps

/-- The **window separation** `hwin` of the endgame, in the vocabulary of this area: the two
windows around the root angles are separated by the window angle `23/63` and lie inside `(0,1)`.
This is the delivered arithmetic of `Work.Landing.Angle.window_separation`. -/
theorem window_separation :
    0 < alpha1 - windowEps ∧ alpha1 + windowEps < windowAngle ∧
      windowAngle < alpha2 - windowEps ∧ alpha2 + windowEps < 1 := by
  simpa [alpha1, alpha2, windowAngle, windowEps, Work.EL.alpha1, Work.EL.alpha2]
    using Work.Landing.Angle.window_separation

/-! ## The root-arc data -/

/-- **The root-arc data at a parameter `c`**: the structure `Work.EL.RootParabolic c` of the root
of a simple parabolic period-`5` cycle carrying the two root rays `371/1023`, `404/1023` (the
`FSeed`/`FQC`/`FBif` side), together with a Leau–Fatou **flower** of the characteristic parabolic
point `z₁` for the second return map `F c = (T_c)^{10}` and its antiholomorphic square root
`(T_c)^5` (the `FatouCoord` side).

`RootArc.ofRootParabolic` (`Submission/Work/Final/RootArc.lean`) produces the flower from the
`RootParabolic` data alone; nothing here is an extra hypothesis. -/
abbrev RootArc (c : ℂ) : Type :=
  Sigma (fun d : Work.EL.RootParabolic c =>
    Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)

namespace RootArc

variable {c : ℂ}

/-- The root-parabolic structure of a root arc (FSeed / FQC / FBif). -/
def d (A : RootArc c) : Work.EL.RootParabolic c := A.1

/-- The Leau–Fatou flower of the characteristic parabolic point. -/
def fl (A : RootArc c) : Work.FatouCoord.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) A.d.z₁ :=
  A.2

/-- The critical orbit of the second return map `F c` enters the attracting petal. -/
theorem exists_entry (A : RootArc c) : ∃ n : ℕ, (Work.EL.F c)^[n] c ∈ A.fl.Pa :=
  A.fl.enters_Pa c A.d.crit.1 A.d.crit.2

/-- The first time the critical orbit of `F c` enters the attracting petal. -/
def nEnter (A : RootArc c) : ℕ := Nat.find A.exists_entry

theorem nEnter_spec (A : RootArc c) : (Work.EL.F c)^[A.nEnter] c ∈ A.fl.Pa :=
  Nat.find_spec A.exists_entry

/-- **The critical Écalle height** of the root-arc parameter: the imaginary part of the attracting
Fatou coordinate of the transited critical value `(F c)^[nEnter] c` (the normalisation of
`NOTES_LEAD_mandelbar_EL_F_contracts.md` §7.1).

This is the quantity that `FQC` shifts to `0`, and it is *identified* by
`Work.Final.critHeight_eq_FQC` with `Work.FQC.critHeightAt d (EcalleData.ofFlower d fl)`, the
quantity used by the `FQC` area; `Work.Final.nEnter_eq_FQC` identifies the entry times.  The
height is invariant under the dynamics (hence independent of the *tap* time past the entry) once
the antiholomorphic square root is known to preserve the petal:
`RootArc.ecalleHeightAt_eq`, `RootArc.critHeight_eq_ecalleHeightAt`; see `NOTES.md` §5 for the
interface remark. -/
def critHeight (A : RootArc c) : ℝ := (A.fl.φa ((Work.EL.F c)^[A.nEnter] c)).im

/-- `critHeight = 0` is exactly the statement that the transited critical value lies on the
equator of the attracting Fatou coordinate. -/
theorem critHeight_eq_zero_iff_mem_equator (A : RootArc c) :
    A.critHeight = 0 ↔ (Work.EL.F c)^[A.nEnter] c ∈ Work.FatouCoord.equator A.fl.φa :=
  Iff.rfl

/-- **The height changes sign under the antiholomorphic square root** (Hubbard–Schleicher
Lemma 2.3, local form): on the petal, `g = (T_c)^5` sends a point of Écalle height `h` to a point
of height `-h`.  This is the ι-symmetry on which the two-sidedness of `hX` rests. -/
theorem ecalleHeight_map (A : RootArc c) {z : ℂ} (hz : z ∈ A.fl.Pa) :
    (A.fl.φa ((Tantibar c)^[5] z)).im = -(A.fl.φa z).im := by
  have h := A.fl.φa_fatou.1.ecalleHeight_map hz
  simpa only [Work.FatouCoord.ecalleHeight, Work.EL.F_eq_tantibar, Function.iterate_mul] using h

/-- **The equator is invariant under the antiholomorphic square root**: if the transited critical
value has height `0` then so does its image under `g = (T_c)^5`.  This is the ι-symmetry on which
the two-sidedness of `hX` rests: at height `0` *both* the transited value and its `g`-image lie on
the equator (the two leak directions `b` and `ι b` of
`NOTES_LEAD_mandelbar_arc_top.md` §2.3). -/
theorem critHeight_image_eq_zero (A : RootArc c) (h : A.critHeight = 0) :
    (A.fl.φa ((Tantibar c)^[5] ((Work.EL.F c)^[A.nEnter] c))).im = 0 := by
  have hv : (A.fl.φa ((Work.EL.F c)^[A.nEnter] c)).im = 0 := h
  rw [A.ecalleHeight_map A.nEnter_spec, hv, neg_zero]

/-- **The equator leak** (`EL`): the repelling equator `E = Ψ '' ℝ` of the parabolic point `z₁`
is not contained in the filled Julia set, i.e. it meets the basin of infinity.  This is the
statement proved by the equator-curve rigidity; see `Work.Final.EL.equatorLeak_of_ELRig` for the
bridge from `Work.EL.equatorLeak`. -/
def EquatorLeak (A : RootArc c) : Prop := ∃ x : ℝ, A.fl.Ψ (x : ℂ) ∉ Work.EL.K c

theorem equatorLeak_iff (A : RootArc c) :
    A.EquatorLeak ↔ ∃ x : ℝ, A.fl.Ψ (x : ℂ) ∉ Work.EL.K c := Iff.rfl

/-- The root-arc parameter is a parameter of the mandelbar. -/
theorem mem_Mandelbar (A : RootArc c) : c ∈ Mandelbar :=
  Work.FSeed.API.mem_Mandelbar A.d

/-- The characteristic parabolic point is fixed by `(T_c)^5`. -/
theorem per_half (A : RootArc c) : (Tantibar c)^[5] A.d.z₁ = A.d.z₁ := A.d.per_half

end RootArc

/-! ## The FBif output: the bifurcation side -/

/-- **The bifurcation side of the root arc** (FBif, `NOTES_LEAD_mandelbar_EL_F_contracts.md` §7.3,
row `FBif`; Hubbard–Schleicher Lemma 3.4 / MNS Thm 2.1): arbitrarily close to `c` there are
parameters at which the period-`5` orbit near `z₁` has disappeared.

This is *verbatim* the conclusion of the delivered assembly `Work.FBif.bifSide_of` of the FBif
area (from its inputs `Work.FBif.HSEstimate` and `Work.FBif.Straightening`, which consume the
MRMT items `Work.MRMT.Found.*`). -/
def BifSide (c z₁ : ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ r > 0, ∃ c' ∈ Metric.ball c r,
    ∀ z ∈ Metric.ball z₁ δ, (Tantibar c')^[5] z ≠ z

/-! ## The implosion side -/

/-- **The implosion side `Nm` of the root arc** — half of item (I1) of
`NOTES_LEAD_mandelbar_arc_top.md` §2.3: the side of the parabolic locus on which the parabolic
period-`5` cycle has disappeared (`Nm = {a_c² < 0}` in the normal form of the perturbed parabolic
germ, HS §4).  It is an open set, it accumulates at the root parameter `c`, and near `c` it
contains no point of the period-`5` orbit near `z₁`.

The remaining content of (I1) — the continuous transit of the critical value in the outgoing
Fatou coordinate, its phase blow-up `≈ π/|a_c|`, and the consequence "if the transited value
escapes then the parameter is outside `Mb`" — is the `Implosion` side of the glue, recorded in
`Work.Final.FinalInputs` as the two residuals `noPath` and `twoSided`
(`Submission/Work/Final/Main.lean`). -/
structure ImplosionSide (c z₁ : ℂ) (Nm : Set ℂ) : Prop where
  /-- the implosion side is open. -/
  isOpen_Nm : IsOpen Nm
  /-- the implosion side accumulates at the root parameter. -/
  c_mem_closure : c ∈ closure Nm
  /-- on the implosion side the period-`5` point near `z₁` has disappeared. -/
  period_five_gone : ∃ ρ : ℝ, 0 < ρ ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ c' ∈ Nm ∩ Metric.ball c ρ, ∀ z ∈ Metric.ball z₁ δ, (Tantibar c')^[5] z ≠ z

namespace ImplosionSide

variable {c z₁ : ℂ} {Nm : Set ℂ}

theorem nonempty (h : ImplosionSide c z₁ Nm) : Nm.Nonempty := by
  by_contra h0
  rw [Set.not_nonempty_iff_eq_empty] at h0
  have hc : c ∈ closure Nm := h.c_mem_closure
  rw [h0, closure_empty] at hc
  exact hc

/-- **FBif is a consequence of the implosion side.**  The implosion side accumulates at `c₀`
(`c_mem_closure`) and consists of parameters at which the period-`5` orbit near `z₁` has
disappeared (`period_five_gone`); hence the bifurcation side of FBif holds at `c₀`.  This is the
sense in which FBif is *not* an independent input of the endgame: it certifies that `Nm` is
nonempty, i.e. that the hypotheses `hX`/`hLB` at `c₀` are not vacuous. -/
theorem toBifSide (h : ImplosionSide c z₁ Nm) : BifSide c z₁ := by
  obtain ⟨ρ, hρ, δ, hδ, hgone⟩ := h.period_five_gone
  refine ⟨δ, hδ, fun r hr => ?_⟩
  set s : ℝ := min r ρ with hs
  have hspos : 0 < s := lt_min hr hρ
  have hsr : s ≤ r := min_le_left _ _
  have hsρ : s ≤ ρ := min_le_right _ _
  obtain ⟨z, hzNm, hzdist⟩ := Metric.mem_closure_iff.mp h.c_mem_closure s hspos
  have hzdist' : dist z c < s := by rwa [dist_comm] at hzdist
  have hzr : z ∈ Metric.ball c r := by rw [Metric.mem_ball]; linarith
  have hzρ : z ∈ Metric.ball c ρ := by rw [Metric.mem_ball]; linarith
  exact ⟨z, hzr, fun w hw => hgone z ⟨hzNm, hzρ⟩ w hw⟩

end ImplosionSide

namespace RootArc

variable {c : ℂ} {Nm : Set ℂ}

/-- The root parameter is *not* on the implosion side: `z₁` is a period-`5` point of `T_c`, while
on `Nm` no period-`5` point survives near `z₁`.  Hence `c ∈ closure Nm \ Nm`, the design's
`(closure Nm \ Nm) ⊆ Par`. -/
theorem notMem_Nm (A : RootArc c) (h : ImplosionSide c A.d.z₁ Nm) : c ∉ Nm := by
  intro hc
  obtain ⟨ρ, hρ, δ, hδ, hgone⟩ := h.period_five_gone
  have hcρ : c ∈ Nm ∩ Metric.ball c ρ := ⟨hc, by simpa [Metric.mem_ball] using hρ⟩
  have hz : A.d.z₁ ∈ Metric.ball A.d.z₁ δ := by simpa [Metric.mem_ball] using hδ
  exact hgone c hcρ A.d.z₁ hz A.per_half

/-- The root parameter lies on the frontier of the implosion side. -/
theorem mem_frontier_Nm (A : RootArc c) (h : ImplosionSide c A.d.z₁ Nm) : c ∈ frontier Nm := by
  rw [frontier_eq_closure_inter_closure, h.isOpen_Nm.isClosed_compl.closure_eq]
  exact ⟨h.c_mem_closure, A.notMem_Nm h⟩

end RootArc

/-! ## The Landing input of `hθ` -/

/-- **The Landing input of `hθ`** (`NOTES_LEAD_mandelbar_arc_top.md` §2.3): at the parameter `c`
the dynamical ray of the window angle `θ = 23/63` lands at a *repelling* periodic point.

`23/63` has exact period `6` under `θ ↦ -2θ`, and `6 ∤ 2·5 = 10`, so the ray cannot land at the
characteristic parabolic point of the period-`5` cycle; the classical landing theorem
(Milnor 18.10 for the even period `6`, together with the exclusion of an indifferent
non-parabolic landing point) then makes it repelling.  See
`Work.Final.ParamAngleRepelling.of_landing` for the reduction to the primitive Landing inputs, and
`Work.Final.ParamAngleRepelling_of_classical` for the composed reduction from
`Work.Landing.PeriodicRaysLand`, `Work.Landing.EvenPeriodLandingDichotomy` and the
non-parabolicity of the window-ray landing point. -/
def ParamAngleRepelling (c : ℂ) : Prop :=
  ∃ k : ℕ, ∃ y : ℂ, Work.Landing.IsRepelling c k y ∧
    Work.Landing.landsAt c Work.Landing.paramAngle y

namespace ParamAngleRepelling

/-- **The reduction of `ParamAngleRepelling` to the primitive Landing inputs**: the landing
dichotomy for the even period `6` (`Work.Landing.EvenPeriodLandingDichotomy`, Milnor 18.10 for
even periods), the landing of the ray `R_c(23/63)`, and the non-parabolicity of the landing
point. -/
theorem of_landing {c z : ℂ} (hdich : Work.Landing.EvenPeriodLandingDichotomy c)
    (hland : Work.Landing.landsAt c Work.Landing.paramAngle z)
    (hpar : ∀ m : ℕ, ¬ Work.Landing.IsParabolic c m z) : ParamAngleRepelling c := by
  obtain ⟨k, hfix, hlt⟩ := Work.Landing.landsAt_paramAngle_repelling hdich hpar hland
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [Work.Landing.multiplier2, Function.iterate_zero] at hlt
      simp [deriv_id] at hlt
    · exact hkpos
  exact ⟨k, z, ⟨⟨hk, hfix⟩, hlt⟩, hland⟩

end ParamAngleRepelling

end Work.Final
