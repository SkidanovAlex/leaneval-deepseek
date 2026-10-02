/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue team
-/
import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.FQC.Flower
import Submission.Work.FatouCoord.Main
import Submission.Work.FatouCoord.Unique.fatouCoordinate_unique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue.FatouUnique` — the corrected uniqueness of the critical Écalle height

The ledger (`NOTES_LEAD_mandelbar_ledger.md` §1) records that the delivered statement
`Work.FQC.FatouUnique` — "the critical Écalle height does not depend on the choice of Écalle
data" — is **not** a consequence of the delivered `Work.FQC.EcalleData`, because that structure
did not pin the Fatou coordinate: it had no Abel equation, no `F`-invariance and no connectedness
of the petal, so a petal assembled out of disjoint fundamental pieces with a local imaginary shift
of `φa` was still a valid `EcalleData` while changing `critHeightAt`.

`Work.FQC.EcalleData` now carries the five corrected fields (`isPreconnected_Pa`,
`z₁_not_mem_Pa`, `mapsTo_Pa`, `tendsto_Pa`, `φa_shift`), all of which are *proved* for the
delivered flower by `Work.FQC.EcalleData.ofFlower` (λthe Abel equation by the identity theorem on
the `g`-invariant part of the petal, `Work.FQC.gInvariantPart`).  This file proves everything that
those fields give:

* `Work.FlowerGlue.EcalleData.φa_shift_iterate` — `φa (F^[k] z) = φa z + k` on the petal;
* `Work.FlowerGlue.EcalleData.ecalleHeight_iterate` — hence `Im φa` (the Écalle **height**) is
  invariant along the orbit: the height may be read off at *any* tap time past the entry time
  (`critHeightAt_eq_ecalleHeight`), and two Écalle data may be compared at a **common** point
  (`mem_inter_of_max`);
* `Work.FlowerGlue.exists_mem_gInvariantPart_of_tendsto` — every orbit converging to `z₁` enters
  the `g`-invariant part of the petal (the corrected structure's replacement for the false
  hypothesis `MapsTo g Pa Pa`);
* `Work.FlowerGlue.fatouCoordinate_difference_eq_const_at` — the uniqueness of the Fatou
  coordinate *at a point* `z₁ ≠ 0` (the delivered
  `Work.FatouCoord.fatouCoordinate_difference_eq_const` is stated for the germ at `0`);
* **`Work.FlowerGlue.real_of_shift_eq`** — the *antiequivariance* makes the comparison constant
  **real**, which is what makes the heights agree;
* **`Work.FlowerGlue.critHeightAt_eq_of_tendsto`** — the corrected uniqueness theorem: if the two
  coordinates have a common limit at `z₁` along the common petal, then
  `critHeightAt d E = critHeightAt d E'`;
* **`Work.FlowerGlue.FatouUnique_of_tendsto`** — the assembled `Work.FQC.FatouUnique`, from that
  single analytic input for every pair of data.

## The one remaining input, and why it is a *different* statement

The hypothesis `hlim : ∃ s, Tendsto (E.φa - E'.φa) (𝓝[E.Pa ∩ E'.Pa] z₁) (𝓝 s)` is the classical
*normalisation* of the Fatou coordinate at the parabolic point: two Abel coordinates of a simple
parabolic germ differ by a constant, and the constant is the limit of their difference at the
point (their difference is holomorphic and bounded there, since both have the same principal part
`-1/(z - z₁)` — a consequence of the Abel equation, not of the flower interface).  It is *not*
derivable from the fields of `ParabolicFlower`/`ParabolicFlowerFix`: those fields are invariant
under `φa ↦ Φ ∘ φa` for every germ `Φ(w) = w + B(w)` with `B` `1`-periodic and
`B (w̄ + 1/2) = conj (B w)` that is injective on the image of the petal, and such `Φ` need not be a
translation — see `Submission/Work/FlowerGlue/NOTES.md` §"the opacity of `φa`".  What is proved
here is everything else: the limit ⟹ constancy ⟹ realness ⟹ equality of the Écalle heights.
-/

open scoped Topology ComplexConjugate
open Filter Set Function
open Classical

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FlowerGlue

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F)
open Work.FQC (EcalleData nEnter nEnter_spec nEnter_minimal critHeightAt gInvariantPart
  gInvariantPart_subset mem_gInvariantPart FatouUnique)

noncomputable section

variable {c : ℂ} {d : RootParabolic c}

/-! ## 1. The corrected structure: the height is read off at any tap time -/

/-- The Abel equation, iterated: on the petal, `φa` advances by `k` per iterate of `F`. -/
theorem φa_shift_iterate (E : EcalleData d) {z : ℂ} (hz : z ∈ E.Pa) (k : ℕ) :
    E.φa ((F c)^[k] z) = E.φa z + (k : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',
      E.φa_shift _ (Work.FatouCoord.mapsTo_iterate_of_mapsTo E.mapsTo_Pa k hz), ih]
    push_cast
    ring

/-- **The Écalle height is invariant along the orbit**: once a point is in the petal, every later
tap of its orbit gives the same imaginary part of the Fatou coordinate. -/
theorem ecalleHeight_iterate (E : EcalleData d) {z : ℂ} (hz : z ∈ E.Pa) (k : ℕ) :
    (E.φa ((F c)^[k] z)).im = (E.φa z).im := by
  rw [φa_shift_iterate E hz k]
  simp

/-- The critical height may be read off at **any** time past the entry time of the critical orbit
into the petal. -/
theorem critHeightAt_eq_ecalleHeight (E : EcalleData d) {n : ℕ} (hn : nEnter E ≤ n) :
    critHeightAt d E = (E.φa ((F c)^[n] c)).im := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hiter : (F c)^[nEnter E + k] c = (F c)^[k] ((F c)^[nEnter E] c) := by
    rw [Nat.add_comm (nEnter E) k, Function.iterate_add_apply]
  rw [critHeightAt, hiter]
  exact (ecalleHeight_iterate E (nEnter_spec E) k).symm

/-- The `g`-invariant part of the petal is `F`-invariant. -/
theorem mapsTo_gInvariantPart (E : EcalleData d) :
    MapsTo (F c) (gInvariantPart E) (gInvariantPart E) := by
  intro z hz
  obtain ⟨hzPa, hgzPa⟩ := hz
  refine ⟨E.mapsTo_Pa hzPa, ?_⟩
  rw [Work.FQC.comp_self_commute (F := F c) (g := (Tantibar c)^[5])
    (Work.FQC.ten_eq_five_comp_five c) z]
  exact E.mapsTo_Pa hgzPa

/-- **Every orbit converging to `z₁` and avoiding it enters the `g`-invariant part of the petal.**
This is the corrected structure's replacement for the (false) hypothesis that `g` preserves the
whole petal: the orbit enters `Pa`, and applying the entry property a second time to the `g`-image
of an orbit point produces an orbit point whose `g`-image is again in `Pa`. -/
theorem exists_mem_gInvariantPart_of_tendsto (E : EcalleData d) {z : ℂ}
    (hz : Tendsto (fun n : ℕ => (F c)^[n] z) atTop (nhds d.z₁))
    (hne : ∀ n : ℕ, (F c)^[n] z ≠ d.z₁) :
    ∃ n : ℕ, (F c)^[n] z ∈ gInvariantPart E := by
  obtain ⟨n₀, hn₀⟩ := E.enters z hz hne
  set w : ℂ := (F c)^[n₀] z with hwdef
  have hwPa : w ∈ E.Pa := hn₀
  have hcomm : ∀ u : ℂ, (Tantibar c)^[5] ((F c) u) = (F c) ((Tantibar c)^[5] u) :=
    Work.FQC.comp_self_commute (F := F c) (g := (Tantibar c)^[5])
      (Work.FQC.ten_eq_five_comp_five c)
  have hlim : Tendsto (fun m : ℕ => (F c)^[m] ((Tantibar c)^[5] w)) atTop (nhds d.z₁) := by
    have h1 : Tendsto (fun m : ℕ => (Tantibar c)^[5] ((F c)^[m] w)) atTop (nhds d.z₁) := by
      have h2 := ((Work.FQC.continuous_iterate_five c).tendsto d.z₁).comp
        (E.tendsto_Pa w hwPa)
      rwa [d.per_half] at h2
    exact h1.congr' (Eventually.of_forall fun m =>
      Work.FQC.iterate_commute hcomm m w)
  have hne' : ∀ m : ℕ, (F c)^[m] ((Tantibar c)^[5] w) ≠ d.z₁ := by
    intro m hm
    have h2 : (Tantibar c)^[5] ((F c)^[m] w) = d.z₁ :=
      (Work.FQC.iterate_commute hcomm m w).trans hm
    have h3 : (F c) ((F c)^[m] w) = d.z₁ := by
      rw [Work.FQC.comp_self_apply (F := F c) (g := (Tantibar c)^[5])
        (Work.FQC.ten_eq_five_comp_five c), h2, d.per_half]
    have h4 : (F c)^[m + 1] w = d.z₁ := by
      rw [Function.iterate_succ_apply']; exact h3
    have h5 : (F c)^[m + 1 + n₀] z = d.z₁ := by
      rw [show (F c)^[m + 1 + n₀] z = (F c)^[m + 1] ((F c)^[n₀] z) from
          Function.iterate_add_apply (F c) (m + 1) n₀ z, ← hwdef]
      exact h4
    exact hne _ h5
  obtain ⟨m, hm⟩ := E.enters ((Tantibar c)^[5] w) hlim hne'
  refine ⟨n₀ + m, ?_⟩
  rw [Nat.add_comm n₀ m, Function.iterate_add_apply, ← hwdef]
  refine ⟨Work.FatouCoord.mapsTo_iterate_of_mapsTo E.mapsTo_Pa m hwPa, ?_⟩
  rw [Work.FQC.iterate_commute hcomm m w]
  exact hm

/-- The same for the critical orbit of the parameter. -/
theorem exists_critOrbit_mem_gInvariantPart (E : EcalleData d) :
    ∃ n : ℕ, (F c)^[n] c ∈ gInvariantPart E :=
  exists_mem_gInvariantPart_of_tendsto E d.crit.1 d.crit.2

/-- **The two `g`-invariant parts meet.**  Both meet the critical orbit, hence so does their
intersection. -/
theorem exists_mem_inter_gInvariantPart (E E' : EcalleData d) :
    ∃ z : ℂ, z ∈ gInvariantPart E ∩ gInvariantPart E' := by
  obtain ⟨n, hn⟩ := exists_critOrbit_mem_gInvariantPart E
  obtain ⟨m, hm⟩ := exists_critOrbit_mem_gInvariantPart E'
  refine ⟨(F c)^[max n m] c, ?_, ?_⟩
  · rw [show (F c)^[max n m] c = (F c)^[max n m - n] ((F c)^[n] c) from
        (congrArg (fun k => (F c)^[k] c) (Nat.sub_add_cancel (le_max_left n m))).symm.trans
          (Function.iterate_add_apply (F c) _ _ c)]
    exact Work.FatouCoord.mapsTo_iterate_of_mapsTo (mapsTo_gInvariantPart E) _ hn
  · rw [show (F c)^[max n m] c = (F c)^[max n m - m] ((F c)^[m] c) from
        (congrArg (fun k => (F c)^[k] c) (Nat.sub_add_cancel (le_max_right n m))).symm.trans
          (Function.iterate_add_apply (F c) _ _ c)]
    exact Work.FatouCoord.mapsTo_iterate_of_mapsTo (mapsTo_gInvariantPart E') _ hm

/-- A point of the intersection of the two petals, reached by the critical orbit: the two Écalle
data may therefore be compared at a **common** point. -/
theorem mem_inter_of_max (E E' : EcalleData d) :
    (F c)^[max (nEnter E) (nEnter E')] c ∈ E.Pa ∩ E'.Pa := by
  refine ⟨?_, ?_⟩
  · rw [show (F c)^[max (nEnter E) (nEnter E')] c
        = (F c)^[max (nEnter E) (nEnter E') - nEnter E] ((F c)^[nEnter E] c) from
      (congrArg (fun k => (F c)^[k] c)
        (Nat.sub_add_cancel (le_max_left (nEnter E) (nEnter E')))).symm.trans
        (Function.iterate_add_apply (F c) _ _ c)]
    exact Work.FatouCoord.mapsTo_iterate_of_mapsTo E.mapsTo_Pa _ (nEnter_spec E)
  · rw [show (F c)^[max (nEnter E) (nEnter E')] c
        = (F c)^[max (nEnter E) (nEnter E') - nEnter E'] ((F c)^[nEnter E'] c) from
      (congrArg (fun k => (F c)^[k] c)
        (Nat.sub_add_cancel (le_max_right (nEnter E) (nEnter E')))).symm.trans
        (Function.iterate_add_apply (F c) _ _ c)]
    exact Work.FatouCoord.mapsTo_iterate_of_mapsTo E'.mapsTo_Pa _ (nEnter_spec E')

/-! ## 2. Uniqueness of the Fatou coordinate at a point `z₁ ≠ 0` -/

/-- **Uniqueness of the Fatou coordinate (at a point, up to a constant).**  The delivered
`Work.FatouCoord.fatouCoordinate_difference_eq_const` is stated for the germ at `0`; this is the
same statement at an arbitrary point `z₁`: if two Fatou coordinates for the same map on the same
forward-invariant set, all of whose orbits converge to `z₁`, have a common limit at `z₁`, their
difference is constant. -/
theorem fatouCoordinate_difference_eq_const_at {f φ₁ φ₂ : ℂ → ℂ} {P : Set ℂ} {z₁ : ℂ}
    (h₁ : Work.FatouCoord.IsFatouCoordinateOn f φ₁ P)
    (h₂ : Work.FatouCoord.IsFatouCoordinateOn f φ₂ P) (hP : MapsTo f P P)
    (hP0 : ∀ z ∈ P, Tendsto (fun n : ℕ => f^[n] z) atTop (nhds z₁))
    (hlim : Tendsto (fun z => φ₁ z - φ₂ z) (nhdsWithin z₁ P) (nhds c)) :
    ∀ z ∈ P, φ₁ z - φ₂ z = c := by
  have h₁' : Work.FatouCoord.IsFatouCoordinateOn f (fun z => φ₁ z - c) P := h₁.sub_const c
  have hlim' : Tendsto (fun z => (fun z => φ₁ z - c) z - φ₂ z) (nhdsWithin z₁ P) (nhds 0) := by
    have h := hlim.sub_const c
    have hfun : (fun z => (fun z => φ₁ z - c) z - φ₂ z) = fun z => φ₁ z - φ₂ z - c := by
      funext z; ring
    rw [hfun]
    simpa using h
  have hzeros : ∀ u ∈ P, (fun z => φ₁ z - c) u - φ₂ u = 0 := by
    intro u hu
    have horb : ∀ n : ℕ, f^[n] u ∈ P := fun n => Work.FatouCoord.mapsTo_iterate_of_mapsTo hP n hu
    have hg : Tendsto (fun n : ℕ => f^[n] u) atTop (nhdsWithin z₁ P) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (hP0 u hu) (Eventually.of_forall horb)
    have hcomp := hlim'.comp hg
    have hconst : Tendsto (fun _ : ℕ => (fun z => φ₁ z - c) u - φ₂ u) atTop (nhds 0) :=
      hcomp.congr (fun n => by
        simp only [Function.comp_apply]
        exact h₁'.difference_invariant_iterate h₂ hP hu n)
    exact tendsto_nhds_unique tendsto_const_nhds hconst
  intro z hz
  have h := hzeros z hz
  linear_combination h

/-! ## 3. The comparison constant is real -/

/-- **The comparison constant is real.**  If the difference of the two coordinates is the constant
`s` on the intersection of the two petals, then `s = conj s`: at a point of the intersection of
the two `g`-invariant parts (such points exist, `exists_critOrbit_mem_gInvariantPart`) the
antiequivariance reads the same constant as `conj s`. -/
theorem real_of_shift_eq (E E' : EcalleData d) {z : ℂ}
    (hz : z ∈ gInvariantPart E ∩ gInvariantPart E') {s : ℂ}
    (hs : ∀ u ∈ E.Pa ∩ E'.Pa, E.φa u - E'.φa u = s) : s = star s := by
  have hz1 : z ∈ E.Pa ∩ E'.Pa := ⟨hz.1.1, hz.2.1⟩
  have hgz : (Tantibar c)^[5] z ∈ E.Pa ∩ E'.Pa := ⟨hz.1.2, hz.2.2⟩
  -- the height `s.im` computed at `z` and at `g z` (where it is its negative)
  have h1 : s.im = (E.φa z).im - (E'.φa z).im := by
    rw [← hs z hz1]
    simp
  have h' : s.im = (E'.φa z).im - (E.φa z).im := by
    have h := congrArg Complex.im ((hs ((Tantibar c)^[5] z) hgz).symm)
    rw [Complex.sub_im, E.φa_anti _ hz1.1, E'.φa_anti _ hz1.2,
      Work.FatouCoord.im_star_add_half, Work.FatouCoord.im_star_add_half] at h
    linarith [h]
  have him : s.im = 0 := by linarith
  refine Complex.ext ?_ ?_
  · simp
  · simp [him]

/-! ## 4. The corrected uniqueness theorem -/

/-- **The corrected uniqueness theorem.**  Two Écalle data of the same germ whose attracting Fatou
coordinates have a common limit `s` at `z₁` along the intersection of their petals have the same
critical Écalle height.

The proof is the classical one, now run on the corrected structure:
`fatouCoordinate_difference_eq_const_at` turns the limit into constancy on the common
`F`-invariant petal; `real_of_shift_eq` makes the constant real (the antiequivariance); and
`critHeightAt_eq_ecalleHeight` plus `mem_inter_of_max` compare the two heights at the common
`max (nEnter E) (nEnter E')`-th point of the critical orbit. -/
theorem critHeightAt_eq_of_tendsto (E E' : EcalleData d)
    (hlim : ∃ s : ℂ, Tendsto (fun z => E.φa z - E'.φa z) (nhdsWithin d.z₁ (E.Pa ∩ E'.Pa))
      (nhds s)) :
    critHeightAt d E = critHeightAt d E' := by
  obtain ⟨s, hs⟩ := hlim
  -- both coordinates are Fatou coordinates on the common petal
  have h₁ : Work.FatouCoord.IsFatouCoordinateOn (F c) E.φa (E.Pa ∩ E'.Pa) :=
    ⟨E.φa_diff.mono inter_subset_left, fun z hz => E.φa_shift z hz.1⟩
  have h₂ : Work.FatouCoord.IsFatouCoordinateOn (F c) E'.φa (E.Pa ∩ E'.Pa) :=
    ⟨E'.φa_diff.mono inter_subset_right, fun z hz => E'.φa_shift z hz.2⟩
  have hP : MapsTo (F c) (E.Pa ∩ E'.Pa) (E.Pa ∩ E'.Pa) :=
    fun z hz => ⟨E.mapsTo_Pa hz.1, E'.mapsTo_Pa hz.2⟩
  have hP0 : ∀ z ∈ E.Pa ∩ E'.Pa, Tendsto (fun n : ℕ => (F c)^[n] z) atTop (nhds d.z₁) :=
    fun z hz => E.tendsto_Pa z hz.1
  have hconst := fatouCoordinate_difference_eq_const_at h₁ h₂ hP hP0 hs
  -- the constant is real, at a point of the intersection of the `g`-invariant parts
  obtain ⟨z₀, hz₀⟩ := exists_mem_inter_gInvariantPart E E'
  have hreal : s = star s := real_of_shift_eq E E' (z := z₀) hz₀ hconst
  -- compare at the common orbit point
  have hmem : (F c)^[max (nEnter E) (nEnter E')] c ∈ E.Pa ∩ E'.Pa := mem_inter_of_max E E'
  have hkey : E.φa ((F c)^[max (nEnter E) (nEnter E')] c)
      - E'.φa ((F c)^[max (nEnter E) (nEnter E')] c) = s := hconst _ hmem
  have hE := critHeightAt_eq_ecalleHeight E (le_max_left (nEnter E) (nEnter E'))
  have hE' := critHeightAt_eq_ecalleHeight E' (le_max_right (nEnter E) (nEnter E'))
  rw [hE, hE']
  have hs0 : s.im = 0 := by
    have h := congrArg Complex.im hreal
    simp at h
    linarith
  have : (E.φa ((F c)^[max (nEnter E) (nEnter E')] c)).im
      - (E'.φa ((F c)^[max (nEnter E) (nEnter E')] c)).im = 0 := by
    have h2 : (E.φa ((F c)^[max (nEnter E) (nEnter E')] c)
        - E'.φa ((F c)^[max (nEnter E) (nEnter E')] c)).im = s.im := by rw [hkey]
    rw [Complex.sub_im] at h2
    linarith
  linarith

/-- **The `Work.FQC.FatouUnique` reduction.**  If every pair of Écalle data of every root-parabolic
parameter has a common limit of the difference of their coordinates at the parabolic point, then
the critical Écalle height is independent of the choice of Écalle data — i.e. the corrected
`FatouUnique` holds. -/
theorem FatouUnique_of_tendsto
    (H : ∀ {c : ℂ} (d : RootParabolic c) (E E' : EcalleData d),
      ∃ s : ℂ, Tendsto (fun z => E.φa z - E'.φa z) (nhdsWithin d.z₁ (E.Pa ∩ E'.Pa)) (nhds s)) :
    FatouUnique where
  eq := fun d E E' => critHeightAt_eq_of_tendsto E E' (H d E E')

/-- The same reduction from the *constancy* form: if the difference of the two coordinates is
constant on the intersection of the petals (for every pair), then `FatouUnique` holds. -/
theorem FatouUnique_of_const
    (H : ∀ {c : ℂ} (d : RootParabolic c) (E E' : EcalleData d),
      ∃ s : ℂ, ∀ z ∈ E.Pa ∩ E'.Pa, E.φa z - E'.φa z = s) :
    FatouUnique :=
  FatouUnique_of_tendsto fun d E E' => by
    obtain ⟨s, hs⟩ := H d E E'
    refine ⟨s, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hs z hz).symm

/-! ## 5. The honest pair: re-aiming the uniqueness at the transported data

The ledger's `FatouUnique` asserts the independence of the Écalle height for **every** pair of
Écalle data.  The endgame needs it for one *honest* pair only: the transported coordinate of the
MNS deformation (`Work.FQC.height_after_pg`) against the canonical coordinate of the new
parameter.  The predicate `HonestData` below isolates exactly that: it is the hypothesis of
`critHeightAt_eq_of_tendsto`, i.e. the classical normalisation (two Fatou coordinates of the same
germ have the same asymptotics at the parabolic point, so their difference has a limit).  See
`Submission/Work/FlowerGlue/NOTES_FALSE_FatouUnique.md` for why the fields of `EcalleData` do
*not* imply it for arbitrary pairs. -/

/-- The **honest-pair normalisation** at a fixed root-parabolic parameter: the coordinate of `E`
and the canonical coordinate have a common limit at `z₁` along the common petal. -/
def HonestData {c : ℂ} (d : RootParabolic c) (E : EcalleData d) : Prop :=
  ∃ s : ℂ, Tendsto (fun z => E.φa z - (EcalleData.canonical d).φa z)
    (nhdsWithin d.z₁ (E.Pa ∩ (EcalleData.canonical d).Pa)) (nhds s)

/-- **An honest pair computes the canonical critical height.** -/
theorem critHeightAt_eq_critHeight_of_honest {c : ℂ} {d : RootParabolic c} {E : EcalleData d}
    (h : HonestData d E) : critHeightAt d E = Work.FQC.critHeight d :=
  critHeightAt_eq_of_tendsto E (EcalleData.canonical d) h

/-- The corrected `FatouUnique` follows from the honest-pair normalisation for every data. -/
theorem FatouUnique_of_honest
    (H : ∀ {c : ℂ} (d : RootParabolic c) (E : EcalleData d), HonestData d E) : FatouUnique where
  eq := fun d E E' => by
    rw [critHeightAt_eq_critHeight_of_honest (H d E),
      critHeightAt_eq_critHeight_of_honest (H d E')]

end

end Work.FlowerGlue
