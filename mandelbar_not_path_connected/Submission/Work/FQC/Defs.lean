/-
# `Work.FQC` — quasiconformal deformation of the attracting Écalle cylinder

This is the vocabulary of the area `Submission/Work/FQC/` (mandelbar, `F` part 2):
the quasiconformal deformation that shifts the *critical Écalle height* of a
root-parabolic parameter by an arbitrary real number
(Hubbard–Schleicher, *Multicorns are not Path Connected*, §2; Nakane–Schleicher,
*On multicorns and unicorns II*, Theorem 3.2).

## Conventions

* `Tantibar c` is the antipolynomial `z ↦ z̄² + c` of `ChallengeDeps`;
  `Tsq c = Tantibar c ∘ Tantibar c` is its holomorphic second iterate and
  `F c = (Tsq c)^[5] = (Tantibar c)^[10]` (from `Work.EL`) is the holomorphic
  tenth iterate whose fixed point `z₁` is the simple parabolic point of a
  root-parabolic parameter.
* `fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁` is the Leau–Fatou flower
  of `F c` at `z₁`, with antiholomorphic square root `g = (Tantibar c)^[5]`
  (`Work.FatouCoord`, the export of §4 of the lead's contracts).  Its fields that
  this area uses are `Pa` (attracting petal), `φa` (antiholomorphic Fatou
  coordinate: `φa (g z) = conj (φa z) + 1/2` on `Pa`) and `enters_Pa`.
* `saw`/`ell` : the MNS piecewise-affine "twist" `ℓ_t` of the Écalle cylinder;
  `ℓ_t (x + iy) = x + i(y + t · saw x)`, so that `ℓ_t` commutes with the
  involution `ι w = conj w + 1/2` and with the shift `w ↦ w + 1`, and moves the
  point `1/4 + ih` to `1/4 + i(h + t/2)`.
* `muQC d fl t` : the invariant Beltrami coefficient obtained by pulling back the
  coefficient of `ℓ_t` from the Écalle cylinder, first along the Fatou coordinate
  (`pullHolo`), then along the dynamics (`pullAnti`), and by `0` outside the
  parabolic basin.
* `critHeight` : the critical Écalle height, `Im φa` of the first critical-orbit
  point inside the petal.

## Explicit inputs (documented, taken as hypotheses until the sibling areas land)

* `MRMTInput` — items M1, M2, M3, M2′ of `NOTES_LEAD_mrmt_foundations.md` §2, for
  the *principal* solution `Work.MRMT.Found.principal μ`.  These are proved in
  the workspace (`Work.MRMT.Found`); `MRMTInput.found` is the instance.
* `PetalReturn` — the standard structure of the immediate parabolic basin of the
  period-`5` cycle: the petal is invariant under the half-return
  `g = (Tantibar c)^[5]`, and the `T_c`-orbit of a point of the petal does not
  return to it in fewer than `5` steps (the immediate basin has one component per
  point of the cycle).  This is what makes the pulled-back coefficient invariant.
* `FatouUnique` — the uniqueness of the Fatou coordinate up to a real constant
  (the export requested in §4 of the lead's contracts), in the form used here:
  the height of the critical orbit is independent of the choice of Écalle data.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.FatouCoord.Flower
import Submission.Work.FatouCoord.Flower.exists_parabolicFlower
import Submission.Work.ParamRays.isDynBottcher_unique
import Submission.Work.ParamRays.DynBottcher
import Submission.Work.Landing.Rays
import Submission.Work.MRMT.Found.Principal
import Submission.Work.MRMT.Found.differentiableOn_comp_principal_symm
import Submission.Work.MRMT.Found.differentiableOn_principal_of_eq_zero
import Submission.Work.MRMT.Found.antiholo_conj

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

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## 1. The piecewise-affine cylinder twist `ℓ_t` -/

/-- The triangle wave with `saw 0 = saw 1/2 = 0`, `saw (1/4) = 1/2`, `saw (3/4) = -1/2`;
`1`-periodic and odd.  This is the vertical displacement of the MNS twist `ℓ_t`. -/
def saw (x : ℝ) : ℝ := 1 / 2 - 2 * |Int.fract (x + 1 / 4) - 1 / 2|

/-- The MNS twist of the Écalle cylinder: `ℓ t (x + iy) = x + i (y + t · saw x)`. -/
def ell (t : ℝ) (w : ℂ) : ℂ := w + ((t * saw w.re : ℝ) : ℂ) * Complex.I

@[simp] theorem ell_apply (t : ℝ) (w : ℂ) :
    ell t w = w + ((t * saw w.re : ℝ) : ℂ) * Complex.I := rfl

@[simp] theorem saw_apply (x : ℝ) : saw x = 1 / 2 - 2 * |Int.fract (x + 1 / 4) - 1 / 2| := rfl

/-! ## 2. Pull-backs of Beltrami coefficients -/

/-- Pull-back of a Beltrami coefficient `ν` by a holomorphic map `φ`: the coefficient of
`ν ∘ φ` is `ν (φ z) · conj (φ' z) / φ' z`. -/
def pullHolo (ν φ : ℂ → ℂ) : ℂ → ℂ := fun z => ν (φ z) * star (deriv φ z) / deriv φ z

/-- Pull-back of a Beltrami coefficient along an antiholomorphic map `f`, in the sense in which
it enters the invariance relation for `φ ∘ f ∘ φ⁻¹` (see `Work.MRMT.Found.pullRev`). -/
def pullAnti (μ f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => star (μ (f z)) * Work.MRMT.dzbar f z / star (Work.MRMT.dzbar f z)

/-- Where `f` is antiholomorphic (`dz f = 0`), `pullAnti` is exactly MRMT's `pullRev`. -/
theorem pullAnti_eq_pullRev {μ f : ℂ → ℂ} {z : ℂ} (h : Work.MRMT.dz f z = 0) :
    pullAnti μ f z = Work.MRMT.Found.pullRev μ f z := by
  rw [pullAnti, Work.MRMT.Found.pullRev, h, star_zero]
  ring_nf

/-- The `n`-fold pull-back of a coefficient along `f` (used to spread a coefficient from the
petal over the whole parabolic basin). -/
def pullAntiIter (f : ℂ → ℂ) (n : ℕ) (μ : ℂ → ℂ) : ℂ → ℂ := (fun ν => pullAnti ν f)^[n] μ

theorem pullAntiIter_zero (f : ℂ → ℂ) (μ : ℂ → ℂ) : pullAntiIter f 0 μ = μ := rfl

theorem pullAntiIter_succ (f : ℂ → ℂ) (n : ℕ) (μ : ℂ → ℂ) :
    pullAntiIter f (n + 1) μ = pullAnti (pullAntiIter f n μ) f := by
  simp [pullAntiIter, Function.iterate_succ_apply']

/-! ## 3. The iterates Tsq and F -/

theorem Tsq_eq_iterate (c : ℂ) : Work.Landing.Tsq c = (Tantibar c)^[2] := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, Function.iterate_add, Function.iterate_one]
  funext z
  rw [Function.comp_apply, Work.Landing.Tsq_apply, Work.Landing.Tantibar_apply,
    Work.Landing.Tantibar_apply]
  simp only [star_add, star_pow, star_star]

theorem F_eq_iterate (c : ℂ) : F c = (Tantibar c)^[10] := by
  rw [Work.EL.F, Tsq_eq_iterate, show (10 : ℕ) = 2 * 5 by norm_num, Function.iterate_mul]

/-! ### Continuity, differentiability and iterate combinatorics of `T_c`, `g = (T_c)^5`, `F`

`F c = (T_c)^{10}` is holomorphic (it is the fifth iterate of the holomorphic second iterate
`(T_c)^2 = Tsq c`), `g = (T_c)^5` is continuous, and `F c = g ∘ g`.  The general lemmas
`comp_self_apply`, `comp_self_commute` and `iterate_commute` are stated with *opaque* functions:
this keeps the elaborator away from the `Nat`-iterate unfolding of `F c = (T_c)^{10}`, which is
expensive. -/

/-- `T_c = z ↦ z̄² + c` is continuous. -/
theorem continuous_of_Tantibar (c : ℂ) : Continuous (Tantibar c) := by
  have h : Tantibar c = fun z : ℂ => (starRingEnd ℂ z) ^ 2 + c := rfl
  rw [h]; fun_prop

/-- The *holomorphic* second iterate `(T_c)^2` is the polynomial `z ↦ (z² + c̄)² + c`. -/
theorem iterate_two_eq_poly (c : ℂ) :
    (Tantibar c)^[2] = fun z : ℂ => (z ^ 2 + star c) ^ 2 + c := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, Function.iterate_add, Function.iterate_one]
  funext z
  simp only [Function.comp_apply, LeanEval.ComplexAnalysis.Tantibar]
  simp

/-- **`F c = (T_c)^{10} = ((T_c)^2)^5` is holomorphic.** -/
theorem differentiable_ten (c : ℂ) : Differentiable ℂ (F c) := by
  have h : F c = ((Tantibar c)^[2])^[5] := by
    rw [F_eq_iterate c, show (10 : ℕ) = 2 * 5 by norm_num, Function.iterate_mul]
  rw [h, iterate_two_eq_poly c]
  fun_prop

/-- `g = (T_c)^5` is continuous. -/
theorem continuous_iterate_five (c : ℂ) : Continuous ((Tantibar c)^[5]) :=
  (continuous_of_Tantibar c).iterate 5

/-- `F c = g ∘ g` with `g = (T_c)^5`. -/
theorem ten_eq_five_comp_five (c : ℂ) :
    F c = ((Tantibar c)^[5]) ∘ ((Tantibar c)^[5]) := by
  rw [F_eq_iterate c, show (10 : ℕ) = 5 + 5 by norm_num, Function.iterate_add]

/-- `F z = g (g z)` for `F = g ∘ g` (statement with opaque functions). -/
theorem comp_self_apply {F g : ℂ → ℂ} (h : F = g ∘ g) (z : ℂ) : F z = g (g z) := by
  rw [h]; rfl

/-- `g` commutes with `F = g ∘ g` (statement with opaque functions). -/
theorem comp_self_commute {F g : ℂ → ℂ} (h : F = g ∘ g) (z : ℂ) : g (F z) = F (g z) := by
  rw [h]; rfl

/-- If `g` commutes with `F`, then it commutes with every iterate of `F`. -/
theorem iterate_commute {F g : ℂ → ℂ} (h : ∀ z : ℂ, g (F z) = F (g z)) (n : ℕ) (z : ℂ) :
    g (F^[n] z) = F^[n] (g z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (F z), h z]

/-! ## 4. The invariant Beltrami coefficient `muQC`

The coefficient is built from a *fundamental domain* `P` for the return map: a set on which the
half-return `g = (Tantibar c)^[5]` acts, and to which the `T_c`-orbit of a point of `P` returns only
after `5` steps.  The petal `fl.Pa` of the flower is *not* such a set in general (its construction
does not give `g (Pa) ⊆ Pa`), which is why the domain is an explicit argument; the Fatou coordinate
is read off only on `P`, where it really is an antiequivariant Fatou coordinate. -/

/-- Pull-back of a Beltrami coefficient by a holomorphic map, guarded on a set `P`: the coefficient
of `ν ∘ φ` on `P`, and `0` outside. -/
def pullHoloOn (ν φ : ℂ → ℂ) (P : Set ℂ) : ℂ → ℂ :=
  fun z => if z ∈ P then ν (φ z) * star (deriv φ z) / deriv φ z else 0

/-- The parabolic basin of a fundamental domain `P`: `⋃_n (T_c)^[-n] P`. -/
def basin {c : ℂ} (d : RootParabolic c) (P : Set ℂ) : Set ℂ := {z | ∃ n : ℕ, (Tantibar c)^[n] z ∈ P}

/-- The Beltrami coefficient of the deformation, on the parabolic basin of the fundamental domain
`P`.

On `P` it is the coefficient of `ℓ_t` pulled back by the Fatou coordinate (`pullHoloOn`), and off
`P` it is obtained by pulling back along the dynamics, using the *least* `n` with
`(T_c)^[n] z ∈ P`.  Outside the basin it is `0`. -/
def muQC {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) (P : Set ℂ)
    (t : ℝ) : ℂ → ℂ :=
  fun z => if h : ∃ n : ℕ, (Tantibar c)^[n] z ∈ P then
      pullAntiIter (Tantibar c) (Nat.find h) (pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa P) z
    else 0

theorem muQC_of_mem {c : ℂ} (d : RootParabolic c)
    {fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁} {P : Set ℂ} {t : ℝ}
    {z : ℂ} (h : z ∈ basin d P) :
    muQC d fl P t z =
      pullAntiIter (Tantibar c) (Nat.find h) (pullHoloOn (Work.MRMT.beltramiOf (ell t)) fl.φa P) z := by
  simp only [muQC, basin] at *
  exact dif_pos h

theorem muQC_of_notMem {c : ℂ} (d : RootParabolic c)
    {fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁} {P : Set ℂ} {t : ℝ}
    {z : ℂ} (h : z ∉ basin d P) : muQC d fl P t z = 0 := by
  simp only [muQC, basin] at *
  exact dif_neg h

/-- The basin of a fundamental domain is backward invariant. -/
theorem basin_backward {c : ℂ} (d : RootParabolic c) {P : Set ℂ} {z : ℂ}
    (hz : Tantibar c z ∈ basin d P) : z ∈ basin d P := by
  obtain ⟨n, hn⟩ := hz
  exact ⟨n + 1, (Function.iterate_succ_apply (f := Tantibar c) n z) ▸ hn⟩

/-- The basin of a `g`-invariant fundamental domain is also forward invariant (the points already
in `P` are moved into `P` by `g = T_c^[5]`). -/
theorem basin_forward {c : ℂ} (d : RootParabolic c) {P : Set ℂ}
    (hP : ∀ z ∈ P, (Tantibar c)^[5] z ∈ P) {z : ℂ} (hz : z ∈ basin d P) :
    Tantibar c z ∈ basin d P := by
  obtain ⟨n, hn⟩ := hz
  rcases n with _ | n
  · refine ⟨4, ?_⟩
    have hT : (Tantibar c)^[4] (Tantibar c z) = (Tantibar c)^[5] z :=
      (Function.iterate_succ_apply (f := Tantibar c) 4 z)
    rw [hT]
    exact hP z hn
  · exact ⟨n, Function.iterate_succ_apply (f := Tantibar c) n z ▸ hn⟩

theorem basin_invariant {c : ℂ} (d : RootParabolic c) {P : Set ℂ}
    (hP : ∀ z ∈ P, (Tantibar c)^[5] z ∈ P) {z : ℂ} :
    Tantibar c z ∈ basin d P ↔ z ∈ basin d P :=
  ⟨fun h => basin_backward d h, fun h => basin_forward d hP h⟩

/-! ## 5. Écalle data and the critical Écalle height -/

/-- The data out of which the critical Écalle height is read off: the attracting petal and its
(antiholomorphic) Fatou coordinate.  A `ParabolicFlower` provides an instance
(`EcalleData.ofFlower`); the point of the separate structure is that after a quasiconformal
deformation the transported petal and coordinate are available directly. -/
structure EcalleData {c : ℂ} (d : RootParabolic c) where
  /-- the attracting petal -/
  Pa : Set ℂ
  /-- the attracting Fatou coordinate -/
  φa : ℂ → ℂ
  /-- the petal is open (it is a Fatou component piece) -/
  isOpen_Pa : IsOpen Pa
  /-- the Fatou coordinate is holomorphic on the petal -/
  φa_diff : DifferentiableOn ℂ φa Pa
  /-- the Fatou coordinate is injective on the petal -/
  φa_inj : Set.InjOn φa Pa
  /-- the antiholomorphic equivariance `φa ∘ g = conj ∘ φa + 1/2`, `g = (Tantibar c)^[5]` -/
  φa_anti : ∀ z ∈ Pa, φa ((Tantibar c)^[5] z) = star (φa z) + 1 / 2
  /-- every orbit converging to `z₁` without attaining it eventually enters the petal -/
  enters : ∀ z : ℂ, Tendsto (fun n : ℕ => (F c)^[n] z) atTop (nhds d.z₁) →
    (∀ n : ℕ, (F c)^[n] z ≠ d.z₁) → ∃ n : ℕ, (F c)^[n] z ∈ Pa
  /-- **CORRECTED field (1)**: the petal is preconnected. -/
  isPreconnected_Pa : IsPreconnected Pa
  /-- **CORRECTED field (2)**: the parabolic point is not in the petal. -/
  z₁_not_mem_Pa : d.z₁ ∉ Pa
  /-- **CORRECTED field (3)**: the petal is invariant under the second return map
  `F c = (Tantibar c)^[10]`. -/
  mapsTo_Pa : MapsTo (F c) Pa Pa
  /-- **CORRECTED field (4)**: the orbits of the petal converge to `z₁`. -/
  tendsto_Pa : ∀ z ∈ Pa, Tendsto (fun n : ℕ => (F c)^[n] z) atTop (nhds d.z₁)
  /-- **CORRECTED field (5)**: the Abel equation `φa (F c z) = φa z + 1` for the second return
  map, on the **whole** petal.  This is the field whose absence made `Work.FQC.FatouUnique`
  refutable (ledger §1); `EcalleData.ofFlower` *proves* it, by the identity theorem. -/
  φa_shift : ∀ z ∈ Pa, φa (F c z) = φa z + 1

/-- **The `g`-invariant part of the petal**: the points of `Pa` whose `g`-image is again in
`Pa`, `g = (Tantibar c)^[5]`.  On it the antiequivariance of `φa` squares to the Abel equation;
`Work.FQC.EcalleData.ofFlower` uses it to prove the Abel equation on the *whole* petal by the
identity theorem. -/
def gInvariantPart {c : ℂ} {d : RootParabolic c} (E : EcalleData d) : Set ℂ :=
  {z : ℂ | z ∈ E.Pa ∧ (Tantibar c)^[5] z ∈ E.Pa}

@[simp] theorem mem_gInvariantPart {c : ℂ} {d : RootParabolic c} (E : EcalleData d) {z : ℂ} :
    z ∈ gInvariantPart E ↔ z ∈ E.Pa ∧ (Tantibar c)^[5] z ∈ E.Pa := Iff.rfl

theorem gInvariantPart_subset {c : ℂ} {d : RootParabolic c} (E : EcalleData d) :
    gInvariantPart E ⊆ E.Pa := fun _ h => h.1

/-- On the `g`-invariant part of the petal, the antiequivariance squares to the Abel equation. -/
theorem EcalleData.shift_of_gInvariantPart {c : ℂ} {d : RootParabolic c} (E : EcalleData d)
    {z : ℂ} (hz : z ∈ gInvariantPart E) : E.φa (F c z) = E.φa z + 1 := by
  obtain ⟨hzPa, hgzPa⟩ := hz
  rw [comp_self_apply (F := F c) (g := (Tantibar c)^[5]) (ten_eq_five_comp_five c) z,
    E.φa_anti _ hgzPa, E.φa_anti _ hzPa, Work.FatouCoord.star_star_add_half]
  ring

/-- The `g`-invariant part of the petal is open. -/
theorem isOpen_gInvariantPart {c : ℂ} {d : RootParabolic c} (E : EcalleData d) :
    IsOpen (gInvariantPart E) :=
  E.isOpen_Pa.inter (E.isOpen_Pa.preimage (continuous_iterate_five c))

/-- **The `g`-invariant part of the petal is nonempty.**  The critical orbit enters `Pa` at the
entry time `n₀` and then stays there (the petal is `F`-invariant); the orbit of `g` of that point
converges to `z₁` without hitting it (otherwise the critical orbit would hit `z₁`), so the entry
property applied a second time produces an orbit point whose `g`-image is also in `Pa`. -/
theorem nonempty_gInvariantPart {c : ℂ} {d : RootParabolic c} (E : EcalleData d) :
    (gInvariantPart E).Nonempty := by
  obtain ⟨n₀, hn₀⟩ := E.enters c d.crit.1 d.crit.2
  set w : ℂ := (F c)^[n₀] c with hwdef
  have hwPa : w ∈ E.Pa := hn₀
  have hcomm : ∀ z : ℂ, (Tantibar c)^[5] ((F c) z) = (F c) ((Tantibar c)^[5] z) :=
    comp_self_commute (F := F c) (g := (Tantibar c)^[5]) (ten_eq_five_comp_five c)
  have hlim : Tendsto (fun n : ℕ => (F c)^[n] ((Tantibar c)^[5] w)) atTop (nhds d.z₁) := by
    have h1 : Tendsto (fun n : ℕ => (Tantibar c)^[5] ((F c)^[n] w)) atTop (nhds d.z₁) := by
      have h2 := ((continuous_iterate_five c).tendsto d.z₁).comp (E.tendsto_Pa w hwPa)
      rwa [d.per_half] at h2
    exact h1.congr' (Eventually.of_forall fun n => iterate_commute hcomm n w)
  have hne : ∀ n : ℕ, (F c)^[n] ((Tantibar c)^[5] w) ≠ d.z₁ := by
    intro n hn
    have h2 : (Tantibar c)^[5] ((F c)^[n] w) = d.z₁ := (iterate_commute hcomm n w).trans hn
    have h3 : (F c) ((F c)^[n] w) = d.z₁ := by
      rw [comp_self_apply (F := F c) (g := (Tantibar c)^[5]) (ten_eq_five_comp_five c), h2,
        d.per_half]
    have h4 : (F c)^[n + 1] w = d.z₁ := by
      rw [Function.iterate_succ_apply']; exact h3
    have h5 : (F c)^[n + 1 + n₀] c = d.z₁ := by
      rw [show (F c)^[n + 1 + n₀] c = (F c)^[n + 1] ((F c)^[n₀] c) from
        Function.iterate_add_apply (F c) (n + 1) n₀ c, ← hwdef]
      exact h4
    exact d.crit.2 _ h5
  obtain ⟨m, hm⟩ := E.enters ((Tantibar c)^[5] w) hlim hne
  refine ⟨(F c)^[m] w, ?_, ?_⟩
  · exact Work.FatouCoord.mapsTo_iterate_of_mapsTo E.mapsTo_Pa m hwPa
  · rw [iterate_commute hcomm m w]; exact hm

/-- **The Écalle data of a Leau–Fatou flower**, with all five corrected fields supplied.  The
Abel equation is *proved*: it holds on the open nonempty subset `gInvariantPart` of the
preconnected petal (there the antiequivariance squares), and the function
`z ↦ φa (F z) - φa z - 1` is holomorphic on the petal, so the identity theorem extends the
vanishing to all of `Pa`. -/
def EcalleData.ofFlower {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) : EcalleData d where
  Pa := fl.Pa
  φa := fl.φa
  isOpen_Pa := fl.isOpen_Pa
  φa_diff := fl.φa_fatou.1.2.1
  φa_inj := fl.φa_fatou.2
  φa_anti := fun z hz => fl.φa_fatou.1.2.2 z hz
  enters := fl.enters_Pa
  isPreconnected_Pa := fl.isPreconnected_Pa
  z₁_not_mem_Pa := fl.z₀_not_mem
  mapsTo_Pa := fl.mapsTo_Pa
  tendsto_Pa := fl.tendsto_Pa
  φa_shift := by
    have hgg := ten_eq_five_comp_five c
    -- the Abel equation on the `g`-invariant part of the petal
    have habel : ∀ z : ℂ, z ∈ fl.Pa → (Tantibar c)^[5] z ∈ fl.Pa →
        fl.φa (F c z) = fl.φa z + 1 := by
      intro z hzPa hgzPa
      rw [comp_self_apply (F := F c) (g := (Tantibar c)^[5]) hgg z,
        fl.φa_fatou.1.2.2 _ hgzPa, fl.φa_fatou.1.2.2 _ hzPa,
        Work.FatouCoord.star_star_add_half]
      ring
    -- an orbit point in the `g`-invariant part, from the critical orbit
    obtain ⟨n₀, hn₀⟩ := fl.enters_Pa c d.crit.1 d.crit.2
    set w : ℂ := (F c)^[n₀] c with hwdef
    have hwPa : w ∈ fl.Pa := hn₀
    have hcomm : ∀ z : ℂ, (Tantibar c)^[5] ((F c) z) = (F c) ((Tantibar c)^[5] z) :=
      comp_self_commute (F := F c) (g := (Tantibar c)^[5]) hgg
    have hlim : Tendsto (fun n : ℕ => (F c)^[n] ((Tantibar c)^[5] w)) atTop (nhds d.z₁) := by
      have h1 : Tendsto (fun n : ℕ => (Tantibar c)^[5] ((F c)^[n] w)) atTop (nhds d.z₁) := by
        have h2 := ((continuous_iterate_five c).tendsto d.z₁).comp (fl.tendsto_Pa w hwPa)
        rwa [d.per_half] at h2
      exact h1.congr' (Eventually.of_forall fun n => iterate_commute hcomm n w)
    have hne : ∀ n : ℕ, (F c)^[n] ((Tantibar c)^[5] w) ≠ d.z₁ := by
      intro n hn
      have h2 : (Tantibar c)^[5] ((F c)^[n] w) = d.z₁ := (iterate_commute hcomm n w).trans hn
      have h3 : (F c) ((F c)^[n] w) = d.z₁ := by
        rw [comp_self_apply (F := F c) (g := (Tantibar c)^[5]) hgg, h2, d.per_half]
      have h4 : (F c)^[n + 1] w = d.z₁ := by
        rw [Function.iterate_succ_apply']; exact h3
      have h5 : (F c)^[n + 1 + n₀] c = d.z₁ := by
        rw [show (F c)^[n + 1 + n₀] c = (F c)^[n + 1] ((F c)^[n₀] c) from
          Function.iterate_add_apply (F c) (n + 1) n₀ c, ← hwdef]
        exact h4
      exact d.crit.2 _ h5
    obtain ⟨m, hm⟩ := fl.enters_Pa ((Tantibar c)^[5] w) hlim hne
    have hzmem : (F c)^[m] w ∈ fl.Pa ∧ (Tantibar c)^[5] ((F c)^[m] w) ∈ fl.Pa :=
      ⟨Work.FatouCoord.mapsTo_iterate_of_mapsTo fl.mapsTo_Pa m hwPa,
        by rw [iterate_commute hcomm m w]; exact hm⟩
    -- the identity theorem
    have hdiff : DifferentiableOn ℂ (fun z : ℂ => fl.φa (F c z) - fl.φa z - 1) fl.Pa :=
      ((fl.φa_fatou.1.2.1.comp (differentiable_ten c).differentiableOn fl.mapsTo_Pa).sub
        fl.φa_fatou.1.2.1).sub_const 1
    have hana : AnalyticOnNhd ℂ (fun z : ℂ => fl.φa (F c z) - fl.φa z - 1) fl.Pa :=
      hdiff.analyticOnNhd fl.isOpen_Pa
    have hEv : (fun z : ℂ => fl.φa (F c z) - fl.φa z - 1) =ᶠ[nhds ((F c)^[m] w)] 0 :=
      Filter.eventuallyEq_of_mem
        ((fl.isOpen_Pa.inter (fl.isOpen_Pa.preimage (continuous_iterate_five c))).mem_nhds hzmem)
        (fun z hz => by
          have := habel z hz.1 hz.2
          simp only [Pi.zero_apply]
          rw [this]; ring)
    intro z hz
    have h0 := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero fl.isPreconnected_Pa
      hzmem.1 hEv hz
    simp only [Pi.zero_apply] at h0
    linear_combination h0

@[simp] theorem EcalleData.ofFlower_Pa {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    (EcalleData.ofFlower d fl).Pa = fl.Pa := rfl

@[simp] theorem EcalleData.ofFlower_φa {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) :
    (EcalleData.ofFlower d fl).φa = fl.φa := rfl

/-- The first time the critical orbit enters the petal. -/
def nEnter {c : ℂ} {d : RootParabolic c} (E : EcalleData d) : ℕ :=
  Nat.find (E.enters c d.crit.1 d.crit.2)

theorem nEnter_spec {c : ℂ} {d : RootParabolic c} (E : EcalleData d) :
    (F c)^[nEnter E] c ∈ E.Pa := Nat.find_spec (E.enters c d.crit.1 d.crit.2)

theorem nEnter_minimal {c : ℂ} {d : RootParabolic c} (E : EcalleData d) {m : ℕ}
    (hm : (F c)^[m] c ∈ E.Pa) : nEnter E ≤ m :=
  Nat.find_min' (E.enters c d.crit.1 d.crit.2) hm

/-- The **critical Écalle height**: the imaginary part of the Fatou coordinate at the first
point of the critical orbit that lies in the petal. -/
def critHeightAt {c : ℂ} (d : RootParabolic c) (E : EcalleData d) : ℝ :=
  (E.φa ((F c)^[nEnter E] c)).im

/-! ## 6. The explicit inputs

The statements below are the ones taken as hypotheses until the corresponding area delivers
them.  `MRMTInput` duplicates statements that `Work.MRMT.Found` already proves (and
`MRMTInput.found` is the resulting instance, so downstream users may work unconditionally);
`PetalReturn` and `FatouUnique` are inputs whose home areas have not produced them yet. -/

/-- Items M1, M2, M3 and M2′ of `NOTES_LEAD_mrmt_foundations.md` §2: the properties of the
*principal* solution `Work.MRMT.Found.principal μ` that the deformation consumes. -/
structure MRMTInput : Prop where
  /-- **M1**: the principal solution is normalised as `z + O(1/‖z‖)` at infinity. -/
  decay : ∀ {μ : ℂ → ℂ}, Work.MRMT.Found.Admissible μ →
    ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖Work.MRMT.Found.principal μ z - z‖ ≤ C / ‖z‖
  /-- **M3**: where the coefficient vanishes a.e., the principal solution is holomorphic. -/
  holo : ∀ {μ : ℂ → ℂ}, Work.MRMT.Found.Admissible μ → ∀ {U : Set ℂ}, IsOpen U →
    (∀ᵐ z ∂volume, z ∈ U → μ z = 0) → DifferentiableOn ℂ (Work.MRMT.Found.principal μ) U
  /-- **M2**: a map with the same coefficient is conformal in the `μ`-coordinate. -/
  conf : ∀ {μ : ℂ → ℂ}, Work.MRMT.Found.Admissible μ → ∀ {U : Set ℂ}, IsOpen U →
    ∀ {g : ℂ → ℂ}, LocallyLipschitzOn U g →
    (∀ᵐ z ∂volume, z ∈ U →
      Work.MRMT.dzbar g z = μ z * Work.MRMT.dz g z) →
    DifferentiableOn ℂ (g ∘ (Work.MRMT.Found.principal μ).symm)
      (Work.MRMT.Found.principal μ '' U)
  /-- **M2′**: if the coefficient is invariant under an antiholomorphic `f`, then the conjugate
  of `f` is antiholomorphic. -/
  anti : ∀ {μ : ℂ → ℂ}, Work.MRMT.Found.Admissible μ → ∀ {f : ℂ → ℂ},
    Differentiable ℂ (star ∘ f) →
    (∀ᵐ z ∂volume, μ z = star (μ (f z)) * Work.MRMT.dzbar f z / star (Work.MRMT.dzbar f z)) →
    Differentiable ℂ (star ∘ (Work.MRMT.Found.principal μ) ∘ f ∘
      (Work.MRMT.Found.principal μ).symm)

/-! ## 6b. The MRMT items, in the `principal μ` vocabulary

These are the four items of `MRMTInput` for the canonical principal solution
`Work.MRMT.Found.principal μ`, obtained from the corresponding statements for an arbitrary
`PrincipalData μ` (`Work.MRMT.Found.*`) by rewriting along
`Work.MRMT.Found.principal_eq_principalData`.  They are exactly what `Work.MRMT.Found.M`
records, restated here so that this area does not depend on the whole of that file. -/

/-- **M2** for `Work.MRMT.Found.principal μ`: a map with the same coefficient is conformal in the
`μ`-coordinate. -/
theorem principal_comp_symm {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ) {U : Set ℂ}
    (hU : IsOpen U) {g : ℂ → ℂ} (hg : LocallyLipschitzOn U g)
    (hrel : ∀ᵐ z ∂volume, z ∈ U → Work.MRMT.dzbar g z = μ z * Work.MRMT.dz g z) :
    DifferentiableOn ℂ (g ∘ ((Work.MRMT.Found.principal μ).symm : ℂ → ℂ))
      ((Work.MRMT.Found.principal μ : ℂ → ℂ) '' U) := by
  have h := Work.MRMT.Found.differentiableOn_comp_principal_symm hμ
    (Work.MRMT.Found.principalData μ hμ) hU hg hrel
  rwa [← Work.MRMT.Found.principal_eq_principalData hμ] at h

/-- **M3** for `Work.MRMT.Found.principal μ`: where the coefficient vanishes a.e., the principal
solution is holomorphic. -/
theorem principal_holo_of_eq_zero {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ) {U : Set ℂ}
    (hU : IsOpen U) (h0 : ∀ᵐ z ∂volume, z ∈ U → μ z = 0) :
    DifferentiableOn ℂ (Work.MRMT.Found.principal μ) U := by
  have h := Work.MRMT.Found.differentiableOn_principal_of_eq_zero hμ
    (Work.MRMT.Found.principalData μ hμ) hU h0
  rwa [← Work.MRMT.Found.principal_eq_principalData hμ] at h

/-- **M2′** for `Work.MRMT.Found.principal μ`: an invariant coefficient makes the conjugate of an
antiholomorphic map antiholomorphic. -/
theorem principal_antiholo_conj {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ (star ∘ f))
    (hinv : ∀ᵐ z ∂volume,
      μ z = star (μ (f z)) * Work.MRMT.dzbar f z / star (Work.MRMT.dzbar f z)) :
    Differentiable ℂ (star ∘ (Work.MRMT.Found.principal μ : ℂ → ℂ) ∘ f ∘
      ((Work.MRMT.Found.principal μ).symm : ℂ → ℂ)) := by
  have h := Work.MRMT.Found.antiholo_conj hμ (Work.MRMT.Found.principalData μ hμ) hf hinv
  rwa [← Work.MRMT.Found.principal_eq_principalData hμ] at h

/-- `MRMTInput` is available: M1, M2, M3 and M2′ hold for `Work.MRMT.Found.principal μ`. -/
theorem MRMTInput.found : MRMTInput where
  decay := fun {μ} hμ => Work.MRMT.Found.principal_decay hμ
  holo := fun {μ} hμ {U} hU h0 => principal_holo_of_eq_zero hμ hU h0
  conf := fun {μ} hμ {U} hU {g} hg hrel => principal_comp_symm hμ hU hg hrel
  anti := fun {μ} hμ {f} hf hinv => principal_antiholo_conj hμ hf hinv

/-- **Uniqueness of the Fatou coordinate up to a real constant**, in the form used here: the
critical Écalle height does not depend on the choice of Écalle data.  (For holomorphic Fatou
coordinates this is `Work.FatouCoord.Unique.fatouCoordinate_difference_eq_const`; the
antiholomorphic equivariance `φa ∘ g = conj ∘ φa + 1/2` forces the additive constant to be
real, so the imaginary part is canonical.) -/
structure FatouUnique : Prop where
  eq : ∀ {c : ℂ} (d : RootParabolic c) (E E' : EcalleData d), critHeightAt d E = critHeightAt d E'

end Work.FQC

end
