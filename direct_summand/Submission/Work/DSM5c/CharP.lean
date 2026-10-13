import Submission.Work.DSM5c.Basic

/-!
# DSM5c — the characteristic-`p` input `M5b` at the tilted data

This file is the second layer of the subproject `DSM5c` (node **M5c** of the mixed-characteristic
route, `DSMap.Mix2.area_M5c`).  It performs the step that the design describes as

> *"char-p input M5b on `W♭`"* (`sources/dsmap/direct_summand_mix2.md`, Task 1 (4)),

i.e. it instantiates the characteristic-`p` blowup-acyclicity input
`DSMap.Mix2.area_M5b` at the tilted datum attached to the M5c hypotheses, and it records that input
as an interface (`Work.DSM5c.M5bInterface`) so that the sibling area
`Submission/Work/DSM5b` (`DSMap.Mix2.area_M5b_proved`) can discharge it.

## Contents

* `Work.DSM5c.M5bInput` — the conclusion of `DSMap.Mix2.area_M5b` for a given perfect
  characteristic-`p` ring and a given pair `(t, T)`; this is the shape in which the input is
  consumed.
* `Work.DSM5c.M5bInterface` — the same, universally quantified over all perfect characteristic-`p`
  rings and all data (`Finite` index sets); this is the *hypothesis* form of the node.
* `Work.DSM5c.m5bInput_of_interface` / `Work.DSM5c.m5bInput_tilt` — the tilt instantiation: for the
  M5c datum `(W, QW, t, tr, j₀, e)`, if the root tower of `t j₀` is the canonical tower of `ϖ₀ ^ e`
  (which is the normalisation produced by the nodes `DEN`/`ROOTS`, see `NOTES.md` §4), then the
  interface yields the characteristic-`p` almost-acyclicity statement for the perfect ring
  `R = PreTilt W p`, the tilted generators `tiltGens t tr …` and `T = tiltVarpi QW`.
* `Work.DSM5c.not_isUnit_of_nontrivial` — the tilt `PreTilt W p` is only defined when `p` is not a
  unit in `W`; for a `PerfectoidData` the two alternatives are `p` not a unit and `W = 0`
  (`Subsingleton W`), which is the degenerate case of the M5c statement.

## State of the reduction (see `NOTES.md`)

Downstream of this file the M5c proof has to *transport* the characteristic-`p` statement back to
`W`: the perfectoid charts `D_S` are the untilts of the completed perfections of the tilted charts
(node **PB3**, the untilt functor), and the transport is `Č(D)/p ≅ Č(D♭)/ϖ♭ ^ p` (node **PB2**,
available as `DSMap.Mix.perfectoid_modp_tilt_proved`) followed by the dévissage `p ↦ p ^ m`.  Those
two steps are **not** in this file: they are the remaining content of the M5c node and are listed in
`Submission/Work/DSM5c/NOTES.md` §3–§5.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.DSM5c

universe a

open CategoryTheory
open DSMap DSMap.Mix DSMap.Mix2

/-- **The characteristic-`p` input `M5b` in interface form at given data**: for a perfect ring `R` of
characteristic `p`, a family `t : ι → R` and an element `T`, the coaugmented Čech complex of the
*perfected charts* of the blowup of `R` in the ideal `(t i)` is `T ^ (1/p^k)`-almost acyclic.

Up to the naming of `R`/`ι` this is exactly the conclusion of the frozen node `DSMap.Mix2.area_M5b`
(with the extra data `j₀`, `e` and the hypothesis `t j₀ = T ^ e` supplying the regularity that makes
the statement true). -/
def M5bInput (p : ℕ) [Fact p.Prime] {ι : Type a} [DecidableEq ι]
    (R : Type a) [CommRing R] [CharP R p] [PerfectRing R p] (t : ι → R) (T : R) : Prop :=
  AlmostAcyc (fun k => (frobeniusEquiv R p).symm^[k] T) ⊥
    ((cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)) (perfChartCoaug p t)

/-- **The node `M5b` as an interface**: the universal form of `DSMap.Mix2.area_M5b`, i.e. what the
sibling subproject `DSM5b` delivers
(`DSMap.Mix2.area_M5b_proved : M5bInterface`).

Keeping the node in this form lets the whole of `DSM5c` be proved without importing a `sorry`: the
present area takes `M5bInterface` as an explicit hypothesis wherever it needs it (see
`Work.DSM5c.m5bInput_tilt`), and the characteristic-`p` input is discharged in one line once
`Submission/Work/DSM5b/Main.lean` is available. -/
def M5bInterface : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p] [PerfectRing R p]
    {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) (T : R) (j₀ : ι) (e : ℕ),
    t j₀ = T ^ e → M5bInput p R t T

/-! ## The tilt instantiation -/

section Tilt

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
variable {ι : Type a} [Finite ι] [DecidableEq ι]

/-- The interface, applied to the perfect ring `R = PreTilt W p`: this is the *shape* in which the
M5b input enters the M5c proof (the `j₀`-generator relation `t j₀ = T ^ e` being exactly
`Work.DSM5c.tiltGens_j₀_eq_tiltVarpi_pow`). -/
theorem m5bInput_of_interface (hM5b : M5bInterface.{a}) (t : ι → PreTilt W p) (T : PreTilt W p)
    (j₀ : ι) (e : ℕ) (h : t j₀ = T ^ e) : M5bInput p (PreTilt W p) t T :=
  hM5b p (PreTilt W p) t T j₀ e h

/-- **The characteristic-`p` input at the tilted M5c datum**: under the canonical-tower hypothesis
`tr j₀ k = ϖ k ^ e` (the normalisation of `DEN`/`ROOTS`), the M5b interface gives the
almost-acyclicity of the perfected chart complex of the tilt `W♭` in the tilted generators, with
vector `(ϖ♭)^{1/p^k}`.

This is the exact form of *"char-`p` input M5b on `W♭`"* of the design. -/
theorem m5bInput_tilt (hM5b : M5bInterface.{a}) (Q : PerfectoidData p W) (t : ι → W)
    (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (hcanon : ∀ k, tr j₀ k = Q.ϖ k ^ e) :
    M5bInput p (PreTilt W p) (tiltGens t tr htr0 htr) (tiltVarpi Q) :=
  m5bInput_of_interface hM5b (tiltGens t tr htr0 htr) (tiltVarpi Q) j₀ e
    (tiltGens_j₀_eq_tiltVarpi_pow Q t tr htr0 htr j₀ e hcanon)

/-- **The characteristic-`p` input at the tilted M5c datum, with no hypothesis on the tower.**  The
tilted generator is an `e`-th power of itself for `e = 1`, so `area_M5b` applies with
`T := t♭ j₀` *for every* compatible system `tr` — no normalisation of the root tower is needed.

Note carefully what the almost-vector is: the root tower of the *tilted generator*
`t♭ j₀` (i.e. the tilt of the *given* tower `tr j₀`), **not** the root tower of `ϖ♭`.  The two
differ by the tilt of the root-of-unity ratio of the two towers, which is a *unit* of `PreTilt W p`
but is not `1` in general (`W/p` is not reduced, so a `p^k`-th root of unity need not be `1` mod
`p`).  Consequently:

* `m5bInput_tilt` (with `T := ϖ♭`, and hence the vector family `{ϖ♭ ^ (1/p^k)}_k`) is the form whose
  almost-vector matches `QW.ϖ` in the frozen statement, but it needs `t♭ j₀ = (ϖ♭)^e`, i.e. the
  canonical tower `tr j₀ k = ϖ k ^ e` (the normalisation produced by `DEN`/`ROOTS`);
* this lemma applies to every tower, and the missing step to consume it with the frozen statement's
  vector `QW.ϖ` is the *change of almost-vector*: in characteristic `p` the upgrade "killing by a
  power of a tower element implies killing by the element" (via `p`-th roots in the perfected
  complex) turns killing by the `tr j₀`-tower into killing by the `ϖ♭`-tower (their ratio being a
  unit).  That step belongs to the characteristic-`p` side (node `M5b`), see `NOTES.md` §4. -/
theorem m5bInput_tilt_general (hM5b : M5bInterface.{a}) (Q : PerfectoidData p W) (t : ι → W)
    (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) :
    M5bInput p (PreTilt W p) (tiltGens t tr htr0 htr) (tiltGens t tr htr0 htr j₀) :=
  m5bInput_of_interface hM5b (tiltGens t tr htr0 htr) (tiltGens t tr htr0 htr j₀) j₀ 1
    (pow_one _).symm

end Tilt

/-! ## The degenerate case `p` a unit -/

section Unit

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Nontrivial W]

/-- **If `p` is a unit in a `PerfectoidData` ring then the ring is trivial.**  Indeed
`DSMap.PerfectoidData` contains `IsAdicComplete (p) W`, hence `⋂ p ^ n W = 0`; if `p` is a unit then
`(p) = ⊤` and every element is divisible by all powers of `p`, so every element vanishes.

Consequently, for a nontrivial `W` the tilt `PreTilt W p` (which Mathlib only defines when
`¬ IsUnit (p : W)`, see `Mathlib.RingTheory.Perfection`) *is* available; this is the only place
where the side condition of the characteristic-`p` input is discharged on the M5c data. -/
theorem not_isUnit_of_nontrivial (Q : PerfectoidData p W) : ¬ IsUnit (p : W) := by
  intro h
  have htop : (Ideal.span {(p : W)}) = ⊤ := Ideal.span_singleton_eq_top.mpr h
  have hzero : (1 : W) = 0 := by
    refine IsHausdorff.haus (I := Ideal.span {(p : W)}) (M := W) Q.complete.toIsHausdorff 1 fun n => ?_
    rw [htop, Ideal.top_pow, Submodule.top_smul]
    exact SModEq.top
  exact one_ne_zero hzero

end Unit

end Work.DSM5c
