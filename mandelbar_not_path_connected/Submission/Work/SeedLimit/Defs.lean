/-
Copyright: subproject `Submission/Work/SeedLimit/` of `mandelbar_not_path_connected`.

# `Work.SeedLimit` — the limit-point formulation of the seed

This area builds the **parallel fallback route** for the seed of the mandelbar
theorem: the parameter-ray *limit point* formulation of Hubbard--Schleicher's
seed, whose design is `Submission/Work/NOTES_LEAD_mandelbar_noncusp.md` §1(a),(c)
and the appendix §5 (together with `NOTES_LEAD_mandelbar_seed.md` §3--§5).

It has two halves.

* **§5.1 — non-cusp at every parameter-ray limit point.**  A parameter at which
  the ray `R(θ)` accumulates, and at which the holomorphic `5`-th return map
  `(T_c²)^[5] = T_c^[10]` has a *degenerate* parabolic point (multiplier `1`,
  second derivative `0`), does not exist: such a parameter is an interior point
  of the mandelbar.  The main export is
  `Work.SeedLimit.simple_of_mem_closure_paramRay`.
* **§5.2 — co-landing at a limit point.**  The definition
  `Work.SeedLimit.CharacteristicLanding` (MNS Lemma 4.5 for `θ = α₁`) and the
  combinatorial reduction showing that it forces `α₁` and `α₂` to co-land, at a
  parabolic point of exact `T`-period `5`, at every limit point of `R(α₁)`.

## Main definitions

* `Work.SeedLimit.IsParabolicReturnPoint`, `IsDegenerateParabolic`,
  `IsSimpleParabolicPoint` — parabolicity of a periodic point of the tricorn, in
  the only form in which an *odd*-period point of an antiholomorphic polynomial
  can be parabolic: a fixed point of the holomorphic return map `(T_c²)^[k]` of
  multiplier one (the first return map `T_c^[k]` has conjugate-linear derivative,
  so its second iterate `(T_c^[k])² = T_c^[2k] = (T_c²)^[k]` is the holomorphic
  object whose multiplier is a non-negative real number).
* `Work.SeedLimit.CuspSet`, `StrictCuspSet` — the degenerate (multiplicity ≥ 2)
  and the strict (multiplicity exactly 2 = "two petals") parabolic parameters of
  odd period `5`.
* `Work.SeedLimit.CharacteristicLanding` — MNS Lemma 4.5 at `θ = α₁`.
* `Work.SeedLimit.CoLandsAtLimit` — the co-landing statement that the seed needs.

## The classical inputs (named `Prop`s, never `axiom`s)

* `Work.SeedLimit.CuspsInInterior` — MNS, *Multicorns are not path connected II*,
  Lemma 2.9 + Lemma "Cusps in Interior": every parabolic cusp lies in the
  interior of the multicorn.
* `Work.SeedLimit.PetalCountBound` (in `NonCusp.lean`) — MNS, Lemma
  "Odd Indifferent Dynamics" (`LemOddIndiffDyn`), local form: a degenerate
  parabolic point of `(T_c²)^[5]` outside the interior of the mandelbar has at
  most two petals, i.e. its multiplicity is exactly two.
* `Work.SeedLimit.PeriodTenPortraitExists`, `CharacteristicLandingCombinatorial`
  (and their set-theoretic forms `PortraitExistsSet`,
  `CharacteristicLandingCombinatorialSet`) — the combinatorial/dynamical inputs of
  §5.2.

## Main results

* `Work.SeedLimit.simple_of_mem_closure_paramRay` — §5.1 (from `CuspsInInterior`).
* `Work.SeedLimit.cuspSet_subset_interior_of_strict` — the two-input refinement
  (from the strict cusp set and the petal count).
* `Work.SeedLimit.charArcNotAtZero`, `Work.SeedLimit.noTriplePortrait`,
  `Work.SeedLimit.pairPortraitCandidates'` — the finite certificate of §5.2.
* `Work.SeedLimit.coLandsAtLimit_of_characteristicLanding` — §5.2.

## Modules

* `Defs` — this file: the notions and the two statements;
* `NonCusp` — §5.1, `simple_of_mem_closure_paramRay` and its two refined forms;
* `LocalRoute` — §5.1, the local route's two halves (`PetalCountBound`, `IndexParityArgument`);
* `Portrait`, `Certificate`, `Angles` — §5.2, the finite period-`10` certificate and the angle
  dictionary between `Fin 1023` and the real angles `j/1023`;
* `LimitLanding` — §5.2, the co-landing deduction and its named inputs;
* `Contract` — the two conclusions in one theorem;
* `NonCuspNS` — compatibility aliases in `namespace Work.NonCusp`;
* `All`, `Checks` — aggregator and axiom audit.

Import one module: `Submission.Work.SeedLimit.All`.
-/
import Submission.Work.ParamRays.MbDefs
import Submission.Work.Landing.Core
import Submission.Work.Landing.Rays
import Submission.Work.FSeed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedLimit

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The objects of the tricorn family -/

/-- The holomorphic second iterate `(T_c)²(z) = (z² + c̄)² + c` of the tricorn iterator. -/
abbrev Tsq (c : ℂ) : ℂ → ℂ := Work.Landing.Tsq c

/-- The holomorphic `10`-th iterate `T_c^[10] = (T_c²)^[5]`: the holomorphic return map whose
fixed points are the points of `T_c`-period dividing `5` (an *odd* period, which is why this
holomorphic map, and not `T_c^[5]`, carries the multiplier). -/
abbrev F (c : ℂ) : ℂ → ℂ := Work.FSeed.F c

/-- The period `5` of the α-root arc of the tricorn, as used everywhere in the workspace. -/
abbrev k : ℕ := 5

noncomputable section

/-- The angle `α₁ = 371/1023` of the root arc, as in the rest of the workspace. -/
abbrev α₁ : ℝ := Work.FSeed.α₁

/-- The angle `α₂ = 404/1023` of the root arc. -/
abbrev α₂ : ℝ := Work.FSeed.α₂

end

/-! ## Parabolic periodic points of the tricorn -/

/-- `z` is a **parabolic periodic point** of `T_c` of period dividing `n`, in the normal form for
odd periods: `z` is a fixed point of the holomorphic map `(T_c²)^[k]` with multiplier one.

For an odd `k`, a point of `T_c`-period dividing `k` is a fixed point of `T_c^[k]`, whose
derivative is conjugate-linear; the holomorphic second iterate `(T_c^[k])² = T_c^[2k] =
(T_c²)^[k]` has a *real* multiplier there, so indiffrence (`|μ| = 1`) is the equation
`μ = 1`, and the correct notion of the *multiplicity* of the parabolic point is that of the
fixed point of the holomorphic map `(T_c²)^[k]` (compare MNS, *Multicorns are not path
connected II*, proof of Lemma "Odd Indifferent Dynamics"). -/
def IsParabolicReturnPoint (c : ℂ) (n : ℕ) (z : ℂ) : Prop :=
  (Tsq c)^[n] z = z ∧ deriv ((Tsq c)^[n]) z = 1

/-- A **degenerate** parabolic periodic point: parabolic and of multiplicity at least two, i.e.
the second derivative of the holomorphic return map vanishes. -/
def IsDegenerateParabolic (c : ℂ) (n : ℕ) (z : ℂ) : Prop :=
  IsParabolicReturnPoint c n z ∧ iteratedDeriv 2 ((Tsq c)^[n]) z = 0

/-- A **simple** (non-degenerate) parabolic periodic point: parabolic with non-vanishing second
derivative, i.e. a parabolic point of multiplicity exactly one, with a single petal. -/
def IsSimpleParabolicPoint (c : ℂ) (n : ℕ) (z : ℂ) : Prop :=
  IsParabolicReturnPoint c n z ∧ iteratedDeriv 2 ((Tsq c)^[n]) z ≠ 0

/-- A **cusp of the odd-period return map** of the tricorn: a point `z` of `T_c`-period *dividing*
`5` (necessarily a point of odd `T_c`-period, so that the multiplier of the holomorphic return map
`(T_c²)^[5]` at `z` is a non-negative real number) which is a degenerate parabolic point of that
holomorphic return map: multiplier `1` and multiplicity at least two.

This is MNS's notion of a parabolic *cusp* of odd period `k | 5` (their Definition "Parabolic
Cusps"), stated in the degenerate form; the strict form (multiplicity exactly two, two petals) is
`IsStrictCusp`. -/
def IsCusp (c z : ℂ) : Prop := (Tantibar c)^[5] z = z ∧ IsDegenerateParabolic c k z

/-- A **strict cusp**: a cusp whose parabola has multiplicity exactly two, i.e. exactly two petals
(`q = 2`).  Such a cusp is the merger of three periodic orbits (MNS §4). -/
def IsStrictCusp (c z : ℂ) : Prop :=
  IsCusp c z ∧ iteratedDeriv 3 ((Tsq c)^[k]) z ≠ 0

/-- The period-`5` **cusp set** of the tricorn: the parameters carrying a cusp of the odd-period
return map — i.e. a point of `T_c`-period dividing `5` at which the holomorphic return map
`(T_c²)^[5]` has a degenerate parabolic point (multiplier `1`, second derivative `0`).  These are
the "cusps" of the α-root arc in the terminology of MNS. -/
def CuspSet : Set ℂ := {c : ℂ | ∃ z : ℂ, IsCusp c z}

/-- The **strict** cusp set: parameters with a cusp of multiplicity *exactly* two (two petals),
i.e. the `q = 2` cusps of MNS's Definition "Parabolic Cusps". -/
def StrictCuspSet : Set ℂ := {c : ℂ | ∃ z : ℂ, IsStrictCusp c z}

/-- The critical orbit of `T_c` is infinite: no two of its points coincide.  This is the
hypothesis under which MNS's petal count (each petal cycle absorbs an infinite critical orbit)
gives the bound `q ≤ 2` on the number of petals. -/
def InfiniteCritOrbit (c : ℂ) : Prop :=
  ∀ m n : ℕ, m ≠ n → (Tantibar c)^[m] 0 ≠ (Tantibar c)^[n] 0

/-! ## The classical inputs of §5.1 -/

/-- **MNS, "Cusps in the interior"** (arXiv:1404.5031, Lemma "Finitely Many Cusp Points" +
Lemma "Cusps in Interior", PropCuspsInterior): every parabolic cusp of the multicorn is an interior
point of the multicorn.

For the tricorn (`d = 2`) and odd period `k | 5`, a cusp is a parameter at which the holomorphic
return map `(T_c²)^[5]` has a parabolic fixed point of an odd-period cycle.  MNS state the theorem
for cusps in the strict sense (multiplicity exactly two, two petals, `q = 2`);
`CuspsInInterior` below is the *degenerate* form (multiplicity at least two), which is the form in
which §5.1 uses it.  The passage from the strict to the degenerate form is
`Work.SeedLimit.cuspSet_subset_interior_of_strict`, which uses the petal-count bound
`PetalCountBound` of MNS's Lemma "Odd Indifferent Dynamics".

Note the odd-period restriction in the definition of `CuspSet`: `z` is required to be a point of
`T_c`-period dividing `5`, not merely a fixed point of the holomorphic map `T_c^[10]`.  Without it
the set would also contain degenerate parabolic points of *even* `T_c`-period, for which the
multiplier of the return map need not be real, and the cusp theorem is not the literature
statement. -/
def CuspsInInterior : Prop := CuspSet ⊆ interior Mandelbar

/-- The refinement of `CuspsInInterior` from the strict cusp set: cusps of multiplicity exactly
two (`q = 2`) are interior — this is MNS's PropCuspsInterior verbatim — and by `PetalCountBound` no
infinite-critical-orbit parameter carries a cusp of multiplicity `≥ 3`. -/
def CuspsInInteriorStrict : Prop := StrictCuspSet ⊆ interior Mandelbar

/-! ## §5.2: characteristic landing and co-landing -/

/-- The **characteristic Fatou component** of `T_c`: the component of the interior of the filled
Julia set containing the critical value `c = T_c 0`. -/
def characteristicComponent (c : ℂ) : Set ℂ :=
  connectedComponentIn (interior (Work.ParamRays.filledJulia c)) c

/-- **MNS Lemma 4.5** (arXiv:1404.5031, "Let θ be n-periodic ..., R_θ a parameter ray of
M_d*, and c ∈ L(θ).  Then f_c has a parabolic cycle of period k dividing n such that the
corresponding dynamical ray R_θ^c lands at the characteristic parabolic point of f_c"),
specialised to the angle `α₁` of the root arc:

every limit point of the parameter ray `R(α₁)` at which the dynamical ray at angle `α₁` lands
does so at a point of the frontier of the characteristic Fatou component.  (For a parabolic
point of an odd-period cycle, the characteristic parabolic point *is* the point on the frontier
of the characteristic component at which the root points of the cycle co-land.) -/
def CharacteristicLanding : Prop :=
  ∀ c ∈ closure (Work.ParamRays.paramRay α₁), c ∉ Work.ParamRays.paramRay α₁ → ∀ w : ℂ,
    Work.Landing.landsAt c α₁ w → w ∈ frontier (characteristicComponent c)

/-- **The co-landing statement of the seed**: at every limit point of `R(α₁)`, the two root-arc
rays `α₁` and `α₂` co-land at a point fixed by `T_c^[5]` (equivalently: at a parabolic point of
the odd-period return map `(T_c²)^[5]`).

The *exactness* of the period is deliberately not part of this statement: it is derived downstream
in the seed (`Work.FSeed.RootParabolicInput.odd_per`), from the simplicity of the parabolic point
and the portrait count, and not from the limit-point clause. -/
def CoLandsAtLimit : Prop :=
  ∀ c ∈ closure (Work.ParamRays.paramRay α₁), c ∉ Work.ParamRays.paramRay α₁ →
    ∃ w : ℂ, Work.Landing.landsAt c α₁ w ∧ Work.Landing.landsAt c α₂ w ∧
      (Tantibar c)^[5] w = w

/-- The co-landing statement with the exact period: the common landing point has exact
`T_c`-period `5`, i.e. it is not a fixed point of `T_c`. -/
def CoLandsAtLimitExactFive : Prop :=
  ∀ c ∈ closure (Work.ParamRays.paramRay α₁), c ∉ Work.ParamRays.paramRay α₁ →
    ∃ w : ℂ, Work.Landing.landsAt c α₁ w ∧ Work.Landing.landsAt c α₂ w ∧
      (Tantibar c)^[5] w = w ∧ ∀ j : ℕ, 0 < j → j < 5 → (Tantibar c)^[j] w ≠ w

/-! ## Elementary facts -/

/-- `(T_c²)^[5] = T_c^[10]`, as functions. -/
theorem Tsq_iterate_five_eq (c : ℂ) : (Tsq c)^[5] = (Tantibar c)^[10] := by
  have h2 : (Tantibar c)^[2] = Tsq c := by
    funext z
    simpa [Tsq, Work.Landing.Tsq, Function.iterate_succ, Function.iterate_one,
      Function.comp_apply] using Work.ParamRays.orbit_two_eq c z
  have h := Function.iterate_mul (Tantibar c) 2 5
  rw [show (10 : ℕ) = 2 * 5 from rfl, h, h2]

/-- `(T_c²)^[5]` is the holomorphic `T_c^[10]`. -/
theorem Tsq_iterate_five_apply (c z : ℂ) : (Tsq c)^[5] z = (Tantibar c)^[10] z := by
  rw [Tsq_iterate_five_eq]

/-- A point of `T_c`-period dividing `5` is a fixed point of the holomorphic return map
`(T_c²)^[5]`. -/
theorem Tsq_iterate_five_fixed {c z : ℂ} (h : (Tantibar c)^[5] z = z) :
    (Tsq c)^[5] z = z := by
  have h2 : (Tsq c)^[5] z = (Tantibar c)^[5] ((Tantibar c)^[5] z) := by
    rw [Tsq_iterate_five_apply]
    exact Function.iterate_add_apply (f := Tantibar c) 5 5 z
  rw [h2, h, h]

/-- A point of `T_c`-period dividing `5` is a fixed point of `(T_c²)^[5]`, in the form in which
the seed uses it (`T_c^[10] = T_c^[5]` on the cycle). -/
theorem T_ten_of_T_five_fixed {c z : ℂ} (h : (Tantibar c)^[5] z = z) :
    (Tantibar c)^[10] z = z := by
  have h2 : (Tantibar c)^[10] z = (Tantibar c)^[5] ((Tantibar c)^[5] z) :=
    Function.iterate_add_apply (f := Tantibar c) 5 5 z
  rw [h2, h, h]

/-- The parameter rays lie outside the mandelbar. -/
theorem mem_paramRay_not_mem_Mb {θ : ℝ} {c : ℂ} (hc : c ∈ Work.ParamRays.paramRay θ) :
    c ∉ Mandelbar := hc.1

/-- The closure of a parameter ray is contained in the closure of the complement of the
mandelbar.  (Note that `Mandelbarᶜ` is *open*, so this does not say that a limit point of a ray
lies outside the mandelbar: limit points of the parameter rays `R(θ)` may well be mandelbar
parameters, and are exactly the parabolic parameters the seed is about.) -/
theorem closure_paramRay_subset_closure_compl (θ : ℝ) :
    closure (Work.ParamRays.paramRay θ) ⊆ closure ((Mandelbar : Set ℂ)ᶜ) :=
  closure_mono fun _ hx => hx.1

/-- An interior point of the mandelbar is not in the closure of any parameter ray: a ball inside
the mandelbar contains no point of a parameter ray, since parameter rays lie outside the
mandelbar.  This is the (elementary) reason why the §5.1 statement "every cusp is an interior
point" contradicts the hypothesis that `c` is a limit point of `R(θ)`. -/
theorem not_mem_closure_paramRay_of_mem_interior {θ : ℝ} {c : ℂ}
    (h : c ∈ interior Mandelbar) : c ∉ closure (Work.ParamRays.paramRay θ) := by
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp isOpen_interior c h
  intro hc
  obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.mp hc r hr
  exact hy.1 (interior_subset (hrsub (Metric.mem_ball.mpr (by rwa [dist_comm] at hyd))))

end Work.SeedLimit
