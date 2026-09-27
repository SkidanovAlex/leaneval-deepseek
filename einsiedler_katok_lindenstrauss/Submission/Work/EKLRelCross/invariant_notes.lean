/-
# `Work.EKLRelCross.invariant_notes` — the road to clause (U4) of `P_Leafwise`

This file contains NO declarations; it records the mathematical analysis of
`Work.EKLRelCross.leafwise_invariant` (see `Submission/Work/EKLRelCross/leafwise_invariant.lean`),
whose statement is

  `IsUInvariant μ U ↔ AeHaar μ U ν`

with `AeHaar μ U ν := ∀ᵐ x ∂μ, ∀ u ∈ U, (ν x).map (fun g => g * u) = ν x` (see
`Work.EKLRelCross.entropy_cs_interface`).  It is Pisa 6.27 / EKL (6).

## Available proved pieces

* `Work.EKLRelCross.plaque_identity_base : … → PlaqueId μ U ν`  (P1) — the `condexp` field of
  `IsLeafwise` at the *base point* of an orbit plaque:
  `ν x₀ (V ε ∩ U) * μ (A ∩ P) = μ P * ν x₀ {u ∈ V ε ∩ U | u • x₀ ∈ A}`, `P = (V ε ∩ U) • x₀`.
* `Work.EKLRelCross.plaque_ratio : PlaqueId → PlaqueRatio`  (P1′) — the same with the plaque of
  `t • x₀` in place of the plaque of `x₀`.
* `Work.EKLRelCross.plaqueDensity` — the (P1) identity in pointed "average" form:
  `(μ P).toReal⁻¹ * ∫_P f = (∫_{V ε ∩ U} f (u • x₀) ∂ν x₀) / (ν x₀ (V ε ∩ U)).toReal`.
* `Work.EKLRelCross.horoZone` — the structure of `U` forced by the contraction: every `u ∈ U` is
  block-unitriangular, `u i j = 0` when `i ≠ j` and `t0 i ≥ t0 j`, and `u i i = 1`.
* `Work.EKLRelCross.flower`/`flower_balls`/`flower_geom`/`bigShape_flowers`/`atom_flower` —
  Pisa 6.7–6.15 flowers (disjoint families of `U`-plaques over a cross-section).
* `Work.EKLC6Core.Covariant.covariant_step` — normalised one-step `aDiag`-covariance (from
  `ACovariant`).

## Direction (⟸): `AeHaar μ U ν → IsUInvariant μ U`  (Pisa 6.27)

1. `AeHaar` plus uniqueness of Haar (with `horoUnimodular`/`horoZone`: `U` is unipotent, hence
   nilpotent, hence unimodular) gives that there is ONE Radon measure `ν₀` on `SL₃(ℝ)`, carried
   by `U`, right- and left-invariant (bi-invariant Haar, `ν₀ (Box1 U) = 1`), with `ν x = ν₀` for
   every `x ∈ X'`.  In particular `ν_y (z E) = ν_y (E)` and `ν_y (g E g⁻¹) = ν_y (E)`.
2. From (P1) (in the "density" form, i.e. `plaqueDensity` with `f = 1_A`) one gets, for every
   good base point `y`, every ball `B` and every Borel `D ⊆ B • y`:
   `μ D = c y * ν₀ (B ∩ S_D)`, `c y := μ (Box1 U • y)`, `S_D := {u ∈ U | u • y ∈ D}`.
   Applying this with `B` a ball and with `u B u⁻¹` (for `u ∈ U`) and using bi-invariance of `ν₀`
   gives the **plaque-local invariance**
   `μ (u • D) = μ D` whenever `D ⊆ B • y` and `u • D ⊆ B • y`.
3. Globalization.  This is the hard step.  Two routes:
   * *Flow box.*  `U` is contained in the block unipotent group of `horoZone`; use a local slice
     `S` with `U ∩ (S S⁻¹) = {1}` and `U · S` a neighbourhood of `1` in `SL₃(ℝ)` (in the group,
     the map `(u,s) ↦ u s` is a local diffeo onto the "big cell").  In the chart
     `(u,s) ↦ u • s • x₀` the `U`-action is `(u,s) ↦ (u₁ u, s)`: it does not move the transversal
     coordinate `s`.  Disintegrating `μ` along the chart fibres (which are exactly the `U`-plaques
     `(V ε ∩ U) • (s • x₀)`, with conditional measure `ν₀` by step 2 — use `Measure.condKernel`)
     gives `μ|chart = ν₀ ⊗ ρ` in the chart coordinates; the `U`-action preserves this product, so
     `μ` is invariant under every `u ∈ U` close enough to `1`; a closed subgroup containing a
     neighbourhood of `1` is open, and `U` is connected (it is contracted onto `1` along the
     `α`-orbit and `exp` of a unipotent Lie algebra), so `μ` is `U`-invariant.
   * *Covering.*  For a fixed `u ∈ U` and every radius `r`, the sets
     `S(y) = ⋃_{n ≥ 0} α^{-n} ((V r ∩ U) • y)` satisfy `μ (u D) = μ D` for every `D ⊆ S(y)` (use
     the `α^{t0}`-invariance of `μ` and step 2 at `α^{-n} • y`) and cover a conull set; the
     multiplicities are unbounded, so this needs a genuine Besicovitch/Vitali argument on the
     plaque family (the differentiation-basis statement for the plaques).

## Direction (⟹): `IsUInvariant μ U → AeHaar μ U ν`  (EKL (6))

1. Compare (P1) at the base points `x₀` and `u • x₀` for the *same* plaque
   `P = (u B) • x₀ = B • (u • x₀)` (`u ∈ U`, `B` a ball): the two identities have the same left
   side, so with the notation `S_A = {v ∈ U | v • x₀ ∈ A}`,
   `ν (u • x₀) (u B u⁻¹) * μ (A ∩ P) = μ P * ν (u • x₀) (u S_A)`
   while (P1) at `x₀` with the ball `u B` gives `ν x₀ (u B) * μ (A ∩ P) = μ P * ν x₀ (S_A)`.
   Together with `IsUInvariant μ` (which makes `μ (u • D) = μ D`, hence `μ P` computable in the
   two ways) and bi-invariance of `ν (u • x₀)` (`horoUnimodular`), this yields, for a.e. `x₀` and
   all `u ∈ U` with `u • x₀ ∈ X'`:
   **(L)  `(ν (u • x₀)).map (fun g => u * g)` is proportional to `ν x₀`**,
   whereas the `equivariant` field of `IsLeafwise` gives
   **(R)  `(ν (u • x₀)).map (fun g => g * u)` is proportional to `ν x₀`**.
   Combining (L) and (R): `ν (u • x₀)` is proportional to its image under `g ↦ u g u⁻¹`.
2. The EKL (8) argument (Poincaré recurrence for `aDiag t0` + the `aDiag`-covariance (U7), i.e.
   `Work.EKLRelCross.Covariance μ U ν X'` — proved from the fields in
   `Work.EKLRelCross.acovariant_of_isLeafwise`), applied to the contraction of `U`, turns
   "`ν x` proportional to its translate" into "`ν x` equal to its translate"
   (`Work.EKLRelCross.leafwise_propor`, clause (U5)).
3. Alternatively (EKL (9) route): the period set argument
   (`Work.EKLRelCross.ae_translation_invariant_of_period`) gives `AeHaar` from the existence of
   one right-translation period, and (U4)-⟸ (Pisa 6.27) gives `IsUInvariant`; combining with the
   `equivariant` field closes the circle.

## The globalization step is cheap: no connectedness needed

Let `N ⊆ U` be ANY neighbourhood of `1` in `U` such that `(L_u)_*μ = μ` for `u ∈ N`.  Then
`(L_u)_*μ = μ` for **every** `u ∈ U`.  Indeed, for `u ∈ U` put `u' = aDiag t₀^n * u * (aDiag t₀^n)⁻¹`
with `n ∈ ℕ` large, so that `u' ∈ N` (contraction).  Since `α := aDiag t₀` normalises `U`,
`u = aDiag t₀^(-n) * u' * aDiag t₀^n`, and `(L_{aDiag w})_*μ = μ` for every `w` (iterate the
hypothesis `MeasurePreserving (fun x => aDiag t₀ • x) μ μ`), so

  `(L_u)_*μ = (L_{α^{-n}})_* (L_{u'})_* (L_{α^{n}})_*μ = (L_{α^{-n}})_* (L_{u'})_* μ = μ`.

Hence `localInvariant_of_AeHaar` (invariance for `u ∈ U ∩ V ε`) already gives the whole of the
(⟸) direction: no connectedness of `U`, and no `exp`, is required.  The only genuine content of
(⟸) is therefore the *local* statement, i.e. the flow-box/disintegration (or Besicovitch) step.

## Direction (⟹) — what the `(P1)` comparison gives

The comparison of (P1) at `x₀` (ball `u W`, `W = V ε ∩ U`) and at `u • x₀` (ball `W`,
`u ∈ U`) gives, with `S_A = {v ∈ U | v • x₀ ∈ A}`, for the same plaque
`(u W) • x₀ = W • (u • x₀)`:

  `ν (u • x₀) (u W u⁻¹) * μ (A ∩ P) = μ P * ν (u • x₀) (u S_A)`,
  `ν x₀ (u W) * μ (A ∩ P) = μ P * ν x₀ (S_A)`,

and `IsUInvariant μ U` gives `μ ((u W u⁻¹) • (u • x₀)) = μ (u • (W • x₀)) = μ (W • x₀)`, i.e. the
two `μ P`'s agree.  Since `S_A` ranges over all Borel subsets of `W`, this yields

  **(L)  `(ν (u • x₀)).map (fun g => u * g) ∝ ν x₀`**   (`translateLeftPropor`),

while the `equivariant` field gives `(ν (u • x₀)).map (fun g => g * u) ∝ ν x₀`.  Combining the
two: `(L_{u⁻¹} ∘ R_u)_* ν (u • x₀) ∝ ν (u • x₀)`, i.e. `ν (u • x₀)` is proportional to its
conjugate.  To reach `AeHaar` one still needs the flow-box argument (in the chart the invariance
of `μ` forces the fibre conditional measures to be left-Haar, and the leafwise identification
differs from the chart fibre coordinate by a right translation), or the EKL (8) recurrence
argument applied to a proportionality `ν x ∝ (R_u)_* ν x` — which is *not* obtained above.

## Status / gap

Steps that are *proved* in the workspace: (P1), (P1′), `horoZone`, and the pieces of the EKL (9)
route.  Steps still to be built: `horoUnimodular`, (L) above, and the globalization step 3 of the
(⟸) direction (flow box + disintegration, or Besicovitch covering).  A proof of (U4) that does
*not* use the group structure (a slice/flow box) cannot work: the conditional measures alone
determine `μ` only up to a leafwise-constant factor, which can be non-trivial for a general
foliation.
-/
