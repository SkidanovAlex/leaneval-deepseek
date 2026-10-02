import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.Thom.bijective_proj_zeroComplementA
import Submission.Work.ThomBordism.Grassmann.openThomVanishesBelowRank
import Submission.Work.ThomBordism.Grassmann.p1Rat_ne_zero_via_probe
import Submission.Work.ThomBordism.Grassmann.p1Sq_p2_linearIndependent_via_probes
import Submission.Work.ThomBordism.Grassmann.lowDegreeVanishingAndDimensionsProbeIsland

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The low-degree rational cohomology of the oriented Grassmannian

This module is the home of `Work.ThomBordism.Grassmann.lowDegreeCohomology`, the statement
`LowDegreeCohomology k m` of `Submission/Work/ThomBordism/Grassmann/Model.lean`:

for `k ≥ 10` and `m ≥ 10`, writing `G = G̃r_k(ℝ^{k+m})` for the oriented Grassmannian and
`γ` for its tautological oriented `k`-plane bundle,

* `H^j(G;ℚ) = 0` for `j ∈ {1,2,3,5,6,7}` (`lowDegrees`),
* `a ↦ a • p₁(γ)` is a bijection `ℚ → H⁴(G;ℚ)`,
* `(a,b) ↦ a • p₁(γ)² + b • p₂(γ)` is a bijection `ℚ × ℚ → H⁸(G;ℚ)`.

## The shape of the proof

**Step 1 (reduction to the dimensions).**  The three clauses are *equivalent* to the two
"dimension" statements together with the non-degeneracy of the classes:

* `H^j(G;ℚ) = 0` for `j ∈ lowDegrees` (the vanishing clause, which is what is proved),
* `finrank ℚ H⁴(G;ℚ) = 1` and `p₁(γ) ≠ 0`,
* `finrank ℚ H⁸(G;ℚ) = 2` and `p₁(γ)², p₂(γ)` linearly independent.

This is proved here (`lowDegreeCohomology_of_inputs`): it is pure linear algebra over `ℚ`.

**Step 2 (the lower bounds: `p₁ ≠ 0` and the independence of `p₁², p₂`).**  These are proved by
*pullback* along classifying maps into the two Hirzebruch generators: the tautological rank-`2`
bundle over `ℂP⁴` (giving `p₁ ↦ x²`, `p₂ ↦ 0`) and a rank-`4` bundle over `ℂP⁴` or `ℂP² × ℂP²`
(giving a second independent linear functional).  What is needed is
(a) the maps `ℂP⁴ → G̃r_k(ℝ^{k+m})` (send a complex line to the oriented real `2`-plane it spans,
then add a fixed oriented plane), (b) the identification of the pullback of `γ` with the exhibited
bundle, and (c) the naturality of the Pontryagin classes
(`Work.Thom.pontryaginClass_comap`) together with the known cohomology and Chern classes of `ℂP⁴`
(area `Projective`, area `Gen`).

**Step 3 (the upper bounds: the computation of `H^*(G;ℚ)` in degrees `≤ 8`).**  The classical
route, with the vocabulary already in the workspace:

* `H^j(G;ℚ) ≅ H^j(S γ;ℚ)` for `j ≤ k-2` (the Gysin sequence of `γ`, whose Euler class lives in
  degree `k ≥ 10`), where `S γ ⊆ γ` is the sphere bundle
  (`Work.Thom.gysin_exact_at_base`, `Work.Thom.gysin_exact_at_sphere`, and the vanishing
  `H^j(γ, γ∖0) = 0` for `j < k` — the latter has to be *re-proved* in this import island, see
  `Model.OpenThomVanishesBelowRank`);
* `S γ = {(P,v) : P ∈ G, v ∈ P, |v| = 1}` also fibres over `S^{k+m-1}` (`(P,v) ↦ v`) with fibre
  `G̃r_{k-1}(ℝ^{k+m-1})`, and since the base is `(k+m-2)`-connected,
  `H^j(S γ;ℚ) ≅ H^j(G̃r_{k-1}(ℝ^{k+m-1});ℚ)` for `j ≤ k+m-3` (Mayer–Vietoris over the two
  hemispheres of the base, with the triviality of the bundle over each hemisphere);
* iterating, all pairs `(k,m)` with `k,m ≥ 10` have the same `H^j` in degrees `≤ 8`, and the
  iteration down to `k = 9, 8, …` is controlled by the *Euler classes* of the successive bundles:
  for *odd* rank the Euler class is `2`-torsion, hence vanishes rationally
  (`2e = 0` for an odd-rank oriented bundle: the fibrewise `-1` map is an orientation-reversing
  bundle automorphism, so `e = -e`), which makes the Gysin sequence split into short exact
  sequences `0 → H^j(F_{i-1}) → H^j(F_i) → H^{j-r+1}(F_{i-1}) → 0`; for even rank the Euler class
  of the tautological-type bundle is a non-zero-divisor in the range of interest.  This is the
  classical Borel computation of `H^*(BSO;ℚ) = ℚ[p₁,p₂]` in degrees `≤ 8`, done by the Gysin
  sequences of the tower of sphere bundles only (no spectral sequences: the tower is
  `G = F_0 ⊂ F_1 ⊂ … ⊂ F_{k-1} ≅ V_k(ℝ^{k+m})`, whose top has vanishing cohomology in degrees
  `1..9`).

**Step 4 (the identification of the generators).**  The classes produced by the computation in
degrees `4` and `8` are the Pontryagin classes of the tautological bundle: this is the classical
statement that `H^*(BSO(k);ℚ) = ℚ[p₁,p₂,…]` with `p₁, p₂` *the* Pontryagin classes of the
universal bundle, and it is proved by naturality along the tower.

## Status of this file

**Proved** (all `sorry`-free, axioms `⊆ {propext, Classical.choice, Quot.sound}`):

* `lowDegreeCohomology_of_inputs` — Step 1, the assembly (pure linear algebra over `ℚ`): it reduces
  the target to the upper bounds (vanishing and dimensions) plus the two lower bounds;
* `gysinStep` — the first half of Step 3: for `j + 2 ≤ k` the rational cohomology of the
  Grassmannian in degree `j` is that of the sphere bundle of `γ`
  (`Work.Thom.bijective_proj_zeroComplementA`, the Gysin descent `π^*`);
* `p1Rat_ne_zero` — the lower bound `p₁(γ) ≠ 0`, imported from
  `Submission.Work.ThomBordism.Grassmann.p1Rat_ne_zero_via_probe` (a probe
  `ℂP² → G̃r_k(ℝ^{k+m})` with `p₁ ↦ x² ≠ 0`);
* `linearIndependent_p1Sq_p2` — the lower bound on degree `8`, imported from
  `Submission.Work.ThomBordism.Grassmann.p1Sq_p2_linearIndependent_via_probes`
  (a two-probe argument with independent `(p₁², p₂)`-functionals);
* `lowDegreeVanishingAndDimensions` — the upper bounds, imported from
  `Submission.Work.ThomBordism.Grassmann.lowDegreeVanishingAndDimensionsProbeIsland`:
  the vanishing in the degrees `lowDegrees`, `finrank ℚ H⁴ = 1` and `finrank ℚ H⁸ = 2`.
  These are the Borel computation in the stable range, carried out by the team: the Gysin descent
  `gysinStep`, the incidence step
  (`Submission.Work.ThomBordism.Grassmann.sphereBundleReduction`, proved: the sphere bundle
  fibres over `S^{k+m-1}` with fibre `G̃r_{k-1}(ℝ^{k+m-1})`), the `k`-descent reducing to `k = 10`,
  the Gysin exact sequence of `γ` with the Euler class of an odd-rank oriented bundle being
  `2`-torsion (hence rationally zero), and `degreeEightFinrankLeTwo` / `grassmannianLowDegreeVanishing`
  in the `deg8` development;

so that `lowDegreeCohomology` below is **proved** outright.

**Library hygiene note (relevant to future edits).**  The incidence/`Dim` chain and the probe chain
originally clashed on the duplicated declaration `Work.ThomBordism.Grassmann.snocE_sum_smul`
(declared both in `AddLineDefs` and in `fibreBaseHomeomorph`).  The declaration in
`fibreBaseHomeomorph` is used nowhere else, so it was renamed to `snocE_sum_smul_fibreBase` (3
occurrences, all in that file; a backup of the original is kept as `_bak_fbh.txt` in this
directory), which frees the two islands; the modules imported below are then simultaneously
importable.  The clash-free probe copies in `Probe2/` are the alternative route.

* `p1Rat_ne_zero`, `linearIndependent_p1Sq_p2` — Step 2, the "lower bound" direction: pullback of
  the classes along classifying maps `ℂP⁴ → G̃r_k(ℝ^{k+m})` (`x ↦` the oriented real `2`-plane it
  spans, then `⊕` a fixed oriented plane) and a second probe with `p₂ ≠ 0`, using the naturality
  `Work.Thom.pontryaginClass_comap` and the cohomology of `ℂP⁴` (`Projective`, `Gen`).

* `sphereBundleReduction` — the second half of Step 3, the *incidence* step:
  `S γ = {(P,v)}` fibres over `S^{k+m-1}` (`(P,v) ↦ v`) with fibre the `(k-1)`-planes in
  `v^⊥ ≅ ℝ^{k+m-1}`, i.e. `G̃r_{k-1}(ℝ^{k+m-1}) = OG (k-1) m`; because the base is
  `(k+m-2)`-connected, `H^j(S γ;ℚ) ≅ H^j(OG (k-1) m;ℚ)` for `j ≤ 8` (Mayer–Vietoris on the two
  hemispheres of the base, which is where the local triviality of this fibre bundle is used).
  This is the only missing *geometric* input of the reduction; together with `gysinStep` it gives
  `H^j(OG k m;ℚ) ≅ H^j(OG (k-1) m;ℚ)` for `j ≤ 8`, `k ≥ 10`.
-/

namespace Work.ThomBordism.Grassmann

open scoped TensorProduct

/-! ## Linear algebra over `ℚ`: the two bijectivity statements -/

/-- **A nonzero vector in a one-dimensional `ℚ`-vector space spans it.** -/
theorem span_singleton_eq_top_of_finrank_eq_one {V : Type*} [AddCommGroup V] [Module ℚ V]
    (h : Module.finrank ℚ V = 1) {v : V} (hv : v ≠ 0) : Submodule.span ℚ {v} = ⊤ :=
  (finrank_eq_one_iff_of_nonzero v hv).mp h

/-- **The multiplication map `a ↦ a • v` is bijective** as soon as `v` is a nonzero vector
spanning a one-dimensional space: injectivity from `v ≠ 0`, surjectivity from the spanning. -/
theorem bijective_smul_of_span_eq_top {V : Type*} [AddCommGroup V] [Module ℚ V] {v : V}
    (hv : v ≠ 0) (h : Submodule.span ℚ {v} = ⊤) :
    Function.Bijective (fun a : ℚ => a • v) := by
  constructor
  · intro a b hab
    have hab' : a • v = b • v := hab
    have h1 : (a - b) • v = 0 := by rw [sub_smul, hab', sub_self]
    have h2 : a - b = 0 := by
      rcases smul_eq_zero.mp h1 with h3 | h3
      · exact h3
      · exact absurd h3 hv
    exact sub_eq_zero.mp h2
  · intro w
    have hw : w ∈ Submodule.span ℚ ({v} : Set V) := by rw [h]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
    exact ⟨a, ha⟩

/-- **The two-variable map `(a,b) ↦ a • u + b • v` is bijective** when `u, v` are linearly
independent and the ambient space is two-dimensional. -/
theorem bijective_pair_of_linearIndependent_of_finrank_eq_two {V : Type*}
    [AddCommGroup V] [Module ℚ V] (h : Module.finrank ℚ V = 2)
    {u v : V} (hli : LinearIndependent ℚ ![u, v]) :
    Function.Bijective (fun p : ℚ × ℚ => p.1 • u + p.2 • v) := by
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ V := by
    rw [Fintype.card_fin]; exact h.symm
  have hspan : Submodule.span ℚ (Set.range ![u, v]) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank hli hcard
  constructor
  · rintro ⟨a, b⟩ ⟨c, d⟩ hab
    have hsum : ∑ i, (![a - c, b - d] : Fin 2 → ℚ) i • (![u, v] : Fin 2 → V) i = 0 := by
      have h0 : (a - c) • u + (b - d) • v = 0 := by
        have h1 : a • u + b • v = c • u + d • v := hab
        rw [sub_smul, sub_smul,
          show (a • u - c • u) + (b • v - d • v) = a • u + b • v - (c • u + d • v) by abel,
          h1, sub_self]
      rw [Fin.sum_univ_two]
      simpa using h0
    have h2 := Fintype.linearIndependent_iff.mp hli ![a - c, b - d] hsum 0
    have h3 := Fintype.linearIndependent_iff.mp hli ![a - c, b - d] hsum 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h2 h3
    exact Prod.ext (sub_eq_zero.mp h2) (sub_eq_zero.mp h3)
  · intro w
    have hw : w ∈ Submodule.span ℚ (Set.range ![u, v]) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hw
    refine ⟨(c 0, c 1), ?_⟩
    rw [← hc, Fin.sum_univ_two]
    simp

/-! ## The Gysin step and the vanishing below the rank

Both are available in this import island: `Work.Thom.subsingleton_OpenThom_genFibreA` (the
vanishing of the relative cohomology of the Thom pair below the rank, the statement
`OpenThomVanishesBelowRank` of `Model.lean`) and its consequence
`Work.Thom.bijective_proj_zeroComplementA` (the Gysin descent `π^* : H^j(B;ℤ) ≅ H^j(E∖0;ℤ)` for
`j + 2 ≤ rank`). -/

/-- **The Gysin step.**  For `j + 2 ≤ k` the rational cohomology of the oriented Grassmannian in
degree `j` agrees with that of the sphere bundle of its tautological bundle: the middle map
`gysinπ` of the Gysin sequence is an isomorphism below the rank of `γ` (the Euler class of `γ`
lives in degree `k`, so both neighbouring terms of the Gysin sequence vanish in these degrees). -/
theorem gysinStep (k m j : ℕ) (hj : j + 2 ≤ k) :
    Nonempty (Work.SignatureBordism.ratCohomology j (sset (OG k m)) ≃ₗ[ℤ]
      Work.SignatureBordism.ratCohomology j
        (sset (Work.Thom.zeroComplement (tautologicalBundle k m)))) := by
  refine ⟨?_⟩
  have hF : Module.finrank ℝ (Amb k) = k := by simp [Amb]
  have hbij := Work.Thom.bijective_proj_zeroComplementA (tautologicalBundle k m) hF
    (tautologicalThomClass k m) hj
  have hg : (Work.Thom.CohMap ((Work.Thom.bundleProj (tautologicalBundle k m)).comp
        (Work.Thom.subtypeMap (Work.Thom.zeroComplement (tautologicalBundle k m)))) ℤ j).hom
      = Work.Thom.gysinπ (tautologicalBundle k m) j := by
    rw [Work.Thom.CohMap_comp (Work.Thom.subtypeMap _) (Work.Thom.bundleProj _) ℤ j]
    rfl
  rw [hg] at hbij
  exact TensorProduct.congr (LinearEquiv.refl ℤ ℚ) (LinearEquiv.ofBijective _ hbij)

/-! ## The assembly: the target from the dimensions and the non-degeneracy -/

/-- **The low-degree cohomology of the oriented Grassmannian follows from the dimension count and
the non-degeneracy of the Pontryagin classes.**

This is Step 1 of the module docstring: pure linear algebra over `ℚ` (no topology).  The three
hypotheses are exactly the three remaining mathematical inputs; the second and third say that
`H⁴(G;ℚ)` is one-dimensional and `p₁(γ)` is a nonzero class, resp. that `H⁸(G;ℚ)` is
two-dimensional and `p₁(γ)², p₂(γ)` are independent. -/
theorem lowDegreeCohomology_of_inputs {k m : ℕ}
    (hvan : ∀ j ∈ lowDegrees,
      Subsingleton (Work.SignatureBordism.ratCohomology j (sset (OG k m))))
    (h4 : Module.finrank ℚ (Work.SignatureBordism.ratCohomology 4 (sset (OG k m))) = 1)
    (h8 : Module.finrank ℚ (Work.SignatureBordism.ratCohomology 8 (sset (OG k m))) = 2)
    (hp1 : p1Rat k m ≠ 0)
    (hind : LinearIndependent ℚ ![(p1SqRat k m), (p2Rat k m)]) :
    LowDegreeCohomology k m := by
  intro _ _
  refine ⟨hvan, ?_, ?_⟩
  · exact bijective_smul_of_span_eq_top hp1 (span_singleton_eq_top_of_finrank_eq_one h4 hp1)
  · exact bijective_pair_of_linearIndependent_of_finrank_eq_two h8 hind

/-! ## The remaining mathematical inputs

These three statements are the honest content of Steps 2–4 of the module docstring.  They are
stated here (rather than assumed) so that they can be proved independently and then assembled by
`lowDegreeCohomology_of_inputs`. -/

/-- **Upper bounds: the vanishing and the dimensions.**  For `k, m ≥ 10`, the rational cohomology
of `G̃r_k(ℝ^{k+m})` vanishes in the degrees `lowDegrees`, is one-dimensional in degree `4` and
two-dimensional in degree `8`. -/
theorem lowDegreeVanishingAndDimensions (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    (∀ j ∈ lowDegrees,
      Subsingleton (Work.SignatureBordism.ratCohomology j (sset (OG k m)))) ∧
    Module.finrank ℚ (Work.SignatureBordism.ratCohomology 4 (sset (OG k m))) = 1 ∧
    Module.finrank ℚ (Work.SignatureBordism.ratCohomology 8 (sset (OG k m))) = 2 :=
  lowDegreeVanishingAndDimensionsProbeIsland k m hk hm

/-- **Lower bound: `p₁(γ) ≠ 0`**, by pullback along the probe map of
`p1Rat_ne_zero_via_probe`. -/
theorem p1Rat_ne_zero (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) : p1Rat k m ≠ 0 :=
  p1Rat_ne_zero_via_probe k m hk hm

/-- **Lower bound: `p₁(γ)²` and `p₂(γ)` are linearly independent**, by the two-probe argument of
`p1Sq_p2_linearIndependent_via_probes`. -/
theorem linearIndependent_p1Sq_p2 (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    LinearIndependent ℚ ![(p1SqRat k m), (p2Rat k m)] :=
  p1Sq_p2_linearIndependent_via_probes k m hk hm

/-- The target, assembled from the three mathematical inputs above. -/
theorem lowDegreeCohomology (k m : ℕ) : Work.ThomBordism.Grassmann.LowDegreeCohomology k m := by
  intro hk hm
  exact lowDegreeCohomology_of_inputs
    (lowDegreeVanishingAndDimensions k m hk hm).1
    (lowDegreeVanishingAndDimensions k m hk hm).2.1
    (lowDegreeVanishingAndDimensions k m hk hm).2.2
    (p1Rat_ne_zero k m hk hm) (linearIndependent_p1Sq_p2 k m hk hm) hk hm

end Work.ThomBordism.Grassmann
