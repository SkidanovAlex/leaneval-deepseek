import Mathlib
import Submission.UnifMain
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_regular_aux
import Submission.Work.EQ.good_directions
import Submission.Work.EQ.H0_hyperbolic
import Submission.Work.EQ.H0_fatou
import Submission.Work.EQ.H0_no_convergence
import Submission.Work.Covering.exists_tendsto_of_isCoveringMap_comp
import Submission.Work.EQ.cayley_homeomorph_uhp


import Submission.Work.EQ.cluster_values_countable_ns
import Submission.Work.EQ.countable_puncture_values_ns
import Submission.Work.EQ.H0_path_limit_Iio
import Submission.Work.EQ.H0_shiftCluster
import Submission.Work.EQ.good_directions_uncountable
import Submission.Work.EQ.fatou_riesz_ns
import Submission.Work.EQ.H0_disc_cover_holomorphic
import Submission.Work.EQ.H0_secondCountable
import Submission.Work.EQ.H0_step5_aux
import Submission.Work.EQ.H0_component_uniformization
import Submission.Work.EQ.exists_uniformizing_cover
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.H0_invParam_ge

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN.md, DESIGN_CORE.md and PAPER_PROOFS.md (the lead's full paper proofs for the sketched Rychlik steps; follow them). Defs: Submission/Work/EQ/Defs.lean + DefsCore.lean (namespace Work.EQ; do NOT edit; IsPuncturedChart now carries a scale κ). Proved UNIFORMIZATION library in this workspace (Submission.UnifMain etc.). With UnifMain imported write `open _root_.Topology`.

# H0_regular: every component is regular (Rychlik Thms 10–11) (7–11k; READY as stated)

**Proof.** `PAPER_PROOFS.md` §6. Assume `ψ` is nonconstant on a component `S`.
1. Setup:
   * `S` is an étale Riemann surface via `exists_chartedSpace_of_isLocalHomeomorph`.
   * `g = 1/ψ` is bounded (`H0_invParam_ge`).
   * `S` is noncompact (maximum modulus).
   * `exists_uniformizing_cover`: the `ℂ`-cover case is killed by Liouville. Otherwise use the
     disc cover `p`.
2. Genuine punctures (charts without a limit in `H0`) have countably many values `1/(u₀v₀)`. Their
   limit data are discrete in the second-countable closure (F3).
3. `fatou_riesz` gives a full-measure set of good `θ`: the radial limit exists, is nonzero, and
   avoids those countably many values. The good radial-limit values are uncountable.
4. On a good ray `ψ → c₀`, but `ψ₁` does not converge in `ℂ*`, by `H0_path_limit`:
   * convergence in `S` would contradict path lifting;
   * a genuine puncture would put `ĉ` in the excluded countable set.
   So the cluster set in the torus `ℂ*/λ^ℤ` is a nondegenerate continuum, hence uncountable.
5. Each cluster point `z` in the annulus `A`: take shifted points, apply `fan_trichotomy` (case
   (iii) is killed by `no_near_axis_segment`), and take the limit segment. So `z ∈ W_{ε₀η₀}(c₀μ₁μ₂)`
   with countably many labels.
   * One `W` is uncountable, hence (F3 branch counting) contains an open disc.
   * `exists_regular_of_family` then gives `c₀μ₁μ₂ ∈ C_reg`, which is countable.
   * Hence `c₀` lies in a countable set, contradicting step 3.

**Not needed:** Picard, Lemma 15, and any hyperbolic geometry ("geodesic ray" = radius).

## State of this development (work in progress)

Steps 1 and 3 of the sketch, the plane case of step 1, and the path-lifting half of step 4 are
formalised, sorry-free, in companion modules of this workspace (none of them imports the others'
work in progress except `H0_path_limit_Iio`, which uses the statement of `H0_path_limit`):

* `Work.EQ.psi_local_chart` — on a neighbourhood of every point of `H0`, `ψ = ψ₁ψ₂` is an
  analytic function of `ψ₁` alone (from `H0_structure`); `Work.EQ.psi1_ne_zero_of_mem`.
* `Work.EQ.not_compactSpace_connectedComponent` — no component of `H0` is compact (purely
  topological: `ψ₁` is an open map and never vanishes, so its image of a component is a nonempty
  clopen subset of the connected space `ℂ` missing `0`), which feeds `exists_uniformizing_cover`.
* `Work.EQ.plane_cover_const` — the `ℂ`-cover case: `1/ψ` pulls back to a bounded entire function,
  so Liouville makes `ψ` constant on the component.
* `Work.EQ.cayley_homeomorph_uhp`, `Work.EQ.exists_disc_covering_of_uhp`,
  `Work.EQ.not_tendsto_discRay`, `Work.EQ.not_tendsto_comp_discRay` — the hyperbolic case is
  reduced to a covering by the unit disc, and a radius of the disc has no limit at `1⁻`
  (`Work.Covering.exists_tendsto_of_isCoveringMap_comp`: a covering does not create limits).
* `Work.EQ.FatouRiesz`, `Work.EQ.ae_radial_limit_ne_zero_notMem_countable`,
  `Work.EQ.good_ray_data` — Fatou–Riesz gives good radii; along them the `ψ`-limit `c₀` is
  nonzero and `1/c₀` avoids any prescribed countable set `L` of values not attained identically.
* `Work.EQ.not_tendsto_psi1_of_covering_ray` — step 4: given the path-limit dichotomy, `ψ₁`
  cannot converge along a good radius.
* `Work.EQ.H0_path_limit_Iio` — the path-limit dichotomy at `1⁻`, transferred from the
  `s → +∞` form `Work.EQ.H0_path_limit` via `Work.Topology.reparam_tendsto_Iio`.
* `Work.Topology.not_countable_of_isPreconnected_isCompact`,
  `Work.Topology.not_countable_clusterSet` — a nondegenerate continuum is uncountable, so the
  cluster set of a non-convergent path in a compact Hausdorff space is uncountable.  Together with
  the covering lemma this gives the "cluster set in the torus `ℂ*/λ^ℤ` is nondegenerate, hence
  uncountable" step, since `ψ₁` converges in `ℂ*` exactly when its image in the torus converges.

Still missing:

1. the countability of the set of puncture values `1/(u₀v₀)` (step 2) — needs the F3
   "backward Puiseux" machinery (`Work.EQ.backward_puiseux`, still a `sorry`);
2. the countability of the set of *regular values* `C_reg` (the paper's "`H` has only countably
   many components").  This is NOT free from the current definitions: it needs either
   (a) countability of the `ψ₁`-fibre of `H0` (a chain is determined by its `0`-th entry and its
   branch word; the branch word is eventually constant, but the *convention* for the two branches
   — `invBranch true/false` versus `fwdC/fwdAlt` — is only consistent near the fan family, which
   is exactly what `Work.EQ.fan_estimates` supplies), or
   (b) an equally hard alternative;
3. the trichotomy bookkeeping (step 5): every shifted cluster point of a good radius gives an
   `EqRelC`-segment, so `c₀` lies in the countable set `C_reg · (M·M)⁻¹`.  Needs
   `Work.EQ.H0_structure` (sections, `EqRelC`-segments over the annulus) and
   `Work.EQ.fan_trichotomy` (both still `sorry`), plus `Work.EQ.exists_regular_of_family` (proved)
   and `Work.EQ.charVal_props` (proved).

## What is now available (end of second session)

* Step 1: `Work.EQ.H0_component_uniformization` (dispatched; file
  `Submission/Work/EQ/H0_component_uniformization.lean`) — uniformization of a component by `ℂ` or
  `ℍ`.  Note `Work.EQ.H0_secondCountable`/`H0_component_secondCountable`: `ChainData` is a
  *countable* product, so `H0` and all its subspaces are second countable with no hypotheses.
* Step 2 (punctures): NOT done; needs `Work.EQ.backward_puiseux` (still `sorry`).
* Step 3 (good values uncountable): `Work.EQ.not_countable_good_values`
  (`Submission/Work/EQ/good_directions_uncountable.lean`), and
  `Work.EQ.fatouRiesz_holds : FatouRiesz` (`Submission/Work/EQ/fatouRiesz_holds.lean`) discharges
  the Fatou hypothesis from the workspace lemma `Work.EQ.fatou_riesz`.
* Step 4 (shifted cluster set uncountable): `Work.EQ.not_countable_shiftClusterSet_of_good_ray`
  (`Submission/Work/EQ/H0_shiftCluster.lean`), built on the torus modules `TorusZ`,
  `TorusZ_basics`, `ShiftCluster`.
* Step 5 (trichotomy bookkeeping): NOT done; needs `Work.EQ.fan_trichotomy` and
  `Work.EQ.H0_structure` (both still `sorry`) plus `Work.EQ.exists_regular_of_family` (proved).
* Countability inputs for the final contradiction:
  `Work.EQ.countable_fibre`/`H0_countable_fibre` (fibre of `ψ₁` over a point — proved by a
  colleague), `Work.EQ.countable_regular_values` (the regular values `C_reg` — proved by a
  colleague), `Work.EQ.countable_charValSet` (the set `M` of characteristic values).

## A dead end (recorded so it is not retried)

Step 5 cannot be short-circuited by reading only the `0`-th entries of the shifted chains: for a
sequence of chains `x_k ∈ H0` with `ψ₁(x_k) → z` and `ψ(x_k) → c₀`, one is tempted to pass to a
subsequence on which the fan words `ε_k, η_k` (with `(x k).1 0 = fan ε_k (ψ₁ x_k)`) are constant and
then to conclude the *scaled-free* identity `fan ε z = eqMirror (fan η (c₀/z))`.  This is wrong for
two reasons (verified in the second session):

* `List Bool × List Bool` is countably **infinite**, so no pigeonhole makes `k ↦ (ε_k, η_k)`
  eventually constant; what is needed is the *finiteness* of the set of words occurring over a fixed
  annulus, which comes from `fan_trichotomy` (case (ii)) and `CompactModPunctures`;
* in case (ii) of the trichotomy the words are `ε₀ ++ true^{s_k} ++ C_k` with `s_k → ∞` and the fan
  maps converge only to `fan ε₀ (μ₁ ·)` with a characteristic value `μ₁`; the limit identity is the
  *scaled* one `fan ε₀ (μ₁ z) = eqMirror (fan η₀ (μ₂ (c₀/z)))`, and the scales cannot be dropped.

So the countability contradiction genuinely needs the `W`-sets with their `M × M` labels
(`PAPER_PROOFS.md` §6 step 5), i.e. `fan_trichotomy` plus `charVal_props`.

## Progress as of the second session

**Step 4 of the paper's §6 sketch is now complete and sorry-free:**

* `Submission/Work/EQ/TorusZ.lean` — the torus `TorusZ l = ℂˣ ⧸ Subgroup.zpowers (lamU l)`;
* `Submission/Work/EQ/TorusZ_basics.lean` — `TorusZ_isDiscrete` (the group `λ^ℤ` is discrete in
  `ℂ*`), `TorusZ_isCoveringMap` (`ℂ* → ℂ*/λ^ℤ` is a covering map, from
  `Subgroup.isQuotientCoveringMap_of_comm`), `TorusZ_t2Space`, `TorusZ_compactSpace`,
  `mk_zpow_mul`, `TorusZ_zpow_mem_annulus` (orbit normalisation: every `λ^ℤ`-orbit meets
  `{r₁ ≤ ‖z‖ ≤ r₂}` when `r₁ ≤ λ r₂`), `exists_tendsto_of_tendsto_mk` ("coverings do not create
  limits");
* `Submission/Work/EQ/ShiftCluster.lean` — **`not_countable_shiftClusterSet`**: for a continuous
  path `u : ℝ → ℂ*` with no limit in `ℂ*` at `1⁻`, the set of `z` in the annulus `A(r₁,r₂)` which
  are limits of shifted values `λ^{p_k} u(s_k)` (`s_k → 1⁻`) is uncountable (Rychlik (140)).
  Proof: the image of `u` in the compact torus is continuous and non-convergent, so its cluster
  set is uncountable (`Work.Topology.not_countable_clusterSet`); each cluster point is the image
  of a shifted cluster point in `A`, by normalising into the compact annulus and passing to a
  convergent subsequence;
* `Submission/Work/EQ/H0_shiftCluster.lean` — **`not_countable_shiftClusterSet_of_good_ray`**:
  Step 4, i.e. the combination of the above with `Work.EQ.not_tendsto_psi1_of_covering_ray`
  (the path-limit dichotomy `H0_path_limit` is taken as the explicit hypothesis `hpath`).

namespace Work.EQ; do NOT edit; IsPuncturedChart now carries a scale κ). Proved UNIFORMIZATION library in this workspace (Submission.UnifMain etc.). With UnifMain imported write `open _root_.Topology`.

# H0_regular: every component is regular (Rychlik Thms 10–11) (7–11k; READY as stated)

**Proof.** `PAPER_PROOFS.md` §6. Assume `ψ` is nonconstant on a component `S`.
1. Setup:
   * `S` is an étale Riemann surface via `exists_chartedSpace_of_isLocalHomeomorph`.
   * `g = 1/ψ` is bounded (`H0_invParam_ge`).
   * `S` is noncompact (maximum modulus).
   * `exists_uniformizing_cover`: the `ℂ`-cover case is killed by Liouville. Otherwise use the
     disc cover `p`.
2. Genuine punctures (charts without a limit in `H0`) have countably many values `1/(u₀v₀)`. Their
   limit data are discrete in the second-countable closure (F3).
3. `fatou_riesz` gives a full-measure set of good `θ`: the radial limit exists, is nonzero, and
   avoids those countably many values. The good radial-limit values are uncountable.
4. On a good ray `ψ → c₀`, but `ψ₁` does not converge in `ℂ*`, by `H0_path_limit`:
   * convergence in `S` would contradict path lifting;
   * a genuine puncture would put `ĉ` in the excluded countable set.
   So the cluster set in the torus `ℂ*/λ^ℤ` is a nondegenerate continuum, hence uncountable.
5. Each cluster point `z` in the annulus `A`: take shifted points, apply `fan_trichotomy` (case
   (iii) is killed by `no_near_axis_segment`), and take the limit segment. So `z ∈ W_{ε₀η₀}(c₀μ₁μ₂)`
   with countably many labels.
   * One `W` is uncountable, hence (F3 branch counting) contains an open disc.
   * `exists_regular_of_family` then gives `c₀μ₁μ₂ ∈ C_reg`, which is countable.
   * Hence `c₀` lies in a countable set, contradicting step 3.

**Not needed:** Picard, Lemma 15, and any hyperbolic geometry ("geodesic ray" = radius).

## State of this development (work in progress)

Steps 1 and 3, the plane case of step 1, and step 4's path-lifting half are formalised in
companion modules of this directory:

* `Work.EQ.psi_local_chart` — `ψ` is locally an analytic function of `ψ₁` on `H0`
  (from `H0_structure`); `Work.EQ.psi1_ne_zero_of_mem`.
* `Work.EQ.not_compactSpace_connectedComponent` — no component of `H0` is compact (purely
  topological), for `exists_uniformizing_cover`.
* `Work.EQ.plane_cover_const` — the `ℂ`-cover case: `1/ψ` pulls back to a bounded entire
  function, so `ψ` is constant on the component (Liouville).
* `Work.EQ.cayley_homeomorph_uhp`, `Work.EQ.exists_disc_covering_of_uhp`,
  `Work.EQ.not_tendsto_discRay`, `Work.EQ.not_tendsto_comp_discRay` — the hyperbolic case is
  reduced to a disc cover, and a radius of the disc has no limit.
* `Work.EQ.FatouRiesz`, `Work.EQ.ae_radial_limit_ne_zero_notMem_countable`,
  `Work.EQ.good_ray_data` — Fatou's theorem gives good radii, and the `ψ`-limits along them are
  nonzero with reciprocal avoiding a countable set.
* `Work.EQ.not_tendsto_psi1_of_covering_ray` — step 4: `ψ₁` cannot converge along a good radius.

Still missing (the hard analytic core of Rychlik §5.9–§7, all of it owning the F3
"backward Puiseux" machinery): the countability of the puncture values `1/(u₀v₀)`; the
uncountability of the cluster set in the torus `ℂ*/λ^ℤ`; and the trichotomy bookkeeping that
pushes every good `ψ`-limit into the countable set `C_reg · (M·M)⁻¹`.
-/

/-! ## Session 5: the assembly is complete

`Submission/Work/EQ/H0_regular.lean` now contains a sorry-free proof of `H0_regular`, built
exactly on the interface chain described above: `H0_structure`/`H0_invParam_ge` (structure of `H0`),
`exists_uniformizing_cover` + `plane_cover_const` (`ℂ`-cover case),
`H0_disc_cover_holomorphic` (disc cover), `good_ray_data`/`not_countable_good_values`
(uncountably many good values), `H0_path_limit_Iio` (the path-limit dichotomy, used to build the
`hpath` hypothesis of `not_countable_shiftClusterSet_of_good_ray`),
`not_countable_shiftClusterSet_of_good_ray` (the shifted cluster set is uncountable) and
`cluster_values_countable` (only countably many such values), giving the contradiction.

Two auxiliary lemmas are proved in this file: `tendsto_of_meromorphicAt_of_tendsto_comp` (a
meromorphic function whose limit along a curve exists has that limit at the puncture — this is
what turns the chart branch of `H0_path_limit_Iio` into a member of the countable set `L`) and
`range_eq_univ_of_isCoveringMap` (a covering map onto a preconnected space is surjective, used to
see that `1/ψ` is nonconstant on the disc).  The theorem `fatouRiesz_ns : FatouRiesz` re-exports the
workspace Fatou–Riesz theorem through the namespace copy `Work.EQ.FR.fatou_riesz`
(`Submission/Work/EQ/fatou_riesz_ns.lean`), which exists because `Work.EQ.fatou_riesz` and
`Submission.Work.EQ.bp_aux` both declare `Work.EQ.rhoSeq.eq_1` and hence cannot be imported into a
single environment.

Step 5 (`Work.EQ.cluster_values_countable`) is imported in a *namespace-copied* form,
`Work.EQ.CVC.cluster_values_countable` (`Submission/Work/EQ/cluster_values_countable_ns.lean`),
which rests on `Work.EQ.JVC.junction_values_countable`
(`Submission/Work/EQ/junction_values_countable_ns.lean`).  The copies exist for the same reason as
`fatou_riesz_ns`: `Submission/Work/EQ/junction_values_countable.lean` declares
`Work.EQ.analyticAt_eqMirror`, which is also declared in `Submission/Work/EQ/H0_section_local.lean`
(itself unavoidable here, through `H0_structure`), so the two modules cannot be imported into one
environment.  The copies are verbatim; only the namespace changed.

Similarly, the countability of the puncture values is imported from
`Work.EQ.CPV.countable_puncture_values` (`Submission/Work/EQ/countable_puncture_values_ns.lean`),
which is the assembly of `Submission/Work/EQ/countable_puncture_values.lean` on top of the *proved*
modules `Work.EQ.countable_puncture_psi1_limits` and `Work.EQ.countable_puncture_psi2_limits`.  The
original file still contains a stale, `sorry`ed inline copy of the first of these.
-/

noncomputable section

open Filter _root_.Topology Complex Metric
open scoped Topology

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.EQ

theorem tendsto_of_meromorphicAt_of_tendsto_comp {α : Type*} {l : Filter α} (hl : l.NeBot)
    {f : ℂ → ℂ} (hf : MeromorphicAt f 0) {g : α → ℂ}
    (hg : Tendsto g l (nhdsWithin (0:ℂ) ({(0:ℂ)}ᶜ))) {v : ℂ}
    (hv : Tendsto (fun a => f (g a)) l (𝓝 v)) :
    Tendsto f (nhdsWithin (0:ℂ) ({(0:ℂ)}ᶜ)) (𝓝 v) := by
  haveI := hl
  by_cases hlim : ∃ c, Tendsto f (nhdsWithin (0:ℂ) ({(0:ℂ)}ᶜ)) (𝓝 c)
  · obtain ⟨c, hc⟩ := hlim
    have hvc : v = c := tendsto_nhds_unique hv (hc.comp hg)
    rw [hvc]; exact hc
  · have hlt : meromorphicOrderAt f (0:ℂ) < 0 := by
      rw [← not_le]
      exact fun hge => hlim (tendsto_nhds_of_meromorphicOrderAt_nonneg hf hge)
    have hcob : Tendsto f (nhdsWithin (0:ℂ) ({(0:ℂ)}ᶜ)) (Bornology.cobounded ℂ) :=
      tendsto_cobounded_of_meromorphicOrderAt_neg hlt
    have hnorm : Tendsto (fun z => ‖f z‖) (nhdsWithin (0:ℂ) ({(0:ℂ)}ᶜ)) atTop :=
      tendsto_norm_atTop_iff_cobounded.2 hcob
    exact absurd (hnorm.comp hg) (not_tendsto_atTop_of_tendsto_nhds hv.norm)

/-- `FatouRiesz` from the namespace copy `Work.EQ.FR.fatou_riesz`. -/
theorem fatouRiesz_ns : FatouRiesz := by
  intro g hg M hM
  obtain ⟨h1, h2⟩ := FR.fatou_riesz (g := g) hg (M := M) hM
  exact ⟨by simpa only [Complex.ofReal_mul] using h1,
    fun c hne => by simpa only [Complex.ofReal_mul] using h2 c hne⟩

theorem range_eq_univ_of_isCoveringMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [PreconnectedSpace Y] {p : X → Y} (hp : IsCoveringMap p) :
    Set.range p = Set.univ := by
  have hclosed : IsClosed (Set.range p) := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    obtain ⟨-, U, hyU, hUo, -, H, hH⟩ := hp y
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hy U hUo hyU
    obtain ⟨w, rfl⟩ := hz
    refine ⟨((H.symm ((⟨y, hyU⟩ : ↥U), (H ⟨w, by simpa using hzU⟩).2) : ↥(p ⁻¹' U)) : X), ?_⟩
    show p ((H.symm ((⟨y, hyU⟩ : ↥U), (H ⟨w, by simpa using hzU⟩).2) : ↥(p ⁻¹' U)) : X) = y
    rw [← hH (H.symm ((⟨y, hyU⟩ : ↥U), (H ⟨w, by simpa using hzU⟩).2))]
    simp
  have hopen : IsOpen (Set.range p) := by
    simpa [Set.image_univ] using hp.isOpenMap Set.univ isOpen_univ
  have hne : (Set.range p).Nonempty := ⟨p (Classical.arbitrary X), ⟨Classical.arbitrary X, rfl⟩⟩
  exact Set.eq_univ_of_univ_subset
    (isPreconnected_univ.subset_isClopen ⟨hclosed, hopen⟩ (by simpa using hne))

set_option maxHeartbeats 1600000 in
theorem H0_regular {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∀ p ∈ H0 a h, ∃ c : ℂ, ∀ q ∈ connectedComponentIn (H0 a h) p, q.2.1 * q.2.2 = c := by
  classical
  intro p hp
  obtain ⟨hét, hsect, -, -⟩ := H0_structure ha0 ha1 hh
  obtain ⟨ρ₀, hρ₀, hρ₀b⟩ := H0_invParam_ge ha0 ha1 hh
  suffices hmain : ∀ P : H0 a h, ∃ c : ℂ, ∀ u : ↥(connectedComponent P), psiC u = c by
    obtain ⟨c, hc⟩ := hmain ⟨p, hp⟩
    refine ⟨c, fun q hq => ?_⟩
    rw [connectedComponentIn_eq_image hp] at hq
    obtain ⟨u, hu, rfl⟩ := hq
    simpa [psiC, psi] using hc ⟨u, hu⟩
  intro P
  by_contra hnc
  have hφ : IsLocalHomeomorph (fun u : ↥(connectedComponent P) => ((u : H0 a h) : ChainData).2.1) :=
    isLocalHomeomorph_subtype_connectedComponent hét P
  obtain ⟨instC, hman, hφmd⟩ := UnivCover.exists_chartedSpace_of_isLocalHomeomorph (X := ℂ) hφ
  letI : ChartedSpace ℂ ↥(connectedComponent P) := instC
  haveI : IsManifold (modelWithCornersSelf ℂ ℂ) 1 ↥(connectedComponent P) := hman
  haveI : SecondCountableTopology ↥(connectedComponent P) := H0_component_secondCountable P
  haveI : PreconnectedSpace ↥(connectedComponent P) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent
  haveI : Nonempty ↥(connectedComponent P) := ⟨P, mem_connectedComponent⟩
  haveI : ConnectedSpace ↥(connectedComponent P) :=
    (connectedSpace_iff _).mpr ⟨inferInstance, inferInstance⟩
  have hbd : ∀ u : ↥(connectedComponent P), ρ₀ ≤ ‖psiC u‖ :=
    fun u => hρ₀b _ (u : H0 a h).2
  have hψne : ∀ u : ↥(connectedComponent P), psiC u ≠ 0 := fun u h0 => by
    have h1 := hbd u; rw [h0, norm_zero] at h1; linarith
  rcases exists_uniformizing_cover (X := ↥(connectedComponent P))
      (not_compactSpace_connectedComponent_of_isLocalHomeomorph hét P) with
    ⟨pc, hpcov, hpcmd⟩ | ⟨ph, hphcov, hphmd⟩
  · have hpψ : Differentiable ℂ fun z => ((pc z : H0 a h) : ChainData).2.1 :=
      mdifferentiable_iff_differentiable.mp (hφmd.comp hpcmd)
    obtain ⟨c, hc⟩ := plane_cover_const hsect hρ₀ hbd hpcov hpψ
    exact hnc ⟨c, fun u => by simpa [psiC] using hc u⟩
  · obtain ⟨q, hqcov, hqdiff⟩ := H0_disc_cover_holomorphic hsect hphcov hphmd hφmd
    haveI : Nonempty Disc := ⟨⟨0, by simp [Metric.mem_ball]⟩⟩
    have hqsurj : Function.Surjective q := by
      have := range_eq_univ_of_isCoveringMap hqcov
      intro y
      have : y ∈ Set.range q := by rw [this]; exact Set.mem_univ y
      exact this
    set g : ℂ → ℂ := fun z => (psiC (discExt q z))⁻¹ with hgdef
    have hg0 : ∀ z : ℂ, g z = (psiC (discExt q z))⁻¹ := fun z => rfl
    have hG : DifferentiableOn ℂ g (Metric.ball (0:ℂ) 1) :=
      hqdiff.inv (fun z _ => hψne _)
    have hM : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖g z‖ ≤ ρ₀⁻¹ := by
      intro z hz
      rw [hg0, norm_inv, discExt_of_mem q hz]
      exact (inv_le_inv₀ (norm_pos_iff.mpr (hψne _)) hρ₀).mpr (hbd _)
    have hne0 : ∃ z ∈ Metric.ball (0:ℂ) 1, g z ≠ 0 := by
      refine ⟨0, by simp [Metric.mem_ball], ?_⟩
      rw [hg0, discExt_of_mem q (by simp [Metric.mem_ball])]
      exact inv_ne_zero (hψne _)
    have hconstfalse : (∃ c : ℂ, ∀ z ∈ Metric.ball (0:ℂ) 1, g z = c) → False := by
      rintro ⟨c, hc⟩
      have hcu : ∀ u : Disc, (psiC (q u))⁻¹ = c := by
        intro u
        have h1 := hc (u : ℂ) u.2
        rw [hg0, discExt_of_mem q u.2] at h1
        exact h1
      have hc0 : c ≠ 0 := by
        intro h0
        have h1 := hcu ⟨0, by simp [Metric.mem_ball]⟩
        rw [h0] at h1
        exact (inv_ne_zero (hψne _)) h1
      refine hnc ⟨c⁻¹, fun v => ?_⟩
      obtain ⟨u, rfl⟩ := hqsurj v
      have h2 : psiC (q u) = c⁻¹ := by
        apply inv_inj.mp
        rw [inv_inv]
        exact hcu u
      simpa [psiC, psi] using h2
    have hncd : ∃ z₁ ∈ Metric.ball (0:ℂ) 1, ∃ z₂ ∈ Metric.ball (0:ℂ) 1, g z₁ ≠ g z₂ := by
      by_contra hcon
      push_neg at hcon
      exact hconstfalse ⟨g 0, fun z hz => (hcon 0 (by simp [Metric.mem_ball]) z hz).symm⟩
    set L : Set ℂ := {w : ℂ | ∃ (e : ℂ → ChainData) (u₀ v₀ : ℂ) (k : ℕ),
      IsPuncturedChart a h e u₀ k ∧
      (¬ ∃ q' ∈ H0 a h, Tendsto e (nhdsWithin (0:ℂ) ({(0:ℂ)}ᶜ)) (𝓝 q')) ∧
      Tendsto (fun ζ => (e ζ).2.2) (nhdsWithin (0:ℂ) ({(0:ℂ)}ᶜ)) (𝓝 v₀) ∧
      w = (u₀ * v₀)⁻¹} with hLdef
    have hLcount : L.Countable := by rw [hLdef]; exact CPV.countable_puncture_values ha0 ha1 hh
    have hLc_disc : ∀ c ∈ L, ∃ u : Disc, (psiC (q u))⁻¹ ≠ c := by
      intro c hc
      by_contra hcon
      push_neg at hcon
      exact hconstfalse ⟨c, fun z hz => by
        rw [hg0, discExt_of_mem q hz]; exact hcon ⟨z, hz⟩⟩
    have hLc_g : ∀ c ∈ L, ∃ z ∈ Metric.ball (0:ℂ) 1, g z ≠ c := by
      intro c hc
      obtain ⟨u, hu⟩ := hLc_disc c hc
      refine ⟨(u : ℂ), u.2, ?_⟩
      rw [hg0, discExt_of_mem q u.2]
      exact hu
    have hpath : ∀ (γ : ℝ → ChainData) (u v : ℂ), u ≠ 0 → v ≠ 0 →
        (∀ r : ℝ, r ∈ Set.Iio (1:ℝ) → γ r ∈ H0 a h) →
        ContinuousOn γ (Set.Iio (1:ℝ)) →
        Tendsto (fun r : ℝ => (γ r).2.1) (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 u) →
        Tendsto (fun r : ℝ => (γ r).2.2) (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 v) →
        (∃ p ∈ H0 a h, Tendsto γ (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 p)) ∨
          (u * v)⁻¹ ∈ L := by
      intro γ u v hu hv hγmem hγcont h1 h2
      haveI : NeBot (nhdsWithin 1 (Set.Iio (1:ℝ))) := nhdsWithin_Iio_neBot le_rfl
      rcases H0_path_limit_Iio ha0 ha1 hh hγmem hγcont hu hv h1 h2 with
        ⟨q', hq', hq'l⟩ | ⟨e, k, hchart, hρ⟩
      · exact Or.inl ⟨q', hq', hq'l⟩
      · by_cases hgen : ∃ q' ∈ H0 a h, Tendsto e (nhdsWithin (0:ℂ) ({(0:ℂ)}ᶜ)) (𝓝 q')
        · left
          obtain ⟨q', hq', hq'e⟩ := hgen
          refine ⟨q', hq', ?_⟩
          refine Filter.le_def.mpr fun W hW => ?_
          rw [Filter.mem_map]
          have hV : e ⁻¹' W ∈ nhdsWithin (0:ℂ) ({(0:ℂ)}ᶜ) := by
            rw [← Filter.mem_map]; exact Filter.le_def.mp hq'e W hW
          obtain ⟨ρ, hρpos, hρsub⟩ :=
            (Metric.nhdsWithin_basis_ball (x := (0:ℂ)) (s := ({(0:ℂ)}ᶜ : Set ℂ))).mem_iff.mp hV
          filter_upwards [hρ ρ hρpos] with r hr
          obtain ⟨ζ, hζ, hζe⟩ := hr
          change γ r ∈ W
          have h2 : e ζ ∈ W := by
            simpa only [Set.mem_preimage] using hρsub (by simpa using hζ)
          rwa [← hζe]
        · right
          have hchart' := hchart
          obtain ⟨hk, hu₀, κ, hκ, hprop, hinj, hcont, hmer, hcoord⟩ := hchart
          have hev : ∀ᶠ r in nhdsWithin 1 (Set.Iio (1:ℝ)),
              ∃ x ∈ Metric.ball (0:ℂ) 1 \ {0}, e x = γ r := by
            filter_upwards [hρ 1 one_pos] with r hr
            simpa only [Set.mem_image] using hr
          set ζf : ℝ → ℂ := fun r =>
            if h : ∃ x ∈ Metric.ball (0:ℂ) 1 \ {0}, e x = γ r then Classical.choose h else 0
            with hζdef
          have hζmem : ∀ᶠ r in nhdsWithin 1 (Set.Iio (1:ℝ)),
              ζf r ∈ Metric.ball (0:ℂ) 1 \ {0} := by
            filter_upwards [hev] with r hr
            simp only [hζdef]
            rw [dif_pos hr]
            exact (Classical.choose_spec hr).1
          have hζe : ∀ᶠ r in nhdsWithin 1 (Set.Iio (1:ℝ)), e (ζf r) = γ r := by
            filter_upwards [hev] with r hr
            simp only [hζdef]
            rw [dif_pos hr]
            exact (Classical.choose_spec hr).2
          have hψ1 : ∀ᶠ r in nhdsWithin 1 (Set.Iio (1:ℝ)),
              (γ r).2.1 = u + κ * (ζf r)^k := by
            filter_upwards [hζe, hζmem] with r he hm
            rw [← he, (hprop (ζf r) hm).2]
          have hkζ : Tendsto (fun r => κ * (ζf r)^k) (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 0) := by
            have hsum : Tendsto (fun r => u + κ * (ζf r)^k)
                (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 u) := h1.congr' hψ1
            have h2' : Tendsto (fun r => (u + κ * (ζf r)^k) - u)
                (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 (u - u)) := hsum.sub tendsto_const_nhds
            simpa using h2'
          have hzpow : Tendsto (fun r => (ζf r)^k) (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 0) := by
            have h := hkζ.const_mul κ⁻¹
            simpa only [Pi.zero_apply, mul_zero, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul] using h
          have hpow : Tendsto (fun r => ‖ζf r‖ ^ k) (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 0) := by
            have := hzpow.norm
            simpa [norm_pow] using this
          have hnorm : Tendsto (fun r => ‖ζf r‖) (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 0) := by
            rw [Metric.tendsto_nhds]
            intro ε hε
            have hεk : 0 < ε ^ k := pow_pos hε k
            filter_upwards [hpow.eventually (eventually_lt_nhds hεk)] with r hr
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
            exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (le_of_lt hε) hk.ne').mp hr
          have hζ0 : Tendsto ζf (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 0) :=
            tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
          have hζne : ∀ᶠ r in nhdsWithin 1 (Set.Iio (1:ℝ)), ζf r ∈ ({(0:ℂ)}ᶜ : Set ℂ) := by
            filter_upwards [hζmem] with r hr
            exact fun h0 => hr.2 (by simpa using h0)
          have hζlim : Tendsto ζf (nhdsWithin 1 (Set.Iio (1:ℝ))) (nhdsWithin (0:ℂ) ({(0:ℂ)}ᶜ)) :=
            tendsto_nhdsWithin_iff.mpr ⟨hζ0, hζne⟩
          have hcomp : Tendsto (fun r => (e (ζf r)).2.2) (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 v) :=
            h2.congr' (hζe.mono fun r hr => by
              show (γ r).2.2 = (e (ζf r)).2.2
              rw [← hr])
          have hgoal : Tendsto (fun ζ : ℂ => (e ζ).2.2) (nhdsWithin (0:ℂ) ({(0:ℂ)}ᶜ)) (𝓝 v) :=
            tendsto_of_meromorphicAt_of_tendsto_comp inferInstance hmer hζlim hcomp
          rw [hLdef]
          exact ⟨e, u, v, k, hchart', hgen, hgoal, rfl⟩
    have hgood := good_ray_data fatouRiesz_ns hρ₀ hbd hG L hLcount hLc_disc
    have hunc := not_countable_good_values fatouRiesz_ns hG hM hne0 hncd L hLcount hLc_g
    obtain ⟨δ, hδpos, hδcount⟩ := CVC.cluster_values_countable ha0 ha1 hh
    set GV : Set ℂ := {c₀ : ℂ | c₀ ≠ 0 ∧ c₀⁻¹ ∉ L ∧
        ∃ θ : ℝ, Tendsto (fun r : ℝ => psiC (q (discRay θ r)))
          (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 c₀)} with hGVdef
    have hIoo : Set.Ioo (0:ℝ) 1 ∈ nhdsWithin 1 (Set.Iio (1:ℝ)) :=
      (nhdsLT_basis (1:ℝ)).mem_iff.mpr ⟨0, zero_lt_one, fun t ht => ht⟩
    have hGVunc : ¬ GV.Countable := by
      intro hGVc
      apply hunc
      refine (hGVc.image (fun c => c⁻¹)).mono ?_
      rintro c ⟨θ, hc0, hcL, hclim⟩
      refine ⟨c⁻¹, ?_, by simp⟩
      refine ⟨inv_ne_zero hc0, ?_, θ, ?_⟩
      · rwa [inv_inv]
      · have hconv : (fun t : ℝ => g (t * Complex.exp ((θ:ℂ) * Complex.I)))
            =ᶠ[nhdsWithin 1 (Set.Iio (1:ℝ))] (fun t => (psiC (q (discRay θ t)))⁻¹) := by
          filter_upwards [hIoo] with t ht
          show g (t * Complex.exp ((θ:ℂ) * Complex.I)) = (psiC (q (discRay θ t)))⁻¹
          have hmemt : t * Complex.exp ((θ:ℂ) * Complex.I) ∈ Metric.ball (0:ℂ) 1 := by
            rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
            have hnorm : ‖(t:ℂ)‖ = |t| := RCLike.norm_ofReal t
            rw [hnorm, abs_of_pos ht.1]
            exact ht.2
          rw [hg0, discExt_of_mem q hmemt, discRay, dif_pos ht]
        have h1' : Tendsto (fun t : ℝ => (psiC (q (discRay θ t)))⁻¹)
            (nhdsWithin 1 (Set.Iio (1:ℝ))) (𝓝 c) := Tendsto.congr' hconv hclim
        simpa [inv_inv] using h1'.inv₀ hc0
    have hGVcount : GV.Countable := by
      refine Set.Countable.mono ?_ (hδcount (r₁ := eqLam a * (δ / 2)) (r₂ := δ / 2) ?_ ?_)
      · intro c₀ hc₀
        rw [hGVdef] at hc₀
        obtain ⟨hc₀ne, hc₀L, θ, hθlim⟩ := hc₀
        have hrle : eqLam a * (δ / 2) ≤ eqLam a * (δ / 2) := le_refl _
        refine ⟨hc₀ne, ?_⟩
        set Z : Set ℂ := {z : ℂ | eqLam a * (δ / 2) ≤ ‖z‖ ∧ ‖z‖ ≤ δ / 2 ∧
            ∃ s : ℕ → ℝ, Tendsto s atTop (nhdsWithin 1 (Set.Iio (1:ℝ))) ∧
              ∃ p : ℕ → ℤ, Tendsto (fun k => ((eqLam a : ℝ) : ℂ) ^ (p k) *
                (((q (discRay θ (s k)) : H0 a h)) : ChainData).2.1) atTop (𝓝 z)} with hZdef
        have hZunc : ¬ Z.Countable := by
          rw [hZdef]
          exact not_countable_shiftClusterSet_of_good_ray ha0 ha1 hqcov hc₀ne hθlim hc₀L hpath
            (mul_pos (eqLam_pos' ha0 ha1) (by linarith)) hrle
        have hhex : ∀ z : ℂ, ∃ (s : ℕ → ℝ) (p : ℕ → ℤ),
            (z ∈ Z → Tendsto s atTop (nhdsWithin 1 (Set.Iio (1:ℝ)))) ∧
            (z ∈ Z → Tendsto (fun k => ((eqLam a : ℝ) : ℂ) ^ (p k) *
              (((q (discRay θ (s k)) : H0 a h)) : ChainData).2.1) atTop (𝓝 z)) := by
          intro z
          by_cases hz : z ∈ Z
          · have hz' : eqLam a * (δ / 2) ≤ ‖z‖ ∧ ‖z‖ ≤ δ / 2 ∧
                ∃ s : ℕ → ℝ, Tendsto s atTop (nhdsWithin 1 (Set.Iio (1:ℝ))) ∧
                  ∃ p : ℕ → ℤ, Tendsto (fun k => ((eqLam a : ℝ) : ℂ) ^ (p k) *
                    (((q (discRay θ (s k)) : H0 a h)) : ChainData).2.1) atTop (𝓝 z) := by
              rwa [hZdef] at hz
            obtain ⟨s, hs, p, hp⟩ := hz'.2.2
            exact ⟨s, p, fun _ => hs, fun _ => hp⟩
          · exact ⟨fun _ => 0, fun _ => 0, fun h => absurd h hz, fun h => absurd h hz⟩
        let sOf : ℂ → ℕ → ℝ := fun z => Classical.choose (hhex z)
        let pOf : ℂ → ℕ → ℤ := fun z => Classical.choose (Classical.choose_spec (hhex z))
        have hsOf : ∀ z ∈ Z, Tendsto (sOf z) atTop (nhdsWithin 1 (Set.Iio (1:ℝ))) :=
          fun z hz => (Classical.choose_spec (Classical.choose_spec (hhex z))).1 hz
        have hpOf : ∀ z ∈ Z, Tendsto (fun k => ((eqLam a : ℝ) : ℂ) ^ (pOf z k) *
            (((q (discRay θ (sOf z k)) : H0 a h)) : ChainData).2.1) atTop (𝓝 z) :=
          fun z hz => (Classical.choose_spec (Classical.choose_spec (hhex z))).2 hz
        let X : ℂ → ℕ → ChainData := fun z k =>
          shiftZ a (pOf z k) ((q (discRay θ (sOf z k)) : H0 a h) : ChainData)
        refine ⟨Z, X, hZunc, ?_, ?_, ?_, ?_⟩
        · intro z hz
          have hz' : eqLam a * (δ / 2) ≤ ‖z‖ ∧ ‖z‖ ≤ δ / 2 ∧ (∃ s : ℕ → ℝ,
              Tendsto s atTop (nhdsWithin 1 (Set.Iio (1:ℝ))) ∧
                ∃ p : ℕ → ℤ, Tendsto (fun k => ((eqLam a : ℝ) : ℂ) ^ (p k) *
                  (((q (discRay θ (s k)) : H0 a h)) : ChainData).2.1) atTop (𝓝 z)) := by
            rwa [hZdef] at hz
          exact ⟨hz'.1, hz'.2.1⟩
        · intro z hz k
          exact mem_H0_shiftZ ha0 ha1 (q (discRay θ (sOf z k)) : H0 a h).2 (pOf z k)
        · intro z hz
          refine (hpOf z hz).congr' ?_
          filter_upwards with k
          rfl
        · intro z hz
          refine (hθlim.comp (hsOf z hz)).congr' ?_
          filter_upwards with k
          show psiC (q (discRay θ (sOf z k))) = psi (X z k)
          have hX : X z k = shiftZ a (pOf z k)
              ((q (discRay θ (sOf z k)) : H0 a h) : ChainData) := rfl
          rw [hX, psi_shiftZ ha0 ha1]
          rfl
      · exact mul_pos (eqLam_pos' ha0 ha1) (by linarith)
      · linarith
    exact hGVunc hGVcount

end Work.EQ
