import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornProper
import Submission.Work.Horn.pushdown_germ
import Submission.Work.Horn.basin
import Submission.Work.Horn.pushdown_critval_unique
import Submission.Work.Horn.deriv_pushdown_zero
import Submission.Work.Horn.gholo
import Submission.Work.HornTopo.horn_topo
import Submission.Work.Horn.crit_of_parts
import Submission.Work.HornPhi.horn_phi
import Submission.Work.HornVarphi.horn_varphi
import Submission.Work.Repel.germ1_differentiableOn
import Submission.Work.Repel.deriv_rescale
import Submission.Work.Horn.assembly
import Submission.Work.Horn.pushdown_germ_not_id
import Submission.Work.Horn.immediateBasin_has_critval_free
import Submission.Work.Horn.no_two_immediate_basins_rDg
import Submission.Work.Horn.unique_critPoint_of_single_critVal
import Submission.Work.HornSC.horn_sc
import Submission.Work.BasinSC.basin_sc
import Submission.Work.PlanarSC.planar_inter_sc

namespace Work.Horn

/-!
# `Work.Horn.germF0_base` — sorry-free base for the `horn_germ_F0` area

Everything of `Submission/Work/Horn/horn_germ_F0.lean` EXCEPT the target `Work.Horn.horn_germ_F0`
lives here, so that consumers do not inherit the target's remaining `sorry`.  It contains the
Écalle-germ reduction of conjunct 1 (`pushdown_second_deriv_ne_zero_iff`,
`pushdown_not_eventually_id`), the global critical value of the pushed-down horn map
(`pushdown_critval_global`, `pushdown_critval_global_eq`), the `IsParabolicGerm` clauses of the
rescaled horn map (`isParabolicGerm_germ1`), the counting step (`subsingleton_of_spreads`,
`eq_one_of_spreads`), the `∃!`-clause transport (`existsUnique_critPoint_germ1`), and the
assembly reduction `horn_germ_F0_of_basinClause`.
-/

/-- **Every immediate basin meets a capturing forward-invariant part of the basin.**

If `Ω` is a preconnected nonempty subset of the parabolic basin, forward invariant under `f`,
and every basin point eventually enters `Ω`, then each nonempty immediate basin contains `Ω`;
consequently any two nonempty immediate basins coincide.  (This is the `q = 1` half of
Shishikura's Lemma 5.2: the immediate basin is unique.)

In the application `Ω = ParabData.Ωp` is the attracting petal, `henter` is
`ParabData.basin_enter` (together with forward invariance of the basin, which forbids basin
orbits from hitting `0`), and `hΩc` is the preconnectedness of the petal. -/
theorem basin_petal_unique (f : ℂ → ℂ) (D : Set ℂ) (Ω B B' : Set ℂ)
    (hΩc : IsPreconnected Ω) (hΩsub : Ω ⊆ MandelDim.ParabolicBasin f D)
    (hΩne : Ω.Nonempty)
    (hB : MandelDim.IsImmediateBasin f D B) (hBne : B.Nonempty)
    (hB' : MandelDim.IsImmediateBasin f D B') (hB'ne : B'.Nonempty)
    (henter : ∀ z ∈ B ∪ B', ∃ n : ℕ, f^[n] z ∈ Ω) :
    B = B' := by
  obtain ⟨_, hBconn, hBsub, hBmax, hBmap, -⟩ := hB
  obtain ⟨_, hB'conn, hB'sub, hB'max, hB'map, -⟩ := hB'
  -- an immediate basin meets `Ω`
  have hBΩ : (B ∩ Ω).Nonempty := by
    obtain ⟨b, hb⟩ := hBne
    obtain ⟨n, hn⟩ := henter b (Or.inl hb)
    exact ⟨f^[n] b, Set.MapsTo.iterate hBmap n hb, hn⟩
  have hB'Ω : (B' ∩ Ω).Nonempty := by
    obtain ⟨b, hb⟩ := hB'ne
    obtain ⟨n, hn⟩ := henter b (Or.inr hb)
    exact ⟨f^[n] b, Set.MapsTo.iterate hB'map n hb, hn⟩
  -- maximality puts `Ω` inside each of them
  have hΩB : Ω ⊆ B := hBmax Ω hΩc hΩsub hBΩ
  have hΩB' : Ω ⊆ B' := hB'max Ω hΩc hΩsub hB'Ω
  obtain ⟨ω, hω⟩ := hΩne
  -- the two basins meet, so each is contained in the other
  exact le_antisymm
    (hB'max B hBconn.isPreconnected hBsub ⟨ω, hΩB' hω, hΩB hω⟩)
    (hBmax B' hB'conn.isPreconnected hB'sub ⟨ω, hΩB hω, hΩB' hω⟩)




/-- **Conjunct 1 reduced to the Écalle germ.**  `g = pushdown d.E` has the form
`ζ ↦ ζ · π (H ζ)` near `0` with `H` analytic at `0`, `H 0 = 0`, and
`g''(0) = 4πi H'(0)`; hence `g''(0) ≠ 0 ↔ H'(0) ≠ 0`.  (Source:
`Work.Horn.pushdown_germ`.) -/
theorem pushdown_second_deriv_ne_zero_iff (f₀ : ℂ → ℂ) (D₀ : Set ℂ)
    (d : MandelDim.ParabData f₀ D₀) :
    ∃ H : ℂ → ℂ, H 0 = 0 ∧ DifferentiableAt ℂ H 0 ∧
      (∀ᶠ ζ in nhds (0 : ℂ), MandelDim.pushdown d.E ζ = ζ * MandelDim.piExp (H ζ)) ∧
      (deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0 ↔ deriv H 0 ≠ 0) := by
  obtain ⟨H, hH0, hHd, hgerm, hsec⟩ := Work.Horn.pushdown_germ f₀ D₀ d
  refine ⟨H, hH0, hHd, hgerm, ?_⟩
  rw [hsec, mul_ne_zero_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    simp [Complex.I_ne_zero]


/-- **The parabolic fixed point is not in the parabolic basin** (its own neighbourhoods contain
points of the repelling limb).  Derivable from the fields alone: if `0` were in the basin, the
Abel equation `d.Φ_abel` at the fixed point would give `Φ 0 = Φ 0 + 1`. -/
theorem zero_not_mem_basin {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) :
    (0 : ℂ) ∉ MandelDim.ParabolicBasin f₀ D₀ := by
  intro h
  have hfix : f₀ 0 = 0 := hF0.1.2.2.2.1
  have habel : d.Φ (f₀ 0) = d.Φ 0 + 1 := d.Φ_abel 0 h
  rw [hfix] at habel
  have h1 : d.Φ 0 + 1 = d.Φ 0 + 0 := by rw [habel.symm, add_zero]
  exact one_ne_zero (add_left_cancel h1)

/-- **A basin orbit eventually enters every ball around `0`.**  Immediate from the defining uniform
convergence of the iterates on a neighbourhood of the starting point. -/
theorem eventually_mem_ball_of_mem_basin {f : ℂ → ℂ} {D : Set ℂ} {z : ℂ}
    (hz : z ∈ MandelDim.ParabolicBasin f D) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n in Filter.atTop, f^[n] z ∈ Metric.ball 0 r := by
  obtain ⟨U, hU, -, hconv⟩ := hz
  obtain ⟨V, hVU, -, hzV⟩ := _root_.mem_nhds_iff.mp hU
  have h := (Metric.tendstoUniformlyOn_iff.mp (hconv.mono fun x hx => hVU hx)) r hr
  filter_upwards [h] with n hn
  simpa [dist_eq_norm] using hn z hzV

/-- **A holomorphic function on a preconnected open set is nowhere locally constant, provided it is
not locally constant near one point.**  (The points at which `f` agrees with its value on a
neighbourhood form a clopen subset; on a preconnected domain it is therefore empty or everything,
and the second alternative forces `deriv f z₀ = 0`.) -/
theorem not_eventually_constant_of_deriv_ne_zero {f : ℂ → ℂ} {D : Set ℂ}
    (hD : IsOpen D) (hconn : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    {z₀ : ℂ} (hz₀ : z₀ ∈ D) (hder : deriv f z₀ ≠ 0) :
    ∀ z ∈ D, ¬ ∀ᶠ w in nhds z, f w = f z := by
  intro z hz hconst
  have hEqOn : Set.EqOn f (fun _ => f z) D :=
    (hf.analyticOnNhd hD).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn hz hconst
  have hfc : f =ᶠ[nhds z₀] (fun _ => f z) := by
    filter_upwards [hD.mem_nhds hz₀] with w hw
    exact hEqOn hw
  have hd : deriv f z₀ = deriv (fun _ : ℂ => f z) z₀ := Filter.EventuallyEq.deriv_eq hfc
  rw [hd] at hder
  simp at hder

/-- **`hopen` from a nonzero derivative on a preconnected domain** — the form `flower_q_component`
consumes.  This is `MandelDim.basin_open_map` re-exported under the name the flower interface uses;
it is the bridge from `deriv f 0 = 1` (`IsParabolicGerm`) to the openness hypothesis, and it is the
stand-alone statement of the *analytic* half of gap #5: holomorphic plus not locally constant gives
locally open. -/
theorem hopen_of_deriv_ne_zero {f : ℂ → ℂ} {D : Set ℂ}
    (hD : IsOpen D) (hconn : IsPreconnected D) (hf : DifferentiableOn ℂ f D)
    {z₀ : ℂ} (hz₀ : z₀ ∈ D) (hne : deriv f z₀ ≠ 0) :
    ∀ z ∈ D, ∀ U ∈ nhds z, f '' U ∈ nhds (f z) :=
  Work.Horn.MandelDim.basin_open_map hD hconn hf hz₀ hne

/-- **`hcB` from the component-wise petal data — the assembly of the `hcB` chain.**

Inputs: `InF0 f D` (an immediate basin with exactly one critical point), a preconnected petal `V`
inside the *ambient* basin, the capture of the basin *of the component of `0`* by `V` (output of
`Horn/petal_subset_basin_on_component`), and local openness of `f` at the points of every immediate
basin (output of `hopen_on_component` together with §18: an immediate basin sits in a non-constant
component).

Then *every* nonempty immediate basin `B` contains the unique critical point of `𝓕₀`: `V` captures
`B` and `InF0`'s basin (`capture_component`), the two coincide (`basin_petal_unique`), and the
critical point transfers. -/
theorem crit_unique_of_immediate_component {f : ℂ → ℂ} {D : Set ℂ} (hF0 : MandelDim.InF0 f D)
    {V : Set ℂ} (hVc : IsPreconnected V) (hVne : V.Nonempty)
    (hVsub : V ⊆ MandelDim.ParabolicBasin f D)
    (hcapt : ∀ B' : Set ℂ, MandelDim.IsImmediateBasin f D B' → B'.Nonempty →
      ∀ z ∈ B', ∃ n : ℕ, f^[n] z ∈ V)
    (B : Set ℂ) (hB : MandelDim.IsImmediateBasin f D B) (hBne : B.Nonempty) :
    ∃! c : ℂ, c ∈ B ∧ deriv f c = 0 := by
  obtain ⟨_, B₀, hB₀, hcrit⟩ := hF0
  obtain ⟨c₀, hc₀, huniq₀⟩ := hcrit
  have hB₀ne : B₀.Nonempty := ⟨c₀, hc₀.1⟩
  have hcap : ∀ z ∈ B ∪ B₀, ∃ n : ℕ, f^[n] z ∈ V := by
    intro z hz
    rcases hz with hzB | hzB₀
    · exact hcapt B hB hBne z hzB
    · exact hcapt B₀ hB₀ hB₀ne z hzB₀
  have hEq : B = B₀ := basin_petal_unique f D V B B₀ hVc hVsub hVne hB hBne hB₀ hB₀ne hcap
  refine ⟨c₀, ?_, ?_⟩
  · rw [hEq]; exact hc₀
  · intro y hy
    exact huniq₀ y (by rw [← hEq]; exact hy)

/-- **Monotonicity of the basin in its domain.**  Enlarging the domain of definition can only
enlarge the basin: the defining condition is a condition on the iterates and on uniform convergence
to `0`, and the only place the domain appears is in `MapsTo`.  This is the crux of the step
"`V ⊆ ParabolicBasin f (connectedComponentIn D 0) ⊆ ParabolicBasin f D`" needed to feed
`basin_petal_unique`'s maximality clause (`Horn/petal_subset_basin_on_component`). -/
theorem parabolicBasin_mono {f : ℂ → ℂ} {D D' : Set ℂ} (h : D ⊆ D') :
    MandelDim.ParabolicBasin f D ⊆ MandelDim.ParabolicBasin f D' := by
  rintro z ⟨U, hU, hmap, hconv⟩
  exact ⟨U, hU, fun n x hx => h (hmap n hx), hconv⟩

/-- **Norm of a real, read in `ℂ`.**  The toolchain has no `Complex.norm_ofReal`, so this is the
general brick (the numerals need care, see `norm_ofReal_div_two` below). -/
theorem norm_ofReal_coe (r : ℝ) : ‖(r : ℂ)‖ = |r| :=
  calc ‖(r : ℂ)‖ = Real.sqrt (‖(r : ℂ)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (r ^ 2) := by
          rw [show ‖(r : ℂ)‖ ^ 2 = r ^ 2 by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring]
    _ = |r| := Real.sqrt_sq_eq_abs r

/-- **The missing brick:** the norm of a nonnegative real, halved, i.e. `ε / 2` as the distance
from `c` to `c + ε/2` in `ℂ`.

*Signpost (this cost a build):* `(2 : ℂ)` is **not** syntactically `↑r`, so `Complex.normSq_ofReal`
silently declines to fire on it — the numeral has to be handled separately
(`norm_num [Complex.normSq_apply]`), and the same trap applies to `norm_ofReal_coe` when its argument
is a literal.  Keep both bricks; downstream lemmas about distances to `c + ε/2` need exactly this. -/
theorem norm_ofReal_div_two (ε : ℝ) (hε : 0 ≤ ε) : ‖((ε : ℂ) / 2)‖ = ε / 2 := by
  have h : Complex.normSq ((ε : ℂ) / 2) = (ε / 2) ^ 2 := by
    rw [Complex.normSq_div, Complex.normSq_ofReal]
    have h4 : Complex.normSq (2 : ℂ) = 4 := by norm_num [Complex.normSq_apply]
    rw [h4]
    ring
  have h2 : ‖((ε : ℂ) / 2)‖ ^ 2 = (ε / 2) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, h]
  nlinarith [norm_nonneg ((ε : ℂ) / 2), h2, hε]

/-- **`f` is open at the points of every immediate basin** — the third link of the `hcB` chain, and
the `hopen` argument of `Work.Horn.crit_unique_of_immediate_of_petal`, with no connectedness
assumption on `D`.

`B` is open and preconnected, `B ⊆ D` comes pointwise from the `n = 0` clause of `ParabolicBasin`,
and `f` is non-constant on `B`: a constant `c` would give `B ⊆ f '' B = {c}`, hence `B = {c}`,
contradicting `IsOpen B`.  So `AnalyticOnNhd.is_constant_or_isOpen` makes `f` open on `B`, and
intersecting a neighbourhood of `z` with `B` gives the claim. -/
theorem hopen_of_immediateBasin {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hf : DifferentiableOn ℂ f D) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f D B) :
    ∀ z ∈ B, ∀ U ∈ nhds z, f '' U ∈ nhds (f z) := by
  obtain ⟨hBopen, hBconn, hBsub, -, -, hBsurj, -⟩ := hB
  have hBsubD : B ⊆ D := by
    intro w hw
    obtain ⟨U', hU', hmap', -⟩ := hBsub hw
    obtain ⟨V, hVU, -, hwV⟩ := _root_.mem_nhds_iff.mp hU'
    exact hmap' 0 (hVU hwV)
  have hnc : ¬ ∃ c, ∀ w ∈ B, f w = c := by
    rintro ⟨c, hc⟩
    have hBsingle : B = {c} := by
      have h1 : B ⊆ {c} := by
        intro w hw
        obtain ⟨y, hy, hyw⟩ := hBsurj hw
        rw [Set.mem_singleton_iff]
        rw [← hyw, hc y hy]
      have h2 : ({c} : Set ℂ) ⊆ B := by
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        obtain ⟨b, hb⟩ := hBconn.nonempty
        obtain ⟨y, hy, hyb⟩ := hBsurj hb
        have hyc : f y = c := hc y hy
        rw [hyc] at hyb
        rw [hyb]
        exact hb
      exact Set.Subset.antisymm h1 h2
    have hnotOpen : ¬ IsOpen ({c} : Set ℂ) := by
      intro hopen
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen c rfl
      have hmem : c + (ε : ℂ) / 2 ∈ Metric.ball c ε := by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_ofReal_div_two ε hε.le]
        linarith
      have hne : c + (ε : ℂ) / 2 ≠ c := by
        intro heq
        have h2 : (ε : ℂ) / 2 = 0 := by linear_combination heq
        have h3 : ε = 0 := by
          have := congrArg Complex.re h2
          simp at this
          linarith
        linarith
      exact hne (Set.mem_singleton_iff.mp (hball hmem))
    exact hnotOpen (hBsingle ▸ hBopen)
  have hana : AnalyticOnNhd ℂ f B := (hf.analyticOnNhd hD).mono hBsubD
  have hopen : ∀ s ⊆ B, IsOpen s → IsOpen (f '' s) := by
    rcases hana.is_constant_or_isOpen hBconn.isPreconnected with hconst | hop
    · exact absurd hconst hnc
    · exact hop
  intro z hzB U hU
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  have hVB : IsOpen (V ∩ B) := hVopen.inter hBopen
  have himg : f '' (V ∩ B) ∈ nhds (f z) :=
    (hopen (V ∩ B) Set.inter_subset_right hVB).mem_nhds ⟨z, ⟨hzV, hzB⟩, rfl⟩
  exact Filter.mem_of_superset himg (Set.image_mono (Set.inter_subset_left.trans hVU))

/-- **The `-1`-translate of an upper-half-plane point of `Bu` lies in `Bu`** (and hence its
`φ`-value lies in the immediate basin `B`).  This is the input the critical-value analysis needs:
it replaces the (`-1`)-invariance of `φ ⁻¹' B ∩ d.Dφ`, which is *not* a consequence of the
`ParabData` fields, by the half-plane containment `hup` of the statement. -/
theorem phi_sub_one_mem_of_im {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {B : Set ℂ} {η : ℝ} {Bu : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hup : {w : ℂ | η < w.im} ⊆ Bu) :
    ∀ v : ℂ, η < v.im → d.φ (v - 1) ∈ B := by
  intro v hv
  have hmem : v - 1 ∈ Bu := hup (by simpa using hv)
  have hsub : Bu ⊆ d.φ ⁻¹' B ∩ d.Dφ := hBu ▸ connectedComponentIn_subset _ _
  exact (hsub hmem).1

/-- **The unique critical point of `f₀` in a given immediate basin.**

If the attracting petal `Ωp` is preconnected and captures all basin orbits, then by
`basin_petal_unique` every nonempty immediate basin equals the one produced by `InF0`, so the
unique critical point of `𝓕₀` sits in *any* given nonempty immediate basin. -/
theorem crit_unique_of_immediate {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF0 : MandelDim.InF0 f₀ D₀) (hΩc : IsPreconnected d.Ωp)
    (hΩenter : ∀ z ∈ MandelDim.ParabolicBasin f₀ D₀, ∃ n : ℕ, f₀^[n] z ∈ d.Ωp)
    (B : Set ℂ) (hB : MandelDim.IsImmediateBasin f₀ D₀ B) (hBne : B.Nonempty) :
    ∃! c : ℂ, c ∈ B ∧ deriv f₀ c = 0 := by
  obtain ⟨_, B₀, hB₀, hcrit⟩ := hF0
  obtain ⟨c₀, hc₀, huniq₀⟩ := hcrit
  have hB₀ne : B₀.Nonempty := ⟨c₀, hc₀.1⟩
  have hΩne : d.Ωp.Nonempty := by
    obtain ⟨b, hb⟩ := hBne
    obtain ⟨n, hn⟩ := hΩenter b (hB.2.2.1 hb)
    exact ⟨f₀^[n] b, hn⟩
  have hEq : B = B₀ := basin_petal_unique f₀ D₀ d.Ωp B B₀ hΩc d.Ωp_sub hΩne
    hB hBne hB₀ hB₀ne (fun z hz => hΩenter z (hz.elim (fun h => hB.2.2.1 h) (fun h => hB₀.2.2.1 h)))
  refine ⟨c₀, ?_, ?_⟩
  · rw [hEq]; exact hc₀
  · intro y hy
    exact huniq₀ y (by rw [← hEq]; exact hy)


/-- **The unique critical point of `f₀` in a given immediate basin** (petal form).

Same as `crit_unique_of_immediate`, but with an *arbitrary* preconnected capturing part `Ω` of the
basin instead of `ParabData.Ωp`: instantiate with `Ω := V 0` from `Work.Horn.flower_q` (q = 1 for
an order-2 germ), which supplies `IsPreconnected`, `Ω ⊆ basin` and the capture clause. -/
theorem crit_unique_of_immediate_petal {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω) (hΩsub : Ω ⊆ MandelDim.ParabolicBasin f₀ D₀)
    (hΩne : Ω.Nonempty)
    (hΩenter : ∀ z ∈ MandelDim.ParabolicBasin f₀ D₀, ∃ n : ℕ, f₀^[n] z ∈ Ω)
    (B : Set ℂ) (hB : MandelDim.IsImmediateBasin f₀ D₀ B) (hBne : B.Nonempty) :
    ∃! c : ℂ, c ∈ B ∧ deriv f₀ c = 0 := by
  obtain ⟨_, B₀, hB₀, hcrit⟩ := hF0
  obtain ⟨c₀, hc₀, huniq₀⟩ := hcrit
  have hB₀ne : B₀.Nonempty := ⟨c₀, hc₀.1⟩
  have hEq : B = B₀ := basin_petal_unique f₀ D₀ Ω B B₀ hΩc hΩsub hΩne hB hBne hB₀ hB₀ne
    (fun z hz => hΩenter z (hz.elim (fun h => hB.2.2.1 h) (fun h => hB₀.2.2.1 h)))
  refine ⟨c₀, ?_, ?_⟩
  · rw [hEq]; exact hc₀
  · intro y hy
    exact huniq₀ y (by rw [← hEq]; exact hy)

theorem isOpen_parabolicBasin (f : ℂ → ℂ) (D : Set ℂ) :
    IsOpen (MandelDim.ParabolicBasin f D) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨U, hU, hmap, hconv⟩
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  refine Filter.mem_of_superset (hVopen.mem_nhds hzV) fun w hw =>
    ⟨V, hVopen.mem_nhds hw, fun n x hx => hmap n (hVU hx),
      hconv.mono fun x hx => hVU hx⟩

/-- **All critical values of the pushed-down horn map near `0` coincide.**

Transports the critical-value uniqueness of the lifted horn map
(`Work.Horn.pushdown_critval_unique`, above the line `Im w > η`) to the pushed-down germ: for
`0 < ‖ζ‖ < exp (-2π max η η₀)` the principal lift `w = log ζ/(2πi)` has `Im w > max η η₀`, hence
`w ∈ DE` (`ends_sub`), `pushdown d.E ζ = π (d.E w)` (`pushdown_piExp`, using `T`-equivariance on
`{|Im| > η₀}`), and critical points correspond (`Work.Horn.deriv_pushdown_zero`). -/
theorem pushdown_critval_germ {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hcB : ∃! c : ℂ, c ∈ B ∧ deriv f₀ c = 0)
    {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hF0 : MandelDim.InF0 f₀ D₀) :
    ∃ v₀ : ℂ, ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < Real.exp (-(2 * Real.pi * max η d.η₀)) →
      deriv (MandelDim.pushdown d.E) ζ = 0 → MandelDim.pushdown d.E ζ = v₀ := by
  have hT : MandelDim.IsTInvariant {w : ℂ | d.η₀ < |w.im|} := fun w => by simp
  have hopen : IsOpen {w : ℂ | d.η₀ < |w.im|} :=
    isOpen_Ioi.preimage (continuous_abs.comp Complex.continuous_im)
  have heq : ∀ u ∈ ({w : ℂ | d.η₀ < |w.im|} : Set ℂ), d.E (u + 1) = d.E u + 1 := by
    intro u hu
    have hu1 : u + 1 ∈ ({w : ℂ | d.η₀ < |w.im|} : Set ℂ) := by simpa using hu
    exact Work.Horn.MandelDim.ParabData.E_add_one d
      ⟨(d.ends_sub u hu).1, (d.ends_sub u hu).2⟩
      ⟨(d.ends_sub (u + 1) hu1).1, (d.ends_sub (u + 1) hu1).2⟩
  obtain ⟨v₀, hv₀⟩ := Work.Horn.pushdown_critval_unique f₀ D₀ d B hB hcB η Bu Bl hBu hBl hsub
    hup hlo (fun v hv => phi_sub_one_mem_of_im d hBu hup v hv) hF0
  refine ⟨v₀, fun ζ hζ0 hζ hcrit => ?_⟩
  set w : ℂ := Complex.log ζ / (2 * Real.pi * Complex.I) with hw
  have hζne : ζ ≠ 0 := norm_pos_iff.mp hζ0
  have hπw : MandelDim.piExp w = ζ := Work.Horn.MandelDim.piExp_log_div ζ hζne
  have hnorm : ‖MandelDim.piExp w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
    rw [MandelDim.piExp, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have hexp : Real.exp (-(2 * Real.pi * w.im)) = ‖ζ‖ := by rw [← hnorm, hπw]
  have hbig : max η d.η₀ < w.im := by
    have h1 : Real.log ‖ζ‖ = -(2 * Real.pi * w.im) := by rw [← hexp, Real.log_exp]
    have h3 : Real.log ‖ζ‖ < Real.log (Real.exp (-(2 * Real.pi * max η d.η₀))) :=
      Real.log_lt_log hζ0 hζ
    rw [h1, Real.log_exp] at h3
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    nlinarith [h2π]
  have hIm₀ : d.η₀ < |w.im| := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hbig (le_abs_self _))
  have hwS : w ∈ ({w : ℂ | d.η₀ < |w.im|} : Set ℂ) := by simpa using hIm₀
  have hwDE : w ∈ d.DE := ⟨(d.ends_sub w hIm₀).1, (d.ends_sub w hIm₀).2⟩
  have hmem : MandelDim.piExp w ∈ Metric.ball 0 (Real.exp (-(2 * Real.pi * d.η₀))) \ {0} := by
    constructor
    · rw [Metric.mem_ball, dist_zero_right, hπw]
      have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
      have hle : Real.exp (-(2 * Real.pi * max η d.η₀)) ≤ Real.exp (-(2 * Real.pi * d.η₀)) :=
        Real.exp_le_exp.mpr (by nlinarith [le_max_right η d.η₀, h2π])
      linarith
    · simp [hπw, hζne]
  have hd : DifferentiableAt ℂ (MandelDim.pushdown d.E) (MandelDim.piExp w) :=
    (Work.Horn.pushdown_differentiableOn_punctured f₀ D₀ d).differentiableAt
      ((Metric.isOpen_ball.inter isClosed_singleton.isOpen_compl).mem_nhds hmem)
  have hEat : DifferentiableAt ℂ d.E w := by
    have hφ : DifferentiableAt ℂ d.φ w :=
      d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds (d.ends_sub w hIm₀).1)
    have hΦ : DifferentiableAt ℂ d.Φ (d.φ w) :=
      d.Φ_holo.differentiableAt
        ((isOpen_parabolicBasin f₀ D₀).mem_nhds (d.ends_sub w hIm₀).2)
    change DifferentiableAt ℂ (fun x => d.Φ (d.φ x)) w
    exact hΦ.comp w hφ
  have hder : deriv (MandelDim.pushdown d.E) (MandelDim.piExp w) = 0 ↔ deriv d.E w = 0 :=
    Work.Horn.deriv_pushdown_zero hT hwS (hopen.mem_nhds hwS) heq hEat hd
  have hEcrit : deriv d.E w = 0 := by rw [← hder, hπw]; exact hcrit
  rw [← hπw, Work.Horn.MandelDim.pushdown_piExp hT (fun u hu _ => heq u hu) hwS]
  exact hv₀ w (lt_of_le_of_lt (le_max_left _ _) hbig) hEcrit


/-! ## 18. Interface plumbing for the target

The statement's `Bu`, `Bl` are the components of `d.φ ⁻¹' B ∩ d.Dφ` through `±i(η+1)`.  The
`HornTopoStatement` of the lead's decomposition (`Work.HornTopo.horn_topo`) gives all the
structural facts about the *canonical* components `BuOf d B`, `BlOf d B` (through `±i(η₀+1)`).
Since two components of one set that meet are equal, and both the statement's `Bu` and `BuOf d B`
contain the half plane `{|Im| > max η η₀}`, the two agree. -/

/-- **`hcB` for an arbitrary nonempty immediate basin of an `𝓕₀`-germ.**  Uniqueness of the
immediate basin via `basin_petal_unique` and `ParabData.Ωp`: `parabaticBasin`-orbits cannot hit `0`
(inside an immediate basin, `MapsTo` keeps them there and `zero_not_mem_basin` forbids `0`), so the
petal captures every orbit. -/
theorem immediate_basin_crit_unique {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) : ∃! c : ℂ, c ∈ B ∧ deriv f₀ c = 0 := by
  obtain ⟨hgem, B₀, hB₀, c₀, hc₀, hc₀uniq⟩ := hF0
  have hF0c : MandelDim.InF0 f₀ D₀ := ⟨hgem, B₀, hB₀, c₀, hc₀, hc₀uniq⟩
  have hB₀ne : B₀.Nonempty := ⟨c₀, hc₀.1⟩
  have hent : ∀ z ∈ B ∪ B₀, ∃ n : ℕ, f₀^[n] z ∈ d.Ωp := by
    intro z hz
    have hzb : z ∈ MandelDim.ParabolicBasin f₀ D₀ :=
      hz.elim (fun h => hB.2.2.1 h) (fun h => hB₀.2.2.1 h)
    have hne : ∀ n : ℕ, f₀^[n] z ≠ 0 := by
      intro n hn
      have h0 : (0 : ℂ) ∈ MandelDim.ParabolicBasin f₀ D₀ := by
        rw [← hn]
        exact hz.elim (fun h => hB.2.2.1 (hB.2.2.2.2.1.iterate n h))
          (fun h => hB₀.2.2.1 (hB₀.2.2.2.2.1.iterate n h))
      exact zero_not_mem_basin hF0c d h0
    exact d.basin_enter z hzb hne
  have heq : B = B₀ :=
    basin_petal_unique f₀ D₀ d.Ωp B B₀ d.Ωp_conn.isPreconnected d.Ωp_sub d.Ωp_conn.nonempty
      hB hBne hB₀ hB₀ne hent
  rw [heq]
  exact ⟨c₀, hc₀, fun c' hc' => hc₀uniq c' hc'⟩

/-- `IsF0Setup f₀ D₀ B c` for an arbitrary nonempty immediate basin `B` of an `𝓕₀`-germ. -/
theorem isF0Setup_of_immediateBasin {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) : ∃ c : ℂ, MandelDim.IsF0Setup f₀ D₀ B c := by
  obtain ⟨c, hc, hcu⟩ := immediate_basin_crit_unique hF0 d hB hBne
  exact ⟨c, hF0.1, hB, hc.1, hc.2, fun c' hc' hd' => hcu c' ⟨hc', hd'⟩⟩

/-- `BuOf d B` is the component of `d.φ ⁻¹' B ∩ d.Dφ` through `i (η₀ + 1)`. -/
theorem BuOf_eq_component {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (B : Set ℂ) :
    MandelDim.BuOf d B = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (d.η₀ + 1)) := by
  rw [MandelDim.BuOf, MandelDim.Btil]
  congr 1
  ext w
  simp [Set.mem_inter_iff, and_comm]

/-- `BlOf d B` is the component of `d.φ ⁻¹' B ∩ d.Dφ` through `-i (η₀ + 1)`. -/
theorem BlOf_eq_component {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (B : Set ℂ) :
    MandelDim.BlOf d B =
      connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (d.η₀ + 1))) := by
  rw [MandelDim.BlOf, MandelDim.Btil]
  congr 1
  ext w
  simp [Set.mem_inter_iff, and_comm]

/-- **The statement's `Bu` is the canonical upper component.** -/
theorem Bu_eq_BuOf {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ}
    {η : ℝ} {Bu : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hup : {w : ℂ | η < w.im} ⊆ Bu)
    (hup₀ : {w : ℂ | d.η₀ < w.im} ⊆ MandelDim.BuOf d B) :
    Bu = MandelDim.BuOf d B := by
  set S := d.φ ⁻¹' B ∩ d.Dφ with hS
  set p : ℂ := Complex.I * ((max η d.η₀ : ℝ) + 1) with hp
  have hp_im : p.im = max η d.η₀ + 1 := by
    rw [hp]; simp [Complex.mul_im]
  have h1 : p ∈ connectedComponentIn S (Complex.I * (η + 1)) := by
    rw [← hBu]
    exact hup (by show η < p.im; rw [hp_im]; linarith [le_max_left η d.η₀])
  have h2 : p ∈ connectedComponentIn S (Complex.I * (d.η₀ + 1)) := by
    rw [← BuOf_eq_component d B]
    exact hup₀ (by show d.η₀ < p.im; rw [hp_im]; linarith [le_max_right η d.η₀])
  have e1 : connectedComponentIn S (Complex.I * (η + 1)) = connectedComponentIn S p :=
    connectedComponentIn_eq h1
  have e2 : connectedComponentIn S p = connectedComponentIn S (Complex.I * (d.η₀ + 1)) :=
    (connectedComponentIn_eq h2).symm
  have hBueq : Bu = connectedComponentIn S (Complex.I * (η + 1)) := by rw [hBu, hS]
  have hBuOfeq : MandelDim.BuOf d B = connectedComponentIn S (Complex.I * (d.η₀ + 1)) := by
    rw [BuOf_eq_component d B, hS]
  rw [hBueq, e1, e2, ← hBuOfeq]

/-- **The statement's `Bl` is the canonical lower component.** -/
theorem Bl_eq_BlOf {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ}
    {η : ℝ} {Bl : Set ℂ}
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hlo₀ : {w : ℂ | w.im < -d.η₀} ⊆ MandelDim.BlOf d B) :
    Bl = MandelDim.BlOf d B := by
  set S := d.φ ⁻¹' B ∩ d.Dφ with hS
  set p : ℂ := -(Complex.I * ((max η d.η₀ : ℝ) + 1)) with hp
  have hp_im : p.im = -(max η d.η₀ + 1) := by
    rw [hp]; simp [Complex.mul_im]
  have h1 : p ∈ connectedComponentIn S (-(Complex.I * (η + 1))) := by
    rw [← hBl]
    exact hlo (by show p.im < -η; rw [hp_im]; linarith [le_max_left η d.η₀])
  have h2 : p ∈ connectedComponentIn S (-(Complex.I * (d.η₀ + 1))) := by
    rw [← BlOf_eq_component d B]
    exact hlo₀ (by show p.im < -d.η₀; rw [hp_im]; linarith [le_max_right η d.η₀])
  have e1 : connectedComponentIn S (-(Complex.I * (η + 1))) = connectedComponentIn S p :=
    connectedComponentIn_eq h1
  have e2 : connectedComponentIn S p = connectedComponentIn S (-(Complex.I * (d.η₀ + 1))) :=
    (connectedComponentIn_eq h2).symm
  have hBleq : Bl = connectedComponentIn S (-(Complex.I * (η + 1))) := by rw [hBl, hS]
  have hBlOfeq : MandelDim.BlOf d B = connectedComponentIn S (-(Complex.I * (d.η₀ + 1))) := by
    rw [BlOf_eq_component d B, hS]
  rw [hBleq, e1, e2, ← hBlOfeq]

/-- **All structural facts for the statement's own `Bu`, `Bl`.**

`Bu` and `Bl` are open, `ℤ`-invariant (`T`-invariant), their union lies in `DE`, and they contain
the half planes above `η` and below `-η` (the latter by hypothesis). -/
theorem horn_topo_facts {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    IsOpen Bu ∧ IsOpen Bl ∧ MandelDim.IsTInvariant Bu ∧ MandelDim.IsTInvariant Bl ∧
      {w : ℂ | d.η₀ < w.im} ⊆ MandelDim.BuOf d B ∧
      {w : ℂ | w.im < -d.η₀} ⊆ MandelDim.BlOf d B ∧ Bu ∪ Bl ⊆ d.DE := by
  obtain ⟨c, hsetup⟩ := isF0Setup_of_immediateBasin hF0 d hB hBne
  have h := Work.HornTopo.horn_topo f₀ D₀ B c d hsetup
  obtain ⟨hBuO, hBlO, hBuT, hBlT, hup₀, hlo₀, hsub₀⟩ := h
  refine ⟨?_, ?_, ?_, ?_, hup₀, hlo₀, ?_⟩
  · rwa [Bu_eq_BuOf d hBu hup hup₀]
  · rwa [Bl_eq_BlOf d hBl hlo hlo₀]
  · rwa [Bu_eq_BuOf d hBu hup hup₀]
  · rwa [Bl_eq_BlOf d hBl hlo hlo₀]
  · rwa [Bu_eq_BuOf d hBu hup hup₀, Bl_eq_BlOf d hBl hlo hlo₀]

/-- `HornData.g_holo` for the statement's own `Bu`, `Bl`, `η`: `pushdown d.E` is holomorphic on
`{0} ∪ π(Bu ∪ Bl)`. -/
theorem pushdown_g_holo {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    DifferentiableOn ℂ (MandelDim.pushdown d.E) (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := by
  obtain ⟨hBuO, hBlO, hBuT, hBlT, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  exact Work.Horn.pushdown_E_differentiableOn d η Bu Bl hBuO hBlO hBuT hBlT hsub hup hlo


/-! ## 19. Openness of the domain, the global critical value, and `IsParabolicGerm` -/

/-- `{0} ∪ π(Bu ∪ Bl)` is open. -/
theorem isOpen_insert_piExp {Bu Bl : Set ℂ} {η : ℝ} (hBuO : IsOpen Bu) (hBlO : IsOpen Bl)
    (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := by
  have h1 : {w : ℂ | η + 1 ≤ |w.im|} ⊆ Bu ∪ Bl := by
    intro w hw
    have hw' : η + 1 ≤ |w.im| := by simpa only [Set.mem_setOf_eq] using hw
    rcases lt_or_ge w.im 0 with h | h
    · rw [abs_of_neg h] at hw'
      exact Or.inr (hlo (by show w.im < -η; linarith))
    · rw [abs_of_nonneg h] at hw'
      exact Or.inl (hup (by show η < w.im; linarith))
  exact Work.Repel.isOpen_insert_zero_piExp_image (hBuO.union hBlO) h1

/-- Pointwise: the derivative of `ζ ↦ s * f (ζ / s)` is `ζ ↦ f' (ζ / s)`. -/
theorem deriv_rescale_eq (f : ℂ → ℂ) (s : ℂ) (hs : s ≠ 0) :
    deriv (fun ζ : ℂ => s * f (ζ / s)) = fun ζ : ℂ => deriv f (ζ / s) := by
  funext ζ
  rcases em (DifferentiableAt ℂ f (ζ / s)) with hf | hf
  · have hd : DifferentiableAt ℂ (fun z : ℂ => z / s) ζ := differentiableAt_id.div_const s
    have hcomp := deriv_comp (x := ζ) (h₂ := f) (h := fun z : ℂ => z / s)
      (by simpa using hf) hd
    simp only [Function.comp_def] at hcomp
    rw [deriv_const_mul_field s, hcomp]
    have h3 : deriv (fun z : ℂ => z / s) ζ = 1 / s := by
      simpa using deriv_div_const (f := id) (c := s) (x := ζ)
    rw [h3]
    field_simp
  · have hnf : ¬ DifferentiableAt ℂ (fun ζ : ℂ => s * f (ζ / s)) ζ := by
      intro h
      have hmul : DifferentiableAt ℂ (fun w : ℂ => w * s) (ζ / s) :=
        differentiableAt_id.mul_const s
      have h2a : DifferentiableAt ℂ (fun w : ℂ => s * f (w * s / s)) (ζ / s) :=
        DifferentiableAt.comp (x := (ζ / s)) (f := fun w : ℂ => w * s)
          (g := fun z : ℂ => s * f (z / s)) (by simpa [div_mul_cancel₀ ζ hs] using h) hmul
      have h2 : DifferentiableAt ℂ (fun w : ℂ => (1 / s) * (s * f (w * s / s))) (ζ / s) :=
        h2a.const_mul (1 / s)
      have he : (fun w : ℂ => (1 / s) * (s * f (w * s / s))) = f := by
        funext w
        rw [mul_div_cancel_right₀ w hs]
        field_simp
      rw [he] at h2
      exact hf h2
    rw [deriv_zero_of_not_differentiableAt hnf, deriv_zero_of_not_differentiableAt hf]

/-- Differentiating `ζ ↦ f (ζ / s)` at `0` divides the derivative by `s`. -/
theorem deriv_comp_div_const (f : ℂ → ℂ) (s : ℂ) (hs : s ≠ 0) :
    deriv (fun ζ : ℂ => f (ζ / s)) 0 = deriv f 0 / s := by
  rcases em (DifferentiableAt ℂ f 0) with hf | hf
  · have hd : DifferentiableAt ℂ (fun z : ℂ => z / s) 0 := differentiableAt_id.div_const s
    have hcomp := deriv_comp (x := (0 : ℂ)) (h₂ := f) (h := fun z : ℂ => z / s)
      (by simpa using hf) hd
    simp only [Function.comp_def, zero_div] at hcomp
    rw [hcomp]
    have h3 : deriv (fun z : ℂ => z / s) 0 = 1 / s := by
      simpa using deriv_div_const (f := id) (c := s) (x := (0 : ℂ))
    rw [h3]
    field_simp
  · have hnf : ¬ DifferentiableAt ℂ (fun ζ : ℂ => f (ζ / s)) 0 := by
      intro h
      have hmul : DifferentiableAt ℂ (fun w : ℂ => w * s) 0 := differentiableAt_id.mul_const s
      have h2 : DifferentiableAt ℂ (fun w : ℂ => f (w * s / s)) 0 :=
        DifferentiableAt.comp (x := (0 : ℂ)) (f := fun w : ℂ => w * s)
          (g := fun z : ℂ => f (z / s)) (by simpa using h) hmul
      have he : (fun w : ℂ => f (w * s / s)) = f := by
        funext w; rw [mul_div_cancel_right₀ w hs]
      rw [he] at h2
      exact hf h2
    rw [deriv_zero_of_not_differentiableAt hnf, deriv_zero_of_not_differentiableAt hf, zero_div]

/-- The second derivative of the rescaled germ `ζ ↦ s * f (ζ / s)`. -/
theorem deriv_deriv_rescale (f : ℂ → ℂ) (s : ℂ) (hs : s ≠ 0) :
    deriv (deriv (fun ζ : ℂ => s * f (ζ / s))) 0 = deriv (deriv f) 0 / s := by
  rw [deriv_rescale_eq f s hs]
  exact deriv_comp_div_const (deriv f) s hs

/-- **The critical value of the pushed-down horn map is unique** (global form).

Every critical point of `g = pushdown d.E` **inside** `{0} ∪ π(Bu ∪ Bl)` (the only place where `g`
is the horn map rather than junk) has the same value `π(Φ₀ c)`.  The proof pushes `crit_of_parts`
(all critical values of `Ẽ` on `BuOf ∪ BlOf` are `Φ₀ c + ℤ`) along the `ℤ`-action. -/
theorem pushdown_critval_global {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    ∃ v : ℂ, ∀ ζ ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      deriv (MandelDim.pushdown d.E) ζ = 0 → MandelDim.pushdown d.E ζ = v := by
  obtain ⟨c, hsetup⟩ := isF0Setup_of_immediateBasin hF0 d hB hBne
  obtain ⟨hBuO, hBlO, hBuT, hBlT, hup₀, hlo₀, -⟩ :=
    horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hBuE : Bu = MandelDim.BuOf d B := Bu_eq_BuOf d hBu hup hup₀
  have hBlE : Bl = MandelDim.BlOf d B := Bl_eq_BlOf d hBl hlo hlo₀
  have hcrit := Work.Horn.crit_of_parts Work.HornPhi.horn_phi Work.HornVarphi.horn_varphi
    f₀ D₀ B c d hsetup
  have hcrit' : ∀ w ∈ Bu ∪ Bl, deriv d.E w = 0 → ∃ k : ℤ, d.E w = d.Φ c + k := by
    intro w hw hz
    exact hcrit w (by rw [← hBuE, ← hBlE]; exact hw) hz
  have hholo := pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have hOpen := isOpen_insert_piExp hBuO hBlO hup hlo
  have hUO : IsOpen (Bu ∪ Bl) := hBuO.union hBlO
  have hdiffU : DifferentiableOn ℂ d.E (Bu ∪ Bl) := (Work.Horn.differentiableOn_E d).mono hsub
  have hT : MandelDim.IsTInvariant (Bu ∪ Bl) := fun u => by
    constructor
    · rintro (h | h)
      · exact Or.inl ((hBuT u).mp h)
      · exact Or.inr ((hBlT u).mp h)
    · rintro (h | h)
      · exact Or.inl ((hBuT u).mpr h)
      · exact Or.inr ((hBlT u).mpr h)
  have heq : ∀ u ∈ Bu ∪ Bl, d.E (u + 1) = d.E u + 1 :=
    fun u hu => Work.Horn.MandelDim.ParabData.E_add_one d (hsub hu) (hsub ((hT u).mp hu))
  have heq3 : ∀ u ∈ Bu ∪ Bl, u + 1 ∈ Bu ∪ Bl → d.E (u + 1) = d.E u + 1 :=
    fun u hu _ => heq u hu
  refine ⟨MandelDim.piExp (d.Φ c), ?_⟩
  intro ζ hζ hd
  rcases Set.mem_insert_iff.mp hζ with rfl | hζ
  · exfalso
    rw [Work.Horn.MandelDim.deriv_pushdown_E d] at hd
    exact one_ne_zero hd
  · obtain ⟨w, hw, rfl⟩ := hζ
    have hEd : DifferentiableAt ℂ d.E w := (hdiffU w hw).differentiableAt (hUO.mem_nhds hw)
    have hmem : MandelDim.piExp w ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) :=
      Set.mem_insert_of_mem _ ⟨w, hw, rfl⟩
    have hgd : DifferentiableAt ℂ (MandelDim.pushdown d.E) (MandelDim.piExp w) :=
      (hholo (MandelDim.piExp w) hmem).differentiableAt (hOpen.mem_nhds hmem)
    have hz : deriv d.E w = 0 :=
      (Work.Horn.deriv_pushdown_zero hT hw (hUO.mem_nhds hw) heq hEd hgd).mp hd
    obtain ⟨k, hk⟩ := hcrit' w hw hz
    rw [Work.Horn.MandelDim.pushdown_piExp hT heq3 hw, hk,
      Work.Horn.MandelDim.piExp_add_intCast]

/-- **`IsParabolicGerm` for the rescaled pushed-down horn map.**  This is the first five clauses of
`InF0 (germ1 (s₀ d) d.E) (Dgerm1 (s₀ d) (Bu ∪ Bl))`: openness of the domain, `0` in it, holomorphy,
`g 0 = 0`, `g'(0) = 1`, `g''(0) = 2` (the last needs `hsecond`). -/
theorem isParabolicGerm_germ1 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hsecond : deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0) :
    MandelDim.IsParabolicGerm (Work.Repel.germ1 (Work.Repel.s0 d) d.E)
      (Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl)) := by
  obtain ⟨hBuO, hBlO, hBuT, hBlT, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hs : Work.Repel.s0 d ≠ 0 := by
    rw [Work.Repel.s0]
    exact div_ne_zero hsecond (by norm_num)
  have hUO : IsOpen (Bu ∪ Bl) := hBuO.union hBlO
  have hT : MandelDim.IsTInvariant (Bu ∪ Bl) := fun u => by
    constructor
    · rintro (h | h)
      · exact Or.inl ((hBuT u).mp h)
      · exact Or.inr ((hBlT u).mp h)
    · rintro (h | h)
      · exact Or.inl ((hBuT u).mpr h)
      · exact Or.inr ((hBlT u).mpr h)
  have heq : MandelDim.IsTEquivariantOn d.E (Bu ∪ Bl) :=
    ⟨hT, fun w hw => Work.Horn.MandelDim.ParabData.E_add_one d (hsub hw) (hsub ((hT w).mp hw))⟩
  have hdiff : DifferentiableOn ℂ d.E (Bu ∪ Bl) := (Work.Horn.differentiableOn_E d).mono hsub
  have hy : ∀ w : ℂ, η + 1 ≤ |w.im| → w ∈ Bu ∪ Bl := by
    intro w hw
    rcases lt_or_ge w.im 0 with h | h
    · exact Or.inr (hlo (by show w.im < -η; rw [abs_of_neg h] at hw; linarith))
    · exact Or.inl (hup (by show η < w.im; rw [abs_of_nonneg h] at hw; linarith))
  have hEu : Filter.Tendsto (fun w => d.E w - w) MandelDim.upperEnd (nhds 0) := d.E_upper
  obtain ⟨hOp, h0, hDiff, hfix⟩ :=
    Work.Repel.germ1_differentiableOn (s := Work.Repel.s0 d) (DR := Bu ∪ Bl) (y := η + 1)
      (c := 0) hs hUO heq hdiff hy (by simpa using hEu)
  have hder1 : deriv (Work.Repel.germ1 (Work.Repel.s0 d) d.E) 0 = 1 := by
    have h := Work.Repel.deriv_rescale (MandelDim.pushdown d.E) (Work.Repel.s0 d) hs
    change deriv (fun ζ : ℂ => Work.Repel.s0 d * MandelDim.pushdown d.E
      (ζ / Work.Repel.s0 d)) 0 = 1
    rw [h, Work.Horn.MandelDim.deriv_pushdown_E d]
  have hder2 : deriv (deriv (Work.Repel.germ1 (Work.Repel.s0 d) d.E)) 0 = 2 := by
    have h := deriv_deriv_rescale (MandelDim.pushdown d.E) (Work.Repel.s0 d) hs
    change deriv (deriv (fun ζ : ℂ => Work.Repel.s0 d * MandelDim.pushdown d.E
      (ζ / Work.Repel.s0 d))) 0 = 2
    rw [h, Work.Repel.s0, div_div_eq_mul_div, mul_div_cancel_left₀ (b := (2 : ℂ)) hsecond]
  exact ⟨hOp, h0, hDiff, hfix, hder1, hder2⟩

/-- **The basin of the pushed-down horn map is open, forward invariant and backward
invariant.**  (`MandelDim.basin_basic` applied to `g = pushdown d.E`, using the open mapping
theorem at `0`, where `g'(0) = 1`; the preconnectedness of the domain is the only hypothesis that
is not already available.) -/
theorem pushdown_basin_basic {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hconn : IsPreconnected (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) :
    IsOpen (MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) ∧
      (∀ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))),
        MandelDim.pushdown d.E z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) ∧
      (∀ z ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
        MandelDim.pushdown d.E z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) →
        z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
          (insert 0 (MandelDim.piExp '' (Bu ∪ Bl)))) := by
  obtain ⟨hBuO, hBlO, -, -, -, -, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hDg : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) :=
    isOpen_insert_piExp hBuO hBlO hup hlo
  have hholo := pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have h0 : (0 : ℂ) ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := Set.mem_insert _ _
  have hne : deriv (MandelDim.pushdown d.E) 0 ≠ 0 := by
    rw [Work.Horn.MandelDim.deriv_pushdown_E d]
    norm_num
  exact MandelDim.basin_basic hDg hholo (MandelDim.basin_open_map hDg hconn hholo h0 hne)

/-- **The target follows from conjunct 1 and the basin clause.**  This lemma records the exact
remaining obligation: the first conjunct, and an immediate basin of the rescaled pushed-down germ
carrying exactly one critical point. -/
theorem horn_germ_F0_of_basinClause {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hsecond : deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0)
    (hbasin : ∃ B' : Set ℂ, MandelDim.IsImmediateBasin (Work.Repel.germ1 (Work.Repel.s0 d) d.E)
        (Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl)) B' ∧
      ∃! c : ℂ, c ∈ B' ∧ deriv (Work.Repel.germ1 (Work.Repel.s0 d) d.E) c = 0) :
    deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0 ∧
      MandelDim.InF0
        (fun ζ => (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2) *
          MandelDim.pushdown d.E (ζ / (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2)))
        ((fun ζ => (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2) * ζ) ''
          insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) := by
  have hBne : B.Nonempty := hB.2.1.1
  have hpg := isParabolicGerm_germ1 hF0 d hB hBne hBu hBl hsub hup hlo hsecond
  have hs : Work.Repel.s0 d = deriv (deriv (MandelDim.pushdown d.E)) 0 / 2 := rfl
  have hger : Work.Repel.germ1 (Work.Repel.s0 d) d.E
      = fun ζ => (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2) *
          MandelDim.pushdown d.E (ζ / (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2)) := by
    funext ζ
    rw [Work.Repel.germ1_apply, hs]
  have hdom : Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl)
      = (fun ζ => (deriv (deriv (MandelDim.pushdown d.E)) 0 / 2) * ζ) ''
          insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) := by
    rw [Work.Repel.Dgerm1, hs]
  rw [hger, hdom] at hpg hbasin
  exact ⟨hsecond, hpg, hbasin⟩

/-- **An analytic map that agrees with the identity near a point of a preconnected open set cannot
have a critical point in that set.**  The identity theorem propagates `g = id` from a neighbourhood
of `0` to the whole preconnected domain, where `deriv g = deriv id = 1` contradicts `deriv g = 0`.

This is the shape in which the `H ≡ 0` case of conjunct 1 is excluded: if the Écalle germ of
`g = pushdown d.E` vanished then `g =ᶠ[𝓝 0] id`, so the component of `0` of the horn domain would
carry no critical point of `g`. -/
theorem not_id_of_deriv_zero {g : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hconn : IsPreconnected D)
    (hg : DifferentiableOn ℂ g D) (hcrit : ∃ ζ ∈ D, deriv g ζ = 0)
    (hid : ∀ᶠ ζ in nhds (0 : ℂ), g ζ = ζ) (h0 : (0 : ℂ) ∈ D) : False := by
  obtain ⟨ζ, hζD, hζ0⟩ := hcrit
  have heq : Set.EqOn g id D :=
    (hg.analyticOnNhd hD).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_id hconn h0
      (by filter_upwards [hid] with z hz; simpa using hz)
  have hder := heq.deriv hD
  rw [hder hζD, deriv_id] at hζ0
  exact one_ne_zero hζ0

/-- **The germ of `g = pushdown d.E` at `0` is not the identity, provided `g` has a critical point
in the connected component of `0` of its horn domain.**

By `not_id_of_deriv_zero` it suffices that the horn domain of `g` is preconnected: then
`g =ᶠ[𝓝 0] id` would force `g = id` there and kill the critical point.  (What the paper's
Proposition 5.3 supplies is exactly such a critical point: the lifted horn map `Ẽ` is ramified over
`Φ₀ c`, so `g` is ramified over `v = π (Φ₀ c) ≠ 0`.) -/
theorem pushdown_not_id_of_critPoint {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hDg : IsOpen (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))))
    (hconn : IsPreconnected (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))))
    (hcrit : ∃ ζ ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      deriv (MandelDim.pushdown d.E) ζ = 0) :
    ¬ (∀ᶠ ζ in nhds (0 : ℂ), MandelDim.pushdown d.E ζ = ζ) :=
  fun hid => not_id_of_deriv_zero hDg hconn (pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo)
    hcrit hid (Set.mem_insert _ _)

/-- **The critical value of the pushed-down horn map, explicitly.**  Every critical point of
`g = pushdown d.E` inside `{0} ∪ π(Bu ∪ Bl)` (the only place where `g` is the horn map rather than
junk) has value `π (Φ₀ c)`, where `c` is the unique critical point of `f₀` in the immediate basin
`B`.  In particular this value is **nonzero** (`π` never vanishes), which is what a counting
argument against the critical values of `g` needs. -/
theorem pushdown_critval_global_eq {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {c : ℂ} (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    ∀ ζ ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)),
      deriv (MandelDim.pushdown d.E) ζ = 0 → MandelDim.pushdown d.E ζ = MandelDim.piExp (d.Φ c) := by
  obtain ⟨hBuO, hBlO, hBuT, hBlT, hup₀, hlo₀, -⟩ :=
    horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  have hBuE : Bu = MandelDim.BuOf d B := Bu_eq_BuOf d hBu hup hup₀
  have hBlE : Bl = MandelDim.BlOf d B := Bl_eq_BlOf d hBl hlo hlo₀
  have hcrit := Work.Horn.crit_of_parts Work.HornPhi.horn_phi Work.HornVarphi.horn_varphi
    f₀ D₀ B c d hsetup
  have hcrit' : ∀ w ∈ Bu ∪ Bl, deriv d.E w = 0 → ∃ k : ℤ, d.E w = d.Φ c + k := by
    intro w hw hz
    exact hcrit w (by rw [← hBuE, ← hBlE]; exact hw) hz
  have hholo := pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have hOpen := isOpen_insert_piExp hBuO hBlO hup hlo
  have hUO : IsOpen (Bu ∪ Bl) := hBuO.union hBlO
  have hdiffU : DifferentiableOn ℂ d.E (Bu ∪ Bl) := (Work.Horn.differentiableOn_E d).mono hsub
  have hT : MandelDim.IsTInvariant (Bu ∪ Bl) := fun u => by
    constructor
    · rintro (h | h)
      · exact Or.inl ((hBuT u).mp h)
      · exact Or.inr ((hBlT u).mp h)
    · rintro (h | h)
      · exact Or.inl ((hBuT u).mpr h)
      · exact Or.inr ((hBlT u).mpr h)
  have heq : ∀ u ∈ Bu ∪ Bl, d.E (u + 1) = d.E u + 1 :=
    fun u hu => Work.Horn.MandelDim.ParabData.E_add_one d (hsub hu) (hsub ((hT u).mp hu))
  have heq3 : ∀ u ∈ Bu ∪ Bl, u + 1 ∈ Bu ∪ Bl → d.E (u + 1) = d.E u + 1 :=
    fun u hu _ => heq u hu
  intro ζ hζ hd
  rcases Set.mem_insert_iff.mp hζ with rfl | hζ
  · exfalso
    rw [Work.Horn.MandelDim.deriv_pushdown_E d] at hd
    exact one_ne_zero hd
  · obtain ⟨w, hw, rfl⟩ := hζ
    have hEd : DifferentiableAt ℂ d.E w := (hdiffU w hw).differentiableAt (hUO.mem_nhds hw)
    have hmem : MandelDim.piExp w ∈ insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) :=
      Set.mem_insert_of_mem _ ⟨w, hw, rfl⟩
    have hgd : DifferentiableAt ℂ (MandelDim.pushdown d.E) (MandelDim.piExp w) :=
      (hholo (MandelDim.piExp w) hmem).differentiableAt (hOpen.mem_nhds hmem)
    have hz : deriv d.E w = 0 :=
      (Work.Horn.deriv_pushdown_zero hT hw (hUO.mem_nhds hw) heq hEd hgd).mp hd
    obtain ⟨k, hk⟩ := hcrit' w hw hz
    rw [Work.Horn.MandelDim.pushdown_piExp hT heq3 hw, hk,
      Work.Horn.MandelDim.piExp_add_intCast]

/-- **`HornData.inf_u` (infinite `π`-images of the fibres of `Ẽ` on `BuOf`) from the four
Proposition-5.3 statements.**

This is the *only* input of `Work.Horn.pushdown_germ_not_id`, hence the exclusion of the `H ≡ 0`
case of conjunct 1: as soon as `MandelDim.HornSCStatement` is proved (HornSC area, from
`BasinSCStatement` + `PlanarInterSCStatement`), this lemma instantiates it.  Nothing here is new
mathematics: it is the composition `Delta` -> `inf_from_parts`
(`Work.Horn.assembly`) `= inf_of_parts ∘ (varphi_image_BuOf, Phi_fiber_infinite_of_parts)`. -/
theorem inf_u_of_parts (hTopo : MandelDim.HornTopoStatement) (hPhi : MandelDim.HornPhiStatement)
    (hVarphi : MandelDim.HornVarphiStatement) (hSC : MandelDim.HornSCStatement)
    (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    ∀ y : ℂ, (MandelDim.piExp '' {w : ℂ | w ∈ MandelDim.BuOf d B ∧ d.E w = y}).Infinite :=
  (Work.Horn.inf_from_parts hTopo hPhi hVarphi hSC f₀ D₀ B c d hsetup).1

/-- **The Écalle germ `H` of `pushdown d.E` is not identically zero** (assuming the infinite-fibre
input of Proposition 5.3).  Indeed `H ≡ 0` near `0` would give `g =ᶠ[𝓝 0] id`, which
`Work.Horn.pushdown_germ_not_id` forbids. -/
theorem exists_germ_ne_zero_of_parts (hTopo : MandelDim.HornTopoStatement)
    (hPhi : MandelDim.HornPhiStatement) (hVarphi : MandelDim.HornVarphiStatement)
    (hSC : MandelDim.HornSCStatement) (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ)
    (d : MandelDim.ParabData f₀ D₀) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    ∀ H : ℂ → ℂ, H 0 = 0 → DifferentiableAt ℂ H 0 →
      (∀ᶠ ζ in nhds (0 : ℂ), MandelDim.pushdown d.E ζ = ζ * MandelDim.piExp (H ζ)) →
      ¬ (∀ᶠ ζ in nhds (0 : ℂ), H ζ = 0) := by
  intro H hH0 hHd hgerm hid
  refine Work.Horn.pushdown_germ_not_id hTopo f₀ D₀ B c d hsetup
    (inf_u_of_parts hTopo hPhi hVarphi hSC f₀ D₀ B c d hsetup) ?_
  filter_upwards [hgerm, hid] with ζ hg h0
  rw [hg, h0]
  simp [MandelDim.piExp]

/-! ## 20. The HORN-SC area is proved: unconditional `inf_u`, `¬ (g =ᶠ id)`, and the two
components of `D_g` -/

/-- **`MandelDim.HornSCStatement`, unconditionally** — the HORN-SC area (`Work.HornSC.horn_sc`) is
proved from `Work.HornTopo.horn_topo`, `Work.BasinSC.basin_sc` and `Work.PlanarSC.planar_inter_sc`
(all sorry-free).  This makes every statement that was conditional on it unconditional. -/
theorem hornSC : MandelDim.HornSCStatement :=
  Work.HornSC.horn_sc Work.HornTopo.horn_topo Work.BasinSC.basin_sc Work.PlanarSC.planar_inter_sc

/-- `HornData.inf_u` unconditionally (`Work.Horn.inf_u_of_parts` with `hornSC`). -/
theorem inf_u (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    ∀ y : ℂ, (MandelDim.piExp '' {w : ℂ | w ∈ MandelDim.BuOf d B ∧ d.E w = y}).Infinite :=
  inf_u_of_parts Work.HornTopo.horn_topo Work.HornPhi.horn_phi Work.HornVarphi.horn_varphi
    hornSC f₀ D₀ B c d hsetup

/-- **The `H ≡ 0` case of conjunct 1, unconditionally.**  The pushed-down horn map
`g = pushdown d.E` is never eventually the identity near `0`. -/
theorem pushdown_not_eventually_id {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (d : MandelDim.ParabData f₀ D₀) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    ¬ (∀ᶠ ζ in nhds (0 : ℂ), MandelDim.pushdown d.E ζ = ζ) :=
  Work.Horn.pushdown_germ_not_id Work.HornTopo.horn_topo f₀ D₀ B c d hsetup
    (inf_u f₀ D₀ B c d hsetup)

/-- `w ∈ D → w - k ∈ D` for a `T`-invariant `D` (backward direction of
`MandelDim.IsTInvariant.add_int`). -/
theorem IsTInvariant_sub_int {D : Set ℂ} (hD : MandelDim.IsTInvariant D) {w : ℂ} (hw : w ∈ D)
    (k : ℤ) : w - k ∈ D := by
  have h := MandelDim.IsTInvariant.add_int hD hw (-k)
  rw [Int.cast_neg] at h
  simpa [sub_eq_add_neg] using h

/-- **Conjunct 1 of `horn_germ_F0` from the four Proposition-5.3 statements and the
flat-germ exclusion.**  This records the exact remaining obligation of conjunct 1:

* the infinite-fibre input of Proposition 5.3 (`hTopo`, `hPhi`, `hVarphi`, `hSC`) supplies
  `¬ (g =ᶠ[𝓝 0] id)` (`pushdown_germ_not_id`), hence `H ≢ 0` for the Écalle germ `H`;
* `hflat` is the statement that the *non-identity* flat germ case cannot occur: if
  `g ζ = ζ · π (H ζ)` near `0` with `H` analytic at `0`, `H 0 = 0`, `H ≢ 0`, then
  `deriv H 0 ≠ 0`.

`hflat` is exactly what Shishikura's Lemma 5.2 argument provides (`flower_q` gives `q` petals when
`ζ ↦ ζ + a ζ^{q+1} + o`; `immediateBasin_has_critval_free` puts a critical value into every
immediate basin; `pushdown_critval_global_eq` says the only critical value of `g` in its horn
domain is `π (Φ₀ c) ≠ 0`, so two distinct immediate basins are impossible). -/
theorem second_deriv_ne_zero_of_flat_germ (hTopo : MandelDim.HornTopoStatement)
    (hPhi : MandelDim.HornPhiStatement) (hVarphi : MandelDim.HornVarphiStatement)
    (hSC : MandelDim.HornSCStatement) (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ)
    (d : MandelDim.ParabData f₀ D₀) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (hflat : ∀ H : ℂ → ℂ, H 0 = 0 → DifferentiableAt ℂ H 0 →
      (∀ᶠ ζ in nhds (0 : ℂ), MandelDim.pushdown d.E ζ = ζ * MandelDim.piExp (H ζ)) →
      ¬ (∀ᶠ ζ in nhds (0 : ℂ), H ζ = 0) → deriv H 0 ≠ 0) :
    deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0 := by
  obtain ⟨H, hH0, hHd, hgerm, hsec⟩ := Work.Horn.pushdown_germ f₀ D₀ d
  have hHne := exists_germ_ne_zero_of_parts hTopo hPhi hVarphi hSC f₀ D₀ B c d hsetup
    H hH0 hHd hgerm
  have hH' := hflat H hH0 hHd hgerm hHne
  intro hzero
  have h4 : (4 * (Real.pi : ℂ) * Complex.I) * deriv H 0 = 0 := by
    rw [← hsec, hzero]
  exact hH' ((mul_eq_zero.mp h4).resolve_left (by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]))

/-- **At most one immediate basin carries a critical value.**  If all critical values of `f` on `D`
coincide with one nonzero `v`, then two immediate basins (simply connected, `f` not injective on
them, so that by `Work.Horn.immediateBasin_has_critval_free` each contains a critical point whose
value - hence `v` - lies in it) must be equal: both contain `v`, and disjoint maximal preconnected
subsets of the basin containing a common point coincide.

This is the counting step in Shishikura's Lemma 5.2: `q ≥ 2` petals would produce two distinct
immediate basins, both of which would have to contain the single critical value. -/
theorem immediateBasin_unique_of_single_critval {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hf : DifferentiableOn ℂ f D)
    (hcrit : ∃ v : ℂ, v ≠ 0 ∧ ∀ z ∈ D, deriv f z = 0 → f z = v)
    {B B' : Set ℂ} (hB : MandelDim.IsImmediateBasin f D B) (hB' : MandelDim.IsImmediateBasin f D B')
    (hscB : SimplyConnectedSpace B) (hscB' : SimplyConnectedSpace B')
    (hniB : ¬ Set.InjOn f B) (hniB' : ¬ Set.InjOn f B') : B = B' := by
  obtain ⟨v, -, hv⟩ := hcrit
  obtain ⟨z, hzD, hzB, hz0⟩ := Work.Horn.immediateBasin_has_critval_free hD hf hB hscB hniB
  obtain ⟨z', hz'D, hz'B', hz'0⟩ := Work.Horn.immediateBasin_has_critval_free hD hf hB' hscB' hniB'
  have hvB : v ∈ B := by rw [← hv z hzD hz0]; exact hzB
  have hvB' : v ∈ B' := by rw [← hv z' hz'D hz'0]; exact hz'B'
  exact le_antisymm
    (hB'.2.2.2.1 B hB.2.1.isPreconnected hB.2.2.1 ⟨v, hvB', hvB⟩)
    (hB.2.2.2.1 B' hB'.2.1.isPreconnected hB'.2.2.1 ⟨v, hvB, hvB'⟩)

/-- Specialisation of `immediateBasin_unique_of_single_critval` to `g = pushdown d.E` on its horn
domain `insert 0 (π '' (Bu ∪ Bl))`, using `pushdown_critval_global_eq`: all critical values of `g`
there are the single `π (Φ₀ c) ≠ 0`. -/
theorem pushdown_immediateBasin_unique {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {c : ℂ} (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    {B₁ B₂ : Set ℂ}
    (h₁ : MandelDim.IsImmediateBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) B₁)
    (h₂ : MandelDim.IsImmediateBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) B₂)
    (hsc₁ : SimplyConnectedSpace B₁) (hsc₂ : SimplyConnectedSpace B₂)
    (hni₁ : ¬ Set.InjOn (MandelDim.pushdown d.E) B₁)
    (hni₂ : ¬ Set.InjOn (MandelDim.pushdown d.E) B₂) : B₁ = B₂ := by
  obtain ⟨hBuO, hBlO, -, -, -, -, -⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  refine immediateBasin_unique_of_single_critval (isOpen_insert_piExp hBuO hBlO hup hlo)
    (pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo) ?_ h₁ h₂ hsc₁ hsc₂ hni₁ hni₂
  refine ⟨MandelDim.piExp (d.Φ c), (by unfold MandelDim.piExp; exact Complex.exp_ne_zero _), ?_⟩
  intro z hz hz0
  exact pushdown_critval_global_eq hF0 d hB hBne hsetup hBu hBl hsub hup hlo z hz hz0

/-- **The counting step of conjunct 1** (Shishikura's Lemma 5.2, `q = 1` case).

If finitely many pairwise disjoint immediate basins of `g` on `D` are each simply connected and
non-injective, and *all* critical values of `g` in `D` coincide with a single `v`, then there is at
most one of them: each basin carries a critical point
(`Work.Horn.immediateBasin_has_critval_free`), hence contains its value `v`, so disjointness
leaves room for only one basin.

Applied with `B := B'` the spreads of `Work.Horn.petal_spread_component`/`flower_q` and with
`hcritval` from `Work.Horn.pushdown_critval_global_eq` (`v = π (d.Φ c) ≠ 0`, the unique critical
value of `pushdown d.E` on `D_g`), this is what turns `q ≥ 2` into a contradiction, i.e. what
proves `hflat` (see `NOTES_GERM_F0.md` §§32f, 36–39). -/
theorem subsingleton_of_spreads {g : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {v : ℂ} {B : Fin q → Set ℂ}
    (hD : IsOpen D) (hg : DifferentiableOn ℂ g D)
    (hcritval : ∀ z ∈ D, deriv g z = 0 → g z = v)
    (hB : ∀ i, MandelDim.IsImmediateBasin g D (B i))
    (hsc : ∀ i, SimplyConnectedSpace (B i)) (hni : ∀ i, ¬ Set.InjOn g (B i))
    (hdisj : ∀ i j : Fin q, i ≠ j → Disjoint (B i) (B j)) :
    Subsingleton (Fin q) := by
  have hv : ∀ i : Fin q, v ∈ B i := by
    intro i
    obtain ⟨z, hzD, hzB, hz0⟩ :=
      Work.Horn.immediateBasin_has_critval_free hD hg (hB i) (hsc i) (hni i)
    rw [← hcritval z hzD hz0]
    exact hzB
  refine ⟨fun i j => ?_⟩
  by_contra hij
  exact (Set.disjoint_left.mp (hdisj i j hij)) (hv i) (hv j)

/-- **`q = 1`.**  Under the hypotheses of `subsingleton_of_spreads`, `q` petals with `1 ≤ q` force
`q = 1` (this is the `q = 1` case of Shishikura's Lemma 5.2, and is exactly the statement that the
pushed-down horn map has `g''(0) ≠ 0`). -/
theorem eq_one_of_spreads {g : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {v : ℂ} {B : Fin q → Set ℂ}
    (hD : IsOpen D) (hg : DifferentiableOn ℂ g D)
    (hcritval : ∀ z ∈ D, deriv g z = 0 → g z = v)
    (hB : ∀ i, MandelDim.IsImmediateBasin g D (B i))
    (hsc : ∀ i, SimplyConnectedSpace (B i)) (hni : ∀ i, ¬ Set.InjOn g (B i))
    (hdisj : ∀ i j : Fin q, i ≠ j → Disjoint (B i) (B j)) (hq : 1 ≤ q) :
    q = 1 := by
  have hss : Subsingleton (Fin q) :=
    subsingleton_of_spreads hD hg hcritval hB hsc hni hdisj
  have hle : q ≤ 1 := by
    have h := Fintype.card_le_one_iff_subsingleton.mpr hss
    simpa using h
  omega

/-- **The `∃!` clause of the target's second conjunct** (Shishikura's "the immediate basin contains
exactly one critical point"): an immediate basin of the rescaled horn map
`germ1 (s₀ d) E` which is simply connected and carries a critical point has exactly one, because all
its critical values coincide (`Work.Horn.pushdown_critval_global_eq`, transported by
`Work.Horn.deriv_rescale_eq`). -/
theorem existsUnique_critPoint_germ1 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {c : ℂ} (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hsecond : deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0) {B' : Set ℂ}
    (hB' : MandelDim.IsImmediateBasin (Work.Repel.germ1 (Work.Repel.s0 d) d.E)
      (Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl)) B')
    (hB'sc : SimplyConnectedSpace B')
    (hcrit : ∃ z ∈ B', deriv (Work.Repel.germ1 (Work.Repel.s0 d) d.E) z = 0) :
    ∃! c' : ℂ, c' ∈ B' ∧ deriv (Work.Repel.germ1 (Work.Repel.s0 d) d.E) c' = 0 := by
  obtain ⟨-, -, hDgDiff, -, -, -⟩ :=
    isParabolicGerm_germ1 hF0 d hB hBne hBu hBl hsub hup hlo hsecond
  have hs : Work.Repel.s0 d ≠ 0 := by
    rw [Work.Repel.s0]
    exact div_ne_zero hsecond (by norm_num)
  have hsub' : B' ⊆ Work.Repel.Dgerm1 (Work.Repel.s0 d) (Bu ∪ Bl) :=
    subset_domain_of_immediateBasin hB'
  refine unique_critPoint_of_single_critVal hB'.1 hB'.2.1 hB'sc (hDgDiff.mono hsub')
    hB'.2.2.2.2.1 hB'.2.2.2.2.2.1 hB'.2.2.2.2.2.2 ?_ hcrit
  refine ⟨Work.Repel.s0 d * MandelDim.piExp (d.Φ c), ?_⟩
  intro z hz hzd
  obtain ⟨ζ, hζ, rfl⟩ := hsub' hz
  have hder : deriv (Work.Repel.germ1 (Work.Repel.s0 d) d.E) (Work.Repel.s0 d * ζ)
      = deriv (MandelDim.pushdown d.E) ζ := by
    change deriv (fun w : ℂ => Work.Repel.s0 d * MandelDim.pushdown d.E
      (w / Work.Repel.s0 d)) (Work.Repel.s0 d * ζ) = deriv (MandelDim.pushdown d.E) ζ
    rw [deriv_rescale_eq (MandelDim.pushdown d.E) (Work.Repel.s0 d) hs]
    simp only [mul_div_cancel_left₀ ζ hs]
  rw [hder] at hzd
  rw [Work.Repel.germ1_apply, mul_div_cancel_left₀ ζ hs]
  exact congrArg (fun w => Work.Repel.s0 d * w)
    (pushdown_critval_global_eq hF0 d hB hBne hsetup hBu hBl hsub hup hlo ζ hζ hzd)


end Work.Horn

namespace Work.Horn

/-- **Spread datum (conjunct 1).**  For the ACTUAL Leau–Fatou expansion `g z = z + a z^(q+1) +
o(z^(q+1))` of `g = pushdown d.E` there are `q` pairwise disjoint `g`-invariant subsets of
`D_g = {0} ∪ π(Bu ∪ Bl)`, each containing a critical point of `g`.

This is deliberately WEAK: no properness, no simple connectivity and no injectivity — so
`Work.Horn.eq_one_of_invariant_disjoint` converts it into `q ≤ 1`, hence (with the flat germ
expansion) into `g''(0) ≠ 0`.  It is the `V^{(i)}_n`-chain content of Shishikura's Lemma 5.4
reduced to its counting-relevant part; unlike a `∀ q`-version it is not refutable (see
`NOTES_GERM_F0.md` §69). -/
def SpreadDatum {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (η : ℝ)
    (Bu Bl : Set ℂ) : Prop :=
  ∃ (q : ℕ) (a : ℂ), 1 ≤ q ∧ a ≠ 0 ∧
    Filter.Tendsto (fun z : ℂ => (MandelDim.pushdown d.E z - z - a * z ^ (q + 1))
        / z ^ (q + 1)) (nhdsWithin 0 {0}ᶜ) (nhds 0) ∧
    ∃ B' : Fin q → Set ℂ,
      (∀ i, B' i ⊆ insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) ∧
      (∀ i, Set.MapsTo (MandelDim.pushdown d.E) (B' i) (B' i)) ∧
      (∀ i, ∃ z ∈ B' i, deriv (MandelDim.pushdown d.E) z = 0) ∧
      (∀ i j : Fin q, i ≠ j → Disjoint (B' i) (B' j))

/-- **Basin datum (conjunct 2).**  An immediate parabolic basin of `g = pushdown d.E` on
`D_g = {0} ∪ π(Bu ∪ Bl)` that is simply connected and contains a critical point of `g`.

After the scaling `ζ ↦ s₀ d · ζ` this is exactly what `Work.Horn.existsUnique_critPoint_germ1`
turns into the `∃!` clause of `MandelDim.InF0` of the rescaled horn map. -/
def BasinDatum {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (η : ℝ)
    (Bu Bl : Set ℂ) : Prop :=
  ∃ B' : Set ℂ,
    MandelDim.IsImmediateBasin (MandelDim.pushdown d.E) (insert 0 (MandelDim.piExp '' (Bu ∪ Bl))) B' ∧
    SimplyConnectedSpace B' ∧ ∃ z ∈ B', deriv (MandelDim.pushdown d.E) z = 0

end Work.Horn
