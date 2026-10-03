import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.HornVarphi.exists_ball_subset_diff_critOrbit
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.isPreconnected_compl_closedDiscrete

/-!
# `φ₀` maps each of the components `B̃ᵘ`, `B̃ˡ` onto `B` off the forward critical orbit

(`Work.Horn.varphi_image_BuOf`, Shishikura Prop. 5.3, the "`surj`" half of the assembly.)

For `f₀ ∈ 𝓕₀` with immediate basin `B`, unique critical point `c ∈ B`, §4.1 data `d`, put
`P⁺ = critOrbit f₀ c = {f₀^k c | k ≥ 1}` (the forward critical orbit) and let `B̃ᵘ = BuOf d B`,
`B̃ˡ = BlOf d B` be the two components of `Btil d B = φ₀⁻¹(B) ∩ Dφ` through `±i(η₀+1)`.

Claim B (`HornVarphiStatement`) supplies holomorphic local sections of `φ₀` over small discs in
`B ∖ P⁺`, *through any prescribed point of `B̃ᵘ ∪ B̃ˡ` over that disc*.  Since such a section's image
is preconnected, contained in `Btil d B` and meets the component `Q` in question, it lies in `Q`
(`IsPreconnected.subset_connectedComponentIn` + `connectedComponentIn_eq`).  Hence
`φ₀ '' Q ∩ (B ∖ P⁺)` is clopen in `B ∖ P⁺`; as `B ∖ P⁺` is preconnected (the critical orbit
accumulates only at `0 ∉ B`, so it is closed and discrete in `B`) it suffices to know one point:
if `φ₀ '' Q ⊆ P⁺` then `φ₀ '' Q` would be a singleton (`P⁺` is pointwise isolated), say
`{φ₀ w}`, and `T`-invariance `w + 1 ∈ Q` together with the Abel equation would make `φ₀ w ∈ B` a
fixed point of `f₀` — impossible because `0` is the only fixed point of the basin and `0 ∉ B`.
-/

namespace Work.Horn

open Filter Topology Metric
open scoped Topology Manifold

noncomputable section

/-! ## Two elementary metric lemmas about convergent sequences -/

/-- For a sequence `u` and a point `y`, the finitely many terms `u k` (`k < K`) that differ from
`y` are at a positive distance from `y`. -/
private lemma exists_pos_le_dist_of_ne_of_lt {y : ℂ} {u : ℕ → ℂ} :
    ∀ K : ℕ, ∃ d : ℝ, 0 < d ∧ ∀ k : ℕ, k < K → u k ≠ y → d ≤ ‖u k - y‖ := by
  intro K
  induction K with
  | zero => exact ⟨1, one_pos, fun k hk _ => absurd hk (Nat.not_lt_zero k)⟩
  | succ K ih =>
      obtain ⟨d, hd, hle⟩ := ih
      by_cases h : u K = y
      · refine ⟨d, hd, fun k hk hne => hle k ?_ hne⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
        · exact hlt
        · exact absurd (heq ▸ h) hne
      · have hpos : 0 < ‖u K - y‖ := by
          rw [norm_pos_iff, sub_ne_zero]
          exact h
        refine ⟨min d ‖u K - y‖, lt_min hd hpos, fun k hk hne => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
        · exact le_trans (min_le_left _ _) (hle k hlt hne)
        · subst heq
          exact min_le_right _ _

/-- If `u k → L` and `y = u j ≠ L`, then a ball around `y` meets `range u` only in `y`. -/
private lemma exists_ball_range_subset_singleton {u : ℕ → ℂ} {L y : ℂ}
    (hu : Tendsto u atTop (𝓝 L)) (hy : y ≠ L) {j : ℕ} (hj : u j = y) :
    ∃ U : Set ℂ, IsOpen U ∧ y ∈ U ∧ ∀ z ∈ U, z ∈ Set.range u → z = y := by
  have hL : 0 < ‖y - L‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hu (‖y - L‖ / 2) (by linarith)
  obtain ⟨d, hd, hle⟩ := exists_pos_le_dist_of_ne_of_lt (y := y) (u := u) K
  refine ⟨Metric.ball y (min d (‖y - L‖ / 2)), Metric.isOpen_ball,
    Metric.mem_ball_self (lt_min hd (by linarith)), ?_⟩
  rintro z hz ⟨k, hk⟩
  subst hk
  by_cases hky : u k = y
  · exact hky
  · rcases lt_or_ge k K with hkK | hkK
    · have h1 : d ≤ ‖u k - y‖ := hle k hkK hky
      have h2 : ‖u k - y‖ < min d (‖y - L‖ / 2) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      have h3 : min d (‖y - L‖ / 2) ≤ d := min_le_left _ _
      linarith
    · have htail : ‖u k - L‖ < ‖y - L‖ / 2 := by
        simpa [dist_eq_norm] using hK k hkK
      have hlow : ‖y - L‖ / 2 < ‖u k - y‖ := by
        have h2 : ‖y - L‖ ≤ ‖y - u k‖ + ‖u k - L‖ := by
          have h3 := norm_add_le (y - u k) (u k - L)
          rwa [show y - u k + (u k - L) = y - L by ring] at h3
        rw [norm_sub_rev y (u k)] at h2
        linarith
      have hz' : ‖u k - y‖ < min d (‖y - L‖ / 2) := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      have h4 : min d (‖y - L‖ / 2) ≤ ‖y - L‖ / 2 := min_le_right _ _
      linarith

/-! ## Discreteness of the forward critical orbit -/

/-- **Every point of the forward critical orbit is isolated in it.**
`P⁺ = critOrbit f₀ c = {f₀^k c | k ≥ 1}`. -/
theorem critOrbit_pointwise_discrete {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    ∀ p ∈ MandelDim.critOrbit f₀ c, ∃ U : Set ℂ, IsOpen U ∧ p ∈ U ∧
      ∀ z ∈ MandelDim.critOrbit f₀ c, z ∈ U → z = p := by
  obtain ⟨hDopen, h0D, hfdiff, hf0, hdf, -⟩ := hsetup.1
  obtain ⟨-, -, hBsub, -, hmaps, -, -⟩ := hsetup.2.1
  have hcB : c ∈ B := hsetup.2.2.1
  have h0B : (0 : ℂ) ∉ B := fun h =>
    Work.Horn.BasinAux.zero_not_mem hDopen h0D hfdiff hf0 hdf (hBsub h)
  have hconv : Tendsto (fun k : ℕ => f₀^[k] c) atTop (𝓝 0) :=
    Work.Horn.BasinAux.tendsto_zero (hBsub hcB)
  have hshift : Tendsto (fun k : ℕ => f₀^[k+1] c) atTop (𝓝 0) :=
    hconv.comp (tendsto_add_atTop_nat 1)
  intro p hp
  obtain ⟨j, hj1, hpj⟩ := hp
  have hpB : p ∈ B := by
    rw [hpj]
    exact hmaps.iterate j hcB
  have hp0 : p ≠ 0 := fun h => h0B (h ▸ hpB)
  have hjrange : (fun k : ℕ => f₀^[k+1] c) (j - 1) = p := by
    show f₀^[(j - 1) + 1] c = p
    rw [Nat.sub_add_cancel hj1]
    exact hpj.symm
  obtain ⟨U, hUo, hpU, hU⟩ := exists_ball_range_subset_singleton hshift hp0 hjrange
  refine ⟨U, hUo, hpU, fun z hz hzU => hU z hzU ?_⟩
  obtain ⟨k, hk1, hzk⟩ := hz
  exact ⟨k - 1, by show f₀^[(k - 1) + 1] c = z; rw [Nat.sub_add_cancel hk1]; exact hzk.symm⟩

/-! ## Two topological gluing lemmas -/

/-- **A preconnected subset of a pointwise-isolated set is a single point.** -/
theorem preconnected_subset_singleton_of_pointwise_discrete {S T : Set ℂ}
    (hS : IsPreconnected S) (hST : S ⊆ T)
    (hT : ∀ x ∈ T, ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧ ∀ z ∈ T, z ∈ U → z = x)
    {x : ℂ} (hx : x ∈ S) : S ⊆ {x} := by
  intro z hzS
  by_contra hzx
  obtain ⟨U, hUo, hxU, hUT⟩ := hT x (hST hx)
  have hsub : S ⊆ U ∪ {x}ᶜ := by
    intro w hwS
    by_cases hwU : w ∈ U
    · exact Or.inl hwU
    · refine Or.inr ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun hwx => hwU (hwx ▸ hxU)
  have hneU : (S ∩ U).Nonempty := ⟨x, hx, hxU⟩
  have hneC : (S ∩ {x}ᶜ).Nonempty := ⟨z, hzS, by simpa using hzx⟩
  obtain ⟨w, hwS, hwU, hwx⟩ := hS U {x}ᶜ hUo isOpen_compl_singleton hsub hneU hneC
  exact hwx (hUT w (hST hwS) hwU)

/-- **A preconnected set on which a property is locally constant is contained in any of its
non-empty level sets.**  `Q` is the level set; the local constancy hypothesis is that around every
point of `s` there is a ball inside `s` that is either contained in `Q` or disjoint from it. -/
theorem preconnected_subset_of_locally_const {s Q : Set ℂ} (hs : IsPreconnected s)
    (hloc : ∀ y ∈ s, ∃ r : ℝ, 0 < r ∧ Metric.ball y r ⊆ s ∧
      (Metric.ball y r ⊆ Q ∨ Disjoint (Metric.ball y r) Q))
    (hne : (s ∩ Q).Nonempty) : s ⊆ Q := by
  obtain ⟨x, hxs, hxQ⟩ := hne
  set u : Set ℂ := {z | ∃ y ∈ s, ∃ r : ℝ, 0 < r ∧ Metric.ball y r ⊆ s ∧
      Metric.ball y r ⊆ Q ∧ z ∈ Metric.ball y r} with hu
  set v : Set ℂ := {z | ∃ y ∈ s, ∃ r : ℝ, 0 < r ∧ Metric.ball y r ⊆ s ∧
      Disjoint (Metric.ball y r) Q ∧ z ∈ Metric.ball y r} with hv
  have huopen : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨y, hys, r, hr, hbs, hbQ, hz⟩
    exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz)
      (fun w hw => ⟨y, hys, r, hr, hbs, hbQ, hw⟩)
  have hvopen : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨y, hys, r, hr, hbs, hbv, hz⟩
    exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz)
      (fun w hw => ⟨y, hys, r, hr, hbs, hbv, hw⟩)
  have huv : Disjoint u v := by
    rw [Set.disjoint_left]
    rintro z ⟨y₁, -, r₁, -, -, hb₁, hz₁⟩ ⟨y₂, -, r₂, -, -, hb₂, hz₂⟩
    exact (Set.disjoint_left.mp hb₂ hz₂) (hb₁ hz₁)
  have hsub : s ⊆ u ∪ v := by
    intro y hys
    obtain ⟨r, hr, hbs, hcase⟩ := hloc y hys
    rcases hcase with h | h
    · exact Or.inl ⟨y, hys, r, hr, hbs, h, Metric.mem_ball_self hr⟩
    · exact Or.inr ⟨y, hys, r, hr, hbs, h, Metric.mem_ball_self hr⟩
  have hune : (s ∩ u).Nonempty := by
    obtain ⟨r, hr, hbs, hcase⟩ := hloc x hxs
    rcases hcase with h | h
    · exact ⟨x, hxs, x, hxs, r, hr, hbs, h, Metric.mem_ball_self hr⟩
    · exact ((Set.disjoint_left.mp h (Metric.mem_ball_self hr)) hxQ).elim
  have hsu : s ⊆ u := hs.subset_left_of_subset_union huopen hvopen huv hsub hune
  intro z hzs
  obtain ⟨y, -, r, -, -, hbQ, hz⟩ := hsu hzs
  exact hbQ hz

/-! ## `B ∖ P⁺` is preconnected -/

/-- **`B ∖ P⁺` is preconnected** (`B` the immediate basin of `f₀ ∈ 𝓕₀`, `P⁺ = critOrbit f₀ c`).
`P⁺` accumulates only at `0 ∉ B`, so it is closed and discrete in `B`; removing a closed discrete
set from the complex one-manifold `B` leaves a preconnected set
(`Work.SimplyConnected.ABS.isPreconnected_compl_closedDiscrete`). -/
theorem isPreconnected_compl_critOrbit {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    IsPreconnected (B \ MandelDim.critOrbit f₀ c) := by
  obtain ⟨hDopen, h0D, hfdiff, hf0, hdf, -⟩ := hsetup.1
  obtain ⟨hBopen, hBconn, hBsub, -, -, -, -⟩ := hsetup.2.1
  haveI : ConnectedSpace ↥(⟨B, hBopen⟩ : TopologicalSpace.Opens ℂ) :=
    isConnected_iff_connectedSpace.mp hBconn
  have hKc : IsClosed {z : B | (z : ℂ) ∈ MandelDim.critOrbit f₀ c} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    rintro ⟨z, hzB⟩ hzK
    have hzK' : z ∉ MandelDim.critOrbit f₀ c := hzK
    obtain ⟨R, hRpos, hRsub, hRcrit⟩ :=
      Work.HornVarphi.exists_ball_subset_diff_critOrbit hsetup hzB hzK'
    refine Filter.mem_of_superset
      ((Metric.isOpen_ball.preimage continuous_subtype_val).mem_nhds
        (Metric.mem_ball_self hRpos)) ?_
    intro w hw
    simp only [Set.mem_preimage] at hw
    exact hRcrit w hw
  have hKd : ∀ x ∈ {z : B | (z : ℂ) ∈ MandelDim.critOrbit f₀ c},
      ∃ U : Set B, IsOpen U ∧ x ∈ U ∧
        U ∩ {z : B | (z : ℂ) ∈ MandelDim.critOrbit f₀ c} = {x} := by
    rintro ⟨x, hxB⟩ hxK
    have hxK' : x ∈ MandelDim.critOrbit f₀ c := hxK
    obtain ⟨U, hUo, hxU, hUis⟩ := critOrbit_pointwise_discrete hsetup x hxK'
    refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hxU, ?_⟩
    ext y
    constructor
    · rintro ⟨hyU, hyK⟩
      exact Subtype.ext (hUis y hyK hyU)
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      obtain rfl : y = ⟨x, hxB⟩ := hy
      exact ⟨hxU, hxK⟩
  have hpc : IsPreconnected
      ({z : B | (z : ℂ) ∈ MandelDim.critOrbit f₀ c}ᶜ : Set B) :=
    Work.SimplyConnected.ABS.isPreconnected_compl_closedDiscrete
      (X := ↥(⟨B, hBopen⟩ : TopologicalSpace.Opens ℂ)) hKc hKd
  have himg : (Subtype.val : B → ℂ)
      '' ({z : B | (z : ℂ) ∈ MandelDim.critOrbit f₀ c}ᶜ : Set B)
      = B \ MandelDim.critOrbit f₀ c := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, by simpa using hw⟩
    · rintro ⟨hzB, hzP⟩
      exact ⟨⟨z, hzB⟩, by simpa using hzP, rfl⟩
  rw [← himg]
  exact hpc.image (Subtype.val : B → ℂ) continuous_subtype_val.continuousOn

/-! ## The main component argument -/

/-- **`φ₀` maps a component `Q` of `Btil d B` onto `B ∖ P⁺`**, given that `Q` is a union of
connected components of `Btil d B` (`hQcomp`), that `Q ⊆ B̃ᵘ ∪ B̃ˡ` and that `Q` is `T`-invariant. -/
theorem image_subset_of_component_image {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (hVarphi : MandelDim.HornVarphiStatement) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (d : MandelDim.ParabData f₀ D₀) {Q : Set ℂ}
    (hQcomp : ∀ u ∈ Q, connectedComponentIn (MandelDim.Btil d B) u = Q)
    (hQne : Q.Nonempty) (hQT : MandelDim.IsTInvariant Q)
    (hQBu : Q ⊆ MandelDim.BuOf d B ∪ MandelDim.BlOf d B) :
    B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' Q := by
  obtain ⟨hDopen, h0D, hfdiff, hf0, hdf, -⟩ := hsetup.1
  obtain ⟨-, -, hBsub, -, -, -, -⟩ := hsetup.2.1
  have h0B : (0 : ℂ) ∉ B := fun h =>
    Work.Horn.BasinAux.zero_not_mem hDopen h0D hfdiff hf0 hdf (hBsub h)
  have hQsub : Q ⊆ MandelDim.Btil d B := by
    obtain ⟨u, hu⟩ := hQne
    rw [← hQcomp u hu]
    exact connectedComponentIn_subset _ _
  have hQpre : IsPreconnected Q := by
    obtain ⟨u, hu⟩ := hQne
    rw [← hQcomp u hu]
    exact isPreconnected_connectedComponentIn
  have hQDφ : ∀ u ∈ Q, u ∈ d.Dφ := fun u hu => (hQsub hu).1
  have hQφB : ∀ u ∈ Q, d.φ u ∈ B := fun u hu => (hQsub hu).2
  have hφcontQ : ContinuousOn d.φ Q := d.φ_holo.continuousOn.mono hQDφ
  -- ## step 1: some point of `B ∖ P⁺` is in `φ '' Q`
  have hne : ((B \ MandelDim.critOrbit f₀ c) ∩ (d.φ '' Q)).Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsubP : d.φ '' Q ⊆ MandelDim.critOrbit f₀ c := by
      rintro z ⟨u, hu, rfl⟩
      by_contra hzP
      exact (Set.eq_empty_iff_forall_notMem.mp hcon) (d.φ u) ⟨⟨hQφB u hu, hzP⟩, u, hu, rfl⟩
    obtain ⟨u₀, hu₀⟩ := hQne
    have hsingle : d.φ '' Q ⊆ {d.φ u₀} :=
      preconnected_subset_singleton_of_pointwise_discrete (hQpre.image d.φ hφcontQ) hsubP
        (critOrbit_pointwise_discrete hsetup) ⟨u₀, hu₀, rfl⟩
    have hu₀1 : u₀ + 1 ∈ Q := (hQT u₀).mp hu₀
    have hfix : f₀ (d.φ u₀) = d.φ u₀ := by
      have h1 : d.φ (u₀ + 1) = d.φ u₀ := hsingle ⟨u₀ + 1, hu₀1, rfl⟩
      rw [d.φ_abel u₀ (hQDφ u₀ hu₀) (hQDφ (u₀ + 1) hu₀1)] at h1
      exact h1
    have hyB : d.φ u₀ ∈ B := hQφB u₀ hu₀
    have hconst : Tendsto (fun n : ℕ => (f₀^[n]) (d.φ u₀)) atTop (𝓝 0) :=
      Work.Horn.BasinAux.tendsto_zero (hBsub hyB)
    have hiter : ∀ n : ℕ, (f₀^[n]) (d.φ u₀) = d.φ u₀ := by
      intro n
      induction n with
      | zero => simp
      | succ m ih => rw [Function.iterate_succ_apply', ih, hfix]
    have h2 : Tendsto (fun n : ℕ => (f₀^[n]) (d.φ u₀)) atTop (𝓝 (d.φ u₀)) := by
      rw [show (fun n : ℕ => (f₀^[n]) (d.φ u₀)) = fun _ => d.φ u₀ from funext hiter]
      exact tendsto_const_nhds
    have hzero : d.φ u₀ = 0 := tendsto_nhds_unique h2 hconst
    exact h0B (hzero ▸ hyB)
  -- ## step 2: local constancy of `· ∈ φ '' Q` on `B ∖ P⁺`
  have hloc : ∀ y ∈ B \ MandelDim.critOrbit f₀ c, ∃ r : ℝ, 0 < r ∧
      Metric.ball y r ⊆ B \ MandelDim.critOrbit f₀ c ∧
      (Metric.ball y r ⊆ d.φ '' Q ∨ Disjoint (Metric.ball y r) (d.φ '' Q)) := by
    intro y hy
    obtain ⟨hyB, hyP⟩ := hy
    obtain ⟨R, hRpos, hRsub, hRcrit⟩ :=
      Work.HornVarphi.exists_ball_subset_diff_critOrbit hsetup hyB hyP
    obtain ⟨r₀, hr₀pos, -, hsec⟩ := hVarphi f₀ D₀ B c d hsetup y hyB hyP
    set r : ℝ := min R r₀ with hrdef
    have hrpos : 0 < r := lt_min hRpos hr₀pos
    have hrR : r ≤ R := min_le_left _ _
    have hr₀ : r ≤ r₀ := min_le_right _ _
    refine ⟨r, hrpos, ?_, ?_⟩
    · intro z hz
      have hzR : z ∈ Metric.ball y R := Metric.ball_subset_ball hrR hz
      exact ⟨hRsub hzR, hRcrit z hzR⟩
    · by_cases hnon : (Metric.ball y r ∩ d.φ '' Q).Nonempty
      · left
        obtain ⟨z, hzball, hzim⟩ := hnon
        obtain ⟨u, huQ, huφ⟩ := hzim
        have hzu : d.φ u ∈ Metric.ball y r := by rw [huφ]; exact hzball
        obtain ⟨σ, hσdiff, hσmaps, hσid, hσval⟩ :=
          hsec u (hQBu huQ) (Metric.ball_subset_ball hr₀ hzu)
        have hσpre : IsPreconnected (σ '' Metric.ball y r₀) :=
          isPreconnected_ball.image σ hσdiff.continuousOn
        have hσsub : σ '' Metric.ball y r₀ ⊆ MandelDim.Btil d B := by
          rintro w ⟨s, hs, rfl⟩
          rcases hσmaps hs with h | h
          · exact connectedComponentIn_subset _ _ h
          · exact connectedComponentIn_subset _ _ h
        have hmem : u ∈ σ '' Metric.ball y r₀ :=
          ⟨d.φ u, Metric.ball_subset_ball hr₀ hzu, hσval⟩
        have hcomp : σ '' Metric.ball y r₀ ⊆
            connectedComponentIn (MandelDim.Btil d B) u :=
          hσpre.subset_connectedComponentIn hmem hσsub
        intro z hz
        refine ⟨σ z, ?_, ?_⟩
        · rw [← hQcomp u huQ]
          exact hcomp ⟨z, Metric.ball_subset_ball hr₀ hz, rfl⟩
        · exact hσid z (Metric.ball_subset_ball hr₀ hz)
      · right
        rw [Set.not_nonempty_iff_eq_empty] at hnon
        exact Set.disjoint_iff_inter_eq_empty.mpr hnon
  exact preconnected_subset_of_locally_const (isPreconnected_compl_critOrbit hsetup) hloc hne

/-! ## The target -/

theorem varphi_image_BuOf (hTopo : MandelDim.HornTopoStatement)
    (hVarphi : MandelDim.HornVarphiStatement) (hSC : MandelDim.HornSCStatement)
    (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' MandelDim.BuOf d B ∧
      B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' MandelDim.BlOf d B := by
  obtain ⟨-, -, hBuT, hBlT, hhalfU, hhalfL, -⟩ := hTopo f₀ D₀ B c d hsetup
  have hwU : (Complex.I * ((d.η₀ + 1 : ℝ) : ℂ)) ∈ MandelDim.BuOf d B := by
    refine hhalfU ?_
    have h : (Complex.I * ((d.η₀ + 1 : ℝ) : ℂ)).im = d.η₀ + 1 := by
      rw [Complex.mul_im]; simp
    simp only [Set.mem_setOf_eq, h]
    linarith
  have hwL : -(Complex.I * ((d.η₀ + 1 : ℝ) : ℂ)) ∈ MandelDim.BlOf d B := by
    have heq : -(Complex.I * ((d.η₀ + 1 : ℝ) : ℂ))
        = Complex.I * ((-(d.η₀ + 1) : ℝ) : ℂ) := by push_cast; ring
    rw [heq]
    refine hhalfL ?_
    have h : (Complex.I * ((-(d.η₀ + 1) : ℝ) : ℂ)).im = -(d.η₀ + 1) := by
      rw [Complex.mul_im]; simp
    simp only [Set.mem_setOf_eq, h]
    linarith
  constructor
  · refine image_subset_of_component_image hVarphi hsetup d (Q := MandelDim.BuOf d B)
      (fun u hu => (connectedComponentIn_eq hu).symm) ⟨_, hwU⟩ hBuT (fun u hu => Or.inl hu)
  · refine image_subset_of_component_image hVarphi hsetup d (Q := MandelDim.BlOf d B)
      (fun u hu => (connectedComponentIn_eq hu).symm) ⟨_, hwL⟩ hBlT (fun u hu => Or.inr hu)

end

end Work.Horn
