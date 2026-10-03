import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# L62 — interface facts for the parabolic basin and the lifted horn-map domain

`basin_iface` collects the elementary structural facts about `ParabolicBasin g₀ D` and about the
§4.1 data `d : ParabData g₀ D` that the §6 assembly (Lemma 6.2) consumes.

* the basin is contained in the domain `D`, every point of the basin has all its iterates in `D`,
  the basin is open, and it is invariant backwards along `g₀` (on `D`);
* forward invariance of the basin is *not* a formal consequence of the definition alone (the
  definition only constrains `g₀` on the open set `D`, which need not be connected, and
  `ParabolicBasin` is a locally uniform notion): it is proved here from the attracting petal `Ωp`
  supplied by the §4.1 data.  A basin point enters `Ωp` after finitely many steps, `Ωp` is forward
  invariant and lies in the basin, while the basin is backward invariant on `D` — so the first
  point of the orbit cannot leave the basin;
* consequently the lifted domain `d.DE = d.Dφ ∩ d.φ ⁻¹' (basin)` is `ℤ`-invariant
  (`w ∈ d.DE ↔ w + 1 ∈ d.DE`) and `d.E = d.Φ ∘ d.φ` is equivariant on it,
  `d.E (w + 1) = d.E w + 1`;
* `d.DE` contains the ends `{η₀ < |Im w|}` (this is the field `ends_sub` of the §4.1 data).
-/

namespace Work.L62

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

/-! ## Elementary structure of `ParabolicBasin` -/

/-- The basin is contained in the domain. -/
lemma parabolicBasin_subset (f : ℂ → ℂ) (D : Set ℂ) : ParabolicBasin f D ⊆ D := by
  rintro z ⟨U, hU, hmap, -⟩
  exact hmap 0 (mem_of_mem_nhds hU)

/-- Every point of the basin has all its forward iterates in the domain. -/
lemma parabolicBasin_iterate_mem (f : ℂ → ℂ) (D : Set ℂ) {z : ℂ}
    (hz : z ∈ ParabolicBasin f D) (n : ℕ) : (f^[n]) z ∈ D := by
  obtain ⟨U, hU, hmap, -⟩ := hz
  exact hmap n (mem_of_mem_nhds hU)

/-- The basin is open. -/
lemma isOpen_parabolicBasin (f : ℂ → ℂ) (D : Set ℂ) : IsOpen (ParabolicBasin f D) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨U, hU, hmap, hunif⟩
  obtain ⟨V, hVU, hVopen, hzV⟩ := mem_nhds_iff.mp hU
  refine mem_of_superset (hVopen.mem_nhds hzV) fun y hy => ?_
  exact ⟨V, hVopen.mem_nhds hy, fun n => (hmap n).mono hVU Subset.rfl, hunif.mono hVU⟩

/-- The basin is invariant backwards: a point of the domain whose image lies in the basin is
itself in the basin.  (Only the continuity of `f` at the point is used.) -/
lemma parabolicBasin_backward (f : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D)
    (hf : DifferentiableOn ℂ f D) {z : ℂ} (hz : z ∈ D)
    (hz' : f z ∈ ParabolicBasin f D) : z ∈ ParabolicBasin f D := by
  obtain ⟨U, hU, hmap, hunif⟩ := hz'
  have hcont : ContinuousAt f z := hf.continuousOn.continuousAt (hD.mem_nhds hz)
  have hW : D ∩ f ⁻¹' U ∈ 𝓝 z :=
    Filter.inter_mem (hD.mem_nhds hz) (hcont.preimage_mem_nhds hU)
  refine ⟨D ∩ f ⁻¹' U, hW, ?_, ?_⟩
  · intro n
    cases n with
    | zero =>
      intro y hy
      exact hy.1
    | succ k =>
      intro y hy
      rw [Function.iterate_succ_apply]
      exact hmap k hy.2
  · rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hunif ε hε)
    refine Filter.eventually_atTop.mpr ⟨N + 1, fun n hn y hy => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simpa only [Function.iterate_succ_apply] using hN m (by omega) (f y) hy.2

/-! ## Forward invariance from the petal of the §4.1 data -/

/-- The basin is invariant forwards, using the attracting petal `Ωp` of the §4.1 data: every basin
point enters `Ωp` after finitely many steps, `Ωp` is forward invariant and contained in the basin,
while the basin is backward invariant on `D`; hence the first point of an orbit which ends up in
`Ωp` cannot leave the basin. -/
lemma parabolicBasin_forward (g₀ : ℂ → ℂ) (D : Set ℂ) (d : ParabData g₀ D) (hD : IsOpen D)
    (hf : DifferentiableOn ℂ g₀ D)
    (hreg : ∀ z ∈ ParabolicBasin g₀ D, ∀ n : ℕ, (g₀^[n]) z ≠ 0) :
    MapsTo g₀ (ParabolicBasin g₀ D) (ParabolicBasin g₀ D) := by
  intro z hz
  by_contra hw
  -- contrapositive of backward invariance: a point of `D` outside the basin has its image
  -- outside the basin as well
  have hstep : ∀ y ∈ D, y ∉ ParabolicBasin g₀ D → g₀ y ∉ ParabolicBasin g₀ D := by
    intro y hyD hyB hy'
    exact hyB (parabolicBasin_backward g₀ D hD hf hyD hy')
  have hiter : ∀ n : ℕ, (g₀^[n]) z ∉ ParabolicBasin g₀ D →
      (g₀^[n.succ]) z ∉ ParabolicBasin g₀ D := by
    intro n hn
    have hmem : (g₀^[n]) z ∈ D := parabolicBasin_iterate_mem g₀ D hz n
    have h := hstep ((g₀^[n]) z) hmem hn
    rw [Function.iterate_succ_apply']
    exact h
  -- hence no point of the orbit of `z` after the first one is in the basin
  have hP : ∀ j : ℕ, (g₀^[j.succ]) z ∉ ParabolicBasin g₀ D := by
    intro j
    induction j with
    | zero =>
      exact hw
    | succ k ih =>
      exact hiter k.succ ih
  obtain ⟨m, hm⟩ := d.basin_enter z hz (hreg z hz)
  cases m with
  | zero =>
    exact hw (d.Ωp_sub (d.Ωp_maps (by simpa using hm)))
  | succ k =>
    exact hP k (d.Ωp_sub hm)

/-! ## The interface lemma -/

theorem basin_iface (g₀ : ℂ → ℂ) (D : Set ℂ) (d : ParabData g₀ D) (hg : IsParabolicGerm g₀ D)
    (hreg : ∀ z ∈ ParabolicBasin g₀ D, ∀ n : ℕ, (g₀^[n]) z ≠ 0) :
    ParabolicBasin g₀ D ⊆ D ∧
    MapsTo g₀ (ParabolicBasin g₀ D) (ParabolicBasin g₀ D) ∧
    (∀ z ∈ D, g₀ z ∈ ParabolicBasin g₀ D → z ∈ ParabolicBasin g₀ D) ∧
    IsTInvariant d.DE ∧
    (∀ w ∈ d.DE, d.E (w + 1) = d.E w + 1) ∧
    (∀ w : ℂ, d.η₀ < |w.im| → w ∈ d.DE) := by
  have hD : IsOpen D := hg.1
  have hf : DifferentiableOn ℂ g₀ D := hg.2.2.1
  have hfwd : MapsTo g₀ (ParabolicBasin g₀ D) (ParabolicBasin g₀ D) :=
    parabolicBasin_forward g₀ D d hD hf hreg
  refine ⟨parabolicBasin_subset g₀ D, hfwd,
    fun z hz hz' => parabolicBasin_backward g₀ D hD hf hz hz', ?_, ?_, ?_⟩
  · -- `d.DE` is invariant under `w ↦ w + 1`
    intro w
    constructor
    · rintro ⟨hwφ, hwb⟩
      have hwD : d.φ w ∈ D := parabolicBasin_subset g₀ D hwb
      have hsucc : w + 1 ∈ d.Dφ := (d.succ_iff w hwφ).mpr hwD
      exact ⟨hsucc, by rw [d.φ_abel w hwφ hsucc]; exact hfwd hwb⟩
    · rintro ⟨hsucc, hb⟩
      have hwφ : w ∈ d.Dφ := by
        have h := d.left_inv (w + 1) hsucc
        simpa using h
      have hwD : d.φ w ∈ D := (d.succ_iff w hwφ).mp hsucc
      have habel : d.φ (w + 1) = g₀ (d.φ w) := d.φ_abel w hwφ hsucc
      exact ⟨hwφ, parabolicBasin_backward g₀ D hD hf hwD (habel ▸ hb)⟩
  · -- `d.E = d.Φ ∘ d.φ` is equivariant on `d.DE`
    intro w hw
    obtain ⟨hwφ, hwb⟩ := hw
    have hwD : d.φ w ∈ D := parabolicBasin_subset g₀ D hwb
    have hsucc : w + 1 ∈ d.Dφ := (d.succ_iff w hwφ).mpr hwD
    change d.Φ (d.φ (w + 1)) = d.Φ (d.φ w) + 1
    rw [d.φ_abel w hwφ hsucc]
    exact d.Φ_abel (d.φ w) hwb
  · -- the ends are inside `d.DE`
    intro w hw
    exact d.ends_sub w hw

end

end Work.L62
