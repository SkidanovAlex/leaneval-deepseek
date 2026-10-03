import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Interfaces.HornParts
import Submission.Work.Parab.basinCoord.exists_basin_coordinate
import Submission.Work.Parab.petalExtras.petal_conn_sc_image
import Submission.Work.Parab.basinEnters.petal_capture
import Submission.Work.Parab.basinEnters.zero_not_mem_basin
import Submission.Work.Horn.isCompact_inter_preimage_of_chain
import Submission.Work.Horn.HB.exists_petal_data
import Submission.Work.Horn.HB.simplyConnectedSpace_iUnion_of_monotone
import Submission.Work.Horn.HB.mapsTo_componentIn_and_avoids_zero
import Submission.Work.Horn.HB.false_of_abel_spread
import Submission.Work.Horn.HB.covering_component_data

/-! Guidance from the project lead (the requester):

LEAD DESIGN (read Submission/Work/Horn/HB/DESIGN.md). Piece HB5: the Lemma 5.2/5.4 tower for an abstract parabolic germ g, given sibling HB4 (Work.Horn.HB.proper_of_covering_LF; import it).
1. Petal: Work.Parab.basinCoord.exists_basin_coordinate hg gives Petal r M ⊆ basin, MapsTo, and a Fatou coordinate Φg (injective on the petal, Φg∘g = Φg+1 on the basin). Work.Parab.petalExtras.petal_conn_sc_image gives a connected, simply connected petal whose Φg-image contains every half-strip {Re > C_b, |Im| ≤ b}. Shrink so that V₀ := petal ⊆ D' and 0 ∉ V₀ (see how parab.lean builds Ωp, Φ_image, flower_petal).
2. Tower: V_{n+1} := connectedComponentIn (D ∩ g⁻¹V_n) of a point of V₀. Then V_n ⊆ V_{n+1} and g(V_{n+1}) ⊆ V_n. Inductively, V_n is open, connected and SC, 0 ∉ V_n (g 0 = 0 ∉ V_n), and HB4 applies at each level.
3. B' := ⋃ V_n = connectedComponentIn (ParabolicBasin g D) z₀ with z₀ ∈ V₀.
   - (⊆) is clear.
   - (⊇): take a path in the basin component from V₀ to z. Its image is compact, so g^N maps it into V₀ for large N (basin = locally uniform convergence to 0, plus petal absorption near 0). By induction, a connected K meeting V₀ with g^N K ⊆ V₀ lies in V_N.
4. Properness: if v ∈ V_{n₀}, then for n ≥ n₀, B' ∩ g⁻¹V_n = V_{n+1}. Indeed any other component of g⁻¹V_n inside V_{m+1} maps onto V_n ∋ v by HB4, but V_{m+1} has a single preimage of v. If v ∉ B', every level is injective by HB4 and the same equality holds. Compact L ⊆ B' lies in some V_N, so B' ∩ g⁻¹L = V_{N+1} ∩ g⁻¹L is compact.
5. SC of B': an increasing union of SC opens (loops and homotopies are compact). See BasinSC/assembly.lean (path_homotopic_refl/subsingleton_hom) and Lib Unif2 simplyConnectedSpace_biUnion_list.
6. Critical point: if g is NOT injective on B', some level V_{m+1} → V_m is non-injective, so v ∈ V_m and the HB4 point a is critical.
   If g IS injective on B', extend Φg to B' by Φg(z) := Φg(g^n z) − n. It is injective on B' and its image is ℂ (half-strips). So Φg : B' → ℂ is a biholomorphism with entire inverse into the BOUNDED set B' ⊆ D' (hD'comp: B' is preconnected in D∖{0} and meets D' near 0). Liouville makes the inverse constant: contradiction.
Split 1, 3, 4, 5 and 6 into children.
-/

namespace Work.Horn.HB

open MandelDim Set Metric Filter Topology

/-! ## Elementary facts about the parabolic basin -/

/-- The parabolic basin is open. -/
lemma isOpen_parabolicBasin (g : ℂ → ℂ) (D : Set ℂ) :
    IsOpen (MandelDim.ParabolicBasin g D) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨U, hU, hUm, hUc⟩ := hz
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  refine Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hε)) fun u hu => ?_
  exact ⟨ball z ε, isOpen_ball.mem_nhds hu, fun n w hw => hUm n (hεU hw), hUc.mono hεU⟩

/-- Every point of the parabolic basin lies in `D` (the defining neighbourhood is a subset of
`D`, by the `n = 0` instance of the defining property). -/
lemma basin_subset_D {g : ℂ → ℂ} {D : Set ℂ} {z : ℂ}
    (hz : z ∈ MandelDim.ParabolicBasin g D) : z ∈ D := by
  obtain ⟨U, hU, hUm, -⟩ := hz
  exact hUm 0 (mem_of_mem_nhds hU)

/-- **The basin is backward invariant inside `D`**: if `g x` is in the basin and `x ∈ D`, then `x`
is in the basin.  (Only continuity of `g` at `x` is used.) -/
lemma mem_basin_of_map_mem_basin {g : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hgd : DifferentiableOn ℂ g D) {x : ℂ} (hx : x ∈ D)
    (h : g x ∈ MandelDim.ParabolicBasin g D) : x ∈ MandelDim.ParabolicBasin g D := by
  obtain ⟨U, hU, hUm, hUc⟩ := h
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD x hx
  have hgx : ContinuousAt g x := (hgd.differentiableAt (hD.mem_nhds hx)).continuousAt
  have hpre : g ⁻¹' U ∈ 𝓝 x := hgx.preimage_mem_nhds hU
  set W : Set ℂ := g ⁻¹' U ∩ ball x ε with hWdef
  have hW : W ∈ 𝓝 x :=
    Filter.inter_mem hpre (isOpen_ball.mem_nhds (mem_ball_self hε))
  refine ⟨W, hW, ?_, ?_⟩
  · intro n
    induction n with
    | zero => intro w hw; exact hεD hw.2
    | succ k _ => intro w hw; rw [Function.iterate_succ_apply]; exact hUm k hw.1
  · rw [Metric.tendstoUniformlyOn_iff] at hUc ⊢
    intro ε' hε'
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hUc ε' hε')
    refine eventually_atTop.mpr ⟨N + 1, fun n hn w hw => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Function.iterate_succ_apply]
    exact hN m (by omega) (g w) hw.1

/-! ## The tower of preimages of the petal -/

/-- The tower `V 0 = V₀`, `V (n+1)` = the connected component in `D ∩ g ⁻¹' V n` of `x`. -/
noncomputable def tower (g : ℂ → ℂ) (D V₀ : Set ℂ) (x : ℂ) : ℕ → Set ℂ
  | 0 => V₀
  | n + 1 => connectedComponentIn (D ∩ g ⁻¹' tower g D V₀ x n) x

lemma tower_zero {g : ℂ → ℂ} {D V₀ : Set ℂ} {x : ℂ} : tower g D V₀ x 0 = V₀ := rfl

lemma tower_succ {g : ℂ → ℂ} {D V₀ : Set ℂ} {x : ℂ} (n : ℕ) :
    tower g D V₀ x (n + 1) = connectedComponentIn (D ∩ g ⁻¹' tower g D V₀ x n) x := rfl

/-- `V (n+1) ⊆ g ⁻¹' V n`, by construction. -/
lemma tower_succ_subset {g : ℂ → ℂ} {D V₀ : Set ℂ} {x : ℂ} (n : ℕ) :
    tower g D V₀ x (n + 1) ⊆ g ⁻¹' tower g D V₀ x n :=
  (connectedComponentIn_subset _ _).trans Set.inter_subset_right

/-- **The elementary inductive facts about the tower.**  Assuming the level-`0` data (open,
connected, `g`-invariant, inside `D`, containing `x₀`, avoiding `0`, inside the basin), every level
is open, connected, contains `x₀`, is `g`-invariant, increases, lies in `D`, avoids `0` and lies in
the basin. -/
lemma tower_facts {g : ℂ → ℂ} {D V₀ : Set ℂ} {x₀ : ℂ}
    (hgD : IsOpen D) (hgd : DifferentiableOn ℂ g D) (hg0 : g 0 = 0)
    (hV₀D : V₀ ⊆ D) (hV₀o : IsOpen V₀) (hV₀c : IsConnected V₀)
    (hV₀map : Set.MapsTo g V₀ V₀) (hx₀ : x₀ ∈ V₀) (h0V₀ : (0 : ℂ) ∉ V₀)
    (hV₀basin : V₀ ⊆ MandelDim.ParabolicBasin g D) :
    ∀ n : ℕ,
      IsOpen (tower g D V₀ x₀ n) ∧ x₀ ∈ tower g D V₀ x₀ n ∧
      IsConnected (tower g D V₀ x₀ n) ∧ tower g D V₀ x₀ n ⊆ tower g D V₀ x₀ (n + 1) ∧
      Set.MapsTo g (tower g D V₀ x₀ n) (tower g D V₀ x₀ n) ∧
      tower g D V₀ x₀ n ⊆ D ∧ (0 : ℂ) ∉ tower g D V₀ x₀ n ∧
      tower g D V₀ x₀ n ⊆ MandelDim.ParabolicBasin g D := by
  have hcont : ContinuousOn g D := hgd.continuousOn
  -- the `n+1`-st level is the component of an open set through `x₀`
  have hVsucc : ∀ n : ℕ,
      tower g D V₀ x₀ (n + 1) = connectedComponentIn (D ∩ g ⁻¹' tower g D V₀ x₀ n) x₀ :=
    fun n => tower_succ n
  have hsubsucc : ∀ n : ℕ, tower g D V₀ x₀ (n + 1) ⊆ g ⁻¹' tower g D V₀ x₀ n :=
    fun n => tower_succ_subset n
  intro n
  induction n with
  | zero =>
      refine ⟨hV₀o, hx₀, hV₀c, ?_, hV₀map, hV₀D, h0V₀, hV₀basin⟩
      rw [tower_zero, hVsucc 0, tower_zero]
      exact IsPreconnected.subset_connectedComponentIn hV₀c.isPreconnected hx₀
        (fun z hz => ⟨hV₀D hz, hV₀map hz⟩)
  | succ n ih =>
      obtain ⟨hVno, hxn, hVnc, hnest, hVnmap, hVnD, h0Vn, hVnbasin⟩ := ih
      have hVn1o : IsOpen (tower g D V₀ x₀ (n + 1)) := by
        rw [hVsucc n]
        exact (hcont.isOpen_inter_preimage hgD hVno).connectedComponentIn
      have hxVn1 : x₀ ∈ tower g D V₀ x₀ (n + 1) := by
        rw [hVsucc n]; exact mem_connectedComponentIn ⟨hV₀D hx₀, hVnmap hxn⟩
      have hVn1c : IsConnected (tower g D V₀ x₀ (n + 1)) :=
        ⟨⟨x₀, hxVn1⟩, isPreconnected_connectedComponentIn⟩
      have hVn1D : tower g D V₀ x₀ (n + 1) ⊆ D :=
        (connectedComponentIn_subset _ _).trans Set.inter_subset_left
      have hVn1map : Set.MapsTo g (tower g D V₀ x₀ (n + 1)) (tower g D V₀ x₀ (n + 1)) :=
        fun z hz => hnest (hsubsucc n hz)
      have hVn1nest : tower g D V₀ x₀ (n + 1) ⊆ tower g D V₀ x₀ (n + 1 + 1) := by
        rw [hVsucc (n + 1)]
        exact IsPreconnected.subset_connectedComponentIn hVn1c.isPreconnected hxVn1
          (fun z hz => ⟨hVn1D hz, hVn1map hz⟩)
      have h0Vn1 : (0 : ℂ) ∉ tower g D V₀ x₀ (n + 1) := by
        intro h0
        exact h0Vn (hg0 ▸ hsubsucc n h0)
      have hVn1basin : tower g D V₀ x₀ (n + 1) ⊆ MandelDim.ParabolicBasin g D := fun z hz =>
        mem_basin_of_map_mem_basin hgD hgd (hVn1D hz) (hVnbasin (hsubsucc n hz))
      exact ⟨hVn1o, hxVn1, hVn1c, hVn1nest, hVn1map, hVn1D, h0Vn1, hVn1basin⟩

/-! ## The tower exhausts the basin component

This is the `(⊇)` half of the design's step 3: a connected compact set meeting `V₀` whose `N`-th
iterate lies in `V₀` lies in `V N`, and every point of the basin component through `x₀` is joined
to `x₀` by a path, whose image is such a connected compact set (petal absorption turns the
eventual entry into `V₀` into a level `N`). -/

/-- **The single step of the tower induction.**  A preconnected set inside `D` which meets `V n`
and whose `g`-image is contained in `V n` already lies in `V (n+1)`. -/
lemma preconnected_subset_tower_succ {g : ℂ → ℂ} {D V₀ : Set ℂ} {x₀ : ℂ}
    (hgD : IsOpen D) (hgd : DifferentiableOn ℂ g D) (hg0 : g 0 = 0)
    (hV₀D : V₀ ⊆ D) (hV₀o : IsOpen V₀) (hV₀c : IsConnected V₀)
    (hV₀map : Set.MapsTo g V₀ V₀) (hx₀ : x₀ ∈ V₀) (h0V₀ : (0 : ℂ) ∉ V₀)
    (hV₀basin : V₀ ⊆ MandelDim.ParabolicBasin g D) :
    ∀ (n : ℕ) (K : Set ℂ), IsPreconnected K → K ⊆ D →
      (K ∩ tower g D V₀ x₀ n).Nonempty → g '' K ⊆ tower g D V₀ x₀ n →
      K ⊆ tower g D V₀ x₀ (n + 1) := by
  have hfacts := tower_facts hgD hgd hg0 hV₀D hV₀o hV₀c hV₀map hx₀ h0V₀ hV₀basin
  intro n K hKpc hKD hKmeet hKimage
  obtain ⟨y, hyK, hyn⟩ := hKmeet
  have hVnpc : IsPreconnected (tower g D V₀ x₀ n) := ((hfacts n).2.2.1).isPreconnected
  have hKsub : K ⊆ D ∩ g ⁻¹' tower g D V₀ x₀ n :=
    fun z hz => ⟨hKD hz, hKimage ⟨z, hz, rfl⟩⟩
  have hVsub : tower g D V₀ x₀ n ⊆ D ∩ g ⁻¹' tower g D V₀ x₀ n :=
    fun z hz => ⟨(hfacts n).2.2.2.2.2.1 hz, (hfacts n).2.2.2.2.1 hz⟩
  have hunion : IsPreconnected (K ∪ tower g D V₀ x₀ n) :=
    hKpc.union y hyK hyn hVnpc
  rw [tower_succ n]
  exact fun z hz => hunion.subset_connectedComponentIn (Or.inr (hfacts n).2.1)
    (Set.union_subset hKsub hVsub) (Or.inl hz)

/-- **The tower exhausts the basin component through `x₀`.**  Every point of the component is
joined to `x₀` by a path; using petal absorption (and the fact that the `x₀`-component of the basin
never hits `0`) some iterate of that path lands in `V₀`, and the single step above propagates this
back to membership in a level of the tower. -/
lemma tower_union_eq_componentIn {g : ℂ → ℂ} {D V₀ : Set ℂ} {x₀ : ℂ}
    (hg : MandelDim.IsParabolicGerm g D)
    (hV₀o : IsOpen V₀) (hV₀c : IsConnected V₀) (hV₀map : Set.MapsTo g V₀ V₀)
    (hV₀D : V₀ ⊆ D) (h0V₀ : (0 : ℂ) ∉ V₀) (hx₀ : x₀ ∈ V₀)
    (hV₀basin : V₀ ⊆ MandelDim.ParabolicBasin g D)
    (hCmap : Set.MapsTo g (connectedComponentIn (MandelDim.ParabolicBasin g D) x₀)
      (connectedComponentIn (MandelDim.ParabolicBasin g D) x₀))
    (havoids : ∀ z ∈ connectedComponentIn (MandelDim.ParabolicBasin g D) x₀, ∀ n : ℕ, (g^[n]) z ≠ 0)
    (henter : ∀ z ∈ MandelDim.ParabolicBasin g D, (∀ n : ℕ, (g^[n]) z ≠ 0) →
      ∃ n : ℕ, (g^[n]) z ∈ V₀) :
    (⋃ n : ℕ, tower g D V₀ x₀ n) = connectedComponentIn (MandelDim.ParabolicBasin g D) x₀ := by
  have hfacts := tower_facts hg.1 hg.2.2.1 hg.2.2.2.1 hV₀D hV₀o hV₀c hV₀map hx₀ h0V₀ hV₀basin
  have hVconn : ∀ n, IsConnected (tower g D V₀ x₀ n) := fun n => (hfacts n).2.2.1
  have hVnest : ∀ n, tower g D V₀ x₀ n ⊆ tower g D V₀ x₀ (n + 1) := fun n => (hfacts n).2.2.2.1
  have hVbasin : ∀ n, tower g D V₀ x₀ n ⊆ MandelDim.ParabolicBasin g D :=
    fun n => (hfacts n).2.2.2.2.2.2.2
  have hmono : Monotone (tower g D V₀ x₀) := monotone_nat_of_le_succ hVnest
  have hV₀to : ∀ n, V₀ ⊆ tower g D V₀ x₀ n := by
    intro n
    have h := hmono (Nat.zero_le n)
    rwa [tower_zero] at h
  set C : Set ℂ := connectedComponentIn (MandelDim.ParabolicBasin g D) x₀ with hCdef
  have hCsub : C ⊆ MandelDim.ParabolicBasin g D := connectedComponentIn_subset _ _
  have hCsubD : C ⊆ D := fun z hz => basin_subset_D (hCsub hz)
  have hx₀C : x₀ ∈ C := mem_connectedComponentIn (hV₀basin hx₀)
  have hCopen : IsOpen C := (isOpen_parabolicBasin g D).connectedComponentIn
  refine Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
  · rw [hCdef]
    have hpcU : IsPreconnected (⋃ n, tower g D V₀ x₀ n) :=
      isPreconnected_iUnion ⟨x₀, Set.mem_iInter.mpr fun n => (hfacts n).2.1⟩
        (fun n => (hVconn n).isPreconnected)
    exact hpcU.subset_connectedComponentIn (Set.mem_iUnion.mpr ⟨0, (hfacts 0).2.1⟩)
      (fun w hw => by obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hw; exact hVbasin m hm) hz
  · -- continuity of the iterates along `C`
    have hcontAt : ∀ (m : ℕ) {w : ℂ}, w ∈ C → ContinuousAt (g^[m]) w := by
      intro m
      induction m with
      | zero => intro w _; simpa using continuousAt_id
      | succ k ih =>
          intro w hwC
          have h1 : ContinuousAt (g^[k]) w := ih hwC
          have hkw : (g^[k]) w ∈ C := hCmap.iterate k hwC
          have h2 : ContinuousAt g ((g^[k]) w) :=
            (hg.2.2.1.differentiableAt (hg.1.mem_nhds (hCsubD hkw))).continuousAt
          have hcomp := h2.comp h1
          have hfun : g ∘ g^[k] = g^[k+1] :=
            funext fun x => by rw [Function.comp_apply, Function.iterate_succ_apply']
          rwa [hfun] at hcomp
    -- the path from `x₀` to `z` inside the component
    haveI : ConnectedSpace ↥C := isConnected_iff_connectedSpace.mp ⟨⟨x₀, hx₀C⟩,
      isPreconnected_connectedComponentIn⟩
    haveI : LocallyPathConnectedSpace ↥C := hCopen.locallyPathConnectedSpace
    haveI : PathConnectedSpace ↥C := PathConnectedSpace.of_locallyPathConnectedSpace
    let γ : Path (⟨x₀, hx₀C⟩ : ↥C) ⟨z, hz⟩ := PathConnectedSpace.somePath _ _
    set K : Set ℂ := Subtype.val '' (Set.range γ) with hKdef
    have hKc : IsCompact K := (isCompact_range γ.continuous).image continuous_subtype_val
    have hKpc : IsPreconnected K :=
      (isPreconnected_range γ.continuous).image _ continuous_subtype_val.continuousOn
    have hx₀K : x₀ ∈ K := ⟨⟨x₀, hx₀C⟩, ⟨0, γ.source⟩, rfl⟩
    have hzK : z ∈ K := ⟨⟨z, hz⟩, ⟨1, γ.target⟩, rfl⟩
    have hKC : K ⊆ C := by rintro w ⟨t, -, rfl⟩; exact t.2
    have hKD : K ⊆ D := fun w hw => hCsubD (hKC hw)
    -- a level `N` with `g^N K ⊆ V₀`, by compactness
    obtain ⟨N, hN⟩ : ∃ N : ℕ, g^[N] '' K ⊆ V₀ := by
      classical
      have hpoint : ∀ w : ℂ, ∃ n : ℕ, w ∈ K → (g^[n]) w ∈ V₀ := by
        intro w
        by_cases hw : w ∈ K
        · exact ⟨Classical.choose (henter w (hCsub (hKC hw)) (havoids w (hKC hw))),
            fun _ => Classical.choose_spec (henter w (hCsub (hKC hw)) (havoids w (hKC hw)))⟩
        · exact ⟨0, fun h => absurd h hw⟩
      choose hn hn_spec using hpoint
      let U : ℂ → Set ℂ := fun w => interior ((g^[hn w]) ⁻¹' V₀)
      have hUopen : ∀ w, IsOpen (U w) := fun w => isOpen_interior
      have hUmem : ∀ w (hw : w ∈ K), w ∈ U w := by
        intro w hw
        have hpre : (g^[hn w]) ⁻¹' V₀ ∈ 𝓝 w :=
          (hcontAt (hn w) (hKC hw)).preimage_mem_nhds (hV₀o.mem_nhds (hn_spec w hw))
        exact mem_interior_iff_mem_nhds.mpr hpre
      obtain ⟨t, ht⟩ := hKc.elim_finite_subcover U hUopen
        (fun w hw => Set.mem_iUnion.mpr ⟨w, hUmem w hw⟩)
      refine ⟨t.sup hn, fun w hw => ?_⟩
      obtain ⟨y, hyK, hyw⟩ := hw
      subst hyw
      obtain ⟨i, hit, hiy⟩ : ∃ i ∈ t, y ∈ U i := by
        simpa only [Set.mem_iUnion, exists_prop] using ht hyK
      have h1 : (g^[hn i]) y ∈ V₀ :=
        interior_subset (s := (g^[hn i]) ⁻¹' V₀) (show y ∈ interior ((g^[hn i]) ⁻¹' V₀) from hiy)
      have hle : hn i ≤ t.sup hn := Finset.le_sup (f := hn) hit
      have h2 : (g^[t.sup hn]) y = (g^[t.sup hn - hn i]) ((g^[hn i]) y) := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]
      rw [h2]
      exact (hV₀map.iterate (t.sup hn - hn i)) h1
    -- the chain: a preconnected subset of `C` meeting `V₀` whose `m`-th iterate lies in `V₀`
    -- is contained in the `m`-th level
    have hchain : ∀ m : ℕ, ∀ K' : Set ℂ, IsPreconnected K' → K' ⊆ C → (K' ∩ V₀).Nonempty →
        g^[m] '' K' ⊆ V₀ → K' ⊆ tower g D V₀ x₀ m := by
      intro m
      induction m with
      | zero => intro K' _ _ _ himg; simpa [tower_zero] using himg
      | succ k ih =>
          intro K' hpc hsub hmeet himg
          have hK'D : K' ⊆ D := fun w hw => hCsubD (hsub hw)
          have hgK'C : g '' K' ⊆ C := by
            rintro w ⟨u, hu, rfl⟩
            exact hCmap (hsub hu)
          have hpc' : IsPreconnected (g '' K') := hpc.image g (hg.2.2.1.continuousOn.mono hK'D)
          obtain ⟨u, huK', huV₀⟩ := hmeet
          have hmeet' : (g '' K' ∩ V₀).Nonempty := ⟨g u, ⟨u, huK', rfl⟩, hV₀map huV₀⟩
          have himg' : g^[k] '' (g '' K') ⊆ V₀ := by
            rintro y ⟨v, hv, rfl⟩
            obtain ⟨u, hu, rfl⟩ := hv
            have hmem : g^[k + 1] u ∈ V₀ := himg (Set.mem_image_of_mem (g^[k + 1]) hu)
            rw [Function.iterate_succ_apply] at hmem
            exact hmem
          have hstep : g '' K' ⊆ tower g D V₀ x₀ k := ih (g '' K') hpc' hgK'C hmeet' himg'
          have hmeetk : (K' ∩ tower g D V₀ x₀ k).Nonempty :=
            ⟨u, huK', hV₀to k huV₀⟩
          exact preconnected_subset_tower_succ hg.1 hg.2.2.1 hg.2.2.2.1 hV₀D hV₀o hV₀c
            hV₀map hx₀ h0V₀ hV₀basin k K' hpc hK'D hmeetk hstep
    exact Set.mem_iUnion.mpr ⟨N, hchain N K hKpc hKC ⟨x₀, hx₀K, hx₀⟩ hN hzK⟩

/-! ## The abstract covering-component datum (piece HB4 of the design)

Everything below uses exactly one outside ingredient: the abstract statement that a component of
`D ∩ g ⁻¹' V` over a simply connected `V` is proper onto `V`, is simply connected, is injective
off the critical value `v`, and has a unique (critical iff non-injective) preimage of `v`.  It is
stated here as a wrapper so that the rest of the proof does not depend on which copy of that
result is available (see `Submission/Work/Horn/HB/NOTES_HB5.md`). -/
theorem covering_component_data_aux {g : ℂ → ℂ} {D : Set ℂ} {v : ℂ} {r : ℝ}
    (hDo : IsOpen D) (hgd : DifferentiableOn ℂ g D) (hr : 0 < r) (hrv : r < ‖v‖)
    (hcov : IsCoveringMapOn (fun z : D => g z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v})
    (hLF : ∀ x ∈ D, g x ∈ Metric.ball v r → ∀ K ⊆ Metric.ball v r, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K))
    {V : Set ℂ} (hVo : IsOpen V) (hVc : IsConnected V) (hVsc : SimplyConnectedSpace V)
    (h0V : (0 : ℂ) ∉ V) {x : ℂ} (hxD : x ∈ D) (hxV : g x ∈ V) {W : Set ℂ}
    (hW : W = connectedComponentIn (D ∩ g ⁻¹' V) x) :
    (∀ K ⊆ V, IsCompact K → IsCompact (W ∩ g ⁻¹' K)) ∧ V ⊆ g '' W ∧
      SimplyConnectedSpace W ∧ (v ∉ V → Set.InjOn g W) ∧
      (v ∈ V → ∃ a ∈ W, g a = v ∧ (∀ b ∈ W, g b = v → b = a) ∧
        (¬ Set.InjOn g W → deriv g a = 0)) :=
  Work.Horn.HB.covering_component_data hDo hgd hr hrv hcov hLF hVo hVc hVsc h0V hxD hxV hW

theorem basin_of_tower {g : ℂ → ℂ} {D D' : Set ℂ} {v : ℂ} {r : ℝ}
    (hg : MandelDim.IsParabolicGerm g D) (hr : 0 < r) (hrv : r < ‖v‖)
    (hcov : IsCoveringMapOn (fun z : D => g z) {ζ : ℂ | ζ ≠ 0 ∧ ζ ≠ v})
    (hLF : ∀ x ∈ D, g x ∈ Metric.ball v r → ∀ K ⊆ Metric.ball v r, IsCompact K →
      IsCompact (connectedComponentIn (D ∩ g ⁻¹' Metric.ball v r) x ∩ g ⁻¹' K))
    (hD'o : IsOpen D') (hD'sub : D' ⊆ D) (h0D' : (0 : ℂ) ∈ D') (hD'b : Bornology.IsBounded D')
    (hD'comp : ∀ C : Set ℂ, IsPreconnected C → C ⊆ D \ {0} → (C ∩ D').Nonempty → C ⊆ D') :
    ∃ B' : Set ℂ,
      (∃ z ∈ MandelDim.ParabolicBasin g D,
        B' = connectedComponentIn (MandelDim.ParabolicBasin g D) z) ∧
      Set.MapsTo g B' B' ∧ (∀ L : Set ℂ, L ⊆ B' → IsCompact L → IsCompact (B' ∩ g ⁻¹' L)) ∧
      SimplyConnectedSpace B' ∧ ∃ z ∈ B', deriv g z = 0 := by
  classical
  -- ## step 1: the petal `V₀`, its point `x₀` and the Fatou coordinate `Φ`
  obtain ⟨Φ, V₀, x₀, hV₀o, hV₀c, hV₀sc, h0V₀, hx₀, hV₀D, hV₀D'ne, hV₀basin, hV₀map,
    hΦdiff, hΦabel, hΦinj, hΦstrip, henter⟩ :=
    Work.Horn.HB.exists_petal_data hg hD'o h0D'
  have hV₀subD' : V₀ ⊆ D' :=
    hD'comp V₀ hV₀c.isPreconnected (fun z hz => ⟨hV₀D hz, fun h0 => h0V₀ (h0 ▸ hz)⟩) hV₀D'ne
  -- ## step 2: the tower and its elementary properties
  have hfacts := tower_facts hg.1 hg.2.2.1 hg.2.2.2.1 hV₀D hV₀o hV₀c hV₀map hx₀ h0V₀ hV₀basin
  have hVopen : ∀ n : ℕ, IsOpen (tower g D V₀ x₀ n) := fun n => (hfacts n).1
  have hx₀V : ∀ n : ℕ, x₀ ∈ tower g D V₀ x₀ n := fun n => (hfacts n).2.1
  have hVconn : ∀ n : ℕ, IsConnected (tower g D V₀ x₀ n) := fun n => (hfacts n).2.2.1
  have hVnest : ∀ n : ℕ, tower g D V₀ x₀ n ⊆ tower g D V₀ x₀ (n + 1) := fun n => (hfacts n).2.2.2.1
  have hVmap : ∀ n : ℕ, Set.MapsTo g (tower g D V₀ x₀ n) (tower g D V₀ x₀ n) :=
    fun n => (hfacts n).2.2.2.2.1
  have hVsubD : ∀ n : ℕ, tower g D V₀ x₀ n ⊆ D := fun n => (hfacts n).2.2.2.2.2.1
  have h0V : ∀ n : ℕ, (0 : ℂ) ∉ tower g D V₀ x₀ n := fun n => (hfacts n).2.2.2.2.2.2.1
  have hVbasin : ∀ n : ℕ, tower g D V₀ x₀ n ⊆ MandelDim.ParabolicBasin g D :=
    fun n => (hfacts n).2.2.2.2.2.2.2
  have hmono : Monotone (tower g D V₀ x₀) := monotone_nat_of_le_succ hVnest
  have hx₀D : x₀ ∈ D := hV₀D hx₀
  -- ## step 3: the component of the basin through `x₀` is exactly the union of the tower
  have hCmap := (Work.Horn.HB.mapsTo_componentIn_and_avoids_zero hg hV₀basin hV₀c hV₀map
    h0V₀ hx₀).1
  have havoids := (Work.Horn.HB.mapsTo_componentIn_and_avoids_zero hg hV₀basin hV₀c hV₀map
    h0V₀ hx₀).2
  have hB'eq : (⋃ n : ℕ, tower g D V₀ x₀ n) =
      connectedComponentIn (MandelDim.ParabolicBasin g D) x₀ :=
    tower_union_eq_componentIn hg hV₀o hV₀c hV₀map hV₀D h0V₀ hx₀ hV₀basin hCmap havoids henter
  -- ## step 4: the level data (covering + finite local monodromy)
  have hstep : ∀ k : ℕ, SimplyConnectedSpace ↥(tower g D V₀ x₀ k) →
      (∀ K ⊆ tower g D V₀ x₀ k, IsCompact K →
        IsCompact (tower g D V₀ x₀ (k + 1) ∩ g ⁻¹' K)) ∧
      tower g D V₀ x₀ k ⊆ g '' tower g D V₀ x₀ (k + 1) ∧
      SimplyConnectedSpace ↥(tower g D V₀ x₀ (k + 1)) ∧
      (v ∉ tower g D V₀ x₀ k → Set.InjOn g (tower g D V₀ x₀ (k + 1))) ∧
      (v ∈ tower g D V₀ x₀ k → ∃ a ∈ tower g D V₀ x₀ (k + 1), g a = v ∧
        (∀ b ∈ tower g D V₀ x₀ (k + 1), g b = v → b = a) ∧
        (¬ Set.InjOn g (tower g D V₀ x₀ (k + 1)) → deriv g a = 0)) := by
    intro k hsc
    exact covering_component_data_aux hg.1 hg.2.2.1 hr hrv hcov hLF (hVopen k)
      (hVconn k) hsc (h0V k) hx₀D (hVmap k (hx₀V k)) (tower_succ k)
  have hlevelSC : ∀ n : ℕ, SimplyConnectedSpace ↥(tower g D V₀ x₀ n) := by
    intro n
    induction n with
    | zero => exact hV₀sc
    | succ k ih => exact (hstep k ih).2.2.1
  have hlevel : ∀ k : ℕ,
      (∀ K ⊆ tower g D V₀ x₀ k, IsCompact K →
        IsCompact (tower g D V₀ x₀ (k + 1) ∩ g ⁻¹' K)) ∧
      tower g D V₀ x₀ k ⊆ g '' tower g D V₀ x₀ (k + 1) ∧
      SimplyConnectedSpace ↥(tower g D V₀ x₀ (k + 1)) ∧
      (v ∉ tower g D V₀ x₀ k → Set.InjOn g (tower g D V₀ x₀ (k + 1))) ∧
      (v ∈ tower g D V₀ x₀ k → ∃ a ∈ tower g D V₀ x₀ (k + 1), g a = v ∧
        (∀ b ∈ tower g D V₀ x₀ (k + 1), g b = v → b = a) ∧
        (¬ Set.InjOn g (tower g D V₀ x₀ (k + 1)) → deriv g a = 0)) :=
    fun k => hstep k (hlevelSC k)
  -- ## step 5: `B'` and its basic properties
  set B' : Set ℂ := ⋃ n : ℕ, tower g D V₀ x₀ n with hB'def
  have hB'eq' : B' = connectedComponentIn (MandelDim.ParabolicBasin g D) x₀ := by
    rw [hB'def]; exact hB'eq
  have hx₀B' : x₀ ∈ B' := by rw [hB'def]; exact Set.mem_iUnion.mpr ⟨0, hx₀V 0⟩
  have hB'open : IsOpen B' := by rw [hB'def]; exact isOpen_iUnion hVopen
  have h0B' : (0 : ℂ) ∉ B' := by
    rw [hB'def]
    intro h0
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h0
    exact h0V n hn
  have hB'subD : B' ⊆ D := by
    intro z hz
    rw [hB'def] at hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    exact hVsubD n hn
  have hB'basin : B' ⊆ MandelDim.ParabolicBasin g D := by
    intro z hz
    rw [hB'def] at hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    exact hVbasin n hn
  have hB'pc : IsPreconnected B' := by
    rw [hB'def]
    exact isPreconnected_iUnion ⟨x₀, Set.mem_iInter.mpr fun n => hx₀V n⟩
      (fun n => (hVconn n).isPreconnected)
  have hB'subD' : B' ⊆ D' :=
    hD'comp B' hB'pc (fun z hz => ⟨hB'subD hz, fun h0 => h0B' (h0 ▸ hz)⟩)
      ⟨x₀, hx₀B', hV₀subD' hx₀⟩
  have hB'bdd : Bornology.IsBounded B' := hD'b.subset hB'subD'
  have hB'map : Set.MapsTo g B' B' := hB'eq' ▸ hCmap
  have hB'surj : B' ⊆ g '' B' := by
    intro z hz
    rw [hB'def] at hz
    obtain ⟨M, hM⟩ := Set.mem_iUnion.mp hz
    obtain ⟨w, hwV, hwg⟩ := (hlevel M).2.1 hM
    exact ⟨w, by rw [hB'def]; exact Set.mem_iUnion.mpr ⟨M + 1, hwV⟩, hwg⟩
  -- ## step 6: the levels are proper over the previous ones
  have hprop : ∀ L : Set ℂ, L ⊆ B' → IsCompact L → IsCompact (B' ∩ g ⁻¹' L) := by
    intro L hLB hLc
    obtain ⟨N, hN⟩ : ∃ N : ℕ, L ⊆ tower g D V₀ x₀ N :=
      Work.Horn.exists_subset_of_isCompact_iUnion hVopen hVnest hLc
        (fun z hz => by rw [← hB'def]; exact hLB hz)
    by_cases hv : v ∈ B'
    · -- the critical value belongs to the tower: the levels are then unique over `v`
      obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, v ∈ tower g D V₀ x₀ n₀ := by
        rw [hB'def] at hv
        exact Set.mem_iUnion.mp hv
      have hkey : ∀ n : ℕ, n₀ ≤ n →
          B' ∩ g ⁻¹' tower g D V₀ x₀ n ⊆ tower g D V₀ x₀ (n + 1) := by
        intro n hn z hz
        obtain ⟨hzB, hzg⟩ := hz
        rw [hB'def] at hzB
        obtain ⟨M, hM⟩ := Set.mem_iUnion.mp hzB
        by_cases hMn : M ≤ n + 1
        · exact hmono hMn hM
        · push_neg at hMn
          have hvM1 : v ∈ tower g D V₀ x₀ (M - 1) := hmono (by omega) hn₀
          -- the component of `D ∩ g ⁻¹' V n` through `z`
          set W₀ : Set ℂ := connectedComponentIn (D ∩ g ⁻¹' tower g D V₀ x₀ n) z with hW₀
          have hW₀subD : W₀ ⊆ D := (connectedComponentIn_subset _ _).trans Set.inter_subset_left
          have hW₀g : W₀ ⊆ g ⁻¹' tower g D V₀ x₀ n :=
            (connectedComponentIn_subset _ _).trans Set.inter_subset_right
          have hW₀pc : IsPreconnected W₀ := isPreconnected_connectedComponentIn
          have hzW₀ : z ∈ W₀ := mem_connectedComponentIn ⟨hB'subD hzB, hzg⟩
          -- `W₀ ⊆ V M`
          have hW₀subVM : W₀ ⊆ tower g D V₀ x₀ M := by
            have hsub : W₀ ∪ tower g D V₀ x₀ M ⊆ D ∩ g ⁻¹' tower g D V₀ x₀ (M - 1) := by
              rintro x (hx | hx)
              · exact ⟨hW₀subD hx, hmono (by omega) (hW₀g hx)⟩
              · have hx' : x ∈ tower g D V₀ x₀ (M - 1 + 1) := by
                  rw [Nat.sub_add_cancel (by omega : 1 ≤ M)]; exact hx
                exact ⟨hVsubD M hx, tower_succ_subset (M - 1) hx'⟩
            have hpcU : IsPreconnected (W₀ ∪ tower g D V₀ x₀ M) :=
              hW₀pc.union z hzW₀ hM (hVconn M).isPreconnected
            have h1 := hpcU.subset_connectedComponentIn (Or.inr (hx₀V M)) hsub
            rw [← tower_succ (M - 1), Nat.sub_add_cancel (by omega : 1 ≤ M)] at h1
            exact fun w hw => h1 (Or.inl hw)
          -- the unique preimages of `v` in `W₀`, in `V (n+1)` and in `V M`
          obtain ⟨-, -, -, -, hcritW⟩ :=
            covering_component_data_aux hg.1 hg.2.2.1 hr hrv hcov hLF (hVopen n)
              (hVconn n) (hlevelSC n) (h0V n) (hB'subD hzB) hzg hW₀
          obtain ⟨aW, haW, hgaW, huniqW, -⟩ := hcritW (hmono hn hn₀)
          obtain ⟨b, hbV, hgb, -, -⟩ := (hlevel n).2.2.2.2 (hmono hn hn₀)
          have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel (by omega : 1 ≤ M)
          obtain ⟨aM, haM, hgaM, huniqM, -⟩ := (hlevel (M - 1)).2.2.2.2 hvM1
          have huniqM' : ∀ c ∈ tower g D V₀ x₀ M, g c = v → c = aM := by
            intro c hc hgc
            have hc' : c ∈ tower g D V₀ x₀ (M - 1 + 1) := by rw [hM1]; exact hc
            exact huniqM c hc' hgc
          have hW₀subn1 : aW = b := by
            rw [huniqM' aW (hW₀subVM haW) hgaW, huniqM' b (hmono (by omega) hbV) hgb]
          have hsub2 : W₀ ∪ tower g D V₀ x₀ (n + 1) ⊆ D ∩ g ⁻¹' tower g D V₀ x₀ n := by
            rintro x (hx | hx)
            · exact ⟨hW₀subD hx, hW₀g hx⟩
            · exact ⟨hVsubD (n + 1) hx, hmono (by omega) (tower_succ_subset n hx)⟩
          have hpc2 : IsPreconnected (W₀ ∪ tower g D V₀ x₀ (n + 1)) :=
            hW₀pc.union aW haW (hW₀subn1 ▸ hbV) (hVconn (n + 1)).isPreconnected
          have h2 := hpc2.subset_connectedComponentIn (Or.inr (hx₀V (n + 1))) hsub2
          exact h2 (Or.inl hzW₀)
      -- `L ⊆ V (max N n₀)`, and the key identification applies at that level
      have hEq : B' ∩ g ⁻¹' L = tower g D V₀ x₀ (max N n₀ + 1) ∩ g ⁻¹' L := by
        apply Set.Subset.antisymm
        · rintro z ⟨hzB, hzL⟩
          exact ⟨hkey (max N n₀) (le_max_right N n₀)
            ⟨hzB, hmono (le_max_left N n₀) (hN hzL)⟩, hzL⟩
        · rintro z ⟨hzV, hzL⟩
          exact ⟨by rw [hB'def]; exact Set.mem_iUnion.mpr ⟨max N n₀ + 1, hzV⟩, hzL⟩
      rw [hEq]
      exact (hlevel (max N n₀)).1 L (fun z hz => hmono (le_max_left N n₀) (hN hz)) hLc
    · -- the critical value is outside `B'`: every level of the tower is injective
      have hinjB' : Set.InjOn g B' := by
        intro a ha b hb hab
        rw [hB'def] at ha hb
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ha
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hb
        have hv' : v ∉ tower g D V₀ x₀ (max m k) := fun hv' =>
          hv (by rw [hB'def]; exact Set.mem_iUnion.mpr ⟨max m k, hv'⟩)
        exact (hlevel (max m k)).2.2.2.1 hv' (hmono (by omega) hm)
          (hmono (by omega) hk) hab
      have hEq : B' ∩ g ⁻¹' L = tower g D V₀ x₀ (N + 1) ∩ g ⁻¹' L := by
        apply Set.Subset.antisymm
        · rintro z ⟨hzB, hzL⟩
          obtain ⟨w, hwV, hwg⟩ := (hlevel N).2.1 (hN hzL)
          have hwB : w ∈ B' := by rw [hB'def]; exact Set.mem_iUnion.mpr ⟨N + 1, hwV⟩
          have hzw : z = w := hinjB' hzB hwB (by rw [hwg])
          exact ⟨hzw ▸ hwV, hzL⟩
        · rintro z ⟨hzV, hzL⟩
          exact ⟨by rw [hB'def]; exact Set.mem_iUnion.mpr ⟨N + 1, hzV⟩, hzL⟩
      rw [hEq]
      exact (hlevel N).1 L hN hLc
  -- ## step 7: a critical point of `g` lies in `B'`
  have hcrit : ∃ z ∈ B', deriv g z = 0 := by
    by_cases hinj : Set.InjOn g B'
    · -- otherwise `Φ` would be a biholomorphism from the bounded `B'` onto `ℂ`
      exact (Work.Horn.HB.false_of_abel_spread hB'open hB'bdd
        (fun z hz => by
          rw [hB'def]
          exact Set.mem_iUnion.mpr ⟨0, tower_zero.symm ▸ hz⟩)
        hB'map hB'surj hinj (Set.image_subset_iff.mpr hV₀map)
        (hΦdiff.mono hB'basin) (fun z hz => hΦabel z (hB'basin hz)) hΦinj hΦstrip
        (fun z hz => henter z (hB'basin hz)
          (by rw [hB'eq'] at hz; exact havoids z hz))).elim
    · have hex : ∃ a ∈ B', ∃ b ∈ B', a ≠ b ∧ g a = g b := by
        by_contra hcon
        push_neg at hcon
        refine hinj (fun a ha b hb hab => ?_)
        by_contra hne
        exact hcon a ha b hb hne hab
      obtain ⟨a, haB, b, hbB, hab, hgab⟩ := hex
      rw [hB'def] at haB hbB
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp haB
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hbB
      have hnInj : ¬ Set.InjOn g (tower g D V₀ x₀ (max m k + 1)) := fun hI =>
        hab (hI (hmono (by omega) hm) (hmono (by omega) hk) hgab)
      by_cases hv' : v ∈ tower g D V₀ x₀ (max m k)
      · obtain ⟨a₀, ha₀, -, -, hcrit₀⟩ := (hlevel (max m k)).2.2.2.2 hv'
        exact ⟨a₀, by rw [hB'def]; exact Set.mem_iUnion.mpr ⟨max m k + 1, ha₀⟩, hcrit₀ hnInj⟩
      · exact absurd ((hlevel (max m k)).2.2.2.1 hv') hnInj
  -- ## conclusion
  exact ⟨B', ⟨x₀, hV₀basin hx₀, hB'eq'⟩, hB'map, hprop,
    Work.Horn.HB.simplyConnectedSpace_iUnion_of_monotone hVopen hVnest hlevelSC ⟨x₀, hx₀V 0⟩,
    hcrit⟩

end Work.Horn.HB
