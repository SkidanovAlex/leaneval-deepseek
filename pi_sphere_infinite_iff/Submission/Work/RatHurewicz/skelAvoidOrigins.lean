import Mathlib
import Submission.Work.RatHurewicz.cellFacts
import Submission.Work.RatHurewicz.skelChartAux
import Submission.Work.RatHurewicz.AvoidOrigin.Class
import Submission.Work.RatHurewicz.AvoidOrigin.chartInjective
import Submission.Work.RatHurewicz.MAO.linkTo
import Submission.Work.RatHurewicz.avoidCompress
import Submission.Work.RatHurewicz.szFun_eqvGen
import Submission.Work.RatHurewicz.chartAux
import Submission.Work.RatHurewicz.pathConnected_punctured_simplex
import Submission.Work.RatHurewicz.isClosed_image_stratum_compact

/-!
# Pushing a path in the `k`-skeleton of the cycle model off a finite set of points

The model `Model D` of a cycle is described in `Submission.Work.RatHurewicz.cycleModelDefs`: it is
the quotient of `Raw D = (Σ i, Δ^{n+1}) ⊕ (Σ i, I)` by the gluing relation `modelRel D`, and
`skel D k` is its `k`-skeleton, the set of points of `rawWeight ≤ k+1`
(`Work.RatHurewicz.mem_skel_iff`).

The main result of this file is `Work.RatHurewicz.skelAvoidOrigins`: for `k ≥ 2`, a path in the
`k`-skeleton with endpoints in the `1`-skeleton can be homotoped, relative to its endpoints, to a
path in the `k`-skeleton avoiding any prescribed finite set `O` of points of open `k`-cells.

The technical core is the chart of an open cell (see `skelChartAux.lean` and
`exists_isOpen_chartBall` below); the assembly of the target is at the end of the file.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## The chart of an open cell is open in the model -/

/-- **The chart of an open cell is open in the model.**

For a point `c` of the open cell of a face `S` (`ptSupport c = S`, `2 < S.card`) the chart map
`topMap D i : y ↦ [Sum.inl ⟨i,y⟩]` maps the ball of `c` in the stratum of `S` onto the trace, on
the `(S.card - 1)`-skeleton, of an open subset of the model. -/
theorem exists_isOpen_chartBall {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    (hS : 2 < S.card) {c : stdSimplex ℝ (Fin (n + 2))} (hc : ptSupport c = S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (Model D), IsOpen U ∧ U ∩ skel D (S.card - 1)
      = topMap D i '' setOf (fun y : stdSimplex ℝ (Fin (n + 2)) =>
          ptSupport y = S ∧ ‖(y : Fin (n + 2) → ℝ) - (c : Fin (n + 2) → ℝ)‖ < ε) := by
  classical
  set W : Set (stdSimplex ℝ (Fin (n + 2))) := setOf (fun y : stdSimplex ℝ (Fin (n + 2)) =>
    ptSupport y = S ∧ ‖(y : Fin (n + 2) → ℝ) - (c : Fin (n + 2) → ℝ)‖ < ε) with hW
  have hWmem : ∀ x : stdSimplex ℝ (Fin (n + 2)), x ∈ W ↔
      (ptSupport x = S ∧ ‖(x : Fin (n + 2) → ℝ) - (c : Fin (n + 2) → ℝ)‖ < ε) := fun x => Iff.rfl
  -- the support of a point of the chart part is `S`, so the cardinals match
  have hcard_of_mem : ∀ {j : D.Idx} {T : Finset (Fin (n + 2))}
      {y : stdSimplex ℝ (Fin (n + 2))} {h : ptSupport y = T}
      {ρ : {t // t ∈ T} → Fin (n + 2)} {hρ : ChainTrans D j T i ρ},
      transportPt y h ρ (chainTransStrictMono D hρ).injective ∈ W → T.card = S.card := by
    intro j T y h ρ hρ hb
    have h1 : ptSupport (transportPt y h ρ (chainTransStrictMono D hρ).injective) = S :=
      (hWmem _).mp hb |>.1
    rw [transportPtSupp] at h1
    have h2 : (Finset.image ρ T.attach).card = T.card := by
      rw [Finset.card_image_of_injective _ (chainTransStrictMono D hρ).injective,
        Finset.card_attach]
    rw [← h2, h1]
  -- membership in the first part is a union of classes
  have hsat1 : ∀ {a a' : Raw D}, Relation.EqvGen (modelRel D) a a' →
      (∃ (j : D.Idx) (T : Finset (Fin (n + 2))) (y : stdSimplex ℝ (Fin (n + 2)))
        (h : ptSupport y = T) (ρ : {t // t ∈ T} → Fin (n + 2)) (hρ : ChainTrans D j T i ρ),
        (a' = Sum.inl (⟨j, y⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))) ∧
          transportPt y h ρ (chainTransStrictMono D hρ).injective ∈ W)) →
      ∃ (j : D.Idx) (T : Finset (Fin (n + 2))) (y : stdSimplex ℝ (Fin (n + 2)))
        (h : ptSupport y = T) (ρ : {t // t ∈ T} → Fin (n + 2)) (hρ : ChainTrans D j T i ρ),
        (a = Sum.inl (⟨j, y⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))) ∧
          transportPt y h ρ (chainTransStrictMono D hρ).injective ∈ W) := by
    rintro a a' hrel ⟨j, T, y, h, ρ, hρ, ha', hb⟩
    have hTcard : T.card = S.card :=
      hcard_of_mem (j := j) (T := T) (y := y) (h := h) (ρ := ρ) (hρ := hρ) hb
    have hwt : rawWeight D a = S.card := by
      rw [rawWeight_eqvGen D hrel, ha', rawWeight_inl, h, hTcard]
    obtain ⟨j', y', haeq⟩ := exists_eq_inl_of_rawWeight_ne_one (D := D) (by rw [hwt]; omega)
    have hb' : transportPt y h ρ (chainTransStrictMono D hρ).injective ∈ W := hb
    have hchain : Relation.EqvGen (modelRel D)
        (Sum.inl (⟨j, y⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))))
        (Sum.inl (⟨i, transportPt y h ρ (chainTransStrictMono D hρ).injective⟩ :
          Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2)))) :=
      chainTrans_class D h hρ _
    have hrel2 : Relation.EqvGen (modelRel D)
        (Sum.inl (⟨j', y'⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))))
        (Sum.inl (⟨i, transportPt y h ρ (chainTransStrictMono D hρ).injective⟩ :
          Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2)))) := by
      rw [← haeq]
      refine Relation.EqvGen.trans (x := a) (y := a')
        (z := Sum.inl (⟨i, transportPt y h ρ (chainTransStrictMono D hρ).injective⟩ :
          Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2)))) hrel ?_
      rw [ha']
      exact hchain
    have hy'card : (ptSupport y').card = S.card := by
      have h2 := hwt
      rw [haeq, rawWeight_inl] at h2
      exact h2
    obtain ⟨j₁, τ, hτ, hCT, heq2⟩ :=
      (chainTrans D j' (ptSupport y') (by omega) y' rfl (Sum.inl (⟨i, transportPt y h ρ
        (chainTransStrictMono D hρ).injective⟩ : Sigma fun _ : D.Idx =>
          stdSimplex ℝ (Fin (n + 2))))).mp hrel2
    have hj₁ : j₁ = i := (congrArg Sigma.fst (Sum.inl.inj heq2)).symm
    have hval : transportPt y' rfl τ hτ = transportPt y h ρ
        (chainTransStrictMono D hρ).injective :=
      (eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj heq2)).2).symm
    rw [hj₁] at hCT
    exact ⟨j', ptSupport y', y', rfl, τ, hCT, haeq, by rw [hval]; exact hb'⟩
  set A : Set (Raw D) :=
    setOf (fun a : Raw D => ∃ (j : D.Idx) (T : Finset (Fin (n + 2)))
        (y : stdSimplex ℝ (Fin (n + 2))) (h : ptSupport y = T)
        (ρ : {t // t ∈ T} → Fin (n + 2)) (hρ : ChainTrans D j T i ρ),
        a = Sum.inl (⟨j, y⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))) ∧
          transportPt y h ρ (chainTransStrictMono D hρ).injective ∈ W)
      ∪ setOf (fun a : Raw D => S.card + 1 ≤ rawWeight D a) with hA
  have hAsat : Quotient.mk'' ⁻¹' (Quotient.mk'' '' A : Set (Model D)) = A := by
    ext a
    constructor
    · rintro ⟨a', ha', heq⟩
      have hrel : Relation.EqvGen (modelRel D) a a' := (Quotient.exact heq).symm
      rcases ha' with ha' | hw
      · exact Or.inl (hsat1 hrel ha')
      · exact Or.inr (show S.card + 1 ≤ rawWeight D a from by
          rw [rawWeight_eqvGen D hrel]; exact hw)
    · intro ha
      exact ⟨a, ha, rfl⟩
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro a (ha | hwge)
    · obtain ⟨j, T, y, h, ρ, hρ, ha, hb⟩ := ha
      have hTcard : T.card = S.card :=
      hcard_of_mem (j := j) (T := T) (y := y) (h := h) (ρ := ρ) (hρ := hρ) hb
      have hTinj := (chainTransStrictMono D hρ).injective
      have hbε : dist ((transportPt y h ρ hTinj : Fin (n + 2) → ℝ)) ((c : Fin (n + 2) → ℝ)) < ε :=
        (hWmem _).mp hb |>.2
      -- the continuity radius around `y`
      set η : ℝ := ε - dist ((transportPt y h ρ hTinj : Fin (n + 2) → ℝ))
        ((c : Fin (n + 2) → ℝ)) with hη
      have hηpos : 0 < η := by rw [hη]; linarith
      obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧
          ∀ z : {w : stdSimplex ℝ (Fin (n + 2)) // ptSupport w = T},
            dist z ⟨y, h⟩ < δ →
              dist (transportPt z.1 z.2 ρ hTinj : Fin (n + 2) → ℝ)
                (transportPt y h ρ hTinj : Fin (n + 2) → ℝ) < η :=
        Metric.continuousAt_iff.mp
          (show ContinuousAt (fun z : {w : stdSimplex ℝ (Fin (n + 2)) // ptSupport w = T} =>
              (transportPt z.1 z.2 ρ hTinj : Fin (n + 2) → ℝ)) ⟨y, h⟩ from
            (continuous_transportPt (T := T) (τ := ρ) hTinj).continuousAt) η hηpos
      have hne : (ptSupport y).Nonempty := Finset.card_pos.mp (by rw [h, hTcard]; omega)
      set m : ℝ := Finset.inf' (ptSupport y) hne (fun t => (y : Fin (n + 2) → ℝ) t) with hm
      have hmpos : 0 < m := by
        rw [hm, Finset.lt_inf'_iff]
        intro t ht
        exact lt_of_le_of_ne (y.2.1 t) (Ne.symm (mem_ptSupport.mp ht))
      set δ' : ℝ := min δ m with hδ'
      have hδ'pos : 0 < δ' := lt_min hδpos hmpos
      rw [ha]
      refine Filter.mem_of_superset
        ((isOpen_rawBall D j y δ').mem_nhds (by
          rw [mem_rawBall]
          exact ⟨rfl, by rw [dist_self]; exact hδ'pos⟩)) ?_
      rintro a' ha'
      rw [rawBall] at ha'
      obtain ⟨⟨j', y'⟩, ⟨hpj, hpd⟩, hpa⟩ := ha'
      have hpj' : (Sum.inl (⟨j', y'⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))) :
          Raw D) = Sum.inl (⟨j, y'⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))) := by
        rw [show (⟨j', y'⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))) = ⟨j, y'⟩ from
          Sigma.ext hpj (HEq.refl _)]
      rw [← hpa, hpj']
      by_cases hw : S.card + 1 ≤ rawWeight D (Sum.inl (⟨j, y'⟩ : Sigma fun _ : D.Idx =>
        stdSimplex ℝ (Fin (n + 2))))
      · exact Or.inr hw
      · refine Or.inl ?_
        have hsub : ptSupport y ⊆ ptSupport y' := by
          intro t ht
          have h1 : |(y' : Fin (n + 2) → ℝ) t - (y : Fin (n + 2) → ℝ) t| ≤
              dist (y' : stdSimplex ℝ (Fin (n + 2))) y := by
            rw [Subtype.dist_eq, dist_eq_norm]
            have h2 := norm_le_pi_norm (fun s : Fin (n + 2) =>
              (y' : Fin (n + 2) → ℝ) s - (y : Fin (n + 2) → ℝ) s) t
            rwa [Real.norm_eq_abs] at h2
          have h2 : dist (y' : stdSimplex ℝ (Fin (n + 2))) y < m :=
            lt_of_lt_of_le hpd (min_le_right _ _)
          have h3 : m ≤ (y : Fin (n + 2) → ℝ) t := by
            rw [hm]
            exact Finset.inf'_le _ ht
          have h4 : |(y' : Fin (n + 2) → ℝ) t - (y : Fin (n + 2) → ℝ) t|
              < (y : Fin (n + 2) → ℝ) t := lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)
          have h5 := (abs_lt.mp h4).1
          exact mem_ptSupport.mpr (ne_of_gt (by linarith))
        have hle : (ptSupport y').card ≤ (ptSupport y).card := by
          have h' := hw
          rw [rawWeight_inl] at h'
          rw [h, hTcard]
          omega
        have hEq : ptSupport y' = T := by
          have h1 : ptSupport y' = ptSupport y :=
            (Finset.eq_of_subset_of_card_le hsub hle).symm
          rw [h1, h]
        refine ⟨j, T, y', hEq, ρ, hρ, rfl, ?_⟩
        rw [hWmem]
        have hsupp : ptSupport (transportPt y' hEq ρ hTinj) = S := by
          rw [transportPtSupp, ← transportPtSupp y h ρ hTinj]
          exact (hWmem _).mp hb |>.1
        refine ⟨hsupp, ?_⟩
        have hdist : dist (transportPt y' hEq ρ hTinj) (transportPt y h ρ hTinj) < η :=
          hδ ⟨y', hEq⟩ (by
            rw [Subtype.dist_eq]
            exact lt_of_lt_of_le hpd (min_le_left _ _))
        show dist ((transportPt y' hEq ρ hTinj : Fin (n + 2) → ℝ)) ((c : Fin (n + 2) → ℝ)) < ε
        calc dist ((transportPt y' hEq ρ hTinj : Fin (n + 2) → ℝ)) ((c : Fin (n + 2) → ℝ))
            ≤ dist ((transportPt y' hEq ρ hTinj : Fin (n + 2) → ℝ))
                ((transportPt y h ρ hTinj : Fin (n + 2) → ℝ))
              + dist ((transportPt y h ρ hTinj : Fin (n + 2) → ℝ)) ((c : Fin (n + 2) → ℝ)) :=
              dist_triangle _ _ _
          _ < η + dist ((transportPt y h ρ hTinj : Fin (n + 2) → ℝ))
                ((c : Fin (n + 2) → ℝ)) := by
              exact add_lt_add_of_lt_of_le hdist le_rfl
          _ = ε := by rw [hη]; ring
    · have hQopen : IsOpen (setOf (fun a : Raw D => S.card + 1 ≤ rawWeight D a)) :=
        isOpen_rawWeight_ge' D (S.card + 1)
      exact Filter.mem_of_superset (hQopen.mem_nhds hwge) (fun x hx => Or.inr hx)
  refine ⟨Quotient.mk'' '' A, ?_, ?_⟩
  · have hq : Topology.IsCoinducing (Quotient.mk'' : Raw D → Model D) :=
      (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (modelRel D))).isCoinducing
    exact hq.isOpen_preimage.1 (by rw [hAsat]; exact hAopen)
  · ext z
    constructor
    · rintro ⟨hzU, hzsk⟩
      obtain ⟨a, haA, rfl⟩ := hzU
      have hw : rawWeight D a ≤ S.card := by
        obtain ⟨b, hb, hbw⟩ := (mem_skel_iff (D := D)).mp hzsk
        have hqab : (Quotient.mk'' a : Model D) = Quotient.mk'' b := hb.symm
        have h1 : rawWeight D a = rawWeight D b := rawWeight_eqvGen D (Quotient.exact hqab)
        have h2 : S.card - 1 + 1 = S.card := Nat.sub_add_cancel (by omega)
        omega
      rcases haA with ha | hwge
      · obtain ⟨j, T, y, h, ρ, hρ, ha, hb⟩ := ha
        refine ⟨transportPt y h ρ (chainTransStrictMono D hρ).injective, hb, ?_⟩
        have hchain : Relation.EqvGen (modelRel D)
            (Sum.inl (⟨j, y⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))))
            (Sum.inl (⟨i, transportPt y h ρ (chainTransStrictMono D hρ).injective⟩ :
              Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2)))) :=
          chainTrans_class D h hρ _
        rw [ha]
        exact (Quotient.sound hchain).symm
      · exfalso
        have hwge' : S.card + 1 ≤ rawWeight D a := hwge
        exact absurd hwge' (by omega)
    · rintro ⟨x, hxW, rfl⟩
      obtain ⟨hxS, -⟩ := (hWmem x).mp hxW
      refine ⟨⟨Sum.inl (⟨i, x⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))),
        Or.inl ⟨i, S, x, hxS, fun t => t.1, ChainTrans.refl, rfl, ?_⟩, rfl⟩, ?_⟩
      · rw [hWmem]
        rw [transportPt_id]
        exact hxW
      · exact (mem_skel_iff (D := D)).mpr ⟨Sum.inl (⟨i, x⟩ : Sigma fun _ : D.Idx =>
          stdSimplex ℝ (Fin (n + 2))), rfl, by
            rw [rawWeight_inl, hxS, Nat.sub_add_cancel (by omega)]⟩


/-! ## A general form of the openness of the chart

`exists_isOpen_chartBall` gives the openness of a *ball* of a stratum.  Since the balls form a basis
of the stratum, the image of any open subset of the stratum is open in the skeleton; this is the
form in which the openness is used below (it gives that the chart map is an open map, hence that its
inverse is continuous on its range). -/

/-- The chart image of a ball of a stratum, in the explicit form used by
`exists_isOpen_chartBall`. -/
theorem chartImage_chartBall_eq {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    {c : stdSimplex ℝ (Fin (n + 2))} {ε : ℝ} :
    chartImage D i S (chartBall S c ε)
      = topMap D i '' setOf (fun y : stdSimplex ℝ (Fin (n + 2)) =>
          ptSupport y = S ∧ ‖(y : Fin (n + 2) → ℝ) - (c : Fin (n + 2) → ℝ)‖ < ε) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.1, ⟨?_, ?_⟩, rfl⟩
    · rw [← suppOf_eq_ptSupport]; exact x.2
    · rw [mem_chartBall] at hx
      rwa [Subtype.dist_eq, dist_eq_norm] at hx
  · rintro ⟨y, ⟨hyS, hyd⟩, rfl⟩
    refine ⟨⟨y, by rw [suppOf_eq_ptSupport]; exact hyS⟩, ?_, rfl⟩
    rw [mem_chartBall, Subtype.dist_eq, dist_eq_norm]
    exact hyd

/-- **The image of an open subset of a stratum is open in the skeleton.** -/
theorem exists_isOpen_chartImage {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    (hS : 2 < S.card) {N : Set (stratum S)} (hN : IsOpen N) :
    ∃ U : Set (Model D), IsOpen U ∧ U ∩ skel D (S.card - 1) = chartImage D i S N := by
  classical
  -- a chart ball around each point of `N`, contained in `N`
  have hball : ∀ x : ↥N, ∃ ε : ℝ, 0 < ε ∧ chartBall S (x.1 : stratum S).1 ε ⊆ N := by
    intro x
    obtain ⟨ε, hε, hεN⟩ := exists_dist_lt_of_isOpen hN x.2
    exact ⟨ε, hε, fun y hy => hεN y (mem_chartBall.mp hy)⟩
  choose ε hεpos hεsub using hball
  -- the open pieces
  have hpiece : ∀ x : ↥N, ∃ U : Set (Model D), IsOpen U ∧
      U ∩ skel D (S.card - 1) = chartImage D i S (chartBall S (x.1 : stratum S).1 (ε x)) := by
    intro x
    have hc : ptSupport ((x.1 : stratum S).1 : stdSimplex ℝ (Fin (n + 2))) = S := by
      rw [← suppOf_eq_ptSupport]; exact x.1.2
    simpa only [chartImage_chartBall_eq] using
      exists_isOpen_chartBall (D := D) hS (c := (x.1 : stratum S).1) hc (hεpos x)
  choose U hUopen hUeq using hpiece
  refine ⟨⋃ x : ↥N, U x, isOpen_iUnion hUopen, ?_⟩
  ext z
  constructor
  · rintro ⟨hzU, hzsk⟩
    obtain ⟨x, hxU⟩ := Set.mem_iUnion.mp hzU
    have hmem : z ∈ U x ∩ skel D (S.card - 1) := ⟨hxU, hzsk⟩
    rw [hUeq x] at hmem
    obtain ⟨y, hy, hyeq⟩ := hmem
    exact ⟨y, hεsub x hy, hyeq⟩
  · rintro ⟨y, hyN, hyeq⟩
    refine ⟨Set.mem_iUnion.mpr ⟨⟨y, hyN⟩, ?_⟩, ?_⟩
    · have hmem : chartMap D i S y ∈
          chartImage D i S (chartBall S (y.1 : stdSimplex ℝ (Fin (n + 2))) (ε ⟨y, hyN⟩)) :=
        ⟨y, by rw [mem_chartBall, dist_self]; exact hεpos ⟨y, hyN⟩, rfl⟩
      rw [← hUeq ⟨y, hyN⟩] at hmem
      rw [← hyeq]; exact hmem.1
    · rw [← hyeq]; exact chartImage_subset_skel D i S N ⟨y, hyN, rfl⟩

/-! ## The segment in a stratum -/

theorem stratumCombo_zero {S : Finset (Fin (n + 2))} (x y : stratum S) (h0 : (0 : ℝ) ≤ 0)
    (h1 : (0 : ℝ) ≤ 1) : stratumCombo x y 0 h0 h1 = x := by
  have hk : ∀ k : Fin (n + 2),
      (stratumCombo x y 0 h0 h1).1.1 k = (x.1.1 : Fin (n + 2) → ℝ) k := by
    intro k
    show (1 - (0 : ℝ)) * (x.1 : Fin (n + 2) → ℝ) k
        + (0 : ℝ) * (y.1 : Fin (n + 2) → ℝ) k = (x.1 : Fin (n + 2) → ℝ) k
    ring
  exact Subtype.ext (Subtype.ext (funext hk))

theorem stratumCombo_one {S : Finset (Fin (n + 2))} (x y : stratum S) (h0 : (0 : ℝ) ≤ 1)
    (h1 : (1 : ℝ) ≤ 1) : stratumCombo x y 1 h0 h1 = y := by
  have hk : ∀ k : Fin (n + 2),
      (stratumCombo x y 1 h0 h1).1.1 k = (y.1.1 : Fin (n + 2) → ℝ) k := by
    intro k
    show (1 - (1 : ℝ)) * (x.1 : Fin (n + 2) → ℝ) k
        + (1 : ℝ) * (y.1 : Fin (n + 2) → ℝ) k = (y.1 : Fin (n + 2) → ℝ) k
    ring
  exact Subtype.ext (Subtype.ext (funext hk))

theorem stratumCombo_self {S : Finset (Fin (n + 2))} (u : stratum S) (s : ℝ) (h0 : 0 ≤ s)
    (h1 : s ≤ 1) : stratumCombo u u s h0 h1 = u := by
  have hk : ∀ k : Fin (n + 2),
      (stratumCombo u u s h0 h1).1.1 k = (u.1.1 : Fin (n + 2) → ℝ) k := by
    intro k
    show (1 - s) * (u.1 : Fin (n + 2) → ℝ) k + s * (u.1 : Fin (n + 2) → ℝ) k
        = (u.1 : Fin (n + 2) → ℝ) k
    ring
  exact Subtype.ext (Subtype.ext (funext hk))

/-! ## The compression, with the range information

`Work.RatHurewicz.Cofibre.path_compress_twoSet` compresses a path into the set `U` of a two-set
cover `U ∪ V`.  When such a compression is used repeatedly (to push a path off the points of a
finite set, one at a time), one needs to know that the compressing path does not create new points
except inside `V`: every point of `q` lies in the image of `p` or in `V`.  This is a straightforward
strengthening of the construction --- each sub-path of the compressed path is either a sub-path of
`p` or a path in `V` --- carried out here. -/

namespace Rng

open scoped unitInterval

set_option linter.unusedVariables false

/-- A point of the sub-path of `f` from `a` to `b` lies in the image of `f`. -/
theorem pcSeg_mem_range {X : Type*} [TopologicalSpace X] (f : C(ℝ, X)) (a b : ℝ) (s : I) :
    Cofibre.pcSeg f a b s ∈ Set.range f :=
  Set.mem_range.mpr ⟨a + (b - a) * (s : ℝ), rfl⟩

/-- `PcAux` with the extra conclusion that the compressed path stays in the image of `f` together
with `V`. -/
def PcAuxR {X : Type*} [TopologicalSpace X] (U V : Set X) (N : ℕ) : Prop :=
  ∀ (f : C(ℝ, X)) (g : ℕ → ℝ), (∀ k < N, g k < g (k + 1)) →
    ∀ (b : ℕ → Bool), (∀ k < N, ∀ t : ℝ, g k ≤ t → t ≤ g (k + 1) → f t ∈ cond (b k) V U) →
    f (g 0) ∈ U → f (g N) ∈ U →
    ∃ q : Path (f (g 0)) (f (g N)),
      (∀ s, q s ∈ U) ∧ (∀ s, q s ∈ Set.range f ∪ V) ∧
        Nonempty (q.Homotopic (Cofibre.pcSeg f (g 0) (g N)))

theorem pcAuxR_all {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hUV : ∀ a b : ↥(U ∩ V), Nonempty (Path a b))
    (hVsc : ∀ {x y : X} (p q : Path x y), (∀ t, p t ∈ V) → (∀ t, q t ∈ V) →
      Nonempty (Path.Homotopic p q)) :
    ∀ N, PcAuxR U V N := by
  intro N
  refine Nat.strongRecOn (motive := PcAuxR U V) N ?_
  intro n ih f g hmono b hleg h0 hN
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    refine ⟨Path.refl (f (g 0)), (fun s => by simpa using h0), ?_, ?_⟩
    · intro s
      exact Or.inl (Set.mem_range.mpr ⟨g 0, (Path.refl_apply (f (g 0)) s).symm⟩)
    · exact ⟨⟨(Path.Homotopy.refl (Path.refl (f (g 0)))).cast rfl
        (Cofibre.pcSeg_self f (g 0)).symm⟩⟩
  · by_cases hb0 : b 0 = true
    · have hex : ∃ k, 1 ≤ k ∧ k ≤ n ∧ (k = n ∨ b k = false) :=
        ⟨n, by omega, le_rfl, Or.inl rfl⟩
      let j : ℕ := Nat.find hex
      have hjspec : 1 ≤ j ∧ j ≤ n ∧ (j = n ∨ b j = false) := Nat.find_spec hex
      have hjmin : ∀ k < j, ¬ (1 ≤ k ∧ k ≤ n ∧ (k = n ∨ b k = false)) :=
        fun k hk => Nat.find_min hex hk
      have hbV : ∀ k < j, b k = true := by
        intro k hk
        by_contra hc
        rw [Bool.not_eq_true] at hc
        by_cases h0k : k = 0
        · rw [h0k] at hc; rw [hc] at hb0; exact Bool.false_ne_true hb0
        · exact (hjmin k hk) ⟨Nat.pos_of_ne_zero h0k, by omega, Or.inr hc⟩
      have hjN : j ≤ n := hjspec.2.1
      have hcoV : ∀ t, g 0 ≤ t → t ≤ g j → f t ∈ V := by
        have hml := Cofibre.pcMem_of_legs (K := j) hjspec.1
          (fun k hk => le_of_lt (hmono k (by omega)))
          (fun k hk t h1 h2 => by
            have hh := hleg k (by omega) t h1 h2
            rwa [hbV k hk] at hh)
        exact fun t h1 h2 => hml j le_rfl t h1 h2
      have hg0V : f (g 0) ∈ V :=
        hcoV (g 0) le_rfl (Cofibre.pcGrid_mono hmono j hjN 0 (by omega))
      have hgjV : f (g j) ∈ V :=
        hcoV (g j) (Cofibre.pcGrid_mono hmono j hjN 0 (by omega)) le_rfl
      have hgjU : f (g j) ∈ U := by
        rcases hjspec.2.2 with h | h
        · rw [h]; exact hN
        · by_cases hlt : j < n
          · have hh := hleg j hlt (g j) le_rfl (le_of_lt (hmono j hlt))
            rwa [h] at hh
          · rw [le_antisymm hjN (by omega)]; exact hN
      obtain ⟨w⟩ := hUV ⟨f (g 0), h0, hg0V⟩ ⟨f (g j), hgjU, hgjV⟩
      have hwU : ∀ s, (w.map continuous_subtype_val) s ∈ U := fun s => (w s).2.1
      have hwV : ∀ s, (w.map continuous_subtype_val) s ∈ V := fun s => (w s).2.2
      have hwHom : Nonempty ((w.map continuous_subtype_val).Homotopic
          (Cofibre.pcSeg f (g 0) (g j))) :=
        hVsc _ _ hwV (Cofibre.pcSeg_mem (Cofibre.pcGrid_mono hmono j hjN 0 (by omega)) hcoV)
      have hab : g 0 < g n := lt_of_lt_of_le (hmono 0 (by omega))
        (Cofibre.pcGrid_mono hmono n le_rfl 1 (by omega))
      have ham : g 0 ≤ g j := Cofibre.pcGrid_mono hmono j hjN 0 (by omega)
      have hmb : g j ≤ g n := Cofibre.pcGrid_mono hmono n le_rfl j hjN
      have hNJ : (n - j) + j = n := by omega
      have h0'' : f ((Cofibre.pcGshift g j) 0) ∈ U := by
        simpa [Cofibre.pcGshift, Nat.zero_add] using hgjU
      have hN'' : f ((Cofibre.pcGshift g j) (n - j)) ∈ U := by
        simpa [Cofibre.pcGshift, hNJ] using hN
      have hmono'' : ∀ k < n - j, (Cofibre.pcGshift g j) k < (Cofibre.pcGshift g j) (k + 1) := by
        intro k hk
        show g (k + j) < g ((k + 1) + j)
        rw [show (k + 1) + j = (k + j) + 1 by omega]
        exact hmono (k + j) (by omega)
      have hleg'' : ∀ k < n - j, ∀ t : ℝ, (Cofibre.pcGshift g j) k ≤ t →
          t ≤ (Cofibre.pcGshift g j) (k + 1) → f t ∈ cond (b (k + j)) V U := by
        intro k hk t h1 h2
        have h2' : t ≤ g ((k + j) + 1) := by
          rw [show (k + j) + 1 = (k + 1) + j by omega]; exact h2
        exact hleg (k + j) (by omega) t h1 h2'
      obtain ⟨q_tail, hq_img, hq_range, hq_hom⟩ :=
        ih (n - j) (by omega) f (Cofibre.pcGshift g j) hmono''
          (fun k => b (k + j)) hleg'' h0'' hN''
      have haj : g j = (Cofibre.pcGshift g j) 0 := by simp [Cofibre.pcGshift]
      have hbj : g n = (Cofibre.pcGshift g j) (n - j) := by simp [Cofibre.pcGshift, hNJ]
      let qc : Path (f (g j)) (f (g n)) := q_tail.cast (congrArg f haj) (congrArg f hbj)
      have hqc_img : ∀ s, qc s ∈ U := by
        intro s; simpa [qc, Path.cast_coe] using hq_img s
      have hqc_range : ∀ s, qc s ∈ Set.range f ∪ V := by
        intro s; simpa [qc, Path.cast_coe] using hq_range s
      have hqc_hom : Nonempty (qc.Homotopic (Cofibre.pcSeg f (g j) (g n))) :=
        Cofibre.pcCastHomotopicSeg f haj hbj hq_hom
      refine ⟨(w.map continuous_subtype_val).trans qc, ?_, ?_, ?_⟩
      · intro s
        rw [Path.trans_apply]
        split_ifs with hs
        · exact hwU _
        · exact hqc_img _
      · intro s
        rw [Path.trans_apply]
        split_ifs with hs
        · exact Or.inr ((w _).2.2)
        · exact hqc_range _
      · obtain ⟨hwh⟩ := hwHom
        obtain ⟨hqh⟩ := hqc_hom
        exact ⟨(Path.Homotopic.hcomp hwh hqh).trans
          (Cofibre.pcSegTransPcSegHomotopic f hab ham hmb)⟩
    · have hb0' : b 0 = false := by
        rw [Bool.not_eq_true] at hb0; exact hb0
      have hab : g 0 < g n := lt_of_lt_of_le (hmono 0 (by omega))
        (Cofibre.pcGrid_mono hmono n le_rfl 1 (by omega))
      have hg01 : g 0 ≤ g 1 := le_of_lt (hmono 0 (by omega))
      have hg1n : g 1 ≤ g n := Cofibre.pcGrid_mono hmono n le_rfl 1 (by omega)
      have hnz : (n - 1) + 1 = n := by omega
      have h0' : f ((Cofibre.pcGshift g 1) 0) ∈ U := by
        have hh := hleg 0 (by omega) (g 1) hg01 le_rfl
        simpa [Cofibre.pcGshift, hb0'] using hh
      have hN' : f ((Cofibre.pcGshift g 1) (n - 1)) ∈ U := by
        simpa [Cofibre.pcGshift, hnz] using hN
      have hmono1 : ∀ k < n - 1, (Cofibre.pcGshift g 1) k < (Cofibre.pcGshift g 1) (k + 1) := by
        intro k hk
        show g (k + 1) < g ((k + 1) + 1)
        exact hmono (k + 1) (by omega)
      have hleg1 : ∀ k < n - 1, ∀ t : ℝ, (Cofibre.pcGshift g 1) k ≤ t →
          t ≤ (Cofibre.pcGshift g 1) (k + 1) → f t ∈ cond (b (k + 1)) V U := by
        intro k hk
        exact hleg (k + 1) (by omega)
      obtain ⟨q_tail, hq_img, hq_range, hq_hom⟩ :=
        ih (n - 1) (by omega) f (Cofibre.pcGshift g 1) hmono1
          (fun k => b (k + 1)) hleg1 h0' hN'
      have ha1 : g 1 = (Cofibre.pcGshift g 1) 0 := by simp [Cofibre.pcGshift]
      have hb1 : g n = (Cofibre.pcGshift g 1) (n - 1) := by simp [Cofibre.pcGshift, hnz]
      let qc : Path (f (g 1)) (f (g n)) := q_tail.cast (congrArg f ha1) (congrArg f hb1)
      have hqc_img : ∀ s, qc s ∈ U := by
        intro s; simpa [qc, Path.cast_coe] using hq_img s
      have hqc_range : ∀ s, qc s ∈ Set.range f ∪ V := by
        intro s; simpa [qc, Path.cast_coe] using hq_range s
      have hqc_hom : Nonempty (qc.Homotopic (Cofibre.pcSeg f (g 1) (g n))) :=
        Cofibre.pcCastHomotopicSeg f ha1 hb1 hq_hom
      refine ⟨(Cofibre.pcSeg f (g 0) (g 1)).trans qc, ?_, ?_, ?_⟩
      · intro s
        rw [Path.trans_apply]
        split_ifs with hs
        · exact Cofibre.pcSeg_mem hg01 (fun t h1 h2 => by
            have hh := hleg 0 (by omega) t h1 h2
            simpa [hb0'] using hh) _
        · exact hqc_img _
      · intro s
        rw [Path.trans_apply]
        split_ifs with hs
        · exact Or.inl (pcSeg_mem_range f (g 0) (g 1) _)
        · exact hqc_range _
      · obtain ⟨hqh⟩ := hqc_hom
        exact ⟨(Path.Homotopic.hcomp
          (Path.Homotopic.refl (Cofibre.pcSeg f (g 0) (g 1))) hqh).trans
          (Cofibre.pcSegTransPcSegHomotopic f hab hg01 hg1n)⟩

/-- The compression of a path into `U` along the cover `U ∪ V`, with the additional information
that every point of the compressed path lies in the image of `p` or in `V`. -/
theorem path_compress_twoSetR {X : Type} [TopologicalSpace X] {U V : Set X}
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hUV : ∀ a b : ↥(U ∩ V), Nonempty (Path a b))
    (hVsc : ∀ {x y : X} (p q : Path x y), (∀ t, p t ∈ V) → (∀ t, q t ∈ V) →
      Nonempty (Path.Homotopic p q))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (p : Path x y) (hpU : IsOpen (p ⁻¹' U)) :
    ∃ q : Path x y, (∀ t, q t ∈ U) ∧ (∀ t, q t ∈ Set.range p ∪ V) ∧
      Nonempty (p.Homotopic q) := by
  classical
  have hcopen : ∀ i : Bool, IsOpen (p ⁻¹' (cond i V U) : Set I) := by
    intro i
    cases i
    · exact hpU
    · exact hV.preimage p.continuous
  have hcover : (Set.univ : Set I) ⊆ ⋃ i : Bool, (p ⁻¹' (cond i V U) : Set I) := by
    intro t _
    rcases (show p t ∈ U ∨ p t ∈ V from by
      have := Set.eq_univ_iff_forall.mp hcov (p t)
      simpa [Set.mem_union] using this) with h | h
    · exact Set.mem_iUnion.mpr ⟨false, h⟩
    · exact Set.mem_iUnion.mpr ⟨true, h⟩
  obtain ⟨δ, hδpos, hδ⟩ :=
    lebesgue_number_lemma_of_metric (s := (Set.univ : Set I)) isCompact_univ hcopen hcover
  obtain ⟨mn, hmn⟩ := exists_nat_one_div_lt hδpos
  let N : ℕ := mn + 1
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNd : (1 : ℝ) / N < δ := by
    have hcast : ((mn : ℝ) + 1) = (N : ℝ) := by simp [N]
    rw [← hcast]; exact hmn
  let g : ℕ → ℝ := fun k => (k : ℝ) / N
  have hg0 : g 0 = 0 := by simp [g]
  have hgN : g N = 1 := by
    show (N : ℝ) / N = 1
    field_simp
  have hmono : ∀ k < N, g k < g (k + 1) := by
    intro k hk
    show (k : ℝ) / N < ((k + 1 : ℕ) : ℝ) / N
    have h2 : (k : ℝ) < ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact div_lt_div_of_pos_right h2 hNR
  let mid : ∀ k : ℕ, k < N → I := fun k hk => ⟨((k : ℝ) + 1 / 2) / N, by
    have hk1 : k + 1 ≤ N := by omega
    have h1 : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk1
    constructor
    · exact div_nonneg (by positivity) (le_of_lt hNR)
    · rw [div_le_one hNR]; linarith⟩
  let b : ℕ → Bool := fun k =>
    if hk : k < N then Classical.choose (hδ (mid k hk) (Set.mem_univ _)) else false
  have hleg : ∀ k < N, ∀ t : ℝ, g k ≤ t → t ≤ g (k + 1) → p.extend t ∈ cond (b k) V U := by
    intro k hk t ht1 ht2
    have hspec := Classical.choose_spec (hδ (mid k hk) (Set.mem_univ _))
    have hk1 : k + 1 ≤ N := by omega
    have hc1 : (0 : ℝ) ≤ (k : ℝ) / N := by positivity
    have hc2 : ((k + 1 : ℕ) : ℝ) / N ≤ 1 := by
      rw [div_le_one hNR]
      exact_mod_cast hk1
    have htI : t ∈ I :=
      ⟨le_trans (by simpa [g] using hc1) ht1, le_trans ht2 (by simpa [g] using hc2)⟩
    have hball : (⟨t, htI⟩ : I) ∈ Metric.ball (mid k hk) δ := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      have hm1 : (k : ℝ) ≤ N * t := by
        have h1 : (k : ℝ) / N ≤ t := ht1
        rw [div_le_iff₀ hNR] at h1
        linarith
      have hm2 : N * t ≤ (k : ℝ) + 1 := by
        have h2 : t ≤ ((k + 1 : ℕ) : ℝ) / N := ht2
        rw [le_div_iff₀ hNR] at h2
        push_cast at h2
        linarith
      have hkey : |N * t - (k : ℝ) - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]; constructor <;> linarith
      have heq : t - ((k : ℝ) + 1 / 2) / N = (N * t - (k : ℝ) - 1 / 2) / N := by
        field_simp
        ring
      have hlt : (1 : ℝ) / (2 * N) < δ := by
        have hh : (1 : ℝ) / (2 * N) = (1 / 2) / N := by field_simp
        have hle : (1 : ℝ) / (2 * N) < 1 / N := by
          rw [hh, div_lt_div_iff_of_pos_right hNR]; norm_num
        linarith
      have hkey' : |N * t - (k : ℝ) - 1 / 2| / N ≤ (1 / 2) / N :=
        div_le_div_of_nonneg_right hkey (le_of_lt hNR)
      have hhalf2 : (1 / 2) / N = (1 : ℝ) / (2 * N) := by field_simp
      rw [heq, abs_div, abs_of_pos hNR]
      linarith
    have hmem : p ⟨t, htI⟩ ∈ cond (Classical.choose (hδ (mid k hk) (Set.mem_univ _))) V U :=
      hspec hball
    simpa [b, dif_pos hk, Path.extend_apply p htI] using hmem
  have h0g : p.extend (g 0) ∈ U := by rw [hg0, p.extend_zero]; exact hx
  have hNg : p.extend (g N) ∈ U := by rw [hgN, p.extend_one]; exact hy
  obtain ⟨q, hqU, hqR, hqHom⟩ :=
    pcAuxR_all hUV hVsc N p.extend g hmono b hleg h0g hNg
  have hxg : x = p.extend (g 0) := by rw [hg0, p.extend_zero]
  have hyg : y = p.extend (g N) := by rw [hgN, p.extend_one]
  refine ⟨q.cast hxg hyg, ?_, ?_, ?_⟩
  · intro s
    rw [Path.cast_coe]
    exact hqU s
  · intro s
    have h2 := hqR s
    rw [Path.extend_range] at h2
    simpa [Path.cast_coe] using h2
  · obtain ⟨hqh⟩ := hqHom
    have hseg : (Cofibre.pcSeg p.extend (g 0) (g N)).cast hxg hyg = p := by
      ext s
      rw [Path.cast_coe]
      change p.extend (g 0 + (g N - g 0) * (s : ℝ)) = p s
      rw [hg0, hgN]
      simp only [zero_add, sub_zero, one_mul]
      exact (p.extend_apply s.2).trans (congrArg p (Subtype.ext rfl))
    have h2 := Path.Homotopic.pathCast hqh hxg hyg
    rw [hseg] at h2
    exact ⟨h2.symm⟩

end Rng

/-- A `Path.Homotopic` from a homotopy of continuous maps that is constant on the endpoints. -/
theorem homotopic_of_homotopyMap {Y : Type} [TopologicalSpace Y] {x y : Y} {p q : Path x y}
    (F : C(unitInterval × unitInterval, Y)) (h0 : ∀ t, F (0, t) = p t)
    (h1 : ∀ t, F (1, t) = q t) (hf0 : ∀ s, F (s, 0) = p 0) (hf1 : ∀ s, F (s, 1) = p 1) :
    p.Homotopic q :=
  ⟨{ toHomotopy := { toContinuousMap := F, map_zero_left := h0, map_one_left := h1 }
     prop' := by
       intro s x hx
       rcases hx with hx | hx
       · rw [hx]; exact hf0 s
       · rw [hx]; exact hf1 s }⟩

/-! ## Small chart balls avoid the other points -/

theorem chartImage_ball_mono {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    {c : stdSimplex ℝ (Fin (n + 2))} {ε ε' : ℝ} (h : ε' ≤ ε) :
    chartImage D i S (chartBall S c ε') ⊆ chartImage D i S (chartBall S c ε) := by
  rintro z ⟨y, hy, rfl⟩
  exact ⟨y, by rw [mem_chartBall] at hy ⊢; linarith, rfl⟩

theorem exists_chartBall_avoid_one {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    {c : stdSimplex ℝ (Fin (n + 2))} (hc : ptSupport c = S) {o' : Model D}
    (hne : o' ≠ Quotient.mk'' (Sum.inl ⟨i, c⟩)) :
    ∃ ε > 0, o' ∉ chartImage D i S (chartBall S c ε) := by
  classical
  have hsupp : suppOf c = S := by rw [suppOf_eq_ptSupport]; exact hc
  by_cases hmem : o' ∈ openCell D i S
  · rw [openCell, Set.mem_ofPred_eq] at hmem
    obtain ⟨w, hwS, hweq⟩ := hmem
    have hw : suppOf w = S := by rw [suppOf_eq_ptSupport]; exact hwS
    have hdist : 0 < dist w c := by
      rw [dist_pos]
      intro hcw
      have h1 : (⟨w, hw⟩ : stratum S) = ⟨c, hsupp⟩ := Subtype.ext hcw
      have h2 : o' = Quotient.mk'' (Sum.inl ⟨i, c⟩) := by
        rw [← hweq]
        rw [← chartMap_apply D i S ⟨w, hw⟩, h1, chartMap_apply D i S ⟨c, hsupp⟩]
      exact hne h2
    refine ⟨dist w c / 2, by linarith, fun hcon => ?_⟩
    obtain ⟨w', hw', hw'eq⟩ := mem_chartImage.mp hcon
    rw [mem_chartBall] at hw'
    have hsame : w' = (⟨w, hw⟩ : stratum S) := by
      apply chartMap_injective D i S
      rw [hw'eq]
      exact hweq.symm
    rw [hsame] at hw'
    linarith
  · refine ⟨1, one_pos, fun hcon => hmem ?_⟩
    obtain ⟨y, -, hyeq⟩ := mem_chartImage.mp hcon
    exact ⟨y.1, by rw [← suppOf_eq_ptSupport]; exact y.2, hyeq⟩

theorem exists_chartBall_avoid {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    {c : stdSimplex ℝ (Fin (n + 2))} (hc : ptSupport c = S) (T : Finset (Model D)) :
    (∀ o' ∈ T, o' ≠ Quotient.mk'' (Sum.inl ⟨i, c⟩)) →
    ∃ ε > 0, ∀ o' ∈ T, o' ∉ chartImage D i S (chartBall S c ε) := by
  classical
  refine Finset.induction_on T ?_ ?_
  · intro _
    exact ⟨1, one_pos, fun o' ho' => absurd ho' (Finset.notMem_empty o')⟩
  · intro a₁ s₁ ha₁ ih hT
    obtain ⟨ε₁, hε₁, hε₁a⟩ :=
      exists_chartBall_avoid_one (D := D) hc (hT a₁ (Finset.mem_insert_self a₁ s₁))
    obtain ⟨ε₂, hε₂, hε₂s⟩ :=
      ih (fun o' ho' => hT o' (Finset.mem_insert_of_mem ho'))
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun o' ho' => ?_⟩
    rcases Finset.mem_insert.mp ho' with rfl | ho'
    · exact fun hcon => hε₁a (chartImage_ball_mono (min_le_left _ _) hcon)
    · exact fun hcon => hε₂s o' ho' (chartImage_ball_mono (min_le_right _ _) hcon)

/-! ## Pushing a path off one point of an open cell -/

/-- **The single-point case.**  Given a point `o` of the open cell `(i, S)` (with `2 < S.card`), a
radius `ε > 0` and a path `p` in the `(S.card - 1)`-skeleton between two points of the `1`-skeleton
there is a path `q`, homotopic to `p` relative to its endpoints and still in the
`(S.card - 1)`-skeleton, which avoids `o`; moreover every point of `q` lies in the image of `p` or
in the chart ball of radius `ε` around `o` (the extra information used by the iteration over a
finite set). -/
theorem avoidOnePointR {D : MData X n x₀} {i : D.Idx} {S : Finset (Fin (n + 2))}
    (hS : 2 < S.card) {c : stdSimplex ℝ (Fin (n + 2))} (hc : ptSupport c = S)
    (o : Model D) (hceq : Quotient.mk'' (Sum.inl ⟨i, c⟩) = o) {ε : ℝ} (hε : 0 < ε)
    {y z : Model D} (hy : y ∈ skeleton D) (hz : z ∈ skeleton D) (p : Path y z)
    (hp : ∀ t, p t ∈ skel D (S.card - 1)) :
    ∃ q : Path y z, (∀ t, q t ≠ o) ∧ (∀ t, q t ∈ skel D (S.card - 1)) ∧
      Nonempty (Path.Homotopic p q) ∧
      (∀ t, q t ∈ Set.range p ∪ chartImage D i S (chartBall S c ε)) := by
  classical
  have hsupp : suppOf c = S := by rw [suppOf_eq_ptSupport]; exact hc
  -- ## 1. The chart map into the skeleton and its inverse
  let φ : stratum S → ↥(skel D (S.card - 1)) := fun x =>
    ⟨chartMap D i S x, chartImage_subset_skel D i S Set.univ ⟨x, Set.mem_univ x, rfl⟩⟩
  have hφcont : Continuous φ :=
    Continuous.subtype_mk (chartMap D i S).continuous
      (fun x => chartImage_subset_skel D i S Set.univ ⟨x, Set.mem_univ x, rfl⟩)
  have hφinj : Function.Injective φ :=
    fun x y h => chartMap_injective D i S (congrArg Subtype.val h)
  have hφopen : IsOpenMap φ := by
    intro N hN
    obtain ⟨U₀, hU₀open, hU₀eq⟩ := exists_isOpen_chartImage (D := D) hS hN
    have hset : φ '' N = Subtype.val ⁻¹' U₀ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hmem : chartMap D i S x ∈ chartImage D i S N := ⟨x, hx, rfl⟩
        have h2 : (φ x : Model D) ∈ U₀ ∩ skel D (S.card - 1) := by rw [hU₀eq]; exact hmem
        exact h2.1
      · intro hz
        have hmem : (z : Model D) ∈ chartImage D i S N := by
          have h3 : (z : Model D) ∈ U₀ ∩ skel D (S.card - 1) := ⟨hz, z.2⟩
          rwa [hU₀eq] at h3
        obtain ⟨x, hx, hxeq⟩ := hmem
        exact ⟨x, hx, Subtype.ext hxeq⟩
    rw [hset]
    exact hU₀open.preimage continuous_subtype_val
  let χ : ↥(skel D (S.card - 1)) → stratum S := fun z =>
    if h : ∃ x : stratum S, φ x = z then Classical.choose h else ⟨c, hsupp⟩
  have hχφ : Function.LeftInverse χ φ := by
    intro x
    have h : ∃ x' : stratum S, φ x' = φ x := ⟨x, rfl⟩
    change (if h : ∃ x' : stratum S, φ x' = φ x then Classical.choose h else ⟨c, hsupp⟩) = x
    rw [dif_pos h]
    exact hφinj (Classical.choose_spec h)
  have hφχ : ∀ z ∈ Set.range φ, φ (χ z) = z := by
    rintro z ⟨x, rfl⟩
    exact congrArg φ (hχφ x)
  have hχcont : ContinuousOn χ (Set.range φ) :=
    IsOpenMap.continuousOn_range_of_leftInverse hφopen hχφ
  -- ## 2. The two sets
  let V : Set ↥(skel D (S.card - 1)) := Subtype.val ⁻¹' (chartImage D i S (chartBall S c ε))
  let U : Set ↥(skel D (S.card - 1)) := {z | (z : Model D) ≠ o}
  have hVopen : IsOpen V := by
    obtain ⟨U₀, hU₀open, hU₀eq⟩ := exists_isOpen_chartImage (D := D) hS (isOpen_chartBall S c ε)
    have hset : V = Subtype.val ⁻¹' U₀ := by
      change Subtype.val ⁻¹' (chartImage D i S (chartBall S c ε)) = Subtype.val ⁻¹' U₀
      have h2 : (Subtype.val ⁻¹' (chartImage D i S (chartBall S c ε)) :
          Set ↥(skel D (S.card - 1))) = Subtype.val ⁻¹' (U₀ ∩ skel D (S.card - 1)) := by
        rw [hU₀eq]
      rw [h2]
      ext z
      simp only [Set.mem_preimage, Set.mem_inter_iff, z.2, and_true]
    rw [hset]
    exact hU₀open.preimage continuous_subtype_val
  have ho_skel : o ∈ skel D (S.card - 1) := by
    refine (mem_skel_iff (D := D) (k := S.card - 1)).mpr ⟨Sum.inl ⟨i, c⟩, ?_, ?_⟩
    · exact hceq
    · rw [rawWeight_inl, hc]; omega
  have hoV : (⟨o, ho_skel⟩ : ↥(skel D (S.card - 1))) ∈ V := by
    show (o : Model D) ∈ chartImage D i S (chartBall S c ε)
    exact ⟨⟨c, hsupp⟩, by rw [mem_chartBall, dist_self]; exact hε,
      by rw [chartMap_apply]; exact hceq⟩
  -- ## 3. `y` and `z` are not `o`
  have hy_ne : y ≠ o := by
    intro h
    have hy1 : y ∈ skel D 1 := by rw [skel_one_eq_skeleton]; exact hy
    obtain ⟨a, ha, hw⟩ := (mem_skel_iff (D := D)).mp hy1
    have hq : (Quotient.mk'' a : Model D) = Quotient.mk'' (Sum.inl ⟨i, c⟩) := by
      rw [ha, h, hceq.symm]
    have h2 : rawWeight D a = S.card := by
      rw [rawWeight_eqvGen D (Quotient.exact hq), rawWeight_inl, hc]
    omega
  have hz_ne : z ≠ o := by
    intro h
    have hz1 : z ∈ skel D 1 := by rw [skel_one_eq_skeleton]; exact hz
    obtain ⟨a, ha, hw⟩ := (mem_skel_iff (D := D)).mp hz1
    have hq : (Quotient.mk'' a : Model D) = Quotient.mk'' (Sum.inl ⟨i, c⟩) := by
      rw [ha, h, hceq.symm]
    have h2 : rawWeight D a = S.card := by
      rw [rawWeight_eqvGen D (Quotient.exact hq), rawWeight_inl, hc]
    omega
  have hyk : y ∈ skel D (S.card - 1) :=
    skel_mono (show 1 ≤ S.card - 1 by omega) (by rw [skel_one_eq_skeleton]; exact hy)
  have hzk : z ∈ skel D (S.card - 1) :=
    skel_mono (show 1 ≤ S.card - 1 by omega) (by rw [skel_one_eq_skeleton]; exact hz)
  -- ## 4. The path, in the skeleton subspace
  let p' : Path (⟨y, hyk⟩ : ↥(skel D (S.card - 1))) ⟨z, hzk⟩ :=
    { toFun := fun t => ⟨p t, hp t⟩
      continuous_toFun := Continuous.subtype_mk p.continuous hp
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  have hclosed : IsClosed ({o} : Set (Model D)) := by
    have h : topMap D i '' ({c} : Set (stdSimplex ℝ (Fin (n + 2)))) = ({o} : Set (Model D)) := by
      rw [Set.image_singleton]
      rw [Set.singleton_eq_singleton_iff]
      exact hceq
    rw [← h]
    exact isClosed_image_stratum_compact (D := D) hS isCompact_singleton (fun x hx => by
      rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hc)
  have hp'U : IsOpen (p' ⁻¹' U) := by
    have hset : p' ⁻¹' U = p ⁻¹' ({o} : Set (Model D))ᶜ := by
      ext t; exact Iff.rfl
    rw [hset]
    exact (hclosed.isOpen_compl).preimage p.continuous
  -- ## 5. The cover
  have hcov : U ∪ V = Set.univ := by
    ext z
    constructor
    · intro _; trivial
    · intro _
      by_cases h : (z : Model D) = o
      · right
        have hz_eq : z = ⟨o, ho_skel⟩ := Subtype.ext h
        rw [hz_eq]; exact hoV
      · exact Or.inl h
  -- ## 6. The punctured chart is path connected
  have hpc : IsPathConnected
      ((setOf (fun x : stdSimplex ℝ (Fin (n + 2)) => suppOf x = S ∧ dist x c < ε) \ {c})) :=
    pathConnected_punctured_simplex S (by omega) c hsupp hε
  have hUV : ∀ a b : ↥(U ∩ V), Nonempty (Path a b) := by
    intro a b
    have haV : (a.1 : Model D) ∈ chartImage D i S (chartBall S c ε) := Set.mem_preimage.mp a.2.2
    have hbV : (b.1 : Model D) ∈ chartImage D i S (chartBall S c ε) := Set.mem_preimage.mp b.2.2
    obtain ⟨xa, hxaN, hxaeq⟩ := mem_chartImage.mp haV
    obtain ⟨xb, hxbN, hxbeq⟩ := mem_chartImage.mp hbV
    have hxane : xa ≠ ⟨c, hsupp⟩ := by
      intro hh
      exact a.2.1 (by rw [← hxaeq, hh, chartMap_apply]; exact hceq)
    have hxbne : xb ≠ ⟨c, hsupp⟩ := by
      intro hh
      exact b.2.1 (by rw [← hxbeq, hh, chartMap_apply]; exact hceq)
    have hxad : dist xa.1 c < ε := mem_chartBall.mp hxaN
    have hxbd : dist xb.1 c < ε := mem_chartBall.mp hxbN
    have hxamem : xa.1 ∈ (setOf (fun x : stdSimplex ℝ (Fin (n + 2)) => suppOf x = S ∧ dist x c < ε)
        \ {c}) := ⟨⟨xa.2, hxad⟩, fun hh => hxane (Subtype.ext hh)⟩
    have hxbmem : xb.1 ∈ (setOf (fun x : stdSimplex ℝ (Fin (n + 2)) => suppOf x = S ∧ dist x c < ε)
        \ {c}) := ⟨⟨xb.2, hxbd⟩, fun hh => hxbne (Subtype.ext hh)⟩
    obtain ⟨γ, hγ⟩ := hpc.joinedIn xa.1 hxamem xb.1 hxbmem
    have hγsupp : ∀ t, suppOf (γ t) = S := fun t => (hγ t).1.1
    have hγne : ∀ t, γ t ≠ c := fun t => (hγ t).2
    have hUg : ∀ t : ↥I, φ ⟨γ t, hγsupp t⟩ ∈ U := by
      intro t
      show ((φ ⟨γ t, hγsupp t⟩ : ↥(skel D (S.card - 1))) : Model D) ≠ o
      intro hcon
      have hc' : chartMap D i S ⟨γ t, hγsupp t⟩ = o := hcon
      have heq : (⟨γ t, hγsupp t⟩ : stratum S) = ⟨c, hsupp⟩ := by
        apply chartMap_injective D i S
        rw [hc', chartMap_apply]
        exact hceq.symm
      exact hγne t (congrArg Subtype.val heq)
    have hVg : ∀ t : ↥I, φ ⟨γ t, hγsupp t⟩ ∈ V := fun t =>
      Set.mem_preimage.mpr ⟨⟨γ t, hγsupp t⟩, by rw [mem_chartBall]; exact (hγ t).1.2, rfl⟩
    let gg : ↥I → ↥(U ∩ V) := fun t => ⟨φ ⟨γ t, hγsupp t⟩, ⟨hUg t, hVg t⟩⟩
    have hgg_cont : Continuous gg := by
      refine Continuous.subtype_mk ?_ (fun t => ⟨hUg t, hVg t⟩)
      exact hφcont.comp (γ.continuous.subtype_mk hγsupp)
    refine ⟨{ toFun := gg
              continuous_toFun := hgg_cont
              source' := ?_
              target' := ?_ }⟩
    · apply Subtype.ext
      apply Subtype.ext
      show ((φ ⟨γ 0, hγsupp 0⟩ : ↥(skel D (S.card - 1))) : Model D)
        = ((a.1 : ↥(skel D (S.card - 1))) : Model D)
      have h1 : ((φ ⟨γ 0, hγsupp 0⟩ : ↥(skel D (S.card - 1))) : Model D)
          = chartMap D i S ⟨γ 0, hγsupp 0⟩ := rfl
      rw [h1]
      rw [show (⟨γ 0, hγsupp 0⟩ : stratum S) = xa from Subtype.ext γ.source]
      exact hxaeq
    · apply Subtype.ext
      apply Subtype.ext
      show ((φ ⟨γ 1, hγsupp 1⟩ : ↥(skel D (S.card - 1))) : Model D)
        = ((b.1 : ↥(skel D (S.card - 1))) : Model D)
      have h1 : ((φ ⟨γ 1, hγsupp 1⟩ : ↥(skel D (S.card - 1))) : Model D)
          = chartMap D i S ⟨γ 1, hγsupp 1⟩ := rfl
      rw [h1]
      rw [show (⟨γ 1, hγsupp 1⟩ : stratum S) = xb from Subtype.ext γ.target]
      exact hxbeq
  -- ## 7. Paths in `V` with the same endpoints are homotopic
  have hVsc : ∀ {x y : ↥(skel D (S.card - 1))} (P Q : Path x y),
      (∀ t, P t ∈ V) → (∀ t, Q t ∈ V) → Nonempty (P.Homotopic Q) := by
    intro x y P Q hP hQ
    have hPrange : ∀ t, P t ∈ Set.range φ := by
      intro t
      obtain ⟨u, -, hueq⟩ := mem_chartImage.mp (Set.mem_preimage.mp (hP t))
      exact ⟨u, Subtype.ext hueq⟩
    have hQrange : ∀ t, Q t ∈ Set.range φ := by
      intro t
      obtain ⟨u, -, hueq⟩ := mem_chartImage.mp (Set.mem_preimage.mp (hQ t))
      exact ⟨u, Subtype.ext hueq⟩
    have hP' : Continuous fun t : ↥I => χ (P t) := hχcont.comp_continuous P.continuous hPrange
    have hQ' : Continuous fun t : ↥I => χ (Q t) := hχcont.comp_continuous Q.continuous hQrange
    have hcomb : Continuous fun st : ↥I × ↥I =>
        stratumCombo (χ (P st.2)) (χ (Q st.2)) (st.1 : ℝ) st.1.2.1 st.1.2.2 := by
      have h1 : Continuous fun st : ↥I × ↥I =>
          (((χ (P st.2) : stratum S) : stdSimplex ℝ (Fin (n + 2))) : Fin (n + 2) → ℝ) :=
        continuous_subtype_val.comp (continuous_subtype_val.comp (hP'.comp continuous_snd))
      have h2 : Continuous fun st : ↥I × ↥I =>
          (((χ (Q st.2) : stratum S) : stdSimplex ℝ (Fin (n + 2))) : Fin (n + 2) → ℝ) :=
        continuous_subtype_val.comp (continuous_subtype_val.comp (hQ'.comp continuous_snd))
      have h3 : Continuous fun st : ↥I × ↥I => (st.1 : ℝ) :=
        continuous_subtype_val.comp continuous_fst
      have hvec : Continuous fun st : ↥I × ↥I =>
          (1 - (st.1 : ℝ)) • (((χ (P st.2) : stratum S) :
              stdSimplex ℝ (Fin (n + 2))) : Fin (n + 2) → ℝ)
            + (st.1 : ℝ) • (((χ (Q st.2) : stratum S) :
              stdSimplex ℝ (Fin (n + 2))) : Fin (n + 2) → ℝ) :=
        ((continuous_const.sub h3).smul h1).add (h3.smul h2)
      exact (hvec.subtype_mk (fun st => combo_mem_simplex (χ (P st.2)) (χ (Q st.2))
          st.1.2.1 st.1.2.2)).subtype_mk
        (fun st => suppOf_combo (χ (P st.2)) (χ (Q st.2)) st.1.2.1 st.1.2.2)
    refine ⟨homotopic_of_homotopyMap
      (F := ⟨fun st => φ (stratumCombo (χ (P st.2)) (χ (Q st.2)) (st.1 : ℝ)
        st.1.2.1 st.1.2.2), hφcont.comp hcomb⟩) ?_ ?_ ?_ ?_⟩
    · intro t
      show φ (stratumCombo (χ (P t)) (χ (Q t)) ((0 : ↥I) : ℝ) ((0 : ↥I).2.1)
        ((0 : ↥I).2.2)) = P t
      have h1 : stratumCombo (χ (P t)) (χ (Q t)) ((0 : ↥I) : ℝ) ((0 : ↥I).2.1)
          ((0 : ↥I).2.2) = χ (P t) :=
        stratumCombo_zero (χ (P t)) (χ (Q t)) ((0 : ↥I).2.1) ((0 : ↥I).2.2)
      exact (congrArg φ h1).trans (hφχ (P t) (hPrange t))
    · intro t
      show φ (stratumCombo (χ (P t)) (χ (Q t)) ((1 : ↥I) : ℝ) ((1 : ↥I).2.1)
        ((1 : ↥I).2.2)) = Q t
      have h1 : stratumCombo (χ (P t)) (χ (Q t)) ((1 : ↥I) : ℝ) ((1 : ↥I).2.1)
          ((1 : ↥I).2.2) = χ (Q t) :=
        stratumCombo_one (χ (P t)) (χ (Q t)) ((1 : ↥I).2.1) ((1 : ↥I).2.2)
      exact (congrArg φ h1).trans (hφχ (Q t) (hQrange t))
    · intro s
      show φ (stratumCombo (χ (P 0)) (χ (Q 0)) (s : ℝ) s.2.1 s.2.2) = P 0
      have hPQ : χ (Q 0) = χ (P 0) := by rw [Q.source, P.source]
      have h1 : stratumCombo (χ (P 0)) (χ (Q 0)) (s : ℝ) s.2.1 s.2.2 = χ (P 0) := by
        rw [hPQ]
        exact stratumCombo_self (χ (P 0)) (s : ℝ) s.2.1 s.2.2
      exact (congrArg φ h1).trans (hφχ (P 0) (hPrange 0))
    · intro s
      show φ (stratumCombo (χ (P 1)) (χ (Q 1)) (s : ℝ) s.2.1 s.2.2) = P 1
      have hPQ : χ (Q 1) = χ (P 1) := by rw [Q.target, P.target]
      have h1 : stratumCombo (χ (P 1)) (χ (Q 1)) (s : ℝ) s.2.1 s.2.2 = χ (P 1) := by
        rw [hPQ]
        exact stratumCombo_self (χ (P 1)) (s : ℝ) s.2.1 s.2.2
      exact (congrArg φ h1).trans (hφχ (P 1) (hPrange 1))
  -- ## 8. The compression
  obtain ⟨q', hq'U, hq'R, hq'hom⟩ := Rng.path_compress_twoSetR
    (X := ↥(skel D (S.card - 1))) hVopen hcov hUV hVsc
    (x := ⟨y, hyk⟩) (y := ⟨z, hzk⟩)
    (show (⟨y, hyk⟩ : ↥(skel D (S.card - 1))) ∈ U from hy_ne)
    (show (⟨z, hzk⟩ : ↥(skel D (S.card - 1))) ∈ U from hz_ne) p' hp'U
  have hpe : p'.map continuous_subtype_val = p := by ext t; rfl
  refine ⟨q'.map continuous_subtype_val, ?_, ?_, ?_, ?_⟩
  · intro t
    exact hq'U t
  · intro t
    exact (q' t).2
  · obtain ⟨H⟩ := hq'hom
    have hmap : (p'.map continuous_subtype_val).Homotopic (q'.map continuous_subtype_val) :=
      Path.Homotopic.map H ⟨Subtype.val, continuous_subtype_val⟩
    rw [hpe] at hmap
    exact ⟨hmap⟩
  · intro t
    have h2 := hq'R t
    rcases h2 with hrange | hV
    · refine Or.inl ?_
      obtain ⟨s, hs⟩ := hrange
      refine ⟨s, ?_⟩
      have h1 : (p' s : Model D) = p s := rfl
      rw [← h1]
      exact congrArg Subtype.val hs
    · exact Or.inr (Set.mem_preimage.mp hV)

/-! ## The target -/

theorem skelAvoidOrigins {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : Work.RatHurewicz.MData X n x₀) (k : ℕ) (hk : 2 ≤ k)
    (O : Finset (Work.RatHurewicz.Model D))
    (hO : ∀ o ∈ O, ∃ (i : D.Idx) (S : Finset (Fin (n + 2))),
      S.card = k + 1 ∧ o ∈ Work.RatHurewicz.openCell D i S)
    {y z : Work.RatHurewicz.Model D} (hy : y ∈ Work.RatHurewicz.skeleton D)
    (hz : z ∈ Work.RatHurewicz.skeleton D) (p : Path y z)
    (hp : ∀ t, p t ∈ Work.RatHurewicz.skel D k) :
    ∃ q : Path y z, (∀ t, ∀ o ∈ O, q t ≠ o) ∧
      (∀ t, q t ∈ Work.RatHurewicz.skel D k) ∧
        Nonempty (Path.Homotopic p q) := by
  classical
  have hmem_openCell : ∀ (i : D.Idx) (S : Finset (Fin (n + 2))) (z : Model D),
      z ∈ openCell D i S ↔ ∃ x : stdSimplex ℝ (Fin (n + 2)), ptSupport x = S ∧
        Quotient.mk'' (Sum.inl ⟨i, x⟩) = z := by
    intro i S z; rw [openCell, Set.mem_ofPred_eq]
  have key : ∀ (O : Finset (Model D)) (p : Path y z),
      (∀ t, p t ∈ skel D k) →
      (∀ o ∈ O, ∃ (i : D.Idx) (S : Finset (Fin (n + 2))),
        S.card = k + 1 ∧ o ∈ openCell D i S) →
      ∃ q : Path y z, (∀ t, ∀ o ∈ O, q t ≠ o) ∧ (∀ t, q t ∈ skel D k) ∧
        Nonempty (p.Homotopic q) := by
    intro O
    refine Finset.induction_on O ?_ ?_
    · intro p hp _
      exact ⟨p, (fun t o ho => absurd ho (Finset.notMem_empty o)), hp,
        ⟨Path.Homotopic.refl p⟩⟩
    · intro a s ha ih p hp hO
      have hs : ∀ o ∈ s, ∃ (i : D.Idx) (S : Finset (Fin (n + 2))),
          S.card = k + 1 ∧ o ∈ openCell D i S :=
        fun o ho => hO o (Finset.mem_insert_of_mem ho)
      obtain ⟨q₁, hq₁ne, hq₁skel, hq₁hom⟩ := ih p hp hs
      obtain ⟨i, S, hScard, ha_mem⟩ := hO a (Finset.mem_insert_self a s)
      have hS : 2 < S.card := by omega
      have hskel_eq : skel D (S.card - 1) = skel D k := by
        rw [hScard]; exact congrArg (skel D) (Nat.add_sub_cancel k 1)
      obtain ⟨c, hcsupp, hceq⟩ := (hmem_openCell i S a).mp ha_mem
      obtain ⟨eps, hεpos, hεs⟩ := exists_chartBall_avoid (D := D) hcsupp s
        (fun o' ho' hcon => ha (by rw [hcon, hceq] at ho'; exact ho'))
      obtain ⟨q₂, hq₂ne, hq₂skel, hq₂hom, hq₂range⟩ :=
        avoidOnePointR (D := D) hS hcsupp a hceq hεpos hy hz q₁
          (fun t => by rw [hskel_eq]; exact hq₁skel t)
      refine ⟨q₂, ?_, ?_, ?_⟩
      · intro t o ho
        rw [Finset.mem_insert] at ho
        rcases ho with rfl | ho
        · exact hq₂ne t
        · intro hcon
          have hmem2 := hq₂range t
          rw [hcon] at hmem2
          rcases hmem2 with ⟨t', ht'⟩ | hV
          · exact hq₁ne t' o ho ht'
          · exact hεs o ho hV
      · intro t
        rw [← hskel_eq]; exact hq₂skel t
      · exact ⟨hq₁hom.some.trans hq₂hom.some⟩
  exact key O p hp hO

end

end Work.RatHurewicz
