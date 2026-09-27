import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.LocalGraph
import Submission.Work.Drive.TParity.ChartDeriv
import Submission.Work.Drive.TParity.FlowDefs
import Submission.Work.Drive.TParity.exists_local_tangent_data3
import Submission.Work.Drive.ManifoldParity.InterSetFlowDefs
import Submission.Work.Drive.ManifoldParity.FlowSetupDefs
import Submission.Work.Drive.ManifoldParity.GraphMap
import Submission.Work.Drive.ManifoldParity.GraphFDeriv
import Submission.Work.Drive.ManifoldParity.GraphFlow

/-!
# The triple intersection set is preserved by the flow of a tangential field

`Work.Drive.TParity.K3_mapsTo_flowV`: if `V` is a smooth compactly supported field on `ℝ⁹` which is
tangent to the triple intersection set `K3 D` of three smooth chains `D 0, D 1, D 2 : ℝ³ → M` in a
smooth `4`-manifold (`Vtan`), and which crosses the faces of the nine-box transversally at every
boundary triple intersection (`Vface`), then the flow line of `V` through a point of `K3 D` stays in
`K3 D` as long as it stays in the nine-box.

This is the nine-box analogue of `Work.Drive.boxMapsTo_flowV_interSet`
(`ManifoldParity/boxMapsTo_flowV_interSet.lean`).

Proof.  The set `A = {s ∈ [0,t] | Φ_s x ∈ K3 D}` is closed (K3 D is closed) and non-empty, so it
has a supremum `T`; if `T < t` we transport to `q = Φ_T x ∈ K3 D` and use the local invariance
`flowV8_local_K3_right`, contradicting the maximality of `T`.  For negative `t` apply the argument
to the reversed field `-V`.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Set Filter Manifold

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The triple intersection set is closed. -/
theorem isClosed_K3 {M : Type*} [TopologicalSpace M] [T2Space M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (hDc : ∀ k, Continuous (D k)) :
    IsClosed (K3 D) := by
  have h1 : IsClosed {x : Amb 8 | D 0 (bPartC 0 x) = D 1 (bPartC 1 x)} :=
    isClosed_eq ((hDc 0).comp (bPartC 0).continuous) ((hDc 1).comp (bPartC 1).continuous)
  have h2 : IsClosed {x : Amb 8 | D 0 (bPartC 0 x) = D 2 (bPartC 2 x)} :=
    isClosed_eq ((hDc 0).comp (bPartC 0).continuous) ((hDc 2).comp (bPartC 2).continuous)
  have h3 : IsClosed (Submission.Drive.unitBox 8 ∩
      ({x : Amb 8 | D 0 (bPartC 0 x) = D 1 (bPartC 1 x)} ∩
        {x : Amb 8 | D 0 (bPartC 0 x) = D 2 (bPartC 2 x)})) :=
    (Work.Drive.isClosed_unitBox 8).inter (h1.inter h2)
  convert h3 using 1
  ext x
  simp only [K3, meet3, Set.mem_ofPred_eq, Set.mem_inter_iff]

/-- **The flow line through a point of the triple intersection set stays on it, for a short forward
time.**  If `q ∈ K3 D` and the flow line of `q` stays in the closed box for times in `[0,E]`
(`E > 0`), then there is `ε ∈ (0,E]` such that the flow line of `q` is again in `K3 D` for all times
in `[0,ε]`.

This is the local step: near `q` the triple intersection set is the graph of `η` over a suitable
coordinate `i` (`Work.Drive.TParity.exists_local_graph3`), and `V` is tangent to that graph
(`Work.Drive.TParity.exists_local_tangent_data3`), so the graph is invariant under the flow
(`Work.Drive.ManifoldParity.eq_graphMap_of_tangent_flow_right`).  The coordinate `i` is the
coordinate of a face of the box carrying `q` when `q` is on the boundary (`hface` gives it, and the
tangency at `q` upgrades it to one for which the charted difference map is surjective on
`{v | v i = 0}`), and an arbitrary transversal coordinate when `q` is in the interior of the box. -/
theorem flowV8_local_K3_right
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (htrans : transHyp D)
    (V : Amb 8 → Amb 8) (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (hVtan : Vtan D V) (hface : Vface D V)
    {q : Amb 8} (hq : q ∈ K3 D) {E : ℝ} (hE : 0 < E)
    (hbox : ∀ s ∈ Set.Icc (0 : ℝ) E, flowV8 V hV hVs s q ∈ Submission.Drive.unitBox 8) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ E ∧
      ∀ s ∈ Set.Icc (0 : ℝ) ε, flowV8 V hV hVs s q ∈ K3 D := by
  classical
  obtain ⟨hboxq, hmq⟩ := mem_K3.mp hq
  have hregq : q ∈ region3 (D 0 (bPartC 0 q)) D := mem_region3_self D hmq
  have hsurjq : Function.Surjective (fderiv ℝ (chartDiff3 (D 0 (bPartC 0 q)) D) q) :=
    chartDiff3_surj D hD hregq hmq (htrans q hboxq hmq)
  -- choose the coordinate over which the triple intersection set is a graph near `q`
  have hkey : ∃ i : Fin 9,
      (Function.Surjective (fun v : {v : Amb 8 // v i = 0} =>
        fderiv ℝ (chartDiff3 (D 0 (bPartC 0 q)) D) q v.1)) ∧
      (∀ j : Fin 9, j ≠ i → q j ∈ Set.Ioo (0 : ℝ) 1) := by
    by_cases hint : q ∈ interior (Submission.Drive.unitBox 8)
    · obtain ⟨i, hi⟩ := Work.Drive.exists_domRestrict_surjective hsurjq
      refine ⟨i, hi, fun j _ => ?_⟩
      rw [Work.Drive.interior_unitBox] at hint
      exact hint j
    · have hbdry : q ∈ Submission.Drive.unitBoxBdry 8 :=
        ⟨hboxq, Work.Drive.exists_coord_eq_zero_or_one_of_not_mem_interior hboxq hint⟩
      obtain ⟨i, -, hother, hVi⟩ := hface q hq hbdry
      refine ⟨i, ?_, hother⟩
      rw [Work.Drive.surjective_domRestrict_iff_cofactorVec_ne_zero _ hsurjq i]
      have hker : fderiv ℝ (chartDiff3 (D 0 (bPartC 0 q)) D) q (V q) = 0 :=
        hVtan q hq (D 0 (bPartC 0 q)) hregq
      have hVne : V q ≠ 0 := fun h0 => hVi (by simp [h0])
      exact (Work.Drive.cofactorVec_apply_ne_zero_iff _ hsurjq hker hVne i).mpr hVi
  obtain ⟨i, hsurj_i, hother⟩ := hkey
  -- the local graph data
  obtain ⟨η, εs, hεs, hηcd, hηi, hgq, -, hK_at, htan_at, C, -, hC⟩ :=
    exists_local_tangent_data3 (V := V) D hD htrans hVtan hq hsurj_i hother
  have hηdiff : Differentiable ℝ η := hηcd.differentiable (by simp)
  obtain ⟨L, hL⟩ := Work.Drive.exists_lipschitzWith_of_contDiff_hasCompactSupport hV hVs
  set γ : ℝ → Amb 8 := fun s => flowV8 V hV hVs s q with hγdef
  have hγ : ∀ s, HasDerivAt γ (V (γ s)) s := fun s => flowV8_deriv V hV hVs q s
  have hγ0 : γ 0 = q := flowV8_zero V hV hVs q
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  -- a time interval on which the flow remains close to `q`
  obtain ⟨ε₁, hε₁, hε₁'⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ s : ℝ, |s| < ε₁ → ‖γ s - q‖ < εs := by
    have hball : Metric.ball q εs ∈ 𝓝 (γ 0) := by
      rw [hγ0]
      exact Metric.ball_mem_nhds q hεs
    obtain ⟨ε₁, hε₁, hε₁'⟩ :=
      Metric.eventually_nhds_iff.mp (hγc.continuousAt.preimage_mem_nhds hball)
    exact ⟨ε₁, hε₁, fun s hs => hε₁' (by rwa [Real.dist_eq, sub_zero])⟩
  refine ⟨min (ε₁ / 2) E, lt_min (by linarith) hE, min_le_right _ _, ?_⟩
  intro s hs
  have hsE : s ∈ Set.Icc (0 : ℝ) E := ⟨hs.1, le_trans hs.2 (min_le_right _ _)⟩
  have hsa : |s| < ε₁ := by
    rw [abs_of_nonneg hs.1]
    exact lt_of_le_of_lt hs.2 (min_lt_of_left_lt (by linarith))
  have hclose : |(γ s) i - q i| < εs := by
    have h1 : |(γ s) i - q i| ≤ ‖γ s - q‖ := by
      have h := PiLp.norm_apply_le (γ s - q) i
      simpa [PiLp.sub_apply, Real.norm_eq_abs] using h
    exact lt_of_le_of_lt h1 (hε₁' s hsa)
  -- the hypothesis of `eq_graphMap_of_tangent_flow_right` on the whole interval
  have htan : ∀ s' ∈ Set.Icc (0 : ℝ) (min (ε₁ / 2) E),
      V (Work.Drive.ManifoldParity.graphMap i η ((γ s') i)) =
        fderiv ℝ (Work.Drive.ManifoldParity.graphMap i η) ((γ s') i)
          ((V (Work.Drive.ManifoldParity.graphMap i η ((γ s') i))) i) := by
    intro s' hs'
    have hs'E : s' ∈ Set.Icc (0 : ℝ) E := ⟨hs'.1, le_trans hs'.2 (min_le_right _ _)⟩
    have hsa' : |s'| < ε₁ := by
      rw [abs_of_nonneg hs'.1]
      exact lt_of_le_of_lt hs'.2 (min_lt_of_left_lt (by linarith))
    have hcl' : |(γ s') i - q i| < εs := by
      have h1 : |(γ s') i - q i| ≤ ‖γ s' - q‖ := by
        have h := PiLp.norm_apply_le (γ s' - q) i
        simpa [PiLp.sub_apply, Real.norm_eq_abs] using h
      exact lt_of_le_of_lt h1 (hε₁' s' hsa')
    exact htan_at ((γ s') i) hcl' ((hbox s' hs'E) i)
  have hC' : ∀ s' ∈ Set.Icc (0 : ℝ) (min (ε₁ / 2) E),
      ‖fderiv ℝ (Work.Drive.ManifoldParity.graphMap i η) ((γ s') i)‖ ≤ C := by
    intro s' hs'
    have hs'E : s' ∈ Set.Icc (0 : ℝ) E := ⟨hs'.1, le_trans hs'.2 (min_le_right _ _)⟩
    have hsa' : |s'| < ε₁ := by
      rw [abs_of_nonneg hs'.1]
      exact lt_of_le_of_lt hs'.2 (min_lt_of_left_lt (by linarith))
    have hcl' : |(γ s') i - q i| < εs := by
      have h1 : |(γ s') i - q i| ≤ ‖γ s' - q‖ := by
        have h := PiLp.norm_apply_le (γ s' - q) i
        simpa [PiLp.sub_apply, Real.norm_eq_abs] using h
      exact lt_of_le_of_lt h1 (hε₁' s' hsa')
    exact hC ((γ s') i) hcl'.le
  have hinit : γ 0 = Work.Drive.ManifoldParity.graphMap i η ((γ 0) i) := by
    rw [hγ0]
    exact hgq.symm
  have hgraph : ∀ s' ∈ Set.Icc (0 : ℝ) (min (ε₁ / 2) E),
      γ s' = Work.Drive.ManifoldParity.graphMap i η ((γ s') i) :=
    Work.Drive.ManifoldParity.eq_graphMap_of_tangent_flow_right (i := i) (ε := min (ε₁ / 2) E)
      hL hγ hηdiff (lt_min (by linarith) hE) hC' htan hinit
  have hfinal : flowV8 V hV hVs s q = Work.Drive.ManifoldParity.graphMap i η ((γ s) i) := by
    change γ s = Work.Drive.ManifoldParity.graphMap i η ((γ s) i)
    exact hgraph s hs
  rw [hfinal]
  exact mem_K3.mpr ⟨by rw [← hfinal]; exact hbox s hsE, hK_at ((γ s) i) hclose⟩

/-- **The triple intersection set is preserved by the flow while the line stays in the box, under
the face condition.**

`K3 D = {x ∈ [0,1]⁹ | D₀ x₀ = D₁ x₁ = D₂ x₂}` for smooth chains `D 0, D 1, D 2 : ℝ³ → M` in a
smooth `4`-manifold `M`; `V` is a compactly supported smooth field on `ℝ⁹`, tangent to the triple
intersection set at every point of the box (`hVtan`), and `hface` is the face condition: at every
triple intersection point on the boundary of the box, exactly one coordinate is `0` or `1`, all
other coordinates are strictly inside `(0,1)`, and the corresponding component of `V` is non-zero
(the flow crosses that face transversally).

If the flow line of `x ∈ K3 D` stays in the closed box on the whole interval between the times `0`
and `t`, then it is again in `K3 D` at time `t`. -/
theorem K3_mapsTo_flowV {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (htrans : Work.Drive.TParity.transHyp D) (V : Work.Drive.Amb 8 → Work.Drive.Amb 8)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hVs : HasCompactSupport V)
    (hVtan : Work.Drive.TParity.Vtan D V) (hface : Work.Drive.TParity.Vface D V)
    (x : Work.Drive.Amb 8) (hx : x ∈ Work.Drive.TParity.K3 D) (t : ℝ)
    (hbox : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      Work.Drive.TParity.flowV8 V hV hVs u x ∈ Submission.Drive.unitBox 8) :
    Work.Drive.TParity.flowV8 V hV hVs t x ∈ Work.Drive.TParity.K3 D := by
  classical
  -- the argument for `t ≥ 0`, applicable to any tangent field `V'`
  have hpos : ∀ (V' : Amb 8 → Amb 8) (hV' : ContDiff ℝ Ctop V') (hVs' : HasCompactSupport V')
      (hVtan' : Vtan D V') (hface' : Vface D V') (t' : ℝ), 0 ≤ t' →
      (∀ u ∈ Set.uIcc (0 : ℝ) t', flowV8 V' hV' hVs' u x ∈ Submission.Drive.unitBox 8) →
      flowV8 V' hV' hVs' t' x ∈ K3 D := by
    intro V' hV' hVs' hVtan' hface' t' ht0 htbox
    have htbox' : ∀ u ∈ Set.Icc (0 : ℝ) t',
        flowV8 V' hV' hVs' u x ∈ Submission.Drive.unitBox 8 := by
      intro u hu
      exact htbox u (by rw [Set.uIcc_of_le ht0]; exact hu)
    have hγc : Continuous (fun s : ℝ => flowV8 V' hV' hVs' s x) :=
      continuous_iff_continuousAt.mpr fun s => (flowV8_deriv V' hV' hVs' x s).continuousAt
    have hKclosed : IsClosed (K3 D) := isClosed_K3 D (fun k => (hD k).continuous)
    set A : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) t' ∧ flowV8 V' hV' hVs' s x ∈ K3 D} with hA
    have hAclosed : IsClosed A := by
      rw [hA]
      exact (isClosed_Icc.preimage continuous_id).inter (hKclosed.preimage hγc)
    have hAne : A.Nonempty := ⟨0, by
      rw [hA]
      exact ⟨⟨le_rfl, ht0⟩, by rw [flowV8_zero]; exact hx⟩⟩
    have hAbdd : BddAbove A := ⟨t', fun s hs => hs.1.2⟩
    set T : ℝ := sSup A with hT
    have hTmem : T ∈ A := hAclosed.csSup_mem hAne hAbdd
    have hTE : T = t' := by
      by_contra hne
      have hTlt : T < t' := lt_of_le_of_ne hTmem.1.2 hne
      set q' : Amb 8 := flowV8 V' hV' hVs' T x with hq'def
      have hq'K : q' ∈ K3 D := hTmem.2
      have hbox' : ∀ s ∈ Set.Icc (0 : ℝ) (t' - T),
          flowV8 V' hV' hVs' s q' ∈ Submission.Drive.unitBox 8 := by
        intro s hs
        have h1 : flowV8 V' hV' hVs' s q' = flowV8 V' hV' hVs' (s + T) x := by
          rw [hq'def]
          exact (flowV8_add V' hV' hVs' s T x).symm
        rw [h1]
        exact htbox' (s + T) ⟨by linarith [hs.1, hTmem.1.1, hTlt], by linarith [hs.2]⟩
      obtain ⟨ε, hε, hεE, hloc⟩ :=
        flowV8_local_K3_right (M := M) D hD htrans V' hV' hVs' hVtan' hface' hq'K
          (by linarith) hbox'
      have hmem : T + ε / 2 ∈ A := by
        refine ⟨⟨by linarith [hTmem.1.1], by linarith [hεE]⟩, ?_⟩
        have hs : ε / 2 ∈ Set.Icc (0 : ℝ) ε := ⟨by linarith, by linarith⟩
        have h2 : flowV8 V' hV' hVs' (ε / 2) q' ∈ K3 D := hloc (ε / 2) hs
        have h3 : flowV8 V' hV' hVs' (ε / 2) q' = flowV8 V' hV' hVs' (T + ε / 2) x := by
          rw [hq'def, ← flowV8_add]
          congr 1
          ring
        rwa [h3] at h2
      have hle := le_csSup hAbdd hmem
      linarith [hε]
    rw [← hTE]
    exact hTmem.2
  by_cases ht : (0 : ℝ) ≤ t
  · exact hpos V hV hVs hVtan hface t ht hbox
  · -- `t < 0`: apply the nonnegative case to the reversed field `-V`
    have htneg : t < 0 := not_le.mp ht
    have hV1 : ContDiff ℝ Ctop (-V) := hV.neg
    have hVs1 : HasCompactSupport (-V) := hVs.neg
    have hVtan1 : Vtan D (-V) := by
      intro y hy p hype
      rw [Pi.neg_apply, map_neg, hVtan y hy p hype, neg_zero]
    have hface1 : Vface D (-V) := by
      intro b hbK hbBdry
      obtain ⟨i, hi, hoth, hVne⟩ := hface b hbK hbBdry
      exact ⟨i, hi, hoth, by simpa using hVne⟩
    have hbox1 : ∀ u ∈ Set.uIcc (0 : ℝ) (-t),
        flowV8 (-V) hV1 hVs1 u x ∈ Submission.Drive.unitBox 8 := by
      intro u hu
      have hu1 : u ∈ Set.Icc (0 : ℝ) (-t) := by rwa [Set.uIcc_of_le (by linarith)] at hu
      rw [flowV8_neg (V := V) hV hVs hV1 hVs1 u x]
      refine hbox (-u) ?_
      rw [Set.uIcc_comm, Set.uIcc_of_le htneg.le]
      exact ⟨by linarith [hu1.2], by linarith [hu1.1]⟩
    have hfinal := hpos (-V) hV1 hVs1 hVtan1 hface1 (-t) (by linarith) hbox1
    rw [flowV8_neg (V := V) hV hVs hV1 hVs1 (-t) x] at hfinal
    simpa using hfinal

end

end Work.Drive.TParity
