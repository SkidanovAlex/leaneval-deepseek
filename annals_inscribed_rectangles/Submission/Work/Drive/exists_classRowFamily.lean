import Mathlib
import Submission.Work.Drive.hdenseNodeRows
import Submission.Work.Drive.hdenseNodeVocab
import Submission.Work.Drive.hdenseNodeOpens
import Submission.Work.Drive.hdenseDesignData
import Submission.Work.Drive.classTripleOdd
import Submission.Work.Drive.encFamQ0Sard
import Submission.Work.Drive.classRowVocab
import Submission.Work.Drive.classRowDesignData
import Submission.Work.Drive.endTripleReg_cyclic
import Submission.Work.Drive.exists_meet3Hyp_and_cond_near_of_openDense
import Submission.Work.Drive.classRowsSweep_openDense
import Submission.Work.Drive.classRowsLin_openDense


namespace Work.Drive

open Manifold Set Filter
open scoped Manifold ContDiff Topology BigOperators

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
attribute [local instance] Work.Drive.projTimesLineCharted
  Work.Drive.isManifold_projTimesLineCharted

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## Elementary permutation lemmas, the `pt2`/`mk2` bridge, and the density of a finite intersection -/

theorem endTripleReg_swap23_row {F A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)}
    (h : EndTripleReg F A B) : EndTripleReg F B A := by
  intro y₀ y₁ y₂ hFB hFA
  obtain ⟨hF, hA, hB, hI⟩ := h y₀ y₂ y₁ hFA hFB
  exact ⟨hF, hB, hA, by rw [← hI]; ac_rfl⟩

theorem pt2_eq_mk2_row (a b : ℝ) : pt2 a b = mk2 a b := by
  ext i
  fin_cases i <;> simp [pt2, mk2]

/-- **A finite intersection of open sets that are dense at every point of the closed unit ball is again
dense at every such point.**  `ClassRowFamily`'s density clause is exactly the hypothesis here; the
point is that the centre of the ball one is testing may lie on the boundary `‖x‖ = 1`, where the
supporting lemma `Work.Drive.exists_mem_all_near_of_isOpen_dense_fintype` is not directly applicable:
one first moves slightly inside. -/
theorem exists_mem_inter_of_open_dense_ball {m : ℕ} {S T : Set (EuclideanSpace ℝ (Fin m))}
    (hS : IsOpen S) (hT : IsOpen T)
    (hdS : ∀ x : EuclideanSpace ℝ (Fin m), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ S ∧ ‖y - x‖ < δ)
    (hdT : ∀ x : EuclideanSpace ℝ (Fin m), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
      ∃ y, y ∈ T ∧ ‖y - x‖ < δ)
    {m₀ : EuclideanSpace ℝ (Fin m)} (hm₀ : ‖m₀‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y, y ∈ S ∩ T ∧ ‖y - m₀‖ < δ := by
  classical
  -- a point `m'` strictly inside the unit ball, close to `m₀`
  have hinner : ∃ m' : EuclideanSpace ℝ (Fin m), ‖m'‖ < 1 ∧ ‖m' - m₀‖ < δ / 2 := by
    by_cases h : ‖m₀‖ < 1
    · exact ⟨m₀, h, by rw [sub_self, norm_zero]; linarith⟩
    · have h1 : ‖m₀‖ = 1 := le_antisymm hm₀ (not_lt.mp h)
      set ε : ℝ := min (δ / 4) (1 / 2) with hεdef
      have hεpos : 0 < ε := lt_min (by linarith) (by norm_num)
      have hεδ : ε < δ / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      refine ⟨(1 - ε) • m₀, ?_, ?_⟩
      · have hnorm : ‖((1 - ε : ℝ))‖ = 1 - ε := by
          rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
        rw [norm_smul, hnorm, h1, mul_one]
        linarith
      · have hsub : (1 - ε) • m₀ - m₀ = (-ε) • m₀ := by
          rw [sub_smul, one_smul]
          module
        have hnorm : ‖((-ε : ℝ))‖ = ε := by
          rw [Real.norm_eq_abs, abs_neg, abs_of_pos hεpos]
        rw [hsub, norm_smul, hnorm, h1, mul_one]
        linarith
  obtain ⟨m', hm'1, hm'd⟩ := hinner
  -- the supporting intersection lemma at the interior centre
  have hfam := exists_mem_all_near_of_isOpen_dense_fintype (n := m) (ι := Fin 2)
    (fun i : Fin 2 => ![S, T] i)
    (by intro i; fin_cases i
        · simpa using hS
        · simpa using hT)
    (by intro i x hx ε hε; fin_cases i
        · simpa using hdS x hx ε hε
        · simpa using hdT x hx ε hε)
    hm'1 (δ / 2) (by linarith)
  obtain ⟨y, hyd, hyS⟩ := hfam
  refine ⟨y, ⟨hyS 0, hyS 1⟩, ?_⟩
  calc ‖y - m₀‖ ≤ ‖y - m'‖ + ‖m' - m₀‖ := by
        have := norm_add_le (y - m') (m' - m₀)
        rwa [sub_add_sub_cancel] at this
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

/-- **The producer of the class-row family** (`NOTES_LEAD_hodd_blockT6.md` §3): for the given linear
family `Φ` and level `cl`, an open set of design parameters, dense at every point of the closed unit
ball, on which all nine class-level clauses `Work.Drive.DesignRowsAt` hold.

This is the conjunction of the two delegated producers `Work.Drive.classRowsSweep_openDense` and
`Work.Drive.classRowsLin_openDense`, intersected with the density lemma above. -/
theorem classRowRows_openDense {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    {c : ℝ} (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q))
    (a c' : UnitAddCircle) (ha : a ∈ Work.Drive.Zc γ) (hc' : c' ∈ Work.Drive.Zc γ)
    (hac : a + c' ∈ Work.Drive.Zc γ)
    (A : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (cl : ℝ) (hcl : 0 < cl) :
    ∃ R : Set (EuclideanSpace ℝ (Fin 12)), IsOpen R ∧
      (∀ x : EuclideanSpace ℝ (Fin 12), ‖x‖ ≤ 1 → ∀ δ : ℝ, 0 < δ →
        ∃ y, y ∈ R ∧ ‖y - x‖ < δ) ∧
      (∀ t ∈ R, Work.Drive.DesignRowsAt Q a c' (fun k => Work.Drive.linBase A k) cl hcl t) := by
  obtain ⟨R₁, hR₁o, hR₁d, hR₁r⟩ := classRowsSweep_openDense (γ := γ) (hγne := hγne) hγinj hQ hc hcbot
    hdisjZc a c' ha hc' hac (fun k => linBase A k) cl hcl
  obtain ⟨R₂, hR₂o, hR₂d, hR₂r⟩ := classRowsLin_openDense (γ := γ) (hγne := hγne) hγinj hQ hc hcbot
    hdisjZc a c' ha hc' hac A cl hcl
  refine ⟨R₁ ∩ R₂, hR₁o.inter hR₂o, ?_, ?_⟩
  · intro x hx δ hδ
    obtain ⟨y, hy, hyd⟩ := exists_mem_inter_of_open_dense_ball hR₁o hR₂o hR₁d hR₂d hx hδ
    exact ⟨y, hy, hyd⟩
  · intro t ht
    exact ⟨hR₁r t ht.1, hR₂r t ht.2⟩
/-- **The class-row family of the design's triple exists** (`NOTES_LEAD_hodd_blockT6.md` §2.1, §2.5, §3):
for an **injective** curve `γ` with a plane chart `Q`, a level `c` above the chart's disk and a
collision-free triple of angles `(0, a, a + c')`, there is an open set of design parameters `t : ℝ¹²`,
dense at every point of the closed unit ball, at which the perturbed class triple of the design is
**odd**.

This is the last input of the node `Work.Drive.hdense_sideGerm` (see
`Work.Drive.hdense_sideGerm_of_classRowFamily`, `Drive/hdenseNodeRows.lean`, and the addenda of
`HDENSE_STATUS.md`).

**The hypothesis `hγinj` is necessary** (the first delegation of this statement, without it, was
correctly returned as false by the fleet: for the *constant* curve `γ ≡ (1,0)`, whose constant chart is
a plane chart — `Work.Drive.constChart_isPlaneChart`, `Drive/hn2_sideGerm_reference.lean`, see
`HN2_INJECTIVITY_DEFECT.md` — the perturbed class triple is constant, so the class triple set is the whole
`(unitBox 1)³`, of `ncard = 0`, and no open `R` can satisfy the oddness clause).  Every consumer supplies
injectivity (the node's own statement carries it).

Route: the seven class rows of the lead's §3 table (all open-dense in `t`) fed to
`Work.Drive.hasClassLinearization_of_endData` (§2.5) and then
`Work.Drive.odd_ncard_classTripleSet_of_hasClassLinearization`; the per-clause encoded `Meet3Hyp`
`Work.Drive.exists_homotopy_meet3Hyp_encoded` (§2.1) is currently a stub in `Drive/encodedGeneric.lean`
and must be produced (a Sard statement with the box-reparametrisation family of §2.2).  The rows:
`endTripleReg_blockPlane_of_designMeet3` (+ the unrestricted form) for `{P̂₀,P̂₁,P̂₂}`;
`pairReg_of_loopBoxData`-type rows for `PairReg P̂₁P̂₂` and `PairReg lin₀P̂₂`; the second-`Meet3Hyp`
bridge for `{lin₀,P̂₁,P̂₂}`; the `GoodLoopChain`-lift bridge for `{lin₁,lin₀,P̂₂}`; and the φ-chooser
`exists_linPlaneCharts_hgen` for `PairReg lin₀lin₁` and `EndTripleReg lin₂lin₀lin₁`.  The design's own
`GoodAt`/`Meet3Hyp` genericity of `exists_designGoodData` is available for the block-dependent rows. -/
theorem exists_classRowFamily {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγinj : Function.Injective γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q) {c : ℝ} (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q))
    (a c' : UnitAddCircle) (ha : a ∈ Work.Drive.Zc γ) (hc' : c' ∈ Work.Drive.Zc γ)
    (hac : a + c' ∈ Work.Drive.Zc γ) :
    ∃ R : Set (EuclideanSpace ℝ (Fin 12)), Work.Drive.ClassRowFamily Q c a c' R := by
  classical
  -- ## the `t`-independent design data (the sheared linear family and the untransported homotopies)
  obtain ⟨A, H0, hH00, hH01, hH0seam, hH0cont, hH0sm⟩ :=
    exists_linBase_homotopies (γ := γ) (hγne := hγne) hγinj hQ (designAnglesReal a c') c hc
  -- ## the nine class-level rows on an open, dense-at-every-point set of parameters
  obtain ⟨R, hRopen, hRdense, hRows⟩ :=
    classRowRows_openDense (γ := γ) (hγne := hγne) hγinj hQ hc hcbot hdisjZc a c' ha hc' hac
      A c hc
  refine ⟨R, hRopen, hRdense, ?_⟩
  intro t ht
  -- ## the angle representatives and the transported homotopies
  set u : Fin 3 → UnitAddCircle := fun k => ((designAnglesReal a c' k : ℝ) : UnitAddCircle) with hu
  have hu_eq : ∀ k, u k = designAngles a c' k := fun k => designAnglesReal_coe a c' k
  set H : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3) :=
    fun k => transportHom H0 t k with hH
  have hsmH : ∀ k, ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => H k (x 2, mk2 (x 0) (x 1))) :=
    fun k => contMDiff_transportHom_chain H0 t k (hH0sm k)
  have hseamH : ∀ (k : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      H k (s, seamInv2 y) = H k (s, y) :=
    fun k s y hy => transportHom_seam H0 t k (fun s' y' hy' => hH0seam k s' y' hy') s y hy
  have hHend0 : ∀ k, (fun y : EuclideanSpace ℝ (Fin 2) => H k (0, y))
      = designPertClass Q (designAngles a c' k) t k := by
    intro k
    rw [transportHom_zero_design Q H0 u (fun k y => congrFun (hH00 k) y) t k, hu_eq k]
  have hHend1 : ∀ k, (fun y : EuclideanSpace ℝ (Fin 2) => H k (1, y))
      = linTransClass (linBase A k) ((blk k) t) c hc :=
    fun k => transportHom_one_design (fun k => linBase A k) c hc H0
      (fun k y => congrFun (hH01 k) y) t k
  have hconst0 : ∀ (k : Fin 3) (s : ℝ), s ≤ 0 → ∀ y : EuclideanSpace ℝ (Fin 2),
      H k (s, y) = H k (0, y) := fun k s hs y => transportHom_left H0 t k hs y
  have hconst1 : ∀ (k : Fin 3) (s : ℝ), 1 ≤ s → ∀ y : EuclideanSpace ℝ (Fin 2),
      H k (s, y) = H k (1, y) := fun k s hs y => transportHom_right H0 t k hs y
  -- ## smoothness, seam invariance and fold-flatness of the plane presentations
  have hΞc : ChartPert (fun _ : ℂ => Q 0) 4 (fun s p => chartPert s p) := isChartPert_chartPert _
  have hsmPert : ∀ k, ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (designPertClass Q (designAngles a c' k) t k) := by
    intro k
    have hsm : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (designPertPlane Q (designAngles a c' k) t k) :=
      (contMDiff_apply_of_chartPert hΞc ((blk k) t)).comp
        (contMDiff_rotPresentation Q (designAngles a c' k) (contMDiff_diskPlane (Q := Q) hQ.1))
    exact fun y => contMDiffAt_cls_of_contMDiff_gen (k := 2) hsm y
  have hseamPert : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      designPertClass Q (designAngles a c' k) t k (seamInv2 y)
        = designPertClass Q (designAngles a c' k) t k y := by
    intro k y hy
    simp only [designPertClass, designPertPlane, planeClassMap]
    rw [rotPresentation_seamInv Q hQ.2.2.1 (designAngles a c' k) y hy]
  have hfoldPert : ∀ k, FoldFlat (designPertClass Q (designAngles a c' k) t k) :=
    fun k => foldFlat_designPertClass Q (IsChartData_of_isPlaneChart hQ).isSmoothChart
      (designAngles a c') t k
  have hsmLin : ∀ k, ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (linTransClass (linBase A k) ((blk k) t) c hc) := by
    intro k
    exact fun y => contMDiffAt_cls_of_contMDiff_gen (k := 2)
      (contMDiff_diskPlane (linPlaneChart_contMDiff ((linBase A k).trans
        (classEquiv ((blk k) t))) c hc)) y
  have hseamLin : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      linTransClass (linBase A k) ((blk k) t) c hc (seamInv2 y)
        = linTransClass (linBase A k) ((blk k) t) c hc y := by
    intro k y hy
    simp only [linTransClass, planeClassMap]
    rw [diskPlane_seamInv2 (Q := linPlaneChart ((linBase A k).trans (classEquiv ((blk k) t))) c hc)
      (fun z hz => linPlaneChart_neg _ c hc hz) hy]
  have hfoldLin : ∀ k, FoldFlat (linTransClass (linBase A k) ((blk k) t) c hc) :=
    fun k => foldFlat_linTransClass (linBase A k) c hc ((blk k) t)
  -- ## the nine rows at `t`
  obtain ⟨hSweep, hLin⟩ := hRows t ht
  obtain ⟨hpair12, h012, hL012, hL10P2⟩ := hSweep
  obtain ⟨hpairL0P2, hpairL0L1, hLLL, hrank_t, hgen_t⟩ := hLin
  -- the same rows, read at the ends of the *transported* homotopies
  have h012' : EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H 0 (0, y))
      (designPertClass Q (designAngles a c' 1) t 1)
      (designPertClass Q (designAngles a c' 2) t 2) := by
    rw [hHend0 0]; exact h012
  have hL012' : EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H 0 (1, y))
      (designPertClass Q (designAngles a c' 1) t 1)
      (designPertClass Q (designAngles a c' 2) t 2) := by
    rw [hHend1 0]; exact hL012
  have hP1L0P2 : EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H 1 (0, y))
      (linTransClass (linBase A 0) ((blk 0) t) c hc)
      (designPertClass Q (designAngles a c' 2) t 2) := by
    rw [hHend0 1]; exact endTripleReg_swap23_row (endTripleReg_cyclic hL012)
  have hL10P2' : EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H 1 (1, y))
      (linTransClass (linBase A 0) ((blk 0) t) c hc)
      (designPertClass Q (designAngles a c' 2) t 2) := by
    rw [hHend1 1]; exact hL10P2
  have hP2L0L1 : EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H 2 (0, y))
      (linTransClass (linBase A 0) ((blk 0) t) c hc)
      (linTransClass (linBase A 1) ((blk 1) t) c hc) := by
    rw [hHend0 2]
    exact endTripleReg_swap23_row (endTripleReg_cyclic (endTripleReg_cyclic hL10P2))
  have hLLL' : EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) => H 2 (1, y))
      (linTransClass (linBase A 0) ((blk 0) t) c hc)
      (linTransClass (linBase A 1) ((blk 1) t) c hc) := by
    rw [hHend1 2]; exact hLLL
  -- ## the three clauses of the linearisation, each by the ends-clause genericity (section 2.1)
  have hc₀0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hc₀1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨H0', hH0'0, hH0'1, hM0⟩ := exists_homotopy_meet3Hyp_encoded_viaReparam
    (H := H 0) (A := designPertClass Q (designAngles a c' 1) t 1)
    (B := designPertClass Q (designAngles a c' 2) t 2) hc₀0 hc₀1
    (hsmH 0) (hsmPert 1) (hsmPert 2) (hseamH 0) (hseamPert 1) (hseamPert 2)
    (fun s hs y => hconst0 0 s hs y) (fun s hs y => hconst1 0 s hs y)
    hpair12 h012' hL012' (hfoldPert 1) (hfoldPert 2)
    (by rw [hHend0 0]; exact hfoldPert 0)
    (by rw [hHend1 0]; exact hfoldLin 0)
  obtain ⟨H1', hH1'0, hH1'1, hM1⟩ := exists_homotopy_meet3Hyp_encoded_viaReparam
    (H := H 1) (A := linTransClass (linBase A 0) ((blk 0) t) c hc)
    (B := designPertClass Q (designAngles a c' 2) t 2) hc₀0 hc₀1
    (hsmH 1) (hsmLin 0) (hsmPert 2) (hseamH 1) (hseamLin 0) (hseamPert 2)
    (fun s hs y => hconst0 1 s hs y) (fun s hs y => hconst1 1 s hs y)
    hpairL0P2 hP1L0P2 hL10P2' (hfoldLin 0) (hfoldPert 2)
    (by rw [hHend0 1]; exact hfoldPert 1)
    (by rw [hHend1 1]; exact hfoldLin 1)
  obtain ⟨H2', hH2'0, hH2'1, hM2⟩ := exists_homotopy_meet3Hyp_encoded_viaReparam
    (H := H 2) (A := linTransClass (linBase A 0) ((blk 0) t) c hc)
    (B := linTransClass (linBase A 1) ((blk 1) t) c hc) hc₀0 hc₀1
    (hsmH 2) (hsmLin 0) (hsmLin 1) (hseamH 2) (hseamLin 0) (hseamLin 1)
    (fun s hs y => hconst0 2 s hs y) (fun s hs y => hconst1 2 s hs y)
    hpairL0L1 hP2L0L1 hLLL' (hfoldLin 0) (hfoldLin 1)
    (by rw [hHend0 2]; exact hfoldPert 2)
    (by rw [hHend1 2]; exact hfoldLin 2)
  -- ## the class linearisation, and the oddness of the class-triple count
  refine odd_ncard_classTripleSet_of_hasClassLinearization (P := fun k => designPertPlane Q
      (designAngles a c' k) t k) ?_
  refine ⟨fun k => (linBase A k).trans (classEquiv ((blk k) t)), c, hc, hrank_t, hgen_t,
    ![H0', H1', H2'], 1 / 2, hc₀0, hc₀1, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · funext y
      change H0' (0, y) = designPertClass Q (designAngles a c' 0) t 0 y
      rw [hH0'0 y]
      exact congrFun (hHend0 0) y
    · funext y
      change H1' (0, y) = designPertClass Q (designAngles a c' 1) t 1 y
      rw [hH1'0 y]
      exact congrFun (hHend0 1) y
    · funext y
      change H2' (0, y) = designPertClass Q (designAngles a c' 2) t 2 y
      rw [hH2'0 y]
      exact congrFun (hHend0 2) y
  · intro k
    fin_cases k
    · funext y
      change H0' (1, y) = linTransClass (linBase A 0) ((blk 0) t) c hc y
      rw [hH0'1 y]
      exact congrFun (hHend1 0) y
    · funext y
      change H1' (1, y) = linTransClass (linBase A 1) ((blk 1) t) c hc y
      rw [hH1'1 y]
      exact congrFun (hHend1 1) y
    · funext y
      change H2' (1, y) = linTransClass (linBase A 2) ((blk 2) t) c hc y
      rw [hH2'1 y]
      exact congrFun (hHend1 2) y
  · change Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ) (encodedChains
      (fun x : EuclideanSpace ℝ (Fin 3) => H0' (x 2, pt2 (x 0) (x 1)))
      (designPertClass Q (designAngles a c' 1) t 1)
      (designPertClass Q (designAngles a c' 2) t 2) (1 / 2))
    exact hM0
  · change Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ) (encodedChains
      (fun x : EuclideanSpace ℝ (Fin 3) => H1' (x 2, pt2 (x 0) (x 1)))
      (linTransClass (linBase A 0) ((blk 0) t) c hc)
      (designPertClass Q (designAngles a c' 2) t 2) (1 / 2))
    exact hM1
  · change Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ) (encodedChains
      (fun x : EuclideanSpace ℝ (Fin 3) => H2' (x 2, pt2 (x 0) (x 1)))
      (linTransClass (linBase A 0) ((blk 0) t) c hc)
      (linTransClass (linBase A 1) ((blk 1) t) c hc) (1 / 2))
    exact hM2

end

end Work.Drive
