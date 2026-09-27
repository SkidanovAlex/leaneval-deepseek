import Mathlib
import Submission.Work.Drive.ManifoldParity.InterSetFlowDefs
import Submission.Work.Drive.finite_of_isCompact_of_isolated

namespace Work.Drive.ManifoldParity

open scoped Manifold ContDiff Topology
open Set Manifold

set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## Isolation of a boundary intersection point on a face

The finiteness of `bInterSet D N` rests on the following local statement: a boundary intersection
point `b` lying on the face with (ambient) coordinate `p` — all the other coordinates of `b` strictly
inside `(0,1)` — is isolated in `bInterSet D N`, provided the derivative of the charted difference
map at `b` is surjective on the coordinate hyperplane `{v | v p = 0}`.

Indeed, `Work.Drive.exists_local_graph` exhibits the intersection set near `b` as the graph
`y ↦ (y p) • e_p + η (y p)` over the `p`-th coordinate.  The open neighbourhood of `b` on which this
graph description is available, intersected with the open condition "all other coordinates are
strictly inside", meets `bInterSet D N` only in `b`: a boundary intersection point `y` close to `b`
must be on the face `p` (its other coordinates are strictly inside), and its `p`-th coordinate is a
boundary value within `1` of `b p ∈ {0,1}`, hence equal to it. -/
theorem isolated_of_face {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    {b : Work.Drive.Amb 4} (hbb : b ∈ Submission.Drive.unitBox 4)
    (hbeq : D (Work.Drive.sqPart b) = N (Work.Drive.cbPart b))
    (p : Fin 5) (hpe : b p = 0 ∨ b p = 1)
    (hpo : ∀ q : Fin 5, q ≠ p → b q ∈ Set.Ioo (0 : ℝ) 1)
    (hsurj_p : Function.Surjective (fun v : {v : Work.Drive.Amb 4 // v p = 0} =>
      fderiv ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart b)) D N) b v.1)) :
    ∃ U : Set (Work.Drive.Amb 4), IsOpen U ∧ b ∈ U ∧
      U ∩ Work.Drive.bInterSet D N ⊆ {b} := by
  have hbreg : b ∈ Work.Drive.chartRegion (D (Work.Drive.sqPart b)) D N := by
    rw [Work.Drive.mem_chartRegion]
    exact ⟨mem_chart_source _ _, by rw [← hbeq]; exact mem_chart_source _ _⟩
  obtain ⟨δ₀, ρ, η, hδ₀, hρ, hηsmooth, hηi, hηb, hchar⟩ :=
    Work.Drive.exists_local_graph (D (Work.Drive.sqPart b)) D N hD hN hbreg hbeq p hsurj_p
  have hηc : Continuous η := hηsmooth.continuous
  set δ : ℝ := min δ₀ 1 with hδdef
  have hδ : 0 < δ := lt_min hδ₀ one_pos
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  -- the three open conditions defining the neighbourhood
  have hU1 : IsOpen {y : Work.Drive.Amb 4 | |y p - b p| < δ} := by
    have hcont : Continuous fun y : Work.Drive.Amb 4 => |y p - b p| :=
      (((PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) p)).sub continuous_const).abs
    exact isOpen_Iio.preimage hcont
  have hU2 : IsOpen {y : Work.Drive.Amb 4 |
      ‖y - (y p) • EuclideanSpace.single p (1 : ℝ) - η (y p)‖ < ρ} := by
    have hcont : Continuous fun y : Work.Drive.Amb 4 =>
        y - (y p) • EuclideanSpace.single p (1 : ℝ) - η (y p) := by
      fun_prop
    exact isOpen_Iio.preimage hcont.norm
  have hU3 : IsOpen {y : Work.Drive.Amb 4 | ∀ q : Fin 5, q ≠ p → y q ∈ Set.Ioo (0 : ℝ) 1} := by
    have hset : {y : Work.Drive.Amb 4 | ∀ q : Fin 5, q ≠ p → y q ∈ Set.Ioo (0 : ℝ) 1} =
        ⋂ (q : {q : Fin 5 // q ≠ p}),
          {y : Work.Drive.Amb 4 | y (q : Fin 5) ∈ Set.Ioo (0 : ℝ) 1} := by
      ext y
      simp [Set.mem_iInter, Subtype.forall]
    rw [hset]
    exact isOpen_iInter_of_finite fun q =>
      isOpen_Ioo.preimage (PiLp.continuous_apply 2 (fun _ : Fin 5 => ℝ) (q : Fin 5))
  refine ⟨{y : Work.Drive.Amb 4 | |y p - b p| < δ} ∩
      {y : Work.Drive.Amb 4 |
        ‖y - (y p) • EuclideanSpace.single p (1 : ℝ) - η (y p)‖ < ρ} ∩
      {y : Work.Drive.Amb 4 | ∀ q : Fin 5, q ≠ p → y q ∈ Set.Ioo (0 : ℝ) 1},
    (hU1.inter hU2).inter hU3, ⟨⟨?_, ?_⟩, hpo⟩, ?_⟩
  · show |b p - b p| < δ
    rw [sub_self, abs_zero]; exact hδ
  · show ‖b - (b p) • EuclideanSpace.single p (1 : ℝ) - η (b p)‖ < ρ
    rw [hηb, sub_self, norm_zero]; exact hρ
  · rintro y ⟨⟨⟨hy1, hy2⟩, hy3⟩, hyS⟩
    obtain ⟨hybox, hyeq, hybdry⟩ := Work.Drive.mem_bInterSet.mp hyS
    have hy1₀ : |y p - b p| < δ₀ := lt_of_lt_of_le hy1 hδδ₀
    obtain ⟨-, r, hr⟩ := hybdry
    have hrp : r = p := by
      by_contra hne
      have hyr : y r ∈ Set.Ioo (0 : ℝ) 1 := hy3 r hne
      rcases hr with h | h
      · rw [h] at hyr
        exact lt_irrefl 0 hyr.1
      · rw [h] at hyr
        exact lt_irrefl 1 hyr.2
    have hyp : y p = 0 ∨ y p = 1 := by
      rcases hr with h | h
      · left; rwa [hrp] at h
      · right; rwa [hrp] at h
    have hsub1 : |y p - b p| < 1 := lt_of_lt_of_le hy1 hδ1
    have hypb : y p = b p := by
      rcases hyp with h | h <;> rcases hpe with h' | h'
      · rw [h, h']
      · rw [h, h'] at hsub1; norm_num at hsub1
      · rw [h, h'] at hsub1; norm_num at hsub1
      · rw [h, h']
    have hgraph := (hchar y hy1₀ hy2).2
    have hyeq' : y = (y p) • EuclideanSpace.single p (1 : ℝ) + η (y p) := hgraph.mp hyeq
    have hbgraph : b = (b p) • EuclideanSpace.single p (1 : ℝ) + η (b p) := by
      rw [hηb]; abel
    have hyb : y = b := by
      calc y = (y p) • EuclideanSpace.single p (1 : ℝ) + η (y p) := hyeq'
        _ = (b p) • EuclideanSpace.single p (1 : ℝ) + η (b p) := by rw [hypb]
        _ = b := hbgraph.symm
    simpa using hyb

end

open scoped Manifold ContDiff in
/-- **Finiteness of the boundary intersection set.**  For smooth chains `D : ℝ² → M`,
`N : ℝ³ → M` in a smooth 4-manifold `M`, meeting transversally (`htrans`) and satisfying the face
hypothesis `hface` (every boundary intersection lies on exactly one face of the box, the other
coordinates strictly inside, with a common tangent direction `(σ,τ)` non-zero in that coordinate),
the set `bInterSet D N` of intersection points on the boundary of the box is finite.

This is the finiteness half of the vector-space statement `Submission.Drive.ParityProp`, and needs no
field: the local graph structure (`Work.Drive.exists_local_graph` at the face coordinate, obtained
from `Work.Drive.chartDiff_face_of_kernel` and `Work.Drive.chartDiff_surjective_of_transverse`)
shows that each `b ∈ bInterSet D N` is isolated in `bInterSet D N`: near `b` the intersection set is
the graph `u ↦ u • eᵢ + η u` over the face coordinate `i`, while a boundary intersection near `b`
must lie on the face `i` (all other coordinates are strictly inside) and has its `i`-th coordinate
within `1` of `b`'s, hence equal to it.  Compactness of `interSet D N`
(`Work.Drive.isCompact_interSet`, from continuity of `D` and `N`) then gives finiteness via
`Work.Drive.finite_of_isCompact_of_isolated` (the argument is the manifold analogue of
`Work.Drive.bdyZeros_isolated`; the block-index bookkeeping can use
`Work.Drive.exists_fin_five_iff`, `Work.Drive.sqPart_apply`, `Work.Drive.cbPart_apply`). -/
theorem finite_bInterSet {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    (htrans : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x)).toLinearMap = ⊤)
    (hface : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) → x ∈ Submission.Drive.unitBoxBdry 4 →
      (∃ i : Fin 2, (Work.Drive.sqPart x i = 0 ∨ Work.Drive.sqPart x i = 1) ∧
          (∀ j : Fin 2, j ≠ i → Work.Drive.sqPart x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, Work.Drive.cbPart x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x) σ =
              mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x) τ ∧ σ i ≠ 0)
      ∨ (∃ j : Fin 3, (Work.Drive.cbPart x j = 0 ∨ Work.Drive.cbPart x j = 1) ∧
          (∀ k : Fin 3, k ≠ j → Work.Drive.cbPart x k ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ i : Fin 2, Work.Drive.sqPart x i ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart x) σ =
              mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart x) τ ∧ τ j ≠ 0)) :
    (Work.Drive.bInterSet D N).Finite := by
  classical
  have hDc : Continuous D := hD.continuous
  have hNc : Continuous N := hN.continuous
  have hisol : ∀ b ∈ Work.Drive.bInterSet D N, ∃ U : Set (Work.Drive.Amb 4),
      IsOpen U ∧ b ∈ U ∧ U ∩ Work.Drive.bInterSet D N ⊆ {b} := by
    intro b hb
    obtain ⟨hbb, hbeq, hbbd⟩ := Work.Drive.mem_bInterSet.mp hb
    have hbreg : b ∈ Work.Drive.chartRegion (D (Work.Drive.sqPart b)) D N := by
      rw [Work.Drive.mem_chartRegion]
      exact ⟨mem_chart_source _ _, by rw [← hbeq]; exact mem_chart_source _ _⟩
    have hsurj : Function.Surjective
        (fderiv ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart b)) D N) b) :=
      Work.Drive.chartDiff_surjective_of_transverse (D (Work.Drive.sqPart b)) D N hD hN hbreg hbeq
        (htrans b hbb hbeq)
    rcases hface b hbb hbeq hbbd with
      ⟨i, hi0, hiin, hjin, σ, τ, hστ, hσne⟩ | ⟨j, hj0, hjin, hiin, σ, τ, hστ, hτne⟩
    · have hker : Work.Drive.mkPart σ τ (Work.Drive.sqIdx i) ≠ 0 := by
        rw [Work.Drive.mkPart_sqIdx]; exact hσne
      refine isolated_of_face D N hD hN hbb hbeq (Work.Drive.sqIdx i) ?_ ?_ ?_
      · rcases hi0 with h | h
        · left; simpa using h
        · right; simpa using h
      · intro q hq
        revert hq
        refine Fin.addCases (m := 2) (n := 3)
          (motive := fun q => q ≠ Work.Drive.sqIdx i → b q ∈ Set.Ioo (0 : ℝ) 1) ?_ ?_ q
        · intro i' hne
          have hne' : i' ≠ i := fun h => hne (by
            show Work.Drive.sqIdx i' = Work.Drive.sqIdx i
            rw [h])
          show b (Work.Drive.sqIdx i') ∈ Set.Ioo (0 : ℝ) 1
          rw [← Work.Drive.sqPart_apply]
          exact hiin i' hne'
        · intro j' _
          show b (Work.Drive.cbIdx j') ∈ Set.Ioo (0 : ℝ) 1
          rw [← Work.Drive.cbPart_apply]
          exact hjin j'
      · exact Work.Drive.chartDiff_face_of_kernel (D (Work.Drive.sqPart b)) D N hD hN hbreg hbeq
          hsurj hστ hker
    · have hker : Work.Drive.mkPart σ τ (Work.Drive.cbIdx j) ≠ 0 := by
        rw [Work.Drive.mkPart_cbIdx]; exact hτne
      refine isolated_of_face D N hD hN hbb hbeq (Work.Drive.cbIdx j) ?_ ?_ ?_
      · rcases hj0 with h | h
        · left; simpa using h
        · right; simpa using h
      · intro q hq
        revert hq
        refine Fin.addCases (m := 2) (n := 3)
          (motive := fun q => q ≠ Work.Drive.cbIdx j → b q ∈ Set.Ioo (0 : ℝ) 1) ?_ ?_ q
        · intro i' _
          show b (Work.Drive.sqIdx i') ∈ Set.Ioo (0 : ℝ) 1
          rw [← Work.Drive.sqPart_apply]
          exact hiin i'
        · intro j' hne
          have hne' : j' ≠ j := fun h => hne (by
            show Work.Drive.cbIdx j' = Work.Drive.cbIdx j
            rw [h])
          show b (Work.Drive.cbIdx j') ∈ Set.Ioo (0 : ℝ) 1
          rw [← Work.Drive.cbPart_apply]
          exact hjin j' hne'
      · exact Work.Drive.chartDiff_face_of_kernel (D (Work.Drive.sqPart b)) D N hD hN hbreg hbeq
          hsurj hστ hker
  have hclosed : IsClosed (Work.Drive.bInterSet D N) := by
    have h1 : IsClosed {x : Work.Drive.Amb 4 |
        D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x)} :=
      isClosed_eq (hDc.comp (by unfold Work.Drive.sqPart; fun_prop))
        (hNc.comp (by unfold Work.Drive.cbPart; fun_prop))
    have h2 : Work.Drive.bInterSet D N = Submission.Drive.unitBoxBdry 4 ∩
        {x : Work.Drive.Amb 4 | D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x)} := by
      ext x
      constructor
      · intro h
        obtain ⟨hbox, heq, hbdry⟩ := Work.Drive.mem_bInterSet.mp h
        exact ⟨hbdry, heq⟩
      · intro h
        rw [Work.Drive.mem_bInterSet]
        exact ⟨h.1.1, h.2, h.1⟩
    rw [h2]
    exact (Work.Drive.isClosed_unitBoxBdry 4).inter h1
  have hKc : IsCompact (Work.Drive.bInterSet D N) :=
    (Work.Drive.isCompact_interSet D N hDc hNc).of_isClosed_subset hclosed
      (Work.Drive.bInterSet_subset_interSet D N)
  exact Work.Drive.finite_of_isCompact_of_isolated hKc hisol

end Work.Drive.ManifoldParity
