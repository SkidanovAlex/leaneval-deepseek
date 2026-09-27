import Mathlib
import Submission.Work.PL.Defs

/-!
# A sub-chart of a cube chart avoiding a closed set (`Work.Cells.Connell`)

Newman's smoothing argument (blueprint §4 / area `A8`) needs, near a point `c y₀` of a cube
chart `c : PL.E n → M` that lies outside a closed set `A`, a *shrunk* cube chart: the map
`z ↦ c (y₀ + r • z)` for a small `r > 0` whose unit cube lies entirely in the complement of
`A`, extended by a constant `p ∈ Aᶜ` outside the open unit cube.

`Work.Cells.Connell.exists_cubeChart_subcube` produces such a chart `ψ : PL.CubeChart n ↥(Aᶜ)`
together with the scaling factor `r > 0`.
-/

open Set Metric

namespace Work.Cells.Connell

/-- The open sup-norm cube `PL.openCube r` of `E n` is open. -/
private theorem isOpen_openCube' (n : ℕ) (r : ℝ) : IsOpen (PL.openCube (n := n) r) := by
  have h : PL.openCube (n := n) r = ⋂ i : Fin n, {x : PL.E n | |x i| < r} := by
    ext x; simp [PL.openCube]
  rw [h]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt (by fun_prop) continuous_const)

/-- A point of the closed sup-norm cube of size `1` in `E n` has Euclidean norm at most `√n`. -/
private theorem norm_le_sqrt_of_mem_closedCube {n : ℕ} {z : PL.E n}
    (hz : z ∈ PL.closedCube (n := n) (1 : ℝ)) : ‖z‖ ≤ Real.sqrt (n : ℝ) := by
  have hsq : ‖z‖ ^ 2 ≤ (n : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i : Fin n, z i ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro i _
          have := abs_le.mp (hz i); nlinarith
      _ = (n : ℝ) := by simp
  rw [← Real.sqrt_sq (norm_nonneg z)]
  exact Real.sqrt_le_sqrt hsq

/-- **A shrunk cube chart avoiding a closed set.**  If the closed set `A ⊆ M` misses `c y₀`
for a cube chart `c : PL.CubeChart n M`, then some sub-cube `z ↦ c (y₀ + r • z)` of `c` lies
entirely in `Aᶜ`; pushing it forward, extended by an arbitrary point `p ∈ Aᶜ` of the complement
outside the unit cube, gives a cube chart of `↥(Aᶜ)`. -/
theorem exists_cubeChart_subcube {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) (y₀ : PL.E n) (hy₀ : y₀ ∈ PL.openCube (n := n) 1)
    (A : Set M) (hA : IsClosed A) (hyA : c.toFun y₀ ∉ A) (p : ↥(Aᶜ)) :
    ∃ r : ℝ, 0 < r ∧ ∃ ψ : PL.CubeChart n ↥(Aᶜ),
      (∀ z ∈ PL.openCube (n := n) 1, (ψ.toFun z : M) = c.toFun (y₀ + r • z)) ∧
      (∀ z, z ∉ PL.openCube (n := n) 1 → ψ.toFun z = p) ∧
      (∀ z ∈ PL.closedCube (1 : ℝ), y₀ + r • z ∈ PL.openCube (n := n) 1 ∧
        c.toFun (y₀ + r • z) ∈ Aᶜ) := by
  classical
  -- `openCube 1` is open, so it contains a ball around `y₀`
  have hsopen : IsOpen (PL.openCube (n := n) 1) := isOpen_openCube' n 1
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp (hsopen.mem_nhds hy₀)
  -- and by continuity of `c` at `y₀`, a ball around `y₀` is mapped into `Aᶜ`
  have hAopen : IsOpen (Aᶜ) := hA.isOpen_compl
  have hcontWithin : ContinuousWithinAt c.toFun (PL.openCube (n := n) 1) y₀ :=
    c.cont.continuousWithinAt hy₀
  have hpre : c.toFun ⁻¹' Aᶜ ∈ nhdsWithin y₀ (PL.openCube (n := n) 1) :=
    hcontWithin.preimage_mem_nhdsWithin (hAopen.mem_nhds hyA)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := mem_nhdsWithin_iff.mp hpre
  -- choose a small scaling factor `r`
  have hSnonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  let m : ℝ := min δ₁ δ₂
  have hmpos : 0 < m := lt_min hδ₁pos hδ₂pos
  let r : ℝ := min (m / (2 * (Real.sqrt (n : ℝ) + 1))) 1
  have hrpos : 0 < r := by
    refine lt_min ?_ one_pos
    exact div_pos hmpos (by positivity)
  have hrle : r ≤ m / (2 * (Real.sqrt (n : ℝ) + 1)) := min_le_left _ _
  have hrS : r * Real.sqrt (n : ℝ) < m := by
    have hden : 0 < 2 * (Real.sqrt (n : ℝ) + 1) := by positivity
    have h2 : r * (2 * (Real.sqrt (n : ℝ) + 1)) ≤ m := by
      calc r * (2 * (Real.sqrt (n : ℝ) + 1))
          ≤ (m / (2 * (Real.sqrt (n : ℝ) + 1))) * (2 * (Real.sqrt (n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right hrle hden.le
        _ = m := by field_simp
    nlinarith [h2, hrpos, hSnonneg]
  -- the closed unit cube is sent by `z ↦ y₀ + r • z` into the two balls
  have hdist : ∀ z ∈ PL.closedCube (n := n) (1 : ℝ), dist (y₀ + r • z) y₀ < m := by
    intro z hz
    have hsub : (y₀ + r • z) - y₀ = r • z := by abel
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg hrpos.le]
    have h1 : ‖z‖ ≤ Real.sqrt (n : ℝ) := norm_le_sqrt_of_mem_closedCube hz
    have h2 := mul_le_mul_of_nonneg_left h1 hrpos.le
    linarith [hrS, h2]
  -- consequently the shrunk closed cube lies in `openCube 1` and `c` maps it into `Aᶜ`
  have hcond3 : ∀ z ∈ PL.closedCube (n := n) (1 : ℝ), y₀ + r • z ∈ PL.openCube (n := n) 1 ∧
      c.toFun (y₀ + r • z) ∈ Aᶜ := by
    intro z hz
    have hd := hdist z hz
    have hlt1 : dist (y₀ + r • z) y₀ < δ₁ := lt_of_lt_of_le hd (min_le_left _ _)
    have hlt2 : dist (y₀ + r • z) y₀ < δ₂ := lt_of_lt_of_le hd (min_le_right _ _)
    have hopen : y₀ + r • z ∈ PL.openCube (n := n) 1 := hδ₁ (mem_ball.mpr hlt1)
    exact ⟨hopen, hδ₂ ⟨mem_ball.mpr hlt2, hopen⟩⟩
  -- the translating/scaling map, as an open embedding of the open cube into itself
  let s : Set (PL.E n) := PL.openCube (n := n) 1
  have hsub_closed : s ⊆ PL.closedCube (n := n) (1 : ℝ) := fun x hx i => le_of_lt (hx i)
  let g : PL.E n → PL.E n := fun z => y₀ + r • z
  have hg_open : Topology.IsOpenEmbedding g := by
    have h1 : g =
        ⇑((Homeomorph.smulOfNeZero r (ne_of_gt hrpos)).trans (Homeomorph.addLeft y₀)) := by
      funext z; simp [g, Homeomorph.trans_apply]
    rw [h1]; exact Homeomorph.isOpenEmbedding _
  let τ : ↥s → ↥s := fun z => ⟨g z, (hcond3 z (hsub_closed z.2)).1⟩
  have hτ : Topology.IsOpenEmbedding τ := by
    apply (Topology.IsOpenEmbedding.of_comp_iff τ hsopen.isOpenEmbedding_subtypeVal).mp
    have h2 : Topology.IsOpenEmbedding (g ∘ (Subtype.val : ↥s → PL.E n)) :=
      hg_open.comp hsopen.isOpenEmbedding_subtypeVal
    convert h2 using 1
    ext z; rfl
  -- the new chart map: the sub-cube inside the open cube, and `p` outside
  let hmem : ∀ z : PL.E n, z ∈ s → c.toFun (g z) ∈ Aᶜ :=
    fun z hz => (hcond3 z (hsub_closed hz)).2
  let ψfun : PL.E n → ↥(Aᶜ) := fun z => if hz : z ∈ s then ⟨c.toFun (g z), hmem z hz⟩ else p
  have hFcont : Continuous (s.domRestrict ψfun) := by
    have hcomp : Continuous (fun x : ↥s => c.toFun (g (x : PL.E n))) := by
      have h := c.cont.comp_continuous (continuous_subtype_val.comp hτ.continuous)
        (fun x => (τ x).2)
      convert h using 1
      ext x
      simp only [Function.comp_apply, τ]
    have hF : (s.domRestrict ψfun) =
        fun x : ↥s => (⟨c.toFun (g (x : PL.E n)), hmem (x : PL.E n) x.2⟩ : ↥(Aᶜ)) := by
      funext x
      simp only [Set.domRestrict, ψfun, dite_eq_left x.2]
    rw [hF]
    exact Continuous.subtype_mk hcomp (fun x => hmem (x : PL.E n) x.2)
  have hemb : Topology.IsOpenEmbedding (s.domRestrict ψfun) := by
    have hι : Topology.IsOpenEmbedding (Subtype.val : ↥(Aᶜ) → M) :=
      hAopen.isOpenEmbedding_subtypeVal
    have hcomp : Topology.IsOpenEmbedding ((s.domRestrict c.toFun) ∘ τ) := c.emb.comp hτ
    have heq : ((Subtype.val : ↥(Aᶜ) → M) ∘ (s.domRestrict ψfun)) =
        ((s.domRestrict c.toFun) ∘ τ) := by
      funext x
      simp only [Function.comp_apply, Set.domRestrict, ψfun, dite_eq_left x.2, τ]
    exact (Topology.IsOpenEmbedding.of_comp_iff (s.domRestrict ψfun) hι).mp (heq.symm ▸ hcomp)
  refine ⟨r, hrpos, ?_⟩
  refine ⟨{ toFun := ψfun, cont := ?_, emb := hemb }, ?_, ?_, ?_⟩
  · exact continuousOn_iff_continuous_domRestrict.mpr hFcont
  · intro z hz
    have hz' : z ∈ s := hz
    simp only [ψfun, dite_eq_left hz', g]
  · intro z hz
    have hz' : z ∉ s := hz
    simp only [ψfun, dite_eq_right hz']
  · exact hcond3

end Work.Cells.Connell
