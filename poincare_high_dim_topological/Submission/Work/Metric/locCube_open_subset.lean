import Mathlib
import Submission.Work.PL.Defs

open Set Metric Filter
open scoped Topology

namespace Work.Metric

/-- The open sup-norm cube `PL.openCube r` of `E n` is open. -/
theorem isOpen_openCube (n : ℕ) (r : ℝ) : IsOpen (PL.openCube (n := n) r) := by
  have h : PL.openCube (n := n) r = ⋂ i : Fin n, {x : PL.E n | |x i| < r} := by
    ext x; simp [PL.openCube]
  rw [h]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt (by fun_prop) continuous_const)

/-- A point of the unit sup-norm cube in `E n` has Euclidean norm at most `√n`. -/
theorem norm_le_sqrt_of_mem_openCube {n : ℕ} {z : PL.E n}
    (hz : z ∈ PL.openCube (n := n) 1) : ‖z‖ ≤ Real.sqrt (n : ℝ) := by
  have hsq : ‖z‖ ^ 2 ≤ (n : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i : Fin n, z i ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum; intro i _
          nlinarith [abs_lt.mp (hz i)]
      _ = (n : ℝ) := by simp
  rw [← Real.sqrt_sq (norm_nonneg z)]
  exact Real.sqrt_le_sqrt hsq

/-- The unit sup-norm cube of `E n` (the domain of a `PL.CubeChart`). -/
abbrev unitCube (n : ℕ) : Set (PL.E n) := PL.openCube (n := n) 1

theorem locCube_open_subset (n : ℕ) (M : Type*) [TopologicalSpace M] (h : PL.LocCube n M)
    (U : Set M) (hU : IsOpen U) : PL.LocCube n U := by
  classical
  intro x
  obtain ⟨ψ, hxψ⟩ := h x.1
  rw [Set.mem_image] at hxψ
  obtain ⟨y, hy_mem, hy_eq⟩ := hxψ
  have hxU : ψ.toFun y ∈ U := by rw [hy_eq]; exact x.2
  have hy_s : y ∈ unitCube n := fun i => lt_trans (hy_mem i) (by norm_num)
  -- a neighbourhood of `y` in the chart on which `ψ.toFun` lands in `U`
  let e : ↥(unitCube n) → M := (unitCube n).domRestrict ψ.toFun
  have he : Topology.IsOpenEmbedding e := ψ.emb
  let y' : ↥(unitCube n) := ⟨y, hy_s⟩
  have hey' : e y' = ψ.toFun y := rfl
  have hUnhds : U ∈ 𝓝 (e y') := by rw [hey']; exact hU.mem_nhds hxU
  have hpre : e ⁻¹' U ∈ 𝓝 y' := he.continuous.continuousAt.preimage_mem_nhds hUnhds
  obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.mp hpre
  have hδprop : ∀ z : PL.E n, z ∈ unitCube n → dist z y < δ → ψ.toFun z ∈ U := by
    intro z hz hdz
    have h1 : (⟨z, hz⟩ : ↥(unitCube n)) ∈ Metric.ball y' δ := by
      rw [Metric.mem_ball, Subtype.dist_eq]
      simpa [y'] using hdz
    simpa [e, Set.domRestrict] using hδball h1
  -- choose a small scaling factor
  let R : ℝ := Real.sqrt (n : ℝ)
  have hRnn : 0 ≤ R := Real.sqrt_nonneg _
  let r : ℝ := min (1/4) (δ / (2 * (R + 1)))
  have hrpos : 0 < r := by
    refine lt_min (by norm_num) ?_
    positivity
  have hrle : r ≤ 1/4 := min_le_left _ _
  have hrR : r * R < δ := by
    have h1 : r ≤ δ / (2 * (R + 1)) := min_le_right _ _
    have h2 : r * (R + 1) ≤ δ / 2 := by
      calc r * (R + 1) ≤ (δ / (2 * (R + 1))) * (R + 1) :=
            mul_le_mul_of_nonneg_right h1 (by linarith)
        _ = δ / 2 := by field_simp
    have h3 : r * R ≤ r * (R + 1) := by nlinarith [hrpos, hRnn]
    linarith
  -- the scaled cube stays inside the unit cube
  have hyz : ∀ z : PL.E n, z ∈ unitCube n → y + r • z ∈ unitCube n := by
    intro z hz i
    have hyi := abs_lt.mp (hy_mem i)
    have hzi := abs_lt.mp (hz i)
    have hcoord : (y + r • z) i = y i + r * z i := by simp [PiLp.add_apply, PiLp.smul_apply]
    rw [hcoord, abs_lt]
    refine ⟨?_, ?_⟩ <;> nlinarith [hyi.1, hyi.2, hzi.1, hzi.2, hrpos, hrle]
  -- and inside the δ-ball around `y`
  have hdiff : ∀ z : PL.E n, z ∈ unitCube n → dist (y + r • z) y < δ := by
    intro z hz
    have hsub : (y + r • z) - y = r • z := by abel
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg hrpos.le]
    have hzR : ‖z‖ ≤ R := norm_le_sqrt_of_mem_openCube hz
    have := mul_le_mul_of_nonneg_left hzR hrpos.le
    linarith
  have hmem : ∀ z : PL.E n, z ∈ unitCube n → ψ.toFun (y + r • z) ∈ U :=
    fun z hz => hδprop (y + r • z) (hyz z hz) (hdiff z hz)
  -- the new chart map
  let F : PL.E n → U :=
    fun z => if hz : z ∈ unitCube n then ⟨ψ.toFun (y + r • z), hmem z hz⟩ else x
  have hF_apply : ∀ (z : PL.E n) (hz : z ∈ unitCube n),
      F z = ⟨ψ.toFun (y + r • z), hmem z hz⟩ := by
    intro z hz
    simp only [F]
    rw [dite_eq_left hz]
  have hG_eq : (Subtype.val : U → M) ∘ (unitCube n).domRestrict F
      = (unitCube n).domRestrict (fun z : PL.E n => ψ.toFun (y + r • z)) := by
    funext z
    simp only [Function.comp_apply, Set.domRestrict]
    rw [hF_apply z z.2]
  -- the scaled cube, seen as a self-map of the unit cube, is an open embedding
  let τ : ↥(unitCube n) → ↥(unitCube n) :=
    fun z => ⟨y + r • (z : PL.E n), hyz (z : PL.E n) z.2⟩
  have hτ : Topology.IsOpenEmbedding τ := by
    apply (Topology.IsOpenEmbedding.of_comp_iff τ
      (isOpen_openCube n 1).isOpenEmbedding_subtypeVal).1
    have hσ : Topology.IsOpenEmbedding (fun w : PL.E n => y + r • w) := by
      have hh := (Homeomorph.addLeft y).isOpenEmbedding.comp
        (Homeomorph.smulOfNeZero r (ne_of_gt hrpos)).isOpenEmbedding
      exact hh
    have hcomp := hσ.comp (isOpen_openCube n 1).isOpenEmbedding_subtypeVal
    convert hcomp using 1
    ext z
    rfl
  have hGemb : Topology.IsOpenEmbedding
      ((unitCube n).domRestrict (fun z : PL.E n => ψ.toFun (y + r • z))) := by
    have hcomp := he.comp hτ
    convert hcomp using 1
    ext z
    rfl
  have hemb : Topology.IsOpenEmbedding ((unitCube n).domRestrict F) := by
    apply (Topology.IsOpenEmbedding.of_comp_iff ((unitCube n).domRestrict F)
      hU.isOpenEmbedding_subtypeVal).1
    rw [hG_eq]
    exact hGemb
  refine ⟨{ toFun := F
            cont := continuousOn_iff_continuous_domRestrict.mpr hemb.continuous
            emb := hemb }, ⟨0, ?_, ?_⟩⟩
  · intro i; simp
  · change F 0 = x
    rw [hF_apply 0 (by intro i; simp)]
    exact Subtype.ext (by simp [hy_eq])

end Work.Metric
