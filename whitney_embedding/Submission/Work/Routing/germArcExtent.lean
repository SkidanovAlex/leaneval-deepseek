import Mathlib
import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm
import Submission.Work.Crux.reparam_gen

/-!
# The seed arc with a *prescribed* germ extent

`Work.Noncompact.CompressionTube.germArcExtent` is `exists_germ_arc_gen` with the (existential)
germ extent `e₀` replaced by a *prescribed* length `L`: the straight germ `t ↦ c.symm (c p + t • v)`
is realised on the whole interval `[0,L]`, the arc is a global smooth immersion, injective on
`[0,1]`, inside `W`, and it ends with a straight germ in the same chart.

The room hypotheses are exactly what the germ identity needs: the chart line stays in `c.target`
for `|t| < min ρpos ρneg` and its `c.symm`-image stays in `W` for `0 < t < min ρpos ρneg`; the
prescribed length `L` must lie below that room and below the affine threshold `h < 1`.

This is the tool that lets a *stage* of the routing choose the extent of the straight germ at its
starting junction, which is what the rootedness bookkeeping of the lane recursion consumes.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff Topology MeasureTheory
open Set Metric Filter MeasureTheory

/-- **The seed arc with a prescribed germ extent.** -/
theorem germArcExtent {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M]
    {W : Set M} (hW : IsOpen W) {p : M} (hp : p ∈ W)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) (hpc : p ∈ c.source)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0)
    {ρpos ρneg : ℝ} (hρpos : 0 < ρpos) (hρneg : 0 < ρneg)
    (hray : ∀ t : ℝ, 0 ≤ t → t < ρpos → c p + t • v ∈ c.target)
    (hrayb : ∀ t : ℝ, -ρneg < t → t ≤ 0 → c p + t • v ∈ c.target)
    (hgerW : ∀ t : ℝ, 0 < t → t < min ρpos ρneg → c.symm (c p + t • v) ∈ W)
    {L : ℝ} (hL0 : 0 < L) (hLρ : L < min ρpos ρneg)
    {h : ℝ} (hLh : L < h) (hh1 : h < 1)
    {δ : ℝ} (hδ : 0 < δ) (hLδ : L < δ) :
    ∃ A : ℝ → M, ContMDiff MCreal (MC n) smoothOrder A ∧ A 0 = p ∧
      (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) A t)) ∧
      Set.InjOn A (Set.Icc (0:ℝ) 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → A t ∈ W) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
        A t ∈ c.symm '' (Metric.ball (c p) (min ρpos ρneg * ‖v‖) ∩ c.target)) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) L → A t = c.symm (c p + t • v)) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) L → c p + t • v ∈ c.target) ∧
      (∃ (w : EuclideanSpace ℝ (Fin n)) (ε : ℝ), w ≠ 0 ∧ 0 < ε ∧
        (∀ t : ℝ, 1 - ε ≤ t → t ≤ 1 → A t ∈ c.source ∧ c (A t) = c (A 1) + (t - 1) • w) ∧
        (∃ e' : ℝ, 0 < e' ∧ ∀ t : ℝ, 0 < t → t ≤ e' →
          c.symm (c (A 1) + t • w) ∈ W ∧ c (A 1) + t • w ∈ c.target)) := by
  have hc_s : ContMDiffOn (MC n) (MC n) smoothOrder c.symm c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hc
  have hcp : c p ∈ c.target := c.map_source hpc
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set ρv : ℝ := min ρpos ρneg with hρvdef
  have hρvpos : 0 < ρv := by rw [hρvdef]; exact lt_min hρpos hρneg
  have hLρv : L < ρv := by rw [hρvdef]; exact hLρ
  have hρvρpos : ρv ≤ ρpos := by rw [hρvdef]; exact min_le_left _ _
  have hρvρneg : ρv ≤ ρneg := by rw [hρvdef]; exact min_le_right _ _
  have hchart : ∀ t : ℝ, -ρv < t → t < ρv → c p + t • v ∈ c.target := by
    intro t h1 h2
    by_cases h0 : (0:ℝ) ≤ t
    · exact hray t h0 (lt_of_lt_of_le h2 hρvρpos)
    · push_neg at h0
      refine hrayb t ?_ h0.le
      linarith
  obtain ⟨φ, hφcd, hφmono, hφid, hφrange, hφ1, μ, hμ⟩ :=
    exists_smooth_reparam_gen (-ρv) ρv L h (by linarith) hL0 hLh hh1.le hLρv
  have hφstrict : StrictMono φ := strictMono_of_deriv_pos hφmono
  have hφ0 : φ 0 = 0 := hφid 0 (by constructor <;> linarith)
  have hμpos : 0 < μ := by
    have h1 : φ h = φ 1 + μ * (h - 1) := hμ h (by constructor <;> linarith)
    have h2 : φ h < φ 1 := hφstrict hh1
    have h3 : μ * (h - 1) < 0 := by linarith
    have h4 : h - 1 < 0 := by linarith
    by_contra hcon
    push_neg at hcon
    have h5 : 0 ≤ μ * (h - 1) := mul_nonneg_of_nonpos_of_nonpos hcon h4.le
    linarith
  set A : ℝ → M := fun t => c.symm (c p + (φ t) • v) with hAdef
  have hAval : ∀ t : ℝ, A t = c.symm (c p + (φ t) • v) := fun t => rfl
  have hAin : ∀ t : ℝ, c p + (φ t) • v ∈ c.target := by
    intro t
    have hrange := hφrange (Set.mem_range_self t)
    exact hchart (φ t) (by linarith [hrange.1]) (by linarith [hrange.2])
  refine ⟨A, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ContMDiff
    have hinner : ContMDiff MCreal (MC n) smoothOrder (fun t : ℝ => c p + (φ t) • v) := by
      rw [MCreal, MC, smoothOrder, contMDiff_iff_contDiff]
      fun_prop
    exact hc_s.comp_contMDiff hinner hAin
  · -- A 0 = p
    show c.symm (c p + (φ 0) • v) = p
    rw [hφ0, zero_smul, add_zero]
    exact c.left_inv hpc
  · -- immersion
    intro t
    have hφdiff : DifferentiableAt ℝ φ t :=
      (contMDiffAt_iff_contDiffAt.mp (contMDiff_iff_contDiff.mpr hφcd).contMDiffAt).differentiableAt
        (by simp [smoothOrder])
    have hderiv : deriv (fun s : ℝ => c p + (φ s) • v) t = (deriv φ t) • v := by
      rw [deriv_const_add, deriv_smul_const hφdiff]
    have h1 : Function.Injective (mfderiv (MC n) (MC n) c.symm (c p + (φ t) • v)) :=
      mfderiv_chart_symm_injective c (contMDiffOn_of_mem_maximalAtlas hc) hc_s (hAin t)
    have h2 : Function.Injective (mfderiv MCreal (MC n)
        (fun s : ℝ => c p + (φ s) • v) t) := by
      have h2' : Function.Injective (fderiv ℝ (fun s : ℝ => c p + (φ s) • v) t) := by
        intro a b hab
        have key : ∀ y : ℝ, (fderiv ℝ (fun s : ℝ => c p + (φ s) • v) t) y
            = y • deriv (fun s : ℝ => c p + (φ s) • v) t := fun y => fderiv_eq_smul_deriv y
        rw [key a, key b, hderiv] at hab
        have h2'' : (a - b) • (deriv φ t • v) = 0 := by rw [sub_smul, hab, sub_self]
        rcases smul_eq_zero.mp h2'' with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h (smul_ne_zero (ne_of_gt (hφmono t)) hv)
      simp only [mfderiv_eq_fderiv]
      exact h2'
    have hinmd : MDifferentiableAt MCreal (MC n) (fun s : ℝ => c p + (φ s) • v) t := by
      have hcd : ContMDiff MCreal (MC n) smoothOrder (fun s : ℝ => c p + (φ s) • v) := by
        rw [MCreal, MC, smoothOrder, contMDiff_iff_contDiff]
        fun_prop
      exact hcd.contMDiffAt.mdifferentiableAt (by simp [smoothOrder])
    have hcs_md : MDifferentiableAt (MC n) (MC n) c.symm (c p + (φ t) • v) :=
      (hc_s.contMDiffAt (c.open_target.mem_nhds (hAin t))).mdifferentiableAt
        (by simp [smoothOrder])
    have hchain : mfderiv MCreal (MC n) A t
        = (mfderiv (MC n) (MC n) c.symm (c p + (φ t) • v)).comp
          (mfderiv MCreal (MC n) (fun s : ℝ => c p + (φ s) • v) t) := by
      have hcomp := mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MC n)
        (f := fun s : ℝ => c p + (φ s) • v) (g := c.symm) t hcs_md hinmd
      rw [show A = c.symm ∘ (fun s : ℝ => c p + (φ s) • v) from rfl]
      exact hcomp
    rw [hchain]
    intro a b hab
    simp only [ContinuousLinearMap.comp_apply] at hab
    exact h2 (h1 hab)
  · -- injectivity on [0,1]
    intro s hs t ht hst
    rw [hAval s, hAval t] at hst
    have hinj : Set.InjOn c.symm c.target := by
      have h := c.symm.injOn
      rwa [OpenPartialHomeomorph.symm_source] at h
    have h2 := hinj (hAin s) (hAin t) hst
    have h3 : (φ s - φ t) • v = 0 := by rw [sub_smul, add_left_cancel h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact hφstrict.injective (sub_eq_zero.mp h)
    · exact absurd h hv
  · -- image in W
    intro t ht
    rw [hAval t]
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, hφ0, zero_smul, add_zero, c.left_inv hpc]; exact hp
    · exact hgerW (φ t) (by rw [← hφ0]; exact hφstrict h0)
        (lt_of_le_of_lt (hφstrict.monotone ht.2) hφ1.2)
  · -- the image is carried by the chart ball (intersected with the chart target)
    intro t ht
    have hφt := hφrange (Set.mem_range_self t)
    refine ⟨c p + (φ t) • v, ⟨?_, hchart _ hφt.1 hφt.2⟩, rfl⟩
    have hsmall : ‖(φ t) • v‖ < min ρpos ρneg * ‖v‖ := by
      have h2 : ‖(φ t) • v‖ = |φ t| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
      rw [h2, show min ρpos ρneg * ‖v‖ = ρv * ‖v‖ from by rw [hρvdef]]
      exact mul_lt_mul_of_pos_right (abs_lt.mpr hφt) hvnorm
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : c p + (φ t) • v - c p = (φ t) • v := by abel
    rwa [h1]
  · -- germ on [0,L]
    intro t ht
    rw [hAval t, hφid t ht]
  · -- the germ chart points lie in the chart target (the state's `hintgt`)
    intro t ht
    exact hchart t (by linarith [ht.1, hρvpos]) (by linarith [ht.2, hLρv])
  · -- terminal clause, with the *forward ray* at its head
    refine ⟨μ • v, 1 - h, smul_ne_zero hμpos.ne' hv, by linarith, ?_, ?_⟩
    · intro t ht1 ht2
      have h1 : φ t = φ 1 + μ * (t - 1) := hμ t (by constructor <;> linarith)
      have hcA1 : c (A 1) = c p + (φ 1) • v := by
        rw [hAval 1]; exact c.right_inv (hAin 1)
      constructor
      · rw [hAval t]; exact c.map_target (hAin t)
      · rw [hAval t, c.right_inv (hAin t), hcA1, h1]
        module
    · -- the straight continuation of the germ line beyond `A 1`
      refine ⟨(ρv - φ 1) / (2 * μ), div_pos (by linarith [hφ1.2]) (by positivity), ?_⟩
      intro t ht0 ht1
      have hs_lt : φ 1 + t * μ < ρv := by
        have h2 : t * μ ≤ ((ρv - φ 1) / (2 * μ)) * μ :=
          mul_le_mul_of_nonneg_right ht1 hμpos.le
        have h3 : ((ρv - φ 1) / (2 * μ)) * μ = (ρv - φ 1) / 2 := by
          field_simp
        linarith [h2, h3, hφ1.2]
      have hs_pos : 0 < φ 1 + t * μ := by nlinarith [hφ1.1, hμpos, ht0]
      have hcA1 : c (A 1) = c p + (φ 1) • v := by
        rw [hAval 1]; exact c.right_inv (hAin 1)
      have harg : c (A 1) + t • (μ • v) = c p + (φ 1 + t * μ) • v := by
        rw [hcA1, smul_smul, add_smul]
        module
      constructor
      · rw [harg]
        exact hgerW (φ 1 + t * μ) hs_pos
          (lt_min (by linarith [hρvρpos]) (by linarith [hρvρneg]))
      · rw [harg]
        exact hchart (φ 1 + t * μ) (by linarith [hs_pos, hρvpos]) hs_lt

end Work.Noncompact.CompressionTube
