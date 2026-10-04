import Mathlib
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.MP.hessAt_nonpos_of_isLocalMax
import Submission.Work.Diff.MP.Defs
import Submission.Work.Diff.GE.contMDiff_rmP_fields
import Submission.Work.Diff.MP.frobDot_rot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for the local orthonormal-frame model

Vocabulary used by `Work.Diff.MP.local_model`: the real-valued smoothness wrapper `SmFun`, the
functional `frobDotCLM L = (X ↦ frobDot L X)` (needed to feed the frozen `LapRmFrameParallel`
contract, which is stated for continuous linear functionals), the `O(n)`-invariance of `frobNorm`,
and the second-derivative test `laplAt ≤ 0` at a local maximum.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.MP.LM

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The real-valued version of `CMDiff ∞`. -/
abbrev SmFun (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (u : M → ℝ) : Prop := CMDiff ∞ u

variable {n : ℕ}

/-- `frobDot L` as a continuous linear functional. -/
noncomputable def frobDotCLM (L : Curv4 n) : Curv4 n →L[ℝ] ℝ where
  toLinearMap :=
    { toFun := fun X => frobDot L X
      map_add' := fun X Y => frobDot_add_right L X Y
      map_smul' := fun c X => by rw [frobDot_smul_right]; rfl }
  cont := by
    simp only [frobDot]
    fun_prop

theorem frobDotCLM_apply (L X : Curv4 n) : frobDotCLM L X = frobDot L X := rfl

/-- `rot A` preserves the Frobenius norm for `A ∈ O(n)`. -/
theorem frobNorm_rot (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Curv4 n) : frobNorm (rot A R) = frobNorm R := by
  rw [frobNorm, frobNorm, frobDot_rot n A hA R R]

/-- The bilinear-form bundle version of `frobBall`-membership is unchanged by `rot A`. -/
theorem mem_frobBall_rot (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    {ρ : ℝ} {R : Curv4 n} : rot A R ∈ frobBall ρ ↔ R ∈ frobBall ρ := by
  rw [frobBall_mem, frobBall_mem, frobNorm_rot A hA R]

/-- The Laplacian of a smooth function at a local maximum is `≤ 0`. -/
theorem laplAt_nonpos_of_isLocalMax [I.Boundaryless] [T2Space M]
    (g : SMet I M) (u : M → ℝ) (hu : CMDiff ∞ u) (x : M)
    (hmax : ∀ᶠ y in 𝓝 x, u y ≤ u x) : laplAt g u x ≤ 0 := by
  rw [laplAt]
  exact Finset.sum_nonpos fun i _ => hessAt_nonpos_of_isLocalMax g u hu x hmax _

/-- The curvature array of a smooth frame field is a smooth function of the point. -/
theorem contMDiff_rmFrame_field [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M) (g : SMet I M)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmField I M (Ef i)) :
    ContMDiff I 𝓘(ℝ, Curv4 (Module.finrank ℝ E)) ∞ (fun y : M => rmFrame g y (fun i => Ef i y)) := by
  rw [contMDiff_pi_space]
  intro i
  rw [contMDiff_pi_space]
  intro j
  rw [contMDiff_pi_space]
  intro k
  rw [contMDiff_pi_space]
  intro l
  exact Work.Diff.GE.contMDiff_rmP_fields (I := I) (M := M) hLC g (hEf i) (hEf j) (hEf k) (hEf l)

/-- For a continuous linear functional `ℓ`, the function `y ↦ ℓ (Rm(y))` of a smooth frame field is
smooth. -/
theorem contMDiff_ell_rmFrame [I.Boundaryless] [T2Space M] (hLC : LCSmooth I M) (g : SMet I M)
    (ℓ : Curv4 (Module.finrank ℝ E) →L[ℝ] ℝ)
    (Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y)
    (hEf : ∀ i, SmField I M (Ef i)) :
    SmFun I M (fun y : M => ℓ (rmFrame g y (fun i => Ef i y))) :=
  (ℓ.contMDiff).comp (contMDiff_rmFrame_field hLC g Ef hEf)

/-! ## Uniformity in the spatial variable on a compact set

Two ingredients for the uniform first-order expansion of a family `s ↦ F s y` whose derivative
`dF s y` is continuous on a compact box: a tube-lemma form of "the derivative is uniformly close to
its value at `t` for `s` near `t`", and the mean-value-theorem step. -/

/-- **Tube lemma, interval form.** If `f` is continuous on `Icc t (t+δ) ×ˢ K` with `K` compact and
`f t y ∈ W` for all `y ∈ K` (`W` open), then `f s y ∈ W` for all `s ∈ Icc t (t+δ)` close to `t` and
all `y ∈ K`. -/
theorem exists_pos_forall_mem_of_isCompact {X : Type*} [TopologicalSpace X] {Y : Type*}
    [TopologicalSpace Y] {W : Set Y} (hW : IsOpen W) {K : Set X} (hK : IsCompact K) {t δ : ℝ}
    (hδ : 0 < δ) {f : ℝ → X → Y}
    (hf : ContinuousOn (fun p : ℝ × X => f p.1 p.2) (Set.Icc t (t + δ) ×ˢ K))
    (h0 : ∀ y ∈ K, f t y ∈ W) :
    ∃ η : ℝ, 0 < η ∧ ∀ s ∈ Set.Icc t (t + δ), |s - t| ≤ η → ∀ y ∈ K, f s y ∈ W := by
  let g : ℝ × X → Y := fun p => f p.1 p.2
  let S : Set (ℝ × X) := Set.Icc t (t + δ) ×ˢ K
  have hfS : ContinuousOn g S := hf
  have hn : g ⁻¹' W ∈ 𝓝ˢ[S] ({t} ×ˢ K) := by
    rw [mem_nhdsSetWithin]
    obtain ⟨u, hu_open, hu_eq⟩ := continuousOn_iff'.1 hfS W hW
    refine ⟨u, hu_open, ?_, ?_⟩
    · intro p hp
      obtain ⟨hp1, hp2⟩ := hp
      have hp1' : p.1 = t := hp1
      have hpp : p = (t, p.2) := by ext <;> simp [hp1']
      have hgp : g p ∈ W := by rw [hpp]; exact h0 p.2 hp2
      have hpS : p ∈ S := ⟨by rw [hp1']; exact ⟨le_rfl, by linarith⟩, hp2⟩
      have hmem : p ∈ g ⁻¹' W ∩ S := ⟨hgp, hpS⟩
      rw [hu_eq] at hmem
      exact hmem.1
    · intro p hp
      have hp' : p ∈ g ⁻¹' W ∩ S := by rw [hu_eq]; exact hp
      exact hp'.1
  obtain ⟨u, hu_mem, v, hv_mem, huv⟩ :=
    generalized_tube_lemma' (s := ({t} : Set ℝ)) (s' := Set.Icc t (t + δ)) (t := K) (t' := K)
      (n := g ⁻¹' W) isCompact_singleton hK hn
  have hu_mem' : u ∈ 𝓝[Set.Icc t (t + δ)] t := by
    rwa [nhdsSetWithin_singleton] at hu_mem
  rw [nhdsWithin] at hu_mem'
  obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_inf_iff_superset.mp hu_mem'
  have hBs : Set.Icc t (t + δ) ⊆ B := Filter.mem_principal.mp hB
  obtain ⟨l, r, htIoo, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp hA
  have hv : K ⊆ v := by rw [nhdsSetWithin_self] at hv_mem; exact hv_mem
  refine ⟨min (t - l) (r - t) / 2, ?_, ?_⟩
  · refine div_pos (lt_min ?_ ?_) (by norm_num)
    · linarith [htIoo.1]
    · linarith [htIoo.2]
  · intro s hs hst y hy
    have h1 : min (t - l) (r - t) ≤ t - l := min_le_left _ _
    have h2 : min (t - l) (r - t) ≤ r - t := min_le_right _ _
    have hsO : s ∈ Set.Ioo l r := by
      constructor
      · have habs : |s - t| ≤ (t - l) / 2 := le_trans hst (by linarith)
        have := (abs_le.mp habs).1
        linarith [this, htIoo.1]
      · have habs : |s - t| ≤ (r - t) / 2 := le_trans hst (by linarith)
        have := (abs_le.mp habs).2
        linarith [this, htIoo.2]
    exact huv (show (s, y) ∈ u ×ˢ v from ⟨hAB ⟨hIoo hsO, hBs hs⟩, hv hy⟩)

/-- On a compact box, a function continuous in the pair `(s,y)` with values in a normed space is
uniformly close, for `s` near `t`, to its value at `(t,y)`, with the same modulus for all `y ∈ K`. -/
theorem LM_uniform_slice
    {ι : Type*} [TopologicalSpace ι] {K : Set ι} (hK : IsCompact K)
    {E : Type*} [NormedAddCommGroup E]
    (dF : ℝ → ι → E) {t δ : ℝ} (hδ : 0 ≤ δ)
    (hdF : ContinuousOn (fun p : ℝ × ι => dF p.1 p.2) (Set.prod (Set.Icc t (t + δ)) K)) :
    ∀ ε > 0, ∃ η > 0, ∀ y ∈ K, ∀ s ∈ Set.Icc t (t + δ), |s - t| < η →
      ‖dF s y - dF t y‖ ≤ ε := by
  intro ε hε
  rcases eq_or_lt_of_le hδ with hδ0 | hδpos
  · refine ⟨1, one_pos, fun y hy s hs hst => ?_⟩
    have hs_eq : s = t := le_antisymm (by rw [← hδ0] at hs; simpa using hs.2) hs.1
    rw [hs_eq, sub_self, norm_zero]
    exact hε.le
  · have hslice : ContinuousOn (fun y : ι => dF t y) K :=
      hdF.comp' ((continuous_const.prodMk continuous_id).continuousOn)
        (fun y hy => ⟨⟨le_rfl, by linarith⟩, hy⟩)
    have h2 : ContinuousOn (fun p : ℝ × ι => dF t p.2) (Set.prod (Set.Icc t (t + δ)) K) :=
      hslice.comp' continuous_snd.continuousOn (fun p hp => hp.2)
    have hf : ContinuousOn (fun p : ℝ × ι => dF p.1 p.2 - dF t p.2)
        (Set.prod (Set.Icc t (t + δ)) K) := hdF.sub h2
    have h0 : ∀ y ∈ K, dF t y - dF t y ∈ Metric.ball (0 : E) ε := by
      intro y hy
      simp only [Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]
      exact hε
    obtain ⟨η, hηpos, hη⟩ := exists_pos_forall_mem_of_isCompact (f := fun s y => dF s y - dF t y)
      (Metric.isOpen_ball (x := (0:E))) hK hδpos hf h0
    refine ⟨η, hηpos, fun y hy s hs hst => ?_⟩
    have h := hη s hs (le_of_lt hst) y hy
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at h
    exact le_of_lt h

/-- **Uniform first-order expansion in time.** From a two-sided derivative at each `s ∈ [t, t+δ)`
and a uniform-in-`K` modulus of continuity of the derivative at `t`, the one-step expansion holds
uniformly on `K`. -/
theorem LM_uniform_expansion
    {ι : Type*} [TopologicalSpace ι] {K : Set ι} (hK : IsCompact K)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F dF : ℝ → ι → E) {t δ : ℝ} (hδ : 0 < δ)
    (hderiv : ∀ y ∈ K, ∀ s ∈ Set.Ico t (t + δ),
      HasDerivAt (fun s' : ℝ => F s' y) (dF s y) s)
    (hdF : ∀ ε > 0, ∃ η > 0, ∀ y ∈ K, ∀ s ∈ Set.Icc t (t + δ),
      |s - t| < η → ‖dF s y - dF t y‖ ≤ ε) :
    ∀ ε > 0, ∃ δ' > 0, δ' ≤ δ ∧ ∀ h : ℝ, 0 < h → h ≤ δ' → ∀ y ∈ K,
      ‖F (t + h) y - (F t y + h • dF t y)‖ ≤ ε * h := by
  intro ε hε
  obtain ⟨η, hηpos, hη⟩ := hdF ε hε
  refine ⟨min (η / 2) (δ / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
  · exact le_trans (min_le_right _ _) (by linarith)
  · intro h hh hh' y hy
    have hhδ : h ≤ δ / 2 := le_trans hh' (min_le_right _ _)
    have hhη : h ≤ η / 2 := le_trans hh' (min_le_left _ _)
    have hlin : ∀ x : ℝ, HasDerivAt (fun s' : ℝ => (s' - t) • dF t y) (dF t y) x := by
      intro x
      have h1 : HasDerivAt (fun s' : ℝ => s' - t) (1 : ℝ) x := by
        simpa only [id_eq] using (hasDerivAt_id x).sub_const t
      simpa only [one_smul] using h1.smul_const (dF t y)
    have hgc : ∀ x ∈ Set.Icc t (t + h),
        HasDerivWithinAt (fun s' : ℝ => (F s' y - F t y) - (s' - t) • dF t y)
          (dF x y - dF t y) (Set.Icc t (t + h)) x := by
      intro x hx
      have hx' : x ∈ Set.Ico t (t + δ) := ⟨hx.1, by linarith [hx.2]⟩
      have hc : HasDerivAt (fun s' : ℝ => F s' y - F t y) (dF x y) x :=
        (hderiv y hy x hx').sub_const (F t y)
      exact ((hc.sub (hlin x)).hasDerivWithinAt)
    have hbound : ∀ x ∈ Set.Ico t (t + h), ‖dF x y - dF t y‖ ≤ ε := by
      intro x hx
      have hxI : x ∈ Set.Icc t (t + δ) := ⟨hx.1, by linarith [hx.2]⟩
      exact hη y hy x hxI (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])
    have hMVT := norm_image_sub_le_of_norm_deriv_le_segment' (a := t) (b := t + h)
      (f := fun s : ℝ => (F s y - F t y) - (s - t) • dF t y)
      (f' := fun x : ℝ => dF x y - dF t y) (C := ε) hgc hbound
      (t + h) ⟨le_add_of_nonneg_right hh.le, le_rfl⟩
    have hth : t + h - t = h := by ring
    simp only [hth, sub_self, zero_smul, sub_zero, sub_sub] at hMVT
    exact hMVT

end Work.Diff.MP.LM
