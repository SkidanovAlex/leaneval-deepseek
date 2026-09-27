import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Whitney.radial_bump_deriv_half
import Submission.Work.Whitney.PathTools.arc_nonseparates_open_surface
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_arc
import Submission.Work.Whitney.SmoothArc.ManifoldBump
import Submission.Work.Whitney.SmoothArc.Bump

/-!
# An immersed arc with a prescribed germ

`Work.Noncompact.CompressionTube.immersedArcWithGerm`: in a smooth `n`-manifold `M` (`2 ≤ n`),
for an open preconnected set `W`, two distinct points `p, q ∈ W`, a chart `c` at `p` and a
direction `v ≠ 0` whose short forward germ lies in `W`, there is a smooth immersed curve
`α : ℝ → M` which is injective on `[0,1]`, runs from `p` to `q` inside `W`, agrees with the
prescribed chart line `t ↦ c.symm (c p + t • v)` near `0`, and ends with a straight germ in a
chart at `q`.

The proof follows the reachability scheme of `Work.Whitney.exists_smooth_arc_of_isPreconnected`:
the set `Ŝ` of endpoints reachable by an arc carrying the prescribed initial germ is shown to be
open and closed inside the open preconnected set `W` with the initial germ arc removed, so that
`Ŝ = W \ germ`.  The endpoint is moved by the bump translations of `SmoothArc.Bump` (which are
immersions, hence preserve the immersion property), and the base point of `Ŝ` is an explicit
reparametrisation of the germ.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff Topology MeasureTheory
open Set Metric Filter MeasureTheory

/-- **Removing an injective arc from an open preconnected set** in an `n`-manifold, `n ≥ 2`,
leaves it preconnected.  (Copy of `Work.Noncompact.CompressionTube.isPreconnected_sdiff_arc_of_open`
from `exists_canals_aux.lean`, reproduced here to avoid importing that module.) -/
theorem sdiff_arc_isPreconnected {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (hn : 2 ≤ n) {U : Set M} (hUo : IsOpen U) (hUp : IsPreconnected U) {γ : ℝ → M}
    (hγc : Continuous γ) (hγinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    (hγU : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ U) :
    IsPreconnected (U \ γ '' Set.Icc (0:ℝ) 1) := by
  haveI : LocallyPathConnectedSpace M :=
    Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
  rcases eq_or_lt_of_le hn with h2 | h3
  · subst h2
    exact (Work.Whitney.PathTools.arc_nonseparates_open_surface hUo hUp hγc hγinj hγU).isConnected.2
  · have hpath : IsPathConnected U :=
      hUo.isConnected_iff_isPathConnected.mp ⟨⟨γ 0, hγU 0 (by norm_num)⟩, hUp⟩
    have h := Work.Whitney.PathTools.isPathConnected_sdiff_arc h3 hUo hpath hγc hγinj hγU
      (∅ : Set M) Set.finite_empty (by simp) (by simp)
    simpa using h.isConnected.2

/-- Injectivity of the derivative of `s ↦ s • V` (`V ≠ 0`). -/
lemma smulRight_one_injective {n : ℕ} {V : EuclideanSpace ℝ (Fin n)} (hV : V ≠ 0) :
    Function.Injective ((1 : ℝ →L[ℝ] ℝ).smulRight V) := by
  intro a b hab
  have hab' : a • V = b • V := by simpa using hab
  have h2 : (a - b) • V = 0 := by rw [sub_smul, hab', sub_self]
  rcases smul_eq_zero.mp h2 with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hV

/-- The manifold derivative of a chart `c : M → E` (with smooth inverse) is injective. -/
theorem mfderiv_chart_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c c.source)
    (hcs : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm c.target)
    {y : M} (hy : y ∈ c.source) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (c : M → EuclideanSpace ℝ (Fin n)) y) := by
  let Φ : PartialDiffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M (EuclideanSpace ℝ (Fin n))
      ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := hc
      contMDiffOn_invFun := hcs }
  have hld : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (c : M → EuclideanSpace ℝ (Fin n)) y :=
    PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ hy
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  rw [← IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hld hn]
  exact (hld.mfderivToContinuousLinearEquiv hn).injective

/-- The manifold derivative of the inverse of a chart `c : M → E` (with smooth inverse) is
injective. -/
theorem mfderiv_chart_symm_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c c.source)
    (hcs : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm c.target)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ c.target) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c.symm y) := by
  let Φ : PartialDiffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (EuclideanSpace ℝ (Fin n)) M
      ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    { toPartialEquiv := c.symm.toPartialEquiv
      open_source := c.open_target
      open_target := c.open_source
      contMDiffOn_toFun := hcs
      contMDiffOn_invFun := hc }
  have hld : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      c.symm y := PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ hy
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  rw [← IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hld hn]
  exact (hld.mfderivToContinuousLinearEquiv hn).injective

/-- **The bump translation in `ℝⁿ`, with injective derivative.**  This is
`Work.Whitney.exists_bumpTranslation` (from `Submission/Work/Whitney/SmoothArc/Bump.lean`)
with the additional conclusion that the derivative of `Ψ` is injective everywhere. -/
theorem bumpTranslation_imm {n : ℕ} :
    ∃ κ > 0, ∀ (u : EuclideanSpace ℝ (Fin n)) (σ : ℝ), 0 < σ →
      ∀ d : EuclideanSpace ℝ (Fin n), ‖d‖ < κ * σ →
      ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        ContDiff ℝ ∞ Ψ ∧ Function.Injective Ψ ∧ Ψ u = u + d ∧
        (∀ v, σ/2 ≤ dist v u → Ψ v = v) ∧
        (∀ v, dist v u < σ → dist (Ψ v) u < σ) ∧
        (∀ v, Function.Injective (fderiv ℝ Ψ v)) ∧
        (∀ v, dist v u ≤ σ/4 → Ψ v = v + d) := by
  classical
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  have hbC : ContDiff ℝ ((1 : ℕ∞) : WithTop ℕ∞)
      (fun v : EuclideanSpace ℝ (Fin n) => b v) := b.contDiff (n := 1)
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ)
      (n := ((1 : ℕ∞) : WithTop ℕ∞)) (f := fun v : EuclideanSpace ℝ (Fin n) => b v)
      b.hasCompactSupport hbC (by simp)
  have hCnn : (0:ℝ) ≤ C := NNReal.coe_nonneg C
  have hCpos : (0:ℝ) < 4*((C:ℝ)+1) := by linarith
  refine ⟨1/(4*((C:ℝ)+1)), by positivity, ?_⟩
  intro u σ hσ d hd
  have hκ4 : 1/(4*((C:ℝ)+1)) ≤ 1/4 := by
    rw [div_le_div_iff₀ hCpos (by norm_num : (0:ℝ) < 4)]
    nlinarith
  have hd4 : ‖d‖ < σ/4 := by
    calc ‖d‖ < (1/(4*((C:ℝ)+1))) * σ := hd
      _ ≤ (1/4) * σ := mul_le_mul_of_nonneg_right hκ4 hσ.le
      _ = σ/4 := by ring
  have hdC : (C:ℝ) * ‖d‖ < σ := by
    have h2 : (C:ℝ) * (1/(4*((C:ℝ)+1))) ≤ 1/4 := by
      rw [mul_one_div, div_le_div_iff₀ hCpos (by norm_num : (0:ℝ) < 4)]
      nlinarith
    rcases lt_or_eq_of_le hCnn with hCpos | hC0
    · calc (C:ℝ) * ‖d‖ < (C:ℝ) * ((1/(4*((C:ℝ)+1))) * σ) :=
            mul_lt_mul_of_pos_left hd hCpos
        _ = ((C:ℝ) * (1/(4*((C:ℝ)+1)))) * σ := by ring
        _ ≤ (1/4) * σ := mul_le_mul_of_nonneg_right h2 hσ.le
        _ < σ := by linarith
    · rw [← hC0]; simp [hσ]
  refine ⟨fun v => v + b ((σ⁻¹ : ℝ) • (v - u)) • d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hinner : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => (σ⁻¹:ℝ) • (v - u)) := by
      fun_prop
    have hbm : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin n) => b ((σ⁻¹:ℝ) • (v - u))) :=
      (b.contDiff (n := ⊤)).comp hinner
    exact contDiff_id.add (hbm.smul_const d)
  · intro v w hvw
    have hvw' : v + b ((σ⁻¹:ℝ) • (v - u)) • d = w + b ((σ⁻¹:ℝ) • (w - u)) • d := hvw
    have hkey : v - w = (b ((σ⁻¹:ℝ) • (w - u)) - b ((σ⁻¹:ℝ) • (v - u))) • d := by
      calc v - w = (v + b ((σ⁻¹:ℝ) • (v-u)) • d) - (w + b ((σ⁻¹:ℝ) • (w-u)) • d)
            + (b ((σ⁻¹:ℝ) • (w-u)) • d - b ((σ⁻¹:ℝ) • (v-u)) • d) := by abel
        _ = 0 + (b ((σ⁻¹:ℝ) • (w-u)) • d - b ((σ⁻¹:ℝ) • (v-u)) • d) := by rw [hvw']; abel
        _ = (b ((σ⁻¹:ℝ) • (w-u)) - b ((σ⁻¹:ℝ) • (v-u))) • d := by rw [sub_smul]; abel
    have hdiff : ‖(σ⁻¹:ℝ) • (w - u) - σ⁻¹ • (v - u)‖ = ‖w - v‖ / σ := by
      rw [← smul_sub, show w - u - (v - u) = w - v from by abel, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ σ⁻¹), inv_mul_eq_div]
    have hlip : |b ((σ⁻¹:ℝ) • (w - u)) - b ((σ⁻¹:ℝ) • (v - u))| ≤ ((C:ℝ)/σ) * ‖w - v‖ := by
      have h := hC.dist_le_mul ((σ⁻¹:ℝ) • (w - u)) ((σ⁻¹:ℝ) • (v - u))
      rw [Real.dist_eq, dist_eq_norm, hdiff] at h
      calc |b ((σ⁻¹:ℝ) • (w-u)) - b ((σ⁻¹:ℝ) • (v-u))| ≤ (C:ℝ) * (‖w-v‖/σ) := h
        _ = ((C:ℝ)/σ) * ‖w - v‖ := by ring
    have hnorm : ‖v - w‖ =
        |b ((σ⁻¹:ℝ) • (w - u)) - b ((σ⁻¹:ℝ) • (v - u))| * ‖d‖ := by
      rw [hkey, norm_smul, Real.norm_eq_abs]
    have hle : ‖v - w‖ ≤ ((C:ℝ)/σ) * ‖d‖ * ‖v - w‖ := by
      nth_rewrite 1 [hnorm]
      have hwv : ‖w - v‖ = ‖v - w‖ := norm_sub_rev w v
      calc |b ((σ⁻¹:ℝ) • (w-u)) - b ((σ⁻¹:ℝ) • (v-u))| * ‖d‖
            ≤ (((C:ℝ)/σ) * ‖w - v‖) * ‖d‖ :=
              mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
        _ = ((C:ℝ)/σ) * ‖d‖ * ‖v - w‖ := by rw [hwv]; ring
    have h1 : ((C:ℝ)/σ) * ‖d‖ < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hσ]
      exact hdC
    have hnn : 0 ≤ ‖v - w‖ := norm_nonneg _
    have hzero : ‖v - w‖ = 0 := by nlinarith [hle, h1, hnn]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  · have hu : b ((σ⁻¹:ℝ) • (u - u)) = 1 := by
      have : (σ⁻¹:ℝ) • (u - u) = 0 := by simp
      rw [this]
      exact b.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_self]; exact b.rIn_pos.le)
    show u + b ((σ⁻¹:ℝ) • (u - u)) • d = u + d
    rw [hu, one_smul]
  · intro v hv
    have hge : (1:ℝ)/2 ≤ ‖(σ⁻¹:ℝ) • (v - u)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ σ⁻¹),
        inv_mul_eq_div, le_div_iff₀ hσ]
      rw [dist_eq_norm] at hv
      linarith
    have hb0 : b ((σ⁻¹:ℝ) • (v - u)) = 0 := by
      apply b.zero_of_le_dist
      rw [show b.rOut = (1:ℝ)/2 from rfl]
      rw [dist_zero_right]
      exact hge
    simp [hb0]
  · intro v hv
    by_cases h : dist v u < σ/2
    · have hbv : ‖b ((σ⁻¹:ℝ) • (v - u))‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg b.nonneg]; exact b.le_one
      have h1 : dist (v + b ((σ⁻¹:ℝ) • (v - u)) • d) u ≤
          dist v u + ‖b ((σ⁻¹:ℝ) • (v - u))‖ * ‖d‖ := by
        rw [dist_eq_norm]
        have h2 : v + b ((σ⁻¹:ℝ) • (v - u)) • d - u =
            (v - u) + b ((σ⁻¹:ℝ) • (v - u)) • d := by abel
        rw [h2]
        calc ‖(v - u) + b ((σ⁻¹:ℝ) • (v-u)) • d‖ ≤ ‖v - u‖ + ‖b ((σ⁻¹:ℝ) • (v-u)) • d‖ :=
              norm_add_le _ _
          _ = ‖v - u‖ + ‖b ((σ⁻¹:ℝ) • (v-u))‖ * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ = dist v u + ‖b ((σ⁻¹:ℝ) • (v-u))‖ * ‖d‖ := by rw [dist_eq_norm]
      have h2 : ‖b ((σ⁻¹:ℝ) • (v - u))‖ * ‖d‖ ≤ 1 * (σ/4) :=
        mul_le_mul hbv hd4.le (norm_nonneg _) (by norm_num)
      linarith
    · push Not at h
      have hb0 : b ((σ⁻¹:ℝ) • (v - u)) = 0 := by
        apply b.zero_of_le_dist
        rw [show b.rOut = (1:ℝ)/2 from rfl]
        rw [dist_zero_right]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ σ⁻¹),
          inv_mul_eq_div, le_div_iff₀ hσ]
        rw [dist_eq_norm] at h
        linarith
      simpa [hb0] using hv
  · intro v
    set c₁ : EuclideanSpace ℝ (Fin n) → ℝ := fun w => b ((σ⁻¹ : ℝ) • (w - u)) with hc₁def
    set θ : NNReal := ⟨(C : ℝ) * σ⁻¹ * ‖d‖, by positivity⟩ with hθdef
    have hθcoe : (θ : ℝ) = (C : ℝ) * σ⁻¹ * ‖d‖ := by rw [hθdef]; rfl
    have hc₁diff : DifferentiableAt ℝ c₁ v := by
      rw [hc₁def]
      exact ((b.contDiff (n := ⊤)).differentiable (by simp)).differentiableAt.comp v
        (((differentiableAt_id (x := v)).sub_const u).const_smul (σ⁻¹ : ℝ))
    have hT_lip : LipschitzWith θ (fun w : EuclideanSpace ℝ (Fin n) => c₁ w • d) := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      rw [hc₁def]
      dsimp only
      rw [dist_eq_norm, dist_eq_norm]
      have hdiff : ‖(σ⁻¹ : ℝ) • (x - u) - σ⁻¹ • (y - u)‖ = ‖x - y‖ / σ := by
        rw [← smul_sub, show x - u - (y - u) = x - y from by abel, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ σ⁻¹), inv_mul_eq_div]
      have hlip : |b ((σ⁻¹ : ℝ) • (x - u)) - b ((σ⁻¹ : ℝ) • (y - u))|
          ≤ ((C : ℝ)/σ) * ‖x - y‖ := by
        have h := hC.dist_le_mul ((σ⁻¹ : ℝ) • (x - u)) ((σ⁻¹ : ℝ) • (y - u))
        rw [Real.dist_eq, dist_eq_norm, hdiff] at h
        calc |b ((σ⁻¹ : ℝ) • (x - u)) - b ((σ⁻¹ : ℝ) • (y - u))| ≤ (C : ℝ) * (‖x - y‖/σ) := h
          _ = ((C : ℝ)/σ) * ‖x - y‖ := by ring
      calc ‖b ((σ⁻¹ : ℝ) • (x - u)) • d - b ((σ⁻¹ : ℝ) • (y - u)) • d‖
          = ‖(b ((σ⁻¹ : ℝ) • (x - u)) - b ((σ⁻¹ : ℝ) • (y - u))) • d‖ := by rw [sub_smul]
        _ = |b ((σ⁻¹ : ℝ) • (x - u)) - b ((σ⁻¹ : ℝ) • (y - u))| * ‖d‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ (((C : ℝ)/σ) * ‖x - y‖) * ‖d‖ := mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
        _ = θ * dist x y := by
            rw [hθcoe, dist_eq_norm]
            ring
    have hθ1 : (θ : ℝ) < 1 := by
      rw [hθcoe]
      have hσinv : σ⁻¹ * ‖d‖ < 1/(4*((C:ℝ)+1)) := by
        rw [inv_mul_eq_div, div_lt_iff₀ hσ]
        exact hd
      calc (C : ℝ) * σ⁻¹ * ‖d‖ = (C : ℝ) * (σ⁻¹ * ‖d‖) := by ring
        _ ≤ (C : ℝ) * (1/(4*((C:ℝ)+1))) := mul_le_mul_of_nonneg_left hσinv.le hCnn
        _ < 1 := by
            have h2 : (C:ℝ) < 4*((C:ℝ)+1) := by linarith only [hCnn]
            have h3 : (0:ℝ) < 1/(4*((C:ℝ)+1)) := div_pos one_pos hCpos
            calc (C:ℝ) * (1/(4*((C:ℝ)+1))) < (4*((C:ℝ)+1)) * (1/(4*((C:ℝ)+1))) :=
                  mul_lt_mul_of_pos_right h2 h3
              _ = 1 := by field_simp
    have hΨ_deriv : fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) => w + c₁ w • d) v
        = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))
          + fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) => c₁ w • d) v := by
      change fderiv ℝ (id + fun y : EuclideanSpace ℝ (Fin n) => c₁ y • d) v = _
      rw [fderiv_add differentiableAt_id (hc₁diff.smul_const d), fderiv_id]
    intro a b' hab
    have h0 : (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) => w + c₁ w • d) v) (a - b') = 0 := by
      rw [map_sub, hab, sub_self]
    rw [hΨ_deriv, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply] at h0
    have hkey : a - b' = -(fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) => c₁ w • d) v) (a - b') := by
      rw [eq_neg_iff_add_eq_zero]; exact h0
    have hL : ‖fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) => c₁ w • d) v‖ ≤ (θ : ℝ) :=
      norm_fderiv_le_of_lipschitz (𝕜 := ℝ)
        (f := fun w : EuclideanSpace ℝ (Fin n) => c₁ w • d) (x₀ := v) hT_lip
    have hle : ‖a - b'‖ ≤ (θ : ℝ) * ‖a - b'‖ := by
      have h1 : ‖a - b'‖ = ‖(fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) => c₁ w • d) v) (a - b')‖ := by
        conv_lhs => rw [hkey]
        rw [norm_neg]
      calc ‖a - b'‖ = ‖(fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) => c₁ w • d) v) (a - b')‖ := h1
        _ ≤ ‖fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) => c₁ w • d) v‖ * ‖a - b'‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (θ : ℝ) * ‖a - b'‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    have hz : ‖a - b'‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖a - b'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      nlinarith [hle, hθ1, hpos]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro v hv
    have h1 : b ((σ⁻¹ : ℝ) • (v - u)) = 1 := by
      apply b.one_of_mem_closedBall
      have hv' : ‖v - u‖ ≤ σ/4 := by rw [← dist_eq_norm]; exact hv
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ σ⁻¹), show b.rIn = (1:ℝ)/4 from rfl,
        inv_mul_eq_div, div_le_iff₀ hσ]
      linarith
    show v + b ((σ⁻¹ : ℝ) • (v - u)) • d = v + d
    rw [h1, one_smul]

/-- **The bump translation on a manifold, with injective manifold derivative.**  This is
`Work.Whitney.exists_contMDiff_injective_bump` with the additional conclusion that `ψ` is an
immersion. -/
theorem exists_bump_imm {n : ℕ} :
    ∃ ε > 0, ∀ {M : Type*} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M] [T2Space M]
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ c c.source →
      ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ c.symm c.target →
      ∀ (y : M), y ∈ c.source → ∀ (R : ℝ), 0 < R →
      Metric.closedBall (c y) R ⊆ c.target →
      ∀ z : M, z ∈ c.source → ‖c z - c y‖ < ε * R →
      ∃ ψ : M → M,
        ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ ψ ∧
        Function.Injective ψ ∧
        (∀ w : M, w ∉ c.symm '' Metric.ball (c y) R → ψ w = w) ∧
        ψ y = z ∧
        ψ '' (c.symm '' Metric.ball (c y) R) ⊆ c.symm '' Metric.ball (c y) R ∧
        (∀ w : M, Function.Injective (mfderiv
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ψ w)) ∧
        (∀ x ∈ c.source, dist (c x) (c y) ≤ R/4 → c (ψ x) = c x + (c z - c y)) := by
  classical
  obtain ⟨κ, hκpos, hκ⟩ := bumpTranslation_imm (n := n)
  refine ⟨κ, hκpos, ?_⟩
  intro M _ _ _ _ c hc hcs y hy R hR hclosed z hz hzd
  obtain ⟨Ψ, hΨc, hΨinj, hΨu, hΨid, hΨball, hΨimm, hΨtrans⟩ := hκ (c y) R hR (c z - c y) hzd
  have hΨmd : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Ψ :=
    contMDiff_iff_contDiff.mpr hΨc
  have hΨcy : Ψ (c y) = c z := by rw [hΨu]; abel
  have hmemT : ∀ u ∈ Metric.ball (c y) R, u ∈ c.target :=
    fun u hu => hclosed (Metric.ball_subset_closedBall hu)
  set A : Set M := c.symm '' Metric.ball (c y) R with hA
  let ψ : M → M := fun w => if h : w ∈ c.source then c.symm (Ψ (c w)) else w
  have hψeq : ∀ w, w ∈ c.source → ψ w = c.symm (Ψ (c w)) := by
    intro w hw; simp only [ψ, dif_pos hw]
  have injOn_symm : InjOn c.symm c.target := by
    have h := c.symm.injOn
    rwa [OpenPartialHomeomorph.symm_source] at h
  have hΨmem : ∀ w ∈ c.source, Ψ (c w) ∈ c.target := by
    intro w hw
    by_cases hd : dist (c w) (c y) < R
    · exact hclosed (Metric.ball_subset_closedBall (Metric.mem_ball.mpr (hΨball (c w) hd)))
    · have h0 : Ψ (c w) = c w := hΨid (c w) (by push Not at hd; linarith)
      rw [h0]; exact c.map_source hw
  have hψA : ψ '' A ⊆ A := by
    rintro _ ⟨w, ⟨u, hu, hwu⟩, rfl⟩
    have hws : w ∈ c.source := hwu ▸ c.map_target (hmemT u hu)
    have hcw : c w = u := by rw [← hwu, c.right_inv (hmemT u hu)]
    refine ⟨Ψ (c w), Metric.mem_ball.mpr (hΨball (c w) (by rw [hcw]; exact Metric.mem_ball.mp hu)), ?_⟩
    rw [hψeq w hws]
  have hinjA : InjOn ψ A := by
    rintro w ⟨u, hu, hwu⟩ w' ⟨u', hu', hwu'⟩ heq
    have hws : w ∈ c.source := hwu ▸ c.map_target (hmemT u hu)
    have hw's : w' ∈ c.source := hwu' ▸ c.map_target (hmemT u' hu')
    rw [hψeq w hws, hψeq w' hw's] at heq
    exact c.injOn hws hw's (hΨinj (injOn_symm (hΨmem w hws) (hΨmem w' hw's) heq))
  have hψidA : ∀ w : M, w ∉ A → ψ w = w := by
    intro w hwA
    by_cases hws : w ∈ c.source
    · have hcw : c w ∉ Metric.ball (c y) R := fun hmem => hwA ⟨c w, hmem, c.left_inv hws⟩
      have : Ψ (c w) = c w := hΨid (c w) (by
        have := not_lt.mp (fun h => hcw (Metric.mem_ball.mpr h)); linarith)
      rw [hψeq w hws, this, c.left_inv hws]
    · simp only [ψ, dif_neg hws]
  have hinjψ : Function.Injective ψ := by
    intro w w' h
    by_cases hw : w ∈ A
    · by_cases hw' : w' ∈ A
      · exact hinjA hw hw' h
      · have hmem : ψ w' ∈ A := h ▸ hψA ⟨w, hw, rfl⟩
        rw [hψidA w' hw'] at hmem
        exact absurd hmem hw'
    · by_cases hw' : w' ∈ A
      · have hmem : ψ w ∈ A := h ▸ hψA ⟨w', hw', rfl⟩
        rw [hψidA w hw] at hmem
        exact absurd hmem hw
      · rw [hψidA w hw, hψidA w' hw'] at h; exact h
  refine ⟨ψ, ?_, hinjψ, hψidA, ?_, hψA, ?_, ?_⟩
  · have h1 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ (fun w : M => Ψ (c w)) c.source :=
      hΨmd.contMDiffOn (s := univ) |>.comp hc (fun _ _ => Set.mem_univ _)
    have h2 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
        (fun w : M => c.symm (Ψ (c w))) c.source :=
      hcs.comp h1 (fun w hw => hΨmem w hw)
    have h3 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ ψ c.source :=
      h2.congr (fun w hw => hψeq w hw)
    have hclosedA : IsClosed (c.symm '' Metric.closedBall (c y) R) :=
      ((isCompact_closedBall (c y) R).image_of_continuousOn (c.continuousOn_symm.mono hclosed)).isClosed
    have h4 : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ ψ
        (c.symm '' Metric.closedBall (c y) R)ᶜ :=
      contMDiff_id.contMDiffOn.congr (fun w hw => by
        refine hψidA w (fun hmem => hw ?_)
        rcases hmem with ⟨u, hu, hwu⟩
        exact ⟨u, Metric.ball_subset_closedBall hu, hwu⟩)
    have hcover : c.source ∪ (c.symm '' Metric.closedBall (c y) R)ᶜ = univ := by
      ext w
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
      by_cases hw : w ∈ c.symm '' Metric.closedBall (c y) R
      · left; rcases hw with ⟨u, hu, hwu⟩; rw [← hwu]; exact c.map_target (hclosed hu)
      · exact Or.inr hw
    rw [← contMDiffOn_univ, ← hcover]
    exact h3.union_of_isOpen h4 c.open_source hclosedA.isOpen_compl
  · have : ψ y = c.symm (Ψ (c y)) := hψeq y hy
    rw [this, hΨcy]; exact c.left_inv hz

  · -- the manifold derivative of `ψ` is injective everywhere
    intro w
    by_cases hw : w ∈ c.symm '' Metric.closedBall (c y) (R/2)
    · have hwsrc : w ∈ c.source := by
        rcases hw with ⟨u, hu, rfl⟩
        exact c.map_target (hclosed (Metric.closedBall_subset_closedBall (by linarith [hR]) hu))
      have heq : ψ =ᶠ[𝓝 w] (c.symm ∘ (Ψ ∘ c)) := by
        filter_upwards [c.open_source.mem_nhds hwsrc] with w' hw'
        exact hψeq w' hw'
      have hΨt : Ψ (c w) ∈ c.target := hΨmem w hwsrc
      have hmdΨ : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) Ψ (c w) :=
        (contMDiff_iff_contDiff.mpr hΨc).contMDiffAt.mdifferentiableAt (by simp)
      have hmdcc : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c w :=
        (hc.contMDiffAt (c.open_source.mem_nhds hwsrc)).mdifferentiableAt (by simp)
      have hmdcs : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c.symm (Ψ (c w)) :=
        (hcs.contMDiffAt (c.open_target.mem_nhds hΨt)).mdifferentiableAt (by simp)
      have hinjΨ : Function.Injective (mfderiv
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) Ψ (c w)) := by
        rw [show mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) Ψ (c w)
            = fderiv ℝ Ψ (c w) from mfderiv_eq_fderiv]
        exact hΨimm (c w)
      have hinjc : Function.Injective (mfderiv
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c w) :=
        mfderiv_chart_injective c hc hcs hwsrc
      have hinjcs : Function.Injective (mfderiv
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c.symm (Ψ (c w))) :=
        mfderiv_chart_symm_injective c hc hcs hΨt
      rw [heq.mfderiv_eq]
      have h1 : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (c.symm ∘ (Ψ ∘ c)) w
          = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c.symm (Ψ (c w))).comp
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (Ψ ∘ c) w) :=
        mfderiv_comp w hmdcs (hmdΨ.comp w hmdcc)
      have h2 : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (Ψ ∘ c) w
          = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) Ψ (c w)).comp
            (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) c w) :=
        mfderiv_comp w hmdΨ hmdcc
      rw [h1, h2]
      intro a b hab
      exact Function.Injective.comp hinjcs (Function.Injective.comp hinjΨ hinjc) hab
    · have hDclosed : IsClosed (c.symm '' Metric.closedBall (c y) (R/2)) :=
        ((isCompact_closedBall (c y) (R/2)).image_of_continuousOn
          (c.continuousOn_symm.mono (fun u hu => hclosed
            (Metric.closedBall_subset_closedBall (by linarith [hR]) hu)))).isClosed
      have heq : ψ =ᶠ[𝓝 w] id := by
        filter_upwards [hDclosed.isOpen_compl.mem_nhds hw] with w' hw'
        simp only [Set.mem_compl_iff] at hw'
        by_cases hws : w' ∈ c.source
        · rw [hψeq w' hws]
          have hcw : R/2 ≤ dist (c w') (c y) := by
            by_contra hlt
            push Not at hlt
            exact hw' ⟨c w', Metric.mem_closedBall.mpr hlt.le, c.left_inv hws⟩
          rw [hΨid (c w') hcw, c.left_inv hws]
          simp
        · simp only [ψ, dif_neg hws]
          simp
      have h1 : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ψ w
          = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) id w := heq.mfderiv_eq
      have h2 : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) id w
          = ContinuousLinearMap.id ℝ (TangentSpace (modelWithCornersSelf ℝ
              (EuclideanSpace ℝ (Fin n))) w) := mfderiv_id
      rw [h1, h2]
      intro a b hab
      exact hab
  · intro x hx hd
    rw [hψeq x hx, c.right_inv (hΨmem x hx)]
    exact hΨtrans (c x) hd

/-- **A linear chart germ is an immersion.**  For a chart `c` in the maximal atlas, a base point
`p ∈ c.source` and a non-zero direction `V`, the curve `t ↦ c.symm (c p + t • V)` is smooth and
an immersion at every point of any open set `T` on which it is defined. -/
theorem isImmersion_chartLine {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M)
    {p : M} (hp : p ∈ c.source) {V : EuclideanSpace ℝ (Fin n)} (hV : V ≠ 0)
    {T : Set ℝ} (hTopen : IsOpen T) (hT : ∀ t ∈ T, c p + t • V ∈ c.target) :
    ContMDiffOn Work.Noncompact.CompressionTube.MCreal (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder (fun t => c.symm (c p + t • V)) T ∧
      ∀ t ∈ T, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) (fun t => c.symm (c p + t • V)) t) := by
  have hn0 : Work.Noncompact.CompressionTube.smoothOrder ≠ (0 : WithTop ℕ∞) := by
    simp [Work.Noncompact.CompressionTube.smoothOrder]
  have hcs : ContMDiffOn (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC n) Work.Noncompact.CompressionTube.smoothOrder
      c.symm c.target := contMDiffOn_symm_of_mem_maximalAtlas hc
  have hg : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) Work.Noncompact.CompressionTube.smoothOrder
      (fun s : ℝ => c p + s • V) := by
    rw [Work.Noncompact.CompressionTube.MCreal, Work.Noncompact.CompressionTube.MC,
      Work.Noncompact.CompressionTube.smoothOrder, contMDiff_iff_contDiff]
    fun_prop
  refine ⟨hcs.comp hg.contMDiffOn (fun s hs => hT s hs), ?_⟩
  intro t ht
  have hgt : (fun s : ℝ => c p + s • V) t ∈ c.target := hT t ht
  have hmdg : MDifferentiableAt Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) (fun s : ℝ => c p + s • V) t :=
    hg.contMDiffAt.mdifferentiableAt hn0
  have hmdcs : MDifferentiableAt (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC n) c.symm ((fun s : ℝ => c p + s • V) t) :=
    (hcs.contMDiffAt (c.open_target.mem_nhds hgt)).mdifferentiableAt hn0
  have hcomp : mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        (c.symm ∘ (fun s : ℝ => c p + s • V)) t
      = (mfderiv (Work.Noncompact.CompressionTube.MC n)
          (Work.Noncompact.CompressionTube.MC n) c.symm
          ((fun s : ℝ => c p + s • V) t)).comp
        (mfderiv Work.Noncompact.CompressionTube.MCreal
          (Work.Noncompact.CompressionTube.MC n) (fun s : ℝ => c p + s • V) t) :=
    mfderiv_comp (I := Work.Noncompact.CompressionTube.MCreal)
      (I' := Work.Noncompact.CompressionTube.MC n)
      (I'' := Work.Noncompact.CompressionTube.MC n)
      (f := fun s : ℝ => c p + s • V) (g := c.symm) t hmdcs hmdg
  have hinj_symm : Function.Injective (mfderiv (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC n) c.symm
      ((fun s : ℝ => c p + s • V) t)) := by
    let Φ : PartialDiffeomorph (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n) (EuclideanSpace ℝ (Fin n)) M
        Work.Noncompact.CompressionTube.smoothOrder :=
      { toPartialEquiv := c.symm.toPartialEquiv
        open_source := c.open_target
        open_target := c.open_source
        contMDiffOn_toFun := hcs
        contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas hc }
    have hIso : IsLocalDiffeomorphAt (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC n) Work.Noncompact.CompressionTube.smoothOrder
        c.symm ((fun s : ℝ => c p + s • V) t) :=
      PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ hgt
    rw [← IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hIso hn0]
    exact (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv hIso hn0).injective
  have hinj_g : Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) (fun s : ℝ => c p + s • V) t) := by
    have h_eq : mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) (fun s : ℝ => c p + s • V) t
        = fderiv ℝ (fun s : ℝ => c p + s • V) t := mfderiv_eq_fderiv
    have hfd : fderiv ℝ (fun s : ℝ => c p + s • V) t = (1 : ℝ →L[ℝ] ℝ).smulRight V := by
      rw [fderiv_const_add, fderiv_smul_const differentiableAt_id]
      show (fderiv ℝ id t).smulRight V = (1 : ℝ →L[ℝ] ℝ).smulRight V
      rw [fderiv_id]
      rfl
    rw [h_eq, hfd]
    exact smulRight_one_injective hV
  change Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
    (Work.Noncompact.CompressionTube.MC n) (c.symm ∘ (fun s : ℝ => c p + s • V)) t)
  rw [hcomp]
  intro a b hab
  exact hinj_g (hinj_symm hab)

set_option maxHeartbeats 2000000 in
/-- **A bounded smooth reparametrisation.**  There are `C^∞` functions `φ : ℝ → ℝ` which are
strictly increasing with range in `(a, b)`, agree with the identity on `[0, e₀]` and are affine
with positive slope on `[1/2, 1]`. -/
theorem exists_smooth_reparam (a b e₀ : ℝ) (ha : a < 0) (he₀ : 0 < e₀) (he₀h : e₀ < 1/2)
    (he₀b : e₀ < b) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
      (∀ t : ℝ, 0 < deriv φ t) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0:ℝ) e₀ → φ t = t) ∧
      Set.range φ ⊆ Set.Ioo a b ∧
      φ 1 ∈ Set.Ioo e₀ b ∧
      (∃ μ : ℝ, ∀ t : ℝ, t ∈ Set.Icc (1/2 : ℝ) 1 → φ t = φ 1 + μ * (t - 1)) := by
  classical
  have hm_pos : 0 < min 1 (min ((1/2 - e₀)/16) (min ((b - e₀)/16) ((-a)/16))) :=
    lt_min one_pos (lt_min (by linarith) (lt_min (by linarith) (by linarith)))
  obtain ⟨m, hmpos, hm1, hm2, hm3, hm4⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ m ≤ (1/2 - e₀)/16 ∧
      m ≤ (b - e₀)/16 ∧ m ≤ (-a)/16 :=
    ⟨_, hm_pos, min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)),
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  have hme : e₀ + m < 1/2 := by
    have h : e₀ + (1/2 - e₀)/16 < 1/2 := by linarith
    linarith
  set G : ℝ → ℝ := fun t => m * (1 - Real.smoothTransition (t - 1)) +
      Real.smoothTransition (t - 1) * (m * Real.exp (1 - t)) with hG
  set Lf : ℝ → ℝ := fun t => (1/2) * Real.exp ((t + m)/m) with hLf
  set F : ℝ → ℝ := fun t => (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m))) with hF
  have hFcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by rw [hF]; fun_prop
  obtain ⟨hφcd, hφderiv⟩ := Work.Whitney.contDiff_primitive hFcd
  have hcont : Continuous F := hFcd.continuous
  -- pointwise bounds
  have hGle : ∀ t : ℝ, G t ≤ m := by
    intro t
    show m * (1 - Real.smoothTransition (t - 1)) +
      Real.smoothTransition (t - 1) * (m * Real.exp (1 - t)) ≤ m
    by_cases h : t ≤ 1
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : t - 1 ≤ 0)]; simp
    · push Not at h
      have hexp : Real.exp (1 - t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      have h1 : Real.smoothTransition (t - 1) * (m * Real.exp (1 - t)) ≤
          Real.smoothTransition (t - 1) * m :=
        mul_le_mul_of_nonneg_left (by nlinarith [hexp, hmpos]) (Real.smoothTransition.nonneg _)
      nlinarith [h1]
  have hG0 : ∀ t : ℝ, t ≤ 1 → G t = m := by
    intro t ht
    show m * (1 - Real.smoothTransition (t - 1)) +
      Real.smoothTransition (t - 1) * (m * Real.exp (1 - t)) = m
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : t - 1 ≤ 0)]; ring
  have hGdec : ∀ t : ℝ, 2 ≤ t → G t = m * Real.exp (1 - t) := by
    intro t ht
    show m * (1 - Real.smoothTransition (t - 1)) +
      Real.smoothTransition (t - 1) * (m * Real.exp (1 - t)) = m * Real.exp (1 - t)
    rw [Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ t - 1)]; ring
  have hGpos : ∀ t : ℝ, 0 < G t := by
    intro t
    show 0 < m * (1 - Real.smoothTransition (t - 1)) +
      Real.smoothTransition (t - 1) * (m * Real.exp (1 - t))
    by_cases h : t ≤ 1
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : t - 1 ≤ 0)]; simpa using hmpos
    · push Not at h
      have hs := Real.smoothTransition.le_one (t - 1)
      have h0 := Real.smoothTransition.nonneg (t - 1)
      have hpos : 0 < Real.exp (1 - t) := Real.exp_pos _
      rcases lt_or_eq_of_le hs with h' | h'
      · have h2 : 0 ≤ Real.smoothTransition (t - 1) * (m * Real.exp (1 - t)) :=
          mul_nonneg (Real.smoothTransition.nonneg _) (mul_nonneg hmpos.le (Real.exp_nonneg _))
        nlinarith [h2, h', hmpos, h0]
      · rw [h']; nlinarith [hpos, hmpos]
  have hLfle : ∀ t : ℝ, t ≤ -2*m → Lf t ≤ 1/2 := by
    intro t ht
    show (1/2) * Real.exp ((t + m)/m) ≤ 1/2
    have h2 : Real.exp ((t + m)/m) ≤ 1 := by
      rw [Real.exp_le_one_iff, div_le_iff₀ hmpos]; linarith
    nlinarith
  have hLfpos : ∀ t : ℝ, 0 < Lf t := by
    intro t; show 0 < (1/2) * Real.exp ((t + m)/m); positivity
  have hFpos : ∀ t : ℝ, 0 < F t := by
    intro t
    show 0 < (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m)))
    have hs1 := Real.smoothTransition.le_one ((t - e₀)/m)
    have h01 := Real.smoothTransition.nonneg ((t - e₀)/m)
    have hs2 := Real.smoothTransition.le_one ((-t - m)/m)
    have h02 := Real.smoothTransition.nonneg ((-t - m)/m)
    have hA : 0 < Real.smoothTransition ((t - e₀)/m) * G t +
        (1 - Real.smoothTransition ((t - e₀)/m)) := by
      rcases lt_or_eq_of_le hs1 with h | h
      · nlinarith [h01, hGpos t]
      · rw [h]; simpa using hGpos t
    have hB : 0 < Real.smoothTransition ((-t - m)/m) * Lf t +
        (1 - Real.smoothTransition ((-t - m)/m)) := by
      rcases lt_or_eq_of_le hs2 with h | h
      · nlinarith [h02, hLfpos t]
      · rw [h]; simpa using hLfpos t
    exact mul_pos hA hB
  have hFle : ∀ t : ℝ, F t ≤ 1 := by
    intro t
    show (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m))) ≤ 1
    have hs1 := Real.smoothTransition.le_one ((t - e₀)/m)
    have h01 := Real.smoothTransition.nonneg ((t - e₀)/m)
    have hs2 := Real.smoothTransition.le_one ((-t - m)/m)
    have h02 := Real.smoothTransition.nonneg ((-t - m)/m)
    have hA : Real.smoothTransition ((t - e₀)/m) * G t +
        (1 - Real.smoothTransition ((t - e₀)/m)) ≤ 1 := by
      nlinarith [h01, hs1, hGle t, (hGpos t).le]
    have hB : Real.smoothTransition ((-t - m)/m) * Lf t +
        (1 - Real.smoothTransition ((-t - m)/m)) ≤ 1 := by
      by_cases h : -m ≤ t
      · have h2 : Real.smoothTransition ((-t - m)/m) = 0 :=
          Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; exact ⟨by linarith, hmpos.le⟩)
        rw [h2]; norm_num
      · push Not at h
        have hL2 : Lf t ≤ 1 := by
          show (1/2) * Real.exp ((t + m)/m) ≤ 1
          have h3 : Real.exp ((t + m)/m) ≤ 1 := by
            rw [Real.exp_le_one_iff, div_le_iff₀ hmpos]; linarith
          linarith
        nlinarith [h02, hs2, hL2]
    have hBpos : 0 ≤ Real.smoothTransition ((-t - m)/m) * Lf t +
        (1 - Real.smoothTransition ((-t - m)/m)) := by
      rcases lt_or_eq_of_le hs2 with hh | hh
      · nlinarith [h02, (hLfpos t).le]
      · rw [hh]; simpa using (hLfpos t).le
    calc _ ≤ 1 * 1 := mul_le_mul hA hB hBpos (by norm_num)
      _ = 1 := by norm_num
  have hFid : ∀ t : ℝ, 0 ≤ t → t ≤ e₀ → F t = 1 := by
    intro t ht0 ht1
    show (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m))) = 1
    have h1 : Real.smoothTransition ((t - e₀)/m) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; exact ⟨by linarith, hmpos.le⟩)
    have h2 : Real.smoothTransition ((-t - m)/m) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; exact ⟨by linarith, hmpos.le⟩)
    rw [h1, h2, hG0 t (by linarith)]; ring
  have hFaff : ∀ t : ℝ, e₀ + m ≤ t → t ≤ 1 → F t = m := by
    intro t ht0 ht1
    show (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m))) = m
    have h1 : Real.smoothTransition ((t - e₀)/m) = 1 :=
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hmpos]; linarith)
    have h2 : Real.smoothTransition ((-t - m)/m) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; exact ⟨by linarith, hmpos.le⟩)
    rw [h1, h2, hG0 t ht1]; ring
  have hFmid : ∀ t : ℝ, 1 ≤ t → F t = G t := by
    intro t ht0
    show (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m))) = G t
    have h1 : Real.smoothTransition ((t - e₀)/m) = 1 :=
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hmpos]; linarith)
    have h2 : Real.smoothTransition ((-t - m)/m) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; exact ⟨by linarith, hmpos.le⟩)
    rw [h1, h2]; ring
  have hFlow : ∀ t : ℝ, t ≤ -2*m → F t = Lf t := by
    intro t ht
    show (Real.smoothTransition ((t - e₀)/m) * G t +
      (1 - Real.smoothTransition ((t - e₀)/m))) *
      (Real.smoothTransition ((-t - m)/m) * Lf t +
      (1 - Real.smoothTransition ((-t - m)/m))) = Lf t
    have h1 : Real.smoothTransition ((-t - m)/m) = 1 :=
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hmpos]; linarith)
    have h2 : Real.smoothTransition ((t - e₀)/m) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by rw [div_nonpos_iff]; right; exact ⟨by linarith, hmpos.le⟩)
    rw [h1, h2]; ring
  -- integral estimates
  have hAB : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hcont.intervalIntegrable _ _
  have hIntA : ∫ x in (-m)..(0:ℝ), F x ≤ m := by
    have h := intervalIntegral.integral_mono_on (f := F) (g := fun _ : ℝ => (1:ℝ))
      (by linarith : (-m:ℝ) ≤ 0) (hAB _ _) intervalIntegrable_const (fun x _ => hFle x)
    have h2 : ∫ x in (-m)..(0:ℝ), (1:ℝ) = m := by
      rw [intervalIntegral.integral_const]; simp
    linarith [h, h2.le]
  have hIntB : ∫ x in (0:ℝ)..e₀, F x = e₀ := by
    rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (1:ℝ)) (fun x hx => by
      rw [Set.uIcc_of_le he₀.le] at hx
      exact hFid x hx.1 hx.2)]
    rw [intervalIntegral.integral_const]; simp
  have hIntC : ∫ x in e₀..(e₀ + m), F x ≤ m := by
    have h := intervalIntegral.integral_mono_on (f := F) (g := fun _ : ℝ => (1:ℝ))
      (by linarith : e₀ ≤ e₀ + m) (hAB _ _) intervalIntegrable_const (fun x _ => hFle x)
    have h2 : ∫ x in e₀..(e₀ + m), (1:ℝ) = m := by
      rw [intervalIntegral.integral_const]; simp
    linarith [h, h2.le]
  have hIntD : ∫ x in (e₀ + m)..(1:ℝ), F x = m * (1 - e₀ - m) := by
    rw [intervalIntegral.integral_congr (g := fun _ : ℝ => m) (fun x hx => by
      rw [Set.uIcc_of_le (by linarith : e₀ + m ≤ (1:ℝ))] at hx
      exact hFaff x hx.1 hx.2)]
    rw [intervalIntegral.integral_const]; simp; ring
  have hIntE : ∫ x in (1:ℝ)..2, F x ≤ m := by
    have h := intervalIntegral.integral_mono_on (f := F) (g := fun _ : ℝ => m)
      (by norm_num : (1:ℝ) ≤ 2) (hAB _ _) intervalIntegrable_const (fun x hx => by
        rw [hFmid x hx.1]; exact hGle x)
    have h2 : ∫ x in (1:ℝ)..2, m = m := by
      rw [intervalIntegral.integral_const]; norm_num
    linarith [h, h2.le]
  have hIntF : ∀ t : ℝ, 2 ≤ t → ∫ x in (2:ℝ)..t, F x ≤ m := by
    intro t ht
    have hpt : Set.EqOn F (fun x => m * Real.exp (1 - x)) (Set.uIcc (2:ℝ) t) := by
      intro x hx
      rw [Set.uIcc_of_le ht] at hx
      rw [hFmid x (by linarith [hx.1]), hGdec x hx.1]
    rw [intervalIntegral.integral_congr hpt]
    have hderiv : ∀ x ∈ Set.uIcc (2:ℝ) t, HasDerivAt (fun y : ℝ => -m * Real.exp (1 - y))
        (m * Real.exp (1 - x)) x := by
      intro x hx
      have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub 1
      have h2 : HasDerivAt (fun y : ℝ => Real.exp (1 - y)) (Real.exp (1 - x) * (-1)) x := h1.exp
      have h3 : HasDerivAt (fun y : ℝ => -m * Real.exp (1 - y))
          (-m * (Real.exp (1 - x) * (-1))) x := h2.const_mul (-m)
      have h4 : -m * (Real.exp (1 - x) * (-1)) = m * Real.exp (1 - x) := by ring
      rw [h4] at h3
      exact h3
    have hint : IntervalIntegrable (fun x : ℝ => m * Real.exp (1 - x)) volume 2 t :=
      ((by fun_prop : Continuous fun x : ℝ => m * Real.exp (1 - x))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h2 : Real.exp (1 - 2) = Real.exp (-1) := by norm_num
    rw [h2]
    have h3 : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have h4 : Real.exp (1 - t) ≥ 0 := Real.exp_nonneg _
    nlinarith [h3, h4, hmpos]
  have hIntG : ∀ t : ℝ, t ≤ -2*m → ∫ x in t..(-2*m), F x ≤ (1/2) * m := by
    intro t ht
    have hpt : Set.EqOn F (fun x => (1/2) * Real.exp ((x + m)/m)) (Set.uIcc t (-2*m)) := by
      intro x hx
      rw [Set.uIcc_of_le ht] at hx
      rw [hFlow x hx.2, hLf]
    rw [intervalIntegral.integral_congr hpt]
    have hderiv : ∀ x ∈ Set.uIcc t (-2*m),
        HasDerivAt (fun y : ℝ => (1/2) * m * Real.exp ((y + m)/m))
          ((1/2) * Real.exp ((x + m)/m)) x := by
      intro x hx
      have h1 : HasDerivAt (fun y : ℝ => (y + m)/m) (1/m) x := by
        simpa using ((hasDerivAt_id x).add_const m).div_const m
      have h2 : HasDerivAt (fun y : ℝ => Real.exp ((y + m)/m))
          (Real.exp ((x + m)/m) * (1/m)) x := h1.exp
      have h3 : HasDerivAt (fun y : ℝ => (1/2) * m * Real.exp ((y + m)/m))
          ((1/2) * m * (Real.exp ((x + m)/m) * (1/m))) x := h2.const_mul ((1/2) * m)
      have h4 : (1/2) * m * (Real.exp ((x + m)/m) * (1/m)) = (1/2) * Real.exp ((x + m)/m) := by
        field_simp
      rw [h4] at h3
      exact h3
    have hint : IntervalIntegrable (fun x : ℝ => (1/2) * Real.exp ((x + m)/m)) volume t (-2*m) :=
      ((by fun_prop : Continuous fun x : ℝ => (1/2) * Real.exp ((x + m)/m))).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h2 : Real.exp ((-2*m + m)/m) = Real.exp (-1) := by
      have h5 : (-2*m + m)/m = -1 := by field_simp; ring
      rw [h5]
    rw [h2]
    have h3 : Real.exp ((t + m)/m) ≥ 0 := Real.exp_nonneg _
    have h4 : Real.exp (-1) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    nlinarith [h3, h4, hmpos]
  -- assembled bounds
  have hφ_mono : StrictMono (fun t : ℝ => ∫ x in (0:ℝ)..t, F x) :=
    strictMono_of_deriv_pos (fun t => by rw [(hφderiv t).deriv]; exact hFpos t)
  have h1φ : (∫ x in (0:ℝ)..(1:ℝ), F x) ≤ e₀ + 2*m := by
    have h1 : ∫ x in (0:ℝ)..(1:ℝ), F x
        = (∫ x in (0:ℝ)..e₀, F x) + ∫ x in e₀..(1:ℝ), F x :=
      (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
    have h2 : ∫ x in e₀..(1:ℝ), F x
        = (∫ x in e₀..(e₀+m), F x) + ∫ x in (e₀+m)..(1:ℝ), F x :=
      (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
    have h4 : ∫ x in (e₀ + m)..(1:ℝ), F x ≤ m := by
      have h5 : m * (1 - e₀ - m) ≤ m := by nlinarith [hmpos, hme]
      linarith [hIntD, h5]
    rw [h1, h2, hIntB]
    linarith [hIntC, h4]
  have htail : ∀ t : ℝ, 1 ≤ t → ∫ x in (1:ℝ)..t, F x ≤ 2*m := by
    intro t ht
    by_cases h2 : t ≤ 2
    · have hsplit : ∫ x in (1:ℝ)..(2:ℝ), F x = (∫ x in (1:ℝ)..t, F x) + ∫ x in t..(2:ℝ), F x :=
        (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
      have h2' : 0 ≤ ∫ x in t..(2:ℝ), F x :=
        intervalIntegral.integral_nonneg_of_forall h2 (fun x => (hFpos x).le)
      linarith [hIntE, h2', hsplit]
    · push Not at h2
      have hsplit : ∫ x in (1:ℝ)..t, F x = (∫ x in (1:ℝ)..(2:ℝ), F x) + ∫ x in (2:ℝ)..t, F x :=
        (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
      linarith [hIntE, hIntF t h2.le, hsplit]
  have hneg : ∀ t : ℝ, t ≤ 0 → ∫ x in t..(0:ℝ), F x ≤ (5/2)*m := by
    intro t ht
    have hlow : ∫ x in (-2*m)..(-m), F x ≤ m := by
      have h := intervalIntegral.integral_mono_on (f := F) (g := fun _ : ℝ => (1:ℝ))
        (by linarith : (-2*m:ℝ) ≤ -m) (hAB _ _) intervalIntegrable_const (fun x _ => hFle x)
      have h3 : ∫ x in (-2*m)..(-m), (1:ℝ) = m := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      linarith [h, h3.le]
    have hsplit2 : ∫ x in (-2*m)..(0:ℝ), F x =
        (∫ x in (-2*m)..(-m), F x) + ∫ x in (-m)..(0:ℝ), F x :=
      (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
    by_cases h2 : t ≤ -2*m
    · have hsplit1 : ∫ x in t..(0:ℝ), F x =
          (∫ x in t..(-2*m), F x) + ∫ x in (-2*m)..(0:ℝ), F x :=
        (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
      have hg := hIntG t h2
      linarith [hg, hlow, hIntA, hsplit1, hsplit2]
    · push Not at h2
      have hsplit1 : ∫ x in (-2*m)..(0:ℝ), F x =
          (∫ x in (-2*m)..t, F x) + ∫ x in t..(0:ℝ), F x :=
        (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
      have h3 : 0 ≤ ∫ x in (-2*m)..t, F x :=
        intervalIntegral.integral_nonneg_of_forall (by linarith : (-2*m:ℝ) ≤ t)
          (fun x => (hFpos x).le)
      linarith [hlow, hIntA, hsplit1, hsplit2, h3]
  have hrange : Set.range (fun t : ℝ => ∫ x in (0:ℝ)..t, F x) ⊆ Set.Ioo a b := by
    rintro y ⟨t, rfl⟩
    change a < (∫ x in (0:ℝ)..t, F x) ∧ (∫ x in (0:ℝ)..t, F x) < b
    have hb0 : 0 < b := lt_trans he₀ he₀b
    constructor
    · by_cases ht : t ≤ 0
      · have hsymm : ∫ x in (0:ℝ)..t, F x = -∫ x in t..(0:ℝ), F x :=
          intervalIntegral.integral_symm t 0
        rw [hsymm]
        have hb2 : (5/2)*m < -a := by nlinarith [hm4, ha, hmpos]
        linarith [hneg t ht, hb2]
      · push Not at ht
        have h2 : 0 ≤ ∫ x in (0:ℝ)..t, F x :=
          intervalIntegral.integral_nonneg_of_forall ht.le (fun x => (hFpos x).le)
        linarith [ha, h2]
    · by_cases ht : t ≤ 0
      · have hsymm : ∫ x in (0:ℝ)..t, F x = -∫ x in t..(0:ℝ), F x :=
          intervalIntegral.integral_symm t 0
        rw [hsymm]
        have h2 : 0 ≤ ∫ x in t..(0:ℝ), F x :=
          intervalIntegral.integral_nonneg_of_forall ht (fun x => (hFpos x).le)
        linarith [h2, hb0]
      · push Not at ht
        by_cases ht1 : t ≤ 1
        · have hsplit : ∫ x in (0:ℝ)..(1:ℝ), F x = (∫ x in (0:ℝ)..t, F x) + ∫ x in t..(1:ℝ), F x :=
            (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
          have h2 : 0 ≤ ∫ x in t..(1:ℝ), F x :=
            intervalIntegral.integral_nonneg_of_forall ht1 (fun x => (hFpos x).le)
          have hb' : e₀ + 2*m < b := by nlinarith [hm3, he₀b]
          linarith [h1φ, h2, hsplit, hb']
        · push Not at ht1
          have hsplit : ∫ x in (0:ℝ)..t, F x = (∫ x in (0:ℝ)..(1:ℝ), F x) + ∫ x in (1:ℝ)..t, F x :=
            (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
          have hb' : e₀ + 4*m < b := by nlinarith [hm3, he₀b]
          linarith [h1φ, htail t ht1.le, hsplit, hb']
  have hmono : (∫ x in (0:ℝ)..e₀, F x) < ∫ x in (0:ℝ)..(1:ℝ), F x :=
    hφ_mono (by linarith : e₀ < 1)
  refine ⟨fun t => ∫ x in (0:ℝ)..t, F x, hφcd, ?_, ?_, hrange, ?_, ?_⟩
  · intro t
    rw [(hφderiv t).deriv]
    exact hFpos t
  · intro t ht
    rw [Set.mem_Icc] at ht
    change ∫ x in (0:ℝ)..t, F x = t
    have hcc : ∫ x in (0:ℝ)..t, F x = ∫ x in (0:ℝ)..t, (1:ℝ) :=
      intervalIntegral.integral_congr (fun x hx => by
        rw [Set.uIcc_of_le ht.1] at hx
        exact hFid x hx.1 (by linarith [hx.2, ht.2]))
    rw [hcc, intervalIntegral.integral_const]
    simp
  · show e₀ < (∫ x in (0:ℝ)..(1:ℝ), F x) ∧ (∫ x in (0:ℝ)..(1:ℝ), F x) < b
    have hb' : e₀ + 2*m < b := by nlinarith [hm3, he₀b]
    constructor
    · linarith [hmono, hIntB]
    · linarith [h1φ, hb']
  · refine ⟨m, fun t ht => ?_⟩
    rw [Set.mem_Icc] at ht
    have htle : t ≤ 1 := ht.2
    have hsplit : ∫ x in (0:ℝ)..(1:ℝ), F x = (∫ x in (0:ℝ)..t, F x) + ∫ x in t..(1:ℝ), F x :=
      (intervalIntegral.integral_add_adjacent_intervals (hAB _ _) (hAB _ _)).symm
    have hmid : ∫ x in t..(1:ℝ), F x = ∫ x in t..(1:ℝ), m :=
      intervalIntegral.integral_congr (fun x hx => by
        rw [Set.uIcc_of_le htle] at hx
        exact hFaff x (by linarith [ht.1, hme, hx.1]) hx.2)
    rw [hmid, intervalIntegral.integral_const] at hsplit
    have hconst : ((1:ℝ) - t) • m = m * (1 - t) := by ring
    rw [hconst] at hsplit
    linarith [hsplit]

/-- **The seed arc.**  In the situation of `immersedArcWithGerm`, the prescribed germ line
`t ↦ c.symm (c p + t • v)` can be reparametrised so that it becomes a *global* smooth immersion
`A : ℝ → M` which agrees with the germ on an interval `[0, e₀]`, is injective on `[0,1]`, runs
inside `W` on `[0,1]` and ends with a straight germ in the same chart `c`. -/
theorem exists_germ_arc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M]
    {W : Set M} (hW : IsOpen W) {p : M} (hp : p ∈ W)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) (hpc : p ∈ c.source)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0)
    (hger : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t ≤ e → c.symm (c p + t • v) ∈ W)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ < 1 / 2 ∧ e₀ < δ ∧
      (∀ s ∈ Set.Icc (0:ℝ) 1, c.symm (c p + s • (e₀ • v)) ∈ W) ∧
      ∃ A : ℝ → M,
        ContMDiff MCreal (MC n) smoothOrder A ∧ A 0 = p ∧
        (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) A t)) ∧
        Set.InjOn A (Set.Icc (0:ℝ) 1) ∧
        (∀ t ∈ Set.Icc (0:ℝ) 1, A t ∈ W) ∧
        (∀ t ∈ Set.Icc (0:ℝ) e₀, A t = c.symm (c p + t • v)) ∧
        (∀ t ∈ Set.Icc (0:ℝ) e₀, c p + t • v ∈ c.target) ∧
        (∀ s ∈ Set.Icc (0:ℝ) 1, A 1 ≠ c.symm (c p + s • (e₀ • v))) ∧
        (∃ (w : EuclideanSpace ℝ (Fin n)) (ε : ℝ), w ≠ 0 ∧ 0 < ε ∧
          ∀ t : ℝ, 1 - ε ≤ t → t ≤ 1 →
            A t ∈ c.source ∧ c (A t) = c (A 1) + (t - 1) • w) := by
  obtain ⟨e_h, he_h_pos, hger'⟩ := hger
  have hc_s : ContMDiffOn (MC n) (MC n) smoothOrder c.symm c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hc
  have hcp : c p ∈ c.target := c.map_source hpc
  obtain ⟨ρ₀, hρ₀pos, hρ₀sub⟩ := Metric.isOpen_iff.mp c.open_target (c p) hcp
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set ρv : ℝ := ρ₀ / ‖v‖ with hρvdef
  have hρvpos : 0 < ρv := by rw [hρvdef]; positivity
  have hρvρ : ρv * ‖v‖ = ρ₀ := by rw [hρvdef]; field_simp
  have hchart : ∀ t : ℝ, |t| < ρv → c p + t • v ∈ c.target := by
    intro t ht
    apply hρ₀sub
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show c p + t • v - c p = t • v from by abel, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖v‖ < ρv * ‖v‖ := by nlinarith [abs_nonneg t]
      _ = ρ₀ := hρvρ
  set b : ℝ := min e_h ρv with hbdef
  have hbpos : 0 < b := lt_min he_h_pos hρvpos
  have hble : b ≤ e_h := min_le_left _ _
  have hblr : b ≤ ρv := min_le_right _ _
  set e₀ : ℝ := min (1 / 2) (min b δ) / 2 with he₀def
  have he₀pos : 0 < e₀ := by
    rw [he₀def]; exact div_pos (lt_min (by norm_num) (lt_min hbpos hδ)) (by norm_num)
  have he₀h : e₀ < 1 / 2 := by
    rw [he₀def]
    have h1 : min (1 / 2) (min b δ) ≤ 1 / 2 := min_le_left _ _
    linarith
  have he₀b : e₀ < b := by
    rw [he₀def]
    have h1 : min (1 / 2) (min b δ) ≤ b := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have he₀δ : e₀ < δ := by
    rw [he₀def]
    have h1 : min (1 / 2) (min b δ) ≤ δ := le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  have he₀ρ : e₀ < ρv := lt_of_lt_of_le he₀b hblr
  obtain ⟨φ, hφcd, hφmono, hφid, hφrange, hφ1, μ, hμ⟩ :=
    exists_smooth_reparam (-ρv) b e₀ (by linarith) he₀pos he₀h he₀b
  have hφstrict : StrictMono φ := strictMono_of_deriv_pos hφmono
  have hφ0 : φ 0 = 0 := hφid 0 (by constructor <;> linarith)
  have hφe : φ e₀ = e₀ := hφid e₀ (by constructor <;> linarith)
  have hμpos : 0 < μ := by
    have h1 : φ (1 / 2) = φ 1 + μ * (1 / 2 - 1) := hμ (1 / 2) (by constructor <;> norm_num)
    have h2 : φ (1 / 2) < φ 1 := hφstrict (by norm_num)
    linarith
  set A : ℝ → M := fun t => c.symm (c p + (φ t) • v) with hAdef
  have hAval : ∀ t : ℝ, A t = c.symm (c p + (φ t) • v) := fun t => rfl
  have hAin : ∀ t : ℝ, c p + (φ t) • v ∈ c.target := by
    intro t
    apply hchart (φ t)
    have h := hφrange (Set.mem_range_self t)
    exact abs_lt.mpr ⟨by linarith [h.1], by linarith [h.2, hblr]⟩
  have hgermW : ∀ s ∈ Set.Icc (0:ℝ) 1, c.symm (c p + s • (e₀ • v)) ∈ W := by
    intro s hs
    rw [smul_smul]
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, zero_mul, zero_smul, add_zero, c.left_inv hpc]; exact hp
    · exact hger' (s * e₀) (mul_pos h0 he₀pos) (by nlinarith [hs.2, he₀b, hble])
  have hA1not : ∀ s ∈ Set.Icc (0:ℝ) 1, A 1 ≠ c.symm (c p + s • (e₀ • v)) := by
    intro s hs hcontra
    rw [hAval 1, smul_smul] at hcontra
    have hsρ : |s * e₀| < ρv := by
      rw [abs_of_nonneg (mul_nonneg hs.1 he₀pos.le)]
      nlinarith [hs.2, he₀ρ, he₀pos]
    have hinj : Set.InjOn c.symm c.target := by
      have h := c.symm.injOn
      rwa [OpenPartialHomeomorph.symm_source] at h
    have h1 : c p + (φ 1) • v = c p + (s * e₀) • v := hinj (hAin 1) (hchart _ hsρ) hcontra
    have h2 : (φ 1 - s * e₀) • v = 0 := by rw [sub_smul, add_left_cancel h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · have h3 : φ 1 = s * e₀ := sub_eq_zero.mp h
      have h4 : φ 1 ≤ e₀ := by nlinarith [hs.2, he₀pos]
      linarith [hφ1.1]
    · exact absurd h hv
  refine ⟨e₀, he₀pos, he₀h, he₀δ, hgermW, A, ?_, ?_, ?_, ?_, ?_, ?_,
    (fun t ht => hchart t (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2, he₀ρ]⟩)),
    hA1not, ?_⟩
  · -- ContMDiff
    have hinner : ContMDiff MCreal (MC n) smoothOrder (fun t : ℝ => c p + (φ t) • v) := by
      rw [MCreal, MC, smoothOrder, contMDiff_iff_contDiff]
      fun_prop
    exact hc_s.comp_contMDiff hinner hAin
  · -- A 0 = p
    rw [hAval 0, hφ0, zero_smul, add_zero, c.left_inv hpc]
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
  · -- Injectivity on [0,1]
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
    · exact hger' (φ t) (by rw [← hφ0]; exact hφstrict h0)
        (le_trans (hφstrict.monotone ht.2) (le_of_lt (lt_of_lt_of_le hφ1.2 hble)))
  · -- germ on [0,e₀]
    intro t ht
    rw [hAval t, hφid t ht]
  · -- terminal clause
    refine ⟨μ • v, 1 / 2, ?_, by norm_num, ?_⟩
    · exact smul_ne_zero hμpos.ne' hv
    · intro t ht1 ht2
      have h1 : φ t = φ 1 + μ * (t - 1) := hμ t (by constructor <;> linarith)
      have hcA1 : c (A 1) = c p + (φ 1) • v := by
        rw [hAval 1]; exact c.right_inv (hAin 1)
      constructor
      · rw [hAval t]; exact c.map_target (hAin t)
      · rw [hAval t, c.right_inv (hAin t), hcA1, h1]
        module


/-- A real number is a valid bump constant for the manifold bump lemma on `M`. -/
def IsBumpConst (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M] [T2Space M]
    (κ : ℝ) : Prop :=
  ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
    ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ c c.source →
    ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ c.symm c.target →
    ∀ (y : M), y ∈ c.source → ∀ (R : ℝ), 0 < R →
    Metric.closedBall (c y) R ⊆ c.target →
    ∀ z : M, z ∈ c.source → ‖c z - c y‖ < κ * R →
    ∃ ψ : M → M,
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ ψ ∧
      Function.Injective ψ ∧
      (∀ w : M, w ∉ c.symm '' Metric.ball (c y) R → ψ w = w) ∧
      ψ y = z ∧
      ψ '' (c.symm '' Metric.ball (c y) R) ⊆ c.symm '' Metric.ball (c y) R ∧
      (∀ w : M, Function.Injective (mfderiv
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ψ w)) ∧
      (∀ x ∈ c.source, dist (c x) (c y) ≤ R/4 → c (ψ x) = c x + (c z - c y))

lemma exists_isBumpConst (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M] [T2Space M] :
    ∃ κ > 0, IsBumpConst n (M := M) κ := by
  obtain ⟨κ, hκpos, hκ⟩ := exists_bump_imm (n := n)
  exact ⟨κ, hκpos, fun c hc hcs => hκ c hc hcs⟩

theorem bump_step {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M]
    {W : Set M} {p : M} {v : EuclideanSpace ℝ (Fin n)} {e₀ : ℝ} (he₀pos : 0 < e₀)
    {κ : ℝ} (hκspec : IsBumpConst n (M := M) κ)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {α : ℝ → M} (hαcd : ContMDiff MCreal (MC n) smoothOrder α) (hα0 : α 0 = p)
    (hαimm : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) α t))
    (hαinj : Set.InjOn α (Set.Icc (0:ℝ) 1))
    (hαimg : ∀ t ∈ Set.Icc (0:ℝ) 1, α t ∈ W)
    (hαgerm : ∀ t ∈ Set.Icc (0:ℝ) e₀, α t = c.symm (c p + t • v))
    {cc : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hccc : ContMDiffOn (MC n) (MC n) smoothOrder cc cc.source)
    (hccs : ContMDiffOn (MC n) (MC n) smoothOrder cc.symm cc.target)
    (hα1src : α 1 ∈ cc.source)
    {R : ℝ} (hRpos : 0 < R) (hRclosed : Metric.closedBall (cc (α 1)) R ⊆ cc.target)
    (hRW : cc.symm '' Metric.ball (cc (α 1)) R ⊆ W)
    (hRavoid : ∀ t ∈ Set.Icc (0:ℝ) e₀, α t ∉ cc.symm '' Metric.ball (cc (α 1)) R)
    {z' : M} (hz'src : z' ∈ cc.source) (hz'dist : ‖cc z' - cc (α 1)‖ < κ * R) :
    ∃ α' : ℝ → M, ContMDiff MCreal (MC n) smoothOrder α' ∧ α' 0 = p ∧ α' 1 = z' ∧
      (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) α' t)) ∧
      Set.InjOn α' (Set.Icc (0:ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, α' t ∈ W) ∧
      (∀ t ∈ Set.Icc (0:ℝ) e₀, α' t = c.symm (c p + t • v)) := by
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  obtain ⟨ψ, hψcd, hψinj, hψid, hψz, hψA, hψimm, -⟩ :=
    hκspec cc hccc hccs (α 1) hα1src R hRpos hRclosed z' hz'src hz'dist
  refine ⟨ψ ∘ α, hψcd.comp hαcd, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (ψ ∘ α) 0 = p
    rw [Function.comp_apply]
    have h := hψid (α 0) (hRavoid 0 ⟨le_refl 0, he₀pos.le⟩)
    rw [hα0] at h ⊢
    exact h
  · show (ψ ∘ α) 1 = z'
    rw [Function.comp_apply]
    exact hψz
  · intro t
    have hψmd : MDifferentiableAt (MC n) (MC n) ψ (α t) :=
      hψcd.contMDiffAt.mdifferentiableAt hn0
    have hαmd : MDifferentiableAt MCreal (MC n) α t :=
      hαcd.contMDiffAt.mdifferentiableAt hn0
    have hcomp := mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MC n) (f := α) (g := ψ) t
      hψmd hαmd
    rw [hcomp]
    intro a b hab
    simp only [ContinuousLinearMap.comp_apply] at hab
    exact hαimm t (hψimm (α t) hab)
  · intro s hs t ht hst
    exact hαinj hs ht (hψinj hst)
  · intro t ht
    by_cases hmem : α t ∈ cc.symm '' Metric.ball (cc (α 1)) R
    · exact hRW (hψA ⟨α t, hmem, rfl⟩)
    · rw [Function.comp_apply, hψid (α t) hmem]; exact hαimg t ht
  · intro t ht
    rw [Function.comp_apply, hψid (α t) (hRavoid t ht)]
    exact hαgerm t ht

set_option maxHeartbeats 2000000 in
/-- **Straightening a smooth curve germ in `ℝⁿ`.**  Given a `C^∞` curve `k : ℝ → ℝⁿ` with
`k 1 = x₀` and nonzero velocity `v = k'(1)`, there is an open partial homeomorphism `Φ` of `ℝⁿ`,
smooth with smooth inverse, fixing `x₀`, which straightens the germ of `k` at `1` to the line
`t ↦ x₀ + (t - 1) • v`. -/
theorem exists_straightening {n : ℕ} {k : ℝ → EuclideanSpace ℝ (Fin n)}
    {x₀ v : EuclideanSpace ℝ (Fin n)} {V : Set ℝ}
    (hV : IsOpen V) (h1V : (1 : ℝ) ∈ V) (hk : ContDiffOn ℝ smoothOrder k V)
    (hk1 : k 1 = x₀) (hkd : (fderiv ℝ k 1) 1 = v) (hvne : v ≠ 0) :
    ∃ (Φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
      (ρ : ℝ), 0 < ρ ∧ (∀ x ∈ Φ.source, ContDiffAt ℝ smoothOrder (↑Φ) x) ∧
      (∀ y ∈ Φ.target, ContDiffAt ℝ smoothOrder (↑Φ.symm) y) ∧
      Φ x₀ = x₀ ∧ Φ.symm x₀ = x₀ ∧
      (∀ t : ℝ, |t - 1| ≤ ρ → k t ∈ Φ.target ∧ Φ.symm (k t) = x₀ + (t - 1) • v) := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hk1at : ContDiffAt ℝ smoothOrder k 1 := hk.contDiffAt (hV.mem_nhds h1V)
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hvvpos : 0 < inner ℝ v v := by
    rw [real_inner_self_eq_norm_sq]; exact pow_pos hvnorm 2
  have hvvne : inner ℝ v v ≠ 0 := ne_of_gt hvvpos
  -- positivity of the `v`-component of the derivative near `1`
  have hfd_cont : ContinuousAt (fderiv ℝ k) 1 := hk1at.continuousAt_fderiv hn0
  have hev_cont : ContinuousAt (fun t : ℝ => (fderiv ℝ k t) 1) 1 := by
    have hg : ContinuousAt (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1)
        (fderiv ℝ k 1) :=
      (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) (1:ℝ)).continuous.continuousAt
    exact hg.comp hfd_cont
  have hpos1 : 0 < inner ℝ ((fderiv ℝ k 1) 1) v := by
    have h : inner ℝ ((fderiv ℝ k 1) 1) v = ‖v‖ ^ 2 := by
      rw [← hkd]; exact real_inner_self_eq_norm_sq _
    rw [h]; exact pow_pos hvnorm 2
  have hev_pos : ∀ᶠ t in 𝓝 (1:ℝ), 0 < inner ℝ ((fderiv ℝ k t) 1) v :=
    (continuousAt_const (y := (0:ℝ))).eventually_lt
      (ContinuousAt.inner hev_cont continuousAt_const) hpos1
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hev_pos
  obtain ⟨ε₂, hε₂pos, hε₂sub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h1V)
  -- ## the functionals `ξ`, `η` and the straightening map `F`
  set ξ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := (inner ℝ v v)⁻¹ • innerSL ℝ v with hξdef
  have hξapp : ∀ z : EuclideanSpace ℝ (Fin n), ξ z = inner ℝ v z / inner ℝ v v := by
    intro z
    simp only [hξdef, smul_apply, smul_eq_mul, innerSL_apply_apply, div_eq_inv_mul]
  have hξv : ξ v = 1 := by rw [hξapp]; exact div_self hvvne
  set η : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.id ℝ _ - ξ.smulRight v with hηdef
  have hηapp : ∀ z, η z = z - ξ z • v := by
    intro z
    simp only [hηdef, sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply]
  set F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun y => k (1 + ξ (y - x₀)) + η (y - x₀) with hFdef
  have hFval : ∀ y, F y = k (1 + ξ (y - x₀)) + η (y - x₀) := fun y => rfl
  have hFq : F x₀ = x₀ := by
    show k (1 + ξ (x₀ - x₀)) + η (x₀ - x₀) = x₀
    simp [hk1]
  have hFline : ∀ t : ℝ, F (x₀ + (t - 1) • v) = k t := by
    intro t
    show k (1 + ξ (x₀ + (t - 1) • v - x₀)) + η (x₀ + (t - 1) • v - x₀) = k t
    have h1 : x₀ + (t - 1) • v - x₀ = (t - 1) • v := by abel
    rw [h1]
    have h2 : ξ ((t - 1) • v) = t - 1 := by
      rw [hξapp, real_inner_smul_right]
      field_simp
    have h3 : η ((t - 1) • v) = 0 := by
      rw [hηapp, h2, sub_self]
    rw [h2, h3, add_zero]
    congr 1
    ring
  -- ## the neighbourhood where `ξ` is small
  set δ : ℝ := min ε ε₂ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hεpos hε₂pos
  have hδle1 : δ ≤ ε := by rw [hδdef]; exact min_le_left _ _
  have hδle2 : δ ≤ ε₂ := by rw [hδdef]; exact min_le_right _ _
  have hevξ : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), |ξ z| < δ :=
    (ξ.continuous.continuousAt.abs).eventually_lt (continuousAt_const (y := δ))
      (by rw [map_zero, abs_zero]; exact hδpos)
  obtain ⟨κ, hκpos, hκsub⟩ := Metric.mem_nhds_iff.mp hevξ
  have hξbound : ∀ y ∈ Metric.ball x₀ κ, |ξ (y - x₀)| < δ := by
    intro y hy
    apply hκsub
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hVsmooth : ∀ y ∈ Metric.ball x₀ κ, 1 + ξ (y - x₀) ∈ V := by
    intro y hy
    apply hε₂sub
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]
    exact lt_of_lt_of_le (hξbound y hy) hδle2
  -- ## smoothness and derivative of `F` on the ball
  have hFsmooth : ∀ y ∈ Metric.ball x₀ κ, ContDiffAt ℝ smoothOrder F y := by
    intro y hy
    have hky : ContDiffAt ℝ smoothOrder k (1 + ξ (y - x₀)) :=
      hk.contDiffAt (hV.mem_nhds (hVsmooth y hy))
    show ContDiffAt ℝ smoothOrder (fun z : EuclideanSpace ℝ (Fin n) =>
      k (1 + ξ (z - x₀)) + η (z - x₀)) y
    exact ContDiffAt.add (ContDiffAt.comp y hky (by fun_prop)) (by fun_prop)
  set L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    fun y => ContinuousLinearMap.id ℝ _ +
      ξ.smulRight ((fderiv ℝ k (1 + ξ (y - x₀))) 1 - v) with hLdef
  have hLapp : ∀ y, L y = ContinuousLinearMap.id ℝ _ +
      ξ.smulRight ((fderiv ℝ k (1 + ξ (y - x₀))) 1 - v) := fun y => rfl
  have hcomp : ∀ (y z : EuclideanSpace ℝ (Fin n)),
      (fderiv ℝ k (1 + ξ (y - x₀))) (ξ z) = ξ z • ((fderiv ℝ k (1 + ξ (y - x₀))) 1) := by
    intro y z
    conv_lhs => rw [show ξ z = ξ z • (1 : ℝ) by simp]
    rw [map_smul]
  have hFderiv : ∀ y ∈ Metric.ball x₀ κ, HasFDerivAt F (L y) y := by
    intro y hy
    have hky : ContDiffAt ℝ smoothOrder k (1 + ξ (y - x₀)) :=
      hk.contDiffAt (hV.mem_nhds (hVsmooth y hy))
    have hd1 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => z - x₀)
        (ContinuousLinearMap.id ℝ _) y := (hasFDerivAt_id y).sub_const x₀
    have hd2 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => ξ (z - x₀)) ξ y := by
      have h := (ContinuousLinearMap.hasFDerivAt ξ).comp y hd1
      rw [ContinuousLinearMap.comp_id] at h
      exact h
    have hd3 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => 1 + ξ (z - x₀)) ξ y :=
      hd2.const_add 1
    have hd4 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => η (z - x₀)) η y := by
      have h := (ContinuousLinearMap.hasFDerivAt η).comp y hd1
      rw [ContinuousLinearMap.comp_id] at h
      exact h
    have hd5 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => k (1 + ξ (z - x₀)))
        (((fderiv ℝ k (1 + ξ (y - x₀))) : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n)).comp ξ) y :=
      (hky.differentiableAt hn0).hasFDerivAt.comp y hd3
    have hd6 : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) =>
        k (1 + ξ (z - x₀)) + η (z - x₀))
        (((fderiv ℝ k (1 + ξ (y - x₀))).comp ξ) + η) y := hd5.add hd4
    have hL_eq : ((fderiv ℝ k (1 + ξ (y - x₀))).comp ξ) + η = L y := by
      rw [hLapp y]
      refine ContinuousLinearMap.ext fun z => ?_
      simp only [add_apply, ContinuousLinearMap.comp_apply, sub_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, hηdef, smul_sub]
      rw [hcomp y z]
      abel
    rw [hL_eq] at hd6
    exact hd6
  have hLinj : ∀ y ∈ Metric.ball x₀ κ, Function.Injective (L y) := by
    intro y hy a b hab
    have hpos : 0 < inner ℝ ((fderiv ℝ k (1 + ξ (y - x₀))) 1) v := by
      apply hεsub
      rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left]
      exact lt_of_lt_of_le (hξbound y hy) hδle1
    have hLz : L y (a - b) = (a - b) +
        ξ (a - b) • ((fderiv ℝ k (1 + ξ (y - x₀))) 1 - v) := by
      rw [hLapp y]
      simp only [add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply]
    have h0 : L y (a - b) = 0 := by rw [map_sub, hab, sub_self]
    rw [hLz] at h0
    have hprod : ξ (a - b) * (1 + ξ ((fderiv ℝ k (1 + ξ (y - x₀))) 1 - v)) = 0 := by
      have h := congrArg ξ h0
      simp only [map_add, map_smul, map_zero, smul_eq_mul] at h
      rw [mul_add, mul_one]
      exact h
    have hne : (1:ℝ) + ξ ((fderiv ℝ k (1 + ξ (y - x₀))) 1 - v) ≠ 0 := by
      have hval : (1:ℝ) + ξ ((fderiv ℝ k (1 + ξ (y - x₀))) 1 - v)
          = inner ℝ ((fderiv ℝ k (1 + ξ (y - x₀))) 1) v / inner ℝ v v := by
        rw [map_sub, hξv, hξapp,
          real_inner_comm v ((fderiv ℝ k (1 + ξ (y - x₀))) 1)]
        ring
      rw [hval]
      exact div_ne_zero (ne_of_gt hpos) hvvne
    rcases mul_eq_zero.mp hprod with h2 | h2
    · rw [h2, zero_smul, add_zero] at h0
      exact sub_eq_zero.mp h0
    · exact absurd h2 hne
  -- ## the inverse function theorem at `x₀`
  have hx₀κ : x₀ ∈ Metric.ball x₀ κ := Metric.mem_ball_self hκpos
  have hLx₀ : L x₀ = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [hLapp x₀]
    have h1 : 1 + ξ (x₀ - x₀) = 1 := by simp
    have h2 : (fderiv ℝ k 1) 1 - v = 0 := by rw [hkd, sub_self]
    rw [h1, h2]
    simp
  have hderiv₀ : HasFDerivAt F ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)) :
      EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) : _ →L[ℝ] _) x₀ := by
    have h := hFderiv x₀ hx₀κ
    rw [hLx₀] at h
    simpa only [ContinuousLinearEquiv.coe_refl] using h
  have hcd₀ : ContDiffAt ℝ smoothOrder F x₀ := hFsmooth x₀ hx₀κ
  set Ψ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    ContDiffAt.toOpenPartialHomeomorph F hcd₀ hderiv₀ hn0 with hΨdef
  have hΨcoe : (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = F := by
    simp only [hΨdef, ContDiffAt.toOpenPartialHomeomorph_coe]
  have hx₀Ψ : x₀ ∈ Ψ.source := ContDiffAt.mem_toOpenPartialHomeomorph_source hcd₀ hderiv₀ hn0
  have hΨx₀ : Ψ x₀ = x₀ := by rw [hΨcoe]; exact hFq
  have hx₀Ψt : x₀ ∈ Ψ.target := by
    have h := Ψ.map_source hx₀Ψ
    rwa [hΨx₀] at h
  have hΨsx₀ : Ψ.symm x₀ = x₀ := by
    have h := Ψ.left_inv hx₀Ψ
    rwa [hΨx₀] at h
  -- ## restriction to a ball
  set Φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    Ψ.restrOpen (Metric.ball x₀ κ) Metric.isOpen_ball with hΦdef
  have hΦsrc : Φ.source = Ψ.source ∩ Metric.ball x₀ κ := by
    rw [hΦdef]; rfl
  have hΦtgt : Φ.target = Ψ.target ∩ Ψ.symm ⁻¹' Metric.ball x₀ κ := by
    rw [hΦdef]; rfl
  have hΦcoe : (Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) = F := by
    simp only [hΦdef, OpenPartialHomeomorph.coe_restrOpen, hΨcoe]
  have hΦsymm : ((Φ.symm : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      = Ψ.symm := by
    simp only [hΦdef, OpenPartialHomeomorph.coe_restrOpen_symm]
  have hΦsmooth : ∀ z ∈ Φ.source, ContDiffAt ℝ smoothOrder (↑Φ) z := by
    intro z hz
    rw [hΦsrc] at hz
    rw [hΦcoe]
    exact hFsmooth z hz.2
  have hΦsymmsmooth : ∀ y ∈ Φ.target, ContDiffAt ℝ smoothOrder (↑Φ.symm) y := by
    intro y hy
    rw [hΦtgt] at hy
    have hyΨ : y ∈ Ψ.target := hy.1
    have hyb : Ψ.symm y ∈ Metric.ball x₀ κ := hy.2
    have hinjf : Function.Injective (fderiv ℝ F (Ψ.symm y)) := by
      rw [(hFderiv (Ψ.symm y) hyb).fderiv]
      exact hLinj (Ψ.symm y) hyb
    obtain ⟨f', hf'⟩ := exists_continuousLinearEquiv_of_injective
      (rfl : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
      (fderiv ℝ F (Ψ.symm y)) hinjf
    have hLx : fderiv ℝ F (Ψ.symm y) = L (Ψ.symm y) := (hFderiv (Ψ.symm y) hyb).fderiv
    have hFd : HasFDerivAt F (↑f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (Ψ.symm y) := by
      refine (hFderiv (Ψ.symm y) hyb).congr_fderiv ?_
      rw [hf']
      exact hLx.symm
    have hFd' : HasFDerivAt (↑Ψ) (↑f' : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) (Ψ.symm y) := by
      rw [hΨcoe]; exact hFd
    have hΨsymm_cd : ContDiffAt ℝ smoothOrder (↑Ψ) (Ψ.symm y) := by
      rw [hΨcoe]; exact hFsmooth (Ψ.symm y) hyb
    have hres := Ψ.contDiffAt_symm (f₀' := f') hyΨ hFd' hΨsymm_cd
    rw [hΦsymm]
    exact hres
  have hΦx₀ : Φ x₀ = x₀ := by rw [hΦcoe]; exact hFq
  have hΦsx₀ : Φ.symm x₀ = x₀ := by rw [hΦsymm]; exact hΨsx₀
  -- ## the radius of the germ
  obtain ⟨η₁, hη₁pos, hη₁sub⟩ := Metric.mem_nhds_iff.mp (Ψ.open_source.mem_nhds hx₀Ψ)
  obtain ⟨η₂, hη₂pos, hη₂sub⟩ := Metric.mem_nhds_iff.mp (Ψ.open_target.mem_nhds hx₀Ψt)
  set c₀ : ℝ := ‖v‖ + 1 with hc₀def
  have hc₀pos : 0 < c₀ := by rw [hc₀def]; positivity
  set m : ℝ := min η₁ (min η₂ κ) with hmdef
  have hmpos : 0 < m := by rw [hmdef]; exact lt_min hη₁pos (lt_min hη₂pos hκpos)
  have hmle1 : m ≤ η₁ := by rw [hmdef]; exact min_le_left _ _
  have hmle2 : m ≤ η₂ := by
    rw [hmdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmle3 : m ≤ κ := by
    rw [hmdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  set ρ : ℝ := m / c₀ with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact div_pos hmpos hc₀pos
  have hρm : ρ * c₀ = m := by
    rw [hρdef]; exact div_mul_cancel₀ m (ne_of_gt hc₀pos)
  have hline_mem : ∀ s : ℝ, |s| ≤ ρ → x₀ + s • v ∈ Metric.ball x₀ m := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖x₀ + s • v - x₀‖ = |s| * ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rw [hnorm]
    have h1 : |s| * ‖v‖ ≤ ρ * ‖v‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg v)
    have h2 : ρ * ‖v‖ < ρ * c₀ := by
      apply mul_lt_mul_of_pos_left _ hρpos
      rw [hc₀def]; linarith
    rw [hρm] at h2
    linarith
  have hsrc_rad : ∀ s : ℝ, |s| ≤ ρ → x₀ + s • v ∈ Ψ.source :=
    fun s hs => hη₁sub (Metric.ball_subset_ball hmle1 (hline_mem s hs))
  have htgt_rad : ∀ s : ℝ, |s| ≤ ρ → x₀ + s • v ∈ Ψ.target :=
    fun s hs => hη₂sub (Metric.ball_subset_ball hmle2 (hline_mem s hs))
  have hball_rad : ∀ s : ℝ, |s| ≤ ρ → x₀ + s • v ∈ Metric.ball x₀ κ :=
    fun s hs => Metric.ball_subset_ball hmle3 (hline_mem s hs)
  refine ⟨Φ, ρ, hρpos, hΦsmooth, hΦsymmsmooth, hΦx₀, hΦsx₀, ?_⟩
  intro t ht
  have hkey : Ψ.symm (k t) = x₀ + (t - 1) • v := by
    rw [← hFline t]
    have h2 := Ψ.left_inv (hsrc_rad (t - 1) ht)
    rwa [hΨcoe] at h2
  refine ⟨?_, ?_⟩
  · rw [hΦtgt]
    refine ⟨?_, ?_⟩
    · have h := Ψ.map_source (hsrc_rad (t - 1) ht)
      rwa [hΨcoe, hFline t] at h
    · rw [Set.mem_preimage, hkey]
      exact hball_rad (t - 1) ht
  · rw [hΦsymm]
    exact hkey

/-- **Straightening the germ of a smooth immersed curve.**  If `α : ℝ → M` is a `C^∞` curve in an
`n`-manifold whose derivative at `1` is injective, then near `t = 1` the curve is straight in a
suitable chart: there are a chart `c'` at `α 1`, a direction `w ≠ 0` and `e > 0` with
`c' (α t) = c' (α 1) + (t - 1) • w` for `1 - e ≤ t ≤ 1`.

The proof straightens the chart expression `h = chartAt (α 1) ∘ α` of `α` by the local inverse
function theorem: the map `F y = h (1 + ξ (y - x₀)) + η (y - x₀)` (where `ξ` is the covector
`⟨v, ·⟩/⟨v, v⟩` and `η = id - ξ ⊗ v` is the projection along `v`) sends the line
`t ↦ x₀ + (t - 1) • v` to the curve, and its local inverse (restricted to a small ball) is the
straightening chart. -/
theorem exists_straightened_chart {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M]
    {α : ℝ → M} (hα : ContMDiff MCreal (MC n) smoothOrder α)
    (himm : Function.Injective (mfderiv MCreal (MC n) α 1)) :
    ∃ (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e ∧ w ≠ 0 ∧
      c' ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ α 1 ∈ c'.source ∧
      ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 →
        α t ∈ c'.source ∧ c' (α t) = c' (α 1) + (t - 1) • w := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  set q : M := α 1 with hqdef
  set cq : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) q with hcqdef
  have hcqsrc : q ∈ cq.source := mem_chart_source _ q
  have hcqmax : cq ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas q
  have hcqc : ContMDiffOn (MC n) (MC n) smoothOrder (↑cq) cq.source :=
    contMDiffOn_of_mem_maximalAtlas hcqmax
  have hcqs : ContMDiffOn (MC n) (MC n) smoothOrder (↑cq.symm) cq.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hcqmax
  set h : ℝ → EuclideanSpace ℝ (Fin n) := fun t => cq (α t) with hhdef
  have hh1 : h 1 = cq q := rfl
  have hVopen : IsOpen {t : ℝ | α t ∈ cq.source} :=
    IsOpen.preimage hα.continuous cq.open_source
  have h1V : (1:ℝ) ∈ {t : ℝ | α t ∈ cq.source} := hcqsrc
  have hhcdon : ContDiffOn ℝ smoothOrder h {t : ℝ | α t ∈ cq.source} := by
    have h1 : ContMDiffOn MCreal (MC n) smoothOrder (fun t : ℝ => cq (α t))
        {t : ℝ | α t ∈ cq.source} :=
      hcqc.comp (hα.contMDiffOn.mono (subset_univ _)) (fun t ht => ht)
    exact contMDiffOn_iff_contDiffOn.mp (by simpa only [hhdef] using h1)
  set v : EuclideanSpace ℝ (Fin n) := (fderiv ℝ h 1) 1 with hvdef
  have hcur_inj : Function.Injective (mfderiv MCreal (MC n) (fun t : ℝ => cq (α t)) 1) := by
    have hcq_md : MDifferentiableAt (MC n) (MC n) (↑cq : M → EuclideanSpace ℝ (Fin n)) q :=
      (hcqc.contMDiffAt (cq.open_source.mem_nhds hcqsrc)).mdifferentiableAt hn0
    have hα_md : MDifferentiableAt MCreal (MC n) α 1 := hα.contMDiffAt.mdifferentiableAt hn0
    have hcomp := mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MC n)
      (f := α) (g := (↑cq : M → EuclideanSpace ℝ (Fin n))) 1 hcq_md hα_md
    rw [show (fun t : ℝ => cq (α t)) = (↑cq : M → EuclideanSpace ℝ (Fin n)) ∘ α from rfl, hcomp]
    intro a b hab
    simp only [ContinuousLinearMap.comp_apply] at hab
    exact himm (isLocalDiffeomorphAt_chart_mfderiv_injective hcqmax hcqsrc hab)
  have hvne : v ≠ 0 := by
    have hf_inj : Function.Injective (fderiv ℝ h 1) := by
      have hh := hcur_inj
      rw [mfderiv_eq_fderiv, ← hhdef] at hh
      exact hh
    rw [hvdef]
    intro h0
    have h1 : (1:ℝ) = 0 := hf_inj (by rw [h0, map_zero])
    exact absurd h1 (one_ne_zero : (1:ℝ) ≠ 0)
  obtain ⟨Φ, ρ, hρpos, hΦsm, hΦsm', hΦx₀, hΦsx₀, hΦgerm⟩ :=
    exists_straightening hVopen h1V hhcdon hh1 hvdef.symm hvne
  set c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) := cq ≫ₕ Φ.symm with hc'def
  have hc'src : c'.source = cq.source ∩ ↑cq ⁻¹' Φ.target := by
    rw [hc'def, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  have hc'tgt : c'.target = Φ.source ∩ ↑Φ ⁻¹' cq.target := by
    rw [hc'def, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.symm_target]
  have hc'max : c' ∈ IsManifold.maximalAtlas (MC n) smoothOrder M := by
    rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
    constructor
    · rw [hc'src]
      have h1 : ContMDiffOn (MC n) (MC n) smoothOrder (↑Φ.symm) Φ.target :=
        fun z hz => contMDiffWithinAt_iff_contDiffWithinAt.mpr (hΦsm' z hz).contDiffWithinAt
      have h2 := h1.comp (hcqc.mono inter_subset_left) (fun x hx => hx.2)
      simpa only [hc'def, OpenPartialHomeomorph.coe_trans] using h2
    · rw [hc'tgt]
      have h1 : ContMDiffOn (MC n) (MC n) smoothOrder (↑Φ) Φ.source :=
        fun z hz => contMDiffWithinAt_iff_contDiffWithinAt.mpr (hΦsm z hz).contDiffWithinAt
      have h2 := hcqs.comp (h1.mono inter_subset_left) (fun x hx => hx.2)
      simpa only [hc'def, OpenPartialHomeomorph.coe_trans_symm,
        OpenPartialHomeomorph.symm_symm] using h2
  obtain ⟨ε₂, hε₂pos, hε₂sub⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds h1V)
  refine ⟨c', v, min ρ (ε₂ / 2), lt_min hρpos (by positivity), hvne, hc'max, ?_, ?_⟩
  · rw [hc'src]
    refine ⟨hcqsrc, ?_⟩
    rw [Set.mem_preimage]
    exact (hΦgerm 1 (by rw [sub_self, abs_zero]; exact hρpos.le)).1
  · intro t ht1 ht2
    have htm : |t - 1| ≤ min ρ (ε₂ / 2) := by
      rw [abs_of_nonpos (by linarith : t - 1 ≤ 0)]
      linarith
    have htρ : |t - 1| ≤ ρ := le_trans htm (min_le_left _ _)
    have htd : dist t 1 < ε₂ := by
      rw [Real.dist_eq]
      have h := le_trans htm (min_le_right ρ (ε₂ / 2))
      linarith
    have hsrc : α t ∈ cq.source := hε₂sub (Metric.mem_ball.mpr htd)
    obtain ⟨hΦt, hΦs⟩ := hΦgerm t htρ
    refine ⟨?_, ?_⟩
    · rw [hc'src]
      exact ⟨hsrc, hΦt⟩
    · have h1 : c' (α t) = cq q + (t - 1) • v := by
        show Φ.symm (cq (α t)) = cq q + (t - 1) • v
        exact hΦs
      have h2 : c' (α 1) = cq q := by
        show Φ.symm (cq (α 1)) = cq q
        exact hΦsx₀
      rw [h1, h2]





theorem immersedArcWithGerm {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {W : Set M} (hW : IsOpen W) (hWc : IsPreconnected W)
    {p q : M} (hp : p ∈ W) (hq : q ∈ W) (hpq : p ≠ q)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M)
    (hpc : p ∈ c.source) {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0)
    (hger : ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t ≤ e →
      c.symm (c p + t • v) ∈ W) :
    ∃ α : ℝ → M, α 0 = p ∧ α 1 = q ∧
      ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder α ∧
      (∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) α t)) ∧
      Set.InjOn α (Set.Icc (0 : ℝ) 1) ∧
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → α t ∈ W) ∧
      (∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 ≤ t → t ≤ e → α t = c.symm (c p + t • v)) ∧
      ∃ (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (w : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e ∧ w ≠ 0 ∧
        c' ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
          Work.Noncompact.CompressionTube.smoothOrder M ∧ q ∈ c'.source ∧
        ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → α t = c'.symm (c' q + (t - 1) • w) := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  obtain ⟨e_h, he_h_pos, hger'⟩ := hger
  have hc_s : ContMDiffOn (MC n) (MC n) smoothOrder c.symm c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hc
  have hcp : c p ∈ c.target := c.map_source hpc
  obtain ⟨ρ₀, hρ₀pos, hρ₀sub⟩ := Metric.isOpen_iff.mp c.open_target (c p) hcp
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set ρv : ℝ := ρ₀ / ‖v‖ with hρvdef
  have hρvρ : ρv * ‖v‖ = ρ₀ := by rw [hρvdef]; field_simp
  have hchart : ∀ t : ℝ, |t| < ρv → c p + t • v ∈ c.target := by
    intro t ht
    apply hρ₀sub
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show c p + t • v - c p = t • v from by abel, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖v‖ < ρv * ‖v‖ := by nlinarith [abs_nonneg t]
      _ = ρ₀ := hρvρ
  -- ## `q` is not on the germ line near `0`
  have hcontL : ContinuousAt (fun t : ℝ => c.symm (c p + t • v)) 0 := by
    have h1 : ContinuousAt (fun t : ℝ => c p + t • v) 0 := by fun_prop
    exact ContinuousAt.comp (g := c.symm) (f := fun t : ℝ => c p + t • v) (x := 0)
      (c.continuousOn_symm.continuousAt
        (c.open_target.mem_nhds (by simpa using hcp))) h1
  have hqmem : ({q}ᶜ : Set M) ∈ 𝓝 (c.symm (c p + (0:ℝ) • v)) := by
    have hpt : c.symm (c p + (0:ℝ) • v) = p := by rw [zero_smul, add_zero, c.left_inv hpc]
    rw [hpt]
    exact isClosed_singleton.isOpen_compl.mem_nhds (by simpa [Set.mem_compl_iff] using hpq)
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.mem_nhds_iff.mp (hcontL hqmem)
  have hε₁' : ∀ t : ℝ, |t| < ε₁ → c.symm (c p + t • v) ≠ q := by
    intro t ht
    have h := hε₁ (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact ht)
    simpa [Set.mem_compl_iff] using h
  -- ## the bump constant and the seed arc
  obtain ⟨κ, hκpos, hκspec⟩ := exists_isBumpConst (n := n) (M := M)
  obtain ⟨e₀, he₀pos, he₀h, he₀δ, hgermW, A, hAcd, hA0, hAimm, hAinj, hAimg, hAgerm,
    hgermtgt, hA1not, hAterm⟩ := exists_germ_arc hn hW hp c hc hpc hv ⟨e_h, he_h_pos, hger'⟩ hε₁pos
  -- ## the initial germ arc, as a closed set to be removed from `W`
  have hσcont : Continuous (fun s : ℝ => max 0 (min 1 s)) :=
    continuous_const.max (continuous_const.min continuous_id)
  let σ : ℝ → ℝ := fun s => max 0 (min 1 s)
  have hσval : ∀ s : ℝ, σ s = max 0 (min 1 s) := fun s => rfl
  have hσ1 : ∀ s ∈ Set.Icc (0:ℝ) 1, σ s = s := by
    intro s hs
    show max 0 (min 1 s) = s
    rw [min_eq_right hs.2, max_eq_right hs.1]
  have hσmem : ∀ s : ℝ, σ s ∈ Set.Icc (0:ℝ) 1 := fun s =>
    ⟨le_max_left 0 _, max_le (by norm_num) (min_le_left 1 s)⟩
  let η : ℝ → M := fun s => c.symm (c p + (σ s) • (e₀ • v))
  have hηval : ∀ s : ℝ, η s = c.symm (c p + (σ s) • (e₀ • v)) := fun s => rfl
  have hηtgt : ∀ s : ℝ, c p + (σ s) • (e₀ • v) ∈ c.target := by
    intro s
    rw [smul_smul]
    exact hgermtgt (σ s * e₀) ⟨mul_nonneg (hσmem s).1 he₀pos.le,
      by nlinarith [(hσmem s).2, he₀pos]⟩
  have hηcont : Continuous η := by
    have hinner : Continuous (fun s : ℝ => c p + (σ s) • (e₀ • v)) := by
      have : Continuous (fun s : ℝ => σ s) := hσcont
      fun_prop
    exact c.continuousOn_symm.comp_continuous hinner hηtgt
  have hηinj : Set.InjOn η (Set.Icc (0:ℝ) 1) := by
    intro s hs t ht hst
    have hinj : Set.InjOn c.symm c.target := by
      have h := c.symm.injOn
      rwa [OpenPartialHomeomorph.symm_source] at h
    have h2 := hinj (hηtgt s) (hηtgt t) hst
    have h3 : (σ s - σ t) • (e₀ • v) = 0 := by rw [sub_smul, add_left_cancel h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · rw [hσ1 s hs, hσ1 t ht] at h
      exact sub_eq_zero.mp h
    · exact absurd h (smul_ne_zero he₀pos.ne' hv)
  have hηW : ∀ t ∈ Set.Icc (0:ℝ) 1, η t ∈ W := by
    intro s hs
    rw [hηval s, hσ1 s hs]
    exact hgermW s hs
  have hGcl : IsClosed (η '' Set.Icc (0:ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hηcont.continuousOn).isClosed
  have hUopen : IsOpen (W \ η '' Set.Icc (0:ℝ) 1) := by
    simpa [Set.diff_eq] using hW.inter hGcl.isOpen_compl
  have hUpc : IsPreconnected (W \ η '' Set.Icc (0:ℝ) 1) :=
    sdiff_arc_isPreconnected hn hW hWc hηcont hηinj hηW
  -- a germ-carrying arc never ends inside the germ window
  have hnotG : ∀ (α : ℝ → M), (∀ t ∈ Set.Icc (0:ℝ) e₀, α t = c.symm (c p + t • v)) →
      Set.InjOn α (Set.Icc (0:ℝ) 1) → α 1 ∉ η '' Set.Icc (0:ℝ) 1 := by
    intro α hαg hαinj hmem
    rcases hmem with ⟨s, hs, hse⟩
    have hηs : η s = c.symm (c p + s • (e₀ • v)) := by rw [hηval s, hσ1 s hs]
    have hse₀ : s * e₀ ∈ Set.Icc (0:ℝ) e₀ :=
      ⟨mul_nonneg hs.1 he₀pos.le, by nlinarith [hs.2, he₀pos]⟩
    have h1 : α 1 = α (s * e₀) := by
      rw [← hse, hηs, smul_smul, hαg (s * e₀) hse₀]
    have h2 : (1:ℝ) = s * e₀ :=
      hαinj (by norm_num) ⟨mul_nonneg hs.1 he₀pos.le, by nlinarith [hs.2, he₀pos, he₀h]⟩ h1
    nlinarith [h2, he₀h, he₀pos, hs.2]
  -- ## the set of reachable points
  set S : Set M := {z | ∃ α : ℝ → M,
      ContMDiff MCreal (MC n) smoothOrder α ∧ α 0 = p ∧ α 1 = z ∧
      (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) α t)) ∧
      Set.InjOn α (Set.Icc (0:ℝ) 1) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, α t ∈ W) ∧
      (∀ t ∈ Set.Icc (0:ℝ) e₀, α t = c.symm (c p + t • v))} with hSdef
  have hseedU : A 1 ∈ W \ η '' Set.Icc (0:ℝ) 1 :=
    ⟨hAimg 1 (by norm_num), hnotG A hAgerm hAinj⟩
  have hseed : A 1 ∈ S := by
    rw [hSdef]
    exact ⟨A, hAcd, hA0, rfl, hAimm, hAinj, hAimg, hAgerm⟩
  -- ## `S` is open
  have hSopen : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro z hz
    rw [hSdef] at hz
    obtain ⟨α, hαcd, hα0, hα1, hαimm, hαinj, hαimg, hαgerm⟩ := hz
    have hzW : z ∈ W := hα1 ▸ hαimg 1 (by norm_num)
    have hznotG : z ∉ η '' Set.Icc (0:ℝ) 1 := hα1 ▸ hnotG α hαgerm hαinj
    set cz : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
      chartAt (EuclideanSpace ℝ (Fin n)) z with hczdef
    have hzsrc : z ∈ cz.source := mem_chart_source _ z
    have hczc : ContMDiffOn (MC n) (MC n) smoothOrder cz cz.source := contMDiffOn_chart
    have hczs : ContMDiffOn (MC n) (MC n) smoothOrder cz.symm cz.target := contMDiffOn_chart_symm
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp cz.open_target (cz z) (cz.map_source hzsrc)
    have hcont : ContinuousAt cz.symm (cz z) :=
      cz.continuousOn_symm.continuousAt (cz.open_target.mem_nhds (cz.map_source hzsrc))
    have hmemz : cz.symm (cz z) ∈ W \ η '' Set.Icc (0:ℝ) 1 := by
      rw [cz.left_inv hzsrc]; exact ⟨hzW, hznotG⟩
    obtain ⟨ρ₂, hρ₂pos, hρ₂sub⟩ :=
      Metric.mem_nhds_iff.mp (hcont.preimage_mem_nhds (hUopen.mem_nhds hmemz))
    have hρ₂img : cz.symm '' Metric.ball (cz z) ρ₂ ⊆ W \ η '' Set.Icc (0:ℝ) 1 := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hρ₂sub hy
    set R : ℝ := min (ρ / 2) ρ₂ with hRdef
    have hRpos : 0 < R := lt_min (by linarith) hρ₂pos
    have hRleρ : R ≤ ρ / 2 := min_le_left _ _
    have hRleρ₂ : R ≤ ρ₂ := min_le_right _ _
    have hRclosed : Metric.closedBall (cz (α 1)) R ⊆ cz.target := by
      rw [hα1]
      exact Subset.trans (Metric.closedBall_subset_ball (by linarith [hRleρ])) hρsub
    have hRG : cz.symm '' Metric.ball (cz (α 1)) R ⊆ W \ η '' Set.Icc (0:ℝ) 1 := by
      rw [hα1]
      exact Subset.trans (Set.image_mono (Metric.ball_subset_ball hRleρ₂)) hρ₂img
    have hRW : cz.symm '' Metric.ball (cz (α 1)) R ⊆ W := fun x hx => (hRG hx).1
    have hRavoid : ∀ t ∈ Set.Icc (0:ℝ) e₀, α t ∉ cz.symm '' Metric.ball (cz (α 1)) R := by
      intro t ht hmem
      have htI : t / e₀ ∈ Set.Icc (0:ℝ) 1 :=
        ⟨div_nonneg ht.1 he₀pos.le, by rw [div_le_one he₀pos]; exact ht.2⟩
      have hαt : α t = η (t / e₀) := by
        rw [hαgerm t ht, hηval (t / e₀), hσ1 (t / e₀) htI, smul_smul,
          div_mul_cancel₀ t he₀pos.ne']
      exact (hRG hmem).2 ⟨t / e₀, htI, hαt.symm⟩
    refine ⟨cz.symm '' (Metric.ball (cz z) (κ * R) ∩ cz.target), ?_, ?_, ?_⟩
    · rintro z' ⟨u, hu, rfl⟩
      have hutgt : u ∈ cz.target := hu.2
      have hz'src : cz.symm u ∈ cz.source := cz.map_target hutgt
      have hdist : ‖cz (cz.symm u) - cz (α 1)‖ < κ * R := by
        rw [cz.right_inv hutgt, hα1]
        exact Metric.mem_ball.mp hu.1
      have hα1src : α 1 ∈ cz.source := by rw [hα1]; exact hzsrc
      obtain ⟨α', hα'cd, hα'0, hα'1, hα'imm, hα'inj, hα'img, hα'germ⟩ :=
        bump_step he₀pos hκspec hαcd hα0 hαimm hαinj hαimg hαgerm hczc hczs hα1src hRpos
          hRclosed hRW hRavoid hz'src hdist
      rw [hSdef]
      exact ⟨α', hα'cd, hα'0, hα'1, hα'imm, hα'inj, hα'img, hα'germ⟩
    · exact cz.isOpen_image_symm_of_subset_target (Metric.isOpen_ball.inter cz.open_target)
        (fun x hx => hx.2)
    · exact ⟨cz z, ⟨Metric.mem_ball_self (mul_pos hκpos hRpos), cz.map_source hzsrc⟩,
        cz.left_inv hzsrc⟩
  -- ## `S` is closed inside `W` minus the germ window
  have hScl : closure S ∩ (W \ η '' Set.Icc (0:ℝ) 1) ⊆ S := by
    rintro r ⟨hrcl, hrW, hrnotG⟩
    set cr : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
      chartAt (EuclideanSpace ℝ (Fin n)) r with hcrdef
    have hrsrc : r ∈ cr.source := mem_chart_source _ r
    have hcrc : ContMDiffOn (MC n) (MC n) smoothOrder cr cr.source := contMDiffOn_chart
    have hcrs : ContMDiffOn (MC n) (MC n) smoothOrder cr.symm cr.target := contMDiffOn_chart_symm
    obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp cr.open_target (cr r) (cr.map_source hrsrc)
    have hcont : ContinuousAt cr.symm (cr r) :=
      cr.continuousOn_symm.continuousAt (cr.open_target.mem_nhds (cr.map_source hrsrc))
    have hmemr : cr.symm (cr r) ∈ W \ η '' Set.Icc (0:ℝ) 1 := by
      rw [cr.left_inv hrsrc]; exact ⟨hrW, hrnotG⟩
    obtain ⟨ρ₂, hρ₂pos, hρ₂sub⟩ :=
      Metric.mem_nhds_iff.mp (hcont.preimage_mem_nhds (hUopen.mem_nhds hmemr))
    have hρ₂img : cr.symm '' Metric.ball (cr r) ρ₂ ⊆ W \ η '' Set.Icc (0:ℝ) 1 := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hρ₂sub hy
    set R : ℝ := min (ρ / 2) ρ₂ with hRdef
    have hRpos : 0 < R := lt_min (by linarith) hρ₂pos
    have hRleρ : R ≤ ρ / 2 := min_le_left _ _
    have hRleρ₂ : R ≤ ρ₂ := min_le_right _ _
    have hRball : Metric.closedBall (cr r) R ⊆ cr.target :=
      Subset.trans (Metric.closedBall_subset_ball (by linarith [hRleρ])) hρsub
    have hRG : cr.symm '' Metric.ball (cr r) R ⊆ W \ η '' Set.Icc (0:ℝ) 1 :=
      Subset.trans (Set.image_mono (Metric.ball_subset_ball hRleρ₂)) hρ₂img
    set δ : ℝ := min (R / 4) (κ * (R / 4)) / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]
      exact div_pos (lt_min (by linarith) (mul_pos hκpos (by linarith))) (by norm_num)
    have hδR : δ ≤ R / 4 := by
      rw [hδdef]
      have h1 : min (R / 4) (κ * (R / 4)) ≤ R / 4 := min_le_left _ _
      linarith
    have hδκ : δ < κ * (R / 2) := by
      rw [hδdef]
      have h1 : min (R / 4) (κ * (R / 4)) ≤ κ * (R / 4) := min_le_right _ _
      have h2 : 0 < κ * (R / 4) := mul_pos hκpos (by linarith)
      linarith
    have hballtarget : Metric.ball (cr r) δ ⊆ cr.target :=
      Subset.trans Metric.ball_subset_closedBall
        (Subset.trans (Metric.closedBall_subset_closedBall (le_trans hδR (by linarith))) hRball)
    have hballopen : IsOpen (cr.symm '' Metric.ball (cr r) δ) :=
      cr.isOpen_image_symm_of_subset_target Metric.isOpen_ball hballtarget
    have hrball : r ∈ cr.symm '' Metric.ball (cr r) δ :=
      ⟨cr r, Metric.mem_ball_self hδpos, cr.left_inv hrsrc⟩
    obtain ⟨u, hu_ball, hu_S⟩ := (mem_closure_iff_nhds.mp hrcl) _ (hballopen.mem_nhds hrball)
    obtain ⟨v', hv'ball, hvu⟩ := hu_ball
    have hv'tgt : v' ∈ cr.target :=
      hballtarget (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hv'ball) (by linarith)))
    have hu_src : u ∈ cr.source := hvu ▸ cr.map_target hv'tgt
    have hcu : cr u = v' := by rw [← hvu, cr.right_inv hv'tgt]
    rw [hSdef] at hu_S
    obtain ⟨α, hαcd, hα0, hα1, hαimm, hαinj, hαimg, hαgerm⟩ := hu_S
    have hdu : dist v' (cr r) < δ := Metric.mem_ball.mp hv'ball
    have hRclosed : Metric.closedBall (cr (α 1)) (R / 2) ⊆ cr.target := by
      rw [hα1, hcu]
      refine Subset.trans ?_ hRball
      intro x hx
      rw [Metric.mem_closedBall] at hx ⊢
      calc dist x (cr r) ≤ dist x v' + dist v' (cr r) := dist_triangle _ _ _
        _ ≤ R / 2 + δ := add_le_add hx (le_of_lt hdu)
        _ ≤ R := by linarith [hδR]
    have hballsub : Metric.ball (cr (α 1)) (R / 2) ⊆ Metric.ball (cr r) R := by
      rw [hα1, hcu]
      intro y hy
      rw [Metric.mem_ball] at hy ⊢
      calc dist y (cr r) ≤ dist y v' + dist v' (cr r) := dist_triangle _ _ _
        _ < R / 2 + δ := add_lt_add hy hdu
        _ ≤ R := by linarith [hδR]
    have hRW : cr.symm '' Metric.ball (cr (α 1)) (R / 2) ⊆ W :=
      fun x hx => (hRG (Set.image_mono hballsub hx)).1
    have hRavoid : ∀ t ∈ Set.Icc (0:ℝ) e₀, α t ∉ cr.symm '' Metric.ball (cr (α 1)) (R / 2) := by
      intro t ht hmem
      have htI : t / e₀ ∈ Set.Icc (0:ℝ) 1 :=
        ⟨div_nonneg ht.1 he₀pos.le, by rw [div_le_one he₀pos]; exact ht.2⟩
      have hαt : α t = η (t / e₀) := by
        rw [hαgerm t ht, hηval (t / e₀), hσ1 (t / e₀) htI, smul_smul,
          div_mul_cancel₀ t he₀pos.ne']
      exact (hRG (Set.image_mono hballsub hmem)).2 ⟨t / e₀, htI, hαt.symm⟩
    have hdist_r : ‖cr r - cr (α 1)‖ < κ * (R / 2) := by
      rw [hα1, hcu, norm_sub_rev]
      rw [dist_eq_norm] at hdu
      linarith [hδκ]
    have hα1src : α 1 ∈ cr.source := by rw [hα1]; exact hu_src
    obtain ⟨α', hα'cd, hα'0, hα'1, hα'imm, hα'inj, hα'img, hα'germ⟩ :=
      bump_step (R := R / 2) he₀pos hκspec hαcd hα0 hαimm hαinj hαimg hαgerm hcrc hcrs
        hα1src (by linarith) hRclosed hRW hRavoid hrsrc hdist_r
    rw [hSdef]
    exact ⟨α', hα'cd, hα'0, hα'1, hα'imm, hα'inj, hα'img, hα'germ⟩
  -- ## conclusion
  have hsub : W \ η '' Set.Icc (0:ℝ) 1 ⊆ S :=
    hUpc.subset_of_closure_inter_subset hSopen ⟨A 1, hseedU, hseed⟩ hScl
  have hqU : q ∈ W \ η '' Set.Icc (0:ℝ) 1 := by
    refine ⟨hq, ?_⟩
    rintro ⟨s, hs, hse⟩
    have hηs : η s = c.symm (c p + s • (e₀ • v)) := by rw [hηval s, hσ1 s hs]
    have hst : |s * e₀| < ε₁ := by
      rw [abs_of_nonneg (mul_nonneg hs.1 he₀pos.le)]
      nlinarith [hs.2, he₀δ, hε₁pos]
    have hne : c.symm (c p + (s * e₀) • v) ≠ q := hε₁' (s * e₀) hst
    rw [hηs, smul_smul] at hse
    exact hne hse
  have hqS : q ∈ S := hsub hqU
  rw [hSdef, Set.mem_setOf_eq] at hqS
  obtain ⟨α, hαcd, hα0, hα1, hαimm, hαinj, hαimg, hαgerm⟩ := hqS
  obtain ⟨c', w, e, hepos, hwne, hc'max, hqsrc, hterm⟩ :=
    exists_straightened_chart hαcd (hαimm 1)
  refine ⟨α, hα0, hα1, hαcd, hαimm, hαinj, hαimg,
    ⟨e₀, he₀pos, fun t ht0 ht1 => hαgerm t ⟨ht0, ht1⟩⟩,
    c', w, e, hepos, hwne, hc'max, hα1 ▸ hqsrc, ?_⟩
  intro t ht1 ht2
  obtain ⟨hsrc, heq⟩ := hterm t ht1 ht2
  rw [hα1] at heq
  rw [← heq, c'.left_inv hsrc]

end Work.Noncompact.CompressionTube
