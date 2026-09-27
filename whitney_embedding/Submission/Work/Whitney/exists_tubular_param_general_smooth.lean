import Mathlib
import Submission.Work.Whitney.exists_tubular_param

/-!
# The `C^∞` (smooth) form of the tubular-parametrisation lemma

`Work.Whitney.exists_tubular_param_general` states the straightening lemma for *analytic* maps
(`ContDiff ℝ ⊤`, where `⊤ : WithTop ℕ∞` means analyticity in this Mathlib).  Here we record the
same statement for `C^∞` maps, i.e. `ContDiff ℝ ∞` with `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, as needed
for the smooth (non-analytic) chart representations used in the Whitney development.

The construction and proof are those of the analytic version: choose a continuous linear
equivalence `T : E × E ≃L ℝ × ℝ` whose restriction to `E × {0}` is `L = fderiv ℝ φ 0`, and put
`H = T ∘ ψ` where `ψ = id + G` is a perturbation of the identity.  The only ingredient whose
regularity level matters is the perturbation lemma, re-proved here for `C^∞` (the analytic proof
of it is order-agnostic; we simply repeat it at order `∞`).

-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology Metric

/-- A smooth map `ψ` which is a "small perturbation of the identity at `0`"
(namely `ψ z = z + G z` with `G` smooth and `fderiv ℝ G 0 = 0`) is injective on a
small ball around `0`, and its Fréchet derivative is injective at every point of
that ball.  This is the `C^∞` counterpart of
`Work.Whitney.exists_injOn_ball_of_perturbation`. -/
private theorem exists_injOn_ball_of_perturbation_smooth
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ψ G : F → F) (hψ : ∀ z, ψ z = z + G z)
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (hG0 : fderiv ℝ G 0 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Set.InjOn ψ (Metric.ball 0 ρ) ∧
      ∀ z ∈ Metric.ball 0 ρ, Function.Injective (fderiv ℝ ψ z) := by
  -- `fderiv G` is continuous, and vanishes at `0`, hence is small on a small ball.
  have hcont : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by simp)
  have hGdiff : Differentiable ℝ G := hG.differentiable (by simp)
  have hmem : {z : F | fderiv ℝ G z ∈ ball (0 : F →L[ℝ] F) (1 / 2)} ∈ 𝓝 (0 : F) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [hG0]; exact ball_mem_nhds 0 (by norm_num))
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨ρ, hρpos, ?_, ?_⟩
  · -- Injectivity of `ψ` on the ball: it is a `1/2`-Lipschitz perturbation of the identity.
    intro x hx y hy hxy
    have h1 : x + G x = y + G y := by simpa [hψ x, hψ y] using hxy
    have h2 : x - y = G y - G x := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm (G y) y]; exact h1
    -- Mean value inequality: `G` is `1/2`-Lipschitz on the ball.
    have hxy2 : ‖x - y‖ ≤ (1 / 2) * ‖y - x‖ := by
      have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le
        (s := ball 0 ρ) (f := G) (C := 1 / 2)
        (fun z _ => hGdiff z)
        (fun z hz => by
          have hz' : fderiv ℝ G z ∈ ball (0 : F →L[ℝ] F) (1 / 2) := hρsub hz
          rw [Metric.mem_ball] at hz'
          exact le_of_lt (by simpa [dist_eq_norm] using hz'))
        (convex_ball 0 ρ) hx hy
      calc ‖x - y‖ = ‖G y - G x‖ := by rw [h2]
        _ ≤ 1 / 2 * ‖y - x‖ := hmvt
    have hnorm : ‖x - y‖ = 0 := by
      have hyx : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
      nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · -- Injectivity of the differential: `fderiv ψ z = id + fderiv G z` with `‖fderiv G z‖ < 1`.
    intro z hz
    have hfdz : fderiv ℝ ψ z = ContinuousLinearMap.id ℝ F + fderiv ℝ G z := by
      have hψeq : ψ = id + G := by funext w; exact hψ w
      rw [hψeq, fderiv_add (differentiableAt_id) (hGdiff z)]
      congr 1
      exact fderiv_id
    rw [hfdz]
    have hLz : ‖fderiv ℝ G z‖ < 1 / 2 := by
      have hz' : fderiv ℝ G z ∈ ball (0 : F →L[ℝ] F) (1 / 2) := hρsub hz
      rw [Metric.mem_ball] at hz'
      simpa [dist_eq_norm] using hz'
    intro u v huv
    -- `u - v = -(fderiv G z) (u - v)`, hence `‖u - v‖ ≤ (1/2) ‖u - v‖`.
    have h0 : u - v + fderiv ℝ G z (u - v) = 0 := by
      have hthis : (ContinuousLinearMap.id ℝ F + fderiv ℝ G z) (u - v) = 0 := by
        rw [map_sub, huv, sub_self]
      simpa using hthis
    have h1 : u - v = - fderiv ℝ G z (u - v) := eq_neg_of_add_eq_zero_left h0
    have h2 : ‖u - v‖ = ‖fderiv ℝ G z (u - v)‖ := by
      have := congrArg (fun t : F => ‖t‖) h1
      rwa [norm_neg] at this
    have h3 : ‖u - v‖ ≤ 1 / 2 * ‖u - v‖ := by
      calc ‖u - v‖ = ‖fderiv ℝ G z (u - v)‖ := h2
        _ ≤ ‖fderiv ℝ G z‖ * ‖u - v‖ := (fderiv ℝ G z).le_opNorm _
        _ ≤ 1 / 2 * ‖u - v‖ := mul_le_mul_of_nonneg_right hLz.le (norm_nonneg _)
    have hfin : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hfin)

/-- Abstract form of the straightening lemma at the smooth regularity level: for a smooth
`φ : E → E × E` whose derivative at `0` is injective, there is a smooth map `H : E × E → E × E`
which is injective and an immersion on a ball around the origin and reproduces `φ` on the axis
`v = 0`.  This is the `C^∞` version of `Work.Whitney.exists_tubular_param_general`. -/
theorem exists_tubular_param_general_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → E × E) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (h0 : Function.Injective (fderiv ℝ φ 0)) :
    ∃ (H : E × E → E × E) (ρ : ℝ), 0 < ρ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H ∧
      (∀ u : E, H (u, 0) = φ u) ∧ Set.InjOn H (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ, Function.Injective (fderiv ℝ H z)) := by
  classical
  let L : E →L[ℝ] E × E := fderiv ℝ φ 0
  have hL : Function.Injective L := h0
  have hfin : Module.finrank ℝ (E × E) = Module.finrank ℝ E + Module.finrank ℝ E :=
    Module.finrank_prod
  obtain ⟨T, hT⟩ := exists_clm_equiv_of_injective L hL hfin
  -- The straightened map `ψ = T.symm ∘ H`, where `H (u,v) = φ u + T (0,v)`.
  let ψ : E × E → E × E := fun z => T.symm (φ z.1) + (0, z.2)
  let G : E × E → E × E := fun z => T.symm (φ z.1) - (z.1, 0)
  have hψG : ∀ z, ψ z = z + G z := by
    intro z
    have hz : (((0:E), z.2) : E × E) = z - ((z.1 : E), (0:E)) := by ext <;> simp
    simp only [ψ, G]
    rw [hz]
    abel
  have hψsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : E × E => T.symm (φ z.1)) :=
      (T.symm : E × E →L[ℝ] E × E).contDiff.comp (hφ.comp contDiff_fst)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : E × E => ((0:E), z.2)) :=
      contDiff_const.prodMk contDiff_snd
    exact h1.add h2
  have hGsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : E × E => T.symm (φ z.1)) :=
      (T.symm : E × E →L[ℝ] E × E).contDiff.comp (hφ.comp contDiff_fst)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : E × E => ((z.1 : E), (0:E))) :=
      contDiff_fst.prodMk contDiff_const
    exact h1.sub h2
  have hG0 : fderiv ℝ G 0 = 0 := by
    have hne0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    have hA : HasFDerivAt (fun z : E × E => T.symm (φ z.1))
        ((T.symm : E × E →L[ℝ] E × E).comp (L.comp (ContinuousLinearMap.fst ℝ E E))) 0 := by
      have hφd : HasFDerivAt φ L (0:E) :=
        ((hφ.differentiable hne0).differentiableAt (x := 0)).hasFDerivAt
      have hfst : HasFDerivAt (fun z : E × E => z.1) (ContinuousLinearMap.fst ℝ E E) (0:E × E) :=
        hasFDerivAt_fst
      exact ((ContinuousLinearMap.hasFDerivAt (T.symm : E × E →L[ℝ] E × E)).comp 0
        (hφd.comp 0 hfst))
    have hB : HasFDerivAt (fun z : E × E => ((z.1 : E), (0:E)))
        ((ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.fst ℝ E E)) 0 := by
      have h := ContinuousLinearMap.hasFDerivAt
        ((ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.fst ℝ E E)) (x := (0:E × E))
      have hfun : (fun z : E × E => ((z.1 : E), (0:E)))
          = (fun z => ((ContinuousLinearMap.inl ℝ E E).comp
              (ContinuousLinearMap.fst ℝ E E)) z) := by
        funext z; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]; rfl
      rw [hfun]; exact h
    have hAB := hA.sub hB
    have hTsymmL : (T.symm : E × E →L[ℝ] E × E).comp L = ContinuousLinearMap.inl ℝ E E := by
      refine ContinuousLinearMap.ext fun u => ?_
      rw [ContinuousLinearMap.comp_apply, ← hT u]; simp
    have hkey : (T.symm : E × E →L[ℝ] E × E).comp (L.comp (ContinuousLinearMap.fst ℝ E E))
        = (ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.fst ℝ E E) := by
      rw [← ContinuousLinearMap.comp_assoc, hTsymmL]
    have h2 : fderiv ℝ G 0 = fderiv ℝ ((fun z : E × E => T.symm (φ z.1))
        - (fun z : E × E => ((z.1 : E), (0:E)))) 0 := by
      congr 1
    rw [h2, hAB.fderiv, hkey, sub_self]
  obtain ⟨ρ, hρ, hinjψ, hfdψ⟩ := exists_injOn_ball_of_perturbation_smooth ψ G hψG hGsm hG0
  -- The straightened map we return.
  let H : E × E → E × E := fun z => (T : E × E →L[ℝ] E × E) (ψ z)
  refine ⟨H, ρ, hρ, ?_, ?_, ?_, ?_⟩
  · have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : E × E => (T : E × E →L[ℝ] E × E) (ψ z)) :=
      (T : E × E →L[ℝ] E × E).contDiff.comp hψsm
    simpa only [H] using hh
  · intro u
    simp only [H, ψ]
    simp
  · intro z1 h1 z2 h2 h
    exact hinjψ h1 h2 (T.injective h)
  · intro z hz
    have hne0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    have hTinj : Function.Injective (T : E × E →L[ℝ] E × E) :=
      fun a b h => T.injective (by simpa using h)
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ z) z :=
      ((hψsm.contDiffAt).differentiableAt hne0).hasFDerivAt
    have hcomp := (ContinuousLinearMap.hasFDerivAt (T : E × E →L[ℝ] E × E)).comp z hψd
    have hfdz : fderiv ℝ H z = (T : E × E →L[ℝ] E × E).comp (fderiv ℝ ψ z) := by
      rw [show H = ((T : E × E →L[ℝ] E × E) ∘ ψ) from rfl]
      exact hcomp.fderiv
    rw [hfdz]
    intro a b hab
    exact (hfdψ z hz) (hTinj (by simpa only [ContinuousLinearMap.comp_apply] using hab))

end Work.Whitney
