import Mathlib
import Submission.Work.Diff.Dim2.levelSet_kit

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The local slice statement for the `d = 2` branch

Let `u : M → ℝ²` be `C^∞` on an open set `N` of a boundaryless smooth manifold `M` whose model
space `E` is two-dimensional, and let `V` be a non-vanishing vector field on `N` with
`du_x (V x) = 0`, `du_x ≠ 0` for `x ∈ N`.  Let `Φ` be the flow of `V` (two-parameter convention:
`Φ s s x = x` and `∂_τ Φ s τ x = V (Φ s τ x)`).

Then around every `z ∈ N` the level set of `u` through `z` is contained in the flow line of `z`:
there is a neighbourhood `Vn` of `z` such that `w ∈ Vn`, `w ∈ N`, `u w = u z` imply `w = Φ 0 s z`
for some `s`.

The proof is the standard one.  A straight chart path `σ` through `z` in a direction `W`
transversal to `V z` (`du_z W ≠ 0`) together with the flow of `V` gives the two-parameter family
`Θ (a, b) = Φ 0 b (σ a)`; its differential at the origin is invertible because `W` and `V (σ 0)`
are linearly independent (`du` kills `V` and does not kill `W`, and `dim M = 2`).  The inverse
function theorem makes `Θ` a local diffeomorphism at `0`, and `u` is constant along the flow, so
the level set of `u` through `z` is the `a = 0` slice of `Θ`.
-/

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
-- `TangentSpace I x` is a type synonym for the model space `E`; the identification is only
-- definitional after unfolding a semireducible definition, which the default transparency of the
-- tactic engine refuses to do.  `respectTransparency false` restores the liberal behaviour.
set_option backward.isDefEq.respectTransparency false

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-! ## Instance aliases for the tangent fibres

`TangentSpace I x` is (definitionally) the model space `E`, but type class inference does not unfold
the definition, so the model space structure has to be provided explicitly.  The same low-priority
aliases are used in `Submission/Work/Diff/GE/`; they agree definitionally with the structures
induced by any `RiemannianBundle` instance, so they introduce no ambiguity. -/

noncomputable local instance instLevelNbhNAG (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  inferInstanceAs (NormedAddCommGroup E)

noncomputable local instance instLevelNbhNS (x : M) : NormedSpace ℝ (TangentSpace I x) :=
  inferInstanceAs (NormedSpace ℝ E)

noncomputable local instance instLevelNbhFD (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/-! ## The two coordinate curves of `ℝ × ℝ` -/

/-- The first coordinate curve. -/
abbrev ax (a : ℝ) : ℝ × ℝ := (a, 0)

/-- The second coordinate curve. -/
abbrev bx (b : ℝ) : ℝ × ℝ := (0, b)

@[simp] lemma ax_zero : ax 0 = (0 : ℝ × ℝ) := rfl
@[simp] lemma bx_zero : bx 0 = (0 : ℝ × ℝ) := rfl

lemma hasMFDerivAt_ax : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ×ℝ) ax 0
    (ContinuousLinearMap.inl ℝ ℝ ℝ) :=
  ContinuousLinearMap.hasMFDerivAt (ContinuousLinearMap.inl ℝ ℝ ℝ) (x := (0 : ℝ))

lemma hasMFDerivAt_bx : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ×ℝ) bx 0
    (ContinuousLinearMap.inr ℝ ℝ ℝ) :=
  ContinuousLinearMap.hasMFDerivAt (ContinuousLinearMap.inr ℝ ℝ ℝ) (x := (0 : ℝ))

lemma mfderiv_ax_one : ((mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ×ℝ) ax 0 : ℝ →L[ℝ] (ℝ × ℝ)) 1)
    = ((1 : ℝ), (0 : ℝ)) := by
  rw [hasMFDerivAt_ax.mfderiv]
  rfl

lemma mfderiv_bx_one : ((mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ×ℝ) bx 0 : ℝ →L[ℝ] (ℝ × ℝ)) 1)
    = ((0 : ℝ), (1 : ℝ)) := by
  rw [hasMFDerivAt_bx.mfderiv]
  rfl

/-! ## The two-parameter family `(a, b) ↦ Φ 0 b (σ a)` -/

/-- The two-parameter family attached to a curve `σ`. -/
abbrev theta (Φ : ℝ → ℝ → M → M) (σ : ℝ → M) (p : ℝ × ℝ) : M := Φ 0 p.2 (σ p.1)

@[simp] lemma theta_apply (Φ : ℝ → ℝ → M → M) (σ : ℝ → M) (p : ℝ × ℝ) :
    theta Φ σ p = Φ 0 p.2 (σ p.1) := rfl

@[simp] lemma theta_zero (Φ : ℝ → ℝ → M → M) (σ : ℝ → M) :
    theta Φ σ 0 = Φ 0 0 (σ 0) := rfl

lemma theta_comp_ax (Φ : ℝ → ℝ → M → M) (σ : ℝ → M) :
    theta Φ σ ∘ ax = fun a : ℝ => Φ 0 0 (σ a) := rfl

lemma theta_comp_bx (Φ : ℝ → ℝ → M → M) (σ : ℝ → M) :
    theta Φ σ ∘ bx = fun b : ℝ => Φ 0 b (σ 0) := rfl

/-- Smoothness of `theta` on the set where `σ` is defined at the first coordinate. -/
lemma contMDiffOn_theta {Φ : ℝ → ℝ → M → M} {σ : ℝ → M} {s : Set ℝ}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hσ : ContMDiffOn 𝓘(ℝ,ℝ) I ∞ σ s) :
    ContMDiffOn 𝓘(ℝ,ℝ×ℝ) I ∞ (theta Φ σ) {p : ℝ × ℝ | p.1 ∈ s} := by
  have h1 : ContMDiffOn 𝓘(ℝ,ℝ×ℝ) (𝓘(ℝ,ℝ).prod I) ∞
      (fun p : ℝ × ℝ => (p.2, σ p.1)) {p : ℝ × ℝ | p.1 ∈ s} :=
    ContMDiffOn.prodMk ((ContinuousLinearMap.snd ℝ ℝ ℝ).contMDiff.contMDiffOn)
      (hσ.comp ((ContinuousLinearMap.fst ℝ ℝ ℝ).contMDiff.contMDiffOn)
        (fun p hp => hp))
  have h2 := ((contMDiff_pair_flow hΦsm).contMDiffOn (s := Set.univ)).comp h1
    (fun p _ => trivial)
  exact h2

/-! ## The main theorem -/

/-- **The local slice statement.**  Around every point `z` of `N` the level set of `u` through `z`
is contained in the flow line of `z`: there is a neighbourhood `Vn` of `z` such that
`w ∈ Vn`, `w ∈ N`, `u w = u z` imply `w = Φ 0 s z` for some `s`. -/
theorem level_nbhd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless]
    {N : Set M} (hN : IsOpen N)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVnz : ∀ x ∈ N, V x ≠ 0)
    (hΦsm : ContMDiff (((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)).prod I)
      I ((⊤ : ENat) : WithTop ENat) (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ (s : ℝ) (x : M), Φ s s x = x)
    (hΦderiv : ∀ (s t : ℝ) (x : M),
      HasMFDerivAt (modelWithCornersSelf ℝ ℝ) I (fun τ : ℝ => Φ s τ x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    {u : M → EuclideanSpace ℝ (Fin 2)}
    (hu : ContMDiffOn I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((⊤ : ENat) : WithTop ENat) u N)
    (huV : ∀ x ∈ N, mfderiv I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) u x (V x) = 0)
    (huinj : ∀ x ∈ N, mfderiv I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) u x ≠ 0)
    (hdim : Module.finrank ℝ E = 2)
    (z : M) (hz : z ∈ N) :
    ∃ Vn : Set M, IsOpen Vn ∧ z ∈ Vn ∧
      ∀ w ∈ Vn, w ∈ N → u w = u z → ∃ s : ℝ, w = Φ 0 s z := by
  classical
  -- ## Step 1: a vector transversal to `V z`
  obtain ⟨W, hW⟩ : ∃ W : TangentSpace I z, (mfderiv I 𝓘(ℝ, Sph2) u z) W ≠ 0 := by
    by_contra h
    push Not at h
    exact huinj z hz (ContinuousLinearMap.ext h)
  -- ## Step 2: the straight chart path through `z` in the direction `W`
  set σ : ℝ → M := chartLine (I := I) z W with hσdef
  have hσ0 : σ 0 = z := chartLine_zero (I := I) z W
  have hσsm : ContMDiffOn 𝓘(ℝ,ℝ) I ∞ σ (chartLineSet (I := I) z W) := by
    rw [hσdef]
    exact chartLine_smoothOn (I := I) z W
  have hσsm0 : ContMDiffAt 𝓘(ℝ,ℝ) I ∞ σ 0 :=
    hσsm.contMDiffAt
      ((chartLine_set_open (I := I) z W).mem_nhds (chartLine_set_mem (I := I) z W))
  have hσderiv : HasMFDerivAt 𝓘(ℝ,ℝ) I σ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight W) := by
    rw [hσdef]
    exact chartLine_hasMFDerivAt (I := I) z W
  -- the same non-vanishing statement, at the flow base point `σ 0`
  have hWσ : (mfderiv I 𝓘(ℝ, Sph2) u (σ 0)) (show TangentSpace I (σ 0) from W) ≠ 0 := by
    have hb : mfderiv I 𝓘(ℝ, Sph2) u (σ 0) = mfderiv I 𝓘(ℝ, Sph2) u z := by
      rw [hσ0]
    rw [hb]
    exact hW
  -- ## Step 3: `u` separates `z` from `σ t` for small `t ≠ 0`
  have hsep : ∀ᶠ t in 𝓝[≠] (0 : ℝ), u (σ t) ≠ u z := by
    have hbase : MDifferentiableAt I 𝓘(ℝ, Sph2) u (σ 0) :=
      (hu.contMDiffAt (hN.mem_nhds (by rw [hσ0]; exact hz))).mdifferentiableAt (by simp)
    have hcomp : HasFDerivAt (u ∘ σ)
        ((mfderiv I 𝓘(ℝ, Sph2) u (σ 0)) ∘SL ((1 : ℝ →L[ℝ] ℝ).smulRight W)) 0 :=
      hasMFDerivAt_iff_hasFDerivAt.mp (hbase.hasMFDerivAt.comp 0 hσderiv)
    have hD : HasDerivAt (u ∘ σ)
        ((mfderiv I 𝓘(ℝ, Sph2) u (σ 0)) (show TangentSpace I (σ 0) from W)) 0 := by
      have h := hcomp.hasDerivAt
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        one_apply_eq_self, one_smul] at h
      exact h
    refine (hD.eventually_ne (c := u z) hWσ).mono (fun t ht hcon => ht hcon)
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ, 0 < |t| → |t| < δ → u (σ t) ≠ u z := by
    rw [eventually_nhdsWithin_iff] at hsep
    obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp hsep
    refine ⟨ε, hε, fun t ht0 hlt => hε' ?_ (abs_pos.mp ht0)⟩
    simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hlt
  -- ## Step 4: for small parameters the flow segments through `σ l` stay in `N`
  have hcontΥ : ContinuousAt (fun q : ℝ × ℝ => Φ 0 q.1 (σ q.2)) ((0 : ℝ), (0 : ℝ)) := by
    have houter : ContinuousAt (fun q : ℝ × M => Φ 0 q.1 q.2) (0, σ 0) :=
      (contMDiff_pair_flow hΦsm).continuous.continuousAt
    have hinner : ContinuousAt (fun q : ℝ × ℝ => (q.1, σ q.2)) ((0 : ℝ), (0 : ℝ)) :=
      ContinuousAt.prodMk continuousAt_fst
        (ContinuousAt.comp (f := Prod.snd) (x := ((0 : ℝ), (0 : ℝ)))
          hσsm0.continuousAt continuousAt_snd)
    exact ContinuousAt.comp (f := fun q : ℝ × ℝ => (q.1, σ q.2))
      (x := ((0 : ℝ), (0 : ℝ))) houter hinner
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ τ l : ℝ, |τ| < δ → |l| < δ → Φ 0 τ (σ l) ∈ N := by
    have hmem : (fun q : ℝ × ℝ => Φ 0 q.1 (σ q.2)) ⁻¹' N ∈ 𝓝 (0, 0) :=
      hcontΥ.preimage_mem_nhds (hN.mem_nhds (by rw [hΦself, hσ0]; exact hz))
    obtain ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.mp hmem
    refine ⟨ε, hε, fun τ l hτ hl => ?_⟩
    have hmem' : (τ, l) ∈ Metric.ball ((0 : ℝ), (0 : ℝ)) ε := by
      simp only [Metric.mem_ball, Prod.dist_eq, dist_zero_right, Real.norm_eq_abs, max_lt_iff]
      exact ⟨hτ, hl⟩
    simpa using hε' hmem'
  -- ## Step 5: the two-parameter family and its differential
  set Θ : ℝ × ℝ → M := theta Φ σ with hΘdef
  have hΘΘ : Θ = theta Φ σ := hΘdef
  have hΘsm : ContMDiffOn 𝓘(ℝ,ℝ×ℝ) I ∞ Θ {p : ℝ × ℝ | p.1 ∈ chartLineSet (I := I) z W} := by
    rw [hΘΘ]
    exact contMDiffOn_theta hΦsm hσsm
  have hΘopen : IsOpen {p : ℝ × ℝ | p.1 ∈ chartLineSet (I := I) z W} :=
    (chartLine_set_open (I := I) z W).preimage (by fun_prop)
  have hΘmem : {p : ℝ × ℝ | p.1 ∈ chartLineSet (I := I) z W} ∈ 𝓝 (0 : ℝ × ℝ) :=
    hΘopen.mem_nhds (chartLine_set_mem (I := I) z W)
  have hmdΘ : MDifferentiableAt 𝓘(ℝ,ℝ×ℝ) I Θ 0 :=
    (hΘsm.contMDiffAt hΘmem).mdifferentiableAt (by simp)
  -- the two directional derivatives (computed in the model space `E`)
  have hval₁ : (mfderiv 𝓘(ℝ,ℝ×ℝ) I Θ 0) ((1 : ℝ), (0 : ℝ)) =
      (show TangentSpace I (Θ 0) from W) := by
    have hchain : (((mfderiv 𝓘(ℝ,ℝ) I (Θ ∘ ax) 0 : ℝ →L[ℝ] E) 1 : E))
        = ((mfderiv 𝓘(ℝ,ℝ×ℝ) I Θ (ax 0) : ℝ × ℝ →L[ℝ] E)
            ((mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ×ℝ) ax 0 : ℝ →L[ℝ] (ℝ × ℝ)) 1) : E) :=
      mfderiv_comp_apply (x := (0 : ℝ)) (f := ax) (g := Θ) hmdΘ
        hasMFDerivAt_ax.mdifferentiableAt (1 : ℝ)
    have hLHS : (((mfderiv 𝓘(ℝ,ℝ) I (Θ ∘ ax) 0 : ℝ →L[ℝ] E) 1 : E)) = W := by
      have hfun : Θ ∘ ax = σ := by
        rw [hΘΘ]
        funext a
        show Φ 0 0 (σ a) = σ a
        exact hΦself 0 (σ a)
      have h1 := congrArg (fun (f : ℝ →L[ℝ] E) => f 1)
        (mfderiv_congr (I := 𝓘(ℝ,ℝ)) (I' := I) (x := (0 : ℝ)) hfun)
      have h2 := congrArg (fun (f : ℝ →L[ℝ] E) => f 1) hσderiv.mfderiv
      have h3 : (((1 : ℝ →L[ℝ] ℝ).smulRight W : ℝ →L[ℝ] E) 1 : E) = W := by
        rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
      exact h1.trans (h2.trans h3)
    have hkey : (((mfderiv 𝓘(ℝ,ℝ×ℝ) I Θ 0 : ℝ × ℝ →L[ℝ] E) ((1 : ℝ), (0 : ℝ)) : E)) = W := by
      rw [mfderiv_ax_one] at hchain
      exact hchain.symm.trans hLHS
    exact hkey
  have hval₂ : (mfderiv 𝓘(ℝ,ℝ×ℝ) I Θ 0) ((0 : ℝ), (1 : ℝ)) = V (Θ 0) := by
    have hchain : (((mfderiv 𝓘(ℝ,ℝ) I (Θ ∘ bx) 0 : ℝ →L[ℝ] E) 1 : E))
        = ((mfderiv 𝓘(ℝ,ℝ×ℝ) I Θ (bx 0) : ℝ × ℝ →L[ℝ] E)
            ((mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ×ℝ) bx 0 : ℝ →L[ℝ] (ℝ × ℝ)) 1) : E) :=
      mfderiv_comp_apply (x := (0 : ℝ)) (f := bx) (g := Θ) hmdΘ
        hasMFDerivAt_bx.mdifferentiableAt (1 : ℝ)
    have hLHS : (((mfderiv 𝓘(ℝ,ℝ) I (Θ ∘ bx) 0 : ℝ →L[ℝ] E) 1 : E))
        = ((V (Θ 0) : TangentSpace I (Θ 0)) : E) := by
      have h1 := congrArg (fun (f : ℝ →L[ℝ] E) => f 1) (hΦderiv 0 0 (σ 0)).mfderiv
      have h2 : (((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ 0 0 (σ 0))) : ℝ →L[ℝ] E) 1 : E)
          = ((V (Φ 0 0 (σ 0)) : TangentSpace I (Φ 0 0 (σ 0))) : E) := by
        rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul]
      exact h1.trans h2
    have hkey : (((mfderiv 𝓘(ℝ,ℝ×ℝ) I Θ 0 : ℝ × ℝ →L[ℝ] E) ((0 : ℝ), (1 : ℝ)) : E))
        = ((V (Θ 0) : TangentSpace I (Θ 0)) : E) := by
      rw [mfderiv_bx_one] at hchain
      exact hchain.symm.trans hLHS
    exact hkey
  -- the differential as an explicit linear map
  set L : ℝ × ℝ →L[ℝ] TangentSpace I (Θ 0) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (show TangentSpace I (Θ 0) from W) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (V (Θ 0)) with hLdef
  have hLval : ∀ p : ℝ × ℝ, L p = p.1 • (show TangentSpace I (Θ 0) from W) + p.2 • V (Θ 0) := by
    intro p
    simp [hLdef]
  have hmfderivΘ : mfderiv 𝓘(ℝ,ℝ×ℝ) I Θ 0 = L := by
    refine ContinuousLinearMap.ext fun p => ?_
    have hp : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by
      refine Prod.ext ?_ ?_ <;> simp
    have key : ((mfderiv 𝓘(ℝ,ℝ×ℝ) I Θ 0 : ℝ × ℝ →L[ℝ] E) p : E)
        = ((L p : TangentSpace I (Θ 0)) : E) := by
      rw [hLval p]
      conv_lhs => rw [hp]
      rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
        ContinuousLinearMap.map_smul, hval₁, hval₂]
    exact key
  -- ## Step 6: the differential is invertible
  have hΘ0N : Θ 0 ∈ N := by
    have hΘ0z : Θ 0 = z := by rw [hΘΘ, theta_zero, hΦself, hσ0]
    rwa [hΘ0z]
  have hWΘ : (mfderiv I 𝓘(ℝ, Sph2) u (Θ 0)) (show TangentSpace I (Θ 0) from W) ≠ 0 := by
    have hΘ0z : Θ 0 = z := by rw [hΘΘ, theta_zero, hΦself, hσ0]
    have hb : mfderiv I 𝓘(ℝ, Sph2) u (Θ 0) = mfderiv I 𝓘(ℝ, Sph2) u z := by rw [hΘ0z]
    rw [hb]
    exact hW
  have hinjL : Function.Injective L := by
    intro p q hpq
    have h0 : L (p - q) = 0 := by rw [map_sub, hpq, sub_self]
    have hp1 : (p - q).1 = 0 := by
      have h1 : ((p - q).1) • ((mfderiv I 𝓘(ℝ, Sph2) u (Θ 0))
          (show TangentSpace I (Θ 0) from W)) = 0 := by
        have h2 : (mfderiv I 𝓘(ℝ, Sph2) u (Θ 0)) (L (p - q)) = 0 := by
          rw [h0, ContinuousLinearMap.map_zero]
        rw [hLval (p - q), ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
          ContinuousLinearMap.map_smul, huV (Θ 0) hΘ0N, smul_zero, add_zero] at h2
        exact h2
      rcases smul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hWΘ
    have hp2 : (p - q).2 = 0 := by
      have h1 : ((p - q).2) • (V (Θ 0)) = 0 := by
        rw [hLval (p - q), hp1, zero_smul, zero_add] at h0
        exact h0
      rcases smul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h (hVnz (Θ 0) hΘ0N)
    have hp0 : p - q = 0 := by
      ext <;> [exact hp1; exact hp2]
    exact sub_eq_zero.mp hp0
  have hfin : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ (TangentSpace I (Θ 0)) := by
    rw [Module.finrank_prod, (tangentSpaceCastModel I (Θ 0)).toLinearEquiv.finrank_eq, hdim]
    norm_num
  have hL : L.IsInvertible := by
    have hsurj : Function.Surjective L :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinjL
    refine ⟨(LinearEquiv.ofBijective L.toLinearMap ⟨hinjL, hsurj⟩).toContinuousLinearEquiv, ?_⟩
    exact ContinuousLinearMap.ext fun v => rfl
  -- ## Step 7: the inverse function theorem
  have hIFT : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ×ℝ) I ∞ Θ 0 :=
    Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_infty_of_contMDiffOn_of_mfderiv_isInvertible
      (I := 𝓘(ℝ, ℝ×ℝ)) (I' := I) (f := Θ)
      (U := {p : ℝ × ℝ | p.1 ∈ chartLineSet (I := I) z W}) hΘmem hΘsm
      (BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, ℝ×ℝ)) (M := ℝ × ℝ) (x := (0 : ℝ × ℝ)))
      (by rw [hmfderivΘ]; exact hL)
  obtain ⟨Φd, h0src, hEq⟩ := hIFT
  have hΦd0 : Φd 0 = z := by
    have h := hEq h0src
    rw [show Θ 0 = z from by rw [hΘΘ, theta_zero, hΦself, hσ0]] at h
    exact h.symm
  have hzT : z ∈ Φd.target := hΦd0 ▸ Φd.map_source' h0src
  have hinvz : Φd.invFun z = 0 := by
    have h := Φd.left_inv' h0src
    rwa [hΦd0] at h
  -- ## Step 8: the neighbourhood of `z`
  refine ⟨Φd.target ∩ Φd.invFun ⁻¹' Metric.ball (0 : ℝ × ℝ) (min δ₂ δ₃), ?_, ?_, ?_⟩
  · exact Φd.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage Φd.open_target
      (Metric.isOpen_ball (x := (0 : ℝ × ℝ)) (ε := min δ₂ δ₃))
  · refine ⟨hzT, ?_⟩
    rw [Set.mem_preimage, hinvz]
    simp [Metric.mem_ball, lt_min hδ₂pos hδ₃pos]
  · intro w hwV hwN hwu
    obtain ⟨hwt, hwball⟩ := hwV
    have hwnorm : ‖Φd.invFun w‖ < min δ₂ δ₃ := by
      rw [Set.mem_preimage] at hwball
      simpa [Metric.mem_ball, dist_eq_norm] using hwball
    have hpsrc : Φd.invFun w ∈ Φd.source := Φd.map_target' hwt
    have hwp : Φd (Φd.invFun w) = w := Φd.right_inv' hwt
    have hlt2 : ‖Φd.invFun w‖ < δ₂ := lt_of_lt_of_le hwnorm (min_le_left _ _)
    have hlt3 : ‖Φd.invFun w‖ < δ₃ := lt_of_lt_of_le hwnorm (min_le_right _ _)
    have hb2 : |(Φd.invFun w).1| < δ₂ := by
      have h : |(Φd.invFun w).1| ≤ ‖Φd.invFun w‖ := by
        simpa [Real.norm_eq_abs] using norm_fst_le (Φd.invFun w)
      linarith
    have hb3 : |(Φd.invFun w).2| < δ₂ := by
      have h : |(Φd.invFun w).2| ≤ ‖Φd.invFun w‖ := by
        simpa [Real.norm_eq_abs] using norm_snd_le (Φd.invFun w)
      linarith
    have hb4 : |(Φd.invFun w).1| < δ₃ := by
      have h : |(Φd.invFun w).1| ≤ ‖Φd.invFun w‖ := by
        simpa [Real.norm_eq_abs] using norm_fst_le (Φd.invFun w)
      linarith
    have hwuw : u w = u (σ (Φd.invFun w).1) := by
      have h1 : u (Θ (Φd.invFun w)) = u (σ (Φd.invFun w).1) := by
        rw [hΘΘ]
        exact u_flow_eq (N := N) (u := u) (V := V) (Φ := Φ) hΦself hΦderiv hN hu huV
          (a := -δ₂) (b := δ₂) ⟨by linarith, hδ₂pos⟩ (σ (Φd.invFun w).1)
          (t := (Φd.invFun w).2) (abs_lt.mp hb3)
          (fun τ hτ => hδ₂ τ ((Φd.invFun w).1) (abs_lt.mpr hτ) hb2)
      rw [hEq hpsrc, hwp] at h1
      exact h1
    have h0eq : (Φd.invFun w).1 = 0 := by
      by_contra hne
      exact hδ₃ _ (abs_pos.mpr hne) hb4 (hwuw.symm.trans hwu)
    refine ⟨(Φd.invFun w).2, ?_⟩
    have h2 : w = Θ (Φd.invFun w) := hwp.symm.trans (hEq hpsrc).symm
    calc w = Θ (Φd.invFun w) := h2
      _ = Φ 0 ((Φd.invFun w).2) (σ ((Φd.invFun w).1)) := by rw [hΘΘ]
      _ = Φ 0 ((Φd.invFun w).2) z := by rw [h0eq, hσ0]

end

end Work.Diff.Dim2
