import Mathlib
import Submission.Work.Diff.Dim2.Ambient
import Submission.Work.Diff.Dim2.Lib

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

-- NOTE for the prover (two reviewers approved the statement).  `angForm u x w = ⟪rot90 (u x), mfderiv u x w⟫`
-- (`Submission.Work.Diff.Dim2.Ambient`); `rot90 v = (-(v 1), v 0)`, `rot90_apply_zero/one` and
-- `inner_fin_two` are in `Submission/Work/Diff/Dim2/Lib.lean`.
-- This is the `huang` hypothesis of the proved `Work.Diff.Dim2.azimuth`, isolated.
-- Route: (i) `N` open and `‖u‖ ≡ 1` on `N` give `⟪u x, mfderiv u x w⟫ = 0` for every `w`
-- (differentiate the constant function `y ↦ ⟪u y, u y⟫ = 1`, e.g. `Filter.EventuallyEq.mfderiv_eq`
-- together with the chain rule for the continuous bilinear pairing);
-- (ii) the 2-dimensional Lagrange identity `⟪a,b⟫ ^ 2 + ⟪rot90 a, b⟫ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2`
-- (a `ring` computation from `inner_fin_two`, `rot90_apply_zero`, `rot90_apply_one`);
-- (iii) if `angForm u x w = 0` then (i)+(ii) with `‖u x‖ = 1` force `mfderiv u x w = 0`, so
-- `w ∈ ker (mfderiv u x)`; `huV`+`hVnz` give a nonzero element of that kernel, and `huinj`+`hdim2`
-- + rank-nullity give `finrank (ker (mfderiv u x)) = 2 - 1 = 1`, so `ker (mfderiv u x) = span {V x}`;
-- but `w ≠ 0` with `dτ x w = 0` and `dτ x (V x) = 1` forces `w ∉ span {V x}`.  Contradiction.
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

/-! ## Auxiliary lemmas for `label_u_angForm`

The three ingredients listed in the note above are proved here from `Mathlib` only
(the two `angForm`-specific facts, `inner_sq_add_inner_rot90_sq` and `aux_angForm_apply`,
use the plane lemmas of `Submission/Work/Diff/Dim2/Lib.lean`). -/

section Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- `mvfderiv` (the derivative of a vector-valued map, valued in the model space) and `mfderiv`
(the derivative, valued in the tangent space of the target) agree, since the tangent space of a
normed space at a point is identified with the normed space itself. -/
lemma aux_mvfderiv_eq_mfderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : M → V) (x : M) :
    mvfderiv I g x = mfderiv I 𝓘(ℝ, V) g x := by
  ext v
  rfl

/-- `mvfderiv` respects eventual equality. -/
lemma aux_mvfderiv_congr_of_eventuallyEq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g₁ g₂ : M → V} {x : M} (h : g₁ =ᶠ[𝓝 x] g₂) :
    mvfderiv I g₁ x = mvfderiv I g₂ x := by
  rw [mvfderiv, mvfderiv, h.eq_of_nhds, Filter.EventuallyEq.mfderiv_eq h]
  all_goals first | rfl | (ext v; rfl)

/-- **Product rule for the manifold derivative of an inner product.**  For `Φ Ψ : M → V` into a
real inner product space `V`, differentiable at `x`, and any `v ∈ TₓM`,

`d⟪Φ,Ψ⟫_x v = ⟪dΦ_x v, Ψ x⟫ + ⟪Φ x, dΨ_x v⟫`.

Route: the pair map `y ↦ (Φ y, Ψ y)` into the normed space `V × V`, the smooth pairing
`(u,w) ↦ ⟪u,w⟫` on `V × V` (whose Fréchet derivative is computed with `fderiv_inner_apply`),
and the chain rule `HasMFDerivAt.comp`; the derivative of the pair map is `mfderiv_prodMk`
after the identification of the product model with `V × V`. -/
lemma aux_mvfderiv_inner_pair {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Φ Ψ : M → V} {x : M}
    (hΦ : MDifferentiableAt I (𝓘(ℝ, V)) Φ x) (hΨ : MDifferentiableAt I (𝓘(ℝ, V)) Ψ x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y : M => Inner.inner ℝ (Φ y) (Ψ y)) x v
      = Inner.inner ℝ (mvfderiv I Φ x v) (Ψ x)
        + Inner.inner ℝ (Φ x) (mvfderiv I Ψ x v) := by
  have hP : MDifferentiableAt I (𝓘(ℝ, V × V)) (fun y : M => (Φ y, Ψ y)) x := hΦ.prodMk_space hΨ
  have hgd : MDifferentiableAt (𝓘(ℝ, V × V)) (𝓘(ℝ, ℝ))
      (fun p : V × V => Inner.inner ℝ p.1 p.2) (Φ x, Ψ x) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact DifferentiableAt.inner ℝ differentiableAt_fst differentiableAt_snd
  have hLg_eq : fderiv ℝ (fun p : V × V => Inner.inner ℝ p.1 p.2) (Φ x, Ψ x)
      = (innerSL ℝ (Ψ x)) ∘L (ContinuousLinearMap.fst ℝ V V)
        + (innerSL ℝ (Φ x)) ∘L (ContinuousLinearMap.snd ℝ V V) := by
    apply ContinuousLinearMap.ext
    intro y
    rw [fderiv_inner_apply ℝ differentiableAt_fst differentiableAt_snd, fderiv_fst, fderiv_snd]
    show Inner.inner ℝ (Φ x) y.2 + Inner.inner ℝ y.1 (Ψ x)
        = Inner.inner ℝ (Ψ x) y.1 + Inner.inner ℝ (Φ x) y.2
    rw [real_inner_comm y.1 (Ψ x)]
    ring
  have hLgF : HasFDerivAt (fun p : V × V => Inner.inner ℝ p.1 p.2)
      ((innerSL ℝ (Ψ x)) ∘L (ContinuousLinearMap.fst ℝ V V)
        + (innerSL ℝ (Φ x)) ∘L (ContinuousLinearMap.snd ℝ V V)) (Φ x, Ψ x) := by
    rw [← hLg_eq]
    exact (mdifferentiableAt_iff_differentiableAt.mp hgd).hasFDerivAt
  have hLg : HasMFDerivAt 𝓘(ℝ, V × V) 𝓘(ℝ, ℝ)
      (fun p : V × V => Inner.inner ℝ p.1 p.2) (Φ x, Ψ x)
      ((innerSL ℝ (Ψ x)) ∘L (ContinuousLinearMap.fst ℝ V V)
        + (innerSL ℝ (Φ x)) ∘L (ContinuousLinearMap.snd ℝ V V)) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr hLgF
  have hmf : mfderiv I 𝓘(ℝ, V × V) (fun y : M => (Φ y, Ψ y)) x
      = (mfderiv I 𝓘(ℝ, V) Φ x).prod (mfderiv I 𝓘(ℝ, V) Ψ x) := by
    rw [modelWithCornersSelf_prod (𝕜 := ℝ) (E := V) (F := V), ← chartedSpaceSelf_prod]
    exact mfderiv_prodMk (𝕜 := ℝ) (I := I) hΦ hΨ
  have hmfdf : mfderiv I 𝓘(ℝ, V × V) (fun y : M => (Φ y, Ψ y)) x
      = (mvfderiv I Φ x).prod (mvfderiv I Ψ x) := by
    rw [hmf, ← aux_mvfderiv_eq_mfderiv (I := I) (g := Φ) (x := x),
      ← aux_mvfderiv_eq_mfderiv (I := I) (g := Ψ) (x := x)]
    rfl
  have hdf : HasMFDerivAt I 𝓘(ℝ, V × V) (fun y : M => (Φ y, Ψ y)) x
      ((mvfderiv I Φ x).prod (mvfderiv I Ψ x)) := by
    rw [← hmfdf]
    exact hP.hasMFDerivAt
  have hcomp := hLg.comp x hdf
  have hmv : mvfderiv I ((fun p : V × V => Inner.inner ℝ p.1 p.2) ∘ fun y : M => (Φ y, Ψ y)) x v
      = ((innerSL ℝ (Ψ x)) ∘L (ContinuousLinearMap.fst ℝ V V)
          + (innerSL ℝ (Φ x)) ∘L (ContinuousLinearMap.snd ℝ V V))
          (((mvfderiv I Φ x).prod (mvfderiv I Ψ x)) v) := by
    rw [aux_mvfderiv_eq_mfderiv]
    rw [hcomp.mfderiv]
    rfl
  show (mvfderiv I ((fun p : V × V => Inner.inner ℝ p.1 p.2) ∘ fun y : M => (Φ y, Ψ y)) x) v = _
  rw [hmv, ContinuousLinearMap.prod_apply]
  show Inner.inner ℝ (Ψ x) (mvfderiv I Φ x v) + Inner.inner ℝ (Φ x) (mvfderiv I Ψ x v)
      = Inner.inner ℝ (mvfderiv I Φ x v) (Ψ x) + Inner.inner ℝ (Φ x) (mvfderiv I Ψ x v)
  rw [real_inner_comm (mvfderiv I Φ x v) (Ψ x)]

/-- **The two-dimensional Lagrange identity**: for `a b ∈ ℝ²`,
`⟪a,b⟫² + ⟪J a, b⟫² = ‖a‖² ‖b‖²` where `J = rot90`. -/
lemma inner_sq_add_inner_rot90_sq (a b : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ a b ^ 2 + inner ℝ (rot90 a) b ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq a, ← real_inner_self_eq_norm_sq b]
  rw [inner_fin_two a b, inner_fin_two (rot90 a) b, inner_fin_two a a, inner_fin_two b b]
  rw [show (rot90 a).ofLp 0 = - a 1 from rot90_apply_zero a,
      show (rot90 a).ofLp 1 = a 0 from rot90_apply_one a]
  ring

/-- **A unit vector field has everywhere orthogonal derivative**: if `u` is `C^∞` on the open set
`N`, `x ∈ N` and `‖u y‖ = 1` for `y ∈ N`, then `⟪u x, du_x w⟫ = 0` for every `w ∈ TₓM`.

Route: `y ↦ ⟪u y, u y⟫ = ‖u y‖²` is eventually equal to `1` near `x`, so its derivative at `x`
vanishes (`aux_mvfderiv_congr_of_eventuallyEq` plus `mvfderiv_const`); the product rule
`aux_mvfderiv_inner_pair` identifies that derivative with `2 ⟪u x, du_x w⟫`. -/
lemma inner_mvfderiv_eq_zero_of_norm_eq_one
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u : M → V} {N : Set M} (hN : IsOpen N) {x : M} (hx : x ∈ N)
    (hu : ContMDiffOn I 𝓘(ℝ, V) ∞ u N) (hu1 : ∀ y ∈ N, ‖u y‖ = 1) (w : TangentSpace I x) :
    inner ℝ (u x) ((mvfderiv I u x) w) = 0 := by
  have hux : MDifferentiableAt I 𝓘(ℝ, V) u x :=
    (hu.contMDiffAt (hN.mem_nhds hx)).mdifferentiableAt (by simp)
  have hFeq : (fun y : M => inner ℝ (u y) (u y)) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [hN.mem_nhds hx] with y hy
    rw [real_inner_self_eq_norm_sq, hu1 y hy]
    norm_num
  have hz : mvfderiv I (fun y : M => inner ℝ (u y) (u y)) x = 0 := by
    rw [aux_mvfderiv_congr_of_eventuallyEq hFeq, mvfderiv_const]
  have hpr := aux_mvfderiv_inner_pair (I := I) hux hux w
  have h2 : inner ℝ ((mvfderiv I u x) w) (u x) + inner ℝ (u x) ((mvfderiv I u x) w) = 0 := by
    have h1 := hpr
    rw [hz] at h1
    exact h1.symm
  rw [real_inner_comm (u x) ((mvfderiv I u x) w)] at h2
  have h3 : 2 * inner ℝ (u x) ((mvfderiv I u x) w) = 0 := by linarith
  exact (mul_eq_zero.mp h3).resolve_left two_ne_zero

/-- **Linear algebra.**  A nonzero linear map `L : E' → V` whose domain is 2-dimensional and which
kills a nonzero vector `v` has kernel exactly `ℝ ∙ v`: the range is nonzero (so of dimension at
least `1`), whence rank–nullity forces `finrank (ker L) = 2 - 1 = 1`, and `ker L` contains the
1-dimensional subspace `ℝ ∙ v`. -/
lemma aux_ker_eq_span_of_finrank_two
    {E' V : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : E' →L[ℝ] V) (hE : Module.finrank ℝ E' = 2)
    (hL : L ≠ 0) {v : E'} (hv : v ≠ 0) (hvk : L v = 0) :
    LinearMap.ker (L : E' →ₗ[ℝ] V) = Submodule.span ℝ {v} := by
  have hLlin : (L : E' →ₗ[ℝ] V) ≠ 0 := by
    intro h
    exact hL (ContinuousLinearMap.ext fun x =>
      by simpa using congrArg (fun f : E' →ₗ[ℝ] V => f x) h)
  have hrange_ne : LinearMap.range (L : E' →ₗ[ℝ] V) ≠ ⊥ := by
    intro h
    exact hLlin (LinearMap.range_eq_bot.mp h)
  have h1 : 1 ≤ Module.finrank ℝ (LinearMap.range (L : E' →ₗ[ℝ] V)) := by
    obtain ⟨y, hy, hyne⟩ := (Submodule.ne_bot_iff _).mp hrange_ne
    have hsp : Submodule.span ℝ {y} ≤ LinearMap.range (L : E' →ₗ[ℝ] V) :=
      Submodule.span_le.mpr (by rintro z rfl; exact hy)
    calc (1 : ℕ) = Module.finrank ℝ (Submodule.span ℝ {y}) := (finrank_span_singleton hyne).symm
      _ ≤ Module.finrank ℝ (LinearMap.range (L : E' →ₗ[ℝ] V)) := Submodule.finrank_mono hsp
  have hsum := LinearMap.finrank_range_add_finrank_ker (L : E' →ₗ[ℝ] V)
  rw [hE] at hsum
  have hker_le : Module.finrank ℝ (LinearMap.ker (L : E' →ₗ[ℝ] V)) ≤ 1 := by
    have h3 := Nat.add_le_add_left h1 (Module.finrank ℝ (LinearMap.ker (L : E' →ₗ[ℝ] V)))
    omega
  have hker_ge : 1 ≤ Module.finrank ℝ (LinearMap.ker (L : E' →ₗ[ℝ] V)) := by
    have hvk' : v ∈ LinearMap.ker (L : E' →ₗ[ℝ] V) := hvk
    have hsp : Submodule.span ℝ {v} ≤ LinearMap.ker (L : E' →ₗ[ℝ] V) :=
      Submodule.span_le.mpr (by rintro z rfl; exact hvk')
    calc (1 : ℕ) = Module.finrank ℝ (Submodule.span ℝ {v}) := (finrank_span_singleton hv).symm
      _ ≤ Module.finrank ℝ (LinearMap.ker (L : E' →ₗ[ℝ] V)) := Submodule.finrank_mono hsp
  have hker : Module.finrank ℝ (LinearMap.ker (L : E' →ₗ[ℝ] V)) = 1 := le_antisymm hker_le hker_ge
  have hsp : Submodule.span ℝ {v} ≤ LinearMap.ker (L : E' →ₗ[ℝ] V) :=
    Submodule.span_le.mpr (by rintro z rfl; exact hvk)
  exact (Submodule.eq_of_le_of_finrank_le hsp (by rw [hker, finrank_span_singleton hv])).symm

set_option backward.isDefEq.respectTransparency false in
/-- The angular form of `Az` at `x`, evaluated at `w`, is the inner product of `rot90 (Az x)` with
`dAz_x w` — the definition `Work.Diff.Dim2.angForm` unfolded and `innerSL` evaluated. -/
lemma aux_angForm_apply {Az : M → EuclideanSpace ℝ (Fin 2)} (x : M) (w : TangentSpace I x) :
    angForm (I := I) (M := M) (Az := Az) x w
      = inner ℝ (rot90 (Az x))
          ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) Az x) w) := by
  rw [angForm, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rfl

end Aux

theorem label_u_angForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    (hdim2 : Module.finrank ℝ E = 2)
    {N : Set M} (hN : IsOpen N)
    {V : (x : M) → TangentSpace I x}
    {τ : M → ℝ} {u : M → EuclideanSpace ℝ (Fin 2)}
    (hu_sm : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ u N)
    (hu1 : ∀ x ∈ N, ‖u x‖ = 1)
    (huV : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x (V x) = 0)
    (hVnz : ∀ x ∈ N, V x ≠ 0)
    (huinj : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x ≠ 0)
    (hτV : ∀ x ∈ N, mfderiv I 𝓘(ℝ,ℝ) τ x (V x) = 1) :
    ∀ x ∈ N, ∀ w : TangentSpace I x, w ≠ 0 →
      mfderiv I 𝓘(ℝ,ℝ) τ x w = 0 →
      Work.Diff.Dim2.angForm (I := I) (M := M) (Az := u) x w ≠ 0 := by
  intro x hx w hwne hτw hzero
  -- Work with `b := du_x w` viewed as an element of the target model `ℝ²` (the two types are
  -- definitionally equal; fixing the type keeps the norm and inner product instances coherent).
  obtain ⟨b, hb⟩ : ∃ b : EuclideanSpace ℝ (Fin 2),
      b = (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x) w := ⟨_, rfl⟩
  -- (i) `b ⟂ u x` because `‖u‖ ≡ 1` on the open set `N`.
  have horth : inner ℝ (u x) b = 0 := by
    have h1 : inner ℝ (u x)
        ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x) w) = 0 :=
      inner_mvfderiv_eq_zero_of_norm_eq_one (I := I) hN hx hu_sm hu1 w
    simpa [hb] using h1
  -- (ii) `angForm u x w = 0` says that `b` is also orthogonal to `rot90 (u x)`.
  have hz : inner ℝ (rot90 (u x)) b = 0 := by
    have h1 : inner ℝ (rot90 (u x))
        ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x) w) = 0 := by
      rw [← aux_angForm_apply (I := I) (Az := u) x w]
      exact hzero
    simpa [hb] using h1
  -- The 2-dimensional Lagrange identity then forces `b = 0`.
  have hlag := inner_sq_add_inner_rot90_sq (u x) b
  rw [horth, hz, hu1 x hx] at hlag
  have hb0 : ‖b‖ = 0 := by
    have h : ‖b‖ ^ 2 = 0 := by nlinarith [hlag]
    nlinarith [h, norm_nonneg b]
  have hb_eq : b = 0 := norm_eq_zero.mp hb0
  have hbw : ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x) w) = 0 := by
    rw [← hb, hb_eq]
    rfl
  -- (iii) hence `w` lies in the kernel, which is exactly `ℝ ∙ V x`.
  have hker : LinearMap.ker ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x).toLinearMap)
      = Submodule.span ℝ {V x} :=
    aux_ker_eq_span_of_finrank_two
      (L := mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x) hdim2
      (huinj x hx) (hVnz x hx) (huV x hx)
  have hwker : w ∈ LinearMap.ker ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x).toLinearMap) :=
    hbw
  rw [hker] at hwker
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwker
  -- `dτ x` vanishes on `w = c • V x` but equals `1` on `V x`, so `c = 0`.
  have hc0 : c = 0 := by
    have h := hτw
    rw [← hc, map_smul, hτV x hx] at h
    have h1 : c • (1 : ℝ) = (0 : ℝ) • (1 : ℝ) := by simpa only [h, zero_smul]
    exact smul_left_injective ℝ (m := (1 : ℝ)) one_ne_zero h1
  exact hwne (by rw [← hc, hc0, zero_smul])

end Work.Diff.Dim2
