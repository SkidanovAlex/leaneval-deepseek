import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.grad_smoothAt
import Submission.Work.Diff.C.mvfderiv_contMDiffAt
import Submission.Work.Diff.C.mvfderiv_inner_pair
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_gen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ## The two vector-calculus ingredients

Both are stated for an arbitrary real inner product space `V` (the use is `V = T_qM`), and both
are fully proved here.  `mvfderiv_inner_pair_aux` is the product rule whose intended name in this
workspace is `Work.Diff.C.mvfderiv_inner_pair` (the routing docstring below refers to it under that
name); it is proved here from scratch so that this file depends on nothing unproved.  The smoothness
of `y ↦ mvfderiv I Φ y (𝒵 y)` is taken from `Work.Diff.EXT.contMDiffAt_mvfderiv_gen` (the general
normed-target version of `Work.Diff.C.mvfderiv_contMDiffAt`), imported below. -/

namespace SqNormAux

/-- **The inner product of two maps that are `C^∞` at a point is `C^∞` there.**

Route: `y ↦ (Φ y, Ψ y)` is `C^∞` at `x` into the normed space `V × V`
(`ContMDiffAt.prodMk_space`), the pairing `(u,w) ↦ ⟪u,w⟫` is `C^∞` on `V × V` (`ContDiff.inner` of
the two projections, transported by `contMDiffAt_iff_contDiffAt`), and smoothness is closed under
composition (`ContMDiffAt.comp`). -/
theorem contMDiffAt_inner_pair {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Φ Ψ : M → V} {x : M}
    (hΦ : ContMDiffAt I 𝓘(ℝ, V) ∞ Φ x) (hΨ : ContMDiffAt I 𝓘(ℝ, V) ∞ Ψ x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y : M => Inner.inner ℝ (Φ y) (Ψ y)) x := by
  have hpair : ContMDiffAt I 𝓘(ℝ, V × V) ∞ (fun y : M => (Φ y, Ψ y)) x :=
    hΦ.prodMk_space hΨ
  have hP : ContMDiffAt 𝓘(ℝ, V × V) 𝓘(ℝ, ℝ) ∞
      (fun p : V × V => Inner.inner ℝ p.1 p.2) (Φ x, Ψ x) :=
    contMDiffAt_iff_contDiffAt.mpr
      (ContDiffAt.inner ℝ contDiffAt_fst contDiffAt_snd)
  exact hP.comp x hpair

/-- **The derivative of a constant multiple of a real-valued function**: `d (c · g)_x = c · dg_x`.
Immediate from the Leibniz rule `mvfderiv_smul` for the constant field `fun _ ↦ c`, whose
derivative is `0`. -/
theorem mvfderiv_const_mul {c : ℝ} {g : M → ℝ} {x : M}
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g x) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => c * g y) x v = c * mvfderiv I g x v := by
  have hzero : (d% (fun _ : M => c) x : TangentSpace I x →L[ℝ] ℝ) = 0 := mvfderiv_const c
  have hz : (0 : TangentSpace I x →L[ℝ] ℝ).smulRight (g x) = 0 := by
    ext z
    simp
  have hfun : (fun y : M => c * g y) = (fun _ : M => c) • g := rfl
  have hsmul := mvfderiv_smul (x := x) (a := fun _ : M => c) (mdifferentiableAt_const (c := c)) hg
  rw [hfun, hsmul, hzero, hz, add_zero, smul_apply, smul_eq_mul]

/-- **Product rule for the manifold derivative of an inner product.**

For `Φ Ψ : M → V` (a real inner product space) differentiable at `x` and any `v ∈ TₓM`,
`d⟪Φ,Ψ⟫_x v = ⟪dΦ_x v, Ψ x⟫ + ⟪Φ x, dΨ_x v⟫`.

Route: the polarization identity `⟪Φ y, Ψ y⟫ = ¼(⟪Φ y+Ψ y, Φ y+Ψ y⟫ - ⟪Φ y-Ψ y, Φ y-Ψ y⟫)` reduces
the claim to the composition of the two fields `Φ ± Ψ` with the single-variable quadratic form
`N u = ⟪u,u⟫` on `V`.  The latter is a map between model spaces, so the chain rule
`mvfderiv_comp_apply` applies and, since `mfderiv` of a model-space map is `fderiv`
(`mvfderiv_eq_fderiv`), the derivative of `N` at `u` is `fderivInnerCLM ℝ (u,u)`, whose value on
`w` is `2⟪u,w⟫`.  Additivity of `mvfderiv` (`mvfderiv_add`, `mvfderiv_sub`) and the constant
multiple rule `mvfderiv_const_mul` finish the computation. -/
theorem mvfderiv_inner_pair_aux {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {Φ Ψ : M → V} {x : M} (hΦ : MDifferentiableAt I 𝓘(ℝ, V) Φ x)
    (hΨ : MDifferentiableAt I 𝓘(ℝ, V) Ψ x) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => Inner.inner ℝ (Φ y) (Ψ y)) x v
      = Inner.inner ℝ (mvfderiv I Φ x v) (Ψ x)
        + Inner.inner ℝ (Φ x) (mvfderiv I Ψ x v) := by
  set N : V → ℝ := fun u => Inner.inner ℝ u u with hN
  have hNcd : ContDiff ℝ ∞ N := by
    rw [hN]; exact ContDiff.inner ℝ contDiff_id contDiff_id
  have hNmd (u : V) : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, ℝ) N u :=
    (contMDiffAt_iff_contDiffAt.mpr (hNcd.contDiffAt)).mdifferentiableAt (by simp)
  have hfder (u : V) : fderiv ℝ N u
      = fderivInnerCLM ℝ (u, u)
          ∘SL ((ContinuousLinearMap.id ℝ V).prod (ContinuousLinearMap.id ℝ V)) := by
    rw [hN]
    simpa using ((hasFDerivAt_id u).inner ℝ (hasFDerivAt_id u)).fderiv
  have hkey (u w : V) : (fderiv ℝ N u) w = 2 * Inner.inner ℝ u w := by
    rw [hfder u, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, ContinuousLinearMap.id_apply]
    rw [real_inner_comm (x := w)]
    ring
  have hpolar : ∀ y : M, Inner.inner ℝ (Φ y) (Ψ y)
      = (1/4) * (N (Φ y + Ψ y) - N (Φ y - Ψ y)) := by
    intro y
    rw [hN]
    beta_reduce
    rw [inner_add_left, inner_add_right, inner_add_right, inner_sub_left, inner_sub_right,
      inner_sub_right]
    rw [real_inner_comm (x := Ψ y) (y := Φ y)]
    ring
  -- the derivative of `N` composed with a field
  have hNcomp (s : M → V) (hs : MDifferentiableAt I 𝓘(ℝ, V) s x) :
      mvfderiv I (fun y : M => N (s y)) x v
        = 2 * Inner.inner ℝ (s x) (mvfderiv I s x v) := by
    have hc := mvfderiv_comp_apply (I := 𝓘(ℝ, V)) (I' := I) (f := s) (g := N) x
      (hNmd (s x)) hs v
    change (mvfderiv I (N ∘ s) x) v = 2 * Inner.inner ℝ (s x) (mvfderiv I s x v)
    rw [hc]
    rw [show (mfderiv I 𝓘(ℝ, V) s x) v = mvfderiv I s x v from rfl]
    rw [mvfderiv_eq_fderiv]
    exact hkey (s x) _
  have hfunadd : (fun y : M => Φ y + Ψ y) = Φ + Ψ := rfl
  have hfunsub : (fun y : M => Φ y - Ψ y) = Φ - Ψ := rfl
  have hadd : mvfderiv I (fun y : M => Φ y + Ψ y) x = mvfderiv I Φ x + mvfderiv I Ψ x := by
    rw [hfunadd]; exact mvfderiv_add (x := x) hΦ hΨ
  have hsub : mvfderiv I (fun y : M => Φ y - Ψ y) x = mvfderiv I Φ x - mvfderiv I Ψ x := by
    rw [hfunsub]; exact mvfderiv_sub (x := x) hΦ hΨ
  have hp' : mvfderiv I (fun y : M => N (Φ y + Ψ y)) x v
      = 2 * Inner.inner ℝ (Φ x + Ψ x) (mvfderiv I Φ x v + mvfderiv I Ψ x v) := by
    rw [hNcomp (fun y => Φ y + Ψ y) (hΦ.add hΨ), hadd, add_apply]
  have hm' : mvfderiv I (fun y : M => N (Φ y - Ψ y)) x v
      = 2 * Inner.inner ℝ (Φ x - Ψ x) (mvfderiv I Φ x v - mvfderiv I Ψ x v) := by
    rw [hNcomp (fun y => Φ y - Ψ y) (hΦ.sub hΨ), hsub, sub_apply]
  -- differentiability of the two pieces
  have h1md : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => N (Φ y + Ψ y)) x :=
    (hNmd (Φ x + Ψ x)).comp x (hΦ.add hΨ)
  have h2md : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M => N (Φ y - Ψ y)) x :=
    (hNmd (Φ x - Ψ x)).comp x (hΦ.sub hΨ)
  have hGmd : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => N (Φ y + Ψ y) - N (Φ y - Ψ y)) x := h1md.sub h2md
  -- derivative of the difference
  have hGval : mvfderiv I (fun y : M => N (Φ y + Ψ y) - N (Φ y - Ψ y)) x v
      = 2 * Inner.inner ℝ (Φ x + Ψ x) (mvfderiv I Φ x v + mvfderiv I Ψ x v)
        - 2 * Inner.inner ℝ (Φ x - Ψ x) (mvfderiv I Φ x v - mvfderiv I Ψ x v) := by
    have hfuns : (fun y : M => N (Φ y + Ψ y) - N (Φ y - Ψ y))
        = (fun y : M => N (Φ y + Ψ y)) - (fun y : M => N (Φ y - Ψ y)) := rfl
    rw [hfuns, mvfderiv_sub (x := x) h1md h2md, sub_apply, hp', hm']
  have hfun : (fun y : M => Inner.inner ℝ (Φ y) (Ψ y))
      = fun y : M => (1/4) * (N (Φ y + Ψ y) - N (Φ y - Ψ y)) := funext hpolar
  rw [hfun, mvfderiv_const_mul hGmd v, hGval]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [← real_inner_comm (x := Ψ x) (y := mvfderiv I Φ x v)]
  ring

/-! ## The lemma -/

end SqNormAux

open SqNormAux

/-- For a GLOBALLY smooth map `Φ : M → T_qM` with `Φ q = 0`, the function `F y = ⟪Φ y, Φ y⟫`
(the fixed fibre inner product at `q`) has vanishing gradient at `q` and Hessian
`2 ⟪dΦ_q·, dΦ_q·⟫` there.

Route (all ingredients are in the workspace): `F` is globally smooth, so `rgrad F` is a globally
smooth section (`Work.Diff.C.grad_smoothAt` at every point); with a globally smooth extension `𝒵`
of `W` (`Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq`) the identity
`⟪rgrad F y, 𝒵 y⟫ = mvfderiv I F y (𝒵 y)` holds (`inner_rgrad`), and differentiating it at `q` in
the direction `V` with `IsMetricCompatible hmet` gives
`rhess cov F q V W = mvfderiv I (fun y => ⟪Φ y, mvfderiv I Φ y (𝒵 y)⟫) q V` (the term
`⟪rgrad F q, cov 𝒵 q V⟫` vanishes because `rgrad F q = 0`); the product rule
`Work.Diff.C.mvfderiv_inner_pair` then gives `2 ⟪dΦ_q V, dΦ_q W⟫`, since `Φ q = 0` and
`y ↦ mvfderiv I Φ y (𝒵 y)` is smooth at `q` (`Work.Diff.C.mvfderiv_contMDiffAt`). -/
theorem sqNorm_hess_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov)
    {q : M} {Φ : M → TangentSpace I q}
    (hΦ : ContMDiff I (𝓘(ℝ, TangentSpace I q)) ∞ Φ) (hΦ0 : Φ q = 0) :
    (Work.Diff.C.rgrad (I := I) (M := M) (fun y : M => Inner.inner ℝ (Φ y) (Φ y)) q = 0) ∧
      (∀ V W : TangentSpace I q,
        Work.Diff.C.rhess cov (fun y : M => Inner.inner ℝ (Φ y) (Φ y)) q V W =
          2 * Inner.inner ℝ (mvfderiv I Φ q V) (mvfderiv I Φ q W)) := by
  -- the function whose Hessian is computed
  have hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => Inner.inner ℝ (Φ y) (Φ y)) :=
    fun y => contMDiffAt_inner_pair (hΦ y) (hΦ y)
  have hΦmd : MDifferentiableAt I 𝓘(ℝ, TangentSpace I q) Φ q := (hΦ q).mdifferentiableAt (by simp)
  have hΦymd (y : M) : MDifferentiableAt I 𝓘(ℝ, TangentSpace I q) Φ y :=
    (hΦ y).mdifferentiableAt (by simp)
  -- `rgrad F` is a globally smooth section
  have hgradF : ContMDiff I I.tangent ∞
      (T% (fun y : M => rgrad (I := I) (fun z : M => Inner.inner ℝ (Φ z) (Φ z)) y)) :=
    fun y => grad_smoothAt (x := y) (hF y)
  -- ## First conjunct: the gradient vanishes at `q`
  have hrgrad : rgrad (I := I) (fun y : M => Inner.inner ℝ (Φ y) (Φ y)) q = 0 := by
    refine (inner_self_eq_zero (𝕜 := ℝ)).mp ?_
    rw [inner_rgrad_mvfderiv]
    rw [mvfderiv_inner_pair_aux hΦmd hΦmd (rgrad (I := I) (fun y : M => Inner.inner ℝ (Φ y) (Φ y)) q)]
    rw [hΦ0]
    simp
  refine ⟨hrgrad, ?_⟩
  -- ## Second conjunct: the Hessian
  intro V W
  -- a globally smooth extension of `W`
  obtain ⟨𝒵, h𝒵sm, h𝒵q⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
      (I := I) (M := M) (x := q) W
  -- metric compatibility, with the gradient field and the extension
  have hkey := hmet (fun y : M => rgrad (I := I) (fun z : M => Inner.inner ℝ (Φ z) (Φ z)) y) 𝒵
    hgradF h𝒵sm q V
  -- `⟪∇F, 𝒵⟫` is pointwise `dF(𝒵)`
  have hfun1 : (fun y : M =>
        Inner.inner ℝ (rgrad (I := I) (fun z : M => Inner.inner ℝ (Φ z) (Φ z)) y) (𝒵 y))
      = fun y : M => mvfderiv I (fun z : M => Inner.inner ℝ (Φ z) (Φ z)) y (𝒵 y) :=
    funext (fun y => inner_rgrad_mvfderiv _ y (𝒵 y))
  rw [hfun1] at hkey
  -- the `⟪∇F q, …⟫` term vanishes, and `𝒵 q = W`
  rw [h𝒵q, hrgrad, inner_zero_left, add_zero] at hkey
  -- so `rhess` is the derivative of `y ↦ dF_y(𝒵 y)`
  rw [rhess, ← hkey]
  -- pointwise, `dF_y(𝒵 y) = 2⟪Φ y, dΦ_y(𝒵 y)⟫`
  have hGfun : (fun y : M =>
        mvfderiv I (fun z : M => Inner.inner ℝ (Φ z) (Φ z)) y (𝒵 y))
      = fun y : M => 2 * Inner.inner ℝ (Φ y) (mvfderiv I Φ y (𝒵 y)) := by
    funext y
    rw [mvfderiv_inner_pair_aux (hΦymd y) (hΦymd y) (𝒵 y)]
    rw [← real_inner_comm (x := Φ y) (y := mvfderiv I Φ y (𝒵 y))]
    ring
  rw [hGfun]
  -- `y ↦ dΦ_y(𝒵 y)` is smooth at `q`
  have hΨsm : ContMDiffAt I 𝓘(ℝ, TangentSpace I q) ∞
      (fun y : M => mvfderiv I Φ y (𝒵 y)) q :=
    Work.Diff.EXT.contMDiffAt_mvfderiv_gen (f := Φ) (X := 𝒵) (x := q) (hΦ q) (h𝒵sm q)
  have hΨmd : MDifferentiableAt I 𝓘(ℝ, TangentSpace I q)
      (fun y : M => mvfderiv I Φ y (𝒵 y)) q := hΨsm.mdifferentiableAt (by simp)
  have hGmd : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y : M => Inner.inner ℝ (Φ y) (mvfderiv I Φ y (𝒵 y))) q :=
    (contMDiffAt_inner_pair (hΦ q) hΨsm).mdifferentiableAt (by simp)
  -- the second product rule and the vanishing of `Φ q`
  rw [mvfderiv_const_mul hGmd V,
    mvfderiv_inner_pair_aux hΦmd hΨmd V]
  rw [h𝒵q, hΦ0, inner_zero_left, add_zero]

end Work.Diff.C
