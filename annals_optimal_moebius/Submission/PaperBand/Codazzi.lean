import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Submission.PaperBand.SecondDeriv
import Submission.PaperBand.BendSegments

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 400000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Codazzi equations for the shape matrix of the band

(Roadmap item (1), continue — Lemma `mc` support.)  The shape matrix
`S = dNentry f` of the isometric immersion satisfies the *Codazzi
equations* on the interior of the strip:

    a_v = b_u   and   c_u = b_v

where `a = S₀₀`, `b = S₁₀ = S₀₁`, `c = S₁₁` and subscripts are the
directional derivatives along the coordinate directions.  Together with the
Gauss equation `ac = b²` (flatness, `shapeOperator_det_zero`) these are the
identities that force the kernel vector field `w = (b, −a)` to be
straightening (commons `Commons.Analysis.Calculus.FDeriv.kernelField_direction_perp`).

Proof: on the interior write `S₀₀ = ⟨N_u, t₀⟩`, `S₁₀ = ⟨N_v, t₀⟩`,
`S₁₁ = ⟨N_v, t₁⟩` with `N_u := fderiv N · e₀̂`, differentiate with the
product rule (`fderiv_inner_apply`), substitute the normal second
derivatives of the frame, which vanish against the tangent-valued `dN`, and
commute mixed partials of the smooth normal
(`secondDirectional_commute_two`).
-/

noncomputable section
namespace Submission.PaperBand

/-- The normal is `C^∞` on the interior; so is its derivative map
`y ↦ fderiv N y`. -/
lemma contDiffOn_fderiv_unitNormal {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y) stripInterior := by
  have hN : ContDiffOn ℝ ∞ (fun z : ℝ² => unitNormal f z) stripInterior :=
    contDiffOn_unitNormal hf
  have hdf : ContDiffOn ℝ ∞
      (fun y : ℝ² => fderivWithin ℝ (fun z : ℝ² => unitNormal f z) stripInterior y)
      stripInterior :=
    hN.fderivWithin stripInterior_isOpen.uniqueDiffOn (by simp)
  refine hdf.congr ?_
  intro y hy
  rw [fderivWithin_of_isOpen stripInterior_isOpen hy]

/-- `y ↦ fderiv N y e₀̂` is `C^∞` on the interior. -/
lemma contDiffOn_fderiv_dirN₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[1, 0])
      stripInterior := by
  have hd := contDiffOn_fderiv_unitNormal hf
  simpa using ContDiffOn.clm_apply hd (contDiffOn_const : ContDiffOn ℝ ∞
    (fun _ : ℝ² => (!₂[1, 0] : ℝ²)) stripInterior)

/-- `y ↦ fderiv N y e₁̂` is `C^∞` on the interior. -/
lemma contDiffOn_fderiv_dirN₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ContDiffOn ℝ ∞ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[0, 1])
      stripInterior := by
  have hd := contDiffOn_fderiv_unitNormal hf
  simpa using ContDiffOn.clm_apply hd (contDiffOn_const : ContDiffOn ℝ ∞
    (fun _ : ℝ² => (!₂[0, 1] : ℝ²)) stripInterior)

/-- `y ↦ fderiv N y e₀̂` is differentiable at interior points. -/
lemma differentiableAt_Ndir₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[1, 0]) x := by
  intro x hx
  exact ((contDiffOn_fderiv_dirN₀ hf).differentiableOn (by simp) x hx).differentiableAt
    (IsOpen.mem_nhds stripInterior_isOpen hx)

/-- `y ↦ fderiv N y e₁̂` is differentiable at interior points. -/
lemma differentiableAt_Ndir₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      DifferentiableAt ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[0, 1]) x := by
  intro x hx
  exact ((contDiffOn_fderiv_dirN₁ hf).differentiableOn (by simp) x hx).differentiableAt
    (IsOpen.mem_nhds stripInterior_isOpen hx)

/-- Mixed partials of the smooth normal commute (both equal `N_uv`). -/
lemma Ndir_commute {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[0, 1]) x !₂[1, 0] =
      fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[1, 0]) x !₂[0, 1] := by
  intro x hx
  have hN2 : ContDiffOn ℝ 2 (fun z : ℝ² => unitNormal f z) stripInterior :=
    (contDiffOn_unitNormal hf).of_le (by decide)
  exact Commons.Analysis.Calculus.FDeriv.secondDirectional_commute_two
    (E := ℝ²) (F := ℝ³) (s := stripInterior) (f := fun z : ℝ² => unitNormal f z) (x := x)
    stripInterior_isOpen hx hN2 !₂[0, 1] !₂[1, 0]

/-- Explicit entries of `dNentry`. -/
lemma dNentry₀₀_apply (f : ℝ² → ℝ³) (x : ℝ²) :
    dNentry f x 0 0 = inner ℝ (dN f x !₂[1, 0]) (tangent₀ f x) := by
  simp [dNentry]

/-- Explicit entries of `dNentry`. -/
lemma dNentry₀₁_apply (f : ℝ² → ℝ³) (x : ℝ²) :
    dNentry f x 0 1 = inner ℝ (dN f x !₂[1, 0]) (tangent₁ f x) := by
  simp [dNentry]

/-- Explicit entries of `dNentry`. -/
lemma dNentry₁₀_apply (f : ℝ² → ℝ³) (x : ℝ²) :
    dNentry f x 1 0 = inner ℝ (dN f x !₂[0, 1]) (tangent₀ f x) := by
  simp [dNentry]

/-- Explicit entries of `dNentry`. -/
lemma dNentry₁₁_apply (f : ℝ² → ℝ³) (x : ℝ²) :
    dNentry f x 1 1 = inner ℝ (dN f x !₂[0, 1]) (tangent₁ f x) := by
  simp [dNentry]

/-- On the interior, `dNentry f y 0 0 = ⟨N_u, tangent₀⟩`. -/
lemma dNentry₀₀_eq {f : ℝ² → ℝ³} :
    ∀ y ∈ stripInterior,
      dNentry f y 0 0 = inner ℝ
        (fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[1, 0]) (tangent₀ f y) := by
  intro y hy
  rw [dNentry₀₀_apply f y]
  rw [dN_eq_fderiv (f := f) hy]

/-- On the interior, `dNentry f y 1 0 = ⟨N_v, tangent₀⟩`. -/
lemma dNentry₁₀_eq {f : ℝ² → ℝ³} :
    ∀ y ∈ stripInterior,
      dNentry f y 1 0 = inner ℝ
        (fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[0, 1]) (tangent₀ f y) := by
  intro y hy
  rw [dNentry₁₀_apply f y]
  rw [dN_eq_fderiv (f := f) hy]

/-- On the interior, `dNentry f y 1 1 = ⟨N_v, tangent₁⟩`. -/
lemma dNentry₁₁_eq {f : ℝ² → ℝ³} :
    ∀ y ∈ stripInterior,
      dNentry f y 1 1 = inner ℝ
        (fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[0, 1]) (tangent₁ f y) := by
  intro y hy
  rw [dNentry₁₁_apply f y]
  rw [dN_eq_fderiv (f := f) hy]

/-- On the interior, `dNentry f y 1 0 = ⟨N_u, tangent₁⟩` (symmetry of the
shape operator). -/
lemma dNentry₁₀_eq_symm {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ y ∈ stripInterior,
      dNentry f y 1 0 = inner ℝ
        (fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[1, 0]) (tangent₁ f y) := by
  intro y hy
  calc
    dNentry f y 1 0 = dNentry f y 0 1 := (shapeOperator_symm hf y hy (1 : Fin 2) (0 : Fin 2))
    _ = inner ℝ (dN f y !₂[1, 0]) (tangent₁ f y) := dNentry₀₁_apply f y
    _ = inner ℝ (fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[1, 0]) (tangent₁ f y) := by
        rw [dN_eq_fderiv (f := f) hy]

/-- On the interior, the normal derivatives along `e₀̂` (resp. `e₁̂`) are
orthogonal to the normal (the shape operator is tangent-valued). -/
lemma Ndir_orth_normal {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      inner ℝ (fderiv ℝ (fun z : ℝ² => unitNormal f z) x !₂[1, 0]) (unitNormal f x) = 0 ∧
      inner ℝ (fderiv ℝ (fun z : ℝ² => unitNormal f z) x !₂[0, 1]) (unitNormal f x) = 0 := by
  intro x hx
  constructor
  · have hv := dN_tangent_valued hf x hx !₂[1, 0]
    simpa [dN_eq_fderiv (f := f) hx] using hv
  · have hv := dN_tangent_valued hf x hx !₂[0, 1]
    simpa [dN_eq_fderiv (f := f) hx] using hv

/-- **Codazzi equation `a_v = b_u`**: the directional derivative of
`dNentry · 0 0` along `e₁̂` equals the directional derivative of
`dNentry · 1 0` along `e₀̂`, on the interior of the strip. -/
lemma codazzi₀ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => dNentry f y 0 0) x !₂[0, 1] =
      fderiv ℝ (fun y : ℝ² => dNentry f y 1 0) x !₂[1, 0] := by
  intro x hx
  let N : ℝ² → ℝ³ := fun z => unitNormal f z
  let Nu : ℝ² → ℝ³ := fun y => fderiv ℝ N y !₂[1, 0]
  let Nv : ℝ² → ℝ³ := fun y => fderiv ℝ N y !₂[0, 1]
  let t0 : ℝ² → ℝ³ := fun y => tangent₀ f y
  have hdifNu : DifferentiableAt ℝ Nu x := by
    dsimp [Nu, N]
    exact differentiableAt_Ndir₀ hf x hx
  have hdifNv : DifferentiableAt ℝ Nv x := by
    dsimp [Nv, N]
    exact differentiableAt_Ndir₁ hf x hx
  have hdifT0 : DifferentiableAt ℝ t0 x := by
    dsimp [t0]
    exact differentiableAt_tangent₀ hf x hx
  rcases (Ndir_orth_normal hf x hx) with ⟨hNu0, hNv0⟩
  have heA : (fun y : ℝ² => dNentry f y 0 0) =ᶠ[𝓝 x] (fun y => inner ℝ (Nu y) (t0 y)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    dsimp [Nu, N, t0]
    exact dNentry₀₀_eq y hy
  have heB : (fun y : ℝ² => dNentry f y 1 0) =ᶠ[𝓝 x] (fun y => inner ℝ (Nv y) (t0 y)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    dsimp [Nv, N, t0]
    exact dNentry₁₀_eq y hy
  have hpdA : fderiv ℝ (fun y : ℝ² => inner ℝ (Nu y) (t0 y)) x !₂[0, 1] =
      inner ℝ (Nu x) (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) +
      inner ℝ (fderiv ℝ Nu x !₂[0, 1]) (tangent₀ f x) := by
    simpa [t0] using fderiv_inner_apply (𝕜 := ℝ) hdifNu hdifT0 !₂[0, 1]
  have hpdB : fderiv ℝ (fun y : ℝ² => inner ℝ (Nv y) (t0 y)) x !₂[1, 0] =
      inner ℝ (Nv x) (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]) +
      inner ℝ (fderiv ℝ Nv x !₂[1, 0]) (tangent₀ f x) := by
    simpa [t0] using fderiv_inner_apply (𝕜 := ℝ) hdifNv hdifT0 !₂[1, 0]
  -- derivative of the a-entry along e₁̂:
  have hderA : fderiv ℝ (fun y : ℝ² => dNentry f y 0 0) x !₂[0, 1] =
      inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[1, 0])
        x !₂[0, 1]) (tangent₀ f x) := by
    calc
      fderiv ℝ (fun y : ℝ² => dNentry f y 0 0) x !₂[0, 1]
          = fderiv ℝ (fun y : ℝ² => inner ℝ (Nu y) (t0 y)) x !₂[0, 1] := by
              exact congrArg (fun L : ℝ² →L[ℝ] ℝ => L !₂[0, 1])
                (Filter.EventuallyEq.fderiv_eq heA)
      _ = inner ℝ (Nu x) (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) +
          inner ℝ (fderiv ℝ Nu x !₂[0, 1]) (tangent₀ f x) := hpdA
      _ = inner ℝ (fderiv ℝ Nu x !₂[0, 1]) (tangent₀ f x) := by
          have hsub := secondDeriv_dNentry₁ hf x hx
          have hterm : inner ℝ (Nu x)
              (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[0, 1]) = 0 := by
            rw [hsub]
            rw [inner_smul_right]
            dsimp [Nu, N] at hNu0 ⊢
            rw [hNu0]
            ring
          rw [hterm]
          simp
      _ = inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[1, 0])
          x !₂[0, 1]) (tangent₀ f x) := by
            dsimp [Nu, N]
  -- derivative of the b-entry along e₀̂:
  have hderB : fderiv ℝ (fun y : ℝ² => dNentry f y 1 0) x !₂[1, 0] =
      inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[0, 1])
        x !₂[1, 0]) (tangent₀ f x) := by
    calc
      fderiv ℝ (fun y : ℝ² => dNentry f y 1 0) x !₂[1, 0]
          = fderiv ℝ (fun y : ℝ² => inner ℝ (Nv y) (t0 y)) x !₂[1, 0] := by
              exact congrArg (fun L : ℝ² →L[ℝ] ℝ => L !₂[1, 0])
                (Filter.EventuallyEq.fderiv_eq heB)
      _ = inner ℝ (Nv x) (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]) +
          inner ℝ (fderiv ℝ Nv x !₂[1, 0]) (tangent₀ f x) := hpdB
      _ = inner ℝ (fderiv ℝ Nv x !₂[1, 0]) (tangent₀ f x) := by
          have hsub := secondDeriv_dNentry₀ hf x hx
          have hterm : inner ℝ (Nv x)
              (fderiv ℝ (fun y : ℝ² => tangent₀ f y) x !₂[1, 0]) = 0 := by
            rw [hsub]
            rw [inner_smul_right]
            dsimp [Nv, N] at hNv0 ⊢
            rw [hNv0]
            ring
          rw [hterm]
          simp
      _ = inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[0, 1])
          x !₂[1, 0]) (tangent₀ f x) := by
            dsimp [Nv, N]
  rw [hderA, hderB]
  congr 1
  exact (Ndir_commute hf x hx).symm

/-- **Codazzi equation `c_u = b_v`**: the directional derivative of
`dNentry · 1 1` along `e₀̂` equals the directional derivative of
`dNentry · 1 0` along `e₁̂`, on the interior of the strip. -/
lemma codazzi₁ {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      fderiv ℝ (fun y : ℝ² => dNentry f y 1 1) x !₂[1, 0] =
      fderiv ℝ (fun y : ℝ² => dNentry f y 1 0) x !₂[0, 1] := by
  intro x hx
  let N : ℝ² → ℝ³ := fun z => unitNormal f z
  let Nu : ℝ² → ℝ³ := fun y => fderiv ℝ N y !₂[1, 0]
  let Nv : ℝ² → ℝ³ := fun y => fderiv ℝ N y !₂[0, 1]
  let t1 : ℝ² → ℝ³ := fun y => tangent₁ f y
  have hdifNu : DifferentiableAt ℝ Nu x := by
    dsimp [Nu, N]
    exact differentiableAt_Ndir₀ hf x hx
  have hdifNv : DifferentiableAt ℝ Nv x := by
    dsimp [Nv, N]
    exact differentiableAt_Ndir₁ hf x hx
  have hdifT1 : DifferentiableAt ℝ t1 x := by
    dsimp [t1]
    exact differentiableAt_tangent₁ hf x hx
  rcases (Ndir_orth_normal hf x hx) with ⟨hNu0, hNv0⟩
  have heC : (fun y : ℝ² => dNentry f y 1 1) =ᶠ[𝓝 x] (fun y => inner ℝ (Nv y) (t1 y)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    dsimp [Nv, N, t1]
    exact dNentry₁₁_eq y hy
  have heB' : (fun y : ℝ² => dNentry f y 1 0) =ᶠ[𝓝 x] (fun y => inner ℝ (Nu y) (t1 y)) := by
    filter_upwards [IsOpen.mem_nhds stripInterior_isOpen hx] with y hy
    dsimp [Nu, N, t1]
    exact dNentry₁₀_eq_symm hf y hy
  have hpdC : fderiv ℝ (fun y : ℝ² => inner ℝ (Nv y) (t1 y)) x !₂[1, 0] =
      inner ℝ (Nv x) (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0]) +
      inner ℝ (fderiv ℝ Nv x !₂[1, 0]) (tangent₁ f x) := by
    simpa [t1] using fderiv_inner_apply (𝕜 := ℝ) hdifNv hdifT1 !₂[1, 0]
  have hpdB' : fderiv ℝ (fun y : ℝ² => inner ℝ (Nu y) (t1 y)) x !₂[0, 1] =
      inner ℝ (Nu x) (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) +
      inner ℝ (fderiv ℝ Nu x !₂[0, 1]) (tangent₁ f x) := by
    simpa [t1] using fderiv_inner_apply (𝕜 := ℝ) hdifNu hdifT1 !₂[0, 1]
  -- derivative of the c-entry along e₀̂:
  have hderC : fderiv ℝ (fun y : ℝ² => dNentry f y 1 1) x !₂[1, 0] =
      inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[0, 1])
        x !₂[1, 0]) (tangent₁ f x) := by
    calc
      fderiv ℝ (fun y : ℝ² => dNentry f y 1 1) x !₂[1, 0]
          = fderiv ℝ (fun y : ℝ² => inner ℝ (Nv y) (t1 y)) x !₂[1, 0] := by
              exact congrArg (fun L : ℝ² →L[ℝ] ℝ => L !₂[1, 0])
                (Filter.EventuallyEq.fderiv_eq heC)
      _ = inner ℝ (Nv x) (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0]) +
          inner ℝ (fderiv ℝ Nv x !₂[1, 0]) (tangent₁ f x) := hpdC
      _ = inner ℝ (fderiv ℝ Nv x !₂[1, 0]) (tangent₁ f x) := by
          have hsub := tangent₁_e0_deriv hf x hx
          have hterm : inner ℝ (Nv x)
              (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[1, 0]) = 0 := by
            rw [hsub]
            rw [inner_smul_right]
            dsimp [Nv, N] at hNv0 ⊢
            rw [hNv0]
            ring
          rw [hterm]
          simp
      _ = inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[0, 1])
          x !₂[1, 0]) (tangent₁ f x) := by
            dsimp [Nv, N]
  -- derivative of the b-entry along e₁̂ (using the representation
  -- `dNentry · 1 0 = ⟨N_u, tangent₁⟩`):
  have hderB' : fderiv ℝ (fun y : ℝ² => dNentry f y 1 0) x !₂[0, 1] =
      inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[1, 0])
        x !₂[0, 1]) (tangent₁ f x) := by
    calc
      fderiv ℝ (fun y : ℝ² => dNentry f y 1 0) x !₂[0, 1]
          = fderiv ℝ (fun y : ℝ² => inner ℝ (Nu y) (t1 y)) x !₂[0, 1] := by
              exact congrArg (fun L : ℝ² →L[ℝ] ℝ => L !₂[0, 1])
                (Filter.EventuallyEq.fderiv_eq heB')
      _ = inner ℝ (Nu x) (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) +
          inner ℝ (fderiv ℝ Nu x !₂[0, 1]) (tangent₁ f x) := hpdB'
      _ = inner ℝ (fderiv ℝ Nu x !₂[0, 1]) (tangent₁ f x) := by
          have hsub := secondDeriv_dNentry₂ hf x hx
          have hterm : inner ℝ (Nu x)
              (fderiv ℝ (fun y : ℝ² => tangent₁ f y) x !₂[0, 1]) = 0 := by
            rw [hsub]
            rw [inner_smul_right]
            dsimp [Nu, N] at hNu0 ⊢
            rw [hNu0]
            ring
          rw [hterm]
          simp
      _ = inner ℝ (fderiv ℝ (fun y : ℝ² => fderiv ℝ (fun z : ℝ² => unitNormal f z) y !₂[1, 0])
          x !₂[0, 1]) (tangent₁ f x) := by
            dsimp [Nu, N]
  rw [hderC, hderB']
  congr 1
  exact Ndir_commute hf x hx

end Submission.PaperBand
end
