/-
  WilG4c — `iterDir_pullX`: the effect of an affine rescaling of the `x`-coordinate on the
  iterated directional derivative.

  For `G : ℝⁿ⁺¹ → ℝ` in the `(x, y)` splitting, the *pullback* of `G` along the affine
  `x`-chart `u ↦ (α + β * u 0, u_{>0})` is the function
  `u ↦ G (pt (α + β * u 0) (Fin.tail u))`.  Its iterated directional derivative along a list
  `L` of directions at the base point `pt x y` is `β ^ (xcount L)` times the iterated
  directional derivative of `G` at the image point `pt (α + β * x) y`: every derivative along
  the *distinguished* `x`-direction `0` picks up a factor `β`, while the `y`-direction
  derivatives are unchanged (the chart acts as the identity on the `y`-coordinates).

  This is the chain rule for the iterated derivative along the affine map.  The proof routes
  through the general statement `iterDir_pullMap` (arbitrary base point), which is an induction
  on the direction list: the derivative of `H ∘ pullMap` is
  `(fderiv H (pullMap z)) ∘ diagCLM β`, and `diagCLM β` scales the `x`-direction by `β` and
  fixes all the `y`-directions.
-/
import Mathlib
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.IterDirAux

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace Work.WilG4c

open Work.WilkG4c

/-! ## 1. The linear part of the affine chart `u ↦ (α + β * u 0, u_{>0})` -/

/-- The continuous linear map `u ↦ pt (β * u 0) (Fin.tail u)`: it scales the distinguished
(`0`-th) coordinate by `β` and fixes every `y`-coordinate. -/
def diagCLM (n : ℕ) (β : ℝ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun j : Fin (n + 1) =>
    Fin.cases (β • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0)
      (fun i : Fin n =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.succ) j)

/-- The affine chart `u ↦ pt (α + β * u 0) (Fin.tail u)` on `ℝⁿ⁺¹`. -/
def pullMap (n : ℕ) (α β : ℝ) (u : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  pt (α + β * u 0) (Fin.tail u)

lemma diagCLM_apply (n : ℕ) (β : ℝ) (v : Fin (n + 1) → ℝ) :
    diagCLM n β v = pt (β * v 0) (Fin.tail v) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [diagCLM, pt]
  | succ i => simp [diagCLM, pt, Fin.tail]

/-- The affine chart is its linear part plus the constant `pt α 0`. -/
lemma pullMap_eq (n : ℕ) (α β : ℝ) (u : Fin (n + 1) → ℝ) :
    pullMap n α β u = diagCLM n β u + pt α (0 : Fin n → ℝ) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [pullMap, diagCLM, pt, add_comm]
  | succ i => simp [pullMap, diagCLM, pt, Fin.tail]

lemma hasFDerivAt_pullMap (n : ℕ) (α β : ℝ) (u : Fin (n + 1) → ℝ) :
    HasFDerivAt (pullMap n α β) (diagCLM n β) u := by
  have hfun : pullMap n α β = fun u => diagCLM n β u + pt α (0 : Fin n → ℝ) := by
    funext u; exact pullMap_eq n α β u
  rw [hfun]
  exact (diagCLM n β).hasFDerivAt.add_const _

lemma diagCLM_single_zero (n : ℕ) (β : ℝ) :
    diagCLM n β (Pi.single 0 (1 : ℝ)) = β • (Pi.single 0 (1 : ℝ) : Fin (n + 1) → ℝ) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [diagCLM]
  | succ i => simp [diagCLM]

lemma diagCLM_single_succ (n : ℕ) (β : ℝ) (i : Fin n) :
    diagCLM n β (Pi.single i.succ (1 : ℝ)) = (Pi.single i.succ (1 : ℝ) : Fin (n + 1) → ℝ) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [diagCLM]
  | succ k =>
      simp only [diagCLM, ContinuousLinearMap.pi_apply, Fin.cases_succ]
      by_cases h : k = i
      · subst h; simp
      · simp [h, Pi.single_eq_of_ne, Fin.succ_inj]

/-! ## 2. The chain rule for the affine chart -/

/-- The derivative of `u ↦ H (pullMap α β u)` is the derivative of `H` at the image point,
composed with the linear part `diagCLM β`. -/
lemma fderiv_pullMap {n : ℕ} (H : (Fin (n + 1) → ℝ) → ℝ) (α β : ℝ) (z : Fin (n + 1) → ℝ)
    (hH : DifferentiableAt ℝ H (pullMap n α β z)) :
    fderiv ℝ (fun u => H (pullMap n α β u)) z
      = (fderiv ℝ H (pullMap n α β z)).comp (diagCLM n β) := by
  have h1 := fderiv_comp (x := z) (f := pullMap n α β) (g := H) hH
    (hasFDerivAt_pullMap n α β z).differentiableAt
  rw [(hasFDerivAt_pullMap n α β z).fderiv] at h1
  exact h1

/-- Directional form of the chain rule, for the distinguished `x`-direction `0`: a factor `β`
appears. -/
lemma fderiv_pullMap_zero {n : ℕ} (H : (Fin (n + 1) → ℝ) → ℝ) (α β : ℝ) (z : Fin (n + 1) → ℝ)
    (hH : DifferentiableAt ℝ H (pullMap n α β z)) :
    fderiv ℝ (fun u => H (pullMap n α β u)) z (Pi.single 0 (1 : ℝ))
      = β * fderiv ℝ H (pullMap n α β z) (Pi.single 0 (1 : ℝ)) := by
  rw [fderiv_pullMap H α β z hH, ContinuousLinearMap.comp_apply, diagCLM_single_zero,
    ContinuousLinearMap.map_smul]
  simp

/-- Directional form of the chain rule, for the `y`-directions `i.succ`: no factor appears. -/
lemma fderiv_pullMap_succ {n : ℕ} (H : (Fin (n + 1) → ℝ) → ℝ) (α β : ℝ) (z : Fin (n + 1) → ℝ)
    (hH : DifferentiableAt ℝ H (pullMap n α β z)) (i : Fin n) :
    fderiv ℝ (fun u => H (pullMap n α β u)) z (Pi.single i.succ (1 : ℝ))
      = fderiv ℝ H (pullMap n α β z) (Pi.single i.succ (1 : ℝ)) := by
  rw [fderiv_pullMap H α β z hH, ContinuousLinearMap.comp_apply, diagCLM_single_succ]

/-! ## 3. `xcount` bookkeeping -/

lemma xcount_cons_zero {n : ℕ} (L : List (Fin (n + 1))) : xcount (0 :: L) = xcount L + 1 := by
  simp [xcount, List.filter_cons_of_pos]

lemma xcount_succ_cons {n : ℕ} (i : Fin n) (L : List (Fin (n + 1))) :
    xcount (i.succ :: L) = xcount L := by
  simp [xcount, List.filter_cons_of_neg, Fin.succ_ne_zero i]

/-! ## 4. The transport identity -/

/-- **Transport of the iterated directional derivative along the affine `x`-chart.**  For a
function `G` that is `C^{|L|}` at `pullMap α β z`, the iterated directional derivative of
`G ∘ pullMap α β` along the directions `L` at `z` is `β ^ (xcount L)` times the iterated
directional derivative of `G` at `pullMap α β z`.

Proved by induction on `L`.  In the inductive step the induction hypothesis identifies
`iterDir L' (G ∘ pullMap α β)` on a neighbourhood of `z` with
`β ^ (xcount L') * (iterDir L' G ∘ pullMap α β)` (here the smoothness hypothesis is used, which
propagates through the continuity of the chart), so the two `fderiv`s agree; then the chain rule
`fderiv_pullMap` and its directional forms `fderiv_pullMap_zero`/`fderiv_pullMap_succ` give the
result. -/
lemma iterDir_pullMap {n : ℕ} (G : (Fin (n + 1) → ℝ) → ℝ) (α β : ℝ) :
    ∀ (L : List (Fin (n + 1))) (z : Fin (n + 1) → ℝ),
      ContDiffAt ℝ L.length G (pullMap n α β z) →
      iterDir L (fun u => G (pullMap n α β u)) z =
        β ^ (xcount L) * iterDir L G (pullMap n α β z) := by
  intro L
  induction L with
  | nil =>
      intro z _
      simp [iterDir_nil, xcount]
  | cons i L' ih =>
      intro z hG
      have hG1 : ContDiffAt ℝ (L'.length + 1) G (pullMap n α β z) := hG
      -- smoothness is inherited on a neighbourhood, through the continuity of the chart
      have hev : ∀ᶠ u in 𝓝 z, ContDiffAt ℝ L'.length G (pullMap n α β u) := by
        have h1 : ∀ᶠ y in 𝓝 (pullMap n α β z), ContDiffAt ℝ (L'.length + 1) G y :=
          hG1.eventually (by simp)
        have h2 : ∀ᶠ y in 𝓝 (pullMap n α β z), ContDiffAt ℝ L'.length G y :=
          h1.mono (fun y hy => hy.of_le (by exact_mod_cast Nat.le_succ L'.length))
        exact (hasFDerivAt_pullMap n α β z).continuousAt.tendsto.eventually h2
      -- the induction hypothesis, as an eventual equality of functions
      have heq : iterDir L' (fun u => G (pullMap n α β u)) =ᶠ[𝓝 z]
          (fun u => β ^ (xcount L') * iterDir L' G (pullMap n α β u)) := by
        filter_upwards [hev] with u hu
        exact ih u hu
      have hHdiff : DifferentiableAt ℝ (iterDir L' G) (pullMap n α β z) :=
        (Work.WilG4c.iterDir_contDiffAt G L' 1 (pullMap n α β z) hG1).differentiableAt
          (by norm_num)
      have hHdiff' : DifferentiableAt ℝ (fun u => iterDir L' G (pullMap n α β u)) z :=
        hHdiff.comp z (hasFDerivAt_pullMap n α β z).differentiableAt
      have hconst : fderiv ℝ (fun u : Fin (n + 1) → ℝ =>
            β ^ (xcount L') * (iterDir L' G (pullMap n α β u))) z
          = β ^ (xcount L') • fderiv ℝ
            (fun u : Fin (n + 1) → ℝ => iterDir L' G (pullMap n α β u)) z :=
        fderiv_const_mul hHdiff' _
      have hinner : fderiv ℝ (fun u : Fin (n + 1) → ℝ => iterDir L' G (pullMap n α β u)) z
          = (fderiv ℝ (iterDir L' G) (pullMap n α β z)).comp (diagCLM n β) :=
        fderiv_pullMap (iterDir L' G) α β z hHdiff
      -- peel off the outermost derivative, in both directions
      simp only [iterDir_cons]
      induction i using Fin.cases with
      | zero =>
          rw [heq.fderiv_eq, hconst, hinner, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.comp_apply, diagCLM_single_zero,
            ContinuousLinearMap.map_smul]
          simp only [smul_eq_mul]
          rw [xcount_cons_zero, pow_succ]
          ring
      | succ i =>
          rw [heq.fderiv_eq, hconst, hinner, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.comp_apply, diagCLM_single_succ]
          simp only [smul_eq_mul, xcount_succ_cons]

/-! ## 5. The requested statement -/

theorem iterDir_pullX {n : ℕ} (G : (Fin (n + 1) → ℝ) → ℝ) (α β x : ℝ) (y : Fin n → ℝ)
    (L : List (Fin (n + 1))) (hG : ContDiffAt ℝ L.length G (Work.WilkG4c.pt (α + β * x) y)) :
    Work.WilkG4c.iterDir L
        (fun u : Fin (n + 1) → ℝ => G (Work.WilkG4c.pt (α + β * u 0) (Fin.tail u)))
        (Work.WilkG4c.pt x y) =
      β ^ (Work.WilkG4c.xcount L) *
        Work.WilkG4c.iterDir L G (Work.WilkG4c.pt (α + β * x) y) := by
  have hpt : pullMap n α β (pt x y) = pt (α + β * x) y := by
    simp [pullMap, pt]
  have h := iterDir_pullMap G α β L (pt x y) (by rw [hpt]; exact hG)
  rw [hpt] at h
  simpa only [pullMap] using h

end Work.WilG4c
