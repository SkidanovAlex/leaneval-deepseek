import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.T.clairaut_fderiv_apply

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Coordinate `2`-jet calculus for quasilinear systems of the form `∂ₜu = Φ(·, Ju)`

This file is a working copy of the content of `Submission/Work/Diff/EXT/pde_core.lean`, moved into
the namespace `Work.Diff.EXT.JetsCore` and repaired for the current Mathlib (in the original file
two occurrences of `ContDiffAt.clm_apply _ contDiff_const` must read `contDiffAt_const`).  The
mathematics and the proof scripts are unchanged.  It provides the coordinate `2`-jet `cJet`, the
iterated time derivatives `Dfun`, the universal functions `PsiC` and the representation theorem
`Aseq_eq_PsiC` on which `jets_bounded_of_pde` rests; the separate namespace avoids a clash with the
original file, should the latter be repaired in place.

This file (area `EXT`, splice step) contains the *calculus* part of the restart argument, in the
coordinate setting of `splice_defs.lean`:

* `pDer u k` — the coordinate partial derivative of `u : ℝ × E → F` in the direction of the `k`-th
  basis vector of the model space `E`;
* `cJet u` — the *coordinate* `2`-jet of `u`: the value, the first and the second coordinate
  partial derivatives;
* `tDerFun u` — the time derivative of `u`;
* `Dfun u i` — the `i`-th time derivative of `u`;
* `Aseq Φ u` — the sequence `A₀ = Φ(·, Ju)`, `A_{j+1} = ∂ₜA_j`;
* `PsiC Φ j` — the universal (smooth) function expressing `∂ₜ^j(Φ(·,Ju))` through the coordinate
  `2`-jets of `u, ∂ₜu, …, ∂ₜ^j u` (defined by the recursion
  `PsiC Φ (j+1) (y, ζ) = D(PsiC Φ j)(y, ζ₀,…,ζ_{j-1})[(0, ζ₁,…,ζ_j)]`).

The main output is `Aseq_eq_PsiC` (the universal representation), together with the Clairaut step
`hasDerivAt_cJet` (the time derivative of the coordinate `2`-jet is the coordinate `2`-jet of the
time derivative) on which it rests.
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.JetsCore

set_option linter.unusedSectionVars false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The coordinate partial derivative of `u : ℝ × E → F` in the direction of the `k`-th basis
vector of the model space. -/
noncomputable def pDer (u : ℝ × E → F) (k : Fin (Module.finrank ℝ E)) : ℝ × E → F :=
  fun p => fderiv ℝ (fun y : E => u (p.1, y)) p.2 (Module.finBasis ℝ E k)

/-- The **coordinate `2`-jet** of `u : ℝ × E → F`: the value of `u`, its first and its second
coordinate partial derivatives. -/
noncomputable def cJet (u : ℝ × E → F) :
    ℝ × E → (F × (Fin (Module.finrank ℝ E) → F) ×
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F)) :=
  fun p => (u p, fun k => pDer u k p, fun k l => pDer (pDer u l) k p)

theorem cJet_apply (u : ℝ × E → F) (p : ℝ × E) :
    cJet u p = (u p, fun k => pDer u k p, fun k l => pDer (pDer u l) k p) := rfl

/-- The time derivative of `u : ℝ × E → F` as a function on `ℝ × E`. -/
noncomputable def tDerFun (u : ℝ × E → F) : ℝ × E → F :=
  fun p => deriv (fun s : ℝ => u (s, p.2)) p.1

/-- `Aseq Φ u j` is the `j`-th time derivative of the right hand side `Φ(·, Ju)` of the system
along `u`. -/
noncomputable def Aseq (Φ : E × (F × (Fin (Module.finrank ℝ E) → F) ×
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F)) → F)
    (u : ℝ × E → F) : ℕ → (ℝ × E → F)
  | 0 => fun p => Φ (p.2, cJet u p)
  | (j + 1) => tDerFun (Aseq Φ u j)

/-- The universal function expressing `A_j = ∂ₜ^j (Φ(·,Ju))` through the coordinate `2`-jets of
`u, ∂ₜu, …, ∂ₜ^j u`, defined by the recursion
`PsiC Φ (j+1) (y, ζ) = D(PsiC Φ j)(y, ζ₀,…,ζ_{j-1})[(0, ζ₁,…,ζ_j)]`. -/
noncomputable def PsiC (Φ : E × (F × (Fin (Module.finrank ℝ E) → F) ×
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F)) → F) :
    (j : ℕ) → (E × (Fin (j + 1) → (F × (Fin (Module.finrank ℝ E) → F) ×
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F)))) → F
  | 0 => fun p => Φ (p.1, p.2 0)
  | (j + 1) => fun p =>
      (fderiv ℝ (fun q => PsiC Φ j q) (p.1, fun k : Fin (j + 1) => p.2 k.castSucc))
        ((0 : E), fun i : Fin (j + 1) => p.2 i.succ)

/-! ## The coordinate partial derivatives and Clairaut's theorem -/

/-- The Fréchet derivative of the partial map `y ↦ u (q.1, y)` is the total Fréchet derivative of
`u` at `q`, restricted to the second factor. -/
theorem fderiv_partial_eq (u : ℝ × E → F) {q : ℝ × E} (hu : DifferentiableAt ℝ u q) :
    fderiv ℝ (fun y : E => u (q.1, y)) q.2
      = (fderiv ℝ u q).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have hφ : HasFDerivAt (fun y : E => (q.1, y)) (ContinuousLinearMap.inr ℝ ℝ E) q.2 :=
    hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2
  exact (hu.hasFDerivAt.comp q.2 hφ).fderiv

/-- A coordinate partial derivative of a `C^{N+1}` function is `C^N`. -/
theorem contDiffAt_pDer_succ {u : ℝ × E → F} {p : ℝ × E} {N : ℕ}
    (hu : ContDiffAt ℝ ((N + 1 : ℕ) : WithTop ℕ∞) u p) (k : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (N : WithTop ℕ∞) (pDer u k) p := by
  have hfd : ContDiffAt ℝ (N : WithTop ℕ∞) (fun q : ℝ × E => fderiv ℝ u q) p :=
    hu.fderiv_right (hmn := by simp)
  have h1 : ContDiffAt ℝ (N : WithTop ℕ∞)
      (fun q : ℝ × E => (fderiv ℝ u q) (0, Module.finBasis ℝ E k)) p :=
    hfd.clm_apply contDiffAt_const
  refine h1.congr_of_eventuallyEq ?_
  have hD : ∀ᶠ q : ℝ × E in 𝓝 p, DifferentiableAt ℝ u q :=
    ((hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ((N + 1 : ℕ) : WithTop ℕ∞))).eventually
      (by simp)).mono (fun q hq => hq.differentiableAt (by simp))
  filter_upwards [hD] with q hq
  simp only [pDer, fderiv_partial_eq u hq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]

/-- **Clairaut for the coordinate partials**: the time derivative of `∂_k u` is `∂_k (∂ₜu)`. -/
theorem hasDerivAt_pDer {u : ℝ × E → F} {p : ℝ × E} (hu : ContDiffAt ℝ (2 : ℕ) u p)
    (k : Fin (Module.finrank ℝ E)) :
    HasDerivAt (fun s : ℝ => pDer u k (s, p.2)) (pDer (tDerFun u) k p) p.1 :=
  Work.Diff.T.clairaut_fderiv_apply hu (Module.finBasis ℝ E k)

/-- The time derivative of `∂_l u` is `∂_l` of the time derivative of `u`, as functions near `p`. -/
theorem tDerFun_pDer_eventuallyEq {u : ℝ × E → F} {p : ℝ × E}
    (hu : ContDiffAt ℝ (3 : ℕ) u p) (l : Fin (Module.finrank ℝ E)) :
    tDerFun (pDer u l) =ᶠ[𝓝 p] pDer (tDerFun u) l := by
  filter_upwards [((hu.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (3 : ℕ))).eventually (by simp))]
    with q hq
  have h := hasDerivAt_pDer hq l
  simpa only [tDerFun] using h.deriv

/-- The time derivative of the composition `∂_k (∂_l u)` is `∂_k (∂_l (∂ₜu))`. -/
theorem hasDerivAt_pDer_pDer {u : ℝ × E → F} {p : ℝ × E} (hu : ContDiffAt ℝ (4 : ℕ) u p)
    (k l : Fin (Module.finrank ℝ E)) :
    HasDerivAt (fun s : ℝ => pDer (pDer u l) k (s, p.2))
      (pDer (pDer (tDerFun u) l) k p) p.1 := by
  have hpl : ContDiffAt ℝ (2 : ℕ) (pDer u l) p :=
    contDiffAt_pDer_succ (N := 2) (hu.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ (4 : ℕ))) l
  have h1 : HasDerivAt (fun s : ℝ => pDer (pDer u l) k (s, p.2))
      (pDer (tDerFun (pDer u l)) k p) p.1 :=
    hasDerivAt_pDer hpl k
  have hfg : (fun y : E => tDerFun (pDer u l) (p.1, y)) =ᶠ[𝓝 p.2]
      (fun y : E => pDer (tDerFun u) l (p.1, y)) := by
    have htend : Tendsto (fun y : E => (p.1, y)) (𝓝 p.2) (𝓝 p) := by
      rw [nhds_prod_eq]
      exact tendsto_const_nhds.prodMk tendsto_id
    exact htend.eventually
      (tDerFun_pDer_eventuallyEq (hu.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ (4 : ℕ))) l)
  have h2 : pDer (tDerFun (pDer u l)) k p = pDer (pDer (tDerFun u) l) k p := by
    rw [pDer, pDer, hfg.fderiv_eq]
  rw [h2] at h1
  exact h1

/-- **Clairaut, jet form**: the time derivative of the coordinate `2`-jet of `u` is the coordinate
`2`-jet of the time derivative of `u`. -/
theorem hasDerivAt_cJet {u : ℝ × E → F} {p : ℝ × E} (hu : ContDiffAt ℝ (4 : ℕ) u p) :
    HasDerivAt (fun s : ℝ => cJet u (s, p.2)) (cJet (tDerFun u) p) p.1 := by
  have h1 : HasDerivAt (fun s : ℝ => u (s, p.2)) (tDerFun u p) p.1 := by
    have hd : DifferentiableAt ℝ (fun s : ℝ => u (s, p.2)) p.1 :=
      ((hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ (4 : ℕ))).differentiableAt (by simp)).comp
        p.1 ((hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2).differentiableAt)
    simpa [tDerFun] using hd.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => fun k : Fin (Module.finrank ℝ E) => pDer u k (s, p.2))
      (fun k : Fin (Module.finrank ℝ E) => pDer (tDerFun u) k p) p.1 :=
    hasDerivAt_pi.2 fun k =>
      hasDerivAt_pDer (hu.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (4 : ℕ))) k
  have h3 : HasDerivAt
      (fun s : ℝ => fun k l : Fin (Module.finrank ℝ E) => pDer (pDer u l) k (s, p.2))
      (fun k l : Fin (Module.finrank ℝ E) => pDer (pDer (tDerFun u) l) k p) p.1 :=
    hasDerivAt_pi.2 fun k => hasDerivAt_pi.2 fun l => hasDerivAt_pDer_pDer hu k l
  exact h1.prodMk (h2.prodMk h3)

/-! ## The iterated time derivatives -/

/-- The `i`-th time derivative of `u`, as a function on `ℝ × E`. -/
noncomputable def Dfun (u : ℝ × E → F) (i : ℕ) : ℝ × E → F :=
  fun p => iteratedDeriv i (fun s : ℝ => u (s, p.2)) p.1

theorem Dfun_zero (u : ℝ × E → F) : Dfun u 0 = u := by
  funext p
  simp [Dfun]

theorem Dfun_succ (u : ℝ × E → F) (i : ℕ) : Dfun u (i + 1) = tDerFun (Dfun u i) := by
  funext p
  simp only [Dfun, tDerFun, iteratedDeriv_succ]

/-- `tDerFun w` agrees with the evaluation of the total derivative of `w` on `(1,0)`. -/
theorem tDerFun_eq_fderiv {w : ℝ × E → F} {q : ℝ × E} (hw : DifferentiableAt ℝ w q) :
    tDerFun w q = (fderiv ℝ w q) (1, 0) := by
  have hφ : HasFDerivAt (fun s : ℝ => (s, q.2)) (ContinuousLinearMap.inl ℝ ℝ E) q.1 :=
    hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2
  have h : HasDerivAt (fun s : ℝ => w (s, q.2)) ((fderiv ℝ w q) (1, 0)) q.1 :=
    (hw.hasFDerivAt.comp q.1 hφ).hasDerivAt
  exact h.deriv

/-- The time derivative of a `C^{N+1}` function is `C^N`. -/
theorem contDiffAt_tDerFun {w : ℝ × E → F} {q : ℝ × E} {N : ℕ}
    (hw : ContDiffAt ℝ ((N + 1 : ℕ) : WithTop ℕ∞) w q) :
    ContDiffAt ℝ (N : WithTop ℕ∞) (tDerFun w) q := by
  have hfd : ContDiffAt ℝ (N : WithTop ℕ∞) (fun q' : ℝ × E => fderiv ℝ w q') q :=
    hw.fderiv_right (hmn := by simp)
  have h1 : ContDiffAt ℝ (N : WithTop ℕ∞)
      (fun q' : ℝ × E => (fderiv ℝ w q') (1, 0)) q :=
    hfd.clm_apply contDiffAt_const
  refine h1.congr_of_eventuallyEq ?_
  have hD : ∀ᶠ q' : ℝ × E in 𝓝 q, DifferentiableAt ℝ w q' :=
    ((hw.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ((N + 1 : ℕ) : WithTop ℕ∞))).eventually
      (by simp)).mono (fun q' hq' => hq'.differentiableAt (by simp))
  filter_upwards [hD] with q' hq'
  exact tDerFun_eq_fderiv hq'

/-- **All the iterated time derivatives of a `C^∞` function are `C^∞`** (at every finite order). -/
theorem contDiffAt_Dfun {u : ℝ × E → F} {q : ℝ × E}
    (hu : ∀ N : ℕ, ContDiffAt ℝ (N : WithTop ℕ∞) u q) (i N : ℕ) :
    ContDiffAt ℝ (N : WithTop ℕ∞) (Dfun u i) q := by
  induction i generalizing N with
  | zero => simpa only [Dfun_zero] using hu N
  | succ i ih =>
      rw [Dfun_succ]
      exact contDiffAt_tDerFun (by simpa only [Nat.cast_add, Nat.cast_one] using ih (N + 1))

/-- The strong form of `C^∞`-ness (all finite orders) at a point of an open set. -/
theorem contDiffAt_all_of_contDiffOn {u : ℝ × E → F} {U : Set (ℝ × E)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) {q : ℝ × E} (hq : q ∈ U) :
    ∀ N : ℕ, ContDiffAt ℝ (N : WithTop ℕ∞) u q :=
  fun N => (hu.contDiffAt (hU.mem_nhds hq)).of_le (by simp)

/-! ## Smoothness of the universal function -/

/-- The universal function `PsiC Φ j` is `C^∞` whenever `Φ` is. -/
theorem contDiff_PsiC {Φ : E × (F × (Fin (Module.finrank ℝ E) → F) ×
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F)) → F}
    (hΦ : ContDiff ℝ ∞ Φ) (j : ℕ) : ContDiff ℝ ∞ (PsiC Φ j) := by
  induction j with
  | zero =>
      have h1 : ContDiff ℝ ∞ (fun p : E × (Fin (0 + 1) → (F ×
          (Fin (Module.finrank ℝ E) → F) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F))) => p.2 0) :=
        (contDiff_apply (𝕜 := ℝ) (n := ∞) (ι := Fin (0 + 1)) (i := (0 : Fin (0 + 1)))
          (E := (F × (Fin (Module.finrank ℝ E) → F) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F)))).comp contDiff_snd
      rw [show PsiC Φ 0 = fun p : E × (Fin (0 + 1) → (F ×
          (Fin (Module.finrank ℝ E) → F) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F))) => Φ (p.1, p.2 0)
        from rfl]
      exact hΦ.comp (contDiff_fst.prodMk h1)
  | succ j ih =>
      have hfd : ContDiff ℝ ∞ (fderiv ℝ (PsiC Φ j)) := ih.fderiv_right (hmn := by simp)
      rw [show PsiC Φ (j + 1) = fun p : E × (Fin (j + 1 + 1) → (F ×
          (Fin (Module.finrank ℝ E) → F) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F))) =>
          (fderiv ℝ (PsiC Φ j) (p.1, fun k : Fin (j + 1) => p.2 k.castSucc))
            ((0 : E), fun i : Fin (j + 1) => p.2 i.succ) from rfl]
      have harg : ContDiff ℝ ∞ (fun p : E × (Fin (j + 1 + 1) → (F ×
          (Fin (Module.finrank ℝ E) → F) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F))) =>
          (p.1, fun k : Fin (j + 1) => p.2 k.castSucc)) :=
        contDiff_fst.prodMk (contDiff_pi.2 fun k =>
          (contDiff_apply (𝕜 := ℝ) (n := ∞) (ι := Fin (j + 1 + 1)) (i := k.castSucc) (E := (F ×
            (Fin (Module.finrank ℝ E) → F) ×
            (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F)))).comp
            contDiff_snd)
      have hval : ContDiff ℝ ∞ (fun p : E × (Fin (j + 1 + 1) → (F ×
          (Fin (Module.finrank ℝ E) → F) ×
          (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F))) =>
          ((0 : E), fun i : Fin (j + 1) => p.2 i.succ)) :=
        (contDiff_const (c := (0 : E))).prodMk (contDiff_pi.2 fun i =>
          (contDiff_apply (𝕜 := ℝ) (n := ∞) (ι := Fin (j + 1 + 1)) (i := i.succ) (E := (F ×
            (Fin (Module.finrank ℝ E) → F) ×
            (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F)))).comp contDiff_snd)
      exact (hfd.comp harg).clm_apply hval

/-! ## The universal representation -/

/-- **The universal representation of the time derivatives of `Φ(·,Ju)`.**  For `u` of class `C^∞`
on the open set `U`, the `j`-th time derivative of `Φ(·,Ju)` at `p ∈ U` is `PsiC Φ j` evaluated at
the coordinate `2`-jets of `u, ∂ₜu, …, ∂ₜ^j u` at `p`. -/
theorem Aseq_eq_PsiC {Φ : E × (F × (Fin (Module.finrank ℝ E) → F) ×
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → F)) → F}
    (hΦ : ContDiff ℝ ∞ Φ) {u : ℝ × E → F} {U : Set (ℝ × E)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ ∞ u U) (j : ℕ) :
    ∀ p ∈ U, Aseq Φ u j p = PsiC Φ j (p.2, fun i : Fin (j + 1) => cJet (Dfun u i) p) := by
  induction j with
  | zero =>
      intro p hp
      exact congrArg (fun g : ℝ × E → F => Φ (p.2, cJet g p)) (Dfun_zero u).symm
  | succ j ih =>
      intro p hp
      have huN : ∀ N : ℕ, ContDiffAt ℝ (N : WithTop ℕ∞) u p :=
        contDiffAt_all_of_contDiffOn hU hu hp
      have h2 : deriv (fun s : ℝ => Aseq Φ u j (s, p.2)) p.1
          = deriv (fun s : ℝ => PsiC Φ j (p.2, fun i : Fin (j + 1) => cJet (Dfun u i) (s, p.2)))
              p.1 := by
        refine Filter.EventuallyEq.deriv_eq ?_
        have htend : Tendsto (fun s : ℝ => (s, p.2)) (𝓝 p.1) (𝓝 p) := by
          rw [nhds_prod_eq]
          exact tendsto_id.prodMk tendsto_const_nhds
        filter_upwards [htend.eventually (hU.mem_nhds hp)] with s hs
        exact ih (s, p.2) hs
      have hc : HasDerivAt (fun s : ℝ => (p.2, fun i : Fin (j + 1) => cJet (Dfun u i) (s, p.2)))
          ((0 : E), fun i : Fin (j + 1) => cJet (Dfun u (i + 1)) p) p.1 := by
        refine HasDerivAt.prodMk (hasDerivAt_const (x := p.1) (c := p.2)) ?_
        refine hasDerivAt_pi.2 (fun i => ?_)
        have hD : ContDiffAt ℝ (4 : ℕ) (Dfun u i) p := by
          have h := contDiffAt_Dfun huN i 4
          simpa using h
        have hder := hasDerivAt_cJet (E := E) hD
        simpa only [Dfun_succ] using hder
      have hPsi : HasFDerivAt (PsiC Φ j)
          (fderiv ℝ (PsiC Φ j) (p.2, fun i : Fin (j + 1) => cJet (Dfun u i) p))
          (p.2, fun i : Fin (j + 1) => cJet (Dfun u i) p) :=
        ((contDiff_PsiC hΦ j).contDiffAt.differentiableAt (by simp)).hasFDerivAt
      have h4 : HasDerivAt
          (fun s : ℝ => PsiC Φ j (p.2, fun i : Fin (j + 1) => cJet (Dfun u i) (s, p.2)))
          ((fderiv ℝ (PsiC Φ j) (p.2, fun i : Fin (j + 1) => cJet (Dfun u i) p))
            ((0 : E), fun i : Fin (j + 1) => cJet (Dfun u (i + 1)) p)) p.1 :=
        hPsi.comp_hasDerivAt p.1 hc
      rw [show Aseq Φ u (j + 1) p
            = deriv (fun s : ℝ => Aseq Φ u j (s, p.2)) p.1 from rfl, h2, h4.deriv]
      rw [show PsiC Φ (j + 1) (p.2, fun i : Fin (j + 2) => cJet (Dfun u i) p)
            = (fderiv ℝ (PsiC Φ j) (p.2, fun k : Fin (j + 1) => cJet (Dfun u k) p))
              ((0 : E), fun i : Fin (j + 1) => cJet (Dfun u (i + 1)) p) from rfl]

end Work.Diff.EXT.JetsCore
