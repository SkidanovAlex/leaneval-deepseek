import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform limit of smooth functions with uniformly convergent jets is smooth

Let `U ⊆ E` be open, let `f : ℝ → E → Z` be a family of functions each `C^∞` on `U`, let `g` be the
pointwise limit of `f t` along a nontrivial filter `l` on `ℝ`, and suppose that for every `m ≥ 1`
the `m`-th jets `x ↦ iteratedFDeriv ℝ m (f t) x` converge *uniformly* on `U` to the function
`h m`.  Then `g` is `C^∞` on `U` and its jets are the limits: `iteratedFDeriv ℝ m g = h m` on `U`
for every `m ≥ 1`.

The proof is the classical "swap limit and derivative" argument, iterated.

* At level `0` we have only the pointwise convergence `h0` of `f t` (no uniform convergence is
  assumed for the functions themselves), but pointwise convergence on `U` is exactly what
  `hasFDerivAt_of_tendstoUniformlyOn` needs on the side of the functions.  The derivatives
  `fderiv ℝ (f t)` are, through the linear isometry `continuousMultilinearCurryLeftEquiv`, the
  `1`-jets of `f t`, so their uniform convergence on `U` is precisely `hm 1`.
  This yields `HasFDerivAt g (h 1 x) x` for `x ∈ U`, i.e. (because `iteratedFDeriv ℝ 1 g` is
  `continuousMultilinearCurryLeftEquiv.symm ∘ fderiv ℝ g`) the identity
  `iteratedFDeriv ℝ 1 g = h 1` on `U`.
* Inductively, the same argument applied to the families `x ↦ iteratedFDeriv ℝ m (f t) x` shows
  that the `m`-jet of `g` is differentiable on `U` with derivative the curried `(m+1)`-jet
  `h (m+1)`; equivalently `iteratedFDeriv ℝ (m+1) g = h (m+1)` on `U`.  Here the pointwise
  convergence of the `m`-jets, needed as the input of the theorem, is deduced from the uniform
  convergence `hm (m+1)` via the identity just obtained.
* `ContDiffOn ℝ ∞ g U` follows from `contDiffOn_of_differentiableOn`: all jets of `g`, viewed as
  functions on `U`, are differentiable, and on the open set `U` the "within" jets coincide with
  the ordinary ones (`iteratedFDerivWithin_of_isOpen`).
-/

namespace Work.Diff.EXT.JetGap

theorem contDiffOn_of_tendstoUniformlyOn_iteratedFDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {U : Set E} (hU : IsOpen U) {l : Filter ℝ} [Filter.NeBot l]
    (f : ℝ → E → Z) (g : E → Z)
    (h : (m : ℕ) → E → ContinuousMultilinearMap ℝ (fun _ : Fin m => E) Z)
    (hsmooth : ∀ t, ContDiffOn ℝ (⊤ : ℕ∞) (f t) U)
    (h0 : ∀ x ∈ U, Filter.Tendsto (fun t => f t x) l (nhds (g x)))
    (hm : ∀ m, 1 ≤ m → TendstoUniformlyOn (fun t x => iteratedFDeriv ℝ m (f t) x) (h m) l U) :
    ContDiffOn ℝ (⊤ : ℕ∞) g U ∧ ∀ m, 1 ≤ m → ∀ x ∈ U, iteratedFDeriv ℝ m g x = h m x := by
  -- The two facts proved simultaneously by induction on `m`:
  -- (1) the `m`-jets of `f t` converge pointwise on `U` to the `m`-jet of `g`;
  -- (2) on `U`, the `m`-jet of `g` is differentiable with derivative the curried `(m+1)`-jet
  --     `h (m+1)`.
  have key : ∀ m : ℕ,
      (∀ x ∈ U, Filter.Tendsto (fun t => iteratedFDeriv ℝ m (f t) x) l
        (nhds (iteratedFDeriv ℝ m g x))) ∧
      (∀ x ∈ U, HasFDerivAt (fun y => iteratedFDeriv ℝ m g y)
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) Z) (h (m + 1) x)) x) := by
    intro m
    induction m with
    | zero =>
      constructor
      · -- level `0`: `iteratedFDeriv ℝ 0 u = (continuousMultilinearCurryFin0 ℝ E Z).symm ∘ u`
        intro x hx
        exact (continuousMultilinearCurryFin0 ℝ E Z).symm.continuous.continuousAt.tendsto.comp
          (h0 x hx)
      · -- level `0` to level `1`: swap limit and derivative
        intro x hx
        have hunif : TendstoUniformlyOn
            (fun t x => fderiv ℝ (fun y => iteratedFDeriv ℝ 0 (f t) y) x)
            (fun x => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 => E) Z) (h 1 x))
            l U := by
          have hEq : (fun t x => fderiv ℝ (fun y => iteratedFDeriv ℝ 0 (f t) y) x)
              = fun t x => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 => E) Z)
                  (iteratedFDeriv ℝ 1 (f t) x) := by
            funext t x
            rw [fderiv_iteratedFDeriv]
            rfl
          rw [hEq]
          exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 1 => E) Z).isometry.uniformContinuous.comp_tendstoUniformlyOn
            (hm 1 le_rfl)
        have hf : ∀ t : ℝ, ∀ y ∈ U, HasFDerivAt (fun z => iteratedFDeriv ℝ 0 (f t) z)
            (fderiv ℝ (fun z => iteratedFDeriv ℝ 0 (f t) z) y) y := by
          intro t y hy
          exact (((hsmooth t).contDiffAt (hU.mem_nhds hy)).differentiableAt_iteratedFDeriv
            (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top 0))).hasFDerivAt
        have hfg : ∀ y ∈ U, Filter.Tendsto (fun t => (fun z => iteratedFDeriv ℝ 0 (f t) z) y) l
            (nhds ((fun z => iteratedFDeriv ℝ 0 g z) y)) := by
          intro y hy
          exact (continuousMultilinearCurryFin0 ℝ E Z).symm.continuous.continuousAt.tendsto.comp
            (h0 y hy)
        exact hasFDerivAt_of_tendstoUniformlyOn hU hunif hf hfg hx
    | succ m ih =>
      -- (2) at level `m` gives `iteratedFDeriv ℝ (m+1) g = h (m+1)` on `U`
      have S : ∀ x ∈ U, iteratedFDeriv ℝ (m + 1) g x = h (m + 1) x := by
        intro x hx
        have h2 : iteratedFDeriv ℝ (m + 1) g x
            = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) Z).symm
                (fderiv ℝ (fun y => iteratedFDeriv ℝ m g y) x) := rfl
        rw [h2, (ih.2 x hx).fderiv, LinearIsometryEquiv.symm_apply_apply]
      -- hence the uniform convergence at level `m+1` gives pointwise convergence
      have Rm1 : ∀ x ∈ U, Filter.Tendsto (fun t => iteratedFDeriv ℝ (m + 1) (f t) x) l
          (nhds (iteratedFDeriv ℝ (m + 1) g x)) := fun x hx =>
        ((hm (m + 1) (by omega)).congr_right (fun y hy => (S y hy).symm)).tendsto_at hx
      refine ⟨Rm1, fun x hx => ?_⟩
      -- level `m+1` to level `m+2`: swap limit and derivative once more
      have hunif : TendstoUniformlyOn
          (fun t x => fderiv ℝ (fun y => iteratedFDeriv ℝ (m + 1) (f t) y) x)
          (fun x => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 2) => E) Z)
            (h (m + 2) x)) l U := by
        have hEq : (fun t x => fderiv ℝ (fun y => iteratedFDeriv ℝ (m + 1) (f t) y) x)
            = fun t x => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 2) => E) Z)
                (iteratedFDeriv ℝ (m + 2) (f t) x) := by
          funext t x
          rw [fderiv_iteratedFDeriv]
          rfl
        rw [hEq]
        exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 2) => E) Z).isometry.uniformContinuous.comp_tendstoUniformlyOn
          (hm (m + 2) (by omega))
      have hf : ∀ t : ℝ, ∀ y ∈ U, HasFDerivAt (fun z => iteratedFDeriv ℝ (m + 1) (f t) z)
          (fderiv ℝ (fun z => iteratedFDeriv ℝ (m + 1) (f t) z) y) y := by
        intro t y hy
        exact (((hsmooth t).contDiffAt (hU.mem_nhds hy)).differentiableAt_iteratedFDeriv
          (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top (m + 1)))).hasFDerivAt
      exact hasFDerivAt_of_tendstoUniformlyOn hU hunif hf Rm1 hx
  constructor
  · -- `g` is `C^∞` on `U`: all of its iterated derivatives are differentiable there
    have D : ∀ m : ℕ, ∀ x ∈ U, HasFDerivAt (fun y => iteratedFDeriv ℝ m g y)
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) Z) (h (m + 1) x)) x :=
      fun m => (key m).2
    refine contDiffOn_of_differentiableOn (n := (⊤ : ℕ∞)) (s := U) (f := g) fun m _ => ?_
    refine DifferentiableOn.congr
      (fun x hx => (D m x hx).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
    exact iteratedFDerivWithin_of_isOpen m hU hx
  · -- and the jets of `g` are the limits `h m`
    intro m hm1 x hx
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h2 : iteratedFDeriv ℝ (k + 1) g x
        = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) Z).symm
            (fderiv ℝ (fun y => iteratedFDeriv ℝ k g y) x) := rfl
    rw [h2, ((key k).2 x hx).fderiv, LinearIsometryEquiv.symm_apply_apply]

end Work.Diff.EXT.JetGap
