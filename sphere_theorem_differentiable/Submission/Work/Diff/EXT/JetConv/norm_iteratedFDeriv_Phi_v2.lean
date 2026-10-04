import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.JetConv

/-- **Currying isometry for the derivative tower.**  The `m`-th iterated Fréchet derivative of the
tower `q ↦ iteratedFDeriv ℝ k u q` (a map into the space of continuous `k`-multilinear maps) has
the same norm as the `(k+m)`-th iterated Fréchet derivative of `u`: the two are matched by
currying the variables (`continuousMultilinearCurryLeftEquiv`), an isometry.

Proof by induction on `m` (generalizing `k`), with `norm_iteratedFDeriv_fderiv` shifting the
derivative on the tower to the tower of the derivative, `fderiv_iteratedFDeriv` (which is `rfl`)
replacing `fderiv ℝ (iteratedFDeriv ℝ k u)` by the curried `(k+1)`-st jet, and
`LinearIsometryEquiv.norm_iteratedFDeriv_comp_left` (which needs no differentiability) to remove
the currying isometry. -/
theorem norm_iteratedFDeriv_iteratedFDeriv_curry_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (u : E → Z) (x : E) (m k : ℕ) :
    ‖iteratedFDeriv ℝ m (iteratedFDeriv ℝ k u) x‖ = ‖iteratedFDeriv ℝ (k + m) u x‖ := by
  induction m generalizing k with
  | zero =>
    rw [Nat.add_zero, norm_iteratedFDeriv_zero]
  | succ m ih =>
    have h1 : ‖iteratedFDeriv ℝ (m + 1) (iteratedFDeriv ℝ k u) x‖
        = ‖iteratedFDeriv ℝ m (fderiv ℝ (iteratedFDeriv ℝ k u)) x‖ :=
      (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := iteratedFDeriv ℝ k u) (x := x) (n := m)).symm
    have h2 : ‖iteratedFDeriv ℝ m (fderiv ℝ (iteratedFDeriv ℝ k u)) x‖
        = ‖iteratedFDeriv ℝ m (iteratedFDeriv ℝ (k + 1) u) x‖ := by
      rw [fderiv_iteratedFDeriv (𝕜 := ℝ) (f := u) (n := k)]
      exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left _ _ _ _
    rw [h1, h2, ih (k + 1), show k + (m + 1) = (k + 1) + m from by omega]

/-- **Bound on the jets of the `k`-th time derivative.**  Let `u : ℝ × E → Z` be `C^∞` at `p`.
Then the `m`-th ambient iterated Fréchet derivative at `p` of the function
`q ↦ (iteratedFDeriv ℝ k u q) (fun _ : Fin k => ((1 : ℝ), 0))` (the `k`-th time derivative of `u`,
written as the evaluation of the `k`-th full jet on the tuple `((1,0),…,(1,0))`) is bounded by a
constant depending only on `k, m` and `E`, times `‖iteratedFDeriv ℝ (k + m) u p‖`.

Route (reviewers agree `C = 1` works): the function is `L ∘ (iteratedFDeriv ℝ k u)` for the
continuous linear map `L = Φ ↦ Φ (fun _ => (1,0))`, whose operator norm is `1`; post-composition with
`L` is controlled by `ContinuousLinearMap.norm_iteratedFDeriv_comp_left` (needing
`ContDiffAt ℝ ⊤ (iteratedFDeriv ℝ k u) p`, which follows from `ContDiffAt ℝ ⊤ u p`), and the
identification `‖iteratedFDeriv ℝ m (iteratedFDeriv ℝ k u) p‖ = ‖iteratedFDeriv ℝ (k+m) u p‖` is the
currying isometry (`continuousMultilinearCurryLeftEquiv`, `norm_fderiv_iteratedFDeriv`), which Mathlib
packages only for `k = 1` — the general `k` is a reindexing along `Fin (k+m) ≃ Fin (m+k)`.  Pure
Mathlib. -/
theorem norm_iteratedFDeriv_Phi_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (u : ℝ × E → Z) (p : ℝ × E), ContDiffAt ℝ (⊤ : ℕ∞) u p →
      ‖iteratedFDeriv ℝ m
        (fun q : ℝ × E => (iteratedFDeriv ℝ k u q) (fun _ : Fin k => ((1 : ℝ), 0))) p‖
        ≤ C * ‖iteratedFDeriv ℝ (k + m) u p‖ := by
  refine ⟨1, zero_le_one, ?_⟩
  intro Z _ _ u p hu
  -- `L` is the evaluation of a `k`-multilinear map at the fixed tuple `((1,0),…,(1,0))`.
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × E) Z →L[ℝ] Z :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × E) Z (fun _ : Fin k => ((1 : ℝ), 0))
  have hLapply : ∀ Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × E) Z,
      L Φ = Φ (fun _ : Fin k => ((1 : ℝ), 0)) := fun Φ => ContinuousMultilinearMap.apply_apply
  -- `‖L‖ ≤ 1`, because each `‖((1:ℝ), 0)‖ = 1`.
  have hLnorm : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound L zero_le_one (fun Φ => ?_)
    rw [hLapply Φ]
    calc ‖Φ (fun _ : Fin k => ((1 : ℝ), 0))‖
        ≤ ‖Φ‖ * ∏ i : Fin k, ‖((1 : ℝ), (0 : E))‖ := Φ.le_opNorm _
      _ = ‖Φ‖ * 1 := by simp
      _ = 1 * ‖Φ‖ := by ring
  have hfun : (fun q : ℝ × E => (iteratedFDeriv ℝ k u q) (fun _ : Fin k => ((1 : ℝ), 0)))
      = ⇑L ∘ iteratedFDeriv ℝ k u := by
    funext q
    exact (hLapply (iteratedFDeriv ℝ k u q)).symm
  rw [hfun]
  -- the tower `q ↦ iteratedFDeriv ℝ k u q` is smooth.
  have hf : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (iteratedFDeriv ℝ k u) p :=
    hu.iteratedFDeriv_right (by norm_num)
  calc ‖iteratedFDeriv ℝ m (⇑L ∘ iteratedFDeriv ℝ k u) p‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ m (iteratedFDeriv ℝ k u) p‖ :=
        L.norm_iteratedFDeriv_comp_left hf (WithTop.coe_le_coe.mpr le_top)
    _ = ‖L‖ * ‖iteratedFDeriv ℝ (k + m) u p‖ := by
        rw [norm_iteratedFDeriv_iteratedFDeriv_curry_v2 u p m k]
    _ ≤ 1 * ‖iteratedFDeriv ℝ (k + m) u p‖ :=
        mul_le_mul_of_nonneg_right hLnorm (norm_nonneg _)

end Work.Diff.EXT.JetConv
