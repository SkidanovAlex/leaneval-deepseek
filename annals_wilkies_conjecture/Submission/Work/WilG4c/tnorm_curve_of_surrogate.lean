/-
  WilG4c — the `hbase` producer of the §5.4 engine instantiation (plan §14.4 (D3)).

  `Work.WilkG4c.curve_bound` (BNZ Lemma 22) needs, for each multiindex `M` of `y`-directions,

      hbase :  tnorm k (fun s : ℝ => ∂_M G (curveFun γ s)) x ≤ exp 1,

  where `G` is the *pullback* family and `γ` the curve in the pullback's coordinates.  The
  output of Corollary 5.5 (`F1Affine`) gives the unit operator norms of the *surrogate*
  composite `J = ((∂_M F + 2)/4) ∘ (the affine chart)`, not of `∂_M F ∘ γ` itself.  The
  shrinking trick (BNZ's "`F^{(β)}` bounded by `1`" + the workspace's `(· + 2)/4` surrogate)
  turns that into `hbase`: with the *shrunk* chart `φ'(s) = φ(c + s/4)` one has

      ∂_M (pullback)(curveFun γ_η s) = 4 · J (c + s/4) - 2,

  and `Work.WilkG4c.tnorm_shrink_le` (the shrunken chart has derivatives divided by `4^m`, so
  the unit norm bound is preserved) gives exactly `tnorm r (that function) x ≤ exp 1`.  The
  bridge `ℝ ≃ (Fin 1 → ℝ)` is `Work.WilG4c.tnorm_comp_fin1`.
-/
import Mathlib
import Submission.Work.WilG4c.tnorm_shrink_le
import Submission.Work.WilG4c.tnorm_comp_fin1

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The `hbase` of the engine, from the surrogate data of `F1Affine`.**

`G` is the family the engine is applied to (the pullback `pullX F α β` of BNZ §5.4); `γ` is the
curve in its coordinates (the near-maximising curve, transported to the pullback's coordinates
by the shrunk chart, so that `γ_engine (s)` is the near-maximiser at the F-level coordinate
`α + β (c + s/4)`); `J` is the surrogate composite
`t ↦ ((∂_M F)(α + β t, γ(α + β t)) + 2) / 4` along the *unshrunk* chart, whose unit operator
norms up to order `r + 1` are the conclusion of Corollary 5.5, and whose values lie in
`(1/4, 3/4)` (whence `4 J - 2` is bounded by `1` in absolute value — this is the hypothesis
`hJval`, supplied by the clamped surrogate).

The conclusion is BNZ's `‖G^{(0,M)} ∘ (t, γ)‖_{T,r} ≤ 1`: the `(T,r)`-norm of the pure-y
derivative`∂_M G` along the curve of the *pullback*. -/
theorem tnorm_curve_of_surrogate {n r : ℕ} (hr : 1 ≤ r)
    (G : (Fin (n + 1) → ℝ) → ℝ) (γ : ℝ → Fin n → ℝ)
    (J : (Fin 1 → ℝ) → ℝ) (c : ℝ) (hc0 : 0 ≤ c) (hc3 : c ≤ 3 / 4)
    (hJ : ∀ m, m ≤ r + 1 → ∀ t ∈ openCube 1, ‖iteratedFDeriv ℝ m J t‖ ≤ 1)
    (hJval : ∀ t : Fin 1 → ℝ, |4 * J t - 2| ≤ 1)
    (huM : ∀ u : Fin 1 → ℝ,
      G (curveFun γ (u 0)) = 4 * J (fun _ => c + u 0 / 4) - 2)
    {x : ℝ} (hx : x ∈ I) :
    WilkiesDesign.CG.tnorm r (fun s : ℝ => G (curveFun γ s)) x ≤ Real.exp 1 := by
  have hx1 : (fun _ : Fin 1 => x) ∈ openCube 1 := by
    intro i
    exact hx
  have hmain : WilkiesDesign.CG.tnorm r
      (fun u : Fin 1 → ℝ => G (curveFun γ (u 0))) (fun _ : Fin 1 => x) ≤ Real.exp 1 :=
    Work.WilG4c.tnorm_shrink_le hr J (fun u : Fin 1 → ℝ => G (curveFun γ (u 0))) c hc0 hc3
      hJ (fun u => by rw [huM u]; exact hJval (fun _ => c + u 0 / 4)) (fun u => huM u) hx1
  rwa [Work.WilG4c.tnorm_comp_fin1 r (fun s : ℝ => G (curveFun γ s)) (fun _ : Fin 1 => x)]
    at hmain

end Work.WilkG4c
