/-
  WilG4c — the *germ* form of the `hbase` producer of the §5.4 engine instantiation
  (the version of `Work.WilG4c.tnorm_curve_of_surrogate` in which the surrogate data is
  available only along the germ of the curve, and the jet bound on the surrogate is required
  only at the single relevant point).

  The whole content of `tnorm` at a point is the collection of jets of the function at that
  point, and every jet of order `≥ 1` only depends on the germ of the function; hence the
  identity `∂_M (pullback)(curveFun γ s) = 4 · J(c + s/4) - 2` between the surrogate and the
  `(T,r)`-normed function needs to hold only on a neighbourhood of the point `x`.  Two bridges
  do the job:

  * `Work.WilG4c.tnorm_congr` — the jet norm at a point depends only on the germ there;
  * `Work.WilG4c.tnorm_shrink_le` — the shrunken chart `φ'(s) = φ(c + s/4)` divides the `m`-th
    derivative by `4^m`, so the unit jet bound of the (unshrunk) surrogate is preserved; its
    proof only ever evaluates the jet hypothesis at the *single* point `c + x/4`, which is why
    the germ/pointwise version below goes through.

  The helper lemma `Work.WilG4c.tnorm_shrink_le_pt` below is the pointwise form of
  `tnorm_shrink_le`: the surrogate hypothesis is at the shrunk point `(4 c + x)/4` only, and
  the value bound is also pointwise.  The final assembly is a three-step chain
  `tnorm (G ∘ curveFun γ) x = tnorm ((G ∘ curveFun γ) ∘ (· 0)) x1
     = tnorm (4 J(c + ·/4) - 2) x1 ≤ exp 1`.
-/
import Mathlib
import Submission.Work.WilG4c.tnorm_curve_of_surrogate
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.tnorm_shrink_le
import Submission.Work.WilG4c.tnorm_congr
import Submission.Work.WilG4c.tnorm_comp_fin1
import Submission.Work.WilG4c.norm_iteratedFDeriv_rescale_le

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The pointwise (germ) form of `Work.WilG4c.tnorm_shrink_le`.**

If the surrogate `J` has unit operator norms of all orders `m ≤ r + 1` *at the single shrunk
point* `(4 c + x)/4` (`hJ`) and its value there is bounded by `1` after the affine
normalisation `y ↦ 4 y - 2` (`hval`), then the composite `u ↦ 4 · J(c + u/4) - 2` — the
shrunk-chart avatar of the derivative `∂_M (pullback)(curveFun γ ·)` — has `(T,r)`-norm at `x`
at most `e`.

The bound is the one from `tnorm_shrink_le`: the `m`-th jet of `u ↦ J(c + u/4)` at `x` is at
most `4^{-m}‖D^m J(shrink x)‖ ≤ 4^{-m}` (`Work.WilG4c.norm_iteratedFDeriv_rescale_le` with
`lam = 4`), so the `m`-th jet of `4 · J(c + ·/4) - 2` is at most `4^{1-m} ≤ 1` for `m ≥ 1`
(`Work.WilG4c.itD_mul_sub`), while the `0`-th jet is `|4 J(shrink x) - 2| ≤ 1` by `hval`.
Summing the exponential series gives the result.  No hypothesis is used away from the shrunk
point. -/
theorem tnorm_shrink_le_pt {r : ℕ} (J : (Fin 1 → ℝ) → ℝ) (c : ℝ) (x : Fin 1 → ℝ)
    (hJ : ∀ m, m ≤ r + 1 →
      ‖iteratedFDeriv ℝ m J (fun i : Fin 1 => (4 * c + x i) / 4)‖ ≤ 1)
    (hval : |4 * J (fun i : Fin 1 => (4 * c + x i) / 4) - 2| ≤ 1) :
    WilkiesDesign.CG.tnorm r (fun u : Fin 1 → ℝ => 4 * J (fun i : Fin 1 => c + u i / 4) - 2) x
      ≤ Real.exp 1 := by
  -- The shrunk-chart composite, as a function of the base variable.
  set G : (Fin 1 → ℝ) → ℝ := fun u => J (fun i => c + u i / 4) with hG
  have hGeq : G = (fun z : Fin 1 → ℝ => J (fun i => (4 * c + z i) / 4)) := by
    funext z
    simp only [hG]
    congr 1
    funext i
    ring
  -- Pointwise jet bound: `‖D^m (4 G - 2)(x)‖ ≤ 1` for all `m ≤ r`.
  have hbound : ∀ m ≤ r, ‖iteratedFDeriv ℝ m (fun u : Fin 1 → ℝ => 4 * G u - 2) x‖ ≤ 1 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · rw [hm0, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      show |4 * G x - 2| ≤ 1
      have hGx : G x = J (fun i : Fin 1 => (4 * c + x i) / 4) := by
        simp only [hG]
        congr 1
        funext i
        ring
      rw [hGx]
      exact hval
    · rw [itD_mul_sub hpos 4 2 G x, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      -- The jet of the shrunk chart composite is `4^{-m}` times the jet of `J` at the image.
      have hGresc : ‖iteratedFDeriv ℝ m G x‖ ≤ 1 / 4 := by
        have hres := Work.WilG4c.norm_iteratedFDeriv_rescale_le (N := 1) (4 : ℝ) (by norm_num)
          J (fun _ : Fin 1 => 4 * c) x m
        calc ‖iteratedFDeriv ℝ m G x‖
            = ‖iteratedFDeriv ℝ m (fun z : Fin 1 → ℝ => J (fun i => (4 * c + z i) / 4)) x‖ := by
              rw [hGeq]
          _ ≤ ‖iteratedFDeriv ℝ m J (fun i : Fin 1 => (4 * c + x i) / 4)‖ * (4 : ℝ)⁻¹ ^ m :=
              hres
          _ ≤ 1 * (4 : ℝ)⁻¹ := by
              refine mul_le_mul (hJ m (by omega))
                (pow_le_of_le_one (by norm_num) (by norm_num) (ne_of_gt hpos)) (by positivity)
                (by norm_num)
          _ = 1 / 4 := by norm_num
      nlinarith [hGresc]
  -- Sum the pointwise bounds against the exponential series.
  have hsum : WilkiesDesign.CG.tnorm r (fun u : Fin 1 → ℝ => 4 * G u - 2) x ≤
      ∑ k ∈ Finset.range (r + 1), (1 : ℝ) / (k.factorial : ℝ) := by
    rw [WilkiesDesign.CG.tnorm]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk' : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact div_le_div_of_nonneg_right (hbound k hk') (Nat.cast_nonneg _)
  have hfun : (fun u : Fin 1 → ℝ => 4 * J (fun i : Fin 1 => c + u i / 4) - 2)
      = fun u : Fin 1 → ℝ => 4 * G u - 2 := by
    funext u
    rw [hG]
  rw [hfun]
  refine hsum.trans ?_
  have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) (r + 1)
  simpa using h

/-- **The `hbase` of the engine, from surrogate data along the germ of the curve.**

`G` is the family the engine is applied to (the pullback of BNZ §5.4), `γ` the near-maximising
curve in its coordinates, and `J` the surrogate composite `((∂_M F + 2)/4) ∘ φ` along the
chart `φ`.  Here the identification `∂_M G (curveFun γ s) = 4 J(c + s/4) - 2` is known only on
the *germ* of the curve at `x` (`huM`), and the unit jet bound on `J` is required only at the
image point `c + x/4` (`hJ`) together with the value bound `|4 J(c + x/4) - 2| ≤ 1` (`hJval`) —
exactly what the clamped surrogate of Corollary 5.5 provides at the near-maximiser.

The conclusion is BNZ's `‖G^{(0,M)} ∘ (t, γ)‖_{T,r} ≤ 1`. -/
theorem tnorm_curve_of_surrogate_germ {n r : ℕ} (hr : 1 ≤ r)
    (G : (Fin (n + 1) → ℝ) → ℝ) (γ : ℝ → Fin n → ℝ)
    (J : (Fin 1 → ℝ) → ℝ) (x c : ℝ) (hc0 : 0 ≤ c) (hc3 : c ≤ 3 / 4)
    (hJ : ∀ m, m ≤ r + 1 → ‖iteratedFDeriv ℝ m J (fun _ : Fin 1 => c + x / 4)‖ ≤ 1)
    (hJval : |4 * J (fun _ : Fin 1 => c + x / 4) - 2| ≤ 1)
    (huM : Filter.EventuallyEq (nhds (fun _ : Fin 1 => x))
             (fun u : Fin 1 → ℝ => G (Work.WilkG4c.curveFun γ (u 0)))
             (fun u : Fin 1 → ℝ => 4 * J (fun _ : Fin 1 => c + u 0 / 4) - 2)) :
    WilkiesDesign.CG.tnorm r (fun s : ℝ => G (Work.WilkG4c.curveFun γ s)) x ≤ Real.exp 1 := by
  -- The point of `Fin 1 → ℝ` at which everything happens.
  set x1 : Fin 1 → ℝ := fun _ => x with hx1
  -- The shrunk point of the surrogate agrees with the point in the germ hypotheses.
  have hpt : (fun i : Fin 1 => (4 * c + x1 i) / 4) = (fun _ : Fin 1 => c + x / 4) := by
    funext i
    simp only [hx1]
    ring
  have hJ' : ∀ m, m ≤ r + 1 →
      ‖iteratedFDeriv ℝ m J (fun i : Fin 1 => (4 * c + x1 i) / 4)‖ ≤ 1 := by
    intro m hm
    rw [hpt]
    exact hJ m hm
  have hval' : |4 * J (fun i : Fin 1 => (4 * c + x1 i) / 4) - 2| ≤ 1 := by
    rw [hpt]
    exact hJval
  -- The pointwise shrink bound for the surrogate.
  have hbound := Work.WilG4c.tnorm_shrink_le_pt J c x1 hJ' hval'
  -- The two lambda forms of the surrogate (indexing `Fin 1` by `0` or by a variable) agree.
  have hfun : (fun u : Fin 1 → ℝ => 4 * J (fun _ : Fin 1 => c + u 0 / 4) - 2)
      = (fun u : Fin 1 → ℝ => 4 * J (fun i : Fin 1 => c + u i / 4) - 2) := by
    funext u
    have h : (fun _ : Fin 1 => c + u 0 / 4) = (fun i : Fin 1 => c + u i / 4) := by
      funext i
      rw [Subsingleton.elim i 0]
    rw [h]
  -- The bridge between `ℝ` and `Fin 1 → ℝ` at the level of the curve.
  have hbridge : WilkiesDesign.CG.tnorm r
        (fun u : Fin 1 → ℝ => G (Work.WilkG4c.curveFun γ (u 0))) x1
      = WilkiesDesign.CG.tnorm r (fun s : ℝ => G (Work.WilkG4c.curveFun γ s)) x :=
    Work.WilG4c.tnorm_comp_fin1 r (fun s : ℝ => G (Work.WilkG4c.curveFun γ s)) x1
  -- Everything is a jet at the single point `x`, so the germ identity suffices.
  calc WilkiesDesign.CG.tnorm r (fun s : ℝ => G (Work.WilkG4c.curveFun γ s)) x
      = WilkiesDesign.CG.tnorm r (fun u : Fin 1 → ℝ => G (Work.WilkG4c.curveFun γ (u 0))) x1 :=
        hbridge.symm
    _ = WilkiesDesign.CG.tnorm r
          (fun u : Fin 1 → ℝ => 4 * J (fun _ : Fin 1 => c + u 0 / 4) - 2) x1 :=
        Work.WilG4c.tnorm_congr r huM
    _ = WilkiesDesign.CG.tnorm r
          (fun u : Fin 1 → ℝ => 4 * J (fun i : Fin 1 => c + u i / 4) - 2) x1 := by rw [hfun]
    _ ≤ Real.exp 1 := hbound

end Work.WilG4c
