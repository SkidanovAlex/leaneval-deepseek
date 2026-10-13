/-
  WilG4c — the analytic core of BNZ §5.4: the curve bound.

  BNZ Lemma 22 (our `Work.WilG4c.tnorm_curve_system_w`, the *weighted* form) bounds
  `‖∂_x^j ∂_M G ∘ (t,γ)‖_{T,k-j-|M|}` by `e·(k(1+ne))^j`.  This file instantiates the engine for
  the concrete family

      `u j M (s) := ∂_x^j ∂_M G (curveFun γ s)`,

  i.e. it discharges `hsm`, `hsmg` and `hchain` from the smoothness of `G` near the curve point,
  the smoothness of `γ`, the base bound `hbase` (Corollary 19 applied to the tuple of composites)
  and the unit bounds `hgd` of `γᵢ'`.  The resulting `curve_bound` is the input `hcurve` of
  `Work.WilkG4c.subdiv_normle`: at the chosen near-maximiser `γ x` the derivative `∂^{(j,M)}` is at
  most `e (r(1+ne))^j`, hence (by the near-maximiser transfer) the whole fibre is bounded by twice
  that.

  Smoothness bookkeeping.  The weighted engine asks for `ContDiffAt ℝ (k-j-|M|) (u j M) x`; since
  `u j M` is `iterDir L G ∘ curveFun γ` with `|L| = j+|M|`, this is exactly what `G ∈ C^k` and
  `γ ∈ C^k` give (no extra derivatives of `G` are needed).  This is the reason for the weighted
  form of the engine.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.IterDirAux
import Submission.Work.WilG4c.iterDir_eq_iteratedFDeriv
import Submission.Work.WilG4c.tnorm_curve_system_w
import Submission.Work.WilG4c.curve_chain_ineq_w
import Submission.Work.WilG4c.hasDerivAt_iterDir_curve
import Submission.Work.WilG4c.tnorm_congr

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical

open scoped BigOperators Topology

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- Combined form of `Work.WilG4c.iterDir_contDiffAt` with the order arithmetic kept in `ℕ`:
an iterated directional derivative of a `C^K` function is `C^{k'}` when `|L| + k' = K`. -/
private theorem iterDir_contDiffAt_of_add {m : ℕ} (G : (Fin m → ℝ) → ℝ) (L : List (Fin m))
    {k' K : ℕ} (h : L.length + k' = K) (z : Fin m → ℝ) (hG : ContDiffAt ℝ K G z) :
    ContDiffAt ℝ k' (iterDir L G) z := by
  subst h
  exact Work.WilG4c.iterDir_contDiffAt G L k' z hG

/-- The curve `t ↦ (t, γ t)` is `C^N` at `x` as soon as every `γᵢ` is. -/
private theorem curveFun_contDiffAt {n : ℕ} {γ : ℝ → Fin n → ℝ} {x : ℝ} {N : ℕ}
    (h : ∀ i : Fin n, ContDiffAt ℝ N (fun s => γ s i) x) : ContDiffAt ℝ N (curveFun γ) x := by
  rw [contDiffAt_pi]
  intro i
  induction i using Fin.cases with
  | zero =>
    have he : (fun s : ℝ => curveFun γ s 0) = fun s : ℝ => s := by
      funext s; rw [curveFun_zero]
    rw [he]; exact contDiffAt_id
  | succ i =>
    have he : (fun s : ℝ => curveFun γ s i.succ) = fun s : ℝ => γ s i := by
      funext s; rw [curveFun_succ]
    rw [he]; exact h i

/-- The `k = 0` summand of the jet norm: `|f x| ≤ tnorm r f x`. -/
theorem abs_le_tnorm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ) (f : E → ℝ)
    (x : E) : |f x| ≤ tnorm r f x := by
  have hmem : (0 : ℕ) ∈ Finset.range (r + 1) := Finset.mem_range.mpr (Nat.succ_pos r)
  have h := Finset.single_le_sum (s := Finset.range (r + 1))
    (f := fun k : ℕ => jetCoeff k f x) (fun k _ => jetCoeff_nonneg k f x) hmem
  rw [tnorm_eq_sum_jetCoeff]
  calc |f x| = ‖f x‖ := Real.norm_eq_abs _
    _ = jetCoeff 0 f x := (jetCoeff_zero f x).symm
    _ ≤ ∑ k ∈ Finset.range (r + 1), jetCoeff k f x := h

/-- **The curve bound of BNZ §5.4.**  Let `G : ℝ^{n+1} → ℝ` be `C^k` near the curve point
`curveFun γ x` and let `γ` be `C^k` there, with

* `hbase`: the pure-`y` composites `∂_M G ∘ (t,γ)` have jet norm `≤ e` up to order `k`
  (this is BNZ Corollary 19 applied to the tuple, cf. `StepHigherPlan.md` §2.3);
* `hgd`: `γᵢ'` is bounded by `1` in all derivative norms up to order `k`.

Then every derivative `∂_x^j ∂_M G` at the curve point, with `j + |M| ≤ k ≤ r`, is bounded by
`e (r(1+ne))^j`. -/
theorem curve_bound {n r : ℕ} (G : (Fin (n + 1) → ℝ) → ℝ) (γ : ℝ → Fin n → ℝ) (x : ℝ)
    (k : ℕ) (hk : k ≤ r)
    (hG : ContDiffAt ℝ k G (curveFun γ x))
    (hγc : ∀ i : Fin n, ContDiffAt ℝ k (fun s => γ s i) x)
    (hbase : ∀ M : List (Fin n), M.length ≤ k →
      tnorm k (fun s => iterDir (M.map Fin.succ) G (curveFun γ s)) x ≤ Real.exp 1)
    (hgd : ∀ i : Fin n, ∀ m ≤ k,
      ‖iteratedFDeriv ℝ m (fun s => deriv (fun u => γ u i) s) x‖ ≤ 1)
    (hsmoothg : ∀ i : Fin n, ContDiffAt ℝ k (fun s => deriv (fun u => γ u i) s) x) :
    ∀ (j : ℕ) (M : List (Fin n)), M.length + j ≤ k →
      |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G (curveFun γ x)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j := by
  intro j M hMj
  -- `u j M := ∂_x^j ∂_M G ∘ curveFun γ`, `gd i := (γᵢ)'`
  have hsm : ∀ (j : ℕ) (M : List (Fin n)), M.length + j ≤ k →
      ContDiffAt ℝ (k - j - M.length)
        (fun s => iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
          (curveFun γ s)) x := by
    intro j M hMj
    have hlen : (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ).length = j + M.length := by
      rw [List.length_append, List.length_replicate, List.length_map]
    have hk' : (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ).length
        + (k - j - M.length) = k := by
      rw [hlen]; omega
    have h1 : ContDiffAt ℝ (k - j - M.length)
        (iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G) (curveFun γ x) :=
      iterDir_contDiffAt_of_add G _ hk' (curveFun γ x) hG
    have h2 : ContDiffAt ℝ (k - j - M.length) (curveFun γ) x :=
      curveFun_contDiffAt (fun i => (hγc i).of_le (by
        show ((k - j - M.length : ℕ) : WithTop ℕ∞) ≤ ((k : ℕ) : WithTop ℕ∞)
        exact_mod_cast (show k - j - M.length ≤ k by omega)))
    simpa only [Function.comp_def] using ContDiffAt.comp x h1 h2
  have hchain : ∀ (j : ℕ) (M : List (Fin n)), M.length + (j + 1) ≤ k →
      tnorm (k - (j + 1) - M.length)
          (fun s => iterDir (List.replicate (j + 1) (0 : Fin (n + 1)) ++ M.map Fin.succ) G
            (curveFun γ s)) x ≤
        tnorm (k - (j + 1) - M.length)
            (fun s => deriv (fun w => iterDir
              (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G (curveFun γ w)) s) x +
        ∑ i : Fin n, tnorm (k - (j + 1) - M.length)
          (fun s => iterDir (List.replicate j (0 : Fin (n + 1)) ++ (i :: M).map Fin.succ) G
            (curveFun γ s) * deriv (fun u => γ u i) s) x := by
    intro j M hMj
    have hG' : ∀ L : List (Fin (n + 1)), L.length + 1 ≤ k →
        ContDiffAt ℝ (L.length + 1) G (curveFun γ x) := by
      intro L hL
      refine hG.of_le ?_
      exact_mod_cast (by omega : L.length + 1 ≤ k)
    have hγ' : ∀ i : Fin n, ContDiffAt ℝ 1 (fun s => γ s i) x :=
      fun i => (hγc i).of_le (by exact_mod_cast (by omega : 1 ≤ k))
    exact Work.WilG4c.curve_chain_ineq_w (n := n) (r := k) G γ x hG' hγ' hsm hsmoothg
      j M (k - (j + 1) - M.length) (by omega)
  have hbase' : ∀ M : List (Fin n), M.length ≤ k →
      tnorm (k - M.length)
        (fun s => iterDir (List.replicate 0 (0 : Fin (n + 1)) ++ M.map Fin.succ) G
          (curveFun γ s)) x ≤ Real.exp 1 := by
    intro M hM
    have h := hbase M hM
    refine (tnorm_mono (Nat.sub_le k M.length)
      (fun s => iterDir (M.map Fin.succ) G (curveFun γ s)) x).trans ?_
    simpa using h
  have hgd' : ∀ i : Fin n, ∀ m ≤ k,
      ‖iteratedFDeriv ℝ m (fun s => deriv (fun u => γ u i) s) x‖ ≤ 1 := hgd
  have hmain := Work.WilG4c.tnorm_curve_system_w (n := n) (r := k)
    (fun j M s => iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
      (curveFun γ s))
    (fun i s => deriv (fun u => γ u i) s) x hsm (fun i => (hsmoothg i)) hbase' hchain hgd'
  have h1 := hmain j M hMj
  -- `|u j M x| ≤ tnorm (k-j-|M|) (u j M) x ≤ e (k(1+ne))^j ≤ e (r(1+ne))^j`
  have h2 : |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G (curveFun γ x)|
      ≤ tnorm (k - j - M.length)
        (fun s => iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
          (curveFun γ s)) x := abs_le_tnorm (k - j - M.length)
        (fun s => iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
          (curveFun γ s)) x
  have h3 : Real.exp 1 * (k * (1 + n * Real.exp 1)) ^ j
      ≤ Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j := by
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
    refine pow_le_pow_left₀ (by positivity) ?_ j
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
  exact h2.trans (h1.trans h3)

end Work.WilkG4c
