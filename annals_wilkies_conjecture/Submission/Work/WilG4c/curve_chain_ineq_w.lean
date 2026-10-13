import Mathlib
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.hasDerivAt_iterDir_curve
import Submission.Work.WilG4c.iterDir_perm
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.tnorm_congr
import Submission.Work.WilG4c.tnorm_finset_sum_le

namespace Work.WilG4c

open Work.WilkG4c
open scoped BigOperators Topology

/-- `a :: (P ++ Q)` and `P ++ a :: Q` are permutations of one another: the head can be moved
past the block `P`.  (Used together with `Work.WilkG4c.iterDir_perm` to move the direction
`i.succ` of a `y`-derivative past the block of `x`-directions `List.replicate j 0`.) -/
private theorem ccw_perm_cons_insert {α : Type} (a : α) (P Q : List α) :
    (a :: (P ++ Q)).Perm (P ++ a :: Q) := by
  induction P with
  | nil => exact List.Perm.refl _
  | cons b P ih =>
      simpa only [List.cons_append] using
        ((List.Perm.swap a b (P ++ Q)).symm).trans (List.Perm.cons b ih)

/-- Subadditivity of the jet norm for a difference, `‖f - g‖_{T,r} ≤ ‖f‖_{T,r} + ‖g‖_{T,r}`:
`f - g = f + (-g)` and the jet norm is invariant under negation
(`WilkiesDesign.CG.tnorm_neg`), so this is `WilkiesDesign.CG.tnorm_add_le`. -/
private theorem ccw_tnorm_sub_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ)
    (f g : E → ℝ) (x : E) (hf : ContDiffAt ℝ r f x) (hg : ContDiffAt ℝ r g x) :
    WilkiesDesign.CG.tnorm r (f - g) x ≤
      WilkiesDesign.CG.tnorm r f x + WilkiesDesign.CG.tnorm r g x := by
  have h : f - g = f + -g := by funext y; simp [sub_eq_add_neg]
  rw [h]
  calc WilkiesDesign.CG.tnorm r (f + -g) x
      ≤ WilkiesDesign.CG.tnorm r f x + WilkiesDesign.CG.tnorm r (-g) x :=
        WilkiesDesign.CG.tnorm_add_le r f (-g) x hf hg.neg
    _ = WilkiesDesign.CG.tnorm r f x + WilkiesDesign.CG.tnorm r g x := by
        rw [WilkiesDesign.CG.tnorm_neg]

/-- `↑m + 1` is not the "`C^∞`" level `↑⊤` of `WithTop ℕ∞`: it is a finite level. -/
private theorem withTopNat_add_one_ne_midTop (m : ℕ) :
    (((m : ℕ) : WithTop ℕ∞) + 1) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast (ENat.natCast_ne_top (m + 1))

theorem curve_chain_ineq_w {n r : ℕ} (G : (Fin (n + 1) → ℝ) → ℝ) (γ : ℝ → Fin n → ℝ) (t : ℝ)
    (hG : ∀ L : List (Fin (n + 1)), L.length + 1 ≤ r →
      ContDiffAt ℝ (L.length + 1) G (Work.WilkG4c.curveFun γ t))
    (hγ : ∀ i : Fin n, ContDiffAt ℝ 1 (fun s => γ s i) t)
    (hsmooth : ∀ (j : ℕ) (M : List (Fin n)), M.length + j ≤ r →
      ContDiffAt ℝ (r - j - M.length)
        (fun s => Work.WilkG4c.iterDir
          (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
          (Work.WilkG4c.curveFun γ s)) t)
    (hsmoothg : ∀ i : Fin n, ContDiffAt ℝ r (fun s => deriv (fun u => γ u i) s) t) :
    ∀ (j : ℕ) (M : List (Fin n)) (s : ℕ), M.length + (j + 1) + s ≤ r →
      WilkiesDesign.CG.tnorm s (fun v => Work.WilkG4c.iterDir
          (List.replicate (j + 1) (0 : Fin (n + 1)) ++ M.map Fin.succ) G
          (Work.WilkG4c.curveFun γ v)) t ≤
        WilkiesDesign.CG.tnorm s (fun v => deriv (fun w => Work.WilkG4c.iterDir
            (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
            (Work.WilkG4c.curveFun γ w)) v) t +
        ∑ i : Fin n, WilkiesDesign.CG.tnorm s (fun v => Work.WilkG4c.iterDir
            (List.replicate j (0 : Fin (n + 1)) ++ (i :: M).map Fin.succ) G
            (Work.WilkG4c.curveFun γ v) * deriv (fun u => γ u i) v) t := by
  intro j M s hMJ
  -- length bookkeeping
  have hMj : M.length + j ≤ r := by omega
  have hlenL : (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ).length + 1 ≤ r := by
    rw [List.length_append, List.length_replicate, List.length_map]; omega
  -- ### The hypotheses are local at `t`; propagate them to a neighbourhood of `t` along
  -- the curve, so that the chain rule can be applied there.
  have htend : Filter.Tendsto (fun v => curveFun γ v) (𝓝 t) (𝓝 (curveFun γ t)) :=
    (hasDerivAt_curveFun γ t (fun i => (hγ i).differentiableAt_one)).continuousAt
  have hGLt : ContDiffAt ℝ
      ((((List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ).length : ℕ) : WithTop ℕ∞) + 1)
      G (curveFun γ t) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hG (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) hlenL
  have hGL : ∀ᶠ v in 𝓝 t, ContDiffAt ℝ
      ((((List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ).length : ℕ) : WithTop ℕ∞) + 1)
      G (curveFun γ v) :=
    htend.eventually (hGLt.eventually (withTopNat_add_one_ne_midTop _))
  have hγev : ∀ᶠ v in 𝓝 t, ∀ i : Fin n, DifferentiableAt ℝ (fun s => γ s i) v :=
    Filter.eventually_all.mpr fun i =>
      ((hγ i).eventually (by simp)).mono fun v hv => hv.differentiableAt_one
  -- ### The pointwise chain-rule identity, valid on that neighbourhood: the germ equality.
  have hkey : (fun v => iterDir (List.replicate (j + 1) (0 : Fin (n + 1)) ++ M.map Fin.succ)
        G (curveFun γ v))
      =ᶠ[𝓝 t] (fun v =>
        deriv (fun w => iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
            (curveFun γ w)) v
          - ∑ i : Fin n,
              iterDir (List.replicate j (0 : Fin (n + 1)) ++ (i :: M).map Fin.succ) G
                (curveFun γ v) * deriv (fun u => γ u i) v) := by
    filter_upwards [hGL, hγev] with v hCv hDv
    have hd := (hasDerivAt_iterDir_curve G γ
      (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) v hCv hDv).deriv
    rw [hd]
    have h1 : iterDir ((0 : Fin (n + 1)) ::
          (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ)) G (curveFun γ v)
        = iterDir (List.replicate (j + 1) (0 : Fin (n + 1)) ++ M.map Fin.succ) G
            (curveFun γ v) := by
      simp only [List.replicate_succ, List.cons_append]
    have h2 : (∑ i : Fin n,
          iterDir (i.succ :: (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ)) G
              (curveFun γ v) * deriv (fun u => γ u i) v)
        = ∑ i : Fin n,
            iterDir (List.replicate j (0 : Fin (n + 1)) ++ (i :: M).map Fin.succ) G
              (curveFun γ v) * deriv (fun u => γ u i) v := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hp := iterDir_perm G
        (ccw_perm_cons_insert i.succ (List.replicate j (0 : Fin (n + 1))) (M.map Fin.succ))
        (curveFun γ v)
        (by
          simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using hCv)
      rw [hp, List.map_cons]
    rw [h1, h2]
    ring
  -- ### Smoothness of the two pieces of the right-hand side, at order `s`.
  have hsumterm : ∀ i : Fin n, ContDiffAt ℝ ((s : ℕ) : WithTop ℕ∞)
      (fun v => iterDir (List.replicate j (0 : Fin (n + 1)) ++ (i :: M).map Fin.succ) G
          (curveFun γ v) * deriv (fun u => γ u i) v) t := by
    intro i
    have hli : (i :: M).length + j ≤ r := by simp only [List.length_cons]; omega
    have hle1 : ((s : ℕ) : WithTop ℕ∞) ≤
        ((r - j - (i :: M).length : ℕ) : WithTop ℕ∞) := by
      have h : s ≤ r - j - (i :: M).length := by simp only [List.length_cons]; omega
      exact_mod_cast h
    have hle2 : ((s : ℕ) : WithTop ℕ∞) ≤ ((r : ℕ) : WithTop ℕ∞) := by
      have h : s ≤ r := by omega
      exact_mod_cast h
    exact ((hsmooth j (i :: M) hli).of_le hle1).mul ((hsmoothg i).of_le hle2)
  have hsumAll : ContDiffAt ℝ ((s : ℕ) : WithTop ℕ∞)
      (fun v => ∑ i : Fin n,
        iterDir (List.replicate j (0 : Fin (n + 1)) ++ (i :: M).map Fin.succ) G
          (curveFun γ v) * deriv (fun u => γ u i) v) t := by
    simpa using ContDiffAt.sum (s := Finset.univ)
      (f := fun i v => iterDir (List.replicate j (0 : Fin (n + 1)) ++ (i :: M).map Fin.succ) G
          (curveFun γ v) * deriv (fun u => γ u i) v) (fun i _ => hsumterm i)
  have hleD : (((s + 1 : ℕ)) : WithTop ℕ∞) ≤ (((r - j - M.length : ℕ)) : WithTop ℕ∞) :=
    Nat.cast_le.mpr (by omega : s + 1 ≤ r - j - M.length)
  have hD : ContDiffAt ℝ (((s + 1 : ℕ)) : WithTop ℕ∞)
      (fun v => iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
        (curveFun γ v)) t :=
    (hsmooth j M hMj).of_le hleD
  have hcast : ((s : ℕ) : WithTop ℕ∞) + 1 = (((s + 1 : ℕ)) : WithTop ℕ∞) := by
    rw [Nat.cast_add, Nat.cast_one]
  have hDeriv : ContDiffAt ℝ ((s : ℕ) : WithTop ℕ∞)
      (fun v => deriv (fun w => iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
          (curveFun γ w)) v) t :=
    hD.derivWithin (le_of_eq hcast)
  -- ### Assemble.
  calc WilkiesDesign.CG.tnorm s
        (fun v => iterDir (List.replicate (j + 1) (0 : Fin (n + 1)) ++ M.map Fin.succ) G
          (curveFun γ v)) t
      = WilkiesDesign.CG.tnorm s
          (fun v => deriv (fun w =>
              iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
                (curveFun γ w)) v
            - ∑ i : Fin n,
                iterDir (List.replicate j (0 : Fin (n + 1)) ++ (i :: M).map Fin.succ) G
                  (curveFun γ v) * deriv (fun u => γ u i) v) t :=
        tnorm_congr s hkey
    _ ≤ WilkiesDesign.CG.tnorm s
          (fun v => deriv (fun w =>
            iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
              (curveFun γ w)) v) t
        + WilkiesDesign.CG.tnorm s
          (fun v => ∑ i : Fin n,
            iterDir (List.replicate j (0 : Fin (n + 1)) ++ (i :: M).map Fin.succ) G
              (curveFun γ v) * deriv (fun u => γ u i) v) t :=
        ccw_tnorm_sub_le s _ _ t hDeriv hsumAll
    _ ≤ WilkiesDesign.CG.tnorm s
          (fun v => deriv (fun w =>
            iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
              (curveFun γ w)) v) t
        + ∑ i : Fin n, WilkiesDesign.CG.tnorm s
          (fun v => iterDir (List.replicate j (0 : Fin (n + 1)) ++ (i :: M).map Fin.succ) G
            (curveFun γ v) * deriv (fun u => γ u i) v) t :=
        add_le_add le_rfl (tnorm_finset_sum_le s
          (fun i v => iterDir (List.replicate j (0 : Fin (n + 1)) ++ (i :: M).map Fin.succ) G
            (curveFun γ v) * deriv (fun u => γ u i) v) t hsumterm)

end Work.WilG4c
