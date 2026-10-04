import Mathlib
import Submission.Work.Diff.EXT.evolKDefs
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.frame_evol_of_fixed
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.T.lc_variation
import Submission.Work.Diff.EXT.covKRmExt_eval_bound
import Submission.Work.Diff.EXT.covK_valueDep
import Submission.Work.Diff.EXT.covK_frameInv
import Submission.Work.Diff.EXT.evolCompKFix_all
import Submission.Work.Diff.EXT.evolX.substC.ReactAll

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `evolCompK_all` (clash-free copy `C`)

A copy of `Submission/Work/Diff/EXT/evolCompK_all.lean` in which the import of
`evolCompKFixReact_all` is replaced by the climb-free chain `substC.ReactAll` (so that this module
does **not** pull in `Submission.Work.Diff.EXT.evolX.lapOpEDefs`, whose `SOp` clashes with
`substB/Defs.lean`'s `SOp`).  Used by `Work.Diff.EXT.evolK_of_flow`.
-/

namespace Work.Diff.EXT

/-!
# The analytic core of the `k`-th order Shi estimate: componentwise evolution of `∇^k Rm`

`EvolCompK k` (`Submission/Work/Diff/EXT/evolKDefs.lean`) is the *componentwise* evolution estimate
for the `k`-th covariant derivative of the curvature along a Ricci flow, in a moving orthonormal
frame.  Its bound is

`C (1+K') (1 + Σ_{j<k} f_j) (1 + √f_k)`,  `f_j = curvNormK (G t) x j`,

which is the shape forced by the reaction `∂ₜ∇^k Rm − Δ∇^k Rm = Σ_{i+j=k} ∇^iRm ∗ ∇^jRm` (pairs with
`i,j ≤ k−1` need `Σ_{j<k}f_j`; the boundary pairs need `1+√f_k`).  For `k = 1` the GE-area result
`Work.Diff.GE.covRm_frame_evol_abs` implies this bound.

This is the only ingredient of the verified assembly `evolK_of_pieces`
(`Submission/Work/Diff/EXT/evolK_of_flow.lean`) that has no owner yet: `EvolK` for every `k ≥ 1`
follows from it together with the Kato identity `laplAt_curvNormK_eq`, the frame family
`Work.Diff.GE.exists_ON_frame_family_onFrame` and frame independence `curvNormK_frame_indep`.
The assembly converts the bound above into `EvolK`'s `c(1+ΣA_j)(f_k+1)` by `Σ_{j<k}f_j ≤ ΣA_j`,
`(1+√f_k)√f_k ≤ 3(1+f_k)` and Cauchy–Schwarz on the components (already verified).

ROUTE.  Fix `k ≥ 1`.  In *fixed* vectors `∂ₜ(∇^k Rm) = Δ(∇^k Rm) + R_k` with
`|R_k| ≤ C_k Σ_{i+j=k}|∇^iRm||∇^jRm|` (Hamilton 1982 §13, Chow–Knopf Ch. 6, Topping §2.5), whence
`|R_k| ≤ C_k(1+Σ_{j<k}f_j)(1+√f_k)` by `2√(f_if_j) ≤ f_i+f_j`; the `−2|∇^{k+1}Rm|²` of the exact
identity is dropped.  Suggested decomposition (file each as an exact sub-lemma):

1. *Fixed vectors first*: for `covKRm (G s) x k u a b c d` with the five vectors fixed at `x` the
   `s`-dependence is only through the metric, no frame bookkeeping is needed, and Clairaut
   (`Work.Diff.GE.hasDerivAt_mvfderiv`) applies directly.
2. *Base case `k = 1`*: `Work.Diff.GE.covRm_frame_evol_abs` / `hasDerivWithinAt_covRm_le` (GE area,
   in progress); two-sidedness from the one-sided form via the antisymmetry
   `Work.Diff.EXT.covKRmExt_antisymm_pair1` (in progress).
3. *Induction step*: expand `covKRmExt g (k+1) v A B C D x` by its defining recursion
   (`local_ext_of_bounded_curv.lean`), differentiate in `s`, use Clairaut for the `mvfderiv` term,
   the level-`k` identity for `∂ₛ` of the level-`k` expression, and `LCVariation` for
   `∂ₛ(lcOf (G s))`.  Terms: (a) `∇_{v₀}(Δ_k) − Δ_{k+1}`, the Ricci-identity commutator
   (`Work.Diff.GE.ExtTensor.extDD_antisymm`); (b) connection-variation terms (`connVar_bound`,
   `covRic_le_dRmNormSq`); (c) the quadratic terms from `∇^{k+1}(Rm ∗ Rm)`.
   NB: the induction must carry the *explicit* reaction `R_k` (differentiating the level-`k`
   evolution in space needs its structure), so run it on "identity with explicit reaction + bounds"
   or define the reaction recursively.  `Work.Diff.EXT.covKRmExt_locality` (in progress) identifies
   the `Classical.epsilon`-extensions with the chosen fields.
4. *Moving frames*: expand `e s j = Σ_r c (s) j r • onFrame (G t) x r`, differentiate the
   coefficients (bounded by the velocity hypothesis `K'`), and use multilinearity;
   `Work.Diff.EXT.curvNormK_frame_indep` (in progress) identifies the `f_j`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option maxHeartbeats 4000000

/-! ## Auxiliary facts for the moving-frame reduction -/

/-- **Cauchy–Schwarz against a vector of an orthonormal family.**  For a `g`-orthonormal family
`e`, the pairing of `e i` with any vector `v` is bounded by the `g`-length `√(g(v,v))`. -/
theorem inner_le_sqrt_of_isONFrameC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M) {m : ℕ} (e : Fin m → TangentSpace I x)
    (he : ∀ i j, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (i : Fin m) (v : TangentSpace I x) :
    |g.inner x (e i) v| ≤ Real.sqrt (g.inner x v v) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have key : ∀ v z : TangentSpace I x, inner ℝ v z = g.inner x v z := fun v z => rfl
  have h1 : ‖e i‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, key (e i) (e i), he i i, if_pos rfl, Real.sqrt_one]
  have h2 : ‖v‖ = Real.sqrt (g.inner x v v) := by rw [norm_eq_sqrt_real_inner, key v v]
  calc |g.inner x (e i) v| = |inner ℝ (e i) v| := by rw [key]
    _ ≤ ‖e i‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ = Real.sqrt (g.inner x v v) := by rw [h1, one_mul, h2]

/-- The metric pairing with a fixed vector is differentiable along a differentiable curve. -/
theorem hasDerivWithinAt_inner_constC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M) (u : TangentSpace I x)
    {γ : ℝ → TangentSpace I x} {γ' : TangentSpace I x} {σ : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt γ γ' σ t) :
    HasDerivWithinAt (fun s => g.inner x u (γ s)) (g.inner x u γ') σ t := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact (ContinuousLinearMap.hasFDerivAt (g.inner x u)).comp_hasDerivWithinAt t h

open scoped BigOperators

/-- **The moving-frame reduction at level `k`.**

Given

* `heval`: the evaluation bound `|∇^k Rm(v₁,…,v_k;a,b,c,d)| ≤ Ce (1+√(f_k)) ∏‖vᵢ‖‖a‖‖b‖‖c‖‖d‖`;
* `hfix`: the *fixed-vector* evolution estimate
  `|∂ₛ(component) − (Δ∇^kRm)(component)| ≤ C₀ (1+Σ_{j<k}f_j)(1+√f_k) ∏‖·‖`;
* `hexp`: the multilinear expansion of a component of `∇^k Rm` on an arbitrary frame,

the componentwise evolution estimate `EvolCompK k` in a *moving* orthonormal frame holds, with
constant `C₀ + Ce·(dim^{k+4}·(k+4))`.

The proof is the general-`k` form of `Work.Diff.GE.frame_evol_of_fixed`: expand the moving frame at
time `s` in the *fixed* frame `e t` (which is `G t`-orthonormal), so that the component becomes a
finite sum of products of scalar coefficients `⟨e t r, e s (ι q)⟩` with *fixed-vector* components;
the product rule then gives the fixed-vector derivative at the tuple `e t ∘ ι` (whose coefficient
product at `t` is the Kronecker delta) plus `(k+4)` frame-motion terms, each bounded by
`√(K' |Rm|²) √f_k`. -/
theorem evolCompK_of_fixedC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (k : ℕ) (hk : 1 ≤ k)
    (Ce : ℝ) (hCe : 0 ≤ Ce)
    (heval : ∀ (g : Submission.Diff.SMet I M) (x : M)
      (v : Fin k → TangentSpace I x) (a b c d : TangentSpace I x),
      |covKRm g x k v a b c d|
        ≤ Ce * (1 + Real.sqrt (curvNormK g x k))
            * (Finset.univ.prod (fun i : Fin k => Real.sqrt (g.inner x (v i) (v i)))
               * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
               * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)))
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hfix : ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      ∀ (v : Fin k → TangentSpace I x) (a b c d : TangentSpace I x), ∃ D : ℝ,
        HasDerivWithinAt (fun s ↦ covKRm (G s) x k v a b c d) D (Set.Ico 0 T) t ∧
        |D - lapCovKRm (G t) x k v a b c d|
          ≤ C₀ * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
              * (1 + Real.sqrt (curvNormK (G t) x k))
              * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i)))
                 * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
                 * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d)))
    (hexp : ∀ (g : Submission.Diff.SMet I M) (x : M) {n : ℕ} (a : Fin n → TangentSpace I x)
      (p : Fin (k + 4) → TangentSpace I x) (cp : Fin (k + 4) → Fin n → ℝ),
      (∀ j : Fin (k + 4), ∑ r, cp j r • a r = p j) →
      covKRm g x k (fun i : Fin k => p (Fin.castAdd 4 i)) (p (Fin.natAdd k 0))
          (p (Fin.natAdd k 1)) (p (Fin.natAdd k 2)) (p (Fin.natAdd k 3))
        = ∑ r : Fin (k + 4) → Fin n, (∏ j : Fin (k + 4), cp j (r j)) *
            covKRm g x k (fun i : Fin k => a (r (Fin.castAdd 4 i))) (a (r (Fin.natAdd k 0)))
              (a (r (Fin.natAdd k 1))) (a (r (Fin.natAdd k 2))) (a (r (Fin.natAdd k 3))))
    : EvolCompK (I := I) (M := M) k := by
  classical
  refine ⟨C₀ + Ce * ((Module.finrank ℝ E : ℝ) ^ (k + 4) * ((k : ℝ) + 4)), by positivity, ?_⟩
  intro G T hflow t ht x e edot K' hK' het hvel hON hder u i j l m
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hn0 | hn
  · have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk
    exact Fin.elim0 (hn0 ▸ u ⟨0, hk0⟩)
  · have hONt : Submission.Diff.IsONFrame (G t) x (e t) := hON.self_of_nhdsWithin ht
    set ι : Fin (k + 4) → Fin (Module.finrank ℝ E) := Fin.append u ![i, j, l, m] with hι
    set w : ℝ → Fin (k + 4) → TangentSpace I x := fun s r => e s (ι r) with hw
    set cp : ℝ → Fin (k + 4) → Fin (Module.finrank ℝ E) → ℝ
      := fun s q r => (G t).inner x (e t r) (w s q) with hcp
    set F : ℝ → ℝ := fun s => covKRm (G s) x k (fun i : Fin k => w s (Fin.castAdd 4 i))
      (w s (Fin.natAdd k 0)) (w s (Fin.natAdd k 1)) (w s (Fin.natAdd k 2))
      (w s (Fin.natAdd k 3)) with hF
    set κ : (Fin (k + 4) → Fin (Module.finrank ℝ E)) → ℝ → ℝ := fun r s =>
      covKRm (G s) x k (fun i : Fin k => e t (r (Fin.castAdd 4 i))) (e t (r (Fin.natAdd k 0)))
        (e t (r (Fin.natAdd k 1))) (e t (r (Fin.natAdd k 2))) (e t (r (Fin.natAdd k 3))) with hκ
    set P : ℝ → (Fin (k + 4) → Fin (Module.finrank ℝ E)) → ℝ :=
      fun s r => ∏ q : Fin (k + 4), cp s q (r q) with hP
    set A : (Fin (k + 4) → Fin (Module.finrank ℝ E)) → ℝ := fun r =>
      ∑ q : Fin (k + 4), (∏ q' ∈ Finset.univ.erase q, cp t q' (r q')) *
        (G t).inner x (e t (r q)) (edot (ι q)) with hA
    have hF_eq : ∀ s : ℝ, F s = covKRm (G s) x k (fun r : Fin k => e s (u r))
        (e s i) (e s j) (e s l) (e s m) := by
      intro s
      simp only [hF, hw, hι, Fin.append_left, Fin.append_right, Matrix.cons_val_zero,
        Matrix.cons_val, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
    have hexps : ∀ s : ℝ,
        F s = ∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E), P s r * κ r s := by
      intro s
      simp only [hF, hP, hκ]
      exact hexp (G s) x (fun r => e t r) (w s) (cp s) (fun q => by
        rw [hcp]
        exact Work.Diff.GE.sum_inner_smul_eq_self (G t) x hn (e t) hONt (w s q))
    have hcd : ∀ (q : Fin (k + 4)) (r : Fin (Module.finrank ℝ E)),
        HasDerivWithinAt (fun s : ℝ => cp s q r) ((G t).inner x (e t r) (edot (ι q)))
          (Set.Ico 0 T) t := by
      intro q r
      have h1 := hasDerivWithinAt_inner_constC (G t) x (e t r) (hder (ι q))
      simpa only [hcp, hw] using h1
    have hcp_eval : ∀ (q : Fin (k + 4)) (r : Fin (Module.finrank ℝ E)),
        cp t q r = (G t).inner x (e t r) (e t (ι q)) := by
      intro q r
      simp only [hcp, hw]
    have hfac_eval : ∀ (q : Fin (k + 4)) (r : Fin (Module.finrank ℝ E)),
        cp t q r = if r = ι q then (1 : ℝ) else 0 := by
      intro q r
      rw [hcp_eval q r, hONt r (ι q)]
    choose D hD hDb using fun r : Fin (k + 4) → Fin (Module.finrank ℝ E) =>
      hfix G T hflow t ht x (fun i : Fin k => e t (r (Fin.castAdd 4 i)))
        (e t (r (Fin.natAdd k 0))) (e t (r (Fin.natAdd k 1))) (e t (r (Fin.natAdd k 2)))
        (e t (r (Fin.natAdd k 3)))
    have hterm : ∀ r : Fin (k + 4) → Fin (Module.finrank ℝ E),
        HasDerivWithinAt (fun s : ℝ => P s r * κ r s) (A r * κ r t + P t r * D r)
          (Set.Ico 0 T) t := by
      intro r
      have hPder : HasDerivWithinAt (fun s : ℝ => P s r) (A r) (Set.Ico 0 T) t := by
        simp only [hP, hA]
        refine HasDerivWithinAt.fun_finsetProd (u := Finset.univ)
          (f := fun q s => cp s q (r q))
          (f' := fun q => (G t).inner x (e t (r q)) (edot (ι q))) ?_
        intro q _
        exact hcd q (r q)
      have hκder : HasDerivWithinAt (fun s : ℝ => κ r s) (D r) (Set.Ico 0 T) t := by
        simpa only [hκ] using hD r
      exact hPder.mul hκder
    have hmain : HasDerivWithinAt F (∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E),
        (A r * κ r t + P t r * D r)) (Set.Ico 0 T) t := by
      have h := HasDerivWithinAt.sum (u := Finset.univ) (fun r _ => hterm r)
      refine h.congr_of_eventuallyEq ?_ ?_
      · filter_upwards with s
        simpa only [Finset.sum_apply] using hexps s
      · simpa only [Finset.sum_apply] using hexps t
    have hcollapse : (∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E), P t r * D r) = D ι := by
      have hprod : ∀ r : Fin (k + 4) → Fin (Module.finrank ℝ E),
          P t r = if r = ι then (1 : ℝ) else 0 := by
        intro r
        by_cases hr : r = ι
        · subst hr
          have hfac' : ∀ q : Fin (k + 4), cp t q (ι q) = (1 : ℝ) := by
            intro q; rw [hfac_eval q (ι q), if_pos rfl]
          simp only [hP]
          refine (Finset.prod_eq_one (s := Finset.univ) (fun q _ => hfac' q)).trans ?_
          simp
        · obtain ⟨q, hq⟩ := Function.ne_iff.mp hr
          have hz : cp t q (r q) = 0 := by rw [hfac_eval q (r q), if_neg hq]
          have hzero : P t r = 0 := by
            simp only [hP]
            exact Finset.prod_eq_zero (Finset.mem_univ q) hz
          rw [hzero, if_neg hr]
      calc (∑ r, P t r * D r) = ∑ r, (if r = ι then (1 : ℝ) else 0) * D r :=
            Finset.sum_congr rfl (fun r _ => by rw [hprod r])
        _ = D ι := by simp
    have hone : ∀ p : Fin (Module.finrank ℝ E),
        Real.sqrt ((G t).inner x (e t p) (e t p)) = 1 := by
      intro p
      rw [hONt p p, if_pos rfl, Real.sqrt_one]
    have hprod1 : ∀ (l : ℕ) (f : Fin l → Fin (Module.finrank ℝ E)),
        (∏ s : Fin l, Real.sqrt ((G t).inner x (e t (f s)) (e t (f s)))) = 1 :=
      fun l f => Finset.prod_eq_one (fun s _ => hone (f s))
    have hrm0 : 0 ≤ curvNormK (G t) x 0 := curvNormK_nonneg (G t) x 0
    have hfk0 : 0 ≤ curvNormK (G t) x k := curvNormK_nonneg (G t) x k
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, curvNormK (G t) x j :=
      Finset.sum_nonneg (fun j _ => curvNormK_nonneg (G t) x j)
    have hf0le : curvNormK (G t) x 0 ≤ ∑ j ∈ Finset.range k, curvNormK (G t) x j :=
      Finset.single_le_sum (fun j _ => curvNormK_nonneg (G t) x j)
        (Finset.mem_range.mpr (lt_of_lt_of_le (by norm_num) hk))
    have hκbound : ∀ r : Fin (k + 4) → Fin (Module.finrank ℝ E),
        |κ r t| ≤ Ce * (1 + Real.sqrt (curvNormK (G t) x k)) := by
      intro r
      have h := heval (G t) x (fun i : Fin k => e t (r (Fin.castAdd 4 i)))
        (e t (r (Fin.natAdd k 0))) (e t (r (Fin.natAdd k 1))) (e t (r (Fin.natAdd k 2)))
        (e t (r (Fin.natAdd k 3)))
      simp only [hone, Finset.prod_const, one_pow, mul_one, one_mul] at h
      simpa only [hκ] using h
    have hvelb : ∀ (r : Fin (k + 4) → Fin (Module.finrank ℝ E)) (q : Fin (k + 4)),
        |(G t).inner x (e t (r q)) (edot (ι q))| ≤ Real.sqrt (K' * curvNormK (G t) x 0) := by
      intro r q
      refine le_trans (inner_le_sqrt_of_isONFrameC (G t) x (e t) hONt (r q) (edot (ι q))) ?_
      rw [curvNormK_zero_eq_rmNormSq]
      exact Real.sqrt_le_sqrt (hvel (ι q))
    have hAbound : ∀ r : Fin (k + 4) → Fin (Module.finrank ℝ E),
        |A r| ≤ ((k : ℝ) + 4) * Real.sqrt (K' * curvNormK (G t) x 0) := by
      intro r
      simp only [hA]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hle : ∀ q : Fin (k + 4),
          |(∏ q' ∈ Finset.univ.erase q, cp t q' (r q')) *
            (G t).inner x (e t (r q)) (edot (ι q))|
          ≤ Real.sqrt (K' * curvNormK (G t) x 0) := by
        intro q
        rw [abs_mul]
        have h1 : |∏ q' ∈ Finset.univ.erase q, cp t q' (r q')| ≤ 1 := by
          rw [Finset.abs_prod]
          refine Finset.prod_le_one₀ (fun q' _ => abs_nonneg _) (fun q' _ => ?_)
          rw [hfac_eval q' (r q')]
          split_ifs <;> norm_num
        calc |∏ q' ∈ Finset.univ.erase q, cp t q' (r q')|
              * |(G t).inner x (e t (r q)) (edot (ι q))|
            ≤ 1 * Real.sqrt (K' * curvNormK (G t) x 0) :=
              mul_le_mul h1 (hvelb r q) (abs_nonneg _) zero_le_one
          _ = Real.sqrt (K' * curvNormK (G t) x 0) := one_mul _
      calc ∑ q : Fin (k + 4), |(∏ q' ∈ Finset.univ.erase q, cp t q' (r q')) *
            (G t).inner x (e t (r q)) (edot (ι q))|
          ≤ ∑ _q : Fin (k + 4), Real.sqrt (K' * curvNormK (G t) x 0) :=
            Finset.sum_le_sum (fun q _ => hle q)
        _ = ((k : ℝ) + 4) * Real.sqrt (K' * curvNormK (G t) x 0) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            norm_num
    have hXfbound : |∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E), A r * κ r t|
        ≤ (Module.finrank ℝ E : ℝ) ^ (k + 4) * (((k : ℝ) + 4)
            * Real.sqrt (K' * curvNormK (G t) x 0))
            * (Ce * (1 + Real.sqrt (curvNormK (G t) x k))) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hle : ∀ r : Fin (k + 4) → Fin (Module.finrank ℝ E),
          |A r * κ r t| ≤ (((k : ℝ) + 4) * Real.sqrt (K' * curvNormK (G t) x 0))
              * (Ce * (1 + Real.sqrt (curvNormK (G t) x k))) := by
        intro r
        rw [abs_mul]
        exact mul_le_mul (hAbound r) (hκbound r) (abs_nonneg _) (by positivity)
      calc ∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E), |A r * κ r t|
          ≤ ∑ _r : Fin (k + 4) → Fin (Module.finrank ℝ E),
              ((((k : ℝ) + 4) * Real.sqrt (K' * curvNormK (G t) x 0))
                * (Ce * (1 + Real.sqrt (curvNormK (G t) x k)))) :=
            Finset.sum_le_sum (fun r _ => hle r)
        _ = (Fintype.card (Fin (k + 4) → Fin (Module.finrank ℝ E)) : ℝ) *
              ((((k : ℝ) + 4) * Real.sqrt (K' * curvNormK (G t) x 0))
                * (Ce * (1 + Real.sqrt (curvNormK (G t) x k)))) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = (Module.finrank ℝ E : ℝ) ^ (k + 4) * (((k : ℝ) + 4)
              * Real.sqrt (K' * curvNormK (G t) x 0))
              * (Ce * (1 + Real.sqrt (curvNormK (G t) x k))) := by
            rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
            ring
    -- the fixed-vector bound at the identity tuple
    let lapE : ℝ := lapCovKRm (G t) x k (fun r : Fin k => e t (u r)) (e t i) (e t j)
      (e t l) (e t m)
    have hDbound : |D ι - lapE| ≤ C₀ * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
        * (1 + Real.sqrt (curvNormK (G t) x k)) := by
      have h := hDb ι
      simp only [hι, Fin.append_left, Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val,
        Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, hone, Finset.prod_const, one_pow,
        mul_one, one_mul] at h
      exact h
    -- the goal
    refine ⟨(∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E), A r * κ r t) + D ι, ?_, ?_⟩
    · have h := hmain
      rw [Finset.sum_add_distrib, hcollapse] at h
      refine h.congr_of_eventuallyEq ?_ ?_
      · filter_upwards with s
        exact (hF_eq s).symm
      · exact (hF_eq t).symm
    · have hLap : lapCovKRm (G t) x k (fun r : Fin k => Submission.Diff.onFrame (G t) x (u r))
            (Submission.Diff.onFrame (G t) x i) (Submission.Diff.onFrame (G t) x j)
            (Submission.Diff.onFrame (G t) x l) (Submission.Diff.onFrame (G t) x m) = lapE := by
        have h1 : (fun r : Fin k => Submission.Diff.onFrame (G t) x (u r))
            = (fun r : Fin k => e t (u r)) := by
          funext r
          rw [← het (u r)]
        rw [h1, ← het i, ← het j, ← het l, ← het m]
      rw [hLap]
      have hsplit : |(∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E), A r * κ r t) + D ι - lapE|
          ≤ |D ι - lapE| + |∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E), A r * κ r t| := by
        have h := abs_add_le (D ι - lapE)
          (∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E), A r * κ r t)
        rw [show (D ι - lapE) + (∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E), A r * κ r t)
            = (∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E), A r * κ r t) + D ι - lapE by ring] at h
        exact h
      have hXf' : |∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E), A r * κ r t|
          ≤ Ce * ((Module.finrank ℝ E : ℝ) ^ (k + 4) * ((k : ℝ) + 4))
            * Real.sqrt (K' * curvNormK (G t) x 0)
            * (1 + Real.sqrt (curvNormK (G t) x k)) := by
        have heq : (Module.finrank ℝ E : ℝ) ^ (k + 4) * (((k : ℝ) + 4)
              * Real.sqrt (K' * curvNormK (G t) x 0))
              * (Ce * (1 + Real.sqrt (curvNormK (G t) x k)))
            = Ce * ((Module.finrank ℝ E : ℝ) ^ (k + 4) * ((k : ℝ) + 4))
              * Real.sqrt (K' * curvNormK (G t) x 0)
              * (1 + Real.sqrt (curvNormK (G t) x k)) := by ring
        rwa [heq] at hXfbound
      have hsqrt : Real.sqrt (K' * curvNormK (G t) x 0)
          ≤ (1 + K') * (1 + curvNormK (G t) x 0) := by
        rw [Real.sqrt_mul hK']
        have h1 : Real.sqrt K' ≤ 1 + K' := by
          nlinarith [Real.sq_sqrt hK', Real.sqrt_nonneg K']
        have h2 : Real.sqrt (curvNormK (G t) x 0) ≤ 1 + curvNormK (G t) x 0 := by
          nlinarith [Real.sq_sqrt hrm0, Real.sqrt_nonneg (curvNormK (G t) x 0)]
        exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
      have hstep : Real.sqrt (K' * curvNormK (G t) x 0)
          ≤ (1 + K') * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) :=
        le_trans hsqrt (mul_le_mul_of_nonneg_left (by linarith [hf0le]) (by linarith [hK']))
      have hA1 : Ce * ((Module.finrank ℝ E : ℝ) ^ (k + 4) * ((k : ℝ) + 4))
            * Real.sqrt (K' * curvNormK (G t) x 0)
            * (1 + Real.sqrt (curvNormK (G t) x k))
          ≤ Ce * ((Module.finrank ℝ E : ℝ) ^ (k + 4) * ((k : ℝ) + 4))
            * (1 + K') * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
            * (1 + Real.sqrt (curvNormK (G t) x k)) := by
        have hC1 : (0 : ℝ) ≤ Ce * ((Module.finrank ℝ E : ℝ) ^ (k + 4) * ((k : ℝ) + 4)) := by
          positivity
        calc Ce * ((Module.finrank ℝ E : ℝ) ^ (k + 4) * ((k : ℝ) + 4))
              * Real.sqrt (K' * curvNormK (G t) x 0)
              * (1 + Real.sqrt (curvNormK (G t) x k))
            ≤ Ce * ((Module.finrank ℝ E : ℝ) ^ (k + 4) * ((k : ℝ) + 4))
              * ((1 + K') * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j))
              * (1 + Real.sqrt (curvNormK (G t) x k)) := by
              gcongr
          _ = Ce * ((Module.finrank ℝ E : ℝ) ^ (k + 4) * ((k : ℝ) + 4))
              * (1 + K') * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
              * (1 + Real.sqrt (curvNormK (G t) x k)) := by ring
      have hA2 : C₀ * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
            * (1 + Real.sqrt (curvNormK (G t) x k))
          ≤ C₀ * (1 + K') * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
            * (1 + Real.sqrt (curvNormK (G t) x k)) := by
        have hB : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j := by linarith
        have hC : (0 : ℝ) ≤ 1 + Real.sqrt (curvNormK (G t) x k) := by positivity
        have hleB : (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
            ≤ (1 + K') * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) := by
          nlinarith [hB, hK', hsum0]
        calc C₀ * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
              * (1 + Real.sqrt (curvNormK (G t) x k))
            = C₀ * ((1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
                * (1 + Real.sqrt (curvNormK (G t) x k))) := by ring
          _ ≤ C₀ * (((1 + K') * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j))
                * (1 + Real.sqrt (curvNormK (G t) x k))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hleB hC) hC₀
          _ = C₀ * (1 + K') * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
              * (1 + Real.sqrt (curvNormK (G t) x k)) := by ring
      have hfin : |(∑ r : Fin (k + 4) → Fin (Module.finrank ℝ E), A r * κ r t) + D ι - lapE|
          ≤ (C₀ + Ce * ((Module.finrank ℝ E : ℝ) ^ (k + 4) * ((k : ℝ) + 4)))
            * (1 + K') * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
            * (1 + Real.sqrt (curvNormK (G t) x k)) := by
        refine le_trans hsplit ?_
        linarith [hDbound, hXf', hA1, hA2]
      exact hfin

/-! ## Discharging the structural hypotheses of the reduction

The evaluation bound `heval` and the frame expansion `hexp` of `evolCompK_of_fixedC` are now
*theorems* of the workspace:

* `Work.Diff.EXT.KrMulti_of_Kpt` (`covK_valueDep.lean`, proved) gives the value-level
  multilinearity `KrMulti g x k` of the tower, and `Work.Diff.EXT.covKRm_expand_packed`
  (`covKRm_expand_packed.lean`, proved) turns it into the multilinear expansion in an arbitrary
  frame — exactly the hypothesis `hexp`;
* `Work.Diff.EXT.covKRmExt_eval_bound` (`covKRmExt_eval_bound.lean`, proved) is the evaluation
  bound, which is the hypothesis `heval` because `covKRm` is *defined* as `covKRmExt` on the
  `Classical.epsilon`-chosen smooth extensions.

Consequently the whole content of `EvolCompK k` is reduced (in `evolCompK_of_fixed_estimateC`) to
the *fixed-vector* estimate alone. -/

/-- **The evaluation bound** in the vocabulary of `EvolCompK` (from
`Work.Diff.EXT.covKRmExt_eval_bound`, since `covKRm` is `covKRmExt` on smooth extensions). -/
theorem heval_ofC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) :
    ∃ Ce : ℝ, 0 ≤ Ce ∧
      ∀ (g : Submission.Diff.SMet I M) (x : M) (v : Fin k → TangentSpace I x)
        (a b c d : TangentSpace I x),
        |covKRm g x k v a b c d|
          ≤ Ce * (1 + Real.sqrt (curvNormK g x k))
              * (Finset.univ.prod (fun i : Fin k => Real.sqrt (g.inner x (v i) (v i)))
                 * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
                 * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) := by
  obtain ⟨C, hC0, hC⟩ := Work.Diff.EXT.covKRmExt_eval_bound (I := I) (M := M) hLC k
  exact ⟨C, hC0, fun g x v a b c d => hC g x v a b c d⟩

/-- **The frame expansion** in the vocabulary of `EvolCompK` (from the value-level multilinearity
`Work.Diff.EXT.KrMulti_of_Kpt`, packaged as the multilinear map `Work.Diff.EXT.krVLin` of
`covK_frameInv.lean`). -/
theorem hexp_ofC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) :
    ∀ (g : Submission.Diff.SMet I M) (x : M) {n : ℕ} (a : Fin n → TangentSpace I x)
      (p : Fin (k + 4) → TangentSpace I x) (cp : Fin (k + 4) → Fin n → ℝ),
      (∀ j : Fin (k + 4), ∑ r, cp j r • a r = p j) →
      covKRm g x k (fun i : Fin k => p (Fin.castAdd 4 i)) (p (Fin.natAdd k 0))
          (p (Fin.natAdd k 1)) (p (Fin.natAdd k 2)) (p (Fin.natAdd k 3))
        = ∑ r : Fin (k + 4) → Fin n, (∏ j : Fin (k + 4), cp j (r j)) *
            covKRm g x k (fun i : Fin k => a (r (Fin.castAdd 4 i))) (a (r (Fin.natAdd k 0)))
              (a (r (Fin.natAdd k 1))) (a (r (Fin.natAdd k 2))) (a (r (Fin.natAdd k 3))) := by
  intro g x n a p cp hp
  classical
  have hsum : ∀ (q : Fin (k + 4) → TangentSpace I x),
      (fun i : Fin k ⊕ Fin 4 => q (finSumFinEquiv i))
        = Sum.elim (fun i : Fin k => q (Fin.castAdd 4 i))
            (fun j : Fin 4 => q (Fin.natAdd k j)) := by
    intro q
    funext s
    rcases s with i | j <;>
      simp only [Sum.elim_inl, Sum.elim_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  have hkr : ∀ (q : Fin (k + 4) → TangentSpace I x),
      krVLin g x k (Work.Diff.EXT.KrMulti_of_Kpt hLC g x k) q
        = covKRm g x k (fun i : Fin k => q (Fin.castAdd 4 i)) (q (Fin.natAdd k 0))
            (q (Fin.natAdd k 1)) (q (Fin.natAdd k 2)) (q (Fin.natAdd k 3)) := by
    intro q
    rw [Work.Diff.EXT.krVLin_apply, hsum q]
    rfl
  have hp' : (fun j : Fin (k + 4) => ∑ r, cp j r • a r) = p := funext hp
  rw [← hkr p, ← hp', MultilinearMap.map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [MultilinearMap.map_smul_univ, smul_eq_mul, hkr (fun j => a (r j))]

/-- **`EvolCompK k` from the fixed-vector estimate alone.**

All the structural ingredients of `evolCompK_of_fixedC` (`heval`, `hexp`, and `LCSmooth`) are now
theorems of the workspace, so the whole remaining content of the `k`-th order Shi estimate in a
moving orthonormal frame is the *fixed-vector* evolution estimate at level `k`. -/
theorem evolCompK_of_fixed_estimateC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (hk : 1 ≤ k)
    (hfix : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ), Submission.Diff.IsRicciFlow G T →
        ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∀ (v : Fin k → TangentSpace I x) (a b c d : TangentSpace I x), ∃ D : ℝ,
          HasDerivWithinAt (fun s ↦ covKRm (G s) x k v a b c d) D (Set.Ico 0 T) t ∧
          |D - lapCovKRm (G t) x k v a b c d|
            ≤ C₀ * (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j)
                * (1 + Real.sqrt (curvNormK (G t) x k))
                * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i)))
                   * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
                   * Real.sqrt ((G t).inner x c c) * Real.sqrt ((G t).inner x d d)))
    : EvolCompK (I := I) (M := M) k := by
  obtain ⟨Ce, hCe, heval⟩ := heval_ofC (I := I) (M := M) hLC k
  obtain ⟨C₀, hC₀, hfix'⟩ := hfix
  exact evolCompK_of_fixedC k hk Ce hCe heval C₀ hC₀ hfix' (hexp_ofC (I := I) (M := M) hLC k)


/-! ## State of the proof, and the exact remaining obligation

**Proved in this file** (all sorry-free, axiom-clean):

* `inner_le_sqrt_of_isONFrameC`, `hasDerivWithinAt_inner_constC`, `curvNormK_zero_eq_rmNormSq` —
  the small tools of the moving-frame reduction;
* `evolCompK_of_fixedC` — **the general-`k` moving-frame reduction**: `EvolCompK k` follows from the
  *fixed-vector* evolution estimate at level `k`, the evaluation bound `heval` and the frame
  expansion `hexp`.  This is the general-`k` form of the proved
  `Work.Diff.GE.frame_evol_of_fixed` (`k = 1`);
* `heval_ofC` — the evaluation bound, from the *proved* `Work.Diff.EXT.covKRmExt_eval_bound`
  (`covKRm` *is* `covKRmExt` on the `Classical.epsilon`-chosen extensions);
* `hexp_ofC` — the frame expansion, from the *proved* value-level multilinearity
  `Work.Diff.EXT.KrMulti_of_Kpt` (packaged as the multilinear map `Work.Diff.EXT.krVLin`);
* `evolCompK_of_fixed_estimateC` — hence **the whole content of `EvolCompK k` is now reduced to the
  fixed-vector estimate at level `k` alone**.

So the remaining obligation is exactly:

> for every `k ≥ 1` there is `C` such that for every Ricci flow `G` on `[0,T)`, every `t ∈ [0,T)`,
> every `x` and all fixed vectors `v₁,…,v_k, a,b,c,d ∈ TₓM`,
> `∃ D, HasDerivWithinAt (s ↦ (∇^k Rm)(G s)(x)(v₁,…,v_k;a,b,c,d)) D ([0,T)) t ∧
>  |D − Δ(∇^kRm)(G t)(x)(v₁,…,v_k;a,b,c,d)| ≤ C (1 + Σ_{j<k} f_j)(1 + √(f_k)) ∏‖·‖`,
> where `f_j = curvNormK (G t) x j` and `Δ` is the rough Laplacian.

**Route for that obligation** (no induction on `k` — the "diagonal" induction
`RV_{k+1} = ∇RV_k + (∂ₜ∇)T_k − [Δ,∇]T_k` is *circular*: bounding `RV_{k+1}` at derivative order `m`
needs `RV_k` at order `m+1`, and the diagonal ends at the level-`0` reaction at order `k`, which is
*equivalent* to the goal).  Use instead the non-inductive, explicit-level-0 route, for which the
ingredients are now concrete:

1. `Work.Diff.GE.reactionMap` (`reaction_map_defs.lean`, proved) is the **explicit** quadratic
   reaction map of the *fixed-vector* curvature evolution,
   `reactionMap R = Q R − Σ_p (Ric_{ip}R_{pjkl} + Ric_{jp}R_{ipkl} + Ric_{lp}R_{ijkp} + Ric_{kp}R_{ijpl})`;
   `Work.Diff.EXT.evolX.curvature_evolution_fixed` (in flight) is the corresponding level-`0`
   identity `∂ₜRm = ΔRm + reactionFormAt reactionMap`;
2. `∂ₜ(∇^kRm) = ∇^k(∂ₜRm) + C₁` and `Δ(∇^kRm) = ∇^k(ΔRm) + C₂`, where `C₁` collects the
   Leibniz/connection-variation corrections and `C₂` the `[Δ,∇]`-commutators (one step is
   `Work.Diff.EXT.lapCovKRm_comm_bound`, in flight); each term is a product of tower components of
   total order `≤ k`;
3. `|∇^k(reactionFormAt reactionMap)| ≤ C Σ_{i+j=k} √(f_i) √(f_j) ∏‖·‖`: the Leibniz rule for the
   *explicit quadratic natural form* `reactionMap` (contractions commute with `∇`);
4. the arithmetic `2√(f_if_j) ≤ f_i + f_j ≤ Σ_{j<k} f_j` (`i,j ≤ k−1`) and
   `√(f_0 f_k) ≤ (1+f_0)(1+√f_k)`.

Note that the same route also covers `k = 1`, so no separate base case is needed. -/

/-! ## The final assembly

The whole *frame-free* (fixed-vector) content of the `k`-th order Shi estimate is
`Work.Diff.EXT.EvolCompKFixReact k` (`evolCompKFixReact_allC.lean`, the "reaction ladder"), which
implies the one-sided fixed-vector estimate `EvolCompKFix k`
(`Work.Diff.EXT.evolCompKFix_of_reaction`), whose two-sided form is exactly the hypothesis `hfix`
of `evolCompK_of_fixed_estimateC` (`Work.Diff.EXT.twoSided_of_EvolCompKFix`).  Composing with the
moving-frame reduction and with `Work.Diff.T.lc_smooth` (which discharges `LCSmooth`) gives the
target `evolCompK_allC` — the composition is the theorem below; the last step of the file's target
is the single application of it to `Work.Diff.EXT.evolCompKFixReact_allC`. -/

/-- **`EvolCompK k` for all `k ≥ 1`, from the frame-free reaction ladder.** -/
theorem evolCompK_all_of_reactC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hR : ∀ k : ℕ, 1 ≤ k → Work.Diff.EXT.EvolCompKFixReact (I := I) (M := M) k) :
    ∀ k : ℕ, 1 ≤ k → Work.Diff.EXT.EvolCompK (I := I) (M := M) k := by
  intro k hk
  have hLC : Submission.Diff.LCSmooth I M := Work.Diff.T.lc_smooth
  exact evolCompK_of_fixed_estimateC (I := I) (M := M) hLC k hk
    (Work.Diff.EXT.twoSided_of_EvolCompKFix (I := I) (M := M) k
      (Work.Diff.EXT.evolCompKFix_of_reaction (I := I) (M := M) k hk (hR k hk)))


theorem evolCompK_allC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] :
    ∀ k : ℕ, 1 ≤ k → Work.Diff.EXT.EvolCompK (I := I) (M := M) k :=
  evolCompK_all_of_reactC (I := I) (M := M) Work.Diff.EXT.evolCompKFixReact_allC

end Work.Diff.EXT
