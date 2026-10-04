import Mathlib
import Submission.Work.Diff.EXT.ConnCov.aTowerMovingDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Leibniz rule for an insertion (`pD_Ins`)

`Work.Diff.EXT.ConnCov.AMB.pD cov σ` is the *packed* recursion step of the tower: slot `0` of the
tuple is the direction and slots `1..N` are the slots of the object `σ`.  `AMB.Ins Δ τ` replaces
every slot field `τ_j` of `τ` by `Δ τ_j dir`.

The identity proved here is the derivative of an insertion: for a `(1,2)`-tensor `Δ` and an object
`τ` which is additive in its slots (`AMB.SlotAddP`),

  `pD cov (Ins Δ τ) (Y :: G) = ∑_j pD cov τ (Y :: G[j ↦ Δ (G_j) (G_0)])
                                + ∑_j τ (G[j ↦ ∇_Y Δ (G_j) (G_0)])`,

where `∇_Y Δ = AMB.nab cov Y Δ` is the honest tensor derivative of `Δ` along `Y`.  The
pairing-direction correction of the covariant derivative and the `Δ (X, ∇Z)` term of the Leibniz
rule cancel exactly, which is why no jets appear.

The proof is a term-by-term comparison of two finite sums: both sides are sums of `τ` applied to
tuples in which two slots have been replaced, and the two index sets match through the commuting
update `Function.update_comm`.  The only structural input is `AMB.SlotAddP` (used to split the
`AMB.nab`-insertion into its three pieces, and read backwards for subtraction).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The tools -/

/-- Differentiability of a finite sum of smooth scalar functions. -/
private lemma mdiffAt_sum' {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) {x : M}
    (hf : ∀ i, CMDiff ∞ (f i)) : MDiffAt (fun y : M => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h : (fun y : M => ∑ i ∈ (∅ : Finset ι), f i y) = fun _ : M => (0 : ℝ) := by
        funext z; simp
      rw [h]; exact mdifferentiableAt_const (c := (0 : ℝ))
  | insert a t ha ih =>
      have h : (fun z : M => ∑ j ∈ insert a t, f j z) = fun z : M => f a z + ∑ j ∈ t, f j z := by
        funext z; rw [Finset.sum_insert ha]
      rw [h]
      exact (hf a).mdifferentiableAt (by simp) |>.add ih

/-- `mvfderiv` of a finite sum of smooth functions.  (A local copy of `Kato3.mvfderiv_sum`, without
the `[T2Space M]` assumption of that file.) -/
private lemma mvfderiv_sum_sm {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) (x : M)
    (v : TangentSpace I x) (hf : ∀ i, CMDiff ∞ (f i)) :
    mvfderiv I (fun y : M => ∑ i ∈ s, f i y) x v = ∑ i ∈ s, mvfderiv I (f i) x v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h : (fun y : M => ∑ i ∈ (∅ : Finset ι), f i y) = fun _ : M => (0 : ℝ) := by
        funext z; simp
      rw [h]
      simp [mvfderiv_const]
  | insert a t ha ih =>
      have h : (fun z : M => ∑ j ∈ insert a t, f j z) = fun z : M => f a z + ∑ j ∈ t, f j z := by
        funext z; rw [Finset.sum_insert ha]
      have hplus : (fun z : M => f a z + ∑ j ∈ t, f j z)
          = f a + (fun z : M => ∑ j ∈ t, f j z) := rfl
      have hd : mvfderiv I (fun z : M => f a z + ∑ j ∈ t, f j z) x v
          = mvfderiv I (f a) x v + mvfderiv I (fun z : M => ∑ j ∈ t, f j z) x v := by
        rw [hplus]
        have hh := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v)
          (mvfderiv_add (x := x) (g := f a) (g' := fun z : M => ∑ j ∈ t, f j z)
            ((hf a).mdifferentiableAt (by simp)) ((mdiffAt_sum' t f hf)))
        simpa only [add_apply] using hh
      rw [h, hd, Finset.sum_insert ha, ih]

/-- **Slot additivity read backwards**: `AMB.SlotAddP τ` gives the subtraction rule in every
slot (on smooth fields). -/
private lemma slotAddP_sub {N : ℕ} {τ : AMB.Fam (I := I) (M := M) N}
    (had : AMB.SlotAddP (I := I) (M := M) τ)
    (j : Fin N) (H : Fin N → AMB.TF (I := I) (M := M)) (W W' : AMB.TF (I := I) (M := M))
    (hH : ∀ i, ATower.SmE I M (H i)) (hW : ATower.SmE I M W) (hW' : ATower.SmE I M W')
    (hsub : ATower.SmE I M (W - W')) (x : M) :
    τ (Function.update H j (W - W')) x
      = τ (Function.update H j W) x - τ (Function.update H j W') x := by
  have h1 := had j H W' (W - W') hH hW' hsub x
  have hfe : W' + (W - W') = W := by funext y; simp only [Pi.add_apply, Pi.sub_apply]; abel
  rw [hfe] at h1
  linarith

/-- The two sums over the *off-diagonal* pairs of a `Fintype` are exchanged by swapping the two
arguments of `F` (i.e. the roles of the two summation indices). -/
private lemma sum_erase_swap {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ι → ℝ) :
    (∑ j : ι, ∑ i ∈ Finset.univ.erase j, F i j) = ∑ m : ι, ∑ j ∈ Finset.univ.erase m, F m j := by
  have h1 : ∀ j : ι, (∑ i ∈ Finset.univ.erase j, F i j) = (∑ i : ι, F i j) - F j j := by
    intro j; rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
  have h2 : ∀ m : ι, (∑ j ∈ Finset.univ.erase m, F m j) = (∑ j : ι, F m j) - F m m := by
    intro m; rw [Finset.sum_erase_eq_sub (Finset.mem_univ m)]
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_congr rfl (fun m _ => h2 m)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_comm]

/-! ## The target -/

theorem pD_Ins
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) {N : ℕ}
    (τ : Work.Diff.EXT.ConnCov.AMB.Fam (I := I) (M := M) N)
    (Δ : Work.Diff.EXT.ConnCov.AMB.Tens12 (I := I) (M := M))
    (had : Work.Diff.EXT.ConnCov.AMB.SlotAddP (I := I) (M := M) τ)
    (hτsm : Work.Diff.EXT.ConnCov.AMB.SmP (I := I) (M := M) τ)
    (hcov : ∀ X Z : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M),
      Work.Diff.EXT.ATower.SmE I M X → Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmE I M (fun y => cov X y (Z y)))
    (hΔsm : ∀ X Z : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M),
      Work.Diff.EXT.ATower.SmE I M X → Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmE I M (Δ X Z))
    (Y : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (G : Fin (N+1) → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
    (hY : Work.Diff.EXT.ATower.SmE I M Y)
    (hG : ∀ i, Work.Diff.EXT.ATower.SmE I M (G i)) (x : M) :
    Work.Diff.EXT.ConnCov.AMB.pD cov (Work.Diff.EXT.ConnCov.AMB.Ins Δ τ) (Fin.cons Y G) x
      = (∑ j : Fin N,
          Work.Diff.EXT.ConnCov.AMB.pD cov τ
            (Fin.cons Y (Function.update (fun i : Fin N => G i.succ) j
              (Δ (G j.succ) (G 0)))) x)
        + (∑ j : Fin N,
            τ (Function.update (fun i : Fin N => G i.succ) j
              (Work.Diff.EXT.ConnCov.AMB.nab cov Y Δ (G j.succ) (G 0))) x) := by
  classical
  -- ### The `Ins`-evaluation and the `pD`-unfolding on cons-tuples
  have hInsG : (AMB.Ins Δ τ) G
      = fun y => ∑ j : Fin N, τ (Function.update (fun i : Fin N => G i.succ) j
          (Δ (G j.succ) (G 0))) y := rfl
  have hPDany : ∀ (σ : AMB.Fam (I := I) (M := M) (N+1))
      (K : Fin (N+1) → AMB.TF (I := I) (M := M)),
      AMB.pD cov σ (Fin.cons Y K) x = mvfderiv I (σ K) x (Y x)
        - ∑ i : Fin (N+1), σ (Function.update K i (fun y => cov (K i) y (Y y))) x := by
    intro σ K; simp only [AMB.pD, Fin.cons_succ, Fin.cons_zero]
  have hPDcons : ∀ (K : Fin N → AMB.TF (I := I) (M := M)),
      AMB.pD cov τ (Fin.cons Y K) x = mvfderiv I (τ K) x (Y x)
        - ∑ i : Fin N, τ (Function.update K i (fun y => cov (K i) y (Y y))) x := by
    intro K; simp only [AMB.pD, Fin.cons_succ, Fin.cons_zero]
  -- ### Smoothness of the inserted fields and the derivative of the `Ins`-sum
  have hτQ : ∀ (j : Fin N), CMDiff ∞ (τ (Function.update (fun i : Fin N => G i.succ) j
      (Δ (G j.succ) (G 0)))) := by
    intro j
    refine hτsm _ (fun i => ?_)
    by_cases hi : i = j
    · rw [hi, Function.update_self]; exact hΔsm (G j.succ) (G 0) (hG _) (hG 0)
    · rw [Function.update_of_ne hi]; exact hG _
  have hDD : mvfderiv I ((AMB.Ins Δ τ) G) x (Y x)
      = ∑ j : Fin N, mvfderiv I (τ (Function.update (fun i : Fin N => G i.succ) j
          (Δ (G j.succ) (G 0)))) x (Y x) := by
    rw [hInsG]
    exact mvfderiv_sum_sm Finset.univ
      (fun j => τ (Function.update (fun i : Fin N => G i.succ) j (Δ (G j.succ) (G 0))))
      x (Y x) hτQ
  -- ### Left-hand side
  have hL : AMB.pD cov (AMB.Ins Δ τ) (Fin.cons Y G) x
      = (∑ j : Fin N, mvfderiv I (τ (Function.update (fun i : Fin N => G i.succ) j
            (Δ (G j.succ) (G 0)))) x (Y x))
        - (∑ k : Fin (N+1), (AMB.Ins Δ τ) (Function.update G k
            (fun y => cov (G k) y (Y y))) x) := by
    rw [hPDany (AMB.Ins Δ τ) G, hDD]
  -- ### The correction sum of `pD (Ins Δ τ)`, split at `k = 0` and `k = m.succ`
  have hBB0 : (AMB.Ins Δ τ) (Function.update G 0 (fun y' => cov (G 0) y' (Y y'))) x
      = ∑ j : Fin N, τ (Function.update (fun i : Fin N => G i.succ) j
          (Δ (G j.succ) (fun y' => cov (G 0) y' (Y y')))) x := by
    have hj0 : ∀ j : Fin N,
        Function.update G 0 (fun y' => cov (G 0) y' (Y y')) j.succ = G j.succ :=
      fun j => Function.update_of_ne (Fin.succ_ne_zero j) _ G
    have hz0 : Function.update G 0 (fun y' => cov (G 0) y' (Y y')) 0
        = (fun y' => cov (G 0) y' (Y y')) := Function.update_self _ _ _
    simp only [AMB.Ins, hz0, hj0]
  have hBBs : (∑ m : Fin N, (AMB.Ins Δ τ) (Function.update G m.succ
        (fun y' => cov (G m.succ) y' (Y y'))) x)
      = ∑ m : Fin N, ∑ j : Fin N, τ (Function.update (Function.update (fun i : Fin N => G i.succ) m
          (fun y' => cov (G m.succ) y' (Y y'))) j
          (Δ ((Function.update (fun i : Fin N => G i.succ) m
            (fun y' => cov (G m.succ) y' (Y y'))) j) (G 0))) x := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hj2 : ∀ j : Fin N, Function.update G m.succ (fun y' => cov (G m.succ) y' (Y y')) j.succ
        = Function.update (fun i : Fin N => G i.succ) m
            (fun y' => cov (G m.succ) y' (Y y')) j := by
      intro j
      by_cases hj : j = m
      · rw [hj, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne (fun h => hj (Fin.succ_inj.mp h)), Function.update_of_ne hj]
    have hz2 : Function.update G m.succ (fun y' => cov (G m.succ) y' (Y y')) 0 = G 0 :=
      Function.update_of_ne (fun h => Fin.succ_ne_zero m h.symm) _ G
    simp only [AMB.Ins, hj2, hz2]
  have hB : (∑ k : Fin (N+1), (AMB.Ins Δ τ) (Function.update G k
        (fun y => cov (G k) y (Y y))) x)
      = (∑ j : Fin N, τ (Function.update (fun i : Fin N => G i.succ) j
            (Δ (G j.succ) (fun y' => cov (G 0) y' (Y y')))) x)
        + (∑ m : Fin N, ∑ j : Fin N, τ (Function.update (Function.update
            (fun i : Fin N => G i.succ) m (fun y' => cov (G m.succ) y' (Y y'))) j
            (Δ ((Function.update (fun i : Fin N => G i.succ) m
              (fun y' => cov (G m.succ) y' (Y y'))) j) (G 0))) x) := by
    rw [Fin.sum_univ_succ, hBB0, hBBs]
  -- ### Right-hand side: the `pD cov τ` part
  have hR : (∑ j : Fin N, AMB.pD cov τ (Fin.cons Y (Function.update
          (fun i : Fin N => G i.succ) j (Δ (G j.succ) (G 0)))) x)
        + (∑ j : Fin N, τ (Function.update (fun i : Fin N => G i.succ) j
            (AMB.nab cov Y Δ (G j.succ) (G 0))) x)
      = ((∑ j : Fin N, mvfderiv I (τ (Function.update (fun i : Fin N => G i.succ) j
            (Δ (G j.succ) (G 0)))) x (Y x))
          - (∑ j : Fin N, ∑ i : Fin N, τ (Function.update (Function.update
              (fun i : Fin N => G i.succ) j (Δ (G j.succ) (G 0))) i
              (fun y => cov (Function.update (fun i : Fin N => G i.succ) j
                (Δ (G j.succ) (G 0)) i) y (Y y))) x))
        + (∑ j : Fin N, τ (Function.update (fun i : Fin N => G i.succ) j
            (AMB.nab cov Y Δ (G j.succ) (G 0))) x) := by
    rw [show (∑ j : Fin N, AMB.pD cov τ (Fin.cons Y (Function.update
          (fun i : Fin N => G i.succ) j (Δ (G j.succ) (G 0)))) x)
        = ∑ j : Fin N, (mvfderiv I (τ (Function.update (fun i : Fin N => G i.succ) j
              (Δ (G j.succ) (G 0)))) x (Y x)
            - ∑ i : Fin N, τ (Function.update (Function.update (fun i : Fin N => G i.succ) j
                (Δ (G j.succ) (G 0))) i (fun y => cov (Function.update
                  (fun i : Fin N => G i.succ) j (Δ (G j.succ) (G 0)) i) y (Y y))) x)
        from Finset.sum_congr rfl (fun j _ => hPDcons (Function.update
          (fun i : Fin N => G i.succ) j (Δ (G j.succ) (G 0))))]
    rw [Finset.sum_sub_distrib]
  -- ### The double sum `SS`, split into its diagonal and its off-diagonal part
  have hSS : (∑ j : Fin N, ∑ i : Fin N, τ (Function.update (Function.update
        (fun i : Fin N => G i.succ) j (Δ (G j.succ) (G 0))) i (fun y => cov (Function.update
          (fun i : Fin N => G i.succ) j (Δ (G j.succ) (G 0)) i) y (Y y))) x)
      = (∑ j : Fin N, τ (Function.update (fun i : Fin N => G i.succ) j
            (fun y => cov (Δ (G j.succ) (G 0)) y (Y y))) x)
        + (∑ j : Fin N, ∑ i ∈ Finset.univ.erase j, τ (Function.update (Function.update
            (fun i : Fin N => G i.succ) i (fun y' => cov (G i.succ) y' (Y y'))) j
            (Δ (G j.succ) (G 0))) x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin N))
      (fun i => τ (Function.update (Function.update (fun i : Fin N => G i.succ) j
        (Δ (G j.succ) (G 0))) i (fun y => cov (Function.update (fun i : Fin N => G i.succ) j
          (Δ (G j.succ) (G 0)) i) y (Y y))) x) (Finset.mem_univ j)]
    have hoff : (∑ i ∈ Finset.univ.erase j, τ (Function.update (Function.update
          (fun i : Fin N => G i.succ) j (Δ (G j.succ) (G 0))) i (fun y => cov (Function.update
            (fun i : Fin N => G i.succ) j (Δ (G j.succ) (G 0)) i) y (Y y))) x)
        = ∑ i ∈ Finset.univ.erase j, τ (Function.update (Function.update
            (fun i : Fin N => G i.succ) i (fun y' => cov (G i.succ) y' (Y y'))) j
            (Δ (G j.succ) (G 0))) x := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hne : i ≠ j := (Finset.mem_erase.mp hi).1
      have htu : Function.update (Function.update (fun i : Fin N => G i.succ) j
            (Δ (G j.succ) (G 0))) i (fun y => cov (Function.update (fun i : Fin N => G i.succ) j
              (Δ (G j.succ) (G 0)) i) y (Y y))
          = Function.update (Function.update (fun i : Fin N => G i.succ) i
              (fun y' => cov (G i.succ) y' (Y y'))) j (Δ (G j.succ) (G 0)) := by
        rw [Function.update_of_ne hne]
        exact Function.update_comm (Ne.symm hne) (Δ (G j.succ) (G 0))
          (fun y' => cov (G i.succ) y' (Y y')) (fun i : Fin N => G i.succ)
      rw [htu]
    have hdiag : τ (Function.update (Function.update (fun i : Fin N => G i.succ) j
          (Δ (G j.succ) (G 0))) j (fun y => cov (Function.update (fun i : Fin N => G i.succ) j
            (Δ (G j.succ) (G 0)) j) y (Y y))) x
        = τ (Function.update (fun i : Fin N => G i.succ) j
            (fun y => cov (Δ (G j.succ) (G 0)) y (Y y))) x := by
      rw [Function.update_self, Function.update_idem]
    rw [hoff, hdiag]
    exact add_comm _ _
  -- ### The `k = m.succ` part `B1`, split at `j = m`
  have hB1 : (∑ m : Fin N, ∑ j : Fin N, τ (Function.update (Function.update
        (fun i : Fin N => G i.succ) m (fun y' => cov (G m.succ) y' (Y y'))) j
        (Δ ((Function.update (fun i : Fin N => G i.succ) m
          (fun y' => cov (G m.succ) y' (Y y'))) j) (G 0))) x)
      = (∑ m : Fin N, τ (Function.update (fun i : Fin N => G i.succ) m
            (Δ (fun y' => cov (G m.succ) y' (Y y')) (G 0))) x)
        + (∑ m : Fin N, ∑ j ∈ Finset.univ.erase m, τ (Function.update (Function.update
            (fun i : Fin N => G i.succ) m (fun y' => cov (G m.succ) y' (Y y'))) j
            (Δ (G j.succ) (G 0))) x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin N))
      (fun j => τ (Function.update (Function.update (fun i : Fin N => G i.succ) m
        (fun y' => cov (G m.succ) y' (Y y'))) j (Δ ((Function.update
          (fun i : Fin N => G i.succ) m (fun y' => cov (G m.succ) y' (Y y'))) j) (G 0))) x)
      (Finset.mem_univ m)]
    have hdiag : τ (Function.update (Function.update (fun i : Fin N => G i.succ) m
          (fun y' => cov (G m.succ) y' (Y y'))) m (Δ ((Function.update
            (fun i : Fin N => G i.succ) m (fun y' => cov (G m.succ) y' (Y y'))) m) (G 0))) x
        = τ (Function.update (fun i : Fin N => G i.succ) m
            (Δ (fun y' => cov (G m.succ) y' (Y y')) (G 0))) x := by
      rw [Function.update_self, Function.update_idem]
    have hoff : (∑ j ∈ Finset.univ.erase m, τ (Function.update (Function.update
          (fun i : Fin N => G i.succ) m (fun y' => cov (G m.succ) y' (Y y'))) j
          (Δ ((Function.update (fun i : Fin N => G i.succ) m
            (fun y' => cov (G m.succ) y' (Y y'))) j) (G 0))) x)
        = ∑ j ∈ Finset.univ.erase m, τ (Function.update (Function.update
            (fun i : Fin N => G i.succ) m (fun y' => cov (G m.succ) y' (Y y'))) j
            (Δ (G j.succ) (G 0))) x := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hne : j ≠ m := (Finset.mem_erase.mp hj).1
      rw [Function.update_of_ne hne]
    rw [hoff, hdiag]
    exact add_comm _ _
  -- ### The two off-diagonal sums agree (the two indices are swapped)
  have hOff : (∑ j : Fin N, ∑ i ∈ Finset.univ.erase j, τ (Function.update (Function.update
        (fun i : Fin N => G i.succ) i (fun y' => cov (G i.succ) y' (Y y'))) j
        (Δ (G j.succ) (G 0))) x)
      = ∑ m : Fin N, ∑ j ∈ Finset.univ.erase m, τ (Function.update (Function.update
          (fun i : Fin N => G i.succ) m (fun y' => cov (G m.succ) y' (Y y'))) j
          (Δ (G j.succ) (G 0))) x :=
    sum_erase_swap (fun i j => τ (Function.update (Function.update (fun i : Fin N => G i.succ) i
      (fun y' => cov (G i.succ) y' (Y y'))) j (Δ (G j.succ) (G 0))) x)
  -- ### The `nab`-sum, expanded with the subtraction rule
  have hRHS2 : (∑ j : Fin N, τ (Function.update (fun i : Fin N => G i.succ) j
        (AMB.nab cov Y Δ (G j.succ) (G 0))) x)
      = (∑ j : Fin N, τ (Function.update (fun i : Fin N => G i.succ) j
            (fun y => cov (Δ (G j.succ) (G 0)) y (Y y))) x)
        - (∑ j : Fin N, τ (Function.update (fun i : Fin N => G i.succ) j
            (Δ (fun y' => cov (G j.succ) y' (Y y')) (G 0))) x)
        - (∑ j : Fin N, τ (Function.update (fun i : Fin N => G i.succ) j
            (Δ (G j.succ) (fun y' => cov (G 0) y' (Y y')))) x) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hA : ATower.SmE I M (fun y => cov (Δ (G j.succ) (G 0)) y (Y y)) :=
      hcov _ _ (hΔsm _ _ (hG _) (hG 0)) hY
    have hV : ATower.SmE I M (fun y' => cov (G j.succ) y' (Y y')) := hcov _ _ (hG _) hY
    have hV0 : ATower.SmE I M (fun y' => cov (G 0) y' (Y y')) := hcov _ _ (hG 0) hY
    have hC1 : ATower.SmE I M (Δ (fun y' => cov (G j.succ) y' (Y y')) (G 0)) :=
      hΔsm _ _ hV (hG 0)
    have hC2 : ATower.SmE I M (Δ (G j.succ) (fun y' => cov (G 0) y' (Y y'))) :=
      hΔsm _ _ (hG _) hV0
    have hsub1 : ATower.SmE I M ((fun y => cov (Δ (G j.succ) (G 0)) y (Y y))
        - (Δ (fun y' => cov (G j.succ) y' (Y y')) (G 0))) := ContMDiff.sub_section hA hC1
    have h2 := slotAddP_sub (I := I) (M := M) had j (fun i : Fin N => G i.succ)
      (fun y => cov (Δ (G j.succ) (G 0)) y (Y y))
      (Δ (fun y' => cov (G j.succ) y' (Y y')) (G 0))
      (fun i => hG _) hA hC1 hsub1 x
    have h3 := slotAddP_sub (I := I) (M := M) had j (fun i : Fin N => G i.succ)
      ((fun y => cov (Δ (G j.succ) (G 0)) y (Y y))
        - (Δ (fun y' => cov (G j.succ) y' (Y y')) (G 0)))
      (Δ (G j.succ) (fun y' => cov (G 0) y' (Y y')))
      (fun i => hG _) hsub1 hC2 (ContMDiff.sub_section hsub1 hC2) x
    rw [show AMB.nab cov Y Δ (G j.succ) (G 0)
        = ((fun y => cov (Δ (G j.succ) (G 0)) y (Y y))
            - (Δ (fun y' => cov (G j.succ) y' (Y y')) (G 0)))
          - (Δ (G j.succ) (fun y' => cov (G 0) y' (Y y'))) from rfl]
    rw [h3, h2]
  -- ### Assembly
  rw [hL, hR, hB, hB1, hSS, hOff, hRHS2]
  ring

end Work.Diff.EXT.ConnCov
