import Mathlib
import Submission.Work.Diff.Evol.RicDeriv
import Submission.Work.Diff.Evol.RicPhi
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.RL.covRm_linear_fst
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.kato_geodesic_frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Filter

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The Leibniz rule for the Levi-Civita connection

`LCSmooth I M` gives, as its third component, the challenge's metric compatibility
`IsMetricCompatible (lcOf g)` for every smooth metric `g`, which *is* the Leibniz rule
`v·⟪Y,Z⟫ = ⟪∇_v Y, Z⟫ + ⟪Y, ∇_v Z⟫` stated with the explicit metric `g.inner`. -/
theorem covRic_mvfderiv_inner_lc (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v : TangentSpace I x) {Y Z : Π y : M, TangentSpace I y}
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    mvfderiv I (fun y : M => g.inner y (Y y) (Z y)) x v
      = g.inner x (lcOf g Y x v) (Z x) + g.inner x (Y x) (lcOf g Z x v) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact (hLC g).2.2 Y Z hY hZ x v

/-! ## A smooth `g`-orthonormal frame near `x` with prescribed values at `x`

This is the Gram–Schmidt (Kato) construction of `Work.Diff.GE.katoFrame` applied to an arbitrary
smooth family `V` which is already `g`-orthonormal at `x`: the smoothed normalisation makes the
result globally smooth, and near `x` the smoothed Gram function agrees with the honest one, so that
`Work.Diff.GE.kato_orthonormal_algebra` gives the orthonormality.  Unlike
`Work.Diff.GE.kato_geodesic_frame` no jet correction is used, so nothing beyond the (unconditional)
algebraic part of the Kato development is needed. -/
theorem covRic_onFrame_family (g : SMet I M) (x : M)
    (V : katoIdx E → Π y : M, TangentSpace I y)
    (hVs : ∀ i, CMDiff ∞ (T% (V i)))
    (hVON : IsONFrame g x (fun i => V i x)) :
    (∀ i, CMDiff ∞ (T% (katoFrame g x V i))) ∧
      (∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => katoFrame g x V i y)) ∧
      (∀ i, katoFrame g x V i x = V i x) := by
  classical
  have key : ∀ m : ℕ, ∀ i : katoIdx E, i.val < m →
      (CMDiff ∞ (T% (katoFrame g x V i)))
      ∧ (katoFrame g x V i x = V i x)
      ∧ (∀ᶠ y in 𝓝 x, g.inner y (katoFrame g x V i y) (katoFrame g x V i y) = 1)
      ∧ (∀ᶠ y in 𝓝 x, ∀ k, k.val < i.val →
          g.inner y (katoFrame g x V i y) (katoFrame g x V k y) = 0) := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · have hIH : ∀ j, j.val < i.val →
            (CMDiff ∞ (T% (katoFrame g x V j)))
            ∧ (katoFrame g x V j x = V j x)
            ∧ (∀ᶠ y in 𝓝 x, g.inner y (katoFrame g x V j y) (katoFrame g x V j y) = 1)
            ∧ (∀ᶠ y in 𝓝 x, ∀ k, k.val < j.val →
                g.inner y (katoFrame g x V j y) (katoFrame g x V k y) = 0) :=
          fun j hj => ih j (by rw [← heq]; exact hj)
        obtain ⟨hUs, hGs⟩ :=
          kato_smooth g V (katoFrame g x V) i (hVs i) (fun j hj => (hIH j hj).1)
        have hON : ∀ j, j.val < i.val → g.inner x (V i x) (V j x) = 0 := by
          intro j hj
          have hne : i ≠ j := by
            intro hij; rw [← hij] at hj; exact absurd hj (Nat.lt_irrefl _)
          rw [hVON i j, ite_eq_right hne]
        have hUx : katoU g V (katoFrame g x V) i x = V i x :=
          katoU_apply_x g x V (katoFrame g x V) i (fun j hj => (hIH j hj).2.1) hON
        have hV1 : g.inner x (V i x) (V i x) = 1 := by
          rw [hVON i i, ite_eq_left rfl]
        have hfx : 0 < katoGram g V (katoFrame g x V) i x := by
          rw [katoGram_apply_x g x V (katoFrame g x V) i hUx hV1]; norm_num
        obtain ⟨hFpos, hFs, hCs, hCeq, hFx, hFeq⟩ :=
          kato_smooth_norm g x V (katoFrame g x V) i hGs hfx
        have hCx : katoC g x V (katoFrame g x V) i x = 1 :=
          katoC_apply_x g x V (katoFrame g x V) i
            (by rw [hFx, katoGram_apply_x g x V (katoFrame g x V) i hUx hV1])
        have hWx : katoFrame g x V i x = V i x := by
          rw [katoFrame_eq g x V i]
          show katoC g x V (katoFrame g x V) i x • katoU g V (katoFrame g x V) i x = V i x
          rw [hCx, hUx, one_smul]
        have hWs : CMDiff ∞ (T% (katoFrame g x V i)) := by
          rw [katoFrame_eq g x V i]
          exact hCs.smul_section hUs
        have hdiag_prev : ∀ᶠ y in 𝓝 x, ∀ j, j.val < i.val →
            g.inner y (katoFrame g x V j y) (katoFrame g x V j y) = 1 := by
          rw [Filter.eventually_all]
          intro j
          by_cases hj : j.val < i.val
          · filter_upwards [(hIH j hj).2.2.1] with y hy
            exact fun _ => hy
          · exact Filter.Eventually.of_forall fun y h => absurd h hj
        have hoff_prev : ∀ᶠ y in 𝓝 x, ∀ j, j.val < i.val → ∀ k, k.val < j.val →
            g.inner y (katoFrame g x V j y) (katoFrame g x V k y) = 0 := by
          rw [Filter.eventually_all]
          intro j
          by_cases hj : j.val < i.val
          · filter_upwards [(hIH j hj).2.2.2] with y hy
            exact fun _ => hy
          · exact Filter.Eventually.of_forall fun y h => absurd h hj
        have hbump1 : ∀ᶠ y in 𝓝 x,
            katoBump (I := I) (katoGram g V (katoFrame g x V) i) x y = 1 :=
          (katoBump_spec hGs hfx).2.2.2.2
        have hfpos_ev : ∀ᶠ y in 𝓝 x, 0 < katoGram g V (katoFrame g x V) i y :=
          (hGs x).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hfx)
        have hdiag_i : ∀ᶠ y in 𝓝 x,
            g.inner y (katoFrame g x V i y) (katoFrame g x V i y) = 1 := by
          filter_upwards [hbump1, hfpos_ev, hdiag_prev, hoff_prev] with y hb hf hp ho
          rw [katoFrame_eq g x V i]
          exact (kato_orthonormal_algebra g x V (katoFrame g x V) i y hb hf hp ho).1
        have hoff_i : ∀ᶠ y in 𝓝 x, ∀ k, k.val < i.val →
            g.inner y (katoFrame g x V i y) (katoFrame g x V k y) = 0 := by
          filter_upwards [hbump1, hfpos_ev, hdiag_prev, hoff_prev] with y hb hf hp ho
          intro k hk
          rw [katoFrame_eq g x V i]
          exact (kato_orthonormal_algebra g x V (katoFrame g x V) i y hb hf hp ho).2 k hk
        exact ⟨hWs, hWx, hdiag_i, hoff_i⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (key (i.val + 1) i (Nat.lt_succ_self _)).1
  · refine isONFrame_of_diag_off g x (katoFrame g x V) ?_ ?_
    · rw [Filter.eventually_all]
      intro i
      exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.2.1
    · rw [Filter.eventually_all]
      intro i
      exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.2.2
  · intro i
    exact (key (i.val + 1) i (Nat.lt_succ_self _)).2.1

/-! ## The frame derivative is skew-adjoint

For a smooth frame which is `g`-orthonormal near `x`, the pairing `y ↦ g.inner y (W m y) (W k y)` is
*constant* near `x`, so its derivative at `x` vanishes; the Leibniz rule turns that into
`g(∇_v W_m, W_k) + g(W_m, ∇_v W_k) = 0`. -/
theorem covRic_frame_skew (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    (W : katoIdx E → Π y : M, TangentSpace I y)
    (hWs : ∀ i, CMDiff ∞ (T% (W i)))
    (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y)) (m k : katoIdx E) :
    g.inner x (lcOf g (W m) x v) (W k x) + g.inner x (W m x) (lcOf g (W k) x v) = 0 := by
  have hconst : (fun y : M => g.inner y (W m y) (W k y))
      =ᶠ[𝓝 x] fun _ : M => (if m = k then (1 : ℝ) else 0) := by
    filter_upwards [hON] with y hy
    exact hy m k
  have h0 : mvfderiv I (fun y : M => g.inner y (W m y) (W k y)) x v = 0 := by
    rw [mvfderiv_congr_eventuallyEq hconst, mvfderiv_const]
    rfl
  have hleib := covRic_mvfderiv_inner_lc hLC g x v (Y := W m) (Z := W k) (hWs m) (hWs k)
  rw [hleib] at h0
  exact h0

/-! ## A skew-symmetric matrix contracted against a symmetric pair vanishes -/
theorem covRic_skew_sum_zero {ι : Type*} [Fintype ι] (c X : ι → ι → ℝ)
    (h : ∀ m k, c m k = -c k m) :
    (∑ m, ∑ k, c m k * X k m) + (∑ m, ∑ k, c m k * X m k) = 0 := by
  have hmain : (∑ m, ∑ k, c m k * X k m) = -(∑ m, ∑ k, c m k * X m k) := by
    rw [Finset.sum_comm]
    have hα : (∑ k, ∑ m, c m k * X k m) = ∑ m, ∑ k, c k m * X m k := rfl
    rw [hα, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h k m]; ring
  linarith

/-! ## The `∇W` correction sums cancel

Expanding `∇_v W_m` in the orthonormal frame turns the two families of corrections into a
skew-symmetric matrix contracted against the symmetric pair `(u,w) ↦ Rm(W_u, ·, W_w, ·)`, which
vanishes.  Consequently no *geodesic* frame is needed: any smooth orthonormal frame near `x` with
the prescribed values at `x` computes `∇Ric` as the trace of `∇Rm`. -/
theorem covRic_frame_correction_zero (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v : TangentSpace I x) (W : katoIdx E → Π y : M, TangentSpace I y)
    (hWs : ∀ i, CMDiff ∞ (T% (W i)))
    (hON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y)) (a b : TangentSpace I x) :
    (∑ m, rmP g x (lcOf g (W m) x v) a (W m x) b)
      + (∑ m, rmP g x (W m x) a (lcOf g (W m) x v) b) = 0 := by
  classical
  have hONx : IsONFrame g x (fun m => W m x) := hON.self_of_nhds
  have hskew : ∀ m k, g.inner x (lcOf g (W m) x v) (W k x)
      = -g.inner x (lcOf g (W k) x v) (W m x) := by
    intro m k
    have h := covRic_frame_skew hLC g x v W hWs hON m k
    rw [← g.symm x (lcOf g (W k) x v) (W m x)] at h
    linarith
  by_cases hfr : 0 < Module.finrank ℝ E
  · have hexp : ∀ m, lcOf g (W m) x v = ∑ k, g.inner x (lcOf g (W m) x v) (W k x) • W k x :=
      fun m => (sum_smul_inner_eq_self g x hfr (fun i => W i x) hONx (lcOf g (W m) x v)).symm
    have hP : (∑ m, rmP g x (lcOf g (W m) x v) a (W m x) b)
        = ∑ m, ∑ k, g.inner x (lcOf g (W m) x v) (W k x) * rmP g x (W k x) a (W m x) b := by
      refine Finset.sum_congr rfl fun m _ => ?_
      conv_lhs => rw [hexp m]
      exact rmP_sum_fst hLC g x Finset.univ
        (fun k => g.inner x (lcOf g (W m) x v) (W k x)) (fun k => W k x) a (W m x) b
    have hR : (∑ m, rmP g x (W m x) a (lcOf g (W m) x v) b)
        = ∑ m, ∑ k, g.inner x (lcOf g (W m) x v) (W k x) * rmP g x (W m x) a (W k x) b := by
      refine Finset.sum_congr rfl fun m _ => ?_
      conv_lhs => rw [hexp m]
      exact rmP_sum_thd hLC g x Finset.univ
        (fun k => g.inner x (lcOf g (W m) x v) (W k x)) (fun k => W k x) (W m x) a b
    rw [hP, hR]
    exact covRic_skew_sum_zero (fun m k => g.inner x (lcOf g (W m) x v) (W k x))
      (fun u w => rmP g x (W u x) a (W w x) b) hskew
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hfr
    haveI : IsEmpty (katoIdx E) := by
      show IsEmpty (Fin (Module.finrank ℝ E))
      rw [h0]
      infer_instance
    simp [Finset.univ_eq_empty]

-- `(∇_v Ric)(a,b) = ∑_m (∇_v Rm)(e_m, a, e_m, b)` in an orthonormal frame `e`: the covariant
-- derivative of the Ricci tensor is the metric trace of the covariant derivative of the curvature.
-- The pointwise trace identity `ricAt (lcOf g) y u v = ∑_m rmP g y (e m) u (e m) v` for an
-- orthonormal frame is the hypothesis `htr`.  Route: take a smooth orthonormal frame `W` near `x`
-- with `W m x = onFrame g x m` (`Work.Diff.GE.covRic_onFrame_family`, the Gram–Schmidt construction
-- `Work.Diff.GE.katoFrame` applied to `smoothExt x (onFrame g x ·)`: no jet correction is needed);
-- with `A := smoothExt x a`, `B := smoothExt x b` the functions `ricF g A B` and
-- `y ↦ ∑ m, rmP g y (W m y) (A y) (W m y) (B y)` agree near `x` by `htr`
-- (`Work.Diff.GE.mvfderiv_congr_eventuallyEq`, `Work.Diff.GE.Kato3.mvfderiv_sum`); computing both
-- sides with `Work.Diff.Evol.mvfderiv_ricF_eq` and the definition of `Work.Diff.GE.dRmPhi` produces
-- the `Rm(∇_v W_m, ...)` corrections, which cancel against each other by the skew-adjointness of
-- `∇_v W` (`Work.Diff.GE.covRic_frame_correction_zero`), while the `∇_v A`, `∇_v B` corrections
-- cancel against the two `ricAt` corrections (by `htr` at `x`); the remaining terms are
-- `∑ m, covRm g x v (W m x) (A x) (W m x) (B x) = ∑ m, covRm g x v (e_m) a (e_m) b` by
-- `Work.Diff.GE.Kato3.covRm_field_form`, and `Work.Diff.Evol.covRic_eq_dRicPhi` identifies `dRicPhi`
-- on `smoothExt`.
theorem covRic_eq_sum_covRm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (htr : ∀ (g : Submission.Diff.SMet I M) (y : M)
        (e : Fin (Module.finrank ℝ E) → TangentSpace I y),
        Submission.Diff.IsONFrame g y e →
          ∀ u v : TangentSpace I y,
            Submission.Diff.ricAt (Submission.Diff.lcOf g) y u v
              = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
                  (fun m => Submission.Diff.rmP g y (e m) u (e m) v))
    (g : Submission.Diff.SMet I M) (x : M) (v a b : TangentSpace I x) :
    Work.Diff.Evol.covRic g x v a b
      = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun m => Submission.Diff.covRm g x v (Submission.Diff.onFrame g x m) a
            (Submission.Diff.onFrame g x m) b) := by
  classical
  -- a smooth `g`-orthonormal frame near `x` agreeing with the chosen frame at `x`
  have hVs : ∀ i : katoIdx E, CMDiff ∞ (T% (smoothExt x (onFrame g x i))) :=
    fun i => smoothExt_cmdiff x (onFrame g x i)
  have hVON : IsONFrame g x (fun i => smoothExt x (onFrame g x i) x) := by
    have h : (fun i => smoothExt x (onFrame g x i) x) = onFrame g x := by
      funext i; exact smoothExt_apply x (onFrame g x i)
    rw [h]; exact isONFrame_onFrame g x
  obtain ⟨hWs0, hWON0, hWx0⟩ :=
    covRic_onFrame_family g x (fun i => smoothExt x (onFrame g x i)) hVs hVON
  set W : katoIdx E → Π y : M, TangentSpace I y :=
    katoFrame g x (fun i => smoothExt x (onFrame g x i)) with hWdef
  have hWs : ∀ i : katoIdx E, CMDiff ∞ (T% (W i)) := fun i => by rw [hWdef]; exact hWs0 i
  have hWON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => W i y) := by rw [hWdef]; exact hWON0
  have hWx : ∀ i : katoIdx E, W i x = onFrame g x i := by
    intro i; rw [hWx0 i, smoothExt_apply]
  have hONx : IsONFrame g x (fun m => W m x) := hWON.self_of_nhds
  -- the smooth extensions of `a` and `b`
  set A : Π y : M, TangentSpace I y := smoothExt x a with hA
  set B : Π y : M, TangentSpace I y := smoothExt x b with hB
  have hAs : CMDiff ∞ (T% A) := by rw [hA]; exact smoothExt_cmdiff x a
  have hBs : CMDiff ∞ (T% B) := by rw [hB]; exact smoothExt_cmdiff x b
  have hAx : A x = a := by rw [hA]; exact smoothExt_apply x a
  have hBx : B x = b := by rw [hB]; exact smoothExt_apply x b
  -- `Ric` and the frame trace agree near `x`
  have hsm : ∀ m : katoIdx E,
      CMDiff ∞ (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) :=
    fun m => rmP_fields_smooth hLC g (hWs m) hAs (hWs m) hBs
  have hagree : (Work.Diff.Evol.ricF g A B)
      =ᶠ[𝓝 x] (fun y : M => ∑ m, rmP g y (W m y) (A y) (W m y) (B y)) := by
    filter_upwards [hWON] with y hy
    simpa only [Work.Diff.Evol.ricF] using htr g y (fun m => W m y) hy (A y) (B y)
  have hkey : mvfderiv I (Work.Diff.Evol.ricF g A B) x v
      = ∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) x v := by
    have h := mvfderiv_congr_eventuallyEq (I := I) hagree
    exact (congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) h).trans
      (Kato3.mvfderiv_sum Finset.univ _ hsm x v)
  have hric := Work.Diff.Evol.mvfderiv_ricF_eq (I := I) (M := M) g x v A B
  -- the definition of `dRmPhi` on the frame
  have hdRm : ∀ m : katoIdx E,
      dRmPhi g x v (W m) A (W m) B
        = mvfderiv I (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) x v
          - rmP g x (lcOf g (W m) x v) (A x) (W m x) (B x)
          - rmP g x (W m x) (lcOf g A x v) (W m x) (B x)
          - rmP g x (W m x) (A x) (lcOf g (W m) x v) (B x)
          - rmP g x (W m x) (A x) (W m x) (lcOf g B x v) := by
    intro m
    simp only [dRmPhi]
  -- summing the definition of `dRmPhi` gives an identity relating the five sums
  have h1 : (∑ m, dRmPhi g x v (W m) A (W m) B)
      + (∑ m, rmP g x (lcOf g (W m) x v) (A x) (W m x) (B x))
      + (∑ m, rmP g x (W m x) (lcOf g A x v) (W m x) (B x))
      + (∑ m, rmP g x (W m x) (A x) (lcOf g (W m) x v) (B x))
      + (∑ m, rmP g x (W m x) (A x) (W m x) (lcOf g B x v))
      = ∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) x v := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hdRm m]
    ring
  -- the two frame-derivative corrections cancel
  have hPR : (∑ m, rmP g x (lcOf g (W m) x v) (A x) (W m x) (B x))
      + (∑ m, rmP g x (W m x) (A x) (lcOf g (W m) x v) (B x)) = 0 :=
    covRic_frame_correction_zero hLC g x v W hWs hWON (A x) (B x)
  -- the two `∇A`, `∇B` corrections are the `ricAt` corrections
  have hQr : (∑ m, rmP g x (W m x) (lcOf g A x v) (W m x) (B x))
      = ricAt (lcOf g) x (lcOf g A x v) (B x) :=
    (htr g x (fun m => W m x) hONx (lcOf g A x v) (B x)).symm
  have hYr : (∑ m, rmP g x (W m x) (A x) (W m x) (lcOf g B x v))
      = ricAt (lcOf g) x (A x) (lcOf g B x v) :=
    (htr g x (fun m => W m x) hONx (A x) (lcOf g B x v)).symm
  have h2 : (∑ m, mvfderiv I (fun y : M => rmP g y (W m y) (A y) (W m y) (B y)) x v)
      = Work.Diff.Evol.dRicPhi g x v A B
        + ricAt (lcOf g) x (lcOf g A x v) (B x)
        + ricAt (lcOf g) x (A x) (lcOf g B x v) := by
    rw [← hkey, hric]
  -- the trace of `∇Rm` is `dRicPhi`
  have hmain : Work.Diff.Evol.dRicPhi g x v A B
      = ∑ m, dRmPhi g x v (W m) A (W m) B := by
    linarith [h1, h2, hPR, hQr, hYr]
  -- rewrite `dRmPhi` back into `covRm`
  have hper : ∀ m : katoIdx E,
      dRmPhi g x v (W m) A (W m) B = covRm g x v (onFrame g x m) a (onFrame g x m) b := by
    intro m
    have h := Kato3.covRm_field_form (X₁ := W m) (X₂ := A) (X₃ := W m) (X₄ := B) hLC g x v
      (hWs m) hAs (hWs m) hBs
    rw [hWx m, hAx, hBx] at h
    exact h.symm
  have hDRsm : Work.Diff.Evol.dRicPhi g x v A B
      = Work.Diff.Evol.dRicPhi g x v (smoothExt x a) (smoothExt x b) := by
    rw [hA, hB]
  rw [Work.Diff.Evol.covRic_eq_dRicPhi (I := I) (M := M) g x v a b]
  rw [← hDRsm, hmain]
  exact Finset.sum_congr rfl (fun m _ => hper m)

end Work.Diff.GE
