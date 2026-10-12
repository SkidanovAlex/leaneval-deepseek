import ChallengeDeps
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Submission.Work.BoseSym.Assemble.hsub_liminf_lsc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lower semicontinuity of the Dirichlet form along a *given* subsequence

This is the subsequence form of `Work.BoseSym.Assemble.hsub_liminf_lsc`: here the
convergent subsequence `φ` and the limit `q` are produced *together*, so that the
statement also records the strong `L²` convergence
`(p (φ n)).1 → (q.1 : L²)`.

The mathematical content is identical to the proof of `hsub_liminf_lsc` (Rellich
compactness for the function part, a Hahn–Banach/Riesz argument for the gradient
part, and monotone convergence for the weighted potential), with the convergence
statement kept rather than discarded.  All the infrastructure (`Xsp`, `toX`,
`projFirst`, `projW`, `HsubX`, ...) is imported from that module.
-/

namespace Work.BoseSym.Assemble

open MeasureTheory Filter
open scoped Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem hsub_liminf_lsc_subseq {N : ℕ} {L : ℝ} {C C' : ℝ}
    (p : ℕ → Work.BoseSym.Hsub N L) (hp1 : ∀ n, Work.BoseSym.l2Sq ((p n : Work.BoseSym.Amb N)) = 1)
    (hC : ∀ n, Work.BoseSym.gSq ((p n : Work.BoseSym.Amb N)) ≤ C)
    {W : ℕ → Work.BoseSym.Conf N → ℝ} {Wlim : Work.BoseSym.Conf N → ℝ}
    (hW0 : ∀ n, 0 ≤ W n) (hWlim0 : 0 ≤ Wlim)
    (hWm : ∀ n, MeasureTheory.AEStronglyMeasurable (W n)
      (MeasureTheory.volume.restrict (BoseGases.box N L)))
    (hWlimm : MeasureTheory.AEStronglyMeasurable Wlim
      (MeasureTheory.volume.restrict (BoseGases.box N L)))
    (hWmono : ∀ n x, W n x ≤ W (n + 1) x)
    (hWtend : ∀ x, Filter.Tendsto (fun n => W n x) Filter.atTop (nhds (Wlim x)))
    (hC'i : ∀ n, MeasureTheory.IntegrableOn
      (fun x => W n x * (((p n : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
      (BoseGases.box N L) MeasureTheory.volume)
    (hC'b : ∀ n, ∫ x in BoseGases.box N L,
        W n x * (((p n : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2 ≤ C') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ q : Work.BoseSym.Hsub N L,
      Work.BoseSym.l2Sq (q : Work.BoseSym.Amb N) = 1 ∧
      Filter.Tendsto (fun n => ((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.L2 N))
        Filter.atTop (nhds (((q : Work.BoseSym.Amb N).1 : Work.BoseSym.L2 N))) ∧
      MeasureTheory.IntegrableOn
        (fun x => Wlim x * (((q : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
        (BoseGases.box N L) MeasureTheory.volume ∧
      Work.BoseSym.gSq (q : Work.BoseSym.Amb N) + ∫ x in BoseGases.box N L,
          Wlim x * (((q : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2
        ≤ Filter.liminf (fun n => Work.BoseSym.gSq ((p (φ n) : Work.BoseSym.Amb N))
            + ∫ x in BoseGases.box N L,
                W (φ n) x * (((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
            Filter.atTop := by
  classical
  -- (0) the graph norm is bounded
  have hSq_le : ∀ n, Work.BoseSym.hSq ((p n : Work.BoseSym.Amb N)) ≤ C + 1 := by
    intro n
    have h1 := hp1 n
    simp only [Work.BoseSym.hSq, h1]
    linarith [hC n]
  -- (1) Rellich: strong `L²` convergence of the function parts
  obtain ⟨φ, hφ, w, hw⟩ := Rellich.rellich N L (C + 1) p hSq_le
  have hwt : Tendsto (fun n => ((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.L2 N))
      Filter.atTop (nhds w) := hw
  -- (2) the limit has norm one
  have hwnorm : ‖w‖ = 1 := by
    have h1 : Tendsto (fun n => ‖((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.L2 N)‖)
        Filter.atTop (nhds ‖w‖) := hwt.norm
    have h2 : (fun n => ‖((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.L2 N)‖)
        = fun _ => (1 : ℝ) := by
      funext n
      have h3 := hp1 (φ n)
      simp only [Work.BoseSym.l2Sq] at h3
      nlinarith [norm_nonneg (((p (φ n) : Work.BoseSym.Amb N).1) : Work.BoseSym.L2 N)]
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- (3) the kinetic part
  have hCnn : 0 ≤ C :=
    (Finset.sum_nonneg
      (fun j (_ : j ∈ Finset.univ) => sq_nonneg (‖((p 0 : Work.BoseSym.Amb N).2) j‖))).trans (hC 0)
  set Lam : ℝ :=
    Filter.liminf (fun n => Work.BoseSym.gSq ((p (φ n) : Work.BoseSym.Amb N))) Filter.atTop
    with hLamdef
  have hLamnn : 0 ≤ Lam := by
    rw [hLamdef]
    refine le_liminf_of_le (f := (Filter.atTop : Filter ℕ))
      (u := fun n : ℕ => Work.BoseSym.gSq ((p (φ n) : Work.BoseSym.Amb N))) (a := (0 : ℝ)) ?_ ?_
    · exact IsBoundedUnder.isCoboundedUnder_flip (r := (· ≤ ·))
        (isBoundedUnder_of_eventually_le (a := C) (Eventually.of_forall (fun n : ℕ => hC (φ n))))
    · exact Eventually.of_forall (fun n : ℕ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  let Y : Submodule ℝ (Xsp N) := (HsubX N L)ᗮ
  let T : Y →L[ℝ] Wg N := (projWclm N).comp (Submodule.subtypeL Y)
  let chi : Work.BoseSym.L2 N →ₗ[ℝ] ℝ :=
    { toFun := fun x => inner ℝ w x
      map_add' := fun x y => inner_add_right w x y
      map_smul' := fun c x => inner_smul_right w x c }
  let ell : Y →ₗ[ℝ] ℝ := -(chi.comp ((projFirst N).comp (Submodule.subtype Y)))
  have hell : ∀ y : Y, ell y = -inner ℝ w (projFirst N (y : Xsp N)) := fun y => rfl
  -- well-definedness of `ell` on the fibres of the gradient-coordinate projection
  have hker : T.ker ≤ ell.ker := by
    intro y hy
    have hyν : projW N (y : Xsp N) = 0 := hy
    have hδ : inner ℝ w (projFirst N (y : Xsp N)) = 0 := by
      have h1 : Tendsto (fun n => inner ℝ (((p (φ n) : Work.BoseSym.Amb N).1) : Work.BoseSym.L2 N)
          (projFirst N (y : Xsp N))) Filter.atTop
          (nhds (inner ℝ w (projFirst N (y : Xsp N)))) :=
        hwt.inner tendsto_const_nhds
      have h2 : ∀ n, inner ℝ (((p (φ n) : Work.BoseSym.Amb N).1) : Work.BoseSym.L2 N)
          (projFirst N (y : Xsp N)) = 0 := by
        intro n
        have h3 := (Submodule.mem_orthogonal (HsubX N L) (y : Xsp N)).mp y.2
          (toX N ((p (φ n)) : Work.BoseSym.Amb N)) (HsubX_of_mem (p (φ n)).2)
        rw [inner_toX] at h3
        rw [hyν, inner_zero_right, add_zero] at h3
        exact h3
      rw [funext h2] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    show ell y = 0
    rw [hell y, hδ, neg_zero]
  -- the quantitative bound
  have hbound : ∀ y : Y, |ell y| ≤ Real.sqrt Lam * ‖T y‖ := by
    intro y
    rcases eq_or_ne (projW N (y : Xsp N)) 0 with hν0 | hν0
    · have hyk : y ∈ T.ker := hν0
      have hz : ell y = 0 := hker hyk
      have hTy : T y = 0 := hν0
      rw [hz, hTy, norm_zero, mul_zero, abs_zero]
    · have hνpos : 0 < ‖projW N (y : Xsp N)‖ := norm_pos_iff.mpr hν0
      have hb : ∀ n, |inner ℝ (((p (φ n) : Work.BoseSym.Amb N).1) : Work.BoseSym.L2 N)
            (projFirst N (y : Xsp N))| / ‖projW N (y : Xsp N)‖
          ≤ Real.sqrt (Work.BoseSym.gSq ((p (φ n)) : Work.BoseSym.Amb N)) := by
        intro n
        have h3 := (Submodule.mem_orthogonal (HsubX N L) (y : Xsp N)).mp y.2
          (toX N ((p (φ n)) : Work.BoseSym.Amb N)) (HsubX_of_mem (p (φ n)).2)
        rw [inner_toX] at h3
        have h4 : inner ℝ (((p (φ n) : Work.BoseSym.Amb N).1) : Work.BoseSym.L2 N)
            (projFirst N (y : Xsp N))
            = - inner ℝ (WithLp.toLp 2 (((p (φ n)) : Work.BoseSym.Amb N).2))
                (projW N (y : Xsp N)) := by
          linarith [h3]
        rw [h4, abs_neg, div_le_iff₀ hνpos]
        calc |inner ℝ (WithLp.toLp 2 (((p (φ n)) : Work.BoseSym.Amb N).2))
              (projW N (y : Xsp N))|
            ≤ ‖(WithLp.toLp 2 (((p (φ n)) : Work.BoseSym.Amb N).2) : Wg N)‖
                * ‖projW N (y : Xsp N)‖ := abs_real_inner_le_norm _ _
          _ = Real.sqrt (Work.BoseSym.gSq ((p (φ n)) : Work.BoseSym.Amb N))
                * ‖projW N (y : Xsp N)‖ := by rw [norm_toLp_grad]
      have hlim : Tendsto (fun n => |inner ℝ (((p (φ n) : Work.BoseSym.Amb N).1) : Work.BoseSym.L2 N)
            (projFirst N (y : Xsp N))| / ‖projW N (y : Xsp N)‖) Filter.atTop
          (nhds (|inner ℝ w (projFirst N (y : Xsp N))| / ‖projW N (y : Xsp N)‖)) :=
        ((hwt.inner tendsto_const_nhds).abs).div_const _
      have hmain : |inner ℝ w (projFirst N (y : Xsp N))| / ‖projW N (y : Xsp N)‖
          ≤ Real.sqrt Lam := by
        refine (le_liminf_of_tendsto_of_le hlim hb (M := Real.sqrt C) ?_).trans ?_
        · intro n
          rw [Real.sqrt_le_sqrt_iff hCnn]
          exact hC (φ n)
        · rw [hLamdef]
          exact liminf_sqrt_le_sqrt_liminf
            (s := fun n => Work.BoseSym.gSq ((p (φ n)) : Work.BoseSym.Amb N))
            (fun n => Finset.sum_nonneg fun j _ => sq_nonneg _) (fun n => hC (φ n))
      rw [hell y, abs_neg]
      have hTy : ‖T y‖ = ‖projW N (y : Xsp N)‖ := rfl
      rw [hTy]
      exact (div_le_iff₀ hνpos).mp hmain
  obtain ⟨h, hhnorm, hhinner⟩ :=
    Work.BoseSym.Liminf.exists_inner_eq_of_ker_le_ker T ell hker (Real.sqrt_nonneg Lam) hbound
  -- (4) the pair `(w, h)` lies in `Hsub`
  have hQmem : (w, WithLp.ofLp h) ∈ Work.BoseSym.Hsub N L := by
    have horth : toX N (w, WithLp.ofLp h) ∈ (HsubX N L)ᗮᗮ := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      have hz : inner ℝ (toX N (w, WithLp.ofLp h)) y = 0 := by
        rw [inner_pair]
        have h1 := hhinner ⟨y, hy⟩
        have h2 : T ⟨y, hy⟩ = projW N y := rfl
        have h3 : ell ⟨y, hy⟩ = -inner ℝ w (projFirst N y) := hell ⟨y, hy⟩
        rw [h2, h3] at h1
        linarith [h1]
      rw [real_inner_comm]
      exact hz
    have hcl : (HsubX N L)ᗮᗮ = HsubX N L := by
      rw [Submodule.orthogonal_orthogonal_eq_closure,
        IsClosed.submodule_topologicalClosure_eq (HsubX_closed N L)]
    rw [hcl] at horth
    rw [HsubX, Submodule.mem_map] at horth
    obtain ⟨q, hq, hqx⟩ := horth
    have hqw : (w, WithLp.ofLp h) = q := (toX_injective N hqx).symm
    rw [hqw]
    exact hq
  -- (5) the potential part
  have hWle : ∀ {m k : ℕ}, m ≤ k → ∀ x, W m x ≤ W k x := by
    intro m k hmk
    induction hmk with
    | refl => intro x; exact le_rfl
    | step hmk ih => intro x; exact le_trans (ih x) (hWmono _ x)
  have hpot := Work.BoseSym.Liminf.potSq_liminf_box (N := N) (L := L) (C' := C')
    (W := fun n => W (φ n)) (Wlim := Wlim)
    (fun n => hW0 (φ n)) hWlim0 (fun n => hWm (φ n)) hWlimm
    (fun n x => hWle (hφ.monotone (Nat.le_succ n)) x)
    (fun x => (hWtend x).comp hφ.tendsto_atTop)
    (u := fun n => ((p (φ n)) : Work.BoseSym.Amb N).1) (v := w) hwt
    (fun n => hC'i (φ n)) (fun n => hC'b (φ n))
  -- (6) assembly
  refine ⟨φ, hφ, ⟨(w, WithLp.ofLp h), hQmem⟩, ?_, ?_, hpot.1, ?_⟩
  · show ‖w‖ ^ 2 = 1
    rw [hwnorm]; norm_num
  · -- the extra conjunct: the subsequence is the one produced by Rellich, and the
    -- limit `q` has function part `w`, so this is exactly the recorded `L²` convergence
    exact hwt
  · have hgsq : Work.BoseSym.gSq (w, WithLp.ofLp h) ≤ Lam := by
      have h1 : Work.BoseSym.gSq (w, WithLp.ofLp h) = ‖h‖ ^ 2 := by
        simp only [Work.BoseSym.gSq]
        rw [PiLp.norm_sq_eq_of_L2]
      rw [h1]
      nlinarith [norm_nonneg h, Real.sq_sqrt hLamnn, hLamnn]
    have hsum : Lam + (Filter.liminf (fun n => ∫ x in BoseGases.box N L,
        W (φ n) x * (((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
        Filter.atTop)
        ≤ Filter.liminf (fun n => Work.BoseSym.gSq ((p (φ n) : Work.BoseSym.Amb N))
            + ∫ x in BoseGases.box N L,
                W (φ n) x * (((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
            Filter.atTop := by
      rw [hLamdef]
      exact le_liminf_add
        (isBoundedUnder_of_eventually_ge (a := (0 : ℝ))
          (Eventually.of_forall (fun n : ℕ => Finset.sum_nonneg fun j _ => sq_nonneg _)))
        (isBoundedUnder_of_eventually_le (a := C) (Eventually.of_forall (fun n : ℕ => hC (φ n))))
        (isBoundedUnder_of_eventually_ge (a := (0 : ℝ)) (Eventually.of_forall (fun n : ℕ =>
          integral_nonneg fun x => mul_nonneg (hW0 (φ n) x) (sq_nonneg _))))
        (IsBoundedUnder.isCoboundedUnder_flip (r := (· ≤ ·))
          (isBoundedUnder_of_eventually_le (a := C') (Eventually.of_forall (fun n => hC'b (φ n)))))
    exact (add_le_add hgsq hpot.2).trans hsum


end

end Work.BoseSym.Assemble
