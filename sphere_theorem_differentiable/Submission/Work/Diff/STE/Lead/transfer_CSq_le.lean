import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.BNorm_J_le_uniform
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.B3.CSq_period_comp_arg_le_of_isOpen
import Submission.Work.Diff.STE.B3.tMapFun_injOn_det
import Submission.Work.Diff.STE.B3.BNorm_J_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart transfer for the reconstruction: `CSq` of `R_i (R*_j f)` is bounded by the `CSq`
of the components of `f`

`Work.Diff.STE.B3.BNorm_J_le` proves the chart-transfer estimate uniformly over the whole
composite norm; the present file isolates the *single component* statement used in the Layer-D
consumers: the `k`-th `CSq` norm of the chart-`i` component of the reconstruction `R*_j f` of a
coefficient family `f` is bounded by a constant (independent of `f`) times the sum of the `k`-th
`CSq` norms of the components of `f`.

The proof is the `(interior of the) proof of `Work.Diff.STE.B3.BNorm_J_le` with the sum over the
charts removed:

* `Work.Diff.STE.B3.bump_expansion` writes the chart-`i` component of `R*_j ·` as a double sum
  `Σ_{cd} G c d z * u c d (T z)` with `G c d` smooth, supported in the open cube, and `T` smooth,
  injective with invertible Jacobian on an open set containing all the supports;
* `Work.Diff.STE.B3.CSq_period_comp_arg_le_of_isOpen` (the chart transfer) bounds the `CSq` of each
  periodised summand `G c d · (u c d ∘ T)` by the `CSq` of `u c d`, up to an additive constant,
  and `Work.Diff.STE.B3.homog_transfer` removes the additive constant by rescaling;
* the periodised summands are combined with `Work.Diff.STE.B3.CSq_sum_le` and the `Hᵏ`-algebra of
  finite sums.
-/

set_option maxHeartbeats 2000000

namespace Work.Diff.STE.Lead

set_option maxHeartbeats 2000000 in
theorem transfer_CSq_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i j : ι₀) (a b : Fin (Module.finrank ℝ E)) (k : ℕ)
    (hk : Module.finrank ℝ E < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
        (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
      (hsm : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (f c d))
      (hper : ∀ c d, Work.Diff.STE.Periodic1 (f c d)),
      Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j f) a b))
        ≤ C * ∑ c, ∑ d, Work.Diff.STE.CSq k
            (Work.Diff.STE.fourierCoeff (fun z =>
              ((f c d z : ℝ) : ℂ))) := by
  classical
  -- Step 1: the junk-free expansion of the chart-`i` component of `R*_j ·`
  obtain ⟨T, G, U, hUopen, hTsm, hTinj, hTdet, hGsm, hGsupp, hGcomp, hGsub, hid⟩ :=
    Work.Diff.STE.B3.bump_expansion D j i a b
      (Work.Diff.STE.B3.closure_Omega_goodSet D j i)
      (Work.Diff.STE.B3.goodSet_smooth_noT2 D j i).1
      (Work.Diff.STE.B3.goodSet_smooth_noT2 D j i).2.1
      (fun c d => (Work.Diff.STE.B3.goodSet_smooth_noT2 D j i).2.2 a b c d)
      (Work.Diff.STE.B3.tMapFun_injOn_det D j i).1
      (Work.Diff.STE.B3.tMapFun_injOn_det D j i).2
  -- Step 2: the chart transfer for each summand
  choose Ct hCt using fun (c d : Fin (Module.finrank ℝ E)) =>
    Work.Diff.STE.B3.CSq_period_comp_arg_le_of_isOpen (ι := Fin (Module.finrank ℝ E)) k
      (by simpa using hk) T (G c d) (hGsm c d) (hGsupp c d) (hGcomp c d) U hUopen (hGsub c d)
      (fun z _ => hTsm.contDiffAt) hTinj hTdet
  refine ⟨(Fintype.card (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ) *
    (∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), 2 * Ct t.1 t.2), ?_, ?_⟩
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ => by
      have := (hCt t.1 t.2).1; linarith)
  · intro f hsm hper
    have hu : ∀ c d : Fin (Module.finrank ℝ E),
        ContDiff ℝ (⊤ : ℕ∞) (fun z => ((f c d z : ℝ) : ℂ)) :=
      fun c d => (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp (hsm c d)
    have hup : ∀ c d : Fin (Module.finrank ℝ E),
        Work.Diff.STE.Periodic1 (fun z => ((f c d z : ℝ) : ℂ)) :=
      fun c d i x => congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) (hper c d i x)
    have hhom : ∀ (c d : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (fun z =>
          ∑' m : Fin (Module.finrank ℝ E) → ℤ,
            G c d (z + Work.Diff.STE.iVec m) *
              ((f c d (T (z + Work.Diff.STE.iVec m)) : ℝ) : ℂ)))
          ≤ 2 * Ct c d * Work.Diff.STE.CSq k
              (Work.Diff.STE.fourierCoeff (fun z => ((f c d z : ℝ) : ℂ))) :=
      fun c d => Work.Diff.STE.B3.homog_transfer k (Ct c d) (hCt c d).1 T (G c d) (hCt c d).2
        (fun z => ((f c d z : ℝ) : ℂ)) (hu c d) (hup c d)
    -- the periodised summands
    set per : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) →
        (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun t z =>
      ∑' m : Fin (Module.finrank ℝ E) → ℤ,
        G t.1 t.2 (z + Work.Diff.STE.iVec m) *
          ((f t.1 t.2 (T (z + Work.Diff.STE.iVec m)) : ℝ) : ℂ) with hper_def
    have hper_t : ∀ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        ContDiff ℝ (⊤ : ℕ∞) (per t) ∧ Work.Diff.STE.Periodic1 (per t) := by
      intro t
      rw [hper_def]
      obtain ⟨h1, h2, -⟩ := Work.Diff.STE.periodization_contDiff_periodic
        (fun w => G t.1 t.2 w * ((f t.1 t.2 (T w) : ℝ) : ℂ))
        ((hGsm t.1 t.2).mul ((hu t.1 t.2).comp hTsm))
        (fun w hw => hGsupp t.1 t.2 (fun h0 => hw (by
          show G t.1 t.2 w * ((f t.1 t.2 (T w) : ℝ) : ℂ) = 0
          rw [h0, zero_mul])))
      exact ⟨h1, h2⟩
    -- the pointwise expansion of the periodisation
    have hpoint : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
        D.Rper i (D.Rstar j f) a b z
          = ∑ c, ∑ d, per (c, d) z := by
      intro z
      set N : Fin (Module.finrank ℝ E) → ℤ := fun i => ⌊|z i|⌋ + 2 with hNdef
      set S : Finset (Fin (Module.finrank ℝ E) → ℤ) :=
        Fintype.piFinset (fun i => Finset.Icc (-(N i)) (N i)) with hSdef
      have hsupp' : ∀ (c d : Fin (Module.finrank ℝ E)),
          Function.support (fun w : Fin (Module.finrank ℝ E) → ℝ =>
            G c d w * ((f c d (T w) : ℝ) : ℂ)) ⊆
            Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
              Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
        intro c d w hw
        exact hGsupp c d (fun h0 => hw (by
          show G c d w * ((f c d (T w) : ℝ) : ℂ) = 0
          rw [h0, zero_mul]))
      have hzero : ∀ (c d : Fin (Module.finrank ℝ E))
          (m : Fin (Module.finrank ℝ E) → ℤ), m ∉ S →
          G c d (z + Work.Diff.STE.iVec m) *
            ((f c d (T (z + Work.Diff.STE.iVec m)) : ℝ) : ℂ) = 0 := by
        intro c d m hm
        by_contra hne
        have hmem : ∀ j : Fin (Module.finrank ℝ E), m j ∈ Finset.Icc (-(N j)) (N j) := by
          intro j
          have hlt : |m j| < N j := by
            have := Work.Diff.STE.abs_lt_floor_add_two_of_support (hsupp' c d)
              (x := z) (y := z) (fun j => by rw [sub_self, abs_zero]; norm_num) hne j
            simpa [hNdef] using this
          rw [Finset.mem_Icc]
          have h2 := abs_lt.mp hlt
          exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
        exact hm (by rw [hSdef, Fintype.mem_piFinset]; exact hmem)
      rw [show D.Rper i (D.Rstar j f) a b z =
          ∑' m : Fin (Module.finrank ℝ E) → ℤ,
            ((D.R i (D.Rstar j f) a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) from rfl]
      rw [tsum_congr (fun m => hid f (z + Work.Diff.STE.iVec m))]
      rw [Work.Diff.STE.B3.tsum_finset_sum_eq
        (f := fun (c : Fin (Module.finrank ℝ E)) (m : Fin (Module.finrank ℝ E) → ℤ) =>
          ∑ d, G c d (z + Work.Diff.STE.iVec m) *
            ((f c d (T (z + Work.Diff.STE.iVec m)) : ℝ) : ℂ))
        (fun c m hm => Finset.sum_eq_zero fun d _ => hzero c d m hm)]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Work.Diff.STE.B3.tsum_finset_sum_eq
        (f := fun (d : Fin (Module.finrank ℝ E)) (m : Fin (Module.finrank ℝ E) → ℤ) =>
          G c d (z + Work.Diff.STE.iVec m) *
            ((f c d (T (z + Work.Diff.STE.iVec m)) : ℝ) : ℂ))
        (fun d m hm => hzero c d m hm)]
    -- the `fourierCoeff` of the periodisation, as a finite sum
    have hfun : D.Rper i (D.Rstar j f) a b
        = fun z => ∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), per t z := by
      funext z
      rw [hpoint z]
      exact (Fintype.sum_prod_type (f := fun t : Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E) => per t z)).symm
    have hcoeff : Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j f) a b)
        = fun m => ∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.fourierCoeff (per t) m := by
      rw [hfun]
      funext m
      exact Work.Diff.STE.B3.fourierCoeff_finset_sum_of_continuous (fun t => per t)
        (fun t => (hper_t t).1.continuous) m
    have hsummable : ∀ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        Summable fun m : Fin (Module.finrank ℝ E) → ℤ =>
          Work.Diff.STE.wt m ^ k * ‖Work.Diff.STE.fourierCoeff (per t) m‖ ^ 2 :=
      fun t => Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff (per t)
        (hper_t t).1 (hper_t t).2 k
    -- the three steps of the estimate
    have hstep1 : Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j f) a b))
        ≤ (Fintype.card (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ) *
          ∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (per t)) := by
      rw [hcoeff]
      exact Work.Diff.STE.B3.CSq_sum_le k (fun t => Work.Diff.STE.fourierCoeff (per t)) hsummable
    have hstep2 : (∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (per t)))
        ≤ ∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            (2 * Ct t.1 t.2) *
              Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff
                (fun z => ((f t.1 t.2 z : ℝ) : ℂ))) := by
      refine Finset.sum_le_sum fun t _ => ?_
      rw [hper_def]
      exact hhom t.1 t.2
    have hstep3 : (∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            (2 * Ct t.1 t.2) *
              Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff
                (fun z => ((f t.1 t.2 z : ℝ) : ℂ))))
        ≤ (∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), 2 * Ct t.1 t.2) *
          (∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff
              (fun z => ((f t.1 t.2 z : ℝ) : ℂ)))) := by
      have hA : ∀ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          0 ≤ 2 * Ct t.1 t.2 := fun t => by have := (hCt t.1 t.2).1; linarith
      have hB : ∀ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          0 ≤ Work.Diff.STE.CSq k
            (Work.Diff.STE.fourierCoeff (fun z => ((f t.1 t.2 z : ℝ) : ℂ))) :=
        fun t => Work.Diff.STE.CSq_nonneg k _
      have hBt : ∀ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (fun z => ((f t.1 t.2 z : ℝ) : ℂ)))
            ≤ ∑ s : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                Work.Diff.STE.CSq k
                  (Work.Diff.STE.fourierCoeff (fun z => ((f s.1 s.2 z : ℝ) : ℂ))) :=
        fun t => Finset.single_le_sum (fun s _ => hB s) (Finset.mem_univ t)
      calc (∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              (2 * Ct t.1 t.2) *
                Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff
                  (fun z => ((f t.1 t.2 z : ℝ) : ℂ))))
          ≤ ∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              (2 * Ct t.1 t.2) *
                (∑ s : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                  Work.Diff.STE.CSq k
                    (Work.Diff.STE.fourierCoeff (fun z => ((f s.1 s.2 z : ℝ) : ℂ)))) :=
            Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hBt t) (hA t)
        _ = (∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), 2 * Ct t.1 t.2) *
              (∑ s : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                Work.Diff.STE.CSq k
                  (Work.Diff.STE.fourierCoeff (fun z => ((f s.1 s.2 z : ℝ) : ℂ)))) := by
            rw [Finset.sum_mul]
    -- reindex the target's double sum over `(c,d)` as a sum over `Fin n × Fin n`
    have hreindex : (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          Work.Diff.STE.CSq k
            (Work.Diff.STE.fourierCoeff (fun z => ((f c d z : ℝ) : ℂ))))
        = ∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq k
              (Work.Diff.STE.fourierCoeff (fun z => ((f t.1 t.2 z : ℝ) : ℂ))) :=
      (Fintype.sum_prod_type (f := fun t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
        Work.Diff.STE.CSq k
          (Work.Diff.STE.fourierCoeff (fun z => ((f t.1 t.2 z : ℝ) : ℂ))))).symm
    rw [hreindex]
    calc Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i (D.Rstar j f) a b))
        ≤ (Fintype.card (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ) *
          ∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (per t)) := hstep1
      _ ≤ (Fintype.card (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ) *
          ∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            (2 * Ct t.1 t.2) *
              Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff
                (fun z => ((f t.1 t.2 z : ℝ) : ℂ))) :=
          mul_le_mul_of_nonneg_left hstep2 (by positivity)
      _ ≤ (Fintype.card (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ) *
          ((∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), 2 * Ct t.1 t.2) *
            (∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff
                (fun z => ((f t.1 t.2 z : ℝ) : ℂ))))) :=
          mul_le_mul_of_nonneg_left hstep3 (by positivity)
      _ = ((Fintype.card (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ) *
            (∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), 2 * Ct t.1 t.2)) *
          (∑ t : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff
              (fun z => ((f t.1 t.2 z : ℝ) : ℂ)))) := by ring

end Work.Diff.STE.Lead
