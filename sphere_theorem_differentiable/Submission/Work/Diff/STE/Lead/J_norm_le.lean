import Mathlib
import Submission.Diff.STEGal
import Submission.Work.Diff.STE.B3.BNorm_J_le_uniform
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.CSq_period_comp_arg_le_nodim_of_isOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: last layer of short_time_existence (owner H10, Diff/STE). The lead dispatched these pieces top-level so they run in parallel.
Vocabulary: Submission/Work/Diff/STE/B3/Comp.lean (R, Rper, CPair, BPair, BNorm, Rstar, STruncR, J), B3/Data.lean (B3Data: x₀, χ, ζ, e, dens,
psi), D/* (Galerkin, genMap, jSym, addSec, deTurckSec, ChartData, smetOf), and the lead's Submission/Diff/STEGal.lean (galState, IsGalSol,
GalUniform). REUSE the PROVED Layer A toolkit (Submission/Work/Diff/STE/*.lean; LayerA.lean lists it): CSq_trunc_le,
CSq_trunc_sub_le, friedrichs_commutator, CSq_period_comp_arg_le, CSq_conv_tame_le, CSq_comp_le, garding_vec_uniform,
gronwall_linear_bound, norm_seriesFun_le (Sobolev), CSq_tail_le (compactness), eq_zero_of_fourierCoeff_eq_zero, BPair_J_self,
BPair_Rstar, J_finite_rank, R_Rstar_expansion2 (chart transfer). Read DESIGN.md (sessions 6–8) first. Do not re-prove anything listed.
If a statement here is false as stated (e.g. a missing hypothesis on ρ or on B3Data), declare_false with the precise reason; the lead fixes it.
ROUTE (J_norm_le). J h = Σ_i R_i*(S_ε R_i h). BNorm k (J h) = Σ_j Σ_ab CSq k (coeffs of Rper_j (J h) a b).
R_j(R_i* f) is a chart transfer: multiplication by smooth compactly supported weights plus a smooth change of coordinates on the
overlap. It is bounded on H^k with a constant independent of ε (CSq_period_comp_arg_le, R_Rstar_expansion2).
S_ε is a contraction on every CSq level (CSq_trunc_le, |ρ| ≤ 1). Sum over the finitely many (i,j).
-/

/-
**Remarks of the prover of `Work.Diff.STE.Lead.J_norm_le`.**

The library result `Work.Diff.STE.B3.BNorm_J_le_uniform` already proves the requested bound, but
under the extra hypothesis `Module.finrank ℝ E < 2 * k`, which enters only through the chart
transfer `Work.Diff.STE.B3.CSq_period_comp_arg_le_of_isOpen` (its proof bounds the test function in
sup norm via the Sobolev embedding `Work.Diff.STE.norm_seriesFun_le`).  That dimension hypothesis is
removed by the sibling `Work.Diff.STE.B3.CSq_period_comp_arg_le_nodim_of_isOpen`, and the regularity
hypothesis `∀ i a b, ContDiff ℝ ⊤ (D.R i h a b)` of the library result is replaced by the section
regularity `Work.Diff.STE.D.ChartData` required by the statement, through the sibling
`Work.Diff.STE.B3.R_contDiff_of_chartData`.

`BNorm_J_le_of_transfer` below is the library argument with the transfer estimate carried as an
explicit hypothesis; it is the only place where `k` versus `Module.finrank ℝ E` used to matter.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory BigOperators
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.Lead

set_option linter.unusedSectionVars false

/-- **The Friedrichs mollifier is bounded in `BNorm k`, with the chart transfer as a hypothesis.**

`htr` is the dimension-free chart-transfer estimate (the level `k` being fixed): for a smooth
`1`-periodic `u` and a smooth `f` supported in the open cube,
`CSq k (fourierCoeff (periodisation of z ↦ f z * u (T z))) ≤ C (1 + CSq k (fourierCoeff u))`.

The proof is the proof of `Work.Diff.STE.B3.BNorm_J_le_uniform` with the single call to
`CSq_period_comp_arg_le_of_isOpen` replaced by `htr` and the hypothesis
`Module.finrank ℝ E < 2 * k` deleted. -/
theorem BNorm_J_le_of_transfer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (k : ℕ)
    (htr : ∀ (T : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ))
      (f : (Fin (Module.finrank ℝ E) → ℝ) → ℂ), ContDiff ℝ (⊤ : ℕ∞) f →
      Function.support f ⊆ Set.pi Set.univ
        (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
      IsCompact (tsupport f) → ∀ U : Set (Fin (Module.finrank ℝ E) → ℝ), IsOpen U →
      tsupport f ⊆ U →
      (∀ z ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) T z) → Set.InjOn T U →
      (∀ z ∈ U, (fderiv ℝ T z).det ≠ 0) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
        Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (fun z =>
          ∑' m : Fin (Module.finrank ℝ E) → ℤ,
            f (z + Work.Diff.STE.iVec m) * u (T (z + Work.Diff.STE.iVec m))))
          ≤ C * (1 + Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff u)))
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
          (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
            ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b)) →
          D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h := by
  classical
  -- the per-`(j,a,b)` bound, uniform in the section
  have hmain : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        (∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          ContDiff ℝ (⊤ : ℕ∞) (D.R i h c d)) →
        CSq k (fourierCoeff (D.Rper j (D.J ρ ε h) a b)) ≤ Cf * D.BNorm k h := by
    intro j a b
    -- the junk-free expansion of the cross-chart terms
    choose T G U hUopen hTsm hTinj hTdet hGsm hGsupp hGcomp hGsub hid using fun (i : ι₀) =>
      Work.Diff.STE.B3.bump_expansion D i j a b
        (Work.Diff.STE.B3.closure_Omega_goodSet D i j)
        (Work.Diff.STE.B3.goodSet_smooth_noT2 D i j).1
        (Work.Diff.STE.B3.goodSet_smooth_noT2 D i j).2.1
        (fun c d => (Work.Diff.STE.B3.goodSet_smooth_noT2 D i j).2.2 a b c d)
        (Work.Diff.STE.B3.tMapFun_injOn_det D i j).1
        (Work.Diff.STE.B3.tMapFun_injOn_det D i j).2
    -- the transfer constants (here: the transfer estimate is a hypothesis)
    choose Ct hCt using fun (i : ι₀) (c d : Fin (Module.finrank ℝ E)) =>
      htr (T i) (G i c d) (hGsm i c d) (hGsupp i c d) (hGcomp i c d) (U i) (hUopen i)
        (hGsub i c d) (fun z _ => (hTsm i).contDiffAt) (hTinj i) (hTdet i)
    have hhom : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E))
        (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
        CSq k (fourierCoeff (fun z => ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
          G i c d (z + Work.Diff.STE.iVec m) * u (T i (z + Work.Diff.STE.iVec m))))
          ≤ 2 * Ct i c d * CSq k (fourierCoeff u) :=
      fun i c d => Work.Diff.STE.B3.homog_transfer k (Ct i c d) (hCt i c d).1 (T i) (G i c d)
        (hCt i c d).2
    refine ⟨(Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ) *
      (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        2 * Ct i c d), ?_, ?_⟩
    · have h0 : (0 : ℝ) ≤ ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
          ∑ d : Fin (Module.finrank ℝ E), 2 * Ct i c d :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ =>
          Finset.sum_nonneg fun d _ => by have := (hCt i c d).1; linarith
      have h1 : (0 : ℝ) ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E)) : ℝ) := by positivity
      exact mul_nonneg h1 h0
    · intro ε _hε _hε1 h hsm
      -- the chart components of `J ρ ε h`
      have hRsupp : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          Function.support (D.R i h c d) ⊆
            Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
              Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
        intro i c d z hz
        exact D.psi_supp i (fun h0 => hz (by
          simp only [Work.Diff.STE.B3Data.R, h0, zero_mul, mul_zero]))
      have hcomp : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.STruncC ρ ε (D.R i h c d)) ∧
            Work.Diff.STE.Periodic1 (Work.Diff.STE.STruncC ρ ε (D.R i h c d)) :=
        fun i c d => Work.Diff.STE.B3.STruncC_contDiff_periodic ρ hρ ε (D.R i h c d)
          (hsm i c d) (hRsupp i c d)
      -- `D.J ρ ε h` in terms of `STruncC`
      have hJeq : D.J ρ ε h = ∑ i : ι₀, D.Rstar i (fun c d w =>
          (Work.Diff.STE.STruncC ρ ε (D.R i h c d) w).re) := by
        rw [Work.Diff.STE.B3Data.J]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
      -- linearity of `R j` in its section argument
      have hRlin : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
          D.R j (D.J ρ ε h) a b w = ∑ i : ι₀,
            D.R j (D.Rstar i (fun c d y =>
              (Work.Diff.STE.STruncC ρ ε (D.R i h c d) y).re)) a b w := by
        intro w
        rw [hJeq]
        simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Finset.sum_apply, sum_apply,
          Finset.mul_sum]
      -- the pointwise expansion of the cross-chart terms
      have hlin : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
          ((D.R j (D.J ρ ε h) a b w : ℝ) : ℂ) = ∑ i : ι₀,
            ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              G i c d w * Work.Diff.STE.STruncC ρ ε (D.R i h c d) (T i w) := by
        intro w
        rw [hRlin w]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hid i (fun c d y => (Work.Diff.STE.STruncC ρ ε (D.R i h c d) y).re) w]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        have hre : (((Work.Diff.STE.STruncC ρ ε (D.R i h c d) (T i w)).re : ℝ) : ℂ)
            = Work.Diff.STE.STruncC ρ ε (D.R i h c d) (T i w) := by
          rw [Work.Diff.STE.STruncC]
          simp [Complex.ofReal_re]
        rw [hre]
      -- the decomposition of the `j`-th component of `J ρ ε h`
      have hpoint : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
          D.Rper j (D.J ρ ε h) a b z =
            ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
                G i c d (z + Work.Diff.STE.iVec m) *
                  Work.Diff.STE.STruncC ρ ε (D.R i h c d)
                    (T i (z + Work.Diff.STE.iVec m)) := by
        intro z
        set N : Fin (Module.finrank ℝ E) → ℤ := fun i => ⌊|z i|⌋ + 2 with hNdef
        set S : Finset (Fin (Module.finrank ℝ E) → ℤ) :=
          Fintype.piFinset (fun i => Finset.Icc (-(N i)) (N i)) with hSdef
        have hsupp' : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
            Function.support (fun w : Fin (Module.finrank ℝ E) → ℝ =>
              G i c d w * Work.Diff.STE.STruncC ρ ε (D.R i h c d) (T i w)) ⊆
              Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
                Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
          intro i c d w hw
          exact hGsupp i c d (fun h0 => hw (by
            show G i c d w * Work.Diff.STE.STruncC ρ ε (D.R i h c d) (T i w) = 0
            rw [h0, zero_mul]))
        have hzero : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E))
            (m : Fin (Module.finrank ℝ E) → ℤ), m ∉ S →
            G i c d (z + Work.Diff.STE.iVec m) *
              Work.Diff.STE.STruncC ρ ε (D.R i h c d)
                (T i (z + Work.Diff.STE.iVec m)) = 0 := by
          intro i c d m hm
          by_contra hne
          have hmem : ∀ j : Fin (Module.finrank ℝ E),
              m j ∈ Finset.Icc (-(N j)) (N j) := by
            intro j
            have hlt : |m j| < N j := by
              have := Work.Diff.STE.abs_lt_floor_add_two_of_support (hsupp' i c d)
                (x := z) (y := z) (fun j => by rw [sub_self, abs_zero]; norm_num) hne j
              simpa [hNdef] using this
            rw [Finset.mem_Icc]
            have h2 := abs_lt.mp hlt
            exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
          exact hm (by rw [hSdef, Fintype.mem_piFinset]; exact hmem)
        rw [show D.Rper j (D.J ρ ε h) a b z = ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
            ((D.R j (D.J ρ ε h) a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) from rfl]
        rw [tsum_congr (fun m => hlin (z + Work.Diff.STE.iVec m))]
        rw [Work.Diff.STE.B3.tsum_finset_sum_eq (f := fun (i : ι₀) (m : Fin (Module.finrank ℝ E) → ℤ) =>
              ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                G i c d (z + Work.Diff.STE.iVec m) *
                  Work.Diff.STE.STruncC ρ ε (D.R i h c d)
                    (T i (z + Work.Diff.STE.iVec m)))
            (fun i m hm => Finset.sum_eq_zero fun c _ =>
              Finset.sum_eq_zero fun d _ => hzero i c d m hm)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Work.Diff.STE.B3.tsum_finset_sum_eq (f := fun (c : Fin (Module.finrank ℝ E))
              (m : Fin (Module.finrank ℝ E) → ℤ) =>
              ∑ d : Fin (Module.finrank ℝ E),
                G i c d (z + Work.Diff.STE.iVec m) *
                  Work.Diff.STE.STruncC ρ ε (D.R i h c d)
                    (T i (z + Work.Diff.STE.iVec m)))
            (fun c m hm => Finset.sum_eq_zero fun d _ => hzero i c d m hm)]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Work.Diff.STE.B3.tsum_finset_sum_eq (f := fun (d : Fin (Module.finrank ℝ E))
              (m : Fin (Module.finrank ℝ E) → ℤ) =>
              G i c d (z + Work.Diff.STE.iVec m) *
                Work.Diff.STE.STruncC ρ ε (D.R i h c d)
                  (T i (z + Work.Diff.STE.iVec m)))
            (fun d m hm => hzero i c d m hm)]
      -- abbreviations for the terms of the finite sum
      set per : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) →
          (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun t =>
        fun z => ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
          G t.1 t.2.1 t.2.2 (z + Work.Diff.STE.iVec m) *
            Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2)
              (T t.1 (z + Work.Diff.STE.iVec m)) with hper_def
      set Ab : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ :=
        fun t => 2 * Ct t.1 t.2.1 t.2.2 with hAb_def
      set Bb : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) → ℝ :=
        fun t => CSq k (fourierCoeff (Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2)))
        with hBb_def
      have hper_t : ∀ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ContDiff ℝ (⊤ : ℕ∞) (per t) ∧ Work.Diff.STE.Periodic1 (per t) := by
        intro t
        rw [hper_def]
        obtain ⟨h1, h2, -⟩ := Work.Diff.STE.periodization_contDiff_periodic
          (fun w => G t.1 t.2.1 t.2.2 w *
            Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2) (T t.1 w))
          ((hGsm t.1 t.2.1 t.2.2).mul ((hcomp t.1 t.2.1 t.2.2).1.comp (hTsm t.1)))
          (fun w hw => hGsupp t.1 t.2.1 t.2.2 (fun h0 => hw (by
            show G t.1 t.2.1 t.2.2 w * Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2)
              (T t.1 w) = 0
            rw [h0, zero_mul])))
        exact ⟨h1, h2⟩
      -- the coefficient family of `Rper j (J ρ ε h) a b`
      have hperVal : ∀ (t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ),
          per t z = ∑' m : (Fin (Module.finrank ℝ E) → ℤ),
            G t.1 t.2.1 t.2.2 (z + Work.Diff.STE.iVec m) *
              Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2)
                (T t.1 (z + Work.Diff.STE.iVec m)) := by
        intro t z
        rw [hper_def]
      have hfun : D.Rper j (D.J ρ ε h) a b = fun z => ∑ t, per t z := by
        funext z
        rw [hpoint]
        refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ =>
          Finset.sum_congr rfl fun d _ => (hperVal (i, c, d) z).symm).trans ?_
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_prod_type]
      have hcoeff : fourierCoeff (D.Rper j (D.J ρ ε h) a b)
          = fun m => ∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              fourierCoeff (per t) m := by
        rw [hfun]
        funext m
        rw [Work.Diff.STE.B3.fourierCoeff_finset_sum_of_continuous _ (fun t => (hper_t t).1.continuous) m]
      -- reindexing the finite sums over the product index type
      have hBeq : (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            CSq k (fourierCoeff (Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2))))
          = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              CSq k (fourierCoeff (Work.Diff.STE.STruncC ρ ε (D.R i h c d))) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fintype.sum_prod_type]
      have hBeq' : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              CSq k (fourierCoeff (Work.Diff.STE.STruncC ρ ε (D.R i h c d))))
          ≤ ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              CSq k (fourierCoeff (D.Rper i h c d)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ =>
          Work.Diff.STE.B3.STruncR_CSq_le ρ hρ ε k (D.R i h c d) (hsm i c d) (hRsupp i c d)
      have hBN : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E), CSq k (fourierCoeff (D.Rper i h c d)))
          = D.BNorm k h := rfl
      -- the bound on the sum of the `Bb`
      have hB : (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Bb t)
          ≤ D.BNorm k h := by
        calc (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Bb t)
            = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                CSq k (fourierCoeff (Work.Diff.STE.STruncC ρ ε (D.R i h c d))) := by
              rw [hBb_def]
              exact hBeq
          _ ≤ ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                CSq k (fourierCoeff (D.Rper i h c d)) := hBeq'
          _ = D.BNorm k h := hBN
      -- the chain
      have hh : ∀ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          CSq k (fourierCoeff (per t)) ≤ Ab t * Bb t := by
        intro t
        have := hhom t.1 t.2.1 t.2.2 (Work.Diff.STE.STruncC ρ ε (D.R t.1 h t.2.1 t.2.2))
          (hcomp t.1 t.2.1 t.2.2).1 (hcomp t.1 t.2.1 t.2.2).2
        rw [hper_def, hAb_def, hBb_def]
        exact this
      have hsummand : ∀ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          Ab t * Bb t ≤ Ab t * D.BNorm k h := by
        intro t
        have hAb : 0 ≤ Ab t := by
          rw [hAb_def]
          have := (hCt t.1 t.2.1 t.2.2).1
          linarith
        have hBb : Bb t ≤ D.BNorm k h := by
          have h1 : Bb t ≤ ∑ s, Bb s :=
            Finset.single_le_sum (f := fun s => Bb s)
              (fun s _ => by rw [hBb_def]; exact CSq_nonneg k _) (Finset.mem_univ t)
          exact h1.trans hB
        exact mul_le_mul_of_nonneg_left hBb hAb
      have hfin : CSq k (fourierCoeff (D.Rper j (D.J ρ ε h) a b))
          ≤ ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E)) : ℝ) *
              (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ab t))
            * D.BNorm k h := by
        calc CSq k (fourierCoeff (D.Rper j (D.J ρ ε h) a b))
            = CSq k (fun m => ∑ t, fourierCoeff (per t) m) := by rw [hcoeff]
          _ ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
                Fin (Module.finrank ℝ E)) : ℝ) *
              ∑ t, CSq k (fourierCoeff (per t)) :=
              Work.Diff.STE.B3.CSq_sum_le k _ (fun t => ?_)
          _ ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
                Fin (Module.finrank ℝ E)) : ℝ) * ∑ t, Ab t * Bb t :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => hh t) (by positivity)
          _ ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
                Fin (Module.finrank ℝ E)) : ℝ) * ((∑ t, Ab t) * D.BNorm k h) :=
              mul_le_mul_of_nonneg_left ?_ (by positivity)
          _ = ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
                Fin (Module.finrank ℝ E)) : ℝ) * (∑ t, Ab t)) * D.BNorm k h := by ring
        · exact summable_weighted_fourierCoeff_of_contDiff _ (hper_t t).1 (hper_t t).2 k
        · rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun t _ => hsummand t
      -- translate the constant back
      refine hfin.trans ?_
      have hSbeq : (∑ t : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ab t)
          = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E), 2 * Ct i c d := by
        rw [hAb_def]
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fintype.sum_prod_type]
      have heq : ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E)) : ℝ) * (∑ t, Ab t)) * D.BNorm k h
          = ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) ×
              Fin (Module.finrank ℝ E)) : ℝ) *
              (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
                ∑ d : Fin (Module.finrank ℝ E), 2 * Ct i c d)) * D.BNorm k h := by
        rw [hSbeq]
      exact le_of_eq heq
  -- assemble over `(j,a,b)`
  choose Cf hCf using fun (j : ι₀) (a b : Fin (Module.finrank ℝ E)) => hmain j a b
  refine ⟨∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
      Cf j a b, ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => (hCf j a b).1
  · intro ε _hε _hε1 h hsm
    rw [show D.BNorm k (D.J ρ ε h) = ∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          CSq k (fourierCoeff (D.Rper j (D.J ρ ε h) a b)) from rfl]
    rw [show (∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Cf j a b) * D.BNorm k h
        = ∑ j : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            Cf j a b * D.BNorm k h from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_mul]]
    refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun a _ =>
      Finset.sum_le_sum fun b _ => ?_
    exact (hCf j a b).2 ε _hε _hε1 h hsm

theorem J_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h := by
  -- the transfer estimate without the dimension restriction `finrank ℝ E < 2 k`
  obtain ⟨C, hCnn, hC⟩ := BNorm_J_le_of_transfer (I := I) (M := M) k
    (fun T f hf hfsupp hK U hU hUf hT hinj hdet =>
      Work.Diff.STE.B3.CSq_period_comp_arg_le_nodim_of_isOpen k T f hf hfsupp hK U hU hUf hT hinj
        hdet)
    D ρ hρ
  -- `ChartData` gives the smoothness of the chart components required by the bound
  exact ⟨C, hCnn, fun ε hε h hh =>
    hC ε hε.1 hε.2 h (Work.Diff.STE.B3.R_contDiff_of_chartData D h hh)⟩

end Work.Diff.STE.Lead
