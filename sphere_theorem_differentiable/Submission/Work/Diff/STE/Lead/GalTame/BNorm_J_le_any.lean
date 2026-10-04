import Mathlib
import Submission.Work.Diff.STE.Lead.J_norm_le
import Submission.Work.Diff.STE.B3.BNorm_J_le_uniform_nodim
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CSq_period_comp_arg_le_nodim_of_isOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! `BNorm_J_le_any`: the Friedrichs mollifier `D.J ρ ε` is bounded on `BNorm k` with a constant uniform
in `ε ∈ (0, ε₁]` and in the section `h` — no `ε ≤ 1` restriction.

ROUTE (confirmed by the reviewers): the restriction `ε ≤ 1` in
`Work.Diff.STE.Lead.BNorm_J_le_of_transfer` and in
`Work.Diff.STE.B3.BNorm_J_le_uniform_nodim` is *never used*: the proof body is
`intro ε _hε _hε1 h hsm` and `_hε1` is passed around but never consumed; the constant is built from
the ε-free chart-transfer constants (`Work.Diff.STE.B3.CSq_period_comp_arg_le_nodim_of_isOpen`) before
`ε` is quantified, and the only ε-dependent ingredients (`Work.Diff.STE.CSq_trunc_le`,
`Work.Diff.STE.B3.STruncR_CSq_le`) hold for every real `ε` with just `‖ρ‖ ≤ 1`. So replay
`BNorm_J_le_of_transfer` (or `BNorm_J_le_uniform_nodim`) with the spurious `ε ≤ 1` hypothesis
deleted; no `hρ0` and no smoothness of `ρ` is needed. -/

noncomputable section

open MeasureTheory BigOperators
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.Lead

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-- **The Friedrichs mollifier is bounded in `BNorm k`, with the chart transfer as a hypothesis and
no restriction on `ε`.**

This is `Work.Diff.STE.Lead.BNorm_J_le_of_transfer` with the (unused) hypothesis `ε ≤ 1` deleted
from the conclusion and from the auxiliary `hmain`; the proof is a verbatim replay. -/

theorem BNorm_J_le_of_transfer_uniform
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
      ∀ (ε : ℝ), 0 < ε →
        ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
          (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
            ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b)) →
          D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h := by
  classical
  -- the per-`(j,a,b)` bound, uniform in the section
  have hmain : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (ε : ℝ), 0 < ε →
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
    · intro ε _hε h hsm
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
  · intro ε _hε h hsm
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
    exact (hCf j a b).2 ε _hε h hsm

end Work.Diff.STE.Lead

namespace Work.Diff.STE.Lead.GalTame

/-! `BNorm_J_le_any`: the Friedrichs mollifier `D.J ρ ε` is bounded on `BNorm k` with a constant uniform
in `ε ∈ (0, ε₁]` and in the section `h` — no `ε ≤ 1` restriction. -/

theorem BNorm_J_le_any
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) ε₁, ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)), ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b)) →
      D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h := by
  -- the ε-free version, obtained by replaying `BNorm_J_le_of_transfer`
  obtain ⟨C, hCnn, hC⟩ := Work.Diff.STE.Lead.BNorm_J_le_of_transfer_uniform (I := I) (M := M) k
    (fun T f hf hfsupp hK U hU hUf hT hinj hdet =>
      Work.Diff.STE.B3.CSq_period_comp_arg_le_nodim_of_isOpen k T f hf hfsupp hK U hU hUf hT hinj
        hdet)
    D ρ hρ
  exact ⟨C, hCnn, fun ε hε h hsm => hC ε hε.1 h hsm⟩

end Work.Diff.STE.Lead.GalTame
