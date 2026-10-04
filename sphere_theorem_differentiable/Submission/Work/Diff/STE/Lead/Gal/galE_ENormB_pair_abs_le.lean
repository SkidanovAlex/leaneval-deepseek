import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.ENormSq_pairing_le
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.continuous_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.Gal

/-- The physical energy `ENormSq k f = Σ_l ∫_{unitCube} ‖pdVec k l f‖²` is nonnegative (a sum of
integrals of nonnegative functions; no integrability is needed for this). -/
private lemma ENormSq_nonneg' {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (f : (ι → ℝ) → ℂ) :
    0 ≤ Work.Diff.STE.ENormSq k f :=
  Finset.sum_nonneg fun _ _ => MeasureTheory.integral_nonneg fun _ => sq_nonneg _

/-- A continuous complex-valued function has square-integrable norm over the unit cube: the unit
cube sits inside the compact box `[0,1]^ι`, on which a continuous function is integrable. -/
private lemma integrable_normSq_of_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : (ι → ℝ) → ℂ) (hU : Continuous U) :
    MeasureTheory.Integrable (fun x : ι → ℝ => ‖U x‖ ^ 2)
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : Work.Diff.STE.unitCube (ι := ι) ⊆
      Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [Work.Diff.STE.unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC
      ((continuous_norm.comp hU).pow 2).continuousOn).mono_set hsub

/-- **Finite-dimensional Cauchy–Schwarz, in the "square-root" form used below.**  If
`|c x| ≤ √(A x) · √(B x)` with `A`, `B ≥ 0`, then
`|Σ_x c x| ≤ √(Σ_x A x) · √(Σ_x B x)`.
(The triangle inequality followed by Cauchy–Schwarz for the sequences `√(A ·)`, `√(B ·)`.) -/
private lemma abs_sum_le_sqrt_mul_sqrt {α : Type*} [Fintype α] (A B c : α → ℝ)
    (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x)
    (hc : ∀ x, |c x| ≤ Real.sqrt (A x) * Real.sqrt (B x)) :
    |∑ x, c x| ≤ Real.sqrt (∑ x, A x) * Real.sqrt (∑ x, B x) := by
  have h1 : |∑ x, c x| ≤ ∑ x, Real.sqrt (A x) * Real.sqrt (B x) :=
    (Finset.abs_sum_le_sum_abs c Finset.univ).trans (Finset.sum_le_sum fun x _ => hc x)
  have hsq : (∑ x, Real.sqrt (A x) * Real.sqrt (B x)) ^ 2 ≤ (∑ x, A x) * (∑ x, B x) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
      (fun x => Real.sqrt (A x)) (fun x => Real.sqrt (B x))
    rwa [Finset.sum_congr rfl (fun x _ => Real.sq_sqrt (hA x)),
      Finset.sum_congr rfl (fun x _ => Real.sq_sqrt (hB x))] at h
  have h3 : |∑ x, c x| ^ 2 ≤ (∑ x, A x) * (∑ x, B x) :=
    (pow_le_pow_left₀ (abs_nonneg _) h1 2).trans hsq
  have h4 := Real.sqrt_le_sqrt h3
  rwa [Real.sqrt_sq (abs_nonneg _), Real.sqrt_mul (Finset.sum_nonneg fun x _ => hA x)] at h4

/-- **Cauchy–Schwarz for the physical `Hᵏ` pairing, summed over the charts.**

`D.ENormB_pair k h h'` is the physical `Hᵏ` pairing of the localised chart components
(`B3/BNorm_ENormB_equiv.lean`), `D.ENormB k h = D.ENormB_pair k h h` the associated energy.  Claim

  `|D.ENormB_pair k h h'| ≤ √(D.ENormB k h) · √(D.ENormB k h')`

for sections `h`, `h'` with `C^∞` localised components.

PROOF ROUTE: unfold `ENormB_pair` as
`Σ_i Σ_{a,b} Σ_{l : Fin k → ι} L2re (∂^l (Rper i h a b)) (∂^l (Rper i h' a b))`.
The cleanest proof is one finite-dimensional Cauchy–Schwarz over the *full* index set
`(i,a,b,l)` (reviewer's suggestion), or `Work.Diff.STE.ENormSq_pairing_le` per component
`(i,a,b)` followed by `Finset.sum_mul_sq_le_sq_mul_sq` over `(i,a,b)`.  The integrability hypotheses
of `ENormSq_pairing_le` (`Integrable (fun x => ‖pdVec k l v x‖²) (volume.restrict unitCube)`) come
from the continuity of `pdVec k l v` (smoothness of the component; `continuous_pdVec` is proved in
`Diff/STE/continuous_pdVec.lean`) plus `unitCube ⊆ Set.Icc 0 1` (compact, finite measure) — the
workspace may already have `integrableOn_normSq_pdVec`.

Consumer: `galE_apriori` needs the level-`0` estimate
`|E_0 (D.J ρ ε f) u| ≤ √(E_0 (D.J ρ ε f))·√(E_0 u)` for the DeTurck tensor `f` of the foreground
(the only way to bound the level-`0` part of the energy derivative), and the analogous
level-`k` estimates.  The statement is independent of the mollifier and of `ε`. -/
theorem galE_ENormB_pair_abs_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (h h' : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b))
    (hh' : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h' a b)) :
    |D.ENormB_pair k h h'|
      ≤ Real.sqrt (D.ENormB k h) * Real.sqrt (D.ENormB k h') := by
  classical
  -- ## Cauchy–Schwarz for a single chart component `(i,a,b)`, by `ENormSq_pairing_le`
  have hcs : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      |∑ l : Fin k → Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l (D.Rper i h a b))
            (Work.Diff.STE.pdVec k l (D.Rper i h' a b))|
        ≤ Real.sqrt (Work.Diff.STE.ENormSq k (D.Rper i h a b))
          * Real.sqrt (Work.Diff.STE.ENormSq k (D.Rper i h' a b)) := by
    intro i a b
    -- smoothness and `1`-periodicity of the periodised components
    obtain ⟨hsm, _⟩ := Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i h a b (hh i a b)
    obtain ⟨hsm', _⟩ := Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i h' a b (hh' i a b)
    -- square-integrability of all the iterated derivatives, from their continuity
    have hint : ∀ (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) u → ∀ l : Fin k → Fin (Module.finrank ℝ E),
        MeasureTheory.Integrable (fun x => ‖Work.Diff.STE.pdVec k l u x‖ ^ 2)
          (MeasureTheory.volume.restrict
            (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))) := by
      intro u hu l
      exact integrable_normSq_of_continuous _
        (Work.Diff.STE.continuous_pdVec k l u
          (hu.of_le (WithTop.coe_le_coe.mpr (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))))
    have hpair := Work.Diff.STE.ENormSq_pairing_le k (D.Rper i h a b) (D.Rper i h' a b)
      (hint _ hsm) (hint _ hsm')
    have h1 := Real.sqrt_le_sqrt hpair
    rw [Real.sqrt_sq (abs_nonneg _),
      Real.sqrt_mul (ENormSq_nonneg' k (D.Rper i h a b))] at h1
    exact h1
  -- ## Rewriting the composite pairing and energy as sums over the full index set `(i,a,b)`
  have hpair : D.ENormB_pair k h h'
      = ∑ x : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
          ∑ l : Fin k → Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re
              (Work.Diff.STE.pdVec k l (D.Rper x.1 h x.2.1 x.2.2))
              (Work.Diff.STE.pdVec k l (D.Rper x.1 h' x.2.1 x.2.2)) := by
    simp only [Work.Diff.STE.B3Data.ENormB_pair]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
  have hE : D.ENormB k h
      = ∑ x : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
          Work.Diff.STE.ENormSq k (D.Rper x.1 h x.2.1 x.2.2) := by
    simp only [Work.Diff.STE.B3Data.ENormB]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
  have hE' : D.ENormB k h'
      = ∑ x : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
          Work.Diff.STE.ENormSq k (D.Rper x.1 h' x.2.1 x.2.2) := by
    simp only [Work.Diff.STE.B3Data.ENormB]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
  -- ## Cauchy–Schwarz over the full index set
  have hmain := abs_sum_le_sqrt_mul_sqrt
    (fun x : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) =>
      Work.Diff.STE.ENormSq k (D.Rper x.1 h x.2.1 x.2.2))
    (fun x : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) =>
      Work.Diff.STE.ENormSq k (D.Rper x.1 h' x.2.1 x.2.2))
    (fun x : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) =>
      ∑ l : Fin k → Fin (Module.finrank ℝ E),
        Work.Diff.STE.L2re
          (Work.Diff.STE.pdVec k l (D.Rper x.1 h x.2.1 x.2.2))
          (Work.Diff.STE.pdVec k l (D.Rper x.1 h' x.2.1 x.2.2)))
    (fun _ => ENormSq_nonneg' k _) (fun _ => ENormSq_nonneg' k _)
    (fun x => hcs x.1 x.2.1 x.2.2)
  rw [← hpair, ← hE, ← hE'] at hmain
  exact hmain

end Work.Diff.STE.Lead.Gal
