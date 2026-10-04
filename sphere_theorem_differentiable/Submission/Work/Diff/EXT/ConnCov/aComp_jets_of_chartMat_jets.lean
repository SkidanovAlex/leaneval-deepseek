import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.EXT.christoffel_bounds_of_core
import Submission.Work.Diff.EXT.koszulPair_eq_sKz
import Submission.Work.Diff.EXT.chartData_step_aux
import Submission.Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound
import Submission.Work.Diff.EXT.chartMat_fderiv_basis
import Submission.Work.Diff.GE.chrB_eq_sum_gramInv
import Submission.Work.Diff.GE.cGram_chrB_eq_koszulPair
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.T.mvfderiv_frameVector_real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Chart jets of the connection difference from chart jets of the metric

`Work.Diff.EXT.ConnCov.aComp_jets_of_chartMat_jets`: the chart components
`aComp G x₀ t y i j l = ∑_p g_{lp}(Γ^p_{ij}(G t) − Γ^p_{ij}(G 0))` of the *lowered* connection
difference `g_t(∇^{g_t} − ∇^{g_0})` have uniformly bounded iterated Fréchet derivatives of every
order on `K × [T/2, T)`, as soon as the chart matrix `y ↦ chartMat G x₀ t y` has uniformly bounded
iterated Fréchet derivatives of every order there (and is smooth at the points of `K` in the
spatial variable).

The point of the statement is that **no lower bound on the chart matrix (uniform ellipticity) is
needed**: the term of `aComp` that would require the inverse metric cancels.  Namely, lowering the
upper index of the Christoffel symbol gives the Koszul pairing,

`∑_p g_{lp} Γ^p_{ij}(G t) = Γ_{lij}(G t) = ½(∂_i g_{jl} + ∂_j g_{il} − ∂_l g_{ij})`,

which is a *linear* expression in the first chart derivatives of `G t`
(`Work.Diff.EXT.koszulPair_eq_sKz`), and the remaining term `∑_p g_{lp}Γ^p_{ij}(G 0)` only involves
the *fixed* initial metric `G 0` (whose Christoffel jets are bounded on the compact `K` by
`Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound`, again with no ellipticity hypothesis).

The proof machinery is the `JBu` interface of `Submission.Work.Diff.EXT.christoffel_bounds_of_core`
(smoothness at the points of `K` plus a uniform bound for each order `≤ k`), which is closed under
sums, products and directional derivatives; the directional derivative of a `JBu` family of order
`k + 1` is a `JBu` family of order `k` (Mathlib's `norm_iteratedFDeriv_clm_apply_const` and
`norm_iteratedFDeriv_fderiv`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.EXT.CBound

namespace Work.Diff.EXT.ConnCov

section Aux

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## Elementary jet estimates -/

/-- A component of a smooth map into a `Π`-type has no larger jets. -/
lemma norm_iteratedFDeriv_component_le_aux
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} [Fintype ι] {f : E → (ι → F)} {y : E} (n : ℕ)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f y) (a : ι) :
    ‖iteratedFDeriv ℝ n (fun y' => f y' a) y‖ ≤ ‖iteratedFDeriv ℝ n f y‖ := by
  have h := (ContinuousLinearMap.proj a : (ι → F) →L[ℝ] F).norm_iteratedFDeriv_comp_left
    (f := f) (x := y) (n := n) hf (by simp)
  have hnorm : ‖(ContinuousLinearMap.proj a : (ι → F) →L[ℝ] F)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
    simpa using norm_le_pi_norm x a
  calc ‖iteratedFDeriv ℝ n (fun y' => f y' a) y‖
      = ‖iteratedFDeriv ℝ n ((ContinuousLinearMap.proj a : (ι → F) →L[ℝ] F) ∘ f) y‖ := rfl
    _ ≤ ‖(ContinuousLinearMap.proj a : (ι → F) →L[ℝ] F)‖ * ‖iteratedFDeriv ℝ n f y‖ := h
    _ ≤ 1 * ‖iteratedFDeriv ℝ n f y‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ n f y‖ := one_mul _

/-- Smoothness of one component of an `MatE`-valued map. -/
lemma contDiffAt_component_of_chartMat
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (h : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y)
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' a b) y :=
  (ContinuousLinearMap.contDiff
      ((ContinuousLinearMap.proj b : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj a : (Fin (Module.finrank ℝ E) →
          Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)))).contDiffAt.comp
    y h

/-- `JBu` is closed under multiplication by a constant. -/
lemma JBu_const_mul_aux (T : ℝ) (K : Set E) (k : ℕ) (c : ℝ) {A : ℝ → E → ℝ}
    (hA : JBu (T / 2) T K k A) :
    JBu (T / 2) T K k (fun t y => c * A t y) := by
  obtain ⟨hsm, B, hB0, hB⟩ := hA
  refine ⟨fun t ht y hy => by
      simpa only [smul_eq_mul] using (hsm t ht y hy).const_smul c,
    fun i => |c| * B i,
    fun i => mul_nonneg (abs_nonneg c) (hB0 i), fun t ht y hy i hi => ?_⟩
  have h1 : iteratedFDeriv ℝ i (fun y' : E => c * A t y') y
      = c • iteratedFDeriv ℝ i (A t) y := by
    rw [show (fun y' : E => c * A t y') = c • (A t) by
      funext y'; rw [Pi.smul_apply, smul_eq_mul]]
    exact iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (f := A t) (x := y) (a := c)
      ((hsm t ht y hy).of_le (by simp))
  rw [h1, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB t ht y hy i hi) (abs_nonneg c)

/-- A `JBu` family of order `k + 1` has directional derivatives which are `JBu` families of
order `k`. -/
lemma JBu_fderiv_apply_aux (A : ℝ → E → ℝ) (T : ℝ) (K : Set E) (k : ℕ) (v : E)
    (hA : JBu (T / 2) T K (k + 1) A) :
    JBu (T / 2) T K k (fun t y => fderiv ℝ (A t) y v) := by
  obtain ⟨hsm, B, hB0, hB⟩ := hA
  refine ⟨fun t ht y hy => ?_, fun i => ‖v‖ * B (i + 1),
    fun i => mul_nonneg (norm_nonneg v) (hB0 (i + 1)), fun t ht y hy i hi => ?_⟩
  · exact ((hsm t ht y hy).fderiv_right (by simp)).clm_apply contDiffAt_const
  · have hf : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => fderiv ℝ (A t) y') y :=
      (hsm t ht y hy).fderiv_right (by simp)
    refine le_trans (norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ)
      (f := fun y' : E => fderiv ℝ (A t) y') (c := v) (x := y) (n := i) hf (by simp)) ?_
    rw [norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := A t) (x := y) (n := i)]
    exact mul_le_mul_of_nonneg_left (hB t ht y hy (i + 1) (by omega)) (norm_nonneg v)

/-! ## The lowered Christoffel symbol is the Koszul pairing -/

/-- **Lowering the upper index of the Christoffel symbol.**  Contracting the Christoffel symbols of
the Levi-Civita connection of `G t` with the Gram matrix of the coordinate frame gives the Koszul
pairing of the chart coordinates. -/
lemma sum_GramM_cGam_eq_koszulPair_aux
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j k : Fin (Module.finrank ℝ E)) :
    (∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) k p
          * Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
      = Work.Diff.GE.koszulPair (I := I) G x₀ i j k t (Work.Diff.EXT.pt (I := I) x₀ y) := by
  have hp : Work.Diff.EXT.pt (I := I) x₀ y ∈ (chartAt H x₀).source := by
    rw [Work.Diff.EXT.pt, ← extChartAt_source (I := I) x₀]
    exact (extChartAt I x₀).map_target hy
  have hsym : ∀ p : Fin (Module.finrank ℝ E),
      Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) k p
        = Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) p k :=
    fun p => Work.Diff.GE.mComp_comm (I := I) G x₀ k p t (Work.Diff.EXT.pt (I := I) x₀ y)
  have hswap : (∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) k p
          * Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
      = ∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j
          * Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) p k := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hsym p, mul_comm]
  rw [hswap]
  rw [Work.Diff.EXT.cmfb_sum_cGam_mul_GramM_eq (I := I) G x₀ t hp i j k]
  rw [Work.Diff.GE.cGram_chrB_eq_koszulPair (I := I) G x₀ hp t j i k]
  exact (Work.Diff.EXT.cmfb_koszulPair_comm (I := I) G x₀ (Work.Diff.EXT.pt (I := I) x₀ y) t i j k).symm

/-! ## `JBu` families built from the chart matrix -/

/-- The components of the chart matrix have `JBu` jets of every order. -/
lemma chartMat_component_jBu
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (x₀ : M) (K : Set E) (k : ℕ)
    (hjets : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y‖
        ≤ C)
    (hsm : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y)
    (a b : Fin (Module.finrank ℝ E)) :
    JBu (T / 2) T K k
      (fun t y => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y a b) := by
  choose C hC0 hC using hjets
  refine ⟨fun t ht y hy => contDiffAt_component_of_chartMat (I := I) (M := M) G x₀ t
      (hsm t ht y hy) a b, C, hC0, fun t ht y hy i hi => ?_⟩
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y := hsm t ht y hy
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' a) y :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.proj a :
      (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) →L[ℝ]
        (Fin (Module.finrank ℝ E) → ℝ))).contDiffAt.comp y h1
  calc ‖iteratedFDeriv ℝ i
        (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' a b) y‖
      ≤ ‖iteratedFDeriv ℝ i
          (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' a) y‖ :=
        norm_iteratedFDeriv_component_le_aux (f := fun y' : E =>
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' a) i h2 b
    _ ≤ ‖iteratedFDeriv ℝ i
          (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y‖ :=
        norm_iteratedFDeriv_component_le_aux (f := fun y' : E =>
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') i h1 a
    _ ≤ C i := hC i t ht y hy

/-- The Koszul pairing `sKz` of the first chart jets of `G t` is a `JBu` family of order `k`. -/
lemma sKz_dJet1_jBu
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (x₀ : M) (K : Set E) (k : ℕ)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hcomp : ∀ (a b : Fin (Module.finrank ℝ E)), JBu (T / 2) T K (k + 1)
      (fun t y => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y a b))
    (i j l : Fin (Module.finrank ℝ E)) :
    JBu (T / 2) T K k
      (fun t y => Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G t) x₀ y) i j l) := by
  have hL : ∀ (m a b : Fin (Module.finrank ℝ E)), JBu (T / 2) T K k
      (fun t y => fderiv ℝ (fun y' : E =>
        Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' a b) y
          (Work.Diff.EXT.bB (E := E) m)) :=
    fun m a b => JBu_fderiv_apply_aux _ T K k (Work.Diff.EXT.bB (E := E) m) (hcomp a b)
  have hcomb : JBu (T / 2) T K k
      (fun t y => (fderiv ℝ (fun y' : E =>
            Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' j l) y
            (Work.Diff.EXT.bB (E := E) i)
          + fderiv ℝ (fun y' : E =>
            Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i l) y
            (Work.Diff.EXT.bB (E := E) j))
        - fderiv ℝ (fun y' : E =>
            Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
            (Work.Diff.EXT.bB (E := E) l)) :=
    ((hL i j l).add (hL j i l)).sub (hL l i j)
  have hhalf := JBu_const_mul_aux T K k ((1 : ℝ) / 2) hcomb
  refine hhalf.congrOn (x₀ := x₀) hKt (fun t y hy => ?_)
  simp only [Work.Diff.EXT.sKz, Work.Diff.EXT.dJet1, Work.Diff.EXT.chartMat]
  rw [Work.Diff.EXT.kz_fderiv_chartMatFun_apply (I := I) (M := M) (G t) x₀ hy i j l,
    Work.Diff.EXT.kz_fderiv_chartMatFun_apply (I := I) (M := M) (G t) x₀ hy j i l,
    Work.Diff.EXT.kz_fderiv_chartMatFun_apply (I := I) (M := M) (G t) x₀ hy l i j]

/-- The Christoffel jets of the fixed initial metric `G 0` are `JBu` families of every order. -/
lemma cGam0_jBu_aux
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (x₀ : M) (K : Set E) (k : ℕ)
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x₀).target)
    (p i j : Fin (Module.finrank ℝ E)) :
    JBu (T / 2) T K k
      (fun _ y => Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j) :=
  Work.Diff.EXT.CBound.cGam0_jBu (I := I) (M := M) G (T / 2) T x₀ K hKt
    (fun k => Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound (I := I) (M := M) G x₀ K hK hKt k)
    k p i j

/-- The second summand `∑_p g_{lp}Γ^p_{ij}(G 0)` of the chart array of the connection difference
is a `JBu` family of order `k`. -/
lemma aComp_termB_jBu
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (x₀ : M) (K : Set E) (k : ℕ)
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x₀).target)
    (hjets : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y‖
        ≤ C)
    (hsm : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y)
    (i j l : Fin (Module.finrank ℝ E)) :
    JBu (T / 2) T K k (fun t y => ∑ p : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y l p
        * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j) :=
  JBu.sum (fun p => (chartMat_component_jBu (I := I) (M := M) G T x₀ K k hjets hsm l p).mul
    (cGam0_jBu_aux (I := I) (M := M) G T x₀ K k hK hKt p i j))

/-! ## The pointwise identity -/

/-- The chart array of the lowered connection difference is the Koszul pairing minus the
`G 0`-contribution. -/
lemma aComp_eq_sKz_sub
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j l : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y i j l
      = Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G t) x₀ y) i j l
        - ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y l p
              * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j := by
  have h1 := sum_GramM_cGam_eq_koszulPair_aux (I := I) (M := M) G x₀ t hy i j l
  have h2 : Work.Diff.GE.koszulPair (I := I) G x₀ i j l t (Work.Diff.EXT.pt (I := I) x₀ y)
      = Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G t) x₀ y) i j l :=
    Work.Diff.EXT.koszulPair_eq_sKz (I := I) (M := M) (G t) x₀ hy i j l
  simp only [Work.Diff.EXT.aComp]
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ) =>
    show Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) l p
        * (Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j
          - Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
      = Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) l p
          * Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j
        - Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y l p
          * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j from by
      rw [mul_sub]
      rfl)]
  rw [Finset.sum_sub_distrib, h1, h2]

end Aux

theorem aComp_jets_of_chartMat_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (x₀ : M) (K : Set E) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x₀).target)
    (hjets : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y‖
        ≤ C)
    (hsm : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k
          (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y‖ ≤ C := by
  intro k
  have hcomp : ∀ (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.EXT.CBound.JBu (T / 2) T K (k + 1)
        (fun t y => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y a b) :=
    fun a b => chartMat_component_jBu (I := I) (M := M) G T x₀ K (k + 1) hjets hsm a b
  have hA : ∀ (i j l : Fin (Module.finrank ℝ E)),
      Work.Diff.EXT.CBound.JBu (T / 2) T K k
        (fun t y => Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G t) x₀ y) i j l) :=
    fun i j l => sKz_dJet1_jBu (I := I) (M := M) G T x₀ K k hKt hcomp i j l
  have hB : ∀ (i j l : Fin (Module.finrank ℝ E)),
      Work.Diff.EXT.CBound.JBu (T / 2) T K k
        (fun t y => ∑ p : Fin (Module.finrank ℝ E),
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y l p
            * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j) :=
    fun i j l => aComp_termB_jBu (I := I) (M := M) G T x₀ K k hK hKt hjets hsm i j l
  have hfull : ∀ (i j l : Fin (Module.finrank ℝ E)),
      Work.Diff.EXT.CBound.JBu (T / 2) T K k
        (fun t y => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y i j l) := by
    intro i j l
    refine ((hA i j l).sub (hB i j l)).congrOn (x₀ := x₀) hKt (fun t y hy => ?_)
    exact (aComp_eq_sKz_sub (I := I) (M := M) G x₀ t hy i j l).symm
  choose B hB0 hB using fun p :
      Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
    (hfull p.1 p.2.1 p.2.2).2
  refine ⟨∑ p, B p k, Finset.sum_nonneg (fun p _ => hB0 p k), ?_⟩
  intro t ht y hy i j l
  refine le_trans (hB (i, j, l) t ht y hy k le_rfl) ?_
  exact Finset.single_le_sum (fun p _ => hB0 p k) (Finset.mem_univ (i, j, l))

end Work.Diff.EXT.ConnCov
