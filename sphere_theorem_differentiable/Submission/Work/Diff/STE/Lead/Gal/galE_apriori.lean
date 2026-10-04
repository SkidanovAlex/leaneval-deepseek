import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.Lead.Gal.hasDerivAt_galE
import Submission.Work.Diff.STE.Lead.Gal.gardingAssembly
import Submission.Work.Diff.STE.Lead.Gal.galE_exp_bound
import Submission.Work.Diff.STE.Lead.Gal.galE_J_bounded
import Submission.Work.Diff.STE.Lead.Gal.galE_J_L2_bounded
import Submission.Work.Diff.STE.Lead.Gal.galE_ENormB_pair_abs_le
import Submission.Work.Diff.STE.B3.ENormB_pair_J_commutator_v2
import Submission.Work.Diff.STE.B3.BPair_J_self_smooth
import Submission.Work.Diff.STE.B3.transport_Rres_contDiffOn
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.D.chartData_metric
import Submission.Work.Diff.STE.ENormSq_pairing_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The a priori energy estimate `galE_apriori` (Layer D2 of the STE design)

`galE D k ε c = ENormB k (galState D ε c) + ENormB 0 (galState D ε c)` is the physical `Hᵏ`
energy of the metric `galState D ε c`; along a solution `c` of the span-form Galerkin ODE
`c' = galVF2 … c` (the Friedrichs scheme `u~' = J ρ ε (P u~)`, `u~ = J ρ ε (galState D ε c)` the
*foreground*, `P` the DeTurck operator) it obeys an exponential bound uniform in `ε ∈ (0,1]`.

The proof assembles:

* `hasDerivAt_galE` — the derivative of the energy along a coefficient curve is
  `2 (⟨genMap c', galState⟩_k + ⟨genMap c', galState⟩_0)`;
* `genMap_galVF2` — `genMap (galVF2 … c) = J ρ ε (P (J ρ ε (galState c)))`;
* `galE_comm` — the **order-`k` Friedrichs adjointness** (the commutator "(F)"): the mollifier is
  self-adjoint for the `Hᵏ` pairing up to an error losing one derivative;
* `gardingAssembly` — the Gårding/dissipation bound
  `⟨P v, v⟩_k ≤ -(λ'/2) ‖v‖²_{k+1} + C (1 + B)²` for every metric `v` with `λ g₀ ≤ v ≤ K g₀` and
  bounded chart jets, plus `‖P v‖²_{k-1} + ‖P v‖²_0 ≤ C (1+B)² (1 + ‖v‖²_{k+1})`;
* `galE_J_bounded`, `galE_J_L2_bounded` — the `ε`-uniform boundedness of the mollifier;
* `galE_ENormB_pair_abs_le` — Cauchy–Schwarz for the physical pairing;
* `galE_exp_bound` — the comparison step.

The chain is `y' / 2 ≤ -(λ'/2) μ + A + √(A(1+μ))·M₁` with `μ = ‖v‖²_{k+1}`; Young's inequality
against the dissipation bounds the right-hand side by the constant `M = 2(A + η + A M₁²/(4η))`,
which is then `C` in the conclusion.
-/

namespace Work.Diff.STE.Lead.Gal

open Classical LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
  Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## Elementary facts about the energy -/

/-- The energy `galE` is nonnegative. -/
lemma galE_nonneg (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    0 ≤ galE D k ε c := by
  have h1 : 0 ≤ D.ENormB k (galState D ε c) :=
    Work.Diff.STE.B3Data.ENormB_nonneg D k _ (fun i _ _ => ENormSq_nonneg _)
  have h2 : 0 ≤ D.ENormB 0 (galState D ε c) :=
    Work.Diff.STE.B3Data.ENormB_nonneg D 0 _ (fun i _ _ => ENormSq_nonneg _)
  simp only [galE]
  linarith

/-- Both summands of `galE` are dominated by `galE`. -/
lemma ENormB_le_galE (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (ε : ℝ)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    D.ENormB k (galState D ε c) ≤ galE D k ε c ∧
      D.ENormB 0 (galState D ε c) ≤ galE D k ε c := by
  have h1 : 0 ≤ D.ENormB k (galState D ε c) :=
    Work.Diff.STE.B3Data.ENormB_nonneg D k _ (fun i _ _ => ENormSq_nonneg _)
  have h2 : 0 ≤ D.ENormB 0 (galState D ε c) :=
    Work.Diff.STE.B3Data.ENormB_nonneg D 0 _ (fun i _ _ => ENormSq_nonneg _)
  constructor <;> simp only [galE] <;> linarith

/-- **The a priori estimate, assembled from its analytic inputs** (the statements proved or
requested elsewhere, taken here as explicit hypotheses). -/
theorem galE_apriori_aux
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (k : ℕ) (hk : Module.finrank ℝ E + 12 < 2 * k)
    (hJb : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b)) →
        D.ENormB k (D.J ρ ε h) ≤ C * (D.ENormB k h + D.ENormB 0 h))
    (hJ0 : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b)) →
        D.ENormB 0 (D.J ρ ε h) ≤ C * D.ENormB 0 h)
    (hCS : ∀ (m : ℕ) (h h' : Work.Diff.STE.Bil (I := I) (M := M)),
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b)) →
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h' a b)) →
        |D.ENormB_pair m h h'| ≤ Real.sqrt (D.ENormB m h) * Real.sqrt (D.ENormB m h'))
    (hcomm : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (f u : Work.Diff.STE.Bil (I := I) (M := M)),
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b)) →
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b)) →
        |D.ENormB_pair k (D.J ρ ε f) u - D.ENormB_pair k f (D.J ρ ε u)|
          ≤ C * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f) * Real.sqrt (D.ENormB k u))
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (D.J ρ ε (galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        (D.J ρ ε (galState D ε (c t))) x v v ≤ K * g₀.inner x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (i : ι₀) (c' d : Fin (Module.finrank ℝ E)) (m : ℕ)
        (hm : m ≤ k + 1) (β : Fin m → Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i (D.J ρ ε (galState D ε (c t))) c' d y : ℝ) : ℂ)) z‖ ≤ K) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, galE D k ε (c t) ≤ B) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        galE D k ε (c t) ≤ (galE D k ε (c 0) + 1) * Real.exp (C * t) - 1 := by
  obtain ⟨CJ, hCJ0, hJb⟩ := hJb
  obtain ⟨CJ0, hCJ00, hJ0⟩ := hJ0
  obtain ⟨Cc, hCc0, hcomm⟩ := hcomm
  obtain ⟨lam', Cg, hlam'0, hCg0, hGard⟩ :=
    gardingAssembly (I := I) (M := M) D hLC k hk lam K hlam hK
  -- the universal constants
  set B' : ℝ := CJ * B with hB'def
  have hB'0 : 0 ≤ B' := by rw [hB'def]; exact mul_nonneg hCJ0 hB
  set A : ℝ := Cg * (1 + B') ^ 2 with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  set M1 : ℝ := (Cc + Real.sqrt CJ0) * Real.sqrt B with hM1def
  have hM10 : 0 ≤ M1 := by
    rw [hM1def]
    exact mul_nonneg (add_nonneg hCc0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  set eta : ℝ := lam' / 4 with hetadef
  have heta0 : 0 < eta := by rw [hetadef]; linarith
  have heta_le : eta ≤ lam' / 2 := by rw [hetadef]; linarith
  set Cfin : ℝ := 2 * (A + eta + A * M1 ^ 2 / (4 * eta)) with hCfindef
  have hCf0 : 0 ≤ Cfin := by
    rw [hCfindef]
    have h1 : 0 ≤ A * M1 ^ 2 / (4 * eta) := by positivity
    linarith
  refine ⟨Cfin, hCf0, ?_⟩
  intro ε hε hε1 c T hT hder hpos hlow hup hjet hBnd t ht
  -- the energy and its derivative along `c`
  set y : ℝ → ℝ := fun s => galE D k ε (c s) with hydef
  set y' : ℝ → ℝ := fun s =>
    2 * (D.ENormB_pair k
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε
            (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c s)))
          (galState D ε (c s)) +
         D.ENormB_pair 0
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε
            (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c s)))
          (galState D ε (c s))) with hy'def
  have hg₀ : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner) :=
    Work.Diff.STE.D.chartData_metric g₀
  have hderiv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (y' s) s := by
    intro s hs
    have h := hasDerivAt_galE (I := I) (M := M) D k ε hg₀ (hder s hs)
    rw [hydef, hy'def]
    exact h
  -- the one-sided constant bound on the derivative
  have hineq : ∀ s ∈ Set.Ico (0 : ℝ) T, y' s ≤ Cfin := by
    intro s hs
    -- smoothness / symmetry / positivity of the state and of the foreground
    have hstate : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (galState D ε (c s)) a b) :=
      galE_sm_galState D ε hg₀ (c s)
    have hsym : ∀ (x : M) (p q : TangentSpace I x),
        ((galState D ε (c s) x) p) q = ((galState D ε (c s) x) q) p :=
      isSymm_galState D ε (c s)
    have hcd : Work.Diff.STE.D.ChartData (I := I) (M := M) (galState D ε (c s)) :=
      chartData_galState D ε hg₀ (c s)
    have hsym_v : ∀ (x : M) (p q : TangentSpace I x),
        ((D.J ρ ε (galState D ε (c s)) x) p) q
          = ((D.J ρ ε (galState D ε (c s)) x) q) p :=
      isSymm_J D ρ ε hε hρ0 (galState D ε (c s)) hsym
    have hcd_v : Work.Diff.STE.D.ChartData (I := I) (M := M)
        (D.J ρ ε (galState D ε (c s))) :=
      chartData_J D ρ ε hε hρ0 (galState D ε (c s)) hsym
    have hpos_v : ∀ (x : M) (p : TangentSpace I x), p ≠ 0 →
        0 < ((D.J ρ ε (galState D ε (c s)) x) p) p := hpos s hs
    -- the DeTurck tensor of the foreground
    set f : Work.Diff.STE.Bil (I := I) (M := M) :=
      Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (D.J ρ ε (galState D ε (c s)))
        hsym_v hpos_v hcd_v with hfdef
    have hvel : Work.Diff.STE.D.genMap (I := I) (M := M) D ε
        (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c s))
        = D.J ρ ε f := by
      rw [hfdef]
      exact genMap_galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c s) (hpos s hs)
    have hsm_f : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b) := by
      have hcd' : Work.Diff.STE.D.ChartData (I := I) (M := M)
          (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (D.J ρ ε (galState D ε (c s)))
            hsym_v hpos_v hcd_v) :=
        Work.Diff.STE.B3.chartData_deTurckSec (I := I) (g₀ := g₀) hLC
          (D.J ρ ε (galState D ε (c s))) hsym_v hpos_v hcd_v
      rw [hfdef]
      exact Work.Diff.STE.B3.R_contDiff_of_chartData D _ hcd'
    -- the a priori bound for the foreground
    have hBv : D.ENormB k (D.J ρ ε (galState D ε (c s))) ≤ B' := by
      rw [hB'def]
      have h1 := hJb ε hε hε1 (galState D ε (c s)) hstate
      have h2 : D.ENormB k (galState D ε (c s))
          + D.ENormB 0 (galState D ε (c s)) ≤ B := by
        simpa only [galE] using hBnd s hs
      calc D.ENormB k (D.J ρ ε (galState D ε (c s)))
          ≤ CJ * (D.ENormB k (galState D ε (c s))
              + D.ENormB 0 (galState D ε (c s))) := h1
        _ ≤ CJ * B := by gcongr
    -- the Gårding assembly applied to the foreground
    obtain ⟨hAsm1, hAsm2⟩ := hGard (D.J ρ ε (galState D ε (c s))) hsym_v hpos_v hcd_v
      (hlow s hs) (hup s hs) (hjet s hs) B' hBv
    have hAsm1' : D.ENormB_pair k f (D.J ρ ε (galState D ε (c s)))
        ≤ -(lam' / 2) * D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))) + A := by
      rw [hAdef, hfdef]
      exact hAsm1
    have hAsm2' : D.ENormB (k - 1) f + D.ENormB 0 f
        ≤ A * (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))) := by
      rw [hAdef, hfdef]
      exact hAsm2
    -- the commutator input
    have hcom := hcomm ε hε hε1 f (galState D ε (c s)) hsm_f hstate
    -- the level-`0` input
    have hsymf : Work.Diff.STE.D.IsSymm (I := I) f := by
      rw [hfdef]
      exact Work.Diff.STE.D.deTurckSec_symm (g₀ := g₀) hLC (D.J ρ ε (galState D ε (c s)))
        hsym_v hpos_v hcd_v
    have hsm_Jf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (D.J ρ ε f) a b) := by
      have hcd'' : Work.Diff.STE.D.ChartData (I := I) (M := M) (D.J ρ ε f) :=
        chartData_J D ρ ε hε hρ0 f hsymf
      exact fun i a b => Work.Diff.STE.B3.R_contDiff_of_chartData D _ hcd'' i a b
    have hJf0 : D.ENormB 0 (D.J ρ ε f) ≤ CJ0 * D.ENormB 0 f := hJ0 ε hε hε1 f hsm_f
    have hcs0 : |D.ENormB_pair 0 (D.J ρ ε f) (galState D ε (c s))|
        ≤ Real.sqrt (CJ0 * D.ENormB 0 f)
          * Real.sqrt (D.ENormB 0 (galState D ε (c s))) := by
      refine le_trans (hCS 0 (D.J ρ ε f) (galState D ε (c s)) hsm_Jf hstate) ?_
      have h1 : Real.sqrt (D.ENormB 0 (D.J ρ ε f)) ≤ Real.sqrt (CJ0 * D.ENormB 0 f) :=
        Real.sqrt_le_sqrt hJf0
      exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
    -- auxiliary nonnegativity
    have hμ0 : 0 ≤ D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))) :=
      Work.Diff.STE.B3Data.ENormB_nonneg D (k + 1) _ (fun i _ _ => ENormSq_nonneg _)
    have hEf0nn : 0 ≤ D.ENormB 0 f :=
      Work.Diff.STE.B3Data.ENormB_nonneg D 0 _ (fun i _ _ => ENormSq_nonneg _)
    have hA1 : 0 ≤ A * (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))) :=
      mul_nonneg hA0 (by linarith)
    have hEu : D.ENormB k (galState D ε (c s)) ≤ B := by
      have h := (ENormB_le_galE D k ε (c s)).1
      linarith [h, hBnd s hs]
    have hE0u : D.ENormB 0 (galState D ε (c s)) ≤ B := by
      have h := (ENormB_le_galE D k ε (c s)).2
      linarith [h, hBnd s hs]
    -- the bounds on the two error terms
    have hsq : Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
        ≤ Real.sqrt A * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))) := by
      rw [← Real.sqrt_mul hA0]
      exact Real.sqrt_le_sqrt hAsm2'
    have hsq0 : Real.sqrt (D.ENormB 0 f)
        ≤ Real.sqrt A * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))) := by
      have hknn : 0 ≤ D.ENormB (k - 1) f :=
        Work.Diff.STE.B3Data.ENormB_nonneg D (k - 1) _ (fun i _ _ => ENormSq_nonneg _)
      have h : D.ENormB 0 f ≤ A * (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))) := by
        linarith [hEf0nn, hknn, hAsm2']
      rw [← Real.sqrt_mul hA0]
      exact Real.sqrt_le_sqrt h
    have hSnn : 0 ≤ Real.sqrt A
        * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have herr1 : Cc * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
          * Real.sqrt (D.ENormB k (galState D ε (c s)))
        ≤ Real.sqrt A * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))))
          * (Cc * Real.sqrt B) := by
      have hb : Real.sqrt (D.ENormB k (galState D ε (c s))) ≤ Real.sqrt B := Real.sqrt_le_sqrt hEu
      have hmem : Cc * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
            * Real.sqrt (D.ENormB k (galState D ε (c s)))
          ≤ Cc * (Real.sqrt A
              * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))))
            * Real.sqrt B := by
        calc Cc * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
              * Real.sqrt (D.ENormB k (galState D ε (c s)))
            = Cc * (Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
                * Real.sqrt (D.ENormB k (galState D ε (c s)))) := by ring
          _ ≤ Cc * ((Real.sqrt A
                * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))))
                * Real.sqrt B) := by
              refine mul_le_mul_of_nonneg_left ?_ hCc0
              exact mul_le_mul hsq hb (Real.sqrt_nonneg _) hSnn
          _ = Cc * (Real.sqrt A
                * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))))
              * Real.sqrt B := by ring
      calc Cc * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
            * Real.sqrt (D.ENormB k (galState D ε (c s)))
          ≤ Cc * (Real.sqrt A
              * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))))
            * Real.sqrt B := hmem
        _ = Real.sqrt A * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))))
            * (Cc * Real.sqrt B) := by ring
    have herr2 : Real.sqrt (CJ0 * D.ENormB 0 f) * Real.sqrt (D.ENormB 0 (galState D ε (c s)))
        ≤ Real.sqrt A * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))))
          * (Real.sqrt CJ0 * Real.sqrt B) := by
      have hb : Real.sqrt (D.ENormB 0 (galState D ε (c s))) ≤ Real.sqrt B := Real.sqrt_le_sqrt hE0u
      have hCJ0r : 0 ≤ Real.sqrt CJ0 := Real.sqrt_nonneg _
      have hsqc : Real.sqrt (CJ0 * D.ENormB 0 f)
          ≤ Real.sqrt CJ0
            * (Real.sqrt A * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))))) := by
        rw [Real.sqrt_mul hCJ00]
        exact mul_le_mul_of_nonneg_left hsq0 hCJ0r
      have hmem : Real.sqrt (CJ0 * D.ENormB 0 f) * Real.sqrt (D.ENormB 0 (galState D ε (c s)))
          ≤ (Real.sqrt CJ0
              * (Real.sqrt A
                * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))))))
            * Real.sqrt B :=
        mul_le_mul hsqc hb (Real.sqrt_nonneg _) (mul_nonneg hCJ0r hSnn)
      calc Real.sqrt (CJ0 * D.ENormB 0 f) * Real.sqrt (D.ENormB 0 (galState D ε (c s)))
          ≤ (Real.sqrt CJ0
              * (Real.sqrt A
                * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))))))
            * Real.sqrt B := hmem
        _ = Real.sqrt A * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))))
            * (Real.sqrt CJ0 * Real.sqrt B) := by ring
    have herr : Cc * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
          * Real.sqrt (D.ENormB k (galState D ε (c s)))
        + Real.sqrt (CJ0 * D.ENormB 0 f) * Real.sqrt (D.ENormB 0 (galState D ε (c s)))
        ≤ Real.sqrt A * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))))
          * M1 := by
      have heq : Real.sqrt A * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))))
            * ((Cc + Real.sqrt CJ0) * Real.sqrt B)
          = Real.sqrt A * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))))
            * (Cc * Real.sqrt B)
          + Real.sqrt A * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))))
            * (Real.sqrt CJ0 * Real.sqrt B) := by ring
      rw [hM1def, heq]
      linarith [herr1, herr2]
    -- Young's inequality against the dissipation
    have hyoung : Real.sqrt A
          * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))) * M1
        ≤ eta * (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))))
          + A * M1 ^ 2 / (4 * eta) := by
      set P : ℝ := Real.sqrt eta
        * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))) with hP
      set Q : ℝ := Real.sqrt A * M1 / (2 * Real.sqrt eta) with hQ
      have hPQ : Real.sqrt A
            * Real.sqrt (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))) * M1
          = 2 * P * Q := by
        rw [hP, hQ]
        field_simp
      have hP2 : P ^ 2 = eta * (1 + D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s)))) := by
        rw [hP, mul_pow, Real.sq_sqrt heta0.le, Real.sq_sqrt (by linarith)]
      have hden : (2 * Real.sqrt eta) ^ 2 = 4 * eta := by
        have h2 : (2 * Real.sqrt eta) ^ 2 = 4 * (Real.sqrt eta) ^ 2 := by ring
        rw [h2, Real.sq_sqrt heta0.le]
      have hQ2 : Q ^ 2 = A * M1 ^ 2 / (4 * eta) := by
        have h1 : Q ^ 2 = A * M1 ^ 2 / (2 * Real.sqrt eta) ^ 2 := by
          rw [hQ, div_pow, mul_pow, Real.sq_sqrt hA0]
        rw [h1, hden]
      rw [hPQ]
      nlinarith [sq_nonneg (P - Q), hP2, hQ2]
    -- the final bound
    have hk1le : D.ENormB_pair k (D.J ρ ε f) (galState D ε (c s))
        ≤ -(lam' / 2) * D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))) + A
          + Cc * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
            * Real.sqrt (D.ENormB k (galState D ε (c s))) := by
      have h2 : D.ENormB_pair k (D.J ρ ε f) (galState D ε (c s))
            - D.ENormB_pair k f (D.J ρ ε (galState D ε (c s)))
          ≤ Cc * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
            * Real.sqrt (D.ENormB k (galState D ε (c s))) :=
        (abs_le.mp hcom).2
      linarith [hAsm1', h2]
    have h0le : D.ENormB_pair 0 (D.J ρ ε f) (galState D ε (c s))
        ≤ Real.sqrt (CJ0 * D.ENormB 0 f) * Real.sqrt (D.ENormB 0 (galState D ε (c s))) :=
      le_trans (le_abs_self _) hcs0
    have hfinal : D.ENormB_pair k (D.J ρ ε f) (galState D ε (c s))
          + D.ENormB_pair 0 (D.J ρ ε f) (galState D ε (c s))
        ≤ A + eta + A * M1 ^ 2 / (4 * eta) := by
      have hkey : 0 ≤ (lam' / 2 - eta)
          * D.ENormB (k + 1) (D.J ρ ε (galState D ε (c s))) :=
        mul_nonneg (by linarith [heta_le]) hμ0
      linarith [hk1le, h0le, herr, hyoung, hkey]
    simp only [hy'def]
    rw [hvel, hCfindef]
    linarith [hfinal]
  have h0 : 0 ≤ y 0 := by
    rw [hydef]
    exact galE_nonneg D k ε (c 0)
  have hexp := galE_exp_bound hCf0 hderiv hineq h0 t ht
  simpa only [hydef] using hexp

theorem galE_apriori
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (k : ℕ) (hk : Module.finrank ℝ E + 12 < 2 * k)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v ≤ K * g₀.inner x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (i : ι₀) (c' d : Fin (Module.finrank ℝ E)) (m : ℕ)
        (hm : m ≤ k + 1) (β : Fin m → Fin (Module.finrank ℝ E))
        (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) c' d y : ℝ) : ℂ)) z‖ ≤ K) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, Work.Diff.STE.Lead.galE D k ε (c t) ≤ B) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        Work.Diff.STE.Lead.galE D k ε (c t)
          ≤ (Work.Diff.STE.Lead.galE D k ε (c 0) + 1) * Real.exp (C * t) - 1 := by
  have hk' : Module.finrank ℝ E < 2 * k := by omega
  have hk1 : 1 ≤ k := by omega
  exact galE_apriori_aux (I := I) (M := M) D hLC ρ hρ hρ0 hρs hρ1 k hk
    (galE_J_bounded (I := I) (M := M) D ρ hρ k hk')
    (galE_J_L2_bounded (I := I) (M := M) D ρ hρ)
    (fun m h h' hh hh' => galE_ENormB_pair_abs_le (I := I) (M := M) D m h h' hh hh')
    (Work.Diff.STE.B3.ENormB_pair_J_commutator_v2 (I := I) (M := M) D ρ hρ hρ0 hρs hρ1 k hk' hk1)
    lam K hlam hK B hB

end

end Work.Diff.STE.Lead.Gal
