import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.Defs
import Submission.Work.Diff.STE.Lead.GalTame.sharpCoeff
import Submission.Work.Diff.STE.Lead.GalTame.sharpResid
import Submission.Work.Diff.STE.Lead.GalTame.perEnergy
import Submission.Work.Diff.STE.Lead.GalTame.periodic_eq_of_eqOn_openCube
import Submission.Work.Diff.STE.Lead.GalTame.ballIntegralEq
import Submission.Work.Diff.STE.B3.Rres_eq_residualLow
import Submission.Work.Diff.STE.B3.transport_Rres_contDiffOn
import Submission.Work.Diff.STE.B3.Recon
import Submission.Work.Diff.STE.B3.transport_det_Gf_ne_zero
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.Lead.Gal.gardingAssembly
import Submission.Work.Diff.STE.Lead.Gal.gardADefs
import Submission.Work.Diff.STE.Lead.Gal.residualDataPsi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter MeasureTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

/-- **The dictionary between the complex partial derivatives of the periodised component and the
real partial derivatives of the localised component.**  On the open fundamental cube the
periodisation of `R j h a b` is the complexification of `R j h a b`, so the iterated partial
derivatives agree there. -/
lemma st_pd_pd_Rper (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (a b : Idx)
    {z : Idx → ℝ} (hz : ∀ i, z i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) (c d : Idx) :
    Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z
      = ((Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.R j h a b)) z : ℝ) : ℂ) := by
  have hmem : z ∈ Set.pi Set.univ (fun _ : Idx => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    simpa [Set.mem_pi] using hz
  have hopenCube : IsOpen (Set.pi Set.univ (fun _ : Idx => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hevR : D.Rper j h a b =ᶠ[𝓝 z] (fun y => ((D.R j h a b y : ℝ) : ℂ)) :=
    Filter.eventually_of_mem (hopenCube.mem_nhds hmem)
      (fun y hy => D.Rper_eq_R j h a b (by simpa [Set.mem_pi] using hy))
  have hpd : Work.Diff.STE.pd d (D.Rper j h a b)
      =ᶠ[𝓝 z] Work.Diff.STE.pd d (fun y => ((D.R j h a b y : ℝ) : ℂ)) := by
    filter_upwards [hevR.fderiv (𝕜 := ℝ)] with y hy
    simp only [Work.Diff.STE.pd]
    rw [hy]
  rw [Work.Diff.STE.Lead.Gal.pd_congr_of_eventuallyEq_rj hpd c]
  exact congrFun (Work.Diff.STE.Lead.Gal.pd_pd_ofReal_rj c d (D.R j h a b)) z

/-- **A smooth function times a function smooth on an open set containing its closed support.**
The standard bump device. -/
private lemma st_mul_contDiff {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) {f : (Fin n → ℝ) → ℝ} {g : (Fin n → ℝ) → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (hfg : tsupport f ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => f z • g z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · exact hf.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds hz))
  · have hz' : z ∉ tsupport f := fun h => hz (hfg h)
    have hev : f =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hz'
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      (hev.mono fun w hw => by show f w • g w = (0 : F); rw [hw]; simp)

/-- The `pdR`-derivatives of a function that vanishes near a point vanish there. -/
private lemma st_pdR_eq_zero_of_eventuallyEq_zero {n : ℕ} {f : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ}
    (h : f =ᶠ[𝓝 z] 0) (i : Fin n) : Work.Diff.STE.pdR i f z = 0 := by
  rw [Work.Diff.STE.pdR, h.fderiv_eq]
  simp

/-- `R j X a b` vanishes off the `σ j`-ball, hence so do its `pdR`-derivatives. -/
private lemma st_pdR_R_eq_zero (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (a b : Idx) {z : Idx → ℝ}
    (hz : D.σ j < ‖z‖) (i : Idx) :
    Work.Diff.STE.pdR i (D.R j X a b) z = 0 := by
  refine st_pdR_eq_zero_of_eventuallyEq_zero ?_ i
  have hU : {y : Idx → ℝ | D.σ j < ‖y‖} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  filter_upwards [hU] with y hy
  by_cases h0 : D.R j X a b y = 0
  · exact h0
  · exact absurd (Work.Diff.STE.Lead.Gal.support_R_subset_ball D X j a b (by
      simp only [Function.mem_support, Complex.ofReal_ne_zero]; exact h0)) (by
      rw [Metric.mem_ball, dist_zero_right]; exact not_lt.mpr (le_of_lt hy))

/-- `pdR p (pdR q (R j X a b))` vanishes off the `σ j`-ball. -/
private lemma st_pdR_pdR_R_eq_zero (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (a b : Idx) {z : Idx → ℝ}
    (hz : D.σ j < ‖z‖) (p q : Idx) :
    Work.Diff.STE.pdR p (fun y : Idx → ℝ => Work.Diff.STE.pdR q (D.R j X a b) y) z = 0 := by
  refine st_pdR_eq_zero_of_eventuallyEq_zero ?_ p
  have hU : {y : Idx → ℝ | D.σ j < ‖y‖} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  filter_upwards [hU] with y hy
  exact st_pdR_R_eq_zero D X j a b hy q

/-- **The local residual is the lower-order part of the transport identity**, globally: the
difference `R_j(P h) - Σ A^{pq} ∂_p∂_q (R_j h)` with the coefficient `A` of `sharpCoeff` agrees with
`residualLow` everywhere (on the `2σ_j`-ball by the transport identity `Rres_eq_residualLow`, off the
`σ_j`-ball because both sides vanish there). -/
lemma st_Rres_eq_residualLow (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (A : Idx → Idx → (Idx → ℝ) → ℝ) (j : ι₀)
    (hAGf : ∀ (z : Idx → ℝ), ‖z‖ ≤ 2 * D.σ j → ∀ c d : Idx,
      A c d z = ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) c d)
    (a b : Idx) :
    (fun z : Idx → ℝ => Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
        (fun z p q => A p q z) z a b)
      = fun z : Idx → ℝ =>
          Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b := by
  funext z
  by_cases hz : ‖z‖ ≤ 2 * D.σ j
  · have hcongr : Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
          (fun z p q => A p q z) z a b
        = Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
          (fun z p q => ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q)
          z a b := by
      simp only [Work.Diff.STE.B3.Rres]
      congr 1
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [hAGf z hz p q]
    rw [hcongr]
    exact Work.Diff.STE.B3.Rres_eq_residualLow (I := I) (M := M) D hLC h hsym hpos hsmooth j hz a b
  · rw [not_le] at hz
    have hz' : D.σ j < ‖z‖ := by linarith [D.hσ j]
    show D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
        - (∑ p, ∑ q, A p q z * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z)
      = Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b
    rw [Work.Diff.STE.Lead.Gal.residualLow_eq_zero_of_sigma_lt_gal D h j hz' a b]
    have hRP : D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z = 0 := by
      by_cases h0 : D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z = 0
      · exact h0
      · exact absurd (Work.Diff.STE.Lead.Gal.support_R_subset_ball D
          (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) j a b (by
            simp only [Function.mem_support, Complex.ofReal_ne_zero]; exact h0)) (by
          rw [Metric.mem_ball, dist_zero_right]; exact not_lt.mpr (le_of_lt hz'))
    rw [hRP, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    rw [st_pdR_pdR_R_eq_zero D h j a b hz' p q]
    ring

theorem sharpTrans
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (hk : 1 ≤ k) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ (lam' CA CT : ℝ), 0 < lam' ∧ 0 ≤ CA ∧ 0 ≤ CT ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d r : Fin (Module.finrank ℝ E))
            (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
            |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K),
          ∀ j : ι₀,
          ∃ (A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
                (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
            (Th : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
                (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
            (∀ (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
              A c d z = A d c z) ∧
            (∀ (z : Fin (Module.finrank ℝ E) → ℝ)
              (ξ : Fin (Module.finrank ℝ E) → ℝ),
              lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d z * ξ c * ξ d) ∧
            (∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d)) ∧
            (∀ c d, Work.Diff.STE.Periodic1 (A c d)) ∧
            (∀ (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
              |A c d z| ≤ CA) ∧
            (∀ (z : Fin (Module.finrank ℝ E) → ℝ) (r c d : Fin (Module.finrank ℝ E)),
              |Work.Diff.STE.pdR r (fun y : Fin (Module.finrank ℝ E) → ℝ => A c d y) z|
                ≤ CA) ∧
            (∀ (m : ℕ), m ≤ k → ∀ (β : Fin m → Fin (Module.finrank ℝ E))
              (c d : Fin (Module.finrank ℝ E)),
              Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
                (fun y : Fin (Module.finrank ℝ E) → ℝ => ((A c d y : ℝ) : ℂ)))
                ≤ CA * (1 + D.ENormB m h)) ∧
            (∀ a b, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (Th a b)) ∧
            (∀ a b, Work.Diff.STE.Periodic1 (Th a b)) ∧
            (∀ (m : ℕ), m ≤ k → ∀ (β : Fin m → Fin (Module.finrank ℝ E))
              (a b : Fin (Module.finrank ℝ E)),
              Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β (Th a b))
                ≤ CT * (1 + D.ENormB (m + 1) h)) ∧
            (∀ (a b : Fin (Module.finrank ℝ E))
              (z : Fin (Module.finrank ℝ E) → ℝ),
              D.Rper j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
                = (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
                    * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z)
                  + Th a b z) := by
  intro lam K hlam hK
  obtain ⟨lam', CA, hlam'0, hCA0, hcoeff⟩ :=
    sharpCoeff (I := I) (M := M) D k hk lam K hlam hK
  obtain ⟨CT0, hCT00, hres⟩ := sharpResid (I := I) (M := M) D hLC k hk lam K hlam hK
  choose Cn hCn0 hCnE using fun m : ℕ => perEnergy (Module.finrank ℝ E) m
  set Csum : ℝ := ∑ m ∈ Finset.range (k + 1), (Cn m + 1) with hCsumdef
  have hCsum0 : 0 ≤ Csum := by
    rw [hCsumdef]
    exact Finset.sum_nonneg fun m _ => by linarith [hCn0 m]
  have hCnle : ∀ m : ℕ, m ≤ k → Cn m ≤ Csum := by
    intro m hm
    rw [hCsumdef]
    refine (le_add_of_nonneg_right zero_le_one).trans
      (Finset.single_le_sum (f := fun m => Cn m + 1) ?_ ?_)
    · intro i _
      linarith [hCn0 i]
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  set CT : ℝ := (Csum + 1) * (CT0 + 1) + 1 with hCTdef
  have hCTnn : 0 ≤ CT := by rw [hCTdef]; positivity
  refine ⟨lam', CA, CT, hlam'0, hCA0, hCTnn, ?_⟩
  intro h hsym hpos hsmooth hell hub hjet j
  by_cases hn : Module.finrank ℝ E = 0
  · -- the degenerate case: every index type is empty, so the interface is vacuous
    refine ⟨fun c => (hn ▸ c).elim0, fun a => (hn ▸ a).elim0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    · intro z c d; exact (hn ▸ c).elim0
    · intro z ξ; simp [hn]
    · intro c d; exact (hn ▸ c).elim0
    · intro c d; exact (hn ▸ c).elim0
    · intro z c d; exact (hn ▸ c).elim0
    · intro z r c d; exact (hn ▸ c).elim0
    · intro m hm β c d; exact (hn ▸ c).elim0
    · intro a b; exact (hn ▸ a).elim0
    · intro a b; exact (hn ▸ a).elim0
    · intro m hm β a b; exact (hn ▸ a).elim0
    · intro a b z; exact (hn ▸ a).elim0
  · have hnpos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hn
    obtain ⟨A, hAsym, hAell, hAsm, hAper, hAb, hAd, hAen, hAGf⟩ :=
      hcoeff h hsym hsmooth hell hub hjet j
    set P : Work.Diff.STE.Bil (I := I) (M := M) :=
      Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth with hPdef
    have hPcd : Work.Diff.STE.D.ChartData (I := I) (M := M) P := by
      rw [hPdef]
      exact Work.Diff.STE.B3.chartData_deTurckSec (I := I) (M := M) (g₀ := g₀) hLC h hsym hpos
        hsmooth
    -- the chart enlargement
    obtain ⟨δt, hδtpos, htgtj⟩ := Work.Diff.STE.Lead.Gal.gardTargetDelta (I := I) (M := M) D
    set δ : ℝ := min (δt / 2) (1 / 16) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδt : δ ≤ δt / 2 := min_le_left _ _
    have hδ16 : δ ≤ 1 / 16 := min_le_right _ _
    have hRle : 2 * D.σ j + δ ≤ 1 / 2 := by
      have := D.hσ2 j; linarith
    have hR0 : 0 ≤ D.σ j := le_of_lt (D.hσ j)
    have hσR : D.σ j ≤ 2 * D.σ j + δ := by linarith [D.hσ j, hδpos]
    -- global smoothness of the residual function `Rres` with our coefficient
    have hRres_sm : ∀ (a b : Fin (Module.finrank ℝ E)), ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
          (fun z p q => A p q z) z a b) := by
      intro a b
      have hPsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ => D.R j P a b z) :=
        Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D P hPcd j a b
      have hHsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ => D.R j h a b z) :=
        Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsmooth j a b
      have hpd : ∀ p q : Fin (Module.finrank ℝ E), ContDiff ℝ (⊤ : ℕ∞)
          (fun z : Fin (Module.finrank ℝ E) → ℝ => Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z) :=
        fun p q => Work.Diff.STE.B3.contDiff_pdR_top _
          (Work.Diff.STE.B3.contDiff_pdR_top _ hHsm q) p
      have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ∑ p, ∑ q, A p q z * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z) := by
        refine ContDiff.sum fun p _ => ContDiff.sum fun q _ => ?_
        exact (hAsm p q).mul (hpd p q)
      exact hPsm.sub hsum
    -- `Rres` with our coefficient is `residualLow`
    have hRres_eq : ∀ (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
          (fun z p q => A p q z) z a b
          = Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b :=
      fun a b z => congrFun (st_Rres_eq_residualLow D hLC h hsym hpos hsmooth A j hAGf a b) z
    refine ⟨A, fun a b z => D.Rper j P a b z - (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
        * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z),
      hAsym, hAell, hAsm, hAper, hAb, hAd, hAen, ?_, ?_, ?_, ?_⟩
    · -- smoothness of `Th`
      intro a b
      exact ((Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D P hPcd j a b).1).sub
        (ContDiff.sum fun c _ => ContDiff.sum fun d _ =>
          (Complex.ofRealCLM.contDiff.comp (hAsm c d)).mul
            (Work.Diff.STE.Lead.Gal.contDiff_pd_pd
              (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D h hsmooth j a b).1
              d c))
    · -- periodicity of `Th`
      intro a b
      refine Work.Diff.STE.Lead.Gal.periodic1_sub_rj
        (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D P hPcd j a b).2 ?_
      refine Work.Diff.STE.Lead.Gal.periodic1_sum Finset.univ _ fun c _ =>
        Work.Diff.STE.Lead.Gal.periodic1_sum Finset.univ _ fun d _ => ?_
      refine Work.Diff.STE.Lead.Gal.periodic1_mul
        (Work.Diff.STE.Lead.Gal.periodic1_ofReal (hAper c d)) ?_
      exact Work.Diff.STE.Lead.Gal.periodic1_pd_ga
        (Work.Diff.STE.Lead.Gal.periodic1_pd_ga
          (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D h hsmooth j a b).2
          (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D h hsmooth j a b).1 d)
        (Work.Diff.STE.contDiff_pd_of_contDiff_top (i := d)
          (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D h hsmooth j a b).1) c
    · -- the `L²` bound for `Th`
      intro m hm β a b
      set F : (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun z => ((Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym
        hpos hsmooth j (fun z p q => A p q z) z a b : ℝ) : ℂ) with hFdef
      have hFsm : ContDiff ℝ (⊤ : ℕ∞) F :=
        Complex.ofRealCLM.contDiff.comp (hRres_sm a b)
      have hRnz : ∀ z : Fin (Module.finrank ℝ E) → ℝ, D.σ j < ‖z‖ →
          Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
            (fun z p q => A p q z) z a b = 0 := by
        intro z hz
        rw [hRres_eq a b z]
        exact Work.Diff.STE.Lead.Gal.residualLow_eq_zero_of_sigma_lt_gal D h j hz a b
      have hFsupp : Function.support F ⊆ Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ) := by
        intro z hz
        have hR0' : Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
            (fun z p q => A p q z) z a b ≠ 0 := by
          intro h0
          exact hz (by simp [hFdef, h0])
        have hle : ‖z‖ ≤ D.σ j := by
          by_contra hlt
          rw [not_le] at hlt
          exact hR0' (hRnz z hlt)
        rw [Metric.mem_ball, dist_zero_right]
        linarith [D.hσ j, hδpos]
      have hFcube : Function.support F ⊆
          Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
        intro z hz
        have hR0' : Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
            (fun z p q => A p q z) z a b ≠ 0 := by
          intro h0
          exact hz (by simp [hFdef, h0])
        have h1 : ‖z‖ ≤ D.σ j := by
          by_contra hlt
          rw [not_le] at hlt
          exact hR0' (hRnz z hlt)
        rw [Set.mem_pi]
        intro i _
        have h2 : |z i| ≤ ‖z‖ := by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
        have h5 : ‖z‖ ≤ 1 / 8 := by have := D.hσ2 j; linarith
        have h4 : |z i| < 1 / 2 := by linarith
        rw [Set.mem_Ioo]
        exact abs_lt.mp h4
      -- the periodisation of `F` is `Th a b`
      have hThto : (fun z : Fin (Module.finrank ℝ E) → ℝ => D.Rper j P a b z - (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
          * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z))
          = fun z : Fin (Module.finrank ℝ E) → ℝ => ∑' k : Fin (Module.finrank ℝ E) → ℤ, F (z + Work.Diff.STE.iVec k) := by
        have hLper : Work.Diff.STE.Periodic1 (fun z : Fin (Module.finrank ℝ E) → ℝ => D.Rper j P a b z
            - (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
                * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z)) := by
          refine Work.Diff.STE.Lead.Gal.periodic1_sub_rj
            (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D P hPcd j a b).2 ?_
          refine Work.Diff.STE.Lead.Gal.periodic1_sum Finset.univ _ fun c _ =>
            Work.Diff.STE.Lead.Gal.periodic1_sum Finset.univ _ fun d _ => ?_
          refine Work.Diff.STE.Lead.Gal.periodic1_mul
            (Work.Diff.STE.Lead.Gal.periodic1_ofReal (hAper c d)) ?_
          exact Work.Diff.STE.Lead.Gal.periodic1_pd_ga
            (Work.Diff.STE.Lead.Gal.periodic1_pd_ga
              (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D h hsmooth j a b).2
              (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D h hsmooth j a b).1 d)
            (Work.Diff.STE.contDiff_pd_of_contDiff_top (i := d)
              (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D h hsmooth j a b).1) c
        have hLsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ => D.Rper j P a b z
            - (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
                * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z)) :=
          ((Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D P hPcd j a b).1).sub
            (ContDiff.sum fun c _ => ContDiff.sum fun d _ =>
              (Complex.ofRealCLM.contDiff.comp (hAsm c d)).mul
                (Work.Diff.STE.Lead.Gal.contDiff_pd_pd
                  (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData D h hsmooth j a b).1
                  d c))
        have hRper' : Work.Diff.STE.Periodic1
            (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑' k : Fin (Module.finrank ℝ E) → ℤ, F (z + Work.Diff.STE.iVec k)) :=
          Work.Diff.STE.periodization_periodic F
        have hRsm : ContDiff ℝ (⊤ : ℕ∞)
            (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑' k : Fin (Module.finrank ℝ E) → ℤ, F (z + Work.Diff.STE.iVec k)) :=
          (Work.Diff.STE.periodization_contDiff_periodic F hFsm hFcube).1
        refine Work.Diff.STE.Lead.GalTame.periodic_eq_of_eqOn_openCube hLper hRper'
          hLsm.continuous hRsm.continuous ?_
        intro z hz
        have h1 : D.Rper j P a b z = ((D.R j P a b z : ℝ) : ℂ) := D.Rper_eq_R j P a b hz
        have h3 : (∑' k : Fin (Module.finrank ℝ E) → ℤ, F (z + Work.Diff.STE.iVec k)) = F z :=
          Work.Diff.STE.periodization_eq_self hFcube hz
        have hFz : F z = ((Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
            (fun z p q => A p q z) z a b : ℝ) : ℂ) := rfl
        rw [h1, h3, hFz]
        have hsum : (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
              * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z)
            = (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
              * ((Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.R j h a b)) z : ℝ) : ℂ)) := by
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
          rw [st_pd_pd_Rper D h j a b hz c d]
        rw [hsum]
        have hcast : (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
              * ((Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.R j h a b)) z : ℝ) : ℂ))
            = ((∑ c, ∑ d, A c d z
              * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.R j h a b)) z : ℝ) : ℂ) := by
          push_cast
          rfl
        rw [hcast]
        have hRresdef : Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
            (fun z p q => A p q z) z a b
            = D.R j P a b z - ∑ c, ∑ d, A c d z
                * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.R j h a b)) z := rfl
        rw [hRresdef, Complex.ofReal_sub]
      change Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        D.Rper j P a b z - (∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
          * Work.Diff.STE.pd c (Work.Diff.STE.pd d (D.Rper j h a b)) z)))
        ≤ CT * (1 + D.ENormB (m + 1) h)
      rw [hThto]
      -- apply the periodisation energy bound and the tame residual bound
      have h1 := hCnE m F (2 * D.σ j + δ) hFsm hFsupp hRle β
      refine h1.trans ?_
      have hvan : ∀ z : Fin (Module.finrank ℝ E) → ℝ, D.σ j < ‖z‖ → F z = 0 := by
        intro z hz
        have h5 : Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
            (fun z p q => A p q z) z a b = 0 := hRnz z hz
        simp only [hFdef, h5, Complex.ofReal_zero]
      have hball := ballIntegralEq (n := Module.finrank ℝ E) hnpos m F (D.σ j) (2 * D.σ j + δ)
        hR0 hσR hFsm hvan β
      have hresb := hres h hsym hpos hsmooth hell hub hjet j a b m hm β
      have hFeq : (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b : ℝ) : ℂ)) = F := by
        funext z
        simp only [hFdef]
        rw [hRres_eq a b z]
      rw [hFeq] at hresb
      have hmb : ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
          ‖Work.Diff.STE.pdVec m β F z‖ ^ 2
          ≤ CT0 * (1 + D.ENormB (m + 1) h) := by
        rw [hball]
        exact hresb
      have h2 : (∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
          ‖Work.Diff.STE.pdVec m β F z‖ ^ 2) ≤ CT0 * (1 + D.ENormB (m + 1) h) := hmb
      refine (mul_le_mul_of_nonneg_left h2 (hCn0 m)).trans ?_
      have hE0 : 0 ≤ D.ENormB (m + 1) h := by
        rw [Work.Diff.STE.B3Data.ENormB]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun a _ =>
          Finset.sum_nonneg fun b _ => by
            rw [Work.Diff.STE.ENormSq]
            exact Finset.sum_nonneg fun l _ => integral_nonneg fun x => by positivity
      have hCTbig : Cn m * CT0 ≤ CT := by
        have h1 : Cn m * CT0 ≤ (Csum + 1) * (CT0 + 1) :=
          mul_le_mul (le_trans (hCnle m hm) (le_add_of_nonneg_right zero_le_one))
            (le_add_of_nonneg_right zero_le_one) hCT00 (by linarith [hCsum0])
        rw [hCTdef]; linarith
      have h3 : Cn m * (CT0 * (1 + D.ENormB (m + 1) h)) ≤ CT * (1 + D.ENormB (m + 1) h) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hCTbig (by linarith)
      exact h3
    · -- the transport identity, by definition of `Th`
      intro a b z
      ring

end

end Work.Diff.STE.Lead.GalTame
