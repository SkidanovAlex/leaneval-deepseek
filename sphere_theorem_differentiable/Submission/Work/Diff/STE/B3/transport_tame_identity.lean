import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.transport_tame_leibniz
import Submission.Work.Diff.STE.deTurck.pPhi_decomp
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.B3.chartJet_symm_tame
import Submission.Work.Diff.STE.B3.transport_jet_data
import Submission.Work.Diff.STE.B3.secOp_weight_sum_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The **transport identity** (reduced form): given the principal-part lemma `hSec`, the
identification `hGam` of the clamped inverse with the honest inverse of the coordinate chart matrix
on the `2σ`-ball, and the matching `hNom` of the nominal objects with the honest chart data, the
localised component of the DeTurck operator is the second-order operator `γ ∂∂` applied to the
localised component of `h`, plus the explicit residual `tmPsi`. -/
theorem transport_identity
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (af bf : Fin (Module.finrank ℝ E))
    (cl ch : ℝ) (hcl : 0 < cl) (hch : cl < ch)
    (hSec : ∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j →
      ∀ c d : Fin (Module.finrank ℝ E),
      (∑ i, ∑ k, Ff (I := I) (M := M) D j z af i
          * (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
              (yf (I := I) (M := M) D j z)).2.2
              (Work.Diff.EXT.bB (E := E) c) (Work.Diff.EXT.bB (E := E) d) i k
          * Ff (I := I) (M := M) D j z bf k)
        = Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
            (fun w => Mf (I := I) (M := M) D h j w af bf)) z
          - eightTerm (I := I) (M := M) D h j z c d af bf)
    (hGam : ∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j →
      ∀ c d : Fin (Module.finrank ℝ E),
      tmGKi (I := I) (M := M) D j cl ch hcl hch z (fun p q => D.mat j h p q z) c d
        = ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) c d)
    (hNom : ∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j →
      (Matrix.of (tmGK (I := I) (M := M) D j z (fun a b => D.mat j h a b z))
          = Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))
      ∧ (tmDGKclm (I := I) (M := M) D j z (fun a b => D.mat j h a b z)
            (fun a b r => Work.Diff.STE.pdR r (D.mat j h a b) z)
          = (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
              (yf (I := I) (M := M) D j z)).2.1)
      ∧ (∀ c d : Fin (Module.finrank ℝ E),
          tmEight (I := I) (M := M) D j z (fun a b => D.mat j h a b z)
              (fun a b r => Work.Diff.STE.pdR r (D.mat j h a b) z) c d af bf
            = eightTerm (I := I) (M := M) D h j z c d af bf)) :
    ∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j →
      D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) af bf z
        = (∑ p, ∑ q, tmGKi (I := I) (M := M) D j cl ch hcl hch z (fun p q => D.mat j h p q z) p q
            * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h af bf)) z)
          + tmPsi (I := I) (M := M) D j cl ch hcl hch z (fun c d => D.mat j h c d z)
              (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z) af bf := by
  intro z hz
  -- ## 1. The bridge and the jet decomposition
  have hbr := bridge (I := I) (M := M) hLC h hsym hpos hsmooth D j af bf hz
  rw [hbr]
  obtain ⟨hA, hL, hB1, hB2, hdet⟩ :=
    chartJet_symm_tame (I := I) (M := M) D h hsym hpos hsmooth j z hz
  have hdec : ∀ i k : Fin (Module.finrank ℝ E),
      Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h (D.x₀ j)
          (yf (I := I) (M := M) D j z) i k
        = Work.Diff.STE.DeTurck.secOp
            ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
              (yf (I := I) (M := M) D j z)).1)
            ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
              (yf (I := I) (M := M) D j z)).2.2) i k
          + Work.Diff.STE.DeTurck.pN
              ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
                (yf (I := I) (M := M) D j z)).1)
              ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
                (yf (I := I) (M := M) D j z)).2.1)
              ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
                (yf (I := I) (M := M) D j z)).2.2)
              ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
                (yf (I := I) (M := M) D j z)).1)
              ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
                (yf (I := I) (M := M) D j z)).2.1) i k := by
    intro i k
    have hpd := Work.Diff.STE.deTurck.pPhi_decomp
      ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
        (yf (I := I) (M := M) D j z)).1)
      ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
        (yf (I := I) (M := M) D j z)).2.1)
      ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
        (yf (I := I) (M := M) D j z)).2.2)
      ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
        (yf (I := I) (M := M) D j z)).1)
      ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
        (yf (I := I) (M := M) D j z)).2.1)
      ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
        (yf (I := I) (M := M) D j z)).2.2) hA hL hB1 hB2 hdet
    rw [Work.Diff.STE.D.pPhiJetOf_apply]
    exact congrFun (congrFun hpd i) k
  simp only [hdec]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [mul_add]
  -- ## 2. The principal part and the second-order Leibniz rule
  obtain ⟨hSW1, hSW2⟩ := secOp_weight_sum_eq (I := I) (M := M) D hLC h hsym hpos hsmooth j
    af bf z hz (fun c d => hSec z hz c d)
  -- the two halves of `secOp_weight_sum_eq`, re-typed in terms of `D.mat` rather than `Mf`
  have hSW1' : (∑ i, ∑ k, Work.Diff.STE.DeTurck.secOp
        ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (yf (I := I) (M := M) D j z)).1)
        ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (yf (I := I) (M := M) D j z)).2.2) i k
      * (Ff (I := I) (M := M) D j z af i * Ff (I := I) (M := M) D j z bf k))
      = ∑ c, ∑ d, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) c d
          * (Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.mat j h af bf)) z
            - eightTerm (I := I) (M := M) D h j z c d af bf) := hSW1
  have hSW2' : ∀ c d : Fin (Module.finrank ℝ E),
      wf (I := I) (M := M) D j z
          * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.mat j h af bf)) z
        = Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.R j h af bf)) z
          - (Work.Diff.STE.pdR c (wf (I := I) (M := M) D j) z
              * Work.Diff.STE.pdR d (D.mat j h af bf) z
            + Work.Diff.STE.pdR d (wf (I := I) (M := M) D j) z
              * Work.Diff.STE.pdR c (D.mat j h af bf) z
            + Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (wf (I := I) (M := M) D j)) z
              * D.mat j h af bf z) := hSW2
  rw [hSW1']
  -- ## 3. Pushing `wf` inside the double sum and applying the Leibniz rule
  have hSA : wf (I := I) (M := M) D j z
        * (∑ c, ∑ d, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) c d
            * (Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.mat j h af bf)) z
              - eightTerm (I := I) (M := M) D h j z c d af bf))
      = (∑ p, ∑ q, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
            * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h af bf)) z)
        - (∑ p, ∑ q, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
            * (Work.Diff.STE.pdR p (wf (I := I) (M := M) D j) z
                * Work.Diff.STE.pdR q (D.mat j h af bf) z
              + Work.Diff.STE.pdR q (wf (I := I) (M := M) D j) z
                * Work.Diff.STE.pdR p (D.mat j h af bf) z
              + Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (wf (I := I) (M := M) D j)) z
                * D.mat j h af bf z))
        - wf (I := I) (M := M) D j z
          * (∑ p, ∑ q, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
              * eightTerm (I := I) (M := M) D h j z p q af bf) := by
    have h1 : ∀ p q : Fin (Module.finrank ℝ E),
        wf (I := I) (M := M) D j z
          * (((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
            * (Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.mat j h af bf)) z
              - eightTerm (I := I) (M := M) D h j z p q af bf))
        = ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
            * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h af bf)) z
          - ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
            * (Work.Diff.STE.pdR p (wf (I := I) (M := M) D j) z
                * Work.Diff.STE.pdR q (D.mat j h af bf) z
              + Work.Diff.STE.pdR q (wf (I := I) (M := M) D j) z
                * Work.Diff.STE.pdR p (D.mat j h af bf) z
              + Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (wf (I := I) (M := M) D j)) z
                * D.mat j h af bf z)
          - ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
            * (wf (I := I) (M := M) D j z
                * eightTerm (I := I) (M := M) D h j z p q af bf) := by
      intro p q
      have hL : wf (I := I) (M := M) D j z
            * (((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
              * (Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.mat j h af bf)) z
                - eightTerm (I := I) (M := M) D h j z p q af bf))
          = ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
              * (wf (I := I) (M := M) D j z
                  * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.mat j h af bf)) z)
            - ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
              * (wf (I := I) (M := M) D j z
                  * eightTerm (I := I) (M := M) D h j z p q af bf) := by ring
      rw [hL, hSW2' p q]
      ring
    calc wf (I := I) (M := M) D j z
          * (∑ c, ∑ d, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) c d
              * (Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.mat j h af bf)) z
                - eightTerm (I := I) (M := M) D h j z c d af bf))
        = (∑ c, ∑ d, wf (I := I) (M := M) D j z
              * (((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) c d
                * (Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.mat j h af bf)) z
                  - eightTerm (I := I) (M := M) D h j z c d af bf))) := by
            simp only [Finset.mul_sum]
      _ = (∑ c, ∑ d, (((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) c d
              * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (D.R j h af bf)) z
            - ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) c d
              * (Work.Diff.STE.pdR c (wf (I := I) (M := M) D j) z
                  * Work.Diff.STE.pdR d (D.mat j h af bf) z
                + Work.Diff.STE.pdR d (wf (I := I) (M := M) D j) z
                  * Work.Diff.STE.pdR c (D.mat j h af bf) z
                + Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (wf (I := I) (M := M) D j)) z
                  * D.mat j h af bf z)
            - ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) c d
              * (wf (I := I) (M := M) D j z
                  * eightTerm (I := I) (M := M) D h j z c d af bf))) :=
            Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => h1 c d))
      _ = ((∑ p, ∑ q, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
              * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h af bf)) z)
            - (∑ p, ∑ q, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
              * (Work.Diff.STE.pdR p (wf (I := I) (M := M) D j) z
                  * Work.Diff.STE.pdR q (D.mat j h af bf) z
                + Work.Diff.STE.pdR q (wf (I := I) (M := M) D j) z
                  * Work.Diff.STE.pdR p (D.mat j h af bf) z
                + Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (wf (I := I) (M := M) D j)) z
                  * D.mat j h af bf z))
            - wf (I := I) (M := M) D j z
              * (∑ p, ∑ q, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
                  * eightTerm (I := I) (M := M) D h j z p q af bf)) := by
            simp only [Finset.sum_sub_distrib]
            rw [show (∑ p, ∑ q, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
                  * (wf (I := I) (M := M) D j z
                      * eightTerm (I := I) (M := M) D h j z p q af bf))
                = wf (I := I) (M := M) D j z
                  * (∑ p, ∑ q,
                      ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
                      * eightTerm (I := I) (M := M) D h j z p q af bf) from by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun p _ => ?_)
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun q _ => by ring)]
  rw [hSA]
  -- ## 4. The lower-order `pN` sum, in the shape used by `tmPsi`
  have hNomD : tmDGKclm (I := I) (M := M) D j z (fun a b => D.mat j h a b z)
        (fun a b r => Work.Diff.STE.pdR r (D.mat j h a b) z)
      = (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (yf (I := I) (M := M) D j z)).2.1 := (hNom z hz).2.1
  have hNomE : ∀ c d : Fin (Module.finrank ℝ E),
      tmEight (I := I) (M := M) D j z (fun a b => D.mat j h a b z)
          (fun a b r => Work.Diff.STE.pdR r (D.mat j h a b) z) c d af bf
        = eightTerm (I := I) (M := M) D h j z c d af bf := fun c d => (hNom z hz).2.2 c d
  have hNomGK : Matrix.of (tmGK (I := I) (M := M) D j z (fun a b => D.mat j h a b z))
      = Matrix.of (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (yf (I := I) (M := M) D j z)).1 := by
    have hjet1 : (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
        (yf (I := I) (M := M) D j z)).1 = Gf (I := I) (M := M) D h j z := by
      funext i k
      exact (transport_jet_data (I := I) (M := M) D h hsmooth j hz).1 i k
    rw [hjet1]
    exact (hNom z hz).1
  have hNomGKi : ∀ c d : Fin (Module.finrank ℝ E),
      tmGKi (I := I) (M := M) D j cl ch hcl hch z (fun a b => D.mat j h a b z) c d
        = ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) c d :=
    fun c d => hGam z hz c d
  -- the `pN` sum appearing in the goal, in the order of `tmPsi`
  have hSB : (∑ i, ∑ k, (Work.Diff.STE.DeTurck.pN
        ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
          (yf (I := I) (M := M) D j z)).1)
        ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
          (yf (I := I) (M := M) D j z)).2.1)
        ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
          (yf (I := I) (M := M) D j z)).2.2)
        ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (yf (I := I) (M := M) D j z)).1)
        ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (yf (I := I) (M := M) D j z)).2.1) i k)
      * (Ff (I := I) (M := M) D j z af i * Ff (I := I) (M := M) D j z bf k))
      = ∑ i, ∑ k, Ff (I := I) (M := M) D j z af i * Ff (I := I) (M := M) D j z bf k
          * (Work.Diff.STE.DeTurck.pN
              ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
                (yf (I := I) (M := M) D j z)).1)
              ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
                (yf (I := I) (M := M) D j z)).2.1)
              ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
                (yf (I := I) (M := M) D j z)).2.2)
              (Matrix.of (tmGK (I := I) (M := M) D j z (fun a b => D.mat j h a b z)))
              (tmDGKclm (I := I) (M := M) D j z (fun a b => D.mat j h a b z)
                (fun a b r => Work.Diff.STE.pdR r (D.mat j h a b) z)) i k) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hNomGK, hNomD]
    change Work.Diff.STE.DeTurck.pN
        ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
          (yf (I := I) (M := M) D j z)).1)
        ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
          (yf (I := I) (M := M) D j z)).2.1)
        ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
          (yf (I := I) (M := M) D j z)).2.2)
        ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (yf (I := I) (M := M) D j z)).1)
        ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (yf (I := I) (M := M) D j z)).2.1) i k
      * (Ff (I := I) (M := M) D j z af i * Ff (I := I) (M := M) D j z bf k)
      = Ff (I := I) (M := M) D j z af i * Ff (I := I) (M := M) D j z bf k
        * (Work.Diff.STE.DeTurck.pN
            ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
              (yf (I := I) (M := M) D j z)).1)
            ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
              (yf (I := I) (M := M) D j z)).2.1)
            ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
              (yf (I := I) (M := M) D j z)).2.2)
            ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
              (yf (I := I) (M := M) D j z)).1)
            ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
              (yf (I := I) (M := M) D j z)).2.1) i k)
    ring
  rw [hSB]
  -- ## 5. The residual, expanded
  have hSC : tmPsi (I := I) (M := M) D j cl ch hcl hch z (fun a b => D.mat j h a b z)
        (fun a b r => Work.Diff.STE.pdR r (D.mat j h a b) z) af bf
      = - (∑ p, ∑ q, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
            * (Work.Diff.STE.pdR p (wf (I := I) (M := M) D j) z
                * Work.Diff.STE.pdR q (D.mat j h af bf) z
              + Work.Diff.STE.pdR q (wf (I := I) (M := M) D j) z
                * Work.Diff.STE.pdR p (D.mat j h af bf) z
              + Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (wf (I := I) (M := M) D j)) z
                * D.mat j h af bf z))
        - wf (I := I) (M := M) D j z
          * (∑ p, ∑ q, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
              * eightTerm (I := I) (M := M) D h j z p q af bf)
        + wf (I := I) (M := M) D j z
          * (∑ i, ∑ k, Ff (I := I) (M := M) D j z af i * Ff (I := I) (M := M) D j z bf k
              * (Work.Diff.STE.DeTurck.pN
                  ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
                    (yf (I := I) (M := M) D j z)).1)
                  ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
                    (yf (I := I) (M := M) D j z)).2.1)
                  ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
                    (yf (I := I) (M := M) D j z)).2.2)
                  (Matrix.of (tmGK (I := I) (M := M) D j z (fun a b => D.mat j h a b z)))
                  (tmDGKclm (I := I) (M := M) D j z (fun a b => D.mat j h a b z)
                    (fun a b r => Work.Diff.STE.pdR r (D.mat j h a b) z)) i k)) := by
    simp only [tmPsi, hNomE, hNomGKi]
  rw [hSC]
  -- ## 6. The coefficient matrix on the ball
  have hSD : (∑ p, ∑ q, tmGKi (I := I) (M := M) D j cl ch hcl hch z
          (fun p q => D.mat j h p q z) p q
        * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h af bf)) z)
      = (∑ p, ∑ q, ((Matrix.of (fun i k => Gf (I := I) (M := M) D h j z i k))⁻¹) p q
          * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h af bf)) z) := by
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [hNomGKi p q]
  rw [hSD]
  ring

end Work.Diff.STE.B3
