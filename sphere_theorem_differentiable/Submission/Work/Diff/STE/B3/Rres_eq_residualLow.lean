import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.deTurck.pPhi_decomp
import Submission.Work.Diff.STE.D.psi.secChartVal_eq_deTurckOp
import Submission.Work.Diff.STE.B3.transport_jet_data
import Submission.Work.Diff.STE.B3.transport_Mf_second
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.D.psi.chartMatOf_pd_det_pos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. The algebraic bookkeeping of the double sums

The residual identity is, after the transport lemmas, a purely algebraic rearrangement of five
double sums.  The four lemmas below perform it:

* `sum2_split`, `sum3_split`: splitting a double sum of a `2`- resp. `3`-term sum;
* `sum_factor`: pulling a constant out of a double sum;
* `swap2`: the combination `Σ_{pq} A^{pq}(M_q W_p + M_p W_q) = Σ_{pq} A^{pq}·2 W_p M_q` for a
  symmetric weight `A` (this is where the symmetry `(Gf⁻¹)ᵀ = Gf⁻¹` is used);
* `swapSum`: the exchange of the `(i,k)`- and `(p,q)`-summations,
  `Σ_{ik}(Σ_{pq}A^{pq} G^{pq}_{ik}) f_{ik} = Σ_{pq}A^{pq}(Σ_{ik}G^{pq}_{ik} f_{ik})`.

`Rres_algebra` is then the abstract identity from which the target follows by instantiation. -/

private lemma sum2_split {n : ℕ} (F G : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, (F p q + G p q)) = (∑ p, ∑ q, F p q) + (∑ p, ∑ q, G p q) := by
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_add_distrib), Finset.sum_add_distrib]

private lemma sum3_split {n : ℕ} (F G H : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, (F p q + G p q + H p q))
      = (∑ p, ∑ q, F p q) + (∑ p, ∑ q, G p q) + (∑ p, ∑ q, H p q) := by
  calc ∑ p, ∑ q, (F p q + G p q + H p q)
      = ∑ p, ((∑ q, F p q) + (∑ q, G p q) + (∑ q, H p q)) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

private lemma sum_factor {n : ℕ} (c : ℝ) (X : Fin n → Fin n → ℝ) :
    (∑ p, ∑ q, c * X p q) = c * (∑ p, ∑ q, X p q) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]

private lemma swap2 {n : ℕ} (A : Fin n → Fin n → ℝ) (hA : ∀ p q, A p q = A q p)
    (u v : Fin n → ℝ) :
    (∑ p, ∑ q, A p q * (u q * v p + u p * v q)) = ∑ p, ∑ q, A p q * (2 * v p * u q) := by
  have h1 : (∑ p, ∑ q, A p q * (u q * v p)) = ∑ p, ∑ q, A p q * (u p * v q) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_))
    rw [hA p q]
  have hsplit : (∑ p, ∑ q, A p q * (u q * v p + u p * v q))
      = (∑ p, ∑ q, A p q * (u q * v p)) + (∑ p, ∑ q, A p q * (u p * v q)) := by
    calc ∑ p, ∑ q, A p q * (u q * v p + u p * v q)
        = ∑ p, ∑ q, (A p q * (u q * v p) + A p q * (u p * v q)) := by
          refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => by ring))
      _ = ∑ p, ((∑ q, A p q * (u q * v p)) + (∑ q, A p q * (u p * v q))) :=
          Finset.sum_congr rfl (fun p _ => Finset.sum_add_distrib)
      _ = _ := Finset.sum_add_distrib
  have hS2 : (∑ p, ∑ q, A p q * (2 * v p * u q)) = 2 * (∑ p, ∑ q, A p q * (u q * v p)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => by ring)
  rw [hsplit, hS2, h1]
  ring

private lemma swapSum {n : ℕ} (A : Fin n → Fin n → ℝ)
    (G : Fin n → Fin n → Fin n → Fin n → ℝ) (f : Fin n → Fin n → ℝ) :
    (∑ i, ∑ k, (∑ p, ∑ q, A p q * G p q i k) * f i k)
      = ∑ p, ∑ q, A p q * (∑ i, ∑ k, G p q i k * f i k) := by
  have h1 : ∀ i k, (∑ p, ∑ q, A p q * G p q i k) * f i k
      = ∑ p, ∑ q, A p q * (G p q i k * f i k) := by
    intro i k
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q _ => by ring)
  simp only [h1]
  have e1 : (∑ i, ∑ k, ∑ p, ∑ q, A p q * (G p q i k * f i k))
      = ∑ i, ∑ p, ∑ k, ∑ q, A p q * (G p q i k * f i k) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
  have e2 : (∑ i, ∑ p, ∑ k, ∑ q, A p q * (G p q i k * f i k))
      = ∑ p, ∑ i, ∑ k, ∑ q, A p q * (G p q i k * f i k) := Finset.sum_comm
  have e3 : (∑ p, ∑ i, ∑ k, ∑ q, A p q * (G p q i k * f i k))
      = ∑ p, ∑ i, ∑ q, ∑ k, A p q * (G p q i k * f i k) :=
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
  have e4 : (∑ p, ∑ i, ∑ q, ∑ k, A p q * (G p q i k * f i k))
      = ∑ p, ∑ q, ∑ i, ∑ k, A p q * (G p q i k * f i k) :=
    Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
  rw [e1, e2, e3, e4]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]

/-- **The algebraic core of `Rres = residualLow`.**  With a symmetric weight `A`, a scalar `W`, a
scalar `M`, the derivative families `DW`, `DM`, `DDW`, the second jet `G` of the chart matrix and a
family `ff`, the combination

`W·Σ_{ik}(PN_{ik} + Σ_{pq}A^{pq}G^{pq}_{ik})·ff_{ik}
    - Σ_{pq}A^{pq}(W·(E_{pq} + Σ_{ik}G^{pq}_{ik}ff_{ik}) + DM_q DW_p + DM_p DW_q + M·DDW_{pq})`

equals `W·Σ_{ik}PN_{ik}ff_{ik} - W·Σ_{pq}A^{pq}E_{pq} - Σ_{pq}A^{pq}(2 DW_p DM_q + M·DDW_{pq})`: the
`Σ_{pq}A^{pq}Σ_{ik}G^{pq}_{ik}ff_{ik}` produced by the first term cancels the one inside the second,
and the symmetric combination `DM_q DW_p + DM_p DW_q` becomes `2 DW_p DM_q`. -/
private lemma Rres_algebra {n : ℕ} (A : Fin n → Fin n → ℝ) (hAsym : ∀ p q, A p q = A q p)
    (W M : ℝ) (DW DM : Fin n → ℝ) (DDW : Fin n → Fin n → ℝ)
    (G : Fin n → Fin n → Fin n → Fin n → ℝ) (ff : Fin n → Fin n → ℝ)
    (PN E : Fin n → Fin n → ℝ) :
    W * (∑ i, ∑ k, ((∑ p, ∑ q, A p q * G p q i k) + PN i k) * ff i k)
      - (∑ p, ∑ q, A p q * (W * (E p q + ∑ i, ∑ k, G p q i k * ff i k)
            + DM q * DW p + DM p * DW q + M * DDW p q))
    = W * (∑ i, ∑ k, PN i k * ff i k) - W * (∑ p, ∑ q, A p q * E p q)
      - ∑ p, ∑ q, A p q * (2 * DW p * DM q + M * DDW p q) := by
  have hsp1 : (∑ i, ∑ k, ((∑ p, ∑ q, A p q * G p q i k) + PN i k) * ff i k)
      = (∑ i, ∑ k, PN i k * ff i k) + (∑ i, ∑ k, (∑ p, ∑ q, A p q * G p q i k) * ff i k) := by
    have hpt : ∀ i k, ((∑ p, ∑ q, A p q * G p q i k) + PN i k) * ff i k
        = PN i k * ff i k + (∑ p, ∑ q, A p q * G p q i k) * ff i k := by
      intro i k; ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => hpt i k))]
    exact sum2_split _ _
  have hsw := swapSum A G ff
  have hsp2 : (∑ p, ∑ q, A p q * (W * (E p q + ∑ i, ∑ k, G p q i k * ff i k)
        + DM q * DW p + DM p * DW q + M * DDW p q))
      = W * (∑ p, ∑ q, A p q * (E p q + ∑ i, ∑ k, G p q i k * ff i k))
        + (∑ p, ∑ q, A p q * (DM q * DW p + DM p * DW q))
        + (∑ p, ∑ q, A p q * (M * DDW p q)) := by
    have hpt : ∀ p q, A p q * (W * (E p q + ∑ i, ∑ k, G p q i k * ff i k)
          + DM q * DW p + DM p * DW q + M * DDW p q)
        = W * (A p q * (E p q + ∑ i, ∑ k, G p q i k * ff i k))
          + A p q * (DM q * DW p + DM p * DW q) + A p q * (M * DDW p q) := by
      intro p q; ring
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
    rw [sum3_split (fun p q => W * (A p q * (E p q + ∑ i, ∑ k, G p q i k * ff i k)))
          (fun p q => A p q * (DM q * DW p + DM p * DW q))
          (fun p q => A p q * (M * DDW p q))]
    rw [sum_factor W (fun p q => A p q * (E p q + ∑ i, ∑ k, G p q i k * ff i k))]
  have hsp2b : (∑ p, ∑ q, A p q * (E p q + ∑ i, ∑ k, G p q i k * ff i k))
      = (∑ p, ∑ q, A p q * E p q)
        + (∑ p, ∑ q, A p q * (∑ i, ∑ k, G p q i k * ff i k)) := by
    have hpt : ∀ p q, A p q * (E p q + ∑ i, ∑ k, G p q i k * ff i k)
        = A p q * E p q + A p q * (∑ i, ∑ k, G p q i k * ff i k) := by
      intro p q; ring
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
    exact sum2_split _ _
  have hmid : (∑ p, ∑ q, A p q * (DM q * DW p + DM p * DW q))
      = ∑ p, ∑ q, A p q * (2 * DW p * DM q) := swap2 A hAsym DM DW
  have hsp3 : (∑ p, ∑ q, A p q * (2 * DW p * DM q + M * DDW p q))
      = (∑ p, ∑ q, A p q * (2 * DW p * DM q))
        + (∑ p, ∑ q, A p q * (M * DDW p q)) := by
    have hpt : ∀ p q, A p q * (2 * DW p * DM q + M * DDW p q)
        = A p q * (2 * DW p * DM q) + A p q * (M * DDW p q) := by
      intro p q; ring
    rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
    exact sum2_split _ _
  rw [hsp1, hsp2, hsp2b, hmid, hsp3, hsw]
  ring

/-! ## 2. The proof of the residual identity -/

/-- **The residual identity.**  The symmetry hypotheses of `Work.Diff.STE.deTurck.pPhi_decomp` are
discharged by the symmetry of the section `h` (clauses `hAv`, `hLv`, `hB1v`, `hB2v` below, taking
the jet components over to `Gf` with `Work.Diff.STE.B3.transport_jet_data`), and its invertibility
hypothesis `hdetv` by the positive definiteness of `h`
(`Work.Diff.STE.D.psi.chartMatOf_det_pos_of_posDef`). -/
private theorem Rres_aux
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j)
    (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
        (fun z p q => ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q)
        z a b
      = Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b := by
  classical
  -- ## 0. basic data
  have hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
      ∈ (extChartAt I (D.x₀ j)).target := D.htarget j z hz
  obtain ⟨hJ1, hJ2, hJ3⟩ :=
    Work.Diff.STE.B3.transport_jet_data (I := I) (M := M) D h hsmooth j hz
  have hGfv : ∀ i k : Fin (Module.finrank ℝ E),
      (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1 i k
        = Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k := by
    intro i k
    simpa only [Work.Diff.STE.B3.Jetsh] using hJ1 i k
  have hGf2v : ∀ (p q i k : Fin (Module.finrank ℝ E)),
      (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.2 (Work.Diff.EXT.bB p)
          (Work.Diff.EXT.bB q) i k
        = Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
            (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k)) z := by
    intro p q i k
    simpa only [Work.Diff.STE.B3.Jetsh] using hJ3 p q i k
  have hGfsym_all : ∀ (y : Fin (Module.finrank ℝ E) → ℝ) (i k : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k
        = Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y k i := by
    intro y i k
    simp only [Work.Diff.STE.B3.Gf, Work.Diff.STE.B3.yf, Work.Diff.STE.D.chartMatOf_apply]
    exact hsym _ _ _
  have hGfsym : ∀ r s : Fin (Module.finrank ℝ E),
      Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z r s
        = Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z s r := fun r s => hGfsym_all z r s
  have hGfL : ∀ (p i k : Fin (Module.finrank ℝ E)),
      (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.1 (Work.Diff.EXT.bB p) i k
        = Work.Diff.STE.pdR p
            (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z := by
    intro p i k
    simpa only [Work.Diff.STE.B3.Jetsh] using hJ2 p i k
  have hA2 : ContDiffAt ℝ 2
      (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y)
      (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) :=
    ((hsmooth (D.x₀ j)).contDiffAt
      ((isOpen_extChartAt_target (I := I) (D.x₀ j)).mem_nhds hzt)).of_le (by norm_num)
  -- the four symmetry conditions of `pPhi_decomp` for the jet of `Gf`
  have hAv : ∀ i k : Fin (Module.finrank ℝ E),
      (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1 i k
        = (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1 k i := by
    intro i k
    rw [hGfv i k, hGfv k i]
    exact hGfsym i k
  have hLv : ∀ (p i k : Fin (Module.finrank ℝ E)),
      (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.1 (Work.Diff.EXT.bB p) i k
        = (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.1 (Work.Diff.EXT.bB p) k i := by
    intro p i k
    rw [hGfL p i k, hGfL p k i]
    exact Work.Diff.STE.B3.pdR_congr (Filter.Eventually.of_forall (fun y => hGfsym_all y i k)) p
  have hB1v : ∀ (m p q r : Fin (Module.finrank ℝ E)),
      (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.2 (Work.Diff.EXT.bB m)
          (Work.Diff.EXT.bB p) q r
        = (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.2 (Work.Diff.EXT.bB p)
            (Work.Diff.EXT.bB m) q r := by
    intro m p q r
    have hsym2 : IsSymmSndFDerivAt ℝ
        (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y)
        (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) := hA2.isSymmSndFDerivAt (by norm_num)
    exact congrFun (congrFun (hsym2.eq (Work.Diff.EXT.bB m) (Work.Diff.EXT.bB p)) q) r
  have hB2v : ∀ (m p q r : Fin (Module.finrank ℝ E)),
      (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.2 (Work.Diff.EXT.bB m)
          (Work.Diff.EXT.bB p) q r
        = (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.2 (Work.Diff.EXT.bB m)
            (Work.Diff.EXT.bB p) r q := by
    intro m p q r
    rw [hGf2v m p q r, hGf2v m p r q]
    exact Work.Diff.STE.B3.pdR2_congr (Filter.Eventually.of_forall (fun y => hGfsym_all y q r)) m p
  -- ## 1. smoothness of the weight and of the on-frame chart matrix
  have hwf2 : ContDiffAt ℝ 2 (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z :=
    ((D.psi_contDiff j).contDiffAt.mul
      (D.sqrt_dens_contDiffAt j (Work.Diff.STE.B3.densGood (I := I) (M := M) D j) hzt)).of_le
      (by norm_num)
  have hU : ∀ᶠ y in 𝓝 z,
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) y ∈ (extChartAt I (D.x₀ j)).target :=
    ((isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
      (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous).mem_nhds hzt
  have hMf2 : ContDiffAt ℝ 2 (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b) z := by
    have hFa : ∀ i : Fin (Module.finrank ℝ E), ContDiffAt ℝ 2
        (fun y => Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i) z :=
      fun i => (Work.Diff.STE.B3.Ff_contDiffAt (I := I) (M := M) D j a i hzt).of_le (by norm_num)
    have hFb : ∀ k : Fin (Module.finrank ℝ E), ContDiffAt ℝ 2
        (fun y => Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z :=
      fun k => (Work.Diff.STE.B3.Ff_contDiffAt (I := I) (M := M) D j b k hzt).of_le (by norm_num)
    have hGsm : ∀ i k : Fin (Module.finrank ℝ E), ContDiffAt ℝ 2
        (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z :=
      fun i k =>
        (Work.Diff.STE.B3.Gf_contDiffAt (I := I) (M := M) D h hsmooth j i k hzt).of_le
          (by norm_num)
    have hS : ContDiffAt ℝ 2 (fun y : Fin (Module.finrank ℝ E) → ℝ => ∑ i, ∑ k,
        Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i
          * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k
          * Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z :=
      ContDiffAt.sum (s := Finset.univ) (fun i _ =>
        ContDiffAt.sum (s := Finset.univ) (fun k _ =>
          ContDiffAt.mul (ContDiffAt.mul (hFa i) (hGsm i k)) (hFb k)))
    refine hS.congr_of_eventuallyEq ?_
    filter_upwards [hU] with y hy
    exact Work.Diff.STE.B3.Mf_eq_of_target (I := I) (M := M) D h j a b hy
  -- ## 2. the two chart jets of the DeTurck operator
  have hmat : Matrix.of (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1
      = Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z) := by
    ext i k
    simpa only [Matrix.of_apply] using hGfv i k
  have hdetv : (Matrix.of (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1).det ≠ 0 := by
    rw [hmat]
    exact ne_of_gt (Work.Diff.STE.D.psi.chartMatOf_det_pos_of_posDef (I := I) (M := M) h
      (D.x₀ j) hsym hpos (D.htarget j z hz))
  have hsec : ∀ i k : Fin (Module.finrank ℝ E),
      Work.Diff.STE.DeTurck.secOp (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1
          (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.2 i k
        = ∑ p, ∑ q, ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
            * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
                (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k)) z := by
    intro i k
    simp only [Work.Diff.STE.DeTurck.secOp, Work.Diff.EXT.jInv]
    rw [hmat]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [hGf2v p q i k]
  have hpPhi : ∀ i k : Fin (Module.finrank ℝ E),
      Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h (D.x₀ j)
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) i k
        = (∑ p, ∑ q, ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
              * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
                  (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k)) z)
          + Work.Diff.STE.DeTurck.pN
              (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).1
              (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).2.1
              (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).2.2
              (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1
              (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.1 i k := by
    intro i k
    have hpd := congrFun (congrFun (Work.Diff.STE.deTurck.pPhi_decomp
      (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).1
      (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).2.1
      (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).2.2
      (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1
      (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.1
      (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.2
      hAv hLv hB1v hB2v hdetv) i) k
    have h' : Work.Diff.STE.D.pPhiJetOf (I := I) (M := M) g₀ h (D.x₀ j)
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) i k
        = Work.Diff.STE.DeTurck.secOp
            (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1
            (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.2 i k
          + Work.Diff.STE.DeTurck.pN
              (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).1
              (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).2.1
              (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).2.2
              (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1
              (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.1 i k := by
      simpa only [Work.Diff.STE.D.pPhiJetOf_apply, Work.Diff.STE.B3.Jets0,
        Work.Diff.STE.B3.Jetsh, Pi.add_apply] using hpd
    rw [h', hsec i k]
  -- ## 3. the first term
  have hR1 : D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
      = Work.Diff.STE.B3.wf (I := I) (M := M) D j z
        * (∑ i, ∑ k, ((∑ p, ∑ q,
              ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
                * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
                    (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k)) z)
            + Work.Diff.STE.DeTurck.pN
              (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).1
              (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).2.1
              (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).2.2
              (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1
              (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.1 i k)
          * (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
              * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k)) := by
    rw [Work.Diff.STE.B3.bridge (I := I) (M := M) hLC h hsym hpos hsmooth D j a b hz]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hpPhi i k]
  -- ## 4. the second term
  have hpdR2 : ∀ p q : Fin (Module.finrank ℝ E),
      Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z
        = Work.Diff.STE.B3.wf (I := I) (M := M) D j z
            * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
                (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b)) z
          + (Work.Diff.STE.pdR q (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b) z)
            * (Work.Diff.STE.pdR p (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z)
          + (Work.Diff.STE.pdR p (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b) z)
            * (Work.Diff.STE.pdR q (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z)
          + Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b
            * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
                (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) z := by
    intro p q
    have hDR : D.R j h a b
        = fun y => Work.Diff.STE.B3.wf (I := I) (M := M) D j y
            * Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b := rfl
    rw [hDR]
    exact Work.Diff.STE.B3.pdR2_mul_at p q hwf2 hMf2
  have hMf2exp : ∀ p q : Fin (Module.finrank ℝ E),
      Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
          (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b)) z
        = Work.Diff.STE.B3.eightTerm (I := I) (M := M) D h j z p q a b
          + ∑ i, ∑ k, Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
                (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k)) z
              * (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
                  * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k) := by
    intro p q
    rw [Work.Diff.STE.B3.transport_Mf_second (I := I) (M := M) D h hsmooth j hz p q a b]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring
  have hR2 : (∑ p, ∑ q, ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
        * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z)
      = ∑ p, ∑ q, ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
          * (Work.Diff.STE.B3.wf (I := I) (M := M) D j z
              * (Work.Diff.STE.B3.eightTerm (I := I) (M := M) D h j z p q a b
                + ∑ i, ∑ k, Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
                      (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k)) z
                    * (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
                        * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k))
            + (Work.Diff.STE.pdR q
                (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b) z)
              * (Work.Diff.STE.pdR p (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z)
            + (Work.Diff.STE.pdR p
                (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b) z)
              * (Work.Diff.STE.pdR q (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z)
            + Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b
              * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
                  (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) z) := by
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [hpdR2 p q, hMf2exp p q]
  -- ## 5. the lower-order expression
  have hR3 : Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b
      = Work.Diff.STE.B3.wf (I := I) (M := M) D j z
          * (∑ i, ∑ k, Work.Diff.STE.DeTurck.pN
              (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).1
              (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).2.1
              (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).2.2
              (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1
              (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.1 i k
              * (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
                  * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k))
        - Work.Diff.STE.B3.wf (I := I) (M := M) D j z
          * (∑ p, ∑ q, ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
              * Work.Diff.STE.B3.eightTerm (I := I) (M := M) D h j z p q a b)
        - ∑ p, ∑ q, ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
            * (2 * (Work.Diff.STE.pdR p (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z)
                * (Work.Diff.STE.pdR q
                    (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b) z)
              + Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b
                * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
                    (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) z) := rfl
  -- ## 6. the symmetry of the coefficient matrix
  have hAsym : ∀ p q : Fin (Module.finrank ℝ E),
      ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
        = ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) q p := by
    intro p q
    have hA : ∀ r s : Fin (Module.finrank ℝ E),
        Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z r s
          = Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z s r := hGfsym
    simpa only [Work.Diff.EXT.jInv] using
      Work.Diff.STE.deTurck.jInv_symm (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z) hA p q
  -- ## 7. assembly
  show D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
      - (∑ p, ∑ q, ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
          * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z)
    = Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b
  rw [hR1, hR2, hR3]
  exact Rres_algebra (n := Module.finrank ℝ E)
    (A := fun p q => ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q)
    hAsym
    (Work.Diff.STE.B3.wf (I := I) (M := M) D j z)
    (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b)
    (fun r => Work.Diff.STE.pdR r (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z)
    (fun r => Work.Diff.STE.pdR r
      (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b) z)
    (fun p q => Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
      (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) z)
    (fun p q i k => Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
      (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k)) z)
    (fun i k => Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
      * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k)
    (fun i k => Work.Diff.STE.DeTurck.pN
      (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).1
      (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).2.1
      (Work.Diff.STE.B3.Jets0 (I := I) (M := M) D j z).2.2
      (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).1
      (Work.Diff.STE.B3.Jetsh (I := I) (M := M) D h j z).2.1 i k)
    (fun p q => Work.Diff.STE.B3.eightTerm (I := I) (M := M) D h j z p q a b)

end

/-- **The residual is the lower-order expression**: with the principal coefficient `A = (Gf)⁻¹` (the
inverse *coordinate*-frame chart matrix), the difference between the localised DeTurck operator and
`Σ A^{pq}∂_p∂_q` applied to the localised component is the explicit lower-order expression
`residualLow`, which involves only the *first* derivatives of the chart matrices.

PROOF (checked by hand by the reviewers; see the review text): `D.R j h a b = wf · Mf`, so the
second term of `Rres` is `Σ_{pq}(Gf⁻¹)_{pq} ∂_p∂_q(wf · Mf)` — the Leibniz rule brings out
`wf · ∂_p∂_q Mf` plus `2∂wf·∂Mf + Mf·∂∂wf`.  The first term is `wf · Σ_{ik} pPhi(…) Ff_a i Ff_b k`
(`Work.Diff.STE.B3.bridge`), which `pPhi_decomp` splits into `pN + secOp`, and
`secOp A B i k = Σ_{cd}(Gf⁻¹)_{cd}∂_c∂_d Gf_{ik}`.  `Work.Diff.STE.B3.transport_Mf_second` reads
`∂_c∂_d Mf_{ab} = eightTerm + Σ_{ik}Ff_{ai}(∂_c∂_d Gf_{ik})Ff_{bk}`, so the `wf·∂∂Mf` piece cancels
the `wf·secOp` piece exactly and leaves the `−wf·Σ(Gf⁻¹)·eightTerm` term.  What remains is the
right-hand side of `residualLow`.  `pPhi_decomp` needs the symmetry of `Gf`, the symmetry of its
first jet and the two symmetry relations for the second jet, all from `hsym`/`hsmooth`, plus
`det Gf ≠ 0` from `hpos`. -/
theorem Rres_eq_residualLow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j)
    (a b : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
        (fun z p q => ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q)
        z a b
      = Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b := by
  exact Rres_aux (I := I) (M := M) D hLC h hsym hpos hsmooth j hz a b

end Work.Diff.STE.B3
