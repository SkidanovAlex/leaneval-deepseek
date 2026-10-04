import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.densGood_noT2
import Submission.Work.Diff.STE.B3.transport_tame_leibniz
import Submission.Work.Diff.STE.B3.transport_Mf_second

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open scoped BigOperators Topology

set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **Contracting the double sum of `secOp` against the frame weights.**  Purely algebraic: push
the two matrix sums of `Σ_{cd} Inv c d * B c d i k` out of the `(i,k)`-sum and collect the weight
product with the two `(i,k)`-sums. -/
private lemma sum_secOp_weight {k : ℕ} (Inv : Fin k → Fin k → ℝ)
    (B : Fin k → Fin k → Fin k → Fin k → ℝ) (F G : Fin k → Fin k → ℝ) (af bf : Fin k) :
    (∑ i, ∑ k', (∑ c, ∑ d, Inv c d * B c d i k') * (F af i * G bf k'))
      = ∑ c, ∑ d, Inv c d * (∑ i, ∑ k', F af i * B c d i k' * G bf k') := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  have hL : (∑ i, ∑ k', ∑ c, ∑ d, (Inv c d * B c d i k') * (F af i * G bf k'))
      = ∑ p : Fin k × Fin k, ∑ q : Fin k × Fin k,
          (Inv q.1 q.2 * B q.1 q.2 p.1 p.2) * (F af p.1 * G bf p.2) := by
    rw [← Fintype.sum_prod_type (f := fun p : Fin k × Fin k =>
      ∑ c, ∑ d, (Inv c d * B c d p.1 p.2) * (F af p.1 * G bf p.2))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    exact (Fintype.sum_prod_type (f := fun q : Fin k × Fin k =>
      (Inv q.1 q.2 * B q.1 q.2 p.1 p.2) * (F af p.1 * G bf p.2))).symm
  have hR : (∑ c, ∑ d, ∑ i, ∑ k', Inv c d * (F af i * B c d i k' * G bf k'))
      = ∑ q : Fin k × Fin k, ∑ p : Fin k × Fin k,
          Inv q.1 q.2 * (F af p.1 * B q.1 q.2 p.1 p.2 * G bf p.2) := by
    rw [← Fintype.sum_prod_type (f := fun q : Fin k × Fin k =>
      ∑ i, ∑ k', Inv q.1 q.2 * (F af i * B q.1 q.2 i k' * G bf k'))]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    exact (Fintype.sum_prod_type (f := fun p : Fin k × Fin k =>
      Inv q.1 q.2 * (F af p.1 * B q.1 q.2 p.1 p.2 * G bf p.2))).symm
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun p _ => ?_))
  ring

/-- **The localised weight is `C²`** on the `2σ j`-ball: `wf = ψ j · √dens j` is the product of the
smooth bump weight `ψ j` with the square root of the (smooth, positive) volume density. -/
lemma wf_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    ContDiffAt ℝ 2 (wf (I := I) (M := M) D j) z := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (D.psi j) z := (D.psi_contDiff j).contDiffAt
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => Real.sqrt (D.dens j w)) z :=
    D.sqrt_dens_contDiffAt j (densGood (I := I) (M := M) D j) (D.htarget j z hz)
  exact (h1.mul h2).of_le (by norm_num)

/-- **The orthonormal-frame chart matrix is `C²`** on the `2σ j`-ball.  On the chart target the
frame-change identity `Mf = Σ_{ik} Ff a i · Gf i k · Ff b k` holds
(`Work.Diff.STE.B3.Mf_eq_of_target`), and the two factors are smooth there: `Ff` because the
orthonormal frame `e j ·` is a smooth section, `Gf` by the hypothesis `ChartData h`. -/
lemma Mf_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (af bf : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    ContDiffAt ℝ 2 (fun w => Mf (I := I) (M := M) D h j w af bf) z := by
  have hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
    D.htarget j z hz
  have hU : ∀ᶠ y in nhds z,
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) y ∈ (extChartAt I (D.x₀ j)).target :=
    ((isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
      (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous).mem_nhds hzt
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => ∑ i, ∑ k, Ff (I := I) (M := M) D j y af i
        * Gf (I := I) (M := M) D h j y i k * Ff (I := I) (M := M) D j y bf k) z := by
    refine ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ => ?_))
    exact ((Ff_contDiffAt (I := I) (M := M) D j af i hzt).mul
      (Gf_contDiffAt (I := I) (M := M) D h hsmooth j i k hzt)).mul
      (Ff_contDiffAt (I := I) (M := M) D j bf k hzt)
  refine (hsum.of_le (by norm_num)).congr_of_eventuallyEq ?_
  filter_upwards [hU] with y hy
  exact Mf_eq_of_target (I := I) (M := M) D h j af bf hy

theorem secOp_weight_sum_eq
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
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (af bf : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ)
    (hz : ‖z‖ ≤ 2 * D.σ j)
    (hSec : ∀ c d : Fin (Module.finrank ℝ E),
      (∑ i, ∑ k, Work.Diff.STE.B3.Ff (I := I) (M := M) D j z af i
          * (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
              (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.2
              (Work.Diff.EXT.bB (E := E) c) (Work.Diff.EXT.bB (E := E) d) i k
          * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z bf k)
        = Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
            (fun w => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w af bf)) z
          - Work.Diff.STE.B3.eightTerm (I := I) (M := M) D h j z c d af bf) :
    ((∑ i, ∑ k, Work.Diff.STE.DeTurck.secOp
          ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
            (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).1)
          ((Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
            (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.2) i k
        * (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z af i
          * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z bf k))
      = ∑ c, ∑ d, ((Matrix.of (fun i k => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k))⁻¹) c d
          * (Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
              (fun w => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w af bf)) z
            - Work.Diff.STE.B3.eightTerm (I := I) (M := M) D h j z c d af bf))
    ∧ (∀ c d : Fin (Module.finrank ℝ E),
      Work.Diff.STE.B3.wf (I := I) (M := M) D j z
          * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
              (fun w => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w af bf)) z
        = Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
              (fun w => D.R j h af bf w)) z
          - (Work.Diff.STE.pdR c (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z
              * Work.Diff.STE.pdR d (fun w => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w af bf) z
            + Work.Diff.STE.pdR d (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z
              * Work.Diff.STE.pdR c (fun w => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w af bf) z
            + Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) z
              * Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z af bf)) := by
  constructor
  · -- ## Part 1: the contraction of the `secOp` double sum
    -- the chart matrix of the section is the first component of its jet
    have hA : (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
        (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).1
        = Gf (I := I) (M := M) D h j z := rfl
    -- expand `secOp` and `jInv`, and replace the chart matrix by `Gf`
    simp only [Work.Diff.STE.DeTurck.secOp, Work.Diff.EXT.jInv, hA]
    -- push the two matrix sums out of the `(i,k)`-sum
    rw [sum_secOp_weight
      (fun c d => ((Matrix.of (Gf (I := I) (M := M) D h j z))⁻¹) c d)
      (fun c d i k => (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
        (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.2
        (Work.Diff.EXT.bB (E := E) c) (Work.Diff.EXT.bB (E := E) d) i k)
      (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z)
      (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z) af bf]
    -- substitute the principal-part lemma into each summand
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    rw [hSec c d]
  · -- ## Part 2: the second-order Leibniz rule for `R = wf · Mf`
    intro c d
    have hwf : ContDiffAt ℝ 2 (wf (I := I) (M := M) D j) z := wf_contDiffAt D j hz
    have hMf : ContDiffAt ℝ 2
        (fun w => Mf (I := I) (M := M) D h j w af bf) z := Mf_contDiffAt D h hsmooth j af bf hz
    have hR : (fun w => D.R j h af bf w)
        = fun w => wf (I := I) (M := M) D j w * Mf (I := I) (M := M) D h j w af bf := rfl
    rw [hR, pdR2_mul_at (f := wf (I := I) (M := M) D j)
      (g := fun w => Mf (I := I) (M := M) D h j w af bf) c d hwf hMf]
    ring

end Work.Diff.STE.B3
