/-
# The first jet of the coordinate-frame chart matrix equals the nominal jet `tmDGK`

The coordinate-frame chart matrix `Gf` of a section `h` is, on the chart target, the conjugate of
the orthonormal-frame chart matrix by the inverse frame matrix,

`Gf z i k = Σ_{ab} Finvf z i a * Mf z a b * Finvf z k b`

(`Work.Diff.STE.B3.Gf_eq_dual`, and its germ form `Work.Diff.STE.B3.tmNom_Gf_eventuallyEq`, which
is valid on a whole neighbourhood of every point of the `2σ j`-ball).  Differentiating this identity
by the product rule gives exactly the nominal first jet `tmDGK` of `tmGK` at
`V = Mf z`, `W = ∂Mf z` (`Work.Diff.STE.B3.tmDGK`), which is the form in which the first jet of the
coordinate chart matrix enters the transport identity.

The only inputs are the germ form of the frame-change identity and the local smoothness of the two
factor families `Finvf` (`tmNom_Finvf_ContDiffAt`) and `Mf` (`Mf_contDiffAt_loc`, proved here from
`Mf = Ff · Gf · Ffᵀ`).
-/
import Mathlib
import Submission.Work.Diff.STE.B3.tmNom_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set
open LeanEval.Geometry.SphereTheorem Submission.Diff

/-! ## 1. Auxiliary calculus -/

/-- **The Leibniz rule for a triple product**: the first derivative of `A · B · C` is the sum of the
three terms in which exactly one factor is differentiated and the other two are evaluated. -/
lemma pdR_triple_at {d : ℕ} {A B C : (Fin d → ℝ) → ℝ} {z : Fin d → ℝ} (c : Fin d)
    (hA : DifferentiableAt ℝ A z) (hB : DifferentiableAt ℝ B z) (hC : DifferentiableAt ℝ C z) :
    Work.Diff.STE.pdR c (fun y => A y * B y * C y) z
      = Work.Diff.STE.pdR c A z * B z * C z + A z * Work.Diff.STE.pdR c B z * C z
        + A z * B z * Work.Diff.STE.pdR c C z := by
  have hAB : DifferentiableAt ℝ (fun y => A y * B y) z := hA.mul hB
  have h1 := pdR_mul_at c hAB hC
  have h2 := pdR_mul_at c hA hB
  rw [h1, h2]
  ring

/-! ## 2. Smoothness of the orthonormal-frame chart matrix -/

/-- **The orthonormal-frame chart matrix is smooth** at every flat coordinate of the `2σ j`-ball.
On the chart target (an open condition, hence valid on a neighbourhood of `z`) the frame-change
identity `Mf = Σ_{ik} Ff a i · Gf i k · Ff b k` holds, and the two factor families are smooth there
(`Ff` because the orthonormal frame is a smooth section, `Gf` by the hypothesis `ChartData h`). -/
lemma Mf_contDiffAt_loc (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : ‖z‖ ≤ 2 * D.σ j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => Mf (I := I) (M := M) D h j y a b) z := by
  have hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
    D.htarget j z hz
  have hU : ∀ᶠ y in nhds z,
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) y ∈ (extChartAt I (D.x₀ j)).target :=
    ((isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
      (Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous).mem_nhds hzt
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ∑ i, ∑ k,
      Ff (I := I) (M := M) D j y a i * Gf (I := I) (M := M) D h j y i k
        * Ff (I := I) (M := M) D j y b k) z := by
    refine ContDiffAt.sum (s := Finset.univ) (fun i _ => ?_)
    refine ContDiffAt.sum (s := Finset.univ) (fun k _ => ?_)
    exact ((Ff_contDiffAt (I := I) (M := M) D j a i hzt).mul
      (Gf_contDiffAt (I := I) (M := M) D h hsmooth j i k hzt)).mul
      (Ff_contDiffAt (I := I) (M := M) D j b k hzt)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hU] with y hy
  exact Mf_eq_of_target (I := I) (M := M) D h j a b hy

/-! ## 3. The first jet of the frame-change sum -/

/-- **The first derivative of the frame-change sum** `Σ_{ab} Finvf i a · Mf a b · Finvf k b` is the
product-rule expansion in which exactly one of the three factors is differentiated. -/
lemma pdR_nG_at (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j)
    (c i k : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.pdR c
        (fun y => ∑ a, ∑ b, Finvf (I := I) (M := M) D j y i a
          * Mf (I := I) (M := M) D h j y a b * Finvf (I := I) (M := M) D j y k b) z
      = ∑ a, ∑ b,
          ( Work.Diff.STE.pdR c (fun y => Finvf (I := I) (M := M) D j y i a) z
              * Mf (I := I) (M := M) D h j z a b * Finvf (I := I) (M := M) D j z k b
            + Finvf (I := I) (M := M) D j z i a
              * Work.Diff.STE.pdR c (fun y => Mf (I := I) (M := M) D h j y a b) z
              * Finvf (I := I) (M := M) D j z k b
            + Finvf (I := I) (M := M) D j z i a * Mf (I := I) (M := M) D h j z a b
              * Work.Diff.STE.pdR c (fun y => Finvf (I := I) (M := M) D j y k b) z) := by
  have hFinv : ∀ p q : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y => Finvf (I := I) (M := M) D j y p q) z :=
    fun p q => (tmNom_Finvf_ContDiffAt (I := I) (M := M) D j p q hz).differentiableAt (by simp)
  have hMfd : ∀ p q : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun y => Mf (I := I) (M := M) D h j y p q) z :=
    fun p q =>
      (Mf_contDiffAt_loc (I := I) (M := M) D h hsmooth j p q hz).differentiableAt (by simp)
  have hterm : ∀ a b : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        Finvf (I := I) (M := M) D j w i a * Mf (I := I) (M := M) D h j w a b
          * Finvf (I := I) (M := M) D j w k b) z :=
    fun a b => ((hFinv i a).mul (hMfd a b)).mul (hFinv k b)
  have hinner : ∀ a : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        ∑ b : Fin (Module.finrank ℝ E), Finvf (I := I) (M := M) D j w i a
          * Mf (I := I) (M := M) D h j w a b * Finvf (I := I) (M := M) D j w k b) z := by
    intro a
    rw [show (fun w : Fin (Module.finrank ℝ E) → ℝ =>
          ∑ b : Fin (Module.finrank ℝ E), Finvf (I := I) (M := M) D j w i a
            * Mf (I := I) (M := M) D h j w a b * Finvf (I := I) (M := M) D j w k b)
        = (∑ b : Fin (Module.finrank ℝ E), fun w : Fin (Module.finrank ℝ E) → ℝ =>
            Finvf (I := I) (M := M) D j w i a * Mf (I := I) (M := M) D h j w a b
              * Finvf (I := I) (M := M) D j w k b) from by
      funext w; simp only [Finset.sum_apply]]
    exact DifferentiableAt.sum (u := Finset.univ) (fun b _ => hterm a b)
  rw [pdR_fun_sum_at (d := Module.finrank ℝ E) c hinner]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [pdR_fun_sum_at (d := Module.finrank ℝ E) c (fun b => hterm a b)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [pdR_triple_at c (hFinv i a) (hMfd a b) (hFinv k b)]

/-! ## 4. The target -/

theorem pdR_Gf_eq_tmDGK
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j)
    (c i k : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.pdR c
        (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z
      = Work.Diff.STE.B3.tmDGK (I := I) (M := M) D j z
          (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z)
          (fun a b r => Work.Diff.STE.pdR r
            (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b) z)
          c i k := by
  rw [pdR_congr (tmNom_Gf_eventuallyEq (I := I) (M := M) D h j hz i k) c]
  rw [pdR_nG_at (I := I) (M := M) D h hsmooth j hz c i k]
  simp only [tmDGK, tmDFin]

end

end Work.Diff.STE.B3
