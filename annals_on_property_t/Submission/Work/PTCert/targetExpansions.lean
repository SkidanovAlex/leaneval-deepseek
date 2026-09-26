import Mathlib
import Submission.Work.PTCert.Interfaces
import Submission.Work.PTCert.LetterCore
import Submission.Work.PTCert.LetterAPI
import Submission.Work.PTCert.gramLLinear
import Submission.Work.PTCert.gramLOuter
import Submission.Work.PTCert.QAdjOpSplit
import Submission.Work.PTCert.deltaSubExpansion
import Submission.Work.PTCert.edgeLapExpansion

/-!
# (T1) The target expansions of the certificate pipeline

`TargetExpansions r` says that the two target elements of `Submission/PTCert/Interfaces.lean`
are the Gram forms `gramL` of the coefficient matrices `QDelta` and `QAdjOp`:

* `Δ² − λΔ = Σ_{a,b} QDelta λ a b • of(b1 a⁻¹ * b1 b)`,
* `Adj + kop•Op − μΔ = Σ_{a,b} QAdjOp kop μ a b • of(b1 a⁻¹ * b1 b)`,

where `Δ = deltaSub r r = Laplacian (SAutGen r)`, `Adj`, `Op` are the sums of `Δ_e Δ_f` over the
ordered pairs of adjacent/opposite edges, and `b1 r a` are the letters (`0` is the identity `1`,
`1 ≤ a < NB1 r` are the Nielsen transvections).

The proof is the "Gram product formula": for coefficient vectors `x y` over the letters,
`gramL r (x ⊗ y) = (Σ_a x_a • of(b1 a⁻¹)) · (Σ_b y_b • of(b1 b))`
(`gramLOuter`); `Δ` is self-adjoint (`Edge.star_deltaSub`) and its letter expansion is
`deltaSubExpansion`, so `Δ² = star Δ · Δ = gramL (cDelta ⊗ cDelta)`; the `-λΔ` part is the
`a = 0` row plus the `b = 0` column, computed by `gramL_mu_part`.  The second identity is
`QAdjOpSplit` (which splits `QAdjOp` into the `Adj`/`Op` pair sums and the same row-plus-column
part), `edgeLapExpansion` (the letters of an edge), and the linearity of `gramL`
(`gramLLinear`).
-/

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert
open Submission.FreeGroupAut
open Submission.RouteB

noncomputable section

/-! ## Auxiliary lemmas about `gramL`, `star` and the letters -/

/-- `star` of a letter combination. -/
theorem star_sum_smul_letter (r : ℕ) (s : Finset ℕ) (c : ℕ → ℚ)
    (g : ℕ → MulAut (FreeGroup (Fin r))) :
    star (∑ a ∈ s, (c a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (g a))
      = ∑ a ∈ s, (c a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) ((g a)⁻¹) := by
  rw [star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_smul, Submission.Helpers.star_of]
  simp

/-- The `a = 0` row plus the `b = 0` column pattern of the two target forms. -/
def cDeltaFF (r : ℕ) (a b : ℕ) : ℚ :=
  (if a = 0 then cDelta r b else 0) + (if b = 0 then cDelta r a else 0)

/-- The self-adjointness of `Δ`, in the letter form. -/
theorem star_deltaSub_letters (r : ℕ)
    (hDelta : Edge.deltaSub r r = ∑ a ∈ Finset.range (NB1 r),
      (cDelta r a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (b1 r a)) :
    star (Edge.deltaSub r r) = ∑ a ∈ Finset.range (NB1 r),
      (cDelta r a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) ((b1 r a)⁻¹) := by
  rw [hDelta, star_sum_smul_letter]

/-- **The `μ`-part of both target forms**: the `a = 0` row plus the `b = 0` column of
`Δ` contributes `Δ + star Δ = 2 Δ`. -/
theorem gramL_cDeltaFF (r : ℕ)
    (hDelta : Edge.deltaSub r r = ∑ a ∈ Finset.range (NB1 r),
      (cDelta r a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (b1 r a)) :
    gramL r (cDeltaFF r) = Edge.deltaSub r r + Edge.deltaSub r r := by
  have hself : star (Edge.deltaSub r r) = Edge.deltaSub r r := Edge.star_deltaSub r r
  have hstar := star_deltaSub_letters r hDelta
  have h1 : gramL r (fun a b => (if a = 0 then cDelta r b else 0)
        + (if b = 0 then cDelta r a else 0))
      = gramL r (fun a b => if a = 0 then cDelta r b else 0)
        + gramL r (fun a b => if b = 0 then cDelta r a else 0) :=
    (Work.PTCert.gramLLinear r (fun _ _ => (0 : ℚ))
      (fun a b => if a = 0 then cDelta r b else 0)
      (fun a b => if b = 0 then cDelta r a else 0)).1
  have h2 : gramL r (fun a b => if a = 0 then cDelta r b else 0)
      = ∑ b ∈ Finset.range (NB1 r),
        (cDelta r b : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (b1 r b) :=
    (Work.PTCert.gramLOuter r (cDelta r) (cDelta r)).2.1
  have h3 : gramL r (fun a b => if b = 0 then cDelta r a else 0)
      = ∑ a ∈ Finset.range (NB1 r),
        (cDelta r a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) ((b1 r a)⁻¹) :=
    (Work.PTCert.gramLOuter r (cDelta r) (cDelta r)).2.2
  rw [show cDeltaFF r = (fun a b => (if a = 0 then cDelta r b else 0)
      + (if b = 0 then cDelta r a else 0)) from rfl, h1, h2, h3, ← hDelta, ← hstar, hself]

/-- The scaled `μ`-part: `gramL r (fun a b => μ * cDeltaFF r a b / 2) = μ • Δ`. -/
theorem gramL_mu_part (r : ℕ) (mu : ℚ)
    (hDelta : Edge.deltaSub r r = ∑ a ∈ Finset.range (NB1 r),
      (cDelta r a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (b1 r a)) :
    gramL r (fun a b => mu * cDeltaFF r a b / 2) = (mu : ℝ) • Edge.deltaSub r r := by
  have hFF := gramL_cDeltaFF r hDelta
  have hsplit : (fun a b => mu * cDeltaFF r a b / 2)
      = (fun a b => (mu / 2) * cDeltaFF r a b) := by
    funext a b
    ring
  rw [hsplit,
    (Work.PTCert.gramLLinear r (cDeltaFF r) (fun _ _ => (0 : ℚ)) (fun _ _ => (0 : ℚ))).2.2.1
      (mu / 2), hFF]
  rw [← two_smul ℝ (Edge.deltaSub r r), smul_smul]
  congr 1
  push_cast
  ring

/-- The `Adj` bracket of the second target form. -/
def QAadj (r : ℕ) (a b : ℕ) : ℚ :=
  ∑ x ∈ Edge.Psub r r, cEdge r (edgePair x.1) a * cEdge r (edgePair x.2) b

/-- The `Op` bracket of the second target form. -/
def QAop (r : ℕ) (a b : ℕ) : ℚ :=
  ∑ x ∈ Edge.Qsub r r, cEdge r (edgePair x.1) a * cEdge r (edgePair x.2) b

/-- `QAdjOp` in terms of the `Adj`/`Op` brackets and the row-plus-column part. -/
theorem QAdjOp_eq_brackets (r : ℕ) (kop mu : ℚ) (a b : ℕ) :
    QAdjOp r kop mu a b = QAadj r a b + kop * QAop r a b - mu * cDeltaFF r a b / 2 := by
  rw [QAdjOpSplit r kop mu a b]
  simp only [QAadj, QAop, cDeltaFF]

/-- **The product formula for one pair of edges**: `gramL` of the outer product of the two
coefficient vectors of the edge Laplacians is `Δ_e Δ_f`. -/
theorem gramL_edge_outer (r : ℕ)
    (hEdge : ∀ p : Edge r, Edge.edgeLap p = ∑ a ∈ Finset.range (NB1 r),
      (cEdge r (edgePair p) a : ℝ) • MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (b1 r a))
    (x : Edge r × Edge r) :
    gramL r (fun a b => cEdge r (edgePair x.1) a * cEdge r (edgePair x.2) b)
      = Edge.edgeLap x.1 * Edge.edgeLap x.2 := by
  rw [(Work.PTCert.gramLOuter r (cEdge r (edgePair x.1)) (cEdge r (edgePair x.2))).1,
    ← star_sum_smul_letter r (Finset.range (NB1 r)) (cEdge r (edgePair x.1)) (b1 r),
    ← Edge.edgeLap_star x.1, hEdge x.1, hEdge x.2]

/-! ## The target expansions -/

theorem targetExpansions (r : ℕ) : TargetExpansions r := by
  have hDelta := deltaSubExpansion r
  have hEdge := edgeLapExpansion r
  constructor
  · intro lam
    have hsub : gramL r (fun a b => cDelta r a * cDelta r b - lam * cDeltaFF r a b / 2)
        = gramL r (fun a b => cDelta r a * cDelta r b)
          - gramL r (fun a b => lam * cDeltaFF r a b / 2) :=
      (Work.PTCert.gramLLinear r (fun _ _ => (0 : ℚ))
        (fun a b => cDelta r a * cDelta r b) (fun a b => lam * cDeltaFF r a b / 2)).2.1
    rw [show QDelta r lam = (fun a b => cDelta r a * cDelta r b - lam * cDeltaFF r a b / 2)
        from rfl, hsub, gramL_mu_part r lam hDelta]
    congr 1
    rw [(Work.PTCert.gramLOuter r (cDelta r) (cDelta r)).1,
      ← star_sum_smul_letter r (Finset.range (NB1 r)) (cDelta r) (b1 r),
      ← hDelta, Edge.star_deltaSub r r, sq]
  · intro kop mu
    refine (?_ : gramL r (QAdjOp r kop mu) = _).symm
    have hQ' : QAdjOp r kop mu
        = (fun a b => QAadj r a b + kop * QAop r a b - mu * cDeltaFF r a b / 2) :=
      funext fun a => funext fun b => QAdjOp_eq_brackets r kop mu a b
    rw [hQ']
    have h1 : gramL r (fun a b => (QAadj r a b + kop * QAop r a b) - mu * cDeltaFF r a b / 2)
        = gramL r (fun a b => QAadj r a b + kop * QAop r a b)
          - gramL r (fun a b => mu * cDeltaFF r a b / 2) :=
      (Work.PTCert.gramLLinear r (fun _ _ => (0 : ℚ))
        (fun a b => QAadj r a b + kop * QAop r a b)
        (fun a b => mu * cDeltaFF r a b / 2)).2.1
    rw [show (fun a b => QAadj r a b + kop * QAop r a b - mu * cDeltaFF r a b / 2)
        = (fun a b => (QAadj r a b + kop * QAop r a b) - mu * cDeltaFF r a b / 2) from rfl, h1]
    have h2 : gramL r (fun a b => QAadj r a b + kop * QAop r a b)
        = gramL r (QAadj r) + gramL r (fun a b => kop * QAop r a b) :=
      (Work.PTCert.gramLLinear r (fun _ _ => (0 : ℚ))
        (QAadj r) (fun a b => kop * QAop r a b)).1
    rw [h2]
    have h3 : gramL r (fun a b => kop * QAop r a b) = (kop : ℝ) • gramL r (QAop r) :=
      (Work.PTCert.gramLLinear r (QAop r) (fun _ _ => (0 : ℚ)) (fun _ _ => (0 : ℚ))).2.2.1 kop
    rw [h3, gramL_mu_part r mu hDelta]
    have hQAdef : QAadj r = (fun a b => ∑ x ∈ Edge.Psub r r,
        cEdge r (edgePair x.1) a * cEdge r (edgePair x.2) b) := rfl
    have hQOdef : QAop r = (fun a b => ∑ x ∈ Edge.Qsub r r,
        cEdge r (edgePair x.1) a * cEdge r (edgePair x.2) b) := rfl
    have hQA : gramL r (QAadj r) = Edge.AdjPair r r := by
      rw [hQAdef]
      rw [(Work.PTCert.gramLLinear r (fun _ _ => (0 : ℚ)) (fun _ _ => (0 : ℚ))
        (fun _ _ => (0 : ℚ))).2.2.2 (Edge.Psub r r)
        (fun x a b => cEdge r (edgePair x.1) a * cEdge r (edgePair x.2) b)]
      rw [Edge.AdjPair]
      exact Finset.sum_congr rfl fun x _ => gramL_edge_outer r hEdge x
    have hQO : gramL r (QAop r) = Edge.OpPair r r := by
      rw [hQOdef]
      rw [(Work.PTCert.gramLLinear r (fun _ _ => (0 : ℚ)) (fun _ _ => (0 : ℚ))
        (fun _ _ => (0 : ℚ))).2.2.2 (Edge.Qsub r r)
        (fun x a b => cEdge r (edgePair x.1) a * cEdge r (edgePair x.2) b)]
      rw [Edge.OpPair]
      exact Finset.sum_congr rfl fun x _ => gramL_edge_outer r hEdge x
    rw [hQA, hQO]

end

end Work.PTCert
