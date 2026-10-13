import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.DerivLikeDefs
import Submission.Work.FTS.FinalClock.ZopIterLeibniz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

open Set Filter

/-- The one-`Dzd` step of the Leibniz rule for a summand `c * (X * Y)`
(`Dzd u = z u'`). -/
private theorem Dzd_const_mul_mul (c : ℝ) {X Y : ℝ → ℝ} {z : ℝ}
    (hX : DifferentiableAt ℝ X z) (hY : DifferentiableAt ℝ Y z) :
    Work.Elliptic.Dzd (fun w => c * (X w * Y w)) z
      = c * (Work.Elliptic.Dzd X z * Y z + X z * Work.Elliptic.Dzd Y z) := by
  have hXY : DifferentiableAt ℝ (fun w : ℝ => X w * Y w) z := hX.mul hY
  have h1 : deriv (fun w : ℝ => c * (X w * Y w)) z
      = c * deriv (fun w : ℝ => X w * Y w) z := deriv_const_mul c hXY
  have h2 : deriv (fun w : ℝ => X w * Y w) z = deriv X z * Y z + X z * deriv Y z :=
    deriv_mul hX hY
  simp only [Work.Elliptic.Dzd]
  rw [h1, h2]
  ring

/-- `Dzd` is linear over finite sums of differentiable functions. -/
private theorem Dzd_sum_range (K : ℕ) (A : ℕ → ℝ → ℝ) {z : ℝ}
    (hA : ∀ b ≤ K, DifferentiableAt ℝ (A b) z) :
    Work.Elliptic.Dzd (fun w => ∑ b ∈ Finset.range (K + 1), A b w) z
      = ∑ b ∈ Finset.range (K + 1), Work.Elliptic.Dzd (A b) z := by
  have hd : ∀ b ∈ Finset.range (K + 1), DifferentiableAt ℝ (A b) z :=
    fun b hb => hA b (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))
  simp only [Work.Elliptic.Dzd]
  rw [deriv_fun_sum hd, Finset.mul_sum]

theorem DzdIter_mul_of_diff (N : ℕ) (u v : ℝ → ℝ)
    (hu : ∀ b, b + 1 ≤ N → DifferentiableOn ℝ (Work.Elliptic.DzdIter b u) (Set.Ioi (0 : ℝ)))
    (hv : ∀ b, b + 1 ≤ N → DifferentiableOn ℝ (Work.Elliptic.DzdIter b v) (Set.Ioi (0 : ℝ))) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter N (fun z => u z * v z) z
        = ∑ b ∈ Finset.range (N + 1),
            (N.choose b : ℝ) * (Work.Elliptic.DzdIter b u z * Work.Elliptic.DzdIter (N - b) v z) := by
  revert hu hv
  induction N with
  | zero =>
      intro hu hv z hz
      simp
  | succ N ih =>
      intro hu hv z hz
      -- the differentiability hypotheses at the (one lower) level `N`
      have hu' : ∀ b, b + 1 ≤ N → DifferentiableOn ℝ (Work.Elliptic.DzdIter b u) (Set.Ioi 0) :=
        fun b hb => hu b (by omega)
      have hv' : ∀ b, b + 1 ≤ N → DifferentiableOn ℝ (Work.Elliptic.DzdIter b v) (Set.Ioi 0) :=
        fun b hb => hv b (by omega)
      -- the inductive hypothesis, as an `EqOn` on the open set `Ioi 0`
      have hIH : Set.EqOn (Work.Elliptic.DzdIter N (fun z => u z * v z))
          (fun w => ∑ b ∈ Finset.range (N + 1),
            (N.choose b : ℝ) * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (N - b) v w))
          (Set.Ioi 0) := fun w hw => ih hu' hv' w hw
      have hder : deriv (Work.Elliptic.DzdIter N (fun z => u z * v z)) z
          = deriv (fun w => ∑ b ∈ Finset.range (N + 1),
              (N.choose b : ℝ) * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (N - b) v w)) z :=
        hIH.deriv isOpen_Ioi hz
      -- differentiability of the summands at `z ∈ Ioi 0`
      have hd_X : ∀ b ≤ N, DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z :=
        fun b hb => (hu b (by omega)).differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hd_Y : ∀ b ≤ N, DifferentiableAt ℝ (Work.Elliptic.DzdIter (N - b) v) z :=
        fun b hb => (hv (N - b) (by omega)).differentiableAt (isOpen_Ioi.mem_nhds hz)
      calc Work.Elliptic.DzdIter (N + 1) (fun z => u z * v z) z
          = Work.Elliptic.Dzd (Work.Elliptic.DzdIter N (fun z => u z * v z)) z := rfl
        _ = z * deriv (Work.Elliptic.DzdIter N (fun z => u z * v z)) z := rfl
        _ = z * deriv (fun w => ∑ b ∈ Finset.range (N + 1),
              (N.choose b : ℝ) * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (N - b) v w)) z := by
              rw [hder]
        _ = Work.Elliptic.Dzd (fun w => ∑ b ∈ Finset.range (N + 1),
              (N.choose b : ℝ) * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (N - b) v w)) z := rfl
        _ = ∑ b ∈ Finset.range (N + 1), Work.Elliptic.Dzd
              (fun w => (N.choose b : ℝ)
                * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (N - b) v w)) z := by
              apply Dzd_sum_range
              intro b hb
              exact ((hd_X b hb).mul (hd_Y b hb)).const_mul _
        _ = ∑ b ∈ Finset.range (N + 1), (N.choose b : ℝ)
              * (Work.Elliptic.DzdIter (b + 1) u z * Work.Elliptic.DzdIter (N - b) v z
                + Work.Elliptic.DzdIter b u z * Work.Elliptic.DzdIter (N - b + 1) v z) := by
              apply Finset.sum_congr rfl
              intro b hb
              have hbN : b ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
              rw [Dzd_const_mul_mul (N.choose b : ℝ) (hd_X b hbN) (hd_Y b hbN)]
              simp only [Work.Elliptic.DzdIter_succ]
        _ = ∑ j ∈ Finset.range (N + 1 + 1), ((N + 1).choose j : ℝ)
              * (Work.Elliptic.DzdIter j u z * Work.Elliptic.DzdIter (N + 1 - j) v z) :=
              Work.Spaces.leibniz_step N (fun i => Work.Elliptic.DzdIter i u z)
                (fun i => Work.Elliptic.DzdIter i v z)

end Work.FTS.StrongPersist.H6Aux
