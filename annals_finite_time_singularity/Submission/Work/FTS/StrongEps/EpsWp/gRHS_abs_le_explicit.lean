import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.gRHS_abs_le_on_compact
import Submission.Work.FTS.StrongEps.gRHSBound.abs_N0_le
import Submission.Work.FTS.StrongEps.gRHSBound.abs_N_le
import Submission.Work.FTS.StrongEps.gRHSBound.abs_Nstar_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsWp

/-- Triangle inequality for four terms, with the first one negated (the shape in which the
sum `gRHS = -μ̄·AK + N₀ + N + N_*` appears). -/
private lemma abs_neg_add3_le (a b c d : ℝ) : |-a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 : |-a + b + c + d| ≤ |-a + b + c| + |d| := abs_add_le (-a + b + c) d
  have h2 : |-a + b + c| ≤ |-a + b| + |c| := abs_add_le (-a + b) c
  have h3 : |-a + b| ≤ |a| + |b| := by simpa [abs_neg] using abs_add_le (-a) b
  linarith [h1, h2, h3, abs_nonneg c, abs_nonneg d]

/-- Eleven nonnegative summands with total at most `B` are each at most `B`.  This is the
only place where the hypothesis `hbnd` (a bound on the *sum* of the eleven quantities) is
used: it delivers the eleven individual bounds. -/
private lemma le_of_eleven_sum_le {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 B : ℝ}
    (h : a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 ≤ B)
    (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3) (h4 : 0 ≤ a4) (h5 : 0 ≤ a5)
    (h6 : 0 ≤ a6) (h7 : 0 ≤ a7) (h8 : 0 ≤ a8) (h9 : 0 ≤ a9) (h10 : 0 ≤ a10)
    (h11 : 0 ≤ a11) :
    a1 ≤ B ∧ a2 ≤ B ∧ a3 ≤ B ∧ a4 ≤ B ∧ a5 ≤ B ∧ a6 ≤ B ∧ a7 ≤ B ∧ a8 ≤ B
      ∧ a9 ≤ B ∧ a10 ≤ B ∧ a11 ≤ B := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem gRHS_abs_le_explicit {α B μ lam : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hB : 0 ≤ B)
    (hμ : |μ| ≤ 1 / 2) (hlam : |lam| ≤ 1) {F Φ g : Work.FTS.Galerkin.Fn} {z θ : ℝ}
    (hbnd : |F z θ| + |Work.Spaces.pth F z θ| + |Work.Spaces.Dz F z θ| + |g z θ|
        + |Work.Spaces.Dz g z θ| + |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        + |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        + |Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ|
        + |Work.Construction.AK α z θ| ≤ B)
    (hL12Fstar : |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ B)
    (hL12g : |Work.Construction.L12 g z| ≤ B)
    (hmubar : |Work.Construction.mubar (Work.Construction.N0 α F g)
        (Work.Construction.N α F Φ)| ≤ B)
    (hFK : |Work.Construction.FK F z| ≤ B) :
    |Work.Construction.gRHS α μ lam F Φ g z θ| ≤
      B * B + (4 / α + 6) * B ^ 2 + 8 * B ^ 2 + 3 * B := by
  -- unpack `hbnd`: it bounds the *sum* of the eleven quantities, hence each of them
  obtain ⟨hF, hpF, hDzF, hg, hDzg, hpFs, hDzFs, hRop, hUop, hVop, hAK⟩ :=
    le_of_eleven_sum_le hbnd (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      (abs_nonneg _) (abs_nonneg _)
  -- the three summand bounds, from the dedicated helper modules
  have hN0 := Work.FTS.StrongEps.gRHSBound.abs_N0_le hα hB hL12Fstar hL12g hF hpF hDzF hg
    hDzg hpFs hDzFs
  have hN := Work.FTS.StrongEps.gRHSBound.abs_N_le hα hα1 hB hF hpF hDzF hRop hUop hVop hFK
  have hNs := Work.FTS.StrongEps.gRHSBound.abs_Nstar_le hB hμ hlam hg hDzg
  -- the `μ̄·AK` term
  have hmAK : |Work.Construction.mubar (Work.Construction.N0 α F g) (Work.Construction.N α F Φ)
      * Work.Construction.AK α z θ| ≤ B * B := by
    rw [abs_mul]
    exact mul_le_mul hmubar hAK (abs_nonneg _) hB
  -- assemble: `gRHS = -μ̄·AK + N₀ + N + N_*`
  have hsplit : |Work.Construction.gRHS α μ lam F Φ g z θ| ≤
      |Work.Construction.mubar (Work.Construction.N0 α F g) (Work.Construction.N α F Φ)
        * Work.Construction.AK α z θ|
      + |Work.Construction.N0 α F g z θ| + |Work.Construction.N α F Φ z θ|
      + |Work.Construction.Nstar μ lam g z θ| := by
    rw [Work.Construction.gRHS, neg_mul]
    exact abs_neg_add3_le _ _ _ _
  linarith [hsplit, hmAK, hN0, hN, hNs]

end Work.FTS.StrongEps.EpsWp
