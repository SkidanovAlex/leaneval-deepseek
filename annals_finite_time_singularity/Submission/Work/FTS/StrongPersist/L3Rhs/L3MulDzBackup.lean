/-
# `L3MulDzBackup` — self-contained fallbacks for the two slot estimates of `L3MulDz`

Insurance for `Work.FTS.StrongPersist.L3Rhs.L3MulDz`: the same two slot estimates that were
delegated, proved here independently (different namespace, so that both may coexist).  If the
delegated versions land, they are used; otherwise these are.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.DzIter_le_WlInf_open
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.L3Rhs.L3MulDzAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.L3MulDzBackup

open Work.Spaces (Dz DzIter)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The radial slots of the product `h·D_z f`, proved without any delegation. -/
theorem zslot_dz_le_b : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (h f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen h → Work.Spaces.WlInfMem α 4 h →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ i : ℕ, i ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (DzIter i (fun z θ => h z θ * Dz f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ C * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
  refine ⟨10 ^ 8, by norm_num, ?_⟩
  intro α h f _hα _hα1 hsmh hWm hsmf hfm i hi z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hW : 0 ≤ Work.Spaces.WlInf α 4 h := Work.Spaces.WlInf_nonneg α 4 h hWm
  set Hv : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hHv
  have hDzsm : Work.FTS.EllipticEst.SmoothOpen (Dz f) :=
    Work.FTS.EllipticEst.SmoothOpen.Dz hsmf
  have heq := Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i h (Dz f) hsmh hDzsm z θ hz hθ0 hθ1
  have hsplit : (DzIter i (fun z θ => h z θ * Dz f z θ) z θ * Hv) ^ 2
      = (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * DzIter b h z θ)
            * (DzIter (i - b) (Dz f) z θ * Hv)) ^ 2 := by
    rw [heq, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [hsplit]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => ((i.choose b : ℝ) * DzIter b h z θ)
      * (DzIter (i - b) (Dz f) z θ * Hv))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) = (i : ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hper : ∀ b ∈ Finset.range (i + 1),
      (((i.choose b : ℝ) * DzIter b h z θ)
          * (DzIter (i - b) (Dz f) z θ * Hv)) ^ 2
        ≤ 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
          * (DzIter (i - b + 1) f z θ * Hv) ^ 2 := by
    intro b hb
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hDh : |DzIter b h z θ| ≤ 100 * Work.Spaces.WlInf α 4 h :=
      Work.FTS.OpenPkg.DzIter_le_WlInf_open hsmh hWm (by omega) hz hθ
    have hx : (DzIter b h z θ) ^ 2 ≤ (100 * Work.Spaces.WlInf α 4 h) ^ 2 := by
      have hB : (0 : ℝ) ≤ 100 * Work.Spaces.WlInf α 4 h := mul_nonneg (by norm_num) hW
      have h1 := (abs_le.mp hDh).1
      have h2 := (abs_le.mp hDh).2
      nlinarith [hB, h1, h2]
    have hch : ((i.choose b : ℝ)) ^ 2 ≤ 256 := Work.Spaces.choose_sq_le_256 i b hbi (by omega)
    have hshift : DzIter (i - b) (Dz f) = DzIter (i - b + 1) f := dzIter_Dz_eq (i - b) f
    calc (((i.choose b : ℝ) * DzIter b h z θ)
          * (DzIter (i - b) (Dz f) z θ * Hv)) ^ 2
        = ((i.choose b : ℝ)) ^ 2 * (DzIter b h z θ) ^ 2
            * (DzIter (i - b) (Dz f) z θ * Hv) ^ 2 := by ring
      _ ≤ 256 * (100 * Work.Spaces.WlInf α 4 h) ^ 2
            * (DzIter (i - b) (Dz f) z θ * Hv) ^ 2 := by gcongr
      _ = 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
            * (DzIter (i - b + 1) f z θ * Hv) ^ 2 := by rw [hshift]; ring
  have hsumsq : ∑ b ∈ Finset.range (i + 1), (DzIter (i - b + 1) f z θ * Hv) ^ 2
      ≤ 5 * Work.Spaces.HkIntegrand α 4 f z θ := by
    calc ∑ b ∈ Finset.range (i + 1), (DzIter (i - b + 1) f z θ * Hv) ^ 2
        ≤ ∑ _b ∈ Finset.range (i + 1), Work.Spaces.HkIntegrand α 4 f z θ :=
          Finset.sum_le_sum (fun b _ =>
            Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ (i - b + 1) (by omega))
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α 4 f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ 5 * Work.Spaces.HkIntegrand α 4 f z θ := by
          have hnn := Work.Spaces.HkIntegrand_nonneg α 4 f z θ
          have hI2 : (i : ℝ) + 1 ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
          nlinarith
  calc (∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) * DzIter b h z θ)
            * (DzIter (i - b) (Dz f) z θ * Hv)) ^ 2
      ≤ (((Finset.range (i + 1)).card : ℕ) : ℝ) *
          ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ) * DzIter b h z θ)
              * (DzIter (i - b) (Dz f) z θ * Hv)) ^ 2 := hcs
    _ ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          (2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
            * (DzIter (i - b + 1) f z θ * Hv) ^ 2) := by
        rw [hcard]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
    _ = 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2 * (((i : ℝ) + 1)
          * ∑ b ∈ Finset.range (i + 1), (DzIter (i - b + 1) f z θ * Hv) ^ 2) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
          * (5 * (5 * Work.Spaces.HkIntegrand α 4 f z θ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hI2 : (i : ℝ) + 1 ≤ 5 := by exact_mod_cast (by omega : i + 1 ≤ 5)
        exact mul_le_mul hI2 hsumsq (Finset.sum_nonneg (fun b _ => sq_nonneg _)) (by norm_num)
    _ ≤ 10 ^ 8 * (Work.Spaces.WlInf α 4 h) ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ := by
        have hnn := Work.Spaces.HkIntegrand_nonneg α 4 f z θ
        have h2 : 0 ≤ (Work.Spaces.WlInf α 4 h) ^ 2 := sq_nonneg _
        have hh : 2560000 * (Work.Spaces.WlInf α 4 h) ^ 2
              * (5 * (5 * Work.Spaces.HkIntegrand α 4 f z θ))
            = 64000000 * ((Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ) := by ring
        rw [hh, show (10 : ℝ) ^ 8 * (Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ
            = 10 ^ 8 * ((Work.Spaces.WlInf α 4 h) ^ 2
              * Work.Spaces.HkIntegrand α 4 f z θ) from by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg h2 hnn)

end Work.FTS.StrongPersist.L3Rhs.L3MulDzBackup
