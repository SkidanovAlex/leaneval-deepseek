import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.ScoefOpen
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6
import Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.divz_conj2
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.divz_mixed_leibniz
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.divz_DzIter_le
import Submission.Work.FTS.PhiStar.StarPkgo2Aux.CoeffF0
import Submission.Work.Elliptic.division_by_z
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork

open Work.FTS.Galerkin (Fn)

/-! ## The multiplier `z/(1+z)` is smooth on the open quadrant -/

theorem smoothOpen_divz : Work.FTS.EllipticEst.SmoothOpen (fun z _ => z / (1 + z)) := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro n
  show ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 / (1 + p.1)) Work.FTS.EllipticEst.Q0
  refine ContDiffOn.div contDiff_fst.contDiffOn (contDiff_const.add contDiff_fst).contDiffOn ?_
  intro p hp
  have h1 : (0 : ℝ) < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  intro h
  linarith

/-! ## The pure radial slots `i = 0` -/

theorem divz_conj0 (CΦ : ℝ) (hCΦpos : 0 < CΦ)
    (hCΦ : ∀ b : ℕ, b ≤ 6 → ∀ z θ : ℝ, 0 < z →
      |Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ| ≤ CΦ * (z / (1 + z)))
    (hleib : ∀ (j i : ℕ) (G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen G →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.mixed j i (fun z θ => z / (1 + z) * G z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
              (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
                * Work.Spaces.mixed (j - b) i G z θ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (G : ℝ → ℝ → ℝ) (K : ℝ),
        Work.FTS.EllipticEst.SmoothOpen G →
        Work.Spaces.WlInfMem α 6 G → Work.Spaces.WlInf α 6 G ≤ K →
        ∀ j : ℕ, j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j 0 (fun z θ => z / (1 + z) * G z θ) z θ|
            ≤ C * K * (z / (1 + z)) := by
  refine ⟨max 1 (64000 * CΦ), lt_max_of_lt_left (by norm_num), ?_⟩
  intro α hα G K hsm hmem hK j hj z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 G := Work.Spaces.WlInf_nonneg α 6 G hmem
  have hKnn : 0 ≤ K := le_trans hWnn hK
  have hFnn : 0 ≤ z / (1 + z) := by positivity
  have hchoose : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)) = (2 : ℝ) ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  have h2j : (2 : ℝ) ^ j ≤ 64 := by
    calc (2 : ℝ) ^ j ≤ (2 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) hj
      _ = 64 := by norm_num
  rw [hleib j 0 G hsm z θ hz hθ0 hθ1]
  have hterm : ∀ b ∈ Finset.range (j + 1),
      |(j.choose b : ℝ) * (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
        * Work.Spaces.mixed (j - b) 0 G z θ)|
        ≤ (j.choose b : ℝ) * (CΦ * (z / (1 + z))) * (1000 * K) := by
    intro b hb
    have hb6 : b ≤ 6 := by
      have := Finset.mem_range.mp hb
      omega
    have hjb : j - b ≤ 6 := by omega
    have h1 : |Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ| ≤ CΦ * (z / (1 + z)) :=
      hCΦ b hb6 z θ hz
    have h2 : |Work.Spaces.mixed (j - b) 0 G z θ| ≤ 1000 * K := by
      rw [Work.Spaces.mixed_zero_right]
      exact le_trans (Work.FTS.StrongPersist.N6Trans.dzIter_le_WlInf6 hsm hmem hjb hz hθ)
        (mul_le_mul_of_nonneg_left hK (by norm_num))
    have hcb : (0 : ℝ) ≤ (j.choose b : ℝ) := Nat.cast_nonneg _
    calc |(j.choose b : ℝ) * (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
            * Work.Spaces.mixed (j - b) 0 G z θ)|
        = (j.choose b : ℝ) * (|Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ|
            * |Work.Spaces.mixed (j - b) 0 G z θ|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hcb]
      _ ≤ (j.choose b : ℝ) * ((CΦ * (z / (1 + z))) * (1000 * K)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcb
          exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = (j.choose b : ℝ) * (CΦ * (z / (1 + z))) * (1000 * K) := by ring
  calc |∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
            * Work.Spaces.mixed (j - b) 0 G z θ)|
      ≤ ∑ b ∈ Finset.range (j + 1),
          |(j.choose b : ℝ) * (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
            * Work.Spaces.mixed (j - b) 0 G z θ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) * (CΦ * (z / (1 + z))) * (1000 * K) :=
        Finset.sum_le_sum hterm
    _ = (∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ))
          * ((CΦ * (z / (1 + z))) * (1000 * K)) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring
    _ = (2 : ℝ) ^ j * ((CΦ * (z / (1 + z))) * (1000 * K)) := by rw [hchoose]
    _ ≤ 64 * ((CΦ * (z / (1 + z))) * (1000 * K)) := by
        refine mul_le_mul_of_nonneg_right h2j ?_
        positivity
    _ = (64000 * CΦ) * (K * (z / (1 + z))) := by ring
    _ ≤ max 1 (64000 * CΦ) * (K * (z / (1 + z))) := by
        refine mul_le_mul_of_nonneg_right (le_max_right _ _) ?_
        positivity
    _ = max 1 (64000 * CΦ) * K * (z / (1 + z)) := by ring

/-! ## The target -/

theorem wlInf_divz_slotsB : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧ α₂ ≤ 1 ∧ ∀ α ∈ Set.Ioc 0 α₂,
    ∀ (G : Work.FTS.Galerkin.Fn) (K : ℝ),
      Work.FTS.EllipticEst.SmoothOpen G →
      Work.Spaces.WlInfMem α 6 G → Work.Spaces.WlInf α 6 G ≤ K →
      (∀ j i : ℕ, j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i (fun z θ => z / (1 + z) * G z θ) z θ| ≤ C * K * (z / (1 + z))) ∧
      (∀ j i : ℕ, 1 ≤ i → j + i ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
          |Work.Spaces.mixed j i (fun z θ => z / (1 + z) * G z θ) z θ|
            ≤ C * K * (z / (1 + z)) * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  have hCΦ : ∀ b : ℕ, b ≤ 6 → ∀ z θ : ℝ, 0 < z →
      |Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ| ≤ (1000000 : ℝ) * (z / (1 + z)) :=
    fun b hb z θ hz => divz_DzIter_le b hb z θ hz
  have hleib : ∀ (j i : ℕ) (G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen G →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.mixed j i (fun z θ => z / (1 + z) * G z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ) *
              (Work.Spaces.DzIter b (fun z _ => z / (1 + z)) z θ
                * Work.Spaces.mixed (j - b) i G z θ) :=
    fun j i G hG z θ hz hθ0 hθ1 =>
      divz_mixed_leibniz (fun z => z / (1 + z)) G j i smoothOpen_divz hG z θ hz hθ0 hθ1
  obtain ⟨C2, hC2pos, hC2⟩ := divz_conj2 1000000 (by norm_num) hCΦ hleib
  obtain ⟨C0, hC0pos, hC0⟩ := divz_conj0 1000000 (by norm_num) hCΦ hleib
  refine ⟨max (2 * C2) C0, 1, lt_max_of_lt_left (by linarith), by norm_num, le_refl 1, ?_⟩
  intro α hα G K hsm hmem hK
  have hαpos : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 G := Work.Spaces.WlInf_nonneg α 6 G hmem
  have hKnn : 0 ≤ K := le_trans hWnn hK
  have hC2nn : 0 ≤ C2 := le_of_lt hC2pos
  have hC0le : C0 ≤ max (2 * C2) C0 := le_max_right _ _
  have hC2le : C2 ≤ max (2 * C2) C0 := le_trans (by linarith) (le_max_left _ _)
  constructor
  · intro j i hji z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hFnn : 0 ≤ z / (1 + z) := by positivity
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have h := hC0 α hα G K hsm hmem hK j (by omega) z θ hz hθ0 hθ1
      exact le_trans h
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0le hKnn) hFnn)
    · have h := hC2 α hα G K hsm hmem hK j i hipos hji z θ hz hθ0 hθ1
      have hfac := Work.FTS.StrongPersist.N6Trans.L6FBound.angFac_le_two hαpos hα1 hθ
      have hSnn : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg' hθI
      have hΨnn : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
        mul_nonneg (by linarith) (Real.rpow_nonneg hSnn _)
      have hKF : 0 ≤ K * (z / (1 + z)) := mul_nonneg hKnn hFnn
      have hstep : C2 * K * (z / (1 + z)) * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
          ≤ C2 * K * (z / (1 + z)) * 2 := by
        calc C2 * K * (z / (1 + z)) * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
            = C2 * (K * (z / (1 + z))) * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
              ring
          _ ≤ C2 * (K * (z / (1 + z))) * 2 :=
              mul_le_mul_of_nonneg_left hfac (mul_nonneg hC2nn hKF)
          _ = C2 * K * (z / (1 + z)) * 2 := by ring
      calc |Work.Spaces.mixed j i (fun z θ => z / (1 + z) * G z θ) z θ|
          ≤ C2 * K * (z / (1 + z)) * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := h
        _ ≤ C2 * K * (z / (1 + z)) * 2 := hstep
        _ = (2 * C2) * (K * (z / (1 + z))) := by ring
        _ ≤ max (2 * C2) C0 * (K * (z / (1 + z))) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hKF
        _ = max (2 * C2) C0 * K * (z / (1 + z)) := by ring
  · intro j i hi1 hji z θ hz hθ0 hθ1
    have h := hC2 α hα G K hsm hmem hK j i hi1 hji z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hFnn : 0 ≤ z / (1 + z) := by positivity
    have hSnn : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg' hθI
    have hKFnn : 0 ≤ K * (z / (1 + z)) * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
      mul_nonneg (mul_nonneg hKnn hFnn) (mul_nonneg (by linarith) (Real.rpow_nonneg hSnn _))
    refine le_trans h ?_
    calc C2 * K * (z / (1 + z)) * (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)
        = C2 * (K * (z / (1 + z)) * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
          ring
      _ ≤ max (2 * C2) C0
            * (K * (z / (1 + z)) * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul_of_nonneg_right hC2le hKFnn
      _ = max (2 * C2) C0 * K * (z / (1 + z)) * (α + Real.sin (2 * θ))
            * (Real.sin (2 * θ)) ^ (α / 5) := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork
