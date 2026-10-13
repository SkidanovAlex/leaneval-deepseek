import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Split
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19aux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.Gs_bounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.IntegralSubadd
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.HkSq_Vs0_mul_Gs_eq_zero
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.H2.WPQ.Leibniz
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.helpers.GsSmoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.FTS.Nonlinear.Pieces.RNP (Vs Gs)

namespace HsZ

/-! ## 1. The `D_z`-bound for `D_zF_*` with the angular factor kept

`Gs_bounds` records `|D_z^m D_zF_*| ≤ C·α·z/(1+z)²`; for the pointwise majorant of the row-19
coefficient we need the same bound *without* discarding the angular factor `Γ(θ)` (which is
what makes the resulting `ℋ⁴`-majorant integrable in `θ`).  The bound follows from the
factorisation `D_z^m D_zF_* = (αΓ(θ)/c)·D_z^m Hz` (`DzIter_Gs_factor`) and the α-free radial
bound `abs_DzIter_Hz_le`; `α ≤ 1` is *not* needed because the constant may depend on `α`. -/

theorem Gs_DzIter_le {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, m ≤ 4 → ∀ z ∈ Work.Spaces.Iz,
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter m (Gs α) z θ|
        ≤ K * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2) := by
  obtain ⟨CH, hCHpos, hCH⟩ := abs_DzIter_Hz_le
  refine ⟨CH, hCHpos, ?_⟩
  intro m hm z hz θ hθ
  have hz' : (-1 : ℝ) < z := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz; linarith
  have hcpos : 0 < Work.Spaces.c α := c_pos_of_pos hα
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
  have hcoef : 0 ≤ α * Work.Spaces.Gam α θ / Work.Spaces.c α :=
    div_nonneg (mul_nonneg hα.le hG0) hcpos.le
  rw [Row19GsAux.DzIter_Gs_factor hα m hz']
  have hHz := hCH m hm z hz θ
  calc |α * Work.Spaces.Gam α θ / Work.Spaces.c α
        * Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ|
      = (α * Work.Spaces.Gam α θ / Work.Spaces.c α)
          * |Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ| := by
        rw [abs_mul, abs_of_nonneg hcoef]
    _ ≤ (α * Work.Spaces.Gam α θ / Work.Spaces.c α) * (CH * (z / (1 + z) ^ 2)) :=
        mul_le_mul_of_nonneg_left hHz hcoef
    _ = CH * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2) := by ring

/-- The same bound for the mixed `D_z`-iterates of `D_θ^i (D_zF_*)`, `i ≥ 1`. -/
theorem Gs_DzIter_DthIter_le {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ m : ℕ, m ≤ 4 →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter m (Work.Spaces.DthIter i (Gs α)) z θ|
        ≤ K * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2) := by
  obtain ⟨CH, hCHpos, hCH⟩ := abs_DzIter_Hz_le
  obtain ⟨Cg, hCgpos, hCg⟩ := dthIter_Gam_le (α := α) hα
  refine ⟨CH * Cg, by positivity, ?_⟩
  intro i hi1 hi4 m hm z hz θ hθ
  have hz' : (-1 : ℝ) < z := by
    rw [Work.Spaces.Iz, Set.mem_Ici] at hz; linarith
  have hcpos : 0 < Work.Spaces.c α := c_pos_of_pos hα
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
  have hcoef : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  rw [Row19GsAux.DzIter_DthIter_Gs_factor hα i m hz' hθ]
  have hDth : Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ
      = Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ :=
    Work.FTS.LocData.DthIter_rad_eq i (fun θ => Work.Spaces.Gam α θ) 0 θ
  rw [hDth]
  have hΓ := hCg i hi4 θ hθI
  have hHz := hCH m hm z hz θ
  calc |α / Work.Spaces.c α * Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ
        * Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ|
      = (α / Work.Spaces.c α) * |Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ|
          * |Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hcoef]
    _ ≤ (α / Work.Spaces.c α) * (Cg * Work.Spaces.Gam α θ) * (CH * (z / (1 + z) ^ 2)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hΓ hcoef) hHz (abs_nonneg _) ?_
        exact mul_nonneg hcoef (mul_nonneg hCgpos.le hG0)
    _ = CH * Cg * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2) := by ring

/-! ## 2. The pure `D_z`-bound for the row-19 coefficient -/

theorem DzIter_Vs_mul_Gs_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∃ K : ℝ, 0 < K ∧ ∀ i : ℕ, i ≤ 4 → ∀ z ∈ Work.Spaces.Iz,
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ|
        ≤ K * (z / (1 + z) ^ 2) * Work.Spaces.Gam α θ := by
  obtain ⟨K1, hK1pos, hK1⟩ := Gs_DzIter_le (α := α) hα
  have hVs : Work.FTS.LocData.SmoothQuad (Vs α Φs) := Vs_smoothQuad hα hs
  have hGs : Work.FTS.LocData.SmoothQuad (Gs α) := smoothQuad_Gs_of_pos hα
  have hmem : Work.Spaces.WlInfMem α 4 (Vs α Φs) := by
    simpa only [Vs, Work.FTS.Nonlin.PhiTs] using hs.V.1
  have hcpos : 0 < Work.Spaces.c α := c_pos_of_pos hα
  have hΛ0 : 0 ≤ K1 * (α / Work.Spaces.c α) := mul_nonneg hK1pos.le (div_nonneg hα.le hcpos.le)
  have hW0 : 0 ≤ Work.Spaces.WlInf α 4 (Vs α Φs) := Work.Spaces.WlInf_nonneg _ _ _ hmem
  refine ⟨16 * 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (K1 * (α / Work.Spaces.c α)) + 1,
    by positivity, ?_⟩
  intro i hi4 z hz θ hθ
  have hLeib := Work.FTS.LocData.DzIter_mul_smoothQuad i (Vs α Φs) (Gs α) hz
    (hVs.curry_z hθ) (hGs.curry_z hθ)
  have hze : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz (by positivity)
  have hG0 : 0 ≤ Work.Spaces.Gam α θ :=
    (Work.Spaces.Gam_bounds α θ hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩).1
  have hterm : ∀ b ∈ Finset.range (i + 1),
      |(i.choose b : ℝ) * (Work.Spaces.DzIter b (Vs α Φs) z θ
        * Work.Spaces.DzIter (i - b) (Gs α) z θ)|
        ≤ (i.choose b : ℝ)
            * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
                * (K1 * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2))) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hVb : |Work.Spaces.DzIter b (Vs α Φs) z θ| ≤ 15 * Work.Spaces.WlInf α 4 (Vs α Φs) :=
      Work.FTS.H2.WPQ.DzIter_le_WlInf hVs hmem (by omega) hz hθ
    have hGb : |Work.Spaces.DzIter (i - b) (Gs α) z θ|
        ≤ K1 * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2) :=
      hK1 (i - b) (by omega) z hz θ hθ
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    exact mul_le_mul hVb hGb (abs_nonneg _) (by positivity)
  calc |Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ|
      = |∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (Work.Spaces.DzIter b (Vs α Φs) z θ
            * Work.Spaces.DzIter (i - b) (Gs α) z θ)| := by rw [hLeib]
    _ ≤ ∑ b ∈ Finset.range (i + 1),
          |(i.choose b : ℝ) * (Work.Spaces.DzIter b (Vs α Φs) z θ
            * Work.Spaces.DzIter (i - b) (Gs α) z θ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
              * (K1 * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2))) :=
        Finset.sum_le_sum hterm
    _ = (∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ))
          * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
              * (K1 * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2))) := by
        rw [Finset.sum_mul]
    _ = (2 : ℝ) ^ i * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
              * (K1 * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2))) := by
        rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ 16 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
              * (K1 * (α / Work.Spaces.c α) * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc (2 : ℝ) ^ i ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hi4
          _ = 16 := by norm_num
    _ ≤ (16 * 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (K1 * (α / Work.Spaces.c α)) + 1)
          * (z / (1 + z) ^ 2) * Work.Spaces.Gam α θ := by
        nlinarith [hW0, hΛ0, hze, hG0]

/-! ## 3. The mixed bound for the row-19 coefficient -/

theorem Mixed_Vs_mul_Gs_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∃ K : ℝ, 0 < K ∧ ∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 →
      ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ|
        ≤ K * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  obtain ⟨K1, hK1pos, hK1⟩ := Gs_DzIter_le (α := α) hα
  obtain ⟨K2, hK2pos, hK2⟩ := Gs_DzIter_DthIter_le (α := α) hα
  have hVs : Work.FTS.LocData.SmoothQuad (Vs α Φs) := Vs_smoothQuad hα hs
  have hGs : Work.FTS.LocData.SmoothQuad (Gs α) := smoothQuad_Gs_of_pos hα
  have hmem : Work.Spaces.WlInfMem α 4 (Vs α Φs) := by
    simpa only [Vs, Work.FTS.Nonlin.PhiTs] using hs.V.1
  have hcpos : 0 < Work.Spaces.c α := c_pos_of_pos hα
  have hW0 : 0 ≤ Work.Spaces.WlInf α 4 (Vs α Φs) := Work.Spaces.WlInf_nonneg _ _ _ hmem
  have hαc0 : 0 ≤ α / Work.Spaces.c α := div_nonneg hα.le hcpos.le
  set A : ℝ := K1 * (α / Work.Spaces.c α) with hA
  set B : ℝ := K2 * (α / Work.Spaces.c α) with hB
  have hA0 : 0 ≤ A := by rw [hA]; exact mul_nonneg hK1pos.le hαc0
  have hB0 : 0 ≤ B := by rw [hB]; exact mul_nonneg hK2pos.le hαc0
  refine ⟨6400 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)) + 1, by positivity, ?_⟩
  intro j i hi1 hij z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hLeib := Work.FTS.H2.WPQ.mixed_mul_eq_smoothQuad (j := j) (i := i)
    (f := Vs α Φs) (g := Gs α) hVs hGs z hz θ hθ
  have hze : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz (by positivity)
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
  have hG1 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθI).2
  have hΛ0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := angW_nonneg hα hθI
  have hbin : ∀ n : ℕ, n ≤ 4 → ∀ a : ℕ, (n.choose a : ℝ) ≤ 16 := by
    intro n hn a
    by_cases ha : a ∈ Finset.range (n + 1)
    · refine le_trans (Finset.single_le_sum (f := fun b => (n.choose b : ℝ))
        (fun _ _ => Nat.cast_nonneg _) ha) ?_
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      calc (2 : ℝ) ^ n ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hn
        _ = 16 := by norm_num
    · have hlt : n < a := by
        rw [Finset.mem_range] at ha; omega
      rw [Nat.choose_eq_zero_of_lt hlt]
      norm_num
  have hC0 : 0 ≤ 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
      * (z / (1 + z) ^ 2)
      * (Work.Spaces.Gam α θ
        + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by positivity
  have hterm : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      |((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a (Vs α Φs) z θ
              * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)|
        ≤ 256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
            * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
    intro a ha b hb
    have hai : a ≤ i := by have := Finset.mem_range.mp ha; omega
    have hbj : b ≤ j := by have := Finset.mem_range.mp hb; omega
    have hca : (i.choose a : ℝ) ≤ 16 := hbin i (by omega) a
    have hcb : (j.choose b : ℝ) ≤ 16 := hbin j (by omega) b
    have hca0 : (0 : ℝ) ≤ (i.choose a : ℝ) := Nat.cast_nonneg _
    have hcb0 : (0 : ℝ) ≤ (j.choose b : ℝ) := Nat.cast_nonneg _
    have hmid : |Work.Spaces.mixed b a (Vs α Φs) z θ|
        * |Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ|
        ≤ 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
            * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst ha0
        have hVsb : |Work.Spaces.mixed b 0 (Vs α Φs) z θ|
            ≤ 15 * Work.Spaces.WlInf α 4 (Vs α Φs) := by
          rw [Work.Spaces.mixed_zero_right]
          exact Work.FTS.H2.WPQ.DzIter_le_WlInf hVs hmem (by omega) hz hθ
        have hGsb : |Work.Spaces.mixed (j - b) (i - 0) (Gs α) z θ|
            ≤ B * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2) := by
          rw [Nat.sub_zero]
          exact hK2 i hi1 (by omega) (j - b) (by omega) z hz θ hθ
        refine le_trans (mul_le_mul hVsb hGsb (abs_nonneg _) (by positivity)) ?_
        have h1 : B * Work.Spaces.Gam α θ
            ≤ (A + B + 1) * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
          have h2 : B * Work.Spaces.Gam α θ
              ≤ B * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
            mul_le_mul_of_nonneg_left (by linarith) hB0
          have h5 : B * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
              ≤ (A + B + 1) * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
            have h6 : 0 ≤ Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by linarith
            nlinarith [h6]
          linarith
        calc (15 * Work.Spaces.WlInf α 4 (Vs α Φs))
                * (B * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2))
            = (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
                * (B * Work.Spaces.Gam α θ)) * (z / (1 + z) ^ 2) := by ring
          _ ≤ (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
                * ((A + B + 1) * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
                * (z / (1 + z) ^ 2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hze
          _ = 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
                * (z / (1 + z) ^ 2)
                * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
      · have hVsb : |Work.Spaces.mixed b a (Vs α Φs) z θ|
            ≤ 15 * (Work.Spaces.WlInf α 4 (Vs α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          Work.FTS.H2.WPQ.Mixed_le_WlInf hα hVs hmem hapos (by omega) hz hθ
        have hGsb : |Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ|
            ≤ max A B * (z / (1 + z) ^ 2) := by
          rcases Nat.eq_zero_or_pos (i - a) with hid | hidpos
          · rw [hid, Work.Spaces.mixed_zero_right]
            have h := hK1 (j - b) (by omega) z hz θ hθ
            refine le_trans (le_trans h ?_) (mul_le_mul_of_nonneg_right (le_max_left A B) hze)
            calc A * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2)
                ≤ A * 1 * (z / (1 + z) ^ 2) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG1 hA0) hze
              _ = A * (z / (1 + z) ^ 2) := by ring
          · have h := hK2 (i - a) hidpos (by omega) (j - b) (by omega) z hz θ hθ
            refine le_trans (le_trans h ?_) (mul_le_mul_of_nonneg_right (le_max_right A B) hze)
            calc B * Work.Spaces.Gam α θ * (z / (1 + z) ^ 2)
                ≤ B * 1 * (z / (1 + z) ^ 2) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG1 hB0) hze
              _ = B * (z / (1 + z) ^ 2) := by ring
        refine le_trans (mul_le_mul hVsb hGsb (abs_nonneg _) (by positivity)) ?_
        have h1 : max A B ≤ A + B + 1 := by
          refine max_le ?_ ?_ <;> linarith [hA0, hB0]
        calc (15 * (Work.Spaces.WlInf α 4 (Vs α Φs)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
              * (max A B * (z / (1 + z) ^ 2))
            ≤ (15 * (Work.Spaces.WlInf α 4 (Vs α Φs)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
              * ((A + B + 1) * (z / (1 + z) ^ 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hze) (by positivity)
          _ = 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
                * (z / (1 + z) ^ 2)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
          _ ≤ 15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
                * (z / (1 + z) ^ 2)
                * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              linarith
    calc |((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a (Vs α Φs) z θ
              * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)|
        = ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (|Work.Spaces.mixed b a (Vs α Φs) z θ|
              * |Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ|) := by
          rw [abs_mul, abs_of_nonneg (mul_nonneg hca0 hcb0), abs_mul]
      _ ≤ (16 * 16) * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
              * (z / (1 + z) ^ 2)
              * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul (mul_le_mul hca hcb hcb0 (by norm_num)) hmid (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
      _ = 256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
              * (z / (1 + z) ^ 2)
              * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by norm_num
  have hinner : ∀ a ∈ Finset.range (i + 1),
      (∑ b ∈ Finset.range (j + 1),
          |((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (Vs α Φs) z θ
                * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)|)
        ≤ 5 * (256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
            * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by
    intro a ha
    calc (∑ b ∈ Finset.range (j + 1),
          |((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (Vs α Φs) z θ
                * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)|)
        ≤ ∑ _b ∈ Finset.range (j + 1), 256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
            * (A + B + 1) * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          Finset.sum_le_sum (fun b hb => hterm a ha b hb)
      _ ≤ 5 * (256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
            * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast (by omega : j + 1 ≤ 5)
  calc |Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ|
      = |∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (Vs α Φs) z θ
                * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)| := by rw [hLeib]
    _ ≤ ∑ a ∈ Finset.range (i + 1), |∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (Vs α Φs) z θ
                * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          |((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (Vs α Φs) z θ
                * Work.Spaces.mixed (j - b) (i - a) (Gs α) z θ)| :=
        Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _a ∈ Finset.range (i + 1), 5 * (256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs)
            * (A + B + 1) * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :=
        Finset.sum_le_sum hinner
    _ ≤ 5 * (5 * (256 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
            * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast (by omega : i + 1 ≤ 5)
    _ = 6400 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
            * (z / (1 + z) ^ 2)
            * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by ring
    _ ≤ (6400 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)) + 1)
          * (z / (1 + z) ^ 2)
          * (Work.Spaces.Gam α θ
            + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
        rw [show 6400 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1)
              * (z / (1 + z) ^ 2)
              * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            = 6400 * (15 * Work.Spaces.WlInf α 4 (Vs α Φs) * (A + B + 1))
              * (z / (1 + z) ^ 2)
              * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) from by ring]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hze) ?_
        linarith

/-! ## 4. The pointwise `ℋ⁴`-majorant -/

/-- `w z * (z/(1+z)²) = 1/z` for `z > 0`. -/
lemma w_mul_profile {z : ℝ} (hz : 0 < z) :
    Work.Spaces.w z * (z / (1 + z) ^ 2) = 1 / z := by
  have h1 : z ≠ 0 := ne_of_gt hz
  have h2 : (1 + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  rw [Work.Spaces.w]
  field_simp

/-- At `z = 0` the `ℋ⁴`-integrand vanishes (the radial weight `w 0 = 0` kills both sums). -/
lemma HkIntegrand_eq_zero_of_z_eq_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [Work.Spaces.w, Work.Spaces.Wt, Work.Spaces.wTheta]

/-- The pointwise majorant of the `ℋ⁴`-integrand of `V(Φ̃_*)·D_zF_*`: the angular factor
`(Γ + (α+sin 2θ)sin(2θ)^{α/5})²·sin(2θ)^{-γ}` is integrable in `θ` (`theta_majorant_integrable`),
so this gives the integrability of every `θ`-slice of the integrand. -/
theorem Vs_mul_Gs_HkIntegrand_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∃ K : ℝ → ℝ, (∀ z, 0 ≤ K z) ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
        ≤ K z * ((Work.Spaces.Gam α θ
            + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
  obtain ⟨K1, hK1pos, hK1⟩ := DzIter_Vs_mul_Gs_le (α := α) (Cs := Cs) (Φs := Φs) hα hs
  obtain ⟨K2, hK2pos, hK2⟩ := Mixed_Vs_mul_Gs_le (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have hKfun0 : ∀ z : ℝ, 0 ≤ (5 * K1 ^ 2 + 25 * K2 ^ 2 + 1) * (1 / z ^ 2) + 1 := by
    intro z
    have h : 0 ≤ (5 * K1 ^ 2 + 25 * K2 ^ 2 + 1) * (1 / z ^ 2) :=
      mul_nonneg (by nlinarith [sq_nonneg K1, sq_nonneg K2]) (by positivity)
    linarith
  refine ⟨fun z => (5 * K1 ^ 2 + 25 * K2 ^ 2 + 1) * (1 / z ^ 2) + 1, hKfun0, ?_⟩
  intro z hz θ hθ
  have hsin0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ_R hθ
  have hS0 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hsin0 _
  have hbracket0 : 0 ≤ (Work.Spaces.Gam α θ
      + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    mul_nonneg (sq_nonneg _) hS0
  by_cases hz0 : z = 0
  · rw [hz0, HkIntegrand_eq_zero_of_z_eq_zero]
    exact mul_nonneg (hKfun0 0) hbracket0
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    by_cases hsin : Real.sin (2 * θ) = 0
    · rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α 4 _ z θ hsin]
      exact mul_nonneg (hKfun0 z) hbracket0
    · have hθoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
        refine ⟨?_, ?_⟩
        · rcases eq_or_lt_of_le hθ.1 with h | h
          · exact absurd (by rw [← h]; simp) hsin
          · exact h
        · rcases lt_or_eq_of_le hθ.2 with h | h
          · exact h
          · exact absurd (by rw [h, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]) hsin
      have hsinpos : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθoo.1]) (by linarith [hθoo.2, Real.pi_pos])
      have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
      have hΛ0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := angW_nonneg hα hθ
      have hΓΛ0 : 0 ≤ Work.Spaces.Gam α θ
          + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) := by linarith
      have hzs : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz (by positivity)
      have hwprof : Work.Spaces.w z * (z / (1 + z) ^ 2) = 1 / z := w_mul_profile hzpos
      have hsqw : (z / (1 + z) ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2 = (1 / z) ^ 2 := by
        rw [mul_comm, ← mul_pow, hwprof]
      -- the pure `D_z` slots
      have htermZ : ∀ i ∈ Finset.range (4 + 1),
          (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        intro i hi
        have hi4 : i ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hb := hK1 i hi4 z hz θ hθoo
        have hpair0 : 0 ≤ K1 * (z / (1 + z) ^ 2) * Work.Spaces.Gam α θ :=
          mul_nonneg (mul_nonneg hK1pos.le hzs) hΓ0
        have h2 : (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) ^ 2
            ≤ (K1 * (z / (1 + z) ^ 2) * Work.Spaces.Gam α θ) ^ 2 :=
          sq_le_sq.mpr (by rw [abs_of_nonneg hpair0]; exact hb)
        have h3 : (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
            ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          wdiv_sq_le hα hθ
        have hs2 : (Work.Spaces.Gam α θ) ^ 2 ≤ (Work.Spaces.Gam α θ
            + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 :=
          pow_le_pow_left₀ hΓ0 (by linarith) 2
        calc (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            = (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) ^ 2
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by ring
          _ ≤ (K1 * (z / (1 + z) ^ 2) * Work.Spaces.Gam α θ) ^ 2
                * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
              mul_le_mul h2 h3 (sq_nonneg _) (by positivity)
          _ = K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
              rw [show (K1 * (z / (1 + z) ^ 2) * Work.Spaces.Gam α θ) ^ 2
                    * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                  = K1 ^ 2 * ((z / (1 + z) ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2)
                    * (Work.Spaces.Gam α θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from by ring,
                hsqw]
          _ ≤ K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
              rw [show K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  = (K1 ^ 2 * (1 / z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                    * (Work.Spaces.Gam α θ) ^ 2 from by ring]
              rw [show K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                    + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  = (K1 ^ 2 * (1 / z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                    * (Work.Spaces.Gam α θ
                      + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2 from by ring]
              exact mul_le_mul_of_nonneg_left hs2 (by positivity)
      have hZ : (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ 5 * (K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        calc (∑ i ∈ Finset.range (4 + 1),
              (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            ≤ ∑ _i ∈ Finset.range (4 + 1), K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
              Finset.sum_le_sum htermZ
          _ = 5 * (K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              norm_num
      -- the mixed slots
      have htermM : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (4 + 1),
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
            ≤ K2 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        intro i hi j hj
        split_ifs with hc
        · have hb := hK2 j i hc.1 hc.2 z hz θ hθoo
          have hpair0 : 0 ≤ K2 * (z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ
              + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
            mul_nonneg (mul_nonneg hK2pos.le hzs) hΓΛ0
          have h2 : (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) ^ 2
              ≤ (K2 * (z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) ^ 2 :=
            sq_le_sq.mpr (by rw [abs_of_nonneg hpair0]; exact hb)
          have h3 : (Work.Spaces.Wt α z θ) ^ 2
              = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            Wt_sq hsin0
          calc (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2
              = (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) ^ 2
                * (Work.Spaces.Wt α z θ) ^ 2 := by ring
            _ ≤ (K2 * (z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) ^ 2
                * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
                rw [h3]
                exact mul_le_mul h2 le_rfl (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin0 _)) (sq_nonneg _)
            _ = K2 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
                rw [show (K2 * (z / (1 + z) ^ 2) * (Work.Spaces.Gam α θ
                      + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) ^ 2
                      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                    = K2 ^ 2 * ((z / (1 + z) ^ 2) ^ 2 * (Work.Spaces.w z) ^ 2)
                      * (Work.Spaces.Gam α θ
                        + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from by ring,
                  hsqw]
        · exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity))
            (sq_nonneg _)) hS0
      have hM : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ 25 * (K2 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0))
            ≤ ∑ _i ∈ Finset.range (4 + 1), (∑ _j ∈ Finset.range (4 + 1), K2 ^ 2 * (1 / z) ^ 2
                * (Work.Spaces.Gam α θ
                  + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
              Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => htermM i hi j hj))
          _ = 25 * (K2 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range,
                nsmul_eq_mul, nsmul_eq_mul]
              norm_num
              ring
      rw [Work.Spaces.HkIntegrand]
      calc (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => Vs α Φs z θ * Gs α z θ) z θ
                  * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ 5 * (K1 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            + 25 * (K2 ^ 2 * (1 / z) ^ 2 * (Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := add_le_add hZ hM
        _ = (5 * K1 ^ 2 + 25 * K2 ^ 2) * (1 / z ^ 2) * ((Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              rw [div_pow, one_pow]
              ring
        _ ≤ ((5 * K1 ^ 2 + 25 * K2 ^ 2 + 1) * (1 / z ^ 2) + 1) * ((Work.Spaces.Gam α θ
                + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (sq_nonneg _) hS0)
              nlinarith [show (0 : ℝ) ≤ 1 / z ^ 2 by positivity]

/-! ## 5. Integrability of the angular slices -/

theorem integrableOn_slice_Vs_mul_Gs {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 4
        (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) Work.Spaces.Iθ := by
  obtain ⟨K, hK0, hK⟩ := Vs_mul_Gs_HkIntegrand_le (α := α) (Cs := Cs) (Φs := Φs) hα hs
  obtain ⟨hmaj1, hmaj2⟩ := theta_majorant_integrable (α := α) hα
  have hsm : Work.FTS.LocData.SmoothQuad (fun z θ => Vs α Φs z θ * Gs α z θ) :=
    Work.FTS.LocData.smoothQuad_mul (Vs_smoothQuad hα hs) (smoothQuad_Gs_of_pos hα)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4
      (fun z θ => Vs α Φs z θ * Gs α z θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 _ hsm
  intro z hz
  have hint : MeasureTheory.IntegrableOn (fun θ => K z * ((Work.Spaces.Gam α θ
      + (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) Work.Spaces.Iθ :=
    hmaj2.const_mul (K z)
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.HkIntegrand α 4
      (fun z θ => Vs α Φs z θ * Gs α z θ) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd _ hcont hz
  refine MeasureTheory.Integrable.mono' hint haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)]
  exact hK z (le_of_lt hz) θ hθ

/-! ## 6. The lower bound at the origin

For `V(Φ̃_*)` itself (not only its `z = 0` slice) the lower bound `c / z²` is available on a
*small* interval `(0,δ)` of `z` only: the Lipschitz control `|V(z,θ) − V(0,θ)| ≤ M·z` (from
`StarPkg.V`) degrades as `z → 1/2`.  That is all the non-integrability argument needs: `z ↦ 1/z²`
is non-integrable on `(0,δ)` for every `δ > 0`. -/

theorem slice_lower_bound_Vs {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (h0 : ∃ θ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧ Vs α Φs 0 θ ≠ 0) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ z : ℝ, 0 < z → z < δ →
      c / z ^ 2 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
        (fun z θ => Vs α Φs z θ * Gs α z θ) z θ := by
  obtain ⟨θ₀, hθ₀, hne⟩ := h0
  obtain ⟨a, b, c₀, ha0, haθ, hθb, hb, hc₀, hlow⟩ :=
    Vs0_interval_lower (α := α) (Cs := Cs) (Φs := Φs) hα hs hθ₀ hne
  have hcpos : 0 < Work.Spaces.c α := c_pos_of_pos hα
  have hlip := Vs_lipschitz (α := α) (Cs := Cs) (Φs := Φs) hα hs
  have hM0 : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right _ _) hα.le
  have hden : 0 < 2 * (max Cs 0 * α + 1) := by linarith
  have hδpos : 0 < min (1 / 2 : ℝ) (c₀ / (2 * (max Cs 0 * α + 1))) :=
    lt_min (by norm_num) (div_pos hc₀ hden)
  -- the Lipschitz bound gives `|V(z,θ)| ≥ c₀/2` on `(a,b)` as long as `z` is small
  have hlow2 : ∀ z : ℝ, 0 < z → z < min (1 / 2 : ℝ) (c₀ / (2 * (max Cs 0 * α + 1))) →
      ∀ θ : ℝ, θ ∈ Set.Ioo a b → c₀ / 2 ≤ |Vs α Φs z θ| := by
    intro z hz0 hzmin θ hθ
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz0
    have h1 : |Vs α Φs z θ - Vs α Φs 0 θ| ≤ max Cs 0 * α * z :=
      hlip z hzI θ ⟨by linarith [hθ.1, ha0], by linarith [hθ.2, hb]⟩
    have h2 : c₀ ≤ |Vs α Φs 0 θ| := hlow θ hθ
    have h3 : |Vs α Φs 0 θ| ≤ |Vs α Φs z θ - Vs α Φs 0 θ| + |Vs α Φs z θ| := by
      have h := abs_add_le (Vs α Φs 0 θ - Vs α Φs z θ) (Vs α Φs z θ)
      rw [sub_add_cancel] at h
      rwa [abs_sub_comm] at h
    have hzle : z ≤ c₀ / (2 * (max Cs 0 * α + 1)) :=
      le_trans (le_of_lt hzmin) (min_le_right _ _)
    have h4 : max Cs 0 * α * z ≤ c₀ / 2 := by
      refine le_trans (mul_le_mul_of_nonneg_left hzle hM0) ?_
      have h5 : max Cs 0 * α * (c₀ / (2 * (max Cs 0 * α + 1)))
          = (max Cs 0 * α / (max Cs 0 * α + 1)) * (c₀ / 2) := by
        field_simp
      rw [h5]
      refine mul_le_of_le_one_left (by linarith) ?_
      rw [div_le_one (by linarith)]
      linarith
    linarith
  have hcb : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hb]⟩
  have hsa0 : 0 ≤ Real.sin a :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [ha0]) (by linarith [hb, Real.pi_pos])).le
  have hg₀pos : 0 < (Real.sin a * Real.cos b ^ 2) ^ (α / 3) := by
    refine Real.rpow_pos_of_pos ?_ _
    have hsa : 0 < Real.sin a :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ha0]) (by linarith [hb, Real.pi_pos])
    positivity
  have hGam_low : ∀ θ ∈ Set.Ioo a b, (Real.sin a * Real.cos b ^ 2) ^ (α / 3)
      ≤ Work.Spaces.Gam α θ := by
    intro θ hθ
    have hsa0' : 0 ≤ Real.sin a * Real.cos b ^ 2 := mul_nonneg hsa0 (sq_nonneg _)
    have hsb : Real.sin a * Real.cos b ^ 2 ≤ Real.sin θ * Real.cos θ ^ 2 := by
      have hsp : Real.sin a ≤ Real.sin θ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (x := a) (y := θ)
          (by linarith [ha0, Real.pi_pos]) (le_of_lt (lt_trans hθ.2 hb)) (le_of_lt hθ.1)
      have hcθ : 0 ≤ Real.cos θ :=
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩).le
      have hc : Real.cos b ^ 2 ≤ Real.cos θ ^ 2 := by
        have h1 : Real.cos b ≤ Real.cos θ :=
          Real.cos_le_cos_of_nonneg_of_le_pi (x := θ) (y := b)
            (le_of_lt (lt_trans ha0 hθ.1)) (by linarith [hb, Real.pi_pos]) (le_of_lt hθ.2)
        nlinarith [h1, hcb.le, hcθ]
      exact mul_le_mul hsp hc (sq_nonneg _)
        (Real.sin_nonneg_of_mem_Icc ⟨le_of_lt (lt_trans ha0 hθ.1),
          by linarith [hθ.2, hb, Real.pi_pos]⟩)
    rw [Work.Spaces.Gam]
    exact Real.rpow_le_rpow hsa0' hsb (by linarith)
  set K₀ : ℝ := (c₀ / 2) * (α * ((Real.sin a * Real.cos b ^ 2) ^ (α / 3))
      / Work.Spaces.c α) * (1 / 4) with hK₀def
  have hK₀pos : 0 < K₀ := by
    rw [hK₀def]
    refine mul_pos (mul_pos (by linarith) (div_pos (mul_pos hα hg₀pos) hcpos)) (by norm_num)
  have hb_a : 0 < b - a := by linarith [haθ, hθb]
  refine ⟨(b - a) * K₀ ^ 2, min (1 / 2 : ℝ) (c₀ / (2 * (max Cs 0 * α + 1))),
    mul_pos hb_a (pow_pos hK₀pos 2), hδpos, ?_⟩
  intro z hz0 hzδ
  have hz1 : z < 1 / 2 := lt_of_lt_of_le hzδ (min_le_left _ _)
  have hint := integrableOn_slice_Vs_mul_Gs (α := α) (Cs := Cs) (Φs := Φs) hα hs z hz0
  have hw0z : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]; exact div_nonneg (by positivity) (by positivity)
  have hpt : ∀ θ ∈ Set.Ioo a b,
      K₀ ^ 2 / z ^ 2 ≤ ((fun z θ => Vs α Φs z θ * Gs α z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    intro θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ :=
      ⟨le_of_lt (lt_trans ha0 hθ.1), le_of_lt (lt_trans hθ.2 hb)⟩
    have hGamθ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθI).1
    have hX0 : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hX1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsp : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hX0 _
    have hsp1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one hX0.le hX1 (by rw [Work.Spaces.eta]; norm_num)
    have hprof : z / 4 ≤ |prof z| := by
      have h1 : 0 ≤ 2 * z * (1 - z) := by nlinarith [hz0, hz1]
      have h2 : 0 < (1 + z) ^ 3 := pow_pos (by linarith) 3
      rw [prof, abs_of_nonneg (div_nonneg h1 h2.le), le_div_iff₀ h2]
      have h3 : (1 + z) ^ 3 ≤ 27 / 8 := by
        have h4 : 1 + z ≤ 3 / 2 := by linarith
        nlinarith [hz0, sq_nonneg (1 + z), h4]
      nlinarith [hz0, hz1, h3]
    have hVslow : c₀ / 2 ≤ |Vs α Φs z θ| := hlow2 z hz0 hzδ θ hθ
    have hGslow : (α * ((Real.sin a * Real.cos b ^ 2) ^ (α / 3)) / Work.Spaces.c α) * (z / 4)
        ≤ |Gs α z θ| := by
      rw [Gs_eq_prof hα (by linarith : (-1 : ℝ) < z), abs_mul,
        abs_of_nonneg (div_nonneg (mul_nonneg hα.le hGamθ0) hcpos.le)]
      have hΓθ : (Real.sin a * Real.cos b ^ 2) ^ (α / 3) ≤ Work.Spaces.Gam α θ :=
        hGam_low θ hθ
      have h1 : α * ((Real.sin a * Real.cos b ^ 2) ^ (α / 3)) / Work.Spaces.c α
          ≤ α * Work.Spaces.Gam α θ / Work.Spaces.c α :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΓθ hα.le) hcpos.le
      exact mul_le_mul h1 hprof (by positivity) (by positivity)
    have hw : 1 / z ^ 2
        ≤ |Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)| := by
      have hw1 : 1 / z ^ 2 ≤ Work.Spaces.w z := by
        rw [Work.Spaces.w, le_div_iff₀ (by positivity : (0 : ℝ) < z ^ 2)]
        rw [div_mul_cancel₀ 1 (ne_of_gt (by positivity : (0 : ℝ) < z ^ 2))]
        nlinarith [hz0]
      have hprod : 0 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
        div_nonneg hw0z hsp.le
      rw [abs_of_nonneg hprod]
      have h2 : Work.Spaces.w z ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
        rw [le_div_iff₀ hsp]
        nlinarith [hw0z, hsp1]
      linarith
    have hf : K₀ / z
        ≤ |(fun z θ => Vs α Φs z θ * Gs α z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
      have h1 : K₀ * z ≤ |Vs α Φs z θ * Gs α z θ| := by
        rw [abs_mul]
        calc K₀ * z
            = (c₀ / 2) * ((α * ((Real.sin a * Real.cos b ^ 2) ^ (α / 3))
                / Work.Spaces.c α) * (z / 4)) := by rw [hK₀def]; ring
          _ ≤ |Vs α Φs z θ| * |Gs α z θ| :=
              mul_le_mul hVslow hGslow (by positivity) (abs_nonneg _)
      calc K₀ / z = (K₀ * z) * (1 / z ^ 2) := by field_simp
        _ ≤ |Vs α Φs z θ * Gs α z θ| * |Work.Spaces.w z
              / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)| :=
            mul_le_mul h1 hw (by positivity) (abs_nonneg _)
        _ = |(fun z θ => Vs α Φs z θ * Gs α z θ) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))| := by
            simp only [abs_mul]
    have hsq : (K₀ / z) ^ 2
        ≤ ((fun z θ => Vs α Φs z θ * Gs α z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      refine sq_le_sq.mpr ?_
      rw [abs_of_pos (div_pos hK₀pos hz0)]
      exact hf
    rwa [div_pow] at hsq
  have hstep : (∫ θ in Work.Spaces.Iθ,
        (Set.Ioo a b).indicator (fun _ => K₀ ^ 2 / z ^ 2) θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (fun z θ => Vs α Φs z θ * Gs α z θ) z θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hint ?_
    · refine Eventually.of_forall fun θ => ?_
      by_cases h : θ ∈ Set.Ioo a b
      · rw [Set.indicator_of_mem h]; positivity
      · rw [Set.indicator_of_notMem h]; exact le_refl 0
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      by_cases h : θ ∈ Set.Ioo a b
      · rw [Set.indicator_of_mem h]
        exact le_trans (hpt θ h)
          (Work.Spaces.sq_le_HkIntegrand_z α 4
            (fun z θ => Vs α Φs z θ * Gs α z θ) z θ 0 (by norm_num))
      · rw [Set.indicator_of_notMem h]
        exact Work.Spaces.HkIntegrand_nonneg α 4 _ z θ
  have hval : (∫ θ in Work.Spaces.Iθ,
        (Set.Ioo a b).indicator (fun _ => K₀ ^ 2 / z ^ 2) θ)
      = (b - a) * (K₀ ^ 2 / z ^ 2) := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    have hsub : Set.Ioo a b ⊆ Work.Spaces.Iθ := fun θ h =>
      ⟨le_of_lt (lt_trans ha0 h.1), le_of_lt (lt_trans h.2 hb)⟩
    rw [MeasureTheory.setIntegral_const]
    have hreal : (MeasureTheory.volume.restrict Work.Spaces.Iθ).real (Set.Ioo a b) = b - a := by
      rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.restrict_apply measurableSet_Ioo,
        Set.inter_eq_left.mpr hsub, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    rw [hreal]
    ring
  rw [hval] at hstep
  simpa only [mul_div_assoc] using hstep

end HsZ

theorem HkSqZero {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs)
    (h0 : ∃ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs 0 θ ≠ 0) :
    Work.Spaces.HkSq α 4
      (fun z θ => Work.FTS.Nonlinear.Pieces.RNP.Vs α Φs z θ
        * Work.FTS.Nonlinear.Pieces.RNP.Gs α z θ) = 0 := by
  obtain ⟨c, δ, hcpos, hδpos, hclow⟩ :=
    HsZ.slice_lower_bound_Vs (α := α) (Cs := Cs) (Φs := Φs) hα hs h0
  have hnotint : ¬ MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
        (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) Work.Spaces.Iz := by
    intro hint
    have h1 : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
          (fun z θ => Vs α Φs z θ * Gs α z θ) z θ) (Set.Ioo 0 δ) :=
      hint.mono_set (fun z hz => le_of_lt hz.1)
    have h2 : MeasureTheory.IntegrableOn (fun z : ℝ => c / z ^ 2) (Set.Ioo 0 δ) := by
      refine MeasureTheory.Integrable.mono' h1 ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        exact continuousOn_const.div (continuousOn_id.pow 2)
          (fun z hz => pow_ne_zero 2 (ne_of_gt hz.1))
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ?_)
        have h0c : 0 ≤ c / z ^ 2 := by positivity
        have h0i : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
            (fun z θ => Vs α Φs z θ * Gs α z θ) z θ :=
          integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ
        simpa only [Real.norm_of_nonneg h0c, Real.norm_of_nonneg h0i] using hclow z hz.1 hz.2
    have h3 : MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (-(2 : ℝ))) (Set.Ioo 0 δ) := by
      have h4 : MeasureTheory.IntegrableOn (fun z : ℝ => c⁻¹ * (c / z ^ 2))
          (Set.Ioo 0 δ) := h2.const_mul c⁻¹
      refine h4.congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun z hz => ?_)
      have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hz.1)
      have hcz : c ≠ 0 := ne_of_gt hcpos
      show c⁻¹ * (c / z ^ 2) = z ^ (-(2 : ℝ))
      rw [Real.rpow_neg (le_of_lt hz.1) 2, Real.rpow_two, div_eq_mul_inv]
      field_simp
    have h5 : ¬ MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (-(2 : ℝ)))
        (Set.Ioo 0 δ) := by
      rw [intervalIntegral.integrableOn_Ioo_rpow_iff hδpos]
      norm_num
    exact h5 h3
  rw [Work.Spaces.HkSq]
  exact MeasureTheory.integral_undef hnotint

end Work.FTS.Nonlinear.Pieces.RNP.row19
