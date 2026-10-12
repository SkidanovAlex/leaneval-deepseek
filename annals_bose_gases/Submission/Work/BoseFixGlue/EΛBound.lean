import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixGlue.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.EΛBound` — the box energy from the box theorem

FS's localisation comparison `compare_box_energy_v2` needs the **fibre bound**
(`C3` in the design, `Work.BoseKinLoc.Sector.fibre_bound_v3`), whose hypotheses are the two
bounded-below statements `hEo` (the per-sector box energies `EΛn m`) and `hEi` (the box Rayleigh
quotients over the relaxed class `BoxState m ℓ`).  This module shows that **`LHYBoxB` supplies
both**, and in the sharper form actually used by the wiring:

    `ℓ³·Λ(a v, C, η₀, μ) ≤ EΛ(μ) ≤ 0`   (for `Adm`, hence `min 0 EΛ = EΛ`).

The only arithmetic ingredient is `Λ ≤ 0` for small diluteness
(`Work.BoseFixGlue.Lambda_nonpos_of_small`), which handles the degenerate states of vanishing
box norm: for such a state `boxFormB Φ / sqNormB Φ = 0` (Mathlib's junk value), and `0 ≥ ℓ³Λ`.

These are the exact inputs of `fibre_bound_v3`'s `hEo`/`hEi`, so once that skeleton is closed the
fibre clause `Work.BoseFixGlue.FibreInput` follows.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixGlue

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Elementary facts -/

lemma sqNormB_nonneg (n : ℕ) (ℓ : ℝ) (Φ : X n → ℝ) : 0 ≤ sqNormB n ℓ Φ := by
  rw [sqNormB]
  exact integral_nonneg (fun x => sq_nonneg _)

lemma sideB_pos {v : ℝ³ → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) : 0 < ℓB v μ := by
  have ht : 0 < μ * (a v) ^ 3 := by positivity
  have hKl : 0 < (paramsAt μ (a v)).Kl := by
    dsimp [paramsAt, fsParams, fsXp]
    exact Real.rpow_pos_of_pos ht _
  exact boxSide_pos hμ hav hKl

/-- The FS box word at the projected parameters, box-restricted. -/
lemma wordB_eq_boxFormB (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) :
    wordB v h μ n Φ
      = boxFormB n v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) Φ := rfl

/-! ## 1. `EΛ` dominates `ℓ³Λ` -/

/-- **The box theorem bounds the box energy from below.**  From `LHYBoxB` (FS `thm:LHY-Box` on
symmetric box states, `n` free) one gets, uniformly in the particle number,
`ℓ(μ)³ Λ(a v, C, η₀, μ) ≤ E_Λ(μ)`, and the two bounded-below statements in the exact form of
`fibre_bound_v3`'s `hEo`/`hEi`. -/
theorem EΛ_ge_lambda_of_LHYBoxB {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hav : 0 < a v) (hC : 0 ≤ C) (hL : LHYBoxB v h η₀ C) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
      (ℓB v μ) ^ 3 * Lambda (a v) C η₀ μ
          ≤ EΛ v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) ∧
      (ℓB v μ) ^ 3 * Lambda (a v) C η₀ μ
          ≤ min 0 (EΛ v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ)) ∧
      BddBelow (Set.range (fun m : ℕ =>
          EΛn m v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ))) ∧
      (∀ m : ℕ, BddBelow (Set.range (fun Φ : BoxState m (ℓB v μ) =>
          boxFormB m v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) Φ
            / sqNormB m (ℓB v μ) Φ))) := by
  obtain ⟨ε₁, hε₁, hbox⟩ := hL
  obtain ⟨ε₂, hε₂, hΛ⟩ := Lambda_nonpos_of_small (a := a v) (C := C) (η₀ := η₀) hav hC
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun μ hμ => ?_⟩
  have hμpos : 0 < μ := hμ.1
  have hpar : ParamsOK (paramsAt μ (a v)) (μ * (a v) ^ 3) := hμ.2.2
  have hdil₁ : μ * (a v) ^ 3 ≤ ε₁ := le_trans hμ.2.1 (min_le_left _ _)
  have hdil₂ : μ * (a v) ^ 3 ≤ ε₂ := le_trans hμ.2.1 (min_le_right _ _)
  have hΛμ : Lambda (a v) C η₀ μ ≤ 0 := hΛ μ hμpos hdil₂
  have hℓ : 0 < ℓB v μ := sideB_pos hμpos hav
  have hle3 : 0 ≤ (ℓB v μ) ^ 3 := pow_nonneg hℓ.le 3
  -- the per-state bound
  have hper : ∀ (m : ℕ) (Φ : BoxState m (ℓB v μ)),
      (ℓB v μ) ^ 3 * Lambda (a v) C η₀ μ
        ≤ boxFormB m v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) Φ
            / sqNormB m (ℓB v μ) Φ := by
    intro m Φ
    by_cases hsq : sqNormB m (ℓB v μ) Φ = 0
    · rw [hsq, div_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hle3 hΛμ
    · have hsqpos : 0 < sqNormB m (ℓB v μ) Φ :=
        lt_of_le_of_ne (sqNormB_nonneg m (ℓB v μ) Φ) (Ne.symm hsq)
      have hb := hbox μ ⟨hμpos, hdil₁, hpar⟩ m Φ
      rw [BoxBoundB] at hb
      rw [normB_eq, wordB_eq_boxFormB] at hb
      rw [le_div_iff₀ hsqpos]
      exact hb
  have hEΛn : ∀ m : ℕ, (ℓB v μ) ^ 3 * Lambda (a v) C η₀ μ
      ≤ EΛn m v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) :=
    fun m => le_ciInf (hper m)
  have hbdd : BddBelow (Set.range (fun m : ℕ =>
      EΛn m v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ))) :=
    ⟨(ℓB v μ) ^ 3 * Lambda (a v) C η₀ μ, by rintro y ⟨m, rfl⟩; exact hEΛn m⟩
  have hEΛ : (ℓB v μ) ^ 3 * Lambda (a v) C η₀ μ
      ≤ EΛ v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) :=
    le_ciInf hEΛn
  have hmin : (ℓB v μ) ^ 3 * Lambda (a v) C η₀ μ
      ≤ min 0 (EΛ v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ)) :=
    le_min (mul_nonpos_of_nonneg_of_nonpos hle3 hΛμ) hEΛ
  exact ⟨hEΛ, hmin, hbdd, fun m => ⟨_, fun y hy => by
    obtain ⟨Φ, rfl⟩ := hy
    exact hper m Φ⟩⟩

/-- The two bounded-below inputs `hEo`, `hEi` of `fibre_bound_v3`, extracted from
`EΛ_ge_lambda_of_LHYBoxB`. -/
theorem hEo_hEi_of_LHYBoxB {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hav : 0 < a v) (hC : 0 ≤ C) (hL : LHYBoxB v h η₀ C) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
      BddBelow (Set.range (fun m : ℕ =>
        EΛn m v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ))) ∧
      (∀ m : ℕ, BddBelow (Set.range (fun Φ : BoxState m (ℓB v μ) =>
        boxFormB m v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) Φ
          / sqNormB m (ℓB v μ) Φ))) := by
  obtain ⟨ε₀, hε₀, h⟩ := EΛ_ge_lambda_of_LHYBoxB hav hC hL
  exact ⟨ε₀, hε₀, fun μ hμ => ⟨(h μ hμ).2.2.1, (h μ hμ).2.2.2⟩⟩

/-! ## 2. `EΛ ≤ 0`

The `n = 0` sector is trivial (`boxFormB 0 = 0` on symmetric states), so `EΛ ≤ 0`; this is the
sign input that makes `min 0 EΛ` equal to `EΛ` and is used by the sanity tests. -/

lemma potWordU_zero (v : ℝ³ → ℝ) (g : ℝ³ → ℝ) (ℓ μ : ℝ) (u : ℝ³) (x : X 0) :
    potWordU 0 v g ℓ μ u x = 0 := by
  rw [potWordU]
  simp

lemma boxFormB_zero (v : ℝ³ → ℝ) (g : ℝ³ → ℝ) (ℓ μ d s εT b : ℝ) (Φ : X 0 → ℝ) :
    boxFormB 0 v g ℓ μ d s εT b Φ = 0 := by
  rw [boxFormB, kinFormB]
  have h1 : (∑ i : Fin 0, ∫ x in abox 0 ℓ,
      indU ℓ 0 (x i) * fsT ℓ d s εT b 0 (fibre 0 i Φ x)) = 0 := by simp
  rw [h1, mul_zero, zero_add]
  have h2 : (fun x : X 0 => (Φ x) ^ 2 * potWordU 0 v g ℓ μ 0 x) = fun _ => (0 : ℝ) := by
    funext x
    rw [potWordU_zero, mul_zero]
  rw [h2, integral_zero]

lemma EΛn_zero_le (v : ℝ³ → ℝ) (g : ℝ³ → ℝ) (ℓ μ d s εT b : ℝ) :
    EΛn 0 v g ℓ μ d s εT b ≤ 0 := by
  let f : BoxState 0 ℓ → ℝ := fun Φ =>
    boxFormB 0 v g ℓ μ d s εT b (Φ : X 0 → ℝ) / sqNormB 0 ℓ (Φ : X 0 → ℝ)
  have hper : ∀ Φ : BoxState 0 ℓ, f Φ = 0 := by
    intro Φ
    show boxFormB 0 v g ℓ μ d s εT b (Φ : X 0 → ℝ) / sqNormB 0 ℓ (Φ : X 0 → ℝ) = 0
    rw [boxFormB_zero v g ℓ μ d s εT b (Φ : X 0 → ℝ), zero_div]
  have hbdd : BddBelow (Set.range f) := ⟨0, by rintro y ⟨Φ, rfl⟩; rw [hper Φ]⟩
  change (⨅ Φ : BoxState 0 ℓ, f Φ) ≤ 0
  exact le_trans (ciInf_le hbdd (⟨fun _ => 1, contDiff_const, fun σ x => rfl, one_ne_zero⟩ :
    BoxState 0 ℓ)) (le_of_eq (hper _))

/-- **`EΛ ≤ 0`** — used to turn `min 0 EΛ` into `EΛ`.  (The `n = 0` sector alone gives it, once
the box energies are known to be bounded below — which `LHYBoxB` provides.) -/
theorem EΛ_le_zero_of_LHYBoxB {v : ℝ³ → ℝ} {h : ScatSol v} {η₀ C : ℝ}
    (hav : 0 < a v) (hC : 0 ≤ C) (hL : LHYBoxB v h η₀ C) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
      EΛ v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) ≤ 0 ∧
      min 0 (EΛ v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ))
        = EΛ v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) := by
  obtain ⟨ε₀, hε₀, hres⟩ := EΛ_ge_lambda_of_LHYBoxB hav hC hL
  refine ⟨ε₀, hε₀, fun μ hμ => ?_⟩
  have hbdd := (hres μ hμ).2.2.1
  have hle : EΛ v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) ≤
      EΛn 0 v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) :=
    ciInf_le (f := fun m : ℕ =>
      EΛn m v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ)) hbdd 0
  have h0 := EΛn_zero_le v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ)
  have hz : EΛ v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) ≤ 0 :=
    le_trans hle h0
  exact ⟨hz, min_eq_right hz⟩

end Work.BoseFixGlue
