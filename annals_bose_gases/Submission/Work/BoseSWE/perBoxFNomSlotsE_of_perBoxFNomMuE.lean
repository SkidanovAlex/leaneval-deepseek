import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseSWE.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# F3c of the `BoseSWE` route: the slot doubling *with the vanishing slack*

Recipe (`Submission/Work/BoseSWE/BRIEF.md` §7, second bullet): copy
`Work.BoseB1Cube.perBoxFNomSlots_of_slotMu` and `Work.BoseB1Cube.perBoxFNom_slots_of_row`
(`Submission/Work/BoseB1Cube/nomRouteCube.lean` §4), carrying the slack
`− ErrE v CE μ n · ‖Φ‖²` through both steps.

The two steps are

* the **weakening** `(c₁, C) ↦ (min c₁ (5/2), max C 1)`, which only uses that
  `min c₁ (5/2) ≤ c₁` and `C ≤ max C 1` (both factors enter the row linearly, the first with a
  positive coefficient, the second with a negative one), and
* the **slot doubling** `Work.BoseB1Cube.perBoxFNom_slots_of_row`: from the row at the slot `μ`
  with `c₁ ≤ 5/2`, the *same* state satisfies the row at both slots `μ` and `4μ` at the common
  constants `(min (c₁/4) (5/2), max C 1)`, because the `4μ`-row's `F`-term is
  `(c₁/4)·W·A₄` with `A₄ ≤ 4A + 12μ²‖Φ‖²` (`Work.BoseB1Cube.PsiWeightFourIntegral`, i.e. the
  integral form of `ψ(1,4μ,t) ≤ 4ψ(1,μ,t) + 12μ²`) and the `−½(4μ)²W‖Φ‖²` term is four times more
  negative than its `μ`-twin.

The slack `ErrE v CE μ n · normB v μ n Φ` involves neither `c₁`, `C` nor `μp`, and is the *same
literal term* on both sides of each step, so both steps are pure arithmetic in `c₁`, `C`, `μp` on
top of the PROVED twin `Work.BoseB1Cube.perBoxFNom_slots_of_row`: the slack only ever appears as a
common additive constant, which `linarith` carries automatically.

The caller passes `Work.BoseB1Cube.psiWeightFourIntegral_holds` (PROVED) as `hint`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The E-twin of `Work.BoseB1Cube.perBoxFNom_slots_of_row`.**  From the per-box row at the
slot `μ` (with the slack `ErrE v CE μ n · ‖Φ‖²` on its left side) and `c₁ ≤ 5/2`, the *same*
state satisfies the row at **both** slots `μ` and `4μ` at the common constants
`(min (c₁/4) (5/2), max C 1)`, with the **same** slack.

The proof is the twin's, verbatim: the slack is a common additive constant (it does not involve
`c₁`, `C` or `μp`), so every one of the twin's `linarith`/`nlinarith` steps applies after the slack
is abstracted as a single variable. -/
private theorem perBoxFNomE_slots_of_row {v : E3 → ℝ} {h : ScatSol v} {R c₁ C CE μ : ℝ} {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) {u : E3}
    (hint : Work.BoseB1Cube.PsiWeightFourIntegral) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hℓ : 0 < sideAt μ (a v)) (hd : 0 < (paramsAt μ (a v)).d)
    (hV : 0 < Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
    (hμ : 0 < μ) (hav : 0 ≤ a v) (hc₁ : 0 ≤ c₁) (hc₁2 : c₁ ≤ 5 / 2) (hC : 0 ≤ C)
    (hrow : PerBoxFNomE v h R c₁ C CE μ μ n Φ u) :
    PerBoxFNomE v h R (min (c₁ / 4) (5 / 2)) (max C 1) CE μ μ n Φ u ∧
    PerBoxFNomE v h R (min (c₁ / 4) (5 / 2)) (max C 1) CE (4 * μ) μ n Φ u := by
  unfold PerBoxFNomE at hrow ⊢
  unfold Work.BoseBoxFix.normB Work.BoseKinLoc.sqNormB at hrow ⊢
  set W : ℝ := Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
    (paramsAt μ (a v)).d u with hWdef
  set χ : ℝ := Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
    (paramsAt μ (a v)).d u with hχdef
  set N : ℝ := ∫ x in abox n (sideAt μ (a v)), ((Φ : X n → ℝ) x) ^ 2 with hNdef
  set S : ℝ := ErrE v CE μ n * N with hSdef
  set A : ℝ := ∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
    Work.SmallBoxSliding.psiWeight 1 μ
      (Work.BoseB1Cube.boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
        / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) with hAdef
  set A4 : ℝ := ∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
    Work.SmallBoxSliding.psiWeight 1 (4 * μ)
      (Work.BoseB1Cube.boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
        / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) with hA4def
  set Γ : ℝ := (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
    + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) with hΓdef
  have hW0 : 0 ≤ W := by
    rw [hWdef]
    exact w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hN0 : 0 ≤ N := by
    rw [hNdef]
    exact integral_nonneg fun x => sq_nonneg _
  have hχ0 : 0 ≤ χ := by
    rw [hχdef]
    exact Work.SmallBoxSliding.chiMass_nonneg _ _ _ u
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    refine integral_nonneg fun x => mul_nonneg (sq_nonneg _) ?_
    exact Work.BoseB1Cube.psiWeight_nonneg' hμ
      (div_nonneg (Work.BoseB1Cube.boxIndCount_nonneg _ _ _ _) hV.le)
  have hA40 : 0 ≤ A4 := by
    rw [hA4def]
    refine integral_nonneg fun x => mul_nonneg (sq_nonneg _) ?_
    exact Work.BoseB1Cube.psiWeight_nonneg' (by linarith)
      (div_nonneg (Work.BoseB1Cube.boxIndCount_nonneg _ _ _ _) hV.le)
  have hΓ0 : 0 ≤ Γ := by
    rw [hΓdef]
    refine add_nonneg (sq_nonneg _) ?_
    refine mul_nonneg (pow_nonneg ?_ 3) (Real.rpow_nonneg (by positivity) _)
    rw [Work.BoseFixB1.KB_eq_fsXp μ (a v)]
    exact Work.BoseBox.fsXp_nonneg (t := μ * (a v) ^ 3) (c := -6)
      (mul_nonneg hμ.le (pow_nonneg hav 3))
  have hkey : A4 ≤ 4 * A + 12 * μ ^ 2 * N := by
    rw [hA4def, hAdef, hNdef]
    exact hint (sideAt μ (a v)) (paramsAt μ (a v)).d μ u n (Φ : X n → ℝ)
      hℓ hd hμ hV (Φ.contDiff.continuous)
  have h4 : min (c₁ / 4) (5 / 2) ≤ c₁ / 4 := min_le_left _ _
  have h4nn : 0 ≤ min (c₁ / 4) (5 / 2) := le_min (by linarith) (by norm_num)
  have hC4C : C ≤ max C 1 := le_max_left C 1
  have hC41 : (1 : ℝ) ≤ max C 1 := le_max_right C 1
  have hC40 : 0 ≤ max C 1 := le_trans hC hC4C
  have hWA : 0 ≤ W * A := mul_nonneg hW0 hA0
  have hWA4 : 0 ≤ W * A4 := mul_nonneg hW0 hA40
  have hH1 : 0 ≤ μ ^ 2 * (a v) * Γ * χ * N :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav) hΓ0) hχ0) hN0
  have hH2 : 0 ≤ μ * (a v) * N := mul_nonneg (mul_nonneg hμ.le hav) hN0
  have maxid : max (max C 1) 1 = max C 1 := max_eq_left (le_max_right C 1)
  constructor
  · -- the `μ` row at `(min (c₁/4) (5/2), max C 1)`: only the `min` and the `max` move
    have h1 : min (c₁ / 4) (5 / 2) * (W * A) ≤ c₁ * (W * A) :=
      mul_le_mul_of_nonneg_right (by linarith [h4, hc₁]) hWA
    have h2 : C * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N)
        ≤ max C 1 * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N) :=
      mul_le_mul_of_nonneg_right hC4C (add_nonneg hH1 hH2)
    linarith [hrow, h1, h2]
  · -- the `4μ` row at the same constants
    have hstep : min (c₁ / 4) (5 / 2) * (W * A4)
        ≤ c₁ * (W * A) + 3 * c₁ * (μ ^ 2 * (W * N)) := by
      have h1 : min (c₁ / 4) (5 / 2) * (W * A4) ≤ (c₁ / 4) * (W * A4) :=
        mul_le_mul_of_nonneg_right h4 hWA4
      have h2 : (c₁ / 4) * (W * A4) ≤ (c₁ / 4) * (W * (4 * A + 12 * μ ^ 2 * N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hkey hW0) (by linarith)
      have h3 : (c₁ / 4) * (W * (4 * A + 12 * μ ^ 2 * N))
          = c₁ * (W * A) + 3 * c₁ * (μ ^ 2 * (W * N)) := by ring
      linarith [h1, h2, h3.le, h3.ge]
    have h3 : 3 * c₁ * (μ ^ 2 * (W * N)) - 8 * (μ ^ 2 * (W * N))
        ≤ -(1 / 2) * (μ ^ 2 * (W * N)) := by
      have hWN : 0 ≤ μ ^ 2 * (W * N) := mul_nonneg (sq_nonneg μ) (mul_nonneg hW0 hN0)
      nlinarith [hWN, hc₁2]
    have h4' : C * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N)
        ≤ max C 1 * (16 * (μ ^ 2 * (a v) * Γ * χ * N) + 4 * (μ * (a v) * N)) := by
      have b1 : C * (μ ^ 2 * (a v) * Γ * χ * N)
          ≤ max C 1 * (16 * (μ ^ 2 * (a v) * Γ * χ * N)) := by
        calc C * (μ ^ 2 * (a v) * Γ * χ * N)
            ≤ max C 1 * (μ ^ 2 * (a v) * Γ * χ * N) := mul_le_mul_of_nonneg_right hC4C hH1
          _ ≤ max C 1 * (16 * (μ ^ 2 * (a v) * Γ * χ * N)) :=
              mul_le_mul_of_nonneg_left (by linarith) hC40
      have b2 : C * (μ * (a v) * N) ≤ max C 1 * (4 * (μ * (a v) * N)) := by
        calc C * (μ * (a v) * N) ≤ max C 1 * (μ * (a v) * N) := mul_le_mul_of_nonneg_right hC4C hH2
          _ ≤ max C 1 * (4 * (μ * (a v) * N)) :=
              mul_le_mul_of_nonneg_left (by linarith) hC40
      have expand : C * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N)
          = C * (μ ^ 2 * (a v) * Γ * χ * N) + C * (μ * (a v) * N) := by ring
      have expand2 : max C 1 * (16 * (μ ^ 2 * (a v) * Γ * χ * N) + 4 * (μ * (a v) * N))
          = max C 1 * (16 * (μ ^ 2 * (a v) * Γ * χ * N))
            + max C 1 * (4 * (μ * (a v) * N)) := by
        ring
      rw [expand, expand2]
      linarith [b1, b2]
    have hp : min (c₁ / 4) (5 / 2) * (W * A4) - 1 / 2 * (4 * μ) ^ 2 * W * N
        - max C 1 * ((4 * μ) ^ 2 * (a v) * Γ * χ * N + (4 * μ) * (a v) * N)
        ≤ c₁ * (W * A) - 1 / 2 * μ ^ 2 * W * N
          - C * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N) := by
      have e1 : ((4 : ℝ) ^ 2) * (μ ^ 2 * (W * N)) = 16 * (μ ^ 2 * (W * N)) := by ring
      have hX : (4 * μ) ^ 2 * (a v) * Γ * χ * N = 16 * (μ ^ 2 * (a v) * Γ * χ * N) := by ring
      have hY : (4 * μ) * (a v) * N = 4 * (μ * (a v) * N) := by ring
      have hZ : (1 / 2 : ℝ) * (4 * μ) ^ 2 * W * N = 8 * (μ ^ 2 * (W * N)) := by ring
      rw [hX, hY, hZ]
      linarith [hstep, h3, h4']
    linarith [hp, hrow]

/-- **F3c of the `BoseSWE` route**: the slot doubling with the slack.  Recipe
(`Submission/Work/BoseSWE/BRIEF.md` §7, second bullet): copy
`Work.BoseB1Cube.perBoxFNomSlots_of_slotMu` and `Work.BoseB1Cube.perBoxFNom_slots_of_row`
(`Submission/Work/BoseB1Cube/nomRouteCube.lean` §4).  The `4μ`-row follows from the `μ`-row at
`c₁ ↦ min (c₁/4) (5/2)`, `C ↦ max C 1` via the PROVED pointwise `psiWeight_four_le` instantiating
the hypothesis `hint`; the slack `−ErrE v CE μ n·normB` involves neither `c₁`, `C` nor `μp`, so it
is carried **unchanged** (both steps are pure arithmetic in `c₁`, `C`, `μp` on top of the twin).
The caller passes `Work.BoseB1Cube.psiWeightFourIntegral_holds` (PROVED) as `hint`. -/
theorem perBoxFNomSlotsE_of_perBoxFNomMuE {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hint : Work.BoseB1Cube.PsiWeightFourIntegral)
    (hMu : Work.BoseSWE.PerBoxFNomMuE v h R) :
    Work.BoseSWE.PerBoxFNomSlotsE v h R := by
  obtain ⟨ε₀, c₁, C, CE, hε₀, hc₁, hC, hCE, hrow⟩ := hMu
  refine ⟨ε₀, min (min c₁ (5 / 2) / 4) (5 / 2), max C 1, CE, hε₀, ?_, ?_, hCE, ?_⟩
  · exact lt_min (by positivity) (by norm_num)
  · exact le_trans hC (le_max_left C 1)
  · intro μ hAdm n Φ u hu μp hμp
    have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
    have hd : 0 < (paramsAt μ (a v)).d := Work.BoseFixB1.adm_d_pos hAdm
    have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
    have hV : 0 < Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u :=
      Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
    have hc10 : 0 ≤ min c₁ (5 / 2) := le_min hc₁.le (by norm_num)
    have hc125 : min c₁ (5 / 2) ≤ 5 / 2 := min_le_right c₁ (5 / 2)
    have hmax : max (max C 1) 1 = max C 1 := max_eq_left (le_max_right C 1)
    -- the source row weakened to `(min c₁ (5/2), max C 1)`, slack unchanged
    have hrow' : PerBoxFNomE v h R (min c₁ (5 / 2)) (max C 1) CE μ μ n Φ u := by
      have hsrc := hrow μ hAdm n Φ u hu
      unfold PerBoxFNomE at hsrc ⊢
      unfold Work.BoseBoxFix.normB Work.BoseKinLoc.sqNormB at hsrc ⊢
      set W : ℝ := Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u with hWdef
      set χ : ℝ := Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u with hχdef
      set N : ℝ := ∫ x in abox n (sideAt μ (a v)), ((Φ : X n → ℝ) x) ^ 2 with hNdef
      set S : ℝ := ErrE v CE μ n * N with hSdef
      set A : ℝ := ∫ x in abox n (sideAt μ (a v)), (Φ : X n → ℝ) x ^ 2 *
        Work.SmallBoxSliding.psiWeight 1 μ
          (Work.BoseB1Cube.boxIndCount (sideAt μ (a v)) (paramsAt μ (a v)).d u x
            / Work.SmallBoxSliding.boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) with hAdef
      set Γ : ℝ := (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
        + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) with hΓdef
      have hW0 : 0 ≤ W := by
        rw [hWdef]
        exact w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
      have hN0 : 0 ≤ N := by
        rw [hNdef]
        exact integral_nonneg fun x => sq_nonneg _
      have hA0 : 0 ≤ A := by
        rw [hAdef]
        refine integral_nonneg fun x => mul_nonneg (sq_nonneg _) ?_
        exact Work.BoseB1Cube.psiWeight_nonneg' hμ
          (div_nonneg (Work.BoseB1Cube.boxIndCount_nonneg _ _ _ _) hV.le)
      have hΓ0 : 0 ≤ Γ := by
        rw [hΓdef]
        refine add_nonneg (sq_nonneg _) ?_
        refine mul_nonneg (pow_nonneg ?_ 3)
          (Real.rpow_nonneg (mul_nonneg hμ.le
            (pow_nonneg (Work.BoseFixB1.adm_a_pos hAdm).le 3)) _)
        rw [Work.BoseFixB1.KB_eq_fsXp μ (a v)]
        exact Work.BoseBox.fsXp_nonneg (t := μ * (a v) ^ 3) (c := -6)
          (mul_nonneg hμ.le (pow_nonneg (Work.BoseFixB1.adm_a_pos hAdm).le 3))
      have hχ0 : 0 ≤ χ := by
        rw [hχdef]
        exact Work.SmallBoxSliding.chiMass_nonneg _ _ _ u
      have h1 : min c₁ (5 / 2) * (W * A) ≤ c₁ * (W * A) :=
        mul_le_mul_of_nonneg_right (min_le_left c₁ (5 / 2)) (mul_nonneg hW0 hA0)
      have hH1 : 0 ≤ μ ^ 2 * (a v) * Γ * χ * N :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ)
          (Work.BoseFixB1.adm_a_pos hAdm).le) hΓ0) hχ0) hN0
      have hH2 : 0 ≤ μ * (a v) * N :=
        mul_nonneg (mul_nonneg hμ.le (Work.BoseFixB1.adm_a_pos hAdm).le) hN0
      have h2 : C * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N)
          ≤ max C 1 * (μ ^ 2 * (a v) * Γ * χ * N + μ * (a v) * N) :=
        mul_le_mul_of_nonneg_right (le_max_left C 1) (add_nonneg hH1 hH2)
      linarith [hsrc, h1, h2]
    have hpair := perBoxFNomE_slots_of_row (Φ := Φ) (u := u) hint hv hvrad hR hv_supp hℓ hd hV hμ
      (Work.BoseFixB1.adm_a_pos hAdm).le hc10 hc125 (le_trans hC (le_max_left C 1)) hrow'
    rw [hmax] at hpair
    rcases hμp with h' | h'
    · subst h'
      exact hpair.1
    · subst h'
      exact hpair.2

end Work.BoseSWE
