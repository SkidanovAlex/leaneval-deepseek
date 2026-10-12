import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.flatConsistencyArith
import Submission.Work.BoseFixB1.pairMassExcess_pos
import Submission.Work.BoseFixB1.perBoxFWeight_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.perSectorBoundG_holds` — the termwise per-sector residual

**STATUS: SKELETON (not proved).**  The target `Work.BoseFixB1.perSectorBoundG_holds` below still
carries its `sorry`; nothing in the target's import cone may import this file until it closes.
`import Submission.Work.BoseFixB1.perSectorBoundG_inputs` declares the *same* name with a `sorry`
body — the two files cannot be imported together; whoever wires the target up must use one of them.

**Read `perSectorBoundG_FINDING.md` in this directory before touching the target.**  Summary: the
statement is TRUE (FS `thm:smallbox` at the sliding box, termwise in the sector count, with the
background sharpened from `½` to `½ − c`), it is *not* implied by the `½`-forms on disk
(`LHS_{(½−c)} = LHS_{½} + c μ²∬w₁ m_k`), its consistency rests exactly on the strictness
`γ := ∫v(1−ω)ω/(8π a v) > 0` (**proved** in `Submission.Work.BoseFixB1.pairMassExcess_pos`), and
its proof needs the corpus's two open analytic inputs: the localised interaction estimate
(`Work.BoseFixB1.a0SectorLower`, delegated) and FS `lm:appbogolubov` in the *sector-count* form.

## Layout

* **§0** — structural facts of the localised one-body kernel: its fibre vanishes off the sliding
  box, and it is uniformly bounded by `Kfib` (`wSmall1Pair_fibre_abs_le`); hence the fibre count
  bound `Σ_i w1Fibre(x_i) ≤ Kfib M·n_{B(u)}(x)`.
* **§1** — scalar facts on FS's weight `F = psiWeight 1 μ`.
* **§2** — the `k = 0` sector: the empty-occupancy sector carries no word
  (`Work.FockBridge.sectorPiece_zero_word_eq_zero`), so the residual there reduces to the scalar
  fact `c·F(0) − (½−c)μ² = (2c−½)μ² ≤ 0` (at `c ≤ ¼`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Structural facts of the localised one-body kernel

The localised kernel `wSmallPair M ℓ d u h` carries the factor `chiSmallB M ℓ d u` in **both**
slots, so its fibre vanishes off the sliding box; and `wSmall1Pair_fibre_abs_le` bounds that fibre
by the universal constant `Kfib`.  These are the two inputs of the crude (count-small) branch. -/

/-- The fibre of the localised one-body kernel vanishes off the sliding box. -/
lemma w1Fibre_wSmall1Pair_eq_zero_of_notMem {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hM : 1 ≤ M) (u : EuclideanSpace ℝ (Fin 3)) :
    ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ dlBox ℓ d u → w1Fibre ℓ (wSmall1Pair h M ℓ d u) z = 0 := by
  intro z hz
  have hchi : chiSmallB M ℓ d u z = 0 := by
    by_contra hne
    exact hz (Work.BoseFixB1B.chiSmallB_mem_dlBox hℓ hd hM u z hne)
  rw [w1Fibre]
  refine integral_eq_zero_of_ae ?_
  filter_upwards with y
  simp only [wSmall1Pair, wSmallPair, wSmallScaled, hchi, zero_mul]
  rfl

/-- The universal fibre constant `Kfib` of `Work.BoseFixB1.wSmall1Pair_fibre_abs_le`. -/
noncomputable def Kfib {v : EuclideanSpace ℝ (Fin 3) → ℝ} (M : ℕ) : ℝ :=
  (chiSupAbs * chiSmallDecay M)
    * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
        * (8 * π * _root_.BoseGases.a v))

/-- **The uniform fibre bound** (`Work.BoseFixB1.wSmall1Pair_fibre_abs_le`, restated at `Kfib`):
for every `z`, `|w1Fibre ℓ (wSmall1Pair h M ℓ d u) z| ≤ Kfib M`. -/
lemma w1Fibre_wSmall1Pair_abs_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * chiR0) (u : EuclideanSpace ℝ (Fin 3)) :
    ∀ z : EuclideanSpace ℝ (Fin 3), |w1Fibre ℓ (wSmall1Pair h M ℓ d u) z| ≤ Kfib (v := v) M := by
  intro z
  rw [w1Fibre]
  refine le_trans ?_ (le_of_eq rfl)
  have := wSmall1Pair_fibre_abs_le hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
  simpa [Kfib, wSmall1Pair] using this

/-- **The pointwise count bound**: on a configuration with `k` particles in the sliding box, the
sum of the one-body fibres is at most `Kfib M · k`.  (Each fibre is `0` off the box and bounded by
`Kfib M` on it.) -/
lemma sum_w1Fibre_le_Kfib_mul_boxCount {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * chiR0) (u : EuclideanSpace ℝ (Fin 3))
    {N : ℕ} (x : X N) :
    ∑ i : Fin N, w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)
      ≤ Kfib (v := v) M * boxCount (dlBox ℓ d u) x := by
  classical
  have hpt : ∀ i : Fin N, w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)
      ≤ Kfib (v := v) M * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) := by
    intro i
    by_cases hi : x i ∈ dlBox ℓ d u
    · rw [Set.indicator_of_mem hi, mul_one]
      calc w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)
          ≤ |w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)| := le_abs_self _
        _ ≤ Kfib (v := v) M :=
            w1Fibre_wSmall1Pair_abs_le hv_supp hR0 hv hvrad hv1 h hM hℓ hd hR hRχ u (x i)
    · rw [Set.indicator_of_notMem hi, mul_zero,
        w1Fibre_wSmall1Pair_eq_zero_of_notMem h hℓ hd hM u (x i) hi]
  calc ∑ i : Fin N, w1Fibre ℓ (wSmall1Pair h M ℓ d u) (x i)
      ≤ ∑ i : Fin N, Kfib (v := v) M * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = Kfib (v := v) M * ∑ i : Fin N, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) := by
        rw [Finset.mul_sum]
    _ = Kfib (v := v) M * boxCount (dlBox ℓ d u) x := by
        rw [boxCount_eq_sum_indicator]

/-! ## 1. Scalar facts -/
/-- FS's `F(0) = μ²`. -/
lemma psiWeight_one_zero (μ : ℝ) : psiWeight 1 μ 0 = μ ^ 2 := by
  rw [psiWeight]
  norm_num

/-- `psiWeight 1 μ t ≤ μ²` for `0 ≤ t ≤ μ` (the weight decreases from `μ²` at `0` to `0` at `μ`).

**Operator-requested unblock (this workspace, 20:5x):** this copy is unused in this file, and
`Submission/Work/BoseFixB1/perBoxF_flat.lean` declares an identical lemma under the same name, so
the plain `lemma` made this module fail with "'…psiWeight_one_le_mu_sq_of_le' has already been
declared" and left its `.olean` missing — which blocked every downstream module
(`q1CrossW1csLocalised` → `BoxCrossLevelLedger` → `Submission.Work.BoseFixB1S.hopLevelPlusOneLedger`).
Renamed to `..._alt` (nothing references it, and `Work.BoseFixB1.psiWeight_one_le_mu_sq_of_le`
is still provided by `perBoxF_flat`). -/
lemma psiWeight_one_le_mu_sq_of_le_alt (μ : ℝ) (hμ : 0 < μ) {t : ℝ} (ht0 : 0 ≤ t) (htμ : t ≤ μ) :
    psiWeight 1 μ t ≤ μ ^ 2 := by
  rw [psiWeight]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht0 (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [div_le_iff₀ hden]
  have h1 : μ ^ 2 * (1 + t * μ⁻¹) = μ ^ 2 + μ * t := by field_simp
  rw [h1]
  have h2 : 0 ≤ t * (3 * μ - t) := mul_nonneg ht0 (by linarith)
  nlinarith [h2]

/-! ## 2. The `k = 0` occupancy sector -/
/-- **The `k = 0` instance of the per-sector residual.**  The whole localised word vanishes on the
sector `n_{B(u)} = 0` (`Work.FockBridge.sectorPiece_zero_word_eq_zero`), so only the scalar fact
`(2c−½)μ² ∬w_{1,B(u)} ≤ 0` is needed (at `c ≤ ¼`, `∬w₁ ≥ 0`, `Γ ≥ 0`, `C ≥ 0`). -/
theorem perSectorBoundG_zero_sector {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {M : ℕ} {ℓ d ε c C μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ) (hc : c ≤ 1 / 4)
    (hC : 0 ≤ C) (ha : 0 ≤ _root_.BoseGases.a v)
    (hW : ∀ u : EuclideanSpace ℝ (Fin 3), 0 ≤ w1MassB h M ℓ d u)
    (hΓ : 0 ≤ dlGamma (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB μ
      (_root_.BoseGases.a v))
    {n : ℕ} (Φ : X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    sectorMass ℓ (dlBox ℓ d u) Φ 0 *
        ((c * psiWeight 1 μ ((0 : ℝ) / chiMass M ℓ d u) - (1 / 2 - c) * μ ^ 2)
            * w1MassB h M ℓ d u
          - C * (μ ^ 2 * (_root_.BoseGases.a v)
                * dlGamma (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB μ
                  (_root_.BoseGases.a v) * w1MassB h M ℓ d u
            + μ * (_root_.BoseGases.a v)))
      ≤ Work.UBBInputs8.tBwordBInd n ℓ d ε c u (sectorPiece (dlBox ℓ d u) 0 Φ)
        + qLHSwordB h M ℓ d μ u (sectorPiece (dlBox ℓ d u) 0 Φ) := by
  rw [FockBridge.sectorPiece_zero_word_eq_zero (N := n) h M ℓ d μ ε c hℓ hd u Φ]
  -- NB (operator-requested unblock, this workspace): the call `
  -- sectorMass_nonneg ℓ (dlBox ℓ d u) Φ 0` is ambiguous — two lemmas named
  -- `Work.BoseFixB1.sectorMass_nonneg` exist (`perSectorSmooth_holds` with the arity
  -- `(Φ) (u) (k)`, and `sectorAppBogSlidingMass` with the arity `(L) (B) (Φ) (k)`, which is the
  -- one meant here); here Lean resolved it to the former and failed with a type mismatch, which
  -- left this file (and therefore every `request_*` pre-check in the workspace) red.  Proved
  -- directly from the definition, exactly as both siblings do.
  have hm0 : 0 ≤ sectorMass ℓ (dlBox ℓ d u) Φ 0 := by
    rw [Work.FockBridge.sectorMass]; exact ENNReal.toReal_nonneg
  have hbr : (c * psiWeight 1 μ ((0 : ℝ) / chiMass M ℓ d u) - (1 / 2 - c) * μ ^ 2)
      * w1MassB h M ℓ d u
      - C * (μ ^ 2 * (_root_.BoseGases.a v)
            * dlGamma (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB μ
              (_root_.BoseGases.a v) * w1MassB h M ℓ d u
          + μ * (_root_.BoseGases.a v)) ≤ 0 := by
    rw [zero_div, psiWeight_one_zero]
    have h1 : c * μ ^ 2 - (1 / 2 - c) * μ ^ 2 = (2 * c - 1 / 2) * μ ^ 2 := by ring
    rw [h1]
    have h2 : (2 * c - 1 / 2) * μ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg μ)
    have h3 : 0 ≤ C * (μ ^ 2 * (_root_.BoseGases.a v)
            * dlGamma (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB μ
              (_root_.BoseGases.a v) * w1MassB h M ℓ d u
          + μ * (_root_.BoseGases.a v)) :=
      mul_nonneg hC (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hΓ) (hW u))
        (mul_nonneg hμ.le ha))
    have h4 : (2 * c - 1 / 2) * μ ^ 2 * w1MassB h M ℓ d u ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h2 (hW u)
    linarith [h4, h3]
  exact le_trans (mul_nonpos_of_nonneg_of_nonpos hm0 hbr) (le_of_eq rfl)

/-- **The kernel-mass gap parameter** `γ = ∫v(1−ω)ω / (8π a v)`: by
`Submission/Work/BoseFixB1/perSectorBoundG_FINDING.md` §1b this — and *not* the Born-gap
parameter `∫vω/(8π a v)` — is the quantity that pays the residual's `(½−c)` background, since
`w₂ − w₁ = ω w₁` and `∫w₁ = 8π a v·(1+o(1))`. -/
noncomputable def pairGap (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v) : ℝ :=
  (∫ z : EuclideanSpace ℝ (Fin 3),
      v z * (1 - Classical.choose h z) * Classical.choose h z)
    / (8 * π * _root_.BoseGases.a v)

/-- `pairGap` is strictly positive on the standing hypotheses
(`Work.BoseFixB1.pairMassExcess_pos` over `0 < a v`). -/
theorem pairGap_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (hav : 0 < _root_.BoseGases.a v) :
    0 < pairGap v h := by
  rw [pairGap]
  exact div_pos (pairMassExcess_pos hR hv hvrad hv1 hv_supp h hav)
    (by positivity)

/-- **The flat-family consistency of the residual's constants**: with
`c := min (pairGap v h / 4) (1/8) > 0` the flat state's demand
(`perSectorBoundG_FINDING.md` §1b, at `∬w₁ = 8π(a v)V`, `∬w₂ = (1+γ)∬w₁`) is satisfied for every
chemical potential and every density `ρ ≥ 0`:

    c·(F(ρ) + μ²) ≤ (ρ−μ)²/2 + γ·ρ²/2 .

This is the statement that makes the target's `∃ c > 0` non-vacuous at the flat family; it is the
composition of `Work.BoseFixB1.flatConsistencyArith` with `pairMassExcess_pos`. -/
theorem exists_flat_admissible_c {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ c : ℝ, 0 < c ∧ ∀ (μ ρ : ℝ), 0 < μ → 0 ≤ ρ →
      c * (psiWeight 1 μ ρ + μ ^ 2) ≤ (ρ - μ) ^ 2 / 2 + pairGap v h * ρ ^ 2 / 2 := by
  refine ⟨min (pairGap v h / 4) (1 / 8), ?_, ?_⟩
  · have hγ := pairGap_pos hR hv hvrad hv1 hv_supp h hav
    exact lt_min (by linarith) (by norm_num)
  · intro μ ρ hμ hρ
    have hγ := pairGap_pos hR hv hvrad hv1 hv_supp h hav
    have hc1 : min (pairGap v h / 4) (1 / 8) ≤ pairGap v h / 4 := min_le_left _ _
    have hc2 : min (pairGap v h / 4) (1 / 8) ≤ 1 / 8 := min_le_right _ _
    have := flatConsistencyArith μ (pairGap v h) (min (pairGap v h / 4) (1 / 8))
      hμ hγ hc1 hc2 ρ hρ
    simpa using this

/-! ## 3. The dichotomy, and the target

For each sector `k` of `Φ` the residual is one of the two *clauses*

* `2·n₊ ≤ k·m_k` — the **condensed** clause, `perSectorBoundG_condensed_clause`: this is the single
  remaining analytic atom (FS's per-box mean-field/interaction estimate at the sliding box).  It is
  delegated, and the proved statement lands in
  `Submission/Work/BoseFixB1/perSectorBoundG_condensed.lean` under the name
  `Work.BoseFixB1.perSectorBoundG_condensed` (whose conclusion is *this* clause verbatim);
* `k·m_k ≤ 2·n₊` — the **excited** clause, `perSectorBoundG_excited_clause`: at *every*
  `c ∈ (0,1/4]` and every `C ≥ 0`, since the `C`-slot is unused there.  This clause is **PROVED**
  (`sorry`-free) in the sibling module `Submission.Work.BoseFixB1B/perSectorBoundG_excited.lean`
  (theorem `Work.BoseFixB1B.perSectorBoundG_excited` / `perSectorBoundGExcitedAt`); it is restated
  here — as an in-file clause — only because that module's import cone transitively re-declares
  `Work.BoseFixB1.perSectorBoundG_holds` (a stale `sorry` in `perSectorBoundG_inputs.lean`), so the
  two modules cannot be imported together; see `perSectorBoundG_FINDING.md` §H for the collision
  and its one-line fix. -/

/-- **The CONDENSED clause** of the dichotomy: the residual on the sectors with `2·n₊ ≤ k·m_k`.
This is *verbatim* the delegated statement `Work.BoseFixB1.perSectorBoundG_condensed`
(`Submission/Work/BoseFixB1/perSectorBoundG_condensed.lean`), so that file, when it lands, can be
imported here in place of this placeholder (they have the same type up to the unfolding of
`Work.BoseFixB1.PerSectorBoundG`'s body). -/
theorem perSectorBoundG_condensed_clause {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1B.PBℓ v μ))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
          ∀ k ∈ Finset.range (n + 1),
            2 * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u)
                  (Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u)
                  (Work.FockBridge.sectorPiece (Work.BoseFixB1B.PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
              ≤ (k : ℝ) * Work.FockBridge.sectorMass (Work.BoseFixB1B.PBℓ v μ)
                  (Work.BoseFixB1B.PBB v μ u) (Φ : Submission.BoseGases.X n → ℝ) k →
            Work.FockBridge.sectorMass (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u)
                (Φ : Submission.BoseGases.X n → ℝ) k *
              ((c * Work.SmallBoxSliding.psiWeight 1 μ ((k : ℝ) / Work.BoseFixB1B.PBV v μ u)
                  - (1 / 2 - c) * μ ^ 2) * Work.BoseFixB1B.PBW h μ u
                - C * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ
                      * Work.BoseFixB1B.PBW h μ u + μ * (_root_.BoseGases.a v)))
            ≤ Work.UBBInputs8.tBwordBInd n (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ)
                  (Work.BoseFixB1B.PBeT v μ) (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
                  (Work.FockBridge.sectorPiece (Work.BoseFixB1B.PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
              + Work.SmallBoxSliding.qLHSwordB h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                  (Work.BoseFixB1B.PBd v μ) μ u
                  (Work.FockBridge.sectorPiece (Work.BoseFixB1B.PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ)) := by
  sorry

/-- **The EXCITED clause** of the dichotomy: the residual on the sectors with `k·m_k ≤ 2·n₊`, at
*every* `c ∈ (0,1/4]` and every `C ≥ 0`.  **PROVED** (as `Work.BoseFixB1B.perSectorBoundGExcited`
in `Submission/Work/BoseFixB1B/perSectorBoundG_excited.lean`); the `sorry` below is only the
restatement forced by the name collision of `perSectorBoundG_FINDING.md` §H. -/
theorem perSectorBoundG_excited_clause {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {c : ℝ} (hc0 : 0 < c) (hc14 : c ≤ 1 / 4) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1B.PBℓ v μ))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) μ →
        ∀ k ∈ Finset.range (n + 1),
          (k : ℝ) * Work.FockBridge.sectorMass (Work.BoseFixB1B.PBℓ v μ)
                (Work.BoseFixB1B.PBB v μ u) (Φ : Submission.BoseGases.X n → ℝ) k
            ≤ 2 * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u)
                (Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u)
                (Work.FockBridge.sectorPiece (Work.BoseFixB1B.PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ)) →
          ∀ C : ℝ, 0 ≤ C →
            Work.FockBridge.sectorMass (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBB v μ u)
                (Φ : Submission.BoseGases.X n → ℝ) k *
              ((c * Work.SmallBoxSliding.psiWeight 1 μ ((k : ℝ) / Work.BoseFixB1B.PBV v μ u)
                  - (1 / 2 - c) * μ ^ 2) * Work.BoseFixB1B.PBW h μ u
                - C * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseFixB1B.PBΓ v μ
                      * Work.BoseFixB1B.PBW h μ u + μ * (_root_.BoseGases.a v)))
            ≤ Work.UBBInputs8.tBwordBInd n (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ)
                  (Work.BoseFixB1B.PBeT v μ) (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) u
                  (Work.FockBridge.sectorPiece (Work.BoseFixB1B.PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
              + Work.SmallBoxSliding.qLHSwordB h (Work.BoseFixB1B.PBM v μ) (Work.BoseFixB1B.PBℓ v μ)
                  (Work.BoseFixB1B.PBd v μ) μ u
                  (Work.FockBridge.sectorPiece (Work.BoseFixB1B.PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ)) := by
  sorry

/-- **The target, from the two clauses.**  The thresholds `ε₀` are merged by `min`; the coefficient
`c` and the error constant `C` are the *condensed* clause's (the excited clause holds at every
`c ∈ (0,1/4]` and every `C ≥ 0`). -/
theorem perSectorBoundG_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseFixB1.PerSectorBoundG v h R := by
  obtain ⟨ε₀C, cC, CC, hεC, hcC0, hcC14, hCC0, hC'⟩ :=
    perSectorBoundG_condensed_clause h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε₀E, hεE, hE'⟩ :=
    perSectorBoundG_excited_clause h hv hv1 hvrad hR hv_supp hav hcC0 hcC14
  refine ⟨min ε₀E ε₀C, cC, CC, lt_min hεE hεC, hcC0, hcC14, hCC0, ?_⟩
  intro μ hAdm n Φ u hu k hk
  have hAdmE : Work.BoseBoxFix.Adm v ε₀E μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hAdmC : Work.BoseBoxFix.Adm v ε₀C μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
  by_cases hcase : 2 * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1B.PBℓ v μ)
        (Work.BoseFixB1B.PBB v μ u)
        (Work.SmallBoxSliding.boxMass (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u)
        (Work.FockBridge.sectorPiece (Work.BoseFixB1B.PBB v μ u) k (Φ : Submission.BoseGases.X n → ℝ))
      ≤ (k : ℝ) * Work.FockBridge.sectorMass (Work.BoseFixB1B.PBℓ v μ)
          (Work.BoseFixB1B.PBB v μ u) (Φ : Submission.BoseGases.X n → ℝ) k
  · exact hC' μ hAdmC n Φ u hu k hk hcase
  · exact hE' μ hAdmE n Φ u hu k hk (le_of_lt (not_le.mp hcase)) CC hCC0

end Work.BoseFixB1
