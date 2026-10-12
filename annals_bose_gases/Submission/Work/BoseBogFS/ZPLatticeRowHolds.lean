import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.ZPCleanRow
import Submission.Work.BoseBogFS.ZPMassLatticeRowHonest
import Submission.Work.BoseBogFS.cleanFun_nonneg_of_large
import Submission.Work.BoseBogFS.cleanFun_summable_integrable
import Submission.Work.BoseBogFS.cleanFun_tsum_le_integral
import Submission.Work.BoseBogFS.integral_cleanFun_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.ZPLatticeRowHolds` — FS `lem:BogIntegral` on the full dual lattice

The target `Work.BoseBogFS.ZPLatticeRow` is FS `lem:BogIntegral`
(`Papers/fournais_solovej/final_v2.tex`) on the full dual lattice `(2π/ℓ)ℤ³`, with
no cut-off and no cube, in finite-set form.  The definitions and the elementary
pointwise layer live in `Submission/Work/BoseBogFS/ZPLatticeAux.lean`; the two
analytic rows are stated here.

With `τ = tauAt`, `c = ρ·Ŵ₁(k)` and `k_n = kAt n`, FS's `eq:LHYIntegral1` splits
the summand `½·𝒵(τ+c,c)` into the clean part `½·cleanTerm` (= the `I₁` integrand of
`eq:SplitIntegrals`) and the mass part `massTerm = c²/(4‖k‖²)`.  The two rows are

* `ZPMassLatticeRow` — the sharp lattice-Coulomb comparison for the mass part
  (`Σ_{n≠0}Ŵ(k_n)²/(4‖k_n‖²) ≤ (2π)⁻³ℓ³∫Ŵ²/(4‖p‖²) + Cℓ²(∫W)²`), the design's D5
  item `latticeCoulomb_approx`; proved here as the delegated
  `Work.BoseBogFS.ZPMassLatticeRowSharp` (`4R ≤ ℓ`, the source's own Nyquist
  condition — with only `R ≤ ℓ` the row is FALSE, see
  `FINDING_ZPMassLatticeRow_FALSE.md`);
* `ZPCleanDeficitRow` — FS's `I₁ ≤ −lhyValue(8π) + ε` transported to the honest
  datum and to the lattice, with the discretisation error `O(X^{3/2})·LHY`; proved
  here from the four ingredient rows of `Work.BoseBogFS.ZPCleanRow`.

## The route

`ZPLatticeRowHolds_of_rows` reduces the target to `ZPMassStep v h R` plus the clean
row; `ZPMassStep_of_rows` reduces the mass step to the sharp lattice row, the
`E₁`–`E₂` comparison (`ZPE1E2RowW1`, from the proved `Work.BoseBogFS.ZPE1E2Corrected`)
and the kinematic `W₁` facts (`ZPW1Fact`, from the proved `Work.BoseBogFS.ZPW1Facts`),
the remaining arithmetic being `ZPLatticeAux.massStep_arith'`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 3. The two analytic rows -/

/-- **The sharp lattice–Coulomb row at the honest kernel `W₁ = W1fun v h ℓ`** in `Prop` form at a
fixed error constant `C` (the body of the delegated `Work.BoseBogFS.ZPMassLatticeRowHonest`).

This is the sharp (constant `1` on the continuum integral) lattice-vs-continuum comparison for
the mass part `Ŵ₁(k_n)²/(4‖k_n‖²)`, with the near-image error `C·ℓ²(∫W₁)²`, on the full dual
lattice `(2π/ℓ)ℤ³`.  The **parentheses around the integral are essential**: the version filed at
`Submission/Work/BoseBogFS/ZPMassLatticeRowSharp.lean` (and the first version of this file) wrote
`∫ p, Ŵ(p)²/(4‖p‖²) + C ℓ²(∫W)²`, whose integral body swallows the `+ C ℓ²(∫W)²` — the integrand
is then non-integrable, the integral is the junk value `0`, and the row is FALSE. -/
def ZPSharp (C : ℝ) : Prop :=
  ∀ {v : ℝ³ → ℝ} {h : ScatSol v} {R : ℝ}, 0 < R → (∀ x, 0 ≤ v x) →
    _root_.BoseGases.IsRadial v → tsupport v ⊆ Metric.ball 0 R → 0 < a v →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      ∀ S : Finset (Fin 3 → ℤ), (∀ n ∈ S, n ≠ 0) →
        ∑ n ∈ S, (chat (W1At v h μ) (kAt v μ n)) ^ 2 / (4 * ‖kAt v μ n‖ ^ 2)
          ≤ ((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
              * (∫ p : ℝ³, (chat (W1At v h μ) p) ^ 2 / (4 * ‖p‖ ^ 2))
            + C * (ell v μ) ^ 2 * (∫ x : ℝ³, W1At v h μ x) ^ 2

/-- **The sharp lattice-Coulomb row** (FS's `eq:I2-integral` mechanism, sharp form;
the design's D5 `latticeCoulomb_approx`) — proved by the delegated
`Work.BoseBogFS.ZPMassLatticeRowHonest`. -/
theorem ZPMassLatticeRow : ∃ C : ℝ, 0 ≤ C ∧ ZPSharp C :=
  ZPMassLatticeRowHonest

/-- **FS's `I₁` estimate at the honest datum, on the lattice**: the lattice sum of
FS's clean part `𝒵(τ+c,c) − c²/(2‖k‖²)` is bounded by minus the Lee–Huang–Yang term
plus `C·errBracket`.

Proved here from the four ingredient rows of the clean part
(`Work.BoseBogFS.zpCleanDeficit_of_rows`), each of which is a separate module:
`cleanFun_nonneg_of_large`, `cleanFun_summable_integrable`, `cleanFun_tsum_le_integral`
and `integral_cleanFun_le`. -/
theorem ZPCleanDeficitRow :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : ℝ³ → ℝ} {h : ScatSol v} {R : ℝ}, 0 < R → (∀ x, 0 ≤ v x) →
      _root_.BoseGases.IsRadial v → tsupport v ⊆ Metric.ball 0 R → 0 < a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
        ∃ Lam : ℝ, 0 ≤ Lam ∧ ∀ S : Finset (Fin 3 → ℤ),
          (∀ n : Fin 3 → ℤ, n ≠ 0 → ‖kAt v μ n‖ ≤ Lam → n ∈ S) →
          ∑ n ∈ S, (1 / 2) * cleanTerm v h ρ μ n
            ≤ -(4 * Real.pi * lhyC * ρ ^ 2 * (a v) * (ell v μ) ^ 3
                  * Real.sqrt (ρ * (a v) ^ 3))
              + C * errBracket v R μ :=
  zpCleanDeficit_of_rows cleanFun_nonneg_of_large cleanFun_summable_integrable
    cleanFun_tsum_le_integral integral_cleanFun_le

/-! ## 4. The assembly: the enlargement set and the monotonicity step -/

/-- **The monotonicity step of the assembly**: if every honest summand is nonnegative, then
enlarging the finite set cannot decrease the lattice sum. -/
lemma zpSum_le_of_subset {v : ℝ³ → ℝ} {h : ScatSol v} {ρ μ : ℝ}
    (hpos : ∀ n : Fin 3 → ℤ, 0 ≤ zpTerm v h ρ μ n)
    {S T : Finset (Fin 3 → ℤ)} (hST : S ⊆ T) :
    ∑ n ∈ S, zpTerm v h ρ μ n ≤ ∑ n ∈ T, zpTerm v h ρ μ n :=
  finset_sum_le_of_subset_of_nonneg hST (fun i _ => hpos i)

/-- **The monotonicity step at the honest datum**, with the pointwise nonnegativity supplied by
the proved `Work.BoseBogFS.ZPTermNonnegLattice`.  This is the step that lets the deficit row
(stated for sets containing `zBall v μ Lam`) be applied to an arbitrary finite `S`: enlarge `S`
by the (finite) set `zBall v μ Lam` of low-momentum labels. -/
lemma zpSum_le_of_subset_honest {v : ℝ³ → ℝ} {h : ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      ∀ {S T : Finset (Fin 3 → ℤ)}, S ⊆ T →
        ∑ n ∈ S, zpTerm v h ρ μ n ≤ ∑ n ∈ T, zpTerm v h ρ μ n := by
  obtain ⟨ε₀, hε₀, h⟩ := ZPTermNonnegLattice (v := v) (h := h) (R := R)
    hR hv hvrad hv_supp hav
  exact ⟨ε₀, hε₀, fun μ hμ ρ hρ _ _ hST =>
    zpSum_le_of_subset (fun n => h μ hμ ρ hρ n) hST⟩

/-! ## 5. The assembly: `ZPLatticeRow` from the two honest-form rows -/

/-- **The honest mass step** (the form the assembly consumes): the lattice mass sum is bounded by
`½ℓ³ρ²Ŵ₁ω(0)` plus `C₁·errBracket`.  It bundles the sharp lattice-Coulomb row
(`ZPMassLatticeRowSharp`) with FS's `eq:I2-integral` (in the corpus as the proved
`Work.BoseB7AK.C3Q.I2_integral_bound`) and the mass bound `W1_mass_bounds`. -/
def ZPMassStep (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ μ : ℝ, Adm v ε₁ μ → ∀ ρ : ℝ,
    CloseCondFS v μ ρ → ∀ S : Finset (Fin 3 → ℤ), (∀ n ∈ S, n ≠ 0) →
      ∑ n ∈ S, ρ ^ 2 * (chat (W1At v h μ) (kAt v μ n)) ^ 2 / (4 * ‖kAt v μ n‖ ^ 2)
        ≤ (1 / 2) * (ell v μ) ^ 3 * ρ ^ 2 * chat (W1ωAt v h μ) 0
          + C₁ * errBracket v R μ

/-- **The initial segment lemma.**  For every finite `S` there is a finite `T ⊇ S` containing
every nonzero lattice label in the ball of radius `Lam`, namely `T := S ∪ (zBall v μ Lam)`. -/
lemma exists_finset_superset_zBall (v : ℝ³ → ℝ) (μ Lam : ℝ) (hℓ : 0 < ell v μ)
    (S : Finset (Fin 3 → ℤ)) :
    ∃ T : Finset (Fin 3 → ℤ), S ⊆ T ∧
      (∀ n : Fin 3 → ℤ, n ≠ 0 → ‖kAt v μ n‖ ≤ Lam → n ∈ T) :=
  ⟨S ∪ (zBall_finite v μ Lam hℓ).toFinset, Finset.subset_union_left,
    fun n hn hk => Finset.mem_union_right _
      ((Set.Finite.mem_toFinset _).mpr ((mem_zBall).mpr ⟨hn, hk⟩))⟩

/-- The label `0` contributes `0` to the mass sum (its `1/0` is junk). -/
lemma massTerm_zero (v : ℝ³ → ℝ) (h : ScatSol v) (ρ μ : ℝ) : massTerm v h ρ μ 0 = 0 := by
  have hk : kAt v μ 0 = (0 : ℝ³) := by
    rw [kAt, Work.BoseB4.vec]
    ext i
    simp
  rw [massTerm, hk, norm_zero]
  simp

/-- `massTerm` is `ρ²` times the squared transform over `4‖k‖²`. -/
lemma massTerm_eq (v : ℝ³ → ℝ) (h : ScatSol v) (ρ μ : ℝ) (n : Fin 3 → ℤ) :
    massTerm v h ρ μ n
      = ρ ^ 2 * (chat (W1At v h μ) (kAt v μ n)) ^ 2 / (4 * ‖kAt v μ n‖ ^ 2) := by
  rw [massTerm, cAt, mul_pow]

/-- **The assembly.**  Given the honest mass step `ZPMassStep v h R` and the clean/deficit row in
the shape of `ZPCleanDeficitRow`, the target `ZPLatticeRow v h R` follows.

No further analytic input is needed: the pointwise nonnegativity of the honest summand is the
proved `Work.BoseBogFS.ZPTermNonnegLattice`, the enlargement set is the proved `zBall_finite`, and
the ε₀'s are intersected with `adm_mono`.  The two remaining inputs are the honest mass step
`ZPMassStep v h R` and the clean/deficit row. -/
theorem ZPLatticeRowHolds_of_rows (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ)
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < a v) (hM : ZPMassStep v h R)
    (hC : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∃ ε₂ : ℝ, 0 < ε₂ ∧ ∀ μ : ℝ, Adm v ε₂ μ → ∀ ρ : ℝ,
      CloseCondFS v μ ρ → ∃ Lam : ℝ, 0 ≤ Lam ∧ ∀ S : Finset (Fin 3 → ℤ),
        (∀ n : Fin 3 → ℤ, n ≠ 0 → ‖kAt v μ n‖ ≤ Lam → n ∈ S) →
          ∑ n ∈ S, (1 / 2) * cleanTerm v h ρ μ n
            ≤ -(4 * Real.pi * lhyC * ρ ^ 2 * (a v) * (ell v μ) ^ 3
                  * Real.sqrt (ρ * (a v) ^ 3))
              + C₂ * errBracket v R μ)
    :
    ZPLatticeRow v h R := by
  obtain ⟨C₁, hC₁0, ε₁, hε₁0, hMrow⟩ := hM
  obtain ⟨C₂, hC₂0, ε₂, hε₂0, hCrow⟩ := hC
  obtain ⟨ε₃, hε₃0, hnnrow⟩ := ZPTermNonnegLattice (v := v) (h := h) (R := R)
    hR hv hvrad hv_supp hav
  refine ⟨min (min ε₁ ε₂) ε₃, C₁ + C₂, lt_min (lt_min hε₁0 hε₂0) hε₃0,
    add_nonneg hC₁0 hC₂0, ?_⟩
  intro μ hμ ρ hρ S
  have hμ1 : Adm v ε₁ μ :=
    adm_mono (le_trans (min_le_left _ _) (min_le_left _ _)) hμ
  have hμ2 : Adm v ε₂ μ :=
    adm_mono (le_trans (min_le_left _ _) (min_le_right _ _)) hμ
  have hμ3 : Adm v ε₃ μ := adm_mono (min_le_right _ _) hμ
  have hpos : 0 < ell v μ := by
    rw [ell_eq, Work.BoseBox.sideAt_eq_rpow hav hμ.1]
    exact mul_pos hav (Real.rpow_pos_of_pos (mul_pos hμ.1 (pow_pos hav 3)) _)
  obtain ⟨Lam, hLam0, hClem⟩ := hCrow μ hμ2 ρ hρ
  obtain ⟨T, hST, hTball⟩ := exists_finset_superset_zBall v μ Lam hpos S
  calc ∑ n ∈ S, zpTerm v h ρ μ n
      ≤ ∑ n ∈ T, zpTerm v h ρ μ n := zpSum_le_of_subset (hnnrow μ hμ3 ρ hρ) hST
    _ = (∑ n ∈ T, (1 / 2) * cleanTerm v h ρ μ n) + ∑ n ∈ T, massTerm v h ρ μ n := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun n _ => zpTerm_eq v h ρ μ n)
    _ ≤ (-(4 * Real.pi * lhyC * ρ ^ 2 * (a v) * (ell v μ) ^ 3
              * Real.sqrt (ρ * (a v) ^ 3)) + C₂ * errBracket v R μ)
          + ((1 / 2) * (ell v μ) ^ 3 * ρ ^ 2 * chat (W1ωAt v h μ) 0
              + C₁ * errBracket v R μ) := by
        refine add_le_add (hClem T hTball) ?_
        have hsum : ∑ n ∈ T, massTerm v h ρ μ n = ∑ n ∈ T.erase 0, massTerm v h ρ μ n := by
          by_cases h0 : 0 ∈ T
          · rw [← Finset.sum_erase_add (s := T) (f := fun n => massTerm v h ρ μ n) h0,
              massTerm_zero v h ρ μ, add_zero]
          · rw [Finset.erase_eq_of_notMem h0]
        rw [hsum, Finset.sum_congr rfl (fun n _ => massTerm_eq v h ρ μ n)]
        exact hMrow μ hμ1 ρ hρ (T.erase 0) (fun n hn => (Finset.mem_erase.mp hn).1)
    _ = -(4 * Real.pi * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * (a v) ^ 3))
          + (1 / 2) * ell3 v μ * ρ ^ 2 * chat (W1ωAt v h μ) 0
          + (C₁ + C₂) * errBracket v R μ := by
        rw [ell3]; ring

/-! ## 6. The honest mass step from the sharp row, the `E₁`–`E₂` row and the `W₁` facts -/

/-- The **`E₁`–`E₂` comparison** in `Prop` form, in the `W1At`/`W1ωAt` spelling.  This is the
body of the proved `Work.BoseBogFS.ZPE1E2Corrected` (`ZPE1E2Corrected.lean`), restated as a
`Prop` at a fixed datum.  (Named `ZPE1E2RowW1` rather than `ZPE1E2Row` so that this module can
import `ZPE1E2Row.lean`, which carries that name.) -/
def ZPE1E2RowW1 (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ μ : ℝ, Adm v ε₀ μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
    |((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
        * (∫ p : ℝ³, (chat (W1At v h μ) p) ^ 2 / (2 * ‖p‖ ^ 2))
      - (ell v μ) ^ 3 * chat (W1ωAt v h μ) 0|
    ≤ C * (ell v μ) ^ 2 * (∫ x : ℝ³, W1At v h μ x) ^ 2

/-- The **`W₁` facts** in `Prop` form (the body of `ZPW1Facts`). -/
def ZPW1Fact (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    (∀ x : ℝ³, W1At v h μ (-x) = W1At v h μ x) ∧
    tsupport (W1At v h μ) ⊆ Metric.ball 0 R ∧
    MeasureTheory.Integrable (W1At v h μ) ∧
    (∀ᵐ x, 0 ≤ W1At v h μ x) ∧
    MeasureTheory.Integrable (fun p : ℝ³ × ℝ³ => W1At v h μ p.1 * W1At v h μ p.2 / ‖p.1 - p.2‖) ∧
    4 * R ≤ ell v μ ∧
    8 * Real.pi * a v ≤ ∫ x : ℝ³, W1At v h μ x ∧
    (∫ x : ℝ³, W1At v h μ x) ≤ 16 * Real.pi * a v

/-- **The quarter-mass integral is half the half-mass integral** (the elementary identity behind
the `(2π)⁻³ℓ³∫Ŵ²/(2‖p‖²)` of the `E₁`–`E₂` row and the `(2π)⁻³ℓ³∫Ŵ²/(4‖p‖²)` of the sharp
lattice row: `x/(4y) = (1/2)·(x/(2y))`). -/
lemma integral_quarter_eq_half (W : ℝ³ → ℝ) :
    (∫ p : ℝ³, (chat W p) ^ 2 / (4 * ‖p‖ ^ 2))
      = (1 / 2) * (∫ p : ℝ³, (chat W p) ^ 2 / (2 * ‖p‖ ^ 2)) := by
  have hpt : (fun p : ℝ³ => (chat W p) ^ 2 / (4 * ‖p‖ ^ 2))
      = fun p : ℝ³ => (1 / 2) * ((chat W p) ^ 2 / (2 * ‖p‖ ^ 2)) := by
    funext p
    ring
  rw [hpt, integral_const_mul]

/-- **The pure arithmetic of the honest mass step**: the sharp lattice–Coulomb row (in the form
`(2π)⁻³ℓ³∫Ŵ²/(4‖p‖²)`), the `E₁`–`E₂` comparison (`(2π)⁻³ℓ³∫Ŵ²/(2‖p‖²) ≤ ℓ³Ŵ₁ω(0) + CEℓ²M²`)
and the threshold arithmetic (`ρ²CpL²M² ≤ C₁·Err`, `Cp = Csh + CE/2`) combine into the honest
mass row.  All hypotheses are stated at the same atoms, so the step is a chain of
`mul_le_mul_of_nonneg_left` and `ring`. -/
lemma zpmass_final {lhs ρ L M E2 J I Csh CE Cp C1 Err : ℝ}
    (h1 : lhs ≤ ρ ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * L ^ 3 * J + Csh * L ^ 2 * M ^ 2))
    (h2 : ((2 * Real.pi) ^ 3)⁻¹ * L ^ 3 * J
      = (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹ * L ^ 3 * I))
    (h3 : ((2 * Real.pi) ^ 3)⁻¹ * L ^ 3 * I ≤ L ^ 3 * E2 + CE * L ^ 2 * M ^ 2)
    (h4 : Cp = Csh + CE / 2)
    (h5 : ρ ^ 2 * Cp * L ^ 2 * M ^ 2 ≤ C1 * Err)
    (hρsq : 0 ≤ ρ ^ 2) :
    lhs ≤ (1 / 2) * L ^ 3 * ρ ^ 2 * E2 + C1 * Err := by
  have hmono : (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹ * L ^ 3 * I) + Csh * L ^ 2 * M ^ 2
      ≤ (1 / 2) * (L ^ 3 * E2 + CE * L ^ 2 * M ^ 2) + Csh * L ^ 2 * M ^ 2 := by
    have h := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  calc lhs
      ≤ ρ ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * L ^ 3 * J + Csh * L ^ 2 * M ^ 2) := h1
    _ = ρ ^ 2 * ((1 / 2) * (((2 * Real.pi) ^ 3)⁻¹ * L ^ 3 * I)
          + Csh * L ^ 2 * M ^ 2) := by rw [h2]
    _ ≤ ρ ^ 2 * ((1 / 2) * (L ^ 3 * E2 + CE * L ^ 2 * M ^ 2)
          + Csh * L ^ 2 * M ^ 2) := mul_le_mul_of_nonneg_left hmono hρsq
    _ = (1 / 2) * L ^ 3 * ρ ^ 2 * E2 + ρ ^ 2 * Cp * L ^ 2 * M ^ 2 := by rw [h4]; ring
    _ ≤ (1 / 2) * L ^ 3 * ρ ^ 2 * E2 + C1 * Err := by linarith

/-- **The `ρ² ≤ 4μ²` slot of the mass step.**  `CloseCondFS` confines `ρ` to
`|ρ − μ| ≤ μK_ℓ⁻²/(2¹⁴π) ≤ μ/4`, so `ρ ≥ 0` and `ρ² ≤ (5/4)²μ² ≤ 4μ²`. -/
lemma close_rho_sq_four (v : ℝ³ → ℝ) {μ ρ : ℝ} (hμ : 0 < μ) (hav : 0 < a v)
    (hKl : 1 ≤ (paramsAt μ (a v)).Kl) (hclose : CloseCondFS v μ ρ) :
    0 ≤ ρ ∧ ρ ^ 2 ≤ 4 * μ ^ 2 := by
  have hKl1 : 0 < (paramsAt μ (a v)).Kl := lt_of_lt_of_le one_pos hKl
  have hKl2 : ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hKl1.le, Real.rpow_two]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  have hc1 : ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π) ≤ 1 / 4 := by
    have h1 : ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)
        ≤ 1 / ((2 : ℝ) ^ 14 * π) := div_le_div_of_nonneg_right hKl2 (by positivity)
    have h2 : (1 : ℝ) / ((2 : ℝ) ^ 14 * π) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith [Real.pi_gt_three])
    linarith
  have hthr : closeThresholdFS v μ ≤ μ / 4 := by
    rw [closeThresholdFS]
    calc μ * ((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)
        = μ * (((paramsAt μ (a v)).Kl) ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)) := by ring
      _ ≤ μ * (1 / 4) := mul_le_mul_of_nonneg_left hc1 hμ.le
      _ = μ / 4 := by ring
  have h1 := abs_le.mp hclose
  have hρ0 : 0 ≤ ρ := by linarith [h1.1, hthr, hμ]
  have hρle : ρ ≤ 5 * μ / 4 := by linarith [h1.2, hthr, hμ]
  exact ⟨hρ0, by nlinarith [hρle, hρ0, hμ]⟩

/-- **The honest mass step from the three inputs.**  See `NOTES_ZPLatticeRowHolds.md` §11–§21.
The sharp row supplies `ρ²(2π)⁻³ℓ³∫Ŵ²/(4p²) + Cshρ²ℓ²M²`, the `E₁`–`E₂` row replaces
`(2π)⁻³ℓ³∫Ŵ²/(2p²)` by `ℓ³Ŵ₁ω(0) + CEℓ²M²`, and `massStep_arith'` pays
`ρ²(Csh + CE/2)ℓ²M²` against the `t^{1/1615}` slot of `errBracket`. -/
theorem ZPMassStep_of_rows (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ)
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < a v)
    (hsharp : ∃ C : ℝ, 0 ≤ C ∧ ZPSharp C) (he : ZPE1E2RowW1 v h R) (hw : ZPW1Fact v h R)
    (hρ2 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ → ∀ ρ : ℝ, CloseCondFS v μ ρ →
      ρ ^ 2 ≤ 4 * μ ^ 2) :
    ZPMassStep v h R := by
  obtain ⟨Csh, hCsh0, hsharprow⟩ := hsharp
  obtain ⟨εs, hεs0, hsharprow⟩ := hsharprow hR hv hvrad hv_supp hav
  obtain ⟨εe, hεe0, CE, hCE0, her⟩ := he
  obtain ⟨εw, hεw0, hwf⟩ := hw
  obtain ⟨ερ, hερ0, hρ2⟩ := hρ2
  have hCp0 : 0 ≤ Csh + CE / 2 := by linarith
  have hMul0 : 0 ≤ 1024 * Real.pi ^ 2 * (Csh + CE / 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Real.pi)) hCp0
  have hC10 : 0 ≤ 1024 * Real.pi ^ 2 * (Csh + CE / 2) + 1 := by linarith
  refine ⟨1024 * Real.pi ^ 2 * (Csh + CE / 2) + 1, hC10,
    min (min (min εe εw) (min ερ 1)) εs,
    lt_min (lt_min (lt_min hεe0 hεw0) (lt_min hερ0 one_pos)) hεs0, ?_⟩
  intro μ hμ ρ hρc S hS
  have hμe : Adm v εe μ :=
    adm_mono (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))) hμ
  have hμw : Adm v εw μ :=
    adm_mono (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))) hμ
  have hμρ : Adm v ερ μ :=
    adm_mono (le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))) hμ
  have hμs : Adm v εs μ := adm_mono (min_le_right _ _) hμ
  have ht1 : μ * (a v) ^ 3 ≤ 1 :=
    le_trans (le_trans (le_trans hμ.2.1 (min_le_left _ _)) (min_le_right _ _))
      (min_le_right _ _)
  obtain ⟨heven, hsupp, hInt, hnn, hpair, h4R, hMlo, hMhi⟩ := hwf μ hμw
  have hℓ : 0 < ell v μ := by linarith
  -- ## the sharp lattice-Coulomb row at the honest kernel (the delegated row already carries
  -- its own diluteness threshold `εs`)
  have hrowA : ∑ n ∈ S, (chat (W1At v h μ) (kAt v μ n)) ^ 2 / (4 * ‖kAt v μ n‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
          * (∫ p : ℝ³, (chat (W1At v h μ) p) ^ 2 / (4 * ‖p‖ ^ 2))
        + Csh * (ell v μ) ^ 2 * (∫ x : ℝ³, W1At v h μ x) ^ 2 :=
    hsharprow μ hμs ρ hρc S hS
  have h1' : ∑ n ∈ S, ρ ^ 2 * (chat (W1At v h μ) (kAt v μ n)) ^ 2
        / (4 * ‖kAt v μ n‖ ^ 2)
      ≤ ρ ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
            * (∫ p : ℝ³, (chat (W1At v h μ) p) ^ 2 / (4 * ‖p‖ ^ 2))
          + Csh * (ell v μ) ^ 2 * (∫ x : ℝ³, W1At v h μ x) ^ 2) := by
    have hsplit : ∑ n ∈ S, ρ ^ 2 * (chat (W1At v h μ) (kAt v μ n)) ^ 2
          / (4 * ‖kAt v μ n‖ ^ 2)
        = ρ ^ 2 * ∑ n ∈ S, (chat (W1At v h μ) (kAt v μ n)) ^ 2
            / (4 * ‖kAt v μ n‖ ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hrowA (sq_nonneg ρ)
  -- ## the `E₁`–`E₂` comparison
  have h2' : ((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
        * (∫ p : ℝ³, (chat (W1At v h μ) p) ^ 2 / (4 * ‖p‖ ^ 2))
      = (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
          * (∫ p : ℝ³, (chat (W1At v h μ) p) ^ 2 / (2 * ‖p‖ ^ 2))) := by
    rw [integral_quarter_eq_half (W := W1At v h μ)]
    ring
  have h3' : ((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
        * (∫ p : ℝ³, (chat (W1At v h μ) p) ^ 2 / (2 * ‖p‖ ^ 2))
      ≤ (ell v μ) ^ 3 * chat (W1ωAt v h μ) 0
        + CE * (ell v μ) ^ 2 * (∫ x : ℝ³, W1At v h μ x) ^ 2 := by
    have hE := her μ hμe ρ hρc
    have hbase : ((2 * Real.pi) ^ 3)⁻¹ * (ell v μ) ^ 3
          * (∫ p : ℝ³, (chat (W1At v h μ) p) ^ 2 / (2 * ‖p‖ ^ 2))
        - (ell v μ) ^ 3 * chat (W1ωAt v h μ) 0
        ≤ CE * (ell v μ) ^ 2 * (∫ x : ℝ³, W1At v h μ x) ^ 2 := (abs_le.mp hE).2
    linarith
  -- ## the threshold arithmetic: `ρ²(Csh + CE/2)ℓ²M²` against the `t^{1/1615}` slot
  have h5' : ρ ^ 2 * (Csh + CE / 2) * (ell v μ) ^ 2 * (∫ x : ℝ³, W1At v h μ x) ^ 2
      ≤ (1024 * Real.pi ^ 2 * (Csh + CE / 2) + 1) * errBracket v R μ := by
    have hKl1 : 1 ≤ (paramsAt μ (a v)).Kl := Kl_ge_one v hμ.1 hav ht1
    have hρ0 : 0 ≤ ρ := (close_rho_rows v hμ.1 hav hKl1 hρc).1
    have hρsq : ρ ^ 2 ≤ 4 * μ ^ 2 := hρ2 μ hμρ ρ hρc
    have hM0 : 0 ≤ ∫ x : ℝ³, W1At v h μ x :=
      le_trans (by positivity : (0 : ℝ) ≤ 8 * Real.pi * a v) hMlo
    have hℓeq : ell v μ = a v * (μ * (a v) ^ 3) ^ (-(163 / 323) : ℝ) := by
      rw [ell_eq, Work.BoseBox.sideAt_eq_rpow hav hμ.1]
    have hden : (0 : ℝ) < 1024 * Real.pi ^ 2 * (Csh + CE / 2) + 1 := by
      linarith [hMul0]
    have hthr : (μ * (a v) ^ 3) ^ (13 / 3230 : ℝ)
        ≤ (1024 * Real.pi ^ 2 * (Csh + CE / 2) + 1)
            / (1024 * Real.pi ^ 2 * (Csh + CE / 2) + 1) := by
      rw [div_self (ne_of_gt hden)]
      exact Real.rpow_le_one (le_of_lt (mul_pos hμ.1 (pow_pos hav 3))) ht1 (by norm_num)
    have harith := massStep_arith' (μ := μ) (a := a v) (ρ := ρ) (ℓ := ell v μ)
      (M := ∫ x : ℝ³, W1At v h μ x)
      (C₁ := 1024 * Real.pi ^ 2 * (Csh + CE / 2) + 1) (C' := Csh + CE / 2)
      hCp0 hC10 hμ.1 hav hℓ.le hρ0 hρsq hM0 hMhi hℓeq hthr
    have herr : μ ^ 2 * a v * (ell v μ) ^ 3 * Real.sqrt (μ * (a v) ^ 3)
        * (μ * (a v) ^ 3) ^ (1 / 1615 : ℝ) ≤ errBracket v R μ := by
      have hE : errBracket v R μ = μ ^ 2 * a v * (ell v μ) ^ 3
          * Real.sqrt (μ * (a v) ^ 3)
          * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (μ * (a v) ^ 3)
              + (μ * (a v) ^ 3) ^ (1 / 1615 : ℝ)) := rfl
      rw [hE]
      refine mul_le_mul_of_nonneg_left ?_ ?_
      · have hnn : 0 ≤ fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (μ * (a v) ^ 3) := by
          positivity
        linarith
      · exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le)
          (pow_nonneg hℓ.le 3)) (Real.sqrt_nonneg _)
    have hgrp : ρ ^ 2 * (Csh + CE / 2) * (ell v μ) ^ 2
          * (∫ x : ℝ³, W1At v h μ x) ^ 2
        = (Csh + CE / 2) * ρ ^ 2 * (ell v μ) ^ 2 * (∫ x : ℝ³, W1At v h μ x) ^ 2 := by
      ring
    rw [hgrp]
    exact le_trans harith (mul_le_mul_of_nonneg_left herr hC10)
  -- ## the assembly of the mass step
  have hfin := zpmass_final
    (lhs := ∑ n ∈ S, ρ ^ 2 * (chat (W1At v h μ) (kAt v μ n)) ^ 2 / (4 * ‖kAt v μ n‖ ^ 2))
    (ρ := ρ) (L := ell v μ) (M := ∫ x : ℝ³, W1At v h μ x)
    (E2 := chat (W1ωAt v h μ) 0)
    (J := ∫ p : ℝ³, (chat (W1At v h μ) p) ^ 2 / (4 * ‖p‖ ^ 2))
    (I := ∫ p : ℝ³, (chat (W1At v h μ) p) ^ 2 / (2 * ‖p‖ ^ 2))
    (Csh := Csh) (CE := CE) (Cp := Csh + CE / 2)
    (C1 := 1024 * Real.pi ^ 2 * (Csh + CE / 2) + 1) (Err := errBracket v R μ)
    h1' h2' h3' rfl h5' (sq_nonneg ρ)
  exact hfin

/-- **The `W₁` facts are discharged**: the delegated row `Work.BoseBogFS.ZPW1Facts` is proved, and
its conclusion is definitionally `ZPW1Fact v h R`. -/
theorem ZPW1Fact_holds (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ)
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < a v) :
    ZPW1Fact v h R :=
  ZPW1Facts hR hv hvrad hv_supp hav

/-! ## 7. The target -/

theorem ZPLatticeRowHolds (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) {R : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseBogFS.ZPLatticeRow v h R := by
  obtain ⟨C₂, hC₂0, hCrow⟩ := ZPCleanDeficitRow
  refine ZPLatticeRowHolds_of_rows v h R hR hv hvrad hv_supp hav ?_ ?_
  · exact ZPMassStep_of_rows v h R hR hv hvrad hv_supp hav ZPMassLatticeRow
      (ZPE1E2Corrected hR hv hvrad hv_supp hav)
      (ZPW1Fact_holds v h R hR hv hvrad hv_supp hav)
      ⟨1, one_pos, fun μ hμ _ hρc =>
        (close_rho_sq_four v hμ.1 hav (Kl_ge_one v hμ.1 hav hμ.2.1) hρc).2⟩
  · exact ⟨C₂, hC₂0, hCrow (v := v) (h := h) (R := R) hR hv hvrad hv_supp hav⟩

end Work.BoseBogFS
