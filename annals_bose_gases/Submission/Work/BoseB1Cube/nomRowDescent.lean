import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.NomRowDefs
import Submission.Work.BoseFixB1S.SharpMassLedger
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nomRowDescent` — FS's `n = m n' + n''` grouping assembled

**No new analysis**: the assembly of FS `thm:smallbox`'s grouping step (`final_v2.tex` l.3990–4055)
at the *nominal* per-box row `nomRow`.

Inputs (per-size, **state-independent** rows on a two-sided count window — the two residuals of the
per-box chapter, see `FINDING_perBoxFNom_session5.md`):

* `hGRP` — FS l.4019–4026, on the window `C_nμ|B| ≤ n' ≤ 2C_nμ|B|`:
  `(1/18)·μ·(n'/|B|)·W·∫Ψ² ≤ sbWordCube Ψ`;
* `hREM` — FS l.3995–4015, for `n'' ≤ 2C_nμ|B|`:
  `[(1/4)(n''/|B| − μ)² − (1/2)μ²]·W·∫Ψ² − E·∫Ψ² ≤ sbWordCube Ψ`, `E = C(μ²aΓχ + μa)`.

Output (this file): the in-box nominal row at the **canonical index** `m·n₀ + n''` with `c₁ = 1/40`
and the same `C`, `E`:

    nomRow v h R (1/40) C μ μ (m·n₀ + n'') u Φ ≤ sbWordCube v h μ u Φ .

The passage from the canonical index to an arbitrary `n` (`n₀ := ⌈C_nμ|B|⌉₊`, `m := n/n₀`,
`n'' := n % n₀`) is a *pure reindexing* of the state (`Fin.cast`), recorded as the remaining
bookkeeping step; the arithmetic half below is stated for an arbitrary `n` already (it is
state-free).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

/-- **The state-free arithmetic half of the grouping.**  For the group size `n₀` in the window
`C_nμV ≤ n₀ ≤ 2C_nμV` and `n'' < n₀`, the *bracket* of the nominal row at the full density
`n/V = (m n₀ + n'')/V` is dominated by the bracket of the two group rows:

    c₁·W·ψ(1,μ,(m n₀+n'')/V) − ½μ²W − E ≤
        m·[(1/18)μ(n₀/V)W] + ([¼(n''/V − μ)² − ½μ²]W − E)          (`c₁ = 1/40`).

This is `Work.BoseFixB1S.groupingArith_mul` plus `ψ(1,μ,t) = μ(t−μ)²/(μ+t)`. -/
theorem nomBracket_le_groupBracket {μ V W E Cn : ℝ} {n₀ n'' m : ℕ}
    (hμ : 0 < μ) (hV : 0 < V) (hW : 0 ≤ W) (hCn : 2 ≤ Cn) (hCnμV : Cn * μ * V ≤ (n₀ : ℝ))
    (hnr : (n'' : ℝ) < (n₀ : ℝ)) :
    (1 / 40) * (W * psiWeight 1 μ ((((m * n₀ + n'' : ℕ) : ℝ) / V)))
        - (1 / 2) * μ ^ 2 * W - E
      ≤ (m : ℝ) * ((1 / 18) * μ * ((n₀ : ℝ) / V) * W)
        + (((1 / 4) * (((n'' : ℝ) / V) - μ) ^ 2 - (1 / 2) * μ ^ 2) * W - E) := by
  have h2μρ : 2 * μ ≤ (n₀ : ℝ) / V := by
    have h1 : Cn * μ ≤ (n₀ : ℝ) / V := by
      rw [le_div_iff₀ hV]; linarith
    have h2 : 2 * μ ≤ Cn * μ := by nlinarith [hCn, hμ]
    linarith
  have hs0 : 0 ≤ (n'' : ℝ) / V := by positivity
  have hsρ : (n'' : ℝ) / V ≤ (n₀ : ℝ) / V := by
    apply div_le_div_of_nonneg_right _ hV.le
    linarith
  have harith := Work.BoseFixB1S.groupingArith_mul (μ := μ) (ρ' := (n₀ : ℝ) / V)
    (s := (n'' : ℝ) / V) (M₁ := W) m hμ h2μρ hs0 hsρ hW
  have hcast : ((m * n₀ + n'' : ℕ) : ℝ) = (m : ℝ) * (n₀ : ℝ) + (n'' : ℝ) := by push_cast; ring
  have hcomb : (m : ℝ) * ((n₀ : ℝ) / V) + (n'' : ℝ) / V
      = ((m : ℝ) * (n₀ : ℝ) + (n'' : ℝ)) / V := by ring
  have hpsi := psiWeight_one_eq (μ := μ) (t := (((m * n₀ + n'' : ℕ) : ℝ) / V)) hμ
  rw [hpsi, hcast]
  rw [hcomb] at harith
  ring_nf at harith ⊢
  linarith [harith]

end Work.BoseB1Cube

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The state-level descent step** (FS `final_v2.tex` l.3990–4055) at the nominal row, at the
canonical index `N = m·n₀ + n''`:  from the two per-size rows on the window (`hGRP` for the `m`
blocks of size `n₀`, `hREM` for the remainder `n''`) one gets the in-box nominal row at `N` with
`c₁ = 1/40` and the same error row `E`. -/
theorem nomRow_descentStep {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {Cn ε₀ C : ℝ} (hCn : 2 ≤ Cn) (hε₀ : 0 < ε₀) (hC : 0 ≤ C)
    (hGRP : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n' : ℕ) (Ψ : X n' → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox n' (sideAt μ (a v)))), Ψ x ≠ 0 →
          ∀ i : Fin n', x i ∈ dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) →
        Cn * μ * nomV v μ u ≤ (n' : ℝ) → (n' : ℝ) ≤ 2 * Cn * μ * nomV v μ u →
        (1 / 18) * μ * ((n' : ℝ) / nomV v μ u) * nomW v h μ u
            * (∫ x in abox n' (sideAt μ (a v)), (Ψ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
    (hREM : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n' : ℕ) (Ψ : X n' → ℝ) (u : E3),
        u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
        ContDiff ℝ (⊤ : ℕ∞) Ψ →
        (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox n' (sideAt μ (a v)))), Ψ x ≠ 0 →
          ∀ i : Fin n', x i ∈ dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) →
        (n' : ℝ) ≤ 2 * Cn * μ * nomV v μ u →
        ((1 / 4) * (((n' : ℝ) / nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2) * nomW v h μ u
            * (∫ x in abox n' (sideAt μ (a v)), (Ψ x) ^ 2)
          - nomESlot v R C μ μ u * (∫ x in abox n' (sideAt μ (a v)), (Ψ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
    {μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (u : E3)
    (hu : u ∈ Work.SmallBoxSliding.goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ)
    (hVpos : 0 < nomV v μ u)
    (hR16 : R ≤ sideAt μ (a v) * (paramsAt μ (a v)).d / 16)
    (hRχ : R ≤ sideAt μ (a v) * Submission.BoseGases.chiR0)
    {n₀ : ℕ} (hn₀lb : Cn * μ * nomV v μ u ≤ (n₀ : ℝ))
    (hn₀ub : (n₀ : ℝ) ≤ 2 * Cn * μ * nomV v μ u)
    {m nr : ℕ} (hnr : nr < n₀)
    (Φ : Work.BoseKinLoc.BoxState (m * n₀ + nr) (sideAt μ (a v)))
    (hloc : ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (abox (m * n₀ + nr) (sideAt μ (a v)))), (Φ : X (m * n₀ + nr) → ℝ) x ≠ 0 →
          ∀ i : Fin (m * n₀ + nr), x i ∈ dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) :
    nomRow v h R (1 / 40) C μ μ (m * n₀ + nr) u (Φ : X (m * n₀ + nr) → ℝ)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X (m * n₀ + nr) → ℝ) := by
  classical
  have hμ : 0 < μ := hAdm.1
  have hWnn : 0 ≤ nomW v h μ u :=
    Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp
      (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm) u
  have hNnn : 0 ≤ ∫ x in abox (m * n₀ + nr) (sideAt μ (a v)),
      ((Φ : X (m * n₀ + nr) → ℝ) x) ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  have hnrR : (nr : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast le_of_lt hnr
  -- the two per-size rows become the two `G`-rows of the descent
  have hB1 : ∀ (Ψ : X n₀ → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox n₀ (sideAt μ (a v)))), Ψ x ≠ 0 →
        ∀ i : Fin n₀, x i ∈ dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) →
      ((1 / 18) * μ * ((n₀ : ℝ) / nomV v μ u) * nomW v h μ u)
          * (∫ x in abox n₀ (sideAt μ (a v)), (Ψ x) ^ 2)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ :=
    fun Ψ hΨ hl => hGRP μ hAdm n₀ Ψ u hu hΨ hl hn₀lb hn₀ub
  have hB2 : ∀ (Ψ : X nr → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict (abox nr (sideAt μ (a v)))), Ψ x ≠ 0 →
        ∀ i : Fin nr, x i ∈ dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) →
      (((1 / 4) * (((nr : ℝ) / nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2) * nomW v h μ u
          - nomESlot v R C μ μ u)
          * (∫ x in abox nr (sideAt μ (a v)), (Ψ x) ^ 2)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ := by
    intro Ψ hΨ hl
    have h := hREM μ hAdm nr Ψ u hu hΨ hl (le_trans hnrR hn₀ub)
    rw [sub_mul]
    linarith [h]
  have hdesc := Work.BoseB1Cube.sbWordCube_descent_atSizes (v := v) h hv hv1 hvrad hR hv_supp
    hav hAdm hR16 hRχ u
    ((1 / 18) * μ * ((n₀ : ℝ) / nomV v μ u) * nomW v h μ u)
    (((1 / 4) * (((nr : ℝ) / nomV v μ u) - μ) ^ 2 - (1 / 2) * μ ^ 2) * nomW v h μ u
      - nomESlot v R C μ μ u)
    hB1 hB2 Φ.contDiff hloc
  -- the bracket comparison
  have hbracket := nomBracket_le_groupBracket (μ := μ) (V := nomV v μ u)
    (W := nomW v h μ u) (E := nomESlot v R C μ μ u) (Cn := Cn) (n₀ := n₀) (n'' := nr) (m := m)
    hμ hVpos hWnn hCn hn₀lb (by exact_mod_cast hnr)
  rw [nomRow_eq]
  have hmul := mul_le_mul_of_nonneg_right hbracket hNnn
  linarith [hmul, hdesc]

end Work.BoseB1Cube
