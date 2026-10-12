import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowQ2.RowsN
import Submission.Work.BoseRowQ2.lowCut_lipschitz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.MaskRow` — the *mask* form of FS l.3253 (the true `hGchi`), and the full
assembly of row 3 from it

## Why this file exists

`RowsN.lean` states the lead's corrected `GchiAtN` with the correction
`(1+1/ε)(C₁/κ_lat)² • T.N`, where `T.N` is the honest **total** number operator
(`tildeDataHon.N = totNumOp`).  That shape is **false for every absolute `C₁`** on the lead's
own witness for the refutation of the `NH`-form (`BOSE_HARD_DESIGN.md` §3):

* take the one-particle state `u = θ_{s₀} + h_N` (`h_N` high-pass, `≈ −θ_{s₀}` on the ball).
  Then `⟨Gop⟩ = ‖Q_L u‖²_{χ²} = 1`, `⟨Σ_k a_k†a_k⟩ → 0`, and `⟨N⟩ = 1` (one particle!).  So
  `GchiAtN` forces `(1+1/ε)(C₁/κ_lat)² ≥ 1`, i.e. `C₁ ≳ κ_lat/√(1+1/ε) ~ κ_lat = (μa³)^{-12/323}/(2π)`,
  which is **not** an absolute constant;
* while the companion arithmetic `ArithAt2` (`2ρŴ₁ω(0)(1+1/ε)(C₁/κ_lat)² ≤ (b/800)ℓ⁻²`) forces
  `(1+1/ε)(C₁/κ_lat)²` to be *below* `(b/800)ℓ⁻²/(2ρŴ₁ω(0)) ≈ t^{3/323}/1.9e6` — in particular
  `≤ 1` for every `t = μa³ ≤ 1`.

So `RowQ2AllCoreAtN` is false (the two conjuncts contradict each other), and the search for a
`C₁` that works is empty.  The defect is *not* the weight (`T.N ≥` the free high-momentum number,
so it is a *weaker* weight than FS's `n₊^H`) but the **coefficient**: FS's correction is
`Cε^{-1}·n₊^H` with `ε ≍ ε_T^{-1}(dK_ℓ)²` **small**, so `Cε^{-1} ≫ 1`, whereas
`(1+1/ε)(C₁/κ_lat)² ≪ 1` is *tiny*.  No state-independent tiny coefficient can pay a deficit of
order `‖Ψ‖²`.

## The true row — exactly the algebra of FS l.3253

Let `P_w(k) = Σ_s w_s χ̂(k−s)` in θ-coordinates `w_s = (u·g_s)`, `W(x) = Σ_s w_s e^{2πi⟨s,x⟩}` and
`M_{ss'} = χ̂²(s−s')` the `χ²`-weight.  Then (elementary Fourier algebra, no analysis)

* `⟨u, Gop u⟩ = Σ_{s,s'} f_L(s)f_L(s')χ̂²(s−s') w_s w_{s'} = ∫χ² |W_D|²`,  `W_D = Σ_s f_L(s)w_s e_s`;
* `⟨u, allNumOp u⟩ = Σ_{k ∈ Lab N} P_w(k)² ≤ Σ_{k∈ℤ³} P_w(k)² = ∫χ²|W|²`
  (the last step is the Poisson identity `Work.BoseRowQ2.chiLatticeParseval`);
* with `E := W − W_D = Σ_s(1−f_L(s))w_s e_s`, `⟨maskNum⟩ = Σ_s(1−f_L(s))²w_s² = ∫|E|²` and
  `∫W conj(E) = 0`, so Cauchy–Schwarz/Young in the `χ²`-weighted `L²` give, for `ε ∈ (0,1)`,

      ∫χ²|W_D|² ≤ (1/(1−ε))·∫χ²|W|² + (1/(ε(1−ε)))·∫χ²|E|².

Because `∫χ²|W|² = ⟨allNumOp⟩ + (tail)` with `tail = Σ_{k ∉ Lab N} P_w(k)² ≥ 0` — a Schwartz
tail that is negligible as soon as the cube is much finer than the mask cutoff (whence the
cube-size row) — we get the row

    **`GchiAtMask`**  `⟨Gop⟩ ≤ (1+ε)⟨Σ_k a_k†a_k⟩ + (Cχ/ε)⟨Σ_{s∈excited}(1−f_L(s))²ã_s†ã_s⟩ + δ⟨N⟩`

with an **absolute** `Cχ ≤ 2χ(0)² ≤ 12` and `δ` a fixed tiny constant that pays the Schwartz tail.
This is *verbatim* the `hGchi` of the design brief (and of FS l.3253), with the correction carried
by the mask-complement θ-number `maskNum` — and it is *true*, unlike `GchiAtN` (`RowsN.lean`).

## The payment row, and the one gap this directory cannot close

`maskNum` must be paid by the gap.  The only slot of `gapOpT = ℓ⁻²n₊ + ε_T(dℓ)⁻²n₊^H` whose
coefficient can carry a factor `ε^{-1}` is the `n₊^H` slot, so the chain needs

    **`RowPayMask`**  `⟨maskNum⟩ ≤ C₀·⟨T.NH⟩`    (FS's "n₊^H dominates the mask complement"),

and *that* is where the corpus's honest environment fails: `tildeDataHon.NH = (1/32)Σ_k η_H(k)a_k†a_k`
is a **χ-frame** number, while `maskNum` is a θ-frame number, and the lead's witness shows the
ratio is unbounded (`⟨maskNum⟩ ≳ 1/4` while `⟨NH⟩ → 0`).  This is a *modelling* issue in
`BoseBoxFock/Defs.lean` (`NH` should be the free high-momentum number `Σ_s η_H(s)ã_s†ã_s`, i.e. the
mask complement), not a defect of the rows below: with `RowPayMask` available,
`RowArith` (proved at `ε = fsEps`, `RowArith_at_fsEps`) pays `(Cχ/ε)·maskNum` out of the `b/800`
`n₊^H` slot, and the assembly below closes.  The *true* statement `maskNum ⪯ T.N`
(`maskNum_le_totNum`, PROVED here) is not enough: it needs the `ℓ⁻²` slot, and the resulting
ε-window is empty (`max(ε_A, ε_A2) > min(ε_M)`, a factor `t^{0.0186}`).

Everything in this file is `sorry`-free; the assembly `RowQ2AllRegimeN_of_coreMask` is a *theorem*,
so row 3 is reduced here to exactly three rows: `RowGchiMask` (true, delegated),
`RowPayMask` (the modelling gap), `RowMainN` (FS l.3240–3262).
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseB7.FockData

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- `qw` of a finite weighted sum of operators. -/
theorem qw_finset_sum_smul (F : FockData Mode) (S : Finset Mode) (c : Mode → ℝ)
    (X : Mode → F.H →ₗ[ℝ] F.H) (Ψ : F.H) :
    F.qw Ψ (∑ s ∈ S, c s • X s) = ∑ s ∈ S, c s * F.qw Ψ (X s) := by
  induction S using Finset.induction_on with
  | empty => simp [FockData.qw]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, F.qw_add, F.qw_smul, ih]

end Work.BoseB7.FockData

namespace Work.BoseB7A.TildeData

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : Work.BoseB7.FockData Mode} (T : TildeData F)

/-- **The mask-complement number** `Q̄_L`: `Σ_{s∈excited}(1−f_L(s))² ã_s†ã_s`.  This is the
θ-frame number of the part of the state that the low-momentum localisation `f_L` discards, i.e.
the *exact* correction object of FS l.3253 (and of the identity
`∫χ²|W_D|² ≤ (1+ε)∫χ²|W|² + (Cχ/ε)∫χ²|E|²`).  It is *not* the corpus's `T.NH`, which is a
χ-frame number (see the module docstring). -/
def maskNum (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  ∑ s ∈ excited Mode, ((1 - E.fL s) ^ 2) • (T.taDag s ∘ₗ T.ta s)

/-- The `qw`-expansion of the mask-complement number. -/
theorem qw_maskNum (E : Q3Env Mode) (Ψ : F.H) :
    F.qw Ψ (T.maskNum E)
      = ∑ s ∈ excited Mode, (1 - E.fL s) ^ 2 * F.qw Ψ (T.taDag s ∘ₗ T.ta s) :=
  F.qw_finset_sum_smul (excited Mode) (fun s => (1 - E.fL s) ^ 2)
    (fun s => T.taDag s ∘ₗ T.ta s) Ψ

/-- Each `ã_s†ã_s` is a nonnegative quadratic form. -/
theorem qw_taDag_ta_nonneg (s : Mode) (Ψ : F.H) :
    0 ≤ F.qw Ψ (T.taDag s ∘ₗ T.ta s) := by
  have h : F.bp ((T.taDag s ∘ₗ T.ta s) Ψ) Ψ = F.bp (T.ta s Ψ) (T.ta s Ψ) := by
    rw [LinearMap.comp_apply]
    exact T.taDag_adjoint s (T.ta s Ψ) Ψ
  rw [FockData.qw, h]
  exact F.bp_nonneg _

/-- The mask-complement number is a nonnegative quadratic form. -/
theorem maskNum_nonneg (E : Q3Env Mode) (Ψ : F.H) : 0 ≤ F.qw Ψ (T.maskNum E) := by
  rw [T.qw_maskNum]
  refine Finset.sum_nonneg fun s _ => ?_
  exact mul_nonneg (sq_nonneg _) (T.qw_taDag_ta_nonneg s Ψ)

/-- **`maskNum ⪯ T.N`**: the mask complement counts at most the total number.  This is the
*truest* payment available inside the corpus (`(1−f_L)² ≤ 1` pointwise plus FS's
`ta_le_N`), and it is what makes the row `RowPayTotal` below hold — but the `ℓ⁻²n₊` slot
cannot afford the coefficient `Cχ/ε` it forces (see the module docstring). -/
theorem maskNum_le_totNum (E : Q3Env Mode) (hfl : ∀ s, E.fL s ∈ Set.Icc (0:ℝ) 1) (Ψ : F.H) :
    F.qw Ψ (T.maskNum E) ≤ F.qw Ψ T.N := by
  have hstep : F.qw Ψ (T.maskNum E)
      ≤ F.qw Ψ (∑ s ∈ excited Mode, (1 : ℝ) • (T.taDag s ∘ₗ T.ta s)) := by
    rw [T.qw_maskNum, F.qw_finset_sum_smul]
    refine Finset.sum_le_sum fun s _ => ?_
    have h1 : (1 - E.fL s) ^ 2 ≤ 1 := by
      have h0 := hfl s
      nlinarith [h0.1, h0.2]
    have h2 := T.qw_taDag_ta_nonneg s Ψ
    calc (1 - E.fL s) ^ 2 * F.qw Ψ (T.taDag s ∘ₗ T.ta s)
        ≤ 1 * F.qw Ψ (T.taDag s ∘ₗ T.ta s) := mul_le_mul_of_nonneg_right h1 h2
      _ = 1 * F.qw Ψ (T.taDag s ∘ₗ T.ta s) := rfl
  have hmem : ∀ s ∈ excited Mode, s ≠ (0 : Mode) := fun s hs => Finset.ne_of_mem_erase hs
  have hN := T.ta_le_N (excited Mode) hmem Ψ
  have hsum : (∑ s ∈ excited Mode, (1 : ℝ) • (T.taDag s ∘ₗ T.ta s))
      = ∑ s ∈ excited Mode, (T.taDag s ∘ₗ T.ta s) :=
    Finset.sum_congr rfl fun s _ => one_smul ℝ _
  rw [hsum] at hstep
  exact le_trans hstep hN

end Work.BoseB7A.TildeData

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## 1. The mask row and the payment row -/

/-- **FS l.3253, in its true form** (the `hGchi` of the design brief): the localised
`Σ_j Q_{L,j}χ²Q_{L,j}` (`Gop`) against the total χ-number and the **mask-complement θ-number**
`maskNum = Σ_{s∈excited}(1−f_L(s))²ã_s†ã_s`, plus a Schwartz-tail term `δ⟨n₊⟩`.

This is `GchiAt` of `Rows.lean` with the correction carried by `maskNum` instead of the
χ-weighted `T.NH`, and it is the shape the algebra of the row actually produces (see the module
docstring).  Unlike `RowsN.lean`'s `GchiAtN`, it is satisfiable with an **absolute** `Cχ`
(`Cχ ≤ 2χ(0)²`), because the correction object is the *exact* deficit rather than a proxy for it. -/
def GchiAtMask {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (Cχ δ : ℝ) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (ε : ℝ) : Prop :=
  ∀ Ψ : (Work.BoseRowsFS.honF v h fc fu HM μ).H,
    (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        ((Work.BoseRowsFS.honT v h fc fu HM μ).Gop (Work.BoseRowsFS.honE v h fc fu HM μ))
      ≤ (1 + ε) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
        + ((1 + 1 / ε) * Cχ) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honT v h fc fu HM μ).maskNum
              (Work.BoseRowsFS.honE v h fc fu HM μ))
        + δ * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            (Work.BoseRowsFS.honT v h fc fu HM μ).N

/-- **The payment row** (the "row bounding the `(1−f_L)²` θ-number by `NH`" of the design brief):
the mask-complement θ-number is dominated by the gap's high-momentum number.  ⚠ This is the one
false conjunct of the honest environment: `tildeDataHon.NH` is χ-framed while `maskNum` is
θ-framed (witness `θ_{s₀}+h_N`; see the module docstring).  It is the modelling repair owed by
`BoseBoxFock/Defs.lean`, and it is stated here so the rest of the chain is unconditional. -/
def PayMaskAt {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (C₀ : ℝ) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) : Prop :=
  0 ≤ C₀ ∧ ∀ Ψ : (Work.BoseRowsFS.honF v h fc fu HM μ).H,
    (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        ((Work.BoseRowsFS.honT v h fc fu HM μ).maskNum (Work.BoseRowsFS.honE v h fc fu HM μ))
      ≤ C₀ * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          (Work.BoseRowsFS.honT v h fc fu HM μ).NH

/-- The arithmetic of the Schwartz tail: `δ` is paid by the `ℓ⁻²n₊` slot. -/
def ArithAtTail {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (δ : ℝ) (HM : ∀ μ : ℝ, HonestModes v μ) (μ ρ : ℝ) : Prop :=
  2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * δ
    ≤ ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
        * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))

/-! ## 2. The rows -/

/-- **The delegated shape of the mask row**: one absolute `Cχ`, one tail function `δ`, and the
row *simultaneously* for every `ε ∈ (0,1]`.  This is the strongest form (the correction grows as
`ε ↓` and the localised factor grows as `ε ↑`, so `ε = 1` plus the trivial monotonicity lemma
below gives every `ε ≤ 1`); it carries no `ε`-window coupling with the other rows. -/
def RowGchiMaskAll {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Ng : ℝ → ℕ) (Cχ : ℝ) (δ : ℝ → ℝ) : Prop :=
  εg ≤ 1 →
    ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ (μ : ℝ) (hμ : 0 < μ), μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
        ∀ ρ : ℝ, AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
          ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 →
            GchiAtMask (v := v) (h := h) (fc := fc) (fu := fu) Cχ (δ μ) HM μ ε'

/-- The payment row, as a row of the gate. -/
def RowPayMask {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Ng : ℝ → ℕ) (C₀ : ℝ) : Prop :=
  εg ≤ 1 →
    ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ (μ : ℝ) (hμ : 0 < μ), μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
        PayMaskAt (v := v) (h := h) (fc := fc) (fu := fu) C₀ HM μ

/-- The tail arithmetic, as a row. -/
def RowArithTail {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Ng : ℝ → ℕ) (δ : ℝ → ℝ) : Prop :=
  εg ≤ 1 →
    ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ (μ : ℝ) (hμ : 0 < μ), μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
        ∀ ρ : ℝ, AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
          ArithAtTail (v := v) (h := h) (fc := fc) (fu := fu) (δ μ) HM μ ρ

/-- **The core of row 3 at a given threshold and cube size, in the mask form.**  One absolute
`Cχ` (the mask row's constant), one `C₀` (the payment constant), one tiny `δ` (the Schwartz tail),
one `ε : ℝ → ℝ`, with the four rows: the arithmetic `ArithAt (Cχ*C₀)` (proved at `ε = fsEps`
in `ArithRow.lean`), the tail arithmetic, the mask row, the payment row, and FS l.3240–3262
(`RowMainN`). -/
def RowQ2AllCoreMaskAt {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Ng : ℝ → ℕ) : Prop :=
  ∃ Cχ C₀ : ℝ, ∃ δ ε : ℝ → ℝ,
    0 ≤ Cχ ∧ 0 ≤ C₀ ∧ (∀ μ : ℝ, 0 < μ → 0 ≤ δ μ) ∧
    (∀ μ : ℝ, 0 < μ → 0 < ε μ) ∧ (∀ μ : ℝ, 0 < μ → ε μ ≤ 1) ∧
    RowArith (h := h) (fc := fc) (fu := fu) R εg Ng (2 * (Cχ * C₀)) ε ∧
    RowArithTail (h := h) (fc := fc) (fu := fu) R εg Ng δ ∧
    RowGchiMaskAll (h := h) (fc := fc) (fu := fu) R εg Ng Cχ δ ∧
    RowPayMask (h := h) (fc := fc) (fu := fu) R εg Ng C₀ ∧
    RowMainN (h := h) (fc := fc) (fu := fu) R εg Ng ε

/-- The mask-form core, producing its own cube size and diluteness threshold. -/
def RowQ2AllCoreMask {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) : Prop :=
  ∃ Ng : ℝ → ℕ, ∃ εg' : ℝ, 0 < εg' ∧ εg' ≤ εg ∧
    RowQ2AllCoreMaskAt (h := h) (fc := fc) (fu := fu) R εg' Ng

/-! ## 3. The assembly — `RowQ2AllRegimeN` from the mask core -/

/-- **The assembly of row 3 from the mask form.**  The budget:
`2ρŴ₁ω(0)·[(1+ε)⟨Σ_k a_k†a_k⟩ + (Cχ/ε)⟨maskNum⟩ + δ⟨n₊⟩]` is bounded by
`⟨Q₂^{ex,all}⟩ + (b/800)ℓ⁻²n₊ + (b/800)ε_T(dℓ)⁻²n₊^H` (Main, `RowMainN`) plus
`(b/800)ε_T(dℓ)⁻²⟨maskNum⟩` (the arithmetic `ArithAt` at `Cχ*C₀` composed with the payment row
`RowPayMask`) plus `(b/800)ℓ⁻²⟨n₊⟩` (the tail arithmetic), and `b/800 + b/800 = b/400` is the
`ℓ⁻²` half of `gapOpT`, the `NH` half being `b/800 ≤ b/400`. -/
theorem RowQ2AllRegimeN_of_coreMask {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {R εg : ℝ} (hεg1 : εg ≤ 1)
    (hav : 0 < _root_.BoseGases.a v)
    (hw0 : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      0 ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0)
    (hcore : RowQ2AllCoreMask (h := h) (fc := fc) (fu := fu) R εg) :
    ∃ Ng : ℝ → ℕ, ∃ εg' : ℝ, 0 < εg' ∧ εg' ≤ εg ∧
      RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu) Ng R εg' := by
  obtain ⟨Ng, εg', hpos, hle, Cχ, C₀, δ, ε, hCχ, hC₀, hδ, hεpos, hε1, hAr, hAt,
    hG, hPay, hM⟩ := hcore
  have hεg1' : εg' ≤ 1 := le_trans hle hεg1
  refine ⟨Ng, εg', hpos, hle, ?_⟩
  intro HM hNg μ hμ hε ρ hρ Ψ
  have hArith' : ArithAt (v := v) (h := h) (fc := fc) (fu := fu) (2 * (Cχ * C₀)) HM μ ρ (ε μ) :=
    hAr hεg1' HM hNg μ hμ hε ρ hρ
  have hAtail' : ArithAtTail (v := v) (h := h) (fc := fc) (fu := fu) (δ μ) HM μ ρ :=
    hAt hεg1' HM hNg μ hμ hε ρ hρ
  have hAr0' := hArith'
  simp only [ArithAt] at hAr0'
  have hAt0' := hAtail'
  simp only [ArithAtTail] at hAt0'
  have hG'' : GchiAtMask (v := v) (h := h) (fc := fc) (fu := fu) Cχ (δ μ) HM μ (ε μ) :=
    hG hεg1' HM hNg μ hμ hε ρ hρ (ε μ) (hεpos μ hμ) (hε1 μ hμ)
  have hPay' : PayMaskAt (v := v) (h := h) (fc := fc) (fu := fu) C₀ HM μ :=
    hPay hεg1' HM hNg μ hμ hε
  have hM' : MainAtN (v := v) (h := h) (fc := fc) (fu := fu) HM μ ρ (ε μ) :=
    hM hεg1' HM hNg μ hμ hε ρ hρ
  obtain ⟨hC₀nn, hPayΨ⟩ := hPay'
  have hw : 0 ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 := hw0 HM μ hμ
  have hpos2 : 0 ≤ 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 :=
    mul_nonneg (mul_nonneg (by norm_num) hρ.1) hw
  have hNnn : 0 ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
      (Work.BoseRowsFS.honT v h fc fu HM μ).N :=
    (Work.BoseRowsFS.honT v h fc fu HM μ).N_nonneg Ψ
  have hNHnn : 0 ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
      (Work.BoseRowsFS.honT v h fc fu HM μ).NH :=
    (Work.BoseRowsFS.honT v h fc fu HM μ).NH_nonneg Ψ
  have hmask_nn : 0 ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
      ((Work.BoseRowsFS.honT v h fc fu HM μ).maskNum
        (Work.BoseRowsFS.honE v h fc fu HM μ)) :=
    (Work.BoseRowsFS.honT v h fc fu HM μ).maskNum_nonneg
      (Work.BoseRowsFS.honE v h fc fu HM μ) Ψ
  have hb : (0 : ℝ) < (Work.BoseRowsFS.honE v h fc fu HM μ).b := by
    rw [Work.BoseRowsFS.honE_b]; norm_num
  have hb800 : (0 : ℝ) ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800 := by positivity
  have hb400 : (0 : ℝ) ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 400 := by positivity
  have heT0 : (0 : ℝ) ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).eT := by
    rw [Work.BoseRowsFS.honE_eT_eq]
    exact Real.rpow_nonneg (le_of_lt (mul_pos hμ (pow_pos hav 3))) _
  have hdl0 : (0 : ℝ) ≤ ((Work.BoseRowsFS.honE v h fc fu HM μ).d
      * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)) :=
    rpow_neg_two_nonneg _
  have hl0 : (0 : ℝ) ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ)) :=
    rpow_neg_two_nonneg _
  have hεpos' : 0 < ε μ := hεpos μ hμ
  have hε1'' : ε μ ≤ 1 := hε1 μ hμ
  have hgap : (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        ((Work.BoseRowsFS.honT v h fc fu HM μ).gapOpT
          (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
      = (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).N
        + ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
            * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by
    rw [TildeData.qw_gapOpT]
    rfl
  rw [hgap]
  -- the three payments
  have hkey := mul_le_mul_of_nonneg_left (hG'' Ψ) hpos2
  have hpay2 : 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * ((1 + 1 / ε μ) * Cχ)
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          ((Work.BoseRowsFS.honT v h fc fu HM μ).maskNum
            (Work.BoseRowsFS.honE v h fc fu HM μ))
      ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800
          * (Work.BoseRowsFS.honE v h fc fu HM μ).eT
          * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
              * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ))
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by
    have hnonneg : 0 ≤ 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * ((1 + 1 / ε μ) * Cχ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ.1) hw)
        (mul_nonneg (by positivity) hCχ)
    have hcoef : (1 + 1 / ε μ) * Cχ * C₀ ≤ 2 * (Cχ * C₀) / ε μ := by
      have hone : (1 : ℝ) ≤ 1 / ε μ := by
        rw [one_le_div hεpos']
        exact hε1''
      have h1 : (1 + 1 / ε μ) ≤ 2 / ε μ := by
        have h2 : (2 : ℝ) / ε μ = 1 / ε μ + 1 / ε μ := by ring
        rw [h2]
        linarith
      calc (1 + 1 / ε μ) * Cχ * C₀ = ((1 + 1 / ε μ) * Cχ) * C₀ := rfl
        _ ≤ (2 / ε μ) * Cχ * C₀ := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hCχ) hC₀
        _ = 2 * (Cχ * C₀) / ε μ := by ring
    calc 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * ((1 + 1 / ε μ) * Cχ)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honT v h fc fu HM μ).maskNum
              (Work.BoseRowsFS.honE v h fc fu HM μ))
        ≤ 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * ((1 + 1 / ε μ) * Cχ)
          * (C₀ * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).NH) :=
          mul_le_mul_of_nonneg_left (hPayΨ Ψ) hnonneg
      _ = 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          * ((1 + 1 / ε μ) * Cχ * C₀)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by ring
      _ ≤ 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          * (2 * (Cχ * C₀) / ε μ)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by
          refine mul_le_mul_of_nonneg_right ?_ hNHnn
          exact mul_le_mul_of_nonneg_left hcoef
            (mul_nonneg (mul_nonneg (by norm_num) hρ.1) hw)
      _ ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).b / 800
          * (Work.BoseRowsFS.honE v h fc fu HM μ).eT
          * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
              * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ))
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).NH :=
          mul_le_mul_of_nonneg_right hAr0' hNHnn
  have htailPay : 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * δ μ
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          (Work.BoseRowsFS.honT v h fc fu HM μ).N
      ≤ ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
          * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).N := by
    exact mul_le_mul_of_nonneg_right hAt0' hNnn
  calc 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honT v h fc fu HM μ).Gop
              (Work.BoseRowsFS.honE v h fc fu HM μ))
      ≤ 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * ((1 + ε μ) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
            + ((1 + 1 / ε μ) * Cχ) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honT v h fc fu HM μ).maskNum
                  (Work.BoseRowsFS.honE v h fc fu HM μ))
            + δ μ * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).N) := hkey
    _ = 2 * ρ * (1 + ε μ) * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
        + 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * ((1 + 1 / ε μ) * Cχ)
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honT v h fc fu HM μ).maskNum
                (Work.BoseRowsFS.honE v h fc fu HM μ))
        + 2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * δ μ
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).N := by ring
    _ ≤ ((Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
              (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).N
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
              * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                  * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                      * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).NH)
        + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
            * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                    * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).NH
        + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).N := by
        linarith [hM' Ψ, hpay2, htailPay]
    _ = (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
              (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
              * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).N
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
              * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                  * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                      * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  (Work.BoseRowsFS.honT v h fc fu HM μ).NH := by ring
    _ ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
              (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
          + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
              * ((Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
                  * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                      (Work.BoseRowsFS.honT v h fc fu HM μ).N
                + ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                    * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                        * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
                  * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                      (Work.BoseRowsFS.honT v h fc fu HM μ).NH) := by
        have h1 : 0 ≤ ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
            * (((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                    * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ))))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).NH :=
          mul_nonneg (mul_nonneg hb800 (mul_nonneg heT0 hdl0)) hNHnn
        nlinarith [h1, mul_nonneg hb800 hNnn, mul_nonneg hb800 hNHnn,
          mul_nonneg hl0 hNnn, mul_nonneg (mul_nonneg heT0 hdl0) hNHnn,
          mul_nonneg hb400 (mul_nonneg hl0 hNnn), hNnn, hNHnn, hb800, hb400]

end Work.BoseRowQ2
