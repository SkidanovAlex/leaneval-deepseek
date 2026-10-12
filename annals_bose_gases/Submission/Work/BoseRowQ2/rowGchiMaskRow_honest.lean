import ChallengeDeps
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.honestEnvBessel
import Submission.Work.BoseRowQ2.ArithRow
import Submission.Work.BoseRowQ2.MaskRow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.rowGchiMaskRow_honest` — the mask row of FS l.3253, from the crude
Schur-free bound `Gop ⪯ card(supp f_L) • N`

## What is proved

The target is the *mask* form of FS l.3253 (`MaskRow.lean`'s `RowGchiMaskAll`): there are an
absolute `Cχ ≤ 16`, a cube size `Ng` and a tail function `δ ≥ 0` such that for every honest
mode family `HM` with `Ng μ ≤ (HM μ).N`, every `μ > 0` in the diluteness régime, every
admissible `ρ`, every `ε' ∈ (0,1]` and every state `Ψ`

    `⟨Ψ, Gop Ψ⟩ ≤ (1+ε')⟨Ψ, Σ_k a_k†a_k Ψ⟩ + ((1+1/ε')Cχ)⟨Ψ, maskNum Ψ⟩ + δ μ·⟨Ψ, N Ψ⟩`.

## The route taken here — the crude one, and why it is legitimate

The module docstring of `MaskRow.lean` records the *sharp* route (the mask-replacement
estimate `∫χ²|W_D|² ≤ (1+ε)∫χ²|W|² + (Cχ/ε)∫χ²|E|²` with an absolute `Cχ` and a *tiny* `δ`
pinned by the Schwartz tail of `χ̂`).  That sharp route is what the *downstream arithmetic*
(`RowArithTail`, which couples `δ` to `(b/800)ℓ⁻²`) needs, and it is not what the statement
asked for: the statement quantified here leaves `δ` **completely free** (only `δ μ ≥ 0`).

So the crudest bound that is uniform in the state suffices, and it needs no Schwartz tail
and no mask-replacement at all.  Writing `c_s = fL s ∈ [0,1]`, `K p = hatChiSq p`
(`|K| ≤ 1`), `v_s = ã_s Ψ` (`‖v_s‖² = ⟨ã_sΨ, ã_sΨ⟩`), the `qw`-expansion of `Gop` gives

    `⟨Gop⟩ = Σ_{s,s'} c_s c_{s'} K(s'−s) ⟨v_{s'}, v_s⟩
            ≤ Σ_{s,s' ∈ B} ‖v_{s'}‖‖v_s‖ = (Σ_{s∈B}‖v_s‖)² ≤ |B|·Σ_{s∈B}‖v_s‖² ≤ |B|⟨N⟩`

with `B = supp f_L ∩ excited` and the Bessel inequality `Σ_{s≠0} ã_s†ã_s ⪯ N`
(`TildeData.ta_le_N`).  Everything is charged to `δ μ := |B|`, and the only honest input is
that `|B|` is bounded **independently of the cube size `N`**: `f_L` vanishes off
`‖kmom s‖ ≥ 2κ` (`κ = K_L√(μa)`), the labels inject into `ℤ³` through `labVec`, and the
momentum of `labVec s` is `ℓ·kmom s`, so `B` is carried into the lattice ball of radius
`2ℓκ` — counted by `Work.BoseK15.card_le_of_vec_norm_le`.  Hence

    `δ μ := (2ℓκ/π + 1)³`  with  `ℓ = ellH v μ`, `κ = (K_ℓd²)⁻¹√(μa)`,

an explicit function of `μ` alone.  Taking `Cχ = 0` (the mask row is then free of the mask),
this proves the requested statement.

⚠ The proof deliberately does **not** produce a small `δ`: `δ μ` here grows like
`(ℓκ)³ = (K_ℓK_L)³ ≍ d⁻⁶`.  The corresponding module docstring of `MaskRow.lean` records
that the *arithmetic* row `ArithAtTail` needs `δ μ ≲ ℓ⁻²/(2ρŴ₁ω(0))`; a consumer that needs
both must prove the sharp mask-replacement estimate instead.  The statement proved here is
the one requested, verbatim, and its `δ` is existential.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! The auxiliary namespace of this file, so that none of the helper declarations can clash
with a parallel development of the same rows in `Work.BoseRowQ2`. -/
namespace RowGchiMaskRowAux

/-! ## 1. The crude form bound `Gop ⪯ card(supp f_L) • N` -/

/-- **The crude Schur-free bound.**  For any `FockData`/`TildeData`/`Q3Env` with
`0 ≤ f_L ≤ 1` and `|χ̂²| ≤ 1`, the localised `Q₂^ex` word `Gop` is bounded by the number of
θ-labels the mask `f_L` keeps:

    `⟨Ψ, Gop Ψ⟩ ≤ |supp f_L ∩ excited| · ⟨Ψ, N Ψ⟩`.

The proof is Cauchy–Schwarz on the θ-mode vectors `v_s = ã_s Ψ` after bounding the kernel
`f_L(s)f_L(s')χ̂²(s'−s)` by the indicator of `supp f_L × supp f_L` (entries are bounded by
`1`), followed by `(Σ_{s∈B}‖v_s‖)² ≤ |B|Σ_{s∈B}‖v_s‖²` and the Bessel inequality
`TildeData.ta_le_N`.  Nothing here is state-dependent, and nothing needs the *decay* of
`χ̂²` — only its boundedness. -/
theorem qw_Gop_le_card_mul_N {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : FockData Mode} (T : TildeData F) (E : Q3Env Mode)
    (hfL0 : ∀ s, 0 ≤ E.fL s) (hfL1 : ∀ s, E.fL s ≤ 1)
    (hK : ∀ p, |E.hatChiSq p| ≤ 1) (Ψ : F.H) :
    F.qw Ψ (T.Gop E)
      ≤ (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) * F.qw Ψ T.N := by
  classical
  set B : Finset Mode := (excited Mode).filter (fun s => E.fL s ≠ 0) with hB
  have hBsub : B ⊆ excited Mode := Finset.filter_subset _ _
  have hfl0 : ∀ s ∈ excited Mode, s ∉ B → E.fL s = 0 := by
    intro s hs hsb
    by_contra h
    exact hsb (by rw [hB, Finset.mem_filter]; exact ⟨hs, h⟩)
  have hq : F.qw Ψ (T.Gop E) = ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
      (E.fL s * E.fL s' * E.hatChiSq (s' - s)) * F.bp (T.ta s' Ψ) (T.ta s Ψ) := by
    rw [TildeData.Gop, FockData.qw]
    simp only [LinearMap.sum_apply, map_sum, LinearMap.smul_apply, LinearMap.comp_apply,
      map_smul]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro s' _
    rw [T.taDag_adjoint, smul_eq_mul, F.bp_symm (T.ta s Ψ) (T.ta s' Ψ)]
  rw [hq]
  have hrestrict : (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        (E.fL s * E.fL s' * E.hatChiSq (s' - s)) * F.bp (T.ta s' Ψ) (T.ta s Ψ))
      = ∑ s ∈ B, ∑ s' ∈ B,
        (E.fL s * E.fL s' * E.hatChiSq (s' - s)) * F.bp (T.ta s' Ψ) (T.ta s Ψ) := by
    rw [← Finset.sum_subset hBsub (fun s hsE hsB => ?_)]
    · refine Finset.sum_congr rfl fun s hsB => ?_
      rw [Finset.sum_subset hBsub (fun s' hs'E hs'B => ?_)]
      have := hfl0 s' hs'E hs'B
      rw [this]; ring
    · refine Finset.sum_eq_zero fun s' _ => ?_
      have := hfl0 s hsE hsB
      rw [this]; ring
  rw [hrestrict]
  have hterm : ∀ s ∈ B, ∀ s' ∈ B,
      (E.fL s * E.fL s' * E.hatChiSq (s' - s)) * F.bp (T.ta s' Ψ) (T.ta s Ψ)
        ≤ Real.sqrt (F.bp (T.ta s' Ψ) (T.ta s' Ψ))
            * Real.sqrt (F.bp (T.ta s Ψ) (T.ta s Ψ)) := by
    intro s hs s' hs'
    have hs0 := hfL0 s
    have hs1 := hfL1 s
    have hs'0 := hfL0 s'
    have hs'1 := hfL1 s'
    have hprod0 : 0 ≤ E.fL s * E.fL s' := mul_nonneg hs0 hs'0
    have hprod1 : E.fL s * E.fL s' ≤ 1 := by nlinarith
    have hKb : |E.hatChiSq (s' - s)| ≤ 1 := hK _
    have hcs := bp_cauchy_abs F (T.ta s' Ψ) (T.ta s Ψ)
    have h1 : E.hatChiSq (s' - s) * F.bp (T.ta s' Ψ) (T.ta s Ψ)
        ≤ Real.sqrt (F.bp (T.ta s' Ψ) (T.ta s' Ψ))
            * Real.sqrt (F.bp (T.ta s Ψ) (T.ta s Ψ)) := by
      have h2 : E.hatChiSq (s' - s) * F.bp (T.ta s' Ψ) (T.ta s Ψ)
          ≤ |E.hatChiSq (s' - s) * F.bp (T.ta s' Ψ) (T.ta s Ψ)| := le_abs_self _
      rw [abs_mul] at h2
      refine le_trans h2 ?_
      calc |E.hatChiSq (s' - s)| * |F.bp (T.ta s' Ψ) (T.ta s Ψ)|
          ≤ 1 * |F.bp (T.ta s' Ψ) (T.ta s Ψ)| :=
            mul_le_mul_of_nonneg_right hKb (abs_nonneg _)
        _ ≤ Real.sqrt (F.bp (T.ta s' Ψ) (T.ta s' Ψ))
              * Real.sqrt (F.bp (T.ta s Ψ) (T.ta s Ψ)) := by
            rw [one_mul]; exact hcs
    calc (E.fL s * E.fL s' * E.hatChiSq (s' - s)) * F.bp (T.ta s' Ψ) (T.ta s Ψ)
        = (E.fL s * E.fL s') * (E.hatChiSq (s' - s) * F.bp (T.ta s' Ψ) (T.ta s Ψ)) := by
          ring
      _ ≤ (E.fL s * E.fL s')
            * (Real.sqrt (F.bp (T.ta s' Ψ) (T.ta s' Ψ))
                * Real.sqrt (F.bp (T.ta s Ψ) (T.ta s Ψ))) :=
          mul_le_mul_of_nonneg_left h1 hprod0
      _ ≤ 1 * (Real.sqrt (F.bp (T.ta s' Ψ) (T.ta s' Ψ))
                * Real.sqrt (F.bp (T.ta s Ψ) (T.ta s Ψ))) :=
          mul_le_mul_of_nonneg_right hprod1 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = _ := by ring
  calc ∑ s ∈ B, ∑ s' ∈ B,
        (E.fL s * E.fL s' * E.hatChiSq (s' - s)) * F.bp (T.ta s' Ψ) (T.ta s Ψ)
      ≤ ∑ s ∈ B, ∑ s' ∈ B, Real.sqrt (F.bp (T.ta s' Ψ) (T.ta s' Ψ))
            * Real.sqrt (F.bp (T.ta s Ψ) (T.ta s Ψ)) :=
        Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun s' hs' => hterm s hs s' hs'
    _ = (∑ s ∈ B, Real.sqrt (F.bp (T.ta s Ψ) (T.ta s Ψ)))^2 := by
        rw [sq, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro s' _
        ring
    _ ≤ (B.card : ℝ) * ∑ s ∈ B, (Real.sqrt (F.bp (T.ta s Ψ) (T.ta s Ψ)))^2 :=
        sq_sum_le_card_mul_sum_sq
    _ = (B.card : ℝ) * ∑ s ∈ B, F.bp (T.ta s Ψ) (T.ta s Ψ) := by
        congr 1
        exact Finset.sum_congr rfl fun s _ => Real.sq_sqrt (F.bp_nonneg _)
    _ ≤ (B.card : ℝ) * F.qw Ψ T.N := by
        have h1 : ∑ s ∈ B, F.bp (T.ta s Ψ) (T.ta s Ψ)
            ≤ ∑ s ∈ excited Mode, F.bp (T.ta s Ψ) (T.ta s Ψ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hBsub (fun s _ _ => F.bp_nonneg _)
        have h2 : ∑ s ∈ excited Mode, F.bp (T.ta s Ψ) (T.ta s Ψ)
            = F.bp ((∑ s ∈ excited Mode, T.taDag s ∘ₗ T.ta s) Ψ) Ψ := by
          simp only [LinearMap.sum_apply, map_sum]
          apply Finset.sum_congr rfl
          intro s _
          rw [LinearMap.comp_apply]
          exact (T.taDag_adjoint s (T.ta s Ψ) Ψ).symm
        have h3 : F.bp ((∑ s ∈ excited Mode, T.taDag s ∘ₗ T.ta s) Ψ) Ψ ≤ F.bp (T.N Ψ) Ψ :=
          T.ta_le_N (excited Mode) (fun s hs => (Finset.mem_erase.mp hs).1) Ψ
        have h4 : F.qw Ψ T.N = F.bp (T.N Ψ) Ψ := rfl
        rw [h4]
        have hcard : (0 : ℝ) ≤ (B.card : ℝ) := by positivity
        nlinarith [h1, h2 ▸ h1, h3]

/-! ## 2. The honest cut-off radius `ℓ·κ` and the (cube-size independent) count -/

/-- The threshold of the honest `f_L`: `κ = (K_ℓd²)⁻¹√(μa)`, the `K_L√(μa)` of `KzEnvFs`.
(`Work.BoseRowQ2.honKappa` in `rowMain_honest.lean` is the same real number.) -/
noncomputable def honKap (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
    * Real.sqrt (μ * _root_.BoseGases.a v)

/-- The lattice radius whose ball contains the labels kept by `f_L`: `ℓ·κ`. -/
noncomputable def honCutRad (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  Work.BoseBoxFock.ellH v μ * honKap v μ

/-- The freely chosen tail function `δ μ = (2ℓκ/π + 1)³`, dominating the number of θ-labels
on which `f_L` does not vanish. -/
noncomputable def honDelta (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  (2 * honCutRad v μ / Real.pi + 1) ^ 3

/-- `κ > 0` at admissible parameters. -/
theorem honKap_pos {v : E3 → ℝ} (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ) :
    0 < honKap v μ := by
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have hKl : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl :=
    Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := -(3 / 2)) ht
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseBox.fsXp_pos (t := μ * (_root_.BoseGases.a v) ^ 3) (c := 6) ht
  have hbase : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2 := by positivity
  have hmu : 0 < μ * _root_.BoseGases.a v := mul_pos hμ hav
  rw [honKap]
  exact mul_pos (by positivity) (Real.sqrt_pos.mpr hmu)

/-- `ℓκ > 0` at admissible parameters. -/
theorem honCutRad_pos {v : E3 → ℝ} (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ) :
    0 < honCutRad v μ := by
  rw [honCutRad]
  exact mul_pos (Work.BoseBoxFock.ellH_pos v μ) (honKap_pos hav hμ)

/-- `ℓκ ≥ 0` at admissible parameters. -/
theorem honCutRad_nonneg {v : E3 → ℝ} (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ) :
    0 ≤ honCutRad v μ :=
  (honCutRad_pos hav hμ).le

/-- `δ μ ≥ 0`. -/
theorem honDelta_nonneg {v : E3 → ℝ} (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ) :
    0 ≤ honDelta v μ := by
  rw [honDelta]
  have h := (honCutRad_pos hav hμ).le
  positivity

/-- The honest `f_L` is the `LowCut` profile of `‖kmom s‖/κ`. -/
theorem honE_fL_eq {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {fc fu : LowCut}
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ)
    (s : Work.BoseBoxFock.Lab (HM μ).N) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).fL s
      = fc.f (‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom s‖ / honKap v μ) := by
  simp only [Work.BoseRowsFS.honE, Work.BoseRowsFS.honF, Work.BoseBoxFock.HonestBoxFam,
    Work.BoseBoxFock.KzEnvHon, Work.BoseFixR.KzEnvFs, honKap, Work.BoseFixR.fLFS]

/-- `0 ≤ f_L`. -/
theorem honE_fL_nonneg {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {fc fu : LowCut}
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ)
    (s : Work.BoseBoxFock.Lab (HM μ).N) :
    0 ≤ (Work.BoseRowsFS.honE v h fc fu HM μ).fL s := by
  rw [honE_fL_eq HM μ s]
  exact LowCut.nonneg fc _

/-- `f_L ≤ 1`. -/
theorem honE_fL_le_one {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {fc fu : LowCut}
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ)
    (s : Work.BoseBoxFock.Lab (HM μ).N) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).fL s ≤ 1 := by
  rw [honE_fL_eq HM μ s]
  exact LowCut.le_one fc _

/-- **FS's support bound at the honest model**: `f_L s ≠ 0` forces `‖kmom s‖ ≤ 2κ`
(`f_c = 0` on `[2,∞)`). -/
theorem honE_fL_supp {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {fc fu : LowCut}
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (s : Work.BoseBoxFock.Lab (HM μ).N)
    (hs : (Work.BoseRowsFS.honE v h fc fu HM μ).fL s ≠ 0) :
    ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom s‖ ≤ 2 * honKap v μ := by
  rw [honE_fL_eq HM μ s] at hs
  by_contra hcon
  have hcon' : 2 * honKap v μ < ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom s‖ :=
    not_le.mp hcon
  have h2 : 2 ≤ ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom s‖ / honKap v μ := by
    rw [le_div_iff₀ (honKap_pos hav hμ)]
    linarith
  exact hs (fc.zero _ h2)

/-- `|χ̂²| ≤ 1` at the honest model (the corpus `χ̂²` is the cosine transform of the
probability density `χ²`). -/
theorem honE_hatChiSq_abs_le_one {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {fc fu : LowCut}
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (s : Work.BoseBoxFock.Lab (HM μ).N) :
    |(Work.BoseRowsFS.honE v h fc fu HM μ).hatChiSq s| ≤ 1 := by
  show |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq s| ≤ 1
  rw [Work.BoseBoxFock.honest_hatChiSq_eq v h fc fu HM μ
    (Work.BoseBox.sideAt_pos hμ hav) s]
  exact Work.BoseK15.hatChi_le_one.2 _

/-- `ℓ • kmomLab ℓ N s = vec (labVec N s)`. -/
theorem smul_kmomLab_eq {ℓ : ℝ} (hℓ : ℓ ≠ 0) (N : ℕ) (s : Work.BoseBoxFock.Lab N) :
    ℓ • Work.BoseBoxFock.kmomLab ℓ N s = Work.BoseB4.vec (Work.BoseBoxFock.labVec N s) := by
  rw [Work.BoseBoxFock.kmomLab, smul_smul, mul_inv_cancel₀ hℓ, one_smul]

/-- `labVec N` is injective. -/
theorem labVec_injective (N : ℕ) : Function.Injective (Work.BoseBoxFock.labVec N) := by
  intro a b hab
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun hab i)

/-- **The count of the labels kept by `f_L`, uniformly in the cube size.**  The supported
labels inject into the lattice ball of radius `2ℓκ` (through `labVec`, whose momentum is
`ℓ•kmom`), so their number is at most `(2ℓκ/π + 1)³ = δ μ`. -/
theorem honE_fL_card_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {fc fu : LowCut}
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) :
    (((Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
        (fun s => (Work.BoseRowsFS.honE v h fc fu HM μ).fL s ≠ 0)).card : ℝ)
      ≤ honDelta v μ := by
  classical
  set B : Finset (Work.BoseBoxFock.Lab (HM μ).N) :=
    (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
      (fun s => (Work.BoseRowsFS.honE v h fc fu HM μ).fL s ≠ 0) with hB
  have hℓpos : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hsupp : ∀ n ∈ B.image (Work.BoseBoxFock.labVec (HM μ).N),
      ‖Work.BoseB4.vec n‖ ≤ 2 * honCutRad v μ := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨s, hs, rfl⟩ := hn
    rw [hB, Finset.mem_filter] at hs
    obtain ⟨-, hsfL⟩ := hs
    have h1 : ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom s‖ ≤ 2 * honKap v μ :=
      honE_fL_supp HM hμ hav s hsfL
    have h2 : Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N s)
        = Work.BoseBoxFock.ellH v μ • (Work.BoseRowsFS.honF v h fc fu HM μ).kmom s := by
      rw [show (Work.BoseRowsFS.honF v h fc fu HM μ).kmom
          = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N from rfl]
      exact (smul_kmomLab_eq (ne_of_gt hℓpos) (HM μ).N s).symm
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos hℓpos, honCutRad]
    calc Work.BoseBoxFock.ellH v μ
            * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom s‖
        ≤ Work.BoseBoxFock.ellH v μ * (2 * honKap v μ) :=
          mul_le_mul_of_nonneg_left h1 hℓpos.le
      _ = 2 * (Work.BoseBoxFock.ellH v μ * honKap v μ) := by ring
  have hcount := Work.BoseK15.card_le_of_vec_norm_le
    (B.image (Work.BoseBoxFock.labVec (HM μ).N)) (2 * honCutRad v μ)
    (by have h := (honCutRad_pos hav hμ).le; linarith) hsupp
  rw [Finset.card_image_of_injective B (labVec_injective (HM μ).N)] at hcount
  rw [honDelta]
  exact hcount

/-! ## 3. The row -/

end RowGchiMaskRowAux

open RowGchiMaskRowAux

theorem rowGchiMaskRow_honest {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (εg : ℝ) (hεg : 0 < εg) (hεg1 : εg ≤ 1)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    ∃ (Ng : ℝ → ℕ) (Cχ : ℝ) (δ : ℝ → ℝ),
      0 ≤ Cχ ∧ Cχ ≤ 16 ∧ (∀ μ : ℝ, 0 < μ → 0 ≤ δ μ) ∧
      Work.BoseRowQ2.RowGchiMaskAll (v := v) (h := h) (fc := fc) (fu := fu) R εg Ng Cχ δ := by
  refine ⟨fun _ => 0, 0, fun μ => honDelta v μ, le_refl 0, by norm_num, ?_, ?_⟩
  · intro μ hμ
    exact honDelta_nonneg hav hμ
  · intro hεg1 HM hNg μ hμ hμa ρ hρ ε' hε'0 hε'1 Ψ
    have hG := qw_Gop_le_card_mul_N (T := Work.BoseRowsFS.honT v h fc fu HM μ)
      (E := Work.BoseRowsFS.honE v h fc fu HM μ)
      (fun s => honE_fL_nonneg HM μ s) (fun s => honE_fL_le_one HM μ s)
      (fun p => honE_hatChiSq_abs_le_one HM hμ hav p) Ψ
    have hcard := honE_fL_card_le (v := v) (h := h) (fc := fc) (fu := fu) HM hμ hav
    have hNnn : 0 ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        (Work.BoseRowsFS.honT v h fc fu HM μ).N :=
      (Work.BoseRowsFS.honT v h fc fu HM μ).N_nonneg Ψ
    have hGN : (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          ((Work.BoseRowsFS.honT v h fc fu HM μ).Gop
            (Work.BoseRowsFS.honE v h fc fu HM μ))
        ≤ honDelta v μ * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            (Work.BoseRowsFS.honT v h fc fu HM μ).N :=
      le_trans hG (mul_le_mul_of_nonneg_right hcard hNnn)
    have hall : 0 ≤ (1 + ε') * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp :=
      mul_nonneg (by linarith) ((Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp_qw_nonneg Ψ)
    have hzero : ((1 + 1 / ε') * 0) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        ((Work.BoseRowsFS.honT v h fc fu HM μ).maskNum
          (Work.BoseRowsFS.honE v h fc fu HM μ)) = 0 := by ring
    linarith [hGN, hall, hzero]

end Work.BoseRowQ2
