import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseGateFS.HonRowsDecay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.honE_hatChiSq_form_upper` — the Schur `form_upper` row at the honest model

The `form_upper` row of `HonestRows` (`Work.BoseGateFS.HonestRows`, FS §10's
`hatChiSq_form` upper half) **at the honest model**: the quadratic form

    `Σ_{s,s'∈Ss} c s · c s' · χ̂²(s'-s) · ⟨w s', w s⟩`

is bounded above by `K₀ · Σ_s c s² ⟨w s, w s⟩`.

The corpus supplies this row only under the `Work.BoseK15.K15Input` bundle
(`Work.BoseK15.hatChiSq_form_upper`), which has *no* honest instance (finding
F1/F7, `FINDING_K15R_input_vacuous.md`).  Here the two ingredients of the Schur
test are derived at the honest data instead:

* **the χ̂²-row bound** (`honE_hatChiSq_row_le`): the χ-pin
  `KinkEnv.honE_hatChiSq` reads `E.hatChiSq (γ s)` as the corpus `χ̂²` at the
  dual-lattice point `vec (hlat.lift (γ s))` (via `honE_onDualLattice`); the
  decay `ChiReg` and the *uniform* lattice-weight bound `hsuminv` — the honest
  replacement for the `K15Input.sum_geom` row — give `Cchi · Csum` for **any**
  injective `γ : Lab → Lab`.  The two orientations needed by the Schur test are
  `γ x = x - s` and `γ x = s - x` (`sub_left_injective`/`sub_right_injective`):
  no evenness of `χ̂²` is used;
* **the pointwise Cauchy–Schwarz + AM–GM bound** (`Work.BoseK15.bp_mul_abs_le`)
  and **the abstract Schur row-sum lemma** (`Work.BoseK15.double_sum_row_bound`),
  both re-used from the `BoseK15` Schur file;
* the row constant `Cchi · Csum` is dominated by `K₀` by hypothesis.

## Contents

* `honE_hatChiSq_row_le` — the row bound for an arbitrary injective relabelling;
* `honE_hatChiSq_row_sum_fst`, `honE_hatChiSq_row_sum_snd` — the two orientations;
* `honE_hatChiSq_form_upper` — the target.
-/

noncomputable section

open scoped BigOperators Pointwise Real

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
variable {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ}

/-! ## 1. The `χ̂²`-row bound at the honest model -/

/-- **The row bound.**  For *any* injective relabelling `γ` of the modes, the row
sum of `|E.hatChiSq (γ ·)|` is bounded by the lattice constant `Cchi · Csum`.

The mode `γ s` sits at the dual-lattice point `vec (hlat.lift (γ s))` under the
scaling `E.ell` (`honE_onDualLattice`), the χ-pin `honE_hatChiSq` identifies
`E.hatChiSq` with the corpus `χ̂²` there, `ChiReg` bounds each term by
`Cchi·(1+‖·‖²)^{-decayOrder}`, and the injectivity of `γ` turns the sum over `Ss`
into the sum over its lattice image, dominated by `hsuminv`. -/
theorem honE_hatChiSq_row_le (S : HonSetup v h fc fu HM μ) {Cchi Csum : ℝ} (hCchi : 0 ≤ Cchi)
    (hchi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox Work.BoseK15.decayOrder Cchi)
    (hsuminv : ∀ S' : Finset (Fin 3 → ℤ),
      (∑ n ∈ S', (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹) ≤ Csum) :
    ∀ (γ : Lab (HM μ).N → Lab (HM μ).N), Function.Injective γ → ∀ Ss : Finset (Lab (HM μ).N),
      ∑ s ∈ Ss, |(honE v h fc fu HM μ).hatChiSq (γ s)| ≤ Cchi * Csum := by
  classical
  have hlat : Work.BoseK15.OnDualLattice (Work.BoseBoxFock.ellH v μ)
      (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N) :=
    honE_onDualLattice S
  -- the corpus `χ̂²`-decay, in the reciprocal form used below
  have hdecay : ∀ p : EuclideanSpace ℝ (Fin 3),
      |Work.BoseK15.corpusBox.hatChiSq p|
        ≤ Cchi * (((1 : ℝ) + ‖p‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹ := by
    intro p
    have h1 := hchi.2 p
    have hpos : 0 < ((1 : ℝ) + ‖p‖ ^ 2) ^ Work.BoseK15.decayOrder := by positivity
    rw [le_mul_inv_iff₀ hpos]
    exact h1
  intro γ hγ Ss
  -- the lattice label: `ℓ • kmom (γ s) = vec (lift (γ s))`
  have hsm : ∀ s : Lab (HM μ).N,
      (honE v h fc fu HM μ).ell • (honF v h fc fu HM μ).kmom (γ s)
        = Work.BoseB4.vec (hlat.lift (γ s)) := by
    intro s
    rw [honE_ell S, honF_kmom, hlat.lift_spec, smul_smul,
      mul_inv_cancel₀ (ne_of_gt (Work.BoseBoxFock.ellH_pos v μ)), one_smul]
  -- the χ-pin at the lattice label
  have hpin : ∀ s : Lab (HM μ).N,
      (honE v h fc fu HM μ).hatChiSq (γ s)
        = Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (hlat.lift (γ s))) := by
    intro s
    rw [show (honE v h fc fu HM μ).hatChiSq (γ s)
          = Work.BoseK15.corpusBox.hatChiSq ((honE v h fc fu HM μ).ell
              • (honF v h fc fu HM μ).kmom (γ s)) from
        honE_hatChiSq S.hav S.hμ (honF v h fc fu HM μ) (HM μ).N (γ s), hsm s]
  have hterm : ∀ s : Lab (HM μ).N,
      |(honE v h fc fu HM μ).hatChiSq (γ s)|
        ≤ Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (hlat.lift (γ s))‖ ^ 2)
            ^ Work.BoseK15.decayOrder)⁻¹ := fun s => by
    rw [hpin s]
    exact hdecay _
  have hinj : Set.InjOn (fun s => hlat.lift (γ s)) ↑Ss := by
    intro x _ y _ hxy
    exact hγ (hlat.lift_injective hxy)
  calc ∑ s ∈ Ss, |(honE v h fc fu HM μ).hatChiSq (γ s)|
      ≤ ∑ s ∈ Ss, Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec (hlat.lift (γ s))‖ ^ 2)
          ^ Work.BoseK15.decayOrder)⁻¹ := Finset.sum_le_sum fun s _ => hterm s
    _ = Cchi * ∑ s ∈ Ss, (((1 : ℝ) + ‖Work.BoseB4.vec (hlat.lift (γ s))‖ ^ 2)
          ^ Work.BoseK15.decayOrder)⁻¹ := by rw [Finset.mul_sum]
    _ = Cchi * ∑ n ∈ Ss.image (fun s => hlat.lift (γ s)),
          (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹ := by
        rw [Finset.sum_image hinj]
    _ ≤ Cchi * Csum := mul_le_mul_of_nonneg_left (hsuminv _) hCchi

/-- The row bound with the *varying* index in the second slot of the difference
(`χ̂²(x - s)`, `s` fixed).  No evenness of `χ̂²` is used: the relabelling
`x ↦ x - s` is injective. -/
theorem honE_hatChiSq_row_sum_fst (S : HonSetup v h fc fu HM μ) {Cchi Csum : ℝ}
    (hCchi : 0 ≤ Cchi)
    (hchi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox Work.BoseK15.decayOrder Cchi)
    (hsuminv : ∀ S' : Finset (Fin 3 → ℤ),
      (∑ n ∈ S', (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹) ≤ Csum)
    (s : Lab (HM μ).N) (Ss : Finset (Lab (HM μ).N)) :
    ∑ s' ∈ Ss, |(honE v h fc fu HM μ).hatChiSq (s' - s)| ≤ Cchi * Csum :=
  honE_hatChiSq_row_le S hCchi hchi hsuminv (fun x => x - s) sub_left_injective Ss

/-- The transposed row bound: the *varying* index in the first slot of the
difference (`χ̂²(s - x)`, `s` fixed), via the injective relabelling `x ↦ s - x`. -/
theorem honE_hatChiSq_row_sum_snd (S : HonSetup v h fc fu HM μ) {Cchi Csum : ℝ}
    (hCchi : 0 ≤ Cchi)
    (hchi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox Work.BoseK15.decayOrder Cchi)
    (hsuminv : ∀ S' : Finset (Fin 3 → ℤ),
      (∑ n ∈ S', (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹) ≤ Csum)
    (s : Lab (HM μ).N) (Ss : Finset (Lab (HM μ).N)) :
    ∑ s' ∈ Ss, |(honE v h fc fu HM μ).hatChiSq (s - s')| ≤ Cchi * Csum :=
  honE_hatChiSq_row_le S hCchi hchi hsuminv (fun x => s - x) sub_right_injective Ss

/-! ## 2. The Schur form bound -/

theorem honE_hatChiSq_form_upper {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ : ℝ}
    (S : Work.BoseGateFS.HonSetup v h fc fu HM μ) {Cchi Csum K₀ : ℝ} (hCchi : 0 ≤ Cchi)
    (hchi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox Work.BoseK15.decayOrder Cchi)
    (hsuminv : ∀ S' : Finset (Fin 3 → ℤ),
      (∑ n ∈ S', (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹) ≤ Csum)
    (hK : Cchi * Csum ≤ K₀) :
    ∀ (Ss : Finset (Work.BoseBoxFock.Lab (HM μ).N)) (c : Work.BoseBoxFock.Lab (HM μ).N → ℝ)
      (w : Work.BoseBoxFock.Lab (HM μ).N → (Work.BoseGateFS.honF v h fc fu HM μ).H),
      (∑ s ∈ Ss, ∑ s' ∈ Ss, c s * c s'
          * (Work.BoseGateFS.honE v h fc fu HM μ).hatChiSq (s' - s)
          * (Work.BoseGateFS.honF v h fc fu HM μ).bp (w s') (w s))
        ≤ K₀ * ∑ s ∈ Ss, c s ^ 2 * (Work.BoseGateFS.honF v h fc fu HM μ).bp (w s) (w s) := by
  intro Ss c w
  -- the row constant, dominated by the chapter constant
  have hD : Cchi * Csum ≤ K₀ := hK
  -- the pointwise Cauchy–Schwarz + AM–GM bound
  have hpt : ∀ s s' : Lab (HM μ).N,
      c s * c s' * (honE v h fc fu HM μ).hatChiSq (s' - s)
        * (honF v h fc fu HM μ).bp (w s') (w s)
      ≤ |(honE v h fc fu HM μ).hatChiSq (s' - s)| *
          (c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s)
            + c s' ^ 2 * (honF v h fc fu HM μ).bp (w s') (w s')) / 2 := fun s s' =>
    le_trans (le_abs_self _)
      (Work.BoseK15.bp_mul_abs_le (honF v h fc fu HM μ) c w s s' _)
  -- the weighted double sum, via the two halves of the pointwise bound
  have hsum : (∑ s ∈ Ss, ∑ s' ∈ Ss, |(honE v h fc fu HM μ).hatChiSq (s' - s)| *
        (c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s)
          + c s' ^ 2 * (honF v h fc fu HM μ).bp (w s') (w s')) / 2)
      ≤ (Cchi * Csum) * ∑ s ∈ Ss, c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s) := by
    have hsplit : (∑ s ∈ Ss, ∑ s' ∈ Ss, |(honE v h fc fu HM μ).hatChiSq (s' - s)| *
          (c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s)
            + c s' ^ 2 * (honF v h fc fu HM μ).bp (w s') (w s')) / 2)
        = (∑ s ∈ Ss, ∑ s' ∈ Ss, |(honE v h fc fu HM μ).hatChiSq (s' - s)| *
              (c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s) / 2))
          + (∑ s ∈ Ss, ∑ s' ∈ Ss, |(honE v h fc fu HM μ).hatChiSq (s' - s)| *
              (c s' ^ 2 * (honF v h fc fu HM μ).bp (w s') (w s') / 2)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring
    rw [hsplit]
    have h1 : (∑ s ∈ Ss, ∑ s' ∈ Ss, |(honE v h fc fu HM μ).hatChiSq (s' - s)| *
          (c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s) / 2))
        ≤ (Cchi * Csum) * (∑ s ∈ Ss, c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s) / 2) :=
      Work.BoseK15.double_sum_row_bound Ss
        (fun s s' => |(honE v h fc fu HM μ).hatChiSq (s' - s)|)
        (fun s => c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s) / 2) (Cchi * Csum)
        (fun s _ => honE_hatChiSq_row_sum_fst S hCchi hchi hsuminv s Ss)
        (fun s _ => div_nonneg
          (mul_nonneg (sq_nonneg (c s)) ((honF v h fc fu HM μ).bp_nonneg (w s))) (by norm_num))
    have h2 : (∑ s ∈ Ss, ∑ s' ∈ Ss, |(honE v h fc fu HM μ).hatChiSq (s' - s)| *
          (c s' ^ 2 * (honF v h fc fu HM μ).bp (w s') (w s') / 2))
        ≤ (Cchi * Csum) * (∑ s ∈ Ss, c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s) / 2) := by
      rw [Finset.sum_comm]
      exact Work.BoseK15.double_sum_row_bound Ss
        (fun s' s => |(honE v h fc fu HM μ).hatChiSq (s' - s)|)
        (fun s' => c s' ^ 2 * (honF v h fc fu HM μ).bp (w s') (w s') / 2) (Cchi * Csum)
        (fun s' _ => honE_hatChiSq_row_sum_snd S hCchi hchi hsuminv s' Ss)
        (fun s' _ => div_nonneg
          (mul_nonneg (sq_nonneg (c s')) ((honF v h fc fu HM μ).bp_nonneg (w s'))) (by norm_num))
    have h3 : (Cchi * Csum) * (∑ s ∈ Ss, c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s) / 2)
        + (Cchi * Csum) * (∑ s ∈ Ss, c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s) / 2)
        = (Cchi * Csum) * ∑ s ∈ Ss, c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s) := by
      rw [← Finset.sum_div]
      ring
    linarith [h1, h2, h3]
  calc (∑ s ∈ Ss, ∑ s' ∈ Ss, c s * c s' * (honE v h fc fu HM μ).hatChiSq (s' - s)
        * (honF v h fc fu HM μ).bp (w s') (w s))
      ≤ (∑ s ∈ Ss, ∑ s' ∈ Ss, |(honE v h fc fu HM μ).hatChiSq (s' - s)| *
          (c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s)
            + c s' ^ 2 * (honF v h fc fu HM μ).bp (w s') (w s')) / 2) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun s' _ => hpt s s'
    _ ≤ (Cchi * Csum) * ∑ s ∈ Ss, c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s) := hsum
    _ ≤ K₀ * ∑ s ∈ Ss, c s ^ 2 * (honF v h fc fu HM μ).bp (w s) (w s) :=
        mul_le_mul_of_nonneg_right hD
          (Finset.sum_nonneg fun s _ =>
            mul_nonneg (sq_nonneg (c s)) ((honF v h fc fu HM μ).bp_nonneg (w s)))

end Work.BoseGateFS
