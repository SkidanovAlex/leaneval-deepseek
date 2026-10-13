/-
# `Work.FTS.StrongGlobal.Global` — the global family of S5

This module assembles the global strong solution of S5 from the stepping of
`Work.FTS.StrongGlobal.Step`:

* `basePiece` — the first accumulated piece, on `[0, δ]` (from the local existence S1, the
  a-priori bound S4 and the persistence S2);
* `Seq` — the dependent recursion `n ↦ (piece, its data)`, whose `(n+1)`-st term is `stepFam`;
* `Gfam n = (Seq n).val` with `Gfam_spec n : PieceData … n (Gfam n)`;
* the *nesting* `slice (Gfam m) τ = slice (Gfam n) τ` for `n ≤ m` and `τ ≤ stepEnd δ n`;
* the global family
  `Gglob Gfam δ z θ τ = Gfam (pIdx δ τ) z θ τ` with `pIdx δ τ = ⌊τ/δ⌋`, i.e. the piece whose
  interval `[pIdx δ τ · δ, (pIdx δ τ + 1) δ]` covers `τ`.

The key structural fact is `Gglob_eq_piece_near`: on a *neighbourhood* of every `τ ≥ 0` the global
family agrees with the single piece `Gfam (pIdx δ τ)` — this is what transfers every regularity
field of the pieces to the global family (and, in particular, gives the joint `C¹` across the
junctions without any further gluing: the piece covering `τ` is `C¹` on a slab with one unit of
slack, and `Gglob` agrees with it there because the pieces are nested).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.StrongGlobal.Step

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongGlobal

open Work.FTS.Nonlin
open Work.FTS.Apriori
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS)

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn}

/-! ## The first piece -/

/-- **The first accumulated piece**: the local existence S1 applied at `τ₀ = 0` to the datum `g₀`,
with the a-priori `ℋ⁴`-bound (S4) and the persisted `ℋ⁶`-bound (S2) on `[0, δ]`. -/
theorem base_piece {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs CcN α₄ α₀ K δ : ℝ} {g₀ : Fn}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCcN : 0 < CcN) (hα₄ : 0 < α₄)
    (hα : 0 < α) (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) (hαα₀ : α ≤ α₀)
    (hLWP : LWPStrong α Φs EllSol α₀ K δ)
    (hPersist : PersistStrong α Φs EllSol (C0 CcN cc clo Cup Ccs) K)
    (hEnergy : EnergyId IP α Φs EllSol) (hPair : PairBndStrong IP α CcN Φs EllSol)
    (hData : RegQ α 6 g₀) (hXn4₀ : Xn α g₀ ≤ α ^ 2) (hXn6₀ : Xn6 α g₀ ≤ K * α ^ 2) :
    ∃ g : Fam, PieceData α Φs EllSol g₀ δ (C0 CcN cc clo Cup Ccs) K 0 g := by
  obtain ⟨g, hdat, hsol⟩ := hLWP.2.2.2 α hα hαα₀ 0 (le_refl 0) g₀ hData hXn6₀
  have hT : 0 ≤ stepEnd δ 0 := stepEnd_nonneg hLWP.1 0
  have hs : StrongSolOn α Φs EllSol 0 (stepEnd δ 0) g := by
    rw [stepEnd_zero]
    simpa using hsol
  have hsl : slice g 0 = g₀ := by
    funext z θ
    exact hdat z θ
  have hbnd4 : ∀ τ ∈ Set.Icc 0 (stepEnd δ 0),
      Xn α (slice g τ) ≤ C0 CcN cc clo Cup Ccs * α ^ 2 := by
    intro τ hτ
    have hX0 : Xn α (slice g 0) ≤ α ^ 2 := by rw [hsl]; exact hXn4₀
    exact apriori_strong IP hIP hCcN hα₄ hα hα5 hT hs
      (hEnergy g (stepEnd δ 0) hT hs) (hPair g (stepEnd δ 0) hT hs) hX0 τ hτ
  have hbnd6 : ∀ τ ∈ Set.Icc 0 (stepEnd δ 0), Xn6 α (slice g τ) ≤ K * α ^ 2 := by
    intro τ hτ
    refine hPersist.2 g (stepEnd δ 0) hT hs hbnd4 ?_ τ hτ
    rw [hsl]; exact hXn6₀
  exact ⟨g, hdat, hs, hbnd4, hbnd6⟩

/-! ## The recursion -/

/-- The base term of the recursion, as an element of the sigma type. -/
noncomputable def baseVal {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs CcN α₄ α₀ K δ : ℝ} {g₀ : Fn}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCcN : 0 < CcN) (hα₄ : 0 < α₄)
    (hα : 0 < α) (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) (hαα₀ : α ≤ α₀)
    (hLWP : LWPStrong α Φs EllSol α₀ K δ)
    (hPersist : PersistStrong α Φs EllSol (C0 CcN cc clo Cup Ccs) K)
    (hEnergy : EnergyId IP α Φs EllSol) (hPair : PairBndStrong IP α CcN Φs EllSol)
    (hData : RegQ α 6 g₀) (hXn4₀ : Xn α g₀ ≤ α ^ 2) (hXn6₀ : Xn6 α g₀ ≤ K * α ^ 2) :
    {g : Fam // PieceData α Φs EllSol g₀ δ (C0 CcN cc clo Cup Ccs) K 0 g} :=
  ⟨Classical.choose (base_piece hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData
      hXn4₀ hXn6₀),
    Classical.choose_spec (base_piece hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair
      hData hXn4₀ hXn6₀)⟩

/-- **The continuation sequence**: the `n`-th accumulated piece, together with its data. -/
noncomputable def Seq {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs CcN α₄ α₀ K δ : ℝ} {g₀ : Fn}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCcN : 0 < CcN) (hα₄ : 0 < α₄)
    (hα : 0 < α) (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) (hαα₀ : α ≤ α₀)
    (hLWP : LWPStrong α Φs EllSol α₀ K δ)
    (hPersist : PersistStrong α Φs EllSol (C0 CcN cc clo Cup Ccs) K)
    (hEnergy : EnergyId IP α Φs EllSol) (hPair : PairBndStrong IP α CcN Φs EllSol)
    (hData : RegQ α 6 g₀) (hXn4₀ : Xn α g₀ ≤ α ^ 2) (hXn6₀ : Xn6 α g₀ ≤ K * α ^ 2) :
(n : ℕ) → {g : Fam // PieceData α Φs EllSol g₀ δ (C0 CcN cc clo Cup Ccs) K n g} :=
  Nat.rec (baseVal hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀)
    (fun n ih => ⟨stepFam (Φs := Φs) (EllSol := EllSol) (C₀ := C0 CcN cc clo Cup Ccs)
        hLWP hα hαα₀ n ih.val ih.property,
      stepFam_spec (Φs := Φs) (EllSol := EllSol) (C₀ := C0 CcN cc clo Cup Ccs)
        hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hXn4₀ hXn6₀ n
        ih.val ih.property⟩)

/-- The `n`-th accumulated piece of the continuation. -/
noncomputable def Gfam {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs CcN α₄ α₀ K δ : ℝ} {g₀ : Fn}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCcN : 0 < CcN) (hα₄ : 0 < α₄)
    (hα : 0 < α) (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) (hαα₀ : α ≤ α₀)
    (hLWP : LWPStrong α Φs EllSol α₀ K δ)
    (hPersist : PersistStrong α Φs EllSol (C0 CcN cc clo Cup Ccs) K)
    (hEnergy : EnergyId IP α Φs EllSol) (hPair : PairBndStrong IP α CcN Φs EllSol)
    (hData : RegQ α 6 g₀) (hXn4₀ : Xn α g₀ ≤ α ^ 2) (hXn6₀ : Xn6 α g₀ ≤ K * α ^ 2)
    (n : ℕ) : Fam :=
  (Seq hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ n).val

theorem Gfam_spec {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs CcN α₄ α₀ K δ : ℝ} {g₀ : Fn}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCcN : 0 < CcN) (hα₄ : 0 < α₄)
    (hα : 0 < α) (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) (hαα₀ : α ≤ α₀)
    (hLWP : LWPStrong α Φs EllSol α₀ K δ)
    (hPersist : PersistStrong α Φs EllSol (C0 CcN cc clo Cup Ccs) K)
    (hEnergy : EnergyId IP α Φs EllSol) (hPair : PairBndStrong IP α CcN Φs EllSol)
    (hData : RegQ α 6 g₀) (hXn4₀ : Xn α g₀ ≤ α ^ 2) (hXn6₀ : Xn6 α g₀ ≤ K * α ^ 2)
    (n : ℕ) :
    PieceData α Φs EllSol g₀ δ (C0 CcN cc clo Cup Ccs) K n
      (Gfam hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ n) :=
  (Seq hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ n).property


/-! ## The floor rule -/

/-- The index of the piece covering the fake time `τ`: `⌊τ/δ⌋`. -/
def pIdx (δ τ : ℝ) : ℕ := Nat.floor (τ / δ)

theorem pIdx_eq_iff {δ τ : ℝ} (hδ : 0 < δ) (hτ : 0 ≤ τ) {n : ℕ} :
    pIdx δ τ = n ↔ (n : ℝ) * δ ≤ τ ∧ τ < ((n : ℝ) + 1) * δ := by
  have h0 : 0 ≤ τ / δ := div_nonneg hτ hδ.le
  rw [pIdx, Nat.floor_eq_iff h0, le_div_iff₀ hδ, div_lt_iff₀ hδ]

/-- The piece covering `τ` starts at or before `τ`. -/
theorem mul_pIdx_le {δ τ : ℝ} (hδ : 0 < δ) (hτ : 0 ≤ τ) : ((pIdx δ τ : ℕ) : ℝ) * δ ≤ τ :=
  ((pIdx_eq_iff hδ hτ).mp rfl).1

/-- The piece covering `τ` ends after `τ`. -/
theorem lt_pIdx_succ {δ τ : ℝ} (hδ : 0 < δ) : τ < (((pIdx δ τ : ℕ) : ℝ) + 1) * δ :=
  (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (τ / δ))

/-- An integer below `τ/δ` is at most the covering index. -/
theorem le_pIdx_of_mul_lt {δ τ : ℝ} (hδ : 0 < δ) {k : ℕ} (h : (k : ℝ) * δ < τ) :
    k ≤ pIdx δ τ := by
  rw [pIdx]
  refine Nat.le_floor ?_
  rw [le_div_iff₀ hδ]
  exact h.le

/-! ## The global family -/

/-- **The global family**: at each fake time `τ` it is the piece whose interval covers `τ`. -/
noncomputable def Gglob (G : ℕ → Fam) (δ : ℝ) : Fam := fun z θ τ => G (pIdx δ τ) z θ τ

@[simp] theorem slice_Gglob (G : ℕ → Fam) (δ τ : ℝ) :
    slice (Gglob G δ) τ = slice (G (pIdx δ τ)) τ := rfl

section Agreement

variable {IP : ℝ → Fn → Fn → ℝ} {α₂ cc clo Cup Ccs CcN α₄ α₀ K δ : ℝ} {g₀ : Fn}
variable (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCcN : 0 < CcN) (hα₄ : 0 < α₄)
variable (hα : 0 < α) (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) (hαα₀ : α ≤ α₀)
variable (hLWP : LWPStrong α Φs EllSol α₀ K δ)
variable (hPersist : PersistStrong α Φs EllSol (C0 CcN cc clo Cup Ccs) K)
variable (hEnergy : EnergyId IP α Φs EllSol) (hPair : PairBndStrong IP α CcN Φs EllSol)
variable (hData : RegQ α 6 g₀) (hXn4₀ : Xn α g₀ ≤ α ^ 2) (hXn6₀ : Xn6 α g₀ ≤ K * α ^ 2)

/-- The `(n+1)`-st piece is the concatenation of the `n`-th one with the new local piece. -/
theorem Gfam_succ_eq (n : ℕ) :
    Gfam hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ (n + 1)
      = stepFam (Φs := Φs) (EllSol := EllSol) (C₀ := C0 CcN cc clo Cup Ccs)
          hLWP hα hαα₀ n
          (Gfam hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ n)
          (Gfam_spec hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ n) :=
  rfl

/-- **The nesting**: the `(n+1)`-st piece agrees with the `n`-th one on `[0, stepEnd δ n]`. -/
theorem slice_Gfam_succ {n : ℕ} {τ : ℝ} (hτ : τ ≤ stepEnd δ n) :
    slice (Gfam hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ (n + 1)) τ
      = slice (Gfam hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ n) τ := by
  rw [Gfam_succ_eq hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ n,
    stepFam]
  exact slice_concat_of_le hτ

/-- **The nesting, transitively**: the `m`-th piece agrees with the `n`-th one on
`[0, stepEnd δ n]` for `n ≤ m`. -/
theorem slice_Gfam_agree {n m : ℕ} (h : n ≤ m) {τ : ℝ} (hτ : τ ≤ stepEnd δ n) :
    slice (Gfam hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ m) τ
      = slice (Gfam hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ n) τ := by
  induction m with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero h
      subst hn
      rfl
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · have hnm : n ≤ m := Nat.lt_succ_iff.mp hlt
        rw [slice_Gfam_succ hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀
          hXn6₀ (le_trans hτ (stepEnd_mono hLWP.1.le hnm)), ih hnm]
      · have hnm : n = m + 1 := le_antisymm h hge
        subst hnm
        rfl

/-- **The global family agrees with a single piece near every fake time.**  For `τ ≥ 0`, on the
interval `((n)δ - δ, nδ + δ)` (where `n = pIdx δ τ` is the index of the piece covering `τ`) the
global family is the piece `Gfam n`. -/
theorem Gglob_eq_piece_near {n : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (hn : pIdx δ τ = n)
    (z θ τ' : ℝ) (hτ' : τ' ∈ Set.Ioo ((n : ℝ) * δ - δ) ((n : ℝ) * δ + δ)) :
    Gglob (Gfam hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀) δ
        z θ τ'
      = Gfam hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ n z θ τ' := by
  rw [Gglob]
  by_cases hneg : τ' < 0
  · have hn0 : n = 0 := by
      by_contra hne
      have h1 : (1 : ℕ) ≤ n := Nat.one_le_iff_ne_zero.mpr hne
      have h1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
      have : 0 ≤ (n : ℝ) * δ - δ := by nlinarith [hLWP.1]
      linarith [hτ'.1]
    subst hn0
    have hidx : pIdx δ τ' = 0 := by
      rw [pIdx, Nat.floor_eq_zero]
      have : τ' / δ < 0 := div_neg_of_neg_of_pos hneg hLWP.1
      linarith
    rw [hidx]
  · have hτ'nn : 0 ≤ τ' := le_of_not_gt hneg
    have hle : pIdx δ τ' ≤ n := by
      have h1 : τ' < ((n : ℝ) + 1) * δ := by
        have h := hτ'.2; linarith [h]
      by_contra hcon
      have h2 : n + 1 ≤ pIdx δ τ' := Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)
      have h3 := mul_pIdx_le hLWP.1 hτ'nn
      have h4 : ((n : ℝ) + 1) * δ ≤ τ' := by
        have : ((n : ℝ) + 1) ≤ ((pIdx δ τ' : ℕ) : ℝ) := by exact_mod_cast h2
        calc ((n : ℝ) + 1) * δ ≤ ((pIdx δ τ' : ℕ) : ℝ) * δ := by
              exact mul_le_mul_of_nonneg_right this hLWP.1.le
          _ ≤ τ' := h3
      linarith [h1, h4]
    have hge : n - 1 ≤ pIdx δ τ' := by
      by_contra hcon
      have h2 : pIdx δ τ' + 1 ≤ n - 1 := Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)
      have h3 : (((pIdx δ τ' : ℕ) : ℝ) + 1) * δ ≤ ((n - 1 : ℕ) : ℝ) * δ := by
        have hcast : ((pIdx δ τ' : ℕ) : ℝ) + 1 ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h2
        exact mul_le_mul_of_nonneg_right hcast hLWP.1.le
      have h4 : ((n - 1 : ℕ) : ℝ) * δ ≤ τ' := by
        rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        · subst hn0
          simpa using hτ'nn
        · have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ n)]
            norm_num
          rw [hcast]
          linarith [hτ'.1]
      have h5 := lt_pIdx_succ (δ := δ) (τ := τ') hLWP.1
      linarith [h3, h4, h5]
    have h2 : τ' ≤ stepEnd δ (pIdx δ τ') := by
      rw [stepEnd]
      exact le_of_lt (lt_pIdx_succ hLWP.1)
    have hagree := slice_Gfam_agree hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist hEnergy hPair hData
      hXn4₀ hXn6₀ hle h2
    exact congrFun (congrFun hagree.symm z) θ

end Agreement

end Work.FTS.StrongGlobal
