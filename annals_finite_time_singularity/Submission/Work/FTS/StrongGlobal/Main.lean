/-
# `Work.FTS.StrongGlobal.Global` — **S5**: the global strong solution `global_strong`

This is the final module of the `StrongGlobal` area: the theorem

  `global_strong`

which produces, from the four hypotheses of the design (`FTS_STRONG_ROUTE.md` §3)

* **S1** `hLWP : LWPStrong α Φs EllSol α₀ K δ` (uniform local existence),
* **S2** `hPersist : PersistStrong α Φs EllSol (C0 …) K` (persistence of the `ℋ⁶`-bound),
* **S3** `hSob : SobolevC4 α` (interior Sobolev embedding `ℋ⁶ ⊂ C⁴`),
* **S6** `hDbd : DbDStrong α Φs EllSol (C0 …) Cd` (uniform `ℋ³`-bound on `∂_τg`),

together with the two inputs of the energy bootstrap S4 (`hEnergy : EnergyId`, `hPair :
PairBndStrong`) and the small datum `g₀` (`RegQ α 6`, `Xn₄(g₀) ≤ α²`, `Xn₆(g₀) ≤ Kα²`), a **global
strong solution** of the dynamic modulated equation with the canonical stream function
`PsiCan Φs EllSol g`:

* `IsDynGSolWith (IsBslSolPos α) α (PsiCan Φs EllSol g) g` — the elliptic law `IsBslSolPos` at
  every `τ ≥ 0` and the equation in the half-line form `IsDynEqOn`;
* `g (·,·,0) = g₀`;
* the regularity package `RegPkgMin α g` (the interface consumed by `Work.FTS.RegPkgGal`);
* the uniform a-priori bound `Xn α (slice g τ) ≤ C0 … * α²` for all `τ ≥ 0`.

The solution is `Gglob (Gfam …) δ`, the floor-rule family of the stepping of
`Work.FTS.StrongGlobal.Global`; the argument is the instantiation of
`Work.FTS.StrongGlobal.global_of_agree` (the regularity transfer) with the agreement
`Gglob_eq_piece_near` and the pieces `Gfam_spec`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongGlobal.Transfer
import Submission.Work.FTS.Regularity.Defs

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
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot IsDynEqOn IsDynGSolWith)

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn}

/-- At negative fake time the global family is its first piece. -/
theorem Gglob_eq_zero_piece {δ : ℝ} (hδ : 0 < δ) {G : ℕ → Fam} (z θ τ' : ℝ) (h : τ' < 0) :
    Gglob G δ z θ τ' = G 0 z θ τ' := by
  simp only [Gglob, pIdx]
  rw [Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg h.le hδ.le)]

/-- **S5 — global existence of a strong solution of the dynamic modulated equation.**

From the local existence **S1**, the persistence **S2**, the Sobolev embedding **S3** and the
`ℋ³`-bound **S6** (plus the energy identity and N4's pairing estimate of the a-priori bound S4),
a datum `g₀` with `RegQ α 6 g₀`, `Xn₄(g₀) ≤ α²` and `Xn₆(g₀) ≤ Kα²` extends to a *global* strong
solution with the regularity package `RegPkgMin` and the uniform bound `C₀α²`. -/
theorem global_strong {IP : ℝ → Fn → Fn → ℝ}
    {α₂ cc clo Cup Ccs CcN α₄ α₀ K δ Cd : ℝ}
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCcN : 0 < CcN) (hα₄ : 0 < α₄)
    (hα : 0 < α) (hα5 : α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄) (hαα₀ : α ≤ α₀)
    (hLWP : LWPStrong α Φs EllSol α₀ K δ)
    (hPersist : PersistStrong α Φs EllSol (C0 CcN cc clo Cup Ccs) K)
    (hSob : SobolevC4 α) (hDbd : DbDStrong α Φs EllSol (C0 CcN cc clo Cup Ccs) Cd)
    (hEnergy : EnergyId IP α Φs EllSol) (hPair : PairBndStrong IP α CcN Φs EllSol)
    {g₀ : Fn} (hData : RegQ α 6 g₀) (hXn4₀ : Xn α g₀ ≤ α ^ 2)
    (hXn6₀ : Xn6 α g₀ ≤ K * α ^ 2) :
    ∃ g : Fam, IsDynGSolWith (IsBslSolPos α) α (PsiCan Φs EllSol g) g ∧
      (∀ z θ, g z θ 0 = g₀ z θ) ∧ RegPkgMin α g ∧
      (∀ τ, 0 ≤ τ → Xn α (slice g τ) ≤ C0 CcN cc clo Cup Ccs * α ^ 2) := by
  have hδ : 0 < δ := hLWP.1
  refine ⟨Gglob (Gfam (Φs := Φs) (EllSol := EllSol) hIP hCcN hα₄ hα hα5 hαα₀ hLWP hPersist
      hEnergy hPair hData hXn4₀ hXn6₀) δ, ?_⟩
  refine global_of_agree (IP := IP) hδ (fun n => Gfam_spec (Φs := Φs) (EllSol := EllSol) hIP hCcN hα₄ hα
      hα5 hαα₀ hLWP hPersist hEnergy hPair hData hXn4₀ hXn6₀ n) ?_ ?_ hSob hDbd
  · intro n τ hτ hn z θ τ' hτ'
    exact Gglob_eq_piece_near (Φs := Φs) (EllSol := EllSol) hIP hCcN hα₄ hα hα5 hαα₀ hLWP
      hPersist hEnergy hPair hData hXn4₀ hXn6₀ hτ hn z θ τ' hτ'
  · intro z θ τ' hτ'
    exact Gglob_eq_zero_piece hδ z θ τ' hτ'

/-! ## The form consumed by the physical bridge ()

The physical bridge ( §4, and ) works
at the *profile* exponent .  Since every statement of this area is parametric in the
exponent, the bridge form is the following immediate instantiation. -/

/-- **S5 at the profile exponent **, in the exact shape consumed by
. -/
theorem global_strong_pExp {IP : ℝ → Fn → Fn → ℝ}
    {α₂ cc clo Cup Ccs CcN α₄ α₀ K δ Cd : ℝ} {α : ℝ} (hα : 0 < α)
    (hIP : UnifIP IP α₂ cc clo Cup Ccs) (hCcN : 0 < CcN) (hα₄ : 0 < α₄)
    (hα5 : Work.FTS.Regularity.pExp α ≤ alpha5 CcN cc clo Cup Ccs α₂ α₄)
    (hαα₀ : Work.FTS.Regularity.pExp α ≤ α₀)
    (hLWP : LWPStrong (Work.FTS.Regularity.pExp α) Φs EllSol α₀ K δ)
    (hPersist : PersistStrong (Work.FTS.Regularity.pExp α) Φs EllSol
      (C0 CcN cc clo Cup Ccs) K)
    (hSob : SobolevC4 (Work.FTS.Regularity.pExp α))
    (hDbd : DbDStrong (Work.FTS.Regularity.pExp α) Φs EllSol (C0 CcN cc clo Cup Ccs) Cd)
    (hEnergy : EnergyId IP (Work.FTS.Regularity.pExp α) Φs EllSol)
    (hPair : PairBndStrong IP (Work.FTS.Regularity.pExp α) CcN Φs EllSol)
    {g₀ : Fn} (hData : RegQ (Work.FTS.Regularity.pExp α) 6 g₀)
    (hXn4₀ : Xn (Work.FTS.Regularity.pExp α) g₀ ≤ (Work.FTS.Regularity.pExp α) ^ 2)
    (hXn6₀ : Xn6 (Work.FTS.Regularity.pExp α) g₀ ≤ K * (Work.FTS.Regularity.pExp α) ^ 2) :
    ∃ g : Fam,
      IsDynGSolWith (IsBslSolPos (Work.FTS.Regularity.pExp α)) (Work.FTS.Regularity.pExp α)
        (PsiCan Φs EllSol g) g ∧
      (∀ z θ, g z θ 0 = g₀ z θ) ∧ RegPkgMin (Work.FTS.Regularity.pExp α) g ∧
      (∀ τ, 0 ≤ τ →
        Xn (Work.FTS.Regularity.pExp α) (slice g τ) ≤ C0 CcN cc clo Cup Ccs
          * (Work.FTS.Regularity.pExp α) ^ 2) :=
  global_strong hIP hCcN hα₄ (Work.FTS.Regularity.pExp_pos hα) hα5 hαα₀ hLWP hPersist hSob
    hDbd hEnergy hPair hData hXn4₀ hXn6₀

end Work.FTS.StrongGlobal
