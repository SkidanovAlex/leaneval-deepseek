import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.Card
import Submission.Work.BrauerSuzuki.Q8.LamEta
import Submission.Work.BrauerSuzuki.Q8.Eta
import Submission.Work.BrauerSuzuki.Q8.Eta2
import Submission.Work.BrauerSuzuki.Q8.step6_inner_eta
import Submission.Work.CharCore.Basic
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.frobenius_reciprocity_transposed
import Submission.Work.Induction.indFun_trans

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The inner product `(χ, η)` for an arbitrary class function `χ` (Glauberman, step (6))

Glauberman (1974) step (6) computes the inner product `(χ, η)_G` of the generalized character
`η = Ind_{N*}^{G} ζ` with a class function `χ` on `G`, in terms of the average of `χ` over the
coset `x · H*` of `C* = C_G(⟨x⟩)`:

`(χ, η)_G = |H*|⁻¹ ∑_{u ∈ H*} χ (x * u)`.

This is the version needed downstream, where `χ` is only known to be a class function (not
necessarily irreducible).  The computation rewrites `η = Ind_{C*}^{G} (1 - λ)` (transitivity of
induction), applies Frobenius reciprocity in its transposed form, evaluates `1 - λ` on the four
`X`-cosets of `C* = X · H*`, and uses that conjugation by an element of `N*` inverting `x`
identifies the `H*`-cosets of `x` and `x⁻¹`.  The ingredients are the lemmas of
`Submission.Work.BrauerSuzuki.Q8.step6_inner_eta` (`Ctx.sum_Cstar_shift`, which needs only
`IsClassFun χ`).
-/

set_option maxHeartbeats 1000000

open Classical
open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

open Classical in
theorem step6_inner_eta_classfun {G : Type*} [Group G] [Fintype G] {x : G} {S : Sylow 2 G}
    (h : Work.BrauerSuzuki.Q8.Ctx G x S) {χ : G → ℂ} (hχ : Work.CharCore.IsClassFun χ) :
    Work.CharCore.cfInner χ h.eta =
      (Nat.card ↥(Work.BrauerSuzuki.Q8.Hstar x) : ℂ)⁻¹ *
        ∑ u : ↥(Work.BrauerSuzuki.Q8.Hstar x), χ (x * (u : G)) := by
  -- `η = Ind_{C*}^{G} (1 - λ)`: `ζ = Ind_{C*}^{N*} (1 - λ)` and induction is transitive.
  have heta : h.eta =
      Work.Induction.indFun (Cstar x) (fun c : ↥(Cstar x) => 1 - lamFun x c) := by
    have hz : h.zeta = Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x))
        (fun k => (fun c : ↥(Cstar x) => 1 - lamFun x c)
          (Subgroup.subgroupOfEquivOfLe h.Cstar_le_Nstar k)) := by
      rw [show h.zeta = Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) h.phiKc from rfl]
      congr 1
    rw [show h.eta = Work.Induction.indFun (Nstar x) h.zeta from rfl, hz]
    exact Work.Induction.indFun_trans h.Cstar_le_Nstar (fun c : ↥(Cstar x) => 1 - lamFun x c)
  -- Frobenius reciprocity (transposed form), valid for an arbitrary class function `χ`.
  rw [heta, Work.Induction.frobenius_reciprocity_transposed (Cstar x) χ
        (fun c : ↥(Cstar x) => 1 - lamFun x c) hχ]
  rw [Work.CharCore.cfInner_apply]
  -- `1 - λ` is real valued, so the complex conjugation in `cfInner` is harmless.
  have hconj : ∀ c : ↥(Cstar x), starRingEnd ℂ (1 - lamFun x c) = 1 - lamFun x c := by
    intro c
    by_cases hc : (c : G) ∈ (T x : Set G) * (Hstar x : Set G)
    · rw [(h.lamFun_eq_one_iff c).mpr hc]; simp
    · rw [(h.lamFun_eq_neg_one_iff c).mpr hc]; simp
  have hsum : (∑ c : ↥(Cstar x),
        Work.Induction.resFun (Cstar x) χ c * starRingEnd ℂ (1 - lamFun x c))
      = ∑ c : ↥(Cstar x), (1 - lamFun x c) * χ (c : G) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hconj c]
    simp only [Work.Induction.resFun_apply]
    ring
  -- The core computation of step (6).
  rw [hsum, h.sum_Cstar_shift hχ]
  rw [show (Fintype.card ↥(Cstar x) : ℂ) = 4 * (Nat.card ↥(Hstar x) : ℂ) from by
    have hcardNat : Fintype.card ↥(Cstar x) = 4 * Nat.card ↥(Hstar x) := by
      rw [← Nat.card_eq_fintype_card (α := ↥(Cstar x)), h.card_Cstar]
    rw [hcardNat]; push_cast; ring]
  have hne : (Nat.card ↥(Hstar x) : ℂ) ≠ 0 := by
    have hpos : 0 < Nat.card ↥(Hstar x) := Nat.card_pos
    exact_mod_cast hpos.ne'
  field_simp

end Work.BrauerSuzuki.Q8
