import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.InvSetThreeSubgroup
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.OrderThreeLeCentralizer
import Submission.Work.CORE3.J4.J4CosetStep
import Submission.Work.CORE3.J4.J4SevenNeThreeNC

/-!
# `Odd |C_G(x)|` in the `J₃`-case, cycle-free

This is `Work.CORE3.JthreeCentralizerOdd` with two changes made so that the module can be
imported from `Submission.Work.CORE3.Case1bThree` without an import cycle:

* the numerical input `|U| = 3` (which `Work.CORE3.cardU_eq_three_of_case1b` supplies from the
  count data) is taken as a hypothesis `hU3`;
* Bender's step (7) is taken from `Submission.Work.CORE3.J4.J4SevenNeThreeNC`, the verbatim copy
  of `Submission.Work.CORE3.J4.J4SevenNeThree` with its unused (and cyclic)
  `CentHhatOrderThree` import removed.

MATHEMATICS.  Bender 1981 §3, step (7): if an involution `y ∉ Ĥ` inverts a non-trivial odd-order
subgroup `X ≤ Ĥ` whose centralizer *and* normalizer in `G` are both of even order, then the coset
`yĤ` carries exactly four involutions.  Here `X = ⟨x⟩` with `x ∈ Ĥ` of order `3`: `C_G(X)` even
is the hypothesis, and `N_G(X)` is even because `y ∈ N_G(⟨x⟩)` is an involution.  So the
`J₃`-hypothesis `cosetInvCount Ĥ y = 3` forces `C_G(x)` to have odd order.
-/

namespace Work.CORE3

open Subgroup
open Work.GW2

theorem JthreeCentralizerOddNC (I : Case1Inputs) (hSetup : Case1bSetupProp)
    (hCount : Case1bCountProp) (hFive : Case1bFiveProp) (h89 : Case1bEightNineProp)
    {G : Type} [Group G] [Finite G] (hBc : BenderCtx G) (B : BenderSetup G)
    (h1 : Case1 B) (h4 : IsFourGroup (pCoreIn 2 B.Hhat)) (D : Case1bData B) {x y : G}
    (hU3 : Nat.card B.U = 3)
    (hxH : x ∈ B.Hhat) (hx3 : orderOf x = 3)
    (hxVU : x ∉ (pCoreIn 2 B.Hhat ⊔ B.U))
    (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat) (hinv : y * x * y⁻¹ = x⁻¹)
    (hcnt : cosetInvCount B.Hhat y = 3) :
    Odd (Nat.card (Subgroup.centralizer ({x} : Set G))) := by
  classical
  -- ### `x ≠ 1`, `y ≠ 1`
  have hx1 : x ≠ 1 := by
    intro h0
    rw [h0, orderOf_one] at hx3
    exact absurd hx3 (by norm_num)
  have hy1 : y ≠ 1 := by
    intro h0
    rw [h0, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  have hy : y * y = 1 := by rw [← pow_two, ← hy2]; exact pow_orderOf_eq_one y
  -- ### reduce to the contradiction `Even |C_G(x)|`
  rw [← Nat.not_even_iff_odd]
  intro heven
  -- ### the two centralizers of `x` agree
  have hcen : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
      = Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure x, Subgroup.centralizer_closure]
  have heven' :
      Even (Nat.card (Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G))) := by
    rw [hcen]; exact heven
  -- ### `y` inverts `X = ⟨x⟩`, hence `N_G(X)` is even
  have hinvY : Work.GW2.Inverts y (Subgroup.zpowers x) :=
    Work.CORE3.J4.inverts_zpowers_of hinv
  have hNe :
      Even (Nat.card (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G))) :=
    Work.CORE3.J4.even_card_normalizer_of_inverts hy hy1 hinvY
  -- ### Bender's (7) for `X = ⟨x⟩`
  exact (Work.CORE3.J4.J4SevenNeThree G I hBc B h1 D hU3 y hy2 hyH (Subgroup.zpowers x)
    (Subgroup.zpowers_ne_bot.mpr hx1)
    (by rw [Nat.card_zpowers, hx3]; norm_num)
    (Subgroup.zpowers_le.mpr hxH)
    hinvY
    heven' hNe) hcnt
end Work.CORE3
