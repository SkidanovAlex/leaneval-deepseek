import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.BSHallW.OddChain.XDvdOmega
import Submission.Work.BSHallW.Defs
import Submission.Work.ThmF.Prove.step9N6
import Submission.Work.ThmF.ChV3.step9

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.step9v13` — §3 step (9), corrected form

The lead's pass-13 design (`Submission/Work/NOTES_LEAD_bs_pass13.md` §2–§3,
`ThmF/_design13/ThmF13Step9.lean`): step (9) reduces to the single divisibility

* **(X)** `Nat.card P ∣ Nat.card (G ⧸ H)` (`Prove/xDvdOmega`, proved from `N1`–`N4` and
  `HallWielandtOddProp` twice), which gives `p = orderOf (s*t)` via the proved
  `ChV3.card_eq_orderOf_iff_dvd_omega`, hence `Nat.card P ∣ |C_Q(P)| + 1`; and
* **(N6)** `¬ Nat.card P ∣ |Σ|` (`Prove/step9N6`), the arithmetic exclusion of `|Σ| = p`.

Source: Peterfalvi II Ch. V §3, step (9), p. 250.  With `ChV3.step9_repaired` this yields
`p = f ≠ ℓ` (`p = orderOf (s*t)` and `p ≠ |Σ|`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.BSHallW.OddChain

open Work.ThmF Work.ThmF.Prove

/-- **§3 step (9), corrected statement** (replaces the rejected `Prove/step9Divisibility`; it drops
`hCP`, `h7`, `h15` and adds `h3`, `hH`, `hV`, `hPW`, `hVW`, `hTh`). -/
theorem step9v13 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G} {m : ℕ}
    (hC4 : ChIIFourProp) (hTh : ThompsonFrobeniusProp) (hHW : Work.BSHallW.HallWielandtOddProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h3 : Step3Out Q P) (h8 : Step8Out H Q t P)
    (hm : 1 ≤ m) (hcq : Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 = orderOf (s * t) ^ m)
    (hF : (orderOf (s * t)).Prime)
    (hQ1 : Work.ThmF.oddPart Q ≠ ⊥)
    (hG : Nat.card G = (Nat.card Q + 1) * Nat.card ↥H)
    (hH : Nat.card ↥H = Nat.card Q * Nat.card ↥(twoPoint H t))
    (hD : Nat.card ↥(twoPoint H t) = (2 ^ Nat.card P - 1) * Nat.card ↥(Work.ThmF.W H t) * Nat.card P)
    (hV : Nat.card ↥(centD H t) = Nat.card ↥(Work.ThmF.W H t) * Nat.card P)
    (hPW : P ⊓ Work.ThmF.W H t = ⊥)
    (hfpfW : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 →
      Work.ThmF.oddPart Q ⊓ Subgroup.centralizer ({w} : Set G) = ⊥)
    (hVW : ∀ a ∈ centD H t, ∀ b ∈ centD H t, a * b * a⁻¹ * b⁻¹ ∈ Work.ThmF.W H t)
    (hL2b : ∀ X : Subgroup G, X ≤ centD H t → X ≠ ⊥ →
      Subgroup.normalizer (X : Set G) =
        Subgroup.centralizer (X : Set G) ⊔ (centD H t ⊓ Subgroup.normalizer (X : Set G))) :
    Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.CQ Q P) + 1 ∧
      ¬ Nat.card P ∣ Nat.card ↥(Work.ThmF.ChV3.Sig H t P) := by
  have hX : Nat.card P ∣ Nat.card (G ⧸ H) :=
    xDvdOmega hC4 hTh hHW c h3 h8 hQ1 hG hH hD hV hPW hfpfW hVW hL2b
  have hpf : Nat.card P = orderOf (s * t) :=
    (Work.ThmF.ChV3.card_eq_orderOf_iff_dvd_omega hC4 c ⟨hF, m, hm, hcq⟩).mpr hX
  refine ⟨?_, Work.ThmF.Prove.step9N6 (s := s) (r := r) c.P_prime h3 h8 hm hpf hcq⟩
  rw [hcq, ← hpf]
  exact dvd_pow_self _ (by omega)

end Work.BSHallW.OddChain
