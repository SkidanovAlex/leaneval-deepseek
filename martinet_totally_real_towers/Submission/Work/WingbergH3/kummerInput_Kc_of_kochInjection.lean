import Mathlib
import Submission.Work.WingbergH3.Constructive
import Submission.Work.WingbergH3.contH2DimLe_iff_kummerCarrierInput
import Submission.Work.ShafarevichKoch.KcKochInjection
import Submission.Work.ShafarevichKoch.H2Half.natCard_H2Z_quot_two_le_pow_five_Kc
import Submission.Work.ClassFieldTower.unitTwoRank_witness_eq_one

/-!
# `Work.WingbergH3.kummerInput_Kc_of_kochInjection`

**Koch's injection for `Kc = ℚ(√-30030)` produces the Kummer input `KummerInput Kc`.**

`Work.WingbergH3.KummerDatum Kc` asks for a maximal unramified pro-`2` extension `M` of `Kc`, a
number `d` with `#H¹(G_∅,𝔽₂) = 2 ^ d`, and a finite `𝔽₂`-vector space `V` of cardinal at most
`2 ^ (d + d₂(O_Kc^×))` whose `𝔽₂`-dual receives `H²(G_∅,𝔽₂)` injectively.

Here `d = 5` is forced by the arithmetic: `#H¹(G_∅,𝔽₂) = #(G_∅/Φ(G_∅)) = 2 ^ rank₂ Cl(Kc) = 2 ^ 5`
(`Work.ShafarevichKoch.H2Half.natCard_H1_zmodTwo_galoisGroup_Kc`, proved in the workspace without
class field theory), and `d₂(O_Kc^×) = unitTwoRank Kc = 1`
(`Work.ClassFieldTower.unitTwoRank_witness_eq_one`), so the exponent is `5 + 1 = 6`, exactly the
`𝔽₂`-dimension `dim V_∅/Kc^{×2} = d₂(O_Kc^×) + rank₂ Cl(Kc) = 1 + 5` of Koch's Kummer radical.

The arithmetic content is entirely in `Work.ShafarevichKoch.KochInjection M`, the classical
Shafarevich--Koch injection `Sha_∅ = H²(G_∅,𝔽₂) ↪ (V_∅/Kc^{×2})^∨` (Koch, *Galois theory of
`p`-extensions*, Ch. 11 Thm. 11.3; Salle, *Invent. Math.* **44** (1978), Théorème 4.1).  From it,
`Work.ShafarevichKoch.contH2DimLe_six_of_kochInjection` gives
`dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6 = d + d₂(O_Kc^×)`, and the purely group-theoretic adapter
`Work.WingbergH3.contH2DimLe_iff_kummerCarrierInput` turns that relation count into the Kummer
carrier of `KummerDatum`.

This is the bridge that makes Koch's injection (the pinned arithmetic input of the
Shafarevich--Koch chapter) available to the `WingbergH3` route, whose consumer is
`Work.WingbergH3.shafarevichBound_of_kummerInput`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical
open NumberField

noncomputable section

namespace Work.WingbergH3

open Work.ConCohomology Work.RelatorRank Work.ShafarevichKoch Work.ClassFieldTower

/-- **The generator rank of `G_∅` for `Kc` in the exponent form needed by `KummerDatum`.** -/
theorem natCard_H1_galoisGroup_Kc_eq_two_pow_five
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2) :
    Nat.card (H1 (galoisGroup M) (ZMod 2)) = 2 ^ 5 :=
  Work.ShafarevichKoch.H2Half.natCard_H1_zmodTwo_galoisGroup_Kc M

/-- **Koch's injection for `Kc` gives the Kummer input.** -/
theorem kummerInput_Kc_of_kochInjection
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)
    (h : Work.ShafarevichKoch.KochInjection M) :
    Work.WingbergH3.KummerInput Work.WingbergH3.Kc := by
  -- Koch's injection bounds the relation rank: `dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ 6`.
  have hsix : Work.RelatorRank.ContH2DimLe (galoisGroup M) 6 :=
    Work.ShafarevichKoch.contH2DimLe_six_of_kochInjection M h
  -- ... and `d + d₂(O_Kc^×) = 5 + 1 = 6` is exactly that exponent.
  have hd : 5 + unitTwoRank Kc = 6 := by
    rw [Work.ClassFieldTower.unitTwoRank_witness_eq_one]
  refine ⟨⟨M, 5, ?_, ?_⟩⟩
  · exact Work.ShafarevichKoch.H2Half.natCard_H1_zmodTwo_galoisGroup_Kc M
  · rw [hd]
    exact (Work.WingbergH3.contH2DimLe_iff_kummerCarrierInput.mp hsix).some

end Work.WingbergH3
