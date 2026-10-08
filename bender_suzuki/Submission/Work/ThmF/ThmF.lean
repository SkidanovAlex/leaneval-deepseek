import Submission.Work.ThmF.ChV3.Chain

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThmF`: Théorème F (Peterfalvi II, Ch. V, p. 247)

**Main theorem** (`Work.ThmF.ThmF`):

```lean
theorem ThmF (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (hTh : ThompsonFrobeniusProp)
    (hW : WielandtFixedPoint) (hHW : HallWielandtProp) (hA : ArithmeticNineTwoSeven)
    (hNF : ChV3.NearFieldAppXIProp) (hR : ChV3.ChV3Prop) : ThmFProp
```

i.e. in a **simple** finite group `G` in situation (B0)–(B2) with split rank-one data
`H = Q ⋊ D`, `t ∉ H`, `D = H ∩ Hᵗ`, no subgroup `P ≤ V = C_D(t) = centD H t` of prime order has
`C_G(P)` of 2-rank `1`: `C_G(P)` contains a four-group.

The proof is the reduction of §3.  Given `P ≤ V` of prime order, suppose `¬ HasFourGroup C_G(P)`
(hypothesis (F1)).  Ch. V §2 Lemma 1 (b) (`Work.ThmF.ChV12.structureIdentity`) produces the
distinguished involution `s ∈ Q` and `ρ ∈ Q` with `t s t = ρ t ρ⁻¹`; with `r := ρ⁻¹` this is the
structure identity `t s t = r⁻¹ t r` of the standing context, so the hypotheses assemble into
`Work.ThmF.ChV3.CtxF H Q t s ρ⁻¹ P`, which steps (1)–(17) — the input `hR : ChV3Prop` — rule out.

**Status of the inputs.**  `hFT`, `hC4`, `hTh` are other areas' `Prop`s (`FeitThompsonProp`,
`ChIIFourProp` of `ThreePoints`, `ThompsonFrobeniusProp`).  `hW`, `hHW`, `hA`, `hNF` are the
literature inputs of Ch. V §3 recorded in `Tools/External.lean` and `ChV3/NearField.lean`
(Wielandt's fixed-point formula, Hall–Wielandt, HB IX (2-7), App. XI's near-field shadow).
`hR : ChV3.ChV3Prop` is the open part of this area: the numbered steps (1)–(17).  See
`ChV3/Chain.lean` and `NOTES.md`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF

open Work.ThmF.ChV3

/-- **Théorème F** (Peterfalvi II Ch. V p. 247).  See the module docstring. -/
theorem ThmF (hFT : FeitThompsonProp) (hC4 : ChIIFourProp) (hTh : ThompsonFrobeniusProp)
    (hW : Work.ThmF.WielandtFixedPoint) (hHW : Work.ThmF.HallWielandtProp)
    (hA : Work.ThmF.ArithmeticNineTwoSeven) (hNF : ChV3.NearFieldAppXIProp)
    (hR : ChV3.ChV3Prop) : ThmFProp := by
  intro G _ _ hS hsimple H Q t hsplit P hPV hPprime
  by_contra hno
  -- the structure identity of §2 Lemma 1 (b): `s ∈ Q` an involution, `ρ ∈ Q`, `t s t = ρ t ρ⁻¹`
  have hdata : IsSplitRankOneData G H Q t := IsSplitRankOne.toData hsplit
  obtain ⟨⟨s, ρ⟩, ⟨hsQ, hs2, hρQ, hsr⟩, -⟩ := Work.ThmF.ChV12.structureIdentity hdata
  -- `t` is an involution
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [IsSplitRankOne.invol hsplit] at h
    simpa [pow_two] using h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- `t s t = ρ t ρ⁻¹`, i.e. with `r = ρ⁻¹` the identity `t s t = r⁻¹ t r`
  have hsid : t * s * t = ρ * t * ρ⁻¹ := by
    rw [show t * s * t = t * s * t⁻¹ by rw [htinv]]
    exact hsr
  exact hR hFT hC4 hTh hW hHW hA hNF
    { sit := hS, simple := hsimple, split := hsplit, s_mem := hsQ, s_inv := hs2,
      r_mem := Q.inv_mem hρQ, sid := by rw [inv_inv]; exact hsid,
      P_le := hPV, P_prime := hPprime, F1 := hno }

end Work.ThmF
