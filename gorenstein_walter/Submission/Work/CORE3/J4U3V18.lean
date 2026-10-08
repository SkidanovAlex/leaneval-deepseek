import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.J4.J4DTriv
import Submission.Work.CORE3.Case1bCount
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.J4U3V18Aux.KCentralizesFittingU
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.SevenNoInvolCentralizer
import Submission.Work.CORE3.J4U3V18Aux.LcFailsOfCardU

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- **Conjugate form of `KCentralizesFittingU`.**  If `X ≤ K^g` then the conjugate `F(U)^g` of the
Fitting subgroup of `U = O(Ĥ)` centralizes `X`.

Indeed `K ≤ C_G(F(U))` (`Work.CORE3.J4U3V18Aux.KCentralizesFittingU`, which is Bender's step
"`I_U(s)` centralizes `F(U)`, hence lies in `F(U)`" from the proof of Theorem 2.10, p. 222), and
conjugating gives `K^g ≤ C_G(F(U)^g)`; every element of `X ⊆ K^g` then commutes with every element
of `F(U)^g`.  This is the correct form of Bender's displayed claim "`F(U) ⊆ C_Ĥ(X)`" in the proof
of (7) on p. 224: the *conjugate* `F(U)^g`, not `F(U)` itself, is what the argument produces. -/
theorem conjSub_fittingIn_le_centralizer {G : Type} [Group G] [Finite G]
    (I : Case1Inputs) (h : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B)
    (g : G) (X : Subgroup G) (hK : X ≤ conjSub g D.K) :
    conjSub g (fittingIn B.U) ≤ Subgroup.centralizer (X : Set G) := by
  have hKZ : D.K ≤ Subgroup.centralizer (fittingIn B.U : Set G) :=
    J4U3V18Aux.KCentralizesFittingU I h B h1 D
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : g⁻¹ * x * g ∈ D.K := CORE2A.mem_conjSub_iff.mp (hK hx)
  have hw' : g⁻¹ * w * g ∈ fittingIn B.U := CORE2A.mem_conjSub_iff.mp hw
  have hcomm : (g⁻¹ * x * g) * (g⁻¹ * w * g) = (g⁻¹ * w * g) * (g⁻¹ * x * g) :=
    (Subgroup.mem_centralizer_iff.mp (hKZ hx') (g⁻¹ * w * g) hw').symm
  calc x * w = g * ((g⁻¹ * x * g) * (g⁻¹ * w * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * w * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hcomm]
    _ = w * x := by group

/-- Bender 1981 §3, p. 224, step (7), first half: if `y ∉ Ĥ` is an involution and `X ≠ 1` is an
odd subgroup of `Ĥ` inverted by `y` whose centralizer *and* normalizer in `G` have even order,
then `|U| = 3`.

**Reference for the statement**: the printed proof of (7) is defective as printed; the repaired
route is *design pass 23* of this workspace
(`Submission/Work/NOTES_LEAD_gw_design23.md` §A, `/home/ubuntu/.../Submission/Work/CORE3/D23/`),
with these steps:

* the page image reads `C_{F(U)}(V^g) = 1` (the earlier OCR misread it as `C_{Ĥ^g}(V^g)`), and
  everything in the printed paragraph *after* "`F(U) ⊆ C_G(X)`" is correct;
* `F(U) ⊆ C_G(X)` is supplied by Bender's own parenthetical on p. 223 ("`[Ĥ,s]` centralizes
  `F(U)`") together with the existence of an involution `s ∈ Ĥ` inverting `X`: all involutions of
  `Ĥ ∖ V` act identically on `F(U)` (`D23.InvolActionUniform`), and for `x ∈ X` the element
  `x⁻¹ s x` is such an involution with `s·(x⁻¹ s x) = x²`, so `x²` — and hence `x` (odd order) —
  centralizes `F(U)`;
* then `F(U) ≤ C_G(X) ≤ Ĥ^g`, and `C_{F(U)}(V^g) ≤ Ĥ ∩ Ĥ^g` is normalised by `V^g`, so local
  control forces `C_{F(U)}(V^g) = 1` (`D23.FittingFaithfulFour`), whence `|F(U)| ∣ 3`; as `K ≤ F(U)`
  and `K ≠ 1`, `|F(U)| = 3`, and `U/C_U(F(U)) ↪ Aut(C₃)` gives `|U| = 3`
  (`D23.CardUOfFittingThree`).

This file records the *contradiction form* of the same step, which is what the assembly uses:
`Work.CORE3.J4U3V18Aux.LcFailsOfCardU` (proved, axiom-clean) says that `|U| ≠ 3` yields a
non-trivial `Y ≤ F(U) = fittingIn B.U` with `N_G(Y) ≰ Ĥ`, and that is exactly what the second
conjunct of `Case1 B` (local control) forbids.  Note that the `hNeven` hypothesis of the statement
below is *automatic* (`y` normalises `X`) and plays no role; the proof uses only
`h1 : Case1 B`.  -/
theorem J4U3V18 (G : Type) [Group G] [Finite G] (I : Case1Inputs) (h : BenderCtx G)
    (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) {y : G} (hy2 : orderOf y = 2)
    (hyH : y ∉ B.Hhat) (X : Subgroup G) (hXle : X ≤ B.Hhat) (hXne : X ≠ ⊥)
    (hXodd : Odd (Nat.card X)) (hinv : Inverts y X)
    (hCeven : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hNeven : Even (Nat.card (Subgroup.normalizer (X : Set G)))) :
    Nat.card B.U = 3 := by
  -- Bender's repair of (7) (design pass 23 in this workspace) gives the contradiction form of
  -- the step: `|U| ≠ 3` produces a non-trivial `Y ≤ F(U)` with `N_G(Y) ≰ Ĥ`, which is exactly
  -- what Case (1)'s local-control conjunct `h1.2` forbids.
  by_contra hU
  obtain ⟨Y, hYne, hYle, hYnotle⟩ := J4U3V18Aux.LcFailsOfCardU I h B D hU
  exact hYnotle (h1.2 Y hYne hYle)

end Work.CORE3
