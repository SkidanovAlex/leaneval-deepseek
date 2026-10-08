import Submission.Work.CORE2B.Basic

/-!
# AREA CORE2B — assembly: the four contract `Prop`s from their leaves

Each theorem here is *pure logic*: it turns the leaf `Prop`s of `Basic.lean` (Bender's proof
steps, delegated one by one) into the contract statement copied verbatim from
`_design_gw/Contracts2.lean` §3:

```
lemma27_of_leaves : L27_commutator_le → L27_su_not_le → L27_solvable → Lemma27Prop
lemma28_of_leaves : L28_S0U_ne_bot → L28_t_mem_layer → Lemma28Prop
lemma29_of_leaves : L29_two_core_or_layer → Lemma29Prop
thm210_of_contra : Thm210_contra → Thm210Prop
```

If a leaf is proved (`L29_contra → L29_two_core_or_layer` is also done here), the corresponding
`lemma` gets shorter; when all leaves of a lemma are available, the only remaining input is the
`LocalToolkit` and the earlier areas' `Prop`s, exactly as in the design's DAG
(`lemma27 (T) (h23) (h26)`, `lemma28 (T) (h22) (h27)`, `lemma29 (T)`, `thm210 (T) (h26) (h27)
(h28)`).
-/

open scoped MatrixGroups

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false

/-! ## Lemma 2.9: the contradiction form gives the disjunction (classical logic) -/

theorem l29_two_core_or_layer_of_contra (T : Work.GW2.LocalToolkit) (h : L29_contra) :
    L29_two_core_or_layer := by
  intro _ G _ _ hFT hCtx B V N hD
  by_contra hcon
  exact h T G hFT hCtx B V N hD
    (by by_contra h1; exact hcon (Or.inl h1))
    (by by_contra h2; exact hcon (Or.inr h2))

/-! ## Assembly of the four deliverables -/

/-- Bender Lemma 2.7 from its three assertions. -/
theorem lemma27_of_leaves (T : Work.GW2.LocalToolkit) (h23 : Work.GW2.Lemma23Prop)
    (h26 : Work.GW2.Thm26Prop) (hA : L27_commutator_le) (hB : L27_su_not_le)
    (hC : L27_solvable) : Work.GW2.Lemma27Prop := by
  intro G _ _ hFT hCtx B M hM hrel hnotle htM htE hnc hsize
  have hD : L27Hyp B M := ⟨hM, hrel, hnotle, htM, htE, hnc, hsize⟩
  exact ⟨hA T h23 h26 G hFT hCtx B M hD, hB T h23 h26 G hFT hCtx B M hD,
    hC T h23 h26 G hFT hCtx B M hD⟩

/-- Bender Lemma 2.7, **corrected input list**: with `Lemma22Prop` available.  Bender's proof of
conclusion (b) `[S,U] ⊄ F(U)` uses "`U` is not trivial" (Lemma 2.2); with `U = ⊥` the conclusion is
literally false, and `Lemma22Prop` is in scope at every call site of `lemma27` in the DAG
(`Contracts2.lean` §6 computes `h22` before `h27`), so passing it costs nothing. -/
theorem lemma27_of_leaves_h22 (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop)
    (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop) (hA : L27_commutator_le)
    (hB : L27_su_not_le_h22) (hC : L27_solvable) : Work.GW2.Lemma27Prop := by
  intro G _ _ hFT hCtx B M hM hrel hnotle htM htE hnc hsize
  have hD : L27Hyp B M := ⟨hM, hrel, hnotle, htM, htE, hnc, hsize⟩
  exact ⟨hA T h23 h26 G hFT hCtx B M hD, hB T h22 h23 h26 G hFT hCtx B M hD,
    hC T h23 h26 G hFT hCtx B M hD⟩

/-- Bender Lemma 2.8, **corrected input list**: with `Thm26Prop` available.  Bender's proof of
`[S₀,U] ≠ 1` uses the Theorem 2.6 dichotomy `S ⊓ C(U) = O₂(Ĥ)`, so the design's input list
`(T, h22, h27)` for `lemma28` is one input short — and `h26` is already computed before `h28` in
the DAG. -/
theorem lemma28_of_leaves_h26 (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop)
    (h26 : Work.GW2.Thm26Prop) (h27 : Work.GW2.Lemma27Prop) (hA : L28_S0U_ne_bot_h26)
    (hB : L28_t_mem_layer) : Work.GW2.Lemma28Prop := by
  intro G _ _ hFT hCtx B hinv
  have hD : L28Hyp B := ⟨hinv⟩
  refine ⟨hA T h22 h26 h27 G hFT hCtx B hD, ?_⟩
  intro M hM hrel hnotle hSM
  exact hB T h22 h27 G hFT hCtx B hD M ⟨hM, hrel, hnotle, hSM⟩

/-- Bender Lemma 2.8 from its two assertions. -/
theorem lemma28_of_leaves (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop)
    (h27 : Work.GW2.Lemma27Prop) (hA : L28_S0U_ne_bot) (hB : L28_t_mem_layer) :
    Work.GW2.Lemma28Prop := by
  intro G _ _ hFT hCtx B hinv
  have hD : L28Hyp B := ⟨hinv⟩
  refine ⟨hA T h22 h27 G hFT hCtx B hD, ?_⟩
  intro M hM hrel hnotle hSM
  exact hB T h22 h27 G hFT hCtx B hD M ⟨hM, hrel, hnotle, hSM⟩

/-- Bender Lemma 2.9 from the disjunction. -/
theorem lemma29_of_leaves (T : Work.GW2.LocalToolkit) (h : L29_two_core_or_layer) :
    Work.GW2.Lemma29Prop := by
  intro G _ _ hFT hCtx B V N hVN hN hVS htV hfour hhyp
  exact h T G hFT hCtx B V N ⟨hVN, hN, hVS, htV, hfour, hhyp⟩

/-- Bender Theorem 2.10 from the contradiction form. -/
theorem thm210_of_contra (T : Work.GW2.LocalToolkit) (h26 : Work.GW2.Thm26Prop)
    (h27 : Work.GW2.Lemma27Prop) (h28 : Work.GW2.Lemma28Prop) (h : Thm210_contra) :
    Work.GW2.Thm210Prop := by
  intro G _ _ hFT hCtx B
  by_contra hcon
  exact h T h26 h27 h28 G hFT hCtx B (fun h1 => hcon (Or.inl h1))
    (fun h2 => hcon (Or.inr h2))

/-! ## The strengthened Lemma 2.7 (`IsCoatom M`, `M ⇝ Ĥ`) -/

/-- **Bender Lemma 2.7 in the form its proof consumes** (`Lemma27PropS`), from the three
strengthened leaves.  See `NOTES_CORE2B.md` §4: step (4) of Bender's proof of Lemma 2.7
("`O₂(M) = 1`, otherwise `N_G(O₂(M)) ≤ Ĥ`") needs `M` to be maximal. -/
theorem lemma27S_of_leaves (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop)
    (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop) (hA : L27_commutator_leS)
    (hB : L27_su_not_le_h22S) (hC : L27_solvableS) : Lemma27PropS := by
  intro G _ _ hFT hCtx B M hD
  exact ⟨hA T h23 h26 G hFT hCtx B M hD, hB T h22 h23 h26 G hFT hCtx B M hD,
    hC T h23 h26 G hFT hCtx B M hD⟩

/-- The strengthened statement implies the contract `Lemma27Prop` *at maximal `M`*: this is the
form in which CORE4 and Theorem 2.10 use it. -/
theorem lemma27_at_coatom (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop)
    (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop) (h : Lemma27PropS)
    (G : Type) [Group G] [Finite G] (hFT : Work.GW2.FeitThompsonProp)
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (M : Subgroup G)
    (hM : IsCoatom M) (hrel : Work.GW2.BRel B.Hhat M) (hrelrev : Work.GW2.BRel M B.Hhat)
    (hnotle : ¬ M ≤ B.Hhat) (htM : B.t ∈ M) (htE : B.t ∉ Work.GW2.layerIn M)
    (hnc : ∀ P : Sylow 2 M, ¬ IsCyclic P)
    (hsize : 8 ≤ Nat.card ((B.S : Subgroup G) ⊓ M : Subgroup G) ∨
      Nat.card (B.S : Subgroup G) = 4 ∨ B.t ∈ Work.GW2.twoResidualIn M) :
    ⁅M, zpowers B.t⁆ ≤ Work.GW2.fittingPiIn B.piᶜ M ∧
      ¬ ⁅(B.S : Subgroup G), B.U⁆ ≤ Work.GW2.fittingIn B.U ∧ Group.IsSolvable ↥M :=
  h G hFT hCtx B M ⟨⟨hM.ne_top, hrel, hnotle, htM, htE, hnc, hsize⟩, hM, hrelrev⟩

/-! ## Amended signatures of `Core6.lean` §1 (the lead's `lemma27'`, `lemma28'`) -/

/-- `Core6.lean` §1 `lemma27'`, from the leaves: `lemma27` with `h22` (for `U ≠ 1`). -/
theorem lemma27' (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop)
    (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop) (hA : L27_commutator_le)
    (hB : L27_su_not_le_h22) (hC : L27_solvable) : Work.GW2.Lemma27Prop :=
  lemma27_of_leaves_h22 T h22 h23 h26 hA hB hC

/-- `Core6.lean` §1 `lemma28'`, from the leaves: `lemma28` with `h26` (for Theorem 2.6's
dichotomy in `[S₀,U] ≠ 1`). -/
theorem lemma28' (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop)
    (h26 : Work.GW2.Thm26Prop) (h27 : Work.GW2.Lemma27Prop) (hA : L28_S0U_ne_bot_h26)
    (hB : L28_t_mem_layer) : Work.GW2.Lemma28Prop :=
  lemma28_of_leaves_h26 T h22 h26 h27 hA hB

/-! ## Composition: what is still owed

The four deliverables are available as soon as the leaves below are proved.
-/

/-- The list of leaves still owed for `Lemma27Prop`.  (Conclusion (b) is taken in the corrected
form `L27_su_not_le_h22`: Bender's proof uses `U ≠ 1` from Lemma 2.2.  The corresponding assembly
is `lemma27_of_leaves_h22`.) -/
def Lemma27Owed : Prop := L27_commutator_le ∧ L27_su_not_le_h22 ∧ L27_solvable

/-- The list of leaves still owed for `Lemma28Prop`.  (The first assertion is taken in the corrected
form `L28_S0U_ne_bot_h26`: Bender's proof uses the Theorem 2.6 dichotomy.  The corresponding
assembly is `lemma28_of_leaves_h26`.) -/
def Lemma28Owed : Prop := L28_S0U_ne_bot_h26 ∧ L28_t_mem_layer

/-- The list of leaves still owed for `Lemma29Prop`. -/
def Lemma29Owed : Prop := L29_two_core_or_layer

/-- The list of leaves still owed for `Thm210Prop`. -/
def Thm210Owed : Prop := Thm210_contra

end Work.CORE2B
