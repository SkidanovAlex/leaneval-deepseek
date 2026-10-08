/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — design pass 19: `Case2SixImpl9` is correctly stated (Bender §4 (6))

Copied verbatim from `Submission/Work/_design_gw/Core19.lean` (namespace `Work.GW2.C19`).
The one clause the `Case2Six9` prover could not supply — `¬ N_G(X) ≤ Ĥ` for `1 ≠ X ≤ F` — is
derivable (`E ≤ C_G(F) ≤ N_G(X)` and `E ≰ Ĥ` from `I.thm26`), so no restatement is needed and
`Case2PrePlus` is not even used.

Leaves: S1 `SixENotLeHhatProp`, S2 `SixTInLayerNProp`, S3 `SixELeLayerNProp`,
`QOddCentProp` (model fact), S4 (`QOddCentProp → SixLayerNLeMProp`), S5 `SixStarOfLayerProp`,
TI `SixTIOfStarProp`, CY `SixCycOfTIProp`.  The assemblies `star_of_leaves`, `six9_of_leaves` and
`six_of_leaves` are **proved** below.

The supporting helper `layer_facts_proper` (the `K ≠ ⊤` form of `layer_facts_coatom`) is in
`Submission/Work/CORE4/LayerFactsProper.lean`.
-/
import Mathlib
import Submission.Work.CORE4.Defs

open scoped MatrixGroups

namespace Work.GW2.C19

open Subgroup

/-- **S1.** `E(M) ≰ Ĥ`.
Route: suppose `E ≤ Ĥ`.  `I.thm26` gives `O(Ĥ) = U` and either (a) `Ĥ = H = C_G(t)`, or
(b) `V := O₂(Ĥ)` is a four-group and `|Ĥ : VU| = 6`.
(a) `E ≤ C_G(t)` and `t ∈ E`, so `t ∈ Z(E)`; but `|Z(E)|` is odd (`I.toolkit.lay` via the proved
    `Work.CORE4.layer_facts_coatom`) and `t` has order 2.
(b) `VU ⊴ Ĥ`; `E` is perfect and a perfect subgroup of a group of order 6 is trivial, so
    `E ≤ VU`; `VU/U` is abelian, so `E = [E,E] ≤ [VU,VU] ≤ U`, which has odd order — but
    `t ∈ E` has order 2. -/
def SixENotLeHhatProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ (B : BenderSetup G) (D : Case2Data B),
    Case2Pre B D → ¬ layerIn D.M ≤ B.Hhat

/-- **S2.** `t ∈ E(N_G(X))` for `1 ≠ X ≤ F`.
Route: by contradiction apply `I.lem27` (with `I.toolkit.ft`) to `M₀ := N_G(X)`:
* `M₀ ≠ ⊤` (`X ⊴ G` would force `X = G`, but `X ≤ F ≤ M < G`);
* `BRel Ĥ M₀` with witness `X`: `X ≤ F(U) ≤ F(Ĥ)` (as in `CORE2B/fittingIn_U_normalizer.lean`)
  and `N_G(X) ⊓ F*(Ĥ) ≤ M₀`;
* `¬ M₀ ≤ Ĥ`: `E ≤ C_G(X) ≤ M₀` (`F ≤ C_G(E)` from `Case2Pre`) and S1;
* `t ∈ M₀` (`t ∈ E`); Sylow 2-subgroups of `M₀` are not cyclic (a Sylow 2-subgroup of `E` is not
  cyclic, `Work.CORE4.NineQuasisimpleSylowNotCyclic`, and lies in a conjugate of every Sylow of
  `M₀`);  third disjunct: `t ∈ E = O²(E) ≤ O²(M₀)` (`E` perfect, `E/O²(E)` a 2-group).
Then `IsSolvable M₀`, contradicting `E ≤ M₀` with `E` quasisimple. -/
def SixTInLayerNProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ (B : BenderSetup G) (D : Case2Data B),
    Case2Pre B D → ¬ layerIn D.M ≤ B.Hhat →
      ∀ X : Subgroup G, X ≠ ⊥ → X ≤ D.F → B.t ∈ layerIn (normalizer (X : Set G))

/-- **S3.** `E ≤ E₀ := E(N_G(X))`.
Route: `E ≤ C_G(X) ≤ N_G(X) ≤ N_G(E₀)` (`Work.CORE4.layerIn_le_normalizer`), so `E ∩ E₀ ⊴ E`;
it contains `t`, and `t ∉ Z(E)` (`|Z(E)|` odd).  A normal subgroup `N` of a quasisimple `E` with
`N ≰ Z(E)` is `E` (`NZ(E) = E` by simplicity of `E/Z(E)`, then `E = [E,E] = [N,N] ≤ N`). -/
def SixELeLayerNProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ (B : BenderSetup G) (D : Case2Data B),
    Case2Pre B D → ∀ X : Subgroup G, X ≠ ⊥ → X ≤ D.F →
      B.t ∈ layerIn (normalizer (X : Set G)) → layerIn D.M ≤ layerIn (normalizer (X : Set G))

/-- **QOddCent** (model leaf, no §4 data).  `Q/Z(Q) ≅ A₇` or `L₂(q)`, `|Z(Q)|` odd; `R ≤ Q`
quasisimple with `R/Z(R) ≅ A₇` or `L₂(q')`; `V ≤ R` a four-group; `x ∈ C_Q(R)` with `x^m` central
for some odd `m`.  Then `x ∈ Z(Q)`.
Route (bars = images in `Q/Z(Q)`; `x̄` has odd order; `V̄ ≅ V` as `|Z(Q)|` is odd):
* `L₂(q)`: `x̄ ∈ C(V̄) = V̄` (`I.toolkit.l2four`), a 2-group, so `x̄ = 1`.
* `A₇`: `x̄ ∈ C(v̄)` for an involution `v̄ ∈ V̄`, of order 24 (`Work.AUTA7.A7.CentralizerInvolution`),
  so `x̄ = 1` or `|x̄| = 3`.  If `|x̄| = 3` then `R̄ ≤ C(x̄)`, of order 36 or 9
  (`Work.AUTA7.A7.CentralizerOrderThree`), so `|R/Z(R)|` (a quotient of `R̄`, as `R ∩ Z(Q) ≤ Z(R)`)
  divides 36.  `|A₇| = 2520 ∤ 36`; for `L₂(q')` `I.toolkit.l2ti` gives subgroups of orders `q'`
  and `(q'+1)/2`, both dividing 36, forcing `q' = 9` and `5 ∣ 36` — impossible.
GAP: `_design_gw/gw19_qc.g` (A₇, 3·A₇, 3·A₆, `L₂(q)` for `q ≤ 31`: `C_Q(R) ≤ Z(Q)` for every perfect
`R ≰ Z(Q)`; the four-group shortcut fails for A₇ shapes, so `R` is needed there). -/
def QOddCentProp (I : C4Inputs) : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q],
    (Nonempty (Q ⧸ center Q ≃* alternatingGroup (Fin 7)) ∨
      ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty (Q ⧸ center Q ≃* PSL(2, GaloisField p k))) →
    Odd (Nat.card (center Q)) →
    ∀ R : Subgroup Q, IsQuasisimple R →
      (Nonempty (↥R ⧸ center ↥R ≃* alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty (↥R ⧸ center ↥R ≃* PSL(2, GaloisField p k))) →
    ∀ V : Subgroup Q, V ≤ R → IsFourGroup V →
    ∀ x : Q, x ∈ centralizer (R : Set Q) → (∃ m : ℕ, Odd m ∧ x ^ m ∈ center Q) →
      x ∈ center Q

/-- **S4.** `E₀ := E(N_G(X)) ≤ M`, given S3.
Route (Bender: "`N_F(X)` induces inner automorphisms on `E(N_G(X))` by 1.10.ii, …
`E(N_G(X)) ≤ C_G(N_F(X)) ≤ C_G(Z(F)) ≤ M`").  Put `Y := Z(F) = F ⊓ C_G(F)`; `Y ≠ 1` (`F ≠ 1`
nilpotent, `F ≤ F(U)`), `Y ⊴ M` (`N_G(F) = M`), so `N_G(Y) = M` (coatom + simplicity) and
`C_G(Y) ≤ M`.  It suffices: every `x ∈ Y` centralizes `E₀`.
* `x ∈ F_{2'}(C_{N_G(X)}(t))`: `x ∈ F(U) ⊓ N_G(X)`, which is normal nilpotent in
  `H ⊓ N_G(X)`; odd order; `Work.CORE4.mem_fittingPiIn_of_odd_mem_fittingIn` (plumbing as in
  `Case2Setup9Fprops.lean` l. 240–290, with `↥N_G(X)` for `↥M`).
* `I.toolkit.d110ii` on the D-group `↥N_G(X)` (`hbc.ih`, `DihOrCycSub`): `e ∈ E₀` with
  `x y x⁻¹ = e y e⁻¹` on `E₀`.  By S3 and `x ∈ F ≤ C_G(E)`, `e ∈ C_G(E)`; `e^{|x|} ∈ Z(E₀)`, `|x|` odd.
* `QOddCent` at `Q := ↥E₀`, `R := E`, `V` a four-group of `E`: `E₀` is quasisimple with the
  shape and odd centre (`I.toolkit.lay` at `↥N_G(X)`; `t ∈ E₀` so `E₀ ≠ 1`: the proof of
  `Work.CORE4.layer_facts_coatom` uses the coatom only for `≠ ⊤`).  So `e ∈ Z(E₀)`, and `x`
  centralizes `E₀`.
Necessity of "inner": the order-3 field automorphism of `L₂(125)` centralizes `L₂(5)` but not
`L₂(125)` (`gw19_qc.g` part C). -/
def SixLayerNLeMProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ (B : BenderSetup G) (D : Case2Data B),
    Case2Pre B D → ∀ X : Subgroup G, X ≠ ⊥ → X ≤ D.F →
      B.t ∈ layerIn (normalizer (X : Set G)) →
      layerIn D.M ≤ layerIn (normalizer (X : Set G)) → layerIn (normalizer (X : Set G)) ≤ D.M

/-- **S5.** (★) from S3–S4.
Route: `E₀ ≤ M ≤ N_G(E)`, so `E ⊴ E₀`; `E₀ ≠ ⊤` and `E` quasisimple, so
`Case2Six9Aux.layerIn_eq_of_normal_quasisimple` (at `K := E₀`) gives `layerIn E₀ = E`; `E₀` is
quasisimple (as in S4), so `layerIn E₀ = E₀` (same lemma with `E := E₀`, `K := E₀`).  Hence `E₀ = E`, and
`N_G(X) ≤ N_G(E₀) = N_G(E) = M` (`layerIn_le_normalizer`, `Case2Six9.normalizer_layerIn_eq_data`). -/
def SixStarOfLayerProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ (B : BenderSetup G) (D : Case2Data B),
    Case2Pre B D → ∀ X : Subgroup G, X ≠ ⊥ → X ≤ D.F →
      B.t ∈ layerIn (normalizer (X : Set G)) →
      layerIn D.M ≤ layerIn (normalizer (X : Set G)) → layerIn (normalizer (X : Set G)) ≤ D.M →
      normalizer (X : Set G) ≤ D.M

/-- **TI.** (★) ⟹ TI.  Route = `NOTES_CASE2SIX9.md` §3 (⇐): for `1 ≠ X := F ⊓ F^g`, `E` and `E^g`
lie in `C_G(X) ≤ N_G(X) ≤ M ⊓ M^g` ((★) at `X` and at `X^{g⁻¹} ≤ F`); both are normal
quasisimple in `K := E ⊔ E^g ≠ ⊤`, so `E = layerIn K = E^g`, `g ∈ N_G(E) = M`. -/
def SixTIOfStarProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ (B : BenderSetup G) (D : Case2Data B),
    Case2Pre B D → (∀ X : Subgroup G, X ≠ ⊥ → X ≤ D.F → normalizer (X : Set G) ≤ D.M) →
      ∀ g : G, g ∉ D.M → D.F ⊓ conjSub g D.F = ⊥

/-- **CY.** TI ⟹ `F` cyclic: `Case2Six9Aux.exists_witness_of_case2pre` (proved) +
`Case2Six9Aux.isCyclic_F_of_witness_and_ti` (in flight). -/
def SixCycOfTIProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ (B : BenderSetup G) (D : Case2Data B),
    Case2Pre B D → (∀ g : G, g ∉ D.M → D.F ⊓ conjSub g D.F = ⊥) → IsCyclic D.F

/-- (★) from S1–S5. -/
theorem star_of_leaves (I : C4Inputs) (h1 : SixENotLeHhatProp I) (h2 : SixTInLayerNProp I)
    (h3 : SixELeLayerNProp I) (hq : QOddCentProp I) (h4 : QOddCentProp I → SixLayerNLeMProp I)
    (h5 : SixStarOfLayerProp I) :
    ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ (B : BenderSetup G) (D : Case2Data B),
      Case2Pre B D → ∀ X : Subgroup G, X ≠ ⊥ → X ≤ D.F → normalizer (X : Set G) ≤ D.M := by
  intro G _ _ hbc B D hpre X hX hXF
  have hE := h1 G hbc B D hpre
  have ht := h2 G hbc B D hpre hE X hX hXF
  have hle := h3 G hbc B D hpre X hX hXF ht
  exact h5 G hbc B D hpre X hX hXF ht hle (h4 hq G hbc B D hpre X hX hXF ht hle)

/-- **Assembly**: `Case2SixImpl9` (statement unchanged) from the leaves. -/
theorem six9_of_leaves (I : C4Inputs) (h1 : SixENotLeHhatProp I) (h2 : SixTInLayerNProp I)
    (h3 : SixELeLayerNProp I) (hq : QOddCentProp I) (h4 : QOddCentProp I → SixLayerNLeMProp I)
    (h5 : SixStarOfLayerProp I) (hti : SixTIOfStarProp I) (hcy : SixCycOfTIProp I) :
    Case2SixImpl9 I := by
  intro G _ _ hbc B D hpre _hplus
  have hstar := star_of_leaves I h1 h2 h3 hq h4 h5 G hbc B D hpre
  have hTI := hti G hbc B D hpre hstar
  exact ⟨hTI, hcy G hbc B D hpre hTI⟩

/-- The same leaves also prove the older `Case2SixImpl` (no `Case2PrePlus`). -/
theorem six_of_leaves (I : C4Inputs) (h1 : SixENotLeHhatProp I) (h2 : SixTInLayerNProp I)
    (h3 : SixELeLayerNProp I) (hq : QOddCentProp I) (h4 : QOddCentProp I → SixLayerNLeMProp I)
    (h5 : SixStarOfLayerProp I) (hti : SixTIOfStarProp I) (hcy : SixCycOfTIProp I) :
    Case2SixImpl I := by
  intro G _ _ hbc B D hpre
  have hstar := star_of_leaves I h1 h2 h3 hq h4 h5 G hbc B D hpre
  have hTI := hti G hbc B D hpre hstar
  exact ⟨hTI, hcy G hbc B D hpre hTI⟩

end Work.GW2.C19
