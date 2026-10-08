import Mathlib
import Submission.Work.CORE2B.L29CallSite
/-!
# CORE2B, Lemma 2.9 (Bender 1981, p. 222): the four leaves of the lead's design pass 15

Copy of the definitions and leaf statements of `_design_gw/Core15L29.lean`
(namespace `Work.CORE2B.C15`), minus its trailing (unproved) assembly.

* `L29PairProp`      (P1) the pair `u, v` with `[v, C_A(u)] ≠ 1`, from `T.c11iii`;
* `L29GoodProp`      (P2) the printed last sentence with `u = t`;
* `L29TransportProp` (P3) conjugation transport of a witness pair;
* `L29FaithfulProp`  (P4) "Otherwise, `V` acts faithfully on `A := F_{2'}(N)`".

The corrected leaf `L29_contra_h27` (and `L29CallSite`) is in `Submission.Work.CORE2B.L29CallSite`.
-/
/-
Design pass 15 (lead), area CORE2B: Bender 1981 Lemma 2.9 (p. 222), the correct reading.

Page image (p. 222, `lead_gw_prior/pg07.png`):
  "Proof. Otherwise, V acts faithfully on A := F_{2'}(N). Then V contains two involutions,
   say t and s, such that X := [s, C_A(t)] ≠ 1.  Lying in O₂(N_G(X)), t centralizes N_A(X),
   hence (by 1.1.iv) centralizes A, a contradiction."

"say t and s" is a RENAMING: 1.1(iii) gives *some* pair `u ≠ v` in `V#` with `[v, C_A(u)] ≠ 1`;
since `N_G(V)` is transitive on `V#` (standing fact, p. 219, = `T.fus`) and the lemma is invariant
under replacing `N` by `N^g`, `g ∈ N_G(V)` (`V ≤ N^g`, `F_{2'}(N^g) = A^g`, faithfulness
preserved, the hypothesis on `t, S, U` does not mention `N`), one may take `u = t`.
The C₇³ example (`t = diag(1,-1,-1)`, `s = diag(1,-1,1)`) has the pair `(u,v) = (s,t)`:
`[t, C_A(s)] = ⟨e₃⟩ ≠ 1`; the fusion `s ↦ t` is impossible there only because `G` is not simple.

Leaves (statements only; see NOTES_LEAD_gw_design15.md §2):
  P1 `L29PairProp`      pure, from `c11iii`
  P2 `L29GoodProp`      the printed last sentence, with the two missing justifications
  P3 `L29TransportProp` pure conjugation bookkeeping
  P4 `L29FaithfulProp`  "Otherwise V acts faithfully on A" (owner's D16 cases (ii)-(iv) + (i))
-/

namespace Work.CORE2B.C15

open Subgroup

/-- `V` acts faithfully on `A`. -/
def Faithful {G : Type} [Group G] (V A : Subgroup G) : Prop :=
  ∀ v ∈ V, v ≠ 1 → ¬ A ≤ centralizer ({v} : Set G)

/-- **P1 (1.1(iii) contrapositive).**  A four-group acting faithfully on an odd-order group
`A` has `u, v ∈ V#` with `[v, C_A(u)] ≠ 1`.
Route: otherwise every `C_A(u)` (`u ∈ V#`) is centralized by all of `V` (`u` itself trivially),
and `A = ⨆_{u ∈ V#} C_A(u)` (`h11iii`, `p = 2`, `P = E = V`), so `V ≤ C(A)`. -/
def L29PairProp : Prop :=
  Work.GW2.Coprime11iiiProp →
  ∀ (G : Type) [Group G] [Finite G] (A V : Subgroup G), Odd (Nat.card A) →
    V ≤ normalizer (A : Set G) → Work.GW2.IsFourGroup V → Faithful V A →
      ∃ u ∈ V, ∃ v ∈ V, u ≠ 1 ∧ v ≠ 1 ∧
        ⁅zpowers v, A ⊓ centralizer ({u} : Set G)⁆ ≠ ⊥

/-- **P2 (the printed last sentence, with `u = t`).**
Route, `X := [⟨s⟩, C_A(t)]`:
1. `X ≤ C_A(t) ≤ H` (`s` normalizes `C_A(t)`: `s ∈ V ≤ N(A)`, `st = ts`), `X` odd; `H = U S`
   (`T.split`; `S` dihedral as it contains the four-group `V`), so `H/U` is a 2-group and the
   odd `X` lies in `U`.  `⁅⟨s⟩, X⁆ = X` by `T.c11i`.  So `hyp` gives `t ∈ O₂(N_G(X))`.
2. `t` normalizes `A` and `X` (it centralizes `X`), hence `N_A(X)`; for `y ∈ N_A(X)`,
   `[y,t] ∈ N_A(X) ∩ O₂(N_G(X)) = 1` (odd ∩ 2-group).  So `N_G(X) ⊓ A ≤ C(t)`.
3. `L29_tower` (PROVED) gives `A ≤ C(t)`, contradicting faithfulness at `t ≠ 1`. -/
def L29GoodProp : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (G : Type) [Group G] [Finite G],
    Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (V A : Subgroup G),
      V ≤ (B.S : Subgroup G) → B.t ∈ V → Work.GW2.IsFourGroup V →
      (∀ (s : G) (X : Subgroup G), s ∈ (B.S : Subgroup G) → X ≤ B.U → X ≠ ⊥ →
        ⁅zpowers s, X⁆ = X → B.t ∈ Work.GW2.pCoreIn 2 (normalizer (X : Set G))) →
      Group.IsNilpotent ↥A → Odd (Nat.card A) → V ≤ normalizer (A : Set G) → Faithful V A →
      ∀ s ∈ V, ⁅zpowers s, A ⊓ centralizer ({B.t} : Set G)⁆ ≠ ⊥ → False

/-- **P3 (transport).**  Conjugating by `g ∈ N_G(V)` with `g u g⁻¹ = t` moves a witness pair
`(u, v)` for `A` to the witness pair `(t, g v g⁻¹)` for `A^g`, keeping oddness, nilpotency,
`V ≤ N(A^g)` and faithfulness. -/
def L29TransportProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A V : Subgroup G) (u v g t : G),
    Group.IsNilpotent ↥A → Odd (Nat.card A) → V ≤ normalizer (A : Set G) → Faithful V A →
    u ∈ V → v ∈ V → g ∈ normalizer (V : Set G) → g * u * g⁻¹ = t →
    ⁅zpowers v, A ⊓ centralizer ({u} : Set G)⁆ ≠ ⊥ →
      Group.IsNilpotent ↥(Work.GW2.conjSub g A) ∧ Odd (Nat.card (Work.GW2.conjSub g A)) ∧
      V ≤ normalizer ((Work.GW2.conjSub g A : Subgroup G) : Set G) ∧
      Faithful V (Work.GW2.conjSub g A) ∧ g * v * g⁻¹ ∈ V ∧
      ⁅zpowers (g * v * g⁻¹), Work.GW2.conjSub g A ⊓ centralizer ({t} : Set G)⁆ ≠ ⊥

/-- **P4 ("Otherwise, V acts faithfully on A := F_{2'}(N)").**  Call-site form; the owner's
D16 case analysis: (ii) central involution, (iii) `O₂(N)` a four-group, (iv) quasisimple `E`
(excluded by `N` solvable, Lemma 2.7) are PROVED contradictions; case (i)
`C_N(A) ≤ A` gives `V ∩ C_N(A) ≤ V ∩ A = 1`. -/
def L29FaithfulProp : Prop :=
  ∀ (T : Work.GW2.LocalToolkit) (_h22 : Work.GW2.Lemma22Prop) (_h26 : Work.GW2.Thm26Prop)
    (_h27 : Work.GW2.Lemma27Prop) (G : Type) [Group G] [Finite G],
    Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
    ∀ (B : Work.GW2.BenderSetup G) (V N : Subgroup G), L29CallSite B V N →
      V ⊓ Work.GW2.pCoreIn 2 N = ⊥ → V ⊓ Work.GW2.layerIn N = ⊥ →
        Group.IsNilpotent ↥(Work.GW2.fittingPiIn {2}ᶜ N) ∧
        Odd (Nat.card (Work.GW2.fittingPiIn {2}ᶜ N)) ∧
        V ≤ normalizer ((Work.GW2.fittingPiIn {2}ᶜ N : Subgroup G) : Set G) ∧
        Faithful V (Work.GW2.fittingPiIn {2}ᶜ N)


end Work.CORE2B.C15
