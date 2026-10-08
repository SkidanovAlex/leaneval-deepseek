import Submission.Work.ZJB.DefsPaper
import Submission.Work.ZJB.ZJBPropPrime
import Submission.Work.ZJB.ThompsonWeakClosed
import Submission.Work.ZJB.NormalizerConj
import Submission.Work.ZJB.Lemma51Paper

/-!
# ZJB — Theorem 5.1, step (I): vocabulary and leaf statements

Statements copied (verbatim, modulo namespace) from the lead's design file
`Submission/Work/_design_gw/Core11ZJB.lean` §2, which is the companion of
`NOTES_LEAD_gw_design11.md` §3.2.  The assembly `step1_of_leaves` lives in
`Submission/Work/ZJB/Step1/Assembly.lean`; the individual leaves are proved in
`Submission/Work/ZJB/Step1/<leaf>.lean`.

Everything here is stated *inside* `G`: "`N(H)` satisfies `(C_p)`" is `CpIn p (normalizer H)`,
so the argument never has to change the ambient group.  The convention is the paper's:
`x^g = g⁻¹ x g` (`pconj`).
-/

namespace Work.ZJB

open Work.GW2
open Subgroup

/-! ## 1. The vocabulary -/

/-- The paper's `X^g = g⁻¹ X g`. -/
def pconj {G : Type*} [Group G] (X : Subgroup G) (g : G) : Subgroup G :=
  X.map (MulAut.conj g⁻¹).toMonoidHom

@[simp]
theorem mem_pconj {G : Type*} [Group G] {X : Subgroup G} {g x : G} :
    x ∈ pconj X g ↔ g * x * g⁻¹ ∈ X := by
  rw [pconj, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem pconj_mono {G : Type*} [Group G] {X Y : Subgroup G} (h : X ≤ Y) (g : G) :
    pconj X g ≤ pconj Y g :=
  Subgroup.map_mono h

/-- `pconj X g` is the conjugate `g⁻¹Xg`; conjugating by `h` first and then by `g` conjugates
by `h⁻¹g` (in that order). -/
theorem pconj_map_conj {G : Type*} [Group G] (X : Subgroup G) (g h : G) :
    pconj (X.map (MulAut.conj h).toMonoidHom) g = pconj X (h⁻¹ * g) := by
  ext x
  rw [mem_pconj, mem_pconj, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    show h⁻¹ * (g * x * g⁻¹) * h = (h⁻¹ * g) * x * (h⁻¹ * g)⁻¹ by group]

/-- `T` is a Sylow `p`-subgroup of the subgroup `M` (i.e. a maximal `p`-subgroup of `M`). -/
def IsSylowIn {G : Type*} [Group G] (p : ℕ) (T M : Subgroup G) : Prop :=
  T ≤ M ∧ IsPGroup p T ∧ ∀ Q : Subgroup G, T ≤ Q → Q ≤ M → IsPGroup p Q → Q = T

/-- The paper's `(C_p)` for the group `M`, stated inside `G`. -/
def CpIn {G : Type*} [Group G] (p : ℕ) (M : Subgroup G) : Prop :=
  ∀ T : Subgroup G, IsSylowIn p T M → ∀ W : Set G, W.Nonempty → W ⊆ (T : Set G) → ∀ g ∈ M,
    (∀ w ∈ W, g⁻¹ * w * g ∈ T) →
    ∃ c n : G, c ∈ M ∧ c ∈ centralizer W ∧ n ∈ M ∧ n ∈ normalizer (ZJ T : Set G) ∧ g = c * n

/-- The paper's `(C_p*)` for the group `M`, stated inside `G`. -/
def CpStarIn {G : Type*} [Group G] (p : ℕ) (M : Subgroup G) : Prop :=
  ∀ T : Subgroup G, IsSylowIn p T M → ∀ W : Subgroup G, W ≤ M →
    W ≤ normalizer (ZJ T : Set G) → IsPGroup p W → ∀ g ∈ M,
    (∀ w ∈ W, g⁻¹ * w * g ∈ normalizer (ZJ T : Set G)) →
    ∃ c n : G, c ∈ M ∧ c ∈ centralizer (W : Set G) ∧ n ∈ M ∧ n ∈ normalizer (ZJ T : Set G) ∧
      g = c * n

/-- Hypothesis (a) of Theorem 5.1, for every Sylow subgroup (what Theorem B's induction
supplies when `O_p(G) = 1`). -/
def HypA (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (S₂ : Sylow p G) (H : Subgroup G), ZS (S₂ : Subgroup G) ≤ H → H ≤ S₂ →
    CpIn p (normalizer (H : Set G))

/-- `ν_p(|M|)`, so that `|M|_p = p ^ nuP p M`. -/
noncomputable def nuP {G : Type*} [Group G] (p : ℕ) (M : Subgroup G) : ℕ :=
  (Nat.card M).factorization p

/-- The paper's `D = N(J) ∩ S₁` (with `J = J(S)`). -/
def Dsub {G : Type*} [Group G] {p : ℕ} (S S₁ : Sylow p G) : Subgroup G :=
  normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) ⊓ (S₁ : Subgroup G)

/-- `S₁` is a "bad" Sylow subgroup (`Z(S) ≤ S₁`, `Z(S) ⊄ Z(J(S₁))`) with `|N(J) ∩ S₁|`
maximal among bad ones (stated as: every Sylow `S₂ ⊇ Z(S)` with larger `|N(J) ∩ S₂|` is good). -/
def MaxBad {G : Type*} [Group G] [Finite G] (p : ℕ) (S S₁ : Sylow p G) : Prop :=
  ZS (S : Subgroup G) ≤ S₁ ∧ ¬ ZS (S : Subgroup G) ≤ ZJ (S₁ : Subgroup G) ∧
    ∀ S₂ : Sylow p G, ZS (S : Subgroup G) ≤ S₂ →
      Nat.card (Dsub S S₁) < Nat.card (Dsub S S₂) → ZS (S : Subgroup G) ≤ ZJ (S₂ : Subgroup G)

/-- The paper's set `𝓗` (p. 1118) for hypothesis (a): `H ≠ 1`, condition (i), condition (ii). -/
def InScrH {G : Type*} [Group G] [Finite G] (p : ℕ) (S : Sylow p G) (D : Subgroup G) (a : G)
    (H : Subgroup G) : Prop :=
  H ≠ ⊥ ∧
    (∃ T : Subgroup G, ∃ g ∈ normalizer (H : Set G), IsSylowIn p T (normalizer (H : Set G)) ∧
      ZS (S : Subgroup G) ≤ T ∧ pconj (ZS (S : Subgroup G)) g = pconj (ZS (S : Subgroup G)) a ∧
      pconj (ZS (S : Subgroup G)) a ≤ T ∧
      Nat.card D < Nat.card ↥(normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) ⊓ T)) ∧
    ∃ S₂ : Sylow p G, ZS (S₂ : Subgroup G) ≤ H ∧ H ≤ S₂

/-- **Step (I)**: `Z(S)^g ⊆ S ⟹ Z(S)^g ⊆ Z(J(S))`, under hypothesis (a). -/
def Step1Prop (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  HypA p G → ∀ (S : Sylow p G) (g : G),
    pconj (ZS (S : Subgroup G)) g ≤ S → pconj (ZS (S : Subgroup G)) g ≤ ZJ (S : Subgroup G)

/-! ## 2. The leaf statements -/

/-- **F0.** `Z(P) ≤ Z(J(P))`. -/
def ZSLeZJProp (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ P : Subgroup G, ZS P ≤ ZJ P

/-- **F1.** If `J(S) ≤ Q` for a `p`-subgroup `Q`, then `J(Q) = J(S)`. -/
def ThompsonJEqOfLeProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (S : Sylow p G) (Q : Subgroup G), IsPGroup p Q → Work.GW2.thompsonJ (S : Subgroup G) ≤ Q →
    Work.GW2.thompsonJ Q = Work.GW2.thompsonJ (S : Subgroup G)

/-- **F2.** `|T| = |M|_p` for a Sylow subgroup of `M`. -/
def CardSylowInProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ T M : Subgroup G, IsSylowIn p T M → Nat.card T = p ^ nuP p M

/-- **F3 (normalizer condition).** A `p`-subgroup `T` with `|N(T)|_p ≤ |T|` is Sylow in `G`. -/
def SylowOfNormalizerProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ T : Subgroup G, IsPGroup p T → p ^ nuP p (normalizer (T : Set G)) ≤ Nat.card T →
    ∃ T' : Sylow p G, (T' : Subgroup G) = T

/-- **F4.** `N(J(P)) ≤ N(Z(J(P)))`. -/
def NormJLeNormZJProp (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ P : Subgroup G, normalizer (Work.GW2.thompsonJ P : Set G) ≤ normalizer (ZJ P : Set G)

/-- **L5.1 inside `M`.** `(C_p) ⟹ (C_p*)` inside a fixed subgroup `M`. -/
def CpStarInOfCpInProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ M : Subgroup G, CpIn p M → CpStarIn p M

/-- **Bridge** to the induction hypothesis of Theorem B (`SatisfiesCpPaper` of the group
`↥M`): transport along `M.subtype`. -/
def CpInOfSatisfiesProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ M : Subgroup G, SatisfiesCpPaper p ↥M → CpIn p M

/-- **I.0** A violation of (I) gives a bad Sylow subgroup, and then a `MaxBad` one. -/
def ExistsMaxBadProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (S : Sylow p G) (g : G), pconj (ZS (S : Subgroup G)) g ≤ S →
    ¬ pconj (ZS (S : Subgroup G)) g ≤ ZJ (S : Subgroup G) → ∃ S₁ : Sylow p G, MaxBad p S S₁

/-- **I.1** A bad `S₁` is not contained in `N(J)`. -/
def DltProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ S S₁ : Sylow p G, ZS (S : Subgroup G) ≤ S₁ → ¬ ZS (S : Subgroup G) ≤ ZJ (S₁ : Subgroup G) →
    ¬ (S₁ : Subgroup G) ≤ normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G)

/-- **I.2 (Burnside's argument, p. 1117 foot – p. 1118 top).**  If `D ≤ A ≤ N(D) ∩ S₁` and
`Z(S)^a ≤ Z(J)` for all `a ∈ A`, then `A = D`. -/
def ClaimAProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ S S₁ : Sylow p G, MaxBad p S S₁ → ∀ A : Subgroup G, Dsub S S₁ ≤ A →
    A ≤ normalizer (Dsub S S₁ : Set G) ⊓ (S₁ : Subgroup G) →
    (∀ a ∈ A, pconj (ZS (S : Subgroup G)) a ≤ ZJ (S : Subgroup G)) → A = Dsub S S₁

/-- **I.3** `Z(S₁) ≤ D`, and some `a ∈ N(D) ∩ S₁` has `Z(S)^a ⊄ Z(J)`. -/
def ExistsAProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ S S₁ : Sylow p G, MaxBad p S S₁ →
    ZS (S₁ : Subgroup G) ≤ Dsub S S₁ ∧
      ∃ a ∈ normalizer (Dsub S S₁ : Set G) ⊓ (S₁ : Subgroup G),
        ¬ pconj (ZS (S : Subgroup G)) a ≤ ZJ (S : Subgroup G)

/-- **I.4 (5.1)+(5.3).** `D` is not Sylow in `N(J)`, so a Sylow `T₁` of `N(D)` containing `D`
has `|N(J) ∩ T₁| > |D|`. -/
def ExistsT1Prop (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ S S₁ : Sylow p G, MaxBad p S S₁ →
    ∃ T₁ : Subgroup G, IsSylowIn p T₁ (normalizer (Dsub S S₁ : Set G)) ∧ Dsub S S₁ ≤ T₁ ∧
      Nat.card (Dsub S S₁) <
        Nat.card ↥(normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) ⊓ T₁)

/-- **I.5** `D ∈ 𝓗` (witnesses `T₁`, `g = a`, `S₂ = S₁`); `D ≠ 1` because `1 ≠ Z(S) ≤ D`. -/
def DMemProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ S S₁ : Sylow p G, (S : Subgroup G) ≠ ⊥ → MaxBad p S S₁ →
    ZS (S₁ : Subgroup G) ≤ Dsub S S₁ →
    ∀ a ∈ normalizer (Dsub S S₁ : Set G) ⊓ (S₁ : Subgroup G),
    ∀ T₁ : Subgroup G, IsSylowIn p T₁ (normalizer (Dsub S S₁ : Set G)) → Dsub S S₁ ≤ T₁ →
      Nat.card (Dsub S S₁) <
        Nat.card ↥(normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) ⊓ T₁) →
      InScrH p S (Dsub S S₁) a (Dsub S S₁)

/-- **I.6** `𝓗` has a member with maximal `ν_p(|N(H)|)` (finite, nonempty). -/
def ExistsMaxHProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (S : Sylow p G) (D : Subgroup G) (a : G), InScrH p S D a D →
    ∃ H, InScrH p S D a H ∧
      ∀ H', InScrH p S D a H' → nuP p (normalizer (H' : Set G)) ≤ nuP p (normalizer (H : Set G))

/-- **I.7a** `(C_p)` in `N(H)` applied to `W = Z(S)`: `Z(S)^n = Z(S)^a` for some
`n ∈ N(H) ∩ N(Z(J(T)))`. -/
def StepNProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (S : Sylow p G) (H T : Subgroup G) (g a : G), CpIn p (normalizer (H : Set G)) →
    IsSylowIn p T (normalizer (H : Set G)) → g ∈ normalizer (H : Set G) →
    ZS (S : Subgroup G) ≤ T → pconj (ZS (S : Subgroup G)) g = pconj (ZS (S : Subgroup G)) a →
    pconj (ZS (S : Subgroup G)) a ≤ T → (S : Subgroup G) ≠ ⊥ →
    ∃ n ∈ normalizer (H : Set G) ⊓ normalizer (ZJ T : Set G),
      pconj (ZS (S : Subgroup G)) n = pconj (ZS (S : Subgroup G)) a

/-- **I.7b** `Z(J(T)) ∈ 𝓗`. -/
def ZJTMemProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (S : Sylow p G) (D H T : Subgroup G) (a n : G), InScrH p S D a H →
    IsSylowIn p T (normalizer (H : Set G)) → ZS (S : Subgroup G) ≤ T →
    pconj (ZS (S : Subgroup G)) a ≤ T →
    Nat.card D < Nat.card ↥(normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) ⊓ T) →
    n ∈ normalizer (ZJ T : Set G) →
    pconj (ZS (S : Subgroup G)) n = pconj (ZS (S : Subgroup G)) a →
    InScrH p S D a (ZJ T)

/-- **I.8 (the closing argument, p. 1118 foot – p. 1119).** -/
def FinalProp (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (S T : Sylow p G) (a n : G), CpStarIn p (normalizer (ZS (S : Subgroup G) : Set G)) →
    ZS (S : Subgroup G) ≤ ZJ (T : Subgroup G) → n ∈ normalizer (ZJ (T : Subgroup G) : Set G) →
    pconj (ZS (S : Subgroup G)) n = pconj (ZS (S : Subgroup G)) a →
    pconj (ZS (S : Subgroup G)) a ≤ normalizer (ZJ (S : Subgroup G) : Set G) →
    pconj (ZS (S : Subgroup G)) a ≤ ZJ (S : Subgroup G)

end Work.ZJB
