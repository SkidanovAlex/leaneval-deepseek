/-
# Area `PSU3`: the interface of the case-c analysis

This module collects the definitions that the leaves of area `PSU3` share, matching the
lead's design (`Submission/Work/PSU3/NOTES_LEAD_bs_psu3.md` and `_design/PSU3Route.lean`,
not to be imported).  Provided here:

* `Work.PSU3.fMapTot` — the total version `Q → Q` of Peterfalvi's map `f`, `1 ↦ 1`;
* `Work.PSU3.Canon3` — the relation `t x t = g h t y` with `g y ∈ Q`, `h ∈ D` (the data
  `g(x), h(x), f(x)` of Ch. VII §1);
* `Work.PSU3.PSU3Hyp` — the hypotheses of `PSU3Prop` bundled;
* `Work.PSU3.E n = GaloisField 2 (2n)` with `σE = (·)^{2ⁿ}`;
* `Work.PSU3.CoarseFrame`, `Work.PSU3.OmegaHyp`, `Work.PSU3.DFpfBar` — the coarse
  coordinates of Stage A and the hypotheses of Stage B;
* `Work.PSU3.RankOneQUniquenessProp`, `Work.PSU3.ModelRankOneDatum` — the new shared Prop of
  area `RankOneUniqueness` and the model datum used for recognition (`Work.PSU3.recognize`).

Conventions: `x^a` is Peterfalvi's right action `a⁻¹ x a`; `D = twoPoint H t`, `V = centD H t`;
`Q0sub H = ⟨Inv H⟩`, `Ksub H t = J(D,t)`, `W H t = C_V(K)` (from `Work.ThmF.Setup`).
-/
import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.Statements
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.FMap
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.ModelGL

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.ThmF
open Work.PSU3

namespace Work.PSU3

/-! ## The total version of `f` -/

/-- The total version of `SZ.fMap` (`1 ↦ 1`): Peterfalvi's `f : Q# → Q#`, extended by the
identity. -/
noncomputable def fMapTot {E : Type*} [Field E] [FrobeniusInvolution E] (p : SZ E) : SZ E := by
  classical
  exact if h : p = 1 then 1 else SZ.fMap p h

@[simp] lemma fMapTot_one {E : Type*} [Field E] [FrobeniusInvolution E] :
    fMapTot (1 : SZ E) = 1 := by
  classical
  simp [fMapTot]

lemma fMapTot_of_ne_one {E : Type*} [Field E] [FrobeniusInvolution E] {p : SZ E} (hp : p ≠ 1) :
    fMapTot p = SZ.fMap p hp := by
  classical
  simp only [fMapTot, dif_neg hp]

/-! ## The hypotheses of `PSU3Prop`, bundled -/

/-- The hypotheses of `PSU3Prop` (Peterfalvi II, end of Ch. V / Ch. VI–VII): the situation
(B0)–(B2), simplicity, the split rank-one datum, `V ≠ 1` (`¬ IsZassenhaus`), condition (B3),
and `Q` a 2-group. -/
structure PSU3Hyp {G : Type} [Group G] [Finite G] (H Q : Subgroup G) (t : G) : Prop where
  /-- `G` is in situation (B0)–(B2). -/
  situation : Situation G
  /-- `G` is simple. -/
  simple : IsSimpleGroup G
  /-- `H = Q ⋊ D` is a split rank-one datum with involution `t`. -/
  split : IsSplitRankOne H Q t
  /-- `V = C_D(t) ≠ 1` (i.e. `G` is not a Zassenhaus group). -/
  notZ : ¬ IsZassenhaus H
  /-- Condition (B3): centralisers of prime-order subgroups of `V` have 2-rank `≥ 2`. -/
  B3 : ∀ P : Subgroup G, P ≤ centD H t → (Nat.card P).Prime →
    HasFourGroup (Subgroup.centralizer (P : Set G))
  /-- `Q` is a 2-group. -/
  two : IsPGroup 2 Q

/-! ## The canonical form data `g(x), h(x), f(x)` -/

/-- `Canon3 H Q t x g h y` : `t x t = g h t y` with `g, y ∈ Q` and `h ∈ D = H ∩ H^t`.  This
is the data of Peterfalvi's Ch. VII §1 (`g(x), h(x), f(x)`), stated for a single quadruple
`(g, h, y)` so that the identities H1–H6 are pure group computations. -/
def Canon3 {G : Type} [Group G] (H Q : Subgroup G) (t x g h y : G) : Prop :=
  g ∈ Q ∧ h ∈ twoPoint H t ∧ y ∈ Q ∧ t * x * t = g * h * t * y

/-! ## The field `E = GF(q²)`, `q = 2ⁿ` -/

/-- `E n = GF(2^{2n})`: the field `GF(q²)`, `q = 2ⁿ`, with the `q`-power Frobenius `σE`
installed by `Work.PSU3.galoisFieldFrobInv`. -/
abbrev E (n : ℕ) : Type := GaloisField 2 (2 * n)

/-! ## The coarse frame (output of Stage A, input of Stages B/C) -/

/-- **The coarse coordinates** used by Peterfalvi Ch. VII §2–§3(3): `Q₀ = Z(Q)` with
`zc : F ≅ Q₀` (`zc 1 = s`, `tst = sts`), `bar : Q → Q/Q₀ ≅ E`, a copy of `K⟨ζ⟩` inside `D`
mapped injectively to `E*` by `κ` and acting on `Q/Q₀` by multiplication (right action
`x ↦ d⁻¹ x d`), `K` acting on `Q₀` through `nm`, and one `ζ ∈ W#` with `ζ^{q+1} = 1`
(only one `ζ ∈ W` is needed, so `W` need not be shown cyclic). -/
structure CoarseFrame {G : Type} [Group G] (H Q : Subgroup G) (t : G) (n : ℕ) where
  /-- `Q₀ = Z(Q)`. -/
  Q0 : Subgroup G
  Q0_le : Q0 ≤ Q
  Q0_central : ∀ z ∈ Q0, ∀ x ∈ Q, z * x = x * z
  mem_Q0_iff : ∀ x ∈ Q, x ∈ Q0 ↔ x ^ 2 = 1
  sq_mem_Q0 : ∀ x ∈ Q, x ^ 2 ∈ Q0
  /-- `Q/Q₀ ≅ E`. -/
  bar : Q →* Multiplicative (E n)
  bar_surjective : Function.Surjective bar
  bar_eq_one_iff : ∀ x : Q, bar x = 1 ↔ (x : G) ∈ Q0
  /-- `Q₀ ≅ F` (the fixed field of `σE`). -/
  zc : E n → G
  zc_mem : ∀ y : E n, σE y = y → zc y ∈ Q0
  zc_add : ∀ y y' : E n, σE y = y → σE y' = y' → zc (y + y') = zc y * zc y'
  zc_surj : ∀ z ∈ Q0, ∃ y : E n, σE y = y ∧ zc y = z
  zc_inj : ∀ y y' : E n, σE y = y → σE y' = y' → zc y = zc y' → y = y'
  s_struct : t * zc 1 * t = zc 1 * t * zc 1
  /-- A complement `KW ≤ D` of `Q₀` in `D`, linearly isomorphic to a subgroup of `E*`. -/
  KW : Subgroup G
  KW_le : KW ≤ twoPoint H t
  /-- `KW` normalises `Q` (found necessary by the review of `fine_coords`: without it the
  equivariance of the squaring map `Q/Q₀ → Q₀` is only available on `Q ∩ d⁻¹ Q d`). -/
  KW_normal : ∀ d : KW, ∀ x ∈ Q, (d : G)⁻¹ * x * d ∈ Q
  K_le : Ksub H t ≤ KW
  κ : KW →* (E n)ˣ
  κ_injective : Function.Injective κ
  mem_K_iff : ∀ d : KW, (d : G) ∈ Ksub H t ↔ σE ((κ d : (E n)ˣ) : E n) = (κ d : E n)
  K_surj : ∀ a : (E n)ˣ, σE (a : E n) = a → ∃ d : KW, κ d = a
  ζ : KW
  ζ_mem_W : (ζ : G) ∈ W H t
  ζ_ne_one : ζ ≠ 1
  ζ_norm : (κ ζ : E n) * σE (κ ζ : E n) = 1
  KW_gen : ∀ d : KW, ∃ k : KW, (k : G) ∈ Ksub H t ∧ ∃ j : ℕ, d = k * ζ ^ j
  W_semireg : ∀ w ∈ W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w → x ∈ Q0
  act_bar : ∀ (d : KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
    Multiplicative.toAdd (bar y) = (κ d : E n) * Multiplicative.toAdd (bar x)
  /-- The action of `K` on `Q₀ ≅ F` (Peterfalvi's `nm`). -/
  nm : (E n)ˣ →* (E n)ˣ
  nm_F : ∀ a : (E n)ˣ, σE (a : E n) = a → σE (nm a : E n) = nm a
  act_zc_K : ∀ d : KW, (d : G) ∈ Ksub H t → ∀ y : E n, σE y = y →
    (d : G)⁻¹ * zc y * d = zc ((nm (κ d) : E n) * y)
  act_zc_ζ : ∀ y : E n, σE y = y → (ζ : G)⁻¹ * zc y * ζ = zc y

/-! ## The hypotheses of Stage B -/

/-- The hypothesis of Ch. VII §3 Prop.: `f(ω) = (ω⁻¹)^ζ` and `h(ω) ∈ W`. -/
def OmegaHyp {G : Type} [Group G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : CoarseFrame H Q t n) (ω : G) : Prop :=
  ω ∈ Q ∧ ω ∉ fr.Q0 ∧ ∃ g ∈ Q, ∃ hh ∈ W H t,
    t * ω * t = g * hh * t * ((fr.ζ : G)⁻¹ * ω⁻¹ * fr.ζ)

/-- `D` acts fixed-point-freely on `(Q/Q₀)#`. -/
def DFpfBar {G : Type} [Group G] (H Q : Subgroup G) (t : G) : Prop :=
  ∀ d ∈ twoPoint H t, d ≠ 1 → ∀ x ∈ Q, x ∉ Q0sub H → d⁻¹ * x * d * x⁻¹ ∉ Q0sub H

/-! ## Recognition from the model

The new shared Prop of area `RankOneUniqueness` and the model datum live in
`Submission.Work.RankOneUniqueness.Statements` (`Work.RankOneUniqueness.RankOneQUniquenessProp`,
`Work.RankOneUniqueness.ModelRankOneDatum`), and the recognition lemma is
`Work.RankOneUniqueness.recognize`:
`RankOneQUniquenessProp → ModelRankOneDatum Y C fC → (e : Q ≃* C) → (F_rel ↦ fC) → Nonempty (G ≃* Y)`.
Since `Work.RankOneUniqueness.rankOneQUniqueness` is delivered unconditionally, the recognition
step of `psu3Prop_of` takes no named hypothesis beyond the model datum itself.
-/

end Work.PSU3
