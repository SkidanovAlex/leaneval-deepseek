import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.Basic
import Submission.Work.Induction.Defs
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv
import Submission.Work.Clifford.irrDeg_eq_one_of_commutator_le_charKernel

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.Feit.not_excl_linear` (Feit's leaf F2c)

In a split rank-one Zassenhaus configuration `(H, Q, t)` with `Q` an abelian `2`-group, every
irreducible character `lc` of `H` which does **not** lie in
`𝒮 = excludingKernel H Q = {χ ∈ Irr H | Q ⊄ ker χ}` has degree `1` and is trivial on `Q`.

Equivalently: every irreducible character of `H` which is trivial on `Q` is linear, i.e. the
quotient `H ⧸ Q ≅ twoPoint H t` is abelian in the only way that matters for character theory.

## The argument

* `Q ≠ ⊥`: if `Q = ⊥` then `D = twoPoint H t = Q ⊔ D = H`, so `|D|` would be both odd
  (`ZassenhausPSL2.dStab_odd`) and even (`IsStronglyEmbedded`).
* `D = twoPoint H t` is abelian: the Weyl element `t` inverts every element of `D`
  (`ZData.t_conj_eq_inv`, which is Burnside's lemma for the fixed-point-free involution
  `d ↦ t d t` of `D`), so `a * b = ((a * b)⁻¹)⁻¹ = (a⁻¹ * b⁻¹)⁻¹ = b * a` (`twoPoint_comm`).
* Hence `H = Q ⋊ D` is metabelian modulo `Q`, i.e. `H ⧸ Q` is commutative, i.e.
  `⁅H, H⁆ ≤ Q` (`commutator_le_subgroupOf_Q`, via
  `Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top`).
* `lc ∉ excludingKernel H Q`, together with `lc ∈ Irr H`, says exactly that `lc` is constant on
  `Q`, i.e. that `Q ⊆ charKernel lc`.  Since `Q ⊇ ⁅H, H⁆`, the character descends to the
  commutative quotient `H ⧸ Q` and therefore has degree `1`
  (`Work.Clifford.irrDeg_eq_one_of_commutator_le_charKernel`).
* On `Q` the character is then constantly `lc 1 = 1` by the very hypothesis.

The hypotheses `hab : IsAbelianSubgroup Q` and `hz : IsZassenhaus H`/`h2 : IsPGroup 2 Q`
enter only through the abelianness of `D` (which needs `Zassenhaus` and `IsPGroup 2 Q`, see
`ZData.t_conj_eq_inv`); the proof is independent of the Feit bound of `ZData.feit_bound`.

## Note on `Fintype` instances

`Submission.Blueprint.excludingKernel` was defined in a context with only `[Fintype G]`, so its
internal `Work.CharCore.Irr ↥H` carries the instance derived from `[Fintype G]`, whereas the
statement above also assumes a `Fintype ↥H` instance; the two need not be syntactically equal.
The bridge is `mem_Irr_of_fintype` (through the representation-theoretic characterisation
`Work.CharCore.mem_Irr_iff_fdrep`, which does not depend on the `Fintype` instance).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.ZassenhausPSL2.Feit

variable {G : Type} [Group G]

/-- In a split rank-one datum the regular normal subgroup is non-trivial: `Q = ⊥` would force
`D = twoPoint H t = H`, so `|D|` would be odd (`dStab_odd`) and even (strong embedding). -/
private theorem Q_ne_bot {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) : Q ≠ ⊥ := by
  intro hbot
  have htwo : twoPoint H t = H := by
    have hs : Q ⊔ twoPoint H t = H := h.sup_eq
    rw [hbot, bot_sup_eq] at hs
    exact hs
  have hodd : Odd (Nat.card (twoPoint H t)) :=
    Work.ZassenhausPSL2.dStab_odd H t h.stronglyEmbedded h.not_mem
  rw [htwo] at hodd
  exact (Nat.not_odd_iff_even.mpr h.stronglyEmbedded.2.1) hodd

/-- **`D = twoPoint H t` is abelian.**  The Weyl element `t` inverts every element of `D`
(`ZData.t_conj_eq_inv`), so `t * (a * b) * t = (t * a * t) * (t * b * t)` gives
`(a * b)⁻¹ = a⁻¹ * b⁻¹`, whence `a * b = b * a`. -/
private theorem twoPoint_comm {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (h2 : IsPGroup 2 Q) (hQ : Q ≠ ⊥) :
    ∀ a ∈ twoPoint H t, ∀ b ∈ twoPoint H t, a * b = b * a := by
  have hinv := Work.ZassenhausPSL2.ZData.t_conj_eq_inv H Q t h hz hQ h2
  intro a ha b hb
  have hstep : t * (a * b) * t = (t * a * t) * (t * b * t) := by
    have h' : t⁻¹ = t := Work.ZassenhausPSL2.t_inv h
    have hmem : ∀ z : G, (MulAut.conj t) z = t * z * t := fun z => by
      rw [MulAut.conj_apply, h']
    rw [← hmem (a * b), map_mul, hmem a, hmem b]
  have hkey : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
    rw [← hinv (a * b) ((twoPoint H t).mul_mem ha hb), hstep, hinv a ha, hinv b hb]
  calc a * b = ((a * b)⁻¹)⁻¹ := (inv_inv _).symm
    _ = (a⁻¹ * b⁻¹)⁻¹ := by rw [hkey]
    _ = b * a := by rw [mul_inv_rev, inv_inv, inv_inv]

/-- Membership in `Work.CharCore.Irr` is independent of the chosen `Fintype` instance: both
`Finset`s consist of the characters of the simple finite dimensional complex representations
(`Work.CharCore.mem_Irr_iff_fdrep`). -/
private lemma mem_Irr_of_fintype {X : Type} [Group X] {i₁ i₂ : Fintype X} {χ : X → ℂ}
    (h : χ ∈ @Work.CharCore.Irr X _ i₁) : χ ∈ @Work.CharCore.Irr X _ i₂ := by
  rw [@Work.CharCore.mem_Irr_iff_fdrep X _ i₁ χ] at h
  rw [@Work.CharCore.mem_Irr_iff_fdrep X _ i₂ χ]
  exact h

/-- A general form of `Finset.notMem_filter` with the `DecidablePred` instance kept as an
explicit argument, so that it applies to a filter whose instance is opaque. -/
private lemma not_pred_of_notMem_filter {α : Type} {p : α → Prop} {inst : DecidablePred p}
    {s : Finset α} {a : α} (h : a ∉ @Finset.filter α p inst s) (ha : a ∈ s) : ¬ p a :=
  fun hp => h (Finset.mem_filter.mpr ⟨ha, hp⟩)

/-- `H ⧸ Q` is commutative when the two-point stabiliser `D = twoPoint H t` is abelian:
`H = Q ⋊ D`, so `H ⧸ Q` is a quotient of `D`. -/
private theorem commutator_le_subgroupOf_Q {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t)
    (hcomm : ∀ a ∈ twoPoint H t, ∀ b ∈ twoPoint H t, a * b = b * a) :
    _root_.commutator ↥H ≤ Q.subgroupOf H := by
  haveI hN : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  have hsup : (Q.subgroupOf H) ⊔ ((twoPoint H t).subgroupOf H) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.le (inf_le_left : twoPoint H t ≤ H), h.sup_eq,
      Subgroup.subgroupOf_self]
  have hcommD : IsMulCommutative ↥((twoPoint H t).subgroupOf H) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    apply Subtype.ext
    have h' := hcomm ((a : ↥H) : G) (Subgroup.mem_subgroupOf.mp a.2)
      ((b : ↥H) : G) (Subgroup.mem_subgroupOf.mp b.2)
    simpa using h'
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hcommD

theorem not_excl_linear {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥H] {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) {lc : H → ℂ}
    (hlc : lc ∈ Work.CharCore.Irr H) (hlc' : lc ∉ Submission.Blueprint.excludingKernel H Q) :
    lc 1 = 1 ∧ ∀ x : H, (x : G) ∈ Q → lc x = 1 := by
  classical
  -- `Q ≠ ⊥`, and `D = twoPoint H t` is abelian because `t` inverts its elements
  have hQ : Q ≠ ⊥ := Q_ne_bot h
  have hcomm := twoPoint_comm h hz h2 hQ
  -- hence `⁅H, H⁆ ≤ Q`
  haveI hN : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  have hM : _root_.commutator ↥H ≤ Q.subgroupOf H := commutator_le_subgroupOf_Q h hcomm
  -- `lc ∉ 𝒮` means precisely that `lc` is constant on `Q`
  have hnotp : ¬ ∃ x : H, (x : G) ∈ Q ∧ lc x ≠ lc 1 := by
    have h' := hlc'
    simp only [Submission.Blueprint.excludingKernel] at h'
    exact fun hp => not_pred_of_notMem_filter h' (mem_Irr_of_fintype hlc) hp
  have hker : (Q.subgroupOf H : Set H) ⊆ Work.CharCore.charKernel lc := by
    intro x hx
    rw [Work.CharCore.mem_charKernel]
    by_contra hne
    exact hnotp ⟨x, Subgroup.mem_subgroupOf.mp hx, hne⟩
  -- an irreducible character trivial on the commutator subgroup is linear
  have hdeg : Work.CharCore.irrDeg lc = 1 :=
    Work.Clifford.irrDeg_eq_one_of_commutator_le_charKernel (M := Q.subgroupOf H) hM hlc hker
  have h1 : lc 1 = 1 := by
    rw [Work.CharCore.irrDeg_spec hlc, hdeg]
    norm_num
  refine ⟨h1, fun x hx => ?_⟩
  have hmem := hker (show x ∈ (Q.subgroupOf H : Set H) from Subgroup.mem_subgroupOf.mpr hx)
  rw [Work.CharCore.mem_charKernel] at hmem
  rw [hmem, h1]

end Work.ZassenhausPSL2.Feit
