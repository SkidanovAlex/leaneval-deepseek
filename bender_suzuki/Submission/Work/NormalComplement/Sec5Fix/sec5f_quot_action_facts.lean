/-
# `Work.NormalComplement.Sec5Fix.sec5f_quot_action_facts`

The action facts for Peterfalvi I Ch. III §5 Prop. 2 (a): with `H` strongly embedded, `t ∉ H` an
involution, `V = centD H t`, `𝒩 = N_G(V)` and `KK` the kernel of the action of `𝒩` on
`Ω_V = fixedPts H V`, the quotient `𝒩 ⧸ KK` acts on `Ω_V`

* pretransitively and 2-transitively;
* faithfully;
* with point stabiliser (of the base point `H`) that is strongly embedded and a coatom of
  `𝒩 ⧸ KK`.

These are exactly the hypotheses of `Work.NormalComplement.AppIIIProp` (Peterfalvi I Appendix III
(2)–(5)) applied to the action of `𝒩 ⧸ KK` on `Ω_V`.

Mathematical content.

* 2-transitivity of `𝒩 = N_G(V)` on `Ω_V` is Ch. II §4 Prop. 3 (`Work.ThreePoints.p3pkg` at
  `X = V = centD H t` with the subnormal `Y = A`); it transfers to `𝒩 ⧸ KK` because the action of
  the quotient is by definition the action of `𝒩` (`Sec5f.quotient_smul_mk`).
* Faithfulness is the definition of `KK` (`Work.NormalComplement.Sec5Fix.P2a.faithful_Nq`).
* The point stabiliser of `H` in `𝒩` is `𝒩 ⊓ H`, and the point stabiliser of `H` in `𝒩 ⧸ KK` is
  its image (`Sec5f.stabilizer_ptV_quot`).  The subgroup `𝒩 ⊓ H` is strongly embedded in `𝒩`
  (Ch. I §1 (6), `Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf`): it is proper because
  `t ∈ 𝒩` (`P2a.mem_NNg_t`) and `t ∉ H`; it has even order because, by Ch. II §4 Prop. 3 above, a
  *nontrivial* Sylow `2`-subgroup `S` of `F ⊓ H` (`F = O^{2'}(C_G(V))`) satisfies
  `S ≤ F ⊓ H ≤ 𝒩 ⊓ H` (and `|Ω_V| = |S| + 1 ≥ 3`); and `(𝒩 ⊓ H) ⊓ (𝒩 ⊓ H)^g ≤ H ⊓ H^g` has odd
  order for `g ∈ 𝒩 ∖ H`.  Strong embeddedness descends to `𝒩 ⧸ KK` because `KK ≤ 𝒩 ⊓ H` has odd
  order (`P2a.odd_card_KK`): this is `Work.NormalComplement.isStronglyEmbedded_map_of_surjective`.
* Finally, a 2-transitive action of a group on a nontrivial set has maximal point stabilisers
  (`MulAction.isPreprimitive_of_is_two_pretransitive` and
  `MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive`).
-/
import Mathlib
import Submission.Work.NormalComplement.sec5f_setup
import Submission.Work.NormalComplement.Sec5Fix.P2a.Basic
import Submission.Work.NormalComplement.sec5_prop2a

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Classical
open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.Sec5Fix

variable {G : Type} [Group G] [Finite G]

/-! ## Two elementary consequences of the configuration -/

/-- **`|𝒩 ⊓ H|` is even**, where `𝒩 = N_G(V)`, `V = centD H t`.

By Ch. II §4 Prop. 3 (`Work.NormalComplement.p2a_p3_data`) there is a Sylow `2`-subgroup `S` of
`F ⊓ H` (`F = O^{2'}(C_G(V))`) with `|Ω_V| = |S| + 1`; since `|Ω_V| ≥ 3`
(`Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD`), `S` is nontrivial, and
`S ≤ F ⊓ H ≤ 𝒩 ⊓ H` because `F ≤ N_G(V)`. -/
theorem NN_inf_H_even (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ}
    {P A : Subgroup G} {r : ℕ} (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    Even (Nat.card ↥(Work.NormalComplement.Sec5f.NN H t ⊓ H)) := by
  obtain ⟨S, hSpg, hSle, -, -, -, -, hcardS⟩ := Work.NormalComplement.p2a_p3_data hFT hC h
  have h3 : 3 ≤ (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard :=
    Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD h.se h.invol h.notMem le_rfl
  have hS2 : 2 ≤ Nat.card ↥S := by
    rw [Work.NormalComplement.p2a_natCard_sub_eq_ncard S]
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSle' : S ≤ Work.NormalComplement.Sec5f.NN H t ⊓ H :=
    le_inf ((hSle.trans inf_le_left).trans (Work.ThreePoints.p3F_le_normalizer _))
      (hSle.trans inf_le_right)
  have h1 : 2 ∣ Nat.card ↥S := by
    obtain ⟨k, hk⟩ := hSpg.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [hk] at hS2
      norm_num at hS2
    rw [hk]
    exact dvd_pow_self 2 hk0
  exact even_iff_two_dvd.mpr (h1.trans (Subgroup.card_dvd_of_le hSle'))

/-! ## Transfer of transitivity to a quotient acting with the same orbits -/

/-- If `φ : M →* N` is a homomorphism and the action of `N` on `α` is the action of `M` composed
with `φ` (`φ m • a = m • a`), then `k`-transitivity of `M` transfers to `N`. -/
theorem isMultiplyPretransitive_of_smul_eq {M N α : Type*} [Group M] [Group N]
    [MulAction M α] [MulAction N α] (φ : M →* N)
    (hsmul : ∀ (m : M) (a : α), φ m • a = m • a) {k : ℕ}
    (h : MulAction.IsMultiplyPretransitive M α k) :
    MulAction.IsMultiplyPretransitive N α k := by
  rw [MulAction.isMultiplyPretransitive_iff] at h ⊢
  intro x y
  obtain ⟨m, hm⟩ := h x y
  refine ⟨φ m, ?_⟩
  ext i
  have h2 : (m • x) i = y i := congrArg (fun f : Fin k ↪ α => f i) hm
  rw [Function.Embedding.smul_apply, ← hsmul m (x i)] at h2
  rw [Function.Embedding.smul_apply]
  exact h2

/-- If `φ : M →* N` is a homomorphism and the action of `N` on `α` is the action of `M` composed
with `φ`, then pretransitivity transfers from `M` to `N`. -/
theorem isPretransitive_of_smul_eq {M N α : Type*} [Group M] [Group N]
    [MulAction M α] [MulAction N α] (φ : M →* N)
    (hsmul : ∀ (m : M) (a : α), φ m • a = m • a)
    (h : MulAction.IsPretransitive M α) :
    MulAction.IsPretransitive N α := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨m, hm⟩ := h.exists_smul_eq a b
  exact ⟨φ m, by rw [hsmul, hm]⟩

/-! ## The action facts -/

theorem sec5f_quot_action_facts (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) :
    MulAction.IsPretransitive (↥(Work.NormalComplement.Sec5f.NN H t)
        ⧸ Work.NormalComplement.Sec5f.KK H t) (Work.NormalComplement.Sec5f.Omega H t) ∧
      MulAction.IsMultiplyPretransitive (↥(Work.NormalComplement.Sec5f.NN H t)
        ⧸ Work.NormalComplement.Sec5f.KK H t) (Work.NormalComplement.Sec5f.Omega H t) 2 ∧
      (∀ g : ↥(Work.NormalComplement.Sec5f.NN H t) ⧸ Work.NormalComplement.Sec5f.KK H t,
        (∀ ω : Work.NormalComplement.Sec5f.Omega H t, g • ω = ω) → g = 1) ∧
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded
        (MulAction.stabilizer (↥(Work.NormalComplement.Sec5f.NN H t)
          ⧸ Work.NormalComplement.Sec5f.KK H t) (Work.NormalComplement.Sec5f.ptV H t)) ∧
      IsCoatom
        (MulAction.stabilizer (↥(Work.NormalComplement.Sec5f.NN H t)
          ⧸ Work.NormalComplement.Sec5f.KK H t) (Work.NormalComplement.Sec5f.ptV H t)) := by
  classical
  -- `t ∈ 𝒩`, and `|𝒩 ⊓ H|` is even
  have htNN : t ∈ Work.NormalComplement.Sec5f.NN H t := P2a.mem_NNg_t H t
  have heven : Even (Nat.card ↥(Work.NormalComplement.Sec5f.NN H t ⊓ H)) :=
    NN_inf_H_even hFT hC h
  -- ## Ch. II §4 Prop. 3 at `X = V = centD H t` (with the subnormal `Y = A`)
  have hBrSz : Submission.Blueprint.BrauerSuzukiProp := Work.BrauerSuzuki.brauerSuzuki
  have hZJ : Submission.Blueprint.GlaubermanZJProp := Work.ThmF.ChV12.glaubermanZJ_free
  have hA : Submission.Blueprint.ThmAProp := Work.DoubleTransitivity.Sec7.ThmA hFT hZJ hBrSz
  have hMod : Submission.Blueprint.ModelFactsProp := Work.Models.models hFT
  have hPkg : Work.ThreePoints.P3Pkg H t (Submission.Blueprint.centD H t) :=
    Work.ThreePoints.p3pkg hFT hC hA hZJ hBrSz hMod h.sit h.se h.invol h.notMem
      (Submission.Blueprint.centD H t) le_rfl
      ⟨A, h.A_ne, Work.NormalComplement.p2a_IsSubnormalIn_A_V h,
        Work.NormalComplement.p2a_HasNonTrivialNK_A h⟩
  -- ## `𝒩` acts 2-transitively (hence transitively) on `Ω_V`
  have h2t_NN : MulAction.IsMultiplyPretransitive ↥(Work.NormalComplement.Sec5f.NN H t)
      (Work.NormalComplement.Sec5f.Omega H t) 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨y, hy, hyac, hybd⟩ := hPkg.2 (a : G ⧸ H) a.2 (b : G ⧸ H) b.2
      (fun hcon => hab (Subtype.ext hcon)) (c : G ⧸ H) c.2 (d : G ⧸ H) d.2
      (fun hcon => hcd (Subtype.ext hcon))
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyac), Subtype.ext (by simpa using hybd)⟩
  have hpre_NN : MulAction.IsPretransitive ↥(Work.NormalComplement.Sec5f.NN H t)
      (Work.NormalComplement.Sec5f.Omega H t) := by
    have htr := hPkg.2.isTransitiveOnSub
    refine ⟨fun a b => ?_⟩
    obtain ⟨y, hy, hyab⟩ := htr (a : G ⧸ H) a.2 (b : G ⧸ H) b.2
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyab)⟩
  -- ## transfer to `𝒩 ⧸ KK`
  have h2t_Nq : MulAction.IsMultiplyPretransitive
      (↥(Work.NormalComplement.Sec5f.NN H t) ⧸ Work.NormalComplement.Sec5f.KK H t)
      (Work.NormalComplement.Sec5f.Omega H t) 2 :=
    isMultiplyPretransitive_of_smul_eq (M := ↥(Work.NormalComplement.Sec5f.NN H t))
      (N := ↥(Work.NormalComplement.Sec5f.NN H t) ⧸ Work.NormalComplement.Sec5f.KK H t)
      (α := Work.NormalComplement.Sec5f.Omega H t)
      (QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t))
      (fun n ω => Sec5f.quotient_smul_mk n ω) h2t_NN
  have hpre_Nq : MulAction.IsPretransitive
      (↥(Work.NormalComplement.Sec5f.NN H t) ⧸ Work.NormalComplement.Sec5f.KK H t)
      (Work.NormalComplement.Sec5f.Omega H t) :=
    isPretransitive_of_smul_eq (M := ↥(Work.NormalComplement.Sec5f.NN H t))
      (N := ↥(Work.NormalComplement.Sec5f.NN H t) ⧸ Work.NormalComplement.Sec5f.KK H t)
      (QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t))
      (fun n ω => Sec5f.quotient_smul_mk n ω) hpre_NN
  refine ⟨hpre_Nq, h2t_Nq, P2a.faithful_Nq H t, ?_, ?_⟩
  · -- ## the point stabiliser of `H` is strongly embedded in `𝒩 ⧸ KK`
    rw [Sec5f.stabilizer_ptV_quot]
    refine Work.NormalComplement.isStronglyEmbedded_map_of_surjective
      (QuotientGroup.mk' (Work.NormalComplement.Sec5f.KK H t))
      (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' (Work.NormalComplement.Sec5f.KK H t))
      (P2a.odd_card_KK h.se h.notMem)
      (Sec5f.KK_le_subgroupOf (H := H) (t := t)) ?_
    -- `𝒩 ⊓ H` is strongly embedded in `𝒩` (Ch. I §1 (6))
    refine Work.ThreePoints.IsStronglyEmbedded.subgroupOf_inf h.se ?_ heven
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact h.notMem (Subgroup.mem_inf.mp (htop htNN)).2
  · -- ## the point stabiliser of `H` is a coatom of `𝒩 ⧸ KK`
    haveI : Nontrivial (Work.NormalComplement.Sec5f.Omega H t) :=
      ⟨Sec5f.ptV H t, Sec5f.pttV H t, fun hcon =>
        Work.ThreePoints.P3Sub.mk_one_ne_mk_t h.notMem (congrArg Subtype.val hcon)⟩
    haveI : MulAction.IsPreprimitive
        (↥(Work.NormalComplement.Sec5f.NN H t) ⧸ Work.NormalComplement.Sec5f.KK H t)
        (Work.NormalComplement.Sec5f.Omega H t) :=
      MulAction.isPreprimitive_of_is_two_pretransitive h2t_Nq
    exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive _ (Sec5f.ptV H t)

end Work.NormalComplement.Sec5Fix
