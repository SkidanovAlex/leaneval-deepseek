import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3NeBot.p3b_glue

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

/-- Peterfalvi I Ch. II §4 Prop. 3 (b) (p. 170), in the special case `X ≤ W = C_V(K)` that
Prop. 4 (b) needs.  Under (B0)–(B2), for a strongly embedded `H`, an involution `t ∉ H`,
`D = H ∩ H^t`, `V = C_D(t)`, `K = J(D,t)` (so `|K| = |Inv H| ≥ 2`), and a subgroup `X ≤ V` with
`X ⊆ C(K)` and `X ≠ 1`: there is a `2`-subgroup `S ≤ N_H(X)` with `N_H(X) = S ⋊ N_D(X)`,
`S ⊴ N_H(X)`.

This is the weakened form of the area owner's `Work.ThreePoints.sec4_prop3_ab` (Prop. 3 (a),(b))
that Prop. 4 (b) consumes: the factorisation `N_G(X) = F·N_V(X)` and the extra properties
`S ≤ F ⊓ H`, `¬ 2 ∣ (S.subgroupOf (F ⊓ H)).index` of the Sylow `2`-subgroup there are dropped.

IMPORTANT: an independent proof is needed.  Importing `Submission.Work.ThreePoints.sec4_prop3_ab`
(a file which still contains `hole`) would make the proof depend on `holeAx` and fail
`declare_proven`; if that file has become hole-free by the time you read this, deriving the
statement from it is fine.

Source proof (Prop. 3, part 1, pp. 170-171, in the case `N_K(X) ≠ 1`, which holds here since
`X ≤ C(K)` gives `K ⊆ C_G(X) ⊆ N_G(X)`): put `F = O^{2'}(C_G(X))`; by Prop. 1 (a),(b) (see
`Work.ThreePoints.prop1a_of_involution_normalizing` and
`Work.ThreePoints.stronglyEmbedded_subgroupOf_inf_conj`) and Ch. I §2 Lemma 2, `F` acts doubly
transitively on `Ω_X` with `N_G(X) = F·N_V(X)`; by `(B1)` (`hS`) applied to the proper subgroup
`F`, and Prop. 2 (c) + Lemma 1, one gets `O_{2'}(F) = Z(F)` and `F/Z(F) ≅ PSL(2,q)`, `Sz(q)` or
`PSU(3,q)`; the structure `F ∩ H = S ⋊ (F ∩ D)` of the Borel of that model (`hMod`,
`ModelFactsProp`) lifts to `N_H(X) = S ⋊ N_D(X)` with `S` a normal `2`-Sylow of `F ∩ H`. -/
theorem prop3b_normal_sylow {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) (X : Subgroup G)
    (hXV : X ≤ Submission.Blueprint.centD H t)
    (hXK : X ≤ Subgroup.centralizer (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t))
    (hX0 : X ≠ ⊥)
    (hKne : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ H ∧
      S ≤ Subgroup.normalizer (X : Set G) ∧
      H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (S : Set G) ∧
      S ⊓ Submission.Blueprint.twoPoint H t = ⊥ ∧
      S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
        H ⊓ Subgroup.normalizer (X : Set G) := by
  -- `X ≤ C(K)` and `K ≠ 1` give `N_K(X) ≠ 1`: `K ≤ C_G(X) ≤ N_G(X)`.
  have hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
      k ≠ 1 ∧ k ∈ Subgroup.normalizer (X : Set G) := by
    obtain ⟨k, hkK, hkne⟩ := hKne
    refine ⟨k, hkK, hkne, ?_⟩
    have hkc : ∀ y ∈ (X : Set G), y * k = k * y := by
      intro y hy
      have h1 : k * y = y * k := Subgroup.mem_centralizer_iff.mp (hXK hy) k hkK
      exact h1.symm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h2 : k * y * k⁻¹ = y := by rw [← hkc y hy]; group
      rw [h2]; exact hy
    · intro hy
      have h2 : y = k * y * k⁻¹ := by
        have h1 : (k * y * k⁻¹) * k = k * (k * y * k⁻¹) := hkc _ hy
        calc y = k⁻¹ * ((k * y * k⁻¹) * k) := by group
          _ = k⁻¹ * (k * (k * y * k⁻¹)) := by rw [h1]
          _ = k * y * k⁻¹ := by group
      rw [h2]; exact hy
  -- Prop. 3 (b) for `X ≠ ⊥` (`P3NeBot.p3b_glue.p3_b_proof`); only its `∃ S`-clause is used.
  obtain ⟨S, hS2, hSleFH, -, hSnorm, hSD, hSsup⟩ :=
    P3NeBot.p3_b_proof hFT hC hA hZJ hBrSz hMod hS hH ht htH hX0 hXV hNX
  refine ⟨S, hS2, hSleFH.trans inf_le_right, ?_, hSnorm, hSD, hSsup⟩
  -- `S ≤ F ⊓ H ≤ F = O^{2'}(C_G(X)) ≤ C_G(X) ≤ N_G(X)`
  exact (hSleFH.trans inf_le_left).trans
    ((p3F_le_centralizer X).trans (Subgroup.centralizer_le_normalizer (X : Set G)))

end Work.ThreePoints
