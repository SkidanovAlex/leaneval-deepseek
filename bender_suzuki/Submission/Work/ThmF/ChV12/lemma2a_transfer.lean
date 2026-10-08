import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.lemma2a_transfer`

Ch. V §2, Lemma 2(a) — the *transfer* step (Peterfalvi II, p. 243).

Let `H ≤ G` and `X ≤ H` be subgroups of a finite group `G`, and put `C = C_G(X)`.
The centraliser `C` acts on the set `Ω = G ⧸ H` of conjugates of `H` by left translation,
and the points fixed by `X` are `S = fixedPts H X = {ω | ∀ x ∈ X, x • ω = ω}` (the conjugates
of `H` containing `X`).  The hypothesis of the lemma is that `C` acts **2-transitively** on `S`.

The conclusion is that `C` acts 2-transitively on the coset space `C / (C ∩ H)`.

Mathematically: every element of `C` commutes with `X`, so `C` preserves `S`; also `S` is the
orbit of the base point `H ∈ S` (as `X ≤ H`).  Hence the orbit–stabiliser theorem produces a
`C`-equivariant bijection

`φ : C / (C ∩ H) → S`,  `φ (c (C ∩ H)) = c • H`,

with `Stab_C(H) = C ∩ H`; 2-transitivity of `C` on `S` transfers to the coset space along `φ`.
The proof below constructs `φ` explicitly (`hwf`, `φ`, `φ_mk`, `φ_smul`, `φ_inj`, `φ_mem`) and
then transports a pair of points using `MulAction.is_two_pretransitive_iff`.  In particular no
finiteness and no structure theory of `H` are used.
-/

set_option autoImplicit false

open Work.DoubleTransitivity Submission.Blueprint

namespace Work.ThmF.ChV12

theorem lemma2a_transfer {G : Type} [Group G] [Finite G] (H X : Subgroup G) (hXH : X ≤ H) (h2 : Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.centralizer (X : Set G)) (Submission.Blueprint.fixedPts H X)) : MulAction.IsMultiplyPretransitive ↥(Subgroup.centralizer (X : Set G)) (↥(Subgroup.centralizer (X : Set G)) ⧸ (H ⊓ Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.centralizer (X : Set G))) 2 := by
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  let K : Subgroup C := (H ⊓ C).subgroupOf C
  let a0 : G ⧸ H := Work.DoubleTransitivity.pt H
  -- `c₁ (C ∩ H) = c₂ (C ∩ H)` implies `c₁ • H = c₂ • H`: this is the well-definedness of `φ`.
  have hwf : ∀ c₁ c₂ : C, QuotientGroup.leftRel K c₁ c₂ → (c₁ : G) • a0 = (c₂ : G) • a0 := by
    intro c₁ c₂ h
    rw [QuotientGroup.leftRel_apply] at h
    have hHC : ((c₁⁻¹ * c₂ : C) : G) ∈ H ⊓ C := Subgroup.mem_subgroupOf.mp h
    have hH : ((c₁ : G))⁻¹ * (c₂ : G) ∈ H := by
      have := hHC.1
      simpa using this
    have hfix : ((c₁ : G)⁻¹ * (c₂ : G)) • a0 = a0 := by
      rw [show a0 = Work.DoubleTransitivity.pt H from rfl, Work.DoubleTransitivity.smul_pt]
      exact Work.DoubleTransitivity.mk_one_eq_iff.mpr hH
    calc (c₁ : G) • a0 = (c₁ : G) • (((c₁ : G)⁻¹ * (c₂ : G)) • a0) := by rw [hfix]
      _ = ((c₁ : G) * ((c₁ : G)⁻¹ * (c₂ : G))) • a0 := by rw [smul_smul]
      _ = (c₂ : G) • a0 := by rw [mul_inv_cancel_left]
  -- The orbit–stabiliser map `φ : C/(C ∩ H) → Ω`, `φ (c (C ∩ H)) = c • H`.
  let φ : C ⧸ K → G ⧸ H := fun z => Quotient.liftOn' z (fun c : C => (c : G) • a0) hwf
  have φ_mk : ∀ c : C, φ (QuotientGroup.mk c) = (c : G) • a0 := fun c => rfl
  have φ_smul : ∀ (g : C) (z : C ⧸ K), φ (g • z) = (g : G) • φ z := by
    intro g z
    induction z using Quotient.inductionOn' with
    | h c =>
      simp only [φ_mk]
      rw [show g • (QuotientGroup.mk c) = QuotientGroup.mk (g * c) from rfl, φ_mk, smul_smul]
      rfl
  have φ_inj : Function.Injective φ := by
    intro z₁ z₂ h
    induction z₁ using Quotient.inductionOn' with
    | h c₁ =>
    induction z₂ using Quotient.inductionOn' with
    | h c₂ =>
      rw [φ_mk, φ_mk] at h
      have hfix : ((c₁ : G)⁻¹ * (c₂ : G)) • a0 = a0 := by
        rw [← smul_smul, ← h]
        exact inv_smul_smul _ _
      have hmem : ((c₁ : G)⁻¹ * (c₂ : G)) ∈ H := by
        rw [← Work.DoubleTransitivity.mk_one_eq_iff]
        rw [← Work.DoubleTransitivity.smul_pt]
        exact hfix
      refine Quotient.sound' (QuotientGroup.leftRel_apply.mpr ?_)
      rw [Subgroup.mem_subgroupOf]
      exact ⟨by simpa using hmem, (c₁⁻¹ * c₂).2⟩
  -- `φ` lands in the set `S` fixed by `X`.
  have φ_mem : ∀ z : C ⧸ K, φ z ∈ Submission.Blueprint.fixedPts H X := by
    intro z
    induction z using Quotient.inductionOn' with
    | h c =>
      rw [φ_mk]
      intro x hx
      have hcomm : x * (c : G) = (c : G) * x := Subgroup.mem_centralizer_iff.mp c.2 x hx
      rw [smul_smul, hcomm, ← smul_smul]
      congr 1
      rw [show a0 = Work.DoubleTransitivity.pt H from rfl, Work.DoubleTransitivity.smul_pt]
      exact Work.DoubleTransitivity.mk_one_eq_iff.mpr (hXH hx)
  -- Transfer 2-transitivity of `C` on `S` to the coset space `C / (C ∩ H)` along `φ`.
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨g, hgC, hgac, hgbd⟩ :=
    h2 (φ a) (φ_mem a) (φ b) (φ_mem b) (fun h => hab (φ_inj h))
       (φ c) (φ_mem c) (φ d) (φ_mem d) (fun h => hcd (φ_inj h))
  refine ⟨⟨g, hgC⟩, ?_, ?_⟩
  · apply φ_inj
    rw [φ_smul]
    exact hgac
  · apply φ_inj
    rw [φ_smul]
    exact hgbd

end Work.ThmF.ChV12
