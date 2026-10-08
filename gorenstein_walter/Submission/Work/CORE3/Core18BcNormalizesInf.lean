import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aFrattiniApi

namespace Work.CORE3

namespace Work.CORE3

open Subgroup
open Work.GW2

/-! ### Elementary normalizer bookkeeping

These three lemmas are the only group theory used below: an element of `G` normalizing `A` and
`C` normalizes `A ⊓ C` and `A ⊔ C`, and `x` normalizes `K^n` exactly when `n⁻¹ x n` normalizes
`K`. -/

section Core18BcHelpers

variable {G : Type*} [Group G]

/-- An element normalizing two subgroups normalizes their intersection. -/
lemma c18bc_normalizer_inf {A C : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hC : x ∈ Subgroup.normalizer (C : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hC ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨(hA y).mp h.1, (hC y).mp h.2⟩,
    fun h => ⟨(hA y).mpr h.1, (hC y).mpr h.2⟩⟩

/-- An element normalizing two subgroups normalizes their join. -/
lemma c18bc_normalizer_sup {A C : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hC : x ∈ Subgroup.normalizer (C : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hC ⊢
  rw [Subgroup.map_sup, hA, hC]

/-- `x` normalizes `K^g` if and only if `g⁻¹ x g` normalizes `K`. -/
lemma c18bc_mem_normalizer_conjSub {K : Subgroup G} {g x : G} :
    x ∈ Subgroup.normalizer (conjSub g K : Set G) ↔
      g⁻¹ * x * g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h z
    have h1 := h (g * z * g⁻¹)
    simp only [Work.CORE2A.mem_conjSub_iff] at h1
    have h2 : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    have h3 : g⁻¹ * (x * (g * z * g⁻¹) * x⁻¹) * g
        = (g⁻¹ * x * g) * z * (g⁻¹ * x * g)⁻¹ := by group
    rw [h2, h3] at h1
    exact h1
  · intro h y
    rw [Work.CORE2A.mem_conjSub_iff, Work.CORE2A.mem_conjSub_iff]
    rw [show g⁻¹ * (x * y * x⁻¹) * g
        = (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ by group]
    exact h (g⁻¹ * y * g)

end Core18BcHelpers

/-- GW design pass 18, item B, leaf B2a: `B = C_U(S)` normalizes `(P ⊔ P^n) ⊓ B` for
`n ∈ N_G(V₁)`, where `P = O_p(U)` and `V₁ = ⟨t, t₁⟩ ≤ S`.

Sketch (0.1–0.2k): `B ≤ C_G(V₁)` (as `B` centralizes `S ⊇ V₁`), and `C_G(V₁) ≤ C_G(t) = H`,
which normalizes `U` and hence `P` (`Work.CORE2A.bSetup_H_le_normalizer_U`,
`Work.CORE3.c1aLe_normalizer_pCoreIn`, which needs `haveI : Fact D.p.Prime := ⟨D.hp⟩`).
For `b ∈ B`, `n⁻¹ b n ∈ C_G(V₁)` because `n` normalizes `V₁` hence also `C_G(V₁)`; so `b`
normalizes `P^n = n P n⁻¹`.  Thus `b` normalizes `P`, `P^n`, their join and `B` itself, hence
their intersection (elementwise via `Subgroup.mem_normalizer_iff`; for the join use
`Subgroup.map_sup` of `MulAut.conj b`). -/
theorem Core18BcNormalizesInf (G : Type) [Group G] [Finite G] (B : BenderSetup G)
    (D : Case1aData B) (n : G) (hn : n ∈ normalizer ((V1 B D : Subgroup G) : Set G)) :
    B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) ≤
      normalizer (((pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U)) ⊓
        (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) : Subgroup G) : Set G) := by
  haveI : Fact D.p.Prime := ⟨D.hp⟩
  -- `V₁ = ⟨t, t₁⟩ ≤ S`, and `t ∈ V₁`
  have hV1S : V1 B D ≤ (B.S : Subgroup G) := by
    rw [V1]
    exact sup_le (Subgroup.zpowers_le.mpr (B.S0_le B.t_mem))
      (Subgroup.zpowers_le.mpr D.t1_mem)
  have htV1 : ({B.t} : Set G) ⊆ (V1 B D : Set G) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t)
  intro b hb
  have hbC : b ∈ centralizer ((B.S : Subgroup G) : Set G) := (Subgroup.mem_inf.mp hb).2
  -- `b` centralizes `V₁ ⊆ S`, hence lies in `H = C_G(t)`, hence normalizes `P = O_p(U)`
  have hbCV1 : b ∈ centralizer ((V1 B D : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (fun x hx => hV1S hx) hbC
  have hbH : b ∈ B.H := Subgroup.centralizer_le htV1 hbCV1
  have hbNP : b ∈ Subgroup.normalizer (pCoreIn D.p B.U : Set G) :=
    H_le_normalizer_P B D.p hbH
  -- `n` normalizes `V₁`, so conjugation by `n` preserves `C_G(V₁)`: `n⁻¹ b n ∈ C_G(V₁) ≤ H`
  have hconjCV1 : n⁻¹ * b * n ∈ centralizer ((V1 B D : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hbCV1 ⊢
    intro v hv
    have hnvn : n * v * n⁻¹ ∈ V1 B D := (Subgroup.mem_normalizer_iff.mp hn v).mp hv
    have hcomm : (n * v * n⁻¹) * b = b * (n * v * n⁻¹) := hbCV1 _ hnvn
    calc v * (n⁻¹ * b * n) = n⁻¹ * ((n * v * n⁻¹) * b) * n := by group
      _ = n⁻¹ * (b * (n * v * n⁻¹)) * n := by rw [hcomm]
      _ = (n⁻¹ * b * n) * v := by group
  have hconjH : n⁻¹ * b * n ∈ B.H := Subgroup.centralizer_le htV1 hconjCV1
  have hbNPn : b ∈ Subgroup.normalizer (conjSub n (pCoreIn D.p B.U) : Set G) :=
    c18bc_mem_normalizer_conjSub.mpr (H_le_normalizer_P B D.p hconjH)
  -- `b` normalizes `P`, `P^n`, the join `P ⊔ P^n` and `B = C_U(S)`, hence their intersection
  have hbNsup : b ∈ Subgroup.normalizer
      ((pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U) : Subgroup G) : Set G) :=
    c18bc_normalizer_sup hbNP hbNPn
  have hbNQ : b ∈ Subgroup.normalizer
      ((B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hb
  exact c18bc_normalizer_inf hbNsup hbNQ

end Work.CORE3

open Subgroup
open Work.GW2

/-- The same theorem, stated at the namespace of the file path, so that it can be cited both as
`Work.CORE3.Core18BcNormalizesInf` (the name the area requests) and as
`Work.CORE3.Work.CORE3.Core18BcNormalizesInf` (the skeleton's namespace layout). -/
theorem Core18BcNormalizesInf (G : Type) [Group G] [Finite G] (B : BenderSetup G)
    (D : Case1aData B) (n : G) (hn : n ∈ normalizer ((V1 B D : Subgroup G) : Set G)) :
    B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) ≤
      normalizer (((pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U)) ⊓
        (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) : Subgroup G) : Set G) :=
  _root_.Work.CORE3.Work.CORE3.Core18BcNormalizesInf G B D n hn

end Work.CORE3
