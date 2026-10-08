import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.Lambda
import Submission.Work.BG.s02_quotCyclic
import Submission.Work.GLUE.Defs
import Submission.Work.BG.invJCard
import Submission.Work.BG.lamCF_fixed_eq_neg_one

namespace Work.BG

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## The class of `t₁t₂` generates `H₀/U`

The product `t₁t₂` of the two involutions of `S ∖ S₀` generates the cyclic subgroup `S₀`
(`BGData.gen`), and `H₀ = U ⊔ S₀` with `S₀ ≤ N_G(U)`, so every element of `H₀` is a product
`u · s` with `u ∈ U` and `s ∈ S₀ = ⟨t₁t₂⟩`.  Hence every element of `H₀` is congruent mod `U`
to a power of `t₁t₂`: the class of `t₁t₂` generates the whole quotient `H₀/U`.

This is the group-theoretic input behind the "reflection character" computation of BG §2
(cf. `Work.BG.lamCF_fixed_eq_neg_one`): a linear character of `H₀/U` is determined by its
value at the class of `t₁t₂`.  It is recorded here as a standalone statement, in the form
needed for `Work.BG.lemma22EvalWK_gen`.
-/

/-- **The class of `D.t1 * D.t2` generates `H₀/U`**, for any §2 context `C` compatible
with `D`. -/
theorem quotMk_t1t2_mem_zpowers (D : Work.GW2.BGData G) (C : Sec2Ctx G)
    (hc : Work.GW2.C16.Compat D C) (h : ↥C.P.H0) (hh : (h : G) = D.t1 * D.t2)
    (x : ↥C.P.H0) :
    quotMk C.P x ∈ Subgroup.zpowers (quotMk C.P h) := by
  -- decompose `x = u * s` with `u ∈ U`, `s ∈ S₀`
  obtain ⟨u, hu, s, hs, hus⟩ := LamCFFixed.H0_decomp D C hc x
  -- `s = (t₁t₂)^k` for some `k`, and `t₁t₂ = h`
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (show (s : G) ∈ Subgroup.zpowers (D.t1 * D.t2) by rw [← D.gen]; exact hs)
  have hsg : s = h ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow, hh]
    exact hk.symm
  -- `u` is trivial in the quotient
  have hu1 : quotMk C.P u = 1 :=
    (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) u).mpr hu
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨k, ?_⟩
  rw [← hus, map_mul, hsg, map_zpow, hu1, one_mul]

theorem lemma22EvalWK_gen {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G)
    (C : Work.BG.Sec2Ctx G) (hc : Work.GW2.C16.Compat D C) (h : ↥C.P.H0)
    (hh : (h : G) = D.t1 * D.t2) :
    Subgroup.zpowers (Work.BG.quotMk C.P h) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (C.P.U.subgroupOf C.P.H0) x
  exact quotMk_t1t2_mem_zpowers D C hc h hh y

end Work.BG
