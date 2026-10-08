import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.L27_solvable_base
-- RETIRED STUB (on disk for reference only; NOT on the delivered path): the declaration this
-- module was created for is retired because superseded by the hole-free `Work.CORE2B.L27_solvable_v12`; the retained copy could only be proved from it, which is an import cycle.
-- Its corrected form, the reason, and the counterexample configuration are recorded in the
-- `RETIRED` block below and in `Submission/Work/CORE2B/NOTES_FALSE_L27_solvable_proved.md`.
-- Nothing in the delivered closure of `Work.CORE2B.Proved` / `L27su_assembly` /
-- `L29_lemma_assembly` / `Thm210_assembly` imports this module.

/-!
# CORE2B — `isSolvable_of_commutator_le` (Lemma 2.7 (c) reduction)

The proved reduction used by the delivered proof of Bender 1981 Lemma 2.7 (c): given Lemma 2.7 (a)
`⁅M,t⁆ ≤ F_{π'}(M)` and solvability of `H = C_G(t)`, the subgroup `M` is solvable (via
`M = C_M(t)·F_{π'}(M)`, `F_{π'}(M)` abelian because `t` inverts it pointwise).

This declaration used to live in `Submission/Work/CORE2B/L27_solvable_proved.lean`, which is kept on
disk as a retired stub (its target `L27_solvable_proved` was an unproved placeholder superseded by
`Work.CORE2B.L27_solvable_v12`).  It was moved here so that the retired stub is imported by nothing
on the delivered path.  Consumer: `Submission/Work/CORE2B/L27_v12_assembly.lean`.
-/

namespace Work.CORE2B

open Subgroup
open scoped commutatorElement

set_option linter.unusedVariables false

/-!
# CORE2B — Lemma 2.7 (c): `M` is solvable

Bender 1981, Lemma 2.7, p. 221.  The argument used here:

* `t` inverts `F_{π'}(M) = O_{π'}(F(M))` (step 3 of Bender's proof; proved in the base module from
  Lemma 2.3(ii) `F_{π'}(M) ∩ Ĥ = ⊥` and `C(t) = H ≤ Ĥ`, so that the involution `t` acts
  fixed-point-freely on `F_{π'}(M)`);
* `[M,t] ⊆ F_{π'}(M)` (Lemma 2.7 (a));
* hence every `m ∈ M` can be written `m = c·f` with `c ∈ C_M(t)` and `f ∈ F_{π'}(M)`, because the
  squaring map is a bijection of the odd-order group `F_{π'}(M)`:  `M = C_M(t)·F_{π'}(M)`.

Solvability follows: `F_{2'}(M)` is abelian (an involution inverting a group pointwise forces it to
be abelian), and `C_M(t) ≤ C_G(t) = B.H` is solvable, so `M` is an extension of two solvable
groups.
-/


/-! ## 5. Lemma 2.7 (c) from Lemma 2.7 (a) -/

/-- **Bender 1981, Lemma 2.7 (c)**, given Lemma 2.7 (a) `⁅M,t⁆ ≤ F_{π'}(M)`: `M` is solvable.

`M = C_M(t)·F_{π'}(M)` by the factorization lemma, `F_{π'}(M)` is abelian (it is inverted by `t`)
and `C_M(t) ≤ C_G(t) = B.H` is solvable, so `M` is an extension of two solvable groups. -/
theorem isSolvable_of_commutator_le {G : Type} [Group G] [Finite G]
    (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (M : Subgroup G)
    (hD : L27Hyp B M)
    (hcomm : ⁅M, Subgroup.zpowers B.t⁆ ≤ Work.GW2.fittingPiIn B.piᶜ M)
    (hH : Group.IsSolvable ↥B.H) : Group.IsSolvable ↥M := by
  set X : Subgroup G := Work.GW2.fittingPiIn B.piᶜ M with hXdef
  have hXM : X ≤ M := Subgroup.map_subtype_le _
  have ht2 : B.t * B.t = 1 := by
    have h : B.t ^ 2 = 1 := by
      have := pow_orderOf_eq_one B.t
      rwa [B.t_order] at this
    simpa [pow_two] using h
  have hXn : (X.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr
      (le_normalizer_fittingPiIn_local B.piᶜ M)
  have hXodd : Odd (Nat.card X) := odd_card_fittingPiIn_pi_compl_local h26 hFT hCtx B M
  have hinv : ∀ x ∈ X, B.t * x * B.t⁻¹ = x⁻¹ :=
    inverts_fittingPiIn_pi_compl_local h23 hFT hCtx B M hD
  have hprod := exists_mul_of_mem_of_inverts B.t ht2 M X hXM hXn hXodd hinv hcomm
  -- `F_{π'}(M)` is abelian, hence solvable
  have hXsol : Group.IsSolvable ↥X := by
    refine Group.isSolvable_of_comm (fun a b => ?_)
    exact Subtype.ext (commute_of_forall_inverts B.t X hinv a a.2 b b.2)
  have hX'sol : Group.IsSolvable ↥(X.subgroupOf M) := by
    haveI := hXsol
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hXM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXM).injective
  -- `C_M(t) = C_G(t) ⊓ M` is solvable, being contained in `C_G(t) = B.H`
  have hCsol : Group.IsSolvable ↥(Subgroup.centralizer ({B.t} : Set G) ⊓ M) := by
    haveI : Group.IsSolvable ↥(Subgroup.centralizer ({B.t} : Set G)) := hH
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : Subgroup.centralizer ({B.t} : Set G) ⊓ M
        ≤ Subgroup.centralizer ({B.t} : Set G)))
      (Subgroup.inclusion_injective _)
  -- the quotient `M/X` is a quotient of `C_M(t)`, hence solvable
  have hquot : Group.IsSolvable (↥M ⧸ (X.subgroupOf M)) := by
    haveI : Group.IsSolvable ↥(Subgroup.centralizer ({B.t} : Set G) ⊓ M) := hCsol
    let ψ : ↥(Subgroup.centralizer ({B.t} : Set G) ⊓ M) →* (↥M ⧸ (X.subgroupOf M)) :=
      { toFun := fun c => QuotientGroup.mk' (X.subgroupOf M) (⟨(c : G), c.2.2⟩ : ↥M)
        map_one' := rfl
        map_mul' := fun a b => rfl }
    refine Group.isSolvable_of_surjective (f := ψ) ?_
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (X.subgroupOf M) q
    obtain ⟨c, hc, x, hx, hcx⟩ := hprod m m.2
    have hcM : c ∈ M := by
      have h' : c = ((m : ↥M) : G) * x⁻¹ := by
        calc c = c * x * x⁻¹ := by group
          _ = ((m : ↥M) : G) * x⁻¹ := by rw [hcx]
      rw [h']
      exact M.mul_mem m.2 (M.inv_mem (hXM hx))
    refine ⟨⟨c, hc, hcM⟩, ?_⟩
    show QuotientGroup.mk' (X.subgroupOf M) (⟨c, hcM⟩ : ↥M)
      = QuotientGroup.mk' (X.subgroupOf M) m
    have hx' : (⟨x, hXM hx⟩ : ↥M) ∈ X.subgroupOf M := Subgroup.mem_subgroupOf.mpr hx
    have hm'' : m = (⟨c, hcM⟩ : ↥M) * ⟨x, hXM hx⟩ := Subtype.ext hcx.symm
    have hx1 : (QuotientGroup.mk' (X.subgroupOf M)) (⟨x, hXM hx⟩ : ↥M) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx'
    rw [hm'', map_mul, hx1, mul_one]
  exact Group.isSolvable_of_subgroup_quotient (X.subgroupOf M)


end Work.CORE2B
