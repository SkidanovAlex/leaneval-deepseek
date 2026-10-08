import Mathlib
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.S02
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.rem31StabCard
import Submission.Work.BG.rem31IndexUin
import Submission.OddOrder.GroupTheory.RepresentationTheory.SchurCenterBound
import Submission.OddOrder.GroupTheory.RepresentationTheory.AbsolutelyIrreducible

-- Note (prover): the original stub also imported `Submission.Work.BG.decompBig` and
-- `Submission.Work.BG.s02_lemma21Ext`; neither is used by the proof below, and
-- `decompBig` pulls in `Submission.Work.BG.noThirdExceptional` whose current state does not
-- elaborate, so the two unused imports are dropped to keep this module self-contained.

/-!
# Area BG: the `Λ`-orbit of an irreducible character has `n = |S₀|` elements

`Work.BG.c3OrbitCard` (used by the proof of Theorem C, `|S| ≥ 8`) states: if the cyclic
`2`-group `S₀` centralises the odd group `U` (the extra hypothesis `hcomm`, which holds for
all the BG data arising from a Sylow-`2` dihedral structure and is exactly the §3 hypothesis
`S'` centralises `U` upgraded to `S₀`), then for **every** irreducible character `ν` of
`H₀ = U S₀` the `Λ`-orbit `Λν` has exactly `|Λ| = |H₀ : U| = |S₀| = D.n` elements.

Mathematically: `H₀ = U ⊔ S₀ = U S₀` with `U ⊓ S₀ = 1` and `S₀` commuting with `U`, so
`H₀ = U × S₀` and `S₀ ≤ Z(H₀)`.  Hence (Schur) an irreducible `ν ∈ Irr(H₀)` never vanishes
on `S₀`, while `S₀` maps *onto* `H₀/U`.  Consequently `λ_β ν = ν` forces `β = 1`: the
`Λ`-action is free, its orbits have size `|Λ| = |H₀ : U| = D.n`.

The file also records the auxiliary fact that an irreducible character does not vanish at a
central element (`irreducible_apply_ne_zero_of_mem_center`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {K : Type*}

/-- **An irreducible character never vanishes at a central element.**  By Schur's lemma a
central `z` acts on a witnessing irreducible representation by a scalar, so
`χ(z) · χ(z⁻¹) = χ(1)² ≠ 0`. -/
private theorem irreducible_apply_ne_zero_of_mem_center [Group K] [Finite K]
    {χ : ClassFunction K ℂ} (hχ : IsIrreducibleCharacter χ) {z : K}
    (hz : z ∈ Subgroup.center K) : (χ : K → ℂ) z ≠ 0 := by
  obtain ⟨W, _, _, _, ρ, hirr, hcoe⟩ := hχ
  haveI : Representation.IsIrreducible ρ := hirr
  have hchar := char_mul_char_inv_of_mem_center_complex ρ hz
  intro hz0
  have h0 : (Module.finrank ℂ W : ℂ) ^ 2 = 0 := by
    rw [← hchar, ← congrFun hcoe z, hz0, zero_mul]
  have hfin : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    haveI : Nontrivial W := nontrivial_of_isIrreducible ρ
    exact Nat.cast_ne_zero.mpr (ne_of_gt Module.finrank_pos)
  have hsq : (Module.finrank ℂ W : ℂ) * (Module.finrank ℂ W : ℂ) = 0 := by
    rw [← pow_two]; exact h0
  exact hfin (mul_self_eq_zero.mp hsq)

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem c3OrbitCard {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hDC : Work.GW2.C16.Compat D C)
    (hcomm : ∀ x : G, x ∈ D.S0 → ∀ u : G, u ∈ D.U → x * u = u * x)
    (ν : ClassFunction ↥C.P.H0 ℂ) (hν : IsIrreducibleCharacter ν) :
    (Work.BG.lamOrbit C ν).ncard = D.n := by
  classical
  haveI : Finite ↥C.P.H0 :=
    Finite.of_injective (fun x : ↥C.P.H0 => (x : G)) (fun a b h => Subtype.ext h)
  -- ## (1) two elements of `S₀` commute (it is cyclic)
  have hS0comm : ∀ a b : G, a ∈ D.S0 → b ∈ D.S0 → a * b = b * a := by
    intro a b ha hb
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (by rw [← D.gen]; exact ha)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (by rw [← D.gen]; exact hb)
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  -- ## (2) every element of `S₀` is central in `H₀`
  have hS0_center : ∀ s : ↥C.P.H0, (s : G) ∈ D.S0 → s ∈ Subgroup.center ↥C.P.H0 := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨u, hu, s', hs', hus⟩ := LamCFFixed.H0_decomp D C hDC y
    have huD : (u : G) ∈ D.U := hDC.U_eq ▸ hu
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    have hy : (y : G) = (u : G) * (s' : G) := by rw [← hus, Subgroup.coe_mul]
    rw [hy]
    calc ((u : G) * (s' : G)) * (s : G)
        = (u : G) * ((s' : G) * (s : G)) := by rw [mul_assoc]
      _ = (u : G) * ((s : G) * (s' : G)) := by rw [hS0comm (s' : G) (s : G) hs' hs]
      _ = ((u : G) * (s : G)) * (s' : G) := by rw [mul_assoc]
      _ = ((s : G) * (u : G)) * (s' : G) := by rw [← hcomm (s : G) hs (u : G) huD]
      _ = (s : G) * ((u : G) * (s' : G)) := by rw [mul_assoc]
  -- ## (3) the `Λ`-action is free on `ν`
  have hfree : ∀ β : lamDual C, lamCF C β * ν = ν → β = 1 := by
    intro β hβ
    refine MonoidHom.ext fun z => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.P.U.subgroupOf C.P.H0) z
    obtain ⟨u, hu, s, hs, hus⟩ := LamCFFixed.H0_decomp D C hDC x
    have hu1 : quotMk C.P u = 1 :=
      (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) u).mpr hu
    have hπ : quotMk C.P x = quotMk C.P s := by rw [← hus, map_mul, hu1, one_mul]
    rw [hπ]
    -- evaluate `λ_β · ν = ν` at the central element `s`
    have hsval := congrArg (fun f : ClassFunction ↥C.P.H0 ℂ => f s) hβ
    simp only [ClassFunction.mul_apply] at hsval
    rw [lamCF_apply] at hsval
    have hνs : ν s ≠ 0 := irreducible_apply_ne_zero_of_mem_center hν (hS0_center s hs)
    have hval : ((β (quotMk C.P s) : ℂˣ) : ℂ) = 1 := by
      have h2 : ((β (quotMk C.P s) : ℂˣ) : ℂ) * ν s = 1 * ν s := by rw [hsval, one_mul]
      exact mul_right_cancel₀ hνs h2
    exact Units.ext (by simpa using hval)
  -- ## (4) the stabiliser is trivial, hence `|Λν| = |Λ| = |H₀ : U| = D.n`
  have hstab : Nat.card ↥(lamStab C ν) = 1 := by
    rw [Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
    intro β hβ
    exact hfree β ((mem_lamStab C ν β).mp hβ)
  have h := rem31StabCard C ν
  rw [hstab, one_mul] at h
  rw [h, rem31IndexUin D C hDC]

end Work.BG
