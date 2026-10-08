import Mathlib
import Submission.Work.BG.lemma36Defs
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.kerLeOfMulAutInv
import Submission.Work.BG.orbitCardAux
import Submission.Work.BG.glauberman_two
import Submission.Work.BG.ocm.card_lamOrbitOfU_eq_inner
import Submission.Work.BG.ocm.inertia_eq_sup
import Submission.Work.BG.ocm.card_inertia_inf_S0_eq
import Submission.Work.BG.ocm.sStab_le_S0

/-!
# `Work.BG.orbitCardMul` — the orbit product `|S·a| · |Λ(a)| = 2 |S₀|`

Bender–Glauberman 1981, §3 (the repaired route to Lemma 3.6, see
`Submission/Work/BG/NOTES_lemma36_plan.md` §1(b)): for `a ∈ Irr(U)` not trivial on `K`, the
`S`-orbit `Σ_S(a)` of `a` in `Irr(U)` and the `Λ`-orbit `Λ(a)` of `a` (the set of `ν ∈ Irr(H₀)`
with `a` a constituent of `ν|_U`, BG Remark 3.1) satisfy

  `|Σ_S(a)| · |Λ(a)| = 2 · D.n`.

The proof has four independent inputs, three of which are proved in sibling modules:

* `Work.BG.ocm.card_lamOrbitOfU_eq_inner` — `|Λ(a)| = ‖Ind_U^{H₀} a‖²` (Frobenius reciprocity +
  the multiplicity-one shape `Work.BG.rem31Shape`);
* `Work.BG.ocm.inertia_eq_sup` and `Work.BG.card_inertia_eq` — the inertia group of `a` in `H₀`
  is `U ⊔ (I ∩ S₀)`, whence `|I| = |U|·|I ∩ S₀|`;
* `Work.BG.ocm.card_inertia_inf_S0_eq` — `|I ∩ S₀|` is the cardinality of the `S₀`-stabiliser of
  `a` (the two conjugation actions agree);
* `Work.BG.ocm.sStab_le_S0` — every element of `S ∖ S₀` inverts `K`, so a `K`-nontrivial `a` is
  fixed only by elements of `S₀` (piece A, `Work.BG.kerLeOfMulAutInv`).

Together with `Work.BG.sOrbitU_card_mul_sStab_card` (orbit–stabiliser, in `orbitCardAux`) and
`|S| = 2 · D.n` (`D.dih`), this gives the result.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- For subgroups `H, K` of a group with `H` normal and `H ⊓ K = ⊥`, the product of the
cardinalities is the cardinality of the join: `|H ⊔ K| = |H|·|K|` (the multiplication map
`H × K → H ⊔ K` is a bijection, injectivity using `H ⊓ K = ⊥` and surjectivity using
`Subgroup.mem_sup_of_normal_left`). -/
theorem card_sup_mul_card_of_inf_eq_bot {X : Type} [Group X] {H K : Subgroup X} [H.Normal]
    (h : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  classical
  have hbij : Function.Bijective
      (fun p : ↥H × ↥K =>
        (⟨(p.1 : X) * (p.2 : X), Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(H ⊔ K))) := by
    constructor
    · rintro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩ heq
      have hval : (h₁ : X) * (k₁ : X) = (h₂ : X) * (k₂ : X) := by
        simpa using congrArg (fun z : ↥(H ⊔ K) => (z : X)) heq
      have hkey : (h₂ : X)⁻¹ * (h₁ : X) = (k₂ : X) * (k₁ : X)⁻¹ := by
        have := congrArg (fun z : X => (h₂ : X)⁻¹ * z * (k₁ : X)⁻¹) hval
        simpa [mul_assoc] using this
      have hmem : (h₂ : X)⁻¹ * (h₁ : X) ∈ H ⊓ K := by
        refine ⟨H.mul_mem (H.inv_mem h₂.2) h₁.2, ?_⟩
        rw [hkey]
        exact K.mul_mem k₂.2 (K.inv_mem k₁.2)
      have h1e : (h₂ : X)⁻¹ * (h₁ : X) = 1 := Subgroup.mem_bot.mp (h ▸ hmem)
      have hh : h₁ = h₂ := by
        have := congrArg (fun z : X => (h₂ : X) * z) h1e
        simpa using this
      have hk : k₁ = k₂ := by
        apply Subtype.ext
        rw [← mul_left_cancel_iff (a := (h₂ : X))]
        rw [hh] at hval
        exact hval
      simp [hh, hk]
    · intro g
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp g.2
      refine ⟨(⟨y, hy⟩, ⟨z, hz⟩), ?_⟩
      apply Subtype.ext
      simpa using hyz
  have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

/-- The cardinality form of `Work.BG.ocm.inertia_eq_sup`: for the inertia group `I` of a class
function `a` of `U = ↥(Uin C)` in `H₀ = ↥C.P.H0` one has
`|I| = |U| · |I ∩ S₀|` (the elements of `I` factor uniquely as `u·s` with `u ∈ U`, `s ∈ I ∩ S₀`,
because `U ⊔ S₀ = H₀` and `U ∩ S₀ = 1`). -/
theorem card_inertia_eq {G : Type} [Group G] [Finite G]
    (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    [Fintype ↥C.P.H0] [Fintype ↥(Uin C)] [Invertible (Nat.card ↥(Uin C) : ℂ)]
    (a : ClassFunction ↥(Uin C) ℂ) :
    Nat.card ↥(ClassFunction.inertia (G := ↥C.P.H0) (H := Uin C) a)
      = Nat.card ↥(Uin C) * Nat.card ↥(ClassFunction.inertia (G := ↥C.P.H0)
          (H := Uin C) a ⊓ S0in D C hDC) := by
  have hbot : Uin C ⊓ (ClassFunction.inertia (G := ↥C.P.H0) (H := Uin C) a
      ⊓ S0in D C hDC) = ⊥ := by
    rw [← le_bot_iff]
    calc Uin C ⊓ (ClassFunction.inertia (G := ↥C.P.H0) (H := Uin C) a ⊓ S0in D C hDC)
        ≤ Uin C ⊓ S0in D C hDC := inf_le_inf_left _ inf_le_right
      _ = ⊥ := S0in_inf_Uin D C hDC
  conv_lhs => rw [Work.BG.ocm.inertia_eq_sup D C hDC a]
  exact card_sup_mul_card_of_inf_eq_bot hbot

/-- `|S| = 2 · D.n` for the dihedral Sylow `2`-subgroup of the Bender–Glauberman data. -/
theorem card_S_eq {G : Type} [Group G] [Finite G] (D : BGData G) :
    Nat.card ↥(D.S : Subgroup G) = 2 * D.n := by
  obtain ⟨e⟩ := D.dih
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

/-- **The `Λ`-orbit count.**  For `a ∈ Irr(U)` not trivial on `K`, the `Λ`-orbit of `a`
(Remark 3.1) has the cardinality `|S_a|` of the stabiliser of `a` in `S`.

This is the Clifford-theoretic part of the orbit product: `|Λ(a)| = ‖Ind_U^{H₀} a‖² = [I : U]`
with `I` the inertia group of `a` in `H₀`, and `[I : U] = |I ∩ S₀| = |S ∩ S₀| = |S_a|` because
`S_a ⊆ S₀`. -/
theorem card_lamOrbitOfU_eq_card_sStab {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥(Uin C)]
    (hDC : Compat D C) (hS3 : Sec3Hyp D) (K : Subgroup G)
    (hKU : K ≤ D.U)
    (Knorm : ∀ u ∈ D.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K)
    (h1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (h2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹)
    (a : IrreducibleCharacter ↥(Uin C)) (ha : nontrivialOn C K a) :
    (lamOrbitOfU C (a : ClassFunction ↥(Uin C) ℂ)).ncard
      = Nat.card ↥(sStab D C hDC (a : ClassFunction ↥(Uin C) ℂ)) := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  have h1' := Work.BG.ocm.card_lamOrbitOfU_eq_inner (D := D) (C := C) hDC hS3 a
  have h2' := card_mul_inner_self_induce_eq_card_inertia (G := ↥C.P.H0) (H := Uin C) a
  have h3' := card_inertia_eq D C hDC (a : ClassFunction ↥(Uin C) ℂ)
  have h4' := Work.BG.ocm.card_inertia_inf_S0_eq (D := D) (C := C) hDC (a : ClassFunction ↥(Uin C) ℂ)
  have hle := Work.BG.ocm.sStab_le_S0 (D := D) (C := C) hDC K hKU Knorm h1 h2 ha
  have hinf : S0sub D ⊓ sStab D C hDC (a : ClassFunction ↥(Uin C) ℂ)
      = sStab D C hDC (a : ClassFunction ↥(Uin C) ℂ) := inf_eq_right.mpr hle
  have key : (Nat.card ↥(Uin C) : ℂ)
        * ((lamOrbitOfU C (a : ClassFunction ↥(Uin C) ℂ)).ncard : ℂ)
      = (Nat.card ↥(Uin C) : ℂ)
        * (Nat.card ↥(sStab D C hDC (a : ClassFunction ↥(Uin C) ℂ)) : ℂ) := by
    rw [h1', h2', h3']
    push_cast
    rw [h4', hinf]
    rfl
  exact Nat.cast_injective (mul_left_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne') key)

theorem orbitCardMul {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype ↥(Work.GW2.C16.Uin C)] [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter ↥(Work.GW2.C16.Uin C))]
    (hDC : Work.GW2.C16.Compat D C) (hS3 : Work.GW2.C16.Sec3Hyp D) (K : Subgroup G)
    (hKU : K ≤ D.U)
    (Knorm : ∀ u ∈ D.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K)
    (h1 : ∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹)
    (h2 : ∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹)
    {a : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(Work.GW2.C16.Uin C)}
    (ha : Work.BG.nontrivialOn C K a) :
    (Work.BG.sOrbitU D C hDC (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)).ncard *
      (Work.BG.lamOrbitOfU C (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ)).ncard
      = 2 * D.n := by
  rw [card_lamOrbitOfU_eq_card_sStab D C hDC hS3 K hKU Knorm h1 h2 a ha]
  rw [sOrbitU_card_mul_sStab_card D C hDC (a : ClassFunction ↥(Uin C) ℂ)]
  exact card_S_eq D

end Work.BG
