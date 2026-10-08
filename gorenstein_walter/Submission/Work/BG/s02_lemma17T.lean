import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.Lambda
import Submission.Work.BG.CharBridge
import Submission.Work.BG.lemma17_ii
import Submission.Work.BG.s02_lemma17T_aux
import Submission.Work.BG.s02_orbitSumVanish
import Submission.Work.BG.s02_lemma17T_sep
import Submission.Work.BG.s02_lemma17T_sumTwist

/-!
# Area BG: Bender–Glauberman 1981, Lemma 1.7 evaluated on `T` (`s02_lemma17T`)

`Work.BG.Lemma17TProp C` states: for every class function `χ` of `G`, every map `rep`
sending each `ν ∈ Irr(H₀)` to a `Λ`-equivalent irreducible and constant on `Λ`-orbits,
and every `g ∈ T = H₀ ∖ U`,

`χ(g) = Σ_{ν ∈ Irr(H₀)} (χ, (ν − rep ν)^G)_G · ν(g)`.

Proof.  Frobenius reciprocity in the orientation `(χ, θ^G)_G = (χ|_{H₀}, θ)_{H₀}`
(`inner_induce_eq_inner_restrict_right`, from `inner_induce_eq_inner_restrict` and the
star-symmetry of the inner product) turns the right-hand side into
`Σ_ν (a_ν − a_{rep ν})·ν(g)`, where `a_μ := (χ|_{H₀}, μ)_{H₀}`.  The first piece is
`χ(g)` by Fourier inversion (`sum_inner_irreducibleCharacter_smul`), and the second
one vanishes because it is invariant under every twist `ν ↦ λ_β·ν`
(`s02_lemma17T_sumTwist`, since `rep` only depends on the `Λ`-orbit) while some `β` has
`λ_β(g) ≠ 1` (`s02_lemma17T_sep`, from the vanishing of the regular character
`r(Λ) = Σ_β λ_β` on `H₀ ∖ U`, and cyclicity of `H₀/U` as recorded by
`Sec2Ctx.quot_cyclic`, giving commutativity of `H₀/U`:
`Work.BG.commutator_mem_of_quot_cyclic`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- Frobenius reciprocity in the orientation used below:
`(χ, θ^G)_G = (χ|_{H₀}, θ)_{H₀}`. -/
theorem inner_induce_eq_inner_restrict_right {G : Type} [Group G] [Fintype G] {H : Subgroup G}
    [Fintype ↥H] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥H : ℂ)]
    (χ : ClassFunction G ℂ) (θ : ClassFunction ↥H ℂ) :
    ClassFunction.inner χ (ClassFunction.induce H θ) =
      ClassFunction.inner (ClassFunction.restrict H χ) θ := by
  calc ClassFunction.inner χ (ClassFunction.induce H θ)
      = star (ClassFunction.inner (ClassFunction.induce H θ) χ) :=
        ClassFunction.inner_star_comm χ _
    _ = star (ClassFunction.inner θ (ClassFunction.restrict H χ)) := by
        rw [ClassFunction.inner_induce_eq_inner_restrict H θ χ]
    _ = ClassFunction.inner (ClassFunction.restrict H χ) θ :=
        (ClassFunction.inner_star_comm (ClassFunction.restrict H χ) θ).symm

theorem s02_lemma17T {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0)] :
    Work.BG.Lemma17TProp C := by
  classical
  haveI : Fintype ↥C.P.H0 := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥(C.P.U.subgroupOf C.P.H0) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Fintype (quotGroup C.P →* ℂˣ) := Fintype.ofFinite _
  intro χ rep _hrep1 hrep2 g hg
  set ψ : ClassFunction ↥C.P.H0 ℂ := ClassFunction.restrict C.P.H0 χ with hψ
  set a : ClassFunction ↥C.P.H0 ℂ → ℂ := fun μ => ClassFunction.inner ψ μ with ha
  -- (1) `(χ, (ν − rep ν)^G)_G = a_ν − a_{rep ν}`
  have hstep : ∀ ν : IrreducibleCharacter ↥C.P.H0,
      ClassFunction.inner χ (ind C ((ν : ClassFunction ↥C.P.H0 ℂ) - rep ν)) =
        a ν - a (rep ν) := by
    intro ν
    have h1 : ClassFunction.inner χ (ind C ((ν : ClassFunction ↥C.P.H0 ℂ) - rep ν)) =
        ClassFunction.inner (ClassFunction.restrict C.P.H0 χ)
          ((ν : ClassFunction ↥C.P.H0 ℂ) - rep ν) :=
      inner_induce_eq_inner_restrict_right χ _
    rw [h1]
    show ClassFunction.inner ψ ((ν : ClassFunction ↥C.P.H0 ℂ) - rep ν) =
      ClassFunction.inner ψ (ν : ClassFunction ↥C.P.H0 ℂ) - ClassFunction.inner ψ (rep ν)
    rw [ClassFunction.inner_sub_right]
  -- (2) Fourier inversion over `Irr(H₀)`
  have hkey : (∑ ν : IrreducibleCharacter ↥C.P.H0,
      a ν * (ν : ClassFunction ↥C.P.H0 ℂ) g) = χ (g : G) := by
    have h := congrArg (fun f : ClassFunction ↥C.P.H0 ℂ => f g)
      (sum_inner_irreducibleCharacter_smul ψ)
    simp only [ClassFunction.sum_apply, ClassFunction.smul_apply] at h
    show (∑ ν : IrreducibleCharacter ↥C.P.H0,
      ClassFunction.inner ψ (ν : ClassFunction ↥C.P.H0 ℂ) *
        (ν : ClassFunction ↥C.P.H0 ℂ) g) = χ (g : G)
    rw [h]
    exact ClassFunction.restrict_apply C.P.H0 χ g
  -- (3) the `rep`-part vanishes at `g ∉ U`
  have hzero : (∑ ν : IrreducibleCharacter ↥C.P.H0,
      a (rep ν) * (ν : ClassFunction ↥C.P.H0 ℂ) g) = 0 := by
    set S : ℂ := ∑ ν : IrreducibleCharacter ↥C.P.H0,
      a (rep ν) * (ν : ClassFunction ↥C.P.H0 ℂ) g with hSdef
    have hgU : g ∉ C.P.U.subgroupOf C.P.H0 := fun h => hg (Subgroup.mem_subgroupOf.mp h)
    have hsum0 : lambdaSum C.P g = 0 :=
      lambdaSum_apply_eq_zero_of_not_mem_U C.P (commutator_mem_of_quot_cyclic C) hgU
    obtain ⟨β, hβ⟩ := s02_lemma17T_sep C hsum0
    have hinv : ∀ ν : IrreducibleCharacter ↥C.P.H0,
        (fun μ : ClassFunction ↥C.P.H0 ℂ => a (rep μ)) (lamTwist C β ν) =
          (fun μ : ClassFunction ↥C.P.H0 ℂ => a (rep μ)) ν := by
      intro ν
      show a (rep ((lamTwist C β ν : IrreducibleCharacter ↥C.P.H0) :
        ClassFunction ↥C.P.H0 ℂ)) = a (rep (ν : ClassFunction ↥C.P.H0 ℂ))
      rw [← hrep2 ν (lamTwist C β ν) (lamEquiv_lamTwist C β ν)]
    have htwist := s02_lemma17T_sumTwist C β
      (fun μ : ClassFunction ↥C.P.H0 ℂ => a (rep μ)) g hinv
    have hS1 : S = lamCF C β g * S := by
      rw [hSdef]
      exact htwist
    have hmul : (1 - lamCF C β g) * S = 0 := by
      have h2 : lamCF C β g * S = S := hS1.symm
      rw [sub_mul, one_mul, h2, sub_self]
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd (sub_eq_zero.mp h).symm hβ
    · rw [hSdef] at h
      exact h
  -- assembly
  have hR : (∑ ν : IrreducibleCharacter ↥C.P.H0,
      ClassFunction.inner χ (ind C ((ν : ClassFunction ↥C.P.H0 ℂ) - rep ν)) *
        (ν : ClassFunction ↥C.P.H0 ℂ) g)
      = ∑ ν : IrreducibleCharacter ↥C.P.H0,
        (a ν - a (rep ν)) * (ν : ClassFunction ↥C.P.H0 ℂ) g :=
    Finset.sum_congr rfl fun ν _ => by rw [hstep ν]
  have hsplit : (∑ ν : IrreducibleCharacter ↥C.P.H0,
        (a ν - a (rep ν)) * (ν : ClassFunction ↥C.P.H0 ℂ) g)
      = (∑ ν : IrreducibleCharacter ↥C.P.H0,
          a ν * (ν : ClassFunction ↥C.P.H0 ℂ) g)
        - (∑ ν : IrreducibleCharacter ↥C.P.H0,
          a (rep ν) * (ν : ClassFunction ↥C.P.H0 ℂ) g) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ν _ => by rw [sub_mul]
  rw [hR, hsplit, hzero, sub_zero]
  exact hkey.symm

end Work.BG
