import Mathlib
import Submission.OddOrder.GroupTheory.RepresentationTheory.CliffordSingleOrbit

set_option linter.style.haveILetI false

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **Frobenius characters nontrivial on the kernel have degree divisible by the complement
order.**  If `X = N ⋊ A` is a Frobenius group with kernel `N` and complement `A`, and `θ` is an
irreducible character of `X` that is not trivial on `N`, then `θ(1)` is divisible by `|A|`.

Indeed `N ⊄ ker θ`, so `Res_N θ` is not a multiple of the trivial character of `N`, hence it has a
nontrivial irreducible constituent `ψ`.  By Frobenius reciprocity `θ` is a constituent of the
induced character `Ind_N^X ψ`, which is irreducible ([Is] Thm 6.34, the inertia of a nontrivial
irreducible of the kernel being exactly `N`).  Hence `θ = Ind_N^X ψ` and
`θ(1) = [X : N]·ψ(1) = |A|·ψ(1)`. -/
theorem c3FrobFrobeniusDvdDegree {X : Type} [Group X] [Finite X] [Fintype X]
    [Invertible (Nat.card X : ℂ)] (N A : Subgroup X)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup X N A)
    (θ : OddOrder.RepresentationTheory.ClassFunction X ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hker : ∃ n : X, n ∈ N ∧ θ n ≠ θ 1) :
    ∃ d : ℕ, θ 1 = (d : ℂ) ∧ Nat.card A ∣ d := by
  classical
  letI : N.Normal := hF.isNormal
  haveI : Fintype ↥N := Fintype.ofFinite ↥N
  letI : Invertible (Nat.card ↥N : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Finite (IrreducibleCharacter ↥N) := finite_irreducibleCharacter (G := ↥N)
  letI : Fintype (IrreducibleCharacter ↥N) := Fintype.ofFinite _
  set χ : IrreducibleCharacter X := ⟨θ, hθ⟩ with hχ
  have hχcoe : (χ : ClassFunction X ℂ) = θ := by rw [hχ, IrreducibleCharacter.coe_mk]
  obtain ⟨ψ, hover⟩ := IrreducibleCharacter.exists_liesOver N χ
  by_cases hψ : ψ = trivialIrreducibleCharacter ↥N
  · -- `ψ` trivial would make `Res_N χ` a constant class function, contradicting `hker`.
    exfalso
    obtain ⟨n, hnN, hne⟩ := hker
    have hinv : ∀ g : X, IrreducibleCharacter.conjBy g ψ = ψ := by
      intro g
      rw [hψ]
      apply Subtype.ext
      ext x
      simp [IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]
    have hres := restrict_eq_restrictionMultiplicity_smul_of_invariant
      (G := X) (H := N) χ ψ hover hinv
    rw [hψ, IrreducibleCharacter.coe_trivialIrreducibleCharacter] at hres
    have h1 := congrArg (fun f : ClassFunction ↥N ℂ => f ⟨n, hnN⟩) hres
    have h2 := congrArg (fun f : ClassFunction ↥N ℂ => f 1) hres
    simp only [ClassFunction.smul_apply, trivialClassFunction_apply, mul_one,
      ClassFunction.restrict_apply, Subgroup.coe_one] at h1 h2
    rw [hχcoe] at h1 h2
    exact hne (h1.trans h2.symm)
  · -- `ψ` nontrivial: `Ind_N^X ψ` is irreducible, so `θ = Ind_N^X ψ` and `θ(1) = [X:N]·ψ(1)`.
    obtain ⟨dψ, hdψpos, hdψ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ψ
    have hind : IsIrreducibleCharacter (ClassFunction.induce N (ψ : ClassFunction ↥N ℂ)) :=
      isIrreducibleCharacter_induce_of_frobeniusGroup hF ψ hψ
    have hdeg := apply_one_eq_index_mul_of_liesOver_of_isIrreducibleCharacter_induce
      χ ψ hind hover
    refine ⟨N.index * dψ, ?_, ?_⟩
    · change (χ : ClassFunction X ℂ) 1 = ((N.index * dψ : ℕ) : ℂ)
      rw [hdeg, hdψ]
      push_cast
      ring
    · have hcardA : Nat.card ↥A = N.index :=
        (Subgroup.IsComplement'.index_eq_card hF.isComplement.symm).symm
      rw [hcardA]
      exact dvd_mul_right _ _

end Work.BG
