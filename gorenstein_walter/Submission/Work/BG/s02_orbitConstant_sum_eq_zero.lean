import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_assemblyCore
import Submission.Work.BG.s02_lemma17T_aux
import Submission.Work.BG.s02_lemma17T_sep
import Submission.Work.BG.Lambda
import Submission.Work.BG.s02_orbitSumVanish

/-!
# Area BG: a `Λ`-orbit-constant function on `Irr(H₀)` sums to `0` off `U`

`Λ` is the group of linear characters of `H₀/U` inflated to `H₀` (`Work.BG.Lambda`), acting on
`Irr(H₀)` by multiplication, with orbits `Λν` (`Work.BG.lamOrbit`).  The statement proved here is

  `∑_{ν ∈ Irr(H₀)} A ν · ν(g) = 0`  for every `A : Irr(H₀) → ℂ` **constant on `Λ`-orbits** and
  every `g ∈ H₀ ∖ U`.

It is the linear combination of the orbit-sum vanishing `Work.BG.s02_orbitSumVanish`
(=`Work.BG.OrbitSumVanishProp`, Bender–Glauberman 1981, Lemma 1.7(i)) that the coherence
argument uses: `ν ↦ A ν` is constant on the orbits, so the total sum is a combination of the
individual orbit sums `∑_{χ ∈ Λν} χ(g)`, each of which is `0`.

## Proof

`LamEquiv` is an equivalence relation on the class functions of `H₀`
(`s02c_LamEquiv_{refl,symm,trans}`), so it defines a setoid on `Irr(H₀)` whose classes are
exactly the intersections `Λν ∩ Irr(H₀)`.  `Finset.sum_fiberwise` regroups the total sum as a
sum over the quotient (the set of orbits) of the sums over the individual orbits.  On a
nonempty orbit, with representative `ν₀ ∈ Irr(H₀)`:

* `A` is constant there, so the contribution is `A ν₀ · ∑_{ν ∈ Λν₀} ν(g)`;
* `∑_{ν ∈ Λν₀} ν(g) = ∑_ν orbitTerm C ν₀ ν g` is `0` by `s02_orbitSumVanish`.

An empty orbit contributes `0` trivially, so the whole sum vanishes.
-/

namespace Work.BG

/-- Shorthand for the type of irreducible characters of `H₀` (used only inside this file). -/
private abbrev IrrH0 {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G) :=
  OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0

/-- Shorthand for class functions on `H₀` (used only inside this file). -/
private abbrev CFH0 {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G) :=
  OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ

theorem s02_orbitConstant_sum_eq_zero {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0)]
    (A : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0 → ℂ)
    (hA : ∀ μ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
      Work.BG.LamEquiv C (μ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ)
        (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) → A μ = A ν)
    {g : ↥C.P.H0} (hg : (g : G) ∉ C.P.U) :
    ∑ ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0,
      A ν * (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ) g = 0 := by
  classical
  -- `LamEquiv` is an equivalence relation on `CF(H₀)` (`s02c_LamEquiv_{refl,symm,trans}`);
  -- regard it as a setoid on `Irr(H₀)` and partition `Irr(H₀)` into its classes, which are
  -- exactly the `Λ`-orbits `Λν ∩ Irr(H₀)`.
  let s : Setoid (IrrH0 C) :=
    ⟨fun μ ν => Work.BG.LamEquiv C (μ : CFH0 C) (ν : CFH0 C),
     fun μ => Work.BG.s02c_LamEquiv_refl C _,
     fun h => Work.BG.s02c_LamEquiv_symm C h,
     fun h1 h2 => Work.BG.s02c_LamEquiv_trans C h1 h2⟩
  haveI : Fintype (Quotient s) :=
    Fintype.ofSurjective (fun ν : IrrH0 C => (Quotient.mk s ν : Quotient s)) (fun q => by
      obtain ⟨a, ha⟩ := Quotient.exists_rep q
      exact ⟨a, ha⟩)
  haveI : DecidableEq (Quotient s) := Classical.decEq _
  -- `Finset.sum_fiberwise`: sum first over the orbit of `ν`, then over the orbits.
  have key : (∑ ν : IrrH0 C, A ν * (ν : CFH0 C) g)
      = ∑ q : Quotient s, ∑ ν ∈ Finset.univ.filter (fun ν : IrrH0 C => Quotient.mk s ν = q),
          A ν * (ν : CFH0 C) g :=
    (Finset.sum_fiberwise (Finset.univ : Finset (IrrH0 C))
      (fun ν : IrrH0 C => (Quotient.mk s ν : Quotient s))
      (fun ν : IrrH0 C => A ν * (ν : CFH0 C) g)).symm
  rw [key]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hne : ∃ ν : IrrH0 C, Quotient.mk s ν = q
  · -- a non-empty orbit: pick a member `ν₀`, its contribution is `A ν₀ · (orbit sum at `g`)`
    obtain ⟨ν₀, hν₀⟩ := hne
    have hfib : (Finset.univ.filter (fun ν : IrrH0 C => Quotient.mk s ν = q))
        = Finset.univ.filter
            (fun ν : IrrH0 C => Work.BG.LamEquiv C (ν₀ : CFH0 C) (ν : CFH0 C)) := by
      apply Finset.filter_congr
      intro ν _
      constructor
      · intro h
        have h1 : Quotient.mk s ν = Quotient.mk s ν₀ := h.trans hν₀.symm
        exact Work.BG.s02c_LamEquiv_symm C (Quotient.exact h1)
      · intro h
        exact (Quotient.sound h).symm.trans hν₀
    -- the orbit sum of `ν₀` at `g` vanishes (Lemma 1.7(i), `s02_orbitSumVanish`)
    have hsum0 : (∑ ν ∈ Finset.univ.filter
          (fun ν : IrrH0 C => Work.BG.LamEquiv C (ν₀ : CFH0 C) (ν : CFH0 C)),
          (ν : CFH0 C) g) = 0 := by
      have h1 : (∑ ν : IrrH0 C, Work.BG.orbitTerm C (ν₀ : CFH0 C) (ν : CFH0 C) g)
          = ∑ ν : IrrH0 C, (if Work.BG.LamEquiv C (ν₀ : CFH0 C) (ν : CFH0 C)
              then (ν : CFH0 C) g else 0) := by
        apply Finset.sum_congr rfl
        intro ν _
        simp only [Work.BG.orbitTerm]
      have h2 : (∑ ν : IrrH0 C, (if Work.BG.LamEquiv C (ν₀ : CFH0 C) (ν : CFH0 C)
              then (ν : CFH0 C) g else 0))
          = ∑ ν ∈ Finset.univ.filter
              (fun ν : IrrH0 C => Work.BG.LamEquiv C (ν₀ : CFH0 C) (ν : CFH0 C)),
              (ν : CFH0 C) g := by
        rw [← Finset.sum_filter]
      have hvan := Work.BG.s02_orbitSumVanish C (ν₀ : CFH0 C) ν₀.2 g hg
      rw [← h2, ← h1, hvan]
    rw [hfib]
    -- `A` is constant on the orbit, so the orbit sum is `A ν₀` times the vanishing orbit sum
    calc ∑ ν ∈ Finset.univ.filter
            (fun ν : IrrH0 C => Work.BG.LamEquiv C (ν₀ : CFH0 C) (ν : CFH0 C)),
            A ν * (ν : CFH0 C) g
        = ∑ ν ∈ Finset.univ.filter
            (fun ν : IrrH0 C => Work.BG.LamEquiv C (ν₀ : CFH0 C) (ν : CFH0 C)),
            A ν₀ * (ν : CFH0 C) g := by
          apply Finset.sum_congr rfl
          intro ν hν
          rw [hA ν₀ ν ((Finset.mem_filter.mp hν).2)]
      _ = A ν₀ * ∑ ν ∈ Finset.univ.filter
            (fun ν : IrrH0 C => Work.BG.LamEquiv C (ν₀ : CFH0 C) (ν : CFH0 C)),
            (ν : CFH0 C) g := (Finset.mul_sum _ _ _).symm
      _ = A ν₀ * 0 := by rw [hsum0]
      _ = 0 := mul_zero _
  · -- an empty orbit contributes nothing
    apply Finset.sum_eq_zero
    intro ν hν
    exact absurd ⟨ν, (Finset.mem_filter.mp hν).2⟩ hne

end Work.BG
