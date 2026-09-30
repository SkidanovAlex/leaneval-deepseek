import Mathlib
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal
import Submission.Work.SymQuot.DivOf.placeIdeal_injective
import Submission.Work.SymQuot.DivOf.heightOneSpectrum_equiv_place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.unusedVariables false

namespace Work.SymQuot.DivOf

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical Function

universe u

/-- **Chinese remainder theorem for two ideals.**  If `I` and `J` are comaximal ideals of a
commutative ring `R`, then any two residues (`a` mod `I`, `b` mod `J`) are realised by a single
element.  This is the two-ideal instance of `Ideal.exists_forall_sub_mem_ideal`. -/
lemma exists_crt_two {R : Type*} [CommRing R] (I J : Ideal R) (h : IsCoprime I J) (a b : R) :
    ∃ r : R, r - a ∈ I ∧ r - b ∈ J := by
  have hpair : Pairwise (IsCoprime on (![I, J] : Fin 2 → Ideal R)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h
    · exact h.symm
    · exact absurd rfl hij
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hpair (![a, b] : Fin 2 → R)
  exact ⟨r, by simpa using hr 0, by simpa using hr 1⟩

/-- **Chinese remainder theorem for a family, one ideal of which is squared.**  Let `P` be an
ideal of a commutative ring `R` and `Q : ι → Ideal R` a finite family of ideals each comaximal
with `P`.  Then for every `a : R` there is `b : R` with `b ≡ a` modulo `P²` and `b ≡ 1` modulo
every `Q i`.

Indeed, each `Q i` is comaximal with `P`, hence so is `J = ⨅ i, Q i`
(`Ideal.isCoprime_biInf`), hence so is `P²` with `J` (`IsCoprime.pow_left`), and the two-ideal
CRT produces `b`. -/
lemma exists_crt_sq {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (P : Ideal R) (Q : ι → Ideal R) (a : R) (hQ : ∀ i, IsCoprime P (Q i)) :
    ∃ b : R, b - a ∈ P ^ 2 ∧ ∀ i, b - 1 ∈ Q i := by
  have hPJ : IsCoprime P (⨅ i, Q i) := by
    have h := Ideal.isCoprime_biInf (I := P) (J := Q) (s := Finset.univ) (fun j _ => hQ j)
    simpa using h
  have h2 : IsCoprime (P ^ 2) (⨅ i, Q i) := hPJ.pow_left
  obtain ⟨b, hba, hb1⟩ := exists_crt_two (P ^ 2) (⨅ i, Q i) h2 a 1
  exact ⟨b, hba, fun i => iInf_le Q i hb1⟩

theorem exists_crt_placeIdeal_sq_one {F : Type u} [Field F] {C : Work.CurveBasics.Curve F}
    {V : C.left.Opens} [Nonempty V] (hV : AlgebraicGeometry.IsAffineOpen V)
    [IsDedekindDomain (C.left.presheaf.obj (Opposite.op V))]
    {n : ℕ} (y : Fin n → Work.CurveBasics.Curve.Place C)
    (hy : ∀ m, (y m).point ∈ V) (z : Work.CurveBasics.Curve.Place C) (hz : z.point ∈ V)
    (a : C.left.presheaf.obj (Opposite.op V))
    (ha2 : a ∉ (Work.SymQuot.DivOf.placeIdeal C V z hz) ^ 2) :
    ∃ b : C.left.presheaf.obj (Opposite.op V),
      b - a ∈ (Work.SymQuot.DivOf.placeIdeal C V z hz) ^ 2 ∧
      ∀ m, y m ≠ z → b - 1 ∈ Work.SymQuot.DivOf.placeIdeal C V (y m) (hy m) := by
  classical
  -- The family of conditions imposed by the places `y m ≠ z`, with the trivial condition `⊤`
  -- at the indices whose place is `z` (whose congruence is not required).
  let Q : Fin n → Ideal (C.left.presheaf.obj (Opposite.op V)) :=
    fun m => if y m = z then ⊤ else Work.SymQuot.DivOf.placeIdeal C V (y m) (hy m)
  -- Every one of these conditions is comaximal with the maximal ideal of `z`: the ideals of two
  -- distinct places are distinct maximal ideals, hence comaximal.
  have hQ : ∀ m, IsCoprime (Work.SymQuot.DivOf.placeIdeal C V z hz) (Q m) := by
    intro m
    by_cases hm : y m = z
    · rw [show Q m = ⊤ by simp [Q, hm]]
      exact Ideal.isCoprime_iff_sup_eq.mpr (by simp)
    · rw [show Q m = Work.SymQuot.DivOf.placeIdeal C V (y m) (hy m) by simp [Q, hm]]
      have hmaxz := Work.SymQuot.DivOf.placeIdeal_isMaximal hV z hz
      have hmaxm := Work.SymQuot.DivOf.placeIdeal_isMaximal hV (y m) (hy m)
      have hne : Work.SymQuot.DivOf.placeIdeal C V z hz
          ≠ Work.SymQuot.DivOf.placeIdeal C V (y m) (hy m) := by
        intro heq
        exact hm (Work.SymQuot.DivOf.placeIdeal_injective hV hz (hy m) heq).symm
      exact Ideal.isCoprime_iff_sup_eq.mpr (hmaxz.coprime_of_ne hmaxm hne)
  obtain ⟨b, hba, hb1⟩ := exists_crt_sq (Work.SymQuot.DivOf.placeIdeal C V z hz) Q a hQ
  refine ⟨b, hba, ?_⟩
  intro m hm
  have hmem : b - 1 ∈ Q m := hb1 m
  show b - 1 ∈ Work.SymQuot.DivOf.placeIdeal C V (y m) (hy m)
  simpa [Q, hm] using hmem

end Work.SymQuot.DivOf
