import Mathlib
import Submission.Work.Serre.ratAcyclic_of_finite_covering
import Submission.Work.Serre.Models

/-!
# The transfer of a finite covering, in a *range* of degrees

`Work.Serre.ratAcyclic_of_finite_covering` proves that a base of a finite covering with a rationally
acyclic total space is rationally acyclic.  For the applications to `K(ℤ/n,1)` (the lens space
`L^{2N+1} = S^{2N+1}/μₙ`, whose total space `S^{2N+1}` is rationally acyclic only *below* degree
`2N+1`) one needs the *range* form: the same transfer, but only in degrees `1, …, M`.

The proof is the one of `Work.Serre.ratAcyclic_of_finite_covering` verbatim, with the hypothesis
`RatAcyclic E` weakened to the vanishing of `H_t(E;ℚ)` for `0 < t ≤ M`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.RatHurewicz

/-- **The transfer of a finite covering, in a range of degrees.**  If `p : E → X` is a covering map
with `m > 0` sheets and `H_t(E;ℚ) = 0` for `0 < t ≤ M`, then `H_t(X;ℚ) = 0` for `0 < t ≤ M`.

The transfer `τ : C_*(X;ℚ) → C_*(E;ℚ)` satisfies `τ ≫ p_# = m • id`; since `m` is invertible in
`ℚ`, `H_t(X;ℚ)` is a direct summand of `H_t(E;ℚ)`. -/
theorem isZero_ratH_of_finite_covering_range {E X : Type} [TopologicalSpace E]
    [TopologicalSpace X] (p : C(E, X)) (hp : IsCoveringMap p) [PathConnectedSpace X]
    (m : ℕ) (hm : 0 < m) (hcard : ∀ x : X, Nat.card ↥(p ⁻¹' {x}) = m) (M : ℕ)
    (hE : ∀ t : ℕ, 0 < t → t ≤ M → IsZero (Work.Serre.ratH (TopCat.of E) t)) :
    ∀ t : ℕ, 0 < t → t ≤ M → IsZero (Work.Serre.ratH (TopCat.of X) t) := by
  intro t ht htM
  let D : Work.Serre.FiniteCover.CoverData E X := ⟨p, hp, m, hm, hcard⟩
  have hhom := congrArg (fun (f : Work.Serre.ratChains (TopCat.of X) ⟶
      Work.Serre.ratChains (TopCat.of X)) => HomologicalComplex.homologyMap f t)
    (Work.Serre.FiniteCover.transferChain_comp_chainMap D)
  rw [HomologicalComplex.homologyMap_comp] at hhom
  rw [Work.Serre.FiniteCover.homologyMap_smul_id] at hhom
  have hpz : HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℚ (TopCat.of E) (TopCat.of X) (TopCat.ofHom D.p)) t = 0 :=
    IsZero.eq_zero_of_src (hE t ht htM) _
  rw [hpz, comp_zero] at hhom
  have hmm : (D.m : ℚ) • 𝟙 (Work.Serre.ratH (TopCat.of X) t) = 0 := hhom.symm
  have hid : 𝟙 (Work.Serre.ratH (TopCat.of X) t) = 0 := by
    have hmq : (D.m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp D.hm)
    calc 𝟙 (Work.Serre.ratH (TopCat.of X) t)
        = (D.m : ℚ)⁻¹ • ((D.m : ℚ) • 𝟙 (Work.Serre.ratH (TopCat.of X) t)) := by
          rw [smul_smul, inv_mul_cancel₀ hmq, one_smul]
      _ = 0 := by rw [hmm, smul_zero]
  exact (IsZero.iff_id_eq_zero _).mpr hid

end Work.RatHurewicz
