import Mathlib
import Submission.Work.DSG4b.gonfPerfect.Basic
import Submission.Work.DSG4b.gonfPerfect.flat.flat_AN
import Submission.Work.DSG4b.gonfPerfect.flat.exists_stage_Fin

/-!
# Flatness of the perfectification `R →+* S`

Let `R` be a commutative local ring whose residue field `k` has characteristic the prime `p`, and
let `D : PData R p` be the data perfectifying `R` at `p`: the colimit
`S = D.S = colim_N AN D N` of the stages `AN D N = R[T_j : j ∈ Λ] ⧸ (T_j^{p^N} - b̃_j)`.

Every stage `AN D N` is flat over `R` (indeed free, with basis the reduced monomials), because the
relation polynomials are monic in their own variable (`flat_AN`).  Since `S` is a filtered colimit
of the stages and a relation in `S` involves only finitely many elements, it already holds in some
stage, where it is trivial by flatness of that stage.

We formalise this with the equational criterion for flatness
(`Module.Flat.of_forall_isTrivialRelation`): given a relation `∑ᵢ fᵢ xᵢ = 0` in `D.S`, lift the
finitely many `xᵢ` to a single stage `AN D N` (`exists_stage_Fin`), push the relation down to a
stage `AN D M` (`Ring.DirectLimit.of.zero_exact`), trivialise it there using flatness of `AN D M`,
and push the resulting trivialisation back up to `D.S`.
-/

namespace Work.DSG4b.gonfPerfect.flat

set_option linter.style.haveILetI false

theorem flat_S (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) :
    D.phi.Flat := by
  -- `RingHom.Flat φ` is `Module.Flat R S` for the algebra structure induced by `φ`.
  letI : Algebra R D.S := D.phi.toAlgebra
  show Module.Flat R D.S
  refine Module.Flat.of_forall_isTrivialRelation ?_
  intro l f x hx
  -- every element of `S` occurs already in some stage; one stage suffices for all of them.
  obtain ⟨N, x', hx'⟩ := exists_stage_Fin R p D l x
  -- `D.incl M` is `R`-linear for the algebra structure induced by `D.phi`.
  have incl_sum : ∀ (n : ℕ) (M : ℕ) (a : Fin n → R) (z : Fin n → D.AN M),
      D.incl M (∑ i, a i • z i) = ∑ i, a i • D.incl M (z i) := by
    intro n M a z
    rw [show D.incl M (∑ i, a i • z i) = ∑ i, D.incl M (a i • z i) from
      map_sum (D.incl M) (fun i => a i • z i) Finset.univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, ← PData.toAN_eq_algebraMap]
    show D.incl M (D.toAN M (a i) * z i) = D.phi (a i) * D.incl M (z i)
    rw [map_mul, PData.incl_toAN]
  -- likewise for the transition maps `D.trans`.
  have trans_sum : ∀ (M : ℕ) (hNM : N ≤ M) (n : ℕ) (a : Fin n → R) (z : Fin n → D.AN N),
      D.trans N M hNM (∑ i, a i • z i) = ∑ i, a i • D.trans N M hNM (z i) := by
    intro M hNM n a z
    rw [show D.trans N M hNM (∑ i, a i • z i) = ∑ i, D.trans N M hNM (a i • z i) from
      map_sum (D.trans N M hNM) (fun i => a i • z i) Finset.univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, ← PData.toAN_eq_algebraMap, map_mul, PData.trans_toAN,
      Algebra.smul_def, ← PData.toAN_eq_algebraMap]
  -- the relation `∑ᵢ fᵢ x'ᵢ = 0` already holds in the stage `AN D N`.
  have hzero : D.incl N (∑ i : Fin l, f i • x' i) = 0 := by
    rw [incl_sum l N f x', ← hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx' i]
  -- push it down to a single stage `AN D M`.
  obtain ⟨M, hNM, hM⟩ := Ring.DirectLimit.of.zero_exact (G := fun N => D.AN N)
    (f' := fun i j h => D.trans i j h) hzero
  have hM' : ∑ i : Fin l, f i • (D.trans N M hNM (x' i)) = 0 := by
    rw [← trans_sum M hNM l f x']
    exact hM
  -- trivialise the relation in the flat stage `AN D M`.
  haveI : Module.Flat R (D.AN M) := flat_AN R p D M
  obtain ⟨k, a, y', hy', ha'⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (M := D.AN M) hM'
  have hyi : ∀ i : Fin l, D.trans N M hNM (x' i) = ∑ j, a i j • y' j := fun i => hy' i
  -- and push the trivialisation back up to `S`.
  refine ⟨k, a, fun j => D.incl M (y' j), fun i => ?_, ha'⟩
  calc x i = D.incl N (x' i) := (hx' i).symm
    _ = D.incl M (D.trans N M hNM (x' i)) := (PData.incl_trans N M hNM (x' i)).symm
    _ = D.incl M (∑ j, a i j • y' j) := by rw [hyi i]
    _ = ∑ j, a i j • D.incl M (y' j) := incl_sum k M (a i) y'

end Work.DSG4b.gonfPerfect.flat
