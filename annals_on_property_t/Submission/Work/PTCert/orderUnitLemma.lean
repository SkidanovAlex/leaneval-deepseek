import Mathlib
import Submission.Work.PTCert.OrderUnit
import Submission.Work.RouteB.StarStructure
import Submission.Work.PTCert.sosCauchySchwarz
import Submission.Work.PTCert.lprodTelescope
import Submission.Work.PTCert.letterBound

/-! Guidance from the project lead (the requester):

Context: annals_on_property_t. `theorem_1` is reduced (proved, Submission/Work/RouteB/Final.lean) to two
sum-of-squares certificates; Submission/Work/PTCert/ is the kernel-checked certificate pipeline. The
definitions you need are in `Submission/Work/PTCert/Interfaces.lean` (namespace `Submission.PTCert`);
`IsSOS` is `Submission.RouteB.IsSOS` (Submission/Work/RouteB/Symmetrisation.lean: `IsSOS.add`,
`IsSOS.finset_sum`, `IsSOS.map`, `isSOS_of_fintype`; `IsSOS.smul` is used in RouteB/Final.lean).
The star on `MonoidAlgebra ℝ G` is `mapDomain (·⁻¹)` (ChallengeDeps); import
`Submission.Work.RouteB.StarStructure` to get Mathlib's `star_mul`, `star_sum`, `star_smul`, … .
`star (of g) = of g⁻¹` (see Submission/Helpers.lean). Do NOT use `native_decide`. No `decide` on
`MulAut (FreeGroup _)` equalities in bulk (each costs ~0.2 s); prove things generically.
Definitions: `Submission/Work/PTCert/OrderUnit.lean`, `Checkers.lean` (`lprod r ks = (ks.map (b1 r)).prod`).
Prove `OrderUnitLemma r`.  Write `A ≤ B` for `IsSOS (B - A)`.  Steps:
(1) `2•1 - of g - of g⁻¹ = star (1 - of g) * (1 - of g)` (star (of g) = of g⁻¹).
(2) Telescoping: for `g = s₁⋯sₙ`, `1 - g = Σ_{i} (s₁⋯s_{i-1}) (1 - s_i)` =: `Σ aᵢ`.
(3) Cauchy–Schwarz in the Σ² order: `n Σ star aᵢ aᵢ - star(Σ aᵢ)(Σ aᵢ) = Σ_{i<j} star(aᵢ-aⱼ)(aᵢ-aⱼ)`, and
    `star aᵢ aᵢ = star(1-sᵢ)(1-sᵢ)` (the prefix `s₁⋯s_{i-1}` is a group element: star(of h)·of h = 1).
(4) For a letter `s = b1 r k` (`k < NB1 r`): `star(1-s)(1-s) ≤ 2 Δ` where `Δ = deltaSub r r =
    Laplacian (SAutGen r)`: equation (1) of the paper, `2Δ = Σ_{t ∈ SAutGen r} star(1-t)(1-t)`
    (proved: `RouteB.Edge.isSOS_laplacian` / `two_mul_laplacian_eq_sum_sq` in RouteB/PropertyTCert.lean
    and Final.lean), and `b1 r k ∈ SAutGen r` for `1 ≤ k < NB1 r` (see PTCert/targetExpansions.lean and
    its helpers); for `k = 0` the term is `0`.
(5) Combine: `star(1-g)(1-g) ≤ n Σᵢ star(1-sᵢ)(1-sᵢ) ≤ n · n · 2Δ`.  The empty list gives `0 ≤ 0`.
~200 lines; use `IsSOS.add`, `IsSOS.smul`, `IsSOS.finset_sum`.

DELEGATED PIECES (proved in parallel, imported above):
* `Work.PTCert.lprodTelescope`                    -- step (2), the telescoping identity
* `Work.PTCert.sosCauchySchwarz`                  -- step (3), Cauchy–Schwarz in the Σ² order
* `Work.PTCert.letterBound`                       -- step (4), the single-letter bound
Everything below is the assembly (steps (1) and (5)).
-/

open OnPropertyT Submission.RouteB
open scoped BigOperators

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert

lemma star_group_mul {G : Type*} [Group G] (h : G) (x : MonoidAlgebra ℝ G) :
    star (MonoidAlgebra.of ℝ G h * x) * (MonoidAlgebra.of ℝ G h * x) = star x * x := by
  have hh : MonoidAlgebra.of ℝ G h⁻¹ * MonoidAlgebra.of ℝ G h = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [Submission.Helpers.star_mul, Submission.Helpers.star_of]
  rw [show (star x * MonoidAlgebra.of ℝ G h⁻¹) * (MonoidAlgebra.of ℝ G h * x)
      = (star x * (MonoidAlgebra.of ℝ G h⁻¹ * MonoidAlgebra.of ℝ G h)) * x from by
        noncomm_ring,
    hh, mul_one]

theorem orderUnitLemma (r : ℕ) : OrderUnitLemma r := by
  intro ks hks
  classical
  have hcoef : ((2 * ks.length ^ 2 : ℕ) : ℝ) = (2 : ℝ) * (ks.length : ℝ) ^ 2 := by
    push_cast
    ring
  rw [hcoef]
  set g : MulAut (FreeGroup (Fin r)) := lprod r ks with hg
  have hgg : MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) g⁻¹
        * MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hinner : ((2 : ℝ) • (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
        - MonoidAlgebra.of ℝ _ g - MonoidAlgebra.of ℝ _ g⁻¹)
      = star (1 - MonoidAlgebra.of ℝ _ g) * (1 - MonoidAlgebra.of ℝ _ g) := by
    rw [two_smul ℝ (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))]
    rw [Submission.Helpers.star_sub, Submission.Helpers.star_one, Submission.Helpers.star_of,
      sub_mul, one_mul, mul_sub, mul_one, hgg]
    abel
  rw [hinner]
  let a : Fin ks.length → MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))) :=
    fun i => MonoidAlgebra.of ℝ _ (lprod r (ks.take i.val))
      * (1 - MonoidAlgebra.of ℝ _ (b1 r (ks.get i)))
  have htel : (1 - MonoidAlgebra.of ℝ _ g) = Finset.univ.sum a := by
    rw [hg]
    exact lprodTelescope r ks
  have hSQ : (Finset.univ.sum (fun i : Fin ks.length => star (a i) * a i))
      = Finset.univ.sum (fun i : Fin ks.length =>
          star (1 - MonoidAlgebra.of ℝ _ (b1 r (ks.get i)))
            * (1 - MonoidAlgebra.of ℝ _ (b1 r (ks.get i)))) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    dsimp only [a]
    exact star_group_mul (lprod r (ks.take i.val))
      (1 - MonoidAlgebra.of ℝ _ (b1 r (ks.get i)))
  have hA : IsSOS ((ks.length : ℝ) • Finset.univ.sum (fun i : Fin ks.length =>
      ((2 : ℝ) • Submission.RouteB.Edge.deltaSub r r
        - star (1 - MonoidAlgebra.of ℝ _ (b1 r (ks.get i)))
          * (1 - MonoidAlgebra.of ℝ _ (b1 r (ks.get i)))))) := by
    refine IsSOS.smul (Nat.cast_nonneg ks.length) (IsSOS.finset_sum Finset.univ (fun i _ => ?_))
    exact letterBound r (ks.get i) (hks _ (List.get_mem ks i))
  have hB : IsSOS ((ks.length : ℝ) • (Finset.univ.sum (fun i : Fin ks.length => star (a i) * a i))
      - star (1 - MonoidAlgebra.of ℝ _ g) * (1 - MonoidAlgebra.of ℝ _ g)) := by
    have hcs := sosCauchySchwarz a
    rw [← htel] at hcs
    exact hcs
  have hsum := hA.add hB
  rw [hSQ] at hsum
  convert hsum using 1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

end Work.PTCert
