import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.Serre.Engine
import Submission.Work.Rat.sphereOdd
import Submission.Work.Rat.piTorsionSphereEven

/-! Guidance from the project lead (the requester):

AREA RATIONAL (lead's guidance) — rational homotopy of spheres in ALL degrees (Serre).
Hypotheses you are GIVEN (do not prove them): `Work.Serre.SerreE3b` (rational Gysin/Euler class for
spherical fibrations — the milnor drive proves it), `Work.PiS.SphereFG` (π_{j+2}(Sⁿ) f.g.), and for
HopfInfinite also `Work.PiS.SphereTorsion`.
Facts to reach: π_k(Sⁿ) ⊗ ℚ = 0 for k ∉ {n, 2n-1 (n even)}, and π_{2n-1}(Sⁿ) ⊗ ℚ ≅ ℚ for n even.
Route (the milnor SERRE blueprint, REFS/milnor_notes/Drive/SERRE_BLUEPRINT.md §2-3 and addenda, extended
from the stable range to all degrees; ranges are arbitrary so pick N ≫ k):
 (C2) Rational cohomology of K(ℤ,m) range models: ℚ[x] (m even), Λ[x] (m odd), through degree N - c·m.
      Mutual induction: C2odd(m) (the homotopy fibre E_m of a π_m-bijection S^m → K(ℤ,m) is
      rationally acyclic in range) from C2even(m-1) by the Wang sequence with the derivation property
      (`Work.Serre.serreE4`, PROVED); C2even(m) from C2odd(m-1) by E3b on the path–loop fibration
      (fibre ≃_ℚ S^{m-1}). Seed: `Work.Stems.c2evenFull` (takes SerreE3b), Stems/c2odd*.lean,
      Stems/Engine/C2EvenRange.lean — read their exact statements; many are range forms already.
 (S1) Rational vanishing Hurewicz for spaces with f.g. homotopy: X simply connected, π_i(X) f.g. and
      H̃_i(X;ℚ) = 0 for i ≤ N ⇒ π_i(X) torsion (finite) for i ≤ N. Seed: `Work.Serre.serreS1OfC0C3E3a`
      needs SerreC3 for ARBITRARY torsion groups (open); with f.g. input only FINITE groups are killed,
      so use the finite forms `Work.Serre.serreRangeEMVanAllFin_unconditional` (C3 for finite groups,
      proved) and the S1 assembly pattern `serreS1OfRangeEMVan`.
 (odd n) E_n = hofib(Sⁿ → K(ℤ,n) range model) is rationally acyclic in range (C2odd); π_k(E_n) = π_k(Sⁿ)
      for k > n (LES), f.g. by SphereFG; S1 ⇒ torsion.
 (even n) Wang for K(ℤ,n-1) → E_n → Sⁿ with C2 (n-1 odd: Λ[x]) gives H̃^*(E_n;ℚ) = ℚ in degree 2n-1
      only. Pick g : S^{2n-1} → E_n with nonzero rational Hurewicz image (first-degree Hurewicz mod
      torsion, `Work.RatHurewicz.hurewiczModTorsionFirstDegree`); g is a rational homology iso in
      range; its homotopy fibre is rationally acyclic in range (Serre exact sequence / E3a-type
      comparison), so π_*(E_n) ⊗ ℚ ≅ π_*(S^{2n-1}) ⊗ ℚ in range, and the odd case finishes.
      HopfInfinite: π_{2n-1}(Sⁿ) ⊗ ℚ ≅ H_{2n-1}(E_n;ℚ) = ℚ ≠ 0 ⇒ an element of infinite order.
Both targets (SphereTorsion, HopfInfinite) share (C2), (S1) and the even-n analysis: build them as
shared lemmas under Submission/Work/Rat/ and coordinate by reading each other's files.
Check every imported milnor theorem with #print axioms (drafts coexist with proofs).
-/

namespace Work.Rat

theorem sphereTorsion (hE3b : Work.Serre.SerreE3b) (hFG : Work.PiS.SphereFG) :
    Work.PiS.SphereTorsion := by
  intro n hn j hj1 hj2 a
  rcases Nat.even_or_odd n with heven | hodd
  · -- even `n`
    have hk2n : j + 2 ≠ 2 * n - 1 := by
      intro h
      exact hj2 ⟨heven, by omega⟩
    have hmain : Work.Serre.PiTorsion (Work.Serre.Sph n) (Work.PiS.pt n) (j + 2 - 1) :=
      Work.Rat.piTorsionSphereEven hE3b hFG
        (fun n' k' hn' hodd' hk2' hkn' x₀ =>
          Work.Rat.piTorsion_sphere_odd hE3b hFG n' k' hn' hodd' hk2' hkn' x₀)
        n (j + 2) hn heven (by omega) (by omega) hk2n (Work.PiS.pt n)
    exact hmain a
  · -- odd `n`
    have hn3 : 3 ≤ n := by obtain ⟨m, hm⟩ := hodd; omega
    exact Work.Rat.piTorsion_sphere_odd hE3b hFG n (j + 2) hn3 hodd (by omega) (by omega)
      (Work.PiS.pt n) a

end Work.Rat
