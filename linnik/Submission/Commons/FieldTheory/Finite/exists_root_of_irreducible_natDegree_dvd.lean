import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.Finite

/-- If `P` is an irreducible polynomial over a finite field `F`, and `E` is a finite
field extension of `F` whose degree is divisible by `P.natDegree`, then `P` has a root
in `E`. -/
theorem exists_root_of_irreducible_natDegree_dvd {F E : Type*} [Field F] [Field E] [Fintype F]
    [Fintype E] [Algebra F E] (n : ℕ) (hn : Module.finrank F E = n) (P : Polynomial F)
    (hP : Irreducible P) (hdvd : P.natDegree ∣ n) :
    ∃ a : E, Polynomial.eval₂ (algebraMap F E) a P = 0 := by
  -- `AdjoinRoot P = F[X]/(P)` is a field because `P` is irreducible.
  have : Fact (Irreducible P) := ⟨hP⟩
  -- Its degree over `F` is `P.natDegree`.
  have hfr : Module.finrank F (AdjoinRoot P) = P.natDegree := by
    rw [PowerBasis.finrank]
    exact AdjoinRoot.powerBasis_dim hP.ne_zero
  -- So the degree divides `[E : F]`, and we obtain an `F`-algebra hom `F[X]/(P) → E`.
  have hdvd' : Module.finrank F (AdjoinRoot P) ∣ Module.finrank F E := by
    rw [hfr, hn]; exact hdvd
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (K := AdjoinRoot P) (L := E) hdvd'
  -- `AdjoinRoot.root P` is a root of `P` in `F[X]/(P)`.
  have haeval : Polynomial.aeval (AdjoinRoot.root P) P = 0 := by
    rw [Polynomial.aeval_def]
    exact AdjoinRoot.eval₂_root P
  -- Its image under `φ` is a root of `P` in `E`.
  refine ⟨φ (AdjoinRoot.root P), ?_⟩
  rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, haeval, map_zero]

end Commons.FieldTheory.Finite