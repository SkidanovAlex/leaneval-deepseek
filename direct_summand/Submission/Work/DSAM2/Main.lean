import Submission.Work.DSAM2.MatrixDescent
import Submission.Work.DSAM2.modSplit_iff_mulVec
import Submission.Work.DSAM2.Basic

/-!
# DSAM2: the deliverable `DSMap.Mix.modSplit_descent_proved`

Node **AM2** of the MIX design (`sources/dsmap/direct_summand_mix_design.md`): almost-splitting
descent along a map that is faithfully flat modulo the ideal.

`ModSplit P ε ψ J c` means that the `J`-adic quotient `S ⧸ J` of an `A`-algebra `S` receives an
`S`-linear map `s : S ⊗[A] (P.X 0) ⟶ S ⧸ J` killing the image of the differential `d⁻¹` and
carrying the unit `ε 1` to `c`.  The theorem below says that such a splitting over `D'` descends
to `D` when `D ⧸ I → D' ⧸ I·D'` is faithfully flat.

The proof reduces, in bases of `P.X 0` and `P.X (-1)` (`modSplit_iff_mulVec`), to the descent of
solvability of a linear system along a faithfully flat algebra extension
(`exists_mulVec_iff_of_faithfullyFlat`), whose obstruction computation is the classical one:
the cokernel of a matrix commutes with base change, and faithful flatness detects vanishing.
The degenerate case where `A` (hence `D` and `D ⧸ I`) is the zero ring is handled directly by
`Work.DSAM2.modSplit_of_subsingleton`: for a free module over the zero ring there need not exist a
finite basis, so `Module.finBasis` does not apply there.
-/

open CategoryTheory AlgebraicGeometry IsLocalRing Limits

namespace DSMap.Mix

universe a

set_option linter.style.haveILetI false in
set_option linter.unusedVariables false in
/-- **AM2** Almost-splitting descends along a faithfully flat map: if a finite free model `(P, ε)`
of `RΓ(X, 𝒪)` splits modulo `I · D'` over `D'` up to the factor `algebraMap D D' c`, then it splits
modulo `I` over `D`, up to the factor `c`, provided `D ⧸ I → D' ⧸ I · D'` is faithfully flat. -/
theorem modSplit_descent_proved {A : Type a} [CommRing A] (P : CochainComplex (ModuleCat.{a} A) ℤ)
    (hP : IsBddFinFree P) (ε : ModuleCat.of A A ⟶ P.X 0) (hε : ∀ k, ε ≫ P.d 0 k = 0)
    {D D' : Type a} [CommRing D] [CommRing D'] (ψ : A →+* D) [Algebra D D'] (I : Ideal D)
    (hff : Module.FaithfullyFlat (D ⧸ I) (D' ⧸ I.map (algebraMap D D'))) (c : D)
    (h : ModSplit P ε ((algebraMap D D').comp ψ) (I.map (algebraMap D D')) (algebraMap D D' c)) :
    ModSplit P ε ψ I c := by
  by_cases hA : Nontrivial A
  · -- Main case: `A` is nontrivial, so `P.X 0` and `P.X (-1)` have finite bases.
    haveI := hA
    haveI : Module.Free A (P.X 0) := (hP.1 0).1
    haveI : Module.Finite A (P.X 0) := (hP.1 0).2
    haveI : Module.Free A (P.X (-1)) := (hP.1 (-1)).1
    haveI : Module.Finite A (P.X (-1)) := (hP.1 (-1)).2
    let b0 := Module.finBasis A (P.X 0)
    let b1 := Module.finBasis A (P.X (-1))
    let Mmat : Matrix (Option (Fin (Module.finrank A (P.X (-1))))) (Fin (Module.finrank A (P.X 0)))
        (D ⧸ I) :=
      (Work.DSAM2.systemMatrix P ε b0 b1).map (fun x => Ideal.Quotient.mk I (ψ x))
    let yvec : Option (Fin (Module.finrank A (P.X (-1)))) → D ⧸ I :=
      fun k => Ideal.Quotient.mk I (Work.DSAM2.systemRHS c k)
    rw [Work.DSAM2.modSplit_iff_mulVec P ε ψ I c b0 b1]
    rw [Work.DSAM2.modSplit_iff_mulVec P ε ((algebraMap D D').comp ψ)
      (I.map (algebraMap D D')) (algebraMap D D' c) b0 b1] at h
    obtain ⟨q', hq'⟩ := h
    refine (Work.DSAM2.exists_mulVec_iff_of_faithfullyFlat (B := D ⧸ I)
      (B' := D' ⧸ I.map (algebraMap D D')) (M := Mmat) (y := yvec)).mpr ?_
    refine ⟨q', ?_⟩
    -- The system over `D' ⧸ I·D'` produced by `h` is the base change of the system over `D ⧸ I`.
    have hM : Mmat.map (algebraMap (D ⧸ I) (D' ⧸ I.map (algebraMap D D')))
        = (Work.DSAM2.systemMatrix P ε b0 b1).map
            (fun x => Ideal.Quotient.mk (I.map (algebraMap D D')) (((algebraMap D D').comp ψ) x)) := by
      ext i j
      simp only [Mmat, Matrix.map_apply]
      exact Ideal.Quotient.algebraMap_quotient_map_quotient (p := I)
        (ψ (Work.DSAM2.systemMatrix P ε b0 b1 i j))
    have hy : (fun k => algebraMap (D ⧸ I) (D' ⧸ I.map (algebraMap D D')) (yvec k))
        = (fun k => Ideal.Quotient.mk (I.map (algebraMap D D'))
            (Work.DSAM2.systemRHS (algebraMap D D' c) k)) := by
      funext k
      cases k with
      | none => exact Ideal.Quotient.algebraMap_quotient_map_quotient (p := I) c
      | some j => simp [yvec, Work.DSAM2.systemRHS]
    rw [hM, hy]
    exact hq'
  · -- Degenerate case: `A` is the zero ring, hence so are `D` and `D ⧸ I`.
    exact Work.DSAM2.modSplit_of_subsingleton P ε ψ I c
      (not_nontrivial_iff_subsingleton.mp hA)

end DSMap.Mix

/-- The deliverable has exactly the frozen statement of `DSMap.Mix.modSplit_descent`. -/
example : @DSMap.Mix.modSplit_descent_proved = @DSMap.Mix.modSplit_descent := rfl
