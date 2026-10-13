import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSAMR.Main
import Submission.Work.DSEQP.PerfModel
import Submission.Work.DSEQP.almostAcyc_zero_gen
import Submission.Work.DSEQP.almostAcyc_succ
import Submission.Work.DSEQP.exists_chainMap_perf

open CategoryTheory AlgebraicGeometry Limits Opposite
open DSMap DSMap.Mix DSMap.Mix2

universe a

namespace Work.DSEQP

theorem eqp_perfModel_proved (A : Type a) [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p]
    (X : Scheme.{a}) [IsIntegral X] (f : X ⟶ Spec (.of A)) [IsSeparated f] {ι : Type a}
    [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) (g : A)
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : IsFinFreeModelU A X f U P ε)
    (htors : ∀ q : ℕ, ∃ N : ℕ, ∀ z : (cech A X f U).X (q + 1),
      ((cech A X f U).d (q + 1) (q + 2)).hom z = 0 →
        ∃ y : (cech A X f U).X q, ((cech A X f U).d q (q + 1)).hom y = g ^ N • z) :
    ∃ (W : Type a) (_ : CommRing W) (_ : CharP W p) (_ : PerfectRing W p) (ψW : Γ(X, ⊤) →+* W)
      (K : CochainComplex (ModuleCat.{a} W) ℕ) (eK : ModuleCat.of W W ⟶ K.X 0)
      (ρ : P ⟶ ((ModuleCat.restrictScalars (ψW.comp (phi A X f))).mapHomologicalComplex _).obj
        (K.extend ComplexShape.embeddingUpNat)),
      Function.Injective ψW ∧
      (∀ w : W, ∃ (n : ℕ) (x : Γ(X, ⊤)), w = ((frobeniusEquiv W p).symm^[n]) (ψW x)) ∧
      AlmostAcyc (fun k => ((frobeniusEquiv W p).symm^[k]) (ψW (phi A X f g))) ⊥ K eK ∧
      ε ≫ ρ.f 0 ≫ (ModuleCat.restrictScalars (ψW.comp (phi A X f))).map
          (K.extendXIso ComplexShape.embeddingUpNat (i := 0) rfl).hom =
        unitA (ψW.comp (phi A X f)) ≫ (ModuleCat.restrictScalars (ψW.comp (phi A X f))).map eK := by
  let S : PerfSetup A p X f := ⟨CharP.cast_eq_zero A p⟩
  haveI hcharP : CharP S.W p := S.charP_W
  haveI hperf : PerfectRing S.W p := S.perfectRing_W
  obtain ⟨ρ, hρ⟩ := exists_chainMap_perf A p X f S U P ε hP
  refine ⟨S.W, inferInstance, S.charP_W, S.perfectRing_W, S.ψW, S.K U, S.eK U, ρ,
    S.ψW_injective, S.exists_frobEquiv_symm_iter, ?_, hρ⟩
  refine S.almostAcyc_perf U g (fun w hw k => S.almostAcyc_one U hcov g w hw k)
    (fun ϖ z hz => almostAcyc_zero_gen A p X f S U hcov ϖ z hz)
    (fun q k z hz => almostAcyc_succ A p X f S U g htors q k z hz)

end Work.DSEQP
