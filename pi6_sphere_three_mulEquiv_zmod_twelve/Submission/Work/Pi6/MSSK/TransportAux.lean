import Mathlib
import Submission.Work.Pi6.MSSK.CapAux
import Submission.Work.Pi6.MSSK.LastEdge
import Submission.Work.Pi6.MSSK.VertexBridges
import Submission.Work.Pi6.MSSK.CapThetaBasic
import Submission.Work.Pi6.MSSK.exists_bdry_lift_of_pieceAlong_cycle
import Submission.Work.SSSR.ezSimplexZero_chain_class
import Submission.Work.Pi6.MSSK.peel_aux
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Auxiliaries for the cap/transport induction

* `nextDownEq` — the successor of the homology complex shape on `ℕ`;
* `castElem_d` — the differential commutes with degree transport;
* `triv_eqToIso` — the fibre trivialisation commutes with the transport along an equality of
  base points;
* `exists_lift_of_cokernel_π_f_eq_zero` — an element killed by the degreewise cokernel projection
  lies in the range of the degreewise map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

noncomputable section

/-- The successor in the homology complex shape on `ℕ` is the predecessor. -/
theorem nextDownEq (i : ℕ) : (ComplexShape.down ℕ).next i = i - 1 := by
  rcases i with _ | i
  · refine ComplexShape.next_eq_self' (ComplexShape.down ℕ) 0 (fun k hk => ?_)
    rw [ComplexShape.down_Rel] at hk
    omega
  · rw [ComplexShape.next_eq' (ComplexShape.down ℕ)
      (ComplexShape.down_mk (i+1) i (rfl : i + 1 = i + 1))]
    omega

/-- Degree transport commutes with the differential. -/
lemma castElem_d {R : Type} [CommRing R] (K : ChainComplex (ModuleCat R) ℕ) {i j : ℕ} (h : i = j)
    (x : K.X i) :
    K.d j (j - 1) (Work.SSSR.castElem K h x)
      = Work.SSSR.castElem K (congrArg (fun n : ℕ => n - 1) h) (K.d i (i - 1) x) := by
  cases h
  rfl

/-- The fibre trivialisation commutes with the transport along an equality of base points. -/
lemma triv_eqToIso {R : Type} [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hsconn : Work.SSSR.PiS.SimplyConn B (p e₀)) (k : ℕ) {b b' : B} (h : b = b') :
    (CategoryTheory.eqToIso (congrArg (fun x : B =>
        Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p x) k) h)).hom
      ≫ (Work.SSSR.triv p e₀ hfib hsconn k b').hom
      = (Work.SSSR.triv p e₀ hfib hsconn k b).hom := by
  subst h
  simp

/-- Element-level form of `triv_eqToIso`. -/
lemma triv_eqToIso_apply {R : Type} [CommRing R] [Nontrivial R] {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (hfib : Work.SSSR.StemsB.IsSerreFibration p)
    (hsconn : Work.SSSR.PiS.SimplyConn B (p e₀)) (k : ℕ) {b b' : B} (h : b = b')
    (y : Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p b') k) :
    (Work.SSSR.triv p e₀ hfib hsconn k b).hom.hom
        ((CategoryTheory.eqToIso (congrArg (fun x : B =>
          Work.SSSR.PiS.HZ R (Work.SSSR.StemsB.fibre p x) k) h)).inv.hom y)
      = (Work.SSSR.triv p e₀ hfib hsconn k b').hom.hom y := by
  subst h
  simp

/-- An element killed by the degreewise cokernel projection of a morphism of chain complexes lies
in the range of the degreewise map. -/
lemma exists_lift_of_cokernel_π_f_eq_zero {R : Type} [Ring R] {A X : ChainComplex (ModuleCat R) ℕ}
    (i : A ⟶ X) {n : ℕ} {x : X.X n}
    (h : (ModuleCat.Hom.hom ((cokernel.π i).f n)) x = 0) :
    ∃ y : A.X n, (ModuleCat.Hom.hom (i.f n)) y = x := by
  haveI : PreservesColimit (parallelPair i 0)
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n) :=
    HomologicalComplex.eval_preservesColimit_of_hasCokernel_f i n
  have h2 : (ModuleCat.Hom.hom (cokernel.π (i.f n))) x = 0 := by
    have hiso := CategoryTheory.Limits.PreservesCokernel.π_iso_hom
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n) i
    have hh := congrArg (fun (g : (HomologicalComplex.eval (ModuleCat R)
        (ComplexShape.down ℕ) n).obj X ⟶
        cokernel ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n).map i)) =>
      (ModuleCat.Hom.hom g) x) hiso
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
    simp only [HomologicalComplex.eval_map] at hh
    calc (ModuleCat.Hom.hom (cokernel.π (i.f n))) x
        = (ModuleCat.Hom.hom (CategoryTheory.Limits.PreservesCokernel.iso
              (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n) i).hom)
            ((ModuleCat.Hom.hom ((cokernel.π i).f n)) x) := hh.symm
      _ = (ModuleCat.Hom.hom (CategoryTheory.Limits.PreservesCokernel.iso
              (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n) i).hom) 0 := by
            rw [h]
      _ = 0 := map_zero _
  obtain ⟨y, hy⟩ := Work.Pi6.MSSK.exists_eq_of_cokernel_π_eq_zero R (i.f n) h2
  exact ⟨y, hy⟩

end

end Work.Pi6.MSSK
