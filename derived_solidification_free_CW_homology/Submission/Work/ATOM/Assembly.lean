import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.QhTransport
import Submission.Work.ATOM.projective_P
import Submission.Work.ATOM.solidCofibrant_atom_of_finite

/-!
# AREA ATOM — assembly: from `g̃^*` bijective to solid-cofibrancy

This file contains the two formal steps of the assembly of `NOTES_LEAD_solid_gaps1.md` §3.5
(apart from the finite case and the explicit null-sequence data themselves):

* `solidCofibrant_of_bijective_pre`: if precomposition with `singleC n g` is bijective on
  `Hom_K(singleC n W, ιC N)` **and** on `Hom_D(Q singleC n W, Q ιC N)` for every complex `N` of
  solid objects, and `singleC n P` is K-projective, then `singleC n W` is solid-cofibrant.
  (This is the "naturality square of `Qh`" argument.)
* `solidCofibrant_singleC_of_iso`: solid-cofibrancy of an atom is invariant under isomorphism of
  the underlying light condensed abelian group, and passes to direct summands; used to transfer
  `Z̃[S]` back to `ℤ[S]` along `ℤ[S] ≅ ℤ[*] ⊞ ℤ̃[S]`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ATOM

/-- `singleC n P` is K-projective, since `P` is projective. -/
instance instIsKProjective_singleC_P' (n : ℤ) : ((singleC n).obj P).IsKProjective :=
  haveI : Projective P := projective_P
  FiniteAtom.isKProjective_singleC P n

/-- The naturality square of `DerivedCategory.Qh`: precomposition with `singleC n g` commutes with
`Qh`.  Consequence: bijectivity of precomposition with `singleC n g` on `Hom_D`-groups, together
with bijectivity of `Qh` out of the K-projective `singleC n P` and on `Hom_K(singleC n P, −)`,
forces bijectivity of `Qh` on `Hom_K(singleC n W, −)`. -/
theorem solidCofibrant_of_bijective_pre (W : LightCondAb) (g : P ⟶ W)
    [CategoryTheory.Limits.PreservesFiniteLimits (MonoidalCategory.tensorLeft P)] (n : ℤ)
    (hK : ∀ N : CochainComplex Solid ℤ,
      Function.Bijective (fun φ : hq.obj ((singleC n).obj W) ⟶
          hq.obj (Submission.Blueprint.ιC.obj N) =>
        hq.map ((singleC n).map g) ≫ φ))
    (hD : ∀ N : CochainComplex Solid ℤ,
      Function.Bijective (fun ψ : DerivedCategory.Q.obj ((singleC n).obj W) ⟶
          DerivedCategory.Q.obj (Submission.Blueprint.ιC.obj N) =>
        DerivedCategory.Q.map ((singleC n).map g) ≫ ψ)) :
    Submission.Blueprint.SolidCofibrant ((singleC n).obj W) := by
  intro N
  have hKN := hK N
  have hDN := hD N
  -- transport the derived bijectivity to `Qh ∘ quotient`
  have hD' : Function.Bijective (fun ψ : DerivedCategory.Qh.obj (hq.obj ((singleC n).obj W)) ⟶
      DerivedCategory.Qh.obj (hq.obj (Submission.Blueprint.ιC.obj N)) =>
        DerivedCategory.Qh.map (hq.map ((singleC n).map g)) ≫ ψ) :=
    bijective_pre_map_qci ((singleC n).map g) hDN
  -- `Qh` is bijective out of the K-projective `singleC n P`
  have hKP : Function.Bijective (DerivedCategory.Qh.map :
      (hq.obj ((singleC n).obj P) ⟶ hq.obj (Submission.Blueprint.ιC.obj N)) → _) :=
    CochainComplex.IsKProjective.Qh_map_bijective ((singleC n).obj P)
      (hq.obj (Submission.Blueprint.ιC.obj N))
  -- the naturality square
  have hsq : (DerivedCategory.Qh.map ∘ (fun φ : hq.obj ((singleC n).obj W) ⟶
        hq.obj (Submission.Blueprint.ιC.obj N) => hq.map ((singleC n).map g) ≫ φ)) =
      ((fun ψ : DerivedCategory.Qh.obj (hq.obj ((singleC n).obj W)) ⟶
          DerivedCategory.Qh.obj (hq.obj (Submission.Blueprint.ιC.obj N)) =>
            DerivedCategory.Qh.map (hq.map ((singleC n).map g)) ≫ ψ) ∘
        DerivedCategory.Qh.map) := by
    funext φ
    simp only [Function.comp_apply]
    exact DerivedCategory.Qh.map_comp (hq.map ((singleC n).map g)) φ
  have h1 : Function.Bijective (DerivedCategory.Qh.map ∘ (fun φ : hq.obj ((singleC n).obj W) ⟶
      hq.obj (Submission.Blueprint.ιC.obj N) => hq.map ((singleC n).map g) ≫ φ)) :=
    hKP.comp hKN
  rw [hsq] at h1
  exact (Function.Bijective.of_comp_iff' hD' DerivedCategory.Qh.map).mp h1

/-- Solid-cofibrancy of an atom is invariant under isomorphism of the underlying light condensed
abelian group: `singleC n` is a functor, and postcomposition with an isomorphism is a bijection. -/
theorem solidCofibrant_singleC_of_iso {A B : LightCondAb} (n : ℤ) (e : A ≅ B)
    (h : Submission.Blueprint.SolidCofibrant ((singleC n).obj A)) :
    Submission.Blueprint.SolidCofibrant ((singleC n).obj B) := by
  intro N
  have he : (singleC n).obj A ≅ (singleC n).obj B := (singleC n).mapIso e
  have hφ : hq.obj ((singleC n).obj A) ≅ hq.obj ((singleC n).obj B) := hq.mapIso he
  have hΦ : Function.Bijective (fun f : hq.obj ((singleC n).obj B) ⟶
      hq.obj (Submission.Blueprint.ιC.obj N) => hφ.hom ≫ f) :=
    ⟨fun f g hfg => by simpa using congrArg (fun z => hφ.inv ≫ z) hfg,
      fun g => ⟨hφ.inv ≫ g, by simp⟩⟩
  have hΨ : Function.Bijective (fun z : DerivedCategory.Qh.obj (hq.obj ((singleC n).obj A)) ⟶
      DerivedCategory.Qh.obj (hq.obj (Submission.Blueprint.ιC.obj N)) =>
        DerivedCategory.Qh.map hφ.inv ≫ z) :=
    ⟨fun f g hfg => by
        have h := congrArg (fun z => DerivedCategory.Qh.map hφ.hom ≫ z) hfg
        rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id] at h
        simpa using h,
      fun z => ⟨DerivedCategory.Qh.map hφ.hom ≫ z, by
        show DerivedCategory.Qh.map hφ.inv ≫ (DerivedCategory.Qh.map hφ.hom ≫ z) = z
        rw [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]; simp⟩⟩
  have heq : (fun f : hq.obj ((singleC n).obj B) ⟶
        hq.obj (Submission.Blueprint.ιC.obj N) => DerivedCategory.Qh.map f) =
      (fun z : DerivedCategory.Qh.obj (hq.obj ((singleC n).obj A)) ⟶
          DerivedCategory.Qh.obj (hq.obj (Submission.Blueprint.ιC.obj N)) =>
            DerivedCategory.Qh.map hφ.inv ≫ z) ∘
        ((fun g : hq.obj ((singleC n).obj A) ⟶ hq.obj (Submission.Blueprint.ιC.obj N) =>
            DerivedCategory.Qh.map g) ∘
          (fun f : hq.obj ((singleC n).obj B) ⟶ hq.obj (Submission.Blueprint.ιC.obj N) =>
            hφ.hom ≫ f)) := by
    funext f
    simp only [Function.comp_apply]
    rw [DerivedCategory.Qh.map_comp, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    simp
  rw [heq]
  exact hΨ.comp ((h N).comp hΦ)

end Work.ATOM
