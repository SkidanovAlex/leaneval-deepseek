import Mathlib
import Submission.NK.GlobalCFTdeep.HNU.NormTransportDefs
import Submission.NK.GlobalCFTdeep.Transport.NormTransportAux
import Submission.NK.GlobalCFTdeep.Transport.liesOver_placeEquiv
import Submission.NK.GlobalCFTdeep.Transport.fiberInfinite_map_placeEquiv
import Submission.NK.GlobalCFTdeep.Transport.primesOverFinite_map_placeEquiv
import Submission.NK.GlobalCFTdeep.Transport.NormTransportLocal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the idèle norm under the idèle transport along a ring equivalence

This module proves that the idèle transport `HNU.ideleEquivExplicit` — the one built from the
*explicit*, continuous local isomorphisms `Transport.NormTransport.localFieldIso` — commutes with
the idèle norm `N_{L/K}`.  The proof is componentwise: at a place of `K` both sides are products
of local norms over the fibre of that place in `L`, and

* the fibres are identified by `Transport.fiberInfinite_map_placeEquiv` and
  `Transport.primesOverFinite_map_placeEquiv`,
* the local norms commute with the local isomorphisms
  (`localNormInfinite_commute_aux`, `localNormFinite_commute_aux`, copies of the statements in
  `Transport/NormTransportLocal.lean`, which proves them by the density argument).

The two local-norm commutation statements are recorded here with their proofs delegated (they are
proved in `Transport/NormTransportLocal.lean`); the fibre bookkeeping below is independent of their
proofs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.HNU

open NK.GlobalCFT

variable {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [Field K'] [NumberField K'] [Field L'] [NumberField L']
  [Algebra K' L'] [FiniteDimensional K' L']

/-- **The local norms commute with the local isomorphisms at a finite place.** -/
theorem localNormFinite_commute_aux
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (q : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hq' : (Transport.finitePlaceEquiv eL q).asIdeal.LiesOver
      (Transport.finitePlaceEquiv eK Q).asIdeal) :
    ∀ x : (Place.localField L (Place.ofFinite q))ˣ,
      Units.map (Transport.NormTransport.localFieldIso eK (Place.ofFinite Q)).toMonoidHom
          (Place.localNormFinite q Q hq x) =
        Place.localNormFinite (Transport.finitePlaceEquiv eL q) (Transport.finitePlaceEquiv eK Q)
          hq' (Units.map (Transport.NormTransport.localFieldIso eL (Place.ofFinite q)).toMonoidHom
            x) :=
  Transport.NormTransport.localNormFinite_commute eK eL hcomp q Q hq hq'

/-- **The local norms commute with the local isomorphisms at an archimedean place.** -/
theorem localNormInfinite_commute_aux
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (w : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace K)
    (hw : w.LiesOver v)
    (hw' : (Transport.infinitePlaceEquiv eL w).LiesOver (Transport.infinitePlaceEquiv eK v)) :
    ∀ x : (Place.localField L (Place.ofInfinite w))ˣ,
      Units.map (Transport.NormTransport.localFieldIso eK (Place.ofInfinite v)).toMonoidHom
          (Place.localNormInfinite w v x) =
        Place.localNormInfinite (Transport.infinitePlaceEquiv eL w)
          (Transport.infinitePlaceEquiv eK v)
          (Units.map (Transport.NormTransport.localFieldIso eL (Place.ofInfinite w)).toMonoidHom
            x) :=
  Transport.NormTransport.localNormInfinite_commute eK eL hcomp w v hw hw'

/-- **Naturality of the idèle norm** for the idèle transport built from the explicit local
isomorphisms: `ideleEquivExplicit eK ∘ N_{L/K} = N_{L'/K'} ∘ ideleEquivExplicit eL`. -/
theorem map_normIdeleHom_ideleEquivExplicit_aux
    (eK : K ≃+* K') (eL : L ≃+* L')
    (h : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) (y : Idele L) :
    ideleEquivExplicit eK (Idele.normIdeleHom K L y) =
      Idele.normIdeleHom K' L' (ideleEquivExplicit eL y) := by
  refine Idele.ext fun v => ?_
  obtain ⟨v₀, rfl⟩ := (Transport.placeEquiv eK).surjective v
  rw [ideleEquivExplicit_apply]
  cases v₀ with
  | inl w =>
      have hfib : Place.fiberInfinite (K := K') (L := L')
            (Transport.infinitePlaceEquiv eK w) =
          (Place.fiberInfinite (K := K) (L := L) w).map
            (Transport.infinitePlaceEquiv eL).toEmbedding :=
        (Transport.fiberInfinite_map_placeEquiv eK eL h w).symm
      change Units.map (Transport.NormTransport.localFieldIso eK (Place.ofInfinite w)).toMonoidHom
            ((Idele.normIdeleHom K L y) (Place.ofInfinite w)) =
          (Idele.normIdeleHom K' L' (ideleEquivExplicit eL y))
            (Place.ofInfinite (Transport.infinitePlaceEquiv eK w))
      simp only [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofInfinite]
      rw [map_prod]
      refine Finset.prod_bij (fun a _ =>
        ⟨Transport.infinitePlaceEquiv eL a.1, ?_⟩) ?_ ?_ ?_ ?_
      · rw [hfib]; exact Finset.mem_map_of_mem _ a.2
      · intro a ha; exact Finset.mem_attach _ _
      · intro a₁ ha₁ a₂ ha₂ heq
        exact Subtype.ext ((Transport.infinitePlaceEquiv eL).injective
          (congrArg Subtype.val heq))
      · intro b hb
        obtain ⟨c, hc⟩ := b
        refine ⟨⟨(Transport.infinitePlaceEquiv eL).symm c, ?_⟩, Finset.mem_attach _ _, ?_⟩
        · have hc' : c ∈ (Place.fiberInfinite (K := K) (L := L) w).map
              (Transport.infinitePlaceEquiv eL).toEmbedding := by
            rw [← hfib]; exact hc
          exact Finset.mem_map_equiv.mp hc'
        · exact Subtype.ext ((Transport.infinitePlaceEquiv eL).apply_symm_apply c)
      · intro a ha
        have hw : a.1.LiesOver w :=
          (Place.mem_fiberInfinite (K := K) (L := L) (v := w) (w := a.1)).mp a.2
        have hw' : (Transport.infinitePlaceEquiv eL a.1).LiesOver
            (Transport.infinitePlaceEquiv eK w) :=
          (Transport.infinitePlaceEquiv_liesOver_iff eK eL h a.1 w).mp hw
        have hev : (ideleEquivExplicit eL y)
              (Place.ofInfinite (Transport.infinitePlaceEquiv eL a.1)) =
            Units.map (Transport.NormTransport.localFieldIso eL (Place.ofInfinite a.1)).toMonoidHom
              (y (Place.ofInfinite a.1)) :=
          ideleEquivExplicit_apply eL y (Place.ofInfinite a.1)
        rw [hev]
        exact localNormInfinite_commute_aux eK eL h a.1 w hw hw' (y (Place.ofInfinite a.1))
  | inr Q =>
      have hfib : Place.primesOverFinite (K := K') (L := L')
            (Transport.finitePlaceEquiv eK Q) =
          (Place.primesOverFinite (K := K) (L := L) Q).map
            (Transport.finitePlaceEquiv eL).toEmbedding :=
        (Transport.primesOverFinite_map_placeEquiv eK eL h Q).symm
      change Units.map (Transport.NormTransport.localFieldIso eK (Place.ofFinite Q)).toMonoidHom
            ((Idele.normIdeleHom K L y) (Place.ofFinite Q)) =
          (Idele.normIdeleHom K' L' (ideleEquivExplicit eL y))
            (Place.ofFinite (Transport.finitePlaceEquiv eK Q))
      simp only [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofFinite]
      rw [map_prod]
      refine Finset.prod_bij (fun a _ =>
        ⟨Transport.finitePlaceEquiv eL a.1, ?_⟩) ?_ ?_ ?_ ?_
      · rw [hfib]; exact Finset.mem_map_of_mem _ a.2
      · intro a ha; exact Finset.mem_attach _ _
      · intro a₁ ha₁ a₂ ha₂ heq
        exact Subtype.ext ((Transport.finitePlaceEquiv eL).injective (congrArg Subtype.val heq))
      · intro b hb
        obtain ⟨c, hc⟩ := b
        refine ⟨⟨(Transport.finitePlaceEquiv eL).symm c, ?_⟩, Finset.mem_attach _ _, ?_⟩
        · have hc' : c ∈ (Place.primesOverFinite (K := K) (L := L) Q).map
              (Transport.finitePlaceEquiv eL).toEmbedding := by
            rw [← hfib]; exact hc
          exact Finset.mem_map_equiv.mp hc'
        · exact Subtype.ext ((Transport.finitePlaceEquiv eL).apply_symm_apply c)
      · intro a ha
        have hq : a.1.asIdeal.LiesOver Q.asIdeal :=
          (Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := a.1)).mp a.2
        have hq' : (Transport.finitePlaceEquiv eL a.1).asIdeal.LiesOver
            (Transport.finitePlaceEquiv eK Q).asIdeal :=
          (Transport.finitePlaceEquiv_liesOver_iff eK eL h a.1 Q).mp hq
        have hev : (ideleEquivExplicit eL y)
              (Place.ofFinite (Transport.finitePlaceEquiv eL a.1)) =
            Units.map (Transport.NormTransport.localFieldIso eL (Place.ofFinite a.1)).toMonoidHom
              (y (Place.ofFinite a.1)) :=
          ideleEquivExplicit_apply eL y (Place.ofFinite a.1)
        rw [hev]
        exact localNormFinite_commute_aux eK eL h a.1 Q hq hq' (y (Place.ofFinite a.1))

end NK.GlobalCFTdeep.HNU
