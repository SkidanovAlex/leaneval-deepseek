import Mathlib
import Submission.NK.GlobalCFTdeep.Transport.IdeleEquiv
import Submission.NK.GlobalCFTdeep.Transport.NormTransportLocal
import Submission.NK.GlobalCFTdeep.Transport.liesOver_placeEquiv
import Submission.NK.GlobalCFTdeep.Transport.fiberInfinite_map_placeEquiv
import Submission.NK.GlobalCFTdeep.Transport.primesOverFinite_map_placeEquiv

/-!
# Naturality of the idèle norm under the idèle transport

Given a compatible pair of ring equivalences `eK : K ≃+* K'`, `eL : L ≃+* L'` of number fields
(`hcomp : ∀ x, eL (algebraMap K L x) = algebraMap K' L' (eK x)`), the idèle transport
`NK.GlobalCFTdeep.Transport.ideleEquiv` (built in `Transport/IdeleEquiv.lean` from the local
field transport `NormTransport.localFieldIso`) commutes with the idèle norm `N_{L/K}`:

  `ideleEquiv eK ∘ N_{L/K} = N_{L'/K'} ∘ ideleEquiv eL`.

Proof route (componentwise, using the evaluation lemma `ideleEquiv_apply_placeEquiv`,
`ideleEquiv e x (placeEquiv e v) = Units.map (localFieldEquiv e v).toMonoidHom (x v)`).
Both sides are idèles of `K'`; compare them at a place `placeEquiv eK v`, `v : Place K`:

* at an archimedean place `v = ofInfinite w` the components are the products of local norms over
  the fibre `Place.fiberInfinite w`, respectively over the fibre of `placeEquiv eK v` in `L'`;
* at a nonarchimedean one they are the products over `Place.primesOverFinite Q`, respectively
  over the primes of `L'` above `placeEquiv eK Q`.
* The fibres correspond exactly under `infinitePlaceEquiv eL` / `finitePlaceEquiv eL`
  (`fiberInfinite_map_placeEquiv`, `primesOverFinite_map_placeEquiv`), so the two products can be
  compared term by term (`Finset.prod_bij`), and the individual factors agree by the local norm
  commutation `NormTransport.localNormFinite_commute` / `NormTransport.localNormInfinite_commute`
  (proved from Mathlib's `Algebra.norm_eq_of_equiv_equiv` and the density arguments in
  `Transport/NormTransportLocal.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.Transport

open NK.GlobalCFT

theorem ideleEquiv_normIdeleHom {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L'] [FiniteDimensional K' L'] (eK : K ≃+* K') (eL : L ≃+* L') (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) (y : NK.GlobalCFT.Idele L) : NK.GlobalCFTdeep.Transport.ideleEquiv eK (NK.GlobalCFT.Idele.normIdeleHom K L y) = NK.GlobalCFT.Idele.normIdeleHom K' L' (NK.GlobalCFTdeep.Transport.ideleEquiv eL y) := by
  refine Idele.ext fun v => ?_
  obtain ⟨v₀, rfl⟩ := (placeEquiv eK).surjective v
  rw [ideleEquiv_apply_placeEquiv]
  cases v₀ with
  | inl w =>
      have hfib : Place.fiberInfinite (K := K') (L := L') (infinitePlaceEquiv eK w) =
          (Place.fiberInfinite (K := K) (L := L) w).map
            (infinitePlaceEquiv eL).toEmbedding :=
        (fiberInfinite_map_placeEquiv eK eL hcomp w).symm
      change Units.map (NormTransport.localFieldIso eK (Place.ofInfinite w)).toMonoidHom
            ((Idele.normIdeleHom K L y) (Place.ofInfinite w)) =
          (Idele.normIdeleHom K' L' (ideleEquiv eL y))
            (Place.ofInfinite (infinitePlaceEquiv eK w))
      simp only [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofInfinite]
      rw [map_prod]
      refine Finset.prod_bij (fun a _ =>
        ⟨infinitePlaceEquiv eL a.1, ?_⟩) ?_ ?_ ?_ ?_
      · rw [hfib]; exact Finset.mem_map_of_mem _ a.2
      · intro a ha; exact Finset.mem_attach _ _
      · intro a₁ ha₁ a₂ ha₂ heq
        exact Subtype.ext ((infinitePlaceEquiv eL).injective (congrArg Subtype.val heq))
      · intro b hb
        obtain ⟨c, hc⟩ := b
        refine ⟨⟨(infinitePlaceEquiv eL).symm c, ?_⟩, Finset.mem_attach _ _, ?_⟩
        · have hc' : c ∈ (Place.fiberInfinite (K := K) (L := L) w).map
              (infinitePlaceEquiv eL).toEmbedding := by
            rw [← hfib]; exact hc
          exact Finset.mem_map_equiv.mp hc'
        · exact Subtype.ext ((infinitePlaceEquiv eL).apply_symm_apply c)
      · intro a ha
        have hw : a.1.LiesOver w :=
          (Place.mem_fiberInfinite (K := K) (L := L) (v := w) (w := a.1)).mp a.2
        have hw' : (infinitePlaceEquiv eL a.1).LiesOver (infinitePlaceEquiv eK w) :=
          (infinitePlaceEquiv_liesOver_iff eK eL hcomp a.1 w).mp hw
        have hev : (ideleEquiv eL y) (Place.ofInfinite (infinitePlaceEquiv eL a.1)) =
            Units.map (NormTransport.localFieldIso eL (Place.ofInfinite a.1)).toMonoidHom
              (y (Place.ofInfinite a.1)) :=
          ideleEquiv_apply_placeEquiv eL y (Place.ofInfinite a.1)
        rw [hev]
        exact NormTransport.localNormInfinite_commute eK eL hcomp a.1 w hw hw'
          (y (Place.ofInfinite a.1))
  | inr Q =>
      have hfib : Place.primesOverFinite (K := K') (L := L') (finitePlaceEquiv eK Q) =
          (Place.primesOverFinite (K := K) (L := L) Q).map
            (finitePlaceEquiv eL).toEmbedding :=
        (primesOverFinite_map_placeEquiv eK eL hcomp Q).symm
      change Units.map (NormTransport.localFieldIso eK (Place.ofFinite Q)).toMonoidHom
            ((Idele.normIdeleHom K L y) (Place.ofFinite Q)) =
          (Idele.normIdeleHom K' L' (ideleEquiv eL y))
            (Place.ofFinite (finitePlaceEquiv eK Q))
      simp only [Idele.normIdeleHom_apply, Idele.normIdeleFun_ofFinite]
      rw [map_prod]
      refine Finset.prod_bij (fun a _ =>
        ⟨finitePlaceEquiv eL a.1, ?_⟩) ?_ ?_ ?_ ?_
      · rw [hfib]; exact Finset.mem_map_of_mem _ a.2
      · intro a ha; exact Finset.mem_attach _ _
      · intro a₁ ha₁ a₂ ha₂ heq
        exact Subtype.ext ((finitePlaceEquiv eL).injective (congrArg Subtype.val heq))
      · intro b hb
        obtain ⟨c, hc⟩ := b
        refine ⟨⟨(finitePlaceEquiv eL).symm c, ?_⟩, Finset.mem_attach _ _, ?_⟩
        · have hc' : c ∈ (Place.primesOverFinite (K := K) (L := L) Q).map
              (finitePlaceEquiv eL).toEmbedding := by
            rw [← hfib]; exact hc
          exact Finset.mem_map_equiv.mp hc'
        · exact Subtype.ext ((finitePlaceEquiv eL).apply_symm_apply c)
      · intro a ha
        have hq : a.1.asIdeal.LiesOver Q.asIdeal :=
          (Place.mem_primesOverFinite (K := K) (L := L) (Q := Q) (q := a.1)).mp a.2
        have hq' : (finitePlaceEquiv eL a.1).asIdeal.LiesOver
            (finitePlaceEquiv eK Q).asIdeal :=
          (finitePlaceEquiv_liesOver_iff eK eL hcomp a.1 Q).mp hq
        have hev : (ideleEquiv eL y) (Place.ofFinite (finitePlaceEquiv eL a.1)) =
            Units.map (NormTransport.localFieldIso eL (Place.ofFinite a.1)).toMonoidHom
              (y (Place.ofFinite a.1)) :=
          ideleEquiv_apply_placeEquiv eL y (Place.ofFinite a.1)
        rw [hev]
        exact NormTransport.localNormFinite_commute eK eL hcomp a.1 Q hq hq'
          (y (Place.ofFinite a.1))

end NK.GlobalCFTdeep.Transport
