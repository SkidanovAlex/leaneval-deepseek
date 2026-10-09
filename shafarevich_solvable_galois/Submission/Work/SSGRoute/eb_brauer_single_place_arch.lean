import Mathlib
import Submission.Work.SSGRoute.E8Helpers
import Submission.Work.SSGRoute.E8Defs
import Submission.Work.SSGRoute.eb_loc_card
import Submission.Work.SSGRoute.eb_locUnits_resToGal
import Submission.Work.SSGRoute.eb_local_range
import Submission.Work.SSGRoute.eb_arch_aux
import Submission.Work.SSGRoute.eb_arch_beta_local
import Submission.Work.SSGRoute.eb_arch_gamma_local
import Submission.Work.SSGRoute.eb_arch_infl_injective
import Submission.Work.SSGRoute.eb_arch_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **The archimedean case of `Work.SSGRoute.brauer_single_place` (E8', piece P4).** This is the case `w₀` infinite of the target theorem: a class of `Br(L/k) = H²(Gal(L/k), Lˣ)` whose localisation vanishes at every place outside the Galois orbit of an *archimedean* place `w₀` is zero. (Then the target assembles as `rcases w₀ with w | ŵ; exact arch …; exact finite …`.) See the docstring of the request for the intended route: auxiliary cyclic cyclotomic `M/k` with `M` imaginary over the real place `v₀ = w₀` below (e.g. `M = k(ζ_l)`, `l ≥ 3`), the (trivial) archimedean analogue of `Work.SSGRoute.eb_crux` via `Nat.card (Stab_{Gal(E/M)}(ŵ)) = 1` and `Commons…natCard_nsmul_H2_eq_zero`, the square `Work.SSGRoute.eb_locUnits_resToGal`, `NK.HR2.locUnits_inflation_eq_zero_iff`, `NK.GlobalCFTdeep.hbnUnits (M) (E)`, `NK.HR2.exists_cycClassOf_of_res_eq_zero`, `Work.SSGRoute.brauer_single_place_cyclic` at the level `M/k`, and the injectivity of the inflation `H²(Gal(L/k),Lˣ) → H²(Gal(E/k),Eˣ)` (Hilbert 90 for `E/L`, `Commons…H2_inflation_injective_of_subsingleton_H1`). -/
theorem eb_brauer_single_place_arch (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] (a : groupCohomology (NK.HassePrinciple.unitsRep k L) 2) (w₀ : NumberField.InfinitePlace L) (h : ∀ w : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • NK.GlobalCFT.Place.ofInfinite w₀ ≠ w) → (NK.HassePrinciple.locUnits k L w).hom a = 0) : a = 0 := by
  classical
  -- the auxiliary cyclic cyclotomic tower `k ⊆ L ⊆ E`, `k ⊆ M ⊆ E` with `M = k(ζ_3)`
  obtain ⟨M, E, hMf, hMN, hEf, hEN, hkM, hkE, hLE, hME, hstLE, hstME, hfdM, hfdE, hgalM, hgalE,
    hcycM, hcycExt, hgen, hMcomplex⟩ := eb_arch_aux k L 3 (by norm_num) (by norm_num)
  letI : Field M := hMf
  letI : NumberField M := hMN
  letI : Field E := hEf
  letI : NumberField E := hEN
  letI : Algebra k M := hkM
  letI : Algebra k E := hkE
  letI : Algebra L E := hLE
  letI : Algebra M E := hME
  letI : IsScalarTower k L E := hstLE
  letI : IsScalarTower k M E := hstME
  letI : FiniteDimensional k M := hfdM
  letI : FiniteDimensional k E := hfdE
  letI : IsGalois k M := hgalM
  letI : IsGalois k E := hgalE
  letI : IsCyclic (M ≃ₐ[k] M) := hcycM
  haveI : FiniteDimensional M E := Module.Finite.of_restrictScalars_finite k M E
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois k M E
  -- the class `β = res_{E/M}(inf_E a)`
  let β : groupCohomology (NK.HassePrinciple.unitsRep M E) 2 :=
    (NK.NUV2.ChebAux.Transfer.resToGal k M E).hom
      ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a)
  have hβ : ∀ ŵ : NK.GlobalCFT.Place E, (NK.HassePrinciple.locUnits M E ŵ).hom β = 0 :=
    fun ŵ => eb_arch_beta_local (k := k) (L := L) (M := M) (E := E) w₀ a h hMcomplex ŵ
  have hβ0 : β = 0 := NK.GlobalCFTdeep.hbnUnits (F := M) (E := E) β hβ
  -- Galois descent to the cyclic level `M/k`
  obtain ⟨gM, hgM⟩ := IsCyclic.exists_generator (α := M ≃ₐ[k] M)
  obtain ⟨b, hb⟩ := NK.HR2.exists_cycClassOf_of_res_eq_zero (K := k) (L := L) (M := M) (E := E)
    hgen gM hgM ((NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a) hβ0
  -- the cyclic class is locally trivial outside `v₀`, hence zero
  have hγ : NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := k) (F := M) gM hgM b = 0 :=
    eb_arch_cyclic k M (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := k) (F := M) gM hgM b)
      (NK.GlobalCFT.Place.ofInfinite (w₀.comap (algebraMap k L)))
      (fun W hW => eb_arch_gamma_local (k := k) (L := L) (M := M) (E := E) w₀ a h gM hgM b hb W hW)
  -- hence the inflation of `a` vanishes, and the inflation is injective
  have hmain : (NK.NUV2.ARL.HR.inflation (K := k) (L := L) (E := E)).hom a = 0 := by
    rw [hb, hγ, map_zero]
  exact eb_arch_infl_injective (k := k) (L := L) (E := E) (by rw [hmain, map_zero])

end Work.SSGRoute
