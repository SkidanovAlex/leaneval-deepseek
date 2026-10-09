import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.phi1_mono_base
import Submission.Work.SSGRoute.phi1_lambda_defs
import Submission.Work.SSGRoute.phi1_trivial_mono_in
import Submission.Work.SSGRoute.E5Route.pairing_formula
import Submission.Work.SSGRoute.phi0_trivial_epi_in
import Submission.Work.SSGRoute.phi0_lamV_separates
import Submission.Work.SSGRoute.phi0_pTor_scalar
import Submission.Work.SSGRoute.level_family_of_delta
import Submission.Work.SSGRoute.phiTriv_mk0_eq
import Submission.Work.SSGRoute.phi_pair_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester): read `DESIGN_FIX.md` §1 and the docstrings of
`phi1_trivial_mono_in` (E3Ω) and `phi1_mono_step_in` (E5s).

# E5s, `sorryAx`-free route

`Submission/Work/SSGRoute/phi1_mono_step_in.lean` proves E5s (`Work.SSGRoute.phi1_mono_step_in`) by
way of `Work.SSGRoute.exists_realization_of_delta_lam`, whose proof consumes an E4Ω-type lemma
(`Work.SSGRoute.phi0_realization_in`, or `Work.SSGRoute.e4omega` after the E5 lane's rewiring).

This file re-proves the same step *without* those, from pieces that are `sorry`-free:

* E4Ω itself, here `phi0_realization_in_in`, assembled by `Work.SSGRoute.Phi0.phi0_of_pieces`
  (`Submission/Work/SSGRoute/phi0_trivial_epi_in.lean`) from the three arithmetic inputs
  `P2 = Work.SSGRoute.E5Route.pairing_formula`, `P3 = Work.SSGRoute.phi0_lamV_separates`,
  `P4 = Work.SSGRoute.phi0_pTor_scalar`;
* the `Ext`-calculus reduction steps of E5s, copied here under names ending in `_in` so that this
  file does not depend on `phi1_mono_step_in.lean` (whose import closure currently contains files in
  flux, and whose realisation input would reintroduce `sorryAx`);
* the unconditional realisation of the `δ`-family: `Work.SSGRoute.level_family_of_delta`
  (`Submission/Work/SSGRoute/level_family_of_delta.lean`), `sorry`-free.

The step lemma `phi1_mono_step_in_in` below is `Work.SSGRoute.phi1_mono_step_in` with
`phi0_realization_in` replaced by `phi0_realization_in_in`; its statement is character for character
that of `Work.SSGRoute.phi1_mono_step_in`. -/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

section Reduction

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω]

/-- **Case `i^*x = 0` (copy of `Work.SSGRoute.mk₀_f_comp_eq_zero_of_phiOneVanishesIn`).**  For
`S.X₁ ≅ 𝔽_p` and `x ∈ Ext¹_G(S.X₂, C_K)` with `φ¹(x)` vanishing on the levels of `Ω`, the pullback
of `x` along `S.f` vanishes (by E3Ω, `Work.SSGRoute.phi1_trivial_mono_in`). -/
theorem mk₀_f_comp_eq_zero_of_phiOneVanishesIn_in (p : ℕ) [Fact p.Prime] (ζ : k)
    (hζ : IsPrimitiveRoot ζ p)
    (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
    (x : Abelian.Ext S.X₂ (classesK k K) 1) (hx : PhiOneVanishesIn Ω x) :
    (Abelian.Ext.mk₀ S.f).comp x (zero_add 1) = 0 := by
  -- the class `i^*x` for `i = e.inv ≫ S.f` has vanishing pairing
  set i : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ S.X₂ := e.inv ≫ S.f with hi
  have hrel : PhiOneVanishesIn Ω ((Abelian.Ext.mk₀ i).comp x (zero_add 1)) := by
    intro L _ _ _ h
    rw [phiAt_mk₀_comp (i := i) (x := x) (L := L) (h := h)]
    exact hx L _
  have h0 : (Abelian.Ext.mk₀ i).comp x (zero_add 1) = 0 :=
    phi1_trivial_mono_in p k K Ω ζ hζ _ hrel
  -- `mk₀ i = mk₀ e.inv ≫ mk₀ S.f`, so `(mk₀ e.inv).comp ((mk₀ S.f).comp x) = 0`
  have hz : (Abelian.Ext.mk₀ e.inv).comp ((Abelian.Ext.mk₀ S.f).comp x (zero_add 1)) (zero_add 1)
      = 0 := by
    rw [← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.comp_assoc_of_second_deg_zero] at h0
    exact h0
  -- undo the iso: `(mk₀ S.f).comp x = (mk₀ e.hom).comp ((mk₀ e.inv).comp ((mk₀ S.f).comp x))`
  have hkey : (Abelian.Ext.mk₀ e.hom).comp
        ((Abelian.Ext.mk₀ e.inv).comp ((Abelian.Ext.mk₀ S.f).comp x (zero_add 1)) (zero_add 1))
        (zero_add 1)
      = (Abelian.Ext.mk₀ S.f).comp x (zero_add 1) := by
    rw [← Abelian.Ext.comp_assoc_of_second_deg_zero]
    rw [Abelian.Ext.mk₀_comp_mk₀]
    rw [show e.hom ≫ e.inv = 𝟙 S.X₁ from e.hom_inv_id]
    exact Abelian.Ext.mk₀_id_comp _
  rw [← hkey, hz]
  exact Abelian.Ext.comp_zero _ _ _ _ _

/-- **Exactness at the middle term (copy of `Work.SSGRoute.exists_lift_along_g`).**  For
`x ∈ Ext¹_G(S.X₂, C_K)` with `(mk₀ S.f).comp x = 0`, there is `y ∈ Ext¹_G(S.X₃, C_K)` with
`(mk₀ S.g).comp y = x`. -/
theorem exists_lift_along_g_in (S : ShortComplex (Rep.{0} Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (x : Abelian.Ext S.X₂ (classesK k K) 1)
    (hx : (Abelian.Ext.mk₀ S.f).comp x (zero_add 1) = 0) :
    ∃ y : Abelian.Ext S.X₃ (classesK k K) 1, (Abelian.Ext.mk₀ S.g).comp y (zero_add 1) = x :=
  Abelian.Ext.contravariant_sequence_exact₂ hS (classesK k K) x hx

end Reduction

section Step

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω]

/-- **Normalising the coefficient of the pairing along an isomorphism `e : X ≅ 𝔽_p` (copy of
`Work.SSGRoute.phiAt_normCoeff_eq_phiTriv`).**  The realisation produces its coefficient class on
the normalised sequence `0 → 𝔽_p → S.X₂ → S.X₃ → 0`; this identity transports the corresponding
pairing statement back to the given `e : S.X₁ ≅ 𝔽_p`. -/
theorem phiAt_normCoeff_eq_phiTriv_in (p : ℕ) [Fact p.Prime] {k K Ω : Type} [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (X : Rep Coeff (K ≃ₐ[k] K)) (e : X ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
    (c₀ : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K)
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (t : extH (Rep.res (galRes k K L) X) 2) :
    phiAt (k := k) (K := K) (L := L) (Abelian.Ext.mk₀ (e.hom ≫ c₀)) t
      = phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c₀)
          (t.comp (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map e.hom)) (add_zero 2)) := by
  have hL : phiAt (k := k) (K := K) (L := L) (Abelian.Ext.mk₀ (e.hom ≫ c₀)) t
      = t.comp (Abelian.Ext.mk₀ (Rep.resMap (galRes k K L) (e.hom ≫ c₀)
          ≫ classIncl k K L)) (add_zero 2) := by
    simp only [phiAt, levelPair, extRes, Abelian.Ext.mapExactFunctor_mk₀,
      Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.comp_assoc_of_second_deg_zero]
  have hmorph : Rep.resMap (galRes k K L) e.hom ≫ (trivRes (galRes k K L) (ZMod p)
        ≫ Rep.resMap (galRes k K L) c₀ ≫ classIncl k K L)
      = Rep.resMap (galRes k K L) (e.hom ≫ c₀) ≫ classIncl k K L := by
    ext x
    rfl
  have hR : phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c₀)
        (t.comp (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map e.hom)) (add_zero 2))
      = (t.comp (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map e.hom)) (add_zero 2)).comp
          (Abelian.Ext.mk₀ (trivRes (galRes k K L) (ZMod p)
            ≫ Rep.resMap (galRes k K L) c₀ ≫ classIncl k K L)) (add_zero 2) :=
    phiTriv_mk0_eq (k := k) (K := K) (L := L) (ZMod p) c₀ (s := 2)
      (t.comp (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map e.hom)) (add_zero 2))
  rw [hL, hR]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, hmorph]

end Step

/-- **E4Ω, proved from the assembly and the three arithmetic pieces.**  Every compatible
`p`-torsion family of level functionals over the levels `K ≤ L ≤ Ω` is the family of cup products
with one coefficient class `c : 𝔽_p ⟶ C_K`.  Same statement as `Work.SSGRoute.phi0_realization_in`
and `Work.SSGRoute.e4omega`; proved here from `Work.SSGRoute.Phi0.phi0_of_pieces`
(`Submission/Work/SSGRoute/phi0_trivial_epi_in.lean`) and the three pieces
`Work.SSGRoute.E5Route.pairing_formula` (`P2`), `Work.SSGRoute.phi0_lamV_separates` (`P3`),
`Work.SSGRoute.phi0_pTor_scalar` (`P4`) — all `sorry`-free. -/
theorem phi0_realization_in_in (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (Ω : Type)
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2 →+ extH (classesK k L) 2)
    (hp : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2), p • lam L h = 0)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
      (hLL : L ≤ L')
      (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflTrivIn (k := k) hLL (ZMod p) h)) :
    ∃ c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K,
      ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2),
        phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c) h = lam L h :=
  Phi0.phi0_of_pieces (k := k) (K := K) (Ω := Ω) p ζ hζ
    (fun f x => E5Route.pairing_formula (k := k) (K := K) (Ω := Ω) p ζ hζ f x)
    (fun x hx => phi0_lamV_separates (k := k) (K := K) (Ω := Ω) p ζ hζ x hx)
    (fun φ => phi0_pTor_scalar (k := k) (K := K) (Ω := Ω) p φ)
    lam hp hcompat

/-- **The realisation of the `δ`-family (E5R), `sorryAx`-free route.**  For a short exact sequence
`S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` with `S.X₁ ≅ 𝔽_p` and `y ∈ Ext¹_G(S.X₃, C_K)` whose level
functionals kill `ker δ_L` at every level, there is `c : S.X₁ ⟶ C_K` with
`φ(mk₀ c)(δ_L h) = φ(y)(h)` for all levels `L` and all `h`. -/
theorem exists_realization_of_delta_lam_in (p : ℕ) [Fact p.Prime] (k K Ω : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (S : ShortComplex (Rep Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
    (y : Abelian.Ext S.X₃ (classesK k K) 1)
    (hy : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) S.X₃) 1),
        deltaHom (k := k) (K := K) (L := L) S hS h = 0 →
          phiAt (k := k) (K := K) (L := L) y h = 0) :
    ∃ c : S.X₁ ⟶ classesK k K,
      ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) S.X₃) 1),
        phiAt (k := k) (K := K) (L := L) (Abelian.Ext.mk₀ c)
            (deltaHom (k := k) (K := K) (L := L) S hS h)
          = phiAt (k := k) (K := K) (L := L) y h := by
  -- the compatible `p`-torsion level family extending `λ_L(δ_L h) := φ(y)(h)`
  obtain ⟨lam, hp, hcompat, hlam⟩ :=
    Work.SSGRoute.level_family_of_delta p k K Ω ζ hζ S hS e y hy
  -- the Brauer realisation of `lam` by a single coefficient class `c₀ : 𝔽_p ⟶ C_K`
  obtain ⟨c₀, hc₀⟩ := phi0_realization_in_in p k K Ω ζ hζ lam hp hcompat
  refine ⟨e.hom ≫ c₀, fun L _instNF _instFD _instGal h => ?_⟩
  have hw : phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c₀)
      ((deltaHom (k := k) (K := K) (L := L) S hS h).comp
        (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map e.hom)) (add_zero 2))
      = lam L ((deltaHom (k := k) (K := K) (L := L) S hS h).comp
        (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map e.hom)) (add_zero 2)) :=
    hc₀ L _
  rw [phiAt_normCoeff_eq_phiTriv_in (k := k) (K := K) p (X := S.X₁) e c₀ L
    (deltaHom (k := k) (K := K) (L := L) S hS h)]
  exact hw.trans (hlam L h)

/-- **E5s, `sorryAx`-free route.**  Same statement as `Work.SSGRoute.phi1_mono_step_in`: for a
short exact sequence `S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` with `S.X₁ ≅ 𝔽_p`, injectivity of `φ¹` on
`Ext¹_G(S.X₃, C_K)` (tested on the levels of `Ω`) implies injectivity on `Ext¹_G(S.X₂, C_K)`. -/
theorem phi1_mono_step_in_in (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (Ω : Type)
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (S : ShortComplex (Rep Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
    (hX₃ : ∀ z : Abelian.Ext S.X₃ (classesK k K) 1, PhiOneVanishesIn Ω z → z = 0)
    (x : Abelian.Ext S.X₂ (classesK k K) 1) (hx : PhiOneVanishesIn Ω x) : x = 0 := by
  -- Step 1: `(mk₀ S.f).comp x = 0`, by E3Ω
  have hf : (Abelian.Ext.mk₀ S.f).comp x (zero_add 1) = 0 :=
    mk₀_f_comp_eq_zero_of_phiOneVanishesIn_in p ζ hζ S hS e x hx
  -- Step 2: lift `x` along `S.g`
  obtain ⟨y, hy⟩ := exists_lift_along_g_in S hS x hf
  -- Step 3: the level functionals of `y` kill `ker δ_L` at every level
  have hyker : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (h : extH (Rep.res (galRes k K L) S.X₃) 1),
      deltaHom (k := k) (K := K) (L := L) S hS h = 0 →
        phiAt (k := k) (K := K) (L := L) y h = 0 := by
    intro L _ _ _ h hh
    rw [deltaHom_apply] at hh
    have hh' : h.comp ((hS.map_of_exact (Rep.resFunctor (galRes k K L))).extClass)
        (show 1 + 1 = 2 by norm_num) = 0 := by
      rw [← Abelian.Ext.mapExactFunctor_extClass (F := Rep.resFunctor (galRes k K L)) hS]
      exact hh
    obtain ⟨j, hj⟩ := Abelian.Ext.covariant_sequence_exact₃
      (X := unitRep (L ≃ₐ[k] L)) (hS.map_of_exact (Rep.resFunctor (galRes k K L))) h
      (show 1 + 1 = 2 by norm_num) hh'
    have hj' : j.comp (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map S.g))
        (add_zero 1) = h := hj
    calc phiAt (k := k) (K := K) (L := L) y h
        = phiAt (k := k) (K := K) (L := L) y
            (j.comp (Abelian.Ext.mk₀ ((Rep.resFunctor (galRes k K L)).map S.g))
              (add_zero 1)) := by rw [hj']
      _ = phiAt (k := k) (K := K) (L := L)
            ((Abelian.Ext.mk₀ S.g).comp y (zero_add 1)) j :=
          (phiAt_comp_mk₀ (π := S.g) (y := y) (L := L) (h := j)).symm
      _ = phiAt (k := k) (K := K) (L := L) x j := by rw [hy]
      _ = 0 := hx L j
  -- Step 4: realise `λ` by a coefficient class `c` (the colimit/bookkeeping step)
  obtain ⟨c, hc⟩ := exists_realization_of_delta_lam_in p k K Ω ζ hζ S hS e y hyker
  -- Step 5: the algebraic half of the dévissage (`phi_one_step_of_realization_in`)
  have hc' : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (h : extH (Rep.res (galRes k K L) S.X₃) 1),
      phiAt (k := k) (K := K) (L := L) (Abelian.Ext.mk₀ c)
          (h.comp (extRes (galRes k K L) hS.extClass) (show 1 + 1 = 2 by norm_num))
        = phiAt (k := k) (K := K) (L := L) y h := by
    intro L _ _ _ h
    rw [← deltaHom_apply (k := k) (K := K) (L := L) S hS h]
    exact hc L h
  have hg : (Abelian.Ext.mk₀ S.g).comp y (zero_add 1) = 0 :=
    phi_one_step_of_realization_in (k := k) (K := K) Ω S hS y c hc' hX₃
  rw [← hy, hg]

end Work.SSGRoute
