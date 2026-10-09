import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalFactor
import Submission.Work.SSGRoute.ZDataMup.localNormSubgroup_eq_top_of_isSplitIn
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.Work.SSGRoute.ZConstruction.kummerCharZModAdd
import Submission.Work.SSGRoute.ZConstruction.localKummerLift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Proved auxiliary lemmas for the gate `Work.SSGRoute.ZConstruction.auxPairingGate_odd`

This module is `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`), so it can be
imported by other lanes (in particular by the sibling lane
`Work.SSGRoute.ZDataMup.localTate_reciprocityFamily`, whose target this gate is the crux of) without
inheriting the `sorry` of the gate itself.  It contains

* `aux_hLocalFactor_eq_one_of_isSplitIn` -- the local factor at a completely split place is trivial;
* `aux_kummerCharMonoidHom_eq_one_imp_isSplitIn` -- a global element of trivial local Kummer class
  has an `A`-completely split Kummer field;
* `aux_norm_kummerSqrt_gen` -- **the norm of the Kummer root is `β`** (for `p` odd): the arithmetic
  input of the alternation/self-pairing of the crux family, hence of the unramified orthogonality
  (clause (3)) of the gate.
-/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Work.SSGRoute.ZDataMup.LTRecFamHonest in
/-- **The local factor at a completely split place is trivial.** If `A` splits completely in the
level `L/↥K` and `Φ` is an Artin map killing the idèlic norms, then the local factor of `Φ` at the
place below `A` kills every element.  (`P5` of the `LTRecFamHonest` plan.) -/
theorem aux_hLocalFactor_eq_one_of_isSplitIn (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤)
    (L : IntermediateField ↥K Ω) [FiniteDimensional ↥K L] [IsGalois ↥K L] [NumberField ↥L]
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥L ≃ₐ[↥K] ↥L))
    (hΦ : ∀ x ∈ NK.GlobalCFT.Idele.normImage ↥K ↥L, Φ x = 1)
    (hsplit : _root_.SSGRoute.IsSplitIn ↥K L A) (ν : (↥K)ˣ) :
    hLocalFactor (K := K) A hA L Φ ν = 1 := by
  haveI : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  refine hLocalFactor_eq_one_of_mem_localNormSubgroup (K := K) hA L Φ hΦ ν ?_
  have htop := Work.SSGRoute.ZDataMup.localNormSubgroup_eq_top_of_isSplitIn
    (k := k) (K := K) L A hAK (Submission.NeukirchUchida.primeOf A hAK)
    (Submission.NeukirchUchida.primeOf_spec A hAK) hsplit
  rw [Submission.NeukirchUchida.primeOf_eq_of_comap_eq hAK
    (isFinPlace_of_isFinPlace_below (K := K) (A := A) hA) rfl] at htop
  rw [htop]
  exact Subgroup.mem_top _


open Work.SSGRoute.ZDataMup.LTRecFamHonest in
/-- **A global element of trivial local Kummer class at `A` has an `A`-completely split Kummer
field.**  (`P6` of the `LTRecFamHonest` plan.) -/
theorem aux_kummerCharMonoidHom_eq_one_imp_isSplitIn (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A) (ν : (↥K)ˣ)
    (hν : kummerCharMonoidHom (ζ := ζ) (hζ := hζ) (A := A) hA ν = 1) :
    _root_.SSGRoute.IsSplitIn ↥K (hLevel (K := K) (Ω := Ω) (p := p) ν) A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  intro σ hσ
  have hzero : kummerCharZMod (Ω := Ω) p (ζ := ζ) hζ ν σ = 0 :=
    kummerCharZMod_eq_zero_of_kummerCharMonoidHom_eq_one (ζ := ζ) hζ A hA ν hν σ hσ
  have hfix : σ (kummerSqrtZMod (Ω := Ω) (K := ↥K) p ν) =
      kummerSqrtZMod (Ω := Ω) (K := ↥K) p ν :=
    (Work.SSGRoute.ZDataMup.LocalUnramified.kummerCharZMod_eq_zero_iff_apply_sqrt
      (K := ↥K) p hζ ν σ).mp hzero
  have hkf : hLevel (K := K) (Ω := Ω) (p := p) ν =
      IntermediateField.adjoin ↥K ({kummerSqrtZMod (Ω := Ω) (K := ↥K) p ν} : Set Ω) :=
    NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple p Fact.out hζ ν
      (kummerSqrtZMod_pow (Ω := Ω) (K := ↥K) p ν)
  change σ ∈ (hLevel (K := K) (Ω := Ω) (p := p) ν).fixingSubgroup
  rw [hkf]
  exact Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_adjoin_simple _ σ hfix


variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

open Work.SSGRoute.ZDataMup.LTRecFamHonest in
/-- **The norm of the Kummer root is `β`.**  For `p ≠ 2` and `β ∉ (↥K^×)^p`, the chosen `p`-th root
`α` of `β` in `Ω` generates the Kummer level, and its norm over `↥K` is `β`: the minimal polynomial of
`α` is `X ^ p - C β` (monic, of degree `p = [↥K(α) : ↥K]`, and dividing `X ^ p - C β`), so
`PowerBasis.norm_gen_eq_coeff_zero_minpoly` gives `N α = (-1)^p · (-β) = β` because `p` is odd.

This is the arithmetic input of the *alternation* of the crux pairing, hence of the unramified
orthogonality (clause (3)) of the gate: it exhibits `β` as a norm from its own level, so the local
component of `β` is a local norm and the local factor of the Artin map kills it. -/
theorem aux_norm_kummerSqrt_gen (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (β : (↥K)ˣ)
    (hβ : β ∉ NK.LocalAnabelian.powSubgroup p ↥K) :
    Algebra.norm ↥K (IntermediateField.AdjoinSimple.gen ↥K
      (Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β)) = β := by
  classical
  set α : Ω := Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β with hαdef
  have hαp : α ^ p = algebraMap ↥K Ω (β : ↥K) :=
    Work.SSGRoute.kummerSqrtZMod_pow (K := ↥K) (Ω := Ω) p β
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  -- (1) integrality of `α`, with the explicit polynomial `X ^ p - C β`
  have haev : (Polynomial.aeval α) (Polynomial.X ^ p - Polynomial.C (β : ↥K)) = 0 := by
    have h1 : (Polynomial.aeval α) (Polynomial.X ^ p - Polynomial.C (β : ↥K)) =
        α ^ p - algebraMap ↥K Ω (β : ↥K) := by simp
    rw [h1, hαp, sub_self]
  have hx : IsIntegral ↥K α :=
    ⟨Polynomial.X ^ p - Polynomial.C (β : ↥K),
      Polynomial.monic_X_pow_sub_C _ hp0, haev⟩
  -- (2) the minimal polynomial is `X ^ p - C β`
  have hmin : minpoly ↥K α = Polynomial.X ^ p - Polynomial.C (β : ↥K) := by
    have hdiv : minpoly ↥K α ∣ Polynomial.X ^ p - Polynomial.C (β : ↥K) :=
      minpoly.dvd ↥K α haev
    have hdeg : (Polynomial.X ^ p - Polynomial.C (β : ↥K)).natDegree
        ≤ (minpoly ↥K α).natDegree := by
      rw [Polynomial.natDegree_X_pow_sub_C]
      have hgal := NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω)
        (k := ↥K) p Fact.out hζ β hβ
      have hkf : hLevel (K := K) (Ω := Ω) (p := p) β =
          IntermediateField.adjoin ↥K ({α} : Set Ω) :=
        NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple p Fact.out hζ β hαp
      rw [← IntermediateField.adjoin.finrank hx, ← hkf]
      exact le_of_eq hgal.2.symm
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hx)
      (Polynomial.monic_X_pow_sub_C _ hp0) hdiv hdeg).symm
  -- (3) the norm of the generator, via the power basis
  have hnorm := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
    (IntermediateField.adjoin.powerBasis hx)
  rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, hmin] at hnorm
  rw [hnorm]
  have hdim : (IntermediateField.adjoin.powerBasis hx).dim = p := by
    show (minpoly ↥K α).natDegree = p
    rw [hmin, Polynomial.natDegree_X_pow_sub_C]
  rw [hdim]
  have hcoeff : Polynomial.coeff (Polynomial.X ^ p - Polynomial.C (β : ↥K)) 0 = -(β : ↥K) := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    simp [show (0 : ℕ) ≠ p from fun h => hp0 h.symm]
  rw [hcoeff]
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  rw [hpodd.neg_one_pow]
  ring

open Work.SSGRoute.ZDataMup.LTRecFamHonest in
/-- **The arithmetic core of the unramified orthogonality (clause (3)) of the gate.**

For `p ≠ 2` and `β ∈ ↥K^×` which is *not* a `p`-th power in `↥K`, the local component of `β` at any
finite place `A` is a local norm from the Kummer level `↥K⟮β^{1/p}⟯` of `β`.

This is the `β ∈ N_𝔭` statement which makes the crux pairing **alternating** (`F(x,x) = 0`), hence —
with the cyclicity of the unramified subgroup — implies `IsUnramifiedOrthogonal`.

Proof: by `aux_norm_kummerSqrt_gen` the chosen root `α` of `β` has norm `β` over `↥K` (this uses
`hp`), so the principal idèle of `β` is the norm idèle of the principal idèle of `α`; evaluating at
the place of `A` and identifying the component of a principal idèle with `localImageAt` gives the
conclusion via `normIdeleFun_mem_localNormSubgroup`. -/
theorem aux_localImageAt_mem_localNormSubgroup_adjoin_of_notMem (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hp : p ≠ 2) (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) (β : (↥K)ˣ)
    (hβ : β ∉ NK.LocalAnabelian.powSubgroup p ↥K)
    [FiniteDimensional ↥K ↥(IntermediateField.adjoin ↥K
      ({Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β} : Set Ω))]
    [NumberField ↥(IntermediateField.adjoin ↥K
      ({Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β} : Set Ω))]
    [IsGalois ↥K ↥(IntermediateField.adjoin ↥K
      ({Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β} : Set Ω))] :
    NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hAK)) β ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
        (L := ↥(IntermediateField.adjoin ↥K
          ({Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β} : Set Ω)))
        (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hAK)) := by
  classical
  set α : Ω := Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β with hαdef
  have hNα : Algebra.norm ↥K (IntermediateField.AdjoinSimple.gen ↥K α) = β :=
    aux_norm_kummerSqrt_gen ζ hζ hp β hβ
  have hne : IntermediateField.AdjoinSimple.gen ↥K α ≠ 0 := by
    intro h0
    have h1 : Algebra.norm ↥K (IntermediateField.AdjoinSimple.gen ↥K α) = 0 := by
      rw [h0, Algebra.norm_zero]
    rw [h1] at hNα
    exact β.ne_zero hNα.symm
  set γ : (↥(IntermediateField.adjoin ↥K ({α} : Set Ω)))ˣ :=
    Units.mk0 (IntermediateField.AdjoinSimple.gen ↥K α) hne with hγdef
  have hγ : (γ : ↥(IntermediateField.adjoin ↥K ({α} : Set Ω))) =
      IntermediateField.AdjoinSimple.gen ↥K α := rfl
  have h1 : NK.GlobalCFT.Idele.principalIdele ↥K β =
      NK.GlobalCFT.Idele.normIdeleHom ↥K
        ↥(IntermediateField.adjoin ↥K ({α} : Set Ω))
        (NK.GlobalCFT.Idele.principalIdele
          ↥(IntermediateField.adjoin ↥K ({α} : Set Ω)) γ) := by
    rw [NK.GlobalCFT.Idele.normIdeleHom_principalIdele]
    congr 1
    refine Units.ext ?_
    rw [Units.coe_map, hγ, hNα]
  rw [← Work.SSGRoute.ZDataMup.principalIdele_apply_eq_localImageAt (K := ↥K) β
    (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hAK)), h1,
    NK.GlobalCFT.Idele.normIdeleHom_apply]
  exact NK.CFTLib.IdeleHasse.normIdeleFun_mem_localNormSubgroup _ _

/-- **The norm is invariant under the identification of two equal intermediate fields.**

For `h : L = M` and `x : ↥L`, the image of `x` under `IntermediateField.equivOfEq h` has the same
norm over `F`.  Proof: `Algebra.norm` is the determinant of the left-multiplication linear map, and
`equivOfEq h` conjugates it (`LinearMap.det_conj`); the conjugation identity is proved pointwise,
where the only bookkeeping is the coercion `(e.toLinearEquiv.symm : ↥M → ↥L) y = e.symm y` (which
holds by `rfl` once stated with a *function* type ascription rather than a `LinearMap` one). -/
theorem aux_norm_equivOfEq {F E : Type*} [Field F] [Field E] [Algebra F E]
    {L M : IntermediateField F E} (h : L = M) (x : ↥L) :
    Algebra.norm F (IntermediateField.equivOfEq h x) = Algebra.norm F x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have hconj : Algebra.lmul F ↥M (IntermediateField.equivOfEq h x) =
      ((IntermediateField.equivOfEq h).toLinearEquiv : ↥L →ₗ[F] ↥M) ∘ₗ
        (Algebra.lmul F ↥L x ∘ₗ
          ((IntermediateField.equivOfEq h).toLinearEquiv.symm : ↥M →ₗ[F] ↥L)) := by
    ext y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    rw [map_mul, show (((IntermediateField.equivOfEq h).toLinearEquiv.symm : ↥M → ↥L)) y =
      (IntermediateField.equivOfEq h).symm y from rfl, AlgEquiv.apply_symm_apply]
  rw [hconj, LinearMap.det_conj]

open Work.SSGRoute.ZDataMup.LTRecFamHonest in
/-- **The `hLevel`-form glue for the arithmetic core of clause (3).**

`hLevel β` (the Kummer field `↥K(β^{1/p})`, defined as the subfield generated by *all* `p`-th roots
of `β`) is the simple adjoin `↥K⟮β^{1/p}⟯` of the chosen root
(`NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple`), which is the form in which
`adjoin.powerBasis` and hence the computation of the norm of the root works
(`aux_norm_kummerSqrt_gen`).  This lemma transports
`aux_localImageAt_mem_localNormSubgroup_adjoin_of_notMem` to the `hLevel` form used by the rest of the
lane: the norm witness `AdjoinSimple.gen ↥K α` is moved along
`IntermediateField.equivOfEq hkf.symm`, using `aux_norm_equivOfEq`.

Together with `aux_localImageAt_mem_localNormSubgroup_adjoin_of_notMem` this is the complete
arithmetic input of clause (3) (`IsUnramifiedOrthogonal`): with it the crux pairing is alternating
(`F(x,x) = 0` for `x ≠ 0` by `hLocalFactor_eq_one_of_mem_localNormSubgroup`; for `x = 0` the level is
`⊥` and the value is `0`), and the cyclicity of the unramified subgroup finishes the clause. -/
theorem aux_localImageAt_mem_localNormSubgroup_hLevel_of_notMem (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hp : p ≠ 2) (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤) (β : (↥K)ˣ)
    (hβ : β ∉ NK.LocalAnabelian.powSubgroup p ↥K)
    [FiniteDimensional ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) β)]
    [NumberField ↥(hLevel (K := K) (Ω := Ω) (p := p) β)]
    [IsGalois ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) β)] :
    NK.CFTLib.IdeleHasse.localImageAt (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hAK)) β ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K)
        (L := ↥(hLevel (K := K) (Ω := Ω) (p := p) β))
        (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hAK)) := by
  classical
  have hαp : Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β ^ p =
      algebraMap ↥K Ω (β : ↥K) := Work.SSGRoute.kummerSqrtZMod_pow (K := ↥K) (Ω := Ω) p β
  have hkf : hLevel (K := K) (Ω := Ω) (p := p) β =
      IntermediateField.adjoin ↥K
        ({Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β} : Set Ω) :=
    NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple p Fact.out hζ β hαp
  haveI : FiniteDimensional ↥K ↥(IntermediateField.adjoin ↥K
      ({Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β} : Set Ω)) :=
    hkf ▸ (inferInstance : FiniteDimensional ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) β))
  haveI : NumberField ↥(IntermediateField.adjoin ↥K
      ({Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β} : Set Ω)) :=
    hkf ▸ (inferInstance : NumberField ↥(hLevel (K := K) (Ω := Ω) (p := p) β))
  haveI : IsGalois ↥K ↥(IntermediateField.adjoin ↥K
      ({Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β} : Set Ω)) :=
    hkf ▸ (inferInstance : IsGalois ↥K ↥(hLevel (K := K) (Ω := Ω) (p := p) β))
  -- the norm witness, transported to the `hLevel` picture
  set γ : ↥(hLevel (K := K) (Ω := Ω) (p := p) β) :=
    IntermediateField.equivOfEq hkf.symm
      (IntermediateField.AdjoinSimple.gen ↥K
        (Work.SSGRoute.kummerSqrtZMod (K := ↥K) (Ω := Ω) p β)) with hγdef
  have hγnorm : Algebra.norm ↥K γ = β := by
    rw [hγdef, aux_norm_equivOfEq hkf.symm]
    exact aux_norm_kummerSqrt_gen ζ hζ hp β hβ
  have hγne : γ ≠ 0 := by
    intro h0
    have h1 : Algebra.norm ↥K γ = 0 := by rw [h0, Algebra.norm_zero]
    rw [h1] at hγnorm
    exact β.ne_zero hγnorm.symm
  set γu : (↥(hLevel (K := K) (Ω := Ω) (p := p) β))ˣ := Units.mk0 γ hγne with hγudef
  have hcoe : (γu : ↥(hLevel (K := K) (Ω := Ω) (p := p) β)) = γ := rfl
  have h1 : NK.GlobalCFT.Idele.principalIdele ↥K β =
      NK.GlobalCFT.Idele.normIdeleHom ↥K
        ↥(hLevel (K := K) (Ω := Ω) (p := p) β)
        (NK.GlobalCFT.Idele.principalIdele
          ↥(hLevel (K := K) (Ω := Ω) (p := p) β) γu) := by
    rw [NK.GlobalCFT.Idele.normIdeleHom_principalIdele]
    congr 1
    refine Units.ext ?_
    rw [Units.coe_map, hcoe]
    exact hγnorm.symm
  rw [← Work.SSGRoute.ZDataMup.principalIdele_apply_eq_localImageAt (K := ↥K) β
    (NK.GlobalCFT.Place.ofFinite (Submission.NeukirchUchida.primeOf A hAK)), h1,
    NK.GlobalCFT.Idele.normIdeleHom_apply]
  exact NK.CFTLib.IdeleHasse.normIdeleFun_mem_localNormSubgroup _ _

end Work.SSGRoute.ZConstruction
