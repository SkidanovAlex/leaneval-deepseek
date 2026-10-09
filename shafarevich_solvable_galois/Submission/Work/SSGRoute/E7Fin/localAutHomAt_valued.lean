import Submission.Work.SSGRoute.E7aAux
import Submission.Work.SSGRoute.E7Fin.lamFun_map_ringEquiv
import Submission.NK.HassePrinciple.localUnits_h2_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Galois action on a completion is continuous and valuation preserving

Lane `Work.SSGRoute.coker_obstruction_pt`.  `Work.SSGRoute.localAutHomAt k w σ` is the automorphism
of the local field `K_𝔮 = Place.localField K (ofFinite 𝔮)` attached to an element `σ` of the
decomposition group.  The `Γ`-equivariance lemma `E7Fin.lamFun_map_ringEquiv` needs exactly two
inputs about it: continuity and preservation of the valuation `vv 𝔮`.  This file supplies both.

* `E7Fin.localAutHomAt_continuous` — one line from `NK.HassePrinciple.localAut_continuous`;
* **`E7Fin.localAutHomAt_valuation`** — one line from `NK.HassePrinciple.localAut_valued_ofFinite`
  (the library fact that the local automorphisms of a *finite* place preserve `Valued.v`).

Together they are exactly the hypotheses `hτc`, `hτv` of `E7Fin.lamFun_map_ringEquiv`, so the
`Γ`-equivariance of the `p`-adic logarithm applies to the local Galois action.
-/

namespace Work.SSGRoute.E7Fin

/-- **The local Galois action on the completion is continuous.**  One line from
`NK.HassePrinciple.localAut_continuous` (`localAutHomAt` *is* `HassePrinciple.localAutHom`, whose
underlying map is `localAut`). -/
theorem localAutHomAt_continuous
    (k : Type) [Field k] [NumberField k] (K : Type) [Field K] [NumberField K] [Algebra k K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (σ : ↥(MulAction.stabilizer Gal(K/k) (NK.GlobalCFT.Place.ofFinite 𝔮))) :
    Continuous ⇑(Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) σ) :=
  NK.HassePrinciple.localAut_continuous _ σ

/-- **The local Galois action on the completion preserves the valuation.**  One line from
`NK.HassePrinciple.localAut_valued_ofFinite` (`vv 𝔮` *is* `Valued.v`, and `localAutHomAt` *is*
`HassePrinciple.localAut`). -/
theorem localAutHomAt_valuation
    (k : Type) [Field k] [NumberField k] (K : Type) [Field K] [NumberField K] [Algebra k K]
    [IsGalois k K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (σ : ↥(MulAction.stabilizer Gal(K/k) (NK.GlobalCFT.Place.ofFinite 𝔮))) :
    ∀ x : 𝔮.adicCompletion K,
      NK.LocalInputs.PowerQuotient.vv 𝔮
        ((Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) σ) x) =
      NK.LocalInputs.PowerQuotient.vv 𝔮 x :=
  fun x => NK.HassePrinciple.localAut_valued_ofFinite (K := k) 𝔮 σ x

/-- **LOG step 4 for the local Galois action** (the consumer form of
`E7Fin.lamFun_map_ringEquiv`).  For the canonical logarithm of the completion at `𝔮` and an element
`σ` of the decomposition group, if the principal unit `v` is the image of the principal unit `u`
under the local automorphism `localAutHomAt σ`, then

  `lamFun v = localAutHomAt σ (lamFun u)`.

This is the `Γ`-equivariance of `lamFun` — equivalently of the lattice `Λ = log U¹` — for the local
Galois action, which is what the arithmetic of `E7Fin.IsMilneStructure` uses. -/
theorem lamFun_localAutHom {K : Type} [Field K] [NumberField K] {k : Type} [Field k]
    [NumberField k] [Algebra k K] [IsGalois k K]
    {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (σ : ↥(MulAction.stabilizer Gal(K/k) (NK.GlobalCFT.Place.ofFinite 𝔮)))
    (u v : ↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1))
    (hv : ((v : (𝔮.adicCompletionIntegers K)ˣ) : 𝔮.adicCompletion K)
      = (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) σ)
        (((u : (𝔮.adicCompletionIntegers K)ˣ) : 𝔮.adicCompletion K))) :
    NK.LocalInputs.PowerQuotient.lamFun D.toLogData hp hres v
      = (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) σ)
        (NK.LocalInputs.PowerQuotient.lamFun D.toLogData hp hres u) :=
  lamFun_map_ringEquiv D hp hres _
    (localAutHomAt_continuous k K 𝔮 σ) (localAutHomAt_valuation k K 𝔮 σ) u v hv

open scoped WithZero in
/-- **`U¹` is stable under the local Galois action.**  For `u` a principal unit, the image of `u`
under the local automorphism `localAutHomAt σ` (an element of the completion) is again a principal
unit.  This is the `htrans` hypothesis of `E7Fin.map_Lam_le`, i.e. what makes the `Γ`-stability of
`Λ = log U¹` applicable to the local Galois action.

Writing `z = ↑↑u`, the membership of `u` in `U¹` gives `v z = 1` (from `v (z - 1) < 1` and the
additivity of `v`), hence `v (σ z) = v (σ z)⁻¹ = 1`; the ring unit is then built by
`Units.mkOfMulEqOne`, and the `pu 𝔮 1`-membership follows from `map_sub`, `map_one` and the
valuation preservation `E7Fin.localAutHomAt_valuation`. -/
theorem puMap_localAutHomAt
    (k : Type) [Field k] [NumberField k] (K : Type) [Field K] [NumberField K] [Algebra k K]
    [IsGalois k K]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (σ : ↥(MulAction.stabilizer Gal(K/k) (NK.GlobalCFT.Place.ofFinite 𝔮)))
    (u : ↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1)) :
    ∃ v : ↥(NK.LocalInputs.PowerQuotient.pu 𝔮 1),
      ((v : (𝔮.adicCompletionIntegers K)ˣ) : 𝔮.adicCompletion K)
        = (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) σ)
          (((u : (𝔮.adicCompletionIntegers K)ˣ) : 𝔮.adicCompletion K)) := by
  classical
  have hval := localAutHomAt_valuation k K 𝔮 σ
  let z : 𝔮.adicCompletion K :=
    (((u : (𝔮.adicCompletionIntegers K)ˣ) : 𝔮.adicCompletionIntegers K) : 𝔮.adicCompletion K)
  -- `z` is a unit of the completion
  have hzlt : NK.LocalInputs.PowerQuotient.vv 𝔮 (z - 1) < 1 :=
    lt_of_le_of_lt ((NK.LocalInputs.PowerQuotient.mem_pu_iff_val 𝔮 1 u).mp u.2)
      (by simpa using NK.LocalInputs.PowerQuotient.delta_lt_one (M := 1) le_rfl)
  have hz1 : NK.LocalInputs.PowerQuotient.vv 𝔮 z = 1 := by
    have hle : NK.LocalInputs.PowerQuotient.vv 𝔮 z ≤ 1 := by
      have hstep : NK.LocalInputs.PowerQuotient.vv 𝔮 z
          = NK.LocalInputs.PowerQuotient.vv 𝔮 ((z - 1) + 1) := by
        rw [show (z - 1) + 1 = z by ring]
      calc NK.LocalInputs.PowerQuotient.vv 𝔮 z
          = NK.LocalInputs.PowerQuotient.vv 𝔮 ((z - 1) + 1) := hstep
        _ ≤ max (NK.LocalInputs.PowerQuotient.vv 𝔮 (z - 1))
              (NK.LocalInputs.PowerQuotient.vv 𝔮 1) :=
            Valuation.map_add_le (NK.LocalInputs.PowerQuotient.vv 𝔮) (le_max_left _ _) (le_max_right _ _)
        _ ≤ 1 := max_le (le_of_lt hzlt) (le_of_eq (Valuation.map_one _))
    have hge : 1 ≤ NK.LocalInputs.PowerQuotient.vv 𝔮 z := by
      by_contra hcon
      push Not at hcon
      have hmax : max (NK.LocalInputs.PowerQuotient.vv 𝔮 z)
          (NK.LocalInputs.PowerQuotient.vv 𝔮 (z - 1)) < 1 := max_lt hcon hzlt
      have h1 : (1 : NK.LocalInputs.PowerQuotient.Zstar) ≤
          max (NK.LocalInputs.PowerQuotient.vv 𝔮 z)
            (NK.LocalInputs.PowerQuotient.vv 𝔮 (z - 1)) := by
        calc (1 : NK.LocalInputs.PowerQuotient.Zstar)
            = NK.LocalInputs.PowerQuotient.vv 𝔮 (1 : 𝔮.adicCompletion K) :=
              (Valuation.map_one _).symm
          _ = NK.LocalInputs.PowerQuotient.vv 𝔮 (z + -(z - 1)) := by
              rw [show z + -(z - 1) = 1 by ring]
          _ ≤ max (NK.LocalInputs.PowerQuotient.vv 𝔮 z)
                (NK.LocalInputs.PowerQuotient.vv 𝔮 (-(z - 1))) :=
              Valuation.map_add_le (NK.LocalInputs.PowerQuotient.vv 𝔮) (le_max_left _ _) (le_max_right _ _)
          _ = max (NK.LocalInputs.PowerQuotient.vv 𝔮 z)
                (NK.LocalInputs.PowerQuotient.vv 𝔮 (z - 1)) := by rw [Valuation.map_neg]
      exact absurd h1 (not_le.mpr hmax)
    exact le_antisymm hle hge
  have hzne : z ≠ 0 := by
    intro hzero
    have h := hz1
    rw [hzero, Valuation.map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  -- the transported element
  let y : 𝔮.adicCompletion K :=
    (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) σ) z
  have hy1 : NK.LocalInputs.PowerQuotient.vv 𝔮 y = 1 := by
    rw [show y = (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) σ) z from rfl,
      hval z, hz1]
  have hyi1 : NK.LocalInputs.PowerQuotient.vv 𝔮 y⁻¹ = 1 := by
    rw [Valuation.map_inv, hy1]; rfl
  have hyO : y ∈ 𝔮.adicCompletionIntegers K := by
    show y ∈ (NK.LocalInputs.PowerQuotient.vv 𝔮).valuationSubring
    rw [Valuation.mem_valuationSubring_iff, hy1]
  have hyiO : y⁻¹ ∈ 𝔮.adicCompletionIntegers K := by
    show y⁻¹ ∈ (NK.LocalInputs.PowerQuotient.vv 𝔮).valuationSubring
    rw [Valuation.mem_valuationSubring_iff, hyi1]
  have hyne : y ≠ 0 := by
    intro hzero
    have h := hy1
    rw [hzero, Valuation.map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  refine ⟨⟨Units.mkOfMulEqOne ⟨y, hyO⟩ ⟨y⁻¹, hyiO⟩ (by
    apply Subtype.ext
    show y * y⁻¹ = 1
    exact mul_inv_cancel₀ hyne), ?_⟩, ?_⟩
  · rw [NK.LocalInputs.PowerQuotient.mem_pu_iff_val]
    rw [show (((Units.mkOfMulEqOne ⟨y, hyO⟩ ⟨y⁻¹, hyiO⟩ _ : (𝔮.adicCompletionIntegers K)ˣ) :
        𝔮.adicCompletionIntegers K) : 𝔮.adicCompletion K) = y from rfl]
    rw [show y - 1 = (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) σ) (z - 1) by
      rw [show y = (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) σ) z from rfl,
        map_sub, map_one]]
    rw [hval]
    exact (NK.LocalInputs.PowerQuotient.mem_pu_iff_val 𝔮 1 u).mp u.2
  · rw [show (((Units.mkOfMulEqOne ⟨y, hyO⟩ ⟨y⁻¹, hyiO⟩ _ : (𝔮.adicCompletionIntegers K)ˣ) :
        𝔮.adicCompletionIntegers K) : 𝔮.adicCompletion K) = y from rfl]

/-- **`Λ = log U¹` is stable under the local Galois action.**  The counterpart of
`E7Fin.map_Lam_le` for the actual Galois action: for `σ` in the decomposition group,
`localAutHomAt σ` maps the lattice `Λ = Lam D hp hres = log U¹` into itself.  (The `htrans`
hypothesis of `map_Lam_le` is `E7Fin.puMap_localAutHomAt`.) -/
theorem map_Lam_le_localAutHom {K : Type} [Field K] [NumberField K] {k : Type} [Field k]
    [NumberField k] [Algebra k K] [IsGalois k K]
    {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (σ : ↥(MulAction.stabilizer Gal(K/k) (NK.GlobalCFT.Place.ofFinite 𝔮))) :
    ∀ x ∈ NK.LocalInputs.PowerQuotient.Lam D.toLogData hp hres,
      (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) σ) x
        ∈ NK.LocalInputs.PowerQuotient.Lam D.toLogData hp hres :=
  map_Lam_le D hp hres _
    (localAutHomAt_continuous k K 𝔮 σ) (localAutHomAt_valuation k K 𝔮 σ)
    (fun u => puMap_localAutHomAt k K 𝔮 σ u)

/-- **The local Galois action descends to `Λ/pΛ`.**  Elementwise form of the well-definedness of
the induced map on the quotient `Λ/pΛ` (`pΛ` written as `{y | ∃ x ∈ Λ, p • x = y}`): the
`Γ`-action preserves both `Λ` (`E7Fin.map_Lam_le_localAutHom`) and `pΛ` (`τ (p • x) = p • τ x`). -/
theorem map_pLam_le_localAutHom {K : Type} [Field K] [NumberField K] {k : Type} [Field k]
    [NumberField k] [Algebra k K] [IsGalois k K]
    {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {p M : ℕ}
    (D : CanonLogData 𝔮 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔮.adicCompletionIntegers K)) p)
    (σ : ↥(MulAction.stabilizer Gal(K/k) (NK.GlobalCFT.Place.ofFinite 𝔮))) :
    ∀ y, (∃ x ∈ NK.LocalInputs.PowerQuotient.Lam D.toLogData hp hres, p • x = y) →
      ∃ x ∈ NK.LocalInputs.PowerQuotient.Lam D.toLogData hp hres,
        p • x = (Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) σ) y := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨(Work.SSGRoute.localAutHomAt k (NK.GlobalCFT.Place.ofFinite 𝔮) σ) x,
    map_Lam_le_localAutHom D hp hres σ x hx, by
      rw [map_nsmul]⟩

end Work.SSGRoute.E7Fin
