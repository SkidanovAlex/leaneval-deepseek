import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.Work.SSGRoute.finiteIndex_gesU
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reading-off of the escape-form Grünwald construction (brick (2))

`U := im(Kˣ · E) ≤ C_K` with `E = powTIdeles K p T`
(`Submission/Work/SSGRoute/ges_escape_aux.lean`, `…/ges_piece1.lean`).

## What is here

* `gesU` — `U` as a named subgroup, with `gesU_finiteIndex`, `isOpen_gesU'` (piece (1));
* `mem_gesU_iff` — **the structural core of the reading-off**: an idèle class `mk y` lies in `U`
  iff `y = prin γ · e` with `e ∈ E`.  (Proof: `ker (𝕀_K → C_K) = Kˣ` and the abelian rearrangement;
  the principal factor is moved to the left by solving `y⁻¹ (prin γ · b) = prin δ` for `δ`.)
* `exists_localPowClass_one_of_mem_gesU` — the **local consequence at a prime of `T`**: if the
  component of `y` at `𝔭 ∈ T` is `1` (the case of the canonical idèle of a `T`-free `𝔵`), then the
  principal factor `γ` is a local `p`-th power at `𝔭`, stated as
  `NK.UchidaKummer.localPowClass K p 𝔭 γ = 1` — exactly the hypothesis that the local Kummer
  dictionary (`ZSplit.nodeKummerCocharZMod_eq_zero_iff_localPowClass`) turns into the vanishing of
  the Kummer character of `γ` on the decomposition group at `𝔭`.

The remaining halves of brick (2) — the `𝔭 ∉ T` half (`v𝔭(γ) = v𝔭(y)` for `𝔭 ∉ T`, from `e ∈ E`
being a local unit there) and the divisor statement `𝔵 = (γ)·𝔡ᵖ` via `Idele.idealOf` /
`ideleOfFun` (`count_idealOf_ideleOfFun`) — are not here yet; see the route note §3sexies, brick (2).
-/

open scoped NumberField RestrictedProduct

namespace Work.SSGRoute

variable {K : Type*} [Field K] [NumberField K]

/-- **`U = im(Kˣ · E)`**, the open finite-index subgroup of `C_K` of piece (1). -/
noncomputable def gesU (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) : Subgroup (NK.GlobalCFT.IdeleClassGroup K) :=
  (NK.GlobalCFT.Idele.principalSubgroup K ⊔ powTIdeles K p T).map
    (NK.GlobalCFT.IdeleClassGroup.mk K)

theorem gesU_finiteIndex {p : ℕ} [Fact p.Prime] {T : Finset (NK.Chebotarev.PrimeIdeal K)} :
    (gesU K p T).FiniteIndex :=
  finiteIndex_gesU K p T

theorem isOpen_gesU' {p : ℕ} [Fact p.Prime] {T : Finset (NK.Chebotarev.PrimeIdeal K)} :
    IsOpen (gesU K p T : Set (NK.GlobalCFT.IdeleClassGroup K)) :=
  isOpen_gesU (K := K) (Fact.out) T

/-- **Membership in `U`, unpacked.**  An idèle class lies in `U = im(Kˣ · E)` iff the idèle is a
principal idèle times an element of `E`. -/
theorem mem_gesU_iff {p : ℕ} {T : Finset (NK.Chebotarev.PrimeIdeal K)}
    {y : NK.GlobalCFT.Idele K} :
    NK.GlobalCFT.IdeleClassGroup.mk K y ∈ gesU K p T ↔
      ∃ γ : Kˣ, ∃ e ∈ powTIdeles K p T, y = NK.GlobalCFT.Idele.principalIdele K γ * e := by
  constructor
  · intro h
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp h
    rw [Subgroup.mem_sup] at hz
    obtain ⟨a, ha, b, hb, hab⟩ := hz
    obtain ⟨γ, hγ⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp ha
    subst hγ
    have h1 : NK.GlobalCFT.IdeleClassGroup.mk K y =
        NK.GlobalCFT.IdeleClassGroup.mk K (NK.GlobalCFT.Idele.principalIdele K γ * b) := by
      rw [← hzy, ← hab]
    rw [NK.GlobalCFT.IdeleClassGroup.mk_eq_mk_iff] at h1
    obtain ⟨δ, hδ⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp h1
    refine ⟨γ * δ⁻¹, b, hb, ?_⟩
    have h2 : y = NK.GlobalCFT.Idele.principalIdele K γ * b *
        (NK.GlobalCFT.Idele.principalIdele K δ)⁻¹ := by
      rw [hδ]; group
    rw [h2, map_mul, map_inv]
    calc (NK.GlobalCFT.Idele.principalIdele K γ) * b *
            ((NK.GlobalCFT.Idele.principalIdele K δ))⁻¹
        = (NK.GlobalCFT.Idele.principalIdele K γ) *
            (b * ((NK.GlobalCFT.Idele.principalIdele K δ))⁻¹) := by rw [mul_assoc]
      _ = (NK.GlobalCFT.Idele.principalIdele K γ) *
            (((NK.GlobalCFT.Idele.principalIdele K δ))⁻¹ * b) := by rw [mul_comm b]
      _ = (NK.GlobalCFT.Idele.principalIdele K γ) *
            ((NK.GlobalCFT.Idele.principalIdele K δ))⁻¹ * b := by rw [mul_assoc]
  · rintro ⟨γ, e, he, rfl⟩
    refine Subgroup.mem_map.mpr ⟨NK.GlobalCFT.Idele.principalIdele K γ * e, ?_, rfl⟩
    exact Subgroup.mem_sup.mpr ⟨NK.GlobalCFT.Idele.principalIdele K γ,
      NK.GlobalCFT.Idele.mem_principalSubgroup.mpr ⟨γ, rfl⟩, e, he, rfl⟩

/-- **The local consequence of the reading-off at a prime of `T`.**  If `mk y ∈ U` and the component
of `y` at `𝔭 ∈ T` is `1` (true for the canonical idèle of a `T`-free fractional ideal), then the
principal factor `γ` of `mem_gesU_iff` is a local `p`-th power at `𝔭`. -/
theorem exists_localPowClass_one_of_mem_gesU {p : ℕ} {T : Finset (NK.Chebotarev.PrimeIdeal K)}
    {y : NK.GlobalCFT.Idele K} (hy : NK.GlobalCFT.IdeleClassGroup.mk K y ∈ gesU K p T)
    {𝔭 : NK.Chebotarev.PrimeIdeal K} (h𝔭 : 𝔭 ∈ T)
    (h1 : y (NK.GlobalCFT.Place.ofFinite 𝔭) = 1) :
    ∃ γ : Kˣ, NK.UchidaKummer.localPowClass K p 𝔭 γ = 1 := by
  obtain ⟨γ, e, he, hye⟩ := mem_gesU_iff.mp hy
  refine ⟨γ, ?_⟩
  have he𝔭 : e (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
      NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p := (mem_powTIdeles.mp he).1 𝔭 h𝔭
  have hcoe : e (NK.GlobalCFT.Place.ofFinite 𝔭) =
      (NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ := by
    have h := congrArg (fun x : NK.GlobalCFT.Idele K => x (NK.GlobalCFT.Place.ofFinite 𝔭)) hye
    rw [NK.GlobalCFT.Idele.mul_apply, h1] at h
    have hA : NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭) *
        e (NK.GlobalCFT.Place.ofFinite 𝔭) = 1 := h.symm
    calc e (NK.GlobalCFT.Place.ofFinite 𝔭) =
          (NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ *
            (NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭) *
              e (NK.GlobalCFT.Place.ofFinite 𝔭)) := by group
      _ = (NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ * 1 := by
            rw [hA]
      _ = (NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ := by
            rw [mul_one]
  have hval : Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom γ =
      (e (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ := by
    rw [hcoe]; rfl
  rw [← MonoidHom.mem_ker]
  show Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom γ ∈
      (QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p)).ker
  rw [QuotientGroup.ker_mk']
  show Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom γ ∈
      NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p
  rw [hval]
  exact Subgroup.inv_mem _ he𝔭

/-! ## The two halves of the reading-off, with a single principal factor -/

/-- **A local `p`-th power class from a unit component.**  If the component of an element of `E` at
`𝔭` is the inverse of the component of `prin γ`, then `γ` is a local `p`-th power at `𝔭`. -/
theorem localPowClass_eq_one_of_unit_component {p : ℕ} (hp : p.Prime)
    {𝔭 : NK.Chebotarev.PrimeIdeal K} {γ : Kˣ} {e : (𝔭.adicCompletion K)ˣ}
    (he : e ∈ NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p)
    (hval : Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom γ = e⁻¹) :
    NK.UchidaKummer.localPowClass K p 𝔭 γ = 1 := by
  rw [← MonoidHom.mem_ker]
  show Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom γ ∈
      (QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p)).ker
  rw [QuotientGroup.ker_mk']
  show Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom γ ∈
      NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p
  rw [hval]
  exact Subgroup.inv_mem _ he

/-- **The component identity behind the reading-off.**  If `y = prin γ · e` then at every prime
`(y 𝔭)⁻¹ · (prin γ)𝔭 = (e 𝔭)⁻¹`. -/
theorem inv_mul_component_eq_of_eq_mul {𝔭 : NK.Chebotarev.PrimeIdeal K}
    {y e : NK.GlobalCFT.Idele K} {γ : Kˣ}
    (h : y = NK.GlobalCFT.Idele.principalIdele K γ * e) :
    (y (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ *
        Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom γ =
      (e (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ := by
  have hc := congrArg (fun x : NK.GlobalCFT.Idele K => x (NK.GlobalCFT.Place.ofFinite 𝔭)) h
  rw [NK.GlobalCFT.Idele.mul_apply] at hc
  rw [show Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom γ =
      NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭) from rfl]
  rw [hc, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

/-- **The reading-off, with a single principal factor.**  If `mk y ∈ U` and the components of `y` at
the primes of `T` are trivial (the case of the canonical idèle of a `T`-free fractional ideal), then
some `γ : Kˣ` is a local `p`-th power at every prime of `T` and its components outside `T` agree with
those of `y` up to a local unit. -/
theorem exists_gamma_of_mem_gesU {p : ℕ} (hp : p.Prime)
    {T : Finset (NK.Chebotarev.PrimeIdeal K)} {y : NK.GlobalCFT.Idele K}
    (hy : NK.GlobalCFT.IdeleClassGroup.mk K y ∈ gesU K p T)
    (hyT : ∀ 𝔭 ∈ T, y (NK.GlobalCFT.Place.ofFinite 𝔭) = 1) :
    ∃ γ : Kˣ,
      (∀ 𝔭 ∈ T, NK.UchidaKummer.localPowClass K p 𝔭 γ = 1) ∧
      (∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, 𝔭 ∉ T →
        (y (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ *
            Units.map (algebraMap K (𝔭.adicCompletion K)).toMonoidHom γ ∈
          NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭)) := by
  obtain ⟨γ, e, he, hye⟩ := mem_gesU_iff.mp hy
  refine ⟨γ, ?_, ?_⟩
  · intro 𝔭 h𝔭
    have he𝔭 : e (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
        NK.UchidaKummer.ellPowSubgroup (𝔭.adicCompletion K) p :=
      (mem_powTIdeles.mp he).1 𝔭 h𝔭
    have hcoe : e (NK.GlobalCFT.Place.ofFinite 𝔭) =
        (NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ := by
      have h := congrArg (fun x : NK.GlobalCFT.Idele K => x (NK.GlobalCFT.Place.ofFinite 𝔭)) hye
      rw [NK.GlobalCFT.Idele.mul_apply, hyT 𝔭 h𝔭] at h
      have hA : NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭) *
          e (NK.GlobalCFT.Place.ofFinite 𝔭) = 1 := h.symm
      calc e (NK.GlobalCFT.Place.ofFinite 𝔭) =
            (NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ *
              (NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭) *
                e (NK.GlobalCFT.Place.ofFinite 𝔭)) := by
              rw [← mul_assoc, inv_mul_cancel, one_mul]
        _ = (NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ * 1 := by
              rw [hA]
        _ = (NK.GlobalCFT.Idele.principalIdele K γ (NK.GlobalCFT.Place.ofFinite 𝔭))⁻¹ := by
              rw [mul_one]
    exact localPowClass_eq_one_of_unit_component (K := K) hp he𝔭 (by rw [hcoe]; rfl)
  · intro 𝔭 h𝔭
    have he𝔭 : e (NK.GlobalCFT.Place.ofFinite 𝔭) ∈
        NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite 𝔭) :=
      (mem_powTIdeles.mp he).2 _ (fun hmem => h𝔭 (hmem 𝔭 rfl))
    rw [inv_mul_component_eq_of_eq_mul (K := K) (𝔭 := 𝔭) hye]
    exact Subgroup.inv_mem _ he𝔭

end Work.SSGRoute
