import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.E7cC.exists_equivariant_of_fixed_vector
import Submission.Work.SSGRoute.PTdualControl.detectingFunctional_of_regularModuleLevel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The detecting functional on an *induced-coordinate* level (`p ∤ |D_w|`)

This file supplies the coefficient half of the `Sha2Lib`/`indLevelDatum` route to the unramified
detector (node `C6`, `Work.Sha2Lib.IsUnramifiedDetector`), in the `E7cC` spelling.

The situation: `L ⊇ K ⊇ k` is a finite Galois level over `k`, `q' | w` a place,
`N := ker (galRes k K L)`, and `e : N ≃* Ind_{D_w}^{G₀} 𝔽_p` a `Gal(K/k)`-equivariant isomorphism
onto the induced module `indDatum p k K w` (the `𝔽_p`-valued functions on `G₀ = Gal(K/k)` that are
invariant under right multiplication by `D_w = decompK w`, with the left-translation action).

The known algebraic half for the *regular* module
(`Work.SSGRoute.PTdualControl.detectingFunctional_of_regularModuleLevel`) detects the coordinate
`δ₁`, the indicator of the subgroup `{1}`; that is possible only when `D_w = ⊥`.  Here the detecting
coordinate is the **indicator of the set `D_w`** — the element `indDatumBase`, which *is* fixed by
the left action of `D_w` and therefore survives the inertia constraint — and the detection step is
carried by the norm `N_{D_w} m = ∑_{δ ∈ D_w} δ • m`:

for `m` with `μ m ≠ 0` and `φ_m (g) := ∑_{γ ∈ G₀} (e g) γ • (γ • m)` one has, using that
`e (coordKer d) = indDatumBase` and that `μ` is `D_w`-equivariant,

    μ (φ_m (coordKer d)) = μ (∑_{δ ∈ D_w} δ • m) = |D_w| • μ m,

which is non-zero exactly when `p ∤ |D_w|`.

Everything here is linear algebra over `ZMod p` on the `p`-torsion module `M`; the arithmetic input
is the *existence* of the level (the statement `Work.SSGRoute.Sha2Lib.IndLevelDatum`). -/

namespace Work.SSGRoute.E7cC

open CategoryTheory SSGRoute.PTExt

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

attribute [local instance 10000] Rep.hV2 Rep.hV1

/-- **The weighted orbit sum at the indicator of a subgroup.**  For a finite group `G`, a
`ZMod p`-module `V` with an action `ρ`, an element `m ∈ V` and a subgroup `D ≤ G`,

  `∑_{γ ∈ G} (1_D γ) • (γ • m) = ∑_{γ ∈ D} γ • m`,

the norm of `m` over `D`. -/
theorem sum_indicator_smul_eq_subgroupSum {p : ℕ} [Fact p.Prime] {G V : Type} [Group G]
    [Fintype G] [AddCommGroup V] [Module (ZMod p) V] (ρ : G →* (V →ₗ[ZMod p] V)) (m : V)
    (D : Subgroup G) [DecidablePred (fun γ : G => γ ∈ D)] :
    (∑ γ : G, (if γ ∈ D then (1 : ZMod p) else 0) • (ρ γ m))
      = ∑ γ ∈ (Finset.univ.filter (fun γ => γ ∈ D)), ρ γ m := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun γ _ => ?_
  by_cases h : γ ∈ D <;> simp [h]

/-- **The value of `μ` on the `D`-norm is `|D| · μ m`.**  For a `D`-equivariant `μ` (into a group on
which `D` acts trivially), `μ (∑_{δ ∈ D} δ • m) = |D| • μ m`. -/
theorem apply_sum_subgroup_of_equivariant {p : ℕ} [Fact p.Prime] {G V W : Type} [Group G]
    [Fintype G] [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W]
    (ρ : G →* (V →ₗ[ZMod p] V)) (μ : V →+ W) (m : V) (D : Subgroup G)
    [DecidablePred (fun γ : G => γ ∈ D)]
    (hμ : ∀ δ : G, δ ∈ D → μ (ρ δ m) = μ m) :
    μ (∑ γ ∈ (Finset.univ.filter (fun γ => γ ∈ D)), ρ γ m)
      = (Finset.univ.filter (fun γ => γ ∈ D)).card • μ m := by
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun γ hγ => hμ γ (Finset.mem_filter.mp hγ).2)]
  rw [Finset.sum_const]

/-- **`n • x ≠ 0` for `p`-torsion `x ≠ 0` and `p ∤ n`.** -/
theorem nsmul_ne_zero_of_prime_not_dvd {p n : ℕ} [hp : Fact p.Prime] {W : Type} [AddMonoid W]
    {x : W} (hx : p • x = 0) (hx0 : x ≠ 0) (hn : ¬ p ∣ n) : n • x ≠ 0 := by
  intro h
  have h1 : addOrderOf x = p := addOrderOf_eq_prime hx hx0
  have h2 : addOrderOf x ∣ n := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
  rw [h1] at h2
  exact hn h2

/-- **The `D`-norm is fixed by `D`.** -/
theorem norm_fixed {p : ℕ} [Fact p.Prime] {G V : Type} [Group G] [Fintype G]
    [AddCommGroup V] [Module (ZMod p) V] (ρ : G →* (V →ₗ[ZMod p] V)) (m : V) (D : Subgroup G)
    [DecidablePred (fun γ : G => γ ∈ D)] (δ : G) (hδ : δ ∈ D) :
    ρ δ (∑ γ ∈ (Finset.univ.filter (fun γ => γ ∈ D)), ρ γ m)
      = ∑ γ ∈ (Finset.univ.filter (fun γ => γ ∈ D)), ρ γ m := by
  rw [map_sum]
  refine Finset.sum_bij (fun γ _ => δ * γ)
    (fun γ hγ => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      D.mul_mem hδ (Finset.mem_filter.mp hγ).2⟩)
    (fun a _ b _ hab => mul_left_cancel hab)
    (fun b hb => ⟨δ⁻¹ * b, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        D.mul_mem (D.inv_mem hδ) (Finset.mem_filter.mp hb).2⟩,
      by rw [mul_inv_cancel_left]⟩)
    (fun γ _ => by rw [MonoidHom.map_mul]; rfl)

/-- **For `p ∤ |D_w|` a non-zero `μ` is non-zero on the fixed part `M^{D_w}`.**  The norm
`N_{D_w} m = ∑_{δ ∈ D_w} δ • m` is `D_w`-fixed and has `μ (N_{D_w} m) = |D_w| · μ m ≠ 0`.

This is what makes the sharp detection criterion
`∃ v₀ ∈ M^{D_w}, μ v₀ ≠ 0` (see `exists_equivariant_of_fixed_vector`) automatic in the regime
`p ∤ |D_w|`. -/
theorem exists_fixed_vector_apply_ne_zero_of_not_dvd (p : ℕ) [Fact p.Prime] (k K : Type)
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (hM : ∀ m : M.V, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (hp : ¬ p ∣ Nat.card ↥(SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0) :
    ∃ v₀ : M.V, (∀ δ : K ≃ₐ[k] K,
        δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w → M.ρ δ v₀ = v₀) ∧
      (Rep.Hom.hom μ) v₀ ≠ 0 := by
  classical
  haveI : Module (ZMod p) M.V := AddCommGroup.zmodModule hM
  obtain ⟨m, hm⟩ := Work.SSGRoute.PTdualControl.exists_apply_ne_zero_of_rep_hom_ne_zero μ hμ
  let ρ' : (K ≃ₐ[k] K) →* (M.V →ₗ[ZMod p] M.V) :=
    { toFun := fun u => AddMonoidHom.toZModLinearMap p ((M.ρ u : M.V →+ M.V))
      map_one' := by ext x; simp
      map_mul' := by intro u v; ext x; simp [map_mul] }
  have hρ'eval : ∀ (u : K ≃ₐ[k] K) (x : M.V), ρ' u x = M.ρ u x := fun u x => rfl
  have hint : ∀ γ : K ≃ₐ[k] K, γ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w →
      (Rep.Hom.hom μ) (ρ' γ m) = (Rep.Hom.hom μ) m := by
    intro γ hγ
    rw [hρ'eval]
    have h3 := Representation.IntertwiningMap.isIntertwining
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M).ρ
      (Work.SSGRoute.E7cOmega.divRep
        ↥(SSGRoute.PTExt.decompK (k := k) (K := K) w)).ρ
      (Rep.Hom.hom μ) ⟨γ, hγ⟩ m
    have h4 : ((Work.SSGRoute.E7cOmega.divRep
        ↥(SSGRoute.PTExt.decompK (k := k) (K := K) w)).ρ ⟨γ, hγ⟩)
        ((Rep.Hom.hom μ) m) = (Rep.Hom.hom μ) m := by
      rw [Rep.trivial_ρ]
      rfl
    rw [h4] at h3
    exact h3
  refine ⟨∑ γ ∈ (Finset.univ.filter
      (fun γ : K ≃ₐ[k] K => γ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w)), ρ' γ m,
    ?_, ?_⟩
  · intro δ hδ
    rw [← hρ'eval]
    exact norm_fixed ρ' m _ δ hδ
  · have hsum : (Rep.Hom.hom μ)
        (∑ γ ∈ (Finset.univ.filter
          (fun γ : K ≃ₐ[k] K => γ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w)), ρ' γ m)
        = (Finset.univ.filter
            (fun γ : K ≃ₐ[k] K => γ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w)).card
          • ((Rep.Hom.hom μ) m) :=
      apply_sum_subgroup_of_equivariant (V := M.V)
        (W := Work.SSGRoute.E7cOmega.RatDivZ) ρ' (Rep.Hom.hom μ) m _ hint
    rw [hsum]
    have hD : (Finset.univ.filter
          (fun γ : K ≃ₐ[k] K => γ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w)).card
        = Nat.card ↥(SSGRoute.PTExt.decompK (k := k) (K := K) w) := by
      rw [← Fintype.card_subtype
        (fun γ : K ≃ₐ[k] K => γ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w)]
      exact (Nat.card_eq_fintype_card).symm
    rw [hD]
    have hp0 : p • ((Rep.Hom.hom μ) m) = 0 := by
      have h1 : (Rep.Hom.hom μ) (p • m) = 0 := by rw [hM m, map_zero]
      have h2 : (Rep.Hom.hom μ) (p • m) = p • ((Rep.Hom.hom μ) m) := map_nsmul _ _ _
      rw [← h2]
      exact h1
    exact nsmul_ne_zero_of_prime_not_dvd hp0 hm hp

/-- **The exact detection criterion at the single-coset coordinate `indDatumBase`.**

A `Gal(K/k)`-equivariant additive `φ` out of `Ind_{D_w}^{G₀}𝔽_p` has `φ (indDatumBase) ∈ V^{D_w}`
(the basis vector is fixed by `D_w`, `Sha2Lib.indDatumSmul_base`), and conversely — Frobenius
reciprocity, `exists_equivariant_of_fixed_vector` — every `D_w`-fixed vector is such a value.  So

    (∃ φ equivariant, μ (φ indDatumBase) ≠ 0)   ⟺   ∃ v₀ ∈ V^{D_w}, μ v₀ ≠ 0.

This makes precise the sense in which the single-coset coordinate `indDatumBase` (the one demanded by
`Sha2Lib.IndLevelDatum`) can *only* see the fixed part `M^{D_w}` of the coefficient module: when `μ`
kills `M^{D_w}` the level must supply a coordinate supported on several `D_w`-cosets. -/
theorem exists_equivariant_indDatumBase_iff {p : ℕ} [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {W : Type} [AddCommGroup W]
    (ρ : (K ≃ₐ[k] K) →* (V →ₗ[ZMod p] V)) (μ : V →+ W) :
    (∃ φ : ↥(indDatum p k K w) →+ V,
        (∀ (σ : K ≃ₐ[k] K) (f : ↥(indDatum p k K w)),
          φ (Work.SSGRoute.Sha2Lib.indDatumSmul p k K w σ f) = ρ σ (φ f)) ∧
        μ (φ (indDatumBase p k K w)) ≠ 0)
      ↔ ∃ v₀ : V, (∀ δ : K ≃ₐ[k] K,
          δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w → ρ δ v₀ = v₀) ∧ μ v₀ ≠ 0 := by
  constructor
  · rintro ⟨φ, hφ, hμ⟩
    refine ⟨φ (indDatumBase p k K w), ?_, hμ⟩
    intro δ hδ
    rw [← hφ δ (indDatumBase p k K w),
      Work.SSGRoute.Sha2Lib.indDatumSmul_base p k K w δ hδ]
  · rintro ⟨v₀, hv₀, hμ⟩
    obtain ⟨φ, hφ, hbase⟩ := exists_equivariant_of_fixed_vector p k K w V ρ v₀ hv₀
    exact ⟨φ, hφ, by rw [hbase]; exact hμ⟩

/-- **The detecting functional on an induced-coordinate level, sharp form.**  Same level data as
`exists_detectingFunctional_of_indLevelDatum`, but the hypothesis is the *exact* condition under
which the single-coset coordinate `indDatumBase` can detect a non-zero `μ`: there must be a
`D_w`-fixed `v₀ ∈ M^{D_w}` with `μ v₀ ≠ 0` (Frobenius reciprocity
`Hom_{G₀}(Ind_{D_w}^{G₀}𝔽_p, M) ≅ M^{D_w}`, `Work.SSGRoute.E7cC.exists_equivariant_of_fixed_vector`).

No hypothesis on `|D_w|` is needed: the constructive map is not the orbit sum `∑_γ (e g) γ • (γ • m)`
(whose values all lie in `N_{D_w}(M)` and hence are killed by `μ` when `p ∣ |D_w|`), but the
Frobenius map determined by `v₀`. -/
theorem exists_detectingFunctional_of_indLevelDatum_sharp
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (hM : ∀ m : M.V, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
    (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
    (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
    (e : (SSGRoute.PTExt.galRes k K ↥L).ker ≃* Multiplicative ↥(indDatum p k K w))
    (he : ∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
      ((e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
          Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩).toAdd :
          (K ≃ₐ[k] K) → ZMod p)
        = fun τ : K ≃ₐ[k] K =>
            ((e g).toAdd : (K ≃ₐ[k] K) → ZMod p)
              ((SSGRoute.PTExt.galRes k K ↥L σ)⁻¹ * τ))
    (hI : ∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
      Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ = 1)
    (hd : ∃ d : ↥L ≃ₐ[k] ↥L,
      d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
      e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d)
        = Multiplicative.ofAdd (indDatumBase p k K w))
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hfix : ∃ v₀ : M.V, (∀ δ : K ≃ₐ[k] K,
        δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w → M.ρ δ v₀ = v₀) ∧
      (Rep.Hom.hom μ) v₀ ≠ 0) :
    ∃ φ : Additive ((SSGRoute.PTExt.galRes k K ↥L).ker) →+ M.V,
      (∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
        φ (Additive.ofMul ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
            Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩)
          = M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (φ (Additive.ofMul g))) ∧
      (∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
        φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ)) = 0) ∧
      (∃ d : ↥L ≃ₐ[k] ↥L,
        d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
        (Rep.Hom.hom μ) (φ (Additive.ofMul
          (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d))) ≠ 0) := by
  classical
  haveI : Module (ZMod p) M.V := AddCommGroup.zmodModule hM
  let ρ' : (K ≃ₐ[k] K) →* (M.V →ₗ[ZMod p] M.V) :=
    { toFun := fun u => AddMonoidHom.toZModLinearMap p ((M.ρ u : M.V →+ M.V))
      map_one' := by ext x; simp
      map_mul' := by intro u v; ext x; simp [map_mul] }
  have hρ'eval : ∀ (u : K ≃ₐ[k] K) (x : M.V), ρ' u x = M.ρ u x := fun u x => rfl
  obtain ⟨v₀, hv₀fix, hv₀μ⟩ := hfix
  obtain ⟨φ₀, hφ₀eq, hφ₀base⟩ :=
    exists_equivariant_of_fixed_vector p k K w M.V ρ' v₀ hv₀fix
  -- the functional on `N = ker (galRes k K L)`, pulled back along the equivariant `e`
  let φ : Additive (SSGRoute.PTExt.galRes k K ↥L).ker →+ M.V :=
    { toFun := fun x =>
        φ₀ (Multiplicative.toAdd (e (Additive.toMul x)) : ↥(indDatum p k K w))
      map_zero' := by simp
      map_add' := by
        intro x y
        have h1 : (Multiplicative.toAdd (e (Additive.toMul (x + y))) :
            ↥(indDatum p k K w))
            = Multiplicative.toAdd (e (Additive.toMul x))
              + Multiplicative.toAdd (e (Additive.toMul y)) := by
          simp only [toMul_add, map_mul, toAdd_mul]
        rw [h1, map_add] }
  have hφeval : ∀ (a : (SSGRoute.PTExt.galRes k K ↥L).ker),
      φ (Additive.ofMul a) = φ₀ (Multiplicative.toAdd (e a) : ↥(indDatum p k K w)) := by
    intro a
    simp [φ]
  refine ⟨φ, ?_, ?_, ?_⟩
  · -- `Gal(L/k)`-equivariance, via the equivariance of `φ₀` on `indDatum`
    intro σ g
    have h2 : (Multiplicative.toAdd (e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
          Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩) :
            ↥(indDatum p k K w))
        = Work.SSGRoute.Sha2Lib.indDatumSmul p k K w (SSGRoute.PTExt.galRes k K ↥L σ)
            (Multiplicative.toAdd (e g) : ↥(indDatum p k K w)) := by
      refine Subtype.ext ?_
      rw [Work.SSGRoute.Sha2Lib.indDatumSmul_coe]
      exact he σ g
    rw [hφeval, h2, hφeval, hφ₀eq, hρ'eval]
  · -- the inertia coordinates are trivial, and `φ₀ 0 = 0`
    intro γ hγ
    rw [hI γ hγ, hφeval]
    simp
  · -- detection at the coordinate of a decomposition element
    obtain ⟨d, hdmem, hev⟩ := hd
    refine ⟨d, hdmem, ?_⟩
    have hval : φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d)) = v₀ := by
      rw [hφeval]
      have h3 : (Multiplicative.toAdd (e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d)) :
          ↥(indDatum p k K w)) = indDatumBase p k K w := by
        rw [hev, toAdd_ofAdd]
      rw [h3, hφ₀base]
    rw [hval]
    exact hv₀μ

/-- **The detecting functional on an induced-coordinate level.**  Given the level data of
`Work.SSGRoute.Sha2Lib.IndLevelDatum` — in particular the `Gal(K/k)`-equivariant isomorphism
`e : ker (galRes k K L) ≃* Ind_{D_w}^{G₀} 𝔽_p`, a splitting `s` of `galRes`, the triviality of the
inertia coordinates (`hI`), and an element `d ∈ D_{q'}` whose coordinate is the basis vector
`indDatumBase` (the indicator of `D_w`) — and a non-zero `D_w`-equivariant functional
`μ : res_{D_w} M ⟶ ℚ/ℤ` on a `p`-torsion module `M`, there is a `Gal(L/k)`-equivariant additive
`φ : N → M` which vanishes on the inertia coordinates and which `μ` does not kill at the coordinate
of an element of the decomposition group of `q'`, **provided `p ∤ |D_w|`**.

This is the coefficient half of the reduction `IndLevelDatum ⟹ DetectsAt`; the other half
(`Work.SSGRoute.E7cC.coordDatum_to_unramifiedClass`, in this file's sibling) turns such a `φ` into
the class `h ∈ H¹(Gal(L/k), res M)`.

It is the specialisation of `exists_detectingFunctional_of_indLevelDatum_sharp` to the regime in
which `μ ≠ 0` *forces* the sharp hypothesis of that theorem (see
`exists_fixed_vector_apply_ne_zero_of_not_dvd`). -/
theorem exists_detectingFunctional_of_indLevelDatum
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (hM : ∀ m : M.V, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (hp : ¬ p ∣ Nat.card ↥(SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
    (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
    (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
    (e : (SSGRoute.PTExt.galRes k K ↥L).ker ≃* Multiplicative ↥(indDatum p k K w))
    (he : ∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
      ((e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
          Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩).toAdd :
          (K ≃ₐ[k] K) → ZMod p)
        = fun τ : K ≃ₐ[k] K =>
            ((e g).toAdd : (K ≃ₐ[k] K) → ZMod p)
              ((SSGRoute.PTExt.galRes k K ↥L σ)⁻¹ * τ))
    (hI : ∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
      Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ = 1)
    (hd : ∃ d : ↥L ≃ₐ[k] ↥L,
      d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
      e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d)
        = Multiplicative.ofAdd (indDatumBase p k K w))
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0) :
    ∃ φ : Additive ((SSGRoute.PTExt.galRes k K ↥L).ker) →+ M.V,
      (∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
        φ (Additive.ofMul ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
            Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩)
          = M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (φ (Additive.ofMul g))) ∧
      (∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
        φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ)) = 0) ∧
      (∃ d : ↥L ≃ₐ[k] ↥L,
        d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
        (Rep.Hom.hom μ) (φ (Additive.ofMul
          (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d))) ≠ 0) :=
  exists_detectingFunctional_of_indLevelDatum_sharp p k K Ω M hM w L q' hq' s hs e he hI hd μ
    (exists_fixed_vector_apply_ne_zero_of_not_dvd p k K M hM w hp μ hμ)

end Work.SSGRoute.E7cC
