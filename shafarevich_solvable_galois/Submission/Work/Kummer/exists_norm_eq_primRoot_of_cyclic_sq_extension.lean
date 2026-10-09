import Mathlib
import Submission.Work.Kummer.Defs
import Submission.Work.Kummer.exists_algEquiv_div_of_norm_eq_one
import Submission.Work.Kummer.norm_eq_prod_zpowers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace Work.Kummer

/-- Let `K ⊆ L ⊆ M` be a tower of fields with `M/K` finite Galois cyclic and `L/K` finite
Galois cyclic, and suppose `K` contains a primitive `n`-th root of unity `ζ`, with
`[L : K] = n` and `[M : K] = n ^ 2`. Then `ζ` is a norm from `L` to `K`.

The proof uses Hilbert's Theorem 90 for the cyclic extension `M/L`: any element of norm `1` is
of the form `σ y / y`.  Applying this to `ζ` (whose norm is `ζ ^ [M:L] = ζ ^ n = 1`) produces
`y : Mˣ` with `τ ^ n y = ζ y`, for a generator `τ` of `Gal(M/K)`.  The element `τ y / y` is then
fixed by `Gal(M/L)`, hence lies in `L`, and its norm over `K` telescopes to `τ ^ n y / y = ζ`. -/
theorem exists_norm_eq_primRoot_of_cyclic_sq_extension
    {K : Type u} {L : Type u} {M : Type u} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M] [IsCyclic Gal(M/K)]
    [IsGalois K L] [IsCyclic Gal(L/K)] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : Module.finrank K L = n) (hnM : Module.finrank K M = n ^ 2) :
    ∃ η : Lˣ, Algebra.norm K (η : L) = ζ := by
  classical
  let E : IntermediateField K M := (⊥ : IntermediateField L M).restrictScalars K
  let eL : L ≃ₐ[K] E := (IntermediateField.botEquiv L M).symm.restrictScalars K
  haveI : FiniteDimensional K E := eL.toLinearEquiv.finiteDimensional
  haveI : IsGalois K E := IsGalois.of_algEquiv eL
  haveI : Normal K E := IsGalois.to_normal
  haveI : FiniteDimensional E M := FiniteDimensional.right K E M
  have hnE : Module.finrank K E = n := (eL.toLinearEquiv).finrank_eq.symm.trans hn
  have hfinEM : Module.finrank E M = n := by
    have h := Module.finrank_mul_finrank K E M
    rw [hnE, hnM] at h
    exact Nat.eq_of_mul_eq_mul_left (NeZero.pos n) (h.trans (by ring))
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := Gal(M/K))
  haveI : IsCyclic Gal(M/E) :=
    isCyclic_of_injective (AlgEquiv.restrictScalarsHom K) (AlgEquiv.restrictScalarsHom_injective K)
  let ρ : Gal(E/K) := AlgEquiv.restrictNormalHom E τ
  have hρsurj : Function.Surjective (AlgEquiv.restrictNormalHom E) :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥E) M
  have hρ : ∀ x : Gal(E/K), x ∈ Subgroup.zpowers ρ := by
    intro x
    obtain ⟨z, rfl⟩ := hρsurj x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hτ z)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    show ρ ^ k = AlgEquiv.restrictNormalHom E z
    rw [show ρ = AlgEquiv.restrictNormalHom E τ from rfl, ← hk, map_zpow]
  have hcardEK : Nat.card Gal(E/K) = n := by rw [IsGalois.card_aut_eq_finrank]; exact hnE
  have horderρ : orderOf ρ = n := (orderOf_eq_card_of_forall_mem_zpowers hρ).trans hcardEK
  have hτn_restrict : AlgEquiv.restrictNormalHom E (τ ^ n) = 1 := by
    rw [map_pow, show AlgEquiv.restrictNormalHom E τ = ρ from rfl, ← horderρ, pow_orderOf_eq_one]
  have hτn_mem : τ ^ n ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact (AlgEquiv.restrictNormal_eq_one_iff E (τ ^ n)).mp
      (by rwa [show AlgEquiv.restrictNormalHom E (τ^n) = (τ^n).restrictNormal E from rfl] at hτn_restrict)
  let g : Gal(M/E) := IntermediateField.fixingSubgroupEquiv E ⟨τ ^ n, hτn_mem⟩
  have hg_apply : ∀ x : M, (g : M ≃ₐ[E] M) x = (τ ^ n) x := by intro x; rfl
  have horderτ : orderOf τ = n ^ 2 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hτ, IsGalois.card_aut_eq_finrank, hnM]
  have hordergn : orderOf (τ ^ n : Gal(M/K)) = n := by
    rw [orderOf_pow, horderτ, Nat.gcd_eq_right (⟨n, by ring⟩ : n ∣ n ^ 2),
        Nat.pow_two, Nat.mul_div_cancel_left n (NeZero.pos n)]
  have horderg : orderOf g = n := by
    rw [show g = IntermediateField.fixingSubgroupEquiv E ⟨τ ^ n, hτn_mem⟩ from rfl,
        MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hordergn]
  have hcardME : Nat.card Gal(M/E) = n := by
    rw [IsGalois.card_aut_eq_finrank]; exact hfinEM
  have htop : Subgroup.zpowers g = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, horderg, hcardME])
  have hσ : ∀ x : Gal(M/E), x ∈ Subgroup.zpowers g := fun x => by rw [htop]; exact Subgroup.mem_top x
  -- H90 on M/E
  have hnorm1 : Algebra.norm E (algebraMap E M (algebraMap K E ζ)) = 1 := by
    rw [Algebra.norm_algebraMap, hfinEM, ← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨y, hy⟩ := exists_algEquiv_div_of_norm_eq_one (K := ↥E) (L := M) hσ hnorm1
  have hgy' : (τ ^ n) (y : M) = algebraMap K M ζ * (y : M) := by
    have h1 : (g : M ≃ₐ[E] M) (y : M) = algebraMap E M (algebraMap K E ζ) * (y : M) := by
      rw [eq_div_iff (Units.ne_zero y)] at hy; exact hy.symm
    rw [← hg_apply, h1, IsScalarTower.algebraMap_apply K E M]
  -- eta_M
  have hζM_ne : algebraMap K M ζ ≠ 0 := fun h =>
    hζ.ne_zero (NeZero.ne n) ((algebraMap K M).injective (by rw [h, map_zero]))
  set ηM : M := τ (y : M) / (y : M) with hηM
  have hgn : (g : M ≃ₐ[E] M) ηM = ηM := by
    rw [hg_apply, hηM, map_div₀]
    have hstep : (τ ^ n) (τ (y : M)) = algebraMap K M ζ * τ (y : M) := by
      rw [← AlgEquiv.mul_apply, ← pow_succ, pow_succ', AlgEquiv.mul_apply, hgy', map_mul,
          AlgEquiv.commutes]
    rw [hstep, hgy']
    rw [mul_div_mul_left _ _ hζM_ne]
  have hfixall : ∀ f : Gal(M/E), f ηM = ηM := by
    intro f
    have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (Gal(M/E)) ηM :=
      Subgroup.zpowers_le.mpr hgn
    exact hle (htop ▸ Subgroup.mem_top f)
  obtain ⟨ηE, hηE⟩ := Set.mem_range.mp ((IsGalois.mem_range_algebraMap_iff_fixed ηM).mpr hfixall)
  -- key computation of the norm
  have hrec : ∀ x : E, algebraMap E M (ρ x) = τ (algebraMap E M x) := by
    intro x
    simpa [ρ] using AlgEquiv.restrictNormalHom_apply (F := K) E τ x
  have hkey : ∀ i : ℕ, algebraMap E M ((ρ ^ i) ηE) = (τ ^ i) ηM := by
    intro i
    induction i with
    | zero => rw [pow_zero, pow_zero, AlgEquiv.one_apply, AlgEquiv.one_apply, hηE]
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, hrec, ih, ← AlgEquiv.mul_apply, ← pow_succ']
  have htel : ∀ i : ℕ, (τ ^ i) ηM = (τ ^ (i + 1)) (y : M) / (τ ^ i) (y : M) := by
    intro i
    simp only [hηM, map_div₀, ← AlgEquiv.mul_apply, ← pow_succ]
  have htelprod : ∀ m : ℕ,
      (∏ i ∈ Finset.range m, (τ ^ (i + 1)) (y : M) / (τ ^ i) (y : M))
        = (τ ^ m) (y : M) / (y : M) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ, ih]
      have hk : (τ ^ k) (y : M) ≠ 0 :=
        fun h0 => Units.ne_zero y ((τ ^ k).injective (by rw [h0, map_zero]))
      rw [div_mul_div_comm, mul_comm (y : M) ((τ ^ k) (y : M)), mul_div_mul_left _ _ hk]
  have hprod : ∏ i ∈ Finset.range (Module.finrank K E), (ρ ^ i) ηE = algebraMap K E ζ := by
    apply (algebraMap E M).injective
    rw [map_prod]
    rw [Finset.prod_congr rfl (fun i _ => hkey i), hnE,
        Finset.prod_congr rfl (fun i _ => htel i), htelprod,
        hgy', IsScalarTower.algebraMap_apply K E M,
        div_eq_iff (Units.ne_zero y)]
  -- conclude norm in E
  have hEnorm : Algebra.norm K ηE = ζ := by
    apply (algebraMap K E).injective
    rw [norm_eq_prod_zpowers hρ ηE, hprod]
  have hτy : τ (y : M) ≠ 0 := fun h0 => Units.ne_zero y (τ.injective (by rw [h0, map_zero]))
  have hηM0 : ηM ≠ 0 := by
    rw [hηM]; exact div_ne_zero hτy (Units.ne_zero y)
  have hηE0 : ηE ≠ 0 := fun h0 => hηM0 (by rw [← hηE, h0, map_zero])
  refine ⟨Units.mk0 (eL.symm ηE) (fun h0 => hηE0 (by
      simpa using congrArg (⇑eL) h0)), ?_⟩
  rw [Units.val_mk0, Algebra.norm_eq_of_algEquiv eL.symm ηE, hEnorm]



end Work.Kummer
