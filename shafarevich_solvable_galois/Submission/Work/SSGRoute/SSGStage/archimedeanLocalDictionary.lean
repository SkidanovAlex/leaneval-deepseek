import Mathlib
import Submission.Work.SSGRoute.PT.e1a_beta_can
import Submission.Work.SSGRoute.PT.e1aBetaCan_localDictionary_fin_compat
import Submission.Work.SSGRoute.PT.e1aBetaCan_splitPlaces
import Submission.Work.SSGRoute.glue_infinite_place
import Submission.Work.SSGRoute.ext_two_iso_divisible_cohomology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean local dictionary (the `p = 2` correction of the E1a lane)

## What is asked

`archimedeanLocalDictionary`: for an infinite place `w` of `K`, an involution `σ` of `Gal(Ω/k)` whose
image under `res k K` contains the decomposition group `D_w` of `w`, and `y ∈ Ext²_{Gal(K/k)}(E',Kˣ)`
with `E' = DualMod p (E ⊗ T)`, there is an *injective* additive map

  `Λ : Ext²_{D_w}(E'|, K_wˣ) →+ H²(⟨σ⟩, E)`   with   `resH2 (akToGCH2 (e1aChainC y)) = 0 → Λ (extLoc (extToIdeles y)) = 0`.

Since `Λ` is injective and additive, the second clause is equivalent to the `Λ`-free statement

  `resH2 (akToGCH2 (e1aChainC y)) = 0 → extLoc (extToIdeles y) = 0`    (`*`)

which is the archimedean component of the E1a *comparison square* (`classCompat` of
`PT/NOTE_e1aChainC_localComparison.md` §3, the sibling node `SSGStage.e1aLandingInfLocal`).  So the
statement is the conjunction of

  (A) `∃ Λ : Ext²_{D_w}(E'|, K_wˣ) →+ H²(⟨σ⟩,E)` injective, and
  (B) the comparison `(*)`.

## State of the proof (this file)

* **The archimedean local data are provided and formalized here** (`decompK_ofInfinite_eq_stabilizer`,
  `isComplex_of_decompK_ofInfinite_ne_bot`, `complexUnits_divisible`,
  `localUnits_divisible_of_isComplex`, `localUnitsK_divisible_of_isComplex`,
  `archimedeanHomTwoSmulBijective`): a nontrivial decomposition group at an infinite place forces
  the place to be complex, where `K_w = ℂ` has *divisible* unit group.  This is what makes the
  divisible-coefficient `Ext`-dictionary `Work.SSGRoute.ext_two_iso_divisible_cohomology` applicable
  at the archimedean place — the dictionary is *generic*, so **no** local-field glue (the missing
  archimedean analogue of `localField_subfield_place_compat`) is needed for it.

* **`p` odd**: `Ext²_{D_w}(E'|,K_wˣ)` is a *subsingleton*.  This is proved — by another node of the
  team, on top of the ingredients of this file — as
  `Work.SSGRoute.SSGStage.archimedeanLocalExt2Subsingleton` (module
  `Submission.Work.SSGRoute.SSGStage.archimedeanLocalExt2Subsingleton`, which imports *this* file;
  the ingredients it uses are `isComplex_of_decompK_ofInfinite_ne_bot`,
  `localUnitsK_divisible_of_isComplex`, `finite_ptorsion_localUnits_of_isComplex`,
  `finite_ptorsion_additive`, `two_smul_bijective_coeffLinearMap_of_ptorsion_finite`,
  `subsingleton_H2_of_Z2_le_B2` and the generic dictionary
  `Work.SSGRoute.ext_two_iso_divisible_cohomology`).  With that vanishing, `Λ := 0` is injective and
  the comparison `(*)` is vacuous, i.e. **(A) and (B) both hold for odd `p`**.
  (Because the vanishing module imports this one, the odd-primary case of the theorem below must be
  assembled in a module that sits *above* both; it is therefore not spelled out here.)

* **`p = 2`**: `Ext²_{D_w}(E'|,K_wˣ) ≅ H²(ℤ/2,E) ≅ H²(⟨σ⟩,E)` (the dictionary, the coefficient
  identification `Hom_ℤ(E',ℂˣ) ≅ E` — which at an archimedean place reduces to `μ_p ⊆ K`
  (`hζK`) and `NK.HassePrinciple.localAut_algebraMap` — and the transfer `PT.gcH2Transfer` along
  `⟨σ⟩ ≅ D_w`), so the injectivity clause (A) holds.  The comparison `(B)` is, however, *not* a
  formal consequence of the definitions: it is the "comparison square" of the E1a lane, whose two
  missing inputs (a canonical local `E1c` dictionary carrying a computation rule, and its
  compatibility with the canonical global chain `e1aChainC`) are recorded in
  `PT/NOTE_e1aChainC_localComparison.md` §4, §7 and §11.  It is the same frontier as the sibling
  nodes `SSGStage.e1aLandingInfLocal` / `e1aLandingInfCompat`, and it is the only outstanding
  ingredient of the statement above.
-/

namespace Work.SSGRoute.SSGStage

open CategoryTheory SSGRoute.PTExt

variable {k : Type} [Field k] [NumberField k] {K : Type} [Field K] [NumberField K] [Algebra k K]

/-! ## The archimedean local data

For an infinite place `w` of `K`, the decomposition group of `ofInfinite w` is the stabiliser of
`w`; by Mathlib's archimedean ramification theory it is trivial exactly when `w` is unramified in
`K/k`, and a nontrivial decomposition group forces `w` to be a *complex* place (above a real place
of `k`).  In that case the local field `K_w = w.Completion` is `ℂ` — in particular its unit group
is divisible, which is what the divisible-coefficient `Ext`-dictionary
(`Work.SSGRoute.ext_two_iso_divisible_cohomology`) needs. -/

/-- The decomposition group of the infinite place `ofInfinite w` is the stabiliser of `w`. -/
theorem decompK_ofInfinite_eq_stabilizer (w : NumberField.InfinitePlace K) :
    SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)
      = MulAction.stabilizer (K ≃ₐ[k] K) w := by
  refine SetLike.ext fun γ => ?_
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj]

/-- **A nontrivial decomposition group at an infinite place forces the place to be complex**: the
place is then ramified in `K/k` (complex above a real place of `k`). -/
theorem isComplex_of_decompK_ofInfinite_ne_bot [FiniteDimensional k K] [IsGalois k K]
    {w : NumberField.InfinitePlace K}
    (h : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≠ ⊥) :
    w.IsComplex := by
  have hstab : MulAction.stabilizer (K ≃ₐ[k] K) w ≠ ⊥ := by
    rw [← decompK_ofInfinite_eq_stabilizer (k := k) w]; exact h
  have hram : NumberField.InfinitePlace.IsRamified k w := fun hunr =>
    hstab ((NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot).mp hunr)
  exact hram.isComplex

/-- **The units of `ℂ` are divisible.** -/
theorem complexUnits_divisible : ∀ n : ℕ, 0 < n → ∀ y : ℂˣ, ∃ x : ℂˣ, x ^ n = y := by
  intro n hn y
  have hz : (y : ℂ) ≠ 0 := Units.ne_zero y
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (Polynomial.X ^ n - Polynomial.C (y : ℂ))
    (by rw [Polynomial.degree_X_pow_sub_C hn]; exact Nat.cast_ne_zero.mpr hn.ne')
  have hr' : r ^ n = (y : ℂ) := by
    have h := Polynomial.IsRoot.def.mp hr
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at h
    exact sub_eq_zero.mp h
  have hr0 : r ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hn.ne'] at hr'
    exact hz hr'.symm
  exact ⟨Units.mk0 r hr0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hr'])⟩

/-- **The units of the local field at a complex infinite place are divisible** (the local field is
`ℂ`, via Mathlib's `ringEquivComplexOfIsComplex`). -/
theorem localUnits_divisible_of_isComplex [FiniteDimensional k K] [IsGalois k K]
    {w : NumberField.InfinitePlace K} (hw : w.IsComplex) :
    ∀ n : ℕ, 0 < n →
      ∀ y : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ,
        ∃ x, x ^ n = y := by
  intro n hn y
  have e : w.Completion ≃+* ℂ := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  obtain ⟨x, hx⟩ := complexUnits_divisible n hn (Units.mapEquiv e.toMulEquiv y)
  refine ⟨(Units.mapEquiv e.toMulEquiv).symm x, ?_⟩
  apply (Units.mapEquiv e.toMulEquiv).injective
  rw [map_pow, MulEquiv.apply_symm_apply, hx]

/-- The `p`-torsion subgroup of the local units at a complex infinite place is finite: the local
field is `ℂ` and the `p`-torsion of `ℂˣ` is the (finite) group of `p`-th roots of unity. -/
theorem finite_ptorsion_localUnits_of_isComplex [FiniteDimensional k K] [IsGalois k K]
    {w : NumberField.InfinitePlace K} (hw : w.IsComplex) (p : ℕ) [NeZero p] :
    Finite {y : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ //
      y ^ p = 1} := by
  have e : w.Completion ≃+* ℂ := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  have hmap : ∀ y : (w.Completion)ˣ, y ^ p = 1 →
      Units.mapEquiv e.toMulEquiv y ∈ rootsOfUnity p ℂ := by
    intro y hy
    exact (mem_rootsOfUnity p (Units.mapEquiv e.toMulEquiv y)).mpr
      (by rw [← map_pow, hy, map_one])
  refine Finite.of_injective
    (fun y : {y : (w.Completion)ˣ // y ^ p = 1} =>
      (⟨Units.mapEquiv e.toMulEquiv y.1, hmap y.1 y.2⟩ : ↥(rootsOfUnity p ℂ))) ?_
  intro y y' h
  refine Subtype.ext ((Units.mapEquiv e.toMulEquiv).injective ?_)
  exact congrArg (fun z : ↥(rootsOfUnity p ℂ) => (z : ℂˣ)) h

/-- **Doubling is bijective on the `Coeff`-linear maps `M →ₗ N`** for `M` a finite group whose
`p`-torsion is all of `M` (`p` odd) and `N` an abelian group with finite `p`-torsion. -/
theorem two_smul_bijective_coeffLinearMap_of_ptorsion_finite (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {M N : Type} [AddCommGroup M] [Finite M] [AddCommGroup N]
    (hfin : Finite {y : N // p • y = 0}) (hM : ∀ m : M, p • m = 0) :
    Function.Bijective (fun φ : M →ₗ[SSGRoute.PTExt.Coeff] N => φ + φ) := by
  have hval : ∀ (φ : M →ₗ[SSGRoute.PTExt.Coeff] N) (m : M), p • (φ m) = 0 := by
    intro φ m
    have h1 : φ (p • m) = p • φ m := map_nsmul _ p m
    rw [hM m, map_zero] at h1
    exact h1.symm
  haveI : Finite (M →ₗ[SSGRoute.PTExt.Coeff] N) :=
    Finite.of_injective
      (fun φ : M →ₗ[SSGRoute.PTExt.Coeff] N => fun m : M => (⟨φ m, hval φ m⟩ : {y : N // p • y = 0}))
      (fun φ ψ h => LinearMap.ext (fun m => by
        have h1 := congrFun h m
        exact congrArg (fun z : {y : N // p • y = 0} => (z : N)) h1))
  have hpodd : ¬ p ∣ 2 := by
    intro hpdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) (by norm_num)).mp hpdvd)
  have hcop : Nat.Coprime 2 p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr hpodd)
  have hinj_add : Function.Injective (fun φ : M →+ N => φ + φ) := by
    intro φ ψ h
    have hχ : (φ - ψ) + (φ - ψ) = 0 := by
      have h'' : φ + φ = ψ + ψ := h
      have h' : (φ - ψ) + (φ - ψ) = (φ + φ) - (ψ + ψ) := by abel
      rw [h', h'', sub_self]
    ext m
    have h2 : (2 : ℕ) • (φ - ψ) m = 0 := by
      have h1 : ((φ - ψ) + (φ - ψ)) m = 0 := by
        have := congrFun (congrArg (fun e : M →+ N => (e : M → N)) hχ) m
        simpa using this
      rw [AddMonoidHom.add_apply] at h1
      simpa [two_nsmul] using h1
    have hp' : p • (φ - ψ) m = 0 := by
      have h1 : (φ - ψ) (p • m) = p • ((φ - ψ) m) := map_nsmul _ p m
      rw [hM m, map_zero] at h1
      exact h1.symm
    have hdvd : addOrderOf ((φ - ψ) m) ∣ 1 := by
      have hg : addOrderOf ((φ - ψ) m) ∣ Nat.gcd 2 p :=
        Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2)
          (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hp')
      rwa [hcop.gcd_eq_one] at hg
    have hzero : (φ - ψ) m = 0 :=
      AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    have : φ m - ψ m = 0 := hzero
    exact sub_eq_zero.mp this
  have hinj : Function.Injective
      (fun φ : M →ₗ[SSGRoute.PTExt.Coeff] N => φ + φ) := by
    intro φ ψ h
    apply LinearMap.ext
    intro m
    have h' : (φ : M →+ N) + (φ : M →+ N) = (ψ : M →+ N) + (ψ : M →+ N) := by
      apply AddMonoidHom.ext
      intro m'
      have h1 : ((φ + φ : M →ₗ[SSGRoute.PTExt.Coeff] N) : M → N) m'
          = ((ψ + ψ : M →ₗ[SSGRoute.PTExt.Coeff] N) : M → N) m' :=
        congrFun (congrArg (fun e : M →ₗ[SSGRoute.PTExt.Coeff] N => (e : M → N)) h) m'
      simpa using h1
    have h2 := congrFun (congrArg (fun e : M →+ N => (e : M → N)) (hinj_add h')) m
    simpa using h2
  exact ⟨hinj, (Finite.injective_iff_surjective
    (f := fun φ : M →ₗ[SSGRoute.PTExt.Coeff] N => φ + φ)).mp hinj⟩

/-- The `p`-torsion of a group is finite iff the `p`-torsion of its additive incarnation is. -/
theorem finite_ptorsion_additive {M : Type} [CommGroup M] (p : ℕ)
    (h : Finite {y : M // y ^ p = 1}) : Finite {y : Additive M // p • y = 0} := by
  have hmem : ∀ y : Additive M, p • y = 0 → (Additive.toMul y) ^ p = 1 := by
    intro y hy
    have h1 : Additive.ofMul ((Additive.toMul y) ^ p) = (0 : Additive M) := by
      rw [ofMul_pow, ofMul_toMul, hy]
    rwa [← ofMul_one, Additive.ofMul.injective.eq_iff] at h1
  refine Finite.of_injective
    (fun y : {y : Additive M // p • y = 0} =>
      (⟨Additive.toMul y.1, hmem y.1 y.2⟩ : {y : M // y ^ p = 1})) ?_
  intro y y' h
  refine Subtype.ext ?_
  have h1 := congrArg (fun z : {y : M // y ^ p = 1} => (z : M)) h
  exact h1

/-- **Doubling is bijective on `M →+ N`** for `M` a finite group whose `p`-torsion is all of `M`
(`p` odd) and an abelian group `N` whose `p`-torsion is finite. -/
theorem two_smul_bijective_addHom_of_ptorsion_finite (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {M N : Type} [AddCommGroup M] [Finite M] [AddCommGroup N]
    (hfin : Finite {y : N // p • y = 0}) (hM : ∀ m : M, p • m = 0) :
    Function.Bijective (fun φ : M →+ N => φ + φ) := by
  have hval : ∀ (φ : M →+ N) (m : M), p • (φ m) = 0 := by
    intro φ m
    have h1 : φ (p • m) = p • φ m := map_nsmul _ p m
    rw [hM m, map_zero] at h1
    exact h1.symm
  haveI : Finite (M →+ N) :=
    Finite.of_injective
      (fun φ : M →+ N => fun m : M => (⟨φ m, hval φ m⟩ : {y : N // p • y = 0}))
      (fun φ ψ h => AddMonoidHom.ext (fun m => by
        have h1 := congrFun h m
        exact congrArg (fun z : {y : N // p • y = 0} => (z : N)) h1))
  have hpodd : ¬ p ∣ 2 := by
    intro hpdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) (by norm_num)).mp hpdvd)
  have hcop : Nat.Coprime 2 p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr hpodd)
  have hinj : Function.Injective (fun φ : M →+ N => φ + φ) := by
    intro φ ψ h
    have hχ : (φ - ψ) + (φ - ψ) = 0 := by
      have h'' : φ + φ = ψ + ψ := h
      have h' : (φ - ψ) + (φ - ψ) = (φ + φ) - (ψ + ψ) := by abel
      rw [h', h'', sub_self]
    ext m
    have h2 : (2 : ℕ) • (φ - ψ) m = 0 := by
      have h1 : ((φ - ψ) + (φ - ψ)) m = 0 := by
        have := congrFun (congrArg (fun e : M →+ N => (e : M → N)) hχ) m
        simpa using this
      rw [AddMonoidHom.add_apply] at h1
      simpa [two_nsmul] using h1
    have hp' : p • (φ - ψ) m = 0 := by
      have h1 : (φ - ψ) (p • m) = p • ((φ - ψ) m) := map_nsmul _ p m
      rw [hM m, map_zero] at h1
      exact h1.symm
    have hdvd : addOrderOf ((φ - ψ) m) ∣ 1 := by
      have hg : addOrderOf ((φ - ψ) m) ∣ Nat.gcd 2 p :=
        Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2)
          (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hp')
      rwa [hcop.gcd_eq_one] at hg
    have hzero : (φ - ψ) m = 0 :=
      AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    have : φ m - ψ m = 0 := hzero
    exact sub_eq_zero.mp this
  exact ⟨hinj, (Finite.injective_iff_surjective (f := fun φ : M →+ N => φ + φ)).mp hinj⟩

/-- If every `2`-cocycle of `G` with coefficients in `A` is a coboundary, then `H²(G,A)` is a
subsingleton. -/
theorem subsingleton_H2_of_Z2_le_B2 {G A : Type} [Group G] [AddCommGroup A]
    [DistribMulAction G A]
    (h : Work.GroupCohomology.Z2 G A ≤ Work.GroupCohomology.B2 G A) :
    Subsingleton (Work.GroupCohomology.H2 G A) := by
  rw [Work.GroupCohomology.H2]
  have htop : (Work.GroupCohomology.B2 G A).comap (Work.GroupCohomology.Z2 G A).subtype = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact h x.2
  rw [htop]
  exact QuotientAddGroup.subsingleton_quotient_top

/-- Divisibility transports from a group to its additive incarnation. -/
theorem additive_divisible_of_divisible {M : Type} [Group M]
    (h : ∀ n : ℕ, 0 < n → ∀ y : M, ∃ x, x ^ n = y) :
    ∀ n : ℕ, 0 < n → ∀ y : Additive M, ∃ x : Additive M, n • x = y := by
  intro n hn y
  obtain ⟨x, hx⟩ := h n hn (Additive.toMul y)
  refine ⟨Additive.ofMul x, ?_⟩
  rw [← ofMul_pow n x, hx]
  rfl

/-- **Doubling is bijective on `Hom(M,N)` for `M` a finite `𝔽_p`-module (`p` odd) and `N` a finite
`p`-torsion group.**  Injectivity is Bezout (`2x = 0` and `px = 0` force `x = 0`); a self-map of
the finite group `M →+ N` that is injective is bijective. -/
theorem archimedeanHomTwoSmulBijective (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {M N : Type} [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    [AddCommGroup N] [Finite N] (hNp : ∀ y : N, p • y = 0) :
    Function.Bijective (fun φ : M →+ N => φ + φ) := by
  haveI : Finite (M →+ N) :=
    Finite.of_injective (fun φ : M →+ N => (φ : M → N))
      (fun _ _ h => AddMonoidHom.ext (congrFun h))
  haveI : Fintype (M →+ N) := Fintype.ofFinite _
  have hpM : ∀ m : M, p • m = 0 := by
    intro m
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) p m, ZMod.natCast_self, zero_smul]
  have hpodd : ¬ p ∣ 2 := by
    intro hpdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) (by norm_num)).mp hpdvd)
  have hcop : Nat.Coprime 2 p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr hpodd)
  have hinj : Function.Injective (fun φ : M →+ N => φ + φ) := by
    intro φ ψ h
    have hχ : (φ - ψ) + (φ - ψ) = 0 := by
      have h'' : φ + φ = ψ + ψ := h
      have h' : (φ - ψ) + (φ - ψ) = (φ + φ) - (ψ + ψ) := by abel
      rw [h', h'', sub_self]
    ext m
    have h2 : (2 : ℕ) • (φ - ψ) m = 0 := by
      have h1 : ((φ - ψ) + (φ - ψ)) m = 0 := by
        have := congrFun (congrArg (fun e : M →+ N => (e : M → N)) hχ) m
        simpa using this
      rw [AddMonoidHom.add_apply] at h1
      simpa [two_nsmul] using h1
    have hp' : p • (φ - ψ) m = 0 := by
      have h1 : (φ - ψ) (p • m) = p • ((φ - ψ) m) := map_nsmul _ p m
      rw [hpM m, map_zero] at h1
      exact h1.symm
    have hdvd : addOrderOf ((φ - ψ) m) ∣ 1 := by
      have hg : addOrderOf ((φ - ψ) m) ∣ Nat.gcd 2 p :=
        Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2)
          (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hp')
      rwa [hcop.gcd_eq_one] at hg
    have hzero : (φ - ψ) m = 0 :=
      AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    have : φ m - ψ m = 0 := hzero
    exact sub_eq_zero.mp this
  exact ⟨hinj, (Finite.injective_iff_surjective (f := fun φ : M →+ N => φ + φ)).mp hinj⟩

/-- The divisibility of the local units at a complex infinite place, in the additive form required
by the divisible-coefficient `Ext`-dictionary. -/
theorem localUnitsK_divisible_of_isComplex [FiniteDimensional k K] [IsGalois k K]
    {w : NumberField.InfinitePlace K} (hw : w.IsComplex) :
    ∀ n : ℕ, 0 < n →
      ∀ y : (SSGRoute.PTExt.localUnitsK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofInfinite w)).V, ∃ x, n • x = y :=
  additive_divisible_of_divisible
    (M := (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite w))ˣ)
    (localUnits_divisible_of_isComplex (k := k) (K := K) hw)

theorem archimedeanLocalDictionary (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (w : NumberField.InfinitePlace ↥K) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (hle : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≤
      (Subgroup.zpowers σ).map (SSGRoute.res k K)) :
    ∃ Λ : CategoryTheory.Abelian.Ext.{0}
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w)).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (NK.GlobalCFT.Place.ofInfinite w)) 2 →+
      @Work.GroupCohomology.H2 ↥(Subgroup.zpowers σ) E _ _
        (@Subgroup.instDistribMulActionSubtypeMem (Ω ≃ₐ[k] Ω) E _ _
          (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)),
      Function.Injective Λ ∧
      (∀ y : CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))) (SSGRoute.PTExt.unitsK k K) 2,
        @Work.GroupCohomology.resH2 (Ω ≃ₐ[k] Ω) E _ _
            (DistribMulAction.compHom E (SSGRoute.res k K)) (Subgroup.zpowers σ)
            (@Work.SSGRoute.PT.akToGCH2 (Ω ≃ₐ[k] Ω) _ _ E _
              (DistribMulAction.compHom E (SSGRoute.res k K))
              (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E y)) = 0 →
        Λ (SSGRoute.PTExt.extLoc (k := k) (NK.GlobalCFT.Place.ofInfinite w)
            (SSGRoute.PTExt.extToIdeles (k := k) y)) = 0) := by sorry

end Work.SSGRoute.SSGStage
