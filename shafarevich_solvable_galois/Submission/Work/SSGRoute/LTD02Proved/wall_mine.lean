import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E7Fin.corH2_injective_ptorsion_pt
import Submission.Work.SSGRoute.LTD02Proved.mu_transfer_gen
import Submission.Work.SSGRoute.PT.akH2Setup
import Submission.Work.SSGRoute.PT.corH2_bijective_units_openSubgroup
import Submission.Work.SSGRoute.PT.kummerSES
import Submission.Work.SSGRoute.PT.local_resH2_mu_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The corestriction wall (Milne, *ADT*, (1.1b)) from the `μ_n`-transport

`ltdResH2_kill_pPowTorsion` (`resH2 U` kills the `p ^ a`-torsion of `H²(D_A, Ωˣ)`) is deduced
from the transported `μ_{p^a}`-statement `ltdResH2_mu_eq_zero_decomp_gen` by the Kummer sequence
`0 → μ_{p^a} → Ωˣ → Ωˣ → 0` over `D_A` (`PT.exists_kummerSES_units`), the coefficient comparison
`μ_{p^a}(K) ≅ μ_{p^a}(Ω)` and the exponent computation for `H²` with roots of unity coefficients.

From it, `ltdCorH2_injective_ptorsion` (the `p`-torsion form of (1.1b)) and
`ltdCorH2_bijective_units_openSubgroup` (the bijectivity used by the `α²`-dévissage) follow by the
elementary group-theoretic argument of `PT.exists_cor_ptorsion_ne_zero_decomp`.
-/

open Classical
open scoped Pointwise

namespace Work.SSGRoute.LTD02Proved

open Work.AbsoluteKummer

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

/-! ## A primitive root of unity and a finite Galois level containing it -/

/-- A primitive `n`-th root of unity in an algebraically closed field of characteristic `0`. -/
theorem ltdExists_primitiveRoot (n : ℕ) [NeZero n] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] : ∃ ζ : Ω, IsPrimitiveRoot ζ n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : CharZero Ω := by
    have hinj : Function.Injective (algebraMap k Ω) := (algebraMap k Ω).injective
    exact charZero_of_injective_algebraMap hinj
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (Polynomial.degree_cyclotomic_pos n Ω (Nat.pos_of_ne_zero hn)).ne'
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

/-- **A finite Galois level containing a primitive `n`-th root of unity**: `K = k(ζ)` for a
primitive `n`-th root `ζ` is a finite Galois extension of `k` (a cyclotomic one) containing `ζ`. -/
theorem ltdExists_cyclotomic_level (n : ℕ) [NeZero n] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] :
    ∃ (K : IntermediateField k Ω) (_ : FiniteDimensional k K) (_ : IsGalois k K) (ζ : Ω),
      IsPrimitiveRoot ζ n ∧ ζ ∈ K := by
  obtain ⟨ζ, hζ⟩ := ltdExists_primitiveRoot n k Ω
  haveI : Algebra.IsIntegral k Ω := Algebra.IsAlgebraic.isIntegral
  haveI hcyclo : IsCyclotomicExtension {n} k (IntermediateField.adjoin k ({ζ} : Set Ω)) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension k
  refine ⟨_, IsCyclotomicExtension.finiteDimensional {n} k _, IsCyclotomicExtension.isGalois {n} k _,
    ζ, hζ, IntermediateField.subset_adjoin k _ (Set.mem_singleton ζ)⟩

/-! ## The coefficient comparison `μ_n(K) ≅ μ_n(Ω)` -/

/-- The inclusion `μ_n(K) ↪ μ_n(Ω)` along `K ⊆ Ω`. -/
noncomputable def ltdMuInclHom (n : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) : rootsOfUnity n ↥K →* rootsOfUnity n Ω :=
  restrictRootsOfUnity (algebraMap ↥K Ω) n

theorem ltdMuInclHom_injective (n : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) : Function.Injective (ltdMuInclHom n k Ω K) :=
  Work.SSGRoute.PTembedding.restrictRootsOfUnity_injective (algebraMap ↥K Ω)
    (RingHom.injective _) n

theorem ltdMuInclHom_surjective (n : ℕ) [NeZero n] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {ζ : Ω} (hζ : IsPrimitiveRoot ζ n) (hζK : ζ ∈ K) :
    Function.Surjective (ltdMuInclHom n k Ω K) := by
  intro w
  have hw : ((w : Ωˣ) : Ω) ^ n = 1 := (mem_rootsOfUnity' n (w : Ωˣ)).mp w.2
  obtain ⟨i, _hi, hi⟩ := hζ.eq_pow_of_pow_eq_one hw
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  have hw0 : (⟨ζ ^ i, pow_mem hζK i⟩ : ↥K) ≠ 0 := by
    intro h
    have h2 : (ζ ^ i : Ω) = 0 := congrArg Subtype.val h
    exact pow_ne_zero i hζ0 h2
  let v : (↥K)ˣ := Units.mk0 ⟨ζ ^ i, pow_mem hζK i⟩ hw0
  have hv : v ^ n = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show (⟨ζ ^ i, pow_mem hζK i⟩ : ↥K) ^ n = 1
    refine Subtype.ext ?_
    simp only [IntermediateField.coe_pow, IntermediateField.coe_one]
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨⟨v, (mem_rootsOfUnity n v).mpr hv⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  show (((Units.map (algebraMap ↥K Ω).toMonoidHom) v : Ωˣ) : Ω) = ((w : Ωˣ) : Ω)
  rw [Units.coe_map]
  rw [show ((v : (↥K)ˣ) : ↥K) = (⟨ζ ^ i, pow_mem hζK i⟩ : ↥K) from rfl]
  exact hi

/-- The additive equivalence `μ_n(K) ≃+ μ_n(Ω)`. -/
noncomputable def ltdMuInclAddEquiv (n : ℕ) [NeZero n] (k Ω : Type) [Field k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) {ζ : Ω} (hζ : IsPrimitiveRoot ζ n) (hζK : ζ ∈ K) :
    Additive (rootsOfUnity n ↥K) ≃+ Additive (rootsOfUnity n Ω) :=
  (MulEquiv.ofBijective (ltdMuInclHom n k Ω K)
    ⟨ltdMuInclHom_injective n k Ω K, ltdMuInclHom_surjective n k Ω K hζ hζK⟩).toAdditive

theorem ltdMuInclAddEquiv_smul {n : ℕ} [NeZero n] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [Normal k K] {ζ : Ω} (hζ : IsPrimitiveRoot ζ n) (hζK : ζ ∈ K)
    (σ : Ω ≃ₐ[k] Ω) (x : Additive (rootsOfUnity n ↥K)) :
    ltdMuInclAddEquiv n k Ω K hζ hζK (SSGRoute.res k K σ • x) =
      σ • ltdMuInclAddEquiv n k Ω K hζ hζK x := by
  apply Additive.toMul.injective
  show ltdMuInclHom n k Ω K
      (Work.SSGRoute.PTembedding.MupKummer.muMapOfField k ↥K n (SSGRoute.res k K σ)
        (Additive.toMul x)) =
    Work.SSGRoute.PTembedding.MupKummer.muMapOfField k Ω n σ
      (ltdMuInclHom n k Ω K (Additive.toMul x))
  apply Subtype.ext
  apply Units.ext
  simp only [restrictRootsOfUnity_coe_apply,
    Work.SSGRoute.PTembedding.MupKummer.muMapOfField_coe, Units.coe_map,
    Work.SSGRoute.PT.algEquivUnitsMapOfField_coe]
  exact AlgEquiv.restrictNormalHom_apply (F := k) (K₁ := Ω) K σ
    (((Additive.toMul x : rootsOfUnity n ↥K) : (↥K)ˣ) : ↥K)

/-! ## The exponent of `H²` with roots-of-unity coefficients -/

/-- **`H²(G, M)` has exponent dividing `n` when `M` does.** -/
theorem ltdH2_nsmul_eq_zero_of_exponent {G : Type*} [Group G] [TopologicalSpace G]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] (n : ℕ)
    (hM : ∀ m : M, n • m = 0) (x : Work.AbsoluteKummer.H2 G M) : n • x = 0 := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype) x
  have h1 : n • x = Work.AbsoluteKummer.H2π G M (n • c) := by
    rw [show x = Work.AbsoluteKummer.H2π G M c from hc.symm, map_nsmul]
  have hc0 : (n • c : ↥(Work.AbsoluteKummer.Z2 G M)) = 0 := by
    apply Subtype.ext
    show (n • (c : G × G → M)) = 0
    funext p
    obtain ⟨g, h⟩ := p
    exact hM (c.1 (g, h))
  rw [h1, hc0, map_zero]

/-! ## The wall: `resH2 U` kills the `p ^ a`-torsion of `H²(D_A, Ωˣ)` -/

/-- **Milne, *ADT*, (1.1b), `p`-power form**: `resH2 U` kills the `p ^ a`-torsion of
`H²(D_A, Ωˣ)`, for every `a` (with `p ^ a ∣ [D_A : U]`). -/
theorem ltdResH2_kill_pPowTorsion (p a : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)]
    (hpa : p ^ a ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U))
    (e : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))
    (he : p ^ a • e = 0) :
    Work.SSGRoute.PT.resH2 U e = 0 := by
  classical
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    rw [pow_zero, one_nsmul] at he
    rw [he, map_zero]
  haveI hne : NeZero (p ^ a) := ⟨pow_ne_zero a (Fact.out : p.Prime).ne_zero⟩
  -- ### the place-completion data
  letI : Algebra (Work.SSGRoute.PTembedding.localFieldOf k A hA)
      (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion (Submission.NeukirchUchida.primeOf A hA) A
      (Submission.NeukirchUchida.primeOf_spec A hA)).toAlgebra
  have halg : ∀ z : Work.SSGRoute.PTembedding.localFieldOf k A hA,
      (algebraMap (Work.SSGRoute.PTembedding.localFieldOf k A hA)
        (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion
          (Submission.NeukirchUchida.primeOf A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA) z := fun _ => rfl
  have hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
        (NK.NeukirchUchida.adicCompletionToPlaceCompletion
          (Submission.NeukirchUchida.primeOf A hA) A
          (Submission.NeukirchUchida.primeOf_spec A hA)) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers k
        (Submission.NeukirchUchida.primeOf A hA) :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers
      (Submission.NeukirchUchida.primeOf A hA) A (Submission.NeukirchUchida.primeOf_spec A hA)
  -- ### the `μ_{p^a}`-statement at `D_A`
  obtain ⟨K, hKfin, hKgal, ζ, hζ, hζK⟩ := ltdExists_cyclotomic_level (p ^ a) k Ω
  haveI : FiniteDimensional k K := hKfin
  haveI : IsGalois k K := hKgal
  have hμK := ltdResH2_mu_eq_zero_decomp_gen (p ^ a) k Ω A hA halg hW K ζ hζ hζK U hU
  -- ### the coefficient comparison `μ_{p^a}(K) ≃+ μ_{p^a}(Ω)`
  let Ψb : Additive (rootsOfUnity (p ^ a) ↥K) ≃+ Additive (rootsOfUnity (p ^ a) Ω) :=
    ltdMuInclAddEquiv (p ^ a) k Ω K hζ hζK
  have hΨb : Work.GroupCohomology.IsEquivariant ↥(SSGRoute.decomp k A) Ψb.toAddMonoidHom := by
    intro g y
    show ltdMuInclAddEquiv (p ^ a) k Ω K hζ hζK
        (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • y) =
      (g : Ω ≃ₐ[k] Ω) • ltdMuInclAddEquiv (p ^ a) k Ω K hζ hζK y
    exact ltdMuInclAddEquiv_smul (n := p ^ a) hζ hζK (g : Ω ≃ₐ[k] Ω) y
  have hΨbsymm : Work.GroupCohomology.IsEquivariant ↥(SSGRoute.decomp k A) Ψb.symm.toAddMonoidHom := by
    intro g y
    refine Ψb.injective ?_
    show Ψb (Ψb.symm (g • y)) = Ψb (g • Ψb.symm y)
    rw [AddEquiv.apply_symm_apply]
    rw [show Ψb (g • Ψb.symm y) = g • Ψb (Ψb.symm y) from hΨb g (Ψb.symm y)]
    rw [AddEquiv.apply_symm_apply]
  let E : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (rootsOfUnity (p ^ a) ↥K)) ≃+
      Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (rootsOfUnity (p ^ a) Ω)) :=
    Work.SSGRoute.PT.H2Fin.h2AddEquivOfEquiv Ψb hΨb hΨbsymm
  -- ### the Kummer sequence `0 → μ_{p^a} → Ωˣ → Ωˣ → 0` over `D_A`
  obtain ⟨S, hpi, _hiota⟩ := Work.SSGRoute.PT.exists_kummerSES_units (p ^ a) k Ω
    (SSGRoute.decomp k A) (Work.SSGRoute.PTembedding.isClosed_decomp' k Ω A)
  have hpi' : ∀ u : Additive (Units Ω), S.pi u = p ^ a • u := hpi
  have hrange := Work.SSGRoute.PT.range_mapH2_eq_ker_nsmul (p ^ a) S hpi'
  have hemem : e ∈ (Work.SSGRoute.PT.nsmulHom (p ^ a)
      (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))).ker := by
    rw [AddMonoidHom.mem_ker, Work.SSGRoute.PT.nsmulHom_apply]
    exact he
  obtain ⟨w, hw⟩ := AddMonoidHom.mem_range.mp (by rw [hrange]; exact hemem)
  -- ### transport `w` to `μ_{p^a}(K)`-coefficients and apply the `μ_{p^a}`-statement
  obtain ⟨wK, hwKeq⟩ := E.surjective w
  have hwKe : Work.AbsoluteKummer.mapH2 Ψb.toAddMonoidHom hΨb wK = w := hwKeq
  have hCoeff : ∀ m : Additive (rootsOfUnity (p ^ a) Ω), p ^ a • m = 0 := by
    intro m
    show Additive.ofMul ((Additive.toMul m : rootsOfUnity (p ^ a) Ω) ^ (p ^ a)) = 0
    have hm : ((Additive.toMul m : rootsOfUnity (p ^ a) Ω) : Ωˣ) ^ (p ^ a) = 1 :=
      (mem_rootsOfUnity (p ^ a) ((Additive.toMul m : rootsOfUnity (p ^ a) Ω) : Ωˣ)).mp
        (Additive.toMul m : rootsOfUnity (p ^ a) Ω).2
    rw [show (Additive.toMul m : rootsOfUnity (p ^ a) Ω) ^ (p ^ a) = 1 from
      Subtype.ext (by simpa using hm)]
    rfl
  have hNw : Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • w = 0 := by
    obtain ⟨c, hc⟩ := hpa
    rw [hc, mul_comm (p ^ a) c, mul_nsmul' w c (p ^ a),
      ltdH2_nsmul_eq_zero_of_exponent (p ^ a) hCoeff w, smul_zero]
  have hwK0 : Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • wK = 0 := by
    refine E.injective ?_
    rw [map_nsmul, map_zero, hwKeq]
    exact hNw
  have hresK : Work.SSGRoute.PT.resH2 U wK = 0 := hμK wK hwK0
  have hres_w : Work.SSGRoute.PT.resH2 U w = 0 := by
    calc Work.SSGRoute.PT.resH2 U w
        = Work.SSGRoute.PT.resH2 U
            (Work.AbsoluteKummer.mapH2 Ψb.toAddMonoidHom hΨb wK) := by rw [← hwKe]
      _ = Work.AbsoluteKummer.mapH2 (G := ↥U) Ψb.toAddMonoidHom
            (fun u a => hΨb (u : ↥(SSGRoute.decomp k A)) a)
            (Work.SSGRoute.PT.resH2 U wK) :=
            Work.SSGRoute.PT.resH2_mapH2 U Ψb.toAddMonoidHom hΨb wK
      _ = 0 := by rw [hresK, map_zero]
  -- ### conclude
  calc Work.SSGRoute.PT.resH2 U e
      = Work.SSGRoute.PT.resH2 U (Work.AbsoluteKummer.mapH2 (G := ↥(SSGRoute.decomp k A))
          S.iota S.iota_equivariant w) := by rw [hw]
    _ = Work.AbsoluteKummer.mapH2 (G := ↥U) S.iota
          (fun u a => S.iota_equivariant (u : ↥(SSGRoute.decomp k A)) a)
          (Work.SSGRoute.PT.resH2 U w) :=
          Work.SSGRoute.PT.resH2_mapH2 U S.iota S.iota_equivariant w
    _ = 0 := by rw [hres_w, map_zero]

/-! ## Milne (1.1b) at the `p`-torsion, and the bijectivity of `corH2` there -/

/-- **Milne, *ADT*, (1.1b)**: the corestriction `corH2 U hU (Ωˣ)` is injective on the `p`-torsion of
`H²(U, Ωˣ)`, for every open `U ≤ D_A` with `p ∣ [D_A : U]`. -/
theorem ltdCorH2_injective_ptorsion (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)]
    (p : ℕ) (hp : p.Prime) (hpdiv : p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U)) :
    ∀ y : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)), p • y = 0 →
      Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)) y = 0 → y = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- the `p`-torsion of the local Brauer group is nontrivial, and (1.1b) at the open `U` turns that
  -- into a non-zero value of the corestriction (this replaces the direct call to the (removed)
  -- `PT.exists_cor_ptorsion_ne_zero_decomp` by the lane-local `E7Fin` version of (1.1b))
  have hcardA : Nat.card {y : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) // p • y = 0} = p :=
    Work.SSGRoute.PT.cardH2_units_openSubgroup_decomp p k Ω A hA U hU
  obtain ⟨y, hy0, hyne⟩ := Work.SSGRoute.E7Fin.ptorsion_ne_zero_of_natCard_pt
    (V := Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω))) p hcardA
  have hyne' : Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)) y ≠ 0 := fun h0 =>
    hyne (Work.SSGRoute.E7Fin.corH2_injective_ptorsion_of_dvd_index_pt k Ω A hA U hU p hpdiv
      y hy0 h0)
  exact Work.SSGRoute.E7Fin.ptorsion_injective_of_nonzero_pt
    (V := Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)))
    (W := Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))
    p (Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω))) hcardA ⟨y, hy0, hyne'⟩

/-- **The class-formation axiom (1.1b) on the `p`-torsion**: the corestriction of the local Brauer
group is bijective on the `p`-torsion, at every open `U ≤ D_A`. -/
theorem ltdCorH2_bijective_units_openSubgroup (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (U : Subgroup ↥(SSGRoute.decomp k A))
    (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A))) [U.FiniteIndex]
    [Fintype (↥(SSGRoute.decomp k A) ⧸ U)] :
    Function.Bijective
      (fun x : {y : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) // p • y = 0} =>
        (⟨Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)) x.1, by
            rw [← map_nsmul, x.2, map_zero]⟩ :
          {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) //
            p • y = 0})) := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hcardW : Nat.card {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
      (Additive (Units Ω)) // p • y = 0} = p :=
    Work.SSGRoute.Nakayama.br_pTorsion p k Ω A hA
  have hcardV : Nat.card {y : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) // p • y = 0} = p :=
    Work.SSGRoute.PT.cardH2_units_openSubgroup_decomp p k Ω A hA U hU
  refine Work.SSGRoute.PT.bijective_of_nonzero_on_ptorsion
    (V := Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)))
    (W := Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))
    p (Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω))) hcardV hcardW ?_
  by_cases hp : p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U)
  · obtain ⟨v, hv, hvne⟩ := Work.SSGRoute.E7Fin.ptorsion_ne_zero_of_natCard_pt
      (V := Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω))) p hcardV
    exact ⟨v, hv, fun h0 =>
      hvne (Work.SSGRoute.E7Fin.corH2_injective_ptorsion_of_dvd_index_pt k Ω A hA U hU p hp
        v hv h0)⟩
  · haveI : Finite {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) //
        p • y = 0} := Nat.finite_of_card_ne_zero (by rw [hcardW]; exact hp0)
    haveI : Fintype {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) //
        p • y = 0} := Fintype.ofFinite _
    obtain ⟨y, hy⟩ : ∃ y : {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
        (Additive (Units Ω)) // p • y = 0},
        y ≠ (⟨0, by simp⟩ : {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
          (Additive (Units Ω)) // p • y = 0}) := by
      refine Fintype.exists_ne_of_one_lt_card ?_ (⟨0, by simp⟩ : {y : Work.AbsoluteKummer.H2
        ↥(SSGRoute.decomp k A) (Additive (Units Ω)) // p • y = 0})
      rw [Fintype.card_eq_nat_card, hcardW]
      exact (Fact.out : p.Prime).one_lt
    have hy0 : y.1 ≠ 0 := fun h => hy (Subtype.ext h)
    have hord : addOrderOf y.1 = p := addOrderOf_eq_prime y.2 hy0
    have hny : Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • y.1 ≠ 0 := by
      intro h
      have hdvd : addOrderOf y.1 ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U) :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
      rw [hord] at hdvd
      exact hp hdvd
    refine ⟨Work.SSGRoute.PT.resH2 U y.1, ?_, ?_⟩
    · rw [← map_nsmul, y.2, map_zero]
    · rw [Work.SSGRoute.PT.corH2_resH2 U hU (Additive (Units Ω)) y.1]; exact hny

end

end Work.SSGRoute.LTD02Proved
