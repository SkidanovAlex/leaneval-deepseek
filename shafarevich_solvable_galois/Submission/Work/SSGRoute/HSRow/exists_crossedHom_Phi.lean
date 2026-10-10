import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Instances.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.HSRow.CokerFz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The crossed homomorphism `Φ : C → Zr` with prescribed value at `σ`

Construction of the locally constant crossed homomorphism `Φ` on `C = closure (zpowers σ)` with
values in the module `Zr` of locally constant `1`-cocycles on `I`, for the conjugation action
`twR` of `C`, sending `σ` to a prescribed `y ∈ Zr`.

The construction is the classical "partial sums of the orbit of `y`" one:

  `Φ γ = Σ_{i < χ(γ)} twR(σ)^i y`   (`χ : C →* Multiplicative (ZMod M)` continuous, `χ σ = 1`),

which is well defined (resp. a crossed homomorphism) as soon as the partial sums are `M`-periodic,
i.e. `Σ_{i<M} twR(σ)^i y = 0`, and as soon as the action of `C` on `Zr` is trivial modulo the
subgroup `χ.ker`.  Both are consequences of the following finiteness statements:

* `Br = ker cl ≅ M/(M^I)` carries the action `twR γ (δ m) = δ (res γ • m)`, so `(twR γ)^{|G|} = 1`
  on `Br` (`G = Gal(K/k)` finite);
* `Zr ⧸ Br ≅ H¹_loc(I,M)` is finite dimensional over `𝔽_p` by `hfin`, hence finite, so
  `(twR γ)^{|Perm (Zr ⧸ Br)|} = 1` on `Zr ⧸ Br`.

For `e' = |G| · |Perm (Zr ⧸ Br)|` the endomorphism `η = (twR γ)^{e'} - 1` therefore maps `Zr` into
`Br` and kills `Br`, whence `η² = 0` and, in characteristic `p`,
`(twR γ)^{p e'} = (1 + η)^p = 1 + p·η = 1` on all of `Zr`.  With `M = p²·e'` the partial sums
vanish and the above construction goes through.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.HSRow

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- The internal `1`-coboundary `i ↦ res(i) • m - m` on `I`, as an element of `Zr`. -/
def dZr (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (m : M) : ↥(Zr p k Ω K M I) :=
  ⟨fun i => SSGRoute.res k K (i : Ω ≃ₐ[k] Ω) • m - m, by
    refine ⟨?_, ?_⟩
    · intro g h
      show SSGRoute.res k K (((g * h : ↥I) : Ω ≃ₐ[k] Ω)) • m - m
        = (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • m - m)
          + SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)
              • (SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m - m)
      rw [Subgroup.coe_mul, map_mul, mul_smul, smul_sub]
      abel
    · refine ⟨(SSGRoute.res k K).ker, ?_, ?_⟩
      · have h : (SSGRoute.res k K).ker = K.fixingSubgroup :=
          IntermediateField.restrictNormalHom_ker (E := K)
        rw [h]
        exact IntermediateField.fixingSubgroup_isOpen K
      · intro g u hu
        have hu1 : SSGRoute.res k K (u : Ω ≃ₐ[k] Ω) = 1 := hu
        show SSGRoute.res k K (((g * u : ↥I) : Ω ≃ₐ[k] Ω)) • m - m
          = SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • m - m
        rw [Subgroup.coe_mul, map_mul, hu1, mul_one]⟩

@[simp] lemma dZr_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (m : M) (i : ↥I) :
    (dZr p k Ω K M I m : ↥I → M) i
      = SSGRoute.res k K (i : Ω ≃ₐ[k] Ω) • m - m := rfl

/-- Membership in `Br = ker cl`: the elements of `Br` are exactly the internal coboundaries. -/
lemma mem_Br_iff (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (f : ↥(Zr p k Ω K M I)) :
    f ∈ Br p k Ω K M I ↔
      ∃ m : M, ∀ i : ↥I, (f : ↥I → M) i = SSGRoute.res k K (i : Ω ≃ₐ[k] Ω) • m - m := by
  constructor
  · intro hf
    have hzero : cl p k Ω K M I f = 0 := (mem_Br p k Ω K M I f).mp hf
    rw [cl_apply] at hzero
    have hmem : ext0 p k Ω K M I (f : ↥I → M) ∈ SSGRoute.lcCocycles p k Ω K M I :=
      ext0_mem_lcCocycles p k Ω K M I f.2
    have hcob : ext0 p k Ω K M I (f : ↥I → M) ∈ SSGRoute.coboundaries p k Ω K M I :=
      (SSGRoute.toClass_eq_zero_iff p k Ω K M I hmem).mp hzero
    obtain ⟨m, hm⟩ := (SSGRoute.mem_coboundaries p k Ω K M I _).mp hcob
    exact ⟨m, fun i => by
      simpa using hm (i : Ω ≃ₐ[k] Ω) i.2⟩
  · rintro ⟨m, hm⟩
    refine (mem_Br p k Ω K M I f).mpr ?_
    rw [cl_apply, SSGRoute.toClass_eq_zero_iff p k Ω K M I
      (ext0_mem_lcCocycles p k Ω K M I f.2)]
    refine (SSGRoute.mem_coboundaries p k Ω K M I _).mpr ⟨m, fun n hn => ?_⟩
    rw [ext0_apply_mem p k Ω K M I _ hn]
    exact hm ⟨n, hn⟩

/-- The conjugation action on `Br`: `twR γ (δ m) = δ (res γ • m)`. -/
lemma twR_dZr (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (m : M) :
    twR p k Ω K M I σ H γ (dZr p k Ω K M I m)
      = dZr p k Ω K M I (SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • m) := by
  refine Subtype.ext (funext fun i => ?_)
  rw [twR_apply, dZr_apply, dZr_apply, conjI_coe]
  show SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
      • (SSGRoute.res k K (((γ : Ω ≃ₐ[k] Ω)⁻¹ * (i : Ω ≃ₐ[k] Ω) * (γ : Ω ≃ₐ[k] Ω)))
          • m - m)
    = SSGRoute.res k K (i : Ω ≃ₐ[k] Ω) • (SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • m)
      - SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω) • m
  rw [map_mul, map_mul, map_inv, smul_sub, mul_smul, ← mul_smul, mul_inv_cancel_left]

/-- `Br` is stable under `twR`. -/
lemma twR_mem_Br (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) {f : ↥(Zr p k Ω K M I)} (hf : f ∈ Br p k Ω K M I) :
    twR p k Ω K M I σ H γ f ∈ Br p k Ω K M I := by
  obtain ⟨m, hm⟩ := (mem_Br_iff p k Ω K M I f).mp hf
  have hf' : f = dZr p k Ω K M I m := Subtype.ext (funext fun i => by
    rw [dZr_apply]; exact hm i)
  rw [hf', twR_dZr]
  exact (mem_Br_iff p k Ω K M I _).mpr ⟨_, fun i => rfl⟩

/-- `Br ≤ comap (twR γ) Br`, the compatibility needed to descend `twR` to the quotient. -/
lemma Br_le_comap_twR (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) :
    Br p k Ω K M I ≤ Submodule.comap (twR p k Ω K M I σ H γ) (Br p k Ω K M I) :=
  fun f hf => twR_mem_Br p k Ω K M I σ H γ hf

/-! ### The action of `C` on the quotient `Zr ⧸ Br` -/

/-- The action of `γ ∈ C` on the quotient `Zr ⧸ Br = H¹_loc(I,M)`. -/
def twRQ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) (γ : ↥(Ccl k Ω σ)) :
    (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I) →ₗ[ZMod p]
      (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I) :=
  Submodule.mapQ (Br p k Ω K M I) (Br p k Ω K M I) (twR p k Ω K M I σ H γ)
    (Br_le_comap_twR p k Ω K M I σ H γ)

lemma twRQ_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (f : ↥(Zr p k Ω K M I)) :
    twRQ p k Ω K M I σ H γ (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (twR p k Ω K M I σ H γ f) :=
  Submodule.mapQ_apply _ _ _ f

lemma twRQ_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    twRQ p k Ω K M I σ H (1 : ↥(Ccl k Ω σ)) = 1 := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H f => rw [twRQ_apply, twR_one]; rfl

lemma twRQ_comp (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ δ : ↥(Ccl k Ω σ)) (x : ↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I) :
    twRQ p k Ω K M I σ H (γ * δ) x
      = twRQ p k Ω K M I σ H γ (twRQ p k Ω K M I σ H δ x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f => rw [twRQ_apply, twRQ_apply, twRQ_apply, twR_comp]

lemma twRQ_pow_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (n : ℕ) (f : ↥(Zr p k Ω K M I)) :
    ((twRQ p k Ω K M I σ H γ) ^ n) (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (((twR p k Ω K M I σ H γ) ^ n) f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, twRQ_apply, pow_succ', Module.End.mul_apply]

/-- `Zr ⧸ Br ≅ H¹_loc(I,M)` is finite whenever `H¹_loc(I,M)` is. -/
lemma finite_zrBr_quot (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω))
    (hfin : Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I)) :
    Finite (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I) := by
  haveI : Finite (Work.SSGRoute.H1loc p k Ω K M I) := Module.finite_of_finite (ZMod p)
  have e := LinearMap.quotKerEquivRange (cl p k Ω K M I)
  refine Finite.of_injective (fun x => (e x : Work.SSGRoute.H1loc p k Ω K M I)) ?_
  intro x y hxy
  exact e.injective (Subtype.ext hxy)

/-- The action of `C` on `Zr ⧸ Br` is by permutations of the finite set `Zr ⧸ Br`, so its order
divides the order of the permutation group of that set. -/
lemma twRQ_pow_factorial_eq_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) (γ : ↥(Ccl k Ω σ))
    (hfin : Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I)) :
    (twRQ p k Ω K M I σ H γ) ^ (Nat.factorial
      (Nat.card (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I))) = 1 := by
  haveI hFin : Finite (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I) :=
    finite_zrBr_quot p k Ω K M I hfin
  letI : Fintype (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I) := Fintype.ofFinite _
  have hcard : Nat.factorial (Nat.card (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I))
      = Fintype.card (Equiv.Perm (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I)) := by
    rw [Fintype.card_perm, Nat.card_eq_fintype_card]
  rw [hcard]
  have hinv : ∀ x, twRQ p k Ω K M I σ H γ⁻¹ (twRQ p k Ω K M I σ H γ x) = x := by
    intro x
    rw [← twRQ_comp, inv_mul_cancel, twRQ_one]
    rfl
  have hinj : Function.Injective (twRQ p k Ω K M I σ H γ) := by
    intro x y hxy
    have h := congrArg (fun z => twRQ p k Ω K M I σ H γ⁻¹ z) hxy
    rw [hinv, hinv] at h
    exact h
  have hsurj : Function.Surjective (twRQ p k Ω K M I σ H γ) := fun y =>
    ⟨twRQ p k Ω K M I σ H γ⁻¹ y, by
      rw [← twRQ_comp, mul_inv_cancel, twRQ_one]
      rfl⟩
  let T : Equiv.Perm (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I) :=
    Equiv.ofBijective (twRQ p k Ω K M I σ H γ) ⟨hinj, hsurj⟩
  have hT : (T : ↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I → _) = twRQ p k Ω K M I σ H γ := rfl
  refine LinearMap.ext fun x => ?_
  have h2 : (T ^ (Fintype.card (Equiv.Perm (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I)))) x
      = ((twRQ p k Ω K M I σ H γ) ^
          (Fintype.card (Equiv.Perm (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I)))) x := by
    rw [Equiv.Perm.coe_pow, hT]
    induction (Fintype.card (Equiv.Perm (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I))) with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, pow_succ', Module.End.mul_apply]
  rw [← h2]
  have hcard2 : T ^ (Fintype.card (Equiv.Perm (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I))) = 1 :=
    pow_card_eq_one
  rw [hcard2]
  rfl

/-- `(twR γ)^(Eper)` moves every element of `Zr` into `Br`. -/
lemma twR_pow_factorial_sub_mem_Br (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) (γ : ↥(Ccl k Ω σ))
    (hfin : Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I))
    (f : ↥(Zr p k Ω K M I)) :
    ((twR p k Ω K M I σ H γ) ^ (Nat.factorial
      (Nat.card (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I)))) f - f ∈ Br p k Ω K M I := by
  have h1 := congrArg
    (fun (l : (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I) →ₗ[ZMod p]
        (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I)) => l (Submodule.Quotient.mk f))
    (twRQ_pow_factorial_eq_one p k Ω K M I σ H γ hfin)
  rw [twRQ_pow_apply] at h1
  exact (Submodule.Quotient.eq (Br p k Ω K M I)).mp (by simpa using h1)

/-! ### The period of the action of `C` on `Br` -/

/-- `(twR γ)^k` acts on `dZr m` by `dZr ((res γ)^k • m)`. -/
lemma twR_pow_dZr (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (m : M) (n : ℕ) :
    ((twR p k Ω K M I σ H γ) ^ n) (dZr p k Ω K M I m)
      = dZr p k Ω K M I ((SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)) ^ n • m) := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, Module.End.one_eq_id, LinearMap.id_apply, one_smul]
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, twR_dZr, pow_succ', mul_smul]

/-- The action of `C` on `Br` has period dividing the order of `Gal(K/k)`. -/
lemma twR_pow_card_eq_self_of_mem_Br (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) {b : ↥(Zr p k Ω K M I)} (hb : b ∈ Br p k Ω K M I) :
    ((twR p k Ω K M I σ H γ) ^ (Nat.card (K ≃ₐ[k] K))) b = b := by
  obtain ⟨m, hm⟩ := (mem_Br_iff p k Ω K M I b).mp hb
  have hb' : b = dZr p k Ω K M I m := Subtype.ext (funext fun i => by
    rw [dZr_apply]; exact hm i)
  rw [hb', twR_pow_dZr]
  haveI : Finite (K ≃ₐ[k] K) := inferInstance
  letI : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  have hpow : (SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)) ^ (Nat.card (K ≃ₐ[k] K)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  rw [hpow, one_smul]

/-! ### Partial sums of the orbit of `y` -/

/-- The partial sums `Σ_{i<m} twR(σ)^i y`. -/
def Psum (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (y : ↥(Zr p k Ω K M I)) (m : ℕ) : ↥(Zr p k Ω K M I) :=
  ∑ i ∈ Finset.range m, ((twR p k Ω K M I σ H (sigC k Ω σ)) ^ i) y

lemma Psum_zero (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (y : ↥(Zr p k Ω K M I)) : Psum p k Ω K M I σ H y 0 = 0 := by
  simp [Psum]

lemma Psum_succ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (y : ↥(Zr p k Ω K M I)) (m : ℕ) :
    Psum p k Ω K M I σ H y (m + 1)
      = Psum p k Ω K M I σ H y m + ((twR p k Ω K M I σ H (sigC k Ω σ)) ^ m) y := by
  rw [Psum, Finset.sum_range_succ, Psum]

lemma Psum_add (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (y : ↥(Zr p k Ω K M I)) (a b : ℕ) :
    Psum p k Ω K M I σ H y (a + b)
      = Psum p k Ω K M I σ H y a
        + ((twR p k Ω K M I σ H (sigC k Ω σ)) ^ a) (Psum p k Ω K M I σ H y b) := by
  simp only [Psum, Finset.sum_range_add]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add, Module.End.mul_apply]

lemma Psum_mul (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (y : ↥(Zr p k Ω K M I)) (X j : ℕ) :
    Psum p k Ω K M I σ H y (j * X)
      = ∑ i ∈ Finset.range j,
          (((twR p k Ω K M I σ H (sigC k Ω σ)) ^ X) ^ i) (Psum p k Ω K M I σ H y X) := by
  induction j with
  | zero => simp [Psum]
  | succ j ih =>
      have hp : ((twR p k Ω K M I σ H (sigC k Ω σ)) ^ (j * X))
          = (((twR p k Ω K M I σ H (sigC k Ω σ)) ^ X) ^ j) := by
        rw [mul_comm j X, pow_mul]
      rw [Nat.succ_mul, Psum_add, ih, Finset.sum_range_succ, hp]

/-! ### The construction -/

theorem exists_crossedHom_Phi
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Work.SSGRoute.HSRow.Hcx k Ω I σ)
    (hZ : ∀ n : ℕ, 0 < n → ∃ f : ↥(Work.SSGRoute.HSRow.Ccl k Ω σ) →*
        Multiplicative (ZMod n), Function.Surjective f)
    (hfin : Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M I))
    (y : ↥(Work.SSGRoute.HSRow.Zr p k Ω K M I)) :
    ∃ Φ : ↥(Work.SSGRoute.HSRow.Ccl k Ω σ) → ↥(Work.SSGRoute.HSRow.Zr p k Ω K M I),
      Φ 1 = 0 ∧
      (∀ γ δ : ↥(Work.SSGRoute.HSRow.Ccl k Ω σ),
        Φ (γ * δ) = Φ γ + Work.SSGRoute.HSRow.twR p k Ω K M I σ H γ (Φ δ)) ∧
      (∃ W : Subgroup ↥(Work.SSGRoute.HSRow.Ccl k Ω σ),
        IsOpen (W : Set ↥(Work.SSGRoute.HSRow.Ccl k Ω σ)) ∧
        ∀ γ : ↥(Work.SSGRoute.HSRow.Ccl k Ω σ), ∀ u ∈ W, Φ (γ * u) = Φ γ) ∧
      Φ (Work.SSGRoute.HSRow.sigC k Ω σ) = y := by
  classical
  have hFinQ : Finite (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I) :=
    finite_zrBr_quot p k Ω K M I hfin
  letI : Fintype (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I) := Fintype.ofFinite _
  -- the exponents
  set Ep : ℕ := Nat.factorial (Nat.card (↥(Zr p k Ω K M I) ⧸ Br p k Ω K M I)) with hEp
  set G0 : ℕ := Nat.card (K ≃ₐ[k] K) with hG0
  set ee : ℕ := Ep * G0 with hee
  set MM : ℕ := p * (p * ee) with hMM
  have hEp_pos : 0 < Ep := by rw [hEp]; exact Nat.factorial_pos _
  have hG0_pos : 0 < G0 := by rw [hG0]; exact Nat.card_pos
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hMM_gt : 1 < MM := by
    rw [hMM, hee]
    have h1 : 1 < p := by omega
    have h2 : 0 < p * (Ep * G0) := by positivity
    exact lt_of_lt_of_le h1 (Nat.le_mul_of_pos_right p h2)
  have hMM_pos : 0 < MM := by omega
  haveI hNe : NeZero MM := ⟨by omega⟩
  -- (A) the action on the quotient has period `Ep`
  have hA : ∀ (w : ↥(Ccl k Ω σ)) (f : ↥(Zr p k Ω K M I)),
      ((twR p k Ω K M I σ H w) ^ Ep) f - f ∈ Br p k Ω K M I := by
    intro w f
    rw [hEp]
    exact twR_pow_factorial_sub_mem_Br p k Ω K M I σ H w hfin f
  -- (B) the action on `Br` has period `G0`
  have hB : ∀ (w : ↥(Ccl k Ω σ)) {b : ↥(Zr p k Ω K M I)}, b ∈ Br p k Ω K M I →
      ((twR p k Ω K M I σ H w) ^ G0) b = b := by
    intro w b hb
    rw [hG0]
    exact twR_pow_card_eq_self_of_mem_Br p k Ω K M I σ H w hb
  -- (C) `η = (twR w)^Ep - 1` takes values in `Br`
  have hC : ∀ (w : ↥(Ccl k Ω σ)) (f : ↥(Zr p k Ω K M I)),
      ((twR p k Ω K M I σ H w) ^ ee) f - f ∈ Br p k Ω K M I := by
    intro w f
    have h1 : (twR p k Ω K M I σ H w) ^ ee = ((twR p k Ω K M I σ H w) ^ Ep) ^ G0 := by
      rw [hee, pow_mul]
    rw [h1]
    have hstep : ∀ t : ℕ,
        (((twR p k Ω K M I σ H w) ^ Ep) ^ t) f - f ∈ Br p k Ω K M I := by
      intro t
      induction t with
      | zero =>
          rw [pow_zero, Module.End.one_eq_id, LinearMap.id_apply, sub_self]
          exact Submodule.zero_mem _
      | succ t ih =>
          have hh := hA w ((((twR p k Ω K M I σ H w) ^ Ep) ^ t) f)
          rw [pow_succ', Module.End.mul_apply]
          have h2 : ((twR p k Ω K M I σ H w) ^ Ep) ((((twR p k Ω K M I σ H w) ^ Ep) ^ t) f) - f
              = (((twR p k Ω K M I σ H w) ^ Ep) ((((twR p k Ω K M I σ H w) ^ Ep) ^ t) f) - (((twR p k Ω K M I σ H w) ^ Ep) ^ t) f) + (((((twR p k Ω K M I σ H w) ^ Ep) ^ t) f) - f) := by abel
          rw [h2]
          exact Submodule.add_mem _ hh ih
    exact hstep G0
  -- (D) `(twR w)^ee` fixes `Br`
  have hD : ∀ (w : ↥(Ccl k Ω σ)) {b : ↥(Zr p k Ω K M I)}, b ∈ Br p k Ω K M I →
      ((twR p k Ω K M I σ H w) ^ ee) b = b := by
    intro w b hb
    have h1 : (twR p k Ω K M I σ H w) ^ ee = ((twR p k Ω K M I σ H w) ^ G0) ^ Ep := by
      rw [hee, mul_comm Ep G0, pow_mul]
    rw [h1]
    have hstep : ∀ t : ℕ, (((twR p k Ω K M I σ H w) ^ G0) ^ t) b = b := by
      intro t
      induction t with
      | zero => rw [pow_zero, Module.End.one_eq_id, LinearMap.id_apply]
      | succ t ih => rw [pow_succ', Module.End.mul_apply, ih]; exact hB w hb
    exact hstep Ep
  -- (E) `(twR w)^(p * ee) = 1`
  have hE : ∀ w : ↥(Ccl k Ω σ), (twR p k Ω K M I σ H w) ^ (p * ee) = 1 := by
    intro w
    set η : Module.End (ZMod p) ↥(Zr p k Ω K M I) := (twR p k Ω K M I σ H w) ^ ee - 1 with hη
    have hηapp : ∀ f : ↥(Zr p k Ω K M I),
        η f = ((twR p k Ω K M I σ H w) ^ ee) f - f := by
      intro f
      rw [hη, LinearMap.sub_apply, Module.End.one_eq_id, LinearMap.id_apply]
    have hηQ : ∀ f : ↥(Zr p k Ω K M I), η f ∈ Br p k Ω K M I := by
      intro f
      rw [hηapp]
      exact hC w f
    have hηB : ∀ b ∈ Br p k Ω K M I, η b = 0 := by
      intro b hb
      rw [hηapp, hD w hb, sub_self]
    have hsq : η * η = 0 := by
      refine LinearMap.ext fun f => ?_
      rw [Module.End.mul_apply]
      exact hηB (η f) (hηQ f)
    have hsqapp : ∀ f : ↥(Zr p k Ω K M I), η (η f) = 0 := by
      intro f
      have h := congrArg (fun (l : Module.End (ZMod p) ↥(Zr p k Ω K M I)) => l f) hsq
      rw [Module.End.mul_apply, LinearMap.zero_apply] at h
      exact h
    have hpowe : ∀ t : ℕ, ∀ f : ↥(Zr p k Ω K M I),
        ((1 + η) ^ t) f = f + t • (η f) := by
      intro t
      induction t with
      | zero =>
          intro f
          rw [pow_zero, Module.End.one_eq_id, LinearMap.id_apply, zero_smul, add_zero]
      | succ t ih =>
          intro f
          rw [pow_succ', Module.End.mul_apply, ih, LinearMap.add_apply, Module.End.one_eq_id,
            LinearMap.id_apply, LinearMap.map_add, map_nsmul, hsqapp, smul_zero, add_zero,
            succ_nsmul]
          abel
    have h1ee : (1 + η) = (twR p k Ω K M I σ H w) ^ ee := by
      rw [hη]; abel
    rw [mul_comm p ee, pow_mul, ← h1ee]
    refine LinearMap.ext fun f => ?_
    rw [hpowe p f]
    have hp0 : p • (η f) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod p) p (η f), ZMod.natCast_self, zero_smul]
    rw [hp0, add_zero]
    rfl
  -- (F) `(twR w)^MM = 1`
  have hF : ∀ w : ↥(Ccl k Ω σ), (twR p k Ω K M I σ H w) ^ MM = 1 := by
    intro w
    rw [hMM, mul_comm p (p * ee), pow_mul, hE w, one_pow]
  -- the partial sums vanish over a full period `MM`
  have hsum0 : Psum p k Ω K M I σ H y MM = 0 := by
    have h1 : Psum p k Ω K M I σ H y (p * (p * ee))
        = ∑ i ∈ Finset.range p,
            (((twR p k Ω K M I σ H (sigC k Ω σ)) ^ (p * ee)) ^ i)
              (Psum p k Ω K M I σ H y (p * ee)) :=
      Psum_mul p k Ω K M I σ H y (p * ee) p
    rw [hMM, h1]
    have h2 : ∀ i ∈ Finset.range p,
        (((twR p k Ω K M I σ H (sigC k Ω σ)) ^ (p * ee)) ^ i)
            (Psum p k Ω K M I σ H y (p * ee))
          = Psum p k Ω K M I σ H y (p * ee) := by
      intro i _
      rw [hE (sigC k Ω σ), one_pow, Module.End.one_eq_id, LinearMap.id_apply]
    rw [Finset.sum_congr rfl h2]
    rw [Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul (ZMod p) p (Psum p k Ω K M I σ H y (p * ee)),
      ZMod.natCast_self, zero_smul]
  have hper : ∀ m : ℕ, Psum p k Ω K M I σ H y (m + MM) = Psum p k Ω K M I σ H y m := by
    intro m
    rw [Psum_add, hsum0, map_zero, add_zero]
  have hpermul : ∀ m q : ℕ, Psum p k Ω K M I σ H y (m + MM * q)
      = Psum p k Ω K M I σ H y m := by
    intro m q
    induction q with
    | zero => rw [Nat.mul_zero, add_zero]
    | succ q ih => rw [Nat.mul_succ, ← add_assoc, hper, ih]
  have hmod : ∀ n : ℕ, Psum p k Ω K M I σ H y (n % MM) = Psum p k Ω K M I σ H y n := by
    intro n
    have h : n = n % MM + MM * (n / MM) := (Nat.mod_add_div n MM).symm
    conv_rhs => rw [h]
    exact (hpermul (n % MM) (n / MM)).symm
  have hvaladd : ∀ a b : ZMod MM, Psum p k Ω K M I σ H y ((a + b).val)
      = Psum p k Ω K M I σ H y (a.val + b.val) := by
    intro a b
    rw [ZMod.val_add, hmod]
  -- the character and the value of `twR` in terms of `τ = twR σ`
  obtain ⟨χ, hχcont, hχσ⟩ := exists_chiC k Ω σ MM hMM_pos hZ
  have hmul : ∀ γ δ : ↥(Ccl k Ω σ), twR p k Ω K M I σ H (γ * δ)
      = (twR p k Ω K M I σ H γ).comp (twR p k Ω K M I σ H δ) := by
    intro γ δ
    refine LinearMap.ext fun f => ?_
    rw [LinearMap.comp_apply]
    exact (twR_comp p k Ω K M I σ H γ δ f).symm
  have hpow : ∀ (γ : ↥(Ccl k Ω σ)) (n : ℕ), twR p k Ω K M I σ H (γ ^ n)
      = (twR p k Ω K M I σ H γ) ^ n := by
    intro γ n
    induction n with
    | zero => rw [pow_zero, pow_zero, twR_one, Module.End.one_eq_id]
    | succ n ih =>
        rw [pow_succ, hmul, ih, pow_succ, Module.End.mul_eq_comp]
  have htwR : ∀ γ : ↥(Ccl k Ω σ), twR p k Ω K M I σ H γ
      = (twR p k Ω K M I σ H (sigC k Ω σ)) ^ ((χ γ).toAdd.val) := by
    intro γ
    obtain ⟨j, hj, w, hw⟩ :=
      Work.SSGRoute.HSTwoRow.exists_pow_mul_pow_zpowersClosure k Ω σ MM hMM_pos γ
    have hsig : (⟨σ, Subgroup.le_topologicalClosure (Subgroup.zpowers σ)
        (Subgroup.mem_zpowers σ)⟩ : ↥(Ccl k Ω σ)) = sigC k Ω σ := Subtype.ext rfl
    rw [hsig] at hw
    have hχγ : (χ (sigC k Ω σ ^ j * w ^ MM)).toAdd = (j : ZMod MM) := by
      rw [map_mul, map_pow, map_pow, hχσ]
      simp
    have hvalj : (χ (sigC k Ω σ ^ j * w ^ MM)).toAdd.val = j := by
      rw [hχγ]
      exact ZMod.val_natCast_of_lt hj
    have hgoal : twR p k Ω K M I σ H (sigC k Ω σ ^ j * w ^ MM)
        = (twR p k Ω K M I σ H (sigC k Ω σ)) ^ j := by
      rw [hmul, hpow, hpow, hF w, Module.End.one_eq_id, LinearMap.comp_id]
    rw [hw, hvalj]
    exact hgoal
  refine ⟨fun γ => Psum p k Ω K M I σ H y ((χ γ).toAdd.val), ?_, ?_, ?_, ?_⟩
  · show Psum p k Ω K M I σ H y ((χ 1).toAdd.val) = 0
    simp [Psum_zero]
  · intro γ δ
    show Psum p k Ω K M I σ H y ((χ (γ * δ)).toAdd.val)
        = Psum p k Ω K M I σ H y ((χ γ).toAdd.val)
          + twR p k Ω K M I σ H γ (Psum p k Ω K M I σ H y ((χ δ).toAdd.val))
    have hχ : (χ (γ * δ)).toAdd = (χ γ).toAdd + (χ δ).toAdd := by
      rw [map_mul]
      simp
    rw [hχ, hvaladd, Psum_add, ← htwR γ]
  · refine ⟨χ.ker, ?_, ?_⟩
    · have h1 : (χ.ker : Set ↥(Ccl k Ω σ))
          = χ ⁻¹' ({1} : Set (Multiplicative (ZMod MM))) := rfl
      rw [h1]
      exact (isOpen_discrete _).preimage hχcont
    · intro γ u hu
      have hu1 : χ u = 1 := MonoidHom.mem_ker.mp hu
      show Psum p k Ω K M I σ H y ((χ (γ * u)).toAdd.val)
          = Psum p k Ω K M I σ H y ((χ γ).toAdd.val)
      rw [map_mul, hu1, mul_one]
  · show Psum p k Ω K M I σ H y ((χ (sigC k Ω σ)).toAdd.val) = y
    rw [hχσ]
    haveI : Fact (1 < MM) := ⟨hMM_gt⟩
    have h1 : (Multiplicative.ofAdd (1 : ZMod MM)).toAdd.val = 1 := by
      rw [show (Multiplicative.ofAdd (1 : ZMod MM)).toAdd = 1 from by simp]
      exact ZMod.val_one MM
    rw [h1]
    show Psum p k Ω K M I σ H y 1 = y
    rw [Psum, Finset.sum_range_one, pow_zero, Module.End.one_eq_id, LinearMap.id_apply]

end

end Work.SSGRoute.HSRow
