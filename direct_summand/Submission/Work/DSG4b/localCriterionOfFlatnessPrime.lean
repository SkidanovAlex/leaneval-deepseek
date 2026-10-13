import Mathlib
import Submission.Work.DSG4b.localCriterionOfFlatnessPrimeAux

/-!
# The local criterion of flatness (Stacks 00MK)

Let `R → S` be a local homomorphism of Noetherian local rings and let `M` be a finite `S`-module.
If `Tor₁^R(R/𝔪, M) = 0` — spelled out here as the injectivity of the natural map
`M ⊗[R] 𝔪 → M ⊗[R] R ≅ M` — then `M` is flat over `R`.

The proof follows Stacks 00MK:

* **Colength case** (`Work.DSG4b.tor1Subtype_colength`): if the map is injective for `𝔪`, it is
  injective for every ideal `J ⊇ 𝔪 ^ n` (equivalently: `R/J` of finite length).  This is the
  "infinite descent" argument: a maximal counterexample `K ⊇ J` is enlarged by an element
  `x ∈ 𝔪 ^ j \ K` (which satisfies `𝔪 x ⊆ K`), using the step lemma
  `injective_lTensor_of_sup_span`; iterating one reaches `K = ⊤`, which is injective.

* **General case** (`Work.DSG4b.flat_of_tor1_vanishing`): for an arbitrary ideal `I` and
  `ξ ∈ ker(M ⊗ I → M ⊗ R)`, the chase `mem_range_lTensor_inf_of_lTensor_eq_zero` shows that
  `ξ` lies in the image of `M ⊗ (I ⊓ 𝔪^n) → M ⊗ I` for every `n` (because `I ⊔ 𝔪^n` has finite
  colength).  Artin–Rees (`Ideal.exists_pow_inf_eq_pow_smul`) and
  `map_lTensor_mul_le_smul_top` turn this into `ξ ∈ 𝔪^(n-k) • ⊤`, so `ξ` lies in the `𝔪`-adic
  intersection of `M ⊗[R] I`; that vanishes by the Krull intersection theorem, because
  `M ⊗[R] I` is a finite `S`-module (`moduleFinite_tensorProduct_ideal`) and `𝔪S` is contained in
  the maximal ideal of `S`.  Conclude with `Module.Flat.iff_lTensor_injective`.
-/

namespace Work.DSG4b

open TensorProduct LinearMap

/-- `Tor₁^R(R/I, M) = 0`, spelled out as the injectivity of the natural map
`M ⊗[R] I → M ⊗[R] R` induced by the inclusion `I ⊆ R`. -/
private def Tor1 (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (I : Ideal R) : Prop :=
  Function.Injective (LinearMap.lTensor M (Submodule.subtype I))

/-! ### Auxiliary tensor computations

The four tensor computations used below (`injective_lTensor_of_sup_span`,
`mem_range_lTensor_inf_of_lTensor_eq_zero`, `map_lTensor_mul_le_smul_top`,
`moduleFinite_tensorProduct_ideal`) live in `Submission/Work/DSG4b/localCriterionOfFlatnessPrimeAux.lean`
and are imported above. -/

/-! ### The Krull intersection step -/

section Krull

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- The `𝔪`-adic filtration of an `S`-module is contained in the `𝔪S`-adic filtration. -/
private lemma mem_map_pow_smul_top_of_mem_pow_smul_top (I : Ideal R) (n : ℕ) {x : N}
    (hx : x ∈ I ^ n • (⊤ : Submodule R N)) :
    x ∈ (I.map (algebraMap R S)) ^ n • (⊤ : Submodule S N) := by
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => ?_)
  · rw [← IsScalarTower.algebraMap_smul S a y]
    refine Submodule.smul_mem_smul ?_ trivial
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  · exact Submodule.add_mem _ hx hy

/-- **Krull intersection step.**  If `ξ` lies in `𝔪 ^ n • ⊤` for every `n` in a finite module `N`
over the Noetherian local ring `S`, with `𝔪` mapping into the maximal ideal of `S`, then `ξ = 0`. -/
private theorem eq_zero_of_mem_all_pow_smul [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] [Module.Finite S N]
    (ξ : N) (h : ∀ m : ℕ, ξ ∈ (IsLocalRing.maximalIdeal R) ^ m • (⊤ : Submodule R N)) : ξ = 0 := by
  have hmem : ξ ∈ ⨅ i : ℕ,
      ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) ^ i • (⊤ : Submodule S N) := by
    rw [Submodule.mem_iInf]
    exact fun m => mem_map_pow_smul_top_of_mem_pow_smul_top _ m (h m)
  have hbot : (⨅ i : ℕ,
      ((IsLocalRing.maximalIdeal R).map (algebraMap R S)) ^ i • (⊤ : Submodule S N)) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _
      ((IsLocalRing.map_maximalIdeal_le (algebraMap R S)).trans
        (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal S)))
  rw [hbot] at hmem
  exact (Submodule.mem_bot S).mp hmem

end Krull

/-! ### The colength case (Stacks 00MJ) -/

section Colength

variable {R M : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]

omit [IsLocalRing R] in
/-- Tensoring the inclusion `⊤ → R` with `M` gives an injective map. -/
private lemma tor1_top : Tor1 R M (⊤ : Ideal R) := by
  have h : (Submodule.subtype (⊤ : Ideal R)) = (Submodule.topEquiv (R := R)).toLinearMap := by
    ext x; rfl
  rw [Tor1, h]
  exact LinearEquiv.injective (LinearEquiv.lTensor M (Submodule.topEquiv (R := R)))

/-- **Colength case of the local criterion of flatness** (Stacks 00MJ).  If
`M ⊗[R] 𝔪 → M ⊗[R] R` is injective, then so is `M ⊗[R] J → M ⊗[R] R` for every ideal `J`
containing a power of the maximal ideal. -/
private theorem tor1Subtype_colength [IsNoetherianRing R]
    (h𝔪 : Tor1 R M (IsLocalRing.maximalIdeal R)) (J : Ideal R) (n : ℕ)
    (hn : IsLocalRing.maximalIdeal R ^ n ≤ J) : Tor1 R M J := by
  by_contra hJ
  set Ω : Set (Ideal R) := {K | J ≤ K ∧ ¬ Tor1 R M K} with hΩ
  obtain ⟨K, hKΩ, hKmax⟩ :=
    (inferInstance : WellFoundedGT (Ideal R)).exists_maximal Ω ⟨J, le_rfl, hJ⟩
  have hJK : J ≤ K := hKΩ.1
  have hKbad : ¬ Tor1 R M K := hKΩ.2
  -- main claim: `𝔪 ^ (n - j) ≤ K` for every `j ≤ n`
  have key : ∀ j, j ≤ n → IsLocalRing.maximalIdeal R ^ (n - j) ≤ K := by
    intro j
    induction j with
    | zero => intro _; simpa using hn.trans hJK
    | succ j ih =>
      intro hj
      by_contra hnot
      obtain ⟨x, hxmem, hxK⟩ :
          ∃ x, x ∈ IsLocalRing.maximalIdeal R ^ (n - (j + 1)) ∧ x ∉ K := by
        simpa [IsConcreteLE.le_iff, not_forall] using hnot
      have hj' : j ≤ n := Nat.le_of_succ_le hj
      have hprev : IsLocalRing.maximalIdeal R ^ (n - j) ≤ K := ih hj'
      have hmul : ∀ a ∈ IsLocalRing.maximalIdeal R, a * x ∈ K := by
        intro a ha
        have h2 : a * x ∈
            IsLocalRing.maximalIdeal R * IsLocalRing.maximalIdeal R ^ (n - (j + 1)) :=
          Ideal.mul_mem_mul ha hxmem
        have h3 : IsLocalRing.maximalIdeal R *
            IsLocalRing.maximalIdeal R ^ (n - (j + 1)) =
              IsLocalRing.maximalIdeal R ^ (n - j) := by
          rw [← pow_succ', show n - (j + 1) + 1 = n - j from by omega]
        exact hprev (h3 ▸ h2)
      -- enlarging `K` keeps a counterexample, contradicting maximality
      have hbad' : ¬ Tor1 R M (K ⊔ Ideal.span {x}) := fun hinj =>
        hKbad (_root_.Work.DSG4b.injective_lTensor_of_sup_span K x hxK hmul h𝔪 hinj)
      have hle : K ≤ K ⊔ Ideal.span {x} := le_sup_left
      have hmem : (K ⊔ Ideal.span {x}) ∈ Ω := ⟨hJK.trans hle, hbad'⟩
      have hback : K ⊔ Ideal.span {x} ≤ K := hKmax hmem hle
      exact hxK (hback (Submodule.mem_sup_right (Ideal.mem_span_singleton_self x)))
  have htopK : K = ⊤ := le_antisymm le_top (by have := key n le_rfl; simpa using this)
  rw [htopK] at hKbad
  exact hKbad tor1_top

end Colength

/-! ### The general case -/

/-- **Local criterion of flatness** (Stacks 00MK): if `Tor₁^R(R/𝔪, M) = 0` for a finite module over
a Noetherian local `S` which is local over the Noetherian local `R`, then `M` is flat over `R`. -/
private theorem flat_of_tor1_vanishing {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M]
    (h𝔪 : Tor1 R M (IsLocalRing.maximalIdeal R)) : Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  have hfin : Module.Finite S (TensorProduct R M I) :=
    _root_.Work.DSG4b.moduleFinite_tensorProduct_ideal I
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro ξ hξ
  rw [LinearMap.mem_ker] at hξ
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (R := R) (M := R)
    (IsLocalRing.maximalIdeal R) I
  have har : ∀ m : ℕ, I ⊓ IsLocalRing.maximalIdeal R ^ (m + k) ≤
      IsLocalRing.maximalIdeal R ^ m * I := by
    intro m
    have h := hk (m + k) (Nat.le_add_left k m)
    simp only [Ideal.smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel] at h
    rw [inf_comm, h]
    exact Ideal.mul_mono_right (I := IsLocalRing.maximalIdeal R ^ m) inf_le_right
  refine eq_zero_of_mem_all_pow_smul (R := R) (S := S) (N := TensorProduct R M I) ξ (fun m => ?_)
  have h₁ := _root_.Work.DSG4b.mem_range_lTensor_inf_of_lTensor_eq_zero I (IsLocalRing.maximalIdeal R ^ (m + k))
    (tor1Subtype_colength h𝔪 (I ⊔ IsLocalRing.maximalIdeal R ^ (m + k)) (m + k) le_sup_right)
    ξ hξ
  obtain ⟨η, hη⟩ := LinearMap.mem_range.mp h₁
  rw [← hη]
  have hle := har m
  rw [show Submodule.inclusion (inf_le_left : I ⊓ IsLocalRing.maximalIdeal R ^ (m + k) ≤ I) =
      Submodule.inclusion (Ideal.mul_le_right : IsLocalRing.maximalIdeal R ^ m * I ≤ I) ∘ₗ
        Submodule.inclusion hle from rfl]
  rw [LinearMap.lTensor_comp]
  exact _root_.Work.DSG4b.map_lTensor_mul_le_smul_top (IsLocalRing.maximalIdeal R) I m
    (Submodule.mem_map_of_mem (Submodule.mem_top))

/-! ### The requested statement -/

/-- **Local criterion of flatness** (Stacks 00MK / Matsumura, Theorem 22.3).  Let `R → S` be a
local homomorphism of Noetherian local rings and let `M` be a finite `S`-module.  If the map
`M ⊗[R] 𝔪 → M`, `m ⊗ x ↦ x • m`, is injective (i.e. `Tor₁^R(R/𝔪, M) = 0`), then `M` is flat
over `R`. -/
theorem localCriterionOfFlatnessPrime {R S M : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M]
    (h : Function.Injective ((TensorProduct.rid R M).toLinearMap ∘ₗ
      LinearMap.lTensor M (IsLocalRing.maximalIdeal R).subtype)) :
    Module.Flat R M := by
  refine flat_of_tor1_vanishing (S := S) (h𝔪 := ?_)
  rw [Tor1]
  exact (Function.Injective.of_comp_iff (TensorProduct.rid R M).injective
    (⇑(LinearMap.lTensor M (IsLocalRing.maximalIdeal R).subtype))).mp h

end Work.DSG4b
