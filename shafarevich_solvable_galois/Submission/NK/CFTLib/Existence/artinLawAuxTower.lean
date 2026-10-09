import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.CyclotomicSubextension
import Submission.NK.CFTLib.ARL.artinReciprocity_cyclotomic
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace NK.CFTLib.Existence

open scoped NumberField
open NumberField

/-- The product of the images of a list under a multiplicative equivalence is the image of the
product.  (Stated for `MulEquiv` rather than `MonoidHom` so that the coercion of the equivalence
is matched syntactically in rewrites.) -/
private lemma list_prod_map_mulEquiv {ι : Type*} {M N : Type*} [Monoid M] [Monoid N]
    (f : M ≃* N) (l : List ι) (g : ι → M) :
    (l.map (fun i => f (g i))).prod = f ((l.map g).prod) := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih, map_mul]

/-- The product condition `NK.CFTLib.artinKillsPrincipal` is carried forward by a `k`-algebra
isomorphism of Galois extensions of `k`: conjugation by the isomorphism is a multiplicative
equivalence of the Galois groups which preserves the Frobenius property at every prime, and the
product condition only involves the group structure of `Gal(L/k)` together with
`NK.Chebotarev.IsFrobAtPrime`. -/
private lemma artinKillsPrincipal_algEquiv_aux {k L₁ L₂ : Type*} [Field k] [NumberField k]
    [Field L₁] [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra k L₁] [Algebra k L₂]
    [FiniteDimensional k L₁] [FiniteDimensional k L₂] [IsGalois k L₁] [IsGalois k L₂]
    (e : L₁ ≃ₐ[k] L₂) (m : ℕ) :
    NK.CFTLib.artinKillsPrincipal k L₁ m → NK.CFTLib.artinKillsPrincipal k L₂ m := by
  intro h a ha hpos s ex σ hs hfac hσ
  -- the multiplicative equivalence `Gal(L₁/k) ≃* Gal(L₂/k)` given by conjugation along `e`
  let ψ : Gal(L₁/k) ≃* Gal(L₂/k) := AlgEquiv.autCongr e
  -- the conjugate of a Frobenius in `L₂` is a Frobenius in `L₁`
  let τ : NK.Chebotarev.PrimeIdeal k → Gal(L₁/k) := fun p => ψ.symm (σ p)
  have hτ : ∀ p ∈ s, NK.Chebotarev.IsFrobAtPrime (K := k) (L := L₁) p (τ p) := by
    intro p hp
    rw [NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase e (τ p) p]
    have hconj : e.symm.trans ((τ p).trans e) = σ p := by
      rw [← AlgEquiv.autCongr_apply e (τ p)]
      exact MulEquiv.apply_symm_apply ψ (σ p)
    rw [hconj]
    exact hσ p hp
  -- apply the product condition in `L₁` and push the conclusion through `ψ`
  have h1 : (s.toList.map (fun p => τ p ^ ex p)).prod = 1 := h a ha hpos s ex τ hs hfac hτ
  have key := congrArg ψ h1
  rw [map_one] at key
  rw [← list_prod_map_mulEquiv ψ s.toList (fun p => τ p ^ ex p)] at key
  have hmap : s.toList.map (fun p => ψ (τ p ^ ex p))
      = s.toList.map (fun p => σ p ^ ex p) := by
    apply List.map_congr_left
    intro p _
    rw [map_pow]
    congr 1
    exact MulEquiv.apply_symm_apply ψ (σ p)
  rw [hmap] at key
  exact key

/-- The product condition `NK.CFTLib.artinKillsPrincipal` is invariant under a `k`-algebra
isomorphism of Galois extensions of `k`. -/
private theorem artinKillsPrincipal_algEquiv {k L₁ L₂ : Type*} [Field k] [NumberField k]
    [Field L₁] [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra k L₁] [Algebra k L₂]
    [FiniteDimensional k L₁] [FiniteDimensional k L₂] [IsGalois k L₁] [IsGalois k L₂]
    (e : L₁ ≃ₐ[k] L₂) (m : ℕ) :
    NK.CFTLib.artinKillsPrincipal k L₁ m ↔ NK.CFTLib.artinKillsPrincipal k L₂ m :=
  ⟨artinKillsPrincipal_algEquiv_aux e m, artinKillsPrincipal_algEquiv_aux e.symm m⟩

/-- **Unramifiedness from a modulus divisible by the norms of the differents.**  If `m` is a
multiple of `N(𝔡_{E/L₀})` and of `N(𝔡_{L₀/K})`, then every prime `𝔮` of `L₀` not dividing `(m)` is
unramified in `E`, and every prime `𝔭` of `K` not dividing `(m)` is unramified in `M`
(here `M` is any intermediate field such that `E/K` and `M` sit in a tower `K ⊆ M ⊆ E`). -/
private theorem ramificationAux {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E]
    (L₀ M : IntermediateField K E) (m : ℕ)
    (hB : Ideal.absNorm (differentIdeal (𝓞 ↥L₀) (𝓞 E)) ∣ m)
    (hC : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 ↥L₀)) ∣ m) :
    (∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥L₀, (m : 𝓞 ↥L₀) ∉ 𝔮.asIdeal →
        Ideal.ramificationIdxIn 𝔮.asIdeal (𝓞 E) = 1) ∧
    (∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥L₀, (m : 𝓞 ↥L₀) ∉ 𝔮.asIdeal →
        ∀ 𝔔 : NK.Chebotarev.PrimeIdeal E, 𝔔.asIdeal.LiesOver 𝔮.asIdeal →
          𝔔.asIdeal.ramificationIdx (𝓞 ↥L₀) = 1) ∧
    (∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ 𝔭.asIdeal →
        ∀ Q : NK.Chebotarev.PrimeIdeal ↥M, Q.asIdeal.LiesOver 𝔭.asIdeal →
          Q.asIdeal.ramificationIdx (𝓞 K) = 1) := by
  classical
  have h2 : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥L₀, (m : 𝓞 ↥L₀) ∉ 𝔮.asIdeal →
      ∀ 𝔔 : NK.Chebotarev.PrimeIdeal E, 𝔔.asIdeal.LiesOver 𝔮.asIdeal →
        𝔔.asIdeal.ramificationIdx (𝓞 ↥L₀) = 1 := by
    intro 𝔮 h𝔮 𝔔 h𝔔
    refine NK.CFTLib.ramificationIdx_eq_one_of_absNorm_differentIdeal_notMem 𝔮 𝔔 h𝔔 ?_
    intro hmem
    apply h𝔮
    obtain ⟨k, rfl⟩ := hB
    push_cast
    exact Ideal.mul_mem_right (k : 𝓞 ↥L₀) 𝔮.asIdeal hmem
  refine ⟨?_, h2, ?_⟩
  · intro 𝔮 h𝔮
    obtain ⟨Q⟩ : Nonempty (𝔮.asIdeal.primesOver (𝓞 E)) := inferInstance
    rw [Ideal.ramificationIdxIn]
    split_ifs with h
    · haveI := h.choose_spec.2
      exact h2 𝔮 h𝔮 ⟨h.choose, h.choose_spec.1,
        Ideal.ne_bot_of_liesOver_of_ne_bot 𝔮.ne_bot h.choose⟩ h.choose_spec.2
    · exact absurd ⟨Q.1, inferInstance, inferInstance⟩ h
  · intro 𝔭 h𝔭 Q hQ
    obtain ⟨Q'⟩ : Nonempty (Q.asIdeal.primesOver (𝓞 E)) := inferInstance
    let 𝔔 : NK.Chebotarev.PrimeIdeal E :=
      ⟨Q'.1, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot Q.ne_bot Q'.1⟩
    haveI h𝔔Q : 𝔔.asIdeal.LiesOver Q.asIdeal := inferInstance
    have h𝔔K : 𝔔.asIdeal.LiesOver 𝔭.asIdeal := by
      haveI := hQ
      exact Ideal.LiesOver.trans 𝔔.asIdeal Q.asIdeal 𝔭.asIdeal
    haveI h𝔔𝔮 : 𝔔.asIdeal.LiesOver (𝔔.asIdeal.under (𝓞 ↥L₀)) := inferInstance
    have h𝔮𝔭 : (𝔔.asIdeal.under (𝓞 ↥L₀)).LiesOver 𝔭.asIdeal := by
      haveI := h𝔔K
      exact Ideal.LiesOver.tower_bot 𝔔.asIdeal (𝔔.asIdeal.under (𝓞 ↥L₀)) 𝔭.asIdeal
    let 𝔮 : NK.Chebotarev.PrimeIdeal ↥L₀ :=
      ⟨𝔔.asIdeal.under (𝓞 ↥L₀), inferInstance, by
        haveI := h𝔮𝔭
        exact Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _⟩
    have h𝔮m : (m : 𝓞 ↥L₀) ∉ 𝔮.asIdeal := by
      haveI := h𝔮𝔭
      intro hm
      exact h𝔭 ((Ideal.mem_of_liesOver 𝔮.asIdeal 𝔭.asIdeal (m : 𝓞 K)).mpr (by simpa using hm))
    have h𝔮𝔭1 : 𝔮.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      refine NK.CFTLib.ramificationIdx_eq_one_of_absNorm_differentIdeal_notMem 𝔭 𝔮 h𝔮𝔭 ?_
      intro hmem
      apply h𝔭
      obtain ⟨k, rfl⟩ := hC
      push_cast
      exact Ideal.mul_mem_right (k : 𝓞 K) 𝔭.asIdeal hmem
    have h𝔔𝔮1 : 𝔔.asIdeal.ramificationIdx (𝓞 ↥L₀) = 1 := h2 𝔮 h𝔮m 𝔔 h𝔔𝔮
    have hE1 : 𝔔.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      rw [Ideal.ramificationIdx_tower (S := 𝓞 ↥L₀) (T := 𝓞 E) 𝔮.asIdeal 𝔔.asIdeal,
        h𝔮𝔭1, h𝔔𝔮1, mul_one]
    have hmul : Q.asIdeal.ramificationIdx (𝓞 K) * 𝔔.asIdeal.ramificationIdx (𝓞 ↥M) = 1 := by
      rw [← Ideal.ramificationIdx_tower (S := 𝓞 ↥M) (T := 𝓞 E) Q.asIdeal 𝔔.asIdeal, hE1]
    exact Nat.eq_one_of_mul_eq_one_right hmul

/-- The cyclotomic case of the ideal-theoretic Artin reciprocity law for the auxiliary tower: for `K ⊆ L₀, M ⊆ E` with `L₀ ⊓ M = ⊥`, `L₀ ⊔ M = ⊤` and `E/L₀` a subextension of the cyclotomic extension `Ω/L₀` of prime conductor `q` (injective `↥L₀`-algebra map `φ`), there is a modulus `m > 0` such that primes of `L₀` (resp. `K`) not dividing `m` are unramified in `E/L₀` (resp. in `M/K`), with the same statement in the `ramificationIdx` form, and `NK.CFTLib.artinKillsPrincipal ↥L₀ E m` holds. Route: the cyclotomic case `NK.CFTLib.artinKillsPrincipal_of_le_isCyclotomicExtension` (base case `NK.CFTLib.ARL.artinReciprocity_cyclotomic`) applied to the intermediate field `φ.fieldRange ⊆ Ω`, transported along `φ` with `NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase` / `Submission/Work/NUV2/ArtinBridge/AuxiliaryTower/artinKillsPrincipal_algEquiv.lean` (sorry-free), using `NK.CFTLib.artinKillsPrincipal.mono` and `NK.CFTLib.ramificationIdx_eq_one_of_absNorm_differentIdeal_notMem`; take `m := q * N(𝔡_{E'/↥L₀}) * N(𝔡_{E/↥L₀}) * N(𝔡_{↥L₀/K})`. Do NOT use the sorry'd `NK.NUV2.ArtinBridge.AuxiliaryTower.artinLaw`. -/
theorem artinLawAuxTower {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (L₀ M : IntermediateField K E) [IsGalois K ↥L₀] [IsGalois K ↥M]
    (hdisj : L₀ ⊓ M = ⊥) (hsup : L₀ ⊔ M = ⊤)
    (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra ↥L₀ Ω] [IsScalarTower K ↥L₀ Ω]
    [FiniteDimensional ↥L₀ Ω] (q : ℕ) (hq : Nat.Prime q)
    (hcycΩ : IsCyclotomicExtension {q} ↥L₀ Ω) (φ : E →ₐ[↥L₀] Ω) (hφ : Function.Injective φ) :
    ∃ m : ℕ, 0 < m ∧
      (∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L₀),
        (m : NumberField.RingOfIntegers ↥L₀) ∉ 𝔮.asIdeal →
        Ideal.ramificationIdxIn 𝔮.asIdeal (NumberField.RingOfIntegers E) = 1) ∧
      (∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L₀),
        (m : NumberField.RingOfIntegers ↥L₀) ∉ 𝔮.asIdeal →
        ∀ 𝔔 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E),
          𝔔.asIdeal.LiesOver 𝔮.asIdeal →
          𝔔.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥L₀) = 1) ∧
      (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
        ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M),
          Q.asIdeal.LiesOver 𝔭.asIdeal →
          Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) ∧
      NK.CFTLib.artinKillsPrincipal ↥L₀ E m := by
  classical
  haveI hgalE : IsGalois ↥L₀ E := inferInstance
  let E' : IntermediateField ↥L₀ Ω := φ.fieldRange
  let e : E ≃ₐ[↥L₀] ↥E' := AlgHom.equivFieldRange φ
  haveI hgalE' : IsGalois ↥L₀ ↥E' := IsGalois.of_algEquiv e
  haveI hnfΩ : NumberField Ω := NumberField.of_module_finite ↥L₀ Ω
  haveI hgalΩ : IsGalois ↥L₀ Ω := IsCyclotomicExtension.isGalois {q} ↥L₀ Ω
  haveI hcyc : IsCyclotomicExtension {q} ↥L₀ Ω := hcycΩ
  haveI hq0 : NeZero q := ⟨hq.ne_zero⟩
  have hbase : NK.CFTLib.artinKillsPrincipal ↥L₀ Ω q := fun a ha hpos s e σ hs hfac hfrob =>
    NK.CFTLib.ARL.artinReciprocity_cyclotomic ↥L₀ Ω q a ha hpos s e σ hs hfac hfrob
  have hE' : NK.CFTLib.artinKillsPrincipal ↥L₀ ↥E'
      (q * Ideal.absNorm (differentIdeal (𝓞 ↥L₀) (𝓞 ↥E'))) :=
    NK.CFTLib.artinKillsPrincipal_of_le_isCyclotomicExtension hbase E'
  have hE : NK.CFTLib.artinKillsPrincipal ↥L₀ E
      (q * Ideal.absNorm (differentIdeal (𝓞 ↥L₀) (𝓞 ↥E'))) :=
    (artinKillsPrincipal_algEquiv e _).mpr hE'
  let A : ℕ := Ideal.absNorm (differentIdeal (𝓞 ↥L₀) (𝓞 ↥E'))
  let B : ℕ := Ideal.absNorm (differentIdeal (𝓞 ↥L₀) (𝓞 E))
  let C : ℕ := Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 ↥L₀))
  let m : ℕ := q * A * B * C
  have hA0 : A ≠ 0 := by
    rw [show A = Ideal.absNorm (differentIdeal (𝓞 ↥L₀) (𝓞 ↥E')) from rfl,
      Ideal.absNorm_ne_zero_iff]
    exact Ring.HasFiniteQuotients.finiteQuotient
      (differentIdeal_ne_bot (A := 𝓞 ↥L₀) (B := 𝓞 ↥E'))
  have hB0 : B ≠ 0 := by
    rw [show B = Ideal.absNorm (differentIdeal (𝓞 ↥L₀) (𝓞 E)) from rfl,
      Ideal.absNorm_ne_zero_iff]
    exact Ring.HasFiniteQuotients.finiteQuotient
      (differentIdeal_ne_bot (A := 𝓞 ↥L₀) (B := 𝓞 E))
  have hC0 : C ≠ 0 := by
    rw [show C = Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 ↥L₀)) from rfl,
      Ideal.absNorm_ne_zero_iff]
    exact Ring.HasFiniteQuotients.finiteQuotient
      (differentIdeal_ne_bot (A := 𝓞 K) (B := 𝓞 ↥L₀))
  have hBdvd : B ∣ m := ⟨q * A * C, by rw [show m = q * A * B * C from rfl]; ring⟩
  have hCdvd : C ∣ m := ⟨q * A * B, by rw [show m = q * A * B * C from rfl]; ring⟩
  have hAdvd : q * A ∣ m := ⟨B * C, by rw [show m = q * A * B * C from rfl]; ring⟩
  refine ⟨m, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show m = q * A * B * C from rfl]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hq.pos (Nat.pos_of_ne_zero hA0))
      (Nat.pos_of_ne_zero hB0)) (Nat.pos_of_ne_zero hC0)
  · exact (ramificationAux L₀ M m hBdvd hCdvd).1
  · exact (ramificationAux L₀ M m hBdvd hCdvd).2.1
  · exact (ramificationAux L₀ M m hBdvd hCdvd).2.2
  · exact hE.mono hAdvd

end NK.CFTLib.Existence
