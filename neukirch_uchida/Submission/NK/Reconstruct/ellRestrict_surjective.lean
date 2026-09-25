import Mathlib
import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.GammaSup
import Submission.NK.Reconstruct.ellPart_map_le

/-!
# Surjectivity of the transition maps `Γ_{M,ℓ} → Γ_{L,ℓ}`

The projective system whose limit is Shimizu's `Γ_K = G_K^{ab,(ℓ),/tor}`
(`NK.Reconstruct.Gamma`) is indexed by the finite normal number-field levels `L ⊆ K'` of `K`,
and its transition maps are

`NK.Reconstruct.ellRestrict ℓ L M h : Γ_{M,ℓ} →* Γ_{L,ℓ}`  (`L ⊆ M`).

For the limit to have the expected properties (for instance for the projections
`Γ_K → Γ_{L,ℓ}` to be surjective, `NK.Reconstruct.Gamma.proj_surjective`, or for the Frobenius
elements of the finite levels to glue) the transition maps have to be **surjective**: every
ℓ-primary class on the smaller level `L` comes from one on the larger level `M`.

This file proves that.  Themathematically the matter is:

* restriction `Gal(M/K) → Gal(L/K)` is surjective (`Ω_{M/L} ≠ ∅`, `L/K` normal), hence so is its
  abelianisation `levelRestrict : Gal(M/K)^ab → Gal(L/K)^ab` (`levelRestrict_surjective`);
* the ℓ-primary part functor is **exact** on finite abelian groups: a surjection of finite abelian
  groups carries the ℓ-primary part of the source onto the ℓ-primary part of the target
  (`ellPart_map_eq_of_surjective`), because the quotient of a finite abelian group by its
  ℓ-primary part is free of ℓ-torsion, hence of order coprime to `ℓ` (Cauchy's theorem)
  (`ellPart_quotient_pow_eq_one`, `coprime_card_ellPart_quotient`).

Assembling the two gives `ellRestrict_surjective`.
-/

set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open scoped Pointwise

/-! ## Exactness of the ℓ-primary part on finite commutative groups -/

section EllPart

variable {A : Type*} [CommGroup A] {B : Type*} [CommGroup B]

/-- **The quotient of a finite commutative group by its ℓ-primary part has no ℓ-power torsion.**

Indeed if `a ^ (ℓ ^ n) ∈ A_ℓ`, say `(a ^ (ℓ ^ n)) ^ (ℓ ^ k) = 1`, then `a ^ (ℓ ^ (n + k)) = 1`,
so already `a ∈ A_ℓ`. -/
theorem ellPart_quotient_pow_eq_one [Finite A] (ℓ n : ℕ) (a : A ⧸ (ellPart A ℓ))
    (ha : a ^ (ℓ ^ n) = 1) : a = 1 := by
  classical
  haveI hN : (ellPart A ℓ).Normal := Subgroup.normal_of_isMulCommutative _
  revert ha
  refine QuotientGroup.induction_on a (fun x => ?_)
  intro ha
  have hmem : x ^ (ℓ ^ n) ∈ ellPart A ℓ := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 : (QuotientGroup.mk' (ellPart A ℓ)) (x ^ (ℓ ^ n)) = 1 := by
      rw [map_pow]
      exact ha
    simpa using h1
  rw [QuotientGroup.eq_one_iff, mem_ellPart_iff]
  obtain ⟨k, hk⟩ := (mem_ellPart_iff ℓ (x ^ (ℓ ^ n))).mp hmem
  exact ⟨n + k, by rw [pow_add, pow_mul]; exact hk⟩

/-- **The order of `A ⧸ A_ℓ` is coprime to `ℓ`** for a finite commutative group `A`: a prime `p`
dividing both would, by Cauchy's theorem, produce an element of order `p` in `A ⧸ A_ℓ`, which is
killed by `ℓ` and therefore trivial, a contradiction. -/
theorem coprime_card_ellPart_quotient [Finite A] (ℓ : ℕ) :
    Nat.Coprime ℓ (Nat.card (A ⧸ (ellPart A ℓ))) := by
  classical
  haveI hN : (ellPart A ℓ).Normal := Subgroup.normal_of_isMulCommutative _
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpℓ : p ∣ ℓ := hpdvd.trans (Nat.gcd_dvd_left ℓ _)
  have hpcard : p ∣ Nat.card (A ⧸ (ellPart A ℓ)) := hpdvd.trans (Nat.gcd_dvd_right ℓ _)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hpcard
  have h1 : a ^ ℓ = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, ha]
    exact hpℓ
  have h2 : a = 1 := ellPart_quotient_pow_eq_one ℓ 1 a (by simpa using h1)
  have ha' : orderOf (1 : A ⧸ (ellPart A ℓ)) = p := by rw [← h2]; exact ha
  rw [orderOf_one] at ha'
  exact hp.one_lt.ne' ha'.symm

/-- **Exactness of the ℓ-primary part on finite commutative groups.**  A surjective homomorphism of
commutative groups with finite source carries the ℓ-primary part of the source *onto* the ℓ-primary
part of the target: the ℓ-primary part is the kernel of the projection to the ℓ-free quotient. -/
theorem ellPart_map_eq_of_surjective [Finite A] (ℓ : ℕ) (f : A →* B)
    (hf : Function.Surjective f) : (ellPart A ℓ).map f = ellPart B ℓ := by
  classical
  haveI hN : (ellPart A ℓ).Normal := Subgroup.normal_of_isMulCommutative _
  refine le_antisymm (ellPart_map_le ℓ f) ?_
  set C : Subgroup B := (ellPart A ℓ).map f with hC
  haveI hCn : C.Normal := Subgroup.normal_of_isMulCommutative C
  have hle : ellPart A ℓ ≤ Subgroup.comap f C := fun a haa => Subgroup.mem_map_of_mem f haa
  intro x hx
  obtain ⟨n, hn⟩ := (mem_ellPart_iff ℓ x).mp hx
  let φ : A ⧸ (ellPart A ℓ) →* B ⧸ C := QuotientGroup.map _ C f hle
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective C y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨QuotientGroup.mk' (ellPart A ℓ) a, by
      simpa [φ] using QuotientGroup.map_mk (ellPart A ℓ) C f hle a⟩
  obtain ⟨ā, hā⟩ := hφ (QuotientGroup.mk' C x)
  have hpow : (QuotientGroup.mk' C x) ^ (ℓ ^ n) = 1 := by
    rw [← map_pow, hn, map_one]
  have h1 : orderOf (QuotientGroup.mk' C x) ∣ ℓ ^ n := orderOf_dvd_of_pow_eq_one hpow
  have h2 : orderOf (QuotientGroup.mk' C x) ∣ Nat.card (A ⧸ (ellPart A ℓ)) := by
    rw [← hā]
    exact (orderOf_map_dvd φ ā).trans (orderOf_dvd_natCard ā)
  have h3 : orderOf (QuotientGroup.mk' C x) = 1 := by
    have hgcd : orderOf (QuotientGroup.mk' C x) ∣
        (ℓ ^ n).gcd (Nat.card (A ⧸ (ellPart A ℓ))) := Nat.dvd_gcd h1 h2
    rw [((coprime_card_ellPart_quotient (A := A) ℓ).pow_left n).gcd_eq_one, Nat.dvd_one] at hgcd
    exact hgcd
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

end EllPart

/-! ## Surjectivity of the restriction maps of the projective system -/

section Level

variable {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K'] [IsGalois K K']

/-- Conjugation by an algebra isomorphism is a bijection of automorphism groups (its inverse is
conjugation by the inverse isomorphism), hence surjective. -/
theorem algEquivConjHom_surjective {F X Y : Type*} [Field F] [Field X] [Field Y] [Algebra F X]
    [Algebra F Y] (e : X ≃ₐ[F] Y) : Function.Surjective (algEquivConjHom e) := by
  intro τ
  refine ⟨e.trans (τ.trans e.symm), ?_⟩
  ext x
  simp [algEquivConjHom]

/-- **The restriction of automorphisms `Gal(M/K) → Gal(L/K)` is surjective** for a pair of
levels `L ⊆ M` (both normal over `K`): by the normality of `L` inside `M` every automorphism of
`L` extends to `M`. -/
theorem levelRestrictHom_surjective (L M : FrobLevel K K') (h : L.L ≤ M.L) :
    Function.Surjective (levelRestrictHom L M h) := by
  haveI := normal_levelTo L M h
  have h1 : Function.Surjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M.L)
      (levelTo L M h)) :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥(levelTo L M h)) (E := ↥M.L)
  have h2 := (algEquivConjHom_surjective (levelToEquiv L M h)).comp h1
  simpa [levelRestrictHom, MonoidHom.coe_comp, Function.comp_def] using h2

/-- **The abelianisation of a surjective homomorphism is surjective**: the abelianisation is
generated by the image of the group. -/
theorem abelianization_map_surjective {G : Type*} [Group G] {H : Type*} [Group H] (f : G →* H)
    (hf : Function.Surjective f) : Function.Surjective (Abelianization.map f) := by
  intro y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (commutator H) y
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨Abelianization.of a, ?_⟩
  rw [Abelianization.map_of]
  rfl

/-- **The transition map `Gal(M/K)^{ab} → Gal(L/K)^{ab}` of the projective system is
surjective** — it is the abelianisation of the surjective restriction `levelRestrictHom`. -/
theorem levelRestrict_surjective (L M : FrobLevel K K') (h : L.L ≤ M.L) :
    Function.Surjective (levelRestrict L M h) := by
  simpa [levelRestrict] using
    abelianization_map_surjective (levelRestrictHom L M h) (levelRestrictHom_surjective L M h)

end Level

/-! ## The statement -/

theorem ellRestrict_surjective {K : Type*} [Field K] {K' : Type*} [Field K'] [Algebra K K']
    [IsGalois K K'] (ℓ : ℕ) {L M : FrobLevel K K'} (h : L.L ≤ M.L) :
    Function.Surjective (ellRestrict ℓ L M h) := by
  classical
  have hmap := ellPart_map_eq_of_surjective (A := LevelAbelianization M.L) ℓ
    (levelRestrict L M h) (levelRestrict_surjective L M h)
  intro y
  have hy : (y : LevelAbelianization L.L) ∈
      (ellPart (LevelAbelianization M.L) ℓ).map (levelRestrict L M h) := by
    rw [hmap]
    exact y.2
  obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨a, ha⟩, Subtype.ext (by simpa using hay)⟩

end NK.Reconstruct
