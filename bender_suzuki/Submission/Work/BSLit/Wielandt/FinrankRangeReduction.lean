import Mathlib
import Submission.Work.BSLit.Wielandt.FreeRangeIdempotent
import Submission.Work.BSLit.Wielandt.NatCardQuotPowB
import Submission.Work.BSLit.Wielandt.exists_eq_mul_of_castHom_eq_zero
import Submission.Work.BSLit.Wielandt.exists_eq_algebraMap_mul_of_mapRingHom_eq_zero
import Submission.Work.BSLit.Wielandt.ForallMapRingHomEqZero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace Work.BSLit.Wielandt

open LinearMap

/-! ## Auxiliary lemmas

These are the module-theoretic ingredients of `FinrankRangeReduction`; they are stated in
Mathlib's vocabulary so they can be reused and are independent of the group algebra.
-/

/-- The number of elements of a free finitely generated module, computed from its rank. -/
theorem natCard_eq_card_pow_finrank {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [StrongRankCondition R] :
    Nat.card M = (Nat.card R) ^ (Module.finrank R M) := by
  rw [natCard_eq_pow_card_of_basis (Module.finBasis R M), Fintype.card_fin]

/-- Coefficientwise reduction `MonoidAlgebra.mapRingHom` is compatible with scalars:
reducing `r • x` gives `ψ r •` the reduction of `x`. -/
theorem mapRingHom_smul {R S : Type*} [CommSemiring R] [CommSemiring S]
    {M : Type*} [Monoid M] (ψ : R →+* S) (r : R) (x : MonoidAlgebra R M) :
    MonoidAlgebra.mapRingHom M ψ (r • x) = ψ r • MonoidAlgebra.mapRingHom M ψ x := by
  have h1 : MonoidAlgebra.mapRingHom M ψ (algebraMap R (MonoidAlgebra R M) r)
      = algebraMap S (MonoidAlgebra S M) (ψ r) := by simp
  rw [Algebra.smul_def, map_mul, h1, Algebra.smul_def]

/-- For an idempotent `P`, an element of its range is divisible by `s` in the ambient module if
and only if it is divisible by `s` inside the range. -/
theorem range_inf_smul_one {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : R) (P : M →ₗ[R] M) (hP : P * P = P) (a : LinearMap.range P) :
    (a : M) ∈ LinearMap.range (s • (1 : M →ₗ[R] M)) ↔
      a ∈ LinearMap.range (s • (1 : LinearMap.range P →ₗ[R] LinearMap.range P)) := by
  rw [LinearMap.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    have hv' : s • v = (a : M) := by simpa using hv
    have hPa : P (a : M) = (a : M) := by
      obtain ⟨w, hw⟩ := a.2
      rw [← hw]
      have h := congrArg (fun (f : M →ₗ[R] M) => f w) hP
      simpa using h
    refine ⟨⟨P v, LinearMap.mem_range_self P v⟩, ?_⟩
    apply Subtype.ext
    show s • P v = (a : M)
    rw [← LinearMap.map_smul, hv', hPa]
  · rintro ⟨b, hb⟩
    exact ⟨(b : M), congrArg Subtype.val hb⟩

/-! ## The rank reduction

The proof is a "purity" statement: the range `N = range α` of an idempotent `ZMod (p^k)`-linear
map is a direct summand of the free module `(ZMod (p^k)[F])^n`, hence free; the coefficientwise
reduction `ρ` maps `N` onto `range ᾱ` with kernel `pN`, so `range ᾱ ≃ N / pN` as groups; comparing
cardinalities via `NatCardQuotPowB` (`|N| = |N/pN|^k`) gives the equality of ranks. -/

theorem FinrankRangeReduction {F : Type*} [Group F] [Fintype F] {p k : ℕ} [Fact p.Prime]
    (hk : 1 ≤ k) {n : ℕ}
    (α : (Fin n → MonoidAlgebra (ZMod (p ^ k)) F) →ₗ[ZMod (p ^ k)]
      (Fin n → MonoidAlgebra (ZMod (p ^ k)) F)) (hα : α * α = α)
    (ᾱ : (Fin n → MonoidAlgebra (ZMod p) F) →ₗ[MonoidAlgebra (ZMod p) F]
      (Fin n → MonoidAlgebra (ZMod p) F)) (hᾱ : ᾱ * ᾱ = ᾱ)
    (hcomm : ∀ x : Fin n → MonoidAlgebra (ZMod (p ^ k)) F,
      (fun i => MonoidAlgebra.mapRingHom F
          (ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) (ZMod p)) (α x i))
        = ᾱ (fun i => MonoidAlgebra.mapRingHom F
          (ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) (ZMod p)) (x i))) :
    Module.finrank (ZMod (p ^ k)) ↥(LinearMap.range α)
      = Module.finrank (ZMod p) ↥(LinearMap.range ᾱ) := by
  classical
  have hp : p.Prime := Fact.out
  -- The reduction `ZMod (p^k) →+* ZMod p` and its coefficientwise extension to `(Fin n → ·)`
  let φ : ZMod (p ^ k) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) (ZMod p)
  have hφsurj : Function.Surjective (MonoidAlgebra.mapRingHom F φ) :=
    MonoidAlgebra.map_surjective (M := F) φ.toAddMonoidHom
      (ZMod.castHom_surjective (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)))
  haveI : RingHomSurjective φ :=
    ⟨ZMod.castHom_surjective (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk))⟩
  let ρ : (Fin n → MonoidAlgebra (ZMod (p ^ k)) F) →ₛₗ[φ]
      (Fin n → MonoidAlgebra (ZMod p) F) :=
    { toFun := fun x i => MonoidAlgebra.mapRingHom F φ (x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun r x => by
        funext i
        exact mapRingHom_smul φ r (x i) }
  have hρ_apply : ∀ (x : Fin n → MonoidAlgebra (ZMod (p ^ k)) F) (i : Fin n),
      ρ x i = MonoidAlgebra.mapRingHom F φ (x i) := fun x i => rfl
  -- `hcomm` is exactly the intertwining relation `ρ ∘ α = ᾱ ∘ ρ`
  have hcommρ : ∀ x, ρ (α x) = ᾱ (ρ x) := fun x => hcomm x
  have hρsurj : Function.Surjective ρ := by
    intro y
    choose x hx using fun i => hφsurj (y i)
    exact ⟨x, funext fun i => by rw [hρ_apply]; exact hx i⟩
  -- the kernel of the coefficientwise reduction on a single coordinate
  have hdiv : ∀ a : ZMod (p ^ k), φ a = 0 → ∃ b : ZMod (p ^ k), a = (p : ZMod (p ^ k)) * b :=
    fun a ha => exists_eq_mul_of_castHom_eq_zero (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) a ha
  have hpz : φ (p : ZMod (p ^ k)) = 0 := by
    rw [ZMod.castHom_apply, ZMod.cast_natCast (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) p,
      ZMod.natCast_self]
  have hker_single : ∀ c : MonoidAlgebra (ZMod (p ^ k)) F,
      MonoidAlgebra.mapRingHom F φ c = 0 ↔
        c ∈ LinearMap.range ((p : ZMod (p ^ k)) • (1 :
          MonoidAlgebra (ZMod (p ^ k)) F →ₗ[ZMod (p ^ k)] MonoidAlgebra (ZMod (p ^ k)) F)) := by
    intro c
    constructor
    · intro hc
      obtain ⟨z, hz⟩ :=
        exists_eq_algebraMap_mul_of_mapRingHom_eq_zero φ (p : ZMod (p ^ k)) hdiv c hc
      rw [LinearMap.mem_range]
      refine ⟨z, ?_⟩
      have hsz : ((p : ZMod (p ^ k)) • (1 : MonoidAlgebra (ZMod (p ^ k)) F →ₗ[ZMod (p ^ k)]
          MonoidAlgebra (ZMod (p ^ k)) F)) z = (p : ZMod (p ^ k)) • z := by simp
      rw [hsz, hz, Algebra.smul_def]
    · intro hc
      rw [LinearMap.mem_range] at hc
      obtain ⟨z, hz⟩ := hc
      have hsz : ((p : ZMod (p ^ k)) • (1 : MonoidAlgebra (ZMod (p ^ k)) F →ₗ[ZMod (p ^ k)]
          MonoidAlgebra (ZMod (p ^ k)) F)) z = (p : ZMod (p ^ k)) • z := by simp
      rw [← hz, hsz, mapRingHom_smul, hpz, zero_smul]
  -- the kernel of `ρ` is `p` times the ambient module
  have hkerρ : ρ.ker = LinearMap.range ((p : ZMod (p ^ k)) • (1 :
      (Fin n → MonoidAlgebra (ZMod (p ^ k)) F) →ₗ[ZMod (p ^ k)]
      (Fin n → MonoidAlgebra (ZMod (p ^ k)) F))) := by
    ext x
    rw [LinearMap.mem_ker, mem_range_smul_one_pi]
    constructor
    · intro hx i
      rw [← hker_single (x i)]
      have h := congrFun hx i
      rwa [hρ_apply, Pi.zero_apply] at h
    · intro hx
      funext i
      rw [hρ_apply, Pi.zero_apply, hker_single (x i)]
      exact hx i
  -- `ρ` maps `range α` onto `range ᾱ`
  have hmap_le : ∀ x ∈ LinearMap.range α, ρ x ∈ LinearMap.range ᾱ := by
    intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨z, hz⟩ := hx
    rw [← hz, hcommρ z]
    exact LinearMap.mem_range_self ᾱ (ρ z)
  -- the surjective additive homomorphism `range α → range ᾱ` induced by `ρ`
  let γ : (LinearMap.range α) →+ (LinearMap.range ᾱ) :=
    { toFun := fun x => ⟨ρ ↑x, hmap_le ↑x x.2⟩
      map_zero' := by apply Subtype.ext; simpa using map_zero ρ
      map_add' := by intro x y; apply Subtype.ext; simpa using map_add ρ ↑x ↑y }
  have hγ_apply : ∀ x : LinearMap.range α,
      ((γ x : LinearMap.range ᾱ) : Fin n → MonoidAlgebra (ZMod p) F) = ρ ↑x := fun x => rfl
  have hγsurj : Function.Surjective γ := by
    intro y
    have hy : (y : Fin n → MonoidAlgebra (ZMod p) F) ∈ LinearMap.range ᾱ := y.2
    rw [LinearMap.mem_range] at hy
    obtain ⟨w, hw⟩ := hy
    obtain ⟨v, hv⟩ := hρsurj w
    refine ⟨⟨α v, LinearMap.mem_range_self α v⟩, ?_⟩
    apply Subtype.ext
    show ρ (α v) = (y : Fin n → MonoidAlgebra (ZMod p) F)
    rw [hcommρ v, hv, hw]
  -- the kernel of `γ` is `p · range α`, using the idempotence of `α`
  have hγker : γ.ker = (LinearMap.range ((p : ZMod (p ^ k)) • (1 :
      LinearMap.range α →ₗ[ZMod (p ^ k)] LinearMap.range α))).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup]
    constructor
    · intro hx
      have hx' : (x : Fin n → MonoidAlgebra (ZMod (p ^ k)) F) ∈ ρ.ker := by
        rw [LinearMap.mem_ker]
        simpa [hγ_apply] using congrArg Subtype.val hx
      rw [hkerρ] at hx'
      exact (range_inf_smul_one (p : ZMod (p ^ k)) α hα x).1 hx'
    · intro hx
      have hx' : (x : Fin n → MonoidAlgebra (ZMod (p ^ k)) F) ∈ ρ.ker := by
        rw [hkerρ]
        exact (range_inf_smul_one (p : ZMod (p ^ k)) α hα x).2 hx
      rw [LinearMap.mem_ker] at hx'
      apply Subtype.ext
      simpa [hγ_apply] using hx'
  -- first isomorphism theorem: `range ᾱ` has the same cardinality as `range α / p·range α`
  have hcard : Nat.card ↥(LinearMap.range ᾱ)
      = Nat.card (↥(LinearMap.range α) ⧸ LinearMap.range ((p : ZMod (p ^ k)) • (1 :
          LinearMap.range α →ₗ[ZMod (p ^ k)] LinearMap.range α))) := by
    have h := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective γ hγsurj).toEquiv
    rw [hγker] at h
    exact h.symm
  -- `range α` is free and finite over `ZMod (p^k)` (the idempotent range of a free module)
  haveI hfree : Module.Free (ZMod (p ^ k)) ↥(LinearMap.range α) := (FreeRangeIdempotent hk α hα).1
  haveI hfin : Module.Finite (ZMod (p ^ k)) ↥(LinearMap.range α) := (FreeRangeIdempotent hk α hα).2
  haveI : Fact (1 < p ^ k) := ⟨Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hk) hp.one_lt⟩
  haveI : Nontrivial (ZMod (p ^ k)) := ZMod.nontrivial (p ^ k)
  haveI : StrongRankCondition (ZMod (p ^ k)) := inferInstance
  haveI hsfin : Module.Finite (ZMod p) ↥(LinearMap.range ᾱ) :=
    FiniteDimensional.finiteDimensional_submodule
      (Submodule.restrictScalars (ZMod p) (LinearMap.range ᾱ))
  haveI : StrongRankCondition (ZMod p) := inferInstance
  have h1 : Nat.card ↥(LinearMap.range α)
      = (p ^ k) ^ Module.finrank (ZMod (p ^ k)) ↥(LinearMap.range α) := by
    rw [natCard_eq_card_pow_finrank (R := ZMod (p ^ k)) (M := ↥(LinearMap.range α)), Nat.card_zmod]
  have h2 : Nat.card ↥(LinearMap.range ᾱ)
      = p ^ Module.finrank (ZMod p) ↥(LinearMap.range ᾱ) := by
    rw [natCard_eq_card_pow_finrank (R := ZMod p) (M := ↥(LinearMap.range ᾱ)), Nat.card_zmod]
  have h3 : Nat.card ↥(LinearMap.range α) =
      (Nat.card (↥(LinearMap.range α) ⧸ LinearMap.range ((p : ZMod (p ^ k)) • (1 :
          LinearMap.range α →ₗ[ZMod (p ^ k)] LinearMap.range α))))^k :=
    NatCardQuotPowB hk
  have hkey : (p ^ k) ^ Module.finrank (ZMod (p ^ k)) ↥(LinearMap.range α)
      = (p ^ k) ^ Module.finrank (ZMod p) ↥(LinearMap.range ᾱ) := by
    rw [← h1, h3, ← hcard, h2, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hp2 : 2 ≤ p ^ k := by
    have : 1 < p ^ k := Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hk) hp.one_lt
    omega
  exact Nat.pow_right_injective hp2 hkey

end Work.BSLit.Wielandt
