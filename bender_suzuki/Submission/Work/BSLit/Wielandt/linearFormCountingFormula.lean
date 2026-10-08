import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.BSLit.Wielandt.ExistsProjector
import Submission.Work.BSLit.Wielandt.LiftIdempotentMatrix
import Submission.Work.BSLit.Wielandt.TraceIdempotentRange
import Submission.Work.BSLit.Wielandt.FreeRangeIdempotent
import Submission.Work.BSLit.Wielandt.NatCardQuotPowB
import Submission.Work.BSLit.Wielandt.groupSum_mul_self
import Submission.Work.BSLit.Wielandt.exists_lift_endomorphism
import Submission.Work.BSLit.Wielandt.FinrankRangeReduction
import Submission.Work.BSLit.Wielandt.RangeAveragingEqInvariants
import Submission.Work.BSLit.Wielandt.RankRangeLsmulComp
import Submission.Work.BSLit.Wielandt.intCastZmodEqZero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 2000000

namespace Work.BSLit.Wielandt

open Classical

variable {F : Type*} [Group F] [Fintype F]

/-! ## The coefficientwise reduction `(ℤ/q^k)[F] → 𝔽_q[F]`

Throughout, `q` is a prime (so `𝔽_q = ZMod q` is a field) and `k ≥ 1`.
-/

/-- The coefficientwise reduction of the group algebra `(ℤ/q^k)[F]` onto `𝔽_q[F]`, induced by
the reduction `ZMod (q^k) →+* ZMod q` of the coefficients. -/
noncomputable def redAlg {q k : ℕ} [Fact q.Prime] (hk : 1 ≤ k) :
    MonoidAlgebra (ZMod (q ^ k)) F →+* MonoidAlgebra (ZMod q) F :=
  MonoidAlgebra.mapRingHom F
    (ZMod.castHom (dvd_pow_self q (Nat.pos_iff_ne_zero.mp hk)) (ZMod q))

/-- The entrywise reduction of vectors over the group algebra. -/
noncomputable def redVec {q k : ℕ} [Fact q.Prime] (hk : 1 ≤ k) {ι : Type*}
    (x : ι → MonoidAlgebra (ZMod (q ^ k)) F) : ι → MonoidAlgebra (ZMod q) F :=
  fun i => redAlg (F := F) hk (x i)

/-- `1_H = Σ_{h ∈ H} h` inside `(ℤ/q^k)[F]`. -/
noncomputable def gsK {q k : ℕ} (H : Subgroup F) : MonoidAlgebra (ZMod (q ^ k)) F :=
  ∑ h : H, MonoidAlgebra.single (h : F) (1 : ZMod (q ^ k))

/-- `1_H = Σ_{h ∈ H} h` inside `𝔽_q[F]`. -/
noncomputable def gsB {q : ℕ} (H : Subgroup F) : MonoidAlgebra (ZMod q) F :=
  ∑ h : H, MonoidAlgebra.single (h : F) (1 : ZMod q)

lemma gsK_eq_map {q k : ℕ} (H : Subgroup F) :
    gsK (q := q) (k := k) H =
      MonoidAlgebra.mapRingHom F (Int.castRingHom (ZMod (q ^ k))) (Work.BSLit.groupSum H) := by
  rw [Work.BSLit.groupSum, gsK, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [MonoidAlgebra.mapRingHom_single, map_one]

lemma gsB_eq_map {q : ℕ} (H : Subgroup F) :
    gsB (q := q) H =
      MonoidAlgebra.mapRingHom F (Int.castRingHom (ZMod q)) (Work.BSLit.groupSum H) := by
  rw [Work.BSLit.groupSum, gsB, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [MonoidAlgebra.mapRingHom_single, map_one]

lemma redAlg_gsK {q k : ℕ} [Fact q.Prime] (hk : 1 ≤ k) (H : Subgroup F) :
    redAlg (F := F) hk (gsK (q := q) (k := k) H) = gsB (q := q) H := by
  rw [gsK, gsB, redAlg, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [MonoidAlgebra.mapRingHom_single, map_one]

lemma redAlg_algebraMap {q k : ℕ} [Fact q.Prime] (hk : 1 ≤ k) (r : ZMod (q ^ k)) :
    redAlg (F := F) hk (algebraMap (ZMod (q ^ k)) (MonoidAlgebra (ZMod (q ^ k)) F) r)
      = algebraMap (ZMod q) (MonoidAlgebra (ZMod q) F)
          (ZMod.castHom (dvd_pow_self q (Nat.pos_iff_ne_zero.mp hk)) (ZMod q) r) := by
  rw [redAlg]
  exact DFunLike.congr_fun (MonoidAlgebra.mapRingHom_comp_algebraMap (M := F)
    (ZMod.castHom (dvd_pow_self q (Nat.pos_iff_ne_zero.mp hk)) (ZMod q))) r

lemma redVec_smul {q k : ℕ} [Fact q.Prime] (hk : 1 ≤ k) {ι : Type*}
    (c : MonoidAlgebra (ZMod (q ^ k)) F) (x : ι → MonoidAlgebra (ZMod (q ^ k)) F) :
    redVec (F := F) hk (c • x) = redAlg (F := F) hk c • redVec (F := F) hk x := by
  funext i
  exact map_mul (redAlg (F := F) hk) c (x i)

/-! ## Rank reduction for the coefficientwise reduction

The range `N` of an idempotent `ZMod (q^k)`-linear endomorphism of `(ℤ/q^k)[F]^n` is a direct
summand of a free module, hence free; the coefficientwise reduction maps `N` onto the range of the
reduced endomorphism with kernel `q·N`, so comparing cardinalities gives the equality of the ranks.
-/

theorem finrank_range_reduce {q k : ℕ} [Fact q.Prime] (hk : 1 ≤ k) {ι : Type*} [Fintype ι]
    {P : (ι → MonoidAlgebra (ZMod (q ^ k)) F) →ₗ[ZMod (q ^ k)]
        (ι → MonoidAlgebra (ZMod (q ^ k)) F)} (hP : P * P = P)
    {Pbar : (ι → MonoidAlgebra (ZMod q) F) →ₗ[ZMod q] (ι → MonoidAlgebra (ZMod q) F)}
    (h : ∀ x : ι → MonoidAlgebra (ZMod (q ^ k)) F,
        redVec (F := F) hk (P x) = Pbar (redVec (F := F) hk x)) :
    Module.finrank (ZMod (q ^ k)) ↥(LinearMap.range P)
      = Module.finrank (ZMod q) ↥(LinearMap.range Pbar) := by
  classical
  have hq' : q.Prime := Fact.out
  have hdvd : q ∣ q ^ k := dvd_pow_self q (Nat.pos_iff_ne_zero.mp hk)
  set φ : ZMod (q ^ k) →+* ZMod q := ZMod.castHom hdvd (ZMod q) with hφdef
  haveI : RingHomSurjective φ := ⟨ZMod.castHom_surjective hdvd⟩
  have hred : ∀ c : MonoidAlgebra (ZMod (q ^ k)) F,
      redAlg (F := F) hk c = MonoidAlgebra.mapRingHom F φ c := fun c => rfl
  let ρ : (ι → MonoidAlgebra (ZMod (q ^ k)) F) →ₛₗ[φ] (ι → MonoidAlgebra (ZMod q) F) :=
    { toFun := fun x i => MonoidAlgebra.mapRingHom F φ (x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun r x => by
        funext i
        exact mapRingHom_smul φ r (x i) }
  have hρ_apply : ∀ (x : ι → MonoidAlgebra (ZMod (q ^ k)) F) (i : ι),
      ρ x i = MonoidAlgebra.mapRingHom F φ (x i) := fun x i => rfl
  have hρ_eq : ∀ x : ι → MonoidAlgebra (ZMod (q ^ k)) F, ρ x = redVec (F := F) hk x :=
    fun x => rfl
  have hφsurj : Function.Surjective (MonoidAlgebra.mapRingHom F φ) :=
    MonoidAlgebra.map_surjective (M := F) φ.toAddMonoidHom (ZMod.castHom_surjective hdvd)
  have hρsurj : Function.Surjective ρ := by
    intro y
    choose x hx using fun i => hφsurj (y i)
    exact ⟨x, funext fun i => by rw [hρ_apply]; exact hx i⟩
  -- the kernel of the coefficientwise reduction on a single coordinate
  have hdiv : ∀ a : ZMod (q ^ k), φ a = 0 → ∃ b : ZMod (q ^ k), a = (q : ZMod (q ^ k)) * b :=
    fun a ha => exists_eq_mul_of_castHom_eq_zero hdvd a ha
  have hqz : φ (q : ZMod (q ^ k)) = 0 := by
    rw [hφdef, ZMod.castHom_apply, ZMod.cast_natCast hdvd q, ZMod.natCast_self]
  have hscalar : ∀ x : MonoidAlgebra (ZMod (q ^ k)) F,
      ((q : ZMod (q ^ k)) • (1 : MonoidAlgebra (ZMod (q ^ k)) F →ₗ[ZMod (q ^ k)]
          MonoidAlgebra (ZMod (q ^ k)) F)) x = (q : ZMod (q ^ k)) • x := fun x => rfl
  have hker_single : ∀ c : MonoidAlgebra (ZMod (q ^ k)) F,
      MonoidAlgebra.mapRingHom F φ c = 0 ↔
        c ∈ LinearMap.range ((q : ZMod (q ^ k)) • (1 :
          MonoidAlgebra (ZMod (q ^ k)) F →ₗ[ZMod (q ^ k)] MonoidAlgebra (ZMod (q ^ k)) F)) := by
    intro c
    constructor
    · intro hc
      obtain ⟨z, hz⟩ :=
        exists_eq_algebraMap_mul_of_mapRingHom_eq_zero φ (q : ZMod (q ^ k)) hdiv c hc
      rw [LinearMap.mem_range]
      refine ⟨z, ?_⟩
      rw [hscalar, hz, Algebra.smul_def]
    · intro hc
      rw [LinearMap.mem_range] at hc
      obtain ⟨z, hz⟩ := hc
      rw [← hz, hscalar, mapRingHom_smul, hqz, zero_smul]
  -- the kernel of `ρ` is `q` times the ambient module
  have hkerρ : ρ.ker = LinearMap.range ((q : ZMod (q ^ k)) • (1 :
      (ι → MonoidAlgebra (ZMod (q ^ k)) F) →ₗ[ZMod (q ^ k)]
      (ι → MonoidAlgebra (ZMod (q ^ k)) F))) := by
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
  -- `ρ` maps `range P` onto `range Pbar`
  have hmap_le : ∀ x ∈ LinearMap.range P, ρ x ∈ LinearMap.range Pbar := by
    intro x hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨z, hz⟩ := hx
    rw [← hz, hρ_eq, h z]
    exact LinearMap.mem_range_self Pbar (redVec (F := F) hk z)
  let γ : (LinearMap.range P) →+ (LinearMap.range Pbar) :=
    { toFun := fun x => ⟨ρ ↑x, hmap_le ↑x x.2⟩
      map_zero' := by apply Subtype.ext; simpa using map_zero ρ
      map_add' := by intro x y; apply Subtype.ext; simpa using map_add ρ ↑x ↑y }
  have hγ_apply : ∀ x : LinearMap.range P,
      ((γ x : LinearMap.range Pbar) : ι → MonoidAlgebra (ZMod q) F) = ρ ↑x := fun x => rfl
  have hγsurj : Function.Surjective γ := by
    intro y
    have hy : (y : ι → MonoidAlgebra (ZMod q) F) ∈ LinearMap.range Pbar := y.2
    rw [LinearMap.mem_range] at hy
    obtain ⟨w, hw⟩ := hy
    obtain ⟨v, hv⟩ := hρsurj w
    refine ⟨⟨P v, LinearMap.mem_range_self P v⟩, ?_⟩
    apply Subtype.ext
    show ρ (P v) = (y : ι → MonoidAlgebra (ZMod q) F)
    rw [hρ_eq, h v, ← hρ_eq, hv, hw]
  -- the kernel of `γ` is `q · range P`, using the idempotence of `P`
  have hγker : γ.ker = (LinearMap.range ((q : ZMod (q ^ k)) • (1 :
      LinearMap.range P →ₗ[ZMod (q ^ k)] LinearMap.range P))).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup]
    constructor
    · intro hx
      have hx' : (x : ι → MonoidAlgebra (ZMod (q ^ k)) F) ∈ ρ.ker := by
        rw [LinearMap.mem_ker]
        simpa [hγ_apply] using congrArg Subtype.val hx
      rw [hkerρ] at hx'
      exact (range_inf_smul_one (q : ZMod (q ^ k)) P hP x).1 hx'
    · intro hx
      have hx' : (x : ι → MonoidAlgebra (ZMod (q ^ k)) F) ∈ ρ.ker := by
        rw [hkerρ]
        exact (range_inf_smul_one (q : ZMod (q ^ k)) P hP x).2 hx
      rw [LinearMap.mem_ker] at hx'
      apply Subtype.ext
      simpa [hγ_apply] using hx'
  -- first isomorphism theorem: `range Pbar` has the same cardinality as `range P / q·range P`
  have hcard : Nat.card ↥(LinearMap.range Pbar)
      = Nat.card (↥(LinearMap.range P) ⧸ LinearMap.range ((q : ZMod (q ^ k)) • (1 :
          LinearMap.range P →ₗ[ZMod (q ^ k)] LinearMap.range P))) := by
    have hcc := Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective γ hγsurj).toEquiv
    rw [hγker] at hcc
    exact hcc.symm
  -- `range P` is free and finite over `ZMod (q^k)`
  haveI hfree : Module.Free (ZMod (q ^ k)) ↥(LinearMap.range P) := (FreeRangeIdempotent hk P hP).1
  haveI hfin : Module.Finite (ZMod (q ^ k)) ↥(LinearMap.range P) := (FreeRangeIdempotent hk P hP).2
  haveI : Fact (1 < q ^ k) := ⟨Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hk) hq'.one_lt⟩
  haveI : Nontrivial (ZMod (q ^ k)) := ZMod.nontrivial (q ^ k)
  haveI : StrongRankCondition (ZMod (q ^ k)) := inferInstance
  haveI hsfin : Module.Finite (ZMod q) ↥(LinearMap.range Pbar) :=
    FiniteDimensional.finiteDimensional_submodule (LinearMap.range Pbar)
  haveI : StrongRankCondition (ZMod q) := inferInstance
  have h1 : Nat.card ↥(LinearMap.range P)
      = (q ^ k) ^ Module.finrank (ZMod (q ^ k)) ↥(LinearMap.range P) := by
    rw [natCard_eq_card_pow_finrank (R := ZMod (q ^ k)) (M := ↥(LinearMap.range P)), Nat.card_zmod]
  have h2 : Nat.card ↥(LinearMap.range Pbar)
      = q ^ Module.finrank (ZMod q) ↥(LinearMap.range Pbar) := by
    rw [natCard_eq_card_pow_finrank (R := ZMod q) (M := ↥(LinearMap.range Pbar)), Nat.card_zmod]
  have h3 : Nat.card ↥(LinearMap.range P) =
      (Nat.card (↥(LinearMap.range P) ⧸ LinearMap.range ((q : ZMod (q ^ k)) • (1 :
          LinearMap.range P →ₗ[ZMod (q ^ k)] LinearMap.range P))))^k :=
    NatCardQuotPowB hk
  have hkey : (q ^ k) ^ Module.finrank (ZMod (q ^ k)) ↥(LinearMap.range P)
      = (q ^ k) ^ Module.finrank (ZMod q) ↥(LinearMap.range Pbar) := by
    rw [← h1, h3, ← hcard, h2, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hq2 : 2 ≤ q ^ k := by
    have := Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hk) hq'.one_lt
    omega
  exact Nat.pow_right_injective hq2 hkey

/-! ## The dimension of the averaged projectors

`𝔽_q[F]^n` carries the left regular action of `F`; the averaging element `|H|⁻¹ · 1_H` acts by
left multiplication, and the range of that endomorphism on the range of `e` is the fixed space of
`H`, which is isomorphic to `V^H` through the given identification `range e ≃ₗ ρ.asModule`.
-/

theorem finrank_range_averaging_projector {q : ℕ} [Fact q.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod q) V] [FiniteDimensional (ZMod q) V]
    (ρ : Representation (ZMod q) F V) (hq : ¬ q ∣ Nat.card F) {n : ℕ}
    (e : (Fin n → MonoidAlgebra (ZMod q) F) →ₗ[MonoidAlgebra (ZMod q) F]
        (Fin n → MonoidAlgebra (ZMod q) F)) (he : e * e = e)
    (ψ : ↥(LinearMap.range e) ≃ₗ[MonoidAlgebra (ZMod q) F] ρ.asModule) (H : Subgroup F) :
    Module.finrank (ZMod q) (LinearMap.range
      (((Algebra.lsmul (ZMod q) (ZMod q) (Fin n → MonoidAlgebra (ZMod q) F))
          ((algebraMap (ZMod q) (MonoidAlgebra (ZMod q) F) ((Nat.card H : ZMod q))⁻¹) *
            (MonoidAlgebra.mapRingHom F (Int.castRingHom (ZMod q)) (Work.BSLit.groupSum H))))
        ∘ₗ (LinearMap.restrictScalars (ZMod q) e))) =
      Module.finrank (ZMod q) ↥(Representation.invariants (ρ.comp H.subtype)) := by
  classical
  set a : MonoidAlgebra (ZMod q) F :=
    algebraMap (ZMod q) (MonoidAlgebra (ZMod q) F) ((Nat.card H : ZMod q))⁻¹ *
      MonoidAlgebra.mapRingHom F (Int.castRingHom (ZMod q)) (Work.BSLit.groupSum H) with ha
  set A : V →ₗ[ZMod q] V := ρ.asAlgebraHom a with hA
  let φ : ↥(LinearMap.range e) ≃ₗ[ZMod q] V :=
    (LinearEquiv.restrictScalars (ZMod q) ψ) ≪≫ₗ ρ.asModuleEquiv
  have hφ : ∀ x : ↥(LinearMap.range e), φ (a • x) = A (φ x) := by
    intro x
    show ρ.asModuleEquiv (ψ (a • x)) = ρ.asAlgebraHom a (ρ.asModuleEquiv (ψ x))
    have h1 : ψ (a • x) = a • ψ x := LinearMap.map_smul _ a x
    rw [h1, Representation.asModuleEquiv_map_smul]
  have hfin := RankRangeLsmulComp (k := ZMod q) (R := MonoidAlgebra (ZMod q) F)
    (P := Fin n → MonoidAlgebra (ZMod q) F) (N := V) a e A φ hφ
  have hrangeA : LinearMap.range A = Representation.invariants (ρ.comp H.subtype) := by
    rw [hA]
    exact RangeAveragingEqInvariants ρ hq H
  rw [hfin, hrangeA]

/-! ## The lifted trace functional -/

/-- **Existence of the lifted trace functional.**  For every `k ≥ 1` there is an additive map
`τ : ℤ[F] → ℤ/q^k` with `τ (1_H) = |H| · dim_{𝔽_q} V^H` for every subgroup `H ≤ F`.

It is the trace, on the lifted module `W = range Ẽ`, of the "sum over `H`": the assertion
`τ (1_H) = |H| · dim V^H` is the idempotent computation
`tr (Σ_{h ∈ H} rt h) = |H| · finrank_{ℤ/q^k} (range (E_H ∘ Ẽ))` combined with
`finrank_{ℤ/q^k} (range (E_H ∘ Ẽ)) = dim_{𝔽_q} V^H` (rank reduction + invariants computation). -/
theorem exists_lifted_trace_functional {q : ℕ} [Fact q.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod q) V] [FiniteDimensional (ZMod q) V]
    (ρ : Representation (ZMod q) F V) (hq : ¬ q ∣ Nat.card F) (k : ℕ) (hk : 1 ≤ k) :
    ∃ τ : MonoidAlgebra ℤ F →+ ZMod (q ^ k),
      ∀ H : Subgroup F, τ (Work.BSLit.groupSum H) =
        ((Nat.card H * Module.finrank (ZMod q)
          ↥(Representation.invariants (ρ.comp H.subtype)) : ℕ) : ZMod (q ^ k)) := by
  classical
  have hq' : q.Prime := Fact.out
  -- (0) a projector onto `V` over `𝔽_q[F]`, and an idempotent lift of it to `(ℤ/q^k)[F]`
  obtain ⟨n, e, he, ⟨ψ⟩⟩ := ExistsProjector ρ hq
  obtain ⟨Et, hEt_idem, hEt_red⟩ := exists_lift_endomorphism (F := F) hk e he
  -- (1) `Et` viewed as a `ZMod (q^k)`-linear endomorphism
  let EtR : (Fin n → MonoidAlgebra (ZMod (q ^ k)) F) →ₗ[ZMod (q ^ k)]
      (Fin n → MonoidAlgebra (ZMod (q ^ k)) F) := Et.restrictScalars (ZMod (q ^ k))
  have hEtR_apply : ∀ x, EtR x = Et x := fun x => rfl
  have hEt_apply : ∀ x, Et (Et x) = Et x := by
    intro x
    have h := congrArg (fun f : (Fin n → MonoidAlgebra (ZMod (q ^ k)) F) →ₗ[MonoidAlgebra (ZMod (q ^ k)) F]
        (Fin n → MonoidAlgebra (ZMod (q ^ k)) F) => f x) hEt_idem
    simpa [Module.End.mul_eq_comp] using h
  have hEtR_idem : EtR * EtR = EtR := by
    rw [Module.End.mul_eq_comp]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hEtR_apply, hEtR_apply]
    exact hEt_apply x
  have hEt_red' : ∀ x : Fin n → MonoidAlgebra (ZMod (q ^ k)) F,
      redVec (F := F) hk (Et x) = e (redVec (F := F) hk x) := fun x => hEt_red x
  -- (2) the additive functional `y ↦ tr ((left multiplication by y) ∘ EtR)`
  set lmul : MonoidAlgebra (ZMod (q ^ k)) F →ₗ[ZMod (q ^ k)]
      ((Fin n → MonoidAlgebra (ZMod (q ^ k)) F) →ₗ[ZMod (q ^ k)]
        (Fin n → MonoidAlgebra (ZMod (q ^ k)) F)) :=
    (Algebra.lsmul (ZMod (q ^ k)) (ZMod (q ^ k)) (Fin n → MonoidAlgebra (ZMod (q ^ k)) F)).toLinearMap
    with hlmul
  have hlmul_apply : ∀ (y : MonoidAlgebra (ZMod (q ^ k)) F)
      (x : Fin n → MonoidAlgebra (ZMod (q ^ k)) F), lmul y x = y • x := by
    intro y x
    rw [hlmul]
    exact Algebra.lsmul_apply (R := ZMod (q ^ k)) (B := ZMod (q ^ k))
      (M := Fin n → MonoidAlgebra (ZMod (q ^ k)) F) y x
  have htr_add : ∀ y z : MonoidAlgebra (ZMod (q ^ k)) F,
      LinearMap.trace (ZMod (q ^ k)) (Fin n → MonoidAlgebra (ZMod (q ^ k)) F) (lmul (y + z) ∘ₗ EtR)
        = LinearMap.trace (ZMod (q ^ k)) (Fin n → MonoidAlgebra (ZMod (q ^ k)) F) (lmul y ∘ₗ EtR)
          + LinearMap.trace (ZMod (q ^ k)) (Fin n → MonoidAlgebra (ZMod (q ^ k)) F)
              (lmul z ∘ₗ EtR) := by
    intro y z
    rw [map_add, LinearMap.add_comp, map_add]
  let Φ : MonoidAlgebra (ZMod (q ^ k)) F →+ ZMod (q ^ k) :=
    AddMonoidHom.mk' (fun y => LinearMap.trace (ZMod (q ^ k))
      (Fin n → MonoidAlgebra (ZMod (q ^ k)) F) (lmul y ∘ₗ EtR)) htr_add
  have hΦ : ∀ y, Φ y = LinearMap.trace (ZMod (q ^ k))
      (Fin n → MonoidAlgebra (ZMod (q ^ k)) F) (lmul y ∘ₗ EtR) := fun y => rfl
  -- (3) the trace of `Σ_{h ∈ H}` is `|H| · dim V^H`
  have key : ∀ H : Subgroup F,
      LinearMap.trace (ZMod (q ^ k)) (Fin n → MonoidAlgebra (ZMod (q ^ k)) F)
        (lmul (gsK (q := q) (k := k) H) ∘ₗ EtR)
      = ((Nat.card H * Module.finrank (ZMod q)
          ↥(Representation.invariants (ρ.comp H.subtype)) : ℕ) : ZMod (q ^ k)) := by
    intro H
    -- `|H|` is invertible modulo `q^k`
    have hHdvd : ¬ q ∣ Nat.card H := fun hd => hq (hd.trans (Subgroup.card_subgroup_dvd_card H))
    have hunit : IsUnit ((Nat.card H : ℕ) : ZMod (q ^ k)) :=
      (ZMod.isUnit_natCast_iff_not_dvd_pow hq' (by omega)).mpr hHdvd
    let u : (ZMod (q ^ k))ˣ := hunit.unit
    have hu : (u : ZMod (q ^ k)) = ((Nat.card H : ℕ) : ZMod (q ^ k)) := hunit.unit_spec
    -- the averaging idempotent `t_H = |H|⁻¹ · 1_H`
    set tH : MonoidAlgebra (ZMod (q ^ k)) F :=
      algebraMap (ZMod (q ^ k)) (MonoidAlgebra (ZMod (q ^ k)) F) (↑u⁻¹) *
        gsK (q := q) (k := k) H with htH
    have hgH2 : gsK (q := q) (k := k) H * gsK (q := q) (k := k) H
        = (Nat.card H : MonoidAlgebra (ZMod (q ^ k)) F) * gsK (q := q) (k := k) H := by
      have h := congrArg (MonoidAlgebra.mapRingHom F (Int.castRingHom (ZMod (q ^ k))))
          (groupSum_mul_self (F := F) H)
      simp only [map_mul, map_natCast] at h
      rw [← gsK_eq_map (q := q) (k := k) H] at h
      exact h
    have hcast : (Nat.card H : MonoidAlgebra (ZMod (q ^ k)) F)
        = algebraMap (ZMod (q ^ k)) (MonoidAlgebra (ZMod (q ^ k)) F) (u : ZMod (q ^ k)) :=
      (map_natCast (algebraMap (ZMod (q ^ k)) (MonoidAlgebra (ZMod (q ^ k)) F))
        (Nat.card H)).symm.trans (by rw [← hu])
    -- `(|H|⁻¹ · 1_H)² = |H|⁻¹ · 1_H`
    have hsq_avg : (algebraMap (ZMod (q ^ k)) (MonoidAlgebra (ZMod (q ^ k)) F) (↑u⁻¹))^2 *
          (Nat.card H : MonoidAlgebra (ZMod (q ^ k)) F)
        = algebraMap (ZMod (q ^ k)) (MonoidAlgebra (ZMod (q ^ k)) F) (↑u⁻¹) := by
      rw [sq, hcast, ← map_mul, ← map_mul]
      congr 1
      rw [mul_assoc, Units.inv_mul, mul_one]
    have hsq_gs : (gsK (q := q) (k := k) H)^2
        = (Nat.card H : MonoidAlgebra (ZMod (q ^ k)) F) * gsK (q := q) (k := k) H := by
      rw [sq, hgH2]
    have htH_idem : tH * tH = tH := by
      calc tH * tH
          = (algebraMap (ZMod (q ^ k)) (MonoidAlgebra (ZMod (q ^ k)) F) (↑u⁻¹) *
              gsK (q := q) (k := k) H)^2 := by rw [htH, sq]
        _ = (algebraMap (ZMod (q ^ k)) (MonoidAlgebra (ZMod (q ^ k)) F) (↑u⁻¹))^2 *
              (gsK (q := q) (k := k) H)^2 :=
            Commute.mul_pow (Algebra.commutes (↑u⁻¹ : ZMod (q ^ k)) (gsK (q := q) (k := k) H)) 2
        _ = (algebraMap (ZMod (q ^ k)) (MonoidAlgebra (ZMod (q ^ k)) F) (↑u⁻¹))^2 *
              ((Nat.card H : MonoidAlgebra (ZMod (q ^ k)) F) * gsK (q := q) (k := k) H) := by
            rw [hsq_gs]
        _ = ((algebraMap (ZMod (q ^ k)) (MonoidAlgebra (ZMod (q ^ k)) F) (↑u⁻¹))^2 *
              (Nat.card H : MonoidAlgebra (ZMod (q ^ k)) F)) * gsK (q := q) (k := k) H := by
            rw [← mul_assoc]
        _ = algebraMap (ZMod (q ^ k)) (MonoidAlgebra (ZMod (q ^ k)) F) (↑u⁻¹) *
              gsK (q := q) (k := k) H := by rw [hsq_avg]
        _ = tH := htH.symm
    -- `1_H = |H| • t_H`
    have hgs_eq : gsK (q := q) (k := k) H = ((Nat.card H : ℕ) : ZMod (q ^ k)) • tH := by
      rw [htH, Algebra.smul_def, ← hu, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
    -- the same averaging element modulo `q`
    set tHbar : MonoidAlgebra (ZMod q) F :=
      algebraMap (ZMod q) (MonoidAlgebra (ZMod q) F) ((Nat.card H : ZMod q))⁻¹ *
        MonoidAlgebra.mapRingHom F (Int.castRingHom (ZMod q)) (Work.BSLit.groupSum H) with htHbar
    have hred_tH : redAlg (F := F) hk tH = tHbar := by
      have hcu : (ZMod.castHom (dvd_pow_self q (Nat.pos_iff_ne_zero.mp hk)) (ZMod q))
          (u : ZMod (q ^ k)) = ((Nat.card H : ℕ) : ZMod q) := by
        rw [hu, ZMod.castHom_apply,
          ZMod.cast_natCast (dvd_pow_self q (Nat.pos_iff_ne_zero.mp hk))]
      have hinv : (ZMod.castHom (dvd_pow_self q (Nat.pos_iff_ne_zero.mp hk)) (ZMod q))
          (↑u⁻¹ : ZMod (q ^ k)) = ((Nat.card H : ℕ) : ZMod q)⁻¹ := by
        refine (inv_eq_of_mul_eq_one_right ?_).symm
        rw [← hcu, ← map_mul, Units.mul_inv, map_one]
      rw [htH, htHbar, map_mul, redAlg_gsK hk H, redAlg_algebraMap, hinv, gsB_eq_map]
    -- the two endomorphisms whose idempotent ranges compute the invariants
    set Psi : (Fin n → MonoidAlgebra (ZMod (q ^ k)) F) →ₗ[ZMod (q ^ k)]
        (Fin n → MonoidAlgebra (ZMod (q ^ k)) F) :=
      (Algebra.lsmul (ZMod (q ^ k)) (ZMod (q ^ k)) (Fin n → MonoidAlgebra (ZMod (q ^ k)) F)) tH
        ∘ₗ EtR with hPsi
    set PsiBar : (Fin n → MonoidAlgebra (ZMod q) F) →ₗ[ZMod q]
        (Fin n → MonoidAlgebra (ZMod q) F) :=
      (Algebra.lsmul (ZMod q) (ZMod q) (Fin n → MonoidAlgebra (ZMod q) F)) tHbar
        ∘ₗ (LinearMap.restrictScalars (ZMod q) e) with hPsiBar
    have hPsi_apply : ∀ x, Psi x = tH • (EtR x) := by
      intro x
      rw [hPsi, LinearMap.comp_apply]
      exact Algebra.lsmul_apply (R := ZMod (q ^ k)) (B := ZMod (q ^ k))
        (M := Fin n → MonoidAlgebra (ZMod (q ^ k)) F) tH (EtR x)
    have hPsiBar_apply : ∀ x, PsiBar x = tHbar • (e.restrictScalars (ZMod q) x) := by
      intro x
      rw [hPsiBar, LinearMap.comp_apply]
      exact Algebra.lsmul_apply (R := ZMod q) (B := ZMod q)
        (M := Fin n → MonoidAlgebra (ZMod q) F) tHbar (e.restrictScalars (ZMod q) x)
    have hPsi_idem : Psi * Psi = Psi := by
      rw [Module.End.mul_eq_comp]
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, hPsi_apply, hEtR_apply, LinearMap.map_smul, hEt_apply,
        smul_smul, htH_idem]
    have hcomm : ∀ x : Fin n → MonoidAlgebra (ZMod (q ^ k)) F,
        redVec (F := F) hk (Psi x) = PsiBar (redVec (F := F) hk x) := by
      intro x
      rw [hPsi_apply, redVec_smul, hEtR_apply, hEt_red' x, hred_tH, hPsiBar_apply,
        LinearMap.restrictScalars_apply]
    -- the rank of the idempotent range is `dim V^H`
    have hrank : Module.finrank (ZMod (q ^ k)) ↥(LinearMap.range Psi)
        = Module.finrank (ZMod q) ↥(Representation.invariants (ρ.comp H.subtype)) := by
      rw [finrank_range_reduce hk hPsi_idem hcomm]
      exact finrank_range_averaging_projector ρ hq e he ψ H
    -- the trace of the averaging projector is that rank
    have hPsi_trace : LinearMap.trace (ZMod (q ^ k)) (Fin n → MonoidAlgebra (ZMod (q ^ k)) F)
        Psi = (Module.finrank (ZMod (q ^ k)) ↥(LinearMap.range Psi) : ZMod (q ^ k)) := by
      haveI hf : Module.Free (ZMod (q ^ k)) ↥(LinearMap.range Psi) :=
        (FreeRangeIdempotent hk Psi hPsi_idem).1
      haveI hn : Module.Finite (ZMod (q ^ k)) ↥(LinearMap.range Psi) :=
        (FreeRangeIdempotent hk Psi hPsi_idem).2
      exact TraceIdempotentRange Psi hPsi_idem
    -- assemble
    have hPsi_eq : lmul tH ∘ₗ EtR = Psi := rfl
    have hlmul_smul : ∀ (c : ZMod (q ^ k)) (y : MonoidAlgebra (ZMod (q ^ k)) F),
        lmul (c • y) = c • lmul y := fun c y => map_smul lmul c y
    rw [hgs_eq, hlmul_smul, LinearMap.smul_comp, map_smul, hPsi_eq, hPsi_trace, hrank,
      smul_eq_mul, ← Nat.cast_mul]
  -- (4) package the functional
  refine ⟨Φ.comp (MonoidAlgebra.mapRingHom F (Int.castRingHom (ZMod (q ^ k)))).toAddMonoidHom, ?_⟩
  intro H
  change Φ ((MonoidAlgebra.mapRingHom F (Int.castRingHom (ZMod (q ^ k))))
      (Work.BSLit.groupSum H)) =
    ((Nat.card H * Module.finrank (ZMod q)
      ↥(Representation.invariants (ρ.comp H.subtype)) : ℕ) : ZMod (q ^ k))
  rw [hΦ, ← gsK_eq_map (q := q) (k := k) H]
  exact key H

/-- **The linear form of Wielandt's counting lemma (Huppert–Blackburn XI 12.4), `ι`-indexed.**

Let `F` be a finite group, `q` a prime with `q ∤ |F|`, and `ρ` a finite-dimensional
`𝔽_q`-representation of `F`. If `∑ i, n i • 1_{H i} = 0` in `ℤ[F]` (with
`1_H = Work.BSLit.groupSum H = ∑_{h ∈ H} h`), then
`∑ i, n i * |H i| * dim_{𝔽_q} V^{H i} = 0`, where
`V^{H} = Representation.invariants (ρ.comp H.subtype)`.

Route: lift `ρ` to `ℤ/q^k` for all `k ≥ 1` (idempotent lifting of a projector onto `V`, averaging
projectors for `H ≤ F`, which exist since `q ∤ |H|`) and take traces, giving `q^k` divisibility of
the displayed integer for every `k`; hence it is `0`.  Sorry-free ingredients for the lift are
available in the workspace: `Work.BSLit.Wielandt.ExistsProjector` (`Range e ≃ₗ ρ.asModule` for an
idempotent `e`), `Work.BSLit.Wielandt.LiftIdempotentMatrix`, `Work.BSLit.Wielandt.ExistsProjector`,
`Work.BSLit.Wielandt.TraceIdempotentRange`, `Work.BSLit.Wielandt.FreeRangeIdempotent`,
`Work.BSLit.Wielandt.NatCardQuotPowB`, `Work.BSLit.Wielandt.InfRangeSmulOne`,
`Work.BSLit.Wielandt.ForallMapRingHomEqZero`, `Work.BSLit.Wielandt.groupSum_mul_self`.
Do NOT import any module containing a `sorry` (in particular not
`Submission.Work.BSLit.Wielandt.ModLiftTrace`, `LiftedTraceFunctional`, `LiftTraceFunctional` nor
`Submission.Work.BSLit.Wielandt.ProductFormula`): the finished proof must be `sorry`-free. -/
theorem linearFormCountingFormula {F : Type*} [Group F] [Fintype F] {q : ℕ} [Fact q.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V]
    (ρ : Representation (ZMod q) F V) (hq : ¬ q ∣ Nat.card F)
    {ι : Type*} [Fintype ι] (H : ι → Subgroup F) (n : ι → ℤ)
    (hrel : ∑ i, n i • Work.BSLit.groupSum (H i) = 0) :
    ∑ i, n i * (Nat.card (H i) : ℤ) *
      (Module.finrank (ZMod q) ↥(Representation.invariants (ρ.comp (H i).subtype)) : ℤ) = 0 := by
  classical
  -- For every `k ≥ 1`, `q^k` divides the displayed integer.
  have hmain : ∀ k : ℕ, 1 ≤ k →
      ((∑ i, n i * (Nat.card (H i) : ℤ) *
        (Module.finrank (ZMod q) ↥(Representation.invariants (ρ.comp (H i).subtype)) : ℤ) : ℤ)
          : ZMod (q ^ k)) = 0 := by
    intro k hk
    obtain ⟨τ, hτ⟩ := exists_lifted_trace_functional ρ hq k hk
    -- evaluate the relation `Σ i, n i • 1_{H i} = 0` in `ℤ/q^k` through `τ`
    have h0 : (∑ i, n i • ((Nat.card (H i) * Module.finrank (ZMod q)
        ↥(Representation.invariants (ρ.comp (H i).subtype)) : ℕ) : ZMod (q ^ k))) = 0 := by
      have h1 : τ (∑ i, n i • Work.BSLit.groupSum (H i)) = 0 := by rw [hrel, map_zero]
      rw [map_sum] at h1
      simpa only [map_zsmul, hτ] using h1
    rw [← h0]
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zsmul_eq_mul, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Nat.cast_mul]
    ring
  exact intCastZmodEqZero (q := q)
    (∑ i, n i * (Nat.card (H i) : ℤ) *
      (Module.finrank (ZMod q) ↥(Representation.invariants (ρ.comp (H i).subtype)) : ℤ)) hmain

end Work.BSLit.Wielandt
