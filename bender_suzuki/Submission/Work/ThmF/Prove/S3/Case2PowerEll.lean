import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.Prove.S3.ConjRep
import Submission.Work.ThmF.Prove.S3.card_dvd_card_of_free_action
import Submission.Work.S3.exists_eq_of_mem_zpowers_of_prime_card
import Submission.Work.S3.powMulAut_of_not_dvd
import Submission.Work.S3.exists_conjMulAutHom
import Submission.Work.ThmF.Prove.S3.ConjEqPowPrimeOfSimple

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.ThmF.Prove.S3

open Work.S3

open scoped IsMulCommutative

/-- The complement of a point in a finite type has one element fewer. -/
private theorem card_compl_singleton {X : Type} [Finite X] (x0 : X) :
    Nat.card {x : X // x ≠ x0} = Nat.card X - 1 := by
  have : Fintype X := Fintype.ofFinite X
  have : Fintype {x : X // x ≠ x0} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := X),
    Fintype.card_subtype_compl (fun x : X => x = x0), Fintype.card_subtype_eq x0]

/-- The conjugation action of a subgroup `K ≤ N_G(M)` on the set `M^# = M \ {1}` of non-identity
elements of `M` (written as a subtype of `↥M`). -/
instance msharpConjMulAction {G : Type} [Group G] {M K : Subgroup G}
    [hKN : Fact (K ≤ Subgroup.normalizer (M : Set G))] : MulAction ↥K {m : ↥M // m ≠ 1} where
  smul k y := ⟨⟨(k : G) * ((y.1 : ↥M) : G) * (k : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hKN.out k.2) ((y.1 : ↥M) : G)).mp y.1.2⟩,
    fun h => y.2 (Subtype.ext (by
      have h1 : (k : G) * ((y.1 : ↥M) : G) * (k : G)⁻¹ = 1 := by
        have h2 := congrArg (fun z : ↥M => (z : G)) h
        simpa using h2
      calc ((y.1 : ↥M) : G)
          = (k : G)⁻¹ * ((k : G) * ((y.1 : ↥M) : G) * (k : G)⁻¹) * (k : G) := by group
        _ = (k : G)⁻¹ * 1 * (k : G) := by rw [h1]
        _ = 1 := by group))⟩
  one_smul y := by
    apply Subtype.ext; apply Subtype.ext
    show (1 : G) * ((y.1 : ↥M) : G) * (1 : G)⁻¹ = ((y.1 : ↥M) : G)
    group
  mul_smul a b y := by
    apply Subtype.ext; apply Subtype.ext
    show ((a : G) * (b : G)) * ((y.1 : ↥M) : G) * ((a : G) * (b : G))⁻¹
      = (a : G) * ((b : G) * ((y.1 : ↥M) : G) * (b : G)⁻¹) * (a : G)⁻¹
    group

/-- Value of the conjugation action `msharpConjMulAction` on an element. -/
@[simp] theorem msharpConjMulAction_smul_val {G : Type} [Group G] {M K : Subgroup G}
    [hKN : Fact (K ≤ Subgroup.normalizer (M : Set G))] (k : ↥K) (y : {m : ↥M // m ≠ 1}) :
    (((k • y : {m : ↥M // m ≠ 1}).1 : ↥M) : G) = (k : G) * ((y.1 : ↥M) : G) * (k : G)⁻¹ :=
  rfl

/-- **Translation lemma.**  `M ≤ G` is abelian of exponent dividing the prime `ℓ` and is
normalised by `L ≤ G`; `K ≤ L` is a subgroup such that no non-trivial `K`-invariant subgroup of
`M` is proper.  Then `↥M`, with the conjugation action of `K` (viewed inside `G` through
`L ≤ G`), is a simple module over the group algebra `𝔽_ℓ[K]`.

The conjugation module structure is the one coming from
`Work.ThmF.Prove.S3.conjRepOfLe`; the argument is the standard dictionary between
`K`-invariant subgroups of `M` and `𝔽_ℓ[K]`-submodules of `↥M` (via
`Subrepresentation.apply_mem_toSubmodule`). -/
theorem isSimpleModule_conjRep_of_simple
    {G : Type} [Group G] {M : Subgroup G} [IsMulCommutative ↥M] (hMne : M ≠ ⊥) {ℓ : ℕ}
    [Fact ℓ.Prime] [Fact (∀ x : ↥M, x ^ ℓ = 1)]
    {L : Subgroup G} (hLN : L ≤ Subgroup.normalizer (M : Set G))
    {K : Subgroup L}
    (hsimple : ∀ N : Subgroup G, N ≤ M → N ≠ ⊥ →
      (∀ x : ↥K, ∀ n ∈ N, ((x : L) : G) * n * (((x : L) : G))⁻¹ ∈ N) → N = M) :
    IsSimpleModule (MonoidAlgebra (ZMod ℓ) ↥K)
      (Representation.asModule ((Work.ThmF.Prove.S3.conjRepOfLe (n := ℓ) L M hLN).comp K.subtype)) := by
  classical
  obtain ⟨m0, hm0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hMne
  haveI hMnt : Nontrivial ↥M := ⟨m0, 1, hm0⟩
  haveI hMnA : Nontrivial (Additive ↥M) :=
    ⟨Additive.ofMul m0, 0, fun h => hm0 (by simpa using congrArg Additive.toMul h)⟩
  haveI hntSub : Nontrivial (Subrepresentation
      ((Work.ThmF.Prove.S3.conjRepOfLe (n := ℓ) L M hLN).comp K.subtype)) :=
    ⟨⊥, ⊤, fun h => by
      have h2 : (⊥ : Submodule (ZMod ℓ) (Additive ↥M)) = ⊤ :=
        congrArg (fun σ : Subrepresentation
          ((Work.ThmF.Prove.S3.conjRepOfLe (n := ℓ) L M hLN).comp K.subtype) => σ.toSubmodule) h
      have h3 : Additive.ofMul m0 ∈ (⊥ : Submodule (ZMod ℓ) (Additive ↥M)) := by
        rw [h2]; trivial
      rw [Submodule.mem_bot] at h3
      exact hm0 (by simpa using congrArg Additive.toMul h3)⟩
  have hmain : IsSimpleOrder (Subrepresentation
      ((Work.ThmF.Prove.S3.conjRepOfLe (n := ℓ) L M hLN).comp K.subtype)) :=
    ⟨fun σ => by
      by_cases hσ : σ = ⊥
      · exact Or.inl hσ
      · refine Or.inr ?_
        let N : Subgroup G := (σ.toSubmodule.toAddSubgroup.toSubgroup').map M.subtype
        have hNmem : ∀ x : G, x ∈ N ↔
            ∃ m : ↥M, (m : G) = x ∧ Additive.ofMul m ∈ σ.toSubmodule := by
          intro x
          show x ∈ Subgroup.map M.subtype (AddSubgroup.toSubgroup' σ.toSubmodule.toAddSubgroup) ↔ _
          rw [Subgroup.mem_map]
          constructor
          · rintro ⟨m, hm, hEq⟩
            exact ⟨m, hEq, (AddSubgroup.mem_toSubgroup' _ _).mp hm⟩
          · rintro ⟨m, hEq, hm⟩
            exact ⟨m, (AddSubgroup.mem_toSubgroup' _ _).mpr hm, hEq⟩
        have hNle : N ≤ M := Subgroup.map_subtype_le _
        have hNinv : ∀ x : ↥K, ∀ n ∈ N, ((x : L) : G) * n * (((x : L) : G))⁻¹ ∈ N := by
          intro x n hn
          obtain ⟨m, hEq, hm⟩ := (hNmem n).mp hn
          subst hEq
          have hxN : ∀ y : G, y ∈ M ↔ ((x : ↥L) : G) * y * (((x : ↥L) : G))⁻¹ ∈ M :=
            Subgroup.mem_normalizer_iff.mp (hLN (x : ↥L).2)
          have hmem : ((x : ↥L) : G) * (m : G) * (((x : ↥L) : G))⁻¹ ∈ M := (hxN (m : G)).mp m.2
          refine (hNmem _).mpr ⟨⟨((x : ↥L) : G) * (m : G) * (((x : ↥L) : G))⁻¹, hmem⟩, rfl, ?_⟩
          exact σ.apply_mem_toSubmodule x hm
        have hNne : N ≠ ⊥ := by
          intro hbot
          refine hσ ?_
          apply Subrepresentation.toSubmodule_injective
          change σ.toSubmodule = (⊥ : Submodule (ZMod ℓ) (Additive ↥M))
          rw [Submodule.eq_bot_iff]
          intro v hv
          rw [← ofMul_toMul v] at hv ⊢
          have hmN : ((Additive.toMul v : ↥M) : G) ∈ N :=
            (hNmem _).mpr ⟨Additive.toMul v, rfl, hv⟩
          have hmem' : ((Additive.toMul v : ↥M) : G) ∈ (⊥ : Subgroup G) := by
            rw [← hbot]; exact hmN
          have h1 : Additive.toMul v = 1 :=
            Subtype.ext (by simpa using Subgroup.mem_bot.mp hmem')
          rw [h1]
          rfl
        have hNM : N = M := hsimple N hNle hNne hNinv
        apply Subrepresentation.toSubmodule_injective
        change σ.toSubmodule = (⊤ : Submodule (ZMod ℓ) (Additive ↥M))
        rw [Submodule.eq_top_iff']
        intro v
        rw [← ofMul_toMul v]
        have hmM : ((Additive.toMul v : ↥M) : G) ∈ N := by
          rw [hNM]; exact (Additive.toMul v).2
        obtain ⟨m', hEq, hm'⟩ := (hNmem _).mp hmM
        have hmm : m' = Additive.toMul v := Subtype.ext hEq
        rw [hmm] at hm'
        exact hm'⟩
  have hirr : Representation.IsIrreducible
      ((Work.ThmF.Prove.S3.conjRepOfLe (n := ℓ) L M hLN).comp K.subtype) := hmain
  exact (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr

theorem case2PowerEll {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : Work.ThmF.ChV3.CtxF H Q t s r P) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t))
    (hKlcop : ¬ ℓ ∣ Nat.card ↥(Work.ThmF.Ksub H t))
    (hKP : P ⊓ Work.ThmF.Ksub H t = ⊥)
    (hKinv : ∀ p ∈ P, ∀ k ∈ Work.ThmF.Ksub H t, p * k * p⁻¹ ∈ Work.ThmF.Ksub H t)
    (hPcent : ∀ a ∈ P, (∀ k ∈ Work.ThmF.Ksub H t, a * k = k * a) → a = 1)
    {M : Subgroup G} (hMne : M ≠ ⊥) (hMcomm : IsMulCommutative ↥M)
    (hMexp : ∀ x : ↥M, x ^ ℓ = 1)
    (hMinv : ∀ x ∈ (Work.ThmF.Ksub H t ⊔ P), ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hMcard : Nat.card ↥M = ℓ ^ Nat.card P)
    (hMfpf : ∀ k ∈ Work.ThmF.Ksub H t, k ≠ 1 → ∀ m ∈ M, k * m * k⁻¹ = m → m = 1)
    (hKsim : ∀ N : Subgroup G, N ≤ M → N ≠ ⊥ →
      (∀ k ∈ Work.ThmF.Ksub H t, ∀ n ∈ N, k * n * k⁻¹ ∈ N) → N = M) :
    ∃ a ∈ P, ∀ k ∈ Work.ThmF.Ksub H t, a * k * a⁻¹ = k ^ ℓ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI hMcommI : IsMulCommutative ↥M := hMcomm
  haveI : Fact (∀ x : ↥M, x ^ ℓ = 1) := ⟨hMexp⟩
  haveI hKcycI : IsCyclic ↥(Work.ThmF.Ksub H t) := hKcyc
  haveI hKcomm : IsMulCommutative ↥(Work.ThmF.Ksub H t) := inferInstance
  obtain ⟨m0, hm0⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hMne
  haveI hMntA : Nontrivial (Additive ↥M) :=
    ⟨Additive.ofMul m0, 0, fun h => hm0 (by simpa using congrArg Additive.toMul h)⟩
  obtain ⟨x₀, hx₀⟩ := hKcyc.exists_generator
  -- `K ⊔ P` normalises `M`
  have hLn : (Work.ThmF.Ksub H t ⊔ P) ≤ Subgroup.normalizer (M : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy; exact hMinv x hx y hy
    · intro hy
      have h : x⁻¹ * (x * y * x⁻¹) * x ∈ M := by
        simpa using hMinv x⁻¹ ((Work.ThmF.Ksub H t ⊔ P).inv_mem hx) (x * y * x⁻¹) hy
      convert h using 1
      group
  -- `K` normalises itself inside `K ⊔ P`
  have hLnorm : ∀ x ∈ (Work.ThmF.Ksub H t ⊔ P), ∀ y ∈ Work.ThmF.Ksub H t,
      x * y * x⁻¹ ∈ Work.ThmF.Ksub H t := by
    have hPN : P ≤ Subgroup.normalizer (Work.ThmF.Ksub H t : Set G) := by
      intro p hp
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact ⟨fun hy => hKinv p hp y hy, fun hy => by
        have h := hKinv p⁻¹ (P.inv_mem hp) (p * y * p⁻¹) hy
        convert h using 1
        group⟩
    have hsup : (Work.ThmF.Ksub H t ⊔ P) ≤ Subgroup.normalizer (Work.ThmF.Ksub H t : Set G) :=
      sup_le Subgroup.le_normalizer hPN
    intro x hx y hy
    exact (Subgroup.mem_normalizer_iff.mp (hsup hx) y).mp hy
  -- the conjugation representation
  let ρ : Representation (ZMod ℓ) ↥(Work.ThmF.Ksub H t ⊔ P) (Additive ↥M) :=
    Work.ThmF.Prove.S3.conjRepOfLe (n := ℓ) (Work.ThmF.Ksub H t ⊔ P) M hLn
  let K' : Subgroup ↥(Work.ThmF.Ksub H t ⊔ P) :=
    (Work.ThmF.Ksub H t).subgroupOf (Work.ThmF.Ksub H t ⊔ P)
  have hK'n : K'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : ((n : ↥(Work.ThmF.Ksub H t ⊔ P)) : G) ∈ Work.ThmF.Ksub H t := hn
    rw [Subgroup.mem_subgroupOf]
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ Work.ThmF.Ksub H t
    exact hLnorm (g : G) g.2 (n : G) hn'
  -- simplicity of `↥M` over `𝔽_ℓ[K]`
  have hsimp : IsSimpleModule (MonoidAlgebra (ZMod ℓ) ↥K')
      (Representation.asModule (ρ.comp K'.subtype)) :=
    isSimpleModule_conjRep_of_simple hMne hLn (K := K')
      (fun N hNM hNne hinv => hKsim N hNM hNne (fun k hk n hn => by
        have h1 := hinv ⟨⟨k, Subgroup.mem_sup_left hk⟩, Subgroup.mem_subgroupOf.mpr hk⟩ n hn
        simpa using h1))
  -- faithfulness of the `K`-action
  have hfaith : ∀ k : ↥K', ρ (k : ↥(Work.ThmF.Ksub H t ⊔ P)) = 1 → k = 1 := by
    intro k hk
    have hk' : (Work.ThmF.Prove.S3.conjRepOfLe (n := ℓ) (Work.ThmF.Ksub H t ⊔ P) M hLn)
        (k : ↥(Work.ThmF.Ksub H t ⊔ P)) = 1 := hk
    have hm : ∀ m : ↥M, ((k : ↥(Work.ThmF.Ksub H t ⊔ P)) : G) * (m : G) *
        (((k : ↥(Work.ThmF.Ksub H t ⊔ P)) : G))⁻¹ = (m : G) := by
      intro m
      have h1 := congrArg (fun f : Additive ↥M →ₗ[ZMod ℓ] Additive ↥M => f (Additive.ofMul m)) hk'
      rw [Work.ThmF.Prove.S3.conjRepOfLe_apply] at h1
      have h2 := congrArg (fun z : ↥M => (z : G)) (by simpa using congrArg Additive.toMul h1)
      simpa using h2
    by_cases hk1 : ((k : ↥(Work.ThmF.Ksub H t ⊔ P)) : G) = 1
    · exact Subtype.ext (Subtype.ext hk1)
    · exfalso
      rw [Subgroup.ne_bot_iff_exists_ne_one] at hMne
      obtain ⟨m, hm1⟩ := hMne
      refine hm1 (Subtype.ext (by
        have hmem : ((k : ↥(Work.ThmF.Ksub H t ⊔ P)) : G) ∈ Work.ThmF.Ksub H t := k.2
        simpa using hMfpf ((k : ↥(Work.ThmF.Ksub H t ⊔ P)) : G) hmem hk1 (m : G) m.2 (hm m)))
  -- the `𝔽_ℓ`-power map `Φ` on `K` and the conjugation hom `γ`
  obtain ⟨γ, hγ⟩ := exists_conjMulAutHom (K := Work.ThmF.Ksub H t) (P := P) hKinv
  obtain ⟨Φ, hΦ⟩ := powMulAut_of_not_dvd (K := ↥(Work.ThmF.Ksub H t)) hℓ hKlcop
  have hpow : ∀ n : ℕ, ∀ k : ↥(Work.ThmF.Ksub H t), (Φ ^ n) k = k ^ ℓ ^ n := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
        intro k
        rw [pow_succ', MulAut.mul_apply, ih, hΦ, ← pow_mul,
          show ℓ ^ n * ℓ = ℓ ^ (n + 1) from (pow_succ ℓ n).symm]
  -- the core input: `γ a` is a power of `Φ`
  have hγΦ : ∀ a : ↥P, ∃ i : ℕ, γ a = Φ ^ i := by
    intro a
    let g : ↥(Work.ThmF.Ksub H t ⊔ P) := ⟨(a : G), Subgroup.mem_sup_right a.2⟩
    let x' : ↥K' := ⟨⟨(x₀ : G), Subgroup.mem_sup_left x₀.2⟩, Subgroup.mem_subgroupOf.mpr x₀.2⟩
    obtain ⟨i, hi⟩ := conj_eq_pow_prime_of_simple (ℓ := ℓ) (L := ↥(Work.ThmF.Ksub H t ⊔ P))
      (K := K') hK'n ρ hsimp hfaith g x'
    refine ⟨i, ?_⟩
    have hgen : (a : G) * (x₀ : G) * (a : G)⁻¹ = ((x₀ : Work.ThmF.Ksub H t) : G) ^ ℓ ^ i := by
      have h1 := congrArg (fun z : ↥K' => ((z : ↥(Work.ThmF.Ksub H t ⊔ P)) : G)) hi
      simpa [g, x'] using h1
    have hgenΦ : γ a x₀ = (Φ ^ i) x₀ := by
      have h1 : ((γ a x₀ : ↥(Work.ThmF.Ksub H t)) : G)
          = ((((x₀ : ↥(Work.ThmF.Ksub H t)) ^ ℓ ^ i) : ↥(Work.ThmF.Ksub H t)) : G) := by
        rw [hγ a x₀, hgen, Subgroup.coe_pow]
      rw [hpow i]
      exact Subtype.ext h1
    apply MulEquiv.ext
    intro k
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hx₀ k)
    rw [← hj, map_zpow, hgenΦ, ← map_zpow]
  have hmem : ∀ a : ↥P, γ a ∈ Subgroup.zpowers Φ := by
    intro a
    obtain ⟨i, hi⟩ := hγΦ a
    exact Subgroup.mem_zpowers_iff.mpr ⟨(i : ℤ), by rw [zpow_natCast, hi]⟩
  -- `K` acts freely on `M^# = M \ {1}`, so `|K|` divides `ℓ ^ |P| - 1`
  have hcard_dvd : Nat.card ↥(Work.ThmF.Ksub H t) ∣ ℓ ^ Nat.card ↥P - 1 := by
    haveI hKN' : Fact (Work.ThmF.Ksub H t ≤ Subgroup.normalizer (M : Set G)) :=
      ⟨le_trans le_sup_left hLn⟩
    have hfree : ∀ k : ↥(Work.ThmF.Ksub H t), k ≠ 1 →
        ∀ y : {m : ↥M // m ≠ 1}, k • y = y → False := by
      intro k hk y hy
      have h1 : (k : G) * ((y.1 : ↥M) : G) * (k : G)⁻¹ = ((y.1 : ↥M) : G) := by
        have h2 : (((k • y : {m : ↥M // m ≠ 1}).1 : ↥M) : G) = ((y.1 : ↥M) : G) :=
          congrArg (fun z : {m : ↥M // m ≠ 1} => ((z.1 : ↥M) : G)) hy
        rw [msharpConjMulAction_smul_val] at h2
        exact h2
      have h3 : (k : G) ≠ 1 := fun h4 => hk (Subtype.ext h4)
      exact y.2 (Subtype.ext (by
        simpa using hMfpf (k : G) k.2 h3 ((y.1 : ↥M) : G) y.1.2 h1))
    have hdvd := Work.ThmF.Prove.S3.card_dvd_card_of_free_action hfree
    rw [card_compl_singleton (1 : ↥M), hMcard] at hdvd
    exact hdvd
  have hΦp : Φ ^ Nat.card ↥P = 1 := by
    apply MulEquiv.ext
    intro k
    rw [hpow (Nat.card ↥P) k]
    show k ^ (ℓ ^ Nat.card ↥P) = k
    have h1 : orderOf k ∣ ℓ ^ Nat.card ↥P - 1 :=
      (orderOf_dvd_natCard k).trans hcard_dvd
    have h2 : k ^ (ℓ ^ Nat.card ↥P - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
    have h3 : 1 ≤ ℓ ^ Nat.card ↥P :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hℓ.ne_zero)
    calc k ^ (ℓ ^ Nat.card ↥P) = k ^ (ℓ ^ Nat.card ↥P - 1 + 1) := by
          rw [Nat.sub_add_cancel h3]
      _ = k ^ (ℓ ^ Nat.card ↥P - 1) * k ^ 1 := by rw [pow_add]
      _ = k := by rw [h2, one_mul, pow_one]
  -- `γ` is injective
  have hγinj : Function.Injective γ := by
    intro a b hab
    have h1 : ∀ k : ↥(Work.ThmF.Ksub H t),
        (a : G) * (k : G) * (a : G)⁻¹ = (b : G) * (k : G) * (b : G)⁻¹ := by
      intro k
      have h2 := congrArg (fun f : MulAut ↥(Work.ThmF.Ksub H t) =>
        ((f k : ↥(Work.ThmF.Ksub H t)) : G)) hab
      simpa [hγ a k, hγ b k] using h2
    have h3 : ∀ k ∈ Work.ThmF.Ksub H t,
        (b : G)⁻¹ * (a : G) * k = k * ((b : G)⁻¹ * (a : G)) := by
      intro k hk
      have h4 := h1 ⟨k, hk⟩
      calc (b : G)⁻¹ * (a : G) * k
          = (b : G)⁻¹ * ((a : G) * k * (a : G)⁻¹) * (a : G) := by group
        _ = (b : G)⁻¹ * ((b : G) * k * (b : G)⁻¹) * (a : G) := by rw [h4]
        _ = k * ((b : G)⁻¹ * (a : G)) := by group
    have h5 : (b : G)⁻¹ * (a : G) ∈ P := P.mul_mem (P.inv_mem b.2) a.2
    have h6 : (b : G)⁻¹ * (a : G) = 1 := hPcent _ h5 h3
    exact Subtype.ext (by simpa using congrArg (fun x : G => (b : G) * x) h6)
  obtain ⟨a, ha⟩ := exists_eq_of_mem_zpowers_of_prime_card (A := MulAut ↥(Work.ThmF.Ksub H t))
    (P := ↥P) c.P_prime Φ hΦp γ hγinj hmem
  refine ⟨a.1, a.2, fun k hk => ?_⟩
  have h1 : γ a ⟨k, hk⟩ = Φ ⟨k, hk⟩ := by rw [ha]
  have h2 : ((γ a ⟨k, hk⟩ : ↥(Work.ThmF.Ksub H t)) : G)
      = (((⟨k, hk⟩ : ↥(Work.ThmF.Ksub H t)) ^ ℓ : ↥(Work.ThmF.Ksub H t)) : G) := by
    rw [h1, hΦ]
  rw [hγ a ⟨k, hk⟩] at h2
  simpa using h2

end Work.ThmF.Prove.S3

