/-
# `Submission.Work.NormalComplement.S5K.prop1_step3_aux3`

The arithmetic core of Peterfalvi I Ch. III §4 Prop. 1, step 3:

* `exists_subgroup_pow_eq_one` — in a cyclic group of order `p ^ k` (`k ≥ 1`, `p` prime), the
  solutions of `x ^ p = 1` form a subgroup of order `p`;
* `exists_D_of_isCyclic_quotient` — if `P₁/P` is cyclic (encoded by a surjection `φ : ↥P₁ →* K`
  with kernel `P.subgroupOf P₁` and `K` cyclic of order `p ^ k`, `k ≥ 1`), there is a subgroup `D`
  with `P ≤ D ≤ P₁`, `Nat.card ↥D = p ^ 2`, `D ≤ {z ∈ P₁ : z ^ p ∈ P}` and
  `{z ∈ P₁ : z ^ p ∈ P} ≤ D`;
* `card_dvd_sub_one_of_fpf` — if `R ≤ N_G(D) ⊓ C_G(P)` acts on `D \ P` with trivial stabilisers,
  then `Nat.card R ∣ p - 1`.
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.S5K.prop1_step3_defs
import Submission.Work.NormalComplement.S5K.prop1_step3_aux
import Submission.Work.NormalComplement.S5K.prop1_step3_aux2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Classical
open scoped Pointwise
open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.S5K

/-! ## The solutions of `x ^ p = 1` in a cyclic `p`-group -/

/-- In a cyclic group `A` of order `p ^ k` (`k ≥ 1`), the set of solutions of `w ^ p = 1` is a
subgroup of order `p` (it is the kernel of the `p`-th power endomorphism; a cyclic subgroup of
order `p ^ m` would have an element of order `p ^ m`, so `m ≤ 1`, and Cauchy gives `m ≥ 1`). -/
lemma exists_subgroup_pow_eq_one {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {p k : ℕ} (hp : p.Prime) (hcard : Nat.card A = p ^ k) (hk : 1 ≤ k) :
    ∃ S : Subgroup A, Nat.card ↥S = p ∧ ∀ w : A, w ∈ S ↔ w ^ p = 1 := by
  classical
  letI : CommGroup A := IsCyclic.commGroup
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype A := Fintype.ofFinite A
  let φ : A →* A :=
    { toFun := fun w => w ^ p, map_one' := one_pow p, map_mul' := fun a b => mul_pow a b p }
  have hA : IsPGroup p ↥(⊤ : Subgroup A) :=
    IsPGroup.iff_card.mpr ⟨k, by rw [Subgroup.card_top]; exact hcard⟩
  have hker : IsPGroup p ↥φ.ker := IsPGroup.to_le hA le_top
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := p) (G := ↥φ.ker)).mp hker
  have hle : m ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    haveI : IsCyclic ↥φ.ker := Subgroup.isCyclic φ.ker
    obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := ↥φ.ker)
    have hzord : orderOf z = Nat.card ↥φ.ker := orderOf_eq_card_of_forall_mem_zpowers hz
    have hzp : (z : A) ^ p = 1 := MonoidHom.mem_ker.mp z.2
    have h1 : orderOf (z : A) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hzp
    rw [Subgroup.orderOf_coe, hzord, hm] at h1
    have h2 : p ^ m ≤ p := Nat.le_of_dvd hp.pos h1
    have h3 : m ≤ 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp (by simpa using h2)
    omega
  have hge : 1 ≤ m := by
    by_contra hcon
    push_neg at hcon
    have hm0 : m = 0 := by omega
    have hpA : p ∣ Nat.card A := by rw [hcard]; exact dvd_pow_self p (by omega)
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (G := A) p
      (by rwa [Nat.card_eq_fintype_card] at hpA)
    have ha1 : a ^ p = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
    have hmem : a ∈ φ.ker := MonoidHom.mem_ker.mpr ha1
    have hbot : φ.ker = ⊥ := Subgroup.card_eq_one.mp (by rw [hm, hm0, pow_zero])
    have ha1' : a = 1 := Subgroup.mem_bot.mp (hbot ▸ hmem)
    rw [ha1', orderOf_one] at ha
    exact hp.ne_one ha.symm
  exact ⟨φ.ker, by rw [hm, show m = 1 from by omega, pow_one],
    fun w => MonoidHom.mem_ker⟩

/-! ## Existence of a subgroup `D` of order `p ^ 2` inside `{z ∈ P₁ : z ^ p ∈ P}` -/

variable {G : Type} [Group G] [Finite G]
variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}

/-- **Construction of `D`** (the preimage in `P₁` of the subgroup of order `p` of the cyclic group
`P₁ ⧸ P`).  The cyclicity of `P₁/P` is encoded by a surjection `φ : ↥P₁ →* K` with kernel
`P.subgroupOf P₁` and `K` cyclic of order `p ^ k`.  The proof picks a generator `x` of `K`, puts
`e := x₀ ^ p ^ (k - 1)` for a preimage `x₀ ∈ P₁` of `x`, and shows `D := {z ∈ P₁ : z ^ p ∈ P}` equals
`⟨e⟩ · P`; `e` has order `p` modulo `P`, and `⟨e⟩ ∩ P = ⟨e^p⟩` has index `p` in `⟨e⟩`. -/
theorem exists_D_of_isCyclic_quotient {K : Type*} [Group K] [Finite K] {P P₁ : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hPP₁ : P ≤ P₁) (hPnorm : P₁ ≤ Subgroup.normalizer (P : Set G))
    (hPcard : Nat.card ↥P = p)
    {φ : ↥P₁ →* K} (hφsurj : Function.Surjective φ) (hφker : φ.ker = P.subgroupOf P₁)
    (hcyc : IsCyclic K) (hk : ∃ k : ℕ, 1 ≤ k ∧ Nat.card K = p ^ k) :
    ∃ D : Subgroup G, P ≤ D ∧ D ≤ P₁ ∧ Nat.card ↥D = p ^ 2 ∧
      (∀ z ∈ D, z ^ p ∈ P) ∧ (∀ z ∈ P₁, z ^ p ∈ P → z ∈ D) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hcycI : IsCyclic K := hcyc
  obtain ⟨k, hk1, hKcard⟩ := hk
  set P₀ : Subgroup ↥P₁ := P.subgroupOf P₁ with hP₀
  have hφker' : φ.ker = P₀ := hφker
  have hcardP₀ : Nat.card ↥P₀ = p := by
    rw [hP₀, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPP₁).toEquiv]
    exact hPcard
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  have hgord : orderOf g = p ^ k := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hKcard]
  obtain ⟨x, hxg⟩ := hφsurj g
  set y : ↥P₁ := x ^ (p ^ (k - 1)) with hy
  have hφy : φ y = g ^ (p ^ (k - 1)) := by rw [hy, map_pow, hxg]
  have hordφy : orderOf (φ y) = p := by
    rw [hφy, orderOf_pow, hgord]
    have h1 : (p ^ k).gcd (p ^ (k - 1)) = p ^ (k - 1) :=
      Nat.gcd_eq_right (pow_dvd_pow p (by omega : k - 1 ≤ k))
    rw [h1, Nat.pow_div (by omega : k - 1 ≤ k) hp.pos,
      show k - (k - 1) = 1 from by omega, pow_one]
  have hcrit : ∀ i : ℤ, (y : G) ^ i ∈ P ↔ (p : ℤ) ∣ i := by
    intro i
    have h1 : ((y : G) ^ i ∈ P) ↔ (y ^ i ∈ P₀) := by
      rw [hP₀, Subgroup.mem_subgroupOf, Subgroup.coe_zpow]
    rw [h1, ← hφker', MonoidHom.mem_ker, map_zpow, ← hordφy]
    exact orderOf_dvd_iff_zpow_eq_one.symm
  have hPe : (y : G) ^ p ∈ P := by
    have h := (hcrit (p : ℤ)).mpr (dvd_refl ((p : ℤ)))
    rwa [zpow_natCast] at h
  obtain ⟨S, hScard, hS⟩ := exists_subgroup_pow_eq_one (A := K) hp hKcard hk1
  have hφymem : φ y ∈ S := (hS _).mpr (by rw [← hordφy]; exact pow_orderOf_eq_one _)
  have hSeq : S = Subgroup.zpowers (φ y) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hφymem) ?_).symm
    rw [hScard, Nat.card_zpowers, hordφy]
  have hincr : Subgroup.zpowers ((y : G)) ⊓ P = Subgroup.zpowers ((y : G) ^ p) := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨hzE, hzP⟩ := Subgroup.mem_inf.mp hz
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzE
      rw [← hm] at hzP
      obtain ⟨n, hn⟩ := (hcrit m).mp hzP
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have h1 : (y : G) ^ m = ((y : G) ^ p) ^ n := by
        rw [hn, ← zpow_natCast ((y : G)) p, zpow_mul]
      rw [← hm, h1]
    · exact le_inf (Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers_iff.mpr ⟨(p : ℤ), by rw [zpow_natCast]⟩))
        (Subgroup.zpowers_le.mpr hPe)
  have heN : Subgroup.zpowers ((y : G)) ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr (hPnorm y.2)
  have hsup_le : Subgroup.zpowers ((y : G)) ⊔ P ≤ P₁ :=
    sup_le (Subgroup.zpowers_le.mpr y.2) hPP₁
  refine ⟨Subgroup.zpowers ((y : G)) ⊔ P, le_sup_right, hsup_le, ?_, ?_, ?_⟩
  · -- `|⟨e⟩ ⊔ P| = p ^ 2`
    rw [show Subgroup.zpowers ((y : G)) ⊔ P = P ⊔ Subgroup.zpowers ((y : G)) from sup_comm ..]
    have h1 := Work.NormalComplement.card_sup_mul_card_inf (H := P)
      (K := Subgroup.zpowers ((y : G))) heN
    rw [inf_comm, hincr, Nat.card_zpowers, hPcard, Nat.card_zpowers] at h1
    have hpe : p ∣ orderOf ((y : G)) := by
      have h := (hcrit ((orderOf ((y : G))) : ℤ)).mp (by
        rw [zpow_natCast, pow_orderOf_eq_one]; exact P.one_mem)
      rwa [Int.natCast_dvd_natCast] at h
    have hordp : orderOf ((y : G) ^ p) = orderOf ((y : G)) / p := by
      rw [orderOf_pow, Nat.gcd_eq_right hpe]
    rw [hordp] at h1
    have h2 : orderOf ((y : G)) = p * (orderOf ((y : G)) / p) := (Nat.mul_div_cancel' hpe).symm
    have h3 : 0 < orderOf ((y : G)) / p :=
      Nat.div_pos (Nat.le_of_dvd (orderOf_pos _) hpe) hp.pos
    have h4 : Nat.card ↥(P ⊔ Subgroup.zpowers ((y : G))) * (orderOf ((y : G)) / p) =
        (p * p) * (orderOf ((y : G)) / p) := by
      rw [h1]
      nth_rewrite 1 [h2]
      ring
    have h5 : Nat.card ↥(P ⊔ Subgroup.zpowers ((y : G))) = p * p :=
      Nat.eq_of_mul_eq_mul_right h3 h4
    rw [h5, pow_two]
  · -- every `p`-th power in `⟨e⟩ · P` lies in `P`
    intro z hz
    have hzP₁ : z ∈ P₁ := hsup_le hz
    have hz' : z ∈ P ⊔ Subgroup.zpowers ((y : G)) := by rwa [sup_comm] at hz
    have hcoe : (((P ⊔ Subgroup.zpowers ((y : G)) : Subgroup G)) : Set G) =
        (P : Set G) * (Subgroup.zpowers ((y : G)) : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left P (Subgroup.zpowers ((y : G))) heN
    have hz'' : z ∈ (P : Set G) * (Subgroup.zpowers ((y : G)) : Set G) := by
      rw [← hcoe]; exact hz'
    obtain ⟨q, hq, a, ha, hqa⟩ := Set.mem_mul.mp hz''
    have hqP₁ : q ∈ P₁ := hPP₁ hq
    have haP₁ : a ∈ P₁ := Subgroup.zpowers_le.mpr y.2 ha
    have hφq : φ ⟨q, hqP₁⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hφker', hP₀, Subgroup.mem_subgroupOf]; exact hq
    have hφyp : (φ y) ^ p = 1 := by rw [← hordφy]; exact pow_orderOf_eq_one _
    have hφa : φ ⟨a, haP₁⟩ ∈ Subgroup.zpowers (φ y) := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
      have h2 : (⟨a, haP₁⟩ : ↥P₁) = (⟨y, y.2⟩ : ↥P₁) ^ m := by
        refine Subtype.ext ?_
        simpa using hm.symm
      rw [h2, map_zpow]
    have hφz : φ ⟨z, hzP₁⟩ = φ ⟨a, haP₁⟩ := by
      have h1 : (⟨z, hzP₁⟩ : ↥P₁) = ⟨q, hqP₁⟩ * ⟨a, haP₁⟩ :=
        Subtype.ext (by rw [Subgroup.coe_mul]; exact hqa.symm)
      rw [h1, map_mul, hφq, one_mul]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hφz ▸ hφa)
    have hzp1 : (φ ⟨z, hzP₁⟩) ^ p = 1 := by
      have h1 : (φ ⟨z, hzP₁⟩) ^ p = (φ y) ^ (m * (p : ℤ)) := by
        rw [← hm, ← zpow_natCast ((φ y) ^ m) p, ← zpow_mul]
      rw [h1, show m * (p : ℤ) = (p : ℤ) * m from by ring, zpow_mul,
        zpow_natCast, hφyp, one_zpow]
    have hmem : (⟨z, hzP₁⟩ : ↥P₁) ^ p ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow]; exact hzp1
    rw [hφker', hP₀, Subgroup.mem_subgroupOf, Subgroup.coe_pow] at hmem
    exact hmem
  · -- every `z ∈ P₁` with `z ^ p ∈ P` lies in `⟨e⟩ · P`
    intro z hz hzp
    have hzmem : φ ⟨z, hz⟩ ∈ S := by
      rw [hS]
      have h1 : (φ ⟨z, hz⟩) ^ p = 1 := by
        rw [← map_pow, show (⟨z, hz⟩ : ↥P₁) ^ p = ⟨z ^ p, P₁.pow_mem hz p⟩ from Subtype.ext rfl,
          ← MonoidHom.mem_ker, hφker', hP₀, Subgroup.mem_subgroupOf]
        exact hzp
      exact h1
    rw [hSeq] at hzmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzmem
    have hmem2 : (⟨z, hz⟩ : ↥P₁) * (y : ↥P₁) ^ (-m) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, ← hm, zpow_neg, mul_inv_cancel]
    rw [hφker', hP₀, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_zpow] at hmem2
    have hzq : z = (z * (y : G) ^ (-m)) * (y : G) ^ m := by group
    have hyz : (y : G) ^ m ∈ Subgroup.zpowers ((y : G)) ⊔ P :=
      Subgroup.mem_sup_left (show (y : G) ^ m ∈ Subgroup.zpowers ((y : G)) from
        Subgroup.mem_zpowers_iff.mpr ⟨m, rfl⟩)
    have hz2 : z * (y : G) ^ (-m) ∈ Subgroup.zpowers ((y : G)) ⊔ P :=
      Subgroup.mem_sup_right hmem2
    rw [hzq]
    exact Subgroup.mul_mem (Subgroup.zpowers ((y : G)) ⊔ P) hz2 hyz

/-! ## The final count -/

/-- **`|R| ∣ p - 1`.**  If `P ≤ D`, `Nat.card ↥D = p ^ 2`, `R ≤ N_G(D) ⊓ C_G(P)` and `R` acts on
`D \ P` with trivial stabilisers, then `|R|` divides `p ^ 2 - p`, hence `p - 1` when `|R|` is
prime to `p`. -/
theorem card_dvd_sub_one_of_fpf {P D R : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hPcard : Nat.card ↥P = p) (hPD : P ≤ D)
    (hDcard : Nat.card ↥D = p ^ 2)
    (hRcen : R ≤ Subgroup.centralizer (P : Set G))
    (hRD : R ≤ Subgroup.normalizer (D : Set G))
    (hRcop : Nat.Coprime (Nat.card R) p)
    (hfpf : ∀ u ∈ R, u ≠ 1 → ∀ y ∈ D, u * y * u⁻¹ = y → y ∈ P) :
    Nat.card R ∣ p - 1 := by
  classical
  let X : Set G := (D : Set G) \ (P : Set G)
  have hXmem : ∀ y : G, y ∈ X ↔ y ∈ D ∧ y ∉ P := fun y => Iff.rfl
  have hXinv : ∀ (u : ↥R) (y : ↥X), (u : G) * (y : G) * (u : G)⁻¹ ∈ X := by
    intro u y
    obtain ⟨hyD, hyP⟩ := (hXmem (y : G)).mp y.2
    refine (hXmem _).mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hRD u.2) (y : G)).mp hyD
    · intro hcon
      have huN : (u : G) ∈ Subgroup.normalizer (P : Set G) :=
        Subgroup.centralizer_le_normalizer (P : Set G) (hRcen u.2)
      have h1 : (u : G)⁻¹ * ((u : G) * (y : G) * (u : G)⁻¹) * (u : G) ∈ P := by
        have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huN)
          ((u : G) * (y : G) * (u : G)⁻¹)).mp hcon
        simpa using h2
      have h3 : (y : G) = (u : G)⁻¹ * ((u : G) * (y : G) * (u : G)⁻¹) * (u : G) := by group
      exact hyP (h3 ▸ h1)
  letI : MulAction ↥R ↥X :=
    { smul := fun u y => ⟨(u : G) * (y : G) * (u : G)⁻¹, hXinv u y⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : ↥R) : G) * (y : G) * ((1 : ↥R) : G)⁻¹ = (y : G)
        rw [Subgroup.coe_one, one_mul, inv_one, mul_one])
      mul_smul := fun a b y => Subtype.ext (by
        show ((a * b : ↥R) : G) * (y : G) * ((a * b : ↥R) : G)⁻¹ =
          (a : G) * ((b : G) * (y : G) * (b : G)⁻¹) * (a : G)⁻¹
        rw [Subgroup.coe_mul]; group) }
  have hfpf' : ∀ u : ↥R, u ≠ 1 → ∀ y : ↥X, u • y = y → False := by
    intro u hu y hy
    have hu1 : (u : G) ≠ 1 := fun h => hu (Subtype.ext h)
    obtain ⟨hyD, hyP⟩ := (hXmem (y : G)).mp y.2
    exact hyP (hfpf (u : G) u.2 hu1 (y : G) hyD (congrArg Subtype.val hy))
  have hdvd : Nat.card ↥R ∣ Nat.card ↥X := card_dvd_card_of_fixedPointFree hfpf'
  have hXcard : Nat.card ↥X = p ^ 2 - p := by
    have h1 : X = (D : Set G) \ (P : Set G) := rfl
    rw [Nat.card_coe_set_eq, h1, Set.ncard_sdiff hPD,
      show (D : Set G).ncard = Nat.card ↥D from Nat.card_coe_set_eq (D : Set G),
      show (P : Set G).ncard = Nat.card ↥P from Nat.card_coe_set_eq (P : Set G),
      hDcard, hPcard]
  rw [hXcard] at hdvd
  have h2 : p ^ 2 - p = (p - 1) * p := by rw [Nat.sub_mul, one_mul, pow_two]
  rw [h2] at hdvd
  exact Nat.Coprime.dvd_of_dvd_mul_right hRcop hdvd

end Work.NormalComplement.S5K
