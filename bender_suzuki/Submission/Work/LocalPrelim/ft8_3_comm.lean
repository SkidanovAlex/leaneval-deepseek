import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.omega_one_eq_omega1
import Submission.Work.PGroup.omega_conj
import Submission.Work.PGroup.Symplectic.centralProduct_of_structure
import Submission.Work.LocalPrelim.exists_invariant_index_prime
import Submission.Work.LocalPrelim.ft8_3_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
open scoped Classical Pointwise commutatorElement
open Subgroup

namespace Work.LocalPrelim

variable {H : Type*} [Group H]

/-- `⟨y⟩` is finite when `y ^ p = 1`. -/
theorem finite_zpowers_of_pow_eq_one {p : ℕ} (hp : p.Prime) {y : H} (hyp : y ^ p = 1) :
    (Subgroup.zpowers y : Set H).Finite := by
  refine (Set.finite_range (fun i : Fin p => y ^ (i : ℕ))).subset ?_
  rintro z ⟨j, rfl⟩
  have hj : ((j % p).toNat : ℤ) = j % p :=
    Int.toNat_of_nonneg (Int.emod_nonneg j (by exact_mod_cast hp.ne_zero))
  have hlt : (j % p).toNat < p := by
    have h2 : j % (p : ℤ) < ↑p := Int.emod_lt_of_pos j (by exact_mod_cast hp.pos)
    omega
  refine Set.mem_range.mpr ⟨⟨(j % p).toNat, hlt⟩, ?_⟩
  have hmain : y ^ j = y ^ (j % (p : ℤ)) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv j (p : ℤ)]
    rw [zpow_add, zpow_mul, zpow_natCast, hyp, one_zpow, mul_one]
  show y ^ ((j % p).toNat : ℕ) = y ^ j
  rw [← zpow_natCast, hj]
  exact hmain.symm

/-- The index-`p` `y`-invariant extension in the ambient group. -/
theorem exists_invariant_index_p_extension {p : ℕ} (hp : p.Prime)
    {A E : Subgroup H} (hAp : IsPGroup p A) [Finite A]
    {y : H} (hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A) (hyp : y ^ p = 1)
    (hEA : E ≤ A) (hEinv : ∀ e ∈ E, y * e * y⁻¹ ∈ E) (hlt : E < A) :
    ∃ B : Subgroup H, E ≤ B ∧ B ≤ A ∧ E ≠ B ∧ (∀ b ∈ B, y * b * y⁻¹ ∈ B) ∧
      ⁅Subgroup.zpowers y, B⁆ ≤ E := by
  set K : Subgroup H := A ⊔ Subgroup.zpowers y with hK
  have hyfin : (Subgroup.zpowers y : Set H).Finite := finite_zpowers_of_pow_eq_one hp hyp
  haveI : Finite ↥(Subgroup.zpowers y) := hyfin.to_subtype
  haveI : Finite ↥A := inferInstance
  haveI hKfin : Finite ↥K := by
    have hsurj : Function.Surjective (fun q : ↥A × ↥(Subgroup.zpowers y) =>
        (⟨(q.1 : H) * (q.2 : H),
          Subgroup.mul_mem _ (Subgroup.mem_sup_left q.1.2) (Subgroup.mem_sup_right q.2.2)⟩ : ↥K)) := by
      intro z
      obtain ⟨e, he, j, hje⟩ := mem_sup_zpowers_of_finite (E := A) hyA (by rw [← hK]; exact z.2)
      exact ⟨(⟨e, he⟩, ⟨y ^ j, Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) j⟩), Subtype.ext hje⟩
    exact Finite.of_surjective _ hsurj
  -- the subgroups of `K` corresponding to `A`, `E`, `⟨y⟩`
  set Q : Subgroup ↥K := (Subgroup.zpowers y).subgroupOf K with hQ
  set A' : Subgroup ↥K := A.subgroupOf K with hA'
  set E' : Subgroup ↥K := E.subgroupOf K with hE'
  have hE'mem : ∀ x : ↥K, x ∈ E' ↔ (x : H) ∈ E := by
    intro x; rw [hE', Subgroup.mem_subgroupOf]
  have hA'mem : ∀ x : ↥K, x ∈ A' ↔ (x : H) ∈ A := by
    intro x; rw [hA', Subgroup.mem_subgroupOf]
  have hYp : IsPGroup p ↥(Subgroup.zpowers y) := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro z
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp z.2
    have hzp : z ^ p = 1 := by
      apply Subtype.ext
      show ((z : H)) ^ p = (1 : H)
      rw [← hj]
      have h1 : (y ^ j : H) ^ p = (y ^ j) ^ (p : ℤ) := by rw [zpow_natCast]
      rw [h1, ← zpow_mul, mul_comm j (p : ℤ), zpow_mul, zpow_natCast, hyp, one_zpow]
    exact ⟨1, by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hzp⟩
  have hQp : IsPGroup p ↥Q :=
    hYp.of_equiv (Subgroup.subgroupOfEquivOfLe (show Subgroup.zpowers y ≤ K from le_sup_right)).symm
  have hA'p : IsPGroup p ↥A' :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (show A ≤ K from le_sup_left)).symm
  -- `Q` is contained in the normalizers of `A'` and `E'`
  have hmemQ : ∀ q : ↥Q, ((q : ↥K) : H) ∈ Subgroup.zpowers y := by
    intro q
    have h1 : (q : ↥K) ∈ (Subgroup.zpowers y).subgroupOf K := by rw [← hQ]; exact q.2
    exact Subgroup.mem_subgroupOf.mp h1
  have hAnorm : Q ≤ Subgroup.normalizer (A' : Set ↥K) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have hkey : ∀ (x : ↥K), ((q * x * q⁻¹ : ↥K) : H) = ((q : ↥K) : H) * (x : H) * (((q : ↥K) : H))⁻¹ :=
      fun x => rfl
    constructor
    · intro ha
      obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp (hmemQ ⟨q, hq⟩)
      have haA : (a : H) ∈ A := (hA'mem a).mp ha
      rw [Subgroup.mem_subgroupOf]
      rw [hkey a, ← ht]
      simpa using conj_zpow_mem_of_finite hyA haA t
    · intro ha
      obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp (hmemQ ⟨q, hq⟩)
      have haA : ((q * a * q⁻¹ : ↥K) : H) ∈ A := (hA'mem _).mp ha
      rw [Subgroup.mem_subgroupOf]
      have h1 : (a : H) = y ^ (-t) * ((q * a * q⁻¹ : ↥K) : H) * y ^ t := by
        rw [hkey a, ← ht]
        rw [show (y ^ t)⁻¹ = y ^ (-t) by rw [zpow_neg]]
        group
      rw [h1]
      simpa using conj_zpow_mem_of_finite hyA haA (-t)
  haveI : Finite ↥E :=
    Finite.of_injective (Subgroup.inclusion hEA) (Subgroup.inclusion_injective hEA)
  have hE'norm : Q ≤ Subgroup.normalizer (E' : Set ↥K) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro e
    have hkey : ∀ (x : ↥K), ((q * x * q⁻¹ : ↥K) : H) = ((q : ↥K) : H) * (x : H) * (((q : ↥K) : H))⁻¹ :=
      fun x => rfl
    constructor
    · intro he
      obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp (hmemQ ⟨q, hq⟩)
      have heE : (e : H) ∈ E := (hE'mem e).mp he
      rw [Subgroup.mem_subgroupOf]
      rw [hkey e, ← ht]
      simpa using conj_zpow_mem_of_finite hEinv heE t
    · intro he
      obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp (hmemQ ⟨q, hq⟩)
      have heE : ((q * e * q⁻¹ : ↥K) : H) ∈ E := (hE'mem _).mp he
      rw [Subgroup.mem_subgroupOf]
      have h1 : (e : H) = y ^ (-t) * ((q * e * q⁻¹ : ↥K) : H) * y ^ t := by
        rw [hkey e, ← ht]
        rw [show (y ^ t)⁻¹ = y ^ (-t) by rw [zpow_neg]]
        group
      rw [h1]
      simpa using conj_zpow_mem_of_finite hEinv heE (-t)
  have hE'le : E' ≤ A' := by
    intro x hx
    exact (hA'mem x).mpr (hEA ((hE'mem x).mp hx))
  have hlt' : E' < A' := by
    refine lt_of_le_of_ne hE'le ?_
    intro hcon
    refine hlt.ne (le_antisymm hEA fun a ha => ?_)
    have h1 : (⟨a, Subgroup.mem_sup_left ha⟩ : ↥K) ∈ A' := (hA'mem _).mpr ha
    have h2 : (⟨a, Subgroup.mem_sup_left ha⟩ : ↥K) ∈ E' := hcon ▸ h1
    exact (hE'mem _).mp h2
  obtain ⟨B', hE'B', hB'A', hidx, hcomm⟩ :=
    exists_invariant_index_prime hp hQp hA'p hAnorm hE'norm hE'le hlt'
  set B : Subgroup H := B'.map K.subtype with hB
  have hEB : E ≤ B := by
    rw [hB]
    calc E = E'.map K.subtype := by
          rw [hE', Subgroup.subgroupOf_map_subtype,
            inf_eq_left.mpr (hEA.trans (show A ≤ K from le_sup_left))]
      _ ≤ B'.map K.subtype := Subgroup.map_mono hE'B'
  have hBA : B ≤ A := by
    rw [hB]
    calc B'.map K.subtype ≤ A'.map K.subtype := Subgroup.map_mono hB'A'
      _ = A := by rw [hA', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_left]
  have hne : E ≠ B := by
    intro hcon
    have hmap : E'.map K.subtype = B'.map K.subtype := by
      rw [hE', Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr (hEA.trans (show A ≤ K from le_sup_left)), hcon, ← hB]
    have h1 : E' = B' := Subgroup.map_injective K.subtype_injective hmap
    have h2 : (E'.subgroupOf B').index = 1 := by
      rw [h1, Subgroup.subgroupOf_self]; exact Subgroup.index_top
    rw [hidx] at h2
    exact hp.ne_one h2
  -- `y` normalizes `B`
  have hyQ : (⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩ : ↥K) ∈ Q := by
    rw [hQ, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers y
  have hBin : ∀ b ∈ B, y * b * y⁻¹ ∈ B := by
    intro b hb
    rw [hB] at hb ⊢
    obtain ⟨b', hb', hb'b⟩ := Subgroup.mem_map.mp hb
    have hc : ⁅(⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩ : ↥K), b'⁆ ∈ E' :=
      Subgroup.commutator_le.mp hcomm _ hyQ _ hb'
    have hcE : ((⁅(⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩ : ↥K), b'⁆ : ↥K) : H) ∈ E :=
      (hE'mem _).mp hc
    have hval : ((⁅(⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩ : ↥K), b'⁆ : ↥K) : H)
        = y * (b' : H) * y⁻¹ * (b' : H)⁻¹ := by
      rw [commutatorElement_def]; rfl
    rw [← hb'b]
    refine Subgroup.mem_map.mpr ⟨⁅(⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩ : ↥K), b'⁆ * b',
      Subgroup.mul_mem B' ?_ hb', ?_⟩
    · exact hE'B' ((hE'mem _).mpr hcE)
    · show ((⁅(⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩ : ↥K), b'⁆ * b' : ↥K) : H)
          = y * (b' : H) * y⁻¹
      rw [Subgroup.coe_mul, hval]
      group
  refine ⟨B, hEB, hBA, hne, hBin, ?_⟩
  -- the commutator condition
  have hcomm' : ⁅Subgroup.zpowers y, B⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [hB] at hb
    obtain ⟨b', hb', hb'b⟩ := Subgroup.mem_map.mp hb
    have hai : (⟨y ^ i, Subgroup.mem_sup_right (Subgroup.zpow_mem (Subgroup.zpowers y)
        (Subgroup.mem_zpowers y) i)⟩ : ↥K) ∈ Q := by
      rw [hQ, Subgroup.mem_subgroupOf]
      exact Subgroup.zpow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) i
    have hc : ⁅(⟨y ^ i, Subgroup.mem_sup_right (Subgroup.zpow_mem (Subgroup.zpowers y)
        (Subgroup.mem_zpowers y) i)⟩ : ↥K), b'⁆ ∈ E' :=
      Subgroup.commutator_le.mp hcomm _ hai _ hb'
    have hcE : ((⁅(⟨y ^ i, Subgroup.mem_sup_right (Subgroup.zpow_mem (Subgroup.zpowers y)
        (Subgroup.mem_zpowers y) i)⟩ : ↥K), b'⁆ : ↥K) : H) ∈ E := (hE'mem _).mp hc
    rw [← hb'b]
    simpa [commutatorElement_def] using hcE
  exact hcomm'

/-- FT 8.3 for a finite abelian `p`-subgroup `A` normalised by `y` of order dividing `p` that
centralises `Ω₁(A)`. -/
theorem ft8_3_finite {H : Type*} [Group H] {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    {A : Subgroup H} (hAab : IsMulCommutative A) (hAp : IsPGroup p A) [Finite A]
    {y : H} (hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A) (hyp : y ^ p = 1)
    (hyC : y ∈ Subgroup.centralizer ((Work.PGroup.omega p 1 A : Subgroup H) : Set H)) :
    ⁅A, Subgroup.zpowers y⁆ ≤ Work.PGroup.omega p 1 A := by
  let Ω : Subgroup H := Work.PGroup.omega1 H p A
  have hΩeq : Work.PGroup.omega p 1 A = Ω := Work.PGroup.omega_one_eq_omega1 p A
  rw [hΩeq]
  have hΩA : Ω ≤ A := Work.PGroup.omega1_le p A
  have hyΩ : ∀ ω ∈ Ω, y * ω = ω * y := fun ω hω =>
    (Subgroup.mem_centralizer_iff.mp hyC ω (by rw [hΩeq]; exact hω)).symm
  set S : Set (Subgroup H) := {E | Ω ≤ E ∧ E ≤ A ∧ (∀ e ∈ E, y * e * y⁻¹ ∈ E) ∧
    ⁅E, Subgroup.zpowers y⁆ ≤ Ω} with hS
  have hSfin : S.Finite := by
    have hmap : Set.Finite ((fun E : Subgroup H => (E : Set H)) '' S) :=
      (Set.Finite.powerset (Set.toFinite (A : Set H))).subset (by
        rintro _ ⟨E, hE, rfl⟩
        rw [Set.mem_powerset_iff]
        exact hE.2.1)
    exact Set.Finite.of_finite_image hmap (fun E _ E' _ h => SetLike.coe_set_eq.mp h)
  have hΩS : Ω ∈ S := by
    refine ⟨le_refl Ω, hΩA, fun e he => ?_, ?_⟩
    · rw [show y * e * y⁻¹ = e by rw [hyΩ e he]; group]; exact he
    · rw [Subgroup.commutator_le]
      intro a ha z hz
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hcy : Commute y a := by rw [commute_iff_eq]; exact hyΩ a ha
      have hcom : y ^ j * a = a * y ^ j := (hcy.zpow_left j).eq
      rw [show ⁅a, y ^ j⁆ = 1 by rw [commutatorElement_def, ← hcom]; group]
      exact Ω.one_mem
  obtain ⟨E, hEfin, hEmax⟩ := hSfin.toFinset.exists_max_image (fun E => Nat.card ↥E)
    (hSfin.toFinset_nonempty.mpr ⟨Ω, hΩS⟩)
  have hES : E ∈ S := (hSfin.mem_toFinset).mp hEfin
  have hEA : E ≤ A := hES.2.1
  have hAE : A = E := by
    by_contra hne
    have hlt : E < A := lt_of_le_of_ne hEA (Ne.symm hne)
    obtain ⟨B, hEB, hBA, hEneB, hBin, hcomm⟩ :=
      exists_invariant_index_p_extension (p := p) hp (A := A) (E := E) hAp hyA hyp hEA
        hES.2.2.1 hlt
    haveI : Finite ↥B :=
      Finite.of_injective (Subgroup.inclusion hBA) (Subgroup.inclusion_injective hBA)
    have hBS : B ∈ S :=
      ⟨hES.1.trans hEB, hBA, hBin,
        commutator_le_of_index_p hp hpodd hAab hEA hBA hEB hyA hyp hyΩ hES.2.2.1 hES.1 hcomm
          hES.2.2.2⟩
    have hcard := hEmax B ((hSfin.mem_toFinset).mpr hBS)
    have hlt2 : Nat.card ↥E < Nat.card ↥B :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne hEB hEneB)
    omega
  rw [hAE]
  exact hES.2.2.2

/-- The `y`-orbit of `a ∈ A` spans a finite `y`-invariant subgroup of `A`. -/
theorem ft8_3_orbit_finite {p : ℕ} (hp : p.Prime)
    {A : Subgroup H} (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    {y : H} (hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A) (hyp : y ^ p = 1)
    {a : H} (ha : a ∈ A) :
    ∃ A' : Subgroup H, a ∈ A' ∧ A' ≤ A ∧ Finite A' ∧ (∀ x ∈ A', y * x * y⁻¹ ∈ A') := by
  set f : Fin p → H := fun i => y ^ (((i : ℕ) : ℤ)) * a * y ^ (-(((i : ℕ) : ℤ))) with hf
  set T : Set H := Set.range f with hT
  have hTfin : T.Finite := by rw [hT]; exact Set.finite_range f
  set A' : Subgroup H := Subgroup.closure T with hA'
  have hTA' : T ⊆ (A' : Set H) := by rw [hA']; exact Subgroup.subset_closure
  have hgen : ∀ n : ℕ, y ^ ((n : ℤ)) * a * y ^ (-((n : ℤ))) ∈ A := by
    intro n
    induction n with
    | zero => simpa using ha
    | succ n ih =>
      have h2 : (((n + 1 : ℕ)) : ℤ) = ((n : ℕ) : ℤ) + 1 := by push_cast; ring
      have h3 : -(((n : ℕ) : ℤ) + 1) = -((n : ℕ) : ℤ) - 1 := by ring
      have h1 : y ^ (((n : ℕ) : ℤ) + 1) * a * y ^ (-(((n : ℕ) : ℤ) + 1))
          = y * (y ^ (((n : ℕ) : ℤ)) * a * y ^ (-(((n : ℕ) : ℤ)))) * y⁻¹ := by
        rw [h3, zpow_add_one, zpow_sub_one]
        group
      rw [h2, h1]
      exact hyA _ ih
  have hA'A : A' ≤ A := by
    rw [hA', Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact hgen (i : ℕ)
  -- `y` permutes the orbit, hence preserves `A'`
  have hTinv : ∀ x ∈ T, y * x * y⁻¹ ∈ T := by
    rintro x ⟨i, rfl⟩
    by_cases h : (i : ℕ) + 1 < p
    · refine Set.mem_range.mpr ⟨⟨(i : ℕ) + 1, h⟩, ?_⟩
      show f ⟨(i : ℕ) + 1, h⟩ = y * f i * y⁻¹
      simp only [hf]
      push_cast
      have hx : -(((i : ℕ) : ℤ) + 1) = -(((i : ℕ) : ℤ)) - 1 := by ring
      rw [zpow_add_one, hx, zpow_sub_one]
      group
    · have hieq : (i : ℕ) + 1 = p := by have := i.2; omega
      refine Set.mem_range.mpr ⟨⟨0, hp.pos⟩, ?_⟩
      show f ⟨0, hp.pos⟩ = y * f i * y⁻¹
      simp only [hf, Nat.cast_zero, neg_zero, zpow_zero, mul_one]
      have hyi : y ^ ((i : ℕ) : ℤ) = y⁻¹ := by
        have h1 : y ^ (((i : ℕ) : ℤ) + 1) = 1 := by
          rw [show ((i : ℕ) : ℤ) + 1 = (p : ℤ) by exact_mod_cast hieq, zpow_natCast, hyp]
        rw [zpow_add_one] at h1
        exact eq_inv_of_mul_eq_one_left h1
      have h2 : y ^ (-((i : ℕ) : ℤ)) = y := by rw [zpow_neg, hyi, inv_inv]
      rw [hyi, h2]
      group
  have hA'inv : ∀ x ∈ A', y * x * y⁻¹ ∈ A' := by
    intro x hx
    rw [hA'] at hx ⊢
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · intro z hz; exact Subgroup.subset_closure (hTinv z hz)
    · simp
    · intro u v _ _ ihu ihv
      rw [show y * (u * v) * y⁻¹ = (y * u * y⁻¹) * (y * v * y⁻¹) from by group]
      exact A'.mul_mem ihu ihv
    · intro u _ ihu
      rw [show y * u⁻¹ * y⁻¹ = (y * u * y⁻¹)⁻¹ from by group]
      exact A'.inv_mem ihu
  have haA' : a ∈ A' := by
    have h0 : f ⟨0, hp.pos⟩ = a := by simp [hf]
    rw [← h0]
    exact hTA' (Set.mem_range_self _)
  refine ⟨A', haA', hA'A, ?_, hA'inv⟩
  -- `A'` is finitely generated and torsion, hence finite
  have hfg : Group.FG ↥A' := by
    refine Group.fg_iff.mpr ⟨{z : ↥A' | (z : H) ∈ T}, ?_, hTfin.preimage Subtype.val_injective.injOn⟩
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hxT : x ∈ Subgroup.closure T := by rw [← hA']; exact hx
    let motive : (w : H) → (w ∈ Subgroup.closure T) → Prop := fun w hw =>
      (⟨w, by rw [hA']; exact hw⟩ : ↥A') ∈ Subgroup.closure {z : ↥A' | (z : H) ∈ T}
    have hkey : motive x hxT := by
      refine Subgroup.closure_induction (p := motive) ?_ ?_ ?_ ?_ hxT
      · intro z hz
        exact Subgroup.subset_closure (show (⟨z, by rw [hA']; exact Subgroup.subset_closure hz⟩ : ↥A')
            ∈ {z : ↥A' | (z : H) ∈ T} from hz)
      · exact Subgroup.one_mem _
      · intro u v hu hv ihu ihv
        exact Subgroup.mul_mem _ ihu ihv
      · intro u hu ihu
        exact Subgroup.inv_mem _ ihu
    exact hkey
  have htor : IsMulTorsion ↥A' := by
    intro x
    obtain ⟨k, hk⟩ := hAp ⟨(x : H), hA'A x.2⟩
    have hkH : ((x : H)) ^ p ^ k = 1 := by
      have h1 := congrArg (fun z : ↥A => (z : H)) hk
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h1
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ k, pow_pos hp.pos k, ?_⟩
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hkH
  haveI : IsMulCommutative A := hAab
  letI : CommGroup ↥A' := { (inferInstance : Group ↥A') with
    mul_comm := fun u v => Subtype.ext (setLike_mul_comm (hA'A u.2) (hA'A v.2)) }
  haveI : Group.FG ↥A' := hfg
  exact CommGroup.finite_of_fg_isMulTorsion ↥A' htor

theorem ft8_3_comm {H : Type*} [Group H] {p : ℕ} (hp : p.Prime)
    (hpodd : Odd p) {A : Subgroup H} (hAab : IsMulCommutative A) (hAp : IsPGroup p A)
    (hAn : A.Normal) {y : H} (hyp : y ^ p = 1)
    (hyC : y ∈ Subgroup.centralizer ((Work.PGroup.omega p 1 A : Subgroup H) : Set H)) :
    ⁅A, Subgroup.zpowers y⁆ ≤ Work.PGroup.omega p 1 A := by
  have hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A := fun a ha => hAn.conj_mem a ha y
  have hyΩ : ∀ ω ∈ Work.PGroup.omega p 1 A, y * ω = ω * y := fun ω hω =>
    (Subgroup.mem_centralizer_iff.mp hyC ω hω).symm
  rw [Subgroup.commutator_le]
  intro a ha z hz
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  obtain ⟨A', haA', hA'A, hA'fin, hA'inv⟩ := ft8_3_orbit_finite hp hAab hAp hyA hyp ha
  haveI : Finite ↥A' := hA'fin
  have hA'ab : IsMulCommutative ↥A' := by
    haveI : IsMulCommutative A := hAab
    exact isMulCommutative_anti hA'A
  have hA'p : IsPGroup p ↥A' := by
    intro x
    obtain ⟨k, hk⟩ := hAp ⟨(x : H), hA'A x.2⟩
    have hkH : ((x : H)) ^ p ^ k = 1 := by
      have h1 := congrArg (fun z : ↥A => (z : H)) hk
      simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h1
    refine ⟨k, ?_⟩
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hkH
  have hyC' : y ∈ Subgroup.centralizer ((Work.PGroup.omega p 1 A' : Subgroup H) : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro ω hω
    rw [Work.PGroup.omega_one_eq_omega1] at hω
    have h1 : ω ∈ Work.PGroup.omega1 H p A := Work.PGroup.omega1_mono hA'A hω
    rw [← Work.PGroup.omega_one_eq_omega1] at h1
    exact Subgroup.mem_centralizer_iff.mp hyC ω h1
  have hmain : ⁅A', Subgroup.zpowers y⁆ ≤ Work.PGroup.omega p 1 A' :=
    ft8_3_finite hp hpodd hA'ab hA'p hA'inv hyp hyC'
  have hcomm : ⁅a, y⁆ ∈ Work.PGroup.omega p 1 A :=
    Work.PGroup.omega_mono hA'A (Subgroup.commutator_le.mp hmain a haA' y (Subgroup.mem_zpowers y))
  exact commutator_zpow_mem (Ω := Work.PGroup.omega p 1 A) hyΩ hcomm j

end Work.LocalPrelim
