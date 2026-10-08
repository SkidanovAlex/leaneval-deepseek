import Mathlib
import Submission.Work.DSTR.D110iDefs
import Submission.Work.L2F.Defs
import Submission.Work.CORE2A.card_PGL2_eq_two_mul_card_PSL2
import Submission.Work.DSTR.L2CentAux.PGLInvCard
import Submission.Work.DSTR.L2CentAux.PSLOddNormalizerCard
import Submission.Work.DSTR.L2CentAux.PSLPSubgroupNormalizerDvd

namespace Work.DSTR

open scoped MatrixGroups

/-! ## Transport of `CentInvariant` along a group isomorphism -/


/-! ## Bridging lemmas: images of centralizers and normalizers -/

/-- The image under an injective homomorphism of the centralizer of `a` is the centralizer of the
image of `a`, intersected with the range. -/
lemma map_centralizer_singleton {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (a : A) :
    (Subgroup.centralizer ({a} : Set A)).map f =
      Subgroup.centralizer ({(f a)} : Set B) ⊓ f.range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    rw [← map_mul, ← map_mul, hy']
  · rintro ⟨hx, hyr⟩
    obtain ⟨y, rfl⟩ := hyr
    refine ⟨y, ?_, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [← map_mul, ← map_mul] at hx'
    exact hf hx'

/-- The image under an injective homomorphism of the normalizer of `P` is the normalizer of the
image of `P`, intersected with the range. -/
lemma map_normalizer {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (P : Subgroup A) :
    (Subgroup.normalizer (P : Set A)).map f =
      Subgroup.normalizer ((P.map f) : Set B) ⊓ f.range := by
  have key : ∀ y : A, f y ∈ P.map f ↔ y ∈ P := by
    intro y
    constructor
    · rintro ⟨w, hw, hwy⟩
      rwa [hf hwy] at hw
    · intro hy
      exact ⟨y, hy, rfl⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩
    refine Subgroup.mem_normalizer_iff.mpr ?_
    have hy' := Subgroup.mem_normalizer_iff.mp hy
    intro z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
      rw [show f y * f w * (f y)⁻¹ = f (y * w * y⁻¹) by simp]
      exact Subgroup.mem_map.mpr ⟨y * w * y⁻¹, (hy' w).mp hw, rfl⟩
    · intro hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
      have h2 : y⁻¹ * w * y ∈ P := by
        refine (hy' (y⁻¹ * w * y)).mpr ?_
        rw [show y * (y⁻¹ * w * y) * y⁻¹ = w from by group]
        exact hw
      have hz' : z = f (y⁻¹ * w * y) := by
        rw [show f (y⁻¹ * w * y) = (f y)⁻¹ * f w * f y by simp, hwz]
        group
      rw [hz']
      exact Subgroup.mem_map.mpr ⟨y⁻¹ * w * y, h2, rfl⟩
  · rintro ⟨hx, hyr⟩
    obtain ⟨y, rfl⟩ := hyr
    refine ⟨y, ?_, rfl⟩
    refine Subgroup.mem_normalizer_iff.mpr ?_
    have hx' := Subgroup.mem_normalizer_iff.mp hx
    intro w
    constructor
    · intro hw
      have h2 : f (y * w * y⁻¹) ∈ P.map f := by
        rw [show f (y * w * y⁻¹) = f y * f w * (f y)⁻¹ by simp]
        exact (hx' (f w)).mp (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)
      obtain ⟨v, hv, hv2⟩ := Subgroup.mem_map.mp h2
      have hv' : v = y * w * y⁻¹ := hf hv2
      rw [hv'] at hv
      exact hv
    · intro hw
      have h2 : f (y * w * y⁻¹) ∈ P.map f := Subgroup.mem_map.mpr ⟨y * w * y⁻¹, hw, rfl⟩
      have h3 := (hx' (f w)).mpr (by
        rw [← show f (y * w * y⁻¹) = f y * f w * (f y)⁻¹ by simp]
        exact h2)
      obtain ⟨v, hv, hv2⟩ := Subgroup.mem_map.mp h3
      have hv' : v = w := hf hv2
      rw [hv'] at hv
      exact hv

/-- The centralizer in a subgroup `H` of an element `t ∈ H` is the intersection with `H` of the
centralizer in the ambient group. -/
lemma subgroupOf_centralizer_singleton {G : Type*} [Group G] (H : Subgroup G) (t : H) :
    (Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf H =
      Subgroup.centralizer ({t} : Set H) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- The normalizer in a subgroup `H` of `P ≤ H` is the intersection with `H` of the normalizer in
the ambient group. -/
lemma subgroupOf_normalizer {G : Type*} [Group G] (H : Subgroup G) (P : Subgroup G)
    (hPH : P ≤ H) :
    (Subgroup.normalizer (P : Set G)).subgroupOf H =
      Subgroup.normalizer ((P.subgroupOf H) : Set H) := by
  ext x
  constructor
  · intro hx
    have hx' : ∀ h : G, h ∈ P ↔ (x : G) * h * (x : G)⁻¹ ∈ P :=
      Subgroup.mem_normalizer_iff.mp (Subgroup.mem_subgroupOf.mp hx)
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hx' (y : G)
  · intro hx
    have hx' : ∀ y : ↥H, y ∈ P.subgroupOf H ↔ x * y * x⁻¹ ∈ P.subgroupOf H :=
      Subgroup.mem_normalizer_iff.mp hx
    refine Subgroup.mem_subgroupOf.mpr ?_
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro h
    constructor
    · intro hh
      have h2 : (⟨h, hPH hh⟩ : ↥H) ∈ P.subgroupOf H := hh
      have h3 := (hx' ⟨h, hPH hh⟩).mp h2
      rw [Subgroup.mem_subgroupOf] at h3
      exact h3
    · intro hh
      have hmem : h ∈ H := by
        have h1 : h = (x : G)⁻¹ * ((x : G) * h * (x : G)⁻¹) * (x : G) := by group
        rw [h1]
        exact H.mul_mem (H.mul_mem (H.inv_mem x.2) (hPH hh)) x.2
      have h2 : x * (⟨h, hmem⟩ : ↥H) * x⁻¹ ∈ P.subgroupOf H := by
        show ((x : G) * h * (x : G)⁻¹) ∈ P
        exact hh
      exact (hx' ⟨h, hmem⟩).mpr h2

/-- An odd-order subgroup of a finite group is contained in every subgroup of index two. -/
lemma le_of_index_two_of_odd_card {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hM : M.index = 2) {K : Subgroup G} (hK : Odd (Nat.card K)) : K ≤ M := by
  haveI : M.Normal := Subgroup.normal_of_index_eq_two hM
  have hdvd : Nat.card (K.map (QuotientGroup.mk' M)) ∣ Nat.card K :=
    Subgroup.card_map_dvd K (QuotientGroup.mk' M)
  have hdvd2 : Nat.card (K.map (QuotientGroup.mk' M)) ∣ 2 := by
    have h : Nat.card (K.map (QuotientGroup.mk' M)) ∣ Nat.card (G ⧸ M) :=
      Subgroup.card_subgroup_dvd_card _
    rwa [← Subgroup.index_eq_card, hM] at h
  have hbot : K.map (QuotientGroup.mk' M) = ⊥ := by
    rw [Subgroup.eq_bot_iff_card]
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact h
    · rw [h] at hdvd
      obtain ⟨m, hm⟩ := hK
      omega
  have hker : K ≤ (QuotientGroup.mk' M).ker := (Subgroup.map_eq_bot_iff K).mp hbot
  intro x hx
  have hx' : (QuotientGroup.mk' M) x = 1 := MonoidHom.mem_ker.mp (hker hx)
  exact (QuotientGroup.eq_one_iff x).mp hx'

/-- `CentInvariant` transports forward along a group isomorphism. -/
private theorem centInvariant_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CentInvariant A) : CentInvariant B := by
  intro t ht p _ hp2 P hP hC
  -- the centralizer of `t` in `B` is the image of the centralizer of `e.symm t` in `A`
  have key : ∀ x : B, x ∈ Subgroup.centralizer ({t} : Set B) ↔
      e.symm x ∈ Subgroup.centralizer ({e.symm t} : Set A) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have := congrArg e.symm hx
      simpa using this
    · intro hx
      have := congrArg e hx
      simpa using this
  -- `z ∈ P.map e.symm ↔ e z ∈ P`
  have map_key : ∀ z : A, z ∈ P.map (e.symm : B →* A) ↔ e z ∈ P := by
    intro z
    constructor
    · rintro ⟨y, hy, hyz⟩
      rw [← hyz]
      simpa using hy
    · intro hz
      exact ⟨e z, hz, by simp⟩
  -- likewise for the normalizer of `P` and of `P.map e.symm`
  have keyN : ∀ x : B, x ∈ Subgroup.normalizer (P : Set B) ↔
      e.symm x ∈ Subgroup.normalizer ((P.map (e.symm : B →* A)) : Set A) := by
    intro x
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hx z
      rw [map_key z, map_key (e.symm x * z * (e.symm x)⁻¹),
        show e (e.symm x * z * (e.symm x)⁻¹) = x * e z * x⁻¹ by simp]
      exact hx (e z)
    · intro hx y
      constructor
      · intro hy
        have h2 : e.symm y ∈ P.map (e.symm : B →* A) :=
          (map_key (e.symm y)).mpr (by simpa using hy)
        have h3 := (hx (e.symm y)).mp h2
        rwa [map_key (e.symm x * e.symm y * (e.symm x)⁻¹),
          show e (e.symm x * e.symm y * (e.symm x)⁻¹) = x * y * x⁻¹ by simp] at h3
      · intro hy
        have h3 : e.symm x * e.symm y * (e.symm x)⁻¹ ∈ P.map (e.symm : B →* A) := by
          rw [map_key]
          simpa using hy
        have h4 := (hx (e.symm y)).mpr h3
        rw [map_key (e.symm y)] at h4
        simpa using h4
  have ht' : orderOf (e.symm t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ht
  have hP' : IsPGroup p (P.map (e.symm : B →* A)) :=
    hP.of_equiv (Subgroup.equivMapOfInjective P (e.symm : B →* A) e.symm.injective)
  have hC' : Subgroup.centralizer ({e.symm t} : Set A) ≤
      Subgroup.normalizer ((P.map (e.symm : B →* A)) : Set A) := by
    intro x hx
    have h1 : e x ∈ Subgroup.normalizer (P : Set B) :=
      hC ((key (e x)).mpr (by simpa using hx))
    have h2 := (keyN (e x)).mp h1
    simpa using h2
  have hres := h (e.symm t) ht' p hp2 (P.map (e.symm : B →* A)) hP' hC'
  intro y hy
  exact (key y).mpr (hres ((map_key (e.symm y)).mpr (by simpa using hy)))

/-- `CentInvariant` only depends on the isomorphism class of the group: the notions of
`orderOf`, `IsPGroup`, `centralizer` and `normalizer` are all preserved by a group isomorphism. -/
theorem centInvariant_congr {Q₁ Q₂ : Type*} [Group Q₁] [Group Q₂] (e : Q₁ ≃* Q₂) :
    CentInvariant Q₁ ↔ CentInvariant Q₂ :=
  ⟨fun h1 => centInvariant_of_equiv e h1, fun h2 => centInvariant_of_equiv e.symm h2⟩


/-! ## Arithmetic facts -/

lemma not_dvd_sub_one_mul_div_half {q : ℕ} (hq : Odd q) (hq5 : 5 ≤ q) :
    ¬ (q - 1) ∣ q * (q - 1) / 2 := by
  obtain ⟨a, ha⟩ := hq
  have hq1 : q - 1 = 2 * a := by omega
  have heven : ∃ k, q * (q - 1) = 2 * k := by
    refine ⟨a * q, ?_⟩
    rw [hq1, mul_comm q (2 * a), mul_assoc, mul_comm a q]
  obtain ⟨k, hk⟩ := heven
  have h2 : 2 * (q * (q - 1) / 2) = q * (q - 1) := by omega
  intro h
  obtain ⟨j, hj⟩ := h
  have hj2 : q * (q - 1) = 2 * ((q - 1) * j) := by rw [← h2, hj]
  have hk2 : k = (q - 1) * j :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : (0:ℕ) < 2) (by rw [← hk, hj2])
  have hkq : 2 * k = 2 * (a * q) := by
    rw [← hk, hq1]
    ring
  have hk' : k = a * q := Nat.eq_of_mul_eq_mul_left (by norm_num : (0:ℕ) < 2) hkq
  have ha0 : 0 < a := by omega
  have h3 : a * q = a * (2 * j) := by
    calc a * q = k := hk'.symm
      _ = (q - 1) * j := hk2
      _ = 2 * a * j := by rw [hq1]
      _ = a * (2 * j) := by ring
  have h4 : q = 2 * j := Nat.eq_of_mul_eq_mul_left ha0 h3
  omega

lemma not_dvd_add_one_mul_div_half {q : ℕ} (hq : Odd q) (hq5 : 5 ≤ q) :
    ¬ (q + 1) ∣ q * (q - 1) / 2 := by
  obtain ⟨a, ha⟩ := hq
  have heven : ∃ k, q * (q - 1) = 2 * k := by
    refine ⟨a * q, ?_⟩
    have h1 : q - 1 = 2 * a := by omega
    rw [h1, mul_comm q (2 * a), mul_assoc, mul_comm a q]
  obtain ⟨k, hk⟩ := heven
  have h2 : 2 * (q * (q - 1) / 2) = q * (q - 1) := by omega
  intro h
  obtain ⟨j, hj⟩ := h
  have h3 : q * (q - 1) = 2 * ((q + 1) * j) := by rw [← h2, hj]
  have h4 : (q + 1) ∣ q * (q - 1) := ⟨2 * j, by rw [h3]; ring⟩
  have h5 : (q + 1) ∣ q * (q + 1) := ⟨q, by ring⟩
  have h7 : (q + 1) ∣ q * (q + 1) - q * (q - 1) := Nat.dvd_sub h5 h4
  have h9 : q * (q + 1) = q * (q - 1) + 2 * q := by
    have h10 : q + 1 = (q - 1) + 2 := by omega
    rw [h10, mul_add]
    ring
  have h8 : q * (q + 1) - q * (q - 1) = 2 * q := by omega
  rw [h8] at h7
  have h11 : (q + 1) ∣ 2 * (q + 1) := ⟨2, by ring⟩
  have h13 : (q + 1) ∣ 2 * (q + 1) - 2 * q := Nat.dvd_sub h11 h7
  have h14 : 2 * (q + 1) - 2 * q = 2 := by omega
  rw [h14] at h13
  have h15 : q + 1 ≤ 2 := Nat.le_of_dvd (by norm_num) h13
  omega

lemma not_dvd_sub_one_add_one {q : ℕ} (hq : 5 ≤ q) : ¬ (q - 1) ∣ (q + 1) := by
  intro h
  have h2 : (q - 1) ∣ (q + 1) - (q - 1) := Nat.dvd_sub h (dvd_refl (q - 1))
  have h3 : q + 1 - (q - 1) = 2 := by omega
  rw [h3] at h2
  have h4 : q - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  omega

lemma not_dvd_add_one_sub_one {q : ℕ} (hq : 5 ≤ q) : ¬ (q + 1) ∣ (q - 1) := by
  intro h
  have h4 : q + 1 ≤ q - 1 := Nat.le_of_dvd (by omega) h
  omega

/-- A subgroup has cardinality dividing the cardinality of any larger subgroup. -/
lemma card_dvd_card_of_le {G : Type*} [Group G] [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H ∣ Nat.card K := by
  have h1 : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have h2 := Subgroup.index_mul_card (H.subgroupOf K)
  rw [h1] at h2
  exact ⟨(H.subgroupOf K).index, by rw [mul_comm (Nat.card H)]; exact h2.symm⟩

/-- An odd prime power is odd. -/
lemma odd_pow_of_odd {r n : ℕ} (hr : Odd r) : Odd (r ^ n) := hr.pow

lemma ne_zero_of_five_le {p k : ℕ} (hk : 5 ≤ p ^ k) : k ≠ 0 := by
  rintro rfl
  simp at hk

/-! ## The `PGL(2,q)` case -/

open Matrix in
theorem centInvariant_PGL_aux {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k)
    (hCard : 2 * Nat.card (PSL(2, GaloisField p k)) = Nat.card (PGL(2, GaloisField p k)))
    (hl2 : Work.L2F.L2CentInvariantProp)
    (hInvCard : ∀ t : PGL(2, GaloisField p k), orderOf t = 2 →
      Nat.card (Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k)))) = 2 * (p ^ k - 1) ∨
      Nat.card (Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k)))) = 2 * (p ^ k + 1))
    (hOddNorm : ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 → r ≠ p →
      ∀ P : Subgroup (PSL(2, GaloisField p k)), IsPGroup r P → P ≠ ⊥ →
      Nat.card (Subgroup.normalizer (P : Set (PSL(2, GaloisField p k)))) = p ^ k - 1 ∨
      Nat.card (Subgroup.normalizer (P : Set (PSL(2, GaloisField p k)))) = p ^ k + 1)
    (hPDvd : ∀ P : Subgroup (PSL(2, GaloisField p k)), IsPGroup p P → P ≠ ⊥ →
      Nat.card (Subgroup.normalizer (P : Set (PSL(2, GaloisField p k)))) ∣
        p ^ k * (p ^ k - 1) / 2) :
    CentInvariant (PGL(2, GaloisField p k)) := by
  intro t ht r _ hr2 P hP hC
  have hq5 : 5 ≤ p ^ k := hk
  have hqodd : Odd (p ^ k) := hp.pow
  haveI : Finite (GaloisField p k) := inferInstance
  haveI : Finite (PGL(2, GaloisField p k)) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk (n := Fin 2) (R := GaloisField p k))
      Matrix.ProjGenLinGroup.mk_surjective
  set π : PSL(2, GaloisField p k) →* PGL(2, GaloisField p k) :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL with hπdef
  have hinj : Function.Injective π := by
    rw [hπdef]
    exact Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  -- the index of the image of `PSL` in `PGL`
  have hLcard : Nat.card (π.range) = Nat.card (PSL(2, GaloisField p k)) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hLindex : π.range.index = 2 := by
    have h := Subgroup.card_mul_index π.range
    rw [hLcard, ← hCard] at h
    have h2 : Nat.card (PSL(2, GaloisField p k)) * π.range.index =
        Nat.card (PSL(2, GaloisField p k)) * 2 := by
      rw [mul_comm 2 (Nat.card (PSL(2, GaloisField p k)))] at h
      exact h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
  -- odd order subgroups lie in the image of `PSL`
  have hPL : P ≤ π.range := le_of_index_two_of_odd_card hLindex (by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    rw [hn]
    exact (Fact.out : r.Prime).odd_of_ne_two hr2 |>.pow)
  rcases eq_or_ne P ⊥ with hbot | hne
  · rw [hbot]
    exact bot_le
  by_cases htL : t ∈ π.range
  · -- ## Case `t ∈ PSL`
    have hpsl : CentInvariant (PSL(2, GaloisField p k)) := by
      intro t' ht' s _ hs2 P' hP' hC'
      exact hl2 p k hp hk t' ht' s hs2 P' hP' hC'
    have hCentL : CentInvariant (π.range) :=
      (centInvariant_congr (MonoidHom.ofInjective hinj)).mp hpsl
    set tL : (π.range) := ⟨t, htL⟩ with htLdef
    have htL2 : orderOf tL = 2 := by
      rw [htLdef, Subgroup.orderOf_mk, ht]
    have hPLgrp : IsPGroup r (P.subgroupOf π.range) :=
      IsPGroup.of_equiv hP (Subgroup.subgroupOfEquivOfLe hPL).symm
    have hCL : Subgroup.centralizer ({tL} : Set (π.range)) ≤
        Subgroup.normalizer ((P.subgroupOf π.range) : Set (π.range)) := by
      rw [← subgroupOf_centralizer_singleton π.range tL, ← subgroupOf_normalizer π.range P hPL]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hC (Subgroup.mem_subgroupOf.mp hx))
    have hres := hCentL tL htL2 r hr2 (P.subgroupOf π.range) hPLgrp hCL
    intro y hy
    have hy' : (⟨y, hPL hy⟩ : (π.range)) ∈ P.subgroupOf π.range := hy
    have hmem : (⟨y, hPL hy⟩ : (π.range)) ∈
        (Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k)))).subgroupOf π.range := by
      rw [subgroupOf_centralizer_singleton π.range tL]
      exact hres hy'
    exact Subgroup.mem_subgroupOf.mp hmem
  · -- ## Case `t ∉ PSL`
    haveI : π.range.Normal := Subgroup.normal_of_index_eq_two hLindex
    -- the index of `C(t) ∩ L` in `C(t)` is two
    have hrelC : π.range.relIndex (Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k)))) = 2 := by
      have hdvd : π.range.relIndex (Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k)))) ∣ 2 := by
        have h := Subgroup.relIndex_dvd_index_of_normal
          (H := π.range) (K := Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ⊔ π.range)
        rw [hLindex, Subgroup.relIndex_sup_right] at h
        exact h
      have hne1 : π.range.relIndex (Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k)))) ≠ 1 := by
        intro h1
        have hle : Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ≤ π.range :=
          Subgroup.relIndex_eq_one.mp h1
        exact htL (hle (by rw [Subgroup.mem_centralizer_singleton_iff]))
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    -- `|C(t) ∩ L| = q - 1` or `q + 1`
    have hcardCL : Nat.card ↥(Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ⊓ π.range)
        = p ^ k - 1 ∨
        Nat.card ↥(Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ⊓ π.range)
          = p ^ k + 1 := by
      have h := Subgroup.relIndex_mul_card
        (H := π.range) (K := Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))))
      rw [hrelC] at h
      rcases hInvCard t ht with hc | hc
      · left
        have h2 : 2 * Nat.card ↥(Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ⊓ π.range)
            = 2 * (p ^ k - 1) := by rw [inf_comm, h, hc]
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
      · right
        have h2 : 2 * Nat.card ↥(Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ⊓ π.range)
            = 2 * (p ^ k + 1) := by rw [inf_comm, h, hc]
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
    -- pull `P` back to `PSL`
    set P₁ : Subgroup (PSL(2, GaloisField p k)) := P.comap π with hP₁def
    have hP₁map : P₁.map π = P := by
      rw [hP₁def, Subgroup.map_comap_eq]
      rw [inf_comm]
      exact inf_eq_left.mpr hPL
    have hP₁ne : P₁ ≠ ⊥ := by
      intro h
      exact hne (by rw [← hP₁map, h, Subgroup.map_bot])
    have hdvdN : Nat.card ↥(Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ⊓ π.range) ∣
        Nat.card ↥(Subgroup.normalizer (P : Set (PGL(2, GaloisField p k))) ⊓ π.range) :=
      card_dvd_card_of_le (fun x hx => ⟨hC hx.1, hx.2⟩)
    -- the cardinality of `N(P) ∩ L` is the normalizer cardinality in `PSL`
    have hNcard : Nat.card (Subgroup.normalizer (P₁ : Set (PSL(2, GaloisField p k)))) =
        Nat.card ↥(Subgroup.normalizer (P : Set (PGL(2, GaloisField p k))) ⊓ π.range) := by
      have e := Subgroup.equivMapOfInjective
        (Subgroup.normalizer (P₁ : Set (PSL(2, GaloisField p k)))) π hinj
      have h1 : Nat.card (Subgroup.normalizer (P₁ : Set (PSL(2, GaloisField p k)))) =
          Nat.card ((Subgroup.normalizer (P₁ : Set (PSL(2, GaloisField p k)))).map π) :=
        Nat.card_congr e.toEquiv
      rw [h1, map_normalizer π hinj P₁, hP₁map]
    have hP₁r : IsPGroup r P₁ := IsPGroup.comap_of_injective hP π hinj
    rcases eq_or_ne r p with hrp | hrp
    · -- ## the case `r = p`
      have hP₁p : IsPGroup p P₁ := hrp ▸ hP₁r
      have hdvd := hPDvd P₁ hP₁p hP₁ne
      rw [hNcard] at hdvd
      have hdvd2 := dvd_trans hdvdN hdvd
      rcases hcardCL with hc | hc <;> rw [hc] at hdvd2
      · exact absurd hdvd2 (not_dvd_sub_one_mul_div_half hqodd hq5)
      · exact absurd hdvd2 (not_dvd_add_one_mul_div_half hqodd hq5)
    · -- ## the case `r ≠ p`
      have hN := hOddNorm r hr2 hrp P₁ hP₁r hP₁ne
      rw [hNcard] at hN
      rcases hN with hN | hN <;> rcases hcardCL with hc | hc <;> rw [hc] at hdvdN
      · -- `q - 1 ∣ q - 1`
        have hl : Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ⊓ π.range ≤
            Subgroup.normalizer (P : Set (PGL(2, GaloisField p k))) ⊓ π.range :=
          fun x hx => ⟨hC hx.1, hx.2⟩
        have hcard : Nat.card ↥(Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ⊓ π.range)
            = Nat.card ↥(Subgroup.normalizer (P : Set (PGL(2, GaloisField p k))) ⊓ π.range) := by
          rw [hc, hN]
        have heq : Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ⊓ π.range =
            Subgroup.normalizer (P : Set (PGL(2, GaloisField p k))) ⊓ π.range :=
          Subgroup.eq_of_le_of_card_ge hl (le_of_eq hcard.symm)
        intro y hy
        have hy' : y ∈ Subgroup.normalizer (P : Set (PGL(2, GaloisField p k))) ⊓ π.range :=
          ⟨Subgroup.le_normalizer hy, hPL hy⟩
        rw [← heq] at hy'
        exact hy'.1
      · -- `q + 1 ∣ q - 1` : contradiction
        rw [hN] at hdvdN
        exact absurd hdvdN (not_dvd_add_one_sub_one hq5)
      · -- `q - 1 ∣ q + 1` : contradiction
        rw [hN] at hdvdN
        exact absurd hdvdN (not_dvd_sub_one_add_one hq5)
      · -- `q + 1 ∣ q + 1`
        have hl : Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ⊓ π.range ≤
            Subgroup.normalizer (P : Set (PGL(2, GaloisField p k))) ⊓ π.range :=
          fun x hx => ⟨hC hx.1, hx.2⟩
        have hcard : Nat.card ↥(Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ⊓ π.range)
            = Nat.card ↥(Subgroup.normalizer (P : Set (PGL(2, GaloisField p k))) ⊓ π.range) := by
          rw [hc, hN]
        have heq : Subgroup.centralizer ({t} : Set (PGL(2, GaloisField p k))) ⊓ π.range =
            Subgroup.normalizer (P : Set (PGL(2, GaloisField p k))) ⊓ π.range :=
          Subgroup.eq_of_le_of_card_ge hl (le_of_eq hcard.symm)
        intro y hy
        have hy' : y ∈ Subgroup.normalizer (P : Set (PGL(2, GaloisField p k))) ⊓ π.range :=
          ⟨Subgroup.le_normalizer hy, hPL hy⟩
        rw [← heq] at hy'
        exact hy'.1

theorem L2CentInvariant (hl2 : Work.L2F.L2CentInvariantProp) (Q : Type*) [Group Q] [Finite Q]
    (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k)
    (h : Nonempty (Q ≃* PSL(2, GaloisField p k)) ∨ Nonempty (Q ≃* PGL(2, GaloisField p k))) :
    Work.DSTR.CentInvariant Q := by
  have hpsl : CentInvariant (PSL(2, GaloisField p k)) := by
    intro t ht r _ hr2 P hP hC
    exact hl2 p k hp hk t ht r hr2 P hP hC
  have hpgl : CentInvariant (PGL(2, GaloisField p k)) :=
    centInvariant_PGL_aux hp hk
      (Work.CORE2A.card_PGL2_eq_two_mul_card_PSL2 hp (ne_zero_of_five_le hk)).symm hl2
      (fun t ht => L2CentAux.PGLInvCard hp hk t ht)
      (fun r _ hr2 hrp P hP hne => L2CentAux.PSLOddNormalizerCard hp hk r hr2 hrp P hP hne)
      (fun P hP hne => L2CentAux.PSLPSubgroupNormalizerDvd hp hk P hP hne)
  rcases h with h | h
  · obtain ⟨e⟩ := h
    exact (centInvariant_congr e.symm).mp hpsl
  · obtain ⟨e⟩ := h
    exact (centInvariant_congr e.symm).mp hpgl

end Work.DSTR
