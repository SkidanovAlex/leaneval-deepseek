import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.D17Defs
import Submission.Work.BMAX.LayerCentralizesFitting
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le
import Submission.Work.BMAX.pCoreIn_eq_bot_iff_not_mem_primesOf
import Submission.Work.BMAX.fittingPiIn_le_iSup_pCoreIn
import Submission.OddOrder.Isaacs.Ch04_Commutators.Main

namespace Work.BMAX

open Subgroup

/-! ## 0. The single-prime case of the key input

Thompson's `P × K` lemma (Bender 1970, 1.1; Isaacs 4.31) applied with the `p`-group
`N_N(X)` playing the role of `P`: since `N_N(X) ≤ C_G(K)`, the `p`-group `N_N(X)` and the
`p'`-group `K` commute, and `K` fixes the `N_N(X)`-fixed points of `N` (an element of `N`
centralizing `N_N(X)` lies in `N_N(X)`, because `X ≤ N_N(X)`). -/
theorem commutator_eq_bot_of_isPGroup_of_centralizer_normalizer {G : Type*} [Group G] [Finite G]
    {N K X : Subgroup G} {r q : ℕ} [Fact r.Prime] [Fact q.Prime]
    (hrq : r ≠ q) (hNr : IsPGroup r ↥N) (hKq : IsPGroup q ↥K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G))
    (hX : X ≤ N)
    (hcent : N ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.centralizer (K : Set G)) :
    ⁅K, N⁆ = ⊥ := by
  classical
  set Y : Subgroup G := N ⊓ Subgroup.normalizer (X : Set G) with hYdef
  have hYN : Y ≤ N := inf_le_left
  have hYX : X ≤ Y := le_inf hX Subgroup.le_normalizer
  have hYK : Y ≤ Subgroup.centralizer (K : Set G) := hcent
  have hYr : IsPGroup r ↥Y := IsPGroup.to_le hNr hYN
  set H : Subgroup G := N ⊔ K with hHdef
  have hNH : N ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_right
  have hYH : Y ≤ H := le_trans hYN hNH
  have hHnorm : H ≤ Subgroup.normalizer (N : Set G) :=
    sup_le Subgroup.le_normalizer hKN
  have hNn : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHnorm
  haveI := hNn
  -- the multiplication homomorphism `Y × K →* H`
  let mult : ↥Y × ↥K →* ↥H :=
    { toFun := fun x => ⟨(x.1 : G) * (x.2 : G), H.mul_mem (hYH x.1.2) (hKH x.2.2)⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
             ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G))
        have hcomm : (y.1 : G) * (x.2 : G) = (x.2 : G) * (y.1 : G) :=
          (Subgroup.mem_centralizer_iff.mp (hYK y.1.2) (x.2 : G) x.2.2).symm
        calc ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G))
            = (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by group
          _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by rw [hcomm]
          _ = ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)) := by group }
  have hmult_left : ∀ x : ↥Y, mult (x, 1) = (⟨(x : G), hYH x.2⟩ : ↥H) := by
    intro x; ext; show (x : G) * 1 = (x : G); simp
  have hmult_right : ∀ y : ↥K, mult (1, y) = (⟨(y : G), hKH y.2⟩ : ↥H) := by
    intro y; ext; show (1 : G) * (y : G) = (y : G); simp
  let φ : ↥Y × ↥K →* MulAut ↥(N.subgroupOf H) := MulAut.conjNormal.comp mult
  have hNr' : IsPGroup r ↥(N.subgroupOf H) :=
    IsPGroup.of_equiv hNr (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hKc : ¬ r ∣ Nat.card ↥K := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hKq
    rw [hk]
    intro hdiv
    exact hrq ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime r) (Fact.out : Nat.Prime q)).mp
      ((Fact.out : Nat.Prime r).dvd_of_dvd_pow hdiv))
  -- the fixed-point hypothesis of Isaacs 4.31
  have hφ_apply : ∀ (x : ↥Y) (y : ↥K), φ (x, y) = MulAut.conjNormal (mult (x, y)) :=
    fun x y => rfl
  have hfix : ∀ g : ↥(N.subgroupOf H),
      (∀ x : ↥Y, (φ (x, 1)) g = g) → ∀ y : ↥K, (φ (1, y)) g = g := by
    intro g hg y
    -- `g` commutes with `Y`
    have hcommY : ∀ x ∈ Y, ((g : ↥H) : G) * (x : G) = (x : G) * ((g : ↥H) : G) := by
      intro x hx
      have h := hg ⟨x, hx⟩
      rw [hφ_apply, hmult_left ⟨x, hx⟩] at h
      have h2 := congrArg (fun z : ↥(N.subgroupOf H) => ((z : ↥H) : G)) h
      rw [MulAut.conjNormal_apply] at h2
      have h3 : (x : G) * ((g : ↥H) : G) * (x : G)⁻¹ = ((g : ↥H) : G) := h2
      calc ((g : ↥H) : G) * (x : G) = ((x : G) * ((g : ↥H) : G) * (x : G)⁻¹) * (x : G) := by
            rw [h3]
        _ = (x : G) * ((g : ↥H) : G) := by group
    -- `g ∈ Y`
    have hgN : ((g : ↥H) : G) ∈ N := Subgroup.mem_subgroupOf.mp g.2
    have heqX : ∀ x ∈ X, ((g : ↥H) : G) * x * ((g : ↥H) : G)⁻¹ = x := by
      intro x hx
      have hcomm := hcommY x (hYX hx)
      calc ((g : ↥H) : G) * x * ((g : ↥H) : G)⁻¹
          = (x * ((g : ↥H) : G)) * ((g : ↥H) : G)⁻¹ := by rw [hcomm]
        _ = x := by group
    have hgY : ((g : ↥H) : G) ∈ Y := by
      refine Subgroup.mem_inf.mpr ⟨hgN, ?_⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [heqX x hx]
        exact hx
      · intro hx
        have hy : ((g : ↥H) : G) * x * ((g : ↥H) : G)⁻¹ ∈ Y := hYX hx
        have hcomm := hcommY _ hy
        have h' : ((g : ↥H) : G) * (((g : ↥H) : G) * x * ((g : ↥H) : G)⁻¹) =
            (((g : ↥H) : G) * x * ((g : ↥H) : G)⁻¹) * ((g : ↥H) : G) := hcomm
        have h'' : (((g : ↥H) : G) * x * ((g : ↥H) : G)⁻¹) * ((g : ↥H) : G) =
            ((g : ↥H) : G) * x := by group
        have h''' : ((g : ↥H) : G) * (((g : ↥H) : G) * x * ((g : ↥H) : G)⁻¹) =
            ((g : ↥H) : G) * x := by rw [h', h'']
        rw [← mul_left_cancel h''']
        exact hx
    -- so `g` centralizes `K`
    have hgK : ∀ y' ∈ K, (y' : G) * ((g : ↥H) : G) = ((g : ↥H) : G) * y' :=
      fun y' hy' => Subgroup.mem_centralizer_iff.mp (hYK hgY) y' hy'
    -- conclude
    rw [hφ_apply, hmult_right y]
    have h2 := hgK (y : G) y.2
    apply Subtype.ext
    apply Subtype.ext
    show (y : G) * ((g : ↥H) : G) * (y : G)⁻¹ = ((g : ↥H) : G)
    rw [h2]
    group
  have hmain := OddOrder.Isaacs.Ch04.isaacs_thm_4_31_external φ hNr' hYr hKc hfix
  have htriv := (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially _).mp hmain
  -- convert `K` acting trivially on `N` into `⁅K, N⁆ = ⊥`
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hpt : (φ (1, (⟨k, hk⟩ : ↥K))) (⟨⟨n, hNH hn⟩, hn⟩ : ↥(N.subgroupOf H)) =
      (⟨⟨n, hNH hn⟩, hn⟩ : ↥(N.subgroupOf H)) :=
    htriv ⟨k, hk⟩ (⟨⟨n, hNH hn⟩, hn⟩ : ↥(N.subgroupOf H))
  rw [hφ_apply, hmult_right ⟨k, hk⟩] at hpt
  have h2 := congrArg (fun z : ↥(N.subgroupOf H) => ((z : ↥H) : G)) hpt
  rw [MulAut.conjNormal_apply] at h2
  have h3 : k * n * k⁻¹ = n := h2
  calc n * k = (k * n * k⁻¹) * k := by rw [h3]
    _ = k * n := by group

/-! ## 0a. Nilpotent groups: unique, characteristic Sylow subgroups -/

/-- Sylow subgroups of a finite nilpotent group are unique. -/
theorem subsingleton_sylow_of_isNilpotent {H : Type*} [Group H] [Finite H]
    [Group.IsNilpotent H] {p : ℕ} [Fact p.Prime] : Subsingleton (Sylow p H) := by
  haveI : Unique (Sylow p H) :=
    Sylow.unique_of_normal (default : Sylow p H) inferInstance
  exact inferInstance

/-- Sylow subgroups of a finite nilpotent group are characteristic. -/
theorem characteristic_sylow_of_isNilpotent {H : Type*} [Group H] [Finite H]
    [Group.IsNilpotent H] {p : ℕ} [Fact p.Prime] (S : Sylow p H) :
    ((S : Subgroup H)).Characteristic := by
  haveI : Subsingleton (Sylow p H) := subsingleton_sylow_of_isNilpotent
  exact Sylow.characteristic_of_subsingleton S

/-- A subgroup normalising `N` normalises every subgroup of `↥N` that is characteristic in
`↥N` (pulled back to `G`). -/
theorem le_normalizer_of_characteristic {G : Type*} [Group G] {N P S : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hSN : S ≤ N)
    (hchar : (S.subgroupOf N).Characteristic) : P ≤ Subgroup.normalizer (S : Set G) := by
  -- conjugation by any `g ∈ P` preserves `S`, because it induces an automorphism of `↥N`
  have key : ∀ g ∈ P, Subgroup.map (MulAut.conj g).toMonoidHom S ≤ S := by
    intro g hg x hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hconj : ∀ z : ↥N, g * (z : G) * g⁻¹ ∈ N := fun z =>
      (Subgroup.mem_normalizer_iff.mp (hPN hg) (z : G)).mp z.2
    have hconj' : ∀ z : ↥N, g⁻¹ * (z : G) * g ∈ N := fun z =>
      (Subgroup.mem_normalizer_iff''.mp (hPN hg) (z : G)).mp z.2
    let φ : ↥N ≃* ↥N :=
      { toFun := fun z => ⟨g * (z : G) * g⁻¹, hconj z⟩
        invFun := fun z => ⟨g⁻¹ * (z : G) * g, hconj' z⟩
        left_inv := fun z => by ext; simp only [mul_inv_rev, inv_inv]; group
        right_inv := fun z => by ext; simp only [mul_inv_rev, inv_inv]; group
        map_mul' := fun z w => by ext; simp only [Subgroup.coe_mul]; group }
    have hmap : Subgroup.map φ.toMonoidHom (S.subgroupOf N) = S.subgroupOf N :=
      (Subgroup.characteristic_iff_map_eq).mp hchar φ
    have hy' : φ ⟨y, hSN hy⟩ ∈ S.subgroupOf N := by
      rw [← hmap]
      exact Subgroup.mem_map.mpr ⟨⟨y, hSN hy⟩, hy, rfl⟩
    have hval : ((φ ⟨y, hSN hy⟩ : ↥N) : G) = g * y * g⁻¹ := by
      simp only [φ, MulEquiv.coe_mk, Equiv.coe_fn_mk]
    have hyS : g * y * g⁻¹ ∈ S := by
      rw [← hval]
      exact Subgroup.mem_subgroupOf.mp hy'
    have hyx' : g * y * g⁻¹ = x := by
      rw [← MulAut.conj_apply g y]
      exact hyx
    rwa [← hyx']
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key p hp (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro hx
    have h1 := key p⁻¹ (P.inv_mem hp) (Subgroup.mem_map.mpr ⟨p * x * p⁻¹, hx, rfl⟩)
    have h1' : p⁻¹ * (p * x * p⁻¹) * p ∈ S := by
      have h1c := h1
      rw [show (MulEquiv.toMonoidHom (MulAut.conj p⁻¹)) (p * x * p⁻¹)
        = (MulAut.conj p⁻¹) (p * x * p⁻¹) from rfl] at h1c
      rw [MulAut.conj_apply] at h1c
      simpa only [inv_inv] using h1c
    have h2 : p⁻¹ * (p * x * p⁻¹) * p = x := by group
    rwa [h2] at h1'

/-! ## 0b. The primary decomposition of a subgroup of a nilpotent group -/

/-- Every subgroup of a finite nilpotent group generates (as a join) its intersections with the
Sylow subgroups.

This is the decomposition `X = ⨆_p (X ⊓ R_p)` used to reduce the general case to the
prime-power case.  Its proof applies the Sylow decomposition of the nilpotent group `↥X` and
the uniqueness of the Sylow subgroups of `↥N`. -/
theorem eq_iSup_inf_sylow_of_isNilpotent {G : Type*} [Group G] [Finite G] {N X : Subgroup G}
    (hNnil : Group.IsNilpotent ↥N) (hX : X ≤ N) :
    X = ⨆ (p : (Nat.card ↥X).primeFactors),
      (X ⊓ (((default : Sylow (p : ℕ) ↥N) : Subgroup ↥N).map N.subtype)) := by
  classical
  haveI : Group.IsNilpotent ↥(X.subgroupOf N) := Subgroup.isNilpotent (X.subgroupOf N)
  haveI hXnil : Group.IsNilpotent ↥X :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hX)).mp inferInstance
  refine le_antisymm ?_ (iSup_le fun p => inf_le_left)
  have htop : (⊤ : Subgroup ↥X) = ⨆ (p : (Nat.card ↥X).primeFactors),
      ((default : Sylow (p : ℕ) ↥X) : Subgroup ↥X) :=
    (OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥X).symm
  have hmap : ((⊤ : Subgroup ↥X).map X.subtype) = X := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  calc X = ((⊤ : Subgroup ↥X).map X.subtype) := hmap.symm
    _ = (⨆ (p : (Nat.card ↥X).primeFactors),
          ((default : Sylow (p : ℕ) ↥X) : Subgroup ↥X)).map X.subtype := by rw [htop]
    _ = ⨆ (p : (Nat.card ↥X).primeFactors),
          (((default : Sylow (p : ℕ) ↥X) : Subgroup ↥X).map X.subtype) :=
        Subgroup.map_iSup X.subtype _
    _ ≤ ⨆ (p : (Nat.card ↥X).primeFactors),
          (X ⊓ (((default : Sylow (p : ℕ) ↥N) : Subgroup ↥N).map N.subtype)) := by
        refine iSup_le fun p => ?_
        haveI : Fact (Nat.Prime (p : ℕ)) := ⟨Nat.prime_of_mem_primeFactors p.2⟩
        haveI : Group.IsNilpotent ↥N := hNnil
        haveI : Subsingleton (Sylow (p : ℕ) ↥N) := subsingleton_sylow_of_isNilpotent
        refine le_iSup_of_le p ?_
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
        have hSX : ((default : Sylow (p : ℕ) ↥X) : Subgroup ↥X).map (Subgroup.inclusion hX) ≤
            ((default : Sylow (p : ℕ) ↥N) : Subgroup ↥N) := by
          have hisp : IsPGroup (p : ℕ)
              ↥(((default : Sylow (p : ℕ) ↥X) : Subgroup ↥X).map (Subgroup.inclusion hX)) :=
            IsPGroup.map (default : Sylow (p : ℕ) ↥X).isPGroup' (Subgroup.inclusion hX)
          obtain ⟨Q, hQ⟩ := hisp.exists_le_sylow
          rwa [Subsingleton.elim Q (default : Sylow (p : ℕ) ↥N)] at hQ
        exact Subgroup.mem_map.mpr
          ⟨⟨y, hX y.2⟩, hSX (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩), rfl⟩

/-! ## 0c. The descent step

The `p`-primary part of a nilpotent group `N` normalises a subgroup `X ≤ N` as soon as it
normalises the `p`-primary part `X ⊓ N_p` of `X`:  for `r ≠ p` the Sylow subgroups `N_p` and
`N_r` of the nilpotent group `N` commute (they are normal and of coprime order), so `N_p`
centralises `X ⊓ N_r`, and `X` is the join of the `X ⊓ N_r`. -/
theorem inf_normalizer_sylow_le {G : Type*} [Group G] [Finite G]
    {N X : Subgroup G} (hNnil : Group.IsNilpotent ↥N) (hX : X ≤ N) {p : ℕ} [Fact p.Prime] :
    ((default : Sylow p ↥N) : Subgroup ↥N).map N.subtype ⊓
        Subgroup.normalizer
          ((X ⊓ ((default : Sylow p ↥N) : Subgroup ↥N).map N.subtype : Subgroup G) : Set G)
      ≤ N ⊓ Subgroup.normalizer (X : Set G) := by
  classical
  haveI := hNnil
  set Rp : Subgroup G := ((default : Sylow p ↥N) : Subgroup ↥N).map N.subtype with hRp
  have hRpN : Rp ≤ N := Subgroup.map_subtype_le _
  -- the `r`-primary pieces of `X` with `r ≠ p` are centralised by the `p`-primary part
  have hcent : ∀ (g : G), g ∈ Rp → ∀ (r : (Nat.card ↥X).primeFactors), (r : ℕ) ≠ p →
      ∀ z ∈ (X ⊓ (((default : Sylow (r : ℕ) ↥N)) : Subgroup ↥N).map N.subtype : Subgroup G),
        g * z = z * g := by
    intro g hgR r hrne z hz
    haveI : Fact (Nat.Prime (r : ℕ)) := ⟨Nat.prime_of_mem_primeFactors r.2⟩
    rw [hRp] at hgR
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hgR
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hz).2
    have hSp : (((default : Sylow p ↥N)) : Subgroup ↥N).Normal :=
      OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent _
    have hSr : (((default : Sylow (r : ℕ) ↥N)) : Subgroup ↥N).Normal :=
      OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent _
    have hdisj : Disjoint (((default : Sylow p ↥N)) : Subgroup ↥N)
        (((default : Sylow (r : ℕ) ↥N)) : Subgroup ↥N) :=
      IsPGroup.disjoint_of_ne p (r : ℕ) (Ne.symm hrne) _ _
        (default : Sylow p ↥N).isPGroup' (default : Sylow (r : ℕ) ↥N).isPGroup'
    have hcab := Subgroup.commute_of_normal_of_disjoint _ _ hSp hSr hdisj a b ha hb
    show N.subtype a * N.subtype b = N.subtype b * N.subtype a
    rw [← map_mul, ← map_mul, hcab.eq]
  -- main computation
  have key : ∀ (g : G), g ∈ Rp →
      g ∈ Subgroup.normalizer ((X ⊓ Rp : Subgroup G) : Set G) →
      ∀ z ∈ X, g * z * g⁻¹ ∈ X := by
    intro g hgR hgN z hz
    rw [eq_iSup_inf_sylow_of_isNilpotent hNnil hX] at hz
    refine Subgroup.iSup_induction (fun r : (Nat.card ↥X).primeFactors =>
        (X ⊓ (((default : Sylow (r : ℕ) ↥N)) : Subgroup ↥N).map N.subtype))
      (C := fun z => g * z * g⁻¹ ∈ X) hz ?_ ?_ ?_
    · intro r w hw
      by_cases hr : (r : ℕ) = p
      · have hr_eq : r = ⟨p, hr ▸ r.2⟩ := Subtype.ext hr
        rw [hr_eq] at hw
        exact (Subgroup.mem_inf.mp ((Subgroup.mem_normalizer_iff.mp hgN w).mp hw)).1
      · have hgw : g * w * g⁻¹ = w := by
          rw [hcent g hgR r hr w hw]; group
        rw [hgw]; exact (Subgroup.mem_inf.mp hw).1
    · simp
    · intro x y hx hy
      have hxy : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [hxy]; exact Subgroup.mul_mem _ hx hy
  intro y hy
  obtain ⟨hyR, hyN⟩ := Subgroup.mem_inf.mp hy
  refine Subgroup.mem_inf.mpr ⟨hRpN hyR, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact key y hyR hyN x hx
  · intro hx
    have h1 : y⁻¹ ∈ Rp := Rp.inv_mem hyR
    have h2 : y⁻¹ ∈ Subgroup.normalizer ((X ⊓ Rp : Subgroup G) : Set G) :=
      (Subgroup.normalizer _).inv_mem hyN
    have h3 := key y⁻¹ h1 h2 (y * x * y⁻¹) hx
    rwa [show y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ = x from by group] at h3

/-! ## 0'. The key group-theoretic input

`P` (a `q`-group with `q ∤ |N|`) acts coprimely on the nilpotent subgroup `N`; if some subgroup
`X ≤ N` has its `N`-normalizer fixed by `P`, then `P` centralizes `N`.

Since `N` is nilpotent it is the join of its Sylow subgroups `N_r`; the previous descent step
shows that `N_r ⊓ N_G(X ⊓ N_r) ≤ N ⊓ N_G(X) ≤ C_G(P)`, so the single-prime case applies to
each `N_r`. -/
theorem commutator_eq_bot_of_normalizer_le_centralizer {G : Type*} [Group G] [Finite G]
    {N P X : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hNnil : Group.IsNilpotent ↥N)
    (hPN : P ≤ Subgroup.normalizer (N : Set G))
    (hPq : IsPGroup q ↥P)
    (hqN : ¬ q ∣ Nat.card ↥N)
    (hX : X ≤ N)
    (hcent : N ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.centralizer (P : Set G)) :
    ⁅P, N⁆ = ⊥ := by
  classical
  haveI := hNnil
  -- `N` is the join of its Sylow subgroups
  have hNdec : N = ⨆ (r : (Nat.card ↥N).primeFactors),
      (((default : Sylow (r : ℕ) ↥N)) : Subgroup ↥N).map N.subtype := by
    have h1 : (⊤ : Subgroup ↥N) = ⨆ (r : (Nat.card ↥N).primeFactors),
        ((default : Sylow (r : ℕ) ↥N) : Subgroup ↥N) :=
      (OddOrder.Isaacs.Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥N).symm
    calc N = (⊤ : Subgroup ↥N).map N.subtype := by
            rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = (⨆ (r : (Nat.card ↥N).primeFactors),
            ((default : Sylow (r : ℕ) ↥N) : Subgroup ↥N)).map N.subtype := by rw [h1]
      _ = ⨆ (r : (Nat.card ↥N).primeFactors),
            (((default : Sylow (r : ℕ) ↥N)) : Subgroup ↥N).map N.subtype :=
            Subgroup.map_iSup N.subtype _
  -- every Sylow component lies in the centraliser of `P`
  have hRc : ∀ r : (Nat.card ↥N).primeFactors,
      (((default : Sylow (r : ℕ) ↥N)) : Subgroup ↥N).map N.subtype ≤
        Subgroup.centralizer (P : Set G) := by
    intro r
    haveI : Fact (Nat.Prime (r : ℕ)) := ⟨Nat.prime_of_mem_primeFactors r.2⟩
    set S : Subgroup ↥N := ((default : Sylow (r : ℕ) ↥N) : Subgroup ↥N) with hS
    -- `P` normalises `S.map N.subtype`
    have hPnorm : P ≤ Subgroup.normalizer ((S.map N.subtype : Subgroup G) : Set G) := by
      have hsub : (S.map N.subtype).subgroupOf N = S := by
        ext x
        rw [Subgroup.mem_subgroupOf]
        constructor
        · intro hx
          obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp hx
          have hx'x : x' = x := Subtype.ext hxx'
          rwa [hx'x] at hx'
        · intro hx
          exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      exact le_normalizer_of_characteristic hPN (Subgroup.map_subtype_le S)
        (hsub.symm ▸ characteristic_sylow_of_isNilpotent (default : Sylow (r : ℕ) ↥N))
    -- `(r : ℕ) ≠ q`
    have hrq : (r : ℕ) ≠ q := by
      intro h
      exact hqN (h ▸ (Nat.mem_primeFactors.mp r.2).2.1)
    have hNr : IsPGroup (r : ℕ) ↥(S.map N.subtype) :=
      IsPGroup.map (default : Sylow (r : ℕ) ↥N).isPGroup' N.subtype
    have hbot : ⁅P, S.map N.subtype⁆ = ⊥ :=
      commutator_eq_bot_of_isPGroup_of_centralizer_normalizer (X := X ⊓ S.map N.subtype)
        hrq hNr hPq hPnorm inf_le_right
        (le_trans (inf_normalizer_sylow_le hNnil hX (p := (r : ℕ))) hcent)
    have hPc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hPc hw) z hz).symm
  rw [Subgroup.commutator_comm P N, Subgroup.commutator_eq_bot_iff_le_centralizer]
  rw [hNdec]
  exact iSup_le hRc

/-! ## 1. The stated lemma -/

theorem commutator_pCoreIn_inf_fittingIn_eq_bot {G : Type} [Group G] [Finite G]
    (hG : IsSimpleGroup G) {A B X : Subgroup G} (hA : IsCoatom A) (hB : B ≠ ⊤)
    (hA_D : Work.GW2.IsDGroup A) (hX : X ≤ Work.GW2.fittingIn A)
    (hSB : Subgroup.normalizer (X : Set G) ⊓ Work.GW2.fstarIn A ≤ B)
    (hSl : Work.GW2.layerIn A ≤ Subgroup.normalizer (X : Set G))
    {q : ℕ} (hq : q.Prime) (hqpi : q ∉ Work.GW2.primesOf (Work.GW2.fittingIn A)) :
    ⁅Work.GW2.pCoreIn q B ⊓ A, Work.GW2.fittingIn A⁆ = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- `q ∤ |F(A)|`
  have hqndvd : ¬ q ∣ Nat.card ↥(Work.GW2.fittingIn A) := fun hd =>
    hqpi (Nat.mem_primeFactors.mpr ⟨hq, hd, Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩⟩)
  -- `O_q(B)` is a `q`-group
  have hpqB : IsPGroup q ↥(Work.GW2.pCoreIn q B) := by
    rw [Work.GW2.pCoreIn]
    exact IsPGroup.map (Work.BMAX.PiPart.pCore_isPGroup (M := ↥B) (p := q)) B.subtype
  -- so is `P := O_q(B) ⊓ A`
  have hPq : IsPGroup q ↥(Work.GW2.pCoreIn q B ⊓ A) := IsPGroup.to_le hpqB inf_le_left
  -- `P ≤ N_G(F(A))`
  have hPN : (Work.GW2.pCoreIn q B ⊓ A) ≤
      Subgroup.normalizer (Work.GW2.fittingIn A : Set G) :=
    le_trans inf_le_right (le_normalizer_fittingIn A)
  -- `B` normalizes `O_q(B)`
  have hBnQ : B ≤ Subgroup.normalizer ((Work.GW2.pCoreIn q B : Subgroup G) : Set G) := by
    rw [Work.GW2.pCoreIn]
    exact le_normalizer_map_subtype_of_normal (Work.GW2.pCore_normal q ↥B)
  -- the core computation: `P` centralizes `F(A) ⊓ N_G(X)`
  have hcent : Work.GW2.fittingIn A ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.centralizer ((Work.GW2.pCoreIn q B ⊓ A : Subgroup G) : Set G) := by
    refine (Subgroup.commutator_eq_bot_iff_le_centralizer).mp ?_
    set Y : Subgroup G := Work.GW2.fittingIn A ⊓ Subgroup.normalizer (X : Set G) with hY
    -- `Y ≤ B`
    have hYB : Y ≤ B :=
      le_trans (le_inf inf_le_right (le_trans inf_le_left (Work.GW2.fittingIn_le_fstarIn A))) hSB
    -- `⁅Y, O_q(B)⁆ ≤ O_q(B)`
    have h1 : ⁅Y, Work.GW2.pCoreIn q B⁆ ≤ Work.GW2.pCoreIn q B :=
      (Subgroup.le_normalizer_iff_commutator_le_right).mp (le_trans hYB hBnQ)
    -- `⁅Y, A⁆ ≤ F(A)`
    have h2 : ⁅Y, A⁆ ≤ Work.GW2.fittingIn A :=
      le_trans (Subgroup.commutator_mono inf_le_left le_rfl)
        ((Subgroup.le_normalizer_iff_commutator_le_left).mp (le_normalizer_fittingIn A))
    -- hence `⁅Y, P⁆ ≤ O_q(B) ⊓ F(A) = ⊥`
    have h3 : ⁅Y, Work.GW2.pCoreIn q B ⊓ A⁆ ≤
        Work.GW2.pCoreIn q B ⊓ Work.GW2.fittingIn A :=
      le_inf (le_trans (Subgroup.commutator_mono le_rfl inf_le_left) h1)
        (le_trans (Subgroup.commutator_mono le_rfl inf_le_right) h2)
    have h4 : Work.GW2.pCoreIn q B ⊓ Work.GW2.fittingIn A = ⊥ := by
      have hqT : IsPGroup q ↥(Work.GW2.pCoreIn q B ⊓ Work.GW2.fittingIn A) :=
        IsPGroup.to_le hpqB inf_le_left
      have hdvd : Nat.card ↥(Work.GW2.pCoreIn q B ⊓ Work.GW2.fittingIn A) ∣
          Nat.card ↥(Work.GW2.fittingIn A) := Subgroup.card_dvd_of_le inf_le_right
      rcases hqT.card_eq_or_dvd with h1 | h1
      · exact Subgroup.card_eq_one.mp h1
      · exact absurd (h1.trans hdvd) hqndvd
    exact le_bot_iff.mp (le_trans h3 (le_of_eq h4))
  exact commutator_eq_bot_of_normalizer_le_centralizer (isNilpotent_fittingIn A) hPN hPq
    hqndvd hX hcent

end Work.BMAX
