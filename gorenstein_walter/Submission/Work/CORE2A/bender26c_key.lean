import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.normalizer_eq_of_coatom
import Submission.Work.CORE2A.sylow_two_not_isCyclic
import Submission.Work.CORE2A.isFourGroup_closure_pair
import Submission.Work.CORE2A.exists_conj_mem_sylow

/-!
# CORE2A: the key construction of Bender 1981, Theorem 2.6, step 3 (`bender26c_key`)

Target: `Work.CORE2A.bender26c_key`, the construction on Bender 1981 pp. 220–221 consumed by
`Work.CORE2A.thm26c_of_key`.

The route (Bender p. 221):

1. `P = [t,P]` (Bender 1.1(i) plus minimality of `P`): `b26c_commutator_eq`;
2. for a maximal subgroup `M ⊇ N_G(P)` (`H = C_G(t) ≤ N_G(P) ≤ M`, so `t ∈ M`), `Lemma 2.1`
   (`h21`) says `M` has more than one class of involutions, so there is a four-group `V ≤ S`
   with `t ∈ V` and `N_G(V) ⊄ M`: `b26c_fourGroup`;
3. Bender 1.1(iii) applied to `V` acting on `P` yields `s ∈ V#`, `s ≠ t`, with
   `C_P(s) ≄ C_P(t)`: `b26c_fourGroup_element`;
4. inside `N_G(V)/(N_G(V) ∩ M)` the stabilizer of `t` has index `3` and equals
   `N_G(V) ∩ M`, so the conjugating element mapping `t` to `s` can be chosen outside `M`:
   `b26c_conj_notMem`;
5. Bender 1.10(i) applied to `M` (a D-group) with `P = [t,P]` gives `P ≤ O_p(M)`; with
   `P₁ := [t, C_P(s)]` one gets `P₁ ≤ O_p(M) ≤ F(M)` and `P^g ≤ O_p(M^g)`;
6. the remaining steps of Bender's argument (p. 221, ll. 20–30 of the printed page) are
   **open**; they produce a maximal subgroup `M' ⊇ N_G(P₁)` with `P^g ≤ M'`, prove `M' = M^g`
   with Lemmas 2.3/2.4 (`h23`, `h24`) and hence `N_G(P₁) ∩ F*(M) ≤ M^g = M^g`.

Steps 1, 2 (Lemma 2.1), 3 (1.1(iii)) and Bender 1.10(i) are proved below (as
`b26c_commutator_eq`, `b26c_fourGroup`, `b26c_fourGroup_element`,
`b26c_commutator_le_pCoreIn`).  What is *not* yet available is the ingredient on Bender p. 221
line 20, "`P₁` centralizes `P^g`" (`P₁ := [t,C_P(s)]`, `s = t^g`) together with its consequence
`N_G(P₁) ∩ F*(M) ≤ M^g`.  Note `P = ⨆_{h ∈ H} P₁^h` (this follows from the minimality of `P`
and 1.1(iii)), so the needed statement is a genuine structural assertion about the minimal
counterexample, not a formal triviality.

The statement of `bender26c_key` is kept verbatim (it is the interface of
`Work.CORE2A.thm26c_of_key`).
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-! ## 0. Elementary facts about `BenderSetup` (copied from the Bender-2.6 context) -/

theorem b26c_card_S0_ge_two {G : Type} [Group G] [Finite G] {B : Work.GW2.BenderSetup G} :
    2 ≤ Nat.card B.S0 := by
  have hle : Subgroup.zpowers B.t ≤ B.S0 := Subgroup.zpowers_le.mpr B.t_mem
  have hcard : Nat.card ↥(Subgroup.zpowers B.t) ≤ Nat.card ↥B.S0 :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have h2 : Nat.card ↥(Subgroup.zpowers B.t) = 2 := by rw [Nat.card_zpowers, B.t_order]
  omega

theorem b26c_card_S_ge_four {G : Type} [Group G] [Finite G] {B : Work.GW2.BenderSetup G} :
    4 ≤ Nat.card (B.S : Subgroup G) := by
  have h := bSetup_card_S_eq B
  have h0 := b26c_card_S0_ge_two (B := B)
  omega

theorem b26c_exists_dihedral {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
  have h2 : 2 ≤ Nat.card (B.S : Subgroup G) := by have := b26c_card_S_ge_four (B := B); omega
  rcases hctx.sylow B.S with hcyc | ⟨n, hn⟩
  · exact absurd hcyc (sylow_two_not_isCyclic hctx.simple hctx.nonab B.S h2)
  · obtain ⟨e⟩ := hn
    have hcard : Nat.card (B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have h4 := b26c_card_S_ge_four (B := B)
    exact ⟨n, by omega, ⟨e⟩⟩

theorem b26c_no_index_two {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  haveI : IsSimpleGroup G := hctx.simple
  intro N hN h2
  haveI : N.Normal := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · rw [hbot, Subgroup.index_bot] at h2
    obtain ⟨a, b, hab⟩ := hctx.nonab
    refine hab ?_
    have hall : ∀ x : G, x * x = 1 := fun x => by
      have h : orderOf x ∣ 2 := h2 ▸ orderOf_dvd_natCard x
      have h1 := orderOf_dvd_iff_pow_eq_one.mp h
      simpa [pow_two] using h1
    have hinv : ∀ x : G, x⁻¹ = x := fun x => inv_eq_iff_mul_eq_one.mpr (hall x)
    calc a * b = (a * b)⁻¹⁻¹ := by simp
      _ = (b⁻¹ * a⁻¹)⁻¹ := by rw [mul_inv_rev]
      _ = (b * a)⁻¹ := by rw [hinv a, hinv b]
      _ = b * a := hinv (b * a)
  · rw [htop, Subgroup.index_top] at h2
    exact absurd h2 (by norm_num)

/-! ## 1. `P = [t,P]` -/

/-- **Bender p. 221**: `P = ⁅⟨t⟩,P⁆`.

`C := ⁅⟨t⟩,P⁆` is an `H`-invariant p-subgroup of `P` (`H ≤ N_G(P)` and `t ∈ H`).  Bender
1.1(i) (`T.c11i`) gives `⁅⟨t⟩,C⁆ = C`; if `C < P`, minimality of `P` puts `C` inside
`C_G(t)`, so `⁅⟨t⟩,C⁆ = ⊥` and `C = ⊥`, i.e. `t` centralizes `P` — contradicting `hnot`. -/
theorem b26c_commutator_eq {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (B : Work.GW2.BenderSetup G) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G)
    (hP : IsPGroup p P) (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (hmin : ∀ Q : Subgroup G, Q < P → IsPGroup p Q → B.H ≤ Subgroup.normalizer (Q : Set G) →
      Q ≤ Subgroup.centralizer ({B.t} : Set G))
    (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G)) :
    ⁅Subgroup.zpowers B.t, P⁆ = P := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := ⁅Subgroup.zpowers B.t, P⁆ with hCdef
  have htH : B.t ∈ B.H := bSetup_t_mem_H B
  have hzt : Subgroup.zpowers B.t ≤ B.H := Subgroup.zpowers_le.mpr htH
  have hzN : Subgroup.zpowers B.t ≤ Subgroup.normalizer (P : Set G) := le_trans hzt hHN
  have hCP : C ≤ P := Subgroup.le_normalizer_iff_commutator_le_right.mp hzN
  -- `H` normalizes `C`
  have hCZt : B.H ≤ Subgroup.normalizer (Subgroup.zpowers B.t : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh z hz
    rw [Subgroup.mem_zpowers_iff] at hz ⊢
    obtain ⟨n, rfl⟩ := hz
    refine ⟨n, ?_⟩
    have hc : Commute B.t h := (Subgroup.mem_centralizer_iff.mp hh) B.t (by simp)
    rw [← (Commute.zpow_left hc n).eq]
    group
  have hCH : B.H ≤ Subgroup.normalizer (C : Set G) := by
    intro h hh
    have h1 : h ∈ Subgroup.normalizer (Subgroup.zpowers B.t : Set G) := hCZt hh
    have h2 : h ∈ Subgroup.normalizer (P : Set G) := hHN hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [hCdef, Subgroup.map_commutator, h1, h2]
  -- Bender 1.1(i) for the 2-group `⟨t⟩` acting on the odd p-group `P`
  have hcop : Nat.Coprime 2 (Nat.card P) := by
    rw [Nat.prime_two.coprime_iff_not_dvd]
    intro hdiv
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    rw [hk] at hdiv
    have h2p : 2 = p :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow hdiv)
    exact hp2 h2p.symm
  have hc11 : ⁅Subgroup.zpowers B.t, C⁆ = C :=
    (T.c11i G 2 (Subgroup.zpowers B.t) P
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, B.t_order, pow_one])) hcop hzN).1
  by_contra hne
  have hlt : C < P := lt_of_le_of_ne hCP hne
  have hCp : IsPGroup p C := hP.to_le hCP
  have hcenC : C ≤ Subgroup.centralizer ({B.t} : Set G) := hmin C hlt hCp hCH
  have hbot : ⁅Subgroup.zpowers B.t, C⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact ((Subgroup.mem_centralizer_iff.mp (hcenC hc)) B.t (Set.mem_singleton B.t)).symm
  rw [hc11] at hbot
  rw [hCdef] at hbot
  have hcenP : B.t ∈ Subgroup.centralizer (P : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) (Subgroup.mem_zpowers B.t)
  exact hnot fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ((Subgroup.mem_centralizer_iff.mp hcenP) x hx).symm

/-! ## 1b. Bender 1.10(i) in the coatom `M ⊇ N_G(P)` -/

/-- **Bender 1.10(i), p. 221**: `⁅⟨t⟩,P⁆ ≤ O_p(M)` for a coatom `M ⊇ N_G(P)`.

`M` is a proper subgroup of `G`, hence a D-group (`hctx.ih` + `dihOrCycSylow_subgroup`), and
`t ∈ N_G(P) ≤ M` centralizes `C_M(t) = H ∩ M ≤ H ≤ N_G(P)`.  So Bender 1.10(i) applies to `M`
with the involution `t` and the p-subgroup `P ≤ M`. -/
theorem b26c_commutator_le_pCoreIn {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (hFT : Work.GW2.FeitThompsonProp) (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G) (hP : IsPGroup p P)
    (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (M : Subgroup G) (hM : IsCoatom M) (hNPM : Subgroup.normalizer (P : Set G) ≤ M) :
    ⁅Subgroup.zpowers B.t, P⁆ ≤ Work.GW2.pCoreIn p M := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have htN : B.t ∈ Subgroup.normalizer (P : Set G) := hHN (bSetup_t_mem_H B)
  have htM : B.t ∈ M := hNPM htN
  have hPM : P ≤ M := le_trans Subgroup.le_normalizer hNPM
  set t' : ↥M := ⟨B.t, htM⟩ with ht'def
  have ht'2 : orderOf t' = 2 := by
    rw [ht'def, Subgroup.orderOf_mk]
    exact B.t_order
  have hP' : IsPGroup p (P.subgroupOf M) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  have hcen : Subgroup.centralizer ({t'} : Set ↥M) ≤
      Subgroup.normalizer (P.subgroupOf M : Set ↥M) := by
    intro x hx
    -- `(x : G)` commutes with `t`, hence lies in `H ≤ N_G(P)`
    have hxG : (x : G) ∈ Subgroup.centralizer ({B.t} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 : t' * x = x * t' := (Subgroup.mem_centralizer_iff.mp hx) t' (by simp)
      have h2 := congrArg (Subtype.val) h1
      simp only [Subgroup.coe_mul] at h2
      rw [ht'def] at h2
      simpa using h2
    have hxN : (x : G) ∈ Subgroup.normalizer (P : Set G) := hHN hxG
    rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact (hxN (y : G)).mp hy
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact (hxN (y : G)).mpr hy
  have hD : DihOrCycSylow ↥M := dihOrCycSylow_subgroup hctx.sylow M
  have hlt : Nat.card ↥M < Nat.card G := card_lt_card_of_ne_top hM.ne_top
  have hDG : IsDGroup ↥M := hctx.ih ↥M hlt hD
  have h := T.d110i ↥M hFT hD hDG t' ht'2 p hp2 (P.subgroupOf M) hP' hcen
  have hmap := Subgroup.map_mono (f := M.subtype) h
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPM,
    MonoidHom.map_zpowers] at hmap
  rw [commutator_comm]
  simpa [Work.GW2.pCoreIn, ht'def] using hmap

/-! ## 2. The four-group `V ∋ t` with `N_G(V) ⊄ M` -/

/-- **Bender p. 221 (Lemma 2.1)**: for a maximal subgroup `M ⊇ H = C_G(t)` which does not have a
single class of involutions, there is a four-group `V ≤ S`, `t ∈ V`, with `N_G(V) ⊄ M`. -/
theorem b26c_fourGroup {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (hFT : Work.GW2.FeitThompsonProp) (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) (hM : IsCoatom M) (hHM : B.H ≤ M) (h2 : ¬ Work.GW2.OneInvClassIn M) :
    ∃ V : Subgroup G, B.t ∈ V ∧ V ≤ (B.S : Subgroup G) ∧ Work.GW2.IsFourGroup V ∧
      ¬ Subgroup.normalizer (V : Set G) ≤ M := by
  classical
  by_contra hcon
  have hcon' : ∀ V : Subgroup G, B.t ∈ V → V ≤ (B.S : Subgroup G) → Work.GW2.IsFourGroup V →
      Subgroup.normalizer (V : Set G) ≤ M := by
    intro V htV hVS hV
    by_contra hVn
    exact hcon ⟨V, htV, hVS, hV, hVn⟩
  apply h2
  have hSleH : (B.S : Subgroup G) ≤ B.H := bSetup_S_le_H B
  have hSleM : (B.S : Subgroup G) ≤ M := le_trans hSleH hHM
  obtain ⟨n, hn2, hiso⟩ := b26c_exists_dihedral hctx B
  have hno12 := b26c_no_index_two hctx
  obtain ⟨_hallconj, htrans⟩ := T.fus G B.S n hn2 hiso hno12
  -- every involution of `S` is `M`-conjugate to `t`
  have hS_conj : ∀ u : G, u ∈ (B.S : Subgroup G) → orderOf u = 2 →
      ∃ m ∈ M, m * u * m⁻¹ = B.t := by
    intro u huS hu2
    by_cases hu0 : u ∈ B.S0
    · refine ⟨1, M.one_mem, ?_⟩
      haveI : IsCyclic ↥B.S0 := B.S0_cyclic
      have h1 : orderOf (⟨u, hu0⟩ : ↥B.S0) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
      have h2t : orderOf (⟨B.t, B.t_mem⟩ : ↥B.S0) = 2 := by
        rw [Subgroup.orderOf_mk]; exact B.t_order
      have hueqt : u = B.t := congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic h1 h2t)
      simp [hueqt]
    · have hu1 : u ≠ 1 := by
        intro h; exact hu0 (by rw [h]; exact B.S0.one_mem)
      have ht1 : B.t ≠ 1 := bSetup_t_ne_one B
      have htu : B.t ≠ u := fun h => hu0 (h ▸ B.t_mem)
      have ht2 : B.t ^ 2 = 1 := by simpa [B.t_order] using pow_orderOf_eq_one B.t
      have hu2' : u ^ 2 = 1 := by simpa [hu2] using pow_orderOf_eq_one u
      have hcomm : B.t * u = u * B.t :=
        (Subgroup.mem_centralizer_iff.mp (hSleH huS)) B.t (by simp)
      have hV4 : Work.GW2.IsFourGroup (Subgroup.closure ({B.t, u} : Set G)) :=
        isFourGroup_closure_pair ht2 hu2' hcomm ht1 hu1 htu
      have htmem : B.t ∈ Subgroup.closure ({B.t, u} : Set G) :=
        Subgroup.subset_closure (by simp)
      have hVS : Subgroup.closure ({B.t, u} : Set G) ≤ (B.S : Subgroup G) := by
        rw [Subgroup.closure_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact bSetup_t_mem_S B
        · exact huS
      have hNle := hcon' _ htmem hVS hV4
      obtain ⟨g, hg, hgconj⟩ :=
        htrans _ hV4 B.t (Subgroup.subset_closure (by simp))
          u (Subgroup.subset_closure (by simp)) ht1 hu1
      exact ⟨g⁻¹, M.inv_mem (hNle hg), by rw [inv_inv, ← hgconj]; group⟩
  -- every involution of `M` is `M`-conjugate into `S`
  have hmove : ∀ z : G, z ∈ M → orderOf z = 2 →
      ∃ m ∈ M, m * z * m⁻¹ ∈ (B.S : Subgroup G) := by
    intro z hzM hz2
    have hzp : IsPGroup 2 ↥(Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
    exact exists_conj_mem_sylow 2 B.S hSleM hzM hzp
  intro x hx y hy
  obtain ⟨hxM, hx2⟩ := hx
  obtain ⟨hyM, hy2⟩ := hy
  obtain ⟨m1, hm1M, hm1S⟩ := hmove x hxM hx2
  have hm1ord : orderOf (m1 * x * m1⁻¹) = 2 := by
    have hsemi : SemiconjBy m1 x (m1 * x * m1⁻¹) := by simp [SemiconjBy, mul_assoc]
    exact (SemiconjBy.orderOf_eq m1 hsemi).symm.trans hx2
  obtain ⟨m2, hm2M, hm2t⟩ := hS_conj (m1 * x * m1⁻¹) hm1S hm1ord
  obtain ⟨n1, hn1M, hn1S⟩ := hmove y hyM hy2
  have hn1ord : orderOf (n1 * y * n1⁻¹) = 2 := by
    have hsemi : SemiconjBy n1 y (n1 * y * n1⁻¹) := by simp [SemiconjBy, mul_assoc]
    exact (SemiconjBy.orderOf_eq n1 hsemi).symm.trans hy2
  obtain ⟨n2, hn2M, hn2t⟩ := hS_conj (n1 * y * n1⁻¹) hn1S hn1ord
  refine ⟨(n2 * n1)⁻¹ * (m2 * m1),
    M.mul_mem (M.inv_mem (M.mul_mem hn2M hn1M)) (M.mul_mem hm2M hm1M), ?_⟩
  have hx_eq : x = (m2 * m1)⁻¹ * B.t * (m2 * m1) := by
    have h : (m2 * m1) * x * (m2 * m1)⁻¹ = B.t := by
      rw [show (m2 * m1) * x * (m2 * m1)⁻¹ = m2 * (m1 * x * m1⁻¹) * m2⁻¹ from by group]
      exact hm2t
    rw [← h]; group
  have hy_eq : y = (n2 * n1)⁻¹ * B.t * (n2 * n1) := by
    have h : (n2 * n1) * y * (n2 * n1)⁻¹ = B.t := by
      rw [show (n2 * n1) * y * (n2 * n1)⁻¹ = n2 * (n1 * y * n1⁻¹) * n2⁻¹ from by group]
      exact hn2t
    rw [← h]; group
  rw [hx_eq, hy_eq]
  group

/-! ## 3. Bender 1.1(iii): an element of `V#` with a larger centralizer in `P` -/

/-- **Bender 1.1(iii), p. 221**: if the four-group `V ≤ S` contains `t` and `t` does not
centralize the `H`-invariant odd p-group `P`, then some `s ∈ V#`, `s ≠ t`, satisfies
`C_P(s) ≰ C_P(t)`. -/
theorem b26c_fourGroup_element {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (B : Work.GW2.BenderSetup G) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G)
    (hP : IsPGroup p P) (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (V : Subgroup G) (hV4 : Work.GW2.IsFourGroup V) (hVS : V ≤ (B.S : Subgroup G))
    (htV : B.t ∈ V) (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G)) :
    ∃ s ∈ V, s ≠ 1 ∧ s ≠ B.t ∧
      ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤ P ⊓ Subgroup.centralizer ({B.t} : Set G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have htH : B.t ∈ B.H := bSetup_t_mem_H B
  have hVH : V ≤ B.H := le_trans hVS (bSetup_S_le_H B)
  have hVN : V ≤ Subgroup.normalizer (P : Set G) := le_trans hVH hHN
  have hVp : IsPGroup 2 ↥V := IsPGroup.of_card (n := 2) (by rw [hV4.1]; norm_num)
  have hcop : Nat.Coprime 2 (Nat.card P) := by
    rw [Nat.prime_two.coprime_iff_not_dvd]
    intro hdiv
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
    rw [hk] at hdiv
    have h2p : 2 = p :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow hdiv)
    exact hp2 h2p.symm
  have hciii := T.c11iii G 2 V P V hVp hcop hVN le_rfl (by rw [hV4.1]; norm_num)
    (fun x hx => by have := hV4.2 x hx; simpa using this)
    (IsFourGroup.isMulCommutative' hV4)
  by_contra hcon
  have hcon' : ∀ s : G, s ∈ V → s ≠ 1 → s ≠ B.t →
      P ⊓ Subgroup.centralizer ({s} : Set G) ≤ P ⊓ Subgroup.centralizer ({B.t} : Set G) := by
    intro s hsV hs1 hst
    by_contra hle
    exact hcon ⟨s, hsV, hs1, hst, hle⟩
  have hsum : (⨆ (a : G) (_ : a ∈ V) (_ : a ≠ 1),
        P ⊓ Subgroup.centralizer ({a} : Set G))
      ≤ P ⊓ Subgroup.centralizer ({B.t} : Set G) := by
    refine iSup_le fun a => iSup_le fun haV => iSup_le fun ha1 => ?_
    rcases eq_or_ne a B.t with rfl | hat
    · exact le_rfl
    · exact hcon' a haV ha1 hat
  have hle : P ≤ P ⊓ Subgroup.centralizer ({B.t} : Set G) :=
    le_trans (le_of_eq hciii) hsum
  exact hnot (le_trans hle inf_le_right)

/-! ## 4. The target -/

-- theorem bender26c_key (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) (h23 : Work.GW2.Lemma23Prop) (h24 : Work.GW2.Lemma24Prop) (h25 : Work.GW2.Lemma25Prop)
--     (G : Type) [Group G] [Finite G] (hFT : Work.GW2.FeitThompsonProp) (hctx : Work.GW2.BenderCtx G)
--     (B : Work.GW2.BenderSetup G) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G)
--     (hP : IsPGroup p P) (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
--     (hmin : ∀ Q : Subgroup G, Q < P → IsPGroup p Q → B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G))
--     (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G)) :
--     ∃ (M : Subgroup G) (g : G) (X : Subgroup G),
--       IsCoatom M ∧ Subgroup.normalizer (P : Set G) ≤ M ∧ g ∉ M ∧ Work.GW2.oddCoreIn M ≠ ⊥ ∧
--         X ≤ Work.GW2.fittingIn M ∧ Subgroup.normalizer (X : Set G) ⊓ Work.GW2.fstarIn M ≤ Work.GW2.conjSub g M := by unproved
--
-- end Work.CORE2A
--