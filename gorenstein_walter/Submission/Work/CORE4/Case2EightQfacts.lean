import Mathlib
import Submission.Work.CORE4.QFImports

/-!
# AREA CORE4 — `Work.CORE4.Case2EightQfacts`

Bender 1981, §4 (8), p. 226: for the odd prime `p` of §4 (8) and the `(p,p)`-subgroup `A` of
`F × K₀`, the subgroup `Q := Ω₁(Z₂(O_p(U)))` (`= Qsub p B`) satisfies

* `Q ≤ F(U)`  (`Q ≤ O_p(U) ≤ F(U)`),
* `U ≤ N_G(Q)`  (`Q` is characteristic in `O_p(U) ⊴ U`),
* `Q` has exponent `p`  (Bender 1.9(i) / `pow_eq_one_of_mem_omega1UpperCentralTwo`),
* `Q` is not cyclic  (Bender 1.9(ii): `O_p(U)` is non-cyclic because it contains `A ≅ C_p × C_p`).
-/

namespace Work.CORE4

open Subgroup
open scoped commutatorElement

/-! ## 1. General group-theoretic helpers -/

/-- `O_p(K) ≤ F(K)`: every normal `p`-subgroup of `K` is nilpotent. -/
theorem pCore_le_fitting {G : Type} [Group G] [Finite G] (K : Subgroup G) {p : ℕ}
    (hp : p.Prime) : Work.GW2.pCore p ↥K ≤ Work.GW2.fitting ↥K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsub : ({N : Subgroup ↥K | N.Normal ∧ IsPGroup p N} : Set (Subgroup ↥K)) ⊆
      {N : Subgroup ↥K | N.Normal ∧ Group.IsNilpotent N} := by
    rintro N ⟨hNn, hNpg⟩
    exact ⟨hNn, IsPGroup.isNilpotent hNpg⟩
  have h1 : (sSup {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}) ≤
      (sSup {N : Subgroup ↥K | N.Normal ∧ Group.IsNilpotent N}) :=
    sSup_le fun N hN => le_sSup (hsub hN)
  have h2 : ((sSup {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}).normalCore) ≤
      (sSup {N : Subgroup ↥K | N.Normal ∧ Group.IsNilpotent N}) :=
    le_trans (Subgroup.normalCore_le _) h1
  haveI : ((sSup {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}).normalCore).Normal :=
    Subgroup.normalCore_normal _
  have h3 := Subgroup.normal_le_normalCore.mpr h2
  rw [Work.GW2.pCore, Work.GW2.fitting]
  exact h3

/-- `O_p(K)` viewed in `G` lies in `F(K)` viewed in `G`. -/
theorem pCoreIn_le_fittingIn {G : Type} [Group G] [Finite G] (K : Subgroup G) {p : ℕ}
    (hp : p.Prime) : Work.GW2.pCoreIn p K ≤ Work.GW2.fittingIn K := by
  have h := pCore_le_fitting K hp
  calc Work.GW2.pCoreIn p K = (Work.GW2.pCore p ↥K).map K.subtype := rfl
    _ ≤ (Work.GW2.fitting ↥K).map K.subtype := Subgroup.map_mono h
    _ = Work.GW2.fittingIn K := rfl

/-- In a finite nilpotent group, every `p`-subgroup lies in `O_p`. -/
theorem le_pCore_of_isNilpotent_of_isPGroup {X : Type} [Group X] [Finite X] [Group.IsNilpotent X]
    (p : ℕ) [Fact p.Prime] {H : Subgroup X} (hH : IsPGroup p H) : H ≤ Work.GW2.pCore p X := by
  obtain ⟨P, hHP⟩ := hH.exists_le_sylow
  haveI hPn : (P : Subgroup X).Normal := inferInstance
  refine hHP.trans ?_
  show (P : Subgroup X) ≤ (sSup {N : Subgroup X | N.Normal ∧ IsPGroup p N}).normalCore
  rw [Subgroup.normal_le_normalCore]
  exact le_sSup ⟨inferInstance, P.isPGroup'⟩

/-- `K` normalizes its own `p`-core `O_p(K)`. -/
theorem pCoreIn_le_normalizer {G : Type} [Group G] [Finite G] (p : ℕ) (K : Subgroup G) :
    K ≤ Subgroup.normalizer (Work.GW2.pCoreIn p K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact conj_mem_pCoreIn p K hg hx
  · intro hx
    have h := conj_mem_pCoreIn p K (K.inv_mem hg) hx
    have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [h2] at h

/-! ## 2. Bender 1.9(ii): `Ω₁(Z₂(R))` is non-cyclic for a non-cyclic odd `p`-group `R` -/

/-- **Bender 1.9(ii) / BG Lemma 4.5(c)** (non-cyclic half). -/
theorem not_isCyclic_omega1UpperCentralTwo {R : Type} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hpg : IsPGroup p R) (hnc : ¬ IsCyclic R) :
    ¬ IsCyclic ↥(OddOrder.GroupTheory.omega1UpperCentralTwo R p) := by
  obtain ⟨S, hS_normal, hS_elem, hScard⟩ :=
    OddOrder.BG.Ch1.S04.exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic
      hpg hp hnc
  haveI : S.Normal := hS_normal
  have hS_ne_bot : S ≠ ⊥ := by
    intro hSbot
    have hcard_one : Nat.card S = 1 := by rw [hSbot, Subgroup.card_bot]
    have hp_sq_gt_one : 1 < p ^ 2 := one_lt_pow₀ (Fact.out : p.Prime).one_lt two_ne_zero
    exact (ne_of_gt hp_sq_gt_one) (by rw [← hScard, hcard_one])
  haveI : Group.IsNilpotent R := IsPGroup.isNilpotent hpg
  let H : Subgroup R := ⁅S, (⊤ : Subgroup R)⁆
  have hHlt : H < S := by
    dsimp [H]
    exact OddOrder.Isaacs.Ch04.commutator_lt_self_of_isNilpotent_ambient
      (E := S) (F := (⊤ : Subgroup R)) hS_ne_bot
  have hH_le_S : H ≤ S := hHlt.le
  have hH_normal : H.Normal := by dsimp [H]; infer_instance
  haveI : H.Normal := hH_normal
  have hH_le_center : H ≤ Subgroup.center R := by
    by_cases hHbot : H = ⊥
    · rw [hHbot]; exact bot_le
    · have hH_dvd : Nat.card H ∣ p ^ 2 := by
        rw [← hScard]; exact Subgroup.card_dvd_of_le hH_le_S
      obtain ⟨j, hj_le, hj_eq⟩ :=
        (Nat.dvd_prime_pow (p := p) (Fact.out (p := p.Prime))).mp hH_dvd
      have hj_ne_zero : j ≠ 0 := by
        intro hj0
        have hHcard_one : Nat.card H = 1 := by simpa [hj0] using hj_eq
        exact hHbot ((Subgroup.card_eq_one (H := H)).mp hHcard_one)
      have hj_ne_two : j ≠ 2 := by
        intro hj2
        have hHcard_eq_S : Nat.card H = Nat.card S := by rw [hj_eq, hj2, hScard]
        have hHS : H = S :=
          Subgroup.eq_of_le_of_card_ge hH_le_S (le_of_eq hHcard_eq_S.symm)
        exact hHlt.ne hHS
      have hj_eq_one : j = 1 := by omega
      have hHcard : Nat.card H = p := by simpa [hj_eq_one] using hj_eq
      exact OddOrder.BG.Ch1.S04.le_center_of_card_eq_prime_of_normal hpg hHcard
  have hS_le_Z2 : S ≤ Subgroup.upperCentralSeries R 2 := by
    intro s hs
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro r
    have hcomm_center : ⁅s, r⁆ ∈ Subgroup.center R := by
      exact hH_le_center (by
        dsimp [H]
        exact Subgroup.commutator_mem_commutator hs trivial)
    simpa [Subgroup.upperCentralSeries_one, commutatorElement_def] using hcomm_center
  let W : Subgroup R := OddOrder.GroupTheory.omega1UpperCentralTwo R p
  have hS_le_W : S ≤ W := by
    intro s hs
    dsimp [W]
    rw [OddOrder.GroupTheory.omega1UpperCentralTwo, Subgroup.mem_map]
    have hs_pow_sub := hS_elem.pow_eq_one (⟨s, hs⟩ : S)
    have hs_pow : s ^ p = 1 := by simpa using congrArg Subtype.val hs_pow_sub
    refine ⟨⟨s, hS_le_Z2 hs⟩, ?_, rfl⟩
    refine OddOrder.GroupTheory.Omega.mem_of_pow_eq_one ?_
    rw [pow_one]
    exact Subtype.ext (by simpa using hs_pow)
  have hS_not_cyclic : ¬ IsCyclic ↥S :=
    hS_elem.not_isCyclic_of_card_prime_sq (Fact.out : p.Prime) hScard
  intro hWcyc
  have hSsub_cyc : IsCyclic ↥(S.subgroupOf W) := by
    have : IsCyclic ↥W := by simpa [W] using hWcyc
    exact Subgroup.isCyclic _
  have hS_cyc : IsCyclic ↥S := by
    have : IsCyclic ↥(S.subgroupOf W) := hSsub_cyc
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS_le_W).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hS_le_W).surjective
  exact hS_not_cyclic hS_cyc

/-! ## 3. The bridge: `z2` and `Qsub` in terms of the upper central series -/

/-- `z2 P` is the carrier of the second centre `Z₂(↥P)` of the subgroup `P`, pushed into `G`. -/
theorem z2_eq_map_upperCentralSeries {G : Type} [Group G] (P : Subgroup G) :
    z2 P = (Subgroup.upperCentralSeries ↥P 2).map P.subtype := by
  apply le_antisymm
  · rw [z2, Subgroup.closure_le]
    rintro x hx
    obtain ⟨hxP, hxz⟩ := hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxP⟩, ?_, rfl⟩
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hcomm : (k : G) * ⁅x, (y : G)⁆ = ⁅x, (y : G)⁆ * (k : G) :=
      ((commutatorElement_eq_one_iff_mul_comm).mp (hxz (y : G) y.2 (k : G) k.2)).symm
    have hcoe : (((⁅(⟨x, hxP⟩ : ↥P), y⁆ : ↥P)) : G) = ⁅x, (y : G)⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      simp
    simp only [Subgroup.coe_mul, hcoe]
    exact hcomm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [z2]
    refine Subgroup.subset_closure ?_
    refine ⟨y.2, ?_⟩
    intro y' hy' z hz
    have hmem : ⁅y, (⟨y', hy'⟩ : ↥P)⁆ ∈ Subgroup.center ↥P := by
      have h := Subgroup.mem_upperCentralSeries_succ_iff.mp hy (⟨y', hy'⟩ : ↥P)
      rwa [Subgroup.upperCentralSeries_one] at h
    have hc := (Subgroup.mem_center_iff.mp hmem ⟨z, hz⟩).symm
    have hc' : ⁅(y : G), y'⁆ * z = z * ⁅(y : G), y'⁆ := by
      have h := congrArg (fun t : ↥P => (t : G)) hc
      have hcoe : (((⁅y, (⟨y', hy'⟩ : ↥P)⁆ : ↥P)) : G) = ⁅(y : G), y'⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        simp
      simp only [Subgroup.coe_mul, hcoe] at h
      simpa using h
    exact (commutatorElement_eq_one_iff_mul_comm).mpr hc'

/-- `Qsub p B = Ω₁(Z₂(O_p(U)))` in the `omega1UpperCentralTwo` normal form. -/
theorem Qsub_eq_map_omega1UpperCentralTwo {G : Type} [Group G] [Finite G]
    (p : ℕ) (B : Work.GW2.BenderSetup G) :
    Qsub p B =
      (OddOrder.GroupTheory.omega1UpperCentralTwo ↥(Work.GW2.pCoreIn p B.U) p).map
        (Work.GW2.pCoreIn p B.U).subtype := by
  have key : Qsub p B = omega1 p
      ((Subgroup.upperCentralSeries ↥(Work.GW2.pCoreIn p B.U) 2).map
        (Work.GW2.pCoreIn p B.U).subtype) := by
    simp only [Qsub, omega1, z2_eq_map_upperCentralSeries]
  rw [key, omega1, OddOrder.GroupTheory.omega1UpperCentralTwo, OddOrder.GroupTheory.Omega]
  rw [MonoidHom.map_closure, MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨hxW, hxp⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hxW
    refine ⟨u, ⟨⟨u, hu⟩, ?_, rfl⟩, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using hxp
  · rintro ⟨w, ⟨g, hg, hgw⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ ?_, ?_⟩
    · rw [← hgw]; exact g.2
    · have h1 : w ^ (p ^ 1) = 1 := by
        rw [← hgw]
        simpa using congrArg (Subgroup.subtype
          (Subgroup.upperCentralSeries ↥(Work.GW2.pCoreIn p B.U) 2)) hg
      have h2 : (((w : ↥(Work.GW2.pCoreIn p B.U)) : G)) ^ (p ^ 1) = 1 := by
        simpa using congrArg (fun t : ↥(Work.GW2.pCoreIn p B.U) => (t : G)) h1
      simpa using h2

/-! ## 4. `Qsub` is preserved by conjugation -/

/-- Conjugation acts on `Ω₁` by changing the ambient subgroup. -/
theorem conjSub_omega1 {G : Type} [Group G] (g : G) (p : ℕ) (W : Subgroup G) :
    Work.GW2.conjSub g (omega1 p W) = omega1 p (Work.GW2.conjSub g W) := by
  let f : G →* G := (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g).injective
  change (omega1 p W).map f = omega1 p (W.map f)
  rw [omega1, omega1, MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨y, ⟨hyW, hyp⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f hyW, by
      rw [← map_pow, hyp, map_one]⟩
  · rintro ⟨hxW, hxp⟩
    obtain ⟨y, hyW, rfl⟩ := Subgroup.mem_map.mp hxW
    refine ⟨y, ⟨hyW, ?_⟩, rfl⟩
    exact hf (by simpa only [map_pow, map_one] using hxp)

/-- Conjugation acts on the second centre by changing the ambient subgroup. -/
theorem conjSub_z2 {G : Type} [Group G] (g : G) (P : Subgroup G) :
    Work.GW2.conjSub g (z2 P) = z2 (Work.GW2.conjSub g P) := by
  let f : G →* G := (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g).injective
  change (z2 P).map f = z2 (P.map f)
  rw [z2, z2, MonoidHom.map_closure]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨y, ⟨hyP, hyz⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f hyP, ?_⟩
    intro y' hy' z hz
    obtain ⟨y₀, hy₀P, rfl⟩ := Subgroup.mem_map.mp hy'
    obtain ⟨z₀, hz₀P, rfl⟩ := Subgroup.mem_map.mp hz
    have key : f ⁅⁅y, y₀⁆, z₀⁆ = 1 := by rw [hyz y₀ hy₀P z₀ hz₀P, map_one]
    rwa [show ⁅⁅f y, f y₀⁆, f z₀⁆ = f ⁅⁅y, y₀⁆, z₀⁆ from by
      simp only [map_commutatorElement]]
  · rintro ⟨hxP, hxz⟩
    obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.mp hxP
    refine ⟨y, ⟨hyP, ?_⟩, rfl⟩
    intro y' hy' z hz
    have h := hxz (f y') (Subgroup.mem_map_of_mem f hy') (f z) (Subgroup.mem_map_of_mem f hz)
    have key : f ⁅⁅y, y'⁆, z⁆ = 1 := by
      rw [map_commutatorElement, map_commutatorElement]
      exact h
    exact hf (by rw [key, map_one])

/-! ## 5. The four facts about `Qsub` -/

/-- **Bender 1981, §4 (8)** (p. 226): the properties of `Q := Ω₁(Z₂(O_p(U)))`. -/
theorem Case2EightQfacts (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj C.D p P A →
          Work.CORE4.Qsub p B ≤ Work.GW2.fittingIn B.U ∧
          B.U ≤ Subgroup.normalizer ((Work.CORE4.Qsub p B) : Set G) ∧
          (∀ x ∈ Work.CORE4.Qsub p B, x ^ p = 1) ∧
          ¬ IsCyclic ↥(Work.CORE4.Qsub p B) := by
  intro G _ _ hbc B h2 C hplus h7 p P A hp hPF hPcard hobj
  haveI : Fact p.Prime := ⟨hp⟩
  have hAcard : Nat.card ↥A = p ^ 2 := hobj.2.2.2.2.1
  have hAexp : ∀ x ∈ A, x ^ p = 1 := hobj.2.2.2.2.2.1
  -- `p` is odd, since it divides `|F| ∣ |U|` and `U` has odd order
  have hpodd : Odd p := by
    have h1 : p ∣ Nat.card ↥C.D.F := by
      rw [← hPcard]; exact Subgroup.card_dvd_of_le hPF
    have h2 : Nat.card ↥C.D.F ∣ Nat.card ↥B.U :=
      Subgroup.card_dvd_of_le (Work.GW2.Case2Data.F_le_U B C.D)
    exact Odd.of_dvd_nat B.U_odd (h1.trans h2)
  -- `A` is not cyclic (`|A| = p²` and every element of `A` has `p`-th power `1`)
  have hAnc : ¬ IsCyclic ↥A := by
    intro hcyc
    haveI : IsCyclic ↥A := hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥A)
    have hgp : (g : G) ^ p = 1 := hAexp (g : G) g.2
    have hgp' : g ^ p = 1 := Subtype.ext (by simpa using hgp)
    have hdvd : orderOf g ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hgp'
    rw [hg, hAcard] at hdvd
    have h1 : ((p : ℤ)) ^ 2 ≤ (p : ℤ) := by
      have := Nat.le_of_dvd hp.pos hdvd
      exact_mod_cast this
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    nlinarith
  -- `A ≤ O_p(U)`: `A ≤ F(U)`, `F(U)` nilpotent, so `A ≤ O_p(F(U)) ≤ O_p(U)`
  have hAleFitting : A ≤ Work.GW2.fittingIn B.U :=
    (Case2EightA_le_FsupK0 I G hbc B h2 C hplus h7 p P A hp hPF hPcard hobj).trans
      (sup_le (Work.GW2.Case2Data.F_le_fitting B C.D)
        (inf_le_left : Work.GW2.fittingIn B.U ⊓ C.D.K ≤ Work.GW2.fittingIn B.U))
  have hApg : IsPGroup p ↥A := IsPGroup.of_card (n := 2) hAcard
  haveI : Group.IsNilpotent ↥(Work.GW2.fittingIn B.U) :=
    SevenX.PiFU.isNilpotent_fittingIn B.U
  have hA'pg : IsPGroup p ↥(A.subgroupOf (Work.GW2.fittingIn B.U)) :=
    hApg.of_equiv (Subgroup.subgroupOfEquivOfLe hAleFitting).symm
  have h1 := le_pCore_of_isNilpotent_of_isPGroup p hA'pg
  have h2' : A ≤ Work.GW2.pCoreIn p (Work.GW2.fittingIn B.U) := by
    calc A = (A.subgroupOf (Work.GW2.fittingIn B.U)).map (Work.GW2.fittingIn B.U).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hAleFitting).symm
      _ ≤ (Work.GW2.pCore p ↥(Work.GW2.fittingIn B.U)).map
            (Work.GW2.fittingIn B.U).subtype := Subgroup.map_mono h1
      _ = Work.GW2.pCoreIn p (Work.GW2.fittingIn B.U) := rfl
  have hfit_le : Work.GW2.fittingIn B.U ≤ B.U := Subgroup.map_subtype_le _
  have hfit_n : ((Work.GW2.fittingIn B.U).subgroupOf B.U).Normal := by
    have h : (Work.GW2.fittingIn B.U).subgroupOf B.U = Work.GW2.fitting ↥B.U := by
      rw [Work.GW2.fittingIn]
      exact Subgroup.comap_map_eq_self_of_injective B.U.subtype_injective _
    rw [h]; exact Subgroup.normalCore_normal _
  have hAleQcore : A ≤ Work.GW2.pCoreIn p B.U :=
    h2'.trans (pCoreIn_le_pCoreIn_of_normal hfit_le hfit_n p)
  have hqcnc : ¬ IsCyclic ↥(Work.GW2.pCoreIn p B.U) := by
    intro hcyc
    haveI : IsCyclic ↥(Work.GW2.pCoreIn p B.U) := hcyc
    have h1 : IsCyclic ↥(A.subgroupOf (Work.GW2.pCoreIn p B.U)) := Subgroup.isCyclic _
    exact hAnc (isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe hAleQcore).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAleQcore).surjective)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) `Q ≤ F(U)`
    rw [Qsub_eq_map_omega1UpperCentralTwo]
    exact (Subgroup.map_subtype_le _).trans (pCoreIn_le_fittingIn B.U hp)
  · -- (2) `U ≤ N_G(Q)`
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show Work.GW2.conjSub g (Qsub p B) = Qsub p B
    have hP : Work.GW2.conjSub g (Work.GW2.pCoreIn p B.U) = Work.GW2.pCoreIn p B.U :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (pCoreIn_le_normalizer p B.U hg)
    calc Work.GW2.conjSub g (Qsub p B)
        = Work.GW2.conjSub g (omega1 p (z2 (Work.GW2.pCoreIn p B.U))) := rfl
      _ = omega1 p (Work.GW2.conjSub g (z2 (Work.GW2.pCoreIn p B.U))) :=
            conjSub_omega1 g p _
      _ = omega1 p (z2 (Work.GW2.conjSub g (Work.GW2.pCoreIn p B.U))) := by rw [conjSub_z2]
      _ = omega1 p (z2 (Work.GW2.pCoreIn p B.U)) := by rw [hP]
      _ = Qsub p B := rfl
  · -- (3) exponent `p`
    intro x hx
    rw [Qsub_eq_map_omega1UpperCentralTwo] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy' := OddOrder.GroupTheory.pow_eq_one_of_mem_omega1UpperCentralTwo hpodd hy
    rw [← map_pow, hy', map_one]
  · -- (4) non-cyclicity
    rw [Qsub_eq_map_omega1UpperCentralTwo]
    intro hcyc
    haveI hI : IsCyclic ↥((OddOrder.GroupTheory.omega1UpperCentralTwo
        ↥(Work.GW2.pCoreIn p B.U) p).map (Work.GW2.pCoreIn p B.U).subtype) := hcyc
    have hWc : IsCyclic ↥(OddOrder.GroupTheory.omega1UpperCentralTwo
        ↥(Work.GW2.pCoreIn p B.U) p) := by
      have e := (Subgroup.equivMapOfInjective
        (OddOrder.GroupTheory.omega1UpperCentralTwo ↥(Work.GW2.pCoreIn p B.U) p)
        (Work.GW2.pCoreIn p B.U).subtype (Work.GW2.pCoreIn p B.U).subtype_injective).symm
      exact isCyclic_of_surjective e.toMonoidHom e.surjective
    exact not_isCyclic_omega1UpperCentralTwo hpodd (isPGroup_pCoreIn p B.U) hqcnc hWc

end Work.CORE4
