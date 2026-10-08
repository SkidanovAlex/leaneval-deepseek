import Mathlib
import Submission.Work.NormalComplement.sec5_setup
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.ThreePoints.P3Sub.part1_b

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.Sec5Fix

/-- An element of a subgroup lies in the centre of the subgroup iff, viewed in the ambient group,
it lies in the subgroup and centralises the subgroup. -/
theorem mem_center_subtype_iff {G : Type} [Group G] (F : Subgroup G) (a : ↥F) :
    a ∈ Subgroup.center ↥F ↔
      (a : G) ∈ F ⊓ Subgroup.centralizer (F : Set G) := by
  constructor
  · intro ha
    refine ⟨a.2, ?_⟩
    change (a : G) ∈ Subgroup.centralizer (F : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha (⟨h, hh⟩ : ↥F))
  · rintro ⟨-, hc⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc (g : G) g.2

/-- Conjugation by an element of `N_G(F)` preserves the centre (as a subgroup of the ambient
group). -/
theorem conj_mem_center_of_mem_center {G : Type} [Group G] {F : Subgroup G} {x z : G}
    (hx : x ∈ Subgroup.normalizer (F : Set G))
    (hz : z ∈ F ⊓ Subgroup.centralizer (F : Set G)) :
    x * z * x⁻¹ ∈ F ⊓ Subgroup.centralizer (F : Set G) := by
  have hmap : F.map (MulAut.conj x).toMonoidHom = F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have hmap' : F.map (MulAut.conj x⁻¹).toMonoidHom = F :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.inv_mem (Subgroup.normalizer (F : Set G)) hx)
  refine ⟨?_, ?_⟩
  · have h := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hz.1
    rw [hmap] at h
    simpa [MulAut.conj_apply] using h
  · change x * z * x⁻¹ ∈ Subgroup.centralizer (F : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hgF : x⁻¹ * g * x ∈ F := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hg
      rw [hmap'] at h
      simpa [MulAut.conj_apply] using h
    have hcomm : (x⁻¹ * g * x) * z = z * (x⁻¹ * g * x) :=
      Subgroup.mem_centralizer_iff.mp hz.2 (x⁻¹ * g * x) hgF
    calc g * (x * z * x⁻¹) = x * ((x⁻¹ * g * x) * z) * x⁻¹ := by group
      _ = x * (z * (x⁻¹ * g * x)) * x⁻¹ := by rw [hcomm]
      _ = (x * z * x⁻¹) * g := by group

/-- In a finite group of odd order, every element is a square. -/
theorem exists_sq_eq_of_odd {H : Type*} [Group H] [Finite H] (hodd : Odd (Nat.card H))
    (m : H) : ∃ z : H, z ^ 2 = m := by
  have hpow : m ^ Nat.card H = 1 := by
    have h1 : orderOf m ∣ Nat.card H := by
      have h2 := Subgroup.orderOf_dvd_natCard (⊤ : Subgroup H) (Subgroup.mem_top m)
      rwa [Subgroup.card_top] at h2
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  obtain ⟨k, hk⟩ := hodd
  refine ⟨m ^ (k + 1), ?_⟩
  calc (m ^ (k + 1)) ^ 2 = m ^ ((k + 1) * 2) := by rw [pow_mul]
    _ = m ^ (Nat.card H + 1) := by congr 1; omega
    _ = m ^ Nat.card H * m := by rw [pow_succ]
    _ = 1 * m := by rw [hpow]
    _ = m := one_mul m

theorem benderLift (hFT : Submission.Blueprint.FeitThompsonProp)
    (hA : Submission.Blueprint.ThmAProp) (hC : Submission.Blueprint.ThmCProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (hMF2 : Submission.Blueprint.BenderModelFacts2Prop)
    (hCor1 : Work.NormalComplement.Design.ChISixCor1Prop)
    (hBC : Work.NormalComplement.Design.BurnsideClassProp)
    (hBP : Work.NormalComplement.BenderPrelimProp) {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G} {r : ℕ}
    (h : Work.NormalComplement.Design.Setup5 G H t W p P A r) (u : G)
    (hu : u ∈ H ∧ orderOf u = 2 ∧
      u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G))
    (hp7 : 7 ≤ p)
    (hbd : let C := Subgroup.centralizer (A : Set G)
      let F₀ := (Submission.Blueprint.oddResidual ↥C).map C.subtype
      ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ : F₀ →* Y) (HY : Subgroup Y),
        Function.Surjective φ ∧ φ.ker = Subgroup.center ↥F₀ ∧
        LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y ∧
        LeanEval.GroupTheory.Defs.IsStronglyEmbedded HY ∧
        Submission.Blueprint.IsZassenhaus HY ∧
        (Submission.Blueprint.involutions (HY : Set Y)).ncard = 2 ^ p - 1 ∧
        ∃ (hu0 : u ∈ F₀) (ht0 : t ∈ F₀),
          φ ⟨u, hu0⟩ ∈ HY ∧ orderOf (φ ⟨u, hu0⟩) = 2 ∧ φ ⟨t, ht0⟩ ∉ HY ∧
          orderOf (φ ⟨t, ht0⟩) = 2 ∧
          ∀ x : F₀, (x : G) ∈ H → φ x ∈ HY) :
    ∃ T : Subgroup G,
      IsCyclic ↥T ∧ 6 ≤ Nat.card T ∧
      (∀ x ∈ T, u * x * u⁻¹ = x⁻¹) ∧
      u * t ∈ T ∧
      P ≤ Subgroup.normalizer (T : Set G) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  let F : Subgroup G := (Submission.Blueprint.oddResidual ↥C).map C.subtype
  obtain ⟨Y, instY, instFinY, φ, HY, hsurj, hker, hBenderY, hHYse, hHYzass, hInvCard,
    hu0, ht0, hφumem, hφuord, hφtnotmem, hφtord, hmapH⟩ := hbd
  letI : Group Y := instY
  letI : Finite Y := instFinY
  let u0 : ↥F := ⟨u, hu0⟩
  let t0 : ↥F := ⟨t, ht0⟩
  -- ## `Z(F)` has odd order
  have hoddZ : Odd (Nat.card ↥(Subgroup.center ↥F)) := by
    have hz := Work.NormalComplement.sec5_setup_p3F_center hFT hC4 h
    dsimp only at hz
    exact hz.2.2
  -- ## the Bender group data in `Y`
  have hp127 : 127 ≤ (Submission.Blueprint.involutions (HY : Set Y)).ncard := by
    rw [hInvCard]
    have h2 : 2 ^ 7 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp7
    norm_num at h2 ⊢
    omega
  have hfact := hMF2 Y hBenderY HY hHYse
  have hCYdata := hfact.2 hHYzass (φ u0) ⟨hφumem, hφuord⟩ (φ t0) hφtord hφtnotmem
  let CY : Subgroup Y := Subgroup.centralizer ({φ u0 * φ t0} : Set Y)
  have hCYcyc : IsCyclic ↥CY := hCYdata.1
  have hCYinv : ∀ y ∈ CY, φ u0 * y * (φ u0)⁻¹ = y⁻¹ := hCYdata.2.1
  have hCYcard : 6 ≤ Nat.card ↥CY := hCYdata.2.2 hp127
  -- ## `T₁ = φ⁻¹(C_Y(φ u₀ · φ t₀))`
  let T1 : Subgroup ↥F := CY.comap φ
  have hmapT1 : T1.map φ = CY := by
    change Subgroup.map φ (Subgroup.comap φ CY) = CY
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hsurj, top_inf_eq]
  -- ## `T₁` is abelian
  have hT1comm : ∀ a b : ↥T1, a * b = b * a := by
    have hle : ∀ y : ↥T1, φ (T1.subtype y) ∈ CY := fun y => y.2
    let f : ↥T1 →* ↥CY := (φ.comp T1.subtype).codRestrict CY hle
    have hkerle : f.ker ≤ Subgroup.center ↥T1 := by
      intro z hz
      have hz' : φ (z : ↥F) = 1 := by
        have h2 : (f z : ↥CY) = 1 := MonoidHom.mem_ker.mp hz
        have h3 : ((f z : ↥CY) : Y) = φ (z : ↥F) := rfl
        rw [← h3, h2]
        simp
      have hzF : (z : ↥F) ∈ Subgroup.center ↥F := by
        rw [← hker, MonoidHom.mem_ker]; exact hz'
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hzF (g : ↥F)
    haveI : IsCyclic ↥CY := hCYcyc
    intro a b
    exact (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hkerle).is_comm.comm a b
  -- ## the subgroup `T = {y ∈ T₁ | u₀ y u₀⁻¹ = y⁻¹}`
  let TT : Subgroup ↥F :=
    { carrier := {y | y ∈ T1 ∧ u0 * y * u0⁻¹ = y⁻¹}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨T1.mul_mem ha1 hb1, ?_⟩
        have hcomm : (⟨a, ha1⟩ : ↥T1) * ⟨b, hb1⟩ = ⟨b, hb1⟩ * ⟨a, ha1⟩ := hT1comm _ _
        have hcomm' : a * b = b * a := congrArg Subtype.val hcomm
        calc u0 * (a * b) * u0⁻¹ = (u0 * a * u0⁻¹) * (u0 * b * u0⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [ha2, hb2]
          _ = (a * b)⁻¹ := by rw [← mul_inv_rev, ← hcomm']
      one_mem' := ⟨T1.one_mem, by group⟩
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨T1.inv_mem ha1, ?_⟩
        have h := congrArg Inv.inv ha2
        simp only [mul_inv_rev, inv_inv] at h
        rw [inv_inv, mul_assoc]
        exact h }
  let Tmap : Subgroup G := TT.map F.subtype
  -- ## `T ≅ C_Y(φ u₀ · φ t₀)`
  have hinjT : ∀ y : ↥F, y ∈ TT → φ y = 1 → y = 1 := by
    intro y hyT hφy
    have hyZ : y ∈ Subgroup.center ↥F := by
      rw [← hker, MonoidHom.mem_ker]; exact hφy
    have hcenter := Subgroup.mem_center_iff.mp hyZ u0
    have h1 : u0 * y * u0⁻¹ = y := by rw [hcenter]; group
    have hyy : y = y⁻¹ := h1.symm.trans hyT.2
    have hsq : y * y = 1 := by nth_rewrite 2 [hyy]; exact mul_inv_cancel y
    have horder : orderOf y ∣ 2 := by rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hsq
    have hdvd : orderOf y ∣ Nat.card ↥(Subgroup.center ↥F) :=
      Subgroup.orderOf_dvd_natCard _ hyZ
    have hcop : Nat.Coprime 2 (Nat.card ↥(Subgroup.center ↥F)) :=
      Nat.coprime_two_left.mpr hoddZ
    have hg : Nat.gcd 2 (Nat.card ↥(Subgroup.center ↥F)) = 1 := hcop.gcd_eq_one
    have hone : orderOf y ∣ 1 := by
      have hh := Nat.dvd_gcd horder hdvd
      rwa [hg] at hh
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)
  have hsurjT : ∀ c : ↥CY, ∃ y ∈ TT, φ y = (c : Y) := by
    intro c
    have hmem : (c : Y) ∈ T1.map φ := by rw [hmapT1]; exact c.2
    obtain ⟨y0, hy01, hy0eq⟩ := Subgroup.mem_map.mp hmem
    let m : ↥F := (u0 * y0 * u0⁻¹) * y0
    have hm : m ∈ Subgroup.center ↥F := by
      rw [← hker, MonoidHom.mem_ker]
      show φ ((u0 * y0 * u0⁻¹) * y0) = 1
      have hinv := hCYinv (c : Y) c.2
      simp only [map_mul, map_inv, hy0eq]
      rw [hinv, inv_mul_cancel]
    obtain ⟨z', hz'2⟩ :=
      exists_sq_eq_of_odd hoddZ (⟨m⁻¹, Subgroup.inv_mem _ hm⟩ : ↥(Subgroup.center ↥F))
    let z : ↥F := z'.1
    have hz2 : z ^ 2 = m⁻¹ := by
      have hh := congrArg Subtype.val hz'2
      simpa [z] using hh
    have hzmem : z ∈ Subgroup.center ↥F := z'.2
    have hz1 : φ z = 1 := by
      rw [← MonoidHom.mem_ker, hker]; exact hzmem
    refine ⟨y0 * z, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · -- `y₀ z ∈ T₁`
        change φ (y0 * z) ∈ CY
        rw [map_mul, hz1, mul_one]
        exact hy01
      · -- `u₀ (y₀ z) u₀⁻¹ = (y₀ z)⁻¹`
        have hzc : ∀ g : ↥F, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hzmem g
        have hzci : ∀ g : ↥F, g * z⁻¹ = z⁻¹ * g :=
          fun g => Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hzmem) g
        have hzcm : ∀ g : ↥F, m * g = g * m :=
          fun g => (Subgroup.mem_center_iff.mp hm g).symm
        have hzu : u0 * z * u0⁻¹ = z := by rw [hzc u0]; group
        have hmz : m = (z ^ 2)⁻¹ := by rw [hz2, inv_inv]
        have hmz1 : m * z = z⁻¹ := by rw [hmz]; group
        have hmdecomp : u0 * y0 * u0⁻¹ = m * y0⁻¹ := by
          show u0 * y0 * u0⁻¹ = ((u0 * y0 * u0⁻¹) * y0) * y0⁻¹
          group
        calc u0 * (y0 * z) * u0⁻¹ = (u0 * y0 * u0⁻¹) * (u0 * z * u0⁻¹) := by group
          _ = (u0 * y0 * u0⁻¹) * z := by rw [hzu]
          _ = (m * y0⁻¹) * z := by rw [hmdecomp]
          _ = (y0⁻¹ * m) * z := by rw [hzcm y0⁻¹]
          _ = y0⁻¹ * (m * z) := by group
          _ = y0⁻¹ * z⁻¹ := by rw [hmz1]
          _ = (y0 * z)⁻¹ := by rw [mul_inv_rev, hzci y0⁻¹]
    · show φ (y0 * z) = (c : Y)
      rw [map_mul, hy0eq, hz1, mul_one]
  -- ## the isomorphism `T ≃* C_Y(φ u₀ · φ t₀)` and its consequences
  let ψ : ↥TT →* ↥CY := (φ.comp TT.subtype).codRestrict CY (fun y => y.2.1)
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro a b hab
      have h1 : φ (a : ↥F) = φ (b : ↥F) := congrArg (fun w : ↥CY => (w : Y)) hab
      have h2 : φ ((a : ↥F) * (b : ↥F)⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
      have h3 : (a : ↥F) * (b : ↥F)⁻¹ ∈ TT := TT.mul_mem a.2 (TT.inv_mem b.2)
      have h4 := hinjT _ h3 h2
      have : (a : ↥F) = (b : ↥F) := by rw [← mul_inv_eq_one]; exact h4
      exact Subtype.ext this
    · intro c
      obtain ⟨y, hyT, hyeq⟩ := hsurjT c
      exact ⟨⟨y, hyT⟩, Subtype.ext hyeq⟩
  let eψ : ↥TT ≃* ↥CY := MulEquiv.ofBijective ψ hψbij
  have hTmap_card : Nat.card ↥Tmap = Nat.card ↥CY := by
    have h1 : Nat.card ↥Tmap = Nat.card ↥TT :=
      Subgroup.card_map_of_injective (K := TT) (f := F.subtype) F.subtype_injective
    rw [h1]
    exact Nat.card_congr eψ.toEquiv
  have hTmap_cyc : IsCyclic ↥Tmap := by
    haveI : IsCyclic ↥CY := hCYcyc
    have hTcyc : IsCyclic ↥TT := isCyclic_of_surjective eψ.symm eψ.symm.surjective
    haveI : IsCyclic ↥TT := hTcyc
    exact isCyclic_of_surjective (Subgroup.equivMapOfInjective TT F.subtype F.subtype_injective)
      (Subgroup.equivMapOfInjective TT F.subtype F.subtype_injective).surjective
  -- ## the inversion property and `u * t ∈ T`
  have hinvTmap : ∀ x ∈ Tmap, u * x * u⁻¹ = x⁻¹ := by
    intro x hxT
    obtain ⟨y, hyT, hyeq⟩ := Subgroup.mem_map.mp hxT
    rw [← hyeq]
    exact congrArg Subtype.val hyT.2
  have hutTmap : u * t ∈ Tmap := by
    refine Subgroup.mem_map.mpr ⟨u0 * t0, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · change φ (u0 * t0) ∈ CY
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        rw [show φ (u0 * t0) = φ u0 * φ t0 from map_mul φ u0 t0]
      · apply Subtype.ext
        show u * (u * t) * u⁻¹ = (u * t)⁻¹
        have hu2 : u * u = 1 := by rw [← pow_two, ← hu.2.1, pow_orderOf_eq_one]
        have ht2 : t * t = 1 := by rw [← pow_two, ← h.invol, pow_orderOf_eq_one]
        have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
        have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
        calc u * (u * t) * u⁻¹ = (u * u) * (t * u⁻¹) := by group
          _ = t * u⁻¹ := by rw [hu2, one_mul]
          _ = t * u := by rw [hui]
          _ = (u * t)⁻¹ := by rw [mul_inv_rev, hui, hti]
    · rfl
  -- ## `P` normalises `T`
  have hPT : P ≤ Subgroup.normalizer (Tmap : Set G) := by
    have hstep : ∀ (x' : G), x' ∈ P → ∀ y ∈ Tmap, x' * y * x'⁻¹ ∈ Tmap := by
      intro x' hx'P y hyT
      obtain ⟨y0, hy0T, hy0eq⟩ := Subgroup.mem_map.mp hyT
      have hy0eq' : (y0 : G) = y := hy0eq
      have hx'V : x' ∈ Submission.Blueprint.centD H t := (h.P_le hx'P).2
      have hx'A : x' ∈ Subgroup.normalizer (A : Set G) := h.A_normal hx'V
      have hx'F : x' ∈ Subgroup.normalizer (F : Set G) :=
        Work.ThreePoints.P3Sub.normalizer_le_normalizer_p3F A hx'A
      have hx'u : x' * u * x'⁻¹ = u := by
        have h := Subgroup.mem_centralizer_iff.mp hu.2.2 x' hx'V
        rw [h]; group
      have hx't : x' * t * x'⁻¹ = t := by
        have h := Subgroup.mem_centralizer_iff.mp hx'V.2 t (by simp)
        rw [← h]; group
      have hx'ut : x' * (u * t) * x'⁻¹ = u * t := by
        calc x' * (u * t) * x'⁻¹ = (x' * u * x'⁻¹) * (x' * t * x'⁻¹) := by group
          _ = u * t := by rw [hx'u, hx't]
      have hmemF : x' * (y0 : G) * x'⁻¹ ∈ F :=
        (Subgroup.mem_normalizer_iff.mp hx'F (y0 : G)).mp y0.2
      let y' : ↥F := ⟨x' * (y0 : G) * x'⁻¹, hmemF⟩
      have hy'eq : (y' : G) = x' * y * x'⁻¹ := by
        show x' * (y0 : G) * x'⁻¹ = x' * y * x'⁻¹
        rw [hy0eq']
      have hy'T : y' ∈ TT := by
        refine ⟨?_, ?_⟩
        · -- `y' ∈ T₁`
          change φ y' ∈ CY
          rw [Subgroup.mem_centralizer_iff]
          let w : ↥F := u0 * t0
          have hwY : φ w = φ u0 * φ t0 := map_mul φ u0 t0
          have hcomm0 : φ y0 * φ w = φ w * φ y0 := by
            have h := Subgroup.mem_centralizer_iff.mp hy0T.1 (φ u0 * φ t0) (by simp)
            rw [← hwY] at h
            exact h.symm
          have hs_ker : y0 * w * y0⁻¹ * w⁻¹ ∈ Subgroup.center ↥F := by
            rw [← hker, MonoidHom.mem_ker]
            simp only [map_mul, map_inv]
            rw [hcomm0]; group
          have hmemcenter : ((y0 * w * y0⁻¹ * w⁻¹ : ↥F) : G) ∈
              F ⊓ Subgroup.centralizer (F : Set G) :=
            (mem_center_subtype_iff F _).mp hs_ker
          have hconj := conj_mem_center_of_mem_center (F := F) hx'F hmemcenter
          have heq : (((y' * w * y'⁻¹ * w⁻¹ : ↥F) : G)) =
              x' * ((y0 * w * y0⁻¹ * w⁻¹ : ↥F) : G) * x'⁻¹ := by
            have hwG : ((w : G)) = x' * (w : G) * x'⁻¹ := by
              show u * t = x' * (u * t) * x'⁻¹
              rw [hx'ut]
            show (y' : G) * (w : G) * (y' : G)⁻¹ * (w : G)⁻¹ =
              x' * ((y0 : G) * (w : G) * (y0 : G)⁻¹ * (w : G)⁻¹) * x'⁻¹
            rw [hy'eq, ← hy0eq']
            conv_lhs => rw [hwG]
            group
          have hs' : y' * w * y'⁻¹ * w⁻¹ ∈ Subgroup.center ↥F := by
            apply (mem_center_subtype_iff F _).mpr
            rw [heq]; exact hconj
          have h1 : φ (y' * w * y'⁻¹ * w⁻¹) = 1 := by
            rw [← MonoidHom.mem_ker, hker]; exact hs'
          have h1' : φ y' * φ w * (φ y')⁻¹ * (φ w)⁻¹ = 1 := by
            simpa only [map_mul, map_inv] using h1
          have h2 : φ y' * φ w = φ w * φ y' := by
            have h3 : (φ y' * φ w) * (φ w * φ y')⁻¹ = 1 := by
              rw [mul_inv_rev, ← mul_assoc]; exact h1'
            exact mul_inv_eq_one.mp h3
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          rw [← hwY]
          exact h2.symm
        · -- `u₀ y' u₀⁻¹ = y'⁻¹`
          apply Subtype.ext
          show u * (y' : G) * u⁻¹ = (y' : G)⁻¹
          have hyinv : u * y * u⁻¹ = y⁻¹ := by
            rw [← hy0eq']; exact congrArg Subtype.val hy0T.2
          calc u * (y' : G) * u⁻¹ = u * (x' * y * x'⁻¹) * u⁻¹ := by rw [hy'eq]
            _ = x' * (u * y * u⁻¹) * x'⁻¹ := by
                  conv_lhs => rw [← hx'u]
                  group
            _ = x' * y⁻¹ * x'⁻¹ := by rw [hyinv]
            _ = (x' * y * x'⁻¹)⁻¹ := by group
            _ = (y' : G)⁻¹ := by rw [hy'eq]
      exact Subgroup.mem_map.mpr ⟨y', hy'T, hy'eq⟩
    intro x hxP
    rw [Subgroup.mem_normalizer_iff]
    intro hh
    constructor
    · intro hhT
      exact hstep x hxP hh hhT
    · intro hhT
      have hxinv : x⁻¹ ∈ P := P.inv_mem hxP
      have h2 := hstep x⁻¹ hxinv (x * hh * x⁻¹) hhT
      have h3 : x⁻¹ * (x * hh * x⁻¹) * x = hh := by group
      simpa only [inv_inv, h3] using h2
  exact ⟨Tmap, hTmap_cyc, le_trans hCYcard (le_of_eq hTmap_card.symm), hinvTmap, hutTmap, hPT⟩

end Work.NormalComplement.Sec5Fix
