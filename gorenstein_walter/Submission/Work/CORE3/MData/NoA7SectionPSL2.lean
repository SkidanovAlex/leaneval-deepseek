import Mathlib
import Submission.Work.ASM.Defs
import Submission.Work.L2F.Main
import Submission.Work.A7.Defs
import Submission.Work.AUTA7.A7.CentralizerInvolution
import Submission.Work.AUTA7.A7.A7KNoOrderFour
import Submission.Work.CORE3.MData.NoA7SectionAux
import Submission.Work.CORE3.MData.FourGroupDihedralFour

open scoped MatrixGroups
open Subgroup

namespace Work.CORE3.MData

theorem A7CentNotCycOrDih (t : alternatingGroup (Fin 7)) (ht : orderOf t = 2) :
    ¬ CycOrDih ↥(Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7)))) := by
  set C : Subgroup (alternatingGroup (Fin 7)) :=
    Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7))) with hCdef
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h; rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have hcard : Nat.card C = 24 := by
    rw [hCdef]; exact Work.AUTA7.A7.CentralizerInvolution ht2 ht1
  rintro (hcyc | ⟨m, ⟨e⟩⟩)
  · haveI := hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥C)
    have h24 : orderOf (g : alternatingGroup (Fin 7)) = 24 := by
      rw [Subgroup.orderOf_coe, hg, hcard]
    exact Work.AUTA7.A7.no_dvd_twelve_orderOf_alternatingGroup _
      ⟨2, by rw [h24]⟩
  · have h2m : 2 * m = 24 := by
      have h := Nat.card_congr e.toEquiv
      rw [DihedralGroup.nat_card, hcard] at h
      omega
    have hm : m = 12 := by omega
    subst hm
    have h12 : orderOf (e.symm (DihedralGroup.r 1)) = 12 := by
      have h := orderOf_injective e.symm.toMonoidHom e.symm.injective (DihedralGroup.r 1)
      simpa [DihedralGroup.orderOf_r_one] using h
    have hcoe : orderOf (((e.symm (DihedralGroup.r 1) : ↥C) : alternatingGroup (Fin 7))) = 12 := by
      rw [Subgroup.orderOf_coe, h12]
    exact Work.AUTA7.A7.no_dvd_twelve_orderOf_alternatingGroup _
      ⟨1, by rw [hcoe]⟩

theorem A7NotCycOrDih : ¬ CycOrDih (alternatingGroup (Fin 7)) := by
  rintro (hcyc | ⟨m, ⟨e⟩⟩)
  · haveI : IsCyclic ↥(⊤ : Subgroup (alternatingGroup (Fin 7))) :=
      (MulEquiv.isCyclic Subgroup.topEquiv).mpr hcyc
    have hc : IsCyclic ↥(Subgroup.centralizer ({Work.A7.a7Invol} :
        Set (alternatingGroup (Fin 7)))) :=
      Subgroup.isCyclic_of_le (le_top)
    exact A7CentNotCycOrDih _ Work.A7.orderOf_a7Invol (Or.inl hc)
  · have h2m : 2 * m = 2520 := by
      have h := Nat.card_congr e.toEquiv
      rw [DihedralGroup.nat_card, Work.A7.card_alternatingGroup_seven] at h
      omega
    have hm : m = 1260 := by omega
    subst hm
    have h12 : orderOf (e.symm (DihedralGroup.r 1)) = 1260 := by
      have h := orderOf_injective e.symm.toMonoidHom e.symm.injective (DihedralGroup.r 1)
      simpa [DihedralGroup.orderOf_r_one] using h
    exact Work.AUTA7.A7.no_dvd_twelve_orderOf_alternatingGroup _
      ⟨105, by rw [h12]⟩

theorem card_map_eq_card_of_disjoint_ker {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (K : Subgroup X) (h : K ⊓ f.ker = ⊥) : Nat.card ↥(K.map f) = Nat.card ↥K :=
  (Nat.card_congr (Equiv.ofBijective
    (fun x : ↥K => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : ↥(K.map f)))
    ⟨fun x y hxy => by
      have h2 : f (x : X) = f (y : X) := congrArg Subtype.val hxy
      have h3 : f ((x : X) * (y : X)⁻¹) = 1 := by
        rw [map_mul, map_inv, h2, mul_inv_cancel]
      have h4 : (x : X) * (y : X)⁻¹ ∈ K ⊓ f.ker :=
        ⟨K.mul_mem x.2 (K.inv_mem y.2), MonoidHom.mem_ker.mpr h3⟩
      rw [h] at h4
      exact Subtype.ext (mul_inv_eq_one.mp (Subgroup.mem_bot.mp h4)),
     fun y => by
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩)).symm

set_option maxHeartbeats 2000000 in
theorem NoA7SectionPSL2 (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k)
    (X : Type) [Group X] [Finite X] (L : Subgroup X) (hL : L.Normal)
    (hLq : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃*
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k) : Type)))
    (E : Subgroup X) (hEq : Work.GW2.IsQuasisimple E) (hEL : E ≤ L)
    (hA7 : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7))) : False := by
  classical
  haveI hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eL⟩ := hLq
  obtain ⟨eA⟩ := hA7
  let Φ : ↥E →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k) :=
    eL.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center ↥L)).comp (Subgroup.inclusion hEL))
  let Ψ : ↥E →* alternatingGroup (Fin 7) :=
    eA.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥E))
  have hΨker : Ψ.ker = Subgroup.center ↥E := by
    ext x
    rw [MonoidHom.mem_ker]
    show eA ((QuotientGroup.mk' (Subgroup.center ↥E)) x) = 1 ↔ x ∈ Subgroup.center ↥E
    constructor
    · intro h
      have h1 : (QuotientGroup.mk' (Subgroup.center ↥E)) x = 1 :=
        eA.injective (by rw [h, map_one])
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    · intro h
      rw [show (QuotientGroup.mk' (Subgroup.center ↥E)) x = 1 from by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact h, map_one]
  have hker_le : Φ.ker ≤ Subgroup.center ↥E := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (QuotientGroup.mk' (Subgroup.center ↥L)) (Subgroup.inclusion hEL x) = 1 := by
      have h2 := congrArg (⇑eL.symm) hx
      simpa [Φ, MonoidHom.comp_apply] using h2
    have h2 : Subgroup.inclusion hEL x ∈ Subgroup.center ↥L := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1; exact h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro y
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact congrArg Subtype.val (h2 (Subgroup.inclusion hEL y))
  have hΨsurj : Function.Surjective Ψ :=
    eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hle : Φ.ker ≤ Ψ.ker := by rw [hΨker]; exact hker_le
  have hkerRR : Φ.rangeRestrict.ker ≤ Ψ.ker := by
    rw [MonoidHom.ker_rangeRestrict]; exact hle
  let ψ : ↥Φ.range →* alternatingGroup (Fin 7) :=
    Φ.rangeRestrict.liftOfSurjective Φ.rangeRestrict_surjective ⟨Ψ, hkerRR⟩
  have hψapply : ∀ x : ↥E, ψ (Φ.rangeRestrict x) = Ψ x := by
    intro x
    have h := MonoidHom.liftOfRightInverse_comp_apply (f := Φ.rangeRestrict)
      (f_inv := Function.surjInv Φ.rangeRestrict_surjective)
      (hf := Function.rightInverse_surjInv Φ.rangeRestrict_surjective) ⟨Ψ, hkerRR⟩ x
    simpa [ψ] using h
  have hψsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨x, hx⟩ := hΨsurj a
    exact ⟨Φ.rangeRestrict x, by rw [hψapply x, hx]⟩
  have hψker : ψ.ker = ((Subgroup.center ↥E).map Φ).subgroupOf Φ.range := by
    ext y
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
    have hy : y = Φ.rangeRestrict x := Subtype.ext hx.symm
    rw [hy, MonoidHom.mem_ker, hψapply x, Subgroup.mem_subgroupOf,
      MonoidHom.coe_rangeRestrict, Subgroup.mem_map]
    constructor
    · intro h
      have h1 : x ∈ Ψ.ker := MonoidHom.mem_ker.mpr h
      rw [hΨker] at h1
      exact ⟨x, h1, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      have hzx' : Φ x = Φ z := hzx.symm
      have hxmem : x * z⁻¹ ∈ Φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hzx', mul_inv_cancel]
      have hx1 : Ψ (x * z⁻¹) = 1 := MonoidHom.mem_ker.mp (hle hxmem)
      have hz1 : Ψ z = 1 := MonoidHom.mem_ker.mp (by rw [hΨker]; exact hz)
      rw [show x = (x * z⁻¹) * z from by group, map_mul, hx1, hz1, one_mul]
  have hNcomm : ∀ n ∈ (Subgroup.center ↥E).map Φ, ∀ y ∈ Φ.range, y * n = n * y := by
    intro n hn y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hn
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hy
    rw [← ha, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz a]
  rcases Nat.even_or_odd (Nat.card ↥(ψ.ker)) with heven | hodd
  · have h2dvd : 2 ∣ Nat.card ↥(ψ.ker) := even_iff_two_dvd.mp heven
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(ψ.ker)) 2 h2dvd
    set mu : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k) :=
      ((z : ↥Φ.range) : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) with hmudef
    have hmu2 : orderOf mu = 2 := by
      rw [hmudef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    obtain ⟨n₀, hn₀, ⟨eC⟩⟩ := (Work.L2F.l2InvolutionCentralizer p k hp hk) mu hmu2
    have hn0 : 2 ≤ n₀ := by rcases hn₀ with h | h <;> omega
    haveI : NeZero n₀ := ⟨by omega⟩
    have hmuN : mu ∈ (Subgroup.center ↥E).map Φ := by
      rw [hmudef]
      exact Subgroup.mem_subgroupOf.mp (by rw [← hψker]; exact z.2)
    have hlecent : Φ.range ≤ Subgroup.centralizer ({mu} :
        Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hNcomm mu hmuN y hy
    have hYcyc : CycOrDih ↥Φ.range := CycOrDih_of_le_of_mulEquiv hlecent eC
    have hquot : CycOrDih (↥Φ.range ⧸ ψ.ker) := CycOrDih_quotient hYcyc ψ.ker
    exact A7NotCycOrDih
      (CycOrDih.of_iso (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj) hquot)
  · have hYcard : Nat.card ↥Φ.range = Nat.card ↥(ψ.ker) * 2520 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (ψ.ker : Subgroup ↥Φ.range)
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).toEquiv,
        Work.A7.card_alternatingGroup_seven] at h1
      omega
    have h8 : 8 ∣ Nat.card ↥Φ.range := by
      rw [hYcard]
      exact dvd_mul_of_dvd_right (by norm_num : (8 : ℕ) ∣ 2520) _
    obtain ⟨S, hScard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Φ.range) (p := 2) (n := 3)
      (by simpa using h8)
    have hScard8 : Nat.card ↥S = 8 := by simpa using hScard
    have hSdisj : S ⊓ ψ.ker = ⊥ := by
      refine Subgroup.eq_bot_of_card_eq _ ?_
      have h1 : Nat.card ↥(S ⊓ ψ.ker) ∣ Nat.card ↥S := Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card ↥(S ⊓ ψ.ker) ∣ Nat.card ↥(ψ.ker) := Subgroup.card_dvd_of_le inf_le_right
      have h3 : Odd (Nat.card ↥(S ⊓ ψ.ker)) := hodd.of_dvd_nat h2
      have h4 : Nat.card ↥(S ⊓ ψ.ker) ∣ 2 ^ 3 := by
        rw [show (2 : ℕ) ^ 3 = Nat.card ↥S from by rw [hScard8]; norm_num]
        exact h1
      have hcop : Nat.Coprime (2 ^ 3) (Nat.card ↥(ψ.ker)) := (hodd.coprime_two_left).pow_left 3
      have hdvd1 : Nat.card ↥(S ⊓ ψ.ker) ∣ 1 := by
        rw [← hcop.gcd_eq_one]
        exact Nat.dvd_gcd h4 h2
      exact Nat.dvd_one.mp hdvd1
    have hSbar : Nat.card ↥(S.map ψ) = 8 := by
      rw [card_map_eq_card_of_disjoint_ker ψ S hSdisj, hScard8]
    obtain ⟨eD⟩ := Work.CORE3.MData.subgroup_card_eight_a7 (S.map ψ) hSbar
    let ι : ↥S →* ↥(S.map ψ) :=
      (ψ.comp S.subtype).codRestrict (S.map ψ)
        (fun x => Subgroup.mem_map.mpr ⟨(x : ↥Φ.range), x.2, rfl⟩)
    have hιinj : Function.Injective ι := by
      intro x y hxy
      have h1 : ψ ((x : ↥S) : ↥Φ.range) = ψ ((y : ↥S) : ↥Φ.range) := by
        have h := congrArg Subtype.val hxy
        simpa [ι, MonoidHom.codRestrict_apply] using h
      have h2 : ((x : ↥S) : ↥Φ.range) * ((y : ↥S) : ↥Φ.range)⁻¹ ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
      have h3 : ((x : ↥S) : ↥Φ.range) * ((y : ↥S) : ↥Φ.range)⁻¹ ∈ S ⊓ ψ.ker :=
        ⟨S.mul_mem x.2 (S.inv_mem y.2), h2⟩
      rw [hSdisj] at h3
      have h4 := Subgroup.mem_bot.mp h3
      exact Subtype.ext (mul_inv_eq_one.mp h4)
    have hιsurj : Function.Surjective ι := by
      intro z
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp z.2
      exact ⟨⟨w, hw⟩, Subtype.ext hwz⟩
    let eι : ↥S ≃* ↥(S.map ψ) := MulEquiv.ofBijective ι ⟨hιinj, hιsurj⟩
    obtain ⟨V₀, hV₀card, hV₀sq⟩ := Work.CORE3.MData.FourGroupDihedralFour
    have hV₀ : Work.L2F.IsFourGroup V₀ := ⟨hV₀card, fun v hv => by
      rw [pow_two]; exact hV₀sq v hv⟩
    have hV₁ : Work.L2F.IsFourGroup (V₀.map (eD.symm.toMonoidHom)) :=
      Work.L2F.PSL.isFourGroup_map_of_injective _ eD.symm.injective hV₀
    have hV₂ : Work.L2F.IsFourGroup ((V₀.map (eD.symm.toMonoidHom)).map eι.symm.toMonoidHom) :=
      Work.L2F.PSL.isFourGroup_map_of_injective _ eι.symm.injective hV₁
    set V : Subgroup ↥Φ.range :=
      ((V₀.map (eD.symm.toMonoidHom)).map eι.symm.toMonoidHom).map S.subtype with hVdef
    have hV : Work.L2F.IsFourGroup V := by
      rw [hVdef]
      exact Work.L2F.PSL.isFourGroup_map_of_injective _ (fun _ _ h => Subtype.ext h) hV₂
    have hV' : Work.L2F.IsFourGroup (V.map Φ.range.subtype) :=
      Work.L2F.PSL.isFourGroup_map_of_injective _ (fun _ _ h => Subtype.ext h) hV
    have hNleV' : (Subgroup.center ↥E).map Φ ≤ V.map Φ.range.subtype := by
      have hcent : (Subgroup.center ↥E).map Φ ≤
          Subgroup.centralizer ((V.map Φ.range.subtype :
            Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) :
            Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
        intro n hn
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
        exact hNcomm n hn y y.2
      rwa [(Work.L2F.l2FourGroup p k hp hk).1 (V.map Φ.range.subtype) hV'] at hcent
    have hoddN : Odd (Nat.card ↥((Subgroup.center ↥E).map Φ)) := by
      have hcard : Nat.card ↥((Subgroup.center ↥E).map Φ) = Nat.card ↥(ψ.ker) :=
        ((Nat.card_congr (MulEquiv.subgroupCongr hψker).toEquiv).trans
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_le_range Φ _)).toEquiv)).symm
      rw [hcard]; exact hodd
    have hNbot : (Subgroup.center ↥E).map Φ = ⊥ := by
      refine Subgroup.eq_bot_of_card_eq _ ?_
      have h1 : Nat.card ↥((Subgroup.center ↥E).map Φ) ∣ Nat.card ↥(V.map Φ.range.subtype) :=
        Subgroup.card_dvd_of_le hNleV'
      have h2 : Nat.card ↥(V.map Φ.range.subtype) = 4 := hV'.1
      rw [h2] at h1
      have h4 : Nat.card ↥((Subgroup.center ↥E).map Φ) ∣ 2 ^ 2 := by
        rw [show (2 : ℕ) ^ 2 = 4 from by norm_num]
        exact h1
      have hcop : Nat.Coprime (2 ^ 2) (Nat.card ↥((Subgroup.center ↥E).map Φ)) :=
        ((hoddN.coprime_two_right).pow_right 2).symm
      have hdvd1 : Nat.card ↥((Subgroup.center ↥E).map Φ) ∣ 1 := by
        rw [← hcop.gcd_eq_one]
        exact Nat.dvd_gcd h4 (dvd_refl _)
      exact Nat.dvd_one.mp hdvd1
    have hkerbot : ψ.ker = ⊥ := by
      rw [hψker, hNbot]
      exact bot_subgroupOf Φ.range
    have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hkerbot
    obtain ⟨x, hxψ⟩ := hψsurj Work.A7.a7Invol
    have hx2 : orderOf (((x : ↥Φ.range)) :
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) = 2 := by
      have h1 : orderOf x = 2 := by
        have h := orderOf_injective ψ hψinj x
        rw [hxψ] at h
        rw [← h, Work.A7.orderOf_a7Invol]
      rw [Subgroup.orderOf_coe]; exact h1
    obtain ⟨n₁, hn₁, ⟨eC₁⟩⟩ := (Work.L2F.l2InvolutionCentralizer p k hp hk) _ hx2
    have hn1 : 2 ≤ n₁ := by rcases hn₁ with h | h <;> omega
    haveI : NeZero n₁ := ⟨by omega⟩
    set C₀ : Subgroup (alternatingGroup (Fin 7)) :=
      Subgroup.centralizer ({Work.A7.a7Invol} : Set (alternatingGroup (Fin 7))) with hC₀def
    set C_Y : Subgroup ↥Φ.range := C₀.comap ψ with hCYdef
    have hCYle : C_Y.map Φ.range.subtype ≤ Subgroup.centralizer
        ({(((x : ↥Φ.range)) :
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))}
          : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
      intro w hw
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [hCYdef, Subgroup.mem_comap] at hy
      have h1 : Work.A7.a7Invol * ψ y = ψ y * Work.A7.a7Invol :=
        Subgroup.mem_centralizer_iff.mp hy Work.A7.a7Invol (Set.mem_singleton _)
      have h2 : ψ (y * x) = ψ (x * y) := by
        rw [map_mul, map_mul, hxψ]
        exact h1.symm
      have h3 : y * x = x * y := hψinj h2
      simpa using congrArg Subtype.val h3
    have hCYcyc : CycOrDih ↥(C_Y.map Φ.range.subtype) :=
      CycOrDih_of_le_of_mulEquiv hCYle eC₁
    have hCYcyc' : CycOrDih ↥C_Y :=
      CycOrDih.of_iso
        (Subgroup.equivMapOfInjective C_Y Φ.range.subtype (fun _ _ h => Subtype.ext h)).symm hCYcyc
    have hmapC₀ : (C₀.comap ψ).map ψ = C₀ := by
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hψsurj, top_inf_eq]
    have hisoC : ↥C_Y ≃* ↥(Subgroup.centralizer
        ({Work.A7.a7Invol} : Set (alternatingGroup (Fin 7)))) := by
      rw [hCYdef]
      exact (Subgroup.equivMapOfInjective (C₀.comap ψ) ψ hψinj).trans
        (MulEquiv.subgroupCongr (hmapC₀.trans hC₀def))
    exact A7CentNotCycOrDih Work.A7.a7Invol Work.A7.orderOf_a7Invol
      (CycOrDih.of_iso hisoC hCYcyc')

end Work.CORE3.MData
