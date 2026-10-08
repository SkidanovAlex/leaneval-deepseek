import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2ParityQOf
import Submission.Work.CORE4.Case2CountPieces
import Submission.Work.CORE4.Case2KB0
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.Case2Fill
import Submission.Work.CORE4.Case2Parity
import Submission.Work.CORE4.Case2EHcard
import Submission.Work.CORE4.Case2KmulS0
import Submission.Work.CORE4.Case2Eight
import Submission.Work.CORE4.Case2EightP1Le
import Submission.Work.CORE4.ConjSubgroupCount
import Submission.Work.CORE4.ProjOfInfBot
import Submission.Work.CORE4.CountFibre
import Submission.Work.CORE4.NcardSubgroupsCardPrimeSq
import Submission.Work.CORE4.Case2ParityIso
import Submission.Work.PSL2.Card

open scoped MatrixGroups commutatorElement

namespace Work.CORE4

open Subgroup

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 1. Generic group-theoretic helpers -/

section Generic

variable {G : Type} [Group G] [Finite G]

/-- A field with more than three elements has a nonzero element whose square is not `1`. -/
theorem exists_ne_zero_and_sq_ne_one {F : Type*} [Field F] [Fintype F]
    (h : 4 ≤ Fintype.card F) : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hsub : (Finset.univ : Finset F) ⊆ ({0, 1, -1} : Finset F) := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · rcases sq_eq_one_iff.mp (hcon x hx) with h1 | h1 <;> simp [h1]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ] at h1
  have h2 : ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
  omega

/-- `Z(PSL(2,q)) = 1` for `q = pF^kF` odd, `q ≥ 5` (`SL(2,F)` is perfect for `|F| ≥ 4`). -/
theorem center_PSL2_bot (pF kF : ℕ) [Fact pF.Prime] (hp : Odd pF) (h5 : 5 ≤ pF ^ kF) :
    Subgroup.center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) = ⊥ := by
  haveI : Fintype (GaloisField pF kF) := Fintype.ofFinite _
  have hk : kF ≠ 0 := by rintro rfl; simp at h5
  have hcard : 4 ≤ Fintype.card (GaloisField pF kF) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card pF kF hk]
    calc 4 ≤ 5 := by norm_num
      _ ≤ pF ^ kF := h5
  obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_and_sq_ne_one hcard
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField pF kF)) :=
    Group.isPerfect_def.mpr (Matrix.SL2.commutator_eq_top ha0 ha1)
  exact Group.IsPerfect.center_quotient_center_eq_bot _

/-- The triviality of the centre transfers along an isomorphism. -/
theorem center_eq_bot_of_mulEquiv {E N : Type*} [Group E] [Group N] (ψ : E ≃* N)
    (h : Subgroup.center N = ⊥) : Subgroup.center E = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hx' : ψ x ∈ Subgroup.center N := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := ψ.surjective y
    rw [← map_mul, ← map_mul, hx z]
  rw [h] at hx'
  exact ψ.injective (by simpa using hx')

/-- If `P` centralizes `E` and the centre of `E` is trivial, then `P ⊓ E = ⊥`. -/
theorem inf_eq_bot_of_le_centralizer {P E : Subgroup G}
    (hP : P ≤ Subgroup.centralizer (E : Set G)) (hZ : Subgroup.center ↥E = ⊥) :
    P ⊓ E = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxP, hxE⟩ := hx
  have hmem : (⟨x, hxE⟩ : ↥E) ∈ Subgroup.center ↥E := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hP hxP) (y : G) y.2
  rw [hZ] at hmem
  simpa using hmem

/-- If `P` and `E` commute elementwise, every element of `P ⊔ E` is a product `p * e`. -/
theorem mem_sup_iff_eq_mul {P E : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (x : G) :
    x ∈ (P ⊔ E : Subgroup G) ↔ ∃ p ∈ P, ∃ e ∈ E, p * e = x := by
  have hPcent : ∀ a ∈ P, a ∈ Subgroup.centralizer (E : Set G) :=
    fun a ha => Subgroup.mem_centralizer_iff.mpr (fun b hb => (hcomm a ha b hb).symm)
  have hLE : P ≤ Subgroup.normalizer (E : Set G) :=
    fun a ha => Subgroup.centralizer_le_normalizer (E : Set G) (hPcent a ha)
  constructor
  · intro hx
    have hx' : x ∈ ((P ⊔ E : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P E hLE] at hx'
    exact Set.mem_mul.mp hx'
  · rintro ⟨p, hp, e, he, rfl⟩
    exact Subgroup.mul_mem_sup hp he

end Generic

/-! ## 2. Cyclic groups and conjugation of subgroups -/

section CyclicConj

variable {G : Type} [Group G] [Finite G]

/-- In a cyclic group `F`, an element `x` with `x ^ p = 1` (`p` a prime) lies in every subgroup of
`F` of order `p`. -/
theorem mem_of_pow_eq_one_of_isCyclic_of_card_eq_prime {F : Subgroup G} (hF : IsCyclic ↥F)
    {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hPF : P ≤ F) (hPcard : Nat.card ↥P = p)
    {x : G} (hxF : x ∈ F) (hxp : x ^ p = 1) : x ∈ P := by
  haveI : IsCyclic ↥F := hF
  have hcard_sub : Nat.card ↥((Subgroup.zpowers x).subgroupOf F) = orderOf x := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxF)).toEquiv,
      Nat.card_zpowers]
  have hcardP : Nat.card ↥(P.subgroupOf F) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPF).toEquiv, hPcard]
  have hle : (Subgroup.zpowers x).subgroupOf F ≤ P.subgroupOf F := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, hcard_sub, hcardP]
    exact orderOf_dvd_iff_pow_eq_one.mpr hxp
  have hxmem : (⟨x, hxF⟩ : ↥F) ∈ (Subgroup.zpowers x).subgroupOf F := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers x
  have hres := hle hxmem
  rwa [Subgroup.mem_subgroupOf] at hres

end CyclicConj

section ConjSub

variable {G : Type} [Group G]

theorem conjSub_one' (K : Subgroup G) : Work.GW2.conjSub 1 K = K := by
  ext x
  rw [Work.GW2.conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, hk'⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hk'
    rw [← hk']; simpa using hk
  · intro hx
    exact ⟨x, hx, by simp [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

theorem conjSub_mul' (a b : G) (K : Subgroup G) :
    Work.GW2.conjSub a (Work.GW2.conjSub b K) = Work.GW2.conjSub (a * b) K := by
  rw [Work.GW2.conjSub, Work.GW2.conjSub, Work.GW2.conjSub, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem conjSub_injective' (g : G) :
    Function.Injective (fun K : Subgroup G => Work.GW2.conjSub g K) := by
  intro K L h
  have h' := congrArg (fun M : Subgroup G => Work.GW2.conjSub g⁻¹ M) h
  simpa [conjSub_mul', conjSub_one'] using h'

theorem conjSub_eq_self_of_commute {K : Subgroup G} {g : G}
    (h : ∀ k ∈ K, g * k = k * g) : Work.GW2.conjSub g K = K := by
  ext x
  rw [Work.GW2.conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, hk'⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hk'
    have hkk : g * k * g⁻¹ = k := by rw [h k hk, mul_assoc, mul_inv_cancel, mul_one]
    rwa [← hk', hkk]
  · intro hx
    refine ⟨x, hx, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h x hx, mul_assoc, mul_inv_cancel, mul_one]

theorem conjSub_sup' (g : G) (K L : Subgroup G) :
    Work.GW2.conjSub g (K ⊔ L) = Work.GW2.conjSub g K ⊔ Work.GW2.conjSub g L := by
  rw [Work.GW2.conjSub, Work.GW2.conjSub, Work.GW2.conjSub]
  exact Subgroup.map_sup _ _ _

theorem le_conjSub_iff {g : G} {K L : Subgroup G} :
    Work.GW2.conjSub g K ≤ Work.GW2.conjSub g L ↔ K ≤ L := by
  constructor
  · intro h
    have h' : Work.GW2.conjSub g⁻¹ (Work.GW2.conjSub g K) ≤
        Work.GW2.conjSub g⁻¹ (Work.GW2.conjSub g L) := Subgroup.map_mono h
    simpa [conjSub_mul', conjSub_one'] using h'
  · intro h
    exact Subgroup.map_mono h

end ConjSub

/-! ## 3. The §4 objects: `K ≤ E(M)` and `F ⊓ K = ⊥` -/

section Case2Facts

variable {G : Type} [Group G] [Finite G] {B : Work.GW2.BenderSetup G}

/-- Bender §4 (1): `K = [S ∩ E(M), U ∩ M] ≤ E(M)` (because `E(M) ⊴ M`). -/
theorem K_le_layerIn_of_case2 (h : Work.GW2.Case2Ctx B)
    (hplus : Work.GW2.Case2PrePlus B h.D) :
    h.D.K ≤ Work.GW2.layerIn h.D.M := by
  have hK := hplus.2.1
  rw [hK]
  refine Subgroup.commutator_le.mpr ?_
  intro a ha b hb
  have haE : a ∈ Work.GW2.layerIn h.D.M := (Subgroup.mem_inf.mp ha).2
  have hbM : b ∈ h.D.M := (Subgroup.mem_inf.mp hb).2
  have hconj : b * a⁻¹ * b⁻¹ ∈ Work.GW2.layerIn h.D.M := by
    have haE' : a⁻¹ ∈ Work.GW2.layerIn h.D.M := inv_mem haE
    have hmem := h.layerIn_subgroupOf_normal.conj_mem
      (⟨a⁻¹, Work.CORE4.layerIn_le h.D.M haE'⟩ : ↥h.D.M)
      (by rw [Subgroup.mem_subgroupOf]; exact haE')
      (⟨b, hbM⟩ : ↥h.D.M)
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  have hcomm : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]; group
  rw [hcomm]
  exact mul_mem haE hconj

/-- Bender §4 (1)–(5): `F ⊓ K = ⊥`.  `F ≤ C(s)` and `K = I_{U∩M}(s)`, and `K ≤ U` has odd order,
so any common element satisfies `x = x⁻¹` and hence `x = 1`. -/
theorem F_inf_K_eq_bot_of_case2 (h : Work.GW2.Case2Ctx B) : h.D.F ⊓ h.D.K = ⊥ := by
  have hB0 : h.D.B0 ≤ Subgroup.centralizer ({h.D.s} : Set G) := by
    rw [h.D.B0_def]
    exact inf_le_right
  have hF_s : h.D.F ≤ Subgroup.centralizer ({h.D.s} : Set G) :=
    le_trans (Work.GW2.Case2Data.F_le_B0 B h.D) hB0
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxF, hxK⟩ := hx
  have hinv : h.D.s * x * h.D.s⁻¹ = x⁻¹ := by
    have hxK' : x ∈ Work.GW2.invSet (B.U ⊓ h.D.M) h.D.s := by
      rw [← h.D.K_def]; exact hxK
    exact hxK'.2
  have hfix : h.D.s * x * h.D.s⁻¹ = x := by
    have h1 := Subgroup.mem_centralizer_iff.mp (hF_s hxF) h.D.s rfl
    rw [h1, mul_assoc, mul_inv_cancel, mul_one]
  have hx2 : x ^ 2 = 1 := by
    have h1 : x = x⁻¹ := hfix.symm.trans hinv
    have h2 : x * x = 1 := by nth_rewrite 1 [h1]; exact inv_mul_cancel x
    simpa [pow_two] using h2
  have hxU : x ∈ B.U := Work.GW2.Case2Data.K_le_U B h.D hxK
  have hdvdU : orderOf x ∣ Nat.card ↥B.U := Subgroup.orderOf_dvd_natCard B.U hxU
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
  have hodd : Odd (orderOf x) := by
    obtain ⟨m, hm⟩ := hdvdU
    obtain ⟨t, ht⟩ := B.U_odd
    rcases Nat.even_or_odd (orderOf x) with he | ho
    · obtain ⟨c, hc⟩ := he
      have hd : 2 ∣ orderOf x * m := ⟨c * m, by rw [hc]; ring⟩
      obtain ⟨u, hu⟩ := hd
      have h2 : orderOf x * m = 2 * t + 1 := by rw [← hm, ht]
      rw [hu] at h2
      omega
    · exact ho
  have hone : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
    · exact h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp hone

end Case2Facts

/-! ## 4. Transport of conjugation along `E ↪ G` and along an isomorphism -/

section Transport

variable {G : Type} [Group G]

/-- Conjugating a subgroup of `↥E` and pushing it into `G` is conjugating the image in `G`. -/
theorem map_subtype_conjSub {E : Subgroup G} (e : ↥E) (Y : Subgroup ↥E) :
    Subgroup.map E.subtype (Work.GW2.conjSub e Y) =
      Work.GW2.conjSub (e : G) (Subgroup.map E.subtype Y) := by
  show Subgroup.map E.subtype (Subgroup.map (MulAut.conj e).toMonoidHom Y) =
    Subgroup.map (MulAut.conj (e : G)).toMonoidHom (Subgroup.map E.subtype Y)
  have hcomp : E.subtype.comp (MulAut.conj e).toMonoidHom =
      (MulAut.conj (e : G)).toMonoidHom.comp E.subtype := by
    ext x; simp [MulAut.conj_apply]
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

/-- Conjugation commutes with a group isomorphism. -/
theorem map_mulEquiv_conjSub {A N : Type*} [Group A] [Group N] (ψ : A ≃* N) (g : N)
    (Y : Subgroup A) :
    Subgroup.map ψ.symm.toMonoidHom (Work.GW2.conjSub g (Subgroup.map ψ.toMonoidHom Y)) =
      Work.GW2.conjSub (ψ.symm g) Y := by
  show Subgroup.map ψ.symm.toMonoidHom
      (Subgroup.map (MulAut.conj g).toMonoidHom (Subgroup.map ψ.toMonoidHom Y)) =
    Subgroup.map (MulAut.conj (ψ.symm g)).toMonoidHom Y
  have hcomp : (ψ.symm.toMonoidHom.comp (MulAut.conj g).toMonoidHom).comp ψ.toMonoidHom =
      (MulAut.conj (ψ.symm g)).toMonoidHom := by
    ext x; simp [MulAut.conj_apply, mul_assoc]
  rw [Subgroup.map_map, Subgroup.map_map, hcomp]

/-- Counting subgroups of a given order contained in a fixed subgroup `E`. -/
theorem ncard_subgroups_le_of_le {G : Type} [Group G] (E : Subgroup G) (r : ℕ) :
    {Y : Subgroup G | Y ≤ E ∧ Nat.card ↥Y = r}.ncard =
      {Y : Subgroup ↥E | Nat.card ↥Y = r}.ncard := by
  refine Set.ncard_congr (fun Y _ => Y.subgroupOf E) ?_ ?_ ?_
  · intro Y hY
    simp only [Set.mem_setOf_eq] at hY ⊢
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY.1).toEquiv, hY.2]
  · intro Y₁ Y₂ hY₁ hY₂ h
    have h1 : Subgroup.map E.subtype (Y₁.subgroupOf E) =
        Subgroup.map E.subtype (Y₂.subgroupOf E) := by rw [h]
    rwa [Subgroup.map_subgroupOf_eq_of_le hY₁.1, Subgroup.map_subgroupOf_eq_of_le hY₂.1] at h1
  · intro Z hZ
    refine ⟨Subgroup.map E.subtype Z, ⟨Subgroup.map_subtype_le Z, ?_⟩, ?_⟩
    · rw [Subgroup.card_map_of_injective (fun x y h => by simpa using h), hZ]
    · ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx
        obtain ⟨y, hy, hyx⟩ := hx
        rw [← Subtype.ext hyx]
        exact hy
      · intro hx
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        exact ⟨x, hx, rfl⟩

end Transport

/-! ## 5. The fibre of conjugates over a subgroup of order `p` -/

section Fibre

variable {G : Type} [Group G] [Finite G]

/-- Conjugating by `e ∈ E` maps the fibre of conjugates of `P` over `Y₀` onto the fibre over
`Y = Y₀ ^ e` (here `P` centralizes `E`). -/
theorem image_conjSub_fibre {P E Y Y₀ : Subgroup G} {e : G} (he : e ∈ E)
    (hPcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (hY : Y = Work.GW2.conjSub e Y₀) :
    {X : Subgroup G | X ≤ P ⊔ Y ∧ ∃ g : G, X = Work.GW2.conjSub g P} =
      Work.GW2.conjSub e '' {X : Subgroup G | X ≤ P ⊔ Y₀ ∧ ∃ g : G, X = Work.GW2.conjSub g P} := by
  have hPe : Work.GW2.conjSub e P = P :=
    conjSub_eq_self_of_commute (fun x hx => (hPcomm x hx e he).symm)
  have hPe' : Work.GW2.conjSub e⁻¹ P = P :=
    conjSub_eq_self_of_commute (fun x hx => (hPcomm x hx e⁻¹ (inv_mem he)).symm)
  have hmap : Work.GW2.conjSub e (P ⊔ Y₀) = P ⊔ Y := by
    rw [conjSub_sup', hPe, hY]
  have hmap' : Work.GW2.conjSub e⁻¹ (P ⊔ Y) = P ⊔ Y₀ := by
    rw [conjSub_sup', hPe', hY, conjSub_mul', inv_mul_cancel, conjSub_one']
  ext X
  constructor
  · rintro ⟨hXle, hXc⟩
    refine ⟨Work.GW2.conjSub e⁻¹ X, ⟨?_, ?_⟩, ?_⟩
    · have h1 : Work.GW2.conjSub e⁻¹ X ≤ Work.GW2.conjSub e⁻¹ (P ⊔ Y) :=
        Subgroup.map_mono hXle
      rwa [hmap'] at h1
    · obtain ⟨g, rfl⟩ := hXc
      exact ⟨e⁻¹ * g, by rw [conjSub_mul']⟩
    · rw [conjSub_mul', mul_inv_cancel, conjSub_one']
  · rintro ⟨X', ⟨hX'le, hX'c⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact hmap ▸ Subgroup.map_mono hX'le
    · obtain ⟨g, rfl⟩ := hX'c
      exact ⟨e * g, by rw [conjSub_mul']⟩

end Fibre

/-! ## 6. The projection of `P ⊔ E` onto `E` -/

section Proj

variable {G : Type} [Group G] [Finite G]

/-- The projection `↥(P ⊔ E) →* ↥E` along `P` satisfies `x * (π x)⁻¹ ∈ P`. -/
theorem exists_proj_property {P E : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) (hinf : P ⊓ E = ⊥) :
    ∃ π : ↥(P ⊔ E) →* ↥E, ∀ x : ↥(P ⊔ E), ((x : G) * (((π x : ↥E) : G))⁻¹) ∈ P := by
  obtain ⟨π, hπ⟩ := ProjOfInfBot P E hcomm hinf
  refine ⟨π, ?_⟩
  intro x
  obtain ⟨pp, hpp, ee, hee, hppee⟩ := (mem_sup_iff_eq_mul hcomm (x : G)).mp x.2
  have hval : (π x : ↥E) = ⟨ee, hee⟩ := by
    have hx : (⟨pp * ee, Subgroup.mul_mem_sup hpp hee⟩ : ↥(P ⊔ E)) = x := Subtype.ext hppee
    rw [← hx]; exact hπ pp hpp ee hee
  rw [hval, show (x : G) = pp * ee from hppee.symm, mul_assoc, mul_inv_cancel, mul_one]
  exact hpp

end Proj

/-! ## 7. `A = P ⊔ (A ∩ K)` for the `(p,p)`-group of §4 (8) -/

section EightObj

variable {G : Type} [Group G] [Finite G]

/-- If `A ≤ F ⊔ K` has order `p ^ 2` and exponent `p`, `F` is cyclic, `F ⊓ K = ⊥`, `F` and `K`
commute, and `P ≤ A ∩ F` has order `p` (`p` prime), then `A = P ⊔ (A ⊓ K)`, and `A ⊓ K` has
order `p`. -/
theorem eq_sup_inf_of_le_sup_of_card_eq_sq {F K A P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hFcyc : IsCyclic ↥F) (hFK : F ⊓ K = ⊥)
    (hcomm : ∀ f ∈ F, ∀ k ∈ K, f * k = k * f)
    (hA : A ≤ F ⊔ K) (hAcard : Nat.card ↥A = p ^ 2)
    (hAexp : ∀ x ∈ A, x ^ p = 1) (hPleA : P ≤ A) (hPF : P ≤ F) (hPcard : Nat.card ↥P = p) :
    A = P ⊔ (A ⊓ K) ∧ Nat.card ↥(A ⊓ K) = p := by
  have hPcomm : ∀ a ∈ P, ∀ b ∈ A ⊓ K, a * b = b * a := fun a ha b hb =>
    hcomm a (hPF ha) b hb.2
  have hle : A ≤ P ⊔ (A ⊓ K) := by
    intro a ha
    obtain ⟨f, hfF, k, hkK, hfk⟩ := (mem_sup_iff_eq_mul hcomm a).mp (hA ha)
    have hcm : Commute f k := hcomm f hfF k hkK
    have hpw : f ^ p * k ^ p = 1 := by
      have h1 : (f * k) ^ p = 1 := by rw [hfk]; exact hAexp a ha
      rwa [hcm.mul_pow] at h1
    have hfp : f ^ p = 1 := by
      have hmem : f ^ p ∈ F ⊓ K := by
        refine Subgroup.mem_inf.mpr ⟨pow_mem hfF p, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hpw]
        exact K.inv_mem (pow_mem hkK p)
      rw [hFK] at hmem
      simpa using hmem
    have hfP : f ∈ P :=
      mem_of_pow_eq_one_of_isCyclic_of_card_eq_prime hFcyc hp hPF hPcard hfF hfp
    have hkA : k ∈ A := by
      have h1 : k = f⁻¹ * a := by rw [← hfk, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h1]
      exact mul_mem (inv_mem (hPleA hfP)) ha
    have h2 : f * k ∈ P ⊔ (A ⊓ K) := Subgroup.mul_mem_sup hfP ⟨hkA, hkK⟩
    rwa [hfk] at h2
  have hAeq : A = P ⊔ (A ⊓ K) := le_antisymm hle (sup_le hPleA inf_le_left)
  refine ⟨hAeq, ?_⟩
  have hsurj : Function.Surjective (fun z : ↥P × ↥(A ⊓ K) =>
      (⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩ :
        ↥(P ⊔ (A ⊓ K)))) := by
    intro x
    obtain ⟨pp, hpp, kk, hkk, hppkk⟩ := (mem_sup_iff_eq_mul hPcomm (x : G)).mp x.2
    exact ⟨(⟨pp, hpp⟩, ⟨kk, hkk⟩), Subtype.ext hppkk⟩
  have hbound : Nat.card ↥(P ⊔ (A ⊓ K)) ≤ Nat.card ↥P * Nat.card ↥(A ⊓ K) := by
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    simpa [Nat.card_prod] using h1
  rw [← hAeq, hAcard, hPcard] at hbound
  have hge : p ≤ Nat.card ↥(A ⊓ K) := by
    have h2 : p * p ≤ p * Nat.card ↥(A ⊓ K) := by simpa [pow_two] using hbound
    exact Nat.le_of_mul_le_mul_left h2 hp.pos
  have hdvd : Nat.card ↥(A ⊓ K) ∣ p ^ 2 := by
    rw [← hAcard]; exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime_pow hp).mp hdvd with ⟨i, hi2, hi⟩
  have hge' : p ^ 1 ≤ p ^ i := by rw [← hi]; simpa using hge
  have hi1 : 1 ≤ i := by
    by_contra hcon
    have h0 : i = 0 := by omega
    rw [h0] at hge'
    simp at hge'
    have h2 : 2 ≤ p := hp.two_le
    omega
  have hcases : i = 1 ∨ i = 2 := by omega
  rcases hcases with h1 | h2
  · rw [hi, h1, pow_one]
  · exfalso
    have hcardAK : Nat.card ↥(A ⊓ K) = Nat.card ↥A := by rw [hi, h2, hAcard]
    have hAK : A ⊓ K = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcardAK.symm)
    have hPK : P ≤ K := hPleA.trans (le_of_eq hAK.symm) |>.trans inf_le_right
    have hPbot : P = ⊥ := by
      have : P ≤ F ⊓ K := le_inf hPF hPK
      rw [hFK] at this
      exact le_bot_iff.mp this
    have h1p : Nat.card ↥P = 1 := by rw [hPbot]; simp
    have h2p : 2 ≤ p := hp.two_le
    omega

end EightObj

section OneClass

/-- **Dickson's fact**: in `PSL(2,q)`, `q = pF^kF` odd `≥ 5`, the subgroups of an odd prime
order `r ≠ pF` form a single conjugacy class.  Route: `2 |C(Y)| = q ± 1` and `|N(Y)| = 2 |C(Y)|`
(`I.l2torusNorm`), so the class of `Y` has `|PSL(2,q)|/(q ± 1) = q (q ∓ 1)/2` elements, while
`I.l2primeCount` says that this is the number of all subgroups of order `r`. -/
theorem psl2_order_prime_subgroups_conjugate (I : Work.GW2.C4Inputs) :
    ∀ (pF kF r : ℕ) (_ : Fact pF.Prime)
      (Y Y' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF))),
      Odd pF → 5 ≤ pF ^ kF → r.Prime → r ≠ 2 → r ≠ pF →
      Nat.card Y = r → Nat.card Y' = r →
      ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF),
        Y' = Work.GW2.conjSub g Y := by
  intro pF kF r hpF Y Y' hpFodd h5 hr hr2 hrpF hYc hY'c
  classical
  haveI : Fact pF.Prime := hpF
  haveI : Fintype (GaloisField pF kF) := Fintype.ofFinite _
  let N := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)
  by_cases hdvd : r ∣ Nat.card N
  · obtain ⟨hCcyc, hCcard, hNnorm⟩ := I.l2torusNorm pF kF hpFodd h5 r hr hr2 hrpF Y hYc
    let C : Subgroup N := Subgroup.centralizer (Y : Set N)
    let Z : Subgroup N := Subgroup.normalizer (Y : Set N)
    have hnc : Nat.card ↥Z = 2 * Nat.card ↥C := by
      show Nat.card ↥(Subgroup.normalizer (Y : Set N)) =
        2 * Nat.card ↥(Subgroup.centralizer (Y : Set N))
      obtain ⟨ψ⟩ := hNnorm
      rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
    have hrc : r ∣ Nat.card ↥C := by
      have h1 : r ∣ Nat.card ↥Z := by
        show r ∣ Nat.card ↥(Subgroup.normalizer (Y : Set N))
        rw [← hYc]
        exact Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := Y))
      rw [hnc] at h1
      rcases (Nat.Prime.dvd_mul hr).mp h1 with h | h
      · exfalso
        rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
        · exact hr.ne_one h1
        · exact hr2 h1
      · exact h
    have hcardN : 2 * Nat.card N = pF ^ kF * ((pF ^ kF) ^ 2 - 1) := by
      have hkF : kF ≠ 0 := by rintro rfl; simp at h5
      have hh := Work.PSL2.card_PSL2_galoisField pF kF hpFodd hkF
      rwa [show pF ^ (2 * kF) = (pF ^ kF) ^ 2 from by rw [← pow_mul, Nat.mul_comm kF 2]] at hh
    have hsq : ((pF ^ kF) ^ 2 - 1) = (pF ^ kF - 1) * (pF ^ kF + 1) := by
      have := Nat.sq_sub_sq (pF ^ kF) 1
      simpa [mul_comm] using this
    have hclass : {X : Subgroup N | ∃ g, X = Work.GW2.conjSub g Y}.ncard = Z.index := by
      show _ = (Subgroup.normalizer (Y : Set N)).index
      exact ConjSubgroupCount N Y
    have hsub : {X : Subgroup N | ∃ g, X = Work.GW2.conjSub g Y} ⊆
        {X : Subgroup N | Nat.card X = r} := by
      rintro X ⟨g, rfl⟩
      change Nat.card ↥(Work.GW2.conjSub g Y) = r
      rw [Work.GW2.conjSub,
        Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective, hYc]
    rcases hCcard with hcase | hcase
    · -- `2 |C| = q + 1`
      have hd : (r : ℤ) ∣ (((pF ^ kF : ℕ) : ℤ) + 1) / 2 := by
        have hql : ((pF ^ kF : ℕ) : ℤ) + 1 = 2 * (Nat.card ↥C : ℤ) := by
          have h : ((2 * Nat.card ↥C : ℕ) : ℤ) = ((pF ^ kF : ℕ) : ℤ) + 1 := by exact_mod_cast hcase
          push_cast at h
          exact h.symm
        rw [Int.ediv_eq_of_eq_mul_right (by norm_num) hql]
        exact_mod_cast hrc
      have htotal : 2 * {X : Subgroup N | Nat.card X = r}.ncard = pF ^ kF * (pF ^ kF - 1) := by
        have h := I.l2primeCount pF kF hpFodd h5 r hr hr2 hrpF 1 (Or.inl rfl) hd
        rw [show ((pF ^ kF : ℕ) : ℤ) - 1 = ((pF ^ kF - 1 : ℕ) : ℤ) from
          (Nat.cast_sub (by omega : 1 ≤ pF ^ kF)).symm, ← Nat.cast_mul] at h
        exact_mod_cast h
      have hindex : 2 * Z.index = pF ^ kF * (pF ^ kF - 1) := by
        have hmul : Z.index * Nat.card ↥Z = Nat.card N := Subgroup.index_mul_card Z
        rw [hnc, hcase] at hmul
        have h2 : (2 * Z.index) * (pF ^ kF + 1) =
            (pF ^ kF * (pF ^ kF - 1)) * (pF ^ kF + 1) := by
          calc (2 * Z.index) * (pF ^ kF + 1) = 2 * (Z.index * (pF ^ kF + 1)) := by ring
            _ = 2 * Nat.card N := by rw [hmul]
            _ = pF ^ kF * ((pF ^ kF) ^ 2 - 1) := hcardN
            _ = pF ^ kF * ((pF ^ kF - 1) * (pF ^ kF + 1)) := by rw [hsq]
            _ = (pF ^ kF * (pF ^ kF - 1)) * (pF ^ kF + 1) := by ring
        exact Nat.mul_right_cancel (by omega : 0 < pF ^ kF + 1) h2
      have heq : {X : Subgroup N | ∃ g, X = Work.GW2.conjSub g Y} =
          {X : Subgroup N | Nat.card X = r} := by
        refine Set.eq_of_subset_of_ncard_le hsub ?_
        rw [hclass]
        have h3 : 2 * {X : Subgroup N | Nat.card X = r}.ncard = 2 * Z.index := by
          rw [htotal, hindex]
        exact le_of_eq (Nat.mul_left_cancel (by norm_num : 0 < 2) h3)
      have hmem : Y' ∈ {X : Subgroup N | ∃ g, X = Work.GW2.conjSub g Y} := by
        rw [heq]
        exact hY'c
      exact hmem
    · -- `2 |C| = q - 1`
      have hd : (r : ℤ) ∣ (((pF ^ kF : ℕ) : ℤ) + (-1)) / 2 := by
        have hql : ((pF ^ kF : ℕ) : ℤ) + (-1) = 2 * (Nat.card ↥C : ℤ) := by
          have h : ((2 * Nat.card ↥C : ℕ) : ℤ) = ((pF ^ kF : ℕ) : ℤ) - 1 := by
            rw [hcase, Nat.cast_sub (by omega : 1 ≤ pF ^ kF)]
            push_cast
            ring
          push_cast at h
          exact h.symm
        rw [Int.ediv_eq_of_eq_mul_right (by norm_num) hql]
        exact_mod_cast hrc
      have htotal : 2 * {X : Subgroup N | Nat.card X = r}.ncard = pF ^ kF * (pF ^ kF + 1) := by
        have h := I.l2primeCount pF kF hpFodd h5 r hr hr2 hrpF (-1) (Or.inr rfl) hd
        rw [show ((pF ^ kF : ℕ) : ℤ) - (-1) = ((pF ^ kF + 1 : ℕ) : ℤ) from by push_cast; ring,
          ← Nat.cast_mul] at h
        exact_mod_cast h
      have hindex : 2 * Z.index = pF ^ kF * (pF ^ kF + 1) := by
        have hmul : Z.index * Nat.card ↥Z = Nat.card N := Subgroup.index_mul_card Z
        rw [hnc, hcase] at hmul
        have h2 : (2 * Z.index) * (pF ^ kF - 1) =
            (pF ^ kF * (pF ^ kF + 1)) * (pF ^ kF - 1) := by
          calc (2 * Z.index) * (pF ^ kF - 1) = 2 * (Z.index * (pF ^ kF - 1)) := by ring
            _ = 2 * Nat.card N := by rw [hmul]
            _ = pF ^ kF * ((pF ^ kF) ^ 2 - 1) := hcardN
            _ = pF ^ kF * ((pF ^ kF - 1) * (pF ^ kF + 1)) := by rw [hsq]
            _ = (pF ^ kF * (pF ^ kF + 1)) * (pF ^ kF - 1) := by ring
        exact Nat.mul_right_cancel (by omega : 0 < pF ^ kF - 1) h2
      have heq : {X : Subgroup N | ∃ g, X = Work.GW2.conjSub g Y} =
          {X : Subgroup N | Nat.card X = r} := by
        refine Set.eq_of_subset_of_ncard_le hsub ?_
        rw [hclass]
        have h3 : 2 * {X : Subgroup N | Nat.card X = r}.ncard = 2 * Z.index := by
          rw [htotal, hindex]
        exact le_of_eq (Nat.mul_left_cancel (by norm_num : 0 < 2) h3)
      have hmem : Y' ∈ {X : Subgroup N | ∃ g, X = Work.GW2.conjSub g Y} := by
        rw [heq]
        exact hY'c
      exact hmem
  · exfalso
    have h1 : Nat.card ↥Y ∣ Nat.card ↥(⊤ : Subgroup N) := Subgroup.card_dvd_of_le le_top
    rw [show Nat.card ↥(⊤ : Subgroup N) = Nat.card N from
      Nat.card_congr (Subgroup.topEquiv (G := N)).toEquiv] at h1
    exact hdvd (hYc ▸ h1)

end OneClass

/-! ## 8. The count of Bender §4 (11) -/

theorem Case2Count11 (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.Case2 B)
    (h : Work.GW2.Case2Ctx B) (hplus : Work.GW2.Case2PrePlus B h.D)
    (h7 : Work.GW2.Case2SevenFacts B h.D) (h8 : Work.GW2.Case2EightAll B h.D)
    (p : ℕ) (P A : Subgroup G) (hpp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Work.GW2.Case2EightObj h.D p P A) :
    {X : Subgroup G | X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard =
      (Work.GW2.Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1 := by
  classical
  -- §4 (9)–(10): the `L₂(q)` identification, the parity data and `|M : M ⊓ H| = q k'`
  obtain ⟨pF, kF, hpF, φ, k, k', hpFodd, h7q, hkeven, hk'odd, hdisj, hrel, hCcard⟩ :=
    Case2ParityIso I G hbc B h
  haveI : Fact pF.Prime := hpF
  have h5q : 5 ≤ pF ^ kF := le_trans (by norm_num) h7q
  -- §4 (8) for the given pair `(p, P)`: the subgroup `A'` produced there is the given `A`
  obtain ⟨hp_obj, hPF_obj, hPcard_obj, hA_le, hAcard, hAexp, hPleA, hAuniq⟩ := hObj
  obtain ⟨A', hObjA', hFactsA'⟩ := h8 p P hpp hPF hPcard
  have hA'eq : A' = A := hAuniq A' hObjA'.2.2.2.1 hObjA'.2.2.2.2.1 hObjA'.2.2.2.2.2.1
  have hFacts : Work.GW2.Case2EightFacts B h.D p P A := hA'eq ▸ hFactsA'
  -- elementary facts about the §4 objects
  have hKE : h.D.K ≤ Work.GW2.layerIn h.D.M := K_le_layerIn_of_case2 h hplus
  have hPcomm : ∀ x ∈ P, ∀ y ∈ Work.GW2.layerIn h.D.M, x * y = y * x :=
    fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp
        (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF_obj hx)) y hy).symm
  have hZE : Subgroup.center ↥(Work.GW2.layerIn h.D.M) = ⊥ :=
    center_eq_bot_of_mulEquiv φ (center_PSL2_bot pF kF hpFodd (by omega))
  have hPEinf : P ⊓ Work.GW2.layerIn h.D.M = ⊥ :=
    inf_eq_bot_of_le_centralizer
      (fun x hx => Subgroup.mem_centralizer_iff.mpr
        (fun y hy => (hPcomm x hx y hy).symm)) hZE
  have hFK : h.D.F ⊓ h.D.K = ⊥ := F_inf_K_eq_bot_of_case2 h
  have hcommFK : ∀ f ∈ h.D.F, ∀ k ∈ h.D.K, f * k = k * f := fun f hf k hk =>
    (Subgroup.mem_centralizer_iff.mp (Work.GW2.Case2Pre.F_cent B h.D h.pre hf) k (hKE hk)).symm
  -- `A = P ⊔ (A ⊓ K)` and `|A ⊓ K| = p`
  obtain ⟨hAsup, hY0card⟩ :=
    eq_sup_inf_of_le_sup_of_card_eq_sq hpp h.F_cyclic hFK hcommFK hA_le hAcard hAexp hPleA
      hPF_obj hPcard_obj
  have hY0le : A ⊓ h.D.K ≤ Work.GW2.layerIn h.D.M := le_trans inf_le_right hKE
  -- `p ∣ k`
  have hKsub : h.D.K ≤ Work.GW2.layerIn h.D.M ⊓ B.H :=
    le_inf hKE (le_trans (Work.GW2.Case2Data.K_le_U B h.D) B.U_le_H)
  have hpK : p ∣ Nat.card ↥h.D.K :=
    dvd_trans hFacts.1 (Subgroup.card_dvd_of_le (show h.D.K0 ≤ h.D.K from inf_le_right))
  have hp2k : p ∣ 2 * k := by
    have h1 : Nat.card ↥h.D.K ∣ Nat.card ↥(Work.GW2.layerIn h.D.M ⊓ B.H) :=
      Subgroup.card_dvd_of_le hKsub
    rw [hCcard] at h1
    exact dvd_trans hpK h1
  have hp2 : p ≠ 2 := by
    intro h2
    have h2dvd : 2 ∣ Nat.card ↥B.U := by
      rw [← h2]
      exact dvd_trans hpK (Subgroup.card_dvd_of_le (Work.GW2.Case2Data.K_le_U B h.D))
    obtain ⟨m, hm⟩ := h2dvd
    obtain ⟨t, ht⟩ := B.U_odd
    omega
  have hpk : p ∣ k := by
    rcases (Nat.Prime.dvd_mul hpp).mp hp2k with h1 | h1
    · exfalso
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2 | h2
      · exact hpp.ne_one h2
      · exact absurd h2 hp2
    · exact h1
  -- one class of subgroups of order `p` inside `E = E(M)`
  have hone : ∀ Y Y' : Subgroup G, Y ≤ Work.GW2.layerIn h.D.M →
      Y' ≤ Work.GW2.layerIn h.D.M → Nat.card ↥Y = p → Nat.card ↥Y' = p →
      ∃ e : G, e ∈ Work.GW2.layerIn h.D.M ∧ Y' = Work.GW2.conjSub e Y := by
    intro Y Y' hYE hY'E hYc hY'c
    have hcardY : Nat.card ↥(Subgroup.map φ.toMonoidHom
        (Y.subgroupOf (Work.GW2.layerIn h.D.M))) = p := by
      rw [Subgroup.card_map_of_injective φ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYE).toEquiv, hYc]
    have hcardY' : Nat.card ↥(Subgroup.map φ.toMonoidHom
        (Y'.subgroupOf (Work.GW2.layerIn h.D.M))) = p := by
      rw [Subgroup.card_map_of_injective φ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY'E).toEquiv, hY'c]
    -- `p ≠ pF`: `p ∣ k` and `pF ∣ q` while `pF ∣ k` would force `pF ∣ 1`
    have hpne : p ≠ pF := by
      intro heq
      have hkF0 : kF ≠ 0 := by rintro rfl; simp at h7q
      have hdvdq : pF ∣ pF ^ kF := dvd_pow_self pF hkF0
      have hdvdk : pF ∣ k := heq ▸ hpk
      have hdvd2k : pF ∣ 2 * k := dvd_mul_of_dvd_right hdvdk 2
      have hone1 : pF ∣ 1 := by
        rcases hdisj with ⟨h1, -⟩ | ⟨h1, -⟩
        · have h2 : pF ∣ pF ^ kF + 1 := by rw [← h1]; exact hdvd2k
          exact (Nat.dvd_add_iff_right hdvdq).mpr h2
        · have h2 : pF ∣ pF ^ kF - 1 := by rw [← h1]; exact hdvd2k
          have h3 : pF ∣ 1 + (pF ^ kF - 1) := by
            rw [Nat.add_comm, Nat.sub_add_cancel (by omega : 1 ≤ pF ^ kF)]
            exact hdvdq
          exact (Nat.dvd_add_iff_left h2).mpr h3
      have h4 := Nat.le_of_dvd one_pos hone1
      have h5 := hpF.out.two_le
      omega
    obtain ⟨g, hg⟩ := psl2_order_prime_subgroups_conjugate I pF kF p hpF
      (Subgroup.map φ.toMonoidHom (Y.subgroupOf (Work.GW2.layerIn h.D.M)))
      (Subgroup.map φ.toMonoidHom (Y'.subgroupOf (Work.GW2.layerIn h.D.M)))
      hpFodd h5q hpp hp2 hpne hcardY hcardY'
    refine ⟨((φ.symm g : ↥(Work.GW2.layerIn h.D.M)) : G), (φ.symm g).2, ?_⟩
    have h1 : Y'.subgroupOf (Work.GW2.layerIn h.D.M) =
        Work.GW2.conjSub (φ.symm g) (Y.subgroupOf (Work.GW2.layerIn h.D.M)) := by
      have h2 := map_mulEquiv_conjSub φ g (Y.subgroupOf (Work.GW2.layerIn h.D.M))
      rw [← hg] at h2
      rw [Subgroup.map_map] at h2
      rw [show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ from
        MonoidHom.ext (fun x => φ.symm_apply_apply x), Subgroup.map_id] at h2
      exact h2
    calc Y' = Subgroup.map (Work.GW2.layerIn h.D.M).subtype
          (Y'.subgroupOf (Work.GW2.layerIn h.D.M)) :=
          (Subgroup.map_subgroupOf_eq_of_le hY'E).symm
      _ = Subgroup.map (Work.GW2.layerIn h.D.M).subtype
            (Work.GW2.conjSub (φ.symm g) (Y.subgroupOf (Work.GW2.layerIn h.D.M))) := by rw [h1]
      _ = Work.GW2.conjSub ((φ.symm g : ↥(Work.GW2.layerIn h.D.M)) : G)
            (Subgroup.map (Work.GW2.layerIn h.D.M).subtype
              (Y.subgroupOf (Work.GW2.layerIn h.D.M))) :=
          map_subtype_conjSub (φ.symm g) _
      _ = Work.GW2.conjSub ((φ.symm g : ↥(Work.GW2.layerIn h.D.M)) : G) Y := by
          rw [Subgroup.map_subgroupOf_eq_of_le hYE]
  -- the fibre cardinality `|{X ≤ P ⊔ Y : X ~ P}| = p₁`
  have hfib : ∀ Y : Subgroup G, Y ≤ Work.GW2.layerIn h.D.M → Nat.card ↥Y = p →
      {X : Subgroup G | X ≤ P ⊔ Y ∧ ∃ g : G, X = Work.GW2.conjSub g P}.ncard =
        Work.GW2.Case2EightP1 P A := by
    intro Y hYE hYcard
    obtain ⟨e, heE, hYeq⟩ := hone (A ⊓ h.D.K) Y hY0le hYE hY0card hYcard
    rw [image_conjSub_fibre (P := P) (E := Work.GW2.layerIn h.D.M) (Y := Y)
      (Y₀ := A ⊓ h.D.K) heE hPcomm hYeq,
      Set.ncard_image_of_injective _ (conjSub_injective' e), ← hAsup]
    rfl
  -- Bender §4 (11), first half: `E` has `q k'` subgroups of order `p`
  have hYcount : {Y : Subgroup G | Y ≤ Work.GW2.layerIn h.D.M ∧ Nat.card ↥Y = p}.ncard =
      (h.D.M ⊓ B.H).relIndex h.D.M := by
    have hcountE : {Y : Subgroup ↥(Work.GW2.layerIn h.D.M) | Nat.card ↥Y = p}.ncard =
        pF ^ kF * k' :=
      L2PrimeCountTransfer I G B h pF kF hpF φ (pF ^ kF) k k' p hpFodd h5q rfl
        hkeven hk'odd hdisj hpp hp2 hpk
    rw [ncard_subgroups_le_of_le (Work.GW2.layerIn h.D.M) p, hcountE, ← hrel]
  -- the projection `P ⊔ E →* E` and the count
  obtain ⟨π, hπ⟩ := exists_proj_property hPcomm hPEinf
  have hmain := CountFibre P (Work.GW2.layerIn h.D.M) p (Work.GW2.Case2EightP1 P A) hpp
    hPcard_obj hPEinf hPcomm π hπ hfib
  rw [hYcount] at hmain
  exact hmain

end Work.CORE4
