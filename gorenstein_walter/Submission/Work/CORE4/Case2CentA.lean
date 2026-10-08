import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2ParityQOf
import Submission.Work.CORE4.Case2Fill
import Submission.Work.CORE4.Case2KmulS0
import Submission.Work.CORE4.Case2Count11
import Submission.Work.CORE4.Case2S0_comm_U

namespace Work.CORE4

open Subgroup
open scoped MatrixGroups

/-!
# AREA CORE4 — `Case2CentA`

Bender 1981, §4 (10) (p. 227), the centralizer identity of the §4 configuration:

    `C_{P·E}(A) = P · K · S₀`,   `E = E(M) ≅ L₂(q)`,

where `A` is the `(p,p)`-subgroup of `F × K₁` with `P ≤ A` produced by §4 (8) (`Case2EightObj`),
`p` is Bender's prime with `P ≤ F` of order `p`, and `K = I_{U∩M}(s)`, `S₀` the index-two cyclic
subgroup of the Sylow `S` fixed by Bender.

The proof splits into

* **peeling off `P`**: `A` has order `p ^ 2`, hence is abelian, so `P ≤ C_G(A)`; as `P` commutes
  elementwise with `E` (because `P ≤ F ≤ C_G(E(M))`), every `x ∈ C_G(A) ⊓ (P ⊔ E)` is a product
  `p · e` with `e ∈ E` also centralizing `A`, so

    `C_G(A) ⊓ (P ⊔ E) = P ⊔ (C_G(A) ⊓ E)`;

* **the `E`-part** `C_G(A) ⊓ E = K ⊔ S₀`: since `A = P ⊔ (A ⊓ K)` (`eq_sup_inf_of_le_sup_of_card_eq_sq`,
  with `A ⊓ K` of order `p`) and `P ≤ C_G(E)`, `C_E(A) = C_E(A ⊓ K)`; the latter is the centralizer
  in the simple group `E ≅ L₂(q)` of an order-`p` subgroup, which is a torus of order `(q ± 1)/2`.
  `K ⊔ S₀` is contained in it (`K` is abelian, and `S₀ ≤ C_G(U) ⊇ K` by `Case2S0_comm_U`), and has
  order `|K| · |S₀| = k` (`Case2KmulS0`, `q = pF ^ kF`, `2k = q ± 1`); `k ∤ k'` forces the two
  subgroups to coincide.
-/

/-- **Centralizers and isomorphisms.**  Pushing a centralizer through a group isomorphism gives the
centralizer of the image. -/
theorem Case2CentA_map_centralizer_iso {A : Type*} [Group A] {N : Type*} [Group N]
    (ψ : A ≃* N) (Z : Subgroup A) :
    (Subgroup.centralizer (Z : Set A)).map ψ.toMonoidHom =
      Subgroup.centralizer ((Z.map ψ.toMonoidHom : Subgroup N) : Set N) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzc : ∀ y ∈ Z, y * z = z * y := fun y hy => Subgroup.mem_centralizer_iff.mp hz y hy
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, hzc z' hz']
  · intro hx
    refine Subgroup.mem_map.mpr ⟨ψ.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply ψ.injective
    have h := hx (ψ z) (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
    show ψ (z * ψ.symm x) = ψ (ψ.symm x * z)
    simpa only [map_mul, ψ.apply_symm_apply] using h

/-- **Centralizer inside a subgroup, along an isomorphism.**  If `Y ≤ E` and `ψ : ↥E ≃* N` then the
cardinality of `C_G(Y) ⊓ E` is the cardinality of the centralizer of the image of `Y` in `N`. -/
theorem Case2CentA_card_centralizer_map {G : Type} [Group G] {E : Subgroup G}
    {N : Type} [Group N] (ψ : ↥E ≃* N) {Y : Subgroup G} (hY : Y ≤ E) :
    Nat.card ↥(Subgroup.centralizer (Y : Set G) ⊓ E) =
      Nat.card ↥(Subgroup.centralizer
        ((Subgroup.map ψ.toMonoidHom (Y.subgroupOf E)) : Set N)) := by
  have hsub : (Subgroup.centralizer (Y : Set G) ⊓ E).subgroupOf E =
      Subgroup.centralizer (Y.subgroupOf E : Set ↥E) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : (x : G) ∈ Subgroup.centralizer (Y : Set G) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
      have h2 : (y : G) * (x : G) = (x : G) * (y : G) :=
        Subgroup.mem_centralizer_iff.mp h1 (y : G) (Subgroup.mem_subgroupOf.mp hy)
      exact Subtype.ext h2
    · intro hx
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, x.2⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h2 : (⟨y, hY hy⟩ : ↥E) * x = x * ⟨y, hY hy⟩ :=
        Subgroup.mem_centralizer_iff.mp hx ⟨y, hY hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
      simpa only [Subgroup.coe_mul] using congrArg Subtype.val h2
  calc Nat.card ↥(Subgroup.centralizer (Y : Set G) ⊓ E)
      = Nat.card ↥((Subgroup.centralizer (Y : Set G) ⊓ E).subgroupOf E) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (inf_le_right : Subgroup.centralizer (Y : Set G) ⊓ E ≤ E)).toEquiv).symm
    _ = Nat.card ↥(Subgroup.centralizer (Y.subgroupOf E : Set ↥E)) := by rw [hsub]
    _ = Nat.card ↥((Subgroup.centralizer (Y.subgroupOf E : Set ↥E)).map ψ.toMonoidHom) :=
        (Subgroup.card_map_of_injective ψ.injective).symm
    _ = Nat.card ↥(Subgroup.centralizer
          ((Subgroup.map ψ.toMonoidHom (Y.subgroupOf E)) : Set N)) := by
        rw [Case2CentA_map_centralizer_iso]

/-- **Replacing `A` by `A ⊓ K` in the centralizer.**  Let `A = P ⊔ Kp` with `P` centralizing `E`.
Then `C_G(A) ⊓ E = C_G(Kp) ⊓ E`: `C_G(A) ≤ C_G(Kp)` because `Kp ≤ A`, and conversely an element of
`E` centralizing `Kp` centralizes `P` (as `P ≤ C_G(E)`) and hence `A = P ⊔ Kp`. -/
theorem Case2CentA_centralizer_inf_eq_of_eq_sup {G : Type} [Group G] [Finite G]
    {P Kp E A : Subgroup G} (hAeq : A = P ⊔ Kp) (hPE : P ≤ Subgroup.centralizer (E : Set G)) :
    Subgroup.centralizer (A : Set G) ⊓ E = Subgroup.centralizer (Kp : Set G) ⊓ E := by
  have hKA : Kp ≤ A := by rw [hAeq]; exact le_sup_right
  have hle : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (Kp : Set G) :=
    Subgroup.centralizer_le hKA
  refine le_antisymm (le_inf (inf_le_left.trans hle) inf_le_right) ?_
  intro x hx
  obtain ⟨hxK, hxE⟩ := Subgroup.mem_inf.mp hx
  have hxP : x ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.mp (hPE hp) x hxE).symm
  have hsub : A ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [hAeq]
    refine sup_le ?_ ?_
    · intro p hp
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp hxP p hp).symm
    · intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.mp hxK k hk).symm
  refine Subgroup.mem_inf.mpr ⟨?_, hxE⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (hsub ha) x rfl).symm

/-- **Peeling off a centralizing factor.**  Let `P` centralize `A` and commute elementwise with
`E`.  Then intersecting the centralizer of `A` with the internal product `P · E` peels off the
factor `P`: `C_G(A) ⊓ (P · E) = P · (C_G(A) ⊓ E)`.

Proof.  `⊇` is clear.  For `⊆`, write `x ∈ P ⊔ E` as `x = p · e` (this uses the elementwise
commutation); if `x` centralizes `A` then so does `e = p⁻¹ · x`, because `p` does. -/
theorem Case2CentA_peel_centralizer {G : Type} [Group G] [Finite G] {P E A : Subgroup G}
    (hPc : P ≤ Subgroup.centralizer (A : Set G))
    (hcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) :
    Subgroup.centralizer (A : Set G) ⊓ (P ⊔ E) =
      P ⊔ (Subgroup.centralizer (A : Set G) ⊓ E) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxc, hxPE⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨p, hp, e, he, hpe⟩ := (mem_sup_iff_eq_mul hcomm x).mp hxPE
    have hec : e ∈ Subgroup.centralizer (A : Set G) := by
      have h3 : p⁻¹ * x = e := by rw [← hpe, inv_mul_cancel_left]
      rw [← h3]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hPc hp)) hxc
    rw [← hpe]
    exact Subgroup.mul_mem_sup hp (Subgroup.mem_inf.mpr ⟨hec, he⟩)
  · refine sup_le (le_inf hPc le_sup_left) ?_
    exact le_inf inf_le_left (le_trans inf_le_right le_sup_right)

theorem Case2CentA (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.Case2 B)
    (h : Work.GW2.Case2Ctx B) (hplus : Work.GW2.Case2PrePlus B h.D)
    (h7 : Work.GW2.Case2SevenFacts B h.D) (h8 : Work.GW2.Case2EightAll B h.D)
    (p : ℕ) (P A : Subgroup G) (hpp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card P = p) (hObj : Work.GW2.Case2EightObj h.D p P A) :
    Subgroup.centralizer ((A : Set G)) ⊓ (P ⊔ Work.GW2.layerIn h.D.M) =
      P ⊔ h.D.K ⊔ B.S0 := by
  obtain ⟨hp_obj, hPF_obj, hPcard_obj, hA_le, hAcard, hAexp, hPleA, hAuniq⟩ := hObj
  have hKE : h.D.K ≤ Work.GW2.layerIn h.D.M := K_le_layerIn_of_case2 h hplus
  have hcommFK : ∀ f ∈ h.D.F, ∀ k ∈ h.D.K, f * k = k * f := fun f hf k hk =>
    (Subgroup.mem_centralizer_iff.mp (Work.GW2.Case2Pre.F_cent B h.D h.pre hf) k (hKE hk)).symm
  have hFK : h.D.F ⊓ h.D.K = ⊥ := F_inf_K_eq_bot_of_case2 h
  obtain ⟨hAeq, hKpcard⟩ := eq_sup_inf_of_le_sup_of_card_eq_sq hpp h.F_cyclic hFK hcommFK
    hA_le hAcard hAexp hPleA hPF_obj hPcard_obj
  set Kp : Subgroup G := A ⊓ h.D.K with hKpdef
  have hKpK : Kp ≤ h.D.K := by rw [hKpdef]; exact inf_le_right
  have hKpE : Kp ≤ Work.GW2.layerIn h.D.M := hKpK.trans hKE
  have hKpU : Kp ≤ B.U := hKpK.trans (Work.GW2.Case2Data.K_le_U B h.D)
  have hS0U : ⁅B.S0, B.U⁆ = ⊥ := Case2S0_comm_U I hbc h2 h hplus h7
  have hS0C : B.S0 ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hS0U
  have hKle : h.D.K ≤ Subgroup.centralizer (Kp : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcommK : IsMulCommutative ↥h.D.K := by
      letI : CommGroup ↥h.D.K := (Work.GW2.Case2Pre.K_cyclic B h.D h.pre).commGroup
      infer_instance
    have h1 := congrArg Subtype.val (hcommK.is_comm.comm (⟨k, hk⟩ : ↥h.D.K) ⟨y, hKpK hy⟩)
    simp only [Subgroup.coe_mul] at h1
    exact h1.symm
  have hS0le : B.S0 ≤ Subgroup.centralizer (Kp : Set G) :=
    hS0C.trans (Subgroup.centralizer_le hKpU)
  have hsup_le : h.D.K ⊔ B.S0 ≤ Subgroup.centralizer (Kp : Set G) := sup_le hKle hS0le
  have hsup_leE : h.D.K ⊔ B.S0 ≤ Work.GW2.layerIn h.D.M :=
    sup_le hKE (B.S0_le.trans (S_le_layerIn h))
  have hKinfS0 : h.D.K ⊓ B.S0 = ⊥ := by
    refine le_bot_iff.mp ?_
    have h1 : h.D.K ⊓ B.S0 ≤ B.U ⊓ (B.S : Subgroup G) :=
      le_inf (le_trans inf_le_left (Work.GW2.Case2Data.K_le_U B h.D)) (le_trans inf_le_right B.S0_le)
    rwa [B.U_inf_S] at h1
  have hKleCS0 : h.D.K ≤ Subgroup.centralizer ((B.S0 : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp
      (hS0C.trans (Subgroup.centralizer_le (Work.GW2.Case2Data.K_le_U B h.D)))
  have hS0leCK : B.S0 ≤ Subgroup.centralizer ((h.D.K : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp hKleCS0
  have hcardKS0 : Nat.card ↥(h.D.K ⊔ B.S0) = Nat.card ↥h.D.K * Nat.card ↥B.S0 :=
    Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
      (hS0leCK.trans (Subgroup.centralizer_le_normalizer _)) hKinfS0
  obtain ⟨pF, kF, hpF, φ, k, k', hpFodd, h7q, hkeven, hk'odd, hdisj, hrel, hCcard⟩ :=
    Case2ParityIso I G hbc B h
  haveI : Fact pF.Prime := hpF
  have hkm : k = Nat.card ↥h.D.K * Nat.card ↥B.S0 :=
    Case2KmulS0 G I hbc B h (pF ^ kF) k k' hpFodd.pow h7q hdisj hrel
  have hcardKS0k : Nat.card ↥(h.D.K ⊔ B.S0) = k := by rw [hcardKS0, ← hkm]
  have hpK : p ∣ Nat.card ↥h.D.K := by
    obtain ⟨A', hObjA', hFactsA'⟩ := h8 p P hpp hPF hPcard
    exact dvd_trans hFactsA'.1 (Subgroup.card_dvd_of_le (show h.D.K0 ≤ h.D.K from inf_le_right))
  have hp2 : p ≠ 2 := by
    intro h2p
    have h2dvd : 2 ∣ Nat.card ↥B.U := by
      rw [← h2p]; exact dvd_trans hpK (Subgroup.card_dvd_of_le (Work.GW2.Case2Data.K_le_U B h.D))
    obtain ⟨m, hm⟩ := h2dvd
    obtain ⟨t, ht⟩ := B.U_odd
    omega
  have hpk : p ∣ k := by
    have hp2k : p ∣ 2 * k := by
      rw [hkm, ← mul_assoc]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpK 2) _
    rcases (Nat.Prime.dvd_mul hpp).mp hp2k with h1 | h1
    · exfalso
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2' | h2'
      · exact hpp.ne_one h2'
      · exact absurd h2' hp2
    · exact h1
  have hpne : p ≠ pF := by
    intro heq
    have hkF0 : kF ≠ 0 := by rintro rfl; simp at h7q
    have hdvdq : pF ∣ pF ^ kF := dvd_pow_self pF hkF0
    have hdvdk : pF ∣ k := heq ▸ hpk
    have hone1 : pF ∣ 1 := by
      rcases hdisj with ⟨h1, -⟩ | ⟨h1, -⟩
      · have h2' : pF ∣ pF ^ kF + 1 := by rw [← h1]; exact dvd_mul_of_dvd_right hdvdk 2
        exact (Nat.dvd_add_iff_right hdvdq).mpr h2'
      · have h2' : pF ∣ pF ^ kF - 1 := by rw [← h1]; exact dvd_mul_of_dvd_right hdvdk 2
        have h3 : pF ∣ 1 + (pF ^ kF - 1) := by
          rw [Nat.add_comm, Nat.sub_add_cancel (by omega : 1 ≤ pF ^ kF)]
          exact hdvdq
        exact (Nat.dvd_add_iff_left h2').mpr h3
    have h4 := Nat.le_of_dvd one_pos hone1
    have h5 := hpF.out.two_le
    omega
  -- The `L₂(q)` half: `|C_E(A ⊓ K)| ∈ {k, k'}`, and `K ⊔ S₀` has order `k`.
  set Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) :=
    Subgroup.map φ.toMonoidHom (Kp.subgroupOf (Work.GW2.layerIn h.D.M)) with hYdef
  have hYcard : Nat.card ↥Y = p := by
    rw [hYdef, Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKpE).toEquiv]
    exact hKpcard
  have hcardCM : Nat.card ↥(Subgroup.centralizer ((Kp : Subgroup G) : Set G) ⊓
        Work.GW2.layerIn h.D.M) =
      Nat.card ↥(Subgroup.centralizer
        (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) :=
    Case2CentA_card_centralizer_map φ hKpE
  obtain ⟨-, hdisjC, -⟩ :=
    I.l2torusNorm pF kF hpFodd (by omega : 5 ≤ pF ^ kF) p hpp hp2 hpne Y hYcard
  have hcase : Nat.card ↥(Subgroup.centralizer ((Kp : Subgroup G) : Set G) ⊓
        Work.GW2.layerIn h.D.M) = k ∨
      Nat.card ↥(Subgroup.centralizer ((Kp : Subgroup G) : Set G) ⊓
        Work.GW2.layerIn h.D.M) = k' := by
    rw [hcardCM]
    rcases hdisj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hdisjC with hc | hc
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have hk2 : 2 ≤ k := by
    have h2S0 : 2 ≤ Nat.card ↥B.S0 := by
      have h1 := Subgroup.orderOf_dvd_natCard B.S0 B.t_mem
      rw [B.t_order] at h1
      exact Nat.le_of_dvd (by norm_num) h1
    rw [hkm]
    calc 2 = 1 * 2 := by ring
      _ ≤ Nat.card ↥h.D.K * Nat.card ↥B.S0 :=
          Nat.mul_le_mul (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne')) h2S0
  have hkdvd : ¬ k ∣ k' := by
    intro hdvd
    have hkle : k ≤ k' := Nat.le_of_dvd (by omega) hdvd
    rcases hdisj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · have hk' : k' = k + 1 := by omega
      have h1' : k ∣ 1 := by
        have hsub : k ∣ k' - k := Nat.dvd_sub hdvd (dvd_refl k)
        rw [hk'] at hsub
        simpa using hsub
      have h2' : k ≤ 1 := Nat.le_of_dvd one_pos h1'
      omega
  have hKSU : h.D.K ⊔ B.S0 ≤ Subgroup.centralizer ((Kp : Subgroup G) : Set G) ⊓
      Work.GW2.layerIn h.D.M := le_inf hsup_le hsup_leE
  have heq : Nat.card ↥(Subgroup.centralizer ((Kp : Subgroup G) : Set G) ⊓
      Work.GW2.layerIn h.D.M) = k := by
    rcases hcase with h' | h'
    · exact h'
    · exfalso
      have hdvd : k ∣ k' := by
        have h'' := Subgroup.card_dvd_of_le hKSU
        rwa [hcardKS0k, h'] at h''
      exact hkdvd hdvd
  have hCoreKp : Subgroup.centralizer ((Kp : Subgroup G) : Set G) ⊓ Work.GW2.layerIn h.D.M =
      h.D.K ⊔ B.S0 :=
    (Subgroup.eq_of_le_of_card_ge hKSU (by rw [hcardKS0k, heq])).symm
  -- `C_G(A) ⊓ E = C_G(A ⊓ K) ⊓ E`
  have hPE : P ≤ Subgroup.centralizer ((Work.GW2.layerIn h.D.M : Subgroup G) : Set G) :=
    hPF_obj.trans (Work.GW2.Case2Pre.F_cent B h.D h.pre)
  have hsplit : Subgroup.centralizer ((A : Set G)) ⊓ Work.GW2.layerIn h.D.M =
      Subgroup.centralizer ((Kp : Subgroup G) : Set G) ⊓ Work.GW2.layerIn h.D.M := by
    refine Case2CentA_centralizer_inf_eq_of_eq_sup ?_ hPE
    rw [hKpdef]
    exact hAeq
  have hCore : Subgroup.centralizer ((A : Set G)) ⊓ Work.GW2.layerIn h.D.M = h.D.K ⊔ B.S0 := by
    rw [hsplit, hCoreKp]
  -- peel off the centralizing factor `P`
  have hcomm : ∀ x ∈ P, ∀ y ∈ Work.GW2.layerIn h.D.M, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF_obj hx))
      y hy).symm
  have hPc : P ≤ Subgroup.centralizer (A : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    haveI : Fact p.Prime := ⟨hpp⟩
    have hcommA : IsMulCommutative ↥A := IsPGroup.isMulCommutative_of_card_eq_prime_sq hAcard
    have h1 := congrArg Subtype.val
      (hcommA.is_comm.comm (⟨q, hPleA hq⟩ : ↥A) ⟨a, ha⟩)
    simp only [Subgroup.coe_mul] at h1
    exact h1.symm
  calc Subgroup.centralizer (A : Set G) ⊓ (P ⊔ Work.GW2.layerIn h.D.M)
      = P ⊔ (Subgroup.centralizer (A : Set G) ⊓ Work.GW2.layerIn h.D.M) :=
        Case2CentA_peel_centralizer hPc hcomm
    _ = P ⊔ (h.D.K ⊔ B.S0) := by rw [hCore]
    _ = P ⊔ h.D.K ⊔ B.S0 := by rw [sup_assoc]

end Work.CORE4
