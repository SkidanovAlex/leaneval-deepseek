import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2EightA_le_FsupK0
import Submission.Work.CORE4.Case2CU_s

/-!
# `Work.CORE4Qsub.A_le_pCoreInU`

Bender 1981, §4 (8), p. 225–226.  For the `(p,p)`-subgroup `A` of §4 (8) (the unique subgroup of
`F ⊔ K` of order `p²` and exponent `p`, where `F = B₀ ⊓ F(U)`, `K = I_{U⊓M}(s)`), we prove

* `A ≤ O_p(U)` (`pCoreIn p B.U`),
* `O_p(U)` is not cyclic,
* `p` is odd,
* `O_p(U)` is a `p`-group.

Mathematics.  By §4 (8) (as formalised in `Work.CORE4.Case2EightA_le_FsupK0`) the subgroup `A`
actually lies in `F ⊔ K₀` with `K₀ = F(U) ⊓ K`.  Both `F ≤ F(U)` and `K₀ ≤ F(U)`, so
`A ≤ F(U)`.  The Fitting subgroup `F(U)` is nilpotent, and in a finite nilpotent group every
`p`-subgroup lies in the (unique, hence normal) Sylow `p`-subgroup, which is `O_p(F(U))`; since
`F(U) ⊴ U` the `p`-core is characteristic, so `O_p(F(U)) ≤ O_p(U)` and `A ≤ O_p(U)`.  Finally `A`
is elementary abelian of order `p²`, hence not cyclic, so neither is its overgroup `O_p(U)`; and
`p ∣ |A| = p` divides `|U|`, which is odd (as `U = O(H)`).

The file develops the small amount of general group theory used above
(`p`-subgroups of nilpotent subgroups, characteristicity of `O_p`).  It mirrors
`Work.BMAX.pCoreIn_inf_pResidualIn_fittingIn_eq_bot`, but for the `Work.GW2` vocabulary of area
`CORE4` (the two copies of `Work.GW2` cannot be imported together).
-/

namespace Work.CORE4Qsub

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Basic API of the `p`-core `O_p(K)`, viewed in `G` -/

/-- `O_p(K)`, viewed in `G`, is a `p`-group. -/
theorem isPGroup_pCoreIn (p : ℕ) (K : Subgroup G) : IsPGroup p (Work.GW2.pCoreIn p K) := by
  have hsup : IsPGroup p ↥(sSup {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}) :=
    Sylow.sSup_of_normal {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}
      (fun N hN => hN.2) (fun N hN => hN.1)
  exact (hsup.to_le (Subgroup.normalCore_le _)).map K.subtype

/-- `O_p(K) ≤ K`. -/
theorem pCoreIn_le_self (p : ℕ) (K : Subgroup G) : Work.GW2.pCoreIn p K ≤ K :=
  Subgroup.map_subtype_le _

/-- Universal property of `O_p(K)`: a normal `p`-subgroup of `K` lies in it. -/
theorem le_pCoreIn_of_normal_isPGroup (p : ℕ) (K : Subgroup G) {A : Subgroup G} (hA : A ≤ K)
    (hAn : (A.subgroupOf K).Normal) (hAp : IsPGroup p (A.subgroupOf K)) :
    A ≤ Work.GW2.pCoreIn p K := by
  haveI := hAn
  have h1 : A.subgroupOf K ≤ Work.GW2.pCore p (↥K) :=
    Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hAn, hAp⟩)
  calc A = (A.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hA).symm
    _ ≤ (Work.GW2.pCore p (↥K)).map K.subtype := Subgroup.map_mono h1
    _ = Work.GW2.pCoreIn p K := rfl

/-! ## 2. `O_p` is characteristic -/

/-- The normal core of a characteristic subgroup is characteristic. -/
theorem characteristic_normalCore {H : Subgroup G} (hH : H.Characteristic) :
    H.normalCore.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  haveI : (H.normalCore.map φ.toMonoidHom).Normal :=
    Subgroup.Normal.map H.normalCore_normal φ.toMonoidHom φ.surjective
  refine Subgroup.normal_le_normalCore.mpr ?_
  calc H.normalCore.map φ.toMonoidHom ≤ H.map φ.toMonoidHom := Subgroup.map_mono H.normalCore_le
    _ = H := Subgroup.characteristic_iff_map_eq.mp hH φ

/-- The join of all the normal `p`-subgroups of a group is characteristic: an automorphism
permutes the family it is the join of. -/
theorem characteristic_sSup_normal_isPGroup (p : ℕ) :
    (sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN x hx => ?_
  rw [Subgroup.mem_comap]
  exact (le_sSup (s := {N : Subgroup G | N.Normal ∧ IsPGroup p N})
    ⟨Subgroup.Normal.map hN.1 φ.toMonoidHom φ.surjective, hN.2.map φ.toMonoidHom⟩)
    (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

/-- `O_p(M)` is characteristic in `M` (for every `p : ℕ`). -/
theorem pCore_characteristic (p : ℕ) : (Work.GW2.pCore p G).Characteristic := by
  rw [Work.GW2.pCore]
  exact characteristic_normalCore (characteristic_sSup_normal_isPGroup (G := G) p)

/-- A subgroup `C` normalising `K` normalises the image in `G` of any subgroup of `↥K` that is
characteristic in `↥K`. -/
theorem le_normalizer_map_subtype_of_characteristic {K C : Subgroup G}
    {H : Subgroup ↥K} (hH : H.Characteristic)
    (h : C ≤ Subgroup.normalizer (K : Set G)) :
    C ≤ Subgroup.normalizer ((H.map K.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff] at h ⊢
  intro c hc x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  -- conjugation by `c` is an automorphism of `↥K`
  let φ : ↥K ≃* ↥K := {
    toFun := fun z => ⟨c * (z : G) * c⁻¹, h c hc z z.2⟩
    invFun := fun z => ⟨c⁻¹ * (z : G) * c, by
      have hh := h c⁻¹ (C.inv_mem hc) z z.2
      rwa [inv_inv] at hh⟩
    left_inv := by intro z; ext; simp [mul_assoc]
    right_inv := by intro z; ext; simp [mul_assoc]
    map_mul' := by intro z w; ext; simp [mul_assoc] }
  refine Subgroup.mem_map.mpr ⟨φ y, ?_, rfl⟩
  exact (Subgroup.characteristic_iff_map_le.mp hH φ) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)

/-- `O_p(N) ≤ O_p(X)` for a normal subgroup `N ⊴ X`: `O_p(N)` is characteristic in `N`, hence
normal in `X`, and it is a `p`-group. -/
theorem pCoreIn_le_pCoreIn_of_le_normal {N X : Subgroup G} (hNX : N ≤ X)
    (hNn : (N.subgroupOf X).Normal) (p : ℕ) : Work.GW2.pCoreIn p N ≤ Work.GW2.pCoreIn p X := by
  have hXnorm : X ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mp hNn
  have hXnpc : X ≤ Subgroup.normalizer ((Work.GW2.pCoreIn p N : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_of_characteristic (pCore_characteristic (G := ↥N) p) hXnorm
  have hle : Work.GW2.pCoreIn p N ≤ X := (pCoreIn_le_self p N).trans hNX
  refine le_pCoreIn_of_normal_isPGroup p X hle
    (Subgroup.normal_subgroupOf_of_le_normalizer hXnpc) ?_
  exact IsPGroup.of_equiv (isPGroup_pCoreIn p N) (Subgroup.subgroupOfEquivOfLe hle).symm

/-! ## 3. `p`-subgroups of finite nilpotent groups -/

/-- **Every `p`-subgroup of a finite nilpotent group lies in `O_p`**: it is contained in some
Sylow `p`-subgroup, which is normal because the group is nilpotent. -/
theorem le_pCore_of_isPGroup_of_isNilpotent {M : Type} [Group M] [Finite M]
    [Group.IsNilpotent M] {p : ℕ} [Fact p.Prime] {X : Subgroup M} (hX : IsPGroup p X) :
    X ≤ Work.GW2.pCore p M := by
  obtain ⟨Q, hXQ⟩ := hX.exists_le_sylow
  haveI : (Q : Subgroup M).Normal := inferInstance
  exact hXQ.trans (Subgroup.normal_le_normalCore.mpr (le_sSup ⟨inferInstance, Q.isPGroup'⟩))

/-- **Every `p`-subgroup of a nilpotent subgroup `H ≤ G` lies in `O_p(H)`.**  No normality of the
`p`-subgroup is needed.  Transported from the group `↥H` to `G` along the inclusion. -/
theorem le_pCoreIn_of_isPGroup_of_isNilpotent (H : Subgroup G) [Group.IsNilpotent ↥H]
    {p : ℕ} [Fact p.Prime] {Y : Subgroup G} (hYH : Y ≤ H) (hY : IsPGroup p ↥Y) :
    Y ≤ Work.GW2.pCoreIn p H := by
  have hcm : IsPGroup p ↥(Subgroup.comap H.subtype Y) :=
    IsPGroup.of_equiv hY (Subgroup.subgroupOfEquivOfLe hYH).symm
  have hle : Subgroup.comap H.subtype Y ≤ Work.GW2.pCore p ↥H :=
    le_pCore_of_isPGroup_of_isNilpotent hcm
  have hmap : Subgroup.map H.subtype (Subgroup.comap H.subtype Y) = Y :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.subtype_range]; exact hYH)
  calc Y = Subgroup.map H.subtype (Subgroup.comap H.subtype Y) := hmap.symm
    _ ≤ Subgroup.map H.subtype (Work.GW2.pCore p ↥H) := Subgroup.map_mono hle
    _ = Work.GW2.pCoreIn p H := rfl

/-! ## 4. The target -/

/-- Bender 1981, §4 (8): the `(p,p)`-subgroup `A` of `F ⊔ K` lies in `O_p(U) = pCoreIn p B.U`,
which is therefore non-cyclic and a `p`-group of odd prime order. -/
theorem A_le_pCoreInU (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case2 B → ∀ C : Work.GW2.Case2Ctx6 B, Work.GW2.Case2PrePlus B C.D →
        Work.GW2.Case2SevenFacts B C.D →
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
          Work.GW2.Case2EightObj C.D p P A →
          A ≤ Work.GW2.pCoreIn p B.U ∧ ¬ IsCyclic ↥(Work.GW2.pCoreIn p B.U) ∧
            Odd p ∧ IsPGroup p ↥(Work.GW2.pCoreIn p B.U) := by
  intro G _ _ hbc B h2 C hplus h7 p P A hp hPF hPcard hObj
  haveI : Fact p.Prime := ⟨hp⟩
  have hAcard : Nat.card ↥A = p ^ 2 := hObj.2.2.2.2.1
  have hAexp : ∀ x ∈ A, x ^ p = 1 := hObj.2.2.2.2.2.1
  -- Step 1: `A ≤ F ⊔ K₀ ≤ F(U)` (`§4 (8)`, `K₀ = F(U) ⊓ K`)
  have hAleK0 : A ≤ C.D.F ⊔ C.D.K0 :=
    Work.CORE4.Case2EightA_le_FsupK0 I G hbc B h2 C hplus h7 p P A hp hPF hPcard hObj
  have hK0le : C.D.K0 ≤ Work.GW2.fittingIn B.U := by
    change Work.GW2.fittingIn B.U ⊓ C.D.K ≤ Work.GW2.fittingIn B.U
    exact inf_le_left
  have hAleFU : A ≤ Work.GW2.fittingIn B.U :=
    hAleK0.trans (sup_le (Work.GW2.Case2Data.F_le_fitting B C.D) hK0le)
  -- Step 2: `A`, an elementary abelian `p`-group of order `p²`, lies in `O_p(F(U))`
  haveI hFUnil : Group.IsNilpotent ↥(Work.GW2.fittingIn B.U) :=
    Work.CORE4.isNilpotent_fittingIn_area B.U
  have hAp : IsPGroup p ↥A := IsPGroup.iff_card.mpr ⟨2, hAcard⟩
  have hAleOPFU : A ≤ Work.GW2.pCoreIn p (Work.GW2.fittingIn B.U) :=
    le_pCoreIn_of_isPGroup_of_isNilpotent (Work.GW2.fittingIn B.U) hAleFU hAp
  -- Step 3: `O_p(F(U)) ≤ O_p(U)` since `F(U) ⊴ U`
  have hFUle : Work.GW2.fittingIn B.U ≤ B.U :=
    Subgroup.map_subtype_le (Work.GW2.fitting ↥(B.U))
  have hNnorm : ((Work.GW2.fittingIn B.U).subgroupOf B.U).Normal := by
    have h : (Work.GW2.fittingIn B.U).subgroupOf B.U = Work.GW2.fitting ↥(B.U) := by
      rw [Work.GW2.fittingIn]
      exact Subgroup.comap_map_eq_self_of_injective B.U.subtype_injective _
    rw [h]
    exact Subgroup.normalCore_normal _
  have hAleOPU : A ≤ Work.GW2.pCoreIn p B.U :=
    hAleOPFU.trans (pCoreIn_le_pCoreIn_of_le_normal hFUle hNnorm p)
  refine ⟨hAleOPU, ?_, ?_, ?_⟩
  · -- `O_p(U)` is not cyclic: it contains the elementary abelian group `A` of order `p²`
    have hAnc : ¬ IsCyclic ↥A := by
      intro hcyc
      haveI : IsCyclic ↥A := hcyc
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥A)
      have hgpow : g ^ p = 1 := by
        apply Subtype.ext
        simpa using hAexp (g : G) g.2
      have hdvd : orderOf g ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hgpow
      rw [hg, hAcard] at hdvd
      have hle : p * p ≤ p := by simpa [pow_two] using Nat.le_of_dvd hp.pos hdvd
      have hp1 : p ≤ 1 := Nat.le_of_mul_le_mul_left (by simpa using hle) hp.pos
      have hp2 : 2 ≤ p := hp.two_le
      omega
    intro hcyc
    haveI : IsCyclic ↥(Work.GW2.pCoreIn p B.U) := hcyc
    exact hAnc (isCyclic_of_le hAleOPU)
  · -- `p` is odd: it divides `|U|`, which is odd as `U = O(H)`
    have hdvd : p ∣ Nat.card ↥B.U := by
      have h1 : p ∣ Nat.card ↥C.D.F := by
        rw [← hPcard]
        exact Subgroup.card_dvd_of_le hPF
      exact h1.trans (Subgroup.card_dvd_of_le (Work.GW2.Case2Data.F_le_U B C.D))
    have hUodd : Odd (Nat.card ↥B.U) := by
      have h : Nat.card ↥B.U = Nat.card ↥(Work.GW2.oddCore ↥(B.H)) :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective B.H)
      rw [h]
      exact Work.CORE4.oddCore_odd ↥(B.H)
    exact Odd.of_dvd_nat hUodd hdvd
  · exact isPGroup_pCoreIn p B.U

end Work.CORE4Qsub
