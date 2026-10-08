import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs19
import Submission.Work.CORE4.LayerFactsProper
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2Setup9Fprops
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.SevenX.piFU_le_pi_K0F
import Submission.Work.CORE4.FpropsAux.mem_fittingIn_of_le_of_normal_isNilpotent
import Submission.Work.CORE4.KFP.SubgroupOf
import Submission.Work.CORE4.NineQuasisimpleSylowNotCyclic
import Submission.Work.RED.DihedralFacts
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic
import Submission.Work.CORE4.ZFacts
import Submission.Work.CORE4.fourGroup_in_layerIn_normalizer

open scoped MatrixGroups

namespace Work.CORE4

open Work.GW2 Subgroup

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## Two auxiliary lemmas

Both are "trivial" transports, but they are what makes the `QOddCent` application in the leaf
below typecheck. -/

/-- **Transport of quasisimplicity, oddness of the centre and the `A₇`/`L₂(q)` shape to a
`subgroupOf`.**  If `E ≤ E₀`, then `↥(E.subgroupOf E₀) ≃* ↥E` (`Subgroup.subgroupOfEquivOfLe`),
the centre is carried onto the centre (`Work.CORE4.map_center_mulEquiv`), and perfectness, the
simplicity of the central quotient and the two possible shapes all transport along that
isomorphism. -/
theorem quasisimple_shape_subgroupOf' {G : Type} [Group G] {E E₀ : Subgroup G} (h : E ≤ E₀)
    (hq : Work.GW2.IsQuasisimple E) (hodd : Odd (Nat.card (Subgroup.center ↥E)))
    (hshape : Nonempty (↥E ⧸ Subgroup.center ↥E ≃* alternatingGroup (Fin 7)) ∨
      ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty (↥E ⧸ Subgroup.center ↥E ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) :
    Work.GW2.IsQuasisimple (E.subgroupOf E₀) ∧
      Odd (Nat.card (Subgroup.center ↥(E.subgroupOf E₀))) ∧
      (Nonempty (↥(E.subgroupOf E₀) ⧸ Subgroup.center ↥(E.subgroupOf E₀) ≃*
          alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty (↥(E.subgroupOf E₀) ⧸ Subgroup.center ↥(E.subgroupOf E₀) ≃*
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
  set R : Subgroup ↥E₀ := E.subgroupOf E₀ with hRdef
  have e : ↥R ≃* ↥E := Subgroup.subgroupOfEquivOfLe h
  have hmap : (Subgroup.center ↥R).map (e : ↥R →* ↥E) = Subgroup.center ↥E :=
    Work.CORE4.map_center_mulEquiv e
  have hcongr : (↥R ⧸ Subgroup.center ↥R) ≃* (↥E ⧸ Subgroup.center ↥E) :=
    QuotientGroup.congr (Subgroup.center ↥R) (Subgroup.center ↥E) e hmap
  have hperfE : Group.IsPerfect ↥E := Subgroup.isPerfect_iff.mpr hq.1
  haveI hperfR : Group.IsPerfect ↥R :=
    Group.IsPerfect.ofSurjective (f := (e.symm : ↥E →* ↥R)) e.symm.surjective
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact Subgroup.isPerfect_iff.mp hperfR
  · haveI : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E) := hq.2
    exact Work.CORE4.isSimpleGroup_of_mulEquiv hcongr.symm
  · have hc : Nat.card ↥(Subgroup.center ↥R) = Nat.card ↥(Subgroup.center ↥E) := by
      rw [← Subgroup.card_map_of_injective (K := Subgroup.center ↥R)
        (f := (e : ↥R →* ↥E)) e.injective, hmap]
    rw [hc]; exact hodd
  · rcases hshape with hA | hB
    · obtain ⟨hA⟩ := hA
      exact Or.inl ⟨hcongr.trans hA⟩
    · obtain ⟨p, k, hpp, hpodd, h5, hY⟩ := hB
      obtain ⟨hiso⟩ := hY
      exact Or.inr ⟨p, k, hpp, hpodd, h5, ⟨hcongr.trans hiso⟩⟩

/-- **The centralizer step of Bender's §4 (Design-19 leaf S4).**

Let `F = D.F`, `K = N_G(X)`, `E = E(M)` and `E₀ = E(K)`.  If `X ≠ ⊥ ≤ F`, `t ∈ E₀` and
`E ≤ E₀`, then the centre `Z(F) = F ⊓ C_G(F)` of `F` centralizes `E₀`.

For `x ∈ Z(F)`:

* `x ∈ K` (it centralizes `F ⊇ X`), `x ∈ F ≤ F(U) ⊓ (K ⊓ C_G(t))`, a nilpotent normal subgroup of
  `K ⊓ C_G(t)` of odd order, so `x ∈ F_{2'}(C_K(t))` (`Work.CORE4.mem_fittingPiIn_of_odd_mem_fittingIn`
  with the `Fitting` plumbing of `Case2Setup9Fprops`);
* `I.toolkit.d110ii` applied to the D-group `↥K` (a proper subgroup of the `BenderCtx` group `G`,
  hence a D-group by `hbc.ih` and `DihOrCycSub`) produces `e ∈ E₀` with `x z x⁻¹ = e z e⁻¹` for
  all `z ∈ E₀`;
* since `F ≤ C_G(E)` and `E ≤ E₀`, the element `e` centralizes `E`; and `e^{|x|} ∈ Z(E₀)` because
  `x^{|x|} = 1` and `x` and `e` induce the same inner automorphism of `E₀`;
* `QOddCentProp` (at `Q := ↥E₀`, `R := E.subgroupOf E₀`, `V` a four-group of `E` lying in `E₀`,
  and the odd number `m := orderOf x`) then gives `e ∈ Z(E₀)`; the `E₀`-data (quasisimplicity, odd
  centre, `A₇`/`L₂(q)` shape) comes from `layer_facts_proper_quasisimple` at `K` (which needs
  `K ≠ ⊤`: `X ⊴ G` with `⊥ < X ≤ D.M < ⊤` would contradict simplicity) and at `M`.
* hence `x z x⁻¹ = e z e⁻¹ = z` for all `z ∈ E₀`. -/
theorem layerIn_normalizer_le_centralizer_ZF (I : Work.GW2.C4Inputs)
    (hQ : Work.GW2.C19.QOddCentProp I)
    {G : Type} [Group G] [Finite G] (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} {D : Work.GW2.Case2Data B} (hpre : Work.GW2.Case2Pre B D)
    {X : Subgroup G} (hX : X ≠ ⊥) (hXF : X ≤ D.F)
    (ht : B.t ∈ Work.GW2.layerIn (Subgroup.normalizer (X : Set G)))
    (hE0le : Work.GW2.layerIn D.M ≤ Work.GW2.layerIn (Subgroup.normalizer (X : Set G))) :
    D.F ⊓ Subgroup.centralizer (D.F : Set G) ≤
      Subgroup.centralizer
        ((Work.GW2.layerIn (Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G) := by
  classical
  intro x hx
  haveI hsimple : IsSimpleGroup G := hbc.simple
  obtain ⟨hnotH, honeClass, hKcyc, hUeq, hFne, hFcen, hNF, hB0⟩ := hpre
  have hFleU : D.F ≤ B.U := D.F_le_U B
  have hFleM : D.F ≤ D.M := le_trans (D.F_le_UinfM B) inf_le_right
  have hFleH : D.F ≤ B.H := hFleU.trans B.U_le_H
  have hFleFit : D.F ≤ Work.GW2.fittingIn B.U := D.F_le_fitting B
  have hxDF : x ∈ D.F := hx.1
  have hxCdf : x ∈ Subgroup.centralizer (D.F : Set G) := hx.2
  set K : Subgroup G := Subgroup.normalizer (X : Set G) with hKdef
  set E : Subgroup G := Work.GW2.layerIn D.M with hEdef
  set E0 : Subgroup G := Work.GW2.layerIn K with hE0def
  -- `K ≠ ⊤`: otherwise `X` would be a nontrivial proper normal subgroup of `G`
  have hKtop : K ≠ ⊤ := by
    intro htop
    have hXnorm : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have hXM : X ≤ D.M := hXF.trans hFleM
    have hXtop : X ≠ ⊤ := fun h1 => D.M_coatom.ne_top (top_le_iff.mp (h1 ▸ hXM))
    rcases hXnorm.eq_bot_or_eq_top with hb | htp
    · exact hX hb
    · exact hXtop htp
  have htK : B.t ∈ K := Work.CORE4.layerIn_le K ht
  -- ## `x ∈ K`
  have hxK : x ∈ K := by
    have hxcenX : x ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_iff.mp hxCdf y (hXF hy)
    exact Subgroup.centralizer_le_normalizer (X : Set G) hxcenX
  have hxH : x ∈ B.H := hFleH hxDF
  have hxU : x ∈ B.U := hFleU hxDF
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat B.U_odd (Subgroup.orderOf_dvd_natCard B.U hxU)
  have hxFit : x ∈ Work.GW2.fittingIn B.U := hFleFit hxDF
  have hxKH : x ∈ K ⊓ B.H := Subgroup.mem_inf.mpr ⟨hxK, hxH⟩
  -- ## `x ∈ F_{2'}(C_K(t))` (the plumbing of `Case2Setup9Fprops`)
  haveI : Group.IsNilpotent ↥(Work.GW2.fittingIn B.U) := SevenX.PiFU.isNilpotent_fittingIn B.U
  have hYnorm : ((Work.GW2.fittingIn B.U ⊓ (K ⊓ B.H)).subgroupOf (K ⊓ B.H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    refine Subgroup.mem_inf.mpr ⟨?_, (K ⊓ B.H).mul_mem
      ((K ⊓ B.H).mul_mem hk (Subgroup.mem_inf.mp hh).2) ((K ⊓ B.H).inv_mem hk)⟩
    exact (Subgroup.le_normalizer_iff.mp (BenderSetup.H_le_normalizer_fittingIn B)) k
      (Subgroup.mem_inf.mp hk).2 h (Subgroup.mem_inf.mp hh).1
  have hYnil : Group.IsNilpotent ↥(Work.GW2.fittingIn B.U ⊓ (K ⊓ B.H)) :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : Work.GW2.fittingIn B.U ⊓ (K ⊓ B.H) ≤
        Work.GW2.fittingIn B.U))
  have hxFitting : x ∈ Work.GW2.fittingIn (K ⊓ B.H) :=
    FpropsAux.mem_fittingIn_of_le_of_normal_isNilpotent
      (M₀ := K ⊓ B.H) (Y := Work.GW2.fittingIn B.U ⊓ (K ⊓ B.H)) inf_le_right hYnorm hYnil
      (Subgroup.mem_inf.mpr ⟨hxFit, hxKH⟩)
  have hxPiIn : x ∈ Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) (K ⊓ B.H) :=
    mem_fittingPiIn_of_odd_mem_fittingIn (K ⊓ B.H) hxFitting hxodd
  have hxSub : (⟨x, hxK⟩ : ↥K) ∈
      Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) ((K ⊓ B.H).subgroupOf K) :=
    KFP.fittingPiIn_subgroupOf (K ⊓ B.H) K inf_le_left x hxKH hxPiIn
  have hcenEq : Subgroup.centralizer ({⟨B.t, htK⟩} : Set ↥K) = (K ⊓ B.H).subgroupOf K := by
    ext z
    constructor
    · intro hz
      have hz' : (z : G) * B.t = B.t * (z : G) :=
        congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hz)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨z.2, Subgroup.mem_centralizer_singleton_iff.mpr hz'⟩
    · intro hz
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hz.2)
  have hxcen : (⟨x, hxK⟩ : ↥K) ∈ Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ)
      (Subgroup.centralizer ({⟨B.t, htK⟩} : Set ↥K)) := by
    rw [hcenEq]
    exact hxSub
  -- ## Bender's 1.10(ii) at the D-group `↥K`
  have hDsyl : Work.GW2.DihOrCycSylow ↥K := DihOrCycSub hbc.sylow K
  have hDisD : Work.GW2.IsDGroup ↥K :=
    hbc.ih ↥K (card_lt_card_of_ne_top hKtop) hDsyl
  obtain ⟨e0, he0mem, he0conj⟩ :=
    I.toolkit.d110ii ↥K I.toolkit.ft hDsyl hDisD (⟨B.t, htK⟩ : ↥K)
      ((Subgroup.orderOf_coe (⟨B.t, htK⟩ : ↥K)).symm.trans B.t_order) (⟨x, hxK⟩ : ↥K) hxcen
  have he0E0 : (e0 : G) ∈ E0 := by
    show (e0 : G) ∈ Work.GW2.layerIn K
    rw [Work.GW2.layerIn]
    exact Subgroup.mem_map_of_mem K.subtype he0mem
  have hKE0 : K ≤ Subgroup.normalizer (E0 : Set G) := by
    rw [hE0def]
    exact Work.CORE4.layerIn_le_normalizer K
  have he_conj : ∀ z ∈ E0, x * z * x⁻¹ = (e0 : G) * z * (e0 : G)⁻¹ := by
    intro z hz
    obtain ⟨z0, hz0mem, hz0eq⟩ := Subgroup.mem_map.mp
      (show z ∈ (Work.GW2.layer ↥K).map K.subtype from hz)
    have h := he0conj z0 hz0mem
    have h' : x * (z0 : G) * x⁻¹ = (e0 : G) * (z0 : G) * (e0 : G)⁻¹ :=
      congrArg (fun w : ↥K => (w : G)) h
    have hz0eq' : (z0 : G) = z := hz0eq
    rw [hz0eq'] at h'
    exact h'
  have hpow : ∀ n : ℕ, ∀ z ∈ E0,
      x ^ n * z * (x ^ n)⁻¹ = (e0 : G) ^ n * z * ((e0 : G) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro z hz; simp
    | succ k ih =>
        intro z hz
        have hz1 : x * z * x⁻¹ ∈ E0 := (Subgroup.le_normalizer_iff.mp hKE0) x hxK z hz
        have hkey : x * z * x⁻¹ = (e0 : G) * z * (e0 : G)⁻¹ := he_conj z hz
        calc x ^ (k + 1) * z * (x ^ (k + 1))⁻¹
            = x ^ k * (x * z * x⁻¹) * (x ^ k)⁻¹ := by rw [pow_succ]; group
          _ = x ^ k * ((e0 : G) * z * (e0 : G)⁻¹) * (x ^ k)⁻¹ := by rw [hkey]
          _ = (e0 : G) ^ k * ((e0 : G) * z * (e0 : G)⁻¹) * ((e0 : G) ^ k)⁻¹ :=
                ih ((e0 : G) * z * (e0 : G)⁻¹) (by rw [← hkey]; exact hz1)
          _ = (e0 : G) ^ (k + 1) * z * ((e0 : G) ^ (k + 1))⁻¹ := by rw [pow_succ]; group
  have he0powC : (e0 : G) ^ orderOf x ∈ Subgroup.centralizer ((E0 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h0 : z = (e0 : G) ^ orderOf x * z * ((e0 : G) ^ orderOf x)⁻¹ := by
      have h := hpow (orderOf x) z hz
      rw [pow_orderOf_eq_one] at h
      simpa using h
    calc z * (e0 : G) ^ orderOf x
        = ((e0 : G) ^ orderOf x * z * ((e0 : G) ^ orderOf x)⁻¹) * (e0 : G) ^ orderOf x := by
          conv_lhs => rw [h0]
      _ = (e0 : G) ^ orderOf x * z := by group
  have he0powcenter : (⟨e0, he0E0⟩ : ↥E0) ^ orderOf x ∈ Subgroup.center ↥E0 := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := Subgroup.mem_centralizer_iff.mp he0powC (g : G) g.2
    refine Subtype.ext ?_
    simpa using h
  -- ## The `E₀`-data for `QOddCent`
  obtain ⟨E1, hE1norm, hlayer1, hE1q, hZodd1, hshape1⟩ :=
    Work.CORE4.layer_facts_proper_quasisimple I hbc hKtop ht
  have hE0eq : E0 = E1.map K.subtype := by
    rw [hE0def, Work.GW2.layerIn, hlayer1]
  have hqK := Work.CORE4.quasisimple_shape_map K.subtype (Subgroup.subtype_injective K)
    hE1q hZodd1 hshape1
  have hZoddE0 : Odd (Nat.card (Subgroup.center ↥E0)) := by rw [hE0eq]; exact hqK.2.1
  have hshapeE0 : (Nonempty (↥E0 ⧸ Subgroup.center ↥E0 ≃* alternatingGroup (Fin 7)) ∨
      ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty (↥E0 ⧸ Subgroup.center ↥E0 ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
    rw [hE0eq]; exact hqK.2.2
  -- ## The `E`-data for `QOddCent`
  obtain ⟨Em, hEmnorm, hlayerM, hEmq, hZoddM, hshapeM⟩ :=
    Work.CORE4.layer_facts_proper_quasisimple (B := B) (M := D.M) I hbc
      D.M_coatom.ne_top D.t_mem
  have hEeq : E = Em.map D.M.subtype := by
    rw [hEdef, Work.GW2.layerIn, hlayerM]
  have hqM := Work.CORE4.quasisimple_shape_map D.M.subtype (Subgroup.subtype_injective D.M)
    hEmq hZoddM hshapeM
  have hQE : Work.GW2.IsQuasisimple E := by rw [hEeq]; exact hqM.1
  have hZoddE : Odd (Nat.card (Subgroup.center ↥E)) := by rw [hEeq]; exact hqM.2.1
  have hshapeE : (Nonempty (↥E ⧸ Subgroup.center ↥E ≃* alternatingGroup (Fin 7)) ∨
      ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty (↥E ⧸ Subgroup.center ↥E ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
    rw [hEeq]; exact hqM.2.2
  obtain ⟨hQR, -, hshapeR⟩ :=
    quasisimple_shape_subgroupOf' (E := E) (E₀ := E0) hE0le hQE hZoddE hshapeE
  obtain ⟨V, hVle, hV4⟩ :=
    fourGroup_in_layerIn_normalizer hbc hX hXF
      (show B.t ∈ Work.GW2.layerIn (Subgroup.normalizer (X : Set G)) from ht)
      (show Work.GW2.layerIn D.M ≤ Work.GW2.layerIn (Subgroup.normalizer (X : Set G)) from hE0le)
  -- ## `e0` centralizes `E`
  have he0cE : (e0 : G) ∈ Subgroup.centralizer ((E : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : x * y * x⁻¹ = y := by
      have h3 : y * x = x * y := Subgroup.mem_centralizer_iff.mp (hFcen hxDF) y hy
      calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [h3]
        _ = y := by group
    have h2 : x * y * x⁻¹ = (e0 : G) * y * (e0 : G)⁻¹ := he_conj y (hE0le hy)
    have h4 : (e0 : G) * y * (e0 : G)⁻¹ = y := h2.symm.trans h1
    calc y * (e0 : G) = ((e0 : G) * y * (e0 : G)⁻¹) * (e0 : G) := by rw [h4]
      _ = (e0 : G) * y := by group
  have he0cenR : (⟨e0, he0E0⟩ : ↥E0) ∈
      Subgroup.centralizer (((E.subgroupOf E0 : Subgroup ↥E0)) : Set ↥E0) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwE : (w : G) ∈ E := Subgroup.mem_subgroupOf.mp hw
    have hcomm : (w : G) * (e0 : G) = (e0 : G) * (w : G) :=
      Subgroup.mem_centralizer_iff.mp he0cE (w : G) hwE
    exact Subtype.ext hcomm
  -- ## `QOddCent`
  have he0center : (⟨e0, he0E0⟩ : ↥E0) ∈ Subgroup.center ↥E0 :=
    hQ ↥E0 hshapeE0 hZoddE0 (E.subgroupOf E0) hQR hshapeR V hVle hV4 (⟨e0, he0E0⟩ : ↥E0)
      he0cenR ⟨orderOf x, hxodd, he0powcenter⟩
  -- ## conclude
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have h := he_conj z hz
  have hc : (e0 : G) * z * (e0 : G)⁻¹ = z := by
    have hcc : (⟨z, hz⟩ : ↥E0) * (⟨e0, he0E0⟩ : ↥E0) = (⟨e0, he0E0⟩ : ↥E0) * ⟨z, hz⟩ :=
      Subgroup.mem_center_iff.mp he0center ⟨z, hz⟩
    have hcc' : z * (e0 : G) = (e0 : G) * z := by
      simpa using congrArg (fun w : ↥E0 => (w : G)) hcc
    calc (e0 : G) * z * (e0 : G)⁻¹ = (z * (e0 : G)) * (e0 : G)⁻¹ := by rw [hcc']
      _ = z := by group
  have hxzz : x * z * x⁻¹ = z := by rw [h, hc]
  have hfin : x * z = z * x := by
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [hxzz]
  exact hfin.symm

/-- **Design-19 leaf S4**: `E₀ := E(N_G(X)) ≤ M` (Bender: "… `E(N_G(X)) ≤ C_G(N_G(X)) ≤ C_G(Z(F)) ≤ M`").

Statement (verbatim): `QOddCentProp I → SixLayerNLeMProp I`, i.e. given `QOddCent` (the model leaf
`CORE4/QOddCent`), for `BenderCtx G`, `B`, `D` with `Case2Pre B D`, `X ≠ ⊥`, `X ≤ D.F`,
`B.t ∈ layerIn (N_G(X))` (S2) and `layerIn D.M ≤ layerIn (N_G(X))` (S3):
`layerIn (N_G(X)) ≤ D.M`.

Route.  Put `Y := Z(F) = F ⊓ C_G(F)`; `Y ≠ 1` (`F ≠ 1` nilpotent, `F ≤ F(U)`), `Y ⊴ M`
(`N_G(F) = M`), so `N_G(Y) = M` (coatom + simplicity) and `C_G(Y) ≤ M`.  It suffices to show that
every `x ∈ Y` centralizes `E₀`:
* `x ∈ F_{2'}(C_{N_G(X)}(t))`: `x ∈ F(U) ⊓ N_G(X)`, normal nilpotent of odd order in
  `H ⊓ N_G(X)`; use `Work.CORE4.mem_fittingPiIn_of_odd_mem_fittingIn` (the plumbing is the
  template of `Submission.Work.CORE4/Case2Setup9Fprops.lean` ll. 240–290, with `↥N_G(X)` in place
  of `↥M`);
* `I.toolkit.d110ii` applied to the D-group `↥N_G(X)` (`BenderCtx.ih` at the proper subgroup
  `N_G(X)`, `DihOrCycSub`) gives `e ∈ E₀` with `x y x⁻¹ = e y e⁻¹` for all `y ∈ E₀`; by S3 and
  `x ∈ F ≤ C_G(E)`, the element `e` centralizes `E`, and `e^{|x|} ∈ Z(E₀)` with `|x|` odd;
* `QOddCent` at `Q := ↥E₀`, `R := E`, `V` a four-group of `E` gives `e ∈ Z(E₀)`, hence `x`
  centralizes `E₀`.  (`E₀` is quasisimple with odd centre and `A₇`/`L₂(q)` shape by
  `Work.CORE4.layer_facts_proper_quasisimple` at `N_G(X)` — it needs only `N_G(X) ≠ ⊤`, and
  `t ∈ E₀` makes `E₀ ≠ 1`.) -/
theorem SixLayerNLeM (I : Work.GW2.C4Inputs) :
    Work.GW2.C19.QOddCentProp I → Work.GW2.C19.SixLayerNLeMProp I := by
  intro hQ G _ _ hbc B D hpre X hX hXF ht hE0le
  set K : Subgroup G := Subgroup.normalizer (X : Set G) with hKdef
  set E0 : Subgroup G := Work.GW2.layerIn K with hE0def
  -- `Y := Z(F) = F ⊓ C_G(F)` is nontrivial with `N_G(Y) = M` (`Work.CORE4.ZFacts`)
  obtain ⟨hZne, hZN⟩ := Work.CORE4.ZFacts hbc hpre
  -- `E₀ ≤ C_G(Y)`
  have hZle : (D.F ⊓ Subgroup.centralizer (D.F : Set G)) ≤
      Subgroup.centralizer ((E0 : Subgroup G) : Set G) :=
    layerIn_normalizer_le_centralizer_ZF I hQ hbc hpre hX hXF ht hE0le
  have hE0leC : E0 ≤
      Subgroup.centralizer
        (((D.F ⊓ Subgroup.centralizer (D.F : Set G)) : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hZle hz) y hy).symm
  -- `C_G(Y) ≤ N_G(Y) = M`
  have hE0leN : E0 ≤
      Subgroup.normalizer
        (((D.F ⊓ Subgroup.centralizer (D.F : Set G)) : Subgroup G) : Set G) :=
    le_trans hE0leC
      (Subgroup.centralizer_le_normalizer
        (((D.F ⊓ Subgroup.centralizer (D.F : Set G)) : Subgroup G) : Set G))
  rw [hZN] at hE0leN
  exact hE0leN

end Work.CORE4
