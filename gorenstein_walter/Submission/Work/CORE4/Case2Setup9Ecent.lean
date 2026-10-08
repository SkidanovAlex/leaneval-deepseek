import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.Case2LayerOneInvClass
import Submission.Work.CORE4.Ecent.alt7_odd_centralizer_sylow
import Submission.Work.CORE4.Ecent.psl_odd_centralizer_sylow
import Submission.OddOrder.Isaacs.Ch09_MoreSubnormality.SylowSubnormal

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## The abstract centre lemma

Let `Q` be a finite group with `Q ⧸ Z(Q) ≅ A₇` or `Q ⧸ Z(Q) ≅ PSL(2,q)` (`q = p^k`, `p` odd,
`q ≥ 5`).  If `x ∈ Q` has odd order and centralises a Sylow 2-subgroup `S` of `Q`, then `x ∈ Z(Q)`.

Indeed the image `x̄` of `x` in `Q ⧸ Z(Q)` has odd order and centralises the image `S̄` of the Sylow
`S` (`Sylow.mapSurjective`), which is a Sylow of the quotient; and in `A₇` (resp. `PSL(2,q)`), an
odd-order element centralising a Sylow 2-subgroup is trivial (`hA7`, `hL2`).  Hence `x̄ = 1`, i.e.
`x ∈ Z(Q)`. -/

theorem odd_mem_center_of_centralizer_sylow (Q : Type) [Group Q] [Finite Q]
    (hA7 : ∀ (D : Sylow 2 (alternatingGroup (Fin 7))) (x : alternatingGroup (Fin 7)),
      x ∈ Subgroup.centralizer
        ((D : Subgroup (alternatingGroup (Fin 7))) : Set (alternatingGroup (Fin 7))) →
      Odd (orderOf x) → x = 1)
    (hL2 : ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
      ∀ (D : Sylow 2 (PSL(2, GaloisField p k))) (x : PSL(2, GaloisField p k)),
      x ∈ Subgroup.centralizer
        ((D : Subgroup (PSL(2, GaloisField p k))) : Set (PSL(2, GaloisField p k))) →
      Odd (orderOf x) → x = 1)
    (hshape : Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 7)) ∨
      ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty (Q ⧸ Subgroup.center Q ≃* PSL(2, GaloisField p k)))
    (S : Sylow 2 Q) (x : Q) (hxodd : Odd (orderOf x))
    (hc : x ∈ Subgroup.centralizer ((S : Subgroup Q) : Set Q)) :
    x ∈ Subgroup.center Q := by
  classical
  set mk : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q) with hmk
  have hmksurj : Function.Surjective mk := QuotientGroup.mk'_surjective (Subgroup.center Q)
  set D : Sylow 2 (Q ⧸ Subgroup.center Q) := Sylow.mapSurjective hmksurj S with hD
  have hDcoe : (D : Subgroup (Q ⧸ Subgroup.center Q)) = (S : Subgroup Q).map mk :=
    Sylow.coe_mapSurjective hmksurj S
  have hxodd' : Odd (orderOf (mk x)) := Odd.of_dvd_nat hxodd (orderOf_map_dvd mk x)
  have hc' : mk x ∈ Subgroup.centralizer
      ((D : Subgroup (Q ⧸ Subgroup.center Q)) : Set (Q ⧸ Subgroup.center Q)) := by
    rw [hDcoe, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hh
    rw [← map_mul, ← map_mul]
    exact congrArg mk (Subgroup.mem_centralizer_iff.mp hc s hs)
  have hkey : mk x = 1 := by
    rcases hshape with hA | ⟨p, k, hpp, hp, hq, hB⟩
    · -- `A₇`
      obtain ⟨φ⟩ := hA
      set D7 : Sylow 2 (alternatingGroup (Fin 7)) :=
        Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective D with hD7
      have hcoe7 : (D7 : Subgroup (alternatingGroup (Fin 7))) =
          (D : Subgroup (Q ⧸ Subgroup.center Q)).map φ.toMonoidHom :=
        Sylow.coe_mapSurjective (f := φ.toMonoidHom) φ.surjective D
      have hc7 : φ (mk x) ∈ Subgroup.centralizer
          ((D7 : Subgroup (alternatingGroup (Fin 7))) : Set (alternatingGroup (Fin 7))) := by
        rw [hcoe7, Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hh
        change φ.toMonoidHom d * φ.toMonoidHom (mk x) =
          φ.toMonoidHom (mk x) * φ.toMonoidHom d
        rw [← map_mul, ← map_mul]
        exact congrArg φ.toMonoidHom (Subgroup.mem_centralizer_iff.mp hc' d hd)
      have h1 := hA7 D7 (φ (mk x)) hc7
        (Odd.of_dvd_nat hxodd' (orderOf_map_dvd φ.toMonoidHom (mk x)))
      exact φ.injective (by rw [h1, map_one])
    · -- `PSL(2,q)`
      have inst : Fact p.Prime := hpp
      obtain ⟨φ⟩ := hB
      set Dq : Sylow 2 (PSL(2, GaloisField p k)) :=
        Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective D with hDq
      have hcoeq : (Dq : Subgroup (PSL(2, GaloisField p k))) =
          (D : Subgroup (Q ⧸ Subgroup.center Q)).map φ.toMonoidHom :=
        Sylow.coe_mapSurjective (f := φ.toMonoidHom) φ.surjective D
      have hc2 : φ (mk x) ∈ Subgroup.centralizer
          ((Dq : Subgroup (PSL(2, GaloisField p k))) : Set (PSL(2, GaloisField p k))) := by
        rw [hcoeq, Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hh
        change φ.toMonoidHom d * φ.toMonoidHom (mk x) =
          φ.toMonoidHom (mk x) * φ.toMonoidHom d
        rw [← map_mul, ← map_mul]
        exact congrArg φ.toMonoidHom (Subgroup.mem_centralizer_iff.mp hc' d hd)
      have h1 := hL2 p k hp hq Dq (φ (mk x)) hc2
        (Odd.of_dvd_nat hxodd' (orderOf_map_dvd φ.toMonoidHom (mk x)))
      exact φ.injective (by rw [h1, map_one])
  exact (QuotientGroup.eq_one_iff x).mp hkey

/-! ## The layer of the coatom -/

/-- **Bender §4, p. 224, first paragraph**, in the minimal form used here: for a coatom `M` of a
`BenderCtx` group with `t ∈ E(M)`, `layer ↥M` is a (unique) normal quasisimple subgroup of `↥M`,
of odd centre, with `E(M)/Z(E(M)) ≅ A₇` or `PSL(2,q)`. -/
theorem layer_facts_coatom (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} {M : Subgroup G} (hcoat : IsCoatom M)
    (ht : B.t ∈ Work.GW2.layerIn M) :
    ∃ E1 : Subgroup ↥M, E1.Normal ∧ Work.GW2.layer ↥M = E1 ∧
      Odd (Nat.card (Subgroup.center ↥E1)) ∧
      (Nonempty (↥E1 ⧸ Subgroup.center ↥E1 ≃* alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty (↥E1 ⧸ Subgroup.center ↥E1 ≃* PSL(2, GaloisField p k))) := by
  have ht1 : B.t ≠ 1 := by
    intro h1
    have ht2 := B.t_order
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  -- the layer of `M` is nontrivial
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro hbot
    have hbot' : Work.GW2.layerIn M = ⊥ := by
      rw [Work.GW2.layerIn, hbot, Subgroup.map_bot]
    exact ht1 (Subgroup.mem_bot.mp (hbot' ▸ ht))
  -- so `M` has a normal quasisimple subgroup
  obtain ⟨E1, hE1norm, hE1q⟩ : ∃ E1 : Subgroup ↥M, E1.Normal ∧ Work.GW2.IsQuasisimple E1 := by
    by_contra hcon
    apply hlayer_ne
    rw [Work.GW2.layer, sSup_eq_bot]
    intro F hF
    by_contra hFne
    exact hcon ⟨F, hF.1, hF.2⟩
  -- `M` is a proper subgroup of `G`, hence a D-group
  have hD : Work.GW2.DihOrCycSylow ↥M := DihOrCycSub hbc.sylow M
  have hcard : Nat.card ↥M < Nat.card G := card_lt_card_of_ne_top hcoat.ne_top
  have hIsD : Work.GW2.IsDGroup ↥M := hbc.ih ↥M hcard hD
  -- Bender 1.6 / `LayerProp`
  obtain ⟨hlayer, hZodd, hshape⟩ :=
    I.toolkit.lay ↥M I.toolkit.ft hD hIsD E1 hE1norm hE1q
  exact ⟨E1, hE1norm, hlayer, hZodd, hshape⟩

/-! ## The main computation -/

/-- `Case2Setup9Ecent` with the two model-group facts (`A₇` and `L₂(q)`) supplied as hypotheses;
the final theorem instantiates them with the delegated lemmas
`alt7_odd_centralizer_sylow` / `psl_odd_centralizer_sylow`. -/
theorem EcentAux (I : Work.GW2.C4Inputs)
    (hA7 : ∀ (D : Sylow 2 (alternatingGroup (Fin 7))) (x : alternatingGroup (Fin 7)),
      x ∈ Subgroup.centralizer
        ((D : Subgroup (alternatingGroup (Fin 7))) : Set (alternatingGroup (Fin 7))) →
      Odd (orderOf x) → x = 1)
    (hL2 : ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
      ∀ (D : Sylow 2 (PSL(2, GaloisField p k))) (x : PSL(2, GaloisField p k)),
      x ∈ Subgroup.centralizer
        ((D : Subgroup (PSL(2, GaloisField p k))) : Set (PSL(2, GaloisField p k))) →
      Odd (orderOf x) → x = 1) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M P : Subgroup G),
        IsCoatom M → B.t ∈ Work.GW2.layerIn M →
        IsPGroup 2 P → P ≤ M ⊓ B.H → ¬ 2 ∣ P.relIndex M →
        ∀ e ∈ Work.GW2.layerIn M, Odd (orderOf e) →
          e ∈ Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G) →
          (∀ y ∈ Work.GW2.layerIn M, e * y = y * e) := by
  intro G _ _ hbc B M P hcoat ht hPp hPle hPidx e heE heodd hecen
  classical
  -- the layer of `M`
  obtain ⟨E1, hE1norm, hlayer, _hZodd, hshape⟩ := layer_facts_coatom I hbc hcoat ht
  have hlayerIn_eq : Work.GW2.layerIn M = E1.map (Subgroup.subtype M) := by
    rw [Work.GW2.layerIn, hlayer]
  -- `P` viewed inside `↥M` is a Sylow
  have hPle' : P ≤ M := le_trans hPle inf_le_left
  set P1 : Subgroup ↥M := P.subgroupOf M with hP1def
  have hP1p : IsPGroup 2 ↥P1 := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPle').symm
  have hP1idx : ¬ 2 ∣ P1.index := hPidx
  set SM : Sylow 2 ↥M := hP1p.toSylow hP1idx with hSMdef
  have hSMcoe : (SM : Subgroup ↥M) = P1 := IsPGroup.toSylow_coe hP1p hP1idx
  have hE1N : E1.Normal := hE1norm
  -- `P1 ⊓ E1` is a Sylow 2-subgroup of `E1` (Isaacs 9.31, normal case)
  have hsyl_inf : ¬ 2 ∣ (P1 ⊓ E1).relIndex E1 := by
    have h := OddOrder.Isaacs.Ch09.not_dvd_relIndex_inf_of_normal (p := 2) E1 SM
    simpa only [hSMcoe] using h
  have hSEp : IsPGroup 2 ↥((P1 ⊓ E1).subgroupOf E1) :=
    (hP1p.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  set SE : Sylow 2 ↥E1 := hSEp.toSylow hsyl_inf with hSEdef
  have hSEcoe : (SE : Subgroup ↥E1) = (P1 ⊓ E1).subgroupOf E1 :=
    IsPGroup.toSylow_coe hSEp hsyl_inf
  -- the element of `E1` corresponding to `e`
  have heE1 : e ∈ E1.map (Subgroup.subtype M) := by rw [← hlayerIn_eq]; exact heE
  obtain ⟨e0, he0mem, he0eq⟩ := Subgroup.mem_map.mp heE1
  set xe : ↥E1 := ⟨e0, he0mem⟩ with hxedef
  have hxeord1 : orderOf xe = orderOf e0 := by
    rw [hxedef]
    exact (Subgroup.orderOf_coe (⟨e0, he0mem⟩ : ↥E1)).symm
  have he0ord : orderOf e0 = orderOf e := by
    rw [← Subgroup.orderOf_coe e0]
    exact congrArg orderOf he0eq
  have hxeodd : Odd (orderOf xe) := by
    rw [hxeord1, he0ord]
    exact heodd
  -- `xe` centralises `SE`
  have hxec : xe ∈ Subgroup.centralizer ((SE : Subgroup ↥E1) : Set ↥E1) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu1 : u ∈ (P1 ⊓ E1).subgroupOf E1 := hSEcoe ▸ hu
    obtain ⟨huP1, huE1⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hu1)
    have huP : ((u : ↥M) : G) ∈ P := Subgroup.mem_subgroupOf.mp huP1
    have huE : ((u : ↥M) : G) ∈ Work.GW2.layerIn M := by
      rw [hlayerIn_eq]
      exact ⟨(u : ↥M), huE1, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hecen) (((u : ↥M) : G)) ⟨huP, huE⟩
    apply Subtype.ext
    show (u : ↥M) * e0 = e0 * (u : ↥M)
    apply Subtype.ext
    change (Subgroup.subtype M) (u : ↥M) * (Subgroup.subtype M) e0 =
      (Subgroup.subtype M) e0 * (Subgroup.subtype M) (u : ↥M)
    rw [he0eq]
    exact hcomm
  -- the abstract centre lemma
  have hcenter : xe ∈ Subgroup.center ↥E1 :=
    odd_mem_center_of_centralizer_sylow ↥E1 hA7 hL2 hshape SE xe hxeodd hxec
  -- conclusion
  intro y hy
  rw [hlayerIn_eq] at hy
  obtain ⟨y0, hy0mem, hy0eq⟩ := Subgroup.mem_map.mp hy
  have hcomm := (Subgroup.mem_center_iff.mp hcenter) (⟨y0, hy0mem⟩ : ↥E1)
  have hcomm' : y0 * e0 = e0 * y0 := by
    have h := congrArg (fun z : ↥E1 => (z : ↥M)) hcomm
    simpa using h
  rw [← he0eq, ← hy0eq]
  have h2 := congrArg (Subgroup.subtype M) hcomm'
  simpa using h2.symm

/-- The structure fact behind Bender 1981, §4 (4) (`F` centralises `E(M)`): an odd-order element of
`E = E(M)` centralising a Sylow 2-subgroup of `E` centralises `E`.

Configuration: `BenderCtx G`, `B : BenderSetup G`, `M : Subgroup G` a coatom with `t = B.t ∈ layerIn M`,
and `P ≤ M ⊓ C_G(t)` a Sylow 2-subgroup of `M` (so `P ⊓ E` is a Sylow 2-subgroup of `E`).

Conclusion: for `e ∈ E` of odd order with `e ∈ C_G(P ⊓ E)`, one has `e ∈ C_G(E)` (written out:
`e * y = y * e` for all `y ∈ E`).

This is true and is a pure structure statement about the two possibilities for `E/Z(E)` given by
`I.toolkit.lay`: `E/Z(E) ≅ A₇` or `E/Z(E) ≅ PSL(2,q)`, `q = p^k ≥ 5`, `p` odd.
* `PSL(2,q)`: the Sylow `S` of `PSL(2,q)` (order ≥ 4, dihedral) contains a Klein four `V`
  (`I.toolkit.l2syl`); `I.toolkit.l2four` says four-groups in `L₂(q)` are self-centralising, so
  `C_{PSL(2,q)}(S) ≤ C(V) = V` is a 2-group; hence the centraliser of `S` has odd part `1`.
* `A₇`: `C_{A₇}(D₈) = Z(D₈)`, a 2-group (so again the odd part is `1`); this is proved in the
  workspace as `Work.AUTA7.A7.SylowFacts` (`N_{A₇}(D) = D`, no `sorry`) — import
  `Submission/Work/AUTA7/A7/SylowFacts.lean`.
Lifting from `E/Z(E)` to `E`: if `e ∈ E` is odd and centralises a Sylow of `E`, then `eZ(E)`
centralises a Sylow of `E/Z(E)`; the odd part of that centraliser being trivial forces `eZ(E) = 1`,
i.e. `e ∈ Z(E)`, and `Z(E) ≤ C_G(E)`.  (For a proper cover `E = 3.A₇` the odd part of
`C_{E/Z(E)}(Sylow)` is trivial as well, and `Z(E)` is central, so the same conclusion holds.) -/
theorem Case2Setup9Ecent (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M P : Subgroup G),
        IsCoatom M → B.t ∈ Work.GW2.layerIn M →
        IsPGroup 2 P → P ≤ M ⊓ B.H → ¬ 2 ∣ P.relIndex M →
        ∀ e ∈ Work.GW2.layerIn M, Odd (orderOf e) →
          e ∈ Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G) →
          (∀ y ∈ Work.GW2.layerIn M, e * y = y * e) :=
  EcentAux I
    (fun D _x hc ho => Work.CORE4.Ecent.alt7_odd_centralizer_sylow D ho hc)
    (fun p k _hpp hp hq D _x hc ho =>
      Work.CORE4.Ecent.psl_odd_centralizer_sylow p k hp hq I.toolkit.l2syl I.toolkit.l2four D ho hc)

end Work.CORE4
