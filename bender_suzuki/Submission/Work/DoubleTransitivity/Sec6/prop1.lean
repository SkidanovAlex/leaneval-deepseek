import Mathlib
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.Sec5.Defs
import Submission.Work.DoubleTransitivity.Sec6.Defs
import Submission.Work.DoubleTransitivity.Sec6.lemma1
import Submission.Work.DoubleTransitivity.Sec5.exists_sylow_normalized_of_regularIntersection
import Submission.Work.DoubleTransitivity.Sec5.exists_conj_of_commuting_involutions
import Submission.Work.DoubleTransitivity.Sec5.inductionStep
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.GlaubermanZJ.ZJ_ne_bot
import Submission.Work.GlaubermanZJ.normalizer_ZJ
import Submission.Work.ThompsonFrobenius.ZJ_map_of_ker_inf_eq_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec6.prop1` — Peterfalvi I, Ch. I §6, Proposition 1 (p. 159)

Let `H` be strongly embedded in a finite group `G` of 2-rank `≥ 2`, `t ∉ H` an involution,
`D = H ∩ H^t = twoPoint H t`, `p` an *odd* prime with `(D,H) ∈ 𝓡_p`, and `u ∈ Inv(H)`.

* `O_{p'}(D ∩ D^u) ≤ O_{p'}(D)` (ambient form `pPrimeCoreSub`);
* if `O_{p'}(D ∩ D^u) = O_{p'}(D)`, then `G` acts doubly transitively on `Ω = G ⧸ H`.

First part: `Sec5.exists_sylow_normalized_of_regularIntersection` gives a `p`-Sylow `P ≤ D`
normalised by `u`, whence `P ≤ D ∩ D^u`; `O_{p'}(D ∩ D^u)` is a `p'`-subgroup of the odd-order
(hence, by Feit--Thompson, solvable) group `D`, normalised by the `p`-Sylow `P`, so Bender's
lemma (`Sec6.lemma1`, ambient form `bender_lemma_ambient`) puts it inside `O_{p'}(D)`.

Second part: by Glauberman's ZJ theorem applied to the abstract group `↥D` (solvable of odd
order, hence with abelian Sylow 2-subgroups), `O_{p'}(D) · Z(J(P))` is *characteristic* in `D`;
its image `A` in `G` is `≠ 1`, normal in `D`, invariant under `t ∈ N_G(D)`, and — because the
chosen Sylow `P` is `u`-invariant and, by the equality hypothesis, `O_{p'}(D ∩ D^u) = O_{p'}(D)`
— invariant under `u` as well.  Ch. I §5 Proposition 1 (`Sec5.inductionStep`, the only place the
induction hypothesis is used) then yields the double transitivity of `G` on `Ω`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
namespace Work.DoubleTransitivity.Sec6

private theorem index_subgroupOf_top {H : Type} [Group H] (Q : Subgroup H) :
    (Q.subgroupOf ⊤).index = Q.index := by
  rw [← Subgroup.relIndex_top_right (H := Q.subgroupOf ⊤),
    ← Subgroup.relIndex_top_right (H := Q)]
  exact Subgroup.relIndex_subgroupOf (H := Q) (K := ⊤) (L := ⊤) le_top

private theorem isSylowSubgroupOf_top {G : Type} [Group G] [Finite G] {p : ℕ} {P D : Subgroup G}
    (h : Work.DoubleTransitivity.IsSylowSubgroupOf p P D) :
    Work.DoubleTransitivity.IsSylowSubgroupOf p (P.subgroupOf D) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact IsPGroup.of_equiv h.2.1 (Subgroup.subgroupOfEquivOfLe h.1).symm
  · rw [index_subgroupOf_top]; exact h.2.2

private theorem bender_lemma_ambient {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X D : Subgroup G}
    (hDsol : Group.IsSolvable ↥D) (hXD : X ≤ D) (hXcop : Nat.Coprime p (Nat.card ↥X))
    {P : Subgroup G} (hPsyl : Work.DoubleTransitivity.IsSylowSubgroupOf p P D)
    (hPn : P ≤ Subgroup.normalizer (X : Set G)) :
    X ≤ Work.DoubleTransitivity.pPrimeCoreSub p D := by
  have hXcop' : Nat.Coprime p (Nat.card ↥(X.subgroupOf D)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXD).toEquiv]; exact hXcop
  have hPn' : P.subgroupOf D ≤ Subgroup.normalizer (X.subgroupOf D : Set ↥D) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh k hk
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact (Subgroup.le_normalizer_iff.mp hPn) h.1 hh k.1 hk
  have hsub : X.subgroupOf D ≤ Submission.Blueprint.pPrimeCore p ↥D :=
    Work.DoubleTransitivity.Sec6.lemma1 hp hDsol hXcop' (isSylowSubgroupOf_top hPsyl) hPn'
  have hmap := Subgroup.map_mono (f := D.subtype) hsub
  rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hXD] at hmap
  rw [Work.DoubleTransitivity.pPrimeCoreSub]
  exact hmap

private theorem map_conj_eq_of_characteristic {G : Type} [Group G] {E : Subgroup G} [Finite ↥E]
    {C : Subgroup ↥E} (hC : C.Characteristic) {g : G}
    (hg : Subgroup.map (↑(MulAut.conj g)) E = E) :
    Subgroup.map (↑(MulAut.conj g)) (C.map E.subtype) = C.map E.subtype := by
  have hmem : ∀ x : ↥E, (MulAut.conj g) (x : G) ∈ E := by
    intro x
    have hx : (MulAut.conj g) (x : G) ∈ Subgroup.map (↑(MulAut.conj g)) E :=
      Subgroup.mem_map_of_mem _ x.2
    rwa [hg] at hx
  let φ : ↥E →* ↥E :=
    { toFun := fun x => ⟨(MulAut.conj g) (x : G), hmem x⟩
      map_one' := by ext; simp [MulAut.conj_apply]
      map_mul' := by intro a b; ext; simp only [Subgroup.coe_mul, MulAut.conj_apply]; group }
  have hinj : Function.Injective φ := by
    intro a b h
    have h2 : (MulAut.conj g) (a : G) = (MulAut.conj g) (b : G) :=
      congrArg Subtype.val h
    exact Subtype.ext ((MulAut.conj g).injective h2)
  have hbij : Function.Bijective φ := Finite.injective_iff_bijective.mp hinj
  have hfix : Subgroup.map φ C = C := by
    have h := (Subgroup.characteristic_iff_map_eq.mp hC) (MulEquiv.ofBijective φ hbij)
    rwa [show (MulEquiv.ofBijective φ hbij).toMonoidHom = φ from MonoidHom.ext (fun _ => rfl)] at h
  calc Subgroup.map (↑(MulAut.conj g)) (C.map E.subtype)
      = Subgroup.map ((↑(MulAut.conj g) : G →* G).comp E.subtype) C := Subgroup.map_map C _ _
    _ = Subgroup.map (E.subtype.comp φ) C := by congr 1
    _ = Subgroup.map E.subtype (Subgroup.map φ C) := (Subgroup.map_map C E.subtype φ).symm
    _ = C.map E.subtype := by rw [hfix]

private theorem card_dvd_card_top {X : Type} [Group X] {H : Subgroup X} :
    Nat.card ↥H ∣ Nat.card X := by
  have h := Subgroup.card_dvd_of_le (le_top : H ≤ ⊤)
  rwa [Nat.card_congr Subgroup.topEquiv.toEquiv] at h

private theorem hasAbelianSylowTwo_of_odd {X : Type} [Group X] [Finite X] (h : Odd (Nat.card X)) :
    Work.GlaubermanZJ.HasAbelianSylowTwo X := by
  intro S
  have hSbot : (S : Subgroup X) = ⊥ := by
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    have hdvd : Nat.card ↥(S : Subgroup X) ∣ Nat.card X := card_dvd_card_top
    rw [hk] at hdvd
    have hcop : Nat.Coprime (2 ^ k) (Nat.card X) := (Nat.coprime_two_left.mpr h).pow_left k
    have h1 : 2 ^ k = 1 := hcop.eq_one_of_dvd hdvd
    have hcard : Nat.card ↥(S : Subgroup X) = 1 := by rw [hk, h1]
    exact Subgroup.card_eq_one.mp hcard
  intro x hx y hy
  rw [hSbot, Subgroup.mem_bot] at hx hy
  rw [hx, hy]

private theorem exists_normal_subgroup_in_twoPoint {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hZJ : Submission.Blueprint.GlaubermanZJProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hPsyl : Work.DoubleTransitivity.IsSylowSubgroupOf p P (Submission.Blueprint.twoPoint H t))
    {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    (huP : u ∈ Subgroup.normalizer (P : Set G))
    (hDne : Submission.Blueprint.twoPoint H t ≠ ⊥)
    (heq : Work.DoubleTransitivity.pPrimeCoreSub p
        (Submission.Blueprint.twoPoint H t ⊓ Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t))
      = Work.DoubleTransitivity.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t)) :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ A ≤ Submission.Blueprint.twoPoint H t ∧
      Submission.Blueprint.twoPoint H t ≤ Subgroup.normalizer (A : Set G) ∧
      t ∈ Subgroup.normalizer (A : Set G) ∧ u ∈ Subgroup.normalizer (A : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup G := Submission.Blueprint.twoPoint H t with hD
  have hDodd : Odd (Nat.card ↥D) := by
    rw [hD]
    simpa [Submission.Blueprint.twoPoint, Submission.Blueprint.conj] using hH.2.2 t htH
  have hDsol : Group.IsSolvable ↥D := hFT ↥D hDodd
  have h2ab : Work.GlaubermanZJ.HasAbelianSylowTwo ↥D := hasAbelianSylowTwo_of_odd hDodd
  have hPp : IsPGroup p (P.subgroupOf D) :=
    IsPGroup.of_equiv hPsyl.2.1 (Subgroup.subgroupOfEquivOfLe hPsyl.1).symm
  have hidx : ¬ p ∣ (P.subgroupOf D).index := hPsyl.2.2
  let Q : Sylow p ↥D := hPp.toSylow hidx
  have hQ : (Q : Subgroup ↥D) = P.subgroupOf D := rfl
  have hchar : (Submission.Blueprint.pPrimeCore p ↥D ⊔
      Submission.Blueprint.ZJ (Q : Subgroup ↥D)).Characteristic :=
    hZJ ↥D p hp hp2 hDsol h2ab Q
  let C : Subgroup ↥D := Submission.Blueprint.pPrimeCore p ↥D ⊔
    Submission.Blueprint.ZJ (Q : Subgroup ↥D)
  have hCchar : C.Characteristic := hchar
  let A : Subgroup G := C.map D.subtype
  have hker : D.subtype.ker ⊓ (Q : Subgroup ↥D) = ⊥ := by
    rw [Subgroup.ker_subtype, bot_inf_eq]
  have hZ : (Submission.Blueprint.ZJ (Q : Subgroup ↥D)).map D.subtype =
      Submission.Blueprint.ZJ P := by
    rw [Work.ThompsonFrobenius.ZJ_map_of_ker_inf_eq_bot D.subtype (Q : Subgroup ↥D) hker, hQ,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hPsyl.1]
  have hAeq : A = Work.DoubleTransitivity.pPrimeCoreSub p D ⊔ Submission.Blueprint.ZJ P := by
    rw [show A = Subgroup.map D.subtype (Submission.Blueprint.pPrimeCore p ↥D ⊔
      Submission.Blueprint.ZJ (Q : Subgroup ↥D)) from rfl, Subgroup.map_sup,
      Work.DoubleTransitivity.pPrimeCoreSub, hZ]
  have hAle : A ≤ D := Subgroup.map_subtype_le C
  have htopmap : (⊤ : Subgroup ↥D).map D.subtype = D := by
    refine le_antisymm (Subgroup.map_subtype_le ⊤) ?_
    intro x hx
    exact Subgroup.mem_map_of_mem D.subtype (Subgroup.mem_top (⟨x, hx⟩ : ↥D))
  refine ⟨A, ?_, hAle, ?_, ?_, ?_⟩
  · intro hbot
    rw [hAeq] at hbot
    have hX0 : Work.DoubleTransitivity.pPrimeCoreSub p D = ⊥ :=
      le_bot_iff.mp (hbot ▸ le_sup_left)
    have hZ0 : Submission.Blueprint.ZJ P = ⊥ := le_bot_iff.mp (hbot ▸ le_sup_right)
    have hPne : P ≠ ⊥ := by
      intro hPbot
      have hpd : ¬ p ∣ Nat.card ↥D := by
        have h := hPsyl.2.2
        rw [hPbot, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h
        exact h
      have htop : Submission.Blueprint.pPrimeCore p ↥D = ⊤ := by
        rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
        refine le_antisymm le_top ?_
        refine Work.Fitting.le_piCore (N := ⊤) inferInstance ?_
        rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
        exact (Work.GlaubermanZJ.isPiNat_ne_iff_coprime hp).mpr
          (hp.coprime_iff_not_dvd.mpr hpd).symm
      have hsub : Work.DoubleTransitivity.pPrimeCoreSub p D = D := by
        rw [Work.DoubleTransitivity.pPrimeCoreSub, htop, htopmap]
      rw [hsub] at hX0
      exact hDne hX0
    exact (Work.GlaubermanZJ.ZJ_ne_bot hp P hPsyl.2.1 hPne) hZ0
  · rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hAle]
    have hsub : A.subgroupOf D = C := by
      rw [← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective D) C
    rw [hsub]
    haveI : C.Characteristic := hCchar
    infer_instance
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have ht2 : t * t = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [ht, pow_two] at h
    have htD : Subgroup.map (↑(MulAut.conj t)) D = D := by
      rw [hD, Submission.Blueprint.twoPoint]
      have h1 : Subgroup.map (↑(MulAut.conj t)) (Submission.Blueprint.conj t H) = H := by
        show Submission.Blueprint.conj t (Submission.Blueprint.conj t H) = H
        rw [← Work.DoubleTransitivity.conj_mul t t H, ht2, Work.DoubleTransitivity.conj_one]
      rw [Subgroup.map_inf (f := (MulAut.conj t : G →* G)) H (Submission.Blueprint.conj t H)
          (MulAut.conj t).injective, h1, inf_comm]
      rfl
    exact map_conj_eq_of_characteristic hCchar htD
  · have hu2 : u * u = 1 := by
      have h := pow_orderOf_eq_one u
      rw [hu.2, pow_two] at h
      exact h
    have huX : Subgroup.map (↑(MulAut.conj u)) (Work.DoubleTransitivity.pPrimeCoreSub p D)
        = Work.DoubleTransitivity.pPrimeCoreSub p D := by
      haveI hcE : (Submission.Blueprint.pPrimeCore p ↥(D ⊓ Submission.Blueprint.conj u D)).Characteristic := by
        rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
        infer_instance
      have huE : Subgroup.map (↑(MulAut.conj u)) (D ⊓ Submission.Blueprint.conj u D)
          = D ⊓ Submission.Blueprint.conj u D := by
        have h1 : Subgroup.map (↑(MulAut.conj u)) (Submission.Blueprint.conj u D) = D := by
          show Submission.Blueprint.conj u (Submission.Blueprint.conj u D) = D
          rw [← Work.DoubleTransitivity.conj_mul u u D, hu2, Work.DoubleTransitivity.conj_one]
        rw [Subgroup.map_inf (f := (MulAut.conj u : G →* G)) D (Submission.Blueprint.conj u D)
          (MulAut.conj u).injective, h1, inf_comm]
        rfl
      have h := map_conj_eq_of_characteristic
        (E := D ⊓ Submission.Blueprint.conj u D)
        (C := Submission.Blueprint.pPrimeCore p ↥(D ⊓ Submission.Blueprint.conj u D)) hcE huE
      change Subgroup.map (↑(MulAut.conj u))
        (Work.DoubleTransitivity.pPrimeCoreSub p (D ⊓ Submission.Blueprint.conj u D))
        = Work.DoubleTransitivity.pPrimeCoreSub p (D ⊓ Submission.Blueprint.conj u D) at h
      rw [heq] at h
      exact h
    have huZ : Subgroup.map (↑(MulAut.conj u)) (Submission.Blueprint.ZJ P)
        = Submission.Blueprint.ZJ P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Work.GlaubermanZJ.normalizer_ZJ P huP)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show Subgroup.map (↑(MulAut.conj u)) A = A
    rw [hAeq, Subgroup.map_sup, huX, huZ]

theorem prop1 {G : Type} [Group G] [Finite G] (hFT : Submission.Blueprint.FeitThompsonProp)
    (hZJ : Submission.Blueprint.GlaubermanZJProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hInd : Work.DoubleTransitivity.ThmAForBelow (Nat.card G))
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (h4 : Submission.Blueprint.HasFourGroup G) {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : Work.DoubleTransitivity.IsRegularIntersection p (Submission.Blueprint.twoPoint H t) H)
    {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G)) :
    Work.DoubleTransitivity.pPrimeCoreSub p
        (Submission.Blueprint.twoPoint H t ⊓ Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t)) ≤
      Work.DoubleTransitivity.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t) ∧
    (Work.DoubleTransitivity.pPrimeCoreSub p
        (Submission.Blueprint.twoPoint H t ⊓ Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H t)) =
      Work.DoubleTransitivity.pPrimeCoreSub p (Submission.Blueprint.twoPoint H t) →
      Submission.Blueprint.IsTwoTransitiveOn H) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup G := Submission.Blueprint.twoPoint H t with hD
  set E : Subgroup G := D ⊓ Submission.Blueprint.conj u D with hE
  have hBender : Work.DoubleTransitivity.IsBender H :=
    ((Work.DoubleTransitivity.isStronglyEmbedded_iff H).mp hH).2
  have hHne : H ≠ ⊤ := ((Work.DoubleTransitivity.isStronglyEmbedded_iff H).mp hH).1
  have hDodd : Odd (Nat.card ↥D) := by
    rw [hD]
    simpa [Submission.Blueprint.twoPoint, Submission.Blueprint.conj] using hH.2.2 t htH
  have hDsol : Group.IsSolvable ↥D := hFT ↥D hDodd
  obtain ⟨P, hPsyl, huP⟩ :=
    Work.DoubleTransitivity.Sec5.exists_sylow_normalized_of_regularIntersection
      hBender hHne ht htH hreg hu
  -- ## The first conjunct
  have hXD : Work.DoubleTransitivity.pPrimeCoreSub p E ≤ D :=
    (Work.DoubleTransitivity.pPrimeCoreSub_le p E).trans inf_le_left
  have hXcop : Nat.Coprime p (Nat.card ↥(Work.DoubleTransitivity.pPrimeCoreSub p E)) := by
    have hcard : Nat.card ↥(Work.DoubleTransitivity.pPrimeCoreSub p E) =
        Nat.card ↥(Submission.Blueprint.pPrimeCore p ↥E) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective E)
    rw [hcard, Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
    exact ((Work.GlaubermanZJ.isPiNat_ne_iff_coprime hp).mp
      (Work.Fitting.piCore_isPiNat ↥E (fun q => q ≠ p))).symm
  have hEnorm : E ≤ Subgroup.normalizer
      (Work.DoubleTransitivity.pPrimeCoreSub p E : Set G) := by
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := Work.DoubleTransitivity.pPrimeCoreSub p E) (K := E)
      (Work.DoubleTransitivity.pPrimeCoreSub_le p E)]
    have hsub : (Work.DoubleTransitivity.pPrimeCoreSub p E).subgroupOf E =
        Submission.Blueprint.pPrimeCore p ↥E := by
      rw [Work.DoubleTransitivity.pPrimeCoreSub, ← Subgroup.comap_subtype]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective E) _
    rw [hsub, Work.GlaubermanZJ.pPrimeCore_eq_fitting p hp]
    infer_instance
  have hPleE : P ≤ E := by
    refine le_inf hPsyl.1 ?_
    have hconj : Submission.Blueprint.conj u P = P :=
      (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer u P).mpr huP
    rw [← hconj]
    exact Subgroup.map_mono hPsyl.1
  have h1 : Work.DoubleTransitivity.pPrimeCoreSub p E ≤
      Work.DoubleTransitivity.pPrimeCoreSub p D :=
    bender_lemma_ambient hp hDsol hXD hXcop hPsyl (hPleE.trans hEnorm)
  refine ⟨h1, ?_⟩
  -- ## The second conjunct
  intro heq
  have hDne : D ≠ ⊥ := by
    obtain ⟨a, b, ha2, hb2, hab_ne, hab_comm⟩ := h4
    obtain ⟨g, hag, hbg⟩ :=
      Work.DoubleTransitivity.Sec5.exists_conj_of_commuting_involutions
        hBender ha2 hb2 hab_ne hab_comm
    have haH : g⁻¹ * a * g ∈ H := (Work.DoubleTransitivity.mem_conj g a H).mp hag
    have hbH : g⁻¹ * b * g ∈ H := (Work.DoubleTransitivity.mem_conj g b H).mp hbg
    set a' : G := g⁻¹ * a * g with ha'
    set b' : G := g⁻¹ * b * g with hb'
    have ha'inv : a' ∈ Submission.Blueprint.involutions (H : Set G) := by
      refine ⟨haH, ?_⟩
      rw [ha']
      have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) a
      rw [MulAut.conj_apply, inv_inv] at h
      exact h.trans ha2
    have hb'inv : b' ∈ Submission.Blueprint.involutions (H : Set G) := by
      refine ⟨hbH, ?_⟩
      rw [hb']
      have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) b
      rw [MulAut.conj_apply, inv_inv] at h
      exact h.trans hb2
    intro hDbot
    obtain ⟨d, hd, hdu⟩ :=
      (Work.DoubleTransitivity.Sec2.prop2 hBender hHne ht htH).1 a' b' ha'inv hb'inv
    have hdD : d ∈ D := by rwa [hD]
    rw [hDbot, Subgroup.mem_bot] at hdD
    have hab_eq : a = b := by
      have h := hdu
      rw [hdD, inv_one, one_mul, mul_one] at h
      have h2 : g * a' * g⁻¹ = g * b' * g⁻¹ := by rw [h]
      simpa [ha', hb'] using h2
    exact hab_ne hab_eq
  obtain ⟨A, hAne, hAle, hAn, hAt, huA⟩ :=
    exists_normal_subgroup_in_twoPoint hFT hZJ hH ht htH hp hp2 hPsyl hu huP hDne heq
  exact Work.DoubleTransitivity.Sec5.inductionStep
    hBrSz hH h4 hInd ht htH hAne hAle hAn hAt ⟨u, hu, huA⟩

end Work.DoubleTransitivity.Sec6
