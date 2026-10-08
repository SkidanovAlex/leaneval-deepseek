import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.Fitting.mem_piCore_iff
import Submission.Work.GlaubermanZJ.pPrimeCore_eq_fitting
import Submission.Work.LocalPrelim.relIndex_sup_eq_relIndex_inf
import Submission.Work.DoubleTransitivity.App2.SylowAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `P` Sylow in `W` from `P` Sylow in `E` and `N_W(P) = O_{p'}(C_W(P))·(N_W(P) ∩ E)`

This is the first step of the proof that `E` is a `p`-control group in `W` (Peterfalvi I, Ch. III
§1).  Since `O_{p'}(C_W(P))` is characteristic in `C_W(P)` and `C_W(P) ⊴ N_W(P)`, the subgroup
`O_{p'}(C_W(P))` is normal in `N_W(P)`; the hypothesis `h1` therefore exhibits `N_W(P)` as a
product of the `p'`-group `O_{p'}(C_W(P))` and `N_W(P) ∩ E`, which forces `[N_W(P) : P]` to be
prime to `p`.  `P` is Sylow in its own normalizer, hence in `W`.
-/

namespace Work.NormalComplement

/-- Membership in the conjugate `H^x = x H x⁻¹`, spelled out. -/
private lemma mem_map_conj_iff {G : Type*} [Group G] {H : Subgroup G} {x y : G} :
    y ∈ H.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * y * x ∈ H := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhx⟩
    have hy : y = x * h * x⁻¹ := hhx.symm.trans (MulAut.conj_apply x h)
    have hx : x⁻¹ * y * x = h := by rw [hy]; group
    rw [hx]; exact hh
  · intro h
    exact ⟨x⁻¹ * y * x, h, by
      show (MulAut.conj x) (x⁻¹ * y * x) = y
      rw [MulAut.conj_apply]
      group⟩

/-- `O_{p'}(X)`, viewed as a subgroup of the ambient group, has order prime to `p`. -/
private lemma not_dvd_card_pPrimeCoreSub {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (X : Subgroup G) : ¬ p ∣ Nat.card ↥(pPrimeCoreSub p X) := by
  have hcard : Nat.card ↥(pPrimeCoreSub p X) = Nat.card ↥(Work.Fitting.pPrimeCore p ↥X) := by
    rw [show pPrimeCoreSub p X = (Work.Fitting.pPrimeCore p ↥X).map X.subtype from by
      show (Submission.Blueprint.pPrimeCore p ↥X).map X.subtype = _
      rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p (Fact.out : p.Prime)]]
    exact Subgroup.card_map_of_injective X.subtype_injective
  have hispi := Work.Fitting.piCore_isPiNat ↥X (fun q => q ≠ p)
  intro hdvd
  exact absurd rfl (hispi p (Fact.out : p.Prime) (hcard ▸ hdvd))

/-- If `M` normalizes `Q` and `N = Q ⊔ M`, then the index of `M` in `N` divides the order
of `Q` (second isomorphism theorem for the coset spaces `N/M` and `Q/(Q ⊓ M)`). -/
private lemma relIndex_sup_dvd_card_of_le_normalizer {G : Type*} [Group G]
    {Q M N : Subgroup G} (hMQ : M ≤ Subgroup.normalizer (Q : Set G)) (hN : N = Q ⊔ M) :
    M.relIndex N ∣ Nat.card ↥Q := by
  subst hN
  rw [sup_comm, Work.LocalPrelim.relIndex_sup_eq_relIndex_inf_auxL hMQ,
    Subgroup.inf_relIndex_right]
  exact Subgroup.relIndex_dvd_card M Q

/-- `pPrimeCoreSub p C` is invariant under any conjugation normalizing `C`: it is the `p'`-core
of `C`, hence characteristic in `C`. -/
private lemma map_conj_pPrimeCoreSub_eq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {C : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (C : Set G)) :
    (pPrimeCoreSub p C).map (MulAut.conj x).toMonoidHom = pPrimeCoreSub p C := by
  have hxC : C.map (MulAut.conj x).toMonoidHom = C :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have hQ : pPrimeCoreSub p C = (Work.Fitting.pPrimeCore p ↥C).map C.subtype := by
    show (Submission.Blueprint.pPrimeCore p ↥C).map C.subtype =
      (Work.Fitting.pPrimeCore p ↥C).map C.subtype
    rw [Work.GlaubermanZJ.pPrimeCore_eq_fitting p (Fact.out : p.Prime)]
  have hle : (pPrimeCoreSub p C).map (MulAut.conj x).toMonoidHom ≤ pPrimeCoreSub p C := by
    rw [hQ, Subgroup.map_map]
    rintro y ⟨k, hk, rfl⟩
    have hmem : x * (k : G) * x⁻¹ ∈ (Work.Fitting.pPrimeCore p ↥C).map C.subtype := by
      obtain ⟨D, hD, hkD⟩ :=
        (Work.Fitting.mem_piCore_iff (G := ↥C) (π := fun q => q ≠ p) (x := k)).mp hk
      obtain ⟨hDnorm, hDpi⟩ := Work.Fitting.mem_piCoreSet.mp hD
      -- the conjugate of `D` by `x`, pulled back to `C`
      have hDC : (D.map C.subtype).map (MulAut.conj x).toMonoidHom ≤ C := by
        intro z hz
        have hz' : x⁻¹ * z * x ∈ D.map C.subtype :=
          (mem_map_conj_iff (H := D.map C.subtype)).mp hz
        obtain ⟨d, hd, hdd⟩ := Subgroup.mem_map.mp hz'
        have hdd' : (d : G) = x⁻¹ * z * x := hdd
        have hzeq : z = x * (d : G) * x⁻¹ := by rw [hdd']; group
        have hconj : x * (d : G) * x⁻¹ = (MulAut.conj x) (d : G) :=
          (MulAut.conj_apply x (d : G)).symm
        have hdC : (MulAut.conj x) (d : G) ∈ C := by
          have h1 : (MulAut.conj x) (d : G) ∈ C.map (MulAut.conj x).toMonoidHom :=
            Subgroup.mem_map.mpr ⟨(d : G), d.2, rfl⟩
          rwa [hxC] at h1
        rw [hzeq, hconj]; exact hdC
      set D' : Subgroup ↥C :=
        ((D.map C.subtype).map (MulAut.conj x).toMonoidHom).comap C.subtype with hD'
      have hmapD' : D'.map C.subtype = (D.map C.subtype).map (MulAut.conj x).toMonoidHom :=
        Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
      have hcardD' : Nat.card ↥D' = Nat.card ↥D := by
        have h1 : Nat.card ↥D' = Nat.card ↥((D.map C.subtype).map
            (MulAut.conj x).toMonoidHom) := by
          rw [← Subgroup.card_map_of_injective (f := C.subtype) C.subtype_injective, hmapD']
        have h2 : Nat.card ↥((D.map C.subtype).map (MulAut.conj x).toMonoidHom) =
            Nat.card ↥(D.map C.subtype) :=
          Subgroup.card_map_of_injective (MulAut.conj x).injective
        have h3 : Nat.card ↥(D.map C.subtype) = Nat.card ↥D :=
          Subgroup.card_map_of_injective C.subtype_injective
        exact h1.trans (h2.trans h3)
      have hD'normal : D'.Normal := by
        refine ⟨fun a ha b => ?_⟩
        have haX : (a : G) ∈ (D.map C.subtype).map (MulAut.conj x).toMonoidHom := ha
        have hpre : x⁻¹ * (a : G) * x ∈ D.map C.subtype :=
          (mem_map_conj_iff (H := D.map C.subtype)).mp haX
        obtain ⟨d, hd, hdd⟩ := Subgroup.mem_map.mp hpre
        have hbC : x⁻¹ * (b : G) * x ∈ C :=
          (mem_map_conj_iff (H := C)).mp (by rw [hxC]; exact b.2)
        have hconjD : (⟨x⁻¹ * (b : G) * x, hbC⟩ : ↥C) * d *
            (⟨x⁻¹ * (b : G) * x, hbC⟩ : ↥C)⁻¹ ∈ D :=
          hDnorm.conj_mem d hd _
        have hG : (x⁻¹ * (b : G) * x) * (d : G) * (x⁻¹ * (b : G) * x)⁻¹
            ∈ D.map C.subtype := Subgroup.mem_map.mpr ⟨_, hconjD, rfl⟩
        have heq : (x⁻¹ * (b : G) * x) * (d : G) * (x⁻¹ * (b : G) * x)⁻¹ =
            x⁻¹ * ((b : G) * (a : G) * (b : G)⁻¹) * x := by
          have hdd' : (d : G) = x⁻¹ * (a : G) * x := hdd
          rw [hdd']; group
        have hgoal : ((b * a * b⁻¹ : ↥C) : G)
            ∈ (D.map C.subtype).map (MulAut.conj x).toMonoidHom := by
          refine (mem_map_conj_iff (H := D.map C.subtype)).mpr ?_
          show x⁻¹ * ((b : G) * (a : G) * (b : G)⁻¹) * x ∈ D.map C.subtype
          rw [← heq]
          exact hG
        exact hgoal
      have hD'pi : Work.Fitting.IsPiNat (fun q => q ≠ p) (Nat.card ↥D') := by
        rw [hcardD']; exact hDpi
      have hD'le : D' ≤ Work.Fitting.pPrimeCore p ↥C :=
        Work.Fitting.le_piCore hD'normal hD'pi
      have hk'C : x * (k : G) * x⁻¹ ∈ C := by
        have h1 : (MulAut.conj x) (k : G) ∈ C.map (MulAut.conj x).toMonoidHom :=
          Subgroup.mem_map.mpr ⟨(k : G), k.2, rfl⟩
        have h2 : (MulAut.conj x) (k : G) = x * (k : G) * x⁻¹ := MulAut.conj_apply x k
        rw [h2, hxC] at h1
        exact h1
      let k' : ↥C := ⟨x * (k : G) * x⁻¹, hk'C⟩
      have hk'D' : k' ∈ D' := by
        have h1 : (k' : G) ∈ (D.map C.subtype).map (MulAut.conj x).toMonoidHom := by
          refine (mem_map_conj_iff (H := D.map C.subtype)).mpr ?_
          show x⁻¹ * (x * (k : G) * x⁻¹) * x ∈ D.map C.subtype
          rw [show x⁻¹ * (x * (k : G) * x⁻¹) * x = (k : G) from by group]
          exact Subgroup.mem_map.mpr ⟨k, hkD, rfl⟩
        exact h1
      exact Subgroup.mem_map.mpr ⟨k', hD'le hk'D', rfl⟩
    show (MulAut.conj x) (k : G) ∈ (Work.Fitting.pPrimeCore p ↥C).map C.subtype
    have hgoal : (MulAut.conj x) (k : G) = x * (k : G) * x⁻¹ := MulAut.conj_apply x k
    rw [hgoal]
    exact hmem
  refine le_antisymm hle ?_
  have hcard : Nat.card ↥((pPrimeCoreSub p C).map (MulAut.conj x).toMonoidHom) =
      Nat.card ↥(pPrimeCoreSub p C) :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  exact ge_of_eq (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm))

section

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- `N_G(P) ⊓ W` normalizes the centralizer `C_W(P) = C_G(P) ⊓ W`: conjugation by an element
of `N_G(P) ⊓ W` permutes both `P` and `W`. -/
private lemma normalizer_inf_le_normalizer_centralizer_inf {P W : Subgroup G} :
    Subgroup.normalizer (P : Set G) ⊓ W ≤
      Subgroup.normalizer ((Subgroup.centralizer (P : Set G) ⊓ W : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx c hc
  have hxP : x ∈ Subgroup.normalizer (P : Set G) := hx.1
  have hxW : x ∈ W := hx.2
  have hcC : c ∈ Subgroup.centralizer (P : Set G) := hc.1
  have hcW : c ∈ W := hc.2
  refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem hxW hcW) (inv_mem hxW)⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : x⁻¹ * a * x ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hxP (x⁻¹ * a * x)).mpr (by
      show x * (x⁻¹ * a * x) * x⁻¹ ∈ P
      rwa [show x * (x⁻¹ * a * x) * x⁻¹ = a from by group])
  have hcomm := (Subgroup.mem_centralizer_iff.mp hcC) (x⁻¹ * a * x) ha'
  calc a * (x * c * x⁻¹) = x * ((x⁻¹ * a * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * a * x)) * x⁻¹ := by rw [hcomm]
    _ = (x * c * x⁻¹) * a := by group

end

theorem isSylowIn_of_sylowIn_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E W : Subgroup G} (hEW : E ≤ W) {P : Subgroup G}
    (hPsyl : Work.NormalComplement.IsSylowIn p P E)
    (h1 : Subgroup.normalizer (P : Set G) ⊓ W =
      Work.NormalComplement.pPrimeCoreSub p (Subgroup.centralizer (P : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (P : Set G) ⊓ E)) :
    Work.NormalComplement.IsSylowIn p P W := by
  have hP : IsPGroup p P := hPsyl.1
  have hPE : P ≤ E := hPsyl.2.1
  have hPW : P ≤ W := hPE.trans hEW
  have hnotE : ¬ p ∣ (P.subgroupOf E).index := hPsyl.2.2
  set N : Subgroup G := Subgroup.normalizer (P : Set G) ⊓ W with hN
  set M : Subgroup G := Subgroup.normalizer (P : Set G) ⊓ E with hM
  set C : Subgroup G := Subgroup.centralizer (P : Set G) ⊓ W with hC
  set Q : Subgroup G := Work.NormalComplement.pPrimeCoreSub p C with hQ
  have hPM : P ≤ M := le_inf Subgroup.le_normalizer hPE
  have hME : M ≤ E := inf_le_right
  have hMN : M ≤ N := le_inf inf_le_left (le_trans inf_le_right hEW)
  have hNQ : N = Q ⊔ M := h1
  -- `N_W(P)` normalizes `O_{p'}(C_W(P))`
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    refine le_trans hMN (le_trans (normalizer_inf_le_normalizer_centralizer_inf (P := P)
      (W := W)) ?_)
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact map_conj_pPrimeCoreSub_eq hx
  have hnotM : ¬ p ∣ P.relIndex M := by
    intro hdvd
    have hmul : P.relIndex M * M.relIndex E = (P.subgroupOf E).index :=
      Subgroup.relIndex_mul_relIndex P M E hPM hME
    exact hnotE (hmul ▸ dvd_mul_of_dvd_left hdvd (M.relIndex E))
  have hnotN : ¬ p ∣ M.relIndex N := fun hdvd =>
    not_dvd_card_pPrimeCoreSub C
      (dvd_trans hdvd (relIndex_sup_dvd_card_of_le_normalizer hMQ hNQ))
  have hnotPN : ¬ p ∣ P.relIndex N := by
    intro hdvd
    have hmul : P.relIndex M * M.relIndex N = P.relIndex N :=
      Subgroup.relIndex_mul_relIndex P M N hPM hMN
    have h2 : p ∣ P.relIndex M * M.relIndex N := by rw [hmul]; exact hdvd
    rcases (Fact.out : p.Prime).dvd_mul.mp h2 with h3 | h3
    · exact hnotM h3
    · exact hnotN h3
  refine ⟨hP, hPW, ?_⟩
  have hpg : IsPGroup p (P.subgroupOf W) :=
    IsPGroup.of_equiv hP (Subgroup.subgroupOfEquivOfLe hPW).symm
  have hnorm : Subgroup.normalizer ((P.subgroupOf W : Subgroup W) : Set W) = N.subgroupOf W := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPW, Subgroup.inf_subgroupOf_right]
  have hrel : (P.subgroupOf W).relIndex
      (Subgroup.normalizer ((P.subgroupOf W : Subgroup W) : Set W)) = P.relIndex N := by
    rw [hnorm]
    exact Subgroup.relIndex_subgroupOf (H := P) (K := N) (L := W) inf_le_right
  refine Work.DoubleTransitivity.App2.not_dvd_index_of_not_dvd_relIndex_normalizer
    (G := W) (Q := P.subgroupOf W) hpg ?_
  rw [hrel]
  exact hnotPN

end Work.NormalComplement
