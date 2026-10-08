import Mathlib
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.Case2AmalgamSetup
import Submission.Work.CORE4.Case2PNotConjKp9
import Submission.Work.CORE4.BadCountInH
import Submission.Work.CORE4.L2TorusNormE
import Submission.Work.CORE4.Case2CountImpl9
import Submission.Work.CORE4.mem_A_of_mem_inConjSet

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

/-! ## Helper lemmas -/

section Helpers

variable {G : Type} [Group G]

/-- Conjugating a centralizer inclusion. -/
lemma conjSub_le_centralizer_c4 (g : G) {A B : Subgroup G}
    (h : A ≤ Subgroup.centralizer (B : Set G)) :
    Work.GW2.conjSub g A ≤
      Subgroup.centralizer ((Work.GW2.conjSub g B : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨x₀, hx₀, rfl⟩ := (Work.CORE4.ConjSub.mem_conjSub (g := g) (K := A)).mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := (Work.CORE4.ConjSub.mem_conjSub (g := g) (K := B)).mp hy
  have h1 := Subgroup.mem_centralizer_iff.mp (h hx₀) y₀ hy₀
  show (g * y₀ * g⁻¹) * (g * x₀ * g⁻¹) = (g * x₀ * g⁻¹) * (g * y₀ * g⁻¹)
  calc (g * y₀ * g⁻¹) * (g * x₀ * g⁻¹) = g * (y₀ * x₀) * g⁻¹ := by group
    _ = g * (x₀ * y₀) * g⁻¹ := by rw [h1]
    _ = (g * x₀ * g⁻¹) * (g * y₀ * g⁻¹) := by group

end Helpers

section Helpers2

variable {G : Type} [Group G] [Finite G]

/-- `Y ≤ C(P^g)` from `Y = Z^g` with `Z ≤ P ⊔ E` and `P` commuting with `P` and `E`. -/
lemma le_centralizer_conjSub_of_le_sup {P E : Subgroup G}
    (hPcentE : P ≤ Subgroup.centralizer (E : Set G))
    (hPcentP : P ≤ Subgroup.centralizer (P : Set G)) {g : G} {Y Z : Subgroup G}
    (hYZ : Y = Work.GW2.conjSub g Z) (hZle : Z ≤ P ⊔ E) :
    Y ≤ Subgroup.centralizer ((Work.GW2.conjSub g P : Subgroup G) : Set G) := by
  have hPcentPE : P ≤ Subgroup.centralizer ((P ⊔ E : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_sup]
    exact le_inf hPcentP hPcentE
  have hXcent := conjSub_le_centralizer_c4 g hPcentPE
  have hYle : Y ≤ Work.GW2.conjSub g (P ⊔ E) := by
    rw [hYZ]; exact Subgroup.map_mono hZle
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hXcent hx) y (hYle hy)).symm

/-- An element of `M` preserves `𝓓 = inConjSet P (E(M))`. -/
lemma conjSub_image_inConjSet_c4 {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B)
    {P : Subgroup G} (hPF : P ≤ h.D.F) (hPne : P ≠ ⊥) {m : G} (hm : m ∈ h.D.M) :
    Work.GW2.conjSub m '' inConjSet P (Work.GW2.layerIn h.D.M) =
      inConjSet P (Work.GW2.layerIn h.D.M) := by
  have hPm : Work.GW2.conjSub m P = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Work.CORE4.Case2NormalizerP G B h P hPF hPne) ▸ hm)
  have hEm : Work.GW2.conjSub m (Work.GW2.layerIn h.D.M) = Work.GW2.layerIn h.D.M := by
    have hn := h.layerIn_subgroupOf_normal
    have hle : Work.GW2.layerIn h.D.M ≤ h.D.M := Work.CORE4.layerIn_le h.D.M
    have hpt : ∀ x ∈ Work.GW2.layerIn h.D.M, m * x * m⁻¹ ∈ Work.GW2.layerIn h.D.M :=
      fun x hx => (Subgroup.normal_subgroupOf_iff hle).mp hn x m hx hm
    apply Subgroup.eq_of_le_of_card_ge
    · intro a ha
      obtain ⟨x, hx, rfl⟩ :=
        (Work.CORE4.ConjSub.mem_conjSub (g := m) (K := Work.GW2.layerIn h.D.M)).mp ha
      exact hpt x hx
    · rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj m).injective]
  have hsupm : Work.GW2.conjSub m (P ⊔ Work.GW2.layerIn h.D.M) =
      P ⊔ Work.GW2.layerIn h.D.M := by
    rw [Work.GW2.conjSub, Subgroup.map_sup]
    rw [show P.map (MulAut.conj m).toMonoidHom = P from hPm,
        show (Work.GW2.layerIn h.D.M).map (MulAut.conj m).toMonoidHom =
          Work.GW2.layerIn h.D.M from hEm]
  have hsub : Work.GW2.conjSub m '' inConjSet P (Work.GW2.layerIn h.D.M) ⊆
      inConjSet P (Work.GW2.layerIn h.D.M) := by
    rintro Y ⟨Y₀, hY₀, rfl⟩
    obtain ⟨hY₀le, u, hu⟩ := hY₀
    refine ⟨?_, m * u, ?_⟩
    · have h1 : Work.GW2.conjSub m Y₀ ≤ Work.GW2.conjSub m (P ⊔ Work.GW2.layerIn h.D.M) :=
        Subgroup.map_mono hY₀le
      rwa [hsupm] at h1
    · rw [hu, Work.CORE4.ConjSub.conjSub_mul]
  refine Set.eq_of_subset_of_ncard_le hsub ?_
  rw [Set.ncard_image_of_injective _ (Work.CORE4.conjSub_injective m)]

end Helpers2

section Helpers3

variable {G : Type} [Group G] [Finite G]

/-- `A = P ⊔ X` for two distinct order-`p` subgroups `P, X` of the elementary abelian group `A`. -/
lemma eq_sup_of_two_prime_subgroups {p : ℕ} {P X A : Subgroup G} (hp : p.Prime)
    (hPA : P ≤ A) (hXA : X ≤ A) (hAcard : Nat.card ↥A = p ^ 2)
    (hPcard : Nat.card ↥P = p) (hXcard : Nat.card ↥X = p) (hne : X ≠ P) :
    A = P ⊔ X := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hAcomm : IsMulCommutative ↥A := IsPGroup.isMulCommutative_of_card_eq_prime_sq hAcard
  have hbot : P ⊓ X = ⊥ := by
    have hdvd : Nat.card ↥(P ⊓ X) ∣ p := by
      rw [← hPcard]; exact Subgroup.card_dvd_of_le inf_le_left
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · rw [Subgroup.card_eq_one] at h1; exact h1
    · exfalso
      have hPeq : P ⊓ X = P := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hPcard])
      have hle : P ≤ X := hPeq ▸ inf_le_right
      exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hXcard, hPcard])).symm
  have hN : P ≤ Subgroup.normalizer (X : Set G) := by
    have hPCX : P ≤ Subgroup.centralizer (X : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hAcomm.is_comm.comm ⟨y, hXA hy⟩ ⟨x, hPA hx⟩)
    exact hPCX.trans (Subgroup.centralizer_le_normalizer _)
  have hcard : Nat.card ↥(P ⊔ X) = p * p := by
    rw [Work.CORE4.card_sup_of_disjoint_normalizer hbot hN, hPcard, hXcard]
  refine (Subgroup.eq_of_le_of_card_ge (sup_le hPA hXA) ?_).symm
  rw [hAcard, hcard]
  exact le_of_eq (by ring)

end Helpers3

/-! ## The main theorem -/

/-- Design-27 leaf `Work.GW2.C27.PerYProp I` (see `Submission/Work/_design_gw/Core27.lean:183`
and `CORE4/Defs27.lean`), conditional on the copy statement and the four-group centralizer fact:
`CopyLocalProp → FourCentProp I → PerYProp I`.

In words: in the `AmalgamCtx` of Bender p. 227 (`𝓓 = inConjSet P (layerIn h.D.M)`,
`W = P ⊔ E(M)`, `X = conjSub g P`), every *bad* `Y ∈ amalgamSII P E g` has at least `2p` partners
`Z ∈ amalgamWit E (A ⊓ h.D.K) X (qOf h)` centralizing it.

Route (design docstring): `CopyLocalProp` with `(P₀, E₀, T₀, X₁) = (P, layerIn h.D.M, K_p, X)`.
Inputs: `Y ∉ 𝓓 ⟹ ¬ P ≤ C(Y)` (`NOTES_CASE2COUNTIMPL9E.md` §1(2): `Y ∈ 𝓓^g`, `[Y,P] = 1` ⟹
`Y ≤ C_G(A)` ⟹ `Y ≤ A^g = A` by the copy of `BadCountInH_first`'s `key`, after `WLOG g = h'`);
`Y ≤ C(X)` (`X = Z(W^g)`); the four-group hypothesis from `FourCentProp` (`M = N_G(P)`,
`Case2NormalizerP`); `X ≠ K_p` (`P` is centralized by `S`, `K_p` is inverted by `s`).  The first
alternative of `CopyLocalProp` contradicts the witness `Z ≠ X` of `Y ∈ SII`; in the second,
`Syl_p(D) ∖ {X} ⊆ amalgamWit` and `|Syl_p(D)| ≥ 2p + 1` (the `ncard % (2p) = 1` conjunct).

Must be sorry-free: `#print axioms Work.CORE4.PerY` = `[propext, Classical.choice, Quot.sound]`. -/
theorem PerY (I : Work.GW2.C4Inputs) (hCopy : Work.GW2.C27.CopyLocalProp)
    (hFour : Work.GW2.C27.FourCentProp I) : Work.GW2.C27.PerYProp I := by
  intro G _ _ hbc B h h2 hplus h7 h8 p P A hp hPF hPcard hObj g hgne hgle
  classical
  haveI hpFact : Fact p.Prime := ⟨hp⟩
  -- ## The objects of §4 (8): `Kp = A ⊓ K`, `A = P ⊔ Kp`, the parity of `p`.
  obtain ⟨Kp, hKpK, hKpcard, hKpomega, hAeq⟩ := Work.CORE4.exists_Kp_A_eq I h hp hPF hPcard hObj
  obtain ⟨hpodd, hp2, hpne⟩ := Work.CORE4.p_parity_facts I hbc h hp hPF hPcard hObj
  have hAexp : ∀ x ∈ A, x ^ p = 1 := hObj.2.2.2.2.2.1
  have hAcard : Nat.card ↥A = p ^ 2 := hObj.2.2.2.2.1
  have hPleA : P ≤ A := hObj.2.2.2.2.2.2.1
  have hKpE : Kp ≤ Work.GW2.layerIn h.D.M := hKpK.trans (Work.CORE4.K_le_layerIn B h)
  have hPne : P ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hPcard
    exact hp.ne_one hPcard.symm
  have hAK : A ⊓ h.D.K = Kp := by
    refine le_antisymm ?_ (le_inf (hAeq ▸ le_sup_right) hKpK)
    intro x hx
    exact (hKpomega x (Subgroup.mem_inf.mp hx).2).mp (hAexp x (Subgroup.mem_inf.mp hx).1)
  haveI : Fact (nineP h).Prime := ⟨Work.CORE4.nineP_prime h⟩
  -- cyclicity of `C_E(Kp)`
  have hcyc : IsCyclic ↥(Work.GW2.layerIn h.D.M ⊓ Subgroup.centralizer (Kp : Set G)) := by
    have h1 := (Work.CORE4.L2TorusNormE I G hbc B h p Kp hp hp2 hpne hKpE hKpcard).1
    rw [inf_comm]
    exact h1
  -- `P` centralizes `P` and `E(M)`, and meets `E(M)` trivially
  have hPcentP : P ≤ Subgroup.centralizer (P : Set G) := by
    haveI : IsCyclic ↥P := isCyclic_of_prime_card hPcard
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hPcentE : P ≤ Subgroup.centralizer (Work.GW2.layerIn h.D.M : Set G) :=
    hPF.trans (Work.GW2.Case2Pre.F_cent B h.D h.pre)
  have hPEinf : P ⊓ Work.GW2.layerIn h.D.M = ⊥ := by
    refine Work.CORE4.inf_eq_bot_of_le_centralizer hPcentE ?_
    obtain ⟨pF, kF, hpF, hpFodd, h7q, hφ, -⟩ := h.nine
    haveI : Fact pF.Prime := hpF
    obtain ⟨φ⟩ := hφ
    exact Work.CORE4.center_eq_bot_of_mulEquiv φ (Work.CORE4.center_PSL2_bot pF kF hpFodd (by omega))
  -- `5 ≤ pField ^ kField`
  have h5 : 5 ≤ (nineP h) ^ (nineK h) := by
    have h7q := Work.CORE4.nineP_seven h
    simp only [Work.CORE4.qOf] at h7q
    omega
  -- `X := P^g` lies in `A = P ⊔ Kp`
  have hXcard : Nat.card ↥(Work.GW2.conjSub g P) = p := by
    rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hPcard]
  have hXA2 : Work.GW2.conjSub g P ≤ P ⊔ Kp := by rw [← hAeq]; exact hgle
  have hXneKp : Work.GW2.conjSub g P ≠ Kp := by
    intro hx
    exact (Work.CORE4.Case2PNotConjKp9 I G hbc B h h2 hplus h7 h8 p P A hp hPF hPcard hObj)
      ⟨g, by rw [hAK]; exact hx⟩
  -- ## The per-`Y` argument
  intro Y hY
  simp only [Work.GW2.C27.amalgamSII, Set.mem_ofPred_eq] at hY
  obtain ⟨⟨Z1, hZ1, hYZ1⟩, hYnotD, Z0, hZ0, hZ0ne, hYZ0⟩ := hY
  -- basic facts about `Y`
  have hYcard : Nat.card ↥Y = p := by
    obtain ⟨-, u, hu⟩ := hZ1
    rw [hYZ1, hu, ← Work.CORE4.ConjSub.conjSub_mul, Work.GW2.conjSub,
      Subgroup.card_map_of_injective (MulAut.conj (g * u)).injective, hPcard]
  have hYodd : Odd (Nat.card ↥Y) := by rw [hYcard]; exact hpodd
  have hYX : Y ≤ Subgroup.centralizer ((Work.GW2.conjSub g P : Subgroup G) : Set G) := by
    obtain ⟨hZ1le, -⟩ := hZ1
    exact le_centralizer_conjSub_of_le_sup (G := G) hPcentE hPcentP hYZ1 hZ1le
  have hZ0card : Nat.card ↥Z0 = p := by
    obtain ⟨-, u, hu⟩ := hZ0
    rw [hu, Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj u).injective, hPcard]
  -- the four-group hypothesis of `CopyLocalProp`
  have hfour : ∀ V : Subgroup G, V ≤ Work.GW2.layerIn h.D.M → Work.GW2.IsFourGroup V →
      Y ≤ Subgroup.centralizer (V : Set G) → Y ≤ Subgroup.normalizer (P : Set G) := by
    intro V hVE hV4 hYV
    have hYM : Y ≤ h.D.M := hFour G hbc B h h2 hplus h7 V hVE hV4 Y hYodd hYV
    rw [Work.CORE4.Case2NormalizerP G B h P hPF hPne]
    exact hYM
  -- `¬ P ≤ C(Y)`: conjugate to the `h'`-setting via `Case2AmalgamSetup`
  have hPnotCY : ¬ P ≤ Subgroup.centralizer (Y : Set G) := by
    intro hPY
    have hYP : Y ≤ Subgroup.centralizer (P : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hPY hx) y hy).symm
    have hAeqPX : A = P ⊔ Work.GW2.conjSub g P :=
      eq_sup_of_two_prime_subgroups (G := G) hp hPleA hgle hAcard hPcard hXcard hgne
    have hYCA : Y ≤ Subgroup.centralizer (A : Set G) := by
      rw [hAeqPX, Subgroup.centralizer_sup]
      exact le_inf hYP hYX
    -- Bender's `h'` with `P^{h'} = X` and `A^{h'} = A`
    obtain ⟨h', hh'H, hh'P, hh'A⟩ :=
      Work.CORE4.Case2AmalgamSetup I G hbc B h p P A hp hPF hPcard hObj
        (Work.GW2.conjSub g P) hgle hgne ⟨g, rfl⟩
    -- `m = h'⁻¹ g ∈ M`, so `𝓓^g = 𝓓^{h'}`
    have hconjP : Work.GW2.conjSub (h'⁻¹ * g) P = P := by
      apply Work.CORE4.conjSub_injective h'
      rw [← Work.CORE4.ConjSub.conjSub_mul, ← mul_assoc, mul_inv_cancel, one_mul, hh'P]
    have hmM : h'⁻¹ * g ∈ h.D.M := by
      rw [← Work.CORE4.Case2NormalizerP G B h P hPF hPne]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconjP
    have hDsm : Work.GW2.conjSub (h'⁻¹ * g) ''
        inConjSet P (Work.GW2.layerIn h.D.M) = inConjSet P (Work.GW2.layerIn h.D.M) :=
      conjSub_image_inConjSet_c4 h hPF hPne hmM
    have himg : Work.GW2.conjSub (h' * (h'⁻¹ * g)) '' inConjSet P (Work.GW2.layerIn h.D.M) =
        Work.GW2.conjSub h' '' (Work.GW2.conjSub (h'⁻¹ * g) ''
          inConjSet P (Work.GW2.layerIn h.D.M)) := by
      rw [Set.image_image]
      congr 1
      funext Y'
      exact Work.CORE4.ConjSub.conjSub_mul h' (h'⁻¹ * g) Y'
    have hDg : Work.GW2.conjSub g '' inConjSet P (Work.GW2.layerIn h.D.M) =
        Work.GW2.conjSub h' '' inConjSet P (Work.GW2.layerIn h.D.M) := by
      have hgm : g = h' * (h'⁻¹ * g) := by group
      rw [hgm, himg, hDsm]
    obtain ⟨Z', hZ', hYZ'⟩ : ∃ Z' : Subgroup G,
        Z' ∈ inConjSet P (Work.GW2.layerIn h.D.M) ∧ Y = Work.GW2.conjSub h' Z' := by
      have h1 : Y ∈ Work.GW2.conjSub h' '' inConjSet P (Work.GW2.layerIn h.D.M) := by
        rw [← hDg]
        exact ⟨Z1, hZ1, hYZ1.symm⟩
      obtain ⟨Z', hZ', hZ'eq⟩ := h1
      exact ⟨Z', hZ', hZ'eq.symm⟩
    -- `Z' ≤ C(A)` and `Z' ≤ A`
    have hAfix' : Work.GW2.conjSub h'⁻¹ A = A := by
      have h1 : Work.GW2.conjSub h' (Work.GW2.conjSub h'⁻¹ A) = Work.GW2.conjSub h' A := by
        rw [← Work.CORE4.ConjSub.conjSub_mul, mul_inv_cancel, Work.CORE4.conjSub_one, hh'A]
      exact Work.CORE4.conjSub_injective h' h1
    have hZ'CA : Z' ≤ Subgroup.centralizer (A : Set G) := by
      have h1 : Work.GW2.conjSub h' Z' ≤ Subgroup.centralizer (A : Set G) := by
        rw [← hYZ']; exact hYCA
      have h2 := (Work.CORE4.conjSub_le_centralizer_iff_bcih h' Z' A).mp h1
      rwa [hAfix'] at h2
    have hZ'A : Z' ≤ A :=
      Work.CORE4.mem_A_of_mem_inConjSet I hbc h hp hPF hPcard hObj Z' hZ' hZ'CA
    -- hence `Y ≤ A`, and since `Y ~ P` and `A ≤ P ⊔ E`, `Y ∈ 𝓓`
    have hYA : Y ≤ A := by
      rw [hYZ']
      calc Work.GW2.conjSub h' Z' ≤ Work.GW2.conjSub h' A := Subgroup.map_mono hZ'A
        _ = A := hh'A
    exact hYnotD (by
      refine ⟨hYA.trans (by rw [hAeq]; exact sup_le le_sup_left (hKpE.trans le_sup_right)), ?_⟩
      obtain ⟨-, u, hu⟩ := hZ'
      exact ⟨h' * u, by rw [hYZ', hu, Work.CORE4.ConjSub.conjSub_mul]⟩)
  -- ## `CopyLocalProp`
  set Syl : Set (Subgroup G) := {Z : Subgroup G |
      Z ≤ (P ⊔ Work.GW2.layerIn h.D.M) ⊓ Subgroup.centralizer (Y : Set G) ∧ Nat.card Z = p}
    with hSyl
  set Par : Set (Subgroup G) := {Z : Subgroup G |
      Z ∈ Work.GW2.C27.amalgamWit (Work.GW2.layerIn h.D.M) (A ⊓ h.D.K)
            (Work.GW2.conjSub g P) (qOf h) ∧ Y ≤ Subgroup.centralizer (Z : Set G)} with hPar
  have hCL : Syl = {Work.GW2.conjSub g P} ∨
      ∃ R : Subgroup G, R ≤ Work.GW2.layerIn h.D.M ∧ Nat.card ↥R = qOf h ∧
        Kp ≤ Subgroup.normalizer (R : Set G) ∧
        (∀ Z : Subgroup G,
            Z ≤ (P ⊔ Work.GW2.layerIn h.D.M) ⊓ Subgroup.centralizer (Y : Set G) →
            Nat.card Z = p → ∃ c ∈ R, Z = Work.GW2.conjSub c (Work.GW2.conjSub g P)) ∧
        Syl.ncard % (2 * p) = 1 ∧ Syl.ncard ≤ qOf h :=
    hCopy G P (Work.GW2.layerIn h.D.M) Kp (Work.GW2.conjSub g P) Y p
      (Work.CORE4.nineP h) (Work.CORE4.nineK h) (Work.CORE4.nineP_odd h) h5
      (Work.CORE4.nineP_iso h) hp hp2 hpne hPcard hPcentE hPEinf hKpE hKpcard hcyc hXA2 hXcard
      hgne hXneKp hYcard hYX hPnotCY hfour
  -- the two members of `Syl`
  have hXmem : Work.GW2.conjSub g P ∈ Syl := by
    rw [hSyl]
    refine ⟨le_inf (hXA2.trans (sup_le_sup_left hKpE P)) ?_, hXcard⟩
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hYX hy) x hx).symm
  have hZ0mem : Z0 ∈ Syl := by
    rw [hSyl]
    refine ⟨le_inf hZ0.1 ?_, hZ0card⟩
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hYZ0 hy) z hz).symm
  rcases hCL with hsingle | ⟨R, hRE, hRcard, hRn, hall, hmod, hle⟩
  · rw [hsingle] at hZ0mem
    simp only [Set.mem_singleton_iff] at hZ0mem
    exact absurd hZ0mem hZ0ne
  · -- second alternative: `|Syl| ≡ 1 (mod 2p)` and `|Syl| ≥ 2`
    have h2Syl : 2 ≤ Syl.ncard := by
      have hsub : ({Work.GW2.conjSub g P, Z0} : Set (Subgroup G)) ⊆ Syl := by
        rw [Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨hXmem, hZ0mem⟩
      have hcard2 : ({Work.GW2.conjSub g P, Z0} : Set (Subgroup G)).ncard = 2 :=
        Set.ncard_pair (fun h => hZ0ne h.symm)
      calc 2 = ({Work.GW2.conjSub g P, Z0} : Set (Subgroup G)).ncard := hcard2.symm
        _ ≤ Syl.ncard := Set.ncard_le_ncard hsub
    have hdecomp : Syl.ncard = 2 * p * (Syl.ncard / (2 * p)) + 1 := by
      have hd := Nat.mod_add_div Syl.ncard (2 * p)
      rw [hmod] at hd
      omega
    have hk1 : 1 ≤ Syl.ncard / (2 * p) := by
      by_contra hc
      push_neg at hc
      have h0 : Syl.ncard / (2 * p) = 0 := Nat.lt_one_iff.mp hc
      rw [h0, mul_zero, zero_add] at hdecomp
      omega
    have hncard : 2 * p ≤ (Syl \ {Work.GW2.conjSub g P}).ncard := by
      rw [Set.ncard_sdiff_singleton_of_mem hXmem]
      have hkey : 2 * p ≤ 2 * p * (Syl.ncard / (2 * p)) := by
        simpa using Nat.mul_le_mul_left (2 * p) hk1
      have hkey2 : 2 * p * (Syl.ncard / (2 * p)) ≤ Syl.ncard - 1 := by omega
      exact hkey.trans hkey2
    have hsub2 : Syl \ {Work.GW2.conjSub g P} ⊆ Par := by
      intro Z hZ
      rw [Set.mem_sdiff, Set.mem_singleton_iff] at hZ
      obtain ⟨hZSyl, hZX⟩ := hZ
      rw [hSyl] at hZSyl
      obtain ⟨hZle, hZcard⟩ := hZSyl
      obtain ⟨c, hc, hZeq⟩ := hall Z hZle hZcard
      rw [hPar]
      refine ⟨?_, ?_⟩
      · refine ⟨hZX, R, hRE, hRcard, ?_, c, hc, hZeq⟩
        · rw [hAK]; exact hRn
      · intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.mp ((hZle.trans inf_le_right) hz) y hy).symm
    have hle2 : (Syl \ {Work.GW2.conjSub g P}).ncard ≤ Par.ncard := Set.ncard_le_ncard hsub2
    exact hncard.trans hle2

end Work.CORE4
