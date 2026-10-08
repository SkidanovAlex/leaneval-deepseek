import Mathlib
import Submission.Work.CORE4.Defs27
import Submission.Work.CORE4.Case2AmalgamSetup
import Submission.Work.CORE4.Case2PNotConjKp9
import Submission.Work.CORE4.Case2CountImpl9
import Submission.Work.CORE4.mem_A_of_mem_inConjSet
import Submission.Work.CORE4.BadCountInH
import Submission.Work.CORE4.L2TorusNormE
import Submission.Work.CORE4.ConjSub.conjSub_mul
import Submission.Work.CORE4.ConjSub.normalizer_conjSub
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2NormalizerP
import Submission.Work.CORE4.PerZConjLayer
import Submission.Work.CORE4.PerZDirect
import Submission.Work.CORE4.PerZKpUniq
import Submission.Work.CORE4.PerZWitFacts

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

/-! ## §1  Helper lemmas -/

/-- Conjugating a centralizer inclusion. -/
theorem perZ_conjSub_le_centralizer {G : Type} [Group G] (g : G) {A B : Subgroup G}
    (h : A ≤ Subgroup.centralizer (B : Set G)) :
    Work.GW2.conjSub g A ≤
      Subgroup.centralizer ((Work.GW2.conjSub g B : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨x₀, hx₀, rfl⟩ := (Work.CORE4.ConjSub.mem_conjSub (g := g) (K := A)).mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := (Work.CORE4.ConjSub.mem_conjSub (g := g) (K := B)).mp hy
  have h1 := Subgroup.mem_centralizer_iff.mp (h hx₀) y₀ hy₀
  calc (g * y₀ * g⁻¹) * (g * x₀ * g⁻¹) = g * (y₀ * x₀) * g⁻¹ := by group
    _ = g * (x₀ * y₀) * g⁻¹ := by rw [h1]
    _ = (g * x₀ * g⁻¹) * (g * y₀ * g⁻¹) := by group

/-- Conjugation carries centralizers to centralizers. -/
theorem perZ_conjSub_centralizer {G : Type} [Group G] (g : G) (A : Subgroup G) :
    Work.GW2.conjSub g (Subgroup.centralizer (A : Set G)) =
      Subgroup.centralizer ((Work.GW2.conjSub g A : Subgroup G) : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, rfl⟩ :=
      (Work.CORE4.ConjSub.mem_conjSub (g := g) (K := Subgroup.centralizer (A : Set G))).mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (Work.CORE4.ConjSub.mem_conjSub (g := g) (K := A)).mp hy
    have h1 := Subgroup.mem_centralizer_iff.mp hc a ha
    calc (g * a * g⁻¹) * (g * c * g⁻¹) = g * (a * c) * g⁻¹ := by group
      _ = g * (c * a) * g⁻¹ := by rw [h1]
      _ = (g * c * g⁻¹) * (g * a * g⁻¹) := by group
  · intro hx
    refine (Work.CORE4.ConjSub.mem_conjSub (g := g)
      (K := Subgroup.centralizer (A : Set G))).mpr ⟨g⁻¹ * x * g, ?_, by group⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hy : g * a * g⁻¹ ∈ Work.GW2.conjSub g A :=
      (Work.CORE4.ConjSub.mem_conjSub (g := g) (K := A)).mpr ⟨a, ha, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp hx (g * a * g⁻¹) hy
    calc a * (g⁻¹ * x * g) = g⁻¹ * ((g * a * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * a * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * x * g) * a := by group

/-- `Y ≤ C(P^g)` when `Y = Z^g` with `Z ≤ P ⊔ E`, `P` commuting with `P` and `E`. -/
theorem perZ_le_centralizer_conjSub {G : Type} [Group G] [Finite G] {P E : Subgroup G}
    (hPcE : P ≤ Subgroup.centralizer (E : Set G))
    (hPcP : P ≤ Subgroup.centralizer (P : Set G)) {g : G} {Y Z : Subgroup G}
    (hYZ : Y = Work.GW2.conjSub g Z) (hZle : Z ≤ P ⊔ E) :
    Y ≤ Subgroup.centralizer ((Work.GW2.conjSub g P : Subgroup G) : Set G) := by
  have hPcentPE : P ≤ Subgroup.centralizer ((P ⊔ E : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_sup]
    exact le_inf hPcP hPcE
  have hXcent := perZ_conjSub_le_centralizer g hPcentPE
  have hYle : Y ≤ Work.GW2.conjSub g (P ⊔ E) := by
    rw [hYZ]; exact Subgroup.map_mono hZle
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (hXcent hx) y (hYle hy)).symm

/-- Two distinct order-`p` subgroups of an elementary abelian group of order `p²` generate it. -/
theorem perZ_eq_sup_of_two_prime_subgroups {G : Type} [Group G] [Finite G] {p : ℕ}
    {P X A : Subgroup G} (hp : p.Prime) (hPA : P ≤ A) (hXA : X ≤ A)
    (hAcard : Nat.card ↥A = p ^ 2) (hPcard : Nat.card ↥P = p) (hXcard : Nat.card ↥X = p)
    (hne : X ≠ P) : A = P ⊔ X := by
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

/-- The set of order-`p` subgroups of `(X ⊔ E') ⊓ C_G(Z)`. -/
def perZSet {G : Type} [Group G] (X Eh Z : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {Z' : Subgroup G | Z' ≤ (X ⊔ Eh) ⊓ Subgroup.centralizer (Z : Set G) ∧ Nat.card Z' = p}

/-- Design-27 leaf `Work.GW2.C27.PerZProp I` (see `Submission/Work/_design_gw/Core27.lean:198`,
`CORE4/Defs27.lean`), conditional on the copy statement and the four-group centralizer fact:
`CopyLocalProp → FourCentProp I → PerZProp I`.

In words (Bender p. 227, the symmetric half of the double count): in the `AmalgamCtx`,
`𝓓 = inConjSet P (layerIn h.D.M)`, `X = conjSub g P`, every partner
`Z ∈ amalgamWit E (A ⊓ h.D.K) X (qOf h)` is centralized by at most `qOf h - 1` bad
`Y ∈ amalgamSII P E g`.

Route (design docstring): if no bad `Y` centralizes `Z` the count is `0`.  Otherwise `[Z,X] ≠ 1`
(`NOTES_CASE2COUNTIMPL9E.md` §1(3)).  Replace `g` by `h' ∈ H` with `P^{h'} = X`, `A^{h'} = A`
(`Case2AmalgamSetup`; `h'⁻¹g ∈ M` preserves `𝓓`, so the bad set is unchanged).  `CopyLocalProp` in
the copy: `(P₀, E₀, T₀, X₁, Y) = (X, E^{h'}, K_p^{h'}, P, Z)` — `P ≤ A = A^{h'} = X × K_p^{h'}`,
`Z ≤ W ≤ C(P)`, `¬ X ≤ C(Z)`, the four-group hypothesis is `FourCentProp` conjugated by `h'`
(`N_G(X) = M^{h'}`).  A bad `Y` centralizing `Z` is an order-`p` subgroup of `C_{W^{h'}}(Z)` other
than `P` (`P ∈ 𝓓`), so there are `≤ qOf h` of them, and `X` is one of those but is not bad.

Must be sorry-free: `#print axioms Work.CORE4.PerZ` = `[propext, Classical.choice, Quot.sound]`. -/
theorem PerZ (I : Work.GW2.C4Inputs) (hCopy : Work.GW2.C27.CopyLocalProp)
    (hFour : Work.GW2.C27.FourCentProp I) : Work.GW2.C27.PerZProp I := by
  intro G _ _ hbc B h h2 hplus h7 h8 p P A hp hPF hPcard hObj g hgne hgle Z hZ
  classical
  haveI hpFact : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Work.CORE4.nineP h).Prime := ⟨Work.CORE4.nineP_prime h⟩
  -- ## §4 (8): `Kp = A ⊓ K`, `A = P ⊔ Kp`, parity of `p`
  obtain ⟨Kp, hKpK, hKpcard, hKpomega, hAeq⟩ := Work.CORE4.exists_Kp_A_eq I h hp hPF hPcard hObj
  obtain ⟨hpodd, hp2, hpne⟩ := Work.CORE4.p_parity_facts I hbc h hp hPF hPcard hObj
  have hAexp : ∀ x ∈ A, x ^ p = 1 := hObj.2.2.2.2.2.1
  have hAcard : Nat.card ↥A = p ^ 2 := hObj.2.2.2.2.1
  have hPleA : P ≤ A := hObj.2.2.2.2.2.2.1
  have hApe : A ≤ P ⊔ Work.GW2.layerIn h.D.M := by
    rw [hAeq]
    exact sup_le le_sup_left (hKpK.trans ((Work.CORE4.K_le_layerIn B h).trans le_sup_right))
  have hKpE : Kp ≤ Work.GW2.layerIn h.D.M := hKpK.trans (Work.CORE4.K_le_layerIn B h)
  have hPne : P ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hPcard
    exact hp.ne_one hPcard.symm
  have hPcentE : P ≤ Subgroup.centralizer (Work.GW2.layerIn h.D.M : Set G) :=
    hPF.trans (Work.GW2.Case2Pre.F_cent B h.D h.pre)
  have hPcentP : P ≤ Subgroup.centralizer (P : Set G) := by
    haveI : IsCyclic ↥P := isCyclic_of_prime_card hPcard
    exact Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hXcard : Nat.card ↥(Work.GW2.conjSub g P) = p := by
    rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hPcard]
  have hAeqPX : A = P ⊔ Work.GW2.conjSub g P :=
    perZ_eq_sup_of_two_prime_subgroups hp hPleA hgle hAcard hPcard hXcard hgne
  -- ## Bender's `h'`
  obtain ⟨h', hh'H, hh'P, hh'A⟩ :=
    Work.CORE4.Case2AmalgamSetup I G hbc B h p P A hp hPF hPcard hObj
      (Work.GW2.conjSub g P) hgle hgne ⟨g, rfl⟩
  have hEgh' : Work.GW2.conjSub g (Work.GW2.layerIn h.D.M) =
      Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) :=
    PerZConjLayer I G hbc B h p P g h' hp hPF hPcard hh'P.symm
  have hAeqh : A = Work.GW2.conjSub h' P ⊔ Work.GW2.conjSub h' Kp := by
    rw [← hh'A, hAeq, Work.CORE4.conjSub_sup']
  have hAeqXK : A = Work.GW2.conjSub g P ⊔ Work.GW2.conjSub h' Kp := by
    rw [← hh'P]; exact hAeqh
  -- ## the facts about the partner `Z`
  obtain ⟨hZX, hZinD, hZcard, hZcP⟩ :=
    PerZWitFacts I G hbc B h p P A Kp g hp hPF hPcard hObj hKpK hKpcard hKpomega hAeq hgle Z hZ
  have hPcZ : P ≤ Subgroup.centralizer (Z : Set G) := Subgroup.le_centralizer_iff.mp hZcP
  -- ## the copy `W^{h'} = X ⊔ E^{h'}`
  have hXcentEh : Work.GW2.conjSub g P ≤
      Subgroup.centralizer ((Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) : Subgroup G) : Set G) := by
    have h1 := perZ_conjSub_le_centralizer (g := h') hPcentE
    rwa [hh'P] at h1
  have hcenterE : Subgroup.center ↥(Work.GW2.layerIn h.D.M) = ⊥ := by
    obtain ⟨pF, kF, hpF, hpFodd, h7q, hφ, -⟩ := h.nine
    haveI : Fact pF.Prime := hpF
    obtain ⟨φ⟩ := hφ
    exact Work.CORE4.center_eq_bot_of_mulEquiv φ
      (Work.CORE4.center_PSL2_bot pF kF hpFodd (by omega))
  have hcenterEh : Subgroup.center ↥(Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M)) = ⊥ :=
    Work.CORE4.center_eq_bot_of_mulEquiv
      (Subgroup.equivMapOfInjective (Work.GW2.layerIn h.D.M) (MulAut.conj h').toMonoidHom
        (MulAut.conj h').injective).symm hcenterE
  have hXinfEh : Work.GW2.conjSub g P ⊓ Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) = ⊥ :=
    Work.CORE4.inf_eq_bot_of_le_centralizer hXcentEh hcenterEh
  have hKphE : Work.GW2.conjSub h' Kp ≤ Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) :=
    Subgroup.map_mono hKpE
  have hKphcard : Nat.card ↥(Work.GW2.conjSub h' Kp) = p := by
    rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj h').injective, hKpcard]
  have hcycE : IsCyclic ↥(Work.GW2.layerIn h.D.M ⊓ Subgroup.centralizer (Kp : Set G)) := by
    have h1 := (Work.CORE4.L2TorusNormE I G hbc B h p Kp hp hp2 hpne hKpE hKpcard).1
    rw [inf_comm]
    exact h1
  have hconjinf : Work.GW2.conjSub h'
        (Work.GW2.layerIn h.D.M ⊓ Subgroup.centralizer (Kp : Set G)) =
      Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) ⊓
        Subgroup.centralizer (Work.GW2.conjSub h' Kp : Set G) := by
    have h2 : Work.GW2.conjSub h'
          (Work.GW2.layerIn h.D.M ⊓ Subgroup.centralizer (Kp : Set G)) =
        Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) ⊓
          Work.GW2.conjSub h' (Subgroup.centralizer (Kp : Set G)) := by
      simp only [Work.GW2.conjSub]
      rw [Subgroup.map_inf_eq]
      exact (MulAut.conj h').injective
    rwa [perZ_conjSub_centralizer] at h2
  have hcyc : IsCyclic ↥(Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) ⊓
      Subgroup.centralizer (Work.GW2.conjSub h' Kp : Set G)) := by
    rw [← hconjinf]
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective
      (Work.GW2.layerIn h.D.M ⊓ Subgroup.centralizer (Kp : Set G))
      (MulAut.conj h').toMonoidHom (MulAut.conj h').injective)).mp hcycE
  obtain ⟨φ⟩ := Work.CORE4.nineP_iso h
  have hiso : Nonempty (↥(Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M)) ≃*
      PSL(2, GaloisField (Work.CORE4.nineP h) (Work.CORE4.nineK h))) :=
    ⟨(Subgroup.equivMapOfInjective (Work.GW2.layerIn h.D.M) (MulAut.conj h').toMonoidHom
        (MulAut.conj h').injective).symm.trans φ⟩
  have h5 : 5 ≤ Work.CORE4.nineP h ^ Work.CORE4.nineK h := by
    have h7q := Work.CORE4.nineP_seven h
    simp only [Work.CORE4.qOf] at h7q
    omega
  -- ## the four-group hypothesis of `CopyLocalProp`
  have hfour : ∀ V : Subgroup G, V ≤ Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) →
      Work.GW2.IsFourGroup V → Z ≤ Subgroup.centralizer (V : Set G) →
      Z ≤ Subgroup.normalizer (Work.GW2.conjSub g P : Set G) := by
    intro V hVE hV4 hZV
    have hV4' : Work.GW2.IsFourGroup (Work.GW2.conjSub h'⁻¹ V) := by
      refine ⟨?_, ?_⟩
      · rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj h'⁻¹).injective]
        exact hV4.1
      · intro v hv
        obtain ⟨w, hw, rfl⟩ := (Work.CORE4.ConjSub.mem_conjSub (g := h'⁻¹) (K := V)).mp hv
        have h2 : (h'⁻¹ * w * h'⁻¹⁻¹) ^ 2 = h'⁻¹ * w ^ 2 * h'⁻¹⁻¹ := by
          rw [pow_two, pow_two]; group
        rw [h2, hV4.2 w hw]
        group
    have hVE' : Work.GW2.conjSub h'⁻¹ V ≤ Work.GW2.layerIn h.D.M := by
      have h1 : Work.GW2.conjSub h'⁻¹ V ≤ Work.GW2.conjSub h'⁻¹
          (Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M)) := Subgroup.map_mono hVE
      rwa [show Work.GW2.conjSub h'⁻¹ (Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M)) =
          Work.GW2.layerIn h.D.M from by
        rw [← Work.CORE4.ConjSub.conjSub_mul, inv_mul_cancel, Work.CORE4.conjSub_one]] at h1
    have hZV' : Work.GW2.conjSub h'⁻¹ Z ≤
        Subgroup.centralizer (Work.GW2.conjSub h'⁻¹ V : Set G) :=
      perZ_conjSub_le_centralizer h'⁻¹ hZV
    have hZodd : Odd (Nat.card ↥(Work.GW2.conjSub h'⁻¹ Z)) := by
      rw [Work.GW2.conjSub, Subgroup.card_map_of_injective (MulAut.conj h'⁻¹).injective,
        hZcard]
      exact hpodd
    have hZM : Work.GW2.conjSub h'⁻¹ Z ≤ h.D.M :=
      hFour G hbc B h h2 hplus h7 (Work.GW2.conjSub h'⁻¹ V) hVE' hV4'
        (Work.GW2.conjSub h'⁻¹ Z) hZodd hZV'
    have hNX : Subgroup.normalizer (Work.GW2.conjSub g P : Set G) =
        Work.GW2.conjSub h' h.D.M := by
      rw [← hh'P, Work.CORE4.ConjSub.normalizer_conjSub,
        Work.CORE4.Case2NormalizerP G B h P hPF hPne]
    rw [hNX]
    have hZZ : Z = Work.GW2.conjSub h' (Work.GW2.conjSub h'⁻¹ Z) := by
      rw [← Work.CORE4.ConjSub.conjSub_mul, mul_inv_cancel, Work.CORE4.conjSub_one]
    rw [hZZ]
    exact Subgroup.map_mono hZM
  -- ## the set to be counted
  set SZ : Set (Subgroup G) := {Y : Subgroup G |
      Y ∈ Work.GW2.C27.amalgamSII P (Work.GW2.layerIn h.D.M) g ∧
        Y ≤ Subgroup.centralizer (Z : Set G)} with hSZ
  -- ## the uniqueness of the order-`p` subgroup of `C_{E^{h'}}(Kp^{h'})`
  have huniq : ∀ Z' : Subgroup G, Z' ≤ Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) →
      Nat.card ↥Z' = p → Z' ≤ Subgroup.centralizer (Work.GW2.conjSub h' Kp : Set G) →
      Z' = Work.GW2.conjSub h' Kp :=
    fun Z' h1 h2 h3 =>
      PerZKpUniq I G hbc B h p P A Kp h' Z' hp hPF hPcard hObj hKpK hKpcard h1 h2 h3
  have hPinD : P ∈ Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M) :=
    ⟨le_sup_left, ⟨1, (Work.CORE4.conjSub_one P).symm⟩⟩
  by_cases hXCZ : Work.GW2.conjSub g P ≤ Subgroup.centralizer (Z : Set G)
  · -- ## Case A: `X ≤ C(Z)`: the counted set is empty
    have hZCX : Z ≤ Subgroup.centralizer (Work.GW2.conjSub g P : Set G) :=
      Subgroup.le_centralizer_iff.mp hXCZ
    have hZCA : Z ≤ Subgroup.centralizer (A : Set G) := by
      rw [hAeqPX, Subgroup.centralizer_sup]
      exact le_inf hZcP hZCX
    have hZleA : Z ≤ A :=
      Work.CORE4.mem_A_of_mem_inConjSet I hbc h hp hPF hPcard hObj Z hZinD hZCA
    have hXZA : A = Work.GW2.conjSub g P ⊔ Z :=
      perZ_eq_sup_of_two_prime_subgroups hp hgle hZleA hAcard hXcard hZcard hZX
    have hEmpty : SZ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro Y hY
      rw [hSZ] at hY
      simp only [Set.mem_ofPred_eq] at hY
      obtain ⟨hYSII, hYCZ⟩ := hY
      simp only [Work.GW2.C27.amalgamSII, Set.mem_ofPred_eq] at hYSII
      obtain ⟨⟨Z₁, hZ₁, hYZ₁⟩, hYnotD, -⟩ := hYSII
      obtain ⟨hZ₁le, u, hu⟩ := hZ₁
      have hYeq : Y = Work.GW2.conjSub (g * u) P := by
        rw [hYZ₁, hu, Work.CORE4.ConjSub.conjSub_mul]
      have hYcard : Nat.card ↥Y = p := by
        rw [hYeq, Work.GW2.conjSub,
          Subgroup.card_map_of_injective (MulAut.conj (g * u)).injective, hPcard]
      have hYX : Y ≤ Subgroup.centralizer ((Work.GW2.conjSub g P : Subgroup G) : Set G) :=
        perZ_le_centralizer_conjSub hPcentE hPcentP hYZ₁ hZ₁le
      have hYCA : Y ≤ Subgroup.centralizer (A : Set G) := by
        rw [hXZA, Subgroup.centralizer_sup]
        exact le_inf hYX hYCZ
      have hYleCopy : Y ≤ Work.GW2.conjSub g P ⊔
          Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) := by
        have h1 : Y ≤ Work.GW2.conjSub g (P ⊔ Work.GW2.layerIn h.D.M) := by
          rw [hYZ₁]; exact Subgroup.map_mono hZ₁le
        rw [Work.CORE4.conjSub_sup', hEgh'] at h1
        exact h1
      have hYXinf : Y ⊓ Work.GW2.conjSub g P = ⊥ := by
        have hYXne : Y ≠ Work.GW2.conjSub g P := by
          intro hYXe
          have hXinD : Work.GW2.conjSub g P ∈
              Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M) :=
            ⟨hgle.trans hApe, ⟨g, rfl⟩⟩
          exact hYnotD (hYXe ▸ hXinD)
        have hconj : Y = Work.GW2.conjSub ((g * u) * g⁻¹)
            (Work.GW2.conjSub g P) := by
          rw [hYeq, ← Work.CORE4.ConjSub.conjSub_mul]
          congr 1
          group
        exact (Work.CORE4.Fibre9CardConj hp hXcard
          ⟨(g * u) * g⁻¹, hconj⟩ hYXne).2
      have hYA : Y ≤ A :=
        PerZDirect hXinfEh hXcentEh hKphE hKphcard huniq hAeqXK hYcard hYleCopy
          hYXinf (Subgroup.le_centralizer_iff.mp hYCA)
      exact hYnotD ⟨hYA.trans hApe, ⟨g * u, hYeq⟩⟩
    rw [hEmpty]
    simp
  · -- ## Case B: `¬ X ≤ C(Z)`: `CopyLocalProp` bounds the set
    have hPAKh : P ≤ Work.GW2.conjSub h' P ⊔ Work.GW2.conjSub h' Kp := by
      rw [← hAeqh]; exact hPleA
    have hPAXK : P ≤ Work.GW2.conjSub g P ⊔ Work.GW2.conjSub h' Kp := by
      rw [← hh'P]; exact hPAKh
    have hPleCopy : P ≤ Work.GW2.conjSub g P ⊔
        Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) :=
      hPAXK.trans (sup_le_sup_left hKphE (Work.GW2.conjSub g P))
    have hAK : A ⊓ h.D.K = Kp := by
      refine le_antisymm ?_ (le_inf (hAeq ▸ le_sup_right) hKpK)
      intro x hx
      exact (hKpomega x (Subgroup.mem_inf.mp hx).2).mp (hAexp x (Subgroup.mem_inf.mp hx).1)
    have hPKph : P ≠ Work.GW2.conjSub h' Kp := by
      intro heq
      have hbad := Work.CORE4.Case2PNotConjKp9 I G hbc B h h2 hplus h7 h8 p P A
        hp hPF hPcard hObj
      apply hbad
      refine ⟨h'⁻¹, ?_⟩
      rw [hAK, heq, ← Work.CORE4.ConjSub.conjSub_mul, inv_mul_cancel,
        Work.CORE4.conjSub_one]
    have hmemT : P ∈ perZSet (Work.GW2.conjSub g P)
        (Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M)) Z p :=
      ⟨le_inf hPleCopy hPcZ, hPcard⟩
    have hsub : SZ ⊆ perZSet (Work.GW2.conjSub g P)
        (Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M)) Z p \ {P} := by
      intro Y hY
      rw [hSZ] at hY
      simp only [Set.mem_ofPred_eq] at hY
      obtain ⟨hYSII, hYCZ⟩ := hY
      simp only [Work.GW2.C27.amalgamSII, Set.mem_ofPred_eq] at hYSII
      obtain ⟨⟨Z₁, hZ₁, hYZ₁⟩, hYnotD, -⟩ := hYSII
      obtain ⟨hZ₁le, u, hu⟩ := hZ₁
      have hYeq : Y = Work.GW2.conjSub (g * u) P := by
        rw [hYZ₁, hu, Work.CORE4.ConjSub.conjSub_mul]
      have hYcard : Nat.card ↥Y = p := by
        rw [hYeq, Work.GW2.conjSub,
          Subgroup.card_map_of_injective (MulAut.conj (g * u)).injective, hPcard]
      have hYleCopy : Y ≤ Work.GW2.conjSub g P ⊔
          Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M) := by
        have h1 : Y ≤ Work.GW2.conjSub g (P ⊔ Work.GW2.layerIn h.D.M) := by
          rw [hYZ₁]; exact Subgroup.map_mono hZ₁le
        rw [Work.CORE4.conjSub_sup', hEgh'] at h1
        exact h1
      refine ⟨⟨le_inf hYleCopy hYCZ, hYcard⟩, ?_⟩
      intro hYP
      exact hYnotD (hYP.symm ▸ hPinD)
    have hCL := hCopy G (Work.GW2.conjSub g P)
      (Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M)) (Work.GW2.conjSub h' Kp) P Z p
      (Work.CORE4.nineP h) (Work.CORE4.nineK h)
      (Work.CORE4.nineP_odd h) h5 hiso hp hp2 hpne hXcard hXcentEh hXinfEh
      hKphE hKphcard hcyc hPAXK hPcard hgne.symm hPKph hZcard hZcP hXCZ hfour
    have hTle : (perZSet (Work.GW2.conjSub g P)
        (Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M)) Z p).ncard ≤ Work.CORE4.qOf h := by
      rcases hCL with hsingle | ⟨R, hRE, hRcard, hRn, hall, hmod, hle⟩
      · have hsingle' : perZSet (Work.GW2.conjSub g P)
            (Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M)) Z p = {P} := hsingle
        rw [hsingle', Set.ncard_singleton]
        have h7q := Work.CORE4.nineP_seven h
        omega
      · exact hle
    calc SZ.ncard ≤ (perZSet (Work.GW2.conjSub g P)
          (Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M)) Z p \ {P}).ncard :=
          Set.ncard_le_ncard hsub
      _ = (perZSet (Work.GW2.conjSub g P)
            (Work.GW2.conjSub h' (Work.GW2.layerIn h.D.M)) Z p).ncard - 1 :=
          Set.ncard_sdiff_singleton_of_mem hmemT
      _ ≤ Work.CORE4.qOf h - 1 := Nat.sub_le_sub_right hTle 1

end Work.CORE4
