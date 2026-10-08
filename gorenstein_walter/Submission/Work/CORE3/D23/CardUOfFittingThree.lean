import Mathlib
import Submission.Work.CORE3.D23.Core23A
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.ASM.FT
import Submission.OddOrder.GroupTheory.FittingSelfCentralizing

namespace Work.CORE3.D23

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## The two group-theoretic ingredients of L4

* `le_centralizer_fittingIn_of_card_three`: a subgroup of odd order acts trivially (by
  conjugation) on a subgroup of order `3` — the induced automorphisms have order dividing both
  the (odd) order of the acting element and `2 = |Aut(C₃)|`.
* `centralizer_fittingIn_inf_le`: Fitting's self-centralizing lemma in Bender's relative
  notation (`C_K(F(K)) ≤ F(K)` for solvable `K`), from the FT library's
  `OddOrder.GroupTheory.centralizer_fitting_le_fitting`. -/

/-- `F(K) = fittingIn K` is contained in `K`. -/
theorem fittingIn_le_self_local {G : Type*} [Group G] (K : Subgroup G) :
    Work.GW2.fittingIn K ≤ K := by
  rw [Work.GW2.fittingIn]
  exact Subgroup.map_subtype_le _

/-- `K` normalises its Fitting subgroup `F(K) = fittingIn K` (characteristic in `K`). -/
theorem le_normalizer_fittingIn_local {G : Type*} [Group G] (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((Work.GW2.fittingIn K : Subgroup G) : Set G) := by
  have hN : (Work.GW2.fitting K).Normal := by
    rw [Work.GW2.fitting]
    exact Subgroup.normalCore_normal _
  have hconj : ∀ a ∈ K, ∀ x ∈ (Work.GW2.fitting K).map K.subtype,
      a * x * a⁻¹ ∈ (Work.GW2.fitting K).map K.subtype := by
    rintro a ha x ⟨y, hy, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨(⟨a, ha⟩ : ↥K) * y * (⟨a, ha⟩ : ↥K)⁻¹, hN.conj_mem y hy (⟨a, ha⟩ : ↥K), by simp⟩
  intro a ha
  rw [Work.GW2.fittingIn, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj a ha x
  · intro hx
    have h := hconj a⁻¹ (K.inv_mem ha) (a * x * a⁻¹) hx
    rwa [show a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ = x by group] at h

/-- **Odd-order subgroups act trivially on a characteristic subgroup of order `3`.**
If `Odd (Nat.card K)` and `|F(K)| = 3`, then `K ≤ C_G(F(K))`: the conjugation action of `K` on
`F(K)` has image in `MulAut F(K)`, a group of order `2 = φ(3)`, and the order of the image
divides the odd number `|K|`; hence the image is trivial. -/
theorem le_centralizer_fittingIn_of_card_three {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (hodd : Odd (Nat.card K))
    (hcard : Nat.card (Work.GW2.fittingIn K) = 3) :
    K ≤ Subgroup.centralizer ((Work.GW2.fittingIn K : Subgroup G) : Set G) := by
  classical
  have hle : K ≤ Subgroup.normalizer ((Work.GW2.fittingIn K : Subgroup G) : Set G) :=
    le_normalizer_fittingIn_local K
  haveI : IsCyclic ↥(Work.GW2.fittingIn K) := isCyclic_of_prime_card hcard
  have hAut : Nat.card (MulAut ↥(Work.GW2.fittingIn K)) = 2 := by
    rw [IsCyclic.card_mulAut, hcard, Nat.totient_prime Nat.prime_three]
  let φ : ↥K →* MulAut ↥(Work.GW2.fittingIn K) :=
    (Subgroup.normalizerMonoidHom (Work.GW2.fittingIn K)).comp (Subgroup.inclusion hle)
  intro x hx
  have hxord : orderOf (⟨x, hx⟩ : ↥K) = orderOf x := (Subgroup.orderOf_coe ⟨x, hx⟩).symm
  have hdvd : orderOf (φ ⟨x, hx⟩) ∣ Nat.card K := by
    have h1 := orderOf_map_dvd φ ⟨x, hx⟩
    rw [hxord] at h1
    exact h1.trans (Subgroup.orderOf_dvd_natCard K hx)
  have hoddα : Odd (orderOf (φ ⟨x, hx⟩)) := hodd.of_dvd_nat hdvd
  have hdvd2 : orderOf (φ ⟨x, hx⟩) ∣ 2 := by
    have h1 := orderOf_dvd_natCard (φ ⟨x, hx⟩)
    rwa [hAut] at h1
  have hα1 : φ ⟨x, hx⟩ = 1 := by
    have h1 : orderOf (φ ⟨x, hx⟩) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact h
      · exfalso
        obtain ⟨k, hk⟩ := hoddα
        omega
    exact orderOf_eq_one_iff.mp h1
  have hmem : Subgroup.inclusion hle ⟨x, hx⟩ ∈
      (Subgroup.normalizerMonoidHom (Work.GW2.fittingIn K)).ker := by
    rw [MonoidHom.mem_ker]
    exact hα1
  rw [Subgroup.normalizerMonoidHom_ker] at hmem
  have h2 := Subgroup.mem_subgroupOf.mp hmem
  simpa [Subgroup.coe_inclusion] using h2

/-- **Fitting's self-centralizing lemma in Bender's relative notation**: for a solvable
subgroup `K`, `C_K(F(K)) ≤ F(K)`.

This is `OddOrder.GroupTheory.centralizer_fitting_le_fitting` applied in `↥K`, translated along
the bridge `Work.CORE2A.fitting_eq_isaacsFitting`. -/
theorem centralizer_fittingIn_inf_le {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hsolv : Group.IsSolvable ↥K) :
    Subgroup.centralizer ((Work.GW2.fittingIn K : Subgroup G) : Set G) ⊓ K ≤
      Work.GW2.fittingIn K := by
  haveI : Group.IsSolvable ↥K := hsolv
  intro x hx
  obtain ⟨hxcen, hxK⟩ := Subgroup.mem_inf.mp hx
  have hcen : (⟨x, hxK⟩ : ↥K) ∈
      Subgroup.centralizer ((Work.GW2.fitting ↥K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hy' : (y : G) ∈ Work.GW2.fittingIn K := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have h := (Subgroup.mem_centralizer_iff.mp hxcen) (y : G) hy'
    simpa using h
  have hcen' : (⟨x, hxK⟩ : ↥K) ∈
      Subgroup.centralizer ((OddOrder.Isaacs.Ch01.fitting ↥K : Subgroup ↥K) : Set ↥K) := by
    rw [← Work.CORE2A.fitting_eq_isaacsFitting (G := ↥K)]
    exact hcen
  have hmem := OddOrder.GroupTheory.centralizer_fitting_le_fitting (G := ↥K) hcen'
  have hmem' : (⟨x, hxK⟩ : ↥K) ∈ Work.GW2.fitting ↥K := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting (G := ↥K)]
    exact hmem
  exact Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, hmem', rfl⟩

/-- **L4 of GW design pass 23 §A** (Bender 1981, p. 224, (7), last step), in the unfolded form of
`Work.CORE3.D23.CardUOfFittingThreeProp`: if the Fitting subgroup `F(U)` of `U = O(Ĥ)` has order
`3`, then `|U| = 3`.

Route.  `F(U) = fittingIn B.U` is characteristic in `U`, so `U` acts on it and the image of `U`
in `Aut(F(U)) = Aut(C₃)` has order dividing `2`; `U` is odd (`Work.CORE2A.bSetup_U_odd`), so the
image is trivial, i.e. `U = C_U(F(U))`.  Frobenius' theorem (Fitting's self-centralizing lemma) in
the FT library, `OddOrder.GroupTheory.centralizer_fitting_le_fitting`, applied with `H := U`
(solvable because `U` is odd, by Feit–Thompson — the toolkit field `I.T.ft`, or the top-level
`Work.GW2.feitThompsonProp`), gives `C_U(F(U)) ≤ F(U)`, whence `|U| ∣ 3`; `F(U)` has order `3`, so
`1 < |U|` and `|U| = 3`.  The same tool is used at `Submission/Work/CORE2B/HallAux.lean:277`. -/
theorem CardUOfFittingThree (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (h : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hF : Nat.card (Work.GW2.fittingIn B.U) = 3) :
    Nat.card B.U = 3 := by
  have hodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hsolv : Group.IsSolvable ↥B.U := I.T.ft ↥B.U hodd
  have hsub : B.U ≤ Work.GW2.fittingIn B.U := by
    intro x hx
    exact centralizer_fittingIn_inf_le B.U hsolv
      (Subgroup.mem_inf.mpr ⟨le_centralizer_fittingIn_of_card_three B.U hodd hF hx, hx⟩)
  have heq : B.U = Work.GW2.fittingIn B.U := le_antisymm hsub (fittingIn_le_self_local B.U)
  rw [heq]
  exact hF

end Work.CORE3.D23
