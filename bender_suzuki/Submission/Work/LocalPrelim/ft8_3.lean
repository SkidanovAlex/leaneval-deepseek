import Mathlib
import Submission.Work.LocalPrelim.Defs
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Omega1
import Submission.Work.PGroup.omega_one_eq_omega1
import Submission.Work.PGroup.omega_conj
import Submission.Work.PGroup.Symplectic.centralProduct_of_structure
import Submission.Work.PGroup.centralizer_eq_of_maximal_normal_abelian
import Submission.Work.PGroup.inf_centralizer_ne_bot_of_isPGroup
import Submission.Work.PGroup.rank_eq_rank_frattini
import Submission.Work.PGroup.rank_eq_log_card_of_isElementaryAbelian
import Submission.Work.PGroup.frattini_eq_agemo_sup_commutator
import Submission.Work.LocalPrelim.ft8_3_comm
import Submission.Work.LocalPrelim.ft8_3_fixed
import Submission.Work.LocalPrelim.rank_omega_eq_rank
import Submission.Work.LocalPrelim.ft8_3_normal_exp

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 2000000
open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.LocalPrelim

/-- `Ωᵢ` of a normal subgroup is normal. -/
theorem omega_normal_of_normal {H : Type*} [Group H] (p i : ℕ) {A : Subgroup H}
    (hA : A.Normal) : (Work.PGroup.omega p i A).Normal := by
  have hnorm : Subgroup.normalizer (A : Set H) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hA
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  intro g _
  have hg : g ∈ Subgroup.normalizer (A : Set H) := by rw [hnorm]; exact Subgroup.mem_top g
  have hg' : g⁻¹ ∈ Subgroup.normalizer (A : Set H) := by rw [hnorm]; exact Subgroup.mem_top g⁻¹
  have hconj : Work.PGroup.conjBy g (Work.PGroup.omega p i A) = Work.PGroup.omega p i A :=
    Work.PGroup.omega_conj p i A g hg
  have hconj' : Work.PGroup.conjBy g⁻¹ (Work.PGroup.omega p i A) = Work.PGroup.omega p i A :=
    Work.PGroup.omega_conj p i A g⁻¹ hg'
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hmem : MulAut.conj g • x ∈ Work.PGroup.conjBy g (Work.PGroup.omega p i A) := by
      rw [Work.PGroup.conjBy]
      exact ⟨x, hx, rfl⟩
    rwa [hconj] at hmem
  · intro hx
    have hmem : MulAut.conj g⁻¹ • (g * x * g⁻¹) ∈
        Work.PGroup.conjBy g⁻¹ (Work.PGroup.omega p i A) := by
      rw [Work.PGroup.conjBy]
      exact ⟨g * x * g⁻¹, hx, rfl⟩
    rw [hconj'] at hmem
    have heq : MulAut.conj g⁻¹ • (g * x * g⁻¹) = x := by
      show MulAut.conj g⁻¹ (g * x * g⁻¹) = x
      rw [MulAut.conj_apply]; group
    rwa [heq] at hmem

/-- The centralizer of a normal subgroup is normal. -/
theorem centralizer_normal_of_normal {X : Type*} [Group X] {A : Subgroup X} (hA : A.Normal) :
    (Subgroup.centralizer (A : Set X)).Normal := by
  refine Subgroup.Normal.mk (fun n hn g => ?_)
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro a ha
  have hga : g⁻¹ * a * g ∈ A := by simpa using hA.conj_mem a ha g⁻¹
  have h := hn (g⁻¹ * a * g) hga
  calc a * (g * n * g⁻¹) = g * ((g⁻¹ * a * g) * n) * g⁻¹ := by group
    _ = g * (n * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
    _ = (g * n * g⁻¹) * a := by group

end Work.LocalPrelim

namespace Work.LocalPrelim

open scoped Classical Pointwise commutatorElement
open Subgroup


/-- Existence of a maximal (by inclusion) normal abelian subgroup containing a given normal
abelian subgroup. -/
theorem exists_maximal_normal_abelian_ge {X : Type*} [Group X] [Finite X] {E : Subgroup X}
    (hEn : E.Normal) (hEab : IsMulCommutative E) :
    ∃ B : Subgroup X, E ≤ B ∧ B.Normal ∧ IsMulCommutative B ∧
      (∀ B' : Subgroup X, B'.Normal → IsMulCommutative B' → B ≤ B' → B' = B) := by
  classical
  let S : Set (Subgroup X) := {B | E ≤ B ∧ B.Normal ∧ IsMulCommutative B}
  have hfin : S.Finite := Set.toFinite S
  have hne : S.Nonempty := ⟨E, le_rfl, hEn, hEab⟩
  obtain ⟨B, hB, hmax⟩ :=
    Finset.exists_max_image hfin.toFinset (fun B => Nat.card B) (hfin.toFinset_nonempty.mpr hne)
  rw [Set.Finite.mem_toFinset hfin] at hB
  refine ⟨B, hB.1, hB.2.1, hB.2.2, ?_⟩
  intro B' hB'n hB'ab hle'
  have hmem : B' ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset hfin]; exact ⟨le_trans hB.1 hle', hB'n, hB'ab⟩
  have hcard : Nat.card B' ≤ Nat.card B := hmax B' hmem
  have hcard' : Nat.card B ≤ Nat.card B' := Subgroup.card_le_of_le hle'
  exact (Subgroup.eq_of_le_of_card_ge hle' hcard).symm

theorem ft8_3 {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hX : IsPGroup p X) {A : Subgroup X} (hA : IsSCN (⊤ : Subgroup X) A)
    (hmax : ∀ B : Subgroup X, IsSCN (⊤ : Subgroup X) B → Group.rank B ≤ Group.rank A) :
    Work.PGroup.omega p 1 (Subgroup.centralizer ((Work.PGroup.omega p 1 A : Subgroup X) : Set X)) =
      Work.PGroup.omega p 1 A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent X := IsPGroup.isNilpotent hX
  have hAab : IsMulCommutative A := hA.2.2.1
  have hAcent : Subgroup.centralizer (A : Set X) ≤ A := by simpa using hA.2.2.2
  have hAn : A.Normal := Subgroup.Normal.mk fun n hn g =>
    (Subgroup.normal_subgroupOf_iff le_top).mp hA.2.1 n g hn (Subgroup.mem_top g)
  have hAp : IsPGroup p A := hX.of_injective A.subtype Subtype.val_injective
  have hcentA_eq : Subgroup.centralizer (A : Set X) = A := by
    refine le_antisymm hAcent ?_
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (isMulCommutative_iff_of_setLike.mp hAab) b hb a ha
  set A0 : Subgroup X := Work.PGroup.omega p 1 A with hA0def
  set C : Subgroup X := Subgroup.centralizer (A0 : Set X) with hCdef
  set D : Subgroup X := Work.PGroup.omega p 1 C with hDdef
  have hA0leA : A0 ≤ A := by rw [hA0def]; exact Work.PGroup.omega_le p 1 A
  have hA_le_centA : A ≤ Subgroup.centralizer (A : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (isMulCommutative_iff_of_setLike.mp hAab) b hb a ha
  have hcentA_le_C : Subgroup.centralizer (A : Set X) ≤ C := by
    rw [hCdef]; exact Subgroup.centralizer_le (fun x hx => hA0leA hx)
  have hA_le_C : A ≤ C := le_trans hA_le_centA hcentA_le_C
  have hA0n : A0.Normal := by rw [hA0def]; exact omega_normal_of_normal p 1 hAn
  have hCn : C.Normal := by rw [hCdef]; exact centralizer_normal_of_normal hA0n
  have hDn : D.Normal := by rw [hDdef]; exact omega_normal_of_normal p 1 hCn
  have h1 : A0 ≤ D := by rw [hDdef, hA0def]; exact Work.PGroup.omega_mono hA_le_C
  have hexpA0 : ∀ a ∈ A0, a ^ p = 1 := by
    intro a ha
    rw [hA0def, Work.PGroup.omega_one_eq_omega1 p A] at ha
    exact (Work.PGroup.omega1_mem_and_pow hAab ha).2
  have hA0elem : Work.PGroup.IsElementaryAbelian p A0 := by
    refine ⟨?_, fun x => Subtype.ext (by simpa using hexpA0 x.1 x.2)⟩
    rw [hA0def, Work.PGroup.omega_one_eq_omega1 p A]
    exact Work.PGroup.omega1_isMulCommutative hAab
  have hD_eq : D = A0 := by
    by_contra hne
    have hgen : D = Subgroup.closure {y : X | y ∈ D ∧ y ^ p = 1} := by
      apply le_antisymm
      · rw [hDdef, Work.PGroup.omega]
        apply Subgroup.closure_mono
        rintro y ⟨hyC, hyp⟩
        exact ⟨Work.PGroup.subset_omega hyC hyp, by simpa using hyp⟩
      · exact (Subgroup.closure_le D).mpr (fun y hy => hy.1)
    have hcentD : ∀ d ∈ D, ∀ a ∈ A0, a * d = d * a := by
      intro d hd a ha
      have hdC : d ∈ C := by rw [hDdef] at hd; exact Work.PGroup.omega_le p 1 C hd
      have hdC' : d ∈ Subgroup.centralizer (A0 : Set X) := by rwa [hCdef] at hdC
      exact Subgroup.mem_centralizer_iff.mp hdC' a ha
    have hAD : ⁅A, D⁆ ≤ A0 := by
      rw [hDdef, Work.PGroup.omega, Subgroup.commutator_le]
      intro a ha d hd
      have key : ∀ y ∈ ({y : X | y ∈ C ∧ y ^ p ^ 1 = 1} : Set X), ⁅a, y⁆ ∈ A0 := by
        intro y hy
        exact (ft8_3_comm hp hpodd hAab hAp hAn (by simpa using hy.2) hy.1)
          (Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers y))
      induction hd using Subgroup.closure_induction with
      | mem y hy => exact key y hy
      | one => simp
      | mul y z hy hz ihy ihz =>
          rw [commutatorElement_mul_right_eq_mul_conj]
          have h := A0.mul_mem ihy (hA0n.conj_mem ⁅a, z⁆ ihz y)
          simpa only [mul_assoc] using h
      | inv y hy ihy =>
          rw [commutatorElement_inv_right, ← commutatorElement_inv]
          simpa using hA0n.conj_mem ⁅a, y⁆⁻¹ (A0.inv_mem ihy) y⁻¹
    have hA0_le_centD : A0 ≤ Subgroup.centralizer (D : Set X) := by
      rw [Subgroup.le_centralizer_iff, ← hCdef, hDdef]
      exact Work.PGroup.omega_le p 1 C
    have hcommA0D : ⁅A0, D⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hA0_le_centD
    have hDA_le : ⁅D, A⁆ ≤ A0 := by rw [Subgroup.commutator_comm]; exact hAD
    have h1r : ⁅⁅D, A⁆, D⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono hDA_le le_rfl).trans (le_of_eq hcommA0D))
    have h2r : ⁅⁅A, D⁆, D⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono hAD le_rfl).trans (le_of_eq hcommA0D))
    have hDD_A : ⁅⁅D, D⁆, A⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1r h2r
    have hD'leA : ⁅D, D⁆ ≤ A :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hDD_A).trans (le_of_eq hcentA_eq)
    have hgamma3 : ⁅⁅D, D⁆, D⁆ ≤ A0 :=
      (Subgroup.commutator_mono hD'leA le_rfl).trans hAD
    obtain ⟨N, hND, hNn, hA0N, hNne, hNexp⟩ :=
      ft8_3_normal_exp hp hpodd hX hexpA0 h1 hne hgen hgamma3 hcentD
    haveI : N.Normal := hNn
    obtain ⟨c, hcN, hcA0, hccent⟩ := ft8_3_fixed hp hX hA0N hNne hNexp
    have hcp : c ^ p = 1 := hNexp c hcN
    -- the normal elementary abelian extension E = ⟨A0, c⟩
    set E : Subgroup X := Subgroup.closure ((A0 : Set X) ∪ {c}) with hEdef
    have hA0E : A0 ≤ E := fun a ha => Subgroup.subset_closure (Set.mem_union_left _ ha)
    have hcE : c ∈ E := Subgroup.subset_closure (Set.mem_union_right _ rfl)
    have hEab : IsMulCommutative E := by
      rw [hEdef]
      apply Subgroup.isMulCommutative_closure
      rintro x hx y hy hxy
      have hxc : ∀ a ∈ A0, Commute c a := fun a ha => (hcentD c (hND hcN) a ha).symm
      rw [Set.mem_union, Set.mem_singleton_iff] at hx hy
      rcases hx with hxA0 | rfl
      · rcases hy with hyA0 | rfl
        · exact (isMulCommutative_iff_of_setLike.mp hAab) x (hA0leA hxA0) y (hA0leA hyA0)
        · exact (hxc x hxA0).symm
      · rcases hy with hyA0 | rfl
        · exact hxc y hyA0
        · exact absurd rfl hxy
    have hEexp : ∀ e ∈ E, e ^ p = 1 := by
      rw [hEdef]
      intro e he
      induction he using Subgroup.closure_induction with
      | mem x hx =>
          rw [Set.mem_union, Set.mem_singleton_iff] at hx
          rcases hx with hxA0 | rfl
          · exact hexpA0 x hxA0
          · exact hcp
      | one => simp
      | mul x y hx hy ihx ihy =>
          have hcomm : Commute x y :=
            isMulCommutative_iff_of_setLike.mp hEab x hx y hy
          rw [hcomm.mul_pow, ihx, ihy, one_mul]
      | inv x hx ihx => rw [inv_pow, ihx, inv_one]
    have hEelem : Work.PGroup.IsElementaryAbelian p E :=
      ⟨hEab, fun x => Subtype.ext (by simpa using hEexp x x.2)⟩
    have hEn : E.Normal := by
      rw [hEdef]
      have key : ∀ g : X, MulAut.conj g • Subgroup.closure ((A0 : Set X) ∪ {c}) ≤
          Subgroup.closure ((A0 : Set X) ∪ {c}) := by
        intro g
        rw [Subgroup.smul_closure]
        refine (Subgroup.closure_le _).mpr ?_
        rintro z hz
        rw [Set.mem_smul_set] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        rw [Set.mem_union, Set.mem_singleton_iff] at hw
        rcases hw with hwA0 | hwc
        · exact Subgroup.subset_closure (Set.mem_union_left _ (hA0n.conj_mem w hwA0 g))
        · rw [hwc]
          have h1 : ⁅c, g⁆ ∈ A0 := by
            have h := hccent g
            simpa [commutatorElement_def] using h
          have hg : ⁅c⁻¹, g⁆ ∈ A0 := by
            rw [commutatorElement_inv_left, ← commutatorElement_inv]
            simpa using hA0n.conj_mem ⁅c, g⁆⁻¹ (A0.inv_mem h1) c⁻¹
          have hgc : MulAut.conj g c = c * ⁅c⁻¹, g⁆ := by
            rw [MulAut.conj_apply, commutatorElement_def]; group
          change MulAut.conj g c ∈ Subgroup.closure ((A0 : Set X) ∪ {c})
          rw [hgc]
          exact Subgroup.mul_mem _
            (Subgroup.subset_closure (Set.mem_union_right _ rfl))
            (Subgroup.subset_closure (Set.mem_union_left _ hg))
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact key g (Set.mem_smul_set.mpr ⟨x, hx, rfl⟩)
      · intro hx
        have h1 : MulAut.conj g⁻¹ • (g * x * g⁻¹) ∈ Subgroup.closure ((A0 : Set X) ∪ {c}) :=
          key g⁻¹ (Set.mem_smul_set.mpr ⟨g * x * g⁻¹, hx, rfl⟩)
        have h2 : MulAut.conj g⁻¹ • (g * x * g⁻¹) = x := by
          show MulAut.conj g⁻¹ (g * x * g⁻¹) = x
          rw [MulAut.conj_apply]; group
        rwa [h2] at h1
    -- rank bookkeeping
    have hA0ltE : A0 < E := lt_of_le_of_ne hA0E (fun h => hcA0 (h ▸ hcE))
    have hrankA0 : Group.rank ↥A0 = Group.rank ↥A := by
      rw [hA0def]; exact rank_omega_eq_rank hp hAab hAp
    have hpoweqA0 : Nat.card ↥A0 = p ^ Group.rank ↥A0 := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA0elem.isPGroup
      rw [Work.PGroup.rank_eq_log_card_of_isElementaryAbelian hp A0 hA0elem, hn,
        Nat.log_pow hp.one_lt]
    have hpoweqE : Nat.card ↥E = p ^ Group.rank ↥E := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEelem.isPGroup
      rw [Work.PGroup.rank_eq_log_card_of_isElementaryAbelian hp E hEelem, hn, Nat.log_pow hp.one_lt]
    have hltcard : Nat.card ↥A0 < Nat.card ↥E := Subgroup.card_lt_of_lt hA0ltE
    have hranklt : Group.rank ↥A0 < Group.rank ↥E := by
      rw [hpoweqA0, hpoweqE] at hltcard
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hltcard
    -- maximal normal abelian B ⊇ E
    obtain ⟨B, hEB, hBn, hBab, hBmax⟩ := exists_maximal_normal_abelian_ge hEn hEab
    haveI : B.Normal := hBn
    have hBcent : Subgroup.centralizer (B : Set X) = B :=
      Work.PGroup.centralizer_eq_of_maximal_normal_abelian hBab
        (fun B' hB'n hB'ab hle => hBmax B' hB'n hB'ab hle)
    have hBscn : IsSCN (⊤ : Subgroup X) B :=
      ⟨le_top, hBn.subgroupOf ⊤, hBab, inf_le_left.trans hBcent.le⟩
    have hBrankle : Group.rank ↥B ≤ Group.rank ↥A := hmax B hBscn
    have hBp : IsPGroup p B := hX.of_injective B.subtype Subtype.val_injective
    have homega_elem : Work.PGroup.IsElementaryAbelian p (Work.PGroup.omega p 1 B) := by
      refine ⟨?_, ?_⟩
      · rw [Work.PGroup.omega_one_eq_omega1 p B]
        exact Work.PGroup.omega1_isMulCommutative hBab
      · intro x
        have hx : (x : X) ∈ Work.PGroup.omega1 X p B := by
          rw [← Work.PGroup.omega_one_eq_omega1 p B]; exact x.2
        exact Subtype.ext (by simpa using (Work.PGroup.omega1_mem_and_pow hBab hx).2)
    have hE_le_omega : E ≤ Work.PGroup.omega p 1 B := fun e he =>
      Work.PGroup.subset_omega (hEB he) (by simpa using hEexp e he)
    have hrankE_le_B : Group.rank ↥E ≤ Group.rank ↥B := by
      rw [← rank_omega_eq_rank hp hBab hBp]
      rw [Work.PGroup.rank_eq_log_card_of_isElementaryAbelian hp E hEelem,
        Work.PGroup.rank_eq_log_card_of_isElementaryAbelian hp _ homega_elem]
      exact Nat.log_mono_right (Subgroup.card_le_of_le hE_le_omega)
    omega
  exact hD_eq
