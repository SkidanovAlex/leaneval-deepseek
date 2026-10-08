import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Symplectic.Basic
import Submission.Work.PGroup.Symplectic.exists_centralizer_agemo_generator
import Submission.Work.PGroup.Symplectic.commutator_mem_zpowers_of_normal_form
import Submission.Work.PGroup.Symplectic.centralizes_of_pow_mem_zpowers
import Submission.Work.PGroup.Symplectic.extraspecial_of_exponent_p_sq
import Submission.Work.PGroup.Symplectic.zpowers_pow_eq_closure
import Submission.Work.PGroup.Symplectic.false_of_three_le_of_allAbelianCharCyclic
import Submission.Work.PGroup.center_eq_commutator_of_isExtraspecial
import Submission.Work.PGroup.exists_isCriticalSubgroup
import Submission.Work.PGroup.Symplectic.critical_subgroup_decomposition
import Submission.Work.PGroup.Symplectic.of_characteristic
-- import Submission.Work.PGroup.Symplectic.exists_centralizer_agemo_generator
import Submission.Work.PGroup.Symplectic.exists_pow_eq_one_add_mul_p
import Submission.Work.PGroup.Symplectic.pow_eq_of_conj_eq
import Submission.Work.PGroup.Symplectic.prime_pow_dvd_pow_pred_one_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A `p`-group of symplectic type (odd `p`) has nilpotency class at most two

Let `X` be a finite `p`-group, `p` an odd prime, in which every abelian characteristic subgroup
is cyclic (`Work.PGroup.AllAbelianCharCyclic X`).  Then the derived subgroup of `X` is central:
`⁅X, X⁆ ≤ Z(X)`.  Consequently `X` itself is a critical subgroup of itself and Gorenstein's
Lemma 5.4.7 (formalised as `Work.PGroup.Symplectic.critical_subgroup_decomposition`) applies with
`C = ⊤`; this is the route by which the main theorem
`Work.PGroup.Symplectic.symplectic_main` is proved.

The proof follows Gorenstein, *Finite Groups*, §5.4 (Theorem 5.4.9), for odd `p`.  A critical
subgroup `C` of `X` is replaced by `E ⊔ R = X` with `E` extraspecial, `R = C_X(E)`, and
`H = Z(C) ≤ R` self-centralizing in `R`.  If `R` is abelian then `R = Z(X)` and `X = E·Z(X)`
has class two.  Otherwise `H = ⟨c⟩` is cyclic of order `p^n` with `n ≥ 2`, and one shows that
the centralizer `M = C_R(℧¹(H))` is generated modulo `H` by a single element `y` of order `p`
conjugating `c` to `c ^ (1 + m p ^ (n-1))`.  For `n ≥ 3` the subgroup `Z(Ω₁(C_X(℧¹(H))))`
contains `⟨c ^ p ^ (n-1)⟩ × ⟨y⟩`, so it is a noncyclicity-witnessing abelian characteristic
subgroup of `X`, a contradiction.  For `n = 2` one shows directly that `X' = ⟨c ^ p⟩` is the
order-`p` centre of `X`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section

namespace Work.PGroup.Symplectic

/-- If two subgroups of a group commute elementwise, then every element of their join is the
product of an element of the first and an element of the second. -/
theorem exists_mul_eq_of_mem_sup_of_commute {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let S : Subgroup G :=
    { carrier := {x : G | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      mul_mem' := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        exact ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', by
          calc (a * a') * (b * b') = a * (a' * (b * b')) := by rw [mul_assoc]
            _ = a * ((a' * b) * b') := by rw [mul_assoc]
            _ = a * ((b * a') * b') := by rw [h a' ha' b hb]
            _ = a * (b * (a' * b')) := by rw [mul_assoc]
            _ = (a * b) * (a' * b') := by rw [← mul_assoc]⟩
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, by
          rw [mul_inv_rev, h a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)]⟩ }
  have hA : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩
  have hB : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩
  exact (sup_le hA hB) hx

/-- Left multiplication by a central element does not change a commutator. -/
theorem commutatorElement_mul_center_left {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (a b : G) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have h1 : ⁅z, b⁆ = 1 := Commute.commutator_eq (Subgroup.mem_center_iff.mp hz b).symm
  rw [h1]
  group

/-- Right multiplication by a central element does not change a commutator. -/
theorem commutatorElement_mul_center_right {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (a b : G) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have h1 : ⁅a, z⁆ = 1 := Commute.commutator_eq (Subgroup.mem_center_iff.mp hz a)
  rw [h1]
  group

/-- In a group `G = A ⊔ B` with `A` and `B` commuting elementwise and with `⁅A,A⁆` and `⁅B,B⁆`
contained in a central subgroup `L`, the whole derived subgroup is contained in `L`. -/
theorem commutator_top_le_of_commutator_le {G : Type*} [Group G] {A B L : Subgroup G}
    (hsup : A ⊔ B = ⊤) (hAB : ⁅A, B⁆ = ⊥) (hA : ⁅A, A⁆ ≤ L) (hB : ⁅B, B⁆ ≤ L)
    (hL : L ≤ Subgroup.center G) : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ L := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have h : a ∈ Subgroup.centralizer (B : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB ha
    exact (Subgroup.mem_centralizer_iff.mp h b hb).symm
  refine Subgroup.commutator_le.mpr ?_
  intro x _ y _
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    exists_mul_eq_of_mem_sup_of_commute hcomm (hsup ▸ Subgroup.mem_top x)
  obtain ⟨c, hc, d, hd, rfl⟩ :=
    exists_mul_eq_of_mem_sup_of_commute hcomm (hsup ▸ Subgroup.mem_top y)
  have hbc : ⁅b, c⁆ = 1 := Commute.commutator_eq (hcomm c hc b hb).symm
  have had : ⁅a, d⁆ = 1 := Commute.commutator_eq (hcomm a ha d hd)
  have hbd : ⁅b, d⁆ ∈ L := (Subgroup.commutator_le.mp hB) b hb d hd
  have hac : ⁅a, c⁆ ∈ L := (Subgroup.commutator_le.mp hA) a ha c hc
  have hconj : (a * c) * ⁅b, d⁆ * (a * c)⁻¹ ∈ L := by
    have h2 : (a * c) * ⁅b, d⁆ * (a * c)⁻¹ = ⁅b, d⁆ := by
      rw [Subgroup.mem_center_iff.mp (hL hbd) (a * c)]
      group
    rw [h2]
    exact hbd
  have hexp : ⁅a * b, c * d⁆ = (a * c) * ⁅b, d⁆ * (a * c)⁻¹ * ⁅a, c⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_mul_right_eq_mul_conj, hbc, had]
    group
  rw [hexp]
  exact L.mul_mem hconj hac

/-- The centre of the top subgroup is the centre of the group. -/
theorem centerIn_top_eq_center {G : Type*} [Group G] :
    Work.PGroup.centerIn (⊤ : Subgroup G) = Subgroup.center G := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : (⟨g, trivial⟩ : ↥(⊤ : Subgroup G)) * a = a * ⟨g, trivial⟩ :=
      Subgroup.mem_center_iff.mp ha ⟨g, trivial⟩
    have h2 := congrArg (fun t : ↥(⊤ : Subgroup G) => (t : G)) h1
    simp only [Subgroup.coe_mul] at h2
    rw [← haz]
    exact h2
  · intro hx
    refine Subgroup.mem_map.mpr ⟨⟨x, trivial⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hx (g : G))


/-- `p`-th powers of elements of an extraspecial `p`-group are central. -/
theorem pow_mem_centerIn_of_isExtraspecial {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : Work.PGroup.IsExtraspecial p E) :
    ∀ e ∈ E, e ^ p ∈ Work.PGroup.centerIn E := by
  have hZ : Work.PGroup.centerIn E = ⁅E, E⁆ :=
    Work.PGroup.center_eq_commutator_of_isExtraspecial E hE
  have hZcard : Nat.card ↥(Work.PGroup.centerIn E) = p := hE.2.2
  intro e he
  refine Subgroup.mem_map.mpr ⟨⟨e ^ p, E.pow_mem he p⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro f
  apply Subtype.ext
  show (f : G) * e ^ p = e ^ p * (f : G)
  rw [← commutatorElement_eq_one_iff_mul_comm]
  have hcf : ⁅e, (f : G)⁆ ∈ Work.PGroup.centerIn E := by
    rw [hZ]
    exact Subgroup.commutator_mem_commutator he f.2
  have horder : orderOf ⁅e, (f : G)⁆ ∣ p := by
    have h := Subgroup.orderOf_dvd_natCard (Work.PGroup.centerIn E) hcf
    rwa [hZcard] at h
  have hpow : ⁅e, (f : G)⁆ ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp horder
  have hcomm : Commute e ⁅e, (f : G)⁆ := by
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hcf
    have h2 : (⟨e, he⟩ : ↥E) * z = z * ⟨e, he⟩ := Subgroup.mem_center_iff.mp hz ⟨e, he⟩
    have h3 : e * (z : G) = (z : G) * e := congrArg Subtype.val h2
    rw [← hzeq]
    exact h3
  have h1 : ⁅e ^ p, (f : G)⁆ = 1 := by
    rw [← hcomm.commutatorElement_pow_left p]
    exact hpow
  rw [← commutatorElement_inv, h1, inv_one]

/-- **A finite `p`-group of symplectic type (`p` odd) has nilpotency class at most two.**

If every abelian characteristic subgroup of the finite `p`-group `X` is cyclic, then the derived
subgroup of `X` is contained in its centre.  (Gorenstein, *Finite Groups*, §5.4, for odd `p`.) -/
theorem commutator_le_center_of_allAbelianCharCyclic {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2) (hX : IsPGroup p X) (hnab : ¬ IsMulCommutative X)
    (hdc : Work.PGroup.AllAbelianCharCyclic X) :
    ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ Subgroup.center X := by
  classical
  have hnt : Nontrivial X := by
    by_contra h
    haveI : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
    exact hnab (IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _)
  haveI : Nontrivial X := hnt
  obtain ⟨C, hCchar, hCne, hfr, hcomm, hsc⟩ :=
    Work.PGroup.exists_characteristic_critical_intrinsic (H := X) hp hX
  have hcrit : Work.PGroup.IsCriticalSubgroup p (⊤ : Subgroup X) C :=
    { le_self := le_top
      ne_bot := hCne
      characteristic := by
        intro g hg
        rw [Work.PGroup.conjBy_eq_map]
        exact Subgroup.characteristic_iff_map_eq.mp hCchar (MulAut.conj g)
      frattini_le_center := hfr
      commutator_le_center := hcomm
      self_centralizing := inf_le_right.trans hsc }
  have hdcC : Work.PGroup.AllAbelianCharCyclic ↥C := by
    intro A hA hAc
    exact of_characteristic hCchar hdc A hA hAc
  obtain ⟨E, R, hsup, hcommER, hinf, hEorb, hZleR, hcentR⟩ :=
    critical_subgroup_decomposition hp hodd hX C hcrit hdcC
  -- The centre of `X` is contained in `Z(C) = centerIn C ≤ R`.
  have hZleC : Subgroup.center X ≤ Work.PGroup.centerIn C := by
    intro z hz
    have hzC : z ∈ C := hcrit.self_centralizing (Subgroup.mem_inf.mpr ⟨trivial, by
      rw [Subgroup.mem_centralizer_iff]
      intro c _
      exact Subgroup.mem_center_iff.mp hz c⟩)
    refine Subgroup.mem_map.mpr ⟨⟨z, hzC⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz c)
  have hZleR' : Subgroup.center X ≤ R := hZleC.trans hZleR
  by_cases hRab : IsMulCommutative ↥R
  · -- Case 1: `R` is abelian, so `R = Z(X)` and `X = E · Z(X)` has class two.
    haveI : IsMulCommutative ↥R := hRab
    have hER : ∀ a ∈ E, ∀ b ∈ R, a * b = b * a := by
      intro a ha b hb
      have h : a ∈ Subgroup.centralizer (R : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommER ha
      exact (Subgroup.mem_centralizer_iff.mp h b hb).symm
    have hRleZ : R ≤ Subgroup.center X := by
      intro r hr
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨e, he, r', hr', rfl⟩ :=
        exists_mul_eq_of_mem_sup_of_commute hER (hsup ▸ Subgroup.mem_top x)
      calc (e * r') * r = e * (r' * r) := mul_assoc e r' r
        _ = e * (r * r') := by rw [setLike_mul_comm hr' hr]
        _ = (e * r) * r' := (mul_assoc e r r').symm
        _ = (r * e) * r' := by rw [hER e he r hr]
        _ = r * (e * r') := mul_assoc r e r'
    have hRZ : R = Subgroup.center X := le_antisymm hRleZ hZleR'
    have hEne : E ≠ ⊥ := by
      intro hbot
      refine hnab (IsMulCommutative.of_comm fun x y => ?_)
      have htop : (⊤ : Subgroup X) = R := by rw [← hsup, hbot, bot_sup_eq]
      have hx : x ∈ R := htop ▸ Subgroup.mem_top x
      have hy : y ∈ R := htop ▸ Subgroup.mem_top y
      exact congrArg (fun t : ↥R => (t : X)) (isMulCommutative_iff.mp hRab ⟨x, hx⟩ ⟨y, hy⟩)
    have hEex : Work.PGroup.IsExtraspecial p E := hEorb.resolve_left hEne
    have hEE : ⁅E, E⁆ ≤ Subgroup.center X := by
      rw [← Work.PGroup.center_eq_commutator_of_isExtraspecial E hEex]
      exact (le_of_eq hinf.symm).trans (inf_le_right.trans (le_of_eq hRZ))
    have hRR : ⁅R, R⁆ ≤ Subgroup.center X := by
      have h : ⁅R, R⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro r hr
        rw [Subgroup.mem_centralizer_iff]
        intro r' hr'
        exact (setLike_mul_comm hr hr').symm
      rw [h]
      exact bot_le
    exact commutator_top_le_of_commutator_le hsup hcommER hEE hRR le_rfl
  · -- Case 2: `R` is nonabelian.
    have hER : ∀ a ∈ E, ∀ b ∈ R, a * b = b * a := by
      intro a ha b hb
      have h : a ∈ Subgroup.centralizer (R : Set X) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommER ha
      exact (Subgroup.mem_centralizer_iff.mp h b hb).symm
    obtain ⟨c₀, hc₀⟩ := Work.PGroup.center_eq_zpowers_of_allAbelianCharCyclic hdcC
    set c : X := (c₀ : X) with hcdef
    have hH : Work.PGroup.centerIn C = Subgroup.zpowers c := by
      rw [Work.PGroup.centerIn, hc₀, MonoidHom.map_zpowers]
      rfl
    have hcH : c ∈ Work.PGroup.centerIn C := hH ▸ Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    have hcR : c ∈ R := hZleR hcH
    haveI : Fact p.Prime := ⟨hp⟩
    have hCpg : IsPGroup p ↥C := hX.to_subgroup C
    haveI hCnt : Nontrivial ↥C := by
      obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
      exact ⟨x, 1, hx⟩
    haveI hCnil : Group.IsNilpotent ↥C := hCpg.isNilpotent
    have hZne : Work.PGroup.centerIn C ≠ ⊥ := by
      have h1 : Subgroup.center ↥C ≠ ⊥ := by
        have h2 := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥C) (H := ⊤) (by simp)
        simpa using h2
      intro hbot
      have h3 : Subgroup.center ↥C ≤ (C.subtype).ker :=
        (Subgroup.map_eq_bot_iff _).mp (by
          show (Subgroup.center ↥C).map C.subtype = ⊥
          exact hbot)
      rw [Subgroup.ker_subtype] at h3
      exact h1 (le_bot_iff.mp h3)
    have hcne : c ≠ 1 := by
      intro h1
      exact hZne (by rw [hH, h1, Subgroup.zpowers_one_eq_bot])
    obtain ⟨n, hn0⟩ := IsPGroup.iff_orderOf.mp hCpg c₀
    have hn : orderOf c = p ^ n := by
      rw [hcdef, Subgroup.orderOf_coe]
      exact hn0
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exfalso
        rw [h, pow_zero] at hn
        exact hcne (orderOf_eq_one_iff.mp hn)
      · exact h
    have hHchar : (Work.PGroup.centerIn C).Characteristic := centerIn_characteristic hCchar
    have hHnormal : (Work.PGroup.centerIn C).Normal := by
      haveI := hHchar
      infer_instance
    have hnormal : ∀ r ∈ R, r⁻¹ * c * r ∈ Subgroup.zpowers c := by
      intro r hr
      have h1 : r⁻¹ * c * r ∈ Work.PGroup.centerIn C := by
        have h2 := Subgroup.Normal.conj_mem hHnormal c hcH r⁻¹
        simpa [mul_assoc] using h2
      rwa [hH] at h1
    have hCen : ∀ r ∈ R, r⁻¹ * c * r = c → r ∈ Subgroup.zpowers c := by
      intro r hr hconj
      have hcent : r ∈ Subgroup.centralizer ((Work.PGroup.centerIn C : Subgroup X) : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [hH] at hh
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
        have hkey : (MulAut.conj r⁻¹) c = c := by
          rw [MulAut.conj_apply]
          simpa using hconj
        have h3 : (MulAut.conj r⁻¹) (c ^ k) = c ^ k := by rw [map_zpow, hkey]
        have h4 : r⁻¹ * h * r = h := by
          rw [← hk]
          simpa [MulAut.conj_apply] using h3
        have h5 : h * r = r * h := by
          have h6 := congrArg (fun t => r * t) h4
          simpa [mul_assoc] using h6
        exact h5
      have hmem : r ∈ R ⊓ Subgroup.centralizer ((Work.PGroup.centerIn C : Subgroup X) : Set X) :=
        Subgroup.mem_inf.mpr ⟨hr, hcent⟩
      rw [hcentR, hH] at hmem
      exact hmem
    have hRpg : IsPGroup p ↥R := hX.to_subgroup R
    have hMpow : ∀ r ∈ R, ∃ m : ℕ, r⁻¹ * c * r = c ^ (1 + m * p) := by
      intro r hr
      refine exists_pow_eq_one_add_mul_p hp hn (hnormal r hr) ?_
      obtain ⟨k, hk⟩ := hRpg (⟨r, hr⟩ : ↥R)
      refine ⟨k, ?_⟩
      have hk1 : r ^ p ^ k = 1 := by
        have h := congrArg (fun t : ↥R => (t : X)) hk
        simpa using h
      rw [hk1]
      simp
    have hn2 : 2 ≤ n := by
      rcases lt_or_ge n 2 with h | h
      · exfalso
        have hn_eq : n = 1 := by omega
        have hc1 : c ^ p = 1 := by
          have h1 : orderOf c ∣ p := by rw [hn, hn_eq, pow_one]
          exact orderOf_dvd_iff_pow_eq_one.mp h1
        have hRleH : R ≤ Subgroup.zpowers c := by
          intro r hr
          obtain ⟨m', hm'⟩ := hMpow r hr
          apply hCen r hr
          rw [hm', pow_add, pow_one, mul_comm, pow_mul, hc1, one_pow, mul_one]
        apply hRab
        refine IsMulCommutative.of_comm fun x y => ?_
        obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hRleH x.2)
        obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hRleH y.2)
        apply Subtype.ext
        show (x : X) * (y : X) = (y : X) * (x : X)
        rw [← ha, ← hb, ← zpow_add, add_comm, zpow_add]
      · exact h
    have hnotle : ¬ (R ≤ Subgroup.zpowers c) := by
      intro hle
      apply hRab
      refine IsMulCommutative.of_comm fun x y => ?_
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hle x.2)
      obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hle y.2)
      apply Subtype.ext
      show (x : X) * (y : X) = (y : X) * (x : X)
      rw [← ha, ← hb, ← zpow_add, add_comm, zpow_add]
    have hne : ∃ r ∈ R, r ∉ Subgroup.zpowers c := Set.not_subset.mp hnotle
    obtain ⟨y, hyR, hynmem, hyp, hnorm, hmconj⟩ :=
      exists_centralizer_agemo_generator hp hodd R hRpg hcR hn2 hn hnormal hCen hne
    obtain ⟨m, hm⟩ := hmconj
    have hynw : y ∉ Subgroup.zpowers (c ^ p ^ (n - 1)) := by
      intro hmem
      apply hynmem
      exact (Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers_iff.mpr
        ⟨(p ^ (n - 1) : ℕ), zpow_natCast c (p ^ (n - 1))⟩)) hmem
    rcases eq_or_lt_of_le hn2 with h2 | h3
    · -- Case 2a: `n = 2`.
      have hc2 : orderOf c = p ^ 2 := by rw [hn, h2]
      have hcp1 : c ^ p ^ 2 = 1 := by
        rw [← hc2]
        exact pow_orderOf_eq_one c
      have hcpR : ∀ r ∈ R, r⁻¹ * c ^ p * r = c ^ p := by
        intro r hr
        obtain ⟨m', hm'⟩ := hMpow r hr
        have h1 : r⁻¹ * c ^ p * r = (r⁻¹ * c * r) ^ p := by
          have h1' : r⁻¹ * c * r = (MulAut.conj r⁻¹) c := by
            rw [MulAut.conj_apply]
            simp
          rw [h1']
          rw [← map_pow, MulAut.conj_apply]
          simp
        rw [h1, hm', ← pow_mul]
        rw [show (1 + m' * p) * p = p + m' * p ^ 2 by ring, pow_add]
        rw [show c ^ (m' * p ^ 2) = 1 by
          rw [show m' * p ^ 2 = p ^ 2 * m' by ring, pow_mul, hcp1, one_pow]]
        rw [mul_one]
      have hcpZ : Subgroup.zpowers (c ^ p) ≤ Subgroup.center X := by
        rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
        intro x
        obtain ⟨e, he, r, hr, rfl⟩ :=
          exists_mul_eq_of_mem_sup_of_commute hER (hsup ▸ Subgroup.mem_top x)
        have he1 : e * c ^ p = c ^ p * e := hER e he (c ^ p) (R.pow_mem hcR p)
        have hr1 : r * c ^ p = c ^ p * r := by
          have h := congrArg (fun t => r * t) (hcpR r hr)
          simpa [mul_assoc] using h.symm
        calc (e * r) * c ^ p = e * (r * c ^ p) := mul_assoc e r (c ^ p)
          _ = e * (c ^ p * r) := by rw [hr1]
          _ = (e * c ^ p) * r := (mul_assoc e (c ^ p) r).symm
          _ = (c ^ p * e) * r := by rw [he1]
          _ = c ^ p * (e * r) := mul_assoc (c ^ p) e r
      have hA : ⁅E, E⁆ ≤ Subgroup.center X := by
        rcases eq_or_ne E ⊥ with hbot | hneE
        · rw [hbot]
          have h0 : ⁅(⊥ : Subgroup X), (⊥ : Subgroup X)⁆ = ⊥ :=
            Subgroup.commutator_eq_bot_iff_le_centralizer.mpr bot_le
          rw [h0]
          exact bot_le
        · have hex : Work.PGroup.IsExtraspecial p E := hEorb.resolve_left hneE
          rw [← Work.PGroup.center_eq_commutator_of_isExtraspecial E hex]
          intro z hz
          obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
          rw [Subgroup.mem_center_iff]
          intro x
          obtain ⟨e, he, r, hr, rfl⟩ :=
            exists_mul_eq_of_mem_sup_of_commute hER (hsup ▸ Subgroup.mem_top x)
          have hze : e * (z' : X) = (z' : X) * e :=
            congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨e, he⟩)
          have hzr : r * (z' : X) = (z' : X) * r := by
            have h : (z' : X) ∈ Subgroup.centralizer (R : Set X) :=
              Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommER z'.2
            exact Subgroup.mem_centralizer_iff.mp h r hr
          calc (e * r) * (z' : X) = e * (r * (z' : X)) := mul_assoc e r (z' : X)
            _ = e * ((z' : X) * r) := by rw [hzr]
            _ = (e * (z' : X)) * r := (mul_assoc e (z' : X) r).symm
            _ = ((z' : X) * e) * r := by rw [hze]
            _ = (z' : X) * (e * r) := mul_assoc (z' : X) e r
      have hB : ⁅R, R⁆ ≤ Subgroup.center X := by
        refine (Subgroup.commutator_le.mpr ?_).trans hcpZ
        intro u hu u' hu'
        have huM : u⁻¹ * c ^ p * u = c ^ p := hcpR u hu
        have hu'M : u'⁻¹ * c ^ p * u' = c ^ p := hcpR u' hu'
        obtain ⟨i, j, rfl⟩ := hnorm u hu huM
        obtain ⟨i', j', rfl⟩ := hnorm u' hu' hu'M
        have hconj2 : y⁻¹ * c * y = c ^ (1 + m * p) := by
          rw [hm, ← h2]
          norm_num
        exact commutator_mem_zpowers_of_normal_form hp hodd hc2 hyp hconj2
          ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
      exact commutator_top_le_of_commutator_le hsup hcommER hA hB le_rfl
    · -- Case 2b: `3 ≤ n`.  Here `Z(Ω₁(C_X(℧¹(H))))` supplies a noncyclic abelian
      -- characteristic subgroup, contradicting the hypothesis `hdc`.
      exfalso
      have hn3 : 3 ≤ n := h3
      have hEp : ∀ e ∈ E, e ^ p ∈ Subgroup.zpowers (c ^ p ^ (n - 1)) := by
        intro e he
        rcases eq_or_ne E ⊥ with hbot | hneE
        · rw [hbot] at he
          rw [Subgroup.mem_bot] at he
          rw [he]
          simp
        · have hex : Work.PGroup.IsExtraspecial p E := hEorb.resolve_left hneE
          have hZEX : Work.PGroup.centerIn E ≤ Subgroup.center X := by
            intro z hz
            obtain ⟨z', hz', hzeq⟩ := Subgroup.mem_map.mp hz
            rw [← hzeq, Subgroup.mem_center_iff]
            intro x
            obtain ⟨f, hf, r, hr, rfl⟩ :=
              exists_mul_eq_of_mem_sup_of_commute hER (hsup ▸ Subgroup.mem_top x)
            have hzf : f * (z' : X) = (z' : X) * f :=
              congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨f, hf⟩)
            have hzr : r * (z' : X) = (z' : X) * r := by
              have h : (z' : X) ∈ Subgroup.centralizer (R : Set X) :=
                Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommER z'.2
              exact Subgroup.mem_centralizer_iff.mp h r hr
            calc (f * r) * (z' : X) = f * (r * (z' : X)) := mul_assoc f r (z' : X)
              _ = f * ((z' : X) * r) := by rw [hzr]
              _ = (f * (z' : X)) * r := (mul_assoc f (z' : X) r).symm
              _ = ((z' : X) * f) * r := by rw [hzf]
              _ = (z' : X) * (f * r) := mul_assoc (z' : X) f r
          have h2 : e ^ p ∈ Subgroup.zpowers c := by
            have h3 : e ^ p ∈ Work.PGroup.centerIn C :=
              hZleC (hZEX (pow_mem_centerIn_of_isExtraspecial hp hex e he))
            rwa [hH] at h3
          have h4 : (e ^ p) ^ p = 1 := by
            have h5 : orderOf (e ^ p) ∣ p := by
              have h := Subgroup.orderOf_dvd_natCard (Work.PGroup.centerIn E)
                (pow_mem_centerIn_of_isExtraspecial hp hex e he)
              rwa [hex.2.2] at h
            exact orderOf_dvd_iff_pow_eq_one.mp h5
          have h6 : Subgroup.zpowers (c ^ p ^ (n - 1)) =
              Subgroup.closure {x : X | x ∈ Subgroup.zpowers c ∧ x ^ p ^ 1 = 1} :=
            zpowers_pow_eq_closure (a := c) (p := p) (m := n) (i := 1) hp hn hn1
          rw [h6]
          exact Subgroup.subset_closure ⟨h2, by simpa using h4⟩
      exact false_of_three_le_of_allAbelianCharCyclic hp hodd hn3 hdc hsup hcommER
        (hH ▸ hHchar) hEp hcR hn hyR hyp hm hynw hnorm

end Work.PGroup.Symplectic
