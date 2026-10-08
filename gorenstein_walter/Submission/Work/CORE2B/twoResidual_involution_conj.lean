import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.Work.CORE2B.L27_aux
import Submission.Work.CORE2B.cyclic_index_two_center_mem
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral
import Submission.Work.FUS.Dihedral
import Submission.Work.AUTA7.GroupTheory.SylowInfNormal
import Submission.Work.Dihedral.Defs

/-!
# CORE2B — involutions of the `2`-residual are conjugate to the central involution

`Work.CORE2B.twoResidual_involution_conj`: if `M` is a finite group whose Sylow `2`-subgroup `P`
satisfies `P ≃* DihedralGroup n` with `n ≥ 4`, and if the fusion hypothesis `hfus` holds (every
group with dihedral Sylow `2`-subgroups and no normal subgroup of index two has one class of
involutions), then every involution `t ∈ O²(M)` is conjugate in `M` to any involution `z ∈ Z(P)`.

The proof is a strong induction on `Nat.card M`:

* if `M` has no normal subgroup of index `2`, apply `hfus` to `M` itself;
* otherwise descend to a normal subgroup `N ≤ M` of index two.  Both `t` and `z` lie in `N`
  (`t` because `O²(M) ≤ N`; `z` because `z` is a *square* of an element of `X` and every
  index-two subgroup contains all squares, `z` corresponding to `r (n/2) = (r (n/4))²`), and
  `P ⊓ N` is a Sylow `2`-subgroup of `N`.  It is non-cyclic (otherwise Burnside's normal
  `2`-complement theorem would make `O²(N) ∋ t` odd), hence dihedral, and the induction
  hypothesis applies to `N`.

The hypothesis `hfus` is stated for `X : Type`, i.e. for groups in the bottom universe, so the
argument is first given for such groups (`twoResidual_involution_conj_aux`) and then transported
to an arbitrary `M` along `Shrink.{0} M ≃* M`.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-! ## 1. The `2`-residual of a normal subgroup of index two -/

/-- Every element of odd order lies in a normal subgroup of index two, so `O²(G) ≤ N`. -/
private theorem twoResidual_le_of_index_two_aux {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    (hN : N.Normal) (hidx : N.index = 2) : Work.GW2.twoResidual G ≤ N := by
  haveI : N.Normal := hN
  rw [Work.GW2.twoResidual, Subgroup.closure_le]
  intro g hg
  have hgord : Odd (orderOf g) := hg
  have h1 : orderOf ((QuotientGroup.mk' N) g) ∣ 2 := by
    rw [← hidx, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h2 : orderOf ((QuotientGroup.mk' N) g) ∣ orderOf g := orderOf_map_dvd _ g
  have hodd : Odd (orderOf ((QuotientGroup.mk' N) g)) := Odd.of_dvd_nat hgord h2
  have hone : orderOf ((QuotientGroup.mk' N) g) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by norm_num)
  have hmem : g ∈ (QuotientGroup.mk' N).ker := by
    rw [MonoidHom.mem_ker]
    show ((QuotientGroup.mk' N) g : G ⧸ N) = 1
    exact orderOf_eq_one_iff.mp hone
  rwa [QuotientGroup.ker_mk'] at hmem

/-- Every square lies in a normal subgroup of index two. -/
private theorem sq_mem_of_index_two_aux {G : Type*} [Group G] [Finite G] {N : Subgroup G} (hN : N.Normal)
    (hidx : N.index = 2) (g : G) : g * g ∈ N := by
  haveI : N.Normal := hN
  have h1 : orderOf ((QuotientGroup.mk' N) g) ∣ 2 := by
    rw [← hidx, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h2 : ((QuotientGroup.mk' N) g) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
  have h3 : QuotientGroup.mk' N (g * g) = 1 := by rw [map_mul, ← pow_two]; exact h2
  exact (QuotientGroup.eq_one_iff (N := N) (g * g)).mp h3

/-- The `2`-residual is transported by a multiplicative equivalence. -/
private theorem twoResidual_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Work.GW2.twoResidual H = (Work.GW2.twoResidual G).map (e : G →* H) := by
  rw [Work.GW2.twoResidual, Work.GW2.twoResidual, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · intro hy
    exact ⟨e.symm y, by simpa [MulEquiv.orderOf_eq] using hy, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    simpa [MulEquiv.orderOf_eq] using hx

/-! ## 2. The central involution of a dihedral Sylow subgroup is a square -/

/-- Let `P` be a Sylow `2`-subgroup of `X` with `P ≃* DihedralGroup n`, `n ≥ 4`, and let `z ∈ Z(P)`
be an involution.  Then `z ∈ N` for every normal subgroup `N ≤ X` of index two.

Indeed `z` corresponds to `r (n/2)`, and since `n` is a power of `2` with `n ≥ 4` we have
`4 ∣ n`, so `r (n/2) = (r (n/4))²`: `z` is a square, and index-two subgroups contain all
squares. -/
private theorem central_involution_mem_of_index_two {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) (n : ℕ) (hn : 4 ≤ n) (hP : Nonempty ((P : Subgroup X) ≃* DihedralGroup n))
    {z : X} (hz2 : orderOf z = 2) (hzmem : z ∈ (P : Subgroup X))
    (hzc : ∀ y ∈ (P : Subgroup X), y * z = z * y)
    (N : Subgroup X) (hN : N.Normal) (hidx : N.index = 2) : z ∈ N := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ⟩ := hP
  have hcardP : Nat.card ↥(P : Subgroup X) = 2 * n := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  -- `n = 2 ^ j` with `j ≥ 2`, so `4 ∣ n`
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have h2n : 2 * n = 2 ^ k := by rw [← hcardP]; exact hk
  have hk2 : 2 ≤ k := by
    by_contra h
    push_neg at h
    interval_cases k
    · rw [pow_zero] at h2n; omega
    · rw [pow_one] at h2n; omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ'] at h2n
  have hnj : n = 2 ^ j := Nat.mul_left_cancel (by norm_num) h2n
  have hj2 : 2 ≤ j := by
    by_contra h
    push_neg at h
    interval_cases j
    · rw [pow_zero] at hnj; omega
    · rw [pow_one] at hnj; omega
  have hEven : Even n := by
    refine ⟨2 ^ (j - 1), ?_⟩
    rw [hnj, ← two_mul, ← pow_succ']
    congr 1
    omega
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn0⟩
  -- the additive identities in `ℕ` used below
  have hn4 : n / 4 = 2 ^ (j - 2) := by
    rw [hnj, show (4 : ℕ) = 2 ^ 2 from by norm_num]
    exact Nat.pow_div (by omega : 2 ≤ j) (by norm_num)
  have hn2 : n / 2 = 2 ^ (j - 1) := by
    rw [hnj, show (2 : ℕ) = 2 ^ 1 from by norm_num]
    exact Nat.pow_div (by omega : 1 ≤ j) (by norm_num)
  have hadd : n / 4 + n / 4 = n / 2 := by
    rw [hn4, hn2]
    rw [← two_mul, ← pow_succ']
    congr 1
    omega
  -- `z` is the central involution of `DihedralGroup n`
  have hPu : (φ ⟨z, hzmem⟩ : DihedralGroup n) ∈ Subgroup.center (DihedralGroup n) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := φ.surjective w
    have hy : y * ⟨z, hzmem⟩ = ⟨z, hzmem⟩ * y := by
      apply Subtype.ext
      exact hzc y y.2
    rw [← map_mul, ← map_mul, hy]
  have horder : orderOf (φ ⟨z, hzmem⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hz2
  have h2mul : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hEven)
  have hr2 : orderOf (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, DihedralGroup.r_mul_r]
      have h : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
        rw [← Nat.cast_add, show n / 2 + n / 2 = 2 * (n / 2) from by omega, h2mul,
          ZMod.natCast_self]
      rw [h, DihedralGroup.r_zero]
    · intro h1
      have h0 : ((n / 2 : ℕ) : ZMod n) = 0 :=
        DihedralGroup.r.inj (by rw [h1, DihedralGroup.r_zero])
      rw [ZMod.natCast_eq_zero_iff] at h0
      have hpos : 0 < n / 2 := by omega
      have hle := Nat.le_of_dvd hpos h0
      omega
  have hr2mem : (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ∈
      Subgroup.center (DihedralGroup n) := by
    rw [DihedralGroup.center_eq_closure_of_even_ne_two hEven (by omega : n ≠ 2)]
    exact Subgroup.mem_zpowers _
  have hz_eq : φ ⟨z, hzmem⟩ = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) :=
    center_involution_unique_dihedral hn hPu hr2mem horder hr2
  -- `z` is a square
  set w : ↥(P : Subgroup X) := φ.symm (DihedralGroup.r ((n / 4 : ℕ) : ZMod n)) with hw
  have hwsq : (w : X) * (w : X) = z := by
    have h1 : w * w = φ.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) := by
      apply φ.injective
      rw [map_mul]
      simp only [hw, MulEquiv.apply_symm_apply]
      rw [DihedralGroup.r_mul_r]
      congr 1
      rw [← Nat.cast_add, hadd]
    have h2 : φ.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) = ⟨z, hzmem⟩ := by
      rw [← hz_eq, MulEquiv.symm_apply_apply]
    have h3 : w * w = ⟨z, hzmem⟩ := h1.trans h2
    exact congrArg (fun y : ↥(P : Subgroup X) => (y : X)) h3
  have hsq : (w : X) * (w : X) ∈ N := sq_mem_of_index_two_aux hN hidx (w : X)
  rwa [hwsq] at hsq

/-! ## 3. The Sylow `2`-subgroup of a normal index-two subgroup is cyclic or dihedral -/

/-- If `P` is a Sylow `2`-subgroup with `P ≃* DihedralGroup n` (`n ≥ 2`) and `N ≤ X` has
index two, then `P ⊓ N`, viewed inside `N`, is cyclic or dihedral of order `≥ 4`. -/
private theorem sylow_inf_index_two_dichotomy {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) (n : ℕ) (hn : 2 ≤ n) (hP : Nonempty ((P : Subgroup X) ≃* DihedralGroup n))
    (N : Subgroup X) (_hidx : N.index = 2) :
    IsCyclic ↥(((P : Subgroup X) ⊓ N).subgroupOf N) ∨
      ∃ k : ℕ, 2 ≤ k ∧
        Nonempty (↥(((P : Subgroup X) ⊓ N).subgroupOf N) ≃* DihedralGroup k) := by
  have hQ2 : IsPGroup 2 ↥((P : Subgroup X) ⊓ N) := IsPGroup.to_le P.isPGroup' inf_le_left
  rcases Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral P n hn hP
    ((P : Subgroup X) ⊓ N) hQ2 with hcyc | ⟨m, hm2, ⟨e⟩⟩
  · exact Or.inl
      ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe (inf_le_right : _ ≤ N))).mpr hcyc)
  · exact Or.inr ⟨m, hm2,
      ⟨(Subgroup.subgroupOfEquivOfLe (inf_le_right : _ ≤ N)).trans e⟩⟩

/-! ## 4. The statement for groups in `Type 0` -/

/-- The statement of `twoResidual_involution_conj` for groups in the bottom universe, proved by
strong induction on the group order.  This is the shape in which the fusion hypothesis `hfus`
(which is only stated for `X : Type`) can be applied. -/
private theorem twoResidual_involution_conj_aux
    (hfus : ∀ (X : Type) [Group X] [Finite X] (P : Sylow 2 X) (k : ℕ), 2 ≤ k →
      Nonempty ((P : Subgroup X) ≃* DihedralGroup k) →
      (∀ N : Subgroup X, N.Normal → N.index ≠ 2) →
      (∀ x y : X, orderOf x = 2 → orderOf y = 2 → ∃ c : X, c * x * c⁻¹ = y)) :
    ∀ (N' : ℕ) (X : Type) [Group X] [Finite X], Nat.card X = N' →
      ∀ (P : Sylow 2 X) (k : ℕ), 2 ≤ k →
        Nonempty ((P : Subgroup X) ≃* DihedralGroup k) →
      ∀ t z : X, orderOf t = 2 → t ∈ Work.GW2.twoResidual X → orderOf z = 2 →
        z ∈ (P : Subgroup X) → (∀ y ∈ (P : Subgroup X), y * z = z * y) →
        ∃ c : X, c * t * c⁻¹ = z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro N₀
  refine Nat.strong_induction_on N₀ (fun N' ih => ?_)
  intro X _ _ hXN P k hk hP t z ht2 htO hz2 hzmem hzc
  by_cases hno : ∀ Nb : Subgroup X, Nb.Normal → Nb.index ≠ 2
  · exact hfus X P k hk hP hno t z ht2 hz2
  · push_neg at hno
    obtain ⟨Nb, hNbnorm, hNbidx⟩ := hno
    haveI : Nb.Normal := hNbnorm
    -- `t` lies in `Nb`, and `t ∈ O²(↥Nb)`
    have htNb : t ∈ Nb := twoResidual_le_of_index_two_aux Nb hNbnorm hNbidx htO
    have hresN : t ∈ (Work.GW2.twoResidual ↥Nb).map Nb.subtype :=
      twoResidual_le_map_of_index_two Nb hNbnorm hNbidx htO
    obtain ⟨tn, htn, htneq⟩ := Subgroup.mem_map.mp hresN
    have htn_eq : tn = ⟨t, htNb⟩ := Subtype.ext htneq
    have htON : (⟨t, htNb⟩ : ↥Nb) ∈ Work.GW2.twoResidual ↥Nb := htn_eq ▸ htn
    have ht2N : orderOf (⟨t, htNb⟩ : ↥Nb) = 2 := by
      rw [Subgroup.orderOf_mk]; exact ht2
    -- the Sylow `2`-subgroup of `↥Nb`
    let Q' : Subgroup ↥Nb := ((P : Subgroup X) ⊓ Nb).subgroupOf Nb
    have hQinf := Work.AUTA7.GroupTheory.SylowInfNormal P Nb hNbnorm
    have hQ'pg : IsPGroup 2 ↥Q' :=
      hQinf.1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : _ ≤ Nb)).symm
    have hQ'idx : ¬ 2 ∣ Q'.index := by
      have h : Q'.index = ((P : Subgroup X) ⊓ Nb).relIndex Nb := rfl
      rw [h]; exact hQinf.2
    let P' : Sylow 2 ↥Nb := hQ'pg.toSylow hQ'idx
    have hP'coe : (P' : Subgroup ↥Nb) = Q' := IsPGroup.toSylow_coe hQ'pg hQ'idx
    rcases sylow_inf_index_two_dichotomy P k hk hP Nb hNbidx with hcyc | ⟨m, hm2, ⟨eiso⟩⟩
    · -- `P'` cyclic: Burnside's theorem contradicts `t ∈ O²(↥Nb)`
      exfalso
      have hcyc' : IsCyclic ↥(P' : Subgroup ↥Nb) := by rw [hP'coe]; exact hcyc
      have hodd := twoResidual_odd_of_cyclic_sylow_two P' hcyc'
      have h2dvd : 2 ∣ Nat.card ↥(Work.GW2.twoResidual ↥Nb) := by
        have h := orderOf_dvd_natCard (⟨⟨t, htNb⟩, htON⟩ : ↥(Work.GW2.twoResidual ↥Nb))
        rwa [Subgroup.orderOf_mk, ht2N] at h
      exact absurd hodd (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h2dvd))
    · -- `P'` is dihedral; first show `z ∈ Nb`, then descend
      have hcardP : Nat.card ↥(P : Subgroup X) = 2 * k := by
        obtain ⟨eP⟩ := hP
        rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
      have hcardQ' : Nat.card ↥Q' = 2 * m := by
        rw [Nat.card_congr eiso.toEquiv, DihedralGroup.nat_card]
      have hcardQQ' : Nat.card ↥Q' = Nat.card ↥((P : Subgroup X) ⊓ Nb) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : _ ≤ Nb)).toEquiv
      have hzNb : z ∈ Nb := by
        by_cases hPN : (P : Subgroup X) ≤ Nb
        · exact hPN hzmem
        · -- `P ⊔ Nb = ⊤`, so `|P ⊓ Nb| = k`, and `|Q'| = 2 * m` forces `k = 2 * m ≥ 4`
          have hk4 : 4 ≤ k := by
            have hsup : (P : Subgroup X) ⊔ Nb = ⊤ := by
              have hlt : ¬ ((P : Subgroup X) ⊔ Nb ≤ Nb) :=
                fun h => hPN (le_trans le_sup_left h)
              have h1 : Nb.relIndex ((P : Subgroup X) ⊔ Nb) *
                  ((P : Subgroup X) ⊔ Nb).index = Nb.index :=
                Subgroup.relIndex_mul_index le_sup_right
              rw [hNbidx] at h1
              have hdiv : Nb.relIndex ((P : Subgroup X) ⊔ Nb) ∣ 2 := ⟨_, h1.symm⟩
              have hne1 : Nb.relIndex ((P : Subgroup X) ⊔ Nb) ≠ 1 :=
                fun h => hlt (Subgroup.relIndex_eq_one.mp h)
              have hrel : Nb.relIndex ((P : Subgroup X) ⊔ Nb) = 2 := by
                rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
                · exact absurd h hne1
                · exact h
              have hidx1 : ((P : Subgroup X) ⊔ Nb).index = 1 := by
                rw [hrel] at h1; omega
              exact Subgroup.index_eq_one.mp hidx1
            have hrel2 : ((P : Subgroup X) ⊓ Nb).relIndex (P : Subgroup X) = 2 := by
              rw [Subgroup.inf_relIndex_left,
                ← Subgroup.relIndex_sup_right (P : Subgroup X) Nb, hsup,
                Subgroup.relIndex_top_right]
              exact hNbidx
            have hcardQ : Nat.card ↥((P : Subgroup X) ⊓ Nb) = k := by
              have h := Subgroup.relIndex_mul_card ((P : Subgroup X) ⊓ Nb) (P : Subgroup X)
              rw [inf_of_le_left inf_le_left, hrel2, hcardP] at h
              omega
            have hkm : k = 2 * m := by
              rw [← hcardQ, ← hcardQQ', hcardQ']
            omega
          exact central_involution_mem_of_index_two P k hk4 hP hz2 hzmem hzc Nb hNbnorm hNbidx
      have hz2N : orderOf (⟨z, hzNb⟩ : ↥Nb) = 2 := by
        rw [Subgroup.orderOf_mk]; exact hz2
      have hzmemN : (⟨z, hzNb⟩ : ↥Nb) ∈ (P' : Subgroup ↥Nb) := by
        rw [hP'coe]
        exact Subgroup.mem_subgroupOf.mpr ⟨hzmem, hzNb⟩
      have hzcN : ∀ y ∈ (P' : Subgroup ↥Nb), y * ⟨z, hzNb⟩ = ⟨z, hzNb⟩ * y := by
        intro y hy
        apply Subtype.ext
        have hyP : (y : X) ∈ (P : Subgroup X) := by
          have h2 : y ∈ ((P : Subgroup X) ⊓ Nb).subgroupOf Nb := by rwa [hP'coe] at hy
          exact (Subgroup.mem_subgroupOf.mp h2).1
        exact hzc (y : X) hyP
      have hlt : Nat.card ↥Nb < N' := by
        have h := Subgroup.card_mul_index Nb
        rw [hNbidx] at h
        rw [← hXN]
        have hpos : 0 < Nat.card ↥Nb :=
          Nat.pos_of_ne_zero (Nat.card_ne_zero.mpr ⟨⟨1, Nb.one_mem⟩, inferInstance⟩)
        omega
      have hisoP' : Nonempty (↥P' ≃* DihedralGroup m) := by
        change Nonempty (↥(P' : Subgroup ↥Nb) ≃* DihedralGroup m)
        rw [hP'coe]
        exact ⟨eiso⟩
      obtain ⟨c, hc⟩ :=
        ih (Nat.card ↥Nb) hlt ↥Nb rfl P' m hm2 hisoP'
          ⟨t, htNb⟩ ⟨z, hzNb⟩ ht2N htON hz2N hzmemN hzcN
      refine ⟨(c : ↥Nb), ?_⟩
      have hc' := congrArg (fun y : ↥Nb => (y : X)) hc
      simpa using hc'

/-! ## 5. The main theorem, transported to an arbitrary universe -/

theorem twoResidual_involution_conj {M : Type*} [Group M] [Finite M]
    (hfus : ∀ (X : Type) [Group X] [Finite X] (P : Sylow 2 X) (k : ℕ), 2 ≤ k →
      Nonempty ((P : Subgroup X) ≃* DihedralGroup k) →
      (∀ N : Subgroup X, N.Normal → N.index ≠ 2) →
      (∀ x y : X, orderOf x = 2 → orderOf y = 2 → ∃ c : X, c * x * c⁻¹ = y))
    (P : Sylow 2 M) (n : ℕ) (hn : 4 ≤ n) (hP : Nonempty ((P : Subgroup M) ≃* DihedralGroup n))
    {t z : M} (ht2 : orderOf t = 2) (htO : t ∈ Work.GW2.twoResidual M)
    (hz2 : orderOf z = 2) (hzmem : z ∈ (P : Subgroup M))
    (hzc : ∀ y ∈ (P : Subgroup M), y * z = z * y) :
    ∃ c : M, c * t * c⁻¹ = z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ (X : Type) [Group X] [Finite X], ∀ (P : Sylow 2 X) (k : ℕ), 2 ≤ k →
        Nonempty ((P : Subgroup X) ≃* DihedralGroup k) →
      ∀ t z : X, orderOf t = 2 → t ∈ Work.GW2.twoResidual X → orderOf z = 2 →
        z ∈ (P : Subgroup X) → (∀ y ∈ (P : Subgroup X), y * z = z * y) →
        ∃ c : X, c * t * c⁻¹ = z :=
    fun X _ _ => twoResidual_involution_conj_aux hfus (Nat.card X) X rfl
  -- Reduce `M` to the bottom universe, where `hfus` applies.
  let φ : Shrink.{0} M ≃* M := Shrink.mulEquiv
  let P₀ : Sylow 2 (Shrink.{0} M) :=
    P.comapOfInjective (φ : Shrink.{0} M →* M) φ.injective
      (by rw [MonoidHom.range_eq_top.mpr φ.surjective]; exact le_top)
  have hP₀coe : (P₀ : Subgroup (Shrink.{0} M)) =
      (P : Subgroup M).map (φ.symm : M →* Shrink.{0} M) := by
    rw [Sylow.coe_comapOfInjective, Subgroup.comap_equiv_eq_map_symm]
  have hiso₀ : Nonempty ((P₀ : Subgroup (Shrink.{0} M)) ≃* DihedralGroup n) := by
    obtain ⟨eP⟩ := hP
    refine ⟨(MulEquiv.subgroupCongr hP₀coe).trans ?_⟩
    exact (Subgroup.equivMapOfInjective P (φ.symm : M →* Shrink.{0} M)
      φ.symm.injective).symm.trans eP
  have ht2₀ : orderOf (φ.symm t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht2
  have hz2₀ : orderOf (φ.symm z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz2
  have htO₀ : (φ.symm t) ∈ Work.GW2.twoResidual (Shrink.{0} M) := by
    have hres : (Work.GW2.twoResidual (Shrink.{0} M)).map (φ : Shrink.{0} M →* M)
        = Work.GW2.twoResidual M := (twoResidual_map_mulEquiv φ).symm
    have h : t ∈ (Work.GW2.twoResidual (Shrink.{0} M)).map (φ : Shrink.{0} M →* M) := by
      rw [hres]; exact htO
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp h
    have hxt : x = φ.symm t := by
      apply φ.injective
      simpa using hxeq
    rwa [hxt] at hx
  have hzmem₀ : (φ.symm z) ∈ (P₀ : Subgroup (Shrink.{0} M)) := by
    rw [hP₀coe, Subgroup.mem_map]
    exact ⟨z, hzmem, rfl⟩
  have hzc₀ : ∀ y ∈ (P₀ : Subgroup (Shrink.{0} M)),
      y * (φ.symm z) = (φ.symm z) * y := by
    intro y hy
    have hyP : (φ y) ∈ (P : Subgroup M) := by
      rw [hP₀coe, Subgroup.mem_map] at hy
      obtain ⟨w, hw, hweq⟩ := hy
      have hyw : y = φ.symm w := hweq.symm
      rw [hyw, MulEquiv.apply_symm_apply]
      exact hw
    have h := hzc (φ y) hyP
    apply φ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact h
  obtain ⟨c, hc⟩ := key (Shrink.{0} M) P₀ n (by omega) hiso₀ (φ.symm t) (φ.symm z)
    ht2₀ htO₀ hz2₀ hzmem₀ hzc₀
  refine ⟨φ c, ?_⟩
  have h := congrArg (⇑φ) hc
  simpa using h

end Work.CORE2B
