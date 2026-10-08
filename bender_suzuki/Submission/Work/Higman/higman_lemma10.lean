import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end
open scoped BigOperators
open MvPolynomial

namespace Work.Higman

lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a ^ 2 = a := ZMod.pow_card a
  have h2 : a * (a - 1) = 0 := by
    have hh : a ^ 2 - a = 0 := sub_eq_zero.mpr h
    calc a * (a - 1) = a ^ 2 - a := by ring
      _ = 0 := hh
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr (sub_eq_zero.mp h3)

/-- **Higman (1963), Lemma 10.**  Let `K` be a *finite* field of characteristic two and `L` a
proper extension of odd degree.  For every `r` and every `ε ∈ L` there is `α ≠ 0` in `L` with
`Tr_{L/K}(α ^ (1 + 2 ^ r) * ε) = 0`. -/
theorem higman_lemma10 {K L : Type} [Field K] [Field L] [Algebra K L] [CharP K 2]
    [Finite K] [Finite L] [FiniteDimensional K L] (hodd : Odd (Module.finrank K L))
    (hproper : 1 < Module.finrank K L) (r : ℕ) (ε : L) :
    ∃ α : L, α ≠ 0 ∧ Algebra.trace K L (α ^ (1 + 2 ^ r) * ε) = 0 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype L := Fintype.ofFinite L
  haveI hL2 : CharP L 2 := (Algebra.charP_iff K L 2).mp inferInstance
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  letI : Algebra (ZMod 2) L := ZMod.algebra L 2
  haveI : IsScalarTower (ZMod 2) K L := inferInstance
  haveI : FiniteDimensional (ZMod 2) K := inferInstance
  haveI : FiniteDimensional (ZMod 2) L := inferInstance
  haveI : Module.Free (ZMod 2) K := inferInstance
  haveI : Module.Free (ZMod 2) L := inferInstance
  have hDfac : Module.finrank (ZMod 2) K * Module.finrank K L = Module.finrank (ZMod 2) L :=
    Module.finrank_mul_finrank (ZMod 2) K L
  have hKpos : 0 < Module.finrank (ZMod 2) K := Module.finrank_pos
  have hn3 : 3 ≤ Module.finrank K L := by
    obtain ⟨t, ht⟩ := hodd; omega
  have hDgt : 2 * Module.finrank (ZMod 2) K < Module.finrank (ZMod 2) L := by
    rw [← hDfac]; nlinarith [hKpos, hn3]
  let m : ℕ := Module.finrank (ZMod 2) K
  let D : ℕ := Module.finrank (ZMod 2) L
  have hmD : m = Module.finrank (ZMod 2) K := rfl
  have hDD : D = Module.finrank (ZMod 2) L := rfl
  have hDgt' : 2 * m < D := hDgt
  let bK : Module.Basis (Fin m) (ZMod 2) K := Module.finBasis (ZMod 2) K
  let bL : Module.Basis (Fin D) (ZMod 2) L := Module.finBasis (ZMod 2) L
  let P : Fin D → Fin D → K := fun i j => Algebra.trace K L ((bL i * (bL j) ^ (2^r)) * ε)
  let f : Fin m → MvPolynomial (Fin D) (ZMod 2) :=
    fun l => ∑ i, ∑ j, MvPolynomial.C (bK.coord l (P i j)) * MvPolynomial.X i * MvPolynomial.X j
  -- degree bound on f
  have hterm : ∀ (a : ZMod 2) (i j : Fin D),
      (MvPolynomial.C a * MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin D) (ZMod 2)).totalDegree ≤ 2 := by
    intro a i j
    calc (MvPolynomial.C a * MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin D) (ZMod 2)).totalDegree
        ≤ (MvPolynomial.C a * MvPolynomial.X i).totalDegree + (MvPolynomial.X j).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ ((MvPolynomial.C a).totalDegree + (MvPolynomial.X i).totalDegree) + (MvPolynomial.X j).totalDegree := by
          gcongr; exact MvPolynomial.totalDegree_mul _ _
      _ = 2 := by rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]; norm_num
  have hdegterm : ∀ l, (f l).totalDegree ≤ 2 := by
    intro l
    simp only [f]
    refine MvPolynomial.totalDegree_finsetSum_le (fun i _ => ?_)
    refine MvPolynomial.totalDegree_finsetSum_le (fun j _ => ?_)
    exact hterm _ i j
  -- product polynomial F
  let F : MvPolynomial (Fin D) (ZMod 2) := ∏ l, (1 + f l)
  have hFdeg : F.totalDegree < (Fintype.card (ZMod 2) - 1) * Fintype.card (Fin D) := by
    rw [ZMod.card]
    simp only [Nat.reduceSub]
    rw [one_mul, Fintype.card_fin]
    calc F.totalDegree ≤ ∑ l, (1 + f l).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ l : Fin m, (f l).totalDegree := by
          refine Finset.sum_le_sum (fun l _ => ?_)
          calc (1 + f l).totalDegree ≤ max (1 : MvPolynomial (Fin D) (ZMod 2)).totalDegree (f l).totalDegree :=
                MvPolynomial.totalDegree_add _ _
            _ ≤ (f l).totalDegree := by simp
      _ ≤ ∑ _l : Fin m, 2 := Finset.sum_le_sum (fun l _ => hdegterm l)
      _ = 2 * m := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
      _ < D := hDgt'
  have hsum : ∑ x : Fin D → ZMod 2, MvPolynomial.eval x F = 0 :=
    MvPolynomial.sum_eval_eq_zero F hFdeg
  have hFexpand : ∀ x : Fin D → ZMod 2,
      MvPolynomial.eval x F = ∏ l, (1 + MvPolynomial.eval x (f l)) := by
    intro x
    simp only [F]
    rw [map_prod]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    rw [map_add, map_one]
  -- solution set
  let Sol : Finset (Fin D → ZMod 2) :=
    Finset.univ.filter (fun x => ∀ l, MvPolynomial.eval x (f l) = 0)
  have hpoint : ∀ x : Fin D → ZMod 2,
      (if (∀ l, MvPolynomial.eval x (f l) = 0) then (1 : ZMod 2) else 0) = MvPolynomial.eval x F := by
    intro x
    rw [hFexpand x]
    by_cases hx : ∀ l, MvPolynomial.eval x (f l) = 0
    · rw [if_pos hx]
      refine (Finset.prod_eq_one (fun l _ => ?_)).symm
      rw [hx l]; ring
    · rw [if_neg hx]
      obtain ⟨l, hl⟩ : ∃ l, MvPolynomial.eval x (f l) ≠ 0 := by
        simpa only [not_forall] using hx
      refine (Finset.prod_eq_zero (Finset.mem_univ l) ?_).symm
      have h1 : MvPolynomial.eval x (f l) = 1 := by
        rcases zmod2_eq_zero_or_one (MvPolynomial.eval x (f l)) with h | h
        · exact absurd h hl
        · exact h
      rw [h1]; decide
  have hcard : ((Sol.card : ℕ) : ZMod 2) = 0 := by
    have h1 : ((Sol.card : ℕ) : ZMod 2)
        = ∑ x : Fin D → ZMod 2,
            (if (∀ l, MvPolynomial.eval x (f l) = 0) then (1 : ZMod 2) else 0) := by
      rw [show Sol = Finset.univ.filter (fun x => ∀ l, MvPolynomial.eval x (f l) = 0) from rfl]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast
      rfl
    rw [h1, show (∑ x : Fin D → ZMod 2,
            (if (∀ l, MvPolynomial.eval x (f l) = 0) then (1 : ZMod 2) else 0))
        = ∑ x : Fin D → ZMod 2, MvPolynomial.eval x F from
          Finset.sum_congr rfl (fun x _ => hpoint x)]
    exact hsum
  have h2dvd : 2 ∣ Sol.card := (CharP.cast_eq_zero_iff (ZMod 2) 2 Sol.card).mp hcard
  have hz0mem : (0 : Fin D → ZMod 2) ∈ Sol := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro l
    simp only [f]
    rw [map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [map_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    simp
  have hz0pos : 0 < Sol.card := Finset.card_pos.mpr ⟨0, hz0mem⟩
  have hSol2 : 2 ≤ Sol.card := Nat.le_of_dvd hz0pos h2dvd
  have hSol1 : 1 < Sol.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hSol1
  have hxexit : ∃ x ∈ Sol, x ≠ 0 := by
    by_cases ha0 : a = 0
    · exact ⟨b, hb, fun hb0 => hab (by rw [ha0, hb0])⟩
    · exact ⟨a, ha, ha0⟩
  obtain ⟨x, hxmem, hx0⟩ := hxexit
  have hxeval : ∀ l, MvPolynomial.eval x (f l) = 0 := (Finset.mem_filter.mp hxmem).2
  let α : L := ∑ i, x i • bL i
  have hαdef : α = ∑ i, x i • bL i := rfl
  have hαne : α ≠ 0 := by
    intro hα
    apply hx0
    have hαsym : α = bL.equivFun.symm x := by
      rw [hαdef, Module.Basis.equivFun_symm_apply]
    calc x = bL.equivFun (bL.equivFun.symm x) := (LinearEquiv.apply_symm_apply bL.equivFun x).symm
      _ = bL.equivFun α := by rw [hαsym]
      _ = bL.equivFun 0 := by rw [hα]
      _ = 0 := map_zero _
  -- main coordinate identity
  have hcoord : ∀ l, bK.coord l (Algebra.trace K L (α ^ (1 + 2 ^ r) * ε)) = MvPolynomial.eval x (f l) := by
    intro l
    have hα2 : α ^ (2^r) = ∑ i, x i • (bL i) ^ (2^r) := by
      rw [hαdef, sum_pow_char_pow (R := L) 2 r Finset.univ (fun i => x i • bL i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hx' : x i ^ (2^r) = x i := ZMod.pow_card_pow (n := r) (x i)
      rw [Algebra.smul_def, Algebra.smul_def, mul_pow]
      congr 1
      rw [← map_pow, hx']
    have hαk : α ^ (1+2^r) = ∑ i, ∑ j, (x i * x j) • (bL i * (bL j)^(2^r)) := by
      rw [pow_add, pow_one, hα2, hαdef]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Algebra.smul_def, map_mul]
      ring
    have htr : Algebra.trace K L (α^(1+2^r) * ε) = ∑ i, ∑ j, (x i * x j) • P i j := by
      rw [hαk]
      have e1 : (∑ i, ∑ j, (x i * x j) • (bL i * (bL j)^(2^r))) * ε
          = ∑ i, ∑ j, (x i * x j) • ((bL i * (bL j)^(2^r)) * ε) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Algebra.smul_mul_assoc]
      rw [e1]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [LinearMap.map_smul_of_tower]
    have hc : bK.coord l (∑ i, ∑ j, (x i * x j) • P i j)
        = ∑ i, ∑ j, (x i * x j) * (bK.coord l (P i j)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul, smul_eq_mul]
    have hev : MvPolynomial.eval x (f l) = ∑ i, ∑ j, (x i * x j) * (bK.coord l (P i j)) := by
      simp only [f]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      ring
    rw [htr, hc, hev]
  have hfinal : Algebra.trace K L (α ^ (1 + 2 ^ r) * ε) = 0 :=
    (Module.Basis.forall_coord_eq_zero_iff bK).mp (fun l => by rw [hcoord l, hxeval l])
  exact ⟨α, hαne, hfinal⟩

end Work.Higman
