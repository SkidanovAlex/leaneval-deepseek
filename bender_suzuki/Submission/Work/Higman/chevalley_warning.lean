/-
Copyright (c) 2024. All rights reserved.

# Chevalley–Warning for anisotropic quadratic maps over `𝔽₂`

`card_le_sq_of_quadratic_anisotropic`: a quadratic map `Q : V → W` over `𝔽₂` with values in a
finite-dimensional `𝔽₂`-vector space `W`, with polar form `b` and `Q 0 = 0`, which is *anisotropic*
(`Q v = 0 → v = 0`), satisfies `|V| ≤ |W| ^ 2`.  This is the Chevalley–Warning theorem applied to
the `dim W` quadratic forms cutting out `Q = 0`; equivalently `finrank V ≤ 2 * finrank W`.

It is the tool that bounds the order of a class-`2` Suzuki 2-group by `q ^ 3`.
-/

import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

section ChevalleyWarning

open MvPolynomial

variable {V₀ W₀ : Type*} [AddCommGroup V₀] [Module (ZMod 2) V₀]
  [AddCommGroup W₀] [Module (ZMod 2) W₀]

/-- In a module over `ZMod 2` every element is its own negative. -/
private lemma add_self_eq_zero' (v : V₀) : v + v = 0 := by
  have h : ((1 : ZMod 2) + 1) = 0 := by decide
  calc v + v = (1 : ZMod 2) • v + (1 : ZMod 2) • v := by simp
    _ = ((1 : ZMod 2) + 1) • v := (add_smul 1 1 v).symm
    _ = (0 : ZMod 2) • v := by rw [h]
    _ = 0 := zero_smul (ZMod 2) v

variable {m n : ℕ}

/-- The `i`-th standard basis vector in `Fin m → ZMod 2`. -/
private def stdB (i : Fin m) : Fin m → ZMod 2 := Pi.single i 1

private lemma smul_stdB_apply (c : ZMod 2) (i j : Fin m) :
    (c • stdB i) j = if j = i then c else 0 := by
  by_cases h : j = i
  · subst h; simp [stdB]
  · simp [stdB, Pi.single_eq_of_ne (Ne.symm h), h]

private lemma sum_smul_stdB (x : Fin m → ZMod 2) : (∑ i, x i • stdB i) = x := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp [stdB]
  · intro b _ hb
    rw [smul_stdB_apply, if_neg (Ne.symm hb)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The polar form is alternating. -/
private lemma polar_diag (Q : (Fin m → ZMod 2) → (Fin n → ZMod 2)) (hQ0 : Q 0 = 0)
    (b : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hb : ∀ v w, Q (v + w) = Q v + Q w + b v w) (v : Fin m → ZMod 2) : b v v = 0 := by
  have h := hb v v
  rw [add_self_eq_zero', hQ0, add_self_eq_zero' (Q v), zero_add] at h
  exact h.symm

private lemma polar_comm (Q : (Fin m → ZMod 2) → (Fin n → ZMod 2)) (hQ0 : Q 0 = 0)
    (b : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hb : ∀ v w, Q (v + w) = Q v + Q w + b v w) (v w : Fin m → ZMod 2) : b v w = b w v := by
  have h5 : b v w + b w v = 0 := by
    have h := polar_diag Q hQ0 b hb (v + w)
    simp only [map_add, LinearMap.add_apply, polar_diag Q hQ0 b hb v,
      polar_diag Q hQ0 b hb w, zero_add, add_zero] at h
    simpa [add_comm] using h
  have hneg : - b w v = b w v := neg_eq_of_add_eq_zero_left (add_self_eq_zero' (b w v))
  have h6 : b v w = - b w v := eq_neg_of_add_eq_zero_left h5
  rw [hneg] at h6
  exact h6

/-- **Expansion of `Q` over a set of standard basis vectors.** -/
private lemma quad_expand_sum (Q : (Fin m → ZMod 2) → (Fin n → ZMod 2)) (hQ0 : Q 0 = 0)
    (b : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hb : ∀ v w, Q (v + w) = Q v + Q w + b v w) (S : Finset (Fin m)) :
    Q (∑ i ∈ S, stdB i) = (∑ i ∈ S, Q (stdB i))
      + ∑ p ∈ (S.product S).filter (fun p : Fin m × Fin m => p.1 < p.2),
          b (stdB p.1) (stdB p.2) := by
  refine Finset.induction_on_max S ?_ ?_
  · simpa using hQ0
  · intro a S hlt ih
    have ha : a ∉ S := fun hc => absurd (hlt a hc) (lt_irrefl a)
    have hpairs : ((insert a S).product (insert a S)).filter (fun p : Fin m × Fin m => p.1 < p.2)
        = (S.product S).filter (fun p : Fin m × Fin m => p.1 < p.2) ∪ S.image (fun i => (i, a)) := by
      ext p
      rcases p with ⟨p1, p2⟩
      constructor
      · intro hp
        obtain ⟨hmem, hplt⟩ := Finset.mem_filter.mp hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hmem
        have hma : p1 = a ∨ p1 ∈ S := Finset.mem_insert.mp hp1
        have hmb : p2 = a ∨ p2 ∈ S := Finset.mem_insert.mp hp2
        rcases hma with h1 | h1
        · rw [h1] at hplt
          rcases hmb with h2 | h2
          · rw [h2] at hplt
            exact absurd hplt (lt_irrefl a)
          · exact absurd hplt (not_lt_of_ge (le_of_lt (hlt p2 h2)))
        · rcases hmb with h2 | h2
          · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p1, h1, by rw [h2]⟩)
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
              ⟨Finset.mem_product.mpr ⟨h1, h2⟩, hplt⟩)
      · intro hp
        rcases Finset.mem_union.mp hp with hp | hp
        · obtain ⟨hmem, hplt⟩ := Finset.mem_filter.mp hp
          obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_insert.mpr (Or.inr h1), Finset.mem_insert.mpr (Or.inr h2)⟩, hplt⟩
        · obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp hp
          have h1 : p1 = i := (congrArg Prod.fst hie).symm
          have h2 : p2 = a := (congrArg Prod.snd hie).symm
          rw [h1, h2]
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_insert.mpr (Or.inr hi), Finset.mem_insert.mpr (Or.inl rfl)⟩, hlt i hi⟩
    have hdisj : Disjoint ((S.product S).filter (fun p : Fin m × Fin m => p.1 < p.2))
        (S.image (fun i => (i, a))) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hp1
      obtain ⟨-, hp1b⟩ := Finset.mem_product.mp hmem
      obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp hp2
      have h2 : p.2 = a := (congrArg Prod.snd hie).symm
      rw [h2] at hp1b
      exact ha hp1b
    have hinj : ∀ i ∈ S, ∀ j ∈ S, (i, a) = (j, a) → i = j := by
      intro i _ j _ h
      simpa using h
    have hsum : (∑ i ∈ insert a S, stdB i) = stdB a + ∑ i ∈ S, stdB i :=
      Finset.sum_insert ha
    rw [hsum, hb, ih, map_sum]
    rw [Finset.sum_insert ha, hpairs, Finset.sum_union hdisj, Finset.sum_image hinj]
    rw [Finset.sum_congr rfl (fun i _ => polar_comm Q hQ0 b hb (stdB a) (stdB i))]
    abel

/-- In `ZMod 2` every element is `0` or `1`. -/
private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

/-- The polynomial whose `k`-th component agrees with the `k`-th coordinate of `Q`. -/
private noncomputable def quadPoly (Q : (Fin m → ZMod 2) → (Fin n → ZMod 2))
    (b : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (k : Fin n) : MvPolynomial (Fin m) (ZMod 2) :=
  (∑ s : Fin m, MvPolynomial.C ((Q (stdB s)) k) * MvPolynomial.X s)
    + ∑ p ∈ ((Finset.univ : Finset (Fin m)).product Finset.univ).filter
        (fun p : Fin m × Fin m => p.1 < p.2),
        MvPolynomial.C ((b (stdB p.1) (stdB p.2)) k) * MvPolynomial.X p.1
          * MvPolynomial.X p.2

private lemma quadPoly_totalDegree (Q : (Fin m → ZMod 2) → (Fin n → ZMod 2))
    (b : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (k : Fin n) : (quadPoly Q b k).totalDegree ≤ 2 := by
  have hA : (∑ s : Fin m, MvPolynomial.C ((Q (stdB s)) k) * MvPolynomial.X s).totalDegree ≤ 2 :=
    MvPolynomial.totalDegree_finsetSum_le (fun s _ => by
      have h1 : (MvPolynomial.C ((Q (stdB s)) k) * MvPolynomial.X s).totalDegree ≤ 1 := by
        refine le_trans (MvPolynomial.totalDegree_mul _ _) (le_of_eq ?_)
        rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, Nat.zero_add]
      exact le_trans h1 (by decide))
  have hB : ((∑ p ∈ ((Finset.univ : Finset (Fin m)).product Finset.univ).filter
        (fun p : Fin m × Fin m => p.1 < p.2),
        MvPolynomial.C ((b (stdB p.1) (stdB p.2)) k) * MvPolynomial.X p.1
          * MvPolynomial.X p.2) : MvPolynomial (Fin m) (ZMod 2)).totalDegree ≤ 2 :=
    MvPolynomial.totalDegree_finsetSum_le (fun p _ => by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : ((MvPolynomial.C ((b (stdB p.1) (stdB p.2)) k)
          * MvPolynomial.X p.1) : MvPolynomial (Fin m) (ZMod 2)).totalDegree ≤ 1 := by
        refine le_trans (MvPolynomial.totalDegree_mul _ _) (le_of_eq ?_)
        rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, Nat.zero_add]
      have h2 : ((MvPolynomial.X p.2 : MvPolynomial (Fin m) (ZMod 2))).totalDegree ≤ 1 :=
        le_of_eq (MvPolynomial.totalDegree_X p.2)
      have h3 := add_le_add h1 h2
      exact le_trans h3 (by decide))
  rw [quadPoly]
  exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le hA hB)

private lemma quadPoly_eval (Q : (Fin m → ZMod 2) → (Fin n → ZMod 2)) (hQ0 : Q 0 = 0)
    (b : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hb : ∀ v w, Q (v + w) = Q v + Q w + b v w) (x : Fin m → ZMod 2) :
    (fun k : Fin n => MvPolynomial.eval x (quadPoly Q b k)) = Q x := by
  let S : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => x i ≠ 0)
  have hSmem : ∀ i : Fin m, i ∈ S ↔ x i ≠ 0 := by
    intro i
    show i ∈ Finset.univ.filter (fun i : Fin m => x i ≠ 0) ↔ x i ≠ 0
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩
  have hS0 : ∀ i : Fin m, i ∉ S → x i = 0 := by
    intro i hi
    by_contra h
    exact hi ((hSmem i).mpr h)
  have hS1 : ∀ i : Fin m, i ∈ S → x i = 1 := by
    intro i hi
    rcases zmod2_eq_zero_or_one (x i) with h | h
    · exact absurd h ((hSmem i).mp hi)
    · exact h
  have hx : x = ∑ i ∈ S, stdB i := by
    have h1 : (∑ i ∈ S, x i • stdB i) = ∑ i, x i • stdB i :=
      Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by rw [hS0 i hi, zero_smul])
    have h2 : (∑ i ∈ S, x i • stdB i) = ∑ i ∈ S, stdB i :=
      Finset.sum_congr rfl (fun i hi => by rw [hS1 i hi, one_smul])
    rw [← sum_smul_stdB x]
    exact h1.symm.trans h2
  have hsub : (S.product S).filter (fun p : Fin m × Fin m => p.1 < p.2) ⊆
      ((Finset.univ : Finset (Fin m)).product Finset.univ).filter
        (fun p : Fin m × Fin m => p.1 < p.2) := by
    intro p hp
    obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hlt⟩
  have hA : ∀ k : Fin n, MvPolynomial.eval x (quadPoly Q b k)
      = (∑ s : Fin m, ((Q (stdB s)) k) * (x s))
        + ∑ p ∈ ((Finset.univ : Finset (Fin m)).product Finset.univ).filter
            (fun p : Fin m × Fin m => p.1 < p.2),
            ((b (stdB p.1) (stdB p.2)) k) * (x p.1) * (x p.2) := by
    intro k
    rw [quadPoly, MvPolynomial.eval_add, MvPolynomial.eval_sum, MvPolynomial.eval_sum]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro s _
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    · refine Finset.sum_congr rfl ?_
      intro p _
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
        MvPolynomial.eval_X, MvPolynomial.eval_X]
  have hA1 : ∀ k : Fin n, (∑ i ∈ S, (Q (stdB i)) k)
      = ∑ s : Fin m, ((Q (stdB s)) k) * (x s) := by
    intro k
    have h1 : (∑ i ∈ S, (Q (stdB i)) k) = ∑ i ∈ S, ((Q (stdB i)) k) * (x i) :=
      Finset.sum_congr rfl (fun i hi => by rw [hS1 i hi, mul_one])
    have h2 : (∑ i ∈ S, ((Q (stdB i)) k) * (x i))
        = ∑ s : Fin m, ((Q (stdB s)) k) * (x s) :=
      Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by rw [hS0 i hi, mul_zero])
    exact h1.trans h2
  have hA2 : ∀ k : Fin n,
      (∑ p ∈ (S.product S).filter (fun p : Fin m × Fin m => p.1 < p.2),
          (b (stdB p.1) (stdB p.2)) k)
      = ∑ p ∈ ((Finset.univ : Finset (Fin m)).product Finset.univ).filter
          (fun p : Fin m × Fin m => p.1 < p.2),
          ((b (stdB p.1) (stdB p.2)) k) * (x p.1) * (x p.2) := by
    intro k
    have h1 : (∑ p ∈ (S.product S).filter (fun p : Fin m × Fin m => p.1 < p.2),
          (b (stdB p.1) (stdB p.2)) k)
        = ∑ p ∈ (S.product S).filter (fun p : Fin m × Fin m => p.1 < p.2),
            ((b (stdB p.1) (stdB p.2)) k) * (x p.1) * (x p.2) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
      rw [hS1 p.1 h1, hS1 p.2 h2, mul_one, mul_one]
    have h2 : (∑ p ∈ (S.product S).filter (fun p : Fin m × Fin m => p.1 < p.2),
            ((b (stdB p.1) (stdB p.2)) k) * (x p.1) * (x p.2))
        = ∑ p ∈ ((Finset.univ : Finset (Fin m)).product Finset.univ).filter
            (fun p : Fin m × Fin m => p.1 < p.2),
            ((b (stdB p.1) (stdB p.2)) k) * (x p.1) * (x p.2) := by
      refine Finset.sum_subset hsub ?_
      intro p hp hpn
      by_cases h1 : x p.1 = 0
      · simp [h1]
      · have h2 : x p.2 = 0 := by
          by_contra h2
          exact hpn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨(hSmem p.1).mpr h1, (hSmem p.2).mpr h2⟩, (Finset.mem_filter.mp hp).2⟩)
        simp [h2]
    exact h1.trans h2
  have hQx : Q x = (∑ i ∈ S, Q (stdB i))
      + ∑ p ∈ (S.product S).filter (fun p : Fin m × Fin m => p.1 < p.2),
          b (stdB p.1) (stdB p.2) := by
    rw [hx]
    exact quad_expand_sum Q hQ0 b hb S
  have hB : ∀ k : Fin n, (Q x) k = (∑ s : Fin m, ((Q (stdB s)) k) * (x s))
        + ∑ p ∈ ((Finset.univ : Finset (Fin m)).product Finset.univ).filter
            (fun p : Fin m × Fin m => p.1 < p.2),
            ((b (stdB p.1) (stdB p.2)) k) * (x p.1) * (x p.2) := by
    intro k
    rw [hQx, Pi.add_apply, Finset.sum_apply, Finset.sum_apply, hA1 k, hA2 k]
  funext k
  rw [hA k, ← hB k]

/-- **Chevalley–Warning for anisotropic quadratic maps over `𝔽₂`, coordinate form.** -/
private theorem chevalley_warning_quad (m n : ℕ)
    (Q : (Fin m → ZMod 2) → (Fin n → ZMod 2)) (hQ0 : Q 0 = 0)
    (b : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hb : ∀ v w, Q (v + w) = Q v + Q w + b v w) (haniso : ∀ v, Q v = 0 → v = 0) :
    m ≤ 2 * n := by
  by_contra hcon
  push_neg at hcon
  have hdeg : (∑ k : Fin n, (quadPoly Q b k).totalDegree) ≤ 2 * n := by
    calc (∑ k : Fin n, (quadPoly Q b k).totalDegree) ≤ ∑ _ : Fin n, 2 :=
          Finset.sum_le_sum (fun k _ => quadPoly_totalDegree Q b k)
      _ = 2 * n := by
          rw [Finset.sum_const, Finset.card_fin]
          simp [smul_eq_mul, mul_comm]
  have hlt : (∑ k : Fin n, (quadPoly Q b k).totalDegree) < Fintype.card (Fin m) := by
    rw [Fintype.card_fin]
    exact lt_of_le_of_lt hdeg hcon
  have hzero : ∀ x : Fin m → ZMod 2,
      (∀ k : Fin n, MvPolynomial.eval x (quadPoly Q b k) = 0) ↔ x = 0 := by
    intro x
    constructor
    · intro hx
      have hQ : Q x = 0 := by
        rw [← quadPoly_eval Q hQ0 b hb x]
        funext k
        simpa using hx k
      exact haniso x hQ
    · intro hx k
      rw [hx]
      have h := congrFun (quadPoly_eval Q hQ0 b hb 0) k
      rw [h, hQ0]
      rfl
  have hcard : Fintype.card {x : Fin m → ZMod 2 //
      ∀ i : Fin n, (MvPolynomial.eval x) (quadPoly Q b i) = 0} = 1 := by
    haveI : Subsingleton {x : Fin m → ZMod 2 //
        ∀ i : Fin n, (MvPolynomial.eval x) (quadPoly Q b i) = 0} :=
      ⟨fun a b => Subtype.ext (by rw [(hzero a.1).mp a.2, (hzero b.1).mp b.2])⟩
    have h1 : Fintype.card {x : Fin m → ZMod 2 //
        ∀ i : Fin n, (MvPolynomial.eval x) (quadPoly Q b i) = 0} ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr ‹Subsingleton _›
    have h2 : 0 < Fintype.card {x : Fin m → ZMod 2 //
        ∀ i : Fin n, (MvPolynomial.eval x) (quadPoly Q b i) = 0} :=
      Fintype.card_pos_iff.mpr ⟨⟨0, (hzero 0).mpr rfl⟩⟩
    omega
  have h2le : 2 ≤ Fintype.card {x : Fin m → ZMod 2 //
      ∀ i : Fin n, (MvPolynomial.eval x) (quadPoly Q b i) = 0} := by
    have hdvd' : 2 ∣ Fintype.card {x : Fin m → ZMod 2 //
        ∀ i : Fin n, (MvPolynomial.eval x) (quadPoly Q b i) = 0} := by
      have h := char_dvd_card_solutions_of_fintype_sum_lt (K := ZMod 2) (p := 2)
        (σ := Fin m) (ι := Fin n) (f := fun k => quadPoly Q b k) hlt
      simpa [Fintype.card_subtype, Finset.filter_congr_decidable] using h
    exact Nat.le_of_dvd (Fintype.card_pos_iff.mpr ⟨⟨0, (hzero 0).mpr rfl⟩⟩) hdvd'
  omega

/-- **Chevalley–Warning for anisotropic quadratic maps over `𝔽₂`.**  Let `V`, `W` be finite
`𝔽₂`-vector spaces, `Q : V → W` a quadratic map with polar form `b` and `Q 0 = 0`.  If `Q` is
anisotropic then `|V| ≤ |W| ^ 2`. -/
theorem card_le_sq_of_quadratic_anisotropic
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (Q : V → W) (hQ0 : Q 0 = 0) (b : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (hb : ∀ v w, Q (v + w) = Q v + Q w + b v w) (haniso : ∀ v, Q v = 0 → v = 0) :
    Nat.card V ≤ Nat.card W ^ 2 := by
  classical
  haveI : Module.Free (ZMod 2) V := Module.Free.of_divisionRing (ZMod 2) V
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  haveI : Module.Free (ZMod 2) W := Module.Free.of_divisionRing (ZMod 2) W
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  set e := (Module.finBasis (ZMod 2) V).equivFun with he
  set f := (Module.finBasis (ZMod 2) W).equivFun with hf
  set Q' : (Fin (Module.finrank (ZMod 2) V) → ZMod 2) →
      (Fin (Module.finrank (ZMod 2) W) → ZMod 2) := fun x => f (Q (e.symm x)) with hQ'
  set b' : (Fin (Module.finrank (ZMod 2) V) → ZMod 2) →ₗ[ZMod 2]
      (Fin (Module.finrank (ZMod 2) V) → ZMod 2) →ₗ[ZMod 2]
      (Fin (Module.finrank (ZMod 2) W) → ZMod 2) :=
    LinearMap.mk₂ (ZMod 2) (fun x y => f (b (e.symm x) (e.symm y)))
      (fun x x' y => by simp only [LinearMap.add_apply, map_add])
      (fun c x y => by simp only [LinearMap.smul_apply, map_smul])
      (fun x y y' => by simp only [LinearMap.add_apply, map_add])
      (fun c x y => by simp only [LinearMap.smul_apply, map_smul]) with hb'
  have key : Module.finrank (ZMod 2) V ≤ 2 * Module.finrank (ZMod 2) W := by
    refine chevalley_warning_quad _ _ Q' ?_ b' ?_ ?_
    · rw [hQ']
      simp [hQ0]
    · intro v w
      have h1 : b' v w = f (b (e.symm v) (e.symm w)) := by
        rw [hb']
        rfl
      rw [hQ', h1]
      simp only [map_add]
      rw [hb (e.symm v) (e.symm w)]
      simp only [map_add]
    · intro v hv
      have h1 : Q (e.symm v) = 0 := by
        have h2 : f.symm (Q' v) = f.symm 0 := by rw [hv]
        simpa [hQ'] using h2
      have h2 : e.symm v = 0 := haniso _ h1
      have h3 : e (e.symm v) = e 0 := by rw [h2]
      simpa using h3
  have hV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    calc Nat.card V = Nat.card (Fin (Module.finrank (ZMod 2) V) → ZMod 2) :=
          Nat.card_congr (Module.finBasis (ZMod 2) V).equivFun.toEquiv
      _ = Nat.card (ZMod 2) ^ Nat.card (Fin (Module.finrank (ZMod 2) V)) := Nat.card_fun
      _ = 2 ^ Module.finrank (ZMod 2) V := by
          have h2 : Nat.card (ZMod 2) = 2 := by
            rw [Nat.card_eq_fintype_card]; exact ZMod.card 2
          have h3 : Nat.card (Fin (Module.finrank (ZMod 2) V)) = Module.finrank (ZMod 2) V := by
            rw [Nat.card_eq_fintype_card, Fintype.card_fin]
          rw [h2, h3]
  have hW : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    calc Nat.card W = Nat.card (Fin (Module.finrank (ZMod 2) W) → ZMod 2) :=
          Nat.card_congr (Module.finBasis (ZMod 2) W).equivFun.toEquiv
      _ = Nat.card (ZMod 2) ^ Nat.card (Fin (Module.finrank (ZMod 2) W)) := Nat.card_fun
      _ = 2 ^ Module.finrank (ZMod 2) W := by
          have h2 : Nat.card (ZMod 2) = 2 := by
            rw [Nat.card_eq_fintype_card]; exact ZMod.card 2
          have h3 : Nat.card (Fin (Module.finrank (ZMod 2) W)) = Module.finrank (ZMod 2) W := by
            rw [Nat.card_eq_fintype_card, Fintype.card_fin]
          rw [h2, h3]
  rw [hV, hW]
  calc 2 ^ Module.finrank (ZMod 2) V ≤ 2 ^ (2 * Module.finrank (ZMod 2) W) :=
        Nat.pow_le_pow_right (by norm_num) key
    _ = (2 ^ Module.finrank (ZMod 2) W) ^ 2 := by
        rw [Nat.mul_comm 2 (Module.finrank (ZMod 2) W), ← pow_mul]

end ChevalleyWarning

end Work.Higman
