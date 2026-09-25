import Mathlib
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_degree_zero_finrank

namespace Commons.Algebra.FreeAlgebra

open _root_.FreeAlgebra

set_option linter.unusedVariables false in
noncomputable def golodShafarevich_gradedProj (K ι : Type*) [Field K] (n : ℕ) :
    FreeAlgebra K ι →ₗ[K] FreeAlgebra K ι :=
  (Finsupp.lsum K (fun w : FreeMonoid ι =>
    if (FreeMonoid.toList w).length = n then
      LinearMap.id.smulRight (FreeAlgebra.basisFreeMonoid K ι w)
    else 0)) ∘ₗ (FreeAlgebra.basisFreeMonoid K ι).repr.toLinearMap

lemma golodShafarevich_gradedProj_apply_basis (K ι : Type*) [Field K] (n : ℕ)
    (w : FreeMonoid ι) :
    golodShafarevich_gradedProj K ι n (FreeAlgebra.basisFreeMonoid K ι w) =
      if (FreeMonoid.toList w).length = n then FreeAlgebra.basisFreeMonoid K ι w else 0 := by
  unfold golodShafarevich_gradedProj
  simp [LinearMap.comp_apply, Module.Basis.repr_self, Finsupp.lsum_single]
  by_cases h : (FreeMonoid.toList w).length = n
  · simp [h]
  · simp [h]

lemma golodShafarevich_gradedProj_mem (K ι : Type*) [Field K] (n : ℕ)
    (x : FreeAlgebra K ι) :
    golodShafarevich_gradedProj K ι n x ∈ golodShafarevich_gradedPart K ι n := by
  unfold golodShafarevich_gradedProj golodShafarevich_gradedPart
  rw [LinearMap.comp_apply, Finsupp.lsum_apply]
  refine Submodule.sum_mem _ ?_
  intro w hw
  by_cases h : (FreeMonoid.toList w).length = n
  · simp [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, h, rfl⟩)
  · simp [h]

lemma golodShafarevich_gradedProj_eq_self_of_mem_gradedPart
    (K ι : Type*) [Field K] (n : ℕ) {x : FreeAlgebra K ι}
    (hx : x ∈ golodShafarevich_gradedPart K ι n) :
    golodShafarevich_gradedProj K ι n x = x := by
  refine Submodule.span_induction (p := fun y (_ : y ∈ golodShafarevich_gradedPart K ι n) =>
    golodShafarevich_gradedProj K ι n y = y) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨w, hlen, rfl⟩
    simp [golodShafarevich_gradedProj_apply_basis, hlen]
  · simp
  · intro y z hy hz ihy ihz
    rw [map_add, ihy, ihz]
  · intro a y hy ihy
    rw [map_smul, ihy]

lemma golodShafarevich_gradedProj_eq_ite_of_mem_gradedPart
    (K ι : Type*) [Field K] (d n : ℕ) {x : FreeAlgebra K ι}
    (hx : x ∈ golodShafarevich_gradedPart K ι d) :
    golodShafarevich_gradedProj K ι n x = if n = d then x else 0 := by
  refine Submodule.span_induction (p := fun y (_ : y ∈ golodShafarevich_gradedPart K ι d) =>
    golodShafarevich_gradedProj K ι n y = if n = d then y else 0) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨w, hlen, rfl⟩
    rw [golodShafarevich_gradedProj_apply_basis]
    by_cases hnd : n = d
    · simp [hnd, hlen]
    · have hfalse : (FreeMonoid.toList w).length = n ↔ False := by
        constructor
        · intro hw; exact hnd (hw.symm.trans hlen)
        · intro f; cases f
      simp [hfalse, hnd]
  · simp
  · intro y z hy hz ihy ihz
    by_cases hnd : n = d
    · subst d
      simp [map_add, ihy, ihz]
    · simp [hnd, map_add, ihy, ihz]
  · intro a y hy ihy
    by_cases hnd : n = d
    · subst d
      simp [map_smul, ihy]
    · simp [hnd, map_smul, ihy]

lemma golodShafarevich_gradedPart_mul_mem {K ι : Type*} [Field K] {d e : ℕ}
    {a b : FreeAlgebra K ι}
    (ha : a ∈ golodShafarevich_gradedPart K ι d)
    (hb : b ∈ golodShafarevich_gradedPart K ι e) :
    a * b ∈ golodShafarevich_gradedPart K ι (d + e) := by
  refine Submodule.span_induction
    (p := fun a (_ : a ∈ golodShafarevich_gradedPart K ι d) =>
      ∀ b, b ∈ golodShafarevich_gradedPart K ι e →
        a * b ∈ golodShafarevich_gradedPart K ι (d + e)) ?_ ?_ ?_ ?_ ha b hb
  · intro a ha b hb
    rcases ha with ⟨u, hulen, rfl⟩
    refine Submodule.span_induction
      (p := fun b (_ : b ∈ golodShafarevich_gradedPart K ι e) =>
        FreeAlgebra.basisFreeMonoid K ι u * b ∈ golodShafarevich_gradedPart K ι (d + e)) ?_ ?_ ?_ ?_ hb
    · intro b hb
      rcases hb with ⟨v, hvlen, rfl⟩
      rw [← golodShafarevich_basisFreeMonoid_mul]
      apply Submodule.subset_span
      refine ⟨u * v, ?_, rfl⟩
      rw [FreeMonoid.toList_mul, List.length_append, hulen, hvlen]
    · simp
    · intro b c hb hc ihb ihc
      rw [mul_add]
      exact Submodule.add_mem _ ihb ihc
    · intro c b hb ihb
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ ihb
  · intro b hb; simp
  · intro a c ha hc iha ihc b hb
    rw [add_mul]
    exact Submodule.add_mem _ (iha b hb) (ihc b hb)
  · intro c a ha iha b hb
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ _ (iha b hb)

lemma golodShafarevich_basisFreeMonoid_mem_gradedPart {K ι : Type*} [Field K]
    (w : FreeMonoid ι) :
    FreeAlgebra.basisFreeMonoid K ι w ∈ golodShafarevich_gradedPart K ι (FreeMonoid.length w) := by
  apply Submodule.subset_span
  refine ⟨w, rfl, rfl⟩

lemma golodShafarevich_freeMonoid_exists_mul_of_of_ne_one {ι : Type*}
    {w : FreeMonoid ι} (hw : w ≠ 1) :
    ∃ (u : FreeMonoid ι) (i : ι), w = u * FreeMonoid.of i := by
  have hlist : FreeMonoid.toList w ≠ [] := by
    intro h
    apply hw
    exact FreeMonoid.toList.injective (by simpa [FreeMonoid.toList_one] using h)
  let l := FreeMonoid.toList w
  let i : ι := l.getLast hlist
  let u : FreeMonoid ι := FreeMonoid.ofList l.dropLast
  refine ⟨u, i, ?_⟩
  apply FreeMonoid.toList.injective
  simp [u, i, FreeMonoid.toList_mul, FreeMonoid.toList_of]
  exact (List.dropLast_concat_getLast hlist).symm

lemma golodShafarevich_gradedProj_twoSided_generator_mem
    {K ι σ : Type*} [Field K] [DecidableEq ι]
    (degRel : σ → ℕ) (rel : σ → FreeAlgebra K ι)
    (hhom : ∀ r, rel r ∈ golodShafarevich_gradedPart K ι (degRel r))
    (n : ℕ) (r : σ) (v w : FreeMonoid ι) :
    let V := golodShafarevich_gradedPart K ι
    let I := golodShafarevich_twoSidedIdeal K ι σ rel
    let T := Submodule.span K {x | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
    let S := Submodule.span K {x | ∃ (r : σ), degRel r ≤ n ∧ ∃ a ∈ V (n - degRel r),
      x = a * rel r}
    golodShafarevich_gradedProj K ι n (FreeAlgebra.basisFreeMonoid K ι v * rel r *
      FreeAlgebra.basisFreeMonoid K ι w) ∈ T ⊔ S := by
  dsimp only
  let V := golodShafarevich_gradedPart K ι
  let I := golodShafarevich_twoSidedIdeal K ι σ rel
  let T := Submodule.span K {x | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
  let S := Submodule.span K {x | ∃ (r : σ), degRel r ≤ n ∧ ∃ a ∈ V (n - degRel r),
      x = a * rel r}
  let P : FreeAlgebra K ι := FreeAlgebra.basisFreeMonoid K ι v * rel r *
    FreeAlgebra.basisFreeMonoid K ι w
  let d : ℕ := (FreeMonoid.length v + degRel r) + FreeMonoid.length w
  have hP_hom : P ∈ V d := by
    dsimp [P, d, V]
    have hvr : FreeAlgebra.basisFreeMonoid K ι v * rel r ∈
        golodShafarevich_gradedPart K ι (FreeMonoid.length v + degRel r) :=
      golodShafarevich_gradedPart_mul_mem
        (golodShafarevich_basisFreeMonoid_mem_gradedPart (K := K) (ι := ι) v) (hhom r)
    exact golodShafarevich_gradedPart_mul_mem hvr
      (golodShafarevich_basisFreeMonoid_mem_gradedPart (K := K) (ι := ι) w)
  have hproj : golodShafarevich_gradedProj K ι n P = if n = d then P else 0 :=
    golodShafarevich_gradedProj_eq_ite_of_mem_gradedPart K ι d n hP_hom
  by_cases hnd : n = d
  · have hprojP : golodShafarevich_gradedProj K ι n P = P := by
      rw [hproj]
      simp [hnd]
    rw [hprojP]
    by_cases hw1 : w = 1
    · have hS : P ∈ S := by
        have hlenw : FreeMonoid.length w = 0 := by simp [hw1]
        have hdeg : FreeMonoid.length v + degRel r = n := by
          have hd := hnd.symm
          dsimp [d] at hd
          simpa [hlenw] using hd
        have hle : degRel r ≤ n := by omega
        have hlenv : FreeMonoid.length v = n - degRel r := by omega
        have hv : FreeAlgebra.basisFreeMonoid K ι v ∈ V (n - degRel r) := by
          simpa [hlenv] using (golodShafarevich_basisFreeMonoid_mem_gradedPart (K := K) (ι := ι) v)
        dsimp [S, V]
        apply Submodule.subset_span
        refine ⟨r, hle, FreeAlgebra.basisFreeMonoid K ι v, hv, ?_⟩
        dsimp [P]
        rw [hw1, golodShafarevich_basisFreeMonoid_one, mul_one]
      exact Submodule.mem_sup_right (S := T) hS
    · rcases golodShafarevich_freeMonoid_exists_mul_of_of_ne_one hw1 with ⟨u, i, hwfac⟩
      let a : FreeAlgebra K ι := FreeAlgebra.basisFreeMonoid K ι v * rel r *
        FreeAlgebra.basisFreeMonoid K ι u
      have hPfac : P = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i) := by
        dsimp [P, a]
        rw [hwfac, golodShafarevich_basisFreeMonoid_mul]
        rw [← mul_assoc]
      have haI : a ∈ I := by
        dsimp [I, golodShafarevich_twoSidedIdeal]
        apply Submodule.subset_span
        refine ⟨r, v, u, rfl⟩
      have hlenw : FreeMonoid.length w = FreeMonoid.length u + 1 := by
        rw [hwfac, FreeMonoid.length_mul, FreeMonoid.length_of]
      have hdega : (FreeMonoid.length v + degRel r) + FreeMonoid.length u = n - 1 := by
        have hd := hnd.symm
        dsimp [d] at hd
        omega
      have haV : a ∈ V (n - 1) := by
        have ha_hom : a ∈ V ((FreeMonoid.length v + degRel r) + FreeMonoid.length u) := by
          dsimp [a, V]
          have hvr : FreeAlgebra.basisFreeMonoid K ι v * rel r ∈
              golodShafarevich_gradedPart K ι (FreeMonoid.length v + degRel r) :=
            golodShafarevich_gradedPart_mul_mem
              (golodShafarevich_basisFreeMonoid_mem_gradedPart (K := K) (ι := ι) v) (hhom r)
          exact golodShafarevich_gradedPart_mul_mem hvr
            (golodShafarevich_basisFreeMonoid_mem_gradedPart (K := K) (ι := ι) u)
        simpa [hdega] using ha_hom
      have haInt : a ∈ I ⊓ V (n - 1) := ⟨haI, haV⟩
      have hT : P ∈ T := by
        dsimp [T]
        apply Submodule.subset_span
        refine ⟨a, haInt, i, hPfac⟩
      exact Submodule.mem_sup_left (T := S) hT
  · have hproj0 : golodShafarevich_gradedProj K ι n P = 0 := by
      rw [hproj]
      simp [hnd]
    rw [hproj0]
    exact Submodule.zero_mem _

theorem golod_shafarevich_ideal_degree_le
    {K ι σ : Type*} [Field K] [DecidableEq ι]
    (degRel : σ → ℕ) (rel : σ → FreeAlgebra K ι)
    (hhom : ∀ r, rel r ∈ golodShafarevich_gradedPart K ι (degRel r))
    (n : ℕ) (hn : 0 < n) :
    let V := golodShafarevich_gradedPart K ι
    let I := golodShafarevich_twoSidedIdeal K ι σ rel
    let T := Submodule.span K {x | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
    let S := Submodule.span K {x | ∃ (r : σ), degRel r ≤ n ∧ ∃ a ∈ V (n - degRel r),
      x = a * rel r}
    I ⊓ V n ≤ T ⊔ S := by
  dsimp only
  have _hn : 0 < n := hn
  let V := golodShafarevich_gradedPart K ι
  let I := golodShafarevich_twoSidedIdeal K ι σ rel
  let T := Submodule.span K {x | ∃ a ∈ I ⊓ V (n - 1), ∃ i : ι,
      x = a * FreeAlgebra.basisFreeMonoid K ι (FreeMonoid.of i)}
  let S := Submodule.span K {x | ∃ (r : σ), degRel r ≤ n ∧ ∃ a ∈ V (n - degRel r),
      x = a * rel r}
  intro x hx
  have hxI : x ∈ I := hx.1
  have hxV : x ∈ V n := hx.2
  have hxproj : golodShafarevich_gradedProj K ι n x = x :=
    golodShafarevich_gradedProj_eq_self_of_mem_gradedPart K ι n hxV
  rw [← hxproj]
  refine Submodule.span_induction (p := fun y (_ : y ∈ I) =>
    golodShafarevich_gradedProj K ι n y ∈ T ⊔ S) ?_ ?_ ?_ ?_ hxI
  · intro y hy
    rcases hy with ⟨r, v, w, rfl⟩
    simpa [V, I, T, S] using
      (golodShafarevich_gradedProj_twoSided_generator_mem (K := K) (ι := ι) (σ := σ)
        degRel rel hhom n r v w)
  · simp
  · intro y z hy hz ihy ihz
    rw [map_add]
    exact Submodule.add_mem _ ihy ihz
  · intro a y hy ihy
    rw [map_smul]
    exact Submodule.smul_mem _ _ ihy

end Commons.Algebra.FreeAlgebra
