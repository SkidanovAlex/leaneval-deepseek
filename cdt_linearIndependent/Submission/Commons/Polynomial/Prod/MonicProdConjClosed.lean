import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial
open scoped BigOperators

namespace Commons.Polynomial.Prod

noncomputable section

private lemma minpoly_int_map_rat (x : ℂ) (hx : IsIntegral ℤ x) :
    (minpoly ℤ x).map (algebraMap ℤ ℂ) = (minpoly ℚ x).map (algebraMap ℚ ℂ) := by
  have e1 := minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (K := ℚ) (S := ℂ) (s := x) hx
  rw [e1, Polynomial.map_map]
  congr

private lemma conjClass_prod_eq_minpoly_int_map (S : Finset ℂ) (x : ℂ) (hx : IsIntegral ℤ x)
    (hcl : ∀ w : ℂ, aeval w (minpoly ℚ x) = 0 → w ∈ S) :
    (∏ y ∈ S.filter (fun y => aeval y (minpoly ℚ x) = 0), (X - C y)) =
      (minpoly ℤ x).map (algebraMap ℤ ℂ) := by
  classical
  let q := minpoly ℚ x
  let q' : ℂ[X] := q.map (algebraMap ℚ ℂ)
  have hQx : IsIntegral ℚ x := IsIntegral.tower_top (R := ℤ) (A := ℚ) hx
  have hqmonic : q'.Monic := by
    dsimp [q']
    exact (minpoly.monic hQx).map (algebraMap ℚ ℂ)
  have hqne : q ≠ 0 := minpoly.ne_zero hQx
  have hq'ne : q' ≠ 0 := by
    dsimp [q']
    exact Polynomial.map_ne_zero hqne
  have hsep : q.Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hQx)
  have hq'sep : q'.Separable := by
    dsimp [q']
    exact hsep.map (f := algebraMap ℚ ℂ)
  have hroots_nodup : q'.roots.Nodup := Polynomial.nodup_roots hq'sep
  have hcard : q'.roots.card = q'.natDegree := IsAlgClosed.card_roots_eq_natDegree (p := q')
  have hq'prod : (q'.roots.map fun a => X - C a).prod = q' :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hqmonic hcard
  have hF : S.filter (fun y => aeval y q = 0) = q'.roots.toFinset := by
    ext y
    dsimp [q']
    constructor
    · intro hy
      rw [Multiset.mem_toFinset]
      rw [Polynomial.mem_roots hq'ne]
      rw [Polynomial.IsRoot.def]
      rw [Polynomial.eval_map]
      rw [← Polynomial.aeval_def]
      exact (Finset.mem_filter.mp hy).2
    · intro hy
      rw [Finset.mem_filter]
      rw [Multiset.mem_toFinset] at hy
      rw [Polynomial.mem_roots hq'ne] at hy
      rw [Polynomial.IsRoot.def] at hy
      rw [Polynomial.eval_map] at hy
      rw [← Polynomial.aeval_def] at hy
      exact ⟨hcl y hy, hy⟩
  calc
    (∏ y ∈ S.filter (fun y => aeval y (minpoly ℚ x) = 0), (X - C y))
        = ∏ y ∈ S.filter (fun y => aeval y q = 0), (X - C y) := rfl
    _ = ∏ y ∈ q'.roots.toFinset, (X - C y) := by rw [hF]
    _ = (q'.roots.map fun a => X - C a).prod := by
          rw [Finset.prod_eq_multiset_prod]
          congr 1
          rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hroots_nodup]
    _ = q' := hq'prod
    _ = (minpoly ℤ x).map (algebraMap ℤ ℂ) := by
          rw [minpoly_int_map_rat x hx]


private lemma conjClosed_intPoly (S : Finset ℂ)
    (hintS : ∀ x ∈ S, IsIntegral ℤ x)
    (hclS : ∀ x ∈ S, ∀ w : ℂ, aeval w (minpoly ℚ x) = 0 → w ∈ S) :
    ∃ P : ℤ[X], (∏ x ∈ S, (X - C x)) = P.map (algebraMap ℤ ℂ) := by
  classical
  have H : ∀ (m : ℕ) (T : Finset ℂ), T.card = m →
      (∀ x ∈ T, IsIntegral ℤ x) → (∀ x ∈ T, ∀ w : ℂ, aeval w (minpoly ℚ x) = 0 → w ∈ T) →
      ∃ P : ℤ[X], (∏ x ∈ T, (X - C x)) = P.map (algebraMap ℤ ℂ) := by
    intro m
    exact Nat.strong_induction_on m (p := fun n => ∀ T : Finset ℂ, T.card = n →
      (∀ x ∈ T, IsIntegral ℤ x) → (∀ x ∈ T, ∀ w : ℂ, aeval w (minpoly ℚ x) = 0 → w ∈ T) →
      ∃ P : ℤ[X], (∏ x ∈ T, (X - C x)) = P.map (algebraMap ℤ ℂ)) (by
      intro n ih T hcard hTi hTc
      by_cases hTempty : T = ∅
      · subst T
        refine ⟨1, ?_⟩
        simp
      · rcases (Finset.nonempty_iff_ne_empty.mpr hTempty) with ⟨x, hxT⟩
        let p : ℂ → Prop := fun y => aeval y (minpoly ℚ x) = 0
        have hxC : x ∈ T.filter p := by
          dsimp [p]
          exact Finset.mem_filter.mpr ⟨hxT, minpoly.aeval ℚ x⟩
        have hT'card : (T.filter (fun y => ¬ p y)).card < T.card := by
          have hsub : T.filter (fun y => ¬ p y) ⊆ T := Finset.filter_subset _ _
          have hxnotin : x ∉ T.filter (fun y => ¬ p y) := by
            intro hx'
            have hnp : ¬ p x := (Finset.mem_filter.mp hx').2
            exact hnp (by dsimp [p]; exact minpoly.aeval ℚ x)
          have hssub : T.filter (fun y => ¬ p y) ⊂ T :=
            (Finset.ssubset_iff_of_subset hsub).2 ⟨x, hxT, hxnotin⟩
          exact Finset.card_lt_card hssub
        have hlt : (T.filter (fun y => ¬ p y)).card < n := by
          rw [← hcard]
          exact hT'card
        -- hypotheses for T' = T.filter (fun y => ¬ p y)
        have hTi' : ∀ y ∈ T.filter (fun y => ¬ p y), IsIntegral ℤ y := by
          intro y hy
          exact hTi y ((Finset.mem_filter.mp hy).1)
        have hTc' : ∀ y ∈ T.filter (fun y => ¬ p y), ∀ w : ℂ,
            aeval w (minpoly ℚ y) = 0 → w ∈ T.filter (fun y => ¬ p y) := by
          intro y hy w hw
          have hyT : y ∈ T := (Finset.mem_filter.mp hy).1
          have hynp : ¬ p y := (Finset.mem_filter.mp hy).2
          have hwT : w ∈ T := hTc y hyT w hw
          have hQx : IsIntegral ℚ x := IsIntegral.tower_top (R := ℤ) (A := ℚ) (hTi x hxT)
          have hQy : IsIntegral ℚ y := IsIntegral.tower_top (R := ℤ) (A := ℚ) (hTi y hyT)
          have hw_not_C : ¬ p w := by
            intro hwC
            have hwrootx : aeval w (minpoly ℚ x) = 0 := by
              dsimp [p] at hwC
              exact hwC
            have hmin_xw : minpoly ℚ x = minpoly ℚ w :=
              (minpoly.eq_iff_aeval_minpoly_eq_zero (h := hQx)).mpr hwrootx
            have hmin_yw : minpoly ℚ y = minpoly ℚ w :=
              (minpoly.eq_iff_aeval_minpoly_eq_zero (h := hQy)).mpr hw
            have hmin_xy : minpoly ℚ x = minpoly ℚ y := hmin_xw.trans hmin_yw.symm
            have hyrootx : aeval y (minpoly ℚ x) = 0 := by
              rw [hmin_xy]
              exact minpoly.aeval ℚ y
            exact hynp (by dsimp [p]; exact hyrootx)
          exact Finset.mem_filter.mpr ⟨hwT, hw_not_C⟩
        -- recursive call
        have hrec := ih (T.filter (fun y => ¬ p y)).card hlt (T.filter (fun y => ¬ p y)) rfl hTi' hTc'
        rcases hrec with ⟨P', hP'⟩
        -- product over the conjugacy class C of x
        have hprodC : (∏ y ∈ T.filter p, (X - C y)) =
            (minpoly ℤ x).map (algebraMap ℤ ℂ) := by
          change (∏ y ∈ T.filter (fun y => aeval y (minpoly ℚ x) = 0), (X - C y)) =
            (minpoly ℤ x).map (algebraMap ℤ ℂ)
          exact conjClass_prod_eq_minpoly_int_map T x (hTi x hxT) (hTc x hxT)
        -- combine
        refine ⟨minpoly ℤ x * P', ?_⟩
        rw [Polynomial.map_mul]
        -- goal: ∏ y ∈ T, (X - C y) = (minpoly ℤ x).map (algebraMap ℤ ℂ) * P'.map (algebraMap ℤ ℂ)
        calc
          (∏ y ∈ T, (X - C y))
              = (∏ y ∈ T.filter p, (X - C y)) * (∏ y ∈ T.filter (fun y => ¬ p y), (X - C y)) := by
                rw [Finset.prod_filter_mul_prod_filter_not T p (fun y => X - C y)]
          _ = (minpoly ℤ x).map (algebraMap ℤ ℂ) * P'.map (algebraMap ℤ ℂ) := by
                rw [hprodC, hP']
      )
  exact H S.card S rfl hintS hclS

lemma MonicProdConjClosed {n : ℕ} (b : Fin n → ℂ)
    (hb : ∀ k : Fin n, IsIntegral ℤ (b k))
    (hinj : Function.Injective b)
    (hclosed : ∀ k : Fin n, ∀ w : ℂ, aeval w (minpoly ℚ (b k)) = 0 → ∃ t : Fin n, b t = w) :
    ∃ P : ℤ[X], (∏ k : Fin n, (X - C (b k))) = P.map (algebraMap ℤ ℂ) := by
  classical
  let S : Finset ℂ := Finset.univ.image b
  have hintS : ∀ x ∈ S, IsIntegral ℤ x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    exact hb k
  have hclS : ∀ x ∈ S, ∀ w : ℂ, aeval w (minpoly ℚ x) = 0 → w ∈ S := by
    intro x hx w hw
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    rcases hclosed k w hw with ⟨t, ht⟩
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, ht⟩
  rcases conjClosed_intPoly S hintS hclS with ⟨P, hP⟩
  refine ⟨P, ?_⟩
  calc
    (∏ k : Fin n, (X - C (b k))) = ∏ y ∈ S, (X - C y) := by
      dsimp [S]
      exact (Finset.prod_image (s := (Finset.univ : Finset (Fin n))) (g := b)
        (f := fun y : ℂ => X - C y) (by intro x hx y hy hxy; exact hinj hxy)).symm
    _ = P.map (algebraMap ℤ ℂ) := hP

end

end Commons.Polynomial.Prod