import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

open Submission.Cohomology

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false

/-!
# The Leibniz rule for the cup product on simplicial cochains

`δ (u ⌣ v) = δu ⌣ v + (-1)^p u ⌣ δv`

We prove the chain level identity `cupOf_coboundary`, which is the simplicial (Alexander–Whitney)
Leibniz rule.  The combinatorial content are the cosimplicial identities relating the front/back
face inclusions `SimplexCategory.subinterval` with the coface maps `SimplexCategory.δ`.
-/

/-! ## Combinatorial identities in the simplex category -/

/-- The "applied" form of `Functor.map_comp` for `S.map`. -/
lemma map_comp_apply' {S : SSet.{0}} {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (σ : S.obj (op c)) : S.map f.op (S.map g.op σ) = S.map (f ≫ g).op σ := by
  rw [← Functor.map_comp_apply, op_comp]

/-- The front `p`-face, followed by the `i`-th face, is the `i`-th face of the front `(p+1)`-face
(here `i ≤ p`; at `i = p+1` the two sides are the "front `p`-face in degree `n+1`"). -/
lemma subint_zero_comp_δ (p q n : ℕ) (h : p + q = n) (i : Fin (p+1)) :
    SimplexCategory.subinterval (n := n) 0 p (by omega) ≫
        (SimplexCategory.δ (⟨(i:ℕ), by omega⟩ : Fin (n+2)))
      = (SimplexCategory.δ i.castSucc : ⦋p⦌ ⟶ ⦋p+1⦌) ≫
          SimplexCategory.subinterval (n := n+1) 0 (p+1) (by omega) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.subinterval, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply, OrderHom.coe_mk,
    Fin.castLE, Fin.succAbove]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.add_zero, Fin.lt_def]
  split_ifs <;> simp_all

/-- For `i ≥ p+1`, the front `p`-face of the `i`-th face of an `(n+1)`-simplex is the front
`p`-face of the `(n+1)`-simplex itself. -/
lemma subint_zero_comp_δ_ge (p q n : ℕ) (h : p + q = n) (j : Fin (n+2)) (hj : p + 1 ≤ (j:ℕ)) :
    SimplexCategory.subinterval (n := n) 0 p (by omega) ≫ SimplexCategory.δ j
      = SimplexCategory.subinterval (n := n+1) 0 p (by omega) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.subinterval, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply, OrderHom.coe_mk,
    Fin.castLE, Fin.succAbove]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.add_zero, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

/-- For `i ≤ p`, the back `q`-face of the `i`-th face of an `(n+1)`-simplex is the back
`q`-face (in degree `n+1`, i.e. along `subinterval (p+1) q`) of the `(n+1)`-simplex. -/
lemma subint_comp_δ_le (p q n : ℕ) (h : p + q = n) (j : Fin (n+2)) (hj : (j:ℕ) ≤ p) :
    SimplexCategory.subinterval (n := n) p q (by omega) ≫ SimplexCategory.δ j
      = SimplexCategory.subinterval (n := n+1) (p+1) q (by omega) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.subinterval, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply, OrderHom.coe_mk,
    Fin.castLE, Fin.succAbove]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.add_zero, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

/-- The general "back face" cosimplicial identity, valid for all `k : Fin (q+2)`:
`subinterval p q ≫ δ_{p+k} = δ_k ≫ subinterval p (q+1)`. -/
lemma subint_comp_δ_ge (p q n : ℕ) (h : p + q = n) (k : Fin (q+2)) :
    SimplexCategory.subinterval (n := n) p q (by omega) ≫
        (SimplexCategory.δ (⟨p + (k:ℕ), by omega⟩ : Fin (n+2)))
      = (SimplexCategory.δ k : ⦋q⦌ ⟶ ⦋q+1⦌) ≫
          SimplexCategory.subinterval (n := n+1) p (q+1) (by omega) := by
  ext kk
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.subinterval, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply, OrderHom.coe_mk,
    Fin.castLE, Fin.succAbove]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.add_zero, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

/-- The face `δ_{p+1}` of the front `(p+1)`-face is the front `p`-face. -/
lemma δ_last_comp_subint (p q n : ℕ) (h : p + q = n) :
    (SimplexCategory.δ (Fin.last (p+1)) : ⦋p⦌ ⟶ ⦋p+1⦌) ≫
        SimplexCategory.subinterval (n := n+1) 0 (p+1) (by omega)
      = SimplexCategory.subinterval (n := n+1) 0 p (by omega) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.subinterval, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply, OrderHom.coe_mk,
    Fin.castLE, Fin.succAbove]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.add_zero, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

/-- The face `δ_0` of the back `(q+1)`-face is the back `q`-face. -/
lemma δ_zero_comp_subint (p q n : ℕ) (h : p + q = n) :
    (SimplexCategory.δ 0 : ⦋q⦌ ⟶ ⦋q+1⦌) ≫
        SimplexCategory.subinterval (n := n+1) p (q+1) (by omega)
      = SimplexCategory.subinterval (n := n+1) (p+1) q (by omega) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, SimplexCategory.subinterval, SimplexCategory.δ,
    SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply, OrderHom.coe_mk,
    Fin.castLE, Fin.succAbove]
  simp only [Fin.val_castSucc, Fin.val_succ, Nat.add_zero, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

/-! ## The same identities for simplicial sets -/

lemma frontOf_δ_castSucc (S : SSet.{0}) {n p q : ℕ} (h : p + q = n) (h₁ : (p+1) + q = n+1)
    (i : Fin (p+1)) (σ : S.obj (op ⦋n+1⦌)) :
    frontOf S h (S.δ (⟨(i:ℕ), by omega⟩ : Fin (n+2)) σ) = S.δ i.castSucc (frontOf S h₁ σ) := by
  simp only [frontOf, SimplicialObject.δ]
  simp only [map_comp_apply']
  rw [subint_zero_comp_δ p q n h i]

lemma frontOf_δ_ge (S : SSet.{0}) {n p q : ℕ} (h : p + q = n) (h₂ : p + (q+1) = n+1)
    (j : Fin (n+2)) (hj : p + 1 ≤ (j:ℕ)) (σ : S.obj (op ⦋n+1⦌)) :
    frontOf S h (S.δ j σ) = frontOf S h₂ σ := by
  simp only [frontOf, SimplicialObject.δ]
  simp only [map_comp_apply']
  rw [subint_zero_comp_δ_ge p q n h j hj]

lemma backOf_δ_le (S : SSet.{0}) {n p q : ℕ} (h : p + q = n) (h₁ : (p+1) + q = n+1)
    (j : Fin (n+2)) (hj : (j:ℕ) ≤ p) (σ : S.obj (op ⦋n+1⦌)) :
    backOf S h (S.δ j σ) = backOf S h₁ σ := by
  simp only [backOf, SimplicialObject.δ]
  simp only [map_comp_apply']
  rw [subint_comp_δ_le p q n h j hj]

lemma backOf_δ_ge (S : SSet.{0}) {n p q : ℕ} (h : p + q = n) (h₂ : p + (q+1) = n+1)
    (k : Fin (q+2)) (σ : S.obj (op ⦋n+1⦌)) :
    backOf S h (S.δ (⟨p + (k:ℕ), by omega⟩ : Fin (n+2)) σ)
      = S.δ k (backOf S h₂ σ) := by
  simp only [backOf, SimplicialObject.δ]
  simp only [map_comp_apply']
  rw [subint_comp_δ_ge p q n h k]

lemma frontOf_δ_last (S : SSet.{0}) {n p q : ℕ} (h : p + q = n) (h₁ : (p+1)+q = n+1)
    (h₂ : p+(q+1) = n+1) (σ : S.obj (op ⦋n+1⦌)) :
    S.δ (Fin.last (p+1)) (frontOf S h₁ σ) = frontOf S h₂ σ := by
  simp only [frontOf, SimplicialObject.δ]
  simp only [map_comp_apply']
  rw [δ_last_comp_subint p q n h]

lemma backOf_δ_zero (S : SSet.{0}) {n p q : ℕ} (h : p + q = n) (h₁ : (p+1)+q = n+1)
    (h₂ : p+(q+1) = n+1) (σ : S.obj (op ⦋n+1⦌)) :
    S.δ 0 (backOf S h₂ σ) = backOf S h₁ σ := by
  simp only [backOf, SimplicialObject.δ]
  simp only [map_comp_apply']
  rw [δ_zero_comp_subint p q n h]

/-! ## Sums -/

/-- Split a sum over `Fin N` into the two blocks `Fin a` and `Fin b` (with `a + b = N`). -/
lemma Fin.sum_univ_split {M : Type*} [AddCommMonoid M] {N a b : ℕ} (h : a + b = N)
    (f : Fin N → M) :
    ∑ i : Fin N, f i
      = (∑ i : Fin a, f ⟨i.1, by omega⟩) + (∑ i : Fin b, f ⟨a + i.1, by omega⟩) := by
  subst h
  rw [Fintype.sum_equiv finSumFinEquiv.symm (fun i : Fin (a+b) => f i) (fun x => f (finSumFinEquiv x))
    (by intro x; simp)]
  simp only [Fintype.sum_sum_type, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    Fin.castAdd, Fin.natAdd, Fin.castLE]

/-- The `(-1)^k`-multiples of a ring element are the scalar multiples. -/
lemma neg_one_zsmul (R : Type) [Ring R] (k : ℕ) (x : R) : (-1:ℤ)^k • x = (-1:R)^k * x := by
  rw [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

lemma neg_one_pow_succ (R : Type) [CommRing R] (k : ℕ) : (-1:R)^(k+1) = -(-1:R)^k := by
  rw [pow_succ]; ring

/-! ## The pointwise Leibniz rule -/

lemma cupOf_coboundary_apply (S : SSet.{0}) (R : Type) [CommRing R] {n p q : ℕ}
    (h : p + q = n) (h₁ : (p+1) + q = n+1) (h₂ : p + (q+1) = n+1)
    (u : Cochain S R p) (v : Cochain S R q) (σ : S.obj (op ⦋n+1⦌)) :
    coboundary S R n (cupOf S R h u v) σ
      = cupOf S R h₁ (coboundary S R p u) v σ
        + (-1 : ℤ) ^ p • (cupOf S R h₂ u (coboundary S R q v) σ) := by
  simp only [coboundary_apply, cupOf_apply, neg_one_zsmul]
  rw [Fin.sum_univ_split (by omega : (p+1) + (q+1) = n+2)]
  -- Block 1 : `i ≤ p`
  have hS1 : (∑ i : Fin (p+1), (-1:R)^(i:ℕ) *
        (u (frontOf S h (S.δ (⟨(i:ℕ), by omega⟩ : Fin (n+2)) σ)) *
         v (backOf S h (S.δ (⟨(i:ℕ), by omega⟩ : Fin (n+2)) σ))))
      = (∑ i : Fin (p+1), (-1:R)^(i:ℕ) * u (S.δ i.castSucc (frontOf S h₁ σ))) *
          v (backOf S h₁ σ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [frontOf_δ_castSucc S h h₁ i σ,
      backOf_δ_le S h h₁ (⟨(i:ℕ), by omega⟩ : Fin (n+2)) (by simp only [Fin.val_mk]; omega) σ]
    ring
  -- Block 2 : `i ≥ p+1`
  have hS2 : (∑ i : Fin (q+1), (-1:R)^(p+1+(i:ℕ)) *
        (u (frontOf S h (S.δ (⟨p+1+(i:ℕ), by omega⟩ : Fin (n+2)) σ)) *
         v (backOf S h (S.δ (⟨p+1+(i:ℕ), by omega⟩ : Fin (n+2)) σ))))
      = (-1:R)^(p+1) * (u (frontOf S h₂ σ) *
          (∑ i : Fin (q+1), (-1:R)^(i:ℕ) * v (S.δ i.succ (backOf S h₂ σ)))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [frontOf_δ_ge S h h₂ (⟨p+1+(i:ℕ), by omega⟩ : Fin (n+2))
      (by simp only [Fin.val_mk]; omega) σ]
    have hjk : (⟨p+1+(i:ℕ), by omega⟩ : Fin (n+2)) = (⟨p + (i.succ:ℕ), by omega⟩ : Fin (n+2)) := by
      apply Fin.ext
      simp only [Fin.val_mk, Fin.val_succ]
      omega
    rw [hjk]
    rw [backOf_δ_ge S h h₂ i.succ σ]
    rw [pow_add]
    ring
  -- The `δu` sum, split off the last term.
  have hr : (∑ j : Fin (p+2), (-1:R)^(j:ℕ) * u (S.δ j (frontOf S h₁ σ)))
      = (∑ i : Fin (p+1), (-1:R)^(i:ℕ) * u (S.δ i.castSucc (frontOf S h₁ σ)))
        + (-1:R)^(p+1) * u (frontOf S h₂ σ) := by
    rw [Fin.sum_univ_castSucc (f := fun j : Fin (p+2) =>
      (-1:R)^(j:ℕ) * u (S.δ j (frontOf S h₁ σ)))]
    simp only [Fin.val_castSucc, Fin.val_last, frontOf_δ_last S h h₁ h₂ σ]
  -- The `δv` sum, split off the first term.
  have hs : (∑ l : Fin (q+2), (-1:R)^(l:ℕ) * v (S.δ l (backOf S h₂ σ)))
      = v (backOf S h₁ σ)
        - (∑ i : Fin (q+1), (-1:R)^(i:ℕ) * v (S.δ i.succ (backOf S h₂ σ))) := by
    rw [Fin.sum_univ_succ (f := fun l : Fin (q+2) =>
      (-1:R)^(l:ℕ) * v (S.δ l (backOf S h₂ σ)))]
    simp only [Fin.val_zero, pow_zero, one_mul]
    rw [backOf_δ_zero S h h₁ h₂ σ]
    have hsum : (∑ i : Fin (q+1), (-1:R)^(Fin.val i.succ) * v (S.δ i.succ (backOf S h₂ σ)))
        = - (∑ i : Fin (q+1), (-1:R)^(i:ℕ) * v (S.δ i.succ (backOf S h₂ σ))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.val_succ, pow_succ]
      ring
    rw [hsum]
    ring
  rw [hS1, hS2, hr, hs, neg_one_pow_succ R p]
  ring_nf


theorem cupOf_coboundary (S : SSet.{0}) (R : Type) [CommRing R] {n p q : ℕ}
    (h : p + q = n) (u : Submission.Cohomology.Cochain S R p)
    (v : Submission.Cohomology.Cochain S R q) :
    Submission.Cohomology.coboundary S R n (Submission.Cohomology.cupOf S R h u v)
      = Submission.Cohomology.cupOf S R (by omega : (p + 1) + q = n + 1)
          (Submission.Cohomology.coboundary S R p u) v
        + (-1 : ℤ) ^ p • Submission.Cohomology.cupOf S R (by omega : p + (q + 1) = n + 1)
          u (Submission.Cohomology.coboundary S R q v) := by
  funext σ
  simp only [Pi.add_apply, Pi.smul_apply]
  exact cupOf_coboundary_apply S R h (by omega) (by omega) u v σ

end Work.Cohomology
