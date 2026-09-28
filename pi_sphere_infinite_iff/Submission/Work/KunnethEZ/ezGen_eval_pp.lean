import Mathlib
import Submission.Work.Cohomology.Kunneth.ezEval
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Cohomology.Crux33.EzGen

/-!
# The evaluation half of the general `(p,p)` Eilenberg–Zilber shuffle computation

For the general `(p,q)`-shuffle chain `Work.Cohomology.Crux33.ezGen p q X Y σ τ` (the sum over the
shuffles `S` of `shufSign S • (σ ∘ a_S, τ ∘ b_S)` in the tensor product `X ⊗ Y`), the
Alexander–Whitney cup product of the pullbacks of a cochain `θ` on `Y` (second factor) and `β` on
`X` (first factor) evaluates as

`⟨(snd^*θ) ⌣ (fst^*β), ezGen p p σ τ⟩ = (-1)^(p*p) · θ(τ) · β(σ)`

whenever `θ` annihilates the degenerate `p`-simplices of `Y` ("normalized").

Of the `binom(2p, p)` shuffle cells, exactly one — the shuffle with all `N`-steps first,
`S = {0, …, p-1}` — has *both* relevant faces equal to the identity; for every other shuffle the
front `p`-face of the second coordinate, `frontIncl p (p+p) ≫ bHom S`, is a non-surjective monotone
self-map of `⦋p⦌` (`not_surjective_of_ne_goodS`), hence the corresponding `Y`-simplex is degenerate
and is killed by `hθ`. The sign of the surviving shuffle is `(-1)^(p*p)`.

This is the general-`p` form of the `(3,3)` statement `Work.Cohomology.Kunneth.ezGen_eval`.

## Main results

* `ezCellGen_eval` — the evaluation of the cup product on a single shuffle cell (every `p`);
* `kronecker_ezGen_pp` — expansion of the shuffle chain into its cells;
* `goodS`, `frontIncl_comp_bHom_goodS`, `backIncl_comp_aHom_goodS` — the exceptional shuffle and
  its two identity faces;
* `not_surjective_of_ne_goodS`, `mem_degenerate_of_not_surjective_self` — the junk-killing step;
* `shufSign_goodS` — the sign of the exceptional shuffle;
* `ezGen_eval_pp` — the statement.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.KunnethEZ

open Work.Cohomology
open Work.Cohomology.Crux33

noncomputable section

/-! ## Auxiliary counting lemma -/

/-- The number of elements `< m` of `Fin N` is `min m N`. -/
lemma card_filter_val_lt (m N : ℕ) :
    ((Finset.univ : Finset (Fin N)).filter (fun j => j.val < m)).card = min m N := by
  rw [← Finset.card_range (min m N)]
  refine Finset.card_bij
    (fun (j : Fin N) (_ : j ∈ (Finset.univ : Finset (Fin N)).filter (fun j => j.val < m)) =>
      j.val) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_range]; omega
  · intro a _ b _ hab; exact Fin.ext hab
  · intro b hb
    simp only [Finset.mem_range] at hb
    exact ⟨⟨b, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩

/-! ## The exceptional shuffle `N … N E … E` -/

/-- The exceptional `(n,n)`-shuffle: all `N`-steps first (`S = {j : j.val < n}`). -/
def goodSF (n : ℕ) : Finset (Fin (n+n)) :=
  (Finset.univ : Finset (Fin (n+n))).filter (fun j => j.val < n)

/-- The exceptional `(n,n)`-shuffle. -/
def goodS (n : ℕ) : PShuffle n n :=
  ⟨goodSF n, by rw [goodSF, card_filter_val_lt]; exact Nat.min_eq_left (Nat.le_add_right n n)⟩

lemma mem_goodS (n : ℕ) (j : Fin (n+n)) : j ∈ (goodS n).1 ↔ j.val < n := by
  show j ∈ goodSF n ↔ j.val < n; simp [goodSF]

/-- The `j`-th vertex (for `j ≤ n`) of the `N`-count map of the exceptional shuffle is `j`. -/
lemma pB_goodS_le (n : ℕ) (i : Fin (n+n+1)) (hi : i.val ≤ n) : pB (goodS n).1 i = i.val := by
  rw [pB]
  have hf : (goodS n).1.filter (fun j => j.val < i.val)
      = (Finset.univ : Finset (Fin (n+n))).filter (fun j => j.val < i.val) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_goodS]; omega
  rw [hf, card_filter_val_lt]
  exact Nat.min_eq_left (le_trans hi (Nat.le_add_right n n))

/-- Cardinality of the (interval) set `{j : Fin (n+n) | n ≤ j.val < n+t}`. -/
lemma card_good_pA (n t : ℕ) (ht : t ≤ n) :
    ((Finset.univ : Finset (Fin (n+n))).filter (fun j => n ≤ j.val ∧ j.val < n+t)).card = t := by
  have hcard : ((Finset.univ : Finset (Fin (n+n))).filter (fun j => n ≤ j.val ∧ j.val < n+t)).card
      = (Finset.range t).card := by
    refine Finset.card_bij
      (fun (j : Fin (n+n))
        (hj : j ∈ (Finset.univ : Finset (Fin (n+n))).filter (fun j => n ≤ j.val ∧ j.val < n+t)) =>
        j.val - n) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [Finset.mem_range]; omega
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      apply Fin.ext; omega
    · intro b hb
      simp only [Finset.mem_range] at hb
      exact ⟨⟨n + b, by omega⟩,
        by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, by simp⟩
  rw [hcard, Finset.card_range]

/-- The `(n+t)`-th vertex (`t ≤ n`) of the `E`-count map of the exceptional shuffle is `t`. -/
lemma pA_goodS (n t : ℕ) (ht : t ≤ n) :
    pA (goodS n).1 (⟨n+t, by omega⟩ : Fin (n+n+1)) = t := by
  rw [pA]
  have hset : (((Finset.univ : Finset (Fin (n+n))).filter (fun j => j.val < n + t)) \ (goodS n).1)
      = (Finset.univ : Finset (Fin (n+n))).filter (fun j => n ≤ j.val ∧ j.val < n+t) := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, mem_goodS]
    omega
  rw [hset, card_good_pA n t ht]

/-- Vertices of `⦋n⦌` have value `≤ n`. -/
lemma fin_len_succ_le (n : ℕ) (j : Fin (⦋n⦌.len + 1)) : j.val ≤ n := by
  have := j.isLt; simp only [SimplexCategory.len_mk] at this; omega

/-- The front `n`-face of the `N`-count map of the exceptional shuffle is the identity. -/
lemma frontIncl_comp_bHom_goodS (n : ℕ) :
    (frontIncl n (n+n) (Nat.le_add_right n n)) ≫ (bHom (goodS n).1 (goodS n).2) = 𝟙 ⦋n⦌ := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  rw [CategoryTheory.comp_apply]
  apply Fin.ext
  rw [bHom_val]
  have harg : ((ConcreteCategory.hom (frontIncl n (n+n) (Nat.le_add_right n n))) j)
      = (⟨j.val, by have := fin_len_succ_le n j; omega⟩ : Fin (n+n+1)) :=
    Fin.ext (by rw [hom_frontIncl_val])
  rw [harg]
  exact pB_goodS_le n ⟨j.val, by have := fin_len_succ_le n j; omega⟩ (fin_len_succ_le n j)

/-- The back `n`-face of the `E`-count map of the exceptional shuffle is the identity. -/
lemma backIncl_comp_aHom_goodS (n : ℕ) :
    (backIncl n n) ≫ (aHom (goodS n).1 (goodS n).2) = 𝟙 ⦋n⦌ := by
  refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
  rw [CategoryTheory.comp_apply]
  apply Fin.ext
  rw [aHom_val]
  have harg : ((ConcreteCategory.hom (backIncl n n)) j)
      = (⟨n + j.val, by have := fin_len_succ_le n j; omega⟩ : Fin (n+n+1)) :=
    Fin.ext (by rw [hom_backIncl_val])
  rw [harg]
  exact pA_goodS n j.val (fin_len_succ_le n j)

/-! ## The sign of the exceptional shuffle -/

/-- The `N`-count of the exceptional shuffle at an `E`-step is `n`. -/
lemma pBNat_goodS (n : ℕ) (j : Fin (n+n)) (hj : j ∉ (goodS n).1) : pBNat (goodS n).1 j.val = n := by
  rw [pBNat]
  have hfil : (goodS n).1.filter (fun k => k.val < j.val) = (goodS n).1 := by
    refine Finset.filter_eq_self.mpr (fun k hk => ?_)
    rw [mem_goodS] at hk
    have : ¬ j.val < n := fun h => hj ((mem_goodS n j).mpr h)
    omega
  rw [hfil, (goodS n).2]

/-- The inversion count of the exceptional shuffle is `p · p = n · n`. -/
lemma invCount_goodS (n : ℕ) : invCount (goodS n).1 = n * n := by
  rw [invCount]
  rw [Finset.sum_congr rfl (fun j hj => pBNat_goodS n j (Finset.mem_sdiff.mp hj).2)]
  rw [Finset.sum_const]
  have hcard : ((Finset.univ : Finset (Fin (n+n))) \ (goodS n).1).card = n := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, (goodS n).2]
    omega
  rw [hcard]; simp

/-- The Eilenberg–Zilber sign of the exceptional shuffle is `(-1)^(n·n)`. -/
lemma shufSign_goodS (n : ℕ) : shufSign (goodS n).1 = (-1 : ℤ) ^ (n*n) := by
  rw [shufSign, invCount_goodS]

/-! ## Junk-killing: every other shuffle has a degenerate `Y`-face -/

/-- For a shuffle `S ≠ goodS n`, the front `n`-face of its `N`-count map is not surjective.

Indeed `frontIncl n (n+n) ≫ bHom S` is monotone with `0 ↦ 0`, and if it were surjective it would
attain the value `n`, i.e. `#{k ∈ S : k.val < n} = n = |S|`, forcing `S = goodS n`. -/
lemma not_surjective_of_ne_goodS {n : ℕ} (S : PShuffle n n) (hS : S ≠ goodS n) :
    ¬ Function.Surjective ⇑((frontIncl n (n+n) (Nat.le_add_right n n)) ≫ (bHom S.1 S.2)).toOrderHom := by
  change ¬ Function.Surjective
    (fun i : Fin (n+1) =>
      (ConcreteCategory.hom ((frontIncl n (n+n) (Nat.le_add_right n n)) ≫ (bHom S.1 S.2))) i)
  intro hsurj
  obtain ⟨j, hj⟩ := hsurj ⟨n, Nat.lt_succ_self n⟩
  have h2 : pB S.1 ((ConcreteCategory.hom (frontIncl n (n+n) (Nat.le_add_right n n))) j) = n := by
    have h3 : (↑((ConcreteCategory.hom
          ((frontIncl n (n+n) (Nat.le_add_right n n)) ≫ (bHom S.1 S.2))) j) : ℕ)
        = pB S.1 ((ConcreteCategory.hom (frontIncl n (n+n) (Nat.le_add_right n n))) j) := by
      simp only [CategoryTheory.comp_apply, bHom_val]
    have h4 : (↑((ConcreteCategory.hom
          ((frontIncl n (n+n) (Nat.le_add_right n n)) ≫ (bHom S.1 S.2))) j) : ℕ) = n := by
      simpa using congrArg Fin.val hj
    rw [← h3, h4]
  have hcard : (S.1.filter (fun k =>
      k.val < ((ConcreteCategory.hom (frontIncl n (n+n) (Nat.le_add_right n n))) j).val)).card
      = S.1.card := by
    show pB S.1 ((ConcreteCategory.hom (frontIncl n (n+n) (Nat.le_add_right n n))) j) = S.1.card
    rw [h2]; exact S.2.symm
  have hfs : S.1.filter (fun k =>
      k.val < ((ConcreteCategory.hom (frontIncl n (n+n) (Nat.le_add_right n n))) j).val) = S.1 := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    rw [hcard]
  have hsub : S.1 ⊆ (goodS n).1 := by
    intro k hk
    rw [mem_goodS]
    have hklt := (Finset.filter_eq_self.mp hfs) k hk
    have hXv : ((ConcreteCategory.hom (frontIncl n (n+n) (Nat.le_add_right n n))) j).val = j.val :=
      hom_frontIncl_val n (n+n) (Nat.le_add_right n n) j
    omega
  have heq : S.1 = (goodS n).1 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [(goodS n).2, S.2])
  exact hS (Subtype.ext heq)

/-- A simplex obtained from a non-surjective monotone self-map of `⦋n+1⦌` is degenerate. -/
lemma mem_degenerate_of_not_surjective_self {X : SSet} {n : ℕ} (f : ⦋n+1⦌ ⟶ ⦋n+1⦌)
    (hf : ¬ Function.Surjective ⇑f.toOrderHom) (x : X _⦋n+1⦌) :
    X.map f.op x ∈ X.degenerate (n+1) := by
  obtain ⟨i, f', hf'⟩ := SimplexCategory.eq_σ_comp_of_not_injective f
    (fun hinj => hf (Finite.injective_iff_surjective.mp hinj))
  rw [hf', CategoryTheory.op_comp, Functor.map_comp]
  exact X.σ_mem_degenerate i (X.map f'.op x)

/-! ## Evaluation on a single shuffle cell -/

/-- The simplex of the tensor product attached to a shuffle `S`: `(σ ∘ a_S, τ ∘ b_S)`. -/
abbrev ezCellGen (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) (S : PShuffle p q) :
    (X ⊗ Y) _⦋p+q⦌ := (X.map (aHom S.1 S.2).op σ, Y.map (bHom S.1 S.2).op τ)

/-- The front `p`-face of the `Y`-coordinate of a shuffle cell, as a composite on the `Y` side. -/
lemma frontFace_bHom_comp_gen (n : ℕ) (Y : SSet) (S : PShuffle (n+1) (n+1)) (τ : Y _⦋n+1⦌) :
    frontFace Y (n+1) ((n+1)+(n+1)) (Nat.le_add_right (n+1) (n+1)) (Y.map (bHom S.1 S.2).op τ)
      = Y.map ((frontIncl (n+1) ((n+1)+(n+1)) (Nat.le_add_right (n+1) (n+1))) ≫
          (bHom S.1 S.2)).op τ := by
  show Y.map (frontIncl (n+1) ((n+1)+(n+1)) (Nat.le_add_right (n+1) (n+1))).op
      (Y.map (bHom S.1 S.2).op τ) = _
  exact Work.Cohomology.map_op_comp (bHom S.1 S.2)
    (frontIncl (n+1) ((n+1)+(n+1)) (Nat.le_add_right (n+1) (n+1))) τ

/-- The back `p`-face of the `X`-coordinate of a shuffle cell, as a composite on the `X` side. -/
lemma backFace_aHom_comp_gen (n : ℕ) (X : SSet) (S : PShuffle (n+1) (n+1)) (σ : X _⦋n+1⦌) :
    backFace X (n+1) (n+1) (X.map (aHom S.1 S.2).op σ)
      = X.map ((backIncl (n+1) (n+1)) ≫ (aHom S.1 S.2)).op σ := by
  show X.map (backIncl (n+1) (n+1)).op (X.map (aHom S.1 S.2).op σ) = _
  exact Work.Cohomology.map_op_comp (aHom S.1 S.2) (backIncl (n+1) (n+1)) σ

/-- **The evaluation of the cup product on one shuffle cell.** -/
lemma ezCellGen_eval (n : ℕ) (X Y : SSet) (β : Cochain ℤ X (n+1)) (θ : Cochain ℤ Y (n+1))
    (σ : X _⦋n+1⦌) (τ : Y _⦋n+1⦌) (S : PShuffle (n+1) (n+1)) :
    genEval ℤ (X ⊗ Y)
      (cup ℤ (X ⊗ Y)
        (Work.Cohomology.Kunneth.ssetPullback (X ⊗ Y) Y
          (SemiCartesianMonoidalCategory.snd X Y) (n+1) θ)
        (Work.Cohomology.Kunneth.ssetPullback (X ⊗ Y) X
          (SemiCartesianMonoidalCategory.fst X Y) (n+1) β))
      (ezCellGen (n+1) (n+1) X Y σ τ S)
    = genEval ℤ Y θ
        (Y.map ((frontIncl (n+1) ((n+1)+(n+1)) (Nat.le_add_right (n+1) (n+1))) ≫ (bHom S.1 S.2)).op τ)
      * genEval ℤ X β
        (X.map ((backIncl (n+1) (n+1)) ≫ (aHom S.1 S.2)).op σ) := by
  simp only [ezCellGen]
  rw [cup_apply, Work.Cohomology.Kunneth.frontFace_prod_mk, Work.Cohomology.Kunneth.backFace_prod_mk,
      Work.Cohomology.Kunneth.ssetPullback_genEval, Work.Cohomology.Kunneth.ssetPullback_genEval,
      Work.Cohomology.Kunneth.fst_apply_prod, Work.Cohomology.Kunneth.snd_apply_prod,
      frontFace_bHom_comp_gen, backFace_aHom_comp_gen]

/-! ## Extracting a scalar -/

/-- Extracting a `ℤ`-scalar on the chain side of the Kronecker pairing (the instances need to be
transported along `Int.cast_smul_eq_zsmul`). -/
lemma cochain_smul_chain (X : SSet) {m : ℕ} (γ : Cochain ℤ X m) (r : ℤ)
    (c : (X.chainComplex (ModuleCat.of ℤ ℤ)).X m) : γ (r • c) = r • γ c := by
  rw [← Int.cast_smul_eq_zsmul ℤ r c, ← Int.cast_smul_eq_zsmul ℤ r (γ c)]
  exact LinearMap.map_smul γ (r : ℤ) c

/-- The shuffle chain, with the Kronecker pairing expanded into a sum over the shuffles. -/
lemma kronecker_ezGen_pp (n : ℕ) (X Y : SSet) (γ : Cochain ℤ (X ⊗ Y) ((n+1)+(n+1)))
    (σ : X _⦋n+1⦌) (τ : Y _⦋n+1⦌) :
    kronecker ℤ (X ⊗ Y) γ (ezGen (n+1) (n+1) X Y σ τ)
      = ∑ S : PShuffle (n+1) (n+1), shufSign S.1 •
          genEval ℤ (X ⊗ Y) γ (ezCellGen (n+1) (n+1) X Y σ τ S) := by
  change γ (ezGen (n+1) (n+1) X Y σ τ)
    = ∑ S : PShuffle (n+1) (n+1), shufSign S.1 •
        γ (((X⊗Y).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (ezCellGen (n+1) (n+1) X Y σ τ S)).hom 1)
  rw [ezGen, map_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  exact cochain_smul_chain (X⊗Y) γ (shufSign S.1) _

/-! ## The main statement -/

theorem ezGen_eval_pp (p : ℕ) (hp : 1 ≤ p) (X Y : SSet)
    (β : Work.Cohomology.Cochain ℤ X p) (θ : Work.Cohomology.Cochain ℤ Y p)
    (σ : X.obj (Opposite.op (SimplexCategory.mk p)))
    (τ : Y.obj (Opposite.op (SimplexCategory.mk p)))
    (hθ : ∀ (x : Y.obj (Opposite.op (SimplexCategory.mk p))), x ∈ Y.degenerate p →
        Work.Cohomology.genEval ℤ Y θ x = 0) :
    Work.Cohomology.kronecker ℤ (CategoryTheory.MonoidalCategory.tensorObj X Y)
      (Work.Cohomology.cup ℤ (CategoryTheory.MonoidalCategory.tensorObj X Y)
        (Work.Cohomology.Kunneth.ssetPullback (CategoryTheory.MonoidalCategory.tensorObj X Y) Y
          (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) p θ)
        (Work.Cohomology.Kunneth.ssetPullback (CategoryTheory.MonoidalCategory.tensorObj X Y) X
          (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p β))
      (Work.Cohomology.Crux33.ezGen p p X Y σ τ)
      = ((-1 : ℤ) ^ (p*p)) * Work.Cohomology.genEval ℤ Y θ τ * Work.Cohomology.genEval ℤ X β σ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  -- evaluation of one shuffle term
  have key : ∀ S : PShuffle (n+1) (n+1),
      (cup ℤ (X ⊗ Y)
          (Work.Cohomology.Kunneth.ssetPullback (X ⊗ Y) Y
            (SemiCartesianMonoidalCategory.snd X Y) (n+1) θ)
          (Work.Cohomology.Kunneth.ssetPullback (X ⊗ Y) X
            (SemiCartesianMonoidalCategory.fst X Y) (n+1) β))
        (shufSign S.1 • (((X ⊗ Y).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (ezCellGen (n+1) (n+1) X Y σ τ S)).hom 1))
      = shufSign S.1 •
          (genEval ℤ Y θ
              (Y.map ((frontIncl (n+1) ((n+1)+(n+1)) (Nat.le_add_right (n+1) (n+1))) ≫
                (bHom S.1 S.2)).op τ)
            * genEval ℤ X β
              (X.map ((backIncl (n+1) (n+1)) ≫ (aHom S.1 S.2)).op σ)) := by
    intro S
    rw [cochain_smul_chain (X⊗Y) _ (shufSign S.1) _]
    congr 1
    simpa only [genEval, ezCellGen] using ezCellGen_eval n X Y β θ σ τ S
  change (cup ℤ (X ⊗ Y)
        (Work.Cohomology.Kunneth.ssetPullback (X ⊗ Y) Y
          (SemiCartesianMonoidalCategory.snd X Y) (n+1) θ)
        (Work.Cohomology.Kunneth.ssetPullback (X ⊗ Y) X
          (SemiCartesianMonoidalCategory.fst X Y) (n+1) β))
      (ezGen (n+1) (n+1) X Y σ τ)
      = ((-1 : ℤ) ^ ((n+1)*(n+1))) * genEval ℤ Y θ τ * genEval ℤ X β σ
  rw [ezGen, map_sum]
  rw [Finset.sum_congr rfl (fun S _ => key S)]
  rw [Finset.sum_eq_single (goodS (n+1))]
  · -- the exceptional shuffle
    have h1 : Y.map ((frontIncl (n+1) ((n+1)+(n+1)) (Nat.le_add_right (n+1) (n+1))) ≫
        (bHom (goodS (n+1)).1 (goodS (n+1)).2)).op τ = τ := by
      have h := congrArg (fun (f : ⦋(n+1)⦌ ⟶ ⦋(n+1)⦌) => Y.map f.op τ)
        (frontIncl_comp_bHom_goodS (n+1))
      simpa using h
    have h2 : X.map ((backIncl (n+1) (n+1)) ≫
        (aHom (goodS (n+1)).1 (goodS (n+1)).2)).op σ = σ := by
      have h := congrArg (fun (f : ⦋(n+1)⦌ ⟶ ⦋(n+1)⦌) => X.map f.op σ)
        (backIncl_comp_aHom_goodS (n+1))
      simpa using h
    rw [h1, h2, shufSign_goodS, smul_eq_mul, mul_assoc]
  · -- every other shuffle is killed by `hθ`
    intro S _ hS
    have hns := not_surjective_of_ne_goodS S hS
    have hdeg : Y.map ((frontIncl (n+1) ((n+1)+(n+1)) (Nat.le_add_right (n+1) (n+1))) ≫
        (bHom S.1 S.2)).op τ ∈ Y.degenerate (n+1) :=
      mem_degenerate_of_not_surjective_self _ hns τ
    rw [hθ _ hdeg, zero_mul, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end

end Work.KunnethEZ
