import Mathlib
import Submission.Work.Cohomology.CupOne
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.coboundary_comp

open CategoryTheory Simplicial Opposite
open ConcreteCategory

namespace Work.Cohomology


/-! ## Basic `Fin`/simplex-category helpers -/

/-- The value of `Fin.succAbove`, as an explicit `if`. -/
lemma val_succAbove {m : ℕ} (p : Fin (m+1)) (i : Fin m) :
    ((p.succAbove i : Fin (m+1)) : ℕ) = if (i:ℕ) < (p:ℕ) then (i:ℕ) else (i:ℕ)+1 := by
  by_cases h : (i:ℕ) < (p:ℕ)
  · rw [Fin.succAbove_of_castSucc_lt p i (by rw [Fin.lt_def]; simpa using h), Fin.val_castSucc,
      if_pos h]
  · rw [Fin.succAbove_of_le_castSucc p i (by rw [Fin.le_def]; simpa using h), Fin.val_succ,
      if_neg h]

/-- The value of a `subinterval` inclusion. -/
lemma subinterval_apply {m : ℕ} (j l : ℕ) (h : j + l ≤ m) (k : Fin (l+1)) :
    ((SimplexCategory.subinterval (n := m) j l h).toOrderHom k : ℕ) = (k:ℕ) + j := rfl

open ConcreteCategory in
/-- `(S.map f.op) ∘ (S.map g.op) = S.map (f ≫ g).op`, in the `ConcreteCategory.hom` form that
`simp` produces. -/
lemma mapCompHom {S : SSet.{0}} {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (σ : S.obj (op c)) : hom (S.map f.op) (hom (S.map g.op) σ) = hom (S.map (f ≫ g).op) σ := by
  rw [← Functor.map_comp_apply, op_comp]

open ConcreteCategory in
/-- `S.map` of a composite, applied to a simplex, `ConcreteCategory.hom` form. -/
lemma hom_map_apply {S : SSet.{0}} {a b : SimplexCategory} (f : a ⟶ b) (σ : S.obj (op b)) :
    hom (S.map f.op) σ = S.map f.op σ := rfl

/-- Split a sum over `Fin N` into the two blocks `Fin a` and `Fin b` (with `a + b = N`). -/
lemma sum_univ_split {M : Type*} [AddCommMonoid M] {N a b : ℕ} (h : a + b = N)
    (f : Fin N → M) :
    ∑ i : Fin N, f i
      = (∑ i : Fin a, f ⟨i.1, by omega⟩) + (∑ i : Fin b, f ⟨a + i.1, by omega⟩) := by
  subst h
  rw [Fintype.sum_equiv finSumFinEquiv.symm (fun i : Fin (a+b) => f i)
    (fun x => f (finSumFinEquiv x)) (by intro x; simp)]
  simp only [Fintype.sum_sum_type, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
    Fin.castAdd, Fin.natAdd, Fin.castLE]

/-- A sum over `Fin (N+1)` with a vanishing `0`-term is a sum over `Fin N`. -/
lemma sum_fin_succ_eq {β : Type*} [AddCommMonoid β] {N : ℕ} {g : Fin (N+1) → β} (h0 : g 0 = 0) :
    (∑ a : Fin (N+1), g a) = ∑ f : Fin N, g f.succ := by
  rw [Fin.sum_univ_succ, h0, zero_add]

lemma fin_succ_castSucc_eq {Q : ℕ} (j : Fin Q) : (j.succ.castSucc : Fin (Q+2)) = ⟨(j:ℕ)+1, by omega⟩ := by
  apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_mk]

lemma sum_fin_Ici' {β : Type*} [AddCommMonoid β] {N a b : ℕ} (hab : a + b = N)
    (g : Fin N → β) :
    (∑ j : Fin b, g ⟨a + j.1, by omega⟩)
      = ∑ i ∈ (Finset.univ.filter (fun i : Fin N => a ≤ (i:ℕ))), g i := by
  refine Finset.sum_bij'
      (fun (y : Fin b) (_ : y ∈ (Finset.univ : Finset (Fin b))) => (⟨a + y.1, by omega⟩ : Fin N))
      (fun (x : Fin N) (hx : x ∈ Finset.univ.filter (fun i : Fin N => a ≤ (i:ℕ))) =>
        (⟨x.1 - a, by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          have := x.isLt
          omega⟩ : Fin b)) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · intro x hx; exact Finset.mem_univ _
  · intro y hy; apply Fin.ext; simp only [Fin.val_mk]; omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    apply Fin.ext; simp only [Fin.val_mk]; omega
  · intro y hy; congr 1

lemma sum_fin_Ico {β : Type*} [AddCommMonoid β] {N a b : ℕ} (hab : a + b ≤ N)
    (g : Fin N → β) :
    (∑ j : Fin b, g ⟨a + j.1, by omega⟩)
      = ∑ i ∈ (Finset.univ.filter (fun i : Fin N => a ≤ (i:ℕ) ∧ (i:ℕ) < a + b)), g i := by
  refine Finset.sum_bij'
    (fun (y : Fin b) (_ : y ∈ (Finset.univ : Finset (Fin b))) => (⟨a + y.1, by omega⟩ : Fin N))
    (fun (x : Fin N) (hx : x ∈ Finset.univ.filter (fun i : Fin N => a ≤ (i:ℕ) ∧ (i:ℕ) < a + b)) =>
        (⟨x.1 - a, by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx; omega⟩ : Fin b))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · intro x hx; exact Finset.mem_univ _
  · intro y hy; apply Fin.ext; simp only [Fin.val_mk]; omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    apply Fin.ext; simp only [Fin.val_mk]; omega
  · intro y hy; congr 1

lemma sum_fin_Ici {β : Type*} [AddCommMonoid β] {N a : ℕ} (ha : a ≤ N)
    (g : Fin N → β) :
    (∑ j : Fin (N - a), g ⟨a + j.1, by omega⟩)
      = ∑ i ∈ (Finset.univ.filter (fun i : Fin N => a ≤ (i:ℕ))), g i := by
  refine Finset.sum_bij'
    (fun (y : Fin (N - a)) (_ : y ∈ (Finset.univ : Finset (Fin (N - a)))) =>
        (⟨a + y.1, by omega⟩ : Fin N))
    (fun (x : Fin N) (hx : x ∈ Finset.univ.filter (fun i : Fin N => a ≤ (i:ℕ))) =>
        (⟨x.1 - a, by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx; omega⟩ :
          Fin (N - a)))
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · intro x hx; exact Finset.mem_univ _
  · intro y hy; apply Fin.ext; simp only [Fin.val_mk]; omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    apply Fin.ext; simp only [Fin.val_mk]; omega
  · intro y hy; congr 1


/-- **Region A** (`i ≤ f`), `u`-component. -/
lemma TA_u {P Q n : ℕ} (h : P + Q = n + 1) (h1 : (P+1) + Q = (n+1) + 1) (f : Fin P) (i : Fin (P+1))
    (hi : (i:ℕ) ≤ (f:ℕ)) :
    Submission.Cohomology.joinFace h f ≫ (SimplexCategory.δ (⟨(i:ℕ), by omega⟩ : Fin (n+2)))
      = (SimplexCategory.δ (⟨(i:ℕ), by omega⟩ : Fin (P+2))) ≫
          Submission.Cohomology.joinFace h1 (⟨(f:ℕ)+1, by omega⟩ : Fin (P+1)) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [val_succAbove, Submission.Cohomology.joinFace_apply]
  rw [Submission.Cohomology.joinFace_apply, val_succAbove]
  split_ifs <;> simp_all <;> omega

/-- **Region A** (`i ≤ f`), `v`-component. -/
lemma TA_v {P Q n : ℕ} (h : P + Q = n + 1) (h1 : (P+1) + Q = (n+1) + 1) (f : Fin P) (i : Fin (P+1))
    (hi : (i:ℕ) ≤ (f:ℕ)) :
    Submission.Cohomology.splitFace h f ≫ (SimplexCategory.δ (⟨(i:ℕ), by omega⟩ : Fin (n+2)))
      = Submission.Cohomology.splitFace h1 (⟨(f:ℕ)+1, by omega⟩ : Fin (P+1)) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Submission.Cohomology.splitFace_apply, val_succAbove]
  rw [Submission.Cohomology.splitFace_apply]
  split_ifs <;> simp_all <;> omega

/-- **Region B** (`i = f + (j+1)`), `u`-component. -/
lemma TB_u {P Q n : ℕ} (h : P + Q = n + 1) (h2 : P + (Q+1) = (n+1) + 1) (f : Fin P) (j : Fin Q) :
    Submission.Cohomology.joinFace h f ≫
        (SimplexCategory.δ (⟨(f:ℕ)+1+(j:ℕ), by omega⟩ : Fin (n+2)))
      = Submission.Cohomology.joinFace h2 f := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [val_succAbove, Submission.Cohomology.joinFace_apply]
  rw [Submission.Cohomology.joinFace_apply]
  split_ifs <;> simp_all <;> omega

/-- **Region B** (`i = f + (j+1)`), `v`-component. -/
lemma TB_v {P Q n : ℕ} (h : P + Q = n + 1) (h2 : P + (Q+1) = (n+1) + 1) (f : Fin P) (j : Fin Q) :
    Submission.Cohomology.splitFace h f ≫
        (SimplexCategory.δ (⟨(f:ℕ)+1+(j:ℕ), by omega⟩ : Fin (n+2)))
      = ((SimplexCategory.δ (⟨(j:ℕ)+1, by omega⟩ : Fin (Q+2))) : ⦋Q⦌ ⟶ ⦋Q+1⦌) ≫
          Submission.Cohomology.splitFace h2 f := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Submission.Cohomology.splitFace_apply, val_succAbove]
  rw [val_succAbove, Submission.Cohomology.splitFace_apply]
  split_ifs <;> simp_all <;> omega

/-- **Region C** (`i = Q + j - 1`), `u`-component. -/
lemma TC_u {P Q n : ℕ} (h : P + Q = n + 1) (h1 : (P+1) + Q = (n+1) + 1) (a : Fin P) (j : Fin (P+2))
    (hj : (a:ℕ)+2 ≤ (j:ℕ)) :
    Submission.Cohomology.joinFace h a ≫
        (SimplexCategory.δ (⟨Q + (j:ℕ) - 1, by omega⟩ : Fin (n+2)))
      = (SimplexCategory.δ j : ⦋P⦌ ⟶ ⦋P+1⦌) ≫
          Submission.Cohomology.joinFace h1 a.castSucc := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [val_succAbove, Submission.Cohomology.joinFace_apply]
  rw [Submission.Cohomology.joinFace_apply, val_succAbove]
  split_ifs <;> simp_all <;> omega

/-- **Region C** (`i = Q + j - 1`), `v`-component. -/
lemma TC_v {P Q n : ℕ} (h : P + Q = n + 1) (h1 : (P+1) + Q = (n+1) + 1) (a : Fin P) (j : Fin (P+2))
    (hj : (a:ℕ)+2 ≤ (j:ℕ)) :
    Submission.Cohomology.splitFace h a ≫
        (SimplexCategory.δ (⟨Q + (j:ℕ) - 1, by omega⟩ : Fin (n+2)))
      = Submission.Cohomology.splitFace h1 a.castSucc := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Submission.Cohomology.splitFace_apply, val_succAbove]
  rw [Submission.Cohomology.splitFace_apply]
  split_ifs <;> simp_all <;> omega

/-- `T3`, component `j' = Q+1`, `u`-part. -/
lemma TL3Q_u {P Q n : ℕ} (h2 : P + (Q+1) = (n+1) + 1) (h1 : (P+1) + Q = (n+1) + 1) (a : Fin P) :
    Submission.Cohomology.joinFace h2 a
      = (SimplexCategory.δ (⟨(a:ℕ)+1, by omega⟩ : Fin (P+2)) : ⦋P⦌ ⟶ ⦋P+1⦌) ≫
          Submission.Cohomology.joinFace h1 a.castSucc := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Submission.Cohomology.joinFace_apply]
  rw [Submission.Cohomology.joinFace_apply, val_succAbove]
  split_ifs <;> simp_all <;> omega

/-- `T3`, component `j' = Q+1`, `v`-part. -/
lemma TL3Q_v {P Q n : ℕ} (h2 : P + (Q+1) = (n+1) + 1) (h1 : (P+1) + Q = (n+1) + 1) (a : Fin P) :
    ((SimplexCategory.δ (⟨Q+1, by omega⟩ : Fin (Q+2))) : ⦋Q⦌ ⟶ ⦋Q+1⦌) ≫
        Submission.Cohomology.splitFace h2 a
      = Submission.Cohomology.splitFace h1 a.castSucc := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Submission.Cohomology.splitFace_apply, val_succAbove]
  rw [Submission.Cohomology.splitFace_apply]
  split_ifs <;> simp_all <;> omega

/-- `T3`, component `j' = 0`, `u`-part. -/
lemma TL3Z_u {P Q n : ℕ} (h2 : P + (Q+1) = (n+1) + 1) (h1 : (P+1) + Q = (n+1) + 1)
    (a : Fin (P+1)) (ha : 1 ≤ (a:ℕ)) :
    Submission.Cohomology.joinFace h2 (⟨(a:ℕ)-1, by omega⟩ : Fin P)
      = (SimplexCategory.δ (⟨(a:ℕ), by omega⟩ : Fin (P+2)) : ⦋P⦌ ⟶ ⦋P+1⦌) ≫
          Submission.Cohomology.joinFace h1 a := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Submission.Cohomology.joinFace_apply]
  rw [Submission.Cohomology.joinFace_apply, val_succAbove]
  split_ifs <;> simp_all <;> omega

/-- `T3`, component `j' = 0`, `v`-part. -/
lemma TL3Z_v {P Q n : ℕ} (h2 : P + (Q+1) = (n+1) + 1) (h1 : (P+1) + Q = (n+1) + 1)
    (a : Fin (P+1)) (ha : 1 ≤ (a:ℕ)) :
    ((SimplexCategory.δ (0 : Fin (Q+2))) : ⦋Q⦌ ⟶ ⦋Q+1⦌) ≫
        Submission.Cohomology.splitFace h2 (⟨(a:ℕ)-1, by omega⟩ : Fin P)
      = Submission.Cohomology.splitFace h1 a := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Submission.Cohomology.splitFace_apply, val_succAbove]
  rw [Submission.Cohomology.splitFace_apply]
  split_ifs <;> simp_all <;> omega

/-- The `u`-argument of the `(v ⌣ u)`-term of the right hand side. -/
lemma R_vu_u {P Q n : ℕ} (h1 : (P+1) + Q = (n+1) + 1) :
    (SimplexCategory.δ (0 : Fin (P+2)) : ⦋P⦌ ⟶ ⦋P+1⦌) ≫
        Submission.Cohomology.joinFace h1 (0 : Fin (P+1))
      = SimplexCategory.subinterval (n := n+1) Q P (by omega) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
  rw [Submission.Cohomology.joinFace_apply, val_succAbove, subinterval_apply]
  split_ifs <;> simp_all <;> omega

/-- The `v`-argument of the `(v ⌣ u)`-term of the right hand side. -/
lemma R_vu_v {P Q n : ℕ} (h1 : (P+1) + Q = (n+1) + 1) :
    Submission.Cohomology.splitFace h1 (0 : Fin (P+1))
      = SimplexCategory.subinterval (n := n+1) 0 Q (by omega) := by
  ext k
  rw [Submission.Cohomology.splitFace_apply, subinterval_apply, Fin.val_zero]
  omega

/-- The `u`-argument of the `(u ⌣ v)`-term of the right hand side. -/
lemma R_uv_u {P Q n : ℕ} (h1 : (P+1) + Q = (n+1) + 1) :
    (SimplexCategory.δ (Fin.last (P+1)) : ⦋P⦌ ⟶ ⦋P+1⦌) ≫
        Submission.Cohomology.joinFace h1 (Fin.last P)
      = SimplexCategory.subinterval (n := n+1) 0 P (by omega) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    SimplexCategory.δ, SimplexCategory.mkHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, Fin.val_last]
  rw [Submission.Cohomology.joinFace_apply, val_succAbove, subinterval_apply]
  split_ifs <;> simp_all <;> omega

/-- The `v`-argument of the `(u ⌣ v)`-term of the right hand side. -/
lemma R_uv_v {P Q n : ℕ} (h1 : (P+1) + Q = (n+1) + 1) :
    Submission.Cohomology.splitFace h1 (Fin.last P)
      = SimplexCategory.subinterval (n := n+1) P Q (by omega) := by
  ext k
  rw [Submission.Cohomology.splitFace_apply, subinterval_apply, Fin.val_last]
  omega


/-- Reindexing a sum over `Fin N` to a sum over `Fin (N+1)` with a zero last term. -/
lemma castSucc_mk {N : ℕ} (a : Fin (N+1)) (h : (a:ℕ) < N) :
    (⟨(a:ℕ), h⟩ : Fin N).castSucc = a := by
  apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_mk]

lemma sum_fin_castSucc_eq {β : Type*} [AddCommMonoid β] {N : ℕ} (g : Fin N → β) :
    (∑ f : Fin N, g f) = ∑ a : Fin (N+1), (if h : (a:ℕ) < N then g ⟨(a:ℕ), h⟩ else 0) := by
  rw [Fin.sum_univ_castSucc (f := fun a : Fin (N+1) =>
      (if h : (a:ℕ) < N then g ⟨(a:ℕ), h⟩ else 0))]
  rw [dif_neg (by simp [Fin.val_last]), add_zero]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [dif_pos (by simpa using f.isLt)]
  congr 1

/-- A sum over `Fin (N+1)` with vanishing `0`-term, `0`-indexed form. -/
lemma sum_fin_succ_eq'' {β : Type*} [AddCommMonoid β] {N : ℕ} (g : Fin (N+1) → β) :
    (∑ f : Fin N, g f.succ) = ∑ a : Fin (N+1), (if a = 0 then 0 else g a) := by
  rw [Fin.sum_univ_succ (f := fun a : Fin (N+1) => if a = 0 then 0 else g a)]
  rw [if_pos rfl, zero_add]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  rw [if_neg (fun h => absurd (congrArg Fin.val h) (by simp))]

/-- A sum of `(if P ∧ j = j₀ then c else 0) • F j` over `j` collapses to its `j₀`-term. -/
lemma sum_ite_zsmul_single {β : Type*} [AddCommGroup β] {N : ℕ} (P : Prop) [Decidable P]
    (j₀ : Fin N) (c : ℤ) (F : Fin N → β) :
    (∑ j : Fin N, (if P ∧ j = j₀ then c else 0) • F j) = (if P then c • F j₀ else 0) := by
  rw [Finset.sum_eq_single j₀ (s := Finset.univ)]
  · by_cases hP : P
    · rw [if_pos hP, if_pos (show P ∧ j₀ = j₀ from ⟨hP, rfl⟩)]
    · rw [if_neg hP, if_neg (show ¬ (P ∧ j₀ = j₀) from fun h => hP h.1), zero_smul]
  · intro j _ hj
    rw [if_neg (show ¬ (P ∧ j = j₀) from fun h => hj h.2), zero_smul]
  · intro hj; exact absurd (Finset.mem_univ j₀) hj

/-- `(-1)^(Y + (2k+1)) = -(-1)^Y`. -/
lemma neg_one_pow_add_odd (Y k : ℕ) : (-1:ℤ)^(Y + (2*k+1)) = -((-1:ℤ)^Y) := by
  rw [pow_add, show (-1:ℤ)^(2*k+1) = -1 by
    rw [pow_succ, show (-1:ℤ)^(2*k) = 1 by
      rw [show 2*k = k+k by ring]
      exact Even.neg_one_pow ⟨k, by ring⟩]
    ring]
  ring

/-- `(-1)^X + (-1)^Y = 0` when `X = Y + (2k+1)`. -/
lemma neg_one_pow_add_eq_zero {X Y : ℕ} (k : ℕ) (h : X = Y + (2*k+1)) :
    (-1:ℤ)^X + (-1:ℤ)^Y = 0 := by
  rw [h, neg_one_pow_add_odd]
  ring

/-- Exponent identity for region A. -/
lemma expA {P Q av jv : ℕ} (hP : av + 1 ≤ P) (hQ : 1 ≤ Q) :
    av + (P + 1 - 1 - av) * Q + jv = ((jv + Q - 1) + (av + (P - 1 - av) * Q)) + 1 := by
  have hP' : P + 1 - 1 - av = P - av := by omega
  have hQ' : jv + Q - 1 = jv + (Q - 1) := by omega
  rw [hP', hQ']
  set c := P - 1 - av with hc
  have hcP : P - av = c + 1 := by omega
  rw [hcP]
  set d := Q - 1 with hd
  have hQd : Q = d + 1 := by omega
  rw [hQd]
  ring

/-- Exponent identity for region `jv = av`, `av < P`. -/
lemma expB {P Q av jv : ℕ} (hP : av < P) (hav : 1 ≤ av) (hj : jv = av) (hQ : 1 ≤ Q) :
    P + ((av - 1) + (P - av) * (Q + 1))
      = (av + (P + 1 - 1 - av) * Q + jv) + (2 * ((P - av) - 1) + 1) := by
  have hP' : P + 1 - 1 - av = P - av := by omega
  rw [hP', hj]
  set c := P - av with hc
  have hc1 : 1 ≤ c := by omega
  have hPc : P = c + av := by omega
  rw [hPc]
  set d := c - 1 with hd
  have hcd : c = d + 1 := by omega
  rw [hcd]
  set e := av - 1 with he
  have hae : av = e + 1 := by omega
  rw [hae]
  ring

/-- Exponent identity for region `jv = av + 1`, `av < P`. -/
lemma expC {P Q av jv : ℕ} (hP : av < P) (hj : jv = av + 1) (hQ : 1 ≤ Q) :
    P + (av + (P - 1 - av) * (Q + 1)) + (Q + 1)
      = (av + (P + 1 - 1 - av) * Q + jv) + (2 * ((P - av) - 1) + 1) := by
  have hsub : P - 1 - av = P - av - 1 := by omega
  have hP' : P + 1 - 1 - av = P - av := by omega
  rw [hsub, hP', hj]
  set c := P - av with hc
  have hc1 : 1 ≤ c := by omega
  have hPc : P = c + av := by omega
  rw [hPc]
  set d := c - 1 with hd
  have hcd : c = d + 1 := by omega
  rw [hcd]
  ring

/-- Region `jv = av + 1`, `av = P`: the `C₂`-coefficient is `-1`. -/
lemma expD {P Q av jv : ℕ} (hP : P = av) (hj : jv = av + 1) :
    (-1:ℤ)^(av + (P + 1 - 1 - av) * Q + jv) = -1 := by
  rw [hP, hj]
  have h1 : av + 1 - 1 - av = 0 := by omega
  rw [h1]
  exact Odd.neg_one_pow ⟨av, by ring⟩

/-- Region `jv = av = 0`: the `C₂`-coefficient is `(-1)^(PQ)`. -/
lemma expE {P Q av jv : ℕ} (hav : av = 0) (hj : jv = 0) :
    av + (P + 1 - 1 - av) * Q + jv = P * Q := by
  rw [hav, hj]
  have h1 : P + 1 - 1 - 0 = P := by omega
  rw [h1]
  ring

/-- Region `jv = av`, `av = P`: the `C₂`-exponent is `2P`. -/
lemma expF {P Q av jv : ℕ} (hP : P = av) (hj : jv = av) :
    av + (P + 1 - 1 - av) * Q + jv = 2 * P := by
  rw [hP, hj]
  have h1 : av + 1 - 1 - av = 0 := by omega
  rw [h1]
  ring

/-- Region `jv = av`, `av = P`: the `C_Z`-exponent is `2P - 1`. -/
lemma expG {P Q av : ℕ} (hP : P = av) (hav : 1 ≤ av) :
    P + ((av - 1) + (P - av) * (Q + 1)) = 2 * P - 1 := by
  rw [hP]
  have h1 : av - av = 0 := by omega
  rw [h1, zero_mul, add_zero]
  omega

/-- `(-1)^Y + (-1)^X = 0` when `X = Y + (2k+1)`. -/
lemma neg_one_pow_add_eq_zero' {X Y : ℕ} (k : ℕ) (h : X = Y + (2*k+1)) :
    (-1:ℤ)^Y + (-1:ℤ)^X = 0 :=
  (add_comm _ _).trans (neg_one_pow_add_eq_zero k h)
theorem cupOne_relation {S : SSet.{0}} {R : Type} [CommRing R] {P Q n : ℕ}
    (h : P + Q = n + 1) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (u : Submission.Cohomology.Cochain S R P) (v : Submission.Cohomology.Cochain S R Q) :
    Submission.Cohomology.coboundary S R n (Submission.Cohomology.cupOneOf S R h u v)
      + Submission.Cohomology.cupOneOf S R (by omega : (P + 1) + Q = (n + 1) + 1)
          (Submission.Cohomology.coboundary S R P u) v
      + (-1 : ℤ) ^ P • Submission.Cohomology.cupOneOf S R (by omega : P + (Q + 1) = (n + 1) + 1)
          u (Submission.Cohomology.coboundary S R Q v)
    = (-1 : ℤ) ^ (P * Q) • Submission.Cohomology.cupOf S R (by omega : Q + P = n + 1) v u
      - Submission.Cohomology.cupOf S R (by omega : P + Q = n + 1) u v := by
  funext σ
  have h1 : (P+1) + Q = (n+1) + 1 := by omega
  have h2 : P + (Q+1) = (n+1) + 1 := by omega
  let uu : (⦋P⦌ ⟶ ⦋n+1⦌) → R := fun φ => u (hom (S.map φ.op) σ)
  let vv : (⦋Q⦌ ⟶ ⦋n+1⦌) → R := fun φ => v (hom (S.map φ.op) σ)
  let T1 : R := ∑ f : Fin P, ∑ i : Fin (n+2), (-1:ℤ)^((i:ℕ)) •
        ((-1:ℤ)^((f:ℕ)+(P-1-(f:ℕ))*Q) •
          (uu (Submission.Cohomology.joinFace h f ≫ SimplexCategory.δ i) *
           vv (Submission.Cohomology.splitFace h f ≫ SimplexCategory.δ i)))
  let T2 : R := ∑ a : Fin (P+1), (-1:ℤ)^((a:ℕ)+(P+1-1-(a:ℕ))*Q) •
        ((∑ j : Fin (P+2), (-1:ℤ)^((j:ℕ)) •
            uu (SimplexCategory.δ j ≫ Submission.Cohomology.joinFace h1 a)) *
         vv (Submission.Cohomology.splitFace h1 a))
  let T3 : R := ∑ f : Fin P, (-1:ℤ)^P • (-1:ℤ)^((f:ℕ)+(P-1-(f:ℕ))*(Q+1)) •
        (uu (Submission.Cohomology.joinFace h2 f) *
         ∑ j : Fin (Q+2), (-1:ℤ)^((j:ℕ)) •
            vv (SimplexCategory.δ j ≫ Submission.Cohomology.splitFace h2 f))
  let RR : R := (-1:ℤ)^(P*Q) •
        (vv (SimplexCategory.subinterval 0 Q (by omega)) *
         uu (SimplexCategory.subinterval Q P (by omega)))
      - uu (SimplexCategory.subinterval 0 P (by omega)) *
        vv (SimplexCategory.subinterval P Q (by omega))
  have hexp : (Submission.Cohomology.coboundary S R n (Submission.Cohomology.cupOneOf S R h u v)
      + Submission.Cohomology.cupOneOf S R (by omega : (P + 1) + Q = (n + 1) + 1)
          (Submission.Cohomology.coboundary S R P u) v
      + (-1 : ℤ) ^ P • Submission.Cohomology.cupOneOf S R
          (by omega : P + (Q + 1) = (n + 1) + 1)
          u (Submission.Cohomology.coboundary S R Q v)) σ = T1 + T2 + T3 := by
    dsimp only [T1, T2, T3, uu, vv]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Submission.Cohomology.coboundary_apply,
      Submission.Cohomology.cupOneOf_apply, Submission.Cohomology.cupOf_apply,
      Submission.Cohomology.frontOf, Submission.Cohomology.backOf, SimplicialObject.δ]
    simp only [mapCompHom]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
  have hRR : ((-1 : ℤ) ^ (P * Q) • Submission.Cohomology.cupOf S R (by omega : Q + P = n + 1) v u
      - Submission.Cohomology.cupOf S R (by omega : P + Q = n + 1) u v) σ = RR := by
    dsimp only [RR, uu, vv]
    simp only [Pi.sub_apply, Pi.smul_apply, Submission.Cohomology.cupOf_apply,
      Submission.Cohomology.frontOf, Submission.Cohomology.backOf]
  rw [hexp, hRR]
  -- split the inner sum of T1
  let T1A : R := ∑ f : Fin P, ∑ i : Fin ((f:ℕ)+1), (-1:ℤ)^((i:ℕ)) •
        ((-1:ℤ)^((f:ℕ)+(P-1-(f:ℕ))*Q) •
          (uu (Submission.Cohomology.joinFace h f ≫
              SimplexCategory.δ (⟨(i:ℕ), by omega⟩ : Fin (n+2))) *
           vv (Submission.Cohomology.splitFace h f ≫
              SimplexCategory.δ (⟨(i:ℕ), by omega⟩ : Fin (n+2)))))
  let T1B : R := ∑ f : Fin P, ∑ j : Fin Q, (-1:ℤ)^(((f:ℕ)+1+(j:ℕ))) •
        ((-1:ℤ)^((f:ℕ)+(P-1-(f:ℕ))*Q) •
          (uu (Submission.Cohomology.joinFace h f ≫
              SimplexCategory.δ (⟨(f:ℕ)+1+(j:ℕ), by omega⟩ : Fin (n+2))) *
           vv (Submission.Cohomology.splitFace h f ≫
              SimplexCategory.δ (⟨(f:ℕ)+1+(j:ℕ), by omega⟩ : Fin (n+2)))))
  let T1C : R := ∑ f : Fin P, ∑ t : Fin (P - (f:ℕ)), (-1:ℤ)^((f:ℕ)+1+(Q+(t:ℕ))) •
        ((-1:ℤ)^((f:ℕ)+(P-1-(f:ℕ))*Q) •
          (uu (Submission.Cohomology.joinFace h f ≫
              SimplexCategory.δ (⟨(f:ℕ)+1+(Q+(t:ℕ)), by omega⟩ : Fin (n+2))) *
           vv (Submission.Cohomology.splitFace h f ≫
              SimplexCategory.δ (⟨(f:ℕ)+1+(Q+(t:ℕ)), by omega⟩ : Fin (n+2)))))
  have hT1 : T1 = T1A + T1B + T1C := by
    dsimp only [T1, T1A, T1B, T1C]
    conv_lhs =>
      enter [2, y]
      rw [sum_univ_split (a := (y:ℕ)+1) (b := Q + (P - (y:ℕ))) (by omega)]
    conv_lhs =>
      enter [2, y]; arg 2
      rw [sum_univ_split (a := Q) (b := P - (y:ℕ)) (by omega)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← add_assoc]
  let T2E : R := ∑ a : Fin (P+1), ∑ i : Fin (a:ℕ),
        (-1:ℤ)^((a:ℕ)+(P+1-1-(a:ℕ))*Q) •
          (((-1:ℤ)^((i:ℕ)) • uu (SimplexCategory.δ (⟨(i:ℕ), by omega⟩ : Fin (P+2)) ≫
              Submission.Cohomology.joinFace h1 a)) *
           vv (Submission.Cohomology.splitFace h1 a))
  let T2L : R := ∑ a : Fin (P+1), ∑ i : Fin (P + 2 - (a:ℕ)),
        (-1:ℤ)^((a:ℕ)+(P+1-1-(a:ℕ))*Q) •
          (((-1:ℤ)^((a:ℕ)+(i:ℕ)) • uu (SimplexCategory.δ (⟨(a:ℕ)+(i:ℕ), by omega⟩ : Fin (P+2)) ≫
              Submission.Cohomology.joinFace h1 a)) *
           vv (Submission.Cohomology.splitFace h1 a))
  have hT2 : T2 = T2E + T2L := by
    dsimp only [T2, T2E, T2L]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.smul_sum]
    conv_lhs =>
      enter [2, x]
      rw [sum_univ_split (a := (x:ℕ)) (b := P + 2 - (x:ℕ)) (by omega)]
    rw [Finset.sum_add_distrib]
  have hinner : ∀ f : Fin P, (∑ j : Fin (Q+2), (-1:ℤ)^((j:ℕ)) •
        vv (SimplexCategory.δ j ≫ Submission.Cohomology.splitFace h2 f))
      = vv (SimplexCategory.δ 0 ≫ Submission.Cohomology.splitFace h2 f)
        + ((∑ j : Fin Q, (-1:ℤ)^((j:ℕ)+1) •
            vv (SimplexCategory.δ (j.succ.castSucc) ≫
              Submission.Cohomology.splitFace h2 f))
          + (-1:ℤ)^(Q+1) • vv (SimplexCategory.δ ((Fin.last Q).succ) ≫
              Submission.Cohomology.splitFace h2 f)) := by
    intro f
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succ_castSucc, Fin.val_succ,
      Fin.val_castSucc, Fin.val_last, Nat.succ_eq_add_one]
  let T3Z : R := ∑ f : Fin P, (-1:ℤ)^P • ((-1:ℤ)^((f:ℕ)+(P-1-(f:ℕ))*(Q+1)) •
        (uu (Submission.Cohomology.joinFace h2 f) *
         vv (SimplexCategory.δ 0 ≫ Submission.Cohomology.splitFace h2 f)))
  let T3M : R := ∑ f : Fin P, (-1:ℤ)^P • ((-1:ℤ)^((f:ℕ)+(P-1-(f:ℕ))*(Q+1)) •
        (uu (Submission.Cohomology.joinFace h2 f) *
         ∑ j : Fin Q, (-1:ℤ)^((j:ℕ)+1) •
            vv (SimplexCategory.δ (j.succ.castSucc) ≫ Submission.Cohomology.splitFace h2 f)))
  let T3Q : R := ∑ f : Fin P, (-1:ℤ)^P • ((-1:ℤ)^((f:ℕ)+(P-1-(f:ℕ))*(Q+1)) •
        (uu (Submission.Cohomology.joinFace h2 f) *
         ((-1:ℤ)^(Q+1) • vv (SimplexCategory.δ ((Fin.last Q).succ) ≫
            Submission.Cohomology.splitFace h2 f))))
  have hT3 : T3 = T3Z + (T3M + T3Q) := by
    dsimp only [T3, T3Z, T3M, T3Q]
    conv_lhs =>
      enter [2, f]
      rw [hinner f]
      simp only [mul_add, smul_add]
    simp only [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hT2E : T2E = ∑ f : Fin P, ∑ i : Fin ((f:ℕ)+1),
        (-1:ℤ)^(((f:ℕ)+1)+(P+1-1-((f:ℕ)+1))*Q) •
          (((-1:ℤ)^((i:ℕ)) • uu (SimplexCategory.δ (⟨(i:ℕ), by omega⟩ : Fin (P+2)) ≫
              Submission.Cohomology.joinFace h1 f.succ)) *
           vv (Submission.Cohomology.splitFace h1 f.succ)) := by
    dsimp only [T2E]
    rw [sum_fin_succ_eq (g := fun a : Fin (P+1) => ∑ i : Fin ((a:ℕ)),
        (-1:ℤ)^((a:ℕ)+(P+1-1-(a:ℕ))*Q) •
          (((-1:ℤ)^((i:ℕ)) • uu (SimplexCategory.δ (⟨(i:ℕ), by omega⟩ : Fin (P+2)) ≫
              Submission.Cohomology.joinFace h1 a)) *
           vv (Submission.Cohomology.splitFace h1 a))) (by
      simp only [Fin.val_zero]
      exact Finset.sum_eq_zero (fun i _ => absurd i.isLt (Nat.not_lt_zero _)))]
    rfl
  have hAE : T1A + T2E = 0 := by
    rw [hT2E, ← Finset.sum_add_distrib]
    conv_lhs => enter [2, f]; rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun f _ => ?_)
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have hi : (i:ℕ) ≤ (f:ℕ) := by have := i.isLt; omega
    have hiP : (i:ℕ) < P + 1 := by have := i.isLt; have := f.isLt; omega
    rw [TA_u h h1 f ⟨(i:ℕ), hiP⟩ hi, TA_v h h1 f ⟨(i:ℕ), hiP⟩ hi]
    simp only [Fin.val_mk, Fin.succ]
    simp only [smul_mul_assoc, smul_smul, ← pow_add]
    rw [show ((f:ℕ)+1+(P+1-1-((f:ℕ)+1))*Q) + (i:ℕ)
          = ((i:ℕ) + ((f:ℕ)+(P-1-(f:ℕ))*Q)) + 1 from by
        have hh : (P+1-1-((f:ℕ)+1)) = (P-1-(f:ℕ)) := by omega
        rw [hh]; ring,
        pow_succ]
    rw [← add_smul,
        show (-1:ℤ)^((i:ℕ) + ((f:ℕ)+(P-1-(f:ℕ))*Q))
              + (-1:ℤ)^((i:ℕ) + ((f:ℕ)+(P-1-(f:ℕ))*Q)) * (-1) = 0 from by ring,
        zero_smul]
  have hT3M : T3M = ∑ f : Fin P, ∑ j : Fin Q,
        (-1:ℤ)^P • ((-1:ℤ)^((f:ℕ)+(P-1-(f:ℕ))*(Q+1)) •
          (uu (Submission.Cohomology.joinFace h2 f) *
           ((-1:ℤ)^((j:ℕ)+1) • vv (SimplexCategory.δ (j.succ.castSucc) ≫
              Submission.Cohomology.splitFace h2 f)))) := by
    dsimp only [T3M]
    simp_rw [Finset.mul_sum, Finset.smul_sum]
  have hBE : T1B + T3M = 0 := by
    rw [hT3M, ← Finset.sum_add_distrib]
    conv_lhs => enter [2, f]; rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun f _ => ?_)
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [TB_u h h2 f j, TB_v h h2 f j, fin_succ_castSucc_eq j]
    rw [mul_smul_comm]
    simp only [smul_smul, ← pow_add]
    rw [← add_smul]
    set fv := (f:ℕ) with hfv
    set c := P - 1 - fv with hc
    have hfvlt : fv < P := by rw [hfv]; exact f.isLt
    have hP : fv + 1 + c = P := by rw [hc]; omega
    rw [show (-1:ℤ)^(P + (fv + c*(Q+1) + (↑j+1)))
          = (-1:ℤ)^(fv+1+↑j + (fv + c*Q)) * (-1) by
      rw [show P + (fv + c*(Q+1) + (↑j+1)) = (fv+1+↑j + (fv+c*Q)) + (1 + 2*c) by
        rw [← hP]; ring,
          pow_add, show (-1:ℤ)^(1 + 2*c) = -1 by
        rw [pow_add, show (-1:ℤ)^(2*c) = 1 by
          rw [show 2*c = c + c by ring]
          exact Even.neg_one_pow ⟨c, by ring⟩]
        norm_num]
      ]
    rw [show (-1:ℤ)^(fv+1+↑j + (fv + c*Q)) + (-1:ℤ)^(fv+1+↑j + (fv + c*Q)) * (-1) = 0 from by ring,
        zero_smul]
  -- The canonical term
  let XX : Fin (P+1) → Fin (P+2) → R := fun a j =>
      uu (SimplexCategory.δ j ≫ Submission.Cohomology.joinFace h1 a) *
      vv (Submission.Cohomology.splitFace h1 a)
  -- Reindex T2L onto the canonical grid.
  have hT2La : T2L = ∑ a : Fin (P+1), ∑ j : Fin (P+2),
      (if (a:ℕ) ≤ (j:ℕ) then
        (-1:ℤ)^(((a:ℕ)+(P+1-1-(a:ℕ))*Q) + (j:ℕ)) else 0) • XX a j := by
    dsimp only [T2L, XX]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    trans ∑ i : Fin (P+2-(a:ℕ)),
        (-1:ℤ)^(((a:ℕ)+(P+1-1-(a:ℕ))*Q) + ((a:ℕ)+(i:ℕ))) •
          (uu (SimplexCategory.δ (⟨(a:ℕ)+(i:ℕ), by omega⟩ : Fin (P+2)) ≫
              Submission.Cohomology.joinFace h1 a) *
           vv (Submission.Cohomology.splitFace h1 a))
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_mul_assoc, smul_smul, ← pow_add]
    · rw [sum_fin_Ici (N := P+2) (a := (a:ℕ)) (by omega)
        (fun j : Fin (P+2) => (-1:ℤ)^(((a:ℕ)+(P+1-1-(a:ℕ))*Q) + (j:ℕ)) •
          (uu (SimplexCategory.δ j ≫ Submission.Cohomology.joinFace h1 a) *
           vv (Submission.Cohomology.splitFace h1 a)))]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hj : (a:ℕ) ≤ (j:ℕ)
      · simp only [if_pos hj]
      · simp only [if_neg hj, zero_smul]
  have hT1Ca : T1C = ∑ a : Fin (P+1), ∑ j : Fin (P+2),
      (if (a:ℕ) < P ∧ (a:ℕ)+2 ≤ (j:ℕ) then
        (-1:ℤ)^(((j:ℕ)+Q-1) + ((a:ℕ)+(P-1-(a:ℕ))*Q)) else 0) • XX a j := by
    dsimp only [T1C, XX]
    rw [sum_fin_castSucc_eq (fun f : Fin P => ∑ t : Fin (P - (f:ℕ)),
        (-1:ℤ)^((f:ℕ)+1+(Q+(t:ℕ))) • ((-1:ℤ)^((f:ℕ)+(P-1-(f:ℕ))*Q) •
          (uu (Submission.Cohomology.joinFace h f ≫
              SimplexCategory.δ (⟨(f:ℕ)+1+(Q+(t:ℕ)), by omega⟩ : Fin (n+2))) *
           vv (Submission.Cohomology.splitFace h f ≫
              SimplexCategory.δ (⟨(f:ℕ)+1+(Q+(t:ℕ)), by omega⟩ : Fin (n+2))))))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases ha : (a:ℕ) < P
    · rw [dif_pos ha]
      simp only [ha, true_and]
      trans ∑ t : Fin (P - (a:ℕ)),
        (-1:ℤ)^(((a:ℕ)+2+(t:ℕ))+Q-1) • ((-1:ℤ)^((a:ℕ)+(P-1-(a:ℕ))*Q) •
          (uu (SimplexCategory.δ (⟨(a:ℕ)+2+(t:ℕ), by omega⟩ : Fin (P+2)) ≫
              Submission.Cohomology.joinFace h1 a) *
           vv (Submission.Cohomology.splitFace h1 a)))
      · refine Finset.sum_congr rfl (fun t _ => ?_)
        have ht1 : (t:ℕ) < P - (a:ℕ) := t.isLt
        have h1t : (a:ℕ)+2+(t:ℕ) < P+2 := by omega
        have hj : (a:ℕ)+2 ≤ (a:ℕ)+2+(t:ℕ) := by omega
        rw [show (⟨(a:ℕ)+1+(Q+(t:ℕ)), by omega⟩ : Fin (n+2)) =
              (⟨Q + ((a:ℕ)+2+(t:ℕ)) - 1, by omega⟩ : Fin (n+2)) from by
            apply Fin.ext; simp only [Fin.val_mk]; omega]
        rw [TC_u h h1 ⟨(a:ℕ), ha⟩ ⟨(a:ℕ)+2+(t:ℕ), h1t⟩ hj,
            TC_v h h1 ⟨(a:ℕ), ha⟩ ⟨(a:ℕ)+2+(t:ℕ), h1t⟩ hj]
        rw [castSucc_mk a ha]
        rw [show (a:ℕ)+1+(Q+(t:ℕ)) = (a:ℕ)+2+(t:ℕ)+Q-1 from by omega]
      · rw [sum_fin_Ici' (N := P+2) (a := (a:ℕ)+2) (b := P - (a:ℕ)) (by omega)
          (fun j : Fin (P+2) => (-1:ℤ)^((j:ℕ)+Q-1) •
            ((-1:ℤ)^((a:ℕ)+(P-1-(a:ℕ))*Q) • XX a j))]
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hj : (a:ℕ)+2 ≤ (j:ℕ)
        · simp only [if_pos hj]
          rw [smul_smul, ← pow_add]
        · simp only [if_neg hj, zero_smul]
    · rw [dif_neg ha]
      symm
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [if_neg (fun hg => ha hg.1), zero_smul]
  have hT3Za : T3Z = ∑ a : Fin (P+1), (if a = 0 then 0 else
      (-1:ℤ)^(P + (((a:ℕ)-1) + (P-(a:ℕ))*(Q+1))) • XX a a.castSucc) := by
    dsimp only [T3Z, XX]
    rw [show (∑ f : Fin P, (-1:ℤ)^P • ((-1:ℤ)^((f:ℕ)+(P-1-(f:ℕ))*(Q+1)) •
          (uu (Submission.Cohomology.joinFace h2 f) *
           vv (SimplexCategory.δ 0 ≫ Submission.Cohomology.splitFace h2 f))))
        = ∑ f : Fin P, (-1:ℤ)^(P + ((↑(f.succ))-1 +
              (P-(↑(f.succ)))*(Q+1))) • XX f.succ f.succ.castSucc from by
      refine Finset.sum_congr rfl (fun f _ => ?_)
      have hid : (⟨↑(f.succ)-1, by simp only [Fin.val_succ]; omega⟩ : Fin P) = f := by
        apply Fin.ext; simp only [Fin.val_mk, Fin.val_succ]; omega
      conv_lhs => rw [← hid]
      rw [TL3Z_u h2 h1 f.succ (by simp only [Fin.val_succ]; omega),
          TL3Z_v h2 h1 f.succ (by simp only [Fin.val_succ]; omega)]
      rw [smul_smul, ← pow_add]
      simp only [Fin.val_mk]
      rw [show P-1-((↑(f.succ))-1) = P - (↑(f.succ)) from by
        simp only [Fin.val_succ]; omega]
      rfl]
    rw [show (∑ f : Fin P, (-1:ℤ)^(P + ((↑(f.succ))-1 +
            (P-(↑(f.succ)))*(Q+1))) • XX f.succ f.succ.castSucc)
        = ∑ a : Fin (P+1), (if a = 0 then 0 else
            (-1:ℤ)^(P + (((a:ℕ)-1) + (P-(a:ℕ))*(Q+1))) • XX a a.castSucc)
        from sum_fin_succ_eq'' (fun a : Fin (P+1) =>
          (-1:ℤ)^(P + (((a:ℕ)-1) + (P-(a:ℕ))*(Q+1))) • XX a a.castSucc)]
  have hT3Za2 : T3Z = ∑ a : Fin (P+1), ∑ j : Fin (P+2),
      (if a ≠ 0 ∧ j = a.castSucc then
        (-1:ℤ)^(P + (((a:ℕ)-1) + (P-(a:ℕ))*(Q+1))) else 0) • XX a j := by
    rw [hT3Za]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [sum_ite_zsmul_single (a ≠ 0) a.castSucc
        ((-1:ℤ)^(P + (((a:ℕ)-1) + (P-(a:ℕ))*(Q+1)))) (fun j => XX a j)]
    by_cases ha : a = 0 <;> simp [ha]
  have hT3Qa : T3Q = ∑ a : Fin (P+1), ∑ j : Fin (P+2),
      (if (a:ℕ) < P ∧ j = a.succ then
        (-1:ℤ)^(P + ((a:ℕ)+(P-1-(a:ℕ))*(Q+1)) + (Q+1)) else 0) • XX a j := by
    dsimp only [T3Q, XX]
    rw [show (∑ f : Fin P, (-1:ℤ)^P • ((-1:ℤ)^((f:ℕ)+(P-1-(f:ℕ))*(Q+1)) •
          (uu (Submission.Cohomology.joinFace h2 f) *
           ((-1:ℤ)^(Q+1) • vv (SimplexCategory.δ ((Fin.last Q).succ) ≫
              Submission.Cohomology.splitFace h2 f)))))
        = ∑ f : Fin P, (-1:ℤ)^(P + ((f:ℕ)+(P-1-(f:ℕ))*(Q+1)) + (Q+1)) •
            XX f.castSucc f.castSucc.succ from by
      refine Finset.sum_congr rfl (fun f _ => ?_)
      rw [TL3Q_u h2 h1 f]
      rw [← show ((SimplexCategory.δ (⟨Q+1, by omega⟩ : Fin (Q+2))) : ⦋Q⦌ ⟶ ⦋Q+1⦌) =
          ((SimplexCategory.δ ((Fin.last Q).succ)) : ⦋Q⦌ ⟶ ⦋Q+1⦌) from by
            congr 1]
      rw [TL3Q_v h2 h1 f]
      simp only [mul_smul_comm, smul_smul, ← pow_add]
      rw [show P + ((f:ℕ) + (P-1-(f:ℕ))*(Q+1) + (Q+1)) =
          (P + ((f:ℕ) + (P-1-(f:ℕ))*(Q+1))) + (Q+1) from by ring]
      rfl]
    rw [show (∑ f : Fin P, (-1:ℤ)^(P + ((f:ℕ)+(P-1-(f:ℕ))*(Q+1)) + (Q+1)) •
            XX f.castSucc f.castSucc.succ)
        = ∑ a : Fin (P+1), (if h : (a:ℕ) < P then
            (-1:ℤ)^(P + ((a:ℕ)+(P-1-(a:ℕ))*(Q+1)) + (Q+1)) •
              XX a a.succ else 0) from by
      rw [sum_fin_castSucc_eq (fun f : Fin P =>
          (-1:ℤ)^(P + ((f:ℕ)+(P-1-(f:ℕ))*(Q+1)) + (Q+1)) •
            XX f.castSucc f.castSucc.succ)]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      by_cases ha : (a:ℕ) < P
      · simp only [dif_pos ha, if_pos ha, castSucc_mk a ha]
      · simp only [dif_neg ha, if_neg ha]]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [sum_ite_zsmul_single ((a:ℕ) < P) a.succ
        ((-1:ℤ)^(P + ((a:ℕ)+(P-1-(a:ℕ))*(Q+1)) + (Q+1))) (fun j => XX a j)]
    by_cases ha : (a:ℕ) < P
    · simp only [dif_pos ha, if_pos ha]
    · simp only [dif_neg ha, if_neg ha]

  let cf : Fin (P+1) → Fin (P+2) → ℤ := fun a j =>
      (if (a:ℕ) ≤ (j:ℕ) then
        (-1:ℤ)^(((a:ℕ)+(P+1-1-(a:ℕ))*Q) + (j:ℕ)) else 0)
    + (if (a:ℕ) < P ∧ (a:ℕ)+2 ≤ (j:ℕ) then
        (-1:ℤ)^(((j:ℕ)+Q-1) + ((a:ℕ)+(P-1-(a:ℕ))*Q)) else 0)
    + (if a ≠ 0 ∧ j = a.castSucc then
        (-1:ℤ)^(P + (((a:ℕ)-1) + (P-(a:ℕ))*(Q+1))) else 0)
    + (if (a:ℕ) < P ∧ j = a.succ then
        (-1:ℤ)^(P + ((a:ℕ)+(P-1-(a:ℕ))*(Q+1)) + (Q+1)) else 0)
  have hcomb : T1C + T2L + T3Z + T3Q
      = ∑ a : Fin (P+1), ∑ j : Fin (P+2), cf a j • XX a j := by
    rw [hT1Ca, hT2La, hT3Za2, hT3Qa]
    simp only [cf, add_smul]
    simp only [Finset.sum_add_distrib]
    abel

  have hcast : ∀ a : Fin (P+1), ∀ j : Fin (P+2), (j = a.castSucc) ↔ ((j:ℕ) = (a:ℕ)) := by
    intro a j; constructor
    · intro h; rw [h]; rfl
    · intro h; exact Fin.ext h
  have hsucc : ∀ a : Fin (P+1), ∀ j : Fin (P+2), (j = a.succ) ↔ ((j:ℕ) = (a:ℕ)+1) := by
    intro a j; constructor
    · intro h; rw [h]; simp only [Fin.val_succ]
    · intro h; exact Fin.ext (by simpa only [Fin.val_succ] using h)
  have hcf_eq : ∀ a j, cf a j = (if (a:ℕ) = 0 ∧ (j:ℕ) = 0 then (-1:ℤ)^(P*Q)
      else if (a:ℕ) = P ∧ (j:ℕ) = P+1 then -1 else 0) := by
    intro a j
    have hc1 := hcast a j
    have hc2 := hsucc a j
    have hz : (a ≠ 0) ↔ ((a:ℕ) ≠ 0) := (not_congr (Fin.val_eq_zero_iff (a := a))).symm
    simp only [cf, hc1, hc2, hz]
    set av := (a:ℕ) with hav
    set jv := (j:ℕ) with hjv
    have havP : av < P + 1 := by rw [hav]; exact a.isLt
    have hjvP : jv < P + 2 := by rw [hjv]; exact j.isLt
    by_cases hlt : jv < av
    · have hg2 : ¬ (av ≤ jv) := by omega
      have hg1 : ¬ (av < P ∧ av + 2 ≤ jv) := by omega
      have hgZ : ¬ (av ≠ 0 ∧ jv = av) := by omega
      have hgQ : ¬ (av < P ∧ jv = av + 1) := by omega
      rw [if_neg hg2, if_neg hg1, if_neg hgZ, if_neg hgQ,
        if_neg (by omega : ¬ (av = 0 ∧ jv = 0)),
        if_neg (by omega : ¬ (av = P ∧ jv = P + 1))]
      simp only [add_zero, zero_add]
    · have hle : av ≤ jv := by omega
      rw [if_pos hle]
      by_cases heq : jv = av
      · have hg1 : ¬ (av < P ∧ av + 2 ≤ jv) := by omega
        have hgQ : ¬ (av < P ∧ jv = av + 1) := by omega
        rw [if_neg hg1, if_neg hgQ]
        by_cases hA0 : av = 0
        · rw [if_neg (by omega : ¬ (av ≠ 0 ∧ jv = av)),
            if_pos (by omega : av = 0 ∧ jv = 0)]
          rw [expE hA0 (by omega : jv = 0)]
          simp only [add_zero, zero_add]
        · rw [if_pos (by omega : av ≠ 0 ∧ jv = av),
            if_neg (by omega : ¬ (av = 0 ∧ jv = 0)),
            if_neg (by omega : ¬ (av = P ∧ jv = P + 1))]
          by_cases hAP : av = P
          · have hPE : P = av := by omega
            have hEZ : P + ((av - 1) + (P - av) * (Q + 1)) = 2 * P - 1 :=
              expG hPE (by omega : 1 ≤ av)
            have key : (-1:ℤ)^(av + (P + 1 - 1 - av) * Q + jv)
                + (-1:ℤ)^(P + ((av - 1) + (P - av) * (Q + 1))) = 0 := by
              rw [expF hPE heq, hEZ]
              exact neg_one_pow_add_eq_zero 0 (by omega : 2 * P = 2 * P - 1 + (2 * 0 + 1))
            simp only [add_zero, zero_add]
            exact key
          · have hlt' : av < P := by omega
            have hEZ : P + ((av - 1) + (P - av) * (Q + 1))
                = (av + (P + 1 - 1 - av) * Q + jv) + (2 * ((P - av) - 1) + 1) :=
              expB hlt' (by omega : 1 ≤ av) heq hQ
            have key : (-1:ℤ)^(av + (P + 1 - 1 - av) * Q + jv)
                + (-1:ℤ)^(P + ((av - 1) + (P - av) * (Q + 1))) = 0 := by
              rw [hEZ]
              exact neg_one_pow_add_eq_zero' ((P - av) - 1) rfl
            simp only [add_zero, zero_add]
            exact key
      · by_cases heq1 : jv = av + 1
        · have hg1 : ¬ (av < P ∧ av + 2 ≤ jv) := by omega
          have hgZ : ¬ (av ≠ 0 ∧ jv = av) := by omega
          rw [if_neg hg1, if_neg hgZ]
          by_cases hAP : av = P
          · have hPE : P = av := by omega
            rw [if_neg (by omega : ¬ (av < P ∧ jv = av + 1)),
              if_neg (by omega : ¬ (av = 0 ∧ jv = 0)),
              if_pos (by omega : av = P ∧ jv = P + 1)]
            simp only [add_zero, zero_add]
            exact expD hPE heq1
          · have hlt' : av < P := by omega
            rw [if_pos (by omega : av < P ∧ jv = av + 1),
              if_neg (by omega : ¬ (av = 0 ∧ jv = 0)),
              if_neg (by omega : ¬ (av = P ∧ jv = P + 1))]
            have hEQ : P + (av + (P - 1 - av) * (Q + 1)) + (Q + 1)
                = (av + (P + 1 - 1 - av) * Q + jv) + (2 * ((P - av) - 1) + 1) :=
              expC hlt' heq1 hQ
            have key : (-1:ℤ)^(av + (P + 1 - 1 - av) * Q + jv)
                + (-1:ℤ)^(P + (av + (P - 1 - av) * (Q + 1)) + (Q + 1)) = 0 := by
              rw [hEQ]
              exact neg_one_pow_add_eq_zero' ((P - av) - 1) rfl
            simp only [add_zero, zero_add]
            exact key
        · have hge : av + 2 ≤ jv := by omega
          have hgZ : ¬ (av ≠ 0 ∧ jv = av) := by omega
          have hgQ : ¬ (av < P ∧ jv = av + 1) := by omega
          rw [if_pos (by omega : av < P ∧ av + 2 ≤ jv), if_neg hgZ, if_neg hgQ,
            if_neg (by omega : ¬ (av = 0 ∧ jv = 0)),
            if_neg (by omega : ¬ (av = P ∧ jv = P + 1))]
          have hE1 : av + (P + 1 - 1 - av) * Q + jv
              = ((jv + Q - 1) + (av + (P - 1 - av) * Q)) + 1 :=
            expA (by omega : av + 1 ≤ P) hQ
          have key : (-1:ℤ)^(av + (P + 1 - 1 - av) * Q + jv)
              + (-1:ℤ)^((jv + Q - 1) + (av + (P - 1 - av) * Q)) = 0 := by
            rw [hE1]
            exact neg_one_pow_add_eq_zero 0 rfl
          simp only [add_zero, zero_add]
          exact key
  have hcf_fin : ∀ a j, cf a j = (if a = 0 ∧ j = 0 then (-1:ℤ)^(P*Q)
      else if a = Fin.last P ∧ j = Fin.last (P+1) then (-1:ℤ) else 0) := by
    intro a j
    rw [hcf_eq a j]
    have hz1 : ((a:ℕ) = 0) ↔ (a = 0) := Fin.val_eq_zero_iff
    have hz2 : ((j:ℕ) = 0) ↔ (j = 0) := Fin.val_eq_zero_iff
    have hl1 : ((a:ℕ) = P) ↔ (a = Fin.last P) := by
      constructor
      · intro hh; exact Fin.ext (by rw [hh, Fin.val_last])
      · intro hh; rw [hh, Fin.val_last]
    have hl2 : ((j:ℕ) = P + 1) ↔ (j = Fin.last (P+1)) := by
      constructor
      · intro hh; exact Fin.ext (by rw [hh, Fin.val_last])
      · intro hh; rw [hh, Fin.val_last]
    simp only [hz1, hz2, hl1, hl2]
  have hsum : (∑ a : Fin (P+1), ∑ j : Fin (P+2), cf a j • XX a j)
      = (-1:ℤ)^(P*Q) • XX 0 0 + (-1:ℤ) • XX (Fin.last P) (Fin.last (P+1)) := by
    simp only [hcf_fin]
    have hinner : ∀ a : Fin (P+1),
        (∑ j : Fin (P+2), (if a = 0 ∧ j = 0 then (-1:ℤ)^(P*Q)
            else if a = Fin.last P ∧ j = Fin.last (P+1) then (-1:ℤ) else 0) • XX a j)
          = (if a = 0 then (-1:ℤ)^(P*Q) • XX 0 0
             else if a = Fin.last P then (-1:ℤ) • XX (Fin.last P) (Fin.last (P+1))
             else 0) := by
      intro a
      by_cases ha0 : a = 0
      · subst ha0
        have hne : ¬ ((0 : Fin (P+1)) = Fin.last P) := by
          intro hc
          have hv := congrArg Fin.val hc
          simp only [Fin.val_zero, Fin.val_last] at hv
          omega
        rw [if_pos rfl]
        rw [Finset.sum_eq_single (0 : Fin (P+2))]
        · rw [if_pos (show (0 : Fin (P+1)) = 0 ∧ (0 : Fin (P+2)) = 0 from ⟨rfl, rfl⟩)]
        · intro b _ hb
          rw [if_neg (show ¬ ((0 : Fin (P+1)) = 0 ∧ b = 0) from fun hh => hb hh.2),
              if_neg (show ¬ ((0 : Fin (P+1)) = Fin.last P ∧ b = Fin.last (P+1))
                from fun hh => hne hh.1),
              zero_smul]
        · intro hh; exact absurd (Finset.mem_univ _) hh
      · rw [if_neg ha0]
        by_cases haP : a = Fin.last P
        · rw [if_pos haP]
          rw [Finset.sum_eq_single (Fin.last (P+1))]
          · rw [if_neg (show ¬ (a = 0 ∧ Fin.last (P+1) = 0) from fun hh => ha0 hh.1),
                if_pos (show a = Fin.last P ∧ Fin.last (P+1) = Fin.last (P+1) from ⟨haP, rfl⟩)]
            rw [haP]
          · intro b _ hb
            rw [if_neg (show ¬ (a = 0 ∧ b = 0) from fun hh => ha0 hh.1),
                if_neg (show ¬ (a = Fin.last P ∧ b = Fin.last (P+1)) from fun hh => hb hh.2),
                zero_smul]
          · intro hh; exact absurd (Finset.mem_univ _) hh
        · rw [if_neg haP]
          refine Finset.sum_eq_zero (fun j _ => ?_)
          rw [if_neg (show ¬ (a = 0 ∧ j = 0) from fun hh => ha0 hh.1),
              if_neg (show ¬ (a = Fin.last P ∧ j = Fin.last (P+1)) from fun hh => haP hh.1),
              zero_smul]
    rw [Finset.sum_congr rfl (fun a _ => hinner a)]
    have hsplit : ∀ a : Fin (P+1),
        (if a = 0 then (-1:ℤ)^(P*Q) • XX 0 0
          else if a = Fin.last P then (-1:ℤ) • XX (Fin.last P) (Fin.last (P+1)) else 0)
        = (if a = 0 then (-1:ℤ)^(P*Q) • XX 0 0 else 0)
          + (if a = Fin.last P then (-1:ℤ) • XX (Fin.last P) (Fin.last (P+1))
             else 0) := by
      intro a
      by_cases ha0 : a = 0
      · have hne : ¬ (a = Fin.last P) := by
          rw [ha0]
          intro hc
          have hv := congrArg Fin.val hc
          simp only [Fin.val_zero, Fin.val_last] at hv
          omega
        simp only [if_pos ha0, if_neg hne, add_zero]
      · simp only [if_neg ha0]
        by_cases haP : a = Fin.last P
        · simp only [if_pos haP, zero_add]
        · simp only [if_neg haP, add_zero]
    rw [Finset.sum_congr rfl (fun a _ => hsplit a)]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (P+1))
      (fun _ => (-1:ℤ)^(P*Q) • XX 0 0)]
    rw [Finset.sum_ite_eq' Finset.univ (Fin.last P)
      (fun _ => (-1:ℤ) • XX (Fin.last P) (Fin.last (P+1)))]
    simp only [Finset.mem_univ, if_true]
  have hXX0 : XX 0 0 = uu (SimplexCategory.subinterval (n := n+1) Q P (by omega))
      * vv (SimplexCategory.subinterval (n := n+1) 0 Q (by omega)) := by
    dsimp only [XX]
    rw [R_vu_u h1, R_vu_v h1]
  have hXXl : XX (Fin.last P) (Fin.last (P+1))
      = uu (SimplexCategory.subinterval (n := n+1) 0 P (by omega))
        * vv (SimplexCategory.subinterval (n := n+1) P Q (by omega)) := by
    dsimp only [XX]
    rw [R_uv_u h1, R_uv_v h1]
  rw [hT1, hT2, hT3]
  rw [show T1A + T1B + T1C + (T2E + T2L) + (T3Z + (T3M + T3Q))
      = (T1A + T2E) + (T1B + T3M) + (T1C + T2L + T3Z + T3Q) from by abel]
  rw [hAE, hBE, hcomb, hsum]
  rw [hXX0, hXXl]
  rw [show uu (SimplexCategory.subinterval (n := n+1) Q P (by omega))
        * vv (SimplexCategory.subinterval (n := n+1) 0 Q (by omega))
      = vv (SimplexCategory.subinterval (n := n+1) 0 Q (by omega))
        * uu (SimplexCategory.subinterval (n := n+1) Q P (by omega)) from mul_comm _ _]
  dsimp only [RR]
  simp only [zero_add, add_zero, neg_one_smul ℤ, sub_eq_add_neg]

end Work.Cohomology
