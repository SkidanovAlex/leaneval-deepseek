import Mathlib
import Submission.Work.Cohomology.AlexanderWhitney

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Leibniz rule for the Alexander–Whitney cup product

This file proves the Leibniz (product) rule for the Alexander–Whitney cup product on the
cochain complex of a simplicial set:
`δ(α ⌣ β) = (δα) ⌣ β + (-1)^n α ⌣ (δβ)`,
where `α` has degree `n` and `β` has degree `m`.  The proof is the standard one, carried out on
generators of the simplicial chains: evaluating at an `(n+m+1)`-simplex `σ` splits the sum of
`(-1)^k (α⌣β)(∂_k σ)` into the faces with `k ≤ n` and those with `k ≥ n+1`, which match,
respectively, the faces of the front `(n+1)`-face and the last `m+2` vertices, the two remaining
terms cancelling.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {R : Type} [CommRing R] {X : SSet}

/-! ## Value lemmas for the simplex-category maps -/

@[simp]
lemma hom_frontIncl_val (p n : ℕ) (h : p ≤ n) (j : Fin (p+1)) :
    ((ConcreteCategory.hom (frontIncl p n h)) j).val = j.val := rfl

@[simp]
lemma hom_backIncl_val (p q : ℕ) (j : Fin (q+1)) :
    ((ConcreteCategory.hom (backIncl p q)) j).val = p + j.val := rfl

lemma coe_eqToHom_mk {a b : ℕ} (h : a = b) (i : Fin (⦋a⦌.len+1)) :
    ((ConcreteCategory.hom (eqToHom (congrArg SimplexCategory.mk h))) i).val = i.val := by
  cases h; simp

lemma coe_eqToHom_mk_symm {a b : ℕ} (h : a = b) (i : Fin (⦋b⦌.len+1)) :
    ((ConcreteCategory.hom (eqToHom (congrArg SimplexCategory.mk h).symm)) i).val = i.val := by
  cases h; simp

/-- Composition rule for the contravariant action of `X` on morphisms. -/
lemma map_op_comp {a b c : ℕ} (φ : ⦋a⦌ ⟶ ⦋b⦌) (ψ : ⦋c⦌ ⟶ ⦋a⦌) (x : X _⦋b⦌) :
    X.map ψ.op (X.map φ.op x) = X.map (ψ ≫ φ).op x := by
  rw [← CategoryTheory.comp_apply (X.map φ.op) (X.map ψ.op) x, ← Functor.map_comp, ← op_comp]

/-! ## Identities in `SimplexCategory` -/

lemma S1 (n m : ℕ) (i : Fin (n+m+2)) (hi : (i:ℕ) ≤ n) :
    frontIncl n (n+m) (by omega) ≫ SimplexCategory.δ i
    = (SimplexCategory.δ (n := n) ⟨i.val, by omega⟩) ≫
        frontIncl (n+1) (n+m+1) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Fin.succAbove]
  split_ifs <;> (simp only [Fin.val_castSucc, Fin.val_succ, hom_frontIncl_val, Fin.lt_def] at *; try omega)

lemma S3 (n m : ℕ) (i : Fin (n+m+2)) (hi : (i:ℕ) ≥ n+1) :
    frontIncl n (n+m) (by omega) ≫ SimplexCategory.δ i = frontIncl n (n+(m+1)) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Fin.succAbove]
  split_ifs <;> (simp only [Fin.val_castSucc, Fin.val_succ, hom_frontIncl_val, Fin.lt_def] at *; try omega)

lemma S4 (n m : ℕ) (i : Fin (n+m+2)) (hi : (i:ℕ) ≥ n+1) (j : Fin (m+2))
    (hj : (j:ℕ) = i.val - n) :
    backIncl n m ≫ SimplexCategory.δ i = SimplexCategory.δ j ≫ backIncl n (m+1) := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Fin.succAbove]
  split_ifs <;> (simp only [Fin.val_castSucc, Fin.val_succ, hom_backIncl_val, Fin.lt_def] at *; try omega)

lemma S5 (n m : ℕ) (j : Fin (n+2)) (hj : (j:ℕ) = n+1) :
    SimplexCategory.δ j ≫ frontIncl (n+1) (n+m+1) (by omega)
      = frontIncl n (n+(m+1)) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun k ↦ ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Fin.succAbove]
  split_ifs <;> (simp only [Fin.val_castSucc, Fin.val_succ, hom_frontIncl_val, Fin.lt_def] at *; try omega)

lemma S2 (n m : ℕ) (k : Fin (n+m+2)) (hk : (k:ℕ) ≤ n)
    (H : ⦋n+1+m⦌ ⟶ ⦋n+m+1⦌) (hH : ∀ i, ((ConcreteCategory.hom H) i).val = i.val) :
    backIncl n m ≫ SimplexCategory.δ k = backIncl (n+1) m ≫ H := by
  refine ConcreteCategory.hom_ext _ _ (fun t ↦ ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Fin.succAbove]
  split_ifs <;> (simp only [Fin.val_castSucc, Fin.val_succ, hom_backIncl_val, Fin.lt_def, hH] at *; try omega)

lemma S6 (n m : ℕ) (j : Fin (m+2)) (hj : (j:ℕ) = 0)
    (H : ⦋n+1+m⦌ ⟶ ⦋n+m+1⦌) (hH : ∀ i, ((ConcreteCategory.hom H) i).val = i.val) :
    SimplexCategory.δ j ≫ backIncl n (m+1) = backIncl (n+1) m ≫ H := by
  refine ConcreteCategory.hom_ext _ _ (fun t ↦ ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, SimplexCategory.coe_δ, Fin.succAbove]
  split_ifs <;> (simp only [Fin.val_castSucc, Fin.val_succ, hom_backIncl_val, Fin.lt_def, hH] at *; try omega)

lemma S7 (n m : ℕ) (H : ⦋n+1+m⦌ ⟶ ⦋n+m+1⦌)
    (hH : ∀ i, ((ConcreteCategory.hom H) i).val = i.val) :
    frontIncl (n+1) (n+1+m) (by omega) ≫ H = frontIncl (n+1) (n+m+1) (by omega) := by
  refine ConcreteCategory.hom_ext _ _ (fun t ↦ ?_)
  apply Fin.ext
  simp only [CategoryTheory.comp_apply, hH, hom_frontIncl_val]

/-! ## Face identities for simplices -/

lemma E1 (n m : ℕ) (i : Fin (n+m+2)) (hi : (i:ℕ) ≤ n) (σ : X _⦋n+m+1⦌) :
    frontFace X n (n+m) (by omega) (X.δ i σ)
    = X.δ (⟨i.val, by omega⟩ : Fin (n+2)) (frontFace X (n+1) (n+m+1) (by omega) σ) := by
  simp only [frontFace, SimplicialObject.δ_def]
  rw [map_op_comp, S1 n m i hi, ← map_op_comp]

lemma E2 (n m : ℕ) (k : Fin (n+m+2)) (hk : (k:ℕ) ≤ n)
    (H : ⦋n+1+m⦌ ⟶ ⦋n+m+1⦌) (hH : ∀ i, ((ConcreteCategory.hom H) i).val = i.val)
    (σ : X _⦋n+m+1⦌) :
    backFace X n m (X.δ k σ) = backFace X (n+1) m (X.map H.op σ) := by
  simp only [backFace, SimplicialObject.δ_def]
  rw [map_op_comp, S2 n m k hk H hH, ← map_op_comp]

lemma E3 (n m : ℕ) (k : Fin (n+m+2)) (hk : (k:ℕ) ≥ n+1) (σ : X _⦋n+m+1⦌) :
    frontFace X n (n+m) (by omega) (X.δ k σ) = frontFace X n (n+(m+1)) (by omega) σ := by
  simp only [frontFace, SimplicialObject.δ_def]
  rw [map_op_comp, S3 n m k hk]

lemma E4 (n m : ℕ) (k : Fin (n+m+2)) (hk : (k:ℕ) ≥ n+1) (j : Fin (m+2))
    (hj : (j:ℕ) = k.val - n) (σ : X _⦋n+m+1⦌) :
    backFace X n m (X.δ k σ) = X.δ j (backFace X n (m+1) σ) := by
  simp only [backFace, SimplicialObject.δ_def]
  rw [map_op_comp, S4 n m k hk j hj, ← map_op_comp]

lemma E5 (n m : ℕ) (j : Fin (n+2)) (hj : (j:ℕ) = n+1) (σ : X _⦋n+m+1⦌) :
    X.δ j (frontFace X (n+1) (n+m+1) (by omega) σ) = frontFace X n (n+(m+1)) (by omega) σ := by
  simp only [frontFace, SimplicialObject.δ_def]
  rw [map_op_comp, S5 n m j hj]

lemma E6 (n m : ℕ) (j : Fin (m+2)) (hj : (j:ℕ) = 0)
    (H : ⦋n+1+m⦌ ⟶ ⦋n+m+1⦌) (hH : ∀ i, ((ConcreteCategory.hom H) i).val = i.val)
    (σ : X _⦋n+m+1⦌) :
    X.δ j (backFace X n (m+1) σ) = backFace X (n+1) m (X.map H.op σ) := by
  simp only [backFace, SimplicialObject.δ_def]
  rw [map_op_comp, S6 n m j hj H hH, ← map_op_comp]

lemma E7 (n m : ℕ) (H : ⦋n+1+m⦌ ⟶ ⦋n+m+1⦌)
    (hH : ∀ i, ((ConcreteCategory.hom H) i).val = i.val) (σ : X _⦋n+m+1⦌) :
    frontFace X (n+1) (n+1+m) (by omega) (X.map H.op σ)
      = frontFace X (n+1) (n+m+1) (by omega) σ := by
  simp only [frontFace]
  rw [map_op_comp, S7 n m H hH]

/-! ## `genEval` lemmas -/

lemma frontFace_proof_irrel (p N : ℕ) (h1 h2 : p ≤ N) (τ : X _⦋N⦌) :
    frontFace X p N h1 τ = frontFace X p N h2 τ := by
  simp only [frontFace]

/-- The cup product evaluated at a generator, with the front-face proof in a canonical form. -/
lemma cup_apply' {n m : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) (σ : X _⦋n+m⦌) :
    genEval R X (cup R X α β) σ
      = genEval R X α (frontFace X n (n+m) (by omega) σ) * genEval R X β (backFace X n m σ) := by
  rw [cup_apply, frontFace_proof_irrel n (n+m) _ (by omega) σ]

lemma genEval_add {k : ℕ} (f g : (X.chainComplex (ModuleCat.of R R)).X k →ₗ[R] R)
    (σ : X _⦋k⦌) :
    genEval R X (f + g) σ = genEval R X f σ + genEval R X g σ := by
  simp only [genEval, LinearMap.add_apply]

lemma genEval_smul {k : ℕ} (c : R) (f : (X.chainComplex (ModuleCat.of R R)).X k →ₗ[R] R)
    (σ : X _⦋k⦌) :
    genEval R X (c • f) σ = c • genEval R X f σ := by
  simp only [genEval, LinearMap.smul_apply]

section
set_option backward.isDefEq.respectTransparency false

/-- Linear functionals on the `k`-chains which agree on all generators are equal. -/
lemma genEval_ext {k : ℕ} {f g : (X.chainComplex (ModuleCat.of R R)).X k →ₗ[R] R}
    (h : ∀ σ : X _⦋k⦌, genEval R X f σ = genEval R X g σ) : f = g := by
  have key : (ModuleCat.ofHom f : (X.chainComplex (ModuleCat.of R R)).X k ⟶ ModuleCat.of R R)
      = (ModuleCat.ofHom g : (X.chainComplex (ModuleCat.of R R)).X k ⟶ ModuleCat.of R R) := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    have hc : (X.ιChainComplex (R := ModuleCat.of R R) σ).hom c
        = c • (X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1 := by
      simpa using LinearMap.map_smul (X.ιChainComplex (R := ModuleCat.of R R) σ).hom c (1 : R)
    have h' : f ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
        = g ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) := h σ
    rw [hc, map_smul, map_smul, h']
  simpa only [ModuleCat.hom_ofHom] using congrArg ModuleCat.Hom.hom key

end

/-- The coboundary of a cochain, evaluated on a generator, is the alternating sum of its values
on the faces. -/
lemma genEval_cochainDiff {k : ℕ} (γ : (X.chainComplex (ModuleCat.of R R)).X k →ₗ[R] R)
    (σ : X _⦋k+1⦌) :
    genEval R X (cochainDiff R X γ) σ =
      ∑ i : Fin (k+2), (-1 : R) ^ (i:ℕ) * genEval R X γ (X.δ i σ) := by
  rw [genEval, cochainDiff, LinearMap.comp_apply]
  have h := congrArg
    (fun (g : ModuleCat.of R R ⟶ (X.chainComplex (ModuleCat.of R R)).X k) => g.hom 1)
    (SSet.ιChainComplex_d X (ModuleCat.of R R) σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, map_sum, ModuleCat.hom_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [genEval]
  rw [LinearMap.smul_apply]
  first | rw [map_zsmul] | rw [map_smul]
  try rw [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  try rw [smul_eq_mul]

/-! ## Transporting along the index identification `(n+1)+m = n+m+1` -/

/-- The identification `⦋n+1+m⦌ → ⦋n+m+1⦌` used to compare the two degrees. -/
def shiftHom (n m : ℕ) : ⦋n+1+m⦌ ⟶ ⦋n+m+1⦌ :=
  eqToHom (congrArg SimplexCategory.mk (Nat.add_right_comm n 1 m).symm).symm

lemma shiftHom_val (n m : ℕ) (i : Fin (⦋n+1+m⦌.len+1)) :
    ((ConcreteCategory.hom (shiftHom n m)) i).val = i.val :=
  coe_eqToHom_mk_symm (Nat.add_right_comm n 1 m).symm i

lemma cast_linearMap_apply {M : ℕ → ModuleCat R} {a b : ℕ} (h : a = b)
    (f : (↑(M a)) →ₗ[R] R) (y : ↑(M b)) :
    (h ▸ f) y = f (h.symm ▸ y) := by
  cases h; rfl

lemma cast_iota {a b : ℕ} (h : a = b) (x : X _⦋a⦌) :
    (h ▸ ((X.ιChainComplex (R := ModuleCat.of R R) x).hom 1))
      = (X.ιChainComplex (R := ModuleCat.of R R)
          (cast (congrArg (fun k => X _⦋k⦌) h) x)).hom 1 := by
  cases h; rfl

lemma transport_map {a b : ℕ} (h : a = b) (x : X _⦋a⦌) :
    cast (congrArg (fun k => X _⦋k⦌) h) x
      = X.map (eqToHom (congrArg SimplexCategory.mk h).symm).op x := by
  cases h; simp

/-- Transporting a generator along an index identification. -/
lemma generator_transport {a b : ℕ} (h : a = b) (x : X _⦋a⦌) :
    (h ▸ ((X.ιChainComplex (R := ModuleCat.of R R) x).hom 1))
      = (X.ιChainComplex (R := ModuleCat.of R R)
          (X.map (eqToHom (congrArg SimplexCategory.mk h).symm).op x)).hom 1 := by
  rw [cast_iota]
  apply congrArg (fun y => (X.ιChainComplex (R := ModuleCat.of R R) y).hom 1)
  exact transport_map h x

/-! ## The Leibniz rule -/

theorem cupLeibniz (R : Type) [CommRing R] (X : SSet) {n m : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) :
    Work.Cohomology.cochainDiff R X (Work.Cohomology.cup R X α β) =
      (Nat.add_right_comm n 1 m ▸ Work.Cohomology.cup R X (Work.Cohomology.cochainDiff R X α) β) +
      ((-1 : R) ^ n) • (Work.Cohomology.cup R X α (Work.Cohomology.cochainDiff R X β)) := by
  apply genEval_ext
  intro σ
  -- key simplices
  let F' : X _⦋n+1⦌ := frontFace X (n+1) (n+m+1) (by omega) σ
  let B' : X _⦋m⦌ := backFace X (n+1) m (X.map (shiftHom n m).op σ)
  let Fr : X _⦋n⦌ := frontFace X n (n+(m+1)) (by omega) σ
  let τ : X _⦋m+1⦌ := backFace X n (m+1) σ
  -- summands
  let dface : ℕ → X _⦋n+m⦌ := fun k => if h : k < n+m+2 then X.δ ⟨k,h⟩ σ else X.δ 0 σ
  let G : ℕ → R := fun k => (-1:R)^k *
    (genEval R X α (frontFace X n (n+m) (by omega) (dface k))
      * genEval R X β (backFace X n m (dface k)))
  let dF : ℕ → X _⦋n⦌ := fun i => if h : i < n+2 then X.δ ⟨i,h⟩ F' else X.δ 0 F'
  let Hsum : ℕ → R := fun i => (-1:R)^i * (genEval R X α (dF i) * genEval R X β B')
  let dtau : ℕ → X _⦋m⦌ := fun j => if h : j < m+2 then X.δ ⟨j,h⟩ τ else X.δ 0 τ
  let Esum : ℕ → R := fun j => (-1:R)^j * (genEval R X α Fr * genEval R X β (dtau j))
  -- LHS
  have hL : genEval R X (cochainDiff R X (cup R X α β)) σ
      = ∑ k ∈ Finset.range (n+m+2), G k := by
    rw [genEval_cochainDiff]
    refine (Finset.sum_congr rfl ?_).trans (Fin.sum_univ_eq_sum_range G (n+m+2))
    intro i _
    simp only [G, dface, dif_pos (by omega : (i:ℕ) < n+m+2)]
    rw [cup_apply']
  -- RHS, first part
  have hA : genEval R X (Nat.add_right_comm n 1 m ▸ cup R X (cochainDiff R X α) β) σ
      = ∑ i ∈ Finset.range (n+2), Hsum i := by
    have h1 : genEval R X (Nat.add_right_comm n 1 m ▸ cup R X (cochainDiff R X α) β) σ
        = genEval R X (cup R X (cochainDiff R X α) β) (X.map (shiftHom n m).op σ) := by
      simp only [genEval]
      rw [cast_linearMap_apply]
      apply congrArg (cup R X (cochainDiff R X α) β)
      exact generator_transport (Nat.add_right_comm n 1 m).symm σ
    rw [h1, cup_apply']
    rw [E7 n m (shiftHom n m) (shiftHom_val n m) σ]
    rw [genEval_cochainDiff, Finset.sum_mul]
    refine (Finset.sum_congr rfl ?_).trans (Fin.sum_univ_eq_sum_range Hsum (n+2))
    intro i _
    simp only [Hsum, dF, F', dif_pos (by omega : (i:ℕ) < n+2)]
    ring
  -- RHS, second part
  have hB : genEval R X (cup R X α (cochainDiff R X β)) σ
      = ∑ j ∈ Finset.range (m+2), Esum j := by
    rw [cup_apply']
    rw [genEval_cochainDiff, Finset.mul_sum]
    refine (Finset.sum_congr rfl ?_).trans (Fin.sum_univ_eq_sum_range Esum (m+2))
    intro j _
    simp only [Esum, dtau, Fr, τ, dif_pos (by omega : (j:ℕ) < m+2)]
    ring
  rw [hL, genEval_add, genEval_smul, smul_eq_mul, hA, hB]
  -- compare the sums
  rw [show n+m+2 = (n+1)+(m+1) by omega]
  rw [Finset.sum_range_add G (n+1) (m+1)]
  rw [show n+2 = (n+1)+1 by omega, Finset.sum_range_succ Hsum (n+1)]
  rw [show m+2 = (m+1)+1 by omega, Finset.sum_range_succ' Esum (m+1)]
  have hterm1 : ∀ k ∈ Finset.range (n+1), G k = Hsum k := by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [G, Hsum, dface, dF, F', B', dif_pos (by omega : k < n+m+2),
      dif_pos (by omega : k < n+2)]
    rw [E1 n m (⟨k, by omega⟩ : Fin (n+m+2)) (by show k ≤ n; omega) σ,
      E2 n m (⟨k, by omega⟩ : Fin (n+m+2)) (by show k ≤ n; omega) (shiftHom n m)
      (shiftHom_val n m) σ]
  have hterm2 : ∀ k ∈ Finset.range (m+1), G ((n+1)+k) = (-1:R)^n * Esum (k+1) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp only [G, Esum, dface, dtau, Fr, τ, dif_pos (by omega : (n+1)+k < n+m+2),
      dif_pos (by omega : k+1 < m+2)]
    rw [E3 n m (⟨(n+1)+k, by omega⟩ : Fin (n+m+2)) (by show (n+1) ≤ (n+1)+k; omega) σ,
      E4 n m (⟨(n+1)+k, by omega⟩ : Fin (n+m+2)) (by show (n+1) ≤ (n+1)+k; omega)
        (⟨k+1, by omega⟩ : Fin (m+2)) (by show k+1 = ((n+1)+k) - n; omega) σ]
    rw [show ((-1:R)^((n+1)+k)) = (-1:R)^n * ((-1:R)^(k+1)) by
      rw [show (n+1)+k = n + (k+1) by omega, pow_add]]
    ring
  have hcancel : Hsum (n+1) + (-1:R)^n * Esum 0 = 0 := by
    simp only [Hsum, Esum, dF, dtau, F', B', τ, dif_pos (by omega : n+1 < n+2),
      dif_pos (by omega : (0:ℕ) < m+2)]
    rw [E5 n m (⟨n+1, by omega⟩ : Fin (n+2)) (by rfl) σ,
      E6 n m (⟨0, by omega⟩ : Fin (m+2)) (by rfl) (shiftHom n m) (shiftHom_val n m) σ]
    rw [show ((-1:R)^(n+1)) = -(-1:R)^n by rw [pow_succ]; ring]
    ring
  rw [mul_add, Finset.sum_congr rfl hterm1, Finset.sum_congr rfl hterm2, Finset.mul_sum]
  have hHn : Hsum (n+1) = -((-1:R)^n * Esum 0) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hcancel
  rw [hHn]
  ring

end

end Work.Cohomology
