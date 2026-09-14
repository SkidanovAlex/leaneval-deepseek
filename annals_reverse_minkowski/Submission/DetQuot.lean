import Mathlib
import ChallengeDeps
import Submission.Poisson
import Submission.Commons.Lattice.Determinant.gram_det_independent
import Submission.QuotientLattice
import Submission.Commons.Analysis.InnerProductSpace.gram_det_shear_orthogonal

open Module MeasureTheory Metric
open Submission.QuotientLattice
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace ENNReal NNReal Pointwise
set_option autoImplicit false

namespace Submission.DetQuot

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable section


/-- The real inner product on `EuclideanSpace ℝ (Fin m)` is the coordinate dot product. -/
lemma inner_coord_sum {m : ℕ} (x y : EuclideanSpace ℝ (Fin m)) :
    ⟪x, y⟫_ℝ = ∑ i : Fin m, x i * y i := by
  rw [PiLp.inner_apply]
  simp
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The Gram matrix of the canonical `finBasis` equals `(B ℒ)ᵀ (B ℒ)`. -/
lemma gram_finBasis_eq_B {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] :
    (Matrix.of (fun i j : Fin (finrank ℤ ℒ) =>
      ⟪(((Module.finBasis ℤ ℒ) i : ℒ) : E), (((Module.finBasis ℤ ℒ) j : ℒ) : E)⟫_ℝ)) =
      (ReverseMinkowski.B ℒ).transpose * (ReverseMinkowski.B ℒ) := by
  ext i j
  dsimp [ReverseMinkowski.B]
  rw [inner_coord_sum]
  rfl

/-- **Gram bridge**: `ReverseMinkowski.determinant ℒ = √(det Gram(e))` for ANY `ℤ`-basis
`e` of `ℒ` (same index type as `finBasis`). -/
lemma determinant_eq_sqrt_gram {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    [Module.Free ℤ ℒ] [Module.Finite ℤ ℒ]
    (e : Module.Basis (Fin (finrank ℤ ℒ)) ℤ ℒ) :
    ReverseMinkowski.determinant ℒ =
      √((Matrix.of (fun i j : Fin (finrank ℤ ℒ) =>
        ⟪(((e i : ℒ) : E)), (((e j : ℒ) : E))⟫_ℝ)).det) := by
  classical
  dsimp [ReverseMinkowski.determinant]
  congr 1
  have h1 : ((ReverseMinkowski.B ℒ).transpose * (ReverseMinkowski.B ℒ)).det =
      (Matrix.of (fun i j : Fin (finrank ℤ ℒ) =>
        ⟪(((Module.finBasis ℤ ℒ) i : ℒ) : E), (((Module.finBasis ℤ ℒ) j : ℒ) : E)⟫_ℝ)).det := by
    rw [gram_finBasis_eq_B]
  rw [h1]
  have h2 := Commons.Lattice.Determinant.gram_det_independent (n := n)
    (m := finrank ℤ ℒ) (ℒ := ℒ) (Module.finBasis ℤ ℒ) e
  -- h2 : Gram(finBasis).det = Gram(e).det
  rw [h2]
/-- Adapted basis of ℒ (e), its first-d values u, tail x, projected tail w. -/
lemma head_span_eq {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hd : Module.finrank ℤ ℒ' ≤ n) (e : Module.Basis (Fin n) ℤ ℒ)
    (he : ∀ i : Fin (Module.finrank ℤ ℒ'),
      ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E)) :
    S = Submodule.span ℝ (Set.range
      (fun i : Fin (Module.finrank ℤ ℒ') => ((e (Fin.castLE hd i) : ℒ) : E))) := by
  classical
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  rw [hS]
  have hb : realSpan ℒ' = Submodule.span ℝ (Set.range
      (fun i : Fin (Module.finrank ℤ ℒ') => ((Module.finBasis ℤ ℒ' i : ℒ') : E))) :=
    realSpan_eq_span_basis (ℒ := ℒ')
  rw [hb]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨i, he i⟩
  · rintro ⟨i, rfl⟩
    refine ⟨i, (he i).symm⟩


/-- determinant of the Gram of a basis family equals that of its split (head, tail) family -/
lemma gram_det_head_tail {ℒ : Submodule ℤ E} (e : Module.Basis (Fin n) ℤ ℒ) {d : ℕ}
    (hd : d ≤ n) :
    let u : Fin d → E := fun i => ((e (Fin.castLE hd i) : ℒ) : E)
    let x : Fin (n - d) → E := fun j => ((e (tailEmb (n := n) hd j) : ℒ) : E)
    (Matrix.gram ℝ (fun k : Fin n => ((e k : ℒ) : E))).det =
      (Matrix.gram ℝ (Sum.elim u x)).det := by
  classical
  intro u x
  let φ : Fin n ≃ (Fin d ⊕ Fin (n - d)) := (Commons.Lattice.Module.BasisExtensionPure.blockEquiv hd).symm
  have hq : ∀ q : Fin d ⊕ Fin (n - d), Sum.elim u x q =
      ((e (Commons.Lattice.Module.BasisExtensionPure.blockEquiv hd q) : ℒ) : E) := by
    intro q
    cases q with
    | inl i => rfl
    | inr j => rfl
  have hpoint : (fun k : Fin n => ((e k : ℒ) : E)) = Sum.elim u x ∘ φ := by
    funext k
    have hqk : Sum.elim u x (φ k) = ((e ((Commons.Lattice.Module.BasisExtensionPure.blockEquiv hd) (φ k)) : ℒ) : E) :=
      hq (φ k)
    have hidx : ((Commons.Lattice.Module.BasisExtensionPure.blockEquiv hd) (φ k) : Fin n) = k := by
      dsimp [φ]
      exact ((Commons.Lattice.Module.BasisExtensionPure.blockEquiv hd).right_inv k)
    calc
      ((e k : ℒ) : E) = ((e ((Commons.Lattice.Module.BasisExtensionPure.blockEquiv hd) (φ k)) : ℒ) : E) := by rw [hidx]
      _ = Sum.elim u x (φ k) := hqk.symm
  calc
    (Matrix.gram ℝ (fun k : Fin n => ((e k : ℒ) : E))).det
        = (Matrix.gram ℝ (Sum.elim u x ∘ φ)).det := by rw [hpoint]
    _ = (Matrix.gram ℝ (Sum.elim u x)).det := by
        change (Matrix.gram ℝ (Sum.elim u x ∘ φ)).det = (Matrix.gram ℝ (Sum.elim u x)).det
        have hg : Matrix.gram ℝ (Sum.elim u x ∘ φ) = (Matrix.gram ℝ (Sum.elim u x)).submatrix φ φ := by
          ext k l
          simp [Matrix.gram]
        rw [hg]
        simp


theorem determinant_quot {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (hℒ : IsZLattice ℝ ℒ) (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ)
    [DiscreteTopology (quotLattice ℒ S)] :
    ReverseMinkowski.determinant (quotLattice ℒ S) =
      ReverseMinkowski.determinant ℒ / ReverseMinkowski.determinant ℒ' := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  rcases exists_adapted_quotBasis (ℒ' := ℒ') (ℒ := ℒ) hℒ S hS hp with ⟨hd, e, β, he, hβval⟩
  haveI : Module.Free ℤ (quotLattice ℒ S) := Module.Free.of_basis β
  haveI : Module.Finite ℤ (quotLattice ℒ S) := Module.Finite.of_basis β
  let d := Module.finrank ℤ ℒ'
  let u : Fin d → E := fun i => ((e (Fin.castLE hd i) : ℒ) : E)
  let x : Fin (n - d) → E := fun j => ((e (tailEmb (n := n) hd j) : ℒ) : E)
  let w : Fin (n - d) → E := fun j => Sᗮ.starProjection (((e (tailEmb (n := n) hd j) : ℒ)) : E)
  let DL : ℝ := (Matrix.gram ℝ (fun k : Fin n => ((e k : ℒ) : E))).det
  let Du : ℝ := (Matrix.gram ℝ u).det
  let Dw : ℝ := (Matrix.gram ℝ w).det
  have hS' : S = Submodule.span ℝ (Set.range u) := by
    dsimp [u]
    exact head_span_eq (n := n) S hS hd e he
  have hxw : ∀ j : Fin (n - d), x j - w j ∈ S := by
    intro j
    have hwj : w j = x j - S.starProjection (x j) := by
      dsimp [w, x]
      exact proj_orth_comp S ((e (tailEmb (n := n) hd j) : ℒ) : E)
    rw [hwj]
    have hxy : x j - (x j - S.starProjection (x j)) = S.starProjection (x j) := by abel
    rw [hxy]
    exact Submodule.starProjection_apply_mem S (x j)
  have hw : ∀ j : Fin (n - d), w j ∈ Sᗮ := by
    intro j
    exact Submodule.starProjection_apply_mem Sᗮ ((e (tailEmb (n := n) hd j) : ℒ) : E)
  have hshear := Commons.Analysis.InnerProductSpace.gram_det_shear_orthogonal (N := n)
    (d := d) (r := n - d) u x w S hS' hxw hw
  have hmain : DL = Du * Dw := by
    dsimp [DL, Du, Dw]
    rw [gram_det_head_tail (n := n) (ℒ := ℒ) e hd]
    exact hshear
  -- square roots
  have hDu0 : 0 ≤ Du := by
    dsimp [Du]
    exact (Matrix.posSemidef_gram ℝ u).det_nonneg
  have hDw0 : 0 ≤ Dw := by
    dsimp [Dw]
    exact (Matrix.posSemidef_gram ℝ w).det_nonneg
  have hsqrt : √(Du * Dw) = √Du * √Dw := by
    rw [Real.sqrt_mul hDu0]
  -- bridge ℒ
  let equiv : Fin n ≃ Fin (Module.finrank ℤ ℒ) := (finCongr (fullrank_finrank ℒ hℒ)).symm
  let e'' : Module.Basis (Fin (Module.finrank ℤ ℒ)) ℤ ℒ := e.reindex equiv
  have hgL : (Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ ℒ) => ((e'' i : ℒ) : E))).det = DL := by
    dsimp [DL]
    let v : Fin n → E := fun k => ((e k : ℒ) : E)
    have hfam : (fun i : Fin (Module.finrank ℤ ℒ) => ((e'' i : ℒ) : E)) = v ∘ equiv.symm := by
      funext i
      dsimp [e'', equiv, v]
      simp [Module.Basis.reindex_apply]
    calc
      (Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ ℒ) => ((e'' i : ℒ) : E))).det
          = (Matrix.gram ℝ (v ∘ equiv.symm)).det := by rw [hfam]
      _ = (Matrix.gram ℝ v).det := by
          have hg : Matrix.gram ℝ (v ∘ equiv.symm) = (Matrix.gram ℝ v).submatrix equiv.symm equiv.symm := by
            ext a b
            simp [Matrix.gram]
          rw [hg]
          simp
  have hL0 := Submission.DetQuot.determinant_eq_sqrt_gram (ℒ := ℒ) e''
  have hL0g : ReverseMinkowski.determinant ℒ = √(Matrix.gram ℝ
      (fun i : Fin (Module.finrank ℤ ℒ) => ((e'' i : ℒ) : E))).det := by
    simpa [Matrix.gram] using hL0
  have hL : ReverseMinkowski.determinant ℒ = √DL := by
    rw [hgL] at hL0g
    exact hL0g
  -- bridge ℒ'
  have hL'0 := Submission.DetQuot.determinant_eq_sqrt_gram (ℒ := ℒ') (Module.finBasis ℤ ℒ')
  have hL'0g : ReverseMinkowski.determinant ℒ' = √(Matrix.gram ℝ
      (fun i : Fin (Module.finrank ℤ ℒ') => ((Module.finBasis ℤ ℒ' i : ℒ') : E))).det := by
    simpa [Matrix.gram] using hL'0
  have hgU : (Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ ℒ') => ((Module.finBasis ℤ ℒ' i : ℒ') : E))).det = Du := by
    dsimp [Du, u]
    congr 1
    -- gram of finBasis values = gram of (e∘castLE) values pointwise
    ext i j
    simp [he i, he j]
  have hL' : ReverseMinkowski.determinant ℒ' = √Du := by
    rw [hgU] at hL'0g
    exact hL'0g
  -- bridge Q
  have hfinQ : Module.finrank ℤ (quotLattice ℒ S) = n - d := by
    dsimp [d]
    simpa using (Module.finrank_eq_card_basis β)
  let equivQ : Fin (n - d) ≃ Fin (Module.finrank ℤ (quotLattice ℒ S)) :=
    (finCongr hfinQ).symm
  let β'' : Module.Basis (Fin (Module.finrank ℤ (quotLattice ℒ S))) ℤ (quotLattice ℒ S) :=
    β.reindex equivQ
  have hgQ : (Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ (quotLattice ℒ S)) => ((β'' i : quotLattice ℒ S) : E))).det = Dw := by
    dsimp [Dw]
    let vq : Fin (n - d) → E := fun j => ((β j : quotLattice ℒ S) : E)
    have hfam : (fun i : Fin (Module.finrank ℤ (quotLattice ℒ S)) => ((β'' i : quotLattice ℒ S) : E)) = vq ∘ equivQ.symm := by
      funext i
      dsimp [β'', equivQ, vq]
      simp [Module.Basis.reindex_apply]
    have hvq : vq = w := by
      dsimp [vq, w]
      funext j
      exact hβval j
    calc
      (Matrix.gram ℝ (fun i : Fin (Module.finrank ℤ (quotLattice ℒ S)) => ((β'' i : quotLattice ℒ S) : E))).det
          = (Matrix.gram ℝ (vq ∘ equivQ.symm)).det := by rw [hfam]
      _ = (Matrix.gram ℝ vq).det := by
          have hg : Matrix.gram ℝ (vq ∘ equivQ.symm) = (Matrix.gram ℝ vq).submatrix equivQ.symm equivQ.symm := by
            ext a b
            simp [Matrix.gram]
          rw [hg]
          simp
      _ = (Matrix.gram ℝ w).det := by rw [hvq]
  have hQ0 := Submission.DetQuot.determinant_eq_sqrt_gram (ℒ := quotLattice ℒ S) β''
  have hQ0g : ReverseMinkowski.determinant (quotLattice ℒ S) = √(Matrix.gram ℝ
      (fun i : Fin (Module.finrank ℤ (quotLattice ℒ S)) => ((β'' i : quotLattice ℒ S) : E))).det := by
    simpa [Matrix.gram] using hQ0
  have hQ : ReverseMinkowski.determinant (quotLattice ℒ S) = √Dw := by
    rw [hgQ] at hQ0g
    exact hQ0g
  -- determinant product
  have hprod : ReverseMinkowski.determinant ℒ =
      ReverseMinkowski.determinant ℒ' * ReverseMinkowski.determinant (quotLattice ℒ S) := by
    calc
      ReverseMinkowski.determinant ℒ = √DL := hL
      _ = √(Du * Dw) := by rw [hmain]
      _ = √Du * √Dw := hsqrt
      _ = ReverseMinkowski.determinant ℒ' * ReverseMinkowski.determinant (quotLattice ℒ S) := by
          rw [← hL', ← hQ]
  -- divide
  have hL'pos : 0 < ReverseMinkowski.determinant ℒ' := by
    rw [hL']
    have hDu_pos : 0 < Du := by
      dsimp [Du]
      have hli : LinearIndependent ℝ u := by
        dsimp [u]
        -- u = e∘castLE subfamily of independent values
        have hli0 := linIndep_basis_values (n := n) (ℒ := ℒ) hℒ e
        exact hli0.comp (Fin.castLE hd) (by
          intro a b hab
          apply Fin.ext
          simpa using congrArg Fin.val hab)
      have hdetnz : (Matrix.gram ℝ u).det ≠ 0 := by
        exact (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)).2 hli
      have hge : 0 ≤ (Matrix.gram ℝ u).det := (Matrix.posSemidef_gram ℝ u).det_nonneg
      exact lt_of_le_of_ne hge (Ne.symm hdetnz)  -- hmm hge : 0 ≤ a and a ≠ 0 gives 0 < a
    exact Real.sqrt_pos.2 hDu_pos
  have hL'neq : ReverseMinkowski.determinant ℒ' ≠ 0 := ne_of_gt hL'pos
  have hprod' : ReverseMinkowski.determinant ℒ = ReverseMinkowski.determinant ℒ' * √Dw := by
    rw [hQ] at hprod
    exact hprod
  calc
    ReverseMinkowski.determinant (quotLattice ℒ S) = √Dw := hQ
    _ = (ReverseMinkowski.determinant ℒ' * √Dw) / ReverseMinkowski.determinant ℒ' := by
        field_simp [hL'neq]
    _ = ReverseMinkowski.determinant ℒ / ReverseMinkowski.determinant ℒ' := by
        rw [← hprod']


end
end Submission.DetQuot
