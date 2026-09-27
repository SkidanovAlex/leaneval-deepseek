import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.Clutch
import Submission.Work.KT.Fund.Pullback
import Submission.Work.KT.Fund.OrthProjAlg
import Submission.Work.KT.homotopy_inv
import Submission.Work.KT.Fund.Disc
import Submission.Work.KT.crossBoundary_agree

namespace Work.KT

open _root_.Matrix

/-! ## Auxiliary lemmas: the Murray--von Neumann data of the clutching idempotent

The proof of `clutchIdem_cls_indep` does not use homotopy invariance at all: the independence of
the lifts is *algebraic*.  Over each disc separately, `(BᴴB)⁻¹Bᴴ` (with `B = graphB F`) exhibits
the orthogonal projection `orthProj B` as Murray--von Neumann equivalent to the identity: it is a
left inverse of `B` and `B (BᴴB)⁻¹Bᴴ` is the projection.  Composing this equivalence for a lift `F`
with the inverse equivalence for a lift `F'` gives Murray--von Neumann data relating
`graphProj F` to `graphProj F'`; on the equator this data agrees with the reciprocal-graph data for
`G`, `G'` (that is `crossBoundary_agree`), so the two pieces glue to matrices over the fibre
product `pullAlg2 X`, exhibiting `clutchIdem … F G` as Murray--von Neumann equivalent to
`clutchIdem … F' G'`.  Their `K₀`-classes therefore agree. -/

/-- Reindexing a matrix along `finSumFinEquiv` commutes with multiplication. -/
lemma reindex_finSum_mul {A : Type} [Ring A] {a b : ℕ}
    (M N : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) A) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv M
        * Matrix.reindex finSumFinEquiv finSumFinEquiv N
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (M * N) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv M N finSumFinEquiv.symm finSumFinEquiv.symm
    finSumFinEquiv.symm

/-- Two `pairMat`s with equal proof arguments are equal. -/
lemma pairMat_pull_proof_irrel {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {ι : Type} {M₀ M₁ : Matrix ι ι C(X × Ball ℂ, ℂ)}
    (h h' : (M₀.map fun f => Fund.bdryRestrict X f) = M₁.map fun f => Fund.bdryRestrict X f) :
    Fund.pairMat X M₀ M₁ h = Fund.pairMat X M₀ M₁ h' := by
  apply Fund.mat_ext X <;> rfl

/-- `pairMat` only depends on the two matrices, not on the proof of agreement. -/
lemma pairMat_pull_congr {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {ι : Type} {M₀ M₁ M₀' M₁' : Matrix ι ι C(X × Ball ℂ, ℂ)}
    (e₀ : M₀ = M₀') (e₁ : M₁ = M₁')
    (h : (M₀.map fun f => Fund.bdryRestrict X f) = M₁.map fun f => Fund.bdryRestrict X f)
    (h' : (M₀'.map fun f => Fund.bdryRestrict X f) = M₁'.map fun f => Fund.bdryRestrict X f) :
    Fund.pairMat X M₀ M₁ h = Fund.pairMat X M₀' M₁' h' := by
  cases e₀
  cases e₁
  exact pairMat_pull_proof_irrel h h'

/-- `pairMat` is multiplicative. -/
lemma pairMat_pull_mul {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {M₀ M₁ N₀ N₁ : Matrix ι ι C(X × Ball ℂ, ℂ)}
    (h : (M₀.map fun f => Fund.bdryRestrict X f) = M₁.map fun f => Fund.bdryRestrict X f)
    (h' : (N₀.map fun f => Fund.bdryRestrict X f) = N₁.map fun f => Fund.bdryRestrict X f) :
    Fund.pairMat X M₀ M₁ h * Fund.pairMat X N₀ N₁ h'
      = Fund.pairMat X (M₀ * N₀) (M₁ * N₁)
          (by rw [Matrix.map_mul, Matrix.map_mul, h, h']) := by
  apply Fund.mat_ext X
  · rw [Matrix.map_mul, Fund.pairMat_map_prF, Fund.pairMat_map_prF, Fund.pairMat_map_prF]
  · rw [Matrix.map_mul, Fund.pairMat_map_prS, Fund.pairMat_map_prS, Fund.pairMat_map_prS]

/-- **The Murray--von Neumann data relating the graph projections of two lifts.**  With
`Y = (BᴴB)⁻¹Bᴴ` a left inverse of `B` and `B Y` the orthogonal projection onto `im B`, the product
`(B Y') (B' Y)` is the projection onto `im B` and `(B' Y) (B Y')` is the projection onto `im B'`. -/
theorem orthProj_inverse_cross {n : ℕ} (R : Type) [CommRing R] [StarRing R]
    (B B' : Matrix (Fin n ⊕ Fin n) (Fin n) R)
    (hB : IsUnit (Bᴴ * B)) (hB' : IsUnit (B'ᴴ * B')) :
    (B * (Ring.inverse (B'ᴴ * B') * B'ᴴ)) * (B' * (Ring.inverse (Bᴴ * B) * Bᴴ))
        = Fund.orthProj R B ∧
    (B' * (Ring.inverse (Bᴴ * B) * Bᴴ)) * (B * (Ring.inverse (B'ᴴ * B') * B'ᴴ))
        = Fund.orthProj R B' := by
  constructor
  · set Y := Ring.inverse (Bᴴ * B) * Bᴴ with hY
    set Y' := Ring.inverse (B'ᴴ * B') * B'ᴴ with hY'
    have h1 : Y' * B' = 1 := by rw [hY', Matrix.mul_assoc, Ring.inverse_mul_cancel _ hB']
    have h2 : B * Y = Fund.orthProj R B := by
      rw [hY]
      show B * (Ring.inverse (Bᴴ * B) * Bᴴ) = B * Ring.inverse (Bᴴ * B) * Bᴴ
      rw [Matrix.mul_assoc]
    show (B * Y') * (B' * Y) = Fund.orthProj R B
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Y' B' Y, h1, Matrix.one_mul, h2]
  · set Y := Ring.inverse (Bᴴ * B) * Bᴴ with hY
    set Y' := Ring.inverse (B'ᴴ * B') * B'ᴴ with hY'
    have h1 : Y * B = 1 := by rw [hY, Matrix.mul_assoc, Ring.inverse_mul_cancel _ hB]
    have h2 : B' * Y' = Fund.orthProj R B' := by
      rw [hY']
      show B' * (Ring.inverse (B'ᴴ * B') * B'ᴴ) = B' * Ring.inverse (B'ᴴ * B') * B'ᴴ
      rw [Matrix.mul_assoc]
    show (B' * Y) * (B * Y') = Fund.orthProj R B'
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Y B Y', h1, Matrix.one_mul, h2]

/-- **Well-definedness of the clutched class in the choice of the lifts** (step 1 of the route
note in `Submission/Work/KT/fund_product.lean`; the piece that lets step 3 treat `κ` as a function
of the clutching function `u` alone).  `Fund.Kappa` already defines `kappa` as
`k0Glue.symm (cls (clutchIdem … (liftOf …) (liftOf …) …))`, so this is exactly the missing
independence.

`Fund.clutchIdem X n u F G hF hG` is the idempotent element of `Mat ↥(pullAlg2 X)` that glues the
orthogonal projection `graphProj F` onto the graph of a lift `F` of `u` (upper disc) to
`recipProj G` onto the reciprocal graph of a lift `G` of `u⁻¹` (lower disc), via `Fund.clutch_agree`
(the agreement of the two projections on the equator).

The claim: its class in `K0 ↥(pullAlg2 X)` depends only on `u`, not on the lifts.

Route.

* The *single-disc* step is **free**: `graphProj F` is Murray–von Neumann equivalent to `1_n` for
  every `F ∈ Mat C(X × D, ℂ)`: with `B := Fund.graphB (C(X × D, ℂ)) F` and
  `Y := Ring.inverse (Bᴴ * B) * Bᴴ` one has `Y * B = 1` and `B * Y = graphProj F` (using
  `Fund.graphB_recipB_conjTranspose_mul_self`, `Bᴴ * B = 1 + Fᴴ * F`, and
  `Fund.isUnit_one_add_conjTranspose_mul`), so `cls (graphProj F) = cls (Mat.one n)`.  (Do not try
  to prove the well-definedness at that level: that statement is vacuous.)
* The content is therefore in the *gluing*: `F_t := (1 - t) • F + t • F'` (and `G_t` likewise) is,
  for every `t ∈ [0,1]`, again a lift of `u` — `bdryRestrict X` is a unital ℂ-algebra homomorphism,
  so its value on `F_t` is `(1-t) • u + t • u = u` — hence `clutch_agree` applies at every `t` and
  `γ_t := Fund.clutchIdem X n u F_t G_t _ _` is a continuous path of idempotents in
  `Mat ↥(pullAlg2 X)`; `clutchIdem` is proof-irrelevant in `hF`/`hG` (they only feed the Prop
  `clutch_agree`), so `γ_0` and `γ_1` are the two `clutchIdem`s of the claim.
* `Work.KT.homotopy_inv` with `𝔄 := C(X × D, ℂ) × C(X × D, ℂ)`, `A := pullAlg2 X` (closed:
  `Fund.isClosed_pullAlg2`) gives `cls γ_0 = cls γ_1`.  Mind the instance for `Ring ↥(pullAlg2 X)`
  (the explicit `@Subalgebra.toRing` pattern of `Submission/Work/KT/ext_product.lean`).
* Continuity of `t ↦ γ_t`: the entries are polynomial in `t ↦ graphProj F_t`, `recipProj G_t`,
  transposition and `Ring.inverse`, and `Ring.inverse` is continuous on the units
  (`NormedRing.inverse_continuousAt`); the inverses are always taken at units because
  `(graphB F_t)ᴴ (graphB F_t) = 1 + F_tᴴ F_t` is a unit for every `t`.  Build the continuity by the
  currying route already used for `Fund.radPath` in `Submission/Work/KT/Fund/Disc.lean`
  (uncurried continuous map on `unitInterval × (X × Ball ℂ)`, then `.curry`). -/
theorem clutchIdem_cls_indep (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (F G F' G' : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hF : F.map (Fund.bdryRestrict X) = ↑u)
    (hG : G.map (Fund.bdryRestrict X) = ↑(u⁻¹))
    (hF' : F'.map (Fund.bdryRestrict X) = ↑u)
    (hG' : G'.map (Fund.bdryRestrict X) = ↑(u⁻¹)) :
    cls (Fund.clutchIdem X n u F G hF hG) = cls (Fund.clutchIdem X n u F' G' hF' hG') := by
  -- The four Gram matrices of the block columns `graphB F`, `graphB F'`, `recipB G`, `recipB G'`
  -- are units, being `1 + FᴴF` (resp. `1 + GᴴG`).
  have hQB : IsUnit ((Fund.graphB C(X × Ball ℂ, ℂ) F)ᴴ * Fund.graphB C(X × Ball ℂ, ℂ) F) := by
    rw [(Fund.graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) F F).1]
    exact Fund.isUnit_one_add_conjTranspose_mul F
  have hQB' : IsUnit ((Fund.graphB C(X × Ball ℂ, ℂ) F')ᴴ * Fund.graphB C(X × Ball ℂ, ℂ) F') := by
    rw [(Fund.graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) F' F').1]
    exact Fund.isUnit_one_add_conjTranspose_mul F'
  have hQC : IsUnit ((Fund.recipB C(X × Ball ℂ, ℂ) G)ᴴ * Fund.recipB C(X × Ball ℂ, ℂ) G) := by
    rw [(Fund.graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) G G).2]
    exact Fund.isUnit_one_add_conjTranspose_mul G
  have hQC' : IsUnit ((Fund.recipB C(X × Ball ℂ, ℂ) G')ᴴ * Fund.recipB C(X × Ball ℂ, ℂ) G') := by
    rw [(Fund.graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) G' G').2]
    exact Fund.isUnit_one_add_conjTranspose_mul G'
  -- The four products of Murray--von Neumann data recover the two projections.
  have hBB : (Fund.graphB C(X × Ball ℂ, ℂ) F
        * (Ring.inverse ((Fund.graphB C(X × Ball ℂ, ℂ) F')ᴴ * Fund.graphB C(X × Ball ℂ, ℂ) F')
            * (Fund.graphB C(X × Ball ℂ, ℂ) F')ᴴ))
      * (Fund.graphB C(X × Ball ℂ, ℂ) F'
        * (Ring.inverse ((Fund.graphB C(X × Ball ℂ, ℂ) F)ᴴ * Fund.graphB C(X × Ball ℂ, ℂ) F)
            * (Fund.graphB C(X × Ball ℂ, ℂ) F)ᴴ))
      = Fund.graphProj C(X × Ball ℂ, ℂ) F :=
    (orthProj_inverse_cross C(X × Ball ℂ, ℂ) _ _ hQB hQB').1
  have hB'B : (Fund.graphB C(X × Ball ℂ, ℂ) F'
        * (Ring.inverse ((Fund.graphB C(X × Ball ℂ, ℂ) F)ᴴ * Fund.graphB C(X × Ball ℂ, ℂ) F)
            * (Fund.graphB C(X × Ball ℂ, ℂ) F)ᴴ))
      * (Fund.graphB C(X × Ball ℂ, ℂ) F
        * (Ring.inverse ((Fund.graphB C(X × Ball ℂ, ℂ) F')ᴴ * Fund.graphB C(X × Ball ℂ, ℂ) F')
            * (Fund.graphB C(X × Ball ℂ, ℂ) F')ᴴ))
      = Fund.graphProj C(X × Ball ℂ, ℂ) F' :=
    (orthProj_inverse_cross C(X × Ball ℂ, ℂ) _ _ hQB hQB').2
  have hCC : (Fund.recipB C(X × Ball ℂ, ℂ) G
        * (Ring.inverse ((Fund.recipB C(X × Ball ℂ, ℂ) G')ᴴ * Fund.recipB C(X × Ball ℂ, ℂ) G')
            * (Fund.recipB C(X × Ball ℂ, ℂ) G')ᴴ))
      * (Fund.recipB C(X × Ball ℂ, ℂ) G'
        * (Ring.inverse ((Fund.recipB C(X × Ball ℂ, ℂ) G)ᴴ * Fund.recipB C(X × Ball ℂ, ℂ) G)
            * (Fund.recipB C(X × Ball ℂ, ℂ) G)ᴴ))
      = Fund.recipProj C(X × Ball ℂ, ℂ) G :=
    (orthProj_inverse_cross C(X × Ball ℂ, ℂ) _ _ hQC hQC').1
  have hC'C : (Fund.recipB C(X × Ball ℂ, ℂ) G'
        * (Ring.inverse ((Fund.recipB C(X × Ball ℂ, ℂ) G)ᴴ * Fund.recipB C(X × Ball ℂ, ℂ) G)
            * (Fund.recipB C(X × Ball ℂ, ℂ) G)ᴴ))
      * (Fund.recipB C(X × Ball ℂ, ℂ) G
        * (Ring.inverse ((Fund.recipB C(X × Ball ℂ, ℂ) G')ᴴ * Fund.recipB C(X × Ball ℂ, ℂ) G')
            * (Fund.recipB C(X × Ball ℂ, ℂ) G')ᴴ))
      = Fund.recipProj C(X × Ball ℂ, ℂ) G' :=
    (orthProj_inverse_cross C(X × Ball ℂ, ℂ) _ _ hQC hQC').2
  -- The two halves of the data agree on the equator, so they glue.
  have hb := crossBoundary_agree X u F G F' G' hF hG hF' hG'
  have ha := crossBoundary_agree X u F' G' F G hF' hG' hF hG
  -- Hence the two clutched idempotents are Murray--von Neumann equivalent.
  have hmv : Mat.MvN (Fund.clutchIdem X n u F G hF hG)
      (Fund.clutchIdem X n u F' G' hF' hG') := by
    refine ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.pairMat X _ _ ha),
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.pairMat X _ _ hb), ?_, ?_⟩
    · show Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.pairMat X _ _ hb)
          * Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.pairMat X _ _ ha)
        = Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Fund.pairMat X (Fund.graphProj C(X × Ball ℂ, ℂ) F)
              (Fund.recipProj C(X × Ball ℂ, ℂ) G) (Fund.clutch_agree X n u F G hF hG))
      rw [reindex_finSum_mul, pairMat_pull_mul]
      congr 1
      exact pairMat_pull_congr hBB hCC _ _
    · show Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.pairMat X _ _ ha)
          * Matrix.reindex finSumFinEquiv finSumFinEquiv (Fund.pairMat X _ _ hb)
        = Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Fund.pairMat X (Fund.graphProj C(X × Ball ℂ, ℂ) F')
              (Fund.recipProj C(X × Ball ℂ, ℂ) G') (Fund.clutch_agree X n u F' G' hF' hG'))
      rw [reindex_finSum_mul, pairMat_pull_mul]
      congr 1
      exact pairMat_pull_congr hB'B hC'C _ _
  exact cls_eq_of_mvN (Fund.clutchIdem_isIdem X n u F G hF hG)
    (Fund.clutchIdem_isIdem X n u F' G' hF' hG') hmv

end Work.KT
