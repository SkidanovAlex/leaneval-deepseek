import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.map_orthProj
import Submission.Work.KT.Fund.recipB_eq_graphB_mul
import Submission.Work.KT.Fund.isUnit_one_add_conjTranspose_mul
import Submission.Work.KT.Fund.graphB_recipB_conjTranspose_mul_self
import Submission.Work.KT.Fund.clutch_agree
import Submission.Work.KT.Bott.GlueAux
import Submission.Work.KT.clutchIdem_cls_indep

/-!
# `Work.KT.Fund.kappa_const`

The clutched class `κ(u) ∈ K₀(C(X × S², ℂ))` of a unit `u` over `C(X × S¹, ℂ)` (Hatcher's
elementary clutching construction of the Bott class, see `Work.KT.Fund.Kappa`) is trivial when the
clutching function is pulled back from `X`:

  `u = pullMat X g` for a unit `g` of matrices over `C(X, ℂ)`  ⟹  `κ(u) = [1_n]`.

Mathematically, the clutched bundle is glued from two trivial bundles along
`(x, z) ↦ g(x) ∈ GL_n(ℂ)`; changing the trivialisation of the first hemisphere by the
constant-in-the-disc function `g` (a unit of matrices over `C(X × D, ℂ)`) turns the gluing
function into the identity, so the glued bundle is trivial.

Formally the proof is a Murray–von Neumann computation in the fibre product
`pullAlg2 X ⊆ C(X × D, ℂ) × C(X × D, ℂ)` (the algebra of clutching data for `X × S²`):

* `Fund.clutchIdem_cls_indep` replaces the `Fund.liftOf` choices inside `Fund.kappa` by the
  explicit lifts `ĝ = gUp g`, `Ĝ = gUp g⁻¹` (constant in the disc variable);
* for these lifts the clutched idempotent `p = pairMat (graphProj ĝ) (recipProj Ĝ)` admits an
  explicit frame `pairMatR (graphB ĝ * ĝ) (recipB Ĝ * ĝ * ĝ)` and its Gram left inverse over
  `pullAlg2 X`, exhibiting `p` as Murray–von Neumann equivalent to `1_n`;
* the `K₀`-isomorphism `Fund.k0Glue` is unital, so it carries the class of `1_n` over
  `C(X × S², ℂ)` to the class of `1_n` over `pullAlg2 X`.
-/

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace KC

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## Pull-back along the projection `X → X × D` -/

/-- `C(X, ℂ) →+* C(X × D, ℂ)`: pull back functions along the projection, so that the result is
constant in the disc variable. -/
def discHom : C(X, ℂ) →+* C(X × Ball ℂ, ℂ) := (pullAlg (projX X)).toRingHom

/-- `C(X, ℂ) →+* C(X × S¹, ℂ)`: pull back along the projection.  This is `discHom` followed by
restriction to the boundary circle. -/
def sphHom : C(X, ℂ) →+* C(X × Sph ℂ, ℂ) :=
  (pullAlg (ContinuousMap.fst : C(X × Sph ℂ, X))).toRingHom

lemma discHom_apply (f : C(X, ℂ)) (p : X × Ball ℂ) : discHom X f p = f p.1 := rfl

lemma sphHom_apply (f : C(X, ℂ)) (p : X × Sph ℂ) : sphHom X f p = f p.1 := rfl

/-- The boundary restriction of `discHom X f` is `sphHom X f`. -/
lemma comp_discHom_eq_sphHom : (bdryRestrict X).comp (discHom X) = sphHom X := by
  refine RingHom.ext fun f => ?_
  refine ContinuousMap.ext fun p => ?_
  simp only [RingHom.comp_apply, bdryRestrict_apply, discHom_apply, sphHom_apply]

/-- The monoid homomorphism "extend a matrix over `C(X, ℂ)` to the disc, constant in the disc
variable". -/
def discHomM (m : ℕ) :
    (Matrix (Fin m) (Fin m) C(X, ℂ)) →* Matrix (Fin m) (Fin m) C(X × Ball ℂ, ℂ) where
  toFun M := M.map ⇑(discHom X)
  map_one' := by rw [Work.KT.Bott.matrix_map_one]
  map_mul' M N := by rw [Matrix.map_mul]

/-- The monoid homomorphism "pull a matrix over `C(X, ℂ)` back to `X × S¹`". -/
def pullHomM (m : ℕ) :
    (Matrix (Fin m) (Fin m) C(X, ℂ)) →* Matrix (Fin m) (Fin m) C(X × Sph ℂ, ℂ) where
  toFun M := M.map ⇑(sphHom X)
  map_one' := by rw [Work.KT.Bott.matrix_map_one]
  map_mul' M N := by rw [Matrix.map_mul]

lemma pullHomM_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) C(X, ℂ)) :
    pullHomM X m M = M.map ⇑(sphHom X) := rfl

/-- `Fund.pullMat` is entrywise application of `sphHom`. -/
lemma pullMat_eq_map {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    pullMat X M = M.map ⇑(sphHom X) := by
  refine Matrix.ext fun i j => ?_
  ext p
  rw [Matrix.map_apply, pullMat_apply]
  rfl

lemma pullMat_eq_pullHomM {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    pullMat X M = pullHomM X n M := by
  rw [pullMat_eq_map]
  rfl

/-- The lift of a matrix over `C(X, ℂ)` to the disc, constant in the disc variable. -/
def gUp {m : ℕ} (M : Matrix (Fin m) (Fin m) C(X, ℂ)) :
    Matrix (Fin m) (Fin m) C(X × Ball ℂ, ℂ) :=
  discHomM X m M

lemma gUp_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) C(X, ℂ)) :
    gUp X M = M.map ⇑(discHom X) := rfl

lemma gUp_bdry {m : ℕ} (M : Matrix (Fin m) (Fin m) C(X, ℂ)) :
    (gUp X M).map ⇑(bdryRestrict X) = pullMat X M := by
  have hcomp := comp_discHom_eq_sphHom X
  simp only [gUp, discHomM, MonoidHom.coe_mk, OneHom.coe_mk, Work.KT.Bott.matrix_map_map,
    pullMat_eq_map, hcomp]

lemma gUp_mul {m : ℕ} (M N : Matrix (Fin m) (Fin m) C(X, ℂ)) :
    gUp X (M * N) = gUp X M * gUp X N :=
  map_mul (discHomM X m) M N

lemma gUp_one {m : ℕ} : gUp X (1 : Matrix (Fin m) (Fin m) C(X, ℂ)) = 1 :=
  map_one (discHomM X m)

/-- `gUp` of a unit matrix is a unit. -/
lemma isUnit_gUp {m : ℕ} (M : Matrix (Fin m) (Fin m) C(X, ℂ)) (hM : IsUnit M) :
    IsUnit (gUp X M) := by
  obtain ⟨v, rfl⟩ := hM
  refine ⟨Units.map (discHomM X m) v, ?_⟩
  exact Units.coe_map (discHomM X m) v

/-- The underlying matrix of the inverse unit over `X × S¹` is `pullMat` of the inverse. -/
lemma pullMat_inv {n : ℕ} (g : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = pullMat X (g : Matrix (Fin n) (Fin n) C(X, ℂ))) :
    pullMat X (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))
      = (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
  have hPu : Units.map (pullHomM X n) g = u := by
    refine Units.ext ?_
    rw [Units.coe_map]
    show pullHomM X n (↑g) = (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
    rw [← pullMat_eq_pullHomM]
    exact hu.symm
  rw [← hPu, ← map_inv, Units.coe_map, ← pullMat_eq_pullHomM]

/-! ## Elementary algebra of `orthProj` -/

/-- The orthogonal projection onto the image of `B` factors through the Gram left inverse. -/
lemma orthProj_eq_mul {n : ℕ} (R : Type) [CommRing R] [Star R]
    (B : Matrix (Fin n ⊕ Fin n) (Fin n) R) :
    B * (Ring.inverse (Bᴴ * B) * Bᴴ) = orthProj R B := by
  unfold orthProj
  rw [Matrix.mul_assoc]

/-- The Gram left inverse `(BᴴB)⁻¹Bᴴ` of `B` (when `BᴴB` is a unit). -/
lemma leftInv_mul {n : ℕ} (R : Type) [CommRing R] [Star R]
    (B : Matrix (Fin n ⊕ Fin n) (Fin n) R) (h : IsUnit (Bᴴ * B)) :
    (Ring.inverse (Bᴴ * B) * Bᴴ) * B = 1 := by
  rw [Matrix.mul_assoc, Ring.inverse_mul_cancel _ h]

/-- The Gram matrix of `B * U` is a unit when `BᴴB` is and `U` is. -/
lemma isUnit_conjTranspose_mul_mul {n : ℕ} (R : Type) [CommRing R] [StarRing R]
    (B : Matrix (Fin n ⊕ Fin n) (Fin n) R) (U : Matrix (Fin n) (Fin n) R)
    (hB : IsUnit (Bᴴ * B)) (hU : IsUnit U) : IsUnit ((B * U)ᴴ * (B * U)) := by
  have hcast : (B * U)ᴴ * (B * U) = Uᴴ * (Bᴴ * B) * U := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc Uᴴ Bᴴ (B * U), Matrix.mul_assoc Uᴴ (Bᴴ * B) U,
      ← Matrix.mul_assoc Bᴴ B U]
  rw [hcast]
  exact ((Matrix.isUnit_conjTranspose U).2 hU).mul hB |>.mul hU

/-- The Gram matrix of `graphB F` is a unit. -/
lemma isUnit_graphB_gram {n : ℕ} (F : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    IsUnit ((graphB C(X × Ball ℂ, ℂ) F)ᴴ * graphB C(X × Ball ℂ, ℂ) F) := by
  rw [(graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) F F).1]
  exact isUnit_one_add_conjTranspose_mul F

/-- The Gram matrix of `recipB G` is a unit. -/
lemma isUnit_recipB_gram {n : ℕ} (G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    IsUnit ((recipB C(X × Ball ℂ, ℂ) G)ᴴ * recipB C(X × Ball ℂ, ℂ) G) := by
  rw [(graphB_recipB_conjTranspose_mul_self C(X × Ball ℂ, ℂ) G G).2]
  exact isUnit_one_add_conjTranspose_mul G

/-! ## Rectangular pairings of the two disc algebras -/

/-- Rectangular version of `Fund.pairMat`. -/
def pairMatR {ι κ : Type} (M₀ M₁ : Matrix ι κ C(X × Ball ℂ, ℂ))
    (h : M₀.map ⇑(bdryRestrict X) = M₁.map ⇑(bdryRestrict X)) :
    Matrix ι κ ↥(pullAlg2 X) :=
  fun i j => mkPair X (M₀ i j) (M₁ i j) (by
    have h' := congrFun (congrFun h i) j
    simpa only [Matrix.map_apply] using h')

@[simp] lemma pairMatR_map_prF {ι κ : Type} (M₀ M₁ : Matrix ι κ C(X × Ball ℂ, ℂ))
    (h : M₀.map ⇑(bdryRestrict X) = M₁.map ⇑(bdryRestrict X)) :
    (pairMatR X M₀ M₁ h).map ⇑(prF X) = M₀ := rfl

@[simp] lemma pairMatR_map_prS {ι κ : Type} (M₀ M₁ : Matrix ι κ C(X × Ball ℂ, ℂ))
    (h : M₀.map ⇑(bdryRestrict X) = M₁.map ⇑(bdryRestrict X)) :
    (pairMatR X M₀ M₁ h).map ⇑(prS X) = M₁ := rfl

/-- `pairMatR` only depends on the two matrices, not on the compatibility proof. -/
lemma pairMatR_congr {ι κ : Type} (M₀ M₁ : Matrix ι κ C(X × Ball ℂ, ℂ))
    (h h' : M₀.map ⇑(bdryRestrict X) = M₁.map ⇑(bdryRestrict X)) :
    pairMatR X M₀ M₁ h = pairMatR X M₀ M₁ h' := by
  refine Matrix.ext fun i j => ?_
  exact Subtype.ext rfl

/-- `pairMatR` agrees with `Fund.pairMat` on square matrices. -/
lemma pairMat_eq_pairMatR {ι : Type} (M₀ M₁ : Matrix ι ι C(X × Ball ℂ, ℂ))
    (h : M₀.map ⇑(bdryRestrict X) = M₁.map ⇑(bdryRestrict X)) :
    pairMat X M₀ M₁ h = pairMatR X M₀ M₁ h := rfl

/-- Two matrices over the fibre product with the same two projections are equal. -/
lemma mat_ext_rect {ι κ : Type} {A B : Matrix ι κ ↥(pullAlg2 X)}
    (h₁ : A.map ⇑(prF X) = B.map ⇑(prF X)) (h₂ : A.map ⇑(prS X) = B.map ⇑(prS X)) : A = B := by
  refine Matrix.ext fun i j => ?_
  refine Subtype.ext (Prod.ext ?_ ?_)
  · have h := congrFun (congrFun h₁ i) j
    rw [Matrix.map_apply, Matrix.map_apply, prF_apply, prF_apply] at h
    exact h
  · have h := congrFun (congrFun h₂ i) j
    rw [Matrix.map_apply, Matrix.map_apply, prS_apply, prS_apply] at h
    exact h

/-- `pairMatR` is multiplicative. -/
lemma pairMatR_mul {ι κ μ : Type} [Fintype κ]
    (M₀ M₁ : Matrix ι κ C(X × Ball ℂ, ℂ)) (N₀ N₁ : Matrix κ μ C(X × Ball ℂ, ℂ))
    (hM : M₀.map ⇑(bdryRestrict X) = M₁.map ⇑(bdryRestrict X))
    (hN : N₀.map ⇑(bdryRestrict X) = N₁.map ⇑(bdryRestrict X)) :
    pairMatR X M₀ M₁ hM * pairMatR X N₀ N₁ hN
      = pairMatR X (M₀ * N₀) (M₁ * N₁)
          (by rw [Matrix.map_mul, Matrix.map_mul, hM, hN]) := by
  apply mat_ext_rect X
  · rw [Matrix.map_mul, pairMatR_map_prF, pairMatR_map_prF, pairMatR_map_prF]
  · rw [Matrix.map_mul, pairMatR_map_prS, pairMatR_map_prS, pairMatR_map_prS]

/-- `pairMatR` of two identity matrices is the identity matrix. -/
lemma pairMatR_one (n : ℕ)
    (h : (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map ⇑(bdryRestrict X)
      = (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map ⇑(bdryRestrict X)) :
    pairMatR X (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
      (1 : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) h = 1 := by
  apply mat_ext_rect X
  · simp only [pairMatR_map_prF, Work.KT.Bott.matrix_map_one]
  · simp only [pairMatR_map_prS, Work.KT.Bott.matrix_map_one]

/-- Murray–von Neumann equivalence is preserved by reindexing: if `a`, `b` exhibit
`b * a = M`, `a * b = N`, the same matrices, reindexed along `e : ι ≃ Fin m`, exhibit
`Mat.MvN ⟨m, reindex e e M⟩ ⟨n, N⟩`. -/
lemma mvN_reindex {A : Type} [Ring A] {ι : Type} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (e : ι ≃ Fin m) {n : ℕ} {M : Matrix ι ι A} {N : Matrix (Fin n) (Fin n) A}
    (a : Matrix (Fin n) ι A) (b : Matrix ι (Fin n) A) (hba : b * a = M) (hab : a * b = N) :
    Work.KT.Mat.MvN ⟨m, Matrix.reindex e e M⟩ ⟨n, N⟩ := by
  refine ⟨a.submatrix id (⇑e.symm), b.submatrix (⇑e.symm) id, ?_, ?_⟩
  · rw [← Matrix.submatrix_mul (M := b) (N := a) (e₁ := ⇑e.symm) (e₂ := id) (e₃ := ⇑e.symm)
      Function.bijective_id, hba, Matrix.reindex_apply]
  · rw [← Matrix.submatrix_mul (M := a) (N := b) (e₁ := id) (e₂ := ⇑e.symm) (e₃ := id)
      e.symm.bijective, hab, Matrix.submatrix_id_id]

/-- Naturality of the Gram left inverse on the boundary circle. -/
lemma map_leftInv {n : ℕ} (C : Matrix (Fin n ⊕ Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (hC : IsUnit (Cᴴ * C)) :
    (Ring.inverse (Cᴴ * C) * Cᴴ).map ⇑(bdryRestrict X)
      = Ring.inverse ((C.map ⇑(bdryRestrict X))ᴴ * (C.map ⇑(bdryRestrict X)))
          * (C.map ⇑(bdryRestrict X))ᴴ := by
  have hgram : (Cᴴ * C).map ⇑(bdryRestrict X)
      = (C.map ⇑(bdryRestrict X))ᴴ * (C.map ⇑(bdryRestrict X)) := by
    rw [Matrix.map_mul, Matrix.conjTranspose_map _ (bdryRestrict_semiconj_star X)]
  rw [Matrix.map_mul, Work.KT.Fund.Matrix.map_ringInverse (bdryRestrict X) _ hC, hgram,
    Matrix.conjTranspose_map _ (bdryRestrict_semiconj_star X)]

end KC

/-! ## The Murray–von Neumann equivalence -/

/-- **The clutched idempotent of a pulled-back unit is trivial.**  For the explicit lifts
`gUp X g`, `gUp X g⁻¹` of `u`, `u⁻¹` (constant in the disc variable) the clutched idempotent over
the fibre product `pullAlg2 X` is Murray–von Neumann equivalent to the rank-`n` identity. -/
theorem mvN_clutch_gUp (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (g : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hF : (KC.gUp X (g : Matrix (Fin n) (Fin n) C(X, ℂ))).map ⇑(bdryRestrict X)
      = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (hG : (KC.gUp X (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))).map ⇑(bdryRestrict X)
      = (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) :
    Work.KT.Mat.MvN (clutchIdem X n u (KC.gUp X (g : Matrix (Fin n) (Fin n) C(X, ℂ)))
        (KC.gUp X (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))) hF hG)
      (Work.KT.Mat.one ↥(pullAlg2 X) n) := by
  set ĝ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    KC.gUp X (g : Matrix (Fin n) (Fin n) C(X, ℂ)) with hĝ
  set Ĝ : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
    KC.gUp X (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ)) with hĜ
  have hF' : ĝ.map ⇑(bdryRestrict X) = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := hF
  have hG' : Ĝ.map ⇑(bdryRestrict X) = (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := hG
  -- units
  have hgU : IsUnit ĝ := by rw [hĝ]; exact KC.isUnit_gUp X _ g.isUnit
  have hgIU : IsUnit Ĝ := by rw [hĜ]; exact KC.isUnit_gUp X _ (g⁻¹).isUnit
  have hgio : Ĝ * ĝ = 1 := by
    have h1 : (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ)) * (↑g : Matrix (Fin n) (Fin n) C(X, ℂ))
        = 1 := Units.inv_mul g
    rw [hĜ, hĝ, ← KC.gUp_mul, h1, KC.gUp_one]
  have hu_mul : (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      * (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = 1 := by
    simpa using Units.mul_inv u
  have hu_inv_mul : (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      * (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = 1 := by
    simpa using Units.inv_mul u
  -- the block columns
  set B : Matrix (Fin n ⊕ Fin n) (Fin n) C(X × Ball ℂ, ℂ) := graphB C(X × Ball ℂ, ℂ) ĝ with hB
  set Bc : Matrix (Fin n ⊕ Fin n) (Fin n) C(X × Ball ℂ, ℂ) := recipB C(X × Ball ℂ, ℂ) Ĝ with hBc
  have hBgram : IsUnit (Bᴴ * B) := by rw [hB]; exact KC.isUnit_graphB_gram X ĝ
  have hBcgram : IsUnit (Bcᴴ * Bc) := by rw [hBc]; exact KC.isUnit_recipB_gram X Ĝ
  -- the framed columns over the two discs
  set A₀ : Matrix (Fin n ⊕ Fin n) (Fin n) C(X × Ball ℂ, ℂ) := B * ĝ with hA₀
  set A₁ : Matrix (Fin n ⊕ Fin n) (Fin n) C(X × Ball ℂ, ℂ) := Bc * (ĝ * ĝ) with hA₁
  have hA₀U : IsUnit (A₀ᴴ * A₀) := by
    rw [hA₀]; exact KC.isUnit_conjTranspose_mul_mul _ B ĝ hBgram hgU
  have hA₁U : IsUnit (A₁ᴴ * A₁) := by
    rw [hA₁]; exact KC.isUnit_conjTranspose_mul_mul _ Bc (ĝ * ĝ) hBcgram (hgU.mul hgU)
  -- the two halves agree on the boundary circle
  have hbd : A₀.map ⇑(bdryRestrict X) = A₁.map ⇑(bdryRestrict X) := by
    have hgb : (graphB C(X × Ball ℂ, ℂ) ĝ).map ⇑(bdryRestrict X)
        = graphB C(X × Sph ℂ, ℂ) (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
      rw [(map_graphB_recipB (bdryRestrict X) ĝ).1, hF']
    have hgbc : (recipB C(X × Ball ℂ, ℂ) Ĝ).map ⇑(bdryRestrict X)
        = recipB C(X × Sph ℂ, ℂ) (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
      rw [(map_graphB_recipB (bdryRestrict X) Ĝ).2, hG']
    simp only [hA₀, hA₁, hB, hBc, Matrix.map_mul, hgb, hgbc, hF', hG']
    rw [recipB_eq_graphB_mul C(X × Sph ℂ, ℂ) (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) hu_mul]
    rw [Matrix.mul_assoc]
    have hcancel : (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
        * ((↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
          * (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
        = (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
      rw [← Matrix.mul_assoc (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
        (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)),
        hu_inv_mul, Matrix.one_mul]
    rw [hcancel]
  -- the Gram left inverses over the two discs also agree on the boundary
  set b₀ : Matrix (Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
    Ring.inverse (A₀ᴴ * A₀) * A₀ᴴ with hb₀
  set b₁ : Matrix (Fin n) (Fin n ⊕ Fin n) C(X × Ball ℂ, ℂ) :=
    Ring.inverse (A₁ᴴ * A₁) * A₁ᴴ with hb₁
  have hbdd : b₀.map ⇑(bdryRestrict X) = b₁.map ⇑(bdryRestrict X) := by
    rw [hb₀, hb₁, KC.map_leftInv X A₀ hA₀U, KC.map_leftInv X A₁ hA₁U]
    rw [hbd]
  -- the frame and its left inverse over the fibre product
  set Fm : Matrix (Fin n ⊕ Fin n) (Fin n) ↥(pullAlg2 X) := KC.pairMatR X A₀ A₁ hbd with hFm
  set Gm : Matrix (Fin n) (Fin n ⊕ Fin n) ↥(pullAlg2 X) := KC.pairMatR X b₀ b₁ hbdd with hGm
  have eA₀ : A₀ * b₀ = graphProj C(X × Ball ℂ, ℂ) ĝ := by
    have h : A₀ * b₀ = orthProj C(X × Ball ℂ, ℂ) (graphB C(X × Ball ℂ, ℂ) ĝ) := by
      rw [hb₀, hA₀, hB, KC.orthProj_eq_mul,
        orthProj_mul_unit C(X × Ball ℂ, ℂ) (graphB C(X × Ball ℂ, ℂ) ĝ) ĝ hgU]
    exact h
  have eA₁ : A₁ * b₁ = recipProj C(X × Ball ℂ, ℂ) Ĝ := by
    have h : A₁ * b₁ = orthProj C(X × Ball ℂ, ℂ) (recipB C(X × Ball ℂ, ℂ) Ĝ) := by
      rw [hb₁, hA₁, hBc, KC.orthProj_eq_mul,
        orthProj_mul_unit C(X × Ball ℂ, ℂ) (recipB C(X × Ball ℂ, ℂ) Ĝ) (ĝ * ĝ) (hgU.mul hgU)]
    exact h
  have eb₀ : b₀ * A₀ = 1 := by
    rw [hb₀, hA₀]; exact KC.leftInv_mul _ (B * ĝ) hA₀U
  have eb₁ : b₁ * A₁ = 1 := by
    rw [hb₁, hA₁]; exact KC.leftInv_mul _ (Bc * (ĝ * ĝ)) hA₁U
  have hFG : Fm * Gm
      = pairMat X (graphProj C(X × Ball ℂ, ℂ) ĝ) (recipProj C(X × Ball ℂ, ℂ) Ĝ)
          (clutch_agree X n u ĝ Ĝ hF' hG') := by
    apply KC.mat_ext_rect X
    · simp only [hFm, hGm, Matrix.map_mul, KC.pairMatR_map_prF, pairMat_map_prF]
      exact eA₀
    · simp only [hFm, hGm, Matrix.map_mul, KC.pairMatR_map_prS, pairMat_map_prS]
      exact eA₁
  have hGF : Gm * Fm = 1 := by
    apply KC.mat_ext_rect X
    · simp only [hFm, hGm, Matrix.map_mul, KC.pairMatR_map_prF, Work.KT.Bott.matrix_map_one]
      exact eb₀
    · simp only [hFm, hGm, Matrix.map_mul, KC.pairMatR_map_prS, Work.KT.Bott.matrix_map_one]
      exact eb₁
  exact KC.mvN_reindex (A := ↥(pullAlg2 X)) finSumFinEquiv Gm Fm hFG hGF

/-! ## The main statement -/

theorem kappa_const (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (g : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = Work.KT.Fund.pullMat X (g : Matrix (Fin n) (Fin n) C(X, ℂ))) :
    Work.KT.Fund.kappa X n u = Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) n) := by
  have hF : (KC.gUp X (g : Matrix (Fin n) (Fin n) C(X, ℂ))).map ⇑(bdryRestrict X)
      = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [KC.gUp_bdry, hu]
  have hG : (KC.gUp X (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))).map ⇑(bdryRestrict X)
      = (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [KC.gUp_bdry, KC.pullMat_inv X g u hu]
  have hmvN := mvN_clutch_gUp X n g u hF hG
  have hcls : Work.KT.cls (clutchIdem X n u (KC.gUp X (g : Matrix (Fin n) (Fin n) C(X, ℂ)))
        (KC.gUp X (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))) hF hG)
      = Work.KT.cls (Work.KT.Mat.one ↥(pullAlg2 X) n) :=
    Work.KT.cls_eq_of_mvn (clutchIdem_isIdem X n u _ _ hF hG)
      (Work.KT.Mat.one_isIdem ↥(pullAlg2 X) n) hmvN
  rw [kappa_val X n u]
  rw [Work.KT.clutchIdem_cls_indep X n u (liftOf X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (liftOf X (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
    (KC.gUp X (g : Matrix (Fin n) (Fin n) C(X, ℂ)))
    (KC.gUp X (↑(g⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ)))
    (liftOf_spec X _) (liftOf_spec X _) hF hG]
  rw [hcls]
  have hkg : (k0Glue X) (Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) n))
      = Work.KT.cls (Work.KT.Mat.one ↥(pullAlg2 X) n) := by
    show Work.KT.K0.map (glueEquiv X : C(X × S2, ℂ) →+* ↥(pullAlg2 X))
        (Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) n)) = _
    rw [Work.KT.K0.map_cls _ (Work.KT.Mat.one_isIdem C(X × S2, ℂ) n)]
    congr 1
    exact Work.KT.Bott.Mat.map_one' (glueEquiv X : C(X × S2, ℂ) →+* ↥(pullAlg2 X)) n
  rw [← hkg]
  exact (k0Glue X).symm_apply_apply _

end

end Work.KT.Fund
