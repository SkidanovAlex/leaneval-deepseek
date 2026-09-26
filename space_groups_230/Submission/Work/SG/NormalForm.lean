import Mathlib
import Submission.Work.SG.Defs

/-! Basic API for the lattice normal form (`exists_normal_form`).

This module fixes the vocabulary used by the normal-form construction: the linear part of a
Euclidean isometry, the translation lattice of a crystallographic group, and the coordinate
equivalence `E 3 ≃ₗ[ℝ] (Fin 3 → ℝ)`.  It contains no `sorry`. -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

noncomputable section

/-- The coordinate equivalence `E 3 ≃ₗ[ℝ] (Fin 3 → ℝ)` underlying `WithLp.toLp 2`. -/
def coordLin : E 3 ≃ₗ[ℝ] (Fin 3 → ℝ) := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)

@[simp] lemma coordLin_toLp (z : Fin 3 → ℝ) : coordLin (WithLp.toLp 2 z) = z := rfl

@[simp] lemma coordLin_symm_apply (z : Fin 3 → ℝ) : coordLin.symm z = WithLp.toLp 2 z := rfl

lemma coordLin_apply (x : E 3) : coordLin x = x.ofLp := by
  conv_lhs => rw [← WithLp.toLp_ofLp (p := 2) x]
  rw [coordLin_toLp]

/-- The linear part of a Euclidean isometry. -/
def linPart (g : EuclideanIsom 3) : E 3 ≃ₗ[ℝ] E 3 := g.toAffineEquiv.linear

/-- The affine normal form of a Euclidean isometry: `g x = linPart g x + g 0`. -/
lemma linPart_apply (g : EuclideanIsom 3) (x : E 3) : g x = linPart g x + g 0 := by
  have h := AffineEquiv.map_vadd g.toAffineEquiv (0 : E 3) x
  simpa [linPart, vadd_eq_add] using h

/-- The linear part is multiplicative. -/
lemma linPart_mul (g h : EuclideanIsom 3) : linPart (g * h) = linPart g * linPart h := by
  have h0 : (g * h) 0 = linPart g (h 0) + g 0 := by
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply]
    exact linPart_apply g (h 0)
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.mul_apply]
  have hx : (g * h) x = linPart g (linPart h x) + (linPart g (h 0) + g 0) := by
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply]
    rw [linPart_apply h x, linPart_apply g (linPart h x + h 0), map_add]
    abel
  have hx2 : (g * h) x = linPart (g * h) x + (g * h) 0 := linPart_apply (g * h) x
  rw [h0, hx] at hx2
  exact (add_right_cancel hx2).symm

lemma linPart_one : linPart (1 : EuclideanIsom 3) = 1 := by
  have h1 : linPart (1 : EuclideanIsom 3) * linPart 1 = linPart 1 := by
    rw [← linPart_mul]
    simp
  have h2 : linPart (1 : EuclideanIsom 3) = 1 := by
    calc linPart (1 : EuclideanIsom 3)
        = 1 * linPart (1 : EuclideanIsom 3) := (one_mul _).symm
      _ = ((linPart (1 : EuclideanIsom 3))⁻¹ * linPart 1) * linPart 1 := by rw [inv_mul_cancel]
      _ = (linPart (1 : EuclideanIsom 3))⁻¹ * (linPart 1 * linPart 1) := by rw [mul_assoc]
      _ = (linPart (1 : EuclideanIsom 3))⁻¹ * linPart 1 := by rw [h1]
      _ = 1 := inv_mul_cancel _
  exact h2

lemma linPart_inv (g : EuclideanIsom 3) : linPart g⁻¹ = (linPart g)⁻¹ := by
  have h1 : linPart g * linPart g⁻¹ = 1 := by
    rw [← linPart_mul, mul_inv_cancel, linPart_one]
  exact eq_inv_of_mul_eq_one_right h1

/-- `IsTranslationBy` in terms of the linear part. -/
lemma isTranslationBy_iff (g : EuclideanIsom 3) (v : E 3) :
    IsTranslationBy g v ↔ linPart g = 1 ∧ g 0 = v := by
  constructor
  · intro h
    have h0 : g 0 = v := by simpa using h 0
    have hx : ∀ x : E 3, linPart g x = x := by
      intro x
      have h1 : g x = linPart g x + g 0 := linPart_apply g x
      rw [h x, h0] at h1
      exact (add_right_cancel h1).symm
    exact ⟨LinearEquiv.ext fun x => by simp [hx x], h0⟩
  · rintro ⟨h1, h0⟩ x
    rw [linPart_apply, h1, h0]
    simp

lemma isTranslationBy_zero_iff (g : EuclideanIsom 3) : IsTranslationBy g 0 ↔ g = 1 := by
  rw [isTranslationBy_iff]
  constructor
  · rintro ⟨h1, h0⟩
    ext x
    rw [linPart_apply, h1, h0]
    simp
  · rintro rfl
    exact ⟨linPart_one, by rfl⟩

lemma isTranslationBy_inv {g : EuclideanIsom 3} {v : E 3} (h : IsTranslationBy g v) :
    IsTranslationBy g⁻¹ (-v) := by
  obtain ⟨h1, h0⟩ := (isTranslationBy_iff g v).mp h
  refine (isTranslationBy_iff g⁻¹ (-v)).mpr ⟨?_, ?_⟩
  · rw [linPart_inv, h1]; simp
  · have hm : g (g⁻¹ 0) = 0 := by
      have hmul : (g * g⁻¹) 0 = 0 := by rw [mul_inv_cancel]; rfl
      rwa [AffineIsometryEquiv.coe_mul, Function.comp_apply] at hmul
    have h3 : linPart g (g⁻¹ 0) + g 0 = 0 := by rw [← linPart_apply g (g⁻¹ 0), hm]
    rw [h1, h0] at h3
    exact eq_neg_of_add_eq_zero_left h3

lemma isTranslationBy_mul {g g' : EuclideanIsom 3} {v v' : E 3}
    (hg : IsTranslationBy g v) (hg' : IsTranslationBy g' v') :
    IsTranslationBy (g * g') (v + v') := by
  intro x
  rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, hg' x, hg (x + v')]
  abel

/-- The translation vectors of a subgroup, as an additive subgroup of `E 3`. -/
def transAdd (G : Subgroup (EuclideanIsom 3)) : AddSubgroup (E 3) where
  carrier := {v | ∃ g ∈ G, IsTranslationBy g v}
  zero_mem' := ⟨1, G.one_mem, by intro x; simp⟩
  add_mem' := by
    rintro a b ⟨g, hg, hgv⟩ ⟨g', hg', hg'v⟩
    exact ⟨g * g', G.mul_mem hg hg', isTranslationBy_mul hgv hg'v⟩
  neg_mem' := by
    rintro a ⟨g, hg, hgv⟩
    exact ⟨g⁻¹, G.inv_mem hg, isTranslationBy_inv hgv⟩

/-- The translation lattice of a subgroup of the Euclidean group, as a `ℤ`-submodule of `E 3`. -/
def transLattice (G : Subgroup (EuclideanIsom 3)) : Submodule ℤ (E 3) :=
  AddSubgroup.toIntSubmodule (transAdd G)

lemma mem_transLattice {G : Subgroup (EuclideanIsom 3)} {v : E 3} :
    v ∈ transLattice G ↔ ∃ g ∈ G, IsTranslationBy g v := Iff.rfl


/-- Euclidean isometries preserve norms after removing the translation part. -/
lemma linPart_norm (g : EuclideanIsom 3) (x : E 3) : ‖linPart g x‖ = ‖x‖ := by
  have h : dist (g x) (g 0) = dist x 0 := by
    have h1 : dist (g x) (g 0) = dist x 0 := AffineIsometryEquiv.dist_map g x 0
    exact h1
  rw [dist_eq_norm, dist_eq_norm] at h
  rw [linPart_apply g x, add_sub_cancel_right, sub_zero] at h
  exact h

/-- Linear parts of elements of `G` preserve the translation lattice. -/
lemma linPart_transLattice {G : Subgroup (EuclideanIsom 3)} {g : EuclideanIsom 3} (hg : g ∈ G)
    {v : E 3} (hv : v ∈ transLattice G) : linPart g v ∈ transLattice G := by
  obtain ⟨h, hh, hhv⟩ := mem_transLattice.mp hv
  rw [mem_transLattice]
  refine ⟨g * h * g⁻¹, G.mul_mem (G.mul_mem hg hh) (G.inv_mem hg), ?_⟩
  intro x
  have hx : linPart g (g⁻¹ x) + g 0 = x := by
    rw [← linPart_apply g (g⁻¹ x)]
    simp
  have h1 : (g * h * g⁻¹) x = linPart g (g⁻¹ x) + linPart g v + g 0 := by
    rw [AffineIsometryEquiv.coe_mul, Function.comp_apply, AffineIsometryEquiv.coe_mul,
      Function.comp_apply, hhv (g⁻¹ x), linPart_apply g (g⁻¹ x + v), map_add]
  rw [h1]
  calc linPart g (g⁻¹ x) + linPart g v + g 0
      = (linPart g (g⁻¹ x) + g 0) + linPart g v := by abel
    _ = x + linPart g v := by rw [hx]

/-- Linear parts of elements of `G` preserve the translation lattice (iff form). -/
lemma linPart_transLattice_iff {G : Subgroup (EuclideanIsom 3)} {g : EuclideanIsom 3}
    (hg : g ∈ G) {v : E 3} : linPart g v ∈ transLattice G ↔ v ∈ transLattice G := by
  refine ⟨?_, linPart_transLattice hg⟩
  intro h
  have h1 : linPart g⁻¹ (linPart g v) ∈ transLattice G :=
    linPart_transLattice (G := G) (g := g⁻¹) (G.inv_mem hg) h
  have h2 : linPart g⁻¹ (linPart g v) = v := by
    rw [linPart_inv]
    exact LinearEquiv.symm_apply_apply _ _
  rwa [h2] at h1

/-- The coordinate model of the linear part of `g` in the coordinates of `T`. -/
def lmap (T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3) (g : EuclideanIsom 3) :
    (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  (T.trans (linPart g)).trans T.symm

lemma lmap_apply (T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3) (g : EuclideanIsom 3) (x : Fin 3 → ℝ) :
    lmap T g x = T.symm (linPart g (T x)) := rfl

lemma lmap_mul (T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3) (g h : EuclideanIsom 3) :
    lmap T (g * h) = lmap T g * lmap T h := by
  rw [lmap, lmap, lmap, linPart_mul]
  ext x
  simp [LinearEquiv.mul_apply]

lemma lmap_one (T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3) : lmap T 1 = 1 := by
  rw [lmap, linPart_one]
  ext x
  simp

lemma lmap_inv (T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3) (g : EuclideanIsom 3) :
    lmap T g⁻¹ = (lmap T g)⁻¹ := by
  have h : lmap T g * lmap T g⁻¹ = 1 := by
    rw [← lmap_mul, mul_inv_cancel, lmap_one]
  exact eq_inv_of_mul_eq_one_right h

/-- The linear part of the conjugating map `φ = x ↦ T⁻¹ x` (with `T` viewed as coordinates). -/
def affLin (T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3) : E 3 ≃ₗ[ℝ] E 3 :=
  T.symm.trans coordLin.symm

lemma affLin_apply (T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3) (x : E 3) :
    affLin T x = WithLp.toLp 2 (T.symm x) := rfl

lemma affLin_symm_apply (T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3) (y : E 3) :
    (affLin T).symm y = T (coordLin y) := by
  rw [affLin, LinearEquiv.trans_symm]
  rfl

/-- Integer matrices act on `ℤ³` as on the integer vectors. -/
lemma matMulVec_intVec (A : IMat) (n : Fin 3 → ℤ) :
    (A.map (Int.cast : ℤ → ℝ)).mulVec (intVec n) = intVec (A.mulVec n) := by
  funext i
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) A n i).symm


/-! ### Integer vectors -/

private lemma intVec_add (n m : Fin 3 → ℤ) : intVec (n + m) = intVec n + intVec m := by
  ext i; simp [intVec]

private lemma intVec_sub (n m : Fin 3 → ℤ) : intVec (n - m) = intVec n - intVec m := by
  ext i; simp [intVec]

private lemma intVec_neg (n : Fin 3 → ℤ) : intVec (-n) = -intVec n := by
  ext i; simp [intVec]

private lemma intVec_zero : intVec (0 : Fin 3 → ℤ) = 0 := by
  ext i; simp [intVec]

lemma intVec_single_nf (j : Fin 3) : intVec (Pi.single j (1 : ℤ)) = Pi.single j (1 : ℝ) := by
  ext i; by_cases h : i = j <;> simp [intVec, h]

lemma intVec_injective_nf : Function.Injective (intVec : (Fin 3 → ℤ) → Fin 3 → ℝ) :=
  fun n m h => funext fun i => Int.cast_injective (congrFun h i)


lemma toLp_add (a b : Fin 3 → ℝ) :
    WithLp.toLp 2 (a + b) = WithLp.toLp 2 a + WithLp.toLp 2 b := rfl


lemma lmap_coe_apply (T : (Fin 3 → ℝ) ≃ₗ[ℝ] E 3) (g : EuclideanIsom 3) (x : Fin 3 → ℝ) :
    (lmap T g : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) x = T.symm (linPart g (T x)) := rfl

lemma matMap_mul (A B : IMat) :
    ((A * B).map (Int.cast : ℤ → ℝ))
      = (A.map (Int.cast : ℤ → ℝ)) * (B.map (Int.cast : ℤ → ℝ)) := by
  have h : ((A * B).map (Int.castRingHom ℝ))
      = (A.map (Int.castRingHom ℝ)) * (B.map (Int.castRingHom ℝ)) := Matrix.map_mul
  simpa using h

lemma matMap_one : ((1 : IMat).map (Int.cast : ℤ → ℝ)) = 1 := by
  have h : ((1 : IMat).map (Int.castRingHom ℝ)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simpa using h

lemma toLin'_matMap_mul (A B : IMat) :
    Matrix.toLin' ((A * B).map (Int.cast : ℤ → ℝ))
      = Matrix.toLin' (A.map (Int.cast : ℤ → ℝ))
        ∘ₗ Matrix.toLin' (B.map (Int.cast : ℤ → ℝ)) := by
  rw [matMap_mul, Matrix.toLin'_mul]


lemma toAffineEquiv_apply_eq (g : EuclideanIsom 3) (x : E 3) : g.toAffineEquiv x = g x := by
  rw [AffineIsometryEquiv.coe_toAffineEquiv]


end

end Work.SG
