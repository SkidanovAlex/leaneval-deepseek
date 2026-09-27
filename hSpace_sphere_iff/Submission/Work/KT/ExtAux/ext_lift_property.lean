import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.ExtProdB

namespace Work.KT.ExtAux

open Matrix

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 4000000

section Basic

variable (V W : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]
variable (y0V : Ball V) (y0W : Ball W)

lemma wedgePr₁_wedgeProj_pullFst (g : Kpair V) :
    wedgePr₁ V W y0V y0W (wedgeProj V W y0V y0W (pullFst V W g)) = g := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (g : C(Ball V, ℂ)) (prFst V W (ballProd V W x y0W)) = (g : C(Ball V, ℂ)) x
  rw [prFst_ballProd]

lemma wedgePr₂_wedgeProj_pullFst (g : Kpair V) :
    wedgePr₂ V W y0V y0W (wedgeProj V W y0V y0W (pullFst V W g))
      = algebraMap ℂ (Kpair W) (augPair V y0V g) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (g : C(Ball V, ℂ)) (prFst V W (ballProd V W y0V x)) = (g : C(Ball V, ℂ)) y0V
  rw [prFst_ballProd]

lemma wedgePr₁_wedgeProj_pullSnd (h : Kpair W) :
    wedgePr₁ V W y0V y0W (wedgeProj V W y0V y0W (pullSnd V W h))
      = algebraMap ℂ (Kpair V) (augPair W y0W h) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (h : C(Ball W, ℂ)) (prSnd V W (ballProd V W x y0W)) = (h : C(Ball W, ℂ)) y0W
  rw [prSnd_ballProd]

lemma wedgePr₂_wedgeProj_pullSnd (h : Kpair W) :
    wedgePr₂ V W y0V y0W (wedgeProj V W y0V y0W (pullSnd V W h)) = h := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (h : C(Ball W, ℂ)) (prSnd V W (ballProd V W y0V x)) = (h : C(Ball W, ℂ)) x
  rw [prSnd_ballProd]

lemma wedgeAlg_ext {x y : wedgeAlg V W y0V y0W}
    (h₁ : wedgePr₁ V W y0V y0W x = wedgePr₁ V W y0V y0W y)
    (h₂ : wedgePr₂ V W y0V y0W x = wedgePr₂ V W y0V y0W y) : x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

end Basic

section General

lemma isUnit_map_matrix {n : ℕ} {A B : Type} [Semiring A] [Semiring B] (f : A →+* B)
    (M : Matrix (Fin n) (Fin n) A) (h : IsUnit M) : IsUnit (M.map f) := by
  have h' := IsUnit.map (RingHom.mapMatrix (m := Fin n) f) h
  rwa [RingHom.mapMatrix_apply] at h'

lemma reindex_fromBlocks_self {n : ℕ} {R : Type} [Semiring R] (u : Matrix (Fin n) (Fin n) R) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks u 0 0 (1 : Matrix (Fin 0) (Fin 0) R)) = u := by
  have hsymm : ∀ i : Fin (n + 0), finSumFinEquiv.symm i = Sum.inl i := by
    intro i
    have h : finSumFinEquiv (Sum.inl i) = i := by
      rw [finSumFinEquiv_apply_left]; rfl
    rw [show finSumFinEquiv.symm i = finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)) from
      congrArg finSumFinEquiv.symm h.symm, Equiv.symm_apply_apply]
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, hsymm i, hsymm j,
    Matrix.fromBlocks_apply₁₁]

end General

section Main

variable (V W : Type) [NormedAddCommGroup V] [NormedAddCommGroup W]
variable (y0V : Ball V) (y0W : Ball W)

lemma lift_exists (n : ℕ) (u : Matrix (Fin n) (Fin n) (wedgeAlg V W y0V y0W)) (hu : IsUnit u) :
    ∃ w : Matrix (Fin n) (Fin n) (prodAlg V W),
      IsUnit w ∧ w.map (wedgeProj V W y0V y0W) = u := by
  set u₁ : Matrix (Fin n) (Fin n) (Kpair V) := u.map (wedgePr₁ V W y0V y0W) with hu₁def
  set u₂ : Matrix (Fin n) (Fin n) (Kpair W) := u.map (wedgePr₂ V W y0V y0W) with hu₂def
  set u₀ : Matrix (Fin n) (Fin n) ℂ := u₁.map (augPair V y0V) with hu₀def
  have hcomp : u₀ = u₂.map (augPair W y0W) := by
    rw [hu₀def, hu₁def, hu₂def]
    ext i j
    exact (u i j).2
  have hu₁ : IsUnit u₁ := by
    rw [hu₁def]
    exact isUnit_map_matrix (wedgePr₁ V W y0V y0W : wedgeAlg V W y0V y0W →+* Kpair V) u hu
  have hu₂ : IsUnit u₂ := by
    rw [hu₂def]
    exact isUnit_map_matrix (wedgePr₂ V W y0V y0W : wedgeAlg V W y0V y0W →+* Kpair W) u hu
  have hu₀ : IsUnit u₀ := by
    rw [hu₀def]
    exact isUnit_map_matrix (augPair V y0V : Kpair V →+* ℂ) u₁ hu₁
  set u₀inv : Matrix (Fin n) (Fin n) ℂ :=
    (↑((hu₀.unit)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) with hu₀invdef
  have hle : u₀inv * u₀ = 1 := by
    have h : (↑((hu₀.unit)⁻¹ * hu₀.unit) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      rw [inv_mul_cancel, Units.val_one]
    rw [Units.val_mul, hu₀.unit_spec] at h
    rwa [hu₀invdef]
  have hre : u₀ * u₀inv = 1 := by
    have h : (↑(hu₀.unit * (hu₀.unit)⁻¹) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      rw [mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, hu₀.unit_spec] at h
    rwa [hu₀invdef]
  set A₁ : Matrix (Fin n) (Fin n) (prodAlg V W) := u₁.map (pullFst V W) with hA₁def
  set A₂ : Matrix (Fin n) (Fin n) (prodAlg V W) := u₂.map (pullSnd V W) with hA₂def
  set Cc : Matrix (Fin n) (Fin n) (prodAlg V W) := u₀inv.map (algebraMap ℂ (prodAlg V W)) with hCcdef
  set w : Matrix (Fin n) (Fin n) (prodAlg V W) := A₁ * Cc * A₂ with hwdef
  have hA₁u : IsUnit A₁ := by
    rw [hA₁def]; exact isUnit_map_matrix (pullFst V W : Kpair V →+* prodAlg V W) u₁ hu₁
  have hA₂u : IsUnit A₂ := by
    rw [hA₂def]; exact isUnit_map_matrix (pullSnd V W : Kpair W →+* prodAlg V W) u₂ hu₂
  have hCcu : IsUnit Cc := by
    rw [hCcdef]
    exact isUnit_map_matrix (algebraMap ℂ (prodAlg V W)) u₀inv ⟨(hu₀.unit)⁻¹, by rw [hu₀invdef]⟩
  have hA₁map₁ : (A₁.map (wedgeProj V W y0V y0W)).map (wedgePr₁ V W y0V y0W) = u₁ := by
    rw [hA₁def]; ext i j
    simp only [Matrix.map_apply, wedgePr₁_wedgeProj_pullFst]
  have hA₂map₁ : (A₂.map (wedgeProj V W y0V y0W)).map (wedgePr₁ V W y0V y0W)
      = (u₂.map (augPair W y0W)).map (algebraMap ℂ (Kpair V)) := by
    rw [hA₂def]; ext i j
    simp only [Matrix.map_apply, wedgePr₁_wedgeProj_pullSnd]
  have hCmap₁ : (Cc.map (wedgeProj V W y0V y0W)).map (wedgePr₁ V W y0V y0W)
      = u₀inv.map (algebraMap ℂ (Kpair V)) := by
    rw [hCcdef]; ext i j
    simp only [Matrix.map_apply, AlgHom.commutes]
  have hA₁map₂ : (A₁.map (wedgeProj V W y0V y0W)).map (wedgePr₂ V W y0V y0W)
      = (u₁.map (augPair V y0V)).map (algebraMap ℂ (Kpair W)) := by
    rw [hA₁def]; ext i j
    simp only [Matrix.map_apply, wedgePr₂_wedgeProj_pullFst]
  have hA₂map₂ : (A₂.map (wedgeProj V W y0V y0W)).map (wedgePr₂ V W y0V y0W) = u₂ := by
    rw [hA₂def]; ext i j
    simp only [Matrix.map_apply, wedgePr₂_wedgeProj_pullSnd]
  have hCmap₂ : (Cc.map (wedgeProj V W y0V y0W)).map (wedgePr₂ V W y0V y0W)
      = u₀inv.map (algebraMap ℂ (Kpair W)) := by
    rw [hCcdef]; ext i j
    simp only [Matrix.map_apply, AlgHom.commutes]
  have hXY : (u₀inv.map (algebraMap ℂ (Kpair V))) * (u₀.map (algebraMap ℂ (Kpair V))) = 1 := by
    rw [← Matrix.map_mul, hle,
      Matrix.map_one (algebraMap ℂ (Kpair V)) (map_zero _) (map_one _)]
  have hXY' : (u₀.map (algebraMap ℂ (Kpair W))) * (u₀inv.map (algebraMap ℂ (Kpair W))) = 1 := by
    rw [← Matrix.map_mul, hre,
      Matrix.map_one (algebraMap ℂ (Kpair W)) (map_zero _) (map_one _)]
  have key₁ : (w.map (wedgeProj V W y0V y0W)).map (wedgePr₁ V W y0V y0W) = u₁ := by
    rw [hwdef, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
    rw [hA₁map₁, hCmap₁, hA₂map₁, ← hcomp, mul_assoc, hXY, mul_one]
  have key₂ : (w.map (wedgeProj V W y0V y0W)).map (wedgePr₂ V W y0V y0W) = u₂ := by
    rw [hwdef, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
    rw [hA₁map₂, hCmap₂, hA₂map₂, ← hu₀def, hXY', one_mul]
  refine ⟨w, ?_, ?_⟩
  · rw [hwdef]; exact (hA₁u.mul hCcu).mul hA₂u
  · apply Matrix.ext
    intro i j
    refine wedgeAlg_ext V W y0V y0W ?_ ?_
    · have h := congrFun (congrFun key₁ i) j
      simpa only [Matrix.map_apply, hu₁def] using h
    · have h := congrFun (congrFun key₂ i) j
      simpa only [Matrix.map_apply, hu₂def] using h

end Main

/-- Every invertible matrix over the wedge algebra `C(S^a ∨ S^b) = C(S^a) ×_ℂ C(S^b)` stably lifts to an invertible matrix over `C(S^a × S^b)`.  Writing `u = (u₁, u₂)` for the two projections (with common basepoint value `u₀`) the explicit lift is `V(x,y) = u₁(x)·u₀⁻¹·u₂(y)`, which is invertible and maps to `u` under the restriction `wedgeProj`; hence `k = 0` suffices.  (The `set_option` is needed because the `Zero`/`One` instances for matrices over a nested subalgebra are expensive to synthesise.) -/
theorem ext_lift_property (V W : Type) [NormedAddCommGroup V] [NormedAddCommGroup W] (y0V : Ball V) (hV : y0V ∈ bdry V) (y0W : Ball W) (hW : y0W ∈ bdry W) (n : ℕ) (u : Matrix (Fin n) (Fin n) (wedgeAlg V W y0V y0W)) (hu : IsUnit u) : ∃ (k : ℕ) (v : Matrix (Fin (n + k)) (Fin (n + k)) (prodAlg V W)), IsUnit v ∧ v.map (wedgeProj V W y0V y0W) = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u 0 0 1) := by
  obtain ⟨w, hw_unit, hw_map⟩ := lift_exists V W y0V y0W n u hu
  refine ⟨0, w, hw_unit, ?_⟩
  rw [hw_map]
  exact (reindex_fromBlocks_self u).symm

end Work.KT.ExtAux
