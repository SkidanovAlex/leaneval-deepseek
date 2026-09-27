import Mathlib
import Submission.Work.KT.Fund.kbi_defs
import Submission.Work.KT.Fund.kappa_homotopic

/-!
# `Work.KT.Fund.kbi_hu` — the clutching identity for the Bott construction

This is the boundary ("gluing") identity of the explicit trivialisation of the target
`2n × 2n` idempotent used in the proof of `Work.KT.Fund.kappa_bott`.

Setup (`Work.KT.Fund.KBI`): on each disc one trivialises `P ⊗ H ⊕ Q` (`H` the Hopf line),
with frames `TBip` (`TB1p`, `TB2p`), retractions `SAip`, and disc-images `Wip` of the target
idempotent.  For the clutching function `u = Q + z·P` (`Q = 1 - P`, `z` the circle
coordinate) the two trivialisations must agree on the boundary circle `|ζ| = 1`:

* `u · (SA1|) = SA2|` and `TB1| = TB2| · u`.

Everything is a boundary-value computation: on the circle `ζ ↦ z`, `ζ̄ ↦ z⁻¹`,
`c = (1+|ζ|²)⁻¹ ↦ 1/2`, and the disc lifts `Pd`, `Qd` restrict to `pullMat X P`,
`1 - pullMat X P`.  The remaining algebra is done once over an arbitrary commutative ring
(`smulB_mul_smulB`, `smulB_mul_smulB2`, `B_mul_smulB`, `key1_generic`, `key2_generic`), using
only `B * B = B`, `z * z⁻¹ = 1`.
-/

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

set_option linter.unusedSectionVars false

/-! ## `Matrix.map` along a ring homomorphism -/

private lemma map_add_rh {m n : Type*} {α β : Type*} [NonAssocSemiring α] [NonAssocSemiring β]
    (f : α →+* β) (M N : Matrix m n α) : (M + N).map f = M.map f + N.map f :=
  Matrix.map_add f (fun a b => f.map_add a b) M N

private lemma map_sub_rh {m n : Type*} {α β : Type*} [NonAssocRing α] [NonAssocRing β]
    (f : α →+* β) (M N : Matrix m n α) : (M - N).map f = M.map f - N.map f :=
  Matrix.map_sub f (fun a b => f.map_sub a b) M N

private lemma map_one_rh {n : Type*} [DecidableEq n] {α β : Type*} [NonAssocSemiring α]
    [NonAssocSemiring β] (f : α →+* β) : (1 : Matrix n n α).map f = 1 :=
  Matrix.map_one f f.map_zero f.map_one

private lemma map_smul_rh {n : Type*} {α β : Type*} [NonAssocRing α] [NonAssocRing β]
    (f : α →+* β) (r : α) (A : Matrix n n α) : (r • A).map f = f r • A.map f :=
  Matrix.map_smul' f r A (fun a b => f.map_mul a b)

/-! ## Elementary matrix algebra over a commutative ring -/

private lemma smulB_mul_smulB {S : Type} [CommRing S] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) S) (hB : B * B = B) (a b : S) :
    ((1 - B) + a • B) * ((1 - B) + b • B) = (1 - B) + (a * b) • B := by
  have hCB : (1 - B) * B = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hB, sub_self]
  have hBC : B * (1 - B) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hB, sub_self]
  have hCC : (1 - B) * (1 - B) = 1 - B := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hB]; abel
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hCC,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hCB, hBC, hB, smul_smul]
  simp

private lemma smulB_mul_smulB2 {S : Type} [CommRing S] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) S) (hB : B * B = B) (a b : S) :
    ((1 - B) + a • B) * (b • B) = (a * b) • B := by
  have hCB : (1 - B) * B = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hB, sub_self]
  rw [Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, hCB, hB, smul_smul]
  simp

private lemma B_mul_smulB {S : Type} [CommRing S] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) S) (hB : B * B = B) (a : S) :
    B * ((1 - B) + a • B) = a • B := by
  have hBC : B * (1 - B) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hB, sub_self]
  rw [Matrix.mul_add, Matrix.mul_smul, hBC, hB]
  simp

/-- The algebraic core of the first gluing identity. -/
private lemma key1_generic {S : Type} [CommRing S] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) S) (hB : B * B = B)
    (z zi hf : S) (hzz : z * zi = 1)
    (R0m R1m : Matrix (Fin n) (Fin n × Fin 2) S) :
    ((1 - B) + z • B) * (((1 - B) + hf • B) * R0m + ((hf * zi) • B) * R1m)
      = ((1 - B) + (hf * z) • B) * R0m + (hf • B) * R1m := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    smulB_mul_smulB B hB z hf, smulB_mul_smulB2 B hB z (hf * zi),
    mul_comm z hf, show z * (hf * zi) = hf from by
      rw [← mul_assoc, mul_comm z hf, mul_assoc, hzz, mul_one]]

/-- The algebraic core of the second gluing identity. -/
private lemma key2_generic {S : Type} [CommRing S] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) S) (hB : B * B = B)
    (z zi : S) (hzz : zi * z = 1)
    (D0m D1m : Matrix (Fin n × Fin 2) (Fin n) S) :
    D0m + D1m * (z • B)
      = (D0m * ((1 - B) + zi • B) + D1m * B) * ((1 - B) + z • B) := by
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    smulB_mul_smulB B hB zi z, B_mul_smulB B hB z, hzz, one_smul,
    show (1 - B) + B = 1 from by abel]
  rw [Matrix.mul_one]

/-! ## The boundary values of the disc data -/

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

private lemma hPull (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P) :
    pullMat X P * pullMat X P = pullMat X P := by
  rw [KC.pullMat_eq_map X P, ← Matrix.map_mul, hP]

private lemma pullMat_one_sub (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    pullMat X (1 - P) = 1 - pullMat X P := by
  rw [KC.pullMat_eq_map, KC.pullMat_eq_map, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
    map_sub, map_one]

variable (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ))

private lemma hPd : (KBI.Pd X n P).map ⇑(bdryRestrict X) = pullMat X P := KC.gUp_bdry X P

private lemma hQd : (KBI.Qd X n P).map ⇑(bdryRestrict X) = 1 - pullMat X P := by
  have h : (KBI.Qd X n P) = 1 - KBI.Pd X n P := rfl
  rw [h, map_sub_rh, map_one_rh, hPd]

private lemma hsm (a : KBI.kdD X) :
    (KBI.sm X n P a).map ⇑(bdryRestrict X) = (bdryRestrict X a) • pullMat X P := by
  have h : KBI.sm X n P a = a • KBI.Pd X n P := by ext i j; rfl
  rw [h, map_smul_rh, hPd]

/-! ## The four boundary computations -/

private lemma SA1p_bdry :
    (KBI.SA1p X n P).map ⇑(bdryRestrict X)
      = ((1 - pullMat X P) + (ContinuousMap.const (X × Work.KT.Sph ℂ) (1/2 : ℂ)) • pullMat X P)
          * (KBI.R0 X n).map ⇑(bdryRestrict X)
        + (((ContinuousMap.const (X × Work.KT.Sph ℂ) (1/2 : ℂ))
              * (↑(Work.KT.zUnit X)⁻¹ : C(X × Work.KT.Sph ℂ, ℂ))) • pullMat X P)
          * (KBI.R1 X n).map ⇑(bdryRestrict X) := by
  have h1 : (KBI.Qd X n P + KBI.sm X n P (KBI.zcn X)).map ⇑(bdryRestrict X)
      = (1 - pullMat X P)
        + (ContinuousMap.const (X × Work.KT.Sph ℂ) (1/2 : ℂ)) • pullMat X P := by
    rw [map_add_rh, hQd, hsm, KBI.bdryRestrict_zcn]
  have h2 : (KBI.sm X n P (KBI.zcn X * KBI.zcb X)).map ⇑(bdryRestrict X)
      = ((ContinuousMap.const (X × Work.KT.Sph ℂ) (1/2 : ℂ))
          * (↑(Work.KT.zUnit X)⁻¹ : C(X × Work.KT.Sph ℂ, ℂ))) • pullMat X P := by
    rw [hsm, map_mul, KBI.bdryRestrict_zcn, KBI.bdryRestrict_zcb]
  rw [KBI.SA1p, map_add_rh, Matrix.map_mul, Matrix.map_mul, h1, h2]

private lemma SA2p_bdry :
    (KBI.SA2p X n P).map ⇑(bdryRestrict X)
      = ((1 - pullMat X P)
            + ((ContinuousMap.const (X × Work.KT.Sph ℂ) (1/2 : ℂ))
                * (Work.KT.zUnit X : C(X × Work.KT.Sph ℂ, ℂ))) • pullMat X P)
          * (KBI.R0 X n).map ⇑(bdryRestrict X)
        + ((ContinuousMap.const (X × Work.KT.Sph ℂ) (1/2 : ℂ)) • pullMat X P)
          * (KBI.R1 X n).map ⇑(bdryRestrict X) := by
  have h1 : (KBI.Qd X n P + KBI.sm X n P (KBI.zcn X * KBI.zc X)).map ⇑(bdryRestrict X)
      = (1 - pullMat X P)
        + ((ContinuousMap.const (X × Work.KT.Sph ℂ) (1/2 : ℂ))
            * (Work.KT.zUnit X : C(X × Work.KT.Sph ℂ, ℂ))) • pullMat X P := by
    rw [map_add_rh, hQd, hsm, map_mul, KBI.bdryRestrict_zcn, KBI.bdryRestrict_zc]
  have h2 : (KBI.sm X n P (KBI.zcn X)).map ⇑(bdryRestrict X)
      = (ContinuousMap.const (X × Work.KT.Sph ℂ) (1/2 : ℂ)) • pullMat X P := by
    rw [hsm, KBI.bdryRestrict_zcn]
  rw [KBI.SA2p, map_add_rh, Matrix.map_mul, Matrix.map_mul, h1, h2]

private lemma TB1p_bdry :
    (KBI.TB1p X n P).map ⇑(bdryRestrict X)
      = (KBI.D0 X n).map ⇑(bdryRestrict X)
        + (KBI.D1 X n).map ⇑(bdryRestrict X)
          * ((Work.KT.zUnit X : C(X × Work.KT.Sph ℂ, ℂ)) • pullMat X P) := by
  have h1 : (KBI.sm X n P (KBI.zc X)).map ⇑(bdryRestrict X)
      = (Work.KT.zUnit X : C(X × Work.KT.Sph ℂ, ℂ)) • pullMat X P := by
    rw [hsm, KBI.bdryRestrict_zc]
  rw [KBI.TB1p, map_add_rh, Matrix.map_mul, h1]

private lemma TB2p_bdry :
    (KBI.TB2p X n P).map ⇑(bdryRestrict X)
      = (KBI.D0 X n).map ⇑(bdryRestrict X)
          * ((1 - pullMat X P)
              + (↑(Work.KT.zUnit X)⁻¹ : C(X × Work.KT.Sph ℂ, ℂ)) • pullMat X P)
        + (KBI.D1 X n).map ⇑(bdryRestrict X) * pullMat X P := by
  have h1 : (KBI.Qd X n P + KBI.sm X n P (KBI.zcb X)).map ⇑(bdryRestrict X)
      = (1 - pullMat X P)
        + (↑(Work.KT.zUnit X)⁻¹ : C(X × Work.KT.Sph ℂ, ℂ)) • pullMat X P := by
    rw [map_add_rh, hQd, hsm, KBI.bdryRestrict_zcb]
  rw [KBI.TB2p, map_add_rh, Matrix.map_mul, Matrix.map_mul, h1, hPd]

/-! ## Transport across the `Fin (n*2)` reindexing -/

private lemma reindex_rf_mul (A : Matrix (Fin n) (Fin n) (C(X × Work.KT.Sph ℂ, ℂ)))
    (M : Matrix (Fin n) (Fin n × Fin 2) (C(X × Work.KT.Sph ℂ, ℂ))) :
    A * Matrix.reindex (Equiv.refl (Fin n)) finProdFinEquiv M
      = Matrix.reindex (Equiv.refl (Fin n)) finProdFinEquiv (A * M) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm,
    Equiv.coe_refl, id_eq]

private lemma reindex_fr_mul (M : Matrix (Fin n × Fin 2) (Fin n) (C(X × Work.KT.Sph ℂ, ℂ)))
    (A : Matrix (Fin n) (Fin n) (C(X × Work.KT.Sph ℂ, ℂ))) :
    Matrix.reindex finProdFinEquiv (Equiv.refl (Fin n)) M * A
      = Matrix.reindex finProdFinEquiv (Equiv.refl (Fin n)) (M * A) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm,
    Equiv.coe_refl, id_eq]

/-! ## The gluing identities at the `Fin n × Fin 2` level -/

private lemma kbi_hu_SA (hP : P * P = P)
    (u : (Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))
      = pullMat X (1 - P) + (Work.KT.zUnit X : C(X × Work.KT.Sph ℂ, ℂ)) • pullMat X P) :
    ((u : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))
        * (KBI.SA1p X n P).map ⇑(bdryRestrict X)
        = (KBI.SA2p X n P).map ⇑(bdryRestrict X)) := by
  rw [hu, pullMat_one_sub, SA1p_bdry, SA2p_bdry]
  exact key1_generic (pullMat X P) (hPull X n P hP) (Work.KT.zUnit X : C(X × Work.KT.Sph ℂ, ℂ))
    (↑(Work.KT.zUnit X)⁻¹ : C(X × Work.KT.Sph ℂ, ℂ))
    (ContinuousMap.const (X × Work.KT.Sph ℂ) (1/2 : ℂ)) (Units.mul_inv (Work.KT.zUnit X))
    ((KBI.R0 X n).map ⇑(bdryRestrict X)) ((KBI.R1 X n).map ⇑(bdryRestrict X))

private lemma kbi_hu_TB (hP : P * P = P)
    (u : (Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))
      = pullMat X (1 - P) + (Work.KT.zUnit X : C(X × Work.KT.Sph ℂ, ℂ)) • pullMat X P) :
    ((KBI.TB1p X n P).map ⇑(bdryRestrict X)
        = (KBI.TB2p X n P).map ⇑(bdryRestrict X)
          * (u : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))) := by
  rw [hu, pullMat_one_sub, TB1p_bdry, TB2p_bdry]
  exact key2_generic (pullMat X P) (hPull X n P hP) (Work.KT.zUnit X : C(X × Work.KT.Sph ℂ, ℂ))
    (↑(Work.KT.zUnit X)⁻¹ : C(X × Work.KT.Sph ℂ, ℂ)) (Units.inv_mul (Work.KT.zUnit X))
    ((KBI.D0 X n).map ⇑(bdryRestrict X)) ((KBI.D1 X n).map ⇑(bdryRestrict X))

end

end Work.KT.Fund

namespace Work.KT.Fund

theorem kbi_hu (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P)
    (u : (Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))ˣ)
    (hu : (u : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))
      = Work.KT.Fund.pullMat X (1 - P)
        + (Work.KT.zUnit X : C(X × Work.KT.Sph ℂ, ℂ)) • Work.KT.Fund.pullMat X P) :
    ((u : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))
        * (Work.KT.Fund.KBI.SA1 X n P).map (fun f => Work.KT.Fund.bdryRestrict X f)
        = (Work.KT.Fund.KBI.SA2 X n P).map (fun f => Work.KT.Fund.bdryRestrict X f)) ∧
      ((Work.KT.Fund.KBI.TB1 X n P).map (fun f => Work.KT.Fund.bdryRestrict X f)
        = (Work.KT.Fund.KBI.TB2 X n P).map (fun f => Work.KT.Fund.bdryRestrict X f)
          * (u : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))) := by
  change ((u : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ))
        * (Work.KT.Fund.KBI.SA1 X n P).map ⇑(Work.KT.Fund.bdryRestrict X)
        = (Work.KT.Fund.KBI.SA2 X n P).map ⇑(Work.KT.Fund.bdryRestrict X)) ∧
      ((Work.KT.Fund.KBI.TB1 X n P).map ⇑(Work.KT.Fund.bdryRestrict X)
        = (Work.KT.Fund.KBI.TB2 X n P).map ⇑(Work.KT.Fund.bdryRestrict X)
          * (u : Matrix (Fin n) (Fin n) C(X × Work.KT.Sph ℂ, ℂ)))
  refine ⟨?_, ?_⟩
  · have key := kbi_hu_SA X n P hP u hu
    rw [KBI.SA1, KBI.SA2, KBI.reindex_map_rf X n (M := KBI.SA1p X n P) (bdryRestrict X),
      KBI.reindex_map_rf X n (M := KBI.SA2p X n P) (bdryRestrict X), reindex_rf_mul]
    exact congrArg (Matrix.reindex (Equiv.refl (Fin n)) finProdFinEquiv) key
  · have key := kbi_hu_TB X n P hP u hu
    rw [KBI.TB1, KBI.TB2, KBI.reindex_map_fr X n (M := KBI.TB1p X n P) (bdryRestrict X),
      KBI.reindex_map_fr X n (M := KBI.TB2p X n P) (bdryRestrict X), reindex_fr_mul]
    exact congrArg (Matrix.reindex finProdFinEquiv (Equiv.refl (Fin n))) key

end Work.KT.Fund
