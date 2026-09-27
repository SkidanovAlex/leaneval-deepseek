import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kappa_add_defs
import Submission.Work.KT.kappa_span
import Submission.Work.KT.Bott.GlueAux
import Submission.Work.KT.cls_eq_stable_mvN
import Submission.Work.KT.RelGen.star_left_inverse
import Submission.Work.KT.ExtGen.disc_square

namespace Work.KT.FP

noncomputable section

set_option maxHeartbeats 1600000

/-! ## 1. The generic two-disc sandwich -/

section Sandwich

variable {R : Type} [Ring R]

/-- **The two-disc sandwich.** Let `B B' : m × d` be "columns" with left inverses `C C' : d × m`
(`C * B = 1`, `C' * B' = 1`), and let `a b : m × m` be Murray--von Neumann data for the
idempotents `B * C = b * a` and `B' * C' = a * b`.  Then the "sandwiches" `C' a B` and `C b B'`
are mutually inverse `d × d` matrices. -/
theorem sandwich_mul_eq_one {m d : ℕ}
    (B B' : Matrix (Fin m) (Fin d) R) (C C' : Matrix (Fin d) (Fin m) R)
    (a b : Matrix (Fin m) (Fin m) R)
    (hCB : C * B = 1) (hC'B' : C' * B' = 1)
    (hBC : B * C = b * a) (hB'C' : B' * C' = a * b)
    (hp : (b * a) * (b * a) = b * a) (hq : (a * b) * (a * b) = a * b) :
    (C' * a * B) * (C * b * B') = 1 ∧ (C * b * B') * (C' * a * B) = 1 := by
  constructor
  · have h1 : a * (B * C) * b = B' * C' := by
      rw [hBC, hB'C']
      calc a * (b * a) * b = (a * b) * (a * b) := by simp only [Matrix.mul_assoc]
        _ = a * b := hq
    calc (C' * a * B) * (C * b * B') = C' * (a * (B * C) * b) * B' := by
          simp only [Matrix.mul_assoc]
      _ = C' * (B' * C') * B' := by rw [h1]
      _ = (C' * B') * (C' * B') := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hC'B', mul_one]
  · have h1 : b * (B' * C') * a = B * C := by
      rw [hB'C', hBC]
      calc b * (a * b) * a = (b * a) * (b * a) := by simp only [Matrix.mul_assoc]
        _ = b * a := hp
    calc (C * b * B') * (C' * a * B) = C * (b * (B' * C') * a) * B := by
          simp only [Matrix.mul_assoc]
      _ = C * (B * C) * B := by rw [h1]
      _ = (C * B) * (C * B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCB, mul_one]

end Sandwich

/-! ## 2. Stabilised graph columns over a commutative ring -/

section Blocks

/-- The stabilised graph column `[[1],[F]] ⊕ 1_k`. -/
def gCol {R : Type} [Ring R] {n : ℕ} (k : ℕ) (F : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin ((n + n) + k)) (Fin (n + k)) R :=
  Bott.blk k (rgraphB R F)

/-- A left inverse of `gCol`. -/
def gLinv {R : Type} [CommRing R] [Star R] {n : ℕ} (k : ℕ) (F : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + k)) (Fin ((n + n) + k)) R :=
  Bott.blk k (rgraphLinv R F)

/-- The stabilised reciprocal column `[[G],[1]] ⊕ 1_k`. -/
def rCol {R : Type} [Ring R] {n : ℕ} (k : ℕ) (G : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin ((n + n) + k)) (Fin (n + k)) R :=
  Bott.blk k (rrecipB R G)

/-- A left inverse of `rCol`. -/
def rLinv {R : Type} [CommRing R] [Star R] {n : ℕ} (k : ℕ) (G : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + k)) (Fin ((n + n) + k)) R :=
  Bott.blk k (rrecipLinv R G)

lemma gCol_mul_gLinv {R : Type} [CommRing R] [Star R] {n : ℕ} (k : ℕ)
    (F : Matrix (Fin n) (Fin n) R) :
    gCol k F * gLinv k F = Bott.blk k (rgraphProj R F) := by
  rw [gCol, gLinv, Bott.blk_mul, rgraphB_mul_rgraphLinv]

lemma rCol_mul_rLinv {R : Type} [CommRing R] [Star R] {n : ℕ} (k : ℕ)
    (G : Matrix (Fin n) (Fin n) R) :
    rCol k G * rLinv k G = Bott.blk k (rrecipProj R G) := by
  rw [rCol, rLinv, Bott.blk_mul, rrecipB_mul_rrecipLinv]

lemma gLinv_mul_gCol {R : Type} [CommRing R] [Star R] {n : ℕ} (k : ℕ)
    (F : Matrix (Fin n) (Fin n) R)
    (h : IsUnit ((Fund.graphB R F).conjTranspose * Fund.graphB R F)) :
    gLinv k F * gCol k F = 1 := by
  rw [gCol, gLinv, Bott.blk_mul, rgraphLinv_mul R F h, Bott.blk_one]

lemma rLinv_mul_rCol {R : Type} [CommRing R] [Star R] {n : ℕ} (k : ℕ)
    (G : Matrix (Fin n) (Fin n) R)
    (h : IsUnit ((Fund.recipB R G).conjTranspose * Fund.recipB R G)) :
    rLinv k G * rCol k G = 1 := by
  rw [rCol, rLinv, Bott.blk_mul, rrecipLinv_mul R G h, Bott.blk_one]

end Blocks

/-! ## 3. Boundary restriction of the stabilised columns -/

section Bdry

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

lemma gCol_bdry {n k : ℕ} (F : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    (gCol k F).map (Fund.bdryRestrict X) = gCol k (F.map (Fund.bdryRestrict X)) := by
  rw [gCol, gCol, Bott.blk_map, rgraphB_map]

lemma rCol_bdry {n k : ℕ} (G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)) :
    (rCol k G).map (Fund.bdryRestrict X) = rCol k (G.map (Fund.bdryRestrict X)) := by
  rw [rCol, rCol, Bott.blk_map, rrecipB_map]

lemma gLinv_bdry {n k : ℕ} (F : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hFs : F.map (Fund.bdryRestrict X) = (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) :
    (gLinv k F).map (Fund.bdryRestrict X) =
      gLinv k (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
  rw [gLinv, gLinv, Bott.blk_map, rgraphLinv_map X F u hFs]

lemma rLinv_bdry {n k : ℕ} (G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))
    (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hGs : G.map (Fund.bdryRestrict X) =
      (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) :
    (rLinv k G).map (Fund.bdryRestrict X) =
      rLinv k (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
  rw [rLinv, rLinv, Bott.blk_map, rrecipLinv_map X G u hGs]

/-! ## 4. The two circle identities -/

lemma rrecipB_mul_unit {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    rrecipB C(X × Sph ℂ, ℂ) (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
        (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) =
      rgraphB C(X × Sph ℂ, ℂ) (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
  rw [rrecipB, rgraphB,
    ← reindexRow_mul (Fund.recipB C(X × Sph ℂ, ℂ)
      (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)))
      (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))]
  rw [recipB_inv_mul_graphB]

lemma mul_rgraphLinv {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
        rgraphLinv C(X × Sph ℂ, ℂ) (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) =
      rrecipLinv C(X × Sph ℂ, ℂ) (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
  rw [rgraphLinv, rrecipLinv,
    ← reindexCol_mul (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      (Ring.inverse ((Fund.graphB C(X × Sph ℂ, ℂ)
            (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))).conjTranspose *
          Fund.graphB C(X × Sph ℂ, ℂ) (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) *
        (Fund.graphB C(X × Sph ℂ, ℂ)
          (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))).conjTranspose)]
  rw [← Matrix.mul_assoc, RelGen.star_left_inverse]

lemma rCol_mul_unit_blk {n k : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    rCol k (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
        Bott.blk k (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) =
      gCol k (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
  rw [rCol, gCol, Bott.blk_mul, rrecipB_mul_unit X u]

lemma blk_mul_gLinv {n k : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    Bott.blk k (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
        gLinv k (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) =
      rLinv k (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
  rw [gLinv, rLinv, Bott.blk_mul, mul_rgraphLinv X u]

end Bdry

/-! ## 5. Lifts and the clutched idempotent -/

section Lift

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- A disc lift of the unit `u`. -/
def liftU {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
  Fund.liftOf X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))

/-- A disc lift of the unit `u⁻¹`. -/
def liftUinv {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ) :=
  Fund.liftOf X (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))

lemma liftU_spec {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    (liftU X u).map (Fund.bdryRestrict X) =
      (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) :=
  Fund.liftOf_spec X (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))

lemma liftUinv_spec {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    (liftUinv X u).map (Fund.bdryRestrict X) =
      (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) :=
  Fund.liftOf_spec X (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))

/-- The clutched idempotent of `u`, with the canonical lifts. -/
def eu {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) : Mat (Fund.pullAlg2 X) :=
  Fund.clutchIdem X n u (liftU X u) (liftUinv X u) (liftU_spec X u) (liftUinv_spec X u)

lemma eu_isIdem {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    (eu X u).IsIdem :=
  Fund.clutchIdem_isIdem X n u (liftU X u) (liftUinv X u) (liftU_spec X u) (liftUinv_spec X u)

/-- `κ` is `cls` of the clutched idempotent, transported along `k0Glue`. -/
lemma k0Glue_kappa {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    (Fund.k0Glue X) (Fund.kappa X n u) = cls (eu X u) := by
  rw [Fund.kappa_val X n u]
  exact (Fund.k0Glue X).apply_symm_apply _

lemma eu_map_prF {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    (eu X u).2.map (Fund.prF X) = rgraphProj C(X × Ball ℂ, ℂ) (liftU X u) :=
  clutchData_map_prF X u (liftU X u) (liftUinv X u) (liftU_spec X u) (liftUinv_spec X u)

lemma eu_map_prS {n : ℕ} (u : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ) :
    (eu X u).2.map (Fund.prS X) = rrecipProj C(X × Ball ℂ, ℂ) (liftUinv X u) :=
  clutchData_map_prS X u (liftU X u) (liftUinv X u) (liftU_spec X u) (liftUinv_spec X u)

end Lift

/-! ## 6. Milnor's exactness at `K₁` -/

/-- Milnor's "exactness at `K₁`" for the two-disc square: if two clutching functions give the same
class, then after stabilisation they differ by units extending over the two discs. -/
theorem kappa_eq_disc (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (u v : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (h : Fund.kappa X n u = Fund.kappa X n v) :
    ∃ (k : ℕ) (g₀ g₁ : (Matrix (Fin (n + k)) (Fin (n + k)) C(X × Ball ℂ, ℂ))ˣ),
      Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) 0 0
            (1 : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))) =
        (g₀ : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Ball ℂ, ℂ)).map
            (fun f => Fund.bdryRestrict X f) *
          Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) 0 0
              (1 : Matrix (Fin k) (Fin k) C(X × Sph ℂ, ℂ))) *
          (g₁ : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Ball ℂ, ℂ)).map
            (fun f => Fund.bdryRestrict X f) := by
  classical
  -- κ(u) = κ(v), transported to the clutched idempotents
  have hcls : cls (eu X u) = cls (eu X v) := by
    rw [← k0Glue_kappa X u, ← k0Glue_kappa X v, h]
  obtain ⟨k, hmvn⟩ :=
    (cls_eq_stable_mvN (eu X u) (eu X v) (eu_isIdem X u) (eu_isIdem X v)).mp hcls
  have heu : (eu X u).2 * (eu X u).2 = (eu X u).2 := eu_isIdem X u
  have hev : (eu X v).2 * (eu X v).2 = (eu X v).2 := eu_isIdem X v
  let MU : Matrix (Fin (n + n)) (Fin (n + n)) (Fund.pullAlg2 X) := (eu X u).2
  let MV : Matrix (Fin (n + n)) (Fin (n + n)) (Fund.pullAlg2 X) := (eu X v).2
  have heuM : MU * MU = MU := heu
  have hevM : MV * MV = MV := hev
  have hMUp : MU.map (Fund.prF X) = rgraphProj C(X × Ball ℂ, ℂ) (liftU X u) := eu_map_prF X u
  have hMUs : MU.map (Fund.prS X) = rrecipProj C(X × Ball ℂ, ℂ) (liftUinv X u) := eu_map_prS X u
  have hMVp : MV.map (Fund.prF X) = rgraphProj C(X × Ball ℂ, ℂ) (liftU X v) := eu_map_prF X v
  have hMVs : MV.map (Fund.prS X) = rrecipProj C(X × Ball ℂ, ℂ) (liftUinv X v) := eu_map_prS X v
  -- transport the stable Murray--von Neumann equivalence to the block-diagonal form
  have hidemStabU : Mat.IsIdem (⟨(n + n) + k, Bott.blk k MU⟩ : Mat (Fund.pullAlg2 X)) := by
    show Bott.blk k MU * Bott.blk k MU = Bott.blk k MU
    rw [Bott.blk_mul, heuM]
  have hidemStabV : Mat.IsIdem (⟨(n + n) + k, Bott.blk k MV⟩ : Mat (Fund.pullAlg2 X)) := by
    show Bott.blk k MV * Bott.blk k MV = Bott.blk k MV
    rw [Bott.blk_mul, hevM]
  have hsumU : ((eu X u).sum (Mat.one (Fund.pullAlg2 X) k)).IsIdem :=
    Mat.sum_idem (eu_isIdem X u) (Mat.one_isIdem (Fund.pullAlg2 X) k)
  have hsumV : ((eu X v).sum (Mat.one (Fund.pullAlg2 X) k)).IsIdem :=
    Mat.sum_idem (eu_isIdem X v) (Mat.one_isIdem (Fund.pullAlg2 X) k)
  have hmvU : Mat.MvN (⟨(n + n) + k, Bott.blk k MU⟩ : Mat (Fund.pullAlg2 X))
      ((eu X u).sum (Mat.one (Fund.pullAlg2 X) k)) := by
    refine ⟨Bott.blk k MU, Bott.blk k MU, ?_, ?_⟩
    · show Bott.blk k MU * Bott.blk k MU = Bott.blk k MU
      rw [Bott.blk_mul, heuM]
    · show Bott.blk k MU * Bott.blk k MU = ((eu X u).sum (Mat.one (Fund.pullAlg2 X) k)).2
      rw [Bott.blk_mul, heuM]
      exact Bott.blk_mat_sum (eu X u) k
  have hmvV : Mat.MvN (⟨(n + n) + k, Bott.blk k MV⟩ : Mat (Fund.pullAlg2 X))
      ((eu X v).sum (Mat.one (Fund.pullAlg2 X) k)) := by
    refine ⟨Bott.blk k MV, Bott.blk k MV, ?_, ?_⟩
    · show Bott.blk k MV * Bott.blk k MV = Bott.blk k MV
      rw [Bott.blk_mul, hevM]
    · show Bott.blk k MV * Bott.blk k MV = ((eu X v).sum (Mat.one (Fund.pullAlg2 X) k)).2
      rw [Bott.blk_mul, hevM]
      exact Bott.blk_mat_sum (eu X v) k
  have hmvn' : Mat.MvN (⟨(n + n) + k, Bott.blk k MU⟩ : Mat (Fund.pullAlg2 X))
      (⟨(n + n) + k, Bott.blk k MV⟩ : Mat (Fund.pullAlg2 X)) :=
    Mat.mvN_trans hidemStabU hsumU hidemStabV hmvU
      (Mat.mvN_trans hsumU hsumV hidemStabV hmvn (Mat.mvN_symm hmvV))
  obtain ⟨a, b, hba, hab⟩ := hmvn'
  have hba' : b * a = Bott.blk k MU := hba
  have hab' : a * b = Bott.blk k MV := hab
  -- the disc projections of the Murray--von Neumann data
  have hP₀ : b.map (Fund.prF X) * a.map (Fund.prF X) =
      Bott.blk k (rgraphProj C(X × Ball ℂ, ℂ) (liftU X u)) := by
    rw [Matrix.map_mul' (Fund.prF X) b a, hba', Bott.blk_map, hMUp]
  have hQ₀ : a.map (Fund.prF X) * b.map (Fund.prF X) =
      Bott.blk k (rgraphProj C(X × Ball ℂ, ℂ) (liftU X v)) := by
    rw [Matrix.map_mul' (Fund.prF X) a b, hab', Bott.blk_map, hMVp]
  have hP₁ : b.map (Fund.prS X) * a.map (Fund.prS X) =
      Bott.blk k (rrecipProj C(X × Ball ℂ, ℂ) (liftUinv X u)) := by
    rw [Matrix.map_mul' (Fund.prS X) b a, hba', Bott.blk_map, hMUs]
  have hQ₁ : a.map (Fund.prS X) * b.map (Fund.prS X) =
      Bott.blk k (rrecipProj C(X × Ball ℂ, ℂ) (liftUinv X v)) := by
    rw [Matrix.map_mul' (Fund.prS X) a b, hab', Bott.blk_map, hMVs]
  -- idempotency of the disc projections
  have hp₀ : (b.map (Fund.prF X) * a.map (Fund.prF X)) *
      (b.map (Fund.prF X) * a.map (Fund.prF X)) = b.map (Fund.prF X) * a.map (Fund.prF X) := by
    rw [Matrix.map_mul' (Fund.prF X) b a, hba',
      Matrix.map_mul' (Fund.prF X) (Bott.blk k MU) (Bott.blk k MU),
      Bott.blk_mul, heuM]
  have hq₀ : (a.map (Fund.prF X) * b.map (Fund.prF X)) *
      (a.map (Fund.prF X) * b.map (Fund.prF X)) = a.map (Fund.prF X) * b.map (Fund.prF X) := by
    rw [Matrix.map_mul' (Fund.prF X) a b, hab',
      Matrix.map_mul' (Fund.prF X) (Bott.blk k MV) (Bott.blk k MV),
      Bott.blk_mul, hevM]
  have hp₁ : (b.map (Fund.prS X) * a.map (Fund.prS X)) *
      (b.map (Fund.prS X) * a.map (Fund.prS X)) = b.map (Fund.prS X) * a.map (Fund.prS X) := by
    rw [Matrix.map_mul' (Fund.prS X) b a, hba',
      Matrix.map_mul' (Fund.prS X) (Bott.blk k MU) (Bott.blk k MU),
      Bott.blk_mul, heuM]
  have hq₁ : (a.map (Fund.prS X) * b.map (Fund.prS X)) *
      (a.map (Fund.prS X) * b.map (Fund.prS X)) = a.map (Fund.prS X) * b.map (Fund.prS X) := by
    rw [Matrix.map_mul' (Fund.prS X) a b, hab',
      Matrix.map_mul' (Fund.prS X) (Bott.blk k MV) (Bott.blk k MV),
      Bott.blk_mul, hevM]
  -- the four sandwich hypotheses
  have hCB : gLinv k (liftU X u) * gCol k (liftU X u) = 1 :=
    gLinv_mul_gCol k (liftU X u) (graphB_gram_isUnit X (liftU X u))
  have hC'B' : gLinv k (liftU X v) * gCol k (liftU X v) = 1 :=
    gLinv_mul_gCol k (liftU X v) (graphB_gram_isUnit X (liftU X v))
  have hD₁C₁ : rLinv k (liftUinv X u) * rCol k (liftUinv X u) = 1 :=
    rLinv_mul_rCol k (liftUinv X u) (recipB_gram_isUnit X (liftUinv X u))
  have hD₁'C₁' : rLinv k (liftUinv X v) * rCol k (liftUinv X v) = 1 :=
    rLinv_mul_rCol k (liftUinv X v) (recipB_gram_isUnit X (liftUinv X v))
  have hBC : gCol k (liftU X u) * gLinv k (liftU X u) =
      b.map (Fund.prF X) * a.map (Fund.prF X) :=
    (gCol_mul_gLinv k (liftU X u)).trans hP₀.symm
  have hB'C' : gCol k (liftU X v) * gLinv k (liftU X v) =
      a.map (Fund.prF X) * b.map (Fund.prF X) :=
    (gCol_mul_gLinv k (liftU X v)).trans hQ₀.symm
  have hD₁C₁' : rCol k (liftUinv X u) * rLinv k (liftUinv X u) =
      b.map (Fund.prS X) * a.map (Fund.prS X) :=
    (rCol_mul_rLinv k (liftUinv X u)).trans hP₁.symm
  have hD₁'C₁'' : rCol k (liftUinv X v) * rLinv k (liftUinv X v) =
      a.map (Fund.prS X) * b.map (Fund.prS X) :=
    (rCol_mul_rLinv k (liftUinv X v)).trans hQ₁.symm
  set α₀ : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Ball ℂ, ℂ) :=
    gLinv k (liftU X v) * a.map (Fund.prF X) * gCol k (liftU X u) with hα₀
  set β₀ : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Ball ℂ, ℂ) :=
    gLinv k (liftU X u) * b.map (Fund.prF X) * gCol k (liftU X v) with hβ₀
  set α₁ : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Ball ℂ, ℂ) :=
    rLinv k (liftUinv X v) * a.map (Fund.prS X) * rCol k (liftUinv X u) with hα₁
  set β₁ : Matrix (Fin (n + k)) (Fin (n + k)) C(X × Ball ℂ, ℂ) :=
    rLinv k (liftUinv X u) * b.map (Fund.prS X) * rCol k (liftUinv X v) with hβ₁
  have hα₀β₀ : α₀ * β₀ = 1 :=
    (sandwich_mul_eq_one (gCol k (liftU X u)) (gCol k (liftU X v))
      (gLinv k (liftU X u)) (gLinv k (liftU X v)) (a.map (Fund.prF X)) (b.map (Fund.prF X))
      hCB hC'B' hBC hB'C' hp₀ hq₀).1
  have hβ₀α₀ : β₀ * α₀ = 1 :=
    (sandwich_mul_eq_one (gCol k (liftU X u)) (gCol k (liftU X v))
      (gLinv k (liftU X u)) (gLinv k (liftU X v)) (a.map (Fund.prF X)) (b.map (Fund.prF X))
      hCB hC'B' hBC hB'C' hp₀ hq₀).2
  have hα₁β₁ : α₁ * β₁ = 1 :=
    (sandwich_mul_eq_one (rCol k (liftUinv X u)) (rCol k (liftUinv X v))
      (rLinv k (liftUinv X u)) (rLinv k (liftUinv X v)) (a.map (Fund.prS X)) (b.map (Fund.prS X))
      hD₁C₁ hD₁'C₁' hD₁C₁' hD₁'C₁'' hp₁ hq₁).1
  have hβ₁α₁ : β₁ * α₁ = 1 :=
    (sandwich_mul_eq_one (rCol k (liftUinv X u)) (rCol k (liftUinv X v))
      (rLinv k (liftUinv X u)) (rLinv k (liftUinv X v)) (a.map (Fund.prS X)) (b.map (Fund.prS X))
      hD₁C₁ hD₁'C₁' hD₁C₁' hD₁'C₁'' hp₁ hq₁).2
  -- the boundary values of the sandwiches
  have ha_circ : (a.map (Fund.prS X)).map (Fund.bdryRestrict X) =
      (a.map (Fund.prF X)).map (Fund.bdryRestrict X) := by
    rw [Bott.matrix_map_map, Bott.matrix_map_map, square_comm_prF X]
  have hA₀ : α₀.map (Fund.bdryRestrict X) =
      gLinv k (↑v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
        (a.map (Fund.prF X)).map (Fund.bdryRestrict X) *
        gCol k (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [hα₀]
    rw [← Matrix.map_mul' (Fund.bdryRestrict X)
        (gLinv k (liftU X v) * a.map (Fund.prF X)) (gCol k (liftU X u)),
      ← Matrix.map_mul' (Fund.bdryRestrict X) (gLinv k (liftU X v)) (a.map (Fund.prF X))]
    rw [gLinv_bdry X (liftU X v) v (liftU_spec X v), gCol_bdry X (liftU X u),
      liftU_spec X u]
  have hA₁ : α₁.map (Fund.bdryRestrict X) =
      rLinv k (↑(v⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
        (a.map (Fund.prF X)).map (Fund.bdryRestrict X) *
        rCol k (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
    rw [hα₁]
    rw [← Matrix.map_mul' (Fund.bdryRestrict X)
        (rLinv k (liftUinv X v) * a.map (Fund.prS X)) (rCol k (liftUinv X u)),
      ← Matrix.map_mul' (Fund.bdryRestrict X) (rLinv k (liftUinv X v)) (a.map (Fund.prS X))]
    rw [rLinv_bdry X (liftUinv X v) v (liftUinv_spec X v),
      rCol_bdry X (liftUinv X u), liftUinv_spec X u, ha_circ]
  -- the key compatibility on the circle
  have hcomp : α₁.map (Fund.bdryRestrict X) *
        Bott.blk k (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) =
      Bott.blk k (↑v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
        α₀.map (Fund.bdryRestrict X) := by
    rw [hA₁, hA₀, Matrix.mul_assoc, rCol_mul_unit_blk X u, ← blk_mul_gLinv X v]
    simp only [Matrix.mul_assoc]
  have hβ₁α₁_map : β₁.map (Fund.bdryRestrict X) * α₁.map (Fund.bdryRestrict X) = 1 := by
    rw [Matrix.map_mul' (Fund.bdryRestrict X) β₁ α₁, hβ₁α₁, Bott.matrix_map_one]
  have hû : Bott.blk k (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) =
      β₁.map (Fund.bdryRestrict X) * Bott.blk k (↑v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
        α₀.map (Fund.bdryRestrict X) := by
    calc Bott.blk k (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
        = (β₁.map (Fund.bdryRestrict X) * α₁.map (Fund.bdryRestrict X)) *
            Bott.blk k (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) := by
          rw [hβ₁α₁_map, one_mul]
      _ = β₁.map (Fund.bdryRestrict X) *
            (α₁.map (Fund.bdryRestrict X) *
              Bott.blk k (↑u : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))) := by
          rw [Matrix.mul_assoc]
      _ = β₁.map (Fund.bdryRestrict X) *
            (Bott.blk k (↑v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
              α₀.map (Fund.bdryRestrict X)) := by rw [hcomp]
      _ = β₁.map (Fund.bdryRestrict X) *
            Bott.blk k (↑v : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) *
              α₀.map (Fund.bdryRestrict X) := by rw [Matrix.mul_assoc]
  refine ⟨k, ⟨β₁, α₁, hβ₁α₁, hα₁β₁⟩, ⟨α₀, β₀, hα₀β₀, hβ₀α₀⟩, ?_⟩
  exact hû

end

end Work.KT.FP
