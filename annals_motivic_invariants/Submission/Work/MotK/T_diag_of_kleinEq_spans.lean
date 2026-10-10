import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotK.KleinPScale
import Submission.Work.MotK.algebraic_mem_base
import Submission.Work.MotTDG.Defs
import Submission.Work.MotTDG.Ring
import Submission.Work.MotTDG.Setup
import Submission.Work.MotTDG.muMat_det_ne_zero
import Submission.Work.MotTDG.rhoVW_eq_zero
import Submission.Work.MotTDG.tenMon_linearIndependent
import Submission.Work.MotTDG.exists_algHom_of_point
import Submission.Work.MotTDG.reduce_alg
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.MotC2.Translation
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

namespace Work.MotK

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

/-! ## §0 Elementary facts about the Pfaffian vector -/

/-- Homogeneity of the Pfaffians: `p_k (c · z) = c² p_k z`. -/
theorem tdg_kleinP_smul {R : Type*} [CommRing R] (a b c : R) (z : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinP a b (fun i => c * z i) k = c ^ 2 * Work.MotK.kleinP a b z k := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four',
      Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2, Work.MotK.kleinP3,
      Work.MotK.kleinP4]
  all_goals ring

/-- The Pfaffians at a standard basis vector: `p_k (e_j) = -a b` if `j = 2k` and `0` otherwise. -/
theorem tdg_kleinP_single {R : Type*} [CommRing R] (a b : R) (j k : Fin 5) :
    Work.MotK.kleinP a b (Pi.single j (1 : R)) k = if j = 2 * k then -(a * b) else 0 := by
  fin_cases j <;> fin_cases k <;>
    simp [Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4, Pi.single, Function.update]

/-- Doubling is injective on `Fin 5`. -/
theorem tdg_two_mul_inj (j k : Fin 5) : 2 * j = 2 * k ↔ j = k := by
  constructor
  · intro h
    fin_cases j <;> fin_cases k <;> simp_all
  · rintro rfl; rfl

/-- The Pfaffians at the even standard basis vectors, with the index read modulo `5`. -/
theorem tdg_kleinP_two_mul {R : Type*} [CommRing R] (a b : R) (m k : Fin 5) :
    Work.MotK.kleinP a b (Pi.single (2 * m) (1 : R)) k = if m = k then -(a * b) else 0 := by
  rw [tdg_kleinP_single]
  by_cases h : m = k
  · subst h; simp
  · have h2 : ¬ (2 * m = 2 * k) := fun hh => h ((tdg_two_mul_inj m k).mp hh)
    simp [h, h2]

/-- `muVW` is natural under a ring homomorphism. -/
theorem tdg_map_muVW {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a₁ : R)
    (P : Fin 5 → R) (B : Fin 5 → Fin 5 → R) (j : Fin 5) :
    f (Work.MotTDG.muVW a₁ P B j) = Work.MotTDG.muVW (f a₁) (fun i => f (P i))
      (fun i j => f (B i j)) j := by
  fin_cases j <;> simp [Work.MotTDG.muVW]

/-! ## §1 The Weierstrass basis `1, x, y, x², xy` is `L`-independent -/

theorem tdg_basE_linearIndependent {L : Type*} [Field L] (E : WeierstrassCurve L) :
    LinearIndependent L (Work.MotTDG.basE E) := by
  have h : (fun m : Fin 5 => Work.MotTDG.tenMon E (Fin.castLE (by norm_num : 5 ≤ 10) m))
      = Work.MotTDG.basE E := by
    funext m
    fin_cases m <;> simp [Work.MotTDG.tenMon, Work.MotTDG.goodMon, Work.MotTDG.basE]
  rw [← h]
  exact (Work.MotTDG.tenMon_linearIndependent E).comp _ (Fin.castLE_injective _)

/-! ## §2 The `spans` matrix is the inverse of the Klein matrix -/

section Matrix

variable {𝕜 : Type} [Field 𝕜]

/-- The Klein coordinates, written in the Weierstrass basis as a linear combination. -/
theorem tdg_kleinCoord_eq_sum (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (i : Fin 5) :
    Work.MotV.kleinCoord D L i
      = ∑ m, Work.MotTDG.cL D L i m • Work.MotTDG.basE (D.E.baseChange L) m := by
  rw [Work.MotTDG.kleinCoord_eq_cL]
  exact Finset.sum_congr rfl fun m _ => (Algebra.smul_def _ _).symm

/-- The Weierstrass basis in terms of the Klein coordinates, in `•`-form. -/
theorem tdg_basE_eq (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (m : Fin 5) :
    Work.MotTDG.basE (D.E.baseChange L) m
      = ∑ i, Work.MotTDG.eL D L e m i • Work.MotV.kleinCoord D L i := by
  rw [Work.MotTDG.basE_eq_eL_kleinCoord D L e he m]
  exact Finset.sum_congr rfl fun i _ => (Algebra.smul_def _ _).symm

/-- The `spans` witness matrix is a left inverse of the Klein matrix. -/
theorem tdg_eL_mul_cL (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i) :
    Work.MotTDG.eL D L e * Work.MotTDG.cL D L = 1 := by
  have hbas := tdg_basE_linearIndependent (D.E.baseChange L)
  ext m l
  have hone : (∑ j, (if j = m then (1 : L) else 0) • Work.MotTDG.basE (D.E.baseChange L) j)
      = Work.MotTDG.basE (D.E.baseChange L) m := by
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [hb]
    · intro hm; exact absurd (Finset.mem_univ m) hm
  have h1 : (∑ j, (Work.MotTDG.eL D L e * Work.MotTDG.cL D L) m j
      • Work.MotTDG.basE (D.E.baseChange L) j) = Work.MotTDG.basE (D.E.baseChange L) m := by
    have hA : (∑ j, (Work.MotTDG.eL D L e * Work.MotTDG.cL D L) m j
        • Work.MotTDG.basE (D.E.baseChange L) j)
        = ∑ i, Work.MotTDG.eL D L e m i •
            (∑ j, Work.MotTDG.cL D L i j • Work.MotTDG.basE (D.E.baseChange L) j) := by
      simp only [Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
    rw [hA]
    simp only [← tdg_kleinCoord_eq_sum]
    exact (tdg_basE_eq D L e he m).symm
  have hsum : (∑ j, ((Work.MotTDG.eL D L e * Work.MotTDG.cL D L) m j
      - (if j = m then (1 : L) else 0)) • Work.MotTDG.basE (D.E.baseChange L) j) = 0 := by
    rw [Finset.sum_congr rfl (fun j _ => sub_smul _ _ _), Finset.sum_sub_distrib, h1, hone,
      sub_self]
  have h0 := (Fintype.linearIndependent_iff.mp hbas
    (fun j => (Work.MotTDG.eL D L e * Work.MotTDG.cL D L) m j - (if j = m then (1 : L) else 0)))
    hsum l
  rw [Matrix.one_apply]
  rw [sub_eq_zero.mp h0]
  by_cases h : m = l
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Consequently the Klein matrix is a left inverse of the `spans` witness matrix. -/
theorem tdg_cL_mul_eL (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i) :
    Work.MotTDG.cL D L * Work.MotTDG.eL D L e = 1 :=
  mul_eq_one_comm.mp (tdg_eL_mul_cL D L e he)

/-- The Klein coordinates are `L`-linearly independent. -/
theorem tdg_kleinCoord_linearIndependent (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L]
    [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i) :
    LinearIndependent L (Work.MotV.kleinCoord D L) := by
  have hbas := tdg_basE_linearIndependent (D.E.baseChange L)
  have hce := tdg_cL_mul_eL D L e he
  rw [linearIndependent_iff']
  intro s g hg i hi
  -- the relation in the Weierstrass basis
  have hR : (∑ j ∈ s, g j • Work.MotV.kleinCoord D L j)
      = ∑ m', (∑ j ∈ s, g j * Work.MotTDG.cL D L j m')
        • Work.MotTDG.basE (D.E.baseChange L) m' := by
    have hinner : ∀ j ∈ s, g j • Work.MotV.kleinCoord D L j
        = ∑ m', (g j * Work.MotTDG.cL D L j m')
          • Work.MotTDG.basE (D.E.baseChange L) m' := by
      intro j _
      rw [tdg_kleinCoord_eq_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun m' _ => by
        simp only [Algebra.smul_def, map_mul]
        rw [mul_assoc]
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm,
      Finset.sum_congr rfl (fun m' _ => (Finset.sum_smul).symm)]
  have hcoef : ∀ m, ∑ j ∈ s, g j * Work.MotTDG.cL D L j m = 0 := fun m =>
    (Fintype.linearIndependent_iff.mp hbas
      (fun m' => ∑ j ∈ s, g j * Work.MotTDG.cL D L j m')) (by rw [← hR]; exact hg) m
  have hdiag : ∀ j, (∑ m, Work.MotTDG.cL D L j m * Work.MotTDG.eL D L e m i)
      = if j = i then (1 : L) else 0 := by
    intro j
    have h := congrFun (congrFun hce j) i
    rwa [Matrix.mul_apply, Matrix.one_apply] at h
  have hgi : (∑ j ∈ s, g j * (if j = i then (1 : L) else 0)) = g i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro hnot; exact absurd hi hnot
  calc g i = ∑ j ∈ s, g j * (if j = i then (1 : L) else 0) := hgi.symm
    _ = ∑ j ∈ s, g j * (∑ m, Work.MotTDG.cL D L j m * Work.MotTDG.eL D L e m i) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hdiag j]
    _ = ∑ m, (∑ j ∈ s, g j * Work.MotTDG.cL D L j m) * Work.MotTDG.eL D L e m i := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
    _ = 0 := by
        rw [Finset.sum_congr rfl (fun m _ => by rw [hcoef m, zero_mul]),
          Finset.sum_const_zero]

/-- Each Klein coordinate is nonzero. -/
theorem tdg_kleinCoord_ne_zero (D : Work.MotV.KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (i : Fin 5) : Work.MotV.kleinCoord D L i ≠ 0 :=
  (tdg_kleinCoord_linearIndependent D L e he).ne_zero i

/-! ## §3 The reduction identity over `L` and the invertibility of the multiplier matrix -/

/-- **The reduction identity over `L`**: for every vector `v`, the Pfaffian `p_k (cL · v)` is the
combination of the five Veronese--Weierstrass quadrics `vwQuad` with coefficients the matrix
`muMat`.  (TDG-b + TDG-c + TDG-d.) -/
theorem tdg_reduce_L (D : Work.MotV.KleinData 𝕜) (L : Type) [Field L] [Algebra 𝕜 L]
    (hke : ∀ (L' : Type) [Field L'] [Algebra 𝕜 L'] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L') k = 0)
    (v : Fin 5 → L) (k : Fin 5) :
    Work.MotK.kleinP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b)
        (fun i => ∑ m, Work.MotTDG.cL D L i m * v m) k
      = ∑ j, Work.MotTDG.muMat D L k j *
          Work.MotTDG.vwQuad (D.E.baseChange L).a₁ (D.E.baseChange L).a₂
            (D.E.baseChange L).a₃ (D.E.baseChange L).a₄ (D.E.baseChange L).a₆ v j := by
  have h1 := Work.MotTDG.kleinP_mulVec_expand (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b)
    (Work.MotTDG.cL D L) v k
  have h2 := Work.MotTDG.quad_reduce (D.E.baseChange L).a₁ (D.E.baseChange L).a₂
    (D.E.baseChange L).a₃ (D.E.baseChange L).a₄ (D.E.baseChange L).a₆
    (Work.MotTDG.colP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (Work.MotTDG.cL D L) k)
    (Work.MotTDG.colB (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (Work.MotTDG.cL D L) k) v
  rw [h1]
  simp only [Work.MotTDG.quadForm] at h2
  have hρ : ∀ t : Fin 10, Work.MotTDG.rhoVW (D.E.baseChange L).a₁ (D.E.baseChange L).a₂
      (D.E.baseChange L).a₃ (D.E.baseChange L).a₄ (D.E.baseChange L).a₆
      (Work.MotTDG.colP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (Work.MotTDG.cL D L) k)
      (Work.MotTDG.colB (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (Work.MotTDG.cL D L) k) t
      = 0 := fun t => Work.MotTDG.rhoVW_eq_zero D hke L k t
  have hz : (∑ t, Work.MotTDG.rhoVW (D.E.baseChange L).a₁ (D.E.baseChange L).a₂
      (D.E.baseChange L).a₃ (D.E.baseChange L).a₄ (D.E.baseChange L).a₆
      (Work.MotTDG.colP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (Work.MotTDG.cL D L) k)
      (Work.MotTDG.colB (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b) (Work.MotTDG.cL D L) k) t *
      Work.MotTDG.goodMon v t) = 0 := by
    rw [Finset.sum_congr rfl (fun t _ => by rw [hρ t, zero_mul]), Finset.sum_const_zero]
  rw [h2, hz, add_zero]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- The left kernel of `muMat` is trivial. -/
theorem tdg_muMat_left_kernel (D : Work.MotV.KleinData 𝕜) (hab : D.a * D.b ≠ 0)
    (hke : ∀ (L' : Type) [Field L'] [Algebra 𝕜 L'] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L') k = 0)
    (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (lam : Fin 5 → L)
    (hlam : ∀ j, ∑ k, lam k * Work.MotTDG.muMat D L k j = 0) : lam = 0 := by
  have habL : algebraMap 𝕜 L D.a * algebraMap 𝕜 L D.b ≠ 0 := by
    rw [← map_mul]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective 𝕜 L)).mpr hab
  have hce := tdg_cL_mul_eL D L e he
  have hker : ∀ v : Fin 5 → L,
      (∑ k, lam k * Work.MotK.kleinP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b)
        (fun i => ∑ m, Work.MotTDG.cL D L i m * v m) k) = 0 := by
    intro v
    rw [Finset.sum_congr rfl fun k _ => by
      rw [tdg_reduce_L D L hke v k, Finset.mul_sum]]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show (∑ k, lam k * (Work.MotTDG.muMat D L k j *
        Work.MotTDG.vwQuad (D.E.baseChange L).a₁ (D.E.baseChange L).a₂
          (D.E.baseChange L).a₃ (D.E.baseChange L).a₄ (D.E.baseChange L).a₆ v j))
        = (∑ k, lam k * Work.MotTDG.muMat D L k j) *
          Work.MotTDG.vwQuad (D.E.baseChange L).a₁ (D.E.baseChange L).a₂
            (D.E.baseChange L).a₃ (D.E.baseChange L).a₄ (D.E.baseChange L).a₆ v j from by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring]
    rw [hlam j, zero_mul]
  funext m
  have hCv : (fun i => ∑ m', Work.MotTDG.cL D L i m'
      * (fun p => Work.MotTDG.eL D L e p (2 * m)) m') = Pi.single (2 * m) (1 : L) := by
    funext i
    have h := congrFun (congrFun hce i) (2 * m)
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [Pi.single, Function.update] using h
  have hv := hker (fun p => Work.MotTDG.eL D L e p (2 * m))
  rw [hCv] at hv
  have h2 : (∑ k, lam k * Work.MotK.kleinP (algebraMap 𝕜 L D.a) (algebraMap 𝕜 L D.b)
      (Pi.single (2 * m) (1 : L)) k) = -(algebraMap 𝕜 L D.a * algebraMap 𝕜 L D.b) * lam m := by
    rw [Finset.sum_congr rfl (fun k _ => by rw [tdg_kleinP_two_mul])]
    rw [Finset.sum_eq_single m]
    · rw [if_pos rfl]; ring
    · intro b _ hb; rw [if_neg (Ne.symm hb), mul_zero]
    · intro hm; exact absurd (Finset.mem_univ m) hm
  rw [h2] at hv
  exact (mul_eq_zero.mp hv).resolve_left (neg_ne_zero.mpr habL)

/-- The multiplier matrix `muMat` is invertible. -/
theorem tdg_muMat_det_ne_zero (D : Work.MotV.KleinData 𝕜) (hab : D.a * D.b ≠ 0)
    (hke : ∀ (L' : Type) [Field L'] [Algebra 𝕜 L'] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L') k = 0)
    (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i) :
    (Work.MotTDG.muMat D L).det ≠ 0 := by
  have hinj : Function.Injective fun lam : Fin 5 → L =>
      (Work.MotTDG.muMat D L).transpose.mulVec lam := by
    intro lam mu h
    have hsub : lam - mu = 0 := by
      refine tdg_muMat_left_kernel D hab hke L e he (lam - mu) fun j => ?_
      have h' : (Work.MotTDG.muMat D L).transpose.mulVec (lam - mu) = 0 := by
        rw [Matrix.mulVec_sub]
        exact sub_eq_zero.mpr h
      have h2 := congrFun h' j
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at h2
      rw [Finset.sum_congr rfl fun i _ => mul_comm ((lam - mu) i) (Work.MotTDG.muMat D L i j)]
      exact h2
    exact sub_eq_zero.mp hsub
  have hli : LinearIndependent L (Work.MotTDG.muMat D L).transpose.col :=
    (Matrix.mulVec_injective_iff).mp hinj
  have hunit : IsUnit (Work.MotTDG.muMat D L).transpose :=
    (Matrix.linearIndependent_cols_iff_isUnit).mp hli
  have hdetT : (Work.MotTDG.muMat D L).transpose.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
  rwa [Matrix.det_transpose] at hdetT

end Matrix

/-! ## §4 The reduction identity in the function field -/

/-- **The reduction identity in the function field**: the `R`-algebra form of node TDG-c
(`Work.MotTDG.reduce_alg`), specialised to `R = L(E)`. -/
theorem tdg_reduce_F {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (L : Type) [Field L]
    [Algebra 𝕜 L]
    (hke : ∀ (L' : Type) [Field L'] [Algebra 𝕜 L'] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L') k = 0)
    (v : Fin 5 → FunctionField (D.E.baseChange L)) (k : Fin 5) :
    Work.MotK.kleinP (algebraMap L _ (algebraMap 𝕜 L D.a)) (algebraMap L _ (algebraMap 𝕜 L D.b))
        (fun i => ∑ m, algebraMap L _ (Work.MotTDG.cL D L i m) * v m) k
      = ∑ j, algebraMap L _ (Work.MotTDG.muMat D L k j) *
          Work.MotTDG.vwQuad (algebraMap L _ (D.E.baseChange L).a₁)
            (algebraMap L _ (D.E.baseChange L).a₂) (algebraMap L _ (D.E.baseChange L).a₃)
            (algebraMap L _ (D.E.baseChange L).a₄) (algebraMap L _ (D.E.baseChange L).a₆) v j :=
  Work.MotTDG.reduce_alg D hke L (FunctionField (D.E.baseChange L)) v k

/-- `L` is relatively algebraically closed in the function field: an element algebraic over `L`
is a constant.  (`Work.MotK.algebraic_mem_base`, restated here for import convenience.) -/
theorem tdg_algebraic_mem_base {L : Type} [Field L] (E : WeierstrassCurve L)
    {z : WeierstrassCurve.Affine.FunctionField E} (hz : IsAlgebraic L z) :
    ∃ c : L, z = algebraMap L (WeierstrassCurve.Affine.FunctionField E) c :=
  Work.MotK.algebraic_mem_base E hz

/-! ## §5 The diagonal construction -/

section Diag

variable {𝕜 : Type} [Field 𝕜]

/-- The diagonal matrix `diag (c^i)`. -/
def tdg_Mdiag (L : Type*) [Field L] (c : L) : Matrix (Fin 5) (Fin 5) L :=
  fun i j => if i = j then c ^ (i : ℕ) else 0

/-- `kvec` of a diagonal matrix: the components are `c^i κ_i`. -/
theorem tdg_kvec_Mdiag (D : Work.MotV.KleinData 𝕜) (L : Type) [Field L] [Algebra 𝕜 L]
    (c : L) (i : Fin 5) :
    Work.MotTDG.kvec D L (tdg_Mdiag L c) i =
      algebraMap L (FunctionField (D.E.baseChange L)) (c ^ (i : ℕ)) *
        Work.MotV.kleinCoord D L i := by
  rw [Work.MotTDG.kvec]
  rw [Finset.sum_eq_single i]
  · rw [tdg_Mdiag]; simp
  · intro b _ hb
    rw [tdg_Mdiag, if_neg (fun h : i = b => hb h.symm), map_zero, zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- For `c ≠ 0` the normalising scalar `ℓ(kvec (diag c^i))` is nonzero. -/
theorem tdg_ell_kvec_Mdiag_ne_zero (D : Work.MotV.KleinData 𝕜) (L : Type) [Field L]
    [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (c : L) (hcne : c ≠ 0) :
    Work.MotTDG.ell D L e (Work.MotTDG.kvec D L (tdg_Mdiag L c)) ≠ 0 := by
  intro h0
  have hrel : (∑ i ∈ (Finset.univ : Finset (Fin 5)),
      (algebraMap 𝕜 L (e 0 i) * c ^ (i : ℕ)) • Work.MotV.kleinCoord D L i) = 0 := by
    rw [← h0, Work.MotTDG.ell]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tdg_kvec_Mdiag]
    simp only [Algebra.smul_def, Work.MotTDG.eL, map_mul]
    refl_ring1
  have hj := (linearIndependent_iff'.mp (Work.MotTDG.kleinCoord_linearIndependent D L e he))
    (Finset.univ : Finset (Fin 5)) (fun i => algebraMap 𝕜 L (e 0 i) * c ^ (i : ℕ)) hrel
  have hall : ∀ i, algebraMap 𝕜 L (e 0 i) = 0 := by
    intro i
    rcases mul_eq_zero.mp (hj i (Finset.mem_univ i)) with h1 | h1
    · exact h1
    · exact absurd h1 (pow_ne_zero _ hcne)
  have hbase : (∑ i ∈ (Finset.univ : Finset (Fin 5)),
      (algebraMap 𝕜 L (e 0 i)) • Work.MotV.kleinCoord D L i) = 1 := by
    have h := Work.MotTDG.basE_eq_eL_kleinCoord D L e he 0
    rw [Work.MotTDG.basE_zero] at h
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Algebra.smul_def, Work.MotTDG.eL]
  have hbase0 : (∑ i ∈ (Finset.univ : Finset (Fin 5)),
      (0 : L) • Work.MotV.kleinCoord D L i) = 1 := by
    rw [← hbase]
    exact Finset.sum_congr rfl fun i _ => by rw [hall i]
  rw [Finset.sum_congr rfl (fun i _ => zero_smul L (Work.MotV.kleinCoord D L i))] at hbase0
  simp only [Finset.sum_const_zero] at hbase0
  exact one_ne_zero hbase0.symm

/-- `wvec 0 = 1`: the normalised Weierstrass vector has first coordinate `1`. -/
theorem tdg_wvec_zero (D : Work.MotV.KleinData 𝕜) (L : Type) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜) (M : Matrix (Fin 5) (Fin 5) L)
    (h : Work.MotTDG.ell D L e (Work.MotTDG.kvec D L M) ≠ 0) :
    Work.MotTDG.wvec D L e M 0 = 1 := by
  rw [Work.MotTDG.wvec]
  rw [show (∑ i, algebraMap L _ (Work.MotTDG.eL D L e 0 i) * Work.MotTDG.kappaShift D L e M i)
      = (∑ i, algebraMap L _ (Work.MotTDG.eL D L e 0 i) * Work.MotTDG.kvec D L M i)
        / Work.MotTDG.ell D L e (Work.MotTDG.kvec D L M) from by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Work.MotTDG.kappaShift, mul_div_assoc]]
  rw [show (∑ i, algebraMap L _ (Work.MotTDG.eL D L e 0 i) * Work.MotTDG.kvec D L M i)
      = Work.MotTDG.ell D L e (Work.MotTDG.kvec D L M) from rfl]
  exact div_self h

/-- The coordinates `wvec` are the `eL`-image of the normalised Klein coordinates
`kappaShift`. -/
theorem tdg_cv_kappaShift (D : Work.MotV.KleinData 𝕜) (L : Type) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (M : Matrix (Fin 5) (Fin 5) L) (i : Fin 5) :
    (∑ m, algebraMap L (FunctionField (D.E.baseChange L)) (Work.MotTDG.cL D L i m)
      * Work.MotTDG.wvec D L e M m) = Work.MotTDG.kappaShift D L e M i := by
  have hcoef : ∀ j, (∑ m, algebraMap L (FunctionField (D.E.baseChange L)) (Work.MotTDG.cL D L i m)
      * algebraMap L (FunctionField (D.E.baseChange L)) (Work.MotTDG.eL D L e m j))
      = if i = j then (1 : FunctionField (D.E.baseChange L)) else 0 := by
    intro j
    rw [Finset.sum_congr rfl (fun m _ => (map_mul _ _ _).symm), ← map_sum, ← Matrix.mul_apply,
      Work.MotTDG.cL_mul_eL D L e he, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]
  have hsum : (∑ j, (if i = j then (1 : FunctionField (D.E.baseChange L)) else 0)
      * Work.MotTDG.kappaShift D L e M j) = Work.MotTDG.kappaShift D L e M i := by
    rw [Finset.sum_eq_single i
      (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
      (fun hnot => absurd (Finset.mem_univ i) hnot)]
    rw [if_pos rfl, one_mul]
  simp only [Work.MotTDG.wvec]
  rw [Finset.sum_congr rfl (fun m _ => by rw [Finset.mul_sum]), Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun j _ => by
    rw [Finset.sum_congr rfl (fun m _ => (mul_assoc _ _ _).symm), ← Finset.sum_mul])]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hcoef j]), hsum]

/-- The Pfaffians vanish at `kappaShift (diag c^i)` for `c^5 = 1`. -/
theorem tdg_kleinP_kappaShift_Mdiag_zero (D : Work.MotV.KleinData 𝕜)
    (hke : ∀ (L' : Type) [Field L'] [Algebra 𝕜 L'] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L') k = 0)
    (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (c : L) (hc5 : c ^ 5 = 1) (hcne : c ≠ 0) (k : Fin 5) :
    Work.MotK.kleinP (algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L D.a))
      (algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L D.b))
      (Work.MotTDG.kappaShift D L e (tdg_Mdiag L c)) k = 0 := by
  have hsplit : Work.MotTDG.kappaShift D L e (tdg_Mdiag L c)
      = fun i : Fin 5 => (Work.MotTDG.ell D L e (Work.MotTDG.kvec D L (tdg_Mdiag L c)))⁻¹ *
          ((algebraMap L (FunctionField (D.E.baseChange L)) c) ^ (i : ℕ)
            * Work.MotV.kleinCoord D L i) := by
    funext i
    rw [Work.MotTDG.kappaShift, tdg_kvec_Mdiag D L c i, ← map_pow, div_eq_mul_inv]
    refl_ring1
  rw [hsplit, tdg_kleinP_smul,
    Work.MotK.KleinPScale (algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L D.a))
      (algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L D.b))
      (algebraMap L (FunctionField (D.E.baseChange L)) c)
      (by rw [← map_pow, hc5, map_one]) (Work.MotV.kleinCoord D L) k,
    show Work.MotK.kleinP (algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L D.a))
        (algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L D.b))
        (Work.MotV.kleinCoord D L) k = 0 from by
      rw [← IsScalarTower.algebraMap_apply 𝕜 L (FunctionField (D.E.baseChange L)) D.a,
        ← IsScalarTower.algebraMap_apply 𝕜 L (FunctionField (D.E.baseChange L)) D.b]
      exact hke L k,
    mul_zero, mul_zero]

/-- **The diagonal construction.**  For `c^5 = 1`, `c ≠ 0`, the diagonal rescaling
`κ_i ↦ c^i κ_i / ℓ(c^i κ_i)` of the Klein coordinates is induced by an `L`-algebra endomorphism
of `L(E)`. -/
theorem tdg_diag_construction (D : Work.MotV.KleinData 𝕜) (hab : D.a * D.b ≠ 0)
    (hke : ∀ (L' : Type) [Field L'] [Algebra 𝕜 L'] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L') k = 0)
    (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (c : L) (hc5 : c ^ 5 = 1) (hcne : c ≠ 0) :
    ∃ φ : FunctionField (D.E.baseChange L) →ₐ[L] FunctionField (D.E.baseChange L),
      ∀ i, φ (Work.MotV.kleinCoord D L i) = Work.MotTDG.kappaShift D L e (tdg_Mdiag L c) i := by
  have hℓ : Work.MotTDG.ell D L e (Work.MotTDG.kvec D L (tdg_Mdiag L c)) ≠ 0 :=
    tdg_ell_kvec_Mdiag_ne_zero D L e he c hcne
  have hv'0 : Work.MotTDG.wvec D L e (tdg_Mdiag L c) 0 = 1 :=
    tdg_wvec_zero D L e (tdg_Mdiag L c) hℓ
  have hCv' : ∀ i, (∑ m, algebraMap L (FunctionField (D.E.baseChange L))
      (Work.MotTDG.cL D L i m) * Work.MotTDG.wvec D L e (tdg_Mdiag L c) m)
      = Work.MotTDG.kappaShift D L e (tdg_Mdiag L c) i :=
    fun i => tdg_cv_kappaShift D L e he (tdg_Mdiag L c) i
  have hpκ' : ∀ k, Work.MotK.kleinP
      (algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L D.a))
      (algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L D.b))
      (Work.MotTDG.kappaShift D L e (tdg_Mdiag L c)) k = 0 :=
    fun k => tdg_kleinP_kappaShift_Mdiag_zero D hke L e he c hc5 hcne k
  have hq : ∀ j, Work.MotTDG.vwQuad
      (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₁)
      (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₂)
      (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₃)
      (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₄)
      (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₆)
      (Work.MotTDG.wvec D L e (tdg_Mdiag L c)) j = 0 := by
    have hmv : ((Work.MotTDG.muMat D L).map
        (algebraMap L (FunctionField (D.E.baseChange L)))).mulVec
        (fun j => Work.MotTDG.vwQuad
          (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₁)
          (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₂)
          (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₃)
          (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₄)
          (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₆)
          (Work.MotTDG.wvec D L e (tdg_Mdiag L c)) j) = 0 := by
      funext k
      have h := tdg_reduce_F D L hke (Work.MotTDG.wvec D L e (tdg_Mdiag L c)) k
      rw [show (fun i => ∑ m, algebraMap L (FunctionField (D.E.baseChange L))
              (Work.MotTDG.cL D L i m) * Work.MotTDG.wvec D L e (tdg_Mdiag L c) m)
            = Work.MotTDG.kappaShift D L e (tdg_Mdiag L c) from funext hCv'] at h
      rw [hpκ' k] at h
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply]
      exact h.symm
    have hdetF : ((Work.MotTDG.muMat D L).map
        (algebraMap L (FunctionField (D.E.baseChange L)))).det ≠ 0 := by
      rw [show (Work.MotTDG.muMat D L).map (algebraMap L (FunctionField (D.E.baseChange L)))
          = (algebraMap L (FunctionField (D.E.baseChange L))).mapMatrix
            (Work.MotTDG.muMat D L) from rfl]
      rw [← RingHom.map_det (algebraMap L (FunctionField (D.E.baseChange L)))
        (Work.MotTDG.muMat D L)]
      exact (map_ne_zero_iff _
        (FaithfulSMul.algebraMap_injective L (FunctionField (D.E.baseChange L)))).mpr
        (tdg_muMat_det_ne_zero D hab hke L e he)
    have hinj : Function.Injective
        ((Work.MotTDG.muMat D L).map
          (algebraMap L (FunctionField (D.E.baseChange L)))).mulVec :=
      (Matrix.mulVec_injective_iff).mpr ((Matrix.linearIndependent_cols_iff_isUnit).mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdetF)))
    have hzero := hinj (show
        ((Work.MotTDG.muMat D L).map
          (algebraMap L (FunctionField (D.E.baseChange L)))).mulVec
          (fun j => Work.MotTDG.vwQuad
            (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₁)
            (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₂)
            (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₃)
            (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₄)
            (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₆)
            (Work.MotTDG.wvec D L e (tdg_Mdiag L c)) j)
        = ((Work.MotTDG.muMat D L).map
          (algebraMap L (FunctionField (D.E.baseChange L)))).mulVec 0 from by
      rw [hmv, Matrix.mulVec_zero])
    intro j
    exact congrFun hzero j
  have hv3 : Work.MotTDG.wvec D L e (tdg_Mdiag L c) 3
      = (Work.MotTDG.wvec D L e (tdg_Mdiag L c) 1) ^ 2 := by
    have h := hq 0
    simp only [Work.MotTDG.vwQuad, Matrix.cons_val_zero] at h
    rw [hv'0] at h
    simp only [one_mul] at h
    linear_combination (norm := refl_ring1) h
  have hv4 : Work.MotTDG.wvec D L e (tdg_Mdiag L c) 4
      = Work.MotTDG.wvec D L e (tdg_Mdiag L c) 1
        * Work.MotTDG.wvec D L e (tdg_Mdiag L c) 2 := by
    have h := hq 1
    simp only [Work.MotTDG.vwQuad, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at h
    rw [hv'0] at h
    simp only [one_mul] at h
    linear_combination (norm := refl_ring1) h
  have hW : (Work.MotTDG.wvec D L e (tdg_Mdiag L c) 2) ^ 2
      + algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₁
        * Work.MotTDG.wvec D L e (tdg_Mdiag L c) 1
        * Work.MotTDG.wvec D L e (tdg_Mdiag L c) 2
      + algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₃
        * Work.MotTDG.wvec D L e (tdg_Mdiag L c) 2
      = (Work.MotTDG.wvec D L e (tdg_Mdiag L c) 1) ^ 3
        + algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₂
          * (Work.MotTDG.wvec D L e (tdg_Mdiag L c) 1) ^ 2
        + algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₄
          * Work.MotTDG.wvec D L e (tdg_Mdiag L c) 1
        + algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₆ := by
    have h := hq 3
    simp only [Work.MotTDG.vwQuad, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_succ, Matrix.cons_val] at h
    rw [hv'0, hv3] at h
    simp only [one_mul, mul_one, one_pow] at h
    linear_combination (norm := refl_ring1) h
  have hUV : WeierstrassCurve.Affine.Equation
      ((D.E.baseChange L).map (algebraMap L (FunctionField (D.E.baseChange L))))
      (Work.MotTDG.wvec D L e (tdg_Mdiag L c) 1)
      (Work.MotTDG.wvec D L e (tdg_Mdiag L c) 2) := by
    rw [WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    exact hW
  have hU : Transcendental L (Work.MotTDG.wvec D L e (tdg_Mdiag L c) 1) := by
    intro halg
    obtain ⟨c0, hc0⟩ := tdg_algebraic_mem_base (D.E.baseChange L) halg
    have hkey : ∀ m : Fin 5,
        Work.MotTDG.wvec D L e (tdg_Mdiag L c) m
          * Work.MotTDG.ell D L e (Work.MotTDG.kvec D L (tdg_Mdiag L c))
        = ∑ i, (algebraMap 𝕜 L (e m i) * c ^ (i : ℕ)) • Work.MotV.kleinCoord D L i := by
      intro m
      simp only [Work.MotTDG.wvec, Work.MotTDG.kappaShift, Work.MotTDG.eL]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tdg_kvec_Mdiag D L c i, Algebra.smul_def, map_mul]
      field_simp
    have hgoal : (∑ i : Fin 5, (algebraMap 𝕜 L (e 1 i) * c ^ (i : ℕ))
          • Work.MotV.kleinCoord D L i)
        = ∑ i : Fin 5, (c0 * (algebraMap 𝕜 L (e 0 i) * c ^ (i : ℕ)))
          • Work.MotV.kleinCoord D L i := by
      have h1 := hkey 1
      rw [hc0] at h1
      have h0 := hkey 0
      rw [hv'0, one_mul] at h0
      rw [← h1, h0, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Algebra.smul_def, map_mul]
      refl_ring1
    have hrel : (∑ i ∈ (Finset.univ : Finset (Fin 5)),
        (algebraMap 𝕜 L (e 1 i) * c ^ (i : ℕ)
          - c0 * (algebraMap 𝕜 L (e 0 i) * c ^ (i : ℕ)))
        • Work.MotV.kleinCoord D L i) = 0 := by
      have hsub : (∑ i ∈ (Finset.univ : Finset (Fin 5)),
            (algebraMap 𝕜 L (e 1 i) * c ^ (i : ℕ)
              - c0 * (algebraMap 𝕜 L (e 0 i) * c ^ (i : ℕ)))
            • Work.MotV.kleinCoord D L i)
          = (∑ i : Fin 5, (algebraMap 𝕜 L (e 1 i) * c ^ (i : ℕ))
              • Work.MotV.kleinCoord D L i)
            - (∑ i : Fin 5, (c0 * (algebraMap 𝕜 L (e 0 i) * c ^ (i : ℕ)))
              • Work.MotV.kleinCoord D L i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [sub_smul]
      rw [hsub, hgoal, sub_self]
    have hj := (linearIndependent_iff'.mp (Work.MotTDG.kleinCoord_linearIndependent D L e he))
      (Finset.univ : Finset (Fin 5))
      (fun i => algebraMap 𝕜 L (e 1 i) * c ^ (i : ℕ)
        - c0 * (algebraMap 𝕜 L (e 0 i) * c ^ (i : ℕ))) hrel
    have hall : ∀ i, algebraMap 𝕜 L (e 1 i) = c0 * algebraMap 𝕜 L (e 0 i) := by
      intro i
      have h := hj i (Finset.mem_univ i)
      have h4 : (algebraMap 𝕜 L (e 1 i) - c0 * algebraMap 𝕜 L (e 0 i)) * c ^ (i : ℕ) = 0 := by
        linear_combination (norm := refl_ring1) h
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact sub_eq_zero.mp h5
      · exact absurd h5 (pow_ne_zero _ hcne)
    have hb1 : Work.MotTDG.basE (D.E.baseChange L) 1
        = algebraMap L (FunctionField (D.E.baseChange L)) c0 := by
      rw [Work.MotTDG.basE_eq_eL_kleinCoord D L e he 1]
      calc (∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (Work.MotTDG.eL D L e 1 i)
              * Work.MotV.kleinCoord D L i)
          = ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) c0
              * (algebraMap L (FunctionField (D.E.baseChange L)) (Work.MotTDG.eL D L e 0 i)
                * Work.MotV.kleinCoord D L i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [Work.MotTDG.eL]
            rw [hall i, map_mul]
            refl_ring1
        _ = algebraMap L (FunctionField (D.E.baseChange L)) c0
              * (∑ i, algebraMap L (FunctionField (D.E.baseChange L))
                  (Work.MotTDG.eL D L e 0 i) * Work.MotV.kleinCoord D L i) := by
            rw [Finset.mul_sum]
        _ = algebraMap L (FunctionField (D.E.baseChange L)) c0 * 1 := by
            rw [← Work.MotTDG.basE_eq_eL_kleinCoord D L e he 0, Work.MotTDG.basE_zero]
        _ = algebraMap L (FunctionField (D.E.baseChange L)) c0 := mul_one _
    have htr : Transcendental L (Work.MotTDG.basE (D.E.baseChange L) 1) := by
      rw [Work.MotTDG.basE_one, Work.MotTDG.genX_eq]
      exact Work.MotC2.transcendental_genX (D.E.baseChange L)
    exact htr (hb1 ▸ isAlgebraic_algebraMap c0)
  obtain ⟨φ, hφx, hφy⟩ := Work.MotTDG.exists_algHom_of_point (D.E.baseChange L)
    (Work.MotTDG.wvec D L e (tdg_Mdiag L c) 1) (Work.MotTDG.wvec D L e (tdg_Mdiag L c) 2) hUV hU
  refine ⟨φ, fun i => ?_⟩
  have hφbas : ∀ m, φ (Work.MotTDG.basE (D.E.baseChange L) m)
      = Work.MotTDG.wvec D L e (tdg_Mdiag L c) m := by
    intro m
    fin_cases m
    · change φ (1 : FunctionField (D.E.baseChange L))
          = Work.MotTDG.wvec D L e (tdg_Mdiag L c) 0
      rw [map_one, hv'0]
    · change φ (Work.MotV.genX (D.E.baseChange L))
          = Work.MotTDG.wvec D L e (tdg_Mdiag L c) 1
      exact hφx
    · change φ (Work.MotV.genY (D.E.baseChange L))
          = Work.MotTDG.wvec D L e (tdg_Mdiag L c) 2
      exact hφy
    · change φ ((Work.MotV.genX (D.E.baseChange L)) ^ 2)
          = Work.MotTDG.wvec D L e (tdg_Mdiag L c) 3
      rw [map_pow, hφx]
      exact hv3.symm
    · change φ (Work.MotV.genX (D.E.baseChange L) * Work.MotV.genY (D.E.baseChange L))
          = Work.MotTDG.wvec D L e (tdg_Mdiag L c) 4
      rw [map_mul, hφx, hφy]
      exact hv4.symm
  rw [Work.MotTDG.kleinCoord_eq_cL, map_sum]
  exact (Finset.sum_congr rfl fun m _ => by rw [map_mul, φ.commutes, hφbas m]).trans (hCv' i)

/-- **Composing diagonal constructions.**  If `φ` induces the diagonal rescaling with parameter
`d` on the Klein coordinates, then it maps the diagonal rescaling with parameter `c` back to the
Klein coordinates themselves, provided `c * d = 1`. -/
theorem tdg_phi_kappaShift_Mdiag (D : Work.MotV.KleinData 𝕜) (L : Type) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (φ : FunctionField (D.E.baseChange L) →ₐ[L] FunctionField (D.E.baseChange L))
    (d : L) (hdne : d ≠ 0)
    (hφ : ∀ j, φ (Work.MotV.kleinCoord D L j)
      = Work.MotTDG.kappaShift D L e (tdg_Mdiag L d) j)
    (c : L) (hcne : c ≠ 0) (hcd : c * d = 1) (i : Fin 5) :
    φ (Work.MotTDG.kappaShift D L e (tdg_Mdiag L c) i) = Work.MotV.kleinCoord D L i := by
  have hhd : Work.MotTDG.ell D L e (Work.MotTDG.kvec D L (tdg_Mdiag L d)) ≠ 0 :=
    tdg_ell_kvec_Mdiag_ne_zero D L e he d hdne
  have hkey : ∀ j, φ (Work.MotTDG.kvec D L (tdg_Mdiag L c) j)
      = algebraMap L (FunctionField (D.E.baseChange L)) ((c * d) ^ (j : ℕ))
        * Work.MotV.kleinCoord D L j
        / Work.MotTDG.ell D L e (Work.MotTDG.kvec D L (tdg_Mdiag L d)) := by
    intro j
    rw [tdg_kvec_Mdiag D L c j, map_mul, AlgHom.commutes, hφ j]
    rw [Work.MotTDG.kappaShift, tdg_kvec_Mdiag D L d j]
    rw [map_pow, map_pow, map_pow, map_mul, mul_pow]
    first | refl_ring1 | ring
  have hterm : ∀ j : Fin 5,
      φ (algebraMap L (FunctionField (D.E.baseChange L)) (Work.MotTDG.eL D L e 0 j)
          * Work.MotTDG.kvec D L (tdg_Mdiag L c) j)
      = algebraMap L (FunctionField (D.E.baseChange L))
          (Work.MotTDG.eL D L e 0 j * (c * d) ^ (j : ℕ))
        * Work.MotV.kleinCoord D L j
        / Work.MotTDG.ell D L e (Work.MotTDG.kvec D L (tdg_Mdiag L d)) := by
    intro j
    rw [map_mul, AlgHom.commutes, hkey j]
    rw [div_eq_mul_inv, div_eq_mul_inv, map_mul]
    refl_ring1
  have hphc : φ (Work.MotTDG.ell D L e (Work.MotTDG.kvec D L (tdg_Mdiag L c)))
      = 1 / Work.MotTDG.ell D L e (Work.MotTDG.kvec D L (tdg_Mdiag L d)) := by
    rw [Work.MotTDG.ell, map_sum]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_div]
    have hone : (∑ j : Fin 5, algebraMap L (FunctionField (D.E.baseChange L))
          (Work.MotTDG.eL D L e 0 j * (c * d) ^ (j : ℕ)) * Work.MotV.kleinCoord D L j) = 1 := by
      simp only [hcd, one_pow, mul_one]
      rw [← Work.MotTDG.basE_eq_eL_kleinCoord D L e he 0, Work.MotTDG.basE_zero]
    rw [hone]
  rw [Work.MotTDG.kappaShift, map_div₀, hkey i, hphc]
  rw [show (c * d) ^ (i : ℕ) = 1 from by rw [hcd, one_pow], map_one, one_mul]
  rw [div_div_div_cancel_right₀ hhd, div_one]

end Diag

end

/-- **`T_diag` is a theorem, not data**: `klein_eq` + `spans` (with `a*b ≠ 0`) force the diagonal
automorphism for *every* Klein datum.  Full route (the lead's node TDG: the `spans` matrix `E`, the
five Veronese–Weierstrass quadrics `vwQuad`, the 15-line `ring` identity `p_k(E v) = Σ μ_kj vwQuad_j`
and `det μ ≠ 0`) in `Submission/Work/MotK/GUIDE_TDiagGeneric.md`; the lead's own write-up is
`MOTIVIC_KDATA_LEAD.md` §3 and the subproject `MotTDG`.  This is the last gap of the KDATA area:
`Work.MotT.kpData_T_diag` and hence `Work.MotK.ExistsKleinData` become one-line corollaries.
Do NOT chase the chord--tangent certificate (80k monomials) and do not use
`Work.MotK.TDiagAbstract` (its `hker` is unsatisfiable, `MOTIVIC_KDATA_LEAD.md` §1.3). -/
theorem T_diag_of_kleinEq_spans {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (hab : D.a * D.b ≠ 0)
    (hke : ∀ (L : Type) [Field L] [Algebra 𝕜 L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L) k = 0)
    (hsp : ∃ e : Fin 5 → Fin 5 → 𝕜, ∀ (L : Type) [Field L] [Algebra 𝕜 L] (m : Fin 5),
      Work.MotV.kleinBas D L m = ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i) :
    ∀ (L : Type) [Field L] [Algebra 𝕜 L] (ζ : L), IsPrimitiveRoot ζ 5 →
      ∃ σ : WeierstrassCurve.Affine.FunctionField (D.E.baseChange L) ≃ₐ[L]
          WeierstrassCurve.Affine.FunctionField (D.E.baseChange L),
        ∀ i, σ (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0) =
          algebraMap L _ ζ ^ (i : ℕ) *
            (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0) := by
  intro L _ _ ζ hζ
  obtain ⟨e, he⟩ := hsp
  have heL : ∀ m : Fin 5, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i := fun m => he L m
  have hζ5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hζne : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζinv5 : ζ⁻¹ ^ 5 = 1 := by rw [inv_pow, hζ5, inv_one]
  have hζinvne : ζ⁻¹ ≠ 0 := inv_ne_zero hζne
  obtain ⟨φ, hφ⟩ := tdg_diag_construction D hab hke L e heL ζ hζ5 hζne
  obtain ⟨ψ, hψ⟩ := tdg_diag_construction D hab hke L e heL ζ⁻¹ hζinv5 hζinvne
  have hcomp1 : ψ.comp φ = AlgHom.id L (FunctionField (D.E.baseChange L)) := by
    apply Work.MotTDG.algHom_eq_id_of_kleinCoord_ratio D L e heL
    intro i
    rw [AlgHom.comp_apply, map_div₀, map_div₀]
    rw [show ψ (φ (Work.MotV.kleinCoord D L i)) = Work.MotV.kleinCoord D L i from by
        rw [hφ i]
        exact tdg_phi_kappaShift_Mdiag D L e heL ψ ζ⁻¹ hζinvne hψ ζ hζne
          (mul_inv_cancel₀ hζne) i,
      show ψ (φ (Work.MotV.kleinCoord D L 0)) = Work.MotV.kleinCoord D L 0 from by
        rw [hφ 0]
        exact tdg_phi_kappaShift_Mdiag D L e heL ψ ζ⁻¹ hζinvne hψ ζ hζne
          (mul_inv_cancel₀ hζne) 0]
  have hcomp2 : φ.comp ψ = AlgHom.id L (FunctionField (D.E.baseChange L)) := by
    apply Work.MotTDG.algHom_eq_id_of_kleinCoord_ratio D L e heL
    intro i
    rw [AlgHom.comp_apply, map_div₀, map_div₀]
    rw [show φ (ψ (Work.MotV.kleinCoord D L i)) = Work.MotV.kleinCoord D L i from by
        rw [hψ i]
        exact tdg_phi_kappaShift_Mdiag D L e heL φ ζ hζne hφ ζ⁻¹ hζinvne
          (inv_mul_cancel₀ hζne) i,
      show φ (ψ (Work.MotV.kleinCoord D L 0)) = Work.MotV.kleinCoord D L 0 from by
        rw [hψ 0]
        exact tdg_phi_kappaShift_Mdiag D L e heL φ ζ hζne hφ ζ⁻¹ hζinvne
          (inv_mul_cancel₀ hζne) 0]
  refine ⟨AlgEquiv.ofAlgHom φ ψ hcomp2 hcomp1, fun i => ?_⟩
  rw [AlgEquiv.ofAlgHom_apply]
  rw [map_div₀, hφ i, hφ 0]
  rw [Work.MotTDG.kappaShift, Work.MotTDG.kappaShift, tdg_kvec_Mdiag, tdg_kvec_Mdiag]
  have hhc : Work.MotTDG.ell D L e (Work.MotTDG.kvec D L (tdg_Mdiag L ζ)) ≠ 0 :=
    tdg_ell_kvec_Mdiag_ne_zero D L e heL ζ hζne
  rw [div_div_div_cancel_right₀ hhc]
  rw [show ζ ^ ((0 : Fin 5) : ℕ) = (1 : L) from by
    rw [show ((0 : Fin 5) : ℕ) = 0 from rfl, pow_zero], map_one, one_mul,
    ← map_pow, mul_div_assoc]

end Work.MotK
