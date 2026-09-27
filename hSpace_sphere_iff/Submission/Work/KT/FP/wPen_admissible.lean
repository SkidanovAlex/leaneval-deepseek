import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.Fund.isUnit_matrix_forall
import Submission.Work.Idx.pen_annulus

/-!
# `Work.KT.FP.wPen_admissible`

The W linearisation `M_b(z) = z • wPenA + wPenB b` of a polynomial clutching function
`q_b(z) = Σ_j b_j z^j` (Hatcher, VBKT, the "companion pencil") is invertible exactly where
`q_b(z)` is.  Consequently, if the coefficient sequence `b : Fin (d+1) → Mₙ(C(X, ℂ))` has the
property that `Σ_j b_j(x) z^j` is invertible for every `(x, z) ∈ X × S¹`, then

* the W clutching function `wPenClutch b` is a unit over `C(X × S¹, ℂ)`, and
* the pencil `z ↦ z • wPenAf + wPenBf b` is a unit on a closed annulus `{ρ ≤ ‖z‖ ≤ 1}` with
  `0 < ρ < 1`.

The mathematical content is the **kernel correspondence**: for `z` and a coefficient sequence `b`,
the matrices `M = z • A + B` (the block companion pencil) and `Q = Σ_j z^j • b_j` have kernels in
canonical bijection, `v ↦ v₀`, with inverse `w ↦ (z^i w)_i`.  This holds over any commutative ring.
-/

namespace Work.KT.FP

open Matrix

noncomputable section

/-! ## Linear algebra: kernel triviality over a field -/

/-- Over a field, a square matrix is a unit iff its kernel (as a `mulVec` map) is trivial. -/
lemma isUnit_iff_mulVec_eq_zero {K : Type*} [Field K] {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m K) : IsUnit A ↔ ∀ v, A *ᵥ v = 0 → v = 0 := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  exact Iff.trans (LinearMap.ker_eq_bot (f := A.mulVecLin)).symm Matrix.ker_mulVecLin_eq_bot_iff

/-! ## The kernel correspondence for the companion pencil -/

/-- Row `i` (`i ≠ d`) of the `z`-coefficient matrix `A` acts as `v ↦ v_i`. -/
lemma wPen_rowA {R : Type*} [CommRing R] (n d : ℕ)
    (A : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) R)
    (hA : ∀ i j, A i j = if i.1 = j.1 ∧ (i.1 : ℕ) ≠ d then
        (1 : Matrix (Fin n) (Fin n) R) i.2 j.2 else 0) :
    ∀ (i : Fin (d + 1)) (_ : (i : ℕ) ≠ d) (a : Fin n) (v : Fin (d + 1) × Fin n → R),
      Matrix.mulVec A v ⟨i, a⟩ = v ⟨i, a⟩ := by
  intro i h a v
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single a]
    · rw [hA, if_pos ⟨rfl, h⟩]; simp
    · intro c _ hc
      rw [hA, if_pos ⟨rfl, h⟩, Matrix.one_apply, if_neg (fun hh => hc hh.symm), zero_mul]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro c _
    rw [hA, if_neg]
    · exact zero_mul _
    · rintro ⟨h1, -⟩; exact hj h1.symm
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- Row `i` (`i ≠ d`) of the constant matrix `B` acts as `v ↦ -v_{i+1}`. -/
lemma wPen_rowB {R : Type*} [CommRing R] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) R)
    (hB : ∀ i j, B i j = if (i.1 : ℕ) + 1 = (j.1 : ℕ) then
        (if (i.1 : ℕ) = d then b j.1 i.2 j.2
          else -(1 : Matrix (Fin n) (Fin n) R) i.2 j.2)
      else if (i.1 : ℕ) = d then b j.1 i.2 j.2 else 0)
    (i : Fin (d + 1)) (h : (i : ℕ) ≠ d) (j : Fin (d + 1)) (hj : (j : ℕ) = (i : ℕ) + 1)
    (a : Fin n) (v : Fin (d + 1) × Fin n → R) :
    Matrix.mulVec B v ⟨i, a⟩ = - v ⟨j, a⟩ := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single a]
    · rw [hB, if_pos (by rw [← hj]), if_neg h, Matrix.one_apply]
      simp
    · intro c _ hc
      rw [hB, if_pos (by rw [← hj]), if_neg h, Matrix.one_apply,
        if_neg (fun hh => hc hh.symm), neg_zero, zero_mul]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  · intro j' _ hj'
    apply Finset.sum_eq_zero
    intro c _
    rw [hB, if_neg, if_neg h]
    · exact zero_mul _
    · intro hcon
      exact hj' (Fin.ext (by rw [hj]; exact hcon)).symm
  · intro hjmem; exact absurd (Finset.mem_univ j) hjmem

/-- Row `(i,a)` of the companion pencil `z • A + B`, for `i ≠ d`. -/
lemma wPen_rowK_lt {R : Type*} [CommRing R] (n d : ℕ) (z : R)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) R)
    (A B : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) R)
    (hA : ∀ i j, A i j = if i.1 = j.1 ∧ (i.1 : ℕ) ≠ d then
        (1 : Matrix (Fin n) (Fin n) R) i.2 j.2 else 0)
    (hB : ∀ i j, B i j = if (i.1 : ℕ) + 1 = (j.1 : ℕ) then
        (if (i.1 : ℕ) = d then b j.1 i.2 j.2
          else -(1 : Matrix (Fin n) (Fin n) R) i.2 j.2)
      else if (i.1 : ℕ) = d then b j.1 i.2 j.2 else 0)
    (i : Fin (d + 1)) (h : (i : ℕ) ≠ d) (j : Fin (d + 1)) (hj : (j : ℕ) = (i : ℕ) + 1)
    (a : Fin n) (v : Fin (d + 1) × Fin n → R) :
    Matrix.mulVec (z • A + B) v ⟨i, a⟩ = z * v ⟨i, a⟩ - v ⟨j, a⟩ := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
    wPen_rowA n d A hA i h a v, wPen_rowB n d b B hB i h j hj a v, smul_eq_mul]
  ring

/-- Row `(d,a)` of the companion pencil `z • A + B`. -/
lemma wPen_rowK_last {R : Type*} [CommRing R] (n d : ℕ) (z : R)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) R)
    (A B : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) R)
    (hA : ∀ i j, A i j = if i.1 = j.1 ∧ (i.1 : ℕ) ≠ d then
        (1 : Matrix (Fin n) (Fin n) R) i.2 j.2 else 0)
    (hB : ∀ i j, B i j = if (i.1 : ℕ) + 1 = (j.1 : ℕ) then
        (if (i.1 : ℕ) = d then b j.1 i.2 j.2
          else -(1 : Matrix (Fin n) (Fin n) R) i.2 j.2)
      else if (i.1 : ℕ) = d then b j.1 i.2 j.2 else 0)
    (a : Fin n) (v : Fin (d + 1) × Fin n → R) :
    Matrix.mulVec (z • A + B) v ⟨⟨d, Nat.lt_succ_self d⟩, a⟩
      = ∑ j : Fin (d + 1), Matrix.mulVec (b j) (fun c => v ⟨j, c⟩) a := by
  have entry_last : ∀ j : Fin (d+1) × Fin n,
      (z • A + B) ⟨⟨d, Nat.lt_succ_self d⟩, a⟩ j = b j.1 a j.2 := by
    intro j
    rw [Matrix.add_apply, Matrix.smul_apply, hA _ j, hB _ j, smul_eq_mul]
    have hAd : ¬ (⟨d, Nat.lt_succ_self d⟩ = j.1 ∧ d ≠ d) := fun hc => hc.2 rfl
    have h2 : ¬ ((⟨d, Nat.lt_succ_self d⟩ : Fin (d + 1)).1 + 1 = (j.1 : ℕ)) := by
      simp only; have := j.1.isLt; omega
    rw [if_neg hAd, if_neg h2]
    simp
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [entry_last]

/-- **The kernel correspondence.**  For any commutative ring, the companion pencil `z • A + B`
has trivial kernel iff the polynomial matrix `Σ_j z^j • b_j` does. -/
theorem wPen_kernel {R : Type*} [CommRing R] (n d : ℕ) (z : R)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) R)
    (A B : Matrix (Fin (d + 1) × Fin n) (Fin (d + 1) × Fin n) R)
    (hA : ∀ i j, A i j = if i.1 = j.1 ∧ (i.1 : ℕ) ≠ d then
        (1 : Matrix (Fin n) (Fin n) R) i.2 j.2 else 0)
    (hB : ∀ i j, B i j = if (i.1 : ℕ) + 1 = (j.1 : ℕ) then
        (if (i.1 : ℕ) = d then b j.1 i.2 j.2
          else -(1 : Matrix (Fin n) (Fin n) R) i.2 j.2)
      else if (i.1 : ℕ) = d then b j.1 i.2 j.2 else 0) :
    (∀ v, Matrix.mulVec (z • A + B) v = 0 → v = 0) ↔
    (∀ w, Matrix.mulVec (∑ j : Fin (d + 1), z ^ (j : ℕ) • b j) w = 0 → w = 0) := by
  constructor
  · intro hM w hw
    have hMσ : Matrix.mulVec (z • A + B)
        (fun p : Fin (d+1) × Fin n => z^(p.1:ℕ) * w p.2) = 0 := by
      funext p
      rcases p with ⟨i, a⟩
      simp only [Pi.zero_apply]
      by_cases hi : (i:ℕ) = d
      · rw [show i = ⟨d, Nat.lt_succ_self d⟩ from Fin.ext hi,
          wPen_rowK_last n d z b A B hA hB a (fun p => z^(p.1:ℕ) * w p.2)]
        rw [show (∑ j : Fin (d+1), Matrix.mulVec (b j) (fun c => z^(j:ℕ) * w c) a)
            = Matrix.mulVec (∑ j : Fin (d+1), z^(j:ℕ) • b j) w a from by
          rw [Matrix.sum_mulVec]
          simp only [Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro j _
          rw [show (fun c => z^(j:ℕ) * w c) = z^(j:ℕ) • w from by funext c; rfl]
          rw [Matrix.mulVec_smul, Matrix.smul_mulVec]]
        rw [hw]; rfl
      · rw [wPen_rowK_lt n d z b A B hA hB i hi ⟨(i:ℕ)+1, by omega⟩ rfl a
            (fun p => z^(p.1:ℕ) * w p.2)]
        rw [pow_succ']
        ring
    funext a
    have h2 := congrFun (hM _ hMσ) (⟨⟨0, Nat.succ_pos d⟩, a⟩ : Fin (d+1) × Fin n)
    simp only [Pi.zero_apply] at h2
    simpa using h2
  · intro hq v hv
    have hrec : ∀ (i : Fin (d+1)) (a : Fin n),
        v ⟨i,a⟩ = z^(i:ℕ) * v ⟨⟨0, Nat.succ_pos d⟩, a⟩ := by
      intro i
      refine Fin.induction (motive := fun i => ∀ a : Fin n,
        v ⟨i,a⟩ = z^(i:ℕ) * v ⟨⟨0, Nat.succ_pos d⟩, a⟩) ?_ ?_ i
      · intro a; simp
      · intro i ih a
        have hne : (i.castSucc : ℕ) ≠ d := by
          simp only [Fin.val_castSucc]; exact ne_of_lt i.isLt
        have hrow := wPen_rowK_lt n d z b A B hA hB i.castSucc hne i.succ (by simp) a v
        have hz : Matrix.mulVec (z • A + B) v ⟨i.castSucc, a⟩ = 0 := by rw [hv]; rfl
        rw [hrow] at hz
        have heq : v ⟨i.succ, a⟩ = z * v ⟨i.castSucc, a⟩ := (sub_eq_zero.mp hz).symm
        rw [heq, ih a]
        simp only [Fin.val_succ, Fin.val_castSucc]
        rw [pow_succ']
        ring
    have hv0 : Matrix.mulVec (∑ j : Fin (d+1), z^(j:ℕ) • b j)
        (fun a => v ⟨⟨0, Nat.succ_pos d⟩, a⟩) = 0 := by
      funext a
      simp only [Pi.zero_apply]
      have hz : ∑ j : Fin (d+1), Matrix.mulVec (b j) (fun c => v ⟨j,c⟩) a = 0 := by
        have h1 : Matrix.mulVec (z • A + B) v ⟨⟨d, Nat.lt_succ_self d⟩, a⟩ = 0 := by
          rw [hv]; rfl
        rwa [wPen_rowK_last n d z b A B hA hB a v] at h1
      rw [← hz]
      rw [Matrix.sum_mulVec]
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [show (fun c => v ⟨j,c⟩) = z^(j:ℕ) • (fun c => v ⟨⟨0, Nat.succ_pos d⟩, c⟩) from by
        funext c
        rw [Pi.smul_apply, hrec j c, smul_eq_mul]]
      rw [Matrix.mulVec_smul, Matrix.smul_mulVec]
    have hv0' : (fun a => v ⟨⟨0, Nat.succ_pos d⟩, a⟩) = 0 := hq _ hv0
    funext p
    rcases p with ⟨i, a⟩
    simp only [Pi.zero_apply]
    have h0 : v ⟨⟨0, Nat.succ_pos d⟩, a⟩ = 0 := by
      have h := congrFun hv0' a; simpa using h
    rw [hrec i a, h0, mul_zero]

/-! ## The entries of the pointwise pencil -/

lemma wPenA_map_apply (X : Type) [TopologicalSpace X] (n d : ℕ) (x : X)
    (i j : Fin (d + 1) × Fin n) :
    ((wPenA X n d).map (Work.KT.evalC x)) i j
      = if i.1 = j.1 ∧ (i.1 : ℕ) ≠ d then (1 : Matrix (Fin n) (Fin n) ℂ) i.2 j.2 else 0 := by
  rw [Matrix.map_apply, wPenA]
  split_ifs <;> simp_all [Matrix.one_apply]

lemma wPenB_map_apply (X : Type) [TopologicalSpace X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (x : X)
    (i j : Fin (d + 1) × Fin n) :
    ((wPenB X n d b).map (Work.KT.evalC x)) i j
      = if (i.1 : ℕ) + 1 = (j.1 : ℕ) then
          (if (i.1 : ℕ) = d then ((b j.1).map (Work.KT.evalC x)) i.2 j.2
            else -(1 : Matrix (Fin n) (Fin n) ℂ) i.2 j.2)
        else if (i.1 : ℕ) = d then ((b j.1).map (Work.KT.evalC x)) i.2 j.2 else 0 := by
  rw [Matrix.map_apply, wPenB]
  split_ifs with h1 h2
  all_goals simp [Matrix.map_apply, Matrix.one_apply, apply_ite]

/-! ## The evaluation identities -/

lemma polyOf_eval (X : Type) [TopologicalSpace X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (x : X) (z : Sph ℂ) :
    (polyOf X n d b).map (fun f => f (x, z))
      = ∑ j : Fin (d + 1), (z : ℂ) ^ (j : ℕ) • (b j).map (Work.KT.evalC x) := by
  ext a c
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply]
  simp only [polyOf, ContinuousMap.mul_apply, pullFun_apply, ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ContinuousMap.pow_apply, Work.KT.zUnit_apply, ContinuousMap.evalAlgHom_apply,
    Work.KT.evalC]
  rw [smul_eq_mul]; ring

lemma wPenClutch_eval (X : Type) [TopologicalSpace X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (x : X) (z : Sph ℂ) :
    (wPenClutch X n d b).map (fun f => f (x, z))
      = (z : ℂ) • (wPenA X n d).map (Work.KT.evalC x)
        + (wPenB X n d b).map (Work.KT.evalC x) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, wPenClutch,
    ContinuousMap.add_apply, ContinuousMap.mul_apply, pullFun_apply, Work.KT.zUnit_apply]
  rw [smul_eq_mul]
  rfl

/-! ## Reindexing and `IsUnit` -/

lemma isUnit_reindex {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (M : Matrix m m R) :
    IsUnit (Matrix.reindex e e M) ↔ IsUnit M := by
  rw [← Matrix.coe_reindexRingEquiv R e]
  exact MulEquiv.isUnit_map (f := (Matrix.reindexRingEquiv R e).toMulEquiv)

/-! ## The main statement -/

theorem wPen_admissible (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hb : ∀ (x : X) (z : Sph ℂ), IsUnit ((polyOf X n d b).map (fun f => f (x, z)))) :
    (∀ (x : X) (z : Sph ℂ), IsUnit ((wPenClutch X n d b).map (fun f => f (x, z)))) ∧
    (∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • wPenAf X n d + wPenBf X n d b)) := by
  -- the pointwise companion pencil is a unit on the unit circle
  have key : ∀ (x : X) (z : ℂ), ‖z‖ = 1 →
      IsUnit (z • (wPenA X n d).map (Work.KT.evalC x)
        + (wPenB X n d b).map (Work.KT.evalC x)) := by
    intro x z hz
    have hzmem : z ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]; exact hz
    have hb' : IsUnit ((polyOf X n d b).map (fun f => f (x, ⟨z, hzmem⟩))) := hb x ⟨z, hzmem⟩
    rw [polyOf_eval] at hb'
    refine (isUnit_iff_mulVec_eq_zero _).mpr ?_
    refine (wPen_kernel n d z (fun j => (b j).map (Work.KT.evalC x)) _ _
      (fun i j => wPenA_map_apply X n d x i j)
      (fun i j => wPenB_map_apply X n d b x i j)).mpr ?_
    exact (isUnit_iff_mulVec_eq_zero _).mp hb'
  refine ⟨?_, ?_⟩
  · intro x z
    have hz' : ‖(z : ℂ)‖ = 1 := by
      have h := Metric.mem_sphere.mp z.2
      rwa [dist_eq_norm, sub_zero] at h
    rw [wPenClutch_eval]
    exact key x (z : ℂ) hz'
  · have hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • wPenAf X n d + wPenBf X n d b) := by
      intro z hz
      refine (Work.KT.Fund.isUnit_matrix_forall ((d + 1) * n) _).mpr (fun x => ?_)
      have hmap : (z • wPenAf X n d + wPenBf X n d b).map (fun f : C(X, ℂ) => f x)
          = Matrix.reindex finProdFinEquiv finProdFinEquiv
              (z • (wPenA X n d).map (Work.KT.evalC x)
                + (wPenB X n d b).map (Work.KT.evalC x)) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, wPenAf, wPenBf,
          Matrix.reindex_apply, Matrix.submatrix_apply]
        rw [smul_eq_mul]; rfl
      rw [hmap]
      exact (isUnit_reindex finProdFinEquiv _).mpr (key x z hz)
    obtain ⟨ε, hε0, hε1, hε⟩ :=
      Work.Idx.pen_annulus X (wPenAf X n d) (wPenBf X n d b) hunit
    exact ⟨1 - ε, by linarith, by linarith, fun z hzl hzr => hε z (by linarith) (by linarith)⟩

end

end Work.KT.FP
