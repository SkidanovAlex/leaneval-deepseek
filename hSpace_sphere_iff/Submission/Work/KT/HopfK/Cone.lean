/-
# The cone side of the `hopf_K` computation

For the Hopf construction `f : S^{4m-1} → S^{2m}` and its mapping cone `C_f`, the cofibre sequence
gives a class `a ∈ K̃(C_f)` lifting a generator of `K̃(S^{2m})`.  Writing `a = [p] - [e]` with the
"collared representatives" `p₊`, `p₋` (equal to `e` on the two caps, cf. `hk_cap_triv`), the
*square* of `a` is the class

`a² = [p₊ ⊗ p₋ ⊕ e ⊗ e] - [p₊ ⊗ e ⊕ e ⊗ p₋]`

(`isk0Mul_sq_eq` below).  The relative-product lemma `hk_rotation` identifies the two block
matrices up to conjugation on the base `Tgt m`, so `a²` vanishes on the base and comes from
`K̃(C_f / T) = K̃(S^{4m})` (`cone_exact` (1)): this is `hk_cone_sq`.
-/
import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.HopfK.Basic

namespace Work.KT

noncomputable section

/-! ## Commutativity of the cone algebra -/

/-- `coneAlg f` is a commutative ring (it is a subalgebra of a product of algebras of
complex-valued functions). -/
lemma coneAlg_comm (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (x y : coneAlg f) :
    x * y = y * x :=
  Subtype.ext (mul_comm _ _)

/-! ## The square of a class represented as `[p] - [e]` -/

/-- **The relative product.**  If `a = [p] - [e] = [q] - [e]` in `K₀ A`, then the square of `a`
with respect to any ring product `μ` is the difference of the classes of the two block matrices
`p ⊗ q ⊕ e ⊗ e` and `p ⊗ e ⊕ e ⊗ q`. -/
theorem isk0Mul_sq_eq {A : Type} [Ring A] (hcomm : ∀ x y : A, x * y = y * x)
    (a : K0 A) (μ : K0 A →+ K0 A →+ K0 A) (hμ : IsK0Mul μ)
    (p q e : Mat A) (hp : p.IsIdem) (hq : q.IsIdem) (he : e.IsIdem)
    (ha : cls p - cls e = a) (hb : cls q - cls e = a) :
    μ a a = cls ((p.kron q).sum (e.kron e)) - cls ((p.kron e).sum (e.kron q)) := by
  have hpq : (p.kron q).IsIdem := Mat.kron_idem hcomm hp hq
  have hpe : (p.kron e).IsIdem := Mat.kron_idem hcomm hp he
  have heq : (e.kron q).IsIdem := Mat.kron_idem hcomm he hq
  have hee : (e.kron e).IsIdem := Mat.kron_idem hcomm he he
  have hgoal : μ a a = μ (cls p - cls e) (cls q - cls e) :=
    congrArg₂ (fun x y : K0 A => μ x y) ha.symm hb.symm
  have hexp : μ (cls p - cls e) (cls q - cls e) =
      (μ (cls p) (cls q) - μ (cls p) (cls e)) - (μ (cls e) (cls q) - μ (cls e) (cls e)) := by
    rw [map_sub, map_sub]
    simp only [AddMonoidHom.sub_apply]
    abel
  rw [hgoal, hexp,
    IsK0Mul_cls hμ hp hq, IsK0Mul_cls hμ hp he, IsK0Mul_cls hμ he hq, IsK0Mul_cls hμ he he,
    cls_sum hpq hee, cls_sum hpe heq]
  abel

/-- The entrywise image of a block sum is the block sum of the entrywise images. -/
lemma Mat.map_sum {A B : Type} [Ring A] [Ring B] (φ : A →+* B) (p q : Mat A) :
    (p.sum q).map φ = (p.map φ).sum (q.map φ) := by
  obtain ⟨n, M⟩ := p
  obtain ⟨k, N⟩ := q
  change (⟨n + k, (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks M 0 0 N)).map φ⟩ : Mat B) =
    ⟨n + k, Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (M.map φ) 0 0 (N.map φ))⟩
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;> simp


/-! ## The relative square lies in the relative group -/

/-- The constant diagonal idempotent `diag(1_r,0)` over `coneAlg f`. -/
abbrev coneDiag (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (r n : ℕ) : Mat (coneAlg f) :=
  ⟨n, Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then (1 : coneAlg f) else 0)⟩

/-- The constant diagonal idempotent `diag(1_r,0)` over the base `C(Tgt m, ℂ)`. -/
abbrev baseDiag (m : ℕ) (r n : ℕ) : Mat C(Tgt m, ℂ) :=
  ⟨n, Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then (1 : C(Tgt m, ℂ)) else 0)⟩

set_option maxHeartbeats 1600000 in
lemma coneDiag_isIdem (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (r n : ℕ) :
    Mat.IsIdem (coneDiag m f r n) :=
  diagMat_isIdem (coneAlg f) r n

set_option maxHeartbeats 1600000 in
/-- **The relative square.**  If the two distributions `p ⊗ q ⊕ e ⊗ e` and `p ⊗ e ⊕ e ⊗ q` (with
`e = diag(1_r,0)`) have the same class after restricting to the base — which, by `hk_rotation`,
holds as soon as `p` and `q` are the collared representatives — then the square of the class they
represent lies in the image of `K̃(C_f/T) → K(C_f)`: the exactness statement of `Work.KT.cone_exact`
(1) is taken here as an explicit hypothesis, so that this file does not depend on that node. -/
theorem cone_sq_relToCone (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (y0 : Ball (Eu m × Eu m)) (hy0 : y0 ∈ bdry (Eu m × Eu m))
    (n r : ℕ) (p q : Matrix (Fin n) (Fin n) (coneAlg f)) (hp : p * p = p) (hq : q * q = q)
    (hCE : ∀ z : K0 (coneAlg f), K0.mapA (coneToT f) z = 0 →
      ∃ w : K0 (Kpair (Eu m × Eu m)), K0.mapA (augPair (Eu m × Eu m) y0) w = 0 ∧
        K0.mapA (relToCone f y0 hy0) w = z)
    (hT : cls (Mat.sum (Mat.kron ⟨n, p.map (coneToT f)⟩ ⟨n, q.map (coneToT f)⟩)
            (Mat.kron ((coneDiag m f r n).map (coneToT f))
              ((coneDiag m f r n).map (coneToT f)))) =
          cls (Mat.sum (Mat.kron ⟨n, p.map (coneToT f)⟩ ((coneDiag m f r n).map (coneToT f)))
            (Mat.kron ((coneDiag m f r n).map (coneToT f)) ⟨n, q.map (coneToT f)⟩))) :
    ∃ γ : K0 (Kpair (Eu m × Eu m)),
      K0.mapA (relToCone f y0 hy0) γ =
        cls (Mat.sum (Mat.kron ⟨n, p⟩ ⟨n, q⟩)
          (Mat.kron (coneDiag m f r n) (coneDiag m f r n))) -
        cls (Mat.sum (Mat.kron ⟨n, p⟩ (coneDiag m f r n))
          (Mat.kron (coneDiag m f r n) ⟨n, q⟩)) := by
  have hcomm := coneAlg_comm m f
  have hp' : Mat.IsIdem (⟨n, p⟩ : Mat (coneAlg f)) := hp
  have hq' : Mat.IsIdem (⟨n, q⟩ : Mat (coneAlg f)) := hq
  have he : Mat.IsIdem (coneDiag m f r n) := coneDiag_isIdem m f r n
  set Q₁ : Mat (coneAlg f) := Mat.sum (Mat.kron ⟨n, p⟩ ⟨n, q⟩)
    (Mat.kron (coneDiag m f r n) (coneDiag m f r n)) with hQ₁
  set Q₂ : Mat (coneAlg f) := Mat.sum (Mat.kron ⟨n, p⟩ (coneDiag m f r n))
    (Mat.kron (coneDiag m f r n) ⟨n, q⟩) with hQ₂
  have h1 : Mat.IsIdem Q₁ := by
    rw [hQ₁]
    exact Mat.sum_idem (Mat.kron_idem hcomm hp' hq') (Mat.kron_idem hcomm he he)
  have h2 : Mat.IsIdem Q₂ := by
    rw [hQ₂]
    exact Mat.sum_idem (Mat.kron_idem hcomm hp' he) (Mat.kron_idem hcomm he hq')
  have hz : K0.mapA (coneToT f) (cls Q₁ - cls Q₂) = 0 := by
    rw [map_sub, K0.map_cls _ h1, K0.map_cls _ h2, hQ₁, hQ₂, Mat.map_sum, Mat.map_sum,
      Mat.map_kron, Mat.map_kron, Mat.map_kron, Mat.map_kron]
    exact sub_eq_zero.mpr hT
  obtain ⟨w, _, hw⟩ := hCE (cls Q₁ - cls Q₂) hz
  exact ⟨w, by rw [hQ₁, hQ₂] at hw ⊢; exact hw⟩

end

end Work.KT
