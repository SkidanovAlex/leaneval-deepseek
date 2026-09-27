import Mathlib
import Submission.Work.Drive.PushDisc.milnorLens
import Submission.Work.Drive.PushDisc.det_pairZ_inc_coprod_graph
import Submission.Work.Whitney.det_one_add_of_sq_eq_zero

/-!
# `Work.Drive.PushDisc.lensCornerSign`

The corner sign of the framing chart (the lead's `L1`).

The target statement is `Work.Drive.PushDisc.lensCornerSign`.  Its content is the computation of the
two corner determinants of the frame `[∂ₓΔ, ∂_yΔ, V, ιu]` in the model coordinates `(x,y,u,v)` of
`Work.Drive.Whitney.Mdl k`: writing `A = ∂ₓΔ (±1,0)`, `B = ∂_yΔ (±1,0)`, expanding along the `x`-row
of the frame matrix (in the `(x,y,v,u)`-coordinates of §1) gives

    frameDet T [A, B, V, ιu] = (B).2.1                     (`lcs_frameDet_corner`)

while the two Hadamard relations `∂ₓΔ (1,0) - 2 ∂_yΔ (1,0) = β1` and
`∂ₓΔ (-1,0) + 2 ∂_yΔ (-1,0) = βm1` together with `∂ₓΔ (±1,0) = e_x` give

    det (corner 1) = -(β1).2.1 / 2,      det (corner -1) = (βm1).2.1 / 2,

so that the product is `-(1/4) (β1).2.1 (βm1).2.1 > 0` by `hsgn`.

Organisation:

* §1 the coordinate functionals of the model space and the coordinate equivalence `lcsT`;
* §2 the bridge `frameDet m T F = LinearMap.det (lcsSum F ∘ T)`;
* §3 the evaluation of that determinant on a corner frame (the `(B).2.1` formula);
* §4 the derivative facts at the two corners and the target.
-/

namespace Work.Drive.PushDisc

noncomputable section

open scoped ContDiff Topology
open Filter Set

/-- The `k`-dimensional Euclidean factor of the model space. -/
abbrev lcsE (k : ℕ) : Type := EuclideanSpace ℝ (Fin k)

/-- The model space, under a local name. -/
abbrev lcsM (k : ℕ) : Type := Work.Drive.Whitney.Mdl k

variable {k : ℕ}

/-! ## §1 The coordinate functions of the model space -/

/-- The `x`-coordinate of the model space. -/
def lcsX (k : ℕ) : lcsM k →ₗ[ℝ] ℝ :=
  LinearMap.fst ℝ ℝ (ℝ × (lcsE k × lcsE k))

/-- The `y`-coordinate of the model space. -/
def lcsY (k : ℕ) : lcsM k →ₗ[ℝ] ℝ :=
  (LinearMap.fst ℝ ℝ (lcsE k × lcsE k)).comp (LinearMap.snd ℝ ℝ (ℝ × (lcsE k × lcsE k)))

/-- The `v`-block of the model space. -/
def lcsVp (k : ℕ) : lcsM k →ₗ[ℝ] lcsE k :=
  (LinearMap.snd ℝ (lcsE k) (lcsE k)).comp ((LinearMap.snd ℝ ℝ (lcsE k × lcsE k)).comp
    (LinearMap.snd ℝ ℝ (ℝ × (lcsE k × lcsE k))))

/-- The `u`-block of the model space. -/
def lcsUp (k : ℕ) : lcsM k →ₗ[ℝ] lcsE k :=
  (LinearMap.fst ℝ (lcsE k) (lcsE k)).comp ((LinearMap.snd ℝ ℝ (lcsE k × lcsE k)).comp
    (LinearMap.snd ℝ ℝ (ℝ × (lcsE k × lcsE k))))

@[simp] theorem lcsX_apply (k : ℕ) (ξ : lcsM k) : lcsX k ξ = ξ.1 := rfl
@[simp] theorem lcsY_apply (k : ℕ) (ξ : lcsM k) : lcsY k ξ = ξ.2.1 := rfl
@[simp] theorem lcsVp_apply (k : ℕ) (ξ : lcsM k) : lcsVp k ξ = ξ.2.2.2 := rfl
@[simp] theorem lcsUp_apply (k : ℕ) (ξ : lcsM k) : lcsUp k ξ = ξ.2.2.1 := rfl

/-- The `l`-th `v`-coordinate of the model space. -/
def lcsV (k : ℕ) (l : Fin k) : lcsM k →ₗ[ℝ] ℝ :=
  (LinearMap.proj l).comp ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap.comp (lcsVp k))

/-- The `l`-th `u`-coordinate of the model space. -/
def lcsU (k : ℕ) (l : Fin k) : lcsM k →ₗ[ℝ] ℝ :=
  (LinearMap.proj l).comp ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap.comp (lcsUp k))

@[simp] theorem lcsV_apply (k : ℕ) (l : Fin k) (ξ : lcsM k) : lcsV k l ξ = ξ.2.2.2 l := by
  simp [lcsV, WithLp.linearEquiv]

@[simp] theorem lcsU_apply (k : ℕ) (l : Fin k) (ξ : lcsM k) : lcsU k l ξ = ξ.2.2.1 l := by
  simp [lcsU, WithLp.linearEquiv]

/-- The family of the `2 + k + k` coordinate functionals of the model space, in the order
`(x, y, v, u)`. -/
def lcsCoord (k : ℕ) : Fin (2 + k + k) → (lcsM k →ₗ[ℝ] ℝ) :=
  Fin.append (Fin.append ![lcsX k, lcsY k] (fun l => lcsV k l)) (fun l => lcsU k l)

/-- The coordinate map of the model space. -/
def lcsLin (k : ℕ) : lcsM k →ₗ[ℝ] (Fin (2 + k + k) → ℝ) := LinearMap.pi (lcsCoord k)

@[simp] theorem lcsLin_apply (k : ℕ) (ξ : lcsM k) (j : Fin (2 + k + k)) :
    lcsLin k ξ j = lcsCoord k j ξ := by
  simp [lcsLin, LinearMap.pi_apply]

theorem lcsLin_x (k : ℕ) (ξ : lcsM k) :
    lcsLin k ξ (Fin.castAdd k (Fin.castAdd k (0 : Fin 2))) = ξ.1 := by
  simp [lcsCoord]

theorem lcsLin_y (k : ℕ) (ξ : lcsM k) :
    lcsLin k ξ (Fin.castAdd k (Fin.castAdd k (1 : Fin 2))) = ξ.2.1 := by
  simp [lcsCoord]

theorem lcsLin_v (k : ℕ) (l : Fin k) (ξ : lcsM k) :
    lcsLin k ξ (Fin.castAdd k (Fin.natAdd 2 l)) = ξ.2.2.2 l := by
  simp [lcsCoord]

theorem lcsLin_u (k : ℕ) (l : Fin k) (ξ : lcsM k) :
    lcsLin k ξ (Fin.natAdd (2 + k) l) = ξ.2.2.1 l := by
  simp [lcsCoord]

theorem lcs_zero_of_coord_zero (k : ℕ) (ξ : lcsM k) (h : lcsLin k ξ = 0) : ξ = 0 := by
  have h1 : ξ.1 = 0 := by
    have := congrFun h (Fin.castAdd k (Fin.castAdd k (0 : Fin 2)))
    rw [lcsLin_x] at this
    simpa using this
  have h2 : ξ.2.1 = 0 := by
    have := congrFun h (Fin.castAdd k (Fin.castAdd k (1 : Fin 2)))
    rw [lcsLin_y] at this
    simpa using this
  have h3 : ξ.2.2.1 = 0 := by
    ext l
    have := congrFun h (Fin.natAdd (2 + k) l)
    rw [lcsLin_u] at this
    simpa using this
  have h4 : ξ.2.2.2 = 0 := by
    ext l
    have := congrFun h (Fin.castAdd k (Fin.natAdd 2 l))
    rw [lcsLin_v] at this
    simpa using this
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

theorem lcsLin_injective (k : ℕ) : Function.Injective (lcsLin k) := by
  intro ξ η h
  have h' : lcsLin k (ξ - η) = 0 := by rw [map_sub, h, sub_self]
  have hz : ξ - η = 0 := lcs_zero_of_coord_zero k (ξ - η) h'
  exact sub_eq_zero.mp hz

theorem lcs_finrank_M (k : ℕ) : Module.finrank ℝ (lcsM k) = 2 + k + k := by
  simp only [lcsM, Work.Drive.Whitney.Mdl]
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
    finrank_euclideanSpace]
  simp
  omega

theorem lcs_finrank_fun (k : ℕ) :
    Module.finrank ℝ (Fin (2 + k + k) → ℝ) = 2 + k + k := by
  rw [Module.finrank_fintype_fun_eq_card]
  simp

theorem lcs_finrank (k : ℕ) :
    Module.finrank ℝ (lcsM k) = Module.finrank ℝ (Fin (2 + k + k) → ℝ) := by
  rw [lcs_finrank_M, lcs_finrank_fun]

theorem lcsLin_bijective (k : ℕ) : Function.Bijective (lcsLin k) := by
  refine ⟨lcsLin_injective k, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (lcs_finrank k)).mp
    (lcsLin_injective k)

/-- **The coordinate equivalence of the model space** (`(x,y,v,u)`-coordinates). -/
def lcsT (k : ℕ) : lcsM k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 + k + k)) :=
  (LinearEquiv.ofBijective (lcsLin k) (lcsLin_bijective k)).trans
    (WithLp.linearEquiv 2 ℝ (Fin (2 + k + k) → ℝ)).symm

@[simp] theorem lcsT_apply (k : ℕ) (ξ : lcsM k) (j : Fin (2 + k + k)) :
    lcsT k ξ j = lcsCoord k j ξ := by
  simp [lcsT, WithLp.linearEquiv, LinearMap.pi_apply]

theorem lcsT_x (k : ℕ) (ξ : lcsM k) :
    lcsT k ξ (Fin.castAdd k (Fin.castAdd k (0 : Fin 2))) = ξ.1 := by
  rw [lcsT_apply]; simp [lcsCoord]

theorem lcsT_y (k : ℕ) (ξ : lcsM k) :
    lcsT k ξ (Fin.castAdd k (Fin.castAdd k (1 : Fin 2))) = ξ.2.1 := by
  rw [lcsT_apply]; simp [lcsCoord]

theorem lcsT_v (k : ℕ) (l : Fin k) (ξ : lcsM k) :
    lcsT k ξ (Fin.castAdd k (Fin.natAdd 2 l)) = ξ.2.2.2 l := by
  rw [lcsT_apply]; simp [lcsCoord]

theorem lcsT_u (k : ℕ) (l : Fin k) (ξ : lcsM k) :
    lcsT k ξ (Fin.natAdd (2 + k) l) = ξ.2.2.1 l := by
  rw [lcsT_apply]; simp [lcsCoord]

/-! ## §2 The bridge between `frameDet` and a determinant of an endomorphism -/

/-- The linear combination map `w ↦ ∑ i, w i • F i`. -/
def lcsSum {m : ℕ} {k : ℕ} (F : Fin m → lcsM k) : (Fin m → ℝ) →ₗ[ℝ] lcsM k :=
  ∑ i, (LinearMap.proj i).smulRight (F i)

@[simp] theorem lcsSum_apply {m : ℕ} {k : ℕ} (F : Fin m → lcsM k) (w : Fin m → ℝ) :
    lcsSum F w = ∑ i, w i • F i := by
  simp [lcsSum]

theorem lcsSum_single {m : ℕ} {k : ℕ} (F : Fin m → lcsM k) (i : Fin m) :
    lcsSum F (Pi.single i 1) = F i := by
  rw [lcsSum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne, hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The bridge**: the determinant of a frame read in the coordinates given by a linear
equivalence `T` is the determinant of the endomorphism `ξ ↦ ∑ i, (T ξ) i • F i`. -/
theorem lcs_frameDet_eq {m : ℕ} (T : lcsM k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (F : Fin m → lcsM k) :
    frameDet m T F = LinearMap.det ((lcsSum F).comp
      ((T.trans (WithLp.linearEquiv 2 ℝ (Fin m → ℝ))).toLinearMap)) := by
  classical
  set M : Matrix (Fin m) (Fin m) ℝ := fun i j => (T (F i)) j with hM
  set N : Matrix (Fin m) (Fin m) ℝ := fun i j => (T (F j)) i with hN
  have hMN : M.transpose = N := by
    ext i j
    rw [Matrix.transpose_apply]
  have h1 : frameDet m T F = N.det := by
    rw [frameDet]
    change M.det = N.det
    rw [← Matrix.det_transpose, hMN]
  rw [h1, ← LinearMap.det_toLin']
  have heq : Matrix.toLin' N
      = ((T.trans (WithLp.linearEquiv 2 ℝ (Fin m → ℝ))).toLinearMap).comp (lcsSum F) := by
    apply LinearMap.ext
    intro w
    funext i
    rw [Matrix.toLin'_apply]
    have hR : (((T.trans (WithLp.linearEquiv 2 ℝ (Fin m → ℝ))).toLinearMap).comp
        (lcsSum F)) w i = ∑ j, w j * (T (F j)).ofLp i := by
      simp [LinearMap.comp_apply, WithLp.linearEquiv]
    rw [hR]
    simp only [Matrix.mulVec, dotProduct, hN]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [heq]
  have hconj := LinearMap.det_conj ((lcsSum F).comp
    ((T.trans (WithLp.linearEquiv 2 ℝ (Fin m → ℝ))).toLinearMap))
    (T.trans (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)))
  rw [← hconj]
  congr 1
  ext w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]

/-! ## §3 The corner determinant -/

/-- The inclusion of the `u`-block: `e ↦ (0,0,e,0)`. -/
def lcsUpIncl (k : ℕ) : lcsE k →ₗ[ℝ] lcsM k :=
  (0 : lcsE k →ₗ[ℝ] ℝ).prod ((0 : lcsE k →ₗ[ℝ] ℝ).prod
    ((LinearMap.id : lcsE k →ₗ[ℝ] lcsE k).prod (0 : lcsE k →ₗ[ℝ] lcsE k)))

theorem lcsUpIncl_apply (k : ℕ) (e : lcsE k) : lcsUpIncl k e = (0, 0, e, 0) := rfl

/-- The `l`-th `v`-coordinate on the `(u,v)`-block. -/
def lcsVv (k : ℕ) (l : Fin k) : (lcsE k × lcsE k) →ₗ[ℝ] ℝ :=
  (LinearMap.proj l).comp ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap.comp
    (LinearMap.snd ℝ (lcsE k) (lcsE k)))

@[simp] theorem lcsVv_apply (k : ℕ) (l : Fin k) (p : lcsE k × lcsE k) :
    lcsVv k l p = p.2 l := by
  simp [lcsVv, WithLp.linearEquiv]

/-- `N (x,y,u,v) = (0, 0, y • p + ∑ l, v l • q l, 0)`. -/
def lcsN (k : ℕ) (p : lcsE k) (q : Fin k → lcsE k) : lcsM k →ₗ[ℝ] lcsM k :=
  (lcsUpIncl k).comp ((lcsY k).smulRight p + ∑ l, (lcsV k l).smulRight (q l))

theorem lcsN_apply (k : ℕ) (p : lcsE k) (q : Fin k → lcsE k) (ξ : lcsM k) :
    lcsN k p q ξ = (0, 0, ξ.2.1 • p + ∑ l, (ξ.2.2.2 l) • q l, 0) := by
  simp [lcsN, lcsUpIncl, LinearMap.smulRight_apply]

theorem lcsN_comp_self (k : ℕ) (p : lcsE k) (q : Fin k → lcsE k) :
    (lcsN k p q).comp (lcsN k p q) = 0 := by
  apply LinearMap.ext
  intro ξ
  rw [LinearMap.comp_apply, lcsN_apply, lcsN_apply]
  simp

/-- The shear `w₁ = 1 + N`, i.e. `(x,y,u,v) ↦ (x, y, u + y • p + ∑ l, v l • q l, v)`. -/
def lcsW1 (k : ℕ) (p : lcsE k) (q : Fin k → lcsE k) : lcsM k →ₗ[ℝ] lcsM k :=
  1 + lcsN k p q

theorem lcsW1_apply (k : ℕ) (p : lcsE k) (q : Fin k → lcsE k) (ξ : lcsM k) :
    lcsW1 k p q ξ = (ξ.1, ξ.2.1,
      ξ.2.2.1 + ξ.2.1 • p + ∑ l, (ξ.2.2.2 l) • q l, ξ.2.2.2) := by
  ext <;> simp [lcsW1, lcsN_apply, add_assoc]

/-- The functional `(u,v) ↦ ∑ l, v l * c l` on the `(u,v)`-block. -/
def lcsCv (k : ℕ) (c : Fin k → ℝ) : (lcsE k × lcsE k) →ₗ[ℝ] ℝ :=
  ∑ l, (lcsVv k l).smulRight (c l)

theorem lcsCv_apply (k : ℕ) (c : Fin k → ℝ) (p : lcsE k × lcsE k) :
    lcsCv k c p = ∑ l, p.2 l * c l := by
  simp [lcsCv, LinearMap.smulRight_apply, smul_eq_mul]

/-- The map `(y,u,v) ↦ (a y + ∑ l, v l * cy l, u, v)`. -/
def lcsG2 (k : ℕ) (a : ℝ) (cy : Fin k → ℝ) :
    (ℝ × (lcsE k × lcsE k)) →ₗ[ℝ] (ℝ × (lcsE k × lcsE k)) :=
  ((LinearMap.mulLeft ℝ a).comp (LinearMap.fst ℝ ℝ (lcsE k × lcsE k)) +
      ((lcsCv k cy).comp (LinearMap.snd ℝ ℝ (lcsE k × lcsE k)))).prod
    ((LinearMap.id : (lcsE k × lcsE k) →ₗ[ℝ] (lcsE k × lcsE k)).comp
      (LinearMap.snd ℝ ℝ (lcsE k × lcsE k)))

theorem lcsG2_apply (k : ℕ) (a : ℝ) (cy : Fin k → ℝ) (ξ : ℝ × (lcsE k × lcsE k)) :
    lcsG2 k a cy ξ = (a * ξ.1 + ∑ l, ξ.2.2 l * cy l, ξ.2) := by
  simp [lcsG2, LinearMap.prod_apply, LinearMap.comp_apply, LinearMap.smulRight_apply,
    lcsCv_apply, LinearMap.mulLeft_apply]

/-- The endomorphism `(x,y,u,v) ↦ (x + ∑ l, v l * cx l, a y + ∑ l, v l * cy l, u, v)` of the
model space. -/
def lcsW2 (k : ℕ) (a : ℝ) (cx cy : Fin k → ℝ) : lcsM k →ₗ[ℝ] lcsM k :=
  (((LinearMap.id : ℝ →ₗ[ℝ] ℝ).comp (LinearMap.fst ℝ ℝ (ℝ × (lcsE k × lcsE k)))) +
      (((lcsCv k cx).comp (LinearMap.snd ℝ ℝ (lcsE k × lcsE k))).comp
        (LinearMap.snd ℝ ℝ (ℝ × (lcsE k × lcsE k))))).prod
    ((lcsG2 k a cy).comp (LinearMap.snd ℝ ℝ (ℝ × (lcsE k × lcsE k))))

theorem lcsW2_apply (k : ℕ) (a : ℝ) (cx cy : Fin k → ℝ) (ξ : lcsM k) :
    lcsW2 k a cx cy ξ = (ξ.1 + ∑ l, ξ.2.2.2 l * cx l,
      a * ξ.2.1 + ∑ l, ξ.2.2.2 l * cy l, ξ.2.2.1, ξ.2.2.2) := by
  ext <;> simp [lcsW2, LinearMap.prod_apply, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.snd_apply, LinearMap.fst_apply, LinearMap.id_apply, lcsG2_apply, lcsCv_apply]

/-- The composite `w₂ ∘ w₁`. -/
def lcsComb (k : ℕ) (a : ℝ) (p : lcsE k) (cx cy : Fin k → ℝ) (q : Fin k → lcsE k) :
    lcsM k →ₗ[ℝ] lcsM k :=
  (lcsW2 k a cx cy).comp (lcsW1 k p q)

theorem lcsComb_apply (k : ℕ) (a : ℝ) (p : lcsE k) (cx cy : Fin k → ℝ)
    (q : Fin k → lcsE k) (ξ : lcsM k) :
    lcsComb k a p cx cy q ξ = (ξ.1 + ∑ l, ξ.2.2.2 l * cx l,
      a * ξ.2.1 + ∑ l, ξ.2.2.2 l * cy l,
      ξ.2.2.1 + ξ.2.1 • p + ∑ l, (ξ.2.2.2 l) • q l, ξ.2.2.2) := by
  rw [lcsComb, LinearMap.comp_apply, lcsW1_apply, lcsW2_apply]

/-- **The general nilpotent determinant**: `1 + N` has determinant one if `N ∘ N = 0`. -/
theorem lcs_det_one_add_of_comp_self_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Module.Finite ℝ V] (N : V →ₗ[ℝ] V) (hN : N.comp N = 0) : LinearMap.det (1 + N) = 1 := by
  have hnil : IsNilpotent N := ⟨2, by rw [sq]; exact hN⟩
  have hcp : (-N).charpoly = (Polynomial.X : Polynomial ℝ) ^ Module.finrank ℝ V :=
    IsNilpotent.charpoly_eq_X_pow_finrank hnil.neg
  have h1 : ((1 : Module.End ℝ V) + N).det = (-N).charpoly.eval 1 := by
    rw [LinearMap.eval_charpoly]
    simp
  rw [h1, hcp]
  simp

theorem lcsW1_det (k : ℕ) (p : lcsE k) (q : Fin k → lcsE k) :
    LinearMap.det (lcsW1 k p q) = 1 := by
  rw [lcsW1]
  exact lcs_det_one_add_of_comp_self_eq_zero (lcsN k p q) (lcsN_comp_self k p q)

theorem lcsW2_det (k : ℕ) (a : ℝ) (cx cy : Fin k → ℝ) :
    LinearMap.det (lcsW2 k a cx cy) = a := by
  rw [lcsW2, det_prod_block, LinearMap.det_id, one_mul]
  rw [lcsG2, det_prod_block, LinearMap.det_mulLeft, LinearMap.det_id, mul_one]

theorem lcsComb_det (k : ℕ) (a : ℝ) (p : lcsE k) (cx cy : Fin k → ℝ) (q : Fin k → lcsE k) :
    LinearMap.det (lcsComb k a p cx cy q) = a := by
  rw [lcsComb, LinearMap.det_comp, lcsW1_det, lcsW2_det, mul_one]

/-! ### Splitting a linear combination along `Fin.append` -/

theorem lcsSum_append {k a b : ℕ} (u : Fin a → lcsM k) (v : Fin b → lcsM k)
    (w : Fin (a + b) → ℝ) :
    lcsSum (Fin.append u v) w
      = lcsSum u (fun i => w (Fin.castAdd b i)) + lcsSum v (fun i => w (Fin.natAdd a i)) := by
  rw [lcsSum_apply, lcsSum_apply, lcsSum_apply, Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [Fin.append_left])
  · exact Finset.sum_congr rfl (fun i _ => by rw [Fin.append_right])

theorem lcsSum_cornerFrame (k : ℕ) (A B : lcsM k) (V : Fin k → lcsM k) (ξ : lcsM k) :
    (∑ i, (lcsT k ξ) i • (Fin.append (Fin.append ![A, B] V) (iotaU k)) i)
      = ξ.1 • A + ξ.2.1 • B + (∑ l, (ξ.2.2.2 l) • V l) + (0, 0, ξ.2.2.1, 0) := by
  rw [Fin.sum_univ_add]
  have h1 : (∑ i : Fin k, (lcsT k ξ) (Fin.natAdd (2 + k) i) •
        (Fin.append (Fin.append ![A, B] V) (iotaU k)) (Fin.natAdd (2 + k) i))
      = (0, 0, ξ.2.2.1, 0) := by
    rw [show (∑ i : Fin k, (lcsT k ξ) (Fin.natAdd (2 + k) i) •
          (Fin.append (Fin.append ![A, B] V) (iotaU k)) (Fin.natAdd (2 + k) i))
        = ∑ i : Fin k, (ξ.2.2.1 i) • iotaU k i from
      Finset.sum_congr rfl (fun i _ => by rw [Fin.append_right, lcsT_u])]
    exact sum_smul_iotaU k ξ.2.2.1
  have h2 : (∑ i : Fin (2 + k), (lcsT k ξ) (Fin.castAdd k i) •
        (Fin.append (Fin.append ![A, B] V) (iotaU k)) (Fin.castAdd k i))
      = ξ.1 • A + ξ.2.1 • B + (∑ l, (ξ.2.2.2 l) • V l) := by
    rw [show (∑ i : Fin (2 + k), (lcsT k ξ) (Fin.castAdd k i) •
          (Fin.append (Fin.append ![A, B] V) (iotaU k)) (Fin.castAdd k i))
        = ∑ i : Fin (2 + k), (lcsT k ξ) (Fin.castAdd k i) •
          (Fin.append ![A, B] V) i from
      Finset.sum_congr rfl (fun i _ => by rw [Fin.append_left])]
    rw [Fin.sum_univ_add]
    have h2a : (∑ i : Fin 2, (lcsT k ξ) (Fin.castAdd k (Fin.castAdd k i)) •
          (Fin.append ![A, B] V) (Fin.castAdd k i)) = ξ.1 • A + ξ.2.1 • B := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.append_left]
      rw [lcsT_x, lcsT_y]
    have h2b : (∑ i : Fin k, (lcsT k ξ) (Fin.castAdd k (Fin.natAdd 2 i)) •
          (Fin.append ![A, B] V) (Fin.natAdd 2 i)) = ∑ l, (ξ.2.2.2 l) • V l := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Fin.append_right, lcsT_v]
    rw [h2a, h2b]
  rw [h2, h1]

theorem lcs_sum_smul_single (k : ℕ) (u : EuclideanSpace ℝ (Fin k)) :
    (∑ i : Fin k, u i • (EuclideanSpace.single i (1 : ℝ))) = u := by
  have h : WithLp.ofLp (∑ i : Fin k, u i • (EuclideanSpace.single i (1 : ℝ)))
      = WithLp.ofLp u := by
    rw [WithLp.ofLp_sum, WithLp.ofLp]
    ext j
    simp [Finset.sum_apply, PiLp.ofLp_single, Pi.single_apply, Finset.sum_ite_eq]
  exact (WithLp.equiv 2 (Fin k → ℝ)).injective h

/-- **The corner determinant**: for a frame `[A, B, V, ιu]` with `A = e_x`, `B` in the plane
`{x = 0, v = 0}` and `V` a `v`-frame, the determinant read in the `(x,y,v,u)`-coordinates is the
`y`-component of `B`. -/
theorem lcs_frameDet_corner (k : ℕ) (A B : lcsM k) (V : Fin k → lcsM k)
    (hA : A = (1, 0, 0, 0)) (hB1 : B.1 = 0) (hBv : B.2.2.2 = 0)
    (hV : ∀ l : Fin k, (V l).2.2.2 = EuclideanSpace.single l 1) :
    frameDet (2 + k + k) (lcsT k) (Fin.append (Fin.append ![A, B] V) (iotaU k)) = B.2.1 := by
  rw [lcs_frameDet_eq]
  have hmap : ((lcsSum (Fin.append (Fin.append ![A, B] V) (iotaU k))).comp
      ((lcsT k).trans (WithLp.linearEquiv 2 ℝ (Fin (2 + k + k) → ℝ))).toLinearMap)
      = lcsComb k (B.2.1) (B.2.2.1) (fun l => (V l).1) (fun l => (V l).2.1)
          (fun l => (V l).2.2.1) := by
    apply LinearMap.ext
    intro ξ
    rw [LinearMap.comp_apply, lcsSum_apply]
    have hstep : (∑ i, (((↑((lcsT k).trans (WithLp.linearEquiv 2 ℝ (Fin (2 + k + k) → ℝ))).toLinearMap :
          lcsM k → (Fin (2 + k + k) → ℝ)) ξ) i) •
          (Fin.append (Fin.append ![A, B] V) (iotaU k)) i)
        = ∑ i, (lcsT k ξ) i • (Fin.append (Fin.append ![A, B] V) (iotaU k)) i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [LinearEquiv.trans_apply, WithLp.linearEquiv]
    have hE : B = (0, B.2.1, B.2.2.1, 0) := by
      ext <;> simp [hB1, hBv]
    have hVexp : ∀ l : Fin k, V l = ((V l).1, (V l).2.1, (V l).2.2.1,
        EuclideanSpace.single l 1) := by
      intro l
      ext <;> simp [hV l]
    rw [hstep, lcsSum_cornerFrame, lcsComb_apply, hA, hE]
    rw [show (∑ l, (ξ.2.2.2 l) • V l)
        = ∑ l, (ξ.2.2.2 l) • ((V l).1, (V l).2.1, (V l).2.2.1,
            EuclideanSpace.single l 1) from
      Finset.sum_congr rfl (fun l _ => by rw [hVexp l])]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    all_goals simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sum,
      Prod.snd_sum, smul_eq_mul, mul_comm, smul_zero, add_zero, zero_add,
      lcs_sum_smul_single]
    all_goals try ring
    all_goals try abel
  rw [hmap, lcsComb_det]

/-! ## §4 The derivative facts at the two corners, and the target -/

/-- **Agreement of a two-sided derivative with a one-sided one.**  If `F` is differentiable at `x`
and `G` has derivative `d` within `s` at `x`, with `F = G` on `𝓝[s] x` and at `x`, and `s` is a
unique-differentiability set at `x`, then `F' x = d`. -/
theorem lcs_deriv_agree {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : ℝ → E} {c d : E} {s : Set ℝ} {x : ℝ}
    (hF : HasDerivAt F c x) (hG : HasDerivWithinAt G d s x)
    (hs : UniqueDiffWithinAt ℝ s x) (h : F =ᶠ[𝓝[s] x] G) (hx : F x = G x) : c = d := by
  have hG' : HasDerivWithinAt F d s x := hG.congr_of_eventuallyEq h hx
  have hEq := hs.eq hF.hasDerivWithinAt.hasFDerivWithinAt hG'.hasFDerivWithinAt
  have h2 := congrArg (fun (f : ℝ →L[ℝ] E) => f 1) hEq
  simpa using h2

theorem lcs_hasDerivAt_arch_one : HasDerivAt arch (-2) 1 := by
  change HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-2) 1
  simpa using ((hasDerivAt_id (1 : ℝ)).pow 2).const_sub 1

theorem lcs_hasDerivAt_arch_neg_one : HasDerivAt arch (2) (-1) := by
  change HasDerivAt (fun t : ℝ => 1 - t ^ 2) (2) (-1)
  simpa using ((hasDerivAt_id (-1 : ℝ)).pow 2).const_sub 1

/-- The `x`-derivative of the disc approximation at the right corner is `e_x`. -/
theorem lcs_xDeriv_one {k : ℕ} (Δ : ℝ × ℝ → lcsM k)
    (hΔ0 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Δ (x, 0) = (x, 0, 0, 0))
    (hd1 : DifferentiableAt ℝ Δ (1, 0)) :
    fderiv ℝ Δ (1, 0) (1, 0) = (1, 0, 0, 0) := by
  have hcurve : HasDerivAt (fun t : ℝ => Δ (t, (0 : ℝ)))
      (fderiv ℝ Δ (1, 0) (1, 0)) 1 := by
    have hd : HasFDerivAt Δ (fderiv ℝ Δ (1, 0)) (1, 0) := hd1.hasFDerivAt
    have hc : HasDerivAt (fun t : ℝ => (t, (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) 1 :=
      (hasDerivAt_id (1 : ℝ)).prodMk (hasDerivAt_const (x := (1 : ℝ)) (0 : ℝ))
    exact hd.comp_hasDerivAt (x := (1 : ℝ)) (f := fun t : ℝ => (t, (0 : ℝ))) hc
  have hbase : HasDerivAt (fun t : ℝ => (((t : ℝ), (0 : ℝ), (0 : lcsE k),
      (0 : lcsE k)) : lcsM k))
      ((1 : ℝ), (0 : ℝ), (0 : lcsE k), (0 : lcsE k)) 1 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℝ)) (1 : ℝ) 1 := hasDerivAt_id 1
    have h2 : HasDerivAt (fun _ : ℝ => (((0 : ℝ), (0 : lcsE k), (0 : lcsE k)) :
        ℝ × (lcsE k × lcsE k))) (0 : ℝ × (lcsE k × lcsE k)) 1 := hasDerivAt_const _ _
    exact h1.prodMk h2
  have heq : (fun t : ℝ => Δ (t, (0 : ℝ))) =ᶠ[𝓝[Set.Iic 1] (1 : ℝ)]
      (fun t : ℝ => (((t : ℝ), (0 : ℝ), (0 : lcsE k), (0 : lcsE k)) : lcsM k)) := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 1 by norm_num)] with t ht
    intro ht0
    exact hΔ0 t ⟨le_of_lt ht, ht0⟩
  exact lcs_deriv_agree hcurve hbase.hasDerivWithinAt (uniqueDiffWithinAt_Iic 1) heq
    (by simpa using hΔ0 1 ⟨by norm_num, by norm_num⟩)

/-- The `x`-derivative of the disc approximation at the left corner is `e_x`. -/
theorem lcs_xDeriv_neg_one {k : ℕ} (Δ : ℝ × ℝ → lcsM k)
    (hΔ0 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Δ (x, 0) = (x, 0, 0, 0))
    (hdm1 : DifferentiableAt ℝ Δ (-1, 0)) :
    fderiv ℝ Δ (-1, 0) (1, 0) = (1, 0, 0, 0) := by
  have hcurve : HasDerivAt (fun t : ℝ => Δ (t, (0 : ℝ)))
      (fderiv ℝ Δ (-1, 0) (1, 0)) (-1) := by
    have hd : HasFDerivAt Δ (fderiv ℝ Δ (-1, 0)) (-1, 0) := hdm1.hasFDerivAt
    have hc : HasDerivAt (fun t : ℝ => (t, (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) (-1) :=
      (hasDerivAt_id (-1 : ℝ)).prodMk (hasDerivAt_const (x := (-1 : ℝ)) (0 : ℝ))
    exact hd.comp_hasDerivAt (x := (-1 : ℝ)) (f := fun t : ℝ => (t, (0 : ℝ))) hc
  have hbase : HasDerivAt (fun t : ℝ => (((t : ℝ), (0 : ℝ), (0 : lcsE k),
      (0 : lcsE k)) : lcsM k))
      ((1 : ℝ), (0 : ℝ), (0 : lcsE k), (0 : lcsE k)) (-1) := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℝ)) (1 : ℝ) (-1) := hasDerivAt_id (-1)
    have h2 : HasDerivAt (fun _ : ℝ => (((0 : ℝ), (0 : lcsE k), (0 : lcsE k)) :
        ℝ × (lcsE k × lcsE k))) (0 : ℝ × (lcsE k × lcsE k)) (-1) := hasDerivAt_const _ _
    exact h1.prodMk h2
  have heq : (fun t : ℝ => Δ (t, (0 : ℝ))) =ᶠ[𝓝[Set.Ici (-1)] (-1 : ℝ)]
      (fun t : ℝ => (((t : ℝ), (0 : ℝ), (0 : lcsE k), (0 : lcsE k)) : lcsM k)) := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (-1 : ℝ) < 1 by norm_num)] with t ht
    intro ht0
    exact hΔ0 t ⟨ht0, le_of_lt ht⟩
  exact lcs_deriv_agree hcurve hbase.hasDerivWithinAt (uniqueDiffWithinAt_Ici (-1)) heq
    (by simpa using hΔ0 (-1) ⟨by norm_num, by norm_num⟩)

/-- The Hadamard relation at the right corner: `∂ₓΔ (1,0) - 2 ∂_yΔ (1,0) = β1`. -/
theorem lcs_hadamard_one {k : ℕ} (Δ : ℝ × ℝ → lcsM k) (B : ℝ → lcsM k) (β1 : lcsM k)
    (hΔ1 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Δ (x, arch x) = B x)
    (hd1 : DifferentiableAt ℝ Δ (1, 0)) (hB1 : HasDerivAt B β1 1) :
    fderiv ℝ Δ (1, 0) (1, -2) = β1 := by
  have harch1 : arch 1 = 0 := by norm_num [arch]
  have hc : HasDerivAt (fun t : ℝ => (t, arch t)) ((1 : ℝ), (-2 : ℝ)) 1 :=
    (hasDerivAt_id (1 : ℝ)).prodMk lcs_hasDerivAt_arch_one
  have hcurve : HasDerivAt (fun t : ℝ => Δ (t, arch t))
      ((fderiv ℝ Δ (1, 0)) ((1 : ℝ), (-2 : ℝ))) 1 := by
    have hd : HasFDerivAt Δ (fderiv ℝ Δ (1, 0)) (1, 0) := hd1.hasFDerivAt
    have hd' : HasFDerivAt Δ (fderiv ℝ Δ (1, arch 1)) (1, arch 1) := by
      rw [harch1]
      exact hd
    have hcomp := hd'.comp_hasDerivAt (x := (1 : ℝ)) (f := fun t : ℝ => (t, arch t)) hc
    rw [harch1] at hcomp
    exact hcomp
  refine lcs_deriv_agree hcurve hB1.hasDerivWithinAt (uniqueDiffWithinAt_Iic 1) ?_ ?_
  · rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 1 by norm_num)] with t ht
    intro ht0
    exact hΔ1 t ⟨le_of_lt ht, ht0⟩
  · simpa [harch1] using hΔ1 1 ⟨by norm_num, by norm_num⟩

/-- The Hadamard relation at the left corner: `∂ₓΔ (-1,0) + 2 ∂_yΔ (-1,0) = βm1`. -/
theorem lcs_hadamard_neg_one {k : ℕ} (Δ : ℝ × ℝ → lcsM k) (B : ℝ → lcsM k) (βm1 : lcsM k)
    (hΔ1 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Δ (x, arch x) = B x)
    (hdm1 : DifferentiableAt ℝ Δ (-1, 0)) (hBm1 : HasDerivAt B βm1 (-1)) :
    fderiv ℝ Δ (-1, 0) (1, 2) = βm1 := by
  have harchm1 : arch (-1) = 0 := by norm_num [arch]
  have hc : HasDerivAt (fun t : ℝ => (t, arch t)) ((1 : ℝ), (2 : ℝ)) (-1) :=
    (hasDerivAt_id (-1 : ℝ)).prodMk lcs_hasDerivAt_arch_neg_one
  have hcurve : HasDerivAt (fun t : ℝ => Δ (t, arch t))
      ((fderiv ℝ Δ (-1, 0)) ((1 : ℝ), (2 : ℝ))) (-1) := by
    have hd : HasFDerivAt Δ (fderiv ℝ Δ (-1, 0)) (-1, 0) := hdm1.hasFDerivAt
    have hd' : HasFDerivAt Δ (fderiv ℝ Δ (-1, arch (-1))) (-1, arch (-1)) := by
      rw [harchm1]
      exact hd
    have hcomp := hd'.comp_hasDerivAt (x := (-1 : ℝ)) (f := fun t : ℝ => (t, arch t)) hc
    rw [harchm1] at hcomp
    exact hcomp
  refine lcs_deriv_agree hcurve hBm1.hasDerivWithinAt (uniqueDiffWithinAt_Ici (-1)) ?_ ?_
  · rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (-1 : ℝ) < 1 by norm_num)] with t ht
    intro ht0
    exact hΔ1 t ⟨ht0, le_of_lt ht⟩
  · simpa [harchm1] using hΔ1 (-1) ⟨by norm_num, by norm_num⟩

/-- The vector form of the Hadamard relation at `x = 1`. -/
theorem lcs_relvec_one {k : ℕ} (Δ : ℝ × ℝ → lcsM k) (β1 : lcsM k)
    (h : fderiv ℝ Δ (1, 0) ((1 : ℝ), (-2 : ℝ)) = β1) :
    fderiv ℝ Δ (1, 0) (1, 0) - (2 : ℝ) • fderiv ℝ Δ (1, 0) (0, 1) = β1 := by
  have h' := h
  rw [show ((1 : ℝ), (-2 : ℝ)) = ((1 : ℝ), (0 : ℝ)) - (2 : ℝ) • ((0 : ℝ), (1 : ℝ))
      from by ext <;> norm_num, map_sub, map_smul] at h'
  simpa using h'

/-- The vector form of the Hadamard relation at `x = -1`. -/
theorem lcs_relvec_neg_one {k : ℕ} (Δ : ℝ × ℝ → lcsM k) (βm1 : lcsM k)
    (h : fderiv ℝ Δ (-1, 0) ((1 : ℝ), (2 : ℝ)) = βm1) :
    fderiv ℝ Δ (-1, 0) (1, 0) + (2 : ℝ) • fderiv ℝ Δ (-1, 0) (0, 1) = βm1 := by
  have h' := h
  rw [show ((1 : ℝ), (2 : ℝ)) = ((1 : ℝ), (0 : ℝ)) + (2 : ℝ) • ((0 : ℝ), (1 : ℝ))
      from by ext <;> norm_num, map_add, map_smul] at h'
  simpa using h'

/-! ## §5 The target -/

/-- **The corner sign of the framing chart** (the lead's `L1`): the product of the two corner
determinants of the frame `[∂ₓΔ, ∂_yΔ, V, ιu]` is **positive**, which is the hypothesis `hsign` of
`Work.Drive.PushDisc.lensFrames` (and hence of `Work.Drive.Whitney.exists_topCompletion`, L2).

This is where the **opposite-sign hypothesis** of the target (`OppositeType`) is spent, through
`Work.Drive.PushDisc.signOfCoreDerivative_of_immersion`: in the flat-tube chart `Φ₀` the *core* of
the finger is `B x = Φ₀ (f (γ₂ (sigR x)))`, its `y`-slope at the two corners has opposite signs,
and (the row `hcorev`) the core lies in the `v = 0` plane, so the same is true of the reduced
corner determinant `E (±1)`; the factor `-1/4` of the two Hadamard corner relations
(`Δ_y (±1,0) = ±(e_x - β) / 2`, which the prover derives by differentiating the top-edge identity
`Δ (x, arch x) = B x` at `x = ±1`) then turns the opposite signs into the positive product.

Concretely, expanding along the `x`-row, the two corner determinants are `∓(1/2) · E (±1)` with
`E (x) = det (β - e_x, V x, ιu)` computed in the hyperplane `{x = 0}`; there the columns `V x j` have
`v`-part `e_j` (row `hVv`) and `β - e_x` has `v`-part `0` (row `hcorev`) and `y`-part `(β).2.1`, so
`E (x) = ± (β).2.1`, and the product is `-(1/4) (β1).2.1 (βm1).2.1 > 0` by `hsgn`. -/
theorem lensCornerSign {k : ℕ}
    (Δ : ℝ × ℝ → Work.Drive.Whitney.Mdl k) (B : ℝ → Work.Drive.Whitney.Mdl k)
    (V : ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (β1 βm1 : Work.Drive.Whitney.Mdl k)
    (hΔ0 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Δ (x, 0) = (x, 0, 0, 0))
    (hΔ1 : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Δ (x, Work.Drive.PushDisc.arch x) = B x)
    (hB1 : HasDerivAt B β1 1) (hBm1 : HasDerivAt B βm1 (-1))
    (hd1 : DifferentiableAt ℝ Δ (1, 0)) (hdm1 : DifferentiableAt ℝ Δ (-1, 0))
    (hBx1 : (β1).1 = 1) (hBxm1 : (βm1).1 = 1)
    (hcorev : (β1).2.2.2 = 0 ∧ (βm1).2.2.2 = 0)
    (hVv : ∀ (x : ℝ) (j : Fin k), (V x j).2.2.2 = EuclideanSpace.single j (1 : ℝ))
    (hsgn : (β1).2.1 * (βm1).2.1 < 0) :
    ∃ T : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 + k + k)),
      0 < Work.Drive.PushDisc.frameDet (2 + k + k) T
            (Work.Drive.PushDisc.cornerFrame (fun p => fderiv ℝ Δ p (1, 0))
              (fun p => fderiv ℝ Δ p (0, 1)) V 1)
        * Work.Drive.PushDisc.frameDet (2 + k + k) T
            (Work.Drive.PushDisc.cornerFrame (fun p => fderiv ℝ Δ p (1, 0))
              (fun p => fderiv ℝ Δ p (0, 1)) V (-1)) := by
  have harch1 : Work.Drive.PushDisc.arch 1 = 0 := by norm_num [Work.Drive.PushDisc.arch]
  have harchm1 : Work.Drive.PushDisc.arch (-1) = 0 := by
    norm_num [Work.Drive.PushDisc.arch]
  have hdx1 : fderiv ℝ Δ (1, 0) (1, 0) = (1, 0, 0, 0) := lcs_xDeriv_one Δ hΔ0 hd1
  have hdxm1 : fderiv ℝ Δ (-1, 0) (1, 0) = (1, 0, 0, 0) := lcs_xDeriv_neg_one Δ hΔ0 hdm1
  have hrel1 : fderiv ℝ Δ (1, 0) (1, 0) - (2 : ℝ) • fderiv ℝ Δ (1, 0) (0, 1) = β1 :=
    lcs_relvec_one Δ β1 (lcs_hadamard_one Δ B β1 hΔ1 hd1 hB1)
  have hrelm1 : fderiv ℝ Δ (-1, 0) (1, 0) + (2 : ℝ) • fderiv ℝ Δ (-1, 0) (0, 1) = βm1 :=
    lcs_relvec_neg_one Δ βm1 (lcs_hadamard_neg_one Δ B βm1 hΔ1 hdm1 hBm1)
  -- component facts at the right corner
  have hdy1 : (fderiv ℝ Δ (1, 0) (0, 1)).2.1 = -(β1).2.1 / 2 := by
    have h := congrArg (fun v : Work.Drive.Whitney.Mdl k => v.2.1) hrel1
    rw [hdx1] at h
    simp [hBx1] at h
    linarith
  have hdyx1 : (fderiv ℝ Δ (1, 0) (0, 1)).1 = 0 := by
    have h := congrArg (fun v : Work.Drive.Whitney.Mdl k => v.1) hrel1
    rw [hdx1] at h
    simp [hBx1] at h
    linarith
  have hdyv1 : (fderiv ℝ Δ (1, 0) (0, 1)).2.2.2 = 0 := by
    have h := congrArg (fun v : Work.Drive.Whitney.Mdl k => v.2.2.2) hrel1
    rw [hdx1] at h
    have h2 : (2 : ℝ) • (fderiv ℝ Δ (1, 0) (0, 1)).2.2.2 = 0 := by
      simpa [hcorev.1, neg_eq_zero] using h
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  -- component facts at the left corner
  have hdym1 : (fderiv ℝ Δ (-1, 0) (0, 1)).2.1 = (βm1).2.1 / 2 := by
    have h := congrArg (fun v : Work.Drive.Whitney.Mdl k => v.2.1) hrelm1
    rw [hdxm1] at h
    simp [hBxm1] at h
    linarith
  have hdyxm1 : (fderiv ℝ Δ (-1, 0) (0, 1)).1 = 0 := by
    have h := congrArg (fun v : Work.Drive.Whitney.Mdl k => v.1) hrelm1
    rw [hdxm1] at h
    simp [hBxm1] at h
    linarith
  have hdyvm1 : (fderiv ℝ Δ (-1, 0) (0, 1)).2.2.2 = 0 := by
    have h := congrArg (fun v : Work.Drive.Whitney.Mdl k => v.2.2.2) hrelm1
    rw [hdxm1] at h
    have h2 : (2 : ℝ) • (fderiv ℝ Δ (-1, 0) (0, 1)).2.2.2 = 0 := by
      simpa [hcorev.2] using h
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  -- the corner determinants
  have hA1 : fderiv ℝ Δ (1, Work.Drive.PushDisc.arch 1) (1, 0) = (1, 0, 0, 0) := by
    rw [harch1]; exact hdx1
  have hB1x : (fderiv ℝ Δ (1, Work.Drive.PushDisc.arch 1) (0, 1)).1 = 0 := by
    rw [harch1]; exact hdyx1
  have hB1v : (fderiv ℝ Δ (1, Work.Drive.PushDisc.arch 1) (0, 1)).2.2.2 = 0 := by
    rw [harch1]; exact hdyv1
  have hA2 : fderiv ℝ Δ (-1, Work.Drive.PushDisc.arch (-1)) (1, 0) = (1, 0, 0, 0) := by
    rw [harchm1]; exact hdxm1
  have hB2x : (fderiv ℝ Δ (-1, Work.Drive.PushDisc.arch (-1)) (0, 1)).1 = 0 := by
    rw [harchm1]; exact hdyxm1
  have hB2v : (fderiv ℝ Δ (-1, Work.Drive.PushDisc.arch (-1)) (0, 1)).2.2.2 = 0 := by
    rw [harchm1]; exact hdyvm1
  have hV1 : ∀ l : Fin k, (V 1 l).2.2.2 = EuclideanSpace.single l 1 := fun l => hVv 1 l
  have hV2 : ∀ l : Fin k, (V (-1) l).2.2.2 = EuclideanSpace.single l 1 := fun l => hVv (-1) l
  have hc1 : frameDet (2 + k + k) (lcsT k)
      (cornerFrame (fun p => fderiv ℝ Δ p (1, 0)) (fun p => fderiv ℝ Δ p (0, 1)) V 1)
      = -(β1).2.1 / 2 := by
    have hfr : cornerFrame (fun p => fderiv ℝ Δ p (1, 0)) (fun p => fderiv ℝ Δ p (0, 1)) V 1
        = Fin.append (Fin.append ![fderiv ℝ Δ (1, Work.Drive.PushDisc.arch 1) (1, 0),
            fderiv ℝ Δ (1, Work.Drive.PushDisc.arch 1) (0, 1)] (V 1)) (iotaU k) := rfl
    rw [hfr, lcs_frameDet_corner k _ _ (V 1) hA1 hB1x hB1v hV1]
    rw [harch1]
    exact hdy1
  have hc2 : frameDet (2 + k + k) (lcsT k)
      (cornerFrame (fun p => fderiv ℝ Δ p (1, 0)) (fun p => fderiv ℝ Δ p (0, 1)) V (-1))
      = (βm1).2.1 / 2 := by
    have hfr : cornerFrame (fun p => fderiv ℝ Δ p (1, 0)) (fun p => fderiv ℝ Δ p (0, 1)) V (-1)
        = Fin.append (Fin.append ![fderiv ℝ Δ (-1, Work.Drive.PushDisc.arch (-1)) (1, 0),
            fderiv ℝ Δ (-1, Work.Drive.PushDisc.arch (-1)) (0, 1)] (V (-1))) (iotaU k) := rfl
    rw [hfr, lcs_frameDet_corner k _ _ (V (-1)) hA2 hB2x hB2v hV2]
    rw [harchm1]
    exact hdym1
  refine ⟨lcsT k, ?_⟩
  rw [hc1, hc2]
  nlinarith [hsgn]

end

end Work.Drive.PushDisc
