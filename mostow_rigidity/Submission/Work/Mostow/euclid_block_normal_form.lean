import Mathlib
import Submission.Work.Mostow.euclidBlockDefs
import Submission.Work.Mostow.vblk_add_smul

/-!
# Euclidean block normal form

Every linear isometry `A` of `E n = EuclideanSpace ℝ (Fin n)` is conjugate, by a linear isometry
`P`, to the map `vblk k hk R` which is the identity on the first `k` coordinates and applies a
fixed-point-free linear isometry `R` of `E (n-k)` to the last `n-k` coordinates.

Here `k` is the dimension of the fixed space `V = ker (A - 1)` of `A`, and the proof uses an
orthonormal basis of `E n` whose first `k` vectors form an orthonormal basis of `V` and whose last
`n - k` vectors form one of `Vᗮ` (`Work.Mostow.adaptedBasis`).
-/

namespace Work.Mostow

open Submission.Mostow

noncomputable section

theorem euclid_block_normal_form (n : ℕ) (A : Submission.Mostow.E n ≃ₗᵢ[ℝ] Submission.Mostow.E n) :
    ∃ (k : ℕ) (hk : k ≤ n) (R : Submission.Mostow.E (n - k) ≃ₗᵢ[ℝ] Submission.Mostow.E (n - k))
      (P : Submission.Mostow.E n ≃ₗᵢ[ℝ] Submission.Mostow.E n),
      (∀ w, R w = w → w = 0) ∧ ∀ u : Submission.Mostow.E n,
        P (A (P.symm u)) = Work.Mostow.vblk k hk R u := by
  classical
  -- the fixed space of `A`
  let V : Submodule ℝ (E n) := LinearMap.eqLocus (A : E n →ₗ[ℝ] E n) 1
  have hVmem : ∀ x : E n, x ∈ V ↔ A x = x := by
    intro x
    show x ∈ LinearMap.eqLocus (A : E n →ₗ[ℝ] E n) 1 ↔ A x = x
    exact LinearMap.mem_eqLocus
  have hVfix : ∀ x ∈ V, A x = x := fun x hx => (hVmem x).mp hx
  -- `A` and `A⁻¹` preserve the orthogonal complement of `V`
  have hWinv : ∀ x ∈ Vᗮ, A x ∈ Vᗮ := by
    intro x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro u hu
    have hAu : A u = u := hVfix u hu
    have h2 : inner ℝ u (A x) = inner ℝ (A u) (A x) := by rw [hAu]
    rw [h2, LinearIsometryEquiv.inner_map_map]
    exact hx u hu
  have hWsinv : ∀ x ∈ Vᗮ, A.symm x ∈ Vᗮ := by
    intro x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro u hu
    have hAu : A u = u := hVfix u hu
    have h2 : inner ℝ u (A.symm x) = inner ℝ (A u) x := by
      have h := LinearIsometryEquiv.inner_map_map A u (A.symm x)
      simpa using h.symm
    rw [h2, hAu]
    exact hx u hu
  -- the dimension of the fixed space
  let k : ℕ := Module.finrank ℝ V
  have hk : k ≤ n := by
    show Module.finrank ℝ V ≤ n
    have h := Submodule.finrank_le V
    rw [finrank_euclideanSpace] at h
    simpa using h
  have hdim : Module.finrank ℝ Vᗮ = n - k := by
    have hVWs := Submodule.finrank_add_finrank_orthogonal V
    rw [finrank_euclideanSpace, Fintype.card_fin] at hVWs
    show Module.finrank ℝ Vᗮ = n - Module.finrank ℝ V
    omega
  -- the adapted orthonormal basis of `E n`
  let bV : OrthonormalBasis (Fin k) ℝ V := stdOrthonormalBasis ℝ V
  let bW : OrthonormalBasis (Fin (n - k)) ℝ Vᗮ :=
    (stdOrthonormalBasis ℝ Vᗮ).reindex (finCongr hdim)
  let b : OrthonormalBasis (Fin n) ℝ (E n) := adaptedBasis k hk V bV bW
  -- the restriction of `A` to `Vᗮ`
  let Awlin : Vᗮ →ₗ[ℝ] Vᗮ :=
    { toFun := fun x => ⟨A x, hWinv x x.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun c x => Subtype.ext (by simp) }
  have hAwlin_inner : ∀ x y : Vᗮ, inner ℝ (Awlin x) (Awlin y) = inner ℝ x y := by
    intro x y
    rw [Submodule.coe_inner, Submodule.coe_inner]
    exact LinearIsometryEquiv.inner_map_map A x y
  have hAwlin_coe : ∀ x : Vᗮ, ((Awlin x : Vᗮ) : E n) = A x := fun x => rfl
  let Awli : Vᗮ →ₗᵢ[ℝ] Vᗮ := Awlin.isometryOfInner hAwlin_inner
  let Awinv : Vᗮ →ₗ[ℝ] Vᗮ :=
    { toFun := fun x => ⟨A.symm x, hWsinv x x.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun c x => Subtype.ext (by simp) }
  have hAwli_coe : ∀ x : Vᗮ, ((Awli x : Vᗮ) : E n) = A x := fun x => hAwlin_coe x
  have hAwsurj : Function.Surjective (Awli : Vᗮ → Vᗮ) := by
    intro y
    refine ⟨Awinv y, ?_⟩
    apply Subtype.ext
    show (A (A.symm (y : E n)) : E n) = (y : E n)
    simp
  set Aw : Vᗮ ≃ₗᵢ[ℝ] Vᗮ := LinearIsometryEquiv.ofSurjective Awli hAwsurj with hAwdef
  have hAw : ∀ x : Vᗮ, (Aw x : E n) = A x := by
    intro x
    rw [hAwdef]
    exact hAwli_coe x
  -- the normal block
  let R : E (n - k) ≃ₗᵢ[ℝ] E (n - k) := (bW.repr.symm).trans (Aw.trans bW.repr)
  refine ⟨k, hk, R, b.repr, ?_, ?_⟩
  · -- `R` has no nonzero fixed vector
    intro w hw
    have hRw : R w = bW.repr (Aw (bW.repr.symm w)) := by
      show (bW.repr.symm).trans (Aw.trans bW.repr) w = _
      rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply]
    have hx : Aw (bW.repr.symm w) = bW.repr.symm w := by
      apply bW.repr.injective
      rw [← hRw, hw, LinearIsometryEquiv.apply_symm_apply]
    have hxV : ((bW.repr.symm w : Vᗮ) : E n) ∈ V := by
      rw [hVmem]
      rw [← hAw (bW.repr.symm w), hx]
    have hzero : inner ℝ ((bW.repr.symm w : Vᗮ) : E n) (((bW.repr.symm w : Vᗮ) : E n)) = 0 :=
      Submodule.inner_right_of_mem_orthogonal hxV (bW.repr.symm w).2
    have hx0 : ((bW.repr.symm w : Vᗮ) : E n) = 0 := inner_self_eq_zero.mp hzero
    have hx0' : (bW.repr.symm w : Vᗮ) = 0 := Subtype.ext hx0
    calc w = bW.repr (bW.repr.symm w) := (LinearIsometryEquiv.apply_symm_apply bW.repr w).symm
      _ = bW.repr 0 := by rw [hx0']
      _ = 0 := map_zero bW.repr
  · -- the block form
    intro u
    let B : E n →ₗ[ℝ] E n :=
      (b.repr : E n →ₗ[ℝ] E n).comp ((A : E n →ₗ[ℝ] E n).comp (b.repr.symm : E n →ₗ[ℝ] E n))
    let L : E n →ₗ[ℝ] E n :=
      { toFun := vblk k hk R
        map_add' := vblk_add k hk R
        map_smul' := vblk_smul k hk R }
    have hBL : B = L := by
      apply Module.Basis.ext (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      intro i
      simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      show b.repr (A (b.repr.symm (EuclideanSpace.single i (1 : ℝ))))
          = vblk k hk R (EuclideanSpace.single i (1 : ℝ))
      rw [OrthonormalBasis.repr_symm_single b i]
      by_cases hi : (i : ℕ) < k
      · -- the fixed block
        have hbi : b i = ((bV ⟨i.val, hi⟩ : V) : E n) := adaptedBasis_apply_left k hk V bV bW i hi
        have hAi : A (b i) = b i := by
          rw [hbi]
          exact hVfix _ (bV ⟨i.val, hi⟩).2
        rw [hAi, OrthonormalBasis.repr_self]
        apply WithLp.ofLp_injective
        funext j
        by_cases hj : (j : ℕ) < k
        · rw [vblk_ofLp_of_lt k hk R _ j hj]
        · have hne : ¬ (j = i) := by
            intro hji
            have h2 : j.val = i.val := congrArg Fin.val hji
            omega
          rw [vblk_ofLp_of_ge k hk R _ j hj, tailOf_single_of_lt k i hi, map_zero,
            PiLp.single_apply, PiLp.zero_apply, if_neg hne]
      · -- the normal block
        have hbi : b i = ((bW ⟨i.val - k, by have := i.isLt; omega⟩ : Vᗮ) : E n) :=
          adaptedBasis_apply_right k hk V bV bW i hi
        rw [hbi, ← hAw (bW ⟨i.val - k, by have := i.isLt; omega⟩)]
        apply WithLp.ofLp_injective
        funext j
        rw [OrthonormalBasis.repr_apply_apply]
        by_cases hj : (j : ℕ) < k
        · have hbj : b j = ((bV ⟨j.val, hj⟩ : V) : E n) := adaptedBasis_apply_left k hk V bV bW j hj
          have hne : ¬ (j = i) := by
            intro hji
            have h2 : j.val = i.val := congrArg Fin.val hji
            omega
          rw [vblk_ofLp_of_lt k hk R _ j hj, PiLp.single_apply, if_neg hne, hbj]
          exact Submodule.inner_right_of_mem_orthogonal (bV ⟨j.val, hj⟩).2
            (Aw (bW ⟨i.val - k, by have := i.isLt; omega⟩)).2
        · have hbj : b j = ((bW ⟨j.val - k, by have := j.isLt; omega⟩ : Vᗮ) : E n) :=
            adaptedBasis_apply_right k hk V bV bW j hj
          have hRc : R (EuclideanSpace.single ⟨i.val - k, by have := i.isLt; omega⟩ (1 : ℝ))
              = bW.repr (Aw (bW ⟨i.val - k, by have := i.isLt; omega⟩)) := by
            show (bW.repr.symm).trans (Aw.trans bW.repr) _ = _
            rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply,
              OrthonormalBasis.repr_symm_single]
          rw [vblk_ofLp_of_ge k hk R _ j hj, tailOf_single_of_ge k i hi, hRc, hbj,
            ← Submodule.coe_inner, ← OrthonormalBasis.repr_apply_apply]
    calc b.repr (A (b.repr.symm u)) = B u := rfl
      _ = L u := by rw [hBL]
      _ = vblk k hk R u := rfl

end

end Work.Mostow
