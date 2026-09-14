import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent

open Matrix
open scoped exteriorPower

namespace Commons.LinearAlgebra.Plucker

variable {K : Type*} [Field K]

open Module in
lemma repr_exteriorPower_ιMulti {M : Type*} [AddCommGroup M] [Module K M]
    {ι : Type*} [LinearOrder ι] (b : Module.Basis ι K M) {n : ℕ}
    (s : Set.powersetCard ι n) (v : Fin n → M) :
    ((Module.Basis.exteriorPower n b).repr (exteriorPower.ιMulti K n v)) s
      = (Matrix.of fun i j => b.coord ((Set.powersetCard.ofFinEmbEquiv.symm s) j) (v i)).det := by
  rw [← Basis.coord_apply, exteriorPower.basis_coord, exteriorPower.ιMultiDual_apply_ιMulti]

lemma iMulti_iota_mul_eq_zero_iff_mem_span {M : Type*} [AddCommGroup M] [Module K M]
    {k : ℕ} (u : Fin k → M) (hu : LinearIndependent K u) (x : M) :
    ExteriorAlgebra.ι K x * ExteriorAlgebra.ιMulti K k u = 0 ↔
      x ∈ Submodule.span K (Set.range u) := by
  constructor
  · intro h0
    by_contra hx
    have hli : LinearIndependent K (Fin.cons x u) :=
      (linearIndependent_finCons).mpr ⟨hu, hx⟩
    have hne :=
      Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent (K := K)
        (v := Fin.cons x u) hli
    apply hne
    apply Subtype.ext
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
    simp only [Fin.cons_zero, Matrix.vecTail]
    exact h0
  · intro hx
    let g : M →ₗ[K] ExteriorAlgebra K M :=
      (LinearMap.mulRight K (ExteriorAlgebra.ιMulti K k u)).comp (ExteriorAlgebra.ι K)
    have hle : Submodule.span K (Set.range u) ≤ LinearMap.ker g := by
      rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      change g (u i) = 0
      have hg : g (u i) = (ExteriorAlgebra.ι K (u i)) * ExteriorAlgebra.ιMulti K k u := by
        simp only [g, LinearMap.comp_apply, LinearMap.mulRight_apply]
      rw [hg]
      have hkey : ExteriorAlgebra.ιMulti K (k+1) (Fin.cons (u i) u) =
          (ExteriorAlgebra.ι K (u i)) * ExteriorAlgebra.ιMulti K k u := by
        rw [ExteriorAlgebra.ιMulti_succ_apply]
        simp [Matrix.vecTail, Function.comp_def, Fin.cons_succ]
      rw [← hkey]
      apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
      intro hinj
      have h1 : (Fin.cons (u i) u : Fin (k+1) → M) 0 =
          (Fin.cons (u i) u : Fin (k+1) → M) i.succ := by
        simp only [Fin.cons_zero, Fin.cons_succ]
      exact (Fin.succ_ne_zero i) ((hinj h1).symm)
    exact (LinearMap.mem_ker.mp (hle hx))

lemma span_le_of_iMulti_eq_smul {M : Type*} [AddCommGroup M] [Module K M] {k : ℕ}
    (u u' : Fin k → M) (hu : LinearIndependent K u) (hu' : LinearIndependent K u')
    {c : K} (hc : c ≠ 0)
    (h : ExteriorAlgebra.ιMulti K k u = c • ExteriorAlgebra.ιMulti K k u') :
    Submodule.span K (Set.range u) ≤ Submodule.span K (Set.range u') := by
  rw [Submodule.span_le]
  rintro x ⟨i, rfl⟩
  have hx : u i ∈ Submodule.span K (Set.range u) := Submodule.subset_span ⟨i, rfl⟩
  have h1 : ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ιMulti K k u = 0 :=
    (iMulti_iota_mul_eq_zero_iff_mem_span u hu (u i)).mpr hx
  rw [h, mul_smul_comm] at h1
  have h2 : ExteriorAlgebra.ι K (u i) * ExteriorAlgebra.ιMulti K k u' = 0 := by
    rcases (smul_eq_zero.mp h1) with hc0 | hz
    · exact absurd hc0 hc
    · exact hz
  exact (iMulti_iota_mul_eq_zero_iff_mem_span u' hu' (u i)).mp h2

/-- **The Plücker embedding is injective (injective up to scaling).**  If the `k × k` minors of
two `k × N` matrices `V`, `V'` with linearly independent rows are proportional (with the same
non-zero factor `c`, for every injective choice of `k` column indices), then the two matrices
have the same row span.  Equivalently: a `k`-dimensional subspace of `K^N` is determined by its
vector of Plücker coordinates. -/
theorem eq_span_of_minors_proportional {K : Type*} [Field K] {k N : ℕ}
    (V V' : Matrix (Fin k) (Fin N) K) (c : K) (hc : c ≠ 0)
    (hV : LinearIndependent K (fun i => V i)) (hV' : LinearIndependent K (fun i => V' i))
    (h : ∀ t : Fin k → Fin N, Function.Injective t →
      (V.submatrix id t).det = c * (V'.submatrix id t).det) :
    Submodule.span K (Set.range (fun i : Fin k => V i)) =
      Submodule.span K (Set.range (fun i : Fin k => V' i)) := by
  let b : Module.Basis (Fin N) K (Fin N → K) := Pi.basisFun K (Fin N)
  let B : Module.Basis (↑(Set.powersetCard (Fin N) k)) K (↥(⋀[K]^k (Fin N → K))) :=
    Module.Basis.exteriorPower k b
  have hcoeff : exteriorPower.ιMulti K k (fun i : Fin k => V i) =
      c • exteriorPower.ιMulti K k (fun i : Fin k => V' i) := by
    apply B.ext_elem_iff.mpr
    intro s
    set e := Set.powersetCard.ofFinEmbEquiv.symm s with he
    have he_inj : Function.Injective (fun j : Fin k => e j) := fun a b hab => e.injective hab
    have hL : (B.repr (exteriorPower.ιMulti K k (fun i : Fin k => V i))) s
        = (V.submatrix id (fun j => e j)).det := by
      rw [repr_exteriorPower_ιMulti]
      congr 1
    have hR : (B.repr (c • exteriorPower.ιMulti K k (fun i : Fin k => V' i))) s
        = c * (V'.submatrix id (fun j => e j)).det := by
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      congr 1
      rw [repr_exteriorPower_ιMulti]
      congr 1
    rw [hL, hR]
    exact h (fun j => e j) he_inj
  have heq : ExteriorAlgebra.ιMulti K k (fun i : Fin k => V i) =
      c • ExteriorAlgebra.ιMulti K k (fun i : Fin k => V' i) := by
    simpa only [exteriorPower.ιMulti_apply_coe, Submodule.coe_smul] using
      congrArg (fun z : ↥(⋀[K]^k (Fin N → K)) => (z : ExteriorAlgebra K (Fin N → K))) hcoeff
  refine le_antisymm ?_ ?_
  · exact span_le_of_iMulti_eq_smul (fun i : Fin k => V i) (fun i : Fin k => V' i) hV hV' hc heq
  · have heq' : ExteriorAlgebra.ιMulti K k (fun i : Fin k => V' i) =
        c⁻¹ • ExteriorAlgebra.ιMulti K k (fun i : Fin k => V i) := by
      rw [heq, smul_smul, inv_mul_cancel₀ hc, one_smul]
    exact span_le_of_iMulti_eq_smul (fun i : Fin k => V' i) (fun i : Fin k => V i) hV' hV
      (inv_ne_zero hc) heq'

end Commons.LinearAlgebra.Plucker