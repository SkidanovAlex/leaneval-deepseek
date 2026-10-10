import Mathlib
import Submission.Work.MotK.KleinIdents
import Submission.Work.MotK.KleinData
import Submission.Work.MotK.CensusFibre.kleinM_alt
import Submission.Work.MotK.CensusFibre.det_submatrix_kleinMat_eq_sq
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open Matrix

namespace Work.MotK.CensusFibre

/-! ## Two linear-algebra lemmas -/

/-- **Matrix--vector product against a principal submatrix.**  If `u : Fin 5 → R` vanishes at `k`,
then applying the principal `4 × 4` minor obtained by deleting row and column `k` to the extracted
vector `b ↦ u (k.succAbove b)` is the same as applying `M` and then extracting: the two sides agree
in every coordinate `a : Fin 4`, both being the sum of `M (k.succAbove a) j * u j` over `j ≠ k`. -/
theorem mulVec_submatrix_succAbove_eq {R : Type*} [CommRing R] (M : Matrix (Fin 5) (Fin 5) R)
    (u : Fin 5 → R) (k : Fin 5) (huk : u k = 0) (a : Fin 4) :
    Matrix.mulVec (M.submatrix k.succAbove k.succAbove) (fun b : Fin 4 => u (k.succAbove b)) a
      = Matrix.mulVec M u (k.succAbove a) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  rw [Fin.sum_univ_succAbove (fun j => M (k.succAbove a) j * u j) k]
  simp [huk]

/-- **Two vectors killed by `M` are proportional at `k`.**  If the principal `4 × 4` minor of `M`
deleting `k` is invertible, then the two kernel vectors `v`, `w` have proportional `k`-th
coordinates: `w k • v = v k • w`.

This is the rank argument in coordinate form: `u := w k • v - v k • w` is again killed by `M` and
vanishes at `k`, so the extracted vector `b ↦ u (k.succAbove b)` is killed by the invertible minor
`M.submatrix k.succAbove k.succAbove`, hence is `0`; as `u` also vanishes at `k`, `u = 0`. -/
theorem smul_eq_smul_of_mulVec_eq_zero {K : Type} [Field K] {M : Matrix (Fin 5) (Fin 5) K}
    {v w : Fin 5 → K} (hw : Matrix.mulVec M w = 0) (hv : Matrix.mulVec M v = 0) {k : Fin 5}
    (hdet : (M.submatrix k.succAbove k.succAbove).det ≠ 0) : w k • v = v k • w := by
  set u : Fin 5 → K := w k • v - v k • w with hu
  have hMu : Matrix.mulVec M u = 0 := by
    simp only [hu, Matrix.mulVec_sub, Matrix.mulVec_smul, hw, hv, smul_zero, sub_self]
  have huk : u k = 0 := by
    simp only [hu, Pi.sub_apply, Pi.smul_apply]
    first | refl_ring1 | ring
  have hN : Matrix.mulVec (M.submatrix k.succAbove k.succAbove)
      (fun b : Fin 4 => u (k.succAbove b)) = 0 := by
    funext a
    rw [mulVec_submatrix_succAbove_eq M u k huk a]
    exact congrFun hMu (k.succAbove a)
  have hu0 : (fun b : Fin 4 => u (k.succAbove b)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hN
  have hz : u = 0 := by
    funext j
    by_cases hj : j = k
    · subst hj
      exact huk
    · obtain ⟨b, hb⟩ := (Fin.exists_succAbove_eq_iff (x := k) (y := j)).mpr hj
      rw [← hb]
      simpa using congrFun hu0 b
  rw [hu] at hz
  exact sub_eq_zero.mp hz

/-- **The fibres of the Pfaffian (quadro) map are the linear spaces `{x : M(x)·c' = 0}`.**

`kleinM a b x` is the skew `5 × 5` matrix `M_{i j} = c_{j - i} x_{i + j}` whose vector of `4 × 4`
Pfaffians is `kleinP a b x`, and `kleinM_mul_kleinP` (`Submission.Work.MotK.KleinIdents`) says
`M(x) · p(x) = 0`.

For `c' ≠ 0` and `x` with `p(x) ≠ 0` (i.e. `x` not on the Klein curve `C = V(p)`), the following are
equivalent:

* `x` lies in the fibre of the quadro map `P = kleinP a b` over `c'` (i.e. `p(x)` is proportional
  to `c'`);
* `c'` lies in the kernel of the linear map `v ↦ M(x)·v`, equivalently `M(x)·c' = 0`.

The proof is the classical rank argument: `p(x) ≠ 0` means that some `4 × 4` Pfaffian of `M(x)` is
nonzero, hence — using `p_k² = det (k-th principal 4 × 4 minor)` — that `rank M(x) ≥ 4`; and
`M(x)·p(x) = 0` with `p(x) ≠ 0` rules out `rank = 5`, so `rank M(x) = 4` and `ker M(x)` is one
dimensional, contains `p(x) ≠ 0`, hence equals `span {p(x)}`.

Consequently the fibre of `P` over `c'` is the **linear** set `{x : M(x)·c' = 0}` minus the base
locus `C` — this is the explicit ruling of the exceptional divisor of the Crauder–Katz link on the
`F`-side, and it is what the census `K4`/`K5` of `Submission/Work/MotK` needs
(`{s = 0} = P⁻¹(C')` is ruled over `C'` by these linear spaces, cf. `GUIDE_K5K6.md`). -/
theorem kleinFibre_eq_ker (K : Type) [Field K] (a b : K) (x c' : Fin 5 → K) (hc' : c' ≠ 0)
    (hx : Work.MotK.kleinP a b x ≠ 0) :
    (∀ i, ∑ j, Work.MotK.kleinM a b x i j * c' j = 0) ↔
      ∃ l : K, l ≠ 0 ∧ ∀ i, Work.MotK.kleinP a b x i = l * c' i := by
  constructor
  · -- **Sufficiency of the linear condition.**  `x` not on the Klein curve means that some Pfaffian
    -- `p k` is nonzero; the corresponding principal `4 × 4` minor of `M(x)` has determinant
    -- `p k ^ 2 ≠ 0`, so the kernel of `M(x)` is one-dimensional.  Both `p` and `c'` lie in it, and
    -- `c' ≠ 0`, so they are proportional.
    intro hM
    obtain ⟨k, hk⟩ := Work.MotK.exists_kleinP_ne_zero a b x hx
    have hdet : ((Work.MotK.kleinMat a b x).submatrix k.succAbove k.succAbove).det ≠ 0 := by
      rw [det_submatrix_kleinMat_eq_sq a b x k]
      exact pow_ne_zero 2 hk
    have hv : Matrix.mulVec (Work.MotK.kleinMat a b x) c' = 0 := by
      funext i
      show ∑ j, Work.MotK.kleinM a b x i j * c' j = 0
      exact hM i
    have hw : Matrix.mulVec (Work.MotK.kleinMat a b x) (Work.MotK.kleinP a b x) = 0 :=
      Work.MotK.kleinMat_mulVec_kleinP a b x
    have hprop : Work.MotK.kleinP a b x k • c' = c' k • Work.MotK.kleinP a b x :=
      smul_eq_smul_of_mulVec_eq_zero hw hv hdet
    have hck : c' k ≠ 0 := by
      intro h0
      have h1 : Work.MotK.kleinP a b x k • c' = 0 := by rw [hprop, h0, zero_smul]
      exact hc' ((smul_eq_zero.mp h1).resolve_left hk)
    refine ⟨(c' k)⁻¹ * Work.MotK.kleinP a b x k, mul_ne_zero (inv_ne_zero hck) hk, fun i => ?_⟩
    have hp : Work.MotK.kleinP a b x = ((c' k)⁻¹ * Work.MotK.kleinP a b x k) • c' := by
      have h2 := congrArg (fun w : Fin 5 → K => (c' k)⁻¹ • w) hprop.symm
      simpa [smul_smul, inv_smul_smul₀ hck] using h2
    simpa using congrFun hp i
  · -- **Necessity.**  If `p(x) = l · c'` with `l ≠ 0`, then `M(x)·c' = l⁻¹ · M(x)·p(x) = 0`.
    rintro ⟨l, hl, hl'⟩ i
    have h1 : (∑ j, Work.MotK.kleinM a b x i j * (l * c' j)) = 0 := by
      have hgen : (∑ j, Work.MotK.kleinM a b x i j * (l * c' j)) =
          ∑ j, Work.MotK.kleinM a b x i j * Work.MotK.kleinP a b x j :=
        Finset.sum_congr rfl fun j _ => by rw [hl' j]
      rw [hgen, Work.MotK.kleinM_mul_kleinP a b x i]
    have h2 : l * (∑ j, Work.MotK.kleinM a b x i j * c' j) = 0 := by
      rw [Finset.mul_sum]
      exact (Finset.sum_congr rfl fun j _ => by ring).trans h1
    exact (mul_eq_zero.mp h2).resolve_left hl

end Work.MotK.CensusFibre
