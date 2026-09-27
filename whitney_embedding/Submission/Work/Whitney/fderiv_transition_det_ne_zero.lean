import Mathlib

/-!
# The derivative of a chart transition is invertible

Let `M` be a smooth `n`-manifold modelled on `E = EuclideanSpace ℝ (Fin n)`, and let
`c, c' : OpenPartialHomeomorph M E` be two charts whose two directions are smooth (i.e. `c` and
`c.symm`, resp. `c'` and `c'.symm`, are `C^∞` as maps between `M` and `E` on their sources and
targets).  Then for every `p` in both sources the *transition map*

  `u ↦ c (c'.symm u)`

is smooth near `c' p` (composition of the smooth maps `c'.symm` and `c`), and it has a local
inverse there, namely `u ↦ c' (c.symm u)`.  Consequently its Fréchet derivative at `c' p` is
invertible, hence has non-zero determinant.

The proof is the algebraic consequence of the chain rule: with
`F = c ∘ c'.symm`, `G = c' ∘ c.symm` one has `F ∘ G =ᶠ[𝓝 (c p)] id`, whence

  `(fderiv ℝ F (c' p)).comp (fderiv ℝ G (c p)) = 1`,

and taking determinants gives `(fderiv ℝ F (c' p)).det * (fderiv ℝ G (c p)).det = 1`.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- The determinant of a composite of continuous linear endomorphisms is the product of the
determinants.  (Mathlib only records the corresponding statement for `LinearMap`.) -/
theorem clm_det_comp {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] (f g : M →L[R] M) : (f.comp g).det = f.det * g.det := by
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]

/-- The determinant of the identity continuous linear endomorphism is `1`. -/
theorem clm_det_one {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] : (1 : M →L[R] M).det = 1 := by
  simp only [ContinuousLinearMap.det]
  exact LinearMap.det_id

theorem fderiv_transition_det_ne_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (c c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (p : M) (hp : p ∈ c.source) (hpd : p ∈ c'.source)
    (hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hcsymm : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u)
    (hc'sm : ∀ y : M, y ∈ c'.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c' y)
    (hc'symm : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c'.target →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c'.symm u) :
    (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => c (c'.symm u)) (c' p)).det ≠ 0 := by
  -- The transition map `F = c ∘ c'.symm` and its formal inverse `G = c' ∘ c.symm`.
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun u => c (c'.symm u)
  let G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun u => c' (c.symm u)
  have hp't : c' p ∈ c'.target := c'.map_source hpd
  have hcpt : c p ∈ c.target := c.map_source hp
  have hsymm_cp' : c'.symm (c' p) = p := c'.left_inv hpd
  have hsymm_cp : c.symm (c p) = p := c.left_inv hp
  -- `F` is smooth at `c' p`: compose `c` (smooth at `p`) with `c'.symm` (smooth at `c' p`).
  have hF : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) F (c' p) := by
    have h2 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c (c'.symm (c' p)) :=
      hcsm (c'.symm (c' p)) (by rw [hsymm_cp']; exact hp)
    have h1 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c'.symm (c' p) :=
      hc'symm (c' p) hp't
    exact h2.comp (c' p) h1
  -- `G` is smooth at `c p`: compose `c'` (smooth at `p`) with `c.symm` (smooth at `c p`).
  have hG : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) G (c p) := by
    have h2 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c' (c.symm (c p)) :=
      hc'sm (c.symm (c p)) (by rw [hsymm_cp]; exact hpd)
    have h1 : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c p) :=
      hcsymm (c p) hcpt
    exact h2.comp (c p) h1
  have hFdiff : DifferentiableAt ℝ F (c' p) :=
    (contMDiffAt_iff_contDiffAt.mp hF).differentiableAt (by simp)
  have hGdiff : DifferentiableAt ℝ G (c p) :=
    (contMDiffAt_iff_contDiffAt.mp hG).differentiableAt (by simp)
  have hGcp : G (c p) = c' p := by simp [G, hsymm_cp]
  -- `F ∘ G` agrees with the identity on a neighbourhood of `c p`.
  have hev : (F ∘ G) =ᶠ[𝓝 (c p)] id := by
    have hcont : ContinuousAt c.symm (c p) := (hcsymm (c p) hcpt).continuousAt
    have hsrc : ∀ᶠ u in 𝓝 (c p), c.symm u ∈ c'.source := by
      have hmem : c'.source ∈ 𝓝 (c.symm (c p)) := by
        rw [hsymm_cp]; exact c'.open_source.mem_nhds hpd
      exact hcont.eventually hmem
    filter_upwards [hsrc, c.open_target.mem_nhds hcpt] with u hsrc' htgt
    simp only [Function.comp_apply, id_eq, F, G]
    rw [c'.left_inv hsrc', c.right_inv htgt]
  -- Chain rule for `F ∘ G` at `c p`.
  have hcr : fderiv ℝ (F ∘ G) (c p) = (fderiv ℝ F (G (c p))).comp (fderiv ℝ G (c p)) :=
    fderiv_comp (𝕜 := ℝ) (f := G) (g := F) (c p) (by rw [hGcp]; exact hFdiff) hGdiff
  -- Hence the two derivatives are mutually inverse.
  have hcomp : (fderiv ℝ F (c' p)).comp (fderiv ℝ G (c p)) = 1 := by
    have e1 : fderiv ℝ (F ∘ G) (c p) =
        fderiv ℝ (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (c p) :=
      Filter.EventuallyEq.fderiv_eq hev
    rw [hGcp] at hcr
    rw [← hcr, e1, fderiv_id]
    rfl
  -- Taking determinants gives `det F' * det G' = 1`, so `det F' ≠ 0`.
  have hkey : (fderiv ℝ F (c' p)).det * (fderiv ℝ G (c p)).det = 1 := by
    have h1 := congrArg ContinuousLinearMap.det hcomp
    rw [clm_det_comp, clm_det_one] at h1
    exact h1
  have hdet_ne : (fderiv ℝ F (c' p)).det ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hkey
    exact zero_ne_one hkey
  exact hdet_ne

end Work.Whitney
