import Mathlib
import Submission.VoronoiMeasure
import Submission.Cvp
import Submission.EpsVoronoi

open Module Real MeasureTheory Measure
open Submission.EpsVoronoi
open scoped BigOperators Pointwise Topology
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# [F-interior] `thm:same_grad_VL` — gradients over lattices and over positions of the cell

For a continuously differentiable `f : ℝ≥0 → ℝ` and lattice `ℒ`, the two functionals
(`A` a nonsingular matrix)

`g(A) := 1/|det A| · ∫_{V(A·ℒ)} f(‖x‖²) dx`   (cell side) and
`h(A) := 1/|det A| · ∫_{A·V(ℒ)} f(‖x‖²) dx`   (smooth side)

have equal gradients at `A = I`:  `∇g(I) = ∇h(I) = 2∫_{V(ℒ)} f'(‖x‖²) x xᵀ dx`
(paper `thm:same_grad_VL`, §3).  This is the bridge that lets the interior branch of
`gamma_stable_of_two_le` compute the derivative of the *cell* functional
`A ↦ γ_{1/t}(V(A·ℒ))` (which a local min over the determinant-one manifold forces to
vanish along trace-zero tangents) by the explicitly computable *smooth* derivative
(ShapeDeriv S1/S3/D1 + S2 ⇒ isotropy of `V(ℒ)` in Gaussian position).

## Why the straightforward two-cell comparison is NOT enough (design warning)

One might try to show `h` and `g` have equal derivatives from the `clm:eps_voronoi`
two-sided inclusions `(1±νε)·V ⊆ {V(A·ℒ), A·V} ⊆ (1+νε)·V`
(`EpsVoronoi.voronoiImage_sandwich`), which give
`|∫_{V(Aℒ)}f − ∫_{A·V} f| = O(‖M‖)`.  That bound is only C⁰: for the *derivative*
comparison one needs `|det(I+M)|·|h−g| = o(‖M‖)` (paper proves `≤ C‖M‖²`), because the
two functionals' difference quotients along a curve `A(t)` must tend to the same limit.

**Follow the paper's route instead**: writing `Λ := A·ℒ`,

1. On the cell, the distance to the lattice is the norm: `x ∈ V(Λ) ⟹ dist(x,Λ) = ‖x‖`
   (this file: `infDist_lattice_eq_norm_on_cell`), so pointwise on `V(Λ)`,
   `f(‖x‖²) = f(dist(x,Λ)²)`.
2. `x ↦ f(dist(x,Λ)²)` is Λ-periodic
   (this file: `infDist_lattice_translate_eq`), and the integral of a bounded periodic
   function over any two bounded fundamental domains of Λ is equal; since
   `A·V(ℒ)` is a fundamental domain of `Λ` (linear image of one) we get
   `∫_{V(Λ)} f(‖x‖²) = ∫_{A·V} f(dist(x,Λ)²) dx`, i.e. `|det A|·g(A)` equals the
   dist-version of the smooth-side integral.
3. For `x ∈ A·V(ℒ)`, `|‖x‖ − dist(x,Λ)| ≤ C₁‖M‖` (move `x′ := (1−ν‖M‖)²x ∈ V(Λ)` using
   the sandwich, triangle inequality), hence by the FTC/Lipschitz bound of
   `r ↦ f(r²)` on `[0, 2μ(ℒ)]`: `|f(‖x‖²) − f(dist(x,Λ)²)| ≤ C₂‖M‖` on `A·V(ℒ)`.
4. The symmetric difference `V̂ := A·V(ℒ) ∖ V(Λ)` lies in the shell
   `(1+νε)V ∖ (1−νε)V`, whose real volume is `≤ ((1+νε)^m − (1−νε)^m)·vol V`
   (`EpsVoronoi.measureReal_shell_le`), i.e. `vol V̂ ≤ C₀‖M‖`.
   Then `|det A|·|h−g| ≤ vol(V̂)·C₂‖M‖ ≤ C·‖M‖²`.  ∎

This module grows the step-(1) and periodicity infrastructure; the fundamental-domain
integral identity (step 2), the Lipschitz/covering-radius bounds (step 3) and the
`O(‖M‖²)` assembly (step 4) are the remaining blocks.  NOT on the import path of
`Solution` (kept off-path like `ShapeDeriv`/`EpsVoronoi` until the interior branch
assembly uses it).
-/

namespace Submission.SameGrad

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "VC" => Submission.Voronoi.voronoi

/-- **Step 1a.** On the Voronoi cell of a lattice, the distance to the lattice equals
the norm: `dist(x, ℒ) = ‖x‖` for `x ∈ V(ℒ)` (the closest lattice point to `x` is `0`). -/
lemma infDist_lattice_eq_norm_on_cell {ℒ : Submodule ℤ E} {x : E} (hx : x ∈ VC ℒ) :
    Metric.infDist x ((ℒ : Submodule ℤ E) : Set E) = ‖x‖ := by
  have h0mem : (0 : E) ∈ ((ℒ : Submodule ℤ E) : Set E) := by
    exact Submodule.zero_mem ℒ
  have hsne : ((ℒ : Submodule ℤ E) : Set E).Nonempty := ⟨0, h0mem⟩
  apply le_antisymm
  · calc
      Metric.infDist x ((ℒ : Submodule ℤ E) : Set E) ≤ dist x (0 : E) :=
        Metric.infDist_le_dist_of_mem h0mem
      _ = ‖x‖ := by simp [dist_eq_norm]
  · rw [Metric.le_infDist (s := ((ℒ : Submodule ℤ E) : Set E)) hsne]
    intro y hy
    let w : ℒ := ⟨y, hy⟩
    have hc := (Submission.VoronoiMeasure.mem_voronoi_iff_norm (ℒ := ℒ) x).mp hx w
    have hnorm : ‖x‖ ≤ dist x y := by
      have hd : dist x y = ‖x - (w : E)‖ := by
        simp [w, dist_eq_norm]
      rw [hd]
      have hc' : |‖x‖| ≤ |‖x - (w : E)‖| := (sq_le_sq.mp hc)
      have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
      have hw0 : 0 ≤ ‖x - (w : E)‖ := norm_nonneg _
      simpa [abs_of_nonneg hx0, abs_of_nonneg hw0] using hc'
    exact hnorm

/-- **Step 1b.** On the Voronoi cell, `f(‖x‖²) = f(dist(x,ℒ)²)` pointwise: the dist
version of the integrand agrees with the plain norm version on the cell. -/
lemma f_norm_sq_eq_f_dist_sq_on_cell {ℒ : Submodule ℤ E} {x : E} (hx : x ∈ VC ℒ)
    (f : ℝ → ℝ) : f (‖x‖ ^ 2) = f (Metric.infDist x ((ℒ : Submodule ℤ E) : Set E) ^ 2) := by
  congr 1
  rw [infDist_lattice_eq_norm_on_cell hx]

/-- **Step 2a (periodicity).** Distance to a lattice is invariant under translation by
a lattice vector: `dist(x + λ, ℒ) = dist(x, ℒ)` for `λ ∈ ℒ`.  Proved by transport along
the translation isometry `Φ y := y + λ` (which maps the lattice set onto itself). -/
lemma infDist_lattice_translate_eq {ℒ : Submodule ℤ E} {x : E} {lam : ℒ} :
    Metric.infDist (x + (lam : E)) ((ℒ : Submodule ℤ E) : Set E) =
      Metric.infDist x ((ℒ : Submodule ℤ E) : Set E) := by
  let Φ : E → E := fun y => y + (lam : E)
  have hΦ : Isometry Φ := by
    dsimp [Φ]
    exact isometry_add_right (lam : E)
  have hset : Φ '' ((ℒ : Submodule ℤ E) : Set E) = ((ℒ : Submodule ℤ E) : Set E) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact add_mem hz lam.2
    · intro hy
      refine ⟨y - (lam : E), ?_, ?_⟩
      · exact sub_mem hy lam.2
      · dsimp [Φ]
        simp
  have hmain := Metric.infDist_image (Φ := Φ) (t := ((ℒ : Submodule ℤ E) : Set E)) (x := x) hΦ
  rw [hset] at hmain
  simpa [Φ] using hmain

/-- **Bad-set volume is `o(‖M‖)` (paper `vol(V̂) ≤ ((1+νε)^m−(1−νε)^m)·vol V`).**  For a
lattice `ℒ` with cell `V := VC ℒ` satisfying `ball r ⊆ V ⊆ ball R` and minimal vector
length `≥ r`, and a perturbation `A` moving points by at most `ε‖x‖`, the bad region
`V̂ := (A·V) ∖ V(A·ℒ)` — the part of the smooth image cell that lies outside the
transformed-lattice cell — is contained in the shell `(1+νε)V ∖ (1−νε)V`
(`ν := 4+4R/r`), whose real volume is `((1+νε)^m − (1−νε)^m)·vol V`
(`EpsVoronoi.measureReal_shell_le`).  This is the volume half of the `o(‖M‖)` estimate
behind `thm:same_grad_VL`; the integrand-oscillation half is the next block. -/
lemma bad_set_volume_le (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hνe_lt : (4 + 4 * (R / r)) * ε < 1)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤) :
    (volume : Measure E).real ((A '' VC ℒ) \ voronoiImage A ℒ) ≤
      (((1 + (4 + 4 * (R / r)) * ε) ^ (Module.finrank ℝ E)) -
       ((1 - (4 + 4 * (R / r)) * ε) ^ (Module.finrank ℝ E))) *
      (volume : Measure E).real (VC ℒ) := by
  classical
  let ν : ℝ := 4 + 4 * (R / r)
  let a : ℝ := ν * ε
  have hνe : ν * ε ≤ 1 := le_of_lt (by simpa [ν] using hνe_lt)
  have ha0 : 0 ≤ a := by
    dsimp [a, ν]
    exact mul_nonneg (by nlinarith [div_nonneg hR0 (le_of_lt hr)]) hε0
  have ha1 : a < 1 := by simpa [a, ν] using hνe_lt
  have hup : A '' VC ℒ ⊆ (1 + a) • VC ℒ := by
    dsimp [a, ν]
    exact image_cell_upper_shell (ℒ := ℒ) r R ε hr hR0 hε0 hball hcell A hA
  have hlow : (1 - a) • VC ℒ ⊆ voronoiImage A ℒ := by
    dsimp [a, ν]
    exact voronoiImage_left_shell (ℒ := ℒ) (A := A) r R ε hr hR0 hε0 hε1 hνe hlam hA hcell
  let shell : Set E := ((1 + a) • VC ℒ) \ ((1 - a) • VC ℒ)
  have hbad_sub : (A '' VC ℒ) \ voronoiImage A ℒ ⊆ shell := by
    intro x hx
    refine ⟨hup hx.1, ?_⟩
    intro hxlow
    exact hx.2 (hlow hxlow)
  have hUfin : (volume : Measure E) ((1 + a) • VC ℒ) ≠ ⊤ := by
    have hms := measure_smul (1 + a) (VC ℒ)
    rw [hms]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin
  have hfin_shell : (volume : Measure E) shell ≠ ⊤ := by
    have hsubU : shell ⊆ (1 + a) • VC ℒ := by
      intro x hx
      exact hx.1
    have hUlt : (volume : Measure E) ((1 + a) • VC ℒ) < ⊤ :=
      (lt_top_iff_ne_top).mpr hUfin
    exact ne_of_lt (lt_of_le_of_lt (measure_mono hsubU) hUlt)
  have hmono := measureReal_mono (μ := (volume : Measure E)) (s₁ := (A '' VC ℒ) \ voronoiImage A ℒ)
    (s₂ := shell) hbad_sub (h₂ := hfin_shell)
  have hVmeas : MeasurableSet (VC ℒ) := Submission.Voronoi.voronoi_measurable ℒ
  have hVc : Convex ℝ (VC ℒ) := Submission.Voronoi.voronoi_convex ℒ
  have hV0 : (0 : E) ∈ VC ℒ := zero_mem_voronoi ℒ
  have hshell := measureReal_shell_le a (VC ℒ) hVc hV0 hVmeas hVfin ha0 ha1
  have hgoal : (volume : Measure E).real shell ≤
      (((1 + a) ^ (Module.finrank ℝ E)) - ((1 - a) ^ (Module.finrank ℝ E))) *
        (volume : Measure E).real (VC ℒ) := by
    simpa [shell] using hshell
  exact hmono.trans hgoal

/-- **Linearized bad-set bound**: with `a := (4+4R/r)·ε ≤ 1`, the bad set has real volume
`≤ m·2^m·a·vol V` (from `bad_set_volume_le` + `EpsVoronoi.shell_pow_lin`). -/
lemma bad_set_volume_lin (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hνe_lt : (4 + 4 * (R / r)) * ε < 1)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤) :
    (volume : Measure E).real ((A '' VC ℒ) \ voronoiImage A ℒ) ≤
      ((Module.finrank ℝ E : ℝ) * (2 : ℝ) ^ (Module.finrank ℝ E) *
        ((4 + 4 * (R / r)) * ε)) * (volume : Measure E).real (VC ℒ) := by
  have hb := bad_set_volume_le r R ε hr hR0 hε0 hε1 hνe_lt hball hcell hlam hA hVfin
  let a : ℝ := (4 + 4 * (R / r)) * ε
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by nlinarith [div_nonneg hR0 (le_of_lt hr)]) hε0
  have ha1 : a < 1 := by simpa [a] using hνe_lt
  have hlin := shell_pow_lin (Module.finrank ℝ E) a ha0 (le_of_lt ha1)
  have hnonneg : 0 ≤ (volume : Measure E).real (VC ℒ) := measureReal_nonneg
  calc
    (volume : Measure E).real ((A '' VC ℒ) \ voronoiImage A ℒ)
        ≤ (((1 + a) ^ (Module.finrank ℝ E)) - ((1 - a) ^ (Module.finrank ℝ E))) *
            (volume : Measure E).real (VC ℒ) := by simpa [a] using hb
    _ ≤ ((Module.finrank ℝ E : ℝ) * (2 : ℝ) ^ (Module.finrank ℝ E) * a) *
            (volume : Measure E).real (VC ℒ) := by
        exact mul_le_mul_of_nonneg_right hlin hnonneg
    _ = ((Module.finrank ℝ E : ℝ) * (2 : ℝ) ^ (Module.finrank ℝ E) *
            ((4 + 4 * (R / r)) * ε)) * (volume : Measure E).real (VC ℒ) := by
        rfl
/-- **Step 2 core (periodic integral over fundamental domains).**  For a lattice `ℒ` with
fundamental domain `VC ℒ`, any OTHER fundamental domain `F` of `ℒ` (given by `hFfund`), and
a `ℒ`-periodic measurable function `φ`, the integral over `F` equals the integral over the
Voronoi cell: `∫_F φ = ∫_{VC ℒ} φ`.  (This is mathlib's
`IsAddFundamentalDomain.setIntegral_eq` specialized; `φ` periodicity is the only input
besides the two fundamental-domain proofs.) -/
lemma integral_eq_of_periodic {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (F : Set E)
    (hFfund : IsAddFundamentalDomain ℒ F)
    (φ : E → ℝ) (hφper : ∀ (lam : ℒ) (x : E), φ (x + (lam : E)) = φ x) :
    (∫ x in F, φ x) = ∫ x in (VC ℒ), φ x := by
  classical
  haveI : VAddInvariantMeasure ℒ E (volume : Measure E) :=
    (inferInstance : VAddInvariantMeasure ℒ.toAddSubgroup E (volume : Measure E))
  have hVfund : IsAddFundamentalDomain ℒ (VC ℒ) :=
    Submission.VoronoiMeasure.isAddFundamentalDomain_voronoi (ℒ := ℒ) hℒ
  have hper' : ∀ (lam : ℒ) (x : E), φ ((lam : ℒ) +ᵥ x) = φ x := by
    intro lam x
    rw [Submission.VoronoiMeasure.lattice_vadd_apply]
    simpa [add_comm] using hφper lam x
  exact (IsAddFundamentalDomain.setIntegral_eq (G := ℒ) hFfund hVfund (f := φ) hper')

/-- **Step 2 (Voronoi-cell form).**  `∫_{F} f(dist(x,ℒ)²) = ∫_{VC ℒ} f(‖x‖²)` for any
fundamental domain `F` of `ℒ`: on the cell `dist = ‖·‖` pointwise
(`infDist_lattice_eq_norm_on_cell`) and `x ↦ f(dist(x,ℒ)²)` is `ℒ`-periodic
(`infDist_lattice_translate_eq`), so the periodic-integral identity applies. -/
lemma dist_sq_integral_eq_of_fundamentalDomain {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (F : Set E)
    (hFfund : IsAddFundamentalDomain ℒ F) (f : ℝ → ℝ) :
    (∫ x in F, f (Metric.infDist x ((ℒ : Submodule ℤ E) : Set E) ^ 2)) =
      ∫ x in (VC ℒ), f (‖x‖ ^ 2) := by
  classical
  let φ : E → ℝ := fun x => f (Metric.infDist x ((ℒ : Submodule ℤ E) : Set E) ^ 2)
  have hφper : ∀ (lam : ℒ) (x : E), φ (x + (lam : E)) = φ x := by
    intro lam x
    dsimp [φ]
    congr 1
    congr 1
    exact infDist_lattice_translate_eq (ℒ := ℒ) (x := x) (lam := lam)
  have hmain := integral_eq_of_periodic (ℒ := ℒ) hℒ F hFfund φ hφper
  have hcell : (∫ x in (VC ℒ), φ x) = ∫ x in (VC ℒ), f (‖x‖ ^ 2) := by
    apply MeasureTheory.setIntegral_congr_fun (s := (VC ℒ))
    · exact (Submission.Voronoi.voronoi_measurable ℒ)
    · intro x hx
      dsimp [φ]
      rw [infDist_lattice_eq_norm_on_cell (ℒ := ℒ) hx]
  calc
    (∫ x in F, f (Metric.infDist x ((ℒ : Submodule ℤ E) : Set E) ^ 2))
        = (∫ x in F, φ x) := by rfl
    _ = (∫ x in (VC ℒ), φ x) := hmain
    _ = ∫ x in (VC ℒ), f (‖x‖ ^ 2) := hcell
/-- scalar-multiple of a measure is absolutely continuous w.r.t. it. -/
lemma smul_absolutelyContinuous (c : ENNReal) (ν : Measure E) :
    Measure.AbsolutelyContinuous (c • ν) ν := by
  intro s hs
  rw [Measure.smul_apply]
  simp [hs]

/-- A real-linear equivalence is quasi-measure-preserving for the Haar volume. -/
lemma linearEquiv_quasiMeasurePreserving (e : E ≃ₗ[ℝ] E) :
    QuasiMeasurePreserving (fun x : E => e x) (volume : Measure E) (volume : Measure E) := by
  refine ⟨?_, ?_⟩
  · exact Continuous.measurable (e.toContinuousLinearEquiv : E →L[ℝ] E).continuous
  · have hd : LinearMap.det (e : E →ₗ[ℝ] E) ≠ 0 := by
      have hcomp : (e : E →ₗ[ℝ] E) ∘ₗ (e.symm : E →ₗ[ℝ] E) = LinearMap.id := by
        ext x
        simp
      have hdet1 : LinearMap.det (e : E →ₗ[ℝ] E) * LinearMap.det (e.symm : E →ₗ[ℝ] E) = 1 := by
        rw [← LinearMap.det_comp, hcomp, LinearMap.det_id]
      intro hz
      rw [hz, zero_mul] at hdet1
      norm_num at hdet1
    have h' := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure E) (f := (e : E →ₗ[ℝ] E)) hd
    have hmap : Measure.map (fun x : E => e x) (volume : Measure E) =
        ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹| • (volume : Measure E) := by
      convert h' using 1
      ext x
      rfl
    rw [hmap]
    exact smul_absolutelyContinuous (ENNReal.ofReal |(LinearMap.det (e : E →ₗ[ℝ] E))⁻¹|) volume

/-- translate of the image-cell: `A '' (y +ᵥ V) = (A y) +ᵥ (A '' V)` for a linear map A. -/
lemma image_vadd {A : E →ₗ[ℝ] E} (y : E) (V : Set E) :
    A '' (y +ᵥ V) = ((A y : E) +ᵥ (A '' V)) := by
  ext z
  constructor
  · intro hz
    rw [Set.mem_image] at hz
    rcases hz with ⟨x, hx, rfl⟩
    rcases (Set.mem_vadd_set.mp hx) with ⟨v, hv, hxv⟩
    rw [Set.mem_vadd_set]
    refine ⟨A v, ⟨v, hv, rfl⟩, ?_⟩
    rw [vadd_eq_add]
    have hxv' : y + v = x := by simpa [vadd_eq_add] using hxv
    calc
      A y + A v = A (y + v) := by rw [map_add]
      _ = A x := by rw [hxv']
  · intro hz
    rw [Set.mem_vadd_set] at hz
    rcases hz with ⟨u, hu, hzu⟩
    rw [Set.mem_image] at hu
    rcases hu with ⟨v, hv, rfl⟩
    rw [Set.mem_image]
    refine ⟨y + v, ?_, ?_⟩
    · rw [Set.mem_vadd_set]
      exact ⟨v, hv, by simp [vadd_eq_add]⟩
    · rw [map_add]
      rw [vadd_eq_add] at hzu
      exact hzu

/-- **`A·V(ℒ)` is a fundamental domain of the image lattice `Λ := A·ℒ`** (paper
`clm:transform_fund_body`). -/
lemma transform_fund_body {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (A : E →ₗ[ℝ] E) (hdetA : LinearMap.det A ≠ 0) :
    IsAddFundamentalDomain (ℒ.map (A.restrictScalars ℤ)) (A '' (VC ℒ)) := by
  classical
  let Λ : Submodule ℤ E := ℒ.map (A.restrictScalars ℤ)
  let e : E ≃ₗ[ℝ] E := LinearMap.equivOfDetNeZero A hdetA
  have heA : ∀ x : E, e x = A x := by intro x; rfl
  have hAinj : Function.Injective A := by
    intro x y hxy
    have : e x = e y := by simpa [heA] using hxy
    exact LinearEquiv.injective e this
  have hfundL : IsAddFundamentalDomain ℒ (VC ℒ) :=
    Submission.VoronoiMeasure.isAddFundamentalDomain_voronoi (ℒ := ℒ) hℒ
  refine MeasureTheory.IsAddFundamentalDomain.mk'' (G := Λ) (s := A '' (VC ℒ)) ?_ ?_ ?_ ?_
  · have hVcl : IsClosed (VC ℒ) := Submission.Voronoi.voronoi_isClosed ℒ
    let eH : E ≃ₜ E := e.toContinuousLinearEquiv.toHomeomorph
    have hcl0 : IsClosed (eH '' (VC ℒ)) := eH.isClosedMap (VC ℒ) hVcl
    have himg : eH '' (VC ℒ) = A '' (VC ℒ) := by
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        refine ⟨x, hx, ?_⟩
        simpa [eH, heA] using hxy
      · rintro ⟨x, hx, hxy⟩
        refine ⟨x, hx, ?_⟩
        simpa [eH, heA] using hxy
    rw [← himg]
    exact hcl0.nullMeasurableSet
  · have hqmp : QuasiMeasurePreserving (fun x : E => e.symm x) (volume : Measure E)
        (volume : Measure E) := linearEquiv_quasiMeasurePreserving e.symm
    have hcov' : ∀ᵐ x ∂(volume : Measure E), ∃ lam : ℒ,
        (lam : ℒ) +ᵥ (e.symm x) ∈ (VC ℒ) := by
      exact hqmp.ae hfundL.ae_covers
    filter_upwards [hcov'] with x hlam
    rcases hlam with ⟨lam, hmem⟩
    rw [Submission.VoronoiMeasure.lattice_vadd_apply] at hmem
    let u : E := (lam : E) + e.symm x
    have hu : u ∈ (VC ℒ) := by simpa [u] using hmem
    have heu : e u = e ((lam : ℒ) : E) + x := by
      dsimp [u]
      rw [map_add]
      simp
    have hgmem : e ((lam : ℒ) : E) ∈ (Λ : Set E) := by
      dsimp [Λ]
      rw [Set.mem_image]
      refine ⟨((lam : ℒ) : E), (lam : ℒ).2, ?_⟩
      exact (heA ((lam : ℒ) : E)).symm
    refine ⟨⟨e ((lam : ℒ) : E), hgmem⟩, ?_⟩
    rw [Submission.VoronoiMeasure.lattice_vadd_apply]
    change e ((lam : ℒ) : E) + x ∈ A '' (VC ℒ)
    rw [Set.mem_image]
    refine ⟨u, hu, ?_⟩
    calc
      A u = e u := (heA u).symm
      _ = e ((lam : ℒ) : E) + x := heu

  · intro w hw0
    have hw2 : (w : E) ∈ (Λ : Set E) := w.2
    dsimp [Λ] at hw2
    rw [Set.mem_image] at hw2
    rcases hw2 with ⟨y0, hy0, hAy0⟩
    let lam : ℒ := ⟨y0, hy0⟩
    have hlamval : (lam : E) = y0 := rfl
    have hAy0' : A y0 = (w : E) := hAy0
    have hwne : (w : E) ≠ 0 := by
      intro hz
      apply hw0
      exact (Submodule.coe_eq_zero.mp hz)
    have hlam0 : lam ≠ 0 := by
      intro hl
      apply hwne
      rw [← hAy0']
      have hz : y0 = 0 := by
        have : (lam : E) = 0 := (Submodule.coe_eq_zero.mpr hl)
        simpa [hlamval] using this
      simp [hz]
    have hadj : AEDisjoint (volume : Measure E) ((lam : ℒ) +ᵥ (VC ℒ)) ((0 : ℒ) +ᵥ (VC ℒ)) :=
      hfundL.aedisjoint (show lam ≠ (0 : ℒ) from hlam0)
    have hzero : volume (((lam : ℒ) +ᵥ (VC ℒ)) ∩ (VC ℒ)) = 0 := by
      unfold AEDisjoint at hadj
      simpa using hadj
    unfold AEDisjoint
    have htrans : (w +ᵥ (A '' (VC ℒ))) ∩ (A '' (VC ℒ)) =
        A '' ((((lam : ℒ) +ᵥ (VC ℒ)) ∩ (VC ℒ))) := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨hxw, hx2⟩
        rw [Set.mem_vadd_set] at hxw
        rcases hxw with ⟨a, ha, hxa⟩
        rw [Set.mem_image] at ha
        rcases ha with ⟨v, hv, hav⟩
        rw [Set.mem_image] at hx2
        rcases hx2 with ⟨v2, hv2, hv2eq⟩
        have hmain : A (((lam : E)) + v) = A v2 := by
          calc
            A ((lam : E) + v) = A (lam : E) + A v := by rw [map_add]
            _ = (w : E) + A v := by rw [hAy0']
            _ = x := by
              rw [Submission.VoronoiMeasure.lattice_vadd_apply] at hxa
              rw [← hxa]
              rw [hav]
            _ = A v2 := by rw [hv2eq]
        have hpre : (lam : E) + v = v2 := hAinj hmain
        rw [Set.mem_image]
        refine ⟨(lam : E) + v, ?_, ?_⟩
        · constructor
          · rw [Set.mem_vadd_set]
            exact ⟨v, hv, Submission.VoronoiMeasure.lattice_vadd_apply lam v⟩
          · rw [hpre]
            exact hv2
        · exact hmain.trans hv2eq
      · intro hx
        rw [Set.mem_image] at hx
        rcases hx with ⟨u, hu, hxu⟩
        rcases hu with ⟨hu1, hu2⟩
        rw [Set.mem_vadd_set] at hu1
        rcases hu1 with ⟨v, hv, huv⟩
        have huv' : ((lam : E)) + v = u := by simpa [vadd_eq_add] using huv
        constructor
        · rw [Set.mem_vadd_set]
          refine ⟨A v, ⟨v, hv, rfl⟩, ?_⟩
          rw [Submission.VoronoiMeasure.lattice_vadd_apply]
          calc
            (w : E) + A v = A y0 + A v := by rw [hAy0']
            _ = A (y0 + v) := by rw [map_add]
            _ = A u := by
              have : y0 + v = u := by
                calc
                  y0 + v = (lam : E) + v := by rw [hlamval]
                  _ = u := huv'
              rw [this]
            _ = x := hxu
        · rw [Set.mem_image]
          refine ⟨u, hu2, hxu⟩
    rw [htrans]
    have hsc := Submission.EpsVoronoi.measure_map_cell A ((((lam : ℒ) +ᵥ (VC ℒ)) ∩ (VC ℒ)))
    rw [hsc]
    rw [hzero]
    simp
  · intro w
    have hmp : MeasurePreserving (fun x : E => w +ᵥ x) volume volume := by
      haveI : VAddInvariantMeasure ↥Λ E (volume : Measure E) :=
        (inferInstance : VAddInvariantMeasure ↥Λ.toAddSubgroup E (volume : Measure E))
      exact MeasureTheory.measurePreserving_vadd (M := ↥Λ) w (volume : Measure E)
    exact hmp.quasiMeasurePreserving
/-- the image lattice of a discrete lattice under an invertible linear map is discrete. -/
lemma discreteTopology_map {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (A : E →ₗ[ℝ] E) (hdetA : LinearMap.det A ≠ 0) :
    DiscreteTopology ↥(ℒ.map (A.restrictScalars ℤ)) := by
  classical
  let e : E ≃ₗ[ℝ] E := LinearMap.equivOfDetNeZero A hdetA
  have heA : ∀ x : E, e x = A x := by intro x; rfl
  let Λ : Submodule ℤ E := ℒ.map (A.restrictScalars ℤ)
  let φ : ↥Λ → ↥ℒ := fun w => ⟨e.symm (w : E), by
    have hw2 : (w : E) ∈ (Λ : Set E) := w.2
    dsimp [Λ] at hw2
    rw [Set.mem_image] at hw2
    rcases hw2 with ⟨y, hy, hAy⟩
    have hthis : e.symm (w : E) = y := by
      rw [← hAy, ← heA y]
      simp
    rw [hthis]
    exact hy⟩
  refine DiscreteTopology.of_continuous_injective (f := φ) ?_ ?_
  · apply Continuous.subtype_mk
    exact (e.symm.toContinuousLinearEquiv : E →L[ℝ] E).continuous.comp continuous_subtype_val
  · intro w w' hww'
    have hval : e.symm (w : E) = e.symm (w' : E) := by
      have := congrArg (fun z : ↥ℒ => (z : E)) hww'
      simpa [φ] using this
    exact Subtype.ext (e.symm.injective hval)

/-- The image lattice spans the whole space (it is a full-rank lattice). -/
lemma span_top_map {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (A : E →ₗ[ℝ] E) (hdetA : LinearMap.det A ≠ 0) :
    Submodule.span ℝ ((ℒ.map (A.restrictScalars ℤ) : Submodule ℤ E) : Set E) = ⊤ := by
  let e : E ≃ₗ[ℝ] E := LinearMap.equivOfDetNeZero A hdetA
  have heA : ∀ x : E, e x = A x := by intro x; rfl
  have hset : ((ℒ.map (A.restrictScalars ℤ) : Submodule ℤ E) : Set E) = A '' (ℒ : Set E) := by
    ext x
    constructor
    · intro hx
      rw [SetLike.mem_coe, Submodule.mem_map] at hx
      rcases hx with ⟨y, hy, hAy⟩
      rw [LinearMap.restrictScalars_apply ℤ A y] at hAy
      rw [Set.mem_image]
      exact ⟨y, hy, hAy⟩
    · intro hx
      rw [Set.mem_image] at hx
      rcases hx with ⟨y, hy, hAy⟩
      rw [SetLike.mem_coe, Submodule.mem_map]
      exact ⟨y, hy, by rw [LinearMap.restrictScalars_apply ℤ A y]; exact hAy⟩
  rw [hset]
  rw [← Submodule.map_span (f := A) ((ℒ : Set E))]
  rw [hℒ.span_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (fun y => ⟨e.symm y, by
    rw [← heA (e.symm y)]
    simp⟩)

/-- **Step 2 (paper Eq. (1), second identity).**  For a lattice `ℒ`, an invertible
`A`, and any `f`, the integral over the *positioned* cell `A·V(ℒ)` of `f(dist(·,Aℒ)²)`
equals the integral over the *transformed-lattice* cell `V(Aℒ)` of `f(‖·‖²)`. -/
theorem cell_dist_integral_image_eq {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (A : E →ₗ[ℝ] E) (hdetA : LinearMap.det A ≠ 0) (f : ℝ → ℝ) :
    (∫ x in A '' (VC ℒ),
        f (Metric.infDist x (((ℒ.map (A.restrictScalars ℤ)) : Submodule ℤ E) : Set E) ^ 2)) =
      ∫ x in VC (ℒ.map (A.restrictScalars ℤ)), f (‖x‖ ^ 2) := by
  classical
  letI hd : DiscreteTopology ↥(ℒ.map (A.restrictScalars ℤ)) := discreteTopology_map A hdetA
  have hΛ : IsZLattice ℝ (ℒ.map (A.restrictScalars ℤ)) := ⟨span_top_map hℒ A hdetA⟩
  have hFfund : IsAddFundamentalDomain (ℒ.map (A.restrictScalars ℤ)) (A '' (VC ℒ)) :=
    transform_fund_body hℒ A hdetA
  exact dist_sq_integral_eq_of_fundamentalDomain hΛ (A '' (VC ℒ)) hFfund f
/-- scaling down a convex set containing `0`. -/
lemma smul_subset_self_of_le_one {V : Set E} (hC : Convex ℝ V) (h0 : (0 : E) ∈ V)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : c • V ⊆ V := by
  have h := Submission.EpsVoronoi.smul_subset_smul_of_le (V := V) hC h0 hc0 hc1
  simpa using h

/-- **The `x' := (1−νε)²x` move**: a point of the positioned cell `A·V(ℒ)` scaled down by
`(1−νε)²` lands in the transformed-lattice cell `V(A·ℒ)`. -/
lemma lower_move_mem (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hνe_lt : (4 + 4 * (R / r)) * ε < 1)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    {x : E} (hx : x ∈ A '' VC ℒ) :
    (1 - (4 + 4 * (R / r)) * ε) ^ 2 • x ∈ voronoiImage A ℒ := by
  let a : ℝ := (4 + 4 * (R / r)) * ε
  have ha1 : a < 1 := by simpa [a] using hνe_lt
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by nlinarith [div_nonneg hR0 (le_of_lt hr)]) hε0
  have hup : A '' VC ℒ ⊆ (1 + a) • VC ℒ := by
    dsimp [a]
    exact image_cell_upper_shell (ℒ := ℒ) r R ε hr hR0 hε0 hball hcell A hA
  have hlow : (1 - a) • VC ℒ ⊆ voronoiImage A ℒ := by
    dsimp [a]
    exact voronoiImage_left_shell (ℒ := ℒ) (A := A) r R ε hr hR0 hε0 hε1 hνe_lt.le hlam hA hcell
  rcases (Set.mem_smul_set.mp (hup hx)) with ⟨v, hv, hxv⟩
  have hstep : (1 - a) ^ 2 • x ∈ (1 - a) • VC ℒ := by
    rw [← hxv, smul_smul]
    rw [Set.mem_smul_set]
    refine ⟨(1 - a ^ 2) • v, ?_, ?_⟩
    · refine smul_subset_self_of_le_one (c := 1 - a ^ 2) (Submission.Voronoi.voronoi_convex ℒ)
        (zero_mem_voronoi ℒ) ?_ ?_ (Set.mem_smul_set.mpr ⟨v, hv, rfl⟩)
      · have hfac : (1 : ℝ) - a ^ 2 = (1 - a) * (1 + a) := by ring
        rw [hfac]
        exact mul_nonneg (by linarith) (by linarith)
      · nlinarith [sq_nonneg a]
    · rw [smul_smul]
      rw [show (1 - a) * (1 - a ^ 2) = (1 - a) ^ 2 * (1 + a) by ring]
  exact hlow hstep

/-- **Distance oscillation**: on the positioned cell `A·V(ℒ)`, the two numbers `‖x‖` and
`dist(x, A·ℒ)` differ by at most `4νε(1+νε)R`. -/
lemma dist_oscillation_le (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hνe_lt : (4 + 4 * (R / r)) * ε < 1)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    {x : E} (hx : x ∈ A '' VC ℒ) :
    |‖x‖ - Metric.infDist x (((ℒ.map (A.restrictScalars ℤ)) : Submodule ℤ E) : Set E)| ≤
      4 * ((4 + 4 * (R / r)) * ε) * (1 + (4 + 4 * (R / r)) * ε) * R := by
  classical
  let a : ℝ := (4 + 4 * (R / r)) * ε
  let Λ : Submodule ℤ E := ℒ.map (A.restrictScalars ℤ)
  have ha1 : a < 1 := by simpa [a] using hνe_lt
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by nlinarith [div_nonneg hR0 (le_of_lt hr)]) hε0
  have hup : A '' VC ℒ ⊆ (1 + a) • VC ℒ := by
    dsimp [a]
    exact image_cell_upper_shell (ℒ := ℒ) r R ε hr hR0 hε0 hball hcell A hA
  -- ‖x‖ ≤ (1+a) R
  have hxR : ‖x‖ ≤ (1 + a) * R := by
    rcases (Set.mem_smul_set.mp (hup hx)) with ⟨v, hv, hxv⟩
    have hvR : ‖v‖ ≤ R := by
      have hb := Metric.mem_closedBall.mp (hcell hv)
      simpa [dist_eq_norm] using hb
    rw [← hxv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + a)]
    exact mul_le_mul_of_nonneg_left hvR (by linarith)
  -- the moved point
  have hx'mem : (1 - a) ^ 2 • x ∈ VC Λ := by
    have h := lower_move_mem (ℒ := ℒ) (A := A) r R ε hr hR0 hε0 hε1 hνe_lt hball hcell hlam hA hx
    dsimp [Λ]
    rw [Submission.EpsVoronoi.voronoi_map_lattice]
    exact h
  have hx'dist : Metric.infDist ((1 - a) ^ 2 • x) ((Λ : Submodule ℤ E) : Set E) = ‖(1 - a) ^ 2 • x‖ :=
    infDist_lattice_eq_norm_on_cell (ℒ := Λ) hx'mem
  -- bounds
  have hnorm1 : |‖x‖ - ‖(1 - a) ^ 2 • x‖| ≤ ‖x - (1 - a) ^ 2 • x‖ := abs_norm_sub_norm_le x _
  have hinf1 : |‖(1 - a) ^ 2 • x‖ - Metric.infDist x ((Λ : Submodule ℤ E) : Set E)| ≤
      ‖x - (1 - a) ^ 2 • x‖ := by
    rw [← hx'dist]
    have htri : |Metric.infDist ((1 - a) ^ 2 • x) ((Λ : Submodule ℤ E) : Set E) -
        Metric.infDist x ((Λ : Submodule ℤ E) : Set E)| ≤
        dist ((1 - a) ^ 2 • x) x := by
      have h1 := Metric.infDist_le_infDist_add_dist
        (x := ((1 - a) ^ 2 • x)) (y := x) (s := ((Λ : Submodule ℤ E) : Set E))
      have h2 := Metric.infDist_le_infDist_add_dist
        (x := x) (y := ((1 - a) ^ 2 • x)) (s := ((Λ : Submodule ℤ E) : Set E))
      rw [abs_sub_le_iff]
      constructor <;> linarith [dist_comm ((1 - a) ^ 2 • x) x]
    have hd : dist ((1 - a) ^ 2 • x) x = ‖x - (1 - a) ^ 2 • x‖ := by
      rw [dist_eq_norm, norm_sub_rev]
    rwa [hd] at htri
  -- ‖x − (1−a)²x‖ = (1 − (1−a)²)·‖x‖
  have hsub : ‖x - (1 - a) ^ 2 • x‖ = (1 - (1 - a) ^ 2) * ‖x‖ := by
    have hrw : x - (1 - a) ^ 2 • x = (1 - (1 - a) ^ 2) • x := by
      rw [sub_smul, one_smul]
    rw [hrw, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith [sq_nonneg (1 - a), ha0, ha1])]
  -- assemble
  have hmain : |‖x‖ - Metric.infDist x ((Λ : Submodule ℤ E) : Set E)| ≤
      2 * (1 - (1 - a) ^ 2) * ‖x‖ := by
    have hsplit : |‖x‖ - Metric.infDist x ((Λ : Submodule ℤ E) : Set E)| ≤
        |‖x‖ - ‖(1 - a) ^ 2 • x‖| +
          |‖(1 - a) ^ 2 • x‖ - Metric.infDist x ((Λ : Submodule ℤ E) : Set E)| := by
      have := dist_triangle ‖x‖ ‖(1 - a) ^ 2 • x‖
        (Metric.infDist x ((Λ : Submodule ℤ E) : Set E))
      simpa [Real.dist_eq] using this
    rw [hsub] at hnorm1
    rw [hsub] at hinf1
    linarith [hsplit, hnorm1, hinf1]
  have hfac : 2 * (1 - (1 - a) ^ 2) ≤ 4 * a := by nlinarith [ha0, ha1]
  calc
    |‖x‖ - Metric.infDist x ((Λ : Submodule ℤ E) : Set E)| ≤ 2 * (1 - (1 - a) ^ 2) * ‖x‖ := hmain
    _ ≤ 4 * a * ‖x‖ := by
        have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
        nlinarith [hfac, hx0]
    _ ≤ 4 * a * ((1 + a) * R) := by
        have : 0 ≤ 4 * a := by linarith
        exact mul_le_mul_of_nonneg_left hxR this
    _ = 4 * a * (1 + a) * R := by ring

/-- Mean-value (FTC) bound for `r ↦ f (r^2)`: for `a, b ∈ [0, B]`,
`|f (a^2) − f (b^2)| ≤ C·(2B)·|a − b|` when `‖deriv f‖ ≤ C` on `[0, B^2]`. -/
lemma abs_sub_sq_le {f : ℝ → ℝ} {B C : ℝ} (hC0 : 0 ≤ C) (hB0 : 0 ≤ B)
    (hdiff : ∀ x ∈ Set.Icc 0 (B ^ 2), DifferentiableAt ℝ f x)
    (hbound : ∀ x ∈ Set.Icc 0 (B ^ 2), ‖deriv f x‖ ≤ C)
    {a b : ℝ} (ha : a ∈ Set.Icc 0 B) (hb : b ∈ Set.Icc 0 B) :
    |f (a ^ 2) - f (b ^ 2)| ≤ C * (2 * B) * |a - b| := by
  have hsq_a : a ^ 2 ∈ Set.Icc 0 (B ^ 2) := ⟨sq_nonneg a, pow_le_pow_left₀ ha.1 ha.2 2⟩
  have hsq_b : b ^ 2 ∈ Set.Icc 0 (B ^ 2) := ⟨sq_nonneg b, pow_le_pow_left₀ hb.1 hb.2 2⟩
  have hconv : Convex ℝ (Set.Icc 0 (B ^ 2)) := convex_Icc _ _
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.Icc 0 (B ^ 2))
    (x := b ^ 2) (y := a ^ 2) (C := C) hdiff hbound hconv hsq_b hsq_a
  have hnorm : |f (a ^ 2) - f (b ^ 2)| ≤ C * |a ^ 2 - b ^ 2| := by
    simpa [Real.norm_eq_abs] using hmvt
  have hab : |a ^ 2 - b ^ 2| ≤ (2 * B) * |a - b| := by
    rw [sq_sub_sq, abs_mul]
    have h1 : |a + b| ≤ 2 * B := by
      rw [abs_of_nonneg (by linarith [ha.1, hb.1])]
      linarith [ha.2, hb.2]
    have h2 : 0 ≤ |a - b| := abs_nonneg _
    nlinarith [h1]
  calc
    |f (a ^ 2) - f (b ^ 2)| ≤ C * |a ^ 2 - b ^ 2| := hnorm
    _ ≤ C * ((2 * B) * |a - b|) := mul_le_mul_of_nonneg_left hab hC0
    _ = C * (2 * B) * |a - b| := by ring



/-- **Integrand oscillation (step 3).**  On the positioned cell `A·V(ℒ)`, the dist-version
and the norm-version of a `C¹` integrand `f (·²)` differ by `C·4R·(4νε(1+νε)R)`, where `C`
bounds `‖deriv f‖` on `[0, (2R)²]`. -/
lemma integrand_oscillation_le (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hνe_lt : (4 + 4 * (R / r)) * ε < 1)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    {f : ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hdiff : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), DifferentiableAt ℝ f u)
    (hbound : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), ‖deriv f u‖ ≤ C) :
    ∀ x ∈ A '' VC ℒ,
      |f (‖x‖ ^ 2) - f (Metric.infDist x (((ℒ.map (A.restrictScalars ℤ)) : Submodule ℤ E) : Set E) ^ 2)|
        ≤ C * (2 * (2 * R)) *
          (4 * ((4 + 4 * (R / r)) * ε) * (1 + (4 + 4 * (R / r)) * ε) * R) := by
  intro x hx
  let a : ℝ := (4 + 4 * (R / r)) * ε
  let Λ : Submodule ℤ E := ℒ.map (A.restrictScalars ℤ)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by nlinarith [div_nonneg hR0 (le_of_lt hr)]) hε0
  have ha1 : a ≤ 1 := le_of_lt (by simpa [a] using hνe_lt)
  have hB0 : (0 : ℝ) ≤ 2 * R := by linarith
  -- bounds on ‖x‖ and dist
  have hup : A '' VC ℒ ⊆ (1 + a) • VC ℒ := by
    dsimp [a]
    exact image_cell_upper_shell (ℒ := ℒ) r R ε hr hR0 hε0 hball hcell A hA
  have hxR : ‖x‖ ≤ 2 * R := by
    have h1 : ‖x‖ ≤ (1 + a) * R := by
      rcases (Set.mem_smul_set.mp (hup hx)) with ⟨v, hv, hxv⟩
      have hvR : ‖v‖ ≤ R := by
        have hb := Metric.mem_closedBall.mp (hcell hv)
        simpa [dist_eq_norm] using hb
      rw [← hxv, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + a)]
      exact mul_le_mul_of_nonneg_left hvR (by linarith)
    calc
      ‖x‖ ≤ (1 + a) * R := h1
      _ ≤ 2 * R := by nlinarith
  have hd0 : 0 ≤ Metric.infDist x ((Λ : Submodule ℤ E) : Set E) := Metric.infDist_nonneg
  have hdR : Metric.infDist x ((Λ : Submodule ℤ E) : Set E) ≤ 2 * R := by
    have h0mem : (0 : E) ∈ ((Λ : Submodule ℤ E) : Set E) := Submodule.zero_mem Λ
    calc
      Metric.infDist x ((Λ : Submodule ℤ E) : Set E) ≤ dist x (0 : E) :=
        Metric.infDist_le_dist_of_mem h0mem
      _ = ‖x‖ := by simp [dist_eq_norm]
      _ ≤ 2 * R := hxR
  have hdist : |‖x‖ - Metric.infDist x ((Λ : Submodule ℤ E) : Set E)| ≤
      4 * a * (1 + a) * R := by
    dsimp [a, Λ]
    exact dist_oscillation_le (ℒ := ℒ) (A := A) r R ε hr hR0 hε0 hε1 hνe_lt hball hcell hlam hA hx
  have hftc := abs_sub_sq_le (f := f) (B := 2 * R) (C := C) hC0 hB0 hdiff hbound
    (a := ‖x‖) (b := Metric.infDist x ((Λ : Submodule ℤ E) : Set E))
    ⟨norm_nonneg x, hxR⟩ ⟨hd0, hdR⟩
  calc
    |f (‖x‖ ^ 2) - f (Metric.infDist x ((Λ : Submodule ℤ E) : Set E) ^ 2)|
        ≤ C * (2 * (2 * R)) * |‖x‖ - Metric.infDist x ((Λ : Submodule ℤ E) : Set E)| := hftc
    _ ≤ C * (2 * (2 * R)) * (4 * a * (1 + a) * R) := by
        have h2 : 0 ≤ C * (2 * (2 * R)) := by positivity
        exact mul_le_mul_of_nonneg_left hdist h2
    _ = C * (2 * (2 * R)) * (4 * ((4 + 4 * (R / r)) * ε) * (1 + (4 + 4 * (R / r)) * ε) * R) := by
        rfl
/-- a 1-Lipschitz slice of `infDist`. -/
lemma infDist_lipschitz_one (s : Set E) :
    LipschitzWith 1 (fun x : E => Metric.infDist x s) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [NNReal.coe_one, one_mul]
  have h1 := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := s)
  have h2 := Metric.infDist_le_infDist_add_dist (x := y) (y := x) (s := s)
  rw [dist_comm y x] at h2
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor <;> linarith

theorem cell_integral_difference_le (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hνe_lt : (4 + 4 * (R / r)) * ε < 1)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    {f : ℝ → ℝ} (hfmeas : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hdiff : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), DifferentiableAt ℝ f u)
    (hbound : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), ‖deriv f u‖ ≤ C)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤) :
    |∫ x in A '' VC ℒ, (f (‖x‖ ^ 2) -
        f (Metric.infDist x (((ℒ.map (A.restrictScalars ℤ)) : Submodule ℤ E) : Set E) ^ 2))|
      ≤ (((1 + (4 + 4 * (R / r)) * ε) ^ (Module.finrank ℝ E) -
          (1 - (4 + 4 * (R / r)) * ε) ^ (Module.finrank ℝ E)) *
          (volume : Measure E).real (VC ℒ)) *
        (C * (2 * (2 * R)) * (4 * ((4 + 4 * (R / r)) * ε) * (1 + (4 + 4 * (R / r)) * ε) * R)) := by
  classical
  let a : ℝ := (4 + 4 * (R / r)) * ε
  let Λ : Submodule ℤ E := ℒ.map (A.restrictScalars ℤ)
  let B : ℝ := C * (2 * (2 * R)) * (4 * a * (1 + a) * R)
  let φ : E → ℝ := fun x => f (‖x‖ ^ 2) - f (Metric.infDist x ((Λ : Submodule ℤ E) : Set E) ^ 2)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by nlinarith [div_nonneg hR0 (le_of_lt hr)]) hε0
  have ha1 : a < 1 := by simpa [a] using hνe_lt
  have hvan : ∀ x ∈ (VC Λ : Set E), φ x = 0 := by
    intro x hx
    dsimp [φ]
    rw [infDist_lattice_eq_norm_on_cell (ℒ := Λ) hx]
    ring
  have hφmeas : Measurable φ := by
    have h1 : Measurable (fun x : E => f (‖x‖ ^ 2)) :=
      hfmeas.comp (continuous_norm.pow 2).measurable
    have h2 : Measurable (fun x : E => f (Metric.infDist x ((Λ : Submodule ℤ E) : Set E) ^ 2)) :=
      hfmeas.comp (((infDist_lipschitz_one ((Λ : Submodule ℤ E) : Set E)).continuous.pow 2)).measurable
    exact h1.sub h2
  -- measurability of the positioned cell (compact image)
  have hAmeas : MeasurableSet (A '' (VC ℒ)) := by
    have hK : IsCompact (VC ℒ) :=
      (isCompact_closedBall (0 : E) R).of_isClosed_subset (Submission.Voronoi.voronoi_isClosed ℒ) hcell
    exact ((hK.image (LinearMap.continuous_of_finiteDimensional A))).isClosed.measurableSet
  have hVΛmeas : MeasurableSet (VC Λ : Set E) := Submission.Voronoi.voronoi_measurable Λ
  have hμA : (volume : Measure E) (A '' (VC ℒ)) < ⊤ := by
    rw [Submission.EpsVoronoi.measure_map_cell A (VC ℒ)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((lt_top_iff_ne_top).mpr hVfin)
  have hbadsub : A '' (VC ℒ) \ (VC Λ : Set E) ⊆ A '' (VC ℒ) := Set.sdiff_subset
  have hμbad : (volume : Measure E) (A '' (VC ℒ) \ (VC Λ : Set E)) < ⊤ :=
    lt_of_le_of_lt (measure_mono hbadsub) hμA
  -- oscillation bound pointwise on the positioned cell
  have hosc := integrand_oscillation_le (ℒ := ℒ) (A := A) r R ε hr hR0 hε0 hε1 hνe_lt
    hball hcell hlam hA hC0 hdiff hbound
  have hpoint : ∀ x ∈ A '' (VC ℒ), ‖φ x‖ ≤ B := by
    intro x hx
    have h := hosc x hx
    rw [Real.norm_eq_abs]
    dsimp [φ, B, a, Λ] at h ⊢
    exact h
  -- decomposition: `φ` vanishes on the transformed-lattice cell
  have hsplit : ∫ x in (A '' (VC ℒ)), φ x =
      ∫ x in (A '' (VC ℒ) \ (VC Λ : Set E)), φ x := by
    have hpointwise : ∀ x : E, (A '' (VC ℒ)).indicator φ x =
        (A '' (VC ℒ) \ (VC Λ : Set E)).indicator φ x := by
      intro x
      by_cases hx : x ∈ A '' (VC ℒ)
      · by_cases hxb : x ∈ A '' (VC ℒ) \ (VC Λ : Set E)
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxb]
        · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hxb]
          have hxΛ : x ∈ (VC Λ : Set E) := by
            by_contra h
            exact hxb ⟨hx, h⟩
          exact hvan x hxΛ
      · rw [Set.indicator_of_notMem hx]
        by_cases hxb : x ∈ A '' (VC ℒ) \ (VC Λ : Set E)
        · exact absurd hxb.1 hx
        · rw [Set.indicator_of_notMem hxb]
    calc
      ∫ x in (A '' (VC ℒ)), φ x = ∫ x, (A '' (VC ℒ)).indicator φ x :=
        (MeasureTheory.integral_indicator (f := φ) hAmeas).symm
      _ = ∫ x, (A '' (VC ℒ) \ (VC Λ : Set E)).indicator φ x :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpointwise)
      _ = ∫ x in (A '' (VC ℒ) \ (VC Λ : Set E)), φ x :=
        MeasureTheory.integral_indicator (f := φ) (hAmeas.diff hVΛmeas)
  rw [hsplit]
  have hnorm := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (s := A '' (VC ℒ) \ (VC Λ : Set E)) (f := φ) (μ := (volume : Measure E)) (C := B)
    hμbad (fun x hx => hpoint x (hbadsub hx))
  rw [Real.norm_eq_abs] at hnorm
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have h1 : 0 ≤ 2 * (2 * R) := by linarith
    have h2 : 0 ≤ 4 * a * (1 + a) * R := by
      have : 0 ≤ 1 + a := by linarith
      positivity
    exact mul_nonneg (mul_nonneg hC0 h1) h2
  have hvol : (volume : Measure E).real (A '' (VC ℒ) \ (VC Λ : Set E)) ≤
      (((1 + a) ^ (Module.finrank ℝ E)) - ((1 - a) ^ (Module.finrank ℝ E))) *
        (volume : Measure E).real (VC ℒ) := by
    have h := bad_set_volume_le (ℒ := ℒ) (A := A) r R ε hr hR0 hε0 hε1 hνe_lt
      hball hcell hlam hA hVfin
    dsimp [a, Λ] at h ⊢
    rwa [← Submission.EpsVoronoi.voronoi_map_lattice] at h
  calc
    |∫ x in A '' (VC ℒ) \ (VC Λ : Set E), φ x|
        ≤ B * (volume : Measure E).real (A '' (VC ℒ) \ (VC Λ : Set E)) := hnorm
    _ ≤ B * ((((1 + a) ^ (Module.finrank ℝ E)) - ((1 - a) ^ (Module.finrank ℝ E))) *
          (volume : Measure E).real (VC ℒ)) := mul_le_mul_of_nonneg_left hvol hB0
    _ = ((((1 + a) ^ (Module.finrank ℝ E)) - ((1 - a) ^ (Module.finrank ℝ E))) *
          (volume : Measure E).real (VC ℒ)) * B := by ring
/-- **Step 4, linearized form (paper `|det(I+M)|·|h − g| ≤ C‖M‖²`).**  The cell-integral
difference is `O(ε²)`: bounded by `m·2^m·νε · vol V · (oscillation bound)`. -/
theorem cell_integral_difference_le_sq (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hνe_lt : (4 + 4 * (R / r)) * ε < 1)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    {f : ℝ → ℝ} (hfmeas : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hdiff : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), DifferentiableAt ℝ f u)
    (hbound : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), ‖deriv f u‖ ≤ C)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤) :
    |∫ x in A '' VC ℒ, (f (‖x‖ ^ 2) -
        f (Metric.infDist x (((ℒ.map (A.restrictScalars ℤ)) : Submodule ℤ E) : Set E) ^ 2))|
      ≤ ((Module.finrank ℝ E : ℝ) * (2 : ℝ) ^ (Module.finrank ℝ E) *
            ((4 + 4 * (R / r)) * ε)) *
          (volume : Measure E).real (VC ℒ) *
        (C * (2 * (2 * R)) * (4 * ((4 + 4 * (R / r)) * ε) * (1 + (4 + 4 * (R / r)) * ε) * R)) := by
  classical
  let a : ℝ := (4 + 4 * (R / r)) * ε
  let B : ℝ := C * (2 * (2 * R)) * (4 * a * (1 + a) * R)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by nlinarith [div_nonneg hR0 (le_of_lt hr)]) hε0
  have ha1 : a < 1 := by simpa [a] using hνe_lt
  have hmain := cell_integral_difference_le (ℒ := ℒ) (A := A) r R ε hr hR0 hε0 hε1 hνe_lt
    hball hcell hlam hA hfmeas hC0 hdiff hbound hVfin
  have hlin : ((1 + a) ^ (Module.finrank ℝ E)) - ((1 - a) ^ (Module.finrank ℝ E)) ≤
      (Module.finrank ℝ E : ℝ) * (2 : ℝ) ^ (Module.finrank ℝ E) * a :=
    shell_pow_lin (Module.finrank ℝ E) a ha0 (le_of_lt ha1)
  have hvol0 : 0 ≤ (volume : Measure E).real (VC ℒ) := measureReal_nonneg
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have h1 : 0 ≤ 2 * (2 * R) := by linarith
    have h2 : 0 ≤ 4 * a * (1 + a) * R := by
      have : 0 ≤ 1 + a := by linarith
      positivity
    exact mul_nonneg (mul_nonneg hC0 h1) h2
  have hstep : (((1 + a) ^ (Module.finrank ℝ E)) - ((1 - a) ^ (Module.finrank ℝ E))) *
        (volume : Measure E).real (VC ℒ) * B ≤
      ((Module.finrank ℝ E : ℝ) * (2 : ℝ) ^ (Module.finrank ℝ E) * a) *
          (volume : Measure E).real (VC ℒ) * B := by
    have h1 := mul_le_mul_of_nonneg_right hlin hvol0
    exact mul_le_mul_of_nonneg_right h1 hB0
  dsimp [a, B] at hmain hstep ⊢
  exact hmain.trans hstep
/-- **Matrix-level step 4 (the `hA` instantiation).**  With `A := mvec (1+M)` and
`ε := Σᵢⱼ|Mᵢⱼ|` (the ℓ¹ norm of the matrix, `≤ 1/(2(4+4R/r))` so that `νε ≤ 1/2`),
the cell-integral difference is bounded by the `O(ε²)` shell estimate. -/
theorem cell_integral_difference_le_matrix (r R : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R)
    {ℒ : Submodule ℤ E} (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hsmall : (4 + 4 * (R / r)) * (∑ i : Fin n, ∑ j : Fin n, |M i j|) ≤ 1 / 2)
    {f : ℝ → ℝ} (hfmeas : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hdiff : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), DifferentiableAt ℝ f u)
    (hbound : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), ‖deriv f u‖ ≤ C)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤) :
    |∫ x in (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + M)) '' VC ℒ,
        (f (‖x‖ ^ 2) - f (Metric.infDist x
          (((ℒ.map ((Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + M)).restrictScalars ℤ)) :
            Submodule ℤ E) : Set E) ^ 2))|
      ≤ ((Module.finrank ℝ E : ℝ) * (2 : ℝ) ^ (Module.finrank ℝ E) *
            ((4 + 4 * (R / r)) * (∑ i : Fin n, ∑ j : Fin n, |M i j|))) *
          (volume : Measure E).real (VC ℒ) *
        (C * (2 * (2 * R)) * (4 * ((4 + 4 * (R / r)) * (∑ i : Fin n, ∑ j : Fin n, |M i j|)) *
          (1 + (4 + 4 * (R / r)) * (∑ i : Fin n, ∑ j : Fin n, |M i j|)) * R)) := by
  classical
  let ε : ℝ := ∑ i : Fin n, ∑ j : Fin n, |M i j|
  have hε0 : 0 ≤ ε := by
    dsimp [ε]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have h4 : (1 : ℝ) ≤ 4 + 4 * (R / r) := by
    have : 0 ≤ R / r := div_nonneg hR0 (le_of_lt hr)
    linarith
  have hε1 : ε ≤ 1 / 2 := by
    have h1 : (1 : ℝ) * ε ≤ (4 + 4 * (R / r)) * ε := mul_le_mul_of_nonneg_right h4 hε0
    rw [one_mul] at h1
    exact h1.trans (by simpa [ε] using hsmall)
  have hνe : (4 + 4 * (R / r)) * ε < 1 := by
    have := (by simpa [ε] using hsmall : (4 + 4 * (R / r)) * ε ≤ 1 / 2)
    linarith
  have hA : ∀ w : E, ‖Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + M) w - w‖ ≤
      ε * ‖w‖ := by
    intro w
    have h := Submission.ShapeDeriv.mvec_one_add_lipschitz M w
    simpa [ε] using h
  have hmain := cell_integral_difference_le_sq (ℒ := ℒ)
    (A := Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + M))
    r R ε hr hR0 hε0 hε1 hνe hball hcell hlam hA hfmeas hC0 hdiff hbound hVfin
  simpa [ε] using hmain
/-- The paper's `g(A) = |det A|⁻¹ ∫_{V(A·ℒ)} f(‖x‖²)` (cell side). -/
noncomputable def shapeG (ℒ : Submodule ℤ E) (A : E →ₗ[ℝ] E) (f : ℝ → ℝ) : ℝ :=
  (|LinearMap.det A|)⁻¹ * ∫ x in VC (ℒ.map (A.restrictScalars ℤ)), f (‖x‖ ^ 2)

/-- The paper's `h(A) = |det A|⁻¹ ∫_{A·V(ℒ)} f(‖x‖²)` (smooth side). -/
noncomputable def shapeH (ℒ : Submodule ℤ E) (A : E →ₗ[ℝ] E) (f : ℝ → ℝ) : ℝ :=
  (|LinearMap.det A|)⁻¹ * ∫ x in A '' VC ℒ, f (‖x‖ ^ 2)

/-- **Identification, step 1**: `|det A|·(h(A) − g(A))` is the difference of the two
cell integrals. -/
theorem det_mul_shapeH_sub_shapeG {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (A : E →ₗ[ℝ] E) (hdetA : LinearMap.det A ≠ 0) (f : ℝ → ℝ) :
    |LinearMap.det A| * (shapeH ℒ A f - shapeG ℒ A f) =
      (∫ x in A '' VC ℒ, f (‖x‖ ^ 2)) -
        ∫ x in VC (ℒ.map (A.restrictScalars ℤ)), f (‖x‖ ^ 2) := by
  have hne : |LinearMap.det A| ≠ 0 := abs_ne_zero.mpr hdetA
  unfold shapeH shapeG
  rw [mul_sub]
  congr 1
  · rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  · rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- **Identification, step 2** (Session 108's `cell_dist_integral_image_eq`): the cell-integral
difference equals the integral of the oscillation `f(‖x‖²) − f(dist(x,Aℒ)²)` over `A·V(ℒ)`. -/
theorem cell_integral_difference_eq {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (A : E →ₗ[ℝ] E) (hdetA : LinearMap.det A ≠ 0) (f : ℝ → ℝ)
    (hint1 : IntegrableOn (fun x : E => f (‖x‖ ^ 2)) (A '' VC ℒ))
    (hint2 : IntegrableOn (fun x : E =>
        f (Metric.infDist x ((ℒ.map (A.restrictScalars ℤ) : Submodule ℤ E) : Set E) ^ 2))
      (A '' VC ℒ)) :
    (∫ x in A '' VC ℒ, f (‖x‖ ^ 2)) -
        ∫ x in VC (ℒ.map (A.restrictScalars ℤ)), f (‖x‖ ^ 2)
      = ∫ x in A '' VC ℒ, (f (‖x‖ ^ 2) -
          f (Metric.infDist x ((ℒ.map (A.restrictScalars ℤ) : Submodule ℤ E) : Set E) ^ 2)) := by
  rw [← cell_dist_integral_image_eq hℒ A hdetA f]
  exact (MeasureTheory.integral_sub hint1 hint2).symm

/-- **Paper Eq. (same_grad), abstract form**: `|det A|·|h(A) − g(A)| ≤ O(ε²)`. -/
theorem det_mul_shapeH_sub_shapeG_le (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hνe_lt : (4 + 4 * (R / r)) * ε < 1)
    {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {A : E →ₗ[ℝ] E} (hdetA : LinearMap.det A ≠ 0)
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    {f : ℝ → ℝ} (hfmeas : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hdiff : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), DifferentiableAt ℝ f u)
    (hbound : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), ‖deriv f u‖ ≤ C)
    (hint1 : IntegrableOn (fun x : E => f (‖x‖ ^ 2)) (A '' VC ℒ))
    (hint2 : IntegrableOn (fun x : E =>
        f (Metric.infDist x ((ℒ.map (A.restrictScalars ℤ) : Submodule ℤ E) : Set E) ^ 2))
      (A '' VC ℒ))
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤) :
    |LinearMap.det A| * |shapeH ℒ A f - shapeG ℒ A f| ≤
      (((1 + (4 + 4 * (R / r)) * ε) ^ (Module.finrank ℝ E) -
          (1 - (4 + 4 * (R / r)) * ε) ^ (Module.finrank ℝ E)) *
          (volume : Measure E).real (VC ℒ)) *
        (C * (2 * (2 * R)) * (4 * ((4 + 4 * (R / r)) * ε) * (1 + (4 + 4 * (R / r)) * ε) * R)) := by
  have hident := cell_integral_difference_eq hℒ A hdetA f hint1 hint2
  have h1 : |LinearMap.det A| * |shapeH ℒ A f - shapeG ℒ A f| =
      |(|LinearMap.det A| * (shapeH ℒ A f - shapeG ℒ A f))| := by
    rw [abs_mul, abs_of_nonneg (abs_nonneg (LinearMap.det A))]
  rw [h1, det_mul_shapeH_sub_shapeG A hdetA f, hident]
  exact cell_integral_difference_le (ℒ := ℒ) (A := A) r R ε hr hR0 hε0 hε1 hνe_lt
    hball hcell hlam hA hfmeas hC0 hdiff hbound hVfin

/-- a function with bounded derivative on `[0,B²]` is bounded there. -/
lemma abs_le_of_deriv_le {f : ℝ → ℝ} {B C : ℝ}
    (hdiff : ∀ u ∈ Set.Icc 0 (B ^ 2), DifferentiableAt ℝ f u)
    (hbound : ∀ u ∈ Set.Icc 0 (B ^ 2), ‖deriv f u‖ ≤ C)
    {u : ℝ} (hu : u ∈ Set.Icc 0 (B ^ 2)) :
    |f u| ≤ |f 0| + C * B ^ 2 := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 (B ^ 2) := ⟨le_rfl, sq_nonneg B⟩
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.Icc 0 (B ^ 2))
    (x := 0) (y := u) (C := C) hdiff hbound (convex_Icc _ _) h0 hu
  have h1 : |f u - f 0| ≤ C * B ^ 2 := by
    have h2 : ‖f u - f 0‖ ≤ C * ‖u - 0‖ := hmvt
    rw [sub_zero] at h2
    have hC0 : 0 ≤ C := (norm_nonneg (deriv f 0)).trans (hbound 0 h0)
    have hnorm : ‖u‖ = u := Real.norm_of_nonneg hu.1
    rw [hnorm] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left hu.2 hC0)
  calc
    |f u| = |(f u - f 0) + f 0| := by ring_nf
    _ ≤ |f u - f 0| + |f 0| := abs_add_le _ _
    _ ≤ C * B ^ 2 + |f 0| := by linarith
    _ = |f 0| + C * B ^ 2 := by ring

/-- **Paper Eq. (same_grad), assumption-free form**: `|det A|·|h(A) − g(A)| ≤ O(ε²)`,
with the integrability inputs derived from measurability + boundedness on the bounded cell. -/
theorem det_mul_shapeH_sub_shapeG_le' (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hνe_lt : (4 + 4 * (R / r)) * ε < 1)
    {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    {A : E →ₗ[ℝ] E} (hdetA : LinearMap.det A ≠ 0)
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    {f : ℝ → ℝ} (hfmeas : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hdiff : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), DifferentiableAt ℝ f u)
    (hbound : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), ‖deriv f u‖ ≤ C)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤) :
    |LinearMap.det A| * |shapeH ℒ A f - shapeG ℒ A f| ≤
      (((1 + (4 + 4 * (R / r)) * ε) ^ (Module.finrank ℝ E) -
          (1 - (4 + 4 * (R / r)) * ε) ^ (Module.finrank ℝ E)) *
          (volume : Measure E).real (VC ℒ)) *
        (C * (2 * (2 * R)) * (4 * ((4 + 4 * (R / r)) * ε) * (1 + (4 + 4 * (R / r)) * ε) * R)) := by
  classical
  let Λ : Submodule ℤ E := ℒ.map (A.restrictScalars ℤ)
  let M₀ : ℝ := |f 0| + C * (2 * R) ^ 2
  have hfbound : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), |f u| ≤ M₀ :=
    fun u hu => abs_le_of_deriv_le hdiff hbound hu
  -- measurability of the two integrands
  have hcont_inf : Continuous (fun x : E => Metric.infDist x ((Λ : Submodule ℤ E) : Set E)) :=
    (infDist_lipschitz_one ((Λ : Submodule ℤ E) : Set E)).continuous
  have hmeas1 : Measurable (fun x : E => f (‖x‖ ^ 2)) :=
    hfmeas.comp (continuous_norm.pow 2).measurable
  have hmeas2 : Measurable (fun x : E =>
      f (Metric.infDist x ((Λ : Submodule ℤ E) : Set E) ^ 2)) :=
    hfmeas.comp (hcont_inf.pow 2).measurable
  -- finiteness and the pointwise bounds on the positioned cell
  have hμA : (volume : Measure E) (A '' (VC ℒ)) < ⊤ := by
    rw [Submission.EpsVoronoi.measure_map_cell A (VC ℒ)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((lt_top_iff_ne_top).mpr hVfin)
  have ha0 : 0 ≤ (4 + 4 * (R / r)) * ε := by
    exact mul_nonneg (by nlinarith [div_nonneg hR0 (le_of_lt hr)]) hε0
  have hup : A '' VC ℒ ⊆ (1 + (4 + 4 * (R / r)) * ε) • VC ℒ := by
    exact image_cell_upper_shell (ℒ := ℒ) r R ε hr hR0 hε0 hball hcell A hA
  have hxR : ∀ x ∈ A '' VC ℒ, ‖x‖ ≤ 2 * R := by
    intro x hx
    rcases (Set.mem_smul_set.mp (hup hx)) with ⟨v, hv, hxv⟩
    have hvR : ‖v‖ ≤ R := by
      have hb := Metric.mem_closedBall.mp (hcell hv)
      simpa [dist_eq_norm] using hb
    have hfac : (1 : ℝ) + (4 + 4 * (R / r)) * ε ≤ 2 := by
      have h1 := le_of_lt hνe_lt
      have hq : 0 ≤ R / r := div_nonneg hR0 (le_of_lt hr)
      nlinarith
    have hc0 : (0 : ℝ) ≤ 1 + (4 + 4 * (R / r)) * ε := by
      have hq : 0 ≤ R / r := div_nonneg hR0 (le_of_lt hr)
      nlinarith
    rw [← hxv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    nlinarith [hfac, hvR, norm_nonneg v, hR0]
  have hdR : ∀ x ∈ A '' VC ℒ, Metric.infDist x ((Λ : Submodule ℤ E) : Set E) ≤ 2 * R := by
    intro x hx
    have h0mem : (0 : E) ∈ ((Λ : Submodule ℤ E) : Set E) := Submodule.zero_mem Λ
    calc
      Metric.infDist x ((Λ : Submodule ℤ E) : Set E) ≤ dist x (0 : E) :=
        Metric.infDist_le_dist_of_mem h0mem
      _ = ‖x‖ := by simp [dist_eq_norm]
      _ ≤ 2 * R := hxR x hx
  have hbd1 : ∀ x ∈ A '' VC ℒ, ‖f (‖x‖ ^ 2)‖ ≤ M₀ := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact hfbound _ ⟨sq_nonneg _, pow_le_pow_left₀ (norm_nonneg x) (hxR x hx) 2⟩
  have hbd2 : ∀ x ∈ A '' VC ℒ, ‖f (Metric.infDist x ((Λ : Submodule ℤ E) : Set E) ^ 2)‖ ≤ M₀ := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact hfbound _ ⟨sq_nonneg _, pow_le_pow_left₀ (Metric.infDist_nonneg) (hdR x hx) 2⟩
  have hAmeas : MeasurableSet (A '' (VC ℒ)) := by
    have hK : IsCompact (VC ℒ) :=
      (isCompact_closedBall (0 : E) R).of_isClosed_subset (Submission.Voronoi.voronoi_isClosed ℒ) hcell
    exact ((hK.image (LinearMap.continuous_of_finiteDimensional A))).isClosed.measurableSet
  have hint1 : IntegrableOn (fun x : E => f (‖x‖ ^ 2)) (A '' VC ℒ) :=
    MeasureTheory.IntegrableOn.of_bound hμA (hmeas1.aestronglyMeasurable.restrict) M₀ (by
      rw [MeasureTheory.ae_restrict_iff' hAmeas]
      exact Filter.Eventually.of_forall (fun x hx => hbd1 x hx))
  have hint2 : IntegrableOn (fun x : E =>
      f (Metric.infDist x ((Λ : Submodule ℤ E) : Set E) ^ 2)) (A '' VC ℒ) :=
    MeasureTheory.IntegrableOn.of_bound hμA (hmeas2.aestronglyMeasurable.restrict) M₀ (by
      rw [MeasureTheory.ae_restrict_iff' hAmeas]
      exact Filter.Eventually.of_forall (fun x hx => hbd2 x hx))
  exact det_mul_shapeH_sub_shapeG_le (ℒ := ℒ) r R ε hr hR0 hε0 hε1 hνe_lt hℒ hdetA
    hball hcell hlam hA hfmeas hC0 hdiff hbound hint1 hint2 hVfin
/-- `det ≠ 0` from closeness to the identity. -/
lemma det_ne_zero_of_close (A : E →ₗ[ℝ] E) (ε : ℝ) (hε1 : ε < 1)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖) : LinearMap.det A ≠ 0 := by
  have hker : LinearMap.ker A = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have h := hA x
    rw [hx, zero_sub] at h
    have hle : ‖x‖ ≤ ε * ‖x‖ := by simpa using h
    have hx0 : ‖x‖ = 0 := by
      have h1 : (1 - ε) * ‖x‖ ≤ 0 := by nlinarith [hle]
      have h2 : 0 < 1 - ε := by linarith
      nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hx0
  intro hdet
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot (f := A)).mp hdet hker

/-- The vector bound along the matrix curve with `ε = |t|·K`. -/
lemma curve_lipschitz (M : Matrix (Fin n) (Fin n) ℝ) (K t : ℝ)
    (hK : K = ∑ i : Fin n, ∑ j : Fin n, |M i j|) :
    ∀ w : E, ‖Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M) w - w‖ ≤
      (|t| * K) * ‖w‖ := by
  intro w
  have h := Submission.ShapeDeriv.mvec_one_add_lipschitz (t • M) w
  have hsum : (∑ i : Fin n, ∑ j : Fin n, |(t • M) i j|) = |t| * K := by
    rw [hK]
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]
  rwa [hsum] at h

/-- **The local quadratic bound**: near `t = 0` the difference `h − g` along the matrix curve
is `O(t²)`. -/
lemma shapeH_sub_shapeG_isBigO (r R : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R)
    {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (M : Matrix (Fin n) (Fin n) ℝ)
    {f : ℝ → ℝ} (hfmeas : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hdiff : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), DifferentiableAt ℝ f u)
    (hbound : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), ‖deriv f u‖ ≤ C)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ t : ℝ, |t| ≤ δ →
      |shapeH ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) f -
        shapeG ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) f|
        ≤ C₂ * t ^ 2 := by
  classical
  set K : ℝ := ∑ i : Fin n, ∑ j : Fin n, |M i j| with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  set ν : ℝ := 4 + 4 * (R / r) with hν
  have hν1 : 1 ≤ ν := by
    have hq : 0 ≤ R / r := div_nonneg hR0 (le_of_lt hr)
    rw [hν]; linarith
  have hν0 : 0 < ν := lt_of_lt_of_le one_pos hν1
  set Cn : ℝ := ((n.factorial : ℝ) + n) * 2 ^ n with hCn
  have hCn0 : 0 ≤ Cn := by
    rw [hCn]; positivity
  have hCnpos : 0 < Cn := by
    rw [hCn]; positivity
  have hvol0 : 0 ≤ (volume : Measure E).real (VC ℒ) := measureReal_nonneg
  refine ⟨min (1 / (2 * ν * (K + 1))) (1 / (2 * Cn * (K + 1))), ?_,
    64 * (n : ℝ) * 2 ^ n * ν ^ 2 * C * R ^ 2 * K ^ 2 * (volume : Measure E).real (VC ℒ), ?_, ?_⟩
  · apply lt_min <;> positivity
  · positivity
  · intro t ht
    set A : E →ₗ[ℝ] E := Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M) with hA
    set ε : ℝ := |t| * K with hε
    have hε0 : 0 ≤ ε := by rw [hε]; positivity
    have ht1 : |t| ≤ 1 / (2 * ν * (K + 1)) := le_trans ht (min_le_left _ _)
    have ht2 : |t| ≤ 1 / (2 * Cn * (K + 1)) := le_trans ht (min_le_right _ _)
    have hK1 : 0 < K + 1 := by linarith
    have hνε : ν * ε ≤ 1 / 2 := by
      have h1 : |t| * K ≤ (1 / (2 * ν * (K + 1))) * K :=
        mul_le_mul_of_nonneg_right ht1 hK0
      have h2 : ν * ((1 / (2 * ν * (K + 1))) * K) = K / (2 * (K + 1)) := by
        field_simp
      rw [hε]
      calc ν * (|t| * K) ≤ ν * ((1 / (2 * ν * (K + 1))) * K) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hν0)
        _ = K / (2 * (K + 1)) := h2
        _ ≤ 1 / 2 := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * (K + 1))]
            linarith
    have hε1 : ε ≤ 1 / 2 := le_trans (le_mul_of_one_le_left hε0 hν1) hνε
    have hεlt1 : ε < 1 := by linarith
    have hAlip : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖ := by
      intro w
      have h := curve_lipschitz M K t hK w
      rw [hA, hε]
      exact h
    have hCnε : Cn * ε ≤ 1 / 2 := by
      have h1 : Cn * (|t| * K) ≤ Cn * ((1 / (2 * Cn * (K + 1))) * K) := by
        refine mul_le_mul_of_nonneg_left ?_ hCn0
        exact mul_le_mul_of_nonneg_right ht2 hK0
      have h2 : Cn * ((1 / (2 * Cn * (K + 1))) * K) = K / (2 * (K + 1)) := by
        field_simp
      rw [hε]
      calc Cn * (|t| * K) ≤ Cn * ((1 / (2 * Cn * (K + 1))) * K) := h1
        _ = K / (2 * (K + 1)) := h2
        _ ≤ 1 / 2 := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * (K + 1))]
            linarith
    have hMij : ∀ i j : Fin n, |(t • M) i j| ≤ ε := by
      intro i j
      have h1 : |M i j| ≤ K := by
        rw [hK]
        have hstep1 : |M i j| ≤ ∑ j : Fin n, |M i j| :=
          Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin n => |M i j|)
            (fun b _ => abs_nonneg _) (Finset.mem_univ j)
        have hstep2 : (∑ j : Fin n, |M i j|) ≤ ∑ i : Fin n, ∑ j : Fin n, |M i j| :=
          Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin n => ∑ j : Fin n, |M i j|)
            (fun a _ => Finset.sum_nonneg (fun b _ => abs_nonneg _)) (Finset.mem_univ i)
        exact hstep1.trans hstep2
      rw [hε, Matrix.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg t)
    have hclose1 := det_one_add_close n (t • M) ε hε0 (le_trans hε1 (by norm_num)) hMij
    have hdet1 : |LinearMap.det A - 1| ≤ 1 / 2 := by
      have hd : LinearMap.det A = (1 + t • M).det := by
        rw [hA]
        exact Submission.ShapeDeriv.det_fA _
      rw [hd]
      exact hclose1.trans hCnε
    have hdetA : LinearMap.det A ≠ 0 := det_ne_zero_of_close A ε hεlt1 hAlip
    have hdetge : (1 : ℝ) / 2 ≤ |LinearMap.det A| := by
      have h := (abs_le.mp hdet1).1
      rw [abs_of_nonneg (by linarith)]
      linarith
    -- the paper-shape bound
    have hle := det_mul_shapeH_sub_shapeG_le' (ℒ := ℒ) r R ε hr hR0 hε0 hε1
      (lt_of_le_of_lt hνε (by norm_num)) hℒ hdetA hball hcell hlam hAlip hfmeas hC0 hdiff hbound hVfin
    rw [← hν] at hle
    -- `S ≤ (n)·2^n·(νε)` and `B ≤ 32·ν·C·R²·ε`
    have hfin : Module.finrank ℝ E = n := by simp
    have hS : ((1 + ν * ε) ^ (Module.finrank ℝ E) - (1 - ν * ε) ^ (Module.finrank ℝ E)) ≤
        (n : ℝ) * 2 ^ n * (ν * ε) := by
      have ha0' : 0 ≤ ν * ε := mul_nonneg (le_of_lt hν0) hε0
      have ha1' : ν * ε < 1 := lt_of_le_of_lt hνε (by norm_num)
      have h := shell_pow_lin (Module.finrank ℝ E) (ν * ε) ha0' (le_of_lt ha1')
      simpa [hfin] using h
    have hB : C * (2 * (2 * R)) * (4 * (ν * ε) * (1 + ν * ε) * R) ≤
        32 * ν * C * R ^ 2 * ε := by
      have h2 : 1 + ν * ε ≤ 2 := by linarith
      have h4 : (0 : ℝ) ≤ 4 * (ν * ε) := by positivity
      have hinner : 4 * (ν * ε) * (1 + ν * ε) * R ≤ 8 * (ν * ε) * R := by
        calc 4 * (ν * ε) * (1 + ν * ε) * R = (4 * (ν * ε)) * ((1 + ν * ε) * R) := by ring
          _ ≤ (4 * (ν * ε)) * (2 * R) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hR0) h4
          _ = 8 * (ν * ε) * R := by ring
      calc C * (2 * (2 * R)) * (4 * (ν * ε) * (1 + ν * ε) * R)
          = C * (4 * R) * (4 * (ν * ε) * (1 + ν * ε) * R) := by ring
        _ ≤ C * (4 * R) * (8 * (ν * ε) * R) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = 32 * ν * C * R ^ 2 * ε := by ring
    -- `|h − g| ≤ 2·(S·vol·B)`
    have hS0 : 0 ≤ ((1 + ν * ε) ^ (Module.finrank ℝ E) - (1 - ν * ε) ^ (Module.finrank ℝ E)) := by
      have hνε0 : 0 ≤ ν * ε := mul_nonneg (le_of_lt hν0) hε0
      apply sub_nonneg.mpr
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hB0' : 0 ≤ C * (2 * (2 * R)) * (4 * (ν * ε) * (1 + ν * ε) * R) := by positivity
    have hB0'' : 0 ≤ 32 * ν * C * R ^ 2 * ε := by positivity
    have hX : |shapeH ℒ A f - shapeG ℒ A f| =
        |LinearMap.det A|⁻¹ * (|LinearMap.det A| * |shapeH ℒ A f - shapeG ℒ A f|) := by
      rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hdetA), one_mul]
    have hinv : |LinearMap.det A|⁻¹ ≤ 2 := by
      have h := (inv_le_inv₀ (show (0:ℝ) < |LinearMap.det A| from by linarith [hdetge])
        (by norm_num : (0:ℝ) < 1 / 2)).mpr hdetge
      simpa using h
    have hF2 : |shapeH ℒ A f - shapeG ℒ A f| ≤
        2 * (((1 + ν * ε) ^ (Module.finrank ℝ E) - (1 - ν * ε) ^ (Module.finrank ℝ E)) *
          (volume : Measure E).real (VC ℒ) * (C * (2 * (2 * R)) * (4 * (ν * ε) * (1 + ν * ε) * R))) := by
      rw [hX]
      calc |LinearMap.det A|⁻¹ * (|LinearMap.det A| * |shapeH ℒ A f - shapeG ℒ A f|)
          ≤ |LinearMap.det A|⁻¹ *
              (((1 + ν * ε) ^ (Module.finrank ℝ E) - (1 - ν * ε) ^ (Module.finrank ℝ E)) *
                (volume : Measure E).real (VC ℒ) *
                (C * (2 * (2 * R)) * (4 * (ν * ε) * (1 + ν * ε) * R))) :=
            mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (abs_nonneg _))
        _ ≤ 2 * (((1 + ν * ε) ^ (Module.finrank ℝ E) - (1 - ν * ε) ^ (Module.finrank ℝ E)) *
              (volume : Measure E).real (VC ℒ) *
              (C * (2 * (2 * R)) * (4 * (ν * ε) * (1 + ν * ε) * R))) := by
            refine mul_le_mul_of_nonneg_right hinv ?_
            exact mul_nonneg (mul_nonneg hS0 hvol0) hB0'
    refine hF2.trans ?_
    have hSB : ((1 + ν * ε) ^ (Module.finrank ℝ E) - (1 - ν * ε) ^ (Module.finrank ℝ E)) *
        (volume : Measure E).real (VC ℒ) *
        (C * (2 * (2 * R)) * (4 * (ν * ε) * (1 + ν * ε) * R)) ≤
        ((n : ℝ) * 2 ^ n * (ν * ε)) * (volume : Measure E).real (VC ℒ) * (32 * ν * C * R ^ 2 * ε) := by
      calc ((1 + ν * ε) ^ (Module.finrank ℝ E) - (1 - ν * ε) ^ (Module.finrank ℝ E)) *
            (volume : Measure E).real (VC ℒ) *
            (C * (2 * (2 * R)) * (4 * (ν * ε) * (1 + ν * ε) * R))
          ≤ ((n : ℝ) * 2 ^ n * (ν * ε)) * (volume : Measure E).real (VC ℒ) *
              (C * (2 * (2 * R)) * (4 * (ν * ε) * (1 + ν * ε) * R)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hS hvol0) hB0'
        _ ≤ ((n : ℝ) * 2 ^ n * (ν * ε)) * (volume : Measure E).real (VC ℒ) *
              (32 * ν * C * R ^ 2 * ε) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
    calc 2 * (((1 + ν * ε) ^ (Module.finrank ℝ E) - (1 - ν * ε) ^ (Module.finrank ℝ E)) *
            (volume : Measure E).real (VC ℒ) *
            (C * (2 * (2 * R)) * (4 * (ν * ε) * (1 + ν * ε) * R)))
        ≤ 2 * (((n : ℝ) * 2 ^ n * (ν * ε)) * (volume : Measure E).real (VC ℒ) *
            (32 * ν * C * R ^ 2 * ε)) := mul_le_mul_of_nonneg_left hSB (by norm_num)
      _ = 64 * (n : ℝ) * 2 ^ n * ν ^ 2 * C * R ^ 2 * K ^ 2 *
            (volume : Measure E).real (VC ℒ) * t ^ 2 := by
            rw [hε]
            ring_nf
            rw [sq_abs]
            ring
/-- **`mvec 1 = id`.** -/
lemma mvec_one_eq_id : Submission.ShapeDeriv.mvec (1 : Matrix (Fin n) (Fin n) ℝ) = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  have h := Submission.ShapeDeriv.path_eq (0 : Matrix (Fin n) (Fin n) ℝ) 0 y
  simpa using h

/-- **(c) The `O(‖M‖²)` bound gives `∇g(I) = ∇h(I)`**: along the matrix curve the difference
`h − g` has zero derivative at `t = 0`. -/
theorem shapeH_sub_shapeG_hasDerivAt_zero (r R : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R)
    {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (M : Matrix (Fin n) (Fin n) ℝ)
    {f : ℝ → ℝ} (hfmeas : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hdiff : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), DifferentiableAt ℝ f u)
    (hbound : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), ‖deriv f u‖ ≤ C)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤) :
    HasDerivAt (fun t : ℝ =>
        shapeH ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) f -
        shapeG ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) f) 0 0 := by
  classical
  obtain ⟨δ, hδpos, C₂, hC₂0, hbound2⟩ := shapeH_sub_shapeG_isBigO (ℒ := ℒ) r R hr hR0 hℒ
    hball hcell hlam M hfmeas hC0 hdiff hbound hVfin
  have hF0 : shapeH ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + (0 : ℝ) • M)) f -
      shapeG ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + (0 : ℝ) • M)) f = 0 := by
    have hmap : ℒ.map ((Submission.ShapeDeriv.mvec (1 : Matrix (Fin n) (Fin n) ℝ)).restrictScalars ℤ) = ℒ := by
      rw [mvec_one_eq_id]
      simp
    have hdet : LinearMap.det (Submission.ShapeDeriv.mvec (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
      have h := Submission.ShapeDeriv.det_fA (1 : Matrix (Fin n) (Fin n) ℝ)
      rw [Matrix.det_one] at h
      simpa [Submission.ShapeDeriv.fA] using h
    have himg : Submission.ShapeDeriv.mvec (1 : Matrix (Fin n) (Fin n) ℝ) '' VC ℒ = VC ℒ := by
      rw [mvec_one_eq_id]
      exact Set.image_id _
    simp only [zero_smul, add_zero, shapeH, shapeG, hmap, hdet, himg]
    norm_num
  have hlittle : (fun t : ℝ =>
      shapeH ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) f -
      shapeG ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) f) =o[𝓝 0]
      (fun t : ℝ => t) := by
    refine Asymptotics.IsLittleO.of_bound ?_
    intro c hc
    have hpos : 0 < min δ (c / (C₂ + 1)) := lt_min hδpos (by positivity)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with t ht
    have htδ : |t| ≤ δ := by
      have h : dist t (0 : ℝ) < min δ (c / (C₂ + 1)) := Metric.mem_ball.mp ht
      rw [dist_zero_right, Real.norm_eq_abs] at h
      exact le_trans (le_of_lt h) (min_le_left _ _)
    have htc : |t| ≤ c / (C₂ + 1) := by
      have h : dist t (0 : ℝ) < min δ (c / (C₂ + 1)) := Metric.mem_ball.mp ht
      rw [dist_zero_right, Real.norm_eq_abs] at h
      exact le_trans (le_of_lt h) (min_le_right _ _)
    have h1 := hbound2 t htδ
    have hfac : C₂ * (c / (C₂ + 1)) ≤ c := by
      have h1' : C₂ / (C₂ + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      calc C₂ * (c / (C₂ + 1)) = c * (C₂ / (C₂ + 1)) := by ring
        _ ≤ c * 1 := mul_le_mul_of_nonneg_left h1' (le_of_lt hc)
        _ = c := by ring
    calc ‖shapeH ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) f -
          shapeG ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) f‖
        = |shapeH ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) f -
          shapeG ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) f| :=
          Real.norm_eq_abs _
      _ ≤ C₂ * t ^ 2 := h1
      _ = (C₂ * |t|) * |t| := by rw [← sq_abs]; ring
      _ ≤ (C₂ * (c / (C₂ + 1))) * |t| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htc hC₂0) (abs_nonneg t)
      _ ≤ c * |t| := mul_le_mul_of_nonneg_right hfac (abs_nonneg t)
      _ = c * ‖t‖ := by rw [Real.norm_eq_abs]
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hgoal : (fun h : ℝ =>
        shapeH ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + (0 + h) • M)) f -
        shapeG ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + (0 + h) • M)) f -
        (shapeH ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + (0 : ℝ) • M)) f -
          shapeG ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + (0 : ℝ) • M)) f) -
        h • (0 : ℝ)) =
      (fun t : ℝ =>
        shapeH ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) f -
        shapeG ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) f) := by
    funext h
    rw [hF0]
    simp
  rw [hgoal]
  exact hlittle
/-- the Gaussian integrand `f₁ u = e^{−π u}`, so that `f₁ (‖x‖²) = e^{−π‖x‖²}`. -/
noncomputable def fGauss : ℝ → ℝ := fun u => rexp (-Real.pi * u)

lemma fGauss_apply (u : ℝ) : fGauss u = rexp (-Real.pi * u) := rfl

/-- **Change of variables on the curve**: on the matrix curve (with `det ≠ 0`), the smooth-side
functional `h` is the plain Gaussian integral over the fixed Voronoi cell. -/
lemma shapeH_curve_eq (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hdet : ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M).det ≠ 0)
    {ℒ : Submodule ℤ E} :
    shapeH ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) fGauss
      = ∫ y in VC ℒ, rexp (-Real.pi * ‖Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M) y‖ ^ 2) := by
  have h := Submission.ShapeDeriv.integral_image_fA (A := (1 : Matrix (Fin n) (Fin n) ℝ) + t • M) hdet
    (fun x : E => rexp (-Real.pi * ‖x‖ ^ 2)) (VC ℒ)
  simp only [Submission.ShapeDeriv.fA] at h
  have hdetL : LinearMap.det (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) =
      ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M).det := Submission.ShapeDeriv.det_fA _
  unfold shapeH fGauss
  rw [hdetL, h]
  rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hdet), one_mul]

/-- **S1 along the curve**: the derivative of the smooth-side functional `h` at `t = 0` is the
Session-108 shape-derivative value (paper `clm:grad_h`). -/
theorem shapeH_curve_hasDerivAt (M : Matrix (Fin n) (Fin n) ℝ) {ℒ : Submodule ℤ E}
    [DiscreteTopology ℒ] :
    HasDerivAt (fun t : ℝ => shapeH ℒ
        (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) fGauss)
      (-2 * Real.pi * ∫ y in VC ℒ, rexp (-Real.pi * ‖y‖ ^ 2) *
        inner ℝ y (Submission.ShapeDeriv.mvec M y)) 0 := by
  classical
  set K : ℝ := ∑ i : Fin n, ∑ j : Fin n, |M i j| with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hδpos : 0 < 1 / (K + 1) := by positivity
  have hS1 := Submission.ShapeDeriv.shapeDeriv_mvec M (VC ℒ) (Submission.Voronoi.voronoi_measurable ℒ)
  refine hS1.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδpos] with t ht
  have htabs : |t| ≤ 1 / (K + 1) := by
    have h : dist t (0 : ℝ) < 1 / (K + 1) := Metric.mem_ball.mp ht
    simpa [dist_zero_right, Real.norm_eq_abs] using le_of_lt h
  have hε : |t| * K < 1 := by
    have h1 : |t| * K ≤ (1 / (K + 1)) * K := mul_le_mul_of_nonneg_right htabs hK0
    have h2 : (1 / (K + 1)) * K < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one (by positivity : (0:ℝ) < K + 1)]
      linarith
    linarith
  have hdetne : LinearMap.det (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) ≠ 0 :=
    det_ne_zero_of_close _ (|t| * K) hε (curve_lipschitz M K t hK)
  have hdetmv : ∀ A : Matrix (Fin n) (Fin n) ℝ,
      LinearMap.det (Submission.ShapeDeriv.mvec A) = A.det := by
    intro A
    simpa [Submission.ShapeDeriv.fA] using Submission.ShapeDeriv.det_fA A
  have hdetne' : ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M).det ≠ 0 := by
    intro hzero
    exact hdetne (by rw [hdetmv]; exact hzero)
  exact shapeH_curve_eq (ℒ := ℒ) M t hdetne'

/-- **(S1 into the local-min step)**: the derivative of the CELL-side functional
`γ₁(V(A·ℒ))` along the matrix curve equals the S1 shape-derivative value — this is the input
the local-min-over-det-one argument consumes (via Session-113's `∇g(I) = ∇h(I)`). -/
theorem shapeG_curve_hasDerivAt (r R : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R)
    {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤) :
    HasDerivAt (fun t : ℝ => shapeG ℒ
        (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) fGauss)
      (-2 * Real.pi * ∫ y in VC ℒ, rexp (-Real.pi * ‖y‖ ^ 2) *
        inner ℝ y (Submission.ShapeDeriv.mvec M y)) 0 := by
  have hH := shapeH_curve_hasDerivAt (ℒ := ℒ) M
  have hfmeas : Measurable fGauss := by
    rw [show fGauss = fun u : ℝ => rexp (-Real.pi * u) from rfl]
    exact Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)
  have hdiff : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), DifferentiableAt ℝ fGauss u := by
    intro u _
    rw [show fGauss = fun u : ℝ => rexp (-Real.pi * u) from rfl]
    exact ((Real.hasDerivAt_exp (-Real.pi * u)).comp u (hasDerivAt_const_mul (-Real.pi))).differentiableAt
  have hderiv_val : ∀ u : ℝ, deriv fGauss u = -Real.pi * rexp (-Real.pi * u) := by
    intro u
    have h2 := (Real.hasDerivAt_exp (-Real.pi * u)).comp u (hasDerivAt_const_mul (-Real.pi))
    have h3 := h2.deriv
    rw [show fGauss = fun u : ℝ => rexp (-Real.pi * u) from rfl]
    simpa [mul_comm] using h3
  have hbound : ∀ u ∈ Set.Icc 0 ((2 * R) ^ 2), ‖deriv fGauss u‖ ≤ Real.pi := by
    intro u hu
    rw [hderiv_val u, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (le_of_lt Real.pi_pos)]
    have hexp0 : 0 ≤ rexp (-Real.pi * u) := le_of_lt (Real.exp_pos _)
    rw [abs_of_nonneg hexp0]
    have hexp : rexp (-Real.pi * u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := mul_nonneg Real.pi_pos.le hu.1
      linarith
    nlinarith [Real.pi_pos]
  have hdiffG := shapeH_sub_shapeG_hasDerivAt_zero (ℒ := ℒ) r R hr hR0 hℒ hball hcell hlam M
    hfmeas Real.pi_pos.le hdiff hbound hVfin
  have hsub := hH.sub hdiffG
  have hfun : ((fun t : ℝ => shapeH ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) fGauss) -
      (fun t : ℝ => shapeH ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) fGauss -
        shapeG ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) fGauss))
      = (fun t : ℝ => shapeG ℒ (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) fGauss) := by
    funext t
    simp [sub_sub_cancel]
  rw [hfun] at hsub
  simpa using hsub

/-- **S3 form**: the cell-side derivative is `−2π · Σᵢⱼ Mᵢⱼ · (second moment of the Gaussian
over `V`)` — the matrix pairing that the isotropy argument (S2) consumes. -/
theorem shapeG_curve_hasDerivAt_trace (r R : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R)
    {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hVfin : (volume : Measure E) (VC ℒ) ≠ ⊤) :
    HasDerivAt (fun t : ℝ => shapeG ℒ
        (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + t • M)) fGauss)
      (-2 * Real.pi * ∑ i : Fin n, ∑ j : Fin n, M i j *
        Submission.ShapeDeriv.secondMoment (VC ℒ) i j) 0 := by
  have hmain := shapeG_curve_hasDerivAt (ℒ := ℒ) r R hr hR0 hℒ hball hcell hlam M hVfin
  have htp := Submission.ShapeDeriv.trace_pairing M (VC ℒ) (Submission.Voronoi.voronoi_measurable ℒ)
  rw [htp] at hmain
  simpa using hmain
end Submission.SameGrad