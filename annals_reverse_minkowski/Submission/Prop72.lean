import Mathlib
import Submission.MainStable
import Submission.StableBoundary
import Submission.StableMinimizer
import Submission.StableOpen
import Submission.IsotropicMass
import Submission.CoveringRadius
import Submission.Poisson

open Module Real Matrix MeasureTheory
open Submission.QuotientLattice
open Submission.StableLattices
open scoped Real BigOperators Pointwise
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# Prop 7.2 (paper): `gamma_stable` — Voronoi Gaussian mass of stable lattices

This module sits ABOVE `MainStable` (base cases + `t`), `StableBoundary` (boundary-pair
interface) and `StableMinimizer` (existence of a global γ-minimizer over stable lattices),
and carries the rank-`m ≥ 2` induction step `gamma_stable_of_two_le` of paper Prop 7.2:

> for a stable full-rank lattice `ℒ` in ambient dimension `m`, `γ_{1/t_m}(V(ℒ)) ≥ 2/3`.

The proof follows the paper: take a global minimizer `ℳ` of `γ_{1/t_m}(V(·))` over the
(compact) set of stable full-rank lattices.  If `ℳ` has a strict primitive det-one
sublattice (the *boundary* case), the quotient is automatically stable
(`StableBoundary.stable_quotLattice_of_det_one`) and `boundary_gamma_of_primitive_det_one`
closes the case from the per-rank induction hypothesis + fundamental-product factorization
+ Gaussian concentration + the log claim.  Otherwise (`interior_minimizer_gamma_of_stable`,
the single remaining black box) the paper's §5–§6 machinery (isotropic Gaussian position,
Bobkov's maximum-mass theorem, ell–ell\*, Urysohn/Jensen/Markov) gives `γ ≥ 2/3`.
The global-minimizer property then spreads the bound to every stable lattice `ℒ`.

`RM_stable` and `theorem_1_2_large` complete the paper Prop 7.2 / Theorem 1.2 `n ≥ 2`
branch (moved here from `MainStable`, which now contains only the `m = 0, 1` bases and
the parameter arithmetic).
-/

namespace Submission.MainStable

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- **Interior branch (black box, paper §5–§6).**  A stable full-rank lattice `ℳ` of
rank `m ≥ 2` which (i) is a global minimum of `γ_{1/t_m}(V(·))` over all stable full-rank
lattices, and (ii) has no strict primitive determinant-one sublattice, has Voronoi Gaussian
mass `≥ 2/3` at `1/t m`.

Paper route: by the stable-boundary characterization (Prop. 4.1(vi)), (ii) means `ℳ` is an
*interior* point of the stable set, hence a local minimum over the determinant-one
manifold; `minima_have_mass` (paper Thm. 6.3: `same_grad_VL` + `thm:isotropic_mass`)
yields `γ ≥ 2/3`. -/
theorem interior_minimizer_gamma_of_stable (m : ℕ) (hm : 2 ≤ m)
    (ℳ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) [DiscreteTopology ℳ]
    (hStM : Submission.StableLattices.Stable ℳ) (hfinM : Module.finrank ℤ ℳ = m)
    (hmin : ∀ (ℒ₀ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) (_hDT2 : DiscreteTopology ℒ₀),
      Submission.StableLattices.Stable ℒ₀ → Module.finrank ℤ ℒ₀ = m →
      Submission.GaussianMeasure.gammaMass (1 / t m) (Submission.Voronoi.voronoi ℳ) ≤
        Submission.GaussianMeasure.gammaMass (1 / t m) (Submission.Voronoi.voronoi ℒ₀))
    (hno : ¬ ∃ (ℒ' : Submodule ℤ (EuclideanSpace ℝ (Fin m))) (_hd : DiscreteTopology ℒ'),
      ℒ' ≤ ℳ ∧ Submission.QuotientLattice.Primitive ℒ' ℳ ∧
      ReverseMinkowski.determinant ℒ' = 1 ∧ 1 ≤ Module.finrank ℤ ℒ' ∧
      Module.finrank ℤ ℒ' < m)
    (ih : ∀ (d : ℕ), d < m → ∀ (ℒd : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
      [DiscreteTopology ℒd], Submission.StableLattices.Stable ℒd →
      Module.finrank ℤ ℒd = d →
      (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / t d)
        (Submission.Voronoi.voronoi ℒd)) :
    (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / t m)
      (Submission.Voronoi.voronoi ℳ) := by

  classical
  set s : ℝ := 1 / t m with hsdef
  have hs : 0 < s := by rw [hsdef]; exact inv_t_pos m
  have hℒ : IsZLattice ℝ ℳ := isZLattice_of_finrank (n := m) ℳ hfinM
  let b : Basis (Fin m) ℤ ℳ :=
    (Module.finBasis ℤ ℳ).reindex (Equiv.cast (congrArg Fin hfinM))
  let B₀ : Matrix (Fin m) (Fin m) ℝ := Submission.LatticeParam.basisMatrix b
  have hdetB0 : B₀.det ≠ 0 := Submission.LatticeParam.basisMatrix_det_ne_zero b
  have hlamB : Submission.LatticeParam.latticeOfMatrix B₀ = ℳ :=
    Submission.LatticeParam.latticeOfMatrix_basisMatrix b
  haveI hDTL : DiscreteTopology (Submission.LatticeParam.latticeOfMatrix B₀) := by
    rw [hlamB]; infer_instance
  have habsB0 : |B₀.det| = 1 := by
    have h1 := Submission.StableClosure.det_latticeOfMatrix_eq_abs_det B₀ hdetB0
    have h2 := Submission.Uncrossing.det_eq_of_eq
      (L₁ := Submission.LatticeParam.latticeOfMatrix B₀) (L₂ := ℳ) hlamB
    rw [← h1, h2, Submission.StableLattices.det_eq_one_of_stable hStM]
  have hStB₀ : Submission.StableLattices.Stable (Submission.LatticeParam.latticeOfMatrix B₀) :=
    Submission.Filtration.stable_of_submodule_eq hlamB hStM
  have hnoB₀ : Submission.StableOpen.NoDetOneSublattice
      (Submission.LatticeParam.latticeOfMatrix B₀) := by
    intro h
    apply hno
    rcases h with ⟨ℒ', hd, hle, hp, hdet, hr1, hrm⟩
    refine ⟨ℒ', hd, ?_, ?_, hdet, hr1, hrm⟩
    · rwa [hlamB] at hle
    · intro x
      rw [Primitive] at hp
      rw [hp x, hlamB]
  have hminB₀ : ∀ (ℒ₀ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) (_hd : DiscreteTopology ℒ₀),
      Submission.StableLattices.Stable ℒ₀ → Module.finrank ℤ ℒ₀ = m →
      Submission.GaussianMeasure.gammaMass s
        (Submission.Voronoi.voronoi (Submission.LatticeParam.latticeOfMatrix B₀)) ≤
        Submission.GaussianMeasure.gammaMass s (Submission.Voronoi.voronoi ℒ₀) := by
    intro ℒ₀ hd hSt0 hfin0
    have hgoal := hmin ℒ₀ hd hSt0 hfin0
    rw [Submission.Intrinsic.voronoi_congr _ _ hlamB]
    exact hgoal
  rcases Submission.StableOpen.local_min_gamma_of_no_det_one (m := m) s hs B₀ hm hdetB0 habsB0
    hStB₀ hnoB₀ hminB₀ with ⟨δ₀, hδ₀pos, hbox₀⟩
  rcases Submission.IsotropicMass.mat_mul_near B₀ δ₀ hδ₀pos with ⟨δ, hδpos, hnear⟩
  have hloc : ∃ δ' : ℝ, 0 < δ' ∧ ∀ (A : Matrix (Fin m) (Fin m) ℝ), A.det ≠ 0 → |A.det| = 1 →
      (∀ j i : Fin m, |A j i - (1 : Matrix (Fin m) (Fin m) ℝ) j i| < δ') →
      Submission.GaussianMeasure.gammaMass s (Submission.Voronoi.voronoi ℳ) ≤
        Submission.GaussianMeasure.gammaMass s
          (Submission.Voronoi.voronoi (Submodule.map ((Submission.ShapeDeriv.mvec A).restrictScalars ℤ) ℳ)) := by
    refine ⟨δ, hδpos, ?_⟩
    intro A hdetA habsA hboxA
    have hdetAB : (A * B₀).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hdetA hdetB0
    have habsAB : |(A * B₀).det| = 1 := by
      rw [Matrix.det_mul, abs_mul, habsA, habsB0, one_mul]
    have hboxAB : ∀ j i : Fin m, |(A * B₀) j i - B₀ j i| < δ₀ := fun j i => hnear A hboxA j i
    have hloc0 := hbox₀ (A * B₀) hdetAB habsAB hboxAB
    have h1 : Submission.Voronoi.voronoi (Submission.LatticeParam.latticeOfMatrix B₀)
        = Submission.Voronoi.voronoi ℳ := Submission.Intrinsic.voronoi_congr _ _ hlamB
    have h2 : Submission.LatticeParam.latticeOfMatrix (A * B₀)
        = Submodule.map ((Submission.ShapeDeriv.mvec A).restrictScalars ℤ) ℳ := by
      rw [Submission.IsotropicMass.latticeOfMatrix_mul, hlamB]
    have h3 : Submission.Voronoi.voronoi (Submission.LatticeParam.latticeOfMatrix (A * B₀))
        = Submission.Voronoi.voronoi (Submodule.map ((Submission.ShapeDeriv.mvec A).restrictScalars ℤ) ℳ) :=
      Submission.Intrinsic.voronoi_congr _ _ h2
    rw [h1, h3] at hloc0
    exact hloc0
  -- geometric hypotheses for V ℳ
  have hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (1 / 2) ⊆ Submission.Voronoi.voronoi ℳ :=
    Submission.StableLattices.half_ball_subset_voronoi_of_stable hStM
  have hlam : ∀ z : ℳ, z ≠ 0 → (1 / 2 : ℝ) ≤ ‖(z : EuclideanSpace ℝ (Fin m))‖ := by
    intro z hz
    have h1 := Submission.StableLattices.norm_ge_one_of_stable hStM z hz
    linarith
  have hVfin : volume (Submission.Voronoi.voronoi ℳ) ≠ ⊤ := by
    intro htop
    have hre : volume.real (Submission.Voronoi.voronoi ℳ) = 1 := by
      rw [Submission.Poisson.voronoi_volume_eq_det (ℒ := ℳ) hℒ,
        Submission.StableLattices.det_eq_one_of_stable hStM]
    rw [Measure.real, htop] at hre
    simp at hre
  let R : ℝ := ∑ i : Fin m, ‖((b i : ℳ) : EuclideanSpace ℝ (Fin m))‖
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hcell : Submission.Voronoi.voronoi ℳ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R := by
    dsimp [R]
    exact Submission.CoveringRadius.voronoi_subset_closedBall_basis ℳ hℒ b
  rcases Submission.Isotropic.secondMoment_scalar_of_local_min_scaled (ℒ := ℳ) hℒ s hs
    (1 / 2) R (by norm_num) hR0 hball hcell hlam hVfin hloc hm with ⟨α, hα⟩
  have hIso : ∃ α' : ℝ, ∀ i j : Fin m,
      Submission.ShapeDeriv.secondMoment ((1 / s) • Submission.Voronoi.voronoi ℳ) i j
        = α' * (if i = j then 1 else 0) := by
    refine ⟨α, ?_⟩
    intro i j
    have h := hα i j
    rw [Submission.Isotropic.voronoi_smulLattice (1 / s) (by positivity) ℳ] at h
    exact h
  have hvol : volume.real (Submission.Voronoi.voronoi ℳ) = 1 := by
    rw [Submission.Poisson.voronoi_volume_eq_det (ℒ := ℳ) hℒ,
      Submission.StableLattices.det_eq_one_of_stable hStM]
  have h0K : (0 : EuclideanSpace ℝ (Fin m)) ∈ Submission.Voronoi.voronoi ℳ := by
    apply hball
    rw [Metric.mem_closedBall, dist_self]
    norm_num
  have hInt : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior (Submission.Voronoi.voronoi ℳ) := by
    have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (1 / 2)
        ⊆ Submission.Voronoi.voronoi ℳ := fun x hx => hball (Metric.ball_subset_closedBall hx)
    have hii : Metric.ball (0 : EuclideanSpace ℝ (Fin m)) (1 / 2)
        ⊆ interior (Submission.Voronoi.voronoi ℳ) :=
      interior_maximal hsub Metric.isOpen_ball
    exact hii (by rw [Metric.mem_ball, dist_self]; norm_num)
  have hcpt : IsCompact (Submission.Voronoi.voronoi ℳ) := by
    refine Metric.isCompact_of_isClosed_isBounded (Submission.Voronoi.voronoi_isClosed ℳ) ?_
    exact Metric.isBounded_closedBall.subset hcell
  have hsymm : (-(Submission.Voronoi.voronoi ℳ) : Set (EuclideanSpace ℝ (Fin m))) = Submission.Voronoi.voronoi ℳ := by
    ext x
    rw [Set.mem_neg]
    constructor
    · intro hx; simpa using Submission.Voronoi.voronoi_neg_mem hx
    · intro hx; exact Submission.Voronoi.voronoi_neg_mem hx
  exact Submission.IsotropicMass.isotropic_mass (m := m) (by omega)
    (K := Submission.Voronoi.voronoi ℳ)
    (Submission.Voronoi.voronoi_convex ℳ) hcpt hsymm h0K hInt hvol
    s hs (by rw [hsdef]) hIso



/-- **Induction step of `gamma_stable` (ranks `m ≥ 2`).** — the analytic core of the
paper (§3–§7): a global-minimum argument over the (compact, by Mahler) set of stable
lattices, split into an interior case (isotropic Gaussian position, paper §6) and a
boundary case (Voronoi fundamental-product factorization §5 + Gaussian concentration).

Carries the strong-induction hypothesis `ih`: the rank-`m` case may invoke `gamma_stable`
at every rank `d < m` on any full-rank stable lattice `ℒd ≤ EuclideanSpace ℝ (Fin d)`
(in the boundary case these are the rank-`d` stable sublattice and its stable quotient,
transported to their own ambient spaces via the [C]-block isometric identifications). -/
theorem gamma_stable_of_two_le (m : ℕ) (hm : 2 ≤ m)
    (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) [DiscreteTopology ℒ]
    (hSt : Submission.StableLattices.Stable ℒ) (hfin : Module.finrank ℤ ℒ = m)
    (ih : ∀ (d : ℕ), d < m → ∀ (ℒd : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
      [DiscreteTopology ℒd], Submission.StableLattices.Stable ℒd →
      Module.finrank ℤ ℒd = d →
      (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / t d)
        (Submission.Voronoi.voronoi ℒd)) :
    (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / t m)
      (Submission.Voronoi.voronoi ℒ) := by
  classical
  have hne : ∃ (ℳ : Submodule ℤ (EuclideanSpace ℝ (Fin m))) (_hDT : DiscreteTopology ℳ),
      @Submission.StableLattices.Stable m ℳ _hDT ∧ Module.finrank ℤ ℳ = m := by
    refine ⟨ℒ, ?_, hSt, hfin⟩
    exact ‹DiscreteTopology ℒ›
  rcases Submission.StableMinimizer.exists_stable_gamma_minimizer (m := m) (1 / t m)
    (inv_t_pos m) hne with ⟨ℳ, hDTM, hStM, hfinM, hmin⟩
  haveI : DiscreteTopology ℳ := hDTM
  have hγM : (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / t m)
      (Submission.Voronoi.voronoi ℳ) := by
    by_cases hb : ∃ (ℒ' : Submodule ℤ (EuclideanSpace ℝ (Fin m))) (_hd : DiscreteTopology ℒ'),
        ℒ' ≤ ℳ ∧ Submission.QuotientLattice.Primitive ℒ' ℳ ∧
        ReverseMinkowski.determinant ℒ' = 1 ∧ 1 ≤ Module.finrank ℤ ℒ' ∧
        Module.finrank ℤ ℒ' < m
    · rcases hb with ⟨ℒ', hdL', hle, hp, hdet, hr1, hrm⟩
      haveI : DiscreteTopology ℒ' := hdL'
      exact Submission.StableBoundary.boundary_gamma_of_primitive_det_one (m := m) hm
        ℳ hStM hfinM ℒ' hle hp hdet hr1 hrm ih
    · exact interior_minimizer_gamma_of_stable m hm ℳ hStM hfinM
        (fun ℒ₀ _hDT0 hSt0 hfin0 => hmin ℒ₀ _hDT0 hSt0 hfin0) hb ih
  exact le_trans hγM (hmin ℒ ‹DiscreteTopology ℒ› hSt hfin)

/--
**Voronoi-γ statement (paper §7.2, the analytic core).** For a stable full-rank
lattice `ℒ` in ambient dimension `m`, the Gaussian mass of its Voronoi cell at
parameter `1/(10 (log m + 2))` is at least `2/3`.

Together with the `rho_gamma` identity (VoronoiMeasure) this gives Prop RM_stable.
The base cases `m = 0` (trivial space) and `m = 1` (one-dimensional ball integral)
are proved in `MainStable`; the ranks `m ≥ 2` are the induction step of the paper
(interior = isotropic position / boundary = fundamental-product factorization).
-/
theorem gamma_stable : ∀ (m : ℕ) (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin m)))
    [DiscreteTopology ℒ], Submission.StableLattices.Stable ℒ →
    Module.finrank ℤ ℒ = m →
    (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / t m)
      (Submission.Voronoi.voronoi ℒ) := by
  classical
  intro m ℒ _hDT hSt hfin
  -- The theorem is proved by STRONG INDUCTION on the rank m: the rank-m case may invoke the
  -- statement at every smaller rank d (boundary factors ℒ', ℒ/ℒ' of the paper's Prop 7.2),
  -- transported to their own ambient space E_d via the [C]-block identifications.
  let P : ℕ → Prop := fun mm : ℕ =>
    ∀ (ℒm : Submodule ℤ (EuclideanSpace ℝ (Fin mm))) [DiscreteTopology ℒm],
      Submission.StableLattices.Stable ℒm → Module.finrank ℤ ℒm = mm →
      (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / t mm)
        (Submission.Voronoi.voronoi ℒm)
  have hP : P m := by
    refine Nat.strong_induction_on m ?_
    intro mm hmm
    intro ℒm _hDTm hStm hfinm
    by_cases hm0 : mm = 0
    · subst mm
      exact gamma_stable_zero ℒm hStm hfinm
    · by_cases hm1 : mm = 1
      · subst mm
        exact gamma_stable_one ℒm hStm
      · have hm2 : 2 ≤ mm := by omega
        exact gamma_stable_of_two_le mm hm2 ℒm hStm hfinm
          (fun d hd ℒd _hDTd hStd hfind => hmm d hd ℒd hStd hfind)
  exact hP ℒ hSt hfin

/--
**Prop RM_stable (paper §7.2).** For a stable full-rank lattice in ambient dimension `m`,
the Gaussian mass at `s = 1/(10 (log m + 2))` is at most `3/2`.

Follows from `gamma_stable` via the `rho_gamma` bridge.
-/
theorem RM_stable (m : ℕ) (ℒ : Submodule ℤ (EuclideanSpace ℝ (Fin m)))
    [DiscreteTopology ℒ] (hSt : Submission.StableLattices.Stable ℒ)
    (hfin : Module.finrank ℤ ℒ = m) :
    mass (1 / t m) ℒ ≤ 3 / 2 := by
  have hγ : (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / t m)
      (Submission.Voronoi.voronoi ℒ) := by
    exact gamma_stable m ℒ hSt hfin
  haveI hℒ : IsZLattice ℝ ℒ := isZLattice_of_finrank (n := m) ℒ hfin
  dsimp [t]
  exact Submission.VoronoiMeasure.rho_le_three_halves_of_gamma_ge (ℒ := ℒ) hℒ
    (1 / (10 * (Real.log (m : ℝ) + 2))) (inv_t_pos m) hγ

/-- The `n ≥ 2` branch of Theorem 1.2, assembled from the [B] reduction and RM_stable.
Here `n` is the ambient dimension (any `n`, not only `≥ 2`). -/
theorem theorem_1_2_large (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ)
    (h : ∀ ℒ' (_h : ℒ' ≤ ℒ) [DiscreteTopology ℒ'], ReverseMinkowski.determinant ℒ' ≥ 1) :
    ReverseMinkowski.ρ (1 / t n) ℒ ≤ 3 / 2 := by
  classical
  let s : ℝ := 1 / t n
  have hs : 0 < s := by
    dsimp [s]
    exact inv_t_pos n
  have hdet : ∀ (M : Submodule ℤ E), [DiscreteTopology M] → M ≤ ℒ →
      (1 : ℝ) ≤ ReverseMinkowski.determinant M := by
    intro M _hMd hle
    exact h M hle
  rcases Submission.Filtration.canonical_mass_bound (ℒ := ℒ) hℒ hdet s hs with
    ⟨S, hSd, hSt, hfin, hmass⟩
  haveI : DiscreteTopology S := hSd
  have hS : mass s S ≤ 3 / 2 := by
    dsimp [s]
    exact RM_stable n S hSt hfin
  rw [Submission.VoronoiMeasure.rho_eq_ambient_sum]
  change mass s ℒ ≤ 3 / 2
  exact le_trans hmass hS

end Submission.MainStable
