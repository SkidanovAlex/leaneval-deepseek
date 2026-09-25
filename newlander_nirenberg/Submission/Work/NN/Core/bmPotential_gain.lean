import Mathlib
import Submission.Work.NN.Core.bmPot_riesz_Ck
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv
import Submission.Work.NN.Core.bmPotentialHolderContinuous
import Submission.Work.NN.Core.bmPotential_differentiableAt_holder
import Submission.Work.NN.Core.bmPot_repr
import Submission.Work.NN.Core.czHolderEstimate
import Submission.Work.CR.Flat.Cauchy.dbar_interior_oneshot
import Submission.Work.CR.Flat.Cauchy.bmPotential_solves_dbar
import Submission.Work.NN.Core.holderNorm_le_of_tendsto
import Submission.Work.CR.Flat.Cauchy.iteratedFDeriv_succ_of_slice_bounds
import Submission.Work.NN.Core.diff_iter_of_slice_bounds
import Submission.Work.NN.Core.iteratedFDeriv_apply_eq_zero_of_vanishing
import Submission.Work.NN.Core.continuousOn_iterFDerivWithin_of_holderSeminorm

namespace Work.NN.Core

set_option maxHeartbeats 1600000

open scoped NNReal ENNReal Topology ContDiff
open Set Filter
open Work.CR.Flat
open Work.CR.Flat.Cauchy

noncomputable section

/-- Auxiliary lemma (also proved in `Submission.Work.NN.Core.diff_iter_of_slice_bounds`):
the `k`-th iterated derivative of `F` is differentiable on the convex open set `Ω` as soon as all
its slices `y ↦ D^k F y u` are differentiable there with derivatives uniformly bounded by
`K · ∏ ‖u i‖` and uniformly `α`-Hölder with the same constant. -/
theorem diffIter_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {F : E → ℂ}
    {Ω : Set E} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω) {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hdiff : ∀ u : Fin k → E, ∀ z ∈ Ω, DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ k F y u) z)
    (hbound : ∀ u : Fin k → E, ∀ z ∈ Ω,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z‖ ≤ K * ∏ i, ‖u i‖)
    (hholder : ∀ u : Fin k → E, ∀ z ∈ Ω, ∀ z' ∈ Ω,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z
        - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z'‖
        ≤ K * (∏ i, ‖u i‖) * ‖z - z'‖ ^ α) :
    ∀ z ∈ Ω, DifferentiableAt ℝ (iteratedFDeriv ℝ k F) z :=
  diff_iter_of_slice_bounds hΩopen hΩconv hα hK hdiff hbound hholder

/-- Auxiliary lemma (also proved in `Submission.Work.NN.Core.iteratedFDeriv_apply_eq_zero_of_vanishing`):
all the derivatives of a `C^m` function vanishing off the polydisc of multiradii `ρ` vanish there
as well. -/
theorem vanishing_aux {n : ℕ} {ρ : Fin n → ℝ} {f : (Fin n → ℂ) → ℂ} {m : ℕ}
    (hf : ContDiff ℝ m f) (hsub : ∀ z, (∃ i, ρ i ≤ ‖z i‖) → f z = 0) :
    ∀ z, (∃ i, ρ i ≤ ‖z i‖) → ∀ v : Fin m → Fin n → ℂ, iteratedFDeriv ℝ m f z v = 0 :=
  iteratedFDeriv_apply_eq_zero_of_vanishing hf hsub

/-- Auxiliary lemma (also proved in
`Submission.Work.NN.Core.continuousOn_iterFDerivWithin_of_holderSeminorm`): a finite
Hölder seminorm bound for the `m`-th derivative on `Ω` makes that derivative continuous on `Ω`. -/
theorem continuousOn_aux {n : ℕ} {m : ℕ} {α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C)
    {f : (Fin n → ℂ) → ℂ} {Ω : Set (Fin n → ℂ)}
    (h : holderSeminorm m α f Ω ≤ ENNReal.ofReal C) :
    ContinuousOn (iteratedFDerivWithin ℝ m f Ω) Ω :=
  continuousOn_iterFDerivWithin_of_holderSeminorm hα hC h

/-- **The Bochner–Martinelli potential gains exactly one derivative, with a `C^{N+1,α}`
estimate and a `C^{N+1}` regularity statement.**

For `0 < α < 1`, positive multiradii `ρ` and every `N` there is `C > 0` such that every family
`g` of class `C^N` with compactly supported components which vanish off the open polydisc
`polydisc 0 ρ` and have finite `C^{N,α}`-norm satisfies: the Bochner–Martinelli potential
`bmPotential g` is of class `C^{N+1}` on `polydisc 0 ρ` and

`‖bmPotential g‖_{C^{N+1,α}(polydisc 0 ρ)} ≤ C · Σ_j ‖g_j‖_{C^{N,α}(ℂⁿ)}`.

The `C^{N+1,α}` estimate is the Schauder estimate `Work.NN.Core.bmPot_riesz_Ck`; the
differentiability at the top order (which turns the estimate into genuine `C^{N+1}` regularity) is
obtained by representing the slices of `D^N (bmPotential g)` as potentials of the derived data
`D^N g · v` — these again vanish off `polydisc 0 ρ` and have finite `C^{0,α}`-norm, so their
potentials are differentiable with uniformly bounded and uniformly Hölder continuous first
derivatives; the criterion `diffIter_aux` then gives differentiability of the
multilinear-map-valued function `D^N (bmPotential g)`. -/
theorem bmPotential_gain {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, ContDiff ℝ N (g j)) → (∀ j, HasCompactSupport (g j)) →
      (∀ j, Work.CR.Flat.holderNorm N α (g j) Set.univ < ⊤) →
      (∀ j z, (∃ i, ρ i ≤ ‖z i‖) → g j z = 0) →
      ContDiffOn ℝ (((N + 1 : ℕ)) : ℕ∞) (Work.CR.Flat.Cauchy.bmPotential g)
          (Work.CR.Flat.polydisc 0 ρ) ∧
      Work.CR.Flat.holderNorm (N + 1) α (Work.CR.Flat.Cauchy.bmPotential g)
          (Work.CR.Flat.polydisc 0 ρ)
        ≤ ENNReal.ofReal C * ∑ j, Work.CR.Flat.holderNorm N α (g j) Set.univ := by
  classical
  -- the outer multiradii `2ρ`, whose halves are `ρ`
  have h2ρ : ∀ j, 0 < 2 * ρ j := fun j => by linarith [hρ j]
  have hhalf : (fun j : Fin n => (2 * ρ j) / 2) = ρ := funext fun j => by ring
  -- the Schauder estimates (with the outer radius `2ρ`) and the `C^{1,α}` estimate for `C^{0,α}`
  -- data (the latter also supplies differentiability of the potentials)
  obtain ⟨CD, hCDpos, hCD⟩ :=
    bmPot_riesz_Ck (n := n) hn (c := 0) (r := fun j => 2 * ρ j) hα0 hα1 h2ρ N
  obtain ⟨CT, hCTpos, hCT⟩ :=
    bmPotential_top_gain (n := n) hn (c := 0) (r := fun j => 2 * ρ j) hα0 hα1 h2ρ N
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    bmPotential_holder_one_of_holderNorm (n := n) hn (c := 0) (s := ρ) hα0 hα1 hρ
  refine ⟨CD + CT + C₀ + 1, by positivity, ?_⟩
  intro g hg hcs hgfin hgsup
  -- the vanishing hypothesis in the form used by the estimates
  have hsup2 : ∀ j z, (∃ i, (2 * ρ i) / 2 ≤ ‖z i - (0 : Fin n → ℂ) i‖) → g j z = 0 := by
    intro j z hz
    obtain ⟨i, hi⟩ := hz
    refine hgsup j z ⟨i, ?_⟩
    have h1 : (2 * ρ i) / 2 = ρ i := by ring
    rw [h1] at hi
    simpa using hi
  -- the total size of the data, as a real number
  set S : ℝ := ∑ j, (holderNorm N α (g j) Set.univ).toReal with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
  have hSeq : (∑ j, holderNorm N α (g j) Set.univ) = ENNReal.ofReal S := by
    rw [hSdef, ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_toReal (ne_of_lt (hgfin j))).symm
  -- the potential is `C^N` everywhere
  have hu : ContDiff ℝ N (bmPotential g) :=
    bmPotential_contDiff_of_hasCompactSupport hn hg hcs
  have hPopen : IsOpen (polydisc (0 : Fin n → ℂ) ρ) := isOpen_polydisc 0 ρ
  have hPuniq : UniqueDiffOn ℝ (polydisc (0 : Fin n → ℂ) ρ) := hPopen.uniqueDiffOn
  have hPconv : Convex ℝ (polydisc (0 : Fin n → ℂ) ρ) := convex_polydisc 0 ρ
  -- ### the `C^{N+1,α}` bound
  have hnorm : holderNorm (N + 1) α (bmPotential g) (polydisc 0 ρ)
      ≤ ENNReal.ofReal (CD + CT + C₀ + 1) * ∑ j, holderNorm N α (g j) Set.univ := by
    have h := hCD g hg hgfin hsup2
    rw [hhalf] at h
    refine h.trans ?_
    exact mul_le_mul_left (show ENNReal.ofReal CD ≤ ENNReal.ofReal (CD + CT + C₀ + 1) from
      ENNReal.ofReal_le_ofReal (by linarith)) (∑ j, holderNorm N α (g j) Set.univ)
  -- ### the derived data of order `N`
  set ψ : (Fin N → Fin n → ℂ) → Fin n → (Fin n → ℂ) → ℂ :=
    fun v j y => iteratedFDeriv ℝ N (g j) y v with hψdef
  -- its slices are the potentials of the derived data
  have hslice : ∀ v : Fin N → Fin n → ℂ,
      (fun y => iteratedFDeriv ℝ N (bmPotential g) y v) = fun y => bmPotential (ψ v) y := by
    intro v
    funext y
    simpa [hψdef] using
      bmPotential_iteratedFDeriv (n := n) hn (c := 0) (R := fun j => 2 * ρ j) h2ρ (G := g) hg
        hsup2 v y
  -- the derived data have finite `C^{0,α}`-norm, with a bound uniform in `v`
  have hψfin : ∀ v j, holderNorm 0 α (ψ v j) Set.univ < ⊤ := by
    intro v j
    refine lt_of_le_of_lt (b := ENNReal.ofReal (∏ i, ‖v i‖) * holderNorm N α (g j) Set.univ) ?_ ?_
    · simpa [hψdef] using
        holderNorm_zero_iteratedFDeriv_apply_le (m := N) (k := N) le_rfl (α := α) (f := g j) v
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hgfin j)
  have hψcont : ∀ v j, Continuous (ψ v j) := fun v j =>
    continuous_of_holderNorm_zero_lt_top hα0 (hψfin v j)
  have hψsum : ∀ v, (∑ j, holderNorm 0 α (ψ v j) Set.univ)
      ≤ ENNReal.ofReal (∏ i, ‖v i‖) * ENNReal.ofReal S := by
    intro v
    calc ∑ j, holderNorm 0 α (ψ v j) Set.univ
        ≤ ∑ j, ENNReal.ofReal (∏ i, ‖v i‖) * holderNorm N α (g j) Set.univ :=
          Finset.sum_le_sum fun j _ => by
            simpa [hψdef] using
              holderNorm_zero_iteratedFDeriv_apply_le (m := N) (k := N) le_rfl (α := α) (f := g j) v
      _ = ENNReal.ofReal (∏ i, ‖v i‖) * (∑ j, holderNorm N α (g j) Set.univ) := by
          rw [Finset.mul_sum]
      _ = ENNReal.ofReal (∏ i, ‖v i‖) * ENNReal.ofReal S := by rw [hSeq]
  have hψsum_ne : ∀ v, (∑ j, holderNorm 0 α (ψ v j) Set.univ) ≠ ⊤ := fun v =>
    ne_of_lt (ENNReal.sum_lt_top.mpr fun j _ => hψfin v j)
  -- the derived data vanish off `polydisc 0 ρ`
  have hψvanish : ∀ v j z, (∃ i, ρ i ≤ ‖z i‖) → ψ v j z = 0 := by
    intro v j z hz
    simpa [hψdef] using vanishing_aux (ρ := ρ) (f := g j) (m := N) (hg j) (hgsup j) z hz v
  have hψvanish' : ∀ v j z, (∃ i, ρ i ≤ ‖z i - (0 : Fin n → ℂ) i‖) → ψ v j z = 0 := by
    intro v j z hz
    obtain ⟨i, hi⟩ := hz
    exact hψvanish v j z ⟨i, by simpa using hi⟩
  -- ### the `C^{1,α}` bound and differentiability for the potentials of the derived data
  have hψdata : ∀ v, (holderNorm 1 α (fun y => bmPotential (ψ v) y) (polydisc 0 ρ)
        ≤ ENNReal.ofReal (C₀ * (∏ i, ‖v i‖) * S)) ∧
      (∀ z ∈ polydisc 0 ρ, DifferentiableAt ℝ (fun y => bmPotential (ψ v) y) z) := by
    intro v
    obtain ⟨hbd, hdiff⟩ := hC₀ (ψ v) (hψcont v) (hψvanish' v) (hψsum_ne v)
    refine ⟨hbd.trans ?_, hdiff⟩
    calc ENNReal.ofReal C₀ * (∑ j, holderNorm 0 α (ψ v j) Set.univ)
        ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal (∏ i, ‖v i‖) * ENNReal.ofReal S) :=
          mul_le_mul_right (hψsum v) _
      _ = ENNReal.ofReal (C₀ * (∏ i, ‖v i‖) * S) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀pos.le,
            ← ENNReal.ofReal_mul (mul_nonneg hC₀pos.le
              (Finset.prod_nonneg fun i _ => norm_nonneg _))]
  -- ### the derivative bounds for the slices
  have hBnonneg : ∀ v : Fin N → Fin n → ℂ, 0 ≤ C₀ * (∏ i, ‖v i‖) * S := fun v =>
    mul_nonneg (mul_nonneg hC₀pos.le (Finset.prod_nonneg fun i _ => norm_nonneg _)) hS0
  have hslice_bnd : ∀ v z, z ∈ polydisc 0 ρ →
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ N (bmPotential g) y v) z‖
        ≤ (C₀ * S) * ∏ i, ‖v i‖ := by
    intro v z hz
    have hb := (holderNorm_one_bounds (isOpen_polydisc (0 : Fin n → ℂ) ρ) (hBnonneg v)
      (hψdata v).1).2.2.1 z hz
    rw [← hslice v] at hb
    calc ‖fderiv ℝ (fun y => iteratedFDeriv ℝ N (bmPotential g) y v) z‖
        ≤ C₀ * (∏ i, ‖v i‖) * S := hb
      _ = (C₀ * S) * ∏ i, ‖v i‖ := by ring
  have hslice_holder : ∀ v z, z ∈ polydisc 0 ρ → ∀ z' ∈ polydisc 0 ρ,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ N (bmPotential g) y v) z
        - fderiv ℝ (fun y => iteratedFDeriv ℝ N (bmPotential g) y v) z'‖
        ≤ (C₀ * S) * (∏ i, ‖v i‖) * ‖z - z'‖ ^ α := by
    intro v z hz z' hz'
    have hb := (holderNorm_one_bounds (isOpen_polydisc (0 : Fin n → ℂ) ρ) (hBnonneg v)
      (hψdata v).1).2.2.2 z hz z' hz'
    rw [← hslice v] at hb
    calc ‖fderiv ℝ (fun y => iteratedFDeriv ℝ N (bmPotential g) y v) z
          - fderiv ℝ (fun y => iteratedFDeriv ℝ N (bmPotential g) y v) z'‖
        ≤ C₀ * (∏ i, ‖v i‖) * S * ‖z - z'‖ ^ α := hb
      _ = (C₀ * S) * (∏ i, ‖v i‖) * ‖z - z'‖ ^ α := by ring
  -- ### differentiability of the `N`-th iterated derivative
  have hdiffN : ∀ z ∈ polydisc 0 ρ,
      DifferentiableAt ℝ (iteratedFDeriv ℝ N (bmPotential g)) z :=
    diffIter_aux (Ω := polydisc 0 ρ) hPopen hPconv hα0 (mul_nonneg hC₀pos.le hS0)
      (fun v z hz => by
        rw [hslice v]
        exact (hψdata v).2 z hz)
      (fun v z hz => hslice_bnd v z hz)
      (fun v z hz z' hz' => hslice_holder v z hz z' hz')
  -- ### continuity of the `(N+1)`-st within-derivative
  have hcontN1 : ContinuousOn (iteratedFDerivWithin ℝ (N + 1) (bmPotential g) (polydisc 0 ρ))
      (polydisc 0 ρ) := by
    have htop := hCT g hg hgfin hsup2
    rw [hhalf] at htop
    have hsem : holderSeminorm (N + 1) α (bmPotential g) (polydisc 0 ρ)
        ≤ ENNReal.ofReal (CT * S) := by
      calc holderSeminorm (N + 1) α (bmPotential g) (polydisc 0 ρ)
          ≤ iterDerivNorm (N + 1) (bmPotential g) (polydisc 0 ρ)
            + holderSeminorm (N + 1) α (bmPotential g) (polydisc 0 ρ) := le_add_left le_rfl
        _ ≤ ENNReal.ofReal CT * ∑ j, holderNorm N α (g j) Set.univ := htop
        _ = ENNReal.ofReal (CT * S) := by rw [hSeq, ← ENNReal.ofReal_mul hCTpos.le]
    exact continuousOn_aux hα0 (mul_nonneg hCTpos.le hS0) hsem
  -- ### assembly
  refine ⟨?_, hnorm⟩
  refine contDiffOn_of_continuousOn_differentiableOn (n := ((N + 1 : ℕ) : ℕ∞)) ?_ ?_
  · intro m hm
    have hmle : m ≤ N + 1 := by exact_mod_cast hm
    rcases lt_or_eq_of_le hmle with hmlt | heq
    · have hle : m ≤ N := Nat.lt_succ_iff.mp hmlt
      exact (hu.contDiffOn).continuousOn_iteratedFDerivWithin (by exact_mod_cast hle) hPuniq
    · rw [heq]
      exact hcontN1
  · intro m hm
    have hmlt : m < N + 1 := by exact_mod_cast hm
    have hmle : m ≤ N := Nat.lt_succ_iff.mp hmlt
    rcases lt_or_eq_of_le hmle with hlt | heq
    · exact (hu.contDiffOn).differentiableOn_iteratedFDerivWithin (by exact_mod_cast hlt) hPuniq
    · rw [heq]
      intro z hz
      have h1 : (fun x => iteratedFDerivWithin ℝ N (bmPotential g) (polydisc 0 ρ) x)
          =ᶠ[𝓝 z] iteratedFDeriv ℝ N (bmPotential g) := by
        filter_upwards [hPopen.mem_nhds hz] with w hw
        exact iteratedFDerivWithin_of_isOpen N hPopen hw
      exact ((h1.differentiableAt_iff).mpr (hdiffN z hz)).differentiableWithinAt

end

end Work.NN.Core
