import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.H_conv_alt
import Submission.Work.A14D.H_local_at_one
import Submission.Work.A14D.H_not_holo_at_one
import Submission.Work.A14D.uh_not_holo_at_ninth
import Submission.Work.A14D.logCoeff_exists
import Submission.Work.A14D.uh_ode
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.A14D.LZ_sub_const_mul
import Submission.Work.A14D.exists_sol_LZ_convex
import Submission.Work.A14D.eqOn_of_sol_LZ
import Submission.Work.A14D.om1_geometry
import Submission.Work.A14D.glue_three_LZ_Om1

namespace Work.A14D

/-
ROUTE (area A14D, design `REFS/design/a14/A14_design.lean.txt` (K), the existential half).

`SU = {im z > (1-re z)/8}`, `SL = {im z < (re z-1)/8}`, `Om1 = {im z ≠ 0 ∨ 1 < re z} = ℂ∖(-∞,1]`.
`SU ∩ SL = {re z > 1, (1-re z)/8 < im z < (re z-1)/8}` is a nonempty open convex wedge inside
`Om1`; `SU`, `SL` are convex and `PZ` has no zero on `Om1`.

1. `LZ (HU - HL) = rhsZ - rhsZ = 0` on `SU ∩ SL`, so the germ of `D₀ := HU - HL` there is a
   solution of the homogeneous equation; continue it to `Om1`
   by gluing along the three convex sets `{im > 0} ∪ {im < 0} ∪ (SU ∩ SL)` to get `D` with
   `LZ D = 0` on `Om1` and `D = HU - HL` on `SU ∩ SL` (this is the "jump" `J(H)`).
2. `halfU δ = ball ninth δ ∩ {im > 0}`, `halfL δ = ball ninth δ ∩ {im < 0}` are open convex and
   contained in `Om1`; apply the PROVED `Work.A14D.logCoeff_exists` to `D` on each to get `κU`,
   `κL`.

Note (do not be misled): the two coefficients need NOT be equal — `halfU`, `halfL` are disjoint
and the log term is the principal `Complex.log (z - ninth)`.  What is true (and provable) is
`κL = -conj κU` (see `kappa_jump_nnz`).  The previous prover's argument "`SU ∪ SL` is simply
connected hence `HU = HL`" is wrong: `HU` is the continuation of `Hfun` to `SU`, `HL` to `SL`,
and the two differ because `Hfun` (= `HZ a b c`) has a genuine `log^2` singularity at `x = 1`
(`H_local_at_one`), so the difference loop (which winds once around 1) has non-trivial monodromy.
-/

open Complex Metric
open scoped BigOperators
open Work.A14D



theorem kappa_jump_sol (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (y9 : ℂ → ℂ) (δ : ℝ) (hY : Y9 y9 δ) :
    ∃ D : ℂ → ℂ, DifferentiableOn ℂ D Om1 ∧ (∀ z ∈ Om1, LZ D z = 0) ∧
      (∀ z ∈ SU ∩ SL, D z = HU z - HL z) ∧
      ∃ κU κL : ℂ, LogCoeff y9 δ (halfU δ) D κU ∧ LogCoeff y9 δ (halfL δ) D κL := by
  obtain ⟨hSUc, hSUo, -, hSLc, hSLo, -, hcover, hPZpos, hPZneg, -, -⟩ := om1_geometry
  obtain ⟨hHUd, hHUode, -⟩ := hHU
  obtain ⟨hHLd, hHLode, -⟩ := hHL
  -- the three open convex pieces: upper half-plane, lower half-plane, and the wedge `SU ∩ SL`
  have hAo : IsOpen ({z : ℂ | 0 < z.im}) := isOpen_lt continuous_const Complex.continuous_im
  have hBo : IsOpen ({z : ℂ | z.im < 0}) := isOpen_lt Complex.continuous_im continuous_const
  have hCo : IsOpen (SU ∩ SL) := hSUo.inter hSLo
  have hCc : Convex ℝ (SU ∩ SL) := hSUc.inter hSLc
  have hAB : ({z : ℂ | 0 < z.im} : Set ℂ) ∩ {z : ℂ | z.im < 0} = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false]
    constructor
    · rintro ⟨h1, h2⟩
      linarith
    · intro h
      exact h.elim
  set gC : ℂ → ℂ := fun w => HU w - HL w with hgC
  -- `gC` solves the homogeneous equation on the wedge
  have hCd : DifferentiableOn ℂ gC (SU ∩ SL) :=
    (hHUd.mono (fun z hz => hz.1)).sub (hHLd.mono (fun z hz => hz.2))
  have hCL : ∀ z ∈ SU ∩ SL, LZ gC z = 0 := by
    intro z hz
    have hsub : (fun w : ℂ => HU w - 1 * HL w) = gC := by
      rw [hgC]; funext w; ring
    rw [← hsub, LZ_sub_const_mul hCo (c := 1)
      (hHUd.mono (fun z hz => hz.1)) (hHLd.mono (fun z hz => hz.2)) hz,
      hHUode z hz.1, hHLode z hz.2]
    ring
  -- seed points in the two halves of the wedge
  set p : ℂ := 4 + (1/4 : ℂ) * Complex.I with hpdef
  set q : ℂ := 4 - (1/4 : ℂ) * Complex.I with hqdef
  have hpA : p ∈ ({z : ℂ | 0 < z.im}) := by
    rw [hpdef]
    show 0 < (4 + (1/4 : ℂ) * Complex.I).im
    norm_num
  have hpC : p ∈ SU ∩ SL := by
    rw [hpdef]
    refine ⟨?_, ?_⟩
    · show (1 - (4 + (1/4 : ℂ) * Complex.I).re) / 8 < (4 + (1/4 : ℂ) * Complex.I).im
      norm_num
    · show (4 + (1/4 : ℂ) * Complex.I).im < ((4 + (1/4 : ℂ) * Complex.I).re - 1) / 8
      norm_num
  have hqB : q ∈ ({z : ℂ | z.im < 0}) := by
    rw [hqdef]
    show (4 - (1/4 : ℂ) * Complex.I).im < 0
    norm_num
  have hqC : q ∈ SU ∩ SL := by
    rw [hqdef]
    refine ⟨?_, ?_⟩
    · show (1 - (4 - (1/4 : ℂ) * Complex.I).re) / 8 < (4 - (1/4 : ℂ) * Complex.I).im
      norm_num
    · show (4 - (1/4 : ℂ) * Complex.I).im < ((4 - (1/4 : ℂ) * Complex.I).re - 1) / 8
      norm_num
  -- extend `gC` to the upper half-plane
  obtain ⟨gA, hgAd, hgAp, hgApd, -, hgAL⟩ :=
    exists_sol_LZ_convex hAo (convex_halfSpace_im_gt 0) (fun z hz => hPZpos z hz) hpA
      (HU p - HL p) (deriv gC p)
  have hAC : Set.EqOn gA gC ({z : ℂ | 0 < z.im} ∩ (SU ∩ SL)) := by
    refine eqOn_of_sol_LZ (hAo.inter hCo) ((convex_halfSpace_im_gt 0).inter hCc).isPreconnected
      (fun z hz => hPZpos z hz.1) (hgAd.mono Set.inter_subset_left) ?_ ?_ ?_ ⟨hpA, hpC⟩
      hgAp hgApd
    · exact hCd.mono Set.inter_subset_right
    · exact fun z hz => hgAL z hz.1
    · exact fun z hz => hCL z hz.2
  -- extend `gC` to the lower half-plane
  obtain ⟨gB, hgBd, hgBq, hgBqd, -, hgBL⟩ :=
    exists_sol_LZ_convex hBo (convex_halfSpace_im_lt 0) (fun z hz => hPZneg z hz) hqB
      (HU q - HL q) (deriv gC q)
  have hBC : Set.EqOn gB gC ({z : ℂ | z.im < 0} ∩ (SU ∩ SL)) := by
    refine eqOn_of_sol_LZ (hBo.inter hCo) ((convex_halfSpace_im_lt 0).inter hCc).isPreconnected
      (fun z hz => hPZneg z hz.1) (hgBd.mono Set.inter_subset_left) ?_ ?_ ?_ ⟨hqB, hqC⟩
      hgBq hgBqd
    · exact hCd.mono Set.inter_subset_right
    · exact fun z hz => hgBL z hz.1
    · exact fun z hz => hCL z hz.2
  -- glue the three pieces
  obtain ⟨F, hFd, hFL, -, -, hFC⟩ :=
    glue_three_LZ_Om1 hAo hBo hCo hAB hcover hgAd hgBd hCd hgAL hgBL hCL hAC hBC
  -- the log-coefficients on the two halves of the disc
  have hUsub : halfU δ ⊆ ball ninth δ ∩ {z : ℂ | z.im ≠ 0 ∨ ninth.re < z.re} :=
    fun z hz => ⟨hz.1, Or.inl (ne_of_gt hz.2)⟩
  have hUOm1 : halfU δ ⊆ Om1 := fun z hz => Or.inl (ne_of_gt hz.2)
  have hLsub : halfL δ ⊆ ball ninth δ ∩ {z : ℂ | z.im ≠ 0 ∨ ninth.re < z.re} :=
    fun z hz => ⟨hz.1, Or.inl (ne_of_lt hz.2)⟩
  have hLOm1 : halfL δ ⊆ Om1 := fun z hz => Or.inl (ne_of_lt hz.2)
  obtain ⟨κU, hU⟩ :=
    logCoeff_exists hY (halfU δ) (isOpen_halfUp δ) (convex_halfUp δ) hUsub F
      (hFd.mono hUOm1) (fun z hz => hFL z (hUOm1 hz))
  obtain ⟨κL, hL⟩ :=
    logCoeff_exists hY (halfL δ) (isOpen_halfDn δ) (convex_halfDn δ) hLsub F
      (hFd.mono hLOm1) (fun z hz => hFL z (hLOm1 hz))
  refine ⟨F, hFd, hFL, ?_, κU, κL, hU, hL⟩
  intro z hz
  exact hFC hz

end Work.A14D
