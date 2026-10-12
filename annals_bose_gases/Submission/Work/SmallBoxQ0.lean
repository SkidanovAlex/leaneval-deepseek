import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Convex.finset_uniform_jensen
import Submission.Commons.Analysis.Real.window_density_quadratic_bound
import Submission.Q0Convex
import Submission.Work.KineticBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SmallBoxes front (thm:smallbox), step 1: the scale-`s` Q0 repulsion bound

For the small-box scale `s` (the FS `ℓ·d ≪ (μa)^{-1/2}` of thm:smallbox) the
corpus centred box at `ℓ := s` serves as the small box, and the first
repulsion ingredient is a lower bound on the renormalized Q0 value
`q0RenVal(s,μ,Φ) := ½s⁻³(8πa v)·S₂ − (8πa v)·μ·S₁`, `S₁ = cS1 s Φ`,
`S₂ = cS2 s Φ`, for a NORMALIZED state (`∫Φ² = 1`).  This module proves

    q0RenVal(s,μ,Φ) ≥ (4πa/s³)(S₁ − μs³ − ½)² − 4πaμ²s³(1 + 1/(2μs³))²

(`q0RenVal_repulsion`): the condensed-count concentration
(`Q0Convex.cS2_ge_sq_sub_self` : `S₂ ≥ S₁² − S₁`) + completion of the square
(`Q0Convex.q0c_square_identity`), both used exactly as in
`Q0Convex.q0_concentration` but for the q0RenVal object.  This is the
scale-`s` repulsion quadratic of thm:smallbox (with `S₁ = N̂ − n₊ ≈ N̂` by the
subsequent n₊-window); the remaining thm:smallbox steps (gap absorption via
`KineticBound.kinWord_ge_mu_a_cnPlus`, the (u,u″)-split algebra, the error
terms `(R/s)²`, `K_B³(μa³)^{1/2}`) are recorded in STATUS Session-78.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Scale-`s` Q0 repulsion** (normalised state): with `S₁ := cS1 s Φ`,
`q0RenVal(s,μ,Φ) ≥ (4πa/s³)(S₁−μs³−½)² − 4πaμ²s³(1+1/(2μs³))²`. -/
lemma q0RenVal_repulsion {N : ℕ} {v : ℝ³ → ℝ} {R s μ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRℓ : R ≤ s * chiR0) (hμ : 0 < μ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) :
    (4 * π * (a v) / s ^ 3) * (cS1 s Φ - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
      ≤ q0RenVal (N := N) (v := v) s μ Φ := by
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hCS : cS1 s Φ * cS1 s Φ - cS1 s Φ ≤ cS2 s Φ :=
    cS2_ge_sq_sub_self hs hΦc hnorm
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hnum : 0 ≤ 4 * π * (a v) := by positivity
  have hcoef : 0 ≤ 4 * π * (a v) / s ^ 3 := div_nonneg hnum (pow_nonneg hs.le 3)
  have hmul : (4 * π * (a v) / s ^ 3) * (cS1 s Φ * cS1 s Φ - cS1 s Φ)
      ≤ (4 * π * (a v) / s ^ 3) * cS2 s Φ :=
    mul_le_mul_of_nonneg_left hCS hcoef
  have hident : (1 / 2 : ℝ) * (s ^ 3)⁻¹ * (8 * π * (a v)) = 4 * π * (a v) / s ^ 3 := by
    field_simp [ne_of_gt hs]
    ring
  have hA : (4 * π * (a v) / s ^ 3) * (cS1 s Φ ^ 2 - cS1 s Φ)
        - (8 * π * (a v)) * μ * cS1 s Φ
      ≤ q0RenVal (N := N) (v := v) s μ Φ := by
    dsimp [q0RenVal]
    calc
      (4 * π * (a v) / s ^ 3) * (cS1 s Φ ^ 2 - cS1 s Φ)
          - (8 * π * (a v)) * μ * cS1 s Φ
          ≤ (4 * π * (a v) / s ^ 3) * cS2 s Φ - (8 * π * (a v)) * μ * cS1 s Φ := by
            nlinarith [hmul]
      _ = (1 / 2) * (s ^ 3)⁻¹ * (8 * π * (a v)) * cS2 s Φ
          - (8 * π * (a v)) * μ * cS1 s Φ := by
            rw [← hident]
  have hsq := q0c_square_identity (a v) μ s (cS1 s Φ) (ne_of_gt hs) (ne_of_gt hμ)
  calc
    (4 * π * (a v) / s ^ 3) * (cS1 s Φ - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        = (4 * π * (a v) / s ^ 3) * (cS1 s Φ ^ 2 - cS1 s Φ)
          - (8 * π * (a v)) * μ * cS1 s Φ := hsq.symm
    _ ≤ q0RenVal (N := N) (v := v) s μ Φ := hA



/-- **The `S₁ = N̂ − cnPlus` bridge at `J := 1`** (a-priori link between the
Q0-repulsion variable `S₁ := cS1 ℓ Φ` and the particle density
`u := N̂/ℓ³`): from `cnPlus + cS1 = N̂·J` (`CentredSector.cnPlus_add_cS1`) at
normalisation `J = 1`, the condensate count differs from the particle number
exactly by the excited count,

    cS1 ℓ Φ = (N : ℝ) − cnPlus ℓ Φ . -/
lemma cS1_eq_nat_sub_cnPlus {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ)
    (hJ1 : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    cS1 ℓ Φ = (N : ℝ) - cnPlus ℓ Φ := by
  have h := cnPlus_add_cS1 hℓ hΦc
  rw [hJ1] at h
  nlinarith

/-- **n₊-window ⟹ density distance of `S₁`**: the condensate density
`S₁/ℓ³` sits at distance exactly `cnPlus/ℓ³` from the particle density
`u := N̂/ℓ³` (so an a-priori bound `cnPlus ℓ Φ ≤ B` transfers to
`|S₁/ℓ³ − u| ≤ B/ℓ³`). -/
lemma cS1_density_dist {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ)
    (hJ1 : (∫ x in abox N ℓ, (Φ x) ^ 2) = 1) :
    |cS1 ℓ Φ / ℓ ^ 3 - (N : ℝ) / ℓ ^ 3| ≤ cnPlus ℓ Φ / ℓ ^ 3 := by
  have hEq := cS1_eq_nat_sub_cnPlus hℓ hΦc hJ1
  have hnn : 0 ≤ cnPlus ℓ Φ := cnPlus_nonneg
  have hd : 0 < ℓ ^ 3 := pow_pos hℓ 3
  rw [hEq]
  have hdE : ((N : ℝ) - cnPlus ℓ Φ) / ℓ ^ 3 - (N : ℝ) / ℓ ^ 3 = -(cnPlus ℓ Φ) / ℓ ^ 3 := by
    field_simp [ne_of_gt hd]
    ring
  rw [hdE]
  rw [neg_div]
  rw [abs_neg]
  rw [abs_of_nonneg (div_nonneg hnn hd.le)]



/-- **Per-sector small-box repulsion at the DENSITY `u := N̂/s³`** (combining
`q0RenVal_repulsion` + the J=1 bridge `cS1 = N̂ − cnPlus` + the square
transfer `½U² − P² ≤ (U−P)²` — the general fact is delegated to the Commons
as `Commons.Analysis.Real.sub_sq_half_sq` and inlined here): for normalized Φ,
`0 < s`, `0 < μ`, chosen branch, with `U := N̂ − μs³ − ½` and
`P := cnPlus s Φ`,

    q0RenVal(s,μ,Φ) ≥ (4πa/s³)·(½U² − P²) − 4πaμ²s³(1 + 1/(2μs³))² .

The repulsion is now in the particle count `N̂` (density `u := N̂/s³`) rather
than the condensate count `S₁`; the only `S₁`-dependent remnant is the
explicit `−(4πa/s³)·(cnPlus s Φ)²` error, which the later n₊-window + kinetic
gap absorb (checklist items 3–4). -/
lemma q0RenVal_density_repulsion {N : ℕ} {v : ℝ³ → ℝ} {R s μ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRℓ : R ≤ s * chiR0) (hμ : 0 < μ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) :
    (4 * π * (a v) / s ^ 3) *
        ((1 / 2 : ℝ) * ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2 - (cnPlus s Φ) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
      ≤ q0RenVal (N := N) (v := v) s μ Φ := by
  have hrep := q0RenVal_repulsion hR hv_nonneg hvrad hv_supp h hs hRℓ hμ hΦc hnorm
  have hS := cS1_eq_nat_sub_cnPlus hs hΦc hnorm
  have hT : cS1 s Φ - μ * s ^ 3 - (1 / 2 : ℝ)
      = ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) - cnPlus s Φ := by
    rw [hS]
    ring
  have hhalf : (1 / 2 : ℝ) * (((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2) - (cnPlus s Φ) ^ 2
      ≤ (cS1 s Φ - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2 := by
    rw [hT]
    have hq : 0 ≤ (((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) - 2 * cnPlus s Φ) ^ 2 := sq_nonneg _
    nlinarith
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hnum : 0 ≤ 4 * π * (a v) := by positivity
  have hcoef : 0 ≤ 4 * π * (a v) / s ^ 3 := div_nonneg hnum (pow_nonneg hs.le 3)
  calc
    (4 * π * (a v) / s ^ 3) *
        ((1 / 2 : ℝ) * ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2 - (cnPlus s Φ) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        ≤ (4 * π * (a v) / s ^ 3) * (cS1 s Φ - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2
          - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2 := by
          exact sub_le_sub_right
            (mul_le_mul_of_nonneg_left hhalf hcoef)
            ((4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2)
    _ ≤ q0RenVal (N := N) (v := v) s μ Φ := hrep



/-- **Potsplit attachment at the small-box scale `s`** — combining
`pot_first_bound_q4free` (qLHS ≥ q0RenVal − cross-errors, at `J := 1`) with
the density repulsion `q0RenVal_density_repulsion`: the potential word of the
small-box Hamiltonian satisfies, for `U := N̂ − μs³ − ½`, `P := cnPlus s Φ`,

    qLHSword(N,s,μ,wPairC v, wPairC g0) Φ
        ≥ (4πa/s³)·(½U² − P²) − 4πaμ²s³(1+1/(2μs³))²
          − 5·qcrossC·(a v)·Xbig − μ·q2C0(a v)·P ,
    Xbig := N̂²/s³ + μ²s³ .

The three error blocks are explicit: the `Xbig` term (window-absorbable, L1),
the `cnPlus`-linear one-body term and the `P²` term (both gap-absorbable via
`kinWord_ge_mu_a_cnPlus` in the next act). -/
lemma qLHS_density_repulsion {N : ℕ} {v : ℝ³ → ℝ} {R s μ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRℓ : R ≤ s * chiR0) (hμ : 0 < μ) {Φ : X N → ℝ}
    (hΦc : Continuous Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1) :
    (4 * π * (a v) / s ^ 3) *
        ((1 / 2 : ℝ) * ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2 - (cnPlus s Φ) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (5 * qcrossC) * (a v) * (((N : ℝ) ^ 2 / s ^ 3) + μ ^ 2 * s ^ 3)
        - μ * q2C0 (a v) * cnPlus s Φ
      ≤ qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  have hF := pot_first_bound_q4free (N := N) (ℓ := s) (μ := μ) hs hμ.le
    (v := v) hv_nonneg hvrad hv_memL1 (R := R) hR hv_supp h hRℓ (Φ := Φ) hΦc
  have hF1 : q0RenVal (N := N) (v := v) s μ Φ
        - (5 * qcrossC) * (a v) * (((N : ℝ) ^ 2 / s ^ 3) + μ ^ 2 * s ^ 3)
        - μ * q2C0 (a v) * cnPlus s Φ
      ≤ qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    simpa [hnorm] using hF
  have hR := q0RenVal_density_repulsion hR hv_nonneg hvrad hv_supp h hs hRℓ hμ hΦc hnorm
  calc
    (4 * π * (a v) / s ^ 3) *
        ((1 / 2 : ℝ) * ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2 - (cnPlus s Φ) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (5 * qcrossC) * (a v) * (((N : ℝ) ^ 2 / s ^ 3) + μ ^ 2 * s ^ 3)
        - μ * q2C0 (a v) * cnPlus s Φ
        ≤ q0RenVal (N := N) (v := v) s μ Φ
          - (5 * qcrossC) * (a v) * (((N : ℝ) ^ 2 / s ^ 3) + μ ^ 2 * s ^ 3)
          - μ * q2C0 (a v) * cnPlus s Φ := by
          nlinarith [hR]
    _ ≤ qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := hF1



/-- **Small-box energy with the gap absorbing the excited-count errors** (first
move of the final assembly): adding `kinWord N s Φ` to both sides of
`qLHS_density_repulsion`, the kinetic Neumann gap
(`kinWord_gap_cnPlus : (1/(36s²))·cnPlus ≤ kinWord`) absorbs BOTH the
one-body linear term and the `(4πa/s³)·(cnPlus s Φ)²` remnant, under the
n₊-window `cnPlus s Φ ≤ B` and the combined gap regime
`μ·q2C0(a v) + (4πa/s³)·B ≤ 1/(36s²)`:

    E_s(Φ) := kinWord N s Φ + qLHSword(N,s,μ,wPairC v, wPairC g0) Φ
        ≥ (4πa/s³)·(1/2)·U² − 4πaμ²s³(1+1/(2μs³))² − 5·qcrossC·(a v)·Xbig ,
    U := N̂ − μs³ − ½ ,  Xbig := N̂²/s³ + μ²s³ .

(Φ is required smooth — `ContDiff ℝ ∞` — for the Neumann gap; the `Xbig`
term is killed next via the μ-window `|N̂/s³ − μ| ≤ μδ`.) -/
lemma energy_smallBox_density {N : ℕ} {v : ℝ³ → ℝ} {R s μ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRℓ : R ≤ s * chiR0) (hμ : 0 < μ)
    {B : ℝ} (hB : 0 ≤ B) {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1)
    (hwinP : cnPlus s Φ ≤ B)
    (hreg : μ * q2C0 (a v) + (4 * π * (a v) / s ^ 3) * B ≤ 1 / (36 * s ^ 2)) :
    (4 * π * (a v) / s ^ 3) *
        ((1 / 2 : ℝ) * ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (5 * qcrossC) * (a v) * (((N : ℝ) ^ 2 / s ^ 3) + μ ^ 2 * s ^ 3)
      ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  have hΦc0 : Continuous Φ := hΦc.continuous
  have hQ := qLHS_density_repulsion hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRℓ hμ
    (Φ := Φ) hΦc0 hnorm
  have hg := kinWord_gap_cnPlus (N := N) (ℓ := s) hs (Φ := Φ) hΦc
  have hPnn : 0 ≤ cnPlus s Φ := cnPlus_nonneg
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hcoef : 0 ≤ 4 * π * (a v) / s ^ 3 := by
    exact div_nonneg (by positivity : 0 ≤ 4 * π * (a v)) (pow_nonneg hs.le 3)
  have hP2 : (cnPlus s Φ) ^ 2 ≤ B * cnPlus s Φ := by
    calc
      (cnPlus s Φ) ^ 2 = cnPlus s Φ * cnPlus s Φ := by rw [pow_two]
      _ ≤ B * cnPlus s Φ := mul_le_mul_of_nonneg_right hwinP hPnn
  have hPb : (4 * π * (a v) / s ^ 3) * (cnPlus s Φ) ^ 2
      ≤ (4 * π * (a v) / s ^ 3) * (B * cnPlus s Φ) :=
    mul_le_mul_of_nonneg_left hP2 hcoef
  have herr : (4 * π * (a v) / s ^ 3) * (cnPlus s Φ) ^ 2
        + μ * q2C0 (a v) * cnPlus s Φ
      ≤ kinWord N s Φ := by
    have hlin : μ * q2C0 (a v) * cnPlus s Φ
          + (4 * π * (a v) / s ^ 3) * B * cnPlus s Φ
        ≤ (1 / (36 * s ^ 2)) * cnPlus s Φ := by
      -- (μq2C0 + (4πa/s³)B) ≤ 1/(36s²), multiply by P ≥ 0 (right-factor)
      have hsum : μ * q2C0 (a v) + (4 * π * (a v) / s ^ 3) * B ≤ 1 / (36 * s ^ 2) := hreg
      -- target is c1·P + c2·P ≤ c3·P with c1+c2 ≤ c3: from hsum via add-distrib: (c1 + c2)·P ≤ c3·P
      have hsumP : (μ * q2C0 (a v) + (4 * π * (a v) / s ^ 3) * B) * cnPlus s Φ
          ≤ (1 / (36 * s ^ 2)) * cnPlus s Φ := mul_le_mul_of_nonneg_right hreg hPnn
      -- LHS = μq2C0·P + ((4πa/s³)B)·P — but written (4πa/s³)*B*P = ((4πa/s³)B)·P ✓ matches expansion
      simpa [add_mul] using hsumP
    calc
      (4 * π * (a v) / s ^ 3) * (cnPlus s Φ) ^ 2
            + μ * q2C0 (a v) * cnPlus s Φ
          ≤ (4 * π * (a v) / s ^ 3) * (B * cnPlus s Φ)
            + μ * q2C0 (a v) * cnPlus s Φ := by
              exact add_le_add_left hPb (μ * q2C0 (a v) * cnPlus s Φ)
      _ ≤ (1 / (36 * s ^ 2)) * cnPlus s Φ := by
            nlinarith [hlin]
      _ ≤ kinWord N s Φ := hg
  calc
    (4 * π * (a v) / s ^ 3) *
        ((1 / 2 : ℝ) * ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (5 * qcrossC) * (a v) * (((N : ℝ) ^ 2 / s ^ 3) + μ ^ 2 * s ^ 3)
        = (4 * π * (a v) / s ^ 3) *
            ((1 / 2 : ℝ) * ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2
              - (cnPlus s Φ) ^ 2)
          - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
          - (5 * qcrossC) * (a v) * (((N : ℝ) ^ 2 / s ^ 3) + μ ^ 2 * s ^ 3)
          - μ * q2C0 (a v) * cnPlus s Φ
          + ((4 * π * (a v) / s ^ 3) * (cnPlus s Φ) ^ 2
              + μ * q2C0 (a v) * cnPlus s Φ) := by
          ring
    _ ≤ qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ
        + ((4 * π * (a v) / s ^ 3) * (cnPlus s Φ) ^ 2
            + μ * q2C0 (a v) * cnPlus s Φ) := by
          exact add_le_add_left hQ
            ((4 * π * (a v) / s ^ 3) * (cnPlus s Φ) ^ 2 + μ * q2C0 (a v) * cnPlus s Φ)
    _ ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
          nlinarith [herr]


/-- **Per-sector small-box energy bound in corpus form (Xbig killed by the
μ-window)** — the final move of the small-box assembly: from
`energy_smallBox_density` and the particle-density window
`|N̂/s³ − μ| ≤ μδ` (`0 ≤ δ ≤ 1`), the Commons lemma
`window_density_quadratic_bound` bounds `Xbig := N̂²/s³ + μ²s³ ≤
((1+δ)²+1)·μ²s³`, so (multiplying by `−5·qcrossC·(a v) ≤ 0`):

    E_s(Φ) := kinWord + qLHSword
        ≥ (4πa/s³)·(1/2)·U² − 4πaμ²s³(1+1/(2μs³))²
          − 5·qcrossC·(a v)·((1+δ)²+1)·(μ²s³),   U := N̂ − μs³ − ½ .

With `u := N̂/s³` this is the thm:smallbox corpus form
`E_s(Φ) ≥ 2πa·s³·(u−μ−1/(2s³))² − 4πaμ²s³(…)² − C·(a v)·μ²s³`
(up to the deliberate (u,u″)-algebra that converts the `(u−μ−1/(2s³))²`
repulsion into `c(u−μ)²/(1+u/μ)·8πas³`, kept for the dedicated step). -/
lemma smallBoxEnergy_window {N : ℕ} {v : ℝ³ → ℝ} {R s μ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRℓ : R ≤ s * chiR0) (hμ : 0 < μ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1)
    (hwinP : cnPlus s Φ ≤ B)
    (hreg : μ * q2C0 (a v) + (4 * π * (a v) / s ^ 3) * B ≤ 1 / (36 * s ^ 2))
    (hwin : |(N : ℝ) / s ^ 3 - μ| ≤ μ * δ) :
    (4 * π * (a v) / s ^ 3) *
        ((1 / 2 : ℝ) * ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3))
      ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  have hE := energy_smallBox_density hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRℓ hμ hB
    (Φ := Φ) hΦc hnorm hwinP hreg
  have hW := Commons.Analysis.Real.window_density_quadratic_bound (μ := μ) (δ := δ) (d := s ^ 3) (x := (N : ℝ))
    hμ.le hδ0 (pow_pos hs 3) (by positivity : 0 ≤ (N : ℝ)) hwin
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hq0 : 0 ≤ qcrossC := by dsimp [qcrossC]; positivity
  have hfac : 0 ≤ (5 * qcrossC) * (a v) := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hq0) hav
  have hWmul : (5 * qcrossC) * (a v) * (((N : ℝ) ^ 2 / s ^ 3) + μ ^ 2 * s ^ 3)
      ≤ (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3)) :=
    mul_le_mul_of_nonneg_left hW hfac
  nlinarith [hE, hWmul]



/-- **u-form of the per-sector small-box bound** — rewriting
`smallBoxEnergy_window` at the density `u := N̂/s³` and absorbing the
`1/(2s³)`-square-shift error via the μ-window.  Concretely:
`U := N̂ − μs³ − ½ = s³·(u − μ − η)`, `η := 1/(2s³)`, the shifted-square
bound `(u−μ−η)² ≥ (u−μ)² − 2η(u+μ)` and `u ≤ μ(1+δ)` give
`2πa·s³·(u−μ−η)² ≥ 2πa·s³·(u−μ)² − 6πaμ`, so:

    E_s(Φ) ≥ 2πa·s³·(u−μ)² − 6πaμ − 4πaμ²s³(1+1/(2μs³))²
             − 5·qcrossC·(a v)·((1+δ)²+1)·(μ²s³),   u := N̂/s³ . -/
lemma smallBoxEnergy_u_form {N : ℕ} {v : ℝ³ → ℝ} {R s μ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRℓ : R ≤ s * chiR0) (hμ : 0 < μ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1)
    (hwinP : cnPlus s Φ ≤ B)
    (hreg : μ * q2C0 (a v) + (4 * π * (a v) / s ^ 3) * B ≤ 1 / (36 * s ^ 2))
    (hwin : |(N : ℝ) / s ^ 3 - μ| ≤ μ * δ) :
    (2 * π * (a v)) * s ^ 3 * (((N : ℝ) / s ^ 3 - μ) ^ 2)
        - 6 * π * (a v) * μ
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3))
      ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  classical
  let u : ℝ := (N : ℝ) / s ^ 3
  let η : ℝ := 1 / (2 * s ^ 3)
  have hW := smallBoxEnergy_window hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRℓ hμ hB hδ0 hδ1
    (Φ := Φ) hΦc hnorm hwinP hreg hwin
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hηs : 2 * η * s ^ 3 = 1 := by
    dsimp [η]
    field_simp [ne_of_gt hs]
  have hηs' : s ^ 3 * (2 * η) = 1 := by
    rw [mul_comm]
    exact hηs
  -- repulsion rewrite: (4πa/s³)(1/2)(N̂−μs³−½)² = 2πa·s³·(u−μ−η)²
  have hRep : (4 * π * (a v) / s ^ 3) * ((1 / 2 : ℝ) * ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ)) ^ 2)
      = (2 * π * (a v)) * s ^ 3 * ((u - μ - η) ^ 2) := by
    dsimp [u, η]
    have hfac : ((N : ℝ) - μ * s ^ 3 - (1 / 2 : ℝ))
        = s ^ 3 * (((N : ℝ) / s ^ 3) - μ - 1 / (2 * s ^ 3)) := by
      field_simp [ne_of_gt hs] <;> ring
    rw [hfac]
    field_simp [ne_of_gt hs] <;> ring
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hC : 0 ≤ (2 * π * (a v)) * s ^ 3 := by
    exact mul_nonneg (by positivity : 0 ≤ 2 * π * (a v)) (pow_nonneg hs.le 3)
  -- window: |u − μ| ≤ μδ  ⟹  u + μ ≤ μ(2+δ)
  have hwinv : |u - μ| ≤ μ * δ := by
    dsimp [u]
    simpa using hwin
  have huμ : u + μ ≤ μ * (2 + δ) := by
    have hx : u - μ ≤ μ * δ := le_trans (le_abs_self (u - μ)) hwinv
    nlinarith
  -- shifted-square bound (abstract variables)
  have hshift_g : ∀ u μ η : ℝ, 0 ≤ μ → 0 ≤ η →
      (u - μ - η) ^ 2 ≥ (u - μ) ^ 2 - 2 * η * (u + μ) := by
    intro u μ η hμm hηm
    have hdiff : (u - μ - η) ^ 2 - (((u - μ) ^ 2) - 2 * η * (u + μ)) = η ^ 2 + 4 * η * μ := by ring
    have hpos : 0 ≤ η ^ 2 + 4 * η * μ := by
      exact add_nonneg (sq_nonneg η) (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hηm) hμm)
    nlinarith [hdiff, hpos]
  have hshift : (u - μ - η) ^ 2 ≥ (u - μ) ^ 2 - 2 * η * (u + μ) :=
    hshift_g u μ η hμ.le hη0
  -- absorbed shift error: C·(2η)·(u+μ) ≤ 6πaμ   (C := (2πa)s³, via 2ηs³ = 1 and u+μ ≤ 3μ)
  have hbase : ((2 * π * (a v)) * s ^ 3) * (2 * η) = 2 * π * (a v) := by
    calc
      ((2 * π * (a v)) * s ^ 3) * (2 * η) = (2 * π * (a v)) * (s ^ 3 * (2 * η)) := by ring
      _ = (2 * π * (a v)) * 1 := by rw [hηs']
      _ = 2 * π * (a v) := by ring
  have hAbs : ((2 * π * (a v)) * s ^ 3) * (2 * η) * (u + μ) ≤ 6 * π * (a v) * μ := by
    have h6a : 0 ≤ 6 * π * (a v) := by positivity
    have h2pa : 0 ≤ 2 * π * (a v) := by positivity
    calc
      ((2 * π * (a v)) * s ^ 3) * (2 * η) * (u + μ)
          = (2 * π * (a v)) * (u + μ) := by rw [hbase]
      _ ≤ (2 * π * (a v)) * (μ * (2 + δ)) := by
            exact mul_le_mul_of_nonneg_left huμ h2pa
      _ ≤ (2 * π * (a v)) * (μ * 3) := by
            have h23 : μ * (2 + δ) ≤ μ * 3 := by
              have h2d : 2 + δ ≤ 3 := by nlinarith [hδ1]
              exact mul_le_mul_of_nonneg_left h2d hμ.le
            exact mul_le_mul_of_nonneg_left h23 h2pa
      _ = 6 * π * (a v) * μ := by ring
  -- abstract crux: C(u−μ)² − 6πaμ ≤ C(u−μ−η)²
  have hGleH : ((2 * π * (a v)) * s ^ 3) * ((u - μ) ^ 2) - 6 * π * (a v) * μ
      ≤ ((2 * π * (a v)) * s ^ 3) * ((u - μ - η) ^ 2) := by
    have h1 : ((2 * π * (a v)) * s ^ 3) * (((u - μ) ^ 2) - 2 * η * (u + μ))
        ≤ ((2 * π * (a v)) * s ^ 3) * ((u - μ - η) ^ 2) :=
      mul_le_mul_of_nonneg_left hshift hC
    have h1' : ((2 * π * (a v)) * s ^ 3) * (((u - μ) ^ 2) - 2 * η * (u + μ))
        = ((2 * π * (a v)) * s ^ 3) * ((u - μ) ^ 2)
          - ((2 * π * (a v)) * s ^ 3) * (2 * η) * (u + μ) := by ring
    calc
      ((2 * π * (a v)) * s ^ 3) * ((u - μ) ^ 2) - 6 * π * (a v) * μ
          ≤ ((2 * π * (a v)) * s ^ 3) * ((u - μ) ^ 2)
            - ((2 * π * (a v)) * s ^ 3) * (2 * η) * (u + μ) := by
            exact sub_le_sub_left hAbs (((2 * π * (a v)) * s ^ 3) * ((u - μ) ^ 2))
      _ = ((2 * π * (a v)) * s ^ 3) * (((u - μ) ^ 2) - 2 * η * (u + μ)) := h1'.symm
      _ ≤ ((2 * π * (a v)) * s ^ 3) * ((u - μ - η) ^ 2) := h1
  have hW' : ((2 * π * (a v)) * s ^ 3) * ((u - μ - η) ^ 2)
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3))
      ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    rw [hRep] at hW
    exact hW
  calc
    (2 * π * (a v)) * s ^ 3 * (((N : ℝ) / s ^ 3 - μ) ^ 2)
        - 6 * π * (a v) * μ
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3))
        = ((2 * π * (a v)) * s ^ 3) * ((u - μ) ^ 2) - 6 * π * (a v) * μ
          - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
          - (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3)) := by
          dsimp [u]
    _ ≤ ((2 * π * (a v)) * s ^ 3) * ((u - μ - η) ^ 2)
          - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
          - (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3)) := by
          have h1 : ((2 * π * (a v)) * s ^ 3) * ((u - μ) ^ 2) - 6 * π * (a v) * μ
                - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
              ≤ ((2 * π * (a v)) * s ^ 3) * ((u - μ - η) ^ 2)
                - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2 := by
            exact sub_le_sub_right hGleH
              ((4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2)
          exact sub_le_sub_right h1
            ((5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3)))
    _ ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := hW'


/-- **The FS-form denominator factor** (pure real): for `u ≥ 0`, `μ > 0`,
`(u−μ)²/(1+u/μ) ≤ (u−μ)²` — since `1 + u/μ ≥ 1 > 0` and `(u−μ)² ≥ 0`.
Together with `(u−μ)²/(1+u/μ) = μ(u−μ)²/(u+μ)` this is the `μ/(u+μ) ≤ 1`
content that converts the plain square into FS's
`c(u−μ)²/(1+u/μ)` repulsion (no window needed). -/
lemma div_sq_le_sq_of_le_den {u μ : ℝ} (hu : 0 ≤ u) (hμ : 0 < μ) :
    (u - μ) ^ 2 / (1 + u / μ) ≤ (u - μ) ^ 2 := by
  have huμ : 0 ≤ u / μ := div_nonneg hu hμ.le
  have hd : 0 < 1 + u / μ := by nlinarith
  have h1 : 1 ≤ 1 + u / μ := by nlinarith
  rw [div_le_iff₀ hd]
  calc
    (u - μ) ^ 2 = (u - μ) ^ 2 * 1 := by rw [mul_one]
    _ ≤ (u - μ) ^ 2 * (1 + u / μ) := by
          exact mul_le_mul_of_nonneg_left h1 (sq_nonneg (u - μ))



/-- **FS-form per-sector small-box bound** — weakening
`smallBoxEnergy_u_form` via the denominator factor
`(u−μ)²/(1+u/μ) ≤ (u−μ)²` (`div_sq_le_sq_of_le_den`; no window needed, only
`u ≥ 0`, `μ > 0`):

    E_s(Φ) ≥ (1/4)·(u−μ)²/(1+u/μ)·(8πa·s³) − 6πaμ
             − 4πaμ²s³(1+1/(2μs³))² − 5·qcrossC·(a v)·((1+δ)²+1)·(μ²s³),

`u := N̂/s³` — the corpus form of FS thm:smallbox's repulsion
`c(u−μ)²/(1+u/μ)·∬w₁` (c := 1/4) with the error blocks explicit. -/
lemma smallBoxEnergy_fs_form {N : ℕ} {v : ℝ³ → ℝ} {R s μ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRℓ : R ≤ s * chiR0) (hμ : 0 < μ)
    {B δ : ℝ} (hB : 0 ≤ B) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {Φ : X N → ℝ} (hΦc : ContDiff ℝ ∞ Φ)
    (hnorm : (∫ x in abox N s, (Φ x) ^ 2) = 1)
    (hwinP : cnPlus s Φ ≤ B)
    (hreg : μ * q2C0 (a v) + (4 * π * (a v) / s ^ 3) * B ≤ 1 / (36 * s ^ 2))
    (hwin : |(N : ℝ) / s ^ 3 - μ| ≤ μ * δ) :
    (1 / 4) * (8 * π * (a v)) * s ^ 3 *
        (((N : ℝ) / s ^ 3 - μ) ^ 2 / (1 + (N : ℝ) / s ^ 3 / μ))
        - 6 * π * (a v) * μ
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3))
      ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  classical
  let u : ℝ := (N : ℝ) / s ^ 3
  have hU := smallBoxEnergy_u_form hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRℓ hμ hB hδ0 hδ1
    (Φ := Φ) hΦc hnorm hwinP hreg hwin
  have hu : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg (by positivity : 0 ≤ (N : ℝ)) (pow_nonneg hs.le 3)
  have hden := div_sq_le_sq_of_le_den hu hμ
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hC : 0 ≤ (2 * π * (a v)) * s ^ 3 := by
    exact mul_nonneg (by positivity : 0 ≤ 2 * π * (a v)) (pow_nonneg hs.le 3)
  have hcoefmul : (2 * π * (a v)) * s ^ 3 * ((u - μ) ^ 2 / (1 + u / μ))
      ≤ (2 * π * (a v)) * s ^ 3 * ((u - μ) ^ 2) :=
    mul_le_mul_of_nonneg_left hden hC
  have hBnd : (1 / 4) * (8 * π * (a v)) * s ^ 3 *
        ((u - μ) ^ 2 / (1 + u / μ))
        - 6 * π * (a v) * μ
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3))
      ≤ (2 * π * (a v)) * s ^ 3 * ((u - μ) ^ 2)
        - 6 * π * (a v) * μ
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3)) := by
    have hh : (1 / 4) * (8 * π * (a v)) * s ^ 3 * ((u - μ) ^ 2 / (1 + u / μ))
        ≤ (2 * π * (a v)) * s ^ 3 * ((u - μ) ^ 2 / (1 + u / μ)) := by
      ring_nf
      exact le_rfl
    have h1 : (1 / 4) * (8 * π * (a v)) * s ^ 3 * ((u - μ) ^ 2 / (1 + u / μ))
          - 6 * π * (a v) * μ
        ≤ (2 * π * (a v)) * s ^ 3 * ((u - μ) ^ 2 / (1 + u / μ))
          - 6 * π * (a v) * μ := by
      exact sub_le_sub_right hh (6 * π * (a v) * μ)
    have h2 : (1 / 4) * (8 * π * (a v)) * s ^ 3 * ((u - μ) ^ 2 / (1 + u / μ))
          - 6 * π * (a v) * μ
          - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        ≤ (2 * π * (a v)) * s ^ 3 * ((u - μ) ^ 2 / (1 + u / μ))
          - 6 * π * (a v) * μ
          - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2 := by
      exact sub_le_sub_right h1 ((4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2)
    have h23 : (2 * π * (a v)) * s ^ 3 * ((u - μ) ^ 2 / (1 + u / μ))
          - 6 * π * (a v) * μ
          - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        ≤ (2 * π * (a v)) * s ^ 3 * ((u - μ) ^ 2)
          - 6 * π * (a v) * μ
          - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2 := by
      exact sub_le_sub_right (sub_le_sub_right hcoefmul (6 * π * (a v) * μ))
        ((4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2)
    exact sub_le_sub_right (le_trans h2 h23)
      ((5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3)))
  calc
    (1 / 4) * (8 * π * (a v)) * s ^ 3 *
        (((N : ℝ) / s ^ 3 - μ) ^ 2 / (1 + (N : ℝ) / s ^ 3 / μ))
        - 6 * π * (a v) * μ
        - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
        - (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3))
        = (1 / 4) * (8 * π * (a v)) * s ^ 3 *
            ((u - μ) ^ 2 / (1 + u / μ))
          - 6 * π * (a v) * μ
          - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
          - (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3)) := by
          dsimp [u]
    _ ≤ (2 * π * (a v)) * s ^ 3 * ((u - μ) ^ 2)
          - 6 * π * (a v) * μ
          - (4 * π * (a v)) * μ ^ 2 * s ^ 3 * (1 + 1 / (2 * μ * s ^ 3)) ^ 2
          - (5 * qcrossC) * (a v) * (((1 + δ) ^ 2 + 1) * (μ ^ 2 * s ^ 3)) := hBnd
    _ ≤ kinWord N s Φ + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := hU



/-- **Tile-density Jensen** (the per-configuration tile step of the Option-A
window proof): with `nT := Fintype.card ι` tiles of equal volume `V > 0`,
counts `c : ι → ℝ ≥ 0` and a convex `F` on `[0,∞)`,

    F (N̂ / (nT·V)) ≤ (Σ_i F(c_i/V)) / nT ,   N̂ := Σ_i c_i ,

i.e. Jensen with uniform weights `1/nT` over the tile densities `c_i/V`
(instantiated in the window proof with `ι := Fin (m³)`, `V := s³`,
`c_i := n_i`, `F := (1/4)(t−μ)²/(1+t/μ)`-shape — cf.
`Commons.Analysis.Convex.fs_repulsion_convex`).  Pure consequence of
`Commons.Analysis.Convex.finset_uniform_jensen`. -/
lemma tile_density_jensen {ι : Type*} [Fintype ι] [Nonempty ι] {F : ℝ → ℝ} {V : ℝ}
    (hV : 0 < V) (hF : ConvexOn ℝ (Set.Ici (0 : ℝ)) F) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    F ((∑ i : ι, c i) / ((Fintype.card ι : ℝ) * V))
      ≤ (∑ i : ι, F (c i / V)) / (Fintype.card ι : ℝ) := by
  have hx : ∀ i : ι, 0 ≤ c i / V := fun i => div_nonneg (hc i) hV.le
  have hJ := Commons.Analysis.Convex.finset_uniform_jensen hF (fun i : ι => c i / V) hx
  have hcard0 : (Fintype.card ι : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast (ne_of_gt hpos)
  have hV0 : V ≠ 0 := ne_of_gt hV
  have hsumdiv : (∑ i : ι, c i / V) = (∑ i : ι, c i) / V := by
    rw [Finset.sum_div]
  have harg : (∑ i : ι, c i / V) / (Fintype.card ι : ℝ)
      = (∑ i : ι, c i) / ((Fintype.card ι : ℝ) * V) := by
    rw [hsumdiv]
    field_simp [hcard0, hV0]
  rwa [harg] at hJ



/-- **Tile-repulsion mass lower bound** (step-2 sub-lemma): with `nT :=
Fintype.card ι` tiles of volume `V > 0`, `ℓ³ = nT·V`, counts `c_i ≥ 0` with
`Σc_i = N̂`, and convex `F` on `[0,∞)`:

    nT·V·F(N̂/ℓ³) ≤ V·Σ_i F(c_i/V)   (equivalently Σ_i V·F(c_i/V) ≥ ℓ³·F(N̂/ℓ³))

i.e. the total per-tile repulsion mass dominates the big-box repulsion at the
total density.  (Instantiations: `F := (1/4)(t−μ)²/(1+t/μ)` via
`fs_repulsion_convex`; in the window proof this is the per-configuration
content feeding `⟨Φ, Σ_j s³F(n_j/s³)·8πa⟩ ≥ 8πa·ℓ³·F(N̂/ℓ³)`.) -/
lemma tile_repulsion_mass {ι : Type*} [Fintype ι] [Nonempty ι] {F : ℝ → ℝ} {V Ntot : ℝ}
    (hV : 0 < V) (hF : ConvexOn ℝ (Set.Ici (0 : ℝ)) F) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hsum : (∑ i : ι, c i) = Ntot) :
    (Fintype.card ι : ℝ) * V * F (Ntot / ((Fintype.card ι : ℝ) * V))
      ≤ V * (∑ i : ι, F (c i / V)) := by
  have hT := tile_density_jensen hV hF c hc
  rw [hsum] at hT
  have hcardPos : 0 < (Fintype.card ι : ℝ) := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast hpos
  have hcard0 : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcardPos
  have hmul : (Fintype.card ι : ℝ) * V * F (Ntot / ((Fintype.card ι : ℝ) * V))
      ≤ (Fintype.card ι : ℝ) * V * ((∑ i : ι, F (c i / V)) / (Fintype.card ι : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hT (mul_nonneg hcardPos.le hV.le)
  have hrhs : (Fintype.card ι : ℝ) * V * ((∑ i : ι, F (c i / V)) / (Fintype.card ι : ℝ))
      = V * (∑ i : ι, F (c i / V)) := by
    field_simp [hcard0]
  rwa [hrhs] at hmul

end BoseGases

end Submission
