import Submission.Work.FrontierLine

open OptimalMoebius Filter Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Distinct flat components do not touch inside the strip (ComponentSeparation)

THEOREM (`flatComponents_no_common_stripInterior_closure`): two distinct
flat components `C₁ = flatComponent f p₁`, `C₂ = flatComponent f p₂`
(`flatComponent f p₂ ≠ flatComponent f p₁`) of an embedded paper band
have no common closure point in the strip interior:

    ∀ e ∈ stripInterior, e ∉ closure C₁ ∩ closure C₂ .

Proof structure (each ingredient green):
* distinct components of the open set `interior (FlatSet f)` are disjoint
  (`flatComponents_disjoint`, via `connectedComponentIn_eq`);
* if `e ∈ closure C₁ ∩ closure C₂` then (open-component argument) `e` is
  in the FRONTIER of both; take the half-disk data at `e`
  (`degenerate_frontier_half_disk`): `Cᵢ ∩ B(e,ρᵢ) = {φᵢ < 0} ∩ B(e,ρᵢ)`,
  `φᵢ := signedLineFunc e wᵢ`, unit `wᵢ`, `ρ := min ρ₁ ρ₂`;
* generic chord membership (`chord_mem_frontier_of_halfdisk`, ⊇ direction
  of the frontier-chord statement, with EXPLICIT half-disk data): a point
  of `B(e,ρᵢ)` with `φᵢ = 0` is a frontier point of `Cᵢ` (walk in the
  perpendicular direction into the `φᵢ < 0` half) — so no `Cⱼ`-point
  (flat-interior) can lie on the chord `φᵢ = 0`;
* side analysis: `C₂ ∩ B(e,ρ) ⊆ {φ₁ > 0}` and `C₁ ∩ B(e,ρ) ⊆ {φ₂ > 0}`
  (points on the `φ₁ ≤ 0` side of the chord through `e` would be in `C₁`
  or on its frontier, both contradicting `q ∈ C₂ ⊆ interior (FlatSet f)`),
  and each `Cᵢ` FILLS its half-disk, so the half-planes `{φᵢ < 0}`
  cannot overlap in `B(e,ρ)`; a common wedge point (both `φᵢ < 0`) would
  exist unless `det2 w₁ w₂ = 0` — hence `w₂ = ±w₁` (`unit_eq_or_neg_of_det2_eq_zero`);
* `w₂ = w₁` contradicts the inclusions; so `w₂ = -w₁` and
  `C₂ ∩ B(e,ρ) = {φ₁ > 0} ∩ B(e,ρ)`: the two open halves of `B(e,ρ)` are
  both flat (`dN = 0`; chord points are flat by
  `flatComponent_frontier_subset_FlatSet`), so `e` is flat-interior —
  contradicting `flatComponent_frontier_not_flat_interior`.

Downstream: this is the first global fact about the arrangement of flat
pieces (step T1-i of the component → `FlatSideData` correspondence): flat
components are isolated from each other inside the strip; every frontier
side of a flat component borders `U` or the seam only.

Build: `lake build Submission.Work.ComponentSeparation` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- Distinct flat components of the same band are disjoint: a point of
`flatComponent f p₁` cannot belong to `flatComponent f p₂` when the two
components are different. -/
lemma flatComponents_disjoint {f : ℝ² → ℝ³} {p₁ p₂ z : ℝ²}
    (hne : flatComponent f p₂ ≠ flatComponent f p₁) (hz₁ : z ∈ flatComponent f p₁) :
    z ∉ flatComponent f p₂ := by
  intro hz₂
  apply hne
  have h₁ : connectedComponentIn (interior (FlatSet f)) p₁ =
      connectedComponentIn (interior (FlatSet f)) z := by
    exact connectedComponentIn_eq hz₁
  have h₂ : connectedComponentIn (interior (FlatSet f)) p₂ =
      connectedComponentIn (interior (FlatSet f)) z := by
    exact connectedComponentIn_eq hz₂
  dsimp [flatComponent]
  rw [h₁, ← h₂]

/-- **Chord membership (⊇ direction, explicit data)**: with half-disk data
at `e` for an OPEN `C` (`z ∈ C ↔ φ_e z < 0` inside `B(e,ρ)`, `φ_e z :=
signedLineFunc e w z`, `w` unit), any point `q ∈ B(e,ρ)` with `φ_e q = 0`
lies on the frontier of `C`.  Generic over any open `C`; the proof walks
from `q` a small distance in the unit perpendicular direction
`n := (−w₁, w₀)` (where `φ` decreases) into the `φ < 0` half, which is
inside `C` (the half-disk) and arbitrarily close to `q`. -/
lemma chord_mem_frontier_of_halfdisk {C : Set ℝ²} (hCopen : IsOpen C) {e w : ℝ²} {ρ : ℝ}
    (hw₁ : ‖w‖ = 1)
    (heq : ∀ z : ℝ², z ∈ Metric.ball e ρ → (z ∈ C ↔ signedLineFunc e w z < 0))
    {q : ℝ²} (hqb : q ∈ Metric.ball e ρ) (hφ0 : signedLineFunc e w q = 0) :
    q ∈ frontier C := by
  constructor
  · -- q ∈ closure C
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hqe : dist q e < ρ := (Metric.mem_ball.mp hqb)
    let n : ℝ² := !₂[-(w 1), w 0]
    have hnn₁ : ‖n‖ = 1 := by
      dsimp [n]
      exact norm_perp_rot hw₁
    have hdetn : det2 n w < 0 := by
      dsimp [n]
      exact det2_perp_rot_neg hw₁
    let t : ℝ := min (ε / 2) ((ρ - dist q e) / 2)
    have htpos : 0 < t := by
      dsimp [t]
      exact lt_min (by linarith) (by linarith)
    let c : ℝ² := q + t • n
    have hdist : dist q c < ε := by
      dsimp [c]
      have hzcn : ‖q - (q + t • n)‖ = t * ‖n‖ := by
        rw [show q - (q + t • n) = -(t • n) by abel]
        rw [norm_neg]
        rw [norm_smul]
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (le_of_lt htpos)]
      have hmain : ‖q - (q + t • n)‖ = t := by
        rw [hzcn, hnn₁]
        ring
      have hε₂ : t < ε := by
        dsimp [t]
        have hmin : min (ε / 2) ((ρ - dist q e) / 2) ≤ ε / 2 := min_le_left _ _
        have hhalf : ε / 2 < ε := by linarith
        exact lt_of_le_of_lt hmin hhalf
      rw [dist_eq_norm]
      rw [hmain]
      exact hε₂
    have hce : dist c e < ρ := by
      have htria : dist c e ≤ dist c q + dist q e := dist_triangle c q e
      have hcz : dist c q = t := by
        dsimp [c]
        have hzcn : ‖(q + t • n) - q‖ = t * ‖n‖ := by
          rw [show (q + t • n) - q = t • n by abel]
          rw [norm_smul]
          rw [Real.norm_eq_abs]
          rw [abs_of_nonneg (le_of_lt htpos)]
        have hmain : ‖(q + t • n) - q‖ = t := by
          rw [hzcn, hnn₁]
          ring
        rw [dist_eq_norm]
        rw [hmain]
      have ht₂ : t ≤ (ρ - dist q e) / 2 := min_le_right (ε / 2) ((ρ - dist q e) / 2)
      nlinarith [htria, hcz, ht₂, hqe]
    have hcball : c ∈ Metric.ball e ρ := (Metric.mem_ball.mpr hce)
    have hφc : signedLineFunc e w c < 0 := by
      have hlin := signedLineFunc_add_smul e w q n t
      have hdetmul : t * det2 n w < 0 := by
        exact mul_neg_of_pos_of_neg htpos hdetn
      rw [hlin, hφ0, zero_add]
      exact hdetmul
    have hcC : c ∈ C := (heq c hcball).mpr hφc
    exact ⟨c, hcC, hdist⟩
  · -- q ∉ interior C (C open, and q ∈ C would give φ q < 0)
    intro hint
    have hqC : q ∈ C := by rwa [hCopen.interior_eq] at hint
    have hφlt : signedLineFunc e w q < 0 := (heq q hqb).1 hqC
    linarith

/-- **Main separation theorem**: two distinct flat components of an
embedded paper Möbius band have no common closure point in the strip
interior. -/
theorem flatComponents_no_common_stripInterior_closure {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p₁ p₂ : ℝ²}
    (hne : flatComponent f p₂ ≠ flatComponent f p₁) :
    ∀ e : ℝ², e ∈ stripInterior → e ∉ closure (flatComponent f p₁) ∩ closure (flatComponent f p₂) := by
  intro e heS hecl
  rcases hecl with ⟨hecl₁, hecl₂⟩
  by_cases he₁ : e ∈ flatComponent f p₁
  · -- e ∈ open C₁: a ball around e (⊆ C₁) must meet C₂, contradiction
    rcases (Metric.isOpen_iff.mp (isOpen_flatComponent f p₁) e he₁) with ⟨δ, hδ, hδball⟩
    rcases (Metric.mem_closure_iff.mp hecl₂) δ hδ with ⟨c, hcC₂, hce⟩
    have hcC₁ : c ∈ flatComponent f p₁ := hδball (Metric.mem_ball.mpr (by simpa [dist_comm] using hce))
    exact (flatComponents_disjoint (p₁ := p₁) (p₂ := p₂) hne hcC₁) hcC₂
  · by_cases he₂ : e ∈ flatComponent f p₂
    · -- symmetric
      rcases (Metric.isOpen_iff.mp (isOpen_flatComponent f p₂) e he₂) with ⟨δ, hδ, hδball⟩
      rcases (Metric.mem_closure_iff.mp hecl₁) δ hδ with ⟨c, hcC₁, hce⟩
      have hcC₂ : c ∈ flatComponent f p₂ := hδball (Metric.mem_ball.mpr (by simpa [dist_comm] using hce))
      exact (flatComponents_disjoint (p₁ := p₂) (p₂ := p₁) (by
        intro h; exact hne h.symm) hcC₂) hcC₁
    · -- e is on the frontier of both components
      have heF₁ : e ∈ frontier (flatComponent f p₁) := by
        change e ∈ closure (flatComponent f p₁) ∧ e ∉ interior (flatComponent f p₁)
        constructor
        · exact hecl₁
        · intro hint
          exact he₁ ((isOpen_flatComponent f p₁).interior_eq ▸ hint)
      have heF₂ : e ∈ frontier (flatComponent f p₂) := by
        change e ∈ closure (flatComponent f p₂) ∧ e ∉ interior (flatComponent f p₂)
        constructor
        · exact hecl₂
        · intro hint
          exact he₂ ((isOpen_flatComponent f p₂).interior_eq ▸ hint)
      rcases degenerate_frontier_half_disk hf ha heS heF₁ with ⟨w₁, ρ₁, hw₁₁, hρ₁, hballS₁, hiff₁⟩
      rcases degenerate_frontier_half_disk hf ha heS heF₂ with ⟨w₂, ρ₂, hw₂₂, hρ₂, hballS₂, hiff₂⟩
      let ρ : ℝ := min ρ₁ ρ₂
      have hρ : 0 < ρ := by dsimp [ρ]; exact lt_min hρ₁ hρ₂
      have hρle₁ : ρ ≤ ρ₁ := by dsimp [ρ]; exact min_le_left ρ₁ ρ₂
      have hρle₂ : ρ ≤ ρ₂ := by dsimp [ρ]; exact min_le_right ρ₁ ρ₂
      have hball₁ : ∀ q : ℝ², q ∈ Metric.ball e ρ → q ∈ Metric.ball e ρ₁ := by
        intro q hq
        exact (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hq) hρle₁))
      have hball₂ : ∀ q : ℝ², q ∈ Metric.ball e ρ → q ∈ Metric.ball e ρ₂ := by
        intro q hq
        exact (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hq) hρle₂))
      -- C₂-points in B(e,ρ) are strictly on the φ₁ > 0 side
      have hA : ∀ q : ℝ², q ∈ flatComponent f p₂ → q ∈ Metric.ball e ρ →
          0 < signedLineFunc e w₁ q := by
        intro q hqC₂ hqball
        have hqball₁ : q ∈ Metric.ball e ρ₁ := hball₁ q hqball
        have hqS : q ∈ stripInterior := (flatComponent_subset_stripInterior f p₂) hqC₂
        have hnotlt : ¬ signedLineFunc e w₁ q < 0 := by
          intro hlt
          have hqC₁ : q ∈ flatComponent f p₁ := (hiff₁ q hqball₁).mpr hlt
          exact (flatComponents_disjoint (p₁ := p₁) (p₂ := p₂) hne hqC₁) hqC₂
        have hnot0 : signedLineFunc e w₁ q ≠ 0 := by
          intro h0
          have hqfront : q ∈ frontier (flatComponent f p₁) :=
            chord_mem_frontier_of_halfdisk (C := flatComponent f p₁) (isOpen_flatComponent f p₁)
              (w := w₁) (ρ := ρ₁) hw₁₁ hiff₁ hqball₁ h0
          have hni : ¬ IsFlatInterior f q :=
            flatComponent_frontier_not_flat_interior (f := f) (p := p₁) (z := q) hqS hqfront
          have hfi : IsFlatInterior f q := flatComponent_mem_flatInterior (f := f) (p := p₂) hqC₂
          exact hni hfi
        have hge : 0 ≤ signedLineFunc e w₁ q := le_of_not_gt hnotlt
        have hne0 : 0 ≠ signedLineFunc e w₁ q := by
          intro hz
          exact hnot0 hz.symm
        exact lt_of_le_of_ne hge hne0
      -- C₁-points in B(e,ρ) are strictly on the φ₂ > 0 side
      have hB : ∀ q : ℝ², q ∈ flatComponent f p₁ → q ∈ Metric.ball e ρ →
          0 < signedLineFunc e w₂ q := by
        intro q hqC₁ hqball
        have hqball₂ : q ∈ Metric.ball e ρ₂ := hball₂ q hqball
        have hqS : q ∈ stripInterior := (flatComponent_subset_stripInterior f p₁) hqC₁
        have hnotlt : ¬ signedLineFunc e w₂ q < 0 := by
          intro hlt
          have hqC₂ : q ∈ flatComponent f p₂ := (hiff₂ q hqball₂).mpr hlt
          exact (flatComponents_disjoint (p₁ := p₂) (p₂ := p₁) (by
            intro h; exact hne h.symm) hqC₂) hqC₁
        have hnot0 : signedLineFunc e w₂ q ≠ 0 := by
          intro h0
          have hqfront : q ∈ frontier (flatComponent f p₂) :=
            chord_mem_frontier_of_halfdisk (C := flatComponent f p₂) (isOpen_flatComponent f p₂)
              (w := w₂) (ρ := ρ₂) hw₂₂ hiff₂ hqball₂ h0
          have hni : ¬ IsFlatInterior f q :=
            flatComponent_frontier_not_flat_interior (f := f) (p := p₂) (z := q) hqS hqfront
          have hfi : IsFlatInterior f q := flatComponent_mem_flatInterior (f := f) (p := p₁) hqC₁
          exact hni hfi
        have hge : 0 ≤ signedLineFunc e w₂ q := le_of_not_gt hnotlt
        have hne0 : 0 ≠ signedLineFunc e w₂ q := by
          intro hz
          exact hnot0 hz.symm
        exact lt_of_le_of_ne hge hne0
      -- C₁ fills its half-disk in B(e,ρ), and those points have φ₂ > 0
      have h₁₂ : ∀ q : ℝ², q ∈ Metric.ball e ρ → signedLineFunc e w₁ q < 0 →
          0 < signedLineFunc e w₂ q := by
        intro q hqball hφ₁lt
        have hqC₁ : q ∈ flatComponent f p₁ := (hiff₁ q (hball₁ q hqball)).mpr hφ₁lt
        exact hB q hqC₁ hqball
      -- C₂ fills its half-disk in B(e,ρ), and those points have φ₁ > 0
      have h₂₁ : ∀ q : ℝ², q ∈ Metric.ball e ρ → signedLineFunc e w₂ q < 0 →
          0 < signedLineFunc e w₁ q := by
        intro q hqball hφ₂lt
        have hqC₂ : q ∈ flatComponent f p₂ := (hiff₂ q (hball₂ q hqball)).mpr hφ₂lt
        exact hA q hqC₂ hqball
      -- the two chord lines through e coincide
      have hΔ0 : det2 w₁ w₂ = 0 := by
        by_contra hΔne
        -- wedge point: both φ₁, φ₂ < 0 inside B(e,ρ)
        let Δ : ℝ := det2 w₁ w₂
        have hΔne' : Δ ≠ 0 := by dsimp [Δ]; exact hΔne
        let u : ℝ² := (-1 / Δ) • w₁ + (1 / Δ) • w₂
        have hdu₁eq : det2 u w₁ = -1 := by
          dsimp [u, Δ]
          have h₁a : det2 ((-1 / det2 w₁ w₂) • w₁) w₁ = (-1 / det2 w₁ w₂) * det2 w₁ w₁ :=
            det2_smul_left (-1 / det2 w₁ w₂) w₁ w₁
          have h₂a : det2 ((1 / det2 w₁ w₂) • w₂) w₁ = (1 / det2 w₁ w₂) * det2 w₂ w₁ :=
            det2_smul_left (1 / det2 w₁ w₂) w₂ w₁
          rw [det2_add_left]
          rw [h₁a, h₂a]
          simp [det2_self]
          have h₂b : det2 w₂ w₁ = -det2 w₁ w₂ := det2_antisymm w₂ w₁
          rw [h₂b]
          field_simp [hΔne]
        have hdu₁ : det2 u w₁ < 0 := by
          rw [hdu₁eq]
          norm_num
        have hdu₂eq : det2 u w₂ = -1 := by
          dsimp [u, Δ]
          have h₁a : det2 ((-1 / det2 w₁ w₂) • w₁) w₂ = (-1 / det2 w₁ w₂) * det2 w₁ w₂ :=
            det2_smul_left (-1 / det2 w₁ w₂) w₁ w₂
          have h₂a : det2 ((1 / det2 w₁ w₂) • w₂) w₂ = (1 / det2 w₁ w₂) * det2 w₂ w₂ :=
            det2_smul_left (1 / det2 w₁ w₂) w₂ w₂
          rw [det2_add_left]
          rw [h₁a, h₂a]
          simp [det2_self]
          field_simp [hΔne]
        have hdu₂ : det2 u w₂ < 0 := by
          rw [hdu₂eq]
          norm_num
        -- z := e + t•u in B(e,ρ) with both φᵢ z < 0
        let t : ℝ := ρ / (2 * (‖u‖ + 1))
        have htpos : 0 < t := by
          dsimp [t]
          exact div_pos hρ (by nlinarith [norm_nonneg u])
        let z : ℝ² := e + t • u
        have hmain : ‖(e + t • u) - e‖ = t * ‖u‖ := by
          rw [show (e + t • u) - e = t • u by abel]
          rw [norm_smul]
          rw [Real.norm_eq_abs]
          rw [abs_of_nonneg (le_of_lt htpos)]
        have hltρ : t * ‖u‖ < ρ := by
          have hden : 0 < ‖u‖ + 1 := by nlinarith [norm_nonneg u]
          have hfrac : ‖u‖ / (‖u‖ + 1) < 1 := by
            rw [div_lt_one hden]
            linarith
          have hhalf : (ρ / 2) * (‖u‖ / (‖u‖ + 1)) < ρ / 2 := by
            simpa using (mul_lt_mul_of_pos_left hfrac (half_pos hρ))
          have heq : t * ‖u‖ = (ρ / 2) * (‖u‖ / (‖u‖ + 1)) := by
            dsimp [t]
            field_simp [hden]
          rw [heq]
          linarith
        have hzball : z ∈ Metric.ball e ρ := by
          rw [Metric.mem_ball]
          rw [dist_eq_norm]
          dsimp [z]
          rw [hmain]
          exact hltρ
        have hφ₁z : signedLineFunc e w₁ z < 0 := by
          have hzd : z - e = t • u := by dsimp [z]; abel
          calc
            signedLineFunc e w₁ z = det2 (z - e) w₁ := signedLineFunc_eq_det2 e w₁ z
            _ = det2 (t • u) w₁ := by rw [hzd]
            _ = t * det2 u w₁ := by rw [det2_smul_left]
            _ < 0 := mul_neg_of_pos_of_neg htpos hdu₁
        have hφ₂z : signedLineFunc e w₂ z < 0 := by
          have hzd : z - e = t • u := by dsimp [z]; abel
          calc
            signedLineFunc e w₂ z = det2 (z - e) w₂ := signedLineFunc_eq_det2 e w₂ z
            _ = det2 (t • u) w₂ := by rw [hzd]
            _ = t * det2 u w₂ := by rw [det2_smul_left]
            _ < 0 := mul_neg_of_pos_of_neg htpos hdu₂
        have hgt : 0 < signedLineFunc e w₂ z := h₁₂ z hzball hφ₁z
        linarith
      rcases unit_eq_or_neg_of_det2_eq_zero hw₁₁ hw₂₂ hΔ0 with hpar₁ | hpar₂
      · -- w₁ = w₂: a C₁-point in B(e,ρ) would need φ₂ > 0 = φ₁ < 0
        rcases (Metric.mem_closure_iff.mp hecl₁) ρ hρ with ⟨c, hcC₁, hce⟩
        have hcball : c ∈ Metric.ball e ρ :=
          (Metric.mem_ball.mpr (by simpa [dist_comm] using hce))
        have hφ₁c : signedLineFunc e w₁ c < 0 := (hiff₁ c (hball₁ c hcball)).1 hcC₁
        have hφ₂cgt : 0 < signedLineFunc e w₂ c := hB c hcC₁ hcball
        have hφ₂c : signedLineFunc e w₂ c = signedLineFunc e w₁ c := by rw [hpar₁]
        linarith
      · -- w₂ = -w₁: the two open halves of B(e,ρ) are both flat, so e is flat-interior
        have hswap : w₂ = -w₁ := by
          have : -w₁ = w₂ := by rw [hpar₂]; simp
          exact this.symm
        have hzflat : ∀ z : ℝ², z ∈ Metric.ball e ρ → z ∈ FlatSet f := by
          intro z hzball
          have hzS : z ∈ stripInterior := hballS₁ (hball₁ z hzball)
          by_cases hz0 : signedLineFunc e w₁ z = 0
          · have hzfront : z ∈ frontier (flatComponent f p₁) :=
              chord_mem_frontier_of_halfdisk (C := flatComponent f p₁) (isOpen_flatComponent f p₁)
                (w := w₁) (ρ := ρ₁) hw₁₁ hiff₁ (hball₁ z hzball) hz0
            exact flatComponent_frontier_subset_FlatSet hf hzS hzfront
          · rcases lt_or_gt_of_ne hz0 with hlt | hgt
            · have hzC₁ : z ∈ flatComponent f p₁ := (hiff₁ z (hball₁ z hzball)).mpr hlt
              exact ⟨hzS, flatComponent_flat (f := f) (p := p₁) hzC₁⟩
            · have hφ₂lt : signedLineFunc e w₂ z < 0 := by
                rw [hswap]
                rw [signedLineFunc_neg e w₁ z]
                linarith
              have hzC₂ : z ∈ flatComponent f p₂ := (hiff₂ z (hball₂ z hzball)).mpr hφ₂lt
              exact ⟨hzS, flatComponent_flat (f := f) (p := p₂) hzC₂⟩
        have heint : e ∈ interior (FlatSet f) := by
          rw [mem_interior]
          refine ⟨Metric.ball e ρ, ?_, ?_⟩
          · intro z hz
            exact hzflat z hz
          · exact ⟨Metric.isOpen_ball, Metric.mem_ball_self hρ⟩
        have hefi : IsFlatInterior f e :=
          (IsFlatInterior_iff_mem_interior_FlatSet (f := f) heS).2 heint
        exact (flatComponent_frontier_not_flat_interior (f := f) (p := p₁) (z := e) heS heF₁) hefi

end Submission.PaperBand
