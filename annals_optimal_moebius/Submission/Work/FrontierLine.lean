import Submission.Work.FrontierArc
import Submission.Work.FrontierChord

open OptimalMoebius Filter Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Frontier arcs of a flat component lie on single straight lines (FrontierLine)

This file carries the pointwise (r2) structure (FrontierChord) to the
ARC level: **any preconnected set `K` of frontier points of a flat
component `C = flatComponent f p`, carrying the half-disk data
`(w e, ρ e)` of `SectorFill`/Target (A), is contained in one straight
line**.  Concretely `frontier_arc_on_line` gives `∃ u c, ‖u‖=1 ∧
∀ e ∈ K, signedLineFunc c u e = 0` — every point of `K` lies on the
single line through `c` in direction `u`; and the data-free version
`frontier_arc_on_line_of_strip` instantiates the half-disk data (choice
over `degenerate_frontier_half_disk`) for any preconnected
`K ⊆ stripInterior ∩ frontier C`.

Proof structure (all pieces green):
* **local chord ⊆** (`frontier_mem_chord_of_halfdisk`, generic over any
  OPEN `C`): from the half-disk data at `x` (`z ∈ C ↔ φ_x z < 0` inside
  `B(x,ρ)`), every frontier point `y` of `C` inside `B(x,ρ)` satisfies
  `φ_x y = 0` — the two-sided argument: `y ∉ C` (C open) gives `φ ≥ 0`;
  `y ∈ closure C` plus continuity of `φ` (a small ball around `y` inside
  `{φ > 0} ∩ B(x,ρ)` would contain no `C`-point) gives `φ ≤ 0`.
* **locally constant on preconnected is constant** (generic
  `preconnected_of_locallyConstant_prop`, metric version with per-point
  radii): the class sets `A := {x | x ∈ K ∧ P x}` and
  `B := {x | x ∈ K ∧ ¬ P x}` are each `K ∩ (union of balls)`, hence
  relatively open, cover `K`; `IsPreconnected K` forbids both nonempty.
* **assembly** (`frontier_arc_on_line`): fix `e₀ ∈ K` and put
  `φ₀ z := signedLineFunc e₀ (w e₀) z`.  For `x, y ∈ K` with
  `y ∈ B(x, ρ x)`: the local chord gives `φ_x y = 0`, and Target (A)
  gives `w x = ± w e₀`, so (via `signedLineFunc_shift`/`_neg`) the zero
  set of `φ_x` is the level set `{φ₀ = φ₀ x}`; hence
  `φ₀ y = 0 ↔ φ₀ x = 0` — the predicate `P := (φ₀ = 0)` is locally
  constant on `K`.  Since `P e₀` holds (`signedLineFunc_self`), the
  preconnected-constant lemma gives `P e` for every `e ∈ K`.

Downstream use: the sides of `C` (connected frontier arcs toward `U`)
are straight segments on the lines so obtained; this is the first step
of the component → `FlatSideData` correspondence of the flat foliation.

Build: `lake build Submission.Work.FrontierLine` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- **Local chord ⊆**: with half-disk data at `x` for an open set `C`
(`z ∈ C ↔ φ_x z < 0` inside `B(x,ρ)`), every frontier point of `C` within
`B(x,ρ)` lies on the chord `φ_x = 0`.  Generic over any open `C : Set ℝ²`;
the two-sided argument uses only openness of `C`, closure membership from
`frontier`, and continuity of `φ_x`. -/
lemma frontier_mem_chord_of_halfdisk {C : Set ℝ²} (hCopen : IsOpen C) {x : ℝ²}
    {w : ℝ²} {ρ : ℝ}
    (heq : ∀ z : ℝ², z ∈ Metric.ball x ρ → (z ∈ C ↔ signedLineFunc x w z < 0))
    {y : ℝ²} (hyF : y ∈ frontier C) (hyb : y ∈ Metric.ball x ρ) :
    signedLineFunc x w y = 0 := by
  have hyF' : y ∈ closure C ∧ y ∉ interior C := by
    change y ∈ closure C ∧ y ∉ interior C at hyF
    exact hyF
  -- 0 ≤ φ y : y ∉ C, and φ<0 would put y in C
  have hge : 0 ≤ signedLineFunc x w y := by
    by_contra hlt
    have hφlt : signedLineFunc x w y < 0 := lt_of_not_ge hlt
    have hyC : y ∉ C := by
      intro hcin
      apply hyF'.2
      rwa [hCopen.interior_eq]
    exact hyC ((heq y hyb).mpr hφlt)
  -- φ y ≤ 0 : y ∈ closure C; if 0 < φ y, a small ball around y has no C point
  have hle : signedLineFunc x w y ≤ 0 := by
    by_contra hgt
    have hφgt : 0 < signedLineFunc x w y := lt_of_not_ge hgt
    have hcont : ContinuousAt (fun z : ℝ² => signedLineFunc x w z) y :=
      (continuous_signedLineFunc x w).continuousAt
    have hevpos : ∀ᶠ z in 𝓝 y, 0 < signedLineFunc x w z := by
      change (fun z : ℝ² => signedLineFunc x w z) ⁻¹' Set.Ioi 0 ∈ 𝓝 y
      exact hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds
        (show (0 : ℝ) < signedLineFunc x w y from hφgt))
    rcases (Metric.eventually_nhds_iff.mp hevpos) with ⟨δ, hδ, hδpos⟩
    have hybx : dist y x < ρ := (Metric.mem_ball.mp hyb)
    let ε₂ : ℝ := (ρ - dist y x) / 2
    have hε₂p : 0 < ε₂ := by dsimp [ε₂]; linarith
    let ε : ℝ := min δ ε₂
    have hεp : 0 < ε := lt_min hδ hε₂p
    have hcl := (Metric.mem_closure_iff.mp hyF'.1) ε hεp
    rcases hcl with ⟨c, hcC, hyc⟩
    -- dist c y < δ (symmetry + ε ≤ δ)
    have hcyδ : dist c y < δ := by
      rw [dist_comm]
      exact lt_of_lt_of_le hyc (min_le_left δ ε₂)
    have hcpos : 0 < signedLineFunc x w c := hδpos hcyδ
    -- c ∈ ball x ρ (triangle + ε₂ bound)
    have hcxρ : dist c x < ρ := by
      have htria : dist c x ≤ dist c y + dist y x := dist_triangle c y x
      have hcz : dist c y < (ρ - dist y x) / 2 := by
        rw [dist_comm]
        exact lt_of_lt_of_le hyc (min_le_right δ ((ρ - dist y x) / 2))
      nlinarith
    have hcball : c ∈ Metric.ball x ρ := (Metric.mem_ball.mpr hcxρ)
    have hcneg : signedLineFunc x w c < 0 := (heq c hcball).1 hcC
    linarith
  exact le_antisymm hle hge

/-- **Locally constant on a preconnected set is constant** (metric form,
with per-point radii): if a predicate `P` is such that every `K`-point has
a radius on which `P` agrees with all neighbouring `K`-points, then `P`
takes a single truth value on `K` (the class sets `A = {P}`, `B = {¬P}`
are relatively open, disjoint, cover `K`, and `IsPreconnected K` forbids
two nonempty such pieces). -/
lemma preconnected_of_locallyConstant_prop {K : Set ℝ²} (hKpre : IsPreconnected K)
    {P : ℝ² → Prop} {r : ℝ² → ℝ}
    (hr : ∀ x, x ∈ K → 0 < r x)
    (hloc : ∀ (x y : ℝ²), x ∈ K → y ∈ K → y ∈ Metric.ball x (r x) → (P y ↔ P x)) :
    ∀ x, x ∈ K → ∀ y, y ∈ K → (P x ↔ P y) := by
  let A : Set ℝ² := {x | x ∈ K ∧ P x}
  let B : Set ℝ² := {x | x ∈ K ∧ ¬ P x}
  let Uₐ : Set ℝ² := {x | ∃ a ∈ A, x ∈ Metric.ball a (r a)}
  let Ub : Set ℝ² := {x | ∃ b ∈ B, x ∈ Metric.ball b (r b)}
  have hAeq : A = K ∩ Uₐ := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, x, hx, Metric.mem_ball_self (hr x hx.1)⟩
    · intro x hx
      rcases hx with ⟨hxK, hxU⟩
      rcases hxU with ⟨a, haA, hxball⟩
      refine ⟨hxK, ?_⟩
      have hxy := hloc a x haA.1 hxK hxball
      exact hxy.mpr haA.2
  have hBeq : B = K ∩ Ub := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, x, hx, Metric.mem_ball_self (hr x hx.1)⟩
    · intro x hx
      rcases hx with ⟨hxK, hxU⟩
      rcases hxU with ⟨b, hbB, hxball⟩
      refine ⟨hxK, ?_⟩
      intro hxA
      have hxy := hloc b x hbB.1 hxK hxball
      exact hbB.2 (hxy.mp hxA)
  have hUopenₐ : IsOpen Uₐ := by
    rw [show Uₐ = ⋃ a ∈ A, Metric.ball a (r a) by
      ext x
      simp [Uₐ]]
    exact isOpen_biUnion (fun a ha => Metric.isOpen_ball)
  have hUopenb : IsOpen Ub := by
    rw [show Ub = ⋃ b ∈ B, Metric.ball b (r b) by
      ext x
      simp [Ub]]
    exact isOpen_biUnion (fun b hb => Metric.isOpen_ball)
  have hcov : K ⊆ Uₐ ∪ Ub := by
    intro x hxK
    by_cases hxA : P x
    · left
      refine ⟨x, ⟨hxK, hxA⟩, Metric.mem_ball_self (hr x hxK)⟩
    · right
      refine ⟨x, ⟨hxK, hxA⟩, Metric.mem_ball_self (hr x hxK)⟩
  intro x hxK y hyK
  by_cases hPx : P x
  · -- P x true: every K-point has P true (else B ∋ y nonempty alongside A ∋ x)
    have hPy' : P y := by
      by_contra hnot
      have hAne : (K ∩ Uₐ).Nonempty := by
        rw [← hAeq]
        exact ⟨x, ⟨hxK, hPx⟩⟩
      have hBne : (K ∩ Ub).Nonempty := by
        rw [← hBeq]
        exact ⟨y, ⟨hyK, hnot⟩⟩
      rcases hKpre Uₐ Ub hUopenₐ hUopenb hcov hAne hBne with ⟨z, hz⟩
      have hzA : z ∈ A := by
        rw [hAeq]
        exact ⟨hz.1, hz.2.1⟩
      have hzB : z ∈ B := by
        rw [hBeq]
        exact ⟨hz.1, hz.2.2⟩
      exact hzB.2 hzA.2
    exact ⟨fun _ => hPy', fun _ => hPx⟩
  · -- P x false: every K-point has P false (else A ∋ y nonempty alongside B ∋ x)
    have hPy' : ¬ P y := by
      by_contra hnot
      have hAne : (K ∩ Uₐ).Nonempty := by
        rw [← hAeq]
        exact ⟨y, ⟨hyK, hnot⟩⟩
      have hBne : (K ∩ Ub).Nonempty := by
        rw [← hBeq]
        exact ⟨x, ⟨hxK, hPx⟩⟩
      rcases hKpre Uₐ Ub hUopenₐ hUopenb hcov hAne hBne with ⟨z, hz⟩
      have hzA : z ∈ A := by
        rw [hAeq]
        exact ⟨hz.1, hz.2.1⟩
      have hzB : z ∈ B := by
        rw [hBeq]
        exact ⟨hz.1, hz.2.2⟩
      exact hzB.2 hzA.2
    exact ⟨fun hx => False.elim (hPx hx), fun hy => False.elim (hPy' hy)⟩

/-- **Frontier arcs lie on a single straight line**: any PRECONNECTED set
`K` of frontier points of the flat component `C = flatComponent f p`
(each `e ∈ K` carrying its half-disk data `(w e, ρ e)`: unit `w e`,
radius `ρ e > 0`, and `z ∈ C ↔ signedLineFunc e (w e) z < 0` inside
`B(e, ρ e)`) is contained in one straight line: there are `c : ℝ²` and a
unit `u : ℝ²` with `signedLineFunc c u e = 0` for every `e ∈ K` — the
line through `c` in direction `u` contains all of `K`. -/
theorem frontier_arc_on_line {f : ℝ² → ℝ³} {p : ℝ²} {K : Set ℝ²}
    (hKpre : IsPreconnected K) (hKsub : K ⊆ frontier (flatComponent f p))
    {w : ℝ² → ℝ²} {ρ : ℝ² → ℝ}
    (hw : ∀ e, e ∈ K → ‖w e‖ = 1) (hρ : ∀ e, e ∈ K → 0 < ρ e)
    (heq : ∀ e, e ∈ K → ∀ z : ℝ², z ∈ Metric.ball e (ρ e) →
      (z ∈ flatComponent f p ↔ signedLineFunc e (w e) z < 0)) :
    ∃ u : ℝ², ‖u‖ = 1 ∧ ∃ c : ℝ², ∀ e ∈ K, signedLineFunc c u e = 0 := by
  by_cases hK : K.Nonempty
  · rcases hK with ⟨e₀, he₀K⟩
    let φ₀ : ℝ² → ℝ := fun z => signedLineFunc e₀ (w e₀) z
    -- local chord ⊆: y ∈ K ∩ B(x, ρ x) ⟹ φ_x y = 0
    have hloc0 : ∀ (x y : ℝ²), x ∈ K → y ∈ K → y ∈ Metric.ball x (ρ x) →
        signedLineFunc x (w x) y = 0 := by
      intro x y hxK hyK hyball
      exact frontier_mem_chord_of_halfdisk (C := flatComponent f p) (isOpen_flatComponent f p)
        (x := x) (w := w x) (ρ := ρ x) (heq := heq x hxK)
        (hyF := hKsub hyK) (hyb := hyball)
    -- direction constancy between any x ∈ K and e₀
    have hdir : ∀ x, x ∈ K → w x = w e₀ ∨ w x = - w e₀ := by
      intro x hxK
      exact preconnected_frontier_directions_parallel hKpre hKsub hw hρ heq x hxK e₀ he₀K
    -- P := (φ₀ = 0) is locally constant on K
    have hlc : ∀ (x y : ℝ²), x ∈ K → y ∈ K → y ∈ Metric.ball x (ρ x) →
        (φ₀ y = 0 ↔ φ₀ x = 0) := by
      intro x y hxK hyK hyball
      have hφx0 : signedLineFunc x (w x) y = 0 := hloc0 x y hxK hyK hyball
      rcases hdir x hxK with hwpos | hwneg
      · have hshift : signedLineFunc x (w e₀) y = φ₀ y - φ₀ x := by
          dsimp [φ₀]
          exact signedLineFunc_shift e₀ x (w e₀) y
        have hm : signedLineFunc x (w x) y = φ₀ y - φ₀ x := by
          rw [hwpos]
          exact hshift
        have hdiff : φ₀ y - φ₀ x = 0 := by rwa [hm] at hφx0
        constructor
        · intro hy0
          linarith
        · intro hx0
          linarith
      · have hm : signedLineFunc x (w x) y = -(φ₀ y - φ₀ x) := by
          rw [hwneg]
          have hneg1 : signedLineFunc x (-(w e₀)) y = -(signedLineFunc x (w e₀) y) :=
            signedLineFunc_neg x (w e₀) y
          rw [hneg1]
          have hshift : signedLineFunc x (w e₀) y = φ₀ y - φ₀ x := by
            dsimp [φ₀]
            exact signedLineFunc_shift e₀ x (w e₀) y
          rw [hshift]
        have hdiff : -(φ₀ y - φ₀ x) = 0 := by rwa [hm] at hφx0
        constructor
        · intro hy0
          linarith
        · intro hx0
          linarith
    refine ⟨w e₀, hw e₀ he₀K, e₀, ?_⟩
    intro e heK
    have hP₀ : φ₀ e₀ = 0 := by
      simpa [φ₀] using (signedLineFunc_self e₀ (w e₀))
    have hconst := preconnected_of_locallyConstant_prop hKpre hρ hlc e₀ he₀K e heK
    have hPe : φ₀ e = 0 := hconst.mp hP₀
    simpa [φ₀] using hPe
  · -- K empty: any unit direction and base work
    refine ⟨!₂[1, 0], ?_, !₂[0, 0], ?_⟩
    · have hsq : ‖(!₂[1, 0] : ℝ²)‖ ^ 2 = 1 := by
        rw [norm_sq_coord_sum]
        norm_num
      have hnn0 : 0 ≤ ‖(!₂[1, 0] : ℝ²)‖ := norm_nonneg _
      apply le_antisymm
      · have hle : ‖(!₂[1, 0] : ℝ²)‖ ^ 2 ≤ 1 ^ 2 := by simpa using hsq.le
        exact (sq_le_sq₀ hnn0 (by norm_num)).mp hle
      · have hle : 1 ^ 2 ≤ ‖(!₂[1, 0] : ℝ²)‖ ^ 2 := by rw [hsq]; norm_num
        exact (sq_le_sq₀ (by norm_num) hnn0).mp hle
    · intro e he
      exact (hK ⟨e, he⟩).elim

/-- **Data-free arc-on-line statement**: any PRECONNECTED set `K` of
frontier points of `flatComponent f p` lying in the strip interior is
contained in a single straight line (the half-disk data is instantiated
from `degenerate_frontier_half_disk` by choice at every point of `K`). -/
theorem frontier_arc_on_line_of_strip {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²} {K : Set ℝ²}
    (hKpre : IsPreconnected K) (hKsubS : K ⊆ stripInterior)
    (hKsubF : K ⊆ frontier (flatComponent f p)) :
    ∃ u : ℝ², ‖u‖ = 1 ∧ ∃ c : ℝ², ∀ e ∈ K, signedLineFunc c u e = 0 := by
  classical
  have hdata : ∀ e : ℝ², e ∈ K →
      ∃ w : ℝ², ∃ ρ : ℝ, ‖w‖ = 1 ∧ 0 < ρ ∧ Metric.ball e ρ ⊆ stripInterior ∧
        (∀ z : ℝ², z ∈ Metric.ball e ρ →
          (z ∈ flatComponent f p ↔ signedLineFunc e w z < 0)) :=
    fun e heK => degenerate_frontier_half_disk hf ha (hKsubS heK) (hKsubF heK)
  let w : ℝ² → ℝ² := fun e => if heK : e ∈ K then Classical.choose (hdata e heK) else 0
  let ρ : ℝ² → ℝ := fun e =>
    if heK : e ∈ K then Classical.choose (Classical.choose_spec (hdata e heK)) else 1
  have hw : ∀ e, e ∈ K → ‖w e‖ = 1 := by
    intro e heK
    dsimp [w]
    rw [dif_pos heK]
    exact (Classical.choose_spec (Classical.choose_spec (hdata e heK))).1
  have hρ : ∀ e, e ∈ K → 0 < ρ e := by
    intro e heK
    dsimp [ρ]
    rw [dif_pos heK]
    exact (Classical.choose_spec (Classical.choose_spec (hdata e heK))).2.1
  have heq : ∀ e, e ∈ K → ∀ z : ℝ², z ∈ Metric.ball e (ρ e) →
      (z ∈ flatComponent f p ↔ signedLineFunc e (w e) z < 0) := by
    intro e heK z hzball
    have hwe : w e = Classical.choose (hdata e heK) := by
      dsimp [w]
      rw [dif_pos heK]
    have hρe : ρ e = Classical.choose (Classical.choose_spec (hdata e heK)) := by
      dsimp [ρ]
      rw [dif_pos heK]
    rw [hwe]
    have hzball' : z ∈ Metric.ball e (Classical.choose (Classical.choose_spec (hdata e heK))) := by
      simpa [hρe] using hzball
    exact (Classical.choose_spec (Classical.choose_spec (hdata e heK))).2.2.2 z hzball'
  rcases frontier_arc_on_line hKpre hKsubF hw hρ heq with ⟨u, hu₁, c, hline⟩
  exact ⟨u, hu₁, c, hline⟩

end Submission.PaperBand
