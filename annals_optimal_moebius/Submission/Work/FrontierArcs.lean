import Submission.Work.ComponentSeparation
import Submission.Commons.Topology.Order.open_preconnected_eq_Ioo_ereal

open OptimalMoebius Filter Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Frontier components of a flat region are locally straight chords (FrontierArcs)

This is the first formal brick of T1-i (session_status60 (S1)+(S2)): for
an OPEN `C` with the half-disk data at a frontier point `e` (unit `w`,
radius `ρ`, `C ∩ B(e,ρ) = {φ_w < 0} ∩ B(e,ρ)`), the connected component
`K(e) := connectedComponentIn (∂C ∩ stripInterior) e` of the frontier
through `e` agrees with the straight chord inside `B(e,ρ)`:

    K(e) ∩ B(e,ρ)  =  chord(e,w) ∩ B(e,ρ) := {z ∈ B(e,ρ) | φ_w z = 0}.

* `⊆`: a point of `K(e)` is a frontier point of `C` inside `B(e,ρ)`, and
  the chord ⊆-direction (`frontier_mem_chord_of_halfdisk`) puts it on
  the chord.
* `⊇`: the chord segment `{z ∈ B(e,ρ) | φ_w z = 0}` is preconnected (it
  is the continuous image of the interval `(-ρ,ρ)` under
  `t ↦ e + t•w`, using `signedLineFunc_const_along_dir` and the
  collinearity lemma `exists_smul_of_det2_eq_zero`), lies in
  `∂C ∩ stripInterior` (chord ⊇-direction
  `chord_mem_frontier_of_halfdisk` + `hballS`), and contains `e` — hence
  by `IsPreconnected.subset_connectedComponentIn` it lies in the
  connected component `K(e)`.

Generic over any open `C` (no `IsMoebiusEmbedding` needed): the flat
component instance supplies the data from `degenerate_frontier_half_disk`
at each frontier point, exactly as `ComponentSeparation` does.

Build: `lake build Submission.Work.FrontierArcs` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The straight chord through `e` in direction `w` inside the ball
`B(e,ρ)`: points of the ball on the line `{z | signedLineFunc e w z = 0}`. -/
def chordSet (e w : ℝ²) (ρ : ℝ) : Set ℝ² :=
  {z : ℝ² | z ∈ Metric.ball e ρ ∧ signedLineFunc e w z = 0}

/-- The chord segment is the image of the interval `(-ρ,ρ)` under
`t ↦ e + t•w` (for unit `w`): the natural straight parametrisation. -/
lemma chordSet_eq_image_smul {e w : ℝ²} {ρ : ℝ} (hw₁ : ‖w‖ = 1) :
    chordSet e w ρ = (fun t : ℝ => e + t • w) '' Set.Ioo (-ρ) ρ := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzball, hφ⟩
    have hdet : det2 (z - e) w = 0 := by
      have hφ' : signedLineFunc e w z = 0 := hφ
      rwa [signedLineFunc_eq_det2 e w z] at hφ'
    have hwne : w ≠ 0 := by
      intro hw0
      rw [hw0] at hw₁
      norm_num at hw₁
    have hsmul : ∃ s : ℝ, z - e = s • w := by
      -- exists_smul_of_det2_eq_zero with a := w, u := z - e needs det2 w (z-e) = 0
      refine exists_smul_of_det2_eq_zero hwne ?_
      exact hdet
    rcases hsmul with ⟨s, hze⟩
    have hz_eq : z = e + s • w := by
      calc z = e + (z - e) := by abel
        _ = e + s • w := by rw [hze]
    refine ⟨s, ?_, hz_eq.symm⟩
    rw [Set.mem_Ioo]
    -- |s| < ρ from ‖z - e‖ < ρ
    have hnorm : ‖s • w‖ = |s| := by
      rw [norm_smul, Real.norm_eq_abs, hw₁]
      ring
    have hnorm' : |s| = ‖z - e‖ := by
      calc |s| = ‖s • w‖ := hnorm.symm
        _ = ‖z - e‖ := by rw [hze]
    have hlt : |s| < ρ := by
      rw [hnorm']
      -- z ∈ ball e ρ
      exact (Metric.mem_ball.mp hzball)
    exact (abs_lt.mp hlt)
  · rintro ⟨t, ht, hz⟩
    constructor
    · -- f t ∈ ball e ρ : ‖f t − e‖ = |t| < ρ
      rw [Metric.mem_ball]
      rw [dist_eq_norm]
      have hmain : ‖(e + t • w) - e‖ = |t| := by
        rw [show (e + t • w) - e = t • w by abel]
        rw [norm_smul]
        rw [Real.norm_eq_abs]
        rw [hw₁]
        ring
      rw [← hz]
      rw [hmain]
      rw [Set.mem_Ioo] at ht
      exact (abs_lt.mpr ht)
    · -- φ(f t) = 0
      rw [← hz]
      exact signedLineFunc_const_along_dir e w t

/-- **The frontier component through `e` is locally the straight chord**:
for an open `C` with half-disk data at a frontier point `e` of the strip
interior, the connected component of `∂C ∩ stripInterior` through `e`
equals the chord `{φ_w = 0}` inside `B(e,ρ)`. -/
theorem frontierComponent_locally_chord {C : Set ℝ²} (hCopen : IsOpen C) {e w : ℝ²} {ρ : ℝ}
    (hw₁ : ‖w‖ = 1) (hρ : 0 < ρ)
    (hballS : Metric.ball e ρ ⊆ stripInterior)
    (heq : ∀ z : ℝ², z ∈ Metric.ball e ρ → (z ∈ C ↔ signedLineFunc e w z < 0)) :
    connectedComponentIn (frontier C ∩ stripInterior) e ∩ Metric.ball e ρ = chordSet e w ρ := by
  let K : Set ℝ² := connectedComponentIn (frontier C ∩ stripInterior) e
  let chord : Set ℝ² := chordSet e w ρ
  apply le_antisymm
  · -- K ∩ ball ⊆ chord
    intro x hx
    rcases hx with ⟨hxK, hxball⟩
    have hxF : x ∈ frontier C := ((connectedComponentIn_subset (frontier C ∩ stripInterior) e) hxK).1
    have hφ0 : signedLineFunc e w x = 0 :=
      frontier_mem_chord_of_halfdisk (C := C) hCopen (x := e) (w := w) (ρ := ρ) heq hxF hxball
    exact ⟨hxball, hφ0⟩
  · -- chord ⊆ K ∩ ball
    intro x hx
    have hxball : x ∈ Metric.ball e ρ := hx.1
    have hφ0 : signedLineFunc e w x = 0 := hx.2
    have hKsub : chord ⊆ K := by
      -- chord is preconnected, lies in frontier C ∩ stripInterior, contains e
      have hpre : IsPreconnected chord := by
        rw [show chord = (fun t : ℝ => e + t • w) '' Set.Ioo (-ρ) ρ by
          dsimp [chord]
          exact chordSet_eq_image_smul hw₁]
        have hcont : Continuous (fun t : ℝ => e + t • w) := by fun_prop
        exact IsPreconnected.image isPreconnected_Ioo (fun t : ℝ => e + t • w)
          (hcont.continuousOn.mono (Set.subset_univ (Set.Ioo (-ρ) ρ)))
      have hmem : e ∈ chord := ⟨Metric.mem_ball_self hρ, signedLineFunc_self e w⟩
      have hsubF : chord ⊆ frontier C ∩ stripInterior := by
        intro z hz
        have hzball : z ∈ Metric.ball e ρ := hz.1
        have hφz0 : signedLineFunc e w z = 0 := hz.2
        have hzF : z ∈ frontier C :=
          chord_mem_frontier_of_halfdisk (C := C) hCopen (e := e) (w := w) (ρ := ρ) hw₁ heq
            hzball hφz0
        exact ⟨hzF, hballS hzball⟩
      exact IsPreconnected.subset_connectedComponentIn (F := frontier C ∩ stripInterior) hpre hmem hsubF
    exact ⟨hKsub hx, hxball⟩

/-- **The frontier component through `e` lies on the single line through
`e` (the spine)**: instantiating `frontier_arc_on_line_of_strip` on
`K(e) := connectedComponentIn (∂C ∩ stripInterior) e` (`C :=
flatComponent f p`) gives one unit direction `u` with
`signedLineFunc e u x = 0` for every `x ∈ K(e)` — every point of the
frontier component through `e` lies on the straight line through `e` in
direction `u`.  (The base is moved from the existential `c` to `e`
itself via `signedLineFunc_shift`, using that `e ∈ K(e)`.) -/
theorem frontierComponent_on_line {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heF : e ∈ frontier (flatComponent f p)) :
    ∃ u : ℝ², ‖u‖ = 1 ∧
      ∀ x : ℝ², x ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e →
        signedLineFunc e u x = 0 := by
  let K : Set ℝ² := connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e
  have hKpre : IsPreconnected K := isPreconnected_connectedComponentIn
  have hKsubS : K ⊆ stripInterior := by
    intro x hx
    exact ((connectedComponentIn_subset (frontier (flatComponent f p) ∩ stripInterior) e) hx).2
  have hKsubF : K ⊆ frontier (flatComponent f p) := by
    intro x hx
    exact ((connectedComponentIn_subset (frontier (flatComponent f p) ∩ stripInterior) e) hx).1
  rcases frontier_arc_on_line_of_strip hf ha (K := K) hKpre hKsubS hKsubF with ⟨u, hu₁, c, hline⟩
  refine ⟨u, hu₁, ?_⟩
  intro x hx
  have heK : e ∈ K := by
    dsimp [K]
    exact mem_connectedComponentIn ⟨heF, heS⟩
  have hce : signedLineFunc c u e = 0 := hline e heK
  have hxline : signedLineFunc c u x = 0 := hline x hx
  have hshift := signedLineFunc_shift c e u x
  rw [hshift, hxline, hce]
  ring

/-- **Parametrised spine**: with the line direction `u` from
`frontierComponent_on_line`, every point of the frontier component
through `e` is `e + s•u` for some real `s`. -/
theorem frontierComponent_param_on_line {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heF : e ∈ frontier (flatComponent f p)) :
    ∃ u : ℝ², ‖u‖ = 1 ∧
      ∀ x : ℝ², x ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e →
        ∃ s : ℝ, x = e + s • u := by
  rcases frontierComponent_on_line hf ha heS heF with ⟨u, hu₁, hline⟩
  refine ⟨u, hu₁, ?_⟩
  intro x hx
  have hφ : signedLineFunc e u x = 0 := hline x hx
  have hdet : det2 (x - e) u = 0 := by
    have hφ' := hφ
    rwa [signedLineFunc_eq_det2 e u x] at hφ'
  have hu_ne : u ≠ 0 := by
    intro hu0
    rw [hu0] at hu₁
    norm_num at hu₁
  rcases exists_smul_of_det2_eq_zero hu_ne hdet with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  calc
    x = e + (x - e) := by abel
    _ = e + s • u := by rw [hs]


/-- **Local chord structure at every point of the frontier component**:
for each `x` in `K(e)`, the half-disk data at `x` exists and the component
`K(e)` coincides with the straight chord through `x` inside the data ball
(the composition of `degenerate_frontier_half_disk` and
`frontierComponent_locally_chord` at `x`, with the component moved back
to `e` by `connectedComponentIn_eq`). -/
theorem frontierComponent_locally_chord_everywhere {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p e x : ℝ²}
    (hx : x ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e) :
    ∃ w : ℝ², ∃ ρ : ℝ, ‖w‖ = 1 ∧ 0 < ρ ∧ Metric.ball x ρ ⊆ stripInterior ∧
      (∀ z : ℝ², z ∈ Metric.ball x ρ →
        (z ∈ flatComponent f p ↔ signedLineFunc x w z < 0)) ∧
      connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e ∩ Metric.ball x ρ =
        chordSet x w ρ := by
  have hxF : x ∈ frontier (flatComponent f p) :=
    ((connectedComponentIn_subset (frontier (flatComponent f p) ∩ stripInterior) e) hx).1
  have hxS : x ∈ stripInterior :=
    ((connectedComponentIn_subset (frontier (flatComponent f p) ∩ stripInterior) e) hx).2
  rcases degenerate_frontier_half_disk hf ha hxS hxF with ⟨w, ρ, hw₁, hρ, hballS, hiff⟩
  refine ⟨w, ρ, hw₁, hρ, hballS, hiff, ?_⟩
  have hc := connectedComponentIn_eq (F := frontier (flatComponent f p) ∩ stripInterior)
    (x := e) (y := x) hx
  have hloc := frontierComponent_locally_chord (C := flatComponent f p) (isOpen_flatComponent f p)
    (e := x) (w := w) (ρ := ρ) hw₁ hρ hballS hiff
  calc
    connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e ∩ Metric.ball x ρ
        = connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) x ∩ Metric.ball x ρ := by
      rw [hc]
    _ = chordSet x w ρ := hloc


/-- **Two lines sharing a two-sided chord segment coincide (2D core of
sub-lemma 1)**: if every point of the chord segment through `x` in
direction `w` inside `B(x,ρ)` lies on the line `{z | signedLineFunc e u
z = 0}` (which passes through `x`), then conversely every point of that
line inside `B(x,ρ)` lies on the chord.  Proof: the two-sided chord
points `x ± t•w` (t := ρ/2) are on the line, so the affine functional
`φ_{e u}` vanishes at both — `0 = φ(x+t w) = φ(x) + t·det2 w u` with
`φ(x)=0` forces `det2 w u = 0`, so (`w`,`u` unit) `w = ±u`, and then
`det2 (z−x) u = 0` gives `det2 (z−x) w = 0`. -/
lemma chord_line_inclusion_of_chord_on_line {e x u w : ℝ²} {ρ : ℝ}
    (hu₁ : ‖u‖ = 1) (hw₁ : ‖w‖ = 1) (hρ : 0 < ρ)
    (hxL : signedLineFunc e u x = 0)
    (hsub : ∀ z : ℝ², z ∈ Metric.ball x ρ → signedLineFunc x w z = 0 →
      signedLineFunc e u z = 0) :
    ∀ z : ℝ², z ∈ Metric.ball x ρ → signedLineFunc e u z = 0 →
      signedLineFunc x w z = 0 := by
  -- the chord direction is parallel to the line direction
  have hdet : det2 w u = 0 := by
    by_contra hne
    let t : ℝ := ρ / 2
    have htpos : 0 < t := by dsimp [t]; exact half_pos hρ
    let z : ℝ² := x + t • w
    have hzball : z ∈ Metric.ball x ρ := by
      rw [Metric.mem_ball]
      rw [dist_eq_norm]
      have hn : ‖(x + t • w) - x‖ = t := by
        rw [show (x + t • w) - x = t • w by abel]
        rw [norm_smul]
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (le_of_lt htpos)]
        rw [hw₁]
        ring
      dsimp [z]
      rw [hn]
      dsimp [t]
      linarith
    have hφx : signedLineFunc x w z = 0 := by
      dsimp [z]
      exact signedLineFunc_const_along_dir x w t
    have hφ : signedLineFunc e u z = 0 := hsub z hzball hφx
    have hlin := signedLineFunc_add_smul e u x w t
    have hz0 : signedLineFunc e u (x + t • w) = 0 := by simpa [z] using hφ
    rw [hlin, hxL, zero_add] at hz0
    have htd : t * det2 w u = 0 := hz0
    have hd0 : det2 w u = 0 := (mul_eq_zero.mp htd).resolve_left (ne_of_gt htpos)
    exact hne hd0
  intro z hzball hφz
  have hdzu : det2 (z - x) u = 0 := by
    have hze : det2 (z - e) u = 0 := by
      have := hφz
      rwa [signedLineFunc_eq_det2 e u z] at this
    have hxe : det2 (x - e) u = 0 := by
      have := hxL
      rwa [signedLineFunc_eq_det2 e u x] at this
    have hsub' : det2 ((z - e) - (x - e)) u = det2 (z - e) u - det2 (x - e) u :=
      det2_sub_left (z - e) (x - e) u
    rw [show (z - e) - (x - e) = z - x by abel] at hsub'
    rw [hsub', hze, hxe]
    ring
  rcases unit_eq_or_neg_of_det2_eq_zero hw₁ hu₁ hdet with hwu | hwuneg
  · -- w = u
    rw [hwu]
    rw [signedLineFunc_eq_det2 x u z]
    exact hdzu
  · -- w = -u
    rw [hwuneg]
    rw [signedLineFunc_neg x u z]
    rw [signedLineFunc_eq_det2 x u z, hdzu]
    simp

/-- **The line segment through a frontier-component point lies inside the
component** (sub-lemma 1, band level): with the spine `u` (`K(e)` on the
line `{φ_{e u} = 0}`), every point of that line within the chord ball at
`x ∈ K(e)` belongs to `K(e)` — so `K(e)` contains a two-sided straight
segment of its line around every one of its points. -/
theorem frontierComponent_line_ball_inside {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p e x : ℝ²}
    (hx : x ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e)
    (u : ℝ²) (hu₁ : ‖u‖ = 1)
    (hline : ∀ y : ℝ²,
      y ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e →
        signedLineFunc e u y = 0) :
    ∃ w : ℝ², ∃ ρ : ℝ, ‖w‖ = 1 ∧ 0 < ρ ∧
      (∀ z : ℝ², z ∈ Metric.ball x ρ → signedLineFunc e u z = 0 →
        z ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e) := by
  rcases frontierComponent_locally_chord_everywhere hf ha hx with ⟨w, ρ, hw₁, hρ, hballS, hiff, hloc⟩
  refine ⟨w, ρ, hw₁, hρ, ?_⟩
  intro z hzball hφz
  have hxL : signedLineFunc e u x = 0 := hline x hx
  have hsub : ∀ y : ℝ², y ∈ Metric.ball x ρ → signedLineFunc x w y = 0 →
      signedLineFunc e u y = 0 := by
    intro y hyball hchord
    have hyC : y ∈ chordSet x w ρ := ⟨hyball, hchord⟩
    have hyKB : y ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e ∩
        Metric.ball x ρ := by
      rw [hloc]
      exact hyC
    exact hline y hyKB.1
  have hmain := chord_line_inclusion_of_chord_on_line (e := e) (x := x) (u := u) (w := w) (ρ := ρ)
    hu₁ hw₁ hρ hxL hsub
  have hzchord : signedLineFunc x w z = 0 := hmain z hzball hφz
  have hzC : z ∈ chordSet x w ρ := ⟨hzball, hzchord⟩
  have hzKB : z ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e ∩
      Metric.ball x ρ := by
    rw [hloc]
    exact hzC
  exact hzKB.1


/-- **The parameter set of the frontier component is open** (sub-lemma
2): with the spine `u` (`K(e)` on the line `{z | signedLineFunc e u z =
0}`), the set of parameters whose points lie in the component,

    S := {s : ℝ | e + s•u ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e},

is OPEN in ℝ.  Proof: for `s₀ ∈ S` put `x := e + s₀•u ∈ K(e)`;
`frontierComponent_line_ball_inside` gives `w, ρ > 0` with every point
of the line inside `B(x,ρ)` in `K(e)`; for `|s − s₀| < ρ` the point
`e + s•u` lies in `B(x,ρ)` (`‖(e+s•u) − (e+s₀•u)‖ = |s−s₀|`) and on the
line (`signedLineFunc e u (e + s•u) = 0`), so it is in `K(e)`. -/
theorem frontierComponent_paramSet_open {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p e u : ℝ²} (hu₁ : ‖u‖ = 1)
    (hline : ∀ y : ℝ²,
      y ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e →
        signedLineFunc e u y = 0) :
    IsOpen {s : ℝ | e + s • u ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e} := by
  rw [Metric.isOpen_iff]
  intro s₀ hs₀
  let x : ℝ² := e + s₀ • u
  have hx : x ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e := by
    simpa [x] using hs₀
  rcases frontierComponent_line_ball_inside hf ha (e := e) (x := x) hx u hu₁ hline with
    ⟨w, ρ, hw₁, hρ, hincl⟩
  refine ⟨ρ, hρ, ?_⟩
  intro s hs
  have hzball : e + s • u ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball]
    rw [dist_eq_norm]
    have hn : ‖(e + s • u) - x‖ = |s - s₀| := by
      dsimp [x]
      have h1 : (e + s • u) - (e + s₀ • u) = s • u - s₀ • u := by abel
      rw [h1]
      rw [← sub_smul]
      rw [norm_smul]
      rw [Real.norm_eq_abs]
      rw [hu₁]
      ring
    rw [hn]
    simpa [dist_eq_norm, Real.norm_eq_abs] using (Metric.mem_ball.mp hs)
  have hφ0 : signedLineFunc e u (e + s • u) = 0 := signedLineFunc_const_along_dir e u s
  exact hincl (e + s • u) hzball hφ0


/-- The straight line through `e` in direction `u`: the zero set of the
signed functional `φ_{e u}`. -/
def lineSet (e u : ℝ²) : Set ℝ² := {z : ℝ² | signedLineFunc e u z = 0}

/-- Membership in the line through `e` in direction `u`. -/
lemma mem_lineSet_iff (e u z : ℝ²) : z ∈ lineSet e u ↔ signedLineFunc e u z = 0 := by
  rfl

/-- **The line through `e` in unit direction `u` is parametrised by ℝ**
(the `ℝ ≅ L` homeo infrastructure of step 3): `s ↦ e + s•u` is a
homeomorphism from `ℝ` onto the subtype `{z | z ∈ lineSet e u}`.
Inverse: `z ↦ inner ℝ (z − e) u` (the signed distance along the unit
direction, which recovers the parameter because `z = e + s₀•u` with
`s₀ = ⟪z − e, u⟫` when `z` is on the line). -/
def lineHomeo (e u : ℝ²) (hu₁ : ‖u‖ = 1) : ℝ ≃ₜ {z : ℝ² // z ∈ lineSet e u} where
  toFun := fun s => ⟨e + s • u, signedLineFunc_const_along_dir e u s⟩
  invFun := fun z => inner ℝ ((z : ℝ²) - e) u
  left_inv := by
    intro s
    have h : (e + s • u) - e = s • u := by abel
    calc
      inner ℝ ((e + s • u) - e) u = inner ℝ (s • u) u := by rw [h]
      _ = s := by
        rw [inner_smul_left]
        rw [real_inner_self_eq_norm_sq]
        rw [hu₁]
        norm_num
  right_inv := by
    intro z
    have hu_ne : u ≠ 0 := by
      intro h0
      rw [h0] at hu₁
      norm_num at hu₁
    have hφ : signedLineFunc e u (z : ℝ²) = 0 := by
      exact (mem_lineSet_iff e u (z : ℝ²)).mp z.2
    have hdet : det2 ((z : ℝ²) - e) u = 0 := by
      have h := hφ
      rwa [signedLineFunc_eq_det2 e u (z : ℝ²)] at h
    rcases exists_smul_of_det2_eq_zero hu_ne hdet with ⟨s₀, hs₀⟩
    have hsz : inner ℝ ((z : ℝ²) - e) u = s₀ := by
      calc
        inner ℝ ((z : ℝ²) - e) u = inner ℝ (s₀ • u) u := by rw [hs₀]
        _ = s₀ := by
          rw [inner_smul_left]
          rw [real_inner_self_eq_norm_sq]
          rw [hu₁]
          norm_num
    apply Subtype.ext
    calc
      e + inner ℝ ((z : ℝ²) - e) u • u = e + s₀ • u := by rw [hsz]
      _ = e + ((z : ℝ²) - e) := by rw [← hs₀]
      _ = (z : ℝ²) := by abel
  continuous_toFun := by
    have hcont : Continuous (fun s : ℝ => e + s • u) := by fun_prop
    exact Continuous.subtype_mk hcont (fun s => signedLineFunc_const_along_dir e u s)
  continuous_invFun := by
    have hval : Continuous (fun z : {z : ℝ² // z ∈ lineSet e u} => (z : ℝ²)) :=
      continuous_subtype_val
    have hsub : Continuous (fun z : {z : ℝ² // z ∈ lineSet e u} => (z : ℝ²) - e) :=
      hval.sub continuous_const
    exact Continuous.inner hsub continuous_const


/-- **The parameter set of a preconnected subset of the line is
preconnected**: if `K ⊆ lineSet e u` is preconnected then
`{s | e + s•u ∈ K}` is preconnected in ℝ.  Proof: with the continuous
signed parameter `σ x := inner ℝ (x − e) u` (which satisfies
`σ(e + s•u) = s` and, on the line, `e + σ(x)•u = x`), any relatively
open cover `U, V` of the parameter set with both parts nonempty pulls
back to a cover of `K` by `σ⁻¹U, σ⁻¹V` with both parts nonempty, and
preconnectedness of `K` supplies the overlap, which maps back to an
overlap of `U` and `V`. -/
theorem paramSet_preconnected_of_preconnected {e u : ℝ²} (hu₁ : ‖u‖ = 1) {K : Set ℝ²}
    (hKpre : IsPreconnected K) (hKsub : K ⊆ lineSet e u) :
    IsPreconnected {s : ℝ | e + s • u ∈ K} := by
  let S : Set ℝ := {s : ℝ | e + s • u ∈ K}
  have hu_ne : u ≠ 0 := by
    intro h0
    rw [h0] at hu₁
    norm_num at hu₁
  have hσg : ∀ s : ℝ, inner ℝ ((e + s • u) - e) u = s := by
    intro s
    have h : (e + s • u) - e = s • u := by abel
    calc
      inner ℝ ((e + s • u) - e) u = inner ℝ (s • u) u := by rw [h]
      _ = s := by
        rw [inner_smul_left]
        rw [real_inner_self_eq_norm_sq]
        rw [hu₁]
        norm_num
  have hgσ : ∀ x : ℝ², x ∈ lineSet e u → e + inner ℝ (x - e) u • u = x := by
    intro x hxL
    have hφ : signedLineFunc e u x = 0 := (mem_lineSet_iff e u x).mp hxL
    have hdet : det2 (x - e) u = 0 := by
      have h := hφ
      rwa [signedLineFunc_eq_det2 e u x] at h
    rcases exists_smul_of_det2_eq_zero hu_ne hdet with ⟨s₀, hs₀⟩
    have hsz : inner ℝ (x - e) u = s₀ := by
      calc
        inner ℝ (x - e) u = inner ℝ (s₀ • u) u := by rw [hs₀]
        _ = s₀ := by
          rw [inner_smul_left]
          rw [real_inner_self_eq_norm_sq]
          rw [hu₁]
          norm_num
    calc
      e + inner ℝ (x - e) u • u = e + s₀ • u := by rw [hsz]
      _ = e + (x - e) := by rw [← hs₀]
      _ = x := by abel
  let σ : ℝ² → ℝ := fun x => inner ℝ (x - e) u
  have hσcont : Continuous σ := by
    have hc : Continuous (fun x : ℝ² => x - e) := continuous_id.sub continuous_const
    exact Continuous.inner hc continuous_const
  intro U V hUo hVo hcov hU hV
  have hσU : IsOpen (σ ⁻¹' U) := hσcont.isOpen_preimage U hUo
  have hσV : IsOpen (σ ⁻¹' V) := hσcont.isOpen_preimage V hVo
  have hcov' : K ⊆ (σ ⁻¹' U) ∪ (σ ⁻¹' V) := by
    intro x hxK
    have hxS : σ x ∈ S := by
      dsimp [S, σ]
      rw [hgσ x (hKsub hxK)]
      exact hxK
    rcases (hcov hxS) with hxU | hxV
    · left
      exact hxU
    · right
      exact hxV
  have hU' : (K ∩ (σ ⁻¹' U)).Nonempty := by
    rcases hU with ⟨s₀, hs₀⟩
    refine ⟨e + s₀ • u, ?_, ?_⟩
    · exact hs₀.1
    · change σ (e + s₀ • u) ∈ U
      dsimp [σ]
      rw [hσg s₀]
      exact hs₀.2
  have hV' : (K ∩ (σ ⁻¹' V)).Nonempty := by
    rcases hV with ⟨s₀, hs₀⟩
    refine ⟨e + s₀ • u, ?_, ?_⟩
    · exact hs₀.1
    · change σ (e + s₀ • u) ∈ V
      dsimp [σ]
      rw [hσg s₀]
      exact hs₀.2
  rcases hKpre (σ ⁻¹' U) (σ ⁻¹' V) hσU hσV hcov' hU' hV' with ⟨x, hx⟩
  refine ⟨σ x, ?_⟩
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · -- σ x ∈ S
    dsimp [S, σ]
    rw [hgσ x (hKsub hx.1)]
    exact hx.1
  · exact hx.2.1
  · exact hx.2.2

/-- **The parameter set of a frontier component is preconnected**
(band-level instantiation): with the spine `u` on `K(e)`, the set of
parameters whose line points lie in `K(e)` is preconnected in ℝ. -/
theorem frontierComponent_paramSet_preconnected {f : ℝ² → ℝ³}
    {p e u : ℝ²} (hu₁ : ‖u‖ = 1)
    (hline : ∀ y : ℝ²,
      y ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e →
        signedLineFunc e u y = 0) :
    IsPreconnected {s : ℝ | e + s • u ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e} := by
  apply paramSet_preconnected_of_preconnected (e := e) (u := u) hu₁
  · exact isPreconnected_connectedComponentIn
  · intro y hy
    exact (mem_lineSet_iff e u y).mpr (hline y hy)


/-- **The parameter set of a frontier component is an interval of ℝ**
(`OrdConnected` form of step 3): open (`frontierComponent_paramSet_open`)
+ preconnected (`frontierComponent_paramSet_preconnected`) subsets of ℝ
are order-connected, i.e. contain every value between any two of their
points (`isPreconnected_iff_ordConnected`). -/
theorem frontierComponent_paramSet_ordConnected {f : ℝ² → ℝ³} {p e u : ℝ²}
    (hu₁ : ‖u‖ = 1)
    (hline : ∀ y : ℝ²,
      y ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e →
        signedLineFunc e u y = 0) :
    Set.OrdConnected {s : ℝ | e + s • u ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e} := by
  exact isPreconnected_iff_ordConnected.mp (frontierComponent_paramSet_preconnected hu₁ hline)


/-- **A frontier component is an open straight segment of its line**
(T1-i (S2), endpoint form): with the spine `u` on
`K(e) = connectedComponentIn (frontier (flatComponent f p) ∩
stripInterior) e`, there are extended endpoints `a b : EReal` with

    K(e) = {x | ∃ s, a < s < b ∧ x = e + s•u} ,

i.e. `K(e)` is the open straight segment of the line through `e` in
direction `u` with (possibly infinite) endpoints `e + a•u`, `e + b•u`.
Proof: `S := {s | e + s•u ∈ K(e)}` is open
(`frontierComponent_paramSet_open`), preconnected
(`frontierComponent_paramSet_preconnected`) and nonempty (`0 ∈ S` since
`e ∈ K(e)`), so the fleet-proved interval lemma
(`Commons.Topology.Order.open_preconnected_eq_Ioo_ereal`) gives
`S = {s | a < s < b}`; pushing through the parametrisation
`s ↦ e + s•u` (points of `K(e)` lie on the line by the spine and are
`e + s₀•u` by collinearity, with `s₀ ∈ S`) gives the claim. -/
theorem frontierComponent_is_open_segment {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heF : e ∈ frontier (flatComponent f p)) :
    ∃ u : ℝ², ‖u‖ = 1 ∧
      ∃ a' b' : EReal,
        connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e =
          {x : ℝ² | ∃ s : ℝ, a' < (s : EReal) ∧ (s : EReal) < b' ∧ x = e + s • u} := by
  rcases frontierComponent_on_line hf ha heS heF with ⟨u, hu₁, hline⟩
  let S : Set ℝ := {s : ℝ | e + s • u ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e}
  have hSopen : IsOpen S := frontierComponent_paramSet_open hf ha hu₁ hline
  have hSpre : IsPreconnected S := frontierComponent_paramSet_preconnected hu₁ hline
  have hSne : S.Nonempty := by
    refine ⟨0, ?_⟩
    dsimp [S]
    rw [zero_smul, add_zero]
    exact mem_connectedComponentIn ⟨heF, heS⟩
  rcases (Commons.Topology.Order.open_preconnected_eq_Ioo_ereal hSopen hSne hSpre) with ⟨a', b', hSeq⟩
  refine ⟨u, hu₁, a', b', ?_⟩
  ext x
  constructor
  · intro hxK
    have hu_ne : u ≠ 0 := by
      intro h0
      rw [h0] at hu₁
      norm_num at hu₁
    have hxL : x ∈ lineSet e u := (mem_lineSet_iff e u x).mpr (hline x hxK)
    have hφ : signedLineFunc e u x = 0 := (mem_lineSet_iff e u x).mp hxL
    have hdet : det2 (x - e) u = 0 := by
      have h := hφ
      rwa [signedLineFunc_eq_det2 e u x] at h
    rcases exists_smul_of_det2_eq_zero hu_ne hdet with ⟨s₀, hs₀⟩
    have hxeq : x = e + s₀ • u := by
      calc x = e + (x - e) := by abel
        _ = e + s₀ • u := by rw [hs₀]
    have hs₀S : s₀ ∈ S := by
      dsimp [S]
      rw [← hxeq]
      exact hxK
    have hs₀ab : a' < (s₀ : EReal) ∧ (s₀ : EReal) < b' := by
      have hmem : s₀ ∈ {x : ℝ | a' < (x : EReal) ∧ (x : EReal) < b'} := by
        rw [← hSeq]
        exact hs₀S
      exact hmem
    exact ⟨s₀, hs₀ab.1, hs₀ab.2, hxeq⟩
  · rintro ⟨s, has, hsb, hxeq⟩
    have hsS : s ∈ S := by
      rw [hSeq]
      exact ⟨has, hsb⟩
    have hxK : e + s • u ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e := hsS
    rw [hxeq]
    exact hxK


/-- **Adding a closure point keeps a preconnected set preconnected**: if
`K` is preconnected and `q ∈ closure K`, then `K ∪ {q}` is preconnected
(`K` touches `q`, so no open cover can split the union). -/
lemma isPreconnected_insert_of_mem_closure {K : Set ℝ²} {q : ℝ²}
    (hK : IsPreconnected K) (hq : q ∈ closure K) : IsPreconnected (K ∪ {q}) := by
  intro U V hUo hVo hcov hU hV
  have hqmem : q ∈ K ∪ {q} := by simp
  by_cases hqU : q ∈ U
  · by_cases hqV : q ∈ V
    · refine ⟨q, hqmem, hqU, hqV⟩
    · -- q ∈ U only: V meets K (hV, q ∉ V), U meets K (open U ∋ q ∈ closure K)
      have hVK : (K ∩ V).Nonempty := by
        rcases hV with ⟨w, hw⟩
        rcases hw.1 with hwK | hw1
        · exact ⟨w, hwK, hw.2⟩
        · exfalso
          have hwq : w = q := by simpa using hw1
          exact hqV (hwq ▸ hw.2)
      have hUK : (K ∩ U).Nonempty := by
        rw [mem_closure_iff] at hq
        rcases hq U hUo hqU with ⟨w, hwU, hwK⟩
        exact ⟨w, hwK, hwU⟩
      have hcovK : K ⊆ U ∪ V := by
        intro x hxK
        exact hcov (Or.inl hxK)
      rcases hK U V hUo hVo hcovK hUK hVK with ⟨k, hk⟩
      refine ⟨k, Or.inl hk.1, hk.2.1, hk.2.2⟩
  · -- q ∉ U: q ∈ V (q ∈ K∪{q} ⊆ U∪V); symmetric
    have hqV : q ∈ V := by
      rcases hcov hqmem with hqU' | hqV
      · exact False.elim (hqU hqU')
      · exact hqV
    have hUK : (K ∩ U).Nonempty := by
      rcases hU with ⟨w, hw⟩
      rcases hw.1 with hwK | hw1
      · exact ⟨w, hwK, hw.2⟩
      · exfalso
        have hwq : w = q := by simpa using hw1
        exact hqU (hwq ▸ hw.2)
    have hVK : (K ∩ V).Nonempty := by
      rw [mem_closure_iff] at hq
      rcases hq V hVo hqV with ⟨w, hwV, hwK⟩
      exact ⟨w, hwK, hwV⟩
    have hcovK : K ⊆ U ∪ V := by
      intro x hxK
      exact hcov (Or.inl hxK)
    rcases hK U V hUo hVo hcovK hUK hVK with ⟨k, hk⟩
    refine ⟨k, Or.inl hk.1, hk.2.1, hk.2.2⟩

/-- **A connected component of a set that is closed inside `strip` is
itself closed inside `strip`**: for `F` with `closure F ∩ strip ⊆ F`,
every component `connectedComponentIn F e` (`e ∈ F`) satisfies
`closure (connectedComponentIn F e) ∩ strip ⊆ connectedComponentIn F e`.
Proof: a closure point `q ∈ strip` of the component lies in `F`
(relatively closed), so the component through `q` contains the
preconnected `component ∪ {q}` (maximality) — and symmetrically contains
`q`'s component, forcing `q` into the original component. -/
lemma connectedComponentIn_relatively_closed {F strip : Set ℝ²}
    (hFcl : closure F ∩ strip ⊆ F) {e : ℝ²} (heF : e ∈ F) :
    closure (connectedComponentIn F e) ∩ strip ⊆ connectedComponentIn F e := by
  let K : Set ℝ² := connectedComponentIn F e
  intro q hq
  rcases hq with ⟨hqcl, hqstrip⟩
  have hqF : q ∈ F := hFcl ⟨closure_mono (connectedComponentIn_subset F e) hqcl, hqstrip⟩
  have hKpre : IsPreconnected K := isPreconnected_connectedComponentIn
  have hKF : K ⊆ F := connectedComponentIn_subset F e
  have hKqpre : IsPreconnected (K ∪ {q}) := isPreconnected_insert_of_mem_closure hKpre hqcl
  have hKqF : K ∪ {q} ⊆ F := by
    intro x hx
    rcases hx with hxK | hx1
    · exact hKF hxK
    · have hxq : x = q := by simpa using hx1
      rwa [hxq]
  have hqin : q ∈ K ∪ {q} := by simp
  have hsub : K ∪ {q} ⊆ connectedComponentIn F q :=
    IsPreconnected.subset_connectedComponentIn (F := F) hKqpre hqin hKqF
  have heK : e ∈ K := mem_connectedComponentIn heF
  have heKq : e ∈ connectedComponentIn F q := hsub (Or.inl heK)
  have hKqpre' : IsPreconnected (connectedComponentIn F q) := isPreconnected_connectedComponentIn
  have hKqF' : connectedComponentIn F q ⊆ F := connectedComponentIn_subset F q
  exact IsPreconnected.subset_connectedComponentIn (F := F) hKqpre' heKq hKqF' (hsub (Or.inr rfl))

/-- The frontier of a flat component is closed inside the strip interior
(the closure of `∂C ∩ stripInterior` meets `stripInterior` only in
`∂C ∩ stripInterior`, since `∂C` is closed). -/
lemma frontierComponent_frontier_closed_in_strip {C : Set ℝ²} :
    closure (frontier C ∩ stripInterior) ∩ stripInterior ⊆ frontier C ∩ stripInterior := by
  intro q hq
  rcases hq with ⟨hqcl, hqstrip⟩
  have hfrcl : q ∈ frontier C := by
    have hcl : q ∈ closure (frontier C) :=
      closure_mono (by intro x hx; exact hx.1) hqcl
    have hfr : IsClosed (frontier C) := isClosed_frontier
    have hclc : closure (frontier C) = frontier C := hfr.closure_eq
    rwa [hclc] at hcl
  exact ⟨hfrcl, hqstrip⟩

/-- **S3 (no interior endpoints): the frontier component through `e` has
no closure points inside the strip beyond itself** — `K(e)` is closed in
the subspace `stripInterior`, so a maximal frontier arc cannot terminate
at a point of the strip interior (its end points lie on the seam lines
`x0 ∈ {0,1}` or at infinity). -/
theorem frontierComponent_closed_in_strip {f : ℝ² → ℝ³} {p e : ℝ²}
    (heS : e ∈ stripInterior) (heF : e ∈ frontier (flatComponent f p)) :
    closure (connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e) ∩ stripInterior ⊆
      connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e := by
  exact connectedComponentIn_relatively_closed (F := frontier (flatComponent f p) ∩ stripInterior)
    (strip := stripInterior) (frontierComponent_frontier_closed_in_strip (C := flatComponent f p))
    ⟨heF, heS⟩


/-- **Each frontier component is locally isolated from the others**: at
every `x ∈ K(e)` there is a radius `ρ > 0` such that the only frontier
points of `C` inside `B(x,ρ)` are those of `K(e)` itself — no other
frontier component approaches within the ball (immediate from
`frontierComponent_locally_chord_everywhere`: the ball's frontier points
lie on the single chord through `x`, which is inside `K(e)`).  This is
the local separation that underlies the finiteness of arcs (G1). -/
theorem frontierComponent_isolated_locally {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p e x : ℝ²}
    (hx : x ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ y : ℝ², y ∈ frontier (flatComponent f p) ∩ stripInterior → y ∈ Metric.ball x ρ →
        y ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e := by
  rcases frontierComponent_locally_chord_everywhere hf ha hx with ⟨w, ρ, hw, hρ, hballS, hiff, hloc⟩
  refine ⟨ρ, hρ, ?_⟩
  intro y hyF hyball
  have hyFr : y ∈ frontier (flatComponent f p) := hyF.1
  have hφ0 : signedLineFunc x w y = 0 :=
    frontier_mem_chord_of_halfdisk (C := flatComponent f p) (isOpen_flatComponent f p)
      (x := x) (w := w) (ρ := ρ) hiff hyFr hyball
  have hyC : y ∈ chordSet x w ρ := ⟨hyball, hφ0⟩
  have hyKB : y ∈ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e ∩
      Metric.ball x ρ := by
    rw [hloc]
    exact hyC
  exact hyKB.1

/-- **The frontier of a flat component meets each band chunk in a
compact set**: `frontier C ∩ bandChunk a` is compact (`frontier C` is
closed, `bandChunk a` is compact and closed) — the analytic base for the
finiteness of the frontier arcs in any bounded part of the band. -/
lemma isCompact_frontier_bandChunk {C : Set ℝ²} (a : ℝ) (ha : 0 < a) :
    IsCompact (frontier C ∩ bandChunk a) := by
  have hfr : IsClosed (frontier C) := isClosed_frontier (s := C)
  have hbcl : IsClosed (bandChunk a) := isClosed_bandChunk a
  have hclosed : IsClosed (frontier C ∩ bandChunk a) := hfr.inter hbcl
  exact (isCompact_bandChunk a ha).of_isClosed_subset hclosed (by intro x hx; exact hx.2)


end Submission.PaperBand
