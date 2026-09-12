import Submission.PaperBand.FlatRegions

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Bends through flat regions (first step of Proposition `main0`)

`KernelMaximal.kernel_segment_reaches_boundary_or_flat` shows a maximal
kernel segment (a pre-bend) in `U = {dN ≠ 0}` can only stop at the boundary
of the strip or at a *flat* point (`dN = 0`).  This file takes the next step
of Proposition `main0`: what happens at such a flat point.

* **Continuation through a flat region** (`kernel_segment_extend_into_flat`):
  if the endpoint of a kernel segment lies *inside* an open region where the
  shape operator vanishes, the straight segment continues past it in the same
  direction — trivially a kernel segment, since `dN = 0` makes every
  direction a kernel direction.  So a maximal pre-bend can only stop at the
  strip boundary or on the *boundary* of a flat region, never inside one.

* **Straight chords of a flat piece are pre-bends**
  (`flat_chord_is_prebend`): on an open preconnected flat piece `s`
  (`dN = 0` on `s`), any straight chord `{x₀ + t • v}` lying in `s` satisfies
  the three bend properties — points in the strip interior with `v` a kernel
  direction (`dN = 0` makes this automatic), the image of `f` along the chord
  is affine (`FlatRegions.affine_on_flat`), and the unit normal is constant
  (`FlatRegions.unitNormal_const_on`).  These are the leaves that foliate the
  flat trapezoids of `main0`, interpolating between their two bend sides.
-/

noncomputable section
namespace Submission.PaperBand

/-- **A kernel segment continues straight through a flat region**: if the
endpoint `x₀ + ε • w₀` of a kernel segment lies inside an open region `U`
where the shape operator vanishes (a flat region), then the segment extends
past the endpoint in the same direction `w₀` — on `U` every direction is a
kernel direction (`dN = 0`), so the kernel condition holds automatically
there. -/
lemma kernel_segment_extend_into_flat {f : ℝ² → ℝ³} {x₀ w₀ : ℝ²} {ε : ℝ}
    (hseg : ∀ s ∈ Set.Icc 0 ε,
      x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0)
    {U : Set ℝ²} (hU : IsOpen U) (hUp : x₀ + ε • w₀ ∈ U)
    (hUflat : ∀ x ∈ U, dN f x = 0) (hUstrip : U ⊆ stripInterior) :
    ∃ ε' > ε, ∀ s ∈ Set.Icc 0 ε',
      x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0 := by
  have hγcont : ContinuousAt (fun s : ℝ => x₀ + s • w₀) ε := by fun_prop
  have hpre : {s : ℝ | x₀ + s • w₀ ∈ U} ∈ 𝓝 ε :=
    hγcont.preimage_mem_nhds (IsOpen.mem_nhds hU hUp)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨η, hη0, hη⟩
  let ε' : ℝ := ε + η / 2
  have hε' : ε < ε' := by
    dsimp [ε']
    linarith [hη0]
  refine ⟨ε', hε', ?_⟩
  intro s hs
  rcases Set.mem_Icc.mp hs with ⟨hs0, hsε'⟩
  by_cases hsε : s ≤ ε
  · exact hseg s (by rw [Set.mem_Icc]; constructor <;> linarith)
  · have hsεgt : ε < s := lt_of_not_ge hsε
    have hsη : s ∈ Metric.ball ε η := by
      rw [Metric.mem_ball]
      rw [Real.dist_eq]
      rw [abs_of_pos (by linarith : 0 < s - ε)]
      have hε'le : s - ε ≤ η / 2 := by
        dsimp [ε'] at hsε'
        linarith
      exact lt_of_le_of_lt hε'le (by linarith [hη0])
    have hsU : x₀ + s • w₀ ∈ U := hη hsη
    constructor
    · exact hUstrip hsU
    · have hd : dN f (x₀ + s • w₀) = 0 := hUflat (x₀ + s • w₀) hsU
      rw [hd]
      simp

/-- **Straight chords of a flat piece are pre-bends**: on an open
preconnected flat piece `s` (the shape operator vanishes on `s`), a straight
chord `{x₀ + t • v}` lying in `s` satisfies the three bend properties:
points in the strip interior with `v` a kernel direction of the shape
operator, the image of `f` along the chord affine with derivative
`fderiv f x₀ v`, and the unit normal constant. -/
lemma flat_chord_is_prebend {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {s : Set ℝ²} (hs : IsOpen s) (hconn : IsPreconnected s)
    (hsub : s ⊆ stripInterior) (hflat : ∀ x ∈ s, dN f x = 0)
    {x₀ : ℝ²} (hx₀₀ : x₀ ∈ s) {v : ℝ²} {A B : ℝ}
    (hseg : ∀ t ∈ Set.Icc A B, x₀ + t • v ∈ s) :
    (∀ t ∈ Set.Icc A B,
      x₀ + t • v ∈ stripInterior ∧ dN f (x₀ + t • v) v = 0) ∧
    (∀ t ∈ Set.Icc A B,
      f (x₀ + t • v) = f x₀ + t • (fderiv ℝ f x₀ v)) ∧
    (∀ t ∈ Set.Icc A B, unitNormal f (x₀ + t • v) = unitNormal f x₀) := by
  have haff := affine_on_flat hf hs hconn hsub hflat hx₀₀
  rcases unitNormal_const_on hf hs hconn hsub hflat with ⟨N₀, hN₀⟩
  constructor
  · intro t ht
    have htS : x₀ + t • v ∈ s := hseg t ht
    constructor
    · exact hsub htS
    · have hd : dN f (x₀ + t • v) = 0 := hflat (x₀ + t • v) htS
      rw [hd]
      simp
  constructor
  · intro t ht
    have htS : x₀ + t • v ∈ s := hseg t ht
    have hx := haff (x₀ + t • v) htS
    -- f (x₀ + t•v) = f x₀ + (fderiv f x₀) ((x₀ + t•v) - x₀)
    have hlin : (fderiv ℝ f x₀) ((x₀ + t • v) - x₀) = t • (fderiv ℝ f x₀ v) := by
      have hsub' : (x₀ + t • v) - x₀ = t • v := by abel
      rw [hsub', map_smul]
    calc
      f (x₀ + t • v) = f x₀ + (fderiv ℝ f x₀) ((x₀ + t • v) - x₀) := hx
      _ = f x₀ + t • (fderiv ℝ f x₀ v) := by rw [hlin]
  · intro t ht
    have htS : x₀ + t • v ∈ s := hseg t ht
    calc
      unitNormal f (x₀ + t • v) = N₀ := hN₀ (x₀ + t • v) htS
      _ = unitNormal f x₀ := (hN₀ x₀ hx₀₀).symm

end Submission.PaperBand
end
