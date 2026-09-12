import Submission.PaperBand.BendSegments

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Flat regions of the band (input to Proposition `main0`)

The set `{x ∈ stripInterior | dN f x = 0}` is the preimage of the *flat*
part of the band (`Ω ∖ U` in the paper): points where the shape operator
vanishes.  This file proves the two basic structural facts about flat
regions used in `main0`:

* on any open preconnected piece of the flat set the unit normal is constant
  (`unitNormal_const_on` — zero derivative on a connected open set, via
  `IsOpen.exists_is_const_of_fderiv_eq_zero`);
* hence the image of such a piece lies in a single affine plane orthogonal
  to that constant normal (`image_in_plane` — the scalar `⟪f ·, N₀⟫` has
  zero derivative, since `Df` is tangent-valued, hence is constant).

(Together with the isometry of `fderiv` this says each flat region maps
isometrically into a plane — the "flat trapezoid" pieces of `main0`.  The
affine structure of `f` on flat pieces, needed to foliate them by straight
segments, is the next step.)
-/

noncomputable section
namespace Submission.PaperBand

/-- `p` is in the *interior* of the flat region: it has an open
neighbourhood on which the shape operator vanishes everywhere. -/
def IsFlatInterior (f : ℝ² → ℝ³) (p : ℝ²) : Prop :=
  ∃ U : Set ℝ², IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, dN f x = 0

/-- The *flat set* inside the strip: points of the strip interior where the
shape operator vanishes (the preimage of the flat part `Ω ∖ U` of the band). -/
def FlatSet (f : ℝ² → ℝ³) : Set ℝ² := {x | x ∈ stripInterior ∧ dN f x = 0}

/-- Membership in the flat set. -/
lemma mem_FlatSet {f : ℝ² → ℝ³} {x : ℝ²} :
    x ∈ FlatSet f ↔ x ∈ stripInterior ∧ dN f x = 0 := by rfl

/-- The flat set lies inside the strip interior. -/
lemma FlatSet_subset_stripInterior (f : ℝ² → ℝ³) : FlatSet f ⊆ stripInterior := by
  intro x hx
  exact (mem_FlatSet.mp hx).1

/-- A point of the strip interior is *flat-interior* iff it is an interior
point of the flat set. -/
lemma IsFlatInterior_iff_mem_interior_FlatSet {f : ℝ² → ℝ³} {p : ℝ²}
    (hp : p ∈ stripInterior) : IsFlatInterior f p ↔ p ∈ interior (FlatSet f) := by
  constructor
  · rintro ⟨U, hUo, hUp, hUflat⟩
    rw [mem_interior]
    refine ⟨U ∩ stripInterior, ?_, ?_, ?_⟩
    · intro x hx
      rw [mem_FlatSet]
      exact ⟨hx.2, hUflat x hx.1⟩
    · exact hUo.inter stripInterior_isOpen
    · exact ⟨hUp, hp⟩
  · rintro hpint
    rw [mem_interior] at hpint
    rcases hpint with ⟨U, hUsub, hUo, hUp⟩
    refine ⟨U, hUo, hUp, ?_⟩
    intro x hx
    exact (mem_FlatSet.mp (hUsub hx)).2

/-- A flat point of the strip interior which is not flat-interior lies on the
frontier of the flat set: it is in the closure of the flat set but not in its
interior. -/
lemma mem_frontier_FlatSet_of_flat_not_interior {f : ℝ² → ℝ³} {p : ℝ²}
    (hpF : p ∈ FlatSet f) (hni : ¬ IsFlatInterior f p) : p ∈ frontier (FlatSet f) := by
  have hpS : p ∈ stripInterior := (mem_FlatSet.mp hpF).1
  rw [frontier]
  rw [Set.mem_diff]
  constructor
  · exact subset_closure hpF
  · intro hpi
    exact hni ((IsFlatInterior_iff_mem_interior_FlatSet (f := f) hpS).2 hpi)

/-- **The unit normal is constant on a flat piece**: on an open preconnected
subset of the strip interior where the shape operator vanishes everywhere,
the unit normal is constant. -/
lemma unitNormal_const_on {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {s : Set ℝ²} (hs : IsOpen s) (hconn : IsPreconnected s)
    (hsub : s ⊆ stripInterior) (hflat : ∀ x ∈ s, dN f x = 0) :
    ∃ N₀ : ℝ³, ∀ x ∈ s, unitNormal f x = N₀ := by
  let N : ℝ² → ℝ³ := fun y => unitNormal f y
  have hdif : DifferentiableOn ℝ N s := by
    exact ((contDiffOn_unitNormal hf).differentiableOn (by simp)).mono hsub
  have hder : s.EqOn (fderiv ℝ N) 0 := by
    intro x hx
    calc
      fderiv ℝ N x = dN f x := by
        simpa [N] using (dN_eq_fderiv (f := f) (x := x) (hsub hx)).symm
      _ = 0 := hflat x hx
  rcases IsOpen.exists_is_const_of_fderiv_eq_zero hs hconn hdif hder with ⟨N₀, hN₀⟩
  refine ⟨N₀, ?_⟩
  intro x hx
  simpa [N] using hN₀ x hx

/-- **The image of a flat piece lies in a plane**: on an open preconnected
subset of the strip interior where the shape operator vanishes everywhere,
there is a unit vector `N₀` and a constant `c` with `⟪f x, N₀⟫ = c` for every
`x` in the set — i.e. `f` maps the flat piece into the affine plane through
`c·N₀` orthogonal to `N₀`. -/
lemma image_in_plane {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {s : Set ℝ²} (hs : IsOpen s) (hconn : IsPreconnected s)
    (hsub : s ⊆ stripInterior) (hflat : ∀ x ∈ s, dN f x = 0) :
    ∃ N₀ : ℝ³, ‖N₀‖ = 1 ∧ ∃ c : ℝ, ∀ x ∈ s, inner ℝ (f x) N₀ = c := by
  by_cases hempty : s.Nonempty
  · rcases unitNormal_const_on hf hs hconn hsub hflat with ⟨N₀, hN₀⟩
    rcases hempty with ⟨x₀, hx₀₀⟩
    have hN₀unit : ‖N₀‖ = 1 := by
      have hn := unitNormal_norm hf x₀ (stripInterior_subset_unitStrip (hsub hx₀₀))
      rw [← hN₀ x₀ hx₀₀]
      exact hn
    let g : ℝ² → ℝ := fun x => inner ℝ (f x) N₀
    have hgdiff : DifferentiableOn ℝ g s := by
      intro x hx
      have hdF : DifferentiableAt ℝ f x := by
        exact ((hf.smooth.mono stripInterior_subset_unitStrip).differentiableOn (by simp)
          x (hsub hx)).differentiableAt (IsOpen.mem_nhds stripInterior_isOpen (hsub hx))
      exact (DifferentiableAt.inner ℝ hdF (differentiableAt_const N₀)).differentiableWithinAt
    have hgder : s.EqOn (fderiv ℝ g) 0 := by
      intro x hx
      apply ContinuousLinearMap.ext
      intro w
      have hdF : DifferentiableAt ℝ f x := by
        exact ((hf.smooth.mono stripInterior_subset_unitStrip).differentiableOn (by simp)
          x (hsub hx)).differentiableAt (IsOpen.mem_nhds stripInterior_isOpen (hsub hx))
      have hfw := fderiv_inner_apply (𝕜 := ℝ) hdF (differentiableAt_const N₀) w
      -- hfw : fderiv ℝ (fun t => ⟪f t, N₀⟫) x w = ⟪f x, 0⟫ + ⟪fderiv f x w, N₀⟫
      have horth : inner ℝ (fderiv ℝ f x w) N₀ = 0 := by
        have hfdec := fderiv_apply_vec_decomp (f := f) x w
        -- fderiv f x w = (w 0) • fderiv f x e0 + (w 1) • fderiv f x e1
        calc
          inner ℝ (fderiv ℝ f x w) N₀
              = inner ℝ ((w 0) • fderiv ℝ f x !₂[1, 0] + (w 1) • fderiv ℝ f x !₂[0, 1]) N₀ := by
                  rw [hfdec]
          _ = (w 0) * inner ℝ (fderiv ℝ f x !₂[1, 0]) N₀ +
              (w 1) * inner ℝ (fderiv ℝ f x !₂[0, 1]) N₀ := by
                  rw [inner_add_left, inner_smul_left, inner_smul_left]
                  simp
          _ = 0 := by
                  have ht0 : inner ℝ (fderiv ℝ f x !₂[1, 0]) N₀ = 0 := by
                    have hteq : fderiv ℝ f x !₂[1, 0] = tangent₀ f x := by
                      simpa using (tangent₀_eq_fderiv (f := f) (x := x) (hsub hx)).symm
                    rw [hteq]
                    have horth0 := tangent₀_normal_orthogonal hf x
                      (stripInterior_subset_unitStrip (hsub hx))
                    rwa [hN₀ x hx] at horth0
                  have ht1 : inner ℝ (fderiv ℝ f x !₂[0, 1]) N₀ = 0 := by
                    have hteq : fderiv ℝ f x !₂[0, 1] = tangent₁ f x := by
                      simpa using (tangent₁_eq_fderiv (f := f) (x := x) (hsub hx)).symm
                    rw [hteq]
                    have horth1 := tangent₁_normal_orthogonal hf x
                      (stripInterior_subset_unitStrip (hsub hx))
                    rwa [hN₀ x hx] at horth1
                  rw [ht0, ht1]
                  ring
      have hfw' : fderiv ℝ (fun t : ℝ² => inner ℝ (f t) N₀) x w = 0 := by
        -- hfw: fderiv ℝ (fun t => inner (f t) N₀) x w = inner (f x) (0) + inner (fderiv f x w) N₀
        simpa [horth] using hfw
      simpa [g] using hfw'
    rcases IsOpen.exists_is_const_of_fderiv_eq_zero hs hconn hgdiff hgder with ⟨c, hc⟩
    refine ⟨N₀, hN₀unit, c, ?_⟩
    intro x hx
    simpa [g] using hc x hx
  · -- s empty
    refine ⟨unitNormal f !₂[0, 0], ?_, 0, ?_⟩
    · have hn := unitNormal_norm hf !₂[0, 0] (by
        rw [unitStrip]
        simp)
      exact hn
    · intro x hx
      exact (hempty ⟨x, hx⟩).elim


/-- Vanishing of the shape operator makes all its frame entries vanish. -/
lemma dNentry_zero_of_dN_zero {f : ℝ² → ℝ³} {x : ℝ²} (h : dN f x = 0) :
    ∀ i j : Fin 2, dNentry f x i j = 0 := by
  intro i j
  dsimp [dNentry]
  rw [h]
  simp

/-- On a flat piece the second directional derivatives of `f` vanish: for
`x` with `dN f x = 0`, `fderiv ℝ (fun y ↦ fderiv ℝ f y v) x w = 0`. -/
lemma secondDeriv_zero_of_flat {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x v w : ℝ²} (hx : x ∈ stripInterior) (hflat : dN f x = 0) :
    fderiv ℝ (fun y : ℝ² => fderiv ℝ f y v) x w = 0 := by
  rw [secondDeriv_vec_general hf x hx v w]
  have hEnt : ∀ i j : Fin 2, dNentry f x i j = 0 := dNentry_zero_of_dN_zero hflat
  have hsc : (v 0) * (w 0) * dNentry f x 0 0 + (v 0) * (w 1) * dNentry f x 1 0 +
        (v 1) * (w 0) * dNentry f x 1 0 + (v 1) * (w 1) * dNentry f x 1 1 = 0 := by
    simp [hEnt]
  rw [hsc]
  simp

/-- The derivative of `f` is constant on a flat piece (open preconnected
subset of the strip interior where the shape operator vanishes). -/
lemma fderiv_const_on_flat {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {s : Set ℝ²} (hs : IsOpen s) (hconn : IsPreconnected s)
    (hsub : s ⊆ stripInterior) (hflat : ∀ x ∈ s, dN f x = 0) {x₀ : ℝ²}
    (hx₀₀ : x₀ ∈ s) :
    ∀ x ∈ s, fderiv ℝ f x = fderiv ℝ f x₀ := by
  intro x hx
  apply ContinuousLinearMap.ext
  intro v
  let g : ℝ² → ℝ³ := fun y => fderiv ℝ f y v
  have hgdiff : DifferentiableOn ℝ g s := by
    intro y hy
    exact (differentiableAt_fderiv_apply hf y (hsub hy) v).differentiableWithinAt
  have hgder : s.EqOn (fderiv ℝ g) 0 := by
    intro y hy
    apply ContinuousLinearMap.ext
    intro w
    simpa [g] using secondDeriv_zero_of_flat hf (x := y) (v := v) (w := w) (hsub hy) (hflat y hy)
  rcases IsOpen.exists_is_const_of_fderiv_eq_zero hs hconn hgdiff hgder with ⟨a, ha⟩
  calc
    fderiv ℝ f x v = a := by
      simpa [g] using ha x hx
    _ = fderiv ℝ f x₀ v := by
      simpa [g] using (ha x₀ hx₀₀).symm

/-- **`f` is affine on each flat piece**: on an open preconnected subset of
the strip interior where the shape operator vanishes, `f` is the affine map
`x ↦ f x₀ + L(x − x₀)` with `L = fderiv f x₀` (a linear isometry).  Together
with `unitNormal_const_on`/`image_in_plane` this says the flat pieces map
rigidly onto planar regions — the trapezoids of Proposition `main0`. -/
lemma affine_on_flat {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {s : Set ℝ²} (hs : IsOpen s) (hconn : IsPreconnected s)
    (hsub : s ⊆ stripInterior) (hflat : ∀ x ∈ s, dN f x = 0) {x₀ : ℝ²}
    (hx₀₀ : x₀ ∈ s) :
    ∀ x ∈ s, f x = f x₀ + (fderiv ℝ f x₀) (x - x₀) := by
  let L : ℝ² →L[ℝ] ℝ³ := fderiv ℝ f x₀
  let g : ℝ² → ℝ³ := fun z => f x₀ + L (z - x₀)
  let ψ : ℝ² → ℝ³ := fun z => f z - g z
  have hfc : ∀ x ∈ s, fderiv ℝ f x = L := by
    intro x hx
    dsimp [L]
    exact fderiv_const_on_flat hf hs hconn hsub hflat hx₀₀ x hx
  have hψdiff : DifferentiableOn ℝ ψ s := by
    intro y hy
    have hdF : DifferentiableAt ℝ f y := by
      exact ((hf.smooth.mono stripInterior_subset_unitStrip).differentiableOn (by simp)
        y (hsub hy)).differentiableAt (IsOpen.mem_nhds stripInterior_isOpen (hsub hy))
    have hdG : DifferentiableAt ℝ g y := by
      dsimp [g]
      -- g z = L z + (f x₀ - L x₀)
      have hge : (fun z : ℝ² => L z + (f x₀ - L x₀)) = (fun z => f x₀ + L (z - x₀)) := by
        funext z
        rw [map_sub]
        abel
      have hlin : DifferentiableAt ℝ (fun z : ℝ² => L z) y := L.differentiableAt
      have hc : DifferentiableAt ℝ (fun _ : ℝ² => (f x₀ - L x₀ : ℝ³)) y :=
        differentiableAt_const (f x₀ - L x₀)
      have hadd : DifferentiableAt ℝ (fun z : ℝ² => L z + (f x₀ - L x₀)) y := hlin.add hc
      rwa [hge] at hadd
    exact (hdF.sub hdG).differentiableWithinAt
  have hψder : s.EqOn (fderiv ℝ ψ) 0 := by
    intro y hy
    have hdF : DifferentiableAt ℝ f y := by
      exact ((hf.smooth.mono stripInterior_subset_unitStrip).differentiableOn (by simp)
        y (hsub hy)).differentiableAt (IsOpen.mem_nhds stripInterior_isOpen (hsub hy))
    have hG : HasFDerivAt g L y := by
      dsimp [g]
      have hge : (fun z : ℝ² => L z + (f x₀ - L x₀)) = (fun z => f x₀ + L (z - x₀)) := by
        funext z
        rw [map_sub]
        abel
      have hlin : HasFDerivAt (fun z : ℝ² => L z) (L : ℝ² →L[ℝ] ℝ³) y := by
        simpa using (L.hasFDerivAt (x := y))
      have hc : HasFDerivAt (fun _ : ℝ² => (f x₀ - L x₀ : ℝ³)) (0 : ℝ² →L[ℝ] ℝ³) y := by
        simpa using (hasFDerivAt_const (𝕜 := ℝ) (c := (f x₀ - L x₀ : ℝ³)) y)
      have hadd : HasFDerivAt (fun z : ℝ² => L z + (f x₀ - L x₀)) (L + 0) y := hlin.add hc
      have : HasFDerivAt (fun z : ℝ² => L z + (f x₀ - L x₀)) L y := by
        simpa using hadd
      rwa [hge] at this
    have hzero : fderiv ℝ ψ y = 0 := by
      have hdG : DifferentiableAt ℝ g y := by
        dsimp [g]
        have hge : (fun z : ℝ² => L z + (f x₀ - L x₀)) = (fun z => f x₀ + L (z - x₀)) := by
          funext z
          rw [map_sub]
          abel
        have hlin : DifferentiableAt ℝ (fun z : ℝ² => L z) y := L.differentiableAt
        have hc : DifferentiableAt ℝ (fun _ : ℝ² => (f x₀ - L x₀ : ℝ³)) y :=
          differentiableAt_const (f x₀ - L x₀)
        have hadd : DifferentiableAt ℝ (fun z : ℝ² => L z + (f x₀ - L x₀)) y := hlin.add hc
        rwa [hge] at hadd
      have hfder : fderiv ℝ ψ y = fderiv ℝ f y - fderiv ℝ g y := by
        dsimp [ψ]
        exact fderiv_sub hdF hdG
      rw [hfder]
      have hfc' : fderiv ℝ f y = L := hfc y hy
      have hgder : fderiv ℝ g y = L := hG.fderiv
      rw [hfc', hgder]
      simp
    exact hzero
  rcases IsOpen.exists_is_const_of_fderiv_eq_zero hs hconn hψdiff hψder with ⟨c, hc⟩
  intro x hx
  have hψ₀ : ψ x₀ = 0 := by
    dsimp [ψ, g]
    rw [map_sub]
    simp
  have hψx : ψ x = 0 := by
    calc
      ψ x = c := hc x hx
      _ = ψ x₀ := (hc x₀ hx₀₀).symm
      _ = 0 := hψ₀
  -- ψ x = 0 says f x - (f x₀ + L (x - x₀)) = 0
  have hmain : f x - (f x₀ + (fderiv ℝ f x₀) (x - x₀)) = 0 := by
    dsimp [ψ, g, L] at hψx
    simpa using hψx
  calc
    f x = (f x₀ + (fderiv ℝ f x₀) (x - x₀)) +
        (f x - (f x₀ + (fderiv ℝ f x₀) (x - x₀))) := by abel
    _ = f x₀ + (fderiv ℝ f x₀) (x - x₀) + 0 := by rw [hmain]
    _ = f x₀ + (fderiv ℝ f x₀) (x - x₀) := by simp

end Submission.PaperBand
end
