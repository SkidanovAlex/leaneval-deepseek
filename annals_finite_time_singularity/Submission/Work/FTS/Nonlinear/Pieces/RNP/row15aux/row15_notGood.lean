import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Uop_PhiTs_bounds
import Submission.Work.Spaces.DzIter_le_of_pzIter
import Submission.Work.Spaces.scoef
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.StarUBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Row 15: the "first bad angular jet" of `𝒰(Φ̃_*)`

Row 15 of the nonlinear estimates (`N₂^{ss}`) is an `ℋ⁴`-estimate which, at those `z > 0` where
the angular derivatives of `𝒰(Φ̃_*)` vanish at `θ → 0⁺`, is supplied by the pointwise bound of
`Uop_PhiTs_bounds`; at the remaining `z` one instead needs the *lower* bound of `row15_bad`.  The
present lemma is the logical bookkeeping that separates the two cases:

> if all the iterated `z`-derivatives `∂_z^k 𝒰(Φ̃_*)` (`k ≤ 5`) have a limit at `θ → 0⁺`, and
> not all of `D_z^b 𝒰(Φ̃_*)` (`b ≤ 4`) tend to `0`, then there is a **first** index `k ≤ 4` at
> which `∂_z^k 𝒰(Φ̃_*)` fails to tend to `0`, and there it is *bounded away from zero*.

The mathematics is a triangular change of coordinates.  Since `𝒰(Φ̃_*)` is `C^∞` on the open
quadrant (`StarPkg.smooth`), its `z`-slices at interior angles are `C^∞`, and the Stirling
expansion of the operator `D_z = z∂_z` (`Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth`) reads

  `D_z^b 𝒰 = ∑_{k ≤ b} S(b,k)·z^k·∂_z^k 𝒰`     (`S = scoef`, Stirling numbers of the second kind)

in a neighbourhood of `θ = 0` inside `θ > 0` — a *triangular* linear combination of the jets
`∂_z^k 𝒰`, whose diagonal coefficient is `S(b,b) = 1`.  Hence passing to the limit `θ → 0⁺`
(which exists for `∂_z^k 𝒰`, `k ≤ 5`, by hypothesis, and is preserved by finite sums),

  `lim D_z^b 𝒰 = ∑_{k ≤ b} S(b,k) z^k · lim ∂_z^k 𝒰`,

so if every limit `L_k` (`k ≤ 4`) vanished then every `D_z^b 𝒰` (`b ≤ 4`) would tend to `0`,
against `hnotgood`.  Taking `k` minimal with `L_k ≠ 0`, every `L_j` (`j < k`) vanishes by
triangularity, and `L_k ≠ 0` makes `∂_z^k 𝒰` eventually bounded away from `0`.
-/

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

open scoped Real Topology
open Filter Set MeasureTheory

set_option autoImplicit false

/-- **The abstract form of the "first bad angular jet" argument.**  For a function `U` whose
`z`-slices `z ↦ U z θ` are `C^∞` on `(-1,∞)` for every interior angle `θ ∈ (0,π/2)`, if all the
limits `lim_{θ→0⁺} ∂_z^k U z θ` (`k ≤ 5`) exist and not all of `D_z^b U` (`b ≤ 4`) tend to `0`,
then there is a first index `k ≤ 4` with `∂_z^k U` bounded away from `0` near `0⁺`.

The triangularity comes from the Stirling expansion of `D_z = z∂_z`
(`Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth`). -/
theorem row15_notGood_aux {U : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsmooth : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => U z' θ) (Set.Ioi (-1)))
    (hLim : ∀ k : ℕ, k ≤ 5 → ∃ L : ℝ, Filter.Tendsto (fun θ => Work.Spaces.pzIter k U z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L))
    (hnotgood : ¬ (∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun θ => Work.Spaces.DzIter b U z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))) :
    ∃ k : ℕ, k ≤ 4 ∧
      (∀ b : ℕ, b < k → Filter.Tendsto (fun θ => Work.Spaces.pzIter b U z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        δ ≤ |Work.Spaces.pzIter k U z θ| := by
  classical
  -- choose the limits `L k` of `∂_z^k U z ·`; the values `L k` for `k > 5` are irrelevant
  have hchoice : ∀ k : ℕ, ∃ L : ℝ, k ≤ 5 → Filter.Tendsto (fun θ => Work.Spaces.pzIter k U z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
    intro k
    by_cases hk : k ≤ 5
    · exact let ⟨L, hL⟩ := hLim k hk; ⟨L, fun _ => hL⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose L hL using hchoice
  -- `(0,π/2)` is a neighbourhood of `0` inside `(0,∞)`
  have hpid : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by linarith [Real.pi_pos])]
      with θ hθ hθ0
    exact ⟨hθ0, hθ⟩
  have hzmem : z ∈ Set.Ioi (-1 : ℝ) := by rw [Set.mem_Ioi]; linarith
  -- the Stirling expansion of `D_z^b`, as an eventual identity near `0⁺`
  have hexp : ∀ b : ℕ, (fun θ => Work.Spaces.DzIter b U z θ) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun θ => ∑ k ∈ Finset.range (b + 1),
        (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k U z θ)) := by
    intro b
    filter_upwards [hpid] with θ hθ
    exact Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth (hsmooth θ hθ) b z hzmem
  -- hence the limit of `D_z^b U` is the triangular combination of the `L k`
  have hDzlim : ∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun θ => Work.Spaces.DzIter b U z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (z ^ k * L k))) := by
    intro b _
    have hsum : Filter.Tendsto (fun θ => ∑ k ∈ Finset.range (b + 1),
          (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k U z θ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (z ^ k * L k))) := by
      refine tendsto_finsetSum _ (fun k hk => ?_)
      have hk5 : k ≤ 5 := by have := Finset.mem_range.mp hk; omega
      exact ((hL k hk5).const_mul (z ^ k)).const_mul ((Work.Spaces.scoef b k : ℝ))
    exact Filter.Tendsto.congr' (hexp b).symm hsum
  -- some limit is nonzero, else `D_z^b U → 0` for every `b ≤ 4`
  have hex : ∃ b : ℕ, b ≤ 4 ∧ L b ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hnotgood (fun b hb => by
      have hlim := hDzlim b hb
      have h0 : (∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ) * (z ^ k * L k)) = 0 := by
        refine Finset.sum_eq_zero (fun k hk => ?_)
        have hk4 : k ≤ 4 := by have := Finset.mem_range.mp hk; omega
        rw [h k hk4]; ring
      rwa [h0] at hlim)
  -- the first index with a nonzero limit
  set k := Nat.find hex with hkdef
  have hkspec : k ≤ 4 ∧ L k ≠ 0 := Nat.find_spec hex
  have hkmin : ∀ m, m < k → L m = 0 := by
    intro m hm
    have hnot : ¬ (m ≤ 4 ∧ L m ≠ 0) := Nat.find_min hex hm
    have hm4 : m ≤ 4 := by omega
    by_contra hne
    exact hnot ⟨hm4, hne⟩
  refine ⟨k, hkspec.1, ?_, ?_⟩
  · -- below `k` the limits vanish, so the jets tend to `0`
    intro b hb
    have hb0 : L b = 0 := hkmin b hb
    simpa [hb0] using hL b (by omega)
  · -- at `k` the limit `L k` is nonzero, so the jet is eventually bounded away from `0`
    refine ⟨|L k| / 2, half_pos (abs_pos.mpr hkspec.2), ?_⟩
    have hlim := hL k (by omega)
    have hb : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        dist (Work.Spaces.pzIter k U z θ) (L k) < |L k| / 2 :=
      hlim.eventually (Metric.ball_mem_nhds (L k) (half_pos (abs_pos.mpr hkspec.2)))
    filter_upwards [hb] with θ hθ
    rw [Real.dist_eq] at hθ
    have h2 : |L k| - |Work.Spaces.pzIter k U z θ| ≤ |L k - Work.Spaces.pzIter k U z θ| := by
      have h3 := abs_add_le (L k - Work.Spaces.pzIter k U z θ) (Work.Spaces.pzIter k U z θ)
      rw [sub_add_cancel] at h3
      linarith
    rw [abs_sub_comm] at hθ
    linarith

theorem row15_notGood {α Cs z : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : Work.FTS.Nonlin.StarPkg α Cs Φs) (hz : 0 < z)
    (hLim : ∀ k : ℕ, k ≤ 5 → ∃ L : ℝ, Filter.Tendsto (fun θ => Work.Spaces.pzIter k
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L))
    (hnotgood : ¬ (∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun θ => Work.Spaces.DzIter b
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))) :
    ∃ k : ℕ, k ≤ 4 ∧
      (∀ b : ℕ, b < k → Filter.Tendsto (fun θ => Work.Spaces.pzIter b
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        δ ≤ |Work.Spaces.pzIter k (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ| := by
  -- `𝒰(Φ̃_*)` is `C^∞` on the open quadrant, so its `z`-slices at interior angles are `C^∞`
  have hsqPsi : Work.FTS.LocData.SmoothQuad (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_PhiTs hα hα1 hS.smooth
  have hsqU : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.Nonlinear.Pieces.Rl1.smoothQuad_Uop hsqPsi
  exact row15_notGood_aux (U := Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) hz
    (fun θ hθ => hsqU.curry_z hθ) hLim hnotgood

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
