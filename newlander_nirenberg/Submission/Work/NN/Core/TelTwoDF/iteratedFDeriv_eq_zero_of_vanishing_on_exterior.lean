import Mathlib
import Submission.Work.NN.Core.TelTwoDF.bumpFlatAux

namespace Work.NN.Core.TelTwoDF

open Set Filter
open scoped Topology

/-- An auxiliary analytic fact: if `h : ℝ → F` is differentiable at `0` with derivative `c`, and
vanishes (to the right of `0`), then `c = 0`.  Indeed the right-hand difference quotients are
identically `0`, and the two-sided derivative, when it exists, is the limit of them. -/
private lemma eq_zero_of_hasDerivAt_of_eventually_eq {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ → F} {c : F} (hd : HasDerivAt h c 0) (h0 : h 0 = 0)
    (hev : ∀ᶠ t in 𝓝[>] (0:ℝ), h t = 0) : c = 0 := by
  have hmono : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] (0:ℝ) :=
    nhdsWithin_mono 0 (fun t (ht : t ∈ Ioi (0:ℝ)) => by
      simp only [mem_compl_iff, mem_singleton_iff]; exact ht.ne')
  have hts : Tendsto (slope h 0) (𝓝[>] (0:ℝ)) (𝓝 c) := hd.tendsto_slope.mono_left hmono
  have hev' : slope h 0 =ᶠ[𝓝[>] (0:ℝ)] (fun _ : ℝ => (0 : F)) := by
    filter_upwards [hev] with t ht
    simp [slope, ht, h0]
  have hconst : Tendsto (fun _ : ℝ => (0 : F)) (𝓝[>] (0:ℝ)) (𝓝 c) :=
    Filter.Tendsto.congr' hev' hts
  exact tendsto_nhds_unique hconst tendsto_const_nhds

/-- If `G` is differentiable at `y` with derivative `L` and vanishes on the half-line
`{y + t w : t ≥ 0}`, then `L w = 0`. -/
private lemma eq_zero_of_hasFDerivAt_of_ray_mem {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {G : (Fin n → ℂ) → F} {y w : Fin n → ℂ} {L : (Fin n → ℂ) →L[ℝ] F}
    (hL : HasFDerivAt G L y) (hGy : G y = 0)
    (hray : ∀ t : ℝ, 0 ≤ t → G (y + t • w) = 0) : L w = 0 := by
  have hγ : HasDerivAt (fun t : ℝ => y + t • w) w 0 := by
    simpa [id] using HasDerivAt.const_add y ((hasDerivAt_id (0:ℝ)).smul_const w)
  have hcomp : HasDerivAt (fun t : ℝ => G (y + t • w)) (L w) 0 := by
    have hL' : HasFDerivAt G L ((fun t : ℝ => y + t • w) 0) := by simpa using hL
    simpa only [Function.comp_def] using hL'.comp_hasDerivAt (0:ℝ) hγ
  refine eq_zero_of_hasDerivAt_of_eventually_eq hcomp ?_ ?_
  · simpa using hGy
  · filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ)) (a := 0)] with t ht
    exact hray t (le_of_lt ht)

/-- For a point `y` of the closed exterior `{z | ∃ j, ρ j ≤ ‖z j‖}` of the open polydisc
`polydisc 0 ρ` and any direction `w` whose `j`-th component points weakly *away* from the origin
(`0 ≤ ⟪y j, w j⟫`), the whole half-line `{y + t w : t ≥ 0}` stays in the closed exterior. -/
private lemma add_smul_mem_exterior {n : ℕ} {ρ : Fin n → ℝ} {y w : Fin n → ℂ} {j : Fin n}
    (hyj : ρ j ≤ ‖y j‖) (hw : 0 ≤ inner ℝ (y j) (w j)) :
    ∀ t : ℝ, 0 ≤ t → ∃ i, ρ i ≤ ‖(y + t • w) i‖ := by
  intro t ht
  refine ⟨j, ?_⟩
  have hcoord : (y + t • w) j = y j + t • w j := rfl
  rw [hcoord]
  have h1 : ‖y j‖ ^ 2 ≤ ‖y j + t • w j‖ ^ 2 := by
    rw [norm_add_sq_real]
    have h2 : inner ℝ (y j) (t • w j) = t * inner ℝ (y j) (w j) := real_inner_smul_right _ _ _
    rw [h2]
    have h3 : 0 ≤ t * inner ℝ (y j) (w j) := mul_nonneg ht hw
    have h4 : 0 ≤ ‖t • w j‖ ^ 2 := sq_nonneg _
    nlinarith
  have h5 : ‖y j‖ ≤ ‖y j + t • w j‖ := by
    have habs := (sq_le_sq.mp h1)
    rw [abs_of_nonneg (norm_nonneg (y j)), abs_of_nonneg (norm_nonneg (y j + t • w j))] at habs
    exact habs
  linarith

/-- A function `G` vanishing on the closed exterior `{z | ∃ j, ρ j ≤ ‖z j‖}` of the open polydisc
`polydisc 0 ρ` has vanishing `fderiv` at every point of that closed exterior.  No regularity at all
is assumed of `G`: if its derivative at `y` exists, the half-line argument forces it to vanish, and
otherwise `fderiv` is `0` by definition. -/
private lemma fderiv_eq_zero_of_vanishing_on_exterior {n : ℕ} {ρ : Fin n → ℝ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : (Fin n → ℂ) → F}
    (hG : ∀ z : Fin n → ℂ, (∃ j, ρ j ≤ ‖z j‖) → G z = 0)
    {y : Fin n → ℂ} (hy : ∃ j, ρ j ≤ ‖y j‖) :
    fderiv ℝ G y = 0 := by
  obtain ⟨j, hyj⟩ := hy
  -- Any derivative of `G` at `y` kills every direction: for a direction pointing weakly away
  -- from the origin in the `j`-th coordinate the half-line `y + t w` (`t ≥ 0`) lies in the
  -- exterior, and a direction pointing towards the origin is the negative of such a direction.
  have key : ∀ L : (Fin n → ℂ) →L[ℝ] F, HasFDerivAt G L y → L = 0 := by
    intro L hL
    have halfRay : ∀ w : Fin n → ℂ, 0 ≤ inner ℝ (y j) (w j) → L w = 0 :=
      fun w hw =>
        eq_zero_of_hasFDerivAt_of_ray_mem hL (hG y ⟨j, hyj⟩)
          (fun t ht => hG (y + t • w) (add_smul_mem_exterior hyj hw t ht))
    ext v
    by_cases hc : 0 ≤ inner ℝ (y j) (v j)
    · simpa using halfRay v hc
    · have hc' : 0 ≤ inner ℝ (y j) ((-v) j) := by
        rw [Pi.neg_apply, inner_neg_right]; linarith [not_le.mp hc]
      have h := halfRay (-v) hc'
      simpa [map_neg] using h
  by_cases hd : DifferentiableAt ℝ G y
  · exact key (fderiv ℝ G y) hd.hasFDerivAt
  · exact fderiv_zero_of_not_differentiableAt hd

/-- A function which vanishes on the closed exterior `{z | ∃ j, ρ j ≤ ‖z j‖}` of the open
polydisc `polydisc 0 ρ` (with `ρ j > 0`) has all its iterated derivatives equal to zero at every
point of that closed exterior.  No regularity whatsoever is required of `p`.

Proof sketch: the closed exterior `E` has the property that for every `y ∈ E` and every direction
`v` the half-line `{y + t v : t > 0}` or `{y + t v : t < 0}` lies in `E` for small `|t|` (look at a
coordinate `j` with `‖y j‖ = ρ j` and the sign of `Re ⟪y j, v j⟫`, and note that `‖y j + t v j‖ > ρ j`
for small `t` of that sign).  Hence for `G := iteratedFDeriv ℝ m p`, which vanishes on `E`, the
one-sided difference quotient of `G` at `y` along `v` is identically `0` near `y`, so the two-sided
derivative, whenever it exists, is `0`; when it does not exist, `fderiv` is `0` by definition. -/
theorem iteratedFDeriv_eq_zero_of_vanishing_on_exterior {n : ℕ} {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {p : (Fin n → ℂ) → ℂ}
    (hp : ∀ z : Fin n → ℂ, (∃ j, ρ j ≤ ‖z j‖) → p z = 0)
    (m : ℕ) {y : Fin n → ℂ} (hy : ∃ j, ρ j ≤ ‖y j‖) :
    iteratedFDeriv ℝ m p y = 0 := by
  have main : ∀ m : ℕ, ∀ z : Fin n → ℂ, (∃ j, ρ j ≤ ‖z j‖) →
      iteratedFDeriv ℝ m p z = 0 := by
    intro m
    induction m with
    | zero =>
      intro z hz
      ext v
      rw [iteratedFDeriv_zero_apply]
      simp only [zero_apply]
      exact hp z hz
    | succ k ih =>
      -- `iteratedFDeriv ℝ (k+1) p = curryLeft.symm ∘ fderiv ℝ (iteratedFDeriv ℝ k p)`, and by
      -- induction `iteratedFDeriv ℝ k p` vanishes on the whole closed exterior.
      intro z hz
      have hf : fderiv ℝ (iteratedFDeriv ℝ k p) z = 0 :=
        fderiv_eq_zero_of_vanishing_on_exterior ih hz
      rw [iteratedFDeriv_succ_eq_comp_left]
      simp only [Function.comp_apply, hf]
      exact LinearIsometryEquiv.map_zero _
  exact main m y hy

end Work.NN.Core.TelTwoDF
