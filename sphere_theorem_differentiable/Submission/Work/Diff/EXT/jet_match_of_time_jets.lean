/-
# The one-sided time jets determine the whole jet at the seam

`Work.Diff.EXT.jet_match_of_time_jets`: let `H : ℝ × E → Z` be `C^∞` on the slab
`S = (Ico 0 T) ×ˢ U` (`T > 0`, `U` open) and `F : ℝ × E → Z` be `C^∞` everywhere, and suppose that
for every `k` and every `y ∈ U` the *pure time* jets agree,
`∂ₜᵏ H (0,y) = ∂ₜᵏ F (0,y)` (the left-hand side being the within-`S` iterated derivative of `H` at
`(0,y)` in the direction `(1,0)`, the right-hand side the ordinary `k`-th derivative of the slice
`t ↦ F (t,y)` at `0`).  Then the *full* iterated Fréchet derivatives of `H` (within the slab) and of
`F` at `(0,y)` agree to all orders.  This is the analytic bridge between the one-sided data of a
`C^∞` function on a half-slab and the ambient jet of its smooth extension; it is used by
`Submission/Work/Diff/EXT/chartMat_twoSided.lean`.

The uniformity of the hypothesis in `y ∈ U` is essential: it says that the time Taylor coefficients
`a_k(y) = ∂ₜᵏ H (0,y)` of `H` agree with those of `F` on the *whole open set* `U`.  Each `a_k` is a
`C^∞` function on `U`, so not only its values but also all its spatial derivatives at `y` match those
of `F` — and those are exactly the mixed derivatives of `H` and `F`.  Without openness of `U` (or
with a different neighbourhood for each order) the statement is false: on a thin `U` the
within-derivatives of the slab in the spatial directions are junk.

## Route

Write `G := H - F` (`C^∞` on the slab).

1. `Work.Diff.EXT.pureTimeJets_sub` (from `flat_of_matching_isOpen`): all *pure time* within-jets of
   `G` at `(0,y)`, `y ∈ U`, vanish.
2. `Work.Diff.EXT.sliceJet_iteratedDerivWithin`: this is the same as the vanishing of all
   one-dimensional within-derivatives of the slices `t ↦ G (t,y)` at `0`.
3. Hadamard's lemma iterated (`factor_smul_of_vanishing_slice`, `iteratedDerivWithin_smul_id_zero`)
   produces, for every `N`, a `C^∞` `Ψ_N` on the slab with `G = z.1^N • Ψ_N` there, i.e.
   `IsTowerInf ((Ico 0 T) ×ˢ U) G`.
4. Divisibility by every power of the time coordinate kills the whole jet of `G` at the seam:
   `fderivWithin` preserves `IsTowerInf` (`IsTowerInf_fderivWithin`), and the `(j+1)`-st
   within-derivative is the `j`-th within-derivative of the `fderivWithin`
   (`iteratedFDerivWithin_succ_apply_right`), so the claim follows by induction on the order.
5. `iteratedFDerivWithin_sub` splits the jet of `G` at the seam, and the slab within-jets of the
   globally smooth `F` are its ambient jets (`iteratedFDerivWithin_eq_iteratedFDeriv`).

Steps 3 and 4 are the general-normed-space forms of `tower_slice_zero` and `jets_zero_of_isTowerInf`
of `Submission/Work/Diff/EXT/twoSided_of_within.lean`.  Those carry `[FiniteDimensional ℝ E]` and
`[CompleteSpace E]` along as unused section variables, and the statement here is about a general
normed space `E`, so the two lemmas are restated and proved in this file
(`tower_slice_zero_normed`, `jets_zero_of_isTowerInf_normed`); their proofs are those of the
finite-dimensional versions, which never use the extra assumptions.
-/
import Mathlib
import Submission.Work.Diff.EXT.JetTowerDefs
import Submission.Work.Diff.EXT.IsTowerInf_fderivWithin
import Submission.Work.Diff.EXT.factor_smul_of_vanishing_slice
import Submission.Work.Diff.EXT.iteratedDerivWithin_smul_id_zero
import Submission.Work.Diff.EXT.sliceJet_iteratedDerivWithin
import Submission.Work.Diff.EXT.flat_of_matching_isOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

open Set
open scoped ContDiff

namespace Work.Diff.EXT

section Helpers

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Z : Type v} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- **The tower.**  If all one-dimensional within-derivatives of the slices `t ↦ δ (t,y)` vanish at
`0` (for `y` in the open set `U`), then `δ` is divisible on the slab by every power
`z ↦ z.1 ^ N` of the time coordinate, with a quotient that again has vanishing slice derivatives at
the seam.  (Hadamard's lemma iterated: at each step the quotient vanishes on the seam, and its slice
derivatives vanish by the one-dimensional Leibniz rule `iteratedDerivWithin_smul_id_zero`.) -/
theorem tower_slice_zero_normed {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U)
    (δ : ℝ × E → Z) (hδ : ContDiffOn ℝ (⊤ : ℕ∞) δ ((Set.Ico 0 T) ×ˢ U))
    (h0 : ∀ (j : ℕ) (y : E), y ∈ U →
      iteratedDerivWithin j (fun t : ℝ => δ (t, y)) (Set.Ico 0 T) 0 = 0) :
    ∀ N : ℕ, ∃ Ψ : ℝ × E → Z,
      ContDiffOn ℝ (⊤ : ℕ∞) Ψ ((Set.Ico 0 T) ×ˢ U) ∧
      (∀ z ∈ (Set.Ico 0 T) ×ˢ U, δ z = z.1 ^ N • Ψ z) ∧
      (∀ (j : ℕ) (y : E), y ∈ U →
        iteratedDerivWithin j (fun t : ℝ => Ψ (t, y)) (Set.Ico 0 T) 0 = 0) := by
  intro N
  induction N with
  | zero => exact ⟨δ, hδ, fun z _ => by simp, h0⟩
  | succ N ih =>
    obtain ⟨Ψ, hΨsm, hΨeq, hΨvan⟩ := ih
    have hΨ0 : ∀ y ∈ U, Ψ (0, y) = 0 := by
      intro y hy
      have h := hΨvan 0 y hy
      rwa [iteratedDerivWithin_zero] at h
    obtain ⟨Ψ', hΨ'sm, hΨ'eq⟩ := factor_smul_of_vanishing_slice (Z := Z) hT hU Ψ hΨsm hΨ0
    refine ⟨Ψ', hΨ'sm, ?_, ?_⟩
    · intro z hz
      rw [hΨeq z hz, hΨ'eq z hz, smul_smul, pow_succ]
    · intro j y hy
      have hslice : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => Ψ' (t, y)) (Set.Ico 0 T) :=
        hΨ'sm.comp (contDiffOn_id.prodMk contDiffOn_const) (fun t ht => ⟨ht, hy⟩)
      refine iteratedDerivWithin_smul_id_zero (Z := Z) hT (fun t : ℝ => Ψ' (t, y)) hslice ?_ j
      intro k
      have hEqOn : Set.EqOn (fun t : ℝ => t • Ψ' (t, y)) (fun t : ℝ => Ψ (t, y))
          (Set.Ico 0 T) := fun t ht => (hΨ'eq (t, y) ⟨ht, hy⟩).symm
      have hmem : (0 : ℝ) ∈ Set.Ico 0 T := ⟨le_refl 0, hT⟩
      have hval : iteratedDerivWithin (k + 1) (fun t : ℝ => t • Ψ' (t, y)) (Set.Ico 0 T) 0
          = iteratedDerivWithin (k + 1) (fun t : ℝ => Ψ (t, y)) (Set.Ico 0 T) 0 :=
        iteratedDerivWithin_congr (n := k + 1) hEqOn hmem
      rw [hval]
      exact hΨvan (k + 1) y hy

/-- The tower property of `tower_slice_zero_normed`. -/
theorem isTowerInf_of_slice_zero_normed {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U)
    (δ : ℝ × E → Z) (hδ : ContDiffOn ℝ (⊤ : ℕ∞) δ ((Set.Ico 0 T) ×ˢ U))
    (h0 : ∀ (j : ℕ) (y : E), y ∈ U →
      iteratedDerivWithin j (fun t : ℝ => δ (t, y)) (Set.Ico 0 T) 0 = 0) :
    IsTowerInf ((Set.Ico 0 T) ×ˢ U) δ := by
  intro N
  obtain ⟨Ψ, hsm, heq, _⟩ := tower_slice_zero_normed hT hU δ hδ h0 N
  exact ⟨Ψ, hsm, heq⟩

/-- **Divisibility by all powers of the time coordinate kills the whole jet at the seam**, for
codomains in a universe containing that of the source (so that the derivative recursion, which
passes from `W` to `ℝ × E →L[ℝ] W`, stays put).  The `(j+1)`-st within-derivative of `G` at `(0,y)`
is, by `iteratedFDerivWithin_succ_apply_right`, the `j`-th within-derivative of `fderivWithin G S`
there, and `IsTowerInf` is preserved by `fderivWithin`; the case `j = 0` follows from `G = z.1 • Ψ`
together with `0.1 = 0`. -/
private theorem jets_zero_aux_normed {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U)
    {W : Type (max u v)} [NormedAddCommGroup W] [NormedSpace ℝ W] :
    ∀ (j : ℕ) (G : ℝ × E → W), IsTowerInf ((Set.Ico 0 T) ×ˢ U) G → ∀ y : E, y ∈ U →
      iteratedFDerivWithin ℝ j G ((Set.Ico 0 T) ×ˢ U) ((0 : ℝ), y) = 0 := by
  have hs : UniqueDiffOn ℝ ((Set.Ico 0 T) ×ˢ U) := slab_uniqueDiffOn (T := T) hU
  have hx : ∀ y : E, y ∈ U → ((0 : ℝ), y) ∈ (Set.Ico 0 T) ×ˢ U :=
    fun y hy => ⟨⟨le_refl 0, hT⟩, hy⟩
  have key : ∀ j : ℕ,
      (∀ {W : Type (max u v)} [NormedAddCommGroup W] [NormedSpace ℝ W]
        (G : ℝ × E → W), IsTowerInf ((Set.Ico 0 T) ×ˢ U) G → ∀ y : E, y ∈ U →
          iteratedFDerivWithin ℝ j G ((Set.Ico 0 T) ×ˢ U) ((0 : ℝ), y) = 0) := by
    intro j
    induction j with
    | zero =>
      intro W _ _ G hG y hy
      rw [iteratedFDerivWithin_zero_eq_comp]
      obtain ⟨Ψ, _, heq⟩ := hG 1
      have hz : G ((0 : ℝ), y) = 0 := by
        rw [heq ((0 : ℝ), y) (hx y hy)]; simp
      rw [Function.comp_apply, hz]
      apply ContinuousMultilinearMap.ext
      intro m
      simp
    | succ j ih =>
      intro W _ _ G hG y hy
      have hD : IsTowerInf ((Set.Ico 0 T) ×ˢ U)
          (fun z => fderivWithin ℝ G ((Set.Ico 0 T) ×ˢ U) z) := IsTowerInf_fderivWithin hs hG
      have hprev := ih (W := ℝ × E →L[ℝ] W)
        (fun z => fderivWithin ℝ G ((Set.Ico 0 T) ×ˢ U) z) hD y hy
      apply ContinuousMultilinearMap.ext
      intro m
      rw [iteratedFDerivWithin_succ_apply_right hs (hx y hy)]
      rw [hprev]
      simp
  intro j G hG y hy
  exact key j G hG y hy

/-- **Divisibility by all powers of the time coordinate kills the whole jet at the seam**, in every
target universe: reduce to `jets_zero_aux_normed` by lifting the codomain to a universe containing
that of the source with `ULift` (the derivative recursion does not change the universe, so the
lifting is harmless). -/
theorem jets_zero_of_isTowerInf_normed {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U)
    {G : ℝ × E → Z} (hG : IsTowerInf ((Set.Ico 0 T) ×ˢ U) G) :
    ∀ (j : ℕ) (y : E), y ∈ U →
      iteratedFDerivWithin ℝ j G ((Set.Ico 0 T) ×ˢ U) ((0 : ℝ), y) = 0 := by
  have hs : UniqueDiffOn ℝ ((Set.Ico 0 T) ×ˢ U) := slab_uniqueDiffOn (T := T) hU
  have hx : ∀ y : E, y ∈ U → ((0 : ℝ), y) ∈ (Set.Ico 0 T) ×ˢ U :=
    fun y hy => ⟨⟨le_refl 0, hT⟩, hy⟩
  intro j
  match j with
  | 0 =>
    intro y hy
    rw [iteratedFDerivWithin_zero_eq_comp]
    obtain ⟨Ψ, _, heq⟩ := hG 1
    have hz : G ((0 : ℝ), y) = 0 := by
      rw [heq ((0 : ℝ), y) (hx y hy)]; simp
    rw [Function.comp_apply, hz]
    apply ContinuousMultilinearMap.ext
    intro m
    simp
  | k + 1 =>
    intro y hy
    let up : Z →L[ℝ] ULift.{max u v, v} Z :=
      (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := Z)).symm.toContinuousLinearMap
    let dn : ULift.{max u v, v} Z →L[ℝ] Z :=
      (ContinuousLinearEquiv.ulift (R₁ := ℝ) (M₁ := Z)).toContinuousLinearMap
    have hGup : IsTowerInf ((Set.Ico 0 T) ×ˢ U) (fun z => up (G z)) := by
      intro N
      obtain ⟨Ψ, hΨ, heq⟩ := hG N
      refine ⟨fun z => up (Ψ z), ?_, ?_⟩
      · exact (up.contDiff.contDiffOn (s := Set.univ)).comp hΨ (fun z _ => Set.mem_univ _)
      · intro z hz
        show up (G z) = z.1 ^ N • up (Ψ z)
        rw [heq z hz, map_smul]
    have hsmup : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => up (G z)) ((Set.Ico 0 T) ×ˢ U) := by
      obtain ⟨Ψ, hΨ, heq⟩ := hGup 0
      exact hΨ.congr (fun z hz => by simpa using heq z hz)
    have haux := jets_zero_aux_normed hT hU (k + 1) (fun z => up (G z)) hGup y hy
    have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_left
      (s := (Set.Ico 0 T) ×ˢ U) (x := ((0 : ℝ), y)) (f := fun z => up (G z)) dn
      (hsmup.contDiffWithinAt (hx y hy)) hs (hx y hy) (i := k + 1) (by simp)
    have hzero : iteratedFDerivWithin ℝ (k + 1) (fun z => dn (up (G z)))
        ((Set.Ico 0 T) ×ˢ U) ((0 : ℝ), y) = 0 := by
      rw [show (fun z => dn (up (G z))) = ⇑dn ∘ (fun z => up (G z)) from rfl]
      rw [hcomp, haux]
      ext m
      simp
    have hfun : (fun z => dn (up (G z))) = G := by
      funext z
      rfl
    rwa [hfun] at hzero

end Helpers

theorem jet_match_of_time_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U)
    (H : ℝ × E → Z) (F : ℝ × E → Z)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ((Set.Ico 0 T) ×ˢ U))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hmatch : ∀ (k : ℕ) (y : E), y ∈ U →
      iteratedFDerivWithin ℝ k H ((Set.Ico 0 T) ×ˢ U) (0, y) (fun _ => (1, 0)) =
        iteratedDeriv k (fun t : ℝ => F (t, y)) 0) :
    ∀ (j : ℕ) (y : E), y ∈ U →
      iteratedFDerivWithin ℝ j H ((Set.Ico 0 T) ×ˢ U) (0, y) =
        iteratedFDeriv ℝ j F (0, y) := by
  intro j y hy
  have hs : UniqueDiffOn ℝ ((Set.Ico 0 T) ×ˢ U) := slab_uniqueDiffOn (T := T) hU
  have hx : ((0 : ℝ), y) ∈ (Set.Ico 0 T) ×ˢ U := ⟨⟨le_refl 0, hT⟩, hy⟩
  have hFon : ContDiffOn ℝ (⊤ : ℕ∞) F ((Set.Ico 0 T) ×ˢ U) := hF.contDiffOn
  have hGsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => H p - F p)
      ((Set.Ico 0 T) ×ˢ U) := hH.sub hFon
  -- (1) the pure time jets of `G = H - F` vanish at the seam
  have hpure := pureTimeJets_sub hT hU H F hH hF hmatch
  -- (2) hence all one-dimensional within-derivatives of its slices vanish
  have hslice : ∀ (j : ℕ) (y : E), y ∈ U →
      iteratedDerivWithin j (fun t : ℝ => H (t, y) - F (t, y)) (Set.Ico 0 T) 0 = 0 := by
    intro j y hy
    rw [← sliceJet_iteratedDerivWithin hT hU (fun p : ℝ × E => H p - F p) hGsm j hy]
    exact hpure j y hy
  -- (3)+(4) hence the whole within-jet of `G` vanishes at the seam
  have hflat := jets_zero_of_isTowerInf_normed hT hU
    (isTowerInf_of_slice_zero_normed hT hU (fun p : ℝ × E => H p - F p) hGsm hslice)
  have hsub := hflat j y hy
  -- (5) split the jet of the difference; the within-jet of the globally smooth `F` is ambient
  rw [iteratedFDerivWithin_sub hs hH hFon hx j] at hsub
  have hle : ((j : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by simp
  have hFw : iteratedFDerivWithin ℝ j F ((Set.Ico 0 T) ×ˢ U) ((0 : ℝ), y)
      = iteratedFDeriv ℝ j F ((0 : ℝ), y) :=
    iteratedFDerivWithin_eq_iteratedFDeriv hs (hF.contDiffAt.of_le hle) hx
  rw [hFw] at hsub
  exact sub_eq_zero.mp hsub

end Work.Diff.EXT
