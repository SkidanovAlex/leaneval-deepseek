/-
STATUS of this file (step (i) is DONE; the statement below is still `sorry`).

Proved here:
* `slab_uniqueDiffOn` -- `UniqueDiffOn ℝ (Ico 0 T ×ˢ U)` for open `U`.
* `hasFTaylorSeriesUpToOn_sub` -- the Taylor series of a difference (absent from Mathlib; built
  from `HasFDerivWithinAt.sub` and `ContinuousOn.sub`).
* `iteratedFDerivWithin_sub` -- `iteratedFDerivWithin ℝ n (f - g) s x = ... f ... - ... g ...` for
  `f`, `g` smooth on a set of unique differentiability (absent from Mathlib; proved by subtracting
  the `ftaylorSeriesWithin` series and using uniqueness of within-derivatives, with the order
  ascription `by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)`).

Remaining gap, in order:

(A) The *line-restriction identity*: for `F` smooth,
    `iteratedFDeriv ℝ k F (0,y) (fun _ => (1,0)) = iteratedDeriv k (fun t => F (t,y)) 0`.
    This is the only missing bridge between the hypothesis of the theorem (stated with
    `iteratedDeriv` on the slice) and the ambient jet of `F`.  Prove it by induction on `k` from
    `iteratedFDeriv_succ_apply_left` together with the chain rule for the curve `t ↦ (t,y)`
    (`HasFDerivAt.comp_hasFDerivAt`).  Note `ContinuousLinearMap.iteratedFDeriv_comp_left` covers
    only *post*-composition with a continuous linear map, so it does not give this directly.
(B) Vanishing of the pure time jets of `G := fun p => H p - F p`:
    `iteratedFDerivWithin ℝ k G s (0,y) (fun _ => (1,0)) = 0`, by `iteratedFDerivWithin_sub`
    (step (i)), the identification of `F`'s slab within-jets with its ambient jets
    (`iteratedFDerivWithin_subset` against `univ`, same `le_top` ascription), (A), and `hmatch`.
(C) Iterated Hadamard factorisation `factor_smul_of_vanishing_slice` to `G = fun p => p.1^N • Ψ_N p`
    (`Ψ_N` smooth on `s`), with the jet shift `∂ₜ^{k+1}G (0,y) = (k+1) • ∂ₜ^k Ψ (0,y)` obtained from
    `fderivWithin_smul` (`HasFDerivWithinAt.smul`) and `UniqueDiffWithinAt ℝ s x` (from
    `slab_uniqueDiffOn`), so that the `Ψ_N` inherit the vanishing of (B).
(D) For `j < N`: every summand of the `j`-th within-derivative of `fun p => p.1^N • Ψ_N p` at
    `(0,y)` carries `∂ₜ^i (p.1^N)` with `i ≤ j < N`, hence `0`; summands where a spatial derivative
    hits `p.1^N` vanish identically.  Same product rule as in (C).  Taking `N > j` gives the claim.

The statement of the theorem below is identical to the independently reviewed
`Diff/EXT/flat_of_matching_final`, which is the intended vehicle for (A)--(D) if the fleet picks it
up; whoever finishes either path should delete the other.
-/
import Mathlib
import Submission.Work.Diff.EXT.MixedSum
import Submission.Work.Diff.EXT.factor_smul_of_vanishing_slice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vanishing time-jets on a half-slab force the whole within-jet to vanish

`Work.Diff.EXT.flat_of_matching_isOpen`: for `H` smooth on `s = (Ico 0 T) ×ˢ U` (`U` open) and
`F` globally smooth, if for every `k` and every `y ∈ U` the *pure time* jets agree,
`∂ₜᵏ H (0,y) = ∂ₜᵏ F (0,y)`, then every within-derivative of `H - F` at `(0,y)` vanishes.

## Why the hypothesis must include `IsOpen U`

`iteratedFDerivWithin` is built from Mathlib's junk-valued `fderivWithin` (`0` whenever `0` is a
valid within-derivative, else `Classical.choose`).  At the seam the within-derivatives are unique
exactly when the tangent cone of the slab at `(0,y)` spans; for `U` open it is `[0,∞) × E`, which
does span, whereas for a thin `U` (e.g. a point, or a codimension ≥ 1 submanifold) it does not and
`hflat`/`hmatch` carry no information in the non-witnessed directions.  Hence `IsOpen U` (and
`0 < T`, so that the seam meets the slab).

## Proof plan

Write `G := H - F` (`ContDiffOn ℝ ∞ G s`, using `hmatch` at `k = 0` to see `G (0,·) = 0`).

1. `s` is uniquely differentiable (`slab_uniqueDiffOn` below), so within-derivatives at the seam
   are the honest Taylor coefficients and `iteratedFDerivWithin ℝ j F s x = iteratedFDeriv ℝ j F x`
   for the globally smooth `F` (`iteratedFDerivWithin_subset` with `s ⊆ univ`).
2. Hence all pure time jets of `G` vanish on the seam.
3. Iterate `factor_smul_of_vanishing_slice`: for every `N` there is `Ψ_N`, smooth on `s`, with
   `G = fun p => p.1^N • Ψ_N p`.  The jet shift at each step uses the first-order product rule
   `fderivWithin_smul` (`UniqueDiffWithinAt ℝ s x` is available from step 1):
   `∂ₜ^{k+1} G (0,y) = (k+1) • ∂ₜᵏ Ψ (0,y)` when `G = t • Ψ`; so the `Ψ_N` inherit the vanishing.
4. Differentiating `fun p => p.1^N • Ψ_N p` `j` times (`j < N`) with the product rule gives that
   every summand carries a factor `∂ₜ^i (p.1^N)` with `i ≤ j < N`, which is `0` at `p.1 = 0`;
   summands where a spatial derivative hits `p.1^N` vanish identically.  Hence the `j`-th within
   jet of `G` at `(0,y)` vanishes, and letting `N → ∞` (i.e. taking `N > j`) is unnecessary: any
   `N > j` suffices.

Note: this Mathlib has no `HasFTaylorSeriesUpToOn.taylor` and no `norm_taylor_sub_le`, so the last
step is done by the explicit product-rule computation above rather than by a Taylor estimate.
-/

namespace Work.Diff.EXT

open Set
open scoped ContDiff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- The Taylor series of a difference is the difference of the Taylor series: the three structure
conditions are the pointwise statements, transported by `HasFDerivWithinAt.sub` and
`ContinuousOn.sub` (there is no such lemma in Mathlib). -/
theorem hasFTaylorSeriesUpToOn_sub {s : Set E'} {f g : E' → F'}
    {pf pg : E' → FormalMultilinearSeries ℝ E' F'} {n : ℕ∞ω}
    (hf : HasFTaylorSeriesUpToOn n f pf s) (hg : HasFTaylorSeriesUpToOn n g pg s) :
    HasFTaylorSeriesUpToOn n (fun z => f z - g z)
      (fun z => pf z - pg z) s := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rw [← hf.zero_eq y hy, ← hg.zero_eq y hy]
    rfl
  · intro m hm y hy
    have h1 : HasFDerivWithinAt (fun z => pf z m - pg z m)
        ((pf y m.succ).curryLeft - (pg y m.succ).curryLeft) s y :=
      (hf.fderivWithin m hm y hy).sub (hg.fderivWithin m hm y hy)
    have h2 : ((pf y - pg y) m.succ).curryLeft
        = (pf y m.succ).curryLeft - (pg y m.succ).curryLeft := rfl
    rw [h2]
    exact h1
  · intro m hm
    exact (hf.cont m hm).sub (hg.cont m hm)

/-- **Within-iterated-derivatives commute with subtraction.**  For `f`, `g` smooth on a set `s`
of unique differentiability, the `n`-th within-derivative of `f - g` is the difference of the
within-derivatives.  Proof: `ftaylorSeriesWithin` gives the two Taylor series; their difference is
a Taylor series for `f - g` (`hasFTaylorSeriesUpToOn_sub`); by uniqueness of the within-derivatives
(`HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`) its coefficients are the
within-derivatives of `f - g`. -/
theorem iteratedFDerivWithin_sub {s : Set E'} (hs : UniqueDiffOn ℝ s) {f g : E' → F'}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g s) {x : E'} (hx : x ∈ s)
    (n : ℕ) :
    iteratedFDerivWithin ℝ n (fun z => f z - g z) s x
      = iteratedFDerivWithin ℝ n f s x - iteratedFDerivWithin ℝ n g s x := by
  have hT := hasFTaylorSeriesUpToOn_sub (hf.ftaylorSeriesWithin hs) (hg.ftaylorSeriesWithin hs)
  have h := hT.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := n)
    (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)) hs hx
  rw [← h]
  simp [ftaylorSeriesWithin]

/-- **The time slice.**  The iterated derivative of `t ↦ Φ (t, z.2)` is the iterated derivative of
`Φ` at `z` composed with the inclusion `inl` of the time axis (time-slice analogue of
`Work.Diff.EXT.iteratedFDeriv_slice_eq`, proved the same way through
`Work.Diff.EXT.iteratedFDeriv_comp_right_at`). -/
theorem iteratedFDeriv_slice_eq_fst {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : ℝ × E → W} {k : ℕ} {z : ℝ × E} (h : ContDiffAt ℝ k Φ z) :
    iteratedFDeriv ℝ k (fun t : ℝ => Φ (t, z.2)) z.1
      = (iteratedFDeriv ℝ k Φ z).compContinuousLinearMap
          (fun _ : Fin k => ContinuousLinearMap.inl ℝ ℝ E) := by
  have hdecomp : (fun t : ℝ => Φ (t, z.2))
      = (fun q : ℝ × E => Φ (q + ((0 : ℝ), z.2))) ∘ (ContinuousLinearMap.inl ℝ ℝ E) := by
    funext t; simp [ContinuousLinearMap.inl_apply]
  have hpt : (ContinuousLinearMap.inl ℝ ℝ E z.1) + ((0 : ℝ), z.2) = z := by
    ext <;> simp [ContinuousLinearMap.inl_apply]
  have hsm : ContDiffAt ℝ k (fun q : ℝ × E => Φ (q + ((0 : ℝ), z.2)))
      (ContinuousLinearMap.inl ℝ ℝ E z.1) :=
    ContDiffAt.comp (ContinuousLinearMap.inl ℝ ℝ E z.1) (by rw [hpt]; exact h)
      (contDiffAt_id.add contDiffAt_const)
  rw [hdecomp, iteratedFDeriv_comp_right_at (ContinuousLinearMap.inl ℝ ℝ E) hsm (le_refl k)]
  congr 1
  rw [iteratedFDeriv_comp_add_right']
  simp only [hpt]

/-- **The line-restriction identity.**  The `k`-th iterated derivative of `F` at `(0,y)` in the
repeated time direction `(1,0)` is the `k`-th iterated derivative of the slice `t ↦ F (t,y)` at `0`.
This is the bridge between the `iteratedDeriv`-based hypothesis of the flatness lemma and the
ambient jet of the smooth function `F`. -/
theorem iteratedFDeriv_prod_line {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : ℝ × E → Z) {k : ℕ} {y : E} (hF : ContDiffAt ℝ k F (0, y)) :
    iteratedFDeriv ℝ k F (0, y) (fun _ => ((1 : ℝ), (0 : E))) =
      iteratedDeriv k (fun t : ℝ => F (t, y)) 0 := by
  rw [iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDeriv_slice_eq_fst (Φ := F) (z := ((0 : ℝ), y)) hF]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.inl_apply]

/-- The slab `(Ico 0 T) ×ˢ U` is a set of unique differentiability as soon as `U` is open:
it is the product of the half-open interval (unique-differentiable by `uniqueDiffOn_Ico`) with the
open set `U` (unique-differentiable by `IsOpen.uniqueDiffOn`). -/
theorem slab_uniqueDiffOn {T : ℝ} {U : Set E} (hU : IsOpen U) :
    UniqueDiffOn ℝ (Set.Ico 0 T ×ˢ U) :=
  (uniqueDiffOn_Ico 0 T).prod hU.uniqueDiffOn

/-- Vanishing of the time jets on the slab is the same as equality of the pure time jets of `H`
and `F`. -/
theorem flat_of_matching_isOpen
    {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U)
    (H F : ℝ × E → Z)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ((Set.Ico 0 T) ×ˢ U))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hmatch : ∀ (k : ℕ) (y : E), y ∈ U →
      iteratedFDerivWithin ℝ k H ((Set.Ico 0 T) ×ˢ U) (0, y) (fun _ => (1, 0)) =
        iteratedDeriv k (fun t : ℝ => F (t, y)) 0) :
    ∀ (j : ℕ) (y : E), y ∈ U →
      iteratedFDerivWithin ℝ j (fun p => H p - F p) ((Set.Ico 0 T) ×ˢ U) (0, y) = 0 := by
  sorry

/-- **Step (B): the pure time jets of `G := H - F` vanish on the seam.**  By
`iteratedFDerivWithin_sub` the jet of `G` is the difference of the jets of `H` and `F`; the
`H`-term is `hmatch`, and the `F`-term is identified with the ambient jet
(`iteratedFDerivWithin_subset` against `univ`) and then with the slice derivative
(`iteratedFDeriv_prod_line`). -/
theorem pureTimeJets_sub {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U) (H F : ℝ × E → Z)
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H ((Set.Ico 0 T) ×ˢ U))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hmatch : ∀ (k : ℕ) (y : E), y ∈ U →
      iteratedFDerivWithin ℝ k H ((Set.Ico 0 T) ×ˢ U) (0, y) (fun _ => (1, 0)) =
        iteratedDeriv k (fun t : ℝ => F (t, y)) 0) :
    ∀ (k : ℕ) (y : E), y ∈ U →
      iteratedFDerivWithin ℝ k (fun p => H p - F p) ((Set.Ico 0 T) ×ˢ U) (0, y)
        (fun _ => ((1 : ℝ), (0 : E))) = 0 := by
  intro k y hy
  have hs : UniqueDiffOn ℝ (Set.Ico 0 T ×ˢ U) := slab_uniqueDiffOn (T := T) hU
  have hx : ((0 : ℝ), y) ∈ Set.Ico 0 T ×ˢ U := ⟨⟨le_refl 0, hT⟩, hy⟩
  have hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.Ico 0 T ×ˢ U) := hF.contDiffOn
  have hle : ((k : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by simp
  -- the jet of the difference is the difference of the jets
  rw [iteratedFDerivWithin_sub hs hH hFs hx k]
  rw [ContinuousMultilinearMap.sub_apply]
  -- the `H`-term is the hypothesis
  rw [hmatch k y hy]
  -- the `F`-term: within = ambient, then ambient = slice
  have hFw : iteratedFDerivWithin ℝ k F (Set.Ico 0 T ×ˢ U) (0, y)
      = iteratedFDeriv ℝ k F (0, y) := by
    rw [← iteratedFDerivWithin_univ]
    exact iteratedFDerivWithin_subset (subset_univ _) hs uniqueDiffOn_univ
      (hF.contDiffOn.of_le hle) hx
  rw [hFw]
  rw [iteratedFDeriv_prod_line F (k := k) (y := y)
    (hF.contDiffAt.of_le hle)]
  exact sub_self _

/-- **First rung of the jet shift (step (C)).**  If `G = fun p => p.1 • Ψ p` on the slab then the
first pure time jet of `G` at a seam point `(0,y)` is the value of `Ψ`:
`∂ₜ G (0,y) = Ψ (0,y)`.  Proof: `iteratedFDerivWithin_one_apply`, the product rule
`fderivWithin_smul`, `fderivWithin_fst`, and `(1,0).1 = 1`. -/
theorem fst_smul_jet_one {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U)
    {Ψ G : ℝ × E → Z} (hG : G = fun p : ℝ × E => p.1 • Ψ p) {y : E} (hy : y ∈ U)
    (hΨ : DifferentiableWithinAt ℝ Ψ (Set.Ico 0 T ×ˢ U) ((0 : ℝ), y)) :
    iteratedFDerivWithin ℝ 1 G (Set.Ico 0 T ×ˢ U) ((0 : ℝ), y) (fun _ => ((1 : ℝ), (0 : E)))
      = Ψ ((0 : ℝ), y) := by
  have hx : ((0 : ℝ), y) ∈ Set.Ico 0 T ×ˢ U := ⟨⟨le_refl 0, hT⟩, hy⟩
  have huniq : UniqueDiffWithinAt ℝ (Set.Ico 0 T ×ˢ U) ((0 : ℝ), y) :=
    (slab_uniqueDiffOn (T := T) hU).uniqueDiffWithinAt hx
  rw [iteratedFDerivWithin_one_apply huniq, hG]
  have key : fderivWithin ℝ (fun p : ℝ × E => p.1 • Ψ p) (Set.Ico 0 T ×ˢ U) ((0 : ℝ), y)
      = fun v : ℝ × E => v.1 • Ψ ((0 : ℝ), y) := by
    rw [show (fun p : ℝ × E => p.1 • Ψ p) = (fun p : ℝ × E => p.1) • Ψ from rfl,
      fderivWithin_smul huniq (by fun_prop) hΨ, fderivWithin_fst huniq]
    ext v
    simp [ContinuousLinearMap.smulRight_apply]
  rw [key]
  simp

/-- **The general rung of the jet shift (remaining piece of step (C)).**  If `G = p.1 • Ψ p` on the
slab with `Ψ` smooth, then `∂ₜ^{k+1} G (0,y) = (k+1) • ∂ₜ^k Ψ (0,y)`: the product rule applied
`k+1` times, only the term where the single `∂ₜ t` lands on the linear factor surviving.
`fst_smul_jet_one` is the case `k = 0`. -/
theorem fst_smul_jet {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U)
    {Ψ G : ℝ × E → Z} (hG : G = fun p : ℝ × E => p.1 • Ψ p)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (Set.Ico 0 T ×ˢ U))
    (k : ℕ) {y : E} (hy : y ∈ U) :
    iteratedFDerivWithin ℝ (k + 1) G (Set.Ico 0 T ×ˢ U) ((0 : ℝ), y)
        (fun _ => ((1 : ℝ), (0 : E)))
      = ((k : ℝ) + 1) • iteratedFDerivWithin ℝ k Ψ (Set.Ico 0 T ×ˢ U) ((0 : ℝ), y)
          (fun _ => ((1 : ℝ), (0 : E))) := by
  sorry

/-
EXACT PROOF PLAN for `iteratedDeriv_smul_id` (derived; the fleet was saturated, so it is written
out rather than proved).

Induction on `k`, generalised over the smooth function `ψ`:

* `k = 0`: `iteratedDeriv 1 (fun t => t • ψ t) 0 = deriv (fun t => t • ψ t) 0`, and the product rule
  at `0` gives `1 • ψ 0 + 0 • deriv ψ 0 = ψ 0`; the right-hand side is `((0:ℝ)+1) • ψ 0`.
* step: with `h1 : deriv (fun t => t • ψ t) = fun t => ψ t + t • deriv ψ t` (from
  `HasDerivAt.smul` applied to `hasDerivAt_id t` and `((hψ.differentiableAt).hasDerivAt)`, then
  `HasDerivAt.deriv` in the `funext`), and `iteratedDeriv_succ`
  (`iteratedDeriv (n+1) f = iteratedDeriv n (deriv f)`),
  `iteratedDeriv (k+2) (fun t => t • ψ t) 0
     = iteratedDeriv (k+1) (fun t => ψ t + t • deriv ψ t) 0`
  by `h1`; then `iteratedDeriv_add` splits this into
  `iteratedDeriv (k+1) ψ 0 + iteratedDeriv (k+1) (fun t => t • deriv ψ t) 0`;
  the induction hypothesis applied to the smooth function `deriv ψ` (whose smoothness is
  `hψ.deriv`-type) rewrites the second term as `((k:ℝ)+1) • iteratedDeriv k (deriv ψ) 0`, and
  `iteratedDeriv_succ` again identifies `iteratedDeriv k (deriv ψ) = iteratedDeriv (k+1) ψ`.
  The sum `x + ((k:ℝ)+1) • x = ((k+1:ℝ)+1) • x` is `← add_smul` + `ring`.

Lemma names to use: `iteratedDeriv_succ`, `HasDerivAt.smul`, `hasDerivAt_id`,
`DifferentiableAt.hasDerivAt`, `iteratedDeriv_add`, `iteratedDeriv_succ`, `ContDiff.deriv`.
-/

/-- **The 1-dimensional rung.**  For a smooth `ψ : ℝ → Z`,
`iteratedDeriv (k+1) (fun t => t • ψ t) 0 = (k+1) • iteratedDeriv k ψ 0`: induct on `k` using
`iteratedDeriv_succ` (`iteratedDeriv (n+1) f = iteratedDeriv n (deriv f)`), the product rule
`HasDerivAt.smul` on `deriv (fun t => t • ψ t) = fun t => ψ t + t • deriv ψ t`, additivity of
`iteratedDeriv`, and `iteratedDeriv_succ` again to see `iteratedDeriv (k-1) (deriv ψ) = iteratedDeriv k ψ`. -/
theorem iteratedDeriv_smul_id {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (ψ : ℝ → Z) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (k : ℕ) :
    iteratedDeriv (k + 1) (fun t : ℝ => t • ψ t) 0
      = ((k : ℝ) + 1) • iteratedDeriv k ψ 0 := by
  /-
  ATTEMPTED PROOF (three `simp`-shape mismatches left; diagnosis for the next pass):

  * base case: `(hasDerivAt_id (0:ℝ)).smul ((hψ.differentiable (by simp)).differentiableAt.hasDerivAt)`
    yields `HasDerivAt (id • ψ) (0 • deriv ψ 0 + 1 • ψ 0) 0`, and `simpa` does not transport this to
    `HasDerivAt (fun t : ℝ => t • ψ t) (ψ 0) 0` — the function form `id • ψ` versus the lambda is
    only definitionally equal, so either state the lambda by hand with
    `HasDerivAt.congr_of_eventuallyEq`/`show`, or state the derivative value as
    `0 • deriv ψ 0 + 1 • ψ 0` and simplify afterwards.
  * step, `hderiv`: same shape issue with `simpa [smul_add, add_comm, one_smul]`.
  * final algebra: after `ih` and `← iteratedDeriv_succ'` the goal is
    `x + ((k:ℝ)+1) • x = (((k+1 : ℕ) : ℝ) + 1) • x`; `rw [← one_smul ℝ x, ← add_smul]` does not
    match because the first summand is `x`, not `1 • x`.  Instead do the algebra as
    `have h : (1 : ℝ) + ((k:ℝ)+1) = ((k+1 : ℕ) : ℝ) + 1 := by push_cast; ring`
    and conclude with `rw [← add_smul, h]` after rewriting `x` with `one_smul`.

  Everything else (`iteratedDeriv_succ'`, `iteratedDeriv_add` with the `by simp` order ascription,
  `ContDiff.iterate_deriv 1` for the smoothness of `deriv ψ`, `contDiffAt_id.smul`) type-checked.
  -/
  sorry