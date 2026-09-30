import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter Metric Set Function
open scoped Real ENNReal Topology

noncomputable section

namespace Commons.NumberTheory.Linnik

/-!
# A good radius for the completed Dirichlet L-function

`goodRadius_pair`: for a primitive non-trivial character `χ mod N` and any `R ≥ 2`,
there is a radius `T ∈ (2R, 2R+1]` whose circle `|z| = T` contains no zero of the
completed L-function `Λ(χ, ·)`.

## Proof

The completed L-function `Λ` of a non-trivial character is entire (`Differentiable ℂ`)
and does not vanish identically (`Λ(0) ≠ 0`).  Hence its divisor on any closed ball is
a locally-finitely-supported integer-valued function whose support contains every zero
inside the ball; a closed ball being compact, the support is *finite*, so the zero set
inside `closedBall 0 (2R+1)` is finite.  The norms of these finitely many zeros form a
finite set of "bad" radii; a finite set of reals cannot cover the interval
`(2R, 2R+1]` (Lebesgue measure), so some `T` in that interval avoids all of them, and
the circle of radius `T` is zero-free.
-/

/-- A finite set of reals cannot contain the whole half-open interval `(a, b]`. -/
lemma exists_notMem_Ioc_of_finite {S : Set ℝ} (hS : S.Finite) {a b : ℝ} (hab : a < b) :
    ∃ x : ℝ, a < x ∧ x ≤ b ∧ x ∉ S := by
  classical
  by_contra h
  have h_all : ∀ x : ℝ, a < x → x ≤ b → x ∈ S := by
    intro x hxa hxb
    by_contra hxS
    exact h ⟨x, hxa, hxb, hxS⟩
  have hsub : Set.Ioc a b ⊆ S := by
    intro x hx
    exact h_all x hx.1 hx.2
  have hvol_le : MeasureTheory.volume (Set.Ioc a b) ≤ MeasureTheory.volume S := by
    exact MeasureTheory.measure_mono hsub
  have hvolS : MeasureTheory.volume S = 0 := hS.measure_zero MeasureTheory.volume
  have hvol_le0 : MeasureTheory.volume (Set.Ioc a b) ≤ 0 := by simpa [hvolS] using hvol_le
  have hvol_eq0 : MeasureTheory.volume (Set.Ioc a b) = 0 := by
    exact le_antisymm hvol_le0 (by exact bot_le)
  have hlen : MeasureTheory.volume (Set.Ioc a b) = ENNReal.ofReal (b - a) := Real.volume_Ioc
  have hlen_ne : ENNReal.ofReal (b - a) ≠ 0 := by
    intro hb
    have hba_le : b - a ≤ 0 := ENNReal.ofReal_eq_zero.mp hb
    linarith
  apply hlen_ne
  rw [hlen] at hvol_eq0
  exact hvol_eq0

/-- The divisor coefficient of a non-zero entire function is non-zero at every zero. -/
lemma divisor_ne_zero_of_apply_eq_zero {f : ℂ → ℂ} (hfdiff : Differentiable ℂ f)
    (hfne : f ≠ 0) {U : Set ℂ} {z : ℂ} (hz : z ∈ U) (hfz : f z = 0) :
    MeromorphicOn.divisor f U z ≠ 0 := by
  have hUan : AnalyticOnNhd ℂ f U := by
    intro z0 hz0
    exact hfdiff.analyticAt z0
  have hz_an : AnalyticAt ℂ f z := hfdiff.analyticAt z
  have hord0 : analyticOrderAt f z ≠ 0 := (AnalyticAt.analyticOrderAt_ne_zero hz_an).2 hfz
  have hordtop : analyticOrderAt f z ≠ ⊤ := by
    intro ht
    exact hfne ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (z : ℂ)
      (by intro z0; exact hfdiff.analyticAt z0)).1 ht)
  have hdiv_eq : MeromorphicOn.divisor f U z = (ENat.map Nat.cast (analyticOrderAt f z)).untop₀ := by
    simpa using (MeromorphicOn.AnalyticOnNhd.divisor_apply hUan hz)
  rw [hdiv_eq]
  rcases ENat.ne_top_iff_exists.mp hordtop with ⟨m, hm⟩
  have hm0 : m ≠ 0 := by
    intro hz0
    apply hord0
    rw [← hm, hz0]
    simp
  rw [← hm]
  rw [ENat.map_natCast]
  rw [WithTop.untop₀_coe]
  exact_mod_cast hm0

/-- **A good radius.**  For a primitive non-trivial character `χ mod N` and every `R ≥ 2`
there is `T ∈ (2R, 2R+1]` such that the completed L-function has no zero on the circle
`|z| = T`. -/
theorem goodRadius_pair {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (R : ℝ) (hR : 2 ≤ R) :
    ∃ T : ℝ, 2 * R < T ∧ T ≤ 2 * R + 1 ∧
      ∀ z : ℂ, ‖z‖ = T → DirichletCharacter.completedLFunction χ z ≠ 0 := by
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let K : Set ℂ := Metric.closedBall (0 : ℂ) (2 * R + 1)
  let Z : Set ℂ := {z : ℂ | Λ z = 0 ∧ ‖z‖ ≤ 2 * R + 1}
  let B : Set ℝ := (fun z : ℂ => ‖z‖) '' Z
  have hΛdiff : Differentiable ℂ Λ := by
    dsimp [Λ]
    exact DirichletCharacter.differentiable_completedLFunction hχ
  have hΛ0 : Λ 0 ≠ 0 := by
    dsimp [Λ]
    exact Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
  have hΛne : Λ ≠ 0 := by
    intro hz
    exact hΛ0 (congrFun hz 0)
  have hΛan : AnalyticOnNhd ℂ Λ K := by
    intro z0 hz0
    exact hΛdiff.analyticAt z0
  have hKcomp : IsCompact K := isCompact_closedBall (0 : ℂ) (2 * R + 1)
  have hsup : (Function.support (fun u : ℂ => MeromorphicOn.divisor Λ K u)).Finite := by
    simpa using (MeromorphicOn.divisor_support_finite_of_subset (f := Λ) (U := K) (V := K)
      hΛan.meromorphicOn hKcomp (by intro z0 hz0; exact hz0))
  have hZsub : Z ⊆ Function.support (fun u : ℂ => MeromorphicOn.divisor Λ K u) := by
    intro z hz
    rw [Function.mem_support]
    have hzK : z ∈ K := by
      dsimp [K]
      simpa [dist_eq_norm] using hz.2
    exact divisor_ne_zero_of_apply_eq_zero hΛdiff hΛne hzK hz.1
  have hZfin : Z.Finite := hsup.subset hZsub
  have hBfin : B.Finite := by
    dsimp [B]
    exact Set.Finite.image (fun z : ℂ => ‖z‖) hZfin
  rcases exists_notMem_Ioc_of_finite hBfin (a := 2 * R) (b := 2 * R + 1) (by linarith)
    with ⟨T, hTgt, hTle, hTnB⟩
  refine ⟨T, hTgt, hTle, ?_⟩
  intro z hzT
  intro hzΛ0
  apply hTnB
  rw [← hzT]
  dsimp [B]
  exact Set.mem_image_of_mem (f := fun z : ℂ => ‖z‖) (x := z) ⟨hzΛ0, by
    rw [hzT]
    exact hTle⟩

end Commons.NumberTheory.Linnik
