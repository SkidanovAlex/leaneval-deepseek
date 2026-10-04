import Mathlib
import Submission.Diff.Grad
import Submission.Work.Diff.GE.Api
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.algebra_bounds
import Submission.Work.Diff.GE.covRm_frame_evol_abs
-- import Submission.Work.Diff.GE.covRm_frame_evol_abs_via_le   (broken in flight; alternative route)
import Submission.Work.Diff.GE.dRmNormSq_eq_sum_of_isONFrame
import Submission.Work.Diff.GE.laplAt_dRmNormSq_eq
import Submission.Work.Diff.GE.hasDerivWithinAt_covRm_frame_le
import Submission.Work.Diff.GE.exists_ON_frame_family_uniformBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# EV2: the evolution of `|∇Rm|²` under the Ricci flow

`EvolDRmNormSq I M` is the contract: there is a universal constant `c ≥ 0` such that along every
Ricci flow `G` on `[0,T)`, at every `t ∈ [0,T)` and every `x : M`, the function
`s ↦ dRmNormSq (G s) x = |∇Rm|²(G s, x)` is differentiable in `s` at `t` and its derivative is at
most `Δ|∇Rm|²(t,x) + c |Rm| |∇Rm|²`.

The classical proof (Hamilton 1982, §7 and §13; Chow–Knopf Ch. 6, Topping Ch. 2) is

`∂ₜ|∇Rm|² = 2⟨∇Rm, ∂ₜ∇Rm⟩ = 2⟨∇Rm, Δ∇Rm + Rm ∗ ∇Rm⟩ = Δ|∇Rm|² − 2|∇²Rm|² + 2⟨∇Rm, Rm ∗ ∇Rm⟩`,

so `∂ₜ|∇Rm|² ≤ Δ|∇Rm|² + c|Rm| |∇Rm|²` by the Cauchy–Schwarz bound on the reaction term.

Formally the computation is split as follows.  The value `dRmNormSq (G s) x` is computed with the
`Classical.epsilon`-chosen frame `onFrame (G s) x`; since it is frame-independent
(`dRmNormSq_eq_sum_of_isONFrame`) it may be evaluated in *any* orthonormal frame, in particular in
a smooth family `s ↦ e s` of orthonormal frames at `x` (`exists_ON_frame_family_onFrame`) which
starts at `onFrame (G t) x` and has a universally bounded velocity.  Differentiating the resulting
sum of squares uses the componentwise evolution estimate
`hasDerivWithinAt_covRm_frame_le`, while the comparison with `laplAt` uses the Kato identity
`laplAt_dRmNormSq_eq` and the elementary bounds `algebra_bounds`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

/-- The five index slots of a component of `∇Rm`. -/
abbrev ev2_Idx5 (n : ℕ) : Type := Fin n × Fin n × Fin n × Fin n × Fin n

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## Elementary calculus lemmas -/

/-- **Derivative of a finite sum of squares**: if each `f i` has derivative `f' i`, then
`∑ i, (f i)²` has derivative `∑ i, 2 * f i t * f' i`. -/
theorem ev2_hasDerivWithinAt_sum_sq {ι : Type*} [Fintype ι] {f : ι → ℝ → ℝ} {f' : ι → ℝ}
    {s : Set ℝ} {t : ℝ} (h : ∀ i, HasDerivWithinAt (f i) (f' i) s t) :
    HasDerivWithinAt (fun x ↦ ∑ i, (f i x) ^ 2) (∑ i, 2 * f i t * f' i) s t := by
  have h1 := HasDerivWithinAt.sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ (h i).mul (h i))
  convert h1 using 1
  · ext x
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [pow_two, Pi.mul_apply]
  · exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Cauchy–Schwarz for the `ℓ¹`-norm**: `(∑ i, |g i|)² ≤ card ι * ∑ i, (g i)²`. -/
theorem ev2_sum_abs_sq_le_card_mul {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    (∑ i, |g i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (g i) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i ↦ |g i|)
  simpa only [Finset.card_univ, sq_abs] using h


/-- **Cauchy–Schwarz for the `ℓ¹`-norm, in `√`-form**: `∑ |g i| ≤ √(card ι) · √(∑ (g i)²)`. -/
theorem ev2_sum_abs_le_sqrt_card_mul_sqrt_sum_sq {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    ∑ i, |g i| ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, (g i) ^ 2) := by
  have h := ev2_sum_abs_sq_le_card_mul (g := g)
  have h0 : 0 ≤ ∑ i, |g i| := Finset.sum_nonneg (fun i _ ↦ abs_nonneg _)
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hsq : 0 ≤ ∑ i, (g i) ^ 2 := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  calc ∑ i, |g i| = Real.sqrt ((∑ i, |g i|) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, (g i) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, (g i) ^ 2) := Real.sqrt_mul hcard _

/-- **The final arithmetic step of the assembly, isolated.**  If a family `D` of derivatives
approximates a family `lp` of rough-Laplacian components to within `B` (two-sidedly), then the
weighted sum `∑ 2 c q (D q)` is bounded by `∑ 2 c q (lp q)` plus the Cauchy–Schwarz term
`2 B ∑ |c q|`.  The two-sided hypothesis is essential: for `c q < 0` an upper bound on `D q` gives
no upper bound on `2 c q D q`. -/
theorem ev2_sum_two_mul_le_of_abs_sub_le {ι : Type*} [Fintype ι] (c D lp : ι → ℝ) {B : ℝ}
    (h : ∀ q, |D q - lp q| ≤ B) :
    ∑ q, 2 * c q * D q ≤ (∑ q, 2 * (c q * lp q)) + 2 * B * ∑ q, |c q| := by
  have hq : ∀ q, 2 * c q * D q ≤ 2 * (c q * lp q) + 2 * |c q| * B := by
    intro q
    have h1 : D q ≤ lp q + B := by have := (abs_le.mp (h q)).2; linarith
    have h2 : lp q - B ≤ D q := by have := (abs_le.mp (h q)).1; linarith
    rcases le_total (c q) 0 with hc | hc
    · -- `c q ≤ 0`: use that `D q` bounds `lp q - B` from above
      have h3 : 2 * c q * D q ≤ 2 * c q * (lp q - B) := by
        have hcc : 2 * c q ≤ 0 := by linarith
        exact mul_le_mul_of_nonpos_left h2 hcc
      have h4 : 2 * c q * (lp q - B) = 2 * (c q * lp q) + 2 * |c q| * B := by
        rw [abs_of_nonpos hc]; ring
      linarith [h3, h4.le, h4.ge]
    · have h3 : 2 * c q * D q ≤ 2 * c q * (lp q + B) := by
        have hcc : 0 ≤ 2 * c q := by linarith
        exact mul_le_mul_of_nonneg_left h1 hcc
      have h4 : 2 * c q * (lp q + B) = 2 * (c q * lp q) + 2 * |c q| * B := by
        rw [abs_of_nonneg hc]; ring
      linarith [h3, h4.le, h4.ge]
  calc ∑ q, 2 * c q * D q
      ≤ ∑ q, (2 * (c q * lp q) + 2 * |c q| * B) := Finset.sum_le_sum (fun q _ ↦ hq q)
    _ = (∑ q, 2 * (c q * lp q)) + 2 * B * ∑ q, |c q| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun q _ ↦ by ring)

/-- The number of components of `∇Rm`: `card (ev2_Idx5 n) = n⁵`. -/
theorem ev2_card_idx (n : ℕ) : Fintype.card (ev2_Idx5 n) = n ^ 5 := by
  simp only [ev2_Idx5, Fintype.card_prod, Fintype.card_fin]
  ring

/-- `|∇Rm|² ≥ 0`, needed to rewrite `√|∇Rm|² · √|∇Rm|² = |∇Rm|²`. -/
theorem ev2_dRmNormSq_nonneg {g : SMet I M} {x : M} : 0 ≤ dRmNormSq g x := by
  refine Finset.sum_nonneg fun m _ ↦ Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun l _ ↦ sq_nonneg _

theorem ev2_sqrt_dRmNormSq_mul_self {g : SMet I M} {x : M} :
    Real.sqrt (dRmNormSq g x) * Real.sqrt (dRmNormSq g x) = dRmNormSq g x :=
  Real.mul_self_sqrt (ev2_dRmNormSq_nonneg (I := I) (M := M) (g := g) (x := x))


/-! ## The contract -/

/-! ### Assembly plan (verified ingredients)

With `g := G t`, `r := √(rmNormSq (G t) x)`, `a := dRmNormSq (G t) x`, and a smooth family
`s ↦ e s` of frames at `x`, orthonormal for `G s` near `t`, differentiable at `t` with velocity
`edot` of size `|edot i|² ≤ K |Rm|²` (`exists_ON_frame_family_onFrame`), whose value at `t` is
`onFrame (G t) x`:

* `dRmNormSq (G s) x = ∑ q, (covRm (G s) x (e s q))²` for `s` near `t`
  (`dRmNormSq_eq_sum_of_isONFrame`);
* each component is differentiable with derivative bounded by the corresponding component of the
  rough Laplacian plus `C (1+K) r √a` (`hasDerivWithinAt_covRm_frame_le`);
* hence, writing `c q := covRm (G t) x (e t q)`, `dl q` for the derivative and `lp q` for
  `lapCovRmAt (G t) x (e t q)`,

  `φ'(t) = ∑ q, 2 * c q * dl q ≤ ∑ q, (2 * (c q * lp q) + 2 * |c q| * B)`
  `      = 2 * (∑ q, c q * lp q) + 2 * B * (∑ q, |c q|)` with `B = C (1+K) r √a`;

* `2 * ∑ q, c q * lp q ≤ laplAt (G t) (dRmNormSq (G t)) x`, because the Kato identity
  `laplAt_dRmNormSq_eq` writes the Laplacian as `2 * (sum of squares) + 2 * (that sum)`
  (`lapCovRmAt` unfolds to the second factor, and `e t = onFrame (G t) x` makes the two sums
  match), and the sum of squares is non-negative;
* `∑ q, |c q| ≤ √(n⁵) √(∑ q, (c q)²) = √(n⁵) √a` by Cauchy–Schwarz (`algebra_bounds`/`sq_sum_le_card_mul_sum_sq`);
* so `φ'(t) ≤ laplAt (G t) (dRmNormSq (G t)) x + (2 C (1+K) √(n⁵)) r a`, which is the contract with
  the universal constant `c := 2 C (1+K) √(n⁵)`.

Two `T = 0` remarks: the pieces above are stated with the derivative within `Set.Ico 0 T`, which is
what the contract asks for; the one-sided derivative at `t = 0` is obtained from the interior
derivative plus continuity of `s ↦ dRmNormSq (G s) x` on `[0,T)` (mean value theorem), which is
available from the joint smoothness of the flow. -/



/-! ## The normalised frame family, from the proved Gram--Schmidt family

`Work.Diff.GE.exists_ON_frame_family_uniformBound` already contains the construction of the
Gram--Schmidt family `frameFamily G t x` of `onFrame (G t) x` for the moving metric `G s`, with a
*universal* velocity bound `4 (finrank ℝ E)³`, and `Work.Diff.GE.frameFamily_at_t` says that this
family equals `onFrame (G t) x` at `s = t`.  What the assembly of EV2 needs is the *packaged*
statement including that last conjunct: this is it.  (Consequently the analytic EV2 assembly does
not depend on the separate obligation `Work.Diff.GE.exists_ON_frame_family_onFrame`.) -/
theorem ev2_frame_family_onFrame
    [I.Boundaryless] [T2Space M] [CompactSpace M] (hLC : LCSmooth I M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∃ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
          (edot : Fin (Module.finrank ℝ E) → TangentSpace I x),
          (∀ i, e t i = onFrame (G t) x i) ∧
          (∀ᶠ s in 𝓝[Set.Ico 0 T] t, IsONFrame (G s) x (e s)) ∧
          (∀ i, HasDerivWithinAt (fun s ↦ e s i) (edot i) (Set.Ico 0 T) t) ∧
          (∀ i, (G t).inner x (edot i) (edot i) ≤ K * rmNormSq (G t) x) := by
  classical
  refine ⟨4 * (Module.finrank ℝ E : ℝ) ^ 3, by positivity, ?_⟩
  intro G T hflow t ht x
  by_cases hnt : 0 < Module.finrank ℝ E
  · refine ⟨frameFamily G t x, frameEdot G t x, ?_, ?_, ?_, ?_⟩
    · intro i; exact congrFun (frameFamily_at_t G t x) i
    · exact Filter.Eventually.of_forall fun s => uniformBound_isONFrame_frameFamily G t s x
    · exact uniformBound_hasDerivWithinAt_frameFamily (G := G) (T := T) hflow ht x hnt
    · intro i; exact uniformBound_frameEdot_inner_le hLC G t x i
  · have h0 : Module.finrank ℝ E = 0 := Nat.eq_zero_of_not_pos hnt
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    refine ⟨fun _ _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
    · intro i; exact isEmptyElim i
    · exact Filter.Eventually.of_forall fun s => by intro i; exact isEmptyElim i
    · intro i; exact isEmptyElim i
    · intro i; exact isEmptyElim i

/-! ## The assembly, with the four classical ingredients as explicit hypotheses

`evol_drm_normsq_core` is the *proof* of EV2 from four pieces, all of them proved in the
workspace (only the first is still an obligation of the `∇Rm`-evolution area):

* `hEvol`  — the two-sided componentwise evolution estimate of `∇Rm` in a moving orthonormal
  frame (`Work.Diff.GE.covRm_frame_evol_abs`, from the shared `CurvVariation`/`CurvEvolution`
  contracts; the one-sided form of the same statement is
  `Work.Diff.GE.hasDerivWithinAt_covRm_frame_le`, and the two-sided form follows from it by
  `Work.Diff.GE.covRm_frame_evol_abs_via_le`);
* `hFamily` — existence of the moving orthonormal frame starting at `onFrame (G t) x`,
  proved here as `Work.Diff.GE.ev2_frame_family_onFrame` from the Gram--Schmidt family of
  `Work.Diff.GE.exists_ON_frame_family_uniformBound`/`Work.Diff.GE.frameFamily_at_t`;
* `hKato`  — the Kato/Weitzenböck identity for `Δ|∇Rm|²` (`Work.Diff.GE.laplAt_dRmNormSq_eq`);
* `hFrame` — frame independence of `|∇Rm|²` (`Work.Diff.GE.dRmNormSq_eq_sum_of_isONFrame`).

Keeping them as hypotheses means the assembly is developed and typechecked independently of the
(much harder) first one. -/

/-- The five components of `∇Rm` in a frame, indexed by the product type `ev2_Idx5`. -/
noncomputable def ev2_covRmIdx (g : SMet I M) (x : M) {n : ℕ} (e : Fin n → TangentSpace I x)
    (q : ev2_Idx5 n) : ℝ :=
  covRm g x (e q.1) (e q.2.1) (e q.2.2.1) (e q.2.2.2.1) (e q.2.2.2.2)

/-- The five components of the rough Laplacian `Δ∇Rm` in a frame, indexed by `ev2_Idx5`. -/
noncomputable def ev2_lapCovRmIdx (g : SMet I M) (x : M) {n : ℕ} (e : Fin n → TangentSpace I x)
    (q : ev2_Idx5 n) : ℝ :=
  lapCovRmAt g x (e q.1) (e q.2.1) (e q.2.2.1) (e q.2.2.2.1) (e q.2.2.2.2)

set_option maxHeartbeats 4000000 in
theorem evol_drm_normsq_core
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hEvol : ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      ∀ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
        (edot : Fin (Module.finrank ℝ E) → TangentSpace I x) (K' : ℝ), 0 ≤ K' →
        (∀ᶠ s in 𝓝[Set.Ico 0 T] t, IsONFrame (G s) x (e s)) →
        (∀ i, HasDerivWithinAt (fun s ↦ e s i) (edot i) (Set.Ico 0 T) t) →
        (∀ i, (G t).inner x (edot i) (edot i) ≤ K' * rmNormSq (G t) x) →
        ∀ m i j k l : Fin (Module.finrank ℝ E), ∃ D : ℝ,
          HasDerivWithinAt
            (fun s ↦ covRm (G s) x (e s m) (e s i) (e s j) (e s k) (e s l)) D (Set.Ico 0 T) t ∧
          |D - lapCovRmAt (G t) x (e t m) (e t i) (e t j) (e t k) (e t l)|
            ≤ C * (1 + K') * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x))
    (K : ℝ) (hK0 : 0 ≤ K)
    (hFamily : ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∃ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
          (edot : Fin (Module.finrank ℝ E) → TangentSpace I x),
          (∀ i, e t i = onFrame (G t) x i) ∧
          (∀ᶠ s in 𝓝[Set.Ico 0 T] t, IsONFrame (G s) x (e s)) ∧
          (∀ i, HasDerivWithinAt (fun s ↦ e s i) (edot i) (Set.Ico 0 T) t) ∧
          (∀ i, (G t).inner x (edot i) (edot i) ≤ K * rmNormSq (G t) x))
    (hKato : ∀ (g : SMet I M) (x : M),
      laplAt g (dRmNormSq g) x
        = 2 * (∑ m, ∑ v, ∑ a, ∑ b, ∑ c, ∑ d,
                (cov2Rm g x (onFrame g x m) (onFrame g x v) (onFrame g x a) (onFrame g x b)
                  (onFrame g x c) (onFrame g x d)) ^ 2)
          + 2 * (∑ v, ∑ a, ∑ b, ∑ c, ∑ d,
                covRm g x (onFrame g x v) (onFrame g x a) (onFrame g x b) (onFrame g x c)
                  (onFrame g x d)
                * (∑ m, cov3Rm g x (onFrame g x m) (onFrame g x m) (onFrame g x v)
                    (onFrame g x a) (onFrame g x b) (onFrame g x c) (onFrame g x d))))
    (hFrame : ∀ (g : SMet I M) (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x),
      IsONFrame g x e →
      dRmNormSq g x
        = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, (covRm g x (e m) (e i) (e j) (e k) (e l)) ^ 2) :
    EvolDRmNormSq I M := by
  classical
  obtain ⟨C, hC0, hEvolC⟩ := hEvol
  refine ⟨2 * C * (1 + K) * Real.sqrt ((Fintype.card (ev2_Idx5 (Module.finrank ℝ E)) : ℝ)), ?_, ?_⟩
  · positivity
  · intro G T hflow t ht x
    obtain ⟨e, edot, het, hON, hder, hvel⟩ := hFamily G T hflow t ht x
    have he_t : IsONFrame (G t) x (e t) := hON.self_of_nhdsWithin ht
    have ev2_hidx : ∀ F : ev2_Idx5 (Module.finrank ℝ E) → ℝ,
        (∑ q : ev2_Idx5 (Module.finrank ℝ E), F q) = ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, F (m, i, j, k, l) := by
      intro F; simp only [ev2_Idx5, Fintype.sum_prod_type]
    -- the per-component evolution estimate
    have hcomp : ∀ q : ev2_Idx5 (Module.finrank ℝ E), ∃ D : ℝ,
        HasDerivWithinAt (fun s ↦ ev2_covRmIdx (G s) x (e s) q) D (Set.Ico 0 T) t ∧
        |D - ev2_lapCovRmIdx (G t) x (e t) q|
          ≤ C * (1 + K) * Real.sqrt (rmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x) := by
      intro q
      exact hEvolC G T hflow t ht x e edot K hK0 hON hder hvel
        q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
    choose D hD hDb using hcomp
    -- the derivative of the sum of squares
    have hsum : HasDerivWithinAt
        (fun s ↦ ∑ q : ev2_Idx5 (Module.finrank ℝ E), (ev2_covRmIdx (G s) x (e s) q) ^ 2)
        (∑ q, 2 * ev2_covRmIdx (G t) x (e t) q * D q) (Set.Ico 0 T) t :=
      ev2_hasDerivWithinAt_sum_sq (f := fun q _ ↦ ev2_covRmIdx (G _) x (e _) q) (f' := D)
        (fun q ↦ hD q)
    -- frame independence transfers it to `dRmNormSq`
    have hEq : (fun s ↦ dRmNormSq (G s) x)
        =ᶠ[𝓝[Set.Ico 0 T] t]
          (fun s ↦ ∑ q : ev2_Idx5 (Module.finrank ℝ E), (ev2_covRmIdx (G s) x (e s) q) ^ 2) := by
      filter_upwards [hON] with s hs
      rw [hFrame (G s) x (e s) hs]
      exact (ev2_hidx (fun q ↦ (ev2_covRmIdx (G s) x (e s) q) ^ 2)).symm
    have hmain : HasDerivWithinAt (fun s ↦ dRmNormSq (G s) x)
        (∑ q, 2 * ev2_covRmIdx (G t) x (e t) q * D q) (Set.Ico 0 T) t :=
      hsum.congr_of_eventuallyEq hEq (by
        rw [hFrame (G t) x (e t) he_t]
        exact (ev2_hidx (fun q ↦ (ev2_covRmIdx (G t) x (e t) q) ^ 2)).symm)
    -- the sum of the squares of the components is `dRmNormSq`
    have hSqsum : (∑ q : ev2_Idx5 (Module.finrank ℝ E), (ev2_covRmIdx (G t) x (e t) q) ^ 2)
        = dRmNormSq (G t) x := by
      rw [ev2_hidx (fun q ↦ (ev2_covRmIdx (G t) x (e t) q) ^ 2)]
      exact (hFrame (G t) x (e t) he_t).symm
    -- the Kato identity identifies the `Δ∇Rm` pairing
    have hS1 : (∑ v, ∑ a, ∑ b, ∑ c, ∑ d,
          covRm (G t) x (onFrame (G t) x v) (onFrame (G t) x a) (onFrame (G t) x b)
            (onFrame (G t) x c) (onFrame (G t) x d)
          * (∑ m, cov3Rm (G t) x (onFrame (G t) x m) (onFrame (G t) x m) (onFrame (G t) x v)
              (onFrame (G t) x a) (onFrame (G t) x b) (onFrame (G t) x c) (onFrame (G t) x d)))
        = ∑ q, ev2_covRmIdx (G t) x (e t) q * ev2_lapCovRmIdx (G t) x (e t) q := by
      rw [ev2_hidx (fun q ↦ ev2_covRmIdx (G t) x (e t) q * ev2_lapCovRmIdx (G t) x (e t) q)]
      simp only [het, ev2_covRmIdx, ev2_lapCovRmIdx, lapCovRmAt]
    have hsq2 : 0 ≤ (∑ m, ∑ v, ∑ a, ∑ b, ∑ c, ∑ d,
        (cov2Rm (G t) x (onFrame (G t) x m) (onFrame (G t) x v) (onFrame (G t) x a)
          (onFrame (G t) x b) (onFrame (G t) x c) (onFrame (G t) x d)) ^ 2) :=
      Finset.sum_nonneg fun m _ ↦ Finset.sum_nonneg fun v _ ↦ Finset.sum_nonneg fun a _ ↦
        Finset.sum_nonneg fun b _ ↦ Finset.sum_nonneg fun c _ ↦ Finset.sum_nonneg fun d _ ↦
          sq_nonneg _
    -- Step 1: split by the sign of the component (two-sided hypothesis used here)
    have hstep1 : (∑ q, 2 * ev2_covRmIdx (G t) x (e t) q * D q)
        ≤ (∑ q, 2 * (ev2_covRmIdx (G t) x (e t) q * ev2_lapCovRmIdx (G t) x (e t) q))
          + 2 * (C * (1 + K) * Real.sqrt (rmNormSq (G t) x)
              * Real.sqrt (dRmNormSq (G t) x)) * ∑ q, |ev2_covRmIdx (G t) x (e t) q| :=
      ev2_sum_two_mul_le_of_abs_sub_le (fun q ↦ ev2_covRmIdx (G t) x (e t) q) D
        (fun q ↦ ev2_lapCovRmIdx (G t) x (e t) q) hDb
    -- Step 2: the Laplacian term, via Kato
    have hstep2 : (∑ q, 2 * (ev2_covRmIdx (G t) x (e t) q * ev2_lapCovRmIdx (G t) x (e t) q))
        ≤ laplAt (G t) (dRmNormSq (G t)) x := by
      rw [← Finset.mul_sum]
      rw [hKato (G t) x, hS1]
      linarith
    -- Step 3: Cauchy–Schwarz on the reaction term
    have hstep3 : (∑ q, |ev2_covRmIdx (G t) x (e t) q|)
        ≤ Real.sqrt ((Fintype.card (ev2_Idx5 (Module.finrank ℝ E)) : ℝ))
          * Real.sqrt (dRmNormSq (G t) x) := by
      have h := ev2_sum_abs_le_sqrt_card_mul_sqrt_sum_sq (fun q ↦ ev2_covRmIdx (G t) x (e t) q)
      rwa [hSqsum] at h
    refine ⟨∑ q, 2 * ev2_covRmIdx (G t) x (e t) q * D q, hmain, ?_⟩
    have hB0 : 0 ≤ 2 * (C * (1 + K) * Real.sqrt (rmNormSq (G t) x)
        * Real.sqrt (dRmNormSq (G t) x)) := by positivity
    calc ∑ q, 2 * ev2_covRmIdx (G t) x (e t) q * D q
        ≤ (∑ q, 2 * (ev2_covRmIdx (G t) x (e t) q * ev2_lapCovRmIdx (G t) x (e t) q))
            + 2 * (C * (1 + K) * Real.sqrt (rmNormSq (G t) x)
                * Real.sqrt (dRmNormSq (G t) x)) * ∑ q, |ev2_covRmIdx (G t) x (e t) q| :=
          hstep1
      _ ≤ laplAt (G t) (dRmNormSq (G t)) x
            + 2 * (C * (1 + K) * Real.sqrt (rmNormSq (G t) x)
                * Real.sqrt (dRmNormSq (G t) x))
              * (Real.sqrt ((Fintype.card (ev2_Idx5 (Module.finrank ℝ E)) : ℝ))
                  * Real.sqrt (dRmNormSq (G t) x)) :=
          add_le_add hstep2 (mul_le_mul_of_nonneg_left hstep3 hB0)
      _ = laplAt (G t) (dRmNormSq (G t)) x
            + 2 * C * (1 + K) * Real.sqrt ((Fintype.card (ev2_Idx5 (Module.finrank ℝ E)) : ℝ))
              * Real.sqrt (rmNormSq (G t) x)
              * (Real.sqrt (dRmNormSq (G t) x) * Real.sqrt (dRmNormSq (G t) x)) := by ring
      _ = laplAt (G t) (dRmNormSq (G t)) x
            + 2 * C * (1 + K) * Real.sqrt ((Fintype.card (ev2_Idx5 (Module.finrank ℝ E)) : ℝ))
              * Real.sqrt (rmNormSq (G t) x) * dRmNormSq (G t) x := by
          rw [Real.mul_self_sqrt
            (ev2_dRmNormSq_nonneg (I := I) (M := M) (g := G t) (x := x))]

set_option maxHeartbeats 4000000 in
/-- **EV2**: the evolution of `|∇Rm|²` under the Ricci flow, with a universal constant. -/
theorem evol_drm_normsq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : LCSmooth I M) (hLV : LCVariation I M) :
    EvolDRmNormSq I M := by
  obtain ⟨K, hK0, hFamily⟩ := ev2_frame_family_onFrame (I := I) (M := M) hLC
  exact evol_drm_normsq_core (I := I) (M := M)
    (covRm_frame_evol_abs (I := I) (M := M) hLC hLV) K hK0 hFamily
    (fun g x ↦ laplAt_dRmNormSq_eq (I := I) (M := M) hLC x)
    (fun g x e he ↦ dRmNormSq_eq_sum_of_isONFrame (I := I) (M := M) hLC x e he)

end Work.Diff.GE

