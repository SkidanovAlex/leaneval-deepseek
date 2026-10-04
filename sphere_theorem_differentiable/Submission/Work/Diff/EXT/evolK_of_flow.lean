import Mathlib
import Submission.Work.Diff.EXT.evolKDefs
import Submission.Work.Diff.EXT.curvNormK_frame_indep
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.EXT.laplAt_curvNormK_eq
import Submission.Work.Diff.EXT.evolX.substC.ReactAll
import Submission.Work.Diff.EXT.evolX.substC.EvolCompKAll
import Submission.Work.Diff.EXT.evolCompKFix_all
import Submission.Work.Diff.EXT.frame_family_along_flow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `EvolK`: the `k`-th order Shi estimate, assembled

`Work.Diff.EXT.EvolK` is Hamilton's evolution inequality for `|∇^k Rm|²` along a Ricci flow: for
every `k ≥ 1` there is a universal constant `c ≥ 0` such that, whenever `|∇^i Rm|² ≤ A i` on
`[σ,T)` for `i < k`, the right derivative `D` of `s ↦ |∇^k Rm|²(G s)(x)` at `t ∈ [σ,T)` satisfies

`D ≤ Δ|∇^k Rm|²(G t)(x) + c (1 + Σ_{i<k} A i) (|∇^k Rm|²(G t)(x) + 1)`.

This file proves `EvolK` from the four ingredients below (`evolK_of_pieces`), the `k`-generalizations
of the four hypotheses of the verified `k = 1` assembly `Work.Diff.GE.evol_drm_normsq_core`:

* `EvolCompK k` (`evolKDefs.lean`): the componentwise evolution of `∇^k Rm` in a moving orthonormal
  frame, with reaction bound `C (1+K') (1 + Σ_{j<k}f_j) (1 + √f_k)`;
* `laplAt_curvNormK_eq` (delegated): the Kato/Weitzenböck identity `Δ|T|² = 2|∇T|² + 2⟨T,ΔT⟩`
  for `T = ∇^k Rm`, which turns the *rough* Laplacian of the components into the *scalar*
  Laplacian of the norm;
* the frame family (GE area): an orthonormal frame family along the flow starting at the
  `Classical.epsilon`-chosen `onFrame`, with velocity bound `⟨ėᵢ,ėᵢ⟩ ≤ K |Rm|²` for a global `K`;
* the frame independence of `curvNormK` (this area).

The `k = 1` instance of `EvolCompK` is exactly the analytic core of `EvolDRmNormSq` (EV2).

## The remaining gap (for the next worker)

`evolK_of_flow` is `evolK_of_pieces` applied to the four ingredients of the statement above.  The
frame family `Work.Diff.GE.exists_ON_frame_family_onFrame` (GE area), the Kato identity
`Work.Diff.EXT.laplAt_curvNormK_eq` and the frame independence `Work.Diff.EXT.curvNormK_frame_indep`
have their own owners; the fourth ingredient, `∀ k ≥ 1, EvolCompK k`, is delegated as
`Submission.Work.Diff.EXT.evolCompK_all`.  An equivalent route is available through the
*fixed-vector* form: `Work.Diff.EXT.evolCompKFix_all` (fixed vectors, no frame) together with the
proved reduction `Work.Diff.EXT.evolCompK_of_fix`, chained in
`Submission/Work/Diff/EXT/evolCompK_all_via_fix.lean`; the statement `∀ k ≥ 1, EvolCompK k` below
can be supplied from either route.  Its `k = 1` case is `Work.Diff.EXT.evolCompK_one`
(delegated; deduced from the GE-area `Work.Diff.GE.covRm_frame_evol_abs` through the bridges of
`Submission/Work/Diff/EXT/evolK_bridges.lean` and
`Work.Diff.EXT.lapCovKRm_one_eq_lapCovRmAt`), so only the induction step `k → k+1` is new.

That step differentiates, in `s`, the defining recursion of `covKRmExt` at level `k + 1`:

`∂ₛ (∇^{k+1} Rm) = ∂ₛ (extD (∇^k Rm)) = extD(∂ₛ ∇^k Rm) + (∂ₛ∇)-terms`,

using Clairaut for `mvfderiv` (`Work.Diff.GE.hasDerivAt_mvfderiv`), the variation of the connection
(`LCVariation`) and the Ext-pattern Ricci identity.  CAUTION: the step is *not* derivable from
`EvolCompK k` alone: differentiating the level-`k` evolution in *space* requires the *explicit*
reaction `R_k = ∂ₜ∇^kRm − Δ∇^kRm = Σ_{i+j=k} ∇^iRm ∗ ∇^jRm + (curvature/connection terms)`, whose
term `(∇Rm) ∗ (∇Rm)` (present from `k = 2` on) is quadratic in a strictly lower order and does not
vanish where `∇^k Rm = 0`.  The induction therefore has to run on "identity with an explicit
reaction + its bounds" — equivalently, define `R_k` by the recursion
`R_{k+1} = ∇R_k + [Ricci commutator] + (∂ₜ∇)-terms`; that is the content of
`Work.Diff.EXT.evolCompK_all`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Vocabulary and elementary lemmas -/

/-- The index type of the components of `∇^k Rm` in a frame. -/
abbrev KrIdx (k : ℕ) : Type _ :=
  (Fin k → Fin (Module.finrank ℝ E)) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
    Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)

/-- The `q`-th component of `∇^k Rm` in the frame `e`. -/
noncomputable def krComp (g : SMet I M) (x : M) (k : ℕ)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (q : KrIdx (E := E) k) : ℝ :=
  covKRm g x k (fun r => e (q.1 r)) (e q.2.1) (e q.2.2.1) (e q.2.2.2.1) (e q.2.2.2.2)

/-- The `q`-th component of the rough Laplacian `Δ∇^k Rm`, traced in `onFrame g x`. -/
noncomputable def krLapComp (g : SMet I M) (x : M) (k : ℕ) (q : KrIdx (E := E) k) : ℝ :=
  lapCovKRm g x k (fun r => onFrame g x (q.1 r)) (onFrame g x q.2.1) (onFrame g x q.2.2.1)
    (onFrame g x q.2.2.2.1) (onFrame g x q.2.2.2.2)

/-- A finite sum over `KrIdx` is the iterated sum over the five index groups. -/
theorem sum_krIdx (k : ℕ) {ι : Type*} [AddCommMonoid ι] (F : KrIdx (E := E) k → ι) :
    ∑ q : KrIdx (E := E) k, F q
      = ∑ u : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m, F (u, i, j, l, m) := by
  rw [Fintype.sum_prod_type]
  congr 1 with u
  rw [Fintype.sum_prod_type]
  congr 1 with i
  rw [Fintype.sum_prod_type]
  congr 1 with j
  rw [Fintype.sum_prod_type]

/-- **Derivative of a finite sum of squares.** -/
theorem hasDerivWithinAt_sum_sq {ι : Type*} [Fintype ι] {f : ι → ℝ → ℝ} {f' : ι → ℝ}
    {s : Set ℝ} {t : ℝ} (h : ∀ i, HasDerivWithinAt (f i) (f' i) s t) :
    HasDerivWithinAt (fun x => ∑ i, (f i x) ^ 2) (∑ i, 2 * f i t * f' i) s t := by
  have h1 := HasDerivWithinAt.sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => (h i).mul (h i))
  convert h1 using 1
  · ext x
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [pow_two, Pi.mul_apply]
  · exact Finset.sum_congr rfl fun i _ => by ring

/-- **Cauchy–Schwarz in `ℓ¹`-form**: `∑ |g i| ≤ √(card ι) √(∑ (g i)²)`. -/
theorem sum_abs_le_sqrt_card_mul_sqrt_sum_sq {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    ∑ i, |g i| ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, (g i) ^ 2) := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => |g i|)
  have h0 : 0 ≤ ∑ i, |g i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have h2 : (∑ i, |g i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (g i) ^ 2 := by
    simpa only [Finset.card_univ, sq_abs] using h
  calc ∑ i, |g i| = Real.sqrt ((∑ i, |g i|) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, (g i) ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, (g i) ^ 2) :=
        Real.sqrt_mul (Nat.cast_nonneg _) _

/-- **Sign splitting**: if `|D q - lp q| ≤ B` then `∑ 2 c q D q ≤ ∑ 2 c q lp q + 2 B ∑ |c q|`.
(Two-sidedness is essential: for `c q < 0` an upper bound on `D q` gives no bound on `2 c q D q`.) -/
theorem sum_two_mul_le_of_abs_sub_le {ι : Type*} [Fintype ι] (c D lp : ι → ℝ) {B : ℝ}
    (h : ∀ q, |D q - lp q| ≤ B) :
    ∑ q, 2 * c q * D q ≤ (∑ q, 2 * (c q * lp q)) + 2 * B * ∑ q, |c q| := by
  have hq : ∀ q, 2 * c q * D q ≤ 2 * (c q * lp q) + 2 * |c q| * B := by
    intro q
    have h1 : D q ≤ lp q + B := by have := (abs_le.mp (h q)).2; linarith
    have h2 : lp q - B ≤ D q := by have := (abs_le.mp (h q)).1; linarith
    rcases le_total (c q) 0 with hc | hc
    · have h3 : 2 * c q * D q ≤ 2 * c q * (lp q - B) := by
        exact mul_le_mul_of_nonpos_left h2 (by linarith)
      have h4 : 2 * c q * (lp q - B) = 2 * (c q * lp q) + 2 * |c q| * B := by
        rw [abs_of_nonpos hc]; ring
      linarith [h3, h4.le, h4.ge]
    · have h3 : 2 * c q * D q ≤ 2 * c q * (lp q + B) := by
        exact mul_le_mul_of_nonneg_left h1 (by linarith)
      have h4 : 2 * c q * (lp q + B) = 2 * (c q * lp q) + 2 * |c q| * B := by
        rw [abs_of_nonneg hc]; ring
      linarith [h3, h4.le, h4.ge]
  calc ∑ q, 2 * c q * D q
      ≤ ∑ q, (2 * (c q * lp q) + 2 * |c q| * B) := Finset.sum_le_sum (fun q _ => hq q)
    _ = (∑ q, 2 * (c q * lp q)) + 2 * B * ∑ q, |c q| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun q _ => by ring)

/-- The right derivative at a point outside the closure of the within-set is vacuous. -/
theorem hasDerivWithinAt_of_notMem_closure {f : ℝ → ℝ} {D t : ℝ} {s : Set ℝ}
    (h : t ∉ closure s) : HasDerivWithinAt f D s t := by
  have hbot : 𝓝[s] t = ⊥ := notMem_closure_iff_nhdsWithin_eq_bot.mp h
  rw [hasDerivWithinAt_iff_tendsto, hbot]
  exact tendsto_bot

/-! ## The assembly -/

set_option maxHeartbeats 8000000 in
/-- **The `k`-th order Shi estimate** from its four ingredients (see the module docstring). -/
theorem evolK_of_pieces
    (hComp : ∀ k : ℕ, 1 ≤ k → EvolCompK (I := I) (M := M) k)
    (hKato : ∀ (g : SMet I M) (x : M) (k : ℕ), 1 ≤ k →
      laplAt g (fun y => curvNormK g y k) x =
        2 * curvNormK g x (k + 1) +
        2 * (∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
              covKRm g x k (fun r => onFrame g x (ι r)) (onFrame g x i) (onFrame g x j)
                (onFrame g x l) (onFrame g x m) *
              lapCovKRm g x k (fun r => onFrame g x (ι r)) (onFrame g x i) (onFrame g x j)
                (onFrame g x l) (onFrame g x m)))
    (hFamily : ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M,
        ∃ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
          (edot : Fin (Module.finrank ℝ E) → TangentSpace I x),
          (∀ i, e t i = onFrame (G t) x i) ∧
          (∀ᶠ s in 𝓝[Set.Ico 0 T] t, IsONFrame (G s) x (e s)) ∧
          (∀ i, HasDerivWithinAt (fun s => e s i) (edot i) (Set.Ico 0 T) t) ∧
          (∀ i, (G t).inner x (edot i) (edot i) ≤ K * rmNormSq (G t) x))
    (hFrame : ∀ (g : SMet I M) (x : M) (k : ℕ)
      (e : Fin (Module.finrank ℝ E) → TangentSpace I x), IsONFrame g x e →
      curvNormK g x k = ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (covKRm g x k (fun r => e (ι r)) (e i) (e j) (e l) (e m)) ^ 2) :
    EvolK (I := I) (M := M) := by
  classical
  intro k hk
  obtain ⟨C, hC0, hC⟩ := hComp k hk
  obtain ⟨K, hK0, hFam⟩ := hFamily
  refine ⟨6 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K),
    by positivity, ?_⟩
  intro A hA G σ T hflow hσT hlow t ht x
  have hAnn : ∀ i, i < k → 0 ≤ A i := fun i hi => hA i (le_of_lt hi)
  set S : ℝ := ∑ j ∈ Finset.range k, A j with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun j _ => hAnn j (Finset.mem_range.mp ‹_›))
  have hleS : ∀ j, j < k → curvNormK (G t) x j ≤ S := by
    intro j hj
    rw [hSdef]
    refine le_trans (hlow j hj t ht x) (Finset.single_le_sum (f := A) (s := Finset.range k) ?_ ?_)
    · intro i hi
      exact hAnn i (Finset.mem_range.mp hi)
    · exact Finset.mem_range.mpr hj
  by_cases ht0 : 0 ≤ t
  · -- the substantive case
    have htI : t ∈ Set.Ico 0 T := ⟨ht0, ht.2⟩
    obtain ⟨e, edot, het, hON, hder, hvel⟩ := hFam G T hflow t htI x
    have he_t : IsONFrame (G t) x (e t) := hON.self_of_nhdsWithin htI
    -- the componentwise evolution estimates
    have hcomp : ∀ q : KrIdx (E := E) k, ∃ D : ℝ,
        HasDerivWithinAt (fun s => krComp (G s) x k (e s) q) D (Set.Ico 0 T) t ∧
        |D - krLapComp (G t) x k q| ≤ C * (1 + K) *
          (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) *
          (1 + Real.sqrt (curvNormK (G t) x k)) := by
      intro q
      have hq := hC G T hflow t htI x e edot K hK0 het hvel hON hder
        q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2
      simpa only [krComp, krLapComp] using hq
    choose D hD hDb using hcomp
    -- the derivative of the sum of squares of the components
    have hsum : HasDerivWithinAt
        (fun s => ∑ q : KrIdx (E := E) k, (krComp (G s) x k (e s) q) ^ 2)
        (∑ q, 2 * krComp (G t) x k (e t) q * D q) (Set.Ico 0 T) t :=
      hasDerivWithinAt_sum_sq (f := fun q _ => krComp (G _) x k (e _) q) (f' := D)
        (fun q => hD q)
    -- frame independence identifies that sum with `curvNormK`
    have hEq : (fun s => curvNormK (G s) x k)
        =ᶠ[𝓝[Set.Ico 0 T] t]
          (fun s => ∑ q : KrIdx (E := E) k, (krComp (G s) x k (e s) q) ^ 2) := by
      filter_upwards [hON] with s hs
      rw [hFrame (G s) x k (e s) hs, sum_krIdx k]
      simp only [krComp]
    have hmain : HasDerivWithinAt (fun s => curvNormK (G s) x k)
        (∑ q, 2 * krComp (G t) x k (e t) q * D q) (Set.Ico 0 T) t :=
      hsum.congr_of_eventuallyEq hEq (by
        rw [hFrame (G t) x k (e t) he_t, sum_krIdx k]
        simp only [krComp])
    have hSqsum : (∑ q : KrIdx (E := E) k, (krComp (G t) x k (e t) q) ^ 2)
        = curvNormK (G t) x k := by
      rw [hFrame (G t) x k (e t) he_t, sum_krIdx k]
      simp only [krComp]
    -- the Kato identity identifies the rough-Laplacian pairing with the scalar Laplacian
    have hS1 : (∑ q : KrIdx (E := E) k, krComp (G t) x k (e t) q * krLapComp (G t) x k q)
        = ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
            covKRm (G t) x k (fun r => onFrame (G t) x (ι r)) (onFrame (G t) x i)
              (onFrame (G t) x j) (onFrame (G t) x l) (onFrame (G t) x m) *
            lapCovKRm (G t) x k (fun r => onFrame (G t) x (ι r)) (onFrame (G t) x i)
              (onFrame (G t) x j) (onFrame (G t) x l) (onFrame (G t) x m) := by
      rw [sum_krIdx k]
      refine Finset.sum_congr rfl fun ι _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun m _ => ?_
      simp only [krComp, krLapComp, het]
    -- the four estimates
    have hstep1 : (∑ q, 2 * krComp (G t) x k (e t) q * D q)
        ≤ (∑ q, 2 * (krComp (G t) x k (e t) q * krLapComp (G t) x k q))
          + 2 * (C * (1 + K) *
                (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) *
              (1 + Real.sqrt (curvNormK (G t) x k))) *
            ∑ q, |krComp (G t) x k (e t) q| :=
      sum_two_mul_le_of_abs_sub_le _ D _ (fun q => hDb q)
    have hstep2 : (∑ q, 2 * (krComp (G t) x k (e t) q * krLapComp (G t) x k q))
        ≤ laplAt (G t) (fun x => curvNormK (G t) x k) x := by
      rw [← Finset.mul_sum, hS1, hKato (G t) x k hk]
      linarith [curvNormK_nonneg (G t) x (k + 1)]
    have hstep3 : (∑ q, |krComp (G t) x k (e t) q|)
        ≤ Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) *
            Real.sqrt (curvNormK (G t) x k) := by
      have h := sum_abs_le_sqrt_card_mul_sqrt_sum_sq
        (fun q : KrIdx (E := E) k => krComp (G t) x k (e t) q)
      rwa [hSqsum] at h
    -- arithmetic
    have hf0 : 0 ≤ curvNormK (G t) x k := curvNormK_nonneg _ _ _
    have hsum_low : (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) ≤ 1 + S := by
      rw [hSdef]
      gcongr with j hj
      exact hlow j (Finset.mem_range.mp hj) t ht x
    have hsq_le : (1 + Real.sqrt (curvNormK (G t) x k)) * Real.sqrt (curvNormK (G t) x k)
        ≤ 3 * (1 + curvNormK (G t) x k) := by
      have h1 : Real.sqrt (curvNormK (G t) x k) ≤ 1 + curvNormK (G t) x k := by
        nlinarith [Real.sq_sqrt hf0, Real.sqrt_nonneg (curvNormK (G t) x k)]
      nlinarith [Real.sq_sqrt hf0, Real.sqrt_nonneg (curvNormK (G t) x k), h1]
    have hSum0 : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j := by
      have h := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range k) => curvNormK_nonneg (G t) x j)
      linarith
    have hK1 : (0 : ℝ) ≤ 1 + K := by linarith
    have hbase : (0 : ℝ) ≤ C * (1 + K) *
        (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) *
        (1 + Real.sqrt (curvNormK (G t) x k)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 hK1) hSum0)
        (by linarith [Real.sqrt_nonneg (curvNormK (G t) x k)])
    have hb2 : 2 * (C * (1 + K) *
          (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) *
          (1 + Real.sqrt (curvNormK (G t) x k))) * (∑ q, |krComp (G t) x k (e t) q|)
        ≤ 6 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K)
            * (1 + S) * (1 + curvNormK (G t) x k) := by
      have hB2 : (0 : ℝ) ≤ C * (1 + K) *
          (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) *
          (1 + Real.sqrt (curvNormK (G t) x k)) := hbase
      have hA1 : (0 : ℝ) ≤ 2 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C *
          (1 + K) := by positivity
      have hA2 : (0 : ℝ) ≤ 2 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C *
          (1 + K) * (3 * (1 + curvNormK (G t) x k)) := by positivity
      have hB3 : (0 : ℝ) ≤ 3 * (1 + curvNormK (G t) x k) := by positivity
      calc 2 * (C * (1 + K) *
            (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) *
            (1 + Real.sqrt (curvNormK (G t) x k))) * (∑ q, |krComp (G t) x k (e t) q|)
          ≤ 2 * (C * (1 + K) *
              (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) *
              (1 + Real.sqrt (curvNormK (G t) x k))) *
              (Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) *
                Real.sqrt (curvNormK (G t) x k)) :=
            mul_le_mul_of_nonneg_left hstep3 (by linarith [hB2])
        _ = 2 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K) *
              (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) *
              ((1 + Real.sqrt (curvNormK (G t) x k)) * Real.sqrt (curvNormK (G t) x k)) := by
            ring
        _ ≤ 2 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K) *
              (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) *
              (3 * (1 + curvNormK (G t) x k)) :=
            mul_le_mul_of_nonneg_left hsq_le (by
              have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range k) =>
                curvNormK_nonneg (G t) x j)
              positivity)
        _ ≤ 2 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K) *
              (1 + S) * (3 * (1 + curvNormK (G t) x k)) := by
            calc 2 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K) *
                  (1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) *
                  (3 * (1 + curvNormK (G t) x k))
                = (2 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K)) *
                    ((1 + ∑ j ∈ Finset.range k, curvNormK (G t) x j) *
                      (3 * (1 + curvNormK (G t) x k))) := by ring
              _ ≤ (2 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K)) *
                    ((1 + S) * (3 * (1 + curvNormK (G t) x k))) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_right hsum_low hB3) hA1
              _ = 2 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K) *
                    (1 + S) * (3 * (1 + curvNormK (G t) x k)) := by ring
        _ = 6 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K)
              * (1 + S) * (1 + curvNormK (G t) x k) := by
            ring
    refine ⟨∑ q, 2 * krComp (G t) x k (e t) q * D q, hmain, ?_⟩
    have hgoal : laplAt (G t) (fun x => curvNormK (G t) x k) x
          + 6 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K)
            * (1 + S) * (1 + curvNormK (G t) x k)
        = laplAt (G t) (fun x => curvNormK (G t) x k) x
          + 6 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K)
            * (1 + ∑ i ∈ Finset.range k, A i) * curvNormK (G t) x k
          + 6 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K)
            * (1 + ∑ i ∈ Finset.range k, A i) := by
      rw [hSdef]; ring
    rw [← hgoal]
    linarith [hstep1, hstep2, hb2]
  · -- `t < 0`: the within-set `Ico 0 T` stays away from `t`, so the derivative condition is vacuous
    push Not at ht0
    have hcl : t ∉ closure (Set.Ico (0 : ℝ) T) := by
      intro hmem
      have hmem2 : t ∈ closure (Set.Ici (0 : ℝ)) := closure_mono (fun y hy => hy.1) hmem
      rw [isClosed_Ici.closure_eq, Set.mem_Ici] at hmem2
      linarith
    refine ⟨laplAt (G t) (fun x => curvNormK (G t) x k) x
        + 6 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K)
            * (1 + S) * curvNormK (G t) x k
        + 6 * Real.sqrt (Fintype.card (KrIdx (E := E) k) : ℝ) * C * (1 + K)
            * (1 + S),
      hasDerivWithinAt_of_notMem_closure hcl, le_rfl⟩

/-- Frame independence of `curvNormK`, in the vocabulary of `covKRm` (the hypothesis `hFrame` of
`evolK_of_pieces`): the sum of the squares of the components of `∇^k Rm` in any orthonormal frame
is `curvNormK`.  Immediate from `curvNormK_frame_indep` and `covKRmC_eq_covKRm`. -/
theorem curvNormK_eq_sum_of_isONFrame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) {g : Submission.Diff.SMet I M} (x : M) (k : ℕ)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) :
    Work.Diff.EXT.curvNormK g x k =
      ∑ ι : Fin k → Fin (Module.finrank ℝ E), ∑ i, ∑ j, ∑ l, ∑ m,
        (Work.Diff.EXT.covKRm g x k (fun r => e (ι r)) (e i) (e j) (e l) (e m)) ^ 2 := by
  rw [Work.Diff.EXT.curvNormK_frame_indep (I := I) (M := M) hLC x k e he]
  simp only [Work.Diff.EXT.covKRmC_eq_covKRm]

/-- **The `k`-th order Shi estimate**: `EvolK` from the four ingredients.  The frame family
(`Work.Diff.EXT.frame_family_along_flow`, a copy of the GE-area statement kept in this area
because that file is currently broken/in-flux), the Kato identity
(`Work.Diff.EXT.laplAt_curvNormK_eq`) and the componentwise evolution
(`Work.Diff.EXT.evolCompK_all`) are the delegated/owned inputs; the frame independence is
`curvNormK_eq_sum_of_isONFrame` above, with `LCSmooth` supplied by `Work.Diff.T.lc_smooth`. -/
theorem evolK_of_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] :
    Work.Diff.EXT.EvolK (I := I) (M := M) :=
  evolK_of_pieces (I := I) (M := M)
    -- `∀ k ≥ 1, EvolCompK k`, through the fixed-vector form in its classical reaction shape:
    -- `EvolCompKFixReact k → EvolCompKFix k` (`evolCompKFix_of_reaction`, proved) and
    -- `EvolCompKFix k → EvolCompK k` (`evolCompK_of_fixed_estimate`, proved); the whole chain is
    -- packaged in `Work.Diff.EXT.evolCompK_all_of_react` (`substC.EvolCompKAll`, the clash-free
    -- copy of `evolCompK_all.lean`).  `evolCompKFixReact_allC` is the reaction ladder of the
    -- `substC` chain (`substC.Assembly` → `substC.ConnVarOpJets` → `substC.ConnVarSrcJets` →
    -- `substC.LadderStep` → `substC.ReactAll`), which avoids `evolX.lapOpEDefs` (its `SOp` clashes
    -- with `substB/Defs.lean`'s `SOp`).
    (evolCompK_all_of_reactC (I := I) (M := M)
      (evolCompKFixReact_allC (I := I) (M := M)))
    (laplAt_curvNormK_eq (I := I) (M := M))
    (frame_family_along_flow (I := I) (M := M))
    (fun _g x k e he => curvNormK_eq_sum_of_isONFrame (I := I) (M := M)
      (Work.Diff.T.lc_smooth (I := I) (M := M)) x k e he)

end Work.Diff.EXT
