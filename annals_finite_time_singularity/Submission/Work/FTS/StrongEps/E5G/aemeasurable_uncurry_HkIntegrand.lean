import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.EpsSlotAux
import Submission.Work.FTS.StrongEps.aemeasurable_mixed_family
import Submission.Work.FTS.EpsEngine.aesm_uncurry_restricted
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint measurability of `(s,z,θ) ↦ HkIntegrand α k (H s) z θ`

For a family `H : ℝ → ℝ → ℝ → ℝ` whose slices `H s` (`s ∈ [0,T]`) are `C^∞` on the open
quadrant and whose values `s ↦ H s z θ` are continuous on `[0,T]` at every point `(z,θ)` of the
quadrant, the map

  `(s, z, θ) ↦ HkIntegrand α k (H s) z θ`

is a.e. strongly measurable for `(volume.restrict (Icc 0 T)).prod ((volume.restrict Iz).prod
(volume.restrict Iθ))`.

The proof has three parts.

* **Slicewise measurability in `s`.**  `HkIntegrand α k (H s) z θ` is a finite sum of squares of
  the mixed slots `mixed j i (H s) z θ` (times weights that depend on `(z,θ)` only), and
  `Work.FTS.StrongEps.aemeasurable_mixed_family` gives the a.e. strong measurability of every
  slot at any point of the *open* quadrant.

* **Carathéodory step.**  The integrand is continuous in `(z,θ)` on the open quadrant and (in its
  truncated version) zero off it, so `Work.FTS.EpsEngine.aesm_uncurry_restricted` gives joint
  measurability of the truncated integrand for `(volume.restrict (Icc 0 T)).prod volume`.

* **Passing to the restricted measure.**  `Iz ×ˢ Iθ` (the support of the target measure) and the
  open quadrant `Qd` agree up to a null set for the planar Lebesgue measure, so
  `(volume.restrict Iz).prod (volume.restrict Iθ) = volume.restrict Qd`, and on that measure the
  truncated integrand agrees a.e. with the integrand itself.
-/

namespace Work.FTS.StrongEps.E5G

open scoped Real Topology
open MeasureTheory Set Filter

/-- The open quadrant `(0,∞) × (0,π/2)` of the elliptic estimates. -/
private def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

private lemma isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

private lemma measurableSet_Qd_compl : MeasurableSet Qdᶜ := isOpen_Qd.measurableSet.compl

/-- The product of the restrictions of the Lebesgue measure to `Iz = [0,∞)` and to
`Iθ = [0,π/2]` is the restriction of the planar Lebesgue measure to the open quadrant `Qd`:
the sets `Iz ×ˢ Iθ` and `Qd` differ only by the null lines `z = 0` and `θ = 0, π/2`. -/
private lemma prod_restrict_Iz_Iθ :
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = volume.restrict Qd := by
  simp only [Work.Spaces.Iz, Work.Spaces.Iθ, Qd]
  rw [MeasureTheory.Measure.prod_restrict]
  refine MeasureTheory.Measure.restrict_congr_set ?_
  exact MeasureTheory.Measure.set_prod_ae_eq MeasureTheory.Ioi_ae_eq_Ici.symm
    MeasureTheory.Ioo_ae_eq_Icc.symm

/-! ## Measurability in `s` of the integrand of a single slice -/

/-- A finite sum (evaluated pointwise) of a.e. strongly measurable real functions is a.e. strongly
measurable. -/
private lemma aesm_finsetSum_apply {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    {μ : Measure ℝ} (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun a : ℝ => ∑ i ∈ s, f i a) μ := by
  have h := Finset.aestronglyMeasurable_sum (M := ℝ) (f := f) s hf
  refine h.congr (Filter.Eventually.of_forall fun a => ?_)
  exact Finset.sum_apply a s f

/-- **Measurability in `s` of `HkIntegrand α k (H s) z θ`** at a point of the open quadrant. -/
private lemma aesm_HkIntegrand_family {α T : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ s ∈ Set.Icc (0:ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => H s z θ) (Set.Icc (0:ℝ) T))
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    AEStronglyMeasurable (fun s : ℝ => Work.Spaces.HkIntegrand α k (H s) z θ)
      (volume.restrict (Set.Icc (0:ℝ) T)) := by
  have hslot : ∀ j i : ℕ, AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
      (volume.restrict (Set.Icc (0:ℝ) T)) :=
    fun j i => Work.FTS.StrongEps.aemeasurable_mixed_family hsm hcont j i z θ hzθ
  unfold Work.Spaces.HkIntegrand
  have hA : AEStronglyMeasurable (fun s : ℝ => ∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (H s) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (volume.restrict (Set.Icc (0:ℝ) T)) :=
    aesm_finsetSum_apply (fun i _ => ((hslot i 0).mul_const
      (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))).pow 2)
  have hB : AEStronglyMeasurable (fun s : ℝ => ∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) (volume.restrict (Set.Icc (0:ℝ) T)) :=
    aesm_finsetSum_apply (fun i _ => aesm_finsetSum_apply (fun j _ => by
      by_cases hh : 1 ≤ i ∧ i + j ≤ k
      · have hthis : (fun s : ℝ => (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun s : ℝ => (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 :=
          funext fun s => ite_eq_left hh
        rw [hthis]
        exact (((hslot j i).mul_const (Work.Spaces.Wt α z θ)).pow 2)
      · have hthis : (fun s : ℝ => (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i (H s) z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun _ : ℝ => (0:ℝ) :=
          funext fun s => ite_eq_right hh
        rw [hthis]
        exact aestronglyMeasurable_const))
  exact hA.add hB

/-! ## The target -/

theorem aemeasurable_uncurry_HkIntegrand {α T : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ s ∈ Set.Icc (0:ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => H s z θ) (Set.Icc (0:ℝ) T)) :
    AEMeasurable
      (fun p : ℝ × (ℝ × ℝ) => Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2)
      ((volume.restrict (Set.Icc (0:ℝ) T)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) := by
  classical
  rw [prod_restrict_Iz_Iθ]
  -- the Carathéodory step, on the larger measure with an unrestricted `(z,θ)`-factor
  have hmain : AEStronglyMeasurable
      (fun p : ℝ × (ℝ × ℝ) =>
        if (p.2.1, p.2.2) ∈ Qd
          then Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2 else 0)
      ((volume.restrict (Set.Icc (0:ℝ) T)).prod (volume : Measure (ℝ × ℝ))) := by
    refine Work.FTS.EpsEngine.aesm_uncurry_restricted (A := Set.Icc (0:ℝ) T)
      (g := fun s z θ => if (z, θ) ∈ Qd
        then Work.Spaces.HkIntegrand α k (H s) z θ else 0)
      measurableSet_Icc ?_ ?_ ?_
    · intro s hs
      refine ((hsm s hs).continuousOn_HkIntegrand α k).congr ?_
      intro q hq
      exact ite_eq_left hq
    · intro s hs q hq
      exact ite_eq_right hq
    · intro q
      by_cases hq : q ∈ Qd
      · have hthis : (fun s : ℝ =>
            if (q.1, q.2) ∈ Qd then Work.Spaces.HkIntegrand α k (H s) q.1 q.2 else 0)
            = fun s : ℝ => Work.Spaces.HkIntegrand α k (H s) q.1 q.2 :=
          funext fun s => ite_eq_left hq
        rw [hthis]
        exact aesm_HkIntegrand_family hsm hcont hq
      · have hthis : (fun s : ℝ =>
            if (q.1, q.2) ∈ Qd then Work.Spaces.HkIntegrand α k (H s) q.1 q.2 else 0)
            = fun _ : ℝ => (0:ℝ) :=
          funext fun s => ite_eq_right hq
        rw [hthis]
        exact aestronglyMeasurable_const
  -- restrict the `(z,θ)`-factor to the open quadrant
  have hg : AEStronglyMeasurable
      (fun p : ℝ × (ℝ × ℝ) =>
        if (p.2.1, p.2.2) ∈ Qd
          then Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2 else 0)
      ((volume.restrict (Set.Icc (0:ℝ) T)).prod (volume.restrict Qd)) :=
    hmain.mono_measure
      (MeasureTheory.Measure.prod_mono le_rfl MeasureTheory.Measure.restrict_le_self)
  -- on that measure, the truncated integrand agrees a.e. with the integrand
  have hae : (fun p : ℝ × (ℝ × ℝ) =>
        if (p.2.1, p.2.2) ∈ Qd
          then Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2 else 0)
      =ᵐ[(volume.restrict (Set.Icc (0:ℝ) T)).prod (volume.restrict Qd)]
      (fun p : ℝ × (ℝ × ℝ) => Work.Spaces.HkIntegrand α k (H p.1) p.2.1 p.2.2) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine measure_mono_null (t := Set.univ ×ˢ Qdᶜ) ?_ ?_
    · intro p hp
      rw [Set.mem_prod]
      refine ⟨Set.mem_univ _, ?_⟩
      intro hpq
      exact hp (ite_eq_left hpq)
    · rw [MeasureTheory.Measure.prod_prod,
        MeasureTheory.Measure.restrict_apply measurableSet_Qd_compl]
      simp
  exact (hg.congr hae).aemeasurable

end Work.FTS.StrongEps.E5G
