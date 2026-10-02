import Submission.Work.Serre.MapPathDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The projection of the mapping path space is a homotopy equivalence

The projection `mpathFst p : mpath p → E`, `(e, γ) ↦ e`, has the strict section
`mpathOf p : e ↦ (e, const (p e))`, and `mpathOf p ∘ mpathFst p` is homotopic to the identity of
`mpath p` by the path contraction `(e, γ) ↦ (e, s ↦ γ (t s))`.  Hence `mpathFst p` is a homotopy
equivalence, and therefore induces isomorphisms on rational singular homology.
-/

open scoped Topology unitInterval
open ContinuousMap

namespace Work.Serre

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **`mpathFst p` is a rational homology isomorphism.**  It is a homotopy equivalence, with
homotopy inverse `mpathOf p`. -/
theorem mpathFst_ratHomologyIso (p : C(E, B)) : IsRatHomologyIso (mpathFst p) := by
  have hF2 : Continuous fun q : mpath p × I => (mpathSnd p) q.1 q.2 :=
    continuous_eval.comp (((mpathSnd p).continuous.comp continuous_fst).prodMk continuous_snd)
  have hcont : Continuous fun y : (I × mpath p) × I =>
      (mpathSnd p) y.1.2 (Work.StemsB.clampI ((y.1.1 : ℝ) * (y.2 : ℝ))) :=
    hF2.comp (Continuous.prodMk (continuous_snd.comp continuous_fst)
      (Work.StemsB.continuous_clampI.comp (by fun_prop)))
  let Ψcm : C((I × mpath p) × I, B) := ⟨_, hcont⟩
  let Cm : C(I × mpath p, C(I, B)) := Ψcm.curry
  have hC : ∀ (y : I × mpath p) (s : I), Cm y s
      = (mpathSnd p) y.2 (Work.StemsB.clampI ((y.1 : ℝ) * (s : ℝ))) :=
    fun y s => ContinuousMap.curry_apply Ψcm y s
  have hdata : ∀ y : I × mpath p,
      (⟨((y.2).1.1, Cm y), by
        have h0I : (((0 : I)) : ℝ) = 0 := rfl
        have hy : (y.1 : ℝ) * (((0 : I)) : ℝ) = 0 := by rw [h0I, mul_zero]
        rw [hC y 0, hy, Work.StemsB.clampI_zero]
        exact (y.2).2⟩ : mpath p)
      = ⟨((y.2).1.1, Cm y), by
        have h0I : (((0 : I)) : ℝ) = 0 := rfl
        have hy : (y.1 : ℝ) * (((0 : I)) : ℝ) = 0 := by rw [h0I, mul_zero]
        rw [hC y 0, hy, Work.StemsB.clampI_zero]
        exact (y.2).2⟩ := fun y => rfl
  let Φp : I × mpath p → mpath p := fun y =>
    ⟨((y.2).1.1, Cm y), by
      have h0I : (((0 : I)) : ℝ) = 0 := rfl
      have hy : (y.1 : ℝ) * (((0 : I)) : ℝ) = 0 := by rw [h0I, mul_zero]
      rw [hC y 0, hy, Work.StemsB.clampI_zero]
      exact (y.2).2⟩
  have hΦpc : Continuous Φp := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ Cm.continuous) _
    exact (mpathFst p).continuous.comp continuous_snd
  let Φ : C(I × mpath p, mpath p) := ⟨Φp, hΦpc⟩
  have hleft : ((mpathOf p).comp (mpathFst p)).Homotopic (ContinuousMap.id (mpath p)) := by
    refine ⟨ContinuousMap.Homotopy.mk Φ ?_ ?_⟩
    · intro x
      show Φp (0, x) = ((mpathOf p).comp (mpathFst p)) x
      rw [show ((mpathOf p).comp (mpathFst p)) x
        = ⟨(x.1.1, ContinuousMap.const I (p x.1.1)), rfl⟩ from rfl]
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro s
        have h0I : (((0 : I)) : ℝ) = 0 := rfl
        have hs : (((0 : I)) : ℝ) * (s : ℝ) = 0 := by rw [h0I, zero_mul]
        rw [hC (0, x) s, hs, Work.StemsB.clampI_zero]
        exact x.2
    · intro x
      show Φp (1, x) = (ContinuousMap.id (mpath p)) x
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro s
        have h1I : (((1 : I)) : ℝ) = 1 := rfl
        have hs : (((1 : I)) : ℝ) * (s : ℝ) = (s : ℝ) := by rw [h1I, one_mul]
        rw [hC (1, x) s, hs, Work.StemsB.clampI_coe_I]
        rfl
  have hright : ((mpathFst p).comp (mpathOf p)).Homotopic (ContinuousMap.id E) := by
    have h : (mpathFst p).comp (mpathOf p) = ContinuousMap.id E := by ext e; rfl
    rw [h]
  exact IsRatHomologyIso.of_homotopyEquiv
    (ContinuousMap.HomotopyEquiv.mk (mpathFst p) (mpathOf p) hleft hright)


end

end Work.Serre
