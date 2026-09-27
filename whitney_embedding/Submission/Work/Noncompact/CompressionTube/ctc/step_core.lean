import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_defs
import Submission.Work.Noncompact.CompressionTube.ctc.exists_gauge
import Submission.Work.Noncompact.CompressionTube.ctc.exists_transverse_blend
import Submission.Work.Noncompact.CompressionTube.ctc.exists_transverse_on_Icc

/-!
# One step of the two-sided piece recursion

Given a piece `Ψ` transverse along the line on the window `(k - 21/8, k + 1)` and a raw piece `ψ`
transverse on the compact window `[k - 2, k + 2]`, we build a new piece `Ψ'` together with a width
`d ∈ (0, 1/4]` such that

* `Ψ'` agrees with `Ψ` on the region `{g ≤ k - d}`,
* `Ψ'` is transverse on the window `(k - 13/8, k + 2)`.

The construction is the blend: gauge `ψ` by the linear map `A` of `exists_gauge` which makes its
differential at `γ k` equal to that of `Ψ` (`A ∘ dψ(γ k) = dΨ(γ k)`), and interpolate between `Ψ`
and `R := A ∘ ψ` with a smooth step function of `g` whose transition is shorter than the radius
supplied by `exists_transverse_blend` at the switch point `k`.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function Filter

noncomputable section

set_option maxHeartbeats 1600000

set_option backward.isDefEq.respectTransparency false in
/-- `A ∘ dψ(γ k)` kills the velocity of `γ` at `k` (the `A` here is the gauge of
`exists_gauge`, but the statement is general). -/
lemma ctc_gauge_comp_velocity {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hψc : ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ) (hψ0 : ∀ s : ℝ, ψ (γ s) = 0)
    (A : EuclideanSpace ℝ (Fin (n - 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n - 1))) (k : ℝ) :
    (A.comp (mfderiv (MC n) (MC (n - 1)) ψ (γ k))) (mfderiv MCreal (MC n) γ k 1) = 0 := by
  show A (mfderiv (MC n) (MC (n - 1)) ψ (γ k) (mfderiv MCreal (MC n) γ k 1)) = 0
  simp only [mfderiv_velocity_eq_zero hγ hψc hψ0 k, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- `dΨ(γ k)` kills the velocity of `γ` at `k`. -/
lemma ctc_velocity_eq_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    {Ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hΨc : ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ) (hΨ0 : ∀ s : ℝ, Ψ (γ s) = 0) (k : ℝ) :
    mfderiv (MC n) (MC (n - 1)) Ψ (γ k) (mfderiv MCreal (MC n) γ k 1) = 0 :=
  mfderiv_velocity_eq_zero hγ hΨc hΨ0 k

/-- **One step of the piece recursion.** -/
theorem ctc_step_exists {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {γ : ℝ → M} (hγ : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder γ) (hinj : Function.Injective γ)
    (hprop : IsProperMap γ) (himm : ∀ s : ℝ, Function.Injective (mfderiv
      Work.Noncompact.CompressionTube.MCreal (Work.Noncompact.CompressionTube.MC n) γ s))
    {g : M → ℝ} (hg : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.MCreal Work.Noncompact.CompressionTube.smoothOrder g)
    (hgcore : ∀ s : ℝ, g (γ s) = s)
    (k : ℤ) {Ψ ψ : M → EuclideanSpace ℝ (Fin (n - 1))}
    (hΨc : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC (n - 1))
      Work.Noncompact.CompressionTube.smoothOrder Ψ)
    (hψc : ContMDiff (Work.Noncompact.CompressionTube.MC n)
      (Work.Noncompact.CompressionTube.MC (n - 1))
      Work.Noncompact.CompressionTube.smoothOrder ψ)
    (hΨ0 : ∀ s : ℝ, Ψ (γ s) = 0) (hψ0 : ∀ s : ℝ, ψ (γ s) = 0)
    (hΨT : ∀ s : ℝ, s ∈ Set.Ioo ((k : ℝ) - 21 / 8) ((k : ℝ) + 1) →
      Work.Noncompact.CompressionTube.Transverse γ g Ψ s)
    (hψT : ∀ s : ℝ, s ∈ Set.Icc ((k : ℝ) - 2) ((k : ℝ) + 2) →
      Work.Noncompact.CompressionTube.Transverse γ g ψ s) :
    ∃ (Ψ' : M → EuclideanSpace ℝ (Fin (n - 1))) (d : ℝ), 0 < d ∧ d ≤ 1 / 8 ∧
      ContMDiff (Work.Noncompact.CompressionTube.MC n)
        (Work.Noncompact.CompressionTube.MC (n - 1))
        Work.Noncompact.CompressionTube.smoothOrder Ψ' ∧
      (∀ s : ℝ, Ψ' (γ s) = 0) ∧
      (∀ s : ℝ, s ∈ Set.Ioo ((k : ℝ) - 13 / 8) ((k : ℝ) + 2) →
        Work.Noncompact.CompressionTube.Transverse γ g Ψ' s) ∧
      (∀ x : M, g x ≤ (k : ℝ) - d → Ψ' x = Ψ x) := by
  classical
  have hn0 : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  -- transversality at the switch point `k`
  have hΨTk : Transverse γ g Ψ (k : ℝ) := by
    refine hΨT _ (Set.mem_Ioo.mpr ⟨?_, ?_⟩) <;> push_cast <;> norm_num
  have hψTk : Transverse γ g ψ (k : ℝ) := by
    refine hψT _ (Set.mem_Icc.mpr ⟨?_, ?_⟩) <;> push_cast <;> norm_num
  -- the gauge
  obtain ⟨A, hAinj, hAgauge⟩ := exists_gauge hn hγ hg hgcore hΨc hψc hΨ0 hψ0 (k : ℝ) hΨTk hψTk
  -- the gauge-transformed raw piece
  set R : M → EuclideanSpace ℝ (Fin (n - 1)) := fun x => A (ψ x) with hRdef
  have hRc : ContMDiff (MC n) (MC (n - 1)) smoothOrder R := by
    rw [hRdef]
    exact (A.contMDiff (n := smoothOrder)).comp hψc
  have hR0 : ∀ s : ℝ, R (γ s) = 0 := fun s => by simp [hRdef, hψ0 s]
  -- the chain rule for `R`
  have hA_at (s : ℝ) : MDifferentiableAt (MC (n - 1)) (MC (n - 1))
      (⇑A) (ψ (γ s)) :=
    (A.contMDiff (n := smoothOrder)).mdifferentiableAt (x := ψ (γ s)) hn0
  have hRder (s : ℝ) : mfderiv (MC n) (MC (n - 1)) R (γ s)
      = A.comp (mfderiv (MC n) (MC (n - 1)) ψ (γ s)) := by
    have hψd : MDifferentiableAt (MC n) (MC (n - 1)) ψ (γ s) :=
      hψc.mdifferentiableAt (x := γ s) hn0
    have hcomp := mfderiv_comp (I := MC n) (I' := MC (n - 1)) (I'' := MC (n - 1))
      (f := ψ) (g := ⇑A) (γ s) (hA_at s) hψd
    have h1 : mfderiv (MC (n - 1)) (MC (n - 1)) (⇑A) (ψ (γ s)) = A := by
      rw [show mfderiv (MC (n - 1)) (MC (n - 1)) (⇑A) (ψ (γ s))
            = fderiv ℝ (⇑A) (ψ (γ s)) from mfderiv_eq_fderiv]
      exact ContinuousLinearMap.fderiv A
    have h2 : R = ⇑A ∘ ψ := rfl
    rw [h2, hcomp, h1]
    rfl
  have hagree : mfderiv (MC n) (MC (n - 1)) R (γ (k : ℝ))
      = mfderiv (MC n) (MC (n - 1)) Ψ (γ (k : ℝ)) := by
    rw [hRder]
    refine eq_of_agree_on_ker hgcore hγ hg (k : ℝ) ?_ ?_ ?_
    · exact ctc_gauge_comp_velocity hγ hψc hψ0 A (k : ℝ)
    · exact ctc_velocity_eq_zero hγ hΨc hΨ0 (k : ℝ)
    · intro v _
      show A (mfderiv (MC n) (MC (n - 1)) ψ (γ (k : ℝ)) v)
        = mfderiv (MC n) (MC (n - 1)) Ψ (γ (k : ℝ)) v
      exact hAgauge v
  -- the blend radius
  obtain ⟨ρ, hρpos, hρ⟩ :=
    exists_transverse_blend hn hγ hinj hprop himm hg hgcore hΨc hRc hΨ0 hR0 hagree.symm hΨTk
  -- the transition width
  set d : ℝ := min (ρ / 2) (1 / 8) with hddef
  have hdpos : 0 < d := lt_min (by linarith) (by norm_num)
  have hdle : d ≤ 1 / 8 := min_le_right _ _
  have hdlt : d < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨χ, hχsm, hχI, hχ1, hχ0⟩ := exists_smoothStep (k : ℝ) d hdpos
  refine ⟨fun x : M => χ (g x) • Ψ x + (1 - χ (g x)) • R x, d, hdpos, hdle, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro x
    have h1 : ContMDiffAt (MC n) MCreal smoothOrder (fun x : M => χ (g x)) x :=
      ((contMDiff_iff_contDiff.mpr hχsm).contMDiffAt (x := g x)).comp x hg.contMDiffAt
    have h2 : ContMDiffAt (MC n) MCreal smoothOrder (fun x : M => 1 - χ (g x)) x :=
      contMDiffAt_const.sub h1
    exact (h1.smul hΨc.contMDiffAt).add (h2.smul hRc.contMDiffAt)
  · -- vanishing on the line
    intro s
    simp only
    rw [hΨ0 s, hR0 s, smul_zero, smul_zero, add_zero]
  · -- transversality
    intro s hs
    by_cases hb : |s - (k : ℝ)| < ρ
    · exact hρ χ hχsm hχI s hb
    · push_neg at hb
      rcases le_total s (k : ℝ) with hsk | hsk
      · -- left of the transition: the germ is `Ψ`
        have hks : (k : ℝ) - s = |s - (k : ℝ)| := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        have hslt : s < (k : ℝ) - d := by linarith [hks.ge, hb, hdlt]
        have hgerm : (fun x : M => χ (g x) • Ψ x + (1 - χ (g x)) • R x) =ᶠ[𝓝 (γ s)] Ψ := by
          have hopen : IsOpen {x : M | g x < (k : ℝ) - d} :=
            isOpen_lt hg.continuous continuous_const
          have hmem : γ s ∈ {x : M | g x < (k : ℝ) - d} := by
            simp only [Set.mem_setOf_eq, hgcore s]; exact hslt
          filter_upwards [hopen.mem_nhds hmem] with x hx
          rw [hχ1 (g x) hx.le]
          simp
        refine (transverse_congr hgerm).mpr (hΨT s ?_)
        refine Set.mem_Ioo.mpr ⟨by linarith [hs.1], by linarith⟩
      · -- right of the transition: the germ is `R`
        have hks : s - (k : ℝ) = |s - (k : ℝ)| := by
          rw [abs_of_nonneg (by linarith)]
        have hsgt : (k : ℝ) + d < s := by linarith [hks.ge, hb, hdlt]
        have hgerm : (fun x : M => χ (g x) • Ψ x + (1 - χ (g x)) • R x) =ᶠ[𝓝 (γ s)] R := by
          have hopen : IsOpen {x : M | (k : ℝ) + d < g x} :=
            isOpen_lt continuous_const hg.continuous
          have hmem : γ s ∈ {x : M | (k : ℝ) + d < g x} := by
            simp only [Set.mem_setOf_eq, hgcore s]; exact hsgt
          filter_upwards [hopen.mem_nhds hmem] with x hx
          rw [hχ0 (g x) hx.le]
          simp
        refine (transverse_congr hgerm).mpr ?_
        intro v hv1 hv2
        have hψv : mfderiv (MC n) (MC (n - 1)) ψ (γ s) v = 0 := by
          refine hAinj ?_
          have happ := congrArg (fun (L : TangentSpace (MC n) (γ s) →L[ℝ]
              EuclideanSpace ℝ (Fin (n - 1))) => L v) (hRder s)
          have hzero : (A.comp (mfderiv (MC n) (MC (n - 1)) ψ (γ s))) v = 0 := by
            rw [← happ]
            exact hv1
          calc A ((mfderiv (MC n) (MC (n - 1)) ψ (γ s)) v)
              = (A.comp (mfderiv (MC n) (MC (n - 1)) ψ (γ s))) v := rfl
            _ = 0 := hzero
            _ = A 0 := (map_zero A).symm
        exact hψT s (Set.mem_Icc.mpr ⟨by linarith, by linarith [hs.2]⟩) v hψv hv2
  · -- the equality on the left
    intro x hx
    simp only [hχ1 (g x) hx, one_smul, sub_self, zero_smul, add_zero]

end

end Work.Noncompact.CompressionTube
