import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2C.isotopyCalc
import Submission.Work.Drive.N2C.isLevelIsotopy_blend
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_roundImage

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology in
/-- **Certificate transfer along an ambient path** (Tier `D2d.2` of
`N2Lead/NOTES_LEAD_mobiusSaddle.md`).  If an ambient path `F` (an `AmbientPath`, i.e. a jointly smooth
family of injective immersions of `ℝ³` starting at the identity) carries the picture `g` of the level
`u` to a *certified* picture (at the end of the path), then `g` itself is certified: the path
`s ↦ F (smoothTransition s) ∘ g` is a level isotopy from `g` to `F 1 ∘ g` (Tier B1, the global
`isLevelIsotopy_ambient`, whose slices `F ·` are injective immersions by `AmbientPath`), and it is
blended with the certificate isotopy of the target picture by Tier B3 `isLevelIsotopy_blend` (the two
agree at the junction time, where the path is constant).  Time reparametrisations are
`isLevelIsotopy_comp_time`.  This is what lets the Möbius certificate move the pinned picture by the
slab twists of `D2d.1` (`Work.Drive.N2Lead.twistToolkit`).  The result goes in namespace
`Work.Drive.N2Lead`. -/
theorem isCertifiedAt_of_ambientPath {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {u : ℝ}
    (hreg : ∀ x : M, f x = u → ¬ Work.Drive.Morse.IsCritical f x)
    {g : M → EuclideanSpace ℝ (Fin 3)}
    (hg : Work.Drive.N2C.IsLevelIsotopy f u (fun _ : ℝ => g))
    {F : ℝ → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hF : Work.Drive.N2Lead.AmbientPath F)
    (h1 : Work.Drive.N2C.IsCertifiedAt f u (fun y : M => F 1 (g y))) :
    Work.Drive.N2C.IsCertifiedAt f u g := by
  -- Unpack the certificate of the target picture `F 1 ∘ g`.
  obtain ⟨n, L, D, eC, hDdisj, heC, heC0, heC1⟩ := h1
  -- (i) The ambient path, run with the monotone transition `smoothTransition` as time.
  have hP : Work.Drive.N2C.IsLevelIsotopy f u (fun s y => F (Real.smoothTransition s) (g y)) :=
    Work.Drive.N2C.isLevelIsotopy_comp_time
      (Work.Drive.N2C.isLevelIsotopy_ambient_contDiff (he := hg) hF.smooth hF.inj hF.imm)
      (Real.smoothTransition.contDiff (n := ⊤))
  -- (ii) The certificate isotopy, held still for two units of time before it starts.
  have hQ : Work.Drive.N2C.IsLevelIsotopy f u
      (fun s y => eC (Real.smoothTransition (s - 2)) y) :=
    Work.Drive.N2C.isLevelIsotopy_comp_time heC (by fun_prop)
  -- The two agree on the level over the junction interval `[1, 2]`: there the path is constant
  -- (`smoothTransition s = 1`, so the first family is `F 1 ∘ g`) and the certificate has not started
  -- (`smoothTransition (s - 2) = 0`, so the second family is `eC 0 = F 1 ∘ g`).
  have hagree : ∀ s ∈ Set.Icc (1:ℝ) 2, ∀ y : M, f y = u →
      (fun s y => F (Real.smoothTransition s) (g y)) s y
        = (fun s y => eC (Real.smoothTransition (s - 2)) y) s y := by
    intro s hs y hy
    simp only
    rw [Real.smoothTransition.one_of_one_le hs.1,
        Real.smoothTransition.zero_of_nonpos (by linarith [hs.2])]
    exact (heC0 y hy).symm
  obtain ⟨E, hE, hEleft, hEright⟩ :=
    Work.Drive.N2C.isLevelIsotopy_blend hf hreg hP hQ (t₀ := 1) (t₁ := 2) (by norm_num) hagree
  -- (iii) A final reparametrisation of the time sends `0 ↦ 0` and `1 ↦ 3`.
  have hfin : Work.Drive.N2C.IsLevelIsotopy f u (fun s => E (3 * Real.smoothTransition s)) :=
    Work.Drive.N2C.isLevelIsotopy_comp_time hE (by fun_prop)
  refine ⟨n, L, D, (fun s => E (3 * Real.smoothTransition s)), hDdisj, hfin, ?_, ?_⟩
  · -- time `0`: the reparametrised blend is `E 0 = g` on the level.
    intro y hy
    have hs0 : Real.smoothTransition (0:ℝ) = 0 := Real.smoothTransition.zero_of_nonpos le_rfl
    have h0 : (3:ℝ) * Real.smoothTransition (0:ℝ) = 0 := by rw [hs0, mul_zero]
    show E (3 * Real.smoothTransition 0) y = g y
    rw [h0]
    have hEP : E 0 = (fun s y => F (Real.smoothTransition s) (g y)) 0 := hEleft 0 (by norm_num)
    rw [hEP]
    simp only [hs0, hF.zero]
  · -- time `1`: the reparametrised blend is `E 3 = eC 1`, the round picture.
    intro i x
    have hs1 : Real.smoothTransition (1:ℝ) = 1 := Real.smoothTransition.one_of_one_le le_rfl
    have h3 : (3:ℝ) * Real.smoothTransition (1:ℝ) = 3 := by rw [hs1, mul_one]
    show E (3 * Real.smoothTransition 1) (L.γ i x) = D.circle i x
    rw [h3]
    have hEQ : E 3 = (fun s y => eC (Real.smoothTransition (s - 2)) y) 3 := hEright 3 (by norm_num)
    rw [hEQ]
    have h32 : (3:ℝ) - 2 = 1 := by norm_num
    simp only [h32, hs1]
    exact heC1 i x

end Work.Drive.N2Lead
