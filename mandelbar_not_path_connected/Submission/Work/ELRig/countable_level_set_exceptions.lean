import Mathlib
import Submission.Work.ELRig.countable_zeros_of_analyticOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Set Filter

/-- For a curve `γ : ℝ → ℂ` which is continuous, satisfies `γ (s+1) = γ s + 1`, and is
real-analytic on each unit interval, the set of imaginary-part levels whose level set
(restricted to the fundamental window `[0,1)`) is infinite is countable. In fact such a level
can only be `(γ 0).im`.

The proof is the classical accumulation-point argument: the imaginary part `f = im γ` is
continuous, `1`-periodic and real analytic on `(0,1)`. If a value `c ≠ f 0` occurred infinitely
often in `[0,1)`, the (infinite) level set inside the compact interval `[0,1]` would have an
accumulation point `x ∈ [0,1]`. At an interior accumulation point the identity theorem forces
`f ≡ c` on `(0,1)`, whence `f 0 = c`; at an endpoint `x ∈ {0,1}` continuity forces `f x = c`,
and `f 1 = f 0`. Both contradict `c ≠ f 0`. -/
theorem countable_level_set_exceptions {γ : ℝ → ℂ}
    (hcont : Continuous γ) (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1)
    (han : ∀ n : ℤ, AnalyticOn ℝ γ (Set.Ioo (n : ℝ) ((n : ℝ) + 1))) :
    ({c : ℝ | ¬ ({s : ℝ | (γ s).im = c} ∩ Set.Ico (0 : ℝ) 1).Finite}).Countable := by
  set f : ℝ → ℝ := fun s => (γ s).im with hf_def
  have hfcont : Continuous f := by
    have h := Complex.continuous_im.comp hcont
    simpa [hf_def, Function.comp_def] using h
  have hfper : ∀ s : ℝ, f (s + 1) = f s := by
    intro s
    have h := congrArg Complex.im (hper s)
    simpa [hf_def] using h
  have hf : AnalyticOn ℝ f (Set.Ioo (0 : ℝ) 1) := by
    have hγ : AnalyticOn ℝ γ (Set.Ioo (0 : ℝ) 1) := by
      have h := han 0
      simpa using h
    have h := Complex.imCLM.comp_analyticOn hγ
    simpa [hf_def, Function.comp_def, Complex.imCLM_apply] using h
  have hfNhd : AnalyticOnNhd ℝ f (Set.Ioo (0 : ℝ) 1) :=
    fun y hy => hf.analyticAt (isOpen_Ioo.mem_nhds hy)
  apply Set.Countable.mono _ (Set.finite_singleton (f 0)).countable
  intro c hc
  have hc' : ¬ ({s : ℝ | f s = c} ∩ Set.Ico (0 : ℝ) 1).Finite := by
    simpa [hf_def] using hc
  let S : Set ℝ := {s : ℝ | f s = c} ∩ Set.Ico (0 : ℝ) 1
  have hSinf : S.Infinite := hc'
  have hSsub : S ⊆ Set.Icc (0 : ℝ) 1 := fun s hs => ⟨hs.2.1, le_of_lt hs.2.2⟩
  obtain ⟨x, hxK, hxacc⟩ := hSinf.exists_accPt_of_subset_isCompact isCompact_Icc hSsub
  rw [Set.mem_Icc] at hxK
  obtain ⟨h0x, hx1⟩ := hxK
  have hTclosed : IsClosed {s : ℝ | f s = c} := isClosed_eq hfcont continuous_const
  have haccT : AccPt x (𝓟 {s : ℝ | f s = c}) :=
    hxacc.mono (Filter.principal_mono.mpr (fun s hs => hs.1))
  have hxT : x ∈ {s : ℝ | f s = c} := (isClosed_iff_accPt.mp hTclosed) x haccT
  have hfx : f x = c := hxT
  have key : f 0 = c := by
    rcases lt_or_eq_of_le h0x with hx0 | hx0
    · rcases lt_or_eq_of_le hx1 with hxlt1 | hxeq1
      · -- interior accumulation point: identity theorem forces `f ≡ c` on `(0,1)`
        have hxI : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hxlt1⟩
        have hAcc : x ∈ closure (S \ {x}) :=
          mem_closure_iff_nhdsWithin_neBot.mpr (accPt_principal_iff_nhdsWithin.mp hxacc)
        have hsub2 : S \ {x} ⊆ ({s : ℝ | f s = c}) \ {x} := by
          intro s hs
          exact ⟨hs.1.1, hs.2⟩
        have hmem : x ∈ closure (({s : ℝ | f s = c}) \ {x}) := closure_mono hsub2 hAcc
        have heq : Set.EqOn f (fun _ : ℝ => c) (Set.Ioo (0 : ℝ) 1) :=
          hfNhd.eqOn_of_preconnected_of_mem_closure analyticOnNhd_const
            isPreconnected_Ioo hxI hmem
        have hsubI : Set.Ioo (0 : ℝ) 1 ⊆ {s : ℝ | f s = c} := fun y hy => heq hy
        have h0cl : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
          rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
          exact left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)
        have h0mem : (0 : ℝ) ∈ closure {s : ℝ | f s = c} := closure_mono hsubI h0cl
        rw [hTclosed.closure_eq] at h0mem
        exact h0mem
      · -- right endpoint
        have hf1 : f 1 = c := by rw [← hxeq1]; exact hfx
        have hper0 : f 1 = f 0 := by simpa using hfper 0
        exact hper0.symm.trans hf1
    · -- left endpoint
      have : f 0 = c := by rw [hx0]; exact hfx
      exact this
  rw [Set.mem_singleton_iff]
  exact key.symm

end Work.ELRig
