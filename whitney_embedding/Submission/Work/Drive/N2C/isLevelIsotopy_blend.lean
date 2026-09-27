import Mathlib
import Submission.Work.Drive.N2C.isotopyCalc
import Submission.Work.Drive.N2.levelPieceCover
import Submission.Work.Compat.MFDerivCongrV433

/-!
# B3: the concatenation of two level isotopies (the `N2C` blend)

`Work.Drive.N2C.IsLevelIsotopy f b e` (see `Submission/Work/Drive/N2C/defs.lean`) says that
`e : ℝ → M → ℝ³` is a jointly smooth family of *pictures* of the regular level `f ⁻¹' {b}`:
jointly smooth at `(s, y)` for `f y = b`, injective there, and `(df, d(e s))`-immersive there.

This file proves B3 of the coherent-window architecture
(`Submission/Work/Drive/N2Lead/NOTES_LEAD_coherentWindows.md`, Tier A/B): if `e₁` and `e₂` are
level isotopies at `b` which *agree on the level* for every time in `Icc t₀ t₁`, then there is a
level isotopy `e` with `e s = e₁ s` for `s ≤ t₀` and `e s = e₂ s` for `t₁ ≤ s`.

The construction is the convex combination with a smooth step `β`

    `e s y := (1 - β s) • e₁ s y + β s • e₂ s y`,

where `β = smoothTransition ∘ (fun s => (s - t₀)/(t₁ - t₀))` is `0` on `(-∞, t₀]` and `1` on
`[t₁, ∞)`.  The three rows of `IsLevelIsotopy` are:

* **smoothness**: a sum of products of the jointly smooth families with the smooth scalar `β`
  (composition of `ContMDiffAt` with the projection on the time, `smul` and `add`);
* **injectivity**: for `s ≤ t₁` the blend agrees on the level with `e₁ s` (for `s ≤ t₀` because
  `β s = 0`; for `t₀ ≤ s ≤ t₁` because `e₁ s = e₂ s` there), and for `t₁ ≤ s` with `e₂ s`;
* **immersion**: likewise for `s ≤ t₁` the blend agrees *on the level* with `e₁ s`, and the two
  derivatives on `ker df` of two maps agreeing on a regular level coincide — this is the
  auxiliary lemma `mfderiv_eq_on_ker_of_agreeOnLevel` at the top of the file, proved by
  parametrising the level near a point by a curve with prescribed tangent
  (`Work.Drive.N2.exists_local_levelParam` + `Work.Drive.N2.inj_imp_ne_zero_and_surj`) and using
  the chain rule, the composite `e₁ s ∘ γ = e₂ s ∘ γ` being eventually constant.

The empty level is not a special case: every row of `IsLevelIsotopy` is a statement about
level points, and the auxiliary lemma is applied at a level point.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter
open Classical

/-- **Two maps agreeing on a regular level have the same derivative on `ker (df)`.**

Let `b` be a regular value of the smooth map `f` on a surface (`¬ IsCritical f x` at every
`f x = b`), and let `g₁, g₂` be smooth at every point of the level and agree there.  Then for
`f x = b` and `v : T_x M` with `df_x v = 0` the two derivatives at `x` in the direction `v`
coincide.

Proof: by `Work.Drive.N2.exists_local_levelParam` the level near a regular point `x` is covered by
a `C^∞` curve `γ` through `x` whose derivative covers `ker df`
(`Work.Drive.N2.inj_imp_ne_zero_and_surj`); writing `v = dγ_t w`, the composites `g₁ ∘ γ` and
`g₂ ∘ γ` agree eventually at `t` (both land on the level there), hence have the same `mfderiv`
(`Filter.EventuallyEq.mfderiv_eq_v433`), and the chain rule converts this into `d(g₁)_x v = d(g₂)_x v`.

(The `TangentSpace` types of the two sides are equal — `TangentSpace I x` is the model space — but
they are not syntactically equal, which is why the final combination is done with `Eq.trans` on
`mfderiv` of the composites rather than by rewriting.) -/
theorem mfderiv_eq_on_ker_of_agreeOnLevel {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤:ℕ∞):WithTop ℕ∞) f) {b : ℝ}
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    {g₁ g₂ : M → EuclideanSpace ℝ (Fin 3)}
    (h₁ : ∀ x : M, f x = b → ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤:ℕ∞):WithTop ℕ∞) g₁ x)
    (h₂ : ∀ x : M, f x = b → ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤:ℕ∞):WithTop ℕ∞) g₂ x)
    (hagree : ∀ x : M, f x = b → g₁ x = g₂ x) :
    ∀ (x : M) (v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) x),
      f x = b →
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) f x v = 0 →
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) g₁ x v
        = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) g₂ x v := by
  intro x v hxb hv
  have hxreg : mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f x ≠ 0 := by
    simpa [Work.Drive.Morse.IsCritical] using hreg x hxb
  obtain ⟨U, V, γ, hUo, hxU, hVo, h0V, hγsm, hlev, hγinj, hγreg, hcov⟩ :=
    Work.Drive.N2.exists_local_levelParam f hf b x hxb hxreg
  obtain ⟨-, hsurj⟩ :=
    Work.Drive.N2.inj_imp_ne_zero_and_surj f hf b γ V hVo hγsm hlev hγinj hγreg
  obtain ⟨t₀, ht₀V, ht₀x⟩ := hcov ⟨hxb, hxU⟩
  subst ht₀x
  obtain ⟨w, hw⟩ := hsurj t₀ ht₀V v hv
  have hev : (g₁ ∘ γ) =ᶠ[𝓝 t₀] (g₂ ∘ γ) := by
    filter_upwards [hVo.mem_nhds ht₀V] with s hs
    exact hagree (γ s) (hlev s hs)
  have hmd : mfderiv (𝓘(ℝ,ℝ)) (𝓡 3) (g₁ ∘ γ) t₀ = mfderiv (𝓘(ℝ,ℝ)) (𝓡 3) (g₂ ∘ γ) t₀ :=
    hev.mfderiv_eq_v433
  have hγmd : MDifferentiableAt (𝓘(ℝ,ℝ)) (𝓡 2) γ t₀ :=
    (hγsm.contMDiffAt (hVo.mem_nhds ht₀V)).mdifferentiableAt (by simp)
  have h1md : MDifferentiableAt (𝓡 2) (𝓡 3) g₁ (γ t₀) :=
    (h₁ (γ t₀) (hlev t₀ ht₀V)).mdifferentiableAt (by simp)
  have h2md : MDifferentiableAt (𝓡 2) (𝓡 3) g₂ (γ t₀) :=
    (h₂ (γ t₀) (hlev t₀ ht₀V)).mdifferentiableAt (by simp)
  have hc₁ := mfderiv_comp_apply (f := γ) (g := g₁) t₀ h1md hγmd w
  have hc₂ := mfderiv_comp_apply (f := γ) (g := g₂) t₀ h2md hγmd w
  rw [← hw]
  exact hc₁.symm.trans ((congrArg (fun L => L w) hmd).trans hc₂)

/-- **B3: the concatenation of two level isotopies.**  If `e₁` and `e₂` are level isotopies at `b`
that agree on the level for all times in `Icc t₀ t₁`, then they can be blended into a single level
isotopy that *is* `e₁` up to `t₀` and *is* `e₂` from `t₁` on. -/
theorem isLevelIsotopy_blend {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {b : ℝ}
    (hreg : ∀ x : M, f x = b → ¬ Work.Drive.Morse.IsCritical f x)
    {e₁ e₂ : ℝ → M → EuclideanSpace ℝ (Fin 3)}
    (h₁ : Work.Drive.N2C.IsLevelIsotopy f b e₁) (h₂ : Work.Drive.N2C.IsLevelIsotopy f b e₂)
    {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (hagree : ∀ s ∈ Set.Icc t₀ t₁, ∀ y : M, f y = b → e₁ s y = e₂ s y) :
    ∃ e : ℝ → M → EuclideanSpace ℝ (Fin 3), Work.Drive.N2C.IsLevelIsotopy f b e ∧
      (∀ s, s ≤ t₀ → e s = e₁ s) ∧ (∀ s, t₁ ≤ s → e s = e₂ s) := by
  have hden : (0:ℝ) < t₁ - t₀ := sub_pos.mpr ht
  -- the smooth step
  set β : ℝ → ℝ := fun s => Real.smoothTransition ((s - t₀) / (t₁ - t₀)) with hβdef
  have hβcd : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) β := by
    rw [hβdef]
    exact Real.smoothTransition.contDiff.comp (by fun_prop)
  have hβ0 : ∀ s, s ≤ t₀ → β s = 0 := by
    intro s hs
    rw [hβdef]
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le)
  have hβ1 : ∀ s, t₁ ≤ s → β s = 1 := by
    intro s hs
    rw [hβdef]
    exact Real.smoothTransition.one_of_one_le ((one_le_div hden).mpr (by linarith))
  -- the blend
  set e : ℝ → M → EuclideanSpace ℝ (Fin 3) :=
    fun s y => (1 - β s) • e₁ s y + β s • e₂ s y with he
  have hjoint : ∀ (s : ℝ) (y : M), f y = b →
      ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 3) ((⊤:ℕ∞):WithTop ℕ∞)
        (fun p : ℝ × M => e p.1 p.2) (s, y) := by
    intro s y hy
    rw [he]
    have hβcomp : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓘(ℝ,ℝ)) ((⊤:ℕ∞):WithTop ℕ∞)
        (fun p : ℝ × M => β p.1) (s, y) :=
      hβcd.contMDiff.contMDiffAt.comp (s, y) contMDiff_fst.contMDiffAt
    have h1b : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓘(ℝ,ℝ)) ((⊤:ℕ∞):WithTop ℕ∞)
        (fun p : ℝ × M => 1 - β p.1) (s, y) := contMDiffAt_const.sub hβcomp
    exact (h1b.smul (h₁.1 s y hy)).add (hβcomp.smul (h₂.1 s y hy))
  have hesm : ∀ (s : ℝ) (y : M), f y = b →
      ContMDiffAt (𝓡 2) (𝓡 3) ((⊤:ℕ∞):WithTop ℕ∞) (e s) y := by
    intro s y hy
    have h := (hjoint s y hy).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
    simpa only [Function.comp_def] using h
  have hslice₁ : ∀ (s : ℝ) (y : M), f y = b →
      ContMDiffAt (𝓡 2) (𝓡 3) ((⊤:ℕ∞):WithTop ℕ∞) (e₁ s) y := by
    intro s y hy
    have h := (h₁.1 s y hy).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
    simpa only [Function.comp_def] using h
  have hslice₂ : ∀ (s : ℝ) (y : M), f y = b →
      ContMDiffAt (𝓡 2) (𝓡 3) ((⊤:ℕ∞):WithTop ℕ∞) (e₂ s) y := by
    intro s y hy
    have h := (h₂.1 s y hy).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
    simpa only [Function.comp_def] using h
  -- the blend agrees with `e₁` on the level for `s ≤ t₁`, and with `e₂` for `t₀ ≤ s`
  have hleft : ∀ s, s ≤ t₁ → ∀ y : M, f y = b → e s y = e₁ s y := by
    intro s hs y hy
    rcases le_total s t₀ with h | h
    · have hb : β s = 0 := hβ0 s h
      simp only [he, hb, sub_zero, zero_smul, add_zero, one_smul]
    · have hb : e₂ s y = e₁ s y := (hagree s ⟨h, hs⟩ y hy).symm
      simp only [he, hb, ← add_smul, sub_add_cancel, one_smul]
  have hright : ∀ s, t₀ ≤ s → ∀ y : M, f y = b → e s y = e₂ s y := by
    intro s hs y hy
    rcases le_total t₁ s with h | h
    · have hb : β s = 1 := hβ1 s h
      simp only [he, hb, sub_self, zero_smul, one_smul, zero_add]
    · have hb : e₁ s y = e₂ s y := hagree s ⟨hs, h⟩ y hy
      simp only [he, hb, ← add_smul, sub_add_cancel, one_smul]
  refine ⟨e, ⟨hjoint, ?_, ?_⟩, ?_, ?_⟩
  · -- injectivity on the level
    intro s x y hx hy hxy
    rcases le_total s t₁ with hs | hs
    · rw [hleft s hs x hx, hleft s hs y hy] at hxy
      exact h₁.2.1 s x y hx hy hxy
    · rw [hright s (le_trans ht.le hs) x hx, hright s (le_trans ht.le hs) y hy] at hxy
      exact h₂.2.1 s x y hx hy hxy
  · -- `ker df`-immersivity on the level
    intro s y hy v hv hw
    rcases le_total s t₁ with hs | hs
    · have hmf := mfderiv_eq_on_ker_of_agreeOnLevel hf hreg (fun z hz => hesm s z hz)
        (fun z hz => hslice₁ s z hz) (fun z hz => hleft s hs z hz) y v hy hv
      exact h₁.2.2 s y hy v hv (hmf.symm.trans hw)
    · have hs0 : t₀ ≤ s := le_trans ht.le hs
      have hmf := mfderiv_eq_on_ker_of_agreeOnLevel hf hreg (fun z hz => hesm s z hz)
        (fun z hz => hslice₂ s z hz) (fun z hz => hright s hs0 z hz) y v hy hv
      exact h₂.2.2 s y hy v hv (hmf.symm.trans hw)
  · -- agreement below `t₀`
    intro s hs
    funext y
    simp only [he, hβ0 s hs, sub_zero, zero_smul, add_zero, one_smul]
  · -- agreement above `t₁`
    intro s hs
    funext y
    simp only [he, hβ1 s hs, sub_self, zero_smul, one_smul, zero_add]

end Work.Drive.N2C
