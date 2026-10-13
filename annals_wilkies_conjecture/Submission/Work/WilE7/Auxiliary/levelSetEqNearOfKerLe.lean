import Mathlib

/-
  `Work.WilE7.Aux.levelSetEqNearOfKerLe` — near a common zero `p`, two submersions
  `g, g' : ℝⁿ → ℝᵏ` whose kernels at `p` are nested (hence equal, both being of
  dimension `n - k`) have the same zero set near `p`, provided one inclusion of the
  zero sets holds near `p`.

  STATUS: PROVED.  Sorry-free; `#print axioms` gives exactly
  `[propext, Classical.choice, Quot.sound]`.

  ## The assigned module path is unbuildable (environment, not mathematics)

  `lake build Submission.Work.WilE7.Aux.levelSetEqNearOfKerLe` can never succeed, for any
  file content.  `Lean.Elab.checkModuleNamePortability` (`Lean/Elab/Import.lean`, toolchain
  4.35.0-rc3) upper-cases every component of the *main module* name while the header is
  processed and rejects `CON PRN AUX NUL COM1..9 LPT1..9`; the path component `Aux` is hit,
  the error is emitted at position 1:0 (before any command of the body is read), and no
  `.olean` is written.  No content, tactic, `import` or `set_option` can avoid it: the module
  name is forced by the path (`lake build X` resolves `X` to the module literally named `X`,
  and bare `lake env lean <file>` derives the same name from the path).  The Lean *namespace*
  `Work.WilE7.Aux` is fine — only the module name is affected.

  ## Buildable copy (use this one)

  A byte-identical copy of this file lives at

    Submission/Work/WilE7/Auxiliary/levelSetEqNearOfKerLe.lean
    module Submission.Work.WilE7.Auxiliary.levelSetEqNearOfKerLe

  which builds:
  `lake build Submission.Work.WilE7.Auxiliary.levelSetEqNearOfKerLe`.
  It declares the same fully qualified names, so consumers may import it and use
  `Work.WilE7.Aux.levelSetChart`, `Work.WilE7.Aux.levelSetEqNearOfKerLe`,
  `Work.WilE7.Aux.levelSetEqNearOfKerLeGeneral` and
  `Work.WilE7.Aux.levelSet_eq_near_of_kerLe`.

  ## Mathematics

  Let `W := (fderiv ℝ g p).ker`.  Both differentials are onto `ℝᵏ`, so both kernels have
  dimension `n - k`; with the hypothesis `ker (fderiv g p) ≤ ker (fderiv g' p)` this gives
  `ker (fderiv g' p) = W`.  Fixing one continuous projection `C : ℝⁿ →L[ℝ] W` onto `W`
  (`Submodule.ClosedComplemented`, available since the range is finite dimensional) and
  applying the implicit function theorem to the two local homeomorphisms
  `x ↦ (g x, C (x - p))` and `x ↦ (g' x, C (x - p))` gives charts `γ, γ' : W → ℝⁿ` of the
  two level sets over the *same* coordinate `v = C (· - p)` (`levelSetChart` below).

  On a ball `B ∋ 0` contained in the open set where `g = 0 → g' = 0`, the two charts agree:
  for `v ∈ B`, `γ v` is a zero of `g` (so of `g'`), and it lies in the source of the second
  chart, whence `γ v = γ' (C (γ v - p)) = γ' v` by the chart's uniqueness property.  Then
  `{y ∈ U' : g' y = 0, C (y - p) ∈ B}` is an open neighbourhood of `p` on which `g = 0`:
  if `g' y = 0` there, the second chart writes `y = γ' v` with `v = C (y - p) ∈ B`, and
  `g y = g (γ' v) = g (γ v) = 0`.  Combining with the hypothesis gives the equivalence.

  The implicit function theorem is used only at the single point `p` (strict
  differentiability), so the analyticity hypotheses of the statement are not actually needed
  by the proof.
-/

namespace Work.WilE7.Aux

open Filter
open scoped Topology

/-- Level-set chart: if `f` is strictly differentiable at `p`, its differential there is
surjective with kernel `W`, and `C : ℝⁿ →L[ℝ] W` is a projection onto `W`, then the level
surface `{f = 0}` through `p` is, near `p`, the graph over `W` of an explicit chart `γ`,
whose `W`-coordinate is given by `C (· - p)`. -/
theorem levelSetChart {n k : ℕ} (f : (Fin n → ℝ) → (Fin k → ℝ)) (p : Fin n → ℝ)
    (W : Submodule ℝ (Fin n → ℝ)) (C : (Fin n → ℝ) →L[ℝ] W) (hC : ∀ x : W, C x = x)
    (hf : HasStrictFDerivAt f (fderiv ℝ f p) p) (hfp : f p = 0)
    (hker : (fderiv ℝ f p).ker = W) (hsurj : (fderiv ℝ f p).range = ⊤) :
    ∃ (γ : W → (Fin n → ℝ)) (V : Set W) (U : Set (Fin n → ℝ)),
      IsOpen V ∧ IsOpen U ∧ (0 : W) ∈ V ∧ p ∈ U ∧ γ 0 = p ∧ ContinuousAt γ 0 ∧
      (∀ v ∈ V, γ v ∈ U) ∧ (∀ v ∈ V, C (γ v - p) = v) ∧ (∀ v ∈ V, f (γ v) = 0) ∧
      (∀ y ∈ U, f y = 0 → ∃ v ∈ V, γ v = y) := by
  let φ : ImplicitFunctionData ℝ (Fin n → ℝ) (Fin k → ℝ) W :=
    { leftFun := f
      leftDeriv := fderiv ℝ f p
      rightFun := fun x => C (x - p)
      rightDeriv := C
      pt := p
      hasStrictFDerivAt_leftFun := hf
      hasStrictFDerivAt_rightFun :=
        C.hasStrictFDerivAt.comp p ((hasStrictFDerivAt_id p).sub_const p)
      range_leftDeriv := hsurj
      range_rightDeriv := LinearMap.range_eq_of_proj hC
      isCompl_ker := hker.symm ▸ LinearMap.isCompl_of_proj hC }
  have hleft : φ.leftFun = f := rfl
  have hright : ∀ x, φ.rightFun x = C (x - p) := fun x => rfl
  let γ : W → (Fin n → ℝ) := fun v => φ.toOpenPartialHomeomorph.symm ((0 : Fin k → ℝ), v)
  let V : Set W := {v | ((0 : Fin k → ℝ), v) ∈ φ.toOpenPartialHomeomorph.target}
  let U : Set (Fin n → ℝ) := φ.toOpenPartialHomeomorph.source
  have hptsrc : p ∈ φ.toOpenPartialHomeomorph.source :=
    φ.pt_mem_toOpenPartialHomeomorph_source
  have hpimg : φ.toOpenPartialHomeomorph p = ((0 : Fin k → ℝ), (0 : W)) := by
    rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
    simp [hleft, hright, hfp]
  have h00 : ((0 : Fin k → ℝ), (0 : W)) ∈ φ.toOpenPartialHomeomorph.target := by
    have h := φ.toOpenPartialHomeomorph.map_source hptsrc
    rwa [hpimg] at h
  have hγcont : ContinuousAt γ 0 := by
    have h1 : ContinuousAt (⇑φ.toOpenPartialHomeomorph.symm) ((0 : Fin k → ℝ), (0 : W)) :=
      φ.toOpenPartialHomeomorph.continuousAt_symm h00
    have h2 : ContinuousAt (fun v : W => ((0 : Fin k → ℝ), v)) 0 :=
      continuousAt_const.prodMk continuousAt_id
    simpa [γ, Function.comp_def] using h1.comp h2
  refine ⟨γ, V, U, ?_, ?_, ?_, ?_, ?_, hγcont, ?_, ?_, ?_, ?_⟩
  · show IsOpen ((fun v : W => ((0 : Fin k → ℝ), v)) ⁻¹' φ.toOpenPartialHomeomorph.target)
    exact φ.toOpenPartialHomeomorph.open_target.preimage
      (continuous_const.prodMk continuous_id)
  · exact φ.toOpenPartialHomeomorph.open_source
  · exact h00
  · exact hptsrc
  · show φ.toOpenPartialHomeomorph.symm ((0 : Fin k → ℝ), (0 : W)) = p
    have h := φ.toOpenPartialHomeomorph.left_inv hptsrc
    rwa [hpimg] at h
  · intro v hv
    exact φ.toOpenPartialHomeomorph.map_target hv
  · intro v hv
    have h := congr_arg Prod.snd (φ.toOpenPartialHomeomorph.right_inv hv)
    simpa [γ, ImplicitFunctionData.toOpenPartialHomeomorph_apply, ImplicitFunctionData.prodFun,
      hleft, hright] using h
  · intro v hv
    have h := congr_arg Prod.fst (φ.toOpenPartialHomeomorph.right_inv hv)
    simpa [γ, ImplicitFunctionData.toOpenPartialHomeomorph_apply, ImplicitFunctionData.prodFun,
      hleft, hright] using h
  · intro y hy hfy
    have hy' : φ.toOpenPartialHomeomorph y = ((0 : Fin k → ℝ), C (y - p)) := by
      rw [ImplicitFunctionData.toOpenPartialHomeomorph_apply]
      simp [hleft, hright, hfy]
    refine ⟨C (y - p), ?_, ?_⟩
    · have h := φ.toOpenPartialHomeomorph.map_source hy
      show ((0 : Fin k → ℝ), C (y - p)) ∈ φ.toOpenPartialHomeomorph.target
      rwa [hy'] at h
    · show φ.toOpenPartialHomeomorph.symm ((0 : Fin k → ℝ), C (y - p)) = y
      rw [← hy']
      exact φ.toOpenPartialHomeomorph.left_inv hy

theorem levelSetEqNearOfKerLe {n k : ℕ} (g g' : (Fin n → ℝ) → (Fin k → ℝ)) (p : Fin n → ℝ)
    (hg : ∀ q, AnalyticAt ℝ g q) (hg' : ∀ q, AnalyticAt ℝ g' q)
    (hgp : g p = 0) (hg'p : g' p = 0)
    (hsurj : (fderiv ℝ g p).range = ⊤) (hsurj' : (fderiv ℝ g' p).range = ⊤)
    (hker : (fderiv ℝ g p).ker ≤ (fderiv ℝ g' p).ker)
    (hvan : ∀ᶠ y in nhds p, g y = 0 → g' y = 0) :
    ∀ᶠ y in nhds p, (g y = 0 ↔ g' y = 0) := by
  -- The two differentials have the same kernel, by dimension count.
  have hfinrank : Module.finrank ℝ (fderiv ℝ g p).ker
      = Module.finrank ℝ (fderiv ℝ g' p).ker := by
    have h1 := LinearMap.finrank_range_add_finrank_ker
      ((fderiv ℝ g p) : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    have h2 := LinearMap.finrank_range_add_finrank_ker
      ((fderiv ℝ g' p) : (Fin n → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    rw [hsurj, finrank_top] at h1
    rw [hsurj', finrank_top] at h2
    simp only [Module.finrank_fin_fun ℝ] at h1 h2
    omega
  have hkerEq : (fderiv ℝ g' p).ker = (fderiv ℝ g p).ker :=
    (Submodule.eq_of_le_of_finrank_eq hker hfinrank).symm
  -- A common projection onto the common kernel, used to chart both level surfaces.
  let W : Submodule ℝ (Fin n → ℝ) := (fderiv ℝ g p).ker
  have hcomp : W.ClosedComplemented := by
    simpa [W] using (fderiv ℝ g p).ker_closedComplemented_of_finiteDimensional_range
  let C : (Fin n → ℝ) →L[ℝ] W := Classical.choose hcomp
  have hC : ∀ x : W, C x = x := Classical.choose_spec hcomp
  obtain ⟨γ, V, U, hVopen, hUopen, h0V, hpU, hγ0, hγcont, hγU, hγC, hγzero, hγsurj⟩ :=
    levelSetChart g p W C hC (hg p).hasStrictFDerivAt hgp rfl hsurj
  obtain ⟨γ', V', U', hV'open, hU'open, h0V', hpU', hγ'0, _hγ'cont, hγ'U, hγ'C, hγ'zero,
    hγ'surj⟩ :=
    levelSetChart g' p W C hC (hg' p).hasStrictFDerivAt hg'p hkerEq hsurj'
  -- The open set where `g = 0` implies `g' = 0`.
  obtain ⟨Oh, hOh, hOh_open, hpOh⟩ := eventually_nhds_iff.mp hvan
  have hA : U' ∩ Oh ∈ 𝓝 p := (hU'open.inter hOh_open).mem_nhds ⟨hpU', hpOh⟩
  have hγpre : γ ⁻¹' (U' ∩ Oh) ∈ 𝓝 (0 : W) :=
    hγcont.preimage_mem_nhds (by rw [hγ0]; exact hA)
  have hBmem : V ∩ V' ∩ γ ⁻¹' (U' ∩ Oh) ∈ 𝓝 (0 : W) :=
    Filter.inter_mem (Filter.inter_mem (hVopen.mem_nhds h0V) (hV'open.mem_nhds h0V')) hγpre
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hBmem
  -- The neighbourhood of `p` on which the two level sets coincide.
  set Õ : Set (Fin n → ℝ) := U' ∩ {y | C (y - p) ∈ Metric.ball (0 : W) ρ} with hÕdef
  have hÕopen : IsOpen Õ := by
    rw [hÕdef]
    exact hU'open.inter (Metric.isOpen_ball.preimage
      (C.continuous.comp (continuous_id.sub continuous_const)))
  have hpÕ : p ∈ Õ := by
    rw [hÕdef]
    refine ⟨hpU', ?_⟩
    show C (p - p) ∈ Metric.ball (0 : W) ρ
    rw [sub_self, map_zero]
    exact Metric.mem_ball_self hρpos
  have hmem : Õ ∈ 𝓝 p := hÕopen.mem_nhds hpÕ
  -- On `Õ`, `g' = 0` forces `g = 0`.
  have hrev : ∀ᶠ y in nhds p, (g' y = 0 → g y = 0) := by
    rw [Filter.eventually_iff]
    refine Filter.mem_of_superset hmem ?_
    intro y hy hy'
    rw [hÕdef] at hy
    have hyU' : y ∈ U' := hy.1
    have hyB : C (y - p) ∈ Metric.ball (0 : W) ρ := hy.2
    obtain ⟨v, hvV', hvy⟩ := hγ'surj y hyU' hy'
    have hvC : v = C (y - p) := by
      rw [← hvy]
      exact (hγ'C v hvV').symm
    have hvB : v ∈ V ∩ V' ∩ γ ⁻¹' (U' ∩ Oh) := hρsub (by rw [hvC]; exact hyB)
    have hvV : v ∈ V := hvB.1.1
    have hvpre : γ v ∈ U' ∩ Oh := hvB.2
    have hg'γv : g' (γ v) = 0 := hOh (γ v) hvpre.2 (hγzero v hvV)
    obtain ⟨v'', hvV'', hv''eq⟩ := hγ'surj (γ v) hvpre.1 hg'γv
    have hv''C : v'' = C (γ v - p) := by
      rw [← hv''eq]
      exact (hγ'C v'' hvV'').symm
    have hv''v : v'' = v := by rw [hv''C, hγC v hvV]
    have hγ'γ : γ' v = γ v := by
      have h1 : γ' v = γ' v'' := by rw [hv''v]
      rw [h1, hv''eq]
    calc g y = g (γ' v) := by rw [hvy]
      _ = g (γ v) := by rw [hγ'γ]
      _ = 0 := hγzero v hvV
  filter_upwards [hvan, hrev] with y h1 h2
  exact ⟨h1, h2⟩

/-- Generalisation of `levelSetEqNearOfKerLe` to possibly different target dimensions
`k` and `k'` (the kernels are then compared by hypothesis `hdim` instead of being forced
to be equal by a common target dimension). -/
theorem levelSetEqNearOfKerLeGeneral {n k k' : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ))
    (g' : (Fin n → ℝ) → (Fin k' → ℝ)) (p : Fin n → ℝ)
    (hg : ∀ q, AnalyticAt ℝ g q) (hg' : ∀ q, AnalyticAt ℝ g' q)
    (hgp : g p = 0) (hg'p : g' p = 0)
    (hsurj : (fderiv ℝ g p).range = ⊤) (hsurj' : (fderiv ℝ g' p).range = ⊤)
    (hker : (fderiv ℝ g p).ker ≤ (fderiv ℝ g' p).ker)
    (hdim : Module.finrank ℝ (fderiv ℝ g p).ker
      = Module.finrank ℝ (fderiv ℝ g' p).ker)
    (hvan : ∀ᶠ y in nhds p, g y = 0 → g' y = 0) :
    ∀ᶠ y in nhds p, (g y = 0 ↔ g' y = 0) := by
  have hkerEq : (fderiv ℝ g' p).ker = (fderiv ℝ g p).ker :=
    (Submodule.eq_of_le_of_finrank_eq hker hdim).symm
  let W : Submodule ℝ (Fin n → ℝ) := (fderiv ℝ g p).ker
  have hcomp : W.ClosedComplemented := by
    simpa [W] using (fderiv ℝ g p).ker_closedComplemented_of_finiteDimensional_range
  let C : (Fin n → ℝ) →L[ℝ] W := Classical.choose hcomp
  have hC : ∀ x : W, C x = x := Classical.choose_spec hcomp
  obtain ⟨γ, V, U, hVopen, hUopen, h0V, hpU, hγ0, hγcont, hγU, hγC, hγzero, hγsurj⟩ :=
    levelSetChart g p W C hC (hg p).hasStrictFDerivAt hgp rfl hsurj
  obtain ⟨γ', V', U', hV'open, hU'open, h0V', hpU', hγ'0, _hγ'cont, hγ'U, hγ'C, hγ'zero,
    hγ'surj⟩ :=
    levelSetChart g' p W C hC (hg' p).hasStrictFDerivAt hg'p hkerEq hsurj'
  obtain ⟨Oh, hOh, hOh_open, hpOh⟩ := eventually_nhds_iff.mp hvan
  have hA : U' ∩ Oh ∈ 𝓝 p := (hU'open.inter hOh_open).mem_nhds ⟨hpU', hpOh⟩
  have hγpre : γ ⁻¹' (U' ∩ Oh) ∈ 𝓝 (0 : W) :=
    hγcont.preimage_mem_nhds (by rw [hγ0]; exact hA)
  have hBmem : V ∩ V' ∩ γ ⁻¹' (U' ∩ Oh) ∈ 𝓝 (0 : W) :=
    Filter.inter_mem (Filter.inter_mem (hVopen.mem_nhds h0V) (hV'open.mem_nhds h0V')) hγpre
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hBmem
  set Õ : Set (Fin n → ℝ) := U' ∩ {y | C (y - p) ∈ Metric.ball (0 : W) ρ} with hÕdef
  have hÕopen : IsOpen Õ := by
    rw [hÕdef]
    exact hU'open.inter (Metric.isOpen_ball.preimage
      (C.continuous.comp (continuous_id.sub continuous_const)))
  have hpÕ : p ∈ Õ := by
    rw [hÕdef]
    refine ⟨hpU', ?_⟩
    show C (p - p) ∈ Metric.ball (0 : W) ρ
    rw [sub_self, map_zero]
    exact Metric.mem_ball_self hρpos
  have hmem : Õ ∈ 𝓝 p := hÕopen.mem_nhds hpÕ
  have hrev : ∀ᶠ y in nhds p, (g' y = 0 → g y = 0) := by
    rw [Filter.eventually_iff]
    refine Filter.mem_of_superset hmem ?_
    intro y hy hy'
    rw [hÕdef] at hy
    have hyU' : y ∈ U' := hy.1
    have hyB : C (y - p) ∈ Metric.ball (0 : W) ρ := hy.2
    obtain ⟨v, hvV', hvy⟩ := hγ'surj y hyU' hy'
    have hvC : v = C (y - p) := by
      rw [← hvy]
      exact (hγ'C v hvV').symm
    have hvB : v ∈ V ∩ V' ∩ γ ⁻¹' (U' ∩ Oh) := hρsub (by rw [hvC]; exact hyB)
    have hvV : v ∈ V := hvB.1.1
    have hvpre : γ v ∈ U' ∩ Oh := hvB.2
    have hg'γv : g' (γ v) = 0 := hOh (γ v) hvpre.2 (hγzero v hvV)
    obtain ⟨v'', hvV'', hv''eq⟩ := hγ'surj (γ v) hvpre.1 hg'γv
    have hv''C : v'' = C (γ v - p) := by
      rw [← hv''eq]
      exact (hγ'C v'' hvV'').symm
    have hv''v : v'' = v := by rw [hv''C, hγC v hvV]
    have hγ'γ : γ' v = γ v := by
      have h1 : γ' v = γ' v'' := by rw [hv''v]
      rw [h1, hv''eq]
    calc g y = g (γ' v) := by rw [hvy]
      _ = g (γ v) := by rw [hγ'γ]
      _ = 0 := hγzero v hvV
  filter_upwards [hvan, hrev] with y h1 h2
  exact ⟨h1, h2⟩

/-- The reverse form: if the kernels are nested the other way round and `g'` vanishes on the
level set of `g` near `p`, then `g` vanishes on the level set of `g'` near `p`.
This is the statement needed when the nesting direction of the two level sets is swapped. -/
theorem levelSet_eq_near_of_kerLe {n k k' : ℕ} (g : (Fin n → ℝ) → (Fin k → ℝ))
    (g' : (Fin n → ℝ) → (Fin k' → ℝ)) (p : Fin n → ℝ)
    (hg : ∀ q, AnalyticAt ℝ g q) (hg' : ∀ q, AnalyticAt ℝ g' q)
    (hgp : g p = 0) (hg'p : g' p = 0)
    (hsurj : (fderiv ℝ g p).range = ⊤) (hsurj' : (fderiv ℝ g' p).range = ⊤)
    (hker : (fderiv ℝ g' p).ker ≤ (fderiv ℝ g p).ker)
    (hdim : Module.finrank ℝ (fderiv ℝ g' p).ker
      = Module.finrank ℝ (fderiv ℝ g p).ker)
    (hvan : ∀ᶠ y in nhds p, g' y = 0 → g y = 0) :
    ∀ᶠ y in nhds p, g y = 0 → g' y = 0 :=
  (levelSetEqNearOfKerLeGeneral g' g p hg' hg hg'p hgp hsurj' hsurj hker hdim hvan).mono
    fun _ h => h.mpr

end Work.WilE7.Aux
