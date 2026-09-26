import Mathlib
import Submission.Work.Smooth.BoxGeneric.Sard.exists_isOpen_volume_image_critical_null

/-!
# Sard's theorem for the *restricted* critical set on a level curve of `h`

The main result of this file is

`Work.Smooth.BoxGeneric.Sard.exists_isOpen_volume_image_restrictedCritical_null`:

for `C¹` maps `G h : ℝ × ℝ → ℝ` and a point `p` with `h p = 0` and `fderiv ℝ h p ≠ 0`,
there is an open neighbourhood `U` of `p` such that the image under `G` of the set

`{q | h q = 0 ∧ ∃ a, fderiv ℝ G q = a • fderiv ℝ h q}`

inside `U` is Lebesgue null.  Equivalently, the critical values of the restriction of `G`
to the level curve `{h = 0}` are null.

The proof follows exactly the same route as in `exists_isOpen_volume_image_critical_null`
(implicit function theorem to parametrise the level curve, then Sard in dimension one),
except that on the critical set we use the chain rule *together with* the fact that
`h` vanishes along the level curve to see that the derivative of `t ↦ G (γ t)` vanishes:
writing `fderiv ℝ G (γ t) = a • fderiv ℝ h (γ t)` and using that
`fderiv ℝ h (γ t) ∘SL fderiv ℝ γ t = fderiv ℝ (h ∘ γ) t = 0`.
-/

namespace Work.Smooth.BoxGeneric.Sard

noncomputable section

open MeasureTheory Set
open scoped Topology
open Filter

/-- A nonzero continuous linear map `ℝ →L[ℝ] ℝ` is a continuous linear equivalence.  (It is
multiplication by the real number `g 1`, which is nonzero.) -/
private theorem isInvertible_of_ne_zero_restricted {g : ℝ →L[ℝ] ℝ} (hg : g ≠ 0) :
    g.IsInvertible := by
  have hg_apply : ∀ x : ℝ, g x = x * g 1 := fun x => by
    simpa [smul_eq_mul] using map_smul g x (1 : ℝ)
  have hg1 : g 1 ≠ 0 := by
    intro h
    apply hg
    apply ContinuousLinearMap.ext
    intro x
    rw [hg_apply x, h, mul_zero]
    simp
  refine ContinuousLinearMap.IsInvertible.of_inverse (f := g)
    (g := ContinuousLinearMap.toSpanSingleton ℝ (g 1)⁻¹) ?_ ?_
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [hg_apply, mul_assoc, inv_mul_cancel₀ hg1, mul_one]
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [hg_apply, mul_assoc, mul_inv_cancel₀ hg1, mul_one]

/-- **Sard on a level curve for the restricted critical set, second partial nonzero.**

If the derivative of `h` in the second coordinate at `p` does not vanish, then `{h = 0}` is
locally the graph of a `C¹` function of the first coordinate, and the restricted critical
values of `G` on the level curve are null. -/
private theorem exists_isOpen_volume_image_restrictedCritical_null_of_snd
    {G h : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hG : ContDiff ℝ 1 G) (hh : ContDiff ℝ 1 h) (hp : h p = 0)
    (hg : (fderiv ℝ h p) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ ≠ 0) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ p ∈ U ∧
      MeasureTheory.volume (G '' ({q : ℝ × ℝ | h q = 0 ∧
        ∃ a : ℝ, fderiv ℝ G q = a • fderiv ℝ h q} ∩ U)) = 0 := by
  classical
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hne : (1 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞) := by norm_num
  -- The implicit function theorem, solving for the second coordinate.
  have hsd : HasStrictFDerivAt h (fderiv ℝ h p) p := hh.contDiffAt.hasStrictFDerivAt hn
  have hinv : ((fderiv ℝ h p) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible :=
    isInvertible_of_ne_zero_restricted hg
  let φ : ImplicitFunctionData ℝ (ℝ × ℝ) ℝ ℝ := hsd.implicitFunctionDataOfProdDomain hinv
  have hpt : φ.pt = p := by simp [φ]
  let f' : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv
      φ.range_rightDeriv φ.isCompl_ker
  have hderiv : HasFDerivAt φ.prodFun (f' : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    have h := φ.hasStrictFDerivAt.hasFDerivAt
    rw [hpt] at h
    simpa [f'] using h
  have hφprod : φ.prodFun = fun q : ℝ × ℝ => (h q, q.1) := by
    funext q; simp [φ, ImplicitFunctionData.prodFun]
  have hcont : ContDiffAt ℝ 1 φ.prodFun p := by rw [hφprod]; fun_prop
  have hpp : φ.prodFun p = (0, p.1) := by rw [hφprod]; simp [hp]
  -- The local parametrisation of the level set: an inverse of `q ↦ (h q, q.1)`.
  let hssd := hcont.hasStrictFDerivAt' hderiv hn
  let LI : ℝ × ℝ → ℝ × ℝ := hssd.localInverse φ.prodFun f' p
  have hLIeq : LI = hcont.localInverse hderiv hn := rfl
  have hleft0 : ∀ᶠ x in 𝓝 p, LI (φ.prodFun x) = x := hssd.eventually_left_inverse
  have hright0 : ∀ᶠ y in 𝓝 (φ.prodFun p), φ.prodFun (LI y) = y :=
    hssd.eventually_right_inverse
  let γ : ℝ → ℝ × ℝ := fun t => LI (0, t)
  have hγeq : γ = fun t => hcont.localInverse hderiv hn (0, t) := rfl
  have hγcont' : ContDiffAt ℝ 1 (fun t => hcont.localInverse hderiv hn (0, t)) p.1 := by
    have h3 := hcont.to_localInverse hderiv hn
    rw [hpp] at h3
    exact h3.comp p.1 ((ContinuousLinearMap.inr ℝ ℝ ℝ).contDiff.contDiffAt)
  have hγcont : ContDiffAt ℝ 1 γ p.1 := hγeq.symm ▸ hγcont'
  -- Points of the level set near `p` are `γ` of their first coordinate.
  have hleft : ∀ᶠ q in 𝓝 p, h q = 0 → γ q.1 = q := by
    filter_upwards [hleft0] with x hx hx0
    have harg : ((0 : ℝ), x.1) = φ.prodFun x := by rw [hφprod]; simp [hx0]
    show LI (0, x.1) = x
    rw [harg]
    exact hx
  obtain ⟨V₁, hV₁sub, hV₁open, hpV₁⟩ := eventually_nhds_iff.mp hleft
  have hγdiff : ∀ᶠ t in 𝓝 p.1, DifferentiableAt ℝ γ t := by
    filter_upwards [hγcont.eventually hne] with t ht
    exact ht.differentiableAt hn
  -- `h` vanishes along `γ`, near `p.1`.
  have hγzero : ∀ᶠ t in 𝓝 p.1, h (γ t) = 0 := by
    have hTcont : Continuous (fun t : ℝ => ((0 : ℝ), t)) := by fun_prop
    have hT : Tendsto (fun t : ℝ => ((0 : ℝ), t)) (𝓝 p.1) (𝓝 (φ.prodFun p)) := by
      rw [hpp]
      exact hTcont.continuousAt
    filter_upwards [hT.eventually hright0] with t ht
    have ht' : (φ.prodFun (LI (0, t))).1 = 0 := by
      rw [ht]
    rw [hφprod] at ht'
    simpa [γ] using ht'
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.eventually_nhds_iff.mp hγdiff
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.eventually_nhds_iff.mp hγzero
  -- The neighbourhood of `p` on which we work, and the arc `γ` restricted to it.
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδpos : 0 < δ := lt_min hδ₁ hδ₂
  set I : Set ℝ := Metric.ball p.1 δ with hI
  have hIopen : IsOpen I := Metric.isOpen_ball
  have hpI : p.1 ∈ I := Metric.mem_ball_self hδpos
  have hγIdiff : ∀ t ∈ I, DifferentiableAt ℝ γ t := fun t ht =>
    hδ₁' (Metric.ball_subset_ball (min_le_left _ _) ht)
  have hγzeroI : ∀ t ∈ I, h (γ t) = 0 := fun t ht =>
    hδ₂' (Metric.ball_subset_ball (min_le_right _ _) ht)
  set U : Set (ℝ × ℝ) := V₁ ∩ {q : ℝ × ℝ | q.1 ∈ I} with hU
  have hUopen : IsOpen U := hV₁open.inter (hIopen.preimage continuous_fst)
  have hpU : p ∈ U := ⟨hpV₁, hpI⟩
  -- `G` along the arc.
  set Gc : ℝ → ℝ := fun t => G (γ t) with hGc
  set Z : Set ℝ := {t : ℝ | t ∈ I ∧
    ∃ a : ℝ, fderiv ℝ G (γ t) = a • fderiv ℝ h (γ t)} with hZ
  have hinc : G '' ({q : ℝ × ℝ | h q = 0 ∧
      ∃ a : ℝ, fderiv ℝ G q = a • fderiv ℝ h q} ∩ U) ⊆ Gc '' Z := by
    rintro y ⟨q, ⟨⟨hq1, hq2⟩, hq3⟩, rfl⟩
    have hγq : γ q.1 = q := hV₁sub q hq3.1 hq1
    refine ⟨q.1, ⟨hq3.2, ?_⟩, ?_⟩
    · rw [hγq]; exact hq2
    · show G (γ q.1) = G q
      rw [hγq]
  -- On `Z` the function `Gc` is differentiable with derivative `0`.
  have hder : ∀ t ∈ Z, HasFDerivWithinAt Gc (0 : ℝ →L[ℝ] ℝ) Z t := by
    intro t ht
    have h1 : DifferentiableAt ℝ G (γ t) := (hG.differentiable hn).differentiableAt
    have h2 : DifferentiableAt ℝ γ t := hγIdiff t ht.1
    have h1h : DifferentiableAt ℝ h (γ t) := (hh.differentiable hn).differentiableAt
    have h3 : fderiv ℝ Gc t = 0 := by
      have hcompG : fderiv ℝ Gc t = fderiv ℝ G (γ t) ∘SL fderiv ℝ γ t := by
        have hh2 := fderiv_comp (𝕜 := ℝ) t (f := γ) (g := G) h1 h2
        simpa [hGc, Function.comp_def] using hh2
      have hcomph : fderiv ℝ (fun s => h (γ s)) t
          = fderiv ℝ h (γ t) ∘SL fderiv ℝ γ t := by
        have hh2 := fderiv_comp (𝕜 := ℝ) t (f := γ) (g := h) h1h h2
        simpa [Function.comp_def] using hh2
      have hz : ∀ᶠ s in 𝓝 t, h (γ s) = 0 :=
        mem_of_superset (hIopen.mem_nhds ht.1) hγzeroI
      have hzerofd : fderiv ℝ (fun s => h (γ s)) t = 0 := by
        rw [Filter.EventuallyEq.fderiv_eq (f := fun _ : ℝ => (0 : ℝ)) hz]
        simp
      obtain ⟨a, ha⟩ := ht.2
      rw [hcompG, ha, ContinuousLinearMap.smul_comp, ← hcomph, hzerofd, smul_zero]
    have h4 : HasFDerivAt Gc (0 : ℝ →L[ℝ] ℝ) t := by
      have hh3 : HasFDerivAt Gc (fderiv ℝ Gc t) t := (h1.comp t h2).hasFDerivAt
      rw [h3] at hh3
      exact hh3
    exact h4.hasFDerivWithinAt
  have hdet : ∀ t ∈ Z, ((0 : ℝ →L[ℝ] ℝ)).det = 0 := fun t _ => by simp
  -- Sard in dimension one.
  have hZnull : MeasureTheory.volume (Gc '' Z) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := MeasureTheory.volume)
      hder hdet
  exact ⟨U, hUopen, hpU, measure_mono_null hinc hZnull⟩

/-- **Sard's theorem for the restricted critical set on a level curve.**  For `C¹` maps
`G h : ℝ × ℝ → ℝ` and a point `p` with `h p = 0` and `fderiv ℝ h p ≠ 0` there is an open
neighbourhood `U` of `p` such that the image under `G` of the set
`{q | h q = 0 ∧ ∃ a, fderiv ℝ G q = a • fderiv ℝ h q}` inside `U` is Lebesgue null. -/
theorem exists_isOpen_volume_image_restrictedCritical_null {G h : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hG : ContDiff ℝ 1 G) (hh : ContDiff ℝ 1 h) (hp : h p = 0) (hg : fderiv ℝ h p ≠ 0) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ p ∈ U ∧
      MeasureTheory.volume (G '' ({q : ℝ × ℝ | h q = 0 ∧
        ∃ a : ℝ, fderiv ℝ G q = a • fderiv ℝ h q} ∩ U)) = 0 := by
  classical
  by_cases h2 : (fderiv ℝ h p) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ = 0
  · -- The second partial derivative vanishes: reduce to the first one by swapping coordinates.
    let L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
    have hLL : ∀ x : ℝ × ℝ, L (L x) = x := fun x => by
      simp [L, ContinuousLinearEquiv.prodComm]
    set G' : ℝ × ℝ → ℝ := fun q => G (L q) with hG'def
    set h' : ℝ × ℝ → ℝ := fun q => h (L q) with hh'def
    have hG' : ContDiff ℝ 1 G' := by
      rw [hG'def]
      exact hG.comp (ContinuousLinearMap.contDiff (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
    have hh' : ContDiff ℝ 1 h' := by
      rw [hh'def]
      exact hh.comp (ContinuousLinearMap.contDiff (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
    have hp' : h' (L p) = 0 := by simp only [hh'def, hLL p, hp]
    have hfderiv' : fderiv ℝ h' (L p) = fderiv ℝ h p ∘SL (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) := by
      have hLLc : (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (L p) = p := hLL p
      have hd1 : DifferentiableAt ℝ h (L (L p)) :=
        (hh.differentiable (by norm_num)).differentiableAt
      have hd2 : DifferentiableAt ℝ (⇑(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) (L p) :=
        ContinuousLinearMap.differentiableAt _
      have hcomp := fderiv_comp (𝕜 := ℝ) (L p)
        (f := (⇑(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))) (g := h) hd1 hd2
      rw [ContinuousLinearMap.fderiv, hLLc] at hcomp
      simpa [hh'def, Function.comp_def] using hcomp
    have hLir : (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) ∘SL ContinuousLinearMap.inr ℝ ℝ ℝ
        = ContinuousLinearMap.inl ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro x
      simp [L, ContinuousLinearEquiv.prodComm, ContinuousLinearMap.inr_apply]
    have h2' : (fderiv ℝ h p) ∘SL ContinuousLinearMap.inr ℝ ℝ ℝ = 0 := h2
    have hinl : (fderiv ℝ h p) ∘SL ContinuousLinearMap.inl ℝ ℝ ℝ ≠ 0 := by
      intro h0
      apply hg
      apply ContinuousLinearMap.ext
      intro v
      have hv := ContinuousLinearMap.comp_inl_add_comp_inr (fderiv ℝ h p) v
      rw [← hv, h0, h2']
      simp
    have hg' : (fderiv ℝ h' (L p)) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ ≠ 0 := by
      rw [hfderiv', ContinuousLinearMap.comp_assoc, hLir]
      exact hinl
    obtain ⟨U', hU'open, hp'U', hvol'⟩ :=
      exists_isOpen_volume_image_restrictedCritical_null_of_snd hG' hh' hp' hg'
    -- The exchanged derivatives.
    have hfdG : ∀ q, fderiv ℝ G' q
        = fderiv ℝ G (L q) ∘SL (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) := by
      intro q
      have hd1 : DifferentiableAt ℝ G (L q) :=
        (hG.differentiable (by norm_num)).differentiableAt
      have hd2 : DifferentiableAt ℝ (⇑(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) q :=
        ContinuousLinearMap.differentiableAt _
      have hcomp := fderiv_comp (𝕜 := ℝ) q
        (f := (⇑(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))) (g := G) hd1 hd2
      rw [ContinuousLinearMap.fderiv] at hcomp
      simpa [hG'def, Function.comp_def] using hcomp
    have hfdh : ∀ q, fderiv ℝ h' q
        = fderiv ℝ h (L q) ∘SL (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) := by
      intro q
      have hd1 : DifferentiableAt ℝ h (L q) :=
        (hh.differentiable (by norm_num)).differentiableAt
      have hd2 : DifferentiableAt ℝ (⇑(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))) q :=
        ContinuousLinearMap.differentiableAt _
      have hcomp := fderiv_comp (𝕜 := ℝ) q
        (f := (⇑(L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))) (g := h) hd1 hd2
      rw [ContinuousLinearMap.fderiv] at hcomp
      simpa [hh'def, Function.comp_def] using hcomp
    -- Right-cancellation against the (surjective) linear isomorphism `L`.
    have hcancel : ∀ {f g : (ℝ × ℝ) →L[ℝ] ℝ},
        f ∘SL (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
          = g ∘SL (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) → f = g := by
      intro f g hfg
      apply ContinuousLinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := L.surjective v
      have hw := congrArg (fun k : (ℝ × ℝ) →L[ℝ] ℝ => k w) hfg
      simpa [ContinuousLinearMap.comp_apply] using hw
    have hcrit : ∀ q, (∃ a : ℝ, fderiv ℝ G' q = a • fderiv ℝ h' q) ↔
        (∃ a : ℝ, fderiv ℝ G (L q) = a • fderiv ℝ h (L q)) := by
      intro q
      constructor
      · rintro ⟨a, ha⟩
        refine ⟨a, hcancel ?_⟩
        rw [← hfdG q, ContinuousLinearMap.smul_comp, ← hfdh q]
        exact ha
      · rintro ⟨a, ha⟩
        exact ⟨a, by rw [hfdG q, hfdh q, ha, ContinuousLinearMap.smul_comp]⟩
    have hset : G' '' ({q | h' q = 0 ∧ ∃ a : ℝ, fderiv ℝ G' q = a • fderiv ℝ h' q} ∩ U')
        = G '' ({q | h q = 0 ∧ ∃ a : ℝ, fderiv ℝ G q = a • fderiv ℝ h q}
            ∩ (L '' U')) := by
      apply Subset.antisymm
      · rintro y ⟨q, ⟨⟨hq1, hq2⟩, hq3⟩, rfl⟩
        refine ⟨L q, ⟨⟨?_, (hcrit q).mp hq2⟩, q, hq3, rfl⟩, ?_⟩
        · show h (L q) = 0
          simpa only [hh'def] using hq1
        · show G (L q) = G' q
          simp only [hG'def]
      · rintro y ⟨q, ⟨⟨hq1, hq2⟩, u, hu, hLu⟩, rfl⟩
        have hq2' : ∃ a : ℝ, fderiv ℝ G (L u) = a • fderiv ℝ h (L u) := by
          obtain ⟨a, ha⟩ := hq2
          exact ⟨a, by rw [hLu]; exact ha⟩
        refine ⟨u, ⟨⟨?_, (hcrit u).mpr hq2'⟩, hu⟩, ?_⟩
        · show h' u = 0
          change h (L u) = 0
          rw [hLu]
          exact hq1
        · show G' u = G q
          change G (L u) = G q
          rw [hLu]
    refine ⟨L '' U', ContinuousLinearEquiv.isOpenMap L U' hU'open, ⟨L p, hp'U', hLL p⟩, ?_⟩
    rw [← hset]
    exact hvol'
  · exact exists_isOpen_volume_image_restrictedCritical_null_of_snd hG hh hp h2

end

end Work.Smooth.BoxGeneric.Sard
