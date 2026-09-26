import Mathlib
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.BoxGen
import Submission.Work.Drive.Mono.gammaArcs_exist
import Submission.Work.Drive.Mono.ae_slabBoxCrossReg

/-!
# `FaceCrossReg` at the level `s`, from `BoxGen ψ c σ s`

`Work.Drive.Mono.BoxGenE` records the pair crossing regularity `FaceCrossReg` as *one half of an
almost-everywhere statement in `u`*, and `Work.Drive.Mono.boxGenE_pairSard` proves only the joint
version `∀ᵐ s, ∀ᵐ u, FaceCrossReg ψ c σ s u`.  The junction route, however, **fixes the box level
`s` in advance** (it is chosen by `Work.BoxShrink.exists_level_of_ae_count` inside a conull set of
levels) and then needs the regularity in `u` *at that fixed `s`*.  This file supplies exactly that:

> if `s` is a level at which every signed face function has `± s` as a regular value
> (the first clause of `Work.Drive.Mono.BoxGen`, i.e. the face regularity, which
> `Work.Drive.Mono.ae_boxGen` provides at almost every level), then for almost every cutting level
> `u` the face planes `i = 0, 1` cross the flat plane `{y (σ 2) = c (σ 2) + u}` transversally on
> the surface: `Work.Drive.Mono.ae_faceCrossReg_of_boxGen`.

Note the quantifier order: the null set of bad `u` **depends on `s`** – this is a fixed-`s`
statement, not the a.e.-in-`(s,u)` statement of `boxGenE_pairSard`.

## Proof

Fix `i ≠ 2` and a sign `ε = ± 1`, and let `H q = (par ψ q) (σ i)` and `G q = (par ψ q) (σ 2)` be
the two face coordinates.  At a parameter `p` with `H p = c (σ i) + ε · boxSide i · s` the pair
`(G, H)` has **non-vanishing first row**: the face regularity clause of `BoxGen` says that
`ε · s` is a regular value of the signed face `(y (σ i) - c (σ i)) / boxSide i`, and the chain rule
(`fderiv_pullback_signedFace_eq`) identifies the derivative of its pull-back with
`(boxSide i)⁻¹ • dH`.

Consequently, at such a `p` the pair `(G, H)` fails to be invertible **iff** `dG p` is a multiple of
`dH p` (elementary linear algebra of `ℝ × ℝ`: a non-invertible endomorphism whose first row does not
vanish has its second row proportional to the first), which is exactly the membership condition of
`Work.Drive.Mono.SlabFaceCritVals ψ c σ s v i ε` for `v = e_{σ 2}` — i.e. `u` is a *restricted
critical value* of `G` on the face `{H = c (σ i) + ε boxSide i s}`.  Those are null at every fixed
level (`Work.Drive.Mono.volume_slabFaceCritVals_eq_zero`, one-dimensional Sard at a prescribed
level), and the pinned coordinate `c (σ 2) + u` is (affine, hence) an a.e.-avoiding translate of
them (`Work.Drive.Mono.ae_avoid_slabFaceCritVals`).
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-! ### The `σ 2`-coordinate functional -/

/-- The vector of `ℝ³` whose inner product with `y` is the coordinate `y (σ 2)`. -/
private def vertVec (σ : Equiv.Perm (Fin 3)) : R3 := EuclideanSpace.single (σ 2) 1

/-- The defining property of `vertVec`. -/
private theorem inner_vertVec (σ : Equiv.Perm (Fin 3)) (y : R3) :
    inner ℝ (vertVec σ) y = y (σ 2) := by
  rw [vertVec, EuclideanSpace.inner_single_left]
  simp

/-! ### The chain rule for a signed face -/

/-- The pulled-back signed face is `(boxSide i)⁻¹` times the shifted pulled-back coordinate
function, so its derivative is `(boxSide i)⁻¹` times the derivative of that coordinate.  (The
same computation appears, `private`, in `Submission/Work/Smooth/BoxGeneric/FaceRegular`.) -/
private theorem fderiv_pullback_signedFace_eq (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (p : ℝ × ℝ) :
    fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.signedFace c σ i)) p =
      (Submission.boxSide i)⁻¹ •
        fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i))) p := by
  have hfun : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.signedFace c σ i)
      = fun q : ℝ × ℝ =>
          (Submission.boxSide i)⁻¹ *
            (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i)) q - c (σ i)) := by
    funext q
    rw [Work.Smooth.BoxGeneric.pullback_signedFace_eq, div_eq_mul_inv, mul_comm]
  rw [hfun]
  have hdiff : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i)) q - c (σ i)) p :=
    (((Work.Smooth.Morse.pullback_contDiff ψ (g := fun y : R3 => y (σ i))
        (by fun_prop)).differentiable (by simp)).sub_const (c (σ i))).differentiableAt
  rw [fderiv_const_mul hdiff, fderiv_sub_const]

/-- **The face regularity, in coordinate form.**  If `ε * s` is a regular value of the signed face
`signedFace c σ i` and `par ψ p` lies on the face `{y (σ i) = c (σ i) + ε boxSide i * s}`, then the
derivative of the pulled-back coordinate `q ↦ (par ψ q) (σ i)` does not vanish at `p`. -/
private theorem fderiv_par_coord_ne_zero {ψ : Submission.Diffeo} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {s : ℝ} {i : Fin 3} {ε : ℝ}
    (hreg : Work.Smooth.Morse.IsRegularValue ψ (Work.Smooth.BoxGeneric.signedFace c σ i) (ε * s))
    {p : ℝ × ℝ}
    (hp : (Work.BoxShrink.Pinch.par ψ p) (σ i) = c (σ i) + ε * Submission.boxSide i * s) :
    fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p ≠ 0 := by
  have hb : Submission.boxSide i ≠ 0 := ne_of_gt (Submission.boxSide_pos i)
  have hpc : Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i)) p
      = c (σ i) + ε * Submission.boxSide i * s := hp
  have hval : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.signedFace c σ i) p = ε * s := by
    rw [Work.Smooth.BoxGeneric.pullback_signedFace_eq, hpc]
    rw [show c (σ i) + ε * Submission.boxSide i * s - c (σ i) = (ε * s) * Submission.boxSide i
      from by ring]
    exact mul_div_cancel_right₀ (ε * s) hb
  have hne := (Work.Smooth.Morse.isRegularValue_iff ψ _ _).mp hreg p hval
  intro hzero
  apply hne
  rw [fderiv_pullback_signedFace_eq]
  rw [show fderiv ℝ (Work.Smooth.Morse.pullback ψ (fun y : R3 => y (σ i))) p
      = fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p from rfl, hzero]
  simp

/-! ### Elementary linear algebra of `ℝ × ℝ` -/

/-- An endomorphism of `ℝ × ℝ` that is injective is invertible. -/
private lemma fcr_isInvertible_of_injective {T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (h : Function.Injective T) : T.IsInvertible := by
  let e : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) := LinearEquiv.ofInjectiveEndo T.toLinearMap h
  have he : ⇑e = T := LinearEquiv.coe_ofInjectiveEndo T.toLinearMap h
  refine ⟨e.toContinuousLinearEquiv, ContinuousLinearMap.ext ?_⟩
  intro x
  simp [he]

/-- An endomorphism of `ℝ × ℝ` that is surjective is invertible. -/
private lemma fcr_isInvertible_of_surjective {T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (h : Function.Surjective T) : T.IsInvertible :=
  fcr_isInvertible_of_injective (LinearMap.injective_iff_surjective.mpr h)

/-- A non-invertible endomorphism of `ℝ × ℝ` whose first row does not vanish has its second row
proportional to the first. -/
private lemma fcr_exists_smul_snd_of_not_isInvertible {T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)}
    (hT : ¬ T.IsInvertible) (h1 : ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T ≠ 0) :
    ∃ a : ℝ, ContinuousLinearMap.snd ℝ ℝ ℝ ∘L T = a • (ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T) := by
  have hsurj : ¬ Function.Surjective T := fun hs => hT (fcr_isInvertible_of_surjective hs)
  have hrange : LinearMap.range T.toLinearMap < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hsurj
    intro y
    have : y ∈ LinearMap.range T.toLinearMap := by rw [htop]; trivial
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩
  obtain ⟨L, hLne, hL⟩ :=
    Submodule.exists_le_ker_of_lt_top (LinearMap.range T.toLinearMap) hrange
  set α : ℝ := L ((1 : ℝ), 0) with hα
  set β : ℝ := L ((0 : ℝ), 1) with hβ
  have hLapply : ∀ v : ℝ × ℝ, L v = α * v.1 + β * v.2 := by
    rintro ⟨x, y⟩
    have hxy : ((x, y) : ℝ × ℝ) = x • ((1 : ℝ), 0) + y • ((0 : ℝ), 1) := by ext <;> simp
    calc L (x, y) = L (x • ((1 : ℝ), 0) + y • ((0 : ℝ), 1)) := by rw [hxy]
      _ = α * x + β * y := by rw [map_add, map_smul, map_smul, hα, hβ]; ring
  have hzero : ∀ v : ℝ × ℝ, L (T v) = 0 := fun v => hL (LinearMap.mem_range.mpr ⟨v, rfl⟩)
  have hcomb : ∀ v : ℝ × ℝ, α * ((ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T) v)
      + β * ((ContinuousLinearMap.snd ℝ ℝ ℝ ∘L T) v) = 0 := by
    intro v
    have h := hzero v
    rw [hLapply (T v)] at h
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd'] using h
  by_cases hβ0 : β = 0
  · exfalso
    have hα0 : α ≠ 0 := by
      intro hαz
      apply hLne
      refine LinearMap.ext (fun v => ?_)
      rw [hLapply v, hαz, hβ0]
      simp
    have hfst0 : ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T = 0 := by
      refine ContinuousLinearMap.ext (fun v => ?_)
      have h := hcomb v
      rw [hβ0] at h
      simp only [zero_mul, add_zero] at h
      simpa using (mul_eq_zero.mp h).resolve_left hα0
    exact h1 hfst0
  · refine ⟨-(α / β), ?_⟩
    refine ContinuousLinearMap.ext (fun v => ?_)
    have h := hcomb v
    have hβne : β ≠ 0 := hβ0
    have key : ((ContinuousLinearMap.snd ℝ ℝ ℝ ∘L T) v)
        = -(α * ((ContinuousLinearMap.fst ℝ ℝ ℝ ∘L T) v)) / β := by
      rw [eq_div_iff hβne]
      linarith
    rw [key, smul_apply, smul_eq_mul]
    ring

/-! ### Smoothness of the face coordinates -/

/-- The pulled-back coordinates of `par ψ` are `C¹`. -/
private theorem contDiff_parCoord (ψ : Submission.Diffeo) (j : Fin 3) :
    ContDiff ℝ 1 (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) j) := by
  have h : (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) j)
      = Work.Smooth.Morse.pullback ψ (fun y : R3 => y j) := rfl
  rw [h]
  exact Work.Smooth.Morse.pullback_contDiff_one ψ
    ((PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : R3 →L[ℝ] ℝ).contDiff)

/-! ### The main statement -/

/-- **The pair crossing regularity at almost every cutting level, at a fixed box level `s`.**

If `s` is a level of `BoxGen` for the centre `c` and permutation `σ` — in particular, if `± s` are
regular values of every signed face function — then for almost every cutting level `u` the face
planes `i = 0, 1` cross the flat plane `{y (σ 2) = c (σ 2) + u}` transversally on the surface
(`Work.Drive.Mono.FaceCrossReg ψ c σ s u`).

The null set of exceptional `u` depends on `s`. -/
theorem ae_faceCrossReg_of_boxGen
    (ψ : Submission.Diffeo) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (s : ℝ) (hs : 0 < s)
    (hBG : Work.Drive.Mono.BoxGen ψ c σ s) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Drive.Mono.FaceCrossReg ψ c σ s u := by
  classical
  -- Every face `i ≠ 2` and sign `ε = ±1` contributes a null set of bad cutting levels.
  have hkey : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ i : Fin 3, i ≠ 2 → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
        c (σ 2) + u ∉ SlabFaceCritVals ψ c σ s (vertVec σ) i ε := by
    refine MeasureTheory.ae_all_iff.mpr (fun i => ?_)
    by_cases hi : i = 2
    · filter_upwards with u hne
      exact (hne hi).elim
    · have h1 := ae_avoid_slabFaceCritVals ψ c σ s (vertVec σ) i 1 (c (σ 2))
      have h2 := ae_avoid_slabFaceCritVals ψ c σ s (vertVec σ) i (-1) (c (σ 2))
      filter_upwards [h1, h2] with u hu1 hu2 hne ε hε
      rcases hε with hε | hε
      · rw [hε]; simpa using hu1 1 (Or.inl rfl)
      · rw [hε]; simpa using hu2 1 (Or.inl rfl)
  filter_upwards [hkey] with u hu
  intro i hi ε hε p hp1 hp2
  -- Suppose the pair derivative is not invertible at such a crossing point `p`.
  by_contra hnot
  have hd1 : DifferentiableAt ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p :=
    ((contDiff_parCoord ψ (σ i)).differentiable (by norm_num)).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ 2)) p :=
    ((contDiff_parCoord ψ (σ 2)).differentiable (by norm_num)).differentiableAt
  have hfd : fderiv ℝ (fun q : ℝ × ℝ => ((Work.BoxShrink.Pinch.par ψ q) (σ i),
        (Work.BoxShrink.Pinch.par ψ q) (σ 2))) p
      = (fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p).prod
        (fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ 2)) p) :=
    DifferentiableAt.fderiv_prodMk hd1 hd2
  -- The first row is the (non-vanishing) derivative of the face coordinate.
  have hfst : ContinuousLinearMap.fst ℝ ℝ ℝ ∘L
      (fderiv ℝ (fun q : ℝ × ℝ => ((Work.BoxShrink.Pinch.par ψ q) (σ i),
        (Work.BoxShrink.Pinch.par ψ q) (σ 2))) p) ≠ 0 := by
    rw [hfd, ContinuousLinearMap.fst_comp_prod]
    exact fderiv_par_coord_ne_zero (hBG.1 i ε hε) hp1
  obtain ⟨b, hb⟩ := fcr_exists_smul_snd_of_not_isInvertible hnot hfst
  have hb' : fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ 2)) p
      = b • fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p := by
    rw [hfd, ContinuousLinearMap.snd_comp_prod, ContinuousLinearMap.fst_comp_prod] at hb
    exact hb
  -- Hence `u` is a restricted critical value of the `σ 2`-coordinate on the face.
  have hvfun : (fun q : ℝ × ℝ => inner ℝ (vertVec σ) (Work.BoxShrink.Pinch.par ψ q))
      = fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ 2) := by
    funext q; exact inner_vertVec σ (Work.BoxShrink.Pinch.par ψ q)
  have hmem : (Work.BoxShrink.Pinch.par ψ p) (σ 2) ∈
      SlabFaceCritVals ψ c σ s (vertVec σ) i ε := by
    refine ⟨p, inner_vertVec σ (Work.BoxShrink.Pinch.par ψ p), hp1,
      fderiv_par_coord_ne_zero (hBG.1 i ε hε) hp1, b, ?_⟩
    rw [hvfun, hb']
  exact hu i hi ε hε (by rw [← hp2]; exact hmem)

end

end Work.Drive.Mono
