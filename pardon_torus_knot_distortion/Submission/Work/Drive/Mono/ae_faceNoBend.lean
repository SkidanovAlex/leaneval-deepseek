import Mathlib
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.NoBend
import Submission.Work.Drive.Mono.Band.ae_finite_preimage

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-!
# `FaceNoBend` at almost every cutting level

This file proves `Work.Drive.Mono.ae_faceNoBend` (item G2 of
`Mono/NOTES_LEAD_junctionGen.md` §2).

Fix a diffeomorphism `ψ`, a box centre `c`, a coordinate permutation `σ` and a level `s`, and write
`par ψ` for the parametrisation of the surface.  For the ordered pair `(σ i, σ j)` of coordinates
put

* `Aᵢ = y_{σ i} ∘ par`, `Aⱼ = y_{σ j} ∘ par`;
* `D = faceVertDet ψ σ i j = det [d Aᵢ ; d Aⱼ]`, the *vertical-tangent determinant*: it vanishes
  exactly where the trace `Γ = {Aᵢ = const}` has a vertical tangent;
* `T = faceTangent ψ σ i p = (-∂₂Aᵢ, ∂₁Aᵢ)`, the Hamiltonian tangent field of `Aᵢ`.

`FaceNoBend` asks that at every point of `Γ` whose *flat height* `A₂` is `c (σ 2) + u` and at which
`D = 0`, the vanishing of `D` is double, i.e. `dD_p (T p) = 0`.  The content of the theorem is that
the exceptional levels `u` form a null set.

The argument is the two-dimensional trace analogue of `Work.Drive.Mono.ae_noBendCrossing`
(`Mono/NoBend.lean`), where a *bending* vertical crossing of a knot was isolated because the
orthogonal velocity has a simple zero there:

* at a point where `D = 0` but `dD_p (T p) ≠ 0` the map `Ψ = (Aᵢ, D)` has an **invertible**
  derivative at `p` (its determinant *is* `dD_p (T p)`, `det_prod_entries`), so `p` is *isolated*
  in the fibre `Ψ ⁻¹ {(Aᵢ p, 0)}` by the inverse function theorem
  (`Work.Drive.Mono.Band.injOn_of_isInvertible_fderiv`);
* the bad points therefore form a discrete set, hence a countable one
  (`countable_of_nhds_isolated`), and the heights of a countable set are null
  (`Set.Countable.measure_zero`).
-/

/-! ## Smoothness of the ingredients -/

/-- The `σ k`-coordinate of the parametrised surface is `C^∞`. -/
theorem contDiff_par_coord (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ k)) :=
  ContDiff.continuousLinearMap_comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (σ k))
    (Work.Smooth.Morse.param_contDiff ψ)

/-- **The vertical-tangent determinant is `C¹`**: it is built from the derivatives of the `C^∞`
coordinate functions of the parametrisation. -/
theorem faceVertDet_contDiff_one (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    ContDiff ℝ 1 (Work.Drive.Mono.faceVertDet ψ σ i j) := by
  have hle : (1 : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by decide
  have h10 := (contDiff_par_coord ψ σ i).contDiff_fderiv_apply (m := 1) (hmn := hle)
  have h01 := (contDiff_par_coord ψ σ i).contDiff_fderiv_apply (m := 1) (hmn := hle)
  have g10 := (contDiff_par_coord ψ σ j).contDiff_fderiv_apply (m := 1) (hmn := hle)
  have g01 := (contDiff_par_coord ψ σ j).contDiff_fderiv_apply (m := 1) (hmn := hle)
  have e10 := h10.comp (contDiff_id.prodMk (contDiff_const (c := (1, 0))))
  have e01 := h01.comp (contDiff_id.prodMk (contDiff_const (c := (0, 1))))
  have f10 := g10.comp (contDiff_id.prodMk (contDiff_const (c := (1, 0))))
  have f01 := g01.comp (contDiff_id.prodMk (contDiff_const (c := (0, 1))))
  have hfun : faceVertDet ψ σ i j = fun q : ℝ × ℝ =>
      fderiv ℝ (fun s : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ s) (σ i)) q (1, 0) *
        fderiv ℝ (fun s : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ s) (σ j)) q (0, 1) -
      fderiv ℝ (fun s : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ s) (σ i)) q (0, 1) *
        fderiv ℝ (fun s : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ s) (σ j)) q (1, 0) := rfl
  rw [hfun]
  exact (e10.mul f01).sub (e01.mul f10)

/-- The trace map `q ↦ (y_{σ i} (par ψ q), faceVertDet ψ σ i j q)` is `C¹`. -/
theorem contDiff_facePair (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    ContDiff ℝ 1 (fun q : ℝ × ℝ =>
      ((Work.BoxShrink.Pinch.par ψ q) (σ i), faceVertDet ψ σ i j q)) :=
  ((contDiff_par_coord ψ σ i).of_le (by decide)).prodMk (faceVertDet_contDiff_one ψ σ i j)

/-! ## The `2 × 2` determinant -/

/-- A continuous linear functional on `ℝ × ℝ` is determined by its values on `(1, 0)` and
`(0, 1)`. -/
theorem clm_pair (L : ℝ × ℝ →L[ℝ] ℝ) (c₁ c₂ : ℝ) :
    L (c₁, c₂) = c₁ * L (1, 0) + c₂ * L (0, 1) := by
  have hxy : (c₁, c₂) = c₁ • ((1, 0) : ℝ × ℝ) + c₂ • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [hxy, map_add, map_smul, map_smul]
  simp [smul_eq_mul]

theorem clm_pair_div₁ (a b c d y₁ y₂ : ℝ) (h : a * d - b * c ≠ 0) :
    a * (d / (a * d - b * c) * y₁ - b / (a * d - b * c) * y₂) +
        b * (a / (a * d - b * c) * y₂ - c / (a * d - b * c) * y₁) = y₁ := by
  field_simp [h]; ring

theorem clm_pair_div₂ (a b c d y₁ y₂ : ℝ) (h : a * d - b * c ≠ 0) :
    c * (d / (a * d - b * c) * y₁ - b / (a * d - b * c) * y₂) +
        d * (a / (a * d - b * c) * y₂ - c / (a * d - b * c) * y₁) = y₂ := by
  have h2 : d * a - c * b ≠ 0 := by rw [mul_comm d a, mul_comm c b]; exact h
  field_simp [h, h2]; ring

theorem clm_pair_div₃ (a b c d y₁ y₂ : ℝ) (h : a * d - b * c ≠ 0) :
    d / (a * d - b * c) * (a * y₁ + b * y₂) - b / (a * d - b * c) * (c * y₁ + d * y₂) = y₁ := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div,
    show d * (a * y₁ + b * y₂) - b * (c * y₁ + d * y₂) = (a * d - b * c) * y₁ by ring]
  field_simp [h]

theorem clm_pair_div₄ (a b c d y₁ y₂ : ℝ) (h : a * d - b * c ≠ 0) :
    a / (a * d - b * c) * (c * y₁ + d * y₂) - c / (a * d - b * c) * (a * y₁ + b * y₂) = y₂ := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div,
    show a * (c * y₁ + d * y₂) - c * (a * y₁ + b * y₂) = (a * d - b * c) * y₂ by ring]
  field_simp [h]

/-- **A `2 × 2` matrix with non-zero determinant is invertible.**  For a continuous linear
endomorphism `L` of `ℝ × ℝ` whose determinant `L (1,0) ₀ · L (0,1) ₁ - L (0,1) ₀ · L (1,0) ₁` does
not vanish, we write the inverse down explicitly. -/
theorem det_prod_entries {L : ℝ × ℝ →L[ℝ] ℝ × ℝ}
    (h : (L (1, 0)).1 * (L (0, 1)).2 - (L (0, 1)).1 * (L (1, 0)).2 ≠ 0) : L.IsInvertible := by
  set a : ℝ := (L (1, 0)).1 with ha
  set b : ℝ := (L (0, 1)).1 with hb
  set c : ℝ := (L (1, 0)).2 with hc
  set d : ℝ := (L (0, 1)).2 with hd
  have hΔ : a * d - b * c ≠ 0 := by rw [ha, hb, hc, hd]; exact h
  set g : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (((d / (a * d - b * c)) • ContinuousLinearMap.fst ℝ ℝ ℝ) -
      ((b / (a * d - b * c)) • ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
    (((a / (a * d - b * c)) • ContinuousLinearMap.snd ℝ ℝ ℝ) -
      ((c / (a * d - b * c)) • ContinuousLinearMap.fst ℝ ℝ ℝ)) with hg
  have hL : ∀ x₁ x₂ : ℝ, L (x₁, x₂) = (a * x₁ + b * x₂, c * x₁ + d * x₂) := by
    intro x₁ x₂
    have hxy : (x₁, x₂) = x₁ • ((1, 0) : ℝ × ℝ) + x₂ • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [hxy, map_add, map_smul, map_smul, ha, hb, hc, hd]
    ext <;> simp <;> ring
  have hgval : ∀ y₁ y₂ : ℝ, g (y₁, y₂) =
      ((d / (a * d - b * c)) * y₁ - (b / (a * d - b * c)) * y₂,
       (a / (a * d - b * c)) * y₂ - (c / (a * d - b * c)) * y₁) := by
    intro y₁ y₂
    simp [hg, smul_eq_mul]
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := g) ?_ ?_
  · apply ContinuousLinearMap.ext
    intro y
    obtain ⟨y₁, y₂⟩ := y
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hgval y₁ y₂, hL]
    ext
    · exact clm_pair_div₁ a b c d y₁ y₂ hΔ
    · exact clm_pair_div₂ a b c d y₁ y₂ hΔ
  · apply ContinuousLinearMap.ext
    intro x
    obtain ⟨x₁, x₂⟩ := x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hL, hgval]
    ext
    · exact clm_pair_div₃ a b c d x₁ x₂ hΔ
    · exact clm_pair_div₄ a b c d x₁ x₂ hΔ

/-- **At a bend point the trace map has invertible derivative.**  If the vertical-tangent
determinant vanishes at `p` without being doubly vanishing there — that is,
`d faceVertDet p (faceTangent p) ≠ 0` — then the derivative of `Ψ = (y_{σ i} ∘ par, faceVertDet)`
at `p` is invertible: its determinant is exactly `d faceVertDet p (faceTangent p)`. -/
theorem isInvertible_fderiv_pair_of_bend (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3))
    (i j : Fin 3) (p : ℝ × ℝ)
    (h : fderiv ℝ (faceVertDet ψ σ i j) p (faceTangent ψ σ i p) ≠ 0) :
    (fderiv ℝ (fun q : ℝ × ℝ => ((Work.BoxShrink.Pinch.par ψ q) (σ i),
      faceVertDet ψ σ i j q)) p).IsInvertible := by
  have hAda : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p :=
    ((contDiff_par_coord ψ σ i).differentiable (by decide)).differentiableAt
  have hDda : DifferentiableAt ℝ (faceVertDet ψ σ i j) p :=
    ((faceVertDet_contDiff_one ψ σ i j).differentiable (by decide)).differentiableAt
  have hfderiv : fderiv ℝ (fun q : ℝ × ℝ => ((Work.BoxShrink.Pinch.par ψ q) (σ i),
      faceVertDet ψ σ i j q)) p
      = (fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p).prod
        (fderiv ℝ (faceVertDet ψ σ i j) p) := hAda.fderiv_prodMk hDda
  rw [hfderiv]
  apply det_prod_entries
  have key : (fderiv ℝ (faceVertDet ψ σ i j) p) (faceTangent ψ σ i p)
      = (fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p) (1, 0) *
          (fderiv ℝ (faceVertDet ψ σ i j) p) (0, 1) -
        (fderiv ℝ (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ i)) p) (0, 1) *
          (fderiv ℝ (faceVertDet ψ σ i j) p) (1, 0) := by
    simp only [faceTangent]
    rw [clm_pair]
    ring
  rw [key] at h
  simpa only [ContinuousLinearMap.prod_apply] using h

/-! ## Countability of a set with isolated points -/

/-- A set all of whose points are isolated is countable, in a second countable space. -/
theorem countable_of_nhds_isolated {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    {S : Set X} (h : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ∩ S ⊆ {x}) : S.Countable := by
  classical
  choose U hU hxU hUS using h
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : ↥S => U x.1 x.2)
    (fun x => hU x.1 x.2)
  have hSsub : S ⊆ ⋃ y : ↥T, (S ∩ U y.1.1 y.1.2) := by
    intro x hxS
    have hxU : x ∈ U x hxS := hxU x hxS
    have : x ∈ ⋃ x : ↥S, U x.1 x.2 := Set.mem_iUnion.mpr ⟨⟨x, hxS⟩, hxU⟩
    rw [← hT] at this
    obtain ⟨y, hyT, hxy⟩ := Set.mem_iUnion₂.mp this
    exact Set.mem_iUnion.mpr ⟨⟨y, hyT⟩, hxS, hxy⟩
  refine Countable.mono hSsub ?_
  have hTsub : Countable ↥T := hTc.to_subtype
  exact Set.countable_iUnion (fun y : ↥T => Set.Subsingleton.countable fun a ha b hb => by
    have ha' : a ∈ ({y.1.1} : Set X) := hUS y.1.1 y.1.2 ⟨ha.2, ha.1⟩
    have hb' : b ∈ ({y.1.1} : Set X) := hUS y.1.1 y.1.2 ⟨hb.2, hb.1⟩
    rw [Set.mem_singleton_iff] at ha' hb'
    rw [ha', hb'])

/-! ## The bad parameters, and the a.e. statement -/

/-- The sign attached to a Boolean sign choice. -/
def nbFaceSgn (b : Bool) : ℝ := if b then 1 else -1

/-- **The bad parameters**: for a sign choice `ω = (i, j, b)` these are the parameters `p` at which
the trace `Γ_{σ i} = {y (σ i) ∘ par = c (σ i) + ε boxSide i s}` is met, the vertical-tangent
determinant `faceVertDet ψ σ i j` vanishes there, and the vanishing is **not** double. -/
def faceBadParams (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ)
    (ω : Fin 3 × Fin 3 × Bool) : Set (ℝ × ℝ) :=
  {p | (Work.BoxShrink.Pinch.par ψ p) (σ ω.1) =
        c (σ ω.1) + nbFaceSgn ω.2.2 * Submission.boxSide ω.1 * s ∧
      faceVertDet ψ σ ω.1 ω.2.1 p = 0 ∧
      fderiv ℝ (faceVertDet ψ σ ω.1 ω.2.1) p (faceTangent ψ σ ω.1 p) ≠ 0}

/-- The flat height of a parameter, measured from the centre `c`. -/
def faceHeight (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (p : ℝ × ℝ) : ℝ :=
  (Work.BoxShrink.Pinch.par ψ p) (σ 2) - c (σ 2)

/-- **The bad parameters are countable.**  At a bad parameter the trace map `(y_{σ i} ∘ par,
faceVertDet)` has invertible derivative, hence is injective on a neighbourhood; every point of
`faceBadParams` is therefore isolated in it. -/
theorem faceBadParams_countable (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3))
    (s : ℝ) (ω : Fin 3 × Fin 3 × Bool) : (faceBadParams ψ c σ s ω).Countable := by
  obtain ⟨i, ⟨j, b⟩⟩ := ω
  refine countable_of_nhds_isolated (S := faceBadParams ψ c σ s (i, j, b)) ?_
  intro p hp
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hinv : (fderiv ℝ (fun q : ℝ × ℝ => ((Work.BoxShrink.Pinch.par ψ q) (σ i),
      faceVertDet ψ σ i j q)) p).IsInvertible := isInvertible_fderiv_pair_of_bend ψ σ i j p hp3
  have hΨ : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => ((Work.BoxShrink.Pinch.par ψ q) (σ i),
      faceVertDet ψ σ i j q)) p := (contDiff_facePair ψ σ i j).contDiffAt
  obtain ⟨U, hUmem, hUinj⟩ := Band.injOn_of_isInvertible_fderiv hΨ hinv
  obtain ⟨V, hVU, hVopen, hpV⟩ := mem_nhds_iff.mp hUmem
  refine ⟨V, hVopen, hpV, ?_⟩
  rintro q ⟨hqV, hqbad⟩
  obtain ⟨hq1, hq2, -⟩ := hqbad
  have heq : ((Work.BoxShrink.Pinch.par ψ q) (σ i), faceVertDet ψ σ i j q) =
      ((Work.BoxShrink.Pinch.par ψ p) (σ i), faceVertDet ψ σ i j p) := by
    rw [hq1, hp1, hq2, hp2]
  exact hUinj (hVU hqV) (hVU hpV) heq

/-- **FaceNoBend at almost every cutting level** (project lead, `Mono/NOTES_LEAD_junctionGen.md`
§2, G2).  For every level `s` and every centre `c`, a *vertical-tangent* crossing of the box trace
`Γ` with the flat plane `{y (σ 2) = c (σ 2) + u}` is a double zero of the vertical-tangent
determinant, for almost every `u`.

This is what replaces the withdrawn `CFree` clause of the earlier design (which was false: a
vertical-tangent crossing with non-zero bend is a fold, and the level functional `ℓ` restricted to
the trace necessarily has a critical point inside the slab arc there, for every choice of the tilt).

Proof sketch (the trace analogue of `Work.Drive.Mono.ae_noBendCrossing`, `Mono/NoBend.lean`): at a
bend point `p` the map `Ψ = (y (σ i) ∘ par, faceVertDet ψ σ i j)` has an **invertible** derivative
(its determinant is `fderiv (faceVertDet ψ σ i j) p (faceTangent ψ σ i p)`, and the tangent field
`faceTangent ψ σ i p` lies in the kernel of `d (y (σ i) ∘ par)`), so `p` is isolated in the fibre
`Ψ⁻¹ (c (σ i) + ε boxSide i · s, 0)` by the inverse function theorem; the fibre is covered by the
injectivity neighbourhoods, hence is countable by Lindelöf
(`TopologicalSpace.isOpen_iUnion_countable`); the heights `y (σ 2) ∘ par` of its points are then
countable, hence null (`Set.Countable.measure_zero`). -/
theorem ae_faceNoBend (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Work.Drive.Mono.FaceNoBend ψ c σ s u := by
  classical
  have hnull : ∀ ω : Fin 3 × Fin 3 × Bool,
      (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        (faceHeight ψ c σ '' faceBadParams ψ c σ s ω) = 0 :=
    fun ω => ((faceBadParams_countable ψ c σ s ω).image (faceHeight ψ c σ)).measure_zero _
  have hunion : (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      (⋃ ω : Fin 3 × Fin 3 × Bool, faceHeight ψ c σ '' faceBadParams ψ c σ s ω) = 0 :=
    measure_iUnion_null hnull
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hunion
  intro u hu
  rw [Set.mem_ofPred_eq] at hu
  simp only [FaceNoBend] at hu
  push Not at hu
  obtain ⟨i, j, _hi2, _hj2, _hij, ε, hε, p, hp1, hp2, hdet, hbend⟩ := hu
  have hsgn : nbFaceSgn (decide (ε = 1)) = ε := by
    rcases hε with h1 | h1
    · have hd : decide (ε = 1) = true := by rw [h1]; norm_num
      rw [hd, h1]; norm_num [nbFaceSgn]
    · have hd : decide (ε = 1) = false := by rw [h1]; norm_num
      rw [hd, h1]; norm_num [nbFaceSgn]
  refine Set.mem_iUnion.mpr ⟨(i, j, decide (ε = 1)), p, ?_, ?_⟩
  · refine ⟨?_, hdet, hbend⟩
    rw [hsgn]
    exact hp1
  · simp only [faceHeight]
    linarith

end

end Work.Drive.Mono
