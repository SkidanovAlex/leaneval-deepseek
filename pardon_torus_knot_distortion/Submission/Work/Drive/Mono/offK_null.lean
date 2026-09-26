import Mathlib
import Submission.Work.Drive.Mono.offK_defs
import Submission.Work.Drive.Mono.faceEvent_degen_null
import Submission.Work.Drive.Mono.no_eventOnFace_null
import Submission.Work.Drive.EpsForm.tiltedSweepGenericity_holds
import Submission.Work.Smooth.Morse.Immersion
import Submission.Work.Drive.Mono.tangent_of_surfPoly_deriv_zero
import Submission.Work.Drive.Mono.countable_of_deriv_ne_zero

/-!
# The `offK` clause: the bad set is null, and off it the clause holds

`Work.Drive.Mono.offKBad` collects the pairs `(h,τ)` at which the clause `offK` of
`Work.Drive.Final.GoodSweepData` may fail for the height direction `nn τ = dirOf τ a₀ b₀`: a
*transversal crossing* of the knot with the surface (`Work.Drive.Mono.offKCrossSet`), inside the box and
the closed slab, at which the swept height is critical.

This module proves

* `Work.Drive.Mono.crit_affine` — the criticality of the height in direction `dirOf τ a₀ b₀` at `q` is
  the pair of *affine* equations `τ ⟪a₀,wᵢ⟫ + ⟪b₀,wᵢ⟫ = 0` in `τ`, where `wᵢ` are the columns of the
  differential of the immersion `par ψ` at `q`;
* `Work.Drive.Mono.tauSet_subsingleton` — hence at most one `τ` makes the height in direction
  `dirOf τ a₀ b₀` critical at a fixed `q`;
* `Work.Drive.Mono.volume_offKBad_eq_zero` — hence `offKBad` is a countable union of *vertical rays*
  (the crossing set is countable by `Work.Drive.Mono.countable_of_deriv_ne_zero`), so it is null;
* `Work.Drive.Mono.offK_of_notMem_offKBad` — and off `offKBad` the clause holds.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

/-- **The chain rule for the swept height in the direction of a unit vector.** -/
theorem fderiv_sweepHeight_comp (ψ : Submission.Diffeo) (n : R3) (q : ℝ × ℝ) :
    fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) n)) q
      = (innerSL ℝ n).comp (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q) := by
  rw [Work.Drive.EpsForm.sweepHeight_innerSL, Work.BoxShrink.Pinch.par]
  exact Work.Drive.Mono.NoEventOnFace.fderiv_heightOf_eq_comp ψ n q

/-- **Criticality of the swept height is an affine equation in `τ`.**  If the height in the direction
`dirOf τ a₀ b₀` is critical at `q`, then for every parameter direction `r`
`τ ⟪a₀, dpar(q) r⟫ + ⟪b₀, dpar(q) r⟫ = 0`. -/
theorem crit_affine {ψ : Submission.Diffeo} {a₀ b₀ : R3} (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1)
    (hab : inner ℝ a₀ b₀ = 0) {q : ℝ × ℝ} {τ : ℝ}
    (h : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) q = 0) (r : ℝ × ℝ) :
    τ * inner ℝ a₀ (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q r)
      + inner ℝ b₀ (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q r) = 0 := by
  have hchain := fderiv_sweepHeight_comp ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) q
  have hL : (innerSL ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀)).comp
      (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q) = 0 := hchain.symm.trans h
  have h1 := congrArg (fun (L : (ℝ × ℝ) →L[ℝ] ℝ) => L r) hL
  have h0 : inner ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀)
      (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q r) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, zero_apply, innerSL_apply_apply] using h1
  rw [Work.Drive.Mono.Band.dirOf, inner_smul_left] at h0
  have hne : (‖τ • a₀ + b₀‖)⁻¹ ≠ 0 :=
    inv_ne_zero (norm_ne_zero_iff.mpr (Work.Drive.Mono.Band.dirOf_denom_ne_zero ha hb hab τ))
  have h2 : inner ℝ (τ • a₀ + b₀) (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q r) = 0 :=
    (mul_eq_zero.mp h0).resolve_left hne
  rw [inner_add_left, inner_smul_left] at h2
  simpa using h2

/-- **At most one `τ` makes the height in the direction `dirOf τ a₀ b₀` critical at a fixed point.**

The two columns `w₁ = dpar(q)(1,0)`, `w₂ = dpar(q)(0,1)` of the differential of the immersion
`par ψ` are linearly independent, so at least one of the two affine functions
`τ ↦ τ⟪a₀,wᵢ⟫ + ⟪b₀,wᵢ⟫` is nonconstant (otherwise `w₁` and `w₂` would both be orthogonal to the
orthonormal triple `v, a₀, b₀`, hence parallel), and the common zero of the two is unique. -/
theorem tauSet_subsingleton {ψ : Submission.Diffeo} {v a₀ b₀ : R3}
    (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) (q : ℝ × ℝ) {τ τ' : ℝ}
    (hτ : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
      ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) q = 0)
    (hτ' : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
      ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ' a₀ b₀))) q = 0) : τ = τ' := by
  set w₁ : R3 := fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q (1, 0) with hw₁
  set w₂ : R3 := fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q (0, 1) with hw₂
  have hind : ∀ c₁ c₂ : ℝ, c₁ • w₁ + c₂ • w₂ = 0 → c₁ = 0 ∧ c₂ = 0 := by
    intro c₁ c₂ hc
    have hdec : (c₁, c₂) = c₁ • ((1, 0) : ℝ × ℝ) + c₂ • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    have hmap : fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q (c₁, c₂) = c₁ • w₁ + c₂ • w₂ := by
      rw [hdec, map_add]
      rw [map_smul, map_smul]
    have hzero : fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q (c₁, c₂) = 0 := by rw [hmap, hc]
    have hinj : Function.Injective (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q) :=
      Work.Smooth.Morse.isImmersion ψ q
    have h0 : (c₁, c₂) = 0 := hinj (by rw [hzero, map_zero])
    exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩
  have eqs : ∀ σ : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf σ a₀ b₀))) q = 0 →
      (σ * inner ℝ a₀ w₁ + inner ℝ b₀ w₁ = 0 ∧ σ * inner ℝ a₀ w₂ + inner ℝ b₀ w₂ = 0) := by
    intro σ hσ
    exact ⟨by simpa [hw₁] using crit_affine ha hb hab hσ (1, 0),
      by simpa [hw₂] using crit_affine ha hb hab hσ (0, 1)⟩
  obtain ⟨hA1, hA2⟩ := eqs τ hτ
  obtain ⟨hB1, hB2⟩ := eqs τ' hτ'
  have hva' : inner ℝ a₀ v = 0 := by rw [real_inner_comm]; exact hva
  have hvb' : inner ℝ b₀ v = 0 := by rw [real_inner_comm]; exact hvb
  -- a vector orthogonal to `a₀` and `b₀` is a multiple of `v`
  have hpar : ∀ w : R3, inner ℝ a₀ w = 0 → inner ℝ b₀ w = 0 → w = inner ℝ w v • v := by
    intro w hwa hwb
    have hvv : inner ℝ v v = 1 := by
      rw [real_inner_self_eq_norm_sq, hv]; norm_num
    have hY : inner ℝ v (w - inner ℝ w v • v) = 0 := by
      rw [inner_sub_right, inner_smul_right, hvv, real_inner_comm v w]
      ring
    have hdec := onb_decomp hv ha hb hab hva hvb hY
    have h1 : inner ℝ a₀ (w - inner ℝ w v • v) = 0 := by
      rw [inner_sub_right, inner_smul_right, hwa, hva']; ring
    have h2 : inner ℝ b₀ (w - inner ℝ w v • v) = 0 := by
      rw [inner_sub_right, inner_smul_right, hwb, hvb']; ring
    rw [h1, h2, zero_smul, zero_smul, add_zero] at hdec
    rw [sub_eq_zero] at hdec
    exact hdec
  rcases eq_or_ne (inner ℝ a₀ w₁) 0 with h1 | h1
  · rcases eq_or_ne (inner ℝ a₀ w₂) 0 with h2 | h2
    · -- both slopes vanish: `w₁` and `w₂` are both multiples of `v`, contradicting independence
      have hb1 : inner ℝ b₀ w₁ = 0 := by
        have h := hA1; rw [h1, mul_zero, zero_add] at h; exact h
      have hb2 : inner ℝ b₀ w₂ = 0 := by
        have h := hA2; rw [h2, mul_zero, zero_add] at h; exact h
      set c₁ : ℝ := inner ℝ w₁ v with hc₁def
      set c₂ : ℝ := inner ℝ w₂ v with hc₂def
      have hc₁ : w₁ = c₁ • v := by rw [hc₁def]; exact hpar w₁ h1 hb1
      have hc₂ : w₂ = c₂ • v := by rw [hc₂def]; exact hpar w₂ h2 hb2
      have hz : c₂ • w₁ - c₁ • w₂ = 0 := by
        rw [hc₁, hc₂, smul_smul, smul_smul, ← sub_smul]
        rw [show c₂ * c₁ - c₁ * c₂ = (0 : ℝ) from by ring, zero_smul]
      obtain ⟨hz1, hz2⟩ := hind c₂ (-c₁) (by rw [neg_smul, ← sub_eq_add_neg]; exact hz)
      have hw1zero : w₁ = 0 := by
        rw [hc₁, show c₁ = (0 : ℝ) from neg_eq_zero.mp hz2, zero_smul]
      have hone : (1 : ℝ) = 0 := by
        have hzz : (1 : ℝ) • w₁ + (0 : ℝ) • w₂ = 0 := by rw [hw1zero]; simp
        exact (hind 1 0 hzz).1
      exact absurd hone one_ne_zero
    · have e1 : τ = -(inner ℝ b₀ w₂) / (inner ℝ a₀ w₂) := by
        field_simp
        linarith [hA2]
      have e2 : τ' = -(inner ℝ b₀ w₂) / (inner ℝ a₀ w₂) := by
        field_simp
        linarith [hB2]
      rw [e1, e2]
  · have e1 : τ = -(inner ℝ b₀ w₁) / (inner ℝ a₀ w₁) := by
      field_simp
      linarith [hA1]
    have e2 : τ' = -(inner ℝ b₀ w₁) / (inner ℝ a₀ w₁) := by
      field_simp
      linarith [hB1]
    rw [e1, e2]

/-- **The bad set of the `offK` clause is null.**  It is contained in a countable union of vertical
rays: for a fixed lift `q` of a crossing point of the knot with the surface at most one `τ` makes the
height critical there (`tauSet_subsingleton`), and the crossing set is countable. -/
theorem volume_offKBad_eq_zero (ψ : Submission.Diffeo) (K : Knot) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v a₀ b₀ : R3)
    (hv : ‖v‖ = 1) (ha : ‖a₀‖ = 1) (hb : ‖b₀‖ = 1) (hab : inner ℝ a₀ b₀ = 0)
    (hva : inner ℝ v a₀ = 0) (hvb : inner ℝ v b₀ = 0) :
    MeasureTheory.volume (offKBad ψ K s c σ u v a₀ b₀) = 0 := by
  classical
  have hcount : (offKCrossSet ψ K).Countable :=
    Work.Drive.Mono.countable_of_deriv_ne_zero (surfLevelKnot ψ K) (surfLevelKnot_contDiff ψ K)
  obtain ⟨g, hg⟩ := (Set.countable_iff_exists_subset_range (α := ℝ)).mp hcount
  have hex : ∀ n : ℕ, ∃ q : ℝ × ℝ, (Work.BoxShrink.Pinch.par ψ q = K.curve (g n)) ∨
      (K.curve (g n) ∉ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
    intro n
    by_cases h : K.curve (g n) ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier
    · rw [Work.Smooth.Morse.torus_carrier] at h
      obtain ⟨q, hq⟩ := Set.mem_range.mp h
      exact ⟨q, Or.inl hq⟩
    · exact ⟨0, Or.inr h⟩
  set qn : ℕ → ℝ × ℝ := (fun n => Classical.choose (hex n)) with hqn_def
  have hqn : ∀ (n : ℕ) (h : ∃ q : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ q = K.curve (g n)),
      Work.BoxShrink.Pinch.par ψ (qn n) = K.curve (g n) := by
    intro n h
    rcases Classical.choose_spec (hex n) with hpar | hnot
    · exact hpar
    · exfalso
      obtain ⟨q, hq⟩ := h
      exact hnot (by rw [← hq]; exact Work.Smooth.Morse.param_mem ψ q)
  set S : ℕ → Set (ℝ × ℝ) := (fun n => {p : ℝ × ℝ |
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf p.2 a₀ b₀))) (qn n) = 0 ∧
      |inner ℝ v (K.curve (g n)) - (inner ℝ v c + u)| ≤ p.1}) with hS_def
  have hSnull : ∀ n, MeasureTheory.volume (S n) = 0 := by
    intro n
    have hsub : ({τ : ℝ | fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) (qn n) = 0}).Subsingleton :=
      fun τ hτ τ' hτ' => tauSet_subsingleton hv ha hb hab hva hvb (qn n) hτ hτ'
    have hfin : ({τ : ℝ | fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) (qn n) = 0}).Finite :=
      Set.Subsingleton.finite hsub
    refine MeasureTheory.measure_mono_null (t := Set.Ici
      |inner ℝ v (K.curve (g n)) - (inner ℝ v c + u)| ×ˢ
      {τ : ℝ | fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) (qn n) = 0}) ?_ ?_
    · intro p hp
      exact ⟨hp.2, hp.1⟩
    · rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
        hfin.measure_zero MeasureTheory.volume, mul_zero]
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_iUnion_null hSnull)
  rintro p ⟨t, ht, hbox, hslab, q, hq, hcrit⟩
  obtain ⟨n, hn⟩ := hg ht
  have hnt : g n = t := hn
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  have hex' : ∃ q' : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ q' = K.curve (g n) := ⟨q, by rw [hnt, hq]⟩
  have hqnl : Work.BoxShrink.Pinch.par ψ (qn n) = K.curve (g n) := hqn n hex'
  have hpar_eq : Work.BoxShrink.Pinch.par ψ q = Work.BoxShrink.Pinch.par ψ (qn n) := by
    rw [hq, hqnl, ← hnt]
  obtain ⟨k, m, hk, hm⟩ := (Work.Drive.EpsForm.par_eq_iff ψ q (qn n)).mp hpar_eq
  have hcrit' : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
      ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf p.2 a₀ b₀))) (qn n) = 0 := by
    have hper := Work.Drive.EpsForm.fderiv_sweepHeight_periodic ψ
      ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf p.2 a₀ b₀)) k m q
    have hqeq : (q.1 - (k : ℝ) * (2 * Real.pi), q.2 - (m : ℝ) * (2 * Real.pi)) = qn n := by
      rw [Prod.ext_iff]
      exact ⟨by linarith [hk], by linarith [hm]⟩
    rw [hqeq] at hper
    rw [hper]
    exact hcrit
  refine ⟨hcrit', ?_⟩
  have : |inner ℝ v (K.curve t) - (inner ℝ v c + u)|
      = |inner ℝ v (K.curve (g n)) - (inner ℝ v c + u)| := by rw [hnt]
  rw [← this]
  exact hslab

/-- **Off the bad set, the `offK` clause holds.**  A bad witness would be a point of the surface
inside the box and the closed slab at which the swept height is critical and which lies on the trace
of the knot; the robustness clause (`∀ t, K.curve t ∈ PBox → |slab| ≤ h → deriv (ℓ ∘ K.curve) t ≠ 0`)
forces the velocity of the knot there to be *transversal* to the surface, i.e. the crossing to be an
element of `Work.Drive.Mono.offKCrossSet`; that is exactly the definition of `offKBad`. -/
theorem offK_of_notMem_offKBad {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c v a₀ b₀ : R3}
    {σ : Equiv.Perm (Fin 3)} {h τ : ℝ}
    (hrob : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h →
      deriv (fun r : ℝ => inner ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) (K.curve r)) t ≠ 0)
    (hnotmem : (h, τ) ∉ offKBad ψ K s c σ u v a₀ b₀) :
    ∀ q : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ q ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ q ∈
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ
        ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))) q = 0 →
      ∀ t : ℝ, K.curve t ≠ Work.BoxShrink.Pinch.par ψ q := by
  intro q hqbox hqslab hqcrit t ht
  refine hnotmem ⟨t, ?_, by rw [ht]; exact hqbox, by rw [ht]; exact hqslab, q, ht.symm, hqcrit⟩
  · refine ⟨?_, ?_⟩
    · show surfPoly (ψ.invFun (K.curve t)) = 0
      rw [ht]
      exact surfPoly_invFun_eq_zero (Work.Smooth.Morse.param_mem ψ q)
    · intro hd
      have htan := Work.Drive.Mono.tangent_of_surfPoly_deriv_zero ψ K.curve K.smooth
        (show K.curve t = Work.Smooth.Morse.param ψ q by rw [ht]; rfl) hd
      obtain ⟨r, hr⟩ := htan
      have hchain := fderiv_sweepHeight_comp ψ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) q
      have hL : (innerSL ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀)).comp
          (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q) = 0 := hchain.symm.trans hqcrit
      have h1 := congrArg (fun (L : (ℝ × ℝ) →L[ℝ] ℝ) => L r) hL
      have h0 : inner ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀)
          (fderiv ℝ (Work.BoxShrink.Pinch.par ψ) q r) = 0 := by
        simpa only [ContinuousLinearMap.comp_apply, zero_apply, innerSL_apply_apply] using h1
      have hdK : HasDerivAt K.curve (deriv K.curve t) t :=
        ((K.smooth.differentiable (by simp)).differentiableAt).hasDerivAt
      have hcomp : HasDerivAt ((fun x : R3 =>
          (innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀) x) ∘ K.curve)
          ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀) (deriv K.curve t)) t :=
        (ContinuousLinearMap.hasFDerivAt
          ((innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))).comp_hasDerivAt t hdK
      have hderiv_eq : deriv (fun r : ℝ => inner ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀)
          (K.curve r)) t
          = (innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀) (deriv K.curve t) := by
        have h3 : (fun r : ℝ => (innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀) (K.curve r))
            = (fun r : ℝ => inner ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) (K.curve r)) := by
          funext r
          rw [innerSL_apply_apply]
        rw [← h3]
        exact hcomp.deriv
      have hzero : inner ℝ (Work.Drive.Mono.Band.dirOf τ a₀ b₀) (deriv K.curve t) = 0 := by
        rw [← hr]
        exact h0
      refine hrob t (by rw [ht]; exact hqbox) (by rw [ht]; exact hqslab) ?_
      rw [hderiv_eq, innerSL_apply_apply, hzero]

/-- **The critical values of the tilted height of the knot form a null set.**  This is the
one-dimensional Sard lemma for the (periodic, smooth) height `t ↦ ⟪v, K.curve t⟫` of the knot; it is
the counting input of the `knotGP` clause of `Work.Drive.Final.GoodSweepData` (`a ± h` away from the
critical values makes the knot transverse to the two slab faces). -/
theorem volume_knotCritValues_eq_zero (K : Knot) (v : R3) :
    MeasureTheory.volume {y : ℝ | ∃ t : ℝ,
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 ∧
        inner ℝ v (K.curve t) = y} = 0 := by
  set g : ℝ → ℝ := fun u => inner ℝ v (K.curve u) with hgdef
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    have h : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (innerSL ℝ v) (K.curve u)) :=
      ContDiff.continuousLinearMap_comp (innerSL ℝ v) K.smooth
    simpa [g] using h
  have hgd : ∀ t, HasDerivAt g (deriv g t) t := fun t =>
    (hg.differentiable (by simp)).differentiableAt.hasDerivAt
  have hnull : MeasureTheory.volume (g '' {t | deriv g t = 0}) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := MeasureTheory.volume)
      (f' := fun t => ContinuousLinearMap.toSpanSingleton ℝ (deriv g t)) ?_ ?_
    · intro t _
      exact (hgd t).hasFDerivAt.hasFDerivWithinAt
    · intro t ht
      rw [ht, ContinuousLinearMap.det_toSpanSingleton]
  have hset : {y : ℝ | ∃ t : ℝ, deriv g t = 0 ∧ g t = y} = g '' {t | deriv g t = 0} := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  rw [show {y : ℝ | ∃ t : ℝ, deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 ∧
      inner ℝ v (K.curve t) = y} = {y : ℝ | ∃ t : ℝ, deriv g t = 0 ∧ g t = y} from by
    simp only [hgdef]]
  rw [hset]
  exact hnull

end

end Work.Drive.Mono
