import Mathlib
import Submission.Work.Drive.Surf.Model
import Submission.Work.Drive.finite_of_isCompact_of_isolated

/-!
# Finiteness of the crossing set of two chords

Under the "no crossings on the boundary of the square" hypothesis (`hint`) and the transversality
hypothesis (`htrans`), the set of parameter pairs `(s,t) ∈ (0,1)²` with `a s = b t` is finite: every
crossing is a nondegenerate zero of the smooth map `(s,t) ↦ a s - b t`, hence isolated, and the
crossing set is contained in the compact box `[0,1]²`.
-/

namespace Work.Surf

open scoped Topology
open Set

noncomputable section

open Work.Drive

/-- Linear independence criterion: `z.1 • p - z.2 • q = 0` forces `z = 0` when `det2 p q ≠ 0`. -/
lemma eq_zero_of_smul_sub_smul_eq_zero {p q : EuclideanSpace ℝ (Fin 2)} (hpq : det2 p q ≠ 0)
    {z : ℝ × ℝ} (hz : z.1 • p - z.2 • q = 0) : z = 0 := by
  have h1 : z.1 * det2 p q = 0 := by
    have h := congrArg (fun v => det2 v q) hz
    have h0 : det2 (0 : EuclideanSpace ℝ (Fin 2)) q = 0 := by simp [det2]
    have hexp : det2 (z.1 • p - z.2 • q) q = z.1 * det2 p q := by
      simp only [det2, WithLp.ofLp_sub, Pi.sub_apply, smul_apply']
      ring
    rw [hexp, h0] at h
    exact h
  have h2 : -(z.2 * det2 p q) = 0 := by
    have h := congrArg (fun v => det2 p v) hz
    have h0 : det2 p (0 : EuclideanSpace ℝ (Fin 2)) = 0 := by simp [det2]
    have hexp : det2 p (z.1 • p - z.2 • q) = -(z.2 * det2 p q) := by
      simp only [det2, WithLp.ofLp_sub, Pi.sub_apply, smul_apply']
      ring
    rw [hexp, h0] at h
    exact h
  have hz1 : z.1 = 0 := (mul_eq_zero.mp h1).resolve_right hpq
  have hz2 : z.2 = 0 := by
    have h : z.2 * det2 p q = 0 := by linarith [h2]
    exact (mul_eq_zero.mp h).resolve_right hpq
  exact Prod.ext hz1 hz2

/-- **Local injectivity of the difference map at a transverse crossing.** -/
lemma local_inj_of_det2_ne {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) {s t : ℝ}
    (h : det2 (deriv a s) (deriv b t) ≠ 0) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (s, t) ∈ U ∧
      Set.InjOn (fun p : ℝ × ℝ => a p.1 - b p.2) U := by
  have had : DifferentiableAt ℝ a s := (ha.differentiable (by norm_num)).differentiableAt
  have hbd : DifferentiableAt ℝ b t := (hb.differentiable (by norm_num)).differentiableAt
  have ha' : HasDerivAt a (deriv a s) s := had.hasDerivAt
  have hb' : HasDerivAt b (deriv b t) t := hbd.hasDerivAt
  set p := deriv a s with hp
  set q := deriv b t with hq
  let L : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (ContinuousLinearMap.toSpanSingleton ℝ p) ∘L (ContinuousLinearMap.fst ℝ ℝ ℝ)
    - (ContinuousLinearMap.toSpanSingleton ℝ q) ∘L (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hLapp : ∀ u v : ℝ, L (u, v) = u • p - v • q := by
    intro u v
    simp [L, ContinuousLinearMap.toSpanSingleton_apply]
  have hker : ∀ z : ℝ × ℝ, L z = 0 → z = 0 := by
    intro z hz
    exact eq_zero_of_smul_sub_smul_eq_zero h (by rw [← hLapp z.1 z.2]; exact hz)
  have hinj : Function.Injective L := by
    intro x y hxy
    have h0 : L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (hker (x - y) h0)
  have hFd : HasFDerivAt (fun z : ℝ × ℝ => a z.1 - b z.2) L (s, t) := by
    have h1 : HasFDerivAt (fun z : ℝ × ℝ => a z.1)
        ((ContinuousLinearMap.toSpanSingleton ℝ p) ∘L (ContinuousLinearMap.fst ℝ ℝ ℝ)) (s, t) := by
      have := HasFDerivAt.comp (s, t) (g := a) (f := Prod.fst) ha'.hasFDerivAt
        (hasFDerivAt_fst (p := (s, t)))
      simpa [hp, Function.comp_def] using this
    have h2 : HasFDerivAt (fun z : ℝ × ℝ => b z.2)
        ((ContinuousLinearMap.toSpanSingleton ℝ q) ∘L (ContinuousLinearMap.snd ℝ ℝ ℝ)) (s, t) := by
      have := HasFDerivAt.comp (s, t) (g := b) (f := Prod.snd) hb'.hasFDerivAt
        (hasFDerivAt_snd (p := (s, t)))
      simpa [hq, Function.comp_def] using this
    exact h1.sub h2
  have hinj' : Function.Injective (L : (ℝ × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) := hinj
  have hkerL : (L : (ℝ × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj'
  have hsurj : (L : (ℝ × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)).range = ⊤ :=
    LinearMap.range_eq_top.mpr
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj')
  set e : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) := ContinuousLinearEquiv.ofBijective L hkerL hsurj
    with he
  have heL : (e : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)) = L := by
    rw [he]
    exact ContinuousLinearEquiv.coe_ofBijective L hkerL hsurj
  have hFd' : HasFDerivAt (fun z : ℝ × ℝ => a z.1 - b z.2)
      (e : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)) (s, t) := hFd.congr_fderiv heL.symm
  have hFcd : ContDiff ℝ 1 (fun z : ℝ × ℝ => a z.1 - b z.2) :=
    (ha.comp contDiff_fst).sub (hb.comp contDiff_snd)
  have hcat : ContDiffAt ℝ 1 (fun z : ℝ × ℝ => a z.1 - b z.2) (s, t) := hFcd.contDiffAt
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  let Φ := ContDiffAt.toOpenPartialHomeomorph (fun z : ℝ × ℝ => a z.1 - b z.2) hcat hFd' hn
  exact ⟨Φ.source, Φ.open_source,
    ContDiffAt.mem_toOpenPartialHomeomorph_source hcat hFd' hn, Φ.injOn⟩

/-- **Finiteness of the crossing set of two chords.** -/
theorem chordMeet_finite {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (ha : IsChord a) (hb : IsChord b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖a s‖ < 1)
    (htrans : ∀ s t : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 → t ∈ Set.Ioo (0 : ℝ) 1 → a s = b t →
      det2 (deriv a s) (deriv b t) ≠ 0) :
    (chordMeet a b).Finite := by
  classical
  set K : Set (ℝ × ℝ) :=
    {z | z.1 ∈ Set.Icc (0 : ℝ) 1 ∧ z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ a z.1 = b z.2} with hK
  have hKcompact : IsCompact K := by
    have h1 : IsClosed {z : ℝ × ℝ | z.1 ∈ Set.Icc (0 : ℝ) 1} :=
      isClosed_Icc.preimage continuous_fst
    have h2 : IsClosed {z : ℝ × ℝ | z.2 ∈ Set.Icc (0 : ℝ) 1} :=
      isClosed_Icc.preimage continuous_snd
    have h3 : IsClosed {z : ℝ × ℝ | a z.1 = b z.2} :=
      isClosed_eq (ha.continuous.comp continuous_fst) (hb.continuous.comp continuous_snd)
    have h4 : K = {z : ℝ × ℝ | z.1 ∈ Set.Icc (0 : ℝ) 1} ∩
        {z : ℝ × ℝ | z.2 ∈ Set.Icc (0 : ℝ) 1} ∩ {z : ℝ × ℝ | a z.1 = b z.2} := by
      ext z
      simp only [hK, Set.mem_setOf_eq, Set.mem_inter_iff]
      tauto
    rw [h4]
    exact IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc) ((h1.inter h2).inter h3)
      (fun z hz => ⟨hz.1.1, hz.1.2⟩)
  have hisol : ∀ z ∈ K, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ z ∈ U ∧ U ∩ K ⊆ {z} := by
    intro z hz
    obtain ⟨hz1, hz2, hzeq⟩ := hz
    obtain ⟨hz1', hz2', -⟩ := hint z.1 z.2 hz1 hz2 hzeq
    have htr := htrans z.1 z.2 hz1' hz2' hzeq
    obtain ⟨U, hUopen, hzU, hUinj⟩ := local_inj_of_det2_ne ha.contDiff hb.contDiff htr
    refine ⟨U, hUopen, hzU, ?_⟩
    rintro w ⟨hwU, hwK⟩
    obtain ⟨-, -, hweq⟩ := hwK
    have hw0 : a w.1 - b w.2 = a z.1 - b z.2 := by rw [hweq, hzeq, sub_self, sub_self]
    have : w = z := hUinj hwU hzU hw0
    simpa using this
  have hKfin : K.Finite := finite_of_isCompact_of_isolated hKcompact hisol
  refine hKfin.subset ?_
  intro z hz
  exact ⟨⟨le_of_lt hz.1.1, le_of_lt hz.1.2⟩, ⟨le_of_lt hz.2.1.1, le_of_lt hz.2.1.2⟩, hz.2.2⟩

end

end Work.Surf
