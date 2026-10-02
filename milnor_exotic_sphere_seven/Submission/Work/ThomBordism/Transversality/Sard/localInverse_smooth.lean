import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The local inverse of a `C^∞` map (on a neighbourhood)

Two lemmas of independent interest:

* `isOpen_setOf_isInvertible`: the set of invertible continuous linear maps `E →L F` (with `E`
  complete) is open in the operator norm topology;
* `contDiffOn_symm_of_contDiffOn`: the local inverse of an open partial homeomorphism whose forward
  map is `C^∞` at every point of an open set, with invertible derivative there, is `C^∞` on an open
  neighbourhood of the image point.

For the second lemma the analytic result `Sard.contDiffOn_symm_of_analyticAt` is not applicable
(a `C^∞` map need not be analytic), and the natural `OpenPartialHomeomorph.restrContDiff` route
needs `n ≠ ∞` because the set of points of `C^∞`-smoothness is not open.  We instead prove the
statement by the classical bootstrap: with `U := e.target ∩ e.symm ⁻¹' G` one shows by induction on
`N` that `e.symm` is `C^N` at every point of `U` — using the derivative formula
`d(e.symm)_y = (d e_{e.symm y})⁻¹` and the `C^N`-smoothness of `inverse ∘ fderiv e ∘ e.symm` — and
then concludes with `contDiffAt_infty`.

This is what the "level set" step of Sard's theorem needs for `C^∞` (rather than analytic) data:
see `Sard.levelSet_null_smooth`.
-/

open scoped ContDiff MeasureTheory
open MeasureTheory Set

namespace Work.ThomBordism.Transversality.Sard

noncomputable section

/-- The set of invertible continuous linear maps is open. -/
theorem isOpen_setOf_isInvertible {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :
    IsOpen {L : E →L[ℝ] F | L.IsInvertible} := by
  rw [isOpen_iff_mem_nhds]
  intro L₀ hL₀
  obtain ⟨e, he⟩ := hL₀
  set Φ : (E →L[ℝ] F) → (E →L[ℝ] E) := fun L => (e.symm : F →L[ℝ] E) ∘L L with hΦ
  have hΦcont : Continuous Φ := continuous_const.clm_comp continuous_id
  have hpre : IsOpen (Φ ⁻¹' {f : E →L[ℝ] E | IsUnit f}) :=
    Units.isOpen.preimage hΦcont
  have hmem : L₀ ∈ Φ ⁻¹' {f : E →L[ℝ] E | IsUnit f} := by
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hΦ]
    rw [← he]
    have : (e.symm : F →L[ℝ] E) ∘L (e : E →L[ℝ] F) = ContinuousLinearMap.id ℝ E := by
      ext x
      simp
    rw [this]
    exact isUnit_one
  refine Filter.mem_of_superset (hpre.mem_nhds hmem) ?_
  intro L hL
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hΦ] at hL
  simp only [Set.mem_ofPred_eq]
  have hbij : Function.Bijective ((e.symm : F →L[ℝ] E) ∘L L) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hL
  have hinj : Function.Injective L := fun x y hxy => hbij.1 (by simp [hxy])
  have hsurj : Function.Surjective L := fun y => by
    obtain ⟨x, hx⟩ := hbij.2 ((e.symm : F →L[ℝ] E) y)
    refine ⟨x, ?_⟩
    have h := congrArg (fun z => e z) hx
    simpa using h
  exact ⟨ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj), rfl⟩

theorem contDiffOn_symm_of_contDiffOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {e : OpenPartialHomeomorph E F} {G : Set E} (hG : IsOpen G)
    (he : ContDiffOn ℝ ∞ (e : E → F) G)
    (hInv : ∀ x ∈ G, (fderiv ℝ (e : E → F) x).IsInvertible)
    {x₀ : E} (hx₀ : x₀ ∈ G) (hx₀e : x₀ ∈ e.source) :
    ∃ W : Set F, IsOpen W ∧ e x₀ ∈ W ∧ W ⊆ e.target ∧
      (∀ y ∈ W, e (e.symm y) = y) ∧ ContDiffOn ℝ ∞ (e.symm : F → E) W := by
  classical
  set U : Set F := e.target ∩ (e.symm : F → E) ⁻¹' G with hU
  have hUopen : IsOpen U := e.isOpen_inter_preimage_symm hG
  have hUtgt : ∀ y ∈ U, y ∈ e.target := fun y hy => hy.1
  have hUG : ∀ y ∈ U, (e.symm : F → E) y ∈ G := fun y hy => hy.2
  let f' : F → F →L[ℝ] E := fun y => (fderiv ℝ (e : E → F) ((e.symm : F → E) y)).inverse
  have hderiv : ∀ y ∈ U, HasFDerivAt (e.symm : F → E) (f' y) y := by
    intro y hy
    obtain ⟨i, hi⟩ := hInv _ (hUG y hy)
    have hd : HasFDerivAt (e : E → F) (fderiv ℝ (e : E → F) ((e.symm : F → E) y))
        ((e.symm : F → E) y) :=
      ((he.contDiffAt (hG.mem_nhds (hUG y hy))).differentiableAt (by simp)).hasFDerivAt
    have hd' : HasFDerivAt (e : E → F) (i : E →L[ℝ] F) ((e.symm : F → E) y) := by
      rw [← hi] at hd
      exact hd
    have h := e.hasFDerivAt_symm hy.1 hd'
    have hf' : f' y = (↑i.symm : F →L[ℝ] E) := by
      simp only [f']
      rw [← hi, ContinuousLinearMap.inverse_equiv]
    rw [hf']
    exact h
  have hpt : ∀ N : ℕ, ∀ y ∈ U, ContDiffAt ℝ (N : ℕ∞ω) (e.symm : F → E) y := by
    intro N
    induction N with
    | zero =>
      intro y hy
      show ContDiffAt ℝ (0 : ℕ∞ω) (e.symm : F → E) y
      rw [contDiffAt_zero]
      exact ⟨e.target, e.open_target.mem_nhds hy.1, by
        simpa only [OpenPartialHomeomorph.symm_source] using e.symm.continuousOn⟩
    | succ N ih =>
      intro y hy
      have hNne : (N : ℕ∞ω) ≠ ∞ := by simp
      have hle : (N : ℕ∞ω) + 1 ≤ ∞ := by
        rw [show (N : ℕ∞ω) + 1 = (↑(N + 1) : ℕ∞ω) from rfl,
          show (∞ : ℕ∞ω) = (↑(⊤ : ℕ∞) : ℕ∞ω) from rfl]
        exact WithTop.coe_le_coe.mpr le_top
      have hcast : (↑(N + 1) : ℕ∞ω) = (N : ℕ∞ω) + 1 := rfl
      rw [← contDiffWithinAt_univ, hcast]
      rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt hNne]
      refine ⟨U, ?_, ?_, f', ?_, ?_⟩
      · rw [insert_eq_of_mem (show y ∈ univ from trivial), nhdsWithin_univ]
        exact hUopen.mem_nhds hy
      · intro h
        exact absurd h (ne_of_lt (WithTop.coe_lt_top (N : ℕ∞)))
      · intro y' hy'
        exact (hderiv y' hy').hasFDerivWithinAt
      · have h1 : ContDiffWithinAt ℝ (N : ℕ∞ω) (e.symm : F → E) U y :=
          (ih y hy).contDiffWithinAt
        have h2 : ContDiffWithinAt ℝ (N : ℕ∞ω) (fun z : E => fderiv ℝ (e : E → F) z) G
            ((e.symm : F → E) y) :=
          (ContDiffAt.fderiv_right (he.contDiffAt (hG.mem_nhds (hUG y hy))) hle).contDiffWithinAt
        have h3 : ContDiffWithinAt ℝ (N : ℕ∞ω)
            (fun z => fderiv ℝ (e : E → F) ((e.symm : F → E) z)) U y :=
          ContDiffWithinAt.comp y (t := G) h2 h1 (fun z hz => hUG z hz)
        have h4 : ContDiffWithinAt ℝ (N : ℕ∞ω) ContinuousLinearMap.inverse Set.univ
            (fderiv ℝ (e : E → F) ((e.symm : F → E) y)) :=
          ((hInv _ (hUG y hy)).contDiffAt_map_inverse (n := (N : ℕ∞ω))).contDiffWithinAt
        exact ContDiffWithinAt.comp y h4 h3 (Set.mapsTo_univ _ U)
  have hfin : ContDiffOn ℝ ∞ (e.symm : F → E) U := by
    rw [hUopen.contDiffOn_iff]
    intro y hy
    rw [contDiffAt_infty]
    exact fun N => hpt N y hy
  have hx₀U : e x₀ ∈ U := by
    refine ⟨e.map_source hx₀e, ?_⟩
    show (e.symm : F → E) (e x₀) ∈ G
    rw [e.left_inv hx₀e]
    exact hx₀
  exact ⟨U, hUopen, hx₀U, fun y hy => hy.1, fun y hy => e.right_inv hy.1, hfin⟩

end

end Work.ThomBordism.Transversality.Sard
