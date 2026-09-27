import Mathlib
import Submission.Work.Drive.boxParity
import Submission.Work.Drive.Surf.Model
import Submission.Work.Surf.chordFamily

namespace Work.Surf

open Submission.Drive
open scoped Topology

noncomputable section

/-! ## Elementary plane algebra -/

/-- The plane determinant changes sign when its second argument is negated. -/
lemma det2_neg_right (u v : EuclideanSpace ℝ (Fin 2)) :
    Work.Drive.det2 u (-v) = -Work.Drive.det2 u v := by
  simp [Work.Drive.det2]
  ring

/-- **A two-dimensional determinant identity.**  For three plane vectors `p q y` one has
`det2 y q • p + det2 p y • q = det2 p q • y`; it is the statement that the two linear functionals
`det2 · q` and `det2 p ·` determine a vector. -/
lemma det2_smul_eq (p q y : EuclideanSpace ℝ (Fin 2)) :
    Work.Drive.det2 y q • p + Work.Drive.det2 p y • q = Work.Drive.det2 p q • y := by
  ext i
  fin_cases i <;> simp [Work.Drive.det2] <;> ring

/-- **A linear map from the three-box into the plane containing two independent vectors is onto.**

If `L` maps the two coordinate directions `e₁ = single 1 1` and `e₂ = single 2 1` to `p` and to `-q`,
and `det2 p q ≠ 0`, then `L` is surjective; moreover a preimage of any `y` can be chosen with
vanishing first coordinate (because both `e₁` and `e₂` have vanishing first coordinate). -/
lemma exists_preimage_of_det2 (L : Work.Drive.Amb 2 →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (p q : EuclideanSpace ℝ (Fin 2)) (h : Work.Drive.det2 p q ≠ 0)
    (h1 : L (EuclideanSpace.single 1 1) = p) (h2 : L (EuclideanSpace.single 2 1) = -q)
    (y : EuclideanSpace ℝ (Fin 2)) :
    ∃ v : Work.Drive.Amb 2, v 0 = 0 ∧ L v = y := by
  have hdq : Work.Drive.det2 p (-q) ≠ 0 := by
    rw [det2_neg_right]
    exact neg_ne_zero.mpr h
  refine ⟨(Work.Drive.det2 p (-q))⁻¹ •
      ((Work.Drive.det2 y (-q)) • EuclideanSpace.single 1 1 +
        (Work.Drive.det2 p y) • EuclideanSpace.single 2 1), ?_, ?_⟩
  · simp
  · rw [map_smul, map_add, map_smul, map_smul, h1, h2]
    rw [det2_smul_eq p (-q) y, smul_smul, inv_mul_cancel₀ hdq, one_smul]

/-! ## Smoothness of the difference map -/

/-- The difference map of the straightening family is `C^∞` as soon as the two chords are. -/
lemma contDiff_chordDiff {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hasm : ContDiff ℝ Work.Drive.Ctop a) (hbsm : ContDiff ℝ Work.Drive.Ctop b) :
    ContDiff ℝ Work.Drive.Ctop (chordDiff a b) := by
  rw [show chordDiff a b = fun x : Work.Drive.Amb 2 =>
      chordHom a (a 0) (x 0) (x 1) - b (x 2) from rfl]
  unfold chordHom
  fun_prop

/-! ## The two directional derivatives of the difference map -/

/-- The derivative of `chordDiff a b` at `x` in the `s`-direction is the speed of the member of the
family at time `x 0`. -/
lemma fderiv_chordDiff_single_one {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hasm : ContDiff ℝ Work.Drive.Ctop a) (hbsm : ContDiff ℝ Work.Drive.Ctop b)
    (x : Work.Drive.Amb 2) :
    (fderiv ℝ (chordDiff a b) x) (EuclideanSpace.single 1 1)
      = deriv (fun u : ℝ => chordHom a (a 0) (x 0) u) (x 1) := by
  have hFd : HasFDerivAt (chordDiff a b) (fderiv ℝ (chordDiff a b) x) x :=
    ((contDiff_chordDiff hasm hbsm).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single 1 1)
      (EuclideanSpace.single 1 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single 1 1)).const_add x
  have hFd' : HasFDerivAt (chordDiff a b) (fderiv ℝ (chordDiff a b) x)
      (x + (0 : ℝ) • EuclideanSpace.single 1 1) := by simpa using hFd
  rw [← (hFd'.comp_hasDerivAt 0 hg).deriv]
  have hfun : ((chordDiff a b) ∘ fun t : ℝ => x + t • EuclideanSpace.single 1 1)
      = fun t : ℝ => chordHom a (a 0) (x 0) (x 1 + t) - b (x 2) := by
    funext t
    simp [chordDiff_apply, chordHom]
  rw [hfun, deriv_sub_const, deriv_comp_const_add]
  ring_nf

/-- The derivative of `chordDiff a b` at `x` in the `t`-direction is minus the speed of the fixed
chord `b` at time `x 2`. -/
lemma fderiv_chordDiff_single_two {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hasm : ContDiff ℝ Work.Drive.Ctop a) (hbsm : ContDiff ℝ Work.Drive.Ctop b)
    (x : Work.Drive.Amb 2) :
    (fderiv ℝ (chordDiff a b) x) (EuclideanSpace.single 2 1) = -deriv b (x 2) := by
  have hFd : HasFDerivAt (chordDiff a b) (fderiv ℝ (chordDiff a b) x) x :=
    ((contDiff_chordDiff hasm hbsm).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single 2 1)
      (EuclideanSpace.single 2 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single 2 1)).const_add x
  have hFd' : HasFDerivAt (chordDiff a b) (fderiv ℝ (chordDiff a b) x)
      (x + (0 : ℝ) • EuclideanSpace.single 2 1) := by simpa using hFd
  rw [← (hFd'.comp_hasDerivAt 0 hg).deriv]
  have hfun : ((chordDiff a b) ∘ fun t : ℝ => x + t • EuclideanSpace.single 2 1)
      = fun t : ℝ => chordHom a (a 0) (x 0) (x 1) - b (x 2 + t) := by
    funext t
    simp [chordDiff_apply, chordHom]
  rw [hfun, deriv_const_sub, deriv_comp_const_add]
  ring_nf

/-! ## The regularity of the difference map at a zero -/

/-- **At a zero of the difference map the `s`- and `t`-coordinate of the parameter are interior.**
If `x` is a zero of `chordDiff a b` in the box, then `x` cannot lie on one of the four faces
`s ∈ {0,1}`, `t ∈ {0,1}`, by the two no-zero statements `chordDiff_ne_zero_of_sface`,
`chordDiff_ne_zero_of_tface`. -/
lemma chord_side_of_zero {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (ha : Work.Drive.IsChord a) (hb : Work.Drive.IsChord b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∈ Set.Ioo (0 : ℝ) 1)
    {x : Work.Drive.Amb 2} (hx : x ∈ Submission.Drive.unitBox 2)
    (hzero : chordDiff a b x = 0) :
    x 1 ∈ Set.Ioo (0 : ℝ) 1 ∧ x 2 ∈ Set.Ioo (0 : ℝ) 1 := by
  have hx1 : x 1 ∈ Set.Icc (0 : ℝ) 1 := hx 1
  have hx2 : x 2 ∈ Set.Icc (0 : ℝ) 1 := hx 2
  have h10 : x 1 ≠ 0 := fun h => chordDiff_ne_zero_of_sface a b ha hb hint hx (Or.inl h) hzero
  have h11 : x 1 ≠ 1 := fun h => chordDiff_ne_zero_of_sface a b ha hb hint hx (Or.inr h) hzero
  have h20 : x 2 ≠ 0 := fun h => chordDiff_ne_zero_of_tface a b ha hb hint hx (Or.inl h) hzero
  have h21 : x 2 ≠ 1 := fun h => chordDiff_ne_zero_of_tface a b ha hb hint hx (Or.inr h) hzero
  exact ⟨⟨lt_of_le_of_ne hx1.1 (Ne.symm h10), lt_of_le_of_ne hx1.2 h11⟩,
    ⟨lt_of_le_of_ne hx2.1 (Ne.symm h20), lt_of_le_of_ne hx2.2 h21⟩⟩

/-- **Regularity at a zero of the difference map.**  At a zero `x` of `chordDiff a b` whose `s`- and
`t`-coordinate are interior and whose `τ`-coordinate lies in `[0,1]`, transversality (`htrans`) makes
the derivative surjective: the derivative in the direction `single 1 1` is the speed of the family
member `chordHom a (a 0) (x 0)`, the derivative in the direction `single 2 1` is minus the speed of
`b` at `x 2`, and these two are independent.  In fact a preimage can always be chosen in the
subspace `v 0 = 0`, which is what the boundary clause of `ParityProp` needs. -/
lemma exists_preimage_chordDiff {a b : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hasm : ContDiff ℝ Work.Drive.Ctop a) (hbsm : ContDiff ℝ Work.Drive.Ctop b)
    (htrans : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ s t : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 →
      t ∈ Set.Ioo (0 : ℝ) 1 → chordHom a (a 0) τ s = b t →
      Work.Drive.det2 (deriv (fun u : ℝ => chordHom a (a 0) τ u) s) (deriv b t) ≠ 0)
    {x : Work.Drive.Amb 2} (hx0 : x 0 ∈ Set.Icc (0 : ℝ) 1)
    (hx1 : x 1 ∈ Set.Ioo (0 : ℝ) 1) (hx2 : x 2 ∈ Set.Ioo (0 : ℝ) 1)
    (hzero : chordDiff a b x = 0) (y : EuclideanSpace ℝ (Fin 2)) :
    ∃ v : Work.Drive.Amb 2, v 0 = 0 ∧ (fderiv ℝ (chordDiff a b) x) v = y := by
  have hch : chordHom a (a 0) (x 0) (x 1) = b (x 2) := by
    have h := hzero
    rw [chordDiff_eq] at h
    exact sub_eq_zero.mp h
  exact exists_preimage_of_det2 (fderiv ℝ (chordDiff a b) x)
    (deriv (fun u : ℝ => chordHom a (a 0) (x 0) u) (x 1)) (deriv b (x 2))
    (htrans (x 0) hx0 (x 1) (x 2) hx1 hx2 hch)
    (fderiv_chordDiff_single_one hasm hbsm x)
    (fderiv_chordDiff_single_two hasm hbsm x) y

/-- **The straightening family of a chord is in general position too.**

Read as coordinates `(τ, s, t)` on the cube `[0,1]³`, `chordDiff a b` is the difference map
`(1-τ) • a s + τ • (cos (π s) • a 0) - b t` of the family that deforms the chord `a` to the diameter
through `a 0` against the fixed chord `b`.  If the family is transverse to `b` (`htrans`) and `a` meets
`b` only in the interior of the parameter square (`hint`), then this difference map satisfies the three
hypotheses of `Submission.Drive.ParityProp` (`= Work.Drive.boxParity`) on the cube, and moreover has no
zeros on the four faces `x 1 ∈ {0,1}`, `x 2 ∈ {0,1}`.

The module `Submission.Work.Surf.chordFamily` already provides `Work.Surf.chordDiff_eq`,
`Work.Surf.norm_chordHom_le`, `Work.Surf.chordDiff_ne_zero_of_sface`,
`Work.Surf.eq_of_combo_norm_eq_one` and `Work.Surf.chordDiff_ne_zero_of_tface`: the last conjunct here
is `chordDiff_ne_zero_of_sface` combined with `chordDiff_ne_zero_of_tface` (no zeros on the `s`/`t`
faces).

What is left is the smoothness (`ContDiff`, from `hasm`/`hbsm`) and the two regularity conjuncts: at a
zero `x` the derivative in the directions `e₁ = single 1 1` and `e₂ = single 2 1` is
`deriv (fun u => chordHom a (a 0) (x 0) u) (x 1)` resp. `- deriv b (x 2)` (via `fderiv_apply`,
`HasFDerivAt.fderiv`, the chain rule and `deriv`/`fderiv` for `ℝ → E`), and these two vectors are
independent exactly by `htrans`; the `unitBoxBdry` conjunct then has the witness `i = 0` (a boundary
zero must have `x 0 ∈ {0,1}` and `x 1, x 2 ∈ (0,1)` by the last conjunct). -/
theorem chordFamily_parity (a b : ℝ → EuclideanSpace ℝ (Fin 2))
    (ha : Work.Drive.IsChord a) (hb : Work.Drive.IsChord b)
    (hasm : ContDiff ℝ Work.Drive.Ctop a) (hbsm : ContDiff ℝ Work.Drive.Ctop b)
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∈ Set.Ioo (0 : ℝ) 1)
    (htrans : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ s t : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 → t ∈ Set.Ioo (0 : ℝ) 1 →
      Work.Surf.chordHom a (a 0) τ s = b t →
      Work.Drive.det2 (deriv (fun u : ℝ => Work.Surf.chordHom a (a 0) τ u) s) (deriv b t) ≠ 0) :
    ContDiff ℝ Work.Drive.Ctop (Work.Surf.chordDiff a b) ∧
      (∀ x ∈ Submission.Drive.unitBox 2, Work.Surf.chordDiff a b x = 0 →
        Function.Surjective (fderiv ℝ (Work.Surf.chordDiff a b) x)) ∧
      (∀ x ∈ Submission.Drive.unitBoxBdry 2, Work.Surf.chordDiff a b x = 0 →
        ∃ i : Fin 3, (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          Function.Surjective (fun v : {v : Work.Drive.Amb 2 // v i = 0} =>
            fderiv ℝ (Work.Surf.chordDiff a b) x v.1)) ∧
      (∀ x ∈ Submission.Drive.unitBox 2, (x 1 = 0 ∨ x 1 = 1 ∨ x 2 = 0 ∨ x 2 = 1) →
        Work.Surf.chordDiff a b x ≠ 0) := by
  refine ⟨contDiff_chordDiff hasm hbsm, ?_, ?_, ?_⟩
  · intro x hx hzero y
    obtain ⟨hs1, hs2⟩ := chord_side_of_zero ha hb hint hx hzero
    obtain ⟨v, -, hv⟩ := exists_preimage_chordDiff hasm hbsm htrans (hx 0) hs1 hs2 hzero y
    exact ⟨v, hv⟩
  · intro x hx hzero
    obtain ⟨hbox, i, hi⟩ := hx
    obtain ⟨hs1, hs2⟩ := chord_side_of_zero ha hb hint hbox hzero
    have h0 : x 0 = 0 ∨ x 0 = 1 := by
      fin_cases i
      · exact hi
      · rcases hi with h | h
        · exact absurd h (ne_of_gt hs1.1)
        · exact absurd h (ne_of_lt hs1.2)
      · rcases hi with h | h
        · exact absurd h (ne_of_gt hs2.1)
        · exact absurd h (ne_of_lt hs2.2)
    refine ⟨0, h0, ?_, ?_⟩
    · intro j hj
      fin_cases j
      · exact absurd rfl hj
      · exact hs1
      · exact hs2
    · intro y
      obtain ⟨v, hv0, hv⟩ :=
        exists_preimage_chordDiff hasm hbsm htrans (hbox 0) hs1 hs2 hzero y
      exact ⟨⟨v, hv0⟩, hv⟩
  · intro x hx h hzero
    rcases h with h | h | h | h
    · exact chordDiff_ne_zero_of_sface a b ha hb hint hx (Or.inl h) hzero
    · exact chordDiff_ne_zero_of_sface a b ha hb hint hx (Or.inr h) hzero
    · exact chordDiff_ne_zero_of_tface a b ha hb hint hx (Or.inl h) hzero
    · exact chordDiff_ne_zero_of_tface a b ha hb hint hx (Or.inr h) hzero

end

end Work.Surf
