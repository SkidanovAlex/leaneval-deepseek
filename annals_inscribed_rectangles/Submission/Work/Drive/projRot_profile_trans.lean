import Mathlib
import Submission.Work.Drive.projLine_preconnected
import Submission.Work.Drive.contMDiffAt_projRot
import Submission.Work.Drive.hcRotation

namespace Work.Drive

open scoped Manifold ContDiff Topology

/-! REFEREE NOTE (prose, not code).  **Transitivity of the profile-defined side value: this is Hugelmeyer's fourth result (transitivity of the order, i.e. the third clause of `Work.Drive.ParityCore`) for the rotated family of one chart's plane, proved elementarily from the level structure -- with no mod-2 counting, no triple-transversality and no genericity input.**

Setting.  For a chart `Q : ℂ → CappingSpace` with class plane `X = projLine U` (`U = ker φ`, a `3`-dimensional subspace of `ℝ⁴`, so `X ≅ ℝP²`) and level profile `ρ : X → ℝ` (satisfying `ρ (class (Q z)) = levelOf (Q z)`, so that the level is a function of the class), the *branch form* of the cut dichotomy (`Submission/Work/Drive/sideAntisymmetry.lean`) says

  `e u = 1  ⟺  ρ < ρ ∘ projRot (-(2u))` on `X ∩ projRot (2u) '' X`,

i.e. the swept plane of angle `u` has class plane `projRot (2u) '' X` (the configuration rotation is by the *doubled* angle: `circ t = exp (iπt) = circleOf (t/2)` in `projRot.lean`) and level profile `ρ ∘ projRot (-(2u))`.  The statement below is that comparison at the three `projRot` parameters `0`, `a`, `a + c`: if it holds at `a` and at `c`, it holds at `a + c`.

Proof (the content is the chain `ρ q < ρ (projRot (-a) q) < ρ (projRot (-(a+c)) q)` at one point, plus sign constancy along a connected line).

* Let `q ∈ projLine U ∩ projRot a '' projLine U` be the witness of `htri`, and put `q' := projRot (-a) q`.  By `ha` at `q` we get `ρ q < ρ q'`.  The hypothesis `htri` says exactly `q' ∈ projLine U ∩ projRot c '' projLine U`, so `hc` at `q'` gives `ρ q' < ρ (projRot (-c) q')`, and `projRot (-c) q' = projRot (-(a+c)) q` by the composition law `projRot_add` (`hcRotation.lean`).  Hence `ρ q < ρ (projRot (-(a+c)) q)` holds **at one point `q`** of the target set.
* The function `q ↦ ρ q - ρ (projRot (-(a+c)) q)` is continuous on `projLine U ∩ projRot (a+c) '' projLine U` (`hρ`, and continuity of `projRot` supplied by `Work.Drive.contMDiffAt_projRot`), and by `hne` it is nowhere zero there.  Since that set is preconnected (`hLpre`) and nonempty (`hLne`), its sign is constant, so the single point above forces the sign to be negative on the whole set -- which is the conclusion.

Why this matters.  Composed with the branch form of the dichotomy and its antisymmetry and local-constancy consequences, this gives all three clauses of `Work.Drive.ParityCore` *without* the mod-2 chain chapter (`ChainAntisymmetry`/`ChainFunctional`/`ChainLocality`), the (SURF) multiplicativity, or the `hc`/`hV`/`hface` genericity design: the paper's cohomological transitivity is replaced by the elementary fact that the three profile comparisons are composable along the chain `q ↦ projRot (-a) q` inside the class plane.  Note the equivalence `ParityCore γ ↔ ∃ e, HasFunctional γ e` (`parityCore_iff_hasFunctional`), i.e. the third clause is exactly the transitivity proved here.

Nothing is vacuous, and the three structural hypotheses are *easy* in the application: `hLpre`/`hLne` are `Work.Drive.isPreconnected_projLine_inf` (the intersection of two projective planes in `ℝP³` is a projective line, hence preconnected, and it is nonempty) and `htri` follows from the dimension count `dim (W₀ ⊓ W₁ ⊓ W₂) ≥ 3 + 3 + 3 - 2·4 = 1` for three `3`-dimensional subspaces of `ℝ⁴` (three projective planes in `ℝP³` always meet). -/

/-! ## The two analytic inputs of the proof

* `prpt_continuous_projRot` — the rotation `projRot t` of `ℝP³` is continuous.  It is the descent of
  the continuous linear map `diagRot t` of `ℂ² ≅ ℝ⁴` along the quotient map from the non-zero vectors
  (`Submission/Work/Drive/ProjectiveTopology.lean`), so no manifold structure is needed.
* `prpt_sign_const` — a continuous nowhere-zero function on a preconnected set has constant sign.
-/

/-- A continuous map is `C^0` at every point (the `n = 0` form of `ContDiffAt`). -/
lemma prpt_contDiffAt_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℂ}
    (h : Continuous f) (x : E) : ContDiffAt ℝ 0 f x :=
  contDiffAt_zero.mpr ⟨Set.univ, Filter.univ_mem, h.continuousOn⟩

/-- The complex-coordinate embedding `w ↦ ofComplex (a w) (b w)` is continuous whenever `a` and `b`
are. -/
lemma prpt_continuous_ofComplex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℂ} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun w => ofComplex (a w) (b w)) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (confProjVecOf_contDiffAt_ofComplex (n := 0)
    (prpt_contDiffAt_zero ha x) (prpt_contDiffAt_zero hb x)).continuousAt

/-- The first complex coordinate of `Eucl 3` is continuous. -/
lemma prpt_continuous_c₁ : Continuous (fun x : Eucl 3 => c₁ x) :=
  (confProjVecOf_c₁CLM.continuous).congr (fun x => confProjVecOf_c₁CLM_apply x)

/-- The second complex coordinate of `Eucl 3` is continuous. -/
lemma prpt_continuous_c₂ : Continuous (fun x : Eucl 3 => c₂ x) :=
  (confProjVecOf_c₂CLM.continuous).congr (fun x => confProjVecOf_c₂CLM_apply x)

/-- The diagonal rotation of `ℂ² ≅ ℝ⁴` is continuous. -/
lemma prpt_continuous_diagRot (t : ℝ) : Continuous (fun x : Eucl 3 => diagRot t x) := by
  have hA : Continuous (fun x : Eucl 3 => circ t * c₁ x) :=
    continuous_const.mul prpt_continuous_c₁
  have hB : Continuous (fun x : Eucl 3 => star (circ t) * c₂ x) :=
    continuous_const.mul prpt_continuous_c₂
  simpa only [diagRot] using prpt_continuous_ofComplex hA hB

/-- **The rotation of `ℝP³` is continuous.** -/
lemma prpt_continuous_projRot (t : ℝ) : Continuous (projRot t) := by
  have hq : Topology.IsQuotientMap
      (fun p : {v : Eucl 3 // v ≠ 0} => Projectivization.mk ℝ p.1 p.2) :=
    (isOpenMap_projectivizationMk ℝ (Eucl 3)).isQuotientMap
      (continuous_projectivizationMk ℝ (Eucl 3))
      (fun q => ⟨⟨q.rep, q.rep_nonzero⟩, Projectivization.mk_rep q⟩)
  refine (hq.continuous_iff (g := projRot t)).mpr ?_
  have hg : Continuous fun p : {v : Eucl 3 // v ≠ 0} =>
      (⟨diagRot t p.1, diagRot_ne_zero t p.2⟩ : {v : Eucl 3 // v ≠ 0}) :=
    Continuous.subtype_mk ((prpt_continuous_diagRot t).comp continuous_subtype_val) _
  refine Continuous.congr ((continuous_projectivizationMk ℝ (Eucl 3)).comp hg) ?_
  intro p
  exact (projRot_mk t p.1 p.2).symm

/-- **The sign of a continuous nowhere-zero function on a preconnected set is constant.** -/
lemma prpt_sign_const {α : Type*} [TopologicalSpace α] {S : Set α} {f : α → ℝ}
    (hpre : IsPreconnected S) (hcont : ContinuousOn f S)
    (hne : ∀ x ∈ S, f x ≠ 0) : (∀ x ∈ S, 0 < f x) ∨ (∀ x ∈ S, f x < 0) := by
  have himg : IsPreconnected (f '' S) := hpre.image f hcont
  have hsub : f '' S ⊆ Set.Ioi (0 : ℝ) ∪ Set.Iio (0 : ℝ) := by
    rintro y ⟨x, hx, rfl⟩
    rcases lt_trichotomy (f x) 0 with h | h | h
    · exact Or.inr h
    · exact absurd h (hne x hx)
    · exact Or.inl h
  have hdisj : Disjoint (Set.Ioi (0 : ℝ)) (Set.Iio (0 : ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd (hx'.trans hx) (lt_irrefl x)
  rcases himg.subset_or_subset isOpen_Ioi isOpen_Iio hdisj hsub with h | h
  · exact Or.inl fun x hx => h ⟨x, hx, rfl⟩
  · exact Or.inr fun x hx => h ⟨x, hx, rfl⟩

theorem projRot_profile_trans
    (U : Submodule ℝ (Eucl 3))
    (ρ : Projectivization ℝ (Eucl 3) → ℝ) (hρ : Continuous ρ) (a c : ℝ)
    (hLpre : IsPreconnected (projLine U ∩ projRot (a + c) '' projLine U))
    (hLne : (projLine U ∩ projRot (a + c) '' projLine U).Nonempty)
    (htri : ∃ q ∈ projLine U ∩ projRot a '' projLine U,
      projRot (-a) q ∈ projLine U ∩ projRot c '' projLine U)
    (hne : ∀ q ∈ projLine U ∩ projRot (a + c) '' projLine U, ρ q ≠ ρ (projRot (-(a + c)) q))
    (ha : ∀ q ∈ projLine U ∩ projRot a '' projLine U, ρ q < ρ (projRot (-a) q))
    (hc : ∀ q ∈ projLine U ∩ projRot c '' projLine U, ρ q < ρ (projRot (-c) q)) :
    ∀ q ∈ projLine U ∩ projRot (a + c) '' projLine U, ρ q < ρ (projRot (-(a + c)) q) := by
  obtain ⟨q, hq, hq'⟩ := htri
  -- the composition law at the transferred angle
  have hkey : projRot (-(a + c)) q = projRot (-c) (projRot (-a) q) := by
    have h := projRot_add_apply (-c) (-a) q
    rw [show (-c + -a : ℝ) = -(a + c) by ring] at h
    exact h
  -- the witness `q` of `htri` is a point of the target set: `projRot (-(a+c)) q` lies in `projLine U`
  have hmem : projRot (-(a + c)) q ∈ projLine U := by
    rw [hkey]
    obtain ⟨x, hx, hxq⟩ := hq'.2
    have hid : projRot (-c) (projRot c x) = x := by
      have h := projRot_add_apply (-c) c x
      rw [neg_add_cancel, projRot_zero_apply] at h
      exact h.symm
    rw [← hxq, hid]
    exact hx
  have hqL : q ∈ projLine U ∩ projRot (a + c) '' projLine U :=
    ⟨hq.1, ⟨projRot (-(a + c)) q, hmem, by
      have h := projRot_add_apply (a + c) (-(a + c)) q
      rw [add_neg_cancel, projRot_zero_apply] at h
      exact h.symm⟩⟩
  -- the chain of comparisons at `q`: `ρ q < ρ (projRot (-a) q) < ρ (projRot (-(a+c)) q)`
  have hfq : ρ q - ρ (projRot (-(a + c)) q) < 0 := by
    have h1 : ρ q < ρ (projRot (-a) q) := ha q hq
    have h2 : ρ (projRot (-a) q) < ρ (projRot (-c) (projRot (-a) q)) := hc _ hq'
    rw [hkey]
    linarith
  -- the difference is continuous and nowhere zero on the target set, so its sign is constant there
  have hcont : Continuous (fun p => ρ p - ρ (projRot (-(a + c)) p)) :=
    hρ.sub (hρ.comp (prpt_continuous_projRot _))
  rcases prpt_sign_const hLpre hcont.continuousOn
      (fun p hp => sub_ne_zero.mpr (hne p hp)) with hpos | hneg
  · exact absurd (hpos q hqL) (not_lt.mpr (le_of_lt hfq))
  · intro p hp
    have h := hneg p hp
    linarith

end Work.Drive
