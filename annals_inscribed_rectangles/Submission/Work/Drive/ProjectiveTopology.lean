import Mathlib
import Submission.Work.Drive.ProjectiveDefs
import Submission.Work.Drive.sphere_quotient_projective

/-!
# The topology of projective space

Hugelmeyer's proof of his Theorem 2 (the total order on pairwise disjoint homologically non-trivial
projective planes) takes place in `ℝ × ℝP³`, and his fifth auxiliary result caps the configuration
Möbius strip so that the capped space is `ℝ × ℝP³`.  Mathlib's `Projectivization` is purely
linear-algebraic: it carries no topological structure, although the bricks of the model route
(`Work.Drive.projLine`, `Work.Drive.projOfUnit`, `Work.Drive.sphere_quotient_projective`,
`Work.Drive.projective_lines_meet_oddly`, `Work.Drive.projective_planes_meet_oddly`) all live in it.
This file supplies the missing topology, so that `ℝP³` (and every `ℝPⁿ`) is available as a
*topological* space for the capping and for the model of `Y ≅ ℝ × ℝP³`:

* `instTopologicalSpaceProjectivization` — the quotient topology on the projectivisation of a
  topological vector space (the quotient of the non-zero vectors by the action of the units of the
  field), with `continuous_projectivizationMk` for the canonical map;
* `T2Space` and `CompactSpace` for `Projectivization ℝ (EuclideanSpace ℝ (Fin (n+1)))`, i.e. `ℝPⁿ`.

The compactness comes from the model of `ℝPⁿ` as the quotient of the unit sphere `Sⁿ ⊆ ℝ^{n+1}` by
the antipodal involution: the map `projOfUnitSphere` sending a unit vector to the line it spans is a
continuous surjection from the compact sphere.  Hausdorffness comes from the continuous scale
invariant map `v ↦ (vᵢvⱼ/‖v‖²)ᵢⱼ`, whose fibres are exactly the scaling classes.
-/

namespace Work.Drive

open scoped LinearAlgebra.Projectivization

noncomputable section

section General

variable (K : Type*) (V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]

/-- **The quotient topology on the projectivisation.**  It is the quotient topology of the canonical
surjection from the non-zero vectors, i.e. the one for which `Projectivization.mk` is a quotient
map. -/
instance instTopologicalSpaceProjectivization : TopologicalSpace (Projectivization K V) :=
  instTopologicalSpaceQuotient

/-- The canonical map to the projectivisation is continuous. -/
lemma continuous_projectivizationMk :
    Continuous (fun p : {v : V // v ≠ 0} => Projectivization.mk K p.1 p.2) :=
  continuous_quotient_mk'

/-- Any two `Projectivization.mk`s of the same vector agree (the proofs of non-vanishing are
irrelevant). -/
lemma projectivizationMk_congr {v : V} {h₁ h₂ : v ≠ 0} :
    Projectivization.mk K v h₁ = Projectivization.mk K v h₂ :=
  congrArg (Quotient.mk'' (s₁ := projectivizationSetoid K V)) (Subtype.ext rfl)

omit [TopologicalSpace V] in
/-- Two non-zero vectors have the same image in the projectivisation exactly when one is a non-zero
multiple of the other. -/
lemma projectivizationSetoid_iff {a b : {v : V // v ≠ 0}} :
    projectivizationSetoid K V a b ↔ ∃ c : Kˣ, c • b.1 = a.1 := by
  change (MulAction.orbitRel Kˣ V) a.1 b.1 ↔ _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

/-- The scaling action of the units on the non-zero vectors is continuous, hence the scaling maps
are homeomorphisms of that (open) subspace. -/
instance instContinuousConstSMulUnitsNeZero [ContinuousConstSMul K V] :
    ContinuousConstSMul Kˣ {v : V // v ≠ 0} where
  continuous_const_smul c := by
    refine Continuous.congr ?_ (fun p => Subtype.ext rfl)
    exact Continuous.subtype_mk
      ((continuous_const_smul (c : K)).comp
        (continuous_subtype_val : Continuous (Subtype.val : {v : V // v ≠ 0} → V)))
      (fun p => smul_ne_zero (Units.ne_zero c) p.2)

/-- **The canonical map is an open quotient map.**  The saturation of an open set of non-zero
vectors under the scaling action of the units is the union of its images, hence open. -/
theorem isOpenMap_projectivizationMk [ContinuousConstSMul K V] :
    IsOpenMap (fun p : {v : V // v ≠ 0} => Projectivization.mk K p.1 p.2) := by
  have htop : instTopologicalSpaceProjectivization K V = TopologicalSpace.coinduced
      (fun p : {v : V // v ≠ 0} => Projectivization.mk K p.1 p.2) inferInstance := rfl
  intro U hU
  rw [htop, isOpen_coinduced]
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨y, hy, hxy⟩
  have hxy' : projectivizationSetoid K V y x := Quotient.exact hxy
  rw [show projectivizationSetoid K V y x ↔ ∃ c : Kˣ, c • x.1 = y.1 from by
    change (MulAction.orbitRel Kˣ V) y.1 x.1 ↔ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]] at hxy'
  obtain ⟨c, hc⟩ := hxy'
  refine ⟨(fun p : {v : V // v ≠ 0} => c⁻¹ • p) '' U, ?_, (isOpenMap_smul c⁻¹) U hU,
    ⟨y, hy, Subtype.ext ?_⟩⟩
  · rintro z ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    exact Quotient.sound (show projectivizationSetoid K V u (c⁻¹ • u) from by
      rw [show projectivizationSetoid K V u (c⁻¹ • u) ↔
          ∃ d : Kˣ, d • (c⁻¹ • u).1 = u.1 from by
        change (MulAction.orbitRel Kˣ V) u.1 (c⁻¹ • u).1 ↔ _
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]]
      exact ⟨c, by
        rw [show ((c⁻¹ • u : {v : V // v ≠ 0}) : V) = c⁻¹ • (u : V) from rfl,
          smul_smul, mul_inv_cancel, one_smul]⟩)
  · show c⁻¹ • y.1 = x.1
    rw [← hc, smul_smul, inv_mul_cancel, one_smul]

end General

/-- The projectivisation of a second countable space is second countable (the canonical map is an
open quotient map). -/
instance instSecondCountableTopologyProjectivization (K : Type*) (V : Type*) [DivisionRing K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] [SecondCountableTopology V]
    [ContinuousConstSMul K V] : SecondCountableTopology (Projectivization K V) := by
  haveI : SecondCountableTopology {v : V // v ≠ 0} :=
    inferInstanceAs (SecondCountableTopology {v : V | v ≠ 0})
  exact TopologicalSpace.Quotient.secondCountableTopology (isOpenMap_projectivizationMk K V)

/-! ## `ℝPⁿ` from the unit sphere -/

section Sphere

/-- The `(n+1)`-dimensional Euclidean space. -/
abbrev Eucl (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

/-- The unit sphere of `ℝ^{n+1}`, whose quotient by the antipodal involution is `ℝPⁿ`. -/
abbrev unitSphere (n : ℕ) := Metric.sphere (0 : Eucl n) 1

/-- A point of the unit sphere has norm `1`. -/
lemma norm_coe_unitSphere {n : ℕ} (v : unitSphere n) : ‖v.1‖ = 1 := by
  have h := Metric.mem_sphere.mp v.2
  simpa [dist_eq_norm] using h

/-- The map `Sⁿ → ℝPⁿ` sending a unit vector to the line that it spans. -/
def projOfUnitSphere {n : ℕ} (v : unitSphere n) : Projectivization ℝ (Eucl n) :=
  Projectivization.mk ℝ v.1 (norm_eq_one_ne_zero (norm_coe_unitSphere v))

/-- `projOfUnitSphere` is `projOfUnit` (`Work.Drive.ProjectiveDefs`) applied to a point of the unit
sphere. -/
lemma projOfUnitSphere_eq {n : ℕ} (v : unitSphere n) :
    projOfUnitSphere v = projOfUnit v.1 (norm_coe_unitSphere v) :=
  projOfUnit_eq_mk v.1 (norm_coe_unitSphere v) _

/-- The map `Sⁿ → ℝPⁿ` is continuous. -/
lemma continuous_projOfUnitSphere {n : ℕ} : Continuous (projOfUnitSphere (n := n)) := by
  have hincl : Continuous (fun v : unitSphere n =>
      (⟨v.1, norm_eq_one_ne_zero (norm_coe_unitSphere v)⟩ : {w : Eucl n // w ≠ 0})) :=
    Continuous.subtype_mk
      (continuous_subtype_val : Continuous (Subtype.val : unitSphere n → Eucl n))
      (fun v => norm_eq_one_ne_zero (norm_coe_unitSphere v))
  refine Continuous.congr ((continuous_projectivizationMk ℝ (Eucl n)).comp hincl) ?_
  intro v
  exact projectivizationMk_congr ℝ (Eucl n)

/-- **`ℝPⁿ` is covered by the unit sphere**: scaling a representative to norm `1` does not change
its class. -/
lemma surjective_projOfUnitSphere {n : ℕ} : Function.Surjective (projOfUnitSphere (n := n)) := by
  intro p
  have hc : ‖p.rep‖ ≠ 0 := norm_ne_zero_iff.mpr p.rep_nonzero
  have hnorm : ‖(‖p.rep‖)⁻¹ • p.rep‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hc]
  refine ⟨⟨(‖p.rep‖)⁻¹ • p.rep, by simpa [Metric.mem_sphere, dist_eq_norm] using hnorm⟩, ?_⟩
  rw [projOfUnitSphere_eq,
    projOfUnit_eq_mk ((‖p.rep‖)⁻¹ • p.rep) hnorm
      (smul_ne_zero (inv_ne_zero hc) p.rep_nonzero),
    mk_smul_eq_mk (‖p.rep‖)⁻¹ (inv_ne_zero hc) p.rep p.rep_nonzero]
  exact Projectivization.mk_rep p

/-- **`ℝPⁿ` is compact**: it is a continuous image of the compact unit sphere. -/
instance instCompactSpaceProjectivizationEuclidean (n : ℕ) :
    CompactSpace (Projectivization ℝ (Eucl n)) where
  isCompact_univ := by
    have h : IsCompact (Set.range (projOfUnitSphere (n := n))) :=
      isCompact_range (continuous_projOfUnitSphere (n := n))
    rwa [Set.range_eq_univ.mpr (surjective_projOfUnitSphere (n := n))] at h

/-! ### Hausdorffness

The normalised outer product of a non-zero vector is continuous, invariant under non-zero scaling,
and separates the scaling classes; hence it factors through a continuous *injection* of `ℝPⁿ` into a
Hausdorff space, which gives the Hausdorff property of `ℝPⁿ`. -/

/-- The normalised outer product `(vᵢvⱼ/‖v‖²)ᵢⱼ` of a vector: a continuous function of `v` which is
invariant under non-zero scaling, and which separates the scaling classes. -/
def projKey {n : ℕ} (v : Eucl n) : Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j => (‖v‖ ^ 2)⁻¹ * (v.ofLp i * v.ofLp j)

lemma continuous_projKey {n : ℕ} :
    Continuous (fun p : {v : Eucl n // v ≠ 0} => projKey p.1) := by
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro j
  refine Continuous.mul ?_ ?_
  · refine Continuous.inv₀ (by fun_prop) ?_
    intro p
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr p.2)
  · fun_prop

/-- `projKey` is invariant under non-zero scaling. -/
lemma projKey_smul {n : ℕ} (c : ℝˣ) (v : Eucl n) : projKey (c • v) = projKey v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [projKey]
  funext i j
  have hco : (c • v).ofLp i = (c : ℝ) * v.ofLp i := by
    rw [Units.smul_def, PiLp.smul_apply, smul_eq_mul]
  have hcoj : (c • v).ofLp j = (c : ℝ) * v.ofLp j := by
    rw [Units.smul_def, PiLp.smul_apply, smul_eq_mul]
  have hnv : ‖(c • v : Eucl n)‖ ^ 2 = (c : ℝ) ^ 2 * ‖v‖ ^ 2 := by
    rw [Units.smul_def, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [projKey, hnv, hco, hcoj]
  have hc : (c : ℝ) ≠ 0 := Units.ne_zero c
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  field_simp

/-- **`projKey` separates the scaling classes**: two non-zero vectors with the same normalised outer
product are non-zero multiples of one another. -/
lemma exists_smul_eq_of_projKey_eq {n : ℕ} {v w : Eucl n} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : projKey v = projKey w) : ∃ c : ℝˣ, c • w = v := by
  have hcoord : ∀ i j : Fin (n + 1),
      (‖v‖ ^ 2)⁻¹ * (v.ofLp i * v.ofLp j) = (‖w‖ ^ 2)⁻¹ * (w.ofLp i * w.ofLp j) :=
    fun i j => congrFun (congrFun h i) j
  have hnorm_v : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnorm_w : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  obtain ⟨i, hi⟩ : ∃ i, v.ofLp i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (by ext k; simpa using hcon k)
  have hwi : w.ofLp i ≠ 0 := by
    intro h0
    have h1 := hcoord i i
    rw [h0, mul_zero, mul_zero] at h1
    exact (mul_ne_zero (inv_ne_zero (pow_ne_zero 2 hnorm_v)) (mul_ne_zero hi hi)) h1
  -- the linear relation `vᵢvⱼ‖w‖² = wᵢwⱼ‖v‖²` for every `j`
  have hrel : ∀ j : Fin (n + 1), v.ofLp i * v.ofLp j * ‖w‖ ^ 2 = w.ofLp i * w.ofLp j * ‖v‖ ^ 2 := by
    intro j
    have h1 := hcoord i j
    field_simp at h1
    linear_combination h1
  refine ⟨Units.mk0 ((w.ofLp i * ‖v‖ ^ 2) / (v.ofLp i * ‖w‖ ^ 2)) (by
    exact div_ne_zero (mul_ne_zero hwi (pow_ne_zero 2 hnorm_v))
      (mul_ne_zero hi (pow_ne_zero 2 hnorm_w))), ?_⟩
  ext j
  rw [Units.smul_def, Units.val_mk0, PiLp.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hi (pow_ne_zero 2 hnorm_w))]
  nlinarith [hrel j]

/-- **`ℝPⁿ` is Hausdorff.**  The continuous scale invariant map `projKey` factors through a
continuous injection of `ℝPⁿ` into the Hausdorff space `ℝ^{(n+1)×(n+1)}`. -/
instance instT2SpaceProjectivizationEuclidean (n : ℕ) :
    T2Space (Projectivization ℝ (Eucl n)) := by
  have hF : Continuous (fun p : {v : Eucl n // v ≠ 0} => projKey p.1) := continuous_projKey
  have hinv : ∀ a b : {v : Eucl n // v ≠ 0},
      projectivizationSetoid ℝ (Eucl n) a b → projKey a.1 = projKey b.1 := by
    intro a b hab
    rw [projectivizationSetoid_iff] at hab
    obtain ⟨c, hc⟩ := hab
    rw [← hc, projKey_smul]
  have hcont : Continuous (Quotient.lift (fun p : {v : Eucl n // v ≠ 0} => projKey p.1) hinv) :=
    hF.quotient_lift hinv
  have hinj : Function.Injective
      (Quotient.lift (fun p : {v : Eucl n // v ≠ 0} => projKey p.1) hinv) := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | h p =>
      induction b using Quotient.inductionOn with
      | h q =>
        have hpq : projKey p.1 = projKey q.1 := hab
        obtain ⟨c, hc⟩ := exists_smul_eq_of_projKey_eq p.2 q.2 hpq
        exact Quotient.sound ((projectivizationSetoid_iff (K := ℝ) (V := Eucl n)).mpr ⟨c, hc⟩)
  rw [t2Space_iff]
  intro x y hne
  exact separated_by_continuous hcont fun h => hne (hinj h)

end Sphere

end

end Work.Drive
