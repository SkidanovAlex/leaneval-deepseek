import Mathlib
import Submission.Work.Drive.sard_weak_empty_interior
import Submission.Work.Drive.SeamSweep
import Submission.Work.Drive.meet32_bordism_invariance

/-!
# The homotopy half of the ends clause: existence by a generic perturbation

`Work.Drive.HasClassLinearization` (`Submission/Work/Drive/classTripleOdd.lean`) bundles, for each of
the three planes, a homotopy `H k` from the class map of the plane to the disk model of a *linear*
projective plane together with the transversality data (`Meet3Hyp`) of the encoded chains.
`Submission/Work/Drive/ENDS_ODD_STATUS.md` §2 calls the *homotopy* half "the `[ℝP²,ℝP³] ≅ ℤ/2` wall".
This file shows that the homotopy half is **not** a wall: given two lifts `V`, `W` of the two end class
maps, a **common** perturbation `χ • p` of both makes the straight-line interpolation of the lifts
nonvanishing.

The mechanism (see `Submission/Work/Drive/ENDS_HOMOTOPY_NOTES.md`):

* the vanishing condition `(1-s) • V y + s • W y + (χ y) • p = 0` **solves for `p`** wherever
  `χ y ≠ 0`, by `p = -((1-s) • V y + s • W y) / (χ y)`; the solving map has a *three*-dimensional
  domain `(s, y)` and values in the *four*-dimensional `Eucl 3`, so its image has empty interior
  (`Work.Drive.interior_image_empty_of_contDiffOn` below, from the workspace's Hausdorff-dimension
  form of Sard `Work.Drive.interior_eq_empty_of_holder`);
* where `χ y = 0` the condition is independent of `p` and is excluded by the hypothesis `hgood` —
  the one place where the essentiality of the two end class maps enters (through the seam, not through
  obstruction theory).
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

/-- **A smooth image of a lower-dimensional set has empty interior.**  If `f : E → F` is smooth on an
open set `V ⊇ K` and `finrank ℝ E < finrank ℝ F`, then `f '' K` has empty interior: `f` is locally
`1`-Lipschitz, hence locally `1`-Hölder, and `dimH (f '' K) ≤ finrank E < finrank F`. -/
theorem interior_image_empty_of_contDiffOn {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hfin : Module.finrank ℝ E < Module.finrank ℝ F) {V : Set E} (hV : IsOpen V)
    {f : E → F} (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f V) {K : Set E} (hK : K ⊆ V) :
    interior (f '' K) = ∅ := by
  refine interior_eq_empty_of_holder f K 1 (by norm_num) ?_ ?_
  · intro x hx
    obtain ⟨C, t, ht, hlip⟩ :=
      ((hf.contDiffAt (hV.mem_nhds (hK hx))).of_le (by simp)).exists_lipschitzOnWith
    exact ⟨C, K ∩ t, inter_mem_nhdsWithin K ht,
      by simpa using (hlip.mono (Set.inter_subset_right (s := K))).holderOnWith⟩
  · rw [Nat.cast_one, div_one]
    exact_mod_cast hfin

/-- The straight-line interpolation of two lifts of a class map. -/
def interpLiftP (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (s : ℝ)
    (y : EuclideanSpace ℝ (Fin 2)) : Eucl 3 := (1 - s) • V y + s • W y

@[simp] lemma interpLiftP_zero (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (y : EuclideanSpace ℝ (Fin 2)) : interpLiftP V W 0 y = V y := by simp [interpLiftP]

@[simp] lemma interpLiftP_one (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (y : EuclideanSpace ℝ (Fin 2)) : interpLiftP V W 1 y = W y := by simp [interpLiftP]

lemma contDiff_interpLiftP {V W : EuclideanSpace ℝ (Fin 2) → Eucl 3}
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => interpLiftP V W q.1 q.2) := by
  unfold interpLiftP
  exact ((contDiff_const.sub contDiff_fst).smul (hV.comp contDiff_snd)).add
    (contDiff_fst.smul (hW.comp contDiff_snd))

/-- The perturbation vector that destroys the nonvanishing at a pair `(s, y)` with `χ y ≠ 0`. -/
def pertSolve (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (χ : EuclideanSpace ℝ (Fin 2) → ℝ) :
    ℝ × EuclideanSpace ℝ (Fin 2) → Eucl 3 :=
  fun q => -(((χ q.2)⁻¹) • interpLiftP V W q.1 q.2)

lemma pertSolve_smul_eq (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (χ : EuclideanSpace ℝ (Fin 2) → ℝ) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2))
    (h : χ y ≠ 0) : (χ y) • pertSolve V W χ (s, y) = -(interpLiftP V W s y) := by
  simp only [pertSolve]
  rw [smul_neg, smul_smul, mul_inv_cancel₀ h, one_smul]

/-- **The perturbation lemma.**  For smooth lifts `V`, `W` and a smooth weight `χ` such that the
*unperturbed* interpolation never vanishes at the zeros of `χ`, there is a single perturbation vector
`p` for which the perturbed interpolation `(1-s) • V y + s • W y + (χ y) • p` is nonvanishing on the
whole box `[0,1] × □`. -/
theorem exists_perturbation_interpLiftP_ne_zero
    (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (χ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hgood : ∀ y ∈ Submission.Drive.unitBox 1, χ y = 0 →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, interpLiftP V W s y ≠ 0) :
    ∃ p : Eucl 3, ∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), s ∈ Set.Icc (0 : ℝ) 1 →
      y ∈ Submission.Drive.unitBox 1 → interpLiftP V W s y + (χ y) • p ≠ 0 := by
  classical
  have hfin : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 2)) < Module.finrank ℝ (Eucl 3) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    norm_num
  set Vset : Set (ℝ × EuclideanSpace ℝ (Fin 2)) := {q | χ q.2 ≠ 0} with hVset
  have hVopen : IsOpen Vset := by
    rw [hVset]
    exact (isOpen_ne (x := (0 : ℝ))).preimage (hχ.continuous.comp continuous_snd)
  have hsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pertSolve V W χ) Vset := by
    refine ContDiffOn.neg ?_
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => (χ q.2)⁻¹) Vset :=
      ContDiffOn.inv (hχ.comp_contDiffOn contDiffOn_snd) (fun q hq => hq)
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => interpLiftP V W q.1 q.2) Vset :=
      (contDiff_interpLiftP hV hW).contDiffOn
    exact h1.smul h2
  set K : Set (ℝ × EuclideanSpace ℝ (Fin 2)) :=
    {q | q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ Submission.Drive.unitBox 1 ∧ χ q.2 ≠ 0} with hK
  have hKV : K ⊆ Vset := fun q hq => hq.2.2
  have hemp : interior (pertSolve V W χ '' K) = ∅ :=
    interior_image_empty_of_contDiffOn hfin hVopen hsmooth hKV
  have hne : (pertSolve V W χ '' K) ≠ Set.univ := by
    intro h
    have h1 : interior (pertSolve V W χ '' K) = Set.univ := by rw [h, interior_univ]
    rw [hemp] at h1
    exact Set.univ_nonempty.ne_empty h1.symm
  obtain ⟨p, hp⟩ := Set.nonempty_compl.mpr hne
  refine ⟨p, ?_⟩
  intro s y hs hy hzero
  have hχne : χ y ≠ 0 := by
    intro h0
    have hz : interpLiftP V W s y = 0 := by
      rw [h0, zero_smul, add_zero] at hzero
      exact hzero
    exact hgood y hy h0 s hs hz
  refine hp ⟨(s, y), ⟨hs, hy, hχne⟩, ?_⟩
  have h1 : (χ y) • pertSolve V W χ (s, y) = (χ y) • p := by
    rw [pertSolve_smul_eq V W χ s y hχne]
    have h2 : interpLiftP V W s y = -((χ y) • p) := by
      rw [eq_neg_iff_add_eq_zero]; exact hzero
    rw [h2, neg_neg]
  have h2 : pertSolve V W χ (s, y) = p := by
    have := congrArg (fun v => ((χ y)⁻¹) • v) h1
    simpa [smul_smul, inv_mul_cancel₀ hχne] using this
  rw [h2]

/-! ## The three families of the homotopy, simultaneously nonvanishing

The homotopy from the class map `[V]` to the class map `[W]` is the concatenation of the two
*perturbation paths* `t ↦ [V + t • χ • p]`, `t ↦ [W + t • χ • p]` and the *perturbed interpolation*
`s ↦ [(1-s) • V + s • W + χ • p]`.  All three families are nonvanishing for a suitable `p`; each
family has its own solving map, and the three bad sets (each the image of a smooth map from a
`3`-dimensional source) have empty interior. -/

/-- The solving map of the perturbation path of `V`: `t ↦ [V + t • χ • p]` vanishes at `(t,y)` with
`t > 0`, `χ y ≠ 0` exactly when `p = pathSolve V χ (t,y)`. -/
def pathSolve (V : EuclideanSpace ℝ (Fin 2) → Eucl 3) (χ : EuclideanSpace ℝ (Fin 2) → ℝ) :
    ℝ × EuclideanSpace ℝ (Fin 2) → Eucl 3 :=
  fun q => -(((q.1 * χ q.2))⁻¹ • V q.2)

lemma pathSolve_smul_eq (V : EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (χ : EuclideanSpace ℝ (Fin 2) → ℝ) (t : ℝ) (y : EuclideanSpace ℝ (Fin 2))
    (h : t * χ y ≠ 0) : (t * χ y) • pathSolve V χ (t, y) = -(V y) := by
  simp only [pathSolve]
  rw [smul_neg, smul_smul, mul_inv_cancel₀ h, one_smul]

lemma contDiff_pathSolve {V : EuclideanSpace ℝ (Fin 2) → Eucl 3}
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {χ : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pathSolve V χ)
      {q : ℝ × EuclideanSpace ℝ (Fin 2) | q.1 * χ q.2 ≠ 0} := by
  refine ContDiffOn.neg ?_
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => (q.1 * χ q.2)⁻¹)
      {q : ℝ × EuclideanSpace ℝ (Fin 2) | q.1 * χ q.2 ≠ 0} :=
    ContDiffOn.inv ((contDiff_fst.mul (hχ.comp contDiff_snd)).contDiffOn) (fun q hq => hq)
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 2) => V q.2)
      {q : ℝ × EuclideanSpace ℝ (Fin 2) | q.1 * χ q.2 ≠ 0} := (hV.comp contDiff_snd).contDiffOn
  exact h1.smul h2

end

end Work.Drive
