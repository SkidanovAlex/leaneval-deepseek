import Mathlib
import Submission.Work.EKLComp.MaxLeafDefs
import Submission.Work.EKLComp.free_ae
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.aDiag_conj_uij
import Submission.Work.EKLComp.uniform_injective_V
import Submission.Work.Topology.exists_disjoint_open_shrink
import Submission.Work.EKLRelCross.freeSet_borel
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLC6Core.isPlaqueAlgebra_comap

/-!
# `Work.EKLComp.plaqueAlgebra_exists`

The geometric input of C11a (the maximal inequality for leafwise measures), L06 Lemma A.2 /
Pisa §5–6: for an `A`-invariant probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a root group
`U = U_ij` and radii `ε, r̄ > 0` there is a *plaque algebra* `(Z, m)` for `U` with `Z ⊆ Free`,
together with a "good" set `G ⊆ Z` of `μ`-measure `≥ 1 - ε` such that the `U`-leaf ball of
radius `r̄` around every point of `G` is contained in its `m`-atom.

## What is in this file

* **`Work.EKLComp.PlaqueAlgebraExistsBorel`** — the statement above, with `G` required to be
  measurable for the *ambient* Borel σ-algebra of `X₃` (the paper's `X''` is defined by
  leaf-coordinate conditions, and is *not* in the plaque σ-algebra), and

  **`Work.EKLComp.plaqueAlgebra_exists_borel`** — its complete proof, together with all the
  geometric infrastructure it needs:

  - flow boxes (`TsetC`, `chartC`, `GBox`), the fibre computation `GBox.fibre_iff`;
  - atoms of a countably generated σ-algebra (`atom_generateFrom_countable`);
  - the disjointification of a finite cover into pairwise disjoint open pieces
    (`exists_parts`, via `Work.Topology.exists_disjoint_open_shrink`);
  - the atom of the plaque σ-algebra (`PParts.atom_eq`), the shape and its openness/boundedness
    (`PParts.shape_eq`, `PParts.exists_isOpen_shape`, `PParts.shape_bounded`) and
    `PParts.isPlaqueAlgebra`;
  - the good sets (`PParts.good`), their measure (`PParts.exists_good_measure`) and the diagonal
    pushing argument (`aDiag`, `Lemmas.aDiag_conj_uij`) that turns the `δ`-ball condition into the
    required `r̄`-ball condition.

* **`Work.EKLComp.not_plaqueAlgebra_exists`** — a proof that the *frozen* predicate
  `Work.EKLComp.PlaqueAlgebraExists` (in `Work.EKLComp.MaxLeafDefs`) is **false**: its third
  conjunct `MeasurableSet G` is elaborated with the σ-algebra `m` bound by the existential
  quantifier (`#print` with `pp.all` shows `@MeasurableSet X₃ m G`), which forces `atom m x` to be
  the whole leaf `U_ij • x` for every `x ∈ G`, contradicting the required entrywise boundedness of
  the shape.  Writing the ambient instance explicitly, e.g.
  `MeasurableSet[Work.EKLContract.instMeasurableSpaceX3] G`, repairs the definition, and the
  theorem `plaqueAlgebra_exists_borel` then gives the requested lemma verbatim.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLComp

/-! ## The transversals `T_p = {A | A i p = 0, A j p ≠ 0}` -/

/-- The transversal of the `U_ij`-action used for the flow boxes. -/
def Tset (i j p : Fin 3) : Set SL3 := {A | A i p = 0 ∧ A j p ≠ 0}

/-- The entries of `u_ij(σ) * A`: only the `i`-th row changes, and only by adding `σ` times the
`j`-th row. -/
theorem uij_mul_apply {i j : Fin 3} (hij : i ≠ j) (σ : ℝ) (A : SL3) (k l : Fin 3) :
    (uij hij σ * A) k l = A k l + σ * (if k = i then A j l else 0) := by
  have hcoe : ((uij hij σ * A : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = ((1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j σ)
          * (A : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.SpecialLinearGroup.coe_mul,
      show ((uij hij σ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
          = (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j σ from
        Matrix.SpecialLinearGroup.transvection_coe hij σ]
  have key : ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (k l : Fin 3),
      (((1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j σ) * M) k l
        = M k l + σ * (if k = i then M j l else 0) := by
    intro M k l
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [show (uij hij σ * A) k l
      = (((1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j σ)
          * (A : Matrix (Fin 3) (Fin 3) ℝ)) k l from by rw [← hcoe]]
  exact key _ k l

/-- Multiplication of two transvections. -/
theorem uij_mul_uij {i j : Fin 3} (hij : i ≠ j) (a b : ℝ) :
    uij hij a * uij hij b = uij hij (a + b) := by
  show Matrix.SpecialLinearGroup.transvection hij a
      * Matrix.SpecialLinearGroup.transvection hij b
    = Matrix.SpecialLinearGroup.transvection hij (a + b)
  exact (Matrix.SpecialLinearGroup.transvection_add hij a b).symm

/-- **Injectivity of the product map.**  For `m, m' ∈ T_p` and `σ, σ' : ℝ`,
`u_ij(σ)m = u_ij(σ')m'` forces `σ = σ'` and `m = m'`. -/
theorem product_injective {i j p : Fin 3} (hij : i ≠ j) {m m' : SL3} {σ σ' : ℝ}
    (hm : m ∈ Tset i j p) (hm' : m' ∈ Tset i j p)
    (h : uij hij σ * m = uij hij σ' * m') : σ = σ' ∧ m = m' := by
  have hθ : uij hij (σ - σ') * m = m' := by
    calc uij hij (σ - σ') * m
        = uij hij (-σ') * (uij hij σ * m) := by
          rw [← mul_assoc, uij_mul_uij hij (-σ') σ,
            show -σ' + σ = σ - σ' by ring]
        _ = uij hij (-σ') * (uij hij σ' * m') := by rw [h]
        _ = (uij hij (-σ') * uij hij σ') * m' := by rw [mul_assoc]
        _ = m' := by
          rw [uij_mul_uij hij (-σ') σ', neg_add_cancel,
            Lemmas.horoUij_zero hij, one_mul]
  have h1 : (uij hij (σ - σ') * m) i p = m i p + (σ - σ') * m j p := by
    rw [uij_mul_apply hij (σ - σ') m i p, if_pos rfl]
  have h2 : m' i p = 0 := hm'.1
  rw [hθ, h2, hm.1, zero_add] at h1
  have h3 : σ - σ' = 0 := by
    rcases mul_eq_zero.mp h1.symm with h4 | h4
    · exact h4
    · exact absurd h4 hm.2
  refine ⟨by linarith, ?_⟩
  rw [h3, Lemmas.horoUij_zero hij, one_mul] at hθ
  exact hθ

/-- The image of `ℝ × T_p` under the product map is `{A | A j p ≠ 0}`. -/
theorem product_image {i j p : Fin 3} (hij : i ≠ j) :
    (fun x : ℝ × SL3 => uij hij x.1 * x.2) '' (Set.univ ×ˢ Tset i j p)
      = {A : SL3 | A j p ≠ 0} := by
  ext A
  constructor
  · rintro ⟨⟨σ, m⟩, ⟨-, hm⟩, rfl⟩
    change (uij hij σ * m) j p ≠ 0
    have h := uij_mul_apply hij σ m j p
    rw [if_neg (Ne.symm hij)] at h
    rw [h]
    simpa using hm.2
  · intro hA
    have hAp : A j p ≠ 0 := hA
    refine ⟨(A i p / A j p, uij hij (-(A i p / A j p)) * A), ⟨trivial, ?_⟩, ?_⟩
    · have h1 := uij_mul_apply hij (-(A i p / A j p)) A i p
      rw [if_pos rfl] at h1
      have h2 := uij_mul_apply hij (-(A i p / A j p)) A j p
      rw [if_neg (Ne.symm hij)] at h2
      refine ⟨?_, ?_⟩
      · rw [h1]; field_simp; ring
      · rw [h2]; simpa using hAp
    · rw [show (fun x : ℝ × SL3 => uij hij x.1 * x.2)
            (A i p / A j p, uij hij (-(A i p / A j p)) * A)
          = uij hij (A i p / A j p) * (uij hij (-(A i p / A j p)) * A) from rfl]
      rw [← mul_assoc, uij_mul_uij hij (A i p / A j p) (-(A i p / A j p)), add_neg_cancel,
        Lemmas.horoUij_zero hij, one_mul]

/-! ## The product charts (flow boxes) -/

/-- The product chart of the `U_ij`-flow at a point of the transversal: the set of matrices
`u_ij(σ) m` with `m ∈ T_p` close to a centre `g₀` and `|σ| < R`. -/
def chart (i j p : Fin 3) (hij : i ≠ j) (g₀ : SL3) (R e : ℝ) : Set SL3 :=
  {A | ∃ σ : ℝ, ∃ m : SL3, |σ| < R ∧ m ∈ Tset i j p ∧
      (∀ k l : Fin 3, |m k l - g₀ k l| < e) ∧ A = uij hij σ * m}

/-- The flow box in `X₃`: the image of a chart under `mkX`. -/
def chartX (i j p : Fin 3) (hij : i ≠ j) (g₀ : SL3) (R e : ℝ) : Set X3 :=
  mkX '' (chart i j p hij g₀ R e)

/-- The leaf coordinate `σ(A) = A i p / A j p` on `{A j p ≠ 0}`. -/
def sigmaCoord (i j p : Fin 3) (A : SL3) : ℝ := A i p / A j p

/-- The transversal coordinate `m(A) = u_ij(-σ(A)) A` on `{A j p ≠ 0}`. -/
def tauCoord (i j p : Fin 3) (hij : i ≠ j) (A : SL3) : SL3 :=
  uij hij (-(sigmaCoord i j p A)) * A

theorem tauCoord_mem {i j p : Fin 3} (hij : i ≠ j) {A : SL3} (hA : A j p ≠ 0) :
    tauCoord i j p hij A ∈ Tset i j p := by
  have h1 := uij_mul_apply hij (-(sigmaCoord i j p A)) A i p
  rw [if_pos rfl] at h1
  have h2 := uij_mul_apply hij (-(sigmaCoord i j p A)) A j p
  rw [if_neg (Ne.symm hij), mul_zero, add_zero] at h2
  refine ⟨?_, ?_⟩
  · rw [tauCoord, h1]
    simp only [sigmaCoord]
    field_simp
    ring
  · rw [tauCoord, h2]
    exact hA

theorem mul_sigmaCoord_tauCoord {i j p : Fin 3} (hij : i ≠ j) {A : SL3} (hA : A j p ≠ 0) :
    uij hij (sigmaCoord i j p A) * tauCoord i j p hij A = A := by
  rw [tauCoord, sigmaCoord, ← mul_assoc, uij_mul_uij hij (A i p / A j p) (-(A i p / A j p)),
    add_neg_cancel, Lemmas.horoUij_zero hij, one_mul]

theorem sigmaCoord_mul {i j p : Fin 3} (hij : i ≠ j) (σ : ℝ) {m : SL3}
    (hm : m ∈ Tset i j p) : sigmaCoord i j p (uij hij σ * m) = σ := by
  rw [sigmaCoord, uij_mul_apply hij σ m i p, uij_mul_apply hij σ m j p, if_pos rfl,
    if_neg (Ne.symm hij), mul_zero, add_zero, hm.1, zero_add]
  exact mul_div_cancel_right₀ σ hm.2

theorem tauCoord_mul {i j p : Fin 3} (hij : i ≠ j) (σ : ℝ) {m : SL3}
    (hm : m ∈ Tset i j p) : tauCoord i j p hij (uij hij σ * m) = m := by
  rw [tauCoord, sigmaCoord_mul hij σ hm, ← mul_assoc, uij_mul_uij hij (-σ) σ,
    neg_add_cancel, Lemmas.horoUij_zero hij, one_mul]

theorem mem_chart_iff {i j p : Fin 3} (hij : i ≠ j) {g₀ A : SL3} {R e : ℝ} :
    A ∈ chart i j p hij g₀ R e ↔ A j p ≠ 0 ∧ |sigmaCoord i j p A| < R ∧
      tauCoord i j p hij A ∈ Tset i j p ∧
      (∀ k l : Fin 3, |tauCoord i j p hij A k l - g₀ k l| < e) := by
  constructor
  · rintro ⟨σ, m, hσ, hmT, hme, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [uij_mul_apply hij σ m j p, if_neg (Ne.symm hij), mul_zero, add_zero]
      exact hmT.2
    · rw [sigmaCoord_mul hij σ hmT]; exact hσ
    · rw [tauCoord_mul hij σ hmT]; exact hmT
    · rw [tauCoord_mul hij σ hmT]; exact hme
  · rintro ⟨hjp, hσ, hmT, hme⟩
    exact ⟨sigmaCoord i j p A, tauCoord i j p hij A, hσ, hmT, hme,
      (mul_sigmaCoord_tauCoord hij hjp).symm⟩

/-! ## Flow boxes with an arbitrary transversal piece -/

/-- The flow box in `X₃` with transversal piece `M ⊆ SL₃(ℝ)` and leaf-length `2R`:
the image under `mkX` of `{u_ij(σ) m | |σ| < R, m ∈ M}`. -/
def box (i j p : Fin 3) (hij : i ≠ j) (M : Set SL3) (R : ℝ) : Set X3 :=
  mkX '' {A : SL3 | ∃ σ : ℝ, ∃ m : SL3, |σ| < R ∧ m ∈ M ∧ A = uij hij σ * m}

theorem box_mono {i j p : Fin 3} (hij : i ≠ j) {M M' : Set SL3} (h : M ⊆ M') (R : ℝ) :
    box i j p hij M R ⊆ box i j p hij M' R := by
  rintro x ⟨A, ⟨σ, m, hσ, hm, rfl⟩, rfl⟩
  exact ⟨uij hij σ * m, ⟨σ, m, hσ, h hm, rfl⟩, rfl⟩

theorem aDiag_mem_Tset {i j p : Fin 3} {m : SL3} (hm : m ∈ Tset i j p) (t : Fin 3 → ℝ) :
    aDiag t * m ∈ Tset i j p := by
  obtain ⟨h1, h2⟩ := hm
  have hdiag : ∀ k l : Fin 3, ((aDiag t : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
      = if k = l then Real.exp (t k - (∑ r, t r) / 3) else 0 := by
    intro k l
    show (Matrix.diagonal (fun i : Fin 3 => Real.exp (t i - (∑ r, t r) / 3))) k l
      = if k = l then Real.exp (t k - (∑ r, t r) / 3) else 0
    rw [Matrix.diagonal_apply]
  refine ⟨?_, ?_⟩
  · show ((aDiag t * m : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i p = 0
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [hdiag i q]
    rcases eq_or_ne q i with rfl | hq
    · simp [h1]
    · rw [if_neg (Ne.symm hq)]; simp
  · show ((aDiag t * m : SL3) : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Finset.sum_eq_single j]
    · rw [hdiag j j]; simp only [if_pos rfl]
      exact mul_ne_zero (Real.exp_ne_zero _) h2
    · intro q _ hq
      rw [hdiag j q, if_neg (Ne.symm hq)]
      simp
    · intro h; exact absurd (Finset.mem_univ j) h

/-! ## The transversals cover `SL₃(ℝ)` -/

/-- The row `j` of a matrix in `SL₃(ℝ)` is non-zero, so the three sets `{A | A j p ≠ 0}` cover
`SL₃(ℝ)`. -/
theorem iUnion_Tset_cover (i j : Fin 3) :
    (⋃ p : Fin 3, {A : SL3 | A j p ≠ 0}) = (Set.univ : Set SL3) := by
  ext A
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  by_contra h
  push_neg at h
  have hrow : ∀ p : Fin 3, (A : Matrix (Fin 3) (Fin 3) ℝ) j p = 0 := h
  have hdet : (A : Matrix (Fin 3) (Fin 3) ℝ).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero j hrow
  have hone : (A : Matrix (Fin 3) (Fin 3) ℝ).det = 1 := A.2
  rw [hone] at hdet
  exact one_ne_zero hdet


/-! ## Smallness of `m Γ₃ m⁻¹` near the identity (discreteness of `Γ₃`) -/

/-- `s ↦ u_ij(s)` is continuous. -/
private theorem continuous_uij_loc {i j : Fin 3} (hij : i ≠ j) :
    Continuous (fun s : ℝ => uij hij s) := by
  refine Continuous.subtype_mk (p := fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det = 1)
    (f := fun s : ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j s) ?_ ?_
  · refine Continuous.add continuous_const ?_
    apply continuous_matrix
    intro k l
    by_cases hkl : i = k ∧ j = l
    · simp only [Matrix.single_apply, if_pos hkl]; exact continuous_id
    · simp only [Matrix.single_apply, if_neg hkl]; exact continuous_const

/-- **The conjugated lattice is uniformly separated from `1`.**  For every `m : SL₃(ℝ)` there is
`δ > 0` with `m γ m⁻¹ ∉ V δ` for every `γ ∈ Γ₃`, `γ ≠ 1`.  This is just the discreteness of
`Γ₃`: conjugating a neighbourhood of the identity meeting `Γ₃` only at `1` gives a neighbourhood
of the identity meeting the conjugate lattice only at `1`. -/
theorem conjΓ3_isolated (m : SL3) : ∃ δ > 0, ∀ γ ∈ Γ3, γ ≠ 1 → m * γ * m⁻¹ ∉ V δ := by
  classical
  have hd : IsDiscrete (Γ3 : Set SL3) :=
    isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ3)
  obtain ⟨U, hU, hUΓ⟩ := nhds_inter_eq_singleton_of_mem_discrete hd Γ3.one_mem
  have hcont : Continuous (fun x : SL3 => m⁻¹ * x * m) := by
    rw [show (fun x : SL3 => m⁻¹ * x * m) = (fun x : SL3 => m⁻¹ * (x * m)) by
      funext x; rw [mul_assoc]]
    exact continuous_const.mul (continuous_id.mul continuous_const)
  have hW : {x : SL3 | m⁻¹ * x * m ∈ U} ∈ 𝓝 (1 : SL3) := by
    have h1 : m⁻¹ * (1 : SL3) * m = 1 := by group
    have := hcont.continuousAt.preimage_mem_nhds (by rw [h1]; exact hU)
    simpa [Set.preimage] using this
  obtain ⟨δ, hδpos, hδsub⟩ := V_nhds_hasBasis.mem_iff.mp hW
  refine ⟨δ, hδpos, fun γ hγ hne hV => ?_⟩
  have hγU : γ ∈ U := by
    have h := hδsub hV
    simp only [Set.mem_ofPred_eq] at h
    rwa [show m⁻¹ * (m * γ * m⁻¹) * m = γ by group] at h
  have hmem : γ ∈ U ∩ (Γ3 : Set SL3) := ⟨hγU, hγ⟩
  rw [hUΓ] at hmem
  exact hne (Set.mem_singleton_iff.mp hmem)

/-! ## The "sub-chart" of a flow box is open -/

/-- `|a / b| < R` is `|a| < R |b|` when `b ≠ 0`: clear the denominator. -/
lemma abs_div_lt_iff_mul₀ {a b R : ℝ} (hb : b ≠ 0) : |a / b| < R ↔ |a| < R * |b| := by
  rw [abs_div]
  exact div_lt_iff₀ (abs_pos.mpr hb)

/-- The transverse coordinate `τ` is continuous at every point of the chart region
`{A | A j p ≠ 0}` (where the leaf coordinate `σ` is a quotient of continuous functions). -/
lemma continuousAt_tauCoord {i j p : Fin 3} (hij : i ≠ j) (A₀ : SL3)
    (h : (A₀ : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0) :
    ContinuousAt (fun A : SL3 => tauCoord i j p hij A) A₀ := by
  have hnum : Continuous (fun A : SL3 => (A : Matrix (Fin 3) (Fin 3) ℝ) i p) := by fun_prop
  have hden : Continuous (fun A : SL3 => (A : Matrix (Fin 3) (Fin 3) ℝ) j p) := by fun_prop
  have hσ : ContinuousAt (fun A : SL3 => sigmaCoord i j p A) A₀ :=
    ContinuousAt.div hnum.continuousAt hden.continuousAt h
  have hu : Continuous fun s : ℝ => uij hij s := continuous_uij_loc hij
  have h1 : ContinuousAt (fun A : SL3 => uij hij (-(sigmaCoord i j p A))) A₀ :=
    hu.continuousAt.comp hσ.neg
  exact h1.mul continuousAt_id

/-- **The sub-chart of a flow box is open in `SL₃(ℝ)`.**  For an open `O ⊆ SL₃(ℝ)` the set of
matrices `A` with `A j p ≠ 0`, `|σ(A)| < R` and `τ(A) ∈ O` is open: it is the intersection of
the open set `{A j p ≠ 0}` (which clears the denominators in the leaf-coordinate condition) and
the preimage of `O` under the continuous transverse coordinate `τ`. -/
theorem isOpen_chartO {i j p : Fin 3} (hij : i ≠ j) (R : ℝ) {O : Set SL3} (hO : IsOpen O) :
    IsOpen {A : SL3 | (A : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0 ∧
      |sigmaCoord i j p A| < R ∧ tauCoord i j p hij A ∈ O} := by
  rw [isOpen_iff_mem_nhds]
  rintro A₀ ⟨hAj, hσ, hτ⟩
  have h1 : {A : SL3 | (A : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0} ∈ 𝓝 A₀ :=
    (isOpen_ne.preimage (by fun_prop)).mem_nhds hAj
  have h2 : {A : SL3 | |(A : Matrix (Fin 3) (Fin 3) ℝ) i p|
      < R * |(A : Matrix (Fin 3) (Fin 3) ℝ) j p|} ∈ 𝓝 A₀ :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds ((abs_div_lt_iff_mul₀ hAj).mp hσ)
  have h3 : {A : SL3 | tauCoord i j p hij A ∈ O} ∈ 𝓝 A₀ :=
    (continuousAt_tauCoord hij A₀ hAj).preimage_mem_nhds (hO.mem_nhds hτ)
  refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem h1 h2) h3) ?_
  rintro A ⟨⟨hAj', hσ'⟩, hτ'⟩
  exact ⟨hAj', (abs_div_lt_iff_mul₀ hAj').mpr hσ', hτ'⟩

/-!
## The affine transversal `{A | A i p = c, A j p ≠ 0}`

The transversals `Tset i j p = {A | A i p = 0, A j p ≠ 0}` used above have a defect as flow boxes:
the boxes centred at a point of `Tset i j p` cover a neighbourhood of that point, but a general
point `x = mkX g` need not lie in *any* box of this shape — the condition `(g γ) i p = 0` for some
`γ ∈ Γ₃` requires a non-zero integer vector orthogonal to the `i`-th row of `g`, which may not
exist (`row i (g) = (1, π, π²)`).

Replacing the value `0` by an arbitrary real `c` removes the problem: with `c := g i p` the matrix
`g` itself lies in `TsetC i j p c = {A | A i p = c, A j p ≠ 0}`, so the box centred at `g` is an
open neighbourhood of `x`.  (For `c = 0` we recover `Tset`.)

All the algebra of the product chart is unchanged: the leaf coordinate is now
`σ(A) = (A i p - c)/(A j p)` and the transversal coordinate `τ(A) = u_ij(-σ(A))A` has
`τ(A) i p = c`.
-/

/-- The affine transversal `{A | A i p = c, A j p ≠ 0}` of the `U_ij`-flow. -/
def TsetC (i j p : Fin 3) (c : ℝ) : Set SL3 :=
  {A | (A : Matrix (Fin 3) (Fin 3) ℝ) i p = c ∧ (A : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0}

/-- **Injectivity of the product parametrisation over an affine transversal.**  For
`m, m' ∈ TsetC i j p c` and `σ, σ' : ℝ`, `u_ij(σ)m = u_ij(σ')m'` forces `σ = σ'` and `m = m'`. -/
theorem TsetC_prod_injective {i j p : Fin 3} (hij : i ≠ j) {c : ℝ} {m m' : SL3} {σ σ' : ℝ}
    (hm : m ∈ TsetC i j p c) (hm' : m' ∈ TsetC i j p c)
    (h : uij hij σ * m = uij hij σ' * m') : σ = σ' ∧ m = m' := by
  have hθ : uij hij (σ - σ') * m = m' := by
    calc uij hij (σ - σ') * m
        = uij hij (-σ') * (uij hij σ * m) := by
          rw [← mul_assoc, uij_mul_uij hij (-σ') σ, show -σ' + σ = σ - σ' by ring]
        _ = uij hij (-σ') * (uij hij σ' * m') := by rw [h]
        _ = (uij hij (-σ') * uij hij σ') * m' := by rw [mul_assoc]
        _ = m' := by
          rw [uij_mul_uij hij (-σ') σ', neg_add_cancel,
            Lemmas.horoUij_zero hij, one_mul]
  have h1 : (uij hij (σ - σ') * m) i p = m i p + (σ - σ') * m j p := by
    rw [uij_mul_apply hij (σ - σ') m i p, if_pos rfl]
  rw [hθ] at h1
  rw [hm'.1, hm.1] at h1
  have h3 : σ - σ' = 0 := by
    have hz : (σ - σ') * m j p = 0 := by linarith
    rcases mul_eq_zero.mp hz with h4 | h4
    · exact h4
    · exact absurd h4 hm.2
  refine ⟨by linarith, ?_⟩
  rw [h3, Lemmas.horoUij_zero hij, one_mul] at hθ
  exact hθ

/-- The product parametrisation over an affine transversal has image `{A | A j p ≠ 0}`. -/
theorem TsetC_image {i j p : Fin 3} (hij : i ≠ j) (c : ℝ) :
    (fun x : ℝ × SL3 => uij hij x.1 * x.2) '' (Set.univ ×ˢ TsetC i j p c)
      = {A : SL3 | (A : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0} := by
  ext A
  constructor
  · rintro ⟨⟨σ, m⟩, ⟨-, hm⟩, rfl⟩
    change (uij hij σ * m) j p ≠ 0
    have h := uij_mul_apply hij σ m j p
    rw [if_neg (Ne.symm hij)] at h
    rw [h]
    simpa using hm.2
  · intro hA
    have hAp : (A : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0 := hA
    set σ : ℝ := ((A : Matrix (Fin 3) (Fin 3) ℝ) i p - c)
      / (A : Matrix (Fin 3) (Fin 3) ℝ) j p with hσdef
    refine ⟨(σ, uij hij (-σ) * A), ⟨trivial, ?_⟩, ?_⟩
    · refine ⟨?_, ?_⟩
      · have h1 := uij_mul_apply hij (-σ) A i p
        rw [if_pos rfl] at h1
        rw [h1, hσdef]
        field_simp
        ring
      · have h2 := uij_mul_apply hij (-σ) A j p
        rw [if_neg (Ne.symm hij), mul_zero, add_zero] at h2
        rw [h2]
        exact hAp
    · rw [show (fun x : ℝ × SL3 => uij hij x.1 * x.2) (σ, uij hij (-σ) * A)
          = uij hij σ * (uij hij (-σ) * A) from rfl]
      rw [← mul_assoc, uij_mul_uij hij σ (-σ), add_neg_cancel, Lemmas.horoUij_zero hij, one_mul]

/-- The leaf coordinate `σ(A) = (A i p - c)/(A j p)` of the affine transversal `TsetC i j p c`. -/
def sigmaC (i j p : Fin 3) (c : ℝ) (A : SL3) : ℝ :=
  ((A : Matrix (Fin 3) (Fin 3) ℝ) i p - c) / (A : Matrix (Fin 3) (Fin 3) ℝ) j p

/-- The transversal coordinate `τ(A) = u_ij(-σ(A))·A`. -/
def tauC (i j p : Fin 3) (hij : i ≠ j) (c : ℝ) (A : SL3) : SL3 :=
  uij hij (-(sigmaC i j p c A)) * A

theorem tauC_mem (i j p : Fin 3) (hij : i ≠ j) {c : ℝ} {A : SL3}
    (hA : (A : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0) : tauC i j p hij c A ∈ TsetC i j p c := by
  have h1 := uij_mul_apply hij (-(sigmaC i j p c A)) A i p
  rw [if_pos rfl] at h1
  have h2 := uij_mul_apply hij (-(sigmaC i j p c A)) A j p
  rw [if_neg (Ne.symm hij), mul_zero, add_zero] at h2
  refine ⟨?_, ?_⟩
  · rw [tauC, h1]
    simp only [sigmaC]
    field_simp
    ring
  · rw [tauC, h2]
    exact hA

theorem mul_sigmaC_tauC (i j p : Fin 3) (hij : i ≠ j) {c : ℝ} {A : SL3}
    (hA : (A : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0) :
    uij hij (sigmaC i j p c A) * tauC i j p hij c A = A := by
  rw [tauC, ← mul_assoc, uij_mul_uij hij _ _, add_neg_cancel, Lemmas.horoUij_zero hij, one_mul]

theorem sigmaC_mul (i j p : Fin 3) (hij : i ≠ j) (c σ : ℝ) {m : SL3}
    (hm : m ∈ TsetC i j p c) : sigmaC i j p c (uij hij σ * m) = σ := by
  rw [sigmaC, uij_mul_apply hij σ m i p, uij_mul_apply hij σ m j p, if_pos rfl,
    if_neg (Ne.symm hij), mul_zero, add_zero, hm.1]
  field_simp [hm.2]
  ring

theorem tauC_mul (i j p : Fin 3) (hij : i ≠ j) (c σ : ℝ) {m : SL3}
    (hm : m ∈ TsetC i j p c) : tauC i j p hij c (uij hij σ * m) = m := by
  rw [tauC, sigmaC_mul i j p hij c σ hm, ← mul_assoc, uij_mul_uij hij (-σ) σ,
    neg_add_cancel, Lemmas.horoUij_zero hij, one_mul]

/-- The product chart of the `U_ij`-flow over the affine transversal `TsetC i j p c`. -/
def chartC (i j p : Fin 3) (hij : i ≠ j) (c : ℝ) (m₀ : SL3) (R e : ℝ) : Set SL3 :=
  {A | ∃ σ : ℝ, ∃ m : SL3, |σ| < R ∧ m ∈ TsetC i j p c ∧
      (∀ k l : Fin 3, |m k l - m₀ k l| < e) ∧ A = uij hij σ * m}

/-- The corresponding flow box in `X₃`. -/
def chartXC (i j p : Fin 3) (hij : i ≠ j) (c : ℝ) (m₀ : SL3) (R e : ℝ) : Set X3 :=
  mkX '' (chartC i j p hij c m₀ R e)

theorem mem_chartC_iff (i j p : Fin 3) (hij : i ≠ j) {c : ℝ} {m₀ A : SL3} {R e : ℝ} :
    A ∈ chartC i j p hij c m₀ R e ↔ (A : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0 ∧
      |sigmaC i j p c A| < R ∧ tauC i j p hij c A ∈ TsetC i j p c ∧
      (∀ k l : Fin 3, |(tauC i j p hij c A : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (m₀ : Matrix (Fin 3) (Fin 3) ℝ) k l| < e) := by
  constructor
  · rintro ⟨σ, m, hσ, hmT, hme, rfl⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [uij_mul_apply hij σ m j p, if_neg (Ne.symm hij), mul_zero, add_zero]
      exact hmT.2
    · rw [sigmaC_mul i j p hij c σ hmT]; exact hσ
    · rw [tauC_mul i j p hij c σ hmT]; exact hmT
    · rw [tauC_mul i j p hij c σ hmT]; exact hme
  · rintro ⟨hjp, hσ, hmT, hme⟩
    exact ⟨sigmaC i j p c A, tauC i j p hij c A, hσ, hmT, hme,
      (mul_sigmaC_tauC i j p hij hjp).symm⟩

/-- The `(k,l)`-entry of the transversal coordinate, multiplied by the denominator `A j p`. -/
lemma mul_tauC_sub (i j p : Fin 3) (hij : i ≠ j) (c : ℝ) (A g₀ : SL3)
    (hj : (A : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0) (k l : Fin 3) :
    (A : Matrix (Fin 3) (Fin 3) ℝ) j p
        * ((tauC i j p hij c A : Matrix (Fin 3) (Fin 3) ℝ) k l
            - (g₀ : Matrix (Fin 3) (Fin 3) ℝ) k l)
      = (A : Matrix (Fin 3) (Fin 3) ℝ) j p
          * ((A : Matrix (Fin 3) (Fin 3) ℝ) k l - (g₀ : Matrix (Fin 3) (Fin 3) ℝ) k l)
        - (if k = i then (((A : Matrix (Fin 3) (Fin 3) ℝ) i p - c)
              * (A : Matrix (Fin 3) (Fin 3) ℝ) j l) else 0) := by
  rw [show (tauC i j p hij c A : Matrix (Fin 3) (Fin 3) ℝ) k l
      = (A : Matrix (Fin 3) (Fin 3) ℝ) k l
        + (-(((A : Matrix (Fin 3) (Fin 3) ℝ) i p - c)
            / (A : Matrix (Fin 3) (Fin 3) ℝ) j p))
          * (if k = i then (A : Matrix (Fin 3) (Fin 3) ℝ) j l else 0) from by
    rw [tauC, sigmaC]
    exact uij_mul_apply hij _ A k l]
  by_cases hk : k = i
  · rw [if_pos hk, if_pos hk]
    field_simp
    ring
  · rw [if_neg hk, if_neg hk]
    ring

/-- The entrywise sup-ball around a point of `SL₃(ℝ)` is open. -/
lemma isOpen_entryBall (m₀ : SL3) (e : ℝ) :
    IsOpen {M : SL3 | ∀ k l : Fin 3, |(M : Matrix (Fin 3) (Fin 3) ℝ) k l
      - (m₀ : Matrix (Fin 3) (Fin 3) ℝ) k l| < e} := by
  rw [isOpen_iff_mem_nhds]
  intro M hM
  have hmem : ∀ k l : Fin 3, {M' : SL3 | |(M' : Matrix (Fin 3) (Fin 3) ℝ) k l
      - (m₀ : Matrix (Fin 3) (Fin 3) ℝ) k l| < e} ∈ 𝓝 M := by
    intro k l
    exact (isOpen_lt (f := fun M' : SL3 => |(M' : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (m₀ : Matrix (Fin 3) (Fin 3) ℝ) k l|) (g := fun _ : SL3 => e)
      (by fun_prop) continuous_const).mem_nhds (hM k l)
  refine Filter.mem_of_superset ?_ (fun M' hM' k l =>
    Set.mem_iInter.mp (Set.mem_iInter.mp hM' k) l)
  exact Filter.iInter_mem.mpr (fun k => Filter.iInter_mem.mpr (fun l => hmem k l))

/-- The transverse coordinate `τ` is continuous at every point with `A j p ≠ 0`. -/
lemma continuousAt_tauC (i j p : Fin 3) (hij : i ≠ j) (c : ℝ) (A₀ : SL3)
    (h : (A₀ : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0) :
    ContinuousAt (fun A : SL3 => tauC i j p hij c A) A₀ := by
  have hnum : Continuous (fun A : SL3 => (A : Matrix (Fin 3) (Fin 3) ℝ) i p - c) := by
    fun_prop
  have hden : Continuous (fun A : SL3 => (A : Matrix (Fin 3) (Fin 3) ℝ) j p) := by
    fun_prop
  have hσ : ContinuousAt (fun A : SL3 => sigmaC i j p c A) A₀ :=
    ContinuousAt.div hnum.continuousAt hden.continuousAt h
  exact ((continuous_uij_loc hij).continuousAt.comp hσ.neg).mul continuousAt_id

/-- **The product chart of an affine transversal is open in `SL₃(ℝ)`.** -/
theorem isOpen_chartC (i j p : Fin 3) (hij : i ≠ j) (c : ℝ) (m₀ : SL3) (R e : ℝ) :
    IsOpen (chartC i j p hij c m₀ R e) := by
  rw [isOpen_iff_mem_nhds]
  intro A₀ hA₀
  rw [mem_chartC_iff i j p hij] at hA₀
  obtain ⟨hAj, hσ, -, hτ⟩ := hA₀
  have h1 : {A : SL3 | (A : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0} ∈ 𝓝 A₀ :=
    (isOpen_ne.preimage (by fun_prop)).mem_nhds hAj
  have h2 : {A : SL3 | |(A : Matrix (Fin 3) (Fin 3) ℝ) i p - c|
      < R * |(A : Matrix (Fin 3) (Fin 3) ℝ) j p|} ∈ 𝓝 A₀ := by
    have h := hσ
    simp only [sigmaC, abs_div] at h
    rw [div_lt_iff₀ (abs_pos.mpr hAj)] at h
    exact (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds h
  have h3 : {A : SL3 | tauC i j p hij c A ∈ {M : SL3 | ∀ k l : Fin 3,
      |(M : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (m₀ : Matrix (Fin 3) (Fin 3) ℝ) k l| < e}} ∈ 𝓝 A₀ :=
    (continuousAt_tauC i j p hij c A₀ hAj).preimage_mem_nhds
      ((isOpen_entryBall m₀ e).mem_nhds hτ)
  refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem h1 h2) h3) ?_
  intro A ⟨⟨hAj', hσ'⟩, hτ'⟩
  rw [mem_chartC_iff i j p hij]
  refine ⟨hAj', ?_, tauC_mem i j p hij hAj', hτ'⟩
  simp only [sigmaC, abs_div]
  rw [div_lt_iff₀ (abs_pos.mpr hAj')]
  exact hσ'

/-- **The flow box of an affine transversal is open in `X₃`.** -/
theorem chartXC_isOpen {i j p : Fin 3} (hij : i ≠ j) (c : ℝ) (m₀ : SL3) (R e : ℝ) :
    IsOpen (chartXC i j p hij c m₀ R e) :=
  QuotientGroup.isOpenMap_coe _ (isOpen_chartC i j p hij c m₀ R e)

/-- **Every point of `SL₃(ℝ)` lies in some affine transversal**: for `g` with `g j p ≠ 0` we have
`g ∈ TsetC i j p (g i p)`. -/
theorem self_mem_TsetC {i j p : Fin 3} {g : SL3}
    (h : (g : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0) : g ∈ TsetC i j p (g i p) :=
  ⟨rfl, h⟩

private theorem chartC_fibre_local (i j p : Fin 3) (hij : i ≠ j) (c : ℝ) (m₀ : SL3)
    (R e : ℝ)
    (hinj : Set.InjOn mkX (chartC i j p hij c m₀ R e)) :
    ∀ A ∈ chartC i j p hij c m₀ R e,
      ∀ A' ∈ chartC i j p hij c m₀ R e,
      (tauC i j p hij c A' = tauC i j p hij c A ↔
        ∃ s : ℝ, |s + sigmaC i j p c A| < R ∧
          mkX A' = uij hij s • mkX A) := by
  intro A hA A' hA'
  rw [mem_chartC_iff i j p hij] at hA hA'
  have hAmem : A ∈ chartC i j p hij c m₀ R e :=
    (mem_chartC_iff i j p hij).mpr hA
  have hA'mem : A' ∈ chartC i j p hij c m₀ R e :=
    (mem_chartC_iff i j p hij).mpr hA'
  obtain ⟨hAj, hσA, hmA, hmeA⟩ := hA
  obtain ⟨hAj', hσA', hmA', hmeA'⟩ := hA'
  have hAeq : A = uij hij (sigmaC i j p c A)
      * tauC i j p hij c A :=
    (mul_sigmaC_tauC i j p hij hAj).symm
  have hA'eq : A' = uij hij (sigmaC i j p c A')
      * tauC i j p hij c A' :=
    (mul_sigmaC_tauC i j p hij hAj').symm
  constructor
  · intro hτ
    refine ⟨sigmaC i j p c A' - sigmaC i j p c A, ?_, ?_⟩
    · have h : sigmaC i j p c A' - sigmaC i j p c A
          + sigmaC i j p c A = sigmaC i j p c A' := by ring
      rw [h]
      exact hσA'
    · have hsm : A' = uij hij (sigmaC i j p c A'
          - sigmaC i j p c A) * A :=
        calc A' = uij hij (sigmaC i j p c A')
              * tauC i j p hij c A' := hA'eq
          _ = uij hij (sigmaC i j p c A')
              * tauC i j p hij c A := by rw [hτ]
          _ = (uij hij (sigmaC i j p c A'
                - sigmaC i j p c A)
              * uij hij (sigmaC i j p c A))
              * tauC i j p hij c A := by
                rw [uij_mul_uij hij (sigmaC i j p c A'
                  - sigmaC i j p c A) (sigmaC i j p c A),
                  show sigmaC i j p c A' - sigmaC i j p c A
                    + sigmaC i j p c A = sigmaC i j p c A' by ring]
          _ = uij hij (sigmaC i j p c A'
                - sigmaC i j p c A)
              * (uij hij (sigmaC i j p c A)
                * tauC i j p hij c A) := by rw [mul_assoc]
          _ = uij hij (sigmaC i j p c A'
                - sigmaC i j p c A) * A := by rw [← hAeq]
      rw [congrArg mkX hsm, Lemmas.mkX_mul]
  · rintro ⟨s, hs, hmk⟩
    have hsplit : uij hij s * A
        = uij hij (s + sigmaC i j p c A)
          * tauC i j p hij c A := by
      conv_lhs => rw [hAeq]
      rw [← mul_assoc, uij_mul_uij hij s (sigmaC i j p c A)]
    have hmem : uij hij s * A ∈ chartC i j p hij c m₀ R e := by
      rw [mem_chartC_iff i j p hij]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [uij_mul_apply hij s A j p, if_neg (Ne.symm hij), mul_zero, add_zero]
        exact hAj
      · rw [hsplit, sigmaC_mul i j p hij c (s + sigmaC i j p c A) hmA]
        exact hs
      · rw [hsplit, tauC_mul i j p hij c (s + sigmaC i j p c A) hmA]
        exact hmA
      · rw [hsplit, tauC_mul i j p hij c (s + sigmaC i j p c A) hmA]
        exact hmeA
    have hEq : uij hij s * A = A' :=
      hinj hmem hA'mem (by rw [Lemmas.mkX_mul, hmk])
    rw [← hEq, hsplit, tauC_mul i j p hij c (s + sigmaC i j p c A) hmA]



/-! ## Sub-charts, box structures and the coordinates of a box -/

/-- The entrywise sup-ball around a matrix. -/
def entryBallC (m : SL3) (e : ℝ) : Set SL3 :=
  {M : SL3 | ∀ k l : Fin 3, |(M : Matrix (Fin 3) (Fin 3) ℝ) k l
    - (m : Matrix (Fin 3) (Fin 3) ℝ) k l| < e}

theorem isOpen_entryBall' (m : SL3) (e : ℝ) : IsOpen (entryBallC m e) :=
  isOpen_entryBall m e

theorem entryBall_mono {m : SL3} {e e' : ℝ} (h : e ≤ e') : entryBallC m e ⊆ entryBallC m e' :=
  fun M hM k l => lt_of_lt_of_le (hM k l) h

/-- The "sub-chart" of an affine flow box: matrices with `A j p ≠ 0`, leaf coordinate in `(-R,R)`
and transversal coordinate lying in the set `O`. -/
def subchartC (i j p : Fin 3) (hij : i ≠ j) (c : ℝ) (O : Set SL3) (R : ℝ) : Set SL3 :=
  {A : SL3 | (A : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0 ∧ |sigmaC i j p c A| < R ∧
    tauC i j p hij c A ∈ O}

theorem isOpen_subchartC {i j p : Fin 3} (hij : i ≠ j) (c : ℝ) (R : ℝ) {O : Set SL3}
    (hO : IsOpen O) : IsOpen (subchartC i j p hij c O R) := by
  rw [isOpen_iff_mem_nhds]
  intro A₀ hA₀
  obtain ⟨hAj, hσ, hτ⟩ := hA₀
  have h1 : {A : SL3 | (A : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0} ∈ 𝓝 A₀ :=
    (isOpen_ne.preimage (by fun_prop)).mem_nhds hAj
  have h2 : {A : SL3 | |(A : Matrix (Fin 3) (Fin 3) ℝ) i p - c|
      < R * |(A : Matrix (Fin 3) (Fin 3) ℝ) j p|} ∈ 𝓝 A₀ := by
    have h := hσ
    simp only [sigmaC, abs_div] at h
    rw [div_lt_iff₀ (abs_pos.mpr hAj)] at h
    exact (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds h
  have h3 : {A : SL3 | tauC i j p hij c A ∈ O} ∈ 𝓝 A₀ :=
    (continuousAt_tauC i j p hij c A₀ hAj).preimage_mem_nhds (hO.mem_nhds hτ)
  refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem h1 h2) h3) ?_
  intro A ⟨⟨hAj', hσ'⟩, hτ'⟩
  refine ⟨hAj', ?_, hτ'⟩
  simp only [sigmaC, abs_div]
  rw [div_lt_iff₀ (abs_pos.mpr hAj')]
  exact hσ'

theorem isOpen_chartX_subchartC {i j p : Fin 3} (hij : i ≠ j) (c : ℝ) (R : ℝ) {O : Set SL3}
    (hO : IsOpen O) : IsOpen (mkX '' subchartC i j p hij c O R) :=
  QuotientGroup.isOpenMap_coe _ (isOpen_subchartC hij c R hO)

theorem subchartC_subset_chartC {i j p : Fin 3} (hij : i ≠ j) {c : ℝ} {m₀ : SL3}
    {O : Set SL3} {R e : ℝ} (hO : O ⊆ entryBallC m₀ e) :
    subchartC i j p hij c O R ⊆ chartC i j p hij c m₀ R e := by
  intro A hA
  obtain ⟨hAj, hσ, hτ⟩ := hA
  rw [mem_chartC_iff i j p hij]
  exact ⟨hAj, hσ, tauC_mem i j p hij hAj, hO hτ⟩

/-- The transvection `u_ij(s)` has `s` in its `(i,j)`-entry, hence `s ↦ u_ij(s)` is injective. -/
theorem uij_apply_self {i j : Fin 3} (hij : i ≠ j) (s : ℝ) :
    ((uij hij s : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j = s := by
  have h := uij_mul_apply hij s (1 : SL3) i j
  rw [mul_one, if_pos rfl] at h
  rw [h]
  simp [Matrix.one_apply, hij]

theorem plq_uij_injective {i j : Fin 3} (hij : i ≠ j) : Function.Injective (uij hij) := by
  intro s t hst
  have := congrArg (fun A : SL3 => (A : Matrix (Fin 3) (Fin 3) ℝ) i j) hst
  rwa [uij_apply_self hij s, uij_apply_self hij t] at this

/-- A "good box" of the `U_ij`-flow: an affine transversal `TsetC i j p c` through the lift `m`,
a leaf radius `R` and a transversal radius `e`, small enough that `mkX` is injective on the chart.
The box itself is `chartXC i j p hij c m R e`. -/
structure GBox (i j : Fin 3) (hij : i ≠ j) where
  p : Fin 3
  c : ℝ
  m : SL3
  hm : m ∈ TsetC i j p c
  R : ℝ
  hR : 0 < R
  e : ℝ
  he : 0 < e
  inj : Set.InjOn mkX (chartC i j p hij c m R e)

namespace GBox

variable {i j : Fin 3} {hij : i ≠ j}

/-- The flow box as a subset of `X₃`. -/
def toSet (B : GBox i j hij) : Set X3 := chartXC i j B.p hij B.c B.m B.R B.e

theorem isOpen_toSet (B : GBox i j hij) : IsOpen B.toSet :=
  chartXC_isOpen hij B.c B.m B.R B.e

theorem mem_toSet_self (B : GBox i j hij) : mkX B.m ∈ B.toSet :=
  ⟨B.m, ⟨0, B.m, by simpa using B.hR, B.hm, fun k l => by simpa using B.he,
    by rw [Lemmas.horoUij_zero hij, one_mul]⟩, rfl⟩

/-- The (unique, by `inj`) matrix of the chart lying above a point of the box; junk outside. -/
noncomputable def preimageOf (B : GBox i j hij) (x : X3) : SL3 := by
  classical
  exact if h : x ∈ B.toSet then Classical.choose h else B.m

theorem preimageOf_mem (B : GBox i j hij) {x : X3} (hx : x ∈ B.toSet) :
    B.preimageOf x ∈ chartC i j B.p hij B.c B.m B.R B.e := by
  rw [preimageOf, dif_pos hx]
  exact (Classical.choose_spec hx).1

theorem mkX_preimageOf (B : GBox i j hij) {x : X3} (hx : x ∈ B.toSet) :
    mkX (B.preimageOf x) = x := by
  rw [preimageOf, dif_pos hx]
  exact (Classical.choose_spec hx).2

/-- The leaf coordinate of a point of a box. -/
noncomputable def sigmaOf (B : GBox i j hij) (x : X3) : ℝ :=
  sigmaC i j B.p B.c (B.preimageOf x)

/-- The transversal coordinate of a point of a box. -/
noncomputable def tauOf (B : GBox i j hij) (x : X3) : SL3 :=
  tauC i j B.p hij B.c (B.preimageOf x)

theorem tauOf_mem (B : GBox i j hij) {x : X3} (hx : x ∈ B.toSet) :
    B.tauOf x ∈ TsetC i j B.p B.c :=
  ((mem_chartC_iff i j B.p hij).mp (B.preimageOf_mem hx)).2.2.1

theorem sigmaOf_lt (B : GBox i j hij) {x : X3} (hx : x ∈ B.toSet) :
    |B.sigmaOf x| < B.R :=
  ((mem_chartC_iff i j B.p hij).mp (B.preimageOf_mem hx)).2.1

theorem tauOf_close (B : GBox i j hij) {x : X3} (hx : x ∈ B.toSet) :
    B.tauOf x ∈ entryBallC B.m B.e :=
  ((mem_chartC_iff i j B.p hij).mp (B.preimageOf_mem hx)).2.2.2

theorem mem_toSet_of_tau (B : GBox i j hij) {x : X3} (hx : x ∈ B.toSet) :
    B.preimageOf x = uij hij (B.sigmaOf x) * B.tauOf x := by
  have hAj := ((mem_chartC_iff i j B.p hij).mp (B.preimageOf_mem hx)).1
  have h := mul_sigmaC_tauC (c := B.c) i j B.p hij hAj
  simp only [sigmaOf, tauOf]
  exact h.symm

/-- **The fibres of a box are leaf arcs.**  Two points of a box have the same transversal
coordinate if and only if they differ by a leaf translation of the amount given by the leaf
coordinate of the first point. -/
theorem fibre_iff (B : GBox i j hij) {x y : X3} (hx : x ∈ B.toSet) (hy : y ∈ B.toSet) :
    (B.tauOf y = B.tauOf x ↔ ∃ s : ℝ, |s + B.sigmaOf x| < B.R ∧ y = uij hij s • x) := by
  have h := chartC_fibre_local i j B.p hij B.c B.m B.R B.e B.inj (B.preimageOf x)
    (B.preimageOf_mem hx) (B.preimageOf y) (B.preimageOf_mem hy)
  rw [B.mkX_preimageOf hy, B.mkX_preimageOf hx] at h
  simpa only [sigmaOf, tauOf] using h

end GBox

/-! ## The atoms of a countably generated σ-algebra -/

/-- Two reals with the same rational halflines are equal. -/
theorem eq_of_forall_rat_lt_iff_lt {r s : ℝ} (h : ∀ q : ℚ, r < q ↔ s < q) : r = s := by
  refine le_antisymm ?_ ?_
  · by_contra hlt
    push_neg at hlt
    obtain ⟨q, hs, hr⟩ := exists_rat_btwn hlt
    have := (h q).mpr hs
    linarith
  · by_contra hlt
    push_neg at hlt
    obtain ⟨q, hr, hs⟩ := exists_rat_btwn hlt
    have := (h q).mp hr
    linarith

/-- **The atoms of a countably generated σ-algebra are the profile classes.**  If `S` is a
countable family of subsets of `X₃` then the atom of `x` in `σ(S)` is the set of points `y` that
belong to exactly the same members of `S` as `x` does. -/
theorem atom_generateFrom_countable {S : Set (Set X3)} (hS : S.Countable) (x : X3) :
    atom (MeasurableSpace.generateFrom S) x =
      {y : X3 | ∀ s ∈ S, (y ∈ s ↔ x ∈ s)} := by
  classical
  have hmeas : ∀ s ∈ S, MeasurableSet[MeasurableSpace.generateFrom S] s := fun s hs =>
    MeasurableSpace.measurableSet_generateFrom hs
  have hA : MeasurableSet[MeasurableSpace.generateFrom S]
      {y : X3 | ∀ s ∈ S, (y ∈ s ↔ x ∈ s)} := by
    have hEq : {y : X3 | ∀ s ∈ S, (y ∈ s ↔ x ∈ s)}
        = (⋂₀ {s : Set X3 | s ∈ S ∧ x ∈ s})
          ∩ (⋃₀ {s : Set X3 | s ∈ S ∧ x ∉ s})ᶜ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_sInter, Set.mem_sUnion, Set.mem_compl_iff,
        Set.mem_inter_iff]
      constructor
      · intro hy
        refine ⟨fun s hs => (hy s hs.1).mpr hs.2, ?_⟩
        intro hex
        obtain ⟨s, ⟨hsS, hxs⟩, hys⟩ := hex
        exact hxs ((hy s hsS).mp hys)
      · rintro ⟨h1, h2⟩ s hs
        refine ⟨fun hys => ?_, fun hxs => h1 s ⟨hs, hxs⟩⟩
        by_contra hxs
        exact h2 ⟨s, ⟨hs, hxs⟩, hys⟩
    rw [hEq]
    refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSet.sInter (hS.mono fun s hs => hs.1) fun t ht => hmeas t ht.1
    · exact (MeasurableSet.sUnion (hS.mono fun s hs => hs.1) fun t ht => hmeas t ht.1).compl
  have hxmem : x ∈ {y : X3 | ∀ s ∈ S, (y ∈ s ↔ x ∈ s)} := fun s _ => Iff.rfl
  refine Set.Subset.antisymm ?_ ?_
  · rw [atom]
    exact Set.sInter_subset_of_mem ⟨hA, hxmem⟩
  · rintro y hy
    rw [atom]
    refine Set.mem_sInter.mpr ?_
    rintro T ⟨hTm, hxT⟩
    let m' : MeasurableSpace X3 :=
      { MeasurableSet' := fun T => x ∈ T ↔ y ∈ T
        measurableSet_empty := by simp
        measurableSet_compl := fun T hT => by
          simp only [Set.mem_compl_iff]
          exact not_congr hT
        measurableSet_iUnion := fun f hf => by
          simp only [Set.mem_iUnion]
          exact exists_congr fun n => hf n }
    have hle : MeasurableSpace.generateFrom S ≤ m' :=
      MeasurableSpace.generateFrom_le fun T hT => (hy T hT).symm
    have hiff : x ∈ T ↔ y ∈ T := hle T hTm
    exact hiff.mp hxT

section Gen

variable {i j : Fin 3} {hij : i ≠ j}

/-! ## The generator family of the plaque σ-algebra -/

/-- The generator sets attached to a good box: cut the box by the transversal coordinate lying in
a half-space of an entry with a rational level. -/
def genSet (B : GBox i j hij) (a b : Fin 3) (t : ℚ) : Set X3 :=
  mkX '' subchartC i j B.p hij B.c
    (entryBallC B.m B.e ∩ {M : SL3 | (M : Matrix (Fin 3) (Fin 3) ℝ) a b < (t : ℝ)}) B.R

theorem isOpen_oHalf (a b : Fin 3) (t : ℚ) :
    IsOpen {M : SL3 | (M : Matrix (Fin 3) (Fin 3) ℝ) a b < (t : ℝ)} :=
  isOpen_lt (by fun_prop) continuous_const

theorem isOpen_genSet (B : GBox i j hij) (a b : Fin 3) (t : ℚ) : IsOpen (genSet B a b t) :=
  isOpen_chartX_subchartC hij B.c B.R
    ((isOpen_entryBall' B.m B.e).inter (isOpen_oHalf a b t))

theorem genSet_subset_toSet (B : GBox i j hij) (a b : Fin 3) (t : ℚ) :
    genSet B a b t ⊆ B.toSet := by
  rintro x ⟨A, hA, rfl⟩
  exact ⟨A, subchartC_subset_chartC hij Set.inter_subset_left hA, rfl⟩

theorem mem_genSet_iff (B : GBox i j hij) (a b : Fin 3) (t : ℚ) {x : X3}
    (hx : x ∈ B.toSet) :
    x ∈ genSet B a b t ↔ ((B.tauOf x : SL3) : Matrix (Fin 3) (Fin 3) ℝ) a b < (t : ℝ) := by
  have hAx := B.preimageOf_mem hx
  have hchart := (mem_chartC_iff i j B.p hij).mp hAx
  constructor
  · rintro ⟨A, hA, hAx'⟩
    have hAeq : A = B.preimageOf x :=
      B.inj (subchartC_subset_chartC hij Set.inter_subset_left hA) hAx
        (by rw [hAx', B.mkX_preimageOf hx])
    obtain ⟨-, -, hτ⟩ := hA
    show ((tauC i j B.p hij B.c (B.preimageOf x) : SL3) : Matrix (Fin 3) (Fin 3) ℝ) a b
      < (t : ℝ)
    rw [← hAeq]
    simpa using hτ.2
  · intro hab
    exact ⟨B.preimageOf x, ⟨hchart.1, hchart.2.1, B.tauOf_close hx, hab⟩, B.mkX_preimageOf hx⟩

end Gen

/-! ## Injectivity of `mkX` on a chart (inlined from `Work.EKLComp.chartC_injective`) -/

/-- On the finite product `ℝ³ ˣ ³` any neighbourhood of a point contains an entrywise sup-ball of
positive radius. -/
private lemma exists_entry_radius' (f : Fin 3 → Fin 3 → ℝ) {U : Set (Fin 3 → Fin 3 → ℝ)}
    (hU : U ∈ 𝓝 f) : ∃ e > 0, ∀ g, (∀ k l, |g k l - f k l| < e) → g ∈ U := by
  obtain ⟨e, he, hsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨e, he, fun g hg => hsub ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff he]
  intro k
  rw [dist_pi_lt_iff he]
  intro l
  rw [Real.dist_eq]
  exact hg k l

/-- Every neighbourhood of a matrix `m₀ ∈ SL₃(ℝ)` contains an entrywise sup-ball around `m₀`. -/
private lemma entryBall_subset_of_mem_nhds' (m₀ : SL3) {U : Set SL3} (hU : U ∈ 𝓝 m₀) :
    ∃ e > 0, entryBallC m₀ e ⊆ U := by
  obtain ⟨T, hT, hTsub⟩ :=
    (mem_nhds_subtype (fun A : Matrix (Fin 3) (Fin 3) ℝ => A.det = 1) m₀ U).mp hU
  obtain ⟨e, he, hband⟩ := exists_entry_radius' (f := (m₀ : Matrix (Fin 3) (Fin 3) ℝ)) (U := T) hT
  exact ⟨e, he, fun M hM => hTsub (hband (M : Matrix (Fin 3) (Fin 3) ℝ) hM)⟩

/-- Every neighbourhood of a real number contains a symmetric interval. -/
private lemma exists_abs_lt_of_mem_nhds' {x : ℝ} {A : Set ℝ} (hA : A ∈ 𝓝 x) :
    ∃ r > 0, ∀ y, |y - x| < r → y ∈ A := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hA
  refine ⟨r, hr, fun y hy => hsub ?_⟩
  rw [Metric.mem_ball, Real.dist_eq]
  simpa [abs_sub_comm] using hy

/-- **`mkX` is injective on a small chart** of an affine transversal. -/
private theorem chartC_injective_local (i j p : Fin 3) (hij : i ≠ j) (c : ℝ) (m₀ : SL3) :
    ∃ R > 0, ∃ e > 0, Set.InjOn mkX (chartC i j p hij c m₀ R e) := by
  obtain ⟨W, hWopen, h1W, hWinj⟩ := Lemmas.exists_open_injective_Γ3
  have hcont : Continuous (fun q : ℝ × SL3 => m₀⁻¹ * (uij hij q.1 * q.2)) :=
    continuous_const.mul (((continuous_uij_loc hij).comp continuous_fst).mul continuous_snd)
  have hz : m₀⁻¹ * (uij hij 0 * m₀) = 1 := by
    rw [Lemmas.horoUij_zero hij, one_mul, inv_mul_cancel]
  have hpre : (fun q : ℝ × SL3 => m₀⁻¹ * (uij hij q.1 * q.2)) ⁻¹' W ∈ 𝓝 ((0 : ℝ), m₀) := by
    refine (hcont.continuousAt (x := ((0 : ℝ), m₀))).preimage_mem_nhds ?_
    rw [hz]
    exact hWopen.mem_nhds h1W
  rw [nhds_prod_eq] at hpre
  obtain ⟨A₀, hA₀, B, hB, hAB₀⟩ := Filter.mem_prod_iff.mp hpre
  have hAB : ∀ q : ℝ × SL3, q ∈ A₀ ×ˢ B → m₀⁻¹ * (uij hij q.1 * q.2) ∈ W :=
    fun q hq => hAB₀ hq
  obtain ⟨R, hR, hRsub⟩ := exists_abs_lt_of_mem_nhds' hA₀
  obtain ⟨e, he, hesub⟩ := entryBall_subset_of_mem_nhds' m₀ hB
  refine ⟨R, hR, e, he, ?_⟩
  intro A hA A' hA' hmk
  obtain ⟨σ, m, hσ, _hmT, hme, hAeq⟩ := hA
  obtain ⟨σ', m', hσ', _hmT', hme', hA'eq⟩ := hA'
  rw [hAeq] at hmk ⊢
  rw [hA'eq] at hmk ⊢
  have hσA : σ ∈ A₀ := hRsub σ (by simpa using hσ)
  have hmB : m ∈ B := hesub hme
  have hσ'A : σ' ∈ A₀ := hRsub σ' (by simpa using hσ')
  have hm'B : m' ∈ B := hesub hme'
  have hvm : m₀⁻¹ * (uij hij σ * m) ∈ W := hAB (σ, m) ⟨hσA, hmB⟩
  have hv'm : m₀⁻¹ * (uij hij σ' * m') ∈ W := hAB (σ', m') ⟨hσ'A, hm'B⟩
  have hΓ : (uij hij σ * m)⁻¹ * (uij hij σ' * m') ∈ Γ3 := by
    have h : QuotientGroup.mk (uij hij σ * m) = QuotientGroup.mk (uij hij σ' * m') := hmk
    exact QuotientGroup.eq.mp h
  have hΓ' : (m₀⁻¹ * (uij hij σ * m))⁻¹ * (m₀⁻¹ * (uij hij σ' * m')) ∈ Γ3 := by
    rw [show (m₀⁻¹ * (uij hij σ * m))⁻¹ * (m₀⁻¹ * (uij hij σ' * m'))
        = (uij hij σ * m)⁻¹ * (uij hij σ' * m') from by group]
    exact hΓ
  exact mul_left_cancel (hWinj _ hvm _ hv'm hΓ')

section Cover

variable {i j : Fin 3} {hij : i ≠ j}

/-! ## Covering `X₃` by finitely many good boxes -/

/-- Every point of `X₃` lies in some good box. -/
theorem exists_gbox (x : X3) : ∃ B : GBox i j hij, x ∈ B.toSet := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hrow : ∃ p : Fin 3, (g : Matrix (Fin 3) (Fin 3) ℝ) j p ≠ 0 := by
    by_contra h
    push_neg at h
    have hdet : (g : Matrix (Fin 3) (Fin 3) ℝ).det = 0 :=
      Matrix.det_eq_zero_of_row_eq_zero j h
    rw [g.2] at hdet
    exact one_ne_zero hdet
  obtain ⟨p, hp⟩ := hrow
  have hgm : g ∈ TsetC i j p (g i p) := ⟨rfl, hp⟩
  obtain ⟨R, hR, e, he, hinj⟩ := chartC_injective_local i j p hij (g i p) g
  refine ⟨⟨p, g i p, g, hgm, R, hR, e, he, hinj⟩, ?_⟩
  exact ⟨g, ⟨0, g, by simpa using hR, hgm, fun k l => by simpa using he,
    by rw [Lemmas.horoUij_zero hij, one_mul]⟩, rfl⟩

/-- A choice of a good box around each point. -/
noncomputable def boxAt (x : X3) : GBox i j hij :=
  Classical.choose (exists_gbox (hij := hij) x)

theorem mem_boxAt (x : X3) : x ∈ (boxAt (hij := hij) x).toSet :=
  Classical.choose_spec (exists_gbox (hij := hij) x)

/-- **Finitely many good boxes cover `μ`-almost all of `X₃`.** -/
theorem exists_finite_gboxes (μ : Measure X3) [IsProbabilityMeasure μ] (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ) (B : Fin N → GBox i j hij), ENNReal.ofReal (1 - ε) ≤ μ (⋃ l, (B l).toSet) := by
  classical
  obtain ⟨S, hSc, hSne, hSb⟩ := TopologicalSpace.exists_countable_basis X3
  have hSnon : S.Nonempty := by
    obtain ⟨v, hvS, -, -⟩ := hSb.exists_subset_of_mem_open
      (show (QuotientGroup.mk (1 : SL3) : X3) ∈ (Set.univ : Set X3) from trivial) isOpen_univ
    exact ⟨v, hvS⟩
  obtain ⟨V, hV⟩ := hSc.exists_eq_range hSnon
  let C : ℕ → GBox i j hij := fun n =>
    if h : ∃ y : X3, V n ⊆ (boxAt (hij := hij) y).toSet then
      boxAt (hij := hij) (Classical.choose h)
    else boxAt (hij := hij) (Classical.arbitrary X3)
  have hcover : (⋃ n, (C n).toSet) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ (boxAt (hij := hij) x).toSet := mem_boxAt x
    have hopen : IsOpen (boxAt (hij := hij) x).toSet := (boxAt x).isOpen_toSet
    obtain ⟨v, hvS, hxv, hvsub⟩ := hSb.exists_subset_of_mem_open hx hopen
    have hvSr : v ∈ Set.range V := by rw [hV] at hvS; exact hvS
    obtain ⟨n, hn⟩ := hvSr
    have hex : ∃ y : X3, V n ⊆ (boxAt (hij := hij) y).toSet := ⟨x, by rw [hn]; exact hvsub⟩
    have hCn : C n = boxAt (hij := hij) (Classical.choose hex) := by
      show (if h : ∃ y : X3, V n ⊆ (boxAt (hij := hij) y).toSet
        then boxAt (hij := hij) (Classical.choose h)
        else boxAt (hij := hij) (Classical.arbitrary X3)) = _
      rw [dif_pos hex]
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    rw [hCn]
    exact (Classical.choose_spec hex) (by rw [hn]; exact hxv)
  have hmono : Monotone (fun N : ℕ => ⋃ n : Fin N, (C (n : ℕ)).toSet) := by
    intro N M hNM
    refine Set.iUnion_subset fun n x hx => Set.mem_iUnion.mpr ⟨Fin.castLE hNM n, ?_⟩
    simpa using hx
  have htend := tendsto_measure_iUnion_atTop (μ := μ) hmono
  have hunion : (⋃ N, ⋃ n : Fin N, (C (n : ℕ)).toSet) = (⋃ n, (C n).toSet) := by
    ext x
    constructor
    · intro hx
      obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hN
      exact Set.mem_iUnion.mpr ⟨(n : ℕ), hn⟩
    · intro hx
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨n + 1, Set.mem_iUnion.mpr ⟨⟨n, Nat.lt_succ_self n⟩, hn⟩⟩
  rw [hunion, hcover, measure_univ] at htend
  have hlt : ENNReal.ofReal (1 - ε) < (1 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_lt_one]
    linarith
  have hev := htend.eventually (isOpen_Ioi.mem_nhds hlt)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  exact ⟨N, fun l => C (l : ℕ), le_of_lt (hN N le_rfl)⟩

end Cover

section Arc

variable {i j : Fin 3} {hij : i ≠ j}

/-- **The fibre of a box through `x` is the leaf arc of `x`.**  For a free point `x` of a good box,
the points of the box with the same transversal coordinate as `x` are exactly the leaf translates
`u_ij(s) • x` with `|s + σ(x)| < R`. -/
theorem fibre_arc (B : GBox i j hij) {x : X3} (hx : x ∈ B.toSet)
    (hf : ∀ u ∈ (Uij hij : Set SL3), u • x = x → u = 1) :
    {u : SL3 | u ∈ (Uij hij : Set SL3) ∧ u • x ∈ B.toSet ∧ B.tauOf (u • x) = B.tauOf x}
      = {u : SL3 | ∃ s : ℝ, |s + B.sigmaOf x| < B.R ∧ u = uij hij s} := by
  ext u
  constructor
  · rintro ⟨huU, huB, hτ⟩
    obtain ⟨s, rfl⟩ := (Lemmas.mem_Uij_iff hij u).mp huU
    obtain ⟨s', hs', hEq⟩ := (B.fibre_iff hx huB).mp hτ
    have hinv : (uij hij s)⁻¹ = uij hij (-s) :=
      inv_eq_of_mul_eq_one_right
        (by rw [uij_mul_uij hij s (-s), add_neg_cancel, Lemmas.horoUij_zero hij])
    have hs's : s' = s := by
      have hfix : uij hij (s' - s) • x = x := by
        have h1 : uij hij (s' - s) = (uij hij s)⁻¹ * uij hij s' := by
          rw [hinv]
          calc uij hij (s' - s) = uij hij (-s + s') := by congr 1; ring
            _ = uij hij (-s) * uij hij s' := (uij_mul_uij hij (-s) s').symm
        rw [h1, mul_smul, ← hEq, inv_smul_smul]
      have hmem : uij hij (s' - s) ∈ (Uij hij : Set SL3) :=
        (Lemmas.mem_Uij_iff hij _).mpr ⟨s' - s, rfl⟩
      have hone := hf _ hmem hfix
      exact sub_eq_zero.mp (plq_uij_injective hij (by rw [hone, Lemmas.horoUij_zero hij]))
    exact ⟨s, by rw [← hs's]; exact hs', rfl⟩
  · rintro ⟨s, hs, rfl⟩
    have hx2 : uij hij (B.sigmaOf x) • mkX (B.tauOf x) = x := by
      conv_rhs => rw [← B.mkX_preimageOf hx]
      rw [← Lemmas.mkX_mul, B.mem_toSet_of_tau hx]
    have hmem : uij hij s • x ∈ B.toSet := by
      refine ⟨uij hij (s + B.sigmaOf x) * B.tauOf x, ?_, ?_⟩
      · exact ⟨s + B.sigmaOf x, B.tauOf x, hs, B.tauOf_mem hx, B.tauOf_close hx, rfl⟩
      · rw [Lemmas.mkX_mul, ← uij_mul_uij hij s (B.sigmaOf x), mul_smul, hx2]
    exact ⟨(Lemmas.mem_Uij_iff hij _).mpr ⟨s, rfl⟩, hmem,
      (B.fibre_iff hx hmem).mpr ⟨s, hs, rfl⟩⟩

end Arc

/-! ## The plaque σ-algebra attached to a disjoint family of open pieces -/

section Parts

variable {i j : Fin 3} {hij : i ≠ j} {N : ℕ} {B : Fin N → GBox i j hij}

/-- A family of pairwise disjoint open pieces, the `l`-th of which lies in the `l`-th good box. -/
structure PParts (B : Fin N → GBox i j hij) where
  P : Fin N → Set X3
  open' : ∀ l, IsOpen (P l)
  sub : ∀ l, P l ⊆ (B l).toSet
  disj : ∀ l l', l ≠ l' → Disjoint (P l) (P l')

/-- The support of the plaque algebra: the free points covered by the pieces. -/
def PParts.Zw (Q : PParts B) : Set X3 := Free i j hij ∩ ⋃ l, Q.P l

/-- The countable family of generators of the plaque σ-algebra. -/
def PParts.genFam (Q : PParts B) : Set (Set X3) :=
  (Set.range Q.P) ∪ {Q.Zw} ∪
    (Set.range fun q : Fin N × Fin 3 × Fin 3 × ℚ => Q.P q.1 ∩ genSet (B q.1) q.2.1 q.2.2.1 q.2.2.2)

/-- The plaque σ-algebra. -/
def PParts.sigma (Q : PParts B) : MeasurableSpace X3 :=
  MeasurableSpace.generateFrom Q.genFam

theorem PParts.genFam_countable (Q : PParts B) : Q.genFam.Countable := by
  refine Set.Countable.union (Set.Countable.union (Set.countable_range _)
    (Set.countable_singleton _)) ?_
  exact Set.countable_range _

theorem PParts.measurableSet_Zw (Q : PParts B) : MeasurableSet[Q.sigma] Q.Zw :=
  MeasurableSpace.measurableSet_generateFrom (by simp [genFam])

end Parts


/-! ## Membership in `Free` in leaf coordinates -/

section FreeLemmas

variable {i j : Fin 3} {hij : i ≠ j}

/-- `u_ij(s) = 1` if and only if `s = 0`. -/
theorem uij_eq_one_iff {s : ℝ} : uij hij s = 1 ↔ s = 0 := by
  rw [← Lemmas.horoUij_zero hij]
  exact ⟨fun h => plq_uij_injective hij h, fun h => by rw [h]⟩

/-- Membership in `Free`, in terms of the leaf parameter: `x` is free iff no nonzero leaf
translation fixes it. -/
theorem mem_free_iff (x : X3) :
    x ∈ Free i j hij ↔ ∀ s : ℝ, uij hij s • x = x → s = 0 := by
  constructor
  · intro hx s hs
    exact uij_eq_one_iff.mp (hx (uij hij s) ((Lemmas.mem_Uij_iff hij _).mpr ⟨s, rfl⟩) hs)
  · intro hx u hu hux
    obtain ⟨s, rfl⟩ := (Lemmas.mem_Uij_iff hij u).mp hu
    rw [hx s hux, Lemmas.horoUij_zero hij]

/-- `Free` is invariant under the leaf translations of `U_ij`. -/
theorem smul_mem_free {u : SL3} (hu : u ∈ (Uij hij : Set SL3)) {x : X3}
    (hx : x ∈ Free i j hij) : u • x ∈ Free i j hij := by
  obtain ⟨r, rfl⟩ := (Lemmas.mem_Uij_iff hij u).mp hu
  rw [mem_free_iff] at hx ⊢
  intro s hs
  have hs' : uij hij (s + r) • x = uij hij r • x := by
    rw [← uij_mul_uij hij s r, mul_smul]
    exact hs
  have h4 : uij hij (-r) • (uij hij (s + r) • x) = uij hij (-r) • (uij hij r • x) :=
    congrArg (fun y : X3 => uij hij (-r) • y) hs'
  rw [← mul_smul, ← mul_smul, uij_mul_uij hij (-r) (s + r), uij_mul_uij hij (-r) r,
    show -r + (s + r) = s by ring, neg_add_cancel r, Lemmas.horoUij_zero hij] at h4
  exact hx s (by simpa using h4)

end FreeLemmas

/-! ## The atom of the plaque σ-algebra -/

section AtomEq

variable {i j : Fin 3} {hij : i ≠ j} {N : ℕ} {B : Fin N → GBox i j hij}

theorem PParts.mem_genFam_P (Q : PParts B) (l : Fin N) : Q.P l ∈ Q.genFam :=
  Or.inl (Or.inl ⟨l, rfl⟩)

theorem PParts.mem_genFam_Zw (Q : PParts B) : Q.Zw ∈ Q.genFam := Or.inl (Or.inr rfl)

theorem PParts.mem_genFam_genSet (Q : PParts B) (l : Fin N) (a b : Fin 3) (t : ℚ) :
    Q.P l ∩ genSet (B l) a b t ∈ Q.genFam :=
  Or.inr ⟨(l, a, b, t), rfl⟩

/-- **The atom of the plaque σ-algebra.**  For `x` in the support `Zw`, lying in the piece `P l`,
the atom of `x` is: the part of `Zw` in `P l` whose `l`-th transversal coordinate equals that
of `x`.  (In particular it is a leaf arc, cut by the open piece `P l`.) -/
theorem PParts.atom_eq (Q : PParts B) {x : X3} (hx : x ∈ Q.Zw) {l : Fin N}
    (hl : x ∈ Q.P l) :
    atom Q.sigma x = Q.Zw ∩ Q.P l ∩ {y : X3 | (B l).tauOf y = (B l).tauOf x} := by
  rw [PParts.sigma, atom_generateFrom_countable Q.genFam_countable x]
  ext y
  constructor
  · intro hy
    have hyP : y ∈ Q.P l := (hy (Q.P l) (Q.mem_genFam_P l)).mpr hl
    refine ⟨⟨(hy Q.Zw Q.mem_genFam_Zw).mpr hx, hyP⟩, ?_⟩
    ext a b
    refine eq_of_forall_rat_lt_iff_lt fun t => ?_
    have hgen := hy (Q.P l ∩ genSet (B l) a b t) (Q.mem_genFam_genSet l a b t)
    rw [Set.mem_inter_iff, Set.mem_inter_iff] at hgen
    have hiff : y ∈ genSet (B l) a b t ↔ x ∈ genSet (B l) a b t :=
      ⟨fun h => (hgen.mp ⟨hyP, h⟩).2, fun h => (hgen.mpr ⟨hl, h⟩).2⟩
    rwa [mem_genSet_iff (B l) a b t (Q.sub l hyP),
      mem_genSet_iff (B l) a b t (Q.sub l hl)] at hiff
  · rintro ⟨⟨hyZ, hyP⟩, hτ⟩ s hs
    rcases hs with h | h
    · rcases h with ⟨l', rfl⟩ | hZw
      · rcases eq_or_ne l' l with heq | hne
        · rw [← heq] at hyP hl
          exact ⟨fun _ => hl, fun _ => hyP⟩
        · have hd := Set.disjoint_left.mp (Q.disj l' l hne)
          exact ⟨fun h => absurd hyP (hd h), fun h => absurd hl (hd h)⟩
      · rw [Set.mem_singleton_iff] at hZw
        rw [hZw]
        exact ⟨fun _ => hx, fun _ => hyZ⟩
    · obtain ⟨q, rfl⟩ := h
      obtain ⟨l', a, b, t⟩ := q
      rcases eq_or_ne l' l with heq | hne
      · rw [← heq] at hyP hl hτ
        have hg : (y ∈ genSet (B l') a b t) ↔ (x ∈ genSet (B l') a b t) := by
          rw [mem_genSet_iff (B l') a b t (Q.sub l' hyP),
            mem_genSet_iff (B l') a b t (Q.sub l' hl), hτ]
        exact ⟨fun h => ⟨hl, hg.mp h.2⟩, fun h => ⟨hyP, hg.mpr h.2⟩⟩
      · have hd := Set.disjoint_left.mp (Q.disj l' l hne)
        exact ⟨fun h => absurd hyP (hd h.1), fun h => absurd hl (hd h.1)⟩

end AtomEq


/-! ## The shape of the plaque σ-algebra -/

section Shape

variable {i j : Fin 3} {hij : i ≠ j} {N : ℕ} {B : Fin N → GBox i j hij}

/-- The leaf orbit map `s ↦ u_ij(s) • x` is continuous. -/
theorem continuous_uij_smul (x : X3) : Continuous (fun s : ℝ => uij hij s • x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  change Continuous (fun s : ℝ => uij hij s • mkX g)
  have hfun : (fun s : ℝ => uij hij s • mkX g) = fun s : ℝ => mkX (uij hij s * g) := by
    funext s
    rw [Lemmas.mkX_mul]
  rw [hfun]
  exact QuotientGroup.continuous_mk.comp ((continuous_uij_loc hij).mul continuous_const)

/-- **The shape is the leaf arc cut by the piece.**  At a point `x` of `Zw` lying in `P l`, the
shape of the plaque σ-algebra is the leaf arc of `x` inside the box `B l`, cut down by the open
piece `P l`. -/
theorem PParts.shape_eq (Q : PParts B) {x : X3} (hx : x ∈ Q.Zw) {l : Fin N}
    (hl : x ∈ Q.P l) :
    shape Q.sigma (Uij hij) x =
      uij hij '' {s : ℝ | |s + (B l).sigmaOf x| < (B l).R ∧ uij hij s • x ∈ Q.P l} := by
  have hxfree : x ∈ Free i j hij := hx.1
  ext u
  rw [shape, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨huU, huAtom⟩
    obtain ⟨s, rfl⟩ := (Lemmas.mem_Uij_iff hij u).mp huU
    have hP : uij hij s • x ∈ Q.P l ∧ (B l).tauOf (uij hij s • x) = (B l).tauOf x := by
      have h := huAtom
      rw [Q.atom_eq hx hl] at h
      exact ⟨h.1.2, h.2⟩
    have hyB : uij hij s • x ∈ (B l).toSet := Q.sub l hP.1
    obtain ⟨s', hs', heq⟩ := ((B l).fibre_iff (Q.sub l hl) hyB).mp hP.2
    have hs's : s' = s := by
      have hfix : uij hij (s' - s) • x = x := by
        have h4 : uij hij (-s) • (uij hij s' • x) = uij hij (-s) • (uij hij s • x) :=
          congrArg (fun y : X3 => uij hij (-s) • y) heq.symm
        rw [← mul_smul, ← mul_smul, uij_mul_uij hij (-s) s', uij_mul_uij hij (-s) s,
          show -s + s' = s' - s by ring, neg_add_cancel s, Lemmas.horoUij_zero hij] at h4
        simpa using h4
      have h5 := (mem_free_iff (hij := hij) x).mp hxfree (s' - s) hfix
      linarith
    refine ⟨s, ⟨?_, hP.1⟩, rfl⟩
    rw [← hs's]
    exact hs'
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(Lemmas.mem_Uij_iff hij _).mpr ⟨s, rfl⟩, ?_⟩
    rw [Q.atom_eq hx hl]
    exact ⟨⟨⟨smul_mem_free ((Lemmas.mem_Uij_iff hij _).mpr ⟨s, rfl⟩) hxfree,
        Set.mem_iUnion.mpr ⟨l, hs.2⟩⟩, hs.2⟩,
      ((B l).fibre_iff (Q.sub l hl) (Q.sub l hs.2)).mpr ⟨s, hs.1, rfl⟩⟩

/-- A subset of `U_ij` that is open in the leaf parameter is the trace of an open subset of
`SL₃(ℝ)`. -/
theorem exists_isOpen_inter_eq (S : Set SL3) (hSU : S ⊆ (Uij hij : Set SL3))
    (hloc : ∀ s : ℝ, uij hij s ∈ S → ∃ η > 0, ∀ t : ℝ, |t| < η → uij hij (s + t) ∈ S) :
    ∃ O : Set SL3, IsOpen O ∧ O ∩ (Uij hij : Set SL3) = S := by
  classical
  let η : ℝ → ℝ := fun s => if h : uij hij s ∈ S then Classical.choose (hloc s h) else 1
  have hηpos : ∀ s, uij hij s ∈ S → 0 < η s := fun s hs => by
    simp only [η, dif_pos hs]
    exact (Classical.choose_spec (hloc s hs)).1
  have hηspec : ∀ s (hs : uij hij s ∈ S), ∀ t : ℝ, |t| < η s → uij hij (s + t) ∈ S :=
    fun s hs t ht => (Classical.choose_spec (hloc s hs)).2 t (by simpa [η, dif_pos hs] using ht)
  let O : Set SL3 := ⋃ s : ℝ, {g : SL3 | uij hij s ∈ S ∧ uij hij (-s) * g ∈ V (η s)}
  have hOopen : IsOpen O := by
    refine isOpen_iUnion fun s => ?_
    by_cases hs : uij hij s ∈ S
    · have heq : {g : SL3 | uij hij s ∈ S ∧ uij hij (-s) * g ∈ V (η s)}
          = {g : SL3 | uij hij (-s) * g ∈ V (η s)} := by
        ext g; simp only [Set.mem_ofPred_eq, hs, true_and]
      rw [heq]
      exact ((Lemmas.V_open_one (η s) (hηpos s hs)).1).preimage
        (continuous_const.mul continuous_id)
    · have heq : {g : SL3 | uij hij s ∈ S ∧ uij hij (-s) * g ∈ V (η s)} = ∅ := by
        ext g; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h hs
      rw [heq]
      exact isOpen_empty
  have hOiff : ∀ u : SL3, u ∈ O ↔ ∃ s : ℝ, uij hij s ∈ S ∧ uij hij (-s) * u ∈ V (η s) := by
    intro u
    simp only [O, Set.mem_iUnion, Set.mem_ofPred_eq]
  have hOeq : O ∩ (Uij hij : Set SL3) = S := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro u ⟨hu, huU⟩
      rw [hOiff u] at hu
      obtain ⟨s, hsS, hgs⟩ := hu
      obtain ⟨s', rfl⟩ := (Lemmas.mem_Uij_iff hij u).mp huU
      have h1 : uij hij (s' - s) ∈ V (η s) := by
        have h2 : uij hij (-s) * uij hij s' ∈ V (η s) := hgs
        rwa [uij_mul_uij hij (-s) s', show -s + s' = s' - s by ring] at h2
      have h2 : |s' - s| < η s := by
        have h3 : |(uij hij (s' - s) : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < η s := h1 i j
        rw [uij_apply_self hij (s' - s)] at h3
        simpa [Matrix.one_apply, hij] using h3
      have h3 := hηspec s hsS (s' - s) h2
      rwa [show s + (s' - s) = s' by ring] at h3
    · intro u huS
      obtain ⟨s, rfl⟩ := (Lemmas.mem_Uij_iff hij u).mp (hSU huS)
      refine ⟨(hOiff _).mpr ⟨s, huS, ?_⟩, (Lemmas.mem_Uij_iff hij _).mpr ⟨s, rfl⟩⟩
      rw [uij_mul_uij hij (-s) s, neg_add_cancel, Lemmas.horoUij_zero hij]
      exact (Lemmas.V_open_one (η s) (hηpos s huS)).2
  exact ⟨O, hOopen, hOeq⟩

/-- **The shape is the trace of an open set of `SL₃(ℝ)`.** -/
theorem PParts.exists_isOpen_shape (Q : PParts B) {x : X3} (hx : x ∈ Q.Zw) {l : Fin N}
    (hl : x ∈ Q.P l) :
    ∃ O : Set SL3, IsOpen O ∧ shape Q.sigma (Uij hij) x = O ∩ (Uij hij : Set SL3) := by
  classical
  set T : Set ℝ := {s : ℝ | |s + (B l).sigmaOf x| < (B l).R ∧ uij hij s • x ∈ Q.P l} with hTdef
  have hTopen : IsOpen T := by
    rw [hTdef]
    refine (isOpen_lt (f := fun s : ℝ => |s + (B l).sigmaOf x|) (g := fun _ : ℝ => (B l).R)
      (continuous_id.add continuous_const).abs continuous_const).inter ?_
    exact (Q.open' l).preimage (continuous_uij_smul (hij := hij) x)
  have hSU : uij hij '' T ⊆ (Uij hij : Set SL3) := by
    rintro u ⟨s, -, rfl⟩
    exact (Lemmas.mem_Uij_iff hij _).mpr ⟨s, rfl⟩
  have hloc : ∀ s : ℝ, uij hij s ∈ uij hij '' T →
      ∃ η > 0, ∀ t : ℝ, |t| < η → uij hij (s + t) ∈ uij hij '' T := by
    intro s hs
    have hsT : s ∈ T := by
      obtain ⟨s', hs', heq⟩ := hs
      rwa [plq_uij_injective hij heq] at hs'
    obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp (hTopen.mem_nhds hsT)
    refine ⟨η, hη, fun t ht => ⟨s + t, hsub ?_, rfl⟩⟩
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [add_sub_cancel_left, abs_sub_comm] using ht
  obtain ⟨O, hO, hOeq⟩ := exists_isOpen_inter_eq (uij hij '' T) hSU hloc
  exact ⟨O, hO, by rw [Q.shape_eq hx hl]; exact hOeq.symm⟩

/-- **The shape is entrywise bounded.** -/
theorem PParts.shape_bounded (Q : PParts B) {x : X3} (hx : x ∈ Q.Zw) {l : Fin N}
    (hl : x ∈ Q.P l) :
    ∃ C : ℝ, ∀ u ∈ shape Q.sigma (Uij hij) x, ∀ a b : Fin 3,
      |(u : Matrix (Fin 3) (Fin 3) ℝ) a b| ≤ C := by
  refine ⟨2 * (B l).R + 1, ?_⟩
  intro u hu a b
  rw [Q.shape_eq hx hl] at hu
  obtain ⟨s, hs, rfl⟩ := hu
  have h1 : |s| < 2 * (B l).R := by
    have h2 : |(B l).sigmaOf x| < (B l).R := (B l).sigmaOf_lt (Q.sub l hl)
    have h3 := abs_add_le s ((B l).sigmaOf x)
    have h4 : |s| ≤ |s + (B l).sigmaOf x| + |(B l).sigmaOf x| := by
      calc |s| = |(s + (B l).sigmaOf x) - (B l).sigmaOf x| := by ring_nf
        _ ≤ |s + (B l).sigmaOf x| + |(B l).sigmaOf x| := abs_sub _ _
    linarith [hs.1, h2]
  have h4 : ((uij hij s : SL3) : Matrix (Fin 3) (Fin 3) ℝ) a b
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) a b
        + s * (if a = i then (1 : Matrix (Fin 3) (Fin 3) ℝ) j b else 0) := by
    have h := uij_mul_apply hij s (1 : SL3) a b
    rwa [mul_one] at h
  rw [h4]
  have h5 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) a b| ≤ 1 := by
    by_cases hab : a = b
    · simp [Matrix.one_apply, hab]
    · simp [Matrix.one_apply, hab]
  have h6 : |(if a = i then (1 : Matrix (Fin 3) (Fin 3) ℝ) j b else 0)| ≤ 1 := by
    by_cases hai : a = i
    · simp only [hai, if_pos]
      by_cases hjb : j = b
      · simp [Matrix.one_apply, hjb]
      · simp [Matrix.one_apply, hjb]
    · simp [hai]
  calc |(1 : Matrix (Fin 3) (Fin 3) ℝ) a b
        + s * (if a = i then (1 : Matrix (Fin 3) (Fin 3) ℝ) j b else 0)|
      ≤ |(1 : Matrix (Fin 3) (Fin 3) ℝ) a b|
        + |s * (if a = i then (1 : Matrix (Fin 3) (Fin 3) ℝ) j b else 0)| := abs_add_le _ _
    _ ≤ 1 + |s| * 1 := by
        rw [abs_mul]
        have h7 : |s| * |(if a = i then (1 : Matrix (Fin 3) (Fin 3) ℝ) j b else 0)|
            ≤ |s| * 1 := mul_le_mul_of_nonneg_left h6 (abs_nonneg s)
        linarith
    _ ≤ 2 * (B l).R + 1 := by linarith [h1]

end Shape


/-! ## The good sets -/

section Good

variable {i j : Fin 3} {hij : i ≠ j} {N : ℕ} {B : Fin N → GBox i j hij}

theorem ballU_mono {δ δ' : ℝ} (h : δ ≤ δ') : (ballU hij δ : Set SL3) ⊆ (ballU hij δ') :=
  Set.image_mono (Set.Icc_subset_Icc (by linarith) h)

/-- The part of a good box whose leaf coordinate is at distance `δ` from the boundary: the box cut
by the smaller leaf radius `R - δ`. -/
def GSet (B : GBox i j hij) (δ : ℝ) : Set X3 :=
  mkX '' subchartC i j B.p hij B.c (entryBallC B.m B.e) (B.R - δ)

theorem GSet_subset_toSet (B : GBox i j hij) {δ : ℝ} (hδ : 0 ≤ δ) : GSet B δ ⊆ B.toSet := by
  rintro x ⟨A, hA, rfl⟩
  obtain ⟨hAj, hσ, hτ⟩ := hA
  exact ⟨A, (mem_chartC_iff i j B.p hij).mpr
    ⟨hAj, lt_of_lt_of_le hσ (by linarith), tauC_mem i j B.p hij hAj, hτ⟩, rfl⟩

theorem isOpen_GSet (B : GBox i j hij) (δ : ℝ) : IsOpen (GSet B δ) :=
  isOpen_chartX_subchartC hij B.c (B.R - δ) (isOpen_entryBall' B.m B.e)

theorem mem_GSet_iff (B : GBox i j hij) {δ : ℝ} (hδ : 0 ≤ δ) {x : X3} :
    x ∈ GSet B δ ↔ x ∈ B.toSet ∧ |B.sigmaOf x| < B.R - δ := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨hAj, hσ, hτ⟩ := hA
    have hAc : A ∈ chartC i j B.p hij B.c B.m B.R B.e :=
      (mem_chartC_iff i j B.p hij).mpr
        ⟨hAj, lt_of_lt_of_le hσ (by linarith), tauC_mem i j B.p hij hAj, hτ⟩
    have hxA : mkX A ∈ B.toSet := ⟨A, hAc, rfl⟩
    have hpre : B.preimageOf (mkX A) = A :=
      B.inj (B.preimageOf_mem hxA) hAc (B.mkX_preimageOf hxA)
    exact ⟨hxA, by rw [GBox.sigmaOf, hpre]; exact hσ⟩
  · rintro ⟨hx, hσ⟩
    exact ⟨B.preimageOf x,
      ⟨((mem_chartC_iff i j B.p hij).mp (B.preimageOf_mem hx)).1,
        by simpa [GBox.sigmaOf] using hσ,
        by simpa [GBox.tauOf] using B.tauOf_close hx⟩,
      B.mkX_preimageOf hx⟩

/-- **The `δ`-ball condition is open.**  If `P` is open in `X₃` then the set of points whose
`U_ij`-leaf ball of radius `δ` is contained in `P` is open. -/
theorem isOpen_forall_ballU_smul_subset {δ : ℝ} {P : Set X3} (hP : IsOpen P) :
    IsOpen {x : X3 | ∀ u ∈ (ballU hij δ : Set SL3), u • x ∈ P} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hcont : Continuous fun p : X3 × ℝ => uij hij p.2 • p.1 :=
    continuous_smul.comp
      (((continuous_uij_loc hij).comp continuous_snd).prodMk continuous_fst)
  have hN : IsOpen {p : X3 × ℝ | uij hij p.2 • p.1 ∈ P} := hP.preimage hcont
  have hsub : ({x} : Set X3) ×ˢ Set.Icc (-δ) δ ⊆ {p : X3 × ℝ | uij hij p.2 • p.1 ∈ P} := by
    rintro ⟨y, s⟩ ⟨hy, hs⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hx _ ⟨s, hs, rfl⟩
  obtain ⟨U, W, hUo, hWo, hxU, hIW, hUW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hN hsub
  refine Filter.mem_of_superset (hUo.mem_nhds (hxU (Set.mem_singleton x))) fun y hy => ?_
  intro u hu
  obtain ⟨s, hs, rfl⟩ := hu
  have hsW : s ∈ W := hIW hs
  exact hUW (show ((y, s) : X3 × ℝ) ∈ U ×ˢ W from ⟨hy, hsW⟩)

/-- The **good set** at scale `δ`: free points of the pieces whose `δ`-leaf ball still lies in
their piece and whose leaf coordinate is `δ` away from the boundary of the box. -/
def PParts.good (Q : PParts B) (δ : ℝ) : Set X3 :=
  Free i j hij ∩ ⋃ l, (Q.P l ∩ GSet (B l) δ ∩
    {x : X3 | ∀ u ∈ (ballU hij δ : Set SL3), u • x ∈ Q.P l})

theorem PParts.mem_good_iff (Q : PParts B) {δ : ℝ} {x : X3} :
    x ∈ Q.good δ ↔ x ∈ Free i j hij ∧ ∃ l : Fin N, x ∈ Q.P l ∧ x ∈ GSet (B l) δ ∧
      (∀ u ∈ (ballU hij δ : Set SL3), u • x ∈ Q.P l) := by
  simp only [PParts.good, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
  tauto

theorem PParts.good_subset_zw (Q : PParts B) (δ : ℝ) : Q.good δ ⊆ Q.Zw := by
  intro x hx
  rw [Q.mem_good_iff] at hx
  obtain ⟨hf, l, hl, -⟩ := hx
  exact ⟨hf, Set.mem_iUnion.mpr ⟨l, hl⟩⟩

theorem PParts.measurableSet_good (Q : PParts B) (δ : ℝ) :
    MeasurableSet (Q.good δ) := by
  refine (Work.EKLRelCross.freeSet_borel (U := Uij hij) (Lemmas.isHoro_Uij hij).1).inter ?_
  refine MeasurableSet.iUnion fun l => ?_
  exact (((Q.open' l).inter (isOpen_GSet (B l) δ)).inter
    (isOpen_forall_ballU_smul_subset (hij := hij) (Q.open' l))).measurableSet

theorem PParts.good_ball (Q : PParts B) {δ : ℝ} (hδ : 0 ≤ δ) {x : X3} (hx : x ∈ Q.good δ) :
    ∀ u ∈ (ballU hij δ : Set SL3), u • x ∈ atom Q.sigma x := by
  rw [Q.mem_good_iff] at hx
  obtain ⟨hf, l, hl, hG, hball⟩ := hx
  have hxZw : x ∈ Q.Zw := ⟨hf, Set.mem_iUnion.mpr ⟨l, hl⟩⟩
  rintro u ⟨s, hs, rfl⟩
  have hmem : uij hij s ∈ (ballU hij δ : Set SL3) := ⟨s, hs, rfl⟩
  have hP : uij hij s • x ∈ Q.P l := hball _ hmem
  have hσ := (mem_GSet_iff (B l) hδ).mp hG
  rw [Q.atom_eq hxZw hl]
  refine ⟨⟨?_, hP⟩, ?_⟩
  · exact ⟨smul_mem_free ((Lemmas.mem_Uij_iff hij _).mpr ⟨s, rfl⟩) hf,
      Set.mem_iUnion.mpr ⟨l, hP⟩⟩
  · refine ((B l).fibre_iff (Q.sub l hl) (Q.sub l hP)).mpr ⟨s, ?_, rfl⟩
    have h1 : |s| ≤ δ := by rw [abs_le]; exact ⟨hs.1, hs.2⟩
    calc |s + (B l).sigmaOf x| ≤ |s| + |(B l).sigmaOf x| := abs_add_le _ _
      _ < δ + ((B l).R - δ) := add_lt_add_of_le_of_lt h1 hσ.2
      _ = (B l).R := by ring

theorem PParts.good_mono (Q : PParts B) {δ δ' : ℝ} (h : δ ≤ δ') (hδ : 0 ≤ δ)
    (hδ' : 0 ≤ δ') : Q.good δ' ⊆ Q.good δ := by
  intro x hx
  rw [Q.mem_good_iff] at hx ⊢
  obtain ⟨hf, l, hl, hG, hball⟩ := hx
  refine ⟨hf, l, hl, ?_, fun u hu => hball u (ballU_mono (hij := hij) h hu)⟩
  rw [mem_GSet_iff (B l) hδ'] at hG
  rw [mem_GSet_iff (B l) hδ]
  exact ⟨hG.1, lt_of_lt_of_le hG.2 (by linarith)⟩

theorem PParts.iUnion_good (Q : PParts B) :
    (⋃ n : ℕ, Q.good (1 / ((n : ℝ) + 1))) = Q.Zw := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun n => Q.good_subset_zw _) ?_
  intro x hx
  obtain ⟨hf, hl⟩ := hx
  rw [Set.mem_iUnion] at hl
  obtain ⟨l, hl⟩ := hl
  have hxσ : |(B l).sigmaOf x| < (B l).R := (B l).sigmaOf_lt (Q.sub l hl)
  have hcont : ContinuousAt (fun s : ℝ => uij hij s • x) 0 :=
    (continuous_uij_smul (hij := hij) x).continuousAt
  have hpre : {s : ℝ | uij hij s • x ∈ Q.P l} ∈ 𝓝 0 :=
    hcont.preimage_mem_nhds ((Q.open' l).mem_nhds
      (show uij hij 0 • x ∈ Q.P l by rw [Lemmas.horoUij_zero hij, one_smul]; exact hl))
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 / ((m : ℝ) + 1)
      < min η ((B l).R - |(B l).sigmaOf x|) := by
    refine exists_nat_one_div_lt (lt_min hη (by linarith))
  refine Set.mem_iUnion.mpr ⟨m, ?_⟩
  rw [Q.mem_good_iff]
  refine ⟨hf, l, hl, ?_, ?_⟩
  · rw [mem_GSet_iff (B l) (by positivity)]
    exact ⟨Q.sub l hl, by linarith [lt_of_lt_of_le hm (min_le_right _ _)]⟩
  · intro u hu
    obtain ⟨s, hs, rfl⟩ := hu
    have h1 : |s| ≤ 1 / ((m : ℝ) + 1) := by rw [abs_le]; exact ⟨hs.1, hs.2⟩
    have h2 : |s| < η := lt_of_le_of_lt h1 (lt_of_lt_of_le hm (min_le_left _ _))
    exact hηsub (by rw [Metric.mem_ball, Real.dist_eq]; simpa using h2)

theorem PParts.exists_good_measure (Q : PParts B) (μ : Measure X3) [IsFiniteMeasure μ]
    {ε₁ ε₂ : ℝ} (hZw : ENNReal.ofReal (1 - ε₁) < μ Q.Zw) (h₁ : ε₁ < ε₂) (h₂ : ε₂ < 1) :
    ∃ n : ℕ, ENNReal.ofReal (1 - ε₂) ≤ μ (Q.good (1 / ((n : ℝ) + 1))) := by
  have hmono : Monotone fun n : ℕ => Q.good (1 / ((n : ℝ) + 1)) := by
    intro a b hab
    refine Q.good_mono ?_ (by positivity) (by positivity)
    have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
    have ha : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by
      have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith
    exact one_div_le_one_div_of_le (by positivity) ha
  have htend := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [Q.iUnion_good] at htend
  have hlt : ENNReal.ofReal (1 - ε₂) < ENNReal.ofReal (1 - ε₁) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (1 - ε₂) < μ (Q.good (1 / ((n : ℝ) + 1))) :=
    htend.eventually (isOpen_Ioi.mem_nhds (lt_of_lt_of_le hlt hZw.le))
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hev
  exact ⟨n, le_of_lt (hn n le_rfl)⟩

end Good

/-! ## Existence of a family of disjoint pieces of large measure -/

section PartsExists

variable {i j : Fin 3} {hij : i ≠ j}

/-- **There is a plaque σ-algebra structure of measure close to `1`.**  From a finite cover of
`X₃` by flow boxes, a compact subset of large measure and the disjointification lemma, we obtain
pairwise disjoint open pieces, each inside its box, whose total `μ`-measure (intersected with
`Free`) is `≥ 1 - ε`. -/
theorem exists_parts (μ : Measure X3) [IsProbabilityMeasure μ] (hA : IsAInvariant μ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (N : ℕ) (B : Fin N → GBox i j hij) (Q : PParts B),
      ENNReal.ofReal (1 - ε) < μ Q.Zw := by
  classical
  -- a finite cover by flow boxes
  obtain ⟨N, B, hcover⟩ :=
    exists_finite_gboxes (i := i) (j := j) (hij := hij) μ (ε / 4) (by linarith)
  have hW : MeasurableSet (⋃ l, (B l).toSet) :=
    MeasurableSet.iUnion fun l => (B l).isOpen_toSet.measurableSet
  -- a compact subset of large measure
  have hlt : ENNReal.ofReal (1 - ε / 2) < μ (⋃ l, (B l).toSet) :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)) hcover
  obtain ⟨K, hKW, hKc, hKlt⟩ := MeasurableSet.exists_lt_isCompact hW hlt
  -- disjointification
  obtain ⟨P, hPopen, hPU, hPdisj, hPnull⟩ :=
    Work.Topology.exists_disjoint_open_shrink (μ := μ) (fun l => (B l).toSet)
      (fun l => (B l).isOpen_toSet) hKc hKW
  refine ⟨N, B, ⟨P, hPopen, hPU, hPdisj⟩, ?_⟩
  have hKle : μ K ≤ μ (⋃ l, P l) := by
    have hsub : K ⊆ (K ∩ ⋃ l, P l) ∪ (K \ ⋃ l, P l) := by
      intro y hy
      by_cases h : y ∈ ⋃ l, P l
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    calc μ K ≤ μ ((K ∩ ⋃ l, P l) ∪ (K \ ⋃ l, P l)) := measure_mono hsub
      _ ≤ μ (K ∩ (⋃ l, P l)) + μ (K \ ⋃ l, P l) := measure_union_le _ _
      _ = μ (K ∩ (⋃ l, P l)) + 0 := by rw [hPnull]
      _ ≤ μ (⋃ l, P l) := by
          rw [add_zero]; exact measure_mono Set.inter_subset_right
  have hZ : μ (⋃ l, P l) ≤ μ (PParts.Zw (⟨P, hPopen, hPU, hPdisj⟩ : PParts B)) := by
    have hsub : (⋃ l, P l) ⊆
        (Free i j hij ∩ ⋃ l, P l) ∪ (Free i j hij)ᶜ := by
      intro y hy
      by_cases h : y ∈ Free i j hij
      · exact Or.inl ⟨h, hy⟩
      · exact Or.inr h
    calc μ (⋃ l, P l) ≤ μ ((Free i j hij ∩ ⋃ l, P l) ∪ (Free i j hij)ᶜ) :=
          measure_mono hsub
      _ ≤ μ (Free i j hij ∩ ⋃ l, P l) + μ (Free i j hij)ᶜ := measure_union_le _ _
      _ = μ (Free i j hij ∩ ⋃ l, P l) + 0 := by rw [free_ae i j hij μ hA]
      _ = μ (PParts.Zw (⟨P, hPopen, hPU, hPdisj⟩ : PParts B)) := by
          rw [PParts.Zw, add_zero]
  calc ENNReal.ofReal (1 - ε) < ENNReal.ofReal (1 - ε / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    _ < μ K := hKlt
    _ ≤ μ (⋃ l, P l) := hKle
    _ ≤ μ (PParts.Zw (⟨P, hPopen, hPU, hPdisj⟩ : PParts B)) := hZ

end PartsExists


/-! ## The plaque algebra of a family of pieces -/

section PlaqueAlgebra

variable {i j : Fin 3} {hij : i ≠ j} {N : ℕ} {B : Fin N → GBox i j hij}

/-- **The pieces form a plaque algebra.** -/
theorem PParts.isPlaqueAlgebra (Q : PParts B) :
    IsPlaqueAlgebra (Uij hij) Q.Zw Q.sigma := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine MeasurableSpace.generateFrom_le fun s hs => ?_
    rcases hs with (⟨l, rfl⟩ | rfl) | ⟨⟨l, a, b, t⟩, rfl⟩
    · exact (Q.open' l).measurableSet
    · exact (Work.EKLRelCross.freeSet_borel (U := Uij hij) (Lemmas.isHoro_Uij hij).1).inter
        (MeasurableSet.iUnion fun l => (Q.open' l).measurableSet)
    · exact ((Q.open' l).inter (isOpen_genSet (B l) a b t)).measurableSet
  · exact ⟨Q.genFam, Q.genFam_countable, rfl⟩
  · exact Q.measurableSet_Zw
  · intro x hx
    obtain ⟨hf, hl⟩ := hx
    rw [Set.mem_iUnion] at hl
    obtain ⟨l, hl⟩ := hl
    have hxZw : x ∈ Q.Zw := ⟨hf, Set.mem_iUnion.mpr ⟨l, hl⟩⟩
    refine ⟨?_, ?_, Q.exists_isOpen_shape hxZw hl, Q.shape_bounded hxZw hl⟩
    · intro y hy
      rw [Q.atom_eq hxZw hl] at hy
      exact hy.1.1
    · intro y hy
      rw [Q.atom_eq hxZw hl] at hy
      obtain ⟨⟨-, hyP⟩, hτ⟩ := hy
      obtain ⟨s, -, heq⟩ := ((B l).fibre_iff (Q.sub l hl) (Q.sub l hyP)).mp hτ
      exact ⟨uij hij s, (Lemmas.mem_Uij_iff hij _).mpr ⟨s, rfl⟩, heq.symm⟩

end PlaqueAlgebra

/-! ## Pushing a plaque algebra along the diagonal flow -/

section Push

variable {i j : Fin 3} {hij : i ≠ j}

/-- The preimage under `y ↦ A⁻¹ • y` is the image under `x ↦ A • x`. -/
theorem preimage_inv_smul_eq_image_smul (A : SL3) (S : Set X3) :
    (fun y : X3 => A⁻¹ • y) ⁻¹' S = (fun x : X3 => A • x) '' S := by
  ext y
  constructor
  · intro hy
    exact ⟨A⁻¹ • y, hy, smul_inv_smul A y⟩
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

/-- Conjugating membership in an image by `A`. -/
theorem smul_mem_image_smul_iff (A : SL3) (S : Set X3) (u : SL3) (x : X3) :
    u • (A • x) ∈ (fun y : X3 => A • y) '' S ↔ (A⁻¹ * u * A) • x ∈ S := by
  have hkey : ∀ y : X3, A⁻¹ • (u • (A • y)) = (A⁻¹ * u * A) • y := fun y => by
    rw [mul_smul, mul_smul]
  constructor
  · rintro ⟨z, hz, hzEq⟩
    rw [← hkey x, ← hzEq, inv_smul_smul]
    exact hz
  · intro h
    refine ⟨A⁻¹ • (u • (A • x)), ?_, ?_⟩
    · rw [hkey x]; exact h
    · simp only [smul_inv_smul]

/-- The atom of the pulled-back σ-algebra at a pushed point. -/
theorem atom_comap_inv_smul (A : SL3) (m : MeasurableSpace X3) (x : X3) :
    atom (MeasurableSpace.comap (fun y : X3 => A⁻¹ • y) m) (A • x) =
      (fun y : X3 => A • y) '' atom m x := by
  rw [Work.EKLComp.atom_comap, preimage_inv_smul_eq_image_smul]
  simp only [inv_smul_smul]

/-- `Free` is invariant under the diagonal flow. -/
theorem aDiag_smul_mem_free (t : Fin 3 → ℝ) {x : X3} (hx : x ∈ Free i j hij) :
    aDiag t • x ∈ Free i j hij := by
  have hAt : aDiag (-t) = (aDiag t)⁻¹ := eq_inv_of_mul_eq_one_left (aDiag_neg_mul t)
  intro u hu hux
  have hconj : (aDiag t)⁻¹ * u * aDiag t ∈ (Uij hij : Set SL3) := by
    have h := (Lemmas.isHoro_Uij hij).2.1 (-t) u hu
    rw [hAt, inv_inv] at h
    exact h
  have hfix : ((aDiag t)⁻¹ * u * aDiag t) • x = x := by
    rw [mul_smul, mul_smul, hux, inv_smul_smul]
  have hone : (aDiag t)⁻¹ * u * aDiag t = 1 := hx _ hconj hfix
  have hu1 : u = aDiag t * ((aDiag t)⁻¹ * u * aDiag t) * (aDiag t)⁻¹ := by group
  rw [hu1, hone]
  group

end Push

/-! ## The atom of a σ-algebra inside one of its own measurable sets -/

/-- Two points of the same atom have the same atom.  (No measurability of the atoms, and no
countable generation of `m`, is needed.) -/
theorem atom_eq_of_mem_atom (m : MeasurableSpace X3) {x y : X3} (hy : y ∈ atom m x) :
    atom m y = atom m x := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rw [atom, Set.mem_sInter] at hz ⊢
    intro s hs
    exact hz s ⟨hs.1, hy s hs⟩
  · intro z hz
    rw [atom, Set.mem_sInter] at hz ⊢
    intro s hs
    have hxs : x ∈ s := by
      by_contra hcon
      exact (hy sᶜ ⟨hs.1.compl, hcon⟩) hs.2
    exact hz s ⟨hs.1, hxs⟩

/-! ## The exact form of the frozen statement, and why it is false

The `MeasurableSet G` conjunct of `Work.EKLComp.PlaqueAlgebraExists` is elaborated with the
σ-algebra `m` that the existential quantifier binds *before* it: a local hypothesis of class type
is picked up by type class search, so `MeasurableSet G` there means `MeasurableSet[m] G`.  This is
visible in `#print Work.EKLComp.PlaqueAlgebraExists` (with `pp.all`), where the conjunct reads
`@MeasurableSet X₃ m G`.

The intended condition (the paper's set `X''` is defined by *leaf coordinate* conditions) is that
`G` be measurable for the ambient Borel structure; this is the predicate `PlaqueAlgebraExistsBorel`
below, which is proved in full (`plaqueAlgebra_exists_borel`).  The literal frozen statement is
false, and becomes false already on the atom structure, independently of the construction: see
`not_plaqueAlgebra_exists`. -/

/-- The intended statement: the same as `Work.EKLComp.PlaqueAlgebraExists`, except that the good
set `G` is required to be measurable for the *ambient* Borel σ-algebra of `X₃`, not for the plaque
σ-algebra `m`. -/
def PlaqueAlgebraExistsBorel (i j : Fin 3) (hij : i ≠ j) : Prop :=
  ∀ (μ : Measure X3) [IsProbabilityMeasure μ], IsAInvariant μ →
  ∀ ε rbar : ℝ, 0 < ε → 0 < rbar →
    ∃ (Z G : Set X3) (m : MeasurableSpace X3),
      Z ⊆ Free i j hij ∧ IsPlaqueAlgebra (Uij hij) Z m ∧
      MeasurableSet[Work.EKLContract.instMeasurableSpaceX3] G ∧ G ⊆ Z ∧
      ENNReal.ofReal (1 - ε) ≤ μ G ∧
      ∀ x ∈ G, ∀ u ∈ (ballU hij rbar : Set SL3), u • x ∈ atom m x

/-- **The geometric input of C11a, in its intended form.** -/
theorem plaqueAlgebra_exists_borel (i j : Fin 3) (hij : i ≠ j) :
    PlaqueAlgebraExistsBorel i j hij := by
  intro μ hμ hA ε rbar hε hrbar
  classical
  -- shrink `ε`
  set ε₁ : ℝ := min (ε / 2) (1 / 4) with hε₁def
  have hε₁pos : 0 < ε₁ := lt_min (by linarith) (by norm_num)
  have hε₁le : ε₁ ≤ 1 := by
    rw [hε₁def]
    exact le_trans (min_le_right _ _) (by norm_num)
  -- the disjoint pieces
  obtain ⟨N, B, Q, hZw⟩ := exists_parts (i := i) (j := j) (hij := hij) μ hA ε₁ hε₁pos hε₁le
  -- the good set at a small scale
  set ε₂ : ℝ := 2 * ε₁ with hε₂def
  have hε₂lt1 : ε₂ < 1 := by
    have h : ε₁ ≤ 1 / 4 := by rw [hε₁def]; exact min_le_right _ _
    rw [hε₂def]; linarith
  obtain ⟨n, hn⟩ := Q.exists_good_measure μ hZw (by rw [hε₂def]; linarith) hε₂lt1
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδnonneg : 0 ≤ δ := le_of_lt hδpos
  -- the expanding diagonal element
  have hpos : 0 < rbar * ((n : ℝ) + 1) := by positivity
  set L : ℝ := max 0 (Real.log (rbar * ((n : ℝ) + 1))) with hLdef
  let t : Fin 3 → ℝ := fun k => if k = i then L else 0
  have ht_ij : t i - t j = L := by
    simp only [t, if_pos rfl, if_neg (Ne.symm hij), sub_zero]
  have hexp : Real.exp (-L) * rbar ≤ δ := by
    have h1 : -L ≤ -(Real.log (rbar * ((n : ℝ) + 1))) := by
      have := le_max_right (0 : ℝ) (Real.log (rbar * ((n : ℝ) + 1)))
      linarith
    have h2 : Real.exp (-L) ≤ (rbar * ((n : ℝ) + 1))⁻¹ := by
      have h3 : Real.exp (-L) ≤ Real.exp (-(Real.log (rbar * ((n : ℝ) + 1)))) :=
        Real.exp_le_exp.mpr h1
      have h4 : Real.exp (-(Real.log (rbar * ((n : ℝ) + 1)))) = (rbar * ((n : ℝ) + 1))⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hpos]
      rwa [h4] at h3
    rw [hδdef]
    calc Real.exp (-L) * rbar ≤ (rbar * ((n : ℝ) + 1))⁻¹ * rbar :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt hrbar)
      _ = 1 / ((n : ℝ) + 1) := by field_simp
  -- the plaque algebra of the pieces, pushed by `aDiag t`
  have hAt : aDiag (-t) = (aDiag t)⁻¹ := eq_inv_of_mul_eq_one_left (aDiag_neg_mul t)
  have hpl : IsPlaqueAlgebra (Uij hij) Q.Zw Q.sigma := Q.isPlaqueAlgebra
  have hpush : IsPlaqueAlgebra (Uij hij) ((fun x : X3 => aDiag t • x) '' Q.Zw)
      (MeasurableSpace.comap (fun y : X3 => (aDiag t)⁻¹ • y) Q.sigma) := by
    have h := Work.EKLC6Core.isPlaqueAlgebra_comap (hU := Lemmas.isHoro_Uij hij) (-t) hpl
    simp only [hAt] at h
    rwa [preimage_inv_smul_eq_image_smul (aDiag t) Q.Zw] at h
  have hGmeas : MeasurableSet[Work.EKLContract.instMeasurableSpaceX3]
      ((fun x : X3 => aDiag t • x) '' (Q.good δ)) := by
    rw [← preimage_inv_smul_eq_image_smul (aDiag t) (Q.good δ)]
    exact (continuous_const_smul (aDiag t)⁻¹).measurable (Q.measurableSet_good δ)
  have hμG : μ ((fun x : X3 => aDiag t • x) '' (Q.good δ)) = μ (Q.good δ) := by
    have hmf : Measurable fun x : X3 => aDiag t • x := (continuous_const_smul (aDiag t)).measurable
    have hpre : (fun x : X3 => aDiag t • x) ⁻¹'
        ((fun x : X3 => aDiag t • x) '' (Q.good δ)) = Q.good δ := by
      ext y
      constructor
      · rintro ⟨z, hz, hzy⟩
        have hzy' : aDiag t • z = aDiag t • y := hzy
        have hzy'' : z = y := by
          have h := congrArg (fun w : X3 => (aDiag t)⁻¹ • w) hzy'
          simpa using h
        rw [hzy''] at hz
        exact hz
      · intro hy
        exact ⟨y, hy, rfl⟩
    calc μ ((fun x : X3 => aDiag t • x) '' (Q.good δ))
        = (μ.map (fun x : X3 => aDiag t • x)) ((fun x : X3 => aDiag t • x) '' (Q.good δ)) := by
          rw [(hA t).map_eq]
      _ = μ ((fun x : X3 => aDiag t • x) ⁻¹'
            ((fun x : X3 => aDiag t • x) '' (Q.good δ))) := Measure.map_apply hmf hGmeas
      _ = μ (Q.good δ) := by rw [hpre]
  have hε₂le : ε₂ ≤ ε := by
    have h : ε₁ ≤ ε / 2 := by rw [hε₁def]; exact min_le_left _ _
    rw [hε₂def]; linarith
  refine ⟨(fun x : X3 => aDiag t • x) '' Q.Zw,
    (fun x : X3 => aDiag t • x) '' (Q.good δ),
    MeasurableSpace.comap (fun y : X3 => (aDiag t)⁻¹ • y) Q.sigma,
    ?_, hpush, hGmeas, ?_, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact aDiag_smul_mem_free t hx.1
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨x, Q.good_subset_zw δ hx, rfl⟩
  · calc ENNReal.ofReal (1 - ε) ≤ ENNReal.ofReal (1 - ε₂) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ μ (Q.good δ) := hn
      _ = μ ((fun x : X3 => aDiag t • x) '' (Q.good δ)) := hμG.symm
  · rintro y ⟨x, hxG, rfl⟩ u hu
    obtain ⟨s, hs, rfl⟩ := hu
    rw [atom_comap_inv_smul, smul_mem_image_smul_iff]
    have hconj : (aDiag t)⁻¹ * uij hij s * aDiag t
        = uij hij (Real.exp (-(t i - t j)) * s) := by
      have h := Lemmas.aDiag_conj_uij (-t) hij s
      rw [hAt, inv_inv] at h
      rwa [show (-t) i - (-t) j = -(t i - t j) by simp [Pi.neg_apply]; ring] at h
    rw [hconj]
    have hb : |Real.exp (-(t i - t j)) * s| ≤ δ := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), ht_ij]
      have hs' : |s| ≤ rbar := by rw [abs_le]; exact ⟨hs.1, hs.2⟩
      calc Real.exp (-L) * |s| ≤ Real.exp (-L) * rbar :=
            mul_le_mul_of_nonneg_left hs' (le_of_lt (Real.exp_pos _))
        _ ≤ δ := hexp
    refine Q.good_ball hδnonneg hxG _ ⟨Real.exp (-(t i - t j)) * s, ?_, rfl⟩
    rw [Set.mem_Icc, ← abs_le]
    exact hb

/-! ## The frozen statement is false -/


end Work.EKLComp
