import Mathlib
import Submission.GeoBridge
import Submission.ColumnGeom

set_option autoImplicit false
set_option allowUnsafeReducibility true in
attribute [reducible] Matrix
set_option linter.style.haveILetI false
open MeasureTheory ProbabilityTheory Measure Matrix
open Submission.NormalVectorMatrix (colVec)
open Submission.ColumnGeom (colDist othersSpan)
open scoped ENNReal BigOperators

noncomputable section

/-!
# Column-invariance of the Bernoulli matrix law (measure step)

Tikhomirov 2020, proof of Theorem A: the law of a random matrix with
measurable, mutually independent Bernoulli(`p`) entries is the product of
Bernoulli measures, which is invariant under column permutations.  We record
this as the joint-law identity for the *pair function* of the matrix
(`pairLaw`), the invariance of the product measure under precomposition with
an index equivalence, and the resulting equality of the laws of a matrix and
its column-permuted version.
-/

namespace Submission.ColumnLaw

/-- Measurable space on matrices (pointwise), needed for matrix-level events. -/
instance instMeasurableSpaceMatrix {n : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (inferInstance : MeasurableSpace (Fin n → Fin n → ℝ))

/-- The entries of `C` viewed as a function on `Fin n × Fin n`. -/
def pairOf {n : ℕ} {Ω : Type*} (C : Ω → Matrix (Fin n) (Fin n) ℝ) :
    Ω → (Fin n × Fin n) → ℝ :=
  fun ω x => C ω x.1 x.2

/-- Column-permuted matrix. -/
def colPerm {n : ℕ} (σ : Equiv (Fin n) (Fin n))
    (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => M i (σ j)

/-- The pair function of the column-permuted matrix is the pair function of
`C` precomposed with the index equivalence `(i,j) ↦ (i, σ j)`. -/
lemma pairOf_colPerm {n : ℕ} {Ω : Type*} (C : Ω → Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv (Fin n) (Fin n)) :
    pairOf (fun ω => colPerm σ (C ω)) = fun ω x => pairOf C ω (x.1, σ x.2) := by
  funext ω x
  rfl

/-- With measurable entries that are mutually independent Bernoulli(`p`), the
law of the pair function of `C` is the product measure. -/
lemma pairLaw_eq_pi {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {p : unitInterval}
    (C : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hCmeas : ∀ i j : Fin n, Measurable (fun ω => C ω i j))
    (hBind : iIndepFun (fun x : Fin n × Fin n => (C · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (C · i j) (bernoulliMeasure 1 0 p) P) :
    P.map (pairOf C) = Measure.pi (fun _ : Fin n × Fin n => bernoulliMeasure 1 0 p) := by
  -- measurable family → joint law is the pi product of the marginals
  have hmeas_fam : ∀ x : Fin n × Fin n, AEMeasurable (fun ω => (C · x.1 x.2) ω) P := by
    intro x
    simpa using (hCmeas x.1 x.2).aemeasurable
  have hjoint := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (f := fun x : Fin n × Fin n => fun ω => (C · x.1 x.2) ω) hmeas_fam).1 hBind
  have hlaw_marg : ∀ x : Fin n × Fin n, P.map (fun ω => (C · x.1 x.2) ω) = bernoulliMeasure 1 0 p := by
    intro x
    exact (hBlaw x.1 x.2).map_eq
  -- rewrite the marginals and the map to the pair function
  calc
    P.map (pairOf C) = P.map (fun ω x => (C · x.1 x.2) ω) := by rfl
    _ = Measure.pi (fun x : Fin n × Fin n => P.map (fun ω => (C · x.1 x.2) ω)) := hjoint
    _ = Measure.pi (fun _ : Fin n × Fin n => bernoulliMeasure 1 0 p) := by
      congr 1
      funext x
      exact hlaw_marg x

/-- A product of a constant measure is invariant under precomposition with an
index equivalence. -/
lemma pi_map_precomp_equiv {ι : Type*} [Fintype ι]
    (τ : Equiv ι ι) (μ : Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ] :
    (Measure.pi (fun _ : ι => μ)).map (fun h : ι → ℝ => fun i => h (τ i)) =
      Measure.pi (fun _ : ι => μ) := by
  classical
  -- the coordinate permutation is piCongrLeft τ⁻¹, and pi products are
  -- invariant under index reindexing (measurePreserving_piCongrLeft)
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) τ.symm)
      (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : ι => μ)) := by
    have h := MeasureTheory.measurePreserving_piCongrLeft (α := fun _ : ι => ℝ)
      (μ := fun _ : ι => μ) (f := τ.symm)
    simpa using h
  have heq : (Measure.pi (fun _ : ι => μ)).map
      (⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) τ.symm)) = Measure.pi (fun _ : ι => μ) :=
    hmp.map_eq
  -- the equiv action is precomposition by τ
  have hfun : (fun h : ι → ℝ => fun i => h (τ i)) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) τ.symm) := by
    funext h i
    -- piCongrLeft τ⁻¹ h i = h (τ i)
    rw [MeasurableEquiv.coe_piCongrLeft]
    have ha : (τ.symm) (τ i) = i := Equiv.symm_apply_apply τ i
    conv_rhs => rw [← ha]
    exact (Equiv.piCongrLeft_apply_apply (P := fun _ : ι => ℝ) (e := τ.symm) h (τ i)).symm
  simpa [hfun] using heq 


/-- The law of the pair function of a column-permuted Bernoulli matrix is the
same product measure (column-invariance of the Bernoulli ensemble). -/
theorem pairLaw_colPerm_eq_pi {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {p : unitInterval}
    (C : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hCmeas : ∀ i j : Fin n, Measurable (fun ω => C ω i j))
    (hBind : iIndepFun (fun x : Fin n × Fin n => (C · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (C · i j) (bernoulliMeasure 1 0 p) P)
    (σ : Equiv (Fin n) (Fin n)) :
    P.map (pairOf (fun ω => colPerm σ (C ω))) =
      Measure.pi (fun _ : Fin n × Fin n => bernoulliMeasure 1 0 p) := by
  classical
  let g : Fin n × Fin n → Fin n × Fin n := fun x => (x.1, σ x.2)
  have hginj : Function.Injective g := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
    dsimp [g] at h
    have h₁ : x₁ = y₁ := congrArg Prod.fst h
    have h₂ : σ x₂ = σ y₂ := congrArg Prod.snd h
    exact Prod.ext h₁ (σ.injective h₂)
  -- permuted family is independent
  have hind := ProbabilityTheory.iIndepFun.precomp (g := g)
    (f := fun x : Fin n × Fin n => fun ω => (C · x.1 x.2) ω) hginj hBind
  have hmeasfam : ∀ x : Fin n × Fin n,
      AEMeasurable (fun ω => (C · (g x).1 (g x).2) ω) P := by
    intro x
    -- (g x).1 = x.1, (g x).2 = σ x.2
    simpa [g] using (hCmeas x.1 (σ x.2)).aemeasurable
  have hj := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (f := fun x : Fin n × Fin n => fun ω => (C · (g x).1 (g x).2) ω) hmeasfam).1 hind
  have hlaw_marg : ∀ x : Fin n × Fin n,
      P.map (fun ω => (C · (g x).1 (g x).2) ω) = bernoulliMeasure 1 0 p := by
    intro x
    simpa [g] using (hBlaw x.1 (σ x.2)).map_eq
  -- compute the law of the permuted pair function
  calc
    P.map (pairOf (fun ω => colPerm σ (C ω)))
        = P.map (fun ω x => (C · (g x).1 (g x).2) ω) := rfl
    _ = Measure.pi (fun x : Fin n × Fin n =>
          P.map (fun ω => (C · (g x).1 (g x).2) ω)) := hj
    _ = Measure.pi (fun _ : Fin n × Fin n => bernoulliMeasure 1 0 p) := by
            congr 1
            funext x
            exact hlaw_marg x


/-! ## Transport to the matrix level and per-column event equality -/

/-- Currying a pair function gives a matrix (curried function space). -/
def curryME (n : ℕ) : (Fin n × Fin n → ℝ) ≃ᵐ (Fin n → Fin n → ℝ) :=
  MeasurableEquiv.curry (Fin n) (Fin n) ℝ

/-- The action of `curryME`. -/
lemma curryME_apply {n : ℕ} (g : Fin n × Fin n → ℝ) (i j : Fin n) :
    (curryME n) g i j = g (i, j) := by
  rfl

/-- `pairOf C ω` is the uncurried `C ω`; currying it back recovers `C ω`. -/
lemma pairOf_uncurry {n : ℕ} {Ω : Type*} (C : Ω → Matrix (Fin n) (Fin n) ℝ) (ω : Ω) :
    (curryME n) (pairOf C ω) = C ω := by
  funext i j
  rfl

/-- The law of the matrix is the curried image of the product law. -/
lemma law_matrix_eq_pi_curry {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {p : unitInterval}
    (C : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hCmeas : ∀ i j : Fin n, Measurable (fun ω => C ω i j))
    (hBind : iIndepFun (fun x : Fin n × Fin n => (C · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (C · i j) (bernoulliMeasure 1 0 p) P) :
    P.map C = (Measure.pi (fun _ : Fin n × Fin n => bernoulliMeasure 1 0 p)).map
      (⇑(curryME n)) := by
  -- P.map C = map curry (map (pairOf C) P)
  have hmm : (P.map (pairOf C)).map (⇑(curryME n)) = P.map C := by
    rw [Measure.map_map (g := ⇑(curryME n)) (f := pairOf C) (curryME n).measurable (by
      exact measurable_pi_iff.mpr (by
        intro x
        simpa [pairOf] using hCmeas x.1 x.2))]
    have hfun : (⇑(curryME n) ∘ pairOf C) = C := by
      funext ω
      exact (pairOf_uncurry C ω).symm
    rw [hfun]
  calc
    P.map C = (P.map (pairOf C)).map (⇑(curryME n)) := hmm.symm
    _ = (Measure.pi (fun _ : Fin n × Fin n => bernoulliMeasure 1 0 p)).map (⇑(curryME n)) := by
      rw [pairLaw_eq_pi P C hCmeas hBind hBlaw]

/-- Column-permuting a Bernoulli matrix does not change its law. -/
theorem map_colPerm_eq_map {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {p : unitInterval}
    (C : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hCmeas : ∀ i j : Fin n, Measurable (fun ω => C ω i j))
    (hBind : iIndepFun (fun x : Fin n × Fin n => (C · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (C · i j) (bernoulliMeasure 1 0 p) P)
    (σ : Equiv (Fin n) (Fin n)) :
    P.map (fun ω => colPerm σ (C ω)) = P.map C := by
  let Cp : Ω → Matrix (Fin n) (Fin n) ℝ := fun ω => colPerm σ (C ω)
  have hCpmeas : ∀ i j : Fin n, Measurable (fun ω => Cp ω i j) := by
    intro i j
    dsimp [Cp, colPerm]
    exact hCmeas i (σ j)
  have hCpind : iIndepFun (fun x : Fin n × Fin n => (Cp · x.1 x.2)) P := by
    -- permuted family is independent: precomp with the injective index map
    let g : Fin n × Fin n → Fin n × Fin n := fun x => (x.1, σ x.2)
    have hginj : Function.Injective g := by
      rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
      simp [g] at h
      exact Prod.ext h.1 h.2
    have hind := ProbabilityTheory.iIndepFun.precomp (g := g)
      (f := fun x : Fin n × Fin n => fun ω => (C · x.1 x.2) ω) hginj hBind
    simpa [Cp, colPerm, g] using hind
  have hCplaw : ∀ i j : Fin n, HasLaw (Cp · i j) (bernoulliMeasure 1 0 p) P := by
    intro i j
    simpa [Cp, colPerm] using hBlaw i (σ j)
  calc
    P.map (fun ω => colPerm σ (C ω)) = P.map Cp := by rfl
    _ = (Measure.pi (fun _ : Fin n × Fin n => bernoulliMeasure 1 0 p)).map (⇑(curryME n)) := by
      exact law_matrix_eq_pi_curry P Cp hCpmeas hCpind hCplaw
    _ = P.map C := by
      rw [law_matrix_eq_pi_curry P C hCmeas hBind hBlaw]

/-- Probabilities of measurable matrix events are invariant under column
permutations. -/
theorem measureReal_colPerm_event_eq {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {p : unitInterval}
    (C : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hCmeas : ∀ i j : Fin n, Measurable (fun ω => C ω i j))
    (hBind : iIndepFun (fun x : Fin n × Fin n => (C · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (C · i j) (bernoulliMeasure 1 0 p) P)
    (σ : Equiv (Fin n) (Fin n)) {S : Set (Matrix (Fin n) (Fin n) ℝ)}
    (hS : MeasurableSet S) :
    P.real {ω : Ω | colPerm σ (C ω) ∈ S} = P.real {ω : Ω | C ω ∈ S} := by
  have hmeasC : Measurable (fun ω => C ω) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact hCmeas i j
  have hmeasCp : Measurable (fun ω => colPerm σ (C ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact hCmeas i (σ j)
  have hL := map_colPerm_eq_map P C hCmeas hBind hBlaw σ
  -- evaluate at S
  have h1 : P.map C S = P {ω : Ω | C ω ∈ S} := by
    exact Measure.map_apply hmeasC hS
  have h2 : P.map (fun ω => colPerm σ (C ω)) S = P {ω : Ω | colPerm σ (C ω) ∈ S} := by
    exact Measure.map_apply hmeasCp hS
  -- real measures equal
  have hen : P {ω : Ω | colPerm σ (C ω) ∈ S} = P {ω : Ω | C ω ∈ S} := by
    calc
      P {ω : Ω | colPerm σ (C ω) ∈ S} = P.map (fun ω => colPerm σ (C ω)) S := h2.symm
      _ = P.map C S := by rw [hL]
      _ = P {ω : Ω | C ω ∈ S} := h1
  have hreal : P.real {ω : Ω | colPerm σ (C ω) ∈ S} = P.real {ω : Ω | C ω ∈ S} := by
    dsimp [Measure.real]
    rw [hen]
  exact hreal



/-- Column vectors of a column-permuted matrix: `colVec (colPerm σ M) i =
colVec M (σ i)`. -/
lemma colVec_colPerm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv (Fin n) (Fin n))
    (i : Fin n) : colVec (colPerm σ M) i = colVec M (σ i) := by
  rfl

/-- The span of the other columns is permuted consistently. -/
lemma othersSpan_colPerm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv (Fin n) (Fin n))
    (i : Fin n) : othersSpan (colPerm σ M) i = othersSpan M (σ i) := by
  -- both are spans of the same set of vectors
  have hrange : Set.range (fun k : {j : Fin n // j ≠ i} => colVec (colPerm σ M) (k : Fin n)) =
      Set.range (fun k : {j : Fin n // j ≠ σ i} => colVec M (k : Fin n)) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      have hne : σ (k : Fin n) ≠ σ i := by
        intro h
        exact k.property (σ.injective h)
      refine ⟨⟨σ (k : Fin n), hne⟩, ?_⟩
      exact colVec_colPerm M σ k
    · rintro ⟨k, hk⟩
      let ℓ : {j : Fin n // j ≠ i} := ⟨σ.symm (k : Fin n), by
        intro hℓ
        exact k.property (by simpa using (congrArg σ hℓ))⟩
      refine ⟨ℓ, ?_⟩
      change colVec (colPerm σ M) (ℓ : Fin n) = x
      have hσ : σ (ℓ : Fin n) = k := by
        dsimp [ℓ]
        simp
      rw [colVec_colPerm M σ (ℓ : Fin n)]
      rw [hσ]
      exact hk
  calc
    othersSpan (colPerm σ M) i
        = Submodule.span ℝ (Set.range (fun k : {j : Fin n // j ≠ i} =>
            colVec (colPerm σ M) (k : Fin n))) := rfl
    _ = Submodule.span ℝ (Set.range (fun k : {j : Fin n // j ≠ σ i} =>
            colVec M (k : Fin n))) := by rw [hrange]
    _ = othersSpan M (σ i) := rfl

/-- The column distance is equivariant under column permutations. -/
lemma colDist_colPerm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv (Fin n) (Fin n))
    (i : Fin n) : colDist (colPerm σ M) i = colDist M (σ i) := by
  unfold colDist
  calc
    ‖colVec (colPerm σ M) i
        - (othersSpan (colPerm σ M) i).starProjection (colVec (colPerm σ M) i)‖
        = ‖colVec M (σ i)
            - (othersSpan (colPerm σ M) i).starProjection (colVec M (σ i))‖ := by
              rw [colVec_colPerm M σ i]
    _ = ‖colVec M (σ i)
            - (othersSpan M (σ i)).starProjection (colVec M (σ i))‖ := by
              have hproj : (othersSpan (colPerm σ M) i).starProjection (colVec M (σ i)) =
                  (othersSpan M (σ i)).starProjection (colVec M (σ i)) :=
                Submission.ColumnGeom.starProjection_eq_of_submodule_eq
                  (othersSpan (colPerm σ M) i) (othersSpan M (σ i))
                  (othersSpan_colPerm M σ i) (colVec M (σ i))
              rw [hproj]

/-- Per-column event equality for the Bernoulli ensemble: the probability that
a given column is within `r` of the span of the others does not depend on the
column index. -/
theorem measureReal_colDist_perm_event_eq {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [MeasureTheory.IsProbabilityMeasure P] {p : unitInterval}
    (C : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hCmeas : ∀ i j : Fin n, Measurable (fun ω => C ω i j))
    (hBind : iIndepFun (fun x : Fin n × Fin n => (C · x.1 x.2)) P)
    (hBlaw : ∀ i j : Fin n, HasLaw (C · i j) (bernoulliMeasure 1 0 p) P)
    (σ : Equiv (Fin n) (Fin n)) (i : Fin n) {r : ℝ}
    (hSi : MeasurableSet {M : Matrix (Fin n) (Fin n) ℝ | colDist M i ≤ r}) :
    P.real {ω : Ω | colDist (C ω) (σ i) ≤ r} = P.real {ω : Ω | colDist (C ω) i ≤ r} := by
  have hrew : {ω : Ω | colDist (C ω) (σ i) ≤ r} =
      {ω : Ω | colDist (colPerm σ (C ω)) i ≤ r} := by
    ext ω
    change colDist (C ω) (σ i) ≤ r ↔ colDist (colPerm σ (C ω)) i ≤ r
    rw [colDist_colPerm (C ω) σ i]
  rw [hrew]
  have htr := measureReal_colPerm_event_eq P C hCmeas hBind hBlaw σ (S := {M | colDist M i ≤ r}) hSi
  simpa using htr


end Submission.ColumnLaw
