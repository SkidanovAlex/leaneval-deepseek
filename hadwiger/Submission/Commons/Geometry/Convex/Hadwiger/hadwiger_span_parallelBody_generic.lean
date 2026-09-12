import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.klain333_fin1
import Submission.Commons.Geometry.Convex.Hadwiger.euclidean_valuation_span_v2

open MeasureTheory Metric Set
open scoped Classical Pointwise

namespace Commons.Geometry.Convex.Hadwiger

noncomputable section

abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The unit ball of `V` as a convex body. -/
def hs_unitBallBody (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [CompleteSpace V] : ConvexBody V :=
  ⟨Metric.closedBall (0 : V) 1, convex_closedBall (0 : V) 1, isCompact_closedBall (0 : V) 1,
    Metric.nonempty_closedBall.mpr zero_le_one⟩

/-- The `n + 1` parallel-body volume functionals on convex bodies of `V`. -/
def parallelBodies (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
    (n : ℕ) : Fin (n + 1) → ConvexBody V → ℝ :=
  fun i K => (MeasureTheory.volume ((K + (i : ℝ) • hs_unitBallBody V : ConvexBody V) : Set V)).toReal

/-- The rigid-motion-invariant valuation predicate on `Euc n` (for statements). -/
def IsValE (n : ℕ) (f : ConvexBody (Euc n) → ℝ) : Prop :=
  Continuous f ∧
  (∀ A B C D : ConvexBody (Euc n),
      (A : Set (Euc n)) = (C : Set (Euc n)) ∪ (D : Set (Euc n)) →
      (B : Set (Euc n)) = (C : Set (Euc n)) ∩ (D : Set (Euc n)) → f A + f B = f C + f D) ∧
  (∀ A B : ConvexBody (Euc n), ∀ e : Euc n ≃ₗᵢ[ℝ] Euc n,
      (B : Set (Euc n)) = e '' (A : Set (Euc n)) → f B = f A) ∧
  (∀ A B : ConvexBody (Euc n), ∀ t : Euc n,
      (B : Set (Euc n)) = (fun x : Euc n => x + t) '' (A : Set (Euc n)) → f A = f B)

/-- The Euclidean Hadwiger classification statement at dimension `n`. -/
def EuclidClassification (n : ℕ) : Prop :=
  ∀ f : ConvexBody (Euc n) → ℝ, IsValE n f → f ∈ Submodule.span ℝ (Set.range (parallelBodies (Euc n) n))

-- ============================================================
-- Transport of valuations along a linear isometry `V ≃ₗᵢ Euc n`
-- ============================================================

/-- Image of an additive set under a linear isometry equivalence. -/
lemma hs_lie_image_add {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (s t : Set V) : e '' (s + t) = e '' s + e '' t := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    exact ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, (e.map_add a b).symm⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    rcases hp with ⟨a, ha, rfl⟩
    rcases hq with ⟨b, hb, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, e.map_add a b⟩

/-- Image of a scalar multiple under a linear isometry equivalence. -/
lemma hs_lie_image_smul {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (t : ℝ) (s : Set V) : e '' (t • s) = t • (e '' s) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (mem_smul_set.mp hx) with ⟨a, ha, rfl⟩
    exact ⟨e a, ⟨a, ha, rfl⟩, (e.map_smul t a).symm⟩
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨a, ha, rfl⟩
    exact ⟨t • a, ⟨a, ha, rfl⟩, e.map_smul t a⟩

/-- The unit ball is mapped onto the unit ball. -/
lemma hs_lie_image_unitBall {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [CompleteSpace W]
    (e : V ≃ₗᵢ[ℝ] W) :
    e '' (hs_unitBallBody V : Set V) = (hs_unitBallBody W : Set W) := by
  change e '' (Metric.closedBall (0 : V) 1) = Metric.closedBall (0 : W) 1
  rw [e.image_closedBall (0 : V) 1]
  simp

/-- The image (under a linear isometry) of a parallel body is the corresponding
parallel body of the image. -/
lemma imageLIE_parallelBody_set {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [CompleteSpace W]
    (e : V ≃ₗᵢ[ℝ] W) (K : ConvexBody V) (t : ℝ) :
    e '' ((K : Set V) + t • (hs_unitBallBody V : Set V)) =
      (e '' (K : Set V)) + t • (hs_unitBallBody W : Set W) := by
  rw [hs_lie_image_add, hs_lie_image_smul, hs_lie_image_unitBall]

/-- A linear isometry between finite-dimensional real inner product spaces preserves
the canonical volume. -/
lemma measure_image_lie {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (s : Set V) : volume (e '' s) = volume s := by
  have hmp := e.measurePreserving
  have hemb := e.toHomeomorph.measurableEmbedding
  calc
    volume (e '' s) = volume (e ⁻¹' (e '' s)) :=
      (hmp.measure_preimage_emb hemb (e '' s)).symm
    _ = volume s := by rw [Set.preimage_image_eq s e.injective]

/-- Parallel-body volumes commute with a linear isometry `V → W`. -/
lemma parallelBodies_imageLIE {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (n : ℕ) (i : Fin (n + 1)) (K : ConvexBody V) :
    parallelBodies W n i (ConvexBody.imageLIE e K) = parallelBodies V n i K := by
  unfold parallelBodies
  congr 1
  rw [← measure_image_lie e ((K + (i : ℝ) • hs_unitBallBody V : ConvexBody V) : Set V)]
  congr 1
  rw [ConvexBody.coe_add, ConvexBody.coe_add, ConvexBody.coe_smul, ConvexBody.coe_smul]
  exact (imageLIE_parallelBody_set e K (i : ℝ)).symm

/-- Conjugate a functional on `V`-bodies to one on `W`-bodies. -/
def conjValuation {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (f : ConvexBody V → ℝ) : ConvexBody W → ℝ :=
  fun L => f (ConvexBody.imageLIE e.symm L)

theorem conjValuation_image {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) (f : ConvexBody V → ℝ) (K : ConvexBody V) :
    conjValuation e f (ConvexBody.imageLIE e K) = f K := by
  unfold conjValuation
  rw [imageLIE_symm_imageLIE]

theorem conjValuation_continuous {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) {f : ConvexBody V → ℝ} (hcont : Continuous f) :
    Continuous (conjValuation e f) := by
  unfold conjValuation
  exact hcont.comp (imageLIE_isometry e.symm).continuous

theorem conjValuation_add {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) {f : ConvexBody V → ℝ}
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → f A + f B = f C + f D) :
    ∀ A B C D : ConvexBody W,
        (A : Set W) = (C : Set W) ∪ (D : Set W) →
        (B : Set W) = (C : Set W) ∩ (D : Set W) →
        conjValuation e f A + conjValuation e f B = conjValuation e f C + conjValuation e f D := by
  intro A B C D hU hI
  unfold conjValuation
  have hA : (ConvexBody.imageLIE e.symm A : Set V) =
      (ConvexBody.imageLIE e.symm C : Set V) ∪ (ConvexBody.imageLIE e.symm D : Set V) := by
    rw [imageLIE_apply, imageLIE_apply, imageLIE_apply, hU, Set.image_union]
  have hB : (ConvexBody.imageLIE e.symm B : Set V) =
      (ConvexBody.imageLIE e.symm C : Set V) ∩ (ConvexBody.imageLIE e.symm D : Set V) := by
    rw [imageLIE_apply, imageLIE_apply, imageLIE_apply, hI,
      Set.image_inter (e.symm.injective)]
  exact hadd (ConvexBody.imageLIE e.symm A) (ConvexBody.imageLIE e.symm B)
    (ConvexBody.imageLIE e.symm C) (ConvexBody.imageLIE e.symm D) hA hB

/-- Linear-isometry invariance transfers by conjugation of the isometry. -/
theorem conjValuation_isometry {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) {f : ConvexBody V → ℝ}
    (hiso : ∀ A B : ConvexBody V, ∀ e' : V ≃ₗᵢ[ℝ] V,
        (B : Set V) = e' '' (A : Set V) → f B = f A) :
    ∀ A B : ConvexBody W, ∀ e' : W ≃ₗᵢ[ℝ] W,
        (B : Set W) = e' '' (A : Set W) →
        conjValuation e f B = conjValuation e f A := by
  intro A B e' hB
  unfold conjValuation
  let e'' : V ≃ₗᵢ[ℝ] V := (e.trans e').trans e.symm
  apply hiso (ConvexBody.imageLIE e.symm A) (ConvexBody.imageLIE e.symm B) e''
  rw [imageLIE_apply, imageLIE_apply, hB]
  -- goal: e.symm '' (e' '' A) = e'' '' (e.symm '' A)
  rw [Set.image_image, Set.image_image]
  congr 1
  funext x
  simp [e'', LinearIsometryEquiv.trans_apply, e.apply_symm_apply]

theorem conjValuation_trans {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : V ≃ₗᵢ[ℝ] W) {f : ConvexBody V → ℝ}
    (htrans : ∀ A B : ConvexBody V, ∀ t : V,
        (B : Set V) = (fun x : V => x + t) '' (A : Set V) → f A = f B) :
    ∀ A B : ConvexBody W, ∀ t : W,
        (B : Set W) = (fun x : W => x + t) '' (A : Set W) →
        conjValuation e f A = conjValuation e f B := by
  intro A B t hB
  unfold conjValuation
  apply htrans (ConvexBody.imageLIE e.symm A) (ConvexBody.imageLIE e.symm B) (e.symm t)
  rw [imageLIE_apply, imageLIE_apply, hB]
  exact lie_image_translate (e := e.symm) (A := (A : Set W)) (t := t)

/-- Given the Euclidean classification, any valuation on a generic `V` of the same
dimension lies in the span of its parallel-body volumes. -/
theorem valuation_span_of_euclid_classification
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : ℕ) (hn : Module.finrank ℝ V = n)
    (f : ConvexBody V → ℝ)
    (hcont : Continuous f)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → f A + f B = f C + f D)
    (hiso : ∀ A B : ConvexBody V, ∀ e : V ≃ₗᵢ[ℝ] V,
        (B : Set V) = e '' (A : Set V) → f B = f A)
    (htrans : ∀ A B : ConvexBody V, ∀ t : V,
        (B : Set V) = (fun x : V => x + t) '' (A : Set V) → f A = f B)
    (hcls : EuclidClassification n) :
    f ∈ Submodule.span ℝ (Set.range (parallelBodies V n)) := by
  classical
  -- a linear isometry from V onto the model space Euc n
  let b₀ := stdOrthonormalBasis ℝ V
  let hcard : Fintype.card (Fin (Module.finrank ℝ V)) = n := by
    simpa using hn
  let eqv : Fin (Module.finrank ℝ V) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b : OrthonormalBasis (Fin n) ℝ V := b₀.reindex eqv
  let e : V ≃ₗᵢ[ℝ] Euc n := b.repr
  -- conjugate f to the model space
  let g : ConvexBody (Euc n) → ℝ := conjValuation e f
  have hgcont : Continuous g := conjValuation_continuous e hcont
  have hgadd : ∀ A B C D : ConvexBody (Euc n),
      (A : Set (Euc n)) = (C : Set (Euc n)) ∪ (D : Set (Euc n)) →
      (B : Set (Euc n)) = (C : Set (Euc n)) ∩ (D : Set (Euc n)) →
      g A + g B = g C + g D := conjValuation_add e hadd
  have hgiso : ∀ A B : ConvexBody (Euc n), ∀ e' : Euc n ≃ₗᵢ[ℝ] Euc n,
      (B : Set (Euc n)) = e' '' (A : Set (Euc n)) → g B = g A :=
    conjValuation_isometry e hiso
  have hgtrans : ∀ A B : ConvexBody (Euc n), ∀ t : Euc n,
      (B : Set (Euc n)) = (fun x : Euc n => x + t) '' (A : Set (Euc n)) → g A = g B :=
    conjValuation_trans e htrans
  have hgIsVal : IsValE n g := ⟨hgcont, hgadd, hgiso, hgtrans⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := parallelBodies (Euc n) n)).1
    (hcls g hgIsVal)
  -- c : Fin (n + 1) → ℝ, hc : (∑ i, c i • parallelBodies (Euc n) n i) = g
  refine (Submodule.mem_span_range_iff_exists_fun (R := ℝ) (v := parallelBodies V n)).2 ⟨c, ?_⟩
  funext K
  calc
    (∑ i : Fin (n + 1), c i • parallelBodies V n i) K
        = ∑ i : Fin (n + 1), c i * parallelBodies V n i K := by
          simp [Pi.smul_apply]
    _ = ∑ i : Fin (n + 1), c i * parallelBodies (Euc n) n i (ConvexBody.imageLIE e K) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [parallelBodies_imageLIE e n i K]
    _ = (∑ i : Fin (n + 1), c i • parallelBodies (Euc n) n i) (ConvexBody.imageLIE e K) := by
          simp [Pi.smul_apply]
    _ = g (ConvexBody.imageLIE e K) := by
          rw [hc]
    _ = f K := conjValuation_image e f K


theorem euclid_classification (n : ℕ) : EuclidClassification n := by
  intro f hf
  obtain ⟨hcont, hadd, hiso, htrans⟩ := hf
  exact euclidean_valuation_span_v2 n f hcont hadd hiso htrans

theorem hadwiger_span_parallelBody_generic
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (n : ℕ) (hn : Module.finrank ℝ V = n)
    (f : ConvexBody V → ℝ)
    (hcont : Continuous f)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → f A + f B = f C + f D)
    (hiso : ∀ A B : ConvexBody V, ∀ e : V ≃ₗᵢ[ℝ] V,
        (B : Set V) = e '' (A : Set V) → f B = f A)
    (htrans : ∀ A B : ConvexBody V, ∀ t : V,
        (B : Set V) = (fun x : V => x + t) '' (A : Set V) → f A = f B) :
    let B : ConvexBody V := ⟨Metric.closedBall (0 : V) 1, convex_closedBall (0 : V) 1, isCompact_closedBall (0 : V) 1, Metric.nonempty_closedBall.mpr zero_le_one⟩
    let F : Fin (n + 1) → ConvexBody V → ℝ := fun i K => (MeasureTheory.volume ((K + (i : ℝ) • B : ConvexBody V) : Set V)).toReal
    f ∈ Submodule.span ℝ (Set.range F) := by
  classical
  change f ∈ Submodule.span ℝ (Set.range (parallelBodies V n))
  exact valuation_span_of_euclid_classification (V := V) n hn f hcont hadd hiso htrans
    (euclid_classification n)
