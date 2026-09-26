import Mathlib
import Submission.Work.Drive.Mono.JunctionGenC
import Submission.Work.CoreTopology.isClosed_carrier

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-!
# The corner locus of the box level is finite for almost every centre and level

This file proves `Work.Drive.Mono.ae_ae_cornerLocus_finite`.

For a box centre `c`, a level `s > 0` and a permutation `σ` of the coordinates, the *corner locus*
is the set of points of the surface `F = ψ(standard torus)` with two `σ`-extremal box coordinates.
It is contained in the union, over the ordered pairs `i ≠ j` and the sign choices `εi, εj ∈ {±1}`,
of the fibres of the pair map

`cornerProj ψ σ i j : (θ, φ) ↦ (param ψ (θ, φ) (σ i), param ψ (θ, φ) (σ j))`

over the value `(c (σ i) + εi * boxSide i * s, c (σ j) + εj * boxSide j * s)`.

Two ingredients make the argument work.

* **Sard in dimension two.**  The critical values of the pair map are Lebesgue-null
  (`cornerCritVals_null`, from Mathlib's fixed-dimension Sard lemma) and Borel
  (`cornerCritVals_measurable`, the critical set is closed and the parameter plane is exhausted by
  balls).
* **Finiteness of the fibre over a non-critical value.**  If the fibre over `v` were infinite, the
  compactness of the fundamental square `[0, 2π]²` (the parametrisation is `2π`-periodic in each
  variable) would produce a sequence of distinct parameters, all mapped to `v`, converging to some
  parameter `p`; the inverse function theorem would make the pair map a local bijection at `p`,
  so the sequence must be eventually constant — a contradiction.  Hence `v` is a critical value
  (`cornerFibre_infinite_subset_critVals`).

Since `sgn : Bool → {±1}` is onto, the linear maps `(c, s) ↦ (c (σ i) + εi * boxSide i * s,
c (σ j) + εj * boxSide j * s)` are surjective, so the preimage of the null set of critical values
is null (`ae_cornerLin_notMem`, via `MeasureTheory.ae_comp_linearMap_mem_iff`); Fubini
(`Measure.ae_ae_of_ae_prod`) then gives the a.e.-in-`c`-then-a.e.-in-`s` statement.
-/

/-- The pair of `σ`-coordinates `(σ i, σ j)` of the surface, read in the parameter plane. -/
def cornerProj (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (ℝ × ℝ) → (ℝ × ℝ) :=
  fun p => (Work.Smooth.Morse.param ψ p (σ i), Work.Smooth.Morse.param ψ p (σ j))

theorem cornerProj_contDiff (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (cornerProj ψ σ i j) := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Work.Smooth.Morse.param ψ p (σ i)) :=
    ContDiff.continuousLinearMap_comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (σ i))
      (Work.Smooth.Morse.param_contDiff ψ)
  have hB : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Work.Smooth.Morse.param ψ p (σ j)) :=
    ContDiff.continuousLinearMap_comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) (σ j))
      (Work.Smooth.Morse.param_contDiff ψ)
  exact hA.prodMk hB

/-- The critical set of the pair projection, in the parameter plane. -/
def cornerCrit (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    Set (ℝ × ℝ) :=
  {p | (fderiv ℝ (cornerProj ψ σ i j) p).det = 0}

/-- The critical values of the pair projection. -/
def cornerCritVals (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    Set (ℝ × ℝ) :=
  cornerProj ψ σ i j '' cornerCrit ψ σ i j

theorem cornerCrit_isClosed (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    IsClosed (cornerCrit ψ σ i j) := by
  have hc : Continuous (fun p : ℝ × ℝ => (fderiv ℝ (cornerProj ψ σ i j) p).det) :=
    ContinuousLinearMap.continuous_det.comp
      ((cornerProj_contDiff ψ σ i j).continuous_fderiv (by norm_num))
  exact isClosed_eq hc continuous_const

/-- **Sard in dimension two**: the critical values of the pair projection are Lebesgue-null. -/
theorem cornerCritVals_null (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    volume (cornerCritVals ψ σ i j) = 0 := by
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
    (s := cornerCrit ψ σ i j) (f := cornerProj ψ σ i j)
    (f' := fun p => fderiv ℝ (cornerProj ψ σ i j) p) ?_ ?_
  · intro x _
    exact ((cornerProj_contDiff ψ σ i j).differentiable (by norm_num)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    exact hx

/-- The set of critical values of the pair projection is Borel (it is a countable union of
continuous images of the compacta `closedBall 0 n`). -/
theorem cornerCritVals_measurable (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    MeasurableSet (cornerCritVals ψ σ i j) := by
  have hcover : cornerCrit ψ σ i j =
      ⋃ n : ℕ, cornerCrit ψ σ i j ∩ Metric.closedBall (0 : ℝ × ℝ) (n : ℝ) := by
    rw [Metric.iUnion_inter_closedBall_nat]
  rw [cornerCritVals, hcover, Set.image_iUnion]
  refine MeasurableSet.iUnion (fun n : ℕ => ?_)
  exact (((isCompact_closedBall (0 : ℝ × ℝ) (n : ℝ)).inter_left
    (cornerCrit_isClosed ψ σ i j)).image (cornerProj_contDiff ψ σ i j).continuous).isClosed.measurableSet

/-- The fibre of the pair projection over `v`, on the surface. -/
def cornerFibre (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3)
    (v : ℝ × ℝ) : Set R3 :=
  {z : R3 | z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧ z (σ i) = v.1 ∧ z (σ j) = v.2}

/-- `param ψ` only depends on the parameters modulo `2π`, so it is unchanged by `redParam`. -/
theorem param_redParam (ψ : Submission.Diffeo) (x y : ℝ) :
    Work.Smooth.Morse.param ψ (Work.CoreTopology.redParam x, Work.CoreTopology.redParam y)
      = Work.Smooth.Morse.param ψ (x, y) := by
  rw [← Work.Smooth.Morse.torus_psi, ← Work.Smooth.Morse.torus_psi,
    Work.CoreTopology.psi_redParam]

/-- **An infinite fibre forces a critical value.**  If the fibre of the pair projection over `v`
meets the surface in infinitely many points, then `v` is a critical value: the fundamental square
is compact, so the fibre has an accumulation point in the parameter plane, and the inverse function
theorem rules out a regular accumulation point. -/
theorem cornerFibre_infinite_subset_critVals (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3))
    (i j : Fin 3) {v : ℝ × ℝ} (hinf : (cornerFibre ψ σ i j v).Infinite) :
    v ∈ cornerCritVals ψ σ i j := by
  classical
  set K : Set (ℝ × ℝ) := Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi) with hK
  set G : Set (ℝ × ℝ) := {p | p ∈ K ∧ cornerProj ψ σ i j p = v} with hG
  have hGK : G ⊆ K := fun p hp => hp.1
  have hchoose : ∀ z : R3, z ∈ cornerFibre ψ σ i j v →
      ∃ p : ℝ × ℝ, p ∈ G ∧ Work.Smooth.Morse.param ψ (p.1, p.2) = z := by
    intro z hz
    rw [cornerFibre, Set.mem_ofPred_eq] at hz
    obtain ⟨hcar, hz1, hz2⟩ := hz
    rw [Work.Smooth.Morse.torus_carrier, Set.mem_range] at hcar
    obtain ⟨⟨x, y⟩, hxy⟩ := hcar
    refine ⟨(Work.CoreTopology.redParam x, Work.CoreTopology.redParam y),
      ⟨⟨Work.CoreTopology.redParam_mem x, Work.CoreTopology.redParam_mem y⟩, ?_⟩, ?_⟩
    · have hred : Work.Smooth.Morse.param ψ
          (Work.CoreTopology.redParam x, Work.CoreTopology.redParam y) = z := by
        rw [param_redParam, hxy]
      rw [cornerProj, hred, hz1, hz2]
    · rw [param_redParam, hxy]
  let f : R3 → ℝ × ℝ := fun z =>
    if hz : z ∈ cornerFibre ψ σ i j v then Classical.choose (hchoose z hz) else 0
  have hf : ∀ z (hz : z ∈ cornerFibre ψ σ i j v), f z ∈ G ∧
      Work.Smooth.Morse.param ψ ((f z).1, (f z).2) = z := by
    intro z hz
    simp only [f, dif_pos hz]
    exact Classical.choose_spec (hchoose z hz)
  have hGinf : G.Infinite := by
    refine Set.Infinite.mono (Set.image_subset_iff.mpr (fun z hz => (hf z hz).1)) ?_
    refine hinf.image ?_
    intro z hz z' hz' h
    rw [← (hf z hz).2, h, (hf z' hz').2]
  have hGclosed : IsClosed G := by
    have h1 : IsClosed (cornerProj ψ σ i j ⁻¹' {v}) :=
      isClosed_singleton.preimage (cornerProj_contDiff ψ σ i j).continuous
    have h2 : IsClosed K := isClosed_Icc.prod isClosed_Icc
    rw [hG]
    exact h2.inter h1
  have hGcompact : IsCompact G :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hGclosed hGK
  let x : ℕ → ℝ × ℝ := fun n =>
    ((Set.Infinite.natEmbedding G hGinf n : G) : ℝ × ℝ)
  have hxmem : ∀ n, x n ∈ G := fun n => (Set.Infinite.natEmbedding G hGinf n).2
  have hxinj : Function.Injective x := by
    intro m n h
    have h' : (Set.Infinite.natEmbedding G hGinf m : G)
        = Set.Infinite.natEmbedding G hGinf n := Subtype.ext h
    exact (Set.Infinite.natEmbedding G hGinf).injective h'
  obtain ⟨a, haG, φ, hφ, hlim⟩ := hGcompact.tendsto_subseq hxmem
  have hua : cornerProj ψ σ i j a = v := haG.2
  have hcrit : (fderiv ℝ (cornerProj ψ σ i j) a).det = 0 := by
    by_contra hne
    have hstr : HasStrictFDerivAt (cornerProj ψ σ i j)
        (fderiv ℝ (cornerProj ψ σ i j) a) a :=
      (cornerProj_contDiff ψ σ i j).hasStrictFDerivAt (by norm_num)
    set e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
      (fderiv ℝ (cornerProj ψ σ i j) a).toContinuousLinearEquivOfDetNeZero hne with he
    have he' : (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = fderiv ℝ (cornerProj ψ σ i j) a :=
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have hstr' : HasStrictFDerivAt (cornerProj ψ σ i j) (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) a := by
      rw [he']; exact hstr
    have hev : ∀ᶠ n in Filter.atTop,
        hstr'.localInverse (cornerProj ψ σ i j) e a (cornerProj ψ σ i j (x (φ n))) = x (φ n) :=
      hlim.eventually hstr'.eventually_left_inverse
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    have h1 := hN N le_rfl
    have h2 := hN (N + 1) (Nat.le_succ N)
    have hx0 : ∀ n, cornerProj ψ σ i j (x n) = v := fun n => (hxmem n).2
    have hEq : x (φ N) = x (φ (N + 1)) := by
      rw [← h1, ← h2, hx0 (φ N), hx0 (φ (N + 1))]
    exact absurd (hxinj hEq) (ne_of_lt (hφ (Nat.lt_succ_self N)))
  exact ⟨a, hcrit, hua⟩

/-- Almost every value of the pair projection has a finite fibre on the surface. -/
theorem ae_cornerFibre_finite (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    ∀ᵐ v ∂(volume : Measure (ℝ × ℝ)), (cornerFibre ψ σ i j v).Finite := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (cornerCritVals_null ψ σ i j)
  intro v hv
  exact cornerFibre_infinite_subset_critVals ψ σ i j (by simpa using hv)

/-- The affine-linear map `(c, s) ↦ (c (σ i) + εi * boxSide i * s, c (σ j) + εj * boxSide j * s)`
whose value at `(c, s)` is the pair of box-corner values of the family `(i, j, εi, εj)`. -/
def cornerLin (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) (εi εj : ℝ) :
    (R3 × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun w := (w.1 (σ i) + εi * Submission.boxSide i * w.2,
              w.1 (σ j) + εj * Submission.boxSide j * w.2)
  map_add' w w' := Prod.ext (by simp; ring) (by simp; ring)
  map_smul' a w := Prod.ext (by simp; ring) (by simp; ring)

@[simp] theorem cornerLin_apply (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) (εi εj : ℝ)
    (c : R3) (s : ℝ) :
    cornerLin σ i j εi εj (c, s) =
      (c (σ i) + εi * Submission.boxSide i * s, c (σ j) + εj * Submission.boxSide j * s) := rfl

/-- `cornerLin` is onto for `i ≠ j` (the two coordinates `σ i ≠ σ j` can be prescribed freely). -/
theorem cornerLin_surjective (σ : Equiv.Perm (Fin 3)) {i j : Fin 3} (hij : i ≠ j)
    (εi εj : ℝ) : Function.Surjective (cornerLin σ i j εi εj) := by
  intro v
  refine ⟨(WithLp.toLp 2 (Function.update (Function.update (0 : Fin 3 → ℝ) (σ i) v.1)
    (σ j) v.2), 0), ?_⟩
  have hne : σ i ≠ σ j := fun h => hij (σ.injective h)
  have hi : ((WithLp.toLp 2 (Function.update (Function.update (0 : Fin 3 → ℝ) (σ i) v.1)
      (σ j) v.2)) : R3) (σ i) = v.1 := by
    simp [Function.update_of_ne hne]
  have hj : ((WithLp.toLp 2 (Function.update (Function.update (0 : Fin 3 → ℝ) (σ i) v.1)
      (σ j) v.2)) : R3) (σ j) = v.2 := by
    simp
  rw [show cornerLin σ i j εi εj
      (WithLp.toLp 2 (Function.update (Function.update (0 : Fin 3 → ℝ) (σ i) v.1)
        (σ j) v.2), 0) =
      (((WithLp.toLp 2 (Function.update (Function.update (0 : Fin 3 → ℝ) (σ i) v.1)
        (σ j) v.2)) : R3) (σ i) + εi * Submission.boxSide i * (0:ℝ),
        ((WithLp.toLp 2 (Function.update (Function.update (0 : Fin 3 → ℝ) (σ i) v.1)
        (σ j) v.2)) : R3) (σ j) + εj * Submission.boxSide j * (0:ℝ)) from rfl]
  rw [hi, hj]
  simp

/-- The two signs, as reals. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sgn_true : sgn true = 1 := rfl

@[simp] theorem sgn_false : sgn false = -1 := rfl

/-- **The corner values of one family avoid the critical values, almost surely.** -/
theorem ae_cornerLin_notMem (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) {i j : Fin 3}
    (hij : i ≠ j) (εi εj : Bool) :
    ∀ᵐ w ∂(volume : Measure (R3 × ℝ)),
      cornerLin σ i j (sgn εi) (sgn εj) w ∉ cornerCritVals ψ σ i j := by
  haveI : MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure (R3 × ℝ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod R3 ℝ]
    exact MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _
  have hiff := MeasureTheory.ae_comp_linearMap_mem_iff (cornerLin σ i j (sgn εi) (sgn εj))
    (volume : Measure (R3 × ℝ)) (volume : Measure (ℝ × ℝ))
    (cornerLin_surjective σ hij (sgn εi) (sgn εj)) (cornerCritVals_measurable ψ σ i j).compl
  refine hiff.mpr ?_
  rw [MeasureTheory.ae_iff]
  simpa using cornerCritVals_null ψ σ i j

/-- **The sign split of the extremality conditions.**  A point of the surface whose `σ i`- and
`σ j`-coordinates are extremal for the box (at level `s > 0`) lies in one of the four corner
families. -/
theorem cornerFibre_mem_of_abs_eq (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3))
    {i j : Fin 3} {c : R3} {s : ℝ} (hs : 0 < s) {z : R3}
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (h1 : |z (σ i) - c (σ i)| = Submission.boxSide i * s)
    (h2 : |z (σ j) - c (σ j)| = Submission.boxSide j * s) :
    ∃ εi εj : Bool, z ∈ cornerFibre ψ σ i j (cornerLin σ i j (sgn εi) (sgn εj) (c, s)) := by
  have hspos : 0 < Submission.boxSide i * s := mul_pos (Submission.boxSide_pos i) hs
  have hspos' : 0 < Submission.boxSide j * s := mul_pos (Submission.boxSide_pos j) hs
  obtain h1' | h1' := (abs_eq hspos.le).mp h1
  · obtain h2' | h2' := (abs_eq hspos'.le).mp h2
    · exact ⟨true, true, hz, by simp only [cornerLin_apply, sgn_true, one_mul]; linarith,
        by simp only [cornerLin_apply, sgn_true, one_mul]; linarith⟩
    · exact ⟨true, false, hz, by simp only [cornerLin_apply, sgn_true, one_mul]; linarith,
        by simp only [cornerLin_apply, sgn_false, neg_one_mul]; linarith⟩
  · obtain h2' | h2' := (abs_eq hspos'.le).mp h2
    · exact ⟨false, true, hz, by simp only [cornerLin_apply, sgn_false, neg_one_mul]; linarith,
        by simp only [cornerLin_apply, sgn_true, one_mul]; linarith⟩
    · exact ⟨false, false, hz, by simp only [cornerLin_apply, sgn_false, neg_one_mul]; linarith,
        by simp only [cornerLin_apply, sgn_false, neg_one_mul]; linarith⟩

/-- The corner locus of the box level `s` with centre `c` and permutation `σ`. -/
def cornerLocus (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (c : R3) (s : ℝ) : Set R3 :=
  {z : R3 | z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
    ∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
      |z (σ j) - c (σ j)| = Submission.boxSide j * s}

/-- **The corner locus is finite at a level whose corner values avoid the critical values.** -/
theorem cornerLocus_finite_of_forall (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3))
    (c : R3) (s : ℝ) (hs : 0 < s)
    (hgood : ∀ (i j : Fin 3), i ≠ j → ∀ εi εj : Bool,
      cornerLin σ i j (sgn εi) (sgn εj) (c, s) ∉ cornerCritVals ψ σ i j) :
    (cornerLocus ψ σ c s).Finite := by
  have hfib : ∀ (i j : Fin 3), i ≠ j → ∀ εi εj : Bool,
      (cornerFibre ψ σ i j (cornerLin σ i j (sgn εi) (sgn εj) (c, s))).Finite := by
    intro i j hij εi εj
    by_contra hinf
    exact hgood i j hij εi εj (cornerFibre_infinite_subset_critVals ψ σ i j hinf)
  set Idx : Finset ((Fin 3 × Fin 3) × (Bool × Bool)) :=
    Finset.univ.filter (fun p => p.1.1 ≠ p.1.2) with hIdx
  set T : ((Fin 3 × Fin 3) × (Bool × Bool)) → Set R3 := fun p =>
    cornerFibre ψ σ p.1.1 p.1.2 (cornerLin σ p.1.1 p.1.2 (sgn p.2.1) (sgn p.2.2) (c, s)) with hT
  have hTfin : ∀ p ∈ (Idx : Set ((Fin 3 × Fin 3) × (Bool × Bool))), (T p).Finite := by
    intro p hp
    have hij : p.1.1 ≠ p.1.2 := (Finset.mem_filter.mp hp).2
    exact hfib p.1.1 p.1.2 hij p.2.1 p.2.2
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet Idx) hTfin) ?_
  rintro z ⟨hz, i, j, hij, h1, h2⟩
  obtain ⟨εi, εj, hmem⟩ := cornerFibre_mem_of_abs_eq ψ σ hs hz h1 h2
  exact Set.mem_biUnion (x := ((i, j), (εi, εj)))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩) hmem
/-- **The corner locus of the box level is finite for almost every box centre and almost every
level.**

The corner locus of the box `PBox s c σ` on the surface `F = torusOf ψ` is the set of points of `F`
with two `σ`-extremal coordinates, i.e. the points of `F` on the box *edges*; it is exactly the set
that clause (c) of `Work.Drive.Mono.JunctionGenB`/`JunctionGenC` speaks about, and the whole point of
that clause is that its `ℓ`-values be finite (they are then put into the finite `exc`).

The statement at a **fixed** centre `c` is false (`Mono/NOTES_H381_edgeArc_OBSTRUCTION.md` §1, §5):
a `C^∞` diffeo of `ℝ³` can flatten a patch of the standard torus into a planar disc lying in the
corner plane `span (w_k, e_{σ k})` of one of the edge families, and then the edge lines of that
family foliate the patch, so the corner locus contains an arc for a whole interval of levels.  The
dependence on the centre is what saves it: the edge line of the family `(i,j,ε_i,ε_j)` is
`c + s w_k + span (e_{σ k})`, i.e. a one-parameter family of parallel lines sweeping a plane; it is
contained in the surface only if it is one of the (at most one-dimensional family of) rulings of the
surface's ruled pieces, which is one scalar equation in `(c, s) ∈ ℝ⁴` per ruling — a null set.
Hence:

* for almost every centre `c` and almost every level `s`, the corner locus `C(c, s)` is finite;
* the finitely many `ℓ`-values of `C(c, s)` are then insertable into `exc` (they lie in the window
  because `C(c,s) ⊆ ∂PBox ⊆ closure (PBox)`), which makes clause (c) *satisfiable* and hence repairs
  the refuted data producers;
* `HasEssBox` is open in the centre, so the box-shrink consumer may choose the centre in the
  conull set above (this is the lead's "move `c`" remark in `NOTES_LEAD_grazes_L.md`), the level `s`
  being chosen in a conull set anyway.

Sard gives a short proof: for a fixed pair `i ≠ j` the corner locus is contained in the fibre of the
coordinate projection `π_{ij} : F → ℝ²`, `π_{ij} z = (z (σ i), z (σ j))`, over the point
`(c (σ i) ± boxSide i * s, c (σ j) ± boxSide j * s)`; the critical values of `π_{ij}` are null by
Sard, over a regular value the fibre is closed and discrete in the compact `F` hence finite, and the
map `(c, s) ↦ (c (σ i) ± boxSide i * s, c (σ j) ± boxSide j * s)` is a surjective linear map
`ℝ⁴ → ℝ²`, so the preimage of the null set is null.  Fubini and the finite union over pairs and
signs finish. -/
theorem ae_ae_cornerLocus_finite (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ c ∂(MeasureTheory.volume : MeasureTheory.Measure R3),
      ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), 0 < s →
        {z : R3 | z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧
          ∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
            |z (σ j) - c (σ j)| = Submission.boxSide j * s}.Finite := by
  have hstep : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure (R3 × ℝ)),
      ∀ (i j : Fin 3), i ≠ j → ∀ εi εj : Bool,
        cornerLin σ i j (sgn εi) (sgn εj) w ∉ cornerCritVals ψ σ i j := by
    refine MeasureTheory.ae_all_iff.mpr (fun i => ?_)
    refine MeasureTheory.ae_all_iff.mpr (fun j => ?_)
    by_cases hij : i = j
    · subst hij
      exact Filter.Eventually.of_forall (fun w h => absurd rfl h)
    · have hb : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure (R3 × ℝ)),
          ∀ εi εj : Bool, cornerLin σ i j (sgn εi) (sgn εj) w ∉ cornerCritVals ψ σ i j := by
        refine MeasureTheory.ae_all_iff.mpr (fun εi => ?_)
        refine MeasureTheory.ae_all_iff.mpr (fun εj => ?_)
        exact ae_cornerLin_notMem ψ σ hij εi εj
      filter_upwards [hb] with w hw
      intro _ εi εj
      exact hw εi εj
  have hae : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure (R3 × ℝ)),
      0 < w.2 → (cornerLocus ψ σ w.1 w.2).Finite := by
    filter_upwards [hstep] with w hw hs
    exact cornerLocus_finite_of_forall ψ σ w.1 w.2 hs (fun i j hij εi εj => hw i j hij εi εj)
  have h2 := Measure.ae_ae_of_ae_prod (μ := (MeasureTheory.volume : MeasureTheory.Measure R3))
    (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) hae
  filter_upwards [h2] with c hc
  filter_upwards [hc] with s hs
  exact hs

end

end Work.Drive.Mono
