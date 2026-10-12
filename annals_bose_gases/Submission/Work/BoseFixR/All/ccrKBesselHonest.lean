import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseFixR.All.FarKernelRowsB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/ccrKBesselHonest.lean`

The Bessel/Hadamard estimate for FS's box commutator kernel

    `ccrK (s-k) (s'-k) = χ̂²(s-s') − χ̂(s-k)χ̂(s'-k) = ⟪f (s-k), f (s'-k)⟫`

at the honest family `Work.BoseBoxFock.HonestBoxFam`:

    `Σ_{s,s'∈excited} c s c s' ccrK(s-k)(s'-k) ⟪u s,u s'⟫ ≤ 100 Σ_{s∈excited} c s² ⟪u s,u s⟫`

(FS §10, `lem:EstimatesOnQ3-js`: the quadratic form of the box kernel against a *state*
quadratic form `⟪u s, u s'⟫` — the input `hccrB` of `Work.BoseFixR.Q3TWedgeBoundV2`.)

## The argument

The kernel `ccrK` is the Gram matrix `gram (f i) (f j)` of the honest one-particle mode
vectors `f i ∈ ℝ^m` (`Work.BoseB4.boxFockData`), and the honest χ-modes satisfy the
*Parseval (synthesis) bound*

    `Σ_i Σ_j z i z j · ccrK i j ≤ (48/π) Σ_i z i²`   (all `z`),

the lattice form of FS's `‖χ‖_∞²` frame bound: it is `frame_int_bound`
(`Submission.Work.BoseBoxFock.bessel_honest`, with `48/π = χ(0)²` by Parseval on the unit
cell).  This is the statement that the Gram matrix of the modes is positive semidefinite
with operator norm at most `48/π ≤ 16 ≤ 100`.

The remaining step is a Hadamard/Hilbert–Schmidt estimate, proved here for the real
Bombieri Fock space `RealFock m = Work.BoseB4.RealFock m`: expanding the state quadratic
form in the orthonormal monomials `x^α/√(α!)` — which are *finitely* supported, so this is
an algebraic Parseval identity needing no Hilbert-basis machinery,

    `Σ_{i,j} c i c j K i j ⟪u i, u j⟫ = Σ_α Σ_{i,j} (c i √(α!) u i α) K i j (c j √(α!) u j α)`,

the Parseval bound applied to `z i = c i √(α!) (u i α)` bounds each `α` by
`Cn Σ_i (c i)² α! (u i α)²`, and summing over `α` gives the state-form estimate.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The abstract Hadamard/Parseval step

This is the only place where the *state* enters: the kernel `K` is merely a kernel whose
quadratic form is bounded by `Cn`. -/

/-- **The Hadamard/Parseval step.**  If the quadratic form of the kernel `K` is bounded by
`Cn` (a Parseval/frame bound at the level of the label set `ι`), then the same form *paired
with the Bombieri form* of arbitrary states `u i ∈ RealFock m` is bounded by `Cn` times the
diagonal state form.

The proof expands in the monomials `x^α` (each `u i` has finite support!) and applies the
kernel bound to the vector `z i = c i √(α!) (u i α)` for each multi-index `α`. -/
theorem bomb_hadamard {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (K : ι → ι → ℝ) (Cn : ℝ) (hCn : 0 ≤ Cn)
    (hquad : ∀ z : ι → ℝ, ∑ i : ι, ∑ j : ι, z i * z j * K i j ≤ Cn * ∑ i : ι, (z i) ^ 2)
    (c : ι → ℝ) (u : ι → Work.BoseB4.RealFock m) :
    ∑ i : ι, ∑ j : ι, c i * c j * K i j * Work.BoseB4.bomb m (u i) (u j)
      ≤ Cn * ∑ i : ι, (c i) ^ 2 * Work.BoseB4.bomb m (u i) (u i) := by
  classical
  set Kf : Finset (Fin m →₀ ℕ) := Finset.univ.biUnion (fun i : ι => (u i).support) with hKf
  have hmem : ∀ (i : ι) (α : Fin m →₀ ℕ), α ∈ (u i).support → α ∈ Kf := by
    intro i α hα
    rw [hKf]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hα⟩
  -- the Bombieri form as a sum over the common index set `Kf`
  have hbomb : ∀ i j : ι, Work.BoseB4.bomb m (u i) (u j)
      = ∑ α ∈ Kf, Work.BoseB4.mfac α * (u i α) * (u j α) := by
    intro i j
    rw [Work.BoseB4.bomb_apply_union]
    refine Finset.sum_subset ?_ ?_
    · intro α hα
      rcases Finset.mem_union.mp hα with h | h
      · exact hmem i α h
      · exact hmem j α h
    · intro α _ hα
      rw [Finset.mem_union, not_or] at hα
      have h0 : u i α = 0 := by
        by_contra hc
        exact hα.1 (Finsupp.mem_support_iff.mpr hc)
      rw [h0]
      ring
  have hsq : ∀ α : Fin m →₀ ℕ, Real.sqrt (Work.BoseB4.mfac α) * Real.sqrt (Work.BoseB4.mfac α)
      = Work.BoseB4.mfac α := fun α => Real.mul_self_sqrt (Work.BoseB4.bomb_mfac_nonneg α)
  have hsq2 : ∀ α : Fin m →₀ ℕ, (Real.sqrt (Work.BoseB4.mfac α)) ^ 2
      = Work.BoseB4.mfac α := fun α => by rw [sq]; exact hsq α
  calc ∑ i : ι, ∑ j : ι, c i * c j * K i j * Work.BoseB4.bomb m (u i) (u j)
      = ∑ i : ι, ∑ j : ι, ∑ α ∈ Kf,
          c i * c j * K i j * (Work.BoseB4.mfac α * (u i α) * (u j α)) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hbomb i j, Finset.mul_sum]
    _ = ∑ i : ι, ∑ α ∈ Kf, ∑ j : ι,
          c i * c j * K i j * (Work.BoseB4.mfac α * (u i α) * (u j α)) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ α ∈ Kf, ∑ i : ι, ∑ j : ι,
          c i * c j * K i j * (Work.BoseB4.mfac α * (u i α) * (u j α)) :=
        Finset.sum_comm
    _ = ∑ α ∈ Kf, ∑ i : ι, ∑ j : ι,
          c i * c j * K i j * ((Real.sqrt (Work.BoseB4.mfac α)) ^ 2 * (u i α) * (u j α)) := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hsq2 α]
    _ = ∑ α ∈ Kf, ∑ i : ι, ∑ j : ι,
          (c i * (Real.sqrt (Work.BoseB4.mfac α) * u i α))
            * (c j * (Real.sqrt (Work.BoseB4.mfac α) * u j α)) * K i j := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring
    _ ≤ ∑ α ∈ Kf, Cn * ∑ i : ι,
          (c i * (Real.sqrt (Work.BoseB4.mfac α) * u i α)) ^ 2 :=
        Finset.sum_le_sum
          (fun α _ => hquad (fun i => c i * (Real.sqrt (Work.BoseB4.mfac α) * u i α)))
    _ = Cn * ∑ i : ι, (c i) ^ 2 * Work.BoseB4.bomb m (u i) (u i) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.mul_sum]
        congr 1
        rw [hbomb i i, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [mul_pow, mul_pow, hsq2 α]
        ring

/-! ## 2. Reindexing the label cube at the excited modes

The target's sums run over `excited = Lab N \ {0}` with the shift `s ↦ s - k`; the abstract
lemma runs over the whole cube with the shift `i ↦ i + k`.  The two families are related by
the bijection `i ↦ i + k` of the group `Lab N`. -/

/-- **Reindexing the cube at the excited modes.**  If `f` vanishes where `i + k` is the
condensate (`i + k ∉ excited`, i.e. `i = -k`), the sum over the cube is the sum over the
excited modes of the shifted family `s ↦ f (s - k)`. -/
theorem sumShiftExcited {N : ℕ} {M : Type*} [AddCommMonoid M] (k : Lab N) (f : Lab N → M)
    (hf : ∀ i : Lab N, i + k ∉ Work.BoseB7.excited (Lab N) → f i = 0) :
    (∑ i : Lab N, f i) = ∑ s ∈ Work.BoseB7.excited (Lab N), f (s - k) := by
  classical
  set T : Finset (Lab N) := Finset.univ.filter (fun i => i + k ∈ Work.BoseB7.excited (Lab N))
    with hT
  have hTmem : ∀ x : Lab N, x ∈ T ↔ x + k ∈ Work.BoseB7.excited (Lab N) := by
    intro x
    rw [hT, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩
  have h1 : (∑ i : Lab N, f i) = ∑ i ∈ T, f i := by
    refine (Finset.sum_subset (Finset.subset_univ T) ?_).symm
    intro x _ hx
    exact hf x (fun hc => hx ((hTmem x).mpr hc))
  have h2 : T = (Work.BoseB7.excited (Lab N)).image (fun s => s - k) := by
    ext i
    constructor
    · intro hi
      have hi' : i + k ∈ Work.BoseB7.excited (Lab N) := (hTmem i).mp hi
      exact Finset.mem_image.mpr ⟨i + k, hi', by simp⟩
    · intro hi
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hi
      exact (hTmem (s - k)).mpr (by simpa using hs)
  rw [h1, h2, Finset.sum_image]
  intro a _ b _ hab
  have hab' : a - k = b - k := hab
  have h : a - k + k = b - k + k := by rw [hab']
  simpa [sub_add_cancel] using h

/-- The double-sum form of `sumShiftExcited`. -/
theorem sum2ShiftExcited {N : ℕ} {M : Type*} [AddCommMonoid M] (k : Lab N)
    (X : Lab N → Lab N → M)
    (h1 : ∀ i j : Lab N, i + k ∉ Work.BoseB7.excited (Lab N) → X i j = 0)
    (h2 : ∀ i j : Lab N, j + k ∉ Work.BoseB7.excited (Lab N) → X i j = 0) :
    (∑ i : Lab N, ∑ j : Lab N, X i j)
      = ∑ s ∈ Work.BoseB7.excited (Lab N),
          ∑ s' ∈ Work.BoseB7.excited (Lab N), X (s - k) (s' - k) := by
  classical
  calc (∑ i : Lab N, ∑ j : Lab N, X i j)
      = ∑ i : Lab N, ∑ s' ∈ Work.BoseB7.excited (Lab N), X i (s' - k) :=
        Finset.sum_congr rfl (fun i _ => sumShiftExcited k (X i) (fun j hj => h2 i j hj))
    _ = ∑ s ∈ Work.BoseB7.excited (Lab N),
          ∑ s' ∈ Work.BoseB7.excited (Lab N), X (s - k) (s' - k) :=
        sumShiftExcited k (fun i => ∑ s' ∈ Work.BoseB7.excited (Lab N), X i (s' - k))
          (fun i hi => by
            rw [Finset.sum_eq_zero]
            intro s' _
            exact h1 i (s' - k) hi)

/-! ## 3. The honest Parseval bound

`frame_int_bound` (`Submission.Work.BoseBoxFock.bessel_honest`) is the synthesis/Parseval
bound of the honest χ-modes; here it is transported to `F.ccrK`, which *is* the Gram matrix
of those modes (`Work.BoseB4.boxFockData`), in the quadratic-form shape consumed by
`bomb_hadamard`. -/

/-- **The honest Parseval bound** in quadratic-form shape: the commutator kernel of the
honest family has operator norm at most `48/π`. -/
theorem honestCcrQuad {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) :
    ∀ z : Work.BoseBoxFock.Lab (HM μ).N → ℝ,
      ∑ i : Work.BoseBoxFock.Lab (HM μ).N, ∑ j : Work.BoseBoxFock.Lab (HM μ).N,
          z i * z j * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.ccrK i j
        ≤ (48 / Real.pi) * ∑ i : Work.BoseBoxFock.Lab (HM μ).N, (z i) ^ 2 := by
  intro z
  have hpin : ∀ i j : Lab (HM μ).N,
      (HonestBoxFam v h fc fu HM μ).F.ccrK i j
        = Work.BoseK15.corpusBox.hatChiSq
            (Work.BoseB4.vec (labVec (HM μ).N i - labVec (HM μ).N j))
          - Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N i))
            * Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N j)) := by
    intro i j
    have hℓ : (ellH v μ) ≠ 0 := ne_of_gt (ellH_pos v μ)
    rw [show (HonestBoxFam v h fc fu HM μ).F.ccrK i j
        = Work.BoseB7.ccrKernel (ellH v μ) Work.BoseK15.corpusBox.hatChiSq
            Work.BoseK15.corpusBox.hatChi
            (kmomLab (ellH v μ) (HM μ).N i) (kmomLab (ellH v μ) (HM μ).N j) from rfl]
    rw [Work.BoseB7.ccrKernel, smul_kmomLab_sub hℓ (HM μ).N i j,
      smul_kmomLab hℓ (HM μ).N i, smul_kmomLab hℓ (HM μ).N j]
  calc ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
        z i * z j * (HonestBoxFam v h fc fu HM μ).F.ccrK i j
      = ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N, z i * z j *
          (Work.BoseK15.corpusBox.hatChiSq
              (Work.BoseB4.vec (labVec (HM μ).N i - labVec (HM μ).N j))
            - Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N i))
              * Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N j))) :=
        Finset.sum_congr rfl (fun i _ =>
          Finset.sum_congr rfl (fun j _ => by rw [hpin i j]))
    _ ≤ (48 / Real.pi) * ∑ i : Lab (HM μ).N, (z i) ^ 2 :=
        frame_int_bound (HM μ).N z

/-! ## 4. The target -/

theorem ccrKBesselHonest {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {ε₀ μ : ℝ} (hε₀ : ε₀ ≤ 10 ^ (-(4000 : ℤ)))
    (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0) :
    ∀ (k : Work.BoseBoxFock.Lab (HM μ).N) (c : Work.BoseBoxFock.Lab (HM μ).N → ℝ)
      (u : Work.BoseBoxFock.Lab (HM μ).N → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H),
      ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ∑ s' ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
          c s * c s' * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.ccrK (s - k) (s' - k)
            * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp (u s) (u s')
        ≤ 100 * ∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
            c s ^ 2 * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.bp (u s) (u s) := by
  classical
  intro k c u
  have hquad : ∀ z : Lab (HM μ).N → ℝ,
      ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
          z i * z j * (HonestBoxFam v h fc fu HM μ).F.ccrK i j
        ≤ (48 / Real.pi) * ∑ i : Lab (HM μ).N, (z i) ^ 2 :=
    honestCcrQuad h fc fu HM μ
  -- the extended coefficient/state families, indexed by the whole cube
  set c' : Lab (HM μ).N → ℝ :=
    fun i => if i + k ∈ Work.BoseB7.excited (Lab (HM μ).N) then c (i + k) else 0 with hc'
  set u' : Lab (HM μ).N → Work.BoseB4.RealFock (HM μ).m :=
    fun i => if i + k ∈ Work.BoseB7.excited (Lab (HM μ).N) then u (i + k) else 0 with hu'
  have hc'eval : ∀ s ∈ Work.BoseB7.excited (Lab (HM μ).N), c' (s - k) = c s := by
    intro s hs
    rw [hc']
    simp only [sub_add_cancel]
    exact if_pos hs
  have hu'eval : ∀ s ∈ Work.BoseB7.excited (Lab (HM μ).N), u' (s - k) = u s := by
    intro s hs
    rw [hu']
    simp only [sub_add_cancel]
    exact if_pos hs
  have hmain := bomb_hadamard (K := (HonestBoxFam v h fc fu HM μ).F.ccrK)
    (Cn := 48 / Real.pi) (by positivity) hquad c' u'
  have hmain' : (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ∑ s' ∈ Work.BoseB7.excited (Lab (HM μ).N),
          c s * c s' * (HonestBoxFam v h fc fu HM μ).F.ccrK (s - k) (s' - k)
            * Work.BoseB4.bomb (HM μ).m (u s) (u s'))
      ≤ (48 / Real.pi) * ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
          c s ^ 2 * Work.BoseB4.bomb (HM μ).m (u s) (u s) := by
    have hL : (∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
          c' i * c' j * (HonestBoxFam v h fc fu HM μ).F.ccrK i j
            * Work.BoseB4.bomb (HM μ).m (u' i) (u' j))
        = ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
            ∑ s' ∈ Work.BoseB7.excited (Lab (HM μ).N),
              c s * c s' * (HonestBoxFam v h fc fu HM μ).F.ccrK (s - k) (s' - k)
                * Work.BoseB4.bomb (HM μ).m (u s) (u s') := by
      rw [sum2ShiftExcited k (fun i j => c' i * c' j * (HonestBoxFam v h fc fu HM μ).F.ccrK i j
            * Work.BoseB4.bomb (HM μ).m (u' i) (u' j))
          (fun i j hj => by simp only [hc', hj, if_false]; ring)
          (fun i j hj => by simp only [hc', hj, if_false]; ring)]
      exact Finset.sum_congr rfl (fun s hs => Finset.sum_congr rfl (fun s' hs' => by
        rw [hc'eval s hs, hc'eval s' hs', hu'eval s hs, hu'eval s' hs']))
    have hR : (∑ i : Lab (HM μ).N,
          (c' i) ^ 2 * Work.BoseB4.bomb (HM μ).m (u' i) (u' i))
        = ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
            c s ^ 2 * Work.BoseB4.bomb (HM μ).m (u s) (u s) := by
      rw [sumShiftExcited k (fun i => (c' i) ^ 2 * Work.BoseB4.bomb (HM μ).m (u' i) (u' i))
          (fun i hj => by simp only [hc', hj, if_false]; ring)]
      exact Finset.sum_congr rfl (fun s hs => by rw [hc'eval s hs, hu'eval s hs])
    calc (∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
          ∑ s' ∈ Work.BoseB7.excited (Lab (HM μ).N),
            c s * c s' * (HonestBoxFam v h fc fu HM μ).F.ccrK (s - k) (s' - k)
              * Work.BoseB4.bomb (HM μ).m (u s) (u s'))
        = ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
            c' i * c' j * (HonestBoxFam v h fc fu HM μ).F.ccrK i j
              * Work.BoseB4.bomb (HM μ).m (u' i) (u' j) := hL.symm
      _ ≤ (48 / Real.pi) * ∑ i : Lab (HM μ).N,
            (c' i) ^ 2 * Work.BoseB4.bomb (HM μ).m (u' i) (u' i) := hmain
      _ = (48 / Real.pi) * ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
            c s ^ 2 * Work.BoseB4.bomb (HM μ).m (u s) (u s) :=
          congrArg (fun x => (48 / Real.pi) * x) hR
  have hnn : 0 ≤ ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
      c s ^ 2 * (HonestBoxFam v h fc fu HM μ).F.bp (u s) (u s) :=
    Finset.sum_nonneg
      (fun s _ => mul_nonneg (sq_nonneg _) ((HonestBoxFam v h fc fu HM μ).F.bp_nonneg (u s)))
  have hconst : (48 : ℝ) / Real.pi ≤ 100 := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  calc ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ∑ s' ∈ Work.BoseB7.excited (Lab (HM μ).N),
          c s * c s' * (HonestBoxFam v h fc fu HM μ).F.ccrK (s - k) (s' - k)
            * (HonestBoxFam v h fc fu HM μ).F.bp (u s) (u s')
      ≤ (48 / Real.pi) * ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
          c s ^ 2 * (HonestBoxFam v h fc fu HM μ).F.bp (u s) (u s) := hmain'
    _ ≤ 100 * ∑ s ∈ Work.BoseB7.excited (Lab (HM μ).N),
          c s ^ 2 * (HonestBoxFam v h fc fu HM μ).F.bp (u s) (u s) :=
        mul_le_mul_of_nonneg_right hconst hnn

end Work.BoseFixR.All
