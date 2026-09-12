import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Body
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Real

noncomputable section

open scoped Real BigOperators ENNReal Pointwise
open MeasureTheory MeasureTheory.Measure Set

/-!
# The coordinate successive-minima engine (Minkowski's second theorem, upper bound)

Self-contained module. Proves:

`Submission.MinkEngine.mink_engine (d : ℕ) (B : Set (Fin d → ℝ)) (a : Fin d → ℝ) ... : 
   (∏ i : Fin d, a i) * (volume : Measure (Fin d → ℝ)).real B ≤ 2 ^ d`

under the hypotheses:
* `B` is an open, convex, symmetric body in `E = Fin d → ℝ` with `0 ∈ B`, bounded.
* scales `a i > 0` are nondecreasing (in the index order of `Fin d`).
* the *flag property* `hP`: for each `i : Fin d` and each integer function `z`,
  if `z ∈ (a i) • B` (i.e. `z` is in the `a i`-dilate of `B`) then `z j = 0` for all
  `j : Fin d` with `i.val ≤ j.val`.

Conclusion: `(∏ i, a i) * vol(B) ≤ 2^d`.

## How the engine is used (do not change the statement)

In `Submission.MinkUpper` the theorem is applied with `B` the interior of the weighted
Vandermonde body `{x | ∀ k, |Σ_j x j · (α k)^j · v k| < 1}` (after a unimodular change of
coordinates that makes the greedy flag equal to the coordinate flag). The `a i` are the greedy
successive scales and `hP` is the minimality property of the greedy construction.

## Mathematical content of the proof (Bambah–Woods / Cassels, "folded volume" route)

For `n : ℕ`, let `Ltype d n` be the type of integer functions that vanish at indices `≥ n`,
and let `slab d n` be `{x | ∀ j, j.val < n → x j ∈ Ico 0 1}`.  Define the *folded volume*
`Dμ d n C := μ ((⋃ z : Ltype d n, (z + C)) ∩ slab d n)`.

The engine is the chain (for fold levels `f = 1..d`):

  Dμ f (½·a_{f-1}·B) ≥ (a_{f-1}/a_{f-2})^(d-f+1) · Dμ (f-1) (½·a_{f-2}·B)   (f ≥ 2)
  Dμ f (½·a_{f-1}·B) = Dμ (f-1) (½·a_{f-1}·B)                                 (no-difference,
                                                                                from hP and B open)
  Dμ 1 (½·a_0·B) = μ (½·a_0·B) = (a_0/2)^d · μ B
  Dμ d (½·a_{d-1}·B) ≤ 1    (folded into the unit cube)

Telescoping gives (∏ a_i)/2^d · μ B ≤ 1.

The tools you will need:
1. `μ (r • C) = ENNReal.ofReal (r ^ d) * μ C` for `0 ≤ r` (addHaar_smul_of_nonneg, finrank of
   `Fin d → ℝ` is `d`), and translation invariance of `volume`.
2. Measurability of `slab d n`; `slab d d` has volume 1.
3. For `C` bounded measurable the union `⋃ z, z + C` is a countable disjoint union when no two
   points of `C` differ by a nonzero element of `Ltype d n`; use `measure_iUnion` / countable
   additivity. `Ltype d n` is countable.
4. Folding an extra coordinate (level n+1 vs n) does not change the measure when no two points
   of `C` differ by an element of `Ltype d (n+1)` outside `Ltype d n`; these elements have a
   nonzero value at index `n`.
5. Scaling lemma: for `s ≥ 1` and convex `C`, `Dμ d n (s • C) ≥ ofReal (s ^ (d-n)) * Dμ d n C`
   — proven by slicing along the coordinate directions: split `E d ≃ (Fin n → ℝ) × (Fin (d-n) → ℝ)`
   and use that for a convex slice `S` (a set in `(Fin n → ℝ)`), the reduced volume
   `ν(S) = μ_S ((S + ℤ^n) ∩ cube)` satisfies `ν(S) ≤ ν(s • S)` because `S ⊆ (1-s)u + s•S` for any
   `u ∈ S` (convexity: `(1/s)y + (1 - 1/s)u ∈ S`), and reduction modulo `ℤ^n` is translation
   invariant.  Use Fubini (product measure on functions) over the tail coordinates.

You may reorganize the definitions below (they live in namespace `Submission.MinkEngine`)
but must keep the name, type and statement of `mink_engine` EXACTLY as given, since
`Submission.MinkUpper` and its consumers import this theorem.
-/

namespace Submission.MinkEngine

/-- coefficient space -/
abbrev E (d : ℕ) := Fin d → ℝ

/-- x : ℝ is an integer -/
def IntV (x : ℝ) : Prop := ∃ n : ℤ, (n : ℝ) = x

/-- integer-valued function -/
def IntFun (d : ℕ) (x : E d) : Prop := ∀ j : Fin d, IntV (x j)

/-- integer function vanishing at indices ≥ n -/
def Lzero (d n : ℕ) (x : E d) : Prop :=
  IntFun d x ∧ ∀ j : Fin d, n ≤ j.val → x j = 0

/-- type of such lattice points -/
abbrev Ltype (d n : ℕ) := {x : E d // Lzero d n x}

/-- slab [0,1)^n × ℝ^{d-n} -/
def Fslab (d n : ℕ) : Set (E d) := {x | ∀ j : Fin d, j.val < n → x j ∈ Set.Ico 0 1}

/-- translate of a set by a lattice point -/
def latShift (d : ℕ) (z : E d) (C : Set (E d)) : Set (E d) :=
  (fun w : E d => w + z) '' C

/-- all lattice translates of C -/
def latOrbit (d n : ℕ) (C : Set (E d)) : Set (E d) :=
  ⋃ z : Ltype d n, latShift d (z : E d) C

/-- folded volume at fold level n -/
def Dμ (d n : ℕ) (C : Set (E d)) : ℝ≥0∞ :=
  MeasureTheory.volume (latOrbit d n C ∩ Fslab d n)


/-- The coordinate successive-minima engine. -/

-- =====================================================================
--  Basic facts about the lattice Ltype, the slab, and the volume measure
-- =====================================================================

lemma IntV_zero : IntV 0 := ⟨0, by simp⟩

lemma IntV_neg {x : ℝ} : IntV x → IntV (-x) := by
  rintro ⟨a, rfl⟩; exact ⟨-a, by simp⟩

lemma IntV_add {x y : ℝ} : IntV x → IntV y → IntV (x + y) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by simp⟩

lemma IntFun_zero (d : ℕ) : IntFun d 0 := by
  intro j; exact IntV_zero

lemma IntFun_neg {d : ℕ} {x : E d} : IntFun d x → IntFun d (-x) := by
  intro hx j; exact IntV_neg (hx j)

lemma IntFun_add {d : ℕ} {x y : E d} : IntFun d x → IntFun d y → IntFun d (x + y) := by
  intro hx hy j; exact IntV_add (hx j) (hy j)

lemma IntFun_sub {d : ℕ} {x y : E d} : IntFun d x → IntFun d y → IntFun d (x - y) := by
  intro hx hy j
  rw [sub_eq_add_neg]
  exact IntV_add (hx j) (IntV_neg (hy j))

lemma Lzero_zero (d n : ℕ) : Lzero d n 0 := by
  refine ⟨?_, ?_⟩
  · intro j; exact IntV_zero
  · intro j hj; rfl

lemma Lzero_neg {d n : ℕ} {x : E d} (hx : Lzero d n x) : Lzero d n (-x) := by
  refine ⟨?_, ?_⟩
  · intro j; exact IntV_neg (hx.1 j)
  · intro j hj; simp [hx.2 j hj]

lemma Lzero_add {d n : ℕ} {x y : E d} (hx : Lzero d n x) (hy : Lzero d n y) : Lzero d n (x + y) := by
  refine ⟨?_, ?_⟩
  · intro j; exact IntV_add (hx.1 j) (hy.1 j)
  · intro j hj; simp [hx.2 j hj, hy.2 j hj]

lemma Lzero_sub {d n : ℕ} {x y : E d} (hx : Lzero d n x) (hy : Lzero d n y) : Lzero d n (x - y) := by
  rw [sub_eq_add_neg]; exact Lzero_add hx (Lzero_neg hy)

instance instCountableLtype (d n : ℕ) : Countable (Ltype d n) := by
  refine Function.Injective.countable (f := fun x : Ltype d n => fun j : Fin d =>
    (Classical.choose (x.2.1 j) : ℤ)) ?_
  intro x y h
  apply Subtype.ext
  ext j
  have h1 := congr_fun h j
  have hx := Classical.choose_spec (x.2.1 j)
  have hy := Classical.choose_spec (y.2.1 j)
  rw [← hx, ← hy]
  exact_mod_cast h1

lemma Fslab_measurable (d n : ℕ) : MeasurableSet (Fslab d n) := by
  classical
  have hEq : Fslab d n =
      Set.pi Set.univ (fun j : Fin d => if j.val < n then Set.Ico (0 : ℝ) 1 else Set.univ) := by
    ext x
    simp [Fslab, Set.pi]
  rw [hEq]
  exact MeasurableSet.pi Set.countable_univ
    (by intro j _; by_cases h : j.val < n <;> simp [h])

lemma Fslab_d_zero (d : ℕ) : Fslab d 0 = Set.univ := by
  ext x; simp [Fslab]

lemma latShift_measurable {d : ℕ} (z : E d) {C : Set (E d)} (hC : MeasurableSet C) :
    MeasurableSet (latShift d z C) := by
  have hme : MeasurableEmbedding (fun w : E d => w + z) := by
    have hh : (Homeomorph.addRight z : E d ≃ₜ E d).toFun = (fun w : E d => w + z) := rfl
    exact (Homeomorph.measurableEmbedding (Homeomorph.addRight z))
  exact (hme.measurableSet_image).2 hC

/-- translates of a measurable set by a lattice point are measurable -/
lemma latOrbit_measurable {d n : ℕ} {C : Set (E d)} (hC : MeasurableSet C) :
    MeasurableSet (latOrbit d n C) := by
  rw [latOrbit]
  exact MeasurableSet.iUnion (fun z : Ltype d n => latShift_measurable (z : E d) hC)

/-- volume is invariant under the translation w ↦ w + z (on measurable sets) -/
lemma vol_translate {d : ℕ} (z : E d) {C : Set (E d)} (hC : MeasurableSet C) :
    (volume : Measure (E d)) (latShift d z C) = (volume : Measure (E d)) C := by
  unfold latShift
  have hMP : MeasurePreserving (fun w : E d => w + z) (volume : Measure (E d))
      (volume : Measure (E d)) := by
    simpa [add_comm] using (measurePreserving_add_left (volume : Measure (E d)) z)
  have him : (fun w : E d => w + z) '' C = (fun w : E d => w - z) ⁻¹' C := by
    ext w; constructor
    · rintro ⟨c, hc, rfl⟩; simp [hc]
    · intro hw
      refine ⟨w - z, ?_, by simp⟩
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hw
  rw [him]
  have hMP' : MeasurePreserving (fun w : E d => w - z) (volume : Measure (E d))
      (volume : Measure (E d)) := by
    simpa [sub_eq_add_neg, add_comm] using (measurePreserving_add_left (volume : Measure (E d)) (-z))
  exact hMP'.measure_preimage hC.nullMeasurableSet

/-- Haar scaling of volume on E d -/
lemma vol_smul_haar (d : ℕ) {C : Set (E d)} (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure (E d)) (r • C) = ENNReal.ofReal (r ^ d) * (volume : Measure (E d)) C := by
  have hf : Module.finrank ℝ (E d) = d := by
    simp [E]
  rw [Measure.addHaar_smul_of_nonneg (volume : Measure (E d)) hr C, hf]

/-- a translate of an open set is open -/
lemma smul_isOpen {d : ℕ} {C : Set (E d)} (r : ℝ) (hr : r ≠ 0) (hC : IsOpen C) :
    IsOpen (r • C) := by
  have heq : r • C = (fun y : E d => r⁻¹ • y) ⁻¹' C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [inv_smul_smul₀ hr]
    · intro hy
      refine ⟨r⁻¹ • y, hy, ?_⟩
      simp [smul_inv_smul₀ hr]
  rw [heq]
  exact hC.preimage (continuous_const_smul (r⁻¹))

/-- rescaling by a non-zero scalar preserves measurability -/
lemma smul_measurable {d : ℕ} {C : Set (E d)} (r : ℝ) (hr : r ≠ 0) (hC : MeasurableSet C) :
    MeasurableSet (r • C) := by
  have heq : r • C = (fun y : E d => r⁻¹ • y) ⁻¹' C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [inv_smul_smul₀ hr]
    · intro hy
      refine ⟨r⁻¹ • y, hy, ?_⟩
      simp [smul_inv_smul₀ hr]
  rw [heq]
  exact hC.preimage (measurable_const_smul (r⁻¹))

/-- the unit cube has volume one -/
lemma volume_Fslab_full (d : ℕ) : (volume : Measure (E d)) (Fslab d d) = 1 := by
  classical
  have hEq : Fslab d d = Set.pi Set.univ (fun j : Fin d => Set.Ico (0 : ℝ) 1) := by
    ext x
    simp [Fslab, Set.pi]
  rw [hEq]
  rw [MeasureTheory.volume_pi_pi]
  simp [Real.volume_Ico]

/-- Dμ at fold level 0 is just the volume -/
lemma Dμ_level_zero (d : ℕ) {C : Set (E d)} (hC : MeasurableSet C) :
    Dμ d 0 C = (volume : Measure (E d)) C := by
  have hOrbit : latOrbit d 0 C = C := by
    ext x
    simp only [latOrbit, latShift, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨z, w, hw, hzw⟩
      have hz0 : (z : E d) = 0 := by
        ext j
        exact z.2.2 j (by omega)
      have hxw : x = w := by
        calc x = w + (z : E d) := hzw.symm
             _ = w + 0 := by rw [hz0]
             _ = w := by simp
      simpa [hxw] using hw
    · intro hx
      refine ⟨(⟨0, Lzero_zero d 0⟩ : Ltype d 0), x, hx, ?_⟩
      simp
  rw [Dμ, hOrbit, Fslab_d_zero]
  simpa using hC





-- =====================================================================
--  Folding one more coordinate (level n → n+1)
-- =====================================================================

/-- the index n : ℕ viewed inside Fin d -/
def finN (d : ℕ) {n : ℕ} (hn : n < d) : Fin d := ⟨n, hn⟩

/-- the standard basis vector e_n of E d -/
def unitVec (d : ℕ) {n : ℕ} (hn : n < d) : E d := fun j => if j = finN d hn then 1 else 0

lemma finN_eq_iff {d n : ℕ} (hn : n < d) (j : Fin d) : j = finN d hn ↔ j.val = n := by
  constructor
  · intro h; simp [finN, h]
  · intro h; ext; exact h

lemma finN_val {d n : ℕ} (hn : n < d) : (finN d hn).val = n := rfl

lemma unitVec_at {d n : ℕ} (hn : n < d) (m : ℤ) :
    ((m : ℝ) • unitVec d hn) (finN d hn) = (m : ℝ) := by
  simp [unitVec, finN_eq_iff hn]

lemma unitVec_away {d n : ℕ} (hn : n < d) (m : ℤ) (j : Fin d) (hj : j ≠ finN d hn) :
    ((m : ℝ) • unitVec d hn) j = 0 := by
  simp [unitVec, hj]

lemma IntFun_unitVec {d n : ℕ} (hn : n < d) (m : ℤ) :
    IntFun d ((m : ℝ) • unitVec d hn) := by
  intro j
  by_cases hj : j = finN d hn
  · subst j; rw [unitVec_at hn m]; exact ⟨m, by norm_num⟩
  · rw [unitVec_away hn m j hj]; exact IntV_zero

lemma Lzero_unitVec {d n : ℕ} (hn : n < d) (m : ℤ) :
    Lzero d (n+1) ((m : ℝ) • unitVec d hn) := by
  constructor
  · exact IntFun_unitVec hn m
  · intro j hj
    by_cases hjn : j = finN d hn
    · subst j
      have : n + 1 ≤ n := by simpa [finN] using hj
      omega
    · exact unitVec_away hn m j hjn

/-- a lattice point at level n+1 decomposes as z + m·e_n with z at level n -/
lemma Lzero_decompose {d n : ℕ} (hn : n < d) {w : E d} (hw : Lzero d (n+1) w) :
    ∃ (z : E d) (m : ℤ), Lzero d n z ∧ w = z + (m : ℝ) • unitVec d hn := by
  classical
  let m : ℤ := Classical.choose (hw.1 (finN d hn))
  have hm : (m : ℝ) = w (finN d hn) := Classical.choose_spec (hw.1 (finN d hn))
  refine ⟨w - (m : ℝ) • unitVec d hn, m, ?_, ?_⟩
  · constructor
    · intro j
      exact (IntFun_sub hw.1 (IntFun_unitVec hn m)) j
    · intro j hj
      by_cases hjn : j = finN d hn
      · subst j
        change w (finN d hn) - ((m : ℝ) • unitVec d hn) (finN d hn) = 0
        rw [unitVec_at hn, hm]
        norm_num
      · have hjnv : j.val ≠ n := by
          intro hval
          apply hjn
          ext
          exact hval
        have : (w - (m : ℝ) • unitVec d hn) j = w j := by
          have hv : ((m : ℝ) • unitVec d hn) j = 0 := unitVec_away hn m j hjn
          simp [hv, sub_eq_add_neg]
        rw [this, hw.2 j (by omega)]
  · ext j
    by_cases hjn : j = finN d hn
    · subst j
      change w (finN d hn) = (w - (m : ℝ) • unitVec d hn + (m : ℝ) • unitVec d hn) (finN d hn)
      simp [unitVec_at hn, hm, sub_eq_add_neg]
    · have hv : ((m : ℝ) • unitVec d hn) j = 0 := unitVec_away hn m j hjn
      simp [hv, hjn]

lemma Lzero_mono {d n m : ℕ} (h : n ≤ m) {x : E d} (hx : Lzero d n x) : Lzero d m x := by
  refine ⟨hx.1, ?_⟩
  intro j hj
  exact hx.2 j (by omega)

/-- membership in a translate -/
lemma mem_latShift {d : ℕ} (z : E d) {C : Set (E d)} {x : E d} :
    x ∈ latShift d z C ↔ ∃ w : E d, w ∈ C ∧ w + z = x := by
  unfold latShift
  rw [Set.mem_image]

/-- membership in the orbit: x ∈ ⋃ z, (C + z)  iff  x − z ∈ C for some lattice point z -/
lemma mem_latOrbit {d n : ℕ} {C : Set (E d)} {x : E d} :
    x ∈ latOrbit d n C ↔ ∃ (z : E d), Lzero d n z ∧ x - z ∈ C := by
  rw [latOrbit, Set.mem_iUnion]
  constructor
  · intro hx
    rcases hx with ⟨z, hz⟩
    rcases (mem_latShift (z : E d) (x := x)).mp hz with ⟨w, hw, hzw⟩
    refine ⟨(z : E d), z.2, ?_⟩
    have : x - (z : E d) = w := by
      calc x - (z : E d) = (w + (z : E d)) - (z : E d) := by rw [hzw]
           _ = w := by abel
    simpa [this]
  · rintro ⟨z, hz, hxz⟩
    refine ⟨(⟨z, hz⟩ : Ltype d n), ?_⟩
    exact (mem_latShift (z : E d) (x := x)).mpr ⟨x - z, hxz, by abel⟩

/-- fold of the level-n orbit gives exactly the level-(n+1) orbit, inside the smaller slab -/
lemma latOrbit_succ {d n : ℕ} (hn : n < d) (C : Set (E d)) :
    (latOrbit d (n+1) C) ∩ Fslab d (n+1) =
      ⋃ m : ℤ, ((fun w : E d => w + (m : ℝ) • unitVec d hn) '' (latOrbit d n C ∩ Fslab d n))
        ∩ Fslab d (n+1) := by
  classical
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx1, hx2⟩
    rw [mem_latOrbit] at hx1
    rcases hx1 with ⟨w, hw, hxw⟩
    rcases Lzero_decompose hn hw with ⟨z, m, hz, hwm⟩
    rw [Set.mem_iUnion]
    refine ⟨m, ?_⟩
    refine ⟨⟨x - (m : ℝ) • unitVec d hn, ⟨?_, ?_⟩, ?_⟩, hx2⟩
    · rw [mem_latOrbit]
      refine ⟨z, hz, ?_⟩
      have : x - (m : ℝ) • unitVec d hn - z = x - (z + (m : ℝ) • unitVec d hn) := by abel
      rw [this, ← hwm]
      exact hxw
    · intro j hj
      have hj' : j ≠ finN d hn := by
        intro hjeq
        have : (finN d hn).val = n := by simp [finN]
        omega
      have hv : ((m : ℝ) • unitVec d hn) j = 0 := unitVec_away hn m j hj'
      have : (x - (m : ℝ) • unitVec d hn) j = x j := by
        simp [hv, sub_eq_add_neg]
      rw [this]
      exact hx2 j (by omega)
    · abel
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨m, hA⟩
    rcases hA with ⟨himg, hx2⟩
    rcases himg with ⟨y, hyX, hym⟩
    refine ⟨?_, hx2⟩
    rw [mem_latOrbit]
    rcases (mem_latOrbit.mp hyX.1) with ⟨w, hw, hyw⟩
    refine ⟨w + (m : ℝ) • unitVec d hn,
      Lzero_add (Lzero_mono (by omega) hw) (Lzero_unitVec hn m), ?_⟩
    have hxeq : x = y + (m : ℝ) • unitVec d hn := by simpa using hym.symm
    have hstep : x - (w + (m : ℝ) • unitVec d hn) = y - w := by
      rw [hxeq]
      abel
    simpa [hstep]


/-- C has no two points differing by a lattice vector at level n+1 that is not at level n -/
def FoldFree (d n : ℕ) (C : Set (E d)) : Prop :=
  ∀ ⦃x y : E d⦄, x ∈ C → y ∈ C → Lzero d (n+1) (x - y) → ¬ Lzero d n (x - y) → x = y

/-- Y has no two points differing by a nonzero multiple of e_n -/
def eFree (d n : ℕ) (hn : n < d) (Y : Set (E d)) : Prop :=
  ∀ m : ℤ, m ≠ 0 → Disjoint Y ((fun w : E d => w + (m : ℝ) • unitVec d hn) ⁻¹' Y)

/-- translated slab-strip: points whose translate by m·e_n lands in the (n+1)-slab -/
def slabStrip (d n : ℕ) (hn : n < d) (m : ℤ) : Set (E d) :=
  (fun w : E d => w + (m : ℝ) • unitVec d hn) ⁻¹' Fslab d (n+1)

lemma exists_z_fract (t : ℝ) : ∃ m : ℤ, (m : ℝ) + t ∈ Set.Ico (0 : ℝ) 1 := by
  refine ⟨-Int.floor t, ?_⟩
  have h1 : (Int.floor t : ℝ) ≤ t := Int.floor_le t
  have h2 : t < (Int.floor t : ℝ) + 1 := Int.lt_floor_add_one t
  have hcast : ((-(Int.floor t) : ℤ) : ℝ) = - (Int.floor t : ℝ) := by simp
  rw [hcast]
  constructor <;> linarith

lemma mem_Fslab_add_unit {d n : ℕ} (hn : n < d) (m : ℤ) (x : E d) :
    x + (m : ℝ) • unitVec d hn ∈ Fslab d (n+1) ↔
      (x ∈ Fslab d n ∧ (m : ℝ) + x (finN d hn) ∈ Set.Ico (0 : ℝ) 1) := by
  constructor
  · intro hx
    constructor
    · intro j hj
      have hj' : j ≠ finN d hn := by
        intro hjeq
        have : (finN d hn).val = n := by simp [finN]
        omega
      have hv : ((m : ℝ) • unitVec d hn) j = 0 := unitVec_away hn m j hj'
      have hxj : (x + (m : ℝ) • unitVec d hn) j ∈ Set.Ico (0 : ℝ) 1 := hx j (by omega)
      simpa [hv] using hxj
    · have hx0 : (x + (m : ℝ) • unitVec d hn) (finN d hn) ∈ Set.Ico (0 : ℝ) 1 :=
        hx (finN d hn) (by simp [finN])
      simpa [unitVec_at hn, add_comm] using hx0
  · intro hx
    intro j hj
    by_cases hjn : j = finN d hn
    · subst j
      have hx0 : (m : ℝ) + x (finN d hn) ∈ Set.Ico (0 : ℝ) 1 := hx.2
      simpa [unitVec_at hn, add_comm] using hx0
    · have hv : ((m : ℝ) • unitVec d hn) j = 0 := unitVec_away hn m j hjn
      have hxj : x j ∈ Set.Ico (0 : ℝ) 1 := hx.1 j (by
        have : j.val ≠ n := by
          intro hc
          apply hjn
          ext; exact hc
        omega)
      simpa [hv] using hxj

lemma slabStrip_tiles {d n : ℕ} (hn : n < d) :
    (⋃ m : ℤ, slabStrip d n hn m) = Fslab d n := by
  ext x
  rw [Set.mem_iUnion]
  constructor
  · intro hx
    rcases hx with ⟨m, hm⟩
    exact (mem_Fslab_add_unit hn m x).mp hm |>.1
  · intro hx
    rcases exists_z_fract (x (finN d hn)) with ⟨m, hmfrac⟩
    exact ⟨m, (mem_Fslab_add_unit hn m x).mpr ⟨hx, by simpa [add_comm] using hmfrac⟩⟩

lemma slabStrip_disjoint {d n : ℕ} (hn : n < d) :
    Pairwise (Function.onFun Disjoint (fun m : ℤ => slabStrip d n hn m)) := by
  intro m1 m2 hm
  rw [Function.onFun]
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hc1 : (m1 : ℝ) + x (finN d hn) ∈ Set.Ico (0 : ℝ) 1 :=
    (mem_Fslab_add_unit hn m1 x).mp hx1 |>.2
  have hc2 : (m2 : ℝ) + x (finN d hn) ∈ Set.Ico (0 : ℝ) 1 :=
    (mem_Fslab_add_unit hn m2 x).mp hx2 |>.2
  rcases lt_or_gt_of_ne hm with hlt | hgt
  · -- m1 < m2
    have hm12 : (m1 : ℝ) + 1 ≤ (m2 : ℝ) := by
      have hz : m1 + 1 ≤ m2 := by omega
      exact_mod_cast hz
    have hnonneg : 0 ≤ (m1 : ℝ) + x (finN d hn) := hc1.1
    have hlt1 : (m2 : ℝ) + x (finN d hn) < 1 := hc2.2
    linarith
  · -- m2 < m1
    have hm21 : (m2 : ℝ) + 1 ≤ (m1 : ℝ) := by
      have hz : m2 + 1 ≤ m1 := by omega
      exact_mod_cast hz
    have hnonneg : 0 ≤ (m2 : ℝ) + x (finN d hn) := hc2.1
    have hlt1 : (m1 : ℝ) + x (finN d hn) < 1 := hc1.2
    linarith



/-- translation by m·e_n is measurable -/
lemma measurable_add_unit {d n : ℕ} (hn : n < d) (m : ℤ) :
    Measurable (fun w : E d => w + (m : ℝ) • unitVec d hn) := by
  exact (Homeomorph.addRight ((m : ℝ) • unitVec d hn)).measurable

lemma measurable_slabStrip {d n : ℕ} (hn : n < d) (m : ℤ) :
    MeasurableSet (slabStrip d n hn m) := by
  unfold slabStrip
  exact (Fslab_measurable d (n+1)).preimage (measurable_add_unit hn m)

/-- folding the n-th coordinate preserves the measure of a set with no two points
    differing by a nonzero multiple of e_n -/
lemma fold_measure {d n : ℕ} (hn : n < d) {Y : Set (E d)}
    (hY : MeasurableSet Y) (hsub : Y ⊆ Fslab d n) (hfree : eFree d n hn Y) :
    (volume : Measure (E d)) (⋃ m : ℤ,
      ((fun w : E d => w + (m : ℝ) • unitVec d hn) '' Y) ∩ Fslab d (n+1)) =
    (volume : Measure (E d)) Y := by
  classical
  have hpiece_disj :
      Pairwise (Function.onFun Disjoint (fun m : ℤ =>
        ((fun w : E d => w + (m : ℝ) • unitVec d hn) '' Y) ∩ Fslab d (n+1))) := by
    intro m1 m2 hm
    rw [Function.onFun]
    rw [Set.disjoint_left]
    intro x hx1 hx2
    rcases hx1 with ⟨hx1a, hxF1⟩
    rcases hx2 with ⟨hx2a, hxF2⟩
    rcases hx1a with ⟨y1, hy1, hym1⟩
    rcases hx2a with ⟨y2, hy2, hym2⟩
    -- x = y1 + m1·e = y2 + m2·e  ⇒  y1 + (m1-m2)·e = y2
    have hyeq : y1 + ((m1 - m2 : ℤ) : ℝ) • unitVec d hn = y2 := by
      have hy1x : y1 + (m1 : ℝ) • unitVec d hn = x := by simpa using hym1
      have hy2x : y2 + (m2 : ℝ) • unitVec d hn = x := by simpa using hym2
      have hxy : y1 + (m1 : ℝ) • unitVec d hn = y2 + (m2 : ℝ) • unitVec d hn := by
        rw [hy1x, hy2x]
      have hsub2 : ((m1 : ℝ) - (m2 : ℝ)) • unitVec d hn =
          (m1 : ℝ) • unitVec d hn - (m2 : ℝ) • unitVec d hn := by
        rw [sub_smul]
      have hcast : ((m1 - m2 : ℤ) : ℝ) = (m1 : ℝ) - (m2 : ℝ) := by norm_num
      calc y1 + ((m1 - m2 : ℤ) : ℝ) • unitVec d hn
          = y1 + ((m1 : ℝ) - (m2 : ℝ)) • unitVec d hn := by rw [hcast]
      _ = y1 + ((m1 : ℝ) • unitVec d hn - (m2 : ℝ) • unitVec d hn) := by rw [hsub2]
      _ = (y1 + (m1 : ℝ) • unitVec d hn) - (m2 : ℝ) • unitVec d hn := by abel
      _ = (y2 + (m2 : ℝ) • unitVec d hn) - (m2 : ℝ) • unitVec d hn := by rw [hxy]
      _ = y2 := by abel
    have hk : (m1 - m2 : ℤ) ≠ 0 := sub_ne_zero.mpr hm
    -- y1 ∈ Y and y2 = y1 + k·e ∈ Y contradict hfree
    have hd := Set.disjoint_left.mp (hfree (m1 - m2) hk) hy1
    have hmem : y1 + ((m1 - m2 : ℤ) : ℝ) • unitVec d hn ∈ Y := by
      rw [hyeq]
      exact hy2
    exact hd hmem
  have hfmeas : ∀ m : ℤ,
      MeasurableSet (((fun w : E d => w + (m : ℝ) • unitVec d hn) '' Y) ∩ Fslab d (n+1)) := by
    intro m
    exact (latShift_measurable ((m : ℝ) • unitVec d hn) hY).inter (Fslab_measurable d (n+1))
  calc
    (volume : Measure (E d)) (⋃ m : ℤ,
      ((fun w : E d => w + (m : ℝ) • unitVec d hn) '' Y) ∩ Fslab d (n+1))
        = ∑' m : ℤ,
          (volume : Measure (E d)) (((fun w : E d => w + (m : ℝ) • unitVec d hn) '' Y) ∩ Fslab d (n+1)) :=
          measure_iUnion hpiece_disj hfmeas
    _ = ∑' m : ℤ, (volume : Measure (E d)) (Y ∩ slabStrip d n hn m) := by
      refine tsum_congr ?_
      intro m
      have hset : ((fun w : E d => w + (m : ℝ) • unitVec d hn) '' Y) ∩ Fslab d (n+1) =
          latShift d ((m : ℝ) • unitVec d hn) (Y ∩ slabStrip d n hn m) := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨hx1, hx2⟩
          rcases hx1 with ⟨y, hy, hym⟩
          refine ⟨y, ⟨hy, ?_⟩, hym⟩
          unfold slabStrip
          -- y + m·e = x ∈ Fslab(n+1)
          simpa [hym] using hx2
        · intro hx
          rcases hx with ⟨y, hy, hym⟩
          constructor
          · refine ⟨y, hy.1, hym⟩
          · unfold slabStrip at hy
            simpa [hym] using hy.2
      rw [hset]
      exact vol_translate ((m : ℝ) • unitVec d hn) (hY.inter (measurable_slabStrip hn m))
    _ = (volume : Measure (E d)) (⋃ m : ℤ, Y ∩ slabStrip d n hn m) := by
      rw [measure_iUnion]
      · intro m1 m2 hm
        rw [Function.onFun]
        rw [Set.disjoint_left]
        intro x hx1 hx2
        rcases hx1 with ⟨hy1, hs1⟩
        rcases hx2 with ⟨hy2, hs2⟩
        have hs1' : x + (m1 : ℝ) • unitVec d hn ∈ Fslab d (n+1) := by simpa [slabStrip] using hs1
        have hs2' : x + (m2 : ℝ) • unitVec d hn ∈ Fslab d (n+1) := by simpa [slabStrip] using hs2
        have hc1 : (m1 : ℝ) + x (finN d hn) ∈ Set.Ico (0 : ℝ) 1 :=
          (mem_Fslab_add_unit hn m1 x).mp hs1' |>.2
        have hc2 : (m2 : ℝ) + x (finN d hn) ∈ Set.Ico (0 : ℝ) 1 :=
          (mem_Fslab_add_unit hn m2 x).mp hs2' |>.2
        rcases lt_or_gt_of_ne hm with hlt | hgt
        · have hm12 : (m1 : ℝ) + 1 ≤ (m2 : ℝ) := by
            have hz : m1 + 1 ≤ m2 := by omega
            exact_mod_cast hz
          have hnonneg : 0 ≤ (m1 : ℝ) + x (finN d hn) := hc1.1
          have hlt1 : (m2 : ℝ) + x (finN d hn) < 1 := hc2.2
          linarith
        · have hm21 : (m2 : ℝ) + 1 ≤ (m1 : ℝ) := by
            have hz : m2 + 1 ≤ m1 := by omega
            exact_mod_cast hz
          have hnonneg : 0 ≤ (m2 : ℝ) + x (finN d hn) := hc2.1
          have hlt1 : (m1 : ℝ) + x (finN d hn) < 1 := hc1.2
          linarith
      · intro m
        exact hY.inter (measurable_slabStrip hn m)
    _ = (volume : Measure (E d)) Y := by
      have hEq : (⋃ m : ℤ, Y ∩ slabStrip d n hn m) = Y := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_iUnion] at hx
          rcases hx with ⟨m, hmem⟩
          exact hmem.1
        · intro hy
          rw [Set.mem_iUnion]
          have hx : x ∈ Fslab d n := hsub hy
          rw [← slabStrip_tiles hn] at hx
          rcases (Set.mem_iUnion.mp hx) with ⟨m, hs⟩
          exact ⟨m, hy, hs⟩
      rw [hEq]


/-- the folded level-(n) set X is free along e_n, given that C is FoldFree -/
lemma fold_free_of_foldFree {d n : ℕ} (hn : n < d) {C : Set (E d)} (hfree : FoldFree d n C) :
    eFree d n hn ((latOrbit d n C) ∩ Fslab d n) := by
  intro m hm
  rw [Set.disjoint_left]
  intro y hy1 hy2
  rcases hy1 with ⟨hy1o, hy1s⟩
  have hy2X : y + (m : ℝ) • unitVec d hn ∈ (latOrbit d n C) ∩ Fslab d n := hy2
  rw [mem_latOrbit] at hy1o
  rcases hy1o with ⟨z1, hz1, hc1⟩
  have hy2o : y + (m : ℝ) • unitVec d hn ∈ latOrbit d n C := hy2X.1
  rw [mem_latOrbit] at hy2o
  rcases hy2o with ⟨z2, hz2, hc2⟩
  let c1 : E d := y - z1
  let c2 : E d := (y + (m : ℝ) • unitVec d hn) - z2
  have hc1' : c1 ∈ C := by dsimp [c1]; exact hc1
  have hc2' : c2 ∈ C := by dsimp [c2]; exact hc2
  have hdiff : c1 - c2 = -((m : ℝ) • unitVec d hn) - (z1 - z2) := by
    dsimp [c1, c2]
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
    ring
  have hz1idx : z1 (finN d hn) = 0 := hz1.2 (finN d hn) (by simp [finN])
  have hz2idx : z2 (finN d hn) = 0 := hz2.2 (finN d hn) (by simp [finN])
  have hL1 : Lzero d (n+1) (-((m : ℝ) • unitVec d hn)) := by
    have h := Lzero_unitVec hn (-m)
    simpa [Int.cast_neg, neg_smul] using h
  have hc1c2_int : Lzero d (n+1) (c1 - c2) := by
    rw [hdiff]
    exact Lzero_sub hL1 (Lzero_mono (by omega) (Lzero_sub hz1 hz2))
  have hval : (c1 - c2) (finN d hn) = -(m : ℝ) := by
    rw [hdiff]
    simp [unitVec_at hn, hz1idx, hz2idx, Pi.sub_apply, Pi.add_apply]
  have hnotC : ¬ Lzero d n (c1 - c2) := by
    intro hL
    have hvanish : (c1 - c2) (finN d hn) = 0 := hL.2 (finN d hn) (by simp [finN])
    have hmz : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have ha : (m : ℝ) = 0 := by linarith
    exact hmz ha
  have heq := hfree hc1' hc2' hc1c2_int hnotC
  have hzero : (c1 - c2) (finN d hn) = 0 := by
    rw [sub_eq_zero.mpr heq]
    rfl
  have hmz : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have ha : (m : ℝ) = 0 := by linarith
  exact hmz ha

/-- folding one more coordinate does not change the folded volume, provided no two points of C
    differ by a lattice vector at level n+1 outside level n -/
lemma Dμ_fold_eq {d n : ℕ} (hn : n < d) {C : Set (E d)}
    (hC : MeasurableSet C) (hfree : FoldFree d n C) :
    Dμ d (n+1) C = Dμ d n C := by
  have hXmeas : MeasurableSet ((latOrbit d n C) ∩ Fslab d n) :=
    (latOrbit_measurable hC).inter (Fslab_measurable d n)
  calc
    Dμ d (n+1) C = (volume : Measure (E d)) ((latOrbit d (n+1) C) ∩ Fslab d (n+1)) := rfl
    _ = (volume : Measure (E d)) (⋃ m : ℤ,
        ((fun w : E d => w + (m : ℝ) • unitVec d hn) '' (latOrbit d n C ∩ Fslab d n)) ∩ Fslab d (n+1)) := by
      rw [latOrbit_succ hn C]
    _ = (volume : Measure (E d)) ((latOrbit d n C) ∩ Fslab d n) :=
      fold_measure hn hXmeas (by intro x hx; exact hx.2) (fold_free_of_foldFree hn hfree)
    _ = Dμ d n C := rfl

/-- the fully-folded volume is at most 1 -/
lemma Dμ_le_one (d : ℕ) (C : Set (E d)) : Dμ d d C ≤ 1 := by
  unfold Dμ
  rw [← volume_Fslab_full d]
  exact measure_mono (Set.inter_subset_right)


-- =====================================================================
--  Peeling the last coordinate (E (d+1) ≃ ℝ × E d) and the slice identity
-- =====================================================================

abbrev ψ (d : ℕ) : E (d+1) ≃ᵐ ℝ × E d :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) (Fin.last d)

def lastCoord (d : ℕ) (x : E (d+1)) : ℝ := x (Fin.last d)
def dropLast (d : ℕ) (x : E (d+1)) : E d := fun j => x (Fin.castSucc j)
def insertLast (d : ℕ) (y : E d) (t : ℝ) : E (d+1) :=
  Fin.insertNth (Fin.last d) t (fun j : Fin d => y j)

lemma insertLast_coord (d : ℕ) (y : E d) (t : ℝ) :
    insertLast d y t (Fin.last d) = t := by
  simp [insertLast, Fin.insertNth_apply_same]

lemma insertLast_coord_castSucc (d : ℕ) (y : E d) (t : ℝ) (j : Fin d) :
    insertLast d y t (Fin.castSucc j) = y j := by
  simp [insertLast, Fin.insertNth_apply_succAbove, Fin.succAbove_last]

lemma eq_last_or_castSucc {d : ℕ} (j : Fin (d+1)) :
    j = Fin.last d ∨ ∃ j0 : Fin d, Fin.castSucc j0 = j := by
  by_cases hj : j.val = d
  · left; ext; simp; omega
  · right
    refine ⟨⟨j.val, by omega⟩, ?_⟩
    ext
    simp

lemma insertLast_surj (d : ℕ) (x : E (d+1)) :
    insertLast d (dropLast d x) (lastCoord d x) = x := by
  ext j
  rcases eq_last_or_castSucc j with hlast | ⟨j0, hj0⟩
  · subst j
    simp [insertLast, lastCoord, Fin.insertNth_apply_same]
  · subst j
    simp [insertLast, dropLast, Fin.insertNth_apply_succAbove, Fin.succAbove_last]

lemma ψ_apply (d : ℕ) (x : E (d+1)) :
    ψ d x = (lastCoord d x, dropLast d x) := by
  unfold ψ
  rw [MeasurableEquiv.piFinSuccAbove_apply]
  ext j
  · rfl
  · -- second component: x((last d).succAbove j) vs x(castSucc j)
    change (fun j0 : Fin d => x ((Fin.last d).succAbove j0)) j = (fun j0 : Fin d => x (Fin.castSucc j0)) j
    simp [Fin.succAbove_last]

lemma ψ_insertLast (d : ℕ) (y : E d) (t : ℝ) :
    ψ d (insertLast d y t) = (t, y) := by
  -- ψ (insertLast y t) = (t, y): both are determined by ψ_apply
  rw [ψ_apply]
  simp [lastCoord_insertLast' d y t, dropLast_insertLast' d y t]
  where
  lastCoord_insertLast' (d : ℕ) (y : E d) (t : ℝ) : lastCoord d (insertLast d y t) = t := by
    simp [lastCoord, insertLast, Fin.insertNth_apply_same]
  dropLast_insertLast' (d : ℕ) (y : E d) (t : ℝ) : dropLast d (insertLast d y t) = y := by
    funext j
    simp [dropLast, insertLast, Fin.insertNth_apply_succAbove, Fin.succAbove_last]

lemma ψ_symm_apply (d : ℕ) (p : ℝ × E d) :
    (ψ d).symm p = insertLast d p.2 p.1 := by
  rw [ψ, MeasurableEquiv.piFinSuccAbove_symm_apply]
  -- ψ.symm = insertNthEquiv.toFun : (t, f) ↦ insertNth last t f
  ext j
  rcases eq_last_or_castSucc j with hlast | ⟨j0, hj0⟩
  · subst j
    simp [insertLast, Fin.insertNth_apply_same]
  · subst j
    simp [insertLast, Fin.insertNth_apply_succAbove, Fin.succAbove_last]

lemma ψ_mp (d : ℕ) :
    MeasurePreserving (ψ d) (volume : Measure (E (d+1))) (volume : Measure (ℝ × E d)) := by
  unfold ψ
  exact MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) (Fin.last d)

lemma insertLast_sub (d : ℕ) (y z : E d) (t : ℝ) :
    insertLast d (y - z) t = insertLast d y t - insertLast d z 0 := by
  ext j
  rcases eq_last_or_castSucc j with hlast | ⟨j0, hj0⟩
  · subst j; simp [insertLast_coord]
  · subst j; simp [insertLast_coord_castSucc, Pi.sub_apply]



/-- a point with last coordinate t belongs to the (d+1,n)-slab iff its drop belongs to the (d,n)-slab -/

lemma insertLast_mem_Fslab {d n : ℕ} (hn : n ≤ d) (y : E d) (t : ℝ) :
    insertLast d y t ∈ Fslab (d+1) n ↔ y ∈ Fslab d n := by
  constructor
  · intro hy j hj
    have hc : insertLast d y t (Fin.castSucc j) = y j := insertLast_coord_castSucc d y t j
    rw [← hc]
    exact hy (Fin.castSucc j) (by simpa using hj)
  · intro hy j hj
    have hjne : j ≠ Fin.last d := by
      intro hlast
      have : (Fin.last d).val = d := by simp [Fin.last]
      omega
    rcases (eq_last_or_castSucc j) with hlast | ⟨j0, hj0⟩
    · exact False.elim (hjne hlast)
    · rw [← hj0]
      rw [insertLast_coord_castSucc]
      exact hy j0 (by simpa [hj0.symm] using hj)

/-- dropping the last coordinate maps the (d+1,n)-lattice into the (d,n)-lattice -/
lemma Lzero_dropLast {d n : ℕ} {w : E (d+1)} (hw : Lzero (d+1) n w) :
    Lzero d n (dropLast d w) := by
  constructor
  · intro j
    exact hw.1 (Fin.castSucc j)
  · intro j hj
    exact hw.2 (Fin.castSucc j) (by simpa using hj)

/-- inserting a lattice point at level (d,n) with last coordinate 0 gives a level (d+1,n) lattice point -/
lemma Lzero_insertLast_zero {d n : ℕ} (hn : n ≤ d) {z : E d} (hz : Lzero d n z) :
    Lzero (d+1) n (insertLast d z 0) := by
  constructor
  · intro j
    rcases eq_last_or_castSucc j with hlast | ⟨j0, hj0⟩
    · rw [hlast]; simp [insertLast_coord]; exact IntV_zero
    · rw [← hj0]; rw [insertLast_coord_castSucc]; exact hz.1 j0
  · intro j hj
    rcases eq_last_or_castSucc j with hlast | ⟨j0, hj0⟩
    · rw [hlast]
      have hco : insertLast d z 0 (Fin.last d) = 0 := insertLast_coord d z 0
      simpa [hco]
    · rw [← hj0]; rw [insertLast_coord_castSucc]; exact hz.2 j0 (by simpa [hj0.symm] using hj)

/-- the last coordinate of a level-n lattice point vanishes when n ≤ d -/
lemma Lzero_last_zero {d n : ℕ} (hn : n ≤ d) {w : E (d+1)} (hw : Lzero (d+1) n w) :
    w (Fin.last d) = 0 := by
  have hle : n ≤ (Fin.last d).val := by simpa [Fin.last] using hn
  exact hw.2 (Fin.last d) hle

lemma dropLast_insertLast_zero {d n : ℕ} (hn : n ≤ d) {w : E (d+1)} (hw : Lzero (d+1) n w) :
    insertLast d (dropLast d w) 0 = w := by
  calc insertLast d (dropLast d w) 0
      = insertLast d (dropLast d w) (lastCoord d w) := by
          have hw0 : w (Fin.last d) = 0 := Lzero_last_zero hn hw
          simp [lastCoord, hw0]
  _ = w := insertLast_surj d w

/-- membership in the orbit at level (d+1,n) can be tested on the drop -/
lemma insertLast_mem_latOrbit {d n : ℕ} (hn : n ≤ d) (C : Set (E (d+1))) (y : E d) (t : ℝ) :
    insertLast d y t ∈ latOrbit (d+1) n C ↔ y ∈ latOrbit d n {x : E d | insertLast d x t ∈ C} := by
  rw [mem_latOrbit]
  constructor
  · intro hw
    rcases hw with ⟨w, hwL, hwy⟩
    rw [mem_latOrbit]
    refine ⟨dropLast d w, Lzero_dropLast hwL, ?_⟩
    change insertLast d (y - dropLast d w) t ∈ C
    have hw0 : w = insertLast d (dropLast d w) 0 := (dropLast_insertLast_zero hn hwL).symm
    have hsub := insertLast_sub d y (dropLast d w) t
    rw [hw0, ← hsub] at hwy
    exact hwy
  · intro hz
    rw [mem_latOrbit] at hz
    rcases hz with ⟨z, hzL, hzy⟩
    refine ⟨insertLast d z 0, Lzero_insertLast_zero hn hzL, ?_⟩
    have hsub := insertLast_sub d y z t
    rw [← hsub]
    change insertLast d (y - z) t ∈ C
    exact hzy

/-- the fiber of the peeled orbit is the orbit of the slice -/
lemma peel_fiber {d n : ℕ} (hn : n ≤ d) {C : Set (E (d+1))} (t : ℝ) :
    (fun y : E d => (t, y)) ⁻¹' ((ψ d) '' ((latOrbit (d+1) n C) ∩ Fslab (d+1) n)) =
      (latOrbit d n {x : E d | insertLast d x t ∈ C}) ∩ Fslab d n := by
  ext y
  constructor
  · intro hy
    have hpaste : insertLast d y t ∈ (latOrbit (d+1) n C) ∩ Fslab (d+1) n := by
      rcases hy with ⟨x, hx, hxeq⟩
      have hx' : x = insertLast d y t := by
        calc x = (ψ d).symm ((ψ d) x) := ((ψ d).symm_apply_apply x).symm
        _ = (ψ d).symm (t, y) := by
          rw [hxeq]
        _ = insertLast d y t := by
          rw [ψ_symm_apply]
      rw [hx'] at hx
      exact hx
    exact ⟨(insertLast_mem_latOrbit (d := d) (n := n) hn C y t).mp hpaste.1,
      (insertLast_mem_Fslab (d := d) hn y t).mp hpaste.2⟩
  · intro hy
    have hpaste : insertLast d y t ∈ (latOrbit (d+1) n C) ∩ Fslab (d+1) n :=
      ⟨(insertLast_mem_latOrbit (d := d) (n := n) hn C y t).mpr hy.1,
       (insertLast_mem_Fslab (d := d) hn y t).mpr hy.2⟩
    refine ⟨insertLast d y t, hpaste, ?_⟩
    exact ψ_insertLast d y t

-- 1-dimensional ENNReal substitution t ↦ t/s (for the slice integral)
lemma map_scale (s : ℝ) (hs0 : 0 < s) :
    Measure.map (fun t : ℝ => s⁻¹ • t) (volume : Measure ℝ) = ENNReal.ofReal s • volume := by
  apply Measure.ext
  intro A hA
  have hmeas : Measurable (fun t : ℝ => s⁻¹ • t) := measurable_const_smul (s⁻¹)
  rw [Measure.map_apply hmeas hA]
  have hEq : (fun t : ℝ => s⁻¹ • t) ⁻¹' A = (s • A : Set ℝ) := by
    ext t
    constructor
    · intro ht
      refine ⟨s⁻¹ • t, ht, ?_⟩
      change s • (s⁻¹ • t) = t
      rw [smul_smul]
      field_simp [ne_of_gt hs0]
      simp
    · intro ht
      rcases ht with ⟨x, hx, rfl⟩
      change s⁻¹ • (s • x) ∈ A
      rw [smul_smul]
      field_simp [ne_of_gt hs0]
      simpa using hx
  rw [hEq]
  rw [Measure.addHaar_smul_of_nonneg (volume : Measure ℝ) (le_of_lt hs0) A]
  simp

lemma lintegral_scale_sub (s : ℝ) (hs1 : 1 ≤ s) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ (t : ℝ), f ((s⁻¹) • t) ∂(volume : Measure ℝ)) =
      ENNReal.ofReal s * (∫⁻ (t : ℝ), f t ∂(volume : Measure ℝ)) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  calc
    (∫⁻ (t : ℝ), f ((s⁻¹) • t) ∂(volume : Measure ℝ))
        = ∫⁻ (u : ℝ), f u ∂(Measure.map (fun t : ℝ => s⁻¹ • t) (volume : Measure ℝ)) := by
          rw [← MeasureTheory.lintegral_map hf (measurable_const_smul (s⁻¹))]
    _ = ∫⁻ (u : ℝ), f u ∂(ENNReal.ofReal s • volume) := by
          rw [map_scale s hs0]
    _ = ENNReal.ofReal s * (∫⁻ (u : ℝ), f u ∂(volume : Measure ℝ)) := by
          rw [MeasureTheory.lintegral_smul_measure]
          simp


-- ===== torus (full-fold) translation invariance and scaling =====
def ZL (k : ℕ) : AddSubgroup (E k) where
  carrier := {x : E k | IntFun k x}
  add_mem' := by
    intro a b ha hb
    exact IntFun_add ha hb
  zero_mem' := by
    exact IntFun_zero k
  neg_mem' := by
    intro a ha
    exact IntFun_neg ha

instance (k : ℕ) : Countable (ZL k) := by
  refine Function.Injective.countable (f := fun x : ZL k => fun j : Fin k =>
    (Classical.choose (x.2 j) : ℤ)) ?_
  intro x y h
  apply Subtype.ext
  ext j
  have h1 := congr_fun h j
  have hx := Classical.choose_spec (x.2 j)
  have hy := Classical.choose_spec (y.2 j)
  rw [← hx, ← hy]
  exact_mod_cast h1

lemma vadd_eq_coe (k : ℕ) (g : ZL k) (x : E k) : g +ᵥ x = (g : E k) + x := by
  rw [AddSubgroup.vadd_def, vadd_eq_add]

lemma vadd_add (k : ℕ) (g : ZL k) (x : E k) (j : Fin k) :
    (g +ᵥ x) j = (g : E k) j + x j := by
  rw [vadd_eq_coe]
  rfl

lemma vadd_add_vec (k : ℕ) (g : ZL k) (x w : E k) :
    (g +ᵥ x) + w = g +ᵥ (x + w) := by
  rw [vadd_eq_coe, vadd_eq_coe]
  abel

lemma fract_mem_Ico (t : ℝ) : t - (Int.floor t : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
  have h1 : (Int.floor t : ℝ) ≤ t := Int.floor_le t
  have h2 : t < (Int.floor t : ℝ) + 1 := Int.lt_floor_add_one t
  constructor <;> linarith

lemma mem_cube_iff {k : ℕ} (y : E k) : y ∈ Fslab k k ↔ ∀ j : Fin k, y j ∈ Set.Ico (0 : ℝ) 1 := by
  simp [Fslab]

/-- each point has a unique integer representative in the cube -/
lemma cube_rep (k : ℕ) (x : E k) : ∃! g : ZL k, g +ᵥ x ∈ Fslab k k := by
  let g : ZL k := ⟨(fun j : Fin k => -((Int.floor (x j) : ℤ) : ℝ)),
    by intro j; exact ⟨-Int.floor (x j), by simp⟩⟩
  have hgx : g +ᵥ x ∈ Fslab k k := by
    rw [mem_cube_iff]
    intro j
    rw [vadd_add]
    dsimp [g]
    change -((Int.floor (x j) : ℤ) : ℝ) + x j ∈ Set.Ico (0 : ℝ) 1
    simpa [sub_eq_add_neg, add_comm] using fract_mem_Ico (x j)
  refine ⟨g, hgx, ?_⟩
  intro g' hg'
  apply Subtype.ext
  ext j
  have h1 : (g : E k) j + x j ∈ Set.Ico (0 : ℝ) 1 := by
    have := (mem_cube_iff (g +ᵥ x)).mp hgx j
    simpa [vadd_add] using this
  have h2 : (g' : E k) j + x j ∈ Set.Ico (0 : ℝ) 1 := by
    have := (mem_cube_iff (g' +ᵥ x)).mp hg' j
    simpa [vadd_add] using this
  rcases g.2 j with ⟨m1, hm1⟩
  rcases g'.2 j with ⟨m2, hm2⟩
  have ha1 : (m1 : ℝ) + x j ∈ Set.Ico (0 : ℝ) 1 := by simpa [hm1] using h1
  have ha2 : (m2 : ℝ) + x j ∈ Set.Ico (0 : ℝ) 1 := by simpa [hm2] using h2
  have hm_eq : m1 = m2 := by
    by_contra hmn
    have hk : (m1 - m2 : ℤ) ≠ 0 := by
      intro hz
      apply hmn
      exact_mod_cast (sub_eq_zero.mp hz)
    have hk1 : (1 : ℤ) ≤ |m1 - m2| := by
      rcases lt_or_gt_of_ne hk with hlt | hgt
      · have : |m1 - m2| = -(m1 - m2) := abs_of_neg hlt
        rw [this]; omega
      · have : |m1 - m2| = m1 - m2 := abs_of_pos hgt
        rw [this]; omega
    have hInt : (1 : ℝ) ≤ |((m1 - m2 : ℤ) : ℝ)| := by exact_mod_cast hk1
    have hdiff_lt : |(m1 : ℝ) + x j - ((m2 : ℝ) + x j)| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [ha1.1, ha1.2, ha2.1, ha2.2]
    have hdiff_eq : (m1 : ℝ) + x j - ((m2 : ℝ) + x j) = ((m1 - m2 : ℤ) : ℝ) := by
      norm_num
    have : (1 : ℝ) ≤ |(m1 : ℝ) + x j - ((m2 : ℝ) + x j)| := by
      rw [hdiff_eq]
      exact hInt
    linarith
  rw [← hm1, ← hm2, hm_eq]

lemma cube_fund (k : ℕ) : IsAddFundamentalDomain (ZL k) (Fslab k k) (volume : Measure (E k)) := by
  exact IsAddFundamentalDomain.mk' (Fslab_measurable k k).nullMeasurableSet (cube_rep k)

/-- the preimage-translate of the cube is also a fundamental domain -/
lemma cube_w_rep (k : ℕ) (w x : E k) :
    ∃! g : ZL k, g +ᵥ x ∈ (fun y : E k => y + w) ⁻¹' Fslab k k := by
  rcases cube_rep k (x + w) with ⟨g, hg, huniq⟩
  refine ⟨g, ?_, ?_⟩
  · change (g +ᵥ x) + w ∈ Fslab k k
    rw [vadd_add_vec]
    exact hg
  · intro g' hg'
    apply huniq
    have hg'' : g' +ᵥ (x + w) ∈ Fslab k k := by
      rw [← vadd_add_vec]
      change (g' +ᵥ x) + w ∈ Fslab k k
      simpa [Set.mem_preimage] using hg'
    exact hg''

lemma cube_w_fund (k : ℕ) (w : E k) :
    IsAddFundamentalDomain (ZL k) ((fun y : E k => y + w) ⁻¹' Fslab k k) (volume : Measure (E k)) := by
  refine IsAddFundamentalDomain.mk' ?meas (cube_w_rep k w)
  exact ((Fslab_measurable k k).preimage (Homeomorph.addRight w).measurable).nullMeasurableSet

lemma ZL_mem_Lzero {k : ℕ} (g : ZL k) : Lzero k k (g : E k) := by
  constructor
  · intro j; exact g.2 j
  · intro j hj
    have : j.val < k := j.isLt
    omega

lemma orbit_invariant (k : ℕ) (T : Set (E k)) (g : ZL k) :
    (fun x : E k => g +ᵥ x) ⁻¹' (latOrbit k k T) = latOrbit k k T := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_preimage] at hx
    rw [vadd_eq_coe] at hx
    rw [mem_latOrbit] at hx ⊢
    rcases hx with ⟨z, hz, hxz⟩
    refine ⟨z - (g : E k), Lzero_sub hz (ZL_mem_Lzero g), ?_⟩
    have : x - (z - (g : E k)) = (g : E k) + x - z := by abel
    simpa [this] using hxz
  · intro hx
    rw [mem_latOrbit] at hx
    rw [Set.mem_preimage]
    rw [vadd_eq_coe]
    rw [mem_latOrbit]
    rcases hx with ⟨z, hz, hxz⟩
    refine ⟨z + (g : E k), Lzero_add hz (ZL_mem_Lzero g), ?_⟩
    have : (g : E k) + x - (z + (g : E k)) = x - z := by abel
    rwa [this]

lemma orbit_translate (k : ℕ) (T : Set (E k)) (w : E k) :
    latOrbit k k ((fun x : E k => x + w) '' T) = (fun x : E k => x + w) '' (latOrbit k k T) := by
  ext x
  rw [mem_latOrbit] at *
  constructor
  · intro hx
    rcases hx with ⟨z, hz, hxz⟩
    rcases hxz with ⟨t, ht, hteq⟩
    have ht_eq' : t + w = x - z := by simpa using hteq
    refine ⟨x - w, ?_, ?_⟩
    · rw [mem_latOrbit]
      refine ⟨z, hz, ?_⟩
      have : (x - w) - z = t := by
        calc (x - w) - z = (x - z) - w := by abel
        _ = (t + w) - w := by rw [← ht_eq']
        _ = t := by abel
      rwa [this]
    · abel
  · intro hx
    rcases hx with ⟨a, ha, haeq⟩
    rw [mem_latOrbit] at ha
    rcases ha with ⟨z, hz, haz⟩
    refine ⟨z, hz, ?_⟩
    have haeq' : a + w = x := by simpa using haeq
    have hxz : x - z = (a - z) + w := by
      calc x - z = (a + w) - z := by rw [← haeq']
      _ = (a - z) + w := by abel
    refine ⟨a - z, haz, hxz.symm⟩

lemma Dμ_full_translate (k : ℕ) {T : Set (E k)} (hT : MeasurableSet T) (w : E k) :
    Dμ k k ((fun x : E k => x + w) '' T) = Dμ k k T := by
  let A : Set (E k) := latOrbit k k T
  have hAmeas : MeasurableSet A := by dsimp [A]; exact latOrbit_measurable hT
  have hinv : ∀ g : ZL k, (fun x : E k => g +ᵥ x) ⁻¹' A = A := by
    intro g; dsimp [A]; exact orbit_invariant k T g
  have hme := MeasureTheory.IsAddFundamentalDomain.measure_set_eq (cube_fund k)
    (cube_w_fund k w) hAmeas hinv
  have hEqSet : ((fun x : E k => x + w) '' A) ∩ Fslab k k =
      (fun x : E k => x + w) '' (A ∩ ((fun y : E k => y + w) ⁻¹' Fslab k k)) := by
    ext z
    constructor
    · intro hz
      rcases hz.1 with ⟨a, ha, haeq⟩
      refine ⟨a, ⟨ha, ?_⟩, haeq⟩
      simpa [haeq] using hz.2
    · intro hz
      rcases hz with ⟨a, ha, haeq⟩
      constructor
      · refine ⟨a, ha.1, haeq⟩
      · simpa [haeq] using ha.2
  calc
    Dμ k k ((fun x : E k => x + w) '' T)
        = (volume : Measure (E k)) ((latOrbit k k ((fun x : E k => x + w) '' T)) ∩ Fslab k k) := rfl
    _ = (volume : Measure (E k)) (((fun x : E k => x + w) '' A) ∩ Fslab k k) := by
      congr 1
      rw [orbit_translate]
    _ = (volume : Measure (E k)) (A ∩ ((fun y : E k => y + w) ⁻¹' Fslab k k)) := by
      rw [hEqSet]
      exact vol_translate w (hAmeas.inter ((Fslab_measurable k k).preimage (Homeomorph.addRight w).measurable))
    _ = (volume : Measure (E k)) (A ∩ Fslab k k) := hme.symm
    _ = Dμ k k T := by
      dsimp [A]
      rfl



/-- monotonicity of Dμ under set inclusion -/
lemma Dμ_mono {k n : ℕ} {C D : Set (E k)} (h : C ⊆ D) : Dμ k n C ≤ Dμ k n D := by
  unfold Dμ
  have horb : latOrbit k n C ⊆ latOrbit k n D := by
    intro x hx
    rw [mem_latOrbit] at hx ⊢
    rcases hx with ⟨z, hz, hxz⟩
    exact ⟨z, hz, h hxz⟩
  exact measure_mono (Set.inter_subset_inter_left (Fslab k n) horb)

/-- the torus lemma: folding into the cube, convex sets grow under scaling by s ≥ 1 -/
lemma Dμ_torus_scale (k : ℕ) {C : Set (E k)} (hC : MeasurableSet C) (hconv : Convex ℝ C)
    (s : ℝ) (hs1 : 1 ≤ s) : Dμ k k (s • C) ≥ Dμ k k C := by
  by_cases hCempty : C = ∅
  · subst hCempty
    simp
  · rcases (nonempty_iff_ne_empty.mpr hCempty) with ⟨u, hu⟩
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    have hmono : Dμ k k C ≤ Dμ k k ((fun x : E k => ((1 - s) • u) + x) '' (s • C)) := by
      -- C ⊆ (fun x => ((1-s)•u) + x)''(s•C)
      have hsub : C ⊆ (fun x : E k => ((1 - s) • u) + x) '' (s • C) := by
        intro c hc
        let w : E k := (1 / s) • c + (1 - 1 / s) • u
        have hw : w ∈ C := by
          dsimp [w]
          have h1 : (0 : ℝ) ≤ 1 / s := by positivity
          have h2 : (0 : ℝ) ≤ 1 - 1 / s := by
            have h1s : 1 / s ≤ 1 := by
              rw [div_le_one hs0]
              exact hs1
            linarith
          have hsum : 1 / s + (1 - 1 / s) = 1 := by ring
          exact hconv hc hu h1 h2 hsum
        have hmain : c = ((1 - s) • u) + (s • w) := by
          dsimp [w]
          funext j
          simp [Pi.smul_apply, Pi.add_apply, Pi.sub_apply]
          field_simp [ne_of_gt hs0]
          ring
        refine ⟨s • w, ⟨w, hw, rfl⟩, hmain.symm⟩
      -- orbit-mono
      exact Dμ_mono hsub
    have htrans : Dμ k k ((fun x : E k => ((1 - s) • u) + x) '' (s • C)) = Dμ k k (s • C) := by
      have hfunext : (fun x : E k => ((1 - s) • u) + x) = fun x : E k => x + ((1 - s) • u) := by
        funext x
        exact add_comm _ _
      rw [hfunext]
      have hsC : MeasurableSet (s • C) := by
        exact smul_measurable (d := k) s (ne_of_gt hs0) hC
      exact Dμ_full_translate k hsC ((1 - s) • u)
    exact le_trans hmono htrans.le




/-- slice of C at last coordinate u -/
def sec (d : ℕ) (C : Set (E (d+1))) (u : ℝ) : Set (E d) :=
  {x : E d | insertLast d x u ∈ C}

/-- inserting the last coordinate is measurable in the E d-part -/
lemma sec_measurable {d : ℕ} {C : Set (E (d+1))} (hC : MeasurableSet C) (u : ℝ) :
    MeasurableSet (sec d C u) := by
  unfold sec
  have hmeas : Measurable (fun x : E d => insertLast d x u) := by
    rw [measurable_pi_iff]
    intro j
    by_cases hj : j = Fin.last d
    · subst j
      -- constant function u
      have hpt : (fun x : E d => insertLast d x u (Fin.last d)) = fun _ : E d => u := by
        funext x
        exact insertLast_coord d x u
      rw [hpt]
      exact measurable_const
    · rcases (eq_last_or_castSucc j) with hlast | ⟨j0, hj0⟩
      · exact False.elim (hj hlast)
      · rw [← hj0]
        have hpt : (fun x : E d => insertLast d x u (Fin.castSucc j0)) = fun x : E d => x j0 := by
          funext x
          exact insertLast_coord_castSucc d x u j0
        rw [hpt]
        exact measurable_pi_apply j0
  exact hC.preimage hmeas

/-- slice of a convex set is convex -/
lemma sec_convex {d : ℕ} {C : Set (E (d+1))} (hC : Convex ℝ C) (u : ℝ) : Convex ℝ (sec d C u) := by
  intro x hx y hy a b ha hb hab
  change insertLast d (a • x + b • y) u ∈ C
  have hlin : insertLast d (a • x + b • y) u = a • insertLast d x u + b • insertLast d y u := by
    ext j
    rcases eq_last_or_castSucc j with hlast | ⟨j0, hj0⟩
    · subst j
      simp [insertLast_coord, Pi.add_apply, Pi.smul_apply]
      rw [← add_mul]
      rw [hab]
      simp
    · subst j
      simp [insertLast_coord_castSucc, Pi.add_apply, Pi.smul_apply]
  rw [hlin]
  exact hC hx hy ha hb hab


/-- scalar multiplication commutes with inserting the last coordinate -/
lemma smul_insertLast {d : ℕ} (a : ℝ) (x : E d) (t : ℝ) :
    a • insertLast d x t = insertLast d (a • x) (a * t) := by
  ext j
  rcases eq_last_or_castSucc j with hlast | ⟨j0, hj0⟩
  · subst j
    simp [insertLast_coord, Pi.smul_apply]
  · subst j
    simp [insertLast_coord_castSucc, Pi.smul_apply]

/-- scaling a body then slicing at u equals scaling the slice at u/s -/
lemma sec_smul {d : ℕ} (C : Set (E (d+1))) (s : ℝ) (hs0 : s ≠ 0) (u : ℝ) :
    sec d (s • C) u = s • sec d C (s⁻¹ • u) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨c, hc, hceq⟩
    have h1 := congrArg (fun z : E (d+1) => s⁻¹ • z) hceq
    rw [smul_insertLast] at h1
    have h2 : s⁻¹ • (s • c) = c := by
      simp [smul_smul, inv_mul_cancel₀ hs0]
    rw [h2] at h1
    refine ⟨s⁻¹ • y, ?_, ?_⟩
    · change insertLast d (s⁻¹ • y) (s⁻¹ • u) ∈ C
      simpa [smul_eq_mul] using h1.symm ▸ hc
    · change s • (s⁻¹ • y) = y
      rw [smul_smul]
      field_simp [hs0]
      simp
  · intro hy
    rcases hy with ⟨z, hz, hyz⟩
    have hyz' : y = s • z := hyz.symm
    have hzil : insertLast d z (s⁻¹ • u) ∈ C := hz
    have hconv : insertLast d (s • z) u = s • insertLast d z (s⁻¹ • u) := by
      have hback := (smul_insertLast s z (s⁻¹ • u)).symm
      have hU : u = s * (s⁻¹ • u) := by
        rw [smul_eq_mul]
        field_simp [hs0]
      calc insertLast d (s • z) u = insertLast d (s • z) (s * (s⁻¹ • u)) :=
        congrArg (fun t : ℝ => insertLast d (s • z) t) hU
      _ = s • insertLast d z (s⁻¹ • u) := by
        simpa [smul_eq_mul] using hback
    have hmain : insertLast d y u ∈ s • C := by
      rw [hyz', hconv]
      refine ⟨insertLast d z (s⁻¹ • u), hzil, rfl⟩
    change insertLast d y u ∈ s • C
    exact hmain

/-- the map (u,y) ↦ insertLast d y u is measurable -/
lemma measurable_insertLast_paste {d : ℕ} :
    Measurable (fun p : ℝ × E d => insertLast d p.2 p.1) := by
  rw [measurable_pi_iff]
  intro j
  by_cases hj : j = Fin.last d
  · subst j
    have hpt : (fun p : ℝ × E d => insertLast d p.2 p.1 (Fin.last d)) = fun p : ℝ × E d => p.1 := by
      funext p
      exact insertLast_coord d p.2 p.1
    rw [hpt]
    exact measurable_fst
  · rcases (eq_last_or_castSucc j) with hlast | ⟨j0, hj0⟩
    · exact False.elim (hj hlast)
    · rw [← hj0]
      have hpt : (fun p : ℝ × E d => insertLast d p.2 p.1 (Fin.castSucc j0)) = fun p : ℝ × E d => p.2 j0 := by
        funext p
        exact insertLast_coord_castSucc d p.2 p.1 j0
      rw [hpt]
      exact (measurable_pi_apply j0).comp measurable_snd


/-- (u,y) ↦ insertLast d (y - z) u is measurable -/
lemma measurable_insertLast_sub {d : ℕ} (z : E d) :
    Measurable (fun p : ℝ × E d => insertLast d (p.2 - z) p.1) := by
  rw [measurable_pi_iff]
  intro j
  by_cases hj : j = Fin.last d
  · subst j
    have hpt : (fun p : ℝ × E d => insertLast d (p.2 - z) p.1 (Fin.last d)) = fun p : ℝ × E d => p.1 := by
      funext p
      exact insertLast_coord d (p.2 - z) p.1
    rw [hpt]
    exact measurable_fst
  · rcases (eq_last_or_castSucc j) with hlast | ⟨j0, hj0⟩
    · exact False.elim (hj hlast)
    · rw [← hj0]
      have hpt : (fun p : ℝ × E d => insertLast d (p.2 - z) p.1 (Fin.castSucc j0)) = fun p : ℝ × E d => p.2 j0 - z j0 := by
        funext p
        rw [insertLast_coord_castSucc]
        rfl
      rw [hpt]
      exact ((measurable_pi_apply j0).comp measurable_snd).sub measurable_const

/-- A-measurable graph of the folded-volume body as a function of the slice coordinate -/
lemma bodyA_measurable (d n : ℕ) {C : Set (E (d+1))} (hC : MeasurableSet C) :
    MeasurableSet {(p : ℝ × E d) | p.2 ∈ (latOrbit d n (sec d C p.1)) ∩ Fslab d n} := by
  have hEq : {(p : ℝ × E d) | p.2 ∈ (latOrbit d n (sec d C p.1)) ∩ Fslab d n} =
      (⋃ z : Ltype d n, (fun p : ℝ × E d => insertLast d (p.2 - (z : E d)) p.1) ⁻¹' C) ∩
        (Set.univ ×ˢ Fslab d n) := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨hpa, hpb⟩
      rw [mem_latOrbit] at hpa
      rcases hpa with ⟨w, hw, hpw⟩
      refine ⟨?_, ?_⟩
      · rw [Set.mem_iUnion]
        refine ⟨(⟨w, hw⟩ : Ltype d n), ?_⟩
        change insertLast d (p.2 - (⟨w, hw⟩ : Ltype d n)) p.1 ∈ C
        change insertLast d (p.2 - w) p.1 ∈ C
        exact hpw
      · exact ⟨trivial, hpb⟩
    · intro hp
      rcases hp with ⟨hz, hz2⟩
      rw [Set.mem_iUnion] at hz
      rcases hz with ⟨z, hzpre⟩
      rcases hz2 with ⟨hz2a, hz2b⟩
      constructor
      · rw [mem_latOrbit]
        refine ⟨(z : E d), z.2, ?_⟩
        change insertLast d (p.2 - (z : E d)) p.1 ∈ C
        exact hzpre
      · exact hz2b
  rw [hEq]
  exact (MeasurableSet.iUnion (fun z : Ltype d n =>
    (hC.preimage (measurable_insertLast_sub (z : E d))))).inter
    (MeasurableSet.univ.prod (Fslab_measurable d n))

/-- u ↦ Dμ d n (sec d C u) is a measurable ENNReal-valued function -/
lemma sec_integrand_measurable (d n : ℕ) (hn : n ≤ d) {C : Set (E (d+1))} (hC : MeasurableSet C) :
    Measurable (fun u : ℝ => Dμ d n (sec d C u)) := by
  let s : Set (ℝ × E d) := {(p : ℝ × E d) | p.2 ∈ (latOrbit d n (sec d C p.1)) ∩ Fslab d n}
  have hA : MeasurableSet s := by
    dsimp [s]
    exact bodyA_measurable d n hC
  have hmeas : Measurable (fun x : ℝ => (volume : Measure (E d)) ((Prod.mk x) ⁻¹' s)) := by
    exact measurable_measure_prodMk_left hA
  convert hmeas using 1
  ext u
  rfl

/-- 1-dimensional substitution for the slice integrals -/
lemma Dμ_sec_sub (d n : ℕ) (hn : n ≤ d) {C : Set (E (d+1))} (hC : MeasurableSet C)
    (s : ℝ) (hs1 : 1 ≤ s) :
    (∫⁻ (t : ℝ), Dμ d n (sec d C (s⁻¹ • t)) ∂(volume : Measure ℝ)) =
      ENNReal.ofReal s * (∫⁻ (u : ℝ), Dμ d n (sec d C u) ∂(volume : Measure ℝ)) := by
  let f : ℝ → ℝ≥0∞ := fun u => Dμ d n (sec d C u)
  have hf : Measurable f := by
    dsimp [f]
    exact sec_integrand_measurable d n hn hC
  have h := lintegral_scale_sub s hs1 f hf
  -- h : ∫⁻ t, f (s⁻¹ • t) = ofReal s * ∫⁻ f
  dsimp [f] at h
  exact h

/-- the fold-level-n scaling lemma (Dμ (sC) ≥ s^{d−n}·Dμ C for convex C) -/
lemma hEq_image (d : ℕ) (S : Set (E (d+1))) :
    (ψ d) '' S = (ψ d).symm ⁻¹' S := by
  ext y
  constructor
  · rintro ⟨x, hx, hxeq⟩
    rw [← hxeq]
    rw [Set.mem_preimage]
    rw [(ψ d).symm_apply_apply x]
    exact hx
  · intro hy
    refine ⟨(ψ d).symm y, hy, ?_⟩
    exact (ψ d).apply_symm_apply y

lemma hEq_preimage (d : ℕ) (S : Set (E (d+1))) :
    (ψ d) ⁻¹' ((ψ d) '' S) = S := by
  ext x
  constructor
  · intro hx
    -- hx : ψ x ∈ ψ''S: ∃ y ∈ S, ψ y = ψ x: by injectivity y = x
    rcases hx with ⟨y, hy, hyx⟩
    have : y = x := (ψ d).injective hyx
    rw [this] at hy
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma Dμ_peel (d n : ℕ) (hn : n ≤ d) {C : Set (E (d+1))} (hC : MeasurableSet C) :
    Dμ (d+1) n C =
      ∫⁻ (t : ℝ), Dμ d n {x : E d | insertLast d x t ∈ C} ∂(volume : Measure ℝ) := by
  let S : Set (E (d+1)) := (latOrbit (d+1) n C) ∩ Fslab (d+1) n
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (latOrbit_measurable hC).inter (Fslab_measurable (d+1) n)
  have hT : MeasurableSet ((ψ d) '' S) := by
    rw [hEq_image]
    exact hS.preimage (ψ d).symm.measurable
  calc
    Dμ (d+1) n C = (volume : Measure (E (d+1))) S := rfl
    _ = (volume : Measure (ℝ × E d)) ((ψ d) '' S) := by
      have h := (ψ_mp d).measure_preimage_emb (ψ d).measurableEmbedding ((ψ d) '' S)
      rw [hEq_preimage] at h
      exact h
    _ = (volume.prod (volume : Measure (E d))) ((ψ d) '' S) := by
      rw [Measure.volume_eq_prod]
    _ = ∫⁻ (t : ℝ), (volume : Measure (E d)) ((Prod.mk t) ⁻¹' ((ψ d) '' S)) ∂volume := by
      rw [Measure.prod_apply hT]
    _ = ∫⁻ (t : ℝ), Dμ d n {x : E d | insertLast d x t ∈ C} ∂(volume : Measure ℝ) := by
      refine lintegral_congr ?_
      intro t
      congr 1
      dsimp [S]
      exact peel_fiber (d := d) (n := n) hn (C := C) t


lemma Dμ_scale (d : ℕ) : ∀ (n : ℕ), n ≤ d →
    ∀ {C : Set (E d)}, MeasurableSet C → Convex ℝ C →
    ∀ (s : ℝ), 1 ≤ s →
    Dμ d n (s • C) ≥ ENNReal.ofReal (s ^ (d - n)) * Dμ d n C := by
  induction d with
  | zero =>
      intro n hn C hC hconv s hs1
      have hn0 : n = 0 := by omega
      subst n
      have hT := Dμ_torus_scale 0 hC hconv s hs1
      -- Dμ 0 0 (sC) ≥ Dμ 0 0 C ; exponent (0 - 0) = 0
      simpa using hT
  | succ d ih =>
      intro n hn C hC hconv s hs1
      by_cases hfull : n = d + 1
      · subst n
        have hT := Dμ_torus_scale (d+1) hC hconv s hs1
        -- exponent (d+1 - (d+1)) = 0
        simpa using hT
      · have hnle : n ≤ d := by omega
        have hs0 : s ≠ 0 := by linarith
        rw [Dμ_peel d n hnle hC]
        -- 1. peel sC
        have hpeel_sC := Dμ_peel d n hnle (smul_measurable (d := d+1) s hs0 hC)
        -- 2. sec of sC
        have hsec1 : ∀ t : ℝ, sec d (s • C) t = s • sec d C (s⁻¹ • t) := by
          intro t
          exact sec_smul C s hs0 t
        -- 3. pointwise IH
        have hpt : ∀ t : ℝ,
            Dμ d n (s • sec d C (s⁻¹ • t)) ≥
              ENNReal.ofReal (s ^ (d - n)) * Dμ d n (sec d C (s⁻¹ • t)) := by
          intro t
          exact ih n hnle (sec_measurable hC (s⁻¹ • t)) (sec_convex hconv (s⁻¹ • t)) s hs1
        -- assemble
        calc
          Dμ (d+1) n (s • C)
              = (∫⁻ (t : ℝ), Dμ d n (sec d (s • C) t) ∂(volume : Measure ℝ)) := hpeel_sC
          _ = (∫⁻ (t : ℝ), Dμ d n (s • sec d C (s⁻¹ • t)) ∂(volume : Measure ℝ)) := by
                refine lintegral_congr ?_
                intro t
                rw [hsec1 t]
          _ ≥ (∫⁻ (t : ℝ), ENNReal.ofReal (s ^ (d - n)) *
                Dμ d n (sec d C (s⁻¹ • t)) ∂(volume : Measure ℝ)) := by
                exact lintegral_mono hpt
          _ ≥ ENNReal.ofReal (s ^ (d - n)) *
              (∫⁻ (t : ℝ), Dμ d n (sec d C (s⁻¹ • t)) ∂(volume : Measure ℝ)) := by
                exact lintegral_const_mul_le (ENNReal.ofReal (s ^ (d - n)))
                  (fun t => Dμ d n (sec d C (s⁻¹ • t)))
          _ = ENNReal.ofReal (s ^ (d - n)) *
              (ENNReal.ofReal s * (∫⁻ (u : ℝ), Dμ d n (sec d C u) ∂(volume : Measure ℝ))) := by
                rw [Dμ_sec_sub d n hnle hC s hs1]
          _ = ENNReal.ofReal (s ^ (d + 1 - n)) *
              (∫⁻ (u : ℝ), Dμ d n (sec d C u) ∂(volume : Measure ℝ)) := by
                -- algebra: ofReal(s^{d-n})·ofReal(s) = ofReal(s^{d+1-n})
                have hpow : s ^ (d - n) * s = s ^ (d + 1 - n) := by
                  rw [← pow_succ]
                  congr 1
                  omega
                rw [← mul_assoc]
                rw [← ENNReal.ofReal_mul (pow_nonneg (by linarith : (0 : ℝ) ≤ s) (d - n))]
                rw [hpow]
        -- note: the ≥ direction in the last step needs = : rw of the peel as equality.


/-- the scaled body (a/2)•B satisfies the FoldFree condition at level i.val -/
lemma body_foldFree {d : ℕ} {B : Set (E d)} (hBconv : Convex ℝ B)
    (hBsym : ∀ x : E d, x ∈ B → -x ∈ B) {i : Fin d} {a : ℝ} (ha : 0 < a)
    (hPi : ∀ z : E d, IntFun d z → z ∈ a • B → ∀ j : Fin d, i.val ≤ j.val → z j = 0) :
    FoldFree d i.val ((a / 2) • B) := by
  intro x y hx hy hz1 hz2
  have hz : x - y ∈ a • B := by
    rcases hx with ⟨bx, hbx, hxeq⟩
    rcases hy with ⟨byp, hbyp, hyeq⟩
    have hneg : -byp ∈ B := hBsym byp hbyp
    have hmid : (1 / 2 : ℝ) • bx + (1 / 2 : ℝ) • (-byp) ∈ B := by
      exact hBconv hbx hneg (by norm_num) (by norm_num) (by norm_num)
    refine ⟨(1 / 2 : ℝ) • (bx - byp), ?_, ?_⟩
    · simpa [smul_sub, smul_neg, sub_eq_add_neg] using hmid
    · have heq : (fun z : E d => a • z) ((1 / 2 : ℝ) • (bx - byp)) = x - y := by
        calc (fun z : E d => a • z) ((1 / 2 : ℝ) • (bx - byp)) = a • ((1 / 2 : ℝ) • (bx - byp)) := rfl
        _ = (a / 2) • (bx - byp) := by
          rw [smul_smul]
          have hh : (a / 2 : ℝ) = a * (1 / 2 : ℝ) := by ring
          rw [hh]
        _ = (a / 2) • bx - (a / 2) • byp := by simp [smul_sub]
        _ = x - y := by
          change (fun z : E d => (a / 2) • z) bx - (fun z : E d => (a / 2) • z) byp = x - y
          rw [hxeq, hyeq]
      exact heq
  have hzint : IntFun d (x - y) := hz1.1
  have hL : Lzero d i.val (x - y) := by
    constructor
    · exact hzint
    · intro j hj
      exact hPi (x - y) hzint hz j hj
  exact False.elim (hz2 hL)

-- =====================================================================
--  Helper arithmetic lemmas (telescoping products, ofReal products)
-- =====================================================================

/-- telescoping: ∏_{j<n} (c(j+1)/c j) = c n / c 0 (for nonzero c) -/
lemma prod_ratio_telescope (n : ℕ) (c : ℕ → ℝ) (h0 : c 0 ≠ 0)
    (hnz : ∀ i, 0 < i → i ≤ n → c i ≠ 0) :
    (∏ j ∈ Finset.range n, (c (j + 1) / c j)) = c n / c 0 := by
  induction n with
  | zero =>
      simp
      field_simp [h0]
  | succ n ih =>
      have hih := ih (fun i hi hin => hnz i hi (by omega))
      have hc0 : c 0 ≠ 0 := h0
      have hcn : c n ≠ 0 := by
        by_cases hn0 : n = 0
        · subst n; exact h0
        · exact hnz n (Nat.pos_of_ne_zero hn0) (by omega)
      have hcn1 : c (n + 1) ≠ 0 := hnz (n+1) (by omega) (by omega)
      calc
        (∏ j ∈ Finset.range (n + 1), (c (j + 1) / c j))
            = (∏ j ∈ Finset.range n, (c (j + 1) / c j)) * (c (n + 1) / c n) := by
              rw [Finset.prod_range_succ]
        _ = (c n / c 0) * (c (n + 1) / c n) := by rw [hih]
        _ = c (n + 1) / c 0 := by
              field_simp [hc0, hcn, hcn1]

/-- ratio-power identity:
    (∏_{j<n} (c(j+1)/c j)^(n-j)) · c 0^(n+1) = ∏_{i<n+1} c i -/
lemma prod_ratio_pow (n : ℕ) (c : ℕ → ℝ) (h0 : c 0 ≠ 0)
    (hnz : ∀ i, 0 < i → i ≤ n + 1 → c i ≠ 0) :
    (∏ j ∈ Finset.range n, (c (j + 1) / c j) ^ (n - j)) * c 0 ^ (n + 1) =
      ∏ i ∈ Finset.range (n + 1), c i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hih := ih (fun i hi hin => hnz i hi (by omega))
      have hc0 : c 0 ≠ 0 := h0
      have hcn : c n ≠ 0 := by
        by_cases hn0 : n = 0
        · subst n; exact h0
        · exact hnz n (Nat.pos_of_ne_zero hn0) (by omega)
      have hcn1 : c (n + 1) ≠ 0 := hnz (n+1) (by omega) (by omega)
      have htel := prod_ratio_telescope n c h0 (fun i hi hin => hnz i hi (by omega))
      have hconvprod :
          (∏ j ∈ Finset.range (n + 1), (c (j + 1) / c j) ^ ((n + 1) - j)) =
            (∏ j ∈ Finset.range n, (c (j + 1) / c j) ^ (n - j)) *
            (∏ j ∈ Finset.range n, (c (j + 1) / c j)) * (c (n + 1) / c n) := by
        rw [Finset.prod_range_succ]
        have hnpow : (n + 1) - n = 1 := by omega
        rw [hnpow, pow_one]
        have hconv : (∏ j ∈ Finset.range n, (c (j + 1) / c j) ^ ((n + 1) - j)) =
            (∏ j ∈ Finset.range n, (c (j + 1) / c j) ^ (n - j) * (c (j + 1) / c j)) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          have hjlt : j < n := by simpa using hj
          have hpow : (n + 1) - j = (n - j) + 1 := by omega
          rw [hpow, pow_succ]
        rw [hconv]
        rw [Finset.prod_mul_distrib]
      calc
        (∏ j ∈ Finset.range (n + 1), (c (j + 1) / c j) ^ ((n + 1) - j)) * c 0 ^ ((n + 1) + 1)
            = (∏ j ∈ Finset.range n, (c (j + 1) / c j) ^ (n - j)) *
              (∏ j ∈ Finset.range n, (c (j + 1) / c j)) * (c (n + 1) / c n) * c 0 ^ (n + 2) := by
              rw [hconvprod]
        _ = (∏ j ∈ Finset.range n, (c (j + 1) / c j) ^ (n - j)) * c 0 ^ (n + 1) * c (n + 1) := by
              rw [htel]
              have h01 : c 0 ^ (n + 2) = c 0 ^ (n + 1) * c 0 := by ring
              rw [h01]
              field_simp [hc0, hcn, hcn1]
        _ = ∏ i ∈ Finset.range (n + 2), c i := by
              rw [hih]
              simp_rw [Finset.prod_range_succ]

/-- product of `ofReal` equals `ofReal` of the product (for nonnegative reals) -/
lemma ofReal_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (s.prod fun i => ENNReal.ofReal (f i)) = ENNReal.ofReal (s.prod f) := by
  classical
  have hmain : ∀ (s' : Finset ι), (∀ i ∈ s', 0 ≤ f i) →
      (s'.prod fun i => ENNReal.ofReal (f i)) = ENNReal.ofReal (s'.prod f) := by
    intro s'
    refine Finset.induction_on s' ?_ ?_
    · intro h
      simp [Finset.prod_empty]
    · intro a t hat ih hf'
      rw [Finset.prod_insert hat, Finset.prod_insert hat]
      rw [ENNReal.ofReal_mul (hf' a (Finset.mem_insert_self a t))]
      rw [← ih (fun i hi => hf' i (Finset.mem_insert_of_mem hi))]
  exact hmain s hf

/-- telescoped product of successive ratios, times the first-scale half-power,
    collapses to the full product divided by 2^d -/
lemma telescoped_prod_eq (d : ℕ) (hd : 0 < d) (b : ℕ → ℝ)
    (hb0 : b 0 ≠ 0) (hnz : ∀ i, 0 < i → i ≤ d → b i ≠ 0) :
    (∏ j ∈ Finset.range (d - 1), (b (j + 1) / b j) ^ (d - (j + 1))) * (b 0 / 2) ^ d
      = (∏ i ∈ Finset.range d, b i) / (2 : ℝ) ^ d := by
  have hd1 : (d - 1) + 1 = d := by omega
  have hpr := prod_ratio_pow (d - 1) b hb0 (fun i hi hin => hnz i hi (by omega))
  rw [hd1] at hpr
  have hexp : (∏ j ∈ Finset.range (d - 1), (b (j + 1) / b j) ^ ((d - 1) - j))
            = (∏ j ∈ Finset.range (d - 1), (b (j + 1) / b j) ^ (d - (j + 1))) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    have he : (d - 1) - j = d - (j + 1) := by omega
    rw [he]
  rw [hexp] at hpr
  have h2ne : (2 : ℝ) ^ d ≠ 0 := by positivity
  calc
    (∏ j ∈ Finset.range (d - 1), (b (j + 1) / b j) ^ (d - (j + 1))) * (b 0 / 2) ^ d
        = (∏ j ∈ Finset.range (d - 1), (b (j + 1) / b j) ^ (d - (j + 1))) * (b 0 ^ d / (2 : ℝ) ^ d) := by
            rw [div_pow]
    _ = ((∏ j ∈ Finset.range (d - 1), (b (j + 1) / b j) ^ (d - (j + 1))) * b 0 ^ d) / (2 : ℝ) ^ d := by
            rw [mul_div_assoc]
    _ = (∏ i ∈ Finset.range d, b i) / (2 : ℝ) ^ d := by
            rw [hpr]
theorem mink_engine (d : ℕ) (B : Set (E d)) (a : Fin d → ℝ)
    (hB_open : IsOpen B) (hB_convex : Convex ℝ B)
    (hB_symm : ∀ x : E d, x ∈ B → -x ∈ B)
    (hB_zero : (0 : E d) ∈ B) (hB_bdd : Bornology.IsBounded B)
    (ha_pos : ∀ i : Fin d, 0 < a i)
    (ha_mono : ∀ i : Fin d, ∀ j : Fin d, i.val ≤ j.val → a i ≤ a j)
    (hP : ∀ i : Fin d, ∀ z : E d, IntFun d z → z ∈ (a i) • B →
      ∀ j : Fin d, i.val ≤ j.val → z j = 0) :
    (∏ i : Fin d, a i) * (MeasureTheory.volume : Measure (E d)).real B ≤ (2 : ℝ) ^ d := by
  classical
  by_cases hd0 : d = 0
  · subst d
    have hBuniv : B = Set.univ := by
      ext x
      constructor <;> intro hx
      · trivial
      · have hx0 : x = (0 : E 0) := Subsingleton.elim x 0
        simpa [hx0] using hB_zero
    have hvol : (MeasureTheory.volume : Measure (E 0)).real B = 1 := by
      rw [hBuniv]
      have hfs : Fslab 0 0 = Set.univ := Fslab_d_zero 0
      rw [← hfs]
      have h1 : (MeasureTheory.volume : Measure (E 0)) (Fslab 0 0) = 1 := volume_Fslab_full 0
      rw [Measure.real_def]
      simp [h1]
    rw [hvol]
    have hprod : (∏ i : Fin 0, a i) = 1 := by simp
    rw [hprod]
    norm_num
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    -- extend the scale to all naturals (a on i<d, 1 beyond)
    let b : ℕ → ℝ := fun i => if h : i < d then a ⟨i, h⟩ else 1
    have hb_eq : ∀ (i : ℕ) (hi : i < d), b i = a ⟨i, hi⟩ := by
      intro i hi
      simp [b, hi]
    have hb_pos : ∀ i : ℕ, 0 < b i := by
      intro i
      by_cases hi : i < d
      · have hp := ha_pos ⟨i, hi⟩
        simpa [b, hi] using hp
      · simp [b, hi]
    have hb_ne : ∀ i : ℕ, b i ≠ 0 := fun i => ne_of_gt (hb_pos i)
    -- the scaled body at natural level i (no proof obligation in the index)
    let bodyN : ℕ → Set (E d) := fun i => (b i / 2) • B
    have hbodyN_meas : ∀ i : ℕ, MeasurableSet (bodyN i) := by
      intro i
      have hne : b i / 2 ≠ 0 := div_ne_zero (ne_of_gt (hb_pos i)) (by norm_num)
      dsimp [bodyN]
      exact smul_measurable (b i / 2) hne hB_open.measurableSet
    have hbodyN_conv : ∀ i : ℕ, Convex ℝ (bodyN i) := by
      intro i
      dsimp [bodyN]
      exact Convex.smul hB_convex (b i / 2)
    have hbodyN_free : ∀ (i : ℕ) (hi : i < d), FoldFree d i (bodyN i) := by
      intro i hi
      have hfree := body_foldFree hB_convex hB_symm (i := ⟨i, hi⟩) (a := a ⟨i, hi⟩)
        (ha_pos ⟨i, hi⟩) (hP ⟨i, hi⟩)
      simpa [bodyN, hb_eq i hi] using hfree
    let T : ℕ → ℝ≥0∞ := fun i => Dμ d i (bodyN i)
    let P : ℕ → ℝ≥0∞ := fun r =>
      ∏ j ∈ Finset.range r, ENNReal.ofReal ((b (j + 1) / b j) ^ (d - (j + 1)))
    have hchain : ∀ (r : ℕ), r < d → T r ≥ P r * T 0 := by
      intro r
      induction r with
      | zero =>
          intro h0
          simp [T, P]
      | succ r ih =>
          intro hsucc
          have hle_r : r < d := by omega
          have hmono_ratio : b r ≤ b (r + 1) := by
            rw [hb_eq r hle_r, hb_eq (r + 1) hsucc]
            exact ha_mono ⟨r, hle_r⟩ ⟨r + 1, hsucc⟩ (by
              change r ≤ r + 1
              omega)
          have hs : 1 ≤ b (r + 1) / b r := by
            rw [one_le_div (hb_pos r)]
            exact hmono_ratio
          have hscale := Dμ_scale d (r + 1) (by omega : r + 1 ≤ d)
            (hbodyN_meas r) (hbodyN_conv r) (b (r + 1) / b r) hs
          have hsbody : (b (r + 1) / b r) • bodyN r = bodyN (r + 1) := by
            dsimp [bodyN]
            ext z
            constructor
            · intro hz
              rcases hz with ⟨w, hw, hzw⟩
              rcases hw with ⟨u, hu, hwu⟩
              refine ⟨u, hu, ?_⟩
              calc (b (r + 1) / 2) • u = (b (r + 1) / b r) • ((b r / 2) • u) := by
                    rw [smul_smul]
                    congr 1
                    field_simp [hb_ne r]
                _ = z := by
                      have hwu' : (b r / 2) • u = w := by simpa using hwu
                      have hzw' : (b (r + 1) / b r) • w = z := by simpa using hzw
                      rw [hwu', hzw']
            · intro hz
              rcases hz with ⟨u, hu, hzu⟩
              refine ⟨(b r / 2) • u, ⟨u, hu, rfl⟩, ?_⟩
              calc (b (r + 1) / b r) • ((b r / 2) • u) = (b (r + 1) / 2) • u := by
                    rw [smul_smul]
                    congr 1
                    field_simp [hb_ne r]
                _ = z := hzu
          have hscale' : Dμ d (r + 1) (bodyN (r + 1)) ≥
              ENNReal.ofReal ((b (r + 1) / b r) ^ (d - (r + 1))) * Dμ d (r + 1) (bodyN r) := by
            rw [hsbody] at hscale
            simpa using hscale
          have hfold : Dμ d (r + 1) (bodyN r) = Dμ d r (bodyN r) := by
            exact Dμ_fold_eq (d := d) (n := r) hle_r (hbodyN_meas r) (hbodyN_free r hle_r)
          have hstep : T (r + 1) ≥
              ENNReal.ofReal ((b (r + 1) / b r) ^ (d - (r + 1))) * T r := by
            simpa [T, hfold] using hscale'
          have ih' := ih hle_r
          let Q : ℝ≥0∞ := ENNReal.ofReal ((b (r + 1) / b r) ^ (d - (r + 1)))
          have hPsucc : P (r + 1) = P r * Q := by
            dsimp [P, Q]
            rw [Finset.prod_range_succ]
          calc
            T (r + 1)
                ≥ Q * T r := by simpa [Q] using hstep
            _ ≥ Q * (P r * T 0) := by
                  exact IsOrderedMonoid.mul_le_mul_right (P r * T 0) (T r) ih' Q
            _ = P (r + 1) * T 0 := by
                  rw [hPsucc]
                  ac_rfl
    -- instantiate the chain at the top level d-1
    have hdminus : d - 1 < d := by omega
    have htop : T (d - 1) ≤ 1 := by
      have hfd := Dμ_fold_eq (d := d) (n := d - 1) (by omega : d - 1 < d)
        (hbodyN_meas (d - 1)) (hbodyN_free (d - 1) (by omega : d - 1 < d))
      have hd1n : (d - 1) + 1 = d := by omega
      rw [hd1n] at hfd
      have hle1 : Dμ d d (bodyN (d - 1)) ≤ 1 := Dμ_le_one d (bodyN (d - 1))
      calc T (d - 1) = Dμ d (d - 1) (bodyN (d - 1)) := by rfl
        _ = Dμ d d (bodyN (d - 1)) := hfd.symm
        _ ≤ 1 := hle1
    have hT0 : T 0 = ENNReal.ofReal ((b 0 / 2) ^ d) * (volume : Measure (E d)) B := by
      have hb0pos : 0 ≤ b 0 / 2 := le_of_lt (div_pos (hb_pos 0) (by norm_num))
      have hlv := vol_smul_haar d (C := B) (b 0 / 2) hb0pos
      calc T 0 = Dμ d 0 (bodyN 0) := by rfl
        _ = (volume : Measure (E d)) (bodyN 0) := Dμ_level_zero d (hbodyN_meas 0)
        _ = (volume : Measure (E d)) ((b 0 / 2) • B) := by rfl
        _ = ENNReal.ofReal ((b 0 / 2) ^ d) * (volume : Measure (E d)) B := hlv
    let volB : ℝ≥0∞ := (volume : Measure (E d)) B
    have hvol_le : (P (d - 1) * ENNReal.ofReal ((b 0 / 2) ^ d)) * volB ≤ 1 := by
      have hPT : P (d - 1) * T 0 ≤ T (d - 1) := hchain (d - 1) hdminus
      calc (P (d - 1) * ENNReal.ofReal ((b 0 / 2) ^ d)) * volB
          = P (d - 1) * T 0 := by
              dsimp [volB]
              rw [hT0]
              ac_rfl
        _ ≤ T (d - 1) := hPT
        _ ≤ 1 := htop
    -- fuse the ENNReal product into a single ofReal
    let realprod : ℝ :=
      (∏ j ∈ Finset.range (d - 1), (b (j + 1) / b j) ^ (d - (j + 1))) * (b 0 / 2) ^ d
    have hratio_nonneg : ∀ i : ℕ, 0 ≤ (b (i + 1) / b i) ^ (d - (i + 1)) := by
      intro i
      exact pow_nonneg (div_nonneg (le_of_lt (hb_pos (i + 1))) (le_of_lt (hb_pos i))) (d - (i + 1))
    have hPof : P (d - 1) =
        ENNReal.ofReal (∏ j ∈ Finset.range (d - 1), (b (j + 1) / b j) ^ (d - (j + 1))) := by
      dsimp [P]
      rw [ofReal_prod (Finset.range (d - 1)) (fun j => (b (j + 1) / b j) ^ (d - (j + 1)))
        (fun i hi => hratio_nonneg i)]
    have hb0pow_nonneg : 0 ≤ (b 0 / 2) ^ d := pow_nonneg (div_nonneg (le_of_lt (hb_pos 0)) (by norm_num)) d
    have hFuse : P (d - 1) * ENNReal.ofReal ((b 0 / 2) ^ d) = ENNReal.ofReal realprod := by
      dsimp [realprod]
      calc P (d - 1) * ENNReal.ofReal ((b 0 / 2) ^ d)
          = ENNReal.ofReal (∏ j ∈ Finset.range (d - 1), (b (j + 1) / b j) ^ (d - (j + 1))) *
              ENNReal.ofReal ((b 0 / 2) ^ d) := by rw [hPof]
      _ = ENNReal.ofReal ((∏ j ∈ Finset.range (d - 1), (b (j + 1) / b j) ^ (d - (j + 1))) * (b 0 / 2) ^ d) := by
            exact (ENNReal.ofReal_mul (Finset.prod_nonneg (fun i hi => hratio_nonneg i))).symm
    have hrealprod : realprod = (∏ i ∈ Finset.range d, b i) / (2 : ℝ) ^ d := by
      dsimp [realprod]
      exact telescoped_prod_eq d hdpos b (hb_ne 0) (fun i hi hle => hb_ne i)
    have hbprod : (∏ i ∈ Finset.range d, b i) = ∏ i : Fin d, a i := by
      rw [← Finset.prod_fin_eq_prod_range (n := d) (c := a)]
    let X : ℝ := (∏ i : Fin d, a i) / (2 : ℝ) ^ d
    have hFuse2 : P (d - 1) * ENNReal.ofReal ((b 0 / 2) ^ d) = ENNReal.ofReal X := by
      calc P (d - 1) * ENNReal.ofReal ((b 0 / 2) ^ d) = ENNReal.ofReal realprod := hFuse
        _ = ENNReal.ofReal ((∏ i ∈ Finset.range d, b i) / (2 : ℝ) ^ d) := by rw [hrealprod]
        _ = ENNReal.ofReal X := by
              dsimp [X]
              rw [hbprod]
    have hE : ENNReal.ofReal X * volB ≤ 1 := by
      calc ENNReal.ofReal X * volB
          = (P (d - 1) * ENNReal.ofReal ((b 0 / 2) ^ d)) * volB := by rw [← hFuse2]
        _ ≤ 1 := hvol_le
    -- real-side conversion
    have hvol_lt : volB < ∞ := by
      dsimp [volB]
      rcases hB_bdd.subset_closedBall (0 : E d) with ⟨r, hsub⟩
      have hlt : (volume : Measure (E d)) (Metric.closedBall (0 : E d) r) < ∞ :=
        measure_closedBall_lt_top (μ := (volume : Measure (E d))) (x := (0 : E d)) (r := r)
      exact lt_of_le_of_lt (measure_mono hsub) hlt
    have hvol_ne : volB ≠ ∞ := ne_of_lt hvol_lt
    have h2pos : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) d
    have h2nonneg : 0 ≤ (2 : ℝ) ^ d := le_of_lt h2pos
    have h2ne : (2 : ℝ) ^ d ≠ 0 := ne_of_gt h2pos
    have hXnonneg : 0 ≤ X := by
      dsimp [X]
      exact div_nonneg (le_of_lt (Finset.prod_pos (fun i hi => ha_pos i))) h2nonneg
    have hEtoReal : X * volB.toReal ≤ 1 := by
      have hfin : ENNReal.ofReal X * volB ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol_ne
      have hconv := (ENNReal.toReal_le_toReal hfin (by simp : (1 : ℝ≥0∞) ≠ ∞)).mpr hE
      have hcalc : (ENNReal.ofReal X * volB).toReal = X * volB.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hXnonneg]
      simpa [hcalc] using hconv
    have hL : (X * volB.toReal) * (2 : ℝ) ^ d = (∏ i : Fin d, a i) * volB.toReal := by
      dsimp [X]
      field_simp [h2ne]
    have hmul := mul_le_mul_of_nonneg_right hEtoReal h2nonneg
    have hR : (∏ i : Fin d, a i) * volB.toReal ≤ (2 : ℝ) ^ d := by
      calc (∏ i : Fin d, a i) * volB.toReal = (X * volB.toReal) * (2 : ℝ) ^ d := hL.symm
        _ ≤ 1 * (2 : ℝ) ^ d := hmul
        _ = (2 : ℝ) ^ d := by ring
    rw [Measure.real_def]
    simpa [volB] using hR

end Submission.MinkEngine
