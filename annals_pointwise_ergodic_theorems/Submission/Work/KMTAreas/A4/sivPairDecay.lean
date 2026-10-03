import Mathlib
import Submission.Work.KMTAreas.A4.memLp_two_count_summable_norm_sq
import Submission.Work.KMTAreas.A4.sivOffDecayHalfLine
import Submission.Work.KMTAreas.A4.eLpNorm_ahalfTranspose_le_of_bdd
import Submission.Work.KMTAreas.A4.sivBlocksGeom
import Submission.Work.KMTAreas.A4.sivPairingCS
import Submission.Work.KMTAreas.A4.sivDecayArith
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory
open Work.Analysis.IonescuWainger (GoodMajorArcs)
open Work.Analysis.EndVar (logN)
open Work.KMTContract

/-! ## Elementary real arithmetic -/

/-- The arithmetic of the geometric mean: for non-negative reals `A`, `B`,
`min (A * A) B ≤ A * √B`. -/
lemma min_sq_le_sqrt_mul {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    min (A * A) B ≤ A * Real.sqrt B := by
  rcases le_total (A * A) B with h | h
  · rw [min_eq_left h]
    have h1 : A ≤ Real.sqrt B := by
      have h2 : Real.sqrt (A ^ 2) ≤ Real.sqrt B := Real.sqrt_le_sqrt (by simpa [sq] using h)
      rwa [Real.sqrt_sq hA] at h2
    exact mul_le_mul_of_nonneg_left h1 hA
  · rw [min_eq_right h]
    have h1 : Real.sqrt B ≤ A := by
      have h2 : Real.sqrt B ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt (by simpa [sq] using h)
      rwa [Real.sqrt_sq hA] at h2
    calc B = Real.sqrt B ^ 2 := (Real.sq_sqrt hB).symm
      _ ≤ A * Real.sqrt B := by nlinarith [h1, Real.sqrt_nonneg B]

/-- The square root of `x ^ (-(M : ℝ))` is `(√x) ^ (-(M : ℝ))`. -/
lemma sqrt_rpow_neg_eq (x : ℝ) (hx : 0 ≤ x) (M : ℕ) :
    Real.sqrt (x ^ (-(M : ℝ))) = (Real.sqrt x) ^ (-(M : ℝ)) := by
  have h1 : Real.sqrt (x ^ (-(M : ℝ))) = x ^ ((-(M : ℝ)) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  have h2 : (Real.sqrt x) ^ (-(M : ℝ)) = x ^ ((1 / 2) * (-(M : ℝ))) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  rw [h1, h2]
  congr 1
  ring

/-- `√(max l 1) ≤ (max l 1) ^ M` for `1 ≤ M`. -/
lemma sqrt_max_one_le_pow (l M : ℕ) (hM : 1 ≤ M) :
    Real.sqrt (max ((l : ℝ)) 1) ≤ (max ((l : ℝ)) 1) ^ M := by
  set z : ℝ := max ((l : ℝ)) 1 with hz
  have h1 : (1 : ℝ) ≤ z := le_max_right _ _
  have h0 : 0 ≤ z := le_trans zero_le_one h1
  calc Real.sqrt z ≤ Real.sqrt (z * z) := Real.sqrt_le_sqrt (by nlinarith)
    _ = z := Real.sqrt_mul_self h0
    _ ≤ z ^ M := le_self_pow₀ h1 (by omega)

/-- Subadditivity of the square root for three non-negative terms. -/
lemma sqrt_add_three_le {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x + y + z) ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
  have h : x + y + z ≤ (Real.sqrt x + Real.sqrt y + Real.sqrt z) ^ 2 := by
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hy
    have h3 := Real.sq_sqrt hz
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z]
  calc Real.sqrt (x + y + z)
      ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y + Real.sqrt z) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y + Real.sqrt z := Real.sqrt_sq (by positivity)

/-- Hölder's inequality for the pairing against the conjugate, at exponents `2, 2, 1`. -/
lemma eLpNorm_mul_star_le (f g : ℤ → ℂ) :
    eLpNorm (fun x : ℤ => f x * star (g x)) 1 (Measure.count : Measure ℤ)
      ≤ eLpNorm f 2 (Measure.count : Measure ℤ) * eLpNorm g 2 (Measure.count : Measure ℤ) := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := (Measure.count : Measure ℤ))
    (p := 2) (q := 2) (r := 1) (f := f) (g := star g)
    (fun a b : ℂ => a * b) 1 (by first | fun_prop | exact continuous_mul | exact continuous_inner | (simp only [Function.uncurry_def]; fun_prop)) ((measurable_of_countable f).aestronglyMeasurable) ((measurable_of_countable (star g)).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => by
      show ‖f x * (star g) x‖₊ ≤ (1 : ℝ≥0) * ‖f x‖₊ * ‖(star g) x‖₊
      rw [nnnorm_mul, one_mul])
  rw [eLpNorm_star] at h
  simpa using h

/-! ## The single-block estimates -/

/-- A block piece of an `ℓ²` function is in `ℓ²`. -/
lemma memLp_blkPiece (P : Polynomial ℤ) (N : ℕ) {g : ℤ → ℂ}
    (hg : MemLp g 2 (Measure.count : Measure ℤ)) (i : ℤ) :
    MemLp (blkPiece P N g i) 2 (Measure.count : Measure ℤ) := by
  refine MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt ?_ hg.eLpNorm_lt_top)
  refine eLpNorm_mono (hf := by pw_aesm) fun x => ?_
  by_cases hx : i * (blkLen P N : ℤ) ≤ x ∧ x < (i + 1) * (blkLen P N : ℤ)
  · rw [blkPiece, if_pos hx]
  · rw [blkPiece, if_neg hx, norm_zero]
    exact norm_nonneg _

/-- The `ℒ²` seminorm of a block piece is its `ℓ²` norm. -/
lemma eLpNorm_blkPiece (P : Polynomial ℤ) (N : ℕ) {g : ℤ → ℂ}
    (hg : MemLp g 2 (Measure.count : Measure ℤ)) (i : ℤ) :
    eLpNorm (blkPiece P N g i) 2 (Measure.count : Measure ℤ)
      = ENNReal.ofReal (l2norm (blkPiece P N g i)) :=
  eLpNorm_two_eq_ofReal_l2norm (memLp_two_count_summable_norm_sq (memLp_blkPiece P N hg i))

/-- The local dual function of the `i`-th block is the first dual function of the block piece. -/
lemma blkDual_eq (P : Polynomial ℤ) (hP : 1 ≤ P.natDegree) (N : ℕ) (hN : 1 ≤ N)
    (h g : ℤ → ℂ) (i : ℤ) :
    blkDual P N h g i = AhalfTranspose N P h (blkPiece P N g i) :=
  (sivBlocksGeom P hP N hN).2.2.2.2.2.2 h g i

/-- The support of the local dual function of a block. -/
lemma blkDual_supp (P : Polynomial ℤ) (hP : 1 ≤ P.natDegree) (N : ℕ) (hN : 1 ≤ N)
    (h g : ℤ → ℂ) (i x : ℤ) (hx : blkDual P N h g i x ≠ 0) :
    blkAlpha P N i ≤ x ∧ x ≤ blkBeta P N i :=
  (sivBlocksGeom P hP N hN).2.2.2.2.2.1 h g i x hx

/-- The local dual function is in `ℓ²`. -/
lemma memLp_blkDual (P : Polynomial ℤ) (hP : 1 ≤ P.natDegree) (N : ℕ) (hN : 1 ≤ N)
    {h g : ℤ → ℂ} (hg : MemLp g 2 (Measure.count : Measure ℤ)) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1)
    (i : ℤ) : MemLp (blkDual P N h g i) 2 (Measure.count : Measure ℤ) := by
  have hle : eLpNorm (blkDual P N h g i) 2 (Measure.count : Measure ℤ)
      ≤ eLpNorm (blkPiece P N g i) 2 (Measure.count : Measure ℤ) := by
    rw [blkDual_eq P hP N hN h g i]
    exact eLpNorm_ahalfTranspose_le_of_bdd N P hh
  exact MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hle (by rw [eLpNorm_blkPiece P N hg i]; exact ENNReal.ofReal_lt_top))

/-- The `ℒ²` seminorm of the local dual function of a block is at most the `ℓ²` norm of the
block piece. -/
lemma eLpNorm_blkDual_le (P : Polynomial ℤ) (hP : 1 ≤ P.natDegree) (N : ℕ) (hN : 1 ≤ N)
    {h g : ℤ → ℂ} (hg : MemLp g 2 (Measure.count : Measure ℤ)) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1)
    (i : ℤ) :
    eLpNorm (blkDual P N h g i) 2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (l2norm (blkPiece P N g i)) := by
  rw [blkDual_eq P hP N hN h g i]
  exact (eLpNorm_ahalfTranspose_le_of_bdd N P hh).trans
    (le_of_eq (eLpNorm_blkPiece P N hg i))

/-! ## The off-diagonal decay in the normalised form used below -/

/-- The left half-line off-diagonal decay with the constant and the height factor folded into a
single `ofReal`; the caller supplies the numerical bound `F` on the decay factor. -/
lemma offDecay_left_norm {ρ Cρ : ℝ} {Cnn : ℝ≥0} {M : ℕ}
    (hleft : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → ∀ (a b c : ℤ) (f : ℤ → ℂ), c < a →
      (∀ x : ℤ, x < a ∨ b < x → f x = 0) → MemLp f 2 (Measure.count : Measure ℤ) →
      eLpNorm (fun x : ℤ => if x ≤ c then kmtProj ρ l k f x else 0)
          2 (Measure.count : Measure ℤ)
        ≤ (Cnn : ENNReal) * ENNReal.ofReal (max ((l : ℝ)) 1 *
              (max ((2 : ℝ) ^ k * ((a - c : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
          eLpNorm f 2 (Measure.count : Measure ℤ))
    {l : ℕ} {k : ℤ} (hGA : GoodMajorArcs ρ Cρ l k) {a b c : ℤ} {f : ℤ → ℂ} {F : ℝ}
    (hF : max ((l : ℝ)) 1 * (max ((2 : ℝ) ^ k * ((a - c : ℤ) : ℝ)) 1) ^ (-(M : ℝ)) ≤ F)
    (hca : c < a) (hf : ∀ x : ℤ, x < a ∨ b < x → f x = 0)
    (hmem : MemLp f 2 (Measure.count : Measure ℤ)) :
    eLpNorm (fun x : ℤ => if x ≤ c then kmtProj ρ l k f x else 0)
        2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal ((Cnn : ℝ) * F) * eLpNorm f 2 (Measure.count : Measure ℤ) := by
  have h := hleft l k hGA a b c f hca hf hmem
  simp only [← ENNReal.ofReal_coe_nnreal] at h
  have h2 : ENNReal.ofReal (max ((l : ℝ)) 1 *
        (max ((2 : ℝ) ^ k * ((a - c : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) ≤ ENNReal.ofReal F :=
    ENNReal.ofReal_le_ofReal hF
  calc eLpNorm (fun x : ℤ => if x ≤ c then kmtProj ρ l k f x else 0)
        2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (Cnn : ℝ) * ENNReal.ofReal (max ((l : ℝ)) 1 *
            (max ((2 : ℝ) ^ k * ((a - c : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
          eLpNorm f 2 (Measure.count : Measure ℤ) := h
    _ ≤ ENNReal.ofReal (Cnn : ℝ) * ENNReal.ofReal F * eLpNorm f 2 (Measure.count : Measure ℤ) :=
        mul_le_mul' (mul_le_mul' le_rfl h2) le_rfl
    _ = ENNReal.ofReal ((Cnn : ℝ) * F) * eLpNorm f 2 (Measure.count : Measure ℤ) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Cnn : ℝ))]

/-- The right half-line off-diagonal decay in the normalised form used below. -/
lemma offDecay_right_norm {ρ Cρ : ℝ} {Cnn : ℝ≥0} {M : ℕ}
    (hright : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → ∀ (a b c : ℤ) (f : ℤ → ℂ), b < c →
      (∀ x : ℤ, x < a ∨ b < x → f x = 0) →
      eLpNorm (fun x : ℤ => if c ≤ x then kmtProj ρ l k f x else 0)
          2 (Measure.count : Measure ℤ)
        ≤ (Cnn : ENNReal) * ENNReal.ofReal (max ((l : ℝ)) 1 *
              (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
          eLpNorm f 2 (Measure.count : Measure ℤ))
    {l : ℕ} {k : ℤ} (hGA : GoodMajorArcs ρ Cρ l k) {a b c : ℤ} {f : ℤ → ℂ} {F : ℝ}
    (hF : max ((l : ℝ)) 1 * (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M : ℝ)) ≤ F)
    (hbc : b < c) (hf : ∀ x : ℤ, x < a ∨ b < x → f x = 0) :
    eLpNorm (fun x : ℤ => if c ≤ x then kmtProj ρ l k f x else 0)
        2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal ((Cnn : ℝ) * F) * eLpNorm f 2 (Measure.count : Measure ℤ) := by
  have h := hright l k hGA a b c f hbc hf
  simp only [← ENNReal.ofReal_coe_nnreal] at h
  have h2 : ENNReal.ofReal (max ((l : ℝ)) 1 *
        (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) ≤ ENNReal.ofReal F :=
    ENNReal.ofReal_le_ofReal hF
  calc eLpNorm (fun x : ℤ => if c ≤ x then kmtProj ρ l k f x else 0)
        2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (Cnn : ℝ) * ENNReal.ofReal (max ((l : ℝ)) 1 *
            (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
          eLpNorm f 2 (Measure.count : Measure ℤ) := h
    _ ≤ ENNReal.ofReal (Cnn : ℝ) * ENNReal.ofReal F * eLpNorm f 2 (Measure.count : Measure ℤ) :=
        mul_le_mul' (mul_le_mul' le_rfl h2) le_rfl
    _ = ENNReal.ofReal ((Cnn : ℝ) * F) * eLpNorm f 2 (Measure.count : Measure ℤ) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Cnn : ℝ))]

/-- **Pair decay of the minor-arc parts of the local dual functions.**  This is the "Schur test"
step in the proof of Corollary `siv` of Krause--Mirek--Tao (§5.1): the correlation of the
minor-arc parts of the local dual functions of two blocks at distance at least `2` decays like
the `(-M/2)`-th power of the block distance (up to the height factor `⟨l⟩^M`). -/
theorem sivPairDecay (P : Polynomial ℤ) (hP : 1 ≤ P.natDegree) {ρ : ℝ} (hOff : Work.KMTAreas.A4.OffDecayClaim ρ) {M : ℕ} (hM : 2 < M) : ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ K : ℝ, 0 < K ∧ ∀ (N l : ℕ) (A : ℝ) (h g : ℤ → ℂ), 1 ≤ N → 0 ≤ A → (∀ x : ℤ, ‖h x‖ ≤ 1) → MeasureTheory.MemLp g 2 MeasureTheory.Measure.count → Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l ((l : ℤ) - Work.Analysis.EndVar.logN N) → (∀ i : ℤ, MeasureTheory.eLpNorm (Work.KMTAreas.A4.blkE P N ρ l h g i) (2 : ENNReal) MeasureTheory.Measure.count ≤ ENNReal.ofReal (A * Work.KMTAreas.A4.l2norm (Work.KMTAreas.A4.blkPiece P N g i))) → ∀ i j : ℤ, i + 2 ≤ j → ‖∑' x : ℤ, Work.KMTAreas.A4.blkE P N ρ l h g i x * star (Work.KMTAreas.A4.blkE P N ρ l h g j x)‖ ≤ K * A * (max ((l : ℝ)) 1) ^ M * (max 1 (((j - i : ℤ)) : ℝ)) ^ (-((M : ℝ) / 2)) * Work.KMTAreas.A4.l2norm (Work.KMTAreas.A4.blkPiece P N g i) * Work.KMTAreas.A4.l2norm (Work.KMTAreas.A4.blkPiece P N g j) := by
  obtain ⟨Cρ, hCρ, Cnn, hCnn, hright, hleft⟩ := sivOffDecayHalfLine ρ M hOff
  obtain ⟨Kar, hKar, har⟩ := sivDecayArith M hM
  set Co : ℝ := (Cnn : ℝ) with hCo
  have hCo0 : 0 < Co := by rw [hCo]; exact_mod_cast hCnn
  have hCo0' : 0 ≤ Co := le_of_lt hCo0
  refine ⟨Cρ, hCρ, 3 * Kar * Real.sqrt Co + 3 * Co * (Kar + 1) ^ 2 + 1, ?_, ?_⟩
  · have h1 : 0 ≤ 3 * Kar * Real.sqrt Co := by positivity
    have h2 : 0 ≤ 3 * Co * (Kar + 1) ^ 2 := by positivity
    linarith
  intro N l A h g hN hA hh hg hGA hE i j hij
  -- ## abbreviations
  set ai : ℝ := l2norm (blkPiece P N g i) with hai
  set aj : ℝ := l2norm (blkPiece P N g j) with haj
  have hai0 : 0 ≤ ai := by rw [hai]; exact l2norm_nonneg _
  have haj0 : 0 ≤ aj := by rw [haj]; exact l2norm_nonneg _
  set u : ℤ → ℂ := blkDual P N h g i with hu
  set v : ℤ → ℂ := blkDual P N h g j with hv
  set Eu : ℤ → ℂ := blkE P N ρ l h g i with hEu
  set Ev : ℤ → ℂ := blkE P N ρ l h g j with hEv
  have hEu_eq : Eu = u - kmtProj ρ l ((l : ℤ) - logN N) u := by rw [hEu, hu, blkE, blkProj]
  have hEv_eq : Ev = v - kmtProj ρ l ((l : ℤ) - logN N) v := by rw [hEv, hv, blkE, blkProj]
  -- ## geometry
  have hgapij : (j - i) * (N : ℤ) ^ P.natDegree ≤ blkAlpha P N j - blkBeta P N i :=
    (sivBlocksGeom P hP N hN).2.2.2.2.1 i j hij
  have hNpow1 : (1 : ℤ) ≤ (N : ℤ) ^ P.natDegree := by
    have h1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    exact one_le_pow₀ h1
  have hm2 : (2 : ℤ) ≤ j - i := by omega
  have hdel2 : (2 : ℤ) ≤ blkAlpha P N j - blkBeta P N i := by
    have h3 : (2 : ℤ) ≤ (j - i) * (N : ℤ) ^ P.natDegree := by nlinarith
    linarith
  have hβiαj : blkBeta P N i < blkAlpha P N j := by linarith
  set βi : ℤ := blkBeta P N i with hβi
  set αj : ℤ := blkAlpha P N j with hαj
  have hβlt : βi < αj := by rw [hβi, hαj]; exact hβiαj
  have hδge : (j - i) * (N : ℤ) ^ P.natDegree ≤ αj - βi := by rw [hβi, hαj]; exact hgapij
  have hδα : (2 : ℤ) ≤ αj - βi := by rw [hβi, hαj]; exact hdel2
  set d : ℤ := (αj - βi) / 2 with hd
  set m : ℤ := βi + d with hm
  have hd1 : 1 ≤ d := by rw [hd]; omega
  have hmgt : βi < m := by rw [hm]; omega
  have hmlt : m < αj := by rw [hm, hd]; omega
  have hmd1 : 4 * d ≥ αj - βi := by rw [hd]; omega
  have hmd2 : 4 * (αj - m) ≥ αj - βi := by rw [hm, hd]; omega
  -- ## supports
  have hsupp_u : ∀ x : ℤ, x < blkAlpha P N i ∨ blkBeta P N i < x → u x = 0 := by
    intro x hx
    rw [hu]
    by_contra hne
    have hmem := blkDual_supp P hP N hN h g i x hne
    rcases hx with hx | hx <;> omega
  have hsupp_v : ∀ x : ℤ, x < blkAlpha P N j ∨ blkBeta P N j < x → v x = 0 := by
    intro x hx
    rw [hv]
    by_contra hne
    have hmem := blkDual_supp P hP N hN h g j x hne
    rcases hx with hx | hx <;> omega
  -- ## MemLp and norm bounds
  have hUmem : MemLp u 2 (Measure.count : Measure ℤ) := by
    rw [hu]; exact memLp_blkDual P hP N hN hg hh i
  have hVmem : MemLp v 2 (Measure.count : Measure ℤ) := by
    rw [hv]; exact memLp_blkDual P hP N hN hg hh j
  have hu_le : eLpNorm u 2 (Measure.count : Measure ℤ) ≤ ENNReal.ofReal ai := by
    rw [hu, hai]; exact eLpNorm_blkDual_le P hP N hN hg hh i
  have hv_le : eLpNorm v 2 (Measure.count : Measure ℤ) ≤ ENNReal.ofReal aj := by
    rw [hv, haj]; exact eLpNorm_blkDual_le P hP N hN hg hh j
  have hEu_le : eLpNorm Eu 2 (Measure.count : Measure ℤ) ≤ ENNReal.ofReal (A * ai) := by
    rw [hEu, hai]; exact hE i
  have hEv_le : eLpNorm Ev 2 (Measure.count : Measure ℤ) ≤ ENNReal.ofReal (A * aj) := by
    rw [hEv, haj]; exact hE j
  -- ## the real scale parameters
  set Ll : ℝ := max ((l : ℝ)) 1 with hLl
  have hLl1 : 1 ≤ Ll := by rw [hLl]; exact le_max_right _ _
  have hLl0 : 0 ≤ Ll := le_trans zero_le_one hLl1
  set y : ℝ := ((j - i : ℤ) : ℝ) with hy
  have hy2 : 2 ≤ y := by rw [hy]; exact_mod_cast hm2
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 ≤ y := le_trans zero_le_one hy1
  set X1 : ℝ := max ((2 : ℝ) ^ ((l : ℤ) - logN N) * (((blkAlpha P N j - βi : ℤ)) : ℝ)) 1 with hX1
  set X2 : ℝ := max ((2 : ℝ) ^ ((l : ℤ) - logN N) * (((blkAlpha P N j - m : ℤ)) : ℝ)) 1 with hX2
  set X3 : ℝ := max ((2 : ℝ) ^ ((l : ℤ) - logN N) * (((m - blkBeta P N i : ℤ)) : ℝ)) 1 with hX3
  have hX1pos : 0 < X1 := lt_of_lt_of_le zero_lt_one (by rw [hX1]; exact le_max_right _ _)
  have hX2pos : 0 < X2 := lt_of_lt_of_le zero_lt_one (by rw [hX2]; exact le_max_right _ _)
  have hX3pos : 0 < X3 := lt_of_lt_of_le zero_lt_one (by rw [hX3]; exact le_max_right _ _)
  -- ## the arithmetic of `2 ^ k`, `N ^ d` and the block gap
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNpowR : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ hNge1
  have hNlepow : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (N : ℝ) ^ P.natDegree := pow_le_pow_right₀ hNge1 hP
  have hlogN : (2 : ℝ) ^ (logN N) ≤ 2 * (N : ℝ) := by
    have h1 : (2 : ℕ) ^ Nat.log 2 (max N 2) ≤ 2 * N := by
      have h2 : (2 : ℕ) ^ Nat.log 2 (max N 2) ≤ max N 2 := Nat.pow_log_le_self 2 (by omega)
      have h3 : max N 2 ≤ 2 * N := by omega
      omega
    rw [logN, zpow_natCast]
    exact_mod_cast h1
  have h2klb : (1 : ℝ) / (2 * (N : ℝ)) ≤ (2 : ℝ) ^ ((l : ℤ) - logN N) := by
    have h1 : (0 : ℝ) < (2 : ℝ) ^ (logN N) := zpow_pos (by norm_num) _
    have h2 : (1 : ℝ) / (2 * (N : ℝ)) ≤ (1 : ℝ) / ((2 : ℝ) ^ (logN N)) :=
      one_div_le_one_div_of_le h1 hlogN
    have h3 : (1 : ℝ) / ((2 : ℝ) ^ (logN N)) ≤ (2 : ℝ) ^ ((l : ℤ) - logN N) := by
      rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0) (l : ℤ) (logN N), div_eq_mul_inv, div_eq_mul_inv]
      have hl : (1 : ℝ) ≤ (2 : ℝ) ^ (l : ℤ) := by
        have h0 : (0 : ℤ) ≤ (l : ℤ) := by positivity
        calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) := (zpow_zero 2).symm
          _ ≤ (2 : ℝ) ^ (l : ℤ) := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h0
      have hpos : (0 : ℝ) < ((2 : ℝ) ^ (logN N))⁻¹ := inv_pos.mpr h1
      nlinarith [hl, hpos]
    linarith
  have hkey : (1 : ℝ) / (2 * (N : ℝ)) * (N : ℝ) ^ P.natDegree ≥ 1 / 2 := by
    have h3 : (1 : ℝ) / (2 * (N : ℝ)) * (N : ℝ) ^ P.natDegree
        = (N : ℝ) ^ P.natDegree / (2 * (N : ℝ)) := by
      rw [one_div, inv_mul_eq_div]
    rw [h3, ge_iff_le, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ))]
    linarith [hNlepow]
  have hX1y : y / 16 ≤ X1 := by
    rw [hX1]
    refine le_trans ?_ (le_max_left _ _)
    have hδz : y * (N : ℝ) ^ P.natDegree ≤ (((blkAlpha P N j - βi : ℤ)) : ℝ) := by
      rw [hy]; exact_mod_cast hδge
    have hstep1 : (1 : ℝ) / (2 * (N : ℝ)) * (y * (N : ℝ) ^ P.natDegree)
        ≤ (2 : ℝ) ^ ((l : ℤ) - logN N) * (((blkAlpha P N j - βi : ℤ)) : ℝ) := by
      calc (1 : ℝ) / (2 * (N : ℝ)) * (y * (N : ℝ) ^ P.natDegree)
          ≤ (2 : ℝ) ^ ((l : ℤ) - logN N) * (y * (N : ℝ) ^ P.natDegree) :=
            mul_le_mul_of_nonneg_right h2klb (by positivity)
        _ ≤ (2 : ℝ) ^ ((l : ℤ) - logN N) * (((blkAlpha P N j - βi : ℤ)) : ℝ) :=
            mul_le_mul_of_nonneg_left hδz (le_of_lt (zpow_pos (by norm_num) _))
    have hstep2 : y / 16 ≤ (1 : ℝ) / (2 * (N : ℝ)) * (y * (N : ℝ) ^ P.natDegree) := by
      nlinarith [hkey, hy1]
    linarith
  have hX2y : y / 16 ≤ X2 := by
    rw [hX2]
    refine le_trans ?_ (le_max_left _ _)
    have hδz : y * (N : ℝ) ^ P.natDegree ≤ (((blkAlpha P N j - βi : ℤ)) : ℝ) := by
      rw [hy]; exact_mod_cast hδge
    have h4 : (((blkAlpha P N j - βi : ℤ)) : ℝ) ≤ 4 * (((αj - m : ℤ)) : ℝ) := by
      have h5 : (blkAlpha P N j - βi) ≤ 4 * (αj - m) := by
        rw [← hαj]; exact hmd2
      exact_mod_cast h5
    have hstep1 : (1 : ℝ) / (2 * (N : ℝ)) * (y * (N : ℝ) ^ P.natDegree / 4)
        ≤ (2 : ℝ) ^ ((l : ℤ) - logN N) * (((αj - m : ℤ)) : ℝ) := by
      have h6 : y * (N : ℝ) ^ P.natDegree / 4 ≤ (((αj - m : ℤ)) : ℝ) := by linarith
      calc (1 : ℝ) / (2 * (N : ℝ)) * (y * (N : ℝ) ^ P.natDegree / 4)
          ≤ (2 : ℝ) ^ ((l : ℤ) - logN N) * (y * (N : ℝ) ^ P.natDegree / 4) :=
            mul_le_mul_of_nonneg_right h2klb (by positivity)
        _ ≤ (2 : ℝ) ^ ((l : ℤ) - logN N) * (((αj - m : ℤ)) : ℝ) :=
            mul_le_mul_of_nonneg_left h6 (le_of_lt (zpow_pos (by norm_num) _))
    have hstep2 : y / 16 ≤ (1 : ℝ) / (2 * (N : ℝ)) * (y * (N : ℝ) ^ P.natDegree / 4) := by
      nlinarith [hkey, hy1]
    linarith
  have hX3y : y / 16 ≤ X3 := by
    rw [hX3]
    refine le_trans ?_ (le_max_left _ _)
    have hδz : y * (N : ℝ) ^ P.natDegree ≤ (((blkAlpha P N j - βi : ℤ)) : ℝ) := by
      rw [hy]; exact_mod_cast hδge
    have h4 : (((blkAlpha P N j - βi : ℤ)) : ℝ) ≤ 4 * (((m - blkBeta P N i : ℤ)) : ℝ) := by
      have h5 : (blkAlpha P N j - βi) ≤ 4 * (m - blkBeta P N i) := by
        rw [← hαj, ← hβi, hm]; linarith [hmd1]
      exact_mod_cast h5
    have hstep1 : (1 : ℝ) / (2 * (N : ℝ)) * (y * (N : ℝ) ^ P.natDegree / 4)
        ≤ (2 : ℝ) ^ ((l : ℤ) - logN N) * (((m - blkBeta P N i : ℤ)) : ℝ) := by
      have h6 : y * (N : ℝ) ^ P.natDegree / 4 ≤ (((m - blkBeta P N i : ℤ)) : ℝ) := by linarith
      calc (1 : ℝ) / (2 * (N : ℝ)) * (y * (N : ℝ) ^ P.natDegree / 4)
          ≤ (2 : ℝ) ^ ((l : ℤ) - logN N) * (y * (N : ℝ) ^ P.natDegree / 4) :=
            mul_le_mul_of_nonneg_right h2klb (by positivity)
        _ ≤ (2 : ℝ) ^ ((l : ℤ) - logN N) * (((m - blkBeta P N i : ℤ)) : ℝ) :=
            mul_le_mul_of_nonneg_left h6 (le_of_lt (zpow_pos (by norm_num) _))
    have hstep2 : y / 16 ≤ (1 : ℝ) / (2 * (N : ℝ)) * (y * (N : ℝ) ^ P.natDegree / 4) := by
      nlinarith [hkey, hy1]
    linarith
  have har1 := har X1 y hy1 hX1y
  have har2 := har X2 y hy1 hX2y
  have har3 := har X3 y hy1 hX3y
  -- ## the piece bounds
  have hF1dec : max ((l : ℝ)) 1 * (max ((2 : ℝ) ^ ((l : ℤ) - logN N) *
        ((blkAlpha P N j - βi : ℤ) : ℝ)) 1) ^ (-(M : ℝ)) ≤ Ll * X1 ^ (-(M : ℝ)) := by
    rw [hLl, hX1]
  have hleftv1 : eLpNorm (fun x : ℤ => if x ≤ βi then kmtProj ρ l ((l : ℤ) - logN N) v x else 0)
      2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (Co * Ll * X1 ^ (-(M : ℝ))) * eLpNorm v 2 (Measure.count : Measure ℤ) := by
    have h := offDecay_left_norm hleft hGA (a := blkAlpha P N j) (b := blkBeta P N j)
      (c := βi) (f := v) (F := Ll * X1 ^ (-(M : ℝ))) hF1dec
      (by rw [hβi]; exact hβiαj) hsupp_v hVmem
    refine h.trans (le_of_eq ?_)
    have he : ENNReal.ofReal ((Cnn : ℝ) * (Ll * X1 ^ (-(M : ℝ))))
        = ENNReal.ofReal (Co * Ll * X1 ^ (-(M : ℝ))) := by
      congr 1
      rw [hCo]; ring
    rw [he]
  have hE1 : eLpNorm (fun x : ℤ => if x ≤ βi then Eu x else 0) 2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (A * ai) := by
    refine (eLpNorm_mono (hf := by pw_aesm) fun x => ?_).trans hEu_le
    by_cases hx : x ≤ βi <;> simp [hx]
  have hF1 : eLpNorm (fun x : ℤ => if x ≤ βi then Ev x else 0) 2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (Co * Ll * X1 ^ (-(M : ℝ)) * aj) := by
    have hEq : (fun x : ℤ => if x ≤ βi then Ev x else 0)
        = -(fun x : ℤ => if x ≤ βi then kmtProj ρ l ((l : ℤ) - logN N) v x else 0) := by
      funext x
      by_cases hx : x ≤ βi
      · have hvx : v x = 0 := hsupp_v x (Or.inl (by omega))
        simp [hx, hEv_eq, Pi.sub_apply, hvx]
      · simp [hx]
    rw [hEq, eLpNorm_neg]
    refine hleftv1.trans ?_
    calc ENNReal.ofReal (Co * Ll * X1 ^ (-(M : ℝ))) * eLpNorm v 2 (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal (Co * Ll * X1 ^ (-(M : ℝ))) * ENNReal.ofReal aj :=
          mul_le_mul' le_rfl hv_le
      _ = ENNReal.ofReal (Co * Ll * X1 ^ (-(M : ℝ)) * aj) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  have hF2dec : max ((l : ℝ)) 1 * (max ((2 : ℝ) ^ ((l : ℤ) - logN N) *
        ((blkAlpha P N j - m : ℤ) : ℝ)) 1) ^ (-(M : ℝ)) ≤ Ll * X2 ^ (-(M : ℝ)) := by
    rw [hLl, hX2]
  have hleftv2 : eLpNorm (fun x : ℤ => if x ≤ m then kmtProj ρ l ((l : ℤ) - logN N) v x else 0)
      2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (Co * Ll * X2 ^ (-(M : ℝ))) * eLpNorm v 2 (Measure.count : Measure ℤ) := by
    have h := offDecay_left_norm hleft hGA (a := blkAlpha P N j) (b := blkBeta P N j)
      (c := m) (f := v) (F := Ll * X2 ^ (-(M : ℝ))) hF2dec
      (by rw [← hαj]; exact hmlt) hsupp_v hVmem
    refine h.trans (le_of_eq ?_)
    have he : ENNReal.ofReal ((Cnn : ℝ) * (Ll * X2 ^ (-(M : ℝ))))
        = ENNReal.ofReal (Co * Ll * X2 ^ (-(M : ℝ))) := by
      congr 1
      rw [hCo]; ring
    rw [he]
  have hE2 : eLpNorm (fun x : ℤ => if βi < x ∧ x < m then Eu x else 0) 2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (A * ai) := by
    refine (eLpNorm_mono (hf := by pw_aesm) fun x => ?_).trans hEu_le
    by_cases hx : βi < x ∧ x < m <;> simp [hx]
  have hF2 : eLpNorm (fun x : ℤ => if βi < x ∧ x < m then Ev x else 0)
      2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (Co * Ll * X2 ^ (-(M : ℝ)) * aj) := by
    have hmono : eLpNorm (fun x : ℤ => if βi < x ∧ x < m then Ev x else 0)
        2 (Measure.count : Measure ℤ)
        ≤ eLpNorm (fun x : ℤ => if x ≤ m then Ev x else 0) 2 (Measure.count : Measure ℤ) := by
      refine eLpNorm_mono (hf := by pw_aesm) fun x => ?_
      by_cases hx : βi < x ∧ x < m
      · rw [if_pos hx, if_pos (le_of_lt hx.2)]
      · rw [if_neg hx]; simp
    have hEq : (fun x : ℤ => if x ≤ m then Ev x else 0)
        = -(fun x : ℤ => if x ≤ m then kmtProj ρ l ((l : ℤ) - logN N) v x else 0) := by
      funext x
      by_cases hx : x ≤ m
      · have hvx : v x = 0 := hsupp_v x (Or.inl (by omega))
        simp [hx, hEv_eq, Pi.sub_apply, hvx]
      · simp [hx]
    refine hmono.trans ?_
    rw [hEq, eLpNorm_neg]
    refine hleftv2.trans ?_
    calc ENNReal.ofReal (Co * Ll * X2 ^ (-(M : ℝ))) * eLpNorm v 2 (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal (Co * Ll * X2 ^ (-(M : ℝ))) * ENNReal.ofReal aj :=
          mul_le_mul' le_rfl hv_le
      _ = ENNReal.ofReal (Co * Ll * X2 ^ (-(M : ℝ)) * aj) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  have hF3dec : max ((l : ℝ)) 1 * (max ((2 : ℝ) ^ ((l : ℤ) - logN N) *
        ((m - blkBeta P N i : ℤ) : ℝ)) 1) ^ (-(M : ℝ)) ≤ Ll * X3 ^ (-(M : ℝ)) := by
    rw [hLl, hX3]
  have hrightu3 : eLpNorm (fun x : ℤ => if m ≤ x then kmtProj ρ l ((l : ℤ) - logN N) u x else 0)
      2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (Co * Ll * X3 ^ (-(M : ℝ))) * eLpNorm u 2 (Measure.count : Measure ℤ) := by
    have h := offDecay_right_norm hright hGA (a := blkAlpha P N i) (b := blkBeta P N i)
      (c := m) (f := u) (F := Ll * X3 ^ (-(M : ℝ))) hF3dec
      (by rw [← hβi]; exact hmgt) hsupp_u
    refine h.trans (le_of_eq ?_)
    have he : ENNReal.ofReal ((Cnn : ℝ) * (Ll * X3 ^ (-(M : ℝ))))
        = ENNReal.ofReal (Co * Ll * X3 ^ (-(M : ℝ))) := by
      congr 1
      rw [hCo]; ring
    rw [he]
  have hE3 : eLpNorm (fun x : ℤ => if m ≤ x then Eu x else 0) 2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (Co * Ll * X3 ^ (-(M : ℝ)) * ai) := by
    have hEq : (fun x : ℤ => if m ≤ x then Eu x else 0)
        = -(fun x : ℤ => if m ≤ x then kmtProj ρ l ((l : ℤ) - logN N) u x else 0) := by
      funext x
      by_cases hx : m ≤ x
      · have hux : u x = 0 := hsupp_u x (Or.inr (by omega))
        simp [hx, hEu_eq, Pi.sub_apply, hux]
      · simp [hx]
    rw [hEq, eLpNorm_neg]
    refine hrightu3.trans ?_
    calc ENNReal.ofReal (Co * Ll * X3 ^ (-(M : ℝ))) * eLpNorm u 2 (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal (Co * Ll * X3 ^ (-(M : ℝ))) * ENNReal.ofReal ai :=
          mul_le_mul' le_rfl hu_le
      _ = ENNReal.ofReal (Co * Ll * X3 ^ (-(M : ℝ)) * ai) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  have hF3 : eLpNorm (fun x : ℤ => if m ≤ x then Ev x else 0) 2 (Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal (A * aj) := by
    refine (eLpNorm_mono (hf := by pw_aesm) fun x => ?_).trans hEv_le
    by_cases hx : m ≤ x <;> simp [hx]
  -- ## the three pairing bounds
  set B1 : ℝ := (A * ai) * (Co * Ll * X1 ^ (-(M : ℝ)) * aj) with hB1def
  set B2 : ℝ := (A * ai) * (Co * Ll * X2 ^ (-(M : ℝ)) * aj) with hB2def
  set B3 : ℝ := (Co * Ll * X3 ^ (-(M : ℝ)) * ai) * (A * aj) with hB3def
  have hB10 : 0 ≤ B1 := by rw [hB1def]; positivity
  have hB20 : 0 ≤ B2 := by rw [hB2def]; positivity
  have hB30 : 0 ≤ B3 := by rw [hB3def]; positivity
  -- ## the pointwise splitting
  have hsplit : ∀ x : ℤ, Eu x * star (Ev x)
      = (if x ≤ βi then Eu x else 0) * star (if x ≤ βi then Ev x else 0)
        + (if βi < x ∧ x < m then Eu x else 0) * star (if βi < x ∧ x < m then Ev x else 0)
        + (if m ≤ x then Eu x else 0) * star (if m ≤ x then Ev x else 0) := by
    intro x
    by_cases h1 : x ≤ βi
    · have h2 : ¬ (βi < x ∧ x < m) := fun hc => absurd hc.1 (not_lt.mpr h1)
      have h3 : ¬ (m ≤ x) := not_le.mpr (lt_of_le_of_lt h1 hmgt)
      simp only [if_pos h1, if_neg h2, if_neg h3]
      ring
    · by_cases h2 : x < m
      · have h3 : ¬ (m ≤ x) := not_le.mpr h2
        have h4 : βi < x ∧ x < m := ⟨not_le.mp h1, h2⟩
        simp only [if_neg h1, if_pos h4, if_neg h3]
        ring
      · have h3 : m ≤ x := not_lt.mp h2
        have h4 : ¬ (βi < x ∧ x < m) := fun hc => absurd hc.2 h2
        simp only [if_neg h1, if_neg h4, if_pos h3]
        ring
  -- ## the ENNReal chain
  have hA1eq : (∑' x : ℤ, ‖(if x ≤ βi then Eu x else 0) * star (if x ≤ βi then Ev x else 0)‖ₑ)
      = eLpNorm (fun x : ℤ => (if x ≤ βi then Eu x else 0) * star (if x ≤ βi then Ev x else 0))
          1 (Measure.count : Measure ℤ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), lintegral_count]
  have hA2eq : (∑' x : ℤ, ‖(if βi < x ∧ x < m then Eu x else 0)
        * star (if βi < x ∧ x < m then Ev x else 0)‖ₑ)
      = eLpNorm (fun x : ℤ => (if βi < x ∧ x < m then Eu x else 0)
          * star (if βi < x ∧ x < m then Ev x else 0)) 1 (Measure.count : Measure ℤ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), lintegral_count]
  have hA3eq : (∑' x : ℤ, ‖(if m ≤ x then Eu x else 0) * star (if m ≤ x then Ev x else 0)‖ₑ)
      = eLpNorm (fun x : ℤ => (if m ≤ x then Eu x else 0) * star (if m ≤ x then Ev x else 0))
          1 (Measure.count : Measure ℤ) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), lintegral_count]
  have hT : ‖∑' x : ℤ, Eu x * star (Ev x)‖ ≤ B1 + B2 + B3 := by
    have key : ENNReal.ofReal ‖∑' x : ℤ, Eu x * star (Ev x)‖
        ≤ ENNReal.ofReal (B1 + B2 + B3) := by
      have h2 : ENNReal.ofReal ‖∑' x : ℤ, Eu x * star (Ev x)‖
          = ‖∑' x : ℤ, Eu x * star (Ev x)‖ₑ := by simp [enorm_eq_nnnorm]
      rw [h2]
      have step1 : ‖∑' x : ℤ, Eu x * star (Ev x)‖ₑ
          ≤ ∑' x : ℤ, (‖(if x ≤ βi then Eu x else 0) * star (if x ≤ βi then Ev x else 0)‖ₑ
              + ‖(if βi < x ∧ x < m then Eu x else 0) * star (if βi < x ∧ x < m then Ev x else 0)‖ₑ
              + ‖(if m ≤ x then Eu x else 0) * star (if m ≤ x then Ev x else 0)‖ₑ) := by
        refine (enorm_tsum_le_tsum_enorm).trans (ENNReal.tsum_le_tsum fun x => ?_)
        rw [hsplit x]
        calc ‖(if x ≤ βi then Eu x else 0) * star (if x ≤ βi then Ev x else 0)
              + (if βi < x ∧ x < m then Eu x else 0) * star (if βi < x ∧ x < m then Ev x else 0)
              + (if m ≤ x then Eu x else 0) * star (if m ≤ x then Ev x else 0)‖ₑ
            ≤ ‖(if x ≤ βi then Eu x else 0) * star (if x ≤ βi then Ev x else 0)
                + (if βi < x ∧ x < m then Eu x else 0) * star (if βi < x ∧ x < m then Ev x else 0)‖ₑ
              + ‖(if m ≤ x then Eu x else 0) * star (if m ≤ x then Ev x else 0)‖ₑ :=
              enorm_add_le _ _
          _ ≤ (‖(if x ≤ βi then Eu x else 0) * star (if x ≤ βi then Ev x else 0)‖ₑ
              + ‖(if βi < x ∧ x < m then Eu x else 0)
                  * star (if βi < x ∧ x < m then Ev x else 0)‖ₑ)
              + ‖(if m ≤ x then Eu x else 0) * star (if m ≤ x then Ev x else 0)‖ₑ :=
              add_le_add (enorm_add_le _ _) le_rfl
      refine step1.trans ?_
      rw [ENNReal.tsum_add, ENNReal.tsum_add, hA1eq, hA2eq, hA3eq]
      have e1 : ENNReal.ofReal (A * ai) * ENNReal.ofReal (Co * Ll * X1 ^ (-(M : ℝ)) * aj)
          = ENNReal.ofReal B1 := by
        rw [hB1def, ← ENNReal.ofReal_mul (by positivity)]
      have e2 : ENNReal.ofReal (A * ai) * ENNReal.ofReal (Co * Ll * X2 ^ (-(M : ℝ)) * aj)
          = ENNReal.ofReal B2 := by
        rw [hB2def, ← ENNReal.ofReal_mul (by positivity)]
      have e3 : ENNReal.ofReal (Co * Ll * X3 ^ (-(M : ℝ)) * ai) * ENNReal.ofReal (A * aj)
          = ENNReal.ofReal B3 := by
        rw [hB3def, ← ENNReal.ofReal_mul (by positivity)]
      have hH1 : eLpNorm (fun x : ℤ => (if x ≤ βi then Eu x else 0)
            * star (if x ≤ βi then Ev x else 0)) 1 (Measure.count : Measure ℤ)
          ≤ ENNReal.ofReal B1 := by
        rw [← e1]
        exact (eLpNorm_mul_star_le _ _).trans (mul_le_mul hE1 hF1 zero_le zero_le)
      have hH2 : eLpNorm (fun x : ℤ => (if βi < x ∧ x < m then Eu x else 0)
            * star (if βi < x ∧ x < m then Ev x else 0)) 1 (Measure.count : Measure ℤ)
          ≤ ENNReal.ofReal B2 := by
        rw [← e2]
        exact (eLpNorm_mul_star_le _ _).trans (mul_le_mul hE2 hF2 zero_le zero_le)
      have hH3 : eLpNorm (fun x : ℤ => (if m ≤ x then Eu x else 0)
            * star (if m ≤ x then Ev x else 0)) 1 (Measure.count : Measure ℤ)
          ≤ ENNReal.ofReal B3 := by
        rw [← e3]
        exact (eLpNorm_mul_star_le _ _).trans (mul_le_mul hE3 hF3 zero_le zero_le)
      have hsum_eq : ENNReal.ofReal B1 + ENNReal.ofReal B2 + ENNReal.ofReal B3
          = ENNReal.ofReal (B1 + B2 + B3) := by
        have h12 : ENNReal.ofReal B1 + ENNReal.ofReal B2 = ENNReal.ofReal (B1 + B2) :=
          (ENNReal.ofReal_add hB10 hB20).symm
        have h123 : ENNReal.ofReal (B1 + B2) + ENNReal.ofReal B3
            = ENNReal.ofReal (B1 + B2 + B3) :=
          (ENNReal.ofReal_add (add_nonneg hB10 hB20) hB30).symm
        calc ENNReal.ofReal B1 + ENNReal.ofReal B2 + ENNReal.ofReal B3
            = ENNReal.ofReal (B1 + B2) + ENNReal.ofReal B3 := by rw [h12]
          _ = ENNReal.ofReal (B1 + B2 + B3) := h123
      exact le_trans (add_le_add (add_le_add hH1 hH2) hH3) (le_of_eq hsum_eq)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key
  -- ## the geometric-mean inputs
  have hT2 : ‖∑' x : ℤ, Eu x * star (Ev x)‖ ≤ (A * A) * (ai * aj) := by
    have h := sivPairingCS (mul_nonneg hA hai0) (mul_nonneg hA haj0) hEu_le hEv_le
    calc ‖∑' x : ℤ, Eu x * star (Ev x)‖ ≤ (A * ai) * (A * aj) := h
      _ = (A * A) * (ai * aj) := by ring
  set σ : ℝ := X1 ^ (-(M : ℝ)) + X2 ^ (-(M : ℝ)) + X3 ^ (-(M : ℝ)) with hσdef
  have hσ0 : 0 ≤ σ := by rw [hσdef]; positivity
  have hT' : ‖∑' x : ℤ, Eu x * star (Ev x)‖ ≤ A * ((Co * Ll * σ) * (ai * aj)) := by
    have h := hT
    rw [hσdef]
    rw [hB1def, hB2def, hB3def] at h
    convert h using 1 <;> ring
  have hKbig1 : 3 * Kar * Real.sqrt Co ≤ 3 * Kar * Real.sqrt Co + 3 * Co * (Kar + 1) ^ 2 + 1 := by
    have h1 : 0 ≤ 3 * Co * (Kar + 1) ^ 2 := by positivity
    linarith
  have hKbig2 : 3 * Co * Kar ^ 2 ≤ 3 * Kar * Real.sqrt Co + 3 * Co * (Kar + 1) ^ 2 + 1 := by
    have h1 : 0 ≤ 3 * Kar * Real.sqrt Co := by positivity
    have h2 : 3 * Co * Kar ^ 2 ≤ 3 * Co * (Kar + 1) ^ 2 := by
      have h3 : Kar ^ 2 ≤ (Kar + 1) ^ 2 := by nlinarith [hKar]
      nlinarith [h3, hCo0]
    linarith
  by_cases hA1 : A ≤ 1
  · -- ### Case `A ≤ 1`
    have hN0 : 0 ≤ (Co * Ll * σ) * (ai * aj) := by positivity
    have hfree : ‖∑' x : ℤ, Eu x * star (Ev x)‖ ≤ (Co * Ll * σ) * (ai * aj) := by
      have h := hT'
      nlinarith [h, hA1, hN0]
    have hmin : ‖∑' x : ℤ, Eu x * star (Ev x)‖
        ≤ min (A * A) (Co * Ll * σ) * (ai * aj) := by
      rw [min_mul_of_nonneg _ _ (mul_nonneg hai0 haj0)]
      exact le_min hT2 hfree
    have hsqrtσ : Real.sqrt σ ≤ 3 * Kar * y ^ (-((M : ℝ) / 2)) := by
      rw [hσdef]
      refine (sqrt_add_three_le (by positivity) (by positivity) (by positivity)).trans ?_
      linarith [har1, har2, har3]
    have hsqsplit : Real.sqrt (Co * Ll * σ) = Real.sqrt Co * Real.sqrt Ll * Real.sqrt σ := by
      rw [Real.sqrt_mul (mul_nonneg hCo0' hLl0), Real.sqrt_mul hCo0']
    have hsqrtLl : Real.sqrt Ll ≤ Ll ^ M := sqrt_max_one_le_pow l M (by omega)
    have hstep : Real.sqrt (Co * Ll * σ)
        ≤ Real.sqrt Co * Ll ^ M * (3 * Kar * y ^ (-((M : ℝ) / 2))) := by
      rw [hsqsplit]
      refine mul_le_mul (mul_le_mul_of_nonneg_left hsqrtLl (Real.sqrt_nonneg Co)) hsqrtσ
        (Real.sqrt_nonneg σ) (by positivity)
    have hmin2 : min (A * A) (Co * Ll * σ) ≤ A * Real.sqrt (Co * Ll * σ) :=
      min_sq_le_sqrt_mul hA (mul_nonneg (mul_nonneg hCo0' hLl0) hσ0)
    have hfin : ‖∑' x : ℤ, Eu x * star (Ev x)‖
        ≤ (3 * Kar * Real.sqrt Co) * A * Ll ^ M * y ^ (-((M : ℝ) / 2)) * ai * aj := by
      calc ‖∑' x : ℤ, Eu x * star (Ev x)‖
          ≤ min (A * A) (Co * Ll * σ) * (ai * aj) := hmin
        _ ≤ (A * Real.sqrt (Co * Ll * σ)) * (ai * aj) :=
            mul_le_mul_of_nonneg_right hmin2 (mul_nonneg hai0 haj0)
        _ ≤ (A * (Real.sqrt Co * Ll ^ M * (3 * Kar * y ^ (-((M : ℝ) / 2))))) * (ai * aj) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hA) (mul_nonneg hai0 haj0)
        _ = (3 * Kar * Real.sqrt Co) * A * Ll ^ M * y ^ (-((M : ℝ) / 2)) * ai * aj := by ring
    calc ‖∑' x : ℤ, Eu x * star (Ev x)‖
        ≤ (3 * Kar * Real.sqrt Co) * A * Ll ^ M * y ^ (-((M : ℝ) / 2)) * ai * aj := hfin
      _ ≤ (3 * Kar * Real.sqrt Co + 3 * Co * (Kar + 1) ^ 2 + 1) * A * Ll ^ M
            * y ^ (-((M : ℝ) / 2)) * ai * aj := by
          have h9 : 0 ≤ A * Ll ^ M * y ^ (-((M : ℝ) / 2)) * ai * aj := by positivity
          nlinarith [hKbig1, h9]
      _ = (3 * Kar * Real.sqrt Co + 3 * Co * (Kar + 1) ^ 2 + 1) * A * max ((l : ℝ)) 1 ^ M
            * max 1 (((j - i : ℤ)) : ℝ) ^ (-((M : ℝ) / 2))
            * l2norm (blkPiece P N g i) * l2norm (blkPiece P N g j) := by
          rw [← hy, hLl, hai, haj, max_eq_right hy1]
  · -- ### Case `1 < A`
    have hAgt : (1 : ℝ) < A := not_le.mp hA1
    have hsq : ∀ X : ℝ, 0 ≤ X → Real.sqrt (X ^ (-(M : ℝ))) ≤ Kar * y ^ (-((M : ℝ) / 2)) →
        X ^ (-(M : ℝ)) ≤ Kar ^ 2 * y ^ (-(M : ℝ)) := by
      intro X hX0 hX
      have h1 : X ^ (-(M : ℝ)) = (Real.sqrt (X ^ (-(M : ℝ)))) ^ (2 : ℝ) := by
        rw [Real.rpow_two, Real.sq_sqrt (Real.rpow_nonneg hX0 _)]
      have h2 : (Real.sqrt (X ^ (-(M : ℝ)))) ^ (2 : ℝ)
          ≤ (Kar * y ^ (-((M : ℝ) / 2))) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (Real.sqrt_nonneg _) hX (by norm_num)
      have h3 : (Kar * y ^ (-((M : ℝ) / 2))) ^ (2 : ℝ) = Kar ^ 2 * y ^ (-(M : ℝ)) := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_two, ← Real.rpow_mul hy0]
        congr 1
        ring
      linarith [h1, h2, h3]
    have hσb : σ ≤ 3 * Kar ^ 2 * y ^ (-(M : ℝ)) := by
      rw [hσdef]
      have hs1 := hsq X1 (le_of_lt hX1pos) har1
      have hs2 := hsq X2 (le_of_lt hX2pos) har2
      have hs3 := hsq X3 (le_of_lt hX3pos) har3
      linarith
    have hstep : Co * Ll * σ ≤ 3 * Co * Kar ^ 2 * Ll ^ M * y ^ (-((M : ℝ) / 2)) := by
      have hyM : y ^ (-(M : ℝ)) ≤ y ^ (-((M : ℝ) / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
      have hLM : Ll ≤ Ll ^ M := le_self_pow₀ hLl1 (by omega)
      have hmul1 : Co * Ll * σ ≤ Co * Ll * (3 * Kar ^ 2 * y ^ (-(M : ℝ))) :=
        mul_le_mul_of_nonneg_left hσb (by positivity : (0 : ℝ) ≤ Co * Ll)
      have hmul2 : Co * Ll * (3 * Kar ^ 2 * y ^ (-(M : ℝ)))
          ≤ Co * Ll * (3 * Kar ^ 2 * y ^ (-((M : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hyM (by positivity : (0 : ℝ) ≤ 3 * Kar ^ 2))
          (by positivity : (0 : ℝ) ≤ Co * Ll)
      have hmul3 : Co * (Ll * (3 * Kar ^ 2 * y ^ (-((M : ℝ) / 2))))
          ≤ Co * (Ll ^ M * (3 * Kar ^ 2 * y ^ (-((M : ℝ) / 2)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hLM (by positivity : (0 : ℝ) ≤ 3 * Kar ^ 2 * y ^ (-((M : ℝ) / 2))))
          (by positivity : (0 : ℝ) ≤ Co)
      calc Co * Ll * σ
          ≤ Co * Ll * (3 * Kar ^ 2 * y ^ (-(M : ℝ))) := hmul1
        _ ≤ Co * Ll * (3 * Kar ^ 2 * y ^ (-((M : ℝ) / 2))) := hmul2
        _ = Co * (Ll * (3 * Kar ^ 2 * y ^ (-((M : ℝ) / 2)))) := by ring
        _ ≤ Co * (Ll ^ M * (3 * Kar ^ 2 * y ^ (-((M : ℝ) / 2)))) := hmul3
        _ = 3 * Co * Kar ^ 2 * Ll ^ M * y ^ (-((M : ℝ) / 2)) := by ring
    calc ‖∑' x : ℤ, Eu x * star (Ev x)‖ ≤ A * ((Co * Ll * σ) * (ai * aj)) := hT'
      _ ≤ A * ((3 * Co * Kar ^ 2 * Ll ^ M * y ^ (-((M : ℝ) / 2))) * (ai * aj)) := by
          refine mul_le_mul_of_nonneg_left ?_ hA
          exact mul_le_mul_of_nonneg_right hstep (mul_nonneg hai0 haj0)
      _ = 3 * Co * Kar ^ 2 * Ll ^ M * y ^ (-((M : ℝ) / 2)) * A * ai * aj := by ring
      _ ≤ (3 * Kar * Real.sqrt Co + 3 * Co * (Kar + 1) ^ 2 + 1) * A * Ll ^ M
            * y ^ (-((M : ℝ) / 2)) * ai * aj := by
          have hX : 0 ≤ Ll ^ M * y ^ (-((M : ℝ) / 2)) * ai * aj := by positivity
          have h10 : 3 * Co * Kar ^ 2 * A
              ≤ (3 * Kar * Real.sqrt Co + 3 * Co * (Kar + 1) ^ 2 + 1) * A :=
            mul_le_mul_of_nonneg_right hKbig2 hA
          have hstep2 := mul_le_mul_of_nonneg_right h10 hX
          have heq : 3 * Co * Kar ^ 2 * A * (Ll ^ M * y ^ (-((M : ℝ) / 2)) * ai * aj)
              = 3 * Co * Kar ^ 2 * Ll ^ M * y ^ (-((M : ℝ) / 2)) * A * ai * aj := by ring
          have heq2 : (3 * Kar * Real.sqrt Co + 3 * Co * (Kar + 1) ^ 2 + 1) * A
                * (Ll ^ M * y ^ (-((M : ℝ) / 2)) * ai * aj)
              = (3 * Kar * Real.sqrt Co + 3 * Co * (Kar + 1) ^ 2 + 1) * A * Ll ^ M
                * y ^ (-((M : ℝ) / 2)) * ai * aj := by ring
          linarith [hstep2, heq, heq2]
      _ = (3 * Kar * Real.sqrt Co + 3 * Co * (Kar + 1) ^ 2 + 1) * A * max ((l : ℝ)) 1 ^ M
            * max 1 (((j - i : ℤ)) : ℝ) ^ (-((M : ℝ) / 2))
            * l2norm (blkPiece P N g i) * l2norm (blkPiece P N g j) := by
          rw [← hy, hLl, hai, haj, max_eq_right hy1]

end Work.KMTAreas.A4
