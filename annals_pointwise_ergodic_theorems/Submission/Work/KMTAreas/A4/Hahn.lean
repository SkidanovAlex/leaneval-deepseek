/-
# The Hahn--Banach structure lemma for dual functions (KMT §5, Lemma `hahn`)

Krause--Mirek--Tao, §5 (minor arc single scale estimate) analyse the *dual functions*
`Ã*_N(h,g)` of the bilinear average by dualising the inverse theorem of §5.  The abstract
functional-analytic step is their Lemma `hahn`:

> Let `A,B > 0` and `G ∈ ℓ²(ℤ)`.  Let `Φ` be a family of vectors in `ℓ²(ℤ)` such that whenever
> `f ∈ ℓ²(ℤ)` has `‖f‖_{ℓ^∞} ≤ 1` and `|⟨f,G⟩| > A`, then `|⟨f,φ⟩| > B` for some `φ ∈ Φ`.
> Then `G` lies in the closed convex hull of
> `V = {lam • φ : φ ∈ Φ, ‖lam‖ ≤ A/B} ∪ {h ∈ ℓ²(ℤ) : ‖h‖_{ℓ¹} ≤ A}`.

The content is the Hahn--Banach separation: if `G` were outside the closed convex hull `C` of
`V`, the nearest point `P ∈ C` to `G` and `f = G - P` would satisfy
`Re inner (G - P) (w - P) ≤ 0` for all `w ∈ C`, hence (using that `C` is balanced)
`‖inner (G-P) w‖ ≤ s` with `s = Re inner (G-P) P`, and `Re inner (G-P) G = s + ‖G-P‖² > s`;
rescaling to `(A/s) (G-P)` produces a `1`-bounded `F` with `‖inner F G‖ > A` while
`‖inner F φ‖ ≤ B` for every `φ ∈ Φ`, contradicting the hypothesis.

Everything is stated with the *Hilbert* inner product `inner` of `ℓ²(ℤ)`
(`inner f g = ∑_x f x · conj (g x)`); the passage to the paper's *bilinear* pairing
`∑_x f x · g x` is by conjugation of `G` and `Φ`, which is an isometry of `ℓ²(ℤ)` preserving
the `ℓ¹`-ball and the class of major-arc functions.
-/
import Mathlib
import Submission.Work.KMTContract.Areas

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.IonescuWainger (L2Z)

/-! ## The `ℓ¹`-ball inside `ℓ²(ℤ)` -/

/-- Membership in the `ℓ¹`-ball of radius `A`, for an element of `ℓ²(ℤ)`. -/
def MemL1Ball (A : ℝ) (f : L2Z) : Prop :=
  Summable (fun x : ℤ => ‖f x‖) ∧ ∑' x : ℤ, ‖f x‖ ≤ A

theorem memL1Ball_zero {A : ℝ} (hA : 0 ≤ A) : MemL1Ball A (0 : L2Z) :=
  ⟨by simpa using (summable_zero : Summable fun _ : ℤ => (0 : ℝ)),
    by simp [hA]⟩

theorem MemL1Ball.smul {A : ℝ} {c : ℂ} (hc : ‖c‖ ≤ 1) {f : L2Z} (hf : MemL1Ball A f) :
    MemL1Ball A (c • f) := by
  obtain ⟨hsum, hle⟩ := hf
  have hpt : ∀ x : ℤ, ‖(c • f : L2Z) x‖ = ‖c‖ * ‖f x‖ := fun x => by
    rw [show (c • f : L2Z) x = c * f x from rfl, norm_mul]
  refine ⟨?_, ?_⟩
  · exact hsum.mul_left ‖c‖ |>.congr fun x => (hpt x).symm
  · rw [tsum_congr hpt, tsum_mul_left]
    calc ‖c‖ * ∑' x : ℤ, ‖f x‖ ≤ 1 * A :=
          mul_le_mul hc hle (tsum_nonneg fun _ => norm_nonneg _) (by norm_num)
      _ = A := one_mul A

/-- The unit vector at `x`, as an element of `ℓ²(ℤ)`. -/
def eZ (x : ℤ) : L2Z := lp.single 2 x (1 : ℂ)

theorem eZ_apply (x y : ℤ) : eZ x y = if y = x then 1 else 0 := by
  rw [eZ, lp.coeFn_single]
  exact Pi.single_apply x 1 y

theorem inner_eZ (f : L2Z) (x : ℤ) : inner ℂ f (eZ x) = star (f x) := by
  rw [eZ, lp.inner_single_right]
  simp

theorem MemL1Ball.smul_eZ {A : ℝ} (hA : 0 < A) (x : ℤ) :
    MemL1Ball A (((A : ℂ)) • eZ x) := by
  have hpt : ∀ y : ℤ, ‖(((A : ℂ)) • eZ x : L2Z) y‖ = if y = x then A else 0 := by
    intro y
    rw [show (((A : ℂ)) • eZ x : L2Z) y = (A : ℂ) * eZ x y from rfl, eZ_apply]
    by_cases hy : y = x
    · rw [if_pos hy, if_pos hy, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
    · rw [if_neg hy, if_neg hy, mul_zero, norm_zero]
  refine ⟨?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := {x}) fun y hy => ?_
    rw [hpt y, if_neg (by simpa using hy)]
  · rw [tsum_congr hpt, tsum_ite_eq]

/-! ## The set `V` of Lemma `hahn`, and its invariances -/

/-- The set `V` of Lemma `hahn`: the dilates `lam • φ` of the inverse-theorem family `Φ` with
`‖lam‖ ≤ A/B`, together with the `ℓ¹`-ball of radius `A`. -/
def hahnV (A B : ℝ) (Φ : Set L2Z) : Set L2Z :=
  {v | (∃ φ ∈ Φ, ∃ lam : ℂ, ‖lam‖ ≤ A / B ∧ v = lam • φ) ∨ MemL1Ball A v}

theorem balanced_hahnV_ptwise (A B : ℝ) (Φ : Set L2Z) :
    ∀ c : ℂ, ‖c‖ ≤ 1 → ∀ v ∈ hahnV A B Φ, c • v ∈ hahnV A B Φ := by
  intro c hc v hv
  rcases hv with ⟨φ, hφ, lam, hlam, rfl⟩ | hv
  · refine Or.inl ⟨φ, hφ, c * lam, ?_, by rw [smul_smul]⟩
    rw [norm_mul]
    calc ‖c‖ * ‖lam‖ ≤ 1 * (A / B) := mul_le_mul hc hlam (norm_nonneg _) (by norm_num)
      _ = A / B := one_mul _
  · exact Or.inr (hv.smul hc)

theorem balanced_hahnV (A B : ℝ) (Φ : Set L2Z) : Balanced ℂ (hahnV A B Φ) := by
  intro c hc x hx
  rcases hx with ⟨v, hv, rfl⟩
  exact balanced_hahnV_ptwise A B Φ c hc v hv

theorem hahnV_zero (A : ℝ) (hA : 0 ≤ A) (B : ℝ) (Φ : Set L2Z) :
    (0 : L2Z) ∈ hahnV A B Φ := Or.inr (memL1Ball_zero hA)

theorem norm_phi_scalar {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ‖((A : ℂ) / (B : ℂ))‖ = A / B := by
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hA, abs_of_pos hB]

theorem mem_closure_convexHull {s : Set L2Z} {x : L2Z} (hx : x ∈ s) :
    x ∈ closure (convexHull ℝ s) :=
  subset_closure (subset_convexHull ℝ s hx)

theorem hahnV_smul_phi {A B : ℝ} {Φ : Set L2Z} {φ : L2Z} (hA : 0 < A) (hB : 0 < B)
    (hφ : φ ∈ Φ) : ((A : ℂ) / (B : ℂ)) • φ ∈ hahnV A B Φ :=
  Or.inl ⟨φ, hφ, (A : ℂ) / (B : ℂ), le_of_eq (norm_phi_scalar hA hB), rfl⟩

/-- The unit-complex invariance of the closed convex hull of a unit-invariant set. -/
theorem unit_smul_mem_of_ptwise {s : Set L2Z}
    (hs : ∀ c : ℂ, ‖c‖ ≤ 1 → ∀ v ∈ s, c • v ∈ s) :
    ∀ μ : ℂ, ‖μ‖ = 1 → ∀ v ∈ closure (convexHull ℝ s), μ • v ∈ closure (convexHull ℝ s) := by
  have hunitCH : ∀ μ : ℂ, ‖μ‖ = 1 → ∀ v ∈ convexHull ℝ s, μ • v ∈ convexHull ℝ s := by
    intro μ hμ v hv
    rw [mem_convexHull_iff_exists_fintype] at hv ⊢
    obtain ⟨ι, hι, w, z, hw, hsum, hz, hx⟩ := hv
    refine ⟨ι, hι, w, fun i => μ • z i, hw, hsum, fun i => hs μ (le_of_eq hμ) (z i) (hz i), ?_⟩
    calc ∑ i, w i • (μ • z i) = ∑ i, μ • (w i • z i) :=
          Finset.sum_congr rfl fun i _ => smul_comm _ _ _
      _ = μ • ∑ i, w i • z i := (Finset.smul_sum).symm
      _ = μ • v := by rw [hx]
  intro μ hμ v hv
  have hclosed : IsClosed {v : L2Z | μ • v ∈ closure (convexHull ℝ s)} := by
    have hcont : Continuous fun v : L2Z => μ • v := by
      have hc : Continuous fun _ : L2Z => μ := continuous_const
      have hid : Continuous fun v : L2Z => v := continuous_id
      exact hc.smul hid
    have h2 : IsClosed ((fun v : L2Z => μ • v) ⁻¹' closure (convexHull ℝ s)) :=
      isClosed_closure.preimage hcont
    rwa [Set.preimage] at h2
  exact hclosed.closure_subset_iff.mpr (fun v hv => subset_closure (hunitCH μ hμ v hv)) hv

/-! ## The complex inner product versus the real inner product of `ℓ²(ℤ)` -/

theorem summable_inner (x y : L2Z) : Summable (fun i : ℤ => inner ℂ (x i) (y i)) := by
  refine Summable.of_norm_bounded
    (lp.summable_mul (p := 2) (q := 2) ⟨by norm_num, by norm_num, by norm_num⟩ x y)
    fun i => ?_
  exact norm_inner_le_norm _ _

theorem norm_star_complex (z : ℂ) : ‖star z‖ = ‖z‖ := Complex.norm_conj z

/-- The real inner product on `ℓ²(ℤ)` induced by the complex one is the real part of the
complex inner product. -/
theorem inner_real_eq_re (x y : L2Z) : inner ℝ x y = (inner ℂ x y).re := by
  rw [lp.inner_eq_tsum (𝕜 := ℝ), lp.inner_eq_tsum (𝕜 := ℂ),
    Complex.re_tsum (summable_inner x y)]
  exact tsum_congr fun i => by simp [Complex.inner, RCLike.inner_apply]

/-! ## Lemma `hahn` -/

/-- **Lemma `hahn` (Krause--Mirek--Tao, §5).**  If every `1`-bounded `f ∈ ℓ²(ℤ)` whose pairing
with `G` exceeds `A` in modulus correlates with some `φ ∈ Φ` to the extent `B`, then `G` lies in
the closed convex hull of `V = {lam • φ : φ ∈ Φ, ‖lam‖ ≤ A/B} ∪ {‖h‖_{ℓ¹} ≤ A}`. -/
theorem hahn_structure {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (G : L2Z) (Φ : Set L2Z)
    (h : ∀ f : L2Z, (∀ x : ℤ, ‖f x‖ ≤ 1) → A < ‖inner ℂ f G‖ →
      ∃ φ ∈ Φ, B < ‖inner ℂ f φ‖) :
    G ∈ closure (convexHull ℝ (hahnV A B Φ)) := by
  have hunitC := unit_smul_mem_of_ptwise (balanced_hahnV_ptwise A B Φ)
  have h0C : (0 : L2Z) ∈ closure (convexHull ℝ (hahnV A B Φ)) :=
    mem_closure_convexHull (hahnV_zero A hA.le B Φ)
  by_contra hG
  have hCne : (closure (convexHull ℝ (hahnV A B Φ))).Nonempty := ⟨0, h0C⟩
  have hCconv : Convex ℝ (closure (convexHull ℝ (hahnV A B Φ))) :=
    (convex_convexHull ℝ (hahnV A B Φ)).closure
  have hCclosed : IsClosed (closure (convexHull ℝ (hahnV A B Φ))) := isClosed_closure
  obtain ⟨P, hP, hPmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hCne hCclosed.isComplete hCconv G
  have hvar : ∀ w ∈ closure (convexHull ℝ (hahnV A B Φ)), inner ℝ (G - P) (w - P) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hCconv hP).mp hPmin
  have hfne : G - P ≠ 0 := by
    intro h0
    exact hG (by rw [sub_eq_zero.mp h0]; exact hP)
  have hfnn : 0 < ‖G - P‖ := norm_pos_iff.mpr hfne
  have hleP : ∀ w ∈ closure (convexHull ℝ (hahnV A B Φ)),
      (inner ℂ (G - P) w).re ≤ (inner ℂ (G - P) P).re := by
    intro w hw
    have h1 := hvar w hw
    simp only [inner_sub_right, inner_real_eq_re, Complex.sub_re] at h1
    linarith
  have hgeP : ∀ w ∈ closure (convexHull ℝ (hahnV A B Φ)),
      -(inner ℂ (G - P) P).re ≤ (inner ℂ (G - P) w).re := by
    intro w hw
    have hw' : -w ∈ closure (convexHull ℝ (hahnV A B Φ)) := by
      have h1 : (-1 : ℂ) • w ∈ closure (convexHull ℝ (hahnV A B Φ)) :=
        hunitC (-1) (by norm_num) w hw
      simpa using h1
    have h2 := hleP (-w) hw'
    rw [inner_neg_right, Complex.neg_re] at h2
    linarith
  have habs : ∀ w ∈ closure (convexHull ℝ (hahnV A B Φ)),
      |(inner ℂ (G - P) w).re| ≤ (inner ℂ (G - P) P).re :=
    fun w hw => abs_le.mpr ⟨hgeP w hw, hleP w hw⟩
  have hs0 : 0 ≤ (inner ℂ (G - P) P).re := by
    have h1 := habs 0 h0C
    rw [inner_zero_right, Complex.zero_re, abs_zero] at h1
    exact h1
  have hcomp : ∀ w ∈ closure (convexHull ℝ (hahnV A B Φ)),
      ‖inner ℂ (G - P) w‖ ≤ (inner ℂ (G - P) P).re := by
    intro w hw
    rcases eq_or_ne (inner ℂ (G - P) w) 0 with h0 | hne
    · rw [h0, norm_zero]; exact hs0
    · have hμ : ‖star (inner ℂ (G - P) w) / (‖inner ℂ (G - P) w‖ : ℂ)‖ = 1 := by
        rw [norm_div, norm_star_complex, Complex.norm_real,
          Real.norm_of_nonneg (norm_nonneg _), div_self (by positivity)]
      have hmem : (star (inner ℂ (G - P) w) / (‖inner ℂ (G - P) w‖ : ℂ)) • w
          ∈ closure (convexHull ℝ (hahnV A B Φ)) := hunitC _ hμ w hw
      have h1 := habs _ hmem
      have h2 : (inner ℂ (G - P) ((star (inner ℂ (G - P) w)
            / (‖inner ℂ (G - P) w‖ : ℂ)) • w)).re = ‖inner ℂ (G - P) w‖ := by
        rw [inner_smul_right]
        have hz : (star (inner ℂ (G - P) w) / (‖inner ℂ (G - P) w‖ : ℂ))
            * inner ℂ (G - P) w = ((‖inner ℂ (G - P) w‖ : ℝ) : ℂ) := by
          have hz0 : (‖inner ℂ (G - P) w‖ : ℂ) ≠ 0 := by
            intro hc
            exact hne (norm_eq_zero.mp (Complex.ofReal_eq_zero.mp hc))
          rw [div_mul_eq_mul_div, ← starRingEnd_apply, Complex.conj_mul']
          field_simp
        rw [hz, Complex.ofReal_re]
      rw [h2] at h1
      rwa [abs_of_nonneg (norm_nonneg _)] at h1
  have hs_pos : 0 < (inner ℂ (G - P) P).re := by
    rcases lt_or_eq_of_le hs0 with hlt | h
    · exact hlt
    exfalso
    have hzero : ∀ w ∈ closure (convexHull ℝ (hahnV A B Φ)), inner ℂ (G - P) w = 0 := by
      intro w hw
      have h1 := hcomp w hw
      rw [← h] at h1
      exact norm_eq_zero.mp (le_antisymm h1 (norm_nonneg _))
    have hall : ∀ x : ℤ, (G - P) x = 0 := by
      intro x
      have hmem : ((A : ℂ)) • eZ x ∈ closure (convexHull ℝ (hahnV A B Φ)) :=
        mem_closure_convexHull (Or.inr (MemL1Ball.smul_eZ hA x))
      have h1 := hzero _ hmem
      rw [inner_smul_right, inner_eZ] at h1
      have h2 : star ((G - P) x) = 0 := by
        rcases mul_eq_zero.mp h1 with h3 | h3
        · exact absurd h3 (by simp [Complex.ofReal_eq_zero, ne_of_gt hA])
        · exact h3
      simpa using congrArg star h2
    refine hfne ?_
    apply Subtype.ext
    funext x
    exact hall x
  have htpos : 0 < A / (inner ℂ (G - P) P).re := div_pos hA hs_pos
  set F : L2Z := ((A / (inner ℂ (G - P) P).re : ℝ) : ℂ) • (G - P) with hFdef
  have hsmallC : ∀ w ∈ closure (convexHull ℝ (hahnV A B Φ)), ‖inner ℂ F w‖ ≤ A := by
    intro w hw
    have h1 : inner ℂ F w = ((A / (inner ℂ (G - P) P).re : ℝ) : ℂ) * inner ℂ (G - P) w := by
      rw [hFdef, inner_smul_left, Complex.conj_ofReal]
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    calc A / (inner ℂ (G - P) P).re * ‖inner ℂ (G - P) w‖
        ≤ A / (inner ℂ (G - P) P).re * (inner ℂ (G - P) P).re := by
          gcongr; exact hcomp w hw
      _ = A := div_mul_cancel₀ A hs_pos.ne'
  have hφ : ∀ φ ∈ Φ, ‖inner ℂ F φ‖ ≤ B := by
    intro φ hφ
    have hmem := hsmallC _ (mem_closure_convexHull (hahnV_smul_phi hA hB hφ))
    rw [inner_smul_right, norm_mul, norm_phi_scalar hA hB] at hmem
    have h1 : (A / B) * ‖inner ℂ F φ‖ ≤ (A / B) * B := by
      rw [div_mul_cancel₀ A hB.ne']
      exact hmem
    exact le_of_mul_le_mul_left h1 (div_pos hA hB)
  have hunit : ∀ x : ℤ, ‖F x‖ ≤ 1 := by
    intro x
    have hmem : ((A : ℂ)) • eZ x ∈ closure (convexHull ℝ (hahnV A B Φ)) :=
      mem_closure_convexHull (Or.inr (MemL1Ball.smul_eZ hA x))
    have h1 := hsmallC _ hmem
    rw [inner_smul_right, inner_eZ, norm_mul, norm_star_complex, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hA] at h1
    have h2 : A * ‖F x‖ ≤ A * 1 := by simpa using h1
    exact le_of_mul_le_mul_left h2 hA
  have hbig : A < ‖inner ℂ F G‖ := by
    have hsplit : inner ℂ F G = ((A / (inner ℂ (G - P) P).re : ℝ) : ℂ) *
        (inner ℂ (G - P) P + inner ℂ (G - P) (G - P)) := by
      rw [hFdef, inner_smul_left, Complex.conj_ofReal, ← inner_add_right,
        show P + (G - P) = G from by abel]
    have hre : (inner ℂ F G).re = A + A / (inner ℂ (G - P) P).re * ‖G - P‖ ^ 2 := by
      have h3 : (inner ℂ F G).re = (A / (inner ℂ (G - P) P).re) * (inner ℂ (G - P) P).re
          + (A / (inner ℂ (G - P) P).re) * ‖G - P‖ ^ 2 := by
        rw [hsplit, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.ofReal_re,
          Complex.add_re]
        rw [← inner_real_eq_re (G - P) (G - P), real_inner_self_eq_norm_sq]
        ring
      rw [h3, div_mul_cancel₀ A hs_pos.ne']
    have h1 : A < (inner ℂ F G).re := by
      rw [hre]
      have h2 : 0 < A / (inner ℂ (G - P) P).re * ‖G - P‖ ^ 2 := mul_pos htpos (pow_pos hfnn 2)
      linarith
    exact lt_of_lt_of_le h1 (Complex.re_le_norm _)
  obtain ⟨φ, hφΦ, hφB⟩ := h F hunit hbig
  exact absurd (hφ φ hφΦ) (not_le.mpr hφB)


/-! ## The decomposition form of Lemma `hahn` (Corollary `struct` of §5) -/

theorem MemL1Ball.add {A₁ A₂ : ℝ} {f g : L2Z} (hf : MemL1Ball A₁ f) (hg : MemL1Ball A₂ g) :
    MemL1Ball (A₁ + A₂) (f + g) := by
  obtain ⟨hs, hle⟩ := hf
  obtain ⟨hs', hle'⟩ := hg
  have hbound : ∀ x : ℤ, ‖(f + g) x‖ ≤ ‖f x‖ + ‖g x‖ := fun x => norm_add_le _ _
  have hsum : Summable fun x : ℤ => ‖f x‖ + ‖g x‖ := hs.add hs'
  have hsup : Summable fun x : ℤ => ‖(f + g) x‖ :=
    Summable.of_nonneg_of_le (fun x => norm_nonneg _) hbound hsum
  refine ⟨hsup, ?_⟩
  calc ∑' x : ℤ, ‖(f + g) x‖ ≤ ∑' x : ℤ, (‖f x‖ + ‖g x‖) := hsup.tsum_le_tsum hbound hsum
    _ = (∑' x : ℤ, ‖f x‖) + ∑' x : ℤ, ‖g x‖ := hs.tsum_add hs'
    _ ≤ A₁ + A₂ := add_le_add hle hle'

theorem MemL1Ball.sum {ι : Type*} (s : Finset ι) (A : ι → ℝ) {f : ι → L2Z}
    (hf : ∀ i ∈ s, MemL1Ball (A i) (f i)) :
    MemL1Ball (∑ i ∈ s, A i) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using memL1Ball_zero (le_refl (0 : ℝ))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem MemL1Ball.smul_of_nonneg {A : ℝ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {f : L2Z}
    (hf : MemL1Ball A f) : MemL1Ball (c * A) ((c : ℂ) • f) := by
  obtain ⟨hs, hle⟩ := hf
  have hpt : ∀ x : ℤ, ‖(((c : ℂ)) • f : L2Z) x‖ = c * ‖f x‖ := fun x => by
    rw [show (((c : ℂ)) • f : L2Z) x = (c : ℂ) * f x from rfl, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hc0]
  refine ⟨(hs.mul_left c).congr fun x => (hpt x).symm, ?_⟩
  rw [tsum_congr hpt, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hle hc0

/-- **The decomposition form of Lemma `hahn`.**  `V` splits into the dilates of the family `Φ`
and the `ℓ¹`-ball; an element of the closed convex hull is therefore (up to an arbitrarily small
`ℓ²` error `e₂`) a finite combination of dilates of `Φ` plus an `ℓ¹`-small term `e₁`.  This is the
decomposition produced by Corollary `struct` of §5. -/
theorem hahn_decomposition {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (G : L2Z) (Φ : Set L2Z)
    (h : ∀ f : L2Z, (∀ x : ℤ, ‖f x‖ ≤ 1) → A < ‖inner ℂ f G‖ → ∃ φ ∈ Φ, B < ‖inner ℂ f φ‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (s : Finset ι) (φ : ι → L2Z) (lam : ι → ℂ) (w : ι → ℝ)
      (e₁ e₂ : L2Z),
      (∀ i ∈ s, φ i ∈ Φ) ∧ (∀ i ∈ s, ‖lam i‖ ≤ A / B) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i ≤ 1) ∧
      MemL1Ball A e₁ ∧ ‖e₂‖ ≤ ε ∧
      G = (∑ i ∈ s, w i • (lam i • φ i)) + e₁ + e₂ := by
  classical
  have hG := hahn_structure hA hB G Φ h
  obtain ⟨g₀, hg₀, hdist⟩ := Metric.mem_closure_iff.mp hG ε hε
  have hdist' : ‖G - g₀‖ ≤ ε := le_of_lt (by rwa [dist_eq_norm] at hdist)
  rw [mem_convexHull_iff_exists_fintype] at hg₀
  obtain ⟨ι, hι, w, z, hw, hsum, hz, hx⟩ := hg₀
  let good : ι → Prop := fun i => ∃ p : L2Z × ℂ, p.1 ∈ Φ ∧ ‖p.2‖ ≤ A / B ∧ z i = p.2 • p.1
  have hgood : ∀ i, good i ∨ MemL1Ball A (z i) := by
    intro i
    rcases hz i with ⟨φ, hφ, lam, hlam, hzi⟩ | h
    · exact Or.inl ⟨(φ, lam), hφ, hlam, hzi⟩
    · exact Or.inr h
  have hchr : ∀ i, good i → ∃ p : L2Z × ℂ, p.1 ∈ Φ ∧ ‖p.2‖ ≤ A / B ∧ z i = p.2 • p.1 :=
    fun i h => h
  let φf : ι → L2Z := fun i => if h : good i then (Classical.choose (hchr i h)).1 else 0
  let lamf : ι → ℂ := fun i => if h : good i then (Classical.choose (hchr i h)).2 else 0
  have hspec : ∀ i (h : good i), (Classical.choose (hchr i h)).1 ∈ Φ ∧
      ‖(Classical.choose (hchr i h)).2‖ ≤ A / B ∧ z i = (Classical.choose (hchr i h)).2 •
        (Classical.choose (hchr i h)).1 := fun i h => Classical.choose_spec (hchr i h)
  have hw1 : ∀ i, w i ≤ 1 := by
    intro i
    have h1 : w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
    rwa [hsum] at h1
  -- the identity `g₀ = Φ-part + ℓ¹-part`
  have hΦe : (∑ i ∈ Finset.univ.filter good, w i • z i)
      = ∑ i ∈ Finset.univ.filter good, w i • (lamf i • φf i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have h : good i := (Finset.mem_filter.mp hi).2
    have hzi : z i = lamf i • φf i := by
      simp only [lamf, φf, dif_pos h]
      exact (hspec i h).2.2
    rw [hzi]
  have hsplit : g₀ = (∑ i ∈ Finset.univ.filter good, w i • (lamf i • φf i))
      + ∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i • z i := by
    rw [← hx, ← Finset.sum_filter_add_sum_filter_not Finset.univ good (fun i => w i • z i),
      hΦe]
  -- the `ℓ¹` small part
  have he₁ : MemL1Ball A (∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i • z i) := by
    have h1 : MemL1Ball (∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i * A)
        (∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i • z i) := by
      refine MemL1Ball.sum (Finset.univ.filter (fun i => ¬ good i)) (fun i => w i * A)
        fun i hi => ?_
      rcases hgood i with h | h
      · exact absurd h (Finset.mem_filter.mp hi).2
      · exact h.smul_of_nonneg (hw i) (hw1 i)
    have h3 : ∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i ≤ 1 := by
      calc ∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i ≤ ∑ i ∈ Finset.univ, w i :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun i _ _ => hw i)
        _ = 1 := hsum
    have h2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i * A ≤ A := by
      calc ∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i * A
          = (∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i) * A := (Finset.sum_mul ..).symm
        _ ≤ 1 * A := by gcongr
        _ = A := one_mul A
    exact ⟨h1.1, h1.2.trans h2⟩
  refine ⟨ι, hι, Finset.univ.filter good, φf, lamf, w,
    ∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i • z i,
    G - (∑ i ∈ Finset.univ.filter good, w i • (lamf i • φf i))
      - ∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i • z i, ?_, ?_, hw,
    le_of_eq hsum, he₁, ?_, ?_⟩
  · intro i hi
    have h : good i := (Finset.mem_filter.mp hi).2
    simp only [φf, dif_pos h]
    exact (hspec i h).1
  · intro i hi
    have h : good i := (Finset.mem_filter.mp hi).2
    simp only [lamf, dif_pos h]
    exact (hspec i h).2.1
  · have : G - (∑ i ∈ Finset.univ.filter good, w i • (lamf i • φf i))
        - ∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i • z i = G - g₀ := by
      rw [hsplit]; abel
    rw [this]; exact hdist'
  · have : (∑ i ∈ Finset.univ.filter good, w i • (lamf i • φf i))
        + (∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i • z i)
        + (G - (∑ i ∈ Finset.univ.filter good, w i • (lamf i • φf i))
          - ∑ i ∈ Finset.univ.filter (fun i => ¬ good i), w i • z i) = G := by abel
    exact this.symm

end Work.KMTAreas.A4
