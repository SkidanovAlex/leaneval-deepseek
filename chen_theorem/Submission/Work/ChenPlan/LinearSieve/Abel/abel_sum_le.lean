import Mathlib
import Submission.Work.ChenPlan.LinearSieve.FrameworkR
import Submission.Work.ChenPlan.LinearSieve.Abel.telescoping
import Submission.Work.ChenPlan.LinearSieve.Abel.abel_step_sum
import Submission.Work.ChenPlan.LinearSieve.Abel.integral_step_bound

/-!
# The Abel/partial-summation bound for the linear sieve

`Work.ChenPlan.LinearSieve.Abel.abel_sum_le` : the weighted prime sum

`Σ_{w ≤ p < Z} ν(p) · VfR A p · Φ(p)`

is dominated by the endpoint term `(K-1)Φ(Z)` plus the logarithmic integral
`∫_w^Z Φ(u) log Z /(u log²u) du`, using only the pointwise hypothesis
`VfR A u ≤ K · VfR A Z · log Z/log u` (`u ∈ [w,Z]`).

Route: split the finite sum with the telescoping (Abel) identity, writing the jumps of the
normalised product `u ↦ VfR A u/(K VfR A Z)`; compare the jumps with the corresponding jumps of
`u ↦ log Z/log u` (`abel_step_sum`), and bound the latter by the integral
(`integral_step_bound`). -/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.Abel

/-- Splitting `VfR` at a real cut `u ≤ v`. -/
theorem VfR_split (A : BoundingSieve) {u v : ℝ} (h : u ≤ v) :
    VfR A v = VfR A u *
      ∏ q ∈ A.prodPrimes.primeFactors.filter (fun q : ℕ => u ≤ (q : ℝ) ∧ (q : ℝ) < v),
        (1 - A.nu q) := by
  unfold VfR
  have hsplit : (A.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < v))
      = (A.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < u))
        ∪ (A.prodPrimes.primeFactors.filter (fun q : ℕ => u ≤ (q : ℝ) ∧ (q : ℝ) < v)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hq, hqv⟩
      by_cases hqu : (q : ℝ) < u
      · exact Or.inl ⟨hq, hqu⟩
      · exact Or.inr ⟨hq, not_lt.mp hqu, hqv⟩
    · rintro (⟨hq, hqu⟩ | ⟨hq, hqu, hqv⟩)
      · exact ⟨hq, lt_of_lt_of_le hqu h⟩
      · exact ⟨hq, hqv⟩
  have hdisj : Disjoint (A.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < u))
      (A.prodPrimes.primeFactors.filter (fun q : ℕ => u ≤ (q : ℝ) ∧ (q : ℝ) < v)) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    simp only [Finset.mem_filter] at hq1 hq2
    exact absurd hq1.2 (not_lt.mpr hq2.2.1)
  rw [hsplit, Finset.prod_union hdisj]

/-! ## The increasing enumeration of a finset of naturals -/

/-- The increasing enumeration `p_0 < p_1 < ⋯` of a finset `S ⊆ ℕ`, extended past the last index
by the constant value `Z`. -/
noncomputable def enumExt (S : Finset ℕ) (Z : ℝ) (k : ℕ) : ℝ :=
  if h : k < S.card then (((S.orderIsoOfFin rfl) ⟨k, h⟩ : ℕ) : ℝ) else Z

theorem enumExt_apply {S : Finset ℕ} {Z : ℝ} {k : ℕ} (h : k < S.card) :
    enumExt S Z k = (((S.orderIsoOfFin rfl) ⟨k, h⟩ : ℕ) : ℝ) :=
  dif_pos h

theorem enumExt_of_ge {S : Finset ℕ} {Z : ℝ} {k : ℕ} (h : S.card ≤ k) : enumExt S Z k = Z :=
  dif_neg (by omega)

theorem enumExt_mono {S : Finset ℕ} {Z : ℝ} (hSZ : ∀ p ∈ S, (p : ℝ) ≤ Z) :
    Monotone (enumExt S Z) := by
  intro a b hab
  rcases lt_or_ge b S.card with hb | hb
  · have ha : a < S.card := lt_of_le_of_lt hab hb
    rw [enumExt_apply ha, enumExt_apply hb]
    exact_mod_cast (S.orderIsoOfFin rfl).monotone (show (⟨a, ha⟩ : Fin S.card) ≤ ⟨b, hb⟩ from hab)
  · rw [enumExt_of_ge hb]
    rcases lt_or_ge a S.card with ha | ha
    · rw [enumExt_apply ha]
      exact hSZ _ ((S.orderIsoOfFin rfl) ⟨a, ha⟩).2
    · rw [enumExt_of_ge ha]

theorem enumExt_le_Z {S : Finset ℕ} {Z : ℝ} (hSZ : ∀ p ∈ S, (p : ℝ) < Z) :
    ∀ k, enumExt S Z k ≤ Z := by
  intro k
  rcases lt_or_ge k S.card with hk | hk
  · rw [enumExt_apply hk]
    exact le_of_lt (hSZ _ ((S.orderIsoOfFin rfl) ⟨k, hk⟩).2)
  · rw [enumExt_of_ge hk]

theorem enumExt_ge {S : Finset ℕ} {Z w : ℝ} (hSw : ∀ p ∈ S, w ≤ (p : ℝ)) (hwZ : w ≤ Z) :
    ∀ k, w ≤ enumExt S Z k := by
  intro k
  rcases lt_or_ge k S.card with hk | hk
  · rw [enumExt_apply hk]
    exact hSw _ ((S.orderIsoOfFin rfl) ⟨k, hk⟩).2
  · rw [enumExt_of_ge hk]
    exact hwZ

theorem enumExt_self (S : Finset ℕ) (Z : ℝ) : enumExt S Z S.card = Z :=
  enumExt_of_ge le_rfl

/-- Any element of `S` lying below the `(i+1)`-st element of the extended enumeration is at most
the `i`-th element of `S`. -/
theorem enumExt_le_enum {S : Finset ℕ} {Z : ℝ} (i : Fin S.card) {q : ℕ} (hq : q ∈ S)
    (h : (q : ℝ) < enumExt S Z ((i : ℕ) + 1)) :
    q ≤ (((S.orderIsoOfFin rfl) i : ↥S) : ℕ) := by
  have hjj : (((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨q, hq⟩) : ↥S) : ℕ) = q := by
    rw [OrderIso.apply_symm_apply]
  rcases lt_or_ge ((i : ℕ) + 1) S.card with hlt | hge
  · rw [enumExt_apply hlt] at h
    have hnat : q < (((S.orderIsoOfFin rfl) ⟨(i : ℕ) + 1, hlt⟩ : ↥S) : ℕ) := by
      exact_mod_cast h
    have h5 : (((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨q, hq⟩) : ↥S) : ℕ)
        < (((S.orderIsoOfFin rfl) ⟨(i : ℕ) + 1, hlt⟩ : ↥S) : ℕ) := by
      rw [hjj]
      exact hnat
    have hlt2 : (S.orderIsoOfFin rfl).symm ⟨q, hq⟩ < (⟨(i : ℕ) + 1, hlt⟩ : Fin S.card) :=
      ((S.orderIsoOfFin rfl).lt_iff_lt).mp h5
    have h3 : ((S.orderIsoOfFin rfl).symm ⟨q, hq⟩ : ℕ) ≤ (i : ℕ) := by
      have h4 : ((S.orderIsoOfFin rfl).symm ⟨q, hq⟩ : ℕ) < (i : ℕ) + 1 := hlt2
      omega
    have hle : (S.orderIsoOfFin rfl).symm ⟨q, hq⟩ ≤ i := Fin.le_iff_val_le_val.mpr h3
    have h6 : (((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨q, hq⟩) : ↥S) : ℕ)
        ≤ (((S.orderIsoOfFin rfl) i : ↥S) : ℕ) := (S.orderIsoOfFin rfl).monotone hle
    rw [hjj] at h6
    exact h6
  · have hival : (i : ℕ) + 1 = S.card := by
      have := i.isLt
      omega
    have h3 : ((S.orderIsoOfFin rfl).symm ⟨q, hq⟩ : ℕ) ≤ (i : ℕ) := by
      have h4 : ((S.orderIsoOfFin rfl).symm ⟨q, hq⟩ : ℕ) < S.card :=
        ((S.orderIsoOfFin rfl).symm ⟨q, hq⟩).isLt
      omega
    have hle : (S.orderIsoOfFin rfl).symm ⟨q, hq⟩ ≤ i := Fin.le_iff_val_le_val.mpr h3
    have h6 : (((S.orderIsoOfFin rfl) ((S.orderIsoOfFin rfl).symm ⟨q, hq⟩) : ↥S) : ℕ)
        ≤ (((S.orderIsoOfFin rfl) i : ↥S) : ℕ) := (S.orderIsoOfFin rfl).monotone hle
    rw [hjj] at h6
    exact h6

theorem enumExt_lt_succ {S : Finset ℕ} {Z : ℝ} (hSZ : ∀ p ∈ S, (p : ℝ) < Z) (i : Fin S.card) :
    ((((S.orderIsoOfFin rfl) i : ↥S) : ℕ) : ℝ) < enumExt S Z ((i : ℕ) + 1) := by
  rcases lt_or_ge ((i : ℕ) + 1) S.card with hlt | hge
  · rw [enumExt_apply hlt]
    have h1 : (i : Fin S.card) < (⟨(i : ℕ) + 1, hlt⟩ : Fin S.card) :=
      Fin.lt_def.mpr (Nat.lt_succ_self (i : ℕ))
    have h2 := (S.orderIsoOfFin rfl).strictMono h1
    exact_mod_cast h2
  · rw [enumExt_of_ge hge]
    exact hSZ _ ((S.orderIsoOfFin rfl) i).2

/-! ## Normalisations -/

/-- The normalised sieve product `u ↦ VfR A u / (KV · VfR A Z)`. -/
noncomputable def Mnorm (A : BoundingSieve) (KV Z : ℝ) : ℝ → ℝ :=
  fun u => VfR A u / (KV * VfR A Z)

/-- `u ↦ log Z / log u`. -/
noncomputable def logRatio (Z : ℝ) : ℝ → ℝ := fun u => Real.log Z / Real.log u

/-! ## The main bound -/

theorem abel_sum_le {A : BoundingSieve} {w Z KV : ℝ} (hKV : 1 ≤ KV) (hw : 2 ≤ w) (hwZ : w ≤ Z)
    (hV : ∀ u : ℝ, w ≤ u → u ≤ Z →
      Work.ChenPlan.LinearSieve.VfR A u
        ≤ KV * Work.ChenPlan.LinearSieve.VfR A Z * (Real.log Z / Real.log u))
    {Φ : ℝ → ℝ} (hΦmono : ∀ a b : ℝ, w ≤ a → a ≤ b → b ≤ Z → Φ a ≤ Φ b)
    (hΦnn : ∀ a : ℝ, w ≤ a → a ≤ Z → 0 ≤ Φ a) :
    ∑ p ∈ A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < Z),
        A.nu p * Work.ChenPlan.LinearSieve.VfR A (p : ℝ) * Φ (p : ℝ)
      ≤ Work.ChenPlan.LinearSieve.VfR A Z *
          ((KV - 1) * Φ Z
            + KV * ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u) ^ 2))) := by
  classical
  have h1w : (1 : ℝ) < w := by linarith
  have h1Z : (1 : ℝ) < Z := by linarith
  have hlogZpos : 0 < Real.log Z := Real.log_pos h1Z
  have hVzpos : 0 < VfR A Z := VfR_pos A Z
  have hKVpos : 0 < KV := lt_of_lt_of_le zero_lt_one hKV
  have hKVne : KV ≠ 0 := ne_of_gt hKVpos
  have hcpos : 0 < KV * VfR A Z := mul_pos hKVpos hVzpos
  have hcne : KV * VfR A Z ≠ 0 := ne_of_gt hcpos
  set S : Finset ℕ := A.prodPrimes.primeFactors.filter
    (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < Z) with hSdef
  have hSsub : ∀ p ∈ S, p ∈ A.prodPrimes.primeFactors := by
    intro p hp
    rw [hSdef] at hp
    exact (Finset.mem_filter.mp hp).1
  have hSw : ∀ p ∈ S, w ≤ (p : ℝ) := by
    intro p hp
    rw [hSdef] at hp
    exact (Finset.mem_filter.mp hp).2.1
  have hSZ : ∀ p ∈ S, (p : ℝ) < Z := by
    intro p hp
    rw [hSdef] at hp
    exact (Finset.mem_filter.mp hp).2.2
  have hSZle : ∀ p ∈ S, (p : ℝ) ≤ Z := fun p hp => le_of_lt (hSZ p hp)
  have hPmono : Monotone (enumExt S Z) := enumExt_mono hSZle
  have hP0 : w ≤ enumExt S Z 0 := enumExt_ge hSw hwZ 0
  have hPn : enumExt S Z S.card = Z := enumExt_self S Z
  have hPw : ∀ k, w ≤ enumExt S Z k := enumExt_ge hSw hwZ
  have hPZ : ∀ k, enumExt S Z k ≤ Z := enumExt_le_Z hSZ
  -- the pointwise comparison of the two profiles
  have hMT : ∀ k : ℕ, k ≤ S.card →
      Mnorm A KV Z (enumExt S Z k) ≤ logRatio Z (enumExt S Z k) := by
    intro k hk
    have hwk : w ≤ enumExt S Z k := hPw k
    have hkZ : enumExt S Z k ≤ Z := hPZ k
    have hVk := hV (enumExt S Z k) hwk hkZ
    rw [Mnorm, logRatio, div_le_iff₀ hcpos]
    calc VfR A (enumExt S Z k) ≤ KV * VfR A Z * (Real.log Z / Real.log (enumExt S Z k)) := hVk
      _ = Real.log Z / Real.log (enumExt S Z k) * (KV * VfR A Z) := by ring
  have hstep := abel_step_sum (P := enumExt S Z) (M := Mnorm A KV Z) (T := logRatio Z)
    hPmono hP0 hPn hMT hΦmono hΦnn
  have hint := integral_step_bound (P := enumExt S Z) (Φ := Φ)
    hPmono hw hwZ hP0 hPn hΦmono hΦnn
  have hTZ : logRatio Z Z = 1 := by
    rw [logRatio, div_self (ne_of_gt hlogZpos)]
  have hMZ : Mnorm A KV Z Z = 1 / KV := by
    rw [Mnorm, div_eq_div_iff hcne (ne_of_gt hKVpos)]
    ring
  have hMsum_le : ∑ k ∈ Finset.range S.card,
        (Mnorm A KV Z (enumExt S Z k) - Mnorm A KV Z (enumExt S Z (k + 1)))
          * Φ (enumExt S Z k)
      ≤ (1 - 1 / KV) * Φ Z
        + ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u) ^ 2)) := by
    have hs := hstep
    rw [hTZ, hMZ] at hs
    simp only [logRatio] at hs
    linarith [hs, hint]
  -- the product splitting at consecutive elements
  have hsplit_i : ∀ i : Fin S.card,
      VfR A (enumExt S Z ((i : ℕ) + 1))
        = VfR A (enumExt S Z (i : ℕ))
          * (1 - A.nu (((S.orderIsoOfFin rfl) i : ↥S) : ℕ)) := by
    intro i
    have ha : (i : ℕ) < S.card := i.isLt
    have hPe : enumExt S Z (i : ℕ) = ((((S.orderIsoOfFin rfl) i : ↥S) : ℕ) : ℝ) :=
      enumExt_apply ha
    have hle : enumExt S Z (i : ℕ) ≤ enumExt S Z ((i : ℕ) + 1) := hPmono (by omega)
    have hfil : (A.prodPrimes.primeFactors.filter
        (fun q : ℕ => ((((S.orderIsoOfFin rfl) i : ↥S) : ℕ) : ℝ) ≤ (q : ℝ) ∧
          (q : ℝ) < enumExt S Z ((i : ℕ) + 1)))
        = {(((S.orderIsoOfFin rfl) i : ↥S) : ℕ)} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hqT, hpq, hqlt⟩
        have hvS : (((S.orderIsoOfFin rfl) i : ↥S) : ℕ) ∈ S :=
          ((S.orderIsoOfFin rfl) i).2
        have hqS : q ∈ S := by
          rw [hSdef]
          exact Finset.mem_filter.mpr ⟨hqT,
            le_trans (hSw _ hvS) (by exact_mod_cast hpq),
            lt_of_lt_of_le hqlt (hPZ ((i : ℕ) + 1))⟩
        have h1 : q ≤ (((S.orderIsoOfFin rfl) i : ↥S) : ℕ) := enumExt_le_enum i hqS hqlt
        exact le_antisymm h1 (by exact_mod_cast hpq)
      · intro hq
        subst hq
        exact ⟨hSsub _ ((S.orderIsoOfFin rfl) i).2, le_refl _,
          enumExt_lt_succ hSZ i⟩
    calc VfR A (enumExt S Z ((i : ℕ) + 1))
        = VfR A (enumExt S Z (i : ℕ))
          * ∏ q ∈ A.prodPrimes.primeFactors.filter
              (fun q : ℕ => (enumExt S Z (i : ℕ)) ≤ (q : ℝ) ∧
                (q : ℝ) < enumExt S Z ((i : ℕ) + 1)), (1 - A.nu q) :=
          VfR_split A hle
      _ = VfR A (enumExt S Z (i : ℕ))
          * (1 - A.nu (((S.orderIsoOfFin rfl) i : ↥S) : ℕ)) := by
          rw [hPe, hfil, Finset.prod_singleton]
  -- the reindexing of the sieve sum
  let g₀ : ℕ → ℝ := fun p => A.nu p * VfR A (p : ℝ) * Φ (p : ℝ)
  let ff : ℕ → ℝ := fun k => (Mnorm A KV Z (enumExt S Z k) - Mnorm A KV Z (enumExt S Z (k + 1)))
    * Φ (enumExt S Z k)
  have hterm : ∀ i : Fin S.card,
      g₀ (((S.orderIsoOfFin rfl) i : ↥S) : ℕ) = KV * VfR A Z * ff (i : ℕ) := by
    intro i
    have ha : (i : ℕ) < S.card := i.isLt
    have hPe : enumExt S Z (i : ℕ) = ((((S.orderIsoOfFin rfl) i : ↥S) : ℕ) : ℝ) :=
      enumExt_apply ha
    have hi := hsplit_i i
    simp only [g₀, ff, Mnorm]
    rw [div_sub_div_same, hi, hPe]
    field_simp
    ring
  have hreindex : ∑ p ∈ S, A.nu p * VfR A (p : ℝ) * Φ (p : ℝ)
      = KV * VfR A Z * ∑ k ∈ Finset.range S.card, ff k := by
    have h1 : (∑ p ∈ S, A.nu p * VfR A (p : ℝ) * Φ (p : ℝ)) = ∑ p ∈ S, g₀ p := by
      simp only [g₀]
    have h2 : (∑ p : ↥S, g₀ (p : ℕ))
        = ∑ i : Fin S.card, g₀ (((S.orderIsoOfFin rfl) i : ↥S) : ℕ) :=
      (Equiv.sum_comp (S.orderIsoOfFin rfl).toEquiv (fun p : ↥S => g₀ (p : ℕ))).symm
    have h3 : (∑ i : Fin S.card, g₀ (((S.orderIsoOfFin rfl) i : ↥S) : ℕ))
        = ∑ i : Fin S.card, KV * VfR A Z * ff (i : ℕ) :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    have h4 : (∑ i : Fin S.card, KV * VfR A Z * ff (i : ℕ))
        = KV * VfR A Z * ∑ i : Fin S.card, ff (i : ℕ) := by
      rw [Finset.mul_sum]
    have h5 : (∑ i : Fin S.card, ff (i : ℕ)) = ∑ k ∈ Finset.range S.card, ff k :=
      Fin.sum_univ_eq_sum_range ff S.card
    rw [h1, ← Finset.sum_coe_sort S g₀, h2, h3, h4, h5]
  calc ∑ p ∈ S, A.nu p * VfR A (p : ℝ) * Φ (p : ℝ)
      = KV * VfR A Z * ∑ k ∈ Finset.range S.card, ff k := hreindex
    _ ≤ KV * VfR A Z *
          ((1 - 1 / KV) * Φ Z
            + ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u) ^ 2))) :=
        mul_le_mul_of_nonneg_left hMsum_le (le_of_lt hcpos)
    _ = VfR A Z *
          ((KV - 1) * Φ Z
            + KV * ∫ u in w..Z, Φ u * (Real.log Z / (u * (Real.log u) ^ 2))) := by
        have h2 : KV * VfR A Z * ((1 - 1 / KV) * Φ Z) = VfR A Z * ((KV - 1) * Φ Z) := by
          field_simp
        rw [mul_add, h2]
        ring

end Work.ChenPlan.LinearSieve.Abel
