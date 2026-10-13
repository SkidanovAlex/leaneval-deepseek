import Mathlib
import Submission.Work.WilC4.ULPMRoute
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.pb_exponent_rational
import Submission.Work.WilC4.unifFinite_of_omin
import Submission.Work.WilC4.ClusterER_definable_self
import Submission.Work.WilC4.Diag_definable
import Submission.Work.WilC4.candidate_bound

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4

open Work.WilC4.Route

variable {k : ℕ}

/-! ## Elementary facts about the cluster exponent set

A cluster value `ρ` is non-negative: on the deep interval the fibre has constant sign
(`deep_sign`), so the doubling ratio `f(2t)/f(t)` is positive, and the witness condition
`|f(2t)/f(t) - ρ| ≤ 1/β` then forces `ρ ≥ -1/β` for arbitrarily large `β`. -/

theorem ClusterER_nonneg {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hgood : GoodFibre Y B₀) {ρ : ℝ} (hρ : ρ ∈ ClusterER Y B₀) : 0 ≤ ρ := by
  by_contra hcon
  have hρneg : ρ < 0 := lt_of_not_ge hcon
  have hnegrho : 0 < -ρ := by linarith
  set β : ℝ := max 2 (1 / (-ρ) + 1) with hβdef
  have hβ2 : 2 ≤ β := le_max_left _ _
  have hβ0 : 0 < β := lt_of_lt_of_le (by norm_num) hβ2
  have hβ1 : 1 ≤ β := le_trans (by norm_num) hβ2
  have hβinv : 1 / β ≤ -ρ := by
    have h : 1 / (-ρ) + 1 ≤ β := le_max_right _ _
    have h1 : 1 / (-ρ) ≤ β := by linarith
    rw [div_le_iff₀ hnegrho] at h1
    rw [div_le_iff₀ hβ0]
    nlinarith [h1]
  obtain ⟨c, x, hx, hdeep, hrat⟩ := hρ β hβ0
  have hxint : x ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := by
    constructor
    · rw [div_lt_iff₀ (by positivity)]; nlinarith
    · nlinarith
  have h2xint : 2 * x ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := by
    constructor
    · rw [div_lt_iff₀ (by positivity)]; nlinarith
    · nlinarith
  obtain ⟨hygr, hyne⟩ := deep_val (hgood := hgood) (β := β) (x := x) hβ1 hx hdeep hxint
  obtain ⟨hy'gr, hy'ne⟩ := deep_val (hgood := hgood) (β := β) (x := x) hβ1 hx hdeep h2xint
  have hwin1 : x / β ≤ x := by rw [div_le_iff₀ hβ0]; nlinarith
  have hwin2 : x ≤ x * β := by nlinarith
  have hrat' := hrat x hwin1 hwin2 (Route.valY Y c x) (Route.valY Y c (2 * x)) hygr hy'gr hyne
  have hsign : 0 < Route.valY Y c x * Route.valY Y c (2 * x) :=
    deep_sign (hgood := hgood) (β := β) (x := x) hβ1 hx hdeep hxint h2xint hygr hy'gr
  have hdiv : 0 < Route.valY Y c (2 * x) / Route.valY Y c x := by
    rcases (mul_pos_iff.mp hsign) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_pos h2 h1
    · exact div_pos_of_neg_of_neg h2 h1
  have hle := (abs_le.mp hrat').2
  linarith

/-! ## The diagonal graph is functional -/

theorem Diag_fibre_unique {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)} {ρ R : ℝ}
    {β y y' : ℝ} (hy : ![β, y] ∈ Diag Y B₀ ρ R) (hy' : ![β, y'] ∈ Diag Y B₀ ρ R) : y = y' := by
  simp only [Diag, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at hy hy'
  have h1 : y ≤ y' := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨z, hzC, hzlt⟩ := hy'.2.2 ε hε
    exact le_trans (hy.2.1 z hzC) (le_of_lt hzlt)
  have h2 : y' ≤ y := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨z, hzC, hzlt⟩ := hy.2.2 ε hε
    exact le_trans (hy'.2.1 z hzC) (le_of_lt hzlt)
  exact le_antisymm h1 h2

/-! ## A countable set that is a finite union of order-convex pieces is finite -/

theorem finite_of_ordConnected_countable {S : Set ℝ}
    (hS : ∃ s : Finset (Set ℝ), (∀ I ∈ s, I.OrdConnected) ∧ S = ⋃₀ (s : Set (Set ℝ)))
    (hcount : S.Countable) : S.Finite := by
  obtain ⟨s, hs, hSeq⟩ := hS
  have hfin : ∀ I ∈ s, I.Finite := by
    intro I hI
    have hIsub : I ⊆ S := by
      intro x hx
      rw [hSeq]
      exact Set.mem_sUnion.mpr ⟨I, hI, hx⟩
    have hcountI : I.Countable := Set.Countable.mono hIsub hcount
    by_contra hnotfin
    have hne : I.Nonempty := by
      by_contra hcon
      exact hnotfin (Set.not_nonempty_iff_eq_empty.mp hcon ▸ Set.finite_empty)
    obtain ⟨x, hx⟩ := hne
    have h2 : ∃ y ∈ I, y ≠ x := by
      by_contra hcon
      push_neg at hcon
      exact hnotfin (Set.Finite.subset (Set.finite_singleton x) (by
        intro z hz
        exact Set.mem_singleton_iff.mpr (hcon z hz)))
    obtain ⟨y, hy, hyx⟩ := h2
    rcases lt_or_gt_of_ne hyx with hlt | hlt
    · have hsub : Set.Icc y x ⊆ I := (hs I hI).out hy hx
      have hc : (Set.Icc y x).Countable := Set.Countable.mono hsub hcountI
      have hc' : x ≤ y := by simpa using hc
      exact absurd hlt (not_lt.mpr hc')
    · have hsub : Set.Icc x y ⊆ I := (hs I hI).out hx hy
      have hc : (Set.Icc x y).Countable := Set.Countable.mono hsub hcountI
      have hc' : y ≤ x := by simpa using hc
      exact absurd hlt (not_lt.mpr hc')
  rw [hSeq]
  simpa [Set.sUnion_eq_biUnion] using Set.Finite.biUnion s.finite_toSet hfin

/-! ## The candidate set is non-empty, and the diagonal is its infimum -/

/-- The candidate set is non-empty as soon as `ρ` is a cluster value: the value `f_c(xβ)/f_c(x)`
at a witness is a candidate. -/
theorem Cand_nonempty {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hgood : GoodFibre Y B₀) {ρ : ℝ} (hρ : ρ ∈ ClusterER Y B₀) {β : ℝ} (hβ : 1 ≤ β) :
    (Cand Y B₀ ρ β).Nonempty := by
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos hβ
  obtain ⟨c, x, hx, hdeep, hrat⟩ := hρ β hβ0
  have hxx0 : x / (2 * β) < x := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hxle : x ≤ x * β := by nlinarith
  have hxβle : x * β < 2 * β * x := by nlinarith [mul_pos hx hβ0]
  have hxint : x ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := ⟨hxx0, by linarith⟩
  have hxβint : x * β ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := ⟨by linarith, hxβle⟩
  obtain ⟨hu, hune⟩ := deep_val (hgood := hgood) (β := β) (x := x) hβ hx hdeep hxint
  obtain ⟨hv, -⟩ := deep_val (hgood := hgood) (β := β) (x := x) hβ hx hdeep hxβint
  refine ⟨Route.valY Y c (x * β) / Route.valY Y c x, c, x, ⟨hx, hdeep, hrat⟩, ?_⟩
  exact ⟨Route.valY Y c x, Route.valY Y c (x * β), hu, hv, div_mul_cancel₀ _ hune⟩

/-- A non-empty set of candidates bounded below has its infimum realised by a point of `Diag`. -/
theorem exists_mem_Diag {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)} {ρ R β A : ℝ}
    (hβR : R ≤ β) (hne : (Cand Y B₀ ρ β).Nonempty)
    (hA : ∀ y ∈ Cand Y B₀ ρ β, A ≤ y) :
    ∃ y : ℝ, ![β, y] ∈ Diag Y B₀ ρ R := by
  have hbdd : BddBelow (Cand Y B₀ ρ β) := ⟨A, fun y hy => hA y hy⟩
  refine ⟨sInf (Cand Y B₀ ρ β), ?_⟩
  have h1 : ∀ y ∈ Cand Y B₀ ρ β, sInf (Cand Y B₀ ρ β) ≤ y :=
    fun y hy => csInf_le hbdd hy
  have h2 : ∀ ε : ℝ, 0 < ε → ∃ y ∈ Cand Y B₀ ρ β, y < sInf (Cand Y B₀ ρ β) + ε := by
    intro ε hε
    by_contra hcon
    push_neg at hcon
    have : sInf (Cand Y B₀ ρ β) + ε ≤ sInf (Cand Y B₀ ρ β) :=
      le_csInf hne (fun y hy => hcon y hy)
    linarith
  simp only [Diag, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact ⟨hβR, h1, h2⟩

/-- The value of `Diag` at `β` lies between the bounds of the candidate set. -/
theorem Diag_bounds {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)} {ρ R A B β y : ℝ}
    (hA : ∀ z ∈ Cand Y B₀ ρ β, A ≤ z) (hB : ∀ z ∈ Cand Y B₀ ρ β, z ≤ B)
    (hy : ![β, y] ∈ Diag Y B₀ ρ R) : A ≤ y ∧ y ≤ B := by
  simp only [Diag, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at hy
  obtain ⟨z, hzC, _⟩ := hy.2.2 1 (by norm_num)
  constructor
  · by_contra hcon
    push_neg at hcon
    obtain ⟨w, hwC, hwlt⟩ := hy.2.2 (A - y) (by linarith)
    exact absurd (hA w hwC) (not_le.mpr (by linarith : w < A))
  · exact le_trans (hy.2.1 z hzC) (hB z hzC)

/-! ## The exponent `logb 2 ρ` is rational

Given the bound on the candidate set, the diagonal graph is a definable graph on a ray whose
values are `≍ β ^ logb 2 ρ`; `pb_exponent_rational` then gives rationality. -/

theorem logb_rat_of_candidate_bound {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    {ρ : ℝ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (hZdef : ∀ R : ℝ, (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Diag Y B₀ ρ R))
    (hne : ∀ β : ℝ, 1 ≤ β → (Cand Y B₀ ρ β).Nonempty)
    (hbound : ∃ C : ℝ, 1 ≤ C ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ y ∈ Cand Y B₀ ρ β,
        C⁻¹ * β ^ (Real.logb 2 ρ) ≤ y ∧ y ≤ C * β ^ (Real.logb 2 ρ)) :
    ∃ q : ℚ, Real.logb 2 ρ = q := by
  obtain ⟨C, hC1, β₀, hbound⟩ := hbound
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1
  set R : ℝ := max β₀ 1 with hRdef
  have hRβ : β₀ ≤ R := le_max_left _ _
  have hR1 : 1 ≤ R := le_max_right _ _
  refine pb_exponent_rational hR hPB (Y := Diag Y B₀ ρ R) (hZdef R) ?_ ?_
    (Real.logb 2 ρ) C hC1 ?_
  · intro x y y' hy hy'
    exact Diag_fibre_unique hy hy'
  · intro R'
    have hR1' : 1 ≤ max R' R := le_trans hR1 (le_max_right _ _)
    have hRβ' : β₀ ≤ max R' R := le_trans hRβ (le_max_right _ _)
    obtain ⟨y, hy⟩ := exists_mem_Diag (β := max R' R) (R := R) (le_max_right _ _)
      (hne _ hR1') (fun z hz => (hbound _ hRβ' z hz).1)
    exact ⟨max R' R, y, le_max_left _ _, hy⟩
  · refine ⟨R, fun β y hβ hy => ?_⟩
    have hb1 : β₀ ≤ β := le_trans hRβ hβ
    have hbβ1 : 1 ≤ β := le_trans hR1 hβ
    have hβ0 : 0 < β := lt_of_lt_of_le one_pos hbβ1
    obtain ⟨hA, hB⟩ := Diag_bounds (β := β) (A := C⁻¹ * β ^ (Real.logb 2 ρ))
      (B := C * β ^ (Real.logb 2 ρ))
      (fun z hz => (hbound β hb1 z hz).1) (fun z hz => (hbound β hb1 z hz).2) hy
    have hAp : 0 < C⁻¹ * β ^ (Real.logb 2 ρ) := by
      have h1 : 0 < C⁻¹ := inv_pos.mpr hCpos
      have h2 : 0 < β ^ (Real.logb 2 ρ) := Real.rpow_pos_of_pos hβ0 _
      positivity
    rw [abs_of_pos (lt_of_lt_of_le hAp hA)]
    exact ⟨hA, hB⟩

/-! ## The candidate values are positive -/

theorem Cand_pos {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hgood : GoodFibre Y B₀) {ρ : ℝ} (hρ : ρ ∈ ClusterER Y B₀) {β y : ℝ} (hβ : 1 ≤ β)
    (hy : y ∈ Cand Y B₀ ρ β) : 0 < y := by
  obtain ⟨c, x, hwit, u, v, hux, hvx, hyu⟩ := hy
  obtain ⟨hx, hdeep, -⟩ := hwit
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos hβ
  have h1 : x / (2 * β) < x := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hxint : x ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := ⟨h1, by nlinarith⟩
  have hxle : x ≤ x * β := by nlinarith
  have hxβint : x * β ∈ Set.Ioo (x / (2 * β)) (2 * β * x) :=
    ⟨by linarith, by nlinarith [mul_pos hx hβ0]⟩
  have hsign : 0 < u * v :=
    deep_sign (hgood := hgood) (β := β) (x := x) hβ hx hdeep hxint hxβint hux hvx
  have hune : u ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hsign
    exact lt_irrefl 0 hsign
  have hyv : y = v / u := (eq_div_iff hune).mpr hyu
  rw [hyv]
  rcases (mul_pos_iff.mp hsign) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact div_pos h2 h1
  · exact div_pos_of_neg_of_neg h2 h1

theorem ulpm_E_finite {k : ℕ} (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hOM : WilkiesDesign.CG.OMinModels) (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y → Work.WilC4.Route.Gr Y c x y' → y = y')
    (B₀ : Set (Fin (k + 1) → ℝ)) (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀)
    (hgood : ∀ (c : Fin k → ℝ) (a b : ℝ), a < b → (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀) →
      (∀ x ∈ Set.Ioo a b, ∃! y : ℝ, Work.WilC4.Route.Gr Y c x y) ∧
      (∀ x ∈ Set.Ioo a b, ∀ y : ℝ, Work.WilC4.Route.Gr Y c x y → y ≠ 0) ∧
      (∀ x ∈ Set.Ioo a b, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ Set.Ioo a b,
        ∀ y y' : ℝ, |x' - x| < δ → Work.WilC4.Route.Gr Y c x y →
        Work.WilC4.Route.Gr Y c x' y' → |y' - y| < ε)) :
    (Work.WilC4.Route.ClusterE Y B₀).Finite := by
  have hgf : GoodFibre Y B₀ := hgood
  -- `ClusterER` is definable
  have hERdef : (∅ : Set ℝ).Definable₁ WilkiesDesign.CG.LRc (ClusterER Y B₀) :=
    ClusterER_definable_self Y B₀ hY hB₀
  -- the candidate bound, in the form used below
  have hcand : ∀ ρ ∈ ClusterER Y B₀, 0 < ρ → ∃ C : ℝ, 1 ≤ C ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ y ∈ Cand Y B₀ ρ β,
        C⁻¹ * β ^ (Real.logb 2 ρ) ≤ y ∧ y ≤ C * β ^ (Real.logb 2 ρ) := by
    intro ρ hρ hρ0
    obtain ⟨C, hC, β₀, hb⟩ := candidate_bound hOM Y hY hfun B₀ hB₀ hgf hρ hρ0
    refine ⟨C, hC, max β₀ 1, fun β hβ y hy => ?_⟩
    have hβ1 : 1 ≤ β := le_trans (le_max_right _ _) hβ
    have hβb : β₀ ≤ β := le_trans (le_max_left _ _) hβ
    obtain ⟨h1, h2⟩ := hb β hβb y hy
    have hypos : 0 < y := Cand_pos hgf hρ hβ1 hy
    rw [abs_of_pos hypos] at h1 h2
    exact ⟨h1, h2⟩
  -- every cluster value is `0` or a power of two with rational exponent
  have hsub : ClusterER Y B₀ ⊆ ({0} : Set ℝ) ∪ Set.range (fun q : ℚ => (2 : ℝ) ^ (q : ℝ)) := by
    intro ρ hρ
    rcases eq_or_lt_of_le (ClusterER_nonneg hgf hρ) with h0 | hpos
    · exact Or.inl h0.symm
    · refine Or.inr ?_
      obtain ⟨q, hq⟩ := logb_rat_of_candidate_bound hR hPB
        (fun R => Diag_definable Y B₀ hY hB₀ ρ R)
        (fun β hβ => Cand_nonempty hgf hρ hβ) (hcand ρ hρ hpos)
      refine ⟨q, ?_⟩
      show (2 : ℝ) ^ (q : ℝ) = ρ
      rw [← hq]
      exact Real.rpow_logb (b := 2) (x := ρ) (by norm_num) (by norm_num) hpos
  -- countability and o-minimality
  have hcount : (ClusterER Y B₀).Countable := by
    refine Set.Countable.mono hsub ?_
    exact Set.Countable.union (Set.finite_singleton (0 : ℝ)).countable
      (Set.countable_range fun q : ℚ => (2 : ℝ) ^ (q : ℝ))
  obtain ⟨s, hs, hSeq⟩ := oMin_ordConnected_set_local hOM hERdef
  have hERfin : (ClusterER Y B₀).Finite := finite_of_ordConnected_countable ⟨s, hs, hSeq⟩ hcount
  exact hERfin.subset (ClusterE_subset_ClusterER Y B₀)

end Work.WilC4
