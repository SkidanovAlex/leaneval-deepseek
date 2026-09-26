import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.sigmaGroupFacts
import Submission.Work.PTCert.rowFormula
import Submission.Work.PTCert.avgMatInvariant
import Submission.Work.PTCert.orbClause
import Submission.Work.PTCert.stabInvPos
import Submission.Work.PTCert.distinctOrbits

/-!
# PTCert — the row facts of `Pmat`

Assembly of `RowFacts` (Glue3) from the semantic hypotheses `CodeFacts`, `ActSetup`,
`NSem`, `TabSem`, `RowSem`, `GroupSem`.

* every element of `EI` is an `Sg`-translate of the row code `x0c (labE 0 x)`;
* the 18 row codes `x0c r` lie in distinct `Sg`-orbits;
* the row label `labE r` is invariant under the stabiliser of `x0_r`.

Then `rowFormula` (Chain.lean), applied to `Umat`, gives the row formula for `Pmat`.
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G
open scoped BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

noncomputable section

/-! ## The 18 rows of the certificate -/

/-- The base points `x0E r pt0` (elements of `EI` with code `x0c r`), `r < 18`. -/
def x0rows : Finset EI := (Finset.range 18).image (fun r => x0E r pt0)

lemma mem_x0rows {z : EI} : z ∈ x0rows ↔ ∃ r < 18, x0E r pt0 = z := by
  simp [x0rows, Finset.mem_image, Finset.mem_range]

/-! ## Basic facts -/

lemma toEI_of_mem {z : ℕ} {x : EI} (h : z ∈ eS) : toEI z x = ⟨z, h⟩ := by
  unfold toEI; rw [dif_pos h]

lemma toEI_val {z : ℕ} {x : EI} (h : z ∈ eS) : (toEI z x).1 = z := by
  rw [toEI_of_mem h]

lemma x0E_val {r : ℕ} (h : x0c r ∈ eS) : (x0E r pt0).1 = x0c r := toEI_val h

lemma x0c_mem_eS (hR : RowSem) (r : ℕ) (hr : r < 18) : x0c r ∈ eS :=
  List.mem_toFinset.mpr (hR.2.1 r hr)

lemma actCode_zero (c : ℕ) : actCode c 0 = 0 := by
  unfold actCode actL normC invLk; simp

lemma x0c_inj (hR : RowSem) : ∀ r < 18, ∀ r' < 18, x0c r = x0c r' → r = r' := by
  intro r hr r' hr' h
  have h1 := hR.2.2.2.1 r hr
  have h2 := hR.2.2.2.1 r' hr'
  rw [h] at h1
  rw [h1] at h2
  exact h2

/-! ## `Sg` as a finite subgroup (from `sigmaGroupFacts`) -/

lemma Sg_one : (1 : G5) ∈ Sg := (sigmaGroupFacts 5).1.1
lemma Sg_mul {s t : G5} (hs : s ∈ Sg) (ht : t ∈ Sg) : s * t ∈ Sg :=
  (sigmaGroupFacts 5).1.2.1 s hs t ht
lemma Sg_inv {s : G5} (hs : s ∈ Sg) : s⁻¹ ∈ Sg := (sigmaGroupFacts 5).1.2.2 s hs

lemma actE_mul (hA : ActSetup) {σ τ : G5} (hσ : σ ∈ Sg) (hτ : τ ∈ Sg) (x : EI) :
    actE (σ * τ) x = actE σ (actE τ x) := hA.2.2.2.1 σ hσ τ hτ x

lemma actE_one_apply (hA : ActSetup) (x : EI) : actE 1 x = x := hA.2.2.2.2.1 x

lemma actE_inv_apply (hA : ActSetup) {σ : G5} (hσ : σ ∈ Sg) (x : EI) :
    actE σ⁻¹ (actE σ x) = x := by
  rw [← actE_mul hA (Sg_inv hσ) hσ x, inv_mul_cancel]
  exact actE_one_apply hA x

/-! ## Row form of `Umat` -/

/-- On the row of a base point `x₀ = x0E r pt0`, `Umat` is just the value table. -/
lemma Umat_rowcode (hR : RowSem) (pv : ℕ → ℤ) {r : ℕ} (hr : r < 18) {x : EI}
    (hx : x.1 = x0c r) (y : EI) :
    Umat pv x y = (pv (keyOf r (labE r y.1)) : ℝ) / (stabCard x : ℝ) := by
  unfold Umat
  have hsum : (∑ r' ∈ Finset.range 18,
        (if x.1 = x0c r' then (pv (keyOf r' (labE r' y.1)) : ℝ) / (stabCard x : ℝ) else 0)) =
      (if x.1 = x0c r then (pv (keyOf r (labE r y.1)) : ℝ) / (stabCard x : ℝ) else 0) :=
    Finset.sum_eq_single r
      (fun r' hr' hne => by
        refine if_neg ?_
        intro hcon
        exact hne (x0c_inj hR r hr r' (Finset.mem_range.mp hr') (by rw [← hx, hcon])).symm)
      (fun hnr => absurd (Finset.mem_range.mpr hr) hnr)
  rw [hsum, if_pos hx]

lemma Umat_support (hR : RowSem) (pv : ℕ → ℤ) :
    ∀ i j : EI, i ∉ x0rows → Umat pv i j = 0 := by
  intro i j hi
  unfold Umat
  apply Finset.sum_eq_zero
  intro r' hr'
  by_cases hc : i.1 = x0c r'
  · refine absurd ?_ hi
    rw [mem_x0rows]
    exact ⟨r', Finset.mem_range.mp hr',
      Subtype.ext (by rw [x0E_val (x0c_mem_eS hR r' (Finset.mem_range.mp hr'))]; exact hc.symm)⟩
  · rw [if_neg hc]

lemma Umat_distinct
    (hDis : ∀ r < 18, ∀ r' < 18, ∀ g ∈ Sg, actE g (x0E r pt0) = x0E r' pt0 → r = r') :
    ∀ x ∈ x0rows, ∀ g ∈ Sg, actE g x ∈ x0rows → actE g x = x := by
  intro x hx g hg hgx
  rw [mem_x0rows] at hx hgx
  obtain ⟨r, hr, hrx⟩ := hx
  obtain ⟨r', hr', hr'x⟩ := hgx
  have hrr : r = r' := hDis r hr r' hr' g hg (by rw [hrx]; exact hr'x.symm)
  rw [← hr'x, ← hrx, hrr]

lemma Umat_stab (hR : RowSem)
    (hLabE0 : ∀ g ∈ Sg, ∀ z : EI, labE 0 (actE g z).1 = labE 0 z.1)
    (hStabPos : ∀ r < 18, 1 ≤ r → ∀ g ∈ Sg, actE g (x0E r pt0) = x0E r pt0 →
      ∀ z, labE r (actE g z).1 = labE r z.1)
    (pv : ℕ → ℤ) :
    ∀ x ∈ x0rows, ∀ g ∈ Sg, actE g x = x → ∀ z, Umat pv x (actE g z) = Umat pv x z := by
  intro x hx g hg hfix z
  rw [mem_x0rows] at hx
  obtain ⟨r, hr, hrx⟩ := hx
  have hxr : x.1 = x0c r := by rw [← hrx, x0E_val (x0c_mem_eS hR r hr)]
  have hfix' : actE g (x0E r pt0) = x0E r pt0 := by rw [hrx]; exact hfix
  have hlab : labE r (actE g z).1 = labE r z.1 := by
    by_cases hr0 : r = 0
    · subst hr0; exact hLabE0 g hg z
    · exact hStabPos r hr (Nat.one_le_iff_ne_zero.mpr hr0) g hg hfix' z
  rw [Umat_rowcode hR pv hr hxr (actE g z), Umat_rowcode hR pv hr hxr z, hlab]

/-! ## `labE 0` is `Sg`-invariant -/

lemma labE0_inv (hA : ActSetup)
    (hOrb : ∀ x : EI, labE 0 x.1 < 18 ∧ ∃ σ ∈ Sg, actE σ (x0E (labE 0 x.1) pt0) = x)
    (hDis : ∀ r < 18, ∀ r' < 18, ∀ g ∈ Sg, actE g (x0E r pt0) = x0E r' pt0 → r = r') :
    ∀ g ∈ Sg, ∀ z : EI, labE 0 (actE g z).1 = labE 0 z.1 := by
  intro g hg z
  obtain ⟨hzl, σz, hσzS, hσz⟩ := hOrb z
  obtain ⟨hwl, σw, hσwS, hσw⟩ := hOrb (actE g z)
  have h1 : x0E (labE 0 (actE g z).1) pt0 = actE σw⁻¹ (actE g z) := by
    conv_rhs => rw [← hσw]
    rw [← actE_mul hA (Sg_inv hσwS) hσwS (x0E (labE 0 (actE g z).1) pt0)]
    rw [inv_mul_cancel]
    exact (actE_one_apply hA _).symm
  have h2 : actE σw⁻¹ (actE g z) = actE ((σw⁻¹ * g) * σz) (x0E (labE 0 z.1) pt0) := by
    calc actE σw⁻¹ (actE g z)
        = actE σw⁻¹ (actE g (actE σz (x0E (labE 0 z.1) pt0))) := by rw [hσz]
      _ = actE σw⁻¹ (actE (g * σz) (x0E (labE 0 z.1) pt0)) := by
            rw [actE_mul hA hg hσzS]
      _ = actE (σw⁻¹ * (g * σz)) (x0E (labE 0 z.1) pt0) :=
            (actE_mul hA (Sg_inv hσwS) (Sg_mul hg hσzS) (x0E (labE 0 z.1) pt0)).symm
      _ = actE ((σw⁻¹ * g) * σz) (x0E (labE 0 z.1) pt0) := by rw [mul_assoc]
  have hy := h1.trans h2
  exact (hDis (labE 0 z.1) hzl (labE 0 (actE g z).1) hwl ((σw⁻¹ * g) * σz)
      (Sg_mul (Sg_mul (Sg_inv hσwS) hg) hσzS) hy.symm).symm

/-! ## Assembly -/

theorem rowFacts_of (hA : ActSetup) (hR : RowSem)
    (hOrb : ∀ x : EI, labE 0 x.1 < 18 ∧ ∃ σ ∈ Sg, actE σ (x0E (labE 0 x.1) pt0) = x)
    (hDis : ∀ r < 18, ∀ r' < 18, ∀ g ∈ Sg, actE g (x0E r pt0) = x0E r' pt0 → r = r')
    (hStabPos : ∀ r < 18, 1 ≤ r → ∀ g ∈ Sg, actE g (x0E r pt0) = x0E r pt0 →
      ∀ z, labE r (actE g z).1 = labE r z.1) :
    RowFacts := by
  intro pv
  have hLabE0 := labE0_inv hA hOrb hDis
  have hsupp := Umat_support hR pv
  have hdist := Umat_distinct hDis
  have hstab := Umat_stab hR hLabE0 hStabPos pv
  have hSg : IsFinSubgroup Sg := (sigmaGroupFacts 5).1
  have hCA : ConjAction Sg fE actE := hA.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro r hr x y hx
    have hrows : x ∈ x0rows := by
      rw [mem_x0rows]
      exact ⟨r, hr, Subtype.ext (by rw [x0E_val (x0c_mem_eS hR r hr)]; exact hx.symm)⟩
    have hRF := rowFormula G5 Sg hSg fE actE hCA x0rows (Umat pv) hsupp hdist hstab x hrows y
    rw [show Pmat pv x y = avgMat Sg actE (Umat pv) x y from rfl, hRF,
      Umat_rowcode hR pv hr hx y]
    have hpos : (stabCard x : ℝ) ≠ 0 := by
      have hone : (1 : G5) ∈ Sg.filter (fun g => actE g x = x) :=
        Finset.mem_filter.mpr ⟨Sg_one, actE_one_apply hA x⟩
      have hcard : 0 < stabCard x := Finset.card_pos.mpr ⟨1, hone⟩
      exact_mod_cast hcard.ne'
    exact mul_div_cancel₀ _ hpos
  · intro σ hσ x y
    exact avgMatInvariant G5 Sg hSg fE actE hCA (Umat pv) σ hσ x y
  · intro x
    obtain ⟨hl, σ, hσS, hσ⟩ := hOrb x
    exact ⟨hl, σ, hσS, x0E (labE 0 x.1) pt0, x0E_val (x0c_mem_eS hR (labE 0 x.1) hl), hσ⟩

theorem rowFacts (hCF : CodeFacts) (hA : ActSetup) (hNst : NStructure) (hE : ESem) (hN : NSem)
    (hT : TabSem) (hR : RowSem) (hG : GroupSem) : RowFacts :=
  rowFacts_of hA hR
    (orbClause hCF hA hN hT hR)
    (distinctOrbits hCF hA hR)
    (fun r hr hr1 g hg hfix z => stabInvPos hCF hA hR hG r hr hr1 g hg hfix z)

end

end Work.PTCert
