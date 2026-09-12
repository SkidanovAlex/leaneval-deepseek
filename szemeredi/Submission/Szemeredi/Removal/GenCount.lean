import Mathlib
import Submission.Szemeredi.Removal.H4

/-!
# The generalized counting lemma (Tao, arXiv:math/0503572, §4)

This file assembles Tao's `gencount` (Lemma 4.2 of the paper) from the abstract
hypotheses `GCHyp` of the lifted atom data.

The induction is on the pair (order `d'`, number `r` of edges of top order).  At an edge
`g₀` of top order the counting product is split into the `p`-, `b`- and `c`-terms; the
pointwise split is `cnt_split` and the bookkeeping is `gencount_of_parts`.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-! ## The pointwise split -/

/-- **The pointwise split of the counting product at an edge `g₀`.**  If the lifted
indicator of `g₀` decomposes as `p + b + c` on the lower set of `g₀`, then on the whole
bundle point space the counting product splits as
`∏_{g ∈ G} 1_{Ag g} = (p + b + c) · ∏_{g ∈ G, g ≠ g₀} 1_{Ag g}`. -/
theorem prod_indicator_eq_add {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (G : Finset (Finset κ)) (Ag : Finset κ → Finset (BPt V π)) (g₀ : Finset κ) (hg₀ : g₀ ∈ G)
    (hclosed : ∀ g ∈ G, ∀ g' ⊆ g, g' ∈ G) (p : ℝ) (b c : BPt V π → ℝ)
    (h1 : ∀ v, v ∈ lowSetAll π Ag g₀ → indicator (Ag g₀) v = p + b v + c v)
    (v : BPt V π) :
    (∏ g ∈ G, indicator (Ag g) v)
      = (p + b v + c v) * ∏ g ∈ G.erase g₀, indicator (Ag g) v := by
  classical
  rw [← Finset.prod_erase_mul G (fun g => indicator (Ag g) v) hg₀]
  by_cases hv : v ∈ lowSetAll π Ag g₀
  · rw [h1 v hv]
    ring
  · rw [mem_lowSetAll] at hv
    push_neg at hv
    obtain ⟨g', hlt, hg'⟩ := hv
    have hmem : g' ∈ G.erase g₀ := Finset.mem_erase.mpr
      ⟨(Finset.ssubset_iff_subset_ne.mp hlt).2, hclosed g₀ hg₀ g' hlt.1⟩
    have hzero : (∏ g ∈ G.erase g₀, indicator (Ag g) v) = 0 :=
      Finset.prod_eq_zero hmem (by rw [indicator, if_neg hg'])
    rw [hzero]
    ring

/-- **The split of the counting functional**: `Cnt G = p · Cnt (G ∖ {g₀}) + (b-term) +
(c-term)`. -/
theorem cnt_split {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (G : Finset (Finset κ)) (Ag : Finset κ → Finset (BPt V π)) (g₀ : Finset κ) (hg₀ : g₀ ∈ G)
    (hclosed : ∀ g ∈ G, ∀ g' ⊆ g, g' ∈ G) (p : ℝ) (b c : BPt V π → ℝ)
    (h1 : ∀ v, v ∈ lowSetAll π Ag g₀ → indicator (Ag g₀) v = p + b v + c v) :
    Cnt π G Ag = p * Cnt π (G.erase g₀) Ag
      + avg (fun v => b v * ∏ g ∈ G.erase g₀, indicator (Ag g) v)
      + avg (fun v => c v * ∏ g ∈ G.erase g₀, indicator (Ag g) v) := by
  classical
  have hpt := fun v => prod_indicator_eq_add (V := V) (π := π) G Ag g₀ hg₀ hclosed p b c h1 v
  unfold Cnt
  rw [show (fun v : BPt V π => ∏ g ∈ G, indicator (Ag g) v)
      = fun v => (p + b v + c v) * ∏ g ∈ G.erase g₀, indicator (Ag g) v
      from funext hpt]
  rw [show (fun v : BPt V π => (p + b v + c v) * ∏ g ∈ G.erase g₀, indicator (Ag g) v)
      = fun v => p * (∏ g ∈ G.erase g₀, indicator (Ag g) v)
          + b v * (∏ g ∈ G.erase g₀, indicator (Ag g) v)
          + c v * (∏ g ∈ G.erase g₀, indicator (Ag g) v)
      from funext (fun v => by ring)]
  rw [avg_add, avg_add, avg_mul_const]

/-! ## The arithmetic bookkeeping -/

/-- **The induction step in bookkeeping form.**  Given the induction hypothesis for
`G ∖ {g₀}` and the bounds for the `b`- and `c`-terms, one obtains the bound for `G`. -/
theorem gencount_of_parts {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (G : Finset (Finset κ)) (Ag : Finset κ → Finset (BPt V π)) (pg : Finset κ → ℝ)
    (g₀ : Finset κ) (hg₀ : g₀ ∈ G) (hclosed : ∀ g ∈ G, ∀ g' ⊆ g, g' ∈ G)
    (bg cg : BPt V π → ℝ)
    (h1 : ∀ v, v ∈ lowSetAll π Ag g₀ → indicator (Ag g₀) v = pg g₀ + bg v + cg v)
    (η₁ η₂ C₁ C₂ : ℝ) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hpg0 : ∀ g ∈ G, 0 ≤ pg g) (hpg1 : ∀ g ∈ G, pg g ≤ 1)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hIH : |Cnt π (G.erase g₀) Ag - ∏ g ∈ G.erase g₀, pg g|
      ≤ η₁ * (∏ g ∈ G.erase g₀, pg g) + C₁ * ρ)
    (hB : |avg (fun v => bg v * ∏ g ∈ G.erase g₀, indicator (Ag g) v)|
      ≤ η₂ * (pg g₀ * ∏ g ∈ G.erase g₀, pg g) + C₂ * ρ)
    (hC : |avg (fun v => cg v * ∏ g ∈ G.erase g₀, indicator (Ag g) v)| ≤ ρ) :
    |Cnt π G Ag - ∏ g ∈ G, pg g| ≤ (η₁ + η₂) * (∏ g ∈ G, pg g) + (C₁ + C₂ + 1) * ρ := by
  classical
  have hsplit := cnt_split (V := V) π G Ag g₀ hg₀ hclosed (pg g₀) bg cg h1
  have hprod : (∏ g ∈ G, pg g) = pg g₀ * ∏ g ∈ G.erase g₀, pg g := by
    rw [(Finset.prod_erase_mul G pg hg₀).symm, mul_comm]
  set P' : ℝ := ∏ g ∈ G.erase g₀, pg g with hP'
  set A : ℝ := Cnt π (G.erase g₀) Ag with hAdef
  set B : ℝ := avg (fun v => bg v * ∏ g ∈ G.erase g₀, indicator (Ag g) v) with hBdef
  set Cc : ℝ := avg (fun v => cg v * ∏ g ∈ G.erase g₀, indicator (Ag g) v) with hCdef
  have hp0 : 0 ≤ pg g₀ := hpg0 g₀ hg₀
  have hp1 : pg g₀ ≤ 1 := hpg1 g₀ hg₀
  have hP'0 : 0 ≤ P' := by
    rw [hP']
    exact Finset.prod_nonneg (fun g hg => hpg0 g (Finset.mem_of_mem_erase hg))
  have hdecomp : Cnt π G Ag - ∏ g ∈ G, pg g
      = pg g₀ * (A - P') + B + Cc := by
    rw [hAdef, hBdef, hCdef, hP', hsplit, hprod]
    ring
  rw [hdecomp]
  have htri : |pg g₀ * (A - P') + B + Cc| ≤ pg g₀ * |A - P'| + |B| + |Cc| := by
    have h1' : |pg g₀ * (A - P') + B + Cc| ≤ |pg g₀ * (A - P') + B| + |Cc| :=
      abs_add_le _ _
    have h2' : |pg g₀ * (A - P') + B| ≤ |pg g₀ * (A - P')| + |B| := abs_add_le _ _
    have h3' : |pg g₀ * (A - P')| = pg g₀ * |A - P'| := by
      rw [abs_mul, abs_of_nonneg hp0]
    linarith
  have hA' : pg g₀ * |A - P'| ≤ pg g₀ * (η₁ * P' + C₁ * ρ) := by
    rw [hAdef]
    exact mul_le_mul_of_nonneg_left hIH hp0
  have hB' : |B| ≤ η₂ * (pg g₀ * P') + C₂ * ρ := by
    rw [hBdef]; exact hB
  have hC' : |Cc| ≤ ρ := by rw [hCdef]; exact hC
  have hkey : pg g₀ * (η₁ * P' + C₁ * ρ) + (η₂ * (pg g₀ * P') + C₂ * ρ) + ρ
      ≤ (η₁ + η₂) * (pg g₀ * P') + (C₁ + C₂ + 1) * ρ := by
    nlinarith [mul_nonneg hp0 hP'0, mul_nonneg hη₁ hP'0, mul_nonneg hη₂ (mul_nonneg hp0 hP'0),
      mul_nonneg hC₁ hρ, mul_nonneg (mul_nonneg hC₁ hρ) hp0]
  calc |pg g₀ * (A - P') + B + Cc|
      ≤ pg g₀ * |A - P'| + |B| + |Cc| := htri
    _ ≤ pg g₀ * (η₁ * P' + C₁ * ρ) + (η₂ * (pg g₀ * P') + C₂ * ρ) + ρ := by linarith
    _ ≤ (η₁ + η₂) * (pg g₀ * P') + (C₁ + C₂ + 1) * ρ := hkey
    _ = (η₁ + η₂) * (∏ g ∈ G, pg g) + (C₁ + C₂ + 1) * ρ := by rw [hprod]

/-! ## The `b`-term: discarding the top-order factors and Fubini -/

/-- `Glt` and `Ggt` are disjoint. -/
theorem disjoint_Glt_Ggt {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : Finset (Finset κ)) (g₀ : Finset κ) (d' : ℕ) :
    Disjoint (Glt G g₀) (Ggt G g₀ d') := by
  rw [Finset.disjoint_left]
  intro h h1 h2
  rw [mem_Glt] at h1
  rw [mem_Ggt] at h2
  exact h2.2.1 h1.2

/-- `Glt ∪ Ggt` consists of the edges of `G` other than `g₀` that are not of top order. -/
theorem Glt_union_Ggt_subset_erase {κ : Type*} [Fintype κ] [DecidableEq κ]
    (d' : ℕ) (hd' : 1 ≤ d') (G : Finset (Finset κ)) {g₀ : Finset κ} (hg₀ : g₀ ∈ G)
    (hg₀card : g₀.card = d') :
    Glt G g₀ ∪ Ggt G g₀ d' ⊆ G.erase g₀ := by
  intro h hh
  rw [Finset.mem_union] at hh
  rcases hh with hh | hh
  · rw [mem_Glt] at hh
    exact Finset.mem_erase.mpr ⟨(Finset.ssubset_iff_subset_ne.mp hh.2).2, hh.1⟩
  · rw [mem_Ggt] at hh
    refine Finset.mem_erase.mpr ⟨fun heq => ?_, hh.1⟩
    have hc : h.card = d' := by rw [heq, hg₀card]
    omega

/-- **Discarding the top-order factors**: the product over `G ∖ {g₀}` is dominated by the
product over `Glt ∪ Ggt`. -/
theorem prod_erase_le_Glt_Ggt {κ : Type*} [Fintype κ] [DecidableEq κ]
    (d' : ℕ) (hd' : 1 ≤ d') (G : Finset (Finset κ)) {g₀ : Finset κ} (hg₀ : g₀ ∈ G)
    (hg₀card : g₀.card = d') (f : Finset κ → ℝ) (hf0 : ∀ g, 0 ≤ f g) (hf1 : ∀ g, f g ≤ 1) :
    (∏ g ∈ G.erase g₀, f g) ≤ ∏ g ∈ Glt G g₀ ∪ Ggt G g₀ d', f g := by
  classical
  have h1 := Finset.prod_sdiff (Glt_union_Ggt_subset_erase d' hd' G hg₀ hg₀card) (f := f)
  have h0 : 0 ≤ ∏ x ∈ Glt G g₀ ∪ Ggt G g₀ d', f x := Finset.prod_nonneg (fun x _ => hf0 x)
  have hle1 : (∏ x ∈ G.erase g₀ \ (Glt G g₀ ∪ Ggt G g₀ d'), f x) ≤ 1 :=
    Finset.prod_le_one (fun x _ => hf0 x) (fun x _ => hf1 x)
  rw [← h1]
  nlinarith

/-- The lower set over the down-closed family `G` is the lower set over all subsets. -/
theorem lowSet_eq_lowSetAll {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (G : Finset (Finset κ)) (Ag : Finset κ → Finset (BPt V π)) {g₀ : Finset κ} (hg₀ : g₀ ∈ G)
    (hclosed : ∀ g ∈ G, ∀ g' ⊆ g, g' ∈ G) :
    lowSet π G Ag g₀ = lowSetAll π Ag g₀ := by
  classical
  ext v
  rw [mem_lowSet, mem_lowSetAll]
  constructor
  · intro h g' hlt
    exact h g' (hclosed g₀ hg₀ g' hlt.1) hlt
  · intro h g' hg' hlt
    exact h g' hlt

/-- The product of the lifted indicators below `g₀` is the indicator of the lower set. -/
theorem prod_Glt_eq_indicator {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (G : Finset (Finset κ)) (Ag : Finset κ → Finset (BPt V π)) (g₀ : Finset κ) (v : BPt V π) :
    (∏ g' ∈ Glt G g₀, indicator (Ag g') v) = indicator (lowSet π G Ag g₀) v :=
  prod_indicator_lowSet (V := V) π G Ag g₀ v

/-- The `Xw` factor evaluated on a combination of a `g₀`-point and frozen coordinates. -/
theorem Xw_combine {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Finset ι → Finset (Pt V)) (π : κ → ι) (G : Finset (Finset κ))
    {g₀ : Finset κ} (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b)
    (hg₀ : g₀ ∈ G) (w : W1 (V := V) π g₀) (u : W2 (V := V) π g₀) :
    Xw (V := V) A π G g₀ hinj w
      = ∏ h ∈ Glt G g₀, indicator (AgOf (V := V) A π G hinj h)
          (combine (V := V) π g₀ w u) := by
  show (∏ h ∈ Glt G g₀, indicator (AgOf (V := V) A π G hinj h)
      (combine (V := V) π g₀ w (Classical.arbitrary (W2 (V := V) π g₀)))) = _
  refine Finset.prod_congr rfl (fun h hh => ?_)
  exact indicator_congr (mem_AgOf_combine_congr (V := V) A π G hinj (mem_Glt.mp hh).1
    (mem_Glt.mp hh).2.1 w (Classical.arbitrary (W2 (V := V) π g₀)) u)


/-- The `b`-factor is independent of the coordinates outside `g`. -/
theorem bgOf_combine {Hd : Finset (Finset ι)} {A : Finset ι → Finset (Pt V)}
    {B B' : ℕ → Finset ι → SigAlg (Pt V)}
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g : Finset κ} (hg : g ∈ G)
    (w : (k : {k // k ∈ g}) → V (π k.val)) (u : (k : {k // k ∉ g}) → V (π k.val)) :
    bgOf (V := V) B B' A π G hB.inj g (combine (V := V) π g w u)
      = betaOf (V := V) B B' A (g.image π) (piCongrImage (V := V) π g (hB.inj g hg) w) := by
  rw [bgOf, dif_pos hg, liftFun_apply, restrict_combine]

/-- **The Fubini step of the `b`-term**: after discarding the top-order factors, the average
splits into averages over the `g₀`-coordinates and the complement. -/
theorem bterm_fubini {Hd : Finset (Finset ι)} {A : Finset ι → Finset (Pt V)}
    {B B' : ℕ → Finset ι → SigAlg (Pt V)} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {π : κ → ι} {G : Finset (Finset κ)} (hB : IsBundle Hd π G) {g₀ : Finset κ} (hg₀ : g₀ ∈ G)
    (d' : ℕ) (hd' : 1 ≤ d') :
    avg (fun v : BPt V π => |bgOf (V := V) B B' A π G hB.inj g₀ v|
        * ∏ h ∈ Glt G g₀ ∪ Ggt G g₀ d', indicator (AgOf (V := V) A π G hB.inj h) v)
      = avg (fun w : W1 (V := V) π g₀ =>
          (|betaOf (V := V) B B' A (g₀.image π)
              (piCongrImage (V := V) π g₀ (hB.inj g₀ hg₀) w)|
            * Xw (V := V) A π G g₀ hB.inj w)
          * avg (fun u : W2 (V := V) π g₀ => Pw (V := V) A π G g₀ d' hB.inj w u)) := by
  conv_lhs => rw [avg_split (V := V) π g₀]
  congr 1
  funext w
  have hinner : (fun u : W2 (V := V) π g₀ => |bgOf (V := V) B B' A π G hB.inj g₀
          (combine (V := V) π g₀ w u)|
        * ∏ h ∈ Glt G g₀ ∪ Ggt G g₀ d', indicator (AgOf (V := V) A π G hB.inj h)
            (combine (V := V) π g₀ w u))
      = fun u : W2 (V := V) π g₀ =>
        (|betaOf (V := V) B B' A (g₀.image π)
            (piCongrImage (V := V) π g₀ (hB.inj g₀ hg₀) w)|
          * Xw (V := V) A π G g₀ hB.inj w)
        * Pw (V := V) A π G g₀ d' hB.inj w u := by
    funext u
    rw [bgOf_combine (V := V) (B := B) (B' := B') hB hg₀ w u,
      Finset.prod_union (disjoint_Glt_Ggt G g₀ d'),
      Xw_combine (V := V) A π G hB.inj hg₀ w u]
    simp only [Pw]
    ring
  rw [hinner, avg_mul_const]


/-! ## Cauchy–Schwarz in the frozen space -/

namespace SigAlg

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-- Cauchy–Schwarz for the average, in square-root form. -/
theorem avg_mul_abs_le_sqrt (f g : Ω → ℝ) :
    |avg (fun x => f x * g x)| ≤ Real.sqrt (avg (fun x => f x ^ 2))
      * Real.sqrt (avg (fun x => g x ^ 2)) := by
  have h := avg_mul_sq_le f g
  have h2 : 0 ≤ avg (fun x => f x ^ 2) := avg_nonneg (fun x => sq_nonneg _)
  calc |avg (fun x => f x * g x)| = Real.sqrt ((avg (fun x => f x * g x)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (avg (fun x => f x ^ 2) * avg (fun x => g x ^ 2)) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (avg (fun x => f x ^ 2)) * Real.sqrt (avg (fun x => g x ^ 2)) :=
        Real.sqrt_mul h2 _

/-- **Weighted Cauchy–Schwarz**: the weight `χ ≥ 0` may be put in both factors. -/
theorem avg_weighted_cauchy (χ : Ω → ℝ) (hχ : ∀ x, 0 ≤ χ x) (β Y : Ω → ℝ) :
    |avg (fun x => χ x * |β x| * Y x)|
      ≤ Real.sqrt (avg (fun x => χ x * (β x) ^ 2))
        * Real.sqrt (avg (fun x => χ x * (Y x) ^ 2)) := by
  have h := avg_mul_abs_le_sqrt (fun x => Real.sqrt (χ x) * |β x|)
    (fun x => Real.sqrt (χ x) * Y x)
  have h1 : (fun x => Real.sqrt (χ x) * |β x| * (Real.sqrt (χ x) * Y x))
      = fun x => Real.sqrt (χ x) * Real.sqrt (χ x) * (|β x| * Y x) := by
    funext x; ring
  have h2 : (fun x => Real.sqrt (χ x) * Real.sqrt (χ x) * (|β x| * Y x))
      = fun x => χ x * |β x| * Y x := by
    funext x; rw [Real.mul_self_sqrt (hχ x)]; ring
  have h3 : (fun x => (Real.sqrt (χ x) * |β x|) ^ 2) = fun x => χ x * (β x) ^ 2 := by
    funext x; rw [mul_pow, Real.sq_sqrt (hχ x), sq_abs]
  have h4 : (fun x => (Real.sqrt (χ x) * Y x) ^ 2) = fun x => χ x * (Y x) ^ 2 := by
    funext x; rw [mul_pow, Real.sq_sqrt (hχ x)]
  simp only [h1, h2, h3, h4] at h
  exact h

end SigAlg

/-- **The Cauchy–Schwarz step of the `b`-term**, with the `Xw` weight in both factors. -/
theorem bterm_cauchy {κ : Type*} [Fintype κ] [DecidableEq κ] (A : Finset ι → Finset (Pt V))
    (π : κ → ι) (G : Finset (Finset κ)) {g₀ : Finset κ}
    (hinj : ∀ h ∈ G, ∀ a ∈ h, ∀ b ∈ h, π a = π b → a = b) (β Yw : W1 (V := V) π g₀ → ℝ)
    (hXw : ∀ w : W1 (V := V) π g₀, 0 ≤ Xw (V := V) A π G g₀ hinj w) :
    |avg (fun w : W1 (V := V) π g₀ =>
        Xw (V := V) A π G g₀ hinj w * |β w| * Yw w)|
      ≤ Real.sqrt (avg (fun w : W1 (V := V) π g₀ =>
            Xw (V := V) A π G g₀ hinj w * (β w) ^ 2))
        * Real.sqrt (avg (fun w : W1 (V := V) π g₀ =>
            Xw (V := V) A π G g₀ hinj w * (Yw w) ^ 2)) :=
  SigAlg.avg_weighted_cauchy (fun w : W1 (V := V) π g₀ => Xw (V := V) A π G g₀ hinj w) hXw β Yw

/-- **The first Cauchy–Schwarz factor** is the weighted `L²` norm of the `b`-term. -/
theorem avg_Xw_mul_sq {Hd : Finset (Finset ι)} {A : Finset ι → Finset (Pt V)}
    {B B' : ℕ → Finset ι → SigAlg (Pt V)} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {π : κ → ι} {G : Finset (Finset κ)} (hB : IsBundle Hd π G) {g₀ : Finset κ} (hg₀ : g₀ ∈ G) :
    avg (fun w : W1 (V := V) π g₀ =>
        Xw (V := V) A π G g₀ hB.inj w
          * (betaOf (V := V) B B' A (g₀.image π)
              (piCongrImage (V := V) π g₀ (hB.inj g₀ hg₀) w)) ^ 2)
      = avg (fun v : BPt V π => (bgOf (V := V) B B' A π G hB.inj g₀ v) ^ 2
          * indicator (lowSetAll π (AgOf (V := V) A π G hB.inj) g₀) v) := by
  classical
  have h := avg_restrict_eq (V := fun k => V (π k)) g₀
    (fun w : W1 (V := V) π g₀ => Xw (V := V) A π G g₀ hB.inj w
      * (betaOf (V := V) B B' A (g₀.image π)
          (piCongrImage (V := V) π g₀ (hB.inj g₀ hg₀) w)) ^ 2)
  rw [← h]
  congr 1
  funext v
  have hbg : bgOf (V := V) B B' A π G hB.inj g₀ v
      = betaOf (V := V) B B' A (g₀.image π)
          (piCongrImage (V := V) π g₀ (hB.inj g₀ hg₀)
            (restrict (V := fun k => V (π k)) v g₀)) := by
    rw [bgOf, dif_pos hg₀, liftFun_apply]
  rw [hbg, Xw_of_restrict, prod_Glt_eq_indicator,
    lowSet_eq_lowSetAll (V := V) π G (AgOf (V := V) A π G hB.inj) hg₀ hB.closed]
  ring

/-- **The second Cauchy–Schwarz factor** is the counting functional of the doubled bundle. -/
theorem avg_Xw_Yw_sq {Hd : Finset (Finset ι)} {A : Finset ι → Finset (Pt V)}
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g₀ : Finset κ} (hg₀ : g₀ ∈ G) {d' : ℕ} (hd' : 1 ≤ d')
    (hg₀card : g₀.card = d') :
    avg (fun w : W1 (V := V) π g₀ => Xw (V := V) A π G g₀ hB.inj w
        * (avg (fun u : W2 (V := V) π g₀ => Pw (V := V) A π G g₀ d' hB.inj w u)) ^ 2)
      = Cnt (dblπ π g₀) (dblG G g₀ d') (AgDbl (V := V) A π G g₀ d' hB.inj) :=
  (avg_dblG_eq (V := V) A π G g₀ d' hg₀card hd' hB.inj).symm


/-- The counting functional over `Glt` is the average of the indicator of the lower set. -/
theorem cnt_Glt_eq {Hd : Finset (Finset ι)} {A : Finset ι → Finset (Pt V)}
    {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι} {G : Finset (Finset κ)}
    (hB : IsBundle Hd π G) {g₀ : Finset κ} (hg₀ : g₀ ∈ G) :
    Cnt π (Glt G g₀) (AgOf (V := V) A π G hB.inj)
      = avg (indicator (lowSetAll π (AgOf (V := V) A π G hB.inj) g₀)) := by
  classical
  have h1 : Cnt π (Glt G g₀) (AgOf (V := V) A π G hB.inj)
      = avg (fun v => ∏ h ∈ Glt G g₀, indicator (AgOf (V := V) A π G hB.inj h) v) := rfl
  rw [h1]
  congr 1
  funext v
  rw [prod_Glt_eq_indicator,
    lowSet_eq_lowSetAll (V := V) π G (AgOf (V := V) A π G hB.inj) hg₀ hB.closed]

/-- The `p`-product over the doubled bundle. -/
theorem prod_dblG_pg {A : Finset ι → Finset (Pt V)} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : κ → ι) (G : Finset (Finset κ)) {g₀ : Finset κ} {d' : ℕ} (hg₀ : g₀.card = d')
    (hd' : 1 ≤ d') :
    (∏ gg ∈ dblG G g₀ d', pgOf A (dblπ π g₀) gg)
      = (∏ h ∈ Glt G g₀, pgOf A π h) * (∏ h ∈ Ggt G g₀ d', pgOf A π h) ^ 2 := by
  rw [prod_dblG G g₀ d' hg₀ hd']
  have hk : ∀ (i : Bool) {h : Finset κ}, pgOf A (dblπ π g₀) (dblEdge g₀ i h)
      = pgOf A π h := fun i h => by rw [pgOf, pgOf, dblEdge_image]
  rw [show (∏ h ∈ Glt G g₀, pgOf A (dblπ π g₀) (dblEdge g₀ false h))
      = ∏ h ∈ Glt G g₀, pgOf A π h from Finset.prod_congr rfl (fun h _ => hk false),
    show (∏ h ∈ Ggt G g₀ d', pgOf A (dblπ π g₀) (dblEdge g₀ false h)
          * pgOf A (dblπ π g₀) (dblEdge g₀ true h))
      = ∏ h ∈ Ggt G g₀ d', pgOf A π h * pgOf A π h
      from Finset.prod_congr rfl (fun h _ => by rw [hk false, hk true]),
    Finset.prod_mul_distrib, sq]


end Szemeredi.Removal

