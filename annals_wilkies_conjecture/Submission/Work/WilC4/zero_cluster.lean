/-
  WilC4/zero_cluster : `0 ∉ ClusterE Y B` — the missing `hzero` of `dev_decay_E`.

  ## The statement

  For a `∅`-definable family of graphs `Y` with a `ULPMStruct` breakpoint family `B`, the value
  `0` is **not** a cluster value of the doubling ratio: there is no sequence of `B`-deep points
  whose doubling ratio is small on the whole window `[x/N, Nx]` with tolerance `1/N`.

  ## Why it is true

  The deep ratio is bounded **above** by the scale at deep points (`deep_ratio_scale_bdd`:
  `|f_c(2x)/f_c(x)| < β` for `β`-deep `x`, `β ≥ Γ`).  That is an upper bound for `Y`, hence a
  *lower* bound for the family whose fibre is `1/f_c`: inverting the fibre value inverts the
  doubling ratio at the same point (`ratW_invY_iff`).  So the *lower* bound of the deep ratio of
  `Y` is the *upper* bound of `deep_ratio_scale_bdd` for the value-inverted family `InvY Y`
  (`InvFamDefs`), taken at its halved breakpoint family `HalfB B` (the halves make the ratio of
  the inverse family of constant sign, so that its monotonicity — the second half of
  `ULPMStruct` — transfers; this is `invY_ulpmStruct_b`).  Putting the two together gives
  `ratW_gt_of_window`: at a point `z` whose window `[z/N, Nz']` is `B`-free, any doubling ratio
  satisfies `2/N < |w|`.

  A `0`-witness for `Y` at the scale `N` is a point `x` with `[x/N, Nx]` `B`-free whose doubling
  ratio is `≤ 1/N` on that window; the same window is `B`-free, so the lower bound gives
  `2/N < |w| ≤ 1/N`, a contradiction.

  ## Files

  * `Submission.Work.WilC4.InvFamDefs` : `InvY`, `HalfB`, `gr_invY_iff`, `ratW_invY_iff`,
    `invY_functional`, `mem_halfB_iff`, `isDeepR_halfB`.
  * `Submission.Work.WilC4.invY_definable` : `InvY Y` is `∅`-definable.
  * `Submission.Work.WilC4.invY_ulpmStruct_b` : `ULPMStruct (InvY Y) (HalfB B)`.
  * `Submission.Work.WilC4.halfB_definable_b` : `HalfB B` is `∅`-definable.
  * `Submission.Work.WilC4.ratW_gt_of_window` : the same lower bound, phrased for peers; its
    proof rests on the two *stubs* `invY_ulpmStruct` / `halfB_definable` in the same directory,
    which are unproved, so this module does not import it.
  * `Submission.Work.WilC4.deep_ratio_scale_bdd` : the upper bound for the deep ratio.
  * `Submission.Work.WilC4.rexp_deep_window_value_ratio` : `isDeepR_half_of_window`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.ULPMAsm
import Submission.Work.WilC4.ULPMExp
import Submission.Work.WilC4.InvFamDefs
import Submission.Work.WilC4.invY_ulpmStruct_b
import Submission.Work.WilC4.halfB_definable_b
import Submission.Work.WilC4.DiagDefs
import Submission.Work.WilC4.deep_ratio_scale_bdd
import Submission.Work.WilC4.rexp_deep_window_value_ratio

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)
open Work.WilC4.Route (Gr ClusterE valY)

variable {k : ℕ}

/-! ## 0. `InvY Y` is `∅`-definable

A self-contained copy of `Work.WilC4.invY_definable` (whose file `Submission/Work/WilC4/invY_definable.lean`
currently fails to elaborate), so that this module does not depend on it.  The body is the set of
`w : (Fin (k+2) ⊕ Fin 1) → ℝ` with `w (inr 0) ≠ 0`, `w (inr 0) * w (inl 1) = 1` and
`(w ∘ UlpmEmb k) ∈ Y`; all three conjuncts are `∅`-definable, and the existential quantifier over
`u : Fin 1 → ℝ` is finite. -/

/-- The defining body of `InvY` in the ambient context `(Fin (k+2) ⊕ Fin 1) → ℝ`
(`v` the free coordinates, `u 0` the quantified inverse value). -/
def invYBody {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) :
    Set ((Fin (k + 2) ⊕ Fin 1) → ℝ) :=
  {w | w (Sum.inr (0 : Fin 1)) ≠ 0} ∩
    ({w | w (Sum.inr (0 : Fin 1)) * w (Sum.inl (1 : Fin (k + 2))) = 1} ∩
      {w | (w ∘ UlpmEmb k) ∈ Y})

theorem invYBody_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (invYBody (k := k) Y) := by
  have h1u : (Set.univ : Set ℝ).Definable LRc
      {w : (Fin (k + 2) ⊕ Fin 1) → ℝ | w (Sum.inr (0 : Fin 1)) ≠ 0} := by
    have h := definable_ne_LRc (σ := Fin (k + 2) ⊕ Fin 1)
      (MvPolynomial.X (Sum.inr (0 : Fin 1))) (MvPolynomial.C (0 : ℝ))
    convert h using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, MvPolynomial.eval_X, MvPolynomial.eval_C]
  have h1 : (∅ : Set ℝ).Definable LRc
      {w : (Fin (k + 2) ⊕ Fin 1) → ℝ | w (Sum.inr (0 : Fin 1)) ≠ 0} :=
    (definable_univ_iff_empty).mp h1u
  have h2u : (Set.univ : Set ℝ).Definable LRc
      {w : (Fin (k + 2) ⊕ Fin 1) → ℝ |
        w (Sum.inr (0 : Fin 1)) * w (Sum.inl (1 : Fin (k + 2))) = 1} := by
    have h := definable_eval_eq_LRc (σ := Fin (k + 2) ⊕ Fin 1)
      (MvPolynomial.X (Sum.inr (0 : Fin 1)) * MvPolynomial.X (Sum.inl (1 : Fin (k + 2))) -
        MvPolynomial.C (1 : ℝ)) 0
    convert h using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_setOf_eq, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
      MvPolynomial.eval_X, MvPolynomial.eval_C]
    constructor <;> intro hw <;> linarith
  have h2 : (∅ : Set ℝ).Definable LRc
      {w : (Fin (k + 2) ⊕ Fin 1) → ℝ |
        w (Sum.inr (0 : Fin 1)) * w (Sum.inl (1 : Fin (k + 2))) = 1} :=
    (definable_univ_iff_empty).mp h2u
  have h3 : (∅ : Set ℝ).Definable LRc
      {w : (Fin (k + 2) ⊕ Fin 1) → ℝ | (w ∘ UlpmEmb k) ∈ Y} :=
    Set.Definable.preimage_comp (UlpmEmb k) hY
  exact h1.inter (h2.inter h3)

/-- **`InvY Y` is `∅`-definable** when `Y` is. -/
theorem invY_definable_b {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (InvY Y) := by
  have hS : (∅ : Set ℝ).Definable LRc (invYBody (k := k) Y) := invYBody_definable hY
  have hex := Set.Definable.exists_of_finite (A := (∅ : Set ℝ)) (L := LRc)
    (α := Fin (k + 2)) (β := Fin 1) hS
  have hset : {v : Fin (k + 2) → ℝ | ∃ u : Fin 1 → ℝ, Sum.elim v u ∈ invYBody (k := k) Y} =
      InvY Y := by
    ext v
    simp only [InvY, invYBody, Set.mem_ofPred_eq, Set.mem_setOf_eq, Set.mem_inter_iff,
      Sum.elim_inl, Sum.elim_inr]
  rw [hset] at hex
  exact hex

/-! ## 1. The deep ratio is bounded below -/

/-- **The doubling ratio is bounded below at points with a `B`-free window.**  Combining the
upper bound `deep_ratio_scale_bdd` on the value-inverted family `InvY Y` (whose doubling ratio is
the inverse of the ratio of `Y`, `ratW_invY_iff`) with `invY_ulpmStruct_b`/`halfB_definable_b`. -/
theorem ratW_gt_of_window_aux {k : ℕ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hOM : WilkiesDesign.CG.OMinModels) (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (B : Set (Fin (k + 1) → ℝ)) (hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B)
    (hst : ULPMStruct Y B) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (c : Fin k → ℝ) (z z' w : ℝ), 0 < z → z ≤ z' → z' ≤ 2 * z →
      (∀ t : ℝ, z / (N : ℝ) ≤ t → t ≤ (N : ℝ) * z' → Fin.cons t c ∉ B) →
      RatW Y c z w → (2 : ℝ) / (N : ℝ) < |w| := by
  have hYinv : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (InvY Y) := invY_definable_b hY
  have hBhalf : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (HalfB B) := halfB_definable_b hB
  have hfinv : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr (InvY Y) c x y →
      Gr (InvY Y) c x y' → y = y' := invY_functional hfun
  have hstinv : ULPMStruct (InvY Y) (HalfB B) := invY_ulpmStruct_b hfun hst
  obtain ⟨Γ, hΓ1, hΓ⟩ :=
    deep_ratio_scale_bdd hR hOM hPB (InvY Y) hYinv hfinv (HalfB B) hBhalf hstinv
  obtain ⟨N, hN2, hNΓ⟩ : ∃ N : ℕ, 2 ≤ N ∧ 4 * Γ ≤ (N : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_ge (max 2 (4 * Γ))
    exact ⟨N, by exact_mod_cast le_trans (le_max_left 2 (4 * Γ)) hN,
      le_trans (le_max_right 2 (4 * Γ)) hN⟩
  refine ⟨N, hN2, ?_⟩
  intro c z z' w hz hle h2z hfree hrat
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN4 : (4 : ℝ) ≤ (N : ℝ) := by linarith [hΓ1, hNΓ]
  have hz'pos : 0 < z' := lt_of_lt_of_le hz hle
  have hab : z / (N : ℝ) < (N : ℝ) * z' := by
    have h1 : z / (N : ℝ) < z := by
      rw [div_lt_iff₀ hNpos]; nlinarith [hz, hNr]
    have h2 : z ≤ (N : ℝ) * z' := by
      have hm := mul_le_mul_of_nonneg_right hN4 (le_of_lt hz'pos)
      linarith
    linarith
  have hfree' : ∀ x ∈ Set.Ioo (z / (N : ℝ)) ((N : ℝ) * z'), Fin.cons x c ∉ B :=
    fun x hx => hfree x (le_of_lt hx.1) (le_of_lt hx.2)
  obtain ⟨-, hnz, -⟩ := hst.1 c (z / (N : ℝ)) ((N : ℝ) * z') hab hfree'
  have hdeep : IsDeepR B c ((N : ℝ) / 2) z :=
    isDeepR_half_of_window hNpos hfree le_rfl hle
  have hdeepHalf : IsDeepR (HalfB B) c (((N : ℝ) / 2) / 2) z :=
    isDeepR_halfB (by linarith : (0 : ℝ) < (N : ℝ) / 2) hz hdeep
  have hβΓ : Γ ≤ ((N : ℝ) / 2) / 2 := by linarith
  obtain ⟨y, y', hy, hy', hy0, hwy⟩ := hrat
  have h2zmem : 2 * z ∈ Set.Ioo (z / (N : ℝ)) ((N : ℝ) * z') := by
    refine ⟨?_, ?_⟩
    · rw [div_lt_iff₀ hNpos]; nlinarith [hz, hN4]
    · have hm := mul_le_mul_of_nonneg_right hN4 (le_of_lt hz'pos)
      nlinarith [hm, hle, hz]
  have hy'0 : y' ≠ 0 := hnz (2 * z) h2zmem y' hy'
  have hwne : w ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hwy
    exact hy'0 hwy.symm
  have hratinv : RatW (InvY Y) c z w⁻¹ :=
    (ratW_invY_iff Y c z w⁻¹).mpr ⟨inv_ne_zero hwne, by
      rw [inv_inv]
      exact ⟨y, y', hy, hy', hy0, hwy⟩⟩
  have hlt := hΓ (((N : ℝ) / 2) / 2) hβΓ c z w⁻¹ hz hdeepHalf hratinv
  have hquarter : ((N : ℝ) / 2) / 2 = (N : ℝ) / 4 := by ring
  rw [hquarter] at hlt
  have hwabs : 0 < |w| := abs_pos.mpr hwne
  have hlt' : (1 : ℝ) / |w| < (N : ℝ) / 4 := by
    rw [abs_inv, inv_eq_one_div] at hlt
    exact hlt
  have h4 : (4 : ℝ) / (N : ℝ) < |w| := by
    rw [div_lt_iff₀ hNpos]
    have h := (div_lt_iff₀ hwabs).mp hlt'
    nlinarith [h]
  have h24 : (2 : ℝ) / (N : ℝ) < (4 : ℝ) / (N : ℝ) :=
    div_lt_div_of_pos_right (by norm_num) hNpos
  linarith

/-! ## 2. `0` is not a cluster value -/

/-- **`0 ∉ ClusterE Y B`.**  A `0`-witness at the scale `N` of `ratW_gt_of_window_aux` is a point
`x` whose window `[x/N, Nx]` is `B`-free, so the ratio at `x` is `> 2/N` by the lower bound, while
the witness condition forces it to be `≤ 1/N`. -/
theorem zero_not_mem_clusterE_aux {k : ℕ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hOM : WilkiesDesign.CG.OMinModels) (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (B : Set (Fin (k + 1) → ℝ)) (hB : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B)
    (hst : ULPMStruct Y B) :
    (0 : ℝ) ∉ ClusterE Y B := by
  intro h0
  have h0R : (0 : ℝ) ∈ ClusterER Y B := ClusterE_subset_ClusterER Y B h0
  obtain ⟨N, hN2, hNgt⟩ := ratW_gt_of_window_aux hR hOM hPB Y hY hfun B hB hst
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  obtain ⟨c, x, hx, hdeep, hrat⟩ := h0R (N : ℝ) hNpos
  have hxI : x ∈ Set.Ioo (x / (2 * (N : ℝ))) (2 * (N : ℝ) * x) := by
    constructor
    · rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (N : ℝ))]
      nlinarith [hx, hNr]
    · nlinarith [hx, hNr]
  have h2xI : 2 * x ∈ Set.Ioo (x / (2 * (N : ℝ))) (2 * (N : ℝ) * x) := by
    constructor
    · rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (N : ℝ))]
      nlinarith [hx, hNr]
    · nlinarith [hx, hNr]
  obtain ⟨hg1, hnz1⟩ := deep_val hst.1 hN1 hx hdeep hxI
  obtain ⟨hg2, hnz2⟩ := deep_val hst.1 hN1 hx hdeep h2xI
  set w : ℝ := valY Y c (2 * x) / valY Y c x with hwdef
  have hratW : RatW Y c x w := by
    refine ⟨valY Y c x, valY Y c (2 * x), hg1, hg2, hnz1, ?_⟩
    rw [hwdef]
    field_simp
  have hfree : ∀ t : ℝ, x / (N : ℝ) ≤ t → t ≤ (N : ℝ) * x → Fin.cons t c ∉ B := by
    intro t ht1 ht2 hBmem
    refine hdeep t hBmem ⟨?_, ?_⟩
    · have h1 : x / (2 * (N : ℝ)) ≤ x / (N : ℝ) := by
        rw [two_mul]
        exact div_le_div_of_nonneg_left (le_of_lt hx) hNpos (by linarith)
      linarith
    · nlinarith [ht2, hNpos, hx]
  have hgt : (2 : ℝ) / (N : ℝ) < |w| :=
    hNgt c x x w hx le_rfl (by linarith) hfree hratW
  have hub : |w| ≤ 1 / (N : ℝ) := by
    have h := hrat x (by rw [div_le_iff₀ hNpos]; nlinarith [hx, hN1])
      (by nlinarith [hx, hN1]) (valY Y c x) (valY Y c (2 * x)) hg1 hg2 hnz1
    rw [hwdef]
    simpa using h
  have hle : (2 : ℝ) / (N : ℝ) ≤ (1 : ℝ) / (N : ℝ) := le_of_lt (lt_of_lt_of_le hgt hub)
  rw [div_le_div_iff_of_pos_right hNpos] at hle
  norm_num at hle

end Work.WilC4
