import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.bmPot_holder_C0a
import Submission.Work.NN.Core.beltrami_theta_setup
import Submission.Work.NN.Core.holderNorm_le_of_tendsto
import Submission.Work.NN.Core.famMul_holderNorm_bound
import Submission.Work.NN.Core.famNorm_contraction_fixedpoint

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Core

/-! ## The multiplication operator `Σ_j conj(β i j ·) · Y_j`

The implicit Beltrami system solved here differs from the decoupled one of
`Work.NN.Core.beltrami_theta_fixedpoint` by the extra pointwise term
`- Σ_j conj(β i j z) · V_j z`, i.e. by multiplication with a small coefficient family.  This
section collects the elementary algebra of that multiplication operator, and the following
sections combine it with the Schauder estimates `BTheta.one_step_bound` /
`BTheta.one_step_finite` for the potential term. -/

/-- `starRingEnd ℂ` is an isometry of `ℂ`. -/
lemma mulFamAux_normStarRingEnd (w : ℂ) : ‖(starRingEnd ℂ) w‖ = ‖w‖ := norm_star w

/-- The `C^{0,α}`-norm is unchanged by conjugating the values. -/
lemma mulFamAux_conj_holderNorm_zero_le {n : ℕ} {α : ℝ} (f : (Fin n → ℂ) → ℂ)
    (Ω : Set (Fin n → ℂ)) :
    Work.CR.Flat.holderNorm 0 α (fun z => starRingEnd ℂ (f z)) Ω
      ≤ Work.CR.Flat.holderNorm 0 α f Ω := by
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm, Finset.sum_range_one,
    Finset.sum_range_one]
  apply add_le_add
  · simpa only [Work.CR.Flat.iterDerivNorm, norm_iteratedFDerivWithin_zero,
      mulFamAux_normStarRingEnd]
      using le_rfl
  · simp only [Work.CR.Flat.holderSeminorm]
    apply iSup₂_le; intro x hx; apply iSup₂_le; intro y hy; apply iSup_le; intro hxy
    refine le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy (le_of_eq ?_)))
    rw [BTheta.norm_iteratedFDerivWithin_zero_sub, BTheta.norm_iteratedFDerivWithin_zero_sub,
      show (starRingEnd ℂ) (f x) - (starRingEnd ℂ) (f y) = (starRingEnd ℂ) (f x - f y) by
        rw [map_sub],
      mulFamAux_normStarRingEnd]

/-- Multiplication of a family by a coefficient family: `(mulFam β Y) i z = Σ_j conj(β i j z) Y_j z`. -/
noncomputable def mulFam {n : ℕ} (β : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (Y : Fin n → (Fin n → ℂ) → ℂ) : Fin n → (Fin n → ℂ) → ℂ :=
  fun i z => ∑ j, (starRingEnd ℂ (β i j z)) * Y j z

lemma mulFam_sub {n : ℕ} (β : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (Y Y' : Fin n → (Fin n → ℂ) → ℂ) : mulFam β (Y - Y') = mulFam β Y - mulFam β Y' := by
  funext i z
  simp only [mulFam, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma mulFam_add {n : ℕ} (β : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (Y Y' : Fin n → (Fin n → ℂ) → ℂ) : mulFam β (Y + Y') = mulFam β Y + mulFam β Y' := by
  funext i z
  simp only [mulFam, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma mulFam_zero {n : ℕ} (β : Fin n → Fin n → (Fin n → ℂ) → ℂ) : mulFam β 0 = 0 := by
  funext i z
  simp [mulFam]

lemma mulFam_vanishes {n : ℕ} {ρ : Fin n → ℝ} {β : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hβsupp : ∀ i j z, β i j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    (Y : Fin n → (Fin n → ℂ) → ℂ) :
    ∀ i z, z ∉ Work.CR.Flat.polydisc 0 ρ → mulFam β Y i z = 0 := by
  intro i z hz
  simp only [mulFam]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : β i j z = 0 := by
    by_contra hc
    exact hz (hβsupp i j z hc)
  simp [this]

/-- Finiteness of the multiplication operator on families of finite `C^{0,α}`-norm. -/
lemma mulFam_famNorm_lt_top {n : ℕ} {α : ℝ} (β : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (Y : Fin n → (Fin n → ℂ) → ℂ)
    (hβ : ∀ i j, Work.CR.Flat.holderNorm 0 α (β i j) Set.univ < ⊤)
    (hY : ∀ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ < ⊤) :
    BTheta.famNorm α (mulFam β Y) < ⊤ := by
  rw [show BTheta.famNorm α (mulFam β Y)
      = ∑ i, Work.CR.Flat.holderNorm 0 α (mulFam β Y i) Set.univ from rfl]
  refine ENNReal.sum_lt_top.mpr fun i _ => ?_
  have hterm : ∀ j, Work.CR.Flat.holderNorm 0 α
        (fun z => (starRingEnd ℂ (β i j z)) * Y j z) Set.univ
      ≤ ENNReal.ofReal (3 * (Work.CR.Flat.holderNorm 0 α (β i j) Set.univ).toReal
          * (Work.CR.Flat.holderNorm 0 α (Y j) Set.univ).toReal) := by
    intro j
    refine BTheta.holderNorm_zero_mul_le_ofReal ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      ?_ ?_
    · exact (mulFamAux_conj_holderNorm_zero_le (β i j) Set.univ).trans
        (le_of_eq (ENNReal.ofReal_toReal (ne_of_lt (hβ i j))).symm)
    · exact (le_of_eq (ENNReal.ofReal_toReal (ne_of_lt (hY j))).symm)
  refine lt_of_le_of_lt ((BTheta.holderNorm_zero_sum_le Finset.univ
      (fun j => fun z => (starRingEnd ℂ (β i j z)) * Y j z) Set.univ).trans
      (Finset.sum_le_sum fun j _ => hterm j)) ?_
  exact ENNReal.sum_lt_top.mpr fun j _ => ENNReal.ofReal_lt_top

/-- The smallness bound for the multiplication operator. -/
lemma mulFam_famNorm_le {n : ℕ} {α : ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (β : Fin n → Fin n → (Fin n → ℂ) → ℂ) (Y : Fin n → (Fin n → ℂ) → ℂ)
    (hβ : ∀ i j, Work.CR.Flat.holderNorm 0 α (β i j) Set.univ ≤ ENNReal.ofReal δ)
    (hY : ∀ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ < ⊤) :
    BTheta.famNorm α (mulFam β Y) ≤
      ENNReal.ofReal (3 * (n : ℝ) * δ) * BTheta.famNorm α Y := by
  have hcomp : ∀ i, Work.CR.Flat.holderNorm 0 α (mulFam β Y i) Set.univ
      ≤ ENNReal.ofReal (3 * δ) * BTheta.famNorm α Y := by
    intro i
    have h := famMul_holderNorm_bound hδ β Y hβ hY i
    rw [show BTheta.famNorm α Y = ∑ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ from rfl]
    exact h
  have hsum : BTheta.famNorm α (mulFam β Y)
      = ∑ i, Work.CR.Flat.holderNorm 0 α (mulFam β Y i) Set.univ := rfl
  rw [hsum]
  refine (Finset.sum_le_sum (fun i _ => hcomp i)).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast n, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (n:ℝ))]
  rw [show (n : ℝ) * (3 * δ) = 3 * (n : ℝ) * δ by ring]

/-! ## The operator of the implicit Beltrami system -/

/-- The (linear) operator `T = Θ - M` of the implicit Beltrami system
`V_i = γ⁻¹ Σ_j β_ij ∂_j(ΦV) - Σ_j conj(β_ij) V_j + G_i`. -/
noncomputable def Tfun {n : ℕ} (β : Fin n → Fin n → (Fin n → ℂ) → ℂ)
    (Y : Fin n → (Fin n → ℂ) → ℂ) : Fin n → (Fin n → ℂ) → ℂ :=
  BTheta.beltramiTheta β Y - mulFam β Y

lemma Tfun_zero {n : ℕ} (β : Fin n → Fin n → (Fin n → ℂ) → ℂ) : Tfun β 0 = 0 := by
  funext i z
  simp [Tfun, BTheta.beltramiTheta_zero, mulFam]

lemma Tfun_vanishes {n : ℕ} {ρ : Fin n → ℝ} {β : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hβsupp : ∀ i j z, β i j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    (Y : Fin n → (Fin n → ℂ) → ℂ) :
    ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Tfun β Y j z = 0 := by
  intro j z hz
  have h1 := BTheta.beltramiTheta_vanishes hβsupp Y j z hz
  have h2 := mulFam_vanishes hβsupp Y j z hz
  simp only [Tfun, Pi.sub_apply]
  rw [h1, h2]
  simp

/-- `T` is additive on differences of families vanishing off the polydisc. -/
lemma Tfun_sub_apply {n : ℕ} {α : ℝ} (hn : 0 < n) (hα0 : 0 < α) (hα1 : α < 1)
    {ρ τ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hτ : ∀ j, 0 < τ j) (hρτ : ∀ j, ρ j < τ j)
    {β : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hβsupp : ∀ i j z, β i j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {Y Y' : Fin n → (Fin n → ℂ) → ℂ}
    (hYfin : ∀ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ < ⊤)
    (hYvan : ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Y j z = 0)
    (hY'fin : ∀ j, Work.CR.Flat.holderNorm 0 α (Y' j) Set.univ < ⊤)
    (hY'van : ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Y' j z = 0)
    (j : Fin n) (z : Fin n → ℂ) :
    Tfun β Y j z - Tfun β Y' j z = Tfun β (Y - Y') j z := by
  have hΘ := BTheta.beltramiTheta_sub_apply hn hα0 hα1 hρ hτ hρτ hβsupp
    hYfin hYvan hY'fin hY'van j z
  have hM : mulFam β (Y - Y') j z = mulFam β Y j z - mulFam β Y' j z := by
    simpa using congrFun (congrFun (mulFam_sub β Y Y') j) z
  change BTheta.beltramiTheta β Y j z - mulFam β Y j z
      - (BTheta.beltramiTheta β Y' j z - mulFam β Y' j z)
    = BTheta.beltramiTheta β (Y - Y') j z - mulFam β (Y - Y') j z
  rw [hM, ← hΘ]
  ring_nf

/-- `T` is additive in the data. -/
lemma Tfun_add_apply {n : ℕ} {α : ℝ} (hn : 0 < n) (hα0 : 0 < α) (hα1 : α < 1)
    {ρ τ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hτ : ∀ j, 0 < τ j) (hρτ : ∀ j, ρ j < τ j)
    {β : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hβsupp : ∀ i j z, β i j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {G Y : Fin n → (Fin n → ℂ) → ℂ}
    (hG1 : ∀ j, ContDiff ℝ 1 (G j)) (hGcs : ∀ j, HasCompactSupport (G j))
    (hGfin : ∀ j, Work.CR.Flat.holderNorm 0 α (G j) Set.univ < ⊤)
    (hYfin : ∀ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ < ⊤)
    (hYvan : ∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Y j z = 0)
    (j : Fin n) (z : Fin n → ℂ) :
    Tfun β (G + Y) j z = Tfun β G j z + Tfun β Y j z := by
  have hΘ := BTheta.beltramiTheta_add_apply hn hα0 hα1 hρ hτ hρτ hβsupp
    hG1 hGcs hGfin hYfin hYvan j z
  have hM : mulFam β (G + Y) j z = mulFam β G j z + mulFam β Y j z := by
    simpa using congrFun (congrFun (mulFam_add β G Y) j) z
  change BTheta.beltramiTheta β (G + Y) j z - mulFam β (G + Y) j z
    = (BTheta.beltramiTheta β G j z - mulFam β G j z)
      + (BTheta.beltramiTheta β Y j z - mulFam β Y j z)
  rw [hM, hΘ]
  ring_nf

/-- **Contraction estimate for `T`.**  There is a constant `C > 0` such that whenever `β` has
`C^{0,α}`-coefficients bounded by `δ` and supported in `polydisc 0 ρ`, and `Y` has finite norm
and vanishes off `polydisc 0 ρ`, then `famNorm (T β Y) ≤ C δ · famNorm Y`. -/
lemma Tfun_bound {n : ℕ} {α : ℝ} (hn : 0 < n) (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : Fin n → Fin n → (Fin n → ℂ) → ℂ)
      (Y : Fin n → (Fin n → ℂ) → ℂ) (δ : ℝ), 0 ≤ δ →
      (∀ i j, Work.CR.Flat.holderNorm 0 α (β i j) Set.univ ≤ ENNReal.ofReal δ) →
      (∀ i j z, β i j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
      (∀ j, Work.CR.Flat.holderNorm 0 α (Y j) Set.univ < ⊤) →
      (∀ j z, z ∉ Work.CR.Flat.polydisc 0 ρ → Y j z = 0) →
      BTheta.famNorm α (Tfun β Y) ≤ ENNReal.ofReal (C * δ) * BTheta.famNorm α Y := by
  set τ : Fin n → ℝ := fun j => 2 * ρ j with hτdef
  have hτpos : ∀ j, 0 < τ j := fun j => by rw [hτdef]; linarith [hρ j]
  have hρτ : ∀ j, ρ j < τ j := fun j => by rw [hτdef]; linarith [hρ j]
  obtain ⟨C1, hC1pos, hC1⟩ := BTheta.one_step_bound (n := n) hn (α := α) hα0 hα1 hρ hτpos hρτ
  refine ⟨(n : ℝ) * C1 + 3 * (n : ℝ) + 1, ?_, ?_⟩
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [hC1pos]
  · intro β Y δ hδ hβnorm hβsupp hYfin hYvan
    set F : ℝ≥0∞ := BTheta.famNorm α Y with hFdef
    have hΘ : BTheta.famNorm α (BTheta.beltramiTheta β Y)
        ≤ ENNReal.ofReal ((n : ℝ) * C1 * δ) * F := by
      have hcomp : ∀ i, Work.CR.Flat.holderNorm 0 α (BTheta.beltramiTheta β Y i) Set.univ
          ≤ ENNReal.ofReal (C1 * δ) * F := by
        intro i
        have h := hC1 (fun l => β i l) Y δ (fun l => hβnorm i l)
          (fun l z hz => hβsupp i l z hz) hYfin hYvan
        rw [show F = ∑ l, Work.CR.Flat.holderNorm 0 α (Y l) Set.univ from rfl]
        exact h
      have hsum : BTheta.famNorm α (BTheta.beltramiTheta β Y)
          = ∑ i, Work.CR.Flat.holderNorm 0 α (BTheta.beltramiTheta β Y i) Set.univ := rfl
      rw [hsum]
      refine (Finset.sum_le_sum (fun i _ => hcomp i)).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast n, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (n:ℝ))]
      rw [show (n : ℝ) * (C1 * δ) = (n : ℝ) * C1 * δ by ring]
    have hM : BTheta.famNorm α (mulFam β Y)
        ≤ ENNReal.ofReal (3 * (n : ℝ) * δ) * F := by
      rw [hFdef]
      exact mulFam_famNorm_le hδ β Y hβnorm hYfin
    calc BTheta.famNorm α (Tfun β Y)
        = BTheta.famNorm α (BTheta.beltramiTheta β Y - mulFam β Y) := rfl
      _ ≤ BTheta.famNorm α (BTheta.beltramiTheta β Y) + BTheta.famNorm α (mulFam β Y) :=
          BTheta.famNorm_sub_le _ _
      _ ≤ ENNReal.ofReal ((n : ℝ) * C1 * δ) * F + ENNReal.ofReal (3 * (n : ℝ) * δ) * F :=
          add_le_add hΘ hM
      _ = (ENNReal.ofReal ((n : ℝ) * C1 * δ) + ENNReal.ofReal (3 * (n : ℝ) * δ)) * F := by
          rw [add_mul]
      _ = ENNReal.ofReal ((n : ℝ) * C1 * δ + 3 * (n : ℝ) * δ) * F := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (((n : ℝ) * C1 + 3 * (n : ℝ) + 1) * δ) * F := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          nlinarith [hC1pos, hδ, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- Finiteness of `T` applied to a compactly supported `C¹` datum. -/
lemma Tfun_finite {n : ℕ} {α : ℝ} (hn : 0 < n) (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {β : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hβfin : ∀ i j, Work.CR.Flat.holderNorm 0 α (β i j) Set.univ < ⊤)
    (hβsupp : ∀ i j z, β i j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {G : Fin n → (Fin n → ℂ) → ℂ} (hG1 : ∀ j, ContDiff ℝ 1 (G j))
    (hGcs : ∀ j, HasCompactSupport (G j))
    (hGfin : ∀ j, Work.CR.Flat.holderNorm 0 α (G j) Set.univ < ⊤) :
    BTheta.famNorm α (Tfun β G) < ⊤ := by
  set τ : Fin n → ℝ := fun j => 2 * ρ j with hτdef
  have hτpos : ∀ j, 0 < τ j := fun j => by rw [hτdef]; linarith [hρ j]
  have hρτ : ∀ j, ρ j < τ j := fun j => by rw [hτdef]; linarith [hρ j]
  have hΘ : BTheta.famNorm α (BTheta.beltramiTheta β G) < ⊤ := by
    rw [show BTheta.famNorm α (BTheta.beltramiTheta β G)
        = ∑ i, Work.CR.Flat.holderNorm 0 α (BTheta.beltramiTheta β G i) Set.univ from rfl]
    refine ENNReal.sum_lt_top.mpr fun i _ => ?_
    obtain ⟨Ci, hCi, hbd⟩ := BTheta.one_step_finite (n := n) hn (α := α) hα0 hα1 hρ hτpos hρτ
      (fun l => β i l) G (fun l => hβfin i l) (fun l z hz => hβsupp i l z hz) hG1 hGcs hGfin
    exact lt_of_le_of_lt hbd ENNReal.ofReal_lt_top
  have hM : BTheta.famNorm α (mulFam β G) < ⊤ := mulFam_famNorm_lt_top β G hβfin hGfin
  calc BTheta.famNorm α (Tfun β G)
      = BTheta.famNorm α (BTheta.beltramiTheta β G - mulFam β G) := rfl
    _ ≤ BTheta.famNorm α (BTheta.beltramiTheta β G) + BTheta.famNorm α (mulFam β G) :=
        BTheta.famNorm_sub_le _ _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hΘ, hM⟩

/-! ## The implicit Beltrami fixed point -/

/-- **Existence for the implicit Beltrami system.**  For `β` of small `C^{0,α}`-norm and
supported in `polydisc 0 ρ`, and compactly supported `C¹` data `G`, there is a compactly
supported family `V` of finite `C^{0,α}`-norm with
`V_i = γ⁻¹ Σ_j β_ij ∂_j(ΦV) - Σ_j conj(β_ij) V_j + G_i`. -/
theorem beltramiImplicit_fixedpoint {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (β : Fin n → Fin n → Work.NN.Core.Cn n → ℂ) (G : Fin n → Work.NN.Core.Cn n → ℂ),
        (∀ i j, ∀ m : ℕ, ContDiff ℝ m (β i j)) →
        (∀ i j, HasCompactSupport (β i j)) →
        (∀ i j z, β i j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
        (∀ i j, Work.CR.Flat.holderNorm 0 α (β i j) Set.univ ≤ ENNReal.ofReal δ) →
        (∀ i, ContDiff ℝ 1 (G i)) →
        (∀ i, HasCompactSupport (G i)) →
        (∀ i, Work.CR.Flat.holderNorm 0 α (G i) Set.univ < ⊤) →
        ∃ V : Fin n → Work.NN.Core.Cn n → ℂ,
          (∀ i, HasCompactSupport (V i)) ∧
          (∀ i, Work.CR.Flat.holderNorm 0 α (V i) Set.univ < ⊤) ∧
          (∀ i z, V i z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
                (∑ j, β i j z * Work.CR.Flat.dCoord j (Work.CR.Flat.Cauchy.bmPotential V) z)
              - (∑ j, (starRingEnd ℂ (β i j z)) * V j z) + G i z) := by
  classical
  obtain ⟨Ctot, hCtotpos, hCtot⟩ := Tfun_bound (n := n) hn hα0 hα1 hρ
  refine ⟨1 / (2 * (Ctot + 1)), ?_, ?_⟩
  · positivity
  intro β G hβsm hβcs hβsupp hβnorm hG1 hGcs hGfin
  have hd0 : (0 : ℝ) < 1 / (2 * (Ctot + 1)) := by positivity
  have hlam : Ctot * (1 / (2 * (Ctot + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith [hCtotpos]
  set τ : Fin n → ℝ := fun j => 2 * ρ j with hτdef
  have hτpos : ∀ j, 0 < τ j := fun j => by rw [hτdef]; linarith [hρ j]
  have hρτ : ∀ j, ρ j < τ j := fun j => by rw [hτdef]; linarith [hρ j]
  have hβfin : ∀ i j, Work.CR.Flat.holderNorm 0 α (β i j) Set.univ < ⊤ :=
    fun i j => lt_of_le_of_lt (hβnorm i j) ENNReal.ofReal_lt_top
  obtain ⟨Y, hYfin, hYvan, hYeq⟩ := famNorm_contraction_fixedpoint (n := n) (α := α) hα0 hα1 hρ
    (Tfun β) (Ctot * (1 / (2 * (Ctot + 1)))) (by positivity) hlam
    (Tfun_zero β)
    (fun Y j z hz => Tfun_vanishes hβsupp Y j z hz)
    (fun Y Y' hYf hYv hY'f hY'v j z =>
      Tfun_sub_apply hn hα0 hα1 hρ hτpos hρτ hβsupp hYf hYv hY'f hY'v j z)
    (fun Y hYf hYv => hCtot β Y (1 / (2 * (Ctot + 1))) hd0.le hβnorm hβsupp hYf hYv)
    (Tfun_vanishes hβsupp G)
    (Tfun_finite hn hα0 hα1 hρ hβfin hβsupp hG1 hGcs hGfin)
  refine ⟨fun i => G i + Y i, ?_, ?_, ?_⟩
  · intro i
    exact (hGcs i).add (BTheta.hasCompactSupport_of_vanishing_off_polydisc hn hρ (hYvan i))
  · intro i
    refine lt_of_le_of_lt (BTheta.holderNorm_zero_add_le (G i) (Y i) Set.univ) ?_
    exact ENNReal.add_lt_top.mpr ⟨hGfin i, hYfin i⟩
  · intro i z
    have hadd := Tfun_add_apply hn hα0 hα1 hρ hτpos hρτ hβsupp hG1 hGcs hGfin hYfin hYvan i z
    have hYeqi := hYeq i z
    have hV : (fun i => G i + Y i) i z = Tfun β (G + Y) i z + G i z := by
      change G i z + Y i z = Tfun β (G + Y) i z + G i z
      rw [hadd, hYeqi]
      ring
    rw [hV]
    rfl

end Work.NN.Core
