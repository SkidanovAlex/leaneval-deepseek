import Mathlib
import Submission.Work.Peluse.UControl.petQuad2Defs
import Submission.Work.Peluse.UControl.petWindowAux
import Submission.Work.Peluse.UControl.lambdaMD_le_l1
import Submission.Work.Peluse.UControl.linFamAvg_radius_le
import Submission.Work.Peluse.UControl.histPhase1RunInv
import Submission.Work.Peluse.UControl.levelCompareDefs
import Submission.Work.Peluse.UControl.petInitSym_SB

/-!
# Bookkeeping lemmas for the quadratic chapter

The elementary lemmas of `petChapter5_quadratic`: the two scale inequalities
(`M ≤ N` and the shell bound are `petQuad5MleN`/`petQuad5Shell`), the `ℓ¹`-mass of the top slot
function at the level of the window, the numeric domination of the constants, and the window
bound of the corner regime.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-! ## The symmetric interval `symIcc` -/

lemma mem_symIcc_natAbs {N : ℕ} {x : ℤ} : x ∈ symIcc N ↔ x.natAbs ≤ N := by
  rw [symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |x| ≤ (N : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · intro h
    have h' : |x| ≤ (N : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h
    exact abs_le.mp h'

/-- The `ℓ¹`-mass of a function supported in `[-N,N]` is the sum over the symmetric interval. -/
lemma tsum_norm_eq_sum_symIcc {g : ℤ → ℂ} {N : ℕ} (hg : SupportIn g N) :
    ∑' x : ℤ, ‖g x‖ = ∑ x ∈ symIcc N, ‖g x‖ := by
  rw [tsum_eq_sum (s := symIcc N)]
  intro x hx
  rw [hg x (not_le.mp fun h => hx (mem_symIcc_natAbs.mpr h)), norm_zero]

/-! ## The top slot function carries the correlation -/

/-- The `ℓ¹`-mass over the symmetric interval of the *top* slot function is at least `γN`: this is
the elementary `ℓ¹`-bound `lambdaMD_le_l1` for the multilinear progresssion average. -/
lemma gamma_mul_le_sum_symIcc {N M : ℕ} {P : Polynomial ℤ}
    {F : Fin (P.natDegree + 1) → ℤ → ℂ} {γ : ℝ}
    (hN : 0 < N) (hFb : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, SupportIn (F i) N)
    (hΛ : γ ≤ ‖LambdaMD N M P F‖) :
    γ * (N : ℝ) ≤ ∑ x ∈ symIcc N, ‖F ⟨P.natDegree, Nat.lt_succ_self _⟩ x‖ := by
  have h1 : ‖LambdaMD N M P F‖
      ≤ (∑' x : ℤ, ‖F ⟨P.natDegree, Nat.lt_succ_self _⟩ x‖) / N :=
    lambdaMD_le_l1 N M P F hN hFb hFs
  rw [tsum_norm_eq_sum_symIcc (hFs _)] at h1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hSnn : (0 : ℝ) ≤ ∑ x ∈ symIcc N, ‖F ⟨P.natDegree, Nat.lt_succ_self _⟩ x‖ :=
    Finset.sum_nonneg (fun x _ => norm_nonneg _)
  have h2 : γ * (N : ℝ) ≤ ‖LambdaMD N M P F‖ * (N : ℝ) :=
    mul_le_mul_of_nonneg_right hΛ (by positivity)
  have h3 : ‖LambdaMD N M P F‖ * (N : ℝ)
      ≤ ((∑ x ∈ symIcc N, ‖F ⟨P.natDegree, Nat.lt_succ_self _⟩ x‖) / N) * (N : ℝ) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have h4 : ((∑ x ∈ symIcc N, ‖F ⟨P.natDegree, Nat.lt_succ_self _⟩ x‖) / N) * (N : ℝ)
      = ∑ x ∈ symIcc N, ‖F ⟨P.natDegree, Nat.lt_succ_self _⟩ x‖ := by
    field_simp
  linarith [h2, h3, h4.le, h4.ge]

/-! ## The two scale inequalities -/

/-- **The window forces `M ≤ N`.**  From `2 ≤ ⌊δ'M⌋` and `Aδ' ≤ γ^6` one gets `M ≥ 2A/γ^6 ≥ A/γ`,
and then `M² ≤ AN/γ` gives `N ≥ M²γ/A ≥ M`. -/
lemma petQuad5MleN {A γ δ' : ℝ} {N M : ℕ} (hA : 1 ≤ A)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hδ'0 : 0 < δ') (hδle : A * δ' ≤ γ ^ 6)
    (hHδ : 2 ≤ ⌊δ' * (M : ℝ)⌋.toNat) (hsc2 : (M : ℝ) ^ 2 ≤ A * γ⁻¹ * (N : ℝ)) :
    (M : ℝ) ≤ (N : ℝ) := by
  have hApos : (0 : ℝ) < A := by linarith
  have hδM : (2 : ℝ) ≤ δ' * (M : ℝ) := by
    have h1 : (2 : ℤ) ≤ ⌊δ' * (M : ℝ)⌋ := by
      by_contra hlt
      have hle : ⌊δ' * (M : ℝ)⌋ ≤ 0 := by omega
      rw [Int.toNat_of_nonpos hle] at hHδ
      omega
    have h2 : (2 : ℝ) ≤ ((⌊δ' * (M : ℝ)⌋ : ℤ) : ℝ) := by exact_mod_cast h1
    linarith [h2, Int.floor_le (δ' * (M : ℝ))]
  have hMpos : 0 < (M : ℝ) := by nlinarith [hδM, hδ'0]
  -- `2A/γ^6 ≤ M`
  have hstep1 : 2 * A / γ ^ 6 ≤ (M : ℝ) := by
    have h1 : A / γ ^ 6 ≤ 1 / δ' := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < γ ^ 6) hδ'0]
      linarith [hδle]
    have h2 : 1 / δ' ≤ 2 / δ' := by
      rw [div_le_div_iff₀ hδ'0 hδ'0]; linarith
    have h3 : 2 / δ' ≤ (M : ℝ) := by
      rw [div_le_iff₀ hδ'0]; linarith [hδM]
    have h5 : 2 * (A / γ ^ 6) ≤ 2 * (1 / δ') := mul_le_mul_of_nonneg_left h1 (by norm_num)
    have h6 : 2 * (A / γ ^ 6) = 2 * A / γ ^ 6 := by ring
    have h7 : 2 * (1 / δ') = 2 / δ' := by ring
    linarith [h5, h6.le, h6.ge, h7.le, h7.ge, h3]
  -- `A/γ ≤ M`
  have hstep2 : A / γ ≤ (M : ℝ) := by
    have h1 : A / γ ≤ 2 * A / γ ^ 6 := by
      have hγ5 : γ ^ 5 ≤ 2 := by
        have := pow_le_one₀ hγ0.le hγ1 (n := 5)
        linarith
      rw [div_le_div_iff₀ hγ0 (by positivity : (0 : ℝ) < γ ^ 6)]
      have h5 : A * γ ^ 6 ≤ 2 * A * γ := by
        have h6 : A * γ ^ 6 = (A * γ ^ 5) * γ := by ring
        rw [h6]
        refine mul_le_mul_of_nonneg_right ?_ hγ0.le
        have h7 : A * γ ^ 5 ≤ A * 2 := mul_le_mul_of_nonneg_left hγ5 hApos.le
        linarith [h7]
      exact h5
    linarith [h1, hstep1]
  have hγA : A ≤ (M : ℝ) * γ := by
    rw [div_le_iff₀ hγ0] at hstep2
    linarith [hstep2]
  have h13 : 1 ≤ (M : ℝ) * γ / A := by
    rw [le_div_iff₀ hApos]; linarith
  have h9 : (M : ℝ) ^ 2 * γ / A ≤ (N : ℝ) := by
    rw [div_le_iff₀ hApos]
    have h11 : (M : ℝ) ^ 2 * γ ≤ A * (N : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hsc2 hγ0.le
      have heq : A * γ⁻¹ * (N : ℝ) * γ = A * (N : ℝ) := by
        field_simp
      linarith [h, heq.le, heq.ge]
    linarith [h11]
  have h12 : (M : ℝ) ≤ (M : ℝ) ^ 2 * γ / A := by
    rw [le_div_iff₀ hApos]
    nlinarith [h13, hMpos]
  linarith [h12, h9]

/-- **The corner window bound.**  In the small-window regime `petWindow·M < 2` the datum's window
is bounded: `⌊δ'M⌋ ≤ ⌈2 Cpw⌉ = qKc`. -/
lemma petQuad5FloorQKc (P : Polynomial ℤ) {A γ δ' : ℝ} {M : ℕ}
    (hA : 1 ≤ A) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hδ'0 : 0 < δ')
    (hδle : A * δ' ≤ γ ^ 6)
    (hDle : ((qD0 P A γ : ℕ) : ℝ) ≤ 2 * qW P * A / γ)
    (hsmall : petWindow γ (qD0 P A γ) 2 * (M : ℝ) < 2) :
    (⌊δ' * (M : ℝ)⌋).toNat ≤ qKc P := by
  have hD1 : 1 ≤ qD0 P A γ := by
    rw [qD0, qDc]
    refine Nat.one_le_ceil_iff.mpr ?_
    have h1 : (1 : ℝ) ≤ 1 + (qSp P : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) (qSp P); linarith
    have h2 : (1 : ℝ) ≤ A / γ := by rw [le_div_iff₀ hγ0]; linarith
    have h3 : (0 : ℝ) < (2 : ℝ) ^ 2 := by norm_num
    nlinarith [h1, h2, h3]
  have hW1 : 1 ≤ qW P := by
    rw [qW]
    have h1 : (1 : ℝ) ≤ 1 + (qSp P : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) (qSp P); linarith
    linarith
  have hpwpos : 0 < petWindow γ (qD0 P A γ) 2 :=
    petWindow_pos γ (qD0 P A γ) 2 hγ0 hγ1 (by norm_num) hD1
  have hratio : δ' / qCpw P ≤ petWindow γ (qD0 P A γ) 2 := by
    have h := petWindow_ratio_le γ (qD0 P A γ) 2 A (qW P) δ' 6 hγ0 hγ1 hA (by norm_num) hD1
      hW1 hDle hδ'0 (by rw [le_div_iff₀ (by linarith : (0:ℝ) < A)]; linarith [hδle])
      (by norm_num)
    simpa [qCpw] using h
  have hCpos : 0 < qCpw P := by
    rw [qCpw]
    exact petWinConst_pos 2 (by linarith)
  have hδ'C : δ' ≤ qCpw P * petWindow γ (qD0 P A γ) 2 := by
    have h := mul_le_mul_of_nonneg_right hratio hCpos.le
    rw [div_mul_cancel₀ _ (ne_of_gt hCpos)] at h
    linarith [h]
  have hlt : δ' * (M : ℝ) < 2 * qCpw P := by
    have h1 : δ' * (M : ℝ) ≤ (qCpw P * petWindow γ (qD0 P A γ) 2) * (M : ℝ) :=
      mul_le_mul_of_nonneg_right hδ'C (by positivity)
    have h2 : (qCpw P * petWindow γ (qD0 P A γ) 2) * (M : ℝ)
        = qCpw P * (petWindow γ (qD0 P A γ) 2 * (M : ℝ)) := by ring
    rw [h2] at h1
    nlinarith [h1, hsmall, hCpos]
  have h1 : ⌊δ' * (M : ℝ)⌋ ≤ ⌊2 * qCpw P⌋ := Int.floor_mono hlt.le
  have h2 : ⌊2 * qCpw P⌋ ≤ ((⌈2 * qCpw P⌉₊ : ℕ) : ℤ) := by
    have h := Nat.le_ceil (2 * qCpw P)
    have h' : (⌊2 * qCpw P⌋ : ℝ) ≤ ((⌈2 * qCpw P⌉₊ : ℕ) : ℝ) :=
      le_trans (Int.floor_le _) h
    exact_mod_cast h'
  have h4 : (0 : ℤ) ≤ ⌊δ' * (M : ℝ)⌋ :=
    Int.floor_nonneg.mpr (by positivity)
  have h5 : ((⌊δ' * (M : ℝ)⌋).toNat : ℤ) ≤ ((⌈2 * qCpw P⌉₊ : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h4]
    exact le_trans h1 h2
  have h6 : ((⌊δ' * (M : ℝ)⌋).toNat : ℤ) ≤ ((qKc P : ℕ) : ℤ) := by
    rw [qKc]; exact h5
  exact_mod_cast h6

/-! ## The numeric dominations -/

lemma qCpw_nonneg (P : Polynomial ℤ) : (0 : ℝ) ≤ qCpw P := by
  rw [qCpw, petWinConst, qW]; positivity

lemma four_abs_lc_le_qKconst (P : Polynomial ℤ) :
    4 * |(P.leadingCoeff : ℝ)| ≤ qKconst P := by
  rw [qKconst, Int.cast_abs]
  have hCpw := qCpw_nonneg P
  have hKc : (0 : ℝ) ≤ (qKc P : ℝ) := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ (qKc P : ℝ) * (2 * qCpw P) + 1 := by nlinarith
  have h3 : (0 : ℝ) ≤ 4 * |(P.leadingCoeff : ℝ)| := by positivity
  have h4 : (0 : ℝ) ≤ 20 * (qSp P : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) (qSp P); linarith
  nlinarith [h1, h3, h4]

lemma twenty_qSp_le_qKconst (P : Polynomial ℤ) :
    20 * (qSp P : ℝ) + 1 ≤ qKconst P := by
  rw [qKconst, Int.cast_abs]
  have hCpw := qCpw_nonneg P
  have hKc : (0 : ℝ) ≤ (qKc P : ℝ) := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ 4 * |(P.leadingCoeff : ℝ)| * ((qKc P : ℝ) * (2 * qCpw P) + 1) := by
    have h1 : (0 : ℝ) ≤ |(P.leadingCoeff : ℝ)| := by positivity
    have h2 : (0 : ℝ) ≤ (qKc P : ℝ) * (2 * qCpw P) := by nlinarith
    nlinarith [h1, h2]
  linarith [h3]

lemma one_le_qKconst (P : Polynomial ℤ) : 1 ≤ qKconst P := by
  have h := twenty_qSp_le_qKconst P
  have h2 : (0 : ℝ) ≤ 20 * (qSp P : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) (qSp P); linarith
  linarith [h, h2]

lemma qCstB_le_qCst1 (P : Polynomial ℤ) : qCstB P ≤ qCst1 P := le_max_right _ _

/-- From `x ≤ y` (with `x ≥ 0`) one gets `⌊x⌋.toNat ≤ ⌊y⌋.toNat`. -/
lemma toNat_floor_le_of_le {x y : ℝ} (hx : 0 ≤ x) (h : x ≤ y) :
    ⌊x⌋.toNat ≤ ⌊y⌋.toNat := by
  have hy : 0 ≤ y := le_trans hx h
  have h1 : ((⌊x⌋.toNat : ℤ)) ≤ ((⌊y⌋.toNat : ℤ)) := by
    rw [Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx),
      Int.toNat_of_nonneg (Int.floor_nonneg.mpr hy)]
    exact Int.floor_mono h
  exact_mod_cast h1


/-- `⌊x⌋.toNat` (as a real) is at most `x`. -/
lemma toNat_floor_cast_le {x : ℝ} (hx : 0 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℝ) ≤ x := by
  have h1 : ((⌊x⌋.toNat : ℕ) : ℤ) ≤ ⌊x⌋ := by
    rw [Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx)]
  have h2 : ((⌊x⌋.toNat : ℕ) : ℝ) ≤ ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast h1
  linarith [h2, Int.floor_le x]

/-- `x - 1 ≤ ⌊x⌋.toNat` for `x ≥ 0`. -/
lemma sub_one_le_toNat_floor {x : ℝ} (hx : 0 ≤ x) : x - 1 ≤ ((⌊x⌋.toNat : ℕ) : ℝ) := by
  have h1 : ((⌊x⌋.toNat : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by
    have h := Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx)
    exact_mod_cast h
  rw [h1]
  have h2 := Int.lt_floor_add_one x
  linarith [h2]

/-- The level-one datum at `n = 2` has three slots in total. -/
lemma levelOneDatum_sum_card : (∑ j : Fin 2, Fintype.card ((levelOneDatum 2).S j)) = 3 := by
  have h0 : Fintype.card ((levelOneDatum 2).S ((0 : Fin 2) : ℕ)) = 1 := Fintype.card_punit
  have h1 : Fintype.card ((levelOneDatum 2).S ((1 : Fin 2) : ℕ)) = 2 := Fintype.card_fin 2
  rw [Fin.sum_univ_two, h0, h1]


/-- **The box comparison with a clipped shift vector.**  If `H' ≤ H` and `β'` agrees with `β` on
`parBox l H'` and vanishes outside it, then the `H'`-average of the fibres with `β` dominates the
`(H' / H)`-fraction of the `H`-average of the fibres with `β'`. -/
lemma linFamAvg_clip_le {l : ℕ} (D : IdxDatum) (c : ℤ) (N M : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) {H H' : ℕ} (hh : H' ≤ H) :
    (((D.parBox l H').card : ℕ) : ℝ) / (((D.parBox l H).card : ℕ) : ℝ)
        * linFamAvg D l c N M H' f b β
      ≤ linFamAvg D l c N M H f b
          (fun a i => if a ∈ D.parBox l H' then β a i else 0) := by
  have hsub : D.parBox l H' ⊆ D.parBox l H := parBox_mono_radius D l hh
  have hSn : (((D.parBox l H).card : ℕ) : ℝ) ≠ 0 := by
    have := Finset.card_pos.mpr (parBox_nonempty D l H)
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  have hS'n : (((D.parBox l H').card : ℕ) : ℝ) ≠ 0 := by
    have := Finset.card_pos.mpr (parBox_nonempty D l H')
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  rw [linFamAvg_eq, linFamAvg_eq]
  have hfac : (((D.parBox l H').card : ℕ) : ℝ) / (((D.parBox l H).card : ℕ) : ℝ)
      * ((((D.parBox l H').card : ℕ) : ℝ)⁻¹ * ∑ a ∈ D.parBox l H', linFib D l c N M f b β a)
      = (((D.parBox l H).card : ℕ) : ℝ)⁻¹
        * ∑ a ∈ D.parBox l H', linFib D l c N M f b β a := by
    field_simp
  rw [hfac]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ∑ a ∈ D.parBox l H', linFib D l c N M f b β a
      = ∑ a ∈ D.parBox l H',
          linFib D l c N M f b (fun a i => if a ∈ D.parBox l H' then β a i else 0) a := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        have hβaeq : ∀ i, (if a ∈ D.parBox l H' then β a i else 0) = β a i :=
          fun i => if_pos ha
        simp only [linFib, hβaeq]
    _ ≤ ∑ a ∈ D.parBox l H,
          linFib D l c N M f b (fun a i => if a ∈ D.parBox l H' then β a i else 0) a :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by
          rw [linFib]; exact norm_nonneg _)

end

end Work.Peluse.UControl
