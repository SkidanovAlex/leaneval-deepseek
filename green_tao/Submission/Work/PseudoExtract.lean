import Submission.Work.Pseudo
import Submission.Work.PseudoCube
import Submission.Work.Halfway
import Submission.Commons.Analysis.Convex.sum_pow_le_card_pow_mul_sum_pow_of_one_le

set_option linter.unusedSectionVars false

/-!
# Extracting the cube-form pseudorandomness hypotheses from `KPseudorandom`

Green–Tao Definition 3.3 (`KPseudorandom`) packages the linear forms condition and the
correlation condition in their "general" form.  The transference machinery (and Green–Tao
Lemma 3.1 in the form `cube_corr_half`) uses the *cube* forms.  This file performs the
translation:

* `pseudo_cube_lfc` : the cube linear forms condition at scale `d = k-1`
  (via `cube_lfc_fixed` and monotonicity of `LinFormsCond`);
* `pseudo_mean` : the mean bound `|𝔼 ν - 1| ≤ ε` (the `m = 1` case of the LFC);
* `corrCond_finset` : the correlation condition in the *finset form* used by
  `cube_corr_half`, with a single weight `τ = Σ_m τ_m` and explicit moment bounds.
-/

open Finset
open scoped BigOperators

namespace GTTrans

/-- Monotonicity of the linear forms condition in its parameters. -/
lemma linFormsCond_mono {p : ℕ} [Fact p.Prime] {ν : ZMod p → ℝ} {m₀ t₀ L₀ m₁ t₁ L₁ : ℕ}
    {ε : ℝ} (h : LinFormsCond p ν m₀ t₀ L₀ ε) (hm : m₁ ≤ m₀) (ht : t₁ ≤ t₀) (hL : L₁ ≤ L₀) :
    LinFormsCond p ν m₁ t₁ L₁ ε := by
  intro ι _ _ h1 h2 t ht1 ht2 L hLs hne hnp b
  exact h ι h1 (le_trans h2 hm) t ht1 (le_trans ht2 ht) L
    (fun i j => ⟨le_trans (hLs i j).1 hL, le_trans (hLs i j).2 hL⟩) hne hnp b

/-- The cube linear forms condition at scale `d = k-1`, extracted from `KPseudorandom`. -/
theorem pseudo_cube_lfc {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 2 ≤ k) {ν : ZMod p → ℝ}
    {C : ℕ → ℕ → ℝ} {ε : ℝ} (hP : KPseudorandom p k ν C ε) :
    ∀ A : Finset (Fin (k - 1) → Bool), A.Nonempty → (0 : Fin (k - 1) → Bool) ∉ A →
      ∀ b : ZMod p,
      |((Fintype.card (Fin (k - 1) → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin (k - 1) → ZMod p,
          ∏ ω ∈ A,
            ν (b + ∑ j : Fin (k - 1), (if ω j then (1 : ZMod p) else 0) * h j)) - 1|
        ≤ ε := by
  have hd : 1 ≤ k - 1 := by omega
  have hk1 : 1 ≤ k := by omega
  have hmono : LinFormsCond p ν ((k - 1) * 2 ^ (k - 1)) (3 * (k - 1 + 1) - 4) (k - 1 + 1) ε := by
    have hm : (k - 1) * 2 ^ (k - 1) ≤ k * 2 ^ (k - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have ht : 3 * (k - 1 + 1) - 4 ≤ 3 * k - 4 := by
      rw [Nat.sub_add_cancel hk1]
    have hL : k - 1 + 1 ≤ k := by omega
    exact linFormsCond_mono hP.1 hm ht hL
  intro A hA h0 b
  exact cube_lfc_fixed hd ν ε hmono A hA h0 b

/-- The mean bound `|𝔼 ν - 1| ≤ ε`, the `m = 1` case of the linear forms condition. -/
theorem pseudo_mean {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 2 ≤ k) {ν : ZMod p → ℝ}
    {C : ℕ → ℕ → ℝ} {ε : ℝ} (hP : KPseudorandom p k ν C ε) :
    |((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ν x - 1| ≤ ε := by
  have hk1 : 1 ≤ k := by omega
  have hcard1 : 1 ≤ Fintype.card (Fin 1) := by simp
  have hcard2 : Fintype.card (Fin 1) ≤ k * 2 ^ (k - 1) := by
    simp only [Fintype.card_fin]
    have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
    nlinarith
  have ht2 : 1 ≤ 3 * k - 4 := by omega
  have h := hP.1 (Fin 1) hcard1 hcard2 1 le_rfl ht2 (fun _ _ => (1 : ℚ))
    (fun i j => ⟨by simp [IsSmallRat]; omega, by simp [IsSmallRat]; omega⟩)
    (fun i => ⟨0, by simp⟩)
    (fun i i' hii => absurd (Subsingleton.elim i i') hii)
    (fun _ => 0)
  simp only [linForm, qmod] at h
  have hsimp : (∑ x : Fin 1 → ZMod p,
      ∏ _i : Fin 1, ν ((∑ j : Fin 1, ((1 : ℚ).num : ZMod p) / ((1 : ℚ).den : ZMod p)
        * x j) + 0)) = ∑ x : ZMod p, ν x := by
    have hpt : ∀ x : ZMod p, ν x = ν x := fun _ => rfl
    rw [← Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod p)) _ _ (by intro x; rfl)]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    rw [Fin.prod_univ_one]
    congr 1
    rw [Fin.sum_univ_one]
    norm_num
  have hcard : ((Fintype.card (Fin 1 → ZMod p) : ℝ)) = ((Fintype.card (ZMod p) : ℝ)) := by
    rw [Fintype.card_congr (Equiv.funUnique (Fin 1) (ZMod p))]
  rw [hcard] at h
  rwa [hsimp] at h

/-- Enumeration of a finset by `Fin s.card` (via the subtype). -/
noncomputable def enumEquiv {α : Type*} [DecidableEq α] (A : Finset α) :
    {x // x ∈ A} ≃ Fin A.card :=
  (Fintype.equivFin {x // x ∈ A}).trans (Fin.castOrderIso (Fintype.card_coe A)).toEquiv

lemma prod_enum {α : Type*} [DecidableEq α] (A : Finset α) (F : α → ℝ) :
    ∏ x ∈ A, F x = ∏ i : Fin A.card, F ((enumEquiv A).symm i).1 := by
  rw [← Finset.prod_attach A F, Finset.attach_eq_univ]
  exact (Equiv.prod_comp (enumEquiv A).symm (fun x : {x // x ∈ A} => F x.1)).symm

/-- Summing over a subtype is summing over the finset. -/
lemma sum_attach_eq {α : Type*} [DecidableEq α] (A : Finset α) (F : α → ℝ) :
    (∑ x : {ω // ω ∈ A}, F x.1) = ∑ x ∈ A, F x := by
  rw [← Finset.sum_attach A F, Finset.attach_eq_univ]

/-- The correlation condition in *finset form*, with a single weight `τ` and explicit moments. -/
theorem corrCond_finset {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) {ν : ZMod p → ℝ}
    {C : ℕ → ℕ → ℝ} (hC : CorrCond p ν (2 ^ d) C) :
    ∃ τ : ZMod p → ℝ, (∀ x, 0 ≤ τ x) ∧
      ∃ Cm : ℕ → ℝ, (∀ q, 1 ≤ q →
          ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τ x) ^ q ≤ Cm q) ∧
        ∀ A : Finset (Fin d → Bool), 2 ≤ A.card → ∀ h : Fin d → ZMod p,
          ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p,
              ∏ ω ∈ A, ν (y + ∑ i, (if ω i then h i else 0))
            ≤ ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'),
                τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))) := by
  classical
  have hτm : ∀ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, ∃ τ : ZMod p → ℝ, (∀ x, 0 ≤ τ x) ∧
      (∀ q : ℕ, 1 ≤ q → ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τ x) ^ q ≤ C m.1 q) ∧
      ∀ h : Fin m.1 → ZMod p,
        ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, ∏ i, ν (x + h i)
          ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), τ (h i - h j) := by
    intro m
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp m.2
    exact hC m.1 (by omega) hm2
  choose τm hτm0 hτmmom hτmcorr using hτm
  set L : ℕ := (Finset.univ : Finset {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}).card with hLdef
  set τ : ZMod p → ℝ := fun x => ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, τm m x with hτdef
  have hτ0 : ∀ x, 0 ≤ τ x := fun x => Finset.sum_nonneg fun m _ => hτm0 m x
  have hNpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by positivity
  have hNne : ((Fintype.card (ZMod p) : ℝ)) ≠ 0 := ne_of_gt hNpos
  refine ⟨τ, hτ0, ?_⟩
  refine ⟨fun q => (L : ℝ) ^ (q - 1) *
      ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, max (C m.1 q) 0, ?_, ?_⟩
  · intro q hq
    have hpm : ∀ x : ZMod p, (∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, τm m x) ^ q ≤
        (L : ℝ) ^ (q - 1) * ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, (τm m x) ^ q := by
      intro x
      rw [hLdef]
      exact Commons.Analysis.Convex.sum_pow_le_card_pow_mul_sum_pow_of_one_le
        (Finset.univ) (fun m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)} => τm m x) q hq
        (fun m _ => hτm0 m x)
    have hA : (∑ x, (∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, τm m x) ^ q) ≤
        (L : ℝ) ^ (q - 1) *
          ∑ x, ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, (τm m x) ^ q := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ => hpm x
    have hB : (∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, ∑ x, (τm m x) ^ q) ≤
        (Fintype.card (ZMod p) : ℝ) *
          ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, max (C m.1 q) 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m _
      have h1 : ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τm m x) ^ q ≤ max (C m.1 q) 0 :=
        le_trans (hτmmom m q hq) (le_max_left _ _)
      have h2 := mul_le_mul_of_nonneg_left h1 hNpos.le
      have h3 : ((Fintype.card (ZMod p) : ℝ)) *
            (((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τm m x) ^ q)
          = ∑ x, (τm m x) ^ q := by
        rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
      rw [h3] at h2
      exact h2
    calc ((Fintype.card (ZMod p) : ℝ))⁻¹ *
          ∑ x, (∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, τm m x) ^ q
        ≤ ((Fintype.card (ZMod p) : ℝ))⁻¹ *
            ((L : ℝ) ^ (q - 1) *
              ∑ x, ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, (τm m x) ^ q) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = ((Fintype.card (ZMod p) : ℝ))⁻¹ *
            ((L : ℝ) ^ (q - 1) *
              ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, ∑ x, (τm m x) ^ q) := by
          rw [Finset.sum_comm]
      _ ≤ ((Fintype.card (ZMod p) : ℝ))⁻¹ *
            ((L : ℝ) ^ (q - 1) *
              ((Fintype.card (ZMod p) : ℝ) *
                ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, max (C m.1 q) 0)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hB (by positivity)
      _ = (L : ℝ) ^ (q - 1) *
            ∑ m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}, max (C m.1 q) 0 := by
          field_simp
  · intro A hA h
    have hk1 : 1 ≤ A.card := by omega
    have hm2 : 1 < A.card := by omega
    have hmle : A.card ≤ 2 ^ d :=
      calc A.card ≤ (Finset.univ : Finset (Fin d → Bool)).card :=
            Finset.card_le_card fun x _ => Finset.mem_univ x
        _ = 2 ^ d := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_bool]
    have hmem : A.card ∈ Finset.Icc 2 (2 ^ d) := Finset.mem_Icc.mpr ⟨by omega, hmle⟩
    set hs : Fin A.card → ZMod p :=
      fun i => ∑ j, (if ((enumEquiv A).symm i).1 j then h j else 0) with hsdef
    set u : (Fin d → Bool) → ZMod p :=
      fun ω => ∑ i, (if ω i then h i else 0) with hudef
    have hcorrA := hτmcorr ⟨A.card, hmem⟩ hs
    have hτle : ∀ x : ZMod p, τm ⟨A.card, hmem⟩ x ≤ τ x := by
      intro x
      rw [hτdef]
      exact Finset.single_le_sum (f := fun m : {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)} => τm m x)
        (fun m _ => hτm0 m x) (Finset.mem_univ (⟨A.card, hmem⟩ :
          {m : ℕ // m ∈ Finset.Icc 2 (2 ^ d)}))
    have hsu : ∀ x : {ω // ω ∈ A}, hs (enumEquiv A x) = u x.1 := by
      intro x
      simp only [hsdef, hudef, Equiv.symm_apply_apply]
    -- the product identity
    have hprod : ∀ y : ZMod p, (∏ ω ∈ A, ν (y + u ω)) = ∏ i : Fin A.card, ν (y + hs i) := by
      intro y
      rw [prod_enum A (fun ω => ν (y + u ω))]
    -- reindexing the double sum
    have h1 : (∑ i : Fin A.card, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), τ (hs i - hs j))
        = ∑ i : Fin A.card, ∑ j : Fin A.card,
            (if j ≠ i then τ (hs i - hs j) else 0) := by
      apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_filter]
    have h2 : (∑ i : Fin A.card, ∑ j : Fin A.card,
            (if j ≠ i then τ (hs i - hs j) else 0))
        = ∑ x : {ω // ω ∈ A}, ∑ y : {ω // ω ∈ A},
            (if y ≠ x then τ (u x.1 - u y.1) else 0) := by
      rw [show (∑ i : Fin A.card, ∑ j : Fin A.card,
            (if j ≠ i then τ (hs i - hs j) else 0))
          = ∑ i : Fin A.card, ∑ y : {ω // ω ∈ A},
              (if enumEquiv A y ≠ i then τ (hs i - hs (enumEquiv A y)) else 0) from by
            apply Finset.sum_congr rfl; intro i _
            exact (Equiv.sum_comp (enumEquiv A)
              (fun j => if j ≠ i then τ (hs i - hs j) else 0)).symm]
      rw [show (∑ i : Fin A.card, ∑ y : {ω // ω ∈ A},
              (if enumEquiv A y ≠ i then τ (hs i - hs (enumEquiv A y)) else 0))
          = ∑ x : {ω // ω ∈ A}, ∑ y : {ω // ω ∈ A},
              (if enumEquiv A y ≠ enumEquiv A x
                then τ (hs (enumEquiv A x) - hs (enumEquiv A y)) else 0) from
            (Equiv.sum_comp (enumEquiv A) (fun i => ∑ y : {ω // ω ∈ A},
              (if enumEquiv A y ≠ i then τ (hs i - hs (enumEquiv A y)) else 0))).symm]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _
      rw [hsu x, hsu y]
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne : ¬ (enumEquiv A y = enumEquiv A x) :=
          fun hh => hyx ((enumEquiv A).injective hh)
        simp [hyx, hne]
    have h3 : (∑ x : {ω // ω ∈ A}, ∑ y : {ω // ω ∈ A},
            (if y ≠ x then τ (u x.1 - u y.1) else 0))
        = ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω' ≠ ω), τ (u ω - u ω') := by
      rw [← sum_attach_eq A (fun ω => ∑ ω' ∈ A.filter (fun ω' => ω' ≠ ω), τ (u ω - u ω'))]
      apply Finset.sum_congr rfl; intro x _
      rw [show (∑ ω' ∈ A.filter (fun ω' => ω' ≠ ↑x), τ (u ↑x - u ω'))
          = ∑ y : {ω // ω ∈ A}, (if y.1 ≠ x.1 then τ (u x.1 - u y.1) else 0) from by
            rw [Finset.sum_filter,
              ← sum_attach_eq A (fun ω' => if ω' ≠ ↑x then τ (u ↑x - u ω') else 0)]]
      apply Finset.sum_congr rfl; intro y _
      by_cases hyx : y.1 = x.1
      · have hyx' : y = x := Subtype.ext hyx
        simp [hyx, hyx']
      · have : ¬ (y = x) := fun hh => hyx (congrArg Subtype.val hh)
        simp [hyx, this]
    -- the swap of the two summation indices
    have hprod_swap : (∑ p ∈ A.product A, (if p.2 ≠ p.1 then τ (u p.1 - u p.2) else 0))
        = ∑ p ∈ A.product A, (if p.1 ≠ p.2 then τ (u p.2 - u p.1) else 0) := by
      refine Finset.sum_bij' (fun p _ => (p.2, p.1)) (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).2, (Finset.mem_product.mp hp).1⟩
      · intro p hp
        exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).2, (Finset.mem_product.mp hp).1⟩
      · intro p hp; rfl
      · intro p hp; rfl
      · intro p hp
        by_cases hne : p.2 ≠ p.1
        · have hne' : p.1 ≠ p.2 := hne.symm
          simp [hne, hne']
        · have hne' : ¬ (p.1 ≠ p.2) := fun hh => hne hh.symm
          simp [hne, hne']
    have hswap : (∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω' ≠ ω), τ (u ω - u ω'))
        = ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'), τ (u ω' - u ω) := by
      rw [show (∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω' ≠ ω), τ (u ω - u ω'))
          = ∑ p ∈ A.product A, (if p.2 ≠ p.1 then τ (u p.1 - u p.2) else 0) from by
            rw [show (∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω' ≠ ω), τ (u ω - u ω'))
                = ∑ ω ∈ A, ∑ ω' ∈ A, (if ω' ≠ ω then τ (u ω - u ω') else 0) from by
                  apply Finset.sum_congr rfl; intro ω _; rw [Finset.sum_filter]]
            exact (Finset.sum_product (s := A) (t := A)
              (f := fun p : (Fin d → Bool) × (Fin d → Bool) =>
                if p.2 ≠ p.1 then τ (u p.1 - u p.2) else 0)).symm]
      rw [show (∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'), τ (u ω' - u ω))
          = ∑ p ∈ A.product A, (if p.1 ≠ p.2 then τ (u p.2 - u p.1) else 0) from by
            rw [show (∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'), τ (u ω' - u ω))
                = ∑ ω ∈ A, ∑ ω' ∈ A, (if ω ≠ ω' then τ (u ω' - u ω) else 0) from by
                  apply Finset.sum_congr rfl; intro ω _; rw [Finset.sum_filter]]
            exact (Finset.sum_product (s := A) (t := A)
              (f := fun p : (Fin d → Bool) × (Fin d → Bool) =>
                if p.1 ≠ p.2 then τ (u p.2 - u p.1) else 0)).symm]
      exact hprod_swap
    -- the step from pairs `i < j` to all ordered pairs
    have hstep : (∑ i : Fin A.card, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            τm ⟨A.card, hmem⟩ (hs i - hs j))
        ≤ ∑ i : Fin A.card, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), τ (hs i - hs j) := by
      apply Finset.sum_le_sum; intro i _
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
        (Finset.sum_le_sum fun j _ => hτle _)
      · intro j hj
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨Finset.mem_univ _, by omega⟩
      · intro j _ _
        exact hτm0 ⟨A.card, hmem⟩ _
    calc ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, ∏ ω ∈ A, ν (y + u ω)
        = ((Fintype.card (ZMod p) : ℝ))⁻¹ *
            ∑ y : ZMod p, ∏ i : Fin A.card, ν (y + hs i) := by
          rw [Finset.sum_congr rfl fun y _ => hprod y]
      _ ≤ ∑ i : Fin A.card, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            τm ⟨A.card, hmem⟩ (hs i - hs j) := hcorrA
      _ ≤ ∑ i : Fin A.card, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), τ (hs i - hs j) := hstep
      _ = ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω' ≠ ω), τ (u ω - u ω') := by rw [h1, h2, h3]
      _ = ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'), τ (u ω' - u ω) := hswap
      _ = ∑ ω ∈ A, ∑ ω' ∈ A.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))) := by
          rw [hudef]

/-- **The halfway measure of a `k`-pseudorandom measure.**  If `ν` is `k`-pseudorandom then
`ν' = (ν+1)/2` satisfies, at scale `d = k-1`, the cube linear forms condition (with the same
error) and the cube correlation condition (with an explicit weight and moments).  These are
exactly the hypotheses of `weier_bound`/`bohr_sigma_atom` with the majorant `ν'`, which is how
Green–Tao §7 accommodates the bound `|F_j| ≤ (1+o(1))(ν+1)` for the anti-uniform generators. -/
theorem pseudo_half {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 2 ≤ k) {ν : ZMod p → ℝ}
    {C : ℕ → ℕ → ℝ} {ε : ℝ} (hP : KPseudorandom p k ν C ε)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hν : ∀ x, 0 ≤ ν x) :
    ∃ τ' : ZMod p → ℝ, (∀ x, 0 ≤ τ' x) ∧ ∃ Cm' : ℕ → ℝ,
      (∀ q : ℕ, ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ x, (τ' x) ^ q ≤ Cm' q) ∧
      (∀ A : Finset (Fin (k - 1) → Bool), A ⊆ Finset.univ.erase (0 : Fin (k - 1) → Bool) →
        A.Nonempty → ∀ b : ZMod p,
        |((Fintype.card (Fin (k - 1) → ZMod p) : ℝ))⁻¹ *
          (∑ h : Fin (k - 1) → ZMod p, ∏ ω ∈ A,
            ((ν (b + ∑ j : Fin (k - 1), (if ω j then (1 : ZMod p) else 0) * h j)) + 1) / 2) - 1|
          ≤ ε) ∧
      (∀ h : Fin (k - 1) → ZMod p,
        ((Fintype.card (ZMod p) : ℝ))⁻¹ * ∑ y : ZMod p, ∏ ω : Fin (k - 1) → Bool,
            ((ν (y + ∑ i, (if ω i then h i else 0)) + 1) / 2)
          ≤ ∑ ω : Fin (k - 1) → Bool,
              ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
                τ' ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0)))) := by
  have hd : 1 ≤ k - 1 := by omega
  obtain ⟨τ, hτ0, Cm, hmom, hcorr⟩ := corrCond_finset (d := k - 1) hd hP.2
  obtain ⟨Cm', hCm'0, τ', hτ'0, hmom', hcorr'⟩ :=
    cube_corr_half (d := k - 1) hd ν hν hε hε1 (pseudo_mean hk hP) hτ0 hmom hcorr
  have hcube : ∀ A : Finset (Fin (k - 1) → Bool),
      A ⊆ Finset.univ.erase (0 : Fin (k - 1) → Bool) → A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin (k - 1) → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin (k - 1) → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin (k - 1), (if ω j then (1 : ZMod p) else 0) * h j)) - 1|
        ≤ ε := by
    intro A hA hne b
    exact pseudo_cube_lfc hk hP A hne (fun h0 => by
      have h1 := hA h0
      simp at h1) b
  exact ⟨τ', hτ'0, Cm', hmom', cube_lfc_half ν hε hcube, hcorr'⟩

end GTTrans
