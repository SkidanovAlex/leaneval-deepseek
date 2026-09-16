import Submission.ZagierHoffmanProof.ZetaCMPL
import Submission.ZagierHoffmanProof.AmbPeriodEll
import Submission.ZagierHoffmanProof.Step3Val
import Submission.ZagierHoffmanProof.LSeriesEvalDepth
import Submission.ZagierHoffmanProof.ChainSwap
import Submission.Commons.Topology.Algebra.Valued.summable_of_v_le_general

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset Filter
open scoped WithZero Topology
open SummationFilter

namespace ZagierHoffmanPositiveChar

/-! ## §1. The `tsum`-form of the iterated power sum -/

section NestT

variable {K : Type*} [CommSemiring K] [TopologicalSpace K]

/-- `nestT r X d` is the sum of `∏_j X_j(d_j)` over the strictly decreasing chains
`d > d_0 > d_1 > ⋯ > d_{r-1} ≥ 0`, written as an iterated `tsum`. -/
noncomputable def nestT : (r : ℕ) → (Fin r → ℕ → K) → ℕ → K
  | 0, _, _ => 1
  | (r+1), Y, d => ∑' i : ℕ,
      (if i < d then Y 0 i else 0) * nestT r (fun j : Fin r => Y j.succ) i

@[simp] lemma nestT_zero (Y : Fin 0 → ℕ → K) (d : ℕ) : nestT 0 Y d = 1 := rfl

lemma nestT_succ (r : ℕ) (Y : Fin (r+1) → ℕ → K) (d : ℕ) :
    nestT (r+1) Y d = ∑' i : ℕ,
      (if i < d then Y 0 i else 0) * nestT r (fun j : Fin r => Y j.succ) i := rfl

end NestT

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- `exp` turns a finite sum of exponents into a product. -/
lemma withZero_exp_finset_sum {G : Type*} [AddCommMonoid G] {ι : Type*} (f : ι → G) (s : Finset ι) :
    (∏ i ∈ s, WithZero.exp (f i)) = WithZero.exp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, WithZero.exp_zero]
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, WithZero.exp_add, ih]

/-- The `Finset.range`-sum as a `tsum` with the indicator `i < d`. -/
lemma sum_range_eq_tsum_ite (d : ℕ) (g : ℕ → Ambient F) :
    (∑ i ∈ Finset.range d, g i) = ∑' i : ℕ, (if i < d then g i else 0) := by
  rw [tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.range d)
    (f := fun i : ℕ => if i < d then g i else 0)
    (fun i hi => by rw [if_neg (by simpa [Finset.mem_range] using hi)])]
  exact Finset.sum_congr rfl (fun i hi => by rw [if_pos (Finset.mem_range.mp hi)])

/-- `nestLvl` is the iterated `tsum` `nestT`. -/
lemma nestLvl_eq_nestT (r : ℕ) (𝔰 : Fin r → ℕ+) (d : ℕ) :
    nestLvl F r 𝔰 d = nestT r (fun j i => (ambEll F i) ^ (-(𝔰 j : ℤ))) d := by
  induction r generalizing d with
  | zero => rw [nestLvl_zero, nestT_zero]
  | succ r ih =>
    rw [nestLvl_succ, nestT_succ, sum_range_eq_tsum_ite]
    refine tsum_congr fun i => ?_
    by_cases h : i < d
    · have hfun : (fun j : Fin r => 𝔰 ⟨j.1 + 1, by omega⟩) = (fun j : Fin r => 𝔰 j.succ) := by
        funext j
        exact congrArg 𝔰 (Fin.ext rfl)
      have h0 : (⟨0, Nat.succ_pos r⟩ : Fin (r+1)) = 0 := Fin.ext rfl
      rw [if_pos h, if_pos h, hfun, h0, ih (fun j : Fin r => 𝔰 j.succ) i]
    · rw [if_neg h, if_neg h, zero_mul]



/-! ## §2. Summability of the chain family from geometric decay -/

section Summable

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- **Summability of a product family over `Fin n → ℕ` from geometric decay of the factors.** -/
lemma summable_pi_of_geometric {n : ℕ} {Z : Fin n → ℕ → K} {ρ C : Γ₀}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hC : C ≠ 0)
    (harch : ∀ a : Γ₀, a < 1 → ∀ ε : Γ₀, ε ≠ 0 → ∃ m : ℕ, a ^ m < ε)
    (hZ : ∀ j d, Valued.v (Z j d) ≤ C * ρ ^ d) :
    Summable fun u : Fin n → ℕ => ∏ j, Z j (u j) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨γ, hγU⟩ := Valued.mem_nhds_zero.mp hU
  set δ : Γ₀ := MonoidWithZeroHom.ValueGroup₀.embedding
      (f := MonoidWithZeroHom.ofClass (Valued.v : Valuation K Γ₀)) (γ.1) with hδdef
  have hδ0 : δ ≠ 0 := by
    rw [hδdef]
    intro hh
    refine Units.ne_zero γ (MonoidWithZeroHom.ValueGroup₀.embedding_injective ?_)
    rw [hh, map_zero]
  have hfin : {u : Fin n → ℕ | δ ≤ Valued.v (∏ j, Z j (u j))}.Finite := by
    obtain ⟨N, hN⟩ := harch ρ hρ1 (δ / C ^ n) (div_ne_zero hδ0 (pow_ne_zero n hC))
    refine Set.Finite.subset (Set.Finite.pi (fun _ : Fin n => Set.finite_Iio N)) ?_
    intro u hu
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_Iio, true_implies] at hu ⊢
    have hle : Valued.v (∏ j, Z j (u j)) ≤ C ^ n * ρ ^ (∑ j, u j) := by
      rw [map_prod]
      calc ∏ j, Valued.v (Z j (u j)) ≤ ∏ j, (C * ρ ^ (u j)) :=
            Finset.prod_le_prod (fun j _ => zero_le) (fun j _ => hZ j (u j))
        _ = C ^ n * ρ ^ (∑ j, u j) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
              Finset.card_univ, Fintype.card_fin]
    have hCpos : (0 : Γ₀) < C ^ n := pow_pos (lt_of_le_of_ne zero_le (Ne.symm hC)) n
    have h1 : C ^ n * ρ ^ N < δ := by
      have h := mul_lt_mul_of_pos_left hN hCpos
      rwa [mul_div_cancel₀ δ (pow_ne_zero n hC)] at h
    have h2 : ρ ^ N < ρ ^ (∑ j, u j) :=
      lt_of_mul_lt_mul_left (lt_of_lt_of_le h1 (le_trans hu hle)) (le_of_lt hCpos)
    have h3 : ∑ j, u j < N := by
      by_contra hc
      exact absurd h2 (not_lt.mpr (pow_le_pow_of_le_one hρ0.le hρ1.le (not_lt.mp hc)))
    intro j
    calc u j ≤ ∑ i, u i := Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_univ j)
      _ < N := h3
  have hmem : ∀ᶠ u : Fin n → ℕ in Filter.cofinite,
      Valued.v.restrict (∏ j, Z j (u j)) < ↑γ := by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset hfin ?_
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu ⊢
    have hiff : Valued.v.restrict (∏ j, Z j (u j)) < ↑γ ↔
        Valued.v (∏ j, Z j (u j)) < δ := by
      rw [hδdef]; exact Valuation.restrict_lt_iff_lt_embedding _
    rw [hiff] at hu
    exact not_lt.mp hu
  exact Filter.mem_of_superset hmem (Set.preimage_mono hγU)

/-- **Summability of the strictly decreasing chain family** from geometric decay. -/
lemma summable_chain_of_geometric {n : ℕ} {Z : Fin n → ℕ → K} {ρ C : Γ₀}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hC : C ≠ 0)
    (harch : ∀ a : Γ₀, a < 1 → ∀ ε : Γ₀, ε ≠ 0 → ∃ m : ℕ, a ^ m < ε)
    (hZ : ∀ j d, Valued.v (Z j d) ≤ C * ρ ^ d) :
    Summable fun u : Fin n → ℕ => if StrictAnti u then ∏ j, Z j (u j) else 0 :=
  Commons.Topology.Algebra.Valued.summable_of_v_le_general
    (summable_pi_of_geometric hρ0 hρ1 hC harch hZ)
    (fun u => by by_cases h : StrictAnti u <;> simp [h])

end Summable

/-! ## §3. The decreasing-chain sum as a `tsum` over `Fin (n+1) → ℕ` -/


variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

lemma strictAnti_cons_iff {r : ℕ} (d : ℕ) (w : Fin r → ℕ) :
    StrictAnti (@Fin.cons r (fun _ : Fin (r+1) => ℕ) d w) ↔
      StrictAnti w ∧ ∀ j : Fin r, w j < d := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun j => ?_⟩
    · have h' := h (Fin.succ_lt_succ_iff.mpr hij)
      simpa using h'
    · have h' := h (show (0 : Fin (r+1)) < j.succ from by simp [Fin.lt_def])
      simpa using h'
  · rintro ⟨hw, hd⟩ i j hij
    rcases Fin.eq_zero_or_eq_succ i with hi | ⟨i', hi⟩
    · subst hi
      obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero (ne_of_gt hij)
      simp only [Fin.cons_zero, Fin.cons_succ]
      exact hd j'
    · subst hi
      obtain ⟨j', rfl⟩ := Fin.eq_succ_of_ne_zero (ne_of_gt (lt_trans (Fin.succ_pos i') hij))
      rw [Fin.succ_lt_succ_iff] at hij
      simpa using hw hij

/-- The forward map of `Fin.consEquiv` is `Fin.cons`. -/
lemma fin_consEquiv_eq {n : ℕ} (α : Fin (n+1) → Type*) (p : α 0 × ((i : Fin n) → α i.succ)) :
    Fin.consEquiv α p = Fin.cons p.1 p.2 := by
  funext i
  rw [Fin.consEquiv_apply, Fin.cons]

lemma strictAnti_fin_one (v : Fin 1 → ℕ) : StrictAnti v := by
  intro i j hij
  exfalso
  rw [Fin.lt_def] at hij
  have h1 := i.isLt
  have h2 := j.isLt
  omega

/-- Summability of the twice-bounded chain family. -/
lemma summable_chain_bounded {n : ℕ} {Z : Fin n → ℕ → K} {d : ℕ} {ρ C : Γ₀}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hC : C ≠ 0)
    (harch : ∀ a : Γ₀, a < 1 → ∀ ε : Γ₀, ε ≠ 0 → ∃ m : ℕ, a ^ m < ε)
    (hZ : ∀ j d, Valued.v (Z j d) ≤ C * ρ ^ d) :
    Summable fun u : Fin n → ℕ =>
      (if StrictAnti u ∧ ∀ j, u j < d then ∏ j, Z j (u j) else 0) :=
  Commons.Topology.Algebra.Valued.summable_of_v_le_general
    (summable_chain_of_geometric hρ0 hρ1 hC harch hZ)
    (fun u => by by_cases h : StrictAnti u ∧ ∀ j, u j < d <;> simp [h])

/-- The `Fin.cons`-family underlying the induction step of `nestT_succ_eq_tsum`. -/
noncomputable def nestConsFam {n : ℕ} (Y : Fin (n+2) → ℕ → K) (d : ℕ) :
    ℕ × (Fin (n+1) → ℕ) → K :=
  fun p => if StrictAnti (@Fin.cons (n+1) (fun _ : Fin (n+2) => ℕ) p.1 p.2)
        ∧ ∀ j : Fin (n+2),
          (@Fin.cons (n+1) (fun _ : Fin (n+2) => ℕ) p.1 p.2) j < d
      then ∏ j : Fin (n+2),
        Y j ((@Fin.cons (n+1) (fun _ : Fin (n+2) => ℕ) p.1 p.2) j) else 0

lemma nestConsFam_apply {n : ℕ} (Y : Fin (n+2) → ℕ → K) (d : ℕ)
    (p : ℕ × (Fin (n+1) → ℕ)) :
    nestConsFam Y d p = (if StrictAnti (@Fin.cons (n+1) (fun _ : Fin (n+2) => ℕ) p.1 p.2)
        ∧ ∀ j : Fin (n+2),
          (@Fin.cons (n+1) (fun _ : Fin (n+2) => ℕ) p.1 p.2) j < d
      then ∏ j : Fin (n+2),
        Y j ((@Fin.cons (n+1) (fun _ : Fin (n+2) => ℕ) p.1 p.2) j) else 0) := rfl

/-- **The decreasing-chain sum as a `tsum` over `Fin (n+1) → ℕ`.** -/
theorem nestT_succ_eq_tsum {n : ℕ} (Y : Fin (n+1) → ℕ → K) (d : ℕ)
    {ρ C : Γ₀} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hC : C ≠ 0)
    (harch : ∀ a : Γ₀, a < 1 → ∀ ε : Γ₀, ε ≠ 0 → ∃ m : ℕ, a ^ m < ε)
    (hY : ∀ j d, Valued.v (Y j d) ≤ C * ρ ^ d) :
    nestT (n+1) Y d = ∑' v : Fin (n+1) → ℕ,
      (if StrictAnti v ∧ ∀ j, v j < d then ∏ j, Y j (v j) else 0) := by
  induction n generalizing d with
  | zero =>
    rw [nestT_succ]
    simp only [nestT_zero, mul_one]
    rw [← Equiv.tsum_eq (Equiv.funUnique (Fin 1) ℕ).symm (fun v : Fin 1 → ℕ =>
      if StrictAnti v ∧ ∀ j, v j < d then ∏ j, Y j (v j) else 0)]
    refine tsum_congr fun i => ?_
    rw [Fin.prod_univ_one]
    by_cases h : i < d
    · rw [if_pos h, if_pos (by
        refine ⟨strictAnti_fin_one _, ?_⟩
        intro j
        simpa using h)]
      simp
    · rw [if_neg h, if_neg (fun hh => h (by simpa using hh.2 0))]
  | succ n ih =>
    rw [nestT_succ]
    have hG : Summable (fun v : Fin (n+2) → ℕ =>
        if StrictAnti v ∧ ∀ j, v j < d then ∏ j, Y j (v j) else 0) :=
      summable_chain_bounded hρ0 hρ1 hC harch hY
    have hsum : Summable (fun c : ℕ × (Fin (n+1) → ℕ) =>
        (fun v : Fin (n+2) → ℕ =>
          if StrictAnti v ∧ ∀ j, v j < d then ∏ j, Y j (v j) else 0)
          ((Fin.consEquiv (fun _ : Fin (n+2) => ℕ)) c)) :=
      ((Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (n+2) => ℕ))).mpr hG).congr
        (fun c => rfl)
    rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ : Fin (n+2) => ℕ))
        (fun v : Fin (n+2) → ℕ =>
          if StrictAnti v ∧ ∀ j, v j < d then ∏ j, Y j (v j) else 0),
      Summable.tsum_prod hsum]
    refine tsum_congr fun i => ?_
    rw [ih (Y := fun j : Fin (n+1) => Y j.succ) (d := i) (fun j d => hY j.succ d), ← tsum_mul_left]
    refine tsum_congr fun w => ?_
    rw [fin_consEquiv_eq]
    dsimp only
    have hcond : (StrictAnti (@Fin.cons (n+1) (fun _ : Fin (n+2) => ℕ) i w)
        ∧ ∀ j : Fin (n+2), (@Fin.cons (n+1) (fun _ : Fin (n+2) => ℕ) i w) j < d)
        ↔ (i < d ∧ StrictAnti w ∧ ∀ j : Fin (n+1), w j < i) := by
      rw [strictAnti_cons_iff]
      constructor
      · rintro ⟨⟨hw, hwi⟩, hd⟩
        exact ⟨by simpa using hd 0, hw, hwi⟩
      · rintro ⟨h1, hw, hwi⟩
        refine ⟨⟨hw, hwi⟩, ?_⟩
        intro j
        rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', hj⟩
        · subst hj; simpa using h1
        · subst hj; exact lt_trans (hwi j') h1
    have hprod : (∏ j : Fin (n+2), Y j ((@Fin.cons (n+1) (fun _ : Fin (n+2) => ℕ) i w) j))
        = Y 0 i * ∏ j : Fin (n+1), Y j.succ (w j) := by
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    simp only [hprod, hcond]
    by_cases h1 : i < d <;> by_cases h2 : StrictAnti w ∧ ∀ j, w j < i <;> simp [h1, h2]



/-! ## §4. The growth of `ℓ_d` and the geometric decay of its powers -/

section AmbEllDecay

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

lemma v_ambTheta_sub_pow (i : ℕ) :
    Valued.v ((ambTheta F) - (ambTheta F) ^ (Nat.card F ^ (i + 1)))
      = WithZero.exp (((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (i + 1)) := by
  have hq : (2 : ℚ) ≤ (Nat.card F : ℚ) := by exact_mod_cast (two_le_card_field F)
  have hq1 : (0 : ℚ) < (Nat.card F : ℚ) - 1 := by linarith
  have hpow1 : (1 : ℚ) < (Nat.card F : ℚ) ^ (i + 1) := one_lt_pow₀ (by linarith) (by omega)
  have hexp : (Nat.card F ^ (i + 1)) • ((Nat.card F : ℚ) - 1)
      = ((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (i + 1) := by
    rw [nsmul_eq_mul, Nat.cast_pow]
    ring
  have hlt : Valued.v (ambTheta F) < Valued.v ((ambTheta F) ^ (Nat.card F ^ (i + 1))) := by
    rw [v_ambTheta, map_pow, v_ambTheta, ← WithZero.exp_nsmul, WithZero.exp_lt_exp]
    rw [hexp]
    simpa using mul_lt_mul_of_pos_left hpow1 hq1
  rw [Valuation.map_sub_eq_of_lt_right (v := (Valued.v : Valuation (Ambient F) ℚᵐ⁰))
    (x := ambTheta F) (y := (ambTheta F) ^ (Nat.card F ^ (i + 1))) hlt, map_pow, v_ambTheta,
    ← WithZero.exp_nsmul, hexp]

lemma v_ambEll_lower (d : ℕ) :
    WithZero.exp ((Nat.card F : ℚ) * d) ≤ Valued.v (ambEll F d) := by
  have hq : (2 : ℚ) ≤ (Nat.card F : ℚ) := by exact_mod_cast (two_le_card_field F)
  have hq1 : (1 : ℚ) ≤ (Nat.card F : ℚ) := by linarith
  have hqm1 : (0 : ℚ) ≤ (Nat.card F : ℚ) - 1 := by linarith
  have hgeom : ∀ i ∈ Finset.range d,
      (Nat.card F : ℚ) ≤ ((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (i + 1) := by
    intro i _
    have hpow : (Nat.card F : ℚ) ≤ (Nat.card F : ℚ) ^ (i + 1) := le_self_pow₀ hq1 (by omega)
    calc (Nat.card F : ℚ) = 1 * (Nat.card F : ℚ) := by ring
      _ ≤ ((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ ((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (i + 1) :=
          mul_le_mul_of_nonneg_left hpow hqm1
  rw [ambEll_eq_prod, map_prod]
  calc (∏ i ∈ Finset.range d, Valued.v ((ambTheta F) - (ambTheta F) ^ (Nat.card F ^ (i + 1))))
      = ∏ i ∈ Finset.range d,
          WithZero.exp (((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (i + 1)) :=
        Finset.prod_congr rfl (fun i _ => v_ambTheta_sub_pow F i)
    _ = WithZero.exp
          (∑ i ∈ Finset.range d, ((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (i + 1)) :=
        withZero_exp_finset_sum _ _
    _ ≥ WithZero.exp ((Nat.card F : ℚ) * d) := by
        refine WithZero.exp_le_exp.mpr ?_
        calc (Nat.card F : ℚ) * d = ∑ _i ∈ Finset.range d, (Nat.card F : ℚ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
            _ ≤ ∑ i ∈ Finset.range d,
                  ((Nat.card F : ℚ) - 1) * (Nat.card F : ℚ) ^ (i + 1) :=
                Finset.sum_le_sum hgeom

/-- **The geometric decay of the `ℓ_d`-powers**: `v (ℓ_d^{-s}) ≤ exp(-q·d)` for `s ≥ 1`. -/
lemma v_ambEll_zpow_le (i s : ℕ) (hs : 1 ≤ s) :
    Valued.v ((ambEll F i) ^ (-(s : ℤ))) ≤ (WithZero.exp (-(Nat.card F : ℚ))) ^ i := by
  have hq : (2 : ℚ) ≤ (Nat.card F : ℚ) := by exact_mod_cast (two_le_card_field F)
  have hpos : (0 : ℚᵐ⁰) < Valued.v (ambEll F i) :=
    (WithZero.exp_pos (a := (Nat.card F : ℚ) * i)).trans_le (v_ambEll_lower F i)
  have hz : Valued.v ((ambEll F i) ^ (-(s : ℤ))) = ((Valued.v (ambEll F i))⁻¹) ^ s := by
    have h1 : (ambEll F i) ^ (-(s : ℤ)) = ((ambEll F i)⁻¹) ^ s := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [h1]
    simp only [Valuation.map_pow, Valuation.map_inv]
  have hb : (0 : ℚᵐ⁰) < WithZero.exp ((Nat.card F : ℚ) * i) := WithZero.exp_pos
  have h1 : (Valued.v (ambEll F i))⁻¹ ≤ (WithZero.exp ((Nat.card F : ℚ) * i))⁻¹ :=
    (inv_le_inv₀ hpos hb).mpr (v_ambEll_lower F i)
  rw [hz]
  calc ((Valued.v (ambEll F i))⁻¹) ^ s
      ≤ ((WithZero.exp ((Nat.card F : ℚ) * i))⁻¹) ^ s :=
        pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) h1 s
    _ = (WithZero.exp ((Nat.card F : ℚ) * i)) ^ (-(s : ℤ)) := by
        rw [zpow_neg, zpow_natCast, inv_pow]
    _ = WithZero.exp (((-(s : ℤ)) • ((Nat.card F : ℚ) * i))) := by
        rw [← WithZero.exp_zsmul]
    _ ≤ WithZero.exp (-((Nat.card F : ℚ) * i)) := by
        refine WithZero.exp_le_exp.mpr ?_
        simp only [zsmul_eq_mul]
        push_cast
        have hsi : (1 : ℚ) ≤ s := by exact_mod_cast hs
        have hqi : (0 : ℚ) ≤ (Nat.card F : ℚ) * i := by positivity
        have hsnn : (0 : ℚ) ≤ (s : ℚ) := by positivity
        nlinarith [hsi, hqi, hsnn]
    _ = (WithZero.exp (-(Nat.card F : ℚ))) ^ i := by
        rw [← WithZero.exp_nsmul, nsmul_eq_mul]
        congr 1
        ring

end AmbEllDecay


/-! ## §5. The `Fin.cons` splitting of the decreasing chain sum -/

section ChainCons

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- **The `Fin.cons` splitting of the decreasing chain sum**: the outer factor `Z 0` separates. -/
lemma tsum_cons_chain {n : ℕ} (Z : Fin (n+2) → ℕ → K) {ρ C : Γ₀}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hC : C ≠ 0)
    (harch : ∀ a : Γ₀, a < 1 → ∀ ε : Γ₀, ε ≠ 0 → ∃ m : ℕ, a ^ m < ε)
    (hZ : ∀ j d, Valued.v (Z j d) ≤ C * ρ ^ d) :
    (∑' d : ℕ, Z 0 d * (∑' v : Fin (n+1) → ℕ,
        (if StrictAnti v ∧ ∀ j, v j < d then ∏ j, Z j.succ (v j) else 0)))
      = ∑' u : Fin (n+2) → ℕ,
          (if StrictAnti u then ∏ j, Z j (u j) else 0) := by
  have hG2 : Summable (fun u : Fin (n+2) → ℕ =>
      if StrictAnti u then ∏ j, Z j (u j) else 0) :=
    summable_chain_of_geometric hρ0 hρ1 hC harch hZ
  have key : ∀ p : ℕ × (Fin (n+1) → ℕ),
      (if StrictAnti p.2 ∧ ∀ j, p.2 j < p.1 then Z 0 p.1 * ∏ j, Z j.succ (p.2 j) else 0)
        = (fun u : Fin (n+2) → ℕ => if StrictAnti u then ∏ j, Z j (u j) else 0)
            ((Fin.consEquiv (fun _ : Fin (n+2) => ℕ)) p) := by
    intro p
    rw [fin_consEquiv_eq]
    dsimp only
    simp only [strictAnti_cons_iff, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have hGsum : Summable (fun p : ℕ × (Fin (n+1) → ℕ) =>
      (if StrictAnti p.2 ∧ ∀ j, p.2 j < p.1 then Z 0 p.1 * ∏ j, Z j.succ (p.2 j) else 0)) :=
    Summable.congr ((Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (n+2) => ℕ))).mpr hG2)
      (fun p => (key p).symm)
  calc (∑' d : ℕ, Z 0 d * (∑' v : Fin (n+1) → ℕ,
          (if StrictAnti v ∧ ∀ j, v j < d then ∏ j, Z j.succ (v j) else 0)))
      = ∑' d : ℕ, ∑' v : Fin (n+1) → ℕ,
          (if StrictAnti v ∧ ∀ j, v j < d then Z 0 d * ∏ j, Z j.succ (v j) else 0) := by
        refine tsum_congr fun d => ?_
        rw [← tsum_mul_left]
        refine tsum_congr fun v => ?_
        by_cases h : StrictAnti v ∧ ∀ j, v j < d
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, mul_zero]
    _ = ∑' p : ℕ × (Fin (n+1) → ℕ),
          (if StrictAnti p.2 ∧ ∀ j, p.2 j < p.1 then Z 0 p.1 * ∏ j, Z j.succ (p.2 j) else 0) :=
        (Summable.tsum_prod hGsum).symm
    _ = ∑' p : ℕ × (Fin (n+1) → ℕ),
          (fun u : Fin (n+2) → ℕ => if StrictAnti u then ∏ j, Z j (u j) else 0)
            ((Fin.consEquiv (fun _ : Fin (n+2) => ℕ)) p) := tsum_congr key
    _ = ∑' u : Fin (n+2) → ℕ, (if StrictAnti u then ∏ j, Z j (u j) else 0) :=
        Equiv.tsum_eq (Fin.consEquiv (fun _ : Fin (n+2) => ℕ))
          (fun u : Fin (n+2) → ℕ => if StrictAnti u then ∏ j, Z j (u j) else 0)

end ChainCons


/-! ## §6. The ζ-side as a chain sum -/

section ZetaChain

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The small parameter of the chain sums. -/
noncomputable def ambRho : ℚᵐ⁰ := WithZero.exp (-(Nat.card F : ℚ))

lemma ambRho_pos : 0 < ambRho F := WithZero.exp_pos

lemma ambRho_lt_one : ambRho F < 1 := by
  rw [ambRho, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  have : (2 : ℚ) ≤ (Nat.card F : ℚ) := by exact_mod_cast (two_le_card_field F)
  linarith

lemma v_ambEll_zpow_le_ambRho (j : ℕ) (s : ℕ+) :
    Valued.v ((ambEll F j) ^ (-(s : ℕ) : ℤ)) ≤ (1 : ℚᵐ⁰) * ambRho F ^ j := by
  rw [one_mul, ambRho]
  exact v_ambEll_zpow_le F j (s : ℕ) s.2

/-- **The ζ_A-value of a tuple with entries `≤ q` as a strictly decreasing chain sum.** -/
theorem ambInfHom_zeta_A_eq_chain (r : ℕ) (𝔰 : Fin (r+1) → ℕ+)
    (h𝔰 : ∀ i, (𝔰 i : ℕ) ≤ Nat.card F) :
    ambInfHom F (ζ_A F 𝔰)
      = ∑' u : Fin (r+1) → ℕ,
          (if StrictAnti u then ∏ j, (ambEll F (u j)) ^ (-(𝔰 j : ℤ)) else 0) := by
  have harch : ∀ a : ℚᵐ⁰, a < 1 → ∀ ε : ℚᵐ⁰, ε ≠ 0 → ∃ m : ℕ, a ^ m < ε :=
    gammaArchimedean_rat
  rcases r with _ | r'
  · rw [ambInfHom_zeta_A_eq_nestLvl F 0 𝔰 h𝔰]
    simp only [nestLvl_zero, mul_one]
    rw [← Equiv.tsum_eq (Equiv.funUnique (Fin 1) ℕ).symm (fun u : Fin 1 → ℕ =>
        if StrictAnti u then ∏ j, (ambEll F (u j)) ^ (-(𝔰 j : ℤ)) else 0)]
    refine tsum_congr fun d => ?_
    rw [Fin.prod_univ_one, if_pos (strictAnti_fin_one _)]
    simp
  · rw [ambInfHom_zeta_A_eq_nestLvl F (r'+1) 𝔰 h𝔰]
    have htail : (fun j : Fin (r'+1) => 𝔰 ⟨j.1 + 1, by omega⟩)
        = (fun j : Fin (r'+1) => 𝔰 j.succ) := by
      funext j
      exact congrArg 𝔰 (Fin.ext rfl)
    have hconv : (∑' d : ℕ, (ambEll F d) ^ (-(𝔰 0 : ℤ))
          * nestLvl F (r'+1) (fun j : Fin (r'+1) => 𝔰 ⟨j.1 + 1, by omega⟩) d)
        = ∑' d : ℕ, (ambEll F d) ^ (-(𝔰 0 : ℤ))
          * nestLvl F (r'+1) (fun j : Fin (r'+1) => 𝔰 j.succ) d :=
      tsum_congr (fun d => by
        rw [congrArg (fun h : Fin (r'+1) → ℕ+ => nestLvl F (r'+1) h d) htail])
    rw [hconv]
    have hconv2 : (∑' d : ℕ, (ambEll F d) ^ (-(𝔰 0 : ℤ))
          * nestLvl F (r'+1) (fun j : Fin (r'+1) => 𝔰 j.succ) d)
        = ∑' d : ℕ, (ambEll F d) ^ (-(𝔰 0 : ℤ))
          * nestT (r'+1) (fun j : Fin (r'+1) => fun i =>
              (ambEll F i) ^ (-(𝔰 j.succ : ℤ))) d :=
      tsum_congr (fun d => by
        rw [nestLvl_eq_nestT F (r'+1) (fun j : Fin (r'+1) => 𝔰 j.succ) d])
    rw [hconv2]
    have hconv3 : (∑' d : ℕ, (ambEll F d) ^ (-(𝔰 0 : ℤ))
          * nestT (r'+1) (fun j : Fin (r'+1) => fun i =>
              (ambEll F i) ^ (-(𝔰 j.succ : ℤ))) d)
        = ∑' d : ℕ, (ambEll F d) ^ (-(𝔰 0 : ℤ))
          * (∑' v : Fin (r'+1) → ℕ, (if StrictAnti v ∧ ∀ j, v j < d
              then ∏ j, (ambEll F (v j)) ^ (-(𝔰 j.succ : ℤ)) else 0)) :=
      tsum_congr (fun d => by
        rw [nestT_succ_eq_tsum
          (Y := fun j : Fin (r'+1) => fun i => (ambEll F i) ^ (-(𝔰 j.succ : ℤ))) d
          (ambRho_pos F) (ambRho_lt_one F) one_ne_zero harch
          (fun j i => v_ambEll_zpow_le_ambRho F i (𝔰 j.succ))])
    rw [hconv3]
    exact tsum_cons_chain (fun j i => (ambEll F i) ^ (-(𝔰 j : ℤ)))
      (ambRho_pos F) (ambRho_lt_one F) one_ne_zero harch
      (fun j i => v_ambEll_zpow_le_ambRho F i (𝔰 j))

end ZetaChain


/-! ## §7. The reindexing `Fin.rev`: increasing chains ↔ decreasing chains -/

section Reindex

variable {K : Type*} [CommSemiring K] [TopologicalSpace K]

lemma fin_rev_lt_rev_iff {n : ℕ} {i j : Fin n} : Fin.rev i < Fin.rev j ↔ j < i := by
  rw [Fin.lt_def, Fin.lt_def]
  simp only [Fin.val_rev]
  constructor <;> intro h <;> omega

lemma strictMono_comp_rev_iff {n : ℕ} {u : Fin n → ℕ} :
    StrictMono (fun j => u (Fin.rev j)) ↔ StrictAnti u := by
  constructor
  · intro h i j hij
    have h' := h (fin_rev_lt_rev_iff.mpr hij)
    simpa [Fin.rev_rev] using h'
  · intro h i j hij
    exact h (fin_rev_lt_rev_iff.mpr hij)

/-- **Reindexing by `Fin.rev`**: a strictly increasing chain sum is a strictly decreasing chain sum
with the labels reversed. -/
lemma tsum_mono_eq_anti {n : ℕ} (Y : Fin n → ℕ → K) :
    (∑' v : Fin n → ℕ, (if StrictMono v then ∏ j, Y j (v j) else 0))
      = ∑' u : Fin n → ℕ, (if StrictAnti u then ∏ j, Y (Fin.rev j) (u j) else 0) := by
  rw [← Equiv.tsum_eq (Equiv.arrowCongr (Fin.revPerm : Equiv.Perm (Fin n)) (Equiv.refl ℕ))
      (fun v : Fin n → ℕ => if StrictMono v then ∏ j, Y j (v j) else 0)]
  refine tsum_congr fun u => ?_
  have hcomp : (Equiv.arrowCongr (Fin.revPerm : Equiv.Perm (Fin n)) (Equiv.refl ℕ)) u
      = fun j => u (Fin.rev j) := by
    funext j
    rw [Equiv.arrowCongr_apply]
    simp [Fin.revPerm_symm]
  rw [hcomp]
  simp only [strictMono_comp_rev_iff]
  by_cases h : StrictAnti u
  · rw [if_pos h, if_pos h]
    simpa [Fin.rev_rev] using (Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin n))
      (fun j => Y j (u (Fin.rev j)))).symm
  · rw [if_neg h, if_neg h]

end Reindex


/-! ## §8. The L-side: the value of the `L`-series as an increasing chain sum -/

section LSide

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- Summability of the increasing chain family (geometric decay). -/
lemma summable_chain_mono_of_geometric {m : ℕ} {Z : Fin (m+1) → ℕ → K} {ρ C : Γ₀}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hC : C ≠ 0)
    (harch : ∀ a : Γ₀, a < 1 → ∀ ε : Γ₀, ε ≠ 0 → ∃ m : ℕ, a ^ m < ε)
    (hZ : ∀ j d, Valued.v (Z j d) ≤ C * ρ ^ d) (N : ℕ) :
    Summable fun v : Fin (m+1) → ℕ =>
      (if N ≤ v 0 ∧ StrictMono v then ∏ j, Z j (v j) else 0) := by
  refine Commons.Topology.Algebra.Valued.summable_of_v_le_general
    (f := fun v : Fin (m+1) → ℕ =>
      if N ≤ v 0 ∧ StrictMono v then ∏ j, Z j (v j) else 0)
    (g := fun v : Fin (m+1) → ℕ => if StrictMono v then ∏ j, Z j (v j) else 0) ?_ ?_
  · refine Commons.Topology.Algebra.Valued.summable_of_v_le_general
      (summable_pi_of_geometric hρ0 hρ1 hC harch hZ) (fun v => ?_)
    by_cases h : StrictMono v <;> simp [h]
  · intro v
    by_cases h : N ≤ v 0 ∧ StrictMono v
    · rw [if_pos h, if_pos h.2]
    · rw [if_neg h]
      by_cases h2 : StrictMono v <;> simp [h2]

end LSide

section LSideAmb

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The arithmetic fact `γ^q · v θ < 1` that replaces the (false) hypothesis `v θ < 1`. -/
lemma ambGamma_pow_card_mul_v_ambTheta_lt_one :
    ambGamma ^ (Nat.card F) * Valued.v (ambTheta F) < 1 := by
  rw [ambGamma, v_ambTheta, ← WithZero.exp_nsmul, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_lt_exp, nsmul_eq_mul]
  linarith

/-- **The `L`-series value as a strictly increasing chain sum** (the ambient case). -/
theorem evalSeriesGen_atLrGen_chain (Lst : List (ℕ × PowerSeries (Ambient F)))
    (hne : Lst ≠ [])
    (hL : ∀ x ∈ Lst, GIsSmall ambGamma ((ambOmega F) ^ x.1 * x.2))
    (hLse : ∀ x ∈ Lst, GSuperEntire ambGamma x.2)
    {ρ : ℚᵐ⁰} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hY : ∀ j : Fin Lst.length, ∀ d : ℕ,
      Valued.v (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
        ((ambOmega F) ^ (Lst.get j).1 * (Lst.get j).2)) (ambTheta F)) ≤ 1 * ρ ^ d) :
    evalSeriesGen (atLrGen (Nat.card F) (ambOmega F) Lst) (ambTheta F)
      = ∑' v : Fin Lst.length → ℕ,
          (if StrictMono v then ∏ j, evalSeriesGen
              (frobTwist (R := Ambient F) (p := Nat.card F) (v j)
                ((ambOmega F) ^ (Lst.get j).1 * (Lst.get j).2)) (ambTheta F) else 0) := by
  rcases Lst with _ | ⟨a, rest⟩
  · exact absurd rfl hne
  · rw [show atLrGen (Nat.card F) (ambOmega F) (a :: rest)
        = atLrcutGen (Nat.card F) (ambOmega F) (a :: rest) 0 from rfl]
    rw [evalSeriesGen_atLrcutGen (γ := ambGamma) (K := Ambient F) ambGamma_lt_one
      (ne_of_gt ambGamma_pos) gammaArchimedean_rat (two_le_ambCard F)
      (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F) hL hLse
      (M := Nat.card F) (le_trans (by norm_num : 1 ≤ 2) (two_le_card_field F))
      (ambGamma_pow_card_mul_v_ambTheta_lt_one F) 0]
    rw [evalIter_eq_evalIterB, evalIterB_eq_incU]
    have hG : Summable (fun v : Fin (rest.length + 1) → ℕ =>
        (if 0 ≤ v 0 ∧ StrictMono v then ∏ j, evalSeriesGen
            (frobTwist (R := Ambient F) (p := Nat.card F) (v j)
              ((ambOmega F) ^ ((a :: rest).get j).1 * ((a :: rest).get j).2))
            (ambTheta F) else 0)) :=
      summable_chain_mono_of_geometric (K := Ambient F) (Γ₀ := ℚᵐ⁰) hρ0 hρ1 one_ne_zero
        gammaArchimedean_rat hY 0
    have hinc0 := incU_succ_eq_tsum (r := rest.length) (N := 0)
        (Y := fun j : Fin (rest.length + 1) => fun d : ℕ => evalSeriesGen
          (frobTwist (R := Ambient F) (p := Nat.card F) d
            ((ambOmega F) ^ ((a :: rest).get j).1 * ((a :: rest).get j).2))
          (ambTheta F)) hG
    have hrhs : (∑' v : Fin (rest.length + 1) → ℕ,
          (if 0 ≤ v 0 ∧ StrictMono v then ∏ j, evalSeriesGen
            (frobTwist (R := Ambient F) (p := Nat.card F) (v j)
              ((ambOmega F) ^ ((a :: rest).get j).1 * ((a :: rest).get j).2))
            (ambTheta F) else 0))
        = ∑' v : Fin (rest.length + 1) → ℕ,
            (if StrictMono v then ∏ j, evalSeriesGen
              (frobTwist (R := Ambient F) (p := Nat.card F) (v j)
                ((ambOmega F) ^ ((a :: rest).get j).1 * ((a :: rest).get j).2))
              (ambTheta F) else 0) := by
      refine tsum_congr fun v => ?_
      by_cases h : StrictMono v
      · rw [if_pos ⟨zero_le, h⟩, if_pos h]
      · rw [if_neg (fun hh => h hh.2), if_neg h]
    exact hinc0.trans hrhs

end LSideAmb


/-! ## §9. THE BRIDGE: `𝓛(𝔰;1)(θ) = π̃^{-w}·ζ_A(𝔰)` -/

section Bridge

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

theorem ambPiTilde_mul_eval :
    (ambPiTilde F) * evalSeriesGen (ambOmega F) (ambTheta F) = 1 := by
  rw [ambPiTilde, inv_mul_cancel₀ (evalSeriesGen_ambOmega_ne_zero F)]

theorem evalSeriesGen_ambOmega_zpow (m : ℕ) :
    (evalSeriesGen (ambOmega F) (ambTheta F)) ^ m = ((ambPiTilde F) ^ m)⁻¹ := by
  rw [ambPiTilde, inv_pow, inv_inv]

/-- **★★★ THE BRIDGE (Dac (4.2) / AT09 (2.4.1), trivial character)**: the value of the
`L`-series of a tuple of positive integers with unit `Q`'s is `π̃^{-w}` times the value of
`ζ_A` on the reversed tuple. -/
theorem bridge (M : List (ℕ × PowerSeries (Ambient F)))
    (hne : M ≠ [])
    (hQ : ∀ j : Fin M.length, (M.get j).2 = 1)
    (hpos : ∀ j : Fin M.length, 1 ≤ (M.get j).1)
    (𝔰 : Fin M.length → ℕ+)
    (h𝔰 : ∀ j : Fin M.length, (𝔰 j : ℕ) = (M.get (Fin.rev j)).1)
    (h𝔰q : ∀ j : Fin M.length, (𝔰 j : ℕ) ≤ Nat.card F) :
    (ambPiTilde F) ^ (∑ j, (𝔰 j : ℕ))
        * evalSeriesGen (atLrGen (Nat.card F) (ambOmega F) M) (ambTheta F)
      = ambInfHom F (ζ_A F 𝔰) := by
  rcases M with _ | ⟨a, rest⟩
  · exact absurd rfl hne
  · have hQmem : ∀ x ∈ (a :: rest), x.2 = 1 := by
      intro x hx
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx
      rw [← hj]
      exact hQ j
    have hposmem : ∀ x ∈ (a :: rest), 1 ≤ x.1 := by
      intro x hx
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx
      rw [← hj]
      exact hpos j
    have hL : ∀ x ∈ (a :: rest), GIsSmall ambGamma ((ambOmega F) ^ x.1 * x.2) := by
      intro x hx
      rw [hQmem x hx, mul_one, ← Nat.sub_add_cancel (hposmem x hx)]
      exact GIsSmall.pow_add_one ambGamma_le_one (gIsSmall_ambOmega F) (x.1 - 1)
    have hLse : ∀ x ∈ (a :: rest), GSuperEntire ambGamma x.2 := by
      intro x hx
      rw [hQmem x hx]
      exact GSuperEntire.one ambGamma
    have hYid : ∀ j : Fin ((a :: rest).length), ∀ d : ℕ,
        evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
          ((ambOmega F) ^ ((a :: rest).get j).1 * ((a :: rest).get j).2)) (ambTheta F)
        = (evalSeriesGen (ambOmega F) (ambTheta F)) ^ ((a :: rest).get j).1
          * (ambEll F d) ^ (-(((a :: rest).get j).1 : ℤ)) := by
      intro j d
      rw [hQ j, mul_one, frobTwist_pow,
        evalSeriesGen_pow ambGamma_lt_one gammaArchimedean_rat
          (GSuperEntire.frobTwist (f := ambOmega F) ambGamma_le_one
            (gSuperEntire_ambOmega F) d),
        ambOmega_twist_eval F d (by rw [← ambEll_eq_prod]; exact ambEll_ne_zero F d), ambEll_eq_prod,
        zpow_neg, zpow_natCast, div_eq_mul_inv, mul_pow, inv_pow]
    have hYdecay : ∀ j : Fin ((a :: rest).length), ∀ d : ℕ,
        Valued.v (evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) d
          ((ambOmega F) ^ ((a :: rest).get j).1 * ((a :: rest).get j).2)) (ambTheta F))
          ≤ 1 * ambRho F ^ d := by
      intro j d
      rw [hYid j d, map_mul, map_pow, v_evalSeriesGen_ambOmega]
      calc ambRho F ^ ((a :: rest).get j).1
              * Valued.v ((ambEll F d) ^ (-(((a :: rest).get j).1 : ℤ)))
          ≤ ambRho F ^ ((a :: rest).get j).1 * ambRho F ^ d :=
            mul_le_mul_of_nonneg_left
              (v_ambEll_zpow_le F d ((a :: rest).get j).1 (hpos j)) zero_le
        _ = ambRho F ^ (((a :: rest).get j).1 + d) := by rw [← pow_add]
        _ ≤ ambRho F ^ d :=
            pow_le_pow_of_le_one zero_le (ambRho_lt_one F).le (Nat.le_add_left d _)
        _ = 1 * ambRho F ^ d := (one_mul _).symm
    rw [evalSeriesGen_atLrGen_chain F (a :: rest) hne hL hLse
      (ambRho_pos F) (ambRho_lt_one F) hYdecay]
    rw [← tsum_mul_left]
    have hpt : ∀ v : Fin ((a :: rest).length) → ℕ,
        ambPiTilde F ^ (∑ j : Fin ((a :: rest).length), (𝔰 j : ℕ))
            * (if StrictMono v then ∏ j : Fin ((a :: rest).length), evalSeriesGen
                (frobTwist (R := Ambient F) (p := Nat.card F) (v j)
                  ((ambOmega F) ^ ((a :: rest).get j).1 * ((a :: rest).get j).2))
                (ambTheta F) else 0)
          = (if StrictMono v then ∏ j : Fin ((a :: rest).length),
                (ambEll F (v j)) ^ (-(((a :: rest).get j).1 : ℤ)) else 0) := by
      intro v
      by_cases hv : StrictMono v
      · rw [if_pos hv, if_pos hv]
        have hprod : (∏ j : Fin ((a :: rest).length), evalSeriesGen
              (frobTwist (R := Ambient F) (p := Nat.card F) (v j)
                ((ambOmega F) ^ ((a :: rest).get j).1 * ((a :: rest).get j).2))
              (ambTheta F))
            = (evalSeriesGen (ambOmega F) (ambTheta F)) ^ (∑ j : Fin ((a :: rest).length),
                ((a :: rest).get j).1)
              * ∏ j : Fin ((a :: rest).length),
                  (ambEll F (v j)) ^ (-(((a :: rest).get j).1 : ℤ)) := by
          rw [Finset.prod_congr rfl (fun j _ => hYid j (v j)),
            Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        rw [hprod]
        have hw : (∑ j : Fin ((a :: rest).length), (𝔰 j : ℕ))
            = ∑ j : Fin ((a :: rest).length), ((a :: rest).get j).1 := by
          have h1 : (∑ j : Fin ((a :: rest).length), (𝔰 j : ℕ))
              = ∑ j : Fin ((a :: rest).length), ((a :: rest).get (Fin.rev j)).1 :=
            Finset.sum_congr rfl (fun j _ => h𝔰 j)
          rw [h1]
          exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin ((a :: rest).length)))
            (fun j => ((a :: rest).get j).1)
        rw [hw, ← mul_assoc, ← mul_pow, ambPiTilde_mul_eval, one_pow, one_mul]
      · rw [if_neg hv, if_neg hv, mul_zero]
    rw [tsum_congr hpt]
    rw [tsum_mono_eq_anti (K := Ambient F) (n := (a :: rest).length)
      (Y := fun j d => (ambEll F d) ^ (-(((a :: rest).get j).1 : ℤ)))]
    have hconv : (∑' u : Fin ((a :: rest).length) → ℕ,
        (if StrictAnti u then ∏ j, (ambEll F (u j))
          ^ (-(((a :: rest).get (Fin.rev j)).1 : ℤ)) else 0))
        = ∑' u : Fin ((a :: rest).length) → ℕ,
        (if StrictAnti u then ∏ j, (ambEll F (u j)) ^ (-(𝔰 j : ℤ)) else 0) := by
      refine tsum_congr fun u => ?_
      by_cases h : StrictAnti u
      · rw [if_pos h, if_pos h]
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [← h𝔰 j]
      · rw [if_neg h, if_neg h]
    rw [hconv]
    exact (ambInfHom_zeta_A_eq_chain F rest.length 𝔰 h𝔰q).symm

end Bridge


/-! ## §10. The `tmF`-splitting (the first half of Step 3) -/

section TmFSplit

variable {K : Type*} [Field K] [DecidableEq K] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- **The `tmF`-splitting**: if `t` is a prefix of `s₀ ∈ S` and `s₀` is the ONLY element of `S`
having `t` as a prefix of length `t.length`, then `tmF` collapses to the single summand at `s₀`.
This is the algebraic content of Dac §5.3's Step 3: for `t = pref_k(𝔰_i)` with `k` larger than
every common-prefix length with the other tuples, `tmF … t = (cf 𝔰_i)·𝓛(𝔰_i.drop k)`. -/
lemma tmF_eq_single {q : ℕ} [FrobPow K q] {ω : PowerSeries K} {w : ℕ}
    {S : Finset (List (ℕ × Polynomial K))} {cf : List (ℕ × Polynomial K) → Polynomial K}
    {t s₀ : List (ℕ × Polynomial K)} (hs₀ : s₀ ∈ S) (ht : s₀.take t.length = t)
    (hun : ∀ s ∈ S, s.take t.length = t → s = s₀) :
    tmF q ω w S cf t = (cf s₀ : PowerSeries K) * tmL q ω (s₀.drop t.length) := by
  rw [tmF]
  rw [Finset.sum_eq_single s₀]
  · rw [if_pos ht]
  · intro s hs hne
    rw [if_neg]
    intro htake
    exact hne (hun s hs htake)
  · intro hnot
    exact absurd hs₀ hnot

end TmFSplit


/-! ## §11. Step 3 (I): the vanishing of the weight-`w` relation on the `L`-series side -/

section FEmpty

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The `K`-element `ambKHomAmb c` is the coefficient in the `Ambient`-wrapped relation. -/
lemma ambKHomAmb_eq (x : RatFunc F) :
    ambKHomAmb F x = ((ambKEquiv F x : ↥(ambK F)) : Ambient F) := rfl

/-- ★★ **Step 3 (I)**: a `K`-linear relation `∑_i c_i·ζ_A(𝔰_i) = 0` between MZV's of a COMMON
weight `w` (all entries `≤ q`) transports, via the bridge, to the vanishing of the corresponding
`L`-series relation `∑_i c_i(θ)·𝓛(𝔰_i)(θ) = 0`.  This is the input `f_∅(θ) = 0` of
`LinearIndependence.linear_independence`. -/
theorem f_empty_vanishing {ι : Type*} [Fintype ι]
    (M : ι → List (ℕ × PowerSeries (Ambient F)))
    (hne : ∀ i, M i ≠ [])
    (hQ : ∀ i j, ((M i).get j).2 = 1)
    (hpos : ∀ i j, 1 ≤ ((M i).get j).1)
    (𝔰 : ∀ i, Fin ((M i).length) → ℕ+)
    (h𝔰 : ∀ i j, (𝔰 i j : ℕ) = ((M i).get (Fin.rev j)).1)
    (h𝔰q : ∀ i j, (𝔰 i j : ℕ) ≤ Nat.card F)
    (w : ℕ) (hw : ∀ i, (∑ j, (𝔰 i j : ℕ)) = w)
    (c : ι → RatFunc F)
    (h : ∑ i, c i • ζ_A F (𝔰 i) = 0) :
    ∑ i, ambKHomAmb F (c i) * evalSeriesGen (atLrGen (Nat.card F) (ambOmega F) (M i))
      (ambTheta F) = 0 := by
  classical
  have hrel := ambInfHom_zeta_A_relation F (fun i => (M i).length)
    (fun i => List.length_pos_iff.mpr (hne i)) 𝔰 c h
  have hb : ∀ i, (ambPiTilde F) ^ w
      * evalSeriesGen (atLrGen (Nat.card F) (ambOmega F) (M i)) (ambTheta F)
      = ambInfHom F (ζ_A F (𝔰 i)) := by
    intro i
    rw [← hw i]
    exact bridge F (M i) (hne i) (hQ i) (hpos i) (𝔰 i) (h𝔰 i) (h𝔰q i)
  have hpinv : ((ambPiTilde F) ^ w)⁻¹ * (ambPiTilde F) ^ w = 1 :=
    inv_mul_cancel₀ (pow_ne_zero _ (ambPiTilde_ne_zero F))
  have hmain : (∑ i, ambKHomAmb F (c i) * evalSeriesGen (atLrGen (Nat.card F) (ambOmega F) (M i))
        (ambTheta F))
      = ((ambPiTilde F) ^ w)⁻¹ * ∑ i, ambKHomAmb F (c i) * ambInfHom F (ζ_A F (𝔰 i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ambKHomAmb_eq, ← hb i,
      show ↑((ambKEquiv F) (c i)) * ((ambPiTilde F) ^ w
          * evalSeriesGen (atLrGen (Nat.card F) (ambOmega F) (M i)) (ambTheta F))
        = (ambPiTilde F) ^ w * (↑((ambKEquiv F) (c i))
          * evalSeriesGen (atLrGen (Nat.card F) (ambOmega F) (M i)) (ambTheta F)) from by ring,
      ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (ambPiTilde_ne_zero F)), one_mul]
  rw [hmain]
  have hzero : (∑ i, ambKHomAmb F (c i) * ambInfHom F (ζ_A F (𝔰 i))) = 0 := by
    simpa only [ambKHomAmb_eq] using hrel
  rw [hzero, mul_zero]

end FEmpty


/-! ## §12. Step 3 (II): the single-summand form of `f_𝔱` -/

section Step3II

attribute [local instance 100] Classical.decEq

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- **The bridge multiplied by an element of `K`** (the shape in which Step 3's second relation is
used). -/
theorem bridge_mul (M : List (ℕ × PowerSeries (Ambient F))) (hne : M ≠ [])
    (hQ : ∀ j : Fin M.length, (M.get j).2 = 1)
    (hpos : ∀ j : Fin M.length, 1 ≤ (M.get j).1)
    (𝔰 : Fin M.length → ℕ+) (h𝔰 : ∀ j : Fin M.length, (𝔰 j : ℕ) = (M.get (Fin.rev j)).1)
    (h𝔰q : ∀ j : Fin M.length, (𝔰 j : ℕ) ≤ Nat.card F)
    (a : Polynomial (Ambient F)) :
    (ambPiTilde F) ^ (∑ j, (𝔰 j : ℕ))
        * (a.eval (ambTheta F) * evalSeriesGen (atLrGen (Nat.card F) (ambOmega F) M) (ambTheta F))
      = a.eval (ambTheta F) * ambInfHom F (ζ_A F 𝔰) := by
  rw [← mul_assoc, mul_comm ((ambPiTilde F) ^ (∑ j, (𝔰 j : ℕ))) (a.eval (ambTheta F)),
    mul_assoc, bridge F M hne hQ hpos 𝔰 h𝔰 h𝔰q]

/-- **Step 3 (II)**: when `t` is a prefix of `s₀ ∈ S` and `s₀` is the unique element of `S` having
`t` as a prefix, the value `f_𝔱(θ)` of the `t`-row of the `t`-motive is a SINGLE term
`(cf s₀)(θ)·𝓛(s₀ \ t)(θ)`.  Combined with `bridge_mul` this gives
`π̃^{w(s₀\t)}·f_𝔱(θ) = (cf s₀)(θ)·ambInfHom (ζ_A 𝔰_{s₀\t})`, the equation whose valuation yields
the divisibility `(q-1) ∣ w(s₀ \ t)` of Dac §5.3. -/
theorem evalSeriesGen_tmF_single {S : Finset (List (ℕ × Polynomial (Ambient F)))}
    {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}
    {t s₀ : List (ℕ × Polynomial (Ambient F))} (w : ℕ)
    (hs₀ : s₀ ∈ S) (ht : s₀.take t.length = t)
    (hun : ∀ s ∈ S, s.take t.length = t → s = s₀)
    (hse2 : GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F) (s₀.drop t.length))) :
    evalSeriesGen (tmF (Nat.card F) (ambOmega F) w S cf t) (ambTheta F)
      = (cf s₀).eval (ambTheta F)
        * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (s₀.drop t.length)) (ambTheta F) := by
  classical
  rw [tmF_eq_single (K := Ambient F) hs₀ ht hun,
    evalSeriesGen_mul ambGamma_lt_one gammaArchimedean_rat
      (GSuperEntire.polynomial ambGamma_pos ambGamma_le_one (cf s₀)) hse2,
    evalSeriesGen_polynomial]

end Step3II


/-! ## §13. Super-entireness of `tmL` for unit `Q`'s -/

section TmLUnit

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- **`GSuperEntire` of `tmL` for unit `Q`'s**: the missing `GSuperEntire` hypothesis of
`evalSeriesGen_tmF_single` in the MZV application (`Q = 1`, exponents `≥ 1`). -/
theorem gSuperEntire_tmL_unit (L : List (ℕ × Polynomial (Ambient F)))
    (hQ : ∀ x ∈ L, x.2 = 1) (hpos : ∀ x ∈ L, 1 ≤ x.1) :
    GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F) L) := by
  rw [tmL]
  refine gSuperEntire_atLrPaperGen (γ := ambGamma) (K := Ambient F) (q := Nat.card F)
    (ω := ambOmega F) (L := tmCoe (K := Ambient F) L)
    ambGamma_lt_one gammaArchimedean_rat (two_le_ambCard F)
    (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F) ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [hQ y hy]
    simp only [Polynomial.coe_one, mul_one]
    rw [← Nat.sub_add_cancel (hpos y hy)]
    exact GIsSmall.pow_add_one ambGamma_le_one (gIsSmall_ambOmega F) (y.1 - 1)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [hQ y hy]
    simp only [Polynomial.coe_one]
    exact GSuperEntire.one ambGamma

end TmLUnit

end ZagierHoffmanPositiveChar
