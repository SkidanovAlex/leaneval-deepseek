/-
# The global carry bound: assembling the block decomposition

`Work.Asymptotics.block_factorization` decomposes `γ ∈ SL(2,ℤ)` as
`γ = (∏_{i<n} w_i) · δ` where `δ ∈ {1, -1, S, -S}` and each `w_i` is a block `T^k` or `S T^k`,
with `n = O(log(1 + ‖γ‖))` and `∏ (1 + ‖w_i‖) = O(‖γ‖^N)`.

This file runs the carry cocycle along that word.  Writing `blk p` for the block `T^{p.1}` or
`S T^{p.1}` (`p.2` records which), `carryBlk p i` for the carries of `blk p` supplied by
`CarryBoundBlockZ`, and
`Amp L = ∏_{p ∈ L} (1 + Frob (blk p))`, the recursion

`bCarry (p :: L) i = ∑_j σ(blk p)_{ij} • bCarry L j + carryBlk p i · of (L.map blk).prod`

satisfies `carryComb (bCarry L i) = rowDiff (of (L.map blk).prod) i` and the bound
`CB (bCarry L i) (Amp L ^ 12 · (1 + ∑_{p∈L} Bf p)) (Amp L · (1 + ∑_{p∈L} Kf p))`.

Since `Amp L` is polynomially bounded in `Frob γ` and `n = O(log)`, the whole bound is
polynomial; the base cases `δ ∈ {1,-1,S,-S}` are handled with the explicit carries
`carryDelta`.
-/
import Mathlib
import Submission.Work.Asymptotics.CarryBoundBlockZ
import Submission.Work.Asymptotics.block_factorization

set_option maxHeartbeats 2000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels
open Work.Residues

/-! ## The blocks `T^k`, `S T^k` and their carries -/

/-- The block indexed by `p : ℤ × Bool`: `T^{p.1}` if `p.2 = false` and `S T^{p.1}` if
`p.2 = true`. -/
noncomputable def blk : ℤ × Bool → SL(2, ℤ)
  | (k, false) => ModularGroup.T ^ k
  | (k, true) => ModularGroup.S * ModularGroup.T ^ k

/-- The carries of the block `blk p`. -/
noncomputable def carryBlk : ℤ × Bool → Fin 6 → R × R × R
  | (k, false), i => carryT k i
  | (k, true), i => carryST k i

/-- The component bound attached to the block `p`. -/
noncomputable def Bf : ℤ × Bool → ℝ
  | (k, false) => cbT k
  | (k, true) => cbST k

/-- The support bound attached to the block `p`. -/
noncomputable def Kf : ℤ × Bool → ℝ
  | (k, false) => kbu k
  | (k, true) => kbu k

@[simp] lemma blk_false (k : ℤ) : blk (k, false) = ModularGroup.T ^ k := rfl
@[simp] lemma blk_true (k : ℤ) : blk (k, true) = ModularGroup.S * ModularGroup.T ^ k := rfl
@[simp] lemma carryBlk_false (k : ℤ) (i : Fin 6) : carryBlk (k, false) i = carryT k i := rfl
@[simp] lemma carryBlk_true (k : ℤ) (i : Fin 6) : carryBlk (k, true) i = carryST k i := rfl
@[simp] lemma Bf_false (k : ℤ) : Bf (k, false) = cbT k := rfl
@[simp] lemma Bf_true (k : ℤ) : Bf (k, true) = cbST k := rfl
@[simp] lemma Kf_false (k : ℤ) : Kf (k, false) = kbu k := rfl
@[simp] lemma Kf_true (k : ℤ) : Kf (k, true) = kbu k := rfl

lemma abs_le_Frob_ST_zpow (k : ℤ) :
    |(k : ℝ)| ≤ Frob (ModularGroup.S * ModularGroup.T ^ k) := by
  rw [Frob_ST_zpow k, Real.le_sqrt (abs_nonneg _) (by positivity)]
  nlinarith [sq_abs (k : ℝ)]

lemma Bf_nonneg (p : ℤ × Bool) : 0 ≤ Bf p := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [Bf_false, cbT]; positivity
  · rw [Bf_true, cbST]; positivity

lemma one_add_Frob_nonneg (γ : SL(2, ℤ)) : (0 : ℝ) ≤ 1 + Frob γ := by
  have := Frob_nonneg γ; linarith

lemma Kf_nonneg (p : ℤ × Bool) : 0 ≤ Kf p := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [Kf_false, kbu]; positivity
  · rw [Kf_true, kbu]; positivity

lemma Bf_le (p : ℤ × Bool) : Bf p ≤ 2000000 * (1 + Frob (blk p)) ^ 5 := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [Bf_false, blk_false, cbT]
    have h1 : 1 + |(k : ℝ)| ≤ 1 + Frob (ModularGroup.T ^ k) := by
      have := abs_le_Frob_T_zpow k; linarith
    have h2 : (1 + |(k : ℝ)|) ^ 5 ≤ (1 + Frob (ModularGroup.T ^ k)) ^ 5 :=
      pow_le_pow_left₀ (by positivity) h1 5
    have h3 : (0 : ℝ) ≤ (1 + Frob (ModularGroup.T ^ k)) ^ 5 :=
      pow_nonneg (one_add_Frob_nonneg _) 5
    calc 300000 * (1 + |(k : ℝ)|) ^ 5
        ≤ 300000 * (1 + Frob (ModularGroup.T ^ k)) ^ 5 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 2000000 * (1 + Frob (ModularGroup.T ^ k)) ^ 5 :=
          mul_le_mul_of_nonneg_right (by norm_num) h3
  · rw [Bf_true, blk_true, cbST]
    have h1 : 1 + |(k : ℝ)| ≤ 1 + Frob (ModularGroup.S * ModularGroup.T ^ k) := by
      have := abs_le_Frob_ST_zpow k; linarith
    have h2 : (1 + |(k : ℝ)|) ^ 5
        ≤ (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 5 :=
      pow_le_pow_left₀ (by positivity) h1 5
    have h3 : (0 : ℝ) ≤ (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 5 :=
      pow_nonneg (one_add_Frob_nonneg _) 5
    calc 2000000 * (1 + |(k : ℝ)|) ^ 5
        ≤ 2000000 * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 5 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 2000000 * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 5 := le_refl _

lemma Kf_le (p : ℤ × Bool) : Kf p ≤ 1000 * (1 + Frob (blk p)) ^ 2 := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [Kf_false, blk_false, kbu]
    have h1 : 1 + |(k : ℝ)| ≤ 1 + Frob (ModularGroup.T ^ k) := by
      have := abs_le_Frob_T_zpow k; linarith
    have h2 : (1 + |(k : ℝ)|) ^ 2 ≤ (1 + Frob (ModularGroup.T ^ k)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (0 : ℝ) ≤ (1 + Frob (ModularGroup.T ^ k)) ^ 2 :=
      pow_nonneg (one_add_Frob_nonneg _) 2
    calc 1000 * (1 + |(k : ℝ)|) ^ 2
        ≤ 1000 * (1 + Frob (ModularGroup.T ^ k)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 1000 * (1 + Frob (ModularGroup.T ^ k)) ^ 2 := le_refl _
  · rw [Kf_true, blk_true, kbu]
    have h1 : 1 + |(k : ℝ)| ≤ 1 + Frob (ModularGroup.S * ModularGroup.T ^ k) := by
      have := abs_le_Frob_ST_zpow k; linarith
    have h2 : (1 + |(k : ℝ)|) ^ 2
        ≤ (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (0 : ℝ) ≤ (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 2 :=
      pow_nonneg (one_add_Frob_nonneg _) 2
    calc 1000 * (1 + |(k : ℝ)|) ^ 2
        ≤ 1000 * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 1000 * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 2 := le_refl _

theorem carryBlk_spec (p : ℤ × Bool) (i : Fin 6) :
    carryComb (carryBlk p i).1 (carryBlk p i).2.1 (carryBlk p i).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p)) i := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [carryBlk_false, blk_false]
    exact carryT_spec k i
  · rw [carryBlk_true, blk_true]
    exact carryST_spec k i

theorem carryBlk_bound (p : ℤ × Bool) (i : Fin 6) : CB (carryBlk p i) (Bf p) (Kf p) := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [carryBlk_false, Bf_false, Kf_false]
    exact carryT_bound k i
  · rw [carryBlk_true, Bf_true, Kf_true]
    exact carryST_bound k i

/-- Entrywise bound for `σ` of a block. -/
lemma sigma_blk_entry_le (p : ℤ × Bool) (i j : Fin 6) :
    ‖(Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j‖
      ≤ 60 * (1 + Frob (blk p)) ^ 2 := by
  rcases p with ⟨k, b⟩
  cases b
  · rw [blk_false, ← sigmaOfT_eq k]
    have h1 : 1 + |(k : ℝ)| ≤ 1 + Frob (ModularGroup.T ^ k) := by
      have := abs_le_Frob_T_zpow k; linarith
    have h2 : (1 + |(k : ℝ)|) ^ 2 ≤ (1 + Frob (ModularGroup.T ^ k)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (0 : ℝ) ≤ (1 + Frob (ModularGroup.T ^ k)) ^ 2 :=
      pow_nonneg (one_add_Frob_nonneg _) 2
    calc ‖sigmaOfT k i j‖ ≤ 10 * (1 + |(k : ℝ)|) ^ 2 := sigmaOfT_entry_bound k i j
      _ ≤ 10 * (1 + Frob (ModularGroup.T ^ k)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 60 * (1 + Frob (ModularGroup.T ^ k)) ^ 2 :=
          mul_le_mul_of_nonneg_right (by norm_num) h3
  · rw [blk_true, sigmaR_of_ST_zpow k, Matrix.mul_apply]
    have hS : ∀ m : Fin 6, ‖Work.Modular.sigmaS i m‖ ≤ 1 := by
      intro m
      fin_cases i <;> fin_cases m <;>
        simp [Work.Modular.sigmaS, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one]
    have hstep : ‖∑ m : Fin 6, Work.Modular.sigmaS i m * sigmaOfT k m j‖
        ≤ 60 * (1 + |(k : ℝ)|) ^ 2 := by
      refine le_trans (norm_sum_le _ _) ?_
      have hle : ∀ m ∈ (Finset.univ : Finset (Fin 6)),
          ‖Work.Modular.sigmaS i m * sigmaOfT k m j‖ ≤ 10 * (1 + |(k : ℝ)|) ^ 2 := by
        intro m _
        rw [norm_mul]
        calc ‖Work.Modular.sigmaS i m‖ * ‖sigmaOfT k m j‖
            ≤ 1 * (10 * (1 + |(k : ℝ)|) ^ 2) :=
              mul_le_mul (hS m) (sigmaOfT_entry_bound k m j) (norm_nonneg _) (by norm_num)
          _ = 10 * (1 + |(k : ℝ)|) ^ 2 := one_mul _
      calc ∑ m : Fin 6, ‖Work.Modular.sigmaS i m * sigmaOfT k m j‖
          ≤ ∑ _m : Fin 6, 10 * (1 + |(k : ℝ)|) ^ 2 := Finset.sum_le_sum hle
        _ = 60 * (1 + |(k : ℝ)|) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            norm_num
            ring
    have h1 : 1 + |(k : ℝ)| ≤ 1 + Frob (ModularGroup.S * ModularGroup.T ^ k) := by
      have := abs_le_Frob_ST_zpow k; linarith
    have h2 : (1 + |(k : ℝ)|) ^ 2
        ≤ (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (0 : ℝ) ≤ (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 2 :=
      pow_nonneg (one_add_Frob_nonneg _) 2
    refine le_trans hstep ?_
    calc 60 * (1 + |(k : ℝ)|) ^ 2
        ≤ 60 * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 60 * (1 + Frob (ModularGroup.S * ModularGroup.T ^ k)) ^ 2 := le_refl _

/-- The `σ`-entry of a block, multiplied by `6`, is absorbed by `(1 + Frob) ^ 12`. -/
lemma six_sigma_blk_le (p : ℤ × Bool) (i j : Fin 6) :
    6 * ‖(Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j‖
      ≤ (1 + Frob (blk p)) ^ 12 := by
  have h := sigma_blk_entry_le p i j
  have h1 : (1 : ℝ) ≤ Frob (blk p) := one_le_Frob (blk p)
  have ha : (2 : ℝ) ≤ 1 + Frob (blk p) := by linarith
  have h10 : (1024 : ℝ) ≤ (1 + Frob (blk p)) ^ 10 := by
    have h2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) ha 10
    norm_num at h2
    linarith
  have h2 : (1 + Frob (blk p)) ^ 12 = (1 + Frob (blk p)) ^ 10 * (1 + Frob (blk p)) ^ 2 := by
    rw [← pow_add]
  have h0 : (0 : ℝ) ≤ (1 + Frob (blk p)) ^ 2 := by positivity
  nlinarith [h, h10, h2, h0]

/-! ## The word recursion and the polynomial bookkeeping -/

/-- `Amp L = ∏_{p ∈ L} (1 + Frob (blk p))`. -/
noncomputable def Amp (L : List (ℤ × Bool)) : ℝ := (L.map (fun p => 1 + Frob (blk p))).prod

/-- `SB L = ∑_{p ∈ L} Bf p`, the accumulated component bound. -/
noncomputable def SB (L : List (ℤ × Bool)) : ℝ := (L.map Bf).sum

/-- `SK L = ∑_{p ∈ L} Kf p`, the accumulated support bound. -/
noncomputable def SK (L : List (ℤ × Bool)) : ℝ := (L.map Kf).sum

@[simp] lemma Amp_nil : Amp [] = 1 := rfl
@[simp] lemma Amp_cons (p : ℤ × Bool) (L : List (ℤ × Bool)) :
    Amp (p :: L) = (1 + Frob (blk p)) * Amp L := by simp [Amp]
@[simp] lemma SB_nil : SB [] = 0 := rfl
@[simp] lemma SB_cons (p : ℤ × Bool) (L : List (ℤ × Bool)) :
    SB (p :: L) = Bf p + SB L := by simp [SB]
@[simp] lemma SK_nil : SK [] = 0 := rfl
@[simp] lemma SK_cons (p : ℤ × Bool) (L : List (ℤ × Bool)) :
    SK (p :: L) = Kf p + SK L := by simp [SK]

lemma one_le_mul' {a b : ℝ} (h1 : 1 ≤ a) (h2 : 1 ≤ b) : 1 ≤ a * b := by
  calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
    _ ≤ a * b := mul_le_mul h1 h2 (by norm_num) (by linarith)

lemma list_prod_map_one_le {α : Type*} (L : List α) {f : α → ℝ} (h : ∀ a, 1 ≤ f a) :
    (1 : ℝ) ≤ (L.map f).prod := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.map_cons, List.prod_cons]; exact one_le_mul' (h a) ih

lemma list_prod_map_nonneg {α : Type*} (L : List α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    (0 : ℝ) ≤ (L.map f).prod := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.map_cons, List.prod_cons]; exact mul_nonneg (h a) ih

lemma le_prod_map_of_mem {α : Type*} {L : List α} {p : α} (hp : p ∈ L)
    {f : α → ℝ} (h : ∀ a, 1 ≤ f a) : f p ≤ (L.map f).prod := by
  induction L with
  | nil => exact absurd hp List.not_mem_nil
  | cons q L ih =>
    rw [List.mem_cons] at hp
    rw [List.map_cons, List.prod_cons]
    rcases hp with rfl | hp
    · have h1 : (1 : ℝ) ≤ (L.map f).prod := list_prod_map_one_le L h
      have h0 : (0 : ℝ) ≤ f p := le_trans zero_le_one (h p)
      calc f p = f p * 1 := (mul_one _).symm
        _ ≤ f p * (L.map f).prod := mul_le_mul_of_nonneg_left h1 h0
    · have h1 : (1 : ℝ) ≤ f q := h q
      have h0 : (0 : ℝ) ≤ (L.map f).prod := list_prod_map_nonneg L (fun a => le_trans zero_le_one (h a))
      calc f p ≤ (L.map f).prod := ih hp
        _ = 1 * (L.map f).prod := (one_mul _).symm
        _ ≤ f q * (L.map f).prod := mul_le_mul_of_nonneg_right h1 h0

lemma le_prod_map_of_mem_three {L : List (ℤ × Bool)} {p : ℤ × Bool} (hp : p ∈ L)
    {f : ℤ × Bool → ℝ} (h : ∀ a, 1 ≤ f a) : f p ≤ (L.map f).prod :=
  le_prod_map_of_mem hp h

lemma Amp_one_le (L : List (ℤ × Bool)) : (1 : ℝ) ≤ Amp L :=
  list_prod_map_one_le L (fun p => by
    have := Frob_nonneg (blk p); linarith)

lemma Amp_nonneg (L : List (ℤ × Bool)) : (0 : ℝ) ≤ Amp L :=
  le_trans zero_le_one (Amp_one_le L)

lemma SB_nonneg (L : List (ℤ × Bool)) : (0 : ℝ) ≤ SB L := by
  induction L with
  | nil => simp
  | cons p L ih => rw [SB_cons]; linarith [Bf_nonneg p]

lemma SK_nonneg (L : List (ℤ × Bool)) : (0 : ℝ) ≤ SK L := by
  induction L with
  | nil => simp
  | cons p L ih => rw [SK_cons]; linarith [Kf_nonneg p]

lemma Amp_eq (L : List (ℤ × Bool)) :
    Amp L = (L.map (fun p => 1 + Frob (blk p))).prod := rfl

lemma one_add_Frob_blk_le_Amp {p : ℤ × Bool} {L : List (ℤ × Bool)} (hp : p ∈ L) :
    1 + Frob (blk p) ≤ Amp L := by
  rw [Amp_eq]
  exact le_prod_map_of_mem (f := fun q => 1 + Frob (blk q)) hp
    (fun q => by have := Frob_nonneg (blk q); linarith)

lemma Bf_le_Amp {p : ℤ × Bool} {L : List (ℤ × Bool)} (hp : p ∈ L) :
    Bf p ≤ 2000000 * Amp L ^ 5 := by
  have h1 := Bf_le p
  have h2 := one_add_Frob_blk_le_Amp hp
  have h3 : (0 : ℝ) ≤ 1 + Frob (blk p) := one_add_Frob_nonneg (blk p)
  have h4 : (1 + Frob (blk p)) ^ 5 ≤ Amp L ^ 5 := pow_le_pow_left₀ h3 h2 5
  have h5 : (0 : ℝ) ≤ (1 + Frob (blk p)) ^ 5 := pow_nonneg h3 5
  calc Bf p ≤ 2000000 * (1 + Frob (blk p)) ^ 5 := h1
    _ ≤ 2000000 * Amp L ^ 5 := mul_le_mul_of_nonneg_left h4 (by norm_num)

lemma Kf_le_Amp {p : ℤ × Bool} {L : List (ℤ × Bool)} (hp : p ∈ L) :
    Kf p ≤ 1000 * Amp L ^ 2 := by
  have h1 := Kf_le p
  have h2 := one_add_Frob_blk_le_Amp hp
  have h3 : (0 : ℝ) ≤ 1 + Frob (blk p) := one_add_Frob_nonneg (blk p)
  have h4 : (1 + Frob (blk p)) ^ 2 ≤ Amp L ^ 2 := pow_le_pow_left₀ h3 h2 2
  calc Kf p ≤ 1000 * (1 + Frob (blk p)) ^ 2 := h1
    _ ≤ 1000 * Amp L ^ 2 := mul_le_mul_of_nonneg_left h4 (by norm_num)

lemma sum_map_le_length_mul {α : Type*} (L : List α) {f : α → ℝ} {K : ℝ}
    (h : ∀ p ∈ L, f p ≤ K) (hK : 0 ≤ K) : (L.map f).sum ≤ (L.length : ℝ) * K := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h p (List.mem_cons_self (a := p) (l := L))
    have h2 := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    push_cast
    linarith

lemma Frob_prod_le (L : List (ℤ × Bool)) : Frob ((L.map blk).prod) ≤ 2 * Amp L := by
  induction L with
  | nil =>
    have h : Frob ((([] : List (ℤ × Bool)).map blk).prod) = Real.sqrt 2 := by
      rw [List.map_nil, List.prod_nil]; exact Frob_one
    rw [h, Amp_nil]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  | cons p L ih =>
    rw [List.map_cons, List.prod_cons, Amp_cons]
    have h0 : (0 : ℝ) ≤ Frob (blk p) := Frob_nonneg (blk p)
    have h1 : Frob (blk p) ≤ 1 + Frob (blk p) := by linarith
    have h2 : (0 : ℝ) ≤ 2 * Amp L := by linarith [Amp_nonneg L]
    calc Frob (blk p * (L.map blk).prod)
        ≤ Frob (blk p) * Frob ((L.map blk).prod) := Frob_mul_le _ _
      _ ≤ (1 + Frob (blk p)) * (2 * Amp L) := mul_le_mul h1 ih (Frob_nonneg _) (by linarith)
      _ = 2 * ((1 + Frob (blk p)) * Amp L) := by ring

lemma six_Np_le (p : ℤ × Bool) :
    6 * (60 * (1 + Frob (blk p)) ^ 2) ≤ (1 + Frob (blk p)) ^ 12 := by
  have h1 : (1 : ℝ) ≤ Frob (blk p) := one_le_Frob (blk p)
  have ha : (2 : ℝ) ≤ 1 + Frob (blk p) := by linarith
  have h10 : (1024 : ℝ) ≤ (1 + Frob (blk p)) ^ 10 := by
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ha 10
    norm_num at h2
    linarith
  have h2 : (1 + Frob (blk p)) ^ 12
      = (1 + Frob (blk p)) ^ 10 * (1 + Frob (blk p)) ^ 2 := by rw [← pow_add]
  have h0 : (0 : ℝ) ≤ (1 + Frob (blk p)) ^ 2 :=
    pow_nonneg (one_add_Frob_nonneg _) 2
  nlinarith [h10, h2, h0]

/-! ## The carry recursion along the word -/

/-- The carries of the word `L` of blocks, defined by the cocycle recursion. -/
noncomputable def bCarry : List (ℤ × Bool) → Fin 6 → R × R × R
  | [], _ => (0, 0, 0)
  | p :: L, i =>
      triAdd (triSum (Finset.univ : Finset (Fin 6))
          (fun j => triSmul
            ((Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j)
            (bCarry L j)))
        (triMulOf (carryBlk p i) ((L.map blk).prod))

@[simp] lemma bCarry_nil (i : Fin 6) : bCarry [] i = ((0, 0, 0) : R × R × R) := rfl

@[simp] lemma bCarry_cons (p : ℤ × Bool) (L : List (ℤ × Bool)) (i : Fin 6) :
    bCarry (p :: L) i =
      triAdd (triSum (Finset.univ : Finset (Fin 6))
          (fun j => triSmul
            ((Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j)
            (bCarry L j)))
        (triMulOf (carryBlk p i) ((L.map blk).prod)) := rfl

theorem bCarry_spec (L : List (ℤ × Bool)) (i : Fin 6) :
    carryComb (bCarry L i).1 (bCarry L i).2.1 (bCarry L i).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod)) i := by
  induction L generalizing i with
  | nil =>
    rw [bCarry_nil,
      show (([] : List (ℤ × Bool)).map blk).prod = (1 : SL(2, ℤ)) from rfl,
      show MonoidAlgebra.of ℂ (SL(2, ℤ)) (1 : SL(2, ℤ)) = 1 from map_one _,
      Work.Residues.rowDiff_one]
    simp [carryComb]
  | cons p L ih =>
    rw [bCarry_cons, carryComb_triAdd, carryComb_triSum']
    rw [show (∑ j : Fin 6, carryComb
          (triSmul ((Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j)
            (bCarry L j)).1
          (triSmul ((Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j)
            (bCarry L j)).2.1
          (triSmul ((Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j)
            (bCarry L j)).2.2)
        = ∑ j : Fin 6, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j
          • carryComb (bCarry L j).1 (bCarry L j).2.1 (bCarry L j).2.2
      from Finset.sum_congr rfl (fun j _ => carryComb_triSmul _ _)]
    rw [show (∑ j : Fin 6, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j
          • carryComb (bCarry L j).1 (bCarry L j).2.1 (bCarry L j).2.2)
        = ∑ j : Fin 6, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j
          • Work.Residues.rowDiff
              (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod)) j
      from Finset.sum_congr rfl (fun j _ => by rw [ih j])]
    rw [carryComb_triMulOf, carryBlk_spec p i]
    rw [show ((p :: L).map blk).prod = blk p * (L.map blk).prod from by
      rw [List.map_cons, List.prod_cons]]
    rw [show MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p * (L.map blk).prod)
        = MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p)
          * MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod) from map_mul _ _ _]
    exact (Work.Residues.rowDiff_mul _ _ i).symm

theorem bCarry_bound (L : List (ℤ × Bool)) (i : Fin 6) :
    CB (bCarry L i) (Amp L ^ 12 * (1 + SB L)) (Amp L * (1 + SK L)) := by
  induction L generalizing i with
  | nil =>
    rw [bCarry_nil, Amp_nil, SB_nil, SK_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [coeffNorm_zero, supportFrobLe_zero]
  | cons p L ih =>
    rw [bCarry_cons]
    set CbL : ℝ := Amp L ^ 12 * (1 + SB L) with hCbL
    set KbL : ℝ := Amp L * (1 + SK L) with hKbL
    have hAmp1 : (1 : ℝ) ≤ Amp L := Amp_one_le L
    have hAmp0 : (0 : ℝ) ≤ Amp L := Amp_nonneg L
    have hSB0 : (0 : ℝ) ≤ SB L := SB_nonneg L
    have hSK0 : (0 : ℝ) ≤ SK L := SK_nonneg L
    have hBf0 : (0 : ℝ) ≤ Bf p := Bf_nonneg p
    have hKf0 : (0 : ℝ) ≤ Kf p := Kf_nonneg p
    have hCbL0 : (0 : ℝ) ≤ CbL := by rw [hCbL]; positivity
    have hKbL0 : (0 : ℝ) ≤ KbL := by rw [hKbL]; positivity
    have hF0 : (0 : ℝ) ≤ Frob (blk p) := Frob_nonneg (blk p)
    have hF1 : (1 : ℝ) ≤ 1 + Frob (blk p) := by linarith
    have hF2 : (2 : ℝ) ≤ 1 + Frob (blk p) := by
      have := one_le_Frob (blk p); linarith
    -- the sum part
    have hsumb : ∀ j : Fin 6,
        CB (triSmul ((Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j)
              (bCarry L j)) (60 * (1 + Frob (blk p)) ^ 2 * CbL) KbL := by
      intro j
      refine CB_mono (CB_triSmul _ (ih j)) ?_ (le_refl _)
      calc ‖(Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j‖ * CbL
          ≤ (60 * (1 + Frob (blk p)) ^ 2) * CbL :=
            mul_le_mul_of_nonneg_right (sigma_blk_entry_le p i j) hCbL0
        _ = 60 * (1 + Frob (blk p)) ^ 2 * CbL := by ring
    have hsum : CB (triSum (Finset.univ : Finset (Fin 6))
        (fun j => triSmul ((Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j)
          (bCarry L j)))
        (6 * (60 * (1 + Frob (blk p)) ^ 2 * CbL)) KbL := by
      refine CB_triSum (Finset.univ : Finset (Fin 6)) _
        (Cb := 60 * (1 + Frob (blk p)) ^ 2 * CbL) (K := KbL) ?_
      intro j _
      exact hsumb j
    have hsum' : CB (triSum (Finset.univ : Finset (Fin 6))
        (fun j => triSmul ((Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i j)
          (bCarry L j)))
        ((1 + Frob (blk p)) ^ 12 * CbL) KbL := by
      refine CB_mono hsum ?_ (le_refl _)
      calc 6 * (60 * (1 + Frob (blk p)) ^ 2 * CbL)
          = (6 * (60 * (1 + Frob (blk p)) ^ 2)) * CbL := by ring
        _ ≤ ((1 + Frob (blk p)) ^ 12) * CbL :=
            mul_le_mul_of_nonneg_right (six_Np_le p) hCbL0
    -- the tail
    have htail : CB (triMulOf (carryBlk p i) ((L.map blk).prod)) (Bf p)
        (Kf p * (2 * Amp L)) := by
      refine CB_mono (CB_triMulOf _ (carryBlk_bound p i)) (le_refl _) ?_
      have hF := Frob_prod_le L
      calc Kf p * Frob ((L.map blk).prod) ≤ Kf p * (2 * Amp L) :=
            mul_le_mul_of_nonneg_left hF hKf0
        _ = Kf p * (2 * Amp L) := rfl
    have hadd := CB_triAdd hsum' htail
    -- the final comparison
    have hCp : (1 + Frob (blk p)) ^ 12 * CbL + Bf p
        ≤ ((1 + Frob (blk p)) * Amp L) ^ 12 * (1 + (Bf p + SB L)) := by
      rw [mul_pow, hCbL]
      have ha12 : (1 : ℝ) ≤ (1 + Frob (blk p)) ^ 12 := one_le_pow₀ hF1
      have hb12 : (1 : ℝ) ≤ Amp L ^ 12 := one_le_pow₀ hAmp1
      have hkey : Bf p ≤ (1 + Frob (blk p)) ^ 12 * Amp L ^ 12 * Bf p := by
        have h1 : (1 : ℝ) ≤ (1 + Frob (blk p)) ^ 12 * Amp L ^ 12 := by nlinarith [ha12, hb12]
        calc Bf p = 1 * Bf p := (one_mul _).symm
          _ ≤ ((1 + Frob (blk p)) ^ 12 * Amp L ^ 12) * Bf p :=
              mul_le_mul_of_nonneg_right h1 hBf0
      calc (1 + Frob (blk p)) ^ 12 * (Amp L ^ 12 * (1 + SB L)) + Bf p
          ≤ (1 + Frob (blk p)) ^ 12 * (Amp L ^ 12 * (1 + SB L))
            + (1 + Frob (blk p)) ^ 12 * Amp L ^ 12 * Bf p := add_le_add_right hkey _
        _ = (1 + Frob (blk p)) ^ 12 * Amp L ^ 12 * (1 + (Bf p + SB L)) := by ring
    have hKp : max KbL (Kf p * (2 * Amp L))
        ≤ (1 + Frob (blk p)) * Amp L * (1 + (Kf p + SK L)) := by
      rw [hKbL]
      refine max_le ?_ ?_
      · have h2 : 1 + SK L ≤ 1 + (Kf p + SK L) := by linarith
        calc Amp L * (1 + SK L) ≤ Amp L * (1 + (Kf p + SK L)) :=
              mul_le_mul_of_nonneg_left h2 hAmp0
          _ ≤ (1 + Frob (blk p)) * (Amp L * (1 + (Kf p + SK L))) :=
              le_mul_of_one_le_left (by positivity) hF1
          _ = (1 + Frob (blk p)) * Amp L * (1 + (Kf p + SK L)) := by ring
      · have h2 : Kf p * 2 ≤ (1 + Frob (blk p)) * (1 + (Kf p + SK L)) := by
          nlinarith [hF2, hKf0, hSK0]
        calc Kf p * (2 * Amp L) = (Kf p * 2) * Amp L := by ring
          _ ≤ ((1 + Frob (blk p)) * (1 + (Kf p + SK L))) * Amp L :=
              mul_le_mul_of_nonneg_right h2 hAmp0
          _ = (1 + Frob (blk p)) * Amp L * (1 + (Kf p + SK L)) := by ring
    rw [Amp_cons, SB_cons, SK_cons]
    exact CB_mono hadd hCp hKp

/-! ## The four base carries for `δ ∈ {1, -1, S, -S}` -/

lemma carryComb_zero_zero (c : R) : carryComb 0 0 c = (Work.Residues.Rneg - 1) * c := by
  simp [carryComb]

lemma CB_triple (a b c : R) (x y : ℝ) :
    CB ((a, b, c) : R × R × R) x y ↔ coeffNorm a ≤ x ∧ coeffNorm b ≤ x ∧ coeffNorm c ≤ x
      ∧ supportFrobLe a y ∧ supportFrobLe b y ∧ supportFrobLe c y := Iff.rfl

lemma sum_one_smul (i : Fin 6) (X : Fin 6 → R) :
    (∑ j : Fin 6, (1 : Matrix (Fin 6) (Fin 6) ℂ) i j • X j) = X i := by
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma rowDiff_Rneg_eq (i : Fin 6) :
    Work.Residues.rowDiff Work.Residues.Rneg i
      = Work.Residues.M6 i * (Work.Residues.Rneg - 1) := by
  rw [Work.Residues.rowDiff, Work.Residues.sigmaR_Rneg, sum_one_smul i Work.Residues.M6,
    mul_sub, mul_one]

lemma rowDiff_of_neg_one (i : Fin 6) :
    Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2, ℤ)) (-1 : SL(2, ℤ))) i
      = Work.Residues.M6 i * (Work.Residues.Rneg - 1) := by
  have h : MonoidAlgebra.of ℂ (SL(2, ℤ)) (-1 : SL(2, ℤ)) = Work.Residues.Rneg := rfl
  rw [h, rowDiff_Rneg_eq]

/-- The carries of the four elements `1, -1, S, -S`. -/
noncomputable def carryDelta (δ : SL(2, ℤ)) (i : Fin 6) : R × R × R :=
  if δ = 1 then (0, 0, 0)
  else if δ = -1 then (0, 0, Work.Residues.M6 i)
  else if δ = ModularGroup.S then carryAtomS i
  else triAdd (carryAtomS i) (triMulOf (0, 0, Work.Residues.M6 i) ModularGroup.S)

lemma negS_ne_S : (-ModularGroup.S : SL(2, ℤ)) ≠ ModularGroup.S := by decide
lemma negS_ne_one : (-ModularGroup.S : SL(2, ℤ)) ≠ 1 := by decide
lemma negS_ne_neg_one : (-ModularGroup.S : SL(2, ℤ)) ≠ -1 := by decide
lemma neg_one_ne_one : (-1 : SL(2, ℤ)) ≠ 1 := by decide
lemma S_ne_neg_one : (ModularGroup.S : SL(2, ℤ)) ≠ -1 := by decide
lemma S_ne_one : (ModularGroup.S : SL(2, ℤ)) ≠ 1 := by decide

lemma carryDelta_one (i : Fin 6) :
    carryDelta 1 i = ((0, 0, 0) : R × R × R) := by
  rw [carryDelta, if_pos rfl]

lemma carryDelta_neg_one (i : Fin 6) :
    carryDelta (-1) i = ((0, 0, Work.Residues.M6 i) : R × R × R) := by
  rw [carryDelta, if_neg neg_one_ne_one, if_pos rfl]

lemma carryDelta_S (i : Fin 6) :
    carryDelta ModularGroup.S i = carryAtomS i := by
  rw [carryDelta, if_neg S_ne_one, if_neg S_ne_neg_one, if_pos rfl]

lemma carryDelta_negS (i : Fin 6) :
    carryDelta (-ModularGroup.S) i
      = triAdd (carryAtomS i)
          (triMulOf (0, 0, Work.Residues.M6 i) ModularGroup.S) := by
  rw [carryDelta, if_neg negS_ne_one, if_neg negS_ne_neg_one, if_neg negS_ne_S]

lemma supportFrobLe_of_of (g : SL(2, ℤ)) :
    supportFrobLe (MonoidAlgebra.of ℂ (SL(2, ℤ)) g) (Frob g) := by
  intro γ hγ
  have hcoeff : (MonoidAlgebra.of ℂ (SL(2, ℤ)) g).coeff = Finsupp.single g (1 : ℂ) := by
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single]
  rw [hcoeff] at hγ
  have hsub := Finsupp.support_single_subset (a := g) (b := (1 : ℂ))
  have : γ ∈ ({g} : Finset SL(2, ℤ)) := hsub hγ
  rw [Finset.mem_singleton] at this
  rw [this]

lemma M6_coeffNorm (i : Fin 6) : coeffNorm (Work.Residues.M6 i) ≤ 4 := by
  have h1 : ∀ g : SL(2, ℤ), coeffNorm (MonoidAlgebra.of ℂ (SL(2, ℤ)) g) ≤ 1 := coeffNorm_of_le
  have h2 : ∀ a b : SL(2, ℤ),
      coeffNorm (MonoidAlgebra.of ℂ (SL(2, ℤ)) a * MonoidAlgebra.of ℂ (SL(2, ℤ)) b) ≤ 1 :=
    fun a b => le_trans (coeffNorm_mul_of_le _ b) (h1 a)
  have h3 : ∀ a b c : SL(2, ℤ),
      coeffNorm (MonoidAlgebra.of ℂ (SL(2, ℤ)) a * MonoidAlgebra.of ℂ (SL(2, ℤ)) b
        * MonoidAlgebra.of ℂ (SL(2, ℤ)) c) ≤ 1 := by
    intro a b c
    refine le_trans (coeffNorm_mul_of_le _ c) ?_
    exact le_trans (coeffNorm_mul_of_le _ b) (h1 a)
  fin_cases i
  · show coeffNorm (Work.Residues.M6 (0 : Fin 6)) ≤ 4
    refine le_trans (h1 1) ?_; norm_num
  · show coeffNorm (Work.Residues.M6 (1 : Fin 6)) ≤ 4
    refine le_trans (h1 ModularGroup.T) ?_; norm_num
  · show coeffNorm (Work.Residues.M6 (2 : Fin 6)) ≤ 4
    refine le_trans (h2 ModularGroup.T ModularGroup.S) ?_; norm_num
  · show coeffNorm (Work.Residues.M6 (3 : Fin 6)) ≤ 4
    refine le_trans (h1 ModularGroup.S) ?_; norm_num
  · show coeffNorm (Work.Residues.M6 (4 : Fin 6)) ≤ 4
    refine le_trans (h2 ModularGroup.S ModularGroup.T) ?_; norm_num
  · show coeffNorm (Work.Residues.M6 (5 : Fin 6)) ≤ 4
    refine le_trans (h3 ModularGroup.S ModularGroup.T ModularGroup.S) ?_; norm_num

lemma M6_supportFrobLe (i : Fin 6) : supportFrobLe (Work.Residues.M6 i) 200 := by
  have hF2 : Frob (1 : SL(2, ℤ)) ≤ 2 := by
    rw [Frob_one]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hT2 : Frob (ModularGroup.T : SL(2, ℤ)) ≤ 2 := by
    rw [Frob_T]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have hS2 : Frob (ModularGroup.S : SL(2, ℤ)) ≤ 2 := by
    rw [Frob_S]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h2 : ∀ a b : SL(2, ℤ), Frob a ≤ 2 → Frob b ≤ 2 → Frob (a * b) ≤ 4 := by
    intro a b ha hb
    have h := Frob_mul_le a b
    nlinarith [Frob_nonneg a, Frob_nonneg b]
  have h3 : ∀ a b c : SL(2, ℤ), Frob a ≤ 2 → Frob b ≤ 2 → Frob c ≤ 2 →
      Frob (a * b * c) ≤ 8 := by
    intro a b c ha hb hc
    have h1 := h2 a b ha hb
    have h := Frob_mul_le (a * b) c
    nlinarith [Frob_nonneg (a * b), Frob_nonneg c]
  have e0 : Work.Residues.M6 (0 : Fin 6) = MonoidAlgebra.of ℂ (SL(2, ℤ)) (1 : SL(2, ℤ)) := by
    rw [Work.Residues.M6_zero, map_one]
  have e1 : Work.Residues.M6 (1 : Fin 6)
      = MonoidAlgebra.of ℂ (SL(2, ℤ)) ModularGroup.T := rfl
  have e2 : Work.Residues.M6 (2 : Fin 6)
      = MonoidAlgebra.of ℂ (SL(2, ℤ)) (ModularGroup.T * ModularGroup.S) := by
    rw [Work.Residues.M6_two]
    show MonoidAlgebra.of ℂ (SL(2, ℤ)) ModularGroup.T
      * MonoidAlgebra.of ℂ (SL(2, ℤ)) ModularGroup.S = _
    rw [← map_mul]
  have e3 : Work.Residues.M6 (3 : Fin 6)
      = MonoidAlgebra.of ℂ (SL(2, ℤ)) ModularGroup.S := rfl
  have e4 : Work.Residues.M6 (4 : Fin 6)
      = MonoidAlgebra.of ℂ (SL(2, ℤ)) (ModularGroup.S * ModularGroup.T) := by
    rw [Work.Residues.M6_four]
    show MonoidAlgebra.of ℂ (SL(2, ℤ)) ModularGroup.S
      * MonoidAlgebra.of ℂ (SL(2, ℤ)) ModularGroup.T = _
    rw [← map_mul]
  have e5 : Work.Residues.M6 (5 : Fin 6)
      = MonoidAlgebra.of ℂ (SL(2, ℤ)) (ModularGroup.S * ModularGroup.T * ModularGroup.S) := by
    rw [Work.Residues.M6_five]
    show MonoidAlgebra.of ℂ (SL(2, ℤ)) ModularGroup.S
      * MonoidAlgebra.of ℂ (SL(2, ℤ)) ModularGroup.T
      * MonoidAlgebra.of ℂ (SL(2, ℤ)) ModularGroup.S = _
    rw [← map_mul, ← map_mul]
  fin_cases i
  · show supportFrobLe (Work.Residues.M6 (0 : Fin 6)) 200
    rw [e0]
    exact supportFrobLe_mono (supportFrobLe_of_of 1) (by linarith)
  · show supportFrobLe (Work.Residues.M6 (1 : Fin 6)) 200
    rw [e1]
    exact supportFrobLe_mono (supportFrobLe_of_of ModularGroup.T) (by linarith)
  · show supportFrobLe (Work.Residues.M6 (2 : Fin 6)) 200
    rw [e2]
    exact supportFrobLe_mono (supportFrobLe_of_of _)
      (by have := h2 ModularGroup.T ModularGroup.S hT2 hS2; linarith)
  · show supportFrobLe (Work.Residues.M6 (3 : Fin 6)) 200
    rw [e3]
    exact supportFrobLe_mono (supportFrobLe_of_of ModularGroup.S) (by linarith)
  · show supportFrobLe (Work.Residues.M6 (4 : Fin 6)) 200
    rw [e4]
    exact supportFrobLe_mono (supportFrobLe_of_of _)
      (by have := h2 ModularGroup.S ModularGroup.T hS2 hT2; linarith)
  · show supportFrobLe (Work.Residues.M6 (5 : Fin 6)) 200
    rw [e5]
    exact supportFrobLe_mono (supportFrobLe_of_of _)
      (by have := h3 ModularGroup.S ModularGroup.T ModularGroup.S hS2 hT2 hS2; linarith)

lemma carryDelta_spec (δ : SL(2, ℤ)) (i : Fin 6)
    (h : δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) :
    carryComb (carryDelta δ i).1 (carryDelta δ i).2.1 (carryDelta δ i).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2, ℤ)) δ) i := by
  rcases h with rfl | rfl | rfl | rfl
  · rw [carryDelta_one]
    show carryComb (0 : R) 0 0 = _
    rw [show carryComb (0 : R) 0 0 = 0 from by simp [carryComb],
      show MonoidAlgebra.of ℂ (SL(2, ℤ)) (1 : SL(2, ℤ)) = 1 from map_one _,
      Work.Residues.rowDiff_one]
  · rw [carryDelta_neg_one]
    show carryComb (0 : R) 0 (Work.Residues.M6 i) = _
    rw [show carryComb (0 : R) 0 (Work.Residues.M6 i)
        = (Work.Residues.Rneg - 1) * Work.Residues.M6 i from by simp [carryComb],
      rowDiff_of_neg_one]
    exact (mul_Rneg_sub_one_comm' (Work.Residues.M6 i)).symm
  · rw [carryDelta_S]
    exact carryAtomS_spec i
  · rw [carryDelta_negS, carryComb_triAdd, carryComb_triMulOf, carryAtomS_spec i]
    show Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2, ℤ)) ModularGroup.S) i
      + carryComb (0 : R) 0 (Work.Residues.M6 i)
        * MonoidAlgebra.of ℂ (SL(2, ℤ)) ModularGroup.S = _
    rw [carryComb_zero_zero]
    have hof : MonoidAlgebra.of ℂ (SL(2, ℤ)) (-ModularGroup.S)
        = MonoidAlgebra.of ℂ (SL(2, ℤ)) (-1 : SL(2, ℤ))
          * MonoidAlgebra.of ℂ (SL(2, ℤ)) ModularGroup.S := by
      rw [← map_mul]
      congr 1
      decide
    rw [hof, Work.Residues.rowDiff_mul]
    rw [show (Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (-1 : SL(2, ℤ)))) = 1 from by
      rw [show MonoidAlgebra.of ℂ (SL(2, ℤ)) (-1 : SL(2, ℤ)) = Work.Residues.Rneg from rfl,
        Work.Residues.sigmaR_Rneg]]
    rw [sum_one_smul, rowDiff_of_neg_one]
    rw [show (Work.Residues.Rneg - 1) * Work.Residues.M6 i
        = Work.Residues.M6 i * (Work.Residues.Rneg - 1) from
      (mul_Rneg_sub_one_comm' (Work.Residues.M6 i)).symm]

lemma carryDelta_bound (δ : SL(2, ℤ)) (i : Fin 6)
    (h : δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) :
    CB (carryDelta δ i) 8 400 := by
  rcases h with rfl | rfl | rfl | rfl
  · rw [carryDelta_one, CB_triple]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [coeffNorm_zero, supportFrobLe_zero]
  · rw [carryDelta_neg_one, CB_triple]
    exact ⟨by simp [coeffNorm_zero], by simp [coeffNorm_zero],
      le_trans (M6_coeffNorm i) (by norm_num), supportFrobLe_zero 400, supportFrobLe_zero 400,
      supportFrobLe_mono (M6_supportFrobLe i) (by norm_num)⟩
  · rw [carryDelta_S]
    exact CB_mono (carryAtomS_bound i) (by norm_num : (1:ℝ) ≤ 8) (by norm_num : (100:ℝ) ≤ 400)
  · rw [carryDelta_negS]
    have hM6 : CB ((0, 0, Work.Residues.M6 i) : R × R × R) 4 200 := by
      rw [CB_triple]
      exact ⟨by simp [coeffNorm_zero], by simp [coeffNorm_zero], M6_coeffNorm i,
        supportFrobLe_zero 200, supportFrobLe_zero 200, M6_supportFrobLe i⟩
    have hFrobS : Frob (ModularGroup.S : SL(2, ℤ)) ≤ 2 := by
      rw [Frob_S]
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hCa : CB (carryAtomS i) 4 400 :=
      CB_mono (carryAtomS_bound i) (by norm_num : (1:ℝ) ≤ 4) (by norm_num : (100:ℝ) ≤ 400)
    have htail : CB (triMulOf (0, 0, Work.Residues.M6 i) ModularGroup.S) 4 400 := by
      have hK : (200 : ℝ) * Frob (ModularGroup.S : SL(2, ℤ)) ≤ 400 := by nlinarith [hFrobS]
      exact CB_mono (CB_triMulOf (ModularGroup.S) hM6) (le_refl 4) hK
    exact CB_mono (CB_triAdd hCa htail) (by norm_num : (4:ℝ) + 4 ≤ 8) (max_le le_rfl le_rfl)

/-! ## The polynomial bound for `σ` of a word of blocks -/

lemma sigma_prod_le (L : List (ℤ × Bool)) (i j : Fin 6) :
    ‖(Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod))) i j‖
      ≤ Amp L ^ 12 := by
  induction L generalizing i j with
  | nil =>
    rw [List.map_nil, List.prod_nil,
      show MonoidAlgebra.of ℂ (SL(2, ℤ)) (1 : SL(2, ℤ)) = 1 from map_one _, map_one,
      Amp_nil, Matrix.one_apply]
    split <;> norm_num
  | cons p L ih =>
    rw [List.map_cons, List.prod_cons,
      show MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p * (List.map blk L).prod)
        = MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p)
          * MonoidAlgebra.of ℂ (SL(2, ℤ)) ((List.map blk L).prod) from map_mul _ _ _,
      map_mul, Matrix.mul_apply, Amp_cons, mul_pow]
    have hA0 : (0 : ℝ) ≤ Amp L ^ 12 := by positivity
    calc ‖∑ m : Fin 6, (Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i m
          * (Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((List.map blk L).prod))) m j‖
        ≤ ∑ m : Fin 6, ‖(Work.Residues.sigmaR
              (MonoidAlgebra.of ℂ (SL(2, ℤ)) (blk p))) i m‖
            * ‖(Work.Residues.sigmaR
              (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((List.map blk L).prod))) m j‖ := by
          refine le_trans (norm_sum_le _ _) ?_
          exact Finset.sum_le_sum (fun m _ => by rw [norm_mul])
      _ ≤ ∑ _m : Fin 6, (60 * (1 + Frob (blk p)) ^ 2) * Amp L ^ 12 := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          exact mul_le_mul (sigma_blk_entry_le p i m) (ih m j) (norm_nonneg _)
            (by positivity)
      _ = 6 * ((60 * (1 + Frob (blk p)) ^ 2) * Amp L ^ 12) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
      _ ≤ (1 + Frob (blk p)) ^ 12 * Amp L ^ 12 := by
          rw [show (6 : ℝ) * ((60 * (1 + Frob (blk p)) ^ 2) * Amp L ^ 12)
              = (6 * (60 * (1 + Frob (blk p)) ^ 2)) * Amp L ^ 12 from by ring]
          exact mul_le_mul_of_nonneg_right (six_Np_le p) hA0

/-! ## The global bound -/

lemma rpow_nat_mul (x : ℝ) (hx : 0 ≤ x) (a : ℝ) (n : ℕ) : (x ^ a) ^ n = x ^ (a * n) := by
  rw [← Real.rpow_natCast (x ^ a) n, ← Real.rpow_mul hx]

lemma Frob_base_le (δ : SL(2, ℤ))
    (h : δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) : Frob δ ≤ 2 := by
  rcases h with rfl | rfl | rfl | rfl
  · rw [Frob_one]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  · rw [Frob_neg_one]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  · rw [Frob_S]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  · rw [Frob_neg_eq, Frob_S]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- The full carry of the word `L` followed by the base element `δ`: the `σ`-combination of the
base carries plus the carries of the word multiplied by `δ`. -/
noncomputable def wordCarryFull (L : List (ℤ × Bool)) (δ : SL(2, ℤ)) (i : Fin 6) : R × R × R :=
  triAdd (triSum (Finset.univ : Finset (Fin 6))
      (fun j => triSmul ((Work.Residues.sigmaR
          (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod))) i j) (carryDelta δ j)))
    (triMulOf (bCarry L i) δ)

lemma wordCarryFull_spec (L : List (ℤ × Bool)) (δ : SL(2, ℤ))
    (hδ : δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) (i : Fin 6) :
    carryComb (wordCarryFull L δ i).1 (wordCarryFull L δ i).2.1 (wordCarryFull L δ i).2.2
      = Work.Residues.rowDiff
          (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod * δ)) i := by
  unfold wordCarryFull
  rw [carryComb_triAdd, carryComb_triSum', carryComb_triMulOf]
  rw [show (∑ j : Fin 6, carryComb
        (triSmul ((Work.Residues.sigmaR
          (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod))) i j) (carryDelta δ j)).1
        (triSmul ((Work.Residues.sigmaR
          (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod))) i j) (carryDelta δ j)).2.1
        (triSmul ((Work.Residues.sigmaR
          (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod))) i j) (carryDelta δ j)).2.2)
      = ∑ j : Fin 6, (Work.Residues.sigmaR
          (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod))) i j
        • carryComb (carryDelta δ j).1 (carryDelta δ j).2.1 (carryDelta δ j).2.2
    from Finset.sum_congr rfl (fun j _ => carryComb_triSmul _ _)]
  rw [show (∑ j : Fin 6, (Work.Residues.sigmaR
          (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod))) i j
        • carryComb (carryDelta δ j).1 (carryDelta δ j).2.1 (carryDelta δ j).2.2)
      = ∑ j : Fin 6, (Work.Residues.sigmaR
          (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod))) i j
        • Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2, ℤ)) δ) j
    from Finset.sum_congr rfl (fun j _ => by rw [carryDelta_spec δ j hδ])]
  rw [bCarry_spec L i]
  rw [show MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod * δ)
      = MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod)
        * MonoidAlgebra.of ℂ (SL(2, ℤ)) δ from map_mul _ _ _]
  exact (Work.Residues.rowDiff_mul _ _ i).symm

lemma wordCarryFull_bound (L : List (ℤ × Bool)) (δ : SL(2, ℤ))
    (hδ : δ = 1 ∨ δ = -1 ∨ δ = ModularGroup.S ∨ δ = -ModularGroup.S) (i : Fin 6) :
    CB (wordCarryFull L δ i) (48 * Amp L ^ 12 + Amp L ^ 12 * (1 + SB L))
      (max 400 (Amp L * (1 + SK L) * Frob δ)) := by
  have hdelta : ∀ j : Fin 6, CB (carryDelta δ j) 8 400 := fun j => carryDelta_bound δ j hδ
  have hAmp0 : (0 : ℝ) ≤ Amp L ^ 12 := pow_nonneg (Amp_nonneg L) 12
  have hsumb : ∀ j : Fin 6,
      CB (triSmul ((Work.Residues.sigmaR
            (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod))) i j)
            (carryDelta δ j)) (Amp L ^ 12 * 8) 400 := by
    intro j
    refine CB_mono (CB_triSmul _ (hdelta j)) ?_ (le_refl _)
    exact mul_le_mul_of_nonneg_right (sigma_prod_le L i j) (by norm_num)
  have hsum : CB (triSum (Finset.univ : Finset (Fin 6))
      (fun j => triSmul ((Work.Residues.sigmaR
            (MonoidAlgebra.of ℂ (SL(2, ℤ)) ((L.map blk).prod))) i j) (carryDelta δ j)))
      (48 * Amp L ^ 12) 400 := by
    refine CB_mono (CB_triSum (Finset.univ : Finset (Fin 6)) _
      (Cb := Amp L ^ 12 * 8) (K := 400) (fun j _ => hsumb j)) ?_ (le_refl _)
    rw [Finset.card_univ, Fintype.card_fin]
    exact le_of_eq (by ring)
  have htail : CB (triMulOf (bCarry L i) δ) (Amp L ^ 12 * (1 + SB L))
      (Amp L * (1 + SK L) * Frob δ) := CB_triMulOf δ (bCarry_bound L i)
  unfold wordCarryFull
  exact CB_triAdd hsum htail

lemma pow_C1_le (C1 : ℝ) (hC1 : 0 ≤ C1) (hC1le : C1 ≤ 1 + C1) (n : ℕ) (hn : n ≤ 60) :
    C1 ^ n ≤ (1 + C1) ^ 60 :=
  le_trans (pow_le_pow_left₀ hC1 hC1le n)
    (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + C1) hn)

lemma C1_le_pow60 (C1 : ℝ) (hC1 : 0 ≤ C1) (hC1le : C1 ≤ 1 + C1) :
    C1 ≤ (1 + C1) ^ 60 := by
  have h2 : (1 + C1) ^ (1 : ℕ) ≤ (1 + C1) ^ 60 :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + C1) (by norm_num)
  rw [pow_one] at h2
  linarith

lemma mul3_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (0 : ℝ) ≤ a * b * c := mul_nonneg (mul_nonneg ha hb) hc

lemma mul4_nonneg {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (0 : ℝ) ≤ a * b * c * d := mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) hd

/-- **The polynomial bound for the carries.**  For every `γ ∈ SL(2, ℤ)` the error vector of the
reduction has carries whose `ℓ¹`-norms and supports are polynomially bounded. -/
theorem carry_bound_aux :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ γ : SL(2, ℤ),
      ∃ t : R × R × R,
        carryComb t.1 t.2.1 t.2.2 = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2, ℤ)) γ) 0
        ∧ CB t (C * (1 + Frob γ) ^ N) (C * (1 + Frob γ) ^ N) := by
  obtain ⟨C1, N1, hC1pos, hN1, hbf⟩ := block_factorization
  have hC1 : (0 : ℝ) ≤ C1 := le_of_lt hC1pos
  have hC1le : C1 ≤ 1 + C1 := by linarith
  have hA0 : (0 : ℝ) ≤ (1 + C1) ^ 60 := pow_nonneg (by linarith) 60
  refine ⟨10 ^ 40 * (1 + C1) ^ 60, 60 * N1 + 60,
    mul_nonneg (by norm_num) hA0, by linarith, fun γ => ?_⟩
  obtain ⟨n, w, δ, hδ, hw, hprod, hn, hpr⟩ := hbf γ
  set x : ℝ := 1 + Frob γ with hx
  set KK : ℝ := 10 ^ 40 * (1 + C1) ^ 60 with hKK
  set MM : ℝ := 60 * N1 + 60 with hMM
  have hx1 : (1 : ℝ) ≤ x := by rw [hx]; linarith [Frob_nonneg γ]
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx1
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hMM0 : (0 : ℝ) ≤ MM := by rw [hMM]; linarith
  have hKK1 : (1 : ℝ) ≤ KK := by
    rw [hKK]
    have hq : (1 : ℝ) ≤ (1 + C1) ^ 60 := one_le_pow₀ (by linarith)
    nlinarith [hA0]
  have hKK400 : (400 : ℝ) ≤ KK := by
    rw [hKK]
    have hq : (1 : ℝ) ≤ (1 + C1) ^ 60 := one_le_pow₀ (by linarith)
    calc (400 : ℝ) = 400 * 1 := by ring
      _ ≤ 400 * (1 + C1) ^ 60 := mul_le_mul_of_nonneg_left hq (by norm_num)
      _ ≤ 10 ^ 40 * (1 + C1) ^ 60 := mul_le_mul_of_nonneg_right (by norm_num) hA0
  have hex : ∀ i : Fin n, ∃ q : ℤ × Bool, w i = blk q := by
    intro i
    obtain ⟨k, hk⟩ := hw i
    rcases hk with hk | hk
    · exact ⟨(k, false), by rw [hk, blk_false]⟩
    · exact ⟨(k, true), by rw [hk, blk_true]⟩
  let p : Fin n → ℤ × Bool := fun i => Classical.choose (hex i)
  have hpw : ∀ i, w i = blk (p i) := fun i => Classical.choose_spec (hex i)
  let L : List (ℤ × Bool) := List.ofFn p
  have hAmp : Amp L = ∏ i : Fin n, (1 + Frob (w i)) := by
    rw [Amp_eq]
    change (List.map (fun q => 1 + Frob (blk q)) (List.ofFn p)).prod = _
    rw [List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_congr rfl (fun i _ => by
      simp only [Function.comp_apply]; rw [← hpw i])
  have hAmpLe : Amp L ≤ C1 * x ^ N1 := by
    rw [hAmp, hx]
    exact hpr
  have hLlen : (L.length : ℝ) = (n : ℝ) := by simp [L]
  have hlog : (L.length : ℝ) ≤ C1 * x := by
    have h1 : 1 + Real.log x ≤ x := by
      have := Real.log_le_sub_one_of_pos hxpos; linarith
    have h2 : C1 * (1 + Real.log x) ≤ C1 * x := mul_le_mul_of_nonneg_left h1 hC1
    have h3 : (L.length : ℝ) ≤ C1 * (1 + Real.log x) := by rw [hLlen, hx]; exact hn
    linarith
  have hLprod : (L.map blk).prod = (List.ofFn w).prod := by
    change ((List.ofFn p).map blk).prod = _
    rw [List.map_ofFn]
    rw [show (blk ∘ p) = w from funext (fun i => (hpw i).symm)]
  have hγ : (L.map blk).prod * δ = γ := by rw [hLprod]; exact hprod
  have hAmp0 : (0 : ℝ) ≤ Amp L := Amp_nonneg L
  have hSB0 : (0 : ℝ) ≤ SB L := SB_nonneg L
  have hSB : SB L ≤ C1 * x * (2000000 * Amp L ^ 5) := by
    have h1 : SB L ≤ (L.length : ℝ) * (2000000 * Amp L ^ 5) := by
      rw [SB]
      exact sum_map_le_length_mul L (fun q hq => Bf_le_Amp hq)
        (mul_nonneg (by norm_num) (pow_nonneg hAmp0 5))
    have h3 : (0 : ℝ) ≤ 2000000 * Amp L ^ 5 :=
      mul_nonneg (by norm_num) (pow_nonneg hAmp0 5)
    calc SB L ≤ (L.length : ℝ) * (2000000 * Amp L ^ 5) := h1
      _ ≤ (C1 * x) * (2000000 * Amp L ^ 5) := mul_le_mul_of_nonneg_right hlog h3
  have hSK : SK L ≤ C1 * x * (1000 * Amp L ^ 2) := by
    have h1 : SK L ≤ (L.length : ℝ) * (1000 * Amp L ^ 2) := by
      rw [SK]
      exact sum_map_le_length_mul L (fun q hq => Kf_le_Amp hq)
        (mul_nonneg (by norm_num) (pow_nonneg hAmp0 2))
    have h3 : (0 : ℝ) ≤ 1000 * Amp L ^ 2 :=
      mul_nonneg (by norm_num) (pow_nonneg hAmp0 2)
    calc SK L ≤ (L.length : ℝ) * (1000 * Amp L ^ 2) := h1
      _ ≤ (C1 * x) * (1000 * Amp L ^ 2) := mul_le_mul_of_nonneg_right hlog h3
  have hA12 : Amp L ^ 12 ≤ C1 ^ 12 * x ^ (N1 * 12) := by
    have h1 : Amp L ^ 12 ≤ (C1 * x ^ N1) ^ 12 := pow_le_pow_left₀ hAmp0 hAmpLe 12
    rwa [mul_pow, rpow_nat_mul x hx0 N1 12] at h1
  have hA5 : Amp L ^ 5 ≤ C1 ^ 5 * x ^ (N1 * 5) := by
    have h1 : Amp L ^ 5 ≤ (C1 * x ^ N1) ^ 5 := pow_le_pow_left₀ hAmp0 hAmpLe 5
    rwa [mul_pow, rpow_nat_mul x hx0 N1 5] at h1
  have hxi : ∀ a b : ℝ, a ≤ b → x ^ a ≤ x ^ b :=
    fun a b hab => Real.rpow_le_rpow_of_exponent_le hx1 hab
  have hxnn : ∀ a : ℝ, (0 : ℝ) ≤ x ^ a := fun a => Real.rpow_nonneg hx0 a
  have hmm1 : x ^ (12 * N1) ≤ x ^ MM := by
    rw [hMM]; exact hxi _ _ (by linarith)
  have hmm2 : x ^ (17 * N1 + 1) ≤ x ^ MM := by
    rw [hMM]; exact hxi _ _ (by linarith)
  have hmm3 : x ^ N1 ≤ x ^ MM := by
    rw [hMM]; exact hxi _ _ (by linarith)
  have hmm4 : x ^ (3 * N1 + 1) ≤ x ^ MM := by
    rw [hMM]; exact hxi _ _ (by linarith)
  -- the component estimate
  have hCb : 48 * Amp L ^ 12 + Amp L ^ 12 * (1 + SB L) ≤ KK * x ^ MM := by
    have hstep1 : Amp L ^ 12 * SB L ≤ 2000000 * C1 ^ 18 * x ^ (17 * N1 + 1) := by
      have h4 : Amp L ^ 12 * SB L
          ≤ (C1 ^ 12 * x ^ (N1 * 12)) * (C1 * x * (2000000 * Amp L ^ 5)) :=
        mul_le_mul hA12 hSB hSB0 (mul_nonneg (pow_nonneg hC1 12) (hxnn _))
      have h5 : (C1 ^ 12 * x ^ (N1 * 12)) * (C1 * x * (2000000 * Amp L ^ 5))
          ≤ (C1 ^ 12 * x ^ (N1 * 12)) * (C1 * x * (2000000 * (C1 ^ 5 * x ^ (N1 * 5)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (pow_nonneg hC1 12) (hxnn _))
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA5 (by norm_num))
          (mul_nonneg hC1 hx0)
      refine le_trans h4 (le_trans h5 ?_)
      have e1 : x ^ (N1 * 12) * (x * x ^ (N1 * 5)) = x ^ (17 * N1 + 1) := by
        rw [show x * x ^ (N1 * 5) = x ^ (1 : ℝ) * x ^ (N1 * 5) from by rw [Real.rpow_one]]
        rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
        congr 1
        ring
      have hrw : (C1 ^ 12 * x ^ (N1 * 12)) * (C1 * x * (2000000 * (C1 ^ 5 * x ^ (N1 * 5))))
          = 2000000 * C1 ^ 18 * x ^ (17 * N1 + 1) := by
        rw [show (C1 ^ 12 * x ^ (N1 * 12)) * (C1 * x * (2000000 * (C1 ^ 5 * x ^ (N1 * 5))))
            = 2000000 * C1 ^ 18 * (x ^ (N1 * 12) * (x * x ^ (N1 * 5))) from by ring]
        rw [e1]
      rw [hrw]
    have h49 : 49 * Amp L ^ 12 ≤ 49 * C1 ^ 12 * x ^ (12 * N1) := by
      calc 49 * Amp L ^ 12 ≤ 49 * (C1 ^ 12 * x ^ (N1 * 12)) :=
            mul_le_mul_of_nonneg_left hA12 (by norm_num)
        _ = 49 * C1 ^ 12 * x ^ (12 * N1) := by
            rw [show N1 * 12 = 12 * N1 from by ring]; ring
    have hsum1 : 48 * Amp L ^ 12 + Amp L ^ 12 * (1 + SB L)
        ≤ 49 * C1 ^ 12 * x ^ (12 * N1) + 2000000 * C1 ^ 18 * x ^ (17 * N1 + 1) := by
      have he : 48 * Amp L ^ 12 + Amp L ^ 12 * (1 + SB L)
          = 49 * Amp L ^ 12 + Amp L ^ 12 * SB L := by ring
      rw [he]
      linarith [h49, hstep1]
    have hcon : 49 * C1 ^ 12 + 2000000 * C1 ^ 18 ≤ KK := by
      rw [hKK]
      have e1 : 49 * C1 ^ 12 ≤ 49 * (1 + C1) ^ 60 :=
        mul_le_mul_of_nonneg_left (pow_C1_le C1 hC1 hC1le 12 (by norm_num)) (by norm_num)
      have e2 : 2000000 * C1 ^ 18 ≤ 2000000 * (1 + C1) ^ 60 :=
        mul_le_mul_of_nonneg_left (pow_C1_le C1 hC1 hC1le 18 (by norm_num)) (by norm_num)
      nlinarith [e1, e2, hA0]
    calc 48 * Amp L ^ 12 + Amp L ^ 12 * (1 + SB L)
        ≤ 49 * C1 ^ 12 * x ^ (12 * N1) + 2000000 * C1 ^ 18 * x ^ (17 * N1 + 1) := hsum1
      _ ≤ 49 * C1 ^ 12 * x ^ MM + 2000000 * C1 ^ 18 * x ^ MM :=
          add_le_add (mul_le_mul_of_nonneg_left hmm1 (by positivity))
            (mul_le_mul_of_nonneg_left hmm2 (by positivity))
      _ = (49 * C1 ^ 12 + 2000000 * C1 ^ 18) * x ^ MM := by ring
      _ ≤ KK * x ^ MM := mul_le_mul_of_nonneg_right hcon (hxnn _)
  -- the support estimate
  have hK : max 400 (Amp L * (1 + SK L) * Frob δ) ≤ KK * x ^ MM := by
    have hFδ : Frob δ ≤ 2 := Frob_base_le δ hδ
    have hxMM1 : (1 : ℝ) ≤ x ^ MM := Real.one_le_rpow hx1 hMM0
    refine max_le ?_ ?_
    · calc (400 : ℝ) = 400 * 1 := by ring
        _ ≤ 400 * x ^ MM := mul_le_mul_of_nonneg_left hxMM1 (by norm_num)
        _ ≤ KK * x ^ MM := mul_le_mul_of_nonneg_right hKK400 (hxnn MM)
    · have h1 : Amp L * (1 + SK L) * Frob δ ≤ Amp L * (1 + SK L) * 2 :=
        mul_le_mul_of_nonneg_left hFδ
          (mul_nonneg hAmp0 (by linarith [SK_nonneg L]))
      have h2 : Amp L * (1 + SK L) * 2 ≤ 2 * Amp L + 2000 * C1 * x * Amp L ^ 3 := by
        have h3 : Amp L * (1 + SK L) * 2 = 2 * Amp L + 2 * (Amp L * SK L) := by ring
        rw [h3]
        have h4 : Amp L * SK L ≤ Amp L * (C1 * x * (1000 * Amp L ^ 2)) :=
          mul_le_mul_of_nonneg_left hSK hAmp0
        nlinarith [h4, hAmp0, hx0, hC1]
      have h5 : 2 * Amp L ≤ 2 * (C1 * x ^ N1) := mul_le_mul_of_nonneg_left hAmpLe (by norm_num)
      have h6 : Amp L ^ 3 ≤ C1 ^ 3 * x ^ (N1 * 3) := by
        have h1 : Amp L ^ 3 ≤ (C1 * x ^ N1) ^ 3 := pow_le_pow_left₀ hAmp0 hAmpLe 3
        rwa [mul_pow, rpow_nat_mul x hx0 N1 3] at h1
      have h7 : 2000 * C1 * x * Amp L ^ 3 ≤ 2000 * C1 ^ 4 * x ^ (3 * N1 + 1) := by
        have h8 : 2000 * C1 * x * Amp L ^ 3 ≤ 2000 * C1 * x * (C1 ^ 3 * x ^ (N1 * 3)) :=
          mul_le_mul_of_nonneg_left h6 (mul3_nonneg (by norm_num) hC1 hx0)
        refine le_trans h8 (le_of_eq ?_)
        have e1 : x * x ^ (N1 * 3) = x ^ (3 * N1 + 1) := by
          rw [show x * x ^ (N1 * 3) = x ^ (1 : ℝ) * x ^ (N1 * 3) from by rw [Real.rpow_one]]
          rw [← Real.rpow_add hxpos]
          congr 1
          ring
        rw [show 2000 * C1 * x * (C1 ^ 3 * x ^ (N1 * 3))
            = 2000 * C1 ^ 4 * (x * x ^ (N1 * 3)) from by ring]
        rw [e1]
      have h9 : 2 * (C1 * x ^ N1) ≤ 2 * C1 * x ^ MM := by
        have h10 : x ^ N1 ≤ x ^ MM := hmm3
        have h11 : (0 : ℝ) ≤ x ^ N1 := hxnn _
        have h12 : (0 : ℝ) ≤ x ^ MM := hxnn _
        nlinarith [h10, hC1, h11, h12]
      have h10 : 2000 * C1 ^ 4 * x ^ (3 * N1 + 1) ≤ 2000 * C1 ^ 4 * x ^ MM :=
        mul_le_mul_of_nonneg_left hmm4 (by positivity)
      have h12 : 2 * C1 + 2000 * C1 ^ 4 ≤ KK := by
        rw [hKK]
        have e1 : 2 * C1 ≤ 2 * (1 + C1) ^ 60 :=
          mul_le_mul_of_nonneg_left (C1_le_pow60 C1 hC1 hC1le) (by norm_num)
        have e2 : 2000 * C1 ^ 4 ≤ 2000 * (1 + C1) ^ 60 :=
          mul_le_mul_of_nonneg_left (pow_C1_le C1 hC1 hC1le 4 (by norm_num)) (by norm_num)
        nlinarith [e1, e2, hA0]
      calc Amp L * (1 + SK L) * Frob δ ≤ Amp L * (1 + SK L) * 2 := h1
        _ ≤ 2 * Amp L + 2000 * C1 * x * Amp L ^ 3 := h2
        _ ≤ 2 * (C1 * x ^ N1) + 2000 * C1 ^ 4 * x ^ (3 * N1 + 1) := add_le_add h5 h7
        _ ≤ 2 * C1 * x ^ MM + 2000 * C1 ^ 4 * x ^ MM := add_le_add h9 h10
        _ = (2 * C1 + 2000 * C1 ^ 4) * x ^ MM := by ring
        _ ≤ KK * x ^ MM := mul_le_mul_of_nonneg_right h12 (hxnn _)
  refine ⟨wordCarryFull L δ 0, ?_, ?_⟩
  · rw [wordCarryFull_spec L δ hδ 0, hγ]
  · exact CB_mono (wordCarryFull_bound L δ hδ 0) hCb hK

