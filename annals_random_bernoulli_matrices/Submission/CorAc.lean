import Mathlib
import Submission.Averaging
import Submission.Anticoncent
open scoped BigOperators
open Submission.IntFun
open Submission.Ell2Update
open Submission.Anticoncent
open Submission.Averaging
open Submission.Sec3Tower
open Submission.ProdCount
open Submission.Admissible
open Submission.PropRefineExport
open Submission.Sec3
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable

namespace Submission.CorAc

/-- Step 1 of cor: anticoncentration: instantiate `th: averaging` with the
kernel `f := fk (1/√n)`; returns its `L, η, n₀` and the count bound
`|{x ∈ ∏A : L/(N√n) < esup (lvl (fk(1/√n)) p n x)}| ≤ e^{-Mn}∏|A_j|`. -/
lemma corac_averaged {p : unitInterval} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁₂ : δ ≤ 1 / 2)
    {ε : ℝ} (hε₀ : 0 < ε) (hεp : ε < (p : ℝ)) :
    ∃ (L : ℝ), 0 < L ∧
      ∀ (M : ℝ) (hM : 1 ≤ M), ∃ (η : ℝ) (n₀ : ℕ), 0 < η ∧ 1 ≤ n₀ ∧
      ∀ (n : ℕ) (hn₀ : n₀ ≤ n), ∀ (N : ℕ) (hN1 : 1 ≤ N),
        (N : ℝ) ≤ (1 / (1 - (p : ℝ) + ε)) ^ n →
        ∀ (A : Fin n → Finset ℤ)
          (hAdm : Admissible N n n δ A)
          (hrad : ∀ j : Fin n, ∀ a : ℤ, a ∈ A j → |a| ≤ ((n * N : ℕ) : ℤ))
          (hsym : ∀ j : Fin n, ∀ a : ℤ, a ∈ A j → -a ∈ A j),
          ((((prodFinset n A).filter (fun x : Fin n → ℤ =>
            L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
              esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x))).card : ℕ) : ℝ) ≤
            Real.exp (-M * (n : ℝ)) * (∏ j : Fin n, (((A j).card : ℕ) : ℝ)) := by
  classical
  rcases averaging (p := p) hp₀ hp₁ (δ := δ) hδ₀ hδ₁₂ (ε := ε) hε₀ hεp with ⟨L, hL, hUnif⟩
  refine ⟨L, hL, ?_⟩
  intro M hM
  rcases hUnif M hM with ⟨η, n₀, hη, hn₀1, hBody⟩
  let n₀' : ℕ := max n₀ (Nat.ceil (1 / η ^ 2))
  refine ⟨η, n₀', hη, ?_, ?_⟩
  · dsimp [n₀']
    have h1 : (1 : ℕ) ≤ n₀ := hn₀1
    omega
  · intro n hn₀' N hN1 hNa A hAdm hrad hsym
    have hn₀ : n₀ ≤ n := by
      exact le_trans (le_max_left n₀ (Nat.ceil (1 / η ^ 2))) hn₀'
    have hceil : Nat.ceil (1 / η ^ 2) ≤ n := by
      exact le_trans (le_max_right n₀ (Nat.ceil (1 / η ^ 2))) hn₀'
    have hηR : 1 / η ^ 2 ≤ (n : ℝ) := eta_real_of_ceil hceil
    have hn1 : 1 ≤ n := by
      have h : (1 : ℕ) ≤ n₀ := hn₀1
      omega
    have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn1)
    have hr : 0 < 1 / Real.sqrt (n : ℝ) := by positivity
    have hlip : Ell2Update.ratioLip η (fk (1 / Real.sqrt (n : ℝ))) := ratioLip_fk_of_eta hη hηR
    have hfpos : ∀ t : ℤ, 0 ≤ fk (1 / Real.sqrt (n : ℝ)) t := fk_nonneg hr
    have hf2 : Summable (fun t : ℤ => (fk (1 / Real.sqrt (n : ℝ)) t) ^ 2) := summable_fk_sq hr
    have hfsum : Summable (fk (1 / Real.sqrt (n : ℝ))) := summable_fk hr
    have hfmass : norm₁ (fk (1 / Real.sqrt (n : ℝ))) ≤ 1 := by
      rw [norm₁_fk hr]
    exact hBody n hn₀ N hN1 hNa A hAdm hrad hsym (f := fk (1 / Real.sqrt (n : ℝ)))
      hfpos hf2 hfsum hfmass hlip


/-! ## Step 2 (first link): lowering the level function at a fixed `t`

`lvl f p n x t` is (by definition) the subset-sum expectation
`Σ_B wB(n,p,B)·f(t + Σ_{j∈B} xⱼ)`.  Combined with the interval lower bound of
the kernel (`fk (1/√n) ≥ (ln2/16)/√n` on `|·| ≤ √n+1`), each good subset term
is at least `((ln2/16)/√n)·wB`, so the level value at `t` is at least that
constant times the total Bernoulli weight of the good subsets
`G_t(x) := {B : |t + Σ_{j∈B} xⱼ| ≤ √n+1}`. -/

/-- fixed-`t` lower bound of the kernel's level function by the good-subset
weight. -/
lemma lvl_fk_lower {n : ℕ} (hn : 1 ≤ n) (p : unitInterval)
    (x : Fin n → ℤ) (t : ℤ) :
    (Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ) *
        (∑ B ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
            (fun B => (|t + Sec3.subSum x B| : ℝ) ≤ Real.sqrt (n : ℝ) + 1)),
          Sec3.wB n p B)
      ≤ lvl (fk (1 / Real.sqrt (n : ℝ))) p n x t := by
  classical
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hr : 0 < 1 / Real.sqrt (n : ℝ) := by positivity
  have hfpos : ∀ u : ℤ, 0 ≤ fk (1 / Real.sqrt (n : ℝ)) u := fk_nonneg hr
  have hgood : ∀ (B : Finset (Fin n)),
      (|t + Sec3.subSum x B| : ℝ) ≤ Real.sqrt (n : ℝ) + 1 →
      (Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ) ≤ fk (1 / Real.sqrt (n : ℝ)) (t + Sec3.subSum x B) := by
    intro B hB
    have hB' : (|(t + Sec3.subSum x B : ℤ)| : ℝ) ≤ Real.sqrt (n : ℝ) + 1 := by
      simpa [Int.cast_add] using hB
    exact fk_lower_bound_on_interval hn hB'
  change (Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ) *
      (∑ B ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
          (fun B => (|t + Sec3.subSum x B| : ℝ) ≤ Real.sqrt (n : ℝ) + 1)),
        Sec3.wB n p B) ≤ avgF (fk (1 / Real.sqrt (n : ℝ))) p n x t
  exact Sec3.avgF_lower_subsetSum (f := fk (1 / Real.sqrt (n : ℝ))) (p := p) (ℓ := n)
    (x := x) (t := t) (a := (Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ))
    (A := Real.sqrt (n : ℝ) + 1) hfpos hgood



/-! ## Step 2 (second link): `sup_t`-upgrade to the `esup` level

`lvl_fk_lower` bounds the level value at each fixed `t`.  Since
`esup g = sSup (Set.range g)`, a pointwise bound `a·W(t) ≤ g(t)` upgrades to
`a·sSup(range W) ≤ esup g` (provided the ranges are bounded above and `a > 0`).
Applied with `g := lvl (fk (1/√n)) p n x` and `W(t)` the good-subset weight at
center `t`, this yields `esup ≥ ((ln2/16)/√n)·sup_t W(t)`. -/

/-- generic `sup_t`-upgrade: pointwise `a·W(t) ≤ g(t)` forces
`a·sSup(range W) ≤ sSup(range g)` (ranges bounded above, `a > 0`). -/
lemma esup_mul_sSup_of_le {g W : ℤ → ℝ} {a : ℝ} (ha : 0 < a)
    (hWbdd : BddAbove (Set.range W)) (hgbdd : BddAbove (Set.range g))
    (hle : ∀ t : ℤ, a * W t ≤ g t) :
    a * sSup (Set.range W) ≤ sSup (Set.range g) := by
  let Sg : ℝ := sSup (Set.range g)
  have hgt : ∀ t : ℤ, g t ≤ Sg := by
    intro t
    dsimp [Sg]
    exact le_csSup hgbdd ⟨t, rfl⟩
  have hstep : ∀ t : ℤ, W t ≤ Sg / a := by
    intro t
    have h1 : a * W t ≤ Sg := le_trans (hle t) (hgt t)
    have h1' : W t * a ≤ Sg := by simpa [mul_comm] using h1
    exact (le_div_iff₀ ha).mpr h1'
  have hSW : sSup (Set.range W) ≤ Sg / a := by
    exact csSup_le ⟨W 0, ⟨0, rfl⟩⟩ (by intro y hy; rcases hy with ⟨t, rfl⟩; exact hstep t)
  calc
    a * sSup (Set.range W) ≤ a * (Sg / a) := mul_le_mul_of_nonneg_left hSW ha.le
    _ = Sg := by field_simp [ne_of_gt ha]
    _ = sSup (Set.range g) := by dsimp [Sg]

/-- the level function of the kernel is bounded above by `1 = ‖fk(1/√n)‖₁`. -/
lemma lvl_fk_bdd {n : ℕ} (hn : 1 ≤ n) (p : unitInterval) (x : Fin n → ℤ) :
    BddAbove (Set.range (fun t : ℤ => lvl (fk (1 / Real.sqrt (n : ℝ))) p n x t)) := by
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hr : 0 < 1 / Real.sqrt (n : ℝ) := by positivity
  have hb : ∀ t : ℤ, lvl (fk (1 / Real.sqrt (n : ℝ))) p n x t ≤ 1 := by
    intro t
    calc
      lvl (fk (1 / Real.sqrt (n : ℝ))) p n x t
          = avgF (fk (1 / Real.sqrt (n : ℝ))) p n x t := rfl
      _ ≤ norm₁ (fk (1 / Real.sqrt (n : ℝ))) := avgF_le_norm₁ (fk_nonneg hr) (summable_fk hr) n x t
      _ = 1 := norm₁_fk hr
  refine ⟨1, ?_⟩
  intro y hy
  rcases hy with ⟨t, rfl⟩
  exact hb t

/-- the good-subset weight function is bounded above by the total weight `1`. -/
lemma good_weight_bdd {n : ℕ} {p : unitInterval} {x : Fin n → ℤ} {A : ℝ} :
    BddAbove (Set.range (fun t : ℤ =>
      ∑ B ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
        (fun B => (|t + Sec3.subSum x B| : ℝ) ≤ A)), Sec3.wB n p B)) := by
  refine ⟨1, ?_⟩
  intro y hy
  rcases hy with ⟨t, rfl⟩
  have hsub : ((Finset.univ : Finset (Fin n)).powerset.filter
        (fun B => (|t + Sec3.subSum x B| : ℝ) ≤ A))
      ⊆ (Finset.univ : Finset (Fin n)).powerset := by
    intro B hB
    exact (Finset.mem_filter.mp hB).1
  have hpos : ∀ B : Finset (Fin n), B ∈ (Finset.univ : Finset (Fin n)).powerset →
      B ∉ (Finset.univ : Finset (Fin n)).powerset.filter (fun B => (|t + Sec3.subSum x B| : ℝ) ≤ A) →
      0 ≤ wB n p B := by
    intro B hB hnot
    exact wB_nonneg n p B
  have hle : (∑ B ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
        (fun B => (|t + Sec3.subSum x B| : ℝ) ≤ A)), wB n p B) ≤
      (∑ B ∈ (Finset.univ : Finset (Fin n)).powerset, wB n p B) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub hpos
  have hw : (∑ B ∈ (Finset.univ : Finset (Fin n)).powerset, wB n p B) = 1 := Sec3.sum_wB_eq_one n p
  rwa [hw] at hle

/-- **`sup_t`-upgrade of `lvl_fk_lower`**: the level-supremum is at least
`((ln2/16)/√n)` times the supremum over integer centers of the good-subset
Bernoulli weight. -/
lemma lvl_fk_sup_lower {n : ℕ} (hn : 1 ≤ n) (p : unitInterval) (x : Fin n → ℤ) :
    (Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ) *
        sSup (Set.range (fun t : ℤ =>
          ∑ B ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
            (fun B => (|t + Sec3.subSum x B| : ℝ) ≤ Real.sqrt (n : ℝ) + 1)), Sec3.wB n p B))
      ≤ esup (lvl (fk (1 / Real.sqrt (n : ℝ))) p n x) := by
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have ha : 0 < (Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ) := by positivity
  let W : ℤ → ℝ := fun t =>
      ∑ B ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
        (fun B => (|t + Sec3.subSum x B| : ℝ) ≤ Real.sqrt (n : ℝ) + 1)), Sec3.wB n p B
  let g : ℤ → ℝ := fun t => lvl (fk (1 / Real.sqrt (n : ℝ))) p n x t
  have hle : ∀ t : ℤ, ((Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ)) * W t ≤ g t := by
    intro t
    dsimp [W, g]
    exact lvl_fk_lower hn p x t
  have hWbdd : BddAbove (Set.range W) := good_weight_bdd (x := x) (A := Real.sqrt (n : ℝ) + 1)
  have hgbdd : BddAbove (Set.range g) := lvl_fk_bdd hn p x
  have hmain := esup_mul_sSup_of_le (g := g) (W := W)
    (a := (Real.log (2 : ℝ) / 16) / Real.sqrt (n : ℝ)) ha hWbdd hgbdd hle
  dsimp [W, g] at hmain ⊢
  simpa [esup] using hmain



/-! ## Step 2 (third link): integer-center rounding (`sup_t` ≥ real-center `cf`)

`GoodWeight(t) = Σ_{B: |t + Σ_{j∈B} xⱼ| ≤ A} wB(n,p,B)` is the Bernoulli
probability that `|t + Σ b·x| ≤ A`.  The concentration `cf(Σb·x, R)` is the
supremum over *real* centers of `P(|Σb·x − λ| ≤ R)`, i.e. (in weight terms)
`sSup_λ Σ_{B: |Σ_{j∈B} xⱼ − λ| ≤ R} wB`.  Rounding the real center `λ` to an
integer `t` at distance `≤ 1/2` (`exists_int_abs_le_half`), the triangle
inequality pushes `{|Σ−λ| ≤ R} ⊆ {|t+Σ| ≤ R + 1/2} ⊆ {|t+Σ| ≤ A}` once
`R + 1/2 ≤ A`, and the weight sum is monotone in the subset family. -/

/-- every real `lam` is within `1/2` of an integer `t` (with the sign used here:
`|lam + t| ≤ 1/2`, i.e. `t ≈ -lam`). -/
lemma exists_int_abs_le_half (lam : ℝ) : ∃ t : ℤ, |lam + (t : ℝ)| ≤ 1 / 2 := by
  let m : ℤ := Int.floor (lam + 1 / 2)
  refine ⟨-m, ?_⟩
  have h1 : ((m : ℤ) : ℝ) ≤ lam + 1 / 2 := Int.floor_le (lam + 1 / 2)
  have h2 : lam + 1 / 2 < ((m : ℤ) : ℝ) + 1 := Int.lt_floor_add_one (lam + 1 / 2)
  have hlb : -(1 / 2) ≤ lam - (m : ℝ) := by linarith
  have hub : lam - (m : ℝ) ≤ 1 / 2 := by linarith
  have h : |lam - (m : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨hlb, hub⟩
  rw [Int.cast_neg]
  exact h

/-- **rounding**: the real-center weight supremum (radius `R`) is at most the
integer-center window-weight supremum (radius `A`), provided `R + 1/2 ≤ A`. -/
lemma weight_sup_real_le_int {n : ℕ} {p : unitInterval} (x : Fin n → ℤ) {R A : ℝ}
    (hRA : R + 1 / 2 ≤ A) :
    sSup (Set.range (fun lam : ℝ =>
        ∑ B ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
          (fun B => |(Sec3.subSum x B : ℝ) - lam| ≤ R)), Sec3.wB n p B))
      ≤ sSup (Set.range (fun t : ℤ =>
        ∑ B ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
          (fun B => (|t + Sec3.subSum x B| : ℝ) ≤ A)), Sec3.wB n p B)) := by
  classical
  let Wt : ℤ → ℝ := fun t =>
      ∑ B ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
        (fun B => (|t + Sec3.subSum x B| : ℝ) ≤ A)), Sec3.wB n p B
  let Wr : ℝ → ℝ := fun lam =>
      ∑ B ∈ ((Finset.univ : Finset (Fin n)).powerset.filter
        (fun B => |(Sec3.subSum x B : ℝ) - lam| ≤ R)), Sec3.wB n p B
  have hWbdd : BddAbove (Set.range Wt) := good_weight_bdd (x := x) (A := A)
  have hbound : ∀ lam : ℝ, Wr lam ≤ sSup (Set.range Wt) := by
    intro lam
    rcases exists_int_abs_le_half lam with ⟨t, ht2⟩
    have hincl : ((Finset.univ : Finset (Fin n)).powerset.filter
          (fun B => |(Sec3.subSum x B : ℝ) - lam| ≤ R))
        ⊆ ((Finset.univ : Finset (Fin n)).powerset.filter
          (fun B => (|t + Sec3.subSum x B| : ℝ) ≤ A)) := by
      intro B hB
      rw [Finset.mem_filter] at hB ⊢
      refine ⟨hB.1, ?_⟩
      have hsB : |(Sec3.subSum x B : ℝ) - lam| ≤ R := hB.2
      have htri : |(Sec3.subSum x B : ℝ) + (t : ℝ)| ≤ R + 1 / 2 := by
        have hstep := abs_add_le ((Sec3.subSum x B : ℝ) - lam) (lam + (t : ℝ))
        have harg : ((Sec3.subSum x B : ℝ) - lam) + (lam + (t : ℝ)) = (Sec3.subSum x B : ℝ) + (t : ℝ) := by ring
        have htri' : |(Sec3.subSum x B : ℝ) + (t : ℝ)| ≤ |(Sec3.subSum x B : ℝ) - lam| + |lam + (t : ℝ)| := by
          rwa [harg] at hstep
        have hadd : |(Sec3.subSum x B : ℝ) - lam| + |lam + (t : ℝ)| ≤ R + 1 / 2 := by
          have h1 : |(Sec3.subSum x B : ℝ) - lam| ≤ R := hsB
          have h2 : |lam + (t : ℝ)| ≤ 1 / 2 := ht2
          linarith
        exact le_trans htri' hadd
      have hcast : (|t + Sec3.subSum x B| : ℝ) = |(Sec3.subSum x B : ℝ) + (t : ℝ)| := by
        congr 1
        ring
      rw [hcast]
      linarith [htri, hRA]
    have hwle : Wr lam ≤ Wt t := by
      dsimp [Wr, Wt]
      exact Finset.sum_le_sum_of_subset_of_nonneg hincl
        (by intro B hB hnot; exact wB_nonneg n p B)
    have hle_sup : Wt t ≤ sSup (Set.range Wt) := by
      exact le_csSup hWbdd ⟨t, rfl⟩
    exact le_trans hwle hle_sup
  exact csSup_le ⟨Wr 0, ⟨0, rfl⟩⟩ (by
    intro y hy
    rcases hy with ⟨lam, rfl⟩
    exact hbound lam)


end Submission.CorAc
