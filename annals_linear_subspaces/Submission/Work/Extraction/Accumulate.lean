import Mathlib
import Submission.Work.Extraction.LevelBound
import Submission.Work.Extraction.SupplyBound
import Submission.Work.Lattice.Prop5Block

/-!
# Accumulating the §3 orthonormal family along the capacity sequence

The §3 extraction (de Saxcé, Prop. 5) builds an orthonormal family by *extending* the family of a
member by the supply of the next member whose capacity is larger.  The capacities are the running
maxima `ω s` of the supply counts; the supply at stage `s` (available when `ω (s-1) < ω s`) is an
orthonormal family of size `ω s` inside `W s` carrying `π₊`-mass at least `cStar d`.

Iterating `LevelBound.exists_dominated_extension_bound` along the stages produces

* an orthonormal family `e : Fin ℓ → ℝᵈ` whose `π₊`-mass is at least the explicit positive constant
  `floorSeq d ℓ N` (the `N`-fold iterate of the loss factor of the extension bound),
* a stage assignment `st : Fin ℓ → ℕ` with `e j ∈ W (st j)`, monotone, and compatible with the
  capacities (`ω (st j − 1) ≤ j < ω (st j)`), which is exactly what is needed to charge the
  norms of the lattice points against the accounting inequality.

Module `Submission.Work.Extraction.Accumulate`, namespace `Submission.Accumulate`.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Submission.Accumulate

open Submission.ExteriorCoordinates
open Submission.WedgeBlocks
open Submission.WedgeBlockZero
open Submission.Supply
open Submission.LevelBound
open Submission.Prop5Block

variable {d : ℕ}

/-- The explicit lower bound for the `π₊`-mass of the accumulated family: the `n`-fold iterate of
the loss factor of `exists_dominated_extension_bound`, applied with the maximal possible size
`ℓ` (the exponents use `2^ℓ`, `2^{ℓ+1}`). -/
noncomputable def floorSeq (d ℓ : ℕ) : ℕ → ℝ
  | 0 => cStar d
  | (n + 1) => (floorSeq d ℓ n) ^ ((2 : ℝ) ^ ℓ) *
      (((2 : ℝ) ^ (ℓ + 1)) ^ (-((2 : ℝ) ^ ℓ)))

lemma floorSeq_zero (d ℓ : ℕ) : floorSeq d ℓ 0 = cStar d := rfl

lemma floorSeq_succ (d ℓ n : ℕ) :
    floorSeq d ℓ (n + 1) = (floorSeq d ℓ n) ^ ((2 : ℝ) ^ ℓ) *
      (((2 : ℝ) ^ (ℓ + 1)) ^ (-((2 : ℝ) ^ ℓ))) :=
  rfl

lemma floorSeq_pos (d ℓ n : ℕ) : 0 < floorSeq d ℓ n := by
  induction n with
  | zero => simpa [floorSeq_zero] using cStar_pos d
  | succ n ih =>
      rw [floorSeq_succ]
      exact mul_pos (Real.rpow_pos_of_pos ih _) (Real.rpow_pos_of_pos (by positivity) _)

lemma floorSeq_le_one (d ℓ n : ℕ) : floorSeq d ℓ n ≤ 1 := by
  induction n with
  | zero =>
      rw [floorSeq_zero, cStar]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  | succ n ih =>
      rw [floorSeq_succ]
      have hC : (1 : ℝ) ≤ (2 : ℝ) ^ (ℓ + 1) := one_le_pow₀ (by norm_num)
      have h1 : (floorSeq d ℓ n) ^ ((2 : ℝ) ^ ℓ) ≤ 1 :=
        Real.rpow_le_one (le_of_lt (floorSeq_pos d ℓ n)) ih (by positivity)
      have h2 : ((2 : ℝ) ^ (ℓ + 1)) ^ (-((2 : ℝ) ^ ℓ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hC (neg_nonpos.mpr (by positivity))
      calc (floorSeq d ℓ n) ^ ((2 : ℝ) ^ ℓ) * ((2 : ℝ) ^ (ℓ + 1)) ^ (-((2 : ℝ) ^ ℓ))
          ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) (by norm_num)
        _ = 1 := by ring

lemma floorSeq_succ_le (d ℓ n : ℕ) : floorSeq d ℓ (n + 1) ≤ floorSeq d ℓ n := by
  rw [floorSeq_succ]
  have hC : (1 : ℝ) ≤ (2 : ℝ) ^ (ℓ + 1) := one_le_pow₀ (by norm_num)
  have hR : (1 : ℝ) ≤ (2 : ℝ) ^ ℓ := one_le_pow₀ (by norm_num)
  have hn := floorSeq_le_one d ℓ n
  have h1 : (floorSeq d ℓ n) ^ ((2 : ℝ) ^ ℓ) ≤ floorSeq d ℓ n := by
    simpa using Real.rpow_le_rpow_of_exponent_ge (floorSeq_pos d ℓ n) hn hR
  have h2 : ((2 : ℝ) ^ (ℓ + 1)) ^ (-((2 : ℝ) ^ ℓ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hC (neg_nonpos.mpr (by positivity))
  calc (floorSeq d ℓ n) ^ ((2 : ℝ) ^ ℓ) * ((2 : ℝ) ^ (ℓ + 1)) ^ (-((2 : ℝ) ^ ℓ))
      ≤ floorSeq d ℓ n * 1 :=
        mul_le_mul h1 h2 (by positivity) (le_of_lt (floorSeq_pos d ℓ n))
    _ = floorSeq d ℓ n := by ring

lemma floorSeq_le_cStar (d ℓ n : ℕ) : floorSeq d ℓ n ≤ cStar d := by
  induction n with
  | zero => rw [floorSeq_zero]
  | succ n ih => exact le_trans (floorSeq_succ_le d ℓ n) ih

/-- **The step comparison.**  One extension step of size `i ∈ [1, ℓ]` starting from a level `x`
which dominates `floorSeq d ℓ n` produces at least the level `floorSeq d ℓ (n+1)`. -/
lemma floorSeq_le_step {d ℓ n : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hx : floorSeq d ℓ n ≤ x) {i : ℕ} (hiℓ : i ≤ ℓ) :
    floorSeq d ℓ (n + 1) ≤ x ^ ((2 : ℝ) ^ i) *
      (((2 : ℝ) ^ (i + 1)) ^ (-((2 : ℝ) ^ i))) := by
  rw [floorSeq_succ]
  have hR' : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ ℓ := pow_le_pow_right₀ (by norm_num) hiℓ
  have hRn : (0 : ℝ) ≤ (2 : ℝ) ^ ℓ := by positivity
  have h1 : (floorSeq d ℓ n) ^ ((2 : ℝ) ^ ℓ) ≤ x ^ ((2 : ℝ) ^ i) := by
    refine le_trans (Real.rpow_le_rpow (le_of_lt (floorSeq_pos d ℓ n)) hx hRn) ?_
    exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hR'
  have h2 : ((2 : ℝ) ^ (ℓ + 1)) ^ (-((2 : ℝ) ^ ℓ)) ≤
      ((2 : ℝ) ^ (i + 1)) ^ (-((2 : ℝ) ^ i)) := by
    have hlog : ((2 : ℝ) ^ i) * Real.log ((2 : ℝ) ^ (i + 1)) ≤
        ((2 : ℝ) ^ ℓ) * Real.log ((2 : ℝ) ^ (ℓ + 1)) := by
      have hnat : (2 ^ i) * (i + 1) ≤ (2 ^ ℓ) * (ℓ + 1) := by
        have h1 : 2 ^ i ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hiℓ
        exact Nat.mul_le_mul h1 (by omega)
      rw [Real.log_pow, Real.log_pow]
      have : (((2 ^ i) * (i + 1) : ℕ) : ℝ) ≤ (((2 ^ ℓ) * (ℓ + 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      push_cast at this ⊢
      nlinarith [this, Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < (2:ℝ) ^ (ℓ + 1)),
      Real.rpow_def_of_pos (by positivity : (0:ℝ) < (2:ℝ) ^ (i + 1))]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hlog]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)


/-- Reindexing invariance of the exterior norm (a small local copy, to avoid importing the
Dani layer). -/
lemma norm_iMulti_cast {k l : ℕ} (h : k = l) (v : Fin k → RD d) :
    ‖exteriorPower.ιMulti ℝ l (fun i => v (Fin.cast h.symm i))‖ =
      ‖exteriorPower.ιMulti ℝ k v‖ := by
  subst h
  simp

/-- **The accumulation of the §3 orthonormal family.** -/
theorem exists_family_of_capacity {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {N : ℕ} (hN : N ≤ d)
    (ω : ℕ → ℕ) (hω0 : ω 0 = 0) (hωmono : Monotone ω) (hωN : ω N = ℓ)
    (W : ℕ → Submodule ℝ (RD d)) (hWmono : ∀ s s', s ≤ s' → W s ≤ W s')
    (hsup : ∀ s, 1 ≤ s → ω (s - 1) < ω s →
      ∃ a : Fin (ω s) → RD d, Orthonormal ℝ a ∧ (∀ k, a k ∈ W s) ∧
        cStar d ≤ ‖exteriorPower.map (ω s) (modelProj (d := d) ℓ)
          (exteriorPower.ιMulti ℝ (ω s) a)‖) :
    ∃ (e : Fin ℓ → RD d) (st : Fin ℓ → ℕ), Orthonormal ℝ e ∧
      (∀ j, e j ∈ W (st j)) ∧ Monotone st ∧ (∀ j, st j ≤ N) ∧
      (∀ j, ω (st j - 1) ≤ j.val ∧ j.val < ω (st j)) ∧
      floorSeq d ℓ N ≤ ‖exteriorPower.map ℓ (modelProj (d := d) ℓ)
        (exteriorPower.ιMulti ℝ ℓ e)‖ := by
  classical
  set P := modelProj (d := d) ℓ with hP
  have hPle : ∀ x, ‖P x‖ ≤ ‖x‖ := fun x => norm_modelProj_le ℓ x
  have hωle : ∀ s, s ≤ N → ω s ≤ ℓ := by
    intro s hs
    rw [← hωN]
    exact hωmono hs
  -- the first stage with positive capacity
  obtain ⟨σ, hσpos, hσmin⟩ : ∃ σ, 0 < ω σ ∧ ∀ s, s < σ → ω s = 0 := by
    let h : ∃ s, 0 < ω s := ⟨N, by rw [hωN]; exact hℓ0⟩
    refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
    intro s hs
    by_contra hne
    have hpos : 0 < ω s := Nat.pos_of_ne_zero hne
    have hle := Nat.find_min' h hpos
    omega
  have hσ1 : 1 ≤ σ := by
    by_contra h
    have h0 : σ = 0 := by omega
    rw [h0, hω0] at hσpos
    exact lt_irrefl 0 hσpos
  have hσpred : ω (σ - 1) = 0 := hσmin (σ - 1) (by omega)
  -- the invariant
  have hQ : ∀ s, σ ≤ s → s ≤ N → ∃ (e : Fin (ω s) → RD d) (stv : ℕ → ℕ),
      Orthonormal ℝ e ∧ (∀ j : Fin (ω s), e j ∈ W (stv j.val)) ∧ Monotone stv ∧
      (∀ j, j < ω s → ω (stv j - 1) ≤ j ∧ j < ω (stv j) ∧ stv j ≤ s) ∧
      floorSeq d ℓ s ≤ ‖exteriorPower.map (ω s) P (exteriorPower.ιMulti ℝ (ω s) e)‖ := by
    intro s hσs hsN
    induction s, hσs using Nat.le_induction with
    | base =>
        obtain ⟨a, haON, haW, hamass⟩ := hsup σ hσ1 (by rw [hσpred]; exact hσpos)
        refine ⟨a, fun _ => σ, haON, ?_, ?_, ?_, ?_⟩
        · intro j
          exact haW j
        · intro j j' _
          exact le_rfl
        · intro j hj
          exact ⟨by rw [hσpred]; exact Nat.zero_le j, hj, le_rfl⟩
        · exact le_trans (floorSeq_le_cStar d ℓ σ) hamass
    | succ s hσs ih =>
        have hsN' : s ≤ N := by omega
        obtain ⟨e, stv, heON, heW, hstvmono, hstvprop, hlev⟩ := ih hsN'
        by_cases hinc : ω s < ω (s + 1)
        · -- extend
          obtain ⟨u, huON, huW, humass⟩ := hsup (s + 1) (by omega) hinc
          have hm0 : 1 ≤ ω s := by
            have hpos : 0 < ω s := lt_of_lt_of_le hσpos (hωmono hσs)
            omega
          have hstvle : ∀ k : Fin (ω s), stv k.val ≤ s := fun k => (hstvprop k.val k.isLt).2.2
          have heW' : ∀ k : Fin (ω s), e k ∈ W (s + 1) :=
            fun k => hWmono (stv k.val) (s + 1) (le_trans (hstvle k) (Nat.le_succ s)) (heW k)
          obtain ⟨e', lev', hlev'pos, hlev'c, he'ON, he'W, he'ext, hstep', hdom'⟩ :=
            exists_dominated_extension_bound (d := d) (m := ω s) (i := ω (s + 1)) hinc hm0 P hPle
              heON heW' (floorSeq_pos d ℓ s) (floorSeq_le_cStar d ℓ s) hlev huON huW humass
          -- the level
          have hx0 : 0 < min (min (floorSeq d ℓ s) (cStar d)) 1 :=
            lt_min (lt_min (floorSeq_pos d ℓ s) (cStar_pos d)) one_pos
          have hx1 : min (min (floorSeq d ℓ s) (cStar d)) 1 ≤ 1 := min_le_right _ _
          have hx : floorSeq d ℓ s ≤ min (min (floorSeq d ℓ s) (cStar d)) 1 :=
            le_min (le_min le_rfl (floorSeq_le_cStar d ℓ s)) (floorSeq_le_one d ℓ s)
          have hstep := floorSeq_le_step (x := min (min (floorSeq d ℓ s) (cStar d)) 1)
            hx0 hx1 hx (i := ω (s + 1)) (hωle (s + 1) (by omega))
          refine ⟨e', fun j => if j < ω s then stv j else s + 1, he'ON, ?_, ?_, ?_,
            le_trans (le_trans hstep hstep') hdom'⟩
          · intro j
            by_cases hj : j.val < ω s
            · simp only [if_pos hj]
              have hcast : Fin.castLE (le_of_lt hinc) (⟨j.val, hj⟩ : Fin (ω s)) = j := Fin.ext rfl
              have : e' j = e ⟨j.val, hj⟩ := by
                have h1 := he'ext ⟨j.val, hj⟩
                rwa [hcast] at h1
              rw [this]
              exact heW ⟨j.val, hj⟩
            · simp only [if_neg hj]
              exact he'W j
          · intro j j' hjj'
            by_cases hj : j < ω s
            · by_cases hj' : j' < ω s
              · simp only [if_pos hj, if_pos hj']
                exact hstvmono hjj'
              · simp only [if_pos hj, if_neg hj']
                exact le_trans (hstvle ⟨j, hj⟩) (Nat.le_succ s)
            · by_cases hj' : j' < ω s
              · exfalso
                have h1 : ω s ≤ j := by omega
                omega
              · simp only [if_neg hj, if_neg hj']
                exact le_rfl
          · intro j hj
            by_cases hjs : j < ω s
            · simp only [if_pos hjs]
              exact ⟨(hstvprop j hjs).1, (hstvprop j hjs).2.1,
                le_trans (hstvprop j hjs).2.2 (Nat.le_succ s)⟩
            · simp only [if_neg hjs]
              refine ⟨?_, hj, le_rfl⟩
              rw [Nat.add_sub_cancel]
              omega
        · -- the capacity does not increase
          have heq : ω (s + 1) = ω s := by
            have h1 : ω s ≤ ω (s + 1) := hωmono (Nat.le_succ s)
            omega
          rw [heq]
          exact ⟨e, stv, heON, heW, hstvmono,
            fun j hj => ⟨(hstvprop j hj).1, (hstvprop j hj).2.1,
              le_trans (hstvprop j hj).2.2 (Nat.le_succ s)⟩,
            le_trans (floorSeq_succ_le d ℓ s) hlev⟩
  have hσle : σ ≤ N := by
    by_contra h
    have := hσmin N (by omega)
    rw [hωN] at this
    omega
  obtain ⟨e, stv, heON, heW, hstvmono, hstvprop, hlev⟩ := hQ N hσle le_rfl
  refine ⟨fun j => e (Fin.cast hωN.symm j), fun j => stv j.val, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact heON.comp (fun j : Fin ℓ => Fin.cast hωN.symm j) (Fin.cast_injective hωN.symm)
  · intro j
    have := heW (Fin.cast hωN.symm j)
    simpa using this
  · intro i j hij
    exact hstvmono hij
  · intro j
    exact (hstvprop j.val (by rw [hωN]; exact j.isLt)).2.2
  · intro j
    exact ⟨(hstvprop j.val (by rw [hωN]; exact j.isLt)).1,
      (hstvprop j.val (by rw [hωN]; exact j.isLt)).2.1⟩
  · have hnorm : ‖exteriorPower.map ℓ P (exteriorPower.ιMulti ℝ ℓ
          (fun j : Fin ℓ => e (Fin.cast hωN.symm j)))‖ =
        ‖exteriorPower.map (ω N) P (exteriorPower.ιMulti ℝ (ω N) e)‖ := by
      rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
      exact norm_iMulti_cast hωN (fun k => P (e k))
    rw [hnorm]
    exact hlev

end Submission.Accumulate

end
