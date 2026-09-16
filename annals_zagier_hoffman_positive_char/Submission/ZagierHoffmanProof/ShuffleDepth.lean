/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.ShuffleGen
import Submission.ZagierHoffmanProof.StepK3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open Polynomial RatFunc
open Filter
open scoped Topology BigOperators Pointwise

/-!
# The depth filtration of the MZV space

`𝒵 w` is the `K`-span of the MZVs of weight `w`; the product formula of `ShuffleGen` shows that the
*level-wise* product relations of the paper's Proposition 2.1 have outputs of depth at most the sum
of the depths (`P1Data.hbd`, `P3Data.hbd`).  Consequently the MZV space carries a **depth
filtration**, defined as the span of the MZVs of weight `w` and depth `≤ D`:

  `𝒵depth w D := span K (⋃_{r ≤ D} ζ_A_weight w r)`,

and the two structural facts hold:

* ★★ `zeta_mul_mem_Zdepth` : `ζ_A(a)·ζ_A(b) ∈ 𝒵depth (|a|+|b|) (depth a + depth b)`;
* ★★★ `Zdepth_mul_le` : `𝒵depth w D · 𝒵depth w' D' ≤ 𝒵depth (w+w') (D+D')`
  — `⨁_w 𝒵_w` is a **filtered graded algebra** for the depth filtration;
* ★★ `Zdepth_eq_Z (D ≥ w)` : `𝒵depth w D = 𝒵 w` — the filtration is exhaustive (an MZV of weight
  `w` can be written using MZVs of depth at most `w`), the trivial bound `depth ≤ weight`.

Everything is stated for an arbitrary finite field `F`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The MZVs of weight `w` and depth at most `D`, as a `K`-subspace of `K∞`. -/
noncomputable def 𝒵depth (w D : ℕ) : Submodule (RatFunc F) (RatFunc.CompletionAtInfty F) :=
  Submodule.span (RatFunc F) (⋃ r ∈ Finset.range (D + 1), ζ_A_weight F w r)

/-- The depth filtration is monotone in the depth bound. -/

lemma Zdepth_mono {w : ℕ} {D D' : ℕ} (h : D ≤ D') : 𝒵depth F w D ≤ 𝒵depth F w D' := by
  rw [𝒵depth, 𝒵depth]
  refine Submodule.span_mono ?_
  intro x hx
  rw [Set.mem_iUnion₂] at hx ⊢
  obtain ⟨r, hr, hxr⟩ := hx
  exact ⟨r, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hr) (Nat.succ_le_succ h)), hxr⟩

/-- The depth-`≤ D` subspace of weight `w` is contained in `𝒵 w`. -/

lemma Zdepth_le_Z (w D : ℕ) : 𝒵depth F w D ≤ 𝒵 F w := by
  rw [𝒵depth, 𝒵]
  refine Submodule.span_mono ?_
  exact Set.iUnion₂_subset fun r _ => Set.subset_iUnion (fun r => ζ_A_weight F w r) r

/-- The filtration is exhaustive: an MZV of weight `w` is a `K`-linear combination of MZVs of depth
at most `w`. -/
lemma Zdepth_eq_Z {w D : ℕ} (hD : w ≤ D) : 𝒵depth F w D = 𝒵 F w := by
  refine le_antisymm (Zdepth_le_Z F w D) ?_
  rw [𝒵depth, 𝒵]
  refine Submodule.span_mono ?_
  intro x hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨r, hxr⟩ := hx
  refine Set.mem_iUnion₂.mpr ⟨r, Finset.mem_range.mpr ?_, hxr⟩
  by_contra hcon
  rw [ζ_A_weight_eq_empty_of_lt F (show w < r by omega)] at hxr
  exact hxr

/-- ★★ An MZV of depth `r` lies in the depth-`≤ D` filtration for every `D ≥ r`. -/
lemma zeta_mem_Zdepth {r : ℕ} (𝔰 : Fin r → ℕ+) {w D : ℕ} (hw : weight r 𝔰 = w) (hD : r ≤ D) :
    ζ_A F 𝔰 ∈ 𝒵depth F w D := by
  refine Submodule.subset_span ?_
  refine Set.mem_iUnion₂.mpr ⟨r, Finset.mem_range.mpr (by omega), ?_⟩
  rw [ζ_A_weight_mem_iff F w r]
  exact ⟨𝔰, hw, rfl⟩

/-- ★★ **The product of two MZVs lies in the depth filtration**: the level-wise product relations
of Proposition 2.1 have outputs of depth at most `depth(a) + depth(b)`. -/
theorem zeta_mul_mem_Zdepth {r k : ℕ} (a : Fin r → ℕ+) (b : Fin k → ℕ+) :
    ζ_A F a * ζ_A F b ∈ 𝒵depth F (weight r a + weight k b) (r + k) := by
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0
    have h1 : ζ_A F a = 1 := zeta_A_fin_zero F a
    have hw0 : weight 0 a = 0 := by simp [weight]
    rw [h1, one_mul, hw0, Nat.zero_add]
    refine zeta_mem_Zdepth F b rfl (by omega)
  · rcases Nat.eq_zero_or_pos k with h0 | hk
    · subst h0
      have h1 : ζ_A F b = 1 := zeta_A_fin_zero F b
      have hw0 : weight 0 b = 0 := by simp [weight]
      rw [h1, mul_one, hw0, Nat.add_zero]
      refine zeta_mem_Zdepth F a rfl (by omega)
    · obtain ⟨D1⟩ := (p1p2_full_all F k hk r hr).1 hr hk a b
      obtain ⟨D3⟩ := p3_full_all F k hk r hr hr hk a b
      obtain ⟨D3'⟩ := p3_full_all F r hr k hk hk hr b a
      letI : Fintype D1.ι := D1.fin
      letI : Fintype D3.ι := D3.fin
      letI : Fintype D3'.ι := D3'.fin
      rw [zeta_mul_expand F hr hk a b D1 D3 D3']
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · refine Submodule.sum_mem _ (fun i _ => ?_)
        have hw : weight (D1.dep i) (D1.c i) = weight r a + weight k b := (D1.hle i).1
        have hsm : ((D1.f i : ℤ) : RatFunc.CompletionAtInfty F)
            = (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) ((D1.f i : ℤ) : RatFunc F) := by
          rw [map_intCast]
        rw [hsm, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _
          (zeta_mem_Zdepth F (D1.c i) hw (by have := D1.hbd i; omega))
      · refine Submodule.sum_mem _ (fun i _ => ?_)
        have hw : weight (D3.dep i) (D3.c i) = weight r a + weight k b := (D3.hle i).1
        have hsm : ((D3.f i : ℤ) : RatFunc.CompletionAtInfty F)
            = (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) ((D3.f i : ℤ) : RatFunc F) := by
          rw [map_intCast]
        rw [hsm, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _
          (zeta_mem_Zdepth F (D3.c i) hw (by have := D3.hbd i; omega))
      · refine Submodule.sum_mem _ (fun i _ => ?_)
        have hw : weight (D3'.dep i) (D3'.c i) = weight r a + weight k b :=
          ((D3'.hle i).1).trans (Nat.add_comm (weight k b) (weight r a))
        have hsm : ((D3'.f i : ℤ) : RatFunc.CompletionAtInfty F)
            = (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) ((D3'.f i : ℤ) : RatFunc F) := by
          rw [map_intCast]
        rw [hsm, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _
          (zeta_mem_Zdepth F (D3'.c i) hw (by have := D3'.hbd i; omega))

/-- ★★★ **The depth filtration is multiplicative**: the product of the weight-`w`, depth-`≤ D`
subspace and the weight-`w'`, depth-`≤ D'` subspace lies in the weight-`(w+w')`, depth-`≤ D+D'`
subspace.  Hence `⨁_w 𝒵_w` is a **filtered graded `K`-algebra** for the depth filtration. -/
theorem Zdepth_mul_le (w D w' D' : ℕ) :
    𝒵depth F w D * 𝒵depth F w' D' ≤ 𝒵depth F (w + w') (D + D') := by
  classical
  have hspan : 𝒵depth F w D * 𝒵depth F w' D' = Submodule.span (RatFunc F)
      ((⋃ r ∈ Finset.range (D + 1), ζ_A_weight F w r)
        * (⋃ r ∈ Finset.range (D' + 1), ζ_A_weight F w' r)) := by
    rw [𝒵depth, 𝒵depth, Submodule.span_mul_span]
  rw [hspan, Submodule.span_le]
  rintro z ⟨x, hx, y, hy, hxy⟩
  rw [← hxy]
  rw [Set.mem_iUnion₂] at hx hy
  obtain ⟨r, hr, hxr⟩ := hx
  obtain ⟨k, hk, hyk⟩ := hy
  rw [ζ_A_weight_mem_iff F w r] at hxr
  rw [ζ_A_weight_mem_iff F w' k] at hyk
  obtain ⟨𝔰, h𝔰w, hxζ⟩ := hxr
  obtain ⟨𝔱, h𝔱w, hyζ⟩ := hyk
  change x * y ∈ 𝒵depth F (w + w') (D + D')
  rw [hxζ, hyζ]
  have hsw : weight r 𝔰 = w := h𝔰w
  have htw : weight k 𝔱 = w' := h𝔱w
  have h := zeta_mul_mem_Zdepth F 𝔰 𝔱
  rw [hsw, htw] at h
  exact (Zdepth_mono F (w := w + w') (D := r + k) (D' := D + D')
    (by have := Finset.mem_range.mp hr; have := Finset.mem_range.mp hk; omega)) h

end ZagierHoffmanPositiveChar