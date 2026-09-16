/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.StepK3
import Submission.ZagierHoffmanProof.ZetaShuffle
import Submission.Commons.Topology.InfiniteSum.fin_sum_tsum
import Submission.Commons.Topology.InfiniteSum.summable_fin_sum
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open Polynomial RatFunc
open Filter
open Commons.Topology.InfiniteSum
open scoped Topology BigOperators Pointwise

/-!
# The product of two MZVs against the level decomposition: the graded-algebra structure

`ZetaShuffle.lean` proved the shuffle relation for two *depth-one* MZVs by splitting the product
of the two level series along the degree trichotomy (`box_identity`) and passing to the limit.
This module does the same for **arbitrary depths**, using the level-wise product relations of the
paper's Proposition 2.1 (`P1Data` for the diagonal `S_d(a)·S_d(b)`, `P3Data` for the two mixed
products `S_<d(a)·S_d(b)` and `S_<d(b)·S_d(a)`):

  ★★★ `zeta_mul_expand` : for tuples `a`, `b` of depths `r, k ≥ 1` and witnesses
      `D1 : P1Data a b`, `D3 : P3Data a b`, `D3' : P3Data b a`,

        `ζ_A(a)·ζ_A(b) = Σ_i D1.f i · ζ_A(D1.c i) + Σ_i D3.f i · ζ_A(D3.c i)
                          + Σ_i D3'.f i · ζ_A(D3'.c i)`.

  ★★ `zeta_mul_mem_Z` : `ζ_A(a)·ζ_A(b) ∈ 𝒵 (weight a + weight b)`.

  ★★★ `Z_mul_Z_le` : `𝒵 w * 𝒵 w' ≤ 𝒵 (w + w')` — **`⨁_w 𝒵_w` is a graded algebra**.

Everything is stated for an arbitrary finite field `F`.
-/

namespace ZagierHoffmanPositiveChar

/-- **The generic finite box identity.**  For any two sequences `f g : ℕ → R` with values in a
commutative semiring and any `N`, the product of the two truncations splits into the three
degree-regions `e < d`, `d < e` and `d = e`. -/
lemma box_gen {R : Type*} [CommSemiring R] (f g : ℕ → R) (N : ℕ) :
    (∑ d ∈ Finset.range N, f d) * (∑ e ∈ Finset.range N, g e)
      = (∑ d ∈ Finset.range N, f d * ∑ e ∈ Finset.range d, g e)
        + (∑ e ∈ Finset.range N, g e * ∑ d ∈ Finset.range e, f d)
        + (∑ d ∈ Finset.range N, f d * g d) := by
  have hpt : ∀ d : ℕ, d < N → f d * (∑ e ∈ Finset.range N, g e)
      = (f d * ∑ e ∈ Finset.range d, g e) + f d * g d
        + f d * (∑ e ∈ Finset.Ico (d + 1) N, g e) := by
    intro d hd
    rw [← mul_add, ← mul_add]
    congr 1
    have h1 := Finset.sum_range_add_sum_Ico (fun e : ℕ => g e) (show d + 1 ≤ N by omega)
    rw [Finset.sum_range_succ] at h1
    exact h1.symm
  have hind1 : ∀ d : ℕ, (∑ e ∈ Finset.range N, if d < e then g e else 0)
      = ∑ e ∈ Finset.Ico (d + 1) N, g e := by
    intro d
    rw [← Finset.sum_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have hind2 : ∀ e : ℕ, e ≤ N → (∑ d ∈ Finset.range N, if d < e then f d else 0)
      = ∑ d ∈ Finset.range e, f d := by
    intro e he
    rw [← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hswap : (∑ d ∈ Finset.range N, f d * ∑ e ∈ Finset.Ico (d + 1) N, g e)
      = ∑ e ∈ Finset.range N, g e * ∑ d ∈ Finset.range e, f d := by
    have h1 : (∑ d ∈ Finset.range N, f d * ∑ e ∈ Finset.Ico (d + 1) N, g e)
        = ∑ d ∈ Finset.range N, ∑ e ∈ Finset.range N,
            (if d < e then f d * g e else 0) := by
      refine Finset.sum_congr rfl ?_
      intro d _
      rw [← hind1 d, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro e _
      by_cases h : d < e
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, mul_zero]
    have h2 : (∑ e ∈ Finset.range N, g e * ∑ d ∈ Finset.range e, f d)
        = ∑ e ∈ Finset.range N, ∑ d ∈ Finset.range N,
            (if d < e then f d * g e else 0) := by
      refine Finset.sum_congr rfl ?_
      intro e he
      rw [← hind2 e (Finset.mem_range.mp he).le, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro d _
      by_cases h : d < e
      · rw [if_pos h, if_pos h, mul_comm]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [h1, h2, Finset.sum_comm]
  rw [Finset.sum_mul,
    Finset.sum_congr rfl (fun d hd => hpt d (Finset.mem_range.mp hd)),
    Finset.sum_add_distrib, Finset.sum_add_distrib, hswap]
  ring

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The partial sums of a level-wise finite `K`-combination of power sums converge to the
corresponding `K`-combination of MZVs. -/
private lemma tendsto_level_combo {ι : Type} [Fintype ι]
    (f : ι → ℤ) (dep : ι → ℕ) (hdep : ∀ i, 0 < dep i) (c : ∀ i, Fin (dep i) → ℕ+) :
    Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.range N, ∑ i : ι,
        ((f i : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep i) (hdep i) (c i) d) Filter.atTop
      (𝓝 (∑ i : ι, ((f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (c i))) := by
  have hg : ∀ i : ι, Summable (fun d : ℕ =>
      ((f i : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep i) (hdep i) (c i) d) :=
    fun i => (summable_S F (hdep i) (c i)).mul_left _
  have hsum : Summable (fun d : ℕ => ∑ i : ι,
      ((f i : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep i) (hdep i) (c i) d) :=
    summable_fin_sum _ hg
  have hlim := hsum.hasSum.tendsto_sum_nat
  rw [← fin_sum_tsum (fun (i : ι) (d : ℕ) =>
      ((f i : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep i) (hdep i) (c i) d) hg] at hlim
  have htarget : (∑ i : ι, ∑' d : ℕ,
        ((f i : ℤ) : RatFunc.CompletionAtInfty F) * S F (dep i) (hdep i) (c i) d)
      = ∑ i : ι, ((f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (c i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [tsum_mul_left, ← zeta_eq_tsum_block F (hdep i) (c i)]
  rw [htarget] at hlim
  exact hlim

/-- ★★★ **The product formula for two MZVs.**  Given level-wise witnesses of the paper's
Proposition 2.1 — `D1` for the diagonal products `S_d(a)·S_d(b)`, `D3` for the mixed products
`S_<d(a)·S_d(b)` and `D3'` for `S_<d(b)·S_d(a)` — the product of the two MZVs expands as the
corresponding `K`-linear combination of MZVs:

  `ζ_A(a)·ζ_A(b) = Σ_i D1.f i·ζ_A(D1.c i) + Σ_i D3.f i·ζ_A(D3.c i) + Σ_i D3'.f i·ζ_A(D3'.c i)`.

Proof: split the product of the two truncated level series by the degree trichotomy
(`box_gen`), rewrite each of the three regions level-wise by `D1.hid`/`D3.hid`/`D3'.hid`, and
pass to the limit `N → ∞` (`tendsto_nhds_unique`). -/
theorem zeta_mul_expand {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (a : Fin r → ℕ+) (b : Fin k → ℕ+)
    (D1 : P1Data F r k hr hk a b) (D3 : P3Data F r k hr hk a b)
    (D3' : P3Data F k r hk hr b a) :
    letI : Fintype D1.ι := D1.fin
    letI : Fintype D3.ι := D3.fin
    letI : Fintype D3'.ι := D3'.fin
    ζ_A F a * ζ_A F b =
      (∑ i : D1.ι, ((D1.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D1.c i))
        + (∑ i : D3.ι, ((D3.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D3.c i))
        + (∑ i : D3'.ι, ((D3'.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D3'.c i)) := by
  letI : Fintype D1.ι := D1.fin
  letI : Fintype D3.ι := D3.fin
  letI : Fintype D3'.ι := D3'.fin
  have hfa : Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.range N, S F r hr a d) Filter.atTop
      (𝓝 (ζ_A F a)) := by
    rw [zeta_eq_tsum_block F hr a]
    exact (summable_S F hr a).hasSum.tendsto_sum_nat
  have hfb : Filter.Tendsto (fun N : ℕ => ∑ e ∈ Finset.range N, S F k hk b e) Filter.atTop
      (𝓝 (ζ_A F b)) := by
    rw [zeta_eq_tsum_block F hk b]
    exact (summable_S F hk b).hasSum.tendsto_sum_nat
  have hptD : ∀ d : ℕ, S F r hr a d * S F k hk b d
      = ∑ i : D1.ι, ((D1.f i : ℤ) : RatFunc.CompletionAtInfty F) *
          S F (D1.dep i) (D1.hdep i) (D1.c i) d := fun d => D1.hid d
  have hptA : ∀ d : ℕ, S F r hr a d * ∑ e ∈ Finset.range d, S F k hk b e
      = ∑ i : D3'.ι, ((D3'.f i : ℤ) : RatFunc.CompletionAtInfty F) *
          S F (D3'.dep i) (D3'.hdep i) (D3'.c i) d := by
    intro d
    calc S F r hr a d * ∑ e ∈ Finset.range d, S F k hk b e
        = S F r hr a d * S_lt F k hk b d := by rw [S_lt_eq_sum_levels F k hk b d]
      _ = S_lt F k hk b d * S F r hr a d := by rw [mul_comm]
      _ = ∑ i : D3'.ι, ((D3'.f i : ℤ) : RatFunc.CompletionAtInfty F) *
            S F (D3'.dep i) (D3'.hdep i) (D3'.c i) d := D3'.hid d
  have hptB : ∀ e : ℕ, S F k hk b e * ∑ d ∈ Finset.range e, S F r hr a d
      = ∑ i : D3.ι, ((D3.f i : ℤ) : RatFunc.CompletionAtInfty F) *
          S F (D3.dep i) (D3.hdep i) (D3.c i) e := by
    intro e
    calc S F k hk b e * ∑ d ∈ Finset.range e, S F r hr a d
        = S F k hk b e * S_lt F r hr a e := by rw [S_lt_eq_sum_levels F r hr a e]
      _ = S_lt F r hr a e * S F k hk b e := by rw [mul_comm]
      _ = ∑ i : D3.ι, ((D3.f i : ℤ) : RatFunc.CompletionAtInfty F) *
            S F (D3.dep i) (D3.hdep i) (D3.c i) e := D3.hid e
  have hD : Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.range N, S F r hr a d * S F k hk b d)
      Filter.atTop (𝓝 (∑ i : D1.ι,
        ((D1.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D1.c i))) := by
    have h := tendsto_level_combo F D1.f D1.dep D1.hdep D1.c
    refine h.congr' (Eventually.of_forall (fun N => ?_))
    exact Finset.sum_congr rfl (fun d _ => (hptD d).symm)
  have hA : Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.range N,
        S F r hr a d * ∑ e ∈ Finset.range d, S F k hk b e) Filter.atTop
      (𝓝 (∑ i : D3'.ι,
        ((D3'.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D3'.c i))) := by
    have h := tendsto_level_combo F D3'.f D3'.dep D3'.hdep D3'.c
    refine h.congr' (Eventually.of_forall (fun N => ?_))
    exact Finset.sum_congr rfl (fun d _ => (hptA d).symm)
  have hB : Filter.Tendsto (fun N : ℕ => ∑ e ∈ Finset.range N,
        S F k hk b e * ∑ d ∈ Finset.range e, S F r hr a d) Filter.atTop
      (𝓝 (∑ i : D3.ι,
        ((D3.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D3.c i))) := by
    have h := tendsto_level_combo F D3.f D3.dep D3.hdep D3.c
    refine h.congr' (Eventually.of_forall (fun N => ?_))
    exact Finset.sum_congr rfl (fun e _ => (hptB e).symm)
  have hL : Filter.Tendsto (fun N : ℕ =>
        (∑ d ∈ Finset.range N, S F r hr a d) * (∑ e ∈ Finset.range N, S F k hk b e))
      Filter.atTop (𝓝 (ζ_A F a * ζ_A F b)) := hfa.mul hfb
  have htarget : (∑ i : D3'.ι,
        ((D3'.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D3'.c i))
      + (∑ i : D3.ι, ((D3.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D3.c i))
      + (∑ i : D1.ι, ((D1.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D1.c i))
      = (∑ i : D1.ι, ((D1.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D1.c i))
      + (∑ i : D3.ι, ((D3.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D3.c i))
      + (∑ i : D3'.ι, ((D3'.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D3'.c i)) := by
    ring
  have hR : Filter.Tendsto (fun N : ℕ =>
        (∑ d ∈ Finset.range N, S F r hr a d * ∑ e ∈ Finset.range d, S F k hk b e)
        + (∑ e ∈ Finset.range N, S F k hk b e * ∑ d ∈ Finset.range e, S F r hr a d)
        + (∑ d ∈ Finset.range N, S F r hr a d * S F k hk b d)) Filter.atTop
      (𝓝 ((∑ i : D1.ι, ((D1.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D1.c i))
        + (∑ i : D3.ι, ((D3.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D3.c i))
        + (∑ i : D3'.ι, ((D3'.f i : ℤ) : RatFunc.CompletionAtInfty F) * ζ_A F (D3'.c i)))) := by
    rw [← htarget]
    exact (hA.add hB).add hD
  have hEq : (fun N : ℕ =>
        (∑ d ∈ Finset.range N, S F r hr a d) * (∑ e ∈ Finset.range N, S F k hk b e))
      =ᶠ[Filter.atTop] (fun N : ℕ =>
        (∑ d ∈ Finset.range N, S F r hr a d * ∑ e ∈ Finset.range d, S F k hk b e)
        + (∑ e ∈ Finset.range N, S F k hk b e * ∑ d ∈ Finset.range e, S F r hr a d)
        + (∑ d ∈ Finset.range N, S F r hr a d * S F k hk b d)) :=
    Eventually.of_forall
      (fun N => box_gen (fun d => S F r hr a d) (fun e => S F k hk b e) N)
  exact tendsto_nhds_unique hL (hR.congr' hEq.symm)

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ **The product of two MZVs lies in `𝒵` at the sum of the weights.** -/
theorem zeta_mul_mem_Z {r k : ℕ} (hr : 0 < r) (hk : 0 < k)
    (a : Fin r → ℕ+) (b : Fin k → ℕ+) :
    ζ_A F a * ζ_A F b ∈ 𝒵 F (weight r a + weight k b) := by
  obtain ⟨D1⟩ := (p1p2_full_all F k hk r hr).1 hr hk a b
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
    exact Submodule.smul_mem _ _ (zeta_mem_Z F (D1.c i) hw)
  · refine Submodule.sum_mem _ (fun i _ => ?_)
    have hw : weight (D3.dep i) (D3.c i) = weight r a + weight k b := (D3.hle i).1
    have hsm : ((D3.f i : ℤ) : RatFunc.CompletionAtInfty F)
        = (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) ((D3.f i : ℤ) : RatFunc F) := by
      rw [map_intCast]
    rw [hsm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (zeta_mem_Z F (D3.c i) hw)
  · refine Submodule.sum_mem _ (fun i _ => ?_)
    have hw : weight (D3'.dep i) (D3'.c i) = weight r a + weight k b :=
      ((D3'.hle i).1).trans (Nat.add_comm (weight k b) (weight r a))
    have hsm : ((D3'.f i : ℤ) : RatFunc.CompletionAtInfty F)
        = (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F)) ((D3'.f i : ℤ) : RatFunc F) := by
      rw [map_intCast]
    rw [hsm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (zeta_mem_Z F (D3'.c i) hw)

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The empty tuple has MZV `1`. -/
theorem zeta_A_fin_zero (𝔰 : Fin 0 → ℕ+) : ζ_A F 𝔰 = 1 := by
  classical
  haveI : Nonempty (monicStrictAntiNatDegree F 0) :=
    ⟨⟨fun i => (Fin.elim0 i : Polynomial F), fun a _ => (Fin.elim0 a : False).elim,
      fun i => Fin.elim0 i⟩⟩
  rw [ζ_A_eq_tsum_zetaTerm F 𝔰]
  rw [tsum_eq_single (Classical.arbitrary (monicStrictAntiNatDegree F 0))
      (fun b hb => absurd (Subsingleton.elim b _) hb)]
  simp [zetaTermAux]

/-- ★★★ **The graded-algebra structure.**  The product of the weight-`w` and the weight-`w'`
space of MZVs lies in `𝒵 (w+w')`; equivalently `⨁_{w≥0} 𝒵_w` is a graded algebra.  (No
positivity hypothesis: the weight-`0` tuples are the empty tuple, whose MZV is `1`.) -/
theorem Z_mul_Z_le (w w' : ℕ) : 𝒵 F w * 𝒵 F w' ≤ 𝒵 F (w + w') := by
  classical
  have hspan : 𝒵 F w * 𝒵 F w' = Submodule.span (RatFunc F)
      ((⋃ r : ℕ, ζ_A_weight F w r) * (⋃ r : ℕ, ζ_A_weight F w' r)) := by
    rw [𝒵, 𝒵, Submodule.span_mul_span]
  rw [hspan, Submodule.span_le]
  rintro z ⟨x, hx, y, hy, hxy⟩
  rw [← hxy]
  obtain ⟨r, hxr⟩ := Set.mem_iUnion.mp hx
  obtain ⟨k, hyk⟩ := Set.mem_iUnion.mp hy
  rw [ζ_A_weight_mem_iff F w r] at hxr
  rw [ζ_A_weight_mem_iff F w' k] at hyk
  obtain ⟨𝔰, h𝔰w, hxζ⟩ := hxr
  obtain ⟨𝔱, h𝔱w, hyζ⟩ := hyk
  change x * y ∈ 𝒵 F (w + w')
  rw [hxζ, hyζ]
  have hsw : weight r 𝔰 = w := h𝔰w
  have htw : weight k 𝔱 = w' := h𝔱w
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0
    have hw0 : w = 0 := by
      have h := hsw
      simp [weight] at h
      omega
    rw [hw0, Nat.zero_add, zeta_A_fin_zero F 𝔰, one_mul]
    exact zeta_mem_Z F 𝔱 htw
  · rcases Nat.eq_zero_or_pos k with h0 | hk
    · subst h0
      have hw0 : w' = 0 := by
        have h := htw
        simp [weight] at h
        omega
      rw [hw0, Nat.add_zero, zeta_A_fin_zero F 𝔱, mul_one]
      exact zeta_mem_Z F 𝔰 hsw
    · simpa [hsw, htw] using zeta_mul_mem_Z F hr hk 𝔰 𝔱

/-- ★★★ The graded-algebra structure, membership form. -/
theorem Z_mul_mem_Z {w w' : ℕ} {x y : RatFunc.CompletionAtInfty F}
    (hx : x ∈ 𝒵 F w) (hy : y ∈ 𝒵 F w') : x * y ∈ 𝒵 F (w + w') :=
  Submodule.mul_le.mp (Z_mul_Z_le F w w') x hx y hy

/-- The graded-algebra structure for the paper's weight convention `w ∈ ℕ+`. -/
theorem Z_mul_Z_le_pnat (w w' : ℕ+) :
    𝒵 F (w : ℕ) * 𝒵 F (w' : ℕ) ≤ 𝒵 F ((w : ℕ) + (w' : ℕ)) :=
  Z_mul_Z_le F (w : ℕ) (w' : ℕ)

/-- ★★ **Products of two `𝒯`-elements lie in `𝒵` at the sum of the weights.** -/
theorem T_mul_T_mem_Z {w w' : ℕ} {x y : RatFunc.CompletionAtInfty F}
    (hx : x ∈ 𝒯 F w) (hy : y ∈ 𝒯 F w') : x * y ∈ 𝒵 F (w + w') :=
  Z_mul_mem_Z F (𝒯_subset_𝒵 F w hx) (𝒯_subset_𝒵 F w' hy)

/-- ★★ **Products of MZVs, stated on tuples**: `ζ_A(𝔰)·ζ_A(𝔱)` lies in `𝒵` at the sum of the
weights, in the paper's `ℕ+` normalisation. -/
theorem zeta_mul_mem_Z_pnat {r k : ℕ+} (a : Fin r → ℕ+) (b : Fin k → ℕ+) :
    ζ_A F a * ζ_A F b ∈ 𝒵 F ((weight r a : ℕ) + (weight k b : ℕ)) :=
  zeta_mul_mem_Z F r.pos k.pos a b

/-- ★★ **The graded algebra, iterated**: a product of `n+1` MZVs of weights `w 0, …, w n` lies in
`𝒵` at the sum of the weights. -/
theorem Z_prod_mem_Z {n : ℕ} (w : Fin (n + 1) → ℕ) (x : Fin (n + 1) → RatFunc.CompletionAtInfty F)
    (hx : ∀ i, x i ∈ 𝒵 F (w i)) :
    ∏ i : Fin (n + 1), x i ∈ 𝒵 F (∑ i : Fin (n + 1), w i) := by
  induction n with
  | zero => simpa using hx 0
  | succ n ih =>
      rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
      exact Z_mul_mem_Z F (hx 0)
        (ih (fun i => w i.succ) (fun i => x i.succ) (fun i => hx _))

/-- ★★ **The weight-`0` space is the line spanned by the unit**: `𝒵 0 = K·1`.  (There are no
non-empty tuples of weight `0`, and the empty tuple has MZV `1`.) -/
theorem Z_zero_eq :
    𝒵 F 0 = Submodule.span (RatFunc F) ({(1 : RatFunc.CompletionAtInfty F)} : Set _) := by
  rw [𝒵]
  congr 1
  ext x
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, hxr⟩
    rcases Nat.eq_zero_or_pos r with h0 | hr
    · subst h0
      rw [ζ_A_weight_mem_iff F 0 0] at hxr
      obtain ⟨𝔰, _, hxζ⟩ := hxr
      rw [hxζ, zeta_A_fin_zero F 𝔰]
    · rw [ζ_A_weight_eq_empty_of_lt F (show 0 < r by omega)] at hxr
      exact absurd hxr (Set.notMem_empty x)
  · intro hx
    refine ⟨0, ?_⟩
    rw [ζ_A_weight_mem_iff F 0 0]
    refine ⟨fun i : Fin 0 => Fin.elim0 i, by simp, ?_⟩
    rw [hx]
    exact (zeta_A_fin_zero F (fun i : Fin 0 => Fin.elim0 i)).symm

/-- The unit of `K∞` is the MZV attached to the empty tuple, and lies in `𝒵 0`. -/
theorem one_mem_Z_zero : (1 : RatFunc.CompletionAtInfty F) ∈ 𝒵 F 0 := by
  rw [Z_zero_eq]
  exact Submodule.subset_span rfl

end ZagierHoffmanPositiveChar