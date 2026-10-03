/-
# `Work.FIChain.VfBFacts` — the elementary `VfB`/`LinNormK` toolbox

The reusable facts about the `B`-delay sieve product `VfB ν y = ∏_{p < y}(1 - ν p)` and its
normalisation `LinNormK ν C κ` that the layer analysis uses.  Split out of
`oddLayers_le_of_delta.lean` (which keeps only the target theorem) so that other developments can
import them without touching the file that still carries the target's `sorry`:

* `prod_one_sub_ge`, `sum_nu_le` — the ratio and measure forms of `LinNormK`;
* `VfB_pos`, `VfB_antitone`, `VfB_ratio_le` — monotonicity and the splittable ratio bound;
* `VfB_succ`, `sum_nu_VfB_eq` — the telescoping `ν p·VfB p = VfB p - VfB p⁺`;
* `chain_cancel` — the Rosser–Iwaniec chain cancellation: the chain's own `∏ ν p` is absorbed by
  the range product `∏(1-ν p)^{-1}` because `ν p ≤ 1/2 ≤ 1-ν p`;
* `TnB_support` — a nonzero layer forces `D < (⌈y⌉₊)^{B+n}`.
-/
import Mathlib
import Submission.Work.FIChain.LamPlusBLayerDefs
import Submission.Work.FIChain.GpB_eq_VfB_add_oddLayers

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The two consequences of `LinNormK` -/

/-- **Ratio bound.** -/
lemma prod_one_sub_ge {ν : ℕ → ℝ} {C κ : ℝ} (h : LinNormK ν C κ)
    (hν1 : ∀ p, p.Prime → ν p ≤ 1/2) {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z)
    (hC : 0 < C) :
    (C * (Real.log z / Real.log w)^κ)⁻¹
      ≤ ∏ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - ν p) := by
  have hprod := h w z hw hwz
  have hpos : 0 < ∏ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - ν p) := by
    refine Finset.prod_pos (fun p hp => ?_)
    have hp' : p.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
    have := hν1 p hp'; linarith
  have hCpos : 0 < C * (Real.log z / Real.log w)^κ := by
    apply mul_pos hC
    exact Real.rpow_pos_of_pos (div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))) κ
  rw [Finset.prod_inv_distrib] at hprod
  rw [inv_le_comm₀ hpos hCpos] at hprod
  exact hprod

/-- **Measure bound.** -/
lemma sum_nu_le {ν : ℕ → ℝ} {C κ : ℝ} (h : LinNormK ν C κ)
    (hν0 : ∀ p, p.Prime → 0 ≤ ν p) (hν1 : ∀ p, p.Prime → ν p ≤ 1/2)
    {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z) (hC : 0 < C) :
    ∑ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), ν p
      ≤ Real.log C + κ * Real.log (Real.log z / Real.log w) := by
  have hpos : 0 < ∏ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - ν p) := by
    refine Finset.prod_pos (fun p hp => ?_)
    have hp' : p.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
    have := hν1 p hp'; linarith
  have hCpos : 0 < C * (Real.log z / Real.log w)^κ := by
    apply mul_pos hC
    exact Real.rpow_pos_of_pos (div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))) κ
  have hle : ∀ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)),
      ν p ≤ - Real.log (1 - ν p) := by
    intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
    have h0 := hν0 p hp'; have h1 := hν1 p hp'
    have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 - ν p by linarith)
    linarith
  have hsumlog : ∑ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)),
      -Real.log (1 - ν p)
      = - Real.log (∏ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - ν p)) := by
    rw [Finset.sum_neg_distrib, Real.log_prod]
    intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
    have := hν1 p hp'; linarith
  have hkey := prod_one_sub_ge h hν1 hw hwz hC
  have hlogc : Real.log ((C * (Real.log z / Real.log w)^κ)⁻¹)
      ≤ Real.log (∏ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - ν p)) :=
    Real.log_le_log (inv_pos.mpr hCpos) hkey
  have hlog2 : Real.log (C * (Real.log z / Real.log w)^κ)
      = Real.log C + κ * Real.log (Real.log z / Real.log w) := by
    rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos
      (div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))) κ)), Real.log_rpow]
    exact div_pos (Real.log_pos (by linarith)) (Real.log_pos (by linarith))
  calc ∑ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), ν p
      ≤ ∑ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), -Real.log (1 - ν p) :=
        Finset.sum_le_sum hle
    _ = - Real.log (∏ p ∈ (Nat.primesBelow (⌈z⌉₊)).filter (fun p : ℕ => w ≤ (p:ℝ)), (1 - ν p)) :=
        hsumlog
    _ ≤ - Real.log ((C * (Real.log z / Real.log w)^κ)⁻¹) := by linarith
    _ = Real.log (C * (Real.log z / Real.log w)^κ) := by rw [Real.log_inv, neg_neg]
    _ = Real.log C + κ * Real.log (Real.log z / Real.log w) := hlog2

/-! ## Elementary facts about `VfB` and the support of the layers -/

/-- `VfB` is positive when `ν p ≤ 1/2` at primes. -/
lemma VfB_pos {ν : ℕ → ℝ} (hν1 : ∀ p, p.Prime → ν p ≤ 1/2) (y : ℝ) : 0 < VfB ν y := by
  rw [VfB]
  refine Finset.prod_pos (fun p hp => ?_)
  have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
  have := hν1 p hp'; linarith

/-- `VfB` is non-increasing in the range. -/
lemma VfB_antitone {ν : ℕ → ℝ} (hν0 : ∀ p, p.Prime → 0 ≤ ν p)
    (hν1 : ∀ p, p.Prime → ν p ≤ 1/2) {w z : ℝ} (hwz : w ≤ z) : VfB ν z ≤ VfB ν w := by
  rw [VfB, VfB]
  have hsub : Nat.primesBelow ⌈w⌉₊ ⊆ Nat.primesBelow ⌈z⌉₊ := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.ceil_le.mpr (le_trans hwz (Nat.le_ceil z))), hp.2⟩
  refine Finset.prod_le_prod_of_subset_of_le_one₀ hsub ?_ ?_
  · intro p hp
    have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have h1 := hν1 p hp'
    linarith
  · intro p hp _
    have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have h0 := hν0 p hp'
    linarith

/-- **`VfB` ratio bound** (the splittable form of `LinNormK`): `VfB c ≤ C(log z/log c)^κ · VfB z`. -/
lemma VfB_ratio_le {ν : ℕ → ℝ} {C κ : ℝ} (h : LinNormK ν C κ)
    (hν1 : ∀ p, p.Prime → ν p ≤ 1/2) {c z : ℕ} (hc : 2 ≤ c) (hcz : c ≤ z) (hC : 0 < C) :
    VfB ν (c:ℝ) ≤ VfB ν (z:ℝ) * (C * (Real.log z / Real.log c)^κ) := by
  have hz1 : 1 < (z:ℝ) := by exact_mod_cast (le_trans hc hcz : 2 ≤ z)
  have hc1 : 1 < (c:ℝ) := by exact_mod_cast hc
  have hsub : Nat.primesBelow c ⊆ Nat.primesBelow z := by
    intro p hp; rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 hcz, hp.2⟩
  have hset : Nat.primesBelow z \ Nat.primesBelow c
      = (Nat.primesBelow z).filter (fun p : ℕ => c ≤ p) := by
    ext p; simp only [Finset.mem_sdiff, Finset.mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hz, hp⟩, hnc⟩
      exact ⟨⟨hz, hp⟩, by by_contra h; exact hnc ⟨by omega, hp⟩⟩
    · rintro ⟨⟨hz, hp⟩, hc'⟩; exact ⟨⟨hz, hp⟩, by omega⟩
  have hlin := h (c:ℝ) (z:ℝ) (by exact_mod_cast hc) (by exact_mod_cast hcz)
  simp only [Nat.ceil_natCast, Nat.cast_le] at hlin
  rw [Finset.prod_inv_distrib] at hlin
  rw [VfB, VfB, Nat.ceil_natCast, Nat.ceil_natCast]
  have hsd := Finset.prod_sdiff hsub (f := fun p : ℕ => (1 - ν p))
  rw [hset] at hsd
  have hVz : 0 < ∏ p ∈ Nat.primesBelow z, (1 - ν p) := Finset.prod_pos (fun p hp => by
    have := hν1 p (Nat.mem_primesBelow.mp hp).2; linarith)
  have hVc0 : 0 < ∏ p ∈ Nat.primesBelow c, (1 - ν p) := Finset.prod_pos (fun p hp => by
    have := hν1 p (Nat.mem_primesBelow.mp hp).2; linarith)
  have hsd' : ∏ p ∈ (Nat.primesBelow z).filter (fun p : ℕ => c ≤ p), (1 - ν p)
      = (∏ p ∈ Nat.primesBelow z, (1 - ν p)) / (∏ p ∈ Nat.primesBelow c, (1 - ν p)) := by
    rw [eq_div_iff (ne_of_gt hVc0)]
    exact hsd
  rw [hsd', inv_div, div_le_iff₀ hVz, mul_comm] at hlin
  exact hlin

/-- **Support of the layers.**  A non-zero layer sum `T_n(D,y)` forces `D < (⌈y⌉₊)^{B+n}`. -/
lemma TnB_support {B : ℝ} (hB0 : 0 ≤ B) {ν : ℕ → ℝ} :
    ∀ n : ℕ, 1 ≤ n → ∀ D y : ℝ, TnB B ν n D y ≠ 0 → D < ((⌈y⌉₊ : ℕ) : ℝ) ^ (B + (n:ℝ)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn D y h
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [show (1:ℕ) = 0 + 1 from rfl, TnB] at h
      obtain ⟨p, hp, _hpnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      rw [Finset.mem_filter] at hp
      obtain ⟨hpb, hpc⟩ := hp
      have hp' : p.Prime := (Nat.mem_primesBelow.mp hpb).2
      have hlt : p < ⌈y⌉₊ := (Nat.mem_primesBelow.mp hpb).1
      have hcond : D < (p:ℝ)^(B+1) := (TcondB_one B D p).mp hpc
      have hple : ((p:ℕ):ℝ) ≤ ((⌈y⌉₊ : ℕ):ℝ) := by exact_mod_cast Nat.le_of_lt hlt
      have hz : (0:ℝ) ≤ B + 1 := by linarith [hB0]
      have h2 := Real.rpow_le_rpow (x := (p:ℝ)) (y := ((⌈y⌉₊ : ℕ):ℝ)) (z := B+1)
        (by positivity) hple hz
      exact lt_of_lt_of_le hcond (by simpa using h2)
    · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n-1, by omega⟩
      subst hk
      rw [TnB] at h
      obtain ⟨p, hp, hpnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      rw [Finset.mem_filter] at hp
      obtain ⟨hpb, _hpc⟩ := hp
      have hp' : p.Prime := (Nat.mem_primesBelow.mp hpb).2
      have hlt : p < ⌈y⌉₊ := (Nat.mem_primesBelow.mp hpb).1
      have hpos : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp'.pos
      have hchild : TnB B ν k (D / (p:ℝ)) (p:ℝ) ≠ 0 := by
        intro hz; exact hpnz (by rw [hz, mul_zero])
      have hih := ih k (by omega) (by omega) (D / (p:ℝ)) (p:ℝ) hchild
      have hple : ((p:ℕ):ℝ) ≤ ((⌈y⌉₊ : ℕ):ℝ) := by exact_mod_cast Nat.le_of_lt hlt
      have hD : D < (p:ℝ)^(B+(k:ℝ)+1) := by
        have hmul := mul_lt_mul_of_pos_right hih hpos
        rw [div_mul_cancel₀ D (ne_of_gt hpos)] at hmul
        simp only [Nat.ceil_natCast] at hmul
        have he : (p:ℝ) ^ (B + (k:ℝ)) * (p:ℝ) = (p:ℝ)^(B+(k:ℝ)+1) := by
          conv_rhs => rw [show B + (k:ℝ) + 1 = (B + (k:ℝ)) + 1 from by ring,
            Real.rpow_add hpos]
          rw [Real.rpow_one]
        linarith [hmul, he]
      have hz2 : (0:ℝ) ≤ B + (k:ℝ) + 1 := by
        have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith [hB0]
      have hfin := Real.rpow_le_rpow (by positivity) hple hz2
      have hcast : B + ((k+1 : ℕ):ℝ) = B + (k:ℝ) + 1 := by push_cast; ring
      rw [hcast]
      exact lt_of_lt_of_le hD hfin

/-! ## The telescoping identity `ν(p)·VfB(p) = VfB(p) - VfB(p⁺)` -/

/-- Passing a prime multiplies `VfB` by `1 - ν p`. -/
lemma VfB_succ (ν : ℕ → ℝ) (n : ℕ) :
    VfB ν ((n+1:ℕ):ℝ)
      = (if n.Prime then (1 - ν n) * VfB ν (n:ℝ) else VfB ν (n:ℝ)) := by
  rw [VfB, VfB, Nat.ceil_natCast, Nat.ceil_natCast, Nat.primesBelow_succ]
  by_cases h : n.Prime
  · rw [if_pos h, if_pos h, Finset.prod_insert (Nat.notMem_primesBelow n)]
  · rw [if_neg h, if_neg h]

/-- **Telescoping.**  `Σ_{m ≤ p < M, p prime} ν p · VfB p = VfB m - VfB M`. -/
lemma sum_nu_VfB_eq {ν : ℕ → ℝ} {m M : ℕ} (hm : m ≤ M) :
    ∑ p ∈ (Finset.Ico m M).filter Nat.Prime, ν p * VfB ν (p:ℝ)
      = VfB ν (m:ℝ) - VfB ν (M:ℝ) := by
  have key : ∀ p : ℕ, (if p.Prime then ν p * VfB ν (p:ℝ) else 0)
      = VfB ν (p:ℝ) - VfB ν ((p+1:ℕ):ℝ) := by
    intro p
    by_cases hpp : p.Prime
    · rw [if_pos hpp, VfB_succ ν p, if_pos hpp]; ring
    · rw [if_neg hpp, VfB_succ ν p, if_neg hpp]; ring
  rw [Finset.sum_filter]
  refine Eq.trans (Finset.sum_congr rfl (fun p _ => key p)) ?_
  rw [Finset.sum_sub_distrib]
  have h := Finset.sum_Ico_sub (f := fun i : ℕ => VfB ν ((i:ℕ):ℝ)) hm
  rw [Finset.sum_sub_distrib] at h
  linarith [h]

/-! ## Chain cancellation

The key inequality that keeps the layer induction's constant independent of `Δ` (and only
polynomial in the `LinNormK` constant `C`): the union of the chain primes with the range
`[p_min, z)` contributes to `VfB(p_min)/VfB z` the inverse sieve factors `(1-νq)⁻¹`; the chain's
own factors cancel against the `νp`, and because `νp ≤ 1/2 ≤ 1-νp`, what survives is bounded by
the product of `(1-νq)⁻¹` over the *complement*. -/

/-- **Chain cancellation (finite-product form).**  Over a finite set `s` of primes with
`0 ≤ ν p ≤ 1/2`, multiplying `∏_{p∈s}ν p` into `(∏_{q∈s∪T}(1-νq))⁻¹` bounds it by
`∏_{q∈T}(1-νq)⁻¹`. -/
lemma chain_cancel (s T : Finset ℕ) (ν : ℕ → ℝ) (hdisj : Disjoint s T)
    (hν0 : ∀ p ∈ s, 0 ≤ ν p) (hν1 : ∀ p ∈ s, ν p ≤ 1/2)
    (hνT : ∀ p ∈ T, 0 ≤ ν p) (hνT1 : ∀ p ∈ T, ν p < 1) :
    (∏ p ∈ s, ν p) * (∏ q ∈ s ∪ T, (1 - ν q))⁻¹ ≤ ∏ q ∈ T, (1 - ν q)⁻¹ := by
  have hs1 : 0 < ∏ q ∈ s, (1 - ν q) :=
    Finset.prod_pos (fun p hp => by have := hν1 p hp; linarith)
  have hBT : 0 ≤ (∏ q ∈ T, (1 - ν q))⁻¹ :=
    inv_nonneg.mpr (Finset.prod_nonneg (fun p hp => by have := hνT1 p hp; linarith))
  have hsν : ∏ p ∈ s, ν p ≤ ∏ q ∈ s, (1 - ν q) :=
    Finset.prod_le_prod₀ (fun p hp => hν0 p hp) (fun p hp => by
      have h0 := hν0 p hp; have h1 := hν1 p hp; linarith)
  have hkey : (∏ p ∈ s, ν p) * (∏ q ∈ s, (1 - ν q))⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hs1, one_mul]; exact hsν
  rw [Finset.prod_union hdisj, mul_inv, ← mul_assoc, Finset.prod_inv_distrib]
  exact mul_le_of_le_one_left hBT hkey

end

end Work.FIChain
