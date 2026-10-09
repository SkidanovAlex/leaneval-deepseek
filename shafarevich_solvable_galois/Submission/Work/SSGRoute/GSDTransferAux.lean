import Mathlib
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.PowTransfer.pCentralCommutatorSum
import Submission.Work.SSGRoute.prop5.commutator_lowerCentralSeries_le
import Submission.Work.ProP.lowerCentralSeries_le_pCentralSeries
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Work.SSGRoute.GSDTransferAux

open scoped commutatorElement
open Work.CohomologicalShrinking

/-- `[P^m, P^n] ≤ P^{m+n}` for the descending central series (`centralSeries P j` is the paper's
`P^j`, `centralSeries P 0 = ⊤`). -/
theorem commutator_centralSeries_le (P : Type*) [Group P] (m n : ℕ) :
    ⁅centralSeries P m, centralSeries P n⁆ ≤ centralSeries P (m + n) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [Nat.zero_add]
    haveI : (centralSeries P n).Normal :=
      Subgroup.lowerCentralSeries_normal (⊤ : Subgroup P) (n - 1)
    exact Subgroup.commutator_le_right _ _
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Nat.add_zero]
    haveI : (centralSeries P m).Normal :=
      Subgroup.lowerCentralSeries_normal (⊤ : Subgroup P) (m - 1)
    exact Subgroup.commutator_le_left _ _
  · have h := Work.SSGRoute.prop5.commutator_lowerCentralSeries_le P (m - 1) (n - 1)
    rw [show centralSeries P m = (⊤ : Subgroup P).lowerCentralSeries (m - 1) from rfl,
      show centralSeries P n = (⊤ : Subgroup P).lowerCentralSeries (n - 1) from rfl,
      show centralSeries P (m + n) = (⊤ : Subgroup P).lowerCentralSeries (m + n - 1) from rfl]
    exact le_trans h (le_of_eq (by
      rw [show (m - 1) + (n - 1) + 1 = m + n - 1 from by omega]))

/-- `[P^m, ·] ≤ P^m`. -/
theorem commutator_centralSeries_right_le (P : Type*) [Group P] (m : ℕ) :
    ⁅centralSeries P m, (⊤ : Subgroup P)⁆ ≤ centralSeries P m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · show ⁅(⊤ : Subgroup P).lowerCentralSeries (m - 1), (⊤ : Subgroup P)⁆
        ≤ (⊤ : Subgroup P).lowerCentralSeries (m - 1)
    rw [← Subgroup.lowerCentralSeries_succ (⊤ : Subgroup P) (m - 1),
      show (m - 1) + 1 = m from by omega]
    exact Subgroup.lowerCentralSeries_antitone _ (by omega)

/-- `x² ∈ P_{i+1}` if `x ∈ P_i` (paper indexing). -/
theorem pow2_mem_pSeries (P : Type*) [Group P] (i : ℕ) (hi : 1 ≤ i) {x : P}
    (hx : x ∈ pSeries 2 P i) : x ^ 2 ∈ pSeries 2 P (i + 1) := by
  have h := Work.Shrinking.pow_mem_pCentralSeries_succ 2 P (n := i - 1) hx
  rwa [show i - 1 + 1 = i from by omega] at h

/-- `x^(2^k) ∈ P_{i+k}` if `x ∈ P_i`. -/
theorem pow_mem_pSeries (P : Type*) [Group P] (i k : ℕ) (hi : 1 ≤ i) {x : P}
    (hx : x ∈ pSeries 2 P i) : x ^ (2 ^ k) ∈ pSeries 2 P (i + k) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      have h : x ^ (2 ^ (k + 1)) = (x ^ (2 ^ k)) ^ 2 := by
        rw [pow_succ, pow_mul]
      rw [h]
      exact pow2_mem_pSeries P (i + k) (by omega) ih

/-- `[P_m, P_n] ≤ P_{m+n}` in the paper's `p`-series indexing. -/
theorem commutator_pSeries_le (P : Type*) [Group P] (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ⁅pSeries 2 P m, pSeries 2 P n⁆ ≤ pSeries 2 P (m + n) := by
  have h := Work.SSGRoute.PowTransfer.commutator_pCentralSeries_two_le P (m - 1) (n - 1)
  show ⁅Work.Shrinking.pCentralSeries 2 P (m - 1),
      Work.Shrinking.pCentralSeries 2 P (n - 1)⁆
      ≤ Work.Shrinking.pCentralSeries 2 P (m + n - 1)
  rw [show (m - 1) + (n - 1) + 1 = m + n - 1 from by omega] at h
  exact h

/-- `[·, P^m] ≤ P^m`. -/
theorem commutator_centralSeries_left_le (P : Type*) [Group P] (m : ℕ) :
    ⁅(⊤ : Subgroup P), centralSeries P m⁆ ≤ centralSeries P m := by
  rw [Subgroup.commutator_comm]
  exact commutator_centralSeries_right_le P m

/-- If `z ∈ γ₀ ⊔ P_t` then `z^(2^j) ∈ γ₀ ⊔ P_{t+j}` (the `p`-series index gains `j` under
iterated squaring). -/
theorem pow_two_pow_mem_pSeries_sup (P : Type*) [Group P] (γ₀ : Subgroup P) [hγ₀ : γ₀.Normal]
    (t j : ℕ) (ht : 1 ≤ t) {z : P} (hz : z ∈ γ₀ ⊔ pSeries 2 P t) :
    z ^ (2 ^ j) ∈ γ₀ ⊔ pSeries 2 P (t + j) := by
  induction j with
  | zero => simpa using hz
  | succ j ih =>
      have h2 : z ^ (2 ^ (j + 1)) = (z ^ (2 ^ j)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [h2]
      haveI : (pSeries 2 P (t + j)).Normal := by
        rw [show pSeries 2 P (t + j) = Work.Shrinking.pCentralSeries 2 P (t + j - 1) from rfl]
        infer_instance
      obtain ⟨γ1, hγ1, g1, hg1, hγ1g1⟩ := Subgroup.mem_sup_of_normal_right.mp ih
      rw [← hγ1g1]
      have hgc : g1 * γ1 * g1⁻¹ ∈ γ₀ := hγ₀.conj_mem γ1 hγ1 g1
      have hg2 : g1 ^ 2 ∈ pSeries 2 P (t + j + 1) := pow2_mem_pSeries P (t + j) (by omega) hg1
      rw [show (γ1 * g1) ^ 2 = (γ1 * (g1 * γ1 * g1⁻¹)) * g1 ^ 2 by
        simp only [pow_two]; group]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mem_sup_left hγ1) (Subgroup.mem_sup_left hgc))
        (Subgroup.mem_sup_right hg2)

/-- `(UV)² (U²V²)⁻¹ [V,U]⁻¹ ∈ P_{m+n+2}` for `U ∈ P_m`, `V ∈ P_n` (0-indexed `pCentralSeries`). -/
theorem commutatorSquare_mem (P : Type*) [Group P] (m n : ℕ) (U V : P)
    (hU : U ∈ Work.Shrinking.pCentralSeries 2 P m)
    (hV : V ∈ Work.Shrinking.pCentralSeries 2 P n) :
    (U * V) ^ 2 * (U ^ 2 * V ^ 2)⁻¹ * (⁅V, U⁆)⁻¹ ∈
      Work.Shrinking.pCentralSeries 2 P (m + n + 2) := by
  have hkey : (U * V) ^ 2 * (U ^ 2 * V ^ 2)⁻¹ = U * ⁅V, U⁆ * U⁻¹ := by
    simp only [commutatorElement_def, pow_two]; group
  rw [hkey, show U * ⁅V, U⁆ * U⁻¹ * ⁅V, U⁆⁻¹ = ⁅U, ⁅V, U⁆⁆ from
    (commutatorElement_def U ⁅V, U⁆).symm]
  have hc' : ⁅U, V⁆ ∈ Work.Shrinking.pCentralSeries 2 P (m + n + 1) :=
    Work.SSGRoute.PowTransfer.commutator_pCentralSeries_two_le P m n (Subgroup.commutator_mem_commutator hU hV)
  have hc : ⁅V, U⁆ ∈ Work.Shrinking.pCentralSeries 2 P (m + n + 1) := by
    rw [← commutatorElement_inv U V]
    exact Subgroup.inv_mem _ hc'
  have hmem : ⁅U, ⁅V, U⁆⁆ ∈ Work.Shrinking.pCentralSeries 2 P (m + (m + n + 1) + 1) :=
    Work.SSGRoute.PowTransfer.commutator_pCentralSeries_two_le P m (m + n + 1)
      (Subgroup.commutator_mem_commutator hU hc)
  exact Work.Shrinking.pCentralSeries_antitone 2 P (by omega) hmem

/-- `[y,x] ∈ P^{b+d} · P_{a+c+1}` for `x ∈ P_{(a,b)}`, `y ∈ P_{(c,d)}` (paper indexing). -/
theorem commutator_refinedTerm_mem (P : Type*) [Group P] (a b c d : ℕ)
    (ha : 1 ≤ a) (hc : 1 ≤ c)
    {x y : P} (hx : x ∈ refinedTerm 2 P a b) (hy : y ∈ refinedTerm 2 P c d) :
    ⁅y, x⁆ ∈ centralSeries P (b + d) ⊔ pSeries 2 P (a + c + 1) := by
  haveI hdn : (centralSeries P (b + d)).Normal :=
    Subgroup.lowerCentralSeries_normal (⊤ : Subgroup P) (b + d - 1)
  haveI hpn : (pSeries 2 P (a + c + 1)).Normal := by
    rw [show pSeries 2 P (a + c + 1) = Work.Shrinking.pCentralSeries 2 P (a + c) from rfl]
    infer_instance
  haveI hT : (centralSeries P (b + d) ⊔ pSeries 2 P (a + c + 1)).Normal :=
    Subgroup.sup_normal _ _
  have hle : ⁅refinedTerm 2 P c d, refinedTerm 2 P a b⁆
      ≤ centralSeries P (b + d) ⊔ pSeries 2 P (a + c + 1) := by
    refine Subgroup.commutator_le.mpr (fun y0 hy0 x0 hx0 => ?_)
    rw [Work.CohomologicalShrinking.refinedTerm] at hy0 hx0
    haveI hpn1 : (pSeries 2 P (c + 1)).Normal := by
      rw [show pSeries 2 P (c + 1) = Work.Shrinking.pCentralSeries 2 P c from rfl]
      infer_instance
    haveI hpn2 : (pSeries 2 P (a + 1)).Normal := by
      rw [show pSeries 2 P (a + 1) = Work.Shrinking.pCentralSeries 2 P a from rfl]
      infer_instance
    rw [Subgroup.mem_sup_of_normal_right] at hy0
    obtain ⟨y1, hy1, y2, hy2, rfl⟩ := hy0
    rw [Subgroup.mem_sup_of_normal_right] at hx0
    obtain ⟨x1, hx1, x2, hx2, rfl⟩ := hx0
    rw [commutatorElement_mul_left_eq_conj_mul]
    -- pieces
    have hy2x1 : ⁅y2, x1⁆ ∈ pSeries 2 P (a + c + 1) := by
      have h2 := commutator_pSeries_le P (c + 1) a (by omega) ha
      rw [show (c + 1) + a = a + c + 1 from by omega] at h2
      exact h2 (Subgroup.commutator_mem_commutator hy2 hx1.1)
    have hy2x2 : ⁅y2, x2⁆ ∈ pSeries 2 P (a + c + 1) := by
      have h2 := commutator_pSeries_le P (c + 1) (a + 1) (by omega) (by omega)
      refine pSeries_antitone 2 P (by omega) (h2 ?_)
      exact Subgroup.commutator_mem_commutator hy2 hx2
    have hy1x1 : ⁅y1, x1⁆ ∈ centralSeries P (b + d) := by
      have h := commutator_centralSeries_le P d b
        (Subgroup.commutator_mem_commutator hy1.2 hx1.2)
      rwa [Nat.add_comm d b] at h
    have hy1x2 : ⁅y1, x2⁆ ∈ pSeries 2 P (a + c + 1) := by
      have h2 := commutator_pSeries_le P c (a + 1) (by omega) (by omega)
      rw [show c + (a + 1) = a + c + 1 from by omega] at h2
      exact h2 (Subgroup.commutator_mem_commutator hy1.1 hx2)
    -- assemble: goal is y1 * ⁅y2, x1*x2⁆ * y1⁻¹ * ⁅y1, x1*x2⁆ ∈ T
    have hy2xx : ⁅y2, x1 * x2⁆ ∈ centralSeries P (b + d) ⊔ pSeries 2 P (a + c + 1) := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hconj : x1 * ⁅y2, x2⁆ * x1⁻¹ ∈
          centralSeries P (b + d) ⊔ pSeries 2 P (a + c + 1) :=
        hT.conj_mem ⁅y2, x2⁆ (Subgroup.mem_sup_right hy2x2) x1
      simpa only [mul_assoc] using
        Subgroup.mul_mem _ (Subgroup.mem_sup_right hy2x1) hconj
    have hy1xx : ⁅y1, x1 * x2⁆ ∈ centralSeries P (b + d) ⊔ pSeries 2 P (a + c + 1) := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hconj : x1 * ⁅y1, x2⁆ * x1⁻¹ ∈
          centralSeries P (b + d) ⊔ pSeries 2 P (a + c + 1) :=
        hT.conj_mem ⁅y1, x2⁆ (Subgroup.mem_sup_right hy1x2) x1
      simpa only [mul_assoc] using
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hy1x1) hconj
    have hconj : y1 * ⁅y2, x1 * x2⁆ * y1⁻¹ ∈
        centralSeries P (b + d) ⊔ pSeries 2 P (a + c + 1) :=
      hT.conj_mem ⁅y2, x1 * x2⁆ hy2xx y1
    simpa only [mul_assoc] using Subgroup.mul_mem _ hconj hy1xx
  exact hle (Subgroup.commutator_mem_commutator hy hx)

/-- The engine of the proof: `(xy)^(2^k) · x^(2^k) y^(2^k)` relation modulo `P^{b+d} · P_{a+c+k}`
(paper indexing).  With `α, β` the `Γ`-levels of `x, y` and `[y,x] ∈ P^{b+d} · P_{a+c+1}`:
`(xy)^(2^k) · ([y,x]^(2^(k-1)))⁻¹ · (x^(2^k) y^(2^k))⁻¹ ∈ P^{b+d} · P_{a+c+k}`. -/
theorem engine (P : Type*) [Group P] (α β b d k : ℕ) (hk : 1 ≤ k) {x y : P}
    (hx : x ∈ pSeries 2 P (α + 1)) (hy : y ∈ pSeries 2 P (β + 1))
    (hcomm : ⁅y, x⁆ ∈ centralSeries P (b + d) ⊔ pSeries 2 P (α + β + 3)) :
    (x * y) ^ (2 ^ k) * (⁅y, x⁆ ^ (2 ^ (k - 1)))⁻¹ * (x ^ (2 ^ k) * y ^ (2 ^ k))⁻¹ ∈
      centralSeries P (b + d) ⊔ pSeries 2 P (α + β + k + 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have key : ∀ j : ℕ,
      (x * y) ^ (2 ^ (j + 1)) * (⁅y, x⁆ ^ (2 ^ j))⁻¹ *
        (x ^ (2 ^ (j + 1)) * y ^ (2 ^ (j + 1)))⁻¹ ∈
      centralSeries P (b + d) ⊔ pSeries 2 P (α + β + (j + 1) + 2) := by
    intro j
    induction j with
    | zero =>
        haveI ht : (pSeries 2 P (α + β + 3)).Normal := by
          rw [show pSeries 2 P (α + β + 3) =
            Work.Shrinking.pCentralSeries 2 P (α + β + 2) from rfl]
          infer_instance
        haveI hsup : (centralSeries P (b + d) ⊔ pSeries 2 P (α + β + 3)).Normal :=
          Subgroup.sup_normal _ _
        let φ : P →* P ⧸ (centralSeries P (b + d) ⊔ pSeries 2 P (α + β + 3)) :=
          QuotientGroup.mk' _
        have hφ0 : ∀ z : P, z ∈ (centralSeries P (b + d) ⊔ pSeries 2 P (α + β + 3)) →
            φ z = 1 := by
          intro z hz
          rw [show φ z = QuotientGroup.mk z from rfl, QuotientGroup.eq_one_iff]
          exact hz
        have hφ1 : ∀ z : P, φ z = 1 →
            z ∈ (centralSeries P (b + d) ⊔ pSeries 2 P (α + β + 3)) := by
          intro z hz
          rw [show φ z = QuotientGroup.mk z from rfl, QuotientGroup.eq_one_iff] at hz
          exact hz
        rw [show α + β + (0 + 1) + 2 = α + β + 3 from by omega]
        apply hφ1
        simp only [Nat.zero_add, pow_zero, pow_one, map_mul, map_inv]
        have hc0 : φ ⁅y, x⁆ = 1 := hφ0 _ hcomm
        have hxy : (x * y) ^ 2 * (x ^ 2 * y ^ 2)⁻¹ = x * ⁅y, x⁆ * x⁻¹ := by
          simp only [commutatorElement_def, pow_two]; group
        rw [hc0, inv_one, mul_one]
        have hcomb : φ ((x * y) ^ 2) * (φ (x ^ 2) * φ (y ^ 2))⁻¹ =
            φ ((x * y) ^ 2 * (x ^ 2 * y ^ 2)⁻¹) := by
          simp only [map_mul, map_inv]
        rw [hcomb, hxy, map_mul, map_mul, map_inv, hc0]
        group
    | succ j ih =>
        have hAe : (x * y) ^ (2 ^ (j + 2)) = ((x * y) ^ (2 ^ (j + 1))) ^ 2 := by
          rw [show j + 2 = (j + 1) + 1 from by omega, pow_succ, pow_mul]
        have hUe : x ^ (2 ^ (j + 2)) = (x ^ (2 ^ (j + 1))) ^ 2 := by
          rw [show j + 2 = (j + 1) + 1 from by omega, pow_succ, pow_mul]
        have hVe : y ^ (2 ^ (j + 2)) = (y ^ (2 ^ (j + 1))) ^ 2 := by
          rw [show j + 2 = (j + 1) + 1 from by omega, pow_succ, pow_mul]
        rw [hAe, hUe, hVe]
        set A : P := (x * y) ^ (2 ^ (j + 1)) with hAdef
        set U : P := x ^ (2 ^ (j + 1)) with hUdef
        set V : P := y ^ (2 ^ (j + 1)) with hVdef
        set c0 : P := ⁅y, x⁆ with hc0def
        set Z : P := c0 ^ (2 ^ j) with hZdef
        set N : Subgroup P := centralSeries P (b + d) ⊔ pSeries 2 P (α + β + j + 4) with hNdef
        haveI hNn : N.Normal := by rw [hNdef]; exact Subgroup.sup_normal _ _
        haveI ht3 : (pSeries 2 P (α + β + j + 3)).Normal := by
          rw [show pSeries 2 P (α + β + j + 3) =
            Work.Shrinking.pCentralSeries 2 P (α + β + j + 2) from rfl]
          infer_instance
        haveI ht4 : (pSeries 2 P (α + β + j + 4)).Normal := by
          rw [show pSeries 2 P (α + β + j + 4) =
            Work.Shrinking.pCentralSeries 2 P (α + β + j + 3) from rfl]
          infer_instance
        haveI hNoldn : (centralSeries P (b + d) ⊔ pSeries 2 P (α + β + j + 3)).Normal :=
          Subgroup.sup_normal _ _
        have hZe2 : c0 ^ (2 ^ (j + 1)) = Z ^ 2 := by
          rw [show (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j, pow_mul, hZdef]
        set Ψ : P := A * Z⁻¹ * (U * V)⁻¹ with hΨdef
        have hΨmem : Ψ ∈ centralSeries P (b + d) ⊔ pSeries 2 P (α + β + j + 3) := ih
        obtain ⟨γ1, hγ1, g1, hg1, hγ1g1⟩ := Subgroup.mem_sup_of_normal_right.mp hΨmem
        have hΨsq : Ψ ^ 2 ∈ N := by
          rw [← hγ1g1, hNdef]
          have hgc : g1 * γ1 * g1⁻¹ ∈ centralSeries P (b + d) :=
            (inferInstance : (centralSeries P (b + d)).Normal).conj_mem γ1 hγ1 g1
          have hg2 : g1 ^ 2 ∈ pSeries 2 P (α + β + j + 4) :=
            pow2_mem_pSeries P (α + β + j + 3) (by omega) hg1
          rw [show (γ1 * g1) ^ 2 = (γ1 * (g1 * γ1 * g1⁻¹)) * g1 ^ 2 by
            simp only [pow_two]; group]
          exact Subgroup.mul_mem _
            (Subgroup.mul_mem _ (Subgroup.mem_sup_left hγ1) (Subgroup.mem_sup_left hgc))
            (Subgroup.mem_sup_right hg2)
        have hΨcomm : ∀ w : P, ⁅Ψ, w⁆ ∈ N := by
          intro w
          rw [← hγ1g1, commutatorElement_mul_left_eq_conj_mul, hNdef]
          have hgw : ⁅g1, w⁆ ∈ pSeries 2 P (α + β + j + 4) :=
            (Work.Shrinking.commutator_le_pCentralSeries_succ 2 P (α + β + j + 2)).1
              (Subgroup.commutator_mem_commutator hg1 (Subgroup.mem_top w))
          have hγw : ⁅γ1, w⁆ ∈ centralSeries P (b + d) :=
            commutator_centralSeries_right_le P (b + d)
              (Subgroup.commutator_mem_commutator hγ1 (Subgroup.mem_top w))
          refine Subgroup.mul_mem _
            ((inferInstance : N.Normal).conj_mem ⁅g1, w⁆ (Subgroup.mem_sup_right hgw) γ1)
            (Subgroup.mem_sup_left hγw)
        have hc0old : Z ∈ centralSeries P (b + d) ⊔ pSeries 2 P (α + β + j + 3) := by
          have h := pow_two_pow_mem_pSeries_sup P (centralSeries P (b + d)) (α + β + 3) j
            (by omega) hcomm
          rwa [show α + β + 3 + j = α + β + j + 3 from by omega] at h
        have hZcomm : ∀ w : P, ⁅Z, w⁆ ∈ N := by
          intro w
          obtain ⟨γ2, hγ2, g2, hg2, hγ2g2⟩ := Subgroup.mem_sup_of_normal_right.mp hc0old
          rw [← hγ2g2, commutatorElement_mul_left_eq_conj_mul, hNdef]
          have hgw : ⁅g2, w⁆ ∈ pSeries 2 P (α + β + j + 4) :=
            (Work.Shrinking.commutator_le_pCentralSeries_succ 2 P (α + β + j + 2)).1
              (Subgroup.commutator_mem_commutator hg2 (Subgroup.mem_top w))
          have hγw : ⁅γ2, w⁆ ∈ centralSeries P (b + d) :=
            commutator_centralSeries_right_le P (b + d)
              (Subgroup.commutator_mem_commutator hγ2 (Subgroup.mem_top w))
          refine Subgroup.mul_mem _
            ((inferInstance : N.Normal).conj_mem ⁅g2, w⁆ (Subgroup.mem_sup_right hgw) γ2)
            (Subgroup.mem_sup_left hγw)
        have hUm : U ∈ Work.Shrinking.pCentralSeries 2 P (α + j + 1) := by
          have h := pow_mem_pSeries P (α + 1) (j + 1) (by omega) hx
          rw [show α + 1 + (j + 1) = (α + j + 1) + 1 from by omega] at h
          exact h
        have hVm : V ∈ Work.Shrinking.pCentralSeries 2 P (β + j + 1) := by
          have h := pow_mem_pSeries P (β + 1) (j + 1) (by omega) hy
          rw [show β + 1 + (j + 1) = (β + j + 1) + 1 from by omega] at h
          exact h
        have hcVU : ⁅V, U⁆ ∈ Work.Shrinking.pCentralSeries 2 P (α + β + 2 * j + 3) := by
          have h2 := Work.SSGRoute.PowTransfer.commutator_pCentralSeries_two_le P (α + j + 1) (β + j + 1)
            (Subgroup.commutator_mem_commutator hUm hVm)
          rw [show (α + j + 1) + (β + j + 1) + 1 = α + β + 2 * j + 3 from by omega] at h2
          rw [← commutatorElement_inv U V]
          exact Subgroup.inv_mem _ h2
        have hUVsq : (U * V) ^ 2 * (U ^ 2 * V ^ 2)⁻¹ ∈ N := by
          have h := commutatorSquare_mem P (α + j + 1) (β + j + 1) U V hUm hVm
          have hmem : (U * V) ^ 2 * (U ^ 2 * V ^ 2)⁻¹ ∈
              Work.Shrinking.pCentralSeries 2 P (α + β + 2 * j + 3) := by
            have h' : (U * V) ^ 2 * (U ^ 2 * V ^ 2)⁻¹ * ⁅V, U⁆⁻¹ ∈
                Work.Shrinking.pCentralSeries 2 P (α + β + 2 * j + 3) :=
              Work.Shrinking.pCentralSeries_antitone 2 P (by omega) h
            have h3 := (Work.Shrinking.pCentralSeries 2 P (α + β + 2 * j + 3)).mul_mem h' hcVU
            simpa only [mul_assoc, inv_mul_cancel, mul_one] using h3
          exact Subgroup.mem_sup_right (Work.Shrinking.pCentralSeries_antitone 2 P (by omega) hmem)
        let φ : P →* P ⧸ N := QuotientGroup.mk' N
        have hφ0 : ∀ z : P, z ∈ N → φ z = 1 := by
          intro z hz
          rw [show φ z = QuotientGroup.mk z from rfl, QuotientGroup.eq_one_iff]
          exact hz
        have hφ1 : ∀ z : P, φ z = 1 → z ∈ N := by
          intro z hz
          rw [show φ z = QuotientGroup.mk z from rfl, QuotientGroup.eq_one_iff] at hz
          exact hz
        have hcommΨ : ∀ w : P, Commute (φ Ψ) (φ w) := by
          intro w
          rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
          exact hφ0 _ (hΨcomm w)
        have hcommZ : ∀ w : P, Commute (φ Z) (φ w) := by
          intro w
          rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
          exact hφ0 _ (hZcomm w)
        have hcommUV : Commute (φ U) (φ V) := by
          rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
          apply hφ0
          rw [hNdef, show ⁅U, V⁆ = (⁅V, U⁆)⁻¹ from (commutatorElement_inv V U).symm]
          exact Subgroup.mem_sup_right (Subgroup.inv_mem _
            (Work.Shrinking.pCentralSeries_antitone 2 P (by omega) hcVU))
        have hΨ2 : (φ Ψ) ^ 2 = 1 := by
          rw [← map_pow]
          exact hφ0 _ hΨsq
        have hAeq : A = Ψ * (U * V) * Z := by
          rw [hΨdef]; group
        have hA2 : φ (A ^ 2) = φ (U ^ 2 * V ^ 2) * φ (Z ^ 2) := by
          rw [map_pow]
          have hAq : φ A = φ Ψ * (φ U * (φ V * φ Z)) := by
            rw [hAeq]; simp only [map_mul, mul_assoc]
          have h1 : Commute (φ Ψ) (φ U * (φ V * φ Z)) :=
            (hcommΨ U).mul_right ((hcommΨ V).mul_right (hcommΨ Z))
          have h2 : Commute (φ U * φ V) (φ Z) :=
            ((hcommZ U).mul_right (hcommZ V)).symm
          rw [hAq, h1.mul_pow, hΨ2, one_mul,
            show φ U * (φ V * φ Z) = φ U * φ V * φ Z from (mul_assoc _ _ _).symm,
            h2.mul_pow, hcommUV.mul_pow, ← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
        rw [hZe2]
        apply hφ1
        have hgoal : φ (A ^ 2 * (Z ^ 2)⁻¹ * (U ^ 2 * V ^ 2)⁻¹)
            = φ (A ^ 2) * (φ (Z ^ 2))⁻¹ * (φ (U ^ 2 * V ^ 2))⁻¹ := by
          simp only [map_mul, map_inv, map_pow]
        rw [hgoal, hA2]
        group
  exact key j

end Work.SSGRoute.GSDTransferAux
