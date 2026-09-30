import Mathlib
import Submission.Work.BMF.recursion.I1I2Defs
import Submission.Work.BMF.recursion.Weyl_factor
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.MomVec
import Submission.Work.BMF.recursion.sum_split_fin
import Submission.Work.BMF.recursion.Tset_prod_sum
import Submission.Work.BMF.recursion.subtype_fourier_eq_WeylMod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.BMF.recursion

open scoped BigOperators
open Classical

noncomputable section

-- ====== helpers ======


lemma zipT_apply_hIdx {k S Q : ℕ} (hkS : k ≤ S) (q : Tup k Q × Tup (S - k) Q) (i : Fin k) :
    zipT hkS q (hIdx hkS i) = q.1 i := by
  simp only [zipT]
  split_ifs with h
  · exact congrArg q.1 (Fin.ext rfl)
  · exact absurd (by simpa only [hIdx] using i.isLt) h

lemma zipT_apply_tIdx {k S Q : ℕ} (hkS : k ≤ S) (q : Tup k Q × Tup (S - k) Q) (r : Fin (S - k)) :
    zipT hkS q (tIdx hkS r) = q.2 r := by
  simp only [zipT]
  split_ifs with h
  · exact absurd h (by simp only [tIdx]; omega)
  · exact congrArg q.2 (Fin.ext (by simp only [tIdx]; omega))

lemma hdT_zipT {k S Q : ℕ} (hkS : k ≤ S) (q : Tup k Q × Tup (S - k) Q) :
    hdT hkS (zipT hkS q) = q.1 := by
  funext i
  exact zipT_apply_hIdx hkS q i

lemma tlT_zipT {k S Q : ℕ} (hkS : k ≤ S) (q : Tup k Q × Tup (S - k) Q) :
    tlT hkS (zipT hkS q) = q.2 := by
  funext r
  exact zipT_apply_tIdx hkS q r

lemma zipT_hdT_tlT {k S Q : ℕ} (hkS : k ≤ S) (x : Tup S Q) :
    zipT hkS (hdT hkS x, tlT hkS x) = x := by
  funext i
  simp only [zipT]
  split_ifs with h
  · exact congrArg x (Fin.ext rfl)
  · exact congrArg x (Fin.ext (by simp only [tIdx]; omega))

lemma HDp_hdT_iff {k S Q p : ℕ} (hkS : k ≤ S) (x : Tup S Q) :
    HDp p k hkS x ↔ HDp p k (le_refl k) (hdT hkS x) := by
  have key : ∀ i : Fin k, hdT hkS x (hIdx (le_refl k) i) = x (hIdx hkS i) := by
    intro i
    show x (hIdx hkS (hIdx (le_refl k) i)) = x (hIdx hkS i)
    exact congrArg x (Fin.ext rfl)
  simp only [HDp]
  constructor
  · intro h i j hij
    rw [key i, key j]
    exact h i j hij
  · intro h i j hij
    rw [← key i, ← key j]
    exact h i j hij

lemma TailEq_tlT_iff {k S Q p : ℕ} (hkS : k ≤ S) (y : ℕ) (x : Tup S Q) :
    TailEq p hkS y x ↔ Tails p y (tlT hkS x) := by
  simp only [TailEq, Tails, tlT]

lemma subtype_fourier_eq_Weyl (k Q : ℕ) (θ : UnitAddTorus (Fin (k + 1))) :
    (∑ b : Finset.Icc 1 Q, UnitAddTorus.mFourier (mom1 k b.1) θ) = Weyl k Q θ :=
  (Weyl_apply k Q θ).symm

lemma powerSums_zipT {k S Q : ℕ} (hkS : k ≤ S) (q : Tup k Q × Tup (S - k) Q) :
    Submission.Vinogradov.powerSums k (zipT hkS q)
      = Submission.Vinogradov.powerSums k q.1 + ∑ r : Fin (S - k), mom1 k ((q.2 r).1) := by
  rw [powerSums_eq_sum_mom1 (k := k) (x := zipT hkS q),
      powerSums_eq_sum_mom1 (k := k) (x := q.1),
      sum_split_fin (k := k) (S := S) hkS (fun i : Fin S => mom1 k ((zipT hkS q) i).1)]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [zipT_apply_hIdx])
  · exact Finset.sum_congr rfl (fun r _ => by rw [zipT_apply_tIdx])

lemma sum_i1Set_eq {M : Type*} [AddCommMonoid M] (S k Q p : ℕ) (hkS : k ≤ S)
    (f : Tup S Q → M) :
    ∑ x ∈ i1Set S k Q p hkS, f x
      = ∑ q ∈ (Ahead p k Q) ×ˢ (Finset.univ : Finset (Tup (S - k) Q)), f (zipT hkS q) := by
  classical
  refine Finset.sum_bij (fun x (_ : x ∈ i1Set S k Q p hkS) => (hdT hkS x, tlT hkS x)) ?_ ?_ ?_ ?_
  · intro x hx
    have hx' : HDp p k hkS x := by
      simpa only [i1Set, Finset.mem_filter, Finset.mem_univ, true_and] using hx
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ (tlT hkS x)⟩
    simp only [Ahead, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (HDp_hdT_iff hkS x).mp hx'
  · intro x hx y hy hxy
    rw [← zipT_hdT_tlT (Q := Q) hkS x, ← zipT_hdT_tlT (Q := Q) hkS y, hxy]
  · intro q hq
    obtain ⟨hqa, _⟩ := Finset.mem_product.mp hq
    have hq1 : HDp p k (le_refl k) q.1 := by
      simpa only [Ahead, Finset.mem_filter, Finset.mem_univ, true_and] using hqa
    refine ⟨zipT hkS q, ?_, ?_⟩
    · simp only [i1Set, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (HDp_hdT_iff hkS (zipT hkS q)).mpr (by rwa [hdT_zipT])
    · rw [hdT_zipT, tlT_zipT]
  · intro x hx
    exact (congrArg f (zipT_hdT_tlT (Q := Q) hkS x)).symm

lemma sum_i2Set_eq {M : Type*} [AddCommMonoid M] (S k Q p y : ℕ) (hkS : k ≤ S)
    (f : Tup S Q → M) :
    ∑ x ∈ i2Set S k Q p y hkS, f x
      = ∑ q ∈ (Ahead p k Q) ×ˢ (Tset p y (S - k) Q), f (zipT hkS q) := by
  classical
  have hmem : ∀ x : Tup S Q, x ∈ i2Set S k Q p y hkS ↔
      HDp p k hkS x ∧ TailEq p hkS y x := by
    intro x
    simp only [i2Set, i1Set, Finset.mem_filter, Finset.mem_univ, true_and]
  refine Finset.sum_bij (fun x (_ : x ∈ i2Set S k Q p y hkS) => (hdT hkS x, tlT hkS x)) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx1, hx2⟩ := (hmem x).mp hx
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · simp only [Ahead, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (HDp_hdT_iff hkS x).mp hx1
    · simp only [Tset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (TailEq_tlT_iff hkS y x).mp hx2
  · intro x hx y hy hxy
    rw [← zipT_hdT_tlT (Q := Q) hkS x, ← zipT_hdT_tlT (Q := Q) hkS y, hxy]
  · intro q hq
    obtain ⟨hqa, hqt⟩ := Finset.mem_product.mp hq
    have hq1 : HDp p k (le_refl k) q.1 := by
      simpa only [Ahead, Finset.mem_filter, Finset.mem_univ, true_and] using hqa
    have hq2 : Tails p y q.2 := by
      simpa only [Tset, Finset.mem_filter, Finset.mem_univ, true_and] using hqt
    refine ⟨zipT hkS q, ?_, ?_⟩
    · rw [hmem]
      refine ⟨?_, ?_⟩
      · exact (HDp_hdT_iff hkS (zipT hkS q)).mpr (by rwa [hdT_zipT])
      · rw [TailEq_tlT_iff, tlT_zipT]
        exact hq2
    · rw [hdT_zipT, tlT_zipT]
  · intro x hx
    exact (congrArg f (zipT_hdT_tlT (Q := Q) hkS x)).symm

lemma inner_sum_i1 (S k Q : ℕ) (hkS : k ≤ S) (a : Tup k Q) (θ : UnitAddTorus (Fin (k + 1))) :
    (∑ t : Tup (S - k) Q,
        UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k (zipT hkS (a, t))) θ)
      = UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k a) θ * (Weyl k Q θ) ^ (S - k) := by
  have h1 : ∀ t : Tup (S - k) Q,
      UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k (zipT hkS (a, t))) θ
        = UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k a) θ *
            ∏ r : Fin (S - k), UnitAddTorus.mFourier (mom1 k ((t r).1)) θ := by
    intro t
    rw [powerSums_zipT hkS (a, t), UnitAddTorus.mFourier_add]
    congr 1
    rw [mFourier_finset_sum Finset.univ (fun r : Fin (S - k) => mom1 k ((t r).1)) θ]
  rw [Finset.sum_congr rfl (fun t _ => h1 t), ← Finset.mul_sum]
  congr 1
  rw [sum_fin_fun_prod (fun b : Finset.Icc 1 Q => UnitAddTorus.mFourier (mom1 k (b.1)) θ) (S - k),
      subtype_fourier_eq_Weyl]

lemma inner_sum_i2 (S k Q p : ℕ) (hkS : k ≤ S) (y : ℕ) (a : Tup k Q)
    (θ : UnitAddTorus (Fin (k + 1))) :
    (∑ t ∈ Tset p y (S - k) Q,
        UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k (zipT hkS (a, t))) θ)
      = UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k a) θ *
          (WeylMod p k Q y θ) ^ (S - k) := by
  have h1 : ∀ t : Tup (S - k) Q,
      UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k (zipT hkS (a, t))) θ
        = UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k a) θ *
            ∏ r : Fin (S - k), UnitAddTorus.mFourier (mom1 k ((t r).1)) θ := by
    intro t
    rw [powerSums_zipT hkS (a, t), UnitAddTorus.mFourier_add]
    congr 1
    rw [mFourier_finset_sum Finset.univ (fun r : Fin (S - k) => mom1 k ((t r).1)) θ]
  rw [Finset.sum_congr rfl (fun t _ => h1 t), ← Finset.mul_sum]
  congr 1
  rw [Tset_prod_sum (Q := Q) (s := S - k) p y
        (fun b : Finset.Icc 1 Q => UnitAddTorus.mFourier (mom1 k (b.1)) θ),
      subtype_fourier_eq_WeylMod]

theorem headtail_factor (S k Q p : ℕ) (hkS : k ≤ S) :
    (F1 S k Q p hkS = fun θ : UnitAddTorus (Fin (k + 1)) =>
        Gw p k Q θ * (Weyl k Q θ) ^ (S - k)) ∧
    (∀ y : ℕ, F2 S k Q p y hkS = fun θ : UnitAddTorus (Fin (k + 1)) =>
        Gw p k Q θ * (WeylMod p k Q y θ) ^ (S - k)) := by
  classical
  constructor
  · funext θ
    simp only [F1]
    rw [sum_i1Set_eq, Finset.sum_product]
    rw [Finset.sum_congr rfl (fun a _ => inner_sum_i1 S k Q hkS a θ), ← Finset.sum_mul]
    rfl
  · intro y
    funext θ
    simp only [F2]
    rw [sum_i2Set_eq, Finset.sum_product]
    rw [Finset.sum_congr rfl (fun a _ => inner_sum_i2 S k Q p hkS y a θ), ← Finset.sum_mul]
    rfl

end

end Work.BMF.recursion
