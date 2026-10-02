import Mathlib
import Submission.Work.ThomBordism.Grassmann.deg8Prelude
import Submission.Work.ThomBordism.Grassmann.deg8RankZero
import Submission.Work.ThomBordism.Grassmann.deg8PathConnectedOG
import Submission.Work.ThomBordism.Grassmann.degreeEightFinrankLeTwo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses
open scoped TensorProduct

universe u

noncomputable section

/-- `H^j(G̃r_k(ℝ^{k+m});ℚ)`. -/
abbrev RR (m j k : ℕ) : Type := Deg8.R m j k

/-! ## Cardinal helpers -/

theorem cardinal_add_one_le_one {c : Cardinal} (h : c + 1 ≤ 1) : c = 0 := by
  have hc : c ≤ 1 := le_trans (le_add_right le_rfl) h
  rcases lt_or_eq_of_le hc with hlt | heq
  · exact Cardinal.lt_one_iff.mp hlt
  · exfalso
    rw [heq] at h
    exact absurd h (by norm_num)

theorem cardinal_eq_zero_of_le_zero {c : Cardinal} (h : c ≤ 0) : c = 0 :=
  le_antisymm h (zero_le : (0 : Cardinal) ≤ c)

theorem cardinal_eq_zero_of_add_le_of_le_one {c d : Cardinal} (h : c + d ≤ d) (hd : d ≤ 1) :
    c = 0 := by
  rcases lt_or_eq_of_le hd with hlt | heq
  · have hd0 : d = 0 := Cardinal.lt_one_iff.mp hlt
    rw [hd0, add_zero] at h
    exact cardinal_eq_zero_of_le_zero h
  · rw [heq] at h
    exact cardinal_add_one_le_one h

theorem cardinal_eq_zero_of_le_of_eq_zero {a b : Cardinal} (h : a ≤ b) (hb : b = 0) : a = 0 :=
  cardinal_eq_zero_of_le_zero (le_trans h (le_of_eq hb))

/-! ## Short exact sequences -/

theorem rank_add_eq_of_shortExact {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [AddCommGroup V₂]
    [AddCommGroup V₃] [Module ℚ V₁] [Module ℚ V₂] [Module ℚ V₃]
    (f : V₁ →ₗ[ℚ] V₂) (g : V₂ →ₗ[ℚ] V₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) :
    Module.rank ℚ V₂ = Module.rank ℚ V₁ + Module.rank ℚ V₃ := by
  have hker : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp h
  have h1 : Module.rank ℚ (LinearMap.range f) = Module.rank ℚ V₁ := rank_range_of_injective f hf
  have h2 : Module.rank ℚ (LinearMap.range g) = Module.rank ℚ V₃ := rank_range_of_surjective g hg
  rw [← h1, ← h2, ← hker, add_comm]
  exact (LinearMap.rank_range_add_rank_ker g).symm

/-! ## The rank bookkeeping -/

theorem rankH0 (m k : ℕ) (hm : 1 ≤ m) : Module.rank ℚ (RR m 0 k) = 1 := by
  haveI := deg8PathConnectedOG k m hm
  exact deg8RankZero (OG k m)

theorem rankH0_zero (m j : ℕ) (hj1 : 1 ≤ j) : Module.rank ℚ (RR m j 0) = 0 := by
  haveI : Subsingleton (OG 0 m) := subsingleton_OG_zero m
  haveI : ContractibleSpace (OG 0 m) := inferInstance
  have hz : CategoryTheory.Limits.IsZero
      (Work.Cohomology.singularCohomology ℤ j (TopCat.of (OG 0 m))) := by
    have h := Work.Cohomology.contractible ℤ (TopCat.of (OG 0 m)) (j - 1)
    rwa [Nat.sub_add_cancel hj1] at h
  haveI hs : Subsingleton (↥(Work.Cohomology.singularCohomology ℤ j (TopCat.of (OG 0 m)))) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  haveI hsub : Subsingleton (RR m j 0) := by
    change Subsingleton (ℚ ⊗[ℤ] ↥(Work.Cohomology.singularCohomology ℤ j (TopCat.of (OG 0 m))))
    have hzero : ∀ x : ℚ ⊗[ℤ] ↥(Work.Cohomology.singularCohomology ℤ j (TopCat.of (OG 0 m))),
        x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul q a => rw [Subsingleton.elim a 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  exact (rank_eq_zero_iff (R := ℚ)).mpr
    (fun x => ⟨1, one_ne_zero, by rw [one_smul]; exact Subsingleton.elim x 0⟩)

theorem rankDesc (m j k : ℕ) (hj : j + 2 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k + m - 3) :
    Module.rank ℚ (RR m j k) = Module.rank ℚ (RR m j (k - 1)) :=
  Deg8.rank_eq_of_descent k m j hj ▸ Deg8.rank_S_eq_R k m j (by omega) hj1 hjk

theorem rankInj (m j k : ℕ) (hjk : j < k) (hj1 : 1 ≤ j) (hj : j ≤ k + m - 3) :
    Module.rank ℚ (RR m j k) ≤ Module.rank ℚ (RR m j (k - 1)) := by
  have hinj : Function.Injective (Deg8.gysinπQ (tautologicalBundle k m) j) := by
    have h0 : Function.Injective (Work.Thom.gysinπ (tautologicalBundle k m) j) :=
      Deg8.injective_gysinπ_tautological k m j hjk
    have h1 : Function.Injective ((Work.Thom.gysinπ (tautologicalBundle k m) j).lTensor ℚ) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ h0
    rwa [← LinearMap.baseChange_eq_ltensor] at h1
  have h2 : Module.rank ℚ (RR m j k) ≤ Module.rank ℚ (Deg8.S m j k) := by
    change Module.rank ℚ (ℚ ⊗[ℤ] ↑(Work.Thom.Coh ℤ j (OG k m))) ≤
      Module.rank ℚ (ℚ ⊗[ℤ] ↑(Work.Thom.Coh ℤ j
        (Work.Thom.zeroComplement (tautologicalBundle k m))))
    rw [← rank_range_of_injective _ hinj]
    exact Submodule.rank_le _
  rw [← Deg8.rank_S_eq_R k m j (by omega) hj1 hj]
  exact h2

theorem rankWin (m j k : ℕ) (hk1 : 1 ≤ k) (hkj : k ≤ j) (hj1 : 1 ≤ j)
    (hj : j ≤ k + m - 3) :
    Module.rank ℚ (RR m j k) ≤ Module.rank ℚ (RR m (j - k) k) + Module.rank ℚ (RR m j (k - 1)) := by
  have h := Deg8.win_le k m j hkj
  rwa [Deg8.rank_S_eq_R k m j hk1 hj1 hj] at h

/-- The odd window, in the form used below. -/
theorem rankOdd (m a k : ℕ) (hk1 : 1 ≤ k) (hodd : Odd k)
    (ha : 1 ≤ a + k) (hb : a + k ≤ k + m - 3) (hc : 1 ≤ a + 1) (hd : a + 1 ≤ k + m - 3) :
    Module.rank ℚ (RR m (a + k) (k - 1)) = Module.rank ℚ (RR m (a + k) k)
      + Module.rank ℚ (RR m (a + 1) k) := by
  have hT : (2 : ℤ) • (tautologicalThomClass k m).eulerClass = 0 :=
    eulerClassOddRank (tautologicalBundle k m) (by simp [RealBundle.rank])
      (tautologicalThomClass k m) hodd
  have hz : Deg8.gysinEulerQ (tautologicalBundle k m) k (tautologicalThomClass k m) a = 0 :=
    Deg8.gysinEulerQ_eq_zero_of_two_zsmul (tautologicalBundle k m) k a
      (tautologicalThomClass k m) hT
  have hz' : Deg8.gysinEulerQ (tautologicalBundle k m) k (tautologicalThomClass k m) (a + 1) = 0 :=
    Deg8.gysinEulerQ_eq_zero_of_two_zsmul (tautologicalBundle k m) k (a + 1)
      (tautologicalThomClass k m) hT
  have hexb := Deg8.gysin_exact_at_base_rat (tautologicalBundle k m) k
    (tautologicalThomClass k m) a
  rw [hz] at hexb
  have hinj : Function.Injective (Deg8.gysinπQ (tautologicalBundle k m) (a + k)) := by
    rw [LinearMap.exact_iff] at hexb
    rw [LinearMap.range_zero] at hexb
    exact LinearMap.ker_eq_bot.mp hexb
  have hexc := Deg8.gysin_exact_at_cobase_rat (tautologicalBundle k m) k
    (tautologicalThomClass k m) a
  rw [hz'] at hexc
  rw [LinearMap.exact_iff, LinearMap.ker_zero] at hexc
  have hsurj : Function.Surjective (Deg8.gysinδQ (tautologicalBundle k m) k
      (tautologicalThomClass k m) a) := LinearMap.range_eq_top.mp hexc.symm
  have hexs := Deg8.gysin_exact_at_sphere_rat (tautologicalBundle k m) k
    (tautologicalThomClass k m) a
  have hrank := rank_add_eq_of_shortExact
    (Deg8.gysinπQ (tautologicalBundle k m) (a + k))
    (Deg8.gysinδQ (tautologicalBundle k m) k (tautologicalThomClass k m) a) hinj hsurj hexs
  rw [← Deg8.rank_S_eq_R k m (a + k) hk1 ha hb]
  exact hrank

/-- **The low window for odd `k`.** -/
theorem rankLowOdd (m k : ℕ) (hm : 2 ≤ m) (hk1 : 2 ≤ k) (hodd : Odd k) :
    Module.rank ℚ (RR m (k - 1) (k - 1))
      = Module.rank ℚ (RR m (k - 1) k) + Module.rank ℚ (RR m 0 k) := by
  rw [← Deg8.rank_S_eq_R k m (k - 1) (by omega) (by omega) (by omega)]
  exact Deg8.rank_S_degen k m hk1 hodd

/-- Transfer of the rank down the stable range. -/
theorem rankTransfer (m j K k : ℕ) (hm : 1 ≤ m) (hj1 : 1 ≤ j) (hJK : j + 1 ≤ K)
    (hKk : K ≤ k) :
    Module.rank ℚ (RR m j k) = Module.rank ℚ (RR m j K) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hKk
  have hle : ∀ t, Module.rank ℚ (RR m j (K + t)) = Module.rank ℚ (RR m j K) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        have hstep : Module.rank ℚ (RR m j (K + (t + 1))) = Module.rank ℚ (RR m j (K + t)) := by
          rw [show K + (t + 1) = K + t + 1 from by omega]
          exact rankDesc m j (K + t + 1) (by omega) hj1 (by omega)
        rw [hstep]
        exact ih
  exact hle d

/-! ## The odd windows in the shapes used below -/

theorem odd_3_0 (m : ℕ) (hm : 10 ≤ m) :
    Module.rank ℚ (RR m 3 2) = Module.rank ℚ (RR m 3 3) + Module.rank ℚ (RR m 1 3) :=
  rankOdd m 0 3 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)

theorem odd_4_1 (m : ℕ) (hm : 10 ≤ m) :
    Module.rank ℚ (RR m 4 2) = Module.rank ℚ (RR m 4 3) + Module.rank ℚ (RR m 2 3) :=
  rankOdd m 1 3 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)

theorem odd_5_2 (m : ℕ) (hm : 10 ≤ m) :
    Module.rank ℚ (RR m 5 2) = Module.rank ℚ (RR m 5 3) + Module.rank ℚ (RR m 3 3) :=
  rankOdd m 2 3 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)

theorem odd_6_3 (m : ℕ) (hm : 10 ≤ m) :
    Module.rank ℚ (RR m 6 2) = Module.rank ℚ (RR m 6 3) + Module.rank ℚ (RR m 4 3) :=
  rankOdd m 3 3 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)

theorem odd_7_4 (m : ℕ) (hm : 10 ≤ m) :
    Module.rank ℚ (RR m 7 2) = Module.rank ℚ (RR m 7 3) + Module.rank ℚ (RR m 5 3) :=
  rankOdd m 4 3 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)

theorem odd_5_0 (m : ℕ) (hm : 10 ≤ m) :
    Module.rank ℚ (RR m 5 4) = Module.rank ℚ (RR m 5 5) + Module.rank ℚ (RR m 1 5) :=
  rankOdd m 0 5 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)

theorem odd_7_2 (m : ℕ) (hm : 10 ≤ m) :
    Module.rank ℚ (RR m 7 4) = Module.rank ℚ (RR m 7 5) + Module.rank ℚ (RR m 3 5) :=
  rankOdd m 2 5 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)

theorem odd_7_0 (m : ℕ) (hm : 10 ≤ m) :
    Module.rank ℚ (RR m 7 6) = Module.rank ℚ (RR m 7 7) + Module.rank ℚ (RR m 1 7) :=
  rankOdd m 0 7 (by norm_num) (by norm_num) (by omega) (by omega) (by omega) (by omega)



/-! ## The six chains -/

/-- **`H^1` vanishes.** -/
theorem rank_H1 (m : ℕ) (hm : 10 ≤ m) (k : ℕ) : Module.rank ℚ (RR m 1 k) = 0 := by
  rcases lt_or_ge k 3 with h | h
  · interval_cases k
    · exact rankH0_zero m 1 (by norm_num)
    · exact Deg8.rank_one_eq_zero m 1 (by norm_num) (by omega)
    · exact cardinal_eq_zero_of_le_of_eq_zero
        (rankInj m 1 2 (by norm_num) (by norm_num) (by omega))
        (Deg8.rank_one_eq_zero m 1 (by norm_num) (by omega))
  · rw [rankTransfer m 1 3 k (by omega) (by norm_num) (by norm_num) (by omega)]
    exact cardinal_eq_zero_of_le_of_eq_zero
      (le_trans (rankInj m 1 3 (by norm_num) (by norm_num) (by omega))
        (rankInj m 1 2 (by norm_num) (by norm_num) (by omega)))
      (Deg8.rank_one_eq_zero m 1 (by norm_num) (by omega))

/-- **`H^2(G̃r_3;ℚ) = 0`**: the low window at `k = 3`. -/
theorem rank_2_3 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 2 3) = 0 := by
  have h22 : Module.rank ℚ (RR m 2 2) ≤ 1 := by
    have hw : Module.rank ℚ (RR m 2 2) ≤ Module.rank ℚ (RR m 0 2) + Module.rank ℚ (RR m 2 1) :=
      rankWin m 2 2 (by norm_num) (by norm_num) (by norm_num) (by omega)
    rw [rankH0 m 2 (by omega), Deg8.rank_one_eq_zero m 2 (by norm_num) (by omega),
      add_zero] at hw
    exact hw
  have hlow := rankLowOdd m 3 (by omega) (by norm_num) (by norm_num)
  rw [rankH0 m 3 (by omega)] at hlow
  exact cardinal_add_one_le_one (le_trans (le_of_eq hlow.symm) h22)

/-- **`H^2` vanishes.** -/
theorem rank_H2 (m : ℕ) (hm : 10 ≤ m) (k : ℕ) (hk : 3 ≤ k) : Module.rank ℚ (RR m 2 k) = 0 := by
  rw [rankTransfer m 2 3 k (by omega) (by norm_num) (by norm_num) (by omega)]
  exact rank_2_3 m hm

/-- **`H^3(G̃r_2;ℚ) = 0`**: the window at `(3,2)`. -/
theorem rank_3_2 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 3 2) = 0 := by
  have hw : Module.rank ℚ (RR m 3 2) ≤ Module.rank ℚ (RR m 1 2) + Module.rank ℚ (RR m 3 1) :=
    rankWin m 3 2 (by norm_num) (by norm_num) (by norm_num) (by omega)
  rw [rank_H1 m hm 2, Deg8.rank_one_eq_zero m 3 (by norm_num) (by omega), zero_add] at hw
  exact cardinal_eq_zero_of_le_zero hw

/-- **`H^3(G̃r_3;ℚ) = 0`**: the odd window at `k = 3`. -/
theorem rank_3_3 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 3 3) = 0 := by
  have hodd := odd_3_0 m hm
  refine cardinal_eq_zero_of_le_of_eq_zero ?_ (rank_3_2 m hm)
  rw [hodd]
  exact le_add_of_nonneg_right zero_le

/-- **`H^3` vanishes.** -/
theorem rank_H3 (m : ℕ) (hm : 10 ≤ m) (k : ℕ) (hk : 4 ≤ k) : Module.rank ℚ (RR m 3 k) = 0 := by
  rw [rankTransfer m 3 4 k (by omega) (by norm_num) (by norm_num) (by omega)]
  exact cardinal_eq_zero_of_le_of_eq_zero
    (rankInj m 3 4 (by norm_num) (by norm_num) (by omega)) (rank_3_3 m hm)

/-- **`H^5(G̃r_2;ℚ) = 0`**. -/
theorem rank_5_2 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 5 2) = 0 := by
  have hw : Module.rank ℚ (RR m 5 2) ≤ Module.rank ℚ (RR m 3 2) + Module.rank ℚ (RR m 5 1) :=
    rankWin m 5 2 (by norm_num) (by norm_num) (by norm_num) (by omega)
  rw [rank_3_2 m hm, Deg8.rank_one_eq_zero m 5 (by norm_num) (by omega), zero_add] at hw
  exact cardinal_eq_zero_of_le_zero hw

/-- **`H^5(G̃r_3;ℚ) = 0`**. -/
theorem rank_5_3 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 5 3) = 0 := by
  have hodd := odd_5_2 m hm
  refine cardinal_eq_zero_of_le_of_eq_zero ?_ (rank_5_2 m hm)
  rw [hodd]
  exact le_add_of_nonneg_right zero_le

/-- **`H^5(G̃r_4;ℚ) = 0`**. -/
theorem rank_5_4 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 5 4) = 0 := by
  have hw : Module.rank ℚ (RR m 5 4) ≤ Module.rank ℚ (RR m 1 4) + Module.rank ℚ (RR m 5 3) :=
    rankWin m 5 4 (by norm_num) (by norm_num) (by norm_num) (by omega)
  rw [rank_H1 m hm 4, zero_add] at hw
  exact cardinal_eq_zero_of_le_of_eq_zero hw (rank_5_3 m hm)

/-- **`H^5(G̃r_5;ℚ) = 0`**. -/
theorem rank_5_5 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 5 5) = 0 := by
  have hodd := odd_5_0 m hm
  refine cardinal_eq_zero_of_le_of_eq_zero ?_ (rank_5_4 m hm)
  rw [hodd]
  exact le_add_of_nonneg_right zero_le

/-- **`H^5` vanishes.** -/
theorem rank_H5 (m : ℕ) (hm : 10 ≤ m) (k : ℕ) (hk : 6 ≤ k) : Module.rank ℚ (RR m 5 k) = 0 := by
  rw [rankTransfer m 5 6 k (by omega) (by norm_num) (by norm_num) (by omega)]
  exact cardinal_eq_zero_of_le_of_eq_zero
    (rankInj m 5 6 (by norm_num) (by norm_num) (by omega)) (rank_5_5 m hm)

/-- **`H^6(G̃r_3;ℚ) = 0`**. -/
theorem rank_6_3 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 6 3) = 0 := by
  have h42 : Module.rank ℚ (RR m 4 2) ≤ 1 := by
    have hw : Module.rank ℚ (RR m 4 2) ≤ Module.rank ℚ (RR m 2 2) + Module.rank ℚ (RR m 4 1) :=
      rankWin m 4 2 (by norm_num) (by norm_num) (by norm_num) (by omega)
    have h22 : Module.rank ℚ (RR m 2 2) ≤ 1 := by
      have hw' : Module.rank ℚ (RR m 2 2) ≤ Module.rank ℚ (RR m 0 2) + Module.rank ℚ (RR m 2 1) :=
        rankWin m 2 2 (by norm_num) (by norm_num) (by norm_num) (by omega)
      rw [rankH0 m 2 (by omega), Deg8.rank_one_eq_zero m 2 (by norm_num) (by omega),
        add_zero] at hw'
      exact hw'
    rw [Deg8.rank_one_eq_zero m 4 (by norm_num) (by omega), add_zero] at hw
    exact le_trans hw h22
  have h43 : Module.rank ℚ (RR m 4 2) = Module.rank ℚ (RR m 4 3) := by
    have hodd := odd_4_1 m hm
    rw [rank_2_3 m hm, add_zero] at hodd
    exact hodd
  have h62 : Module.rank ℚ (RR m 6 2) ≤ Module.rank ℚ (RR m 4 2) := by
    have hw : Module.rank ℚ (RR m 6 2) ≤ Module.rank ℚ (RR m 4 2) + Module.rank ℚ (RR m 6 1) :=
      rankWin m 6 2 (by norm_num) (by norm_num) (by norm_num) (by omega)
    rw [Deg8.rank_one_eq_zero m 6 (by norm_num) (by omega), add_zero] at hw
    exact hw
  have h63 := odd_6_3 m hm
  have hle : Module.rank ℚ (RR m 6 3) + Module.rank ℚ (RR m 4 3) ≤ Module.rank ℚ (RR m 4 3) :=
    le_trans (le_of_eq h63.symm) (le_trans h62 (le_of_eq h43))
  have hd : Module.rank ℚ (RR m 4 3) ≤ 1 := h43 ▸ h42
  exact cardinal_eq_zero_of_add_le_of_le_one hle hd

/-- **`H^6(G̃r_4;ℚ) = 0`**. -/
theorem rank_6_4 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 6 4) = 0 := by
  have hw : Module.rank ℚ (RR m 6 4) ≤ Module.rank ℚ (RR m 2 4) + Module.rank ℚ (RR m 6 3) :=
    rankWin m 6 4 (by norm_num) (by norm_num) (by norm_num) (by omega)
  rw [rank_H2 m hm 4 (by norm_num), zero_add] at hw
  exact cardinal_eq_zero_of_le_of_eq_zero hw (rank_6_3 m hm)

/-- **`H^6(G̃r_5;ℚ) = 0`**. -/
theorem rank_6_5 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 6 5) = 0 := by
  have hw : Module.rank ℚ (RR m 6 5) ≤ Module.rank ℚ (RR m 1 5) + Module.rank ℚ (RR m 6 4) :=
    rankWin m 6 5 (by norm_num) (by norm_num) (by norm_num) (by omega)
  rw [rank_H1 m hm 5, zero_add] at hw
  exact cardinal_eq_zero_of_le_of_eq_zero hw (rank_6_4 m hm)

/-- **`H^6(G̃r_6;ℚ) ≤ 1`**. -/
theorem rank_6_6_le (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 6 6) ≤ 1 := by
  have hw : Module.rank ℚ (RR m 6 6) ≤ Module.rank ℚ (RR m 0 6) + Module.rank ℚ (RR m 6 5) :=
    rankWin m 6 6 (by norm_num) (by norm_num) (by norm_num) (by omega)
  rw [rankH0 m 6 (by omega), rank_6_5 m hm, add_zero] at hw
  exact hw

/-- **`H^6(G̃r_7;ℚ) = 0`**: the low window at `k = 7`. -/
theorem rank_6_7 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 6 7) = 0 := by
  have hlow := rankLowOdd m 7 (by omega) (by norm_num) (by norm_num)
  rw [rankH0 m 7 (by omega)] at hlow
  exact cardinal_add_one_le_one (le_trans (le_of_eq hlow.symm) (rank_6_6_le m hm))

/-- **`H^6` vanishes.** -/
theorem rank_H6 (m : ℕ) (hm : 10 ≤ m) (k : ℕ) (hk : 8 ≤ k) : Module.rank ℚ (RR m 6 k) = 0 := by
  rw [rankTransfer m 6 8 k (by omega) (by norm_num) (by norm_num) (by omega)]
  exact cardinal_eq_zero_of_le_of_eq_zero
    (rankInj m 6 8 (by norm_num) (by norm_num) (by omega)) (rank_6_7 m hm)

/-- **`H^7(G̃r_2;ℚ) = 0`**. -/
theorem rank_7_2 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 7 2) = 0 := by
  have hw : Module.rank ℚ (RR m 7 2) ≤ Module.rank ℚ (RR m 5 2) + Module.rank ℚ (RR m 7 1) :=
    rankWin m 7 2 (by norm_num) (by norm_num) (by norm_num) (by omega)
  rw [rank_5_2 m hm, Deg8.rank_one_eq_zero m 7 (by norm_num) (by omega), zero_add] at hw
  exact cardinal_eq_zero_of_le_zero hw

/-- **`H^7(G̃r_3;ℚ) = 0`**. -/
theorem rank_7_3 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 7 3) = 0 := by
  have hodd := odd_7_4 m hm
  refine cardinal_eq_zero_of_le_of_eq_zero ?_ (rank_7_2 m hm)
  rw [hodd]
  exact le_add_of_nonneg_right zero_le

/-- **`H^7(G̃r_4;ℚ) = 0`**. -/
theorem rank_7_4 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 7 4) = 0 := by
  have hw : Module.rank ℚ (RR m 7 4) ≤ Module.rank ℚ (RR m 3 4) + Module.rank ℚ (RR m 7 3) :=
    rankWin m 7 4 (by norm_num) (by norm_num) (by norm_num) (by omega)
  rw [rank_7_3 m hm, add_zero] at hw
  exact cardinal_eq_zero_of_le_of_eq_zero hw (rank_H3 m hm 4 (by norm_num))

/-- **`H^7(G̃r_5;ℚ) = 0`**. -/
theorem rank_7_5 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 7 5) = 0 := by
  have hodd := odd_7_2 m hm
  refine cardinal_eq_zero_of_le_of_eq_zero ?_ (rank_7_4 m hm)
  rw [hodd]
  exact le_add_of_nonneg_right zero_le

/-- **`H^7(G̃r_6;ℚ) = 0`**. -/
theorem rank_7_6 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 7 6) = 0 := by
  have hw : Module.rank ℚ (RR m 7 6) ≤ Module.rank ℚ (RR m 1 6) + Module.rank ℚ (RR m 7 5) :=
    rankWin m 7 6 (by norm_num) (by norm_num) (by norm_num) (by omega)
  rw [rank_H1 m hm 6, zero_add] at hw
  exact cardinal_eq_zero_of_le_of_eq_zero hw (rank_7_5 m hm)

/-- **`H^7(G̃r_7;ℚ) = 0`**. -/
theorem rank_7_7 (m : ℕ) (hm : 10 ≤ m) : Module.rank ℚ (RR m 7 7) = 0 := by
  have hodd := odd_7_0 m hm
  refine cardinal_eq_zero_of_le_of_eq_zero ?_ (rank_7_6 m hm)
  rw [hodd]
  exact le_add_of_nonneg_right zero_le

/-- **`H^7` vanishes.** -/
theorem rank_H7 (m : ℕ) (hm : 10 ≤ m) (k : ℕ) (hk : 9 ≤ k) : Module.rank ℚ (RR m 7 k) = 0 := by
  rw [rankTransfer m 7 9 k (by omega) (by norm_num) (by norm_num) (by omega)]
  exact cardinal_eq_zero_of_le_of_eq_zero
    (le_trans (rankInj m 7 9 (by norm_num) (by norm_num) (by omega))
      (rankInj m 7 8 (by norm_num) (by norm_num) (by omega))) (rank_7_7 m hm)

/-! ## The target -/

theorem grassmannianLowDegreeVanishing (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    ∀ j ∈ Work.ThomBordism.Grassmann.lowDegrees,
      Subsingleton (Work.SignatureBordism.ratCohomology j (Work.ThomBordism.Grassmann.sset (Work.ThomBordism.Grassmann.OG k m))) := by
  intro j hj
  have hm1 : 1 ≤ m := by omega
  have hj1 : 1 ≤ j := by
    simp only [lowDegrees, Finset.mem_insert, Finset.mem_singleton] at hj
    omega
  have hjmax : j + 1 ≤ 10 := by
    simp only [lowDegrees, Finset.mem_insert, Finset.mem_singleton] at hj
    omega
  have hrank : Module.rank ℚ (RR m j k) = 0 := by
    rw [rankTransfer m j 10 k hm1 hj1 hjmax (by omega)]
    simp only [lowDegrees, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact rank_H1 m hm 10
    · exact rank_H2 m hm 10 (by norm_num)
    · exact rank_H3 m hm 10 (by norm_num)
    · exact rank_H5 m hm 10 (by norm_num)
    · exact rank_H6 m hm 10 (by norm_num)
    · exact rank_H7 m hm 10 (by norm_num)
  have hx0 : ∀ x : RR m j k, x = 0 := by
    intro x
    obtain ⟨a, ha, hax⟩ := (rank_eq_zero_iff (R := ℚ)).mp hrank x
    calc x = a⁻¹ • (a • x) := (inv_smul_smul₀ ha x).symm
      _ = 0 := by rw [hax, smul_zero]
  exact ⟨fun x y => (hx0 x).trans (hx0 y).symm⟩

end

end Work.ThomBordism.Grassmann
