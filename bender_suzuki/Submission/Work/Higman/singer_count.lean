import Mathlib
import Submission.Work.Higman.exists_singer_iso

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- **Counting a Singer cycle.**  Let `V` be a finite `𝔽₂`-vector space of cardinality `2 ^ n` with
`n ≥ 2`, and let `lam : V ≃ₗ[ZMod 2] V` act transitively on the non-zero vectors.  If
`(lam ^ k) w₀ = w₀` forces `lam ^ k = 1` for some non-zero `w₀`, then `lam` has order `2 ^ n - 1`
and no non-zero fixed vector. -/
theorem singer_count {n : ℕ} (hn : 2 ≤ n) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (hV : Nat.card V = 2 ^ n) (lam : V ≃ₗ[ZMod 2] V) (w₀ : V) (hw₀ : w₀ ≠ 0)
    (htrans : ∀ u w : V, u ≠ 0 → w ≠ 0 → ∃ k : ℕ, (lam ^ k) u = w)
    (hfix : ∀ k : ℕ, (lam ^ k) w₀ = w₀ → lam ^ k = 1) :
    orderOf lam = 2 ^ n - 1 ∧ (∀ v : V, lam v = v → v = 0) := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  -- The space of linear automorphisms is finite, so `lam` has finite order.
  haveI hfinEnd : Finite (V →ₗ[ZMod 2] V) :=
    Finite.of_injective (β := V → V) (fun f => (f : V → V)) (fun a b h => by simpa using h)
  haveI hfinAut : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (β := V →ₗ[ZMod 2] V) (LinearEquiv.toLinearMap)
      LinearEquiv.toLinearMap_injective
  set d := orderOf lam with hd
  have hdpos : 0 < d := by
    rw [hd]
    exact orderOf_pos_iff.mpr (isOfFinOrder_of_finite lam)
  have hd1 : lam ^ d = 1 := by rw [hd]; exact pow_orderOf_eq_one lam
  -- Powers of `w₀` are never zero.
  have hpow_ne : ∀ k : ℕ, (lam ^ k) w₀ ≠ 0 := by
    intro k h
    have h' : (lam ^ k).symm ((lam ^ k) w₀) = (lam ^ k).symm 0 := by rw [h]
    rw [LinearEquiv.symm_apply_apply, map_zero] at h'
    exact hw₀ h'
  -- Reduction of exponents modulo `d`.
  have hred : ∀ k : ℕ, lam ^ k = lam ^ (k % d) := by
    intro k
    conv_lhs => rw [← Nat.mod_add_div k d]
    rw [pow_add, pow_mul, hd1, one_pow, mul_one]
  -- The orbit map on one period `Fin d`.
  let g : Fin d → V := fun k => (lam ^ (k : ℕ)) w₀
  have hg_inj : Function.Injective g := by
    intro a b hab
    have hab' : (lam ^ (a : ℕ)) w₀ = (lam ^ (b : ℕ)) w₀ := hab
    rcases le_total (a : ℕ) (b : ℕ) with hle | hle
    · have hkey : lam ^ ((b : ℕ) - (a : ℕ)) = 1 := by
        apply hfix
        have h1 : (lam ^ (a : ℕ)) ((lam ^ ((b : ℕ) - (a : ℕ))) w₀) =
            (lam ^ (a : ℕ)) w₀ := by
          rw [← LinearEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
          exact hab'.symm
        exact (lam ^ (a : ℕ)).injective h1
      have hdv : d ∣ (b : ℕ) - (a : ℕ) := orderOf_dvd_iff_pow_eq_one.mpr hkey
      have hlt : (b : ℕ) - (a : ℕ) < d := lt_of_le_of_lt (Nat.sub_le _ _) b.isLt
      have hzero : (b : ℕ) - (a : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdv hlt
      exact Fin.ext (by omega)
    · have hkey : lam ^ ((a : ℕ) - (b : ℕ)) = 1 := by
        apply hfix
        have h1 : (lam ^ (b : ℕ)) ((lam ^ ((a : ℕ) - (b : ℕ))) w₀) =
            (lam ^ (b : ℕ)) w₀ := by
          rw [← LinearEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hle]
          exact hab'
        exact (lam ^ (b : ℕ)).injective h1
      have hdv : d ∣ (a : ℕ) - (b : ℕ) := orderOf_dvd_iff_pow_eq_one.mpr hkey
      have hlt : (a : ℕ) - (b : ℕ) < d := lt_of_le_of_lt (Nat.sub_le _ _) a.isLt
      have hzero : (a : ℕ) - (b : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdv hlt
      exact Fin.ext (by omega)
  -- Its range is exactly the set of non-zero vectors.
  have hrange : Set.range g = {v : V | v ≠ 0} := by
    ext v
    constructor
    · rintro ⟨k, rfl⟩
      exact hpow_ne k
    · intro hv
      obtain ⟨k, hk⟩ := htrans w₀ v hw₀ hv
      refine ⟨⟨k % d, Nat.mod_lt k hdpos⟩, ?_⟩
      show (lam ^ (k % d)) w₀ = v
      rw [← hred k]; exact hk
  have hncard : (Set.range g).ncard = d := by
    rw [Set.ncard_range_of_injective hg_inj, Nat.card_fin]
  have hcard0 : Nat.card {v : V // v ≠ 0} = 2 ^ n - 1 := by
    rw [Nat.card_eq_fintype_card]
    have hc := Fintype.card_subtype_compl (fun x : V => x = 0)
    rw [Fintype.card_subtype_eq (0 : V)] at hc
    rw [show Fintype.card {v : V // v ≠ 0} = Fintype.card V - 1 from by simpa using hc]
    rw [← Nat.card_eq_fintype_card, hV]
  have hd_eq : d = 2 ^ n - 1 := by
    have hncard2 : ({v : V | v ≠ 0} : Set V).ncard = d := by
      rw [← hrange]; exact hncard
    rw [← Nat.card_coe_set_eq ({v : V | v ≠ 0} : Set V)] at hncard2
    rw [hncard2.symm]
    exact hcard0
  have hno_fix : ∀ v : V, lam v = v → v = 0 := by
    intro v hv
    by_contra hne
    obtain ⟨k, hk⟩ := htrans w₀ v hw₀ hne
    have h1 : (lam ^ k) (lam w₀) = (lam ^ k) w₀ := by
      have hL : (lam ^ k) (lam w₀) = (lam ^ (k + 1)) w₀ := by
        rw [← LinearEquiv.mul_apply, ← pow_succ]
      have hRv : (lam ^ (k + 1)) w₀ = v := by
        rw [pow_succ', LinearEquiv.mul_apply, hk, hv]
      rw [hL, hRv, ← hk]
    have hlamw : lam w₀ = w₀ := (lam ^ k).injective h1
    have hlam1 : lam = 1 := by
      have h3 := hfix 1 (by rw [pow_one]; exact hlamw)
      rwa [pow_one] at h3
    have hbig : 2 ≤ 2 ^ n - 1 := by
      have hp : (2 : ℕ) ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have h4 : (4 : ℕ) ≤ 2 ^ n := by simpa using hp
      omega
    have hthis : orderOf lam = 1 := by rw [hlam1]; exact orderOf_one
    omega
  refine ⟨?_, hno_fix⟩
  exact hd_eq

end Work.Higman
