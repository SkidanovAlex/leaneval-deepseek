import Mathlib
import Submission.Work.ORHughesFree.Prop51
import Submission.Work.ORHughesFree.Tree.Log
import Submission.Work.ORHughesFree.Prop51.coeff_zpowT
import Submission.Work.ORHughesFree.Prop51.treeH_ofGroup

namespace Work.ORHughesFree.Prop51

variable {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
  [MulSemiringAction (Multiplicative ℤ) ↥DN]

/-- For `n : ℕ`, the element `t ^ n` of `Γ` maps under `Φ` to the `n`-th power of the variable
`t` of `D_{N,P}((t;τ))`. -/
theorem Φ_ofGroup_t_pow (d : Prop51Data Γ P DN) (n : ℕ) :
    d.Φ (RatU.ofGroup (d.t ^ (n : ℤ))) =
      d.laurentEmbed ↑(skewLaurentSeriesT ↥DN ^ (n : ℤ)) := by
  rw [zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, skewLaurentSeriesT_coe,
    show RatU.ofGroup (d.t ^ n) = (RatU.ofGroupHom d.t) ^ n from
      map_pow RatU.ofGroupHom d.t n,
    map_pow, RatU.ofGroupHom_apply, d.Φ_t, skewLaurentSeriesT_coe, map_pow]

/-- If `Φ` carries `t ^ (-k)` to the `(-k)`-th power of the variable, then it carries `t ^ k` to
the `k`-th power: both `Φ (ofGroup (t ^ k))` and the variable power are two-sided inverses of the
same element, and two-sided inverses in a monoid are unique. -/
theorem Φ_ofGroup_t_zpow_of_neg (d : Prop51Data Γ P DN) (k : ℤ)
    (h : d.Φ (RatU.ofGroup (d.t ^ (-k))) =
      d.laurentEmbed ↑(skewLaurentSeriesT ↥DN ^ (-k))) :
    d.Φ (RatU.ofGroup (d.t ^ k)) = d.laurentEmbed ↑(skewLaurentSeriesT ↥DN ^ k) := by
  have h1 : d.Φ (RatU.ofGroup (d.t ^ k)) * d.Φ (RatU.ofGroup (d.t ^ (-k))) = 1 := by
    rw [← map_mul, ← RatU.ofGroup_mul, ← zpow_add, add_neg_cancel, zpow_zero, RatU.ofGroup_one,
      map_one]
  have h2 : d.laurentEmbed ↑(skewLaurentSeriesT ↥DN ^ (-k)) *
      d.laurentEmbed ↑(skewLaurentSeriesT ↥DN ^ k) = 1 := by
    rw [← map_mul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, map_one]
  rw [← mul_one (d.Φ (RatU.ofGroup (d.t ^ k))), ← h2, ← mul_assoc, ← h, h1, one_mul]

/-- The `t`-part of condition (iii): `Φ` carries the cyclic subgroup `⟨t⟩` into the variable of
`D_{N,P}((t;τ))`. -/
theorem Φ_ofGroup_t_zpow (d : Prop51Data Γ P DN) (k : ℤ) :
    d.Φ (RatU.ofGroup (d.t ^ k)) = d.laurentEmbed ↑(skewLaurentSeriesT ↥DN ^ k) := by
  rcases le_or_gt 0 k with hk | hk
  · have hk' : ((k.natAbs : ℕ) : ℤ) = k := Int.natAbs_of_nonneg hk
    rw [← hk']
    exact Φ_ofGroup_t_pow d k.natAbs
  · have hk' : ((k.natAbs : ℕ) : ℤ) = -k := by
      have h := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ -k by omega)
      rwa [Int.natAbs_neg] at h
    have hk'' : k = -(((k.natAbs : ℕ)) : ℤ) := by omega
    rw [hk'']
    exact Φ_ofGroup_t_zpow_of_neg d (-(((k.natAbs : ℕ)) : ℤ)) (by
      rw [neg_neg]
      exact Φ_ofGroup_t_pow d k.natAbs)

theorem base_case {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    (u n : Γ) (k : ℤ) (hn : n ∈ d.N) (hu : u = n * d.t ^ k) :
    ∃ f : Work.ORHughesFree.SkewLaurentSeries ↥DN,
      d.laurentEmbed f = d.Φ (Work.ORHughesFree.RatU.ofGroup u) ∧
      (∀ m : ℤ, f.1 m ≠ 0 →
        Work.ORHughesFree.Tree.le (d.treeH (d.coeffToP (f.1 m)))
          (d.treeH (d.Φ (Work.ORHughesFree.RatU.ofGroup u)))) ∧
      (∀ m : ℤ, d.treeH (d.coeffToP (f.1 m)) =
          d.treeH (d.Φ (Work.ORHughesFree.RatU.ofGroup u)) → ∀ j : ℤ, j ≠ m → f.1 j = 0) := by
  refine ⟨skewLaurentCoeff ↥DN ⟨d.Φ (RatU.ofGroup n), d.Φ_N n hn⟩ *
      ↑(skewLaurentSeriesT ↥DN ^ k), ?_, ?_, ?_⟩
  · rw [map_mul, d.laurentEmbed_coeff]
    have hc : (((⟨d.Φ (RatU.ofGroup n), d.Φ_N n hn⟩ : ↥DN)) : P) = d.Φ (RatU.ofGroup n) := rfl
    rw [hc, ← Φ_ofGroup_t_zpow d k, ← map_mul, ← RatU.ofGroup_mul, hu]
  · intro m hm
    have hmk : m = k := by
      by_contra hne
      refine hm ?_
      rw [coeff_zpowT, if_neg hne]
    subst hmk
    rw [coeff_zpowT, if_pos rfl]
    have hc : d.coeffToP (⟨d.Φ (RatU.ofGroup n), d.Φ_N n hn⟩ : ↥DN) =
        d.Φ (RatU.ofGroup n) := rfl
    rw [hc, treeH_ofGroup d n, treeH_ofGroup d u]
    exact Tree.le_refl 1
  · intro m hm j hj
    have hmk : m = k := by
      by_contra hne
      have h0 : (skewLaurentCoeff ↥DN ⟨d.Φ (RatU.ofGroup n), d.Φ_N n hn⟩ *
          ↑(skewLaurentSeriesT ↥DN ^ k)).1 m = 0 := by rw [coeff_zpowT, if_neg hne]
      rw [h0] at hm
      have hz : d.treeH (d.coeffToP (0 : ↥DN)) = 0 := by
        have hc0 : d.coeffToP (0 : ↥DN) = 0 := rfl
        rw [hc0]
        exact (d.treeH_eq_zero_iff d.DH.zero_mem).mpr rfl
      rw [hz, treeH_ofGroup d u] at hm
      exact Tree.one_ne_zero hm.symm
    rw [coeff_zpowT, if_neg (fun h => hj (h.trans hmk.symm))]

end Work.ORHughesFree.Prop51
