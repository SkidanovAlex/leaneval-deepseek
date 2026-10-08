/-
Gorenstein–Walter / Bender–Glauberman, area BG: the fusion leaf
`Work.BG.not_conj_t1_t2_in_S`.

For `D : Work.GW2.BGData G` (Bender–Glauberman Hypothesis 1.1) the two involutions
`t₁, t₂ ∈ S ∖ S₀` are **not** conjugate inside the Sylow 2-subgroup `S`:

  `¬ ∃ g ∈ S, g * t₁ * g⁻¹ = t₂`.

Mathematical content.  Put `a = t₁t₂`, so that `S₀ = ⟨a⟩`, `t₂ = t₁a`, `t₁a t₁ = a⁻¹`
and `|S : S₀| = 2`.  Two things happen:

* **`a` has even order.**  `t ∈ S₀ = ⟨a⟩` is an involution, say `t = a^k`; then
  `a ^ (orderOf a)` is trivial, so `2 = orderOf t ∣ orderOf a`.  (This is the only place
  where the involution `t ∈ S₀` – and hence the dihedral shape of `S` – is used.)
* **`t₁` and `t₂` live in different `S`-classes.**  Since `S₀` has index two in `S`,
  every `g ∈ S` is either in `S₀` or of the shape `u t₁` with `u ∈ S₀`; in both cases
  `g t₁ g⁻¹ = u t₁ u⁻¹`, and for `u = a^j` one computes `u t₁ u⁻¹ = t₁ a^{-2j}`.
  So `g t₁ g⁻¹ = t₂ = t₁ a` would force `a^{-2j} = a`, i.e. `a^{-2j-1} = 1`, hence
  `orderOf a ∣ 2j+1` – impossible because `orderOf a` is even while `2j+1` is odd.

The two auxiliary lemmas below are pure group theory (no dihedral hypothesis).
-/
import Mathlib
import Submission.Work.GLUE.Defs
import Submission.Work.BG.indexOdd

namespace Work.BG

/-- If `t` is an involution inverting `a` (that is `t * a * t = a⁻¹`), then conjugating the
element `a ^ j` past `t` costs a factor `a ^ (-(2 * j))`:
`a ^ j * t * (a ^ j)⁻¹ = t * a ^ (-(2 * j))`. -/
private lemma conj_zpow_inv_eq {G : Type*} [Group G] {a t : G} (ht : t * t = 1)
    (hinv : t * a * t = a⁻¹) (j : ℤ) :
    a ^ j * t * (a ^ j)⁻¹ = t * a ^ (-(2 * j)) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hconj : MulAut.conj t a = a⁻¹ := by
    rw [MulAut.conj_apply, hti, hinv]
  -- conjugation by `t` sends every power of `a` to the opposite power
  have key : ∀ n : ℤ, a ^ n * t = t * a ^ (-n) := by
    intro n
    have h1 : t * a ^ n * t = a ^ (-n) := by
      have h2 : MulAut.conj t (a ^ n) = a ^ (-n) := by
        rw [map_zpow, hconj, inv_zpow, zpow_neg]
      rwa [MulAut.conj_apply, hti] at h2
    calc a ^ n * t = (t * t) * (a ^ n * t) := by rw [ht, one_mul]
      _ = t * (t * a ^ n * t) := by group
      _ = t * a ^ (-n) := by rw [h1]
  calc a ^ j * t * (a ^ j)⁻¹
      = a ^ j * (t * a ^ (-j)) := by rw [← zpow_neg, mul_assoc]
    _ = a ^ j * (a ^ j * t) := by rw [← key j]
    _ = a ^ (2 * j) * t := by rw [← mul_assoc, ← zpow_add, show j + j = 2 * j from by ring]
    _ = t * a ^ (-(2 * j)) := key (2 * j)

/-- For an involution `t`, conjugation of `t` by the element `x * t` is the same as
conjugation by `x`: `(x * t) * t * (x * t)⁻¹ = x * t * x⁻¹`. -/
private lemma mul_inv_conj_involution {G : Type*} [Group G] {x t : G} (ht : t * t = 1) :
    (x * t) * t * (x * t)⁻¹ = x * t * x⁻¹ := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht, mul_assoc x t t, ht, mul_one, mul_assoc]

theorem not_conj_t1_t2_in_S {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    ¬ (∃ g ∈ (D.S : Subgroup G), g * D.t1 * g⁻¹ = D.t2) := by
  rintro ⟨g, hgS, hconj⟩
  have ht1sq : D.t1 * D.t1 = 1 := by
    have h := pow_orderOf_eq_one D.t1
    rw [D.t1_order] at h
    simpa [pow_two] using h
  set a : G := D.t1 * D.t2 with ha
  have hgen : D.S0 = Subgroup.zpowers a := by rw [ha]; exact D.gen
  -- `a` has even order, because the involution `t` lies in `S₀ = ⟨a⟩`
  have h2dvd : 2 ∣ orderOf a := by
    have htmem : D.t ∈ Subgroup.zpowers a := by rw [← hgen]; exact D.t_mem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp htmem
    have hz : D.t ^ (orderOf a : ℤ) = 1 := by
      rw [← hk]
      calc (a ^ k) ^ (orderOf a : ℤ) = (a ^ (orderOf a : ℤ)) ^ k := by
            rw [← zpow_mul, ← zpow_mul, mul_comm]
        _ = 1 ^ k := by rw [zpow_natCast, pow_orderOf_eq_one]
        _ = 1 := one_zpow k
    have hdz : (orderOf D.t : ℤ) ∣ (orderOf a : ℤ) := orderOf_dvd_iff_zpow_eq_one.mpr hz
    rw [D.t_order] at hdz
    exact_mod_cast hdz
  -- `t₁` inverts `a`, and `t₂ = t₁ * a`
  have hinv : D.t1 * a * D.t1 = a⁻¹ := by
    have ht2sq : D.t2 * D.t2 = 1 := by
      have h := pow_orderOf_eq_one D.t2
      rw [D.t2_order] at h
      simpa [pow_two] using h
    rw [ha, mul_inv_rev, inv_eq_of_mul_eq_one_right ht1sq, inv_eq_of_mul_eq_one_right ht2sq]
    calc D.t1 * (D.t1 * D.t2) * D.t1 = (D.t1 * D.t1) * (D.t2 * D.t1) := by group
      _ = D.t2 * D.t1 := by rw [ht1sq, one_mul]
  have ht2eq : D.t2 = D.t1 * a := by rw [ha, ← mul_assoc, ht1sq, one_mul]
  -- `S₀` has index two in `S`, so `g ∈ S` is either in `S₀` or of the form `u * t₁`, `u ∈ S₀`
  have hdec : g ∈ D.S0 ∨ ∃ u ∈ D.S0, u * D.t1 = g := by
    by_cases hg0 : g ∈ D.S0
    · exact Or.inl hg0
    · right
      obtain ⟨r, -, -, hforall⟩ :=
        (Subgroup.relIndex_eq_two_iff_exists_notMem_and (H := D.S0)
          (K := (D.S : Subgroup G))).mp D.S0_index
      have hgr : g * r ∈ D.S0 := (hforall g hgS).resolve_right hg0
      have ht1r : D.t1 * r ∈ D.S0 := (hforall D.t1 D.t1_mem).resolve_right D.t1_nmem
      refine ⟨g * D.t1, ?_, by rw [mul_assoc, ht1sq, mul_one]⟩
      have hm : (g * r) * (D.t1 * r)⁻¹ ∈ D.S0 := D.S0.mul_mem hgr (D.S0.inv_mem ht1r)
      rwa [show (g * r) * (D.t1 * r)⁻¹ = g * D.t1 by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht1sq]; group] at hm
  -- in both cases `g` conjugates `t₁` to `t₁ * a ^ (-(2 * j))`
  obtain ⟨j, hjconj⟩ : ∃ j : ℤ, D.t1 * a ^ (-(2 * j)) = D.t2 := by
    rcases hdec with hg0 | ⟨u, huS0, hu⟩
    · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (by rw [hgen] at hg0; exact hg0)
      exact ⟨j, by rw [← hconj, ← hj]; exact (conj_zpow_inv_eq ht1sq hinv j).symm⟩
    · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (by rw [hgen] at huS0; exact huS0)
      exact ⟨j, by
        rw [← hconj, ← hu, ← hj, mul_inv_conj_involution ht1sq]
        exact (conj_zpow_inv_eq ht1sq hinv j).symm⟩
  -- comparing with `t₂ = t₁ * a` yields `a ^ (-(2 * j)) = a`, an exponent of wrong parity
  have ha_eq : a ^ (-(2 * j)) = a := by
    have h1 : D.t1 * a ^ (-(2 * j)) = D.t1 * a := by rw [hjconj, ht2eq]
    exact mul_left_cancel h1
  have hone : a ^ (-(2 * j) - 1) = 1 := by
    rw [show -(2 * j) - 1 = -(2 * j) + (-1) from by ring, zpow_add, ha_eq, zpow_neg_one,
      mul_inv_cancel]
  have hdvd : (orderOf a : ℤ) ∣ (-(2 * j) - 1) := orderOf_dvd_iff_zpow_eq_one.mpr hone
  have h2z : (2 : ℤ) ∣ (orderOf a : ℤ) := by exact_mod_cast h2dvd
  obtain ⟨c, hc⟩ := dvd_trans h2z hdvd
  omega

end Work.BG
