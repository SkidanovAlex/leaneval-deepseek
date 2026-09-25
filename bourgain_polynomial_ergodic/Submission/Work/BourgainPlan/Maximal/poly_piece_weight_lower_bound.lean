import Mathlib

namespace Work.BourgainPlan.Maximal

open Polynomial MeasureTheory Set

/-- **Lower bound for the polynomial weight `q'(u)·(q u − q a)^{1/k−1}`.**  If `q` is a real
polynomial with `q' > 0` on `(a,b]` (`a < b`), then there are an integer `k ≥ 1` (the multiplicity
of `a` as a root of `q − q(a)`) and a constant `c > 0` with
`c ≤ q'(u) · (q u − q a)^{1/k−1}` for every `u ∈ (a,b]`.

HINT: let `k := Polynomial.rootMultiplicity a (q - Polynomial.C (q.eval a))` and
`s := (q - Polynomial.C (q.eval a)) /ₘ (Polynomial.X - Polynomial.C a)^k`, so that
`(X - C a)^k * s = q - C (q.eval a)` (`Polynomial.pow_mul_divByMonic_rootMultiplicity_eq`) and
`s.eval a ≠ 0` (`Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero`); also `k ≥ 1`
(`Polynomial.rootMultiplicity_pos`, needs `q - C (q.eval a) ≠ 0`, which follows from `q' ≢ 0`).
For `u ∈ (a,b]` (so `u - a > 0` and `q u - q a > 0`, the latter because `q' > 0` on `(a,b]` makes
`q` strictly increasing there) one has `q u - q a = (u-a)^k * s u` and
`q' u = (u-a)^{k-1} * (k * s u + (u-a) * s' u)`, whence the weight
`q'(u) * (q u - q a)^{1/k-1}` equals `T u := (s u)^{1/k-1} * (k * s u + (u-a) * s' u)` (use
`Real.rpow_mul`, `Real.mul_rpow`, `k * (1/k - 1) = 1 - k`).  The function `T` is continuous on
`[a,b]`: its only issue is at `u = a`, where `s u → s a > 0` (note `s a ≠ 0` together with
`s u > 0` on `(a,b]` gives `s a > 0`) and `T` tends to the finite limit `k * s a^{1/k}`
(equivalently define `T a := k * s a^{1/k}` and check continuity on `[a,b]` using
`ContinuousOn.rpow_const`).  And `T > 0` on `[a,b]`: on `(a,b]` it equals the weight, which is
positive there, and at `a` it is `k * s a^{1/k} > 0`.  A continuous function on a compact interval
takes a minimum (`IsCompact.exists_isMinOn`, `isCompact_Icc`), so `c := T u₀ > 0` works. -/
theorem poly_piece_weight_lower_bound (q : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (hderiv : ∀ u ∈ Set.Ioc a b, 0 < q.derivative.eval u) :
    ∃ (k : ℕ) (c : ℝ), 0 < k ∧ 0 < c ∧ ∀ u ∈ Set.Ioc a b,
      c ≤ q.derivative.eval u * (q.eval u - q.eval a) ^ ((k : ℝ)⁻¹ - 1) := by
  classical
  -- The derivative is not the zero polynomial: it is positive at `b`.
  have hbd : b ∈ Set.Ioc a b := ⟨hab, le_refl b⟩
  have hqd : q.derivative ≠ 0 := by
    intro h
    have hb := hderiv b hbd
    rw [h] at hb
    simp at hb
  -- `p := q - q(a)`; the multiplicity `k` of `a` and the cofactor `s`.
  set p : Polynomial ℝ := q - Polynomial.C (q.eval a) with hp_def
  have hp : p ≠ 0 := by
    intro h
    have hq : q = Polynomial.C (q.eval a) := by
      have h0 : q - Polynomial.C (q.eval a) = 0 := by rw [← hp_def]; exact h
      exact sub_eq_zero.mp h0
    rw [hq] at hqd
    exact hqd (by simp)
  set k : ℕ := p.rootMultiplicity a with hk_def
  have hkpos : 0 < k := by
    rw [hk_def, Polynomial.rootMultiplicity_pos hp]
    simp [Polynomial.IsRoot, hp_def]
  set s : Polynomial ℝ := p /ₘ (Polynomial.X - Polynomial.C a) ^ k with hs_def
  have hsroot : s = p /ₘ (Polynomial.X - Polynomial.C a) ^ (p.rootMultiplicity a) := by
    rw [hs_def, hk_def]
  have hsa_ne : s.eval a ≠ 0 := by
    rw [hsroot]
    exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hp
  have hmain : (Polynomial.X - Polynomial.C a) ^ k * s = p := by
    rw [hs_def, hk_def]
    exact Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p a
  -- Evaluation identity: `q u - q a = (u-a)^k * s u`.
  have heval : ∀ u : ℝ, (u - a) ^ k * s.eval u = q.eval u - q.eval a := by
    intro u
    have h1 := congrArg (Polynomial.eval u) hmain
    rw [hp_def] at h1
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at h1
    exact h1
  -- `q` is strictly increasing, hence `q u - q a > 0` on `(a,b]`.
  have heval_pos : ∀ u ∈ Set.Ioc a b, 0 < q.eval u - q.eval a := by
    intro u hu
    have hmono : StrictMonoOn (fun u => q.eval u) (Set.Icc a b) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc a b) q.continuous.continuousOn ?_
      intro x hx
      rw [interior_Icc] at hx
      rw [(Polynomial.hasDerivAt (𝕜 := ℝ) q x).deriv]
      exact hderiv x ⟨hx.1, hx.2.le⟩
    exact sub_pos.mpr (hmono ⟨le_refl a, hab.le⟩ ⟨hu.1.le, hu.2⟩ hu.1)
  have hspos : ∀ u ∈ Set.Ioc a b, 0 < s.eval u := by
    intro u hu
    have h1 : 0 < (u - a) ^ k * s.eval u := by
      rw [heval u]; exact heval_pos u hu
    have h2 : 0 < (u - a) ^ k := pow_pos (by linarith [hu.1]) k
    exact pos_of_mul_pos_right h1 h2.le
  -- `s a > 0`, obtained as the limit of the positive values `s u`, `u → a⁺`.
  have hsa_pos : 0 < s.eval a := by
    have hmem : Set.Ioc a b ∈ nhdsWithin a (Set.Ioi a) := by
      rw [← nhdsWithin_Ioc_eq_nhdsGT hab]
      exact self_mem_nhdsWithin
    have hev : ∀ᶠ u in nhdsWithin a (Set.Ioi a), (0 : ℝ) ≤ s.eval u :=
      Filter.eventually_of_mem hmem (fun u hu => (hspos u hu).le)
    have hge : (0 : ℝ) ≤ s.eval a :=
      ge_of_tendsto (s.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev
    exact lt_of_le_of_ne hge (Ne.symm hsa_ne)
  -- Derivative identity: `q' u = (u-a)^{k-1} * (k * s u + (u-a) * s' u)`.
  have hderiv_eq : ∀ u : ℝ, q.derivative.eval u =
      (u - a) ^ (k - 1) * ((k : ℝ) * s.eval u + (u - a) * s.derivative.eval u) := by
    intro u
    have hpoly : Polynomial.derivative ((Polynomial.X - Polynomial.C a) ^ k * s) = q.derivative := by
      rw [hmain, hp_def, Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero]
    have hexp : Polynomial.derivative ((Polynomial.X - Polynomial.C a) ^ k * s)
        = Polynomial.C (k : ℝ) * (Polynomial.X - Polynomial.C a) ^ (k - 1) * s
          + (Polynomial.X - Polynomial.C a) ^ k * Polynomial.derivative s := by
      rw [Polynomial.derivative_mul, Polynomial.derivative_X_sub_C_pow]
    have hpoly2 : q.derivative
        = Polynomial.C (k : ℝ) * (Polynomial.X - Polynomial.C a) ^ (k - 1) * s
          + (Polynomial.X - Polynomial.C a) ^ k * Polynomial.derivative s := by
      rw [← hpoly, hexp]
    have h2 := congrArg (Polynomial.eval u) hpoly2
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at h2
    rw [h2]
    have hpx : (u - a) ^ k = (u - a) ^ (k - 1) * (u - a) := by
      have : k = (k - 1) + 1 := by omega
      nth_rewrite 1 [this]
      rw [pow_succ]
    rw [hpx]
    ring
  -- The weight equals the continuous expression `T u` on `(a,b]`.
  set e : ℝ := (k : ℝ)⁻¹ - 1 with he_def
  have hkRne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hkpos.ne'
  have he_k : (k : ℝ) * e = 1 - (k : ℝ) := by
    rw [he_def, mul_sub, mul_one, mul_inv_cancel₀ hkRne]
  have hk1R : ((k - 1 : ℕ) : ℝ) + (1 - (k : ℝ)) = 0 := by
    rw [Nat.cast_sub (show 1 ≤ k from hkpos), Nat.cast_one]
    ring
  have hW : ∀ u ∈ Set.Ioc a b,
      q.derivative.eval u * (q.eval u - q.eval a) ^ e
        = s.eval u ^ e * ((k : ℝ) * s.eval u + (u - a) * s.derivative.eval u) := by
    intro u hu
    have hua : 0 < u - a := by linarith [hu.1]
    calc q.derivative.eval u * (q.eval u - q.eval a) ^ e
        = (u - a) ^ (k - 1) * ((k : ℝ) * s.eval u + (u - a) * s.derivative.eval u)
            * ((u - a) ^ k * s.eval u) ^ e := by
          rw [hderiv_eq u, ← heval u]
      _ = (u - a) ^ (k - 1) * ((k : ℝ) * s.eval u + (u - a) * s.derivative.eval u)
            * (((u - a) ^ k) ^ e * s.eval u ^ e) := by
          rw [Real.mul_rpow (pow_nonneg hua.le k) (le_of_lt (hspos u hu))]
      _ = (u - a) ^ (k - 1) * ((k : ℝ) * s.eval u + (u - a) * s.derivative.eval u)
            * ((u - a) ^ ((k : ℝ) * e) * s.eval u ^ e) := by
          rw [← Real.rpow_natCast (u - a) k, ← Real.rpow_mul hua.le (k : ℝ) e]
      _ = (u - a) ^ (k - 1) * ((k : ℝ) * s.eval u + (u - a) * s.derivative.eval u)
            * ((u - a) ^ (1 - (k : ℝ)) * s.eval u ^ e) := by
          rw [he_k]
      _ = ((u - a) ^ (k - 1) * (u - a) ^ (1 - (k : ℝ)))
            * ((k : ℝ) * s.eval u + (u - a) * s.derivative.eval u) * s.eval u ^ e := by ring
      _ = 1 * ((k : ℝ) * s.eval u + (u - a) * s.derivative.eval u) * s.eval u ^ e := by
          rw [← Real.rpow_natCast (u - a) (k - 1), ← Real.rpow_add hua, hk1R, Real.rpow_zero]
      _ = s.eval u ^ e * ((k : ℝ) * s.eval u + (u - a) * s.derivative.eval u) := by ring
  -- Extreme value theorem on `[a,b]`.
  set T : ℝ → ℝ := fun u =>
    s.eval u ^ e * ((k : ℝ) * s.eval u + (u - a) * s.derivative.eval u) with hT
  have hTdef : ∀ u, T u = s.eval u ^ e * ((k : ℝ) * s.eval u + (u - a) * s.derivative.eval u) :=
    fun u => rfl
  have hspos_Icc : ∀ u ∈ Set.Icc a b, 0 < s.eval u := by
    intro u hu
    rcases lt_or_eq_of_le hu.1 with h | h
    · exact hspos u ⟨h, hu.2⟩
    · rw [← h]; exact hsa_pos
  have hcontT : ContinuousOn T (Set.Icc a b) := by
    have h1 : ContinuousOn (fun u => s.eval u ^ e) (Set.Icc a b) :=
      ContinuousOn.rpow_const s.continuous.continuousOn
        (fun u hu => Or.inl (hspos_Icc u hu).ne')
    have h2 : ContinuousOn
        (fun u => (k : ℝ) * s.eval u + (u - a) * s.derivative.eval u) (Set.Icc a b) :=
      ((continuous_const.mul s.continuous).add
        ((continuous_id.sub continuous_const).mul s.derivative.continuous)).continuousOn
    exact h1.mul h2
  have hTpos : ∀ u ∈ Set.Icc a b, 0 < T u := by
    intro u hu
    rcases lt_or_eq_of_le hu.1 with h | h
    · rw [hTdef u, ← hW u ⟨h, hu.2⟩]
      exact mul_pos (hderiv u ⟨h, hu.2⟩) (Real.rpow_pos_of_pos (heval_pos u ⟨h, hu.2⟩) e)
    · rw [hTdef u, ← h]
      simp only [sub_self, zero_mul, add_zero]
      exact mul_pos (Real.rpow_pos_of_pos hsa_pos e) (mul_pos (Nat.cast_pos.mpr hkpos) hsa_pos)
  obtain ⟨u₀, hu₀, hmin⟩ := IsCompact.exists_isMinOn isCompact_Icc
      (show (Set.Icc a b).Nonempty from ⟨a, le_refl a, hab.le⟩) hcontT
  refine ⟨k, T u₀, hkpos, hTpos u₀ hu₀, fun u hu => ?_⟩
  have huIcc : u ∈ Set.Icc a b := ⟨hu.1.le, hu.2⟩
  calc T u₀ ≤ T u := hmin huIcc
    _ = q.derivative.eval u * (q.eval u - q.eval a) ^ e := (hW u hu).symm
    _ = q.derivative.eval u * (q.eval u - q.eval a) ^ ((k : ℝ)⁻¹ - 1) := by rw [he_def]

end Work.BourgainPlan.Maximal
