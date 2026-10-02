import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

/-- The real "level parameter"
`s ↦ t₀ ^ ((1024 : ℝ) ^ s)`, for `1 < t₀`, is a continuous strictly increasing
homeomorphism of `ℝ` onto `(1, ∞)` whose values satisfy the self-similarity
relations
`f (s + 1) = f s ^ 1024`, `f (s + u) = (f s) ^ (t₀ ^ u)` and
`(f s) ^ (1024 ^ m) = f (s + m)`. -/
theorem levelParam_spec {t₀ : ℝ} (ht₀ : 1 < t₀) :
    Continuous (fun s : ℝ => t₀ ^ ((1024 : ℝ) ^ s)) ∧
    StrictMono (fun s : ℝ => t₀ ^ ((1024 : ℝ) ^ s)) ∧
    (∀ s : ℝ, 1 < t₀ ^ ((1024 : ℝ) ^ s)) ∧
    (fun s : ℝ => t₀ ^ ((1024 : ℝ) ^ s)) 0 = t₀ ∧
    (fun s : ℝ => t₀ ^ ((1024 : ℝ) ^ s)) 1 = t₀ ^ (1024 : ℕ) ∧
    (∀ s : ℝ, t₀ ^ ((1024 : ℝ) ^ (s + 1)) = (t₀ ^ ((1024 : ℝ) ^ s)) ^ (1024 : ℕ)) ∧
    (∀ s u : ℝ, t₀ ^ ((1024 : ℝ) ^ (s + u)) = (t₀ ^ ((1024 : ℝ) ^ s)) ^ ((1024 : ℝ) ^ u)) ∧
    (∀ s : ℝ, ∀ m : ℕ, (t₀ ^ ((1024 : ℝ) ^ s)) ^ (1024 ^ m)
        = t₀ ^ ((1024 : ℝ) ^ (s + m))) ∧
    (∀ t : ℝ, 1 < t → ∃ s : ℝ, t₀ ^ ((1024 : ℝ) ^ s) = t) := by
  have ht₀pos : 0 < t₀ := lt_trans one_pos ht₀
  have ht₀ne : t₀ ≠ 0 := ne_of_gt ht₀pos
  have ht₀ne1 : t₀ ≠ 1 := ne_of_gt ht₀
  have h1024pos : (0:ℝ) < 1024 := by norm_num
  have h1024ne : (1024:ℝ) ≠ 0 := by norm_num
  have h1024ne1 : (1024:ℝ) ≠ 1 := by norm_num
  have h1024lt : (1:ℝ) < 1024 := by norm_num
  have hle : (0:ℝ) ≤ t₀ := le_of_lt ht₀pos
  have houter : StrictMono (fun x : ℝ => t₀ ^ x) :=
    fun a b hab => (Real.rpow_lt_rpow_left_iff ht₀).mpr hab
  have hinner : StrictMono (fun x : ℝ => (1024:ℝ) ^ x) :=
    fun a b hab => (Real.rpow_lt_rpow_left_iff h1024lt).mpr hab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Real.continuous_const_rpow ht₀ne).comp (Real.continuous_const_rpow h1024ne)
  · exact houter.comp hinner
  · intro s
    exact Real.one_lt_rpow ht₀ (Real.rpow_pos_of_pos h1024pos s)
  · show t₀ ^ ((1024:ℝ)^(0:ℝ)) = t₀
    rw [Real.rpow_zero, Real.rpow_one]
  · show t₀ ^ ((1024:ℝ)^(1:ℝ)) = t₀ ^ (1024:ℕ)
    rw [Real.rpow_one]
    exact Real.rpow_natCast t₀ 1024
  · intro s
    rw [← Real.rpow_natCast (t₀ ^ ((1024:ℝ)^s)) 1024, ← Real.rpow_mul hle]
    rw [Real.rpow_add h1024pos, Real.rpow_one]
    norm_num
  · intro s u
    rw [← Real.rpow_mul hle, Real.rpow_add h1024pos]
  · intro s m
    rw [← Real.rpow_natCast (t₀ ^ ((1024:ℝ)^s)) (1024^m), ← Real.rpow_mul hle]
    rw [Real.rpow_add h1024pos]
    rw [show (((1024^m : ℕ)) : ℝ) = (1024:ℝ)^(m:ℝ) by
      rw [Nat.cast_pow, ← Real.rpow_natCast]; norm_num]
  · intro t ht
    refine ⟨Real.logb 1024 (Real.logb t₀ t), ?_⟩
    rw [Real.rpow_logb h1024pos h1024ne1 (Real.logb_pos ht₀ ht)]
    exact Real.rpow_logb ht₀pos ht₀ne1 (lt_trans one_pos ht)

end Work.ELRig
