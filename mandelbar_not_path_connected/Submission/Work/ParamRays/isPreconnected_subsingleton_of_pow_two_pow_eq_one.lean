import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ParamRays

/-- A complex number of norm one that is not `1` has real part `< 1`. -/
private lemma re_lt_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) : z.re < 1 := by
  rcases lt_trichotomy z.re 1 with h | h | h
  · exact h
  · exfalso
    have him : z.im = 0 := by
      have hns : Complex.normSq z = 1 := by
        rw [Complex.normSq_eq_norm_sq, hz]; norm_num
      rw [Complex.normSq_apply] at hns
      rw [h] at hns
      nlinarith [sq_nonneg z.im]
    apply hne
    exact Complex.ext (by simp [h]) (by simp [him])
  · have := Complex.re_le_norm z
    rw [hz] at this
    linarith

/-- The set of complex numbers that are `2 ^ n`-th roots of unity for some `n` is countable:
it is the countable union of the finite sets of `2 ^ n`-th roots of unity. -/
private lemma countable_pow_two_pow_eq_one :
    Set.Countable {z : ℂ | ∃ n : ℕ, z ^ (2 ^ n) = 1} := by
  have h : {z : ℂ | ∃ n : ℕ, z ^ (2 ^ n) = 1} = ⋃ n, {z : ℂ | z ^ (2 ^ n) = 1} := by
    ext z; simp
  rw [h]
  apply Set.countable_iUnion
  intro n
  apply Set.Finite.countable
  have hpos : 0 < 2 ^ n := by positivity
  have hfin : {z : ℂ | z ^ (2 ^ n) = 1} = ↑(Polynomial.nthRootsFinset (2 ^ n) (1 : ℂ)) := by
    ext z
    simp
  rw [hfin]
  exact Finset.finite_toSet _

/-- In an open interval of `ℝ` there is a point outside any prescribed countable set. -/
private lemma exists_between_notMem_of_countable {x y : ℝ} (hxy : x < y) {T : Set ℝ}
    (hT : T.Countable) : ∃ c, x < c ∧ c < y ∧ c ∉ T := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hsub : Set.Ioo x y ⊆ T := fun c hc => h c hc.1 hc.2
  have h1 : Cardinal.mk ↥(Set.Ioo x y) ≤ Cardinal.mk ↥T := Cardinal.mk_subtype_mono hsub
  rw [Cardinal.mk_Ioo_real hxy] at h1
  have h2 : Cardinal.mk ↥T ≤ Cardinal.aleph0 := hT.le_aleph0
  exact (not_le.mpr Cardinal.aleph0_lt_continuum) (le_trans h1 h2)

/-- Any preconnected subset of the set of all `2 ^ n`-th roots of unity (for varying `n`)
is a subsingleton. -/
theorem isPreconnected_subsingleton_of_pow_two_pow_eq_one {A : Set ℂ}
    (hA : IsPreconnected A) (hsub : A ⊆ {z : ℂ | ∃ n : ℕ, z ^ (2 ^ n) = 1}) :
    A.Subsingleton := by
  intro a ha b hb
  by_contra hab
  have hS : Set.Countable {z : ℂ | ∃ n : ℕ, z ^ (2 ^ n) = 1} := countable_pow_two_pow_eq_one
  have ha1 : ‖a‖ = 1 := by
    obtain ⟨n, hn⟩ := hsub ha
    have h : ‖a‖ ^ (2 ^ n) = 1 := by rw [← Complex.norm_pow, hn, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) (by positivity)).mp h
  have hb1 : ‖b‖ = 1 := by
    obtain ⟨n, hn⟩ := hsub hb
    have h : ‖b‖ ^ (2 ^ n) = 1 := by rw [← Complex.norm_pow, hn, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg b) (by positivity)).mp h
  -- the linear functional `φ z = Re (z * conj a)` separates `a` (value `1`) from `b` (value `< 1`)
  let φ : ℂ → ℝ := fun z => (z * starRingEnd ℂ a).re
  have hφcont : Continuous φ :=
    Complex.continuous_re.comp (continuous_id.mul continuous_const)
  have hφa : φ a = 1 := by
    change (a * starRingEnd ℂ a).re = 1
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, ha1]
    norm_num
  have hφb : φ b < 1 := by
    have hnorm : ‖b * starRingEnd ℂ a‖ = 1 := by
      rw [norm_mul, Complex.norm_conj, hb1, ha1, mul_one]
    have hca : starRingEnd ℂ a * a = 1 := by
      rw [mul_comm, Complex.mul_conj', ha1]
      norm_num
    have hne : b * starRingEnd ℂ a ≠ 1 := by
      intro h
      have hba : b = a := by
        calc b = b * 1 := (mul_one b).symm
          _ = b * (starRingEnd ℂ a * a) := by rw [hca]
          _ = (b * starRingEnd ℂ a) * a := by rw [mul_assoc]
          _ = 1 * a := by rw [h]
          _ = a := one_mul a
      exact hab hba.symm
    change (b * starRingEnd ℂ a).re < 1
    exact re_lt_one_of_norm_eq_one hnorm hne
  -- choose a separating level avoiding all values of `φ` on the (countable) set of roots
  obtain ⟨c, hbc, hc1, hcn⟩ := exists_between_notMem_of_countable hφb (hS.image φ)
  have hcT : ∀ z ∈ {z : ℂ | ∃ n : ℕ, z ^ (2 ^ n) = 1}, φ z ≠ c :=
    fun z hz h => hcn (h ▸ Set.mem_image_of_mem φ hz)
  -- the two half-spaces are open, cover `A`, both meet `A`, and are disjoint
  have hu : IsOpen {z : ℂ | c < φ z} := isOpen_Ioi.preimage hφcont
  have hv : IsOpen {z : ℂ | φ z < c} := isOpen_Iio.preimage hφcont
  have hcov : A ⊆ {z : ℂ | c < φ z} ∪ {z : ℂ | φ z < c} := by
    intro z hz
    have hzne : φ z ≠ c := hcT z (hsub hz)
    rcases lt_or_gt_of_ne hzne with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hAnU : (A ∩ {z : ℂ | c < φ z}).Nonempty :=
    ⟨a, ha, by change c < φ a; rw [hφa]; exact hc1⟩
  have hAnV : (A ∩ {z : ℂ | φ z < c}).Nonempty := ⟨b, hb, hbc⟩
  rcases hA _ _ hu hv hcov hAnU hAnV with ⟨z, hzA, hzU, hzV⟩
  change c < φ z at hzU
  change φ z < c at hzV
  exact absurd hzU (not_lt.mpr hzV.le)

end Work.ParamRays
