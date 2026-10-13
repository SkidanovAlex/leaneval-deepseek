import Mathlib

/-!
# The archimedean logarithm attached to a cofinal element

Let `Γ` be a linearly ordered commutative group with zero and let `g ∈ Γ`, `g ≠ 0`, be such that the
powers of `g` are cofinal below every non-zero element of `Γ` (this is the `hcof` hypothesis, which
is exactly the shape of `IsContinuousValuation`).  We produce a real-valued "logarithm"

`ψ x = sup { m / n : n > 0, x ^ n ≤ g ^ m }`

with `ψ 1 = 0`, `ψ g = 1`, `ψ` additive on the non-zero part of `Γ` and order-reversing there.

The construction is Hölder's: the cofinality of the powers of `g` makes the floors
`kₙ(x) = max { k : x ^ n ≤ g ^ k }` exist, the ratios `kₙ(x)/n` are bounded above, and the resulting
sup is additive because the floors satisfy `kₙ(xy) ∈ [kₙ(x) + kₙ(y), kₙ(x) + kₙ(y) + 1]`.

## Main result

* `Work.DSM2p.cofinal_log_real_aux`
-/

namespace Work.DSM2p

section Core

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- The data attached to a cofinal element `g` of a linearly ordered commutative group with zero:
`g > 0`, `g < 1` and the cofinality of the powers of `g`. -/
private structure CofData (g : Γ) where
  /-- `g` is positive. -/
  pos : 0 < g
  /-- `g` is smaller than `1`. -/
  lt_one : g < 1
  /-- The powers of `g` are cofinal below every non-zero element. -/
  cof : ∀ γ : Γ, γ ≠ 0 → ∃ n : ℕ, g ^ n < γ

/-- For `0 < g < 1` the powers of `g` reverse the order of the exponents. -/
private lemma zpow_le_zpow_iff_of_lt_one {g : Γ} (hg0 : 0 < g) (hg1 : g < 1) {m n : ℤ} :
    g ^ m ≤ g ^ n ↔ n ≤ m := by
  have h : (g⁻¹) ^ n ≤ (g⁻¹) ^ m ↔ n ≤ m :=
    zpow_le_zpow_iff_right₀ (a := g⁻¹) ((one_lt_inv₀ hg0).mpr hg1)
  rwa [inv_zpow, inv_zpow, inv_le_inv₀ (zpow_pos hg0 n) (zpow_pos hg0 m)] at h

private lemma zpow_lt_zpow_iff_of_lt_one {g : Γ} (hg0 : 0 < g) (hg1 : g < 1) {m n : ℤ} :
    g ^ m < g ^ n ↔ n < m := by
  have h : (g⁻¹) ^ n < (g⁻¹) ^ m ↔ n < m :=
    zpow_lt_zpow_iff_right₀ (a := g⁻¹) ((one_lt_inv₀ hg0).mpr hg1)
  rwa [inv_zpow, inv_zpow, inv_lt_inv₀ (zpow_pos hg0 n) (zpow_pos hg0 m)] at h

/-- The set of rational exponents `m / n` (`n > 0`) with `x ^ n ≤ g ^ m`. -/
private noncomputable def cLogSet (g x : Γ) : Set ℝ :=
  {q : ℝ | ∃ m : ℤ, ∃ n : ℕ, 0 < n ∧ x ^ n ≤ g ^ m ∧ q = (m : ℝ) / (n : ℝ)}

/-- The archimedean logarithm of `x` with respect to the cofinal element `g`. -/
private noncomputable def cLog (g x : Γ) : ℝ := sSup (cLogSet g x)

/-- **The floor.**  For `x ≠ 0` and `n > 0` there is an integer `k` with
`g ^ (k + 1) < x ^ n ≤ g ^ k`. -/
private lemma floor_exists {g : Γ} (D : CofData g) {x : Γ} (hx : x ≠ 0) {n : ℕ} (_hn : 0 < n) :
    ∃ k : ℤ, g ^ (k + 1) < x ^ n ∧ x ^ n ≤ g ^ k := by
  have hxn : x ^ n ≠ 0 := pow_ne_zero n hx
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, x ^ n ≤ g ^ z → z ≤ b := by
    obtain ⟨N, hN⟩ := D.cof (x ^ n) hxn
    refine ⟨(N : ℤ), fun z hz => ?_⟩
    have hN' : g ^ (N : ℤ) < x ^ n := by simpa using hN
    exact le_of_lt ((zpow_lt_zpow_iff_of_lt_one D.pos D.lt_one).mp (lt_of_lt_of_le hN' hz))
  have hne : ∃ z : ℤ, x ^ n ≤ g ^ z := by
    obtain ⟨M, hM⟩ := D.cof ((x ^ n)⁻¹) (inv_ne_zero hxn)
    refine ⟨-(M : ℤ), ?_⟩
    have hM' : g ^ (M : ℤ) < (x ^ n)⁻¹ := by simpa using hM
    have hlt : x ^ n < (g ^ (M : ℤ))⁻¹ := by
      have h := (inv_lt_inv₀ (a := (x ^ n)⁻¹) (b := g ^ (M : ℤ))
        (inv_pos.mpr (pow_pos (zero_lt_iff.mpr hx) n)) (zpow_pos D.pos (M : ℤ))).mpr hM'
      simpa using h
    rw [zpow_neg]
    exact le_of_lt hlt
  obtain ⟨k, hk, hmax⟩ := Int.exists_greatest_of_bdd hbdd hne
  refine ⟨k, ?_, hk⟩
  by_contra hcon
  exact absurd (hmax (k + 1) (not_lt.mp hcon)) (by omega)

/-- `cLogSet g x` is bounded above (for `x ≠ 0`): the bound is any integer `N` with `g ^ N < x`. -/
private lemma cLogSet_bddAbove {g : Γ} (D : CofData g) {x : Γ} (hx : x ≠ 0) :
    BddAbove (cLogSet g x) := by
  obtain ⟨N, hN⟩ := D.cof x hx
  have hN' : g ^ (N : ℤ) < x := by simpa using hN
  have hx0 : (0 : Γ) < x := zero_lt_iff.mpr hx
  refine ⟨(N : ℝ), fun q hq => ?_⟩
  obtain ⟨m, n, hn, hmn, rfl⟩ := hq
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmnR : (m : ℝ) ≤ (N : ℝ) * (n : ℝ) := by
    have hm : m ≤ (N : ℤ) * (n : ℤ) := by
      by_contra hcon
      have hcon' : (N : ℤ) * (n : ℤ) < m := not_le.mp hcon
      have hNn : g ^ m < (g ^ (N : ℤ)) ^ n := by
        have h : g ^ m < g ^ ((N : ℤ) * (n : ℤ)) :=
          (zpow_lt_zpow_iff_of_lt_one D.pos D.lt_one).mpr hcon'
        rwa [zpow_mul, zpow_natCast] at h
      have hxn : x ^ n < (g ^ (N : ℤ)) ^ n := lt_of_le_of_lt hmn hNn
      have hxlt : x < g ^ (N : ℤ) :=
        (pow_lt_pow_iff_left₀ hx0.le (zpow_pos D.pos (N : ℤ)).le (Nat.ne_of_gt hn)).mp hxn
      exact absurd hN' (not_lt.mpr hxlt.le)
    have h : ((m : ℤ) : ℝ) ≤ (((N : ℤ) * (n : ℤ) : ℤ) : ℝ) := by exact_mod_cast hm
    simpa using h
  rw [div_le_iff₀ hnR]
  exact hmnR

/-- `cLogSet g x` is non-empty (for `x ≠ 0`). -/
private lemma cLogSet_nonempty {g : Γ} (D : CofData g) {x : Γ} (hx : x ≠ 0) :
    (cLogSet g x).Nonempty := by
  obtain ⟨k, -, hk2⟩ := floor_exists D hx one_pos
  exact ⟨(k : ℝ), k, 1, one_pos, by simpa using hk2, by simp⟩

/-- Lower bound for the logarithm by the floor. -/
private lemma cLog_ge_floor {g : Γ} (D : CofData g) {x : Γ} (hx : x ≠ 0) {n : ℕ} (hn : 0 < n)
    {k : ℤ} (hk : x ^ n ≤ g ^ k) : (k : ℝ) / (n : ℝ) ≤ cLog g x :=
  le_csSup (cLogSet_bddAbove D hx) ⟨k, n, hn, hk, rfl⟩

/-- Upper bound for the logarithm by the floor (the cross estimate). -/
private lemma cLog_le_floor {g : Γ} (D : CofData g) {x : Γ} (hx : x ≠ 0) {n : ℕ} (hn : 0 < n)
    {k : ℤ} (hk : g ^ (k + 1) < x ^ n ∧ x ^ n ≤ g ^ k) :
    cLog g x ≤ ((k : ℝ) + 1) / (n : ℝ) := by
  refine csSup_le (cLogSet_nonempty D hx) fun q hq => ?_
  obtain ⟨m, j, hj, hmj, rfl⟩ := hq
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [div_le_div_iff₀ hjR hnR]
  have h1 : x ^ (j * n) ≤ g ^ (m * (n : ℤ)) := by
    have h := pow_le_pow_left₀ (zero_le : (0 : Γ) ≤ x ^ j) hmj n
    have hL : (x ^ j) ^ n = x ^ (j * n) := (pow_mul x j n).symm
    have hR : (g ^ m) ^ n = g ^ (m * (n : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul]
    rw [hL, hR] at h
    exact h
  have h2 : g ^ ((k + 1) * (j : ℤ)) < x ^ (n * j) := by
    have h := pow_lt_pow_left₀ hk.1 (zero_le : (0 : Γ) ≤ g ^ (k + 1)) (Nat.ne_of_gt hj)
    have hL : (g ^ (k + 1)) ^ j = g ^ ((k + 1) * (j : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul]
    have hR : (x ^ n) ^ j = x ^ (n * j) := (pow_mul x n j).symm
    rw [hL, hR] at h
    exact h
  have h3 : (m * (n : ℤ) : ℤ) < (k + 1) * (j : ℤ) := by
    refine (zpow_lt_zpow_iff_of_lt_one D.pos D.lt_one).mp ?_
    refine lt_of_lt_of_le h2 ?_
    rw [Nat.mul_comm]
    exact h1
  have h4 : (m : ℝ) * (n : ℝ) < ((k : ℝ) + 1) * (j : ℝ) := by
    have h : ((m * (n : ℤ) : ℤ) : ℝ) < (((k + 1) * (j : ℤ) : ℤ) : ℝ) := by exact_mod_cast h3
    simpa using h
  linarith

/-- The logarithm of `1` is `0`. -/
private lemma cLog_one {g : Γ} (D : CofData g) : cLog g 1 = 0 := by
  refine le_antisymm ?_ ?_
  · refine csSup_le (cLogSet_nonempty D one_ne_zero) fun q hq => ?_
    obtain ⟨m, n, hn, hmn, rfl⟩ := hq
    have hm : m ≤ 0 := by
      by_contra hcon
      have hmpos : (0 : ℤ) < m := not_le.mp hcon
      have h1 : g ^ m < 1 := by
        have h := (zpow_lt_zpow_iff_of_lt_one D.pos D.lt_one).mpr hmpos
        rwa [zpow_zero] at h
      have h2 : (1 : Γ) ≤ g ^ m := by simpa using hmn
      exact absurd h1 (not_lt.mpr h2)
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hm) (by positivity)
  · refine le_csSup (cLogSet_bddAbove D one_ne_zero) ?_
    exact ⟨(0 : ℤ), 1, one_pos, by simp, by norm_num⟩

/-- The logarithm of `g` is `1`. -/
private lemma cLog_self {g : Γ} (D : CofData g) : cLog g g = 1 := by
  refine le_antisymm ?_ ?_
  · refine csSup_le (cLogSet_nonempty D (ne_of_gt D.pos)) fun q hq => ?_
    obtain ⟨m, n, hn, hmn, rfl⟩ := hq
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hle : g ^ ((n : ℤ)) ≤ g ^ m := by simpa using hmn
    have hmn' : m ≤ (n : ℤ) := (zpow_le_zpow_iff_of_lt_one D.pos D.lt_one).mp hle
    rw [div_le_one hnR]
    exact_mod_cast hmn'
  · refine le_csSup (cLogSet_bddAbove D (ne_of_gt D.pos)) ?_
    exact ⟨(1 : ℤ), 1, one_pos, by simp, by norm_num⟩

/-- The logarithm is order-reversing on the non-zero part. -/
private lemma cLog_mono {g : Γ} (D : CofData g) {x y : Γ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x ≤ y) : cLog g y ≤ cLog g x := by
  refine csSup_le_csSup (cLogSet_bddAbove D hx) (cLogSet_nonempty D hy) fun q hq => ?_
  obtain ⟨m, n, hn, hmn, rfl⟩ := hq
  exact ⟨m, n, hn, (pow_le_pow_left₀ (zero_le : (0 : Γ) ≤ x) hxy n).trans hmn, rfl⟩

/-- A real number whose absolute value is `≤ 2 / n` for every positive `n` is `0`. -/
private lemma eq_zero_of_forall_abs_le {D : ℝ}
    (H : ∀ n : ℕ, 0 < n → |D| ≤ 2 / (n : ℝ)) : D = 0 := by
  by_contra hne
  have hpos : 0 < |D| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / |D|)
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hn
      simp only [Nat.cast_zero] at hn
      have : 0 < (2 : ℝ) / |D| := div_pos (by norm_num) hpos
      linarith
    · exact h0
  have hlt : (2 : ℝ) / (n : ℝ) < |D| := by
    rw [div_lt_iff₀ hpos] at hn
    rw [div_lt_iff₀ (by exact_mod_cast hnpos : (0 : ℝ) < (n : ℝ))]
    linarith
  exact absurd (H n hnpos) (not_le.mpr hlt)

/-- The logarithm is additive on the non-zero part. -/
private lemma cLog_mul {g : Γ} (D : CofData g) {x y : Γ} (hx : x ≠ 0) (hy : y ≠ 0) :
    cLog g (x * y) = cLog g x + cLog g y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hgz : g ≠ 0 := ne_of_gt D.pos
  have key : ∀ n : ℕ, 0 < n → |cLog g (x * y) - cLog g x - cLog g y| ≤ 2 / (n : ℝ) := by
    intro n hn
    obtain ⟨k, hk1, hk2⟩ := floor_exists D hx hn
    obtain ⟨l, hl1, hl2⟩ := floor_exists D hy hn
    obtain ⟨m, hm1, hm2⟩ := floor_exists D hxy hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have bxy1 : (m : ℝ) / (n : ℝ) ≤ cLog g (x * y) := cLog_ge_floor D hxy hn hm2
    have bxy2 : cLog g (x * y) ≤ ((m : ℝ) + 1) / (n : ℝ) := cLog_le_floor D hxy hn ⟨hm1, hm2⟩
    have bx1 : (k : ℝ) / (n : ℝ) ≤ cLog g x := cLog_ge_floor D hx hn hk2
    have bx2 : cLog g x ≤ ((k : ℝ) + 1) / (n : ℝ) := cLog_le_floor D hx hn ⟨hk1, hk2⟩
    have by1 : (l : ℝ) / (n : ℝ) ≤ cLog g y := cLog_ge_floor D hy hn hl2
    have by2 : cLog g y ≤ ((l : ℝ) + 1) / (n : ℝ) := cLog_le_floor D hy hn ⟨hl1, hl2⟩
    have hkl : k + l ≤ m := by
      by_contra hcon
      have hcon' : m < k + l := not_le.mp hcon
      have h3 : (x * y) ^ n ≤ g ^ (k + l) := by
        have h := mul_le_mul hk2 hl2 (zero_le : (0 : Γ) ≤ y ^ n) (zero_le : (0 : Γ) ≤ g ^ k)
        rw [← mul_pow, ← zpow_add₀ hgz] at h
        exact h
      have h4 : g ^ (k + l) ≤ g ^ (m + 1) :=
        (zpow_le_zpow_iff_of_lt_one D.pos D.lt_one).mpr (by omega)
      have h5 : g ^ (m + 1) < (x * y) ^ n := hm1
      exact absurd (lt_of_lt_of_le (lt_of_le_of_lt h4 h5) h3) (lt_irrefl _)
    have hmk : m ≤ k + l + 1 := by
      by_contra hcon
      have hcon' : k + l + 2 ≤ m := by omega
      have h1 : g ^ (k + l + 2) < (x * y) ^ n := by
        have h := mul_lt_mul hk1 hl1.le (zpow_pos D.pos (l + 1)) (zero_le : (0 : Γ) ≤ x ^ n)
        rw [← zpow_add₀ hgz, ← mul_pow] at h
        rwa [show k + 1 + (l + 1) = k + l + 2 from by ring] at h
      have h4 : g ^ m ≤ g ^ (k + l + 2) :=
        (zpow_le_zpow_iff_of_lt_one D.pos D.lt_one).mpr hcon'
      exact absurd (lt_of_lt_of_le (lt_of_lt_of_le h1 hm2) h4) (lt_irrefl _)
    have hleft : cLog g (x * y) - cLog g x - cLog g y ≤ 2 / (n : ℝ) := by
      have h2 : (m : ℝ) + 1 - ((k : ℝ) + (l : ℝ)) ≤ 2 := by
        have : ((m : ℤ) + 1 : ℤ) ≤ (k + l + 2 : ℤ) := by omega
        have h3 : (m : ℝ) + 1 ≤ (k : ℝ) + (l : ℝ) + 2 := by exact_mod_cast this
        linarith
      calc cLog g (x * y) - cLog g x - cLog g y
          ≤ ((m : ℝ) + 1) / (n : ℝ) - (k : ℝ) / (n : ℝ) - (l : ℝ) / (n : ℝ) := by
            linarith [bxy2, bx1, by1]
        _ = ((m : ℝ) + 1 - ((k : ℝ) + (l : ℝ))) / (n : ℝ) := by ring
        _ ≤ 2 / (n : ℝ) := div_le_div_of_nonneg_right h2 hnR.le
    have hright : -(2 / (n : ℝ)) ≤ cLog g (x * y) - cLog g x - cLog g y := by
      have h2 : (-2 : ℝ) ≤ (m : ℝ) - ((k : ℝ) + 1) - ((l : ℝ) + 1) := by
        have h3 : ((k : ℝ) + (l : ℝ)) ≤ (m : ℝ) := by
          have : (k + l : ℤ) ≤ m := hkl
          exact_mod_cast this
        linarith
      calc -(2 / (n : ℝ))
          = (-2 : ℝ) / (n : ℝ) := by ring
        _ ≤ ((m : ℝ) - ((k : ℝ) + 1) - ((l : ℝ) + 1)) / (n : ℝ) :=
            div_le_div_of_nonneg_right h2 hnR.le
        _ = (m : ℝ) / (n : ℝ) - ((k : ℝ) + 1) / (n : ℝ) - ((l : ℝ) + 1) / (n : ℝ) := by ring
        _ ≤ cLog g (x * y) - cLog g x - cLog g y := by linarith [bxy1, bx2, by2]
    rw [abs_le]
    exact ⟨hright, hleft⟩
  have := eq_zero_of_forall_abs_le key
  linarith

end Core

/-- **The archimedean logarithm attached to a cofinal element.**  If the powers of `g ≠ 0` are
cofinal below every non-zero element of `Γ` (equivalently: `g` is "topologically nilpotent" in the
`g`-adic sense), then there is a real-valued logarithm `ψ` with `ψ 1 = 0`, `ψ g = 1`, additive on
the non-zero part of `Γ` and order-reversing there. -/
theorem cofinal_log_real_aux {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (g : Γ) (hg : g ≠ 0)
    (hcof : ∀ γ : Γ, γ ≠ 0 → ∃ n : ℕ, g ^ n < γ) :
    ∃ ψ : Γ → ℝ, ψ 1 = 0 ∧ ψ g = 1 ∧
      (∀ x y : Γ, x ≠ 0 → y ≠ 0 → ψ (x * y) = ψ x + ψ y) ∧
      (∀ x y : Γ, x ≠ 0 → y ≠ 0 → x ≤ y → ψ y ≤ ψ x) := by
  have hg0 : 0 < g := zero_lt_iff.mpr hg
  have hg1 : g < 1 := by
    obtain ⟨n, hn⟩ := hcof 1 one_ne_zero
    by_contra h
    exact absurd hn (not_lt.mpr (one_le_pow₀ (not_lt.mp h)))
  have D : CofData g := ⟨hg0, hg1, hcof⟩
  exact ⟨cLog g, cLog_one D, cLog_self D, fun x y hx hy => cLog_mul D hx hy,
    fun x y hx hy hxy => cLog_mono D hx hy hxy⟩

end Work.DSM2p
