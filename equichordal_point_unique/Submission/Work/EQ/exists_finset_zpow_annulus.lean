import Mathlib
import Submission.Work.EQ.DefsCore

namespace Work.EQ

/-- Auxiliary form of `exists_finset_zpow_annulus`, stated directly for a real contraction
`λ ∈ (0,1)` (so that the proof is independent of the particular closed form of `eqLam a`). -/
private lemma zpow_annulus_aux {lam : ℝ} (h0 : 0 < lam) (h1' : lam < 1)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : r₁ < r₂) (hratio : r₂ / r₁ > 1 / lam)
    {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    ∃ J : Finset ℤ, ∀ x : ℝ, m ≤ x → x ≤ M →
      ∃ j ∈ J, r₁ ≤ lam ^ j * x ∧ lam ^ j * x ≤ r₂ := by
  have hMpos : 0 < M := lt_of_lt_of_le hm hmM
  have hne : lam ≠ 0 := ne_of_gt h0
  -- `r₁ < λ r₂`, so consecutive dilated annuli `[λ^j r₁, λ^j r₂]` overlap.
  have hlamr2 : r₁ < lam * r₂ := by
    have h1 : (1:ℝ) / lam < r₂ / r₁ := hratio
    rw [div_lt_div_iff₀ h0 hr₁] at h1
    linarith
  -- An exponent `N⁺` with `λ^{N⁺} M ≤ r₂` (upper bound for the chosen exponent).
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, lam ^ n * M < r₂ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (lt_trans hr₁ hr₂) hMpos) h1'
    refine ⟨n, ?_⟩
    have h := mul_lt_mul_of_pos_right hn hMpos
    rwa [div_mul_cancel₀ r₂ (ne_of_gt hMpos)] at h
  -- An exponent `N⁻ = -(n₂)` with `λ^{N⁻} > λ r₂ / m` (lower bound for the chosen exponent).
  obtain ⟨n₂, hn₂⟩ : ∃ n : ℕ, lam * r₂ / m < lam ^ (-(n:ℤ)) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (lam * r₂ / m) ((one_lt_inv₀ h0).2 h1')
    exact ⟨n, by rw [zpow_neg, zpow_natCast, ← inv_pow]; exact hn⟩
  have hle : (-(n₂:ℤ) : ℤ) ≤ (n₁:ℤ) := by
    have ha : (0:ℤ) ≤ (n₁:ℤ) := Int.natCast_nonneg n₁
    have hb : (-(n₂:ℤ) : ℤ) ≤ 0 := by simp
    omega
  refine ⟨Finset.Icc (-(n₂:ℤ)) (n₁:ℤ), fun x hmx hMx => ?_⟩
  -- `N⁺` is always a feasible exponent for `x`.
  have hkeyN : lam ^ (n₁:ℤ) * x ≤ r₂ := by
    have h2 : lam ^ (n₁:ℤ) * M < r₂ := by rw [zpow_natCast]; exact hn₁
    have h3 : lam ^ (n₁:ℤ) * x ≤ lam ^ (n₁:ℤ) * M :=
      mul_le_mul_of_nonneg_left hMx (zpow_pos h0 _).le
    linarith
  -- The feasible exponents form a nonempty finite set; take its least element.
  set S : Finset ℤ := (Finset.Icc (-(n₂:ℤ)) (n₁:ℤ)).filter (fun j => lam ^ j * x ≤ r₂) with hS
  have hSne : S.Nonempty := by
    refine ⟨(n₁:ℤ), ?_⟩
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hle, le_refl _⟩, hkeyN⟩
  let j : ℤ := S.min' hSne
  have hjmem : j ∈ S := Finset.min'_mem S hSne
  have hjle : ∀ y ∈ S, j ≤ y := fun y hy => (Finset.isLeast_min' S hSne).2 hy
  rw [hS, Finset.mem_filter, Finset.mem_Icc] at hjmem
  obtain ⟨hjIcc, hjleR⟩ := hjmem
  refine ⟨j, ?_, ?_, hjleR⟩
  · rw [Finset.mem_Icc]; exact hjIcc
  · rcases eq_or_lt_of_le hjIcc.1 with heq | hlt
    · -- `j = N⁻`: the direct lower bound `λ^{N⁻} x > λ r₂ > r₁` applies.
      rw [← heq]
      have h1 : lam * r₂ / m < lam ^ (-(n₂:ℤ)) := hn₂
      have h2 : (lam * r₂ / m) * m < lam ^ (-(n₂:ℤ)) * m := mul_lt_mul_of_pos_right h1 hm
      have h3 : (lam * r₂ / m) * m = lam * r₂ := by field_simp
      have h4 : lam ^ (-(n₂:ℤ)) * m ≤ lam ^ (-(n₂:ℤ)) * x :=
        mul_le_mul_of_nonneg_left hmx (zpow_pos h0 _).le
      linarith
    · -- `j > N⁻`: minimality forces `λ^{j-1} x > r₂`, hence `λ^j x > λ r₂ > r₁`.
      have hj1ge : (-(n₂:ℤ) : ℤ) ≤ j - 1 := by omega
      have hj1le : j - 1 ≤ (n₁:ℤ) := by omega
      have hj1Icc : j - 1 ∈ Finset.Icc (-(n₂:ℤ)) (n₁:ℤ) := by
        rw [Finset.mem_Icc]; exact ⟨hj1ge, hj1le⟩
      have hnotin : j - 1 ∉ S := by
        intro hmem
        have hh := hjle (j-1) hmem
        omega
      have hgt : r₂ < lam ^ (j - 1) * x :=
        not_le.mp (fun hcon' => hnotin (by rw [hS, Finset.mem_filter]; exact ⟨hj1Icc, hcon'⟩))
      have hstep : lam ^ j * x = lam * (lam ^ (j - 1) * x) := by
        have h2 : (j - 1) + 1 = j := by ring
        rw [← h2, zpow_add_one₀ hne]
        ring_nf
      have h5 : lam * r₂ < lam * (lam ^ (j - 1) * x) := mul_lt_mul_of_pos_left hgt h0
      rw [hstep]
      linarith

/-- **A bounded set of moduli is covered by finitely many `λ`-scaled annuli.**

For `0 < a < 1`, `λ = eqLam a ∈ (0,1)`, and radii `0 < r₁ < r₂` with ratio `r₂/r₁ > 1/λ`,
every modulus `x ∈ [m, M]` (with `0 < m ≤ M`) can be scaled by a power of `λ` into the annulus
`[r₁, r₂]`, and the exponents needed depend only on `m, M`.  Consequently a fixed finite set `J`
of integer shifts suffices for the whole interval.

(Used to reduce a general compact `K ⊂ ℂ*` to the single annulus `Ann r₁ r₂`: for `z` with
`‖z‖ ∈ [m, M]` some `λ^j` with `j ∈ J` brings `λ^j ‖z‖` into `[r₁, r₂]`.) -/
theorem exists_finset_zpow_annulus {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : r₁ < r₂) (hratio : r₂ / r₁ > 1 / eqLam a)
    {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    ∃ J : Finset ℤ, ∀ x : ℝ, m ≤ x → x ≤ M →
      ∃ j ∈ J, r₁ ≤ (eqLam a) ^ j * x ∧ (eqLam a) ^ j * x ≤ r₂ := by
  have h0 : 0 < eqLam a := by
    rw [eqLam]; exact div_pos (by linarith) (by linarith)
  have h1' : eqLam a < 1 := by
    rw [eqLam, div_lt_one (by linarith : (0:ℝ) < 1 + a)]
    linarith
  exact zpow_annulus_aux h0 h1' hr₁ hr₂ hratio hm hmM

end Work.EQ
