/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (Følner windows for amenable extensions, first leaf of the analytic core)

# Følner windows for `H = N ⋊ ⟨t⟩`

This file begins the formalisation of the **Følner / Lück approximation** input of
[JZLA20, Proposition 3.11] (Jaikin-Zapirain--López-Álvarez, arXiv:1810.12135, proved there from
[Jaikin, *L²-Betti numbers and their analogues in positive characteristic*, Groups St Andrews
2017, LNS 455, Theorem 12.1 and Corollary 12.2]).

The ambient situation is a group `H`, a normal subgroup `N ⊴ H` and an element `t : H` with

`∀ h : H, ∃ n : N, ∃ j : ℤ, h = n * t ^ j`   and   `∀ j : ℤ, t ^ j ∈ N → j = 0`

(i.e. `H = N ⋊ ⟨t⟩` and `H/N ≅ ℤ`; this is `Work.ORP311.IsExtensionByZ H N t`).  The quotient
`H/N ≅ ℤ` is amenable, and its Følner family is the family of intervals `[-k, k]`, pulled back to
`H`:

* `Work.ORP311.coset N t j` — the right `N`-coset `N * t ^ j`;
* `Work.ORP311.window N t k` — **the `k`-th Følner window** `X_k = ⋃_{j ∈ [-k,k]} N * t ^ j`.

The main results here are the structural facts needed by the approximation argument:

* `mem_window_iff`, `window_mono` — the window is the monotone union of the cosets;
* `exists_unique_repr_of_mem_window` — every `h ∈ X_k` has a *unique* representation
  `h = n * t ^ j` with `j ∈ [-k, k]` (the identification `X_k ≅ N × [-k,k]`);
* `left_mul_mem_window` — `N` acts on `X_k` by left multiplication (freely);
* `t_pow_mul_mem_window`, `t_mul_window_subset` — multiplication by `t` (and its powers) maps
  `X_k` into `X_{k+m}` (the "shift" of the Følner family);
* `window_succ_eq` — `X_{k+1} = X_k ∪ N t^{k+1} ∪ N t^{-(k+1)}`: only **two** cosets are added at
  each step, the Følner property `|∂X_k| / |N\X_k| = 2 / (2k+1) → 0` in the quotient;
* `coset_eq_iff` — distinct exponents give distinct cosets (`N t^i = N t^j ↔ i = j`).

These are the group-theoretic objects on top of which the finite approximation spaces
`ℓ²(X_k)ⁿ ≅ ⊕_{j ∈ [-k,k]} ℓ²(N)ⁿ`, the truncated operators and the dimension function
`dim_{X_k}` are built.
-/
import Mathlib
import Submission.Work.ORP311.Defs

set_option autoImplicit false

universe u

namespace Work.ORP311

variable {H : Type u} [Group H]

/-- The right `N`-coset through `t ^ j`, i.e. the set `N * t ^ j`. -/
def coset (N : Subgroup H) (t : H) (j : ℤ) : Set H := {h | ∃ n : N, h = (n : H) * t ^ j}

theorem mem_coset_iff {N : Subgroup H} {t : H} {j : ℤ} {h : H} :
    h ∈ coset N t j ↔ ∃ n : N, h = (n : H) * t ^ j := Iff.rfl

/-- **The `k`-th Følner window** `X_k = ⋃_{j ∈ [-k, k]} N * t ^ j`, the pull-back to `H` of the
interval `[-k, k]` of the amenable quotient `H/N ≅ ℤ`. -/
def window (N : Subgroup H) (t : H) (k : ℕ) : Set H :=
  {h | ∃ n : N, ∃ j : ℤ, -((k : ℤ)) ≤ j ∧ j ≤ (k : ℤ) ∧ h = (n : H) * t ^ j}

theorem mem_window_iff {N : Subgroup H} {t : H} {k : ℕ} {h : H} :
    h ∈ window N t k ↔
      ∃ n : N, ∃ j : ℤ, -((k : ℤ)) ≤ j ∧ j ≤ (k : ℤ) ∧ h = (n : H) * t ^ j := Iff.rfl

/-- The window is the union of the cosets with exponent in `[-k, k]`. -/
theorem window_eq_iUnion_coset (N : Subgroup H) (t : H) (k : ℕ) :
    window N t k = ⋃ j ∈ {j : ℤ | -((k : ℤ)) ≤ j ∧ j ≤ (k : ℤ)}, coset N t j := by
  ext h
  constructor
  · rintro ⟨n, j, hj1, hj2, rfl⟩
    exact Set.mem_iUnion₂.mpr ⟨j, ⟨hj1, hj2⟩, ⟨n, rfl⟩⟩
  · intro hh
    obtain ⟨j, ⟨hj1, hj2⟩, n, hn⟩ := Set.mem_iUnion₂.mp hh
    exact ⟨n, j, hj1, hj2, hn⟩

/-- The window is monotone in `k`. -/
theorem window_mono {N : Subgroup H} {t : H} {k l : ℕ} (hkl : k ≤ l) :
    window N t k ⊆ window N t l := by
  rintro h ⟨n, j, hj1, hj2, rfl⟩
  refine ⟨n, j, ?_, ?_, rfl⟩ <;> omega

/-- `N` acts on the window by left multiplication. -/
theorem left_mul_mem_window {N : Subgroup H} {t : H} {k : ℕ} (n : N) {h : H}
    (hh : h ∈ window N t k) : (n : H) * h ∈ window N t k := by
  obtain ⟨m, j, hj1, hj2, rfl⟩ := hh
  exact ⟨n * m, j, hj1, hj2, by rw [Subgroup.coe_mul, mul_assoc]⟩

/-- The coset `N t ^ j` contains `t ^ j`. -/
theorem t_pow_mem_coset (N : Subgroup H) (t : H) (j : ℤ) : t ^ j ∈ coset N t j :=
  ⟨1, by simp⟩

/-- Conjugation identity used for the shift: `(t ^ m * n * t ^ (-m)) * t ^ (j + m) = t ^ m * (n * t ^ j)`. -/
theorem zpow_conj_mul (t n : H) (m j : ℤ) :
    (t ^ m * n * t ^ (-m)) * t ^ (j + m) = t ^ m * (n * t ^ j) := by
  have h1 : t ^ (-m) * t ^ (j + m) = t ^ j := by
    rw [← zpow_add]
    congr 1
    ring
  rw [mul_assoc, h1, mul_assoc]

/-- **Uniqueness of the `(N, ℤ)`-coordinates of an element of `H`.**  If `H = N ⋊ ⟨t⟩` with `t`
of infinite order modulo `N`, every `h : H` has a unique representation `h = n * t ^ j`. -/
theorem exists_unique_repr (N : Subgroup H) (t : H) (hext : IsExtensionByZ H N t) (h : H) :
    ∃! p : N × ℤ, h = (p.1 : H) * t ^ p.2 := by
  obtain ⟨n, j, hj⟩ := hext.1 h
  refine ⟨(n, j), hj, ?_⟩
  rintro ⟨n', j'⟩ hj'
  have h1 : (n : H) * t ^ j = (n' : H) * t ^ j' := by rw [← hj, ← hj']
  have h2 : t ^ j = (n : H)⁻¹ * (n' : H) * t ^ j' := by
    have h := congrArg (fun x : H => (n : H)⁻¹ * x) h1
    simpa [mul_assoc] using h
  have h4 : t ^ j * (t ^ j')⁻¹ = (n : H)⁻¹ * (n' : H) := by
    rw [h2, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  have h3 : t ^ (j - j') = (n : H)⁻¹ * (n' : H) := by
    simpa only [zpow_sub, zpow_neg] using h4
  have hmem : t ^ (j - j') ∈ N := h3 ▸ N.mul_mem (N.inv_mem n.2) n'.2
  have hz : j - j' = 0 := hext.2 (j - j') hmem
  have hjj : j' = j := (sub_eq_zero.mp hz).symm
  subst hjj
  have hn : (n' : H) = (n : H) := by
    have h5 := h1
    rw [mul_right_cancel_iff] at h5
    exact h5.symm
  exact Prod.ext (Subtype.ext hn) rfl

/-- The `(N, ℤ)`-coordinates of an element of a window are unique, with the exponent in
`[-k, k]`. -/
theorem exists_unique_repr_of_mem_window (N : Subgroup H) (t : H) (hext : IsExtensionByZ H N t)
    {k : ℕ} {h : H} (hh : h ∈ window N t k) :
    ∃! p : N × ℤ, -((k : ℤ)) ≤ p.2 ∧ p.2 ≤ (k : ℤ) ∧ h = (p.1 : H) * t ^ p.2 := by
  obtain ⟨n, j, hj1, hj2, hj⟩ := hh
  refine ⟨(n, j), ⟨hj1, hj2, hj⟩, ?_⟩
  rintro ⟨n', j'⟩ ⟨-, -, hj'⟩
  obtain ⟨p, hp, huniq⟩ := exists_unique_repr N t hext h
  have h1 : ((n, j) : N × ℤ) = p := huniq (n, j) hj
  have h2 : ((n', j') : N × ℤ) = p := huniq (n', j') hj'
  rw [h2, ← h1]

/-- **The shift.**  Multiplication by `t ^ m` maps the window `X_k` into `X_{k+m}`. -/
theorem t_pow_mul_mem_window (N : Subgroup H) (t : H) (hN : N.Normal) (m : ℕ) {k : ℕ} {h : H}
    (hh : h ∈ window N t k) : t ^ (m : ℤ) * h ∈ window N t (k + m) := by
  have hcast : (((k + m : ℕ)) : ℤ) = (k : ℤ) + (m : ℤ) := by push_cast; ring
  obtain ⟨n, j, hj1, hj2, rfl⟩ := hh
  refine ⟨⟨t ^ (m : ℤ) * (n : H) * t ^ (-(m : ℤ)), ?_⟩, j + m, ?_, ?_, ?_⟩
  · simpa [zpow_neg] using hN.conj_mem (n : H) n.2 (t ^ (m : ℤ))
  · rw [hcast]; omega
  · rw [hcast]; omega
  · show t ^ (m : ℤ) * ((n : H) * t ^ j) =
      (t ^ (m : ℤ) * (n : H) * t ^ (-(m : ℤ))) * t ^ (j + m)
    rw [zpow_conj_mul]

/-- Multiplication by `t` maps the window `X_k` into `X_{k+1}` (the "shift" of the Følner
family). -/
theorem t_mul_window_subset (N : Subgroup H) (t : H) (hN : N.Normal) (k : ℕ) :
    (fun h => t * h) '' window N t k ⊆ window N t (k + 1) := by
  rintro _ ⟨h, hh, rfl⟩
  have := t_pow_mul_mem_window N t hN 1 hh
  simpa using this

/-- **The Følner step.**  Passing from `X_k` to `X_{k+1}` adds exactly two right `N`-cosets,
`N t ^ {k+1}` and `N t ^ {-(k+1)}`; in the amenable quotient `H/N ≅ ℤ` this is the statement
`|∂[-k,k]| / |[-k,k]| = 2 / (2k+1) → 0`. -/
theorem window_succ_eq (N : Subgroup H) (t : H) (k : ℕ) :
    window N t (k + 1) =
      window N t k ∪ coset N t ((k : ℤ) + 1) ∪ coset N t (-((k : ℤ) + 1)) := by
  ext h
  constructor
  · rintro ⟨n, j, hj1, hj2, rfl⟩
    rcases lt_or_ge j (-(k : ℤ)) with h1 | h1
    · have hj : j = -((k : ℤ) + 1) := by omega
      exact Or.inr ⟨n, by rw [hj]⟩
    · rcases lt_or_ge j ((k : ℤ) + 1) with h2 | h2
      · exact Or.inl (Or.inl ⟨n, j, h1, by omega, rfl⟩)
      · have hj : j = (k : ℤ) + 1 := by omega
        exact Or.inl (Or.inr ⟨n, by rw [hj]⟩)
  · intro hh
    rcases hh with (hw | hc) | hc
    · obtain ⟨n, j, hj1, hj2, rfl⟩ := hw
      exact ⟨n, j, by omega, by omega, rfl⟩
    · obtain ⟨n, rfl⟩ := hc
      exact ⟨n, (k : ℤ) + 1, by omega, by omega, rfl⟩
    · obtain ⟨n, rfl⟩ := hc
      exact ⟨n, -((k : ℤ) + 1), by omega, by omega, rfl⟩

/-- **Distinct exponents give distinct cosets**: `N t ^ i = N t ^ j ↔ i = j`. -/
theorem coset_eq_iff (N : Subgroup H) (t : H) (hext : IsExtensionByZ H N t) (i j : ℤ) :
    coset N t i = coset N t j ↔ i = j := by
  constructor
  · intro h
    have hmem : t ^ i ∈ coset N t j := h ▸ t_pow_mem_coset N t i
    obtain ⟨n, hn⟩ := hmem
    have h3 : t ^ (i - j) = (n : H) := by
      have h4 : t ^ i * (t ^ j)⁻¹ = (n : H) := by
        rw [hn, mul_assoc, mul_inv_cancel, mul_one]
      simpa only [zpow_sub, zpow_neg] using h4
    have hN' : t ^ (i - j) ∈ N := h3 ▸ n.2
    exact sub_eq_zero.mp (hext.2 (i - j) hN')
  · rintro rfl
    rfl

/-- **The Følner property, coset form.**  The two cosets added when passing from the window `X_k`
(the pull-back of `[-k, k]`) to `X_{k+1}` are genuinely new: they are distinct from every one of
the `2k+1` cosets of `X_k`.  In the amenable quotient `H/N ≅ ℤ` this is the statement
`|∂[-k,k]| / |[-k,k]| = 2 / (2k+1)`. -/
theorem coset_succ_ne (N : Subgroup H) (t : H) (hext : IsExtensionByZ H N t) {k : ℕ} {j : ℤ}
    (hj : -((k : ℤ)) ≤ j ∧ j ≤ (k : ℤ)) :
    coset N t ((k : ℤ) + 1) ≠ coset N t j ∧ coset N t (-((k : ℤ) + 1)) ≠ coset N t j := by
  constructor
  · intro h
    have : (k : ℤ) + 1 = j := (coset_eq_iff N t hext _ _).mp h
    omega
  · intro h
    have : -((k : ℤ) + 1) = j := (coset_eq_iff N t hext _ _).mp h
    omega

/-- **The Følner family exhausts `H`**: every element of `H = N ⋊ ⟨t⟩` lies in some window. -/
theorem iUnion_window_eq_univ (N : Subgroup H) (t : H) (hext : IsExtensionByZ H N t) :
    (⋃ k : ℕ, window N t k) = Set.univ := by
  ext h
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨n, j, hj⟩ := hext.1 h
    refine Set.mem_iUnion.mpr ⟨j.natAbs, ⟨n, j, ?_, ?_, hj⟩⟩
    · have hle := neg_abs_le j
      rwa [Int.abs_eq_natAbs] at hle
    · exact Int.le_natAbs

end Work.ORP311
