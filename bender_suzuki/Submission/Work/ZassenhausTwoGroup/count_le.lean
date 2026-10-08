import Submission.Work.CharCore.Main
import Submission.Work.Coherence.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The final count of Feit's §3 (Feit 1960, pp. 183–184, displays (27)–(28))

This file proves the *arithmetic core* of Feit's proof of Theorem 1 in the Zassenhaus case:

> if `χ₁` is an irreducible character of `G` of degree `q = |D|` and the `r = (q-1)/2` distinct
> irreducible characters `η₁*, …, η_r*` of degree `m + 1 = |Q| + 1` are constituents of
> `χ₁ χ̄₁`, then `m ≤ 2q + 1`, i.e. `2q ≥ m - 1`.

Feit's inequality (28) reads `q² = χ₁(1)² ≥ 1 + ½(q-1)(m+1)`: the trivial character is a
constituent of `χ₁χ̄₁` (with `⟨χ₁χ̄₁, 1⟩ = ⟨χ₁,χ₁⟩ = 1`) and each `ηᵢ*` is a constituent of degree
`m+1`, so the sum of the degrees of the constituents is at least `1 + r(m+1)` and at most
`χ₁χ̄₁(1) = q²`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

namespace Work.ZassenhausTwoGroup

/-- The arithmetic endgame of Feit's (28): `1 + r(m+1) ≤ q²` and `2r + 1 = q > 1` give
`m ≤ 2q + 1`. -/
private lemma arith {q m r : ℕ} (hqr : 2 * r + 1 = q) (hq : 1 < q)
    (h : 1 + r * (m + 1) ≤ q ^ 2) : m ≤ 2 * q + 1 := by
  have h1 : (1 + r * (m + 1) : ℝ) ≤ (q : ℝ) ^ 2 := by exact_mod_cast h
  have h2 : 2 * (r : ℝ) + 1 = (q : ℝ) := by exact_mod_cast hqr
  have h3 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h4 : (0 : ℝ) < (r : ℝ) := by nlinarith [h2, h3]
  have h5 : (m : ℝ) ≤ 2 * (q : ℝ) + 1 := by nlinarith [h1, h2, h4]
  exact_mod_cast h5

/-- **The final count of Feit's §3** (Feit 1960, pp. 183–184, (27) and (28)).

`G` a finite group, `χ ∈ Irr G` of degree `q > 1`, and `η : Fin r → G → ℂ` a family of
`r = (q-1)/2` distinct irreducible characters of `G` of common degree `m + 1`, each a constituent
of `χ χ̄` (i.e. `⟨χ χ̄, η i⟩ ≠ 0`).  Then `m ≤ 2q + 1`, i.e. `m - 1 ≤ 2q`. -/
theorem count_le {G : Type} [Group G] [Fintype G] {q m r : ℕ} (hqr : 2 * r + 1 = q) (hq : 1 < q)
    {χ : G → ℂ} (hχ : χ ∈ Work.CharCore.Irr G) (hdeg : χ 1 = (q : ℂ))
    {η : Fin r → G → ℂ} (hη : ∀ i, η i ∈ Work.CharCore.Irr G)
    (hηdeg : ∀ i, η i 1 = (m : ℂ) + 1) (hinj : Function.Injective η)
    (hcon : ∀ i, Work.CharCore.cfInner (χ * (fun g => star (χ g))) (η i) ≠ 0) :
    m ≤ 2 * q + 1 := by
  classical
  by_cases hm : m = 0
  · subst hm; exact Nat.zero_le _
  set f : G → ℂ := χ * fun g => star (χ g) with hfdef
  -- `f = χ χ̄` is a character
  have hχc : Work.CharCore.IsChar χ := Work.CharCore.IsChar.of_mem_Irr hχ
  have hcjc : Work.CharCore.IsChar (fun g => star (χ g)) := by
    have hmem : (fun g => starRingEnd ℂ (χ g)) ∈ Work.CharCore.Irr G :=
      Work.CharCore.mem_Irr_iff_coherence.mpr
        (Work.Coherence.irr_conj (Work.CharCore.mem_Irr_iff_coherence.mp hχ))
    have hfun : (fun g => star (χ g)) = (fun g => starRingEnd ℂ (χ g)) := by
      funext g; simp
    rw [hfun]
    exact Work.CharCore.IsChar.of_mem_Irr hmem
  have hfc : Work.CharCore.IsChar f := by
    rw [hfdef]; exact Work.CharCore.isChar_mul hχc hcjc
  have hcls : Work.CharCore.IsClassFun f := hfc.isClassFun
  -- the multiplicities of the irreducible constituents of `f`
  let n : (G → ℂ) → ℕ := fun ψ =>
    if h : ψ ∈ Work.CharCore.Irr G then
      Classical.choose ((Work.CharCore.isChar_iff hcls).mp hfc ψ h) else 0
  have hn : ∀ ψ ∈ Work.CharCore.Irr G, Work.CharCore.cfInner f ψ = (n ψ : ℂ) := by
    intro ψ hψ
    simp only [n, dif_pos hψ]
    exact Classical.choose_spec ((Work.CharCore.isChar_iff hcls).mp hfc ψ hψ)
  -- the trivial character
  have htriv : (fun _ : G => (1 : ℂ)) ∈ Work.CharCore.Irr G :=
    Work.CharCore.principalChar_mem_Irr
  have htrivDeg : Work.CharCore.irrDeg (fun _ : G => (1 : ℂ)) = 1 := by
    have h2 : ((Work.CharCore.irrDeg (fun _ : G => (1 : ℂ)) : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      simpa using (Work.CharCore.irrDeg_spec (G := G) (χ := fun _ : G => (1 : ℂ)) htriv).symm
    exact Nat.cast_injective h2
  have hηdeg' : ∀ i, Work.CharCore.irrDeg (η i) = m + 1 := by
    intro i
    have h2 : ((Work.CharCore.irrDeg (η i) : ℕ) : ℂ) = ((m + 1 : ℕ) : ℂ) := by
      rw [← Work.CharCore.irrDeg_spec (hη i), hηdeg i]
      push_cast; ring
    exact Nat.cast_injective h2
  -- the trivial character is none of the `η i`
  have hηne : ∀ i, η i ≠ (fun _ : G => (1 : ℂ)) := by
    intro i h
    have h1 : Work.CharCore.irrDeg (η i) = 1 := by rw [h, htrivDeg]
    rw [hηdeg' i] at h1
    omega
  -- `f 1 = q²`
  have hf1 : f 1 = ((q ^ 2 : ℕ) : ℂ) := by
    rw [hfdef, Pi.mul_apply, hdeg]
    push_cast
    simp
    ring
  -- the degree identity, in `ℕ`
  have hNatEq : ∑ ψ ∈ Work.CharCore.Irr G, n ψ * Work.CharCore.irrDeg ψ = q ^ 2 := by
    have h1 : ((∑ ψ ∈ Work.CharCore.Irr G, n ψ * Work.CharCore.irrDeg ψ : ℕ) : ℂ)
        = ((q ^ 2 : ℕ) : ℂ) := by
      rw [Nat.cast_sum, hf1.symm, Work.CharCore.classFun_eq_sum_irr hcls]
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun ψ hψ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hn ψ hψ, Work.CharCore.irrDeg_spec hψ]
      push_cast
      ring
    exact Nat.cast_injective h1
  -- multiplicities are positive where we need them
  have hmultTriv : 1 ≤ n (fun _ : G => (1 : ℂ)) := by
    have h5 : Work.CharCore.cfInner f (fun _ : G => (1 : ℂ)) = 1 := by
      have h6 : Work.CharCore.cfInner f (fun _ : G => (1 : ℂ)) = Work.CharCore.cfInner χ χ := by
        simp only [Work.CharCore.cfInner, hfdef]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        simp
      rw [h6]
      simpa using Work.CharCore.irr_orthonormal χ χ hχ hχ
    have h4 : (n (fun _ : G => (1 : ℂ)) : ℂ) ≠ 0 := by
      rw [← hn (fun _ : G => (1 : ℂ)) htriv]
      rw [h5]; norm_num
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => h4 (by rw [h0]; norm_num)
  have hmultη : ∀ i, 1 ≤ n (η i) := by
    intro i
    have h4 : (n (η i) : ℂ) ≠ 0 := by
      rw [← hn (η i) (hη i)]
      exact hcon i
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => h4 (by rw [h0]; norm_num)
  -- the comparison of degree sums
  set S : Finset (G → ℂ) :=
    insert (fun _ : G => (1 : ℂ)) (Finset.univ.image η) with hSdef
  have hSsub : S ⊆ Work.CharCore.Irr G := by
    intro ψ hψ
    rw [hSdef] at hψ
    rcases Finset.mem_insert.mp hψ with h | h
    · rw [h]; exact htriv
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
      exact hη i
  have hSp : ∀ ψ ∈ S, 1 ≤ n ψ := by
    intro ψ hψ
    rw [hSdef] at hψ
    rcases Finset.mem_insert.mp hψ with h | h
    · rw [h]; exact hmultTriv
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
      exact hmultη i
  have hSval : ∑ ψ ∈ S, Work.CharCore.irrDeg ψ = 1 + r * (m + 1) := by
    have hnotmem : (fun _ : G => (1 : ℂ)) ∉ Finset.univ.image η := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      exact fun i => hηne i
    rw [hSdef, Finset.sum_insert hnotmem, Finset.sum_image]
    · rw [htrivDeg]
      simp only [hηdeg']
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    · intro i _ j _ hij
      exact hinj hij
  have hSle : ∑ ψ ∈ S, Work.CharCore.irrDeg ψ
      ≤ ∑ ψ ∈ S, n ψ * Work.CharCore.irrDeg ψ := by
    refine Finset.sum_le_sum fun ψ hψ => ?_
    calc Work.CharCore.irrDeg ψ = 1 * Work.CharCore.irrDeg ψ := (one_mul _).symm
      _ ≤ n ψ * Work.CharCore.irrDeg ψ := Nat.mul_le_mul_right _ (hSp ψ hψ)
  have hle : ∑ ψ ∈ S, n ψ * Work.CharCore.irrDeg ψ
      ≤ ∑ ψ ∈ Work.CharCore.Irr G, n ψ * Work.CharCore.irrDeg ψ :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub fun _ _ _ => Nat.zero_le _
  refine arith hqr hq ?_
  rw [← hSval]
  exact hSle.trans (hle.trans (le_of_eq hNatEq))

end Work.ZassenhausTwoGroup
