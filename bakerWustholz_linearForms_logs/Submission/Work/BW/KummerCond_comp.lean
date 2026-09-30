import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.kummer_prod_zpow_even

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Rewrite `∏_j (∏_a η_a^{M_ja})^{e_j}` as a single product over `a` with collected exponents. -/
private lemma prod_zpow_row_comp_local {K : Type*} [Field K] {r ρ : ℕ} (η : Fin r → K)
    (hη : ∀ a, η a ≠ 0) (M : Fin ρ → Fin r → ℤ) (e : Fin ρ → Fin 2) :
    (∏ j, (∏ a, η a ^ (M j a)) ^ (e j : ℕ)) = ∏ a, η a ^ (∑ j, M j a * (e j : ℤ)) := by
  have h1 : ∀ j, (∏ a, η a ^ (M j a)) ^ (e j : ℕ)
      = ∏ a, η a ^ (M j a * ((e j : ℕ) : ℤ)) := by
    intro j
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro a _
    rw [← zpow_natCast, ← zpow_mul]
  have key : ∀ (a : Fin r) (n : Fin ρ → ℤ),
      (∏ j, η a ^ (n j)) = η a ^ (∑ j, n j) := by
    intro a n
    have h : ∀ s : Finset (Fin ρ), s.prod (fun j => η a ^ (n j)) = η a ^ (s.sum n) := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | insert j s hj ih =>
          rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ (hη a)]
    simpa using h Finset.univ
  rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro a _
  exact key a (fun j => M j a * (e j : ℤ))

/-- Mod-`2` injectivity of `c ↦ Mᵀ c` for a primitive system `M`: if every entry of `Mᵀ c` is even
then every entry of `c` is even. -/
private lemma rowSpan_two_dvd_local {ρ r : ℕ} (M : Fin ρ → Fin r → ℤ) (hM : PrimSys M)
    (c : Fin ρ → ℤ) (hdiv : ∀ a, (2 : ℤ) ∣ ∑ j, M j a * c j) : ∀ j, (2 : ℤ) ∣ c j := by
  set v : Fin r → ℤ := fun a => ∑ j, M j a * c j with hv
  have hdv : ∀ a, (2 : ℤ) ∣ v a := by intro a; rw [hv]; exact hdiv a
  set y : Fin r → ℤ := fun a => v a / 2 with hy
  have hv_eq : v = ∑ j, c j • M j := by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hv]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hv_mem : v ∈ Submodule.span ℤ (Set.range M) := by
    rw [hv_eq]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j)))
  have hy2 : (2 : ℤ) • y = v := by
    have h : ∀ a, 2 * (v a / 2) = v a := by
      intro a; rw [mul_comm]; exact Int.ediv_mul_cancel (hdv a)
    funext a
    simpa [Pi.smul_apply, smul_eq_mul, hy] using h a
  have hy_mem : y ∈ Submodule.span ℤ (Set.range M) := by
    apply hM.2 _ 2 (by norm_num)
    rw [hy2]; exact hv_mem
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hy_mem
  have hA : ∑ j, c j • M j = (2 : ℤ) • y := by rw [← hv_eq]; exact hy2.symm
  have hB : (2 : ℤ) • y = ∑ j, (2 * f j) • M j := by
    rw [← hf, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
  have hsum_eq : ∑ j, c j • M j = ∑ j, (2 * f j) • M j := hA.trans hB
  have hz : ∑ j, (c j - 2 * f j) • M j = 0 := by
    calc ∑ j, (c j - 2 * f j) • M j
        = ∑ j, (c j • M j - (2 * f j) • M j) := Finset.sum_congr rfl (fun j _ => sub_smul _ _ _)
      _ = ∑ j, c j • M j - ∑ j, (2 * f j) • M j :=
            Finset.sum_sub_distrib (f := fun j => c j • M j) (g := fun j => (2 * f j) • M j)
      _ = 0 := by rw [hsum_eq, sub_self]
  have hzi : ∀ i, (∑ j, (c j - 2 * f j) * M j i : ℤ) = 0 := by
    intro i
    have := congrFun hz i
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  have hzrat : ∑ j, ((c j : ℚ) - 2 * (f j : ℚ)) • (fun i => (M j i : ℚ)) = 0 := by
    funext i
    have hc : ((∑ j, (c j - 2 * f j) * M j i : ℤ) : ℚ) = 0 := by rw [hzi i]; norm_num
    push_cast at hc
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hc
  have hcoeff := (Fintype.linearIndependent_iff.mp hM.1) (fun j => (c j : ℚ) - 2 * (f j : ℚ)) hzrat
  intro j
  have hj : (c j : ℚ) = 2 * (f j : ℚ) := by have := hcoeff j; linarith
  exact ⟨f j, by exact_mod_cast hj⟩

/-- `KummerCond η` (no nontrivial product `∏ ηᵢ^{eᵢ}`, `eᵢ ∈ {0,1}`, is a square) is inherited by
`η'_j = ∏_a η_a^{M_ja}` when the rows of `M` form a primitive system (`PrimSys M`).

*Proof:* if `∏_j (η'_j)^{e'_j}` is a square with `e' ∈ {0,1}^ρ` nonzero, then with
`m_a = ∑_j e'_j M_ja = 2q_a + r_a` (`r_a ∈ {0,1}`) the quotient of `∏_a η_a^{m_a}` by the square
`(∏_a η_a^{q_a})²` is `∏_{r_a = 1} η_a`, again a square, so `KummerCond η` gives `r = 0`; hence
every `m_a` is even, i.e. `Mᵀe' ∈ 2ℤ^r`; as `Mᵀe' = ∑_j e'_j M_j` also lies in the `ℤ`-span of the
rows, saturation gives `Mᵀe'/2 ∈ span_ℤ(M)`; comparing with `Mᵀe' = ∑_j e'_j M_j` and using
`ℚ`-independence of the rows forces `e'_j = 2f_j`, so `e' = 0`, a contradiction. -/
theorem KummerCond_comp {K : Type*} [Field K] {r ρ : ℕ} {η : Fin r → K} (hη : ∀ a, η a ≠ 0)
    (h : KummerCond η) (M : Fin ρ → Fin r → ℤ) (hM : PrimSys M) :
    KummerCond (fun j => ∏ a, η a ^ (M j a)) := by
  intro e he hsq
  rw [prod_zpow_row_comp_local η hη M e] at hsq
  have hdiv : ∀ a, (2 : ℤ) ∣ ∑ j, M j a * (e j : ℤ) :=
    kummer_prod_zpow_even η hη h (fun a => ∑ j, M j a * (e j : ℤ)) hsq
  have heven : ∀ j, (2 : ℤ) ∣ (e j : ℤ) :=
    rowSpan_two_dvd_local M hM (fun j => (e j : ℤ)) hdiv
  apply he
  funext j
  have h2 : (e j : ℤ) = 0 := by
    have hlt : (e j : ℕ) < 2 := (e j).isLt
    have := heven j
    omega
  have h2n : (e j : ℕ) = 0 := by omega
  exact Fin.ext h2n

end Work.BW
