import Submission.Work.PseudoExtract
import Submission.Work.FinSigma
import Submission.Commons.Combinatorics.Transference.ap_count_decomp_lower
import Submission.Commons.Combinatorics.Additive.Szemeredi.ap_count_lower_of_dense_scaled
import Submission.Work.LCFGvN3
import Submission.Commons.Combinatorics.Transference.Unorm_smul_of_nonneg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Green–Tao Theorem 3.5 (relative Szemerédi): the assembly

Given the output of the structure theorem (Green–Tao Proposition 7.1 / 8.1) — a σ-algebra `B`
presented by its atoms `part`, an exceptional set `Ω` saturated with respect to `part`, the
uniform-distribution bound `|𝔼(ν-1|B)| ≤ τ` outside `Ω`, the mass bound `∑_Ω(ν+1) ≤ ρ` and the
Gowers uniformity of the residual — we assemble the relative Szemerédi theorem by the standard
`f = f_U + f_{U^⊥}` decomposition.
-/

open Finset
open scoped BigOperators

namespace GTTrans

open Commons.Combinatorics.Transference
open Commons.Combinatorics.Additive.Szemeredi
open FinSigma

variable {p : ℕ} [Fact p.Prime]

/-- Conversion between the `range`-indexed and `Fin`-indexed arithmetic progression sums. -/
lemma sum_range_eq_sum_fin (k : ℕ) (g : ZMod p → ℝ) :
    (∑ x : ZMod p, ∑ r : ZMod p, ∏ j ∈ Finset.range k, g (x + (j : ZMod p) * r))
      = ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, g (x + ((i : ℕ) : ZMod p) * r) := by
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro r _
  rw [Finset.prod_range]

/-- Splitting a product indexed by `Fin k` according to a subset `t`. -/
lemma prod_ite_split {k : ℕ} (t : Finset (Fin k)) (A B : ZMod p → ℝ) (x r : ZMod p) :
    (∏ i : Fin k, (if i ∈ t then A (x + ((i : ℕ) : ZMod p) * r)
      else B (x + ((i : ℕ) : ZMod p) * r)))
      = (∏ i ∈ t, A (x + ((i : ℕ) : ZMod p) * r))
        * (∏ i ∈ tᶜ, B (x + ((i : ℕ) : ZMod p) * r)) := by
  have hdisj : Disjoint t tᶜ := Finset.disjoint_left.mpr (fun a ha ha' => by
    simp only [Finset.mem_compl] at ha'; exact ha' ha)
  have h := Finset.prod_union (s₁ := t) (s₂ := tᶜ)
    (f := fun i : Fin k => if i ∈ t then A (x + ((i : ℕ) : ZMod p) * r)
      else B (x + ((i : ℕ) : ZMod p) * r)) hdisj
  rw [Finset.union_compl] at h
  have h1 : (∏ x_1 ∈ t, if x_1 ∈ t then A (x + ((x_1 : ℕ) : ZMod p) * r)
        else B (x + ((x_1 : ℕ) : ZMod p) * r))
      = ∏ x_1 ∈ t, A (x + ((x_1 : ℕ) : ZMod p) * r) :=
    Finset.prod_congr rfl (fun i hi => if_pos hi)
  have h2 : (∏ x_1 ∈ tᶜ, if x_1 ∈ t then A (x + ((x_1 : ℕ) : ZMod p) * r)
        else B (x + ((x_1 : ℕ) : ZMod p) * r))
      = ∏ x_1 ∈ tᶜ, B (x + ((x_1 : ℕ) : ZMod p) * r) :=
    Finset.prod_congr rfl (fun i hi => if_neg (Finset.mem_compl.mp hi))
  rw [h1, h2] at h
  exact h

/-- **Green–Tao Theorem 3.5 (relative Szemerédi), assembly.** -/
theorem relative_szemeredi_of_structure {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) (hkp : k ≤ p)
    (part : ZMod p → Finset (ZMod p)) (hmem : ∀ x, x ∈ part x)
    (heq : ∀ x y : ZMod p, y ∈ part x → part y = part x)
    (Ω : Finset (ZMod p)) (hΩsat : ∀ x ∈ Ω, part x ⊆ Ω)
    (ν f : ZMod p → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    {C₀ : ℕ → ℕ → ℝ} {εp δ τ γ ρ δd cd : ℝ} (hP : Commons.NumberTheory.Sieve.KPseudorandom p k ν C₀ εp)
    (hεp : 0 ≤ εp) (hεp1 : εp ≤ 1)
    (hδ : 0 < δ) (hτ0 : 0 ≤ τ)
    (hmass : ∑ x ∈ Ω, (ν x + 1) ≤ ρ)
    (hcE : ∀ x, x ∉ Ω → |cE part (fun y => ν y - 1) x| ≤ τ)
    (hres : Unorm (k - 1) (fun x => if x ∈ Ω then 0 else f x - cE part f x) ≤ γ)
    (hdens : δ * (p : ℝ) ≤ ∑ x, f x)
    (hρ : ρ ≤ 3 / 4 * (δ * (p : ℝ)))
    (hδd : 0 < δd) (hcd : 0 < cd) {P₀ : ℕ}
    (hDense : ∀ (q : ℕ) [NeZero q], Nat.Prime q → P₀ ≤ q → ∀ g : ZMod q → ℝ,
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → δd * (q : ℝ) ≤ ∑ x, g x →
      cd * (q : ℝ) ^ 2 ≤ ∑ x : ZMod q, ∑ r : ZMod q,
        ∏ j ∈ Finset.range k, g (x + (j : ZMod q) * r))
    (hP₀ : P₀ ≤ p) (hδδd : 4 * δd * (1 + τ) ≤ δ) :
    ((1 + τ) ^ k * cd
      - ((2 : ℝ) ^ k - 1) *
        ((1 + τ) ^ k * ((16 * (2:ℝ)^k) *
          (γ / (1 + τ) + εp ^ (((2^k : ℕ) : ℝ))⁻¹)))) * (p : ℝ) ^ 2
      ≤ ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : Nat.Prime p := Fact.out
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hτ1 : (0 : ℝ) < 1 + τ := by linarith
  have h1τ1 : (0 : ℝ) ≤ 1 + τ := le_of_lt hτ1
  have hν : ∀ x, 0 ≤ ν x := hν0
  have hLFC : LinFormsCond p (fun x => (ν x + 1) / 2) (k * 2 ^ (k - 1)) (3 * k - 4) k εp :=
    Commons.Combinatorics.Transference.lfc_half (p := p) hεp hP.1
  -- (2) the two pieces of the decomposition
  set g : ZMod p → ℝ := fun x => if x ∈ Ω then 0 else cE part f x with hg
  set hh : ZMod p → ℝ := fun x => if x ∈ Ω then 0 else f x - cE part f x with hhh
  set Ff : ZMod p → ℝ := fun x => if x ∈ Ω then 0 else f x with hFf
  have hFg : ∀ x, Ff x = g x + hh x := by
    intro x; simp only [hFf, hg, hhh]; split_ifs <;> ring
  -- pointwise bounds for the anti-uniform part
  have hcEν : ∀ x, x ∉ Ω → cE part f x ≤ 1 + τ := by
    intro x hx
    have h1 : cE part f x ≤ cE part ν x := cE_mono f ν (fun y => hfν y) x
    have hE1 : cE part ((fun y : ZMod p => ν y - 1) + fun _ => (1 : ℝ))
        = cE part (fun y : ZMod p => ν y - 1) + cE part (fun _ : ZMod p => (1 : ℝ)) :=
      cE_add _ _
    have hE2 : cE part ((fun y : ZMod p => ν y - 1) + fun _ => (1 : ℝ)) = cE part ν := by
      congr 1; funext y; simp
    have hE3 : cE part (fun _ : ZMod p => (1 : ℝ)) = fun _ => 1 := cE_const hmem 1
    have h2 : cE part ν x = cE part (fun y => ν y - 1) x + 1 := by
      rw [← hE2, hE1, hE3]; simp
    have h6 : |cE part (fun y => ν y - 1) x| ≤ τ := hcE x hx
    linarith [(abs_le.mp h6).2]
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x; simp only [hg]; split_ifs with hx
    · exact le_rfl
    · exact cE_nonneg f hf0 x
  have hg1 : ∀ x, g x ≤ 1 + τ := by
    intro x; simp only [hg]; split_ifs with hx
    · linarith
    · exact hcEν x hx
  have habs_hh : ∀ x, |hh x| ≤ ν x + (1 + τ) := by
    intro x; simp only [hhh]; split_ifs with hx
    · have := hν x; rw [abs_zero]; linarith
    · have h1 : 0 ≤ cE part f x := cE_nonneg f hf0 x
      have h2 : cE part f x ≤ 1 + τ := hcEν x hx
      have h3 : f x ≤ ν x := hfν x
      have h4 : 0 ≤ ν x := hν x
      have h5 : 0 ≤ f x := hf0 x
      rw [abs_le]
      constructor <;> linarith
  -- (3) the mass of the anti-uniform part
  have hΩc_sat : ∀ x ∈ Finset.univ \ Ω, part x ⊆ Finset.univ \ Ω := by
    intro x hx y hy
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
    intro hyΩ
    have hpart : part y = part x := heq x y hy
    have hsub : part y ⊆ Ω := hΩsat y hyΩ
    exact hx (hsub (hpart.symm ▸ hmem x))
  have hsumg : ∑ x, g x = ∑ x ∈ Finset.univ \ Ω, f x := by
    have h1 : ∑ x, g x = ∑ x ∈ Finset.univ \ Ω, cE part f x := by
      rw [hg]
      have hfun : (fun x : ZMod p => if x ∈ Ω then 0 else cE part f x)
          = fun x => if x ∈ Finset.univ \ Ω then cE part f x else 0 := by
        funext x
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        by_cases hx : x ∈ Ω <;> simp [hx]
      rw [hfun, ← Finset.sum_filter]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    rw [h1]
    exact sum_cE_of_union hmem heq (Finset.univ \ Ω) hΩc_sat f
  have hmassg : δ * (p : ℝ) - ρ ≤ ∑ x, g x := by
    rw [hsumg]
    have hsplit : ∑ x ∈ Finset.univ \ Ω, f x + ∑ x ∈ Ω, f x = ∑ x, f x :=
      Finset.sum_sdiff (Finset.subset_univ Ω)
    have h1 : ∑ x ∈ Ω, f x ≤ ρ := by
      have h2 : ∑ x ∈ Ω, f x ≤ ∑ x ∈ Ω, ν x := Finset.sum_le_sum (fun x _ => hfν x)
      have h3 : ∑ x ∈ Ω, ν x ≤ ∑ x ∈ Ω, (ν x + 1) :=
        Finset.sum_le_sum (fun x _ => by linarith [hν x])
      linarith
    linarith
  -- (4) the dense lower bound for the anti-uniform part
  set G : ZMod p → ℝ := fun x => g x / (1 + τ) with hG
  have hG0 : ∀ x, 0 ≤ G x := fun x => div_nonneg (hg0 x) h1τ1
  have hG1 : ∀ x, G x ≤ 1 := by
    intro x
    rw [hG, div_le_one hτ1]
    exact hg1 x
  have hGmass : δd * (p : ℝ) ≤ ∑ x, G x := by
    have h1 : ∑ x, G x = (∑ x, g x) / (1 + τ) := by rw [hG, Finset.sum_div]
    rw [h1, le_div_iff₀ hτ1]
    have h2 : 4 * δd * (1 + τ) * (p : ℝ) ≤ δ * (p : ℝ) :=
      mul_le_mul_of_nonneg_right hδδd hppos.le
    nlinarith [hmassg, hρ]
  have hdense_G : cd * (p : ℝ) ^ 2 ≤ ∑ x : ZMod p, ∑ r : ZMod p,
      ∏ j ∈ Finset.range k, G (x + (j : ZMod p) * r) := by
    have hG1' : ∀ x, G x ≤ 1 + 0 := fun x => by have := hG1 x; linarith
    have hGmass' : δd * (1 + 0) * (p : ℝ) ≤ ∑ x, G x := by simpa using hGmass
    have h := ap_count_lower_of_dense_scaled (δ := δd) (c := cd) (η := 0) hδd hcd le_rfl
      (k := k) (by omega) (P₀ := P₀) hDense hp hP₀ hG0 hG1' hGmass'
    simpa using h
  -- (5) the `2^k - 1` mixed terms
  have hFf2_bd : ∀ (t : Finset (Fin k)) (i : Fin k) (x : ZMod p),
      |(if i ∈ t then g x / (1 + τ) else hh x / (1 + τ))| ≤ ν x + 1 := by
    intro t i x
    by_cases hi : i ∈ t
    · rw [if_pos hi, abs_div, abs_of_pos hτ1, div_le_iff₀ hτ1]
      have h4 : |g x| ≤ 1 + τ := by
        rw [abs_le]; constructor <;> linarith [hg0 x, hg1 x]
      have h5 : 1 + τ ≤ (ν x + 1) * (1 + τ) := by nlinarith [hν x, hτ0]
      linarith
    · rw [if_neg hi, abs_div, abs_of_pos hτ1, div_le_iff₀ hτ1]
      have h4 := habs_hh x
      have h5 : ν x + (1 + τ) ≤ (ν x + 1) * (1 + τ) := by nlinarith [hν x, hτ0]
      linarith
  have hmixed : ∀ t ∈ (Finset.univ : Finset (Fin k)).powerset, t ≠ Finset.univ →
      |∑ x : ZMod p, ∑ r : ZMod p,
        (∏ i ∈ t, g (x + ((i : ℕ) : ZMod p) * r)) *
          (∏ i ∈ tᶜ, hh (x + ((i : ℕ) : ZMod p) * r))|
        ≤ (p : ℝ) ^ 2 * ((1 + τ) ^ k * ((16 * (2:ℝ)^k) *
            (γ / (1 + τ) + εp ^ (((2^k : ℕ) : ℝ))⁻¹))) := by
    intro t _ htne
    have hex : ∃ j : Fin k, j ∉ t := by
      by_contra hc
      push_neg at hc
      exact htne (Finset.eq_univ_of_forall hc)
    obtain ⟨j, hj⟩ := hex
    have hk0 : 0 < k := by omega
    set Ff2 : Fin k → ZMod p → ℝ := fun i x => if i ∈ t then g x / (1 + τ) else hh x / (1 + τ)
      with hFf2
    have hbd : ∀ i x, |Ff2 i x| ≤ ν x + 1 := by
      intro i x
      simp only [hFf2]
      exact hFf2_bd t i x
    have huni : Unorm (k - 1) (Ff2 j) ≤ γ / (1 + τ) := by
      have hjr : Ff2 j = fun x => hh x / (1 + τ) := by
        funext x; simp only [hFf2]; rw [if_neg hj]
      rw [hjr]
      have hsm : (fun x => hh x / (1 + τ)) = fun x => (1 + τ)⁻¹ * hh x := by
        funext x; rw [div_eq_inv_mul]
      rw [hsm, Unorm_smul_of_nonneg (d := k - 1) (by omega) (inv_nonneg.mpr h1τ1)]
      have hres' : Unorm (k - 1) hh ≤ γ := by
        rw [hhh]; exact hres
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hres' (inv_nonneg.mpr h1τ1)
    have hγ0 : 0 ≤ γ := le_trans (Unorm_nonneg (k - 1) (by omega) hh) (by rw [hhh]; exact hres)
    have hσj : (Equiv.swap (⟨0, hk0⟩ : Fin k) j) ⟨0, hk0⟩ = j := Equiv.swap_apply_left _ _
    have hgv := gvn_puniform_half (p := p) hk hkp hν0 hεp hεp1 hLFC
      (Equiv.swap (⟨0, hk0⟩ : Fin k) j) hk0 Ff2 hbd (γ / (1 + τ)) (div_nonneg hγ0 h1τ1)
      (by rw [hσj]; exact huni)
    have hgv' : |∑ r : ZMod p, ∑ x : ZMod p,
        ∏ i : Fin k, Ff2 i (x + ((i : ℕ) : ZMod p) * r)|
        ≤ (p : ℝ) ^ 2 * (16 * (2:ℝ)^k) *
            (γ / (1 + τ) + εp ^ (((2^k : ℕ) : ℝ))⁻¹) := by
      rw [Finset.sum_comm]; exact hgv
    -- relate the two sums
    have hprod : ∀ x r, (∏ i ∈ t, g (x + ((i : ℕ) : ZMod p) * r)) *
          (∏ i ∈ tᶜ, hh (x + ((i : ℕ) : ZMod p) * r))
        = (1 + τ) ^ k * ∏ i : Fin k, Ff2 i (x + ((i : ℕ) : ZMod p) * r) := by
      intro x r
      have hpt : ∏ i : Fin k, Ff2 i (x + ((i : ℕ) : ZMod p) * r)
          = ∏ i : Fin k, ((1 + τ)⁻¹ *
              (if i ∈ t then g (x + ((i : ℕ) : ZMod p) * r)
                else hh (x + ((i : ℕ) : ZMod p) * r))) := by
        apply Finset.prod_congr rfl; intro i _
        simp only [hFf2]
        by_cases hi : i ∈ t
        · simp only [hi, if_true, if_pos hi, div_eq_inv_mul]
        · simp only [hi, if_false, if_neg hi, div_eq_inv_mul]
      rw [hpt, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        prod_ite_split t g hh x r]
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hτ1), one_pow, one_mul]
    have hval : ∑ x : ZMod p, ∑ r : ZMod p,
        (∏ i ∈ t, g (x + ((i : ℕ) : ZMod p) * r)) *
          (∏ i ∈ tᶜ, hh (x + ((i : ℕ) : ZMod p) * r))
        = (1 + τ) ^ k * ∑ r : ZMod p, ∑ x : ZMod p,
            ∏ i : Fin k, Ff2 i (x + ((i : ℕ) : ZMod p) * r) := by
      rw [Finset.mul_sum, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      rw [hprod x r]
    rw [hval, abs_mul, abs_of_nonneg (pow_nonneg h1τ1 k)]
    calc (1 + τ) ^ k * |∑ r : ZMod p, ∑ x : ZMod p,
            ∏ i : Fin k, Ff2 i (x + ((i : ℕ) : ZMod p) * r)|
        ≤ (1 + τ) ^ k * ((p : ℝ) ^ 2 * (16 * (2:ℝ)^k) *
            (γ / (1 + τ) + εp ^ (((2^k : ℕ) : ℝ))⁻¹)) :=
          mul_le_mul_of_nonneg_left hgv' (pow_nonneg h1τ1 k)
      _ = (p : ℝ) ^ 2 * ((1 + τ) ^ k * ((16 * (2:ℝ)^k) *
            (γ / (1 + τ) + εp ^ (((2^k : ℕ) : ℝ))⁻¹))) := by ring
  -- (6) assembly
  have hmain := ap_count_decomp_lower (p := p) (k := k) Ff g hh hFg
    (c := (1 + τ) ^ k * cd) (η := 0)
    (Bnd := (1 + τ) ^ k * ((16 * (2:ℝ)^k) *
      (γ / (1 + τ) + εp ^ (((2^k : ℕ) : ℝ))⁻¹))) ?hd ?hm
  · have hle : ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, Ff (x + ((i : ℕ) : ZMod p) * r)
        ≤ ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r) := by
      apply Finset.sum_le_sum; intro x _
      apply Finset.sum_le_sum; intro r _
      apply Finset.prod_le_prod
      · intro i _
        simp only [hFf]; split_ifs with hx
        · exact le_rfl
        · exact hf0 _
      · intro i _
        simp only [hFf]; split_ifs with hx
        · exact hf0 _
        · exact le_rfl
    calc ((1 + τ) ^ k * cd
          - ((2 : ℝ) ^ k - 1) * ((1 + τ) ^ k * ((16 * (2:ℝ)^k) *
              (γ / (1 + τ) + εp ^ (((2^k : ℕ) : ℝ))⁻¹)))) * (p : ℝ) ^ 2
        = (1 + 0) ^ k * ((1 + τ) ^ k * cd) * (p : ℝ) ^ 2
          - ((2 : ℝ) ^ k - 1) *
            ((p : ℝ) ^ 2 * ((1 + τ) ^ k * ((16 * (2:ℝ)^k) *
              (γ / (1 + τ) + εp ^ (((2^k : ℕ) : ℝ))⁻¹)))) := by ring
      _ ≤ ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, Ff (x + ((i : ℕ) : ZMod p) * r) := hmain
      _ ≤ _ := hle
  · -- the dense hypothesis
    have h2 : (1 + τ) ^ k * cd * (p : ℝ) ^ 2
        ≤ ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, g (x + ((i : ℕ) : ZMod p) * r) := by
      have hdense_G' : cd * (p : ℝ) ^ 2
          ≤ ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, G (x + ((i : ℕ) : ZMod p) * r) := by
        rw [← sum_range_eq_sum_fin k G]
        exact hdense_G
      have h3 : (1 + τ) ^ k * cd * (p : ℝ) ^ 2
          ≤ (1 + τ) ^ k * (∑ x : ZMod p, ∑ r : ZMod p,
              ∏ i : Fin k, G (x + ((i : ℕ) : ZMod p) * r)) := by
        have := mul_le_mul_of_nonneg_left hdense_G' (pow_nonneg h1τ1 k)
        linarith
      refine le_trans h3 (le_of_eq ?_)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      rw [show (1 + τ) ^ k = ∏ _i : Fin k, (1 + τ) from by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      rw [hG, mul_div_cancel₀ _ (ne_of_gt hτ1)]
    simpa using h2
  · -- the mixed hypothesis
    intro t ht hne
    exact hmixed t ht hne

end GTTrans

#print axioms GTTrans.relative_szemeredi_of_structure
