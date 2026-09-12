import Mathlib
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.closure_P_eq_S_of_degree_le_one
import Submission.Commons.LorentzianPolynomials.closure_P_eq_nonneg
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two
import Submission.Commons.LorentzianPolynomials.subst_coeff_continuous
import Submission.Commons.LorentzianPolynomials.smul_mem_strict
import Submission.Commons.LorentzianPolynomials.L_inter_P_subset_closure_strict
import Submission.Commons.LorentzianPolynomials.subst_mem_L_inter_P
import Submission.Commons.Algebra.MvPolynomial.homogeneous_coeff_equiv
import Submission.Commons.LorentzianPolynomials.monom_pow_mem_L

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set Filter
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.LorentzianPolynomials

noncomputable section


/-- coefficient-wise convergence implies module-topology convergence on `H n d` -/
lemma tendsto_of_coeff_tendsto (n d : ℕ) (u : ℕ → H n d) (f : H n d)
    (h : ∀ m : {m : Fin n →₀ ℕ // Finsupp.weight 1 m = d},
        Tendsto (fun k : ℕ => (u k).1.coeff m.1) atTop (𝓝 (f.1.coeff m.1))) :
    Tendsto u atTop (𝓝 f) := by
  classical
  let S : Type := {m : Fin n →₀ ℕ // Finsupp.weight 1 m = d}
  haveI : Fintype S := by
    dsimp [S]
    let T : Set (Fin n →₀ ℕ) := {m | Finsupp.weight 1 m = d}
    have hfin : T.Finite := by
      dsimp [T]
      exact Finsupp.finite_of_nat_weight_eq (1 : Fin n → ℕ) (by intro x; simp) d
    exact hfin.fintype
  haveI : Finite S := inferInstance
  haveI : IsModuleTopology ℝ (S → ℝ) := inferInstance
  rcases Commons.Algebra.MvPolynomial.homogeneous_coeff_equiv n d with ⟨e, he⟩
  let eH : H n d ≃ₗ[ℝ] (S → ℝ) := e
  have heH : ∀ (f : H n d) (m : S), eH f m = f.1.coeff m.1 := by
    intro f m
    exact he f m
  have hcont_esymm : Continuous (fun x : S → ℝ => (eH.symm x : H n d)) := by
    change Continuous ((eH.symm.toLinearMap : (S → ℝ) →ₗ[ℝ] H n d))
    exact IsModuleTopology.continuous_of_linearMap (eH.symm.toLinearMap)
  have hcoord : Tendsto (fun k : ℕ => eH (u k)) atTop (𝓝 (eH f)) := by
    rw [tendsto_pi_nhds]
    intro m
    have hm : Tendsto (fun k : ℕ => (u k).1.coeff m.1) atTop (𝓝 (f.1.coeff m.1)) := h m
    have hu : ∀ k : ℕ, eH (u k) m = (u k).1.coeff m.1 := fun k => heH (u k) m
    have hf : eH f m = f.1.coeff m.1 := heH f m
    simpa [hu, hf] using hm
  have hcomp : Tendsto (fun k : ℕ => (eH.symm (eH (u k)) : H n d)) atTop
      (𝓝 (eH.symm (eH f) : H n d)) :=
    hcont_esymm.continuousAt.tendsto.comp hcoord
  have hId : (fun k : ℕ => (eH.symm (eH (u k)) : H n d)) = u := by
    funext k
    exact eH.symm_apply_apply (u k)
  have hIdf : (eH.symm (eH f) : H n d) = f := eH.symm_apply_apply f
  simpa [hId, hIdf] using hcomp

/-- substitution at θ = 0 is identity on coefficients -/
lemma subst_coeff_at_zero (n d : ℕ) (f : H n d) (m : Fin n →₀ ℕ) :
    ((MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - (0 : ℝ)) * MvPolynomial.X j +
          MvPolynomial.C (0 : ℝ) * (∑ i : Fin n, MvPolynomial.X i)) f.1).coeff m) =
      f.1.coeff m := by
  have hsub : (fun j : Fin n =>
        MvPolynomial.C (1 - (0 : ℝ)) * MvPolynomial.X j +
          MvPolynomial.C (0 : ℝ) * (∑ i : Fin n, MvPolynomial.X i)) =
      (fun j : Fin n => MvPolynomial.X j) := by
    funext j
    simp
  calc
    ((MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - (0 : ℝ)) * MvPolynomial.X j +
          MvPolynomial.C (0 : ℝ) * (∑ i : Fin n, MvPolynomial.X i)) f.1).coeff m)
        = (MvPolynomial.aeval (fun j : Fin n => MvPolynomial.X j) f.1).coeff m := by
            rw [hsub]
    _ = f.1.coeff m := by
            rw [MvPolynomial.aeval_X_left_apply]

/-- coefficients of the substitution along 1/(k+1) tend to the coefficients of `f` -/
lemma subst_seq_coeff_tendsto (n d : ℕ) (f : H n d) (m : Fin n →₀ ℕ) :
    Tendsto (fun k : ℕ =>
      (MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - (1 : ℝ) / ((k : ℝ) + 1)) * MvPolynomial.X j +
          MvPolynomial.C ((1 : ℝ) / ((k : ℝ) + 1)) * (∑ i : Fin n, MvPolynomial.X i)) f.1).coeff m)
      atTop (𝓝 (f.1.coeff m)) := by
  have hcont := subst_coeff_continuous n d f m
  have hseq : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have ht : Tendsto (fun k : ℕ =>
      (MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - (1 : ℝ) / ((k : ℝ) + 1)) * MvPolynomial.X j +
          MvPolynomial.C ((1 : ℝ) / ((k : ℝ) + 1)) * (∑ i : Fin n, MvPolynomial.X i)) f.1).coeff m)
      atTop (𝓝 ((MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - (0 : ℝ)) * MvPolynomial.X j +
          MvPolynomial.C (0 : ℝ) * (∑ i : Fin n, MvPolynomial.X i)) f.1).coeff m)) :=
    hcont.continuousAt.tendsto.comp hseq
  rw [subst_coeff_at_zero n d f m] at ht
  exact ht

/-- if a sequence lies in the closure of Ŀ and converges to f, then f is in the closure -/
lemma mem_closure_of_seq_in_closure (n d : ℕ) (u : ℕ → H n d) (f : H n d)
    (hmem : ∀ k : ℕ, u k ∈ closure (Ŀ n d))
    (hlim : Tendsto u atTop (𝓝 f)) :
    f ∈ closure (Ŀ n d) := by
  exact (isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall hmem))

/-- positive scalar multiples of elements of the closure of Ŀ stay in the closure -/
lemma smul_mem_closure_strict {n d : ℕ} (hn : 0 < n) {c : ℝ} (hc : 0 < c)
    (f : H n d) (hf : f ∈ closure (Ŀ n d)) :
    c • f ∈ closure (Ŀ n d) := by
  classical
  let φ : H n d → H n d := fun x => c • x
  have hcont : Continuous φ := continuous_const_smul c
  have him : φ '' closure (Ŀ n d) ⊆ closure (φ '' Ŀ n d) :=
    image_closure_subset_closure_image hcont
  have hφ : φ '' Ŀ n d ⊆ Ŀ n d := by
    rintro y ⟨x, hx, rfl⟩
    exact smul_mem_strict n d hn hc x hx
  have hc2 : closure (φ '' Ŀ n d) ⊆ closure (Ŀ n d) := closure_mono hφ
  have hmem : φ f ∈ closure (φ '' Ŀ n d) := him ⟨f, hf, rfl⟩
  exact hc2 hmem

/-- the homotopy part for degree ≥ 3 (non-zero case) -/
lemma homotopy_mem_closure (n d : ℕ) (hn : 0 < n) (hd : 3 ≤ d) (f : H n d)
    (hf : f ∈ L n d) (hf0 : f ≠ 0) :
    f ∈ closure (Ŀ n d) := by
  classical
  let θ : ℕ → ℝ := fun k => (1 : ℝ) / ((k : ℝ) + 1)
  have hθ0 : ∀ k : ℕ, 0 < θ k := by
    intro k
    dsimp [θ]
    positivity
  have hθ1 : ∀ k : ℕ, θ k ≤ 1 := by
    intro k
    dsimp [θ]
    have hk1 : (1 : ℝ) ≤ ((k : ℝ) + 1) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.succ_pos k))
    rw [div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)]
    nlinarith
  have hmem : ∀ k : ℕ, ∃ g : H n d, g ∈ L n d ∧ g ∈ P n d ∧
      g.1 = MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - θ k) * MvPolynomial.X j +
          MvPolynomial.C (θ k) * (∑ i : Fin n, MvPolynomial.X i)) f.1 := fun k =>
    subst_mem_L_inter_P n d hn f hf hf0 (hθ0 k) (hθ1 k)
  let u : ℕ → H n d := fun k => Classical.choose (hmem k)
  have hu : ∀ k : ℕ, (u k ∈ L n d) ∧ (u k ∈ P n d) ∧
      (u k).1 = MvPolynomial.aeval (fun j : Fin n =>
        MvPolynomial.C (1 - θ k) * MvPolynomial.X j +
          MvPolynomial.C (θ k) * (∑ i : Fin n, MvPolynomial.X i)) f.1 := fun k =>
    Classical.choose_spec (hmem k)
  have hucl : ∀ k : ℕ, u k ∈ closure (Ŀ n d) := by
    intro k
    exact (L_inter_P_subset_closure_strict n d hn) ⟨(hu k).1, (hu k).2.1⟩
  have hulim : Tendsto u atTop (𝓝 f) := by
    refine tendsto_of_coeff_tendsto n d u f ?_
    intro m
    have hseq : Tendsto (fun k : ℕ =>
        (MvPolynomial.aeval (fun j : Fin n =>
          MvPolynomial.C (1 - ((1 : ℝ) / ((k : ℝ) + 1))) * MvPolynomial.X j +
            MvPolynomial.C (((1 : ℝ) / ((k : ℝ) + 1))) * (∑ i : Fin n, MvPolynomial.X i)) f.1).coeff m.1)
        atTop (𝓝 (f.1.coeff m.1)) := subst_seq_coeff_tendsto n d f m.1
    have heq : (fun k : ℕ => (u k).1.coeff m.1) = fun k : ℕ =>
        (MvPolynomial.aeval (fun j : Fin n =>
          MvPolynomial.C (1 - ((1 : ℝ) / ((k : ℝ) + 1))) * MvPolynomial.X j +
            MvPolynomial.C (((1 : ℝ) / ((k : ℝ) + 1))) * (∑ i : Fin n, MvPolynomial.X i)) f.1).coeff m.1 := by
      funext k
      dsimp [θ] at hu
      rw [(hu k).2.2]
      rfl
    rw [heq]
    exact hseq
  exact mem_closure_of_seq_in_closure n d u f hucl hulim

/-- 0 is in the closure of Ŀ for degree ≥ 3 -/
lemma zero_mem_closure_strict_of_ge_three (n d : ℕ) (hn : 0 < n) (hd : 3 ≤ d) :
    (0 : H n d) ∈ closure (Ŀ n d) := by
  classical
  obtain ⟨f0, hf0L, hf0ne⟩ := monom_pow_mem_L n d hn
  have hf0cl : f0 ∈ closure (Ŀ n d) := homotopy_mem_closure n d hn hd f0 hf0L hf0ne
  let w : ℕ → H n d := fun k => ((1 : ℝ) / ((k : ℝ) + 1)) • f0
  have hwk : ∀ k : ℕ, w k ∈ closure (Ŀ n d) := by
    intro k
    dsimp [w]
    apply smul_mem_closure_strict hn (by positivity : 0 < (1 : ℝ) / ((k : ℝ) + 1)) f0 hf0cl
  have hwlim : Tendsto w atTop (𝓝 (0 : H n d)) := by
    refine tendsto_of_coeff_tendsto n d w 0 ?_
    intro m
    have hck : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have ht01 : Tendsto (fun k : ℕ => ((1 : ℝ) / ((k : ℝ) + 1)) * f0.1.coeff m.1) atTop
        (𝓝 ((0 : ℝ) * f0.1.coeff m.1)) := hck.mul tendsto_const_nhds
    have ht0 : Tendsto (fun k : ℕ => ((1 : ℝ) / ((k : ℝ) + 1)) * f0.1.coeff m.1) atTop (𝓝 0) := by
      rw [show (0 : ℝ) * f0.1.coeff m.1 = 0 by ring] at ht01
      exact ht01
    have heq : (fun k : ℕ => (w k).1.coeff m.1) = fun k : ℕ => ((1 : ℝ) / ((k : ℝ) + 1)) * f0.1.coeff m.1 := by
      funext k
      dsimp [w]
      rfl
    have hz : (0 : H n d).1.coeff m.1 = 0 := by rfl
    rw [heq, hz]
    exact ht0
  exact mem_closure_of_seq_in_closure n d w 0 hwk hwlim


/-- degree ≥ 3 -/
lemma L_subset_closure_ge_three (n d : ℕ) (hn : 0 < n) (hd : 3 ≤ d) :
    L n d ⊆ closure (Ŀ n d) := by
  intro f hf
  by_cases hf0 : f = 0
  · rw [hf0]
    exact zero_mem_closure_strict_of_ge_three n d hn hd
  · exact homotopy_mem_closure n d hn hd f hf hf0

/-- degree ≤ 1 -/
lemma L_subset_closure_le_one (n d : ℕ) (hd : d ≤ 1) : L n d ⊆ closure (Ŀ n d) := by
  intro f hf
  have hd0 : d = 0 ∨ d = 1 := by omega
  rcases hd0 with rfl | rfl
  · have hg : f ∈ S n 0 := by simpa [L] using hf
    have hcl : closure (Ŀ n 0) = S n 0 := by
      rw [show Ŀ n 0 = P n 0 by rfl]
      exact closure_P_eq_S_of_degree_le_one n 0 (by norm_num)
    rw [hcl]
    exact hg
  · have hg : f ∈ S n 1 := by simpa [L] using hf
    have hcl : closure (Ŀ n 1) = S n 1 := by
      rw [show Ŀ n 1 = P n 1 by rfl]
      exact closure_P_eq_S_of_degree_le_one n 1 (by norm_num)
    rw [hcl]
    exact hg

/-- degree two -/
lemma L_subset_closure_eq_two (n : ℕ) (hn : 0 < n) : L n 2 ⊆ closure (Ŀ n 2) := by
  have hcl : closure (Ŀ n 2) = L n 2 := closure_strict_eq_L_of_degree_le_two n hn
  intro f hf
  rw [hcl]
  exact hf

/-- The statement assigned to this file: `L n d ⊆ closure (Ŀ n d)` for `0 < n`. -/
theorem L_subset_closure (n d : ℕ) (hn : 0 < n) : L n d ⊆ closure (Ŀ n d) := by
  intro f hf
  by_cases hd3 : 3 ≤ d
  · exact L_subset_closure_ge_three n d hn hd3 hf
  · by_cases hd2 : d = 2
    · subst d
      exact L_subset_closure_eq_two n hn hf
    · have hle : d ≤ 1 := by omega
      exact L_subset_closure_le_one n d hle hf

end

end Commons.LorentzianPolynomials
