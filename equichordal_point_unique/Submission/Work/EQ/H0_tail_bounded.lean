import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.fan_ne_germC
import Submission.Work.EQ.chain_pt_far_germ

/-! # The tails of chains near a point of `⁰H` (Rychlik Thm 7 corollary)

`H0_tail_bounded`: on a product-topology neighbourhood of `p ∈ ⁰H`, the forward tail index and
the backward tail index of the chains are bounded, so that the chains in the neighbourhood are
the fan values of words of bounded length.

The file contains the algebraic and combinatorial backbone of the proof.

* `fwdAlt`, `fwd_pair_dichotomy`, `fwd_branch_separation`: a regular pair has exactly two forward
  values `fwdC a P` (principal) and `fwdAlt a P`, and they are separated by `1`.
* `invBranch_true_ne_false`, `invBranch_separation`, `continuousAt_invBranch`: the two backward
  branches of a regular point are distinct, separated by `1`, and continuous where `invBranch` is
  analytic; so the *labels* of the steps of a chain are well defined.
* `IsChainWord`, `exists_isChainWord`: a chain whose tail is the stable germ from index `N` on is
  the fan value of a word of length `N` whose letters are exactly its step labels.  This reduces
  the bounded-tail statement to a statement about words.

* `leaf_of_all_true`: if the letters of the word from position `m` on are all `true`, the chain
  is on the principal leaf from index `m`; hence the forward tail index is bounded by the position
  of the last non-`true` letter.

* `chain_pt_far_germ` (colleague's file `Submission/Work/EQ/chain_pt_far_germ.lean`): a chain
  strictly below its tail index is bounded away from the principal leaf by `c‖λⁿψ₁‖`.

**Proof.**  `forward_tail_bounded` is the engine: for a chain `p` (so `ψ₁ p ≠ 0`) pick a level
`n` at which `‖λⁿ ψ₁ p‖ < min δ ρ / 2`, where `δ` is the separation constant of
`chain_pt_far_germ` and `ρ` the analyticity radius of `germC`.  Claim: there is `k ≥ n` such
that every chain `q` with `q.1 j ≈ p.1 j` for `|j| ≤ k` and `ψ₁ q ≈ ψ₁ p` has `TailP a h q n`.
Otherwise one gets chains `q_k → p` with `k < tailIdx a h q_k`, i.e. `n < tailIdx a h q_k` for
`k ≥ n`; then `chain_pt_far_germ` gives
`c ‖λⁿ ψ₁ q_k‖ ≤ ‖(q_k).1 n - germC a h (λⁿ ψ₁ q_k)‖` while the left side tends to
`c ‖λⁿ ψ₁ p‖ > 0` and the right side to `‖p.1 n - germC a h (λⁿ ψ₁ p)‖ = 0` (using
`TailP a h p n`).  The backward statement is the same engine applied to the mirror chains
`mirrorChain p`, `mirrorChain q`, which swap `ψ₁` and `ψ₂` and the two leaves
(`isChain_mirrorChain`). -/

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section


/-- The non-principal forward branch of the relation. -/
def fwdAlt (a : ℝ) (P : ℂ × ℂ) : ℂ × ℂ := -P - (brho (subO2 a P))⁻¹ • subO2 a P

lemma fwdC_eq (a : ℝ) (P : ℂ × ℂ) :
    fwdC a P = -P + (brho (subO2 a P))⁻¹ • subO2 a P := by
  ext <;>
    simp only [fwdC, subO2, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, div_eq_mul_inv, Prod.fst_neg, Prod.snd_neg] <;> ring

lemma subO2_ne_zero_of {a : ℝ} {P : ℂ × ℂ} (h : bsq (subO2 a P) ≠ 0) : subO2 a P ≠ 0 := by
  intro h0; exact h (by rw [h0]; simp [bsq])

lemma subO1_ne_zero_of {a : ℝ} {Q : ℂ × ℂ} (h : bsq (subO1 a Q) ≠ 0) : subO1 a Q ≠ 0 := by
  intro h0; exact h (by rw [h0]; simp [bsq])

/-- Forward branch form: a regular pair determines `Q` from `P` up to the branch sign. -/
lemma fwd_decomp' {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) (hP : bsq (subO2 a P) ≠ 0) :
    ∃ c : ℂ, c ^ 2 * bsq (subO2 a P) = 1 ∧ Q = -P + c • subO2 a P := by
  have hpar : par (P + Q) (subO2 a P) := by
    rw [par, subO2]
    simp only [Prod.fst_add, Prod.snd_add]
    linear_combination h.2
  obtain ⟨c, hc⟩ := exists_smul_of_par ((par_comm (X := subO2 a P) (Y := P + Q)).mpr hpar)
    (subO2_ne_zero_of hP)
  refine ⟨c, ?_, ?_⟩
  · have hbs : bsq (P + Q) = c ^ 2 * bsq (subO2 a P) := by rw [hc, bsq_smul]
    rw [← hbs]
    show (P.1 + Q.1) ^ 2 + (P.2 + Q.2) ^ 2 = 1
    linear_combination h.1
  · rw [← hc]; abel

/-- **Forward dichotomy.** A regular pair has its second point equal to one of the two forward
branches. -/
theorem fwd_pair_dichotomy {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q) (hP : bsq (subO2 a P) ≠ 0) :
    Q = fwdC a P ∨ Q = fwdAlt a P := by
  obtain ⟨c, hc, hQ⟩ := fwd_decomp' h hP
  have hρ : brho (subO2 a P) ≠ 0 := brho_ne_zero hP
  have hsq : (c * brho (subO2 a P)) ^ 2 = 1 := by rw [mul_pow, brho_sq, hc]
  have h2 : c * brho (subO2 a P) = 1 ∨ c * brho (subO2 a P) = -1 := by
    have h0 : (c * brho (subO2 a P) - 1) * (c * brho (subO2 a P) + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp h0 with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  have hcv : c = (brho (subO2 a P))⁻¹ ∨ c = -(brho (subO2 a P))⁻¹ := by
    rcases h2 with h1 | h1
    · left; exact eq_inv_of_mul_eq_one_left h1
    · right
      have h2' : c * (-(brho (subO2 a P))) = 1 := by rw [mul_neg, h1, neg_neg]
      simpa using eq_inv_of_mul_eq_one_left h2'
  rcases hcv with h1 | h1
  · left; rw [hQ, fwdC_eq, h1]
  · right; rw [hQ, fwdAlt, h1]; simp only [neg_smul, sub_eq_add_neg]

/-- The two forward branches at a regular point are separated by `1`. -/
theorem fwd_branch_separation (a : ℝ) (P : ℂ × ℂ) (hP : bsq (subO2 a P) ≠ 0) :
    1 ≤ ‖fwdC a P - fwdAlt a P‖ := by
  have hρ : brho (subO2 a P) ≠ 0 := brho_ne_zero hP
  have hv : subO2 a P ≠ 0 := subO2_ne_zero_of hP
  have hdiff : fwdC a P - fwdAlt a P = (2 * (brho (subO2 a P))⁻¹) • subO2 a P := by
    rw [fwdC_eq, fwdAlt]
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_neg, Prod.snd_neg, smul_eq_mul] <;> ring
  have hρ2 : ‖brho (subO2 a P)‖ ^ 2 = ‖bsq (subO2 a P)‖ := by
    rw [← norm_pow, brho_sq]
  have hbsq : ‖bsq (subO2 a P)‖ ≤ 2 * ‖subO2 a P‖ ^ 2 := by
    rw [bsq]
    have h1 : ‖(subO2 a P).1 ^ 2 + (subO2 a P).2 ^ 2‖ ≤ ‖(subO2 a P).1‖ ^ 2 + ‖(subO2 a P).2‖ ^ 2 := by
      calc ‖(subO2 a P).1 ^ 2 + (subO2 a P).2 ^ 2‖
          ≤ ‖(subO2 a P).1 ^ 2‖ + ‖(subO2 a P).2 ^ 2‖ := norm_add_le _ _
        _ = ‖(subO2 a P).1‖ ^ 2 + ‖(subO2 a P).2‖ ^ 2 := by rw [norm_pow, norm_pow]
    have h2 : ‖(subO2 a P).1‖ ≤ ‖subO2 a P‖ := by
      rw [Prod.norm_def]; exact le_max_left _ _
    have h3 : ‖(subO2 a P).2‖ ≤ ‖subO2 a P‖ := by
      rw [Prod.norm_def]; exact le_max_right _ _
    have h4 : (0:ℝ) ≤ ‖subO2 a P‖ := norm_nonneg _
    nlinarith [h1, h2, h3, h4, norm_nonneg (subO2 a P).1, norm_nonneg (subO2 a P).2]
  have hnorm : ‖fwdC a P - fwdAlt a P‖ = 2 * ‖subO2 a P‖ / ‖brho (subO2 a P)‖ := by
    rw [hdiff, norm_smul, norm_mul]
    have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [h2n, norm_inv]
    field_simp
  rw [hnorm]
  rw [le_div_iff₀ (norm_pos_iff.mpr hρ)]
  have hsq : ‖brho (subO2 a P)‖ ^ 2 ≤ 2 * ‖subO2 a P‖ ^ 2 := by rw [hρ2]; exact hbsq
  have hpp : (0:ℝ) < ‖subO2 a P‖ := norm_pos_iff.mpr hv
  nlinarith [hsq, hpp, norm_nonneg (brho (subO2 a P))]

/-- The two backward branches at a regular point are distinct. -/
theorem invBranch_true_ne_false {a : ℝ} {Q : ℂ × ℂ} (hQ : bsq (subO1 a Q) ≠ 0) :
    invBranch a true Q ≠ invBranch a false Q := by
  intro h
  have hρ : brho (subO1 a Q) ≠ 0 := brho_ne_zero hQ
  have hv : subO1 a Q ≠ 0 := subO1_ne_zero_of hQ
  have h1 := invBranch_add a true Q
  have h2 := invBranch_add a false Q
  rw [ite_eq_left (by simp), one_smul] at h1
  rw [ite_eq_right (by simp), neg_one_smul] at h2
  have h2' : invBranch a true Q + Q = -(((brho (subO1 a Q))⁻¹) • subO1 a Q) := by
    simpa only [h] using h2
  have h3 : ((brho (subO1 a Q))⁻¹) • subO1 a Q = -(((brho (subO1 a Q))⁻¹) • subO1 a Q) :=
    h1.symm.trans h2'
  have h4 : (2 * ((brho (subO1 a Q))⁻¹)) • subO1 a Q = 0 := by
    rw [two_mul, add_smul]
    nth_rewrite 1 [h3]
    rw [neg_add_cancel]
  have h5 : (2 * ((brho (subO1 a Q))⁻¹)) = 0 := by
    rcases smul_eq_zero.mp h4 with hc | hc
    · exact hc
    · exact absurd hc hv
  have h6 : (brho (subO1 a Q))⁻¹ = 0 := by
    rcases mul_eq_zero.mp h5 with hc | hc
    · exact absurd hc (by norm_num)
    · exact hc
  exact hρ (inv_eq_zero.mp h6)



/-- `IsChainWord a h p N ε`: `ε` is the word of the chain `p` over the annulus `[0,N]`. -/
def IsChainWord (a : ℝ) (h : ℂ → ℂ) (p : ChainData) (N : ℕ) (ε : List Bool) : Prop :=
  ε.length = N ∧ p.1 0 = fan a h ε p.2.1 ∧
    ∀ j : ℕ, j < N → p.1 (j : ℤ) = invBranch a (ε.getD j true) (p.1 ((j : ℤ) + 1))

/-- **A chain is a fan value with its word of labels.** -/
theorem exists_isChainWord {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} :
    ∀ (N : ℕ) (p : ChainData), IsChain a h p →
      (∀ n : ℕ, N ≤ n → p.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * p.2.1)) →
      ∃ ε : List Bool, IsChainWord a h p N ε := by
  intro N
  induction N with
  | zero =>
    intro p hp htail
    refine ⟨[], rfl, ?_, ?_⟩
    · simpa [fan] using htail 0 le_rfl
    · intro j hj; exact absurd hj (by omega)
  | succ N ih =>
    intro p hp htail
    have hp' : IsChain a h (shiftZ a 1 p) := isChain_shiftZ ha0 ha1 hp 1
    have htail' : ∀ n : ℕ, N ≤ n →
        (shiftZ a 1 p).1 (n : ℤ) =
          germC a h (((eqLam a : ℝ) : ℂ) ^ n * (shiftZ a 1 p).2.1) := by
      intro n hn
      rw [shiftZ_fst, shiftZ_psi1, zpow_one,
        show p.1 ((n : ℤ) + 1) = germC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1) * p.2.1)
          from htail (n + 1) (by omega)]
      congr 1
      rw [pow_succ]; ring
    obtain ⟨ε, hlen, hfan, hlab⟩ := ih (shiftZ a 1 p) hp' htail'
    have hfst : p.1 1 = fan a h ε (((eqLam a : ℝ) : ℂ) * p.2.1) := by
      have h1 : (shiftZ a 1 p).1 0 = p.1 1 := by simp [shiftZ]
      have h2 : (shiftZ a 1 p).2.1 = ((eqLam a : ℝ) : ℂ) * p.2.1 := by simp [shiftZ]
      rw [← h1, hfan, h2]
    have hreg0 : RegPair a (p.1 0) (p.1 1) := by simpa using hp.1 0
    rcases H0_invParam_ge_exists_invBranch hreg0.1 hreg0.2.2 with h | h
    · refine ⟨true :: ε, by simp [hlen], ?_, ?_⟩
      · rw [show p.1 0 = invBranch a true (p.1 1) from h, hfst]; rfl
      · intro j hj
        match j with
        | 0 => simpa using h
        | (k+1) =>
          have hk : k < N := by simpa using hj
          have h1 : (shiftZ a 1 p).1 (k : ℤ)
              = invBranch a (ε.getD k true) ((shiftZ a 1 p).1 ((k : ℤ) + 1)) :=
            hlab k hk
          have e0 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
          have e1 : (((k + 1 : ℕ) : ℤ) + 1) = (k : ℤ) + 2 := by push_cast; ring
          rw [e1, e0]
          simp only [List.getD_cons_succ, shiftZ_fst] at h1 ⊢
          exact h1
    · refine ⟨false :: ε, by simp [hlen], ?_, ?_⟩
      · rw [show p.1 0 = invBranch a false (p.1 1) from h, hfst]; rfl
      · intro j hj
        match j with
        | 0 => simpa using h
        | (k+1) =>
          have hk : k < N := by simpa using hj
          have h1 : (shiftZ a 1 p).1 (k : ℤ)
              = invBranch a (ε.getD k true) ((shiftZ a 1 p).1 ((k : ℤ) + 1)) :=
            hlab k hk
          have e0 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; rfl
          have e1 : (((k + 1 : ℕ) : ℤ) + 1) = (k : ℤ) + 2 := by push_cast; ring
          rw [e1, e0]
          simp only [List.getD_cons_succ, shiftZ_fst] at h1 ⊢
          exact h1



/-- The two backward branches at a regular point are separated by `1`. -/
theorem invBranch_separation {a : ℝ} {Q : ℂ × ℂ} (hQ : bsq (subO1 a Q) ≠ 0) :
    1 ≤ ‖invBranch a true Q - invBranch a false Q‖ := by
  have hρ : brho (subO1 a Q) ≠ 0 := brho_ne_zero hQ
  have hv : subO1 a Q ≠ 0 := by
    intro h0; exact hQ (by rw [h0]; simp [bsq])
  have h1 := invBranch_add a true Q
  have h2 := invBranch_add a false Q
  rw [ite_eq_left (by simp), one_smul] at h1
  rw [ite_eq_right (by simp), neg_one_smul] at h2
  have hdiff : invBranch a true Q - invBranch a false Q
      = (2 * (brho (subO1 a Q))⁻¹) • subO1 a Q := by
    have h3 : invBranch a true Q - invBranch a false Q
        = (invBranch a true Q + Q) - (invBranch a false Q + Q) := by abel
    rw [h3, h1, h2, sub_neg_eq_add, two_mul, add_smul]
  have hρ2 : ‖brho (subO1 a Q)‖ ^ 2 = ‖bsq (subO1 a Q)‖ := by
    rw [← norm_pow, brho_sq]
  have hbsq : ‖bsq (subO1 a Q)‖ ≤ 2 * ‖subO1 a Q‖ ^ 2 := by
    rw [bsq]
    have h1' : ‖(subO1 a Q).1 ^ 2 + (subO1 a Q).2 ^ 2‖ ≤
        ‖(subO1 a Q).1‖ ^ 2 + ‖(subO1 a Q).2‖ ^ 2 := by
      calc ‖(subO1 a Q).1 ^ 2 + (subO1 a Q).2 ^ 2‖
          ≤ ‖(subO1 a Q).1 ^ 2‖ + ‖(subO1 a Q).2 ^ 2‖ := norm_add_le _ _
        _ = ‖(subO1 a Q).1‖ ^ 2 + ‖(subO1 a Q).2‖ ^ 2 := by rw [norm_pow, norm_pow]
    have h2' : ‖(subO1 a Q).1‖ ≤ ‖subO1 a Q‖ := by
      rw [Prod.norm_def]; exact le_max_left _ _
    have h3' : ‖(subO1 a Q).2‖ ≤ ‖subO1 a Q‖ := by
      rw [Prod.norm_def]; exact le_max_right _ _
    have h4' : (0:ℝ) ≤ ‖subO1 a Q‖ := norm_nonneg _
    nlinarith [h1', h2', h3', h4', norm_nonneg (subO1 a Q).1, norm_nonneg (subO1 a Q).2]
  have hnorm : ‖invBranch a true Q - invBranch a false Q‖
      = 2 * ‖subO1 a Q‖ / ‖brho (subO1 a Q)‖ := by
    rw [hdiff, norm_smul, norm_mul]
    have h2n : ‖(2:ℂ)‖ = 2 := by norm_num
    rw [h2n, norm_inv]
    field_simp
  rw [hnorm]
  rw [le_div_iff₀ (norm_pos_iff.mpr hρ)]
  have hsq : ‖brho (subO1 a Q)‖ ^ 2 ≤ 2 * ‖subO1 a Q‖ ^ 2 := by rw [hρ2]; exact hbsq
  have hpp : (0:ℝ) < ‖subO1 a Q‖ := norm_pos_iff.mpr hv
  nlinarith [hsq, hpp, norm_nonneg (brho (subO1 a Q))]

/-- `invBranch a s` is continuous at points where the radicand lies in the slit plane. -/
theorem continuousAt_invBranch {a : ℝ} {s : Bool} {Q : ℂ × ℂ}
    (h : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ∈ Complex.slitPlane) :
    ContinuousAt (invBranch a s) Q := by
  have hD : ContinuousAt (fun Q : ℂ × ℂ =>
      (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) Q :=
    (((continuousAt_fst.add continuousAt_const).pow 2).add (continuousAt_snd.pow 2))
  have hroot : ContinuousAt (fun Q : ℂ × ℂ =>
      ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ)) Q :=
    hD.cpow continuousAt_const h
  have hne : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ≠ 0 := Complex.slitPlane_ne_zero h
  have hrootne : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h0
    have h2 := cpow_half_sq ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2)
    rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h2
    exact hne h2.symm
  exact ContinuousAt.prodMk
    (continuousAt_fst.neg.add
      ((continuousAt_const.mul (continuousAt_fst.add continuousAt_const)).div hroot hrootne))
    (continuousAt_snd.neg.add
      ((continuousAt_const.mul continuousAt_snd).div hroot hrootne))


/-- **Leaf propagation from the word.** -/
theorem leaf_of_all_true {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N m : ℕ}
    {p : ChainData} {ε : List Bool} (hε : IsChainWord a h p N ε)
    (htail : ∀ n : ℕ, N ≤ n → p.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * p.2.1))
    (hm : m ≤ N) (hall : ∀ j : ℕ, m ≤ j → j < N → ε.getD j true = true)
    {ρ : ℝ} (hball : ∀ n : ℕ, m ≤ n → n ≤ N → ((eqLam a : ℂ) ^ n * p.2.1) ∈ Metric.ball 0 ρ)
    (hinv : ∀ v ∈ Metric.ball (0 : ℂ) ρ,
      invBranch a true (germC a h ((eqLam a : ℂ) * v)) = germC a h v) :
    ∀ n : ℕ, m ≤ n → p.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * p.2.1) := by
  have step : ∀ k : ℕ, k < N → (m ≤ k + 1 → p.1 ((k + 1 : ℕ) : ℤ)
        = germC a h ((eqLam a : ℂ) ^ (k + 1) * p.2.1)) →
      (m ≤ k → p.1 (k : ℤ) = germC a h ((eqLam a : ℂ) ^ k * p.2.1)) := by
    intro k hk ih hkm
    have hnext : p.1 ((k + 1 : ℕ) : ℤ)
        = germC a h ((eqLam a : ℂ) ^ (k + 1) * p.2.1) := ih (by omega)
    have hstep : p.1 (k : ℤ) = invBranch a (ε.getD k true) (p.1 ((k : ℤ) + 1)) :=
      hε.2.2 k hk
    have hletter : ε.getD k true = true := hall k hkm hk
    have hk' : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by omega
    have hpow : ((eqLam a : ℂ) ^ (k + 1) * p.2.1)
        = (eqLam a : ℂ) * ((eqLam a : ℂ) ^ k * p.2.1) := by rw [pow_succ]; ring
    rw [hstep, hletter, hk', hnext, hpow]
    exact hinv _ (hball k hkm (le_of_lt hk))
  have base : m ≤ N → p.1 (N : ℤ) = germC a h ((eqLam a : ℂ) ^ N * p.2.1) :=
    fun _ => htail N le_rfl
  have key : ∀ k : ℕ, k ≤ N → m ≤ k →
      p.1 (k : ℤ) = germC a h ((eqLam a : ℂ) ^ k * p.2.1) := fun k hkN =>
    Nat.decreasingInduction (n := N) (m := k)
      (motive := fun j _ => m ≤ j → p.1 (j : ℤ) = germC a h ((eqLam a : ℂ) ^ j * p.2.1))
      step base hkN
  intro n hmn
  rcases le_or_gt n N with hnN | hnN
  · exact key n hnN hmn
  · exact htail n (le_of_lt hnN)

lemma norm_eqMirror (Z : ℂ × ℂ) : ‖eqMirror Z‖ = ‖Z‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  simp [eqMirror]

lemma eqMirror_sub (X Y : ℂ × ℂ) : eqMirror X - eqMirror Y = eqMirror (X - Y) := by
  ext <;> simp [eqMirror] <;> ring

lemma eqMirror_eqMirror (Z : ℂ × ℂ) : eqMirror (eqMirror Z) = Z := by
  ext <;> simp [eqMirror]

theorem forward_tail_bounded {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {p : ChainData} (hp : IsChain a h p) :
    ∃ (N K : ℕ) (ε : ℝ), 0 < ε ∧ N ≤ K ∧
      ∀ q : ChainData, IsChain a h q →
        (∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q.1 k - p.1 k‖ < ε) →
        ‖q.2.1 - p.2.1‖ < ε → TailP a h q N := by
  have hlam0 : (0 : ℝ) < eqLam a := by rw [eqLam]; positivity
  have hlam1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  have hlamC : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlam0)
  obtain ⟨ρ, hρ0, hAnC⟩ := germC_analytic ha0 ha1 hh
  obtain ⟨δf, cf, hδf0, hcf0, hfar⟩ := chain_pt_far_germ ha0 ha1 hh
  have hcrit : (0 : ℝ) < min δf ρ / 2 := by positivity
  have hlim : Tendsto (fun n : ℕ => ‖(eqLam a : ℂ) ^ n * p.2.1‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (eqLam a) ^ n * ‖p.2.1‖) atTop (𝓝 0) := by
      have hn := (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const ‖p.2.1‖
      simpa using hn
    refine h1.congr' ?_
    filter_upwards with k
    have hn : ‖(((eqLam a : ℝ)) : ℂ)‖ = eqLam a := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hlam0.le]
    rw [norm_mul, norm_pow, hn]
  obtain ⟨n, hn1, hn2⟩ := ((hlim.eventually (eventually_lt_nhds hcrit)).and
    (eventually_ge_atTop (tailIdx a h p))).exists
  have htailpn : TailP a h p n := TailP_mono (TailP_of_isChain hp) hn2
  have hΛ0 : (0 : ℝ) < ‖(eqLam a : ℂ) ^ n * p.2.1‖ := by
    rw [norm_pos_iff]
    exact mul_ne_zero (pow_ne_zero n hlamC) hp.2.1
  have hΛρ : (eqLam a : ℂ) ^ n * p.2.1 ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith [min_le_right δf ρ, hn1, hρ0]
  by_contra hcon
  have hseq : ∀ k : ℕ, ∃ q : ChainData, IsChain a h q ∧
      (∀ j : ℤ, |j| ≤ (k : ℤ) → ‖q.1 j - p.1 j‖ < 1 / ((k : ℝ) + 1)) ∧
      ‖q.2.1 - p.2.1‖ < 1 / ((k : ℝ) + 1) ∧ ¬ TailP a h q k := by
    intro k
    by_contra hk
    apply hcon
    refine ⟨k, k, 1 / ((k : ℝ) + 1), by positivity, le_rfl, ?_⟩
    intro q hqish hwin hpsi
    by_contra htp
    exact hk ⟨q, hqish, hwin, hpsi, htp⟩
  choose q hqish hqw hqpsi hqnot using hseq
  have hNgt : ∀ k : ℕ, k < tailIdx a h (q k) := by
    intro k
    by_contra hle
    exact hqnot k ((tailIdx_le_iff (tailP_of_isChain (hqish k))).mp (not_lt.mp hle))
  have hpsiT : Tendsto (fun k : ℕ => (q k).2.1) atTop (𝓝 p.2.1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun k : ℕ => 1 / ((k : ℝ) + 1)) (fun k => norm_nonneg _)
      (fun k => le_of_lt (hqpsi k)) ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hq1T : Tendsto (fun k : ℕ => (q k).1 (n : ℤ)) atTop (𝓝 (p.1 (n : ℤ))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (g := fun k : ℕ => 1 / ((k : ℝ) + 1))
      (Eventually.of_forall (fun k => norm_nonneg _)) ?_ ?_
    · filter_upwards [eventually_ge_atTop n] with k hk
      exact le_of_lt (hqw k (n : ℤ) (by
        rw [abs_of_nonneg (Int.natCast_nonneg n)]
        exact_mod_cast hk))
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlamT : Tendsto (fun k : ℕ => (eqLam a : ℂ) ^ n * (q k).2.1) atTop
      (𝓝 ((eqLam a : ℂ) ^ n * p.2.1)) := hpsiT.const_mul _
  have hgermT : Tendsto (fun k : ℕ => germC a h ((eqLam a : ℂ) ^ n * (q k).2.1)) atTop
      (𝓝 (germC a h ((eqLam a : ℂ) ^ n * p.2.1))) :=
    ((hAnC _ hΛρ).continuousAt).tendsto.comp hlamT
  have hFT : Tendsto (fun k : ℕ =>
      ‖(q k).1 (n : ℤ) - germC a h ((eqLam a : ℂ) ^ n * (q k).2.1)‖) atTop (𝓝 0) := by
    have h1 := hq1T.sub hgermT
    have hz : p.1 (n : ℤ) - germC a h ((eqLam a : ℂ) ^ n * p.2.1) = 0 := by
      rw [htailpn n le_rfl, sub_self]
    rw [hz] at h1
    simpa using h1.norm
  have hFev : ∀ᶠ k in atTop,
      ‖(q k).1 (n : ℤ) - germC a h ((eqLam a : ℂ) ^ n * (q k).2.1)‖ <
        cf * ‖(eqLam a : ℂ) ^ n * p.2.1‖ / 2 :=
    hFT.eventually (eventually_lt_nhds (div_pos (mul_pos hcf0 hΛ0) (by norm_num)))
  have hBev : ∀ᶠ k in atTop, ‖(eqLam a : ℂ) ^ n * (q k).2.1‖ < δf :=
    hlamT.norm.eventually (eventually_lt_nhds (by linarith [min_le_left δf ρ, hn1, hδf0]))
  have hGev : ∀ᶠ k in atTop,
      cf * ‖(eqLam a : ℂ) ^ n * p.2.1‖ / 2 ≤ cf * ‖(eqLam a : ℂ) ^ n * (q k).2.1‖ := by
    have hsubT : Tendsto (fun k : ℕ =>
        ‖(eqLam a : ℂ) ^ n * (q k).2.1 - ((eqLam a : ℂ) ^ n * p.2.1)‖) atTop (𝓝 0) := by
      have hh1 := (hlamT.sub_const ((eqLam a : ℂ) ^ n * p.2.1)).norm
      simpa using hh1
    have h3 : ∀ᶠ k in atTop,
        ‖(eqLam a : ℂ) ^ n * (q k).2.1 - ((eqLam a : ℂ) ^ n * p.2.1)‖ <
          ‖(eqLam a : ℂ) ^ n * p.2.1‖ / 2 :=
      hsubT.eventually (eventually_lt_nhds (by linarith))
    filter_upwards [h3] with k hk
    have h4 : ‖(eqLam a : ℂ) ^ n * p.2.1‖ ≤
        ‖(eqLam a : ℂ) ^ n * p.2.1 - ((eqLam a : ℂ) ^ n * (q k).2.1)‖ +
        ‖(eqLam a : ℂ) ^ n * (q k).2.1‖ := by
      have hh2 := norm_add_le ((eqLam a : ℂ) ^ n * p.2.1 - ((eqLam a : ℂ) ^ n * (q k).2.1))
        ((eqLam a : ℂ) ^ n * (q k).2.1)
      have he : ((eqLam a : ℂ) ^ n * p.2.1 - ((eqLam a : ℂ) ^ n * (q k).2.1)) +
          ((eqLam a : ℂ) ^ n * (q k).2.1) = (eqLam a : ℂ) ^ n * p.2.1 := by ring
      rwa [he] at hh2
    have h6 : ‖(eqLam a : ℂ) ^ n * p.2.1 - ((eqLam a : ℂ) ^ n * (q k).2.1)‖ =
        ‖(eqLam a : ℂ) ^ n * (q k).2.1 - ((eqLam a : ℂ) ^ n * p.2.1)‖ := norm_sub_rev _ _
    have h5 : ‖(eqLam a : ℂ) ^ n * p.2.1‖ / 2 ≤ ‖(eqLam a : ℂ) ^ n * (q k).2.1‖ := by
      linarith [h4, h6, hk]
    calc cf * ‖(eqLam a : ℂ) ^ n * p.2.1‖ / 2 = cf * (‖(eqLam a : ℂ) ^ n * p.2.1‖ / 2) := by ring
      _ ≤ cf * ‖(eqLam a : ℂ) ^ n * (q k).2.1‖ := mul_le_mul_of_nonneg_left h5 hcf0.le
  have hall : ∀ᶠ k in atTop, n ≤ k ∧ ‖(eqLam a : ℂ) ^ n * (q k).2.1‖ < δf ∧
      ‖(q k).1 (n : ℤ) - germC a h ((eqLam a : ℂ) ^ n * (q k).2.1)‖ <
        cf * ‖(eqLam a : ℂ) ^ n * p.2.1‖ / 2 ∧
      cf * ‖(eqLam a : ℂ) ^ n * p.2.1‖ / 2 ≤ cf * ‖(eqLam a : ℂ) ^ n * (q k).2.1‖ := by
    filter_upwards [eventually_ge_atTop n, hBev, hFev, hGev] with k hA hB hF hG
    exact ⟨hA, hB, hF, hG⟩
  obtain ⟨k, hkA, hkB, hkF, hkG⟩ := hall.exists
  have hnlt : n < tailIdx a h (q k) := lt_of_le_of_lt hkA (hNgt k)
  have hsep := hfar (hqish k) hnlt hkB
  linarith [hsep, hkF, hkG]

theorem H0_tail_bounded {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∀ p ∈ H0 a h, ∃ (N M : ℕ) (K : ℕ) (ε : ℝ), 0 < ε ∧ N ≤ K ∧ M ≤ K ∧
      ∀ q ∈ H0 a h,
        (∀ k : ℤ, |k| ≤ (K : ℤ) → ‖q.1 k - p.1 k‖ < ε) →
        ‖q.2.1 - p.2.1‖ < ε → ‖q.2.2 - p.2.2‖ < ε →
        (∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * q.2.1)) ∧
        (∀ n : ℕ, M ≤ n → q.1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * q.2.2)) := by
  intro p hp
  have hpc : IsChain a h p := isChain_of_mem_H0 hp
  obtain ⟨N₁, K₁, ε₁, hε₁0, hN₁K₁, hfwd₁⟩ := forward_tail_bounded ha0 ha1 hh hpc
  obtain ⟨N₂, K₂, ε₂, hε₂0, hN₂K₂, hfwd₂⟩ :=
    forward_tail_bounded ha0 ha1 hh (isChain_mirrorChain hpc)
  have h1k : (K₁ : ℤ) ≤ ((max K₁ K₂ : ℕ) : ℤ) := by exact_mod_cast le_max_left K₁ K₂
  have h2k : (K₂ : ℤ) ≤ ((max K₁ K₂ : ℕ) : ℤ) := by exact_mod_cast le_max_right K₁ K₂
  refine ⟨N₁, N₂, max K₁ K₂, min ε₁ ε₂, lt_min hε₁0 hε₂0, ?_, ?_, ?_⟩
  · exact le_trans hN₁K₁ (le_max_left _ _)
  · exact le_trans hN₂K₂ (le_max_right _ _)
  · intro q hq hwin hψ1 hψ2
    have hqc : IsChain a h q := isChain_of_mem_H0 hq
    refine ⟨?_, ?_⟩
    · intro nn hnn
      exact hfwd₁ q hqc
        (fun k hk => lt_of_lt_of_le (hwin k (le_trans hk h1k)) (min_le_left _ _))
        (lt_of_lt_of_le hψ1 (min_le_left _ _)) nn hnn
    · intro nn hnn
      have hb := hfwd₂ (mirrorChain q) (isChain_mirrorChain hqc)
        (fun k hk => ?_)
        (by rw [mirrorChain_psi1, mirrorChain_psi1]
            exact lt_of_lt_of_le hψ2 (min_le_right _ _)) nn hnn
      · rw [mirrorChain_fst, mirrorChain_psi1] at hb
        have h3 := congrArg eqMirror hb
        simpa [ugermC, eqMirror, eqMirror_eqMirror] using h3
      · rw [mirrorChain_fst, mirrorChain_fst, eqMirror_sub, norm_eqMirror]
        exact lt_of_lt_of_le (hwin (-k) (by rw [abs_neg]; exact le_trans hk h2k))
          (min_le_right _ _)

end

end Work.EQ
