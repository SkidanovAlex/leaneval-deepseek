import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.perron_vector_of_nonneg_symm_card_pos_le_one_nonzero
import Submission.Commons.LinearAlgebra.Matrix.posDef_perron_decomp
import Submission.Commons.LinearAlgebra.Matrix.rankOne_sub_posDef_strict

noncomputable section
open Matrix Polynomial Set Topology Filter
open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix

def seq_t (k : ℕ) : ℝ := (1 : ℝ) / (k + 2 : ℝ)

lemma seq_t_pos (k : ℕ) : 0 < seq_t k := by
  unfold seq_t
  positivity

lemma seq_t_lt_one (k : ℕ) : seq_t k < 1 := by
  unfold seq_t
  have h : (1 : ℝ) < (k : ℝ) + 2 := by
    have : (0:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.zero_le k
    linarith
  exact (div_lt_one (by positivity : 0 < (k:ℝ)+2)).mpr h

lemma tendsto_seq_t : Tendsto seq_t atTop (𝓝 0) := by
  unfold seq_t
  have hmain : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop := by
    simpa [add_comm] using
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hdiv : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hmain
  simpa using hdiv

-- zero approximation and its strictness
def zeroApprox (n : ℕ) (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (seq_t k) • Matrix.vecMulVec (fun _ : Fin n => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))
    - (seq_t k)^3 • (1 : Matrix (Fin n) (Fin n) ℝ)

lemma zeroApprox_apply {n : ℕ} (k : ℕ) (i j : Fin n) :
    zeroApprox n k i j = (if i = j then seq_t k - (seq_t k)^3 else seq_t k) := by
  classical
  unfold zeroApprox
  by_cases h : i = j
  · simp [Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, h]
  · simp [Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, h]

lemma zeroApprox_pos_entries {n : ℕ} (k : ℕ) :
    ∀ i j : Fin n, 0 < zeroApprox n k i j := by
  classical
  intro i j
  by_cases h : i = j
  · simp [zeroApprox_apply, h]
    have ht1 : seq_t k < 1 := seq_t_lt_one k
    have ht0 : 0 < seq_t k := seq_t_pos k
    nlinarith [sq_nonneg (seq_t k)]
  · simp [zeroApprox_apply, h, seq_t_pos]

lemma zeroApprox_trace_pos {n : ℕ} (hn : 0 < n) (k : ℕ) :
    0 < (zeroApprox n k).trace := by
  classical
  rw [Matrix.trace]
  have hdiag : ∀ i : Fin n, 0 < zeroApprox n k i i := fun i => zeroApprox_pos_entries (n := n) k i i
  haveI : Nonempty (Fin n) := by
    exact Fin.pos_iff_nonempty.mp hn
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
    classical
    exact Finset.univ_nonempty
  exact Finset.sum_pos (fun i hi => hdiag i) hnonempty

lemma zeroApprox_strict {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (zeroApprox n k).IsSymm ∧ IsUnit (zeroApprox n k) ∧
      ((zeroApprox n k).charpoly.roots.filter (fun r => 0 < r)).card = 1 := by
  classical
  let E : Matrix (Fin n) (Fin n) ℝ := (seq_t k)^3 • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hE : E.PosDef := by
    dsimp [E]
    exact Matrix.PosDef.one.smul (pow_pos (seq_t_pos k) 3)
  have hc : 0 < seq_t k := seq_t_pos k
  have hTrace : 0 < ((seq_t k) • Matrix.vecMulVec (fun _ : Fin n => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ)) - E).trace := by
    dsimp [E]
    -- should match zeroApprox trace
    simpa [zeroApprox, Matrix.trace, Matrix.vecMulVec_apply, Matrix.one_apply] using zeroApprox_trace_pos hn k
  have h := rankOne_sub_posDef_strict (n := n) hn E hE (fun _ : Fin n => (1 : ℝ)) (seq_t k) hc hTrace
  simpa [zeroApprox, E] using h

-- Nonzero approximation
def approxW {n : ℕ} (u : Fin n → ℝ) (k : ℕ) : Fin n → ℝ := fun i => u i + seq_t k

def approxE {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (lam : ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (lam • Matrix.vecMulVec u u - A) + (seq_t k)^3 • (1 : Matrix (Fin n) (Fin n) ℝ)

def approxB {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (lam : ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (lam + seq_t k) • Matrix.vecMulVec (approxW u k) (approxW u k) - approxE A u lam k

lemma approxB_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (lam : ℝ)
    (k : ℕ) (i j : Fin n) :
    approxB A u lam k i j =
      A i j + ((lam + seq_t k) * ((u i + seq_t k) * (u j + seq_t k)) - lam * (u i * u j))
        - (if i = j then (seq_t k)^3 else 0) := by
  classical
  unfold approxB approxE approxW
  simp [Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply]
  ring

lemma approxB_pos_entries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ)
    (lam : ℝ) (k : ℕ)
    (hnn : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hlam : 0 < lam) :
    ∀ i j : Fin n, 0 < approxB A u lam k i j := by
  classical
  intro i j
  by_cases h : i = j
  · subst j
    rw [approxB_apply, if_pos rfl]
    have hdiff : 0 < (lam + seq_t k) * ((u i + seq_t k) * (u i + seq_t k)) - lam * (u i * u i) - (seq_t k)^3 := by
      have ht : 0 < seq_t k := seq_t_pos k
      have hui : 0 ≤ u i := hu i
      have h1 : 0 < lam * (seq_t k * seq_t k) := mul_pos hlam (mul_pos ht ht)
      have h2 : 0 ≤ lam * (u i * seq_t k) := mul_nonneg hlam.le (mul_nonneg hui ht.le)
      have h3 : 0 ≤ seq_t k * (u i * u i) := mul_nonneg ht.le (mul_self_nonneg (u i))
      have h4 : 0 ≤ seq_t k * seq_t k * u i := mul_nonneg (mul_nonneg ht.le ht.le) hui
      nlinarith
    have hAii : 0 ≤ A i i := hnn i i
    have hsum : A i i + ((lam + seq_t k) * ((u i + seq_t k) * (u i + seq_t k)) - lam * (u i * u i)) - (seq_t k)^3 =
        A i i + (((lam + seq_t k) * ((u i + seq_t k) * (u i + seq_t k)) - lam * (u i * u i)) - (seq_t k)^3) := by ring
    rw [hsum]
    exact add_pos_of_nonneg_of_pos hAii hdiff
  · rw [approxB_apply, if_neg h]
    have hdiff : 0 < (lam + seq_t k) * ((u i + seq_t k) * (u j + seq_t k)) - lam * (u i * u j) := by
      have ht : 0 < seq_t k := seq_t_pos k
      have hui : 0 ≤ u i := hu i
      have huj : 0 ≤ u j := hu j
      have h1 : 0 < lam * (seq_t k * seq_t k) := mul_pos hlam (mul_pos ht ht)
      have h2 : 0 ≤ lam * (u i * seq_t k) := mul_nonneg hlam.le (mul_nonneg hui ht.le)
      have h3 : 0 ≤ lam * (u j * seq_t k) := mul_nonneg hlam.le (mul_nonneg huj ht.le)
      have h4 : 0 ≤ seq_t k * ((u i + seq_t k) * (u j + seq_t k)) :=
        mul_nonneg ht.le (mul_nonneg (add_nonneg hui ht.le) (add_nonneg huj ht.le))
      nlinarith
    have hAij : 0 ≤ A i j := hnn i j
    have hsum : A i j + ((lam + seq_t k) * ((u i + seq_t k) * (u j + seq_t k)) - lam * (u i * u j)) - 0 =
        A i j + (((lam + seq_t k) * ((u i + seq_t k) * (u j + seq_t k)) - lam * (u i * u j))) := by ring
    rw [hsum]
    simpa using add_pos_of_nonneg_of_pos hAij hdiff

lemma approxB_trace_pos {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ)
    (lam : ℝ) (k : ℕ)
    (hnn : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hlam : 0 < lam) :
    0 < (approxB A u lam k).trace := by
  classical
  rw [Matrix.trace]
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hdiag : ∀ i : Fin n, 0 < approxB A u lam k i i := fun i => approxB_pos_entries A u lam k hnn hu hlam i i
  exact Finset.sum_pos (fun i hi => hdiag i) Finset.univ_nonempty

lemma approxB_strict {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (u : Fin n → ℝ) (lam : ℝ) (k : ℕ)
    (hnn : ∀ i j, 0 ≤ A i j) (hu : ∀ i, 0 ≤ u i) (hlam : 0 < lam)
    (hu_norm : (∑ i : Fin n, u i * u i) = 1)
    (hu_eigen : A.mulVec u = lam • u)
    (hquad : ∀ x : Fin n → ℝ, (∑ i : Fin n, u i * x i) = 0 →
      (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j) ≤ 0) :
    (approxB A u lam k).IsSymm ∧ IsUnit (approxB A u lam k) ∧
      ((approxB A u lam k).charpoly.roots.filter (fun r => 0 < r)).card = 1 := by
  classical
  let E : Matrix (Fin n) (Fin n) ℝ := approxE A u lam k
  have hE : E.PosDef := by
    dsimp [E, approxE]
    exact posDef_perron_decomp hn A hA u lam ((seq_t k)^3) hlam hu_norm hu_eigen hquad
      (pow_pos (seq_t_pos k) 3)
  have hc : 0 < lam + seq_t k := add_pos hlam (seq_t_pos k)
  have hTrace : 0 < ((lam + seq_t k) • Matrix.vecMulVec (approxW u k) (approxW u k) - E).trace := by
    dsimp [E]
    simpa [approxB, approxE, approxW] using approxB_trace_pos hn A u lam k hnn hu hlam
  have h := rankOne_sub_posDef_strict (n := n) hn E hE (approxW u k) (lam + seq_t k) hc hTrace
  simpa [approxB, E] using h

lemma zeroApprox_tendsto {n : ℕ} :
    Tendsto (fun k : ℕ => zeroApprox n k) atTop (𝓝 0) := by
  classical
  change Tendsto (fun k : ℕ => (fun i : Fin n => fun j : Fin n => zeroApprox n k i j)) atTop
    (𝓝 (fun i : Fin n => fun j : Fin n => (0 : ℝ)))
  apply (tendsto_pi_nhds).2
  intro i
  apply (tendsto_pi_nhds).2
  intro j
  by_cases h : i = j
  · have hlim : Tendsto (fun k : ℕ => seq_t k - (seq_t k)^3) atTop (𝓝 0) := by
      simpa using tendsto_seq_t.sub (tendsto_seq_t.pow 3)
    have hEq : ∀ k : ℕ, zeroApprox n k i j = seq_t k - (seq_t k)^3 := by
      intro k
      simp [zeroApprox_apply, h]
    simpa [hEq] using hlim
  · have hlim : Tendsto seq_t atTop (𝓝 0) := tendsto_seq_t
    have hEq : ∀ k : ℕ, zeroApprox n k i j = seq_t k := by
      intro k
      simp [zeroApprox_apply, h]
    simpa [hEq] using hlim

lemma approxB_tendsto {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (lam : ℝ) :
    Tendsto (fun k : ℕ => approxB A u lam k) atTop (𝓝 A) := by
  classical
  change Tendsto (fun k : ℕ => (fun i : Fin n => fun j : Fin n => approxB A u lam k i j)) atTop
    (𝓝 (fun i : Fin n => fun j : Fin n => A i j))
  apply (tendsto_pi_nhds).2
  intro i
  apply (tendsto_pi_nhds).2
  intro j
  have hdiff : Tendsto (fun k : ℕ => (lam + seq_t k) * ((u i + seq_t k) * (u j + seq_t k)) - lam * (u i * u j)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => lam + seq_t k) atTop (𝓝 lam) := by
      simpa using tendsto_const_nhds.add tendsto_seq_t
    have h2u : Tendsto (fun k : ℕ => u i + seq_t k) atTop (𝓝 (u i)) := by
      simpa using tendsto_const_nhds.add tendsto_seq_t
    have h2v : Tendsto (fun k : ℕ => u j + seq_t k) atTop (𝓝 (u j)) := by
      simpa using tendsto_const_nhds.add tendsto_seq_t
    have h3 : Tendsto (fun k : ℕ => (u i + seq_t k) * (u j + seq_t k)) atTop (𝓝 (u i * u j)) := h2u.mul h2v
    have h4 : Tendsto (fun k : ℕ => (lam + seq_t k) * ((u i + seq_t k) * (u j + seq_t k))) atTop (𝓝 (lam * (u i * u j))) := h1.mul h3
    have h5 : Tendsto (fun k : ℕ => (lam + seq_t k) * ((u i + seq_t k) * (u j + seq_t k)) - lam * (u i * u j)) atTop (𝓝 (lam * (u i * u j) - lam * (u i * u j))) := h4.sub tendsto_const_nhds
    simpa using h5
  by_cases h : i = j
  · subst j
    have hlim : Tendsto (fun k : ℕ => A i i + ((lam + seq_t k) * ((u i + seq_t k) * (u i + seq_t k)) - lam * (u i * u i)) - (seq_t k)^3) atTop (𝓝 (A i i)) := by
      have hdiff_i : Tendsto (fun k : ℕ => (lam + seq_t k) * ((u i + seq_t k) * (u i + seq_t k)) - lam * (u i * u i)) atTop (𝓝 0) := by
        simpa using hdiff
      have hmain : Tendsto (fun k : ℕ => A i i + ((lam + seq_t k) * ((u i + seq_t k) * (u i + seq_t k)) - lam * (u i * u i)) - (seq_t k)^3) atTop (𝓝 (A i i)) := by
        simpa using (tendsto_const_nhds.add hdiff_i).sub (tendsto_seq_t.pow 3)
      simpa using hmain
    have hEq : ∀ k : ℕ, approxB A u lam k i i = A i i + ((lam + seq_t k) * ((u i + seq_t k) * (u i + seq_t k)) - lam * (u i * u i)) - (seq_t k)^3 := by
      intro k
      simp [approxB_apply]
    simpa [hEq] using hlim
  · have hlim : Tendsto (fun k : ℕ => A i j + ((lam + seq_t k) * ((u i + seq_t k) * (u j + seq_t k)) - lam * (u i * u j))) atTop (𝓝 (A i j)) := by
      simpa using tendsto_const_nhds.add hdiff
    have hEq : ∀ k : ℕ, approxB A u lam k i j = A i j + ((lam + seq_t k) * ((u i + seq_t k) * (u j + seq_t k)) - lam * (u i * u j)) := by
      intro k
      simp [approxB_apply, h]
    simpa [hEq] using hlim

theorem strict_lorentzian_quadratic_dense_pos {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hcard : (A.charpoly.roots.filter (fun r => 0 < r)).card ≤ 1) :
    ∃ f : ℕ → Matrix (Fin n) (Fin n) ℝ,
      (∀ k, f k ∈ {B : Matrix (Fin n) (Fin n) ℝ |
        B.IsSymm ∧ (∀ i j, 0 < B i j) ∧ IsUnit B ∧
          (B.charpoly.roots.filter (fun r => 0 < r)).card = 1}) ∧
      Tendsto f atTop (𝓝 A) := by
  classical
  by_cases hA0 : A = 0
  · refine ⟨fun k => zeroApprox n k, ?_, ?_⟩
    · intro k
      have hstrict := zeroApprox_strict hn k
      have hpos : ∀ i j, 0 < zeroApprox n k i j := zeroApprox_pos_entries (n := n) k
      exact ⟨hstrict.1, hpos, hstrict.2.1, hstrict.2.2⟩
    · simpa [hA0] using zeroApprox_tendsto (n := n)
  · obtain ⟨u, lam, hlam, hu_nonneg, hu_norm, hu_eigen, hquad⟩ :=
      perron_vector_of_nonneg_symm_card_pos_le_one_nonzero hn A hA hnn hcard hA0
    refine ⟨fun k => approxB A u lam k, ?_, ?_⟩
    · intro k
      have hstrict := approxB_strict hn A hA u lam k hnn hu_nonneg hlam hu_norm hu_eigen hquad
      have hpos : ∀ i j, 0 < approxB A u lam k i j := approxB_pos_entries A u lam k hnn hu_nonneg hlam
      exact ⟨hstrict.1, hpos, hstrict.2.1, hstrict.2.2⟩
    · exact approxB_tendsto A u lam

end Commons.LinearAlgebra.Matrix
