/-
# A symmetric clamped inverse

`Work.Diff.STE.B3.clampedInv_exists` constructs, for every pair `0 < a ≤ b` and every bound `B ≥ 0`,
a smooth "clamped inverse" `K₀` on the space of symmetric matrices: it agrees with the genuine
inverse on the Loewner window `a I ≤ G ≤ b I`, is elliptic, and its jets on `{|G i j| ≤ B}` are
bounded by `CK₀` — all *uniformly* in `G`, which is what makes the uniform Gårding coefficient of
the DeTurck operator available.

The one property of `K₀` that is not directly exported by `clampedInv_exists` is symmetry *without*
an ellipticity hypothesis: the exported symmetry clause demands `a I ≤ G`.  Most callers only ever
feed symmetric matrices with a (non-uniform) ellipticity bound, but the localisation argument needs
symmetry for the products `θ · Gf` with a *cut-off* `θ`, where the lower bound may degenerate.

This file removes the hypothesis by **symmetrising**: `K G i j = (K₀ G i j + K₀ G j i)/2`.  Every
property is preserved:

* smoothness — a sum of two smooth functions;
* exactness on the window — `M⁻¹` of a symmetric matrix is symmetric
  (`Matrix.transpose_nonsing_inv`), so the average is `M⁻¹`;
* ellipticity — the antisymmetric part contributes `0` to the quadratic form (`symm_quad` below);
* symmetry — tautologically;
* the jet bound — a factor `2`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.clampedInv_exists

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix
open Matrix

namespace Work.Diff.STE.Lead.Gal

/-- **The quadratic form only sees the symmetric part**: averaging a matrix with its transpose does
not change `ξ ↦ ∑ p, ∑ q, M p q * ξ p * ξ q`. -/
lemma symm_quad (n : ℕ) (M : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    (∑ p, ∑ q, ((M p q + M q p) / 2) * ξ p * ξ q)
      = ∑ p, ∑ q, M p q * ξ p * ξ q := by
  have hp : ∀ p q : Fin n, ((M p q + M q p) / 2) * ξ p * ξ q
      = (M p q * ξ p * ξ q + M q p * ξ p * ξ q) / 2 := by
    intro p q; ring
  have hswap : (∑ p, ∑ q, M q p * ξ p * ξ q) = ∑ p, ∑ q, M p q * ξ p * ξ q := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => by ring))
  have hhalf : (∑ p, ∑ q, ((M p q + M q p) / 2) * ξ p * ξ q)
      = ((∑ p, ∑ q, M p q * ξ p * ξ q) + (∑ p, ∑ q, M q p * ξ p * ξ q)) / 2 := by
    simp only [hp, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hhalf, hswap]
  ring

/-- **The symmetric clamped inverse.**  As `Work.Diff.STE.B3.clampedInv_exists`, but the symmetry
clause holds for every symmetric matrix (no ellipticity hypothesis), at the price of a factor `2`
in the jet constant. -/
theorem clampedInv_sym_gal (n k : ℕ) (a b B : ℝ) (ha : 0 < a) (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ (K : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ)) (lam' CK : ℝ),
      0 < lam' ∧ 0 ≤ CK ∧
      (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun G : Fin n → Fin n → ℝ => K G i j)) ∧
      (∀ (G : Fin n → Fin n → ℝ),
        (∀ i j, G i j = G j i) →
        (∀ ξ : Fin n → ℝ, a * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, G i j * ξ i * ξ j) →
        (∀ ξ : Fin n → ℝ, ∑ i, ∑ j, G i j * ξ i * ξ j ≤ b * ∑ i, (ξ i) ^ 2) →
        K G = fun i j => (Matrix.of G)⁻¹ i j) ∧
      (∀ (G : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ),
        lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, K G i j * ξ i * ξ j) ∧
      (∀ (G : Fin n → Fin n → ℝ),
        (∀ i j, G i j = G j i) → (∀ i j, K G i j = K G j i)) ∧
      (∀ (G : Fin n → Fin n → ℝ), (∀ i j, |G i j| ≤ B) →
        ∀ (j : ℕ), j ≤ k → ∀ (p q : Fin n),
          ‖iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K G' p q) G‖ ≤ CK) := by
  classical
  obtain ⟨K0, lam', CK0, hlam', hCK0nn, hsm0, hex0, hell0, hsym0, hjet0⟩ :=
    Work.Diff.STE.B3.clampedInv_exists n k a b B ha hb hB
  have hsm : ∀ i j, ContDiff ℝ (⊤ : ℕ∞)
      (fun G : Fin n → Fin n → ℝ => (K0 G i j + K0 G j i) / 2) := by
    intro i j
    have h1 := (hsm0 i j).add (hsm0 j i)
    simpa using h1.div_const (2 : ℝ)
  have hex : ∀ (G : Fin n → Fin n → ℝ),
      (∀ i j, G i j = G j i) →
      (∀ ξ : Fin n → ℝ, a * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, G i j * ξ i * ξ j) →
      (∀ ξ : Fin n → ℝ, ∑ i, ∑ j, G i j * ξ i * ξ j ≤ b * ∑ i, (ξ i) ^ 2) →
      (fun i j : Fin n => (K0 G i j + K0 G j i) / 2) = fun i j => (Matrix.of G)⁻¹ i j := by
    intro G hGsym hlow hup
    have hK := hex0 G hGsym hlow hup
    funext i j
    have hji : (Matrix.of G)⁻¹ j i = (Matrix.of G)⁻¹ i j := by
      have h2 : (Matrix.of G)⁻¹ᵀ = (Matrix.of G)⁻¹ := by
        rw [Matrix.transpose_nonsing_inv]
        congr 1
        ext p q
        simpa [Matrix.transpose_apply] using (hGsym p q).symm
      have h3 := congrFun (congrFun h2 i) j
      simpa [Matrix.transpose_apply] using h3
    simp only [hK]
    rw [hji]
    ring
  have hell : ∀ (G : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ),
      lam' * ∑ i, (ξ i) ^ 2
        ≤ ∑ i, ∑ j, ((K0 G i j + K0 G j i) / 2) * ξ i * ξ j := by
    intro G ξ
    rw [symm_quad n (K0 G) ξ]
    exact hell0 G ξ
  have hsym : ∀ (G : Fin n → Fin n → ℝ), (∀ i j, G i j = G j i) →
      ∀ i j, (K0 G i j + K0 G j i) / 2 = (K0 G j i + K0 G i j) / 2 := by
    intro G _ i j
    ring
  have hjet : ∀ (G : Fin n → Fin n → ℝ), (∀ i j, |G i j| ≤ B) →
      ∀ (j : ℕ), j ≤ k → ∀ (p q : Fin n),
        ‖iteratedFDeriv ℝ j
          (fun G' : Fin n → Fin n → ℝ => (K0 G' p q + K0 G' q p) / 2) G‖ ≤ 2 * CK0 := by
    intro G hG j hj p q
    have h0a := hjet0 G hG j hj p q
    have h0b := hjet0 G hG j hj q p
    have ha : ContDiffAt ℝ j (fun G' : Fin n → Fin n → ℝ => K0 G' p q) G :=
      (hsm0 p q).contDiffAt.of_le
        (WithTop.coe_le_coe.mpr (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤))
    have hb : ContDiffAt ℝ j (fun G' : Fin n → Fin n → ℝ => K0 G' q p) G :=
      (hsm0 q p).contDiffAt.of_le
        (WithTop.coe_le_coe.mpr (le_top : ((j : ℕ) : ℕ∞) ≤ ⊤))
    have hsum : iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K0 G' p q + K0 G' q p) G
        = iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K0 G' p q) G
          + iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K0 G' q p) G :=
      iteratedFDeriv_add_apply ha hb
    have hcsm : ContDiffAt ℝ j
        (fun G' : Fin n → Fin n → ℝ => K0 G' p q + K0 G' q p) G := ha.add hb
    have hsplit : (fun G' : Fin n → Fin n → ℝ => (K0 G' p q + K0 G' q p) / 2)
        = fun G' => (1 / 2 : ℝ) • (K0 G' p q + K0 G' q p) := by
      funext G'
      rw [smul_eq_mul]
      ring
    have hnorm : ‖iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K0 G' p q) G
          + iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K0 G' q p) G‖ ≤ CK0 + CK0 :=
      (norm_add_le _ _).trans (add_le_add h0a h0b)
    rw [hsplit, iteratedFDeriv_const_smul_apply' (i := j) hcsm, hsum]
    calc ‖(1 / 2 : ℝ) • (iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K0 G' p q) G
            + iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K0 G' q p) G)‖
        = (1 / 2 : ℝ) * ‖iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K0 G' p q) G
            + iteratedFDeriv ℝ j (fun G' : Fin n → Fin n → ℝ => K0 G' q p) G‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      _ ≤ (1 / 2 : ℝ) * (CK0 + CK0) :=
          mul_le_mul_of_nonneg_left hnorm (by norm_num)
      _ = CK0 := by ring
      _ ≤ 2 * CK0 := by linarith [hCK0nn]
  exact ⟨fun G i j => (K0 G i j + K0 G j i) / 2, lam', 2 * CK0, hlam', by positivity,
    hsm, hex, hell, hsym, hjet⟩

end Work.Diff.STE.Lead.Gal
