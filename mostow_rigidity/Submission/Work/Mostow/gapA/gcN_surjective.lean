import Mathlib
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.axisNormDefs
import Submission.Work.Mostow.poAux

/-!
# Surjectivity of the normal-component map `gcN`

`gcN a b u` is the component of the hyperboloid lift `hlift u` orthogonal (in the Minkowski
form) to the plane spanned by the two null vectors `nvec a`, `nvec b`; it lies in the
positive definite plane `NormSub a b`.  Here we prove that `gcN a b : E 3 → NormSub a b` is
surjective.

The proof is elementary: given `Z ∈ NormSub a b` with `mink Z Z ≥ 0`, the affine 3-plane
`Z + span (nvec a, nvec b)` meets the hyperboloid: writing `p • nvec a + q • nvec b + Z` with
`p * q = (1 + mink Z Z) / (4 * gcL a b)` makes the Minkowski square equal to `-1`
(because `mink (nvec a) (nvec b) = inner a b - 1 = - 2 * gcL a b` and `Z ⊥ nvec a, nvec b`).
Choosing `p` large makes the time coordinate positive, so the point is on the upper sheet and
is the lift of a unique point `u ∈ E 3`; the decomposition is then canonical, giving
`gcN a b u = Z`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open _root_.Matrix

noncomputable section

variable {a b : E 3}

/-- For `c > 0` and any real `T` there are `p > 0` and `q` with `p * q = c` and `T < p + q`:
take `p` large and `q = c / p`. -/
lemma gcN_surj_exists_mul (c T : ℝ) (hc : 0 < c) :
    ∃ p q : ℝ, 0 < p ∧ p * q = c ∧ T < p + q := by
  have hm : 0 < max 1 (T + 1) := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨max 1 (T + 1), c / max 1 (T + 1), hm, ?_, ?_⟩
  · rw [mul_comm]
    exact div_mul_cancel₀ c (ne_of_gt hm)
  · have hA : T + 1 ≤ max 1 (T + 1) := le_max_right _ _
    have hB : 0 < c / max 1 (T + 1) := div_pos hc hm
    linarith

/-- The Minkowski square of `p • nvec a + q • nvec b + Z` for `Z ⊥ nvec a, nvec b`. -/
lemma gcN_surj_mink_x_x (p q : ℝ) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3)
    {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZa : mink Z (nvec a) = 0) (hZb : mink Z (nvec b) = 0) :
    mink (p • nvec a + q • nvec b + Z) (p • nvec a + q • nvec b + Z)
      = 2 * (p * q) * (inner ℝ a b - 1) + mink Z Z := by
  have hZa' : mink (nvec a) Z = 0 := by rw [minkSeg_comm]; exact hZa
  have hZb' : mink (nvec b) Z = 0 := by rw [minkSeg_comm]; exact hZb
  simp only [minkSeg_add_left, minkSeg_add_right, mink_smul_left'', mink_smul_right'',
    hZa, hZb, hZa', hZb', mink_nvec_self' ha, mink_nvec_self' hb,
    mink_nvec_nvec' a b, mink_nvec_nvec' b a, real_inner_comm b a]
  ring

/-- The Minkowski pairing of `nvec b` with `p • nvec a + q • nvec b + Z`. -/
lemma gcN_surj_mink_b_x (p q : ℝ) (hb : b ∈ Sph 3)
    {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZb : mink Z (nvec b) = 0) :
    mink (nvec b) (p • nvec a + q • nvec b + Z)
      = p * (inner ℝ a b - 1) := by
  have hZb' : mink (nvec b) Z = 0 := by rw [minkSeg_comm]; exact hZb
  simp only [minkSeg_add_right, mink_smul_right'', hZb', mink_nvec_self' hb,
    mink_nvec_nvec' b a, real_inner_comm b a]
  ring

/-- The Minkowski pairing of `nvec a` with `p • nvec a + q • nvec b + Z`. -/
lemma gcN_surj_mink_a_x (p q : ℝ) (ha : a ∈ Sph 3)
    {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZa : mink Z (nvec a) = 0) :
    mink (nvec a) (p • nvec a + q • nvec b + Z)
      = q * (inner ℝ a b - 1) := by
  have hZa' : mink (nvec a) Z = 0 := by rw [minkSeg_comm]; exact hZa
  simp only [minkSeg_add_right, mink_smul_right'', hZa', mink_nvec_self' ha,
    mink_nvec_nvec' a b]
  ring

theorem gcN_surjective (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3)
    (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b) :
    ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ Work.Mostow.gapA.NormSub a b →
      ∃ u : Submission.Mostow.E 3, Work.Mostow.gapA.gcN a b u = Z := by
  intro Z hZ
  have hL : 0 < gcL a b := gcL_pos a b ha hb hab
  have hZZ : 0 ≤ mink Z Z := mink_nonneg_of_mem_NormSub ha hZ
  obtain ⟨hZa, hZb⟩ := (mem_NormSub).mp hZ
  set c : ℝ := (1 + mink Z Z) / (4 * gcL a b) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]; exact div_pos (by linarith) (by linarith)
  obtain ⟨p, q, hppos, hpq, hpqT⟩ := gcN_surj_exists_mul c (-(Z (Sum.inr 0))) hcpos
  set x : Fin 3 ⊕ Fin 1 → ℝ := p • nvec a + q • nvec b + Z with hxdef
  have h4 : 4 * c * gcL a b = 1 + mink Z Z := by
    rw [hcdef]; field_simp
  have hx1 : mink x x = -1 := by
    rw [hxdef, gcN_surj_mink_x_x p q ha hb hZa hZb]
    have h2 := two_gcL a b
    nlinarith [h4, hpq, h2]
  have hxtime : 0 < x (Sum.inr 0) := by
    rw [hxdef]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nvec, Sum.elim_inr]
    linarith [hpqT]
  set u : Submission.Mostow.E 3 := WithLp.toLp 2 (fun i : Fin 3 => x (Sum.inl i)) with hudef
  have hliftu : hlift u = x := by
    rw [hudef]
    exact (eq_hlift_of_upper x (by rw [← mink_eq_mform]; exact hx1) hxtime).symm
  refine ⟨u, ?_⟩
  have hbx : mink (nvec b) x = -2 * p * gcL a b := by
    rw [hxdef, gcN_surj_mink_b_x p q hb hZb]
    have h2 := two_gcL a b
    nlinarith [h2]
  have hav : lev b u = 2 * p * gcL a b := by
    rw [lev_eq_neg_mink, hliftu, hbx]; ring
  have hax : mink (nvec a) x = -2 * q * gcL a b := by
    rw [hxdef, gcN_surj_mink_a_x p q ha hZa]
    have h2 := two_gcL a b
    nlinarith [h2]
  have hbv : lev a u = 2 * q * gcL a b := by
    rw [lev_eq_neg_mink, hliftu, hax]; ring
  have hne : (2 : ℝ) * gcL a b ≠ 0 := by linarith
  have hA : gcA a b u = p := by
    have h := gcA_mul a b ha hb hab u
    have h2 : gcA a b u * (2 * gcL a b) = p * (2 * gcL a b) := by rw [h, hav]; ring
    exact mul_right_cancel₀ hne h2
  have hB : gcB a b u = q := by
    have h := gcB_mul a b ha hb hab u
    have h2 : gcB a b u * (2 * gcL a b) = q * (2 * gcL a b) := by rw [h, hbv]; ring
    exact mul_right_cancel₀ hne h2
  rw [show gcN a b u = hlift u - gcA a b u • nvec a - gcB a b u • nvec b from rfl,
    hliftu, hA, hB, hxdef]
  abel

end

end Work.Mostow.gapA
