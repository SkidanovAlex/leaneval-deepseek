import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.Defs
import Submission.Work.HP.EulerGrad.euler_grad
import Submission.Work.HP.evaldefs
import Submission.Work.HP.veronese_first
import Submission.Work.HP.rNorm_smul
import Submission.Work.HP.BoundaryMain.Utils

set_option autoImplicit false

noncomputable section

namespace Work.HP.BoundaryMain

open Work.HP

/-- `formEvalR` is additive in the coefficient vector. -/
lemma formEvalR_add_coeff (d n : ℕ) (c c' : Mon d n → ℝ) (y : Fin (n + 1) → ℝ) :
    formEvalR d n c' y = formEvalR d n c y + formEvalR d n (c' - c) y := by
  simp only [formEvalR, Pi.sub_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by ring)

/-- **The last soluble point on the segment.** Let the set of parameters
`S := {t ∈ [0,1] | IPt d n (toR a + t • (b - toR a))}` be the set of points of the segment
from the soluble form `toR a` to the non-soluble form `b` at which the form still has a zero on
the Euclidean unit sphere. This set is closed (hypothesis `hclose`), contains `0` and does not
contain `1`; hence it has a greatest element `t`, which is `< 1`, and every `s ∈ [0,1]` with
`s > t` is non-soluble. -/
theorem exists_crossing (d n : ℕ)
    (hclose : IsClosed {a : Mon d n → ℝ | IPt d n a})
    (a : Mon d n → ℤ) (b : Mon d n → ℝ)
    (hIPt : IPt d n (toR a)) (hb' : ¬ IPt d n b) :
    ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧ t < 1 ∧
      IPt d n (toR a + t • (b - toR a)) ∧
      ∀ s ∈ Set.Icc 0 1, t < s → ¬ IPt d n (toR a + s • (b - toR a)) := by
  let S : Set ℝ := {t : ℝ | t ∈ Set.Icc 0 1 ∧ IPt d n (toR a + t • (b - toR a))}
  have hSval : S = {t : ℝ | t ∈ Set.Icc 0 1 ∧ IPt d n (toR a + t • (b - toR a))} := rfl
  have hcl : IsClosed S := by
    rw [hSval]
    exact isClosed_Icc.inter (isClosed_preimage_IPt_segment d n hclose a b)
  have hmem0 : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_refl 0, zero_le_one⟩, ?_⟩
    simpa using hIPt
  have hbdd : BddAbove S := ⟨1, fun t ht => ht.1.2⟩
  have hgreat : IsGreatest S (sSup S) := IsClosed.isGreatest_csSup hcl ⟨0, hmem0⟩ hbdd
  have hsup_mem : sSup S ∈ S := hgreat.1
  have hsup_max : ∀ s ∈ S, s ≤ sSup S := hgreat.2
  have hsup_le : sSup S ≤ 1 := hsup_mem.1.2
  have hsup_lt : sSup S < 1 := by
    refine lt_of_le_of_ne hsup_le ?_
    intro h1
    have h1mem : (1 : ℝ) ∈ S := h1 ▸ hsup_mem
    exact hb' (by simpa using h1mem.2)
  refine ⟨sSup S, ⟨hsup_mem.1.1, hsup_mem.1.2⟩, hsup_lt, hsup_mem.2, ?_⟩
  intro s hs hlt hcon
  exact absurd (hsup_max s ⟨hs, hcon⟩) (not_le.mpr hlt)

/-- **Real solubility is open at a non-degenerate zero.** If `x` is a unit vector with
`f_c(x) = 0` for the coefficient vector `c : Mon d n → ℝ`, and the gradient `∇f_c(x)` does
not vanish there, then every coefficient vector `c'` close enough to `c` has a zero on the
Euclidean unit sphere (`IPt d n c'`, i.e. `∃ x, rNorm x = 1 ∧ formEvalR d n c' x = 0`). -/
theorem IPt_openAt_nondegenerate (d n : ℕ) (Ctay Cval : ℝ)
    (htay : ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        |formEvalR d n a y - formEvalR d n a x - dotR (gradVec d n a x) (y - x)|
          ≤ Ctay * rNorm a * (rNorm (y - x)) ^ 2)
    (hval : ∀ (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ), rNorm x ≤ 2 →
        |formEvalR d n a x| ≤ Cval * rNorm a)
    (c : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) (hx : rNorm x = 1)
    (hfc : formEvalR d n c x = 0) (hg : gradVec d n c x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c' : Mon d n → ℝ, rNorm (c' - c) < ε → IPt d n c' := by
  have hvpos : 0 < rNorm (gradVec d n c x) :=
    lt_of_le_of_ne (rNorm_nonneg _) (fun h => hg (rNorm_eq_zero.mp h.symm))
  let v : Fin (n + 1) → ℝ := gradVec d n c x
  let A : ℝ := |Ctay| * (rNorm c + 1)
  let δ : ℝ := 1 / (2 * (A + 1) * (rNorm v + 1))
  let ε : ℝ := (δ * rNorm v ^ 2 / 2) / (|Cval| + 1)
  have hAval : A = |Ctay| * (rNorm c + 1) := rfl
  have hδval : δ = 1 / (2 * (A + 1) * (rNorm v + 1)) := rfl
  have hεval : ε = (δ * rNorm v ^ 2 / 2) / (|Cval| + 1) := rfl
  have hv0 : 0 < rNorm v := hvpos
  have hA0 : 0 ≤ A := by
    rw [hAval]
    exact mul_nonneg (abs_nonneg Ctay) (by linarith [rNorm_nonneg c])
  have hA1 : 0 < A + 1 := by linarith
  have hden : 0 < 2 * (A + 1) * (rNorm v + 1) := by
    have h2 : 0 < rNorm v + 1 := by linarith
    have h3 : 0 < (A + 1) * (rNorm v + 1) := mul_pos hA1 h2
    have h4 : 0 < 2 * ((A + 1) * (rNorm v + 1)) := by linarith
    simpa only [mul_assoc] using h4
  have hδpos : 0 < δ := by rw [hδval]; exact one_div_pos.mpr hden
  have hεpos : 0 < ε := by
    rw [hεval]
    exact div_pos (div_pos (mul_pos hδpos (pow_pos hv0 2)) two_pos)
      (by linarith [abs_nonneg Cval])
  refine ⟨ε, hεpos, ?_⟩
  intro c' hc'
  have hδr : δ * rNorm v ≤ 1 / 2 := by
    rw [hδval]
    have heq : 1 / (2 * (A + 1) * (rNorm v + 1)) * rNorm v
        = rNorm v / (2 * (A + 1) * (rNorm v + 1)) := by ring
    rw [heq, div_le_iff₀ hden]
    nlinarith [hA0, hv0, mul_nonneg hA0 hv0.le]
  have hAδ : A * δ ≤ 1 / 2 := by
    rw [hδval]
    have heq : A * (1 / (2 * (A + 1) * (rNorm v + 1)))
        = A / (2 * (A + 1) * (rNorm v + 1)) := by ring
    rw [heq, div_le_iff₀ hden]
    nlinarith [hA0, hv0, mul_nonneg hA0 hv0.le]
  have hball : ∀ s : ℝ, |s| ≤ δ → rNorm (x + s • v) ≤ 2 := by
    intro s hs
    have h1 : rNorm (x + s • v) ≤ rNorm x + rNorm (s • v) := rNorm_add_le _ _
    rw [hx, rNorm_smul'] at h1
    have h2 : |s| * rNorm v ≤ δ * rNorm v := mul_le_mul_of_nonneg_right hs (rNorm_nonneg v)
    linarith
  have hTaylor : ∀ s : ℝ, |s| ≤ δ →
      |formEvalR d n c (x + s • v) - s * rNorm v ^ 2| ≤ A * s ^ 2 * rNorm v ^ 2 := by
    intro s hs
    have h2 : rNorm (x + s • v) ≤ 2 := hball s hs
    have h1 := htay c x (x + s • v) (by rw [hx]; norm_num) h2
    have hyx : (x + s • v) - x = s • v := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hdot : dotR (gradVec d n c x) (s • v) = s * rNorm v ^ 2 := by
      rw [dotR_smul_right, dotR_self_eq_rNorm_sq]
    rw [hyx, hdot, hfc, rNorm_smul'] at h1
    simp only [sub_zero] at h1
    refine h1.trans ?_
    have hcr : Ctay * rNorm c ≤ A := by
      rw [hAval]
      have ha1 : Ctay * rNorm c ≤ |Ctay| * rNorm c :=
        mul_le_mul_of_nonneg_right (le_abs_self Ctay) (rNorm_nonneg c)
      have ha2 : |Ctay| * rNorm c ≤ |Ctay| * (rNorm c + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg Ctay)
      linarith
    have hsq : (|s| * rNorm v) ^ 2 = s ^ 2 * rNorm v ^ 2 := by rw [mul_pow, sq_abs]
    rw [hsq]
    have hnn : (0 : ℝ) ≤ s ^ 2 * rNorm v ^ 2 := by positivity
    calc Ctay * rNorm c * (s ^ 2 * rNorm v ^ 2) ≤ A * (s ^ 2 * rNorm v ^ 2) :=
          mul_le_mul_of_nonneg_right hcr hnn
      _ = A * s ^ 2 * rNorm v ^ 2 := by ring
  have hValA : ∀ s : ℝ, |s| ≤ δ →
      |formEvalR d n (c' - c) (x + s • v)| ≤ |Cval| * rNorm (c' - c) := by
    intro s hs
    have h1 := hval (c' - c) (x + s • v) (hball s hs)
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self Cval) (rNorm_nonneg _))
  have hkey : ∀ s : ℝ, |s| ≤ δ →
      s * rNorm v ^ 2 - A * s ^ 2 * rNorm v ^ 2 - |Cval| * rNorm (c' - c)
        ≤ formEvalR d n c' (x + s • v) := by
    intro s hs
    have hT := hTaylor s hs
    have hV := hValA s hs
    have h1 : s * rNorm v ^ 2 - A * s ^ 2 * rNorm v ^ 2 ≤ formEvalR d n c (x + s • v) := by
      have h9 := (abs_le.mp hT).1
      linarith
    have h2 : -(|Cval| * rNorm (c' - c)) ≤ formEvalR d n (c' - c) (x + s • v) := by
      have h9 := (abs_le.mp hV).1
      linarith
    rw [formEvalR_add_coeff d n c c' (x + s • v)]
    linarith
  have hkey' : ∀ s : ℝ, |s| ≤ δ →
      formEvalR d n c' (x + s • v)
        ≤ s * rNorm v ^ 2 + A * s ^ 2 * rNorm v ^ 2 + |Cval| * rNorm (c' - c) := by
    intro s hs
    have hT := hTaylor s hs
    have hV := hValA s hs
    have h1 : formEvalR d n c (x + s • v) ≤ s * rNorm v ^ 2 + A * s ^ 2 * rNorm v ^ 2 := by
      have h9 := (abs_le.mp hT).2
      linarith
    have h2 : formEvalR d n (c' - c) (x + s • v) ≤ |Cval| * rNorm (c' - c) := (abs_le.mp hV).2
    rw [formEvalR_add_coeff d n c c' (x + s • v)]
    linarith
  have hAδ2 : A * δ ^ 2 * rNorm v ^ 2 ≤ δ * rNorm v ^ 2 / 2 := by
    have heq : A * δ ^ 2 * rNorm v ^ 2 = (A * δ) * (δ * rNorm v ^ 2) := by ring
    rw [heq]
    have hnn : 0 ≤ δ * rNorm v ^ 2 := mul_nonneg hδpos.le (sq_nonneg _)
    calc (A * δ) * (δ * rNorm v ^ 2) ≤ (1 / 2) * (δ * rNorm v ^ 2) :=
          mul_le_mul_of_nonneg_right hAδ hnn
      _ = δ * rNorm v ^ 2 / 2 := by ring
  have hcε : |Cval| * rNorm (c' - c) < δ * rNorm v ^ 2 / 2 := by
    have h1 : rNorm (c' - c) < ε := hc'
    have h2 : rNorm (c' - c) < (δ * rNorm v ^ 2 / 2) / (|Cval| + 1) := by
      rw [hεval] at h1
      exact h1
    have hle : |Cval| * rNorm (c' - c)
        ≤ |Cval| * ((δ * rNorm v ^ 2 / 2) / (|Cval| + 1)) :=
      mul_le_mul_of_nonneg_left h2.le (abs_nonneg Cval)
    have heq : |Cval| * ((δ * rNorm v ^ 2 / 2) / (|Cval| + 1))
        = (|Cval| / (|Cval| + 1)) * (δ * rNorm v ^ 2 / 2) := by ring
    have hX : 0 < δ * rNorm v ^ 2 / 2 := div_pos (mul_pos hδpos (pow_pos hv0 2)) two_pos
    have hq : |Cval| / (|Cval| + 1) < 1 := by
      rw [div_lt_one (by linarith [abs_nonneg Cval] : (0 : ℝ) < |Cval| + 1)]
      linarith [abs_nonneg Cval]
    have hlt : (|Cval| / (|Cval| + 1)) * (δ * rNorm v ^ 2 / 2) < δ * rNorm v ^ 2 / 2 := by
      calc (|Cval| / (|Cval| + 1)) * (δ * rNorm v ^ 2 / 2) < 1 * (δ * rNorm v ^ 2 / 2) :=
            mul_lt_mul_of_pos_right hq hX
        _ = δ * rNorm v ^ 2 / 2 := one_mul _
    rw [heq] at hle
    linarith
  have hδsmall : |δ| ≤ δ := le_of_eq (abs_of_pos hδpos)
  have hpos : 0 < formEvalR d n c' (x + δ • v) := by
    have hk := hkey δ hδsmall
    linarith
  have hneg : formEvalR d n c' (x + (-δ) • v) < 0 := by
    have hk := hkey' (-δ) (by rw [abs_neg]; exact hδsmall)
    have hAδ2' : A * (-δ) ^ 2 * rNorm v ^ 2 ≤ δ * rNorm v ^ 2 / 2 := by
      rw [show (-δ) ^ 2 = δ ^ 2 by ring]
      exact hAδ2
    linarith
  obtain ⟨s0, hs0, hs0eq⟩ : ∃ s0 : ℝ, s0 ∈ Set.Icc (-δ) δ ∧
      formEvalR d n c' (x + s0 • v) = 0 := by
    have hcont : ContinuousOn (fun s : ℝ => formEvalR d n c' (x + s • v)) (Set.Icc (-δ) δ) :=
      (continuous_formEvalR_along d n c' x v).continuousOn
    have hy : (0 : ℝ) ∈ Set.Icc (formEvalR d n c' (x + (-δ) • v))
        (formEvalR d n c' (x + δ • v)) := ⟨le_of_lt hneg, le_of_lt hpos⟩
    have hIVT := intermediate_value_Icc (show -δ ≤ δ by linarith) hcont hy
    obtain ⟨s0, hs0, hs0eq⟩ := hIVT
    exact ⟨s0, hs0, hs0eq⟩
  have hmem : |s0| ≤ δ := by
    rw [abs_le]
    exact ⟨by linarith [hs0.1], by linarith [hs0.2]⟩
  have hrny : 1 / 2 ≤ rNorm (x + s0 • v) := by
    have h3 : rNorm (s0 • v) ≤ δ * rNorm v := by
      rw [rNorm_smul']
      exact mul_le_mul_of_nonneg_right hmem (rNorm_nonneg v)
    have h4 : rNorm x ≤ rNorm (x + s0 • v) + rNorm (s0 • v) := by
      have h5 := rNorm_le_add_sub x (x + s0 • v)
      have h6 : x - (x + s0 • v) = -(s0 • v) := by abel
      rwa [h6, rNorm_neg] at h5
    linarith
  exact IPt_of_ne_zero d n (fun hzero => by
    have h0 : rNorm (x + s0 • v) = 0 := rNorm_eq_zero.mpr hzero
    linarith) hs0eq

/-- Boundary point: if `f_{toR a}` has a real zero on the unit sphere and `b` has no zero on the unit sphere and lies within distance `1` of `toR a`, then on the segment joining them there is a point `c`, still within distance `1` of `toR a`, which is real-soluble and has a critical zero (some unit vector `x` with `f_c x = 0` and `∇f_c x = 0`). -/
theorem exists_crit_zero (d n : ℕ)
    (hclose : IsClosed {a : Mon d n → ℝ | IPt d n a})
    (Ctay Cval : ℝ)
    (htay : ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        |formEvalR d n a y - formEvalR d n a x - dotR (gradVec d n a x) (y - x)|
          ≤ Ctay * rNorm a * (rNorm (y - x)) ^ 2)
    (hval : ∀ (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ), rNorm x ≤ 2 →
        |formEvalR d n a x| ≤ Cval * rNorm a)
    (a : Mon d n → ℤ) (b : Mon d n → ℝ)
    (hIPt : IPt d n (toR a)) (hb : rNorm (b - toR a) ≤ 1) (hb' : ¬ IPt d n b) :
    ∃ c : Mon d n → ℝ, rNorm (c - toR a) ≤ 1 ∧
      ∃ x : Fin (n + 1) → ℝ, rNorm x = 1 ∧ formEvalR d n c x = 0 ∧ gradVec d n c x = 0 := by
  obtain ⟨t, ht01, ht1, htIPt, hmax⟩ := exists_crossing d n hclose a b hIPt hb'
  let cstar : Mon d n → ℝ := toR a + t • (b - toR a)
  have hcstarval : cstar = toR a + t • (b - toR a) := rfl
  obtain ⟨x, hx1, hx0⟩ := htIPt
  have hx0' : formEvalR d n cstar x = 0 := hx0
  refine ⟨cstar, ?_, x, hx1, hx0', ?_⟩
  · rw [hcstarval, rNorm_segment_sub]
    calc |t| * rNorm (b - toR a) = t * rNorm (b - toR a) := by rw [abs_of_nonneg ht01.1]
      _ ≤ 1 * rNorm (b - toR a) := mul_le_mul_of_nonneg_right ht01.2 (rNorm_nonneg _)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = 1 := one_mul 1
  · by_contra hg
    obtain ⟨eps, heps, hneigh⟩ :=
      IPt_openAt_nondegenerate d n Ctay Cval htay hval cstar x hx1 hx0' hg
    let W : ℝ := rNorm (b - toR a)
    have hWval : W = rNorm (b - toR a) := rfl
    have hWpos : 0 < W := by
      rw [hWval]
      refine lt_of_le_of_ne (rNorm_nonneg _) (fun h => hb' ?_)
      have hb_eq : b = toR a := sub_eq_zero.mp (rNorm_eq_zero.mp h.symm)
      rw [hb_eq]
      exact hIPt
    let τ : ℝ := min ((1 - t) / 2) (eps / (2 * (W + 1)))
    let s : ℝ := t + τ
    have hτval : τ = min ((1 - t) / 2) (eps / (2 * (W + 1))) := rfl
    have hsval : s = t + τ := rfl
    have hτaux : τ ≤ (1 - t) / 2 := by rw [hτval]; exact min_le_left _ _
    have hτeps : τ ≤ eps / (2 * (W + 1)) := by rw [hτval]; exact min_le_right _ _
    have hτpos : 0 < τ := by
      rw [hτval]
      exact lt_min (by linarith) (div_pos heps (by linarith))
    have hst : t < s := by rw [hsval]; linarith
    have hs1 : s ≤ 1 := by rw [hsval]; linarith
    have hs0 : 0 ≤ s := le_trans ht01.1 hst.le
    have hdiff : (toR a + s • (b - toR a)) - (toR a + t • (b - toR a))
        = (s - t) • (b - toR a) := by
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hst_sub : s - t = τ := by rw [hsval]; ring
    have hdist : rNorm ((toR a + s • (b - toR a)) - (toR a + t • (b - toR a))) < eps := by
      rw [hdiff, rNorm_smul', hst_sub, abs_of_pos hτpos, ← hWval]
      have h1 : τ * W ≤ (eps / (2 * (W + 1))) * W := mul_le_mul_of_nonneg_right hτeps hWpos.le
      have h2 : (eps / (2 * (W + 1))) * W < eps := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (W + 1))]
        nlinarith [heps, hWpos]
      linarith
    have hIPts : IPt d n (toR a + s • (b - toR a)) :=
      hneigh (toR a + s • (b - toR a)) hdist
    exact (hmax s ⟨hs0, hs1⟩ hst) hIPts

end Work.HP.BoundaryMain
