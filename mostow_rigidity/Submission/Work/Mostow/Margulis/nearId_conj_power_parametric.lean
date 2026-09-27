import Mathlib
import Submission.Work.Mostow.margulisPairDefs
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.abs_mat_le_tpart_actO
import Submission.Work.Mostow.poSheet
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.Margulis.exists_boost_near
import Submission.Work.Mostow.Margulis.exists_pow_near_fix_zero
import Submission.Work.Mostow.Margulis.near1_conj_pow

namespace Work.Mostow.Margulis

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Ordered products of near-identity matrices

`O1 n` is a non-commutative group, so `Finset.prod` is not available for a general index type;
we introduce the recursive ordered product `paProdRange A j = A 0 * A 1 * ⋯ * A (j-1)` and the
standard estimate that multiplying `j` matrices each `γ`-close to `1` produces an error
`(1 + msz n * γ)^j - 1`. -/

/-- The ordered product of the first `j` terms of a sequence of matrices. -/
def paProdRange (A : ℕ → O1 n) : ℕ → O1 n
  | 0 => 1
  | (k + 1) => paProdRange A k * A k

@[simp] lemma paProdRange_zero (A : ℕ → O1 n) : paProdRange A 0 = 1 := rfl
@[simp] lemma paProdRange_succ (A : ℕ → O1 n) (k : ℕ) :
    paProdRange A (k + 1) = paProdRange A k * A k := rfl

/-- A product of `j` matrices each within `γ` of the identity is within `(1 + msz n * γ)^j - 1`
of the identity. -/
lemma near1_paProdRange (n : ℕ) (A : ℕ → O1 n) {γ : ℝ} (hγ : 0 ≤ γ) (j : ℕ)
    (h : ∀ i < j, Near1 (A i) γ) :
    Near1 (paProdRange A j) ((1 + msz n * γ) ^ j - 1) := by
  induction j with
  | zero => simpa using (near1_one : Near1 (1 : O1 n) 0)
  | succ k ih =>
      rw [paProdRange_succ]
      have hk : ∀ i < k, Near1 (A i) γ := fun i hi => h i (Nat.lt_succ_of_lt hi)
      have hstep := near1_mul' (ih hk) (h k (Nat.lt_succ_self k))
      refine fun a b => le_trans (hstep a b) ?_
      have h1 : (1 : ℝ) ≤ 1 + msz n * γ := by
        have := mul_nonneg (msz_nonneg n) hγ
        linarith
      have h2 : (0 : ℝ) ≤ (1 + msz n * γ) ^ k := pow_nonneg (by linarith) k
      have h3 : (0 : ℝ) ≤ msz n * γ := mul_nonneg (msz_nonneg n) hγ
      have h4 : (1 : ℝ) ≤ msz n := one_le_msz n
      rw [pow_succ]
      nlinarith [h1, h2, h3, hγ, h4]

/-- Telescoping identity: the `j`-th power of `B * Q` is `Q ^ j` preceded by the product of the
conjugates `Q ^ i * B * (Q ^ i)⁻¹`, `0 ≤ i < j`. -/
lemma pow_mul_eq_paProdRange (n : ℕ) (B Q : O1 n) (j : ℕ) :
    (B * Q) ^ j = paProdRange (fun i => Q ^ i * B * (Q ^ i)⁻¹) j * Q ^ j := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [paProdRange_succ, pow_succ, ih]
      group

/-! ## A binomial estimate and the resulting choice of the boost accuracy -/

/-- For `0 ≤ x ≤ 1`, `(1 + x)^N ≤ 1 + (2^N - 1) * x`. -/
lemma binom_pow_le (N : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x) ^ N ≤ 1 + ((2 : ℝ) ^ N - 1) * x := by
  induction N with
  | zero => simp
  | succ k ih =>
      have hx2 : x * x ≤ x := by nlinarith
      have hge : (0 : ℝ) ≤ (2 : ℝ) ^ k - 1 := by
        have h : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        linarith
      have hA : (0 : ℝ) ≤ 1 + x := by linarith
      calc (1 + x) ^ (k + 1) = (1 + x) ^ k * (1 + x) := by ring
        _ ≤ (1 + (2 ^ k - 1) * x) * (1 + x) := mul_le_mul_of_nonneg_right ih hA
        _ = 1 + (2 ^ (k + 1) - 1) * x + (2 ^ k - 1) * (x * x - x) := by ring
        _ ≤ 1 + (2 ^ (k + 1) - 1) * x := by
            have hnn : (2 ^ k - 1) * (x * x - x) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos hge (by linarith)
            linarith

/-- For every `N`, `Λ ≥ 0` and `A > 0` there is `δ > 0` with `(1 + Λ * δ)^N - 1 ≤ A`. -/
lemma exists_delta_pow_bound (N : ℕ) (Λ A : ℝ) (hΛ : 0 ≤ Λ) (hA : 0 < A) :
    ∃ δ : ℝ, 0 < δ ∧ (1 + Λ * δ) ^ N - 1 ≤ A := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact ⟨1, one_pos, by rw [hN, pow_zero]; linarith⟩
  · set s : ℝ := (2 : ℝ) ^ N - 1 with hsdef
    have hs : 0 < s := by
      have h : (1 : ℝ) < 2 ^ N := one_lt_pow₀ (by norm_num : (1 : ℝ) < 2)
        (Nat.pos_iff_ne_zero.mp hN)
      rw [hsdef]; linarith
    set cc : ℝ := min 1 (A / s) with hccdef
    have hcc0 : 0 < cc := by rw [hccdef]; exact lt_min one_pos (div_pos hA hs)
    have hcc1 : cc ≤ 1 := by rw [hccdef]; exact min_le_left _ _
    have hccA : cc ≤ A / s := by rw [hccdef]; exact min_le_right _ _
    have hcs : s * cc ≤ A := by
      have h1 : cc * s ≤ (A / s) * s := mul_le_mul_of_nonneg_right hccA hs.le
      rw [div_mul_cancel₀ A (ne_of_gt hs)] at h1
      linarith
    have hden : (0 : ℝ) < Λ + 1 := by linarith
    refine ⟨cc / (Λ + 1), div_pos hcc0 hden, ?_⟩
    set x : ℝ := Λ * (cc / (Λ + 1)) with hxdef
    have hx0 : 0 ≤ x := by rw [hxdef]; exact mul_nonneg hΛ (div_nonneg hcc0.le hden.le)
    have hx1 : x ≤ 1 := by
      rw [hxdef]
      have he : Λ * (cc / (Λ + 1)) = Λ * cc / (Λ + 1) := (mul_div_assoc Λ cc (Λ + 1)).symm
      rw [he, div_le_iff₀ hden]
      nlinarith [hΛ, hcc1, hcc0.le]
    have hsx : s * x ≤ A := by
      rw [hxdef]
      have he : s * (Λ * (cc / (Λ + 1))) = s * Λ * cc / (Λ + 1) := by
        rw [mul_div_assoc]; ring
      rw [he, div_le_iff₀ hden]
      nlinarith [hΛ, hcs, hA]
    have hb := binom_pow_le N hx0 hx1
    have : (1 + x) ^ N - 1 ≤ A := by linarith
    rwa [show (1 + Λ * (cc / (Λ + 1))) = 1 + x from by rw [hxdef]] at this

/-! ## The core base-point estimate -/

/-- **Core estimate.**  For every accuracy `η > 0` there are `N` and `δ > 0` such that every
`O(n,1)`-matrix `M` displacing the base point by less than `δ` has a power `M ^ j`, `0 < j ≤ N`,
that is entrywise `η`-near the identity.

The matrix is split as `M = B * Q` with `B` a boost carrying `0` to `actO M 0` and `Q = B⁻¹ * M`
in the stabiliser of the origin.  The stabiliser being compact (`Work.Mostow.Margulis.exists_pow_near_fix_zero`)
supplies a uniform power `j` of `Q` close to `1`; conjugating the small boost `B` by the powers of
`Q` (`Work.Mostow.Margulis.near1_conj_pow`) keeps it small, so that the product formula
`M ^ j = (∏ Q^i B Q^{-i}) * Q^j` controls the defect. -/
lemma exists_pow_near_of_short_base (n : ℕ) (hI : HypIsometryProp n) (η : ℝ) (hη : 0 < η) :
    ∃ (N : ℕ) (δ : ℝ), 0 < N ∧ 0 < δ ∧ ∀ M : O1 n,
      hdist (0 : E n) (actO M (0 : E n)) < δ →
        ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ Near1 (M ^ j) η := by
  have hmsz1 : (0 : ℝ) < msz n + 1 := by have := msz_nonneg n; linarith
  -- the two accuracies: `c` for the stabiliser pigeonhole *and* for the boost-product defect
  set c : ℝ := min (η / 4) (1 / (4 * (msz n + 1))) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact lt_min (by linarith) (by positivity)
  have hcη : c ≤ η / 4 := by rw [hcdef]; exact min_le_left _ _
  have hcm : c ≤ 1 / (4 * (msz n + 1)) := by rw [hcdef]; exact min_le_right _ _
  have hmc : msz n * c ≤ 1 / 4 := by
    have h1 : msz n * c ≤ msz n * (1 / (4 * (msz n + 1))) :=
      mul_le_mul_of_nonneg_left hcm (msz_nonneg n)
    have h2 : msz n * (1 / (4 * (msz n + 1))) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (msz n + 1))]
      nlinarith [one_le_msz n]
    linarith
  have hbound : msz n * c * c + c + c ≤ η := by
    have hc0 : 0 ≤ c := le_of_lt hcpos
    have hsq : msz n * c * c ≤ c / 4 := by nlinarith [hmc, hc0]
    nlinarith [hsq, hcη]
  -- the uniform power of the stabiliser part
  obtain ⟨N, hNpos, hNmain⟩ := exists_pow_near_fix_zero n c hcpos
  -- the boost accuracy
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ :=
    exists_delta_pow_bound N (3 * msz n ^ 3) c
      (mul_nonneg (by norm_num) (pow_nonneg (msz_nonneg n) 3)) hcpos
  refine ⟨N, min δ₀ 1, hNpos, lt_min hδ₀pos one_pos, ?_⟩
  intro M hM
  set θ : ℝ := hdist (0 : E n) (actO M (0 : E n)) with hθdef
  have hθ0 : 0 ≤ θ := hI.1 (0 : E n) (actO M (0 : E n))
  have hθ1 : θ < 1 := lt_of_lt_of_le hM (min_le_right _ _)
  have hθδ : θ < δ₀ := lt_of_lt_of_le hM (min_le_left _ _)
  obtain ⟨B, hB0, hBnear⟩ := exists_boost_near n (actO M (0 : E n)) (le_of_lt hθ1)
  set Q : O1 n := B⁻¹ * M with hQdef
  have hQfix : actO Q (0 : E n) = 0 := by
    rw [hQdef, poSheet_actO_mul, ← hB0, ← poSheet_actO_mul, inv_mul_cancel, poSheet_actO_one]
  obtain ⟨j, hjpos, hjle, hjQ⟩ := hNmain Q hQfix
  have hMeeq : M = B * Q := by rw [hQdef]; group
  have hpow : M ^ j = paProdRange (fun i => Q ^ i * B * (Q ^ i)⁻¹) j * Q ^ j := by
    rw [hMeeq, pow_mul_eq_paProdRange]
  have hγ : 0 ≤ msz n ^ 2 * (3 * θ) :=
    mul_nonneg (pow_nonneg (msz_nonneg n) 2) (by linarith)
  have hfac : ∀ i < j, Near1 (Q ^ i * B * (Q ^ i)⁻¹) (msz n ^ 2 * (3 * θ)) :=
    fun i _ => near1_conj_pow n Q B (3 * θ) i hQfix hBnear
  have hC := near1_paProdRange n (fun i => Q ^ i * B * (Q ^ i)⁻¹) hγ j hfac
  have hstep := near1_mul' hC hjQ
  refine ⟨j, hjpos, hjle, ?_⟩
  rw [hpow]
  refine fun a b => le_trans (hstep a b) ?_
  have hexp : msz n * (msz n ^ 2 * (3 * θ)) = 3 * msz n ^ 3 * θ := by ring
  have hbase1 : (1 : ℝ) ≤ 1 + 3 * msz n ^ 3 * θ := by
    have h3 : (0 : ℝ) ≤ 3 * msz n ^ 3 :=
      mul_nonneg (by norm_num) (pow_nonneg (msz_nonneg n) 3)
    have := mul_nonneg h3 hθ0
    linarith
  have hbase2 : 1 + 3 * msz n ^ 3 * θ ≤ 1 + 3 * msz n ^ 3 * δ₀ := by
    have h3 : (0 : ℝ) ≤ 3 * msz n ^ 3 :=
      mul_nonneg (by norm_num) (pow_nonneg (msz_nonneg n) 3)
    have := mul_le_mul_of_nonneg_left (le_of_lt hθδ) h3
    linarith
  have hpowmono : (1 + 3 * msz n ^ 3 * θ) ^ j ≤ (1 + 3 * msz n ^ 3 * δ₀) ^ N :=
    le_trans (pow_le_pow_right₀ hbase1 hjle) (pow_le_pow_left₀ (by linarith) hbase2 N)
  have hA_le_c : (1 + msz n * (msz n ^ 2 * (3 * θ))) ^ j - 1 ≤ c := by
    have h1 : (1 + msz n * (msz n ^ 2 * (3 * θ))) ^ j = (1 + 3 * msz n ^ 3 * θ) ^ j := by
      rw [hexp]
    rw [h1]
    linarith [hpowmono, hδ₀]
  have hAnonneg : 0 ≤ (1 + msz n * (msz n ^ 2 * (3 * θ))) ^ j - 1 := by
    have hbase3 : (1 : ℝ) ≤ 1 + msz n * (msz n ^ 2 * (3 * θ)) := by
      have := mul_nonneg (msz_nonneg n) hγ
      linarith
    have := one_le_pow₀ hbase3 (n := j)
    linarith
  nlinarith [hA_le_c, hAnonneg, hbound, msz_nonneg n, le_of_lt hcpos]

/-- Bounded-power pigeonhole, with the near-identity tolerance as a parameter: for every `η > 0`
there are `N` and `δ > 0` such that for every point `u` there is a single conjugating element `h`
with `h • 0 = u` which works for *all* elements displacing `u` by less than `δ`: each such `g` has a
power `g^j`, `0 < j ≤ N`, whose conjugate `h⁻¹ * g^j * h` has a matrix representative within `η` of
the identity.

Proof sketch: conjugate by `h` so that `u = 0`; `γ = h⁻¹ g h` then has `hdist 0 (γ • 0) < δ`.  Write
`γ = β k` with `β` the boost of size `< δ` and `k ∈ Stab(0) ≅ O(n)` compact; then
`γ^j = β (kβk⁻¹) … (k^{j-1}βk^{-(j-1)}) k^j` is a product of `j` boosts of size `< δ` times `k^j`.
Compactness of `O(n)` (pigeonhole on the powers, cf. `Work.Mostow.rotPigeonhole`) gives `N` with every
`k` having `k^j` within `η/2` of `1` for some `0 < j ≤ N`; choosing `δ` with `(1 + Cδ)^N - 1 ≤ η/2`
finishes.  No discreteness is needed. -/
theorem nearId_conj_power_parametric (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∀ η : ℝ, 0 < η → ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧ 0 < N ∧
      ∀ (u : E n), ∃ h : PO n 1, h • (0 : E n) = u ∧
        ∀ (g : PO n 1), hdist u (g • u) < δ →
          ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ NearId η (h⁻¹ * g ^ j * h) := by
  intro η hη
  obtain ⟨N, δ, hNpos, hδpos, hbase⟩ := exists_pow_near_of_short_base n hI η hη
  refine ⟨N, δ, hδpos, hNpos, ?_⟩
  intro u
  obtain ⟨g₀, hg₀⟩ := (BoostTransitive n hA).1 u
  refine ⟨g₀, hg₀, ?_⟩
  intro g hgu
  set H : O1 n := rep g₀ with hHdef
  have hg₀coe : ((H : O1 n) : PO n 1) = g₀ := by
    rw [hHdef]; exact Quotient.out_eq g₀
  have hrep₀ : ((rep g₀ : O1 n) : PO n 1) = g₀ := Quotient.out_eq g₀
  have hH0 : actO H (0 : E n) = u := by
    rw [hHdef, ← hA.2.1 (rep g₀) (0 : E n), hrep₀]
    exact hg₀
  set M : O1 n := H⁻¹ * rep g * H with hMdef
  have hrep : ((rep g : O1 n) : PO n 1) = g := Quotient.out_eq g
  have hMcoe : (M : PO n 1) = (H : PO n 1)⁻¹ * g * (H : PO n 1) := by
    rw [hMdef]; simp [hrep]
  have hMshort : hdist (0 : E n) (actO M (0 : E n)) < δ := by
    have hMact : (M : PO n 1) • (0 : E n) = (H : PO n 1)⁻¹ • (g • u) := by
      simp only [hMcoe, hA.2.2.2.2.1, hA.2.1, hH0]
    rw [← hA.2.1 M (0 : E n), hMact]
    have hiso := hI.2.2.2.2.2.2.1 (H : PO n 1) (0 : E n) ((H : PO n 1)⁻¹ • (g • u))
    rw [← hiso]
    have hfix : (H : PO n 1) • ((H : PO n 1)⁻¹ • (g • u)) = g • u := by
      rw [← hA.2.2.2.2.1, mul_inv_cancel, hA.2.2.2.1]
    rw [hA.2.1, hH0, hfix]
    exact hgu
  obtain ⟨j, hjpos, hjle, hjNear⟩ := hbase M hMshort
  refine ⟨j, hjpos, hjle, ?_⟩
  refine ⟨M ^ j, ?_, hjNear⟩
  have hconj : ∀ k : ℕ, ((H : PO n 1)⁻¹ * g * (H : PO n 1)) ^ k
      = (H : PO n 1)⁻¹ * g ^ k * (H : PO n 1) := by
    intro k
    induction k with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_succ, ih]; group
  rw [show ((M ^ j : O1 n) : PO n 1) = (M : PO n 1) ^ j from rfl, hMcoe, hconj j]
  rw [hg₀coe]

end

end Work.Mostow.Margulis
