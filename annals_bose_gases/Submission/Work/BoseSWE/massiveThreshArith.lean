import ChallengeDeps
import Submission.Work.BoseFixB1.perBoxFWeight_square_arith
import Submission.Work.BoseSWE.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseSWE.massiveThreshArith` — the threshold arithmetic of the massive (regular) box
branch

The "massive" branch of the `BoseSWE` design (`Submission/Work/BoseSWE/BRIEF.md` §3, node N2′)
needs a *threshold* `ε₀` such that for every admissible chemical potential the two FS-parameter
monomials

    ℓ² d^{54}  and  d^{9/4} (ℓd)^{33/16}

dominate the prescribed constants `100 R² K₁` resp. `100 R² K₂ (ℓ)^{1/16}`.  Both are pure
`rpow`-monomials in the diluteness `t = μ (a v)³`, and both blow up as `t → 0⁺`:

    ℓ² d^{54}            = (a v)² t^{−2/323}         → ∞       (exponent −2/323 < 0),
    d^{9/4}(ℓd)^{33/16}  = ℓ^{1/16} · (a v)² t^{−2401/2584} → ∞ (exponent −2401/2584 < 0),

at FS's parameters (`ℓ = a v · t^{−163/323}`, `d = t^{6/323}`, `ℓd = a v · t^{−157/323}`,
see `Work.BoseFixB1.sideAt_eq_fsXp`, `Work.BoseFixB1.d_eq_fsXp`, `Work.BoseFixB1.d_mul_sideAt_eq`).
Hence for a single `ε₀` depending only on `a v, R, K₁, K₂` both inequalities hold throughout the
dilute regime — which is exactly the statement below.

The two closed forms are the content of `bSide_sq_mul_bD_pow54` and `bD_pow_mul_bSide_mul_bD_pow`
(in the `fsXp` vocabulary, where the exponent arithmetic is additive), and the threshold is
produced by the one-line lemma `exists_rpow_neg_ge`: for a *negative* exponent `e`, any constant is
dominated by `t ^ e` on a right neighbourhood of `0`.
-/

namespace Work.BoseSWE

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Real BigOperators

/-! ## 1. A negative power dominates every constant near `0⁺` -/

/-- For a negative exponent `e < 0`, any constant `N` is dominated by `t ^ e` for `t` in a right
neighbourhood of `0` (and the threshold can be taken inside any `(0, ε]`). -/
private lemma exists_rpow_neg_ge {e N ε : ℝ} (he : e < 0) (hε : 0 < ε) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ t₀ ≤ ε ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → N ≤ t ^ e := by
  set M : ℝ := max N 1 + 1 with hMdef
  have hM1 : 1 ≤ M := by rw [hMdef]; linarith [le_max_right N 1]
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hNM : N ≤ M := by rw [hMdef]; linarith [le_max_left N 1]
  refine ⟨min ε (M ^ (1 / e)), lt_min hε (Real.rpow_pos_of_pos hMpos _), min_le_left _ _, ?_⟩
  intro t ht0 hle
  have hle' : t ≤ M ^ (1 / e) := le_trans hle (min_le_right _ _)
  have hmono : (M ^ (1 / e)) ^ e ≤ t ^ e :=
    Real.rpow_le_rpow_of_nonpos ht0 hle' he.le
  have hval : (M ^ (1 / e)) ^ e = M := by
    rw [← Real.rpow_mul hMpos.le,
      show (1 / e) * e = 1 by rw [one_div, inv_mul_cancel₀ (ne_of_lt he)], Real.rpow_one]
  rw [hval] at hmono
  exact le_trans hNM hmono

/-! ## 2. The two closed forms of FS's parameter monomials -/

/-- **The first threshold monomial.**  At FS's parameters `(ℓ d) = (a v · t^{−163/323}) · t^{6/323}`,
so `ℓ² d^{54} = (a v)² t^{−2/323}`: the box-squared volume factor times the `54`-th power of the
localisation parameter is a *negative* power of the diluteness (with the scattering length squared
in front). -/
private lemma bSide_sq_mul_bD_pow54 {A μ : ℝ} (hμ : 0 < μ) (hA : 0 < A) :
    (Work.BoseBox.sideAt μ A) ^ 2 * ((Work.BoseBox.paramsAt μ A).d) ^ 54
      = A ^ 2 * (μ * A ^ 3) ^ (-(2 / 323 : ℝ)) := by
  have ht : 0 < μ * A ^ 3 := by positivity
  rw [Work.BoseFixB1.sideAt_eq_fsXp hA hμ, Work.BoseFixB1.d_eq_fsXp]
  rw [mul_pow]
  have h1 : (Work.BoseBox.fsXp (μ * A ^ 3) (-163)) ^ 2
      = Work.BoseBox.fsXp (μ * A ^ 3) (-326) := by
    rw [Work.BoseBox.fsXp_pow ht.le, show (-163 : ℝ) * ((2 : ℕ) : ℝ) = -326 by norm_num]
  have h2 : (Work.BoseBox.fsXp (μ * A ^ 3) 6) ^ 54
      = Work.BoseBox.fsXp (μ * A ^ 3) 324 := by
    rw [Work.BoseBox.fsXp_pow ht.le, show (6 : ℝ) * ((54 : ℕ) : ℝ) = 324 by norm_num]
  have h3 : Work.BoseBox.fsXp (μ * A ^ 3) (-326) * Work.BoseBox.fsXp (μ * A ^ 3) 324
      = Work.BoseBox.fsXp (μ * A ^ 3) (-2) := by
    rw [Work.BoseBox.fsXp_mul ht, show (-326 : ℝ) + 324 = -2 by norm_num]
  rw [h1, h2]
  rw [show A ^ 2 * Work.BoseBox.fsXp (μ * A ^ 3) (-326) * Work.BoseBox.fsXp (μ * A ^ 3) 324
      = A ^ 2 * (Work.BoseBox.fsXp (μ * A ^ 3) (-326)
          * Work.BoseBox.fsXp (μ * A ^ 3) 324) by ring]
  rw [h3, Work.BoseBox.fsXp, show (-2 : ℝ) / 323 = -(2 / 323) by norm_num]

/-- **The second threshold monomial.**  `d^{9/4} (ℓd)^{33/16}
= ℓ^{1/16} · (a v)² t^{−2401/2584}`: the fractional powers of the localisation parameter and of the
small-box side combine into a single negative power of the diluteness, with `ℓ^{1/16}` — the very
factor that also multiplies the prescribed constant — left over. -/
private lemma bD_pow_mul_bSide_mul_bD_pow {A μ : ℝ} (hμ : 0 < μ) (hA : 0 < A) :
    ((Work.BoseBox.paramsAt μ A).d) ^ (9 / 4 : ℝ)
        * (Work.BoseBox.sideAt μ A * (Work.BoseBox.paramsAt μ A).d) ^ (33 / 16 : ℝ)
      = (A ^ 2 * Work.BoseBox.fsXp (μ * A ^ 3) (-(2401 / 8 : ℝ)))
        * (Work.BoseBox.sideAt μ A) ^ (1 / 16 : ℝ) := by
  have ht : 0 < μ * A ^ 3 := by positivity
  have hA0 : (0 : ℝ) ≤ A := hA.le
  have hX : (0 : ℝ) ≤ Work.BoseBox.fsXp (μ * A ^ 3) (-163) := (Work.BoseBox.fsXp_pos ht).le
  have hY : (0 : ℝ) ≤ Work.BoseBox.fsXp (μ * A ^ 3) (-157) := (Work.BoseBox.fsXp_pos ht).le
  have hd : ((Work.BoseBox.paramsAt μ A).d) ^ (9 / 4 : ℝ)
      = Work.BoseBox.fsXp (μ * A ^ 3) (27 / 2) := by
    rw [Work.BoseFixB1.d_eq_fsXp, Work.BoseBox.fsXp_rpow ht.le,
      show (6 : ℝ) * (9 / 4) = 27 / 2 by norm_num]
  have hld : (Work.BoseBox.sideAt μ A * (Work.BoseBox.paramsAt μ A).d) ^ (33 / 16 : ℝ)
      = A ^ (33 / 16 : ℝ) * Work.BoseBox.fsXp (μ * A ^ 3) (-(5181 / 16)) := by
    rw [mul_comm (Work.BoseBox.sideAt μ A), Work.BoseFixB1.d_mul_sideAt_eq hA hμ,
      Real.mul_rpow hA0 hY, Work.BoseBox.fsXp_rpow ht.le,
      show (-157 : ℝ) * (33 / 16) = -(5181 / 16) by norm_num]
  have hls : (Work.BoseBox.sideAt μ A) ^ (1 / 16 : ℝ)
      = A ^ (1 / 16 : ℝ) * Work.BoseBox.fsXp (μ * A ^ 3) (-(163 / 16)) := by
    rw [Work.BoseFixB1.sideAt_eq_fsXp hA hμ, Real.mul_rpow hA0 hX,
      Work.BoseBox.fsXp_rpow ht.le,
      show (-163 : ℝ) * (1 / 16) = -(163 / 16) by norm_num]
  have hA33 : A ^ 2 * A ^ (1 / 16 : ℝ) = A ^ (33 / 16 : ℝ) := by
    rw [← Real.rpow_natCast A 2, ← Real.rpow_add hA,
      show ((2 : ℕ) : ℝ) + 1 / 16 = 33 / 16 by norm_num]
  have h1 : Work.BoseBox.fsXp (μ * A ^ 3) (27 / 2)
        * Work.BoseBox.fsXp (μ * A ^ 3) (-(5181 / 16))
      = Work.BoseBox.fsXp (μ * A ^ 3) (-(4965 / 16)) := by
    rw [Work.BoseBox.fsXp_mul ht, show (27 : ℝ) / 2 + -(5181 / 16) = -(4965 / 16) by norm_num]
  have h2 : Work.BoseBox.fsXp (μ * A ^ 3) (-(2401 / 8))
        * Work.BoseBox.fsXp (μ * A ^ 3) (-(163 / 16))
      = Work.BoseBox.fsXp (μ * A ^ 3) (-(4965 / 16)) := by
    rw [Work.BoseBox.fsXp_mul ht,
      show (-(2401 / 8 : ℝ)) + (-(163 / 16)) = -(4965 / 16) by norm_num]
  rw [hd, hld, hls]
  rw [show Work.BoseBox.fsXp (μ * A ^ 3) (27 / 2)
          * (A ^ (33 / 16 : ℝ) * Work.BoseBox.fsXp (μ * A ^ 3) (-(5181 / 16)))
        = A ^ (33 / 16 : ℝ)
          * (Work.BoseBox.fsXp (μ * A ^ 3) (27 / 2)
              * Work.BoseBox.fsXp (μ * A ^ 3) (-(5181 / 16))) by ring,
      show (A ^ 2 * Work.BoseBox.fsXp (μ * A ^ 3) (-(2401 / 8)))
          * (A ^ (1 / 16 : ℝ) * Work.BoseBox.fsXp (μ * A ^ 3) (-(163 / 16)))
        = (A ^ 2 * A ^ (1 / 16 : ℝ))
          * (Work.BoseBox.fsXp (μ * A ^ 3) (-(2401 / 8))
              * Work.BoseBox.fsXp (μ * A ^ 3) (-(163 / 16))) by ring,
      h1, h2, hA33]

/-! ## 3. `bSide`/`bD` are FS's `sideAt`/`d` at `A = a v` -/

private lemma bSide_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) :
    Work.BoseFixB1.bSide v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := rfl

private lemma bD_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) :
    Work.BoseFixB1.bD v μ = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := rfl

/-! ## 4. The threshold arithmetic -/

theorem massiveThreshArith {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {R : ℝ} (hR : 0 < R) {K₁ K₂ : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      0 < Work.BoseFixB1.bD v μ ∧ 0 < Work.BoseFixB1.bSide v μ ∧
      100 * R ^ 2 * K₁ ≤ (Work.BoseFixB1.bSide v μ) ^ 2 * (Work.BoseFixB1.bD v μ) ^ 54 ∧
      100 * R ^ 2 * K₂ * (Work.BoseFixB1.bSide v μ) ^ (1 / 16 : ℝ)
        ≤ (Work.BoseFixB1.bD v μ) ^ (9 / 4 : ℝ)
          * (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) ^ (33 / 16 : ℝ) := by
  -- the two thresholds for `t = μ (a v)³`, at the constants normalised by `(a v)²`
  obtain ⟨t₁, ht₁, _, hk₁⟩ :=
    exists_rpow_neg_ge (e := -(2 / 323 : ℝ))
      (N := 100 * R ^ 2 * K₁ / (_root_.BoseGases.a v) ^ 2) (ε := 1) (by norm_num) one_pos
  obtain ⟨t₂, ht₂, _, hk₂⟩ :=
    exists_rpow_neg_ge (e := -(2401 / 2584 : ℝ))
      (N := 100 * R ^ 2 * K₂ / (_root_.BoseGases.a v) ^ 2) (ε := 1) (by norm_num) one_pos
  refine ⟨min t₁ t₂, lt_min ht₁ ht₂, ?_⟩
  intro μ hAdm
  have hμ : 0 < μ := hAdm.1
  have hdle : μ * (_root_.BoseGases.a v) ^ 3 ≤ min t₁ t₂ := hAdm.2.1
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have hbD : 0 < Work.BoseFixB1.bD v μ := by
    rw [bD_eq, Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_pos ht
  have hbS : 0 < Work.BoseFixB1.bSide v μ := by
    rw [bSide_eq, Work.BoseFixB1.sideAt_eq_fsXp hav hμ]
    exact mul_pos hav (Work.BoseBox.fsXp_pos ht)
  have hbS' : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rwa [bSide_eq] at hbS
  refine ⟨hbD, hbS, ?_, ?_⟩
  · -- `100 R² K₁ ≤ ℓ² d^{54}`
    have hkey := hk₁ (μ * (_root_.BoseGases.a v) ^ 3) ht (le_trans hdle (min_le_left _ _))
    have hfin : 100 * R ^ 2 * K₁
        ≤ (_root_.BoseGases.a v) ^ 2 * (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(2 / 323 : ℝ)) := by
      have h2 := mul_le_mul_of_nonneg_left hkey
        (by positivity : (0 : ℝ) ≤ (_root_.BoseGases.a v) ^ 2)
      rwa [mul_div_cancel₀ _
        (by positivity : ((_root_.BoseGases.a v) ^ 2) ≠ 0)] at h2
    rw [bSide_eq, bD_eq, bSide_sq_mul_bD_pow54 (A := _root_.BoseGases.a v) (μ := μ) hμ hav]
    exact hfin
  · -- `100 R² K₂ ℓ^{1/16} ≤ d^{9/4} (ℓd)^{33/16}`
    have hkey := hk₂ (μ * (_root_.BoseGases.a v) ^ 3) ht (le_trans hdle (min_le_right _ _))
    have hfs : (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(2401 / 2584 : ℝ))
        = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(2401 / 8 : ℝ)) := by
      rw [Work.BoseBox.fsXp, show (-(2401 / 8 : ℝ)) / 323 = -(2401 / 2584) by norm_num]
    have hfin : 100 * R ^ 2 * K₂
        ≤ (_root_.BoseGases.a v) ^ 2
          * Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-(2401 / 8 : ℝ)) := by
      have h2 := mul_le_mul_of_nonneg_left hkey
        (by positivity : (0 : ℝ) ≤ (_root_.BoseGases.a v) ^ 2)
      rw [mul_div_cancel₀ _
        (by positivity : ((_root_.BoseGases.a v) ^ 2) ≠ 0), hfs] at h2
      exact h2
    rw [bSide_eq, bD_eq, bD_pow_mul_bSide_mul_bD_pow (A := _root_.BoseGases.a v) (μ := μ) hμ hav]
    exact mul_le_mul_of_nonneg_right hfin (Real.rpow_nonneg hbS'.le _)

end Work.BoseSWE
