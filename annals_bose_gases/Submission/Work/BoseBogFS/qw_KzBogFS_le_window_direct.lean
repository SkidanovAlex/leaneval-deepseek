import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.sum_normSq_bogBShift_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.qw_KzBogFS_le_window_direct`

The **upper** bound on `𝒦^Bog` on window states, proved **directly from the definition**
of `KzBogFS` — i.e. *without* the diagonalisation and hence **without the slot**
`γ_k² ≤ 1` (`FINDING_hgamma_threshold_obstruction.md`).

`qw_KzBogFS_le_window` proves the same conclusion through the diagonalised value
`⟨f,𝒦^Bog f⟩ = Σ_k𝒟_k‖b̂_k f‖² − (…)‖f‖²`, and that route *pays* `(1+γ_k²)‖f‖²` per mode,
which is why it needs `γ_k² ≤ 1` at *every* mode — a row which is **false** at modes sitting
just above the `τ̃`-threshold.  Here the value is bounded by expanding the pair quadratic

```
𝒜_k(n_k+n_{−k}) + ℬ_k(a_ka_{−k}+a_k†a_{−k}†) + 𝒞_k(a_k+a_k†+a_{−k}+a_{−k}†)
```

with the arithmetic–geometric mean, using only the *coefficient* bounds
`𝒜_k ≤ A`, `|ℬ_k| ≤ A`, `|𝒞_k| ≤ C` and the Bessel/window rows:

```
⟨f, 𝒦^Bog f⟩ ≤ 3(A+C+1) Σ_k (‖a_k f‖² + ‖a_{−k} f‖² + ‖a_k† f‖² + ‖a_{−k}† f‖² + ‖f‖²)
             ≤ 100(A+C+1)(𝓜+1)(#Mode+1)‖f‖²
             ≤ Kbar‖f‖²          whenever  10⁶(A+C+1)(𝓜+1)(#Mode+1) ≤ Kbar.
```

`‖a_k† f‖² = ‖a_k f‖² + ccrK k k·‖f‖²`, `Σ_k ccrK k k ≤ #Mode` (`BogNumeric.hccr`) and
`Σ_k‖a_k f‖² ≤ Cn⟨f,T.N f⟩ ≤ 16𝓜‖f‖²` (Bessel + window) are the only inputs.
No `γ` appears anywhere.
-/

namespace Work.BoseBogFS

noncomputable section

open scoped BigOperators

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The quadratic form as linear algebra -/

theorem qw_add_bog (F : FockData Mode) (f : F.H) (X Y : F.H →ₗ[ℝ] F.H) :
    F.qw f (X + Y) = F.qw f X + F.qw f Y := by
  simp only [FockData.qw, LinearMap.add_apply, map_add]

theorem qw_add_three_bog (F : FockData Mode) (f : F.H) (X Y Z : F.H →ₗ[ℝ] F.H) :
    F.qw f (X + Y + Z) = F.qw f X + F.qw f Y + F.qw f Z := by
  rw [qw_add_bog, qw_add_bog]

theorem qw_smul_bog (F : FockData Mode) (f : F.H) (s : ℝ) (X : F.H →ₗ[ℝ] F.H) :
    F.qw f (s • X) = s * F.qw f X := by
  simp only [FockData.qw, LinearMap.smul_apply, map_smul, smul_eq_mul]

theorem qw_nOp_bog (F : FockData Mode) (f : F.H) (i : Mode) :
    F.qw f (F.nOp i) = F.bp (F.a i f) (F.a i f) := by
  simp only [FockData.qw, FockData.nOp, LinearMap.comp_apply, F.aDag_adjoint]

theorem qw_a_pair_bog (F : FockData Mode) (f : F.H) (i j : Mode) :
    F.qw f (F.a i ∘ₗ F.a j) = F.bp (F.a j f) (F.aDag i f) := by
  rw [FockData.qw, LinearMap.comp_apply, F.bp_symm (F.a i (F.a j f)) f]
  exact ((F.bp_symm (F.a j f) (F.aDag i f)).trans (F.aDag_adjoint i f (F.a j f))).symm

theorem qw_aDag_pair_bog (F : FockData Mode) (f : F.H) (i j : Mode) :
    F.qw f (F.aDag i ∘ₗ F.aDag j) = F.bp (F.aDag j f) (F.a i f) := by
  rw [FockData.qw, LinearMap.comp_apply]
  exact F.aDag_adjoint i (F.aDag j f) f

theorem qw_a_one_bog (F : FockData Mode) (f : F.H) (i : Mode) :
    F.qw f (F.a i) = F.bp (F.a i f) f := rfl

theorem qw_aDag_one_bog (F : FockData Mode) (f : F.H) (i : Mode) :
    F.qw f (F.aDag i) = F.bp (F.aDag i f) f := rfl

/-! ## 2. The exact expansion of the pair quadratic in the Fock form -/

theorem qw_bogPairOp_expand (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (f : F.H) :
    F.qw f (bogPairOp F E ρ k)
      = bogA E ρ k * (F.bp (F.a k f) (F.a k f) + F.bp (F.a (-k) f) (F.a (-k) f))
        + bogB E ρ k * (F.bp (F.a (-k) f) (F.aDag k f) + F.bp (F.aDag (-k) f) (F.a k f))
        + bogC E ρ k * (F.bp (F.a k f) f + F.bp (F.aDag k f) f + F.bp (F.a (-k) f) f
            + F.bp (F.aDag (-k) f) f) := by
  simp only [bogPairOp, qw_add_bog, qw_smul_bog, qw_nOp_bog,
    qw_a_pair_bog, qw_aDag_pair_bog, qw_a_one_bog, qw_aDag_one_bog]
  try ring

/-- The per-mode bound of the direct route: from the coefficient rows `𝒜_k ≤ A`,
`|ℬ_k| ≤ A`, `|𝒞_k| ≤ C` (and `0 ≤ A`, `0 ≤ C`),

```
⟨f, pairOp_k f⟩ ≤ 3(A+C+1)(‖a_k f‖² + ‖a_{−k} f‖² + ‖a_k† f‖² + ‖a_{−k}† f‖² + ‖f‖²).
```

The three pieces are: diagonal `𝒜_k(p+q) ≤ A(p+q)`, the two cross terms bounded by
`|ℬ_k|(|⟨a_{−k}f, a_k†f⟩| + |⟨a_{−k}†f, a_kf⟩|) ≤ A(p+q+r+s)/2` (`bp_abs_le`), and the four
linear terms by `|𝒞_k|(p+r+q+s)√z ≤ C((p+q+r+s)/2 + 2z)`. -/
theorem qw_bogPairOp_le_direct (F : FockData Mode) (E : Q3Env Mode) (ρ A C : ℝ) (k : Mode)
    (f : F.H) (hAk : bogA E ρ k ≤ A) (hBk : |bogB E ρ k| ≤ A) (hCk : |bogC E ρ k| ≤ C)
    (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) :
    F.qw f (bogPairOp F E ρ k)
      ≤ 3 * (A + C + 1) * (F.bp (F.a k f) (F.a k f) + F.bp (F.a (-k) f) (F.a (-k) f)
          + F.bp (F.aDag k f) (F.aDag k f) + F.bp (F.aDag (-k) f) (F.aDag (-k) f)
          + F.bp f f) := by
  rw [qw_bogPairOp_expand F E ρ k f]
  have hp : 0 ≤ F.bp (F.a k f) (F.a k f) := F.bp_nonneg _
  have hq : 0 ≤ F.bp (F.a (-k) f) (F.a (-k) f) := F.bp_nonneg _
  have hr : 0 ≤ F.bp (F.aDag k f) (F.aDag k f) := F.bp_nonneg _
  have hs : 0 ≤ F.bp (F.aDag (-k) f) (F.aDag (-k) f) := F.bp_nonneg _
  have hz : 0 ≤ F.bp f f := F.bp_nonneg _
  set p := F.bp (F.a k f) (F.a k f) with hpdef
  set q := F.bp (F.a (-k) f) (F.a (-k) f) with hqdef
  set r := F.bp (F.aDag k f) (F.aDag k f) with hrdef
  set s := F.bp (F.aDag (-k) f) (F.aDag (-k) f) with hsdef
  set zz := F.bp f f with hzzdef
  have hp' : 0 ≤ p := hp
  have hq' : 0 ≤ q := hq
  have hr' : 0 ≤ r := hr
  have hs' : 0 ≤ s := hs
  have hz' : 0 ≤ zz := hz
  -- the two cross terms
  have hX1 : |F.bp (F.a (-k) f) (F.aDag k f)| ≤ (q + r) / 2 :=
    Work.BoseB7.SumABound.bp_abs_le F (F.a (-k) f) (F.aDag k f)
  have hX2 : |F.bp (F.aDag (-k) f) (F.a k f)| ≤ (s + p) / 2 :=
    Work.BoseB7.SumABound.bp_abs_le F (F.aDag (-k) f) (F.a k f)
  -- the four linear terms
  have hL1 : |F.bp (F.a k f) f| ≤ (p + zz) / 2 :=
    Work.BoseB7.SumABound.bp_abs_le F (F.a k f) f
  have hL2 : |F.bp (F.aDag k f) f| ≤ (r + zz) / 2 :=
    Work.BoseB7.SumABound.bp_abs_le F (F.aDag k f) f
  have hL3 : |F.bp (F.a (-k) f) f| ≤ (q + zz) / 2 :=
    Work.BoseB7.SumABound.bp_abs_le F (F.a (-k) f) f
  have hL4 : |F.bp (F.aDag (-k) f) f| ≤ (s + zz) / 2 :=
    Work.BoseB7.SumABound.bp_abs_le F (F.aDag (-k) f) f
  set X1 := F.bp (F.a (-k) f) (F.aDag k f) with hX1def
  set X2 := F.bp (F.aDag (-k) f) (F.a k f) with hX2def
  set L1 := F.bp (F.a k f) f with hL1def
  set L2 := F.bp (F.aDag k f) f with hL2def
  set L3 := F.bp (F.a (-k) f) f with hL3def
  set L4 := F.bp (F.aDag (-k) f) f with hL4def
  -- the diagonal piece
  have e1 : bogA E ρ k * (p + q) ≤ A * (p + q) :=
    mul_le_mul_of_nonneg_right hAk (add_nonneg hp' hq')
  -- the cross piece
  have e2 : bogB E ρ k * (X1 + X2) ≤ A * (p + q + r + s) / 2 := by
    have h1 : bogB E ρ k * (X1 + X2) ≤ A * (|X1| + |X2|) := by
      have hsplit : bogB E ρ k * (X1 + X2)
          = bogB E ρ k * X1 + bogB E ρ k * X2 := by ring
      rw [hsplit]
      calc bogB E ρ k * X1 + bogB E ρ k * X2
          ≤ |bogB E ρ k * X1| + |bogB E ρ k * X2| :=
            add_le_add (le_abs_self _) (le_abs_self _)
        _ = |bogB E ρ k| * (|X1| + |X2|) := by rw [abs_mul, abs_mul]; ring
        _ ≤ A * (|X1| + |X2|) :=
            mul_le_mul_of_nonneg_right hBk (add_nonneg (abs_nonneg _) (abs_nonneg _))
    have h2 : |X1| + |X2| ≤ (q + r) / 2 + (s + p) / 2 := add_le_add hX1 hX2
    calc bogB E ρ k * (X1 + X2) ≤ A * (|X1| + |X2|) := h1
      _ ≤ A * ((q + r) / 2 + (s + p) / 2) := mul_le_mul_of_nonneg_left h2 hA0
      _ = A * (p + q + r + s) / 2 := by ring
  -- the linear piece
  have e3 : bogC E ρ k * (L1 + L2 + L3 + L4) ≤ C * ((p + q + r + s) / 2 + 2 * zz) := by
    have h1 : bogC E ρ k * (L1 + L2 + L3 + L4) ≤ C * (|L1| + |L2| + |L3| + |L4|) := by
      have hsplit : bogC E ρ k * (L1 + L2 + L3 + L4)
          = bogC E ρ k * L1 + bogC E ρ k * L2 + bogC E ρ k * L3 + bogC E ρ k * L4 := by ring
      rw [hsplit]
      calc bogC E ρ k * L1 + bogC E ρ k * L2 + bogC E ρ k * L3 + bogC E ρ k * L4
          ≤ |bogC E ρ k * L1| + |bogC E ρ k * L2| + |bogC E ρ k * L3| + |bogC E ρ k * L4| := by
            linarith [le_abs_self (bogC E ρ k * L1), le_abs_self (bogC E ρ k * L2),
              le_abs_self (bogC E ρ k * L3), le_abs_self (bogC E ρ k * L4)]
        _ = |bogC E ρ k| * (|L1| + |L2| + |L3| + |L4|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul]; ring
        _ ≤ C * (|L1| + |L2| + |L3| + |L4|) :=
            mul_le_mul_of_nonneg_right hCk
              (by positivity)
    have h2 : |L1| + |L2| + |L3| + |L4| ≤ (p + zz) / 2 + (r + zz) / 2 + (q + zz) / 2
        + (s + zz) / 2 := by
      linarith [hL1, hL2, hL3, hL4]
    calc bogC E ρ k * (L1 + L2 + L3 + L4) ≤ C * (|L1| + |L2| + |L3| + |L4|) := h1
      _ ≤ C * ((p + zz) / 2 + (r + zz) / 2 + (q + zz) / 2 + (s + zz) / 2) :=
          mul_le_mul_of_nonneg_left h2 hC0
      _ = C * ((p + q + r + s) / 2 + 2 * zz) := by ring
  -- assemble
  have hT : 0 ≤ p + q + r + s := by linarith
  have hAC : 0 ≤ A + C + 1 := by linarith
  have hsum : A * (p + q) + A * (p + q + r + s) / 2 + C * ((p + q + r + s) / 2 + 2 * zz)
      ≤ 3 * (A + C + 1) * (p + q + r + s + zz) := by
    have h1 : A * (p + q) ≤ (A + C + 1) * (p + q + r + s) := by
      have h2 : A ≤ A + C + 1 := by linarith
      have h3 : p + q ≤ p + q + r + s := by linarith
      calc A * (p + q) ≤ (A + C + 1) * (p + q) := mul_le_mul_of_nonneg_right h2 (by linarith)
        _ ≤ (A + C + 1) * (p + q + r + s) := mul_le_mul_of_nonneg_left h3 hAC
    have h4 : A * (p + q + r + s) / 2 ≤ (A + C + 1) * (p + q + r + s) := by
      have h5 : A / 2 ≤ A + C + 1 := by linarith
      calc A * (p + q + r + s) / 2 = A / 2 * (p + q + r + s) := by ring
        _ ≤ (A + C + 1) * (p + q + r + s) := mul_le_mul_of_nonneg_right h5 hT
    have h6 : C * ((p + q + r + s) / 2 + 2 * zz) ≤ (A + C + 1) * (p + q + r + s)
          + 3 * (A + C + 1) * zz := by
      have h7 : C * (p + q + r + s) / 2 ≤ (A + C + 1) * (p + q + r + s) := by
        have h8 : C / 2 ≤ A + C + 1 := by linarith
        calc C * (p + q + r + s) / 2 = C / 2 * (p + q + r + s) := by ring
          _ ≤ (A + C + 1) * (p + q + r + s) := mul_le_mul_of_nonneg_right h8 hT
      have h9 : 2 * C * zz ≤ 3 * (A + C + 1) * zz := by
        have h10 : 2 * C ≤ 3 * (A + C + 1) := by linarith
        calc 2 * C * zz ≤ (3 * (A + C + 1)) * zz := mul_le_mul_of_nonneg_right h10 hz'
          _ = 3 * (A + C + 1) * zz := by ring
      have h11 : C * ((p + q + r + s) / 2 + 2 * zz)
          = C * (p + q + r + s) / 2 + 2 * C * zz := by ring
      linarith [h7, h9, h11]
    linarith [h1, h4, h6]
  have hmain : bogA E ρ k * (p + q) + bogB E ρ k * (X1 + X2)
        + bogC E ρ k * (L1 + L2 + L3 + L4)
      ≤ 3 * (A + C + 1) * (p + q + r + s + zz) := by
    linarith [e1, e2, e3, hsum]
  rw [hzzdef, hsdef, hrdef, hqdef, hpdef] at hmain ⊢
  exact hmain

/-! ## 4. The window bound -/

/-- **The direct window bound for `𝒦^Bog`** — `qw_KzBogFS_le_window` *without* the slot
`γ_k² ≤ 1`.  The coefficient rows `𝒜_k ≤ A`, `|𝒞_k| ≤ C` (with `|ℬ_k| ≤ 𝒜_k ≤ A` from
`BogNumeric.hB`) replace the diagonalisation, and the conclusion is the same up to the
explicit constant `Kbar ⊇ 10⁶(A+C+1)(𝓜+1)(#Mode+1)`. -/
theorem qw_KzBogFS_le_window_direct {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    (F : FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Q3Env Mode)
    (ρ Cn A C Kbar : ℝ)
    (hnum : BogNumeric F E ρ) (hbigM : 0 ≤ E.bigM)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (hCn : Cn ≤ 16)
    (hAb : ∀ k : Mode, bogA E ρ k ≤ A)
    (hCb : ∀ k : Mode, |bogC E ρ k| ≤ C)
    (hKbig : 10 ^ 6 * (A + C + 1) * (E.bigM + 1) * ((Fintype.card Mode : ℝ) + 1) ≤ Kbar) :
    ∀ f : F.H, T.NWindow E.bigM f →
      F.qw f (KzBogFS F E ρ) ≤ Kbar * F.normSq f := by
  intro f hf
  rw [FockData.normSq]
  have hA0 : 0 ≤ A := le_trans (hnum.hA 0).le (hAb 0)
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hCb 0)
  have hz : 0 ≤ F.bp f f := F.bp_nonneg f
  have hcard : 0 ≤ (Fintype.card Mode : ℝ) := Nat.cast_nonneg _
  have hper : ∀ k : Mode, F.qw f (bogPairOp F E ρ k)
      ≤ 3 * (A + C + 1) * (F.bp (F.a k f) (F.a k f) + F.bp (F.a (-k) f) (F.a (-k) f)
          + F.bp (F.aDag k f) (F.aDag k f) + F.bp (F.aDag (-k) f) (F.aDag (-k) f)
          + F.bp f f) := fun k =>
    qw_bogPairOp_le_direct F E ρ A C k f (hAb k) (le_trans (hnum.hB k) (hAb k)) (hCb k) hA0 hC0
  rw [KzBogFS_eq_sum, qw_sum]
  have hs1 : (∑ k : Mode, (1 / 2 : ℝ) * F.qw f (bogPairOp F E ρ k))
      ≤ ∑ k : Mode, (1 / 2 : ℝ) * (3 * (A + C + 1) * (F.bp (F.a k f) (F.a k f)
          + F.bp (F.a (-k) f) (F.a (-k) f) + F.bp (F.aDag k f) (F.aDag k f)
          + F.bp (F.aDag (-k) f) (F.aDag (-k) f) + F.bp f f)) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hper k) (by norm_num)
  -- the two sums `P = Σ‖a_k f‖²` and `R = Σ‖a_k† f‖²`
  have hP : (∑ k : Mode, F.bp (F.a k f) (F.a k f))
      = F.bp ((∑ k : Mode, F.nOp k) f) f := (bp_nOp_sum_eq F f).symm
  have hR : (∑ k : Mode, F.bp (F.aDag k f) (F.aDag k f))
      = (∑ k : Mode, F.bp (F.a k f) (F.a k f)) + (∑ k : Mode, F.ccrK k k) * F.bp f f := by
    simpa only [FockData.normSq] using sum_normSq_aDag_eq F f
  have hPle : (∑ k : Mode, F.bp (F.a k f) (F.a k f)) ≤ 16 * (E.bigM * F.bp f f) := by
    rw [hP]
    have hNle : F.bp (T.N f) f ≤ E.bigM * F.bp f f :=
      Work.BoseB7A.NWindow_bp_N_le F T hbigM hf
    have hNnn : 0 ≤ F.bp (T.N f) f := T.N_nonneg f
    have h1 : F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f := hBessel f
    have h2 : Cn * F.bp (T.N f) f ≤ max Cn 0 * F.bp (T.N f) f :=
      mul_le_mul_of_nonneg_right (le_max_left Cn 0) hNnn
    have h3 : max Cn 0 * F.bp (T.N f) f ≤ 16 * F.bp (T.N f) f :=
      mul_le_mul_of_nonneg_right (max_le hCn (by norm_num)) hNnn
    have h4 : 16 * F.bp (T.N f) f ≤ 16 * (E.bigM * F.bp f f) :=
      mul_le_mul_of_nonneg_left hNle (by norm_num)
    linarith [h1, h2, h3, h4]
  have hccr : (∑ k : Mode, F.ccrK k k) ≤ (Fintype.card Mode : ℝ) :=
    sum_ccrK_diag_le_card F fun k => hnum.hccr k
  have hRle : (∑ k : Mode, F.bp (F.aDag k f) (F.aDag k f))
      ≤ 16 * (E.bigM * F.bp f f) + (Fintype.card Mode : ℝ) * F.bp f f := by
    rw [hR]
    have h5 : (∑ k : Mode, F.ccrK k k) * F.bp f f ≤ (Fintype.card Mode : ℝ) * F.bp f f :=
      mul_le_mul_of_nonneg_right hccr hz
    linarith [hPle, h5]
  -- evaluate the sum
  have hsum : (∑ k : Mode, (1 / 2 : ℝ) * (3 * (A + C + 1) * (F.bp (F.a k f) (F.a k f)
        + F.bp (F.a (-k) f) (F.a (-k) f) + F.bp (F.aDag k f) (F.aDag k f)
        + F.bp (F.aDag (-k) f) (F.aDag (-k) f) + F.bp f f)))
      = (1 / 2) * (3 * (A + C + 1)) * (2 * (∑ k : Mode, F.bp (F.a k f) (F.a k f))
          + 2 * (∑ k : Mode, F.bp (F.aDag k f) (F.aDag k f))
          + (Fintype.card Mode : ℝ) * F.bp f f) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    rw [sum_neg_index (fun k => F.bp (F.a k f) (F.a k f)),
      sum_neg_index (fun k => F.bp (F.aDag k f) (F.aDag k f))]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  -- the arithmetic
  have hkey : 2 * (∑ k : Mode, F.bp (F.a k f) (F.a k f))
        + 2 * (∑ k : Mode, F.bp (F.aDag k f) (F.aDag k f)) + (Fintype.card Mode : ℝ) * F.bp f f
      ≤ 67 * ((E.bigM + 1) * ((Fintype.card Mode : ℝ) + 1) * F.bp f f) := by
    have h2P : 2 * (∑ k : Mode, F.bp (F.a k f) (F.a k f)) ≤ 32 * E.bigM * F.bp f f := by
      linarith [hPle]
    have h2R : 2 * (∑ k : Mode, F.bp (F.aDag k f) (F.aDag k f))
        ≤ 32 * E.bigM * F.bp f f + 2 * (Fintype.card Mode : ℝ) * F.bp f f := by
      linarith [hRle]
    have hMle : E.bigM ≤ (E.bigM + 1) * ((Fintype.card Mode : ℝ) + 1) := by
      nlinarith [hbigM, hcard]
    have hNle : (Fintype.card Mode : ℝ) ≤ (E.bigM + 1) * ((Fintype.card Mode : ℝ) + 1) := by
      nlinarith [hbigM, hcard]
    have eM : E.bigM * F.bp f f
        ≤ (E.bigM + 1) * ((Fintype.card Mode : ℝ) + 1) * F.bp f f := by
      have h := mul_le_mul_of_nonneg_right hMle hz
      linarith [h]
    have eN : (Fintype.card Mode : ℝ) * F.bp f f
        ≤ (E.bigM + 1) * ((Fintype.card Mode : ℝ) + 1) * F.bp f f := by
      have h := mul_le_mul_of_nonneg_right hNle hz
      linarith [h]
    have e1 : 32 * E.bigM * F.bp f f
        ≤ 32 * ((E.bigM + 1) * ((Fintype.card Mode : ℝ) + 1) * F.bp f f) := by
      have h := mul_le_mul_of_nonneg_left eM (by norm_num : (0 : ℝ) ≤ 32)
      linarith [h]
    have e2 : 2 * (Fintype.card Mode : ℝ) * F.bp f f
        ≤ 2 * ((E.bigM + 1) * ((Fintype.card Mode : ℝ) + 1) * F.bp f f) := by
      have h := mul_le_mul_of_nonneg_left eN (by norm_num : (0 : ℝ) ≤ 2)
      linarith [h]
    linarith [h2P, h2R, e1, e2, eN]
  have hsum_le : (∑ k : Mode, (1 / 2 : ℝ) * (3 * (A + C + 1) * (F.bp (F.a k f) (F.a k f)
        + F.bp (F.a (-k) f) (F.a (-k) f) + F.bp (F.aDag k f) (F.aDag k f)
        + F.bp (F.aDag (-k) f) (F.aDag (-k) f) + F.bp f f))) ≤ Kbar * F.bp f f := by
    rw [hsum]
    have hAAC : 0 ≤ A + C + 1 := by linarith
    have h67 : (1 / 2 : ℝ) * (3 * (A + C + 1)) * (2 * (∑ k : Mode, F.bp (F.a k f) (F.a k f))
          + 2 * (∑ k : Mode, F.bp (F.aDag k f) (F.aDag k f))
          + (Fintype.card Mode : ℝ) * F.bp f f)
        ≤ (1 / 2 : ℝ) * (3 * (A + C + 1)) * (67 * ((E.bigM + 1)
            * ((Fintype.card Mode : ℝ) + 1) * F.bp f f)) :=
      mul_le_mul_of_nonneg_left hkey (by linarith)
    have hfin : (1 / 2 : ℝ) * (3 * (A + C + 1)) * (67 * ((E.bigM + 1)
          * ((Fintype.card Mode : ℝ) + 1) * F.bp f f))
        ≤ 10 ^ 6 * (A + C + 1) * (E.bigM + 1) * ((Fintype.card Mode : ℝ) + 1) * F.bp f f := by
      have h1 : (1 / 2 : ℝ) * (3 * (A + C + 1)) * 67 ≤ 10 ^ 6 * (A + C + 1) := by
        nlinarith [hAAC]
      have hV0 : 0 ≤ (E.bigM + 1) * ((Fintype.card Mode : ℝ) + 1) * F.bp f f := by positivity
      calc (1 / 2 : ℝ) * (3 * (A + C + 1)) * (67 * ((E.bigM + 1)
              * ((Fintype.card Mode : ℝ) + 1) * F.bp f f))
          = ((1 / 2 : ℝ) * (3 * (A + C + 1)) * 67) * ((E.bigM + 1)
              * ((Fintype.card Mode : ℝ) + 1) * F.bp f f) := by ring
        _ ≤ (10 ^ 6 * (A + C + 1)) * ((E.bigM + 1) * ((Fintype.card Mode : ℝ) + 1)
              * F.bp f f) := mul_le_mul_of_nonneg_right h1 hV0
        _ = 10 ^ 6 * (A + C + 1) * (E.bigM + 1) * ((Fintype.card Mode : ℝ) + 1) * F.bp f f := by
              ring
    exact le_trans (le_trans h67 hfin) (mul_le_mul_of_nonneg_right hKbig hz)
  exact le_trans hs1 hsum_le

end

end Work.BoseBogFS
