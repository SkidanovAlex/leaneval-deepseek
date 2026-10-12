import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.Est1.ComZDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.Est1.ComZ` — the analysis of the `χ̂²` half

This module proves the inequalities of the `χ̂²` half `Est1.estT2sum_comZ`
(FS `eq:EstimT2comm`): the split of `T2ComF` (`Est1.t2com_split`) is bounded by
the `Ã`-form `FA` (`Est1.FA`) plus the two errors (`wc`-deviation and the
`χ̂(s-k)χ̂(s'-k)` term), and `FA` is compared with `⟨G Φ⟩` and the two moments
`⟨n₊⟩`, `‖Φ‖²`.

## Contents

* `two_abs_bp_le` — AM–GM for the Fock form.
* `sum_excited_neg` — the reindexing `s ↦ -s` on the excited modes.
* `sum_fL_le_NPL` — `Σ_{s}f_L(s) ≤ NPL`.
* `TA_le_N` — `TA ≤ ⟨n₊⟩`.
* `TB_le` — `TB ≤ TA + NPL·‖Φ‖²`.
* `AbsA0_le` — `Σ f_Lf_L'|⟨Ã_s,Ã_{s'}⟩| ≤ NPL·Σ f_L‖Ã_s‖²`.
* `sum_hatChiSq_shift` — `Σ_{s'}|χ̂²(s'-s)| ≤ K₀+1`.
* `sum_Atil_sq_le` — `Σ f_L‖Ã_{s,k}Φ‖² ≤ 2TA + 2β²TB`.
* `FA_PSD`, `FA_le_Q` — positivity of `FA` and the comparison with `⟨G Φ⟩`.
* `rawY_bound` — the `χ̂(s-k)χ̂(s'-k)` error.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

namespace Est1

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The Fock form -/

/-- **AM–GM for the Fock form**: `2|⟨u,v⟩| ≤ ‖u‖² + ‖v‖²`. -/
theorem two_abs_bp_le (F : FockData Mode) (u v : F.H) :
    2 * |F.bp u v| ≤ F.bp u u + F.bp v v := by
  have h1 : F.bp u v ≤ (F.bp u u + F.bp v v) / 2 := by
    have h := bp_cauchy F (ε := 1) one_pos u v
    simp only [one_mul, inv_one] at h
    linarith
  have h2 : -(F.bp u v) ≤ (F.bp u u + F.bp v v) / 2 := by
    have h := bp_cauchy F (ε := 1) one_pos u (-v)
    have e1 : F.bp u (-v) = -F.bp u v := map_neg (F.bp u) v
    have e2 : F.bp (-v) (-v) = F.bp v v := by
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
    rw [e1, e2, one_mul, inv_one] at h
    linarith
  have h3 : |F.bp u v| ≤ (F.bp u u + F.bp v v) / 2 :=
    abs_le.mpr ⟨by linarith, h1⟩
  linarith

/-! ## 2. The excited modes under `s ↦ -s` -/

/-- The reindexing `Σ_{s∈excited}g(-s) = Σ_{s∈excited}g(s)`: `s ↦ -s` is an
involution of the excited modes (`-s = 0 ↔ s = 0`). -/
theorem sum_excited_neg (g : Mode → ℝ) :
    (∑ s ∈ excited Mode, g (-s)) = ∑ s ∈ excited Mode, g s := by
  refine Finset.sum_equiv (Equiv.neg Mode) ?_ ?_
  · intro i
    simp only [Equiv.neg_apply, excited, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro h; simpa using h
    · intro h; simpa using h
  · intro i _
    rfl

/-- `NPL` is the number of modes in the support of `f_L`. -/
theorem NPL_nonneg (E : Q3Env Mode) : 0 ≤ NPL E := by
  rw [NPL]; exact_mod_cast Nat.zero_le _

/-- `Σ_{s∈excited}f_L(s) ≤ NPL`: the support count. -/
theorem sum_fL_le_NPL {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) :
    (∑ s ∈ excited Mode, E.fL s) ≤ NPL E := by
  have h1 : (∑ s ∈ excited Mode, E.fL s)
      = ∑ s ∈ (excited Mode).filter (fun s => E.fL s ≠ 0), E.fL s := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : E.fL s = 0
    · simp [h]
    · simp [h]
  rw [h1, NPL]
  calc ∑ s ∈ (excited Mode).filter (fun s => E.fL s ≠ 0), E.fL s
      ≤ ∑ s ∈ (excited Mode).filter (fun s => E.fL s ≠ 0), (1 : ℝ) :=
        Finset.sum_le_sum fun s _ => hK.fL_le_one s
    _ = (((excited Mode).filter (fun s => E.fL s ≠ 0)).card : ℝ) := by simp

/-! ## 3. The two moments -/

/-- `TA ≤ ⟨Φ, n₊Φ⟩` (each `ã_s` with `s ≠ 0` counts at most once and
`f_L ≤ 1`). -/
theorem TA_le_N {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (Φ : F.H) :
    TA F T E Φ ≤ F.bp (T.N Φ) Φ := by
  have hle : ∀ s ∈ excited Mode, E.fL s * F.bp (T.ta s Φ) (T.ta s Φ)
      ≤ F.bp (T.ta s Φ) (T.ta s Φ) := fun s _ =>
    mul_le_of_le_one_left (F.bp_nonneg _) (hK.fL_le_one s)
  calc TA F T E Φ = ∑ s ∈ excited Mode, E.fL s * F.bp (T.ta s Φ) (T.ta s Φ) := rfl
    _ ≤ ∑ s ∈ excited Mode, F.bp (T.ta s Φ) (T.ta s Φ) := Finset.sum_le_sum hle
    _ = F.bp ((∑ s ∈ excited Mode, T.taDag s ∘ₗ T.ta s) Φ) Φ := by
        simp only [map_sum, LinearMap.sum_apply, LinearMap.comp_apply, bp_taDag_left]
    _ ≤ F.bp (T.N Φ) Φ :=
        T.ta_le_N (excited Mode) (fun s hs => (Finset.mem_erase.mp hs).1) Φ

/-- `TB ≤ TA + NPL·‖Φ‖²`: `ã_{-s}ã_{-s}† = ã_{-s}†ã_{-s} + 1` (`s ≠ 0`),
`f_L` is even and `Σ f_L ≤ NPL`. -/
theorem TB_le {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (Φ : F.H) :
    TB F T E Φ ≤ TA F T E Φ + NPL E * F.normSq Φ := by
  have hpt : ∀ s ∈ excited Mode,
      F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ)
        = F.bp (T.ta (-s) Φ) (T.ta (-s) Φ) + F.bp Φ Φ := by
    intro s hs
    have hsne : s ≠ 0 := (Finset.mem_erase.mp hs).1
    have hne : -s ≠ 0 := by simpa using hsne
    have hcomm := LinearMap.congr_fun (T.ta_ccr (-s) (-s) hne hne) Φ
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, if_true, one_smul] at hcomm
    calc F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ)
        = F.bp Φ (T.ta (-s) (T.taDag (-s) Φ)) :=
          T.taDag_adjoint (-s) Φ (T.taDag (-s) Φ)
      _ = F.bp Φ (T.taDag (-s) (T.ta (-s) Φ) + Φ) := by rw [hcomm]
      _ = F.bp Φ (T.taDag (-s) (T.ta (-s) Φ)) + F.bp Φ Φ := map_add _ _ _
      _ = F.bp (T.ta (-s) Φ) (T.ta (-s) Φ) + F.bp Φ Φ := by
            rw [F.bp_symm Φ (T.taDag (-s) (T.ta (-s) Φ)),
              T.taDag_adjoint (-s) (T.ta (-s) Φ) Φ]
  have hreindex : (∑ s ∈ excited Mode, E.fL s * F.bp (T.ta (-s) Φ) (T.ta (-s) Φ))
      = ∑ s ∈ excited Mode, E.fL s * F.bp (T.ta s Φ) (T.ta s Φ) := by
    refine Finset.sum_equiv (Equiv.neg Mode) ?_ ?_
    · intro i
      simp only [Equiv.neg_apply, excited, Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro h; simpa using h
      · intro h; simpa using h
    · intro i _
      simp only [Equiv.neg_apply]
      rw [hK.fL_even i]
  have hstep : TB F T E Φ
      = (∑ s ∈ excited Mode, E.fL s * F.bp (T.ta (-s) Φ) (T.ta (-s) Φ))
          + (∑ s ∈ excited Mode, E.fL s) * F.bp Φ Φ := by
    rw [TB]
    rw [show (∑ s ∈ excited Mode,
          E.fL s * F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))
        = ∑ s ∈ excited Mode,
          E.fL s * (F.bp (T.ta (-s) Φ) (T.ta (-s) Φ) + F.bp Φ Φ) from
      Finset.sum_congr rfl fun s hs => by rw [hpt s hs]]
    rw [show (∑ s ∈ excited Mode,
          E.fL s * (F.bp (T.ta (-s) Φ) (T.ta (-s) Φ) + F.bp Φ Φ))
        = ∑ s ∈ excited Mode, (E.fL s * F.bp (T.ta (-s) Φ) (T.ta (-s) Φ)
            + E.fL s * F.bp Φ Φ) from
      Finset.sum_congr rfl fun s _ => by ring]
    rw [Finset.sum_add_distrib, Finset.sum_mul]
  rw [hstep, hreindex, TA, Work.BoseB7.FockData.normSq]
  have hfl := sum_fL_le_NPL (F := F) (T := T) (E := E) hK
  have hnn : 0 ≤ F.bp Φ Φ := F.bp_nonneg Φ
  nlinarith

/-! ## 4. The absolute value of the `Ã`-form -/

/-- The elementary identity behind `AbsA0_le`: for `a ≥ 0`,
`Σ_{s,s'}a_sa_{s'}(b_s+b_{s'})/2 = (Σ_sa_s)(Σ_sa_sb_s)`. -/
private theorem sum_sum_amgm (S : Finset Mode) (a b : Mode → ℝ) :
    (∑ s ∈ S, ∑ s' ∈ S, a s * a s' * ((b s + b s') / 2))
      = (∑ s ∈ S, a s) * (∑ s ∈ S, a s * b s) := by
  have e1 : (∑ s ∈ S, ∑ s' ∈ S, a s * a s' * (b s / 2))
      = (1 / 2) * ((∑ s ∈ S, a s * b s) * (∑ s' ∈ S, a s')) := by
    rw [show (∑ s ∈ S, ∑ s' ∈ S, a s * a s' * (b s / 2))
        = (1 / 2) * (∑ s ∈ S, ∑ s' ∈ S, a s * b s * a s') from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring]
    rw [Finset.sum_mul_sum]
  have e2 : (∑ s ∈ S, ∑ s' ∈ S, a s * a s' * (b s' / 2))
      = (1 / 2) * ((∑ s ∈ S, a s) * (∑ s' ∈ S, a s' * b s')) := by
    rw [show (∑ s ∈ S, ∑ s' ∈ S, a s * a s' * (b s' / 2))
        = (1 / 2) * (∑ s ∈ S, ∑ s' ∈ S, a s * (a s' * b s')) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring]
    rw [Finset.sum_mul_sum]
  rw [show (∑ s ∈ S, ∑ s' ∈ S, a s * a s' * ((b s + b s') / 2))
      = (∑ s ∈ S, ∑ s' ∈ S, a s * a s' * (b s / 2))
        + (∑ s ∈ S, ∑ s' ∈ S, a s * a s' * (b s' / 2)) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring]
  rw [e1, e2]
  ring

/-- `Σ_{s,s'}f_L(s)f_L(s')|⟨Ã_sΦ,Ã_{s'}Φ⟩| ≤ (Σ f_L)·Σ_sf_L(s)‖Ã_sΦ‖²`. -/
theorem AbsA0_le {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (k : Mode) (Φ : F.H) :
    AbsA0 F T E k Φ ≤ (∑ s ∈ excited Mode, E.fL s) *
      (∑ s ∈ excited Mode, E.fL s * F.bp (Atil F T E s k Φ) (Atil F T E s k Φ)) := by
  have hpt : ∀ s ∈ excited Mode, ∀ s' ∈ excited Mode,
      E.fL s * E.fL s' * |F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)|
        ≤ E.fL s * E.fL s' *
            ((F.bp (Atil F T E s k Φ) (Atil F T E s k Φ)
              + F.bp (Atil F T E s' k Φ) (Atil F T E s' k Φ)) / 2) := by
    intro s _ s' _
    have h1 := two_abs_bp_le F (Atil F T E s k Φ) (Atil F T E s' k Φ)
    have h2 : 0 ≤ E.fL s * E.fL s' := mul_nonneg (hK.fL_nonneg s) (hK.fL_nonneg s')
    nlinarith
  calc AbsA0 F T E k Φ
      = ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * |F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)| := rfl
    _ ≤ ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' *
            ((F.bp (Atil F T E s k Φ) (Atil F T E s k Φ)
              + F.bp (Atil F T E s' k Φ) (Atil F T E s' k Φ)) / 2) :=
        Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun s' hs' => hpt s hs s' hs'
    _ = (∑ s ∈ excited Mode, E.fL s) *
          (∑ s ∈ excited Mode, E.fL s * F.bp (Atil F T E s k Φ) (Atil F T E s k Φ)) :=
        sum_sum_amgm (excited Mode) E.fL (fun s => F.bp (Atil F T E s k Φ) (Atil F T E s k Φ))

/-! ## 5. Positivity of `FA` -/

/-- `FA ≥ 0`: the PSD half of `Q3Kernel.hatChiSq_form` with `c = f_L` and
`v s = Ã_{s,k}Φ`. -/
theorem FA_nonneg {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (k : Mode) (Φ : F.H) : 0 ≤ FA F T E k Φ := by
  have hform := (hK.hatChiSq_form (excited Mode) E.fL (fun s => Atil F T E s k Φ)
    (fun s hs => (Finset.mem_erase.mp hs).1)).1
  have heq : (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * E.hatChiSq (s' - s) *
          F.bp (Atil F T E s' k Φ) (Atil F T E s k Φ))
      = FA F T E k Φ := by
    rw [FA]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [F.bp_symm]
  rwa [heq] at hform

/-! ## 6. The `Ã`-moment and the two errors -/

/-- `bm ≥ 0`. -/
theorem bm_nonneg {K₀ : ℝ} {E : Q3Env Mode} (hK0 : 0 ≤ K₀) : 0 ≤ bm K₀ E := by
  rw [bm]
  positivity

/-- `devc ≥ 0`. -/
theorem devc_nonneg {K₀ : ℝ} {E : Q3Env Mode} (hK0 : 0 ≤ K₀) : 0 ≤ devc K₀ E := by
  rw [devc]
  positivity

/-- `2b⟨u,v⟩ ≤ |b|(‖u‖² + ‖v‖²)`: Cauchy–Schwarz in the form used for the
`Ã`-moment. -/
theorem two_mul_bp_le (F : FockData Mode) (b : ℝ) (u v : F.H) :
    2 * b * F.bp u v ≤ |b| * (F.bp u u + F.bp v v) := by
  have hsqrt : 2 * (Real.sqrt (F.bp u u) * Real.sqrt (F.bp v v))
      ≤ F.bp u u + F.bp v v := by
    have hu := F.bp_nonneg u
    have hv := F.bp_nonneg v
    have h := sq_nonneg (Real.sqrt (F.bp u u) - Real.sqrt (F.bp v v))
    rw [sub_sq, Real.sq_sqrt hu, Real.sq_sqrt hv] at h
    ring_nf at h
    linarith
  have h1 : 2 * b * F.bp u v ≤ 2 * |b| * |F.bp u v| := by
    have h := le_abs_self (2 * b * F.bp u v)
    have he : |2 * b * F.bp u v| = 2 * |b| * |F.bp u v| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rwa [he] at h
  have h2 : 2 * |b| * |F.bp u v|
      ≤ 2 * |b| * (Real.sqrt (F.bp u u) * Real.sqrt (F.bp v v)) := by
    have := bp_cauchy_abs F u v
    nlinarith [abs_nonneg b]
  have h3 : 2 * |b| * (Real.sqrt (F.bp u u) * Real.sqrt (F.bp v v))
      ≤ |b| * (F.bp u u + F.bp v v) := by
    have hb := abs_nonneg b
    nlinarith [hsqrt, hb]
  linarith

/-- `Σ_sf_L(s)‖Ã_{s,k}Φ‖² ≤ (1 + β_m + β_m²)(TA + TB)`, where `β_m` bounds
`|bA E s k| = |α_kα_{s-k}|` on the support of `f_L`.

(`Ã_sΦ = ã_sΦ + β_s ã_{-s}†Φ`, `Δ = (1+β_m+β_m²)(U+V) ≥ |β_s|(U+V) + |β_s|²V`.) -/
theorem sum_Atil_sq_le {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (k : Mode) (Φ : F.H)
    (hbm : ∀ s, E.fL s ≠ 0 → |bA E s k| ≤ bm K₀ E) :
    (∑ s ∈ excited Mode, E.fL s * F.bp (Atil F T E s k Φ) (Atil F T E s k Φ))
      ≤ (1 + bm K₀ E) * TA F T E Φ + (bm K₀ E + (bm K₀ E) ^ 2) * TB F T E Φ := by
  have hpt : ∀ s ∈ excited Mode,
      E.fL s * F.bp (Atil F T E s k Φ) (Atil F T E s k Φ)
        ≤ E.fL s * ((1 + bm K₀ E) * F.bp (T.ta s Φ) (T.ta s Φ)
            + (bm K₀ E + (bm K₀ E) ^ 2) * F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ)) := by
    intro s hs
    have hfl : 0 ≤ E.fL s := hK.fL_nonneg s
    have hU : 0 ≤ F.bp (T.ta s Φ) (T.ta s Φ) := F.bp_nonneg _
    have hV : 0 ≤ F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ) := F.bp_nonneg _
    by_cases h0 : E.fL s = 0
    · rw [h0]; simp
    · have hβ : |bA E s k| ≤ bm K₀ E := hbm s h0
      have hβ0 : 0 ≤ bm K₀ E := le_trans (abs_nonneg _) hβ
      have hβ2 : (bA E s k) ^ 2 ≤ (bm K₀ E) ^ 2 := by
        nlinarith [abs_nonneg (bA E s k), sq_abs (bA E s k), hβ, hβ0]
      have hexp : F.bp (Atil F T E s k Φ) (Atil F T E s k Φ)
          = F.bp (T.ta s Φ) (T.ta s Φ)
            + 2 * (bA E s k) * F.bp (T.ta s Φ) (T.taDag (-s) Φ)
            + (bA E s k) ^ 2 * F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ) := by
        have hA : Atil F T E s k Φ = T.ta s Φ + (bA E s k) • T.taDag (-s) Φ := rfl
        rw [hA]
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [F.bp_symm (T.taDag (-s) Φ) (T.ta s Φ)]
        ring
      have hmix := two_mul_bp_le F (bA E s k) (T.ta s Φ) (T.taDag (-s) Φ)
      have hfin : F.bp (Atil F T E s k Φ) (Atil F T E s k Φ)
          ≤ (1 + bm K₀ E) * F.bp (T.ta s Φ) (T.ta s Φ)
            + (bm K₀ E + (bm K₀ E) ^ 2) * F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ) := by
        rw [hexp]
        nlinarith [hmix, hβ, hβ2, hU, hV, hβ0]
      exact mul_le_mul_of_nonneg_left hfin hfl
  calc (∑ s ∈ excited Mode, E.fL s * F.bp (Atil F T E s k Φ) (Atil F T E s k Φ))
      ≤ ∑ s ∈ excited Mode, E.fL s * ((1 + bm K₀ E) * F.bp (T.ta s Φ) (T.ta s Φ)
          + (bm K₀ E + (bm K₀ E) ^ 2) * F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ)) :=
        Finset.sum_le_sum hpt
    _ = (1 + bm K₀ E) * TA F T E Φ + (bm K₀ E + (bm K₀ E) ^ 2) * TB F T E Φ := by
        rw [TA, TB, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring


/-! ## 7. The `Ã`-vs-`ã` comparison and the two error terms -/

/-- `|a·c·χ| ≤ a·M·N` for `a ≥ 0`, `|c| ≤ M`, `|χ| ≤ N`. -/
theorem abs_mul_le_mul (a : ℝ) (ha : 0 ≤ a) (c χ M N : ℝ) (hc : |c| ≤ M) (hχ : |χ| ≤ N)
    (hM : 0 ≤ M) : |a * c * χ| ≤ a * M * N := by
  rw [abs_mul, abs_mul, abs_of_nonneg ha]
  calc (a * |c|) * |χ| ≤ (a * M) * N :=
        mul_le_mul (mul_le_mul_of_nonneg_left hc ha) hχ (abs_nonneg _) (mul_nonneg ha hM)

/-- `rawA - FA ≤ C_dev·AbsA0` (the `wc`-deviation). -/
theorem rawA_sub_FA_le {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (k : Mode) (Φ : F.H) (hdev0 : 0 ≤ devc K₀ E)
    (hdev : ∀ s s', E.fL s ≠ 0 → E.fL s' ≠ 0 → |wc E k s s' - 1| ≤ devc K₀ E) :
    rawA F T E k Φ - FA F T E k Φ ≤ devc K₀ E * AbsA0 F T E k Φ := by
  have h1 : rawA F T E k Φ - FA F T E k Φ
      = ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * (wc E k s s' - 1) * E.hatChiSq (s' - s) *
            F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ) := by
    rw [rawA, FA, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring
  rw [h1]
  calc ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * (wc E k s s' - 1) * E.hatChiSq (s' - s) *
            F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)
      ≤ ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * devc K₀ E *
            |F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)| := by
        refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun s' _ => ?_
        by_cases h0 : E.fL s = 0
        · rw [h0]; simp
        · by_cases h0' : E.fL s' = 0
          · rw [h0']; simp
          · have hfl0 : 0 ≤ E.fL s := hK.fL_nonneg s
            have hfl1 : 0 ≤ E.fL s' := hK.fL_nonneg s'
            have hχ : |E.hatChiSq (s' - s)| ≤ 1 := hK.hatChiSq_le _
            have hw : |wc E k s s' - 1| ≤ devc K₀ E := hdev s s' h0 h0'
            have hb1 : |E.fL s * E.fL s' * (wc E k s s' - 1) * E.hatChiSq (s' - s)|
                ≤ (E.fL s * E.fL s') * devc K₀ E * 1 :=
              abs_mul_le_mul (E.fL s * E.fL s') (mul_nonneg hfl0 hfl1)
                (wc E k s s' - 1) (E.hatChiSq (s' - s)) (devc K₀ E) 1 hw hχ hdev0
            simp only [mul_one] at hb1
            calc E.fL s * E.fL s' * (wc E k s s' - 1) * E.hatChiSq (s' - s)
                  * F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)
                ≤ |E.fL s * E.fL s' * (wc E k s s' - 1) * E.hatChiSq (s' - s)
                    * F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)| := le_abs_self _
              _ = |E.fL s * E.fL s' * (wc E k s s' - 1) * E.hatChiSq (s' - s)|
                    * |F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)| := by rw [abs_mul]
              _ ≤ (E.fL s * E.fL s' * devc K₀ E)
                    * |F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)| :=
                    mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
    _ = devc K₀ E * AbsA0 F T E k Φ := by
        rw [AbsA0, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        ring

/-- `-rawY ≤ (1+C_dev)K₀²η²·AbsA0` (the `χ̂(s-k)χ̂(s'-k)` error). -/
theorem rawY_bound {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (k : Mode) (Φ : F.H) (hK0 : 0 ≤ K₀) (hη : 0 ≤ eta E)
    (hdev0 : 0 ≤ devc K₀ E)
    (hχ : ∀ s, E.fL s ≠ 0 → |E.hatChi (s - k)| ≤ K₀ * eta E)
    (hdev : ∀ s s', E.fL s ≠ 0 → E.fL s' ≠ 0 → |wc E k s s' - 1| ≤ devc K₀ E) :
    -rawY F T E k Φ
      ≤ (1 + devc K₀ E) * (K₀ ^ 2 * eta E ^ 2) * AbsA0 F T E k Φ := by
  have hKη : 0 ≤ K₀ * eta E := mul_nonneg hK0 hη
  have h1 : -rawY F T E k Φ
      ≤ ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          ((E.fL s * E.fL s') * (1 + devc K₀ E) * (K₀ ^ 2 * eta E ^ 2)) *
            |F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)| := by
    rw [rawY, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun s' _ => ?_
    refine (neg_le_abs _).trans ?_
    by_cases h0 : E.fL s = 0
    · rw [h0]; simp
    · by_cases h0' : E.fL s' = 0
      · rw [h0']; simp
      · have hfl0 : 0 ≤ E.fL s := hK.fL_nonneg s
        have hfl1 : 0 ≤ E.fL s' := hK.fL_nonneg s'
        have hχs : |E.hatChi (s - k)| ≤ K₀ * eta E := hχ s h0
        have hχs' : |E.hatChi (s' - k)| ≤ K₀ * eta E := hχ s' h0'
        have hw : |wc E k s s'| ≤ 1 + devc K₀ E := by
          have hh : |wc E k s s' - 1| ≤ devc K₀ E := hdev s s' h0 h0'
          have h3 : wc E k s s' ≤ 1 + devc K₀ E := by
            linarith [le_abs_self (wc E k s s' - 1)]
          have h4 : -(wc E k s s') ≤ 1 + devc K₀ E := by
            linarith [neg_le_abs (wc E k s s' - 1)]
          exact abs_le.mpr ⟨by linarith, h3⟩
        have hχχ : |E.hatChi (s - k) * E.hatChi (s' - k)| ≤ K₀ ^ 2 * eta E ^ 2 := by
          rw [abs_mul]
          calc |E.hatChi (s - k)| * |E.hatChi (s' - k)|
              ≤ (K₀ * eta E) * (K₀ * eta E) :=
                mul_le_mul hχs hχs' (abs_nonneg _) hKη
            _ = K₀ ^ 2 * eta E ^ 2 := by ring
        have hb1 : |E.fL s * E.fL s' * wc E k s s'
              * (E.hatChi (s - k) * E.hatChi (s' - k))|
            ≤ (E.fL s * E.fL s') * (1 + devc K₀ E) * (K₀ ^ 2 * eta E ^ 2) :=
          abs_mul_le_mul (E.fL s * E.fL s') (mul_nonneg hfl0 hfl1)
            (wc E k s s') (E.hatChi (s - k) * E.hatChi (s' - k))
            (1 + devc K₀ E) (K₀ ^ 2 * eta E ^ 2) hw hχχ (by linarith)
        calc |E.fL s * E.fL s' * wc E k s s'
              * (E.hatChi (s - k) * E.hatChi (s' - k))
              * F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)|
            = |E.fL s * E.fL s' * wc E k s s'
                * (E.hatChi (s - k) * E.hatChi (s' - k))|
                * |F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)| := by rw [abs_mul]
          _ ≤ ((E.fL s * E.fL s') * (1 + devc K₀ E) * (K₀ ^ 2 * eta E ^ 2))
                * |F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)| :=
                mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
  calc -rawY F T E k Φ
      ≤ ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          ((E.fL s * E.fL s') * (1 + devc K₀ E) * (K₀ ^ 2 * eta E ^ 2)) *
            |F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)| := h1
    _ = ((1 + devc K₀ E) * (K₀ ^ 2 * eta E ^ 2)) * AbsA0 F T E k Φ := by
        rw [AbsA0, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        ring

/-! ## 8. The `k`-sum `Λ = Σ_{k∈P_H}wgt k` -/

/-- `Λ = Σ_{k∈P_H}wgt k = 2ρ_zΞ/(1-𝓁²)`. -/
theorem wsum_eq {F : FockData Mode} {E : Q3Env Mode}
    (hℓ : 0 < E.ell) (hden : 1 - E.lille ^ 2 ≠ 0)
    (hDne : ∀ k ∈ F.PHset E, E.D k ≠ 0) :
    wsum F E = 2 * E.rho * Xi F E / (1 - E.lille ^ 2) := by
  have hEll : E.ell ^ 3 * E.ell ^ (-(3 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast E.ell 3, ← Real.rpow_add hℓ]
    norm_num
  have hbody : ∀ k : Mode, wgt E k
      = (E.rho * (E.ell ^ 3)⁻¹)
          * ((1 - E.lille ^ 2)⁻¹ * (E.W1 k ^ 2 * (E.D k)⁻¹)) := by
    intro k
    simp only [wgt, cD, Q3Env.rho, rhoZ]
    rw [div_eq_mul_inv, mul_inv_rev]
    ring
  have h2 : (∑ k ∈ F.PHset E, E.W1 k ^ 2 / (2 * E.D k)) = E.ell ^ 3 * Xi F E := by
    rw [Xi, ← mul_assoc, hEll, one_mul]
  have h3 : (∑ k ∈ F.PHset E, E.W1 k ^ 2 * (E.D k)⁻¹) = 2 * (E.ell ^ 3 * Xi F E) := by
    rw [← h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkne : E.D k ≠ 0 := hDne k hk
    rw [div_eq_mul_inv, mul_inv_rev]
    field_simp
  rw [wsum, Finset.sum_congr rfl (fun k _ => hbody k)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [h3]
  rw [div_eq_mul_inv]
  field_simp


/-! ## 9. The `wc`-deviation -/

/-- The normal form of `wc`: `(1-α_{s-k}α_{s'-k})/((1-α_k²)²(1-α_{s-k}²)(1-α_{s'-k}²))`. -/
theorem wc_form (E : Q3Env Mode) (k s s' : Mode) :
    wc E k s s' = (1 - E.alpha (s - k) * E.alpha (s' - k)) /
      ((1 - E.alpha k ^ 2) ^ 2 * (1 - E.alpha (s - k) ^ 2)
        * (1 - E.alpha (s' - k) ^ 2)) := by
  simp only [wc, Q3Env.q3Denom]
  simp only [div_eq_mul_inv, mul_inv_rev]
  rw [← inv_pow]
  ring

/-- The scalar deviation: for `|x|,|u|,|v| ≤ X ≤ 2/3`,
`|(1-uv)/((1-x²)²(1-u²)(1-v²)) - 1| ≤ 2²⁰X²`. -/
theorem wc_arith {x u v X : ℝ} (hx : |x| ≤ X) (hu : |u| ≤ X) (hv : |v| ≤ X)
    (hX0 : 0 ≤ X) (hX : X ≤ 2 / 3) :
    |(1 - u * v) / ((1 - x ^ 2) ^ 2 * (1 - u ^ 2) * (1 - v ^ 2)) - 1| ≤ 2 ^ 8 * X ^ 2 := by
  have hx2 : x ^ 2 ≤ X ^ 2 := sq_le_sq.mpr (by rwa [← abs_of_nonneg hX0] at hx)
  have hu2 : u ^ 2 ≤ X ^ 2 := sq_le_sq.mpr (by rwa [← abs_of_nonneg hX0] at hu)
  have hv2 : v ^ 2 ≤ X ^ 2 := sq_le_sq.mpr (by rwa [← abs_of_nonneg hX0] at hv)
  have hX21 : X ^ 2 ≤ 1 := by nlinarith
  have hna : 0 ≤ 1 - X ^ 2 := by linarith
  have hnu : 0 ≤ 1 - u ^ 2 := by linarith
  have hnv : 0 ≤ 1 - v ^ 2 := by linarith
  have hnx2 : 0 ≤ (1 - x ^ 2) ^ 2 := by positivity
  have hnuv : 0 ≤ (1 - u ^ 2) * (1 - v ^ 2) := mul_nonneg hnu hnv
  set D : ℝ := (1 - x ^ 2) ^ 2 * (1 - u ^ 2) * (1 - v ^ 2) with hD
  have hDlo : (1 - X ^ 2) ^ 4 ≤ D := by
    have h1 : (1 - X ^ 2) ^ 2 ≤ (1 - x ^ 2) ^ 2 := by nlinarith
    have h2 : (1 - X ^ 2) * (1 - X ^ 2) ≤ (1 - u ^ 2) * (1 - v ^ 2) :=
      mul_le_mul (by linarith) (by linarith) hna hnu
    rw [hD]
    calc (1 - X ^ 2) ^ 4 = (1 - X ^ 2) ^ 2 * ((1 - X ^ 2) * (1 - X ^ 2)) := by ring
      _ ≤ (1 - x ^ 2) ^ 2 * ((1 - u ^ 2) * (1 - v ^ 2)) :=
          mul_le_mul h1 h2 (mul_nonneg hna hna) hnx2
      _ = (1 - x ^ 2) ^ 2 * (1 - u ^ 2) * (1 - v ^ 2) := by ring
  have hDle : D ≤ 1 := by
    rw [hD, show (1 - x ^ 2) ^ 2 * (1 - u ^ 2) * (1 - v ^ 2)
        = (1 - x ^ 2) ^ 2 * ((1 - u ^ 2) * (1 - v ^ 2)) by ring]
    have h1 : (1 - x ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg x, hx2, hX21]
    have h2 : (1 - u ^ 2) * (1 - v ^ 2) ≤ 1 := by
      nlinarith [sq_nonneg u, sq_nonneg v, hu2, hv2, hX21, sq_nonneg (u * v)]
    calc (1 - x ^ 2) ^ 2 * ((1 - u ^ 2) * (1 - v ^ 2)) ≤ 1 * 1 :=
          mul_le_mul h1 h2 hnuv (by norm_num)
      _ = 1 := by norm_num
  have hDge : (1 : ℝ) / 11 ≤ D := by
    have h81 : ((5 : ℝ) / 9) ^ 4 ≤ (1 - X ^ 2) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) (by nlinarith) 4
    have h54 : ((5 : ℝ) / 9) ^ 4 = 625 / 6561 := by norm_num
    linarith
  have hDpos : 0 < D := by linarith
  have hDinv : 1 / D ≤ 11 := by
    rw [div_le_iff₀ hDpos]
    linarith [hDge]
  have huv : |u * v| ≤ X ^ 2 := by
    rw [abs_mul]
    nlinarith [abs_le.mp hu, abs_le.mp hv, abs_nonneg u, abs_nonneg v, hX0]
  have huva : -(X ^ 2) ≤ u * v := (abs_le.mp huv).1
  have huvb : u * v ≤ X ^ 2 := (abs_le.mp huv).2
  have h1D : 1 - D ≤ 4 * X ^ 2 := by
    have hb : 1 - 4 * X ^ 2 ≤ (1 - X ^ 2) ^ 4 := by
      have h2 : (0 : ℝ) ≤ 6 - 4 * X ^ 2 + (X ^ 2) ^ 2 := by nlinarith [sq_nonneg (X ^ 2 - 2)]
      have h4 : 0 ≤ (X ^ 2) ^ 2 := by positivity
      have hexp : (1 - X ^ 2) ^ 4 - (1 - 4 * X ^ 2)
          = (X ^ 2) ^ 2 * (6 - 4 * X ^ 2 + (X ^ 2) ^ 2) := by ring
      linarith [mul_nonneg h4 h2]
    linarith
  have h1D0 : 0 ≤ 1 - D := by linarith
  have hnum : |1 - u * v - D| ≤ 5 * X ^ 2 := by
    rw [abs_le]
    constructor <;> linarith [huvb, huva, h1D, h1D0]
  have hkey : (1 - u * v) / D - 1 = (1 - u * v - D) / D := by
    field_simp
  rw [show (1 - u * v) / ((1 - x ^ 2) ^ 2 * (1 - u ^ 2) * (1 - v ^ 2))
      = (1 - u * v) / D from by rw [hD]]
  rw [hkey, abs_div, abs_of_pos hDpos]
  calc |1 - u * v - D| / D ≤ 5 * X ^ 2 / D :=
        div_le_div_of_nonneg_right hnum hDpos.le
    _ = 5 * X ^ 2 * (1 / D) := by ring
    _ ≤ 5 * X ^ 2 * 11 := mul_le_mul_of_nonneg_left hDinv (by positivity)
    _ ≤ 2 ^ 8 * X ^ 2 := by nlinarith [sq_nonneg X]

/-- `η > 0` at the parameter point. -/
theorem eta_pos {E : Q3Env Mode} (h : FSParamsView E) : 0 < eta E := by
  rw [Work.BoseB7A.eta_eq E h]
  exact Work.BoseBox.fsXp_pos h.t_pos

/-- **The `wc`-deviation**: `|wc - 1| ≤ C_dev` on the relevant modes. -/
theorem wc_dev (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseB7A.Q3Kernel K₀ F T E →
        ∀ k s s' : Mode, k ∈ F.PHset E → E.fL s ≠ 0 → E.fL s' ≠ 0 →
          |wc E k s s' - 1| ≤ devc K₀ E := by
  obtain ⟨t₁, ht₁, h₁⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, h₂⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨t₃, ht₃, h₃⟩ := lille_threshold K₀
  refine ⟨min (min t₁ t₂) t₃, lt_min (lt_min ht₁ ht₂) ht₃, ?_⟩
  intro Mode _ _ _ F T E hv hle hb hK k s s' hk hfl hfl'
  have hle₁ : hv.t ≤ t₁ := le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hle₂ : hv.t ≤ t₂ := le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hle₃ : hv.t ≤ t₃ := le_trans hle (min_le_right _ _)
  obtain ⟨hPHq, hsubq⟩ := h₁ F T E hv hle₁ hb hK
  obtain ⟨-, -, -, hαle, -⟩ := h₂ F T E hv hle₂ hb hK
  have hK0 : 0 ≤ K₀ := K₀_nonneg_of_kernel K₀ F T E hv hK
  have hlil : 0 ≤ E.lille := le_of_lt (lille_pos E hv)
  have h96 : 96 * max K₀ 0 * E.lille ≤ 1 := h₃ E hv hle₃
  have hX64 : 64 * K₀ * E.lille ≤ 2 / 3 := by
    have hmax : K₀ ≤ max K₀ 0 := le_max_left _ _
    have h1 : K₀ * E.lille ≤ max K₀ 0 * E.lille := mul_le_mul_of_nonneg_right hmax hlil
    nlinarith
  have hX0 : 0 ≤ 64 * K₀ * E.lille := by positivity
  have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
  have hqk : F.PHq E.KH E.aScat k := hPHq k hkPH
  have hqsk : F.PHq E.KH E.aScat (s - k) := hsubq s k hfl hk
  have hqs'k : F.PHq E.KH E.aScat (s' - k) := hsubq s' k hfl' hk
  have hxk : |E.alpha k| ≤ 64 * K₀ * E.lille := hαle k hqk
  have hxu : |E.alpha (s - k)| ≤ 64 * K₀ * E.lille := hαle (s - k) hqsk
  have hxv : |E.alpha (s' - k)| ≤ 64 * K₀ * E.lille := hαle (s' - k) hqs'k
  rw [wc_form]
  have harith := wc_arith hxk hxu hxv hX0 hX64
  rw [devc]
  calc |(1 - E.alpha (s - k) * E.alpha (s' - k)) /
        ((1 - E.alpha k ^ 2) ^ 2 * (1 - E.alpha (s - k) ^ 2)
          * (1 - E.alpha (s' - k) ^ 2)) - 1|
      ≤ 2 ^ 8 * (64 * K₀ * E.lille) ^ 2 := harith
    _ = 2 ^ 20 * K₀ ^ 2 * E.lille ^ 2 := by ring

/-- `Λ ≤ 2ρ_z(Ŵ₁ω(0) + K₀aK_H⁻¹)(1+2𝓁²)`, from `wsum_eq` and `Xi_bound`. -/
theorem wsum_le {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hv : FSParamsView E)
    (hK : Q3Kernel K₀ F T E) (hℓ : 0 < E.ell) (hlil : E.lille ^ 2 ≤ 1 / 2)
    (hDne : ∀ k ∈ F.PHset E, E.D k ≠ 0) :
    wsum F E ≤ 2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) * (1 + 2 * E.lille ^ 2) := by
  have hden : 1 - E.lille ^ 2 ≠ 0 := by
    intro h; linarith [hlil]
  rw [wsum_eq hℓ hden hDne]
  have hΞ : Xi F E ≤ E.W1omega0 + K₀ * E.aScat * E.KH⁻¹ := by
    have := (abs_le.mp (Xi_bound hv hK)).1
    linarith
  have hρ : 0 < E.rho := Work.BoseB7.rho_pos E hv
  have hdenpos : (0 : ℝ) < 1 - E.lille ^ 2 := by linarith
  have hK0 : 0 ≤ K₀ := K₀_nonneg_of_kernel K₀ F T E hv hK
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
  have hA : 0 ≤ E.W1omega0 + K₀ * E.aScat * E.KH⁻¹ := by
    have h1 : 0 ≤ K₀ * E.aScat * E.KH⁻¹ :=
      mul_nonneg (mul_nonneg hK0 (le_of_lt hv.a_pos)) (inv_nonneg.mpr hKH.le)
    linarith [hK.W1omega0_nonneg]
  have hinv : 1 / (1 - E.lille ^ 2) ≤ 1 + 2 * E.lille ^ 2 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [sq_nonneg E.lille, hlil]
  rw [show 2 * E.rho * Xi F E / (1 - E.lille ^ 2)
      = 2 * E.rho * Xi F E * (1 / (1 - E.lille ^ 2)) by ring]
  calc 2 * E.rho * Xi F E * (1 / (1 - E.lille ^ 2))
      ≤ 2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) * (1 / (1 - E.lille ^ 2)) := by
        have h1 : 0 ≤ 2 * E.rho := by linarith
        have h2 : Xi F E * (1 / (1 - E.lille ^ 2))
            ≤ (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) * (1 / (1 - E.lille ^ 2)) :=
          mul_le_mul_of_nonneg_right hΞ (by positivity)
        nlinarith [h1, h2]
    _ ≤ 2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) * (1 + 2 * E.lille ^ 2) := by
        have h1 : 0 ≤ 2 * E.rho * (E.W1omega0 + K₀ * E.aScat * E.KH⁻¹) :=
          mul_nonneg (by linarith) hA
        exact mul_le_mul_of_nonneg_left hinv h1


/-! ## 10. The `Ã`-vs-`ã` comparison -/

/-- `Σ_{s'∈excited}|χ̂²(s'-s)| ≤ K₀+1`: the shifted kernel is summable because the
shift `s' ↦ s'-s` injects the excited modes into the lattice and `Σ|χ̂²| ≤ K₀+1`
(the value at `0` is the only mode lost). -/
theorem sum_hatChiSq_shift {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (s : Mode) :
    (∑ s' ∈ excited Mode, |E.hatChiSq (s' - s)|) ≤ K₀ + 1 := by
  have hinj : ∀ a ∈ excited Mode, ∀ b ∈ excited Mode, a - s = b - s → a = b := by
    intro a _ b _ h
    have h2 : a - s + s = b - s + s := by rw [h]
    rwa [sub_add_cancel, sub_add_cancel] at h2
  calc (∑ s' ∈ excited Mode, |E.hatChiSq (s' - s)|)
      = ∑ q ∈ (excited Mode).image (fun s' => s' - s), |E.hatChiSq q| :=
        (Finset.sum_image (f := fun q => |E.hatChiSq q|)
          (g := fun s' => s' - s) hinj).symm
    _ ≤ ∑ q ∈ (Finset.univ : Finset Mode), |E.hatChiSq q| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun q _ _ => abs_nonneg _)
    _ = ∑ q ∈ excited Mode, |E.hatChiSq q| + |E.hatChiSq 0| := by
        rw [show (Finset.univ : Finset Mode) = insert 0 (excited Mode) by
          ext q; simp [excited]]
        rw [Finset.sum_insert (by simp [excited])]
        ring
    _ ≤ K₀ + 1 := by
        have h1 := hK.sum_hatChiSq
        have h2 := hK.hatChiSq_le 0
        linarith

/-- `Σ_{s,s'}f_L(s)f_L(s')|χ̂²(s'-s)|X_s ≤ (K₀+1)Σ_sf_L(s)X_s` for `X ≥ 0`. -/
theorem sum_chi2_le {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (X : Mode → ℝ) (hX : ∀ s ∈ excited Mode, 0 ≤ X s) :
    (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * X s)
      ≤ (K₀ + 1) * ∑ s ∈ excited Mode, E.fL s * X s := by
  have hw : ∀ s ∈ excited Mode,
      (∑ s' ∈ excited Mode, E.fL s' * |E.hatChiSq (s' - s)|) ≤ K₀ + 1 := by
    intro s _
    calc (∑ s' ∈ excited Mode, E.fL s' * |E.hatChiSq (s' - s)|)
        ≤ ∑ s' ∈ excited Mode, |E.hatChiSq (s' - s)| :=
          Finset.sum_le_sum fun s' _ =>
            mul_le_of_le_one_left (abs_nonneg _) (hK.fL_le_one s')
      _ ≤ K₀ + 1 := sum_hatChiSq_shift hK s
  calc (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * X s)
      = ∑ s ∈ excited Mode, (E.fL s * X s)
          * (∑ s' ∈ excited Mode, E.fL s' * |E.hatChiSq (s' - s)|) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        ring
    _ ≤ ∑ s ∈ excited Mode, (E.fL s * X s) * (K₀ + 1) :=
        Finset.sum_le_sum fun s hs =>
          mul_le_mul_of_nonneg_left (hw s hs) (mul_nonneg (hK.fL_nonneg s) (hX s hs))
    _ = (K₀ + 1) * ∑ s ∈ excited Mode, E.fL s * X s := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring

/-- The transposed form: the weight may sit on the second index. -/
theorem sum_chi2_le' {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (X : Mode → ℝ) (hX : ∀ s ∈ excited Mode, 0 ≤ X s) :
    (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * X s')
      ≤ (K₀ + 1) * ∑ s ∈ excited Mode, E.fL s * X s := by
  rw [Finset.sum_comm]
  have h := sum_chi2_le (K₀ := K₀) hK X hX
  refine le_trans ?_ h
  refine Finset.sum_le_sum fun s' _ => Finset.sum_le_sum fun s _ => ?_
  rw [hatChiSq_swap hK s' s]
  exact le_of_eq (by ring)

/-- The weighted first-index sum, scaled by `c ≥ 0`. -/
theorem sum_chi2_cX {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (c : ℝ) (hc : 0 ≤ c) (X : Mode → ℝ)
    (hX : ∀ s ∈ excited Mode, 0 ≤ X s) :
    (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * X s))
      ≤ c * ((K₀ + 1) * (∑ s ∈ excited Mode, E.fL s * X s)) := by
  have h := sum_chi2_le (K₀ := K₀) hK X hX
  rw [show (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * X s))
      = c * (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * X s) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring]
  exact mul_le_mul_of_nonneg_left h hc

/-- The weighted second-index sum, scaled by `c ≥ 0`. -/
theorem sum_chi2_cY {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (c : ℝ) (hc : 0 ≤ c) (Y : Mode → ℝ)
    (hY : ∀ s ∈ excited Mode, 0 ≤ Y s) :
    (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * Y s'))
      ≤ c * ((K₀ + 1) * (∑ s ∈ excited Mode, E.fL s * Y s)) := by
  have h := sum_chi2_le' (K₀ := K₀) hK Y hY
  rw [show (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * Y s'))
      = c * (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * Y s') from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring]
  exact mul_le_mul_of_nonneg_left h hc

/-- The combined form: `Σ_{s,s'}Wt·(c·(X_s+Y_{s'})) ≤ c((K₀+1)Σf_LX + (K₀+1)Σf_LY)`. -/
theorem sum_chi2_pair {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (c : ℝ) (hc : 0 ≤ c) (X Y : Mode → ℝ)
    (hX : ∀ s ∈ excited Mode, 0 ≤ X s) (hY : ∀ s ∈ excited Mode, 0 ≤ Y s) :
    (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * (X s + Y s')))
      ≤ c * ((K₀ + 1) * (∑ s ∈ excited Mode, E.fL s * X s)
        + (K₀ + 1) * (∑ s ∈ excited Mode, E.fL s * Y s)) := by
  have hA := sum_chi2_cX (K₀ := K₀) hK c hc X hX
  have hB := sum_chi2_cY (K₀ := K₀) hK c hc Y hY
  have hsplit : (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * (X s + Y s')))
      = (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * X s))
        + (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * |E.hatChiSq (s' - s)| * (c * Y s')) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring
  rw [hsplit]
  linarith

/-- **`FA - ⟨G Φ⟩`**: the `Ã`-vs-`ã` comparison, with the `O(β_m)` correction. -/
theorem FA_sub_Q_le {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3Kernel K₀ F T E) (k : Mode) (Φ : F.H) (hK0 : 0 ≤ K₀)
    (hbm : ∀ s, E.fL s ≠ 0 → |bA E s k| ≤ bm K₀ E) :
    FA F T E k Φ - F.qw Φ (T.Gop E)
      ≤ 2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2) * (TA F T E Φ + TB F T E Φ) := by
  have hbm0 : 0 ≤ bm K₀ E := bm_nonneg hK0
  have hQ : F.qw Φ (T.Gop E)
      = ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * E.hatChiSq (s' - s) * F.bp (T.ta s Φ) (T.ta s' Φ) := by
    simp only [FockData.qw, TildeData.Gop, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, bp_taDag_left]
  have hexp : ∀ s s', F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ)
        - F.bp (T.ta s Φ) (T.ta s' Φ)
      = bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
        + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
        + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ) := by
    intro s s'
    have h1 : Atil F T E s k Φ = T.ta s Φ + (bA E s k) • T.taDag (-s) Φ := rfl
    have h2 : Atil F T E s' k Φ = T.ta s' Φ + (bA E s' k) • T.taDag (-s') Φ := rfl
    rw [h1, h2]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hsumU : (∑ s ∈ excited Mode, E.fL s * (F.bp (T.ta s Φ) (T.ta s Φ)
      + F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))) = TA F T E Φ + TB F T E Φ := by
    rw [TA, TB, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hpair := sum_chi2_pair (K₀ := K₀) hK (bm K₀ E + bm K₀ E ^ 2)
    (by nlinarith [hbm0, sq_nonneg (bm K₀ E)]) (fun s => F.bp (T.ta s Φ) (T.ta s Φ) + F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))
    (fun s => F.bp (T.ta s Φ) (T.ta s Φ) + F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))
    (fun s _ => add_nonneg (F.bp_nonneg _) (F.bp_nonneg _))
    (fun s _ => add_nonneg (F.bp_nonneg _) (F.bp_nonneg _))
  rw [hQ]
  have hdiff : FA F T E k Φ
        - (∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
            E.fL s * E.fL s' * E.hatChiSq (s' - s) * F.bp (T.ta s Φ) (T.ta s' Φ))
      = ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * E.hatChiSq (s' - s)
            * (F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ) - F.bp (T.ta s Φ) (T.ta s' Φ)) := by
    rw [FA, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s' _ => by ring
  rw [hdiff]
  calc ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
        E.fL s * E.fL s' * E.hatChiSq (s' - s)
          * (F.bp (Atil F T E s k Φ) (Atil F T E s' k Φ) - F.bp (T.ta s Φ) (T.ta s' Φ))
      ≤ ∑ s ∈ excited Mode, ∑ s' ∈ excited Mode,
          E.fL s * E.fL s' * |E.hatChiSq (s' - s)|
            * ((bm K₀ E + bm K₀ E ^ 2)
              * ((F.bp (T.ta s Φ) (T.ta s Φ) + F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))
                + (F.bp (T.ta s' Φ) (T.ta s' Φ) + F.bp (T.taDag (-s') Φ) (T.taDag (-s') Φ)))) := by
        refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun s' _ => ?_
        rw [hexp s s']
        by_cases h0 : E.fL s = 0
        · rw [h0]; simp
        · by_cases h0' : E.fL s' = 0
          · rw [h0']; simp
          · have hfs : 0 ≤ E.fL s := hK.fL_nonneg s
            have hfs' : 0 ≤ E.fL s' := hK.fL_nonneg s'
            have hβs : |bA E s k| ≤ bm K₀ E := hbm s h0
            have hβs' : |bA E s' k| ≤ bm K₀ E := hbm s' h0'
            have hβs2 : (bA E s k) ^ 2 ≤ (bm K₀ E) ^ 2 := by
              nlinarith [abs_nonneg (bA E s k), sq_abs (bA E s k), hβs, hbm0]
            have hβs'2 : (bA E s' k) ^ 2 ≤ (bm K₀ E) ^ 2 := by
              nlinarith [abs_nonneg (bA E s' k), sq_abs (bA E s' k), hβs', hbm0]
            have h1 := two_abs_bp_le F (T.ta s Φ) (T.taDag (-s') Φ)
            have h2 := two_abs_bp_le F (T.taDag (-s) Φ) (T.ta s' Φ)
            have h3 := two_abs_bp_le F (T.taDag (-s) Φ) (T.taDag (-s') Φ)
            have e1 : |bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)|
                ≤ bm K₀ E * ((F.bp (T.ta s Φ) (T.ta s Φ)
                  + F.bp (T.taDag (-s') Φ) (T.taDag (-s') Φ)) / 2) := by
              rw [abs_mul]
              exact mul_le_mul hβs' (by linarith [h1]) (abs_nonneg _) hbm0
            have e2 : |bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)|
                ≤ bm K₀ E * ((F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ)
                  + F.bp (T.ta s' Φ) (T.ta s' Φ)) / 2) := by
              rw [abs_mul]
              exact mul_le_mul hβs (by linarith [h2]) (abs_nonneg _) hbm0
            have e3 : |bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ)|
                ≤ bm K₀ E ^ 2 * ((F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ)
                  + F.bp (T.taDag (-s') Φ) (T.taDag (-s') Φ)) / 2) := by
              rw [abs_mul, abs_mul]
              have hβm : |bA E s k| * |bA E s' k| ≤ bm K₀ E ^ 2 := by
                calc |bA E s k| * |bA E s' k| ≤ bm K₀ E * bm K₀ E :=
                      mul_le_mul hβs hβs' (abs_nonneg _) hbm0
                  _ = bm K₀ E ^ 2 := by ring
              exact mul_le_mul hβm (by linarith [h3]) (abs_nonneg _) (by positivity)
            have habs1 := abs_add_le (bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ))
              (bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ))
            have habs2 := abs_add_le (bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ))
              (bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ))
            have hmono : |bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                  + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
                  + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ)|
                ≤ |bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)|
                  + |bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)|
                  + |bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ)| := by
              linarith [habs1, habs2]
            have hkey : |bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                  + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
                  + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ)|
                ≤ (bm K₀ E + bm K₀ E ^ 2)
                  * ((F.bp (T.ta s Φ) (T.ta s Φ) + F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))
                    + (F.bp (T.ta s' Φ) (T.ta s' Φ) + F.bp (T.taDag (-s') Φ) (T.taDag (-s') Φ))) := by
              nlinarith [hmono, e1, e2, e3, hbm0,
                F.bp_nonneg (T.ta s Φ), F.bp_nonneg (T.ta s' Φ),
                F.bp_nonneg (T.taDag (-s) Φ), F.bp_nonneg (T.taDag (-s') Φ)]
            calc E.fL s * E.fL s' * E.hatChiSq (s' - s)
                  * (bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                    + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
                    + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ))
                ≤ |E.fL s * E.fL s' * E.hatChiSq (s' - s)
                    * (bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                      + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
                      + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ))| :=
                  le_abs_self _
              _ = |E.fL s * E.fL s' * E.hatChiSq (s' - s)|
                    * |bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                      + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
                      + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ)| := by
                  rw [abs_mul]
              _ = E.fL s * E.fL s' * |E.hatChiSq (s' - s)|
                    * |bA E s' k * F.bp (T.ta s Φ) (T.taDag (-s') Φ)
                      + bA E s k * F.bp (T.taDag (-s) Φ) (T.ta s' Φ)
                      + bA E s k * bA E s' k * F.bp (T.taDag (-s) Φ) (T.taDag (-s') Φ)| := by
                  rw [abs_mul, abs_mul, abs_of_nonneg hfs, abs_of_nonneg hfs']
              _ ≤ E.fL s * E.fL s' * |E.hatChiSq (s' - s)|
                    * ((bm K₀ E + bm K₀ E ^ 2)
                      * ((F.bp (T.ta s Φ) (T.ta s Φ) + F.bp (T.taDag (-s) Φ) (T.taDag (-s) Φ))
                        + (F.bp (T.ta s' Φ) (T.ta s' Φ) + F.bp (T.taDag (-s') Φ) (T.taDag (-s') Φ)))) :=
                  mul_le_mul_of_nonneg_left hkey
                    (mul_nonneg (mul_nonneg hfs hfs') (abs_nonneg _))
    _ ≤ (bm K₀ E + bm K₀ E ^ 2) * ((K₀ + 1) * (TA F T E Φ + TB F T E Φ)
          + (K₀ + 1) * (TA F T E Φ + TB F T E Φ)) := by
        have := hpair
        rw [hsumU] at this
        exact this
    _ = 2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2) * (TA F T E Φ + TB F T E Φ) := by ring

/-- **`FA ≤ ⟨G Φ⟩ + C_b(⟨n₊⟩ + N_PL‖Φ‖²)`** at the parameter point. -/
theorem FA_le_Q (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseB7A.Q3Kernel K₀ F T E →
        ∀ (k : Mode) (Φ : F.H), k ∈ F.PHset E →
          FA F T E k Φ ≤ F.qw Φ (T.Gop E)
            + cbeta K₀ E * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) := by
  obtain ⟨t₁, ht₁, h₁⟩ := PH_subset_PHq_sub K₀ b₀ hb₀
  obtain ⟨t₂, ht₂, h₂⟩ := kernel_basic K₀ b₀ hb₀
  obtain ⟨t₃, ht₃, h₃⟩ := lille_threshold K₀
  refine ⟨min (min t₁ t₂) t₃, lt_min (lt_min ht₁ ht₂) ht₃, ?_⟩
  intro Mode _ _ _ F T E hv hle hb hK k Φ hk
  have hle₁ : hv.t ≤ t₁ := le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hle₂ : hv.t ≤ t₂ := le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hle₃ : hv.t ≤ t₃ := le_trans hle (min_le_right _ _)
  obtain ⟨hPHq, hsubq⟩ := h₁ F T E hv hle₁ hb hK
  obtain ⟨-, -, -, hαle, -⟩ := h₂ F T E hv hle₂ hb hK
  have hK0 : 0 ≤ K₀ := K₀_nonneg_of_kernel K₀ F T E hv hK
  have hlil : 0 ≤ E.lille := le_of_lt (lille_pos E hv)
  have h96 : 96 * max K₀ 0 * E.lille ≤ 1 := h₃ E hv hle₃
  have hbm : ∀ s, E.fL s ≠ 0 → |bA E s k| ≤ bm K₀ E := by
    intro s hfs
    have hkPH : F.PH E.KH E.aScat k := (Finset.mem_filter.mp hk).2
    have hqk : F.PHq E.KH E.aScat k := hPHq k hkPH
    have hqsk : F.PHq E.KH E.aScat (s - k) := hsubq s k hfs hk
    have h1 := hαle k hqk
    have h2 := hαle (s - k) hqsk
    rw [bA, abs_mul]
    have hmax : K₀ ≤ max K₀ 0 := le_max_left _ _
    have h3 : K₀ * E.lille ≤ max K₀ 0 * E.lille := mul_le_mul_of_nonneg_right hmax hlil
    have h4 : (64 * K₀ * E.lille) * (64 * K₀ * E.lille) ≤ (2 ^ 12 : ℝ) * K₀ ^ 2 * E.lille ^ 2 := by
      have h5 : 64 * K₀ * E.lille ≤ 2 / 3 := by nlinarith
      have h6 : 0 ≤ 64 * K₀ * E.lille := by positivity
      nlinarith
    calc |E.alpha k| * |E.alpha (s - k)| ≤ (64 * K₀ * E.lille) * (64 * K₀ * E.lille) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ (2 ^ 12 : ℝ) * K₀ ^ 2 * E.lille ^ 2 := h4
      _ = bm K₀ E := by rw [bm]
  have hmain := FA_sub_Q_le hK k Φ hK0 hbm
  have hTA := TA_le_N (K₀ := K₀) hK Φ
  have hTB := TB_le (K₀ := K₀) hK Φ
  have hTB0 : 0 ≤ TB F T E Φ := Finset.sum_nonneg fun s _ => mul_nonneg (hK.fL_nonneg s) (F.bp_nonneg _)
  have hTA0 : 0 ≤ TA F T E Φ := Finset.sum_nonneg fun s _ => mul_nonneg (hK.fL_nonneg s) (F.bp_nonneg _)
  have hNPL0 : 0 ≤ NPL E := NPL_nonneg E
  have hNAP0 : 0 ≤ F.bp (T.N Φ) Φ := T.N_nonneg Φ
  have hNS0 : 0 ≤ F.normSq Φ := F.bp_nonneg _
  have hbm0 : 0 ≤ bm K₀ E := bm_nonneg hK0
  have hcb : cbeta K₀ E = (K₀ + 1) * (4 * bm K₀ E + 4 * bm K₀ E ^ 2) := rfl
  have hK1 : 0 ≤ K₀ + 1 := by linarith
  have hfin : 2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2) * (TA F T E Φ + TB F T E Φ)
      ≤ cbeta K₀ E * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) := by
    rw [hcb]
    have h1 : TA F T E Φ + TB F T E Φ ≤ 2 * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) := by
      nlinarith [hTA, hTB, hNPL0, hNS0, hNAP0]
    have h2 : 0 ≤ bm K₀ E + bm K₀ E ^ 2 := by nlinarith [sq_nonneg (bm K₀ E), hbm0]
    have h3 : 2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2) * 2
        ≤ (K₀ + 1) * (4 * bm K₀ E + 4 * bm K₀ E ^ 2) := by nlinarith [hK1, hbm0]
    calc 2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2) * (TA F T E Φ + TB F T E Φ)
        ≤ 2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2)
            * (2 * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ)) :=
          mul_le_mul_of_nonneg_left h1 (by nlinarith [hK1, hbm0])
      _ = (2 * (K₀ + 1) * (bm K₀ E + bm K₀ E ^ 2) * 2)
            * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) := by ring
      _ ≤ ((K₀ + 1) * (4 * bm K₀ E + 4 * bm K₀ E ^ 2))
            * (F.bp (T.N Φ) Φ + NPL E * F.normSq Φ) :=
          mul_le_mul_of_nonneg_right h3 (by nlinarith [hNAP0, hNPL0, hNS0])
  linarith [hmain, hfin]

end Est1

end Work.BoseB7A
