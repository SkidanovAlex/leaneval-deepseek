import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.Est1.ComZDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.Est1.ComZ` — the analysis of the `χ̂²` half

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

namespace Work.BoseC3QAll

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
    (hK : Q3KernelFSAll K₀ F T E) :
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
    (hK : Q3KernelFSAll K₀ F T E) (Φ : F.H) :
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
    (hK : Q3KernelFSAll K₀ F T E) (Φ : F.H) :
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
theorem sum_sum_amgm (S : Finset Mode) (a b : Mode → ℝ) :
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
    (hK : Q3KernelFSAll K₀ F T E) (k : Mode) (Φ : F.H) :
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

/-- `FA ≥ 0`: the PSD half of `Q3KernelFSAll.hatChiSq_form` with `c = f_L` and
`v s = Ã_{s,k}Φ`. -/
theorem FA_nonneg {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}
    (hK : Q3KernelFSAll K₀ F T E) (k : Mode) (Φ : F.H) : 0 ≤ FA F T E k Φ := by
  have hform := (hK.hatChiSq_form (excited Mode) E.fL (fun s => Atil F T E s k Φ)
    (fun s hs h => h)).1
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
    (hK : Q3KernelFSAll K₀ F T E) (k : Mode) (Φ : F.H)
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
    (hK : Q3KernelFSAll K₀ F T E) (k : Mode) (Φ : F.H) (hdev0 : 0 ≤ devc K₀ E)
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
    (hK : Q3KernelFSAll K₀ F T E) (k : Mode) (Φ : F.H) (hK0 : 0 ≤ K₀) (hη : 0 ≤ eta E)
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


end Est1

end Work.BoseC3QAll
