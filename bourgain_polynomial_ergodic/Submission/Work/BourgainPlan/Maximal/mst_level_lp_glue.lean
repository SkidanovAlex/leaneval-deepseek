import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n
import Submission.Work.BourgainPlan.Maximal.ellp_interpolation
import Submission.Work.BourgainPlan.Maximal.mst_level_lp_arith
import Submission.Work.BourgainPlan.Maximal.mst_eLpNorm_iSup_mono_le

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

/-- **The finite-scale Riesz–Thorin step of the level interpolation.**  Let `Φ : ℕ → L^∞(𝕋)` be a
family of symbols whose maximal multiplier `g ↦ (m ↦ ⨆_k ‖Φ_k g (m)‖)` obeys an `ℓ²` bound with
constant `B` and an `ℓʳ` bound with constant `A` (`1 < r < p < 2`).  Then for every *finite* set of
scales `K` the truncated maximal function `g ↦ (m ↦ ⨆_{k ∈ K} ‖Φ_k g (m)‖)` obeys the interpolated
`ℓᵖ` bound with the Riesz–Thorin constant `A^{1-θ} B^θ`, `θ = (1/r - 1/p)/(1/r - 1/2)`.

Proof (linearisation, as in `Commons.Analysis.Interpolation.sublinear_maximal_lp_interpolation`):
for the fixed datum `f` choose at every `m ∈ ℤ` a scale `σ m ∈ K` maximising `‖Φ_k f m‖`; the map
`L g := (m ↦ Φ_{σ m} g m)` is `ℂ`-linear (`opMulFinsuppLM`), it is dominated pointwise by the full
maximal function for every `g` (giving the two endpoint bounds from the hypotheses) and it agrees
with the *truncated* maximal function at `f`.  `ellp_interpolation` (Riesz–Thorin on `ℤ` with
counting measure, applied to `L`) then gives the `ℓᵖ` bound, which is transported back with
`eLpNorm'_congr_enorm_ae`. -/
lemma mst_level_lp_finset (Φ : ℕ → Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    {r p : ℝ} (hr : 1 < r) (hrp : r < p) (hp2 : p < 2)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h2 : ∀ g : ℤ →₀ ℂ,
      eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ‖Work.BourgainPlan.IonescuWainger.opMul (Φ k) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
        (ENNReal.ofReal 2) Measure.count
        ≤ ENNReal.ofReal B * eLpNorm (⇑g) (ENNReal.ofReal 2) Measure.count)
    (hrr : ∀ g : ℤ →₀ ℂ,
      eLpNorm (fun m : ℤ => (⨆ k : ℕ,
          ‖Work.BourgainPlan.IonescuWainger.opMul (Φ k) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
        (ENNReal.ofReal r) Measure.count
        ≤ ENNReal.ofReal A * eLpNorm (⇑g) (ENNReal.ofReal r) Measure.count) :
    ∀ (K : Finset ℕ), K.Nonempty → ∀ g : ℤ →₀ ℂ,
      eLpNorm (fun m : ℤ => (⨆ k ∈ K,
          ‖Work.BourgainPlan.IonescuWainger.opMul (Φ k) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
        (ENNReal.ofReal p) Measure.count
        ≤ ENNReal.ofReal (A ^ (1 - (1 / r - 1 / p) / (1 / r - 1 / 2))
            * B ^ ((1 / r - 1 / p) / (1 / r - 1 / 2)))
          * eLpNorm (⇑g) (ENNReal.ofReal p) Measure.count := by
  intro K hK f
  have hr0 : (0:ℝ) < r := lt_trans zero_lt_one hr
  have hr2 : r < 2 := lt_trans hrp hp2
  have hp1 : (1:ℝ) < p := lt_trans hr hrp
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp1
  set θ : ℝ := (1 / r - 1 / p) / (1 / r - 1 / 2) with hθdef
  have hden : (0:ℝ) < 1 / r - 1 / 2 := by
    have h : (1:ℝ)/2 < 1/r := one_div_lt_one_div_of_lt hr0 hr2
    linarith
  have hnum : (0:ℝ) < 1 / r - 1 / p := by
    have h : (1:ℝ)/p < 1/r := one_div_lt_one_div_of_lt hr0 hrp
    linarith
  have hθ0 : (0:ℝ) ≤ θ := le_of_lt (by rw [hθdef]; exact div_pos hnum hden)
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one hden]
    have h : (1:ℝ)/2 < 1/p := one_div_lt_one_div_of_lt hp0 hp2
    linarith
  have hθp : 1 / p = (1 - θ) / r + θ / 2 := by
    rw [hθdef]
    have h1 : (1/r - 1/p)/(1/r - 1/2) * (1/r - 1/2) = 1/r - 1/p :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    have h2 : 1/r - (1/r - 1/p) = 1/p := by ring
    have h3 : (1 - (1/r - 1/p)/(1/r - 1/2))/r + ((1/r - 1/p)/(1/r - 1/2))/2
        = 1/r - ((1/r - 1/p)/(1/r - 1/2)) * (1/r - 1/2) := by field_simp; ring
    rw [h3, h1, h2]
  let Ak : ℕ → (ℤ →₀ ℂ) → ℤ → ℂ := fun k g m =>
    Work.BourgainPlan.IonescuWainger.opMul (Φ k) (⇑g)
      (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m
  have hsel : ∀ m : ℤ, ∃ i : ℕ, i ∈ K ∧ ∀ j ∈ K, ‖Ak j f m‖ ≤ ‖Ak i f m‖ := by
    intro m
    obtain ⟨i, hiK, hi⟩ := Finset.exists_max_image K (fun j => ‖Ak j f m‖) hK
    exact ⟨i, hiK, fun j hj => hi j hj⟩
  choose σ hσ using hsel
  let L : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
    { toFun := fun g m => opMulFinsuppLM (Φ (σ m)) g m
      map_add' := fun g h => by
        funext m
        exact congrFun (map_add (opMulFinsuppLM (Φ (σ m))) g h) m
      map_smul' := fun c g => by
        funext m
        exact congrFun (map_smul (opMulFinsuppLM (Φ (σ m))) c g) m }
  have hLapply : ∀ (g : ℤ →₀ ℂ) (m : ℤ), L g m = Ak (σ m) g m := by
    intro g m
    change (opMulFinsuppLM (Φ (σ m))) g m = _
    rw [opMulFinsuppLM_apply]
  have henrm : ∀ (a b : ℂ), ‖a‖ ≤ ‖b‖ → ‖a‖ₑ ≤ ‖b‖ₑ := by
    intro a b h
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe]
    exact_mod_cast h
  have hLdom : ∀ (g : ℤ →₀ ℂ) (m : ℤ), ‖L g m‖ₑ ≤ (⨆ k : ℕ, ‖Ak k g m‖ₑ) := by
    intro g m
    rw [hLapply g m]
    exact le_iSup (fun k => ‖Ak k g m‖ₑ) (σ m)
  have hLf : ∀ m : ℤ, ‖L f m‖ₑ = (⨆ k ∈ K, ‖Ak k f m‖ₑ) := by
    intro m
    rw [hLapply f m]
    refine le_antisymm ?_ ?_
    · exact le_iSup_of_le (σ m) (le_iSup_of_le (hσ m).1 le_rfl)
    · refine iSup_le fun k => iSup_le fun hk => ?_
      exact henrm _ _ ((hσ m).2 k hk)
  have hLr : ∀ g : ℤ →₀ ℂ, eLpNorm (L g) (ENNReal.ofReal r) Measure.count
      ≤ ENNReal.ofReal A * eLpNorm (⇑g) (ENNReal.ofReal r) Measure.count := by
    intro g
    refine le_trans (eLpNorm_mono_enorm (f := L g)
      (g := fun m : ℤ => (⨆ k : ℕ, ‖Ak k g m‖ₑ)) AEStronglyMeasurable.of_discrete
      (fun m => hLdom g m)) ?_
    exact hrr g
  have hL2 : ∀ g : ℤ →₀ ℂ, eLpNorm (L g) (ENNReal.ofReal 2) Measure.count
      ≤ ENNReal.ofReal B * eLpNorm (⇑g) (ENNReal.ofReal 2) Measure.count := by
    intro g
    refine le_trans (eLpNorm_mono_enorm (f := L g)
      (g := fun m : ℤ => (⨆ k : ℕ, ‖Ak k g m‖ₑ)) AEStronglyMeasurable.of_discrete
      (fun m => hLdom g m)) ?_
    exact h2 g
  have hint := ellp_interpolation (q₀ := r) (q₁ := 2) (p := p) (θ := θ) (A := A) (B := B)
    (le_of_lt hr) (le_of_lt hr2) hp1 hθ0 hθ1 hθp hA hB L hLr hL2
  have hEq : eLpNorm (L f) (ENNReal.ofReal p) Measure.count
      = eLpNorm (fun m : ℤ => (⨆ k ∈ K, ‖Ak k f m‖ₑ)) (ENNReal.ofReal p) Measure.count := by
    rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
          AEStronglyMeasurable.of_discrete,
        eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
          AEStronglyMeasurable.of_discrete]
    refine eLpNorm'_congr_enorm_ae (Filter.Eventually.of_forall (fun m => ?_))
    simp only [enorm_eq_self]
    exact hLf m
  have h := hint f
  rw [hEq] at h
  exact h

/-- The interpolation of the two level endpoints (Mirek-Stein-Trojan, arXiv:1512.07518, §4.4, the passage from eqs. (178) and (89) to eq. (81)): for an arbitrary family of multiplier classes `ν : ℕ → ℕ → L^∞(𝕋)` (intended `ν k s = mstNuSCls P l d χ η k s`), if for every `s` the maximal function `T g := (m ↦ sup_k ‖opMul (ν_{k,s}) g m‖)` satisfies

* an `ℓ²` bound with *decay* `A₂ (s+1)^{e₂}` (the level `ℓ²` estimate, MST Thm 2, with `e₂ = 1 − δl < 0` for `l` large), and
* an `ℓʳ` bound with *loss* `A_r (s+1) log(s+2)` (the level `ℓʳ` estimate, MST eq. (89), for some `1 < r < p < 2`),

then for `e₂` negative enough there is `C > 0` with

  `‖sup_k |F⁻¹(ν_{k,s}ĝ)|‖_{ℓᵖ} ≤ C (s+1)^{−2} ‖g‖_{ℓᵖ}`  for every `s` and every finitely supported `g`,

which is the hypothesis `hlevel` of the §6 assembly `mst_dyadic_z_of_pieces`.

Route (linearize, do **not** use Lyapunov on the maximal function, which would leave the unmatched factor `‖g‖_r^{1−θ}‖g‖₂^{θ}`): `T` is sublinear; for a fixed finite set of scales the pointwise maximizing scale gives a linear map dominated by `T` with the same endpoint norms (or use Riesz–Thorin for sublinear operators / the standard `max`-linearization), so `‖T g‖_p ≤ A₂^{θ} A_r^{1−θ} (s+1)^{θe₂+1−θ} (log(s+2))^{1−θ} ‖g‖_p` with `1/p = (1−θ)/r + θ/2`.  Choose `e₂ ≤ L` with `θL + 1 − θ < −2` (e.g. `L := −(3−θ)/θ − 1`), and absorb the log powers and the finitely many small `s` into `C`.  (`mst_minor_per_n`'s `opMulFinsuppLM`/`ellp_interpolation` give the linear Riesz–Thorin step for a single multiplier; here it is applied to the linearized maximal operator.) -/
theorem mst_level_lp_glue (ν : ∀ n s : ℕ, MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    {p r : ℝ} (hr : 1 < r) (hrp : r < p) (hp2 : p < 2) :
    ∃ L : ℝ, ∀ (e₂ : ℝ), e₂ ≤ L → ∀ (A₂ A_r : ℝ), 0 < A₂ → 0 < A_r →
      (∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
        MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
            ‖Work.BourgainPlan.IonescuWainger.opMul (ν k s) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal 2) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (A₂ * ((s : ℝ) + 1) ^ e₂)
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal 2) MeasureTheory.Measure.count) →
      (∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
        MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
            ‖Work.BourgainPlan.IonescuWainger.opMul (ν k s) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal r) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (A_r * (((s : ℝ) + 1) * Real.log ((s : ℝ) + 2)))
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal r) MeasureTheory.Measure.count) →
      ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ, ∀ g : ℤ →₀ ℂ,
        MeasureTheory.eLpNorm (fun m : ℤ => (⨆ k : ℕ,
            ‖Work.BourgainPlan.IonescuWainger.opMul (ν k s) (⇑g)
              (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * ((s : ℝ) + 1) ^ (-2 : ℝ))
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hr0 : (0:ℝ) < r := lt_trans zero_lt_one hr
  have hr2 : r < 2 := lt_trans hrp hp2
  have hp1 : (1:ℝ) < p := lt_trans hr hrp
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp1
  set θ : ℝ := (1 / r - 1 / p) / (1 / r - 1 / 2) with hθdef
  have hden : (0:ℝ) < 1 / r - 1 / 2 := by
    have h : (1:ℝ)/2 < 1/r := one_div_lt_one_div_of_lt hr0 hr2
    linarith
  have hnum : (0:ℝ) < 1 / r - 1 / p := by
    have h : (1:ℝ)/p < 1/r := one_div_lt_one_div_of_lt hr0 hrp
    linarith
  have hθ0 : (0:ℝ) < θ := by rw [hθdef]; exact div_pos hnum hden
  have hθmuld : θ * (1 / r - 1 / 2) = 1 / r - 1 / p := by
    rw [hθdef]
    exact div_mul_cancel₀ (1 / r - 1 / p) (ne_of_gt hden)
  have hθ1 : θ < 1 := by
    have h : (1:ℝ)/2 < 1/p := one_div_lt_one_div_of_lt hp0 hp2
    nlinarith [hθmuld, hden, h]
  refine ⟨-3/θ, fun e₂ he₂ A₂ A_r hA₂ hA_r h2 hrr => ?_⟩
  obtain ⟨C, hCpos, hC⟩ := mst_level_lp_arith hθ0 hθ1 hA₂ hA_r he₂
  refine ⟨C, hCpos, fun s g => ?_⟩
  have hslog : (0:ℝ) < Real.log ((s:ℝ) + 2) := by
    apply Real.log_pos
    have : (0:ℝ) ≤ (s:ℝ) := Nat.cast_nonneg s
    linarith
  have hAs : 0 < A_r * (((s:ℝ)+1) * Real.log ((s:ℝ)+2)) := by
    have : (0:ℝ) < (s:ℝ) + 1 := by positivity
    positivity
  have hBs : 0 < A₂ * ((s:ℝ)+1)^e₂ := by
    have : (0:ℝ) < (s:ℝ) + 1 := by positivity
    positivity
  have hfin := mst_level_lp_finset (Φ := fun k => ν k s) hr hrp hp2 hAs hBs (h2 s) (hrr s)
  set z : ℕ → ℤ → ENNReal := fun k m => ‖Work.BourgainPlan.IonescuWainger.opMul (ν k s) (⇑g)
      (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) m‖ₑ with hzdef
  have hbound : ∀ n : ℕ, eLpNorm (fun m : ℤ => ⨆ k ∈ Finset.range (n+1), z k m)
        (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal ((A_r * (((s:ℝ)+1) * Real.log ((s:ℝ)+2))) ^ (1 - θ)
          * (A₂ * ((s:ℝ)+1)^e₂) ^ θ)
        * eLpNorm (⇑g) (ENNReal.ofReal p) Measure.count := by
    intro n
    have h := hfin (Finset.range (n+1)) ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩ g
    simpa only [hzdef] using h
  have hmono : Monotone (fun n : ℕ => fun m : ℤ => ⨆ k ∈ Finset.range (n+1), z k m) := by
    intro n n' hnn'
    refine fun m => iSup_le fun k => iSup_le fun hk => ?_
    exact le_iSup_of_le k (le_iSup_of_le
      (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_succ hnn'))) le_rfl)
  have hsup := mst_eLpNorm_iSup_mono_le (q := p) hp0 hmono hbound
  have hfun : (fun m : ℤ => ⨆ n : ℕ, ⨆ k ∈ Finset.range (n+1), z k m)
      = (fun m : ℤ => ⨆ k : ℕ, z k m) := by
    funext m
    refine le_antisymm ?_ ?_
    · refine iSup_le fun n => iSup_le fun k => iSup_le fun _ => le_iSup (fun k => z k m) k
    · refine iSup_le fun k => ?_
      have h1 : z k m ≤ ⨆ j ∈ Finset.range (k+1), z j m :=
        le_iSup_of_le k (le_iSup_of_le (Finset.mem_range.mpr (Nat.lt_succ_self k)) le_rfl)
      exact le_iSup_of_le k h1
  rw [hfun] at hsup
  refine le_trans hsup ?_
  refine mul_le_mul_of_nonneg_right ?_ ?_
  · refine ENNReal.ofReal_le_ofReal ?_
    exact hC s
  · exact zero_le


end

end Work.BourgainPlan.Maximal
