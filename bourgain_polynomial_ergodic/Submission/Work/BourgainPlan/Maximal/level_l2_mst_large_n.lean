import Mathlib
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n_aux_defs
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols
import Submission.Work.BourgainPlan.Maximal.mstEta_arcSum_le
import Submission.Work.BourgainPlan.Maximal.mstModelFn_modSeq
import Submission.Work.BourgainPlan.Maximal.mstOrthogonality
import Submission.Work.BourgainPlan.Maximal.mstNumeric
import Submission.Work.BourgainPlan.Maximal.mstTorsion
import Submission.Work.BourgainPlan.Maximal.mstMaximal_single
import Submission.Work.BourgainPlan.Maximal.major_arc_model
import Submission.Work.BourgainPlan.Maximal.mstFreeze

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- `opMul` does not depend on the `Memℓp` proof, so it is congruent in the input sequence. -/
lemma asm_opMul_congr {Φ : Lp ℂ ⊤ mstHaar} {g₁ g₂ : ℤ → ℂ} (h : g₁ = g₂)
    (hg₁ : Memℓp g₁ 2) (hg₂ : Memℓp g₂ 2) :
    opMul Φ g₁ hg₁ = opMul Φ g₂ hg₂ := by
  subst h
  rw [Subsingleton.elim hg₁ hg₂]

/-- The arc comb is `Q`-periodic when every arc is a `Q`-torsion point. -/
lemma asm_mstArc_add_period (G : mstCirc → ℂ) (E : Finset mstCirc) (Q : ℕ)
    (hQ : ∀ β ∈ E, fourier (Q : ℤ) β = 1) (t : ℤ) :
    mstArc G E (t + (Q : ℤ)) = mstArc G E t := by
  rw [mstArc, mstArc]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [fourier_add, hQ β hβ, mul_one]

/-- The arc comb is also invariant under subtracting the period. -/
lemma asm_mstArc_sub_period (G : mstCirc → ℂ) (E : Finset mstCirc) (Q : ℕ)
    (hQ : ∀ β ∈ E, fourier (Q : ℤ) β = 1) (t : ℤ) :
    mstArc G E (t - (Q : ℤ)) = mstArc G E t := by
  have h := asm_mstArc_add_period G E Q hQ (t - (Q : ℤ))
  rw [sub_add_cancel] at h
  exact h.symm

/-- The modulated input is `Q`-periodic in the modulation index. -/
lemma asm_mstModSeq_period (G : mstCirc → ℂ) (E : Finset mstCirc) (Q : ℕ)
    (hQ : ∀ β ∈ E, fourier (Q : ℤ) β = 1) (f : ℤ → ℂ) (x : ℤ) :
    mstModSeq G E f (x + (Q : ℤ)) = mstModSeq G E f x := by
  funext k
  simp only [mstModSeq_apply]
  rw [show k - (x + (Q : ℤ)) = (k - x) - (Q : ℤ) by ring, asm_mstArc_sub_period G E Q hQ]

/-- Substitution `m ↦ m + u` in the counting measure, in the *pair* `(m, m + u)`. -/
lemma asm_lintegral_count_pair (F : ℤ → ℤ → ℝ≥0∞) (u : ℤ) :
    ∫⁻ m : ℤ, F m (m + u) ∂MeasureTheory.Measure.count
      = ∫⁻ m : ℤ, F (m - u) m ∂MeasureTheory.Measure.count := by
  rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
  refine (tsum_congr fun a => ?_).trans
    (Equiv.tsum_eq (Equiv.addRight u) (fun m : ℤ => F (m - u) m))
  show F a (a + u) = F (a + u - u) (a + u)
  rw [add_sub_cancel_right]

/-- **Sums over a complete residue system of a periodic function, shift form.** -/
lemma asm_sum_range_add_period (F : ℤ → ℝ≥0∞) (Q : ℕ) (hQpos : 0 < Q)
    (hF : ∀ v : ℤ, F (v + (Q : ℤ)) = F v) (y : ℤ) :
    ∑ u ∈ Finset.range Q, F (y + (u : ℤ)) = ∑ u ∈ Finset.range Q, F (u : ℤ) := by
  have hshift : ∀ y : ℤ,
      (∑ u ∈ Finset.range Q, F (y + 1 + (u : ℤ))) = ∑ u ∈ Finset.range Q, F (y + (u : ℤ)) := by
    intro y
    have hrange : Finset.range Q = Finset.range ((Q - 1) + 1) := by
      congr 1
      exact (Nat.succ_pred_eq_of_pos hQpos).symm
    have eW : (∑ u ∈ Finset.range Q, F (y + (u : ℤ)))
        = ∑ u ∈ Finset.range (Q - 1), F (y + (((u + 1 : ℕ)) : ℤ))
          + F (y + ((0 : ℕ) : ℤ)) := by
      rw [hrange]
      exact Finset.sum_range_succ' _ _
    have eW1 : (∑ u ∈ Finset.range Q, F (y + 1 + (u : ℤ)))
        = ∑ u ∈ Finset.range (Q - 1), F (y + (((u + 1 : ℕ)) : ℤ))
          + F (y + ((Q : ℕ) : ℤ)) := by
      rw [hrange, Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun u _ => ?_
        congr 1
        omega
      · congr 1
        omega
    have hFQ : F (y + ((Q : ℕ) : ℤ)) = F (y + ((0 : ℕ) : ℤ)) := by
      rw [Nat.cast_zero, add_zero]
      exact hF y
    rw [eW1, eW, hFQ]
  refine Int.induction_on (motive := fun y : ℤ =>
      (∑ u ∈ Finset.range Q, F (y + (u : ℤ))) = ∑ u ∈ Finset.range Q, F (u : ℤ)) y ?_ ?_ ?_
  · simp only [zero_add]
  · intro n hn
    rw [hshift (n : ℤ)]
    exact hn
  · intro n hn
    have h := hshift (-(n : ℤ) - 1)
    rw [show (-(n : ℤ) - 1) + 1 = -(n : ℤ) by ring] at h
    rw [← h]
    exact hn

/-- **Sums over a complete residue system of a periodic function.**  If `F : ℤ → ℝ≥0∞` is
`Q`-periodic (`F (v + Q) = F v`, `Q > 0`) then the window `y - u`, `u ∈ {0,…,Q-1}`, meets every
residue class mod `Q` exactly once and therefore reproduces the sum over `{0,…,Q-1}`. -/
lemma asm_sum_range_sub_period (F : ℤ → ℝ≥0∞) (Q : ℕ) (hQpos : 0 < Q)
    (hF : ∀ v : ℤ, F (v + (Q : ℤ)) = F v) (y : ℤ) :
    ∑ u ∈ Finset.range Q, F (y - (u : ℤ)) = ∑ u ∈ Finset.range Q, F (u : ℤ) := by
  have h1 : (∑ u ∈ Finset.range Q, F (y - (u : ℤ)))
      = ∑ u ∈ Finset.range Q, F ((y - (Q : ℤ) + 1) + (u : ℤ)) := by
    rw [← Finset.sum_range_reflect (fun j : ℕ => F ((y - (Q : ℤ) + 1) + (j : ℤ))) Q]
    refine Finset.sum_congr rfl fun u hu => ?_
    congr 1
    have hlt : u < Q := Finset.mem_range.mp hu
    have hcast : (((Q - 1 - u : ℕ)) : ℤ) = (Q : ℤ) - 1 - (u : ℤ) := by omega
    rw [hcast]
    ring
  rw [h1, asm_sum_range_add_period F Q hQpos hF (y - (Q : ℤ) + 1)]

/-- **The large-scale half of MST Theorem 2** (arXiv:1512.07518, §4.3, the estimate for `sup_{n ≥ 2^{κ_s}}`, `κ_s = 20 d (⌊(s+1)^{1/10}⌋+1)`): for the level-`s` major-arc model, the `ℓ²` norm of the maximal function over the dyadic scales `n ≥ 2^{κ_s}` is bounded by `C G0 (s+1)^{−δl} ‖f‖_{ℓ²}` — no `s`-loss, the Gauss-sum decay `(s+1)^{−δl}` being exactly the gain.  (Note the exponent `1/10` in `κ_s` is the **real** one: `(s:ℝ)+1) ^ (1/10 : ℝ)`, not the `ℕ`-valued `^` of a numeral.)  Route (MST §4.3, second half): with `I(x,y) = sup_{n ≥ 2^{κ_s}} |Σ_{β} G β e(−⟨β,x⟩) F⁻¹(Φ_{2^n} η_s f̂(·+β))(y)|` and `J(x,y)` the same with `Φ_{2^n}` deleted, (i) the *freezing* estimate `| ‖I(x,x+u)‖_{ℓ²_x} − ‖I(x,x)‖_{ℓ²_x} | ≲ 2^{−2^{κ_s}/d} Q_s |𝒰_{(s+1)^l}| ‖f‖₂` for `u ∈ ℕ_{Q_s}`, via Plancherel and `sup_ξ ‖ξ‖·|Φ_{2^n}(ξ)| ≲ 2^{−n/d}` (a corollary of `polyProfile_decay_sharp`); (ii) averaging over `u ∈ ℕ_{Q_s}` and using that `x ↦ I(x,·)` and `x ↦ J(x,·)` are `Q_s ℤ`-periodic, which holds because every denominator of the level divides `Q_s` (`q ≤ e^{(s+1)^{1/10}}`, from `sigmaN_denom_le`); (iii) the Magyar–Stein–Wainger sampling principle (`msw_sampling_lp`, MST Proposition 4) replacing `I` by `J` at fixed `u`; (iv) Plancherel, the disjointness of the bump supports (`sigmaN_separated`) and the Gauss decay `|G(a/q)| ≲ q^{−δ}` on the level (`q > s^l`) giving `(s+1)^{−2δl}‖f‖₂²`; (v) the numerical inequality `2^{κ_s}(log 2)/d − (s+1)^{1/10} e^{(s+1)^{1/10}} − (d+1)(s+1)^{1/10} ≥ s`, which is why the estimate is stated for `s ≥ s₀`. -/
theorem level_l2_mst_large_n (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (l : ℕ) (hl : 1 ≤ l) (χ : ℝ) (hχ : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (hη1 : η 0 = 1)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      ∀ (G : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (G0 : ℝ), 0 ≤ G0 →
      (∀ β ∈ (Work.BourgainPlan.Maximal.mstU l (s + 1)) \ (Work.BourgainPlan.Maximal.mstU l s),
        ‖G β‖ ≤ G0 * ((s : ℝ) + 1) ^ (-(δ * l))) →
      ∀ (hS : ∀ n : ℕ, MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))),
      (∀ n : ℕ, ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
        (hS n : Work.BourgainPlan.IonescuWainger.Circle → ℂ) ξ
          = Work.BourgainPlan.Maximal.mstModelFn G (Work.BourgainPlan.Maximal.mstProf P (2 ^ n))
              (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s)
              ((Work.BourgainPlan.Maximal.mstU l (s + 1))
                \ (Work.BourgainPlan.Maximal.mstU l s)) ξ) →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2),
        ∫⁻ m : ℤ,
            (⨆ n : ℕ,
              ⨆ (_ : 2 ^ (20 * P.natDegree * (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1)) ≤ n),
              ‖Work.BourgainPlan.IonescuWainger.opMul (hS n) f hf m‖ₑ) ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((C * G0 * ((s : ℝ) + 1) ^ (-(δ * l))) ^ 2)
            * ∫⁻ m : ℤ, ‖f m‖ₑ ^ 2 ∂MeasureTheory.Measure.count := by
  obtain ⟨C₁, hC₁pos, s₁, hMax⟩ := mstMaximal_single P hd l hl χ hχ hχ1 η hηc hη1 hηsup
  obtain ⟨C₂, hC₂pos, s₂, hOrth⟩ := mstOrthogonality P hd l hl χ hχ hχ1 η hηc hη1 hηsup δ hδ
  obtain ⟨C₃, hC₃pos, s₃, hFreeze⟩ := mstFreeze P hd l hl χ hχ hχ1 η hηc hη1 hηsup δ hδ
  obtain ⟨s₄, hNum⟩ := mstNumeric P hd l hl
  obtain ⟨s₅, hTor⟩ := mstTorsion l hl
  refine ⟨2 * (C₁ * C₂ + C₃ + 1), by positivity, max (max s₁ s₂) (max (max s₃ s₄) s₅), ?_⟩
  intro s hs G G0 hG0 hGdec hS hSeq f hf
  simp only [max_le_iff] at hs
  obtain ⟨⟨hs₁, hs₂⟩, ⟨⟨hs₃, hs₄⟩, hs₅⟩⟩ := hs
  have hGdec' : HasDecay G G0 l s δ := fun β hβ => hGdec β (by simpa [mstLvl] using hβ)
  obtain ⟨Mη, hMη⟩ : ∃ M : ℝ, ∀ x : ℝ, ‖η x‖ ≤ M := by
    obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Set.Icc (-(1 / 2) : ℝ) (1 / 2)) hηc.continuous.continuousOn
    refine ⟨max D 0, fun x => ?_⟩
    by_cases hx : |x| ≤ 1 / 2
    · exact le_trans (hD x (by rw [Set.mem_Icc]; exact abs_le.mp hx)) (le_max_left _ _)
    · rw [hηsup x (le_of_lt (not_le.mp hx)), norm_zero]
      exact le_max_right _ _
  have hmemψ : MemLp (mstEta P.natDegree χ η s) ⊤ mstHaar := by
    have h := (memLp_mst_symbols P 1 ((2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ))) η
      hηc.continuous).2.2
    have hfun : (fun ξ : mstCirc =>
        η ((2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) * iwRep ξ))
        = mstEta P.natDegree χ η s := by
      funext ξ; rw [mstEta_apply]
    rwa [hfun] at h
  have hmemprof : ∀ n : ℕ, MemLp (mstProf P (2 ^ n)) ⊤ mstHaar := fun n =>
    (memLp_mst_symbols P (2 ^ n) 1 η hηc.continuous).2.1
  have hmemprod : ∀ n : ℕ,
      MemLp (fun ξ : mstCirc => mstProf P (2 ^ n) ξ * mstEta P.natDegree χ η s ξ) ⊤ mstHaar :=
    fun n =>
      MemLp.of_bound (((hmemprof n).aestronglyMeasurable).mul hmemψ.aestronglyMeasurable) Mη
        (Filter.Eventually.of_forall fun ξ => by
          rw [norm_mul]
          have h1 : ‖mstProf P (2 ^ n) ξ‖ ≤ 1 := by
            rw [mstProf_apply]; exact norm_polyProfile_le_one P (2 ^ n) (iwRep ξ)
          calc ‖mstProf P (2 ^ n) ξ‖ * ‖mstEta P.natDegree χ η s ξ‖
              ≤ 1 * Mη := mul_le_mul h1 (hMη _) (norm_nonneg _) (by norm_num)
            _ = Mη := one_mul Mη)
  let hB : ∀ n : ℕ, Lp ℂ ⊤ mstHaar := fun n =>
    (hmemprod n).toLp (fun ξ => mstProf P (2 ^ n) ξ * mstEta P.natDegree χ η s ξ)
  have hBmodel : HasModel P P.natDegree χ η s hB := fun n => (hmemprod n).coeFn_toLp
  let hBψ : Lp ℂ ⊤ mstHaar := hmemψ.toLp (mstEta P.natDegree χ η s)
  have hBψbump : HasBump P.natDegree χ η s hBψ := hmemψ.coeFn_toLp
  have hmemA : ∀ n : ℕ, MemLp (mstModelFn G (mstProf P (2 ^ n))
      (mstEta P.natDegree χ η s) (mstLvl l s)) ⊤ mstHaar := fun n => by
    have h := memLp_arcSymbolW (fun β : mstCirc => β) G (mstLvl l s) (hmemprod n)
    simpa only [mstModelFn] using h
  let X : ℝ := ((s : ℝ) + 1) ^ (-(δ * l))
  have X0 : 0 ≤ X := by
    dsimp only [X]; exact Real.rpow_nonneg (by positivity) _
  have hQE : ∀ β ∈ mstLvl l s, fourier (mstQ' s : ℤ) β = 1 := fun β hβ =>
    hTor s hs₅ β (Finset.mem_sdiff.mp (by simpa only [mstLvl] using hβ)).1
  have hQpos : 0 < mstQ' s := mstQ'_pos s
  let J : ℤ → ℤ → ℝ≥0∞ := fun v y => ⨆ n : ℕ, ⨆ (_ : mstN₀' P s ≤ n),
      ‖opMul (hB n) (mstModSeq G (mstLvl l s) f v) (memℒp_mstModSeq hf v) y‖ₑ
  let R : ℝ≥0∞ := ∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count
  let err : ℝ := C₃ * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ))) * (mstQ' s : ℝ)
      * X * G0 * ((mstLvl l s).card : ℝ)
  let E : ℝ≥0∞ := ENNReal.ofReal (err ^ 2)
  have hJperiod : ∀ v y : ℤ, J (v + (mstQ' s : ℤ)) y = J v y := by
    intro v y
    have hseq := asm_mstModSeq_period G (mstLvl l s) (mstQ' s) hQE f v
    have hop : ∀ n : ℕ, opMul (hB n) (mstModSeq G (mstLvl l s) f (v + (mstQ' s : ℤ)))
          (memℒp_mstModSeq hf (v + (mstQ' s : ℤ)))
        = opMul (hB n) (mstModSeq G (mstLvl l s) f v) (memℒp_mstModSeq hf v) :=
      fun n => asm_opMul_congr hseq _ _
    dsimp only [J]
    refine iSup_congr fun n => iSup_congr fun _ => ?_
    rw [hop n]
  have hAnti : ∀ m : ℤ, (⨆ n : ℕ, ⨆ (_ : 2 ^ (20 * P.natDegree *
      (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1)) ≤ n), ‖opMul (hS n) f hf m‖ₑ) = J m m := by
    intro m
    dsimp only [J]
    refine iSup_congr fun n => iSup_congr fun _ => ?_
    have hcls : hS n = MemLp.toLp (mstModelFn G (mstProf P (2 ^ n)) (mstEta P.natDegree χ η s)
        (mstLvl l s)) (hmemA n) := by
      refine Lp.ext ?_
      filter_upwards [hSeq n, (hmemA n).coeFn_toLp] with ξ h1 h2
      rw [h1, h2]
      simp only [mstLvl]
    rw [hcls]
    exact congrArg (fun z : ℂ => ‖z‖ₑ)
      (mstModelFn_modSeq P l P.natDegree χ η s n G f hf (hmemA n) (hmemprod n) m)
  let A : ℝ≥0∞ := ∫⁻ m : ℤ, (J m m) ^ (2 : ℝ) ∂MeasureTheory.Measure.count
  have hAeq : (∫⁻ m : ℤ, (⨆ n : ℕ, ⨆ (_ : 2 ^ (20 * P.natDegree *
        (⌊((s : ℝ) + 1) ^ (1 / 10 : ℝ)⌋₊ + 1)) ≤ n),
        ‖opMul (hS n) f hf m‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count) = A := by
    refine lintegral_congr fun m => ?_
    exact congrArg (fun t : ℝ≥0∞ => t ^ (2 : ℝ)) (hAnti m)
  rw [hAeq]
  let B : ℝ≥0∞ := ∑ u ∈ Finset.range (mstQ' s),
      (∫⁻ m : ℤ, (J (u : ℤ) m) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
  have hfreeze_u : ∀ u ∈ Finset.range (mstQ' s),
      A ≤ 2 * (∫⁻ m : ℤ, (J m (m + (u : ℤ))) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 2 * E * R := fun u hu =>
    hFreeze s hs₃ G G0 hG0 hGdec' hB hBmodel f hf u hu
  have hsum_freeze : (mstQ' s : ℝ≥0∞) * A
      ≤ 2 * (∑ u ∈ Finset.range (mstQ' s),
            (∫⁻ m : ℤ, (J m (m + (u : ℤ))) ^ (2 : ℝ) ∂MeasureTheory.Measure.count))
        + (mstQ' s : ℝ≥0∞) * (2 * E * R) := by
    calc (mstQ' s : ℝ≥0∞) * A = ∑ u ∈ Finset.range (mstQ' s), A := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ u ∈ Finset.range (mstQ' s),
            (2 * (∫⁻ m : ℤ, (J m (m + (u : ℤ))) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
              + 2 * E * R) := Finset.sum_le_sum hfreeze_u
      _ = (∑ u ∈ Finset.range (mstQ' s),
            (2 * (∫⁻ m : ℤ, (J m (m + (u : ℤ))) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)))
            + (∑ _u ∈ Finset.range (mstQ' s), (2 * E * R)) := by
          rw [Finset.sum_add_distrib]
      _ = 2 * (∑ u ∈ Finset.range (mstQ' s),
            (∫⁻ m : ℤ, (J m (m + (u : ℤ))) ^ (2 : ℝ) ∂MeasureTheory.Measure.count))
            + (mstQ' s : ℝ≥0∞) * (2 * E * R) := by
          rw [Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hrelabel : (∑ u ∈ Finset.range (mstQ' s),
        (∫⁻ m : ℤ, (J m (m + (u : ℤ))) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)) = B := by
    calc ∑ u ∈ Finset.range (mstQ' s),
          (∫⁻ m : ℤ, (J m (m + (u : ℤ))) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
        = ∑ u ∈ Finset.range (mstQ' s),
          (∫⁻ m : ℤ, (J (m - (u : ℤ)) m) ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :=
          Finset.sum_congr rfl (fun u _ => asm_lintegral_count_pair (fun a b : ℤ => (J a b) ^ (2 : ℝ)) (u : ℤ))
      _ = ∫⁻ m : ℤ, ∑ u ∈ Finset.range (mstQ' s),
            (J (m - (u : ℤ)) m) ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
          (lintegral_finsetSum _ (fun u _ => measurable_of_countable _)).symm
      _ = ∫⁻ m : ℤ, ∑ u ∈ Finset.range (mstQ' s),
            (J (u : ℤ) m) ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
          refine lintegral_congr fun m => ?_
          exact asm_sum_range_sub_period (fun v : ℤ => (J v m) ^ (2 : ℝ)) (mstQ' s) hQpos
            (fun v => by rw [hJperiod v m]) m
      _ = B := lintegral_finsetSum _ (fun u _ => measurable_of_countable _)
  have hmax_u : ∀ u ∈ Finset.range (mstQ' s),
      (∫⁻ m : ℤ, (J (u : ℤ) m) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal (C₁ ^ 2)
          * (∫⁻ m : ℤ, ‖opMul hBψ (mstModSeq G (mstLvl l s) f u) (memℒp_mstModSeq hf u) m‖ₑ
              ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := fun u _ =>
    hMax s hs₁ (mstModSeq G (mstLvl l s) f u) (memℒp_mstModSeq hf u) hB hBmodel hBψ hBψbump
  have horth_sum : (∑ u ∈ Finset.range (mstQ' s),
        (∫⁻ m : ℤ, ‖opMul hBψ (mstModSeq G (mstLvl l s) f u) (memℒp_mstModSeq hf u) m‖ₑ
          ^ (2 : ℝ) ∂MeasureTheory.Measure.count))
      ≤ ENNReal.ofReal ((C₂ * G0 * X) ^ 2) * ((mstQ' s : ℝ≥0∞) * R) :=
    hOrth s hs₂ G G0 hG0 hGdec' hBψ hBψbump f hf
  have hB_le : B ≤ ENNReal.ofReal ((C₁ * C₂ * G0 * X) ^ 2) * ((mstQ' s : ℝ≥0∞) * R) := by
    have hcoef : ENNReal.ofReal (C₁ ^ 2) * ENNReal.ofReal ((C₂ * G0 * X) ^ 2)
        = ENNReal.ofReal ((C₁ * C₂ * G0 * X) ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C₁ ^ 2)]
      congr 1
      ring
    calc B = ∑ u ∈ Finset.range (mstQ' s),
            (∫⁻ m : ℤ, (J (u : ℤ) m) ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := rfl
      _ ≤ ∑ u ∈ Finset.range (mstQ' s), ENNReal.ofReal (C₁ ^ 2) *
            (∫⁻ m : ℤ, ‖opMul hBψ (mstModSeq G (mstLvl l s) f u) (memℒp_mstModSeq hf u) m‖ₑ
              ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := Finset.sum_le_sum hmax_u
      _ = ENNReal.ofReal (C₁ ^ 2) * (∑ u ∈ Finset.range (mstQ' s),
            (∫⁻ m : ℤ, ‖opMul hBψ (mstModSeq G (mstLvl l s) f u) (memℒp_mstModSeq hf u) m‖ₑ
              ^ (2 : ℝ) ∂MeasureTheory.Measure.count)) := by
          rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal (C₁ ^ 2) * (ENNReal.ofReal ((C₂ * G0 * X) ^ 2)
            * ((mstQ' s : ℝ≥0∞) * R)) :=
          mul_le_mul_right horth_sum (ENNReal.ofReal (C₁ ^ 2))
      _ = ENNReal.ofReal ((C₁ * C₂ * G0 * X) ^ 2) * ((mstQ' s : ℝ≥0∞) * R) := by
          rw [← mul_assoc, hcoef]
  have hsum_freeze' : (mstQ' s : ℝ≥0∞) * A ≤ 2 * B + (mstQ' s : ℝ≥0∞) * (2 * E * R) := by
    have h := hsum_freeze
    rw [hrelabel] at h
    exact h
  have herr0 : 0 ≤ err := by
    dsimp only [err]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₃pos.le
      (Real.rpow_nonneg (by norm_num) _)) (Nat.cast_nonneg _)) X0) hG0) (Nat.cast_nonneg _)
  have herr : err ≤ C₃ * G0 * X := by
    have hnum := hNum s hs₄
    dsimp only [err]
    calc C₃ * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ))) * (mstQ' s : ℝ) * X * G0
          * ((mstLvl l s).card : ℝ)
        = (C₃ * X * G0) * ((2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ)))
            * (mstQ' s : ℝ) * ((mstLvl l s).card : ℝ)) := by ring
      _ ≤ (C₃ * X * G0) * 1 :=
          mul_le_mul_of_nonneg_left hnum (mul_nonneg (mul_nonneg hC₃pos.le X0) hG0)
      _ = C₃ * G0 * X := by ring
  have hZ0 : 0 ≤ C₃ * G0 * X := mul_nonneg (mul_nonneg hC₃pos.le hG0) X0
  have hE_le : E ≤ ENNReal.ofReal ((C₃ * G0 * X) ^ 2) := by
    dsimp only [E]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [herr, herr0, hZ0]
  have hE2_le : 2 * E * R ≤ (2 * ENNReal.ofReal ((C₃ * G0 * X) ^ 2)) * R :=
    mul_le_mul_left (mul_le_mul_right hE_le 2) R
  have hfinal : A ≤ ENNReal.ofReal ((2 * (C₁ * C₂ + C₃ + 1) * G0 * X) ^ 2) * R := by
    have hQne : (mstQ' s : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact (mstQ'_pos s).ne'
    have hQtop : (mstQ' s : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hstep : A ≤ (mstQ' s : ℝ≥0∞)⁻¹ * (2 * B + (mstQ' s : ℝ≥0∞) * (2 * E * R)) := by
      refine (ENNReal.mul_le_mul_iff_right hQne hQtop).mp ?_
      rw [← mul_assoc, ENNReal.mul_inv_cancel hQne hQtop, one_mul]
      exact hsum_freeze'
    have hsimp : (mstQ' s : ℝ≥0∞)⁻¹ * (2 * (ENNReal.ofReal ((C₁ * C₂ * G0 * X) ^ 2)
          * ((mstQ' s : ℝ≥0∞) * R)))
        = 2 * ENNReal.ofReal ((C₁ * C₂ * G0 * X) ^ 2) * R := by
      rw [show (mstQ' s : ℝ≥0∞)⁻¹ * (2 * (ENNReal.ofReal ((C₁ * C₂ * G0 * X) ^ 2)
            * ((mstQ' s : ℝ≥0∞) * R)))
          = 2 * ENNReal.ofReal ((C₁ * C₂ * G0 * X) ^ 2)
            * ((mstQ' s : ℝ≥0∞)⁻¹ * (mstQ' s : ℝ≥0∞)) * R from by ring]
      rw [ENNReal.inv_mul_cancel hQne hQtop, mul_one]
    have hof : 2 * ENNReal.ofReal ((C₁ * C₂ * G0 * X) ^ 2)
          + 2 * ENNReal.ofReal ((C₃ * G0 * X) ^ 2)
        = ENNReal.ofReal (2 * (C₁ * C₂ * G0 * X) ^ 2 + 2 * (C₃ * G0 * X) ^ 2) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    have hreal : 2 * (C₁ * C₂ * G0 * X) ^ 2 + 2 * (C₃ * G0 * X) ^ 2
        ≤ (2 * (C₁ * C₂ + C₃ + 1) * G0 * X) ^ 2 := by
      have h1 : (C₁ * C₂) ^ 2 + C₃ ^ 2 ≤ 2 * (C₁ * C₂ + C₃ + 1) ^ 2 := by
        nlinarith [mul_nonneg hC₁pos.le hC₂pos.le, hC₃pos.le]
      have h2 : 2 * ((C₁ * C₂) ^ 2 + C₃ ^ 2) ≤ 4 * (C₁ * C₂ + C₃ + 1) ^ 2 := by linarith
      calc 2 * (C₁ * C₂ * G0 * X) ^ 2 + 2 * (C₃ * G0 * X) ^ 2
          = 2 * ((C₁ * C₂) ^ 2 + C₃ ^ 2) * (G0 * X) ^ 2 := by ring
        _ ≤ 4 * (C₁ * C₂ + C₃ + 1) ^ 2 * (G0 * X) ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = (2 * (C₁ * C₂ + C₃ + 1) * G0 * X) ^ 2 := by ring
    calc A ≤ (mstQ' s : ℝ≥0∞)⁻¹ * (2 * B + (mstQ' s : ℝ≥0∞) * (2 * E * R)) := hstep
      _ = (mstQ' s : ℝ≥0∞)⁻¹ * (2 * B) + (2 * E * R) := by
          rw [mul_add]
          rw [show (mstQ' s : ℝ≥0∞)⁻¹ * ((mstQ' s : ℝ≥0∞) * (2 * E * R)) = (2 * E * R) from by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hQne hQtop, one_mul]]
      _ ≤ (mstQ' s : ℝ≥0∞)⁻¹ * (2 * (ENNReal.ofReal ((C₁ * C₂ * G0 * X) ^ 2)
            * ((mstQ' s : ℝ≥0∞) * R))) + (2 * ENNReal.ofReal ((C₃ * G0 * X) ^ 2)) * R :=
          add_le_add (mul_le_mul_right (mul_le_mul_right hB_le 2) _) hE2_le
      _ = 2 * ENNReal.ofReal ((C₁ * C₂ * G0 * X) ^ 2) * R
            + (2 * ENNReal.ofReal ((C₃ * G0 * X) ^ 2)) * R := by rw [hsimp]
      _ = (2 * ENNReal.ofReal ((C₁ * C₂ * G0 * X) ^ 2)
            + 2 * ENNReal.ofReal ((C₃ * G0 * X) ^ 2)) * R := by ring
      _ ≤ ENNReal.ofReal ((2 * (C₁ * C₂ + C₃ + 1) * G0 * X) ^ 2) * R := by
          rw [hof]
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hreal) R
  rw [show (∫⁻ m : ℤ, ‖f m‖ₑ ^ 2 ∂MeasureTheory.Measure.count) = R from by
        dsimp only [R]
        refine lintegral_congr fun m => ?_
        exact (ENNReal.rpow_two _).symm]
  exact hfinal

end

end Work.BourgainPlan.Maximal
