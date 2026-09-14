import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Commons.Analysis.Calculus

open Filter Set MeasureTheory intervalIntegral Topology

/-- Fundamental-theorem-of-calculus comparison: if `φ` is differentiable on `(a,b)`, continuous
on `[a,b]` with integrable derivative and `deriv φ x ≤ K / x` on `(a,b)` with `0 < a ≤ b`, then
`φ b - φ a ≤ K * log (b / a)`. -/
lemma sub_le_mul_log_of_deriv_le {φ : ℝ → ℝ} {K a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hcont : ContinuousOn φ (Icc a b))
    (hder : ∀ x ∈ Ioo a b, HasDerivAt φ (deriv φ x) x)
    (hi : IntervalIntegrable (deriv φ) volume a b)
    (hle : ∀ x ∈ Ioo a b, deriv φ x ≤ K / x) :
    φ b - φ a ≤ K * Real.log (b / a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hFTC : φ b - φ a = ∫ x in a..b, deriv φ x :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hder hi).symm
  rw [hFTC]
  have hgcont : ContinuousOn (fun x : ℝ => K / x) (Icc a b) := by
    refine continuousOn_const.div continuousOn_id (fun x hx => ?_)
    simp only [mem_Icc] at hx
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hg : IntervalIntegrable (fun x : ℝ => K / x) volume a b :=
    hgcont.intervalIntegrable_of_Icc hab
  have hmono : ∫ x in a..b, deriv φ x ≤ ∫ x in a..b, K / x :=
    intervalIntegral.integral_mono_on_of_le_Ioo hab hi hg hle
  have hcalc : (∫ x in a..b, K / x) = K * Real.log (b / a) := by
    have h1 : (fun x : ℝ => K / x) = fun x => K * x⁻¹ := by ext x; rw [div_eq_mul_inv]
    rw [h1, intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
  linarith [hmono, hcalc]

/-- If the running averages `t ↦ t⁻¹ ∫_0^t φ` tend to `η` as `t → 0⁺`, then arbitrarily close
to `0⁺` (within `(0,ε)`) the function `φ` takes values below `η + c`, for every `c > 0`. -/
lemma exists_le_near_zero_of_tendsto_average {φ : ℝ → ℝ} {η ε c : ℝ} (hε : 0 < ε)
    (hint0 : ∀ t ∈ Ioo (0:ℝ) ε, IntervalIntegrable φ volume 0 t)
    (havg : Tendsto (fun t : ℝ => t⁻¹ * ∫ s in (0:ℝ)..t, φ s)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds η))
    (hc : 0 < c) :
    ∀ σ, 0 < σ → σ ≤ ε → ∃ s ∈ Ioo (0:ℝ) σ, φ s ≤ η + c := by
  intro σ hσ hσε
  by_contra h
  push_neg at h
  have hlt : η < η + c := by linarith
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), t⁻¹ * ∫ s in (0:ℝ)..t, φ s < η + c :=
    (tendsto_order.1 havg).2 (η + c) hlt
  rw [(nhdsGT_basis (0:ℝ)).eventually_iff] at hev
  obtain ⟨ρ, hρ, hρP⟩ := hev
  set τ := min σ (min ρ (ε/2)) / 2 with hτdef
  have hτpos : 0 < τ := by
    rw [hτdef]
    have h1 : (0:ℝ) < min ρ (ε/2) := lt_min hρ (show (0:ℝ) < ε/2 by linarith)
    have h2 : (0:ℝ) < min σ (min ρ (ε/2)) := lt_min hσ h1
    linarith
  have hτσ : τ < σ := by
    rw [hτdef]; have := min_le_left σ (min ρ (ε/2)); linarith
  have hτρ : τ < ρ := by
    rw [hτdef]
    have h1 : min σ (min ρ (ε/2)) ≤ min ρ (ε/2) := min_le_right _ _
    have h2 : min ρ (ε/2) ≤ ρ := min_le_left _ _
    linarith
  have hτε : τ < ε := by
    rw [hτdef]
    have h1 : min σ (min ρ (ε/2)) ≤ min ρ (ε/2) := min_le_right _ _
    have h2 : min ρ (ε/2) ≤ ε/2 := min_le_right _ _
    linarith
  have hτmem : τ ∈ Ioo (0:ℝ) ε := ⟨hτpos, hτε⟩
  have hile : (∫ s in (0:ℝ)..τ, (fun _ => η + c) s) ≤ ∫ s in (0:ℝ)..τ, φ s := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt hτpos)
    · exact intervalIntegrable_const
    · exact hint0 τ hτmem
    · intro x hx
      exact le_of_lt (h x ⟨hx.1, lt_trans hx.2 hτσ⟩)
  have hconst : (∫ s in (0:ℝ)..τ, (fun _ => η + c) s) = (η + c) * τ := by
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have havτ_ge : η + c ≤ τ⁻¹ * ∫ s in (0:ℝ)..τ, φ s := by
    have hthis : (η + c) * τ ≤ ∫ s in (0:ℝ)..τ, φ s := by rw [← hconst]; exact hile
    calc η + c = τ⁻¹ * ((η + c) * τ) := by
            rw [mul_comm (η + c) τ, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hτpos), one_mul]
      _ ≤ τ⁻¹ * ∫ s in (0:ℝ)..τ, φ s :=
            mul_le_mul_of_nonneg_left hthis (le_of_lt (inv_pos.mpr hτpos))
  have havτ_lt : τ⁻¹ * ∫ s in (0:ℝ)..τ, φ s < η + c := hρP ⟨hτpos, hτρ⟩
  linarith

/-- Crossing-pair lemma. -/
lemma exists_crossing_pair {φ : ℝ → ℝ} {η δ s0 tn : ℝ} (hδ : 0 < δ) (hs0t : s0 < tn)
    (hcont : ContinuousOn φ (Icc s0 tn)) (hφs0 : φ s0 ≤ η + δ/2) (hφtn : η + δ ≤ φ tn) :
    ∃ cn bn : ℝ, s0 ≤ cn ∧ cn < tn ∧ φ cn ≤ η + δ / 2 ∧ cn < bn ∧ bn ≤ tn ∧
      η + δ ≤ φ bn ∧ ∀ s ∈ Ioo cn bn, η + δ / 2 < φ s ∧ φ s < η + δ := by
  have hScl : IsClosed {s : ℝ | s ∈ Icc s0 tn ∧ φ s ≤ η + δ / 2} := by
    have h := hcont.preimage_isClosed_of_isClosed (isClosed_Icc (a := s0) (b := tn)) (isClosed_Iic (a := η + δ / 2))
    simpa only [Set.inter_def, Set.mem_preimage, Set.mem_Iic] using h
  have hSne : ({s : ℝ | s ∈ Icc s0 tn ∧ φ s ≤ η + δ / 2}).Nonempty :=
    ⟨s0, by simp only [Set.mem_setOf_eq, left_mem_Icc.mpr hs0t.le, hφs0, and_self]⟩
  have hSbdd : BddAbove {s : ℝ | s ∈ Icc s0 tn ∧ φ s ≤ η + δ / 2} :=
    ⟨tn, fun x hx => hx.1.2⟩
  set cn := sSup {s : ℝ | s ∈ Icc s0 tn ∧ φ s ≤ η + δ / 2} with hcndef
  have hcnmem : cn ∈ {s : ℝ | s ∈ Icc s0 tn ∧ φ s ≤ η + δ / 2} :=
    hScl.csSup_mem hSne hSbdd
  have hcn_ge : s0 ≤ cn := hcnmem.1.1
  have hcn_le_tn : cn ≤ tn := hcnmem.1.2
  have hcn_phi : φ cn ≤ η + δ / 2 := hcnmem.2
  have hcn_lt_tn : cn < tn := by
    rcases lt_or_eq_of_le hcn_le_tn with h | h
    · exact h
    · exfalso
      have hφ : φ cn = φ tn := by rw [h]
      linarith [hφtn, hcn_phi, hδ]
  have hgt : ∀ s ∈ Ioo cn tn, η + δ / 2 < φ s := by
    intro s hs
    by_contra hle
    push_neg at hle
    have hsS : s ∈ {s : ℝ | s ∈ Icc s0 tn ∧ φ s ≤ η + δ / 2} :=
      ⟨⟨le_of_lt (lt_of_le_of_lt hcn_ge hs.1), le_of_lt hs.2⟩, hle⟩
    have hle' := le_csSup hSbdd hsS
    rw [← hcndef] at hle'
    linarith [hs.1]
  have hTcl : IsClosed {s : ℝ | s ∈ Icc cn tn ∧ η + δ ≤ φ s} := by
    have hcont' : ContinuousOn φ (Icc cn tn) := hcont.mono (Icc_subset_Icc hcn_ge le_rfl)
    have h := hcont'.preimage_isClosed_of_isClosed (isClosed_Icc (a := cn) (b := tn)) (isClosed_Ici (a := η + δ))
    simpa only [Set.inter_def, Set.mem_preimage, Set.mem_Ici] using h
  have hTne : ({s : ℝ | s ∈ Icc cn tn ∧ η + δ ≤ φ s}).Nonempty :=
    ⟨tn, by simp only [Set.mem_setOf_eq, right_mem_Icc.mpr hcn_le_tn, hφtn, and_self]⟩
  have hTbdd : BddBelow {s : ℝ | s ∈ Icc cn tn ∧ η + δ ≤ φ s} :=
    ⟨cn, fun x hx => hx.1.1⟩
  set bn := sInf {s : ℝ | s ∈ Icc cn tn ∧ η + δ ≤ φ s} with hbndef
  have hbnmem : bn ∈ {s : ℝ | s ∈ Icc cn tn ∧ η + δ ≤ φ s} :=
    hTcl.csInf_mem hTne hTbdd
  have hbn_ge_cn : cn ≤ bn := hbnmem.1.1
  have hbn_le_tn : bn ≤ tn := hbnmem.1.2
  have hbn_phi : η + δ ≤ φ bn := hbnmem.2
  have hcn_lt_bn : cn < bn := by
    refine lt_of_le_of_ne hbn_ge_cn (fun heq => ?_)
    have hφ : φ cn = φ bn := by rw [heq]
    linarith [hbn_phi, hcn_phi, hδ]
  have hlt : ∀ s ∈ Ioo cn bn, φ s < η + δ := by
    intro s hs
    by_contra hle
    push_neg at hle
    have hsS : s ∈ {s : ℝ | s ∈ Icc cn tn ∧ η + δ ≤ φ s} :=
      ⟨⟨le_of_lt hs.1, le_trans (le_of_lt hs.2) hbn_le_tn⟩, hle⟩
    have hle' := csInf_le hTbdd hsS
    rw [← hbndef] at hle'
    linarith [hs.2]
  exact ⟨cn, bn, hcn_ge, hcn_lt_tn, hcn_phi, hcn_lt_bn, hbn_le_tn, hbn_phi,
    fun s hs => ⟨hgt s ⟨hs.1, lt_of_lt_of_le hs.2 hbn_le_tn⟩, hlt s hs⟩⟩

/-- **Upper-half lemma.**  If `φ` has running averages tending to `η` at `0⁺`, and on `(0,ε)` its
right derivative is bounded above by `A (φ t) / t` with `A` continuous, then for every `δ > 0`
we have `φ t < η + δ` for all sufficiently small `t > 0`. -/
lemma eventually_lt_nhdsGT_of_deriv_lt_of_tendsto_average {φ : ℝ → ℝ} {η ε : ℝ} (hε : 0 < ε)
    (hderiv : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt φ (deriv φ t) t)
    (hint : ∀ a b : ℝ, 0 < a → a ≤ b → b < ε → IntervalIntegrable (deriv φ) volume a b)
    (hint0 : ∀ t ∈ Ioo (0:ℝ) ε, IntervalIntegrable φ volume 0 t)
    (havg : Tendsto (fun t : ℝ => t⁻¹ * ∫ s in (0:ℝ)..t, φ s)
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds η))
    {A : ℝ → ℝ} (hAc : Continuous A)
    (hAb : ∀ t ∈ Ioo (0:ℝ) ε, deriv φ t < A (φ t) / t) :
    ∀ δ > 0, ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), φ t < η + δ := by
  intro δ hδ
  rw [(nhdsGT_basis (0:ℝ)).eventually_iff]
  by_contra hcon
  push_neg at hcon
  have hcont_eps : ContinuousOn φ (Ioo (0:ℝ) ε) := HasDerivAt.continuousOn hderiv
  have hminpos : ∀ n : ℕ, (0:ℝ) < min (1/((n:ℝ)+1)) (ε/2) := fun n =>
    lt_min (by positivity) (show (0:ℝ) < ε/2 by linarith)
  choose t ht using fun n : ℕ => hcon (min (1/((n:ℝ)+1)) (ε/2)) (hminpos n)
  have ht_mem : ∀ n : ℕ, t n ∈ Ioo (0:ℝ) (min (1/((n:ℝ)+1)) (ε/2)) := fun n => (ht n).1
  have ht_high : ∀ n : ℕ, η + δ ≤ φ (t n) := fun n => (ht n).2
  have ht_pos : ∀ n : ℕ, 0 < t n := fun n => (ht_mem n).1
  have ht_lt_eps : ∀ n : ℕ, t n < ε := fun n =>
    lt_of_lt_of_le (ht_mem n).2 (le_trans (min_le_right _ _) (show (ε/2:ℝ) ≤ ε by linarith))
  have ht_lt_tn : ∀ n : ℕ, t n < 1/((n:ℝ)+1) := fun n => lt_of_lt_of_le (ht_mem n).2 (min_le_left _ _)
  have ht_tendsto : Tendsto t atTop (nhds 0) :=
    squeeze_zero (fun n => le_of_lt (ht_pos n)) (fun n => le_of_lt (ht_lt_tn n))
      tendsto_one_div_add_atTop_nhds_zero_nat
  -- low points s0 n
  choose s0 hs0_mem hs0_le using fun n : ℕ =>
    exists_le_near_zero_of_tendsto_average (c := δ/2) hε hint0 havg (by linarith) (t n) (ht_pos n)
      (le_of_lt (ht_lt_eps n))
  have hs0_pos : ∀ n : ℕ, 0 < s0 n := fun n => (hs0_mem n).1
  have hs0_lt_t : ∀ n : ℕ, s0 n < t n := fun n => (hs0_mem n).2
  have hcont_s0 : ∀ n : ℕ, ContinuousOn φ (Icc (s0 n) (t n)) := fun n =>
    hcont_eps.mono (fun x hx => ⟨lt_of_lt_of_le (hs0_pos n) hx.1, lt_of_le_of_lt hx.2 (ht_lt_eps n)⟩)
  -- crossing pair
  choose cn bn hproperties using fun n : ℕ =>
    exists_crossing_pair hδ (hs0_lt_t n) (hcont_s0 n) (hs0_le n) (ht_high n)
  have hcn_ge_s0 : ∀ n : ℕ, s0 n ≤ cn n := fun n => (hproperties n).1
  have hcn_lt_t : ∀ n : ℕ, cn n < t n := fun n => (hproperties n).2.1
  have hcnphi : ∀ n : ℕ, φ (cn n) ≤ η + δ/2 := fun n => (hproperties n).2.2.1
  have hcn_lt_bn : ∀ n : ℕ, cn n < bn n := fun n => (hproperties n).2.2.2.1
  have hbn_le_t : ∀ n : ℕ, bn n ≤ t n := fun n => (hproperties n).2.2.2.2.1
  have hbnphi : ∀ n : ℕ, η + δ ≤ φ (bn n) := fun n => (hproperties n).2.2.2.2.2.1
  have hprop : ∀ n : ℕ, ∀ s ∈ Ioo (cn n) (bn n), η + δ/2 < φ s ∧ φ s < η + δ :=
    fun n => (hproperties n).2.2.2.2.2.2
  have hcnpos : ∀ n : ℕ, 0 < cn n := fun n => lt_of_lt_of_le (hs0_pos n) (hcn_ge_s0 n)
  have hbnpos : ∀ n : ℕ, 0 < bn n := fun n => lt_trans (hcnpos n) (hcn_lt_bn n)
  have hcn_le_bn : ∀ n : ℕ, cn n ≤ bn n := fun n => le_of_lt (hcn_lt_bn n)
  have hbn_lt_eps : ∀ n : ℕ, bn n < ε := fun n => lt_of_le_of_lt (hbn_le_t n) (ht_lt_eps n)
  have hcn_lt_eps : ∀ n : ℕ, cn n < ε := fun n => lt_of_le_of_lt (hcn_le_bn n) (hbn_lt_eps n)
  -- integrability on the crossing interval
  have hicnbn : ∀ n : ℕ, IntervalIntegrable φ volume (cn n) (bn n) := fun n => by
    have hmem1 : cn n ∈ uIcc (0:ℝ) (bn n) := by
      rw [uIcc_of_le (le_of_lt (hbnpos n))]; exact ⟨le_of_lt (hcnpos n), hcn_le_bn n⟩
    have hmem2 : bn n ∈ uIcc (0:ℝ) (bn n) := by
      rw [uIcc_of_le (le_of_lt (hbnpos n))]; exact ⟨le_of_lt (hbnpos n), le_rfl⟩
    exact (hint0 (bn n) ⟨hbnpos n, hbn_lt_eps n⟩).mono_set (uIcc_subset_uIcc hmem1 hmem2)
  -- the constant K bounding A on the range of φ over the crossing
  obtain ⟨x0, _, hx0max⟩ := (isCompact_Icc (a := η + δ/2) (b := η + δ)).exists_isMaxOn
    ⟨η + δ/2, left_mem_Icc.mpr (by linarith)⟩ hAc.continuousOn
  set K := A x0 with hKdef
  have hKbound : ∀ y ∈ Icc (η + δ/2) (η + δ), A y ≤ K := fun y hy => hx0max hy
  -- crossing bound
  have hcross : ∀ n : ℕ, φ (bn n) - φ (cn n) ≤ K * Real.log (bn n / cn n) := by
    intro n
    apply sub_le_mul_log_of_deriv_le (hcnpos n) (hcn_le_bn n)
    · exact hcont_eps.mono (fun x hx =>
        ⟨lt_of_lt_of_le (hcnpos n) hx.1, lt_of_le_of_lt hx.2 (hbn_lt_eps n)⟩)
    · intro x hx
      exact hderiv x ⟨lt_trans (hcnpos n) hx.1, lt_trans hx.2 (hbn_lt_eps n)⟩
    · exact hint (cn n) (bn n) (hcnpos n) (hcn_le_bn n) (hbn_lt_eps n)
    · intro x hx
      have hxpos : 0 < x := lt_trans (hcnpos n) hx.1
      have hφx : φ x ∈ Icc (η + δ/2) (η + δ) :=
        ⟨le_of_lt (hprop n x hx).1, le_of_lt (hprop n x hx).2⟩
      have hh := hAb x ⟨lt_trans (hcnpos n) hx.1, lt_trans hx.2 (hbn_lt_eps n)⟩
      have hdiv : A (φ x) / x ≤ K / x := div_le_div_of_nonneg_right (hKbound (φ x) hφx) (le_of_lt hxpos)
      linarith [hh, hdiv]
  have hlogpos : ∀ n : ℕ, 0 < Real.log (bn n / cn n) := fun n =>
    Real.log_pos ((one_lt_div (hcnpos n)).mpr (hcn_lt_bn n))
  have hhalf : ∀ n : ℕ, δ/2 ≤ K * Real.log (bn n / cn n) := fun n => by
    have h1 := hcross n
    have h2 : δ/2 ≤ φ (bn n) - φ (cn n) := by linarith [hbnphi n, hcnphi n]
    linarith
  have hKpos : 0 < K := by nlinarith [hhalf 0, hlogpos 0, hδ]
  set ρ := Real.exp (δ / (2 * K)) with hρdef
  have hρpos : 0 < ρ := Real.exp_pos _
  have hρgt1 : 1 < ρ := by
    rw [hρdef]; exact Real.one_lt_exp_iff.mpr (by positivity)
  have hbc_ge : ∀ n : ℕ, ρ ≤ bn n / cn n := fun n => by
    have hlog : δ / (2 * K) ≤ Real.log (bn n / cn n) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * K)]
      nlinarith [hhalf n]
    calc Real.exp (δ / (2 * K)) ≤ Real.exp (Real.log (bn n / cn n)) := Real.exp_le_exp.mpr hlog
      _ = bn n / cn n := Real.exp_log (div_pos (hbnpos n) (hcnpos n))
  have hcnbn_le : ∀ n : ℕ, cn n / bn n ≤ 1 / ρ := fun n => by
    have h1 : ρ * cn n ≤ bn n := (le_div_iff₀ (hcnpos n)).mp (hbc_ge n)
    rw [div_le_div_iff₀ (hbnpos n) hρpos]
    nlinarith [h1]
  have hcnbn_nonneg : ∀ n : ℕ, 0 ≤ cn n / bn n := fun n =>
    div_nonneg (le_of_lt (hcnpos n)) (le_of_lt (hbnpos n))
  -- Chasles
  have hChasles : ∀ n : ℕ, (∫ s in (0:ℝ)..bn n, φ s) = (∫ s in (0:ℝ)..cn n, φ s) + (∫ s in cn n..bn n, φ s) :=
    fun n => (intervalIntegral.integral_add_adjacent_intervals
      (hint0 (cn n) ⟨hcnpos n, hcn_lt_eps n⟩) (hicnbn n)).symm
  have hlow : ∀ n : ℕ, (δ/2) * (bn n - cn n) ≤ ∫ s in cn n..bn n, (φ s - η) := by
    intro n
    have hint2 : IntervalIntegrable (fun s => φ s - η) volume (cn n) (bn n) :=
      (hicnbn n).sub intervalIntegrable_const
    have hmono : (∫ s in cn n..bn n, (fun _ => δ/2) s) ≤ ∫ s in cn n..bn n, (φ s - η) :=
      intervalIntegral.integral_mono_on_of_le_Ioo (hcn_le_bn n) intervalIntegrable_const hint2
        (fun x hx => by have := (hprop n x hx).1; linarith)
    have hci : (∫ s in cn n..bn n, (fun _ => δ/2) s) = (δ/2)*(bn n - cn n) := by
      rw [intervalIntegral.integral_const]; simp only [smul_eq_mul]; ring
    rwa [hci] at hmono
  have havg_eq : ∀ n : ℕ, (bn n)⁻¹ * (∫ s in (0:ℝ)..bn n, φ s) - η =
      (cn n / bn n) * ((cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η)
        + (bn n)⁻¹ * (∫ s in cn n..bn n, (φ s - η)) := by
    intro n
    have hsub : (∫ s in cn n..bn n, (φ s - η)) = (∫ s in cn n..bn n, φ s) - η * (bn n - cn n) := by
      rw [intervalIntegral.integral_sub (hicnbn n) intervalIntegrable_const,
          intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring_nf
    rw [hChasles n, hsub]
    field_simp [ne_of_gt (hcnpos n), ne_of_gt (hbnpos n)]
    ring
  have hbound : ∀ n : ℕ, (bn n)⁻¹ * (∫ s in (0:ℝ)..bn n, φ s) - η ≥
      (cn n / bn n) * ((cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η) + (δ/2)*(1 - 1/ρ) := by
    intro n
    have h1 := havg_eq n
    have h2 : (bn n)⁻¹ * ((δ/2) * (bn n - cn n)) ≤ (bn n)⁻¹ * (∫ s in cn n..bn n, (φ s - η)) :=
      mul_le_mul_of_nonneg_left (hlow n) (le_of_lt (inv_pos.mpr (hbnpos n)))
    have h3 : (bn n)⁻¹ * ((δ/2) * (bn n - cn n)) = (δ/2) * (1 - cn n / bn n) := by
      field_simp [ne_of_gt (hbnpos n)]
    have h4 : (δ/2) * (1 - 1/ρ) ≤ (δ/2) * (1 - cn n / bn n) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith [hcnbn_le n]
    linarith [h1, h2, h3, h4]
  -- limits
  have hcn_tendsto0 : Tendsto (fun n => cn n) atTop (nhds 0) :=
    squeeze_zero (fun n => le_of_lt (hcnpos n)) (fun n => le_trans (hcn_le_bn n) (hbn_le_t n)) ht_tendsto
  have hbn_tendsto0 : Tendsto (fun n => bn n) atTop (nhds 0) :=
    squeeze_zero (fun n => le_of_lt (hbnpos n)) (fun n => hbn_le_t n) ht_tendsto
  have hcn_nhds : Tendsto (fun n => cn n) atTop (nhdsWithin (0:ℝ) (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcn_tendsto0, Eventually.of_forall (fun n => hcnpos n)⟩
  have hbn_nhds : Tendsto (fun n => bn n) atTop (nhdsWithin (0:ℝ) (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hbn_tendsto0, Eventually.of_forall (fun n => hbnpos n)⟩
  have havc : Tendsto (fun n => (cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => (cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s)) atTop (nhds η) :=
      havg.comp hcn_nhds
    simpa using h1.sub (tendsto_const_nhds (x := η))
  have havb : Tendsto (fun n => (bn n)⁻¹ * (∫ s in (0:ℝ)..bn n, φ s) - η) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => (bn n)⁻¹ * (∫ s in (0:ℝ)..bn n, φ s)) atTop (nhds η) :=
      havg.comp hbn_nhds
    simpa using h1.sub (tendsto_const_nhds (x := η))
  have hg : Tendsto (fun n => (cn n / bn n) * ((cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η)) atTop (nhds 0) := by
    have hbd : ∀ n, |(cn n / bn n) * ((cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η)|
        ≤ |(cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η| := fun n => by
      calc |(cn n / bn n) * ((cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η)|
          = (cn n / bn n) * |(cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η| := by
              rw [abs_mul, abs_of_nonneg (hcnbn_nonneg n)]
        _ ≤ (1/ρ) * |(cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η| :=
              mul_le_mul_of_nonneg_right (hcnbn_le n) (abs_nonneg _)
        _ ≤ |(cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η| := by
              apply mul_le_of_le_one_left (abs_nonneg _)
              rw [div_le_one hρpos]; exact le_of_lt hρgt1
    have habs : Tendsto (fun n => |(cn n / bn n) * ((cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η)|)
        atTop (nhds 0) :=
      squeeze_zero (fun n => abs_nonneg _) hbd (by simpa using havc.abs)
    exact (tendsto_zero_iff_abs_tendsto_zero
      (fun n => (cn n / bn n) * ((cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η))).mpr habs
  set Rv := (δ/2) * (1 - 1/ρ) with hRvdef
  have hRvpos : 0 < Rv := by
    rw [hRvdef]; refine mul_pos (by linarith) ?_
    rw [sub_pos, div_lt_one hρpos]; exact hρgt1
  have hev1 : ∀ᶠ n in atTop, -(Rv/2) < (cn n / bn n) * ((cn n)⁻¹ * (∫ s in (0:ℝ)..cn n, φ s) - η) :=
    (tendsto_order.1 hg).1 (-(Rv/2)) (by linarith)
  have hev2 : ∀ᶠ n in atTop, (bn n)⁻¹ * (∫ s in (0:ℝ)..bn n, φ s) - η < Rv/2 :=
    (tendsto_order.1 havb).2 (Rv/2) (by linarith)
  obtain ⟨n, hn1', hn2'⟩ := (hev1.and hev2).exists
  have hb := hbound n
  rw [hRvdef] at hb
  linarith [hb, hn1', hn2']

theorem tendsto_of_tendsto_average_of_deriv_bound {φ : ℝ → ℝ} {η ε : ℝ} (hε : 0 < ε)
    (hderiv : ∀ t ∈ Set.Ioo (0:ℝ) ε, HasDerivAt φ (deriv φ t) t)
    (hint : ∀ a b : ℝ, 0 < a → a ≤ b → b < ε → IntervalIntegrable (deriv φ) MeasureTheory.volume a b)
    (hint0 : ∀ t ∈ Set.Ioo (0:ℝ) ε, IntervalIntegrable φ MeasureTheory.volume 0 t)
    (havg : Filter.Tendsto (fun t : ℝ => t⁻¹ * ∫ s in (0:ℝ)..t, φ s)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds η))
    (hA : ∃ A : ℝ → ℝ, Continuous A ∧ ∀ t ∈ Set.Ioo (0:ℝ) ε, |deriv φ t| < A (φ t) / t) :
    Filter.Tendsto φ (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds η) := by
  obtain ⟨A, hAc, hAb⟩ := hA
  have hupper : ∀ δ > 0, ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), φ t < η + δ :=
    eventually_lt_nhdsGT_of_deriv_lt_of_tendsto_average hε hderiv hint hint0 havg hAc
      (fun t ht => lt_of_le_of_lt (le_abs_self (deriv φ t)) (hAb t ht))
  have hlower : ∀ δ > 0, ∀ᶠ t in nhdsWithin (0:ℝ) (Ioi 0), η - δ < φ t := by
    intro δ hδ
    have hderiv' : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (-φ) (deriv (-φ) t) t := by
      intro t ht
      rw [deriv.neg]
      exact (hderiv t ht).neg
    have hint' : ∀ a b : ℝ, 0 < a → a ≤ b → b < ε →
        IntervalIntegrable (deriv (-φ)) volume a b := by
      intro a b ha hab hb
      have h := (hint a b ha hab hb).neg
      convert h using 1
      funext x
      simp only [deriv.neg, Pi.neg_apply]
    have hint0' : ∀ t ∈ Ioo (0:ℝ) ε, IntervalIntegrable (-φ) volume 0 t := fun t ht =>
      (hint0 t ht).neg
    have havg' : Tendsto (fun t : ℝ => t⁻¹ * ∫ s in (0:ℝ)..t, (-φ) s)
        (nhdsWithin (0:ℝ) (Ioi 0)) (nhds (-η)) := by
      have h := havg.neg
      have heq : (fun t : ℝ => t⁻¹ * ∫ s in (0:ℝ)..t, (-φ) s)
          = fun t : ℝ => -(t⁻¹ * ∫ s in (0:ℝ)..t, φ s) := by
        ext t
        show t⁻¹ * ∫ s in (0:ℝ)..t, -φ s = -(t⁻¹ * ∫ s in (0:ℝ)..t, φ s)
        rw [intervalIntegral.integral_neg, mul_neg]
      rw [heq]; exact h
    have hAb' : ∀ t ∈ Ioo (0:ℝ) ε,
        deriv (-φ) t < (fun y => A (-y)) ((-φ) t) / t := by
      intro t ht
      have h2 : -deriv φ t < A (φ t) / t := lt_of_le_of_lt (neg_le_abs (deriv φ t)) (hAb t ht)
      rw [deriv.neg]
      simp only [Pi.neg_apply, neg_neg]
      exact h2
    have h := eventually_lt_nhdsGT_of_deriv_lt_of_tendsto_average (φ := -φ) (η := -η)
      hε hderiv' hint' hint0' havg' (hAc.comp continuous_neg) hAb'
    filter_upwards [h δ hδ] with t ht
    simp only [Pi.neg_apply] at ht
    linarith
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro b hb
    have h := hlower (η - b) (by linarith)
    filter_upwards [h] with t ht
    linarith
  · intro b hb
    have h := hupper (b - η) (by linarith)
    filter_upwards [h] with t ht
    linarith


end Commons.Analysis.Calculus