import Mathlib
import Submission.Diff.ODE
import Submission.Work.Diff.ODE.Basic
import Submission.Work.Diff.ODE.exists_localBox
import Submission.Work.Diff.ODE.eqOn_Ioo_of_isXCurveOn
import Submission.Work.Diff.ODE.exists_isXCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead. Read HANDOFF.md.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen. Your statement's hypotheses are other
areas' contracts: USE them, do not re-prove them. Go wide: file all the independent sub-lemmas at once,
each with an exact statement, and write your assembly against their statements. If your statement looks
false or unprovable as stated, say so at once in `declare_false` with a precise reason. The lead will fix it.
SHARED piece: the STE area (DeTurck pull-back) and the d = 2 area (gradient-like flow) both use it. Keep the statement general.
-/

namespace Work.Diff.ODE

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ## Shifting the starting time of a solution -/

section Curve

variable {X : ℝ → Π x : M, TangentSpace I x}

/-- **Shifting the starting time of a solution**: if `γ` solves the ODE from `(a, y)`, then
`τ ↦ γ (τ + c)` solves the ODE from `(a + c, γ c)`. -/
theorem IsXCurve.comp_add {a : ℝ} {y : M} {γ : ℝ → M} (c : ℝ) (h : IsXCurve X a y γ) :
    IsXCurve X (a + c) (γ c) (fun τ => γ (τ + c)) := by
  refine ⟨by simp, fun τ => ?_⟩
  have hae : a + c + τ = a + (τ + c) := by ring
  rw [hae]
  show HasMFDerivAt 𝓘(ℝ, ℝ) I (fun τ : ℝ => γ (τ + c)) τ
    ((1 : ℝ →L[ℝ] ℝ).smulRight (X (a + (τ + c)) (γ (τ + c))))
  rw [← ContinuousLinearMap.comp_id
    ((1 : ℝ →L[ℝ] ℝ).smulRight (X (a + (τ + c)) (γ (τ + c))))]
  exact (h.2 (τ + c)).comp τ (((hasFDerivAt_id τ).add_const c).hasMFDerivAt)

end Curve

/-! ## Composing a local flow box with smooth maps -/

/-- A smooth map composed with a local flow box is smooth. -/
theorem localBox_contMDiffAt_comp
    {X : ℝ → Π x : M, TangentSpace I x}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    (B : LocalBox X) {α β : N → ℝ} {Ψ : N → M} {q₀ : N}
    (hα : ContMDiffAt J 𝓘(ℝ, ℝ) ∞ α q₀) (hβ : ContMDiffAt J 𝓘(ℝ, ℝ) ∞ β q₀)
    (hΨ : ContMDiffAt J I ∞ Ψ q₀)
    (hmem : (α q₀, Ψ q₀) ∈ B.U) (hτ : |β q₀| < 2 * B.δ) :
    ContMDiffAt J I ∞ (fun q => B.FL (β q) (α q) (Ψ q)) q₀ := by
  have hg := B.hsmooth (α q₀) (Ψ q₀) hmem (β q₀) hτ
  have hf : ContMDiffAt J ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) ∞
      (fun q => ((β q, α q), Ψ q)) q₀ :=
    ContMDiffAt.prodMk (ContMDiffAt.prodMk hβ hα) hΨ
  simpa [Function.comp_def] using hg.comp q₀ hf

/-! ## The flow associated with a global existence hypothesis -/

section Flow

variable {X : ℝ → Π x : M, TangentSpace I x}

/-- A chosen global solution of the ODE of `X` starting at `(a, y)`. -/
noncomputable def flowCurve (hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ)
    (a : ℝ) (y : M) : ℝ → M :=
  Classical.choose (hEx a y)

lemma flowCurve_isXCurve (hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ)
    (a : ℝ) (y : M) : IsXCurve X a y (flowCurve hEx a y) :=
  Classical.choose_spec (hEx a y)

/-- The flow map: the position at time `t` of the trajectory started at time `s` at `x`. -/
noncomputable def flowMap (hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ)
    (s t : ℝ) (x : M) : M :=
  flowCurve hEx s x (t - s)

lemma flowMap_def (hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ)
    (s t : ℝ) (x : M) : flowMap hEx s t x = flowCurve hEx s x (t - s) := rfl

lemma flowMap_self (hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ)
    (s : ℝ) (x : M) : flowMap hEx s s x = x := by
  rw [flowMap_def, sub_self]
  exact (flowCurve_isXCurve hEx s x).1

/-- Any solution from `(a,y)` is the chosen one. -/
lemma eq_flowCurve_of_isXCurve
    (hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ)
    (hUniq : ∀ {a : ℝ} {y : M} {T : ℝ}, 0 < T → ∀ {γ γ' : ℝ → M},
      IsXCurveOn X a y T γ → IsXCurveOn X a y T γ' → EqOn γ γ' (Ioo (-T) T))
    {a : ℝ} {y : M} {γ : ℝ → M} (hγ : IsXCurve X a y γ) (τ : ℝ) :
    γ τ = flowCurve hEx a y τ := by
  have hT : (0 : ℝ) < |τ| + 1 := by positivity
  have hmem : τ ∈ Ioo (-(|τ| + 1)) (|τ| + 1) := by
    rw [mem_Ioo, ← abs_lt]
    linarith
  exact hUniq hT (hγ.isXCurveOn _) ((flowCurve_isXCurve hEx a y).isXCurveOn _) hmem

/-- The flow identity `Φ t u (Φ s t x) = Φ s u x`. -/
lemma flowMap_comp
    (hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ)
    (hUniq : ∀ {a : ℝ} {y : M} {T : ℝ}, 0 < T → ∀ {γ γ' : ℝ → M},
      IsXCurveOn X a y T γ → IsXCurveOn X a y T γ' → EqOn γ γ' (Ioo (-T) T))
    (s t u : ℝ) (x : M) : flowMap hEx t u (flowMap hEx s t x) = flowMap hEx s u x := by
  have hshift : IsXCurve X t (flowMap hEx s t x)
      (fun τ => flowCurve hEx s x (τ + (t - s))) := by
    have h := (flowCurve_isXCurve hEx s x).comp_add (t - s)
    simpa [flowMap_def] using h
  have h1 := eq_flowCurve_of_isXCurve hEx hUniq hshift (u - t)
  simp only [flowMap_def] at h1 ⊢
  rw [← h1]
  congr 1
  ring

/-- The derivative of the flow in the time variable. -/
lemma flowMap_hasMFDerivAt (hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ)
    (s t : ℝ) (x : M) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun τ => flowMap hEx s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (flowMap hEx s t x))) := by
  have hsub : s + (t - s) = t := by ring
  have hcurve := (flowCurve_isXCurve hEx s x).2 (t - s)
  rw [hsub] at hcurve
  show HasMFDerivAt 𝓘(ℝ, ℝ) I (fun τ : ℝ => flowCurve hEx s x (τ - s)) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (flowCurve hEx s x (t - s))))
  rw [← ContinuousLinearMap.comp_id
    ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (flowCurve hEx s x (t - s))))]
  exact hcurve.comp t (((hasFDerivAt_id t).sub_const s).hasMFDerivAt)

/-- **The box identity**: the flow from `(s,x)` over elapsed time `t + τ` is obtained by stepping
`τ` from the intermediate point `Φ s t x` using the box at `(t, Φ s t x)`. -/
lemma flowMap_eq_localBox
    (hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ)
    (hUniq : ∀ {a : ℝ} {y : M} {T : ℝ}, 0 < T → ∀ {γ γ' : ℝ → M},
      IsXCurveOn X a y T γ → IsXCurveOn X a y T γ' → EqOn γ γ' (Ioo (-T) T))
    (B : LocalBox X) {s t : ℝ} {x : M}
    (hmem : (t, flowMap hEx s t x) ∈ B.U) {τ : ℝ} (hτ : |τ| < 2 * B.δ) :
    flowMap hEx s (t + τ) x = B.FL τ t (flowMap hEx s t x) := by
  have hpos : (0 : ℝ) < 2 * B.δ := by linarith [B.hδ]
  have hshift : IsXCurveOn X t (flowMap hEx s t x) (2 * B.δ)
      (fun σ => flowCurve hEx s x (σ + (t - s))) := by
    have h := ((flowCurve_isXCurve hEx s x).comp_add (t - s)).isXCurveOn (2 * B.δ)
    simpa [flowMap_def] using h
  have hbox : IsXCurveOn X t (flowMap hEx s t x) (2 * B.δ)
      (fun σ => B.FL σ t (flowMap hEx s t x)) :=
    ⟨B.hzero t _ hmem, fun σ hσ => B.hode t _ hmem σ (le_of_lt hσ)⟩
  have hτ' : τ ∈ Ioo (-(2 * B.δ)) (2 * B.δ) := by
    rw [mem_Ioo, ← abs_lt]
    exact hτ
  have heq : B.FL τ t (flowMap hEx s t x) = flowCurve hEx s x (τ + (t - s)) := by
    simpa using hUniq hpos hbox hshift hτ'
  have heq' : B.FL τ t (flowMap hEx s t x) = flowCurve hEx s x (t + τ - s) := by
    rw [heq]
    congr 1
    ring
  rw [flowMap_def, ← heq']

end Flow

/-! ## The interpolated flow used for the long-time smoothness argument -/

section Interp

/-- The interpolation of a pair of times at parameter `k/K`. -/
noncomputable def interpTime (K k : ℕ) (st : ℝ × ℝ) : ℝ := st.1 + ((k : ℝ) / K) * (st.2 - st.1)

lemma interpTime_zero (K : ℕ) (st : ℝ × ℝ) : interpTime K 0 st = st.1 := by
  simp [interpTime]

lemma interpTime_self {K : ℕ} (hK : (K : ℝ) ≠ 0) (st : ℝ × ℝ) : interpTime K K st = st.2 := by
  simp only [interpTime]
  rw [div_self hK, one_mul]
  ring

lemma interpTime_succ (K k : ℕ) (st : ℝ × ℝ) :
    interpTime K (k + 1) st - interpTime K k st = (st.2 - st.1) / K := by
  simp only [interpTime]
  push_cast
  ring

lemma contMDiffAt_interpTime (K k : ℕ) (st₀ : ℝ × ℝ) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun st : ℝ × ℝ => interpTime K k st) st₀ := by
  have h1 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun st : ℝ × ℝ => st.1) st₀ := contMDiffAt_fst
  have h2 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun st : ℝ × ℝ => st.2) st₀ := contMDiffAt_snd
  have h3 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun _ : ℝ × ℝ => ((k : ℝ) / K)) st₀ := contMDiffAt_const
  have h4 : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun st : ℝ × ℝ => ((k : ℝ) / K) * (st.2 - st.1)) st₀ := h3.mul (h2.sub h1)
  have h5 := h1.add h4
  convert h5 using 1
  ext st
  simp only [Pi.add_apply]
  rfl

variable {X : ℝ → Π x : M, TangentSpace I x}

/-- The flow along the interpolated trajectory. -/
noncomputable def interpFlow (hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ)
    (K k : ℕ) (q : (ℝ × ℝ) × M) : M :=
  flowMap hEx q.1.1 (interpTime K k q.1) q.2

lemma interpFlow_apply (hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ)
    (K k : ℕ) (q : (ℝ × ℝ) × M) :
    interpFlow hEx K k q = flowMap hEx q.1.1 (interpTime K k q.1) q.2 := rfl

/-- **Joint smoothness of the flow map.**  This is the heart of the proof: along the trajectory the
flow is a finite composition of local flow boxes, and each step is smooth by
`localBox_contMDiffAt_comp`. -/
theorem contMDiffAt_flowMap
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {X : ℝ → Π x : M, TangentSpace I x}
    (hBox : ∀ a : ℝ, ∀ y : M, ∃ B : LocalBox X, (a, y) ∈ B.U)
    (hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ)
    (hUniq : ∀ {a : ℝ} {y : M} {T : ℝ}, 0 < T → ∀ {γ γ' : ℝ → M},
      IsXCurveOn X a y T γ → IsXCurveOn X a y T γ' → EqOn γ γ' (Ioo (-T) T))
    (q₀ : (ℝ × ℝ) × M) :
    ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => flowMap hEx q.1.1 q.1.2 q.2) q₀ := by
  classical
  -- ## A compact window of times
  let W : Set (ℝ × M) := Icc (min q₀.1.1 q₀.1.2 - 1) (max q₀.1.1 q₀.1.2 + 1) ×ˢ (univ : Set M)
  have hWc : IsCompact W := isCompact_Icc.prod isCompact_univ
  have hWbox : ∀ p : ↥W, ∃ B : LocalBox X, (p : ℝ × M) ∈ B.U :=
    fun p => hBox p.1.1 p.1.2
  choose cB hcB using hWbox
  obtain ⟨t, ht⟩ := hWc.elim_finite_subcover (fun p : ↥W => (cB p).U)
    (fun p => (cB p).hU)
    (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, hcB ⟨p, hp⟩⟩)
  have ht' : ∀ p ∈ W, ∃ i, i ∈ t ∧ p ∈ (cB i).U := fun p hp => by
    obtain ⟨i, hi, hiU⟩ := mem_iUnion₂.mp (ht hp)
    exact ⟨i, hi, hiU⟩
  have hWne : W.Nonempty := by
    refine ⟨(q₀.1.1, q₀.2), ⟨?_, mem_univ _⟩⟩
    exact ⟨by linarith [min_le_left q₀.1.1 q₀.1.2],
      by linarith [le_max_left q₀.1.1 q₀.1.2]⟩
  have htne : t.Nonempty := by
    obtain ⟨p, hp⟩ := hWne
    obtain ⟨i, hi, _⟩ := ht' p hp
    exact ⟨i, hi⟩
  let δmin : ℝ := t.inf' htne (fun i => (cB i).δ)
  have hδmin_pos : 0 < δmin := by
    have h : δmin = t.inf' htne (fun i => (cB i).δ) := rfl
    rw [h, Finset.lt_inf'_iff]
    intro i _
    exact (cB i).hδ
  have hδmin_le : ∀ i ∈ t, δmin ≤ (cB i).δ := fun i hi => by
    have h : δmin = t.inf' htne (fun i => (cB i).δ) := rfl
    rw [h]
    exact Finset.inf'_le _ hi
  -- ## The number of steps
  obtain ⟨K, hKbig⟩ : ∃ K : ℕ, |q₀.1.2 - q₀.1.1| / δmin < (K : ℝ) := exists_nat_gt _
  have hKne : K ≠ 0 := by
    intro h0
    rw [h0] at hKbig
    have hnn : 0 ≤ |q₀.1.2 - q₀.1.1| / δmin := div_nonneg (abs_nonneg _) hδmin_pos.le
    simp only [Nat.cast_zero] at hKbig
    linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hKne
  have hKc : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have hΔlt : |q₀.1.2 - q₀.1.1| / K < δmin := by
    rw [div_lt_iff₀ hKpos, mul_comm]
    rwa [div_lt_iff₀ hδmin_pos] at hKbig
  -- ## The interpolation along the trajectory
  have hσ_mem : ∀ k ≤ K,
      (interpTime K k q₀.1, flowMap hEx q₀.1.1 (interpTime K k q₀.1) q₀.2) ∈ W := by
    intro k hk
    have hc0 : 0 ≤ (k : ℝ) / K := div_nonneg (Nat.cast_nonneg k) hKpos.le
    have hc1 : (k : ℝ) / K ≤ 1 := by
      rw [div_le_one hKpos]
      exact_mod_cast hk
    have hσk : interpTime K k q₀.1
        = (1 - (k : ℝ) / K) * q₀.1.1 + ((k : ℝ) / K) * q₀.1.2 := by
      simp only [interpTime]
      ring
    refine ⟨?_, mem_univ _⟩
    rw [hσk]
    constructor
    · nlinarith [min_le_left q₀.1.1 q₀.1.2, min_le_right q₀.1.1 q₀.1.2, sub_nonneg.mpr hc1]
    · nlinarith [le_max_left q₀.1.1 q₀.1.2, le_max_right q₀.1.1 q₀.1.2, sub_nonneg.mpr hc1]
  have hbox_k : ∀ k < K, ∃ i, i ∈ t ∧
      (interpTime K k q₀.1, flowMap hEx q₀.1.1 (interpTime K k q₀.1) q₀.2) ∈ (cB i).U :=
    fun k hk => ht' _ (hσ_mem k (le_of_lt hk))
  choose cc hcc_t hcc_U using hbox_k
  -- ## Smoothness of the interpolated time
  have hsig : ∀ k : ℕ, ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : (ℝ × ℝ) × M => interpTime K k q.1) q₀ := by
    intro k
    have h2 : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ (fun q : (ℝ × ℝ) × M => q.1) q₀ :=
      contMDiffAt_fst
    exact (contMDiffAt_interpTime K k q₀.1).comp q₀ h2
  -- ## The induction
  have hstep : ∀ k, k ≤ K → ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => interpFlow hEx K k q) q₀ := by
    intro k
    induction k with
    | zero =>
      intro _
      have hfun : (fun q : (ℝ × ℝ) × M => interpFlow hEx K 0 q) = fun q => q.2 := by
        funext q
        rw [interpFlow_apply, interpTime_zero]
        exact flowMap_self hEx q.1.1 q.2
      rw [hfun]
      exact contMDiffAt_snd
    | succ k ih =>
      intro hk
      have hkK : k ≤ K := Nat.le_of_succ_le hk
      have hklt : k < K := Nat.lt_of_succ_le hk
      have ih' := ih hkK
      let B : LocalBox X := cB (cc k hklt)
      have hmem : (interpTime K k q₀.1, interpFlow hEx K k q₀) ∈ B.U := hcc_U k hklt
      have hα : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : (ℝ × ℝ) × M => interpTime K k q.1) q₀ := hsig k
      have hβ : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
          (fun q : (ℝ × ℝ) × M => interpTime K (k + 1) q.1 - interpTime K k q.1) q₀ :=
        (hsig (k + 1)).sub (hsig k)
      have hτ₀ : |interpTime K (k + 1) q₀.1 - interpTime K k q₀.1| < 2 * B.δ := by
        have hBδ : 0 < B.δ := B.hδ
        have hle : δmin ≤ B.δ := hδmin_le (cc k hklt) (hcc_t k hklt)
        rw [interpTime_succ K k q₀.1]
        calc |(q₀.1.2 - q₀.1.1) / K| = |q₀.1.2 - q₀.1.1| / K := by
              rw [abs_div, abs_of_pos hKpos]
          _ < δmin := hΔlt
          _ ≤ B.δ := hle
          _ < 2 * B.δ := by linarith
      have hcomp := localBox_contMDiffAt_comp B hα hβ ih' hmem hτ₀
      refine hcomp.congr_of_eventuallyEq ?_
      have hcontpair : ContinuousAt (fun q : (ℝ × ℝ) × M
          => (interpTime K k q.1, interpFlow hEx K k q)) q₀ := by
        have h1 : ContinuousAt (fun q : (ℝ × ℝ) × M => interpTime K k q.1) q₀ :=
          (hsig k).continuousAt
        have h2 : ContinuousAt (fun q : (ℝ × ℝ) × M => interpFlow hEx K k q) q₀ :=
          ih'.continuousAt
        exact h1.prodMk h2
      have hev1 : ∀ᶠ q in 𝓝 q₀, (interpTime K k q.1, interpFlow hEx K k q) ∈ B.U :=
        hcontpair.eventually (B.hU.mem_nhds hmem)
      have hev2 : ∀ᶠ q in 𝓝 q₀,
          |interpTime K (k + 1) q.1 - interpTime K k q.1| < 2 * B.δ := by
        have h2 : ∀ᶠ q in 𝓝 q₀,
            (interpTime K (k + 1) q.1 - interpTime K k q.1) ∈ Ioo (-(2 * B.δ)) (2 * B.δ) :=
          hβ.continuousAt.eventually (isOpen_Ioo.mem_nhds (by
            rw [mem_Ioo, ← abs_lt]
            exact hτ₀))
        filter_upwards [h2] with q hq
        rw [mem_Ioo, ← abs_lt] at hq
        exact hq
      filter_upwards [hev1, hev2] with q hq1 hq2
      show flowMap hEx q.1.1 (interpTime K (k + 1) q.1) q.2
        = B.FL (interpTime K (k + 1) q.1 - interpTime K k q.1) (interpTime K k q.1)
            (flowMap hEx q.1.1 (interpTime K k q.1) q.2)
      rw [← flowMap_eq_localBox hEx hUniq B hq1 hq2]
      rw [show interpTime K k q.1 + (interpTime K (k + 1) q.1 - interpTime K k q.1)
          = interpTime K (k + 1) q.1 from by ring]
  have hfin := hstep K le_rfl
  have hfun : (fun q : (ℝ × ℝ) × M => interpFlow hEx K K q)
      = (fun q : (ℝ × ℝ) × M => flowMap hEx q.1.1 q.1.2 q.2) := by
    funext q
    rw [interpFlow_apply, interpTime_self hKc]
  rwa [hfun] at hfin

end Interp

/-! ## The contract -/

open Submission.Diff in
/-- **CONTRACT ODE** (`Submission.Diff.SmoothFlow`): every jointly smooth time-dependent vector
field on a compact boundaryless manifold has a global jointly smooth flow `(s,t,x) ↦ Φ s t x`. -/
theorem flow_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] :
    SmoothFlow I M := by
  intro X hX
  have hBox : ∀ a : ℝ, ∀ y : M, ∃ B : LocalBox X, (a, y) ∈ B.U :=
    fun a y => exists_localBox (X := X) hX a y
  have hUniq : ∀ {a : ℝ} {y : M} {T : ℝ}, 0 < T → ∀ {γ γ' : ℝ → M},
      IsXCurveOn X a y T γ → IsXCurveOn X a y T γ' → EqOn γ γ' (Ioo (-T) T) :=
    fun hT _ _ h1 h2 => eqOn_Ioo_of_isXCurveOn (X := X) hX hT h1 h2
  have hEx : ∀ a : ℝ, ∀ y : M, ∃ γ : ℝ → M, IsXCurve X a y γ :=
    fun a y => exists_isXCurve (X := X) hX hBox hUniq a y
  refine ⟨fun s t x => flowMap hEx s t x, ?_, ?_, ?_, ?_⟩
  · exact fun q => contMDiffAt_flowMap hBox hEx hUniq q
  · intro s x
    exact flowMap_self hEx s x
  · intro s t u x
    exact flowMap_comp hEx hUniq s t u x
  · intro s t x
    exact flowMap_hasMFDerivAt hEx s t x

end Work.Diff.ODE
