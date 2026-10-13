import Mathlib
import Submission.Work.WilC4aRW.Defs
import Submission.Work.WilC4aRW.Real.eqOn_zero_ball_of_analyticOnNhd_of_eventually_ofReal

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilC4aRW.Real

open Work.WilC4aRW (cplxIncl ofRealAmbient snocCLM)

/-! ## A polydisc criterion for analytic functions vanishing on real points

The main mathematical input is the standard fact that a complex analytic function which
vanishes on an open subset of the "real points" `ℝ^N ⊆ ℂ^N` vanishes identically near `0`.
We prove it by induction on the number of variables, peeling off the last coordinate. -/

/-- The polydisc of radius `ρ` in `ℂ^N`. -/
def polydisc {N : ℕ} (ρ : ℝ) : Set (Fin N → ℂ) := {y | ∀ i, ‖y i‖ < ρ}

theorem mem_polydisc {N : ℕ} {ρ : ℝ} {y : Fin N → ℂ} :
    y ∈ polydisc ρ ↔ ∀ i, ‖y i‖ < ρ := Iff.rfl

/-- Membership in a ball of the normed space `E` around `0`, in terms of the norm. -/
theorem mem_ball_zero_norm {E : Type*} [SeminormedAddCommGroup E] {z : E} {ρ : ℝ} :
    z ∈ Metric.ball (0 : E) ρ ↔ ‖z‖ < ρ := by
  rw [Metric.mem_ball, dist_zero_right]

/-- A polydisc is a ball. -/
theorem polydisc_eq_ball {N : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    polydisc (N := N) ρ = Metric.ball 0 ρ := by
  ext y
  rw [mem_polydisc, mem_ball_zero_norm]
  exact (pi_norm_lt_iff hρ).symm

/-- `cplxIncl` commutes with `Fin.snoc`. -/
theorem cplxIncl_snoc {N : ℕ} (v : Fin N → ℝ) (s : ℝ) :
    cplxIncl (Fin.snoc v s) = Fin.snoc (cplxIncl v) (s : ℂ) := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [cplxIncl]
  | cast j => simp [cplxIncl]

/-- Membership in the polydisc unfolds along `Fin.snoc`. -/
theorem snoc_mem_polydisc {N : ℕ} {ρ : ℝ} {w : Fin N → ℂ} {z : ℂ} :
    Fin.snoc w z ∈ polydisc ρ ↔ (∀ i, ‖w i‖ < ρ) ∧ ‖z‖ < ρ := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h i.castSucc, by simpa using h (Fin.last N)⟩
  · rintro ⟨hw, hz⟩ i
    cases i using Fin.lastCases with
    | last => simpa using hz
    | cast j => simpa using hw j

/-- The `ℂ`-linear map `w ↦ Fin.snoc w 0`. -/
def snocL (N : ℕ) : (Fin N → ℂ) →L[ℂ] (Fin (N + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i : Fin (N + 1) =>
    Fin.lastCases (0 : (Fin N → ℂ) →L[ℂ] ℂ) (fun j => ContinuousLinearMap.proj (R := ℂ) j) i

theorem snocL_apply {N : ℕ} (w : Fin N → ℂ) :
    snocL N w = (Fin.snoc w 0 : Fin (N + 1) → ℂ) := by
  funext i
  cases i using Fin.lastCases with
  | last => simp [snocL]
  | cast j => simp [snocL]

theorem snoc_eq_snocL_add {N : ℕ} (w : Fin N → ℂ) (z : ℂ) :
    (Fin.snoc w z : Fin (N + 1) → ℂ) = snocL N w + Pi.single (Fin.last N) z := by
  rw [snocL_apply]
  funext i
  cases i using Fin.lastCases with
  | last => simp
  | cast j => simp

theorem snoc_eq_const_add_smul {N : ℕ} (w : Fin N → ℂ) (z : ℂ) :
    (Fin.snoc w z : Fin (N + 1) → ℂ) =
      (Fin.snoc w 0 : Fin (N + 1) → ℂ) + z • Pi.single (Fin.last N) (1 : ℂ) := by
  funext i
  cases i using Fin.lastCases with
  | last => simp
  | cast j => simp

/-- `s ↦ Fin.snoc w s` is analytic. -/
theorem analyticAt_snoc_last {N : ℕ} (w : Fin N → ℂ) (t : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (Fin.snoc w s : Fin (N + 1) → ℂ)) t := by
  have heq : (fun s : ℂ => (Fin.snoc w s : Fin (N + 1) → ℂ)) =
      fun s => (Fin.snoc w 0 : Fin (N + 1) → ℂ)
        + s • (Pi.single (Fin.last N) (1 : ℂ) : Fin (N + 1) → ℂ) := by
    funext s
    exact snoc_eq_const_add_smul w s
  rw [heq]
  exact (analyticAt_const (v := (Fin.snoc w 0 : Fin (N + 1) → ℂ)) (x := t)).add
    (((1 : ℂ →L[ℂ] ℂ).smulRight
      (Pi.single (Fin.last N) (1 : ℂ) : Fin (N + 1) → ℂ)).analyticAt t)

/-- `w ↦ Fin.snoc w z` is analytic. -/
theorem analyticAt_snoc_init {N : ℕ} (z : ℂ) (w₀ : Fin N → ℂ) :
    AnalyticAt ℂ (fun w : Fin N → ℂ => (Fin.snoc w z : Fin (N + 1) → ℂ)) w₀ := by
  have heq : (fun w : Fin N → ℂ => (Fin.snoc w z : Fin (N + 1) → ℂ)) =
      fun w => snocL N w + Pi.single (Fin.last N) z := by
    funext w
    exact snoc_eq_snocL_add w z
  rw [heq]
  exact (snocL N).analyticAt w₀ |>.add analyticAt_const

/-- **Key step.** A function on `ℂ^N`, analytic on a polydisc and vanishing on the real points
of that polydisc, vanishes on the whole polydisc. -/
theorem polydisc_eqOn_zero : ∀ (N : ℕ) {ρ : ℝ} (H : (Fin N → ℂ) → ℂ), 0 < ρ →
    AnalyticOnNhd ℂ H (polydisc ρ) →
    (∀ y ∈ polydisc ρ, y ∈ Set.range (fun v : Fin N → ℝ => cplxIncl v) → H y = 0) →
    ∀ y ∈ polydisc ρ, H y = 0 := by
  intro N
  induction N with
  | zero =>
    intro ρ H hρ hH hreal y hy
    exact hreal y hy ⟨fun i => Fin.elim0 i, by ext i; exact Fin.elim0 i⟩
  | succ N ih =>
    intro ρ H hρ hH hreal
    have step1 : ∀ (w : Fin N → ℂ) (z : ℂ), (∀ i, ‖w i‖ < ρ) →
        w ∈ Set.range (fun v : Fin N → ℝ => cplxIncl v) →
        z ∈ Metric.ball (0 : ℂ) ρ → H (Fin.snoc w z) = 0 := by
      intro w z hw hwreal hz
      have hg : AnalyticOnNhd ℂ (fun t : ℂ => H (Fin.snoc w t)) (Metric.ball (0 : ℂ) ρ) := by
        intro t ht
        refine (hH (Fin.snoc w t) ?_).comp (analyticAt_snoc_last w t)
        exact snoc_mem_polydisc.mpr ⟨hw, mem_ball_zero_norm.mp ht⟩
      have hrealg : ∀ᶠ s : ℝ in nhds 0, (fun t : ℂ => H (Fin.snoc w t)) (s : ℂ) = 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with s hs
        obtain ⟨v, rfl⟩ := hwreal
        have hsz : ‖(s : ℂ)‖ < ρ := by simpa using hs
        refine hreal _ (snoc_mem_polydisc.mpr ⟨hw, hsz⟩) ?_
        exact ⟨Fin.snoc v s, cplxIncl_snoc v s⟩
      exact eqOn_zero_ball_of_analyticOnNhd_of_eventually_ofReal hρ hg hrealg hz
    intro y hy
    rw [← Fin.snoc_init_self (n := N) y]
    refine ih (fun w => H (Fin.snoc w (y (Fin.last N)))) hρ ?_ ?_ (Fin.init y) ?_
    · intro w hw
      refine AnalyticAt.comp
        (f := fun w' : Fin N → ℂ => (Fin.snoc w' (y (Fin.last N)) : Fin (N + 1) → ℂ))
        (x := w) (hH (Fin.snoc w (y (Fin.last N))) ?_)
        (analyticAt_snoc_init (y (Fin.last N)) w)
      exact snoc_mem_polydisc.mpr ⟨hw, hy (Fin.last N)⟩
    · intro w hw hwr
      exact step1 w (y (Fin.last N)) hw hwr (mem_ball_zero_norm.mpr (hy (Fin.last N)))
    · intro i
      change ‖y i.castSucc‖ < ρ
      exact hy i.castSucc

/-- **Main auxiliary statement.** An analytic function on `ℂ^N` vanishing on the real points
near `0` vanishes in a neighbourhood of `0`. -/
theorem eventuallyEq_zero_of_analyticAt_of_forall_ofReal {N : ℕ} {H : (Fin N → ℂ) → ℂ}
    (hH : AnalyticAt ℂ H 0)
    (hreal : ∀ᶠ v : Fin N → ℝ in nhds 0, H (cplxIncl v) = 0) :
    H =ᶠ[nhds 0] 0 := by
  obtain ⟨r, hr, hHr⟩ : ∃ r : ℝ, 0 < r ∧ AnalyticOnNhd ℂ H (Metric.ball 0 r) := by
    obtain ⟨r, hr, hmem⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_analyticAt ℂ H).mem_nhds (show (0 : Fin N → ℂ) ∈ {x | AnalyticAt ℂ H x} from hH))
    exact ⟨r, hr, fun x hx => hmem hx⟩
  obtain ⟨δ, hδ, hδ'⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ v : Fin N → ℝ, ‖v‖ < δ → H (cplxIncl v) = 0 := by
    obtain ⟨δ, hδ, hmem⟩ := Metric.mem_nhds_iff.mp hreal
    exact ⟨δ, hδ, fun v hv => hmem (mem_ball_zero_norm.mpr hv)⟩
  set ρ : ℝ := min r δ / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  have hρr : ρ < r := by rw [hρdef]; have := min_le_left r δ; linarith
  have hρδ : ρ < δ := by rw [hρdef]; have := min_le_right r δ; linarith
  have hHpol : AnalyticOnNhd ℂ H (polydisc ρ) :=
    hHr.mono (by rw [polydisc_eq_ball hρ]; exact Metric.ball_subset_ball (le_of_lt hρr))
  have hrealpol :
      ∀ y ∈ polydisc ρ, y ∈ Set.range (fun v : Fin N → ℝ => cplxIncl v) → H y = 0 := by
    intro y hy hrange
    obtain ⟨v, rfl⟩ := hrange
    refine hδ' v ?_
    rw [pi_norm_lt_iff hδ]
    intro i
    have h1 : ‖((v i : ℝ) : ℂ)‖ < ρ := by simpa [cplxIncl] using hy i
    calc ‖v i‖ = ‖((v i : ℝ) : ℂ)‖ := by simp
      _ < ρ := h1
      _ < δ := hρδ
  have hzero : ∀ y ∈ polydisc ρ, H y = 0 := polydisc_eqOn_zero N H hρ hHpol hrealpol
  have hmem : polydisc ρ ∈ nhds (0 : Fin N → ℂ) := by
    rw [polydisc_eq_ball hρ]
    exact Metric.ball_mem_nhds 0 hρ
  filter_upwards [hmem] with y hy
  simpa using hzero y hy

/-! ## Reindexing the ambient space along `Fin.snoc` -/

/-- Real points of `ℂ^{N+1}`, followed by `Fin.init`/`Fin.last`, are given by `Fin.init`. -/
theorem fin_init_apply {N : ℕ} {α : Type*} (v : Fin (N + 1) → α) (i : Fin N) :
    Fin.init v i = v i.castSucc := rfl

/-- The `ℂ`-linear reindexing `(Fin (n+1) → ℂ) → Ambient n`, `y ↦ (Fin.init y, y (Fin.last n))`. -/
def toAmbient (n : ℕ) : (Fin (n + 1) → ℂ) →L[ℂ] ClassicalComplexWPT.Ambient n :=
  (ContinuousLinearMap.pi fun i : Fin n => ContinuousLinearMap.proj (R := ℂ) i.castSucc).prod
    (ContinuousLinearMap.proj (R := ℂ) (Fin.last n))

theorem toAmbient_fst {n : ℕ} (y : Fin (n + 1) → ℂ) :
    (toAmbient n y).1 = fun i => y i.castSucc := rfl

theorem toAmbient_snd {n : ℕ} (y : Fin (n + 1) → ℂ) :
    (toAmbient n y).2 = y (Fin.last n) := rfl

theorem toAmbient_cplxIncl {n : ℕ} (v : Fin (n + 1) → ℝ) :
    toAmbient n (cplxIncl v) = ofRealAmbient v := by
  refine Prod.ext ?_ ?_
  · funext i
    show cplxIncl v i.castSucc = cplxIncl (Fin.init v) i
    simp only [cplxIncl_apply, fin_init_apply]
  · rw [toAmbient_snd, ofRealAmbient_snd, cplxIncl_apply]

theorem toAmbient_snocCLM {n : ℕ} (z : ClassicalComplexWPT.Ambient n) :
    toAmbient n (snocCLM n z) = z := by
  refine Prod.ext ?_ ?_
  · funext i
    show snocCLM n z i.castSucc = z.1 i
    rw [snocCLM_apply_castSucc]
  · show snocCLM n z (Fin.last n) = z.2
    rw [snocCLM_apply_last]

/-! ## The requested lemma -/

theorem eventuallyEq_of_eventuallyEq_ofRealAmbient {n : ℕ}
    {F G : ClassicalComplexWPT.Ambient n → ℂ}
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (hreal : ∀ᶠ x : Fin (n + 1) → ℝ in nhds 0,
      F (Work.WilC4aRW.ofRealAmbient x) = G (Work.WilC4aRW.ofRealAmbient x)) :
    F =ᶠ[nhds (0 : ClassicalComplexWPT.Ambient n)] G := by
  have hHan : AnalyticAt ℂ (F - G) 0 := hF.sub hG
  have hrealH : ∀ᶠ x : Fin (n + 1) → ℝ in nhds 0, (F - G) (ofRealAmbient x) = 0 := by
    filter_upwards [hreal] with x hx
    show F (ofRealAmbient x) - G (ofRealAmbient x) = 0
    rw [hx, sub_self]
  have hH' : AnalyticAt ℂ ((F - G) ∘ toAmbient n) 0 := hHan.compContinuousLinearMap
  have hrealH' :
      ∀ᶠ v : Fin (n + 1) → ℝ in nhds 0, ((F - G) ∘ toAmbient n) (cplxIncl v) = 0 := by
    filter_upwards [hrealH] with v hv
    simpa only [Function.comp_apply, toAmbient_cplxIncl] using hv
  have key : ((F - G) ∘ toAmbient n) =ᶠ[nhds (0 : Fin (n + 1) → ℂ)] 0 :=
    eventuallyEq_zero_of_analyticAt_of_forall_ofReal hH' hrealH'
  have hsnoc : Tendsto (snocCLM n) (nhds (0 : ClassicalComplexWPT.Ambient n))
      (nhds (0 : Fin (n + 1) → ℂ)) := by
    simpa using (snocCLM n).continuous.tendsto (0 : ClassicalComplexWPT.Ambient n)
  have key2 : ∀ᶠ z : ClassicalComplexWPT.Ambient n in nhds 0, (F - G) z = 0 := by
    filter_upwards [hsnoc.eventually key] with z hz
    simpa [Function.comp_apply, toAmbient_snocCLM] using hz
  filter_upwards [key2] with y hy
  exact sub_eq_zero.mp hy

end Work.WilC4aRW.Real
