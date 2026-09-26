import Mathlib
import Submission.Work.SphereJordan.SpanHyp
import Submission.Work.SphereJordan.SpanSetup
import Submission.Work.SphereJordan.tgtUpPC_isSimple
import Submission.Work.SphereJordan.prelim
import Submission.Work.SphereJordan.span_pairing_plan
import Submission.Work.SphereJordan.odd_windNumber_of_mem_V
import Submission.Work.Smooth.SphereJordan.windNumber_ne_zero_of_mem_V
import Submission.Work.Smooth.SphereJordan.thetaTwoHalvesSphereOfPlane
import Submission.Work.SphereJordan.windNumber_pairing_identities

/-!
# The pairing of the winding numbers of the four target curves

The main theorem `Work.SphereJordan.span_pairing` is proved from two inputs:

* `windNumber_pairing_identities` (an auxiliary lemma, proved in the sibling file
  `Submission/Work/SphereJordan/windNumber_pairing_identities.lean`), the three identities
  `a + d = 1`, `b + c = 1`, `a + b = 1 + e` for the winding numbers of the four target curves and
  of `γ` at a point `x ∈ S.V`;
* `Work.SphereJordan.odd_windNumber_of_mem_V` / `odd_windNumber_of_ne_zero` (the classical parity
  of the index on the bounded side) and the dictionary
  `Work.SphereJordan.mem_V_iff_windNumber_ne_zero`.

The reduction is carried out in `span_pairing_of_identities` below.
-/

open Set

namespace Work.SphereJordan

noncomputable section

/-- The three identities for the winding numbers of the four four-arc curves. -/
def PairingIdentities {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : SpanHyp h hs hball S) : Prop :=
  ∀ x : ℂ, x ∈ S.V →
    (Work.Smooth.SphereJordan.windNumber (H.upPC true).γ (H.upPC true).cont x
      + Work.Smooth.SphereJordan.windNumber (H.dnPC false).γ (H.dnPC false).cont x = 1) ∧
    (Work.Smooth.SphereJordan.windNumber (H.upPC false).γ (H.upPC false).cont x
      + Work.Smooth.SphereJordan.windNumber (H.dnPC true).γ (H.dnPC true).cont x = 1) ∧
    (Work.Smooth.SphereJordan.windNumber (H.upPC true).γ (H.upPC true).cont x
      + Work.Smooth.SphereJordan.windNumber (H.dnPC true).γ (H.dnPC true).cont x
      = 1 + Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x)

/-- **The reduction.**  The three identities for the winding numbers imply the pairing statement. -/
theorem span_pairing_of_identities {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : SpanHyp h hs hball S)
    (hid : PairingIdentities h hs hball S H)
    (STu : Work.Smooth.Jordan.PlaneSchoenflies (H.upPC true))
    (STf : Work.Smooth.Jordan.PlaneSchoenflies (H.upPC false))
    (SDu : Work.Smooth.Jordan.PlaneSchoenflies (H.dnPC true))
    (SDf : Work.Smooth.Jordan.PlaneSchoenflies (H.dnPC false)) :
    (S.V ⊆ STu.V ↔ S.V ⊆ SDu.V) ∧ (S.V ⊆ STu.V ↔ ¬ S.V ⊆ STf.V) ∧
      (S.V ⊆ SDu.V ↔ ¬ S.V ⊆ SDf.V) := by
  classical
  -- a point of the bounded side
  obtain ⟨x₀, hx₀⟩ := S.nonempty_V
  -- the winding number is constant on `S.V`
  have hconst : ∀ (C : Work.Smooth.Jordan.PlaneCurve) (hC : ∀ τ : ℝ, C.γ τ ∉ S.V),
      ∀ x ∈ S.V, Work.Smooth.SphereJordan.windNumber C.γ C.cont x =
        Work.Smooth.SphereJordan.windNumber C.γ C.cont x₀ := by
    intro C hC x hx
    refine Work.Smooth.SphereJordan.windNumber_eq_of_preconnected C S.preconn_V ?_ hx hx₀
    intro z hz
    simp only [Set.mem_compl_iff]
    intro hztr
    obtain ⟨τ, hτ⟩ := hztr
    exact hC τ (hτ ▸ hz)
  -- the four set-inclusions, via the winding-number dictionary
  have key : ∀ (C : Work.Smooth.Jordan.PlaneCurve)
      (SC : Work.Smooth.Jordan.PlaneSchoenflies C) (hC : ∀ τ : ℝ, C.γ τ ∉ S.V),
      (S.V ⊆ SC.V) ↔ Work.Smooth.SphereJordan.windNumber C.γ C.cont x₀ ≠ 0 := by
    intro C SC hC
    constructor
    · intro hsub
      have h1 := (mem_V_iff_windNumber_ne_zero SC).mp (hsub hx₀)
      rwa [hconst C hC x₀ hx₀] at h1
    · intro hne x hx
      rw [mem_V_iff_windNumber_ne_zero SC, hconst C hC x hx]
      exact hne
  -- the oddness of a non-zero winding number
  have hodd : ∀ (C : Work.Smooth.Jordan.PlaneCurve)
      (SC : Work.Smooth.Jordan.PlaneSchoenflies C) {n : ℤ}
      (hn : Work.Smooth.SphereJordan.windNumber C.γ C.cont x₀ = n), n ≠ 0 → Odd n := by
    intro C SC n hn hn0
    rw [← hn] at hn0 ⊢
    exact odd_windNumber_of_ne_zero SC hn0
  -- the three identities at `x₀`
  obtain ⟨hI1, hI2, hI3⟩ := hid x₀ hx₀
  set a := Work.Smooth.SphereJordan.windNumber (H.upPC true).γ (H.upPC true).cont x₀
  set b := Work.Smooth.SphereJordan.windNumber (H.dnPC true).γ (H.dnPC true).cont x₀
  set c := Work.Smooth.SphereJordan.windNumber (H.upPC false).γ (H.upPC false).cont x₀
  set d := Work.Smooth.SphereJordan.windNumber (H.dnPC false).γ (H.dnPC false).cont x₀
  set e := Work.Smooth.SphereJordan.windNumber γ.γ γ.cont x₀
  have he : e ≠ 0 := (mem_V_iff_windNumber_ne_zero S).mp hx₀
  have hb_d : b ≠ d := by
    intro hbd
    have h1 : b - d = e := by linarith
    rw [hbd, sub_self] at h1
    exact he h1.symm
  -- the two possible patterns
  have hpat : (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1) ∨ (a ≠ 0 ∧ b ≠ 0 ∧ c = 0 ∧ d = 0) := by
    by_cases ha : a = 0
    · left
      have hd : d = 1 := by linarith
      by_cases hb : b = 0
      · exact ⟨ha, hb, by linarith, hd⟩
      · exfalso
        have hbodd : Odd b := hodd _ SDu rfl hb
        have hc : c = 0 := by
          by_contra hc0
          have hcodd : Odd c := hodd _ STf rfl hc0
          obtain ⟨k, hk⟩ := hbodd
          obtain ⟨l, hl⟩ := hcodd
          omega
        have hb1 : b = 1 := by linarith
        exact hb_d (by rw [hb1, hd])
    · right
      have haodd : Odd a := hodd _ STu rfl ha
      have hd : d = 0 := by
        by_contra hd0
        have hdodd : Odd d := hodd _ SDf rfl hd0
        obtain ⟨k, hk⟩ := hdodd
        obtain ⟨l, hl⟩ := haodd
        omega
      have hbnz : b ≠ 0 := by
        intro hb0
        exact hb_d (by rw [hb0, hd])
      have hbodd : Odd b := hodd _ SDu rfl hbnz
      have hc : c = 0 := by
        by_contra hc0
        have hcodd : Odd c := hodd _ STf rfl hc0
        obtain ⟨k, hk⟩ := hbodd
        obtain ⟨l, hl⟩ := hcodd
        omega
      exact ⟨ha, hbnz, hc, hd⟩
  -- the traces avoid the bounded side
  have hav1 : ∀ τ : ℝ, (H.upPC true).γ τ ∉ S.V := fun τ => upPC_notMem_V h hs hball S H true τ
  have hav2 : ∀ τ : ℝ, (H.dnPC true).γ τ ∉ S.V := fun τ => dnPC_notMem_V h hs hball S H true τ
  have hav3 : ∀ τ : ℝ, (H.upPC false).γ τ ∉ S.V := fun τ => upPC_notMem_V h hs hball S H false τ
  have hav4 : ∀ τ : ℝ, (H.dnPC false).γ τ ∉ S.V := fun τ => dnPC_notMem_V h hs hball S H false τ
  have H1 : (S.V ⊆ STu.V) ↔ a ≠ 0 := key _ STu hav1
  have H2 : (S.V ⊆ SDu.V) ↔ b ≠ 0 := key _ SDu hav2
  have H3 : (S.V ⊆ STf.V) ↔ c ≠ 0 := key _ STf hav3
  have H4 : (S.V ⊆ SDf.V) ↔ d ≠ 0 := key _ SDf hav4
  rcases hpat with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [H1, H2]; simp [h1, h2]
    · rw [H1, H3]; simp [h1, h3]
    · rw [H2, H4]; simp [h2, h4]
  · refine ⟨?_, ?_, ?_⟩
    · rw [H1, H2]; simp [h1, h2]
    · rw [H1, H3]; simp [h1, h3]
    · rw [H2, H4]; simp [h2, h4]

/-- **The pairing of the four target curves.** -/
theorem span_pairing {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : Work.SphereJordan.SpanHyp h hs hball S)
    (STu : Work.Smooth.Jordan.PlaneSchoenflies (H.upPC true))
    (STf : Work.Smooth.Jordan.PlaneSchoenflies (H.upPC false))
    (SDu : Work.Smooth.Jordan.PlaneSchoenflies (H.dnPC true))
    (SDf : Work.Smooth.Jordan.PlaneSchoenflies (H.dnPC false)) :
    (S.V ⊆ STu.V ↔ S.V ⊆ SDu.V) ∧ (S.V ⊆ STu.V ↔ ¬ S.V ⊆ STf.V) ∧
      (S.V ⊆ SDu.V ↔ ¬ S.V ⊆ SDf.V) := by
  refine span_pairing_of_identities h hs hball S H (fun x hx => ?_) STu STf SDu SDf
  exact windNumber_pairing_identities h hs hball S H hx

end

end Work.SphereJordan
