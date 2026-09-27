import Mathlib
import Submission.Work.EQ.H0_regular
import Submission.Work.EQ.exists_compact_regular_cycle
import Submission.Work.EQ.rational_of_compact_cycle
import Submission.Work.EQ.no_rational_germ
import Submission.Work.EQ.exists_H0_of_heteroclinic
import Submission.Work.EQ.exists_normEqCurve
import Submission.Work.EQ.normEqCurve_symmetric
import Submission.Work.EQ.exists_stableGerm
import Submission.Work.EQ.exists_heteroclinic_of_symmetric

open Filter Topology LeanEval.Geometry.Equichordal

namespace Work.EQ

/-- **No complex heteroclinic connection (Rychlik Cor 4 + Thm 12, assembled).** -/
theorem H0_eq_empty {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) : H0 a h = ∅ := by
  by_contra hne; obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨c, hc⟩ := H0_regular ha0 ha1 hh p hp
  obtain ⟨p', hp', c', hc', d, hd, hcyc, hcpt⟩ := exists_compact_regular_cycle ha0 ha1 hh ⟨p, hp, c, hc⟩
  exact no_rational_germ ha0 ha1 hh (rational_of_compact_cycle ha0 ha1 hh hp' hc' hd hcyc hcpt)

/-- **No real heteroclinic connection.** -/
theorem no_heteroclinic {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    {Γ : ℝ → ℂ} (hΓ : IsHeteroclinic a h r Γ) : False := by
  obtain ⟨p, hp⟩ := exists_H0_of_heteroclinic ha0 ha1 hΓ
  rw [H0_eq_empty ha0 ha1 hΓ.1] at hp; exact hp

theorem equichordal_main {K : Set Plane} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : (interior K).Nonempty) :
    ¬ ∃ P Q : Plane, P ≠ Q ∧ IsEquichordalPoint K P ∧ IsEquichordalPoint K Q := by
  rintro ⟨P, Q, hPQ, hP, hQ⟩
  obtain ⟨a, ha0, ha1, ρ₁, ρ₂, hC⟩ := exists_normEqCurve hK hconv hne hPQ hP hQ
  obtain ⟨hs₁, hs₂⟩ := normEqCurve_symmetric ha0 ha1 hC
  obtain ⟨h, r, hh⟩ := exists_stableGerm ha0 ha1
  obtain ⟨Γ, hΓ⟩ := exists_heteroclinic_of_symmetric ha0 ha1 hC hs₁ hs₂ hh
  exact no_heteroclinic ha0 ha1 hΓ

end Work.EQ

