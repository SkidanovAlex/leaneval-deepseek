import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.FMap
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.canon_exists
import Submission.Work.RankOneUniqueness.canon_unique
import Submission.Work.PSU3.RankOne.H16
import Submission.Work.PSU3.RankOne.canon_conj
import Submission.Work.PSU3.RankOne.canon_mul
import Submission.Work.PSU3.RankOne.canon_mul_ne_one
import Submission.Work.PSU3.StageC.e_zc_eq
import Submission.Work.PSU3.StageC.FSuz
import Submission.Work.PSU3.StageC.FAsm
import Submission.Work.PSU3.StageC.f_formula_on_omega_coset
import Submission.Work.PSU3.StageC.f_formula_extension

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageC

theorem f_formula_of_omega {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) {ω : G}
    (hω : Work.PSU3.OmegaHyp fr ω)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (hω2 : ω ^ 2 = fr.zc ((fr.κ fr.ζ : Work.PSU3.E n) + (fr.κ fr.ζ : Work.PSU3.E n)⁻¹))
    (e : Q ≃* SZ (Work.PSU3.E n)) (μ : (Work.PSU3.E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    (hωcoord : (e ⟨ω, hω.1⟩).y = (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n))⁻¹) :
    ∀ x y : Q, (x : G) ≠ 1 → Work.RankOneUniqueness.FRel H t (x : G) (y : G) →
      e y = Work.PSU3.fMapTot (e x) := by
  intro x y hx hrel
  have hy : (y : G) = (Work.PSU3.StageB.fcan hS.split x : G) :=
    eq_fcan_of_FRel hS hx hrel
  have hpq : ((⟨ω, hω.1⟩ : Q) : G) ∉ fr.Q0 := by
    intro h
    exact hω.2.1 (by simpa using h)
  have hbase := f_formula_on_omega_coset hS fr hω hsq hω2 e μ hex hes heq hωcoord
  have hQ0 := agree_Q0 hS fr hsq e μ hex hes heq
  have hall := f_formula_extension hS fr hsq e μ hex hes heq hpq hbase hQ0
  rw [Subtype.ext hy]
  exact hall x

end Work.PSU3.StageC
