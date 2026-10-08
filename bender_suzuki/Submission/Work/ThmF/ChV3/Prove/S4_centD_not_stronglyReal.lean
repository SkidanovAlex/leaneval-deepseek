import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.centDLowerCentralizerS

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.S4_centD_not_stronglyReal`

Peterfalvi II, Ch. V §2 Lemma 4 (p. 246), in the contrapositive form used as leaf **S4** of the
§3 design: no non-trivial element of `V = C_D(t)` is strongly real, nor is any conjugate.

* `v ∈ V^#` has odd order: `v ∈ D = twoPoint H t`, and `D = H ⊓ Hᵗ` has odd order by strong
  embeddedness of `H` (`t ∉ H`); hence `v * v ≠ 1`.
* `s ∈ C_G(v)`: Ch. V §2 Lemma 3 a), `Prove/centDLowerCentralizerS` (`V ≤ C_G(s)`).
* So `|C_G(v)|` is even.  If `g v g⁻¹` were strongly real, then so would be `v` (conjugation
  preserves products of two involutions), and `ChV12.lemma4` forces `|C_G(v)|` odd: absurd.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3.Prove

open Submission.Blueprint

theorem S4_centD_not_stronglyReal {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    ∀ v ∈ Submission.Blueprint.centD H t, v ≠ 1 → ∀ g : G,
      ¬ Work.ThmF.ChV3.StronglyReal (g * v * g⁻¹) := by
  intro v hv hv1 g hsr
  -- ## (1) `orderOf v` is odd, hence `v * v ≠ 1`
  have hvD : v ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hv).1
  have hoddD : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    c.split.stronglyEmbedded.2.2 t c.split.not_mem
  have hodd : Odd (orderOf v) :=
    hoddD.of_dvd_nat
      (Subgroup.orderOf_dvd_natCard (Submission.Blueprint.twoPoint H t) hvD)
  have hvv : v * v ≠ 1 := by
    intro h
    have hdvd : orderOf v ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact hv1 (orderOf_eq_one_iff.mp h1)
    · rw [h2] at hodd
      exact absurd hodd (by norm_num)
  -- ## (2) `s` centralises `v`, so `|C_G(v)|` is even
  have hvs : v * s = s * v :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid hv)
  have hEven : Even (Nat.card ↥(Subgroup.centralizer ({v} : Set G))) := by
    have hle : Subgroup.zpowers s ≤ Subgroup.centralizer ({v} : Set G) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr hvs.symm)
    have hdv : Nat.card ↥(Subgroup.zpowers s) ∣
        Nat.card ↥(Subgroup.centralizer ({v} : Set G)) :=
      Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, c.s_inv] at hdv
    exact even_iff_two_dvd.mpr hdv
  -- ## (3) `g v g⁻¹` strongly real ⟹ `v` strongly real
  obtain ⟨a, b, ha, hb, hab⟩ := hsr
  have hsvr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = v := by
    refine ⟨g⁻¹ * a * g, g⁻¹ * b * g, ?_, ?_, ?_⟩
    · calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
        _ = 1 := by rw [ha]; group
    · calc (g⁻¹ * b * g) * (g⁻¹ * b * g) = g⁻¹ * (b * b) * g := by group
        _ = 1 := by rw [hb]; group
    · calc (g⁻¹ * a * g) * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
        _ = g⁻¹ * (g * v * g⁻¹) * g := by rw [hab]
        _ = v := by group
  -- ## (4) `ChV12.lemma4` forces `|C_G(v)|` odd
  have hoddC : Odd (Nat.card ↥(Subgroup.centralizer ({v} : Set G))) :=
    (Work.ThmF.ChV12.lemma4 c.sit hC4 H Q t c.split v hvv hsvr).2
  exact (Nat.not_even_iff_odd.mpr hoddC) hEven

end Work.ThmF.ChV3.Prove
