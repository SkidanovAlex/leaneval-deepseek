/-
# `Work.PSU3.StageC.psu3_coords_FT` — `psu3_coords` via the odd-order-theorem route

This is `Work.PSU3.StageC.psu3_coords` with `FeitThompsonProp` supplied as an explicit
hypothesis.  The only difference from the FT-free assembly is the source of the case-c data of
Peterfalvi II, Ch. VI §1: instead of the deep node `centD_le_W_of_PSU3Hyp` (`V ≤ W`, through
`caseC_data`), we obtain `W H t ≠ ⊥` from `hFT` via

* `Work.PSU3.StageA.W_ne_bot_of_PSU3HypFT` (Ch. V §1 Prop. 2 with the odd order theorem
  excluding Ch. VI §1 cases a) and b)),

and then feed it to `Work.PSU3.StageA.caseC_data_of_W_ne_bot`.  Everything downstream — the
coarse frame (A6), the `ω`-existence (B1/B2), the Frobenius-power normalisation (B3/C0), the fine
coordinates (C1) and the `f`-formula (C2) — is identical to `psu3_coords`, and is axiom-clean.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.StageA.centD_le_W_of_PSU3Hyp_closed
import Submission.Work.PSU3.StageB.exists_omega_of_fpf_rebuilt
import Submission.Work.PSU3.StageB.exists_omega_of_not_fpf_FT
import Submission.Work.PSU3.StageC.psu3_coords
import Submission.Work.PSU3.StageA.centD_le_W_of_PSU3HypFT
import Submission.Work.PSU3.StageA.W_ne_bot_of_PSU3HypFT
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.StageA.coarseFrame_exists
import Submission.Work.PSU3.StageB.theta_trivial
import Submission.Work.PSU3.StageC.frame_normalize
import Submission.Work.PSU3.StageC.fine_coords_holds
import Submission.Work.PSU3.StageC.f_formula

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3.StageC

/-- If `s` and `t` are involutions and `(s * t)³ = 1`, then `t * s * t = s * t * s`: in a
group, `(s * t)² = (s * t)⁻¹ = t * s`, and multiplying by `s` on the left gives the claim. -/
private lemma sts_of_cube_FT {G : Type} [Group G] {s t : G} (hs : s * s = 1) (ht : t * t = 1)
    (h : (s * t) ^ 3 = 1) : t * s * t = s * t * s := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ha3 : (s * t) ^ 2 * (s * t) = 1 := by rw [← pow_succ]; exact h
  have h2 : (s * t) ^ 2 = (s * t)⁻¹ := by
    have hh := congrArg (· * (s * t)⁻¹) ha3
    simpa [mul_assoc] using hh
  have hkey : s * t * s * t = t * s := by
    have h1 : s * t * s * t = (s * t) ^ 2 := by simp only [pow_two, mul_assoc]
    calc s * t * s * t = (s * t) ^ 2 := h1
      _ = (s * t)⁻¹ := h2
      _ = t * s := by rw [mul_inv_rev, hs', ht']
  have hsnd : s * (s * t * s) = t * s := by
    calc s * (s * t * s) = s * s * (t * s) := by simp only [mul_assoc]
      _ = 1 * (t * s) := by rw [hs]
      _ = t * s := one_mul _
  have hfin : s * (t * s * t) = s * (s * t * s) := by
    rw [show s * (t * s * t) = s * t * s * t from by simp only [mul_assoc], hkey, hsnd]
  exact mul_left_cancel hfin

/-- A nontrivial subgroup has a nontrivial element. -/
private lemma exists_ne_one_of_ne_bot_FT {G : Type} [Group G] {W : Subgroup G} (h : W ≠ ⊥) :
    ∃ ζ ∈ W, ζ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact h (eq_bot_iff.mpr (fun x hx => Subgroup.mem_bot.mpr (hcon x hx)))

theorem psu3_coords_FT {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) (hFT : Submission.Blueprint.FeitThompsonProp) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ e : Q ≃* SZ (Work.PSU3.E n),
      ∀ x y : Q, (x : G) ≠ 1 → Work.RankOneUniqueness.FRel H t (x : G) (y : G) →
        e y = Work.PSU3.fMapTot (e x) := by
  classical
  -- ### A1: the distinguished involution `s` and its partner `r`
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hS.split.invol] at h
    simpa [pow_two] using h
  have hs2' : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  -- ### Ch. VI §1: `W H t ≠ ⊥` from `FeitThompsonProp`, hence the case-c data
  have hWne : Work.ThmF.W H t ≠ ⊥ :=
    Work.PSU3.StageA.W_ne_bot_of_PSU3HypFT hS hC4 hFT
  obtain ⟨hcard3, h3, _hWne⟩ :=
    Work.PSU3.StageA.caseC_data_of_W_ne_bot hS hC4 hHig hs hs2 hr hsr hWne
  have hcube : (s * t) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (s * t)
    rwa [h3] at h
  have hst : t * s * t = s * t * s := sts_of_cube_FT hs2' ht2 hcube
  -- ### A6: a coarse frame with `zc 1 = s` and `fr.ζ = ζ` for a chosen `ζ ∈ W#`
  obtain ⟨ζ, hζW, hζ1⟩ := exists_ne_one_of_ne_bot_FT hWne
  obtain ⟨n, hn, _hQ0, fr, _hzcs, _hζ⟩ :=
    Work.PSU3.StageA.coarseFrame_exists hS hC4 hHig hs hs2 hr hsr hst hcard3 hζW hζ1
  -- ### B1/B2: an `ω` with `OmegaHyp` for some frame (same `n`)
  obtain ⟨fr₁, ω, hω⟩ : ∃ fr₁ : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G,
      Work.PSU3.OmegaHyp fr₁ ω := by
    by_cases hfpf : Work.PSU3.DFpfBar H Q t
    · exact Work.PSU3.StageB.exists_omega_of_fpf_rebuilt hS hC4 hHig fr hfpf
    · exact Work.PSU3.StageB.exists_omega_of_not_fpf_FT hS hC4 hHig fr hfpf
  -- ### B3: `nm` is a Frobenius power and `ω² = zc((ζ + ζ⁻¹)^{2^i})`
  obtain ⟨i, hi, hω2⟩ := Work.PSU3.StageB.theta_trivial hS fr₁ hω
  -- ### C0: renormalise `zc` so that `nm` is the squaring map
  obtain ⟨fr₂, _hQ0', hω', hsq, hω2'⟩ := Work.PSU3.StageC.frame_normalize fr₁ hω i hi hω2
  -- ### C1: fine coordinates `e : Q ≃* SZ (E n)`
  obtain ⟨e, μ, hex, hes, heq⟩ := Work.PSU3.StageC.fine_coords_holds fr₂ hsq
  -- ### C2: `f` becomes `fMapTot` in these coordinates
  exact ⟨n, hn, e, Work.PSU3.StageC.f_formula hS fr₂ hω' hsq hω2' e μ hex hes heq⟩

end Work.PSU3.StageC
