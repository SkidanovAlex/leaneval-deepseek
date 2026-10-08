import Mathlib
import Submission.Work.PSU3.StageC.FSuz
import Submission.Work.PSU3.StageC.ConjQ
import Submission.Work.PSU3.FMap.torusAct_mul
import Submission.Work.PSU3.FMap.torusAct_bijective
import Submission.Work.PSU3.StageC.fcan_gcan_inv_conjQ
import Submission.Work.PSU3.StageB.ThetaOmega
import Submission.Work.PSU3.StageC.sz_solve_torusAct

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.PSU3.StageB
open Work.PSU3

namespace Work.PSU3.StageC

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

section Helpers

/-- §2 (2) at `x = ρ⁻¹`, in the fine coordinates `e`: the recursion computed in
`Submission.Work.PSU3.StageC.FSuz.fcan_mul_zcQ`, with `f(ρ⁻¹) = ρ^{ζ'⁻¹}` substituted in the
inner argument and H3 used to move the conjugation by `ζ'⁻¹` outside `fcan`. -/
theorem e_fcan_inv_mul_zcQ {hS : Work.PSU3.PSU3Hyp H Q t} {fr : Work.PSU3.CoarseFrame H Q t n}
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (e : Q ≃* SZ (E n)) (μ : (E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    {ρ : Q} (hρ0 : (ρ : G) ∉ fr.Q0) {ζ' : fr.KW}
    (hζ'W : (ζ' : G) ∈ Work.ThmF.W H t)
    (hfρ : fcan hS.split ρ = conjQ hS fr ζ' ρ⁻¹)
    (hζ'fix : ∀ y : E n, σE y = y → (ζ' : G)⁻¹ * fr.zc y * (ζ' : G) = fr.zc y)
    {w : E n} (hw : σE w = w) (hw0 : w ≠ 0) :
    ∃ (A : fr.KW) (_ : (A : G) ∈ Work.ThmF.Ksub H t),
      ((fr.κ A : (E n)ˣ) : E n) = w⁻¹ ∧
      e (fcan hS.split (ρ⁻¹ * zcQ fr w hw)) =
        SZ.torusAct (fr.κ (ζ'⁻¹ * A))
            (e (fcan hS.split (ρ * zcQ fr w⁻¹ (by rw [map_inv₀, hw])))) *
          (⟨0, w⁻¹, by rw [map_inv₀, hw, CharTwo.add_self_eq_zero, zero_mul]⟩ :
            SZ (E n)) := by
  have hw' : σE w⁻¹ = w⁻¹ := by rw [map_inv₀, hw]
  have h1 : (1 : G) ∈ fr.Q0 := (fr.mem_Q0_iff 1 Q.one_mem).mpr (by simp)
  have hρne : (ρ : G) ≠ 1 := fun h => hρ0 (by rw [h]; exact h1)
  have hρinv0 : ((ρ⁻¹ : Q) : G) ∉ fr.Q0 := by
    intro h
    exact hρ0 (by simpa using (fr.Q0).inv_mem h)
  obtain ⟨A, hAK, hAκ, hAeq⟩ := fcan_mul_zcQ hS fr hsq (x := ρ⁻¹) hρinv0 w hw hw0
  refine ⟨A, hAK, hAκ, ?_⟩
  have hfρ' : (fcan hS.split ρ⁻¹ : Q) = conjQ hS fr ζ'⁻¹ ρ :=
    (fcan_gcan_inv_conjQ hS fr hρne ζ' hζ'W hfρ).1
  have hX : ((ρ * zcQ fr w⁻¹ hw' : Q) : G) ≠ 1 := by
    intro h
    have hEq : (ρ * zcQ fr w⁻¹ hw' : Q) = 1 := Subtype.ext h
    have h2 : ρ = (zcQ fr w⁻¹ hw')⁻¹ := by
      calc ρ = ρ * zcQ fr w⁻¹ hw' * (zcQ fr w⁻¹ hw')⁻¹ := by group
        _ = 1 * (zcQ fr w⁻¹ hw')⁻¹ := by rw [hEq]
        _ = (zcQ fr w⁻¹ hw')⁻¹ := one_mul _
    refine hρ0 ?_
    have h3 : ((ρ : Q) : G) = (((zcQ fr w⁻¹ hw' : Q)) : G)⁻¹ := by rw [h2]; rfl
    rw [h3]
    exact (fr.Q0).inv_mem (fr.zc_mem w⁻¹ hw')
  have hζ'Winv : (((ζ'⁻¹ : fr.KW)) : G) ∈ Work.ThmF.W H t := (Work.ThmF.W H t).inv_mem hζ'W
  have hζ't : (((ζ'⁻¹ : fr.KW)) : G) = t * (((ζ'⁻¹ : fr.KW)) : G) * t :=
    (t_conj_of_mem_W hS fr hζ'Winv).symm
  have hH3 : fcan hS.split (conjQ hS fr ζ'⁻¹ (ρ * zcQ fr w⁻¹ hw')) =
      conjQ hS fr ζ'⁻¹ (fcan hS.split (ρ * zcQ fr w⁻¹ hw')) :=
    fcan_conjQ_eq hS fr (d := ζ'⁻¹) (d' := ζ'⁻¹) hζ't hX
  have hkey : (fcan hS.split (ρ⁻¹ * zcQ fr w hw) : Q) =
      conjQ hS fr (ζ'⁻¹ * A) (fcan hS.split (ρ * zcQ fr w⁻¹ hw')) *
        zcQ fr w⁻¹ hw' := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, conjQ_coe, Subgroup.coe_mul]
    have h3 : (fcan hS.split ρ⁻¹ * zcQ fr w⁻¹ hw' : Q) =
        conjQ hS fr ζ'⁻¹ (ρ * zcQ fr w⁻¹ hw') := by
      rw [hfρ', conjQ_mul, conjQ_zcQ hS fr (fix_inv hζ'fix) w⁻¹ hw']
    have hinner : (fcan hS.split (fcan hS.split ρ⁻¹ * zcQ fr w⁻¹ hw') : Q) =
        conjQ hS fr ζ'⁻¹ (fcan hS.split (ρ * zcQ fr w⁻¹ hw')) := by
      rw [h3, hH3]
    rw [hAeq]
    show (A : G)⁻¹ * (fcan hS.split (fcan hS.split ρ⁻¹ * zcQ fr w⁻¹ hw') : G) *
          (A : G) * (zcQ fr w⁻¹ hw' : G) =
        ((conjQ hS fr (ζ'⁻¹ * A) (fcan hS.split (ρ * zcQ fr w⁻¹ hw')) *
          zcQ fr w⁻¹ hw' : Q) : G)
    rw [Subgroup.coe_mul, conjQ_coe, Subgroup.coe_mul, hinner, conjQ_coe]
    group
  rw [hkey, map_mul, e_conjQ hS fr e heq (ζ'⁻¹ * A) _,
    e_zcQ (hS := hS) (hsq := hsq) (e := e) (μ := μ) (hex := hex) (hes := hes)
      (heq := heq) (v := w⁻¹) (hv := hw'), map_mul]


/-- §2 (3) at `y = ρ⁻¹`, in the fine coordinates `e` (with `h(ρ⁻¹) = ζ'⁻³`, `g(ρ⁻¹) = ρ^{ζ'}`,
`f(ρ⁻¹) = ρ^{ζ'⁻¹}` substituted). -/
theorem e_fcan_zcQ_mul_inv {hS : Work.PSU3.PSU3Hyp H Q t} {fr : Work.PSU3.CoarseFrame H Q t n}
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (e : Q ≃* SZ (E n))
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    {ρ : Q} (hρ0 : (ρ : G) ∉ fr.Q0) {ζ' : fr.KW}
    (hζ'W : (ζ' : G) ∈ Work.ThmF.W H t)
    (hfρ : fcan hS.split ρ = conjQ hS fr ζ' ρ⁻¹)
    (hζ'fix : ∀ y : E n, σE y = y → (ζ' : G)⁻¹ * fr.zc y * (ζ' : G) = fr.zc y)
    (hhζ' : (hcan hS.split ρ⁻¹ : G) = ((((ζ'⁻¹ : fr.KW) ^ 3 : fr.KW)) : G))
    {w : E n} (hw : σE w = w) (hw0 : w ≠ 0) :
    e (fcan hS.split (zcQ fr w hw * ρ⁻¹)) =
      SZ.torusAct (fr.κ (((ζ' ^ 2)⁻¹)))
          (e (fcan hS.split (ρ * zcQ fr w⁻¹ (by rw [map_inv₀, hw])))) *
        SZ.torusAct (fr.κ ζ'⁻¹) (e ρ) := by
  have hw' : σE w⁻¹ = w⁻¹ := by rw [map_inv₀, hw]
  have h1 : (1 : G) ∈ fr.Q0 := (fr.mem_Q0_iff 1 Q.one_mem).mpr (by simp)
  have hρne : (ρ : G) ≠ 1 := fun h => hρ0 (by rw [h]; exact h1)
  have hρinvne : ((ρ⁻¹ : Q) : G) ≠ 1 := by
    intro h
    exact hρne (by simpa using congrArg Inv.inv h)
  have hzρ : ((zcQ fr w hw * ρ⁻¹ : Q) : G) ≠ 1 := by
    intro h
    have hEq : (zcQ fr w hw * ρ⁻¹ : Q) = 1 := Subtype.ext h
    have h2 : ρ⁻¹ = (zcQ fr w hw)⁻¹ := by
      calc ρ⁻¹ = (zcQ fr w hw)⁻¹ * (zcQ fr w hw * ρ⁻¹) := by group
        _ = (zcQ fr w hw)⁻¹ * 1 := by rw [hEq]
        _ = (zcQ fr w hw)⁻¹ := mul_one _
    have hρinv0 : ((ρ⁻¹ : Q) : G) ∈ fr.Q0 := by
      rw [h2]
      exact (fr.Q0).inv_mem (fr.zc_mem w hw)
    exact hρ0 (by simpa using (fr.Q0).inv_mem hρinv0)
  have hgρ : gcan hS.split ρ⁻¹ = conjQ hS fr ζ' ρ :=
    (fcan_gcan_inv_conjQ hS fr hρne ζ' hζ'W hfρ).2
  have hfρinv : fcan hS.split ρ⁻¹ = conjQ hS fr ζ'⁻¹ ρ :=
    (fcan_gcan_inv_conjQ hS fr hρne ζ' hζ'W hfρ).1
  have hζ'3W : ((((ζ'⁻¹ : fr.KW) ^ 3 : fr.KW)) : G) ∈ Work.ThmF.W H t :=
    (Work.ThmF.W H t).pow_mem ((Work.ThmF.W H t).inv_mem hζ'W) 3
  have ht : t * (hcan hS.split ρ⁻¹ : G) * t = ((((ζ'⁻¹ : fr.KW) ^ 3 : fr.KW)) : G) := by
    rw [hhζ', t_conj_of_mem_W hS fr hζ'3W]
  -- the argument of the inner `fcan`
  have hX : ((ρ * zcQ fr w⁻¹ hw' : Q) : G) ≠ 1 := by
    intro h
    have hEq : (ρ * zcQ fr w⁻¹ hw' : Q) = 1 := Subtype.ext h
    have h2 : ρ = (zcQ fr w⁻¹ hw')⁻¹ := by
      calc ρ = ρ * zcQ fr w⁻¹ hw' * (zcQ fr w⁻¹ hw')⁻¹ := by group
        _ = 1 * (zcQ fr w⁻¹ hw')⁻¹ := by rw [hEq]
        _ = (zcQ fr w⁻¹ hw')⁻¹ := one_mul _
    refine hρ0 ?_
    have h3 : ((ρ : Q) : G) = (((zcQ fr w⁻¹ hw' : Q)) : G)⁻¹ := by rw [h2]; rfl
    rw [h3]
    exact (fr.Q0).inv_mem (fr.zc_mem w⁻¹ hw')
  have hYne : ((zcQ fr w⁻¹ hw' * ρ : Q) : G) ≠ 1 := by
    intro h
    have hEq : (zcQ fr w⁻¹ hw' * ρ : Q) = 1 := Subtype.ext h
    have h3 : ρ = (zcQ fr w⁻¹ hw')⁻¹ := by
      have h2 := congrArg (fun z : Q => (zcQ fr w⁻¹ hw')⁻¹ * z) hEq
      simpa [mul_assoc] using h2
    have h4 : (ρ : G) = (((zcQ fr w⁻¹ hw' : Q)) : G)⁻¹ := by rw [h3]; rfl
    rw [h4] at hρ0
    exact hρ0 ((fr.Q0).inv_mem (fr.zc_mem w⁻¹ hw'))
  -- `ζ'` commutes with `fcan` (H3)
  have hζ't : ((ζ' : fr.KW) : G) = t * ((ζ' : fr.KW) : G) * t :=
    (t_conj_of_mem_W hS fr hζ'W).symm
  have hH3 : fcan hS.split (conjQ hS fr ζ' (zcQ fr w⁻¹ hw' * ρ)) =
      conjQ hS fr ζ' (fcan hS.split (zcQ fr w⁻¹ hw' * ρ)) :=
    fcan_conjQ_eq hS fr (d := ζ') (d' := ζ') hζ't hYne
  have hinner : (fcan hS.split (zcQ fr w⁻¹ hw' * gcan hS.split ρ⁻¹) : Q) =
      conjQ hS fr ζ' (fcan hS.split (ρ * zcQ fr w⁻¹ hw')) := by
    have harg : (zcQ fr w⁻¹ hw' * gcan hS.split ρ⁻¹ : Q) =
        conjQ hS fr ζ' (zcQ fr w⁻¹ hw' * ρ) := by
      rw [hgρ, conjQ_mul, conjQ_zcQ hS fr hζ'fix w⁻¹ hw']
    have hcomm : (zcQ fr w⁻¹ hw' * ρ : Q) = ρ * zcQ fr w⁻¹ hw' :=
      Subtype.ext (fr.Q0_central (fr.zc w⁻¹) (fr.zc_mem w⁻¹ hw') (ρ : G) ρ.2)
    rw [harg, hH3, hcomm]
  -- the §2 (3) recursion
  have h6 := fcan_zcQ_mul hS fr hsq (p := ρ⁻¹) hρinvne (w := w) hw hw0 hzρ
  have hkey : (fcan hS.split (zcQ fr w hw * ρ⁻¹) : Q) =
      conjQ hS fr (((ζ' ^ 2)⁻¹)) (fcan hS.split (ρ * zcQ fr w⁻¹ hw')) *
        conjQ hS fr ζ'⁻¹ ρ := by
    have hY : (t * (hcan hS.split ρ⁻¹ : G) * t)⁻¹ *
          (fcan hS.split (zcQ fr w⁻¹ hw' * gcan hS.split ρ⁻¹) : G) *
          (t * (hcan hS.split ρ⁻¹ : G) * t) =
        ((conjQ hS fr (((ζ'⁻¹ : fr.KW) ^ 3 : fr.KW))
            (fcan hS.split (zcQ fr w⁻¹ hw' * gcan hS.split ρ⁻¹)) : Q) : G) := by
      rw [ht]
      rfl
    apply Subtype.ext
    rw [Subgroup.coe_mul, h6, hY, hfρinv]
    congr 1
    rw [hinner, conjQ_conjQ,
      show ζ' * (((ζ'⁻¹ : fr.KW) ^ 3 : fr.KW)) = ((ζ' ^ 2)⁻¹) from by group]
  rw [hkey, map_mul, e_conjQ hS fr e heq (((ζ' ^ 2)⁻¹)) _, e_conjQ hS fr e heq (ζ'⁻¹) ρ]

/-- **The `ω`-coset formula** (Peterfalvi II, Ch. VII §3 (1)–(4)): for `ρ` with
`f(ρ) = (ρ⁻¹)^{ζ'}`, `ζ' ∈ W#`, and the coordinate data of `ρ` (its `e`-image is `(A, c)` with
`c = (κζ')⁻¹` and `A·σA = c + c⁻¹`), the model map `f` agrees with `fMapTot` at every
`ρ·zcQ u` with `u ∈ F ∖ {0, 1}`.

The degenerate point `u = 1` of the relation (1) is covered in `f_formula_on_omega_coset` by a
second application of this lemma with `(ρ, ζ')` replaced by `(ρ⁻¹, ζ'⁻¹)`. -/
theorem e_fcan_coset {hS : Work.PSU3.PSU3Hyp H Q t} {fr : Work.PSU3.CoarseFrame H Q t n}
    (hsq : ∀ a : (E n)ˣ, σE (a : E n) = a → (fr.nm a : E n) = (a : E n) ^ 2)
    (e : Q ≃* SZ (E n)) (μ : (E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    {ρ : Q} (hρ0 : (ρ : G) ∉ fr.Q0) {ζ' : fr.KW}
    (hζ'W : (ζ' : G) ∈ Work.ThmF.W H t) (hζ'ne : ζ' ≠ 1)
    (hζ'fix : ∀ y : E n, σE y = y → (ζ' : G)⁻¹ * fr.zc y * (ζ' : G) = fr.zc y)
    (hζ'norm : (((fr.κ ζ' : (E n)ˣ)) : E n) * σE ((((fr.κ ζ' : (E n)ˣ)) : E n)) = 1)
    (hfρ : fcan hS.split ρ = conjQ hS fr ζ' ρ⁻¹)
    (hhζ' : (hcan hS.split ρ⁻¹ : G) = ((((ζ'⁻¹ : fr.KW) ^ 3 : fr.KW)) : G))
    (hρA : (e ρ).x * σE ((e ρ).x) =
      ((((fr.κ ζ' : (E n)ˣ)) : E n))⁻¹ + (((((fr.κ ζ' : (E n)ˣ)) : E n))⁻¹)⁻¹)
    (hρy : (e ρ).y = ((((fr.κ ζ' : (E n)ˣ)) : E n))⁻¹)
    {u : E n} (hu : σE u = u) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    e (fcan hS.split (ρ * zcQ fr u hu)) = Work.PSU3.fMapTot (e (ρ * zcQ fr u hu)) := by
  set c : E n := (((fr.κ ζ' : (E n)ˣ)) : E n)⁻¹ with hcdef
  have hu' : σE u⁻¹ = u⁻¹ := by rw [map_inv₀, hu]
  -- scalar facts about `c`
  have hcσ : c * σE c = 1 := by
    rw [hcdef, map_inv₀, ← mul_inv_rev, mul_comm (σE (((fr.κ ζ' : (E n)ˣ)) : E n)),
      hζ'norm, inv_one]
  have hc0 : c ≠ 0 := by
    intro h
    have h1 : c * σE c = 0 := by rw [h, zero_mul]
    rw [hcσ] at h1
    exact one_ne_zero h1
  have hc1 : c ≠ 1 := by
    intro h
    have hκ : fr.κ ζ' = 1 := by
      have h2 := congrArg Inv.inv h
      rw [hcdef] at h2
      simpa using h2
    exact hζ'ne (fr.κ_injective (by rw [hκ, map_one]))
  have hcu : c + u ≠ 0 := by
    intro h
    have h1 : c = u := by
      have h2 : c = -u := eq_neg_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at h2
    have hσc : σE c = c := by rw [h1, hu]
    have hcc : c * c = 1 := by simpa [hσc] using hcσ
    have h2 : (c + 1) * (c + 1) = 0 := by
      rw [← pow_two, CharTwo.add_sq, one_pow, pow_two, hcc]
      exact CharTwo.add_self_eq_zero 1
    have h3 : c + 1 = 0 := mul_self_eq_zero.mp h2
    have h4 : c = 1 := by
      have h5 := eq_neg_of_add_eq_zero_left h3
      rw [CharTwo.neg_eq] at h5
      exact h5
    exact hc1 h4
  -- non-vanishing of the argument
  have h1 : (1 : G) ∈ fr.Q0 := (fr.mem_Q0_iff 1 Q.one_mem).mpr (by simp)
  have hρx0 : (e ρ).x ≠ 0 := by
    intro h
    have hbar : fr.bar ρ = 1 := by
      have h2 : (μ : E n) * Multiplicative.toAdd (fr.bar ρ) = 0 := by rw [← hex ρ, h]
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (Units.ne_zero μ)
      · simpa using h3
    exact hρ0 ((fr.bar_eq_one_iff ρ).mp hbar)
  -- the two recursions at parameter `u⁻¹`
  obtain ⟨A, hAK, hAκ, ha⟩ :=
    e_fcan_inv_mul_zcQ (hS := hS) (fr := fr) hsq e μ hex hes heq (ρ := ρ) hρ0 (ζ' := ζ') hζ'W hfρ
      hζ'fix (w := u⁻¹) hu' (inv_ne_zero hu0)
  have hb := e_fcan_zcQ_mul_inv (hS := hS) (fr := fr) hsq e heq (ρ := ρ) hρ0 (ζ' := ζ') hζ'W hfρ
    hζ'fix hhζ' (w := u⁻¹) hu' (inv_ne_zero hu0)
  -- the two sides agree
  have hcomm : (ρ⁻¹ * zcQ fr u⁻¹ hu' : Q) = (zcQ fr u⁻¹ hu' * ρ⁻¹ : Q) :=
    Subtype.ext (by
      simp only [Subgroup.coe_mul]
      exact (fr.Q0_central (fr.zc u⁻¹) (fr.zc_mem u⁻¹ hu') (ρ⁻¹ : G) (Q.inv_mem ρ.2)).symm)
  have hEq : SZ.torusAct (fr.κ (ζ'⁻¹ * A)) (e (fcan hS.split (ρ * zcQ fr u hu))) *
      (⟨0, u, by rw [hu, CharTwo.add_self_eq_zero, zero_mul]⟩ : SZ (E n)) =
      SZ.torusAct (fr.κ ((ζ' ^ 2)⁻¹)) (e (fcan hS.split (ρ * zcQ fr u hu))) *
        SZ.torusAct (fr.κ ζ'⁻¹) (e ρ) := by
    simp only [inv_inv] at ha hb
    rw [← ha, ← hb, hcomm]
  -- solve the resulting scalar system
  have hA : (e ρ).x * σE ((e ρ).x) = c + c⁻¹ := by rw [hcdef]; exact hρA
  have hq2x : (SZ.torusAct (fr.κ ζ'⁻¹) (e ρ)).x = c * (e ρ).x := by
    rw [SZ.torusAct_x, map_inv, Units.val_inv_eq_inv_val, hcdef]
  have hσa : σE (((fr.κ ζ' : (E n)ˣ)) : E n) = (((fr.κ ζ' : (E n)ˣ)) : E n)⁻¹ :=
    eq_inv_of_mul_eq_one_right hζ'norm
  have hq2y : (SZ.torusAct (fr.κ ζ'⁻¹) (e ρ)).y = c := by
    rw [SZ.torusAct_y]
    have h1 : (((fr.κ ζ'⁻¹ : (E n)ˣ)) : E n) * σE ((((fr.κ ζ'⁻¹ : (E n)ˣ)) : E n)) = 1 := by
      rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, hσa, inv_inv]
      exact inv_mul_cancel₀ (Units.ne_zero (fr.κ ζ'))
    rw [h1, one_mul, hρy, hcdef]
  have hcu2 : (((fr.κ (ζ'⁻¹ * A) : (E n)ˣ)) : E n) = c * u := by
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hAκ, inv_inv, hcdef]
  have hc2u : (((fr.κ ((ζ' ^ 2)⁻¹) : (E n)ˣ)) : E n) = c ^ 2 := by
    rw [map_inv, map_pow, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    rw [hcdef]
    rw [inv_pow]
  obtain ⟨hpx, hpy⟩ := sz_solve_torusAct
    (p := e (fcan hS.split (ρ * zcQ fr u hu)))
    (q₁ := ⟨0, u, by rw [hu, CharTwo.add_self_eq_zero, zero_mul]⟩)
    (q₂ := SZ.torusAct (fr.κ ζ'⁻¹) (e ρ))
    (A := (e ρ).x) (c := c) (w := u)
    (cu := fr.κ (ζ'⁻¹ * A)) (c2u := fr.κ ((ζ' ^ 2)⁻¹))
    hcu2 hc2u rfl rfl hq2x hq2y hc0 hu0 hu1 hcu hcσ hA hu hEq
  -- identify `e (ρ * zcQ u)` and conclude
  have hρu : e (ρ * zcQ fr u hu) = (e ρ) * (⟨0, u, by rw [hu, CharTwo.add_self_eq_zero,
      zero_mul]⟩ : SZ (E n)) := by
    rw [map_mul, e_zcQ (hS := hS) (hsq := hsq) (e := e) (μ := μ) (hex := hex) (hes := hes)
      (heq := heq) (v := u) (hv := hu)]
  have hρux : (e (ρ * zcQ fr u hu)).x = (e ρ).x := by
    rw [hρu, SZ.mul_x]
    simp
  have hρuy : (e (ρ * zcQ fr u hu)).y = c + u := by
    rw [hρu, SZ.mul_y, hρy]
    simp
  have hpne : e (ρ * zcQ fr u hu) ≠ 1 := by
    intro h
    have h2 : (e (ρ * zcQ fr u hu)).x = 0 := by rw [h]; rfl
    exact hρx0 (by rw [← hρux]; exact h2)
  rw [Work.PSU3.fMapTot_of_ne_one hpne, SZ.eq_iff]
  refine ⟨?_, ?_⟩
  · rw [SZ.fMap_x, hρux, hρuy, hpx]
  · rw [SZ.fMap_y, hρuy, hpy]

/-- The point `ρ` itself: `f(ρ) = (ρ⁻¹)^{ζ'}` in the fine coordinates reads
`e (f(ρ)) = fMapTot (e ρ)` (Peterfalvi II Ch. VII §3 (4), the case `y = ζ'⁻¹`). -/
theorem e_fcan_self {hS : Work.PSU3.PSU3Hyp H Q t} {fr : Work.PSU3.CoarseFrame H Q t n}
    (e : Q ≃* SZ (E n)) (μ : (E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : E n) * Multiplicative.toAdd (fr.bar x))
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    {ρ : Q} (hρ0 : (ρ : G) ∉ fr.Q0) {ζ' : fr.KW}
    (hζ'norm : (((fr.κ ζ' : (E n)ˣ)) : E n) * σE ((((fr.κ ζ' : (E n)ˣ)) : E n)) = 1)
    (hfρ : fcan hS.split ρ = conjQ hS fr ζ' ρ⁻¹)
    (hρy : (e ρ).y = ((((fr.κ ζ' : (E n)ˣ)) : E n))⁻¹)
    (hρA : (e ρ).x * σE ((e ρ).x) =
      ((((fr.κ ζ' : (E n)ˣ)) : E n))⁻¹ + (((((fr.κ ζ' : (E n)ˣ)) : E n))⁻¹)⁻¹) :
    e (fcan hS.split ρ) = Work.PSU3.fMapTot (e ρ) := by
  set c : E n := ((((fr.κ ζ' : (E n)ˣ)) : E n))⁻¹ with hcdef
  have hcσ : c * σE c = 1 := by
    rw [hcdef, map_inv₀, ← mul_inv_rev, mul_comm (σE (((fr.κ ζ' : (E n)ˣ)) : E n)),
      hζ'norm, inv_one]
  have hA : (e ρ).x * σE ((e ρ).x) = c + c⁻¹ := by rw [hcdef]; exact hρA
  have hy : (e ρ).y = c := by rw [hcdef]; exact hρy
  have hx0 : (e ρ).x ≠ 0 := by
    intro h
    refine hρ0 ?_
    have hbar : fr.bar ρ = 1 := by
      have h2 : (μ : E n) * Multiplicative.toAdd (fr.bar ρ) = 0 := by rw [← hex ρ, h]
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (Units.ne_zero μ)
      · simpa using h3
    exact (fr.bar_eq_one_iff ρ).mp hbar
  have hpne : e ρ ≠ 1 := by
    intro h
    exact hx0 (by rw [h]; rfl)
  have hkey : e (fcan hS.split ρ) = SZ.torusAct (fr.κ ζ') ((e ρ)⁻¹) := by
    rw [hfρ, e_conjQ hS fr e heq ζ' ρ⁻¹, map_inv]
  have hκζ : ((fr.κ ζ' : (E n)ˣ) : E n) = c⁻¹ := by rw [hcdef, inv_inv]
  rw [Work.PSU3.fMapTot_of_ne_one hpne, SZ.eq_iff]
  refine ⟨?_, ?_⟩
  · rw [hkey, SZ.torusAct_x, hκζ, SZ.inv_x, SZ.fMap_x, CharTwo.neg_eq, hy, div_eq_mul_inv,
      mul_comm]
  · have hc0 : c ≠ 0 := by
      rw [hcdef]
      exact inv_ne_zero (Units.ne_zero (fr.κ ζ'))
    have hσc : σE c = c⁻¹ := eq_inv_of_mul_eq_one_right hcσ
    have h1 : c⁻¹ * σE c⁻¹ = 1 := by
      rw [map_inv₀, hσc, inv_inv]
      exact mul_inv_cancel₀ (Units.ne_zero (fr.κ ζ'))
    rw [hkey, SZ.torusAct_y, hκζ, SZ.inv_y, SZ.fMap_y, hy, h1, one_mul]
    rw [CharTwo.neg_eq, hA, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

end Helpers

theorem f_formula_on_omega_coset {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
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
    ∀ u : Q, (u : G) ∈ fr.Q0 →
      e (Work.PSU3.StageB.fcan hS.split (⟨ω, hω.1⟩ * u)) =
        Work.PSU3.fMapTot (e (⟨ω, hω.1⟩ * u)) := by
  intro u hu
  have hω' : Work.PSU3.OmegaHyp fr ω := hω
  obtain ⟨hωQ, hωQ0, g, hg, hh, hhW, hωt⟩ := hω
  set ρ : Q := ⟨ω, hωQ⟩ with hρdef
  have hρcoe : (ρ : G) = ω := rfl
  have hρ0 : (ρ : G) ∉ fr.Q0 := by rw [hρcoe]; exact hωQ0
  have hρne : (ρ : G) ≠ 1 := by
    intro h
    exact hρ0 (by rw [h]; exact (fr.mem_Q0_iff 1 Q.one_mem).mpr (by simp))
  have hρomQ : ρ = Work.PSU3.StageB.omQ fr hω' := rfl
  -- the canonical data of `ω` (Ch. VII §3 (1))
  have hTheta := Work.PSU3.StageB.ThetaOmega fr hS.split hω' (g := g) hg (hh := hh) hhW hωt
  have hfρ : fcan hS.split ρ = conjQ hS fr fr.ζ ρ⁻¹ := by
    apply Subtype.ext
    rw [conjQ_coe]
    have h1 : (fcan hS.split ρ : G) = (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G) := by
      rw [hρomQ]; exact hTheta.2.2.1
    rw [h1, Subgroup.coe_inv, hρcoe]
  have hhρW : (hcan hS.split ρ : G) ∈ Work.ThmF.W H t := by
    rw [hρomQ]
    rw [hTheta.2.1]; exact hhW
  have hhρinv : (hcan hS.split ρ⁻¹ : G) = ((((fr.ζ⁻¹ : fr.KW) ^ 3 : fr.KW)) : G) := by
    rw [hρomQ]
    rw [hTheta.2.2.2, Subgroup.coe_pow, Subgroup.coe_inv]
    group
  have hρy : (e ρ).y = (((fr.κ fr.ζ : (E n)ˣ)) : E n)⁻¹ := by
    simpa using hωcoord
  -- the Hermitian data of `ρ` (Ch. VII §3 (3))
  have hαfix : σE ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) =
      ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) := by
    rw [map_add, map_inv₀, eq_inv_of_mul_eq_one_right fr.ζ_norm, inv_inv, add_comm]
  have hρsq : ρ * ρ = zcQ fr ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
      ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) hαfix := by
    apply Subtype.ext
    show (ρ : G) * (ρ : G) = fr.zc _
    rw [hρcoe, ← pow_two, hω2]
  have hρA : (e ρ).x * σE ((e ρ).x) =
      ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹ + (((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹)⁻¹ := by
    have h2 : e (ρ * ρ) = e ρ * e ρ := map_mul e ρ ρ
    have hzc := e_zcQ (hS := hS) (hsq := hsq) (e := e) (μ := μ) (hex := hex) (hes := hes)
      (heq := heq) (v := ((fr.κ fr.ζ : (E n)ˣ) : E n) + (((fr.κ fr.ζ : (E n)ˣ) : E n))⁻¹)
      (hv := hαfix)
    rw [hρsq, hzc] at h2
    have h5 := congrArg (fun p : SZ (E n) => p.y) h2.symm
    simp only at h5
    rw [SZ.mul_y, hρy] at h5
    rw [CharTwo.add_self_eq_zero, zero_add] at h5
    rw [h5, inv_inv]
    ring
  -- parametrise `Q₀` by the fixed field
  obtain ⟨v, hv, hzv⟩ := fr.zc_surj u hu
  have hueq : u = zcQ fr v hv := by
    apply Subtype.ext
    show (u : G) = fr.zc v
    exact hzv.symm
  subst hueq
  by_cases hv0 : v = 0
  · -- `u = 1`
    have hzc0 : zcQ fr v hv = 1 := by
      apply Subtype.ext
      show fr.zc v = 1
      rw [hv0]
      exact Work.PSU3.StageB.zc_zero fr
    rw [hzc0, mul_one]
    exact e_fcan_self (hS := hS) (fr := fr) e μ hex heq hρ0 fr.ζ_norm hfρ hρy hρA
  · by_cases hv1 : v = 1
    · -- the exceptional point `ρ·s`: the pair `(ρ⁻¹, ζ⁻¹)`
      subst hv1
      have hρ'0 : ((ρ⁻¹ : Q) : G) ∉ fr.Q0 := by
        intro h
        exact hρ0 (by simpa using (fr.Q0).inv_mem h)
      have hζ''W : ((fr.ζ⁻¹ : fr.KW) : G) ∈ Work.ThmF.W H t :=
        (Work.ThmF.W H t).inv_mem fr.ζ_mem_W
      have hζ''ne : (fr.ζ⁻¹ : fr.KW) ≠ 1 := by
        intro h
        have h2 : fr.ζ = 1 := by
          have h3 := congrArg Inv.inv h
          simpa using h3
        exact fr.ζ_ne_one h2
      have hζ''fix : ∀ y : E n, σE y = y →
          (((fr.ζ⁻¹ : fr.KW)) : G)⁻¹ * fr.zc y * (((fr.ζ⁻¹ : fr.KW)) : G) = fr.zc y :=
        fix_inv (zeta_fix fr)
      have hζ''norm : (((fr.κ (fr.ζ⁻¹) : (E n)ˣ)) : E n) *
          σE ((((fr.κ (fr.ζ⁻¹) : (E n)ˣ)) : E n)) = 1 := by
        rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv_rev,
          mul_comm (σE (((fr.κ fr.ζ : (E n)ˣ)) : E n)), fr.ζ_norm, inv_one]
      have hfρ' : fcan hS.split ρ⁻¹ = conjQ hS fr (fr.ζ⁻¹) ρ :=
        (fcan_gcan_inv_conjQ hS fr hρne fr.ζ fr.ζ_mem_W hfρ).1
      have hcan_rho : (hcan hS.split ρ : G) = (fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G) := by
        have h4b := Work.PSU3.StageB.hcan_inv hS.split hρne
        rw [hρomQ, hTheta.2.2.2] at h4b
        have htx : t * (hcan hS.split ρ : G) * t = (hcan hS.split ρ : G) := by
          have hmem : (hcan hS.split ρ : G) ∈ centD H t := Work.ThmF.W_le_centD H t hhρW
          have hct : t * (hcan hS.split ρ : G) = (hcan hS.split ρ : G) * t :=
            (Subgroup.mem_centralizer_iff.mp hmem.2) t (by simp)
          rw [hct, mul_assoc, t_mul_self hS, mul_one]
        have h2 : t * (hcan hS.split ρ : G)⁻¹ * t = (hcan hS.split ρ : G)⁻¹ := by
          rw [← Work.PSU3.RankOne.tdt_inv_eq (a := (hcan hS.split ρ : G)) (t_mul_self hS), htx]
        have h2' : t * (hcan hS.split ((Work.PSU3.StageB.omQ fr hω')) : G)⁻¹ * t =
            (hcan hS.split ((Work.PSU3.StageB.omQ fr hω')) : G)⁻¹ := by
          rw [← hρomQ]; exact h2
        rw [h2'] at h4b
        have h7 : (hcan hS.split ρ : G) = (fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G) := by
          have h8 : (hcan hS.split ((Work.PSU3.StageB.omQ fr hω')) : G) =
              ((fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹)⁻¹ := by
            have h8' := congrArg Inv.inv h4b
            rw [inv_inv] at h8'
            exact h8'.symm
          have h9 : ((fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹)⁻¹ =
              (fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G) := by
            simp only [mul_inv_rev, inv_inv, mul_assoc]
          rw [hρomQ, h8, h9]
        exact h7
      have hhζ'' : (hcan hS.split ρ : G) = ((((fr.ζ : fr.KW)) ^ 3 : fr.KW) : G) := by
        rw [hcan_rho, Subgroup.coe_pow, pow_succ, pow_succ, pow_one]
      have hfρX : fcan hS.split (ρ⁻¹) = conjQ hS fr (fr.ζ⁻¹) ((ρ⁻¹)⁻¹) := by
        rw [inv_inv]; exact hfρ'
      have hhρWX : (hcan hS.split (ρ⁻¹)⁻¹ : G) =
          ((((fr.ζ⁻¹)⁻¹ : fr.KW) ^ 3 : fr.KW) : G) := by
        simpa [inv_inv] using hhζ''
      have hρ'x : (e (ρ⁻¹)).x = (e ρ).x := by
        rw [map_inv, SZ.inv_x, CharTwo.neg_eq]
      have hρ'y : (e (ρ⁻¹)).y = (((fr.κ (fr.ζ⁻¹) : (E n)ˣ)) : E n)⁻¹ := by
        rw [map_inv, SZ.inv_y, hρy, hρA, map_inv, Units.val_inv_eq_inv_val, inv_inv,
          ← add_assoc, CharTwo.neg_eq, CharTwo.add_self_eq_zero, zero_add]
      have hρ'A : (e (ρ⁻¹)).x * σE ((e (ρ⁻¹)).x) =
          (((fr.κ (fr.ζ⁻¹) : (E n)ˣ)) : E n)⁻¹ +
            ((((fr.κ (fr.ζ⁻¹) : (E n)ˣ)) : E n)⁻¹)⁻¹ := by
        have hρA' := hρA
        rw [inv_inv] at hρA'
        rw [hρ'x, map_inv, Units.val_inv_eq_inv_val, inv_inv, hρA']
        ring
      -- `ρ² = zcQ α`, `ρ⁻¹ = ρ·zcQ α`, hence `ρ·s = ρ⁻¹·zcQ(1+α)` with `α = κζ + (κζ)⁻¹`
      have h1α : σE (1 + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
          ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹)) =
          1 + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) := by
        rw [map_add, map_one, hαfix]
      have hsqα : zcQ fr ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
          ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) hαfix *
          zcQ fr ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
            ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) hαfix = 1 := by
        rw [← zcQ_mul]
        apply Subtype.ext
        show fr.zc _ = 1
        rw [CharTwo.add_self_eq_zero, Work.PSU3.StageB.zc_zero]
      have hρinv_eq : ρ⁻¹ = ρ * zcQ fr ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
          ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) hαfix := by
        have h1 : ρ * (ρ * zcQ fr ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
            ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) hαfix) = 1 := by
          rw [← mul_assoc, hρsq, hsqα]
        exact (eq_inv_of_mul_eq_one_right h1).symm
      have hsum : ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) +
          (1 + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹)) = 1 := by
        rw [add_comm (1 : E n), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      have hαsum : σE ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹ +
          (1 + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹))) =
          ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹ +
            (1 + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹))) := by
        simp only [map_add, map_one, hαfix]
      have hpt : ρ * zcQ fr 1 hv = ρ⁻¹ * zcQ fr (1 + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
          ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹)) h1α := by
        have hzc : zcQ fr 1 hv = zcQ fr ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
            ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹ + (1 + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
            ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹))) hαsum := by
          apply Subtype.ext
          show fr.zc 1 = fr.zc ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹ +
            (1 + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹)))
          rw [hsum]
        rw [hzc, hρinv_eq, mul_assoc, ← zcQ_mul]
      -- `α ≠ 0`
      have hα0 : ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) ≠ 0 := by
        intro h
        have h2 : ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹ = (((fr.κ fr.ζ : (E n)ˣ)) : E n) := by
          have hh : (((fr.κ fr.ζ : (E n)ˣ)) : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹ =
              (((fr.κ fr.ζ : (E n)ˣ)) : E n) + (((fr.κ fr.ζ : (E n)ˣ)) : E n) := by
            rw [h]
            exact (CharTwo.add_self_eq_zero (((fr.κ fr.ζ : (E n)ˣ)) : E n)).symm
          exact add_left_cancel hh
        have h4 : (((fr.κ fr.ζ : (E n)ˣ)) : E n) * (((fr.κ fr.ζ : (E n)ˣ)) : E n) = 1 := by
          nth_rewrite 2 [← h2]
          exact mul_inv_cancel₀ (Units.ne_zero (fr.κ fr.ζ))
        have h5 : ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + 1) *
            ((((fr.κ fr.ζ : (E n)ˣ)) : E n) + 1) = 0 := by
          rw [← pow_two, CharTwo.add_sq, one_pow, pow_two, h4]
          exact CharTwo.add_self_eq_zero 1
        have h6 : (((fr.κ fr.ζ : (E n)ˣ)) : E n) + 1 = 0 := mul_self_eq_zero.mp h5
        have h7 : (((fr.κ fr.ζ : (E n)ˣ)) : E n) = 1 := by
          have hh := eq_neg_of_add_eq_zero_left h6
          rw [CharTwo.neg_eq] at hh
          exact hh
        exact fr.ζ_ne_one (fr.κ_injective (by
          apply Units.ext
          rw [h7, map_one]
          rfl))
      have h1α_ne1 : (1 : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
          ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) ≠ 1 := by
        intro h
        refine hα0 ?_
        have hh : (1 : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
            ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) = (1 : E n) + 0 := by
          rw [h, add_zero]
        exact add_left_cancel hh
      by_cases h1α0 : (1 : E n) + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
          ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹) = 0
      · have hz : zcQ fr (1 + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
            ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹)) h1α = 1 := by
          apply Subtype.ext
          show fr.zc (1 + ((((fr.κ fr.ζ : (E n)ˣ)) : E n) +
            ((((fr.κ fr.ζ : (E n)ˣ)) : E n))⁻¹)) = 1
          rw [h1α0, Work.PSU3.StageB.zc_zero]
        have h2 : ρ * zcQ fr 1 hv = ρ⁻¹ := by
          rw [hpt, hz, mul_one]
        rw [h2]
        exact e_fcan_self (hS := hS) (fr := fr) e μ hex heq hρ'0 hζ''norm hfρX hρ'y hρ'A
      · have h := e_fcan_coset (hS := hS) (fr := fr) hsq e μ hex hes heq (ρ := ρ⁻¹) hρ'0
          (ζ' := fr.ζ⁻¹) hζ''W hζ''ne hζ''fix hζ''norm hfρX hhρWX hρ'A hρ'y h1α h1α0 h1α_ne1
        rw [hpt]
        exact h
    · exact e_fcan_coset (hS := hS) (fr := fr) hsq e μ hex hes heq (ρ := ρ) hρ0 fr.ζ_mem_W
        fr.ζ_ne_one (zeta_fix fr) fr.ζ_norm hfρ hhρinv hρA hρy hv hv0 hv1


end Work.PSU3.StageC
