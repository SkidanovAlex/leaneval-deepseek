/-
# `Work.PSU3.StageB.Omega.omegaHyp_of_good`

The final reduction of Peterfalvi II, Ch. VII §2: a **good** element `ω ∈ Q ∖ Q₀` whose square
is the `Q₀`-shift of its own canonical data,

  `f (ω) = (ω · zc α)^ζ`   and   `ω * ω = zc α`      (`α ∈ F*`),

already satisfies `OmegaHyp fr ω`, i.e. `f (ω) = ζ⁻¹ ω⁻¹ ζ` **and** `h (ω) ∈ W`.

`f (ω) = ζ⁻¹ ω⁻¹ ζ` is immediate: `ω⁻¹ = ω · ω² = ω · zc α`, so `(ω · zc α)^ζ = (ω⁻¹)^ζ`
(`fcan_eq_zeta_inv_of_sq`).

The point of this file is `h (ω) ∈ W`, which in Peterfalvi's proof (p. 274) is obtained from
§2 (18) together with the *group theory* of `D` (odd-order Frobenius complement, so cyclic Sylow
subgroups, `W ⊴ D`).  That group theory is not needed: **H5 (Peterfalvi II Ch. VII §1) plus
`D`-fixed-point-freeness on `(Q/Q₀)^#` (`DFpfBar`) suffice**.

Indeed, `f (ω) = ζ⁻¹ ω⁻¹ ζ` means `f = c_ζ ∘ j` on the `⟨f, j⟩`-orbit of `ω`, so that
`(f ∘ j)³(ω) = ζ³ ω ζ⁻³` (`fcan_jjj_zeta_of`).  H5 (`fcan_jjj`) says
`(f ∘ j)³(ω) = h(ω) ω h(ω)⁻¹`.  Hence `ζ⁻³ h(ω)` centralises `ω`; it lies in `D`, and `ω ∉ Q₀`,
so `DFpfBar` forces `ζ⁻³ h(ω) = 1`, i.e. `h(ω) = ζ³ ∈ W`.

This removes the "Sylow subgroups of `D` are cyclic" input from Stage B entirely.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.Seq
import Submission.Work.PSU3.StageB.Omega.omegaHyp_of_sq
import Submission.Work.PSU3.StageB.NotFpfAux
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.ThetaOmega
import Submission.Work.PSU3.StageB.ThetaOmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## `h (ω) = ζ³` -/

/-- **H5 + `DFpfBar`.**  If `ω ∈ Q ∖ Q₀` and `f (ω) = ζ⁻¹ ω⁻¹ ζ`, then `h (ω) = ζ³`.

`(f ∘ j)³(ω) = ζ³ ω ζ⁻³` (because `f = c_ζ ∘ j` on the orbit of `ω` under `⟨f, j⟩`), while
H5 says `(f ∘ j)³(ω) = h (ω) · ω · h (ω)⁻¹`.  So `ζ⁻³ h (ω)` is an element of `D` centralising
`ω ∉ Q₀`; `DFpfBar` (Peterfalvi's "`D` acts without fixed points on `(Q/Q₀)^#`") forces it to
be trivial. -/
theorem hcan_eq_zeta_cube (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (hfpf : DFpfBar H Q t) {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0)
    (hf : (fcan hS.split ω : G) = (fr.ζ : G)⁻¹ * (ω : G)⁻¹ * (fr.ζ : G)) :
    (hcan hS.split ω : G) = (fr.ζ : G) ^ 3 := by
  have hω1 : (ω : G) ≠ 1 := fun hc => hω (by rw [hc]; exact Q0_one_mem fr)
  have hjjj := fcan_jjj_zeta_of fr hS.split hω1 hf
  have h5 := fcan_jjj (h := hS.split) hω1
  -- `h(ω) ω h(ω)⁻¹ = ζ³ ω ζ⁻³`
  have hkey : (hcan hS.split ω : G) * (ω : G) * ((hcan hS.split ω : G))⁻¹ =
      ((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G)) * (ω : G) *
        (((fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G)))⁻¹ :=
    h5.symm.trans hjjj
  -- the element `e = ζ⁻³ h(ω) ∈ D`
  set Z : G := (fr.ζ : G) * (fr.ζ : G) * (fr.ζ : G) with hZ
  have hZeq : Z = (fr.ζ : G) ^ 3 := by rw [hZ, pow_three, mul_assoc]
  have hkey' : (hcan hS.split ω : G) * (ω : G) * ((hcan hS.split ω : G))⁻¹ =
      Z * (ω : G) * Z⁻¹ := hkey
  set e : G := Z⁻¹ * (hcan hS.split ω : G) with he
  have heω : e * (ω : G) * e⁻¹ = (ω : G) := by
    rw [he]
    rw [show Z⁻¹ * (hcan hS.split ω : G) * (ω : G) *
          (Z⁻¹ * (hcan hS.split ω : G))⁻¹
        = Z⁻¹ * ((hcan hS.split ω : G) * (ω : G) * ((hcan hS.split ω : G))⁻¹) * Z
        from by group]
    rw [hkey']
    group
  have hee : e⁻¹ * (ω : G) * e = (ω : G) := by
    have h := congrArg (fun y : G => e⁻¹ * y * e) heω
    rw [show e⁻¹ * (e * (ω : G) * e⁻¹) * e = (ω : G) from by group] at h
    exact h.symm
  have hζ3D : (fr.ζ : G) ^ 3 ∈ twoPoint H t := by
    have h := (twoPoint H t).pow_mem (fr.KW_le fr.ζ.2) 3
    simpa using h
  have heD : e ∈ twoPoint H t := by
    rw [he, hZeq]
    exact (twoPoint H t).mul_mem ((twoPoint H t).inv_mem hζ3D) (hcan hS.split ω).2
  -- `DFpfBar` forces `e = 1`
  have he1 : e = 1 := by
    by_contra hne
    have hbad := hfpf e heD hne (ω : G) ω.2
      (fun hc => hω (by rw [frameQ0_eq_Q0sub hS fr]; exact hc))
    have h1 : e⁻¹ * (ω : G) * e * (ω : G)⁻¹ = 1 := by rw [hee, mul_inv_cancel]
    exact hbad (h1 ▸ (Q0sub H).one_mem)
  have hsimp : Z⁻¹ * (hcan hS.split ω : G) = 1 := by
    rw [← he]; exact he1
  calc (hcan hS.split ω : G)
      = Z * (Z⁻¹ * (hcan hS.split ω : G)) := by group
    _ = Z := by rw [hsimp, mul_one]
    _ = (fr.ζ : G) ^ 3 := hZeq

/-- **`h (ω) ∈ W`.**  Same hypotheses as `hcan_eq_zeta_cube`; the point is that the explicit
value `ζ³` lies in `W` because `ζ` does. -/
theorem hcan_mem_W_of_good (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (hfpf : DFpfBar H Q t) {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0)
    (hf : (fcan hS.split ω : G) = (fr.ζ : G)⁻¹ * (ω : G)⁻¹ * (fr.ζ : G)) :
    (hcan hS.split ω : G) ∈ W H t := by
  rw [hcan_eq_zeta_cube hS fr hfpf hω hf]
  exact (W H t).pow_mem fr.ζ_mem_W 3

/-! ## The reduction -/

/-- **Good elements are `OmegaHyp` elements.**  If `f (ω) = (ω · zc α)^ζ` and `ω² = zc α` for
`ω ∈ Q ∖ Q₀`, `α ∈ F*`, then `OmegaHyp fr ω` — with no further group theory, for any frame `fr`
in the hypotheses `PSU3Hyp H Q t` and `DFpfBar H Q t`. -/
theorem omegaHyp_of_good (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (hfpf : DFpfBar H Q t) {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(FX n)}
    (hf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    (hsq : ω * ω = zcQF fr α) :
    OmegaHyp fr (ω : G) :=
  omegaHyp_of_sq hS fr hω hf hsq
    (hcan_mem_W_of_good hS fr hfpf hω (fcan_eq_zeta_inv_of_sq hS fr hf hsq))

end Work.PSU3.StageB.Omega
