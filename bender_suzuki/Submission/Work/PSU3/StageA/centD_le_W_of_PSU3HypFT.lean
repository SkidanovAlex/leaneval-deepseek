/-
# `Work.PSU3.StageA.centD_le_W_of_PSU3HypFT` — `V = C_D(t) ≤ W = C_V(J(D,t))`

Requested statement (verbatim, at the bottom of this file):

  `PSU3Hyp H Q t → ChIIFourProp → FeitThompsonProp → centD H t ≤ W H t`.

With `D = twoPoint H t`, `V = centD H t = C_D(t)`, `K = J(D,t) = Kset H t`, `W = C_V(K)`
(`Work.ThmF.W`), the conclusion is `V ≤ W`, i.e. `V = W` (`W ≤ V` is definitional).  Over
`PSU3Hyp + ChIIFourProp` this is equivalent to the area's main theorem (`PSU3Prop`, resp. the
black box `RankOneVNeqWProp`); the added `FeitThompsonProp` supplies Ch. V §1 Prop. 2
(`Work.ThmF.ChV12.Ksub_cyclic_normal`: `K = J(D,t)` is cyclic and normal in `D`).

## The argument formalised here

`centD_le_W_of_PSU3HypFT_of_pieces` below is *the* assembly, with the three inputs still open in
the tree made explicit:

* `hWne : W H t ≠ ⊥` — Ch. VI §1, case c) (the `W = ⊥` branch is killed by simplicity; the
  status of the two branches is recorded in `caseWbot_abelian_or_card_sq.lean` and
  `W_ne_bot_of_PSU3HypFT.lean`);
* `hfpf` — the fixed-point-free branch of the `ω`-existence (Peterfalvi II Ch. VII §2;
  `Submission/Work/PSU3/StageB/exists_omega_of_fpf.lean` and `Omega/VERDICT_B1.md`);
* `hnfpf` — the `V ≠ W` branch of the `ω`-existence (Peterfalvi II Ch. VII §4, pp. 278–280;
  `Submission/Work/PSU3/StageB/exists_omega_of_not_fpf.lean`).

Given those, the argument is:

1. `W_ne_bot_of_PSU3HypFT`-style input gives `W ≠ ⊥`; with `distinguished_exists` and
   `caseC_data_of_W_ne_bot` this yields the case-c data `|Q| = |Q0sub H|³`, `orderOf (s*t) = 3`
   (whence the structure identity `t s t = s t s`);
2. `coarseFrame_exists` (A6) turns `ζ ∈ W#` and the case-c data into a `CoarseFrame H Q t n`;
3. splitting `DFpfBar H Q t`, `hfpf`/`hnfpf` produce a (possibly rebuilt) frame `fr₁` and `ω`
   with `OmegaHyp fr₁ ω`;
4. Stage B3/C0 (`theta_trivial`, `frame_normalize`) normalise the frame so that `nm` is the
   squaring map and `ω² = zc(ζ + ζ⁻¹)`, and Stage C1/C2 (`fine_coords_holds`, `f_formula`)
   produce `e : Q ≃* SZ (E n)` turning Peterfalvi's `FRel` into `fMapTot`;
5. `Work.RankOneUniqueness.recognize` (with `rankOneQUniqueness`, and the model datum
   `Work.PSU3.psu3DatumProp_holds`) then gives `G ≃* PSU3Model n`, so `G` is a simple Bender
   group and `centD_le_W_of_isSimpleBenderGroup` gives `V ≤ W` — the contradiction with `V ≰ W`.

Everything in steps 2, 4 and 5 is hole-free and axiom-clean in this workspace (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`); so are `W H t ≠ ⊥` (step 1) and the
non-fixed-point-free branch of the `ω`-existence (`Work.PSU3.StageB.exists_omega_of_not_fpf_FT`).

## Status of the inputs (2026-10-07)

* `W H t ≠ ⊥` — **proved**: `Work.PSU3.StageA.W_ne_bot_of_PSU3HypFT` (axiom-clean).  The `W = ⊥`
  branch is handled by the Ch. VI §1 case analysis, with `hFT` supplying `K = J(D,t) ⊴ D` via
  `Work.ThmF.ChV12.Ksub_cyclic_normal` and the new siblings `caseWbot_abelian_eq_Q0sub`,
  `not_caseA_of_FT`, `caseB_false`.
* the `V ≠ W` branch (`¬ DFpfBar`) of the `ω`-existence — **proved**: Peterfalvi II Ch. VII §4
  (pp. 278–280), `Work.PSU3.StageB.exists_omega_of_not_fpf_FT` (axiom-clean).
* the **fixed-point-free branch** (`DFpfBar ⟹ Ω`) — **open, and equivalent to the target**: by the
  axiom-clean `Work.PSU3.StageB.exists_omegaHyp_iff_V_le_W` (and
  `Work.PSU3.StageB.centD_le_W_of_omegaHyp` for the other direction), under
  `PSU3Hyp + ChIIFourProp + HigmanProp + CoarseFrame + DFpfBar` one has

      (∃ fr' ω, OmegaHyp fr' ω)  ↔  centD H t ≤ W H t,

  which is exactly the remaining content of the requested statement.  The node as stated for a
  bare `CoarseFrame` was declared *mis-stated* by the delegated prover
  (`Submission/Work/PSU3/StageB/exists_omega_of_fpf_FT.lean`, path freed; see also
  `Omega/VERDICT_B1.md` and `Omega/fpf_b1.lean`), and the alternative bridge
  `V ≰ W → ¬ DFpfBar H Q t` (`Work.PSU3.StageA.not_DFpfBar_of_centD_not_le_W`) was declared
  mis-stated likewise — it is the same content by the equivalence above.

The requested statement is therefore not derivable from its listed hypotheses with this library:
the hypothesis list omits the structural input — `RankOneVNeqWProp`, equivalently
`IsSimpleBenderGroup G` / `PSU3Prop` — that every route in the tree consumes, `FeitThompsonProp`
supplying only Ch. V §1 Prop. 2 among the prerequisites.  With any of those added the statement is
one line: `centD_le_W_of_RankOneVNeqW` / `centD_le_W_of_isSimpleBenderGroup` /
`centD_le_W_for_simple_of_PSU3Prop`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.Higman.Main
import Submission.Work.PSU3.StageA.W_ne_bot_of_PSU3HypFT
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.PSU3.StageA.coarseFrame_exists
import Submission.Work.PSU3.StageA.centD_le_W_of_isSimpleBenderGroup
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.PSU3.StageB.theta_trivial
import Submission.Work.PSU3.StageC.frame_normalize
import Submission.Work.PSU3.StageC.fine_coords_holds
import Submission.Work.PSU3.StageC.f_formula
import Submission.Work.PSU3.Model.psu3DatumProp
import Submission.Work.PSU3.StageB.exists_omega_of_not_fpf_FT
import Submission.Work.RankOneUniqueness.recognize

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- A nontrivial subgroup has a nontrivial element. -/
private lemma exists_ne_one_of_ne_bot' {G : Type} [Group G] {W : Subgroup G} (h : W ≠ ⊥) :
    ∃ ζ ∈ W, ζ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact h (eq_bot_iff.mpr (fun x hx => Subgroup.mem_bot.mpr (hcon x hx)))

/-- `s² = t² = 1` together with `(s * t)³ = 1` gives `t * s * t = s * t * s`. -/
private lemma sts_of_cube' {G : Type} [Group G] {s t : G} (hs : s * s = 1) (ht : t * t = 1)
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

/-- **The assembly of `centD_le_W_of_PSU3HypFT` from the fixed-point-free `ω`-existence.**

The non-fixed-point-free branch is *proved*: `Work.PSU3.StageB.exists_omega_of_not_fpf_FT`
(Peterfalvi II Ch. VII §4, the `V ≠ W` case; axiom-clean).  Also `W H t ≠ ⊥`
(`Work.PSU3.StageA.W_ne_bot_of_PSU3HypFT`), the case-c data (`caseC_data_of_W_ne_bot`), the
coarse frame (`coarseFrame_exists`), Stage B3/C0 and Stage C1/C2 (`theta_trivial`,
`frame_normalize`, `fine_coords_holds`, `f_formula`), the recognition theorem
(`rankOneQUniqueness`, `recognize`) and the model fact (`centD_le_W_of_isSimpleBenderGroup`) are
all hole-free and axiom-clean.

The only remaining input is `hfpf` — the fixed-point-free branch of the `ω`-existence
(Ch. VII §2, `Work.PSU3.StageB.exists_omega_of_fpf`).  By the axiom-clean equivalence
`Work.PSU3.StageB.exists_omegaHyp_iff_V_le_W`, that branch is *equivalent* (given
`DFpfBar H Q t`) to the present target `V ≤ W`.
-/
theorem centD_le_W_of_PSU3HypFT_of_pieces {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hfpf : ∀ {n : ℕ}, Work.PSU3.CoarseFrame H Q t n → Work.PSU3.DFpfBar H Q t →
      ∃ fr' : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G, Work.PSU3.OmegaHyp fr' ω) :
    Submission.Blueprint.centD H t ≤ Work.ThmF.W H t := by
  classical
  haveI : IsSimpleGroup G := hS.simple
  have hHig : Submission.Blueprint.HigmanProp := Work.Higman.higmanProp
  have hWne : Work.ThmF.W H t ≠ ⊥ := Work.PSU3.StageA.W_ne_bot_of_PSU3HypFT hS hC4 hFT
  by_contra hcon
  -- ## Step 1: the case-c data of Ch. VI §1 (`|Q| = |Q₀|³`, `ord(st) = 3`)
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  obtain ⟨hcard, h3, _hWne'⟩ :=
    Work.PSU3.StageA.caseC_data_of_W_ne_bot hS hC4 hHig hs hs2 hr hsr hWne
  -- ## Step 2: a nontrivial element of `W`, and the structure identity `t s t = s t s`
  obtain ⟨ζ, hζW, hζ1⟩ := exists_ne_one_of_ne_bot' hWne
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hS.split.invol] at h
    simpa [pow_two] using h
  have hs2' : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hcube : (s * t) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (s * t)
    rwa [h3] at h
  have hst : t * s * t = s * t * s := sts_of_cube' hs2' ht2 hcube
  -- ## Step 3: the coarse frame (A6)
  obtain ⟨n, hn, _hQ0sub, fr, _hzcs, _hζfr⟩ :=
    Work.PSU3.StageA.coarseFrame_exists hS hC4 hHig hs hs2 hr hsr hst hcard hζW hζ1
  -- ## Step 4: an `ω` with `OmegaHyp` for some frame at the same index (Ch. VII §2 / §4)
  obtain ⟨fr₁, ω, hω⟩ : ∃ fr₁ : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G,
      Work.PSU3.OmegaHyp fr₁ ω := by
    by_cases hf : Work.PSU3.DFpfBar H Q t
    · exact hfpf fr hf
    · exact Work.PSU3.StageB.exists_omega_of_not_fpf_FT hS hC4 hHig fr hf
  -- ## Step 5: Stage B3 / C0 — the Frobenius power, then the normalised frame
  obtain ⟨i, hi, hω2⟩ := Work.PSU3.StageB.theta_trivial hS fr₁ hω
  obtain ⟨fr₂, _hQ0, hω', hsq, hω2'⟩ := Work.PSU3.StageC.frame_normalize fr₁ hω i hi hω2
  -- ## Step 6: Stage C1 — fine coordinates `e : Q ≃* SZ (E n)`
  obtain ⟨e, μ, hex, hes, heq⟩ := Work.PSU3.StageC.fine_coords_holds fr₂ hsq
  -- ## Step 7: Stage C2 — `FRel` becomes `fMapTot`
  have hf : ∀ x y : Q, (x : G) ≠ 1 →
      Work.RankOneUniqueness.FRel H t (x : G) (y : G) → e y = Work.PSU3.fMapTot (e x) :=
    Work.PSU3.StageC.f_formula hS fr₂ hω' hsq hω2' e μ hex hes heq
  -- ## Step 8: recognition (`rankOneQUniqueness`, `recognize`) gives `G ≃* PSU3Model n`
  obtain ⟨M⟩ := Work.PSU3.psu3DatumProp_holds n hn
  obtain ⟨eisom⟩ := Work.RankOneUniqueness.recognize Work.RankOneUniqueness.rankOneQUniqueness
    hS.split (Y := ↥(PSU3Model n)) (C := SZ (Work.PSU3.E n)) (fC := Work.PSU3.fMapTot) M e hf
  -- ## Step 9: `G` is a simple Bender group, so the model gives `V ≤ W`: contradiction
  exact hcon (centD_le_W_of_isSimpleBenderGroup (.isPSU3 n hn eisom) hS)

/-- **The assembly, via the bridge instead of Ch. VII §2.**

If `V ≰ W` implies `¬ DFpfBar H Q t` (`hbridge`, see
`Work.PSU3.StageA.not_DFpfBar_of_centD_not_le_W`), then in the contradiction branch the
fixed-point-free case is impossible and only the `V ≠ W` branch (`hnfpf`) of the `ω`-existence is
needed — no appeal to Ch. VII §2. -/
theorem centD_le_W_of_PSU3HypFT_of_bridge {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hbridge : ∀ {n : ℕ}, Work.PSU3.CoarseFrame H Q t n →
      ¬ Submission.Blueprint.centD H t ≤ Work.ThmF.W H t → ¬ Work.PSU3.DFpfBar H Q t)
    (hnfpf : ∀ {n : ℕ}, Work.PSU3.CoarseFrame H Q t n → ¬ Work.PSU3.DFpfBar H Q t →
      ∃ fr' : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G, Work.PSU3.OmegaHyp fr' ω) :
    Submission.Blueprint.centD H t ≤ Work.ThmF.W H t := by
  classical
  haveI : IsSimpleGroup G := hS.simple
  have hHig : Submission.Blueprint.HigmanProp := Work.Higman.higmanProp
  have hWne : Work.ThmF.W H t ≠ ⊥ := Work.PSU3.StageA.W_ne_bot_of_PSU3HypFT hS hC4 hFT
  by_contra hcon
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  obtain ⟨hcard, h3, _hWne'⟩ :=
    Work.PSU3.StageA.caseC_data_of_W_ne_bot hS hC4 hHig hs hs2 hr hsr hWne
  obtain ⟨ζ, hζW, hζ1⟩ := exists_ne_one_of_ne_bot' hWne
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hS.split.invol] at h
    simpa [pow_two] using h
  have hs2' : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hcube : (s * t) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (s * t)
    rwa [h3] at h
  have hst : t * s * t = s * t * s := sts_of_cube' hs2' ht2 hcube
  obtain ⟨n, hn, _hQ0sub, fr, _hzcs, _hζfr⟩ :=
    Work.PSU3.StageA.coarseFrame_exists hS hC4 hHig hs hs2 hr hsr hst hcard hζW hζ1
  obtain ⟨fr₁, ω, hω⟩ : ∃ fr₁ : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G,
      Work.PSU3.OmegaHyp fr₁ ω :=
    hnfpf fr (hbridge fr hcon)
  obtain ⟨i, hi, hω2⟩ := Work.PSU3.StageB.theta_trivial hS fr₁ hω
  obtain ⟨fr₂, _hQ0, hω', hsq, hω2'⟩ := Work.PSU3.StageC.frame_normalize fr₁ hω i hi hω2
  obtain ⟨e, μ, hex, hes, heq⟩ := Work.PSU3.StageC.fine_coords_holds fr₂ hsq
  have hf : ∀ x y : Q, (x : G) ≠ 1 →
      Work.RankOneUniqueness.FRel H t (x : G) (y : G) → e y = Work.PSU3.fMapTot (e x) :=
    Work.PSU3.StageC.f_formula hS fr₂ hω' hsq hω2' e μ hex hes heq
  obtain ⟨M⟩ := Work.PSU3.psu3DatumProp_holds n hn
  obtain ⟨eisom⟩ := Work.RankOneUniqueness.recognize Work.RankOneUniqueness.rankOneQUniqueness
    hS.split (Y := ↥(PSU3Model n)) (C := SZ (Work.PSU3.E n)) (fC := Work.PSU3.fMapTot) M e hf
  exact hcon (centD_le_W_of_isSimpleBenderGroup (.isPSU3 n hn eisom) hS)

-- Superseded (2026): the hole-carrying `centD_le_W_of_PSU3HypFT` was removed by the hole
-- sweep; its proved replacement is `Work.PSU3.StageA.centD_le_W_of_PSU3Hyp_closed`.

end Work.PSU3.StageA
