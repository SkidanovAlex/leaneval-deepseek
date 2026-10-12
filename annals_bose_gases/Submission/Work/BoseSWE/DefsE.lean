import ChallengeDeps
import Submission.Work.BoseB1Cube.nomArbAssembly
import Submission.Work.BoseSWE.nomBracketE
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseSWE.DefsE` — the vocabulary of the `E`-twin of the **arity passage**
# (piece B / F3b of the `BoseSWE` route)

The nominal arity passage (`Submission/Work/BoseB1Cube/nomArbAux.lean` +
`nomArbAssembly.lean`, PROVED) converts the in-box row at fixed constants into the row for
**every** `BoxState`, with fresh constants.  This module sets up the same passage with the
*vanshing slack* `ErrE v CE μ n = CE·(a v)·μ·n·d^80` carried on the left-hand side, i.e. for the
`E`-rows `Work.BoseSWE.PerBoxFNomE`.

Everything in the passage is "coefficient times `abox`-mass", so the slack — which is itself
`n`-linear and multiplies the same `abox`-mass — is absorbed into the *coefficient*:

* `nomCoeffE` — the `E`-coefficient `nomCoeff − ErrE(·)`;
* `nomRowE` — the `E`-demand `nomRow − ErrE(n)·‖Ψ‖² = nomCoeffE(n)·‖Ψ‖²`;
* `NomInBoxRowBodyE` / `NomSharpRowBodyE` — the in-box and sharp rows with the slack;
* `PerBoxFNomE_iff_nomRowE` — the in-box collapse of the `E`-row;
* `perBoxRow_eq_sum_slots`, `normB_eq_sum_slots` — the two slot identities of the passage
  (`nomDemand_split` read at `W = c₁·nomW`, `E = ½μ²nomW + nomESlot`, resp. at `W = 0`, `E = -1`);
* `nomCoeffE_zero_nonpos`, `ErrE_mono`-based slack aggregation.

The two sizable transcription lemmas live in sibling files of the F3b node and are **verbatim
copies** of the PROVED twins, with `nomRow ↦ nomRowE` / `nomCoeff ↦ nomCoeffE` /
`NomInBoxRowBody ↦ NomInBoxRowBodyE` / `NomSharpRowBody ↦ NomSharpRowBodyE` and nothing else
changed:

* `Work.BoseSWE.nomSharpRowE_body` — copy of `Work.BoseB1Cube.nomSharpRow_body`
  (`Submission/Work/BoseB1Cube/nomArbAux.lean` §5, ~120 lines).  The only places where the twin's
  proof touches the row are the degenerate case (`nomRow_eq_coeff` at a vanishing mass ⟹
  `nomRowE_eq_zero_of_normB_eq_zero`), `tendsto_nomRow_cutProd`
  (⟹ `tendsto_nomRowE_cutProd`), and the two homogeneity steps
  (`nomRow_const_mul` ⟹ `nomRowE_const_mul`); everything else (`cutProd`,
  `exists_isCutFamily_of_smoothCutoff`, `exists_smoothCutoffB`, `CutProdConvBody`,
  `sbWordCube_eq_zero_of_ae_eq_zero`, `sbWordCube_zero_particle`, `sbWordCube_smul`,
  `sharpState_ae_zero_of_normB_eq_zero`) transfers verbatim.
* `Work.BoseSWE.nomCoeffE_slot_le_word` — copy of `Work.BoseB1Cube.nomCoeff_slot_le_word`
  (`Submission/Work/BoseB1Cube/nomArbAux.lean` §6, ~55 lines): the pointwise sharp row is read
  through `nomRowE_eq_coeffE` instead of `nomRow_eq_coeff`, and `nomCoeff` is replaced by
  `nomCoeffE`.  The two factorisations (`normB_slotFibre`, `sbWordCube_slotFibre`) and the
  integration (`integral_mono_ae`, `integral_const_mul`) are unchanged.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseSWE

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical

/-! ## 1. The `E`-coefficient and the `E`-demand -/

/-- `normB` is the `abox`-`L²`-mass, definitionally — the shape in which the arity passage reads
it. -/
theorem normB_eq_integral (v : E3 → ℝ) (μ : ℝ) (n : ℕ) (Ψ : X n → ℝ) :
    Work.BoseBoxFix.normB v μ n Ψ
      = ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Ψ x) ^ 2 := rfl

/-- **The `E`-coefficient of the arity passage.**  The nominal coefficient of the demand at the
occupant count `k`, minus the slack `ErrE v CE μ k`.  The whole passage is "coefficient times
`abox`-mass", so this is the only change needed over `Work.BoseB1Cube.nomCoeff`. -/
noncomputable def nomCoeffE (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C CE μ : ℝ) (u : E3)
    (k : ℕ) : ℝ :=
  Work.BoseB1Cube.nomCoeff v h R c₁ C μ u k - ErrE v CE μ k

/-- **The `E`-demand of the arity passage** (at the single chemical-potential slot `μp = μ`,
which is all the passage needs): the nominal demand minus the slack times the state's `abox`-mass.
This is exactly the left-hand side of `PerBoxFNomE` at `μp = μ`. -/
noncomputable def nomRowE (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C CE μ : ℝ) (n : ℕ)
    (u : E3) (Ψ : X n → ℝ) : ℝ :=
  Work.BoseB1Cube.nomRow v h R c₁ C μ μ n u Ψ
    - ErrE v CE μ n * Work.BoseBoxFix.normB v μ n Ψ

/-- The `E`-demand in factored form: the `E`-coefficient times the `abox`-mass. -/
theorem nomRowE_eq_coeffE (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C CE μ : ℝ) (n : ℕ)
    (u : E3) (Ψ : X n → ℝ) :
    nomRowE v h R c₁ C CE μ n u Ψ
      = nomCoeffE v h R c₁ C CE μ u n * Work.BoseBoxFix.normB v μ n Ψ := by
  rw [nomRowE, nomCoeffE, Work.BoseB1Cube.nomRow_eq_coeff, normB_eq_integral]
  ring

/-- The `E`-demand is `2`-homogeneous in the state. -/
theorem nomRowE_const_mul {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C CE μ : ℝ} {n : ℕ}
    {u : E3} (Ψ : X n → ℝ) (t : ℝ) :
    nomRowE v h R c₁ C CE μ n u (fun x => t * Ψ x)
      = t ^ 2 * nomRowE v h R c₁ C CE μ n u Ψ := by
  rw [nomRowE_eq_coeffE, nomRowE_eq_coeffE, normB_eq_integral, normB_eq_integral,
    Work.BoseFixB1S.normB_smul']
  ring

/-- The `E`-demand vanishes on an a.e.-zero state of vanishing mass. -/
theorem nomRowE_eq_zero_of_normB_eq_zero {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C CE μ : ℝ}
    {n : ℕ} {u : E3} {Ψ : X n → ℝ}
    (hm0 : Work.BoseBoxFix.normB v μ n Ψ = 0) :
    nomRowE v h R c₁ C CE μ n u Ψ = 0 := by
  rw [nomRowE_eq_coeffE, hm0, mul_zero]

/-- **The `E`-demand converges along the smooth-cutoff approximants of a sharp state** — the twin
of `Work.BoseB1Cube.tendsto_nomRow_cutProd` (the demand is a coefficient times the `abox`-mass). -/
theorem tendsto_nomRowE_cutProd {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C CE μ : ℝ} {n : ℕ}
    {u : E3} {ψ : X n → ℝ} {K : ℝ} {γ : ℝ → E3 → ℝ}
    (hℓ : 0 < Work.BoseFixB1B.PBℓ v μ) (hd : 0 < Work.BoseFixB1B.PBd v μ)
    (hcut : Work.BoseFixB1B.IsCutFamily (Work.BoseFixB1B.PBℓ v μ) (Work.BoseFixB1B.PBd v μ) u K γ)
    (hψ : Continuous ψ) :
    Tendsto (fun δ : ℝ => nomRowE v h R c₁ C CE μ n u (Work.BoseFixB1B.cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (nomRowE v h R c₁ C CE μ n u
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox (Work.BoseFixB1B.PBℓ v μ)
          (Work.BoseFixB1B.PBd v μ) u) ψ))) := by
  have hmass := Work.BoseFixB1B.tendsto_cutProd_mass (k := n) (L := Work.BoseFixB1B.PBℓ v μ)
    (d := Work.BoseFixB1B.PBd v μ) (u := u) (ψ := ψ) (K := K) (γ := γ) hℓ hd hcut hψ
  have h2 := hmass.const_mul (nomCoeffE v h R c₁ C CE μ u n)
  simpa only [nomRowE_eq_coeffE, normB_eq_integral] using h2

/-! ## 2. The two rows of the `E`-passage -/

/-- **The `E`-in-box row at fixed constants**: `nomRowE ≤ sbWordCube` for every a.e.-in-box
`BoxState` on the good set (the `E`-twin of `NomInBoxRowBody`). -/
def NomInBoxRowBodyE (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C CE ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
      (u : E3),
      u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
      (∀ᵐ x ∂((volume : Measure (X n)).restrict
          (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        (Φ : X n → ℝ) x ≠ 0 →
          ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      nomRowE v h R c₁ C CE μ n u (Φ : X n → ℝ)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ)

/-- **The `E`-in-box row at the sharp states** — the `E`-twin of `NomSharpRowBody`. -/
def NomSharpRowBodyE (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (R c₁ C CE ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ (k : ℕ) (ψ : X k → ℝ), ContDiff ℝ (⊤ : ENat) ψ →
      Submission.BoseGases.PermInvariant k ψ →
      ∀ u : E3, u ∈ Work.SmallBoxSliding.goodSet (Work.BoseFixB1B.PBℓ v μ)
            (Work.BoseFixB1B.PBd v μ) μ →
        nomRowE v h R c₁ C CE μ k u
          (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u) ψ)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u
          (Work.BoseFixB1B.sharpBoxState (Work.BoseFixB1B.PBB v μ u) ψ)

/-! ## 3. The in-box collapse of the `E`-row -/

/-- **At an a.e.-in-box `BoxState` the `E`-row is the state-level `E`-row**
`nomRowE ≤ sbWordCube`.  Direct from the PROVED twins `PerBoxFNomE_iff_row` and
`perBoxRow_eq_nomRow`. -/
theorem PerBoxFNomE_iff_nomRowE {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C CE μ : ℝ} {n : ℕ}
    {u : E3} {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    (hloc : ∀ᵐ x ∂((volume : Measure (X n)).restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
      (Φ : X n → ℝ) x ≠ 0 → ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :
    PerBoxFNomE v h R c₁ C CE μ μ n Φ u
      ↔ nomRowE v h R c₁ C CE μ n u (Φ : X n → ℝ)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u (Φ : X n → ℝ) := by
  rw [PerBoxFNomE_iff_row,
    Work.BoseB1Cube.perBoxRow_eq_nomRow (μp := μ) (Φ := Φ) hloc]
  rfl

/-! ## 4. The two slot identities of the passage -/

/-- **The `abox`-mass splits over the occupant sectors** (the partition identity, read off
`nomDemand_split` at `W = 0`, `E = -1`). -/
theorem normB_eq_sum_slots {v : E3 → ℝ} {μ : ℝ} {n : ℕ} {u : E3}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :
    Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
      = ∑ S : Finset (Fin n),
          ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) S (Φ : X n → ℝ) x) ^ 2 := by
  have hsplit := Work.BoseB1Cube.nomDemand_split (N := n)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μ) (W := 0) (E := -1)
    hℓ u (Φ := (Φ : X n → ℝ)) (hΦ := Φ.contDiff.continuous)
  simpa only [normB_eq_integral, zero_mul, zero_sub, neg_mul, one_mul, neg_neg] using hsplit

/-- **The nominal box demand splits over the occupant sectors, with the coefficients of the
passage.**  For *every* continuous state (no in-box hypothesis) the frozen left-hand side
`perBoxRow` is the finite sum of `nomCoeff (|S|)` against the slot masses, where `nomCoeff` is read
at the *total* count `n` only through the sector cardinalities. -/
theorem perBoxRow_eq_sum_slots {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C μ : ℝ} {n : ℕ}
    {u : E3} {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :
    Work.BoseB1Cube.perBoxRow v h R c₁ C μ μ n Φ u
      = ∑ S : Finset (Fin n),
          Work.BoseB1Cube.nomCoeff v h R c₁ C μ u S.card
            * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) S (Φ : X n → ℝ) x) ^ 2) := by
  have hsplit := Work.BoseB1Cube.nomDemand_split (N := n)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μ)
    (W := c₁ * Work.BoseB1Cube.nomW v h μ u)
    (E := (1 / 2) * μ ^ 2 * Work.BoseB1Cube.nomW v h μ u
      + Work.BoseB1Cube.nomESlot v R C μ μ u)
    hℓ u (Φ := (Φ : X n → ℝ)) (hΦ := Φ.contDiff.continuous)
  have hL : Work.BoseB1Cube.perBoxRow v h R c₁ C μ μ n Φ u
      = (c₁ * Work.BoseB1Cube.nomW v h μ u)
          * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Φ : X n → ℝ) x ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
                (Work.BoseB1Cube.boxIndCount (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x
                  / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u))
        - ((1 / 2) * μ ^ 2 * Work.BoseB1Cube.nomW v h μ u
            + Work.BoseB1Cube.nomESlot v R C μ μ u)
          * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Φ : X n → ℝ) x ^ 2) := by
    rw [Work.BoseB1Cube.perBoxRow, Work.BoseB1Cube.nomW, Work.BoseB1Cube.nomESlot,
      Work.BoseB1Cube.nomChi, Work.BoseB1Cube.nomGamma, normB_eq_integral]
    ring
  rw [hL, hsplit]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Work.BoseB1Cube.nomCoeff, Work.BoseB1Cube.nomW, Work.BoseB1Cube.nomV,
    Work.BoseB1Cube.nomESlot, Work.BoseB1Cube.nomChi, Work.BoseB1Cube.nomGamma]
  ring

/-- The `E`-coefficient at the count `0` is nonpositive for `c₁ ≤ 1/2` (the `F`-weight saturates
at `μ²` and the slack vanishes at `k = 0`). -/
theorem nomCoeffE_zero_nonpos {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R c₁ C CE μ : ℝ} {u : E3}
    (hW : 0 ≤ Work.BoseB1Cube.nomW v h μ u)
    (hE : 0 ≤ Work.BoseB1Cube.nomESlot v R C μ μ u) (hc₁ : c₁ ≤ 1 / 2) :
    nomCoeffE v h R c₁ C CE μ u 0 ≤ 0 := by
  have h0 := Work.BoseB1Cube.nomCoeff_zero_nonpos (v := v) (h := h) (R := R) (c₁ := c₁) (C := C)
    (μ := μ) (u := u) hW hE hc₁
  rw [nomCoeffE]
  have hz : ErrE v CE μ 0 = 0 := by simp [ErrE]
  rw [hz, sub_zero]
  exact h0

end Work.BoseSWE
