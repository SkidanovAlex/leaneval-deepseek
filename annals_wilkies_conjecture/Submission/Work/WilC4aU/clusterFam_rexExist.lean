import Mathlib
import Submission.Work.WilC4aU.Defs
import Submission.Work.WilC0.Compl
import Submission.Work.WilC4aU.ClusterDefs
import Submission.Work.WilC4aU.Dset_rexExist
import Submission.Work.WilC4aU.Eset_rexExist

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
noncomputable section
open Classical

namespace Work.WilC4aU

open WilkiesDesign Work.WilC0

/-- **C4aU.Syntax, step E.**  The parameters `(lam, c)` such that `(lam, c, eps) ∈ D` for every
`eps > 0`.  This is the leading universal quantifier `∀ ε > 0` of `RatioCluster`. -/
def Eset (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) : Set (BB0 k → ℝ) :=
  {z | ∀ e : ℝ, 0 < e → Sum.elim z (fun _ : Fin 1 => e) ∈ Dset k Y}

/-- Projecting the block `c` away from `E` gives exactly `ClusterFam Y`. -/
theorem clusterFam_eq {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) :
    {v : Fin 1 → ℝ | ∃ c : Fin k → ℝ, Sum.elim v c ∈ Eset k Y} = ClusterFam Y := by
  ext v
  have key : ∀ c : Fin k → ℝ,
      (Sum.elim v c ∈ Eset k Y) ↔ RatioCluster Y c (v 0) := by
    intro c
    simp only [Eset, Set.mem_ofPred_eq, RatioCluster]
    constructor
    · intro h e he
      simpa only [Dset, Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr] using h e he
    · intro h e he
      simpa only [Dset, Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr] using h e he
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, hc⟩
    rw [mem_clusterFam, mem_clusterSet]
    exact ⟨c, (key c).mp hc⟩
  · intro hv
    rw [mem_clusterFam, mem_clusterSet] at hv
    obtain ⟨c, hc⟩ := hv
    exact ⟨c, (key c).mpr hc⟩

/-- **C4aU.Syntax.**  The set of cluster values of the ratio `f (2 x) / f x` is existentially
definable in `ℝ_rexp`.

Recall (`Submission/Work/WilC4aU/Defs.lean`, namespace `Work.WilC4aU`):
`ClusterFam Y = {v : Fin 1 → ℝ | v 0 ∈ ClusterSet Y}`,
`ClusterSet Y = {lam | ∃ c : Fin k → ℝ, RatioCluster Y c lam}`,
`RatioCluster Y c lam = ∀ ε > 0, ∃ x y y', 1 ≤ ε * x ∧ Fin.cons x (Fin.cons y c) ∈ Y ∧ y ≠ 0 ∧
  Fin.cons (2 * x) (Fin.cons y' c) ∈ Y ∧ (y' - lam * y) ^ 2 < ε ^ 2 * y ^ 2`.

Intended proof, using the existential-definability calculus of `Submission.Work.WilC0.Basic`
(`RExpExistI`, `RExpExistI.pullback`, `.inter`, `.union`, `.rexPoly`, `.existsBlock`, `.of_eq`,
`rexExistI_existsFin`, `rexExistI_existsBlockFin`, `rexExistI_compl`, and the bridge
`rexExistI_iff_rexExist`) together with `hR` for the complements:

Work in the nested-Sum ambient index type
`V7 = (((((((Fin 1 ⊕ Fin k) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1) ⊕ Fin 1`
whose coordinates are, in order, `lam`, `c : Fin k`, `eps`, `x`, `u`, `y`, `y'`, `z`, `w`
(each block is appended on the right; `c` is the block `Fin k`).  Let `selY : Fin (k + 2) → V7`
pick the coordinates `x`, `y`, `c 0 … c (k-1)` (i.e. `selY 0 = x`, `selY 1 = y`,
`selY (i + 2) = c i`), and `selU : Fin (k + 2) → V7` the same with the coordinates `u`, `y'`,
`c 0 … c (k-1)` (i.e. `selU 0 = u`, `selU 1 = y'`, `selU (i + 2) = c i`).

The body is the intersection of these `RExpExistI` subsets of `Set (V7 → ℝ)`:
* the pullback of `Y` along `selY`, and the pullback of `Y` along `selU`
  (`RExpExistI.pullback`, after rewriting `hY` along `rexExistI_iff_rexExist`);
* `z ^ 2 = eps * x - 1`, `u = 2 * x`, `w ^ 2 = eps ^ 2 * y ^ 2 - (y' - lam * y) ^ 2`
  (`RExpExistI.rexPoly`, with the corresponding polynomial in `MvPolynomial (V7 ⊕ V7) ℝ`);
* `y ≠ 0` and `w ≠ 0`, both `hR`-complements of `rexPoly` hyperplanes.

Then project out, in the order `w`, `z`, `y'`, `y`, `u`, `x` (each is the last block), obtaining
`D ⊆ Set ((Fin 1 ⊕ Fin k) ⊕ Fin 1 → ℝ)` with coordinates `lam`, `c`, `eps`:
`D = {(lam,c,eps) | ∃ x y y', 1 ≤ eps * x ∧ (x,y,c) ∈ Y ∧ y ≠ 0 ∧ (2x,y',c) ∈ Y ∧
  (y' - lam * y)^2 < eps^2 * y^2}`.

Next, `G := {0 < eps} ∩ Dᶜ` (the complement via `rexExistI_compl` with `hR`; `0 < eps` is the
complement of `{v | ∃ t, t ^ 2 = -(v eps)}`); projecting out the `eps` coordinate and taking the
`hR`-complement of the result gives
`E = {(lam,c) | ∀ eps, 0 < eps → (lam,c,eps) ∈ D}`, which is the leading `∀ ε > 0`.

Finally project out the block `c` (the last `k` coordinates) with `existsBlock`, obtaining a set
of `Fin 1`-tuples, and identify it with `ClusterFam Y` (use that for `w : V7 → ℝ`,
`w ∘ selY = Fin.cons (w x) (Fin.cons (w y) (fun i => w (c i)))`). -/
theorem clusterFam_rexExist {k : ℕ} (Y : Set (Fin (k + 2) → ℝ))
    (hY : WilkiesDesign.RExpExist Y)
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ) :
    WilkiesDesign.RExpExist (Work.WilC4aU.ClusterFam Y) := by
  -- step D: the existential part (the projected body)
  have hD : RExpExistI (Dset k Y) := Dset_rexExist Y hY hR
  -- step E: the universal quantification over `eps > 0`
  have hE : RExpExistI (Eset k Y) := Eset_rexExist hR hD
  -- project the block `c` away
  have hF : RExpExistI {v : Fin 1 → ℝ | ∃ c : Fin k → ℝ, Sum.elim v c ∈ Eset k Y} :=
    hE.existsBlock
  rw [clusterFam_eq Y] at hF
  exact (rexExistI_iff_rexExist (ClusterFam Y)).mp hF

end Work.WilC4aU
