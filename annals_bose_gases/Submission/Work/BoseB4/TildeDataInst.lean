import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB4.BoxOperators
import Submission.Work.BoseB4.bessel_le_totNumOp_v2
import Submission.Work.BoseB4.exists_gram_jointKernel
import Submission.Work.BoseB4.thetaExp_lattice_pair
import Submission.Work.BoseB4.totNumOp_comp_annOf
import Submission.Work.BoseB4.totNumOp_comp_creOf
import Submission.Work.BoseB4.totNumOp_nonneg
import Submission.Work.BoseB4.totNumOp_symm
import Submission.Work.BoseB7A.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.TildeDataInst` — node `B7A`'s `TildeData` on the box mode system (K1)

This is B4's obligation **K1** of `BOSE_3Q_LEAD.md` §3: the θ-mode data
`Work.BoseB7A.TildeData` on the real bosonic Fock space over the mode lattice.

The construction is parametric in the *joint* one-particle coordinates:

* `f : Mode → Fin m → ℝ` — the χ-modes `a_k` (with `gram (f i)(f j)` the box
  kernel, i.e. `hf`: `Work.BoseB4.boxFockData`);
* `g : Mode → Fin m → ℝ` — the θ-modes `ã_s`, orthonormal on the excited modes
  (`hg`), cross Gram product `gram (g s)(f k)`.

Then `tildeData` takes

* `ta s = annOf (g s)`, `taDag s = creOf (g s)` — the θ-mode operators, with
  `ccrX s k = gram (g s) (f k)` (on the box: `χ̂(ℓ(k−s))`, see
  `Work.BoseB4.realIP_thetaExp_qVec` and `Work.BoseB4.exists_gram_jointKernel`);
* `N = Σ_l a_l†a_l = totNumOp m` — FS's `n₊`, with the *exact* number grading
  (`totNumOp_comp_annOf`/`totNumOp_comp_creOf`), self-adjointness and positivity;
* `NH = totNumOp m` as well (any nonnegative combination of the mode number
  operators is admissible for `n₊^H`; the field only asks for positivity);
* `ta_le_N` from the Bessel inequality `bessel_le_totNumOp_v2`
  (module `Submission.Work.BoseB4.bessel_le_totNumOp_v2`).

Given `Work.BoseB4.exists_gram_jointKernel` (which produces `f`, `g` from the box
data and the two lattice-orthogonality hypotheses), this makes `TildeData`
inhabited on the honest model; the remaining input is the Fourier orthogonality
of the box exponentials at lattice momenta.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The Bessel inequality in the form `ta_le_N` needs: for an orthonormal family
`g` of θ-modes, `⟨(Σ_{s∈S} ã_s†ã_s)Φ, Φ⟩ ≤ ⟨n₊Φ, Φ⟩` with `n₊ = Σ_l a_l†a_l`. -/
theorem bessel_le_totNumOp_sum_comp {Mode : Type*} [DecidableEq Mode] {m : ℕ}
    (g : Mode → Fin m → ℝ) (S : Finset Mode)
    (hg : ∀ s ∈ S, ∀ t ∈ S, gram (g s) (g t) = if s = t then 1 else 0)
    (Φ : RealFock m) :
    bomb m ((∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ) Φ
      ≤ bomb m (totNumOp m Φ) Φ := by
  have hsplit : (∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ
      = ∑ s ∈ S, creOf m (g s) (annOf m (g s) Φ) := by
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  calc bomb m ((∑ s ∈ S, (creOf m (g s)).comp (annOf m (g s))) Φ) Φ
      = ∑ s ∈ S, bomb m (creOf m (g s) (annOf m (g s) Φ)) Φ := by
        rw [hsplit]
        simp only [map_sum, LinearMap.sum_apply]
    _ = ∑ s ∈ S, bomb m (annOf m (g s) Φ) (annOf m (g s) Φ) :=
        Finset.sum_congr rfl fun s _ => CreOf_annOf_adjoint (g s) _ Φ
    _ ≤ bomb m (totNumOp m Φ) Φ := bessel_le_totNumOp_v2 g S hg Φ

/-- **K1: `TildeData` on the box mode system.**  The θ-modes `ã_s` (coordinates
`g`), FS's `n₊` (`N = Σ_l a_l†a_l`, exact grading) and `n₊^H` (`NH`), with the
cross commutator `ccrX s k = gram (g s) (f k)`. -/
noncomputable def tildeData (B : BoxData) {ℓ : ℝ} {Mode : Type*} [AddCommGroup Mode]
    [Fintype Mode] [DecidableEq Mode] (kmom : Mode → ℝ³)
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (m : ℕ) (f g : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode,
      gram (f i) (f j) = BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (hg : ∀ s t : Mode, s ≠ 0 → t ≠ 0 → gram (g s) (g t) = if s = t then 1 else 0) :
    Work.BoseB7A.TildeData (boxFockData B kmom hkmom m f hf) where
  ta := fun s => annOf m (g s)
  taDag := fun s => creOf m (g s)
  taDag_adjoint := fun s x y => CreOf_annOf_adjoint (g s) x y
  ta_comm := fun s t => AnnOf_ann_comm (g s) (g t)
  taDag_comm := fun s t => CreOf_cre_comm (g s) (g t)
  ta_ccr := fun s t hs ht => by
    have h := AnnOf_creOf_ccr (g s) (g t)
    rw [hg s t hs ht] at h
    exact h
  ta_a_comm := fun s k => AnnOf_ann_comm (g s) (f k)
  ccrX := fun s k => gram (g s) (f k)
  ta_aDag := fun s k => AnnOf_creOf_ccr (g s) (f k)
  N := totNumOp m
  NH := totNumOp m
  N_symm := fun x y => totNumOp_symm m x y
  N_nonneg := fun x => totNumOp_nonneg m x
  NH_nonneg := fun x => totNumOp_nonneg m x
  N_a := fun k => totNumOp_comp_annOf m (f k)
  N_aDag := fun k => totNumOp_comp_creOf m (f k)
  N_ta := fun s => totNumOp_comp_annOf m (g s)
  N_taDag := fun s => totNumOp_comp_creOf m (g s)
  ta_le_N := fun S hS Φ =>
    bessel_le_totNumOp_sum_comp g S (fun s hs t ht => hg s t (hS s hs) (hS t ht)) Φ

/-- **K1, packaged.**  Given the box data, the side `ℓ > 0` and an additive
momentum assignment whose θ-modes are orthogonal to each other and to the
condensate (the Fourier orthogonality of the box at lattice momenta,
`∫_{Λ(ℓ)}e^{isx}dx = 0` for `s ∈ (2π/ℓ)ℤ³ ∖ {0}`), node `B7A`'s `TildeData` is
**inhabited** on the box mode system: there are coordinates `f` (χ-modes) and `g`
(θ-modes) such that `boxFockData … f` carries a `TildeData` with `ta = ã`,
`N = n₊ = Σ_l a_l†a_l` and `ccrX s k = ⟨ã_s, a_k†⟩`. -/
theorem exists_tildeData (B : BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (kmom : Mode → ℝ³) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (had : ∀ i j : Mode, kmom (i - j) = kmom i - kmom j)
    (horth : ∀ s t : Mode, s ≠ 0 → t ≠ 0 →
      B.realIP (B.thetaExp ℓ (kmom s)) (B.thetaExp ℓ (kmom t))
        = if s = t then ℓ ^ 3 else 0)
    (horthC : ∀ s : Mode, s ≠ 0 →
      B.realIP (B.thetaExp ℓ (kmom s)) (B.thetaFun ℓ) = 0) :
    ∃ (m : ℕ) (f g : Mode → Fin m → ℝ)
      (hf : ∀ i j : Mode,
        gram (f i) (f j) = BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j)),
      Nonempty (Work.BoseB7A.TildeData (boxFockData B kmom hkmom m f hf)) := by
  obtain ⟨m, f, g, hf, hg, _⟩ := exists_gram_jointKernel B hℓ kmom had horth horthC
  exact ⟨m, f, g, hf, ⟨tildeData B kmom hkmom m f g hf hg⟩⟩


/-- **K1 for FS's concrete box.**  For a `BoxData` on the unit cube, the side
`ℓ > 0`, and an *injective* momentum assignment whose values are dual-lattice
momentum vectors `ℓ⁻¹ • 2π n`, node `B7A`'s `TildeData` exists on the box mode
system.  The θ-mode orthogonality hypotheses of `exists_tildeData` are discharged
by `realIP_thetaExp_thetaExp_of_cell`, so this is the hypothesis-free form of K1
on the honest model. -/
theorem exists_tildeData_lattice (B : BoxData) (hcell : B.cell = unitCell) {ℓ : ℝ}
    (hℓ : 0 < ℓ) {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (kmom : Mode → ℝ³) (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (hinj : Function.Injective kmom)
    (had : ∀ i j : Mode, kmom (i - j) = kmom i - kmom j)
    (hlat : ∀ s : Mode, ∃ n : Fin 3 → ℤ, kmom s = ℓ⁻¹ • vec n) :
    ∃ (m : ℕ) (f g : Mode → Fin m → ℝ)
      (hf : ∀ i j : Mode,
        gram (f i) (f j) = BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j)),
      Nonempty (Work.BoseB7A.TildeData (boxFockData B kmom hkmom m f hf)) := by
  have hcancel : ∀ {v w : ℝ³}, (ℓ⁻¹ : ℝ) • v = ℓ⁻¹ • w → v = w := by
    intro v w h
    have := congrArg (fun u : ℝ³ => ℓ • u) h
    simpa [smul_smul, mul_inv_cancel₀ (ne_of_gt hℓ)] using this
  have hvec0 : vec (0 : Fin 3 → ℤ) = 0 := by
    ext i
    simp [vec]
  have h0 : kmom (0 : Mode) = 0 := by
    have h := had 0 0
    rw [sub_zero, sub_self] at h
    exact h
  refine exists_tildeData B hℓ kmom hkmom had (fun s t hs ht => ?_) (fun s hs => ?_)
  · obtain ⟨n, hn⟩ := hlat s
    obtain ⟨p, hp⟩ := hlat t
    have hiff : n = p ↔ s = t := by
      constructor
      · intro hnp
        refine hinj ?_
        rw [hn, hp, hnp]
      · intro hst
        refine vec_injective (hcancel ?_)
        rw [← hn, ← hp, hst]
    rw [hn, hp, realIP_thetaExp_thetaExp_of_cell B hcell hℓ n p]
    exact if_congr hiff rfl rfl
  · obtain ⟨n, hn⟩ := hlat s
    rw [hn, realIP_thetaExp_thetaFun_of_cell B hcell hℓ n, if_neg ?_]
    intro hn0
    exact hs (hinj (by rw [hn, hn0, hvec0, smul_zero, h0]))

end Work.BoseB4
