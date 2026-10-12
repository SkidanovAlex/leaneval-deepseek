import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseGateFS.KinkFSHonest
import Submission.Work.BoseK15.Constants
import Submission.Work.BoseK15.chi_small_of_decay
import Submission.Work.BoseK15.ell_mul_KL_sqrt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.HonRowsDecay` — the χ-decay rows at the honest model

The first two τ-free χ-rows of `HonestRows` (`hatChi_small`, `ccrX_small`, FS
`lem:DecaychiHat` on `P_H^q`), **derived at the honest model** instead of being
read off `Work.BoseK15.K15Input` — that bundle has no honest instance (finding
F1/F7, `FINDING_K15R_input_vacuous.md`), so its row lemmas are unusable.

The ingredients are bundle-free: the decay predicate `Work.BoseK15.ChiReg` of the
corpus χ (whose existence is `Work.BoseK15.ChiReg_corpus`), the η-arithmetic
`Work.BoseK15.arith_KH_a_div_ell_pow_le_eta`, the absorption core
`Work.BoseK15.decay_absorb`, the χ-pins (`honE_hatChi`) and the F7 support
`honE_fL_supp2`.  The pattern (threshold `(cX)⁻¹`, constant `Cchi·c^{2s}`) is the
one of `Work.BoseK15.chi_small_of_decay`, and the constants are the ones of
`Work.BoseK15.exists_constants`.

* `honE_hatChi_abs_le` — the decay bound `|χ̂(p)| ≤ C·((1+‖p‖²)^s)⁻¹` at a mode;
* `honE_ccrX_eq` — the cross commutator is the corpus χ̂ at the momentum
  difference (`HonestModes.hcross`);
* `honE_hatChi_small`, `honE_ccrX_small` — the two rows;
* `honE_onDualLattice`, `honE_ellKL` — the two geometric rows the later χ-sums
  consume.
-/

noncomputable section

open scoped BigOperators Pointwise Real

namespace Work.BoseGateFS

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
variable {HM : ∀ μ : ℝ, HonestModes v μ} {μ : ℝ}

section Decay

/-- The χ-decay at the honest modes, in the reciprocal form used by
`Work.BoseK15.decay_absorb`: `|χ̂(p)| ≤ C·((1+‖p‖²)^s)⁻¹`. -/
theorem honE_hatChi_abs_le {Cchi : ℝ} (hCchi : 0 ≤ Cchi)
    (hchi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox Work.BoseK15.decayOrder Cchi)
    (p : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseK15.corpusBox.hatChi p|
      ≤ Cchi * (((1 : ℝ) + ‖p‖ ^ 2) ^ Work.BoseK15.decayOrder)⁻¹ := by
  have h1 := hchi.1 p
  have hpos : 0 < ((1 : ℝ) + ‖p‖ ^ 2) ^ Work.BoseK15.decayOrder := by positivity
  rw [le_mul_inv_iff₀ hpos]
  exact h1

/-- The cross commutator at the honest model is the corpus χ̂ at the momentum
difference (`HonestModes.hcross`). -/
theorem honE_ccrX_eq (s q : Lab (HM μ).N) :
    (honT v h fc fu HM μ).ccrX s q
      = Work.BoseK15.corpusBox.hatChi
          (Work.BoseBoxFock.ellH v μ • ((honF v h fc fu HM μ).kmom q
            - (honF v h fc fu HM μ).kmom s)) := by
  simpa only [honT, honF, Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.tildeDataHon,
    Work.BoseB4.boxFockData, Work.BoseB4.b7FockDataBox] using (HM μ).hcross s q

/-- **`hatChi_small` at the honest model** (FS K2 on `P_H^q`). -/
theorem honE_hatChi_small (S : HonSetup v h fc fu HM μ) {Cchi K₀ : ℝ} (hCchi : 0 ≤ Cchi)
    (hchi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox Work.BoseK15.decayOrder Cchi)
    (hK : Cchi * 8 ^ (2 * Work.BoseK15.decayOrder) ≤ K₀) :
    ∀ q : Lab (HM μ).N,
      (honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat q →
      |(honE v h fc fu HM μ).hatChi q| ≤ K₀ * eta (honE v h fc fu HM μ) := by
  intro q hq
  have hell : 0 < (honE v h fc fu HM μ).ell := by
    rw [honE_ell S]; exact Work.BoseBoxFock.ellH_pos v μ
  have hX : 0 < (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH
      / (honE v h fc fu HM μ).ell := by
    refine div_pos (mul_pos S.hv.a_pos ?_) hell
    exact lt_of_lt_of_le one_pos S.hv.one_le_KH
  -- the momentum is above the `P_H^q` threshold
  have hnorm : 1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
      ≤ ‖(honF v h fc fu HM μ).kmom q‖ := by
    have h' := hq
    rw [Work.BoseB7.FockData.PHq, honF_kmom] at h'
    exact h'
  have hy : 1 / (4 * ((honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH
      / (honE v h fc fu HM μ).ell)) ≤ ‖(honE v h fc fu HM μ).ell
        • (honF v h fc fu HM μ).kmom q‖ := by
    rw [norm_smul, Real.norm_of_nonneg hell.le]
    have he : 1 / (4 * ((honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH
        / (honE v h fc fu HM μ).ell))
        = (honE v h fc fu HM μ).ell
          * (1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)) := by
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hnorm hell.le
  have hK4 : Cchi * 4 ^ (2 * Work.BoseK15.decayOrder) ≤ K₀ := by
    have h4 : (4 : ℝ) ^ (2 * Work.BoseK15.decayOrder)
        ≤ 8 ^ (2 * Work.BoseK15.decayOrder) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    exact le_trans (mul_le_mul_of_nonneg_left h4 hCchi) hK
  have hcore := Work.BoseK15.decay_absorb (C := Cchi) (K₀ := K₀)
    (X := (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH
      / (honE v h fc fu HM μ).ell)
    (η := eta (honE v h fc fu HM μ))
    (y := ‖(honE v h fc fu HM μ).ell • (honF v h fc fu HM μ).kmom q‖) (c := 4)
    (by norm_num) hCchi hK4 hX
    (Work.BoseK15.arith_KH_a_div_ell_pow_le_eta (honE v h fc fu HM μ) S.hv) hy
  have hpin : (honE v h fc fu HM μ).hatChi q
      = Work.BoseK15.corpusBox.hatChi
          ((honE v h fc fu HM μ).ell • (honF v h fc fu HM μ).kmom q) :=
    honE_hatChi S.hav S.hμ (honF v h fc fu HM μ) (HM μ).N q
  rw [hpin]
  exact le_trans (honE_hatChi_abs_le hCchi hchi _) hcore

/-- **`ccrX_small` at the honest model** (FS K2 on `P_H^q`, off the `f_L`
support).  The F7 support `‖kmom s‖ ≤ 2K_L√(μa)` and the diluteness row
`K_L√(μa)·K_Ha ≤ 1/16` place `kmom q - kmom s` above `(8K_Ha)⁻¹`. -/
theorem honE_ccrX_small (S : HonSetup v h fc fu HM μ) {Cchi K₀ : ℝ} (hCchi : 0 ≤ Cchi)
    (hchi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox Work.BoseK15.decayOrder Cchi)
    (hK : Cchi * 8 ^ (2 * Work.BoseK15.decayOrder) ≤ K₀)
    (hS1 : (honE v h fc fu HM μ).KL * Real.sqrt ((honE v h fc fu HM μ).mu
        * (honE v h fc fu HM μ).aScat) * ((honE v h fc fu HM μ).KH
          * (honE v h fc fu HM μ).aScat) ≤ 1 / 16) :
    ∀ s q : Lab (HM μ).N, (honE v h fc fu HM μ).fL s ≠ 0 →
      (honF v h fc fu HM μ).PHq (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat q →
      |(honT v h fc fu HM μ).ccrX s q| ≤ K₀ * eta (honE v h fc fu HM μ) := by
  intro s q hs hq
  have hell : 0 < (honE v h fc fu HM μ).ell := by
    rw [honE_ell S]; exact Work.BoseBoxFock.ellH_pos v μ
  have hKH : 0 < (honE v h fc fu HM μ).KH := lt_of_lt_of_le one_pos S.hv.one_le_KH
  have ha : 0 < (honE v h fc fu HM μ).aScat := S.hv.a_pos
  have hX : 0 < (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH
      / (honE v h fc fu HM μ).ell := by
    exact div_pos (mul_pos ha hKH) hell
  have hnorm : 1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
      ≤ ‖(honF v h fc fu HM μ).kmom q‖ := by
    have h' := hq
    rw [Work.BoseB7.FockData.PHq, honF_kmom] at h'
    exact h'
  have hsle : ‖(honF v h fc fu HM μ).kmom s‖
      ≤ 2 * ((honE v h fc fu HM μ).KL
          * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)) :=
    honE_fL_supp2 S s hs
  have hKHa : 0 < (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat := mul_pos hKH ha
  have hsle8 : ‖(honF v h fc fu HM μ).kmom s‖
      ≤ 1 / (8 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) := by
    have h16 : 0 < 8 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat := by positivity
    have h2 : 2 * ((honE v h fc fu HM μ).KL * Real.sqrt ((honE v h fc fu HM μ).mu
        * (honE v h fc fu HM μ).aScat)) ≤ 1 / (8 * (honE v h fc fu HM μ).KH
          * (honE v h fc fu HM μ).aScat) := by
      rw [le_div_iff₀ h16]
      nlinarith [hS1]
    exact le_trans hsle h2
  have hdiff : 1 / (8 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
      ≤ ‖(honF v h fc fu HM μ).kmom q - (honF v h fc fu HM μ).kmom s‖ := by
    have h4 : |‖(honF v h fc fu HM μ).kmom q‖ - ‖(honF v h fc fu HM μ).kmom s‖|
        ≤ ‖(honF v h fc fu HM μ).kmom q - (honF v h fc fu HM μ).kmom s‖ :=
      abs_norm_sub_norm_le _ _
    have hA : 1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
        - 1 / (8 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
        ≤ ‖(honF v h fc fu HM μ).kmom q‖ - ‖(honF v h fc fu HM μ).kmom s‖ := by
      linarith
    have hB : 1 / (8 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
        ≤ 1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
          - 1 / (8 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) := by
      have h : 1 / (4 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
          - 1 / (8 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
          = 1 / (8 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) := by
        first | (field_simp; ring) | field_simp
      rw [h]
    have h3 : 1 / (8 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)
        ≤ ‖(honF v h fc fu HM μ).kmom q‖ - ‖(honF v h fc fu HM μ).kmom s‖ :=
      le_trans hB hA
    linarith [h3, le_abs_self (‖(honF v h fc fu HM μ).kmom q‖
      - ‖(honF v h fc fu HM μ).kmom s‖), h4]
  have hy : 1 / (8 * ((honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH
      / (honE v h fc fu HM μ).ell))
      ≤ ‖(honE v h fc fu HM μ).ell • ((honF v h fc fu HM μ).kmom q
        - (honF v h fc fu HM μ).kmom s)‖ := by
    rw [norm_smul, Real.norm_of_nonneg hell.le]
    have he : 1 / (8 * ((honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH
        / (honE v h fc fu HM μ).ell))
        = (honE v h fc fu HM μ).ell
          * (1 / (8 * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat)) := by
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hdiff hell.le
  have hcore := Work.BoseK15.decay_absorb (C := Cchi) (K₀ := K₀)
    (X := (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH
      / (honE v h fc fu HM μ).ell)
    (η := eta (honE v h fc fu HM μ))
    (y := ‖(honE v h fc fu HM μ).ell • ((honF v h fc fu HM μ).kmom q
      - (honF v h fc fu HM μ).kmom s)‖) (c := 8)
    (by norm_num) hCchi hK hX
    (Work.BoseK15.arith_KH_a_div_ell_pow_le_eta (honE v h fc fu HM μ) S.hv) hy
  have hpin : (honT v h fc fu HM μ).ccrX s q
      = Work.BoseK15.corpusBox.hatChi
          ((honE v h fc fu HM μ).ell • ((honF v h fc fu HM μ).kmom q
            - (honF v h fc fu HM μ).kmom s)) := by
    rw [honE_ccrX_eq s q, honE_ell S]
  rw [hpin]
  exact le_trans (honE_hatChi_abs_le hCchi hchi _) hcore

/-- **The inner ball**: `f_L = 1` for `‖kmom s‖ ≤ K_L√(μa)` (`LowCut.one`).  This is
the honest form of the F7-repaired support pair (`fL_supp2` is the outer ball). -/
theorem honE_fL_eq_one (S : HonSetup v h fc fu HM μ) {s : Lab (HM μ).N}
    (hs : ‖(honF v h fc fu HM μ).kmom s‖
      ≤ (honE v h fc fu HM μ).KL * Real.sqrt ((honE v h fc fu HM μ).mu
        * (honE v h fc fu HM μ).aScat)) :
    (honE v h fc fu HM μ).fL s = 1 := by
  have hκ : 0 < (honE v h fc fu HM μ).KL * Real.sqrt ((honE v h fc fu HM μ).mu
      * (honE v h fc fu HM μ).aScat) := kappa_pos S
  rw [show (honE v h fc fu HM μ).fL s
      = fc.f (‖(honF v h fc fu HM μ).kmom s‖
          / ((honE v h fc fu HM μ).KL
              * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)))
      from rfl]
  exact fc.one _ ((div_le_one hκ).mpr hs)

end Decay

/-! ## 2. The geometric rows the χ-sums consume -/

/-- **The honest cube is a dual lattice**: `ℓ • kmomLab ℓ N n = 2π · labVec N n`. -/
theorem honE_onDualLattice (S : HonSetup v h fc fu HM μ) :
    Work.BoseK15.OnDualLattice (Work.BoseBoxFock.ellH v μ)
      (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N) := by
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have h1 := (Work.BoseB7AK.LatBox.kmom_rows (n := 2 * (HM μ).N + 1)
    (Nat.odd_iff.mpr (by omega)) hℓ).2.2.1
  -- transport the `LatBox` dual-lattice structure along `kmomLab_eq_latBox`
  exact h1

/-- The `ℓ K_L√(μa) = K_ℓK_L` identity at the honest environment. -/
theorem honE_ellKL (S : HonSetup v h fc fu HM μ) :
    (honE v h fc fu HM μ).ell * (honE v h fc fu HM μ).KL
        * Real.sqrt ((honE v h fc fu HM μ).mu * (honE v h fc fu HM μ).aScat)
      = (honE v h fc fu HM μ).Kl * (honE v h fc fu HM μ).KL :=
  Work.BoseK15.ell_mul_KL_sqrt (honE v h fc fu HM μ) S.hv

end Work.BoseGateFS
