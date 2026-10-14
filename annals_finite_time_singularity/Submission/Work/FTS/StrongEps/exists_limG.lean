import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Assembly.step2_data
import Submission.Work.FTS.CoercivityFix.Transfer.L4Step
import Submission.Work.FTS.IPGen.IP4Lin
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.DelicateHon
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.SliceIntQ
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.L4Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ CoerAdm)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The two elementary `α`-bounds -/

/-- If `α·(A+1) ≤ min B 1`, then `A·α² ≤ B`. -/
private lemma key1 {A B α : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (h : α * (A + 1) ≤ min B 1) : A * α ^ 2 ≤ B := by
  have h3 : 0 ≤ α * (A + 1) := mul_nonneg hα (by linarith)
  have h4 : (α * (A + 1)) ^ 2 ≤ min B 1 := by
    nlinarith [h, h3, min_le_right B 1]
  have h5 : A * α ^ 2 ≤ (α * (A + 1)) ^ 2 := by nlinarith [hA, hα]
  linarith [h4, h5, min_le_left B 1]

/-- If `α·(A+1) ≤ B`, then `A·α ≤ B`. -/
private lemma key2 {A B α : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (h : α * (A + 1) ≤ B) : A * α ≤ B := by
  have : A * α ≤ α * (A + 1) := by nlinarith [hA, hα]
  linarith




end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot IsDynEqOn IsDynGSolWith)

set_option autoImplicit false

/-! ## The interval covering -/

/-- The length of the `n`-th interval: `Tn n = n + 1`. -/
def Tn (n : ℕ) : ℝ := (n : ℝ) + 1

theorem Tn_pos (n : ℕ) : 0 < Tn n := by
  simp only [Tn]; exact lt_of_lt_of_le zero_lt_one (by norm_num)

/-- The index of the piece covering `τ`: `⌊τ⌋₊ + 1`, so that `τ < Tn (pidx τ)`. -/
def pidx (τ : ℝ) : ℕ := Nat.floor τ + 1


theorem pidx_cast (τ : ℝ) : ((pidx τ : ℕ) : ℝ) = ((Nat.floor τ : ℕ) : ℝ) + 1 := by
  simp only [pidx, Nat.cast_add, Nat.cast_one]

theorem lt_Tn_pidx (τ : ℝ) : τ < Tn (pidx τ) := by
  have h := Nat.lt_floor_add_one τ
  simp only [Tn, pidx_cast]
  linarith

theorem le_Tn_pidx (τ : ℝ) : τ ≤ Tn (pidx τ) := le_of_lt (lt_Tn_pidx τ)

/-- `Icc 0 b` is a neighbourhood of `x` within `Ici 0` as soon as `x < b`. -/
theorem Icc_zero_mem_nhdsWithin_Ici {b x : ℝ} (hxb : x < b) :
    Set.Icc (0 : ℝ) b ∈ 𝓝[Set.Ici (0 : ℝ)] x := by
  have h1 : Set.Ici (0 : ℝ) ∩ Set.Iio b ∈ 𝓝[Set.Ici (0 : ℝ)] x :=
    Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxb))
  refine Filter.mem_of_superset h1 ?_
  rintro y ⟨hy0, hyb⟩
  exact ⟨hy0, le_of_lt hyb⟩

/-! ## The glued family and its agreement with the pieces -/

/-- The glued family: at `τ ≥ 0` it is the piece `pidx τ`, and at `τ < 0` the first piece. -/
def glued (g : ℕ → Fam) : Fam := fun z θ τ =>
  if 0 ≤ τ then g (pidx τ) z θ τ else g 0 z θ τ

@[simp] theorem glued_of_nonneg {g : ℕ → Fam} {τ : ℝ} (hτ : 0 ≤ τ) (z θ : ℝ) :
    glued g z θ τ = g (pidx τ) z θ τ := if_pos hτ



/-! ## Two congruence facts for the glued family -/

theorem glued_slice {g : ℕ → Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    slice (glued g) τ = slice (g (pidx τ)) τ := by
  funext z θ
  exact glued_of_nonneg hτ z θ


/-! ## E6 — `global_strong2` -/




/-! ## E6 from consistent pieces / from `ExistsLimG` (curric-46 lead install 2026-10-11)

C1–C5 ruling (`cbc/fts_strongeps_c1c5_ruling.md` §5, review fix F1 applied: `c1` is on
`Ioo 0 T`, so the `c1` clause is read inside the piece's horizon and widened by
`mono_of_mem_nhdsWithin`).  `global_strong2_of_limG` is the E6 used by
`GlobalStrong2Prime.global_strong2'_proved`; `global_strong2`/`global_strong2_g2` above stay on the
old `exists_limH` (off the `theorem_1_v2` cone). -/

/-- **E6 from consistent pieces** (generalises `Assembly.global_strong2_of_lim`: the uniqueness
clause of `ExistsLimH` was used ONLY to make the pieces agree on overlaps).  PROVED (the proof of
`global_strong2_of_lim` with `piece_eq_at` replaced by `hcons`). -/
theorem global_strong2_of_pieces {α C₀ K : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g₀ : Fn}
    {Cd : ℕ → ℝ} {g : ℕ → Fam}
    (hpk : ∀ n, EpsLimPkg α C₀ K (Cd n) (Tn n) Φs E g₀ (g n))
    (hcons : ∀ (m n : ℕ) (z θ τ : ℝ), 0 ≤ τ → τ ≤ Tn m → τ ≤ Tn n →
      g m z θ τ = g n z θ τ) :
    ∃ g : Fam, IsDynGSolWith (Work.FTS.StrongGlobal.IsBslSolPos α) α
        (Work.FTS.Nonlin.PsiCan Φs E g) g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧
      Work.FTS.StrongGlobal.RegPkgMin α g ∧
      (∀ τ, 0 ≤ τ → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2) ∧
      LimApproxSE α C₀ Φs E g := by
  have hG : ∀ {τ : ℝ}, 0 ≤ τ → ∀ z θ, ∀ τ' ∈ Set.Icc 0 (Tn (pidx τ)),
      glued g z θ τ' = g (pidx τ) z θ τ' := by
    intro τ _ z θ τ' hτ'
    rw [glued_of_nonneg hτ'.1 z θ]
    exact hcons _ _ z θ τ' hτ'.1 (le_Tn_pidx τ') hτ'.2
  refine ⟨glued g, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro τ hτ
      have hs : slice (g (pidx τ)) τ = slice (glued g) τ := (glued_slice hτ).symm
      exact ((hpk (pidx τ)).law τ hτ (le_Tn_pidx τ)).congr
        (Work.FTS.StrongGlobal.Ftau_congr hs) (Work.FTS.StrongGlobal.slice_PsiCan_congr hs)
    · intro z θ τ hτ hz
      have hmem : Set.Icc (0 : ℝ) (Tn (pidx τ)) ∈ 𝓝[Set.Ici (0 : ℝ)] τ :=
        Icc_zero_mem_nhdsWithin_Ici (lt_Tn_pidx τ)
      have hfun : (fun s => glued g z θ s) =ᶠ[𝓝[Set.Ici (0 : ℝ)] τ]
          (fun s => g (pidx τ) z θ s) := by
        filter_upwards [hmem] with τ' hτ'
        exact hG hτ z θ τ' hτ'
      have hval : glued g z θ τ = g (pidx τ) z θ τ := hG hτ z θ τ ⟨hτ, le_Tn_pidx τ⟩
      have hgoal := (((hpk (pidx τ)).eqT τ hτ (le_Tn_pidx τ) z θ hz).mono_of_mem_nhdsWithin
        hmem).congr_of_eventuallyEq hfun hval
      show HasDerivWithinAt (fun s => glued g z θ s) (rhsFun α Φs E (glued g) τ z θ)
        (Set.Ici (0 : ℝ)) τ
      rw [rhsFun_congr (glued_slice hτ)]
      exact hgoal
  · intro z θ
    rw [glued_of_nonneg le_rfl]
    exact (hpk (pidx 0)).init z θ
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      have hτpos : 0 < p.2.2 := hp.2.2
      have hp' : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 (Tn (pidx p.2.2)) :=
        ⟨hp.1, hp.2.1, hτpos, lt_Tn_pidx p.2.2⟩
      have hnbh : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 (Tn (pidx p.2.2)))
          ∈ 𝓝 p :=
        (isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_Ioo)).mem_nhds hp'
      have hev : (fun q : ℝ × ℝ × ℝ => glued g q.1 q.2.1 q.2.2)
          =ᶠ[𝓝 p] (fun q : ℝ × ℝ × ℝ => g (pidx p.2.2) q.1 q.2.1 q.2.2) := by
        filter_upwards [hnbh] with q hq
        exact hG (τ := p.2.2) (le_of_lt hτpos) q.1 q.2.1 q.2.2
          ⟨le_of_lt hq.2.2.1, le_of_lt hq.2.2.2⟩
      have hval : glued g p.1 p.2.1 p.2.2 = g (pidx p.2.2) p.1 p.2.1 p.2.2 :=
        hG (le_of_lt hτpos) p.1 p.2.1 p.2.2 ⟨le_of_lt hτpos, le_Tn_pidx p.2.2⟩
      have hmemT : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioo 0 (Tn (pidx p.2.2)))
          ∈ 𝓝[Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0] p :=
        nhdsWithin_le_nhds hnbh
      exact (((hpk (pidx p.2.2)).c1.contDiffWithinAt hp').congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hval).mono_of_mem_nhdsWithin hmemT
    · intro τ hτ
      rw [glued_slice hτ]
      exact (hpk (pidx τ)).c4 τ hτ (le_Tn_pidx τ)
    · intro z θ hz τ hτ
      have hmem : Set.Icc (0 : ℝ) (Tn (pidx τ)) ∈ 𝓝[Set.Ici (0 : ℝ)] τ :=
        Icc_zero_mem_nhdsWithin_Ici (lt_Tn_pidx τ)
      have hfun : (fun s => glued g z θ s) =ᶠ[𝓝[Set.Ici (0 : ℝ)] τ]
          (fun s => g (pidx τ) z θ s) := by
        filter_upwards [hmem] with τ' hτ'
        exact hG hτ z θ τ' hτ'
      have hval : glued g z θ τ = g (pidx τ) z θ τ := hG hτ z θ τ ⟨hτ, le_Tn_pidx τ⟩
      exact (((hpk (pidx τ)).cont z θ hz τ ⟨hτ, le_Tn_pidx τ⟩).mono_of_mem_nhdsWithin
        hmem).congr_of_eventuallyEq hfun hval
    · intro τ hτ
      rw [glued_slice hτ]
      exact (hpk (pidx τ)).mem4 τ hτ (le_Tn_pidx τ)
    · refine Work.FTS.StrongGlobal.DbdLoc.of_local (fun S hS => ?_)
      refine ⟨g (pidx S), Cd (pidx S), fun z θ τ hτ => ?_, fun τ hτpos hτS => ?_⟩
      · rw [glued_of_nonneg hτ.1.le z θ]
        exact hcons _ _ z θ τ hτ.1.le (le_Tn_pidx τ)
          (le_of_lt (lt_trans hτ.2 (lt_Tn_pidx S)))
      · exact (hpk (pidx S)).dbd τ hτpos (lt_trans hτS (lt_Tn_pidx S))
    · intro τ hτ z hz
      have hs : glued g z 0 τ = g (pidx τ) z 0 τ :=
        congrFun (congrFun (glued_slice (g := g) hτ) z) 0
      have hs2 : glued g z (π / 2) τ = g (pidx τ) z (π / 2) τ :=
        congrFun (congrFun (glued_slice (g := g) hτ) z) (π / 2)
      have h1 := (hpk (pidx τ)).vanish τ hτ (le_Tn_pidx τ) z hz
      exact ⟨hs.trans h1.1, hs2.trans h1.2⟩
  · intro τ hτ
    rw [glued_slice hτ]
    exact (hpk (pidx τ)).bd4 τ hτ (le_Tn_pidx τ)
  · intro T hT
    obtain ⟨N, hN⟩ : ∃ N : ℕ, T ≤ Tn N :=
      ⟨Nat.ceil T, by
        have h := Nat.le_ceil T
        simp only [Tn]
        push_cast
        linarith⟩
    obtain ⟨gn, B, L, hb, hlip, hjet, hmu⟩ := (hpk N).limApprox T hT hN
    have hs : ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) T → ∀ z' θ', glued g z' θ' τ = g N z' θ' τ := by
      intro τ hτ z' θ'
      rw [glued_of_nonneg hτ.1 z' θ']
      exact hcons _ _ z' θ' τ hτ.1 (le_Tn_pidx τ) (le_trans hτ.2 hN)
    have hsSlice : ∀ {τ : ℝ}, τ ∈ Set.Icc (0 : ℝ) T → slice (glued g) τ = slice (g N) τ := by
      intro τ hτ
      funext z' θ'
      simp only [slice]
      exact hs hτ z' θ'
    refine ⟨gn, B, L, hb, hlip, ?_, ?_⟩
    · intro τ hτ j i hji z θ hzθ
      rw [hsSlice hτ]
      exact hjet τ hτ j i hji z θ hzθ
    · intro τ hτ
      have hPsi : slice (Work.FTS.Nonlin.PsiCan Φs E (glued g)) τ
          = slice (Work.FTS.Nonlin.PsiCan Φs E (g N)) τ := by
        funext z' θ'
        simp only [Work.FTS.Nonlin.PsiCan, slice]
        rw [hsSlice hτ]
      have hF : Work.Construction.Ftau α (glued g) τ = Work.Construction.Ftau α (g N) τ := by
        funext z' θ'
        simp only [Work.Construction.Ftau]
        rw [hs hτ z' θ']
      have hmuEq : Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (glued g))
            (glued g) τ
          = Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (g N)) (g N) τ := by
        simp only [Work.FTS.Galerkin.muDyn]
        rw [hF, hsSlice hτ, hPsi]
      rw [hmuEq]
      exact hmu τ hτ

/-- **E6 from the uniqueness-free E5 conclusion.**  PROVED: constant pieces are consistent. -/
theorem global_strong2_of_limG {α C₀ K : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g₀ : Fn}
    (hlim : ExistsLimG α C₀ K Φs E g₀) :
    ∃ g : Fam, IsDynGSolWith (Work.FTS.StrongGlobal.IsBslSolPos α) α
        (Work.FTS.Nonlin.PsiCan Φs E g) g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧
      Work.FTS.StrongGlobal.RegPkgMin α g ∧
      (∀ τ, 0 ≤ τ → Work.FTS.Nonlin.Xn α (slice g τ) ≤ C₀ * α ^ 2) ∧
      LimApproxSE α C₀ Φs E g := by
  obtain ⟨g, hg⟩ := hlim
  choose Cd _hCd hpk using fun n : ℕ => hg (Tn n) (Tn_pos n)
  exact global_strong2_of_pieces (g := fun _ => g) hpk (fun _ _ _ _ _ _ _ _ => rfl)


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row4u =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- Uniform-in-`Cs`, `Ce` restatement of `Work.FTS.StrongEps.E4R3.N4C.HonRows.n0row4`.
-- The two binders `Cs`, `Ce` are moved from the theorem's argument list into the inner
-- `forall`, so that the constant `K` does not depend on them (the target `rowsN0T`
-- quantifies `{Cs Ce}` *after* the `exists K`).  The proof script is unchanged.

namespace Work.FTS.StrongEps.E4R3.N4C.HonRowsU

open Work.FTS.Galerkin (Fn)
open Work.Spaces (HkMem HkSq HkNorm Dz Dth)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem n0row4u (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Cs Ce α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
      Work.Spaces.HkMem α 5 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.DecayAll 4 g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α g) ∧
        |IP α (Work.FTS.Nonlin.N04bF α g) g|
          ≤ K * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
  obtain ⟨hCt, _⟩ := hE.pos
  obtain ⟨KL, hKLpos, hKLb⟩ := Work.FTS.StrongEps.E4R3.N4C.L12_dzdIter_abs_le_open
  refine ⟨Ct * 25 * (3 / 2) * KL + 1, by positivity, ?_⟩
  intro Cs Ce α g Φs Φg hα hα1 hαα₂ hsm hmem4 hmem5 hL120 hdec hs hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  -- the radial coefficient `(3/(2α)) L₁₂(g)`
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  have hL12 := hN.l12H α hIoc g ⟨hsm, hmem4⟩ hL120
  have hfMem : Work.Spaces.HkMem α 4
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12.1
  have hfx0 : (0 : ℝ) ≤ 3 / (2 * α) := by positivity
  have hX0 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hM0 : (0 : ℝ) ≤ (3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g) :=
    mul_nonneg hfx0 (mul_nonneg hKLpos.le hX0)
  have hfXn : Work.FTS.Nonlin.Xn α
        (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ (3 / (2 * α)) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_of_nonneg hfx0]
    exact mul_le_mul_of_nonneg_left hL12.2 hfx0
  -- the pointwise (`D`-sup) bound on the coefficient
  have hpt : ∀ b j : ℕ, b + j ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b j (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ|
        ≤ (3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g) := by
    intro b j hbj z θ hz hθ0 hθ1
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have hmixed : Work.Spaces.mixed b 0
            (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ
          = (3 / (2 * α)) * Work.Elliptic.DzdIter b (fun z => Work.Construction.L12 g z) z := by
        rw [Work.Spaces.mixed_zero_right,
          Work.FTS.Nonlinear.Pieces.RowsN0Aux.DzIter_const_mul]
        simp only [Work.Elliptic.DzIter_rad]
      rw [hmixed, abs_mul, abs_of_nonneg hfx0]
      exact mul_le_mul_of_nonneg_left
        (hKLb hα hα1 hsm hmem4 hL120 b hbj z hz) hfx0
    · have hzero : Work.Spaces.mixed b j
          (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ = 0 := by
        have hd : Work.Spaces.DthIter j
            (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) = 0 := by
          rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.DthIter_const_mul,
            Work.FTS.NonlinRows.dthIter_rad_eq_zero (fun z => Work.Construction.L12 g z) j hj]
          funext z θ
          simp only [Pi.zero_apply]
          ring
        simp only [Work.Spaces.mixed, hd]
        rw [Work.FTS.NonlinRows.dzIter_zero b]
        simp only [Pi.zero_apply]
      rw [hzero, abs_zero]
      exact hM0
  have hWDmem : Work.FTS.VocabO.WDMem 4
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) :=
    fun b j hbj => ⟨(3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g),
      fun z θ hz hθ0 hθ1 => hpt b j hbj z θ hz hθ0 hθ1⟩
  have hWDp : Work.FTS.VocabO.WDp 4
        (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
      ≤ 25 * ((3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g)) :=
    Work.FTS.OpenPkg.WDp_le_of_pointwise (α := α) hM0 hpt
  -- the `ℋ⁴`-honesty of the piece, by the product rule with `D_θ g`
  have hDthMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth g) :=
    Work.FTS.IPGen.HkMem_Dth_le (k := 4) (by linarith) hsm hmem5
  have hDthSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth g) := hsm.Dth
  have hprod := hN.prod α hIoc (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
    (Work.Spaces.Dth g)
    ⟨Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm, hfMem⟩
    ⟨hDthSm, hDthMem⟩
  have hid : Work.FTS.Nonlin.N04bF α g
      = fun z θ => (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) z θ
          * Work.Spaces.Dth g z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.Ftot,
      Work.Construction.Fstar, Work.Spaces.Dth, Work.Spaces.pth, Work.Construction.s2,
      Work.FTS.Nonlin.PhiTg]
    ring
  rw [hid]
  refine ⟨hprod.1, ?_⟩
  -- the pairing bound, from the honest transport clause `t4`
  have ht4 := hE.t4 α hIoc (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z) g
    (Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm) hWDmem hsm hmem4 hmem5 hdec
  refine ht4.trans ?_
  have hrp : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hb1 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3 :=
    mul_nonneg (Real.rpow_nonneg hα.le _) (pow_nonneg hX0 3)
  have hXg3 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g ^ 2 := pow_nonneg hX0 2
  calc Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.VocabO.WDp 4
          (fun z θ => (3 / (2 * α)) * Work.Construction.L12 g z)
        * Work.FTS.Nonlin.Xn α g ^ 2
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * (25 * ((3 / (2 * α)) * (KL * Work.FTS.Nonlin.Xn α g)))
        * Work.FTS.Nonlin.Xn α g ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWDp ?_) hXg3
        exact mul_nonneg hCt.le hrp
    _ = Ct * 25 * (3 / 2) * KL * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
        have hpow : α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 : ℝ)) = α ^ (-(3 / 2 : ℝ)) := by
          rw [← Real.rpow_add hα]
          norm_num
        have hinv : (3 : ℝ) / (2 * α) = (3 / 2) * α ^ (-(1 : ℝ)) := by
          rw [Real.rpow_neg_one]
          field_simp
        rw [hinv]
        linear_combination (Ct * 25 * (3 / 2) * KL * Work.FTS.Nonlin.Xn α g ^ 3) * hpow
    _ ≤ (Ct * 25 * (3 / 2) * KL + 1)
          * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
        refine mul_le_mul_of_nonneg_right ?_ hb1
        linarith [hCt, hKLpos]

end Work.FTS.StrongEps.E4R3.N4C.HonRowsU
end
-- ===== merged: Submission.Work.FTS.StrongEps.exists_limG =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false


end Work.FTS.StrongEps
end
end
