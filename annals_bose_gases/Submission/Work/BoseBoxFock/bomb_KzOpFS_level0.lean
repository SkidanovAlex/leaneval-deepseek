import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.split_KzBogFS_box
import Submission.Work.BoseBoxFock.split_N_slice
import Submission.Work.BoseBoxFock.split_Q2ex_box
import Submission.Work.BoseBoxFock.split_Q3T_box
import Submission.Work.BoseBoxFock.split_linOpT_box
import Submission.Work.BoseBoxFock.split_numOp_sum_box
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.bomb_KzOpFS_level0` — the level-zero transport of `KzOpFS` to `KzOpC`

`KzOpFS F T E gHat0 ρ` (FS `eq:Kz`) is an operator on `F.H = RealFock m`, the Fock space
of the `m` box modes *including* the condensate coordinate `0`.  Its spectator form
`KzOpC` (`KzOpC.lean`) is obtained by replacing every mode operator by its image under
`annOfE`/`creOfE`, `T.N` by `nPlusC`, `T.NH` by `BNH`, etc.

This file proves the transport on the **zero-condensate slice**: if
`split f0 = Finsupp.single 0 v`, then

    split (KzOpFS F T E gHat0 ρ f0) = Finsupp.single 0 (KzOpC f g BNH F E gHat0 ρ v),

and hence, since `bomb m p q = (coreInner (split p) (split q)).re`
(`Work.BoseB4.Split_inner`),

    bomb m f0 (KzOpFS F T E gHat0 ρ f0) = (inner ℂ v (KzOpC f g BNH F E gHat0 ρ v)).re.

## Assembly

The eight rows of `KzOpFS` are transported one by one (the row lemmas
`split_N_slice`, `split_KzBogFS_box`, `split_numOp_sum_box`, `split_linOpT_box`,
`split_Q2ex_box`, `split_Q3T_box`, plus the hypotheses `hNH`, `hTa`, `hTaDag` on `T`),
and then reassembled.  Every reassembly step is a term-level `Eq.trans` chain, because
the operators of `F := boxFockData … ` live on the *projection* `F.H`, which is only
*definitionally* `RealFock m`: `rw`/`simp` re-typecheck the goal at a transparency where
`F.H` does not unfold, and refuse to match.  `exact`-style terms go through the
elaborator (default transparency) and are unaffected; the three generic helpers
`split_add_eight`, `add_eight_congr` and `single_add_eight` below do the arithmetic.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

/-! ## 1. Slice and reassembly helpers -/

/-- The inner product of two vectors on the zero-condensate level is the spectator
inner product. -/
theorem coreInner_single_zero {m : ℕ} [NeZero m] (v w : cfock (Excited m)) :
    coreInner (Finsupp.single 0 v) (Finsupp.single 0 w) = inner ℂ v w := by
  rw [coreInner, Embed_single, Embed_single, inner_level]
  simp

/-- A real scalar through `Finsupp.single`, written as a complex one. -/
theorem smul_single_zero {m : ℕ} [NeZero m] (c : ℝ) (w : cfock (Excited m)) :
    c • Finsupp.single (0 : ℕ) w = Finsupp.single (0 : ℕ) ((c : ℂ) • w) :=
  (Complex.coe_smul c (Finsupp.single (0 : ℕ) w)).symm.trans
    (Finsupp.smul_single (c : ℂ) 0 w)

/-- `split` of an eight-fold sum. -/
theorem split_add_eight {m : ℕ} [NeZero m] (a b c d e f g h : RealFock m) :
    split (a + b + c + d + e + f + g + h)
      = split a + split b + split c + split d + split e + split f + split g + split h := by
  simp only [map_add]

/-- Congruence for an eight-fold sum. -/
theorem add_eight_congr {α : Type*} [AddCommMonoid α]
    {a b c d e f g h a' b' c' d' e' f' g' h' : α}
    (e1 : a = a') (e2 : b = b') (e3 : c = c') (e4 : d = d') (e5 : e = e') (e6 : f = f')
    (e7 : g = g') (e8 : h = h') :
    a + b + c + d + e + f + g + h = a' + b' + c' + d' + e' + f' + g' + h' := by
  rw [e1, e2, e3, e4, e5, e6, e7, e8]

/-- Eight vectors on the zero-condensate level combine into one. -/
theorem single_add_eight {m : ℕ} [NeZero m] (a b c d e f g h : cfock (Excited m)) :
    Finsupp.single (0 : ℕ) a + Finsupp.single 0 b + Finsupp.single 0 c + Finsupp.single 0 d
      + Finsupp.single 0 e + Finsupp.single 0 f + Finsupp.single 0 g + Finsupp.single 0 h
      = Finsupp.single 0 (a + b + c + d + e + f + g + h) := by
  simp only [← Finsupp.single_add]

/-! ## 2. The target -/

theorem bomb_KzOpFS_level0 {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (B : Work.BoseB4.BoxData) {ℓ : ℝ} (kmom : Mode → EuclideanSpace ℝ (Fin 3))
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (f g : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (T : Work.BoseB7A.TildeData (Work.BoseB4.boxFockData B kmom hkmom m f hf))
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) (hρ : 0 ≤ ρ) (hφ : ∀ k : Mode, f k 0 = 0)
    (BNH : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (hN : ∀ y : Work.BoseB4.RealFock m, Work.BoseB4.split (T.N y)
      = (Work.BoseB4.monoOp 1 1 (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
          + Work.BoseB4.monoOp 0 0 ((Work.BoseBoxFock.nPlusC (m := m))
              - (1 : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m)))) (Work.BoseB4.split y))
    (hNH : ∀ y : Work.BoseB4.RealFock m, Work.BoseB4.split (T.NH y) = Work.BoseB4.lift BNH (Work.BoseB4.split y))
    (hTa : ∀ s : Mode, s ≠ 0 → ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split (T.ta s y) = Work.BoseB4.lift (Work.BoseBoxFock.annOfE (g s)) (Work.BoseB4.split y))
    (hTaDag : ∀ s : Mode, s ≠ 0 → ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split (T.taDag s y) = Work.BoseB4.lift (Work.BoseBoxFock.creOfE (g s)) (Work.BoseB4.split y))
    (f0 : Work.BoseB4.RealFock m) (v : Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (hsp : Work.BoseB4.split f0 = Finsupp.single 0 v) :
    Work.BoseB4.bomb m f0 (Work.BoseBoxFock.KzOpFS (Work.BoseB4.boxFockData B kmom hkmom m f hf) T E gHat0 ρ f0)
      = (inner ℂ v (Work.BoseBoxFock.KzOpC f g BNH (Work.BoseB4.boxFockData B kmom hkmom m f hf)
          E gHat0 ρ v)).re := by
  -- ## the eight transported rows
  have h1 : split (((E.b / (2 * E.ell ^ 2)) • T.N) f0)
      = Finsupp.single 0 ((((E.b / (2 * E.ell ^ 2) : ℝ)) : ℂ) • (nPlusC v)) :=
    (congrArg split (rfl : ((E.b / (2 * E.ell ^ 2)) • T.N) f0
        = (E.b / (2 * E.ell ^ 2)) • (T.N f0))).trans
      ((map_smul split (E.b / (2 * E.ell ^ 2)) (T.N f0)).trans
        ((congrArg (fun z => (E.b / (2 * E.ell ^ 2)) • z)
            (split_N_slice B kmom hkmom f hf T hN f0 v hsp)).trans
          (smul_single_zero _ _)))
  have h2 : split (((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • T.NH) f0)
      = Finsupp.single 0 ((((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2) : ℝ)) : ℂ) • (BNH v)) :=
    (congrArg split (rfl : ((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • T.NH) f0
        = (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • (T.NH f0))).trans
      ((map_smul split (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) (T.NH f0)).trans
        ((congrArg (fun z => (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • z)
            ((hNH f0).trans ((congrArg (lift BNH) hsp).trans
              (lift_single BNH 0 v)))).trans
          (smul_single_zero _ _)))
  have h3 : split (((E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0
          + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0 + (1 / 2) * ρ ^ 2 * E.W1omega0))
        • (1 : (boxFockData B kmom hkmom m f hf).H →ₗ[ℝ]
            (boxFockData B kmom hkmom m f hf).H)) f0)
      = Finsupp.single 0 ((((E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0
          + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0 + (1 / 2) * ρ ^ 2 * E.W1omega0) : ℝ)) : ℂ) • v) :=
    (congrArg split (rfl : ((E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0
          + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0 + (1 / 2) * ρ ^ 2 * E.W1omega0))
        • (1 : (boxFockData B kmom hkmom m f hf).H →ₗ[ℝ]
            (boxFockData B kmom hkmom m f hf).H)) f0
        = (E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0
          + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0 + (1 / 2) * ρ ^ 2 * E.W1omega0)) • f0)).trans
      ((map_smul split (E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0
          + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0 + (1 / 2) * ρ ^ 2 * E.W1omega0)) f0).trans
        ((congrArg (fun z => (E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0
            + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0 + (1 / 2) * ρ ^ 2 * E.W1omega0)) • z)
            hsp).trans
          (smul_single_zero _ _)))
  have h4 : split ((KzBogFS (boxFockData B kmom hkmom m f hf) E ρ) f0)
      = Finsupp.single 0 (KzBogC f E ρ v) :=
    (split_KzBogFS_box B kmom hkmom f hf hφ E ρ f0).trans
      ((congrArg (lift (KzBogC f E ρ)) hsp).trans (lift_single (KzBogC f E ρ) 0 v))
  have h5 : split ((((ρ - E.mu) * E.W1 0) •
        ∑ k : Mode, (boxFockData B kmom hkmom m f hf).nOp k) f0)
      = Finsupp.single 0 (((((ρ - E.mu) * E.W1 0 : ℝ)) : ℂ) •
          ((∑ k : Mode, nOpC (f k)) v)) :=
    (congrArg split (rfl : (((ρ - E.mu) * E.W1 0) •
          ∑ k : Mode, (boxFockData B kmom hkmom m f hf).nOp k) f0
        = ((ρ - E.mu) * E.W1 0) •
          ((∑ k : Mode, (boxFockData B kmom hkmom m f hf).nOp k) f0))).trans
      ((map_smul split ((ρ - E.mu) * E.W1 0)
          ((∑ k : Mode, (boxFockData B kmom hkmom m f hf).nOp k) f0)).trans
        ((congrArg (fun z => ((ρ - E.mu) * E.W1 0) • z)
            ((split_numOp_sum_box B kmom hkmom f hf hφ f0).trans
              ((congrArg (lift (∑ k : Mode, nOpC (f k))) hsp).trans
                (lift_single (∑ k : Mode, nOpC (f k)) 0 v)))).trans
          (smul_single_zero _ _)))
  have h6 : split ((T.linOpT (Work.BoseFixR.KzEnvAt E ρ)) f0)
      = Finsupp.single 0 (linOpTC g (Work.BoseFixR.KzEnvAt E ρ) v) :=
    (split_linOpT_box B kmom hkmom f g hf T hTa hTaDag
        (Work.BoseFixR.KzEnvAt E ρ) f0).trans
      ((congrArg (lift (linOpTC g (Work.BoseFixR.KzEnvAt E ρ))) hsp).trans
        (lift_single (linOpTC g (Work.BoseFixR.KzEnvAt E ρ)) 0 v))
  have h7 : split (((boxFockData B kmom hkmom m f hf).Q2ex (Work.BoseFixR.KzEnvAt E ρ)) f0)
      = Finsupp.single 0 (Q2exC f (Work.BoseFixR.KzEnvAt E ρ) v) :=
    (split_Q2ex_box B kmom hkmom f hf hφ (Work.BoseFixR.KzEnvAt E ρ) f0).trans
      ((congrArg (lift (Q2exC f (Work.BoseFixR.KzEnvAt E ρ))) hsp).trans
        (lift_single (Q2exC f (Work.BoseFixR.KzEnvAt E ρ)) 0 v))
  have h8 : split ((T.Q3T (Work.BoseFixR.KzEnvAt E ρ)) f0)
      = Finsupp.single 0 (Q3TC f g (boxFockData B kmom hkmom m f hf)
          (Work.BoseFixR.KzEnvAt E ρ) v) :=
    (split_Q3T_box B kmom hkmom f g hf hφ T hTa hTaDag (Work.BoseFixR.KzEnvAt E ρ) f0).trans
      ((congrArg (lift (Q3TC f g (boxFockData B kmom hkmom m f hf)
          (Work.BoseFixR.KzEnvAt E ρ))) hsp).trans
        (lift_single (Q3TC f g (boxFockData B kmom hkmom m f hf)
          (Work.BoseFixR.KzEnvAt E ρ)) 0 v))
  -- ## the definitional expansion of `KzOpFS` at `f0`, and the reassembly
  have hKz : (KzOpFS (boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0
      = ((E.b / (2 * E.ell ^ 2)) • T.N) f0
        + ((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • T.NH) f0
        + ((E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0
            + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0 + (1 / 2) * ρ ^ 2 * E.W1omega0))
            • (1 : (boxFockData B kmom hkmom m f hf).H →ₗ[ℝ]
                (boxFockData B kmom hkmom m f hf).H)) f0
        + (KzBogFS (boxFockData B kmom hkmom m f hf) E ρ) f0
        + (((ρ - E.mu) * E.W1 0) •
            ∑ k : Mode, (boxFockData B kmom hkmom m f hf).nOp k) f0
        + (T.linOpT (Work.BoseFixR.KzEnvAt E ρ)) f0
        + ((boxFockData B kmom hkmom m f hf).Q2ex (Work.BoseFixR.KzEnvAt E ρ)) f0
        + (T.Q3T (Work.BoseFixR.KzEnvAt E ρ)) f0 := rfl
  have hKzC : KzOpC f g BNH (boxFockData B kmom hkmom m f hf) E gHat0 ρ v
      = ((((E.b / (2 * E.ell ^ 2) : ℝ)) : ℂ) • (nPlusC v)
        + ((((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2) : ℝ)) : ℂ) • (BNH v))
        + ((((E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0
              + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0 + (1 / 2) * ρ ^ 2 * E.W1omega0) : ℝ)) : ℂ) • v)
        + (KzBogC f E ρ v)
        + (((((ρ - E.mu) * E.W1 0 : ℝ)) : ℂ) • ((∑ k : Mode, nOpC (f k)) v))
        + (linOpTC g (Work.BoseFixR.KzEnvAt E ρ) v)
        + (Q2exC f (Work.BoseFixR.KzEnvAt E ρ) v)
        + (Q3TC f g (boxFockData B kmom hkmom m f hf) (Work.BoseFixR.KzEnvAt E ρ) v)) := rfl
  have hsplit : split ((KzOpFS (boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0)
      = Finsupp.single 0 (KzOpC f g BNH (boxFockData B kmom hkmom m f hf) E gHat0 ρ v) :=
    (congrArg split hKz).trans
      ((split_add_eight _ _ _ _ _ _ _ _).trans
        ((add_eight_congr h1 h2 h3 h4 h5 h6 h7 h8).trans
          ((single_add_eight _ _ _ _ _ _ _ _).trans
            (congrArg (Finsupp.single (0 : ℕ)) hKzC.symm))))
  -- ## the `bomb`/`coreInner` bridge
  have hbomb : bomb m f0 ((KzOpFS (boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0)
      = (coreInner (split f0)
          (split ((KzOpFS (boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0))).re :=
    (Complex.ofReal_re _).symm.trans (congrArg Complex.re
      (Split_inner f0 ((KzOpFS (boxFockData B kmom hkmom m f hf) T E gHat0 ρ) f0))).symm
  refine hbomb.trans (congrArg Complex.re ?_)
  exact (congrArg (fun z => coreInner (split f0) z) hsplit).trans
    ((congrArg (fun z => coreInner z (Finsupp.single 0
        (KzOpC f g BNH (boxFockData B kmom hkmom m f hf) E gHat0 ρ v))) hsp).trans
      (coreInner_single_zero v
        (KzOpC f g BNH (boxFockData B kmom hkmom m f hf) E gHat0 ρ v)))

end Work.BoseBoxFock
