import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-!
# Vocabulary of the semi-tame estimate of `epsWP`

The projected right-hand side `epsWP α ρ ε Φs E g τ` is, definitionally, a function of the
projected slice `w = slice (JfamP ρ ε g) τ`, the elliptic profile `Φg = E w` and the two
modulation constants `μ, lam` alone (`Ftau α (JfamP ρ ε g) τ = Ftot α w`,
`slice (PsiCan Φs E (JfamP ρ ε g)) τ = Φs + Φg`, and `muDyn = muBlk`, `lamDyn = lamfun muBlk`).

It is the signed sum of five blocks, `-𝓛_Γ^T w`, `-μ̄·AK`, `N₀`, `N` and `N_*`; `BData` records
what each block must supply for the semi-tame estimate: open-quadrant smoothness, `ℋ⁶`-honesty,
a level-`4` energy bound priced by the `ℋ⁵`-energy of the slice, and a level-`6` energy bound
with the top order entering *linearly* through `ℋ⁷` and a quadratic remainder in `ℋ⁶`.
-/

/-- The projected right-hand side, written in terms of the projected slice `w`, the elliptic
profile `Φg = E w` and the two modulation constants `μ, lam`. -/
noncomputable def epsWBlk (α : ℝ) (Φs w Φg : Fn) (μ lam : ℝ) : Fn :=
  fun z θ => -Work.Coercivity.LGammaT α w z θ
    + Work.Construction.gRHS α μ lam (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ) w z θ

/-- The modulation constant `μ` of `epsWP` at the projected slice. -/
noncomputable def muBlk (α : ℝ) (Φs w Φg : Fn) : ℝ :=
  Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
    (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) w

/-- **The decomposition of `epsWP`**: with `w = slice (JfamP ρ ε g) τ` and `Φg = E w`, the
projected right-hand side is the block form `epsWBlk` at the modulation constant `muBlk`. -/
theorem epsWP_eq_epsWBlk (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (g : Fam) (τ : ℝ) :
    Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ
      = epsWBlk α Φs (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
          (E (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ))
          (muBlk α Φs (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (E (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)))
          (Work.Construction.lamfun (muBlk α Φs (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (E (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)))) := rfl

/-- The modulation constant is the one `MuLamOK` controls. -/
theorem muDyn_const_eq (α : ℝ) (Φs : Fn) (E : Fn → Fn) (w : Fn) :
    Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E fun z θ _ => w z θ)
        (fun z θ _ => w z θ) 0 = muBlk α Φs w (E w) := rfl

theorem lamDyn_const_eq (α : ℝ) (Φs : Fn) (E : Fn → Fn) (w : Fn) :
    Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E fun z θ _ => w z θ)
        (fun z θ _ => w z θ) 0 = Work.Construction.lamfun (muBlk α Φs w (E w)) := by
  rw [Work.FTS.Galerkin.lamDyn, muDyn_const_eq]

/-! ## The blocks -/

noncomputable def blkLin (α : ℝ) (w : Fn) : Fn := Work.Coercivity.LGammaT α w

noncomputable def blkMu (α : ℝ) (Φs w Φg : Fn) : Fn :=
  fun z θ => Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))
    * Work.Construction.AK α z θ

noncomputable def blkN0 (α : ℝ) (w : Fn) : Fn :=
  Work.Construction.N0 α (Work.Construction.Ftot α w) w

noncomputable def blkN (α : ℝ) (Φs w Φg : Fn) : Fn :=
  Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)

noncomputable def blkNstar (w : Fn) (μ lam : ℝ) : Fn := Work.Construction.Nstar μ lam w

/-- A smart constructor for the five-fold signed sum. -/
noncomputable def sum5 (a b c d e : Fn) : Fn :=
  fun z θ => a z θ + (b z θ + (c z θ + (d z θ + e z θ)))

/-- **`epsWBlk` is the signed sum of the five blocks.** -/
theorem epsWBlk_eq_sum5 (α : ℝ) (Φs w Φg : Fn) (μ lam : ℝ) :
    epsWBlk α Φs w Φg μ lam
      = sum5 (fun z θ => - blkLin α w z θ) (fun z θ => - blkMu α Φs w Φg z θ)
          (blkN0 α w) (blkN α Φs w Φg) (blkNstar w μ lam) := by
  funext z θ
  simp only [epsWBlk, sum5, blkLin, blkMu, blkN0, blkN, blkNstar, Work.Construction.gRHS]
  ring

/-! ## The block data -/

/-- The data every block of `epsWBlk` must supply: open-quadrant smoothness, `ℋ⁶`-honesty, and
the two semi-tame size bounds. -/
structure BData (α : ℝ) (w : Fn) (K : ℝ) (B : Fn) : Prop where
  sm : Work.FTS.EllipticEst.SmoothOpen B
  hm : Work.Spaces.HkMem α 6 B
  b4 : Work.Spaces.HkSq α 4 B ≤ K * (1 + Work.Spaces.HkSq α 5 w)
  b6 : Work.Spaces.HkSq α 6 B ≤ K * (1 + Work.Spaces.HkSq α 7 w)
        + K * (1 + Work.Spaces.HkSq α 6 w) ^ 2

/-! ## Elementary invariance and additivity helpers -/

theorem smoothOpen_add {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ + g z θ) :=
  Work.FTS.EllipticEst.smoothOpen_of_forall (fun n =>
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).1 hf n).add
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall g).1 hg n))

theorem smoothOpen_neg {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f z θ) :=
  Work.FTS.EllipticEst.smoothOpen_of_forall (fun n =>
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).1 hf n).neg)

theorem hkSq_neg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (fun z θ => -f z θ) = Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  exact congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ

theorem hkMem_neg {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hm : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  rw [Work.Spaces.HkMem] at hm ⊢
  constructor
  · intro z hz
    refine (hm.1 z hz).congr ?_
    filter_upwards with θ
    exact (congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ).symm
  · refine hm.2.congr ?_
    filter_upwards with z
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    exact (congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ).symm

/-- `BData` is invariant under negation of the block. -/
theorem BData.neg {α : ℝ} {w : Fn} {K : ℝ} {B : Fn} (d : BData α w K B) :
    BData α w K (fun z θ => -B z θ) where
  sm := smoothOpen_neg d.sm
  hm := hkMem_neg d.hm
  b4 := by rw [hkSq_neg]; exact d.b4
  b6 := by rw [hkSq_neg]; exact d.b6

theorem smoothOpen_sum5 {a b c d e : ℝ → ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen a) (hb : Work.FTS.EllipticEst.SmoothOpen b)
    (hc : Work.FTS.EllipticEst.SmoothOpen c) (hd : Work.FTS.EllipticEst.SmoothOpen d)
    (he : Work.FTS.EllipticEst.SmoothOpen e) :
    Work.FTS.EllipticEst.SmoothOpen (sum5 a b c d e) :=
  smoothOpen_add ha (smoothOpen_add hb (smoothOpen_add hc (smoothOpen_add hd he)))

theorem hkMem_sum5 {α : ℝ} {k : ℕ} {a b c d e : ℝ → ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen a) (hb : Work.FTS.EllipticEst.SmoothOpen b)
    (hc : Work.FTS.EllipticEst.SmoothOpen c) (hd : Work.FTS.EllipticEst.SmoothOpen d)
    (he : Work.FTS.EllipticEst.SmoothOpen e)
    (ma : Work.Spaces.HkMem α k a) (mb : Work.Spaces.HkMem α k b) (mc : Work.Spaces.HkMem α k c)
    (md : Work.Spaces.HkMem α k d) (me : Work.Spaces.HkMem α k e) :
    Work.Spaces.HkMem α k (sum5 a b c d e) := by
  have hsE := smoothOpen_add hd he
  have hmE := Work.FTS.EllipticEst.RPFresh.HkMem_add_open α k hd he md me
  have hsC := smoothOpen_add hc hsE
  have hmC := Work.FTS.EllipticEst.RPFresh.HkMem_add_open α k hc hsE mc hmE
  have hsB := smoothOpen_add hb hsC
  have hmB := Work.FTS.EllipticEst.RPFresh.HkMem_add_open α k hb hsC mb hmC
  exact Work.FTS.EllipticEst.RPFresh.HkMem_add_open α k ha hsB ma hmB

/-- **`HkSq` of the five-fold sum**: four applications of `HkSq_add_le_open`. -/
theorem hkSq_sum5 {α : ℝ} (hα : 0 < α) {k : ℕ} {a b c d e : ℝ → ℝ → ℝ}
    (ha : Work.FTS.EllipticEst.SmoothOpen a) (hb : Work.FTS.EllipticEst.SmoothOpen b)
    (hc : Work.FTS.EllipticEst.SmoothOpen c) (hd : Work.FTS.EllipticEst.SmoothOpen d)
    (he : Work.FTS.EllipticEst.SmoothOpen e)
    (ma : Work.Spaces.HkMem α k a) (mb : Work.Spaces.HkMem α k b) (mc : Work.Spaces.HkMem α k c)
    (md : Work.Spaces.HkMem α k d) (me : Work.Spaces.HkMem α k e) :
    Work.Spaces.HkSq α k (sum5 a b c d e)
      ≤ 16 * (Work.Spaces.HkSq α k a + Work.Spaces.HkSq α k b + Work.Spaces.HkSq α k c
          + Work.Spaces.HkSq α k d + Work.Spaces.HkSq α k e) := by
  have hsE := smoothOpen_add hd he
  have hmE := Work.FTS.EllipticEst.RPFresh.HkMem_add_open α k hd he md me
  have hsC := smoothOpen_add hc hsE
  have hmC := Work.FTS.EllipticEst.RPFresh.HkMem_add_open α k hc hsE mc hmE
  have hsB := smoothOpen_add hb hsC
  have hmB := Work.FTS.EllipticEst.RPFresh.HkMem_add_open α k hb hsC mb hmC
  have h1 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hd he md me
  have h2 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hc hsE mc hmE
  have h3 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα hb hsC mb hmC
  have h4 := Work.FTS.GalFields.RHS.HkSq_add_le_open α k hα ha hsB ma hmB
  have hnn : ∀ f : ℝ → ℝ → ℝ, 0 ≤ Work.Spaces.HkSq α k f := fun f =>
    Work.Spaces.HkSq_nonneg α k f
  have hA : Work.Spaces.HkSq α k (sum5 a b c d e)
      ≤ 2 * (Work.Spaces.HkSq α k a
          + 2 * (Work.Spaces.HkSq α k b
            + 2 * (Work.Spaces.HkSq α k c + 2 * (Work.Spaces.HkSq α k d + Work.Spaces.HkSq α k e)))) := by
    refine le_trans h4 ?_
    have h2' : Work.Spaces.HkSq α k (fun z θ => c z θ + (d z θ + e z θ))
        ≤ 2 * (Work.Spaces.HkSq α k c + 2 * (Work.Spaces.HkSq α k d + Work.Spaces.HkSq α k e)) := by
      refine le_trans h2 ?_
      linarith [h1, hnn c, hnn d, hnn e]
    have h3' : Work.Spaces.HkSq α k (fun z θ => b z θ + (c z θ + (d z θ + e z θ)))
        ≤ 2 * (Work.Spaces.HkSq α k b
            + 2 * (Work.Spaces.HkSq α k c + 2 * (Work.Spaces.HkSq α k d + Work.Spaces.HkSq α k e))) := by
      refine le_trans h3 ?_
      linarith [h2', hnn b, hnn c, hnn d, hnn e]
    linarith [h3', hnn a, hnn b, hnn c, hnn d, hnn e]
  refine le_trans hA ?_
  linarith [hnn a, hnn b, hnn c, hnn d, hnn e]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
