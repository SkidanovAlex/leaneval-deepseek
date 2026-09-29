import Mathlib
import Submission.Work.GenShared.periods_defs
import Submission.Work.GenShared.rreg_Dv
import Submission.Work.GenShared.hasDerivAt_rval
import Submission.Work.GenShared.wevD
import Submission.Work.GenShared.hasDerivAt_wev
import Submission.Work.GenShared.wev_Dv_eq
import Submission.Work.GenShared.continuousOn_wev_Dv

/-!
# `N = ker ev` is stable under the connection `Dv`

`InN x0 δ y1 J n` says that the relation `Wev y1 J n z = a(z)y1(z) + b(z)y1'(z) + Σᵢ cᵢ(z)Jᵢ(z) = 0`
holds at every point of the ball at which all coefficients of `n = (a,b,c)` are regular.  This file
proves that this vanishing is preserved by the connection

`Dv p2 p1 p0 rn rd n = (a' - (p₀/p₂)b + Σᵢ cᵢ rᵢ, a + b' - (p₁/p₂)b, (cᵢ'))`,

i.e. `inN_dv : InN x0 δ y1 J n → InN x0 δ y1 J (Dv p2 p1 p0 rn rd n)`.

The mathematical content is that `∂` is the *dual* of differentiation of the evaluation: at every
point where the coefficients of `n` are regular one has

`d/dz (Wev y1 J n) (z) = Wev y1 J (Dv p2 p1 p0 rn rd n) (z)`,

because `y1` solves `p₂y'' + p₁y' + p₀y = 0` and `Jᵢ' = rᵢ y1`.  (`hasDerivAt_wev` computes the
derivative as `WevD y1 J n z`, `wev_Dv_eq` identifies `Wev (Dv … n) z` with the same expression.)

The subtle point is that the regularity set of `Dv … n` is *not* contained in the regularity set of
`n`: poles of `n` may cancel in `Dv … n` (only `dRat` cannot lose a pole, but the other summands can
cancel it).  So the identity above is available only on the open dense set `Nset x0 δ n ∩ Nset x0 δ m`
(`m = Dv … n`), and the vanishing is transferred to all of `Nset x0 δ m` by continuity: the
complement of the finite pole set of `n` is dense in the open set `Nset x0 δ m`
(`continuousOn_wev_Dv` supplies the continuity).
-/

namespace Work.GenShared

open Complex Metric Work.GenShared
open Filter
open scoped Topology
open Submission.CDT (dRat)

noncomputable section

/-! ## The regularity locus of a tuple as the nonvanishing set of one polynomial -/

/-- A single polynomial whose nonvanishing at `z` is exactly the regularity of `n` at `z`. -/
def Nden {k : ℕ} (n : W k) : Polynomial ℂ := n.1.denom * n.2.1.denom * ∏ i, (n.2.2 i).denom

/-- `n` is regular at `z` iff the polynomial `Nden n` does not vanish at `z`. -/
lemma Nreg_iff_Nden_eval_ne {k : ℕ} (n : W k) (z : ℂ) :
    Nreg n z ↔ (Nden n).eval z ≠ 0 := by
  simp only [Nreg, Rreg, Nden, Polynomial.eval_mul, Polynomial.eval_prod, mul_ne_zero_iff,
    Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies]
  tauto

/-- The regularity locus of `n`, written with the single polynomial `Nden n`. -/
def Nset' {k : ℕ} (x0 : ℂ) (δ : ℝ) (n : W k) : Set ℂ :=
  {z | z ∈ ball x0 δ ∧ (Nden n).eval z ≠ 0}

lemma Nset'_eq_Nset {k : ℕ} (x0 : ℂ) (δ : ℝ) (n : W k) : Nset' x0 δ n = Nset x0 δ n := by
  ext z
  simp only [Nset', Nset, Set.mem_ofPred_eq]
  exact and_congr_right (fun _ => (Nreg_iff_Nden_eval_ne n z).symm)

lemma isOpen_setOf_Nden_ne {k : ℕ} (n : W k) : IsOpen {z : ℂ | (Nden n).eval z ≠ 0} :=
  (isClosed_eq (Polynomial.continuous (Nden n)) continuous_const).isOpen_compl

lemma isOpen_Nset' {k : ℕ} (x0 : ℂ) (δ : ℝ) (n : W k) : IsOpen (Nset' x0 δ n) := by
  have h : IsOpen (ball x0 δ ∩ {z : ℂ | (Nden n).eval z ≠ 0}) :=
    Metric.isOpen_ball.inter (isOpen_setOf_Nden_ne n)
  convert h using 1
  ext z
  simp only [Nset', Set.mem_ofPred_eq, Set.mem_inter_iff]

/-! ## The main theorem -/

theorem inN_dv {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    (x0 : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hp2ne : ∀ z ∈ ball x0 δ, p2.eval z ≠ 0) (hrdne : ∀ i, ∀ z ∈ ball x0 δ, (rd i).eval z ≠ 0)
    (y1 : ℂ → ℂ) (hy1d : DifferentiableOn ℂ y1 (ball x0 δ))
    (hode : ∀ z ∈ ball x0 δ,
      p2.eval z * deriv (deriv y1) z + p1.eval z * deriv y1 z + p0.eval z * y1 z = 0)
    (J : Fin k → ℂ → ℂ) (hJd : ∀ i, DifferentiableOn ℂ (J i) (ball x0 δ))
    (hJderiv : ∀ i, ∀ z ∈ ball x0 δ, HasDerivAt (J i) ((rn i).eval z / (rd i).eval z * y1 z) z)
    {n : W k} (hn : InN x0 δ y1 J n) :
    InN x0 δ y1 J (Dv p2 p1 p0 rn rd n) := by
  set m : W k := Dv p2 p1 p0 rn rd n with hm
  rw [InN_iff_forall_Nset]
  intro z hz
  obtain ⟨hzball, hzreg⟩ := hz
  have hzUn : (Nden m).eval z ≠ 0 := (Nreg_iff_Nden_eval_ne m z).mp hzreg
  have hzU : z ∈ Nset' x0 δ m := ⟨hzball, hzUn⟩
  have hWopen : IsOpen (Nset' x0 δ n) := isOpen_Nset' x0 δ n
  have hUopen : IsOpen (Nset' x0 δ m) := isOpen_Nset' x0 δ m
  -- the pole set of `n` is finite
  have hfin : ({w : ℂ | (Nden n).eval w = 0}).Finite := by
    have hne : Nden n ≠ 0 := by
      rw [Nden]
      exact mul_ne_zero (mul_ne_zero (RatFunc.denom_ne_zero n.1) (RatFunc.denom_ne_zero n.2.1))
        (Finset.prod_ne_zero_iff.mpr (fun i _ => RatFunc.denom_ne_zero (n.2.2 i)))
    simpa [Polynomial.IsRoot.def] using Polynomial.finite_setOfPred_isRoot hne
  have hdense : Dense (({w : ℂ | (Nden n).eval w = 0})ᶜ : Set ℂ) :=
    Set.Countable.dense_compl ℂ hfin.countable
  have hsub : Nset' x0 δ m ⊆
      closure (Nset' x0 δ m ∩ ({w : ℂ | (Nden n).eval w = 0})ᶜ) :=
    hdense.open_subset_closure_inter hUopen
  have hset : Nset' x0 δ m ∩ ({w : ℂ | (Nden n).eval w = 0})ᶜ
      = Nset' x0 δ n ∩ Nset' x0 δ m := by
    ext w
    change ((w ∈ ball x0 δ ∧ (Nden m).eval w ≠ 0) ∧ ¬ ((Nden n).eval w = 0))
        ↔ ((w ∈ ball x0 δ ∧ (Nden n).eval w ≠ 0) ∧ (w ∈ ball x0 δ ∧ (Nden m).eval w ≠ 0))
    constructor
    · rintro ⟨⟨hb, hm'⟩, hn'⟩; exact ⟨⟨hb, hn'⟩, hb, hm'⟩
    · rintro ⟨⟨hb, hn'⟩, _, hm'⟩; exact ⟨⟨hb, hm'⟩, hn'⟩
  have hzcl : z ∈ closure (Nset' x0 δ n ∩ Nset' x0 δ m) := by
    have h := hsub hzU
    rwa [hset] at h
  -- the evaluation vanishes on the intersection of the two regularity loci
  have hzeroOn : ∀ w ∈ Nset' x0 δ n ∩ Nset' x0 δ m, Wev y1 J m w = 0 := by
    intro w hw
    have hwball : w ∈ ball x0 δ := hw.1.1
    have hwn : (Nden n).eval w ≠ 0 := hw.1.2
    have hwnreg : Nreg n w := (Nreg_iff_Nden_eval_ne n w).mpr hwn
    have hder := hasDerivAt_wev y1 J x0 hy1d hJd hwball hwnreg.1 hwnreg.2.1 hwnreg.2.2
    have h1 : deriv (Wev y1 J n) w = WevD y1 J n w := hder.deriv
    have hev : Wev y1 J n =ᶠ[𝓝 w] (fun _ => (0 : ℂ)) := by
      refine Filter.eventually_of_mem (hWopen.mem_nhds hw.1) ?_
      intro u hu
      exact (InN_iff_forall_Nset.mp hn) u (by rwa [Nset'_eq_Nset] at hu)
    have h2 : deriv (Wev y1 J n) w = 0 := by
      rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
    have h3 : Wev y1 J m w = WevD y1 J n w :=
      wev_Dv_eq p2 p1 p0 rn rd x0 hp2ne hrdne y1 hode J hJderiv hwball
        hwnreg.1 hwnreg.2.1 hwnreg.2.2
    rw [h3, ← h1, h2]
  -- continuity of the evaluation on the regularity locus of `m`
  have hcont : ContinuousOn (fun w => Wev y1 J m w) (Nset' x0 δ m) := by
    have h := continuousOn_wev_Dv p2 p1 p0 rn rd x0 y1 hy1d J hJd n
    simpa [Nset'_eq_Nset] using h
  -- conclude by continuity and density
  have hne : NeBot (𝓝[Nset' x0 δ n ∩ Nset' x0 δ m] z) :=
    mem_closure_iff_nhdsWithin_neBot.mp hzcl
  haveI := hne
  have htend1 : Tendsto (fun w => Wev y1 J m w) (𝓝[Nset' x0 δ n ∩ Nset' x0 δ m] z)
      (𝓝 (Wev y1 J m z)) :=
    (hcont.continuousWithinAt hzU).mono_left (nhdsWithin_mono z Set.inter_subset_right)
  have htend2 : Tendsto (fun w => Wev y1 J m w) (𝓝[Nset' x0 δ n ∩ Nset' x0 δ m] z) (𝓝 0) := by
    have hev2 : (fun w => Wev y1 J m w) =ᶠ[𝓝[Nset' x0 δ n ∩ Nset' x0 δ m] z]
        (fun _ => (0 : ℂ)) :=
      Filter.eventually_of_mem self_mem_nhdsWithin hzeroOn
    exact (tendsto_const_nhds (x := (0 : ℂ))).congr' hev2.symm
  exact tendsto_nhds_unique htend1 htend2

end

end Work.GenShared
