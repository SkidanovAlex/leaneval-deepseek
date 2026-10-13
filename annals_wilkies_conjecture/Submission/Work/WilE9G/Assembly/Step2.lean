/-
  Subproject WilE9G / Assembly — the Lagrange-multiplier step of the covering argument.

  Given an ambient `Good` stratum `S`, a weight `Φ` which is strictly positive on `S.X.set`, a
  direction `c` and a point `w'` which is a **local maximum of `Φ · e^{c·(y,t)}` on the fibre of
  `S.X.set` through `w'`**, this file produces multipliers `(μ, μ₀)` with

  * `LagEq S Φ c w' μ μ₀` (the Lagrange equations),
  * `LagNorm μ μ₀` (the normalisation), and
  * `(lagJac S Φ c w' μ μ₀).det ≠ 0` (nondegeneracy, from an input hypothesis).

  The multiplier theorem `exists_multiplier_of_ambStratum_fibre` (G3) is applied to the stratum
  `S` with the chain extended by the atom `c · (y,t)` (`ambCat` + `atomChain`), so that the weight
  `Φ · e^{c·(y,t)}` is an `EA`-polynomial of the stratum's chain; the equations of `S` and of its
  extension agree by the `cat`-transport lemmas.
-/
import Mathlib
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE9G.Assembly.ambCat_eval
import Submission.Work.WilE9G.Assembly.ambCat_set_good_deg
import Submission.Work.WilE9G.Assembly.eaD_cat_inl_inr
import Submission.Work.WilE9G.Mult.exists_multiplier_of_ambStratum_fibre
import Submission.Work.WilE9G.Lagrange.LagBlkAux

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G.Assembly
open WilkiesDesign WilkiesDesign.E Work.WilE9G Work.WilE9G.Lagrange

variable {n m : ℕ}

/-- Evaluation of a sum of `EA`-polynomials. -/
theorem eaEval_add_pt {k r : ℕ} (c : EAChain k r) (P Q : EAPoly k r) (z : Fin k → ℝ) :
    eaEval c (P + Q) z = eaEval c P z + eaEval c Q z := by
  simp only [eaEval, map_add]

/-- Evaluation of a product of `EA`-polynomials. -/
theorem eaEval_mul_pt {k r : ℕ} (c : EAChain k r) (P Q : EAPoly k r) (z : Fin k → ℝ) :
    eaEval c (P * Q) z = eaEval c P z * eaEval c Q z := by
  simp only [eaEval, map_mul]

/-- The stratum `S` with its chain extended by the atom `c·(y,t)`.  (An `abbrev`, on a literal,
so that its fields reduce at reducible transparency: the transport lemmas below are stated for
the stratum's own fields.) -/
abbrev ext (S : Work.WilE9G.AmbStratum (n + (1 + m))) (c : Fin (1 + m) → ℝ) :
    Work.WilE9G.AmbStratum (n + (1 + m)) :=
  ⟨⟨S.X.r + 1, Work.WilE7.EAChain.cat S.X.c (atomChain n m c),
     S.X.basics.map Work.WilE7.Basic.inl⟩, S.j, fun a => Work.WilE7.EAPoly.inl (S.h a)⟩

theorem ext_eq_ambCat (S : Work.WilE9G.AmbStratum (n + (1 + m))) (c : Fin (1 + m) → ℝ) :
    ext S c = ambCat S (atomChain n m c) := by
  simp only [ext, ambCat, Work.WilE7.SemiPf.unionSet]
  rw [show (List.map Work.WilE7.Basic.inr ([] : List (Basic (n + (1 + m)) 1))) = []
    from List.map_nil]
  rw [List.append_nil]

/-- The weight `Φ · e^{c·(y,t)}` as an `EA`-polynomial of the extended chain. -/
def extChi (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ) :
    EAPoly (n + (1 + m)) (ext S c).X.r :=
  Work.WilE7.EAPoly.inl Phi
    * Work.WilE7.EAPoly.inr (MvPolynomial.X (Sum.inr 0))

/-- The evaluation of the extended weight polynomial is `Φ · e^{c·(y,t)}`. -/
theorem eaEval_extChi (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) :
    eaEval (ext S c).X.c (extChi S Phi c) z
      = eaEval S.X.c Phi z * Real.exp (∑ l : Fin (1 + m), c l * z (Fin.natAdd n l)) := by
  rw [extChi, eaEval_mul_pt, Work.WilE7.SubPfAux.eaEval_cat_inl,
    Work.WilE7.SubPfAux.eaEval_cat_inr, eaEval_atomChain]

/-- The derivative of the extended weight in a fibre direction. -/
theorem eaEval_extChi_eaD (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (l : Fin (1 + m)) :
    eaEval (ext S c).X.c (eaD (ext S c).X.c (Fin.natAdd n l) (extChi S Phi c)) z
      = Real.exp (∑ l' : Fin (1 + m), c l' * z (Fin.natAdd n l'))
        * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) z + eaEval S.X.c Phi z * c l) := by
  have hatom : eaEval (ext S c).X.c (Work.WilE7.EAPoly.inr (MvPolynomial.X (Sum.inr 0))) z
      = Real.exp (∑ l' : Fin (1 + m), c l' * z (Fin.natAdd n l')) := by
    rw [Work.WilE7.SubPfAux.eaEval_cat_inr, eaEval_atomChain]
  have hatom' : eaEval (ext S c).X.c
        (Work.WilE7.EAPoly.inr (MvPolynomial.C (c l) * MvPolynomial.X (Sum.inr 0))) z
      = c l * Real.exp (∑ l' : Fin (1 + m), c l' * z (Fin.natAdd n l')) := by
    rw [Work.WilE7.SubPfAux.eaEval_cat_inr, eaEval_mul_pt, eaEval, MvPolynomial.eval_C,
      eaEval_atomChain]
  rw [extChi, Work.WilE9G.Lagrange.LagBlk.pEaD_mul, eaEval_add_pt, eaEval_mul_pt, eaEval_mul_pt,
    eaEval_eaD_cat_inl, Work.WilE7.SubPfAux.eaEval_cat_inl,
    (eaD_cat_inl_inr S.X.c (atomChain n m c)).2, eaD_atomChain, hatom, hatom']
  ring

/-- The lifted equations of the extended stratum, evaluated. -/
theorem eaEval_ext_h_eaD (S : Work.WilE9G.AmbStratum (n + (1 + m))) (c : Fin (1 + m) → ℝ)
    (a : Fin S.j) (l : Fin (1 + m)) (z : Fin (n + (1 + m)) → ℝ) :
    eaEval (ext S c).X.c (eaD (ext S c).X.c (Fin.natAdd n l) ((ext S c).h a)) z
      = eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) z := by
  rw [eaEval_eaD_cat_inl]

/-- **The Lagrange multipliers at a local maximum of the weight on the fibre.** -/
theorem exists_lagrange_of_localmax (S : Work.WilE9G.AmbStratum (n + (1 + m))) (hS : S.Good)
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (hpos : ∀ z ∈ S.X.set, 0 < eaEval S.X.c Phi z)
    (w' : Fin (n + (1 + m)) → ℝ) (hmem : w' ∈ S.X.set)
    (hsub : S.IsBaseSubmersiveAt (Nat.le_add_right n (1 + m)) w')
    (hmax : ∃ ε : ℝ, 0 < ε ∧ ∀ z : Fin (n + (1 + m)) → ℝ, z ∈ S.X.set → dist z w' < ε →
      projBase (Nat.le_add_right n (1 + m)) z = projBase (Nat.le_add_right n (1 + m)) w' →
      eaEval S.X.c Phi z * Real.exp (∑ l : Fin (1 + m), c l * z (Fin.natAdd n l))
        ≤ eaEval S.X.c Phi w' * Real.exp (∑ l : Fin (1 + m), c l * w' (Fin.natAdd n l)))
    (hnd : ∀ (mu : Fin S.j → ℝ) (mu0 : ℝ), LagEq S Phi c w' mu mu0 → LagNorm mu mu0 →
      (lagJac S Phi c w' mu mu0).det ≠ 0) :
    ∃ (mu : Fin S.j → ℝ) (mu0 : ℝ),
      LagEq S Phi c w' mu mu0 ∧ LagNorm mu mu0 ∧ (lagJac S Phi c w' mu mu0).det ≠ 0 := by
  classical
  obtain ⟨hset, hgood, -, -, -, -⟩ := ambCat_set_good_deg S (atomChain n m c)
  have hSext : (ext S c).Good := by rw [ext_eq_ambCat]; exact hgood.mpr hS
  have hmemext : w' ∈ (ext S c).X.set := by rw [ext_eq_ambCat, hset]; exact hmem
  have hsubext : (ext S c).IsBaseSubmersiveAt (Nat.le_add_right n (1 + m)) w' := by
    intro v
    obtain ⟨u, hu, hu0⟩ := hsub v
    refine ⟨u, hu, fun a => ?_⟩
    have hfd : (fderiv ℝ (fun z' : Fin (n + (1 + m)) → ℝ =>
          eaEval (ext S c).X.c ((ext S c).h a) z') w')
        = fderiv ℝ (fun z' : Fin (n + (1 + m)) → ℝ => eaEval S.X.c (S.h a) z') w' :=
      (ambCat_eval S (atomChain n m c)).2.2 w' a
    rw [hfd]
    exact hu0 a
  have hmaxext : ∃ ε : ℝ, 0 < ε ∧ ∀ z : Fin (n + (1 + m)) → ℝ, dist z w' < ε →
      z ∈ (ext S c).X.set → projBase (Nat.le_add_right n (1 + m)) z
        = projBase (Nat.le_add_right n (1 + m)) w' →
      eaEval (ext S c).X.c (extChi S Phi c) z ≤ eaEval (ext S c).X.c (extChi S Phi c) w' := by
    obtain ⟨ε, hε, hε'⟩ := hmax
    refine ⟨ε, hε, fun z hd hz hb => ?_⟩
    rw [eaEval_extChi, eaEval_extChi]
    exact hε' z (by rw [ext_eq_ambCat, hset] at hz; exact hz) hd hb
  obtain ⟨nu, hnu⟩ := Work.WilE9G.Mult.exists_multiplier_of_ambStratum_fibre (ext S c) hSext w'
    hmemext hsubext (extChi S Phi c) hmaxext
  set A : ℝ := Real.exp (∑ l : Fin (1 + m), c l * w' (Fin.natAdd n l)) with hA
  have hApos : 0 < A := Real.exp_pos _
  have hPhipos : 0 < eaEval S.X.c Phi w' := hpos w' hmem
  -- the key relation
  have key : ∀ l : Fin (1 + m),
      A * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) w' + eaEval S.X.c Phi w' * c l)
        = ∑ a, nu a * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) w' := by
    intro l
    have h1 := hnu l
    rw [eaEval_extChi_eaD S Phi c w' l] at h1
    have h2 : (∑ a : Fin S.j, nu a * eaEval (ext S c).X.c
        (eaD (ext S c).X.c (Fin.natAdd n l) ((ext S c).h a)) w')
        = ∑ a : Fin S.j, nu a * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) w' :=
      Finset.sum_congr rfl fun a _ => by rw [eaEval_ext_h_eaD]
    rw [h2] at h1
    exact h1
  -- the unnormalised multipliers
  set mu0 : ℝ := eaEval S.X.c Phi w' with hmu0
  have hmu0pos : 0 < mu0 := hPhipos
  have hLagEq0 : LagEq S Phi c w' (fun a => nu a * mu0 / A) mu0 := by
    intro l
    have h := key l
    have h1 : mu0 * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) w'
        + eaEval S.X.c Phi w' * c l)
        = (mu0 / A) * (A * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) w'
          + eaEval S.X.c Phi w' * c l)) := by
      field_simp
    rw [h1, h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  -- the normalised multipliers
  set N2 : ℝ := (∑ a : Fin S.j, (nu a * mu0 / A) ^ 2) + mu0 ^ 2 with hN2
  have hN2pos : 0 < N2 := by
    rw [hN2]
    have h0 : 0 ≤ ∑ a : Fin S.j, (nu a * mu0 / A) ^ 2 :=
      Finset.sum_nonneg fun a _ => sq_nonneg _
    have h1 : 0 < mu0 ^ 2 := pow_pos hmu0pos 2
    linarith
  set t : ℝ := (Real.sqrt N2)⁻¹ with ht
  have htN : t ^ 2 * N2 = 1 := by
    rw [ht, inv_pow, Real.sq_sqrt hN2pos.le]
    exact inv_mul_cancel₀ (ne_of_gt hN2pos)
  have hLagEq' : LagEq S Phi c w' (fun a => t * (nu a * mu0 / A)) (t * mu0) := by
    intro l
    have h := hLagEq0 l
    have h2 : t * mu0 * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) w'
        + eaEval S.X.c Phi w' * c l)
        = t * (mu0 * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) w'
          + eaEval S.X.c Phi w' * c l)) := by ring
    rw [h2, h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hNorm' : LagNorm (fun a => t * (nu a * mu0 / A)) (t * mu0) := by
    show (∑ a : Fin S.j, (t * (nu a * mu0 / A)) ^ 2) + (t * mu0) ^ 2 = 1
    have h1 : (∑ a : Fin S.j, (t * (nu a * mu0 / A)) ^ 2)
        = t ^ 2 * ∑ a : Fin S.j, (nu a * mu0 / A) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    have h2 : (t * mu0) ^ 2 = t ^ 2 * mu0 ^ 2 := by ring
    rw [h1, h2, ← mul_add, htN]
  exact ⟨fun a => t * (nu a * mu0 / A), t * mu0, hLagEq', hNorm',
    hnd _ _ hLagEq' hNorm'⟩

end Work.WilE9G.Assembly
