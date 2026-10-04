import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.elliptic_inv
import Submission.Work.Diff.STE.flat.inv_jet_bound_symm
import Submission.Work.Diff.STE.flat.inv_jet_bound
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.flat.CSq_symInvC_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Gårding bounds for the symmetrised inverse metric at level `k`

`Work.Diff.STE.fill.symInv_garding_bounds` collects, for the coefficient families used by the
Galerkin approximation of the flat DeTurck system, the two facts the level-`k` energy estimate
needs about the principal coefficient `G = (reMat (seriesFunM c ·))⁻¹` of the operator, symmetrised
by Clairaut (`Work.Diff.STE.flat.symInvR`, `Work.Diff.STE.flat.symInvC`):

* smoothness (`C^∞`) and `1`-periodicity of the symmetrised inverse-metric entries;
* a **uniform sup bound** for their first spatial derivatives, and
* a **uniform lower bound** `lam' > 0` for the quadratic form of the symmetrised inverse (Gårding's
  coercivity condition), with `lam'` depending only on `n`, `k`, `lam` and `B`.

## Route

The only hypothesis on the energy is at the *level `k`* (`ENormSqFull k ≤ B²`), so all the bounds
are built at level `k`.  The Sobolev threshold needed is `sob n = n/2 + 1 ≤ k` (for the sup bound
of the series itself) and `1 + sob n ≤ k` (for the sup bound of its first derivatives); both follow
from `card (Fin n) + 4 < 2 k`:

* `card (Fin n) + 4 < 2 k` gives `n/2 + 2 ≤ k` (`sob_le_of_card`, `one_add_sob_le_of_card`).

The ingredients are, at level `k`:

* `Work.Diff.STE.flat.CSq_symInvC_le`: the level-`k` Fourier mass of `symInvC` is bounded by a
  constant (uniform in the truncation, in `c` and in the index pair), via the Moser-type
  composition estimate applied to the smooth inverse-matrix entry;
* `Work.Diff.STE.flat.invJet_sup_pdVec_seriesFun_le`: a Fourier series whose level-`k` weighted
  mass is bounded has all its jets of order `j ≤ k - sob n` bounded in sup norm (Sobolev
  embedding); with `j = 1` this bounds `∂ᵢ symInvC` (and hence, taking real parts,
  `pdR i symInvR`);
* `Work.Diff.STE.flat.seriesFunM_entry_sup_uniform` + `Work.Diff.STE.flat.inv_quadForm_lower`: the
  entries of `reMat (seriesFunM c x)` are bounded by `Cs (1 + B)`, and the quadratic form of the
  symmetrised inverse of an elliptic matrix with entry bound `β` is at least
  `lam/(n β + 1)² · ‖·‖²`.
-/

namespace Work.Diff.STE.fill

open Work.Diff.STE

open scoped BigOperators

noncomputable section

/-- The hypothesis `card (Fin n) + 4 < 2 k` puts the Sobolev level `sob n = n/2 + 1` below `k`. -/
lemma sob_le_of_card {n k : ℕ} (hk : Fintype.card (Fin n) + 4 < 2 * k) :
    Work.Diff.STE.flat.sob n ≤ k := by
  have h : n + 4 < 2 * k := by simpa using hk
  simp only [Work.Diff.STE.flat.sob]
  omega

/-- The hypothesis `card (Fin n) + 4 < 2 k` gives `1 + sob n ≤ k`: the level-`k` energy bound
controls the *first* spatial derivatives of a Fourier series, not only its values. -/
lemma one_add_sob_le_of_card {n k : ℕ} (hk : Fintype.card (Fin n) + 4 < 2 * k) :
    1 + Work.Diff.STE.flat.sob n ≤ k := by
  have h : n + 4 < 2 * k := by simpa using hk
  simp only [Work.Diff.STE.flat.sob]
  omega

/-- **Gårding bounds for the symmetrised inverse metric at level `k`.**

For every truncation `N` and every box-supported coefficient family `c` whose level-`k` energy is
at most `B²` and whose real part is uniformly elliptic with constant `lam > 0`, the symmetrised
inverse metric `symInvR c = ((reMat (seriesFunM c ·))⁻¹ + transpose)/2` is smooth and `1`-periodic,
its first derivatives are bounded by a constant `C` depending only on `n`, `k`, `lam` and `B`, and
its quadratic form is bounded below by `lam' > 0`, again uniformly in `N` and in `c`. -/
theorem symInv_garding_bounds {n : ℕ} (hn : 1 ≤ n)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ lam' : ℝ, 0 < lam' ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
        Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c) ≤ B ^ 2 →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
        (∀ (a b : Fin n), ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.flat.symInvR c a b)) ∧
        (∀ (a b : Fin n), ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.flat.symInvC c a b)) ∧
        (∀ (a b : Fin n), Work.Diff.STE.Periodic1 (Work.Diff.STE.flat.symInvR c a b)) ∧
        (∀ (a b : Fin n), Work.Diff.STE.Periodic1 (Work.Diff.STE.flat.symInvC c a b)) ∧
        (∀ (a b i : Fin n) (x : Fin n → ℝ),
          |Work.Diff.STE.pdR i (Work.Diff.STE.flat.symInvR c a b) x| ≤ C) ∧
        (∀ (x : Fin n → ℝ) (ξ : Fin n → ℝ),
          lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, Work.Diff.STE.flat.symInvR c i j x * ξ i * ξ j) := by
  classical
  have hsob : Work.Diff.STE.flat.sob n ≤ k := sob_le_of_card hk
  have hsob1 : 1 + Work.Diff.STE.flat.sob n ≤ k := one_add_sob_le_of_card hk
  have hcard : Fintype.card (Fin n) < 2 * Work.Diff.STE.flat.sob n := by
    simpa using Work.Diff.STE.flat.n_lt_two_sob n
  -- sup bound on the entries of `seriesFunM c` (for the Gårding constant)
  obtain ⟨Cs, hCs, hCs'⟩ :=
    Work.Diff.STE.flat.seriesFunM_entry_sup_uniform (n := n) (s := k) hsob
  -- the Sobolev `ℓ¹`-type sup bound for a Fourier series
  obtain ⟨Csup, hCsupnn, hCsup'⟩ :=
    Work.Diff.STE.norm_seriesFun_le (ι := Fin n) (Work.Diff.STE.flat.sob n) hcard
  -- the level-`k` Fourier mass of the symmetrised inverse metric
  obtain ⟨Cinv, hCinvnn, hCinv⟩ := Work.Diff.STE.flat.CSq_symInvC_le hn k hsob lam hlam B hB
  have hCB : (1 : ℝ) ≤ (1 + B) ^ 2 := by nlinarith [hB]
  refine ⟨lam / (((n : ℝ) * (Cs * (1 + B)) + 1) ^ 2), by positivity,
    Csup * (2 * Real.pi) ^ k * Real.sqrt Cinv * (1 + B), by positivity, ?_⟩
  intro N c hc hE hell
  -- the elliptic radius containing the entry vector
  obtain ⟨ρ, _hρnn, hρmem⟩ := Work.Diff.STE.flat.invJet_entryVec_mem_elliptic (n := n) (s := k)
    (Bs := B) (lam := lam) hB hsob
  have hmem : ∀ x : Fin n → ℝ,
      Work.Diff.STE.flat.entryVec n c x ∈ Work.Diff.STE.flat.invNonsing n :=
    fun x => Work.Diff.STE.flat.invJet_invElliptic_subset_invNonsing hlam (hρmem N c hc hE hell x)
  have hvecsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => Work.Diff.STE.flat.entryVec n c x) :=
    Work.Diff.STE.flat.invJet_contDiff_invCvec_series c hc
  -- the composed form of `symInvC`
  have hEq : ∀ a b : Fin n,
      (fun x : Fin n → ℝ => Work.Diff.STE.flat.symInvPhi a b (Work.Diff.STE.flat.entryVec n c x))
        = Work.Diff.STE.flat.symInvC c a b :=
    fun a b => funext fun x =>
      congrFun (Work.Diff.STE.flat.symInvPhi_entryVec c a b) x
  -- smoothness of the symmetrised inverse metric
  have hsmC : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.flat.symInvC c a b) := by
    intro a b
    have hcomp : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Fin n → ℝ => Work.Diff.STE.flat.symInvPhi a b (Work.Diff.STE.flat.entryVec n c x)) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      exact ((Work.Diff.STE.flat.contDiffOn_symInvPhi a b).contDiffAt
        (Work.Diff.STE.flat.invJet_isOpen_invNonsing.mem_nhds (hmem x))).comp x
          hvecsm.contDiffAt
    rw [← hEq a b]
    exact hcomp
  -- periodicity of the symmetrised inverse metric
  have hperC : ∀ a b : Fin n, Work.Diff.STE.Periodic1 (Work.Diff.STE.flat.symInvC c a b) := by
    intro a b
    rw [← hEq a b]
    intro i x
    exact congrArg (Work.Diff.STE.flat.symInvPhi a b)
      (show Work.Diff.STE.flat.entryVec n c (x + Pi.single i 1)
          = Work.Diff.STE.flat.entryVec n c x from
        Work.Diff.STE.flat.invJet_periodic1_invCvec_series c i x)
  have hsmR : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.flat.symInvR c a b) := by
    intro a b
    have h := Complex.reCLM.contDiff.comp (hsmC a b)
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re, Work.Diff.STE.flat.symInvC]
      using h
  have hperR : ∀ a b : Fin n, Work.Diff.STE.Periodic1 (Work.Diff.STE.flat.symInvR c a b) := by
    intro a b i x
    have h := congrArg Complex.re (hperC a b i x)
    simpa only [Work.Diff.STE.flat.symInvC_apply, Complex.ofReal_re] using h
  -- the level-`k` mass bound of the symmetrised inverse metric
  have hcsq : ∀ a b : Fin n,
      Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (fun y => Work.Diff.STE.flat.symInvC c a b y))
        ≤ Cinv := fun a b => hCinv N c hc hE hell a b
  -- all weighted moments of the Fourier coefficients of `symInvC` are summable
  have hdmom2 : ∀ a b : Fin n, ∀ K : ℕ, Summable (fun m : Fin n → ℤ =>
      Work.Diff.STE.wt m ^ K
        * ‖Work.Diff.STE.fourierCoeff (fun y => Work.Diff.STE.flat.symInvC c a b y) m‖ ^ 2) :=
    fun a b K => Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff _
      (hsmC a b) (hperC a b) K
  have hdmom1 : ∀ a b : Fin n, ∀ K : ℕ, Summable (fun m : Fin n → ℤ =>
      Work.Diff.STE.wt m ^ K
        * ‖Work.Diff.STE.fourierCoeff (fun y => Work.Diff.STE.flat.symInvC c a b y) m‖) :=
    fun a b K => Work.Diff.STE.flat.invJet_summable_moment_of_wt_sq _ (hdmom2 a b) K
  -- the sup bound for the first derivatives of the symmetrised inverse metric
  have hsup : ∀ a b : Fin n, ∀ (l : Fin 1 → Fin n) (x : Fin n → ℝ),
      ‖Work.Diff.STE.pdVec 1 l (Work.Diff.STE.flat.symInvC c a b) x‖
        ≤ Csup * (2 * Real.pi) ^ k * Real.sqrt Cinv * (1 + B) := by
    intro a b l x
    have hcsq' : Work.Diff.STE.CSq k
        (Work.Diff.STE.fourierCoeff (fun y => Work.Diff.STE.flat.symInvC c a b y))
          ≤ Cinv * (1 + B) ^ 2 := by
      refine (hcsq a b).trans ?_
      nlinarith [hCinvnn, hCB]
    have h := Work.Diff.STE.flat.invJet_sup_pdVec_seriesFun_le (n := n) (s := k) hsob
      (d := Work.Diff.STE.fourierCoeff (fun y => Work.Diff.STE.flat.symInvC c a b y))
      (hdmom1 a b) hCsupnn hCsup' hCinvnn hB hcsq' 1 hsob1 l x
    rw [show Work.Diff.STE.seriesFun
          (Work.Diff.STE.fourierCoeff (fun y => Work.Diff.STE.flat.symInvC c a b y))
        = Work.Diff.STE.flat.symInvC c a b from
      funext (Work.Diff.STE.flat.seriesFun_fourierCoeff _ (hsmC a b) (hperC a b))] at h
    exact h
  -- the first-derivative bound for `symInvR` (real part of `symInvC`)
  have hpdr : ∀ (a b i : Fin n) (x : Fin n → ℝ),
      |Work.Diff.STE.pdR i (Work.Diff.STE.flat.symInvR c a b) x|
        ≤ Csup * (2 * Real.pi) ^ k * Real.sqrt Cinv * (1 + B) := by
    intro a b i x
    have hgd : Work.Diff.STE.pd i (Work.Diff.STE.flat.symInvC c a b) x
        = ((Work.Diff.STE.pdR i (Work.Diff.STE.flat.symInvR c a b) x : ℝ) : ℂ) :=
      show Work.Diff.STE.pd i (fun y => ((Work.Diff.STE.flat.symInvR c a b y : ℝ) : ℂ)) x
          = ((Work.Diff.STE.pdR i (Work.Diff.STE.flat.symInvR c a b) x : ℝ) : ℂ) from
        Work.Diff.STE.ga_pd_ofReal i (Work.Diff.STE.flat.symInvR c a b) x
          ((hsmR a b).differentiable (by simp) x)
    have hre : (Work.Diff.STE.pd i (Work.Diff.STE.flat.symInvC c a b) x).re
        = Work.Diff.STE.pdR i (Work.Diff.STE.flat.symInvR c a b) x := by
      rw [hgd, Complex.ofReal_re]
    calc |Work.Diff.STE.pdR i (Work.Diff.STE.flat.symInvR c a b) x|
        = |(Work.Diff.STE.pd i (Work.Diff.STE.flat.symInvC c a b) x).re| := by rw [hre]
      _ ≤ ‖Work.Diff.STE.pd i (Work.Diff.STE.flat.symInvC c a b) x‖ := Complex.abs_re_le_norm _
      _ = ‖Work.Diff.STE.pdVec 1 (fun _ : Fin 1 => i) (Work.Diff.STE.flat.symInvC c a b) x‖ := by
          rw [Work.Diff.STE.flat.invJetSymm_pdVec_one]
      _ ≤ Csup * (2 * Real.pi) ^ k * Real.sqrt Cinv * (1 + B) := hsup a b (fun _ => i) x
  -- Gårding's coercivity condition
  have hgard : ∀ (x : Fin n → ℝ) (ξ : Fin n → ℝ),
      lam / (((n : ℝ) * (Cs * (1 + B)) + 1) ^ 2) * ∑ i, (ξ i) ^ 2
        ≤ ∑ i, ∑ j, Work.Diff.STE.flat.symInvR c i j x * ξ i * ξ j := by
    intro x ξ
    have hsqrt : Real.sqrt (Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM c))
        ≤ B := by
      rw [← Real.sqrt_sq hB]
      exact Real.sqrt_le_sqrt hE
    have hab : ∀ i j : Fin n,
        |Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j| ≤ Cs * (1 + B) := by
      intro i j
      calc |Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j|
          = |(Work.Diff.STE.Flat.seriesFunM c x i j).re| := rfl
        _ ≤ ‖Work.Diff.STE.Flat.seriesFunM c x i j‖ := Complex.abs_re_le_norm _
        _ ≤ Cs * (1 + Real.sqrt (Work.Diff.STE.Flat.ENormSqFull k
              (Work.Diff.STE.Flat.seriesFunM c))) := hCs' N c hc i j x
        _ ≤ Cs * (1 + B) := mul_le_mul_of_nonneg_left (by linarith) hCs
    have hβ : 0 ≤ Cs * (1 + B) := by positivity
    have hdet : (Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x)).det ≠ 0 :=
      Work.Diff.STE.flat.det_ne_zero_of_elliptic (Work.Diff.STE.Flat.seriesFunM c x) hlam (hell x)
    have hkey := Work.Diff.STE.flat.inv_quadForm_lower (n := n)
      (A := Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x)) (β := Cs * (1 + B))
      hlam hβ hdet (fun v => hell x v) hab ξ
    simpa only [Work.Diff.STE.flat.symInvR_apply] using hkey
  exact ⟨hsmR, hsmC, hperR, hperC, hpdr, hgard⟩

end

end Work.Diff.STE.fill
