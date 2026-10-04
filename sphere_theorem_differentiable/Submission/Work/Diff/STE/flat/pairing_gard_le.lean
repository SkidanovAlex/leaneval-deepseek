import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.inv_jet_bound_symm
import Submission.Work.Diff.STE.garding_vec_direct
import Submission.Work.Diff.STE.ga_const_bound
import Submission.Work.Diff.STE.GardingConst
import Submission.Work.Diff.STE.CSq_comp_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.STE.flat.pairing_gard_le`

The Gårding dissipation of the level-`(s+1)` pairing of the flat DeTurck system:

`Σ_{ij} Σ_l ⟨ (reMat A)⁻¹ · ∂∂(∂^l u_{ij}), ∂^l u_{ij} ⟩ ≤ -(lam'/2) · ENormSqM (s+2) u
                                                          + C · ENormSqM (s+1) u`,

with a constant `C` that is *uniform* in the Galerkin order `N` and the coefficient family `c`
(because the principal part is the inverse metric, whose derivative is controlled by the level-`s`
energy bound `Bs`).

The ingredients are:

* `Work.Diff.STE.flat.inv_jet_bound_symm` — smoothness, `1`-periodicity and the *uniform*
  first-derivative bound `|∂ (symInvR c a b)| ≤ C₀ (1 + Bs)` of the symmetrised inverse metric
  (Moser's inverse-function bound), together with the ellipticity hypothesis of the statement;
* `Work.Diff.STE.garding_vec_const` (below) — the `H^k` Gårding estimate with the *explicit*
  constant `gardingConst`, which is what makes the resultant `C` uniform;
* `ENormSq_succ_eq` to identify the two accumulated energies with `ENormSqM (s+2)` and
  `ENormSqM (s+1)`.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE
open Work.Diff.STE.Flat

noncomputable section

open MeasureTheory BigOperators

/-- **The multi-index Gårding estimate with the explicit constant.**  The `H^k` version of
`Work.Diff.STE.ga_const_bound`: the accumulated quadratic form of the elliptic operator
`u ↦ Σ_{cd} A_{cd} ∂_c∂_d u` is bounded by `-(lam/2)·ENormSq (k+1) u` plus the explicit constant
`gardingConst (card ι) lam K₁` times `ENormSq k u`.  Because the constant is explicit, it is
uniform in the coefficient matrix, which is what the `pairing_gard_le` assembly needs. -/
lemma garding_vec_const {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∀ (lam : ℝ) (hlam : 0 < lam) (K₁ : ℝ)
      (A : ι → ι → (ι → ℝ) → ℝ)
      (hA : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d))
      (hAper : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
      (hsym : ∀ c d x, A c d x = A d c x)
      (hpos : ∀ x (ξ : ι → ℝ),
        lam * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d x * ξ c * ξ d)
      (hK₁ : ∀ c d i x, |Work.Diff.STE.pdR i (A c d) x| ≤ K₁),
      ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (k + 2) u → Work.Diff.STE.Periodic1 u →
        (∑ l : Fin k → ι, Work.Diff.STE.L2re
            (fun x => ∑ c, ∑ d, A c d x
              * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) x)
            (Work.Diff.STE.pdVec k l u))
          ≤ -((lam / 2) * Work.Diff.STE.ENormSq (k + 1) u)
            + Work.Diff.STE.gardingConst (Fintype.card ι) lam K₁
              * Work.Diff.STE.ENormSq k u := by
  intro lam hlam K₁ A hA hAper hsym hpos hK₁ u hu hup
  -- The scalar explicit-constant Gårding estimate applied to each `k`-fold derivative
  -- `∂^l u`, with the same constant for every `l`.
  have hterm : ∀ l : Fin k → ι,
      Work.Diff.STE.L2re
          (fun x => ∑ c, ∑ d, A c d x
            * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) x)
          (Work.Diff.STE.pdVec k l u)
        ≤ -((lam / 2) * ∑ i, ∫ x in Work.Diff.STE.unitCube (ι := ι),
              ‖Work.Diff.STE.pd i (Work.Diff.STE.pdVec k l u) x‖ ^ 2)
          + Work.Diff.STE.gardingConst (Fintype.card ι) lam K₁
            * ∫ x in Work.Diff.STE.unitCube (ι := ι),
                ‖Work.Diff.STE.pdVec k l u x‖ ^ 2 := by
    intro l
    obtain ⟨hc, hp⟩ :=
      Work.Diff.STE.pdVec_contDiff_periodic k (k + 2) (Nat.le_add_right k 2) l u hu hup
    rw [Work.Diff.STE.withTop_natCast_sub] at hc
    exact Work.Diff.STE.ga_const_bound A hA hAper hsym lam hlam hpos K₁ hK₁
      (Work.Diff.STE.pdVec k l u) (by simpa [Nat.add_sub_cancel] using hc) hp
  refine le_trans (Finset.sum_le_sum (fun l _ => hterm l)) ?_
  -- The sum of the lower order terms is `ENormSq (k+1)`, the sum of the `L²` terms is `ENormSq k`.
  have hS : (∑ l : Fin k → ι, ∑ i : ι, ∫ x in Work.Diff.STE.unitCube (ι := ι),
        ‖Work.Diff.STE.pd i (Work.Diff.STE.pdVec k l u) x‖ ^ 2)
      = Work.Diff.STE.ENormSq (k + 1) u :=
    (Work.Diff.STE.ENormSq_succ_eq k u).symm
  have hT : (∑ l : Fin k → ι, ∫ x in Work.Diff.STE.unitCube (ι := ι),
        ‖Work.Diff.STE.pdVec k l u x‖ ^ 2) = Work.Diff.STE.ENormSq k u := rfl
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hS, hT]

theorem pairing_gard_le {n s : ℕ} (hn : 1 ≤ n) (hs : n + 5 ≤ s)
    (lam : ℝ) (hlam : 0 < lam) (Bs : ℝ) (hBs : 0 ≤ Bs)
    (lam' : ℝ) (hlam' : 0 < lam') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      (∀ (x : Fin n → ℝ) (ξ : Fin n → ℝ),
        lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.flat.symInvR c i j x * ξ i * ξ j) →
      (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin (s + 1) → Fin n,
        Work.Diff.STE.L2re (fun x => ∑ a, ∑ b, Work.Diff.STE.flat.symInvC c a b x
            * Work.Diff.STE.pd a (Work.Diff.STE.pd b (Work.Diff.STE.pdVec (s + 1) l
                (fun x => Work.Diff.STE.Flat.seriesFunM c x i j))) x)
          (Work.Diff.STE.pdVec (s + 1) l (fun x => Work.Diff.STE.Flat.seriesFunM c x i j)))
        ≤ -((lam' / 2) * Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c))
          + C * Work.Diff.STE.Flat.ENormSqM (s + 1) (Work.Diff.STE.Flat.seriesFunM c) := by
  -- The uniform first-derivative (Moser) bound of the symmetrised inverse metric.
  obtain ⟨C0, hC0, hC0'⟩ := inv_jet_bound_symm hn hs lam hlam Bs hBs
  refine ⟨Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' (C0 * (1 + Bs)),
    Work.Diff.STE.gardingConst_nonneg hlam', ?_⟩
  intro N c hc hen hell hinv
  obtain ⟨hsm, hper, _hsup, _hl2, hpdr⟩ := hC0' N c hc hen hell
  -- The hypotheses of the explicit-constant Gårding estimate for `A = symInvR c`.
  have hA : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => symInvR c a b y) := by
    intro a b
    have h := Complex.reCLM.contDiff.comp (hsm a b)
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re, symInvC] using h
  have hAper : ∀ a b : Fin n, Work.Diff.STE.Periodic1
      (fun y : Fin n → ℝ => symInvR c a b y) := by
    intro a b i x
    have h := hper a b i x
    simp only [symInvC_apply] at h
    exact Complex.ofReal_injective h
  have hsym : ∀ a b (y : Fin n → ℝ), symInvR c a b y = symInvR c b a y :=
    fun a b y => symInvR_symm_apply c a b y
  have hpos : ∀ (x : Fin n → ℝ) (ξ : Fin n → ℝ),
      lam' * ∑ i, (ξ i) ^ 2
        ≤ ∑ a, ∑ b, (fun a b y => symInvR c a b y) a b x * ξ a * ξ b := by
    intro x ξ
    simpa using hinv x ξ
  have hK₁ : ∀ a b i (x : Fin n → ℝ),
      |Work.Diff.STE.pdR i ((fun a b y => symInvR c a b y) a b) x| ≤ C0 * (1 + Bs) :=
    fun a b i x => hpdr a b i x
  have hvec := garding_vec_const (ι := Fin n) (s + 1)
    lam' hlam' (C0 * (1 + Bs)) (fun a b y => symInvR c a b y) hA hAper hsym hpos hK₁
  -- The per-entry bound, in the shape of the statement.
  have hper_entry : ∀ i j : Fin n,
      (∑ l : Fin (s + 1) → Fin n, Work.Diff.STE.L2re
          (fun x => ∑ a, ∑ b, symInvC c a b x
            * Work.Diff.STE.pd a (Work.Diff.STE.pd b (Work.Diff.STE.pdVec (s + 1) l
                (fun x => seriesFunM c x i j))) x)
          (Work.Diff.STE.pdVec (s + 1) l (fun x => seriesFunM c x i j)))
        ≤ -((lam' / 2) * Work.Diff.STE.ENormSq (s + 2)
              (fun y => seriesFunM c y i j))
          + Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' (C0 * (1 + Bs))
            * Work.Diff.STE.ENormSq (s + 1) (fun y => seriesFunM c y i j) := by
    intro i j
    have hu : ContDiff ℝ ((s + 1) + 2) (fun y : Fin n → ℝ => seriesFunM c y i j) := by
      have h := Work.Diff.STE.contDiff_seriesFun (c := fun k : Fin n → ℤ => c k i j)
        (fun M => summable_moment_box c hc i j M)
      refine h.of_le ?_
      exact WithTop.coe_le_coe.mpr (le_top : (((s + 1) + 2 : ℕ) : ℕ∞) ≤ ⊤)
    have hp : Work.Diff.STE.Periodic1 (fun y : Fin n → ℝ => seriesFunM c y i j) := by
      have h := Work.Diff.STE.periodic_seriesFun (fun k : Fin n → ℤ => c k i j)
      simpa only [seriesFunM_apply] using h
    have hthis := hvec (fun y : Fin n → ℝ => seriesFunM c y i j) hu hp
    simpa only [symInvC_apply] using hthis
  refine le_trans (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hper_entry i j))) ?_
  -- Identify the accumulated bounds with `ENormSqM`.
  have hsum : (∑ i : Fin n, ∑ j : Fin n,
        (-((lam' / 2) * Work.Diff.STE.ENormSq (s + 2) (fun y => seriesFunM c y i j))
          + Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' (C0 * (1 + Bs))
            * Work.Diff.STE.ENormSq (s + 1) (fun y => seriesFunM c y i j)))
      = -((lam' / 2) * ENormSqM (s + 2) (seriesFunM c))
        + Work.Diff.STE.gardingConst (Fintype.card (Fin n)) lam' (C0 * (1 + Bs))
          * ENormSqM (s + 1) (seriesFunM c) := by
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ENormSqM]
  exact hsum.le

end

end Work.Diff.STE.flat
