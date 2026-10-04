import Mathlib
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.inv_jet_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.STE.flat.inv_jet_bound_symm`

The principal part of the flat DeTurck operator multiplies the second derivatives `∂_a∂_b u` by
the inverse metric `G = (reMat (seriesFunM c ·))⁻¹`; by Clairaut's theorem only the *symmetric*
part `symInvR c a b = (G_{ab} + G_{ba})/2` contributes (`level_defs.lean`, `secOpFlat_eq_symInvR`).

This file transfers the Moser-type jet bounds of `inv_jet_bound` (which are stated for the
individual entries `G_{c'd'} = invEntryFun n c c' d'` of the inverse metric) to the symmetrised
combination.  Since `symInvC c a b = (2 : ℂ)⁻¹ • (G_{ab} + G_{ba})` as functions, all the bounds
follow from:

* the smoothness and `1`-periodicity of the individual entries (the argument already contained in
  the proof of `inv_jet_bound`, extracted here as `invJetSymm_invEntryFun_smooth`), and
* linearity of the iterated partial derivative operator `pdVec j l` on `C^∞` functions
  (`invJetSymm_pdVec_add`, `invJetSymm_pdVec_smul`), together with the elementary `L²` triangle
  estimate `invJetSymm_int_norm_sq_smul_add`.

The same constant `C` produced by `inv_jet_bound` works for all the symmetrised statements, and the
`pdR` bound is a consequence of the `j = 1` case of the `pdVec` sup bound via `ga_pd_ofReal`.
-/

namespace Work.Diff.STE.flat

open Work.Diff.STE
open Work.Diff.STE.Flat

set_option maxHeartbeats 1000000

section Aids

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `pdList` of a `C^∞` function is differentiable. -/
lemma invJetSymm_pdList_differentiable (l : List ι) {f : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Differentiable ℝ (pdList l f) := by
  have h1 : ContDiff ℝ ((l.length + 1 : ℕ) : ℕ∞) f := hf.of_le (by simp)
  exact (contDiff_pdList_of_contDiff l 1 f h1).differentiable (by simp)

/-- `pd` commutes with multiplication by a constant. -/
lemma invJetSymm_pd_smul (i : ι) (a : ℂ) {f : (ι → ℝ) → ℂ} (hf : Differentiable ℝ f) :
    pd i (a • f) = a • pd i f := by
  funext x
  have hfd : fderiv ℝ (fun y => a • f y) x = a • fderiv ℝ f x :=
    fderiv_fun_const_smul (hf x) a
  simp only [pd]
  show (fderiv ℝ (fun y => a • f y) x) (Pi.single i 1) = a • (fderiv ℝ f x (Pi.single i 1))
  rw [hfd, ContinuousLinearMap.smul_apply]

/-- `pdList` is additive on `C^∞` functions. -/
lemma invJetSymm_pdList_add (l : List ι) {f g : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    pdList l (f + g) = pdList l f + pdList l g := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      have h1 : pdList (i :: l) (f + g) = pd i (pdList l (f + g)) := by
        simp only [pdList, List.foldr_cons]
      have h2 : pdList (i :: l) f = pd i (pdList l f) := by
        simp only [pdList, List.foldr_cons]
      have h3 : pdList (i :: l) g = pd i (pdList l g) := by
        simp only [pdList, List.foldr_cons]
      rw [h1, ih, h2, h3, pd_add_fn i (pdList l f) (pdList l g)
        (invJetSymm_pdList_differentiable l hf) (invJetSymm_pdList_differentiable l hg)]

/-- `pdList` is homogeneous in the function. -/
lemma invJetSymm_pdList_smul (l : List ι) (a : ℂ) {f : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : pdList l (a • f) = a • pdList l f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      have h1 : pdList (i :: l) (a • f) = pd i (pdList l (a • f)) := by
        simp only [pdList, List.foldr_cons]
      have h2 : pdList (i :: l) f = pd i (pdList l f) := by
        simp only [pdList, List.foldr_cons]
      rw [h1, ih, h2, invJetSymm_pd_smul i a (invJetSymm_pdList_differentiable l hf)]

/-- `pdVec` is additive on `C^∞` functions. -/
lemma invJetSymm_pdVec_add (j : ℕ) (l : Fin j → ι) {f g : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    pdVec j l (f + g) = pdVec j l f + pdVec j l g := by
  simpa only [pdVec] using invJetSymm_pdList_add (List.ofFn l) hf hg

/-- `pdVec` is homogeneous in the function. -/
lemma invJetSymm_pdVec_smul (j : ℕ) (l : Fin j → ι) (a : ℂ) {f : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : pdVec j l (a • f) = a • pdVec j l f := by
  simpa only [pdVec] using invJetSymm_pdList_smul (List.ofFn l) a hf

/-- The `1`-fold iterated partial derivative is the partial derivative. -/
lemma invJetSymm_pdVec_one (i : ι) (f : (ι → ℝ) → ℂ) :
    pdVec 1 (fun _ : Fin 1 => i) f = pd i f := by
  simp [pdVec, pdList]

/-- **`L²` bound for a scalar multiple of a sum.**  If two continuous functions have
`L²`-norm-squared at most `A` on the unit cube, then so does any constant multiple of their sum,
up to the factor `4‖c‖²`. -/
lemma invJetSymm_int_norm_sq_smul_add (c : ℂ) (U V : (ι → ℝ) → ℂ) (hU : Continuous U)
    (hV : Continuous V) (A : ℝ)
    (hU' : ∫ x in unitCube, ‖U x‖ ^ 2 ≤ A) (hV' : ∫ x in unitCube, ‖V x‖ ^ 2 ≤ A) :
    ∫ x in unitCube, ‖(c • (U + V)) x‖ ^ 2 ≤ 4 * A * ‖c‖ ^ 2 := by
  have hpt : ∀ x : ι → ℝ,
      ‖(c • (U + V)) x‖ ^ 2 ≤ ‖c‖ ^ 2 * (2 * ‖U x‖ ^ 2 + 2 * ‖V x‖ ^ 2) := by
    intro x
    have hx : (c • (U + V)) x = c * (U x + V x) := by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [hx, norm_mul, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have h1 : ‖U x + V x‖ ^ 2 ≤ (‖U x‖ + ‖V x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    have h2 : (‖U x‖ + ‖V x‖) ^ 2 ≤ 2 * ‖U x‖ ^ 2 + 2 * ‖V x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖U x‖ - ‖V x‖)]
    exact h1.trans h2
  have hInt1 : MeasureTheory.Integrable (fun x : ι → ℝ => ‖(c • (U + V)) x‖ ^ 2)
      (MeasureTheory.volume.restrict unitCube) :=
    el_integrableOn_unitCube_of_continuous_real
      (((continuous_const.smul (hU.add hV)).norm).pow 2)
  have hInt2 : MeasureTheory.Integrable
      (fun x : ι → ℝ => ‖c‖ ^ 2 * (2 * ‖U x‖ ^ 2 + 2 * ‖V x‖ ^ 2))
      (MeasureTheory.volume.restrict unitCube) :=
    el_integrableOn_unitCube_of_continuous_real
      (continuous_const.mul ((continuous_const.mul (hU.norm.pow 2)).add
        (continuous_const.mul (hV.norm.pow 2))))
  have hmono := MeasureTheory.integral_mono_ae hInt1 hInt2 (Filter.Eventually.of_forall hpt)
  have hsplit : ∫ x in unitCube, ‖c‖ ^ 2 * (2 * ‖U x‖ ^ 2 + 2 * ‖V x‖ ^ 2)
      = ‖c‖ ^ 2 * (2 * (∫ x in unitCube, ‖U x‖ ^ 2)
          + 2 * (∫ x in unitCube, ‖V x‖ ^ 2)) := by
    have hI1 : MeasureTheory.Integrable (fun x : ι → ℝ => 2 * ‖U x‖ ^ 2)
        (MeasureTheory.volume.restrict unitCube) :=
      el_integrableOn_unitCube_of_continuous_real (continuous_const.mul (hU.norm.pow 2))
    have hI2 : MeasureTheory.Integrable (fun x : ι → ℝ => 2 * ‖V x‖ ^ 2)
        (MeasureTheory.volume.restrict unitCube) :=
      el_integrableOn_unitCube_of_continuous_real (continuous_const.mul (hV.norm.pow 2))
    rw [MeasureTheory.integral_const_mul (r := ‖c‖ ^ 2)
      (f := fun x : ι → ℝ => 2 * ‖U x‖ ^ 2 + 2 * ‖V x‖ ^ 2)]
    rw [MeasureTheory.integral_add (f := fun x : ι → ℝ => 2 * ‖U x‖ ^ 2)
      (g := fun x : ι → ℝ => 2 * ‖V x‖ ^ 2) hI1 hI2]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  calc ∫ x in unitCube, ‖(c • (U + V)) x‖ ^ 2
      ≤ ∫ x in unitCube, ‖c‖ ^ 2 * (2 * ‖U x‖ ^ 2 + 2 * ‖V x‖ ^ 2) := hmono
    _ = ‖c‖ ^ 2 * (2 * (∫ x in unitCube, ‖U x‖ ^ 2)
          + 2 * (∫ x in unitCube, ‖V x‖ ^ 2)) := hsplit
    _ ≤ ‖c‖ ^ 2 * (2 * A + 2 * A) :=
        mul_le_mul_of_nonneg_left (by linarith [hU', hV']) (sq_nonneg _)
    _ = 4 * A * ‖c‖ ^ 2 := by ring

end Aids

section Entry

/-- **Smoothness and periodicity of the inverse-metric entries.**  Under the box-support, energy
and uniform ellipticity hypotheses, each entry `invEntryFun n c c' d'` of the inverse of the real
part of the matrix series is smooth (on the whole torus, because ellipticity is assumed
everywhere) and `1`-periodic.  This is the pair of facts `hg`/`hgper` used inside the proof of
`inv_jet_bound`. -/
lemma invJetSymm_invEntryFun_smooth {n s : ℕ} {lam Bs : ℝ} (hBs : 0 ≤ Bs)
    (hσs : sob n ≤ s) (hlam : 0 < lam)
    (N : ℕ) (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0)
    (hen : ENormSqFull s (seriesFunM c) ≤ Bs ^ 2)
    (hell : ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMat (seriesFunM c x) i j * v i * v j)
    (c' d' : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (invEntryFun n c c' d') ∧ Periodic1 (invEntryFun n c c' d') := by
  obtain ⟨Kρ, hKρ, hKρ'⟩ := invJet_entryVec_sup_le (n := n) (s := s) (Bs := Bs) hBs hσs
  have hWmem : ∀ x : Fin n → ℝ, entryVec n c x ∈ invElliptic n lam (Kρ * (1 + Bs)) := by
    intro x
    refine ⟨fun i => ?_, ?_⟩
    · simpa only [entryVec_apply] using hKρ' N c hc hen x i
    · intro v
      rw [reMatZ_entryVec]
      exact hell x v
  refine ⟨?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    exact ((invJet_contDiffOn_invPhi c' d').contDiffAt
      (invJet_isOpen_invNonsing.mem_nhds
        (invJet_invElliptic_subset_invNonsing hlam (hWmem x)))).comp x
      (invJet_contDiff_invCvec_series c hc).contDiffAt
  · intro i x
    have h : entryVec n c (x + Pi.single i 1) = entryVec n c x :=
      invJet_periodic1_invCvec_series c i x
    simp only [invEntryFun_apply]
    rw [h]

end Entry

theorem inv_jet_bound_symm {n s : ℕ} (hn : 1 ≤ n) (hs : n + 5 ≤ s)
    (lam : ℝ) (hlam : 0 < lam) (Bs : ℝ) (hBs : 0 ≤ Bs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k : Fin n → ℤ, k ∉ Work.Diff.STE.Flat.box n N → c k = 0) →
      Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      (∀ (a b : Fin n), ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.flat.symInvC c a b)) ∧
      (∀ (a b : Fin n), Work.Diff.STE.Periodic1 (Work.Diff.STE.flat.symInvC c a b)) ∧
      (∀ (a b : Fin n) (j : ℕ) (hj : j + Work.Diff.STE.flat.sob n ≤ s) (l : Fin j → Fin n)
          (x : Fin n → ℝ),
        ‖Work.Diff.STE.pdVec j l (Work.Diff.STE.flat.symInvC c a b) x‖ ≤ C * (1 + Bs)) ∧
      (∀ (a b : Fin n) (j : ℕ) (hj : j ≤ s + 1) (l : Fin j → Fin n),
        ∫ x in Work.Diff.STE.unitCube (ι := Fin n),
          ‖Work.Diff.STE.pdVec j l (Work.Diff.STE.flat.symInvC c a b) x‖ ^ 2
          ≤ C * (1 + Bs) ^ 2
            * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1) (Work.Diff.STE.Flat.seriesFunM c))) ∧
      (∀ (a b i : Fin n) (x : Fin n → ℝ),
        |Work.Diff.STE.pdR i (Work.Diff.STE.flat.symInvR c a b) x| ≤ C * (1 + Bs)) := by
  classical
  obtain ⟨C0, hC0, hC0'⟩ := inv_jet_bound hn hs lam hlam Bs hBs
  refine ⟨C0, hC0, ?_⟩
  intro N c hc hen hell
  have hσs : sob n ≤ s := by have h := two_sob_le n; omega
  have h1s : 1 + sob n ≤ s := by
    have h : sob n ≤ n + 1 := by simp only [sob]; omega
    omega
  have hnorm2 : ‖((2 : ℂ)⁻¹)‖ = (2 : ℝ)⁻¹ := by norm_num
  have hnorm2sq : ‖((2 : ℂ)⁻¹)‖ ^ 2 = (4 : ℝ)⁻¹ := by norm_num
  -- the individual inverse-metric entries, and their identification
  have hEq : ∀ c' d' : Fin n,
      invEntryFun n c c' d' = fun y : Fin n → ℝ => (((reMat (seriesFunM c y))⁻¹) c' d' : ℂ) :=
    fun c' d' => invEntryFun_eq n c c' d'
  have hE : ∀ c' d' : Fin n, ContDiff ℝ (⊤ : ℕ∞) (invEntryFun n c c' d') ∧
      Periodic1 (invEntryFun n c c' d') :=
    fun c' d' => invJetSymm_invEntryFun_smooth hBs hσs hlam N c hc hen hell c' d'
  have hdE : ∀ c' d' : Fin n, Differentiable ℝ (invEntryFun n c c' d') :=
    fun c' d' => (hE c' d').1.differentiable (by simp)
  -- the symmetrised inverse metric is a scalar multiple of a sum of two entries
  have hsym : ∀ a b : Fin n, symInvC c a b
      = (2 : ℂ)⁻¹ • (invEntryFun n c a b + invEntryFun n c b a) := by
    intro a b
    funext x
    rw [invEntryFun_eq, invEntryFun_eq]
    simp only [symInvC_apply, symInvR_apply, Pi.smul_apply, Pi.add_apply]
    push_cast
    ring
  have hlin : ∀ (a b : Fin n) (j : ℕ) (l : Fin j → Fin n),
      pdVec j l (symInvC c a b)
        = (2 : ℂ)⁻¹ • (pdVec j l (invEntryFun n c a b) + pdVec j l (invEntryFun n c b a)) := by
    intro a b j l
    rw [hsym a b]
    have h1 : pdVec j l (invEntryFun n c a b + invEntryFun n c b a)
        = pdVec j l (invEntryFun n c a b) + pdVec j l (invEntryFun n c b a) :=
      invJetSymm_pdVec_add j l (hE a b).1 (hE b a).1
    have h2 : pdVec j l ((2 : ℂ)⁻¹ • (invEntryFun n c a b + invEntryFun n c b a))
        = (2 : ℂ)⁻¹ • pdVec j l (invEntryFun n c a b + invEntryFun n c b a) :=
      invJetSymm_pdVec_smul j l (2 : ℂ)⁻¹ ((hE a b).1.add (hE b a).1)
    rw [h2, h1]
  have hsmooth : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (symInvC c a b) := by
    intro a b
    rw [hsym a b]
    exact ((hE a b).1.add (hE b a).1).const_smul (2 : ℂ)⁻¹
  have hper : ∀ a b : Fin n, Periodic1 (symInvC c a b) := by
    intro a b
    rw [hsym a b]
    intro i x
    simp only [Pi.smul_apply, Pi.add_apply]
    rw [(hE a b).2 i x, (hE b a).2 i x]
  have hsup : ∀ (a b : Fin n) (j : ℕ) (hj : j + sob n ≤ s) (l : Fin j → Fin n)
      (x : Fin n → ℝ),
      ‖pdVec j l (symInvC c a b) x‖ ≤ C0 * (1 + Bs) := by
    intro a b j hj l x
    have hU : ‖pdVec j l (invEntryFun n c a b) x‖ ≤ C0 * (1 + Bs) := by
      rw [hEq a b]
      exact (hC0' N c hc hen hell).1 a b j hj l x
    have hV : ‖pdVec j l (invEntryFun n c b a) x‖ ≤ C0 * (1 + Bs) := by
      rw [hEq b a]
      exact (hC0' N c hc hen hell).1 b a j hj l x
    have hsum : ‖pdVec j l (invEntryFun n c a b) x + pdVec j l (invEntryFun n c b a) x‖
        ≤ C0 * (1 + Bs) + C0 * (1 + Bs) := (norm_add_le _ _).trans (add_le_add hU hV)
    have hpx : ((2 : ℂ)⁻¹
          • (pdVec j l (invEntryFun n c a b) + pdVec j l (invEntryFun n c b a))) x
        = (2 : ℂ)⁻¹ * (pdVec j l (invEntryFun n c a b) x
            + pdVec j l (invEntryFun n c b a) x) := by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [hlin a b j l, hpx, norm_mul, hnorm2]
    have h2 := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    linarith [h2]
  have hl2 : ∀ (a b : Fin n) (j : ℕ) (hj : j ≤ s + 1) (l : Fin j → Fin n),
      ∫ x in unitCube (ι := Fin n), ‖pdVec j l (symInvC c a b) x‖ ^ 2
        ≤ C0 * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
    intro a b j hj l
    have hcontA : Continuous (pdVec j l (invEntryFun n c a b)) :=
      continuous_pdVec j l _ ((hE a b).1.of_le (by simp))
    have hcontB : Continuous (pdVec j l (invEntryFun n c b a)) :=
      continuous_pdVec j l _ ((hE b a).1.of_le (by simp))
    rcases lt_or_eq_of_le hj with hlt | heq
    · have hU : ∫ x in unitCube (ι := Fin n), ‖pdVec j l (invEntryFun n c a b) x‖ ^ 2
          ≤ C0 * (1 + Bs) ^ 2 := by
        rw [hEq a b]
        exact (hC0' N c hc hen hell).2.1 a b j (Nat.lt_succ_iff.mp hlt) l
      have hV : ∫ x in unitCube (ι := Fin n), ‖pdVec j l (invEntryFun n c b a) x‖ ^ 2
          ≤ C0 * (1 + Bs) ^ 2 := by
        rw [hEq b a]
        exact (hC0' N c hc hen hell).2.1 b a j (Nat.lt_succ_iff.mp hlt) l
      have hm := invJetSymm_int_norm_sq_smul_add (2 : ℂ)⁻¹ (pdVec j l (invEntryFun n c a b))
        (pdVec j l (invEntryFun n c b a)) hcontA hcontB (C0 * (1 + Bs) ^ 2) hU hV
      calc ∫ x in unitCube (ι := Fin n), ‖pdVec j l (symInvC c a b) x‖ ^ 2
          = ∫ x in unitCube (ι := Fin n),
              ‖((2 : ℂ)⁻¹ • (pdVec j l (invEntryFun n c a b)
                + pdVec j l (invEntryFun n c b a))) x‖ ^ 2 := by rw [hlin a b j l]
        _ ≤ 4 * (C0 * (1 + Bs) ^ 2) * ‖(2 : ℂ)⁻¹‖ ^ 2 := hm
        _ = C0 * (1 + Bs) ^ 2 := by rw [hnorm2sq]; ring
        _ ≤ C0 * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
            have h1 : (1 : ℝ) ≤ 1 + ENormSqFull (s + 1) (seriesFunM c) := by
              have := ENormSqFull_nonneg (s + 1) (seriesFunM c); linarith
            have h2 : (0 : ℝ) ≤ C0 * (1 + Bs) ^ 2 := mul_nonneg hC0 (sq_nonneg _)
            calc C0 * (1 + Bs) ^ 2 = (C0 * (1 + Bs) ^ 2) * 1 := by ring
              _ ≤ (C0 * (1 + Bs) ^ 2) * (1 + ENormSqFull (s + 1) (seriesFunM c)) :=
                  mul_le_mul_of_nonneg_left h1 h2
    · subst heq
      have hU : ∫ x in unitCube (ι := Fin n),
            ‖pdVec (s + 1) l (invEntryFun n c a b) x‖ ^ 2
          ≤ C0 * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
        rw [hEq a b]
        exact (hC0' N c hc hen hell).2.2 a b l
      have hV : ∫ x in unitCube (ι := Fin n),
            ‖pdVec (s + 1) l (invEntryFun n c b a) x‖ ^ 2
          ≤ C0 * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
        rw [hEq b a]
        exact (hC0' N c hc hen hell).2.2 b a l
      have hm := invJetSymm_int_norm_sq_smul_add (2 : ℂ)⁻¹ (pdVec (s + 1) l (invEntryFun n c a b))
        (pdVec (s + 1) l (invEntryFun n c b a)) hcontA hcontB
        (C0 * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c))) hU hV
      calc ∫ x in unitCube (ι := Fin n), ‖pdVec (s + 1) l (symInvC c a b) x‖ ^ 2
          = ∫ x in unitCube (ι := Fin n),
              ‖((2 : ℂ)⁻¹ • (pdVec (s + 1) l (invEntryFun n c a b)
                + pdVec (s + 1) l (invEntryFun n c b a))) x‖ ^ 2 := by
            rw [hlin a b (s + 1) l]
        _ ≤ 4 * (C0 * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c)))
              * ‖(2 : ℂ)⁻¹‖ ^ 2 := hm
        _ = C0 * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
            rw [hnorm2sq]; ring
  have hpdr : ∀ (a b i : Fin n) (x : Fin n → ℝ),
      |pdR i (symInvR c a b) x| ≤ C0 * (1 + Bs) := by
    intro a b i x
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (symInvR c a b) := by
      have h := Complex.reCLM.contDiff.comp (hsmooth a b)
      simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re, symInvC] using h
    have hgd : pd i (symInvC c a b) x = (pdR i (symInvR c a b) x : ℂ) :=
      show pd i (fun y : Fin n → ℝ => ((symInvR c a b y : ℝ) : ℂ)) x
          = (pdR i (symInvR c a b) x : ℂ) from
        ga_pd_ofReal i (symInvR c a b) x (hsm.differentiable (by simp) x)
    have hre : (pd i (symInvC c a b) x).re = pdR i (symInvR c a b) x := by
      rw [hgd, Complex.ofReal_re]
    calc |pdR i (symInvR c a b) x| = |(pd i (symInvC c a b) x).re| := by rw [hre]
      _ ≤ ‖pd i (symInvC c a b) x‖ := Complex.abs_re_le_norm _
      _ = ‖pdVec 1 (fun _ : Fin 1 => i) (symInvC c a b) x‖ := by
          rw [invJetSymm_pdVec_one]
      _ ≤ C0 * (1 + Bs) := hsup a b 1 h1s (fun _ => i) x
  exact ⟨hsmooth, hper, hsup, hl2, hpdr⟩

end Work.Diff.STE.flat
