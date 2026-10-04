import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.garding_estimate_vec
import Submission.Work.Diff.STE.CSq_interpolation
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.garding_vec_direct
import Submission.Work.Diff.STE.ENormSq_succ_eq
import Submission.Work.Diff.STE.continuous_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The energy inequality with lower order terms

`Work.Diff.STE.energy_le_of_coeff_bounds` is the `Hᵏ` coercivity estimate for the linear
operator

  `u ↦ Σ_{c,d} A_{cd} ∂_c∂_d u + Σ_a B_a ∂_a u + C₀ u`

on the flat torus (design note `DESIGN.md`, Layer A9 / D2), in the presence of a bounded
first-order and a bounded zeroth-order perturbation: for a smooth `1`-periodic `u`,

  `Σ_l ⟨L (∂^l u), ∂^l u⟩ ≤ -(λ/8)‖u‖²_{k+1} + C ‖u‖²_k`.

The proof is an assembly of three pieces, all of them already available in the workspace:

* the second-order (principal) part is the multi-index Gårding estimate in its *direct* form
  `Work.Diff.STE.garding_vec_direct`, which gives `-(λ/2)‖u‖²_{k+1} + C₁‖u‖²_k`;
* the first-order part is absorbed by a Young inequality with a small parameter `η`,
  `η = λ / (8 (max KB 0 + 1))`, giving `(λ/8)‖u‖²_{k+1} + C₂‖u‖²_k` — this is
  `elcb_first_order_le` below, proved from the pointwise AM–GM estimate
  `Work.Diff.STE.cm_term_bound`;
* the zeroth-order part is bounded by `max KC 0 · ‖u‖²_k` — `elcb_zero_order_le` below.

The splitting of `L2re` in its first argument is `Work.Diff.STE.cm_L2re_add`.  The remaining
`-(λ/2) + λ/8 + λ/8 = -λ/4 ≤ -λ/8` slack is absorbed using `0 ≤ ENormSq (k+1) u`.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary helpers -/

/-- A sum of a constant (in the index) real number: `∑_{a} c * Y = card · (c * Y)`. -/
lemma elcb_sum_const_mul {α : Type*} [Fintype α] (c Y : ℝ) :
    (∑ _ : α, c * Y) = (Fintype.card α : ℝ) * (c * Y) := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- `∂^l u` is `C²` when `u` is `C^{k+2}`. -/
lemma elcb_contDiff_pdVec (k : ℕ) {u : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (k + 2) u)
    (l : Fin k → ι) : ContDiff ℝ 2 (pdVec k l u) := by
  have h := contDiff_pdList_of_contDiff (List.ofFn l) 2 u (by
    rw [List.length_ofFn]
    exact hu)
  simpa [pdVec] using h

/-- `∂_c ∂_d ∂^l u` is continuous when `u` is `C^{k+2}`. -/
lemma elcb_continuous_pd_pdVec (k : ℕ) {u : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (k + 2) u)
    (l : Fin k → ι) (c d : ι) : Continuous (fun x => pd c (pd d (pdVec k l u)) x) := by
  have h2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (pdVec k l u) := elcb_contDiff_pdVec k hu l
  have h1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (pd d (pdVec k l u)) :=
    contDiff_pd_of_contDiff d (n := 2) (m := 1) h2 (le_refl 2)
  have h0 : ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞) (pd c (pd d (pdVec k l u))) :=
    contDiff_pd_of_contDiff c (n := 1) (m := 0) h1 (le_refl 1)
  simpa using h0.continuous

/-- `∂_a ∂^l u` is continuous when `u` is `C^{k+2}`. -/
lemma elcb_continuous_pd_pdVec' (k : ℕ) {u : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (k + 2) u)
    (l : Fin k → ι) (a : ι) : Continuous (pd a (pdVec k l u)) := by
  have h2 : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (pdVec k l u) := elcb_contDiff_pdVec k hu l
  have h1 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (pd a (pdVec k l u)) :=
    contDiff_pd_of_contDiff a (n := 2) (m := 1) h2 (le_refl 2)
  exact h1.continuous

/-! ## The zeroth-order part -/

/-- **Zeroth-order term.**  For a bounded continuous coefficient `C0` with `‖C0 x‖ ≤ KC`,
`KC ≥ 0`, the `L²` pairing `Σ_l ⟨C0 · ∂^l u, ∂^l u⟩` is bounded by `KC ‖u‖²_k`. -/
lemma elcb_zero_order_le (k : ℕ) (C0 : (ι → ℝ) → ℂ) (KC : ℝ) (hKC : 0 ≤ KC)
    (hC0s : ContDiff ℝ 0 C0) (hC0 : ∀ x, ‖C0 x‖ ≤ KC) :
    ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (k + 2) u →
      (∑ l : Fin k → ι, L2re (fun x => C0 x * pdVec k l u x) (pdVec k l u))
        ≤ KC * ENormSq k u := by
  intro u hu
  have hterm : ∀ l : Fin k → ι,
      L2re (fun x => C0 x * pdVec k l u x) (pdVec k l u)
        ≤ KC * (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) := by
    intro l
    have hgc : Continuous (pdVec k l u) := (elcb_contDiff_pdVec k hu l).continuous
    have hb := cm_term_bound KC (1 / 2) hKC (by norm_num) C0 (pdVec k l u) (pdVec k l u)
      hC0s.continuous hgc hgc hC0
    have h2 : KC * (1 / 2) * (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2)
        + (KC / (4 * (1 / 2))) * (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2)
        = KC * (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) := by ring
    exact (le_abs_self _).trans (hb.trans (le_of_eq h2))
  calc (∑ l : Fin k → ι, L2re (fun x => C0 x * pdVec k l u x) (pdVec k l u))
      ≤ ∑ l : Fin k → ι, KC * (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) :=
        Finset.sum_le_sum (fun l _ => hterm l)
    _ = KC * ENormSq k u :=
        (Finset.mul_sum Finset.univ
          (fun l : Fin k → ι => ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) KC).symm

/-! ## The first-order part -/

/-- **First-order term.**  For coefficients `B a` that are continuous and bounded by `KB ≥ 0`,
and any `η > 0`, the `L²` pairing of `Σ_a B a ∂_a ∂^l u` with `∂^l u`, summed over `l`, is
dominated by the Young-type combination `KB η ‖u‖²_{k+1} + KB (card ι)/(4η) ‖u‖²_k`. -/
lemma elcb_first_order_le (k : ℕ) (B : ι → (ι → ℝ) → ℂ) (KB η : ℝ) (hKB : 0 ≤ KB)
    (hη : 0 < η) (hBs : ∀ a, ContDiff ℝ 0 (B a)) (hB : ∀ a x, ‖B a x‖ ≤ KB) :
    ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (k + 2) u →
      (∑ l : Fin k → ι,
        L2re (fun x => ∑ a, B a x * pd a (pdVec k l u) x) (pdVec k l u))
        ≤ (KB * η) * ENormSq (k + 1) u
          + (KB * (Fintype.card ι : ℝ) / (4 * η)) * ENormSq k u := by
  intro u hu
  have hgl : ∀ l : Fin k → ι, Continuous (pdVec k l u) :=
    fun l => (elcb_contDiff_pdVec k hu l).continuous
  have hpal : ∀ l (a : ι), Continuous (pd a (pdVec k l u)) :=
    fun l a => elcb_continuous_pd_pdVec' k hu l a
  -- The `L²` pairing splits over `a`, and each summand is estimated by Young's inequality.
  have hterm : ∀ l : Fin k → ι,
      L2re (fun x => ∑ a, B a x * pd a (pdVec k l u) x) (pdVec k l u)
        ≤ KB * η * (∑ a : ι, ∫ x in unitCube, ‖pd a (pdVec k l u) x‖ ^ 2)
          + (KB / (4 * η)) * (∑ a : ι, ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) := by
    intro l
    rw [cm_L2re_sum Finset.univ (fun a x => B a x * pd a (pdVec k l u) x) (pdVec k l u)
      (fun a _ => ((hBs a).continuous).mul (hpal l a)) (hgl l)]
    calc (∑ a : ι, L2re (fun x => B a x * pd a (pdVec k l u) x) (pdVec k l u))
        ≤ ∑ a : ι, (KB * η * (∫ x in unitCube, ‖pd a (pdVec k l u) x‖ ^ 2)
            + (KB / (4 * η)) * (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2)) :=
          Finset.sum_le_sum (fun a _ => (le_abs_self _).trans
            (cm_term_bound KB η hKB hη (B a) (pd a (pdVec k l u)) (pdVec k l u)
              ((hBs a).continuous) (hpal l a) (hgl l) (hB a)))
      _ = KB * η * (∑ a : ι, ∫ x in unitCube, ‖pd a (pdVec k l u) x‖ ^ 2)
            + (KB / (4 * η)) * (∑ a : ι, ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  -- Factoring the sums over `l`
  have hX : (∑ l : Fin k → ι, KB * η * (∑ a : ι, ∫ x in unitCube, ‖pd a (pdVec k l u) x‖ ^ 2))
      = (KB * η) * (∑ l : Fin k → ι, ∑ a : ι,
          ∫ x in unitCube, ‖pd a (pdVec k l u) x‖ ^ 2) :=
    (Finset.mul_sum Finset.univ
      (fun l : Fin k → ι => ∑ a : ι, ∫ x in unitCube, ‖pd a (pdVec k l u) x‖ ^ 2)
      (KB * η)).symm
  have hY : (∑ l : Fin k → ι, (KB / (4 * η)) * (∑ a : ι,
        ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2))
      = (KB / (4 * η)) * (∑ l : Fin k → ι, ∑ a : ι,
          ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) :=
    (Finset.mul_sum Finset.univ
      (fun l : Fin k → ι => ∑ a : ι, ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2)
      (KB / (4 * η))).symm
  have hE1 : (∑ l : Fin k → ι, ∑ a : ι, ∫ x in unitCube, ‖pd a (pdVec k l u) x‖ ^ 2)
      = ENormSq (k + 1) u := (ENormSq_succ_eq k u).symm
  have hE2 : (∑ l : Fin k → ι, ∑ a : ι, ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2)
      = (Fintype.card ι : ℝ) * ENormSq k u := by
    have h1 : ∀ l : Fin k → ι, (∑ a : ι, ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2)
        = (Fintype.card ι : ℝ) * (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) := by
      intro l
      simpa using elcb_sum_const_mul (α := ι) (1 : ℝ)
        (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2)
    calc (∑ l : Fin k → ι, ∑ a : ι, ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2)
        = ∑ l : Fin k → ι, (Fintype.card ι : ℝ) * (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) :=
          Finset.sum_congr rfl (fun l _ => h1 l)
      _ = (Fintype.card ι : ℝ) * ENormSq k u :=
          (Finset.mul_sum Finset.univ
            (fun l : Fin k → ι => ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2)
            (Fintype.card ι : ℝ)).symm
  calc (∑ l : Fin k → ι,
        L2re (fun x => ∑ a, B a x * pd a (pdVec k l u) x) (pdVec k l u))
      ≤ ∑ l : Fin k → ι, (KB * η * (∑ a : ι, ∫ x in unitCube, ‖pd a (pdVec k l u) x‖ ^ 2)
          + (KB / (4 * η)) * (∑ a : ι, ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2)) :=
        Finset.sum_le_sum (fun l _ => hterm l)
    _ = (KB * η) * (∑ l : Fin k → ι, ∑ a : ι, ∫ x in unitCube, ‖pd a (pdVec k l u) x‖ ^ 2)
          + (KB / (4 * η)) * (∑ l : Fin k → ι, ∑ a : ι,
              ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) := by
        rw [Finset.sum_add_distrib, hX, hY]
    _ = (KB * η) * ENormSq (k + 1) u
          + (KB / (4 * η)) * ((Fintype.card ι : ℝ) * ENormSq k u) := by
        rw [hE1, hE2]
    _ = (KB * η) * ENormSq (k + 1) u
          + (KB * (Fintype.card ι : ℝ) / (4 * η)) * ENormSq k u := by ring

/-! ## The main theorem -/

theorem energy_le_of_coeff_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (A : ι → ι → (ι → ℝ) → ℝ)
    (hA : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d)) (hAper : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
    (hsym : ∀ c d x, A c d x = A d c x)
    (lam : ℝ) (hlam : 0 < lam)
    (hpos : ∀ x (ξ : ι → ℝ), lam * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d x * ξ c * ξ d)
    (K₁ K : ℝ) (hK₁ : ∀ c d i x, |Work.Diff.STE.pdR i (A c d) x| ≤ K₁)
    (hK : ∀ c d (l : Fin k → ι) x, |Work.Diff.STE.pdRVec k l (A c d) x| ≤ K)
    (B : ι → (ι → ℝ) → ℂ) (C0 : (ι → ℝ) → ℂ) (KB KC : ℝ)
    (hBs : ∀ a, ContDiff ℝ 0 (B a)) (hC0s : ContDiff ℝ 0 C0)
    (hB : ∀ a x, ‖B a x‖ ≤ KB) (hC0 : ∀ x, ‖C0 x‖ ≤ KC) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (k + 2) u →
      Work.Diff.STE.Periodic1 u →
      (∑ l : Fin k → ι,
        Work.Diff.STE.L2re
          (fun x => (∑ c, ∑ d, A c d x * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) x)
            + (∑ a, B a x * Work.Diff.STE.pd a (Work.Diff.STE.pdVec k l u) x)
            + C0 x * Work.Diff.STE.pdVec k l u x)
          (Work.Diff.STE.pdVec k l u))
        ≤ -((lam / 8) * Work.Diff.STE.ENormSq (k + 1) u) + C * Work.Diff.STE.ENormSq k u := by
  obtain ⟨C₁, hC₁, hdir⟩ := garding_vec_direct k A hA hAper hsym lam hlam hpos K₁ hK₁
  -- positive replacements for `KB`, `KC` and the Young parameter `η`
  set KB' : ℝ := max KB 0 with hKB'def
  set KC' : ℝ := max KC 0 with hKC'def
  have hKB' : 0 ≤ KB' := by rw [hKB'def]; exact le_max_right _ _
  have hKC' : 0 ≤ KC' := by rw [hKC'def]; exact le_max_right _ _
  have hB'max : ∀ a x, ‖B a x‖ ≤ KB' := by
    intro a x
    rw [hKB'def]
    exact (hB a x).trans (le_max_left _ _)
  have hC0'max : ∀ x, ‖C0 x‖ ≤ KC' := by
    intro x
    rw [hKC'def]
    exact (hC0 x).trans (le_max_left _ _)
  set η : ℝ := lam / (8 * (KB' + 1)) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    have : (0 : ℝ) < 8 * (KB' + 1) := by linarith
    positivity
  have hKBη : KB' * η ≤ lam / 8 := by
    have h1 : KB' * η = lam * KB' / (8 * (KB' + 1)) := by rw [hηdef]; ring
    rw [h1, div_le_iff₀ (by linarith : (0 : ℝ) < 8 * (KB' + 1))]
    have h2 : lam * KB' ≤ lam * (KB' + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hlam)
    calc lam * KB' ≤ lam * (KB' + 1) := h2
      _ = lam / 8 * (8 * (KB' + 1)) := by ring
  refine ⟨C₁ + KB' * (Fintype.card ι : ℝ) / (4 * η) + KC', ?_, ?_⟩
  · have h : 0 ≤ KB' * (Fintype.card ι : ℝ) / (4 * η) := by positivity
    linarith
  · intro u hu hup
    -- continuity of all the functions involved
    have hgl : ∀ l : Fin k → ι, Continuous (pdVec k l u) :=
      fun l => (elcb_contDiff_pdVec k hu l).continuous
    have hpal : ∀ l (a : ι), Continuous (pd a (pdVec k l u)) :=
      fun l a => elcb_continuous_pd_pdVec' k hu l a
    have hpd2 : ∀ l (c d : ι), Continuous (fun x => pd c (pd d (pdVec k l u)) x) :=
      fun l c d => elcb_continuous_pd_pdVec k hu l c d
    have hcontP : ∀ l : Fin k → ι,
        Continuous (fun x => ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) := by
      intro l
      refine continuous_finsetSum Finset.univ (fun c _ => ?_)
      refine continuous_finsetSum Finset.univ (fun d _ => ?_)
      exact (Complex.ofRealCLM.continuous.comp (hA c d).continuous).mul (hpd2 l c d)
    have hcontB : ∀ l : Fin k → ι,
        Continuous (fun x => ∑ a, B a x * pd a (pdVec k l u) x) := by
      intro l
      refine continuous_finsetSum Finset.univ (fun a _ => ?_)
      exact ((hBs a).continuous).mul (hpal l a)
    have hcontC : ∀ l : Fin k → ι, Continuous (fun x => C0 x * pdVec k l u x) :=
      fun l => hC0s.continuous.mul (hgl l)
    -- the three parts of the pairing
    have hsplit : ∀ l : Fin k → ι,
        L2re (fun x => (∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x)
              + (∑ a, B a x * pd a (pdVec k l u) x)
              + C0 x * pdVec k l u x) (pdVec k l u)
        = L2re (fun x => ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u)
          + L2re (fun x => ∑ a, B a x * pd a (pdVec k l u) x) (pdVec k l u)
          + L2re (fun x => C0 x * pdVec k l u x) (pdVec k l u) := by
      intro l
      have h1 := cm_L2re_add
        (fun x => (∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x)
              + (∑ a, B a x * pd a (pdVec k l u) x))
        (fun x => C0 x * pdVec k l u x) (pdVec k l u)
        ((hcontP l).add (hcontB l)) (hcontC l) (hgl l)
      have h2 := cm_L2re_add
        (fun x => ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x)
        (fun x => ∑ a, B a x * pd a (pdVec k l u) x) (pdVec k l u)
        (hcontP l) (hcontB l) (hgl l)
      rw [h2] at h1
      exact h1
    have hsumsplit :
        (∑ l : Fin k → ι,
          L2re (fun x => (∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x)
              + (∑ a, B a x * pd a (pdVec k l u) x)
              + C0 x * pdVec k l u x) (pdVec k l u))
        = (∑ l : Fin k → ι,
            L2re (fun x => ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u))
          + (∑ l : Fin k → ι,
            L2re (fun x => ∑ a, B a x * pd a (pdVec k l u) x) (pdVec k l u))
          + (∑ l : Fin k → ι, L2re (fun x => C0 x * pdVec k l u x) (pdVec k l u)) := by
      rw [Finset.sum_congr rfl (fun l _ => hsplit l), Finset.sum_add_distrib,
        Finset.sum_add_distrib]
    have hP := hdir u hu hup
    have hBnd := elcb_first_order_le k B KB' η hKB' hηpos hBs hB'max u hu
    have hCnd := elcb_zero_order_le k C0 KC' hKC' hC0s hC0'max u hu
    have hE1 : 0 ≤ ENormSq (k + 1) u := cm_ENormSq_nonneg (k + 1) u
    calc (∑ l : Fin k → ι,
          L2re (fun x => (∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x)
              + (∑ a, B a x * pd a (pdVec k l u) x)
              + C0 x * pdVec k l u x) (pdVec k l u))
        = (∑ l : Fin k → ι,
            L2re (fun x => ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x) (pdVec k l u))
          + (∑ l : Fin k → ι,
            L2re (fun x => ∑ a, B a x * pd a (pdVec k l u) x) (pdVec k l u))
          + (∑ l : Fin k → ι, L2re (fun x => C0 x * pdVec k l u x) (pdVec k l u)) :=
          hsumsplit
      _ ≤ (-(lam / 2 * ENormSq (k + 1) u) + C₁ * ENormSq k u)
            + ((KB' * η) * ENormSq (k + 1) u
                + (KB' * (Fintype.card ι : ℝ) / (4 * η)) * ENormSq k u)
            + KC' * ENormSq k u := add_le_add (add_le_add hP hBnd) hCnd
      _ ≤ -((lam / 8) * ENormSq (k + 1) u)
            + (C₁ + KB' * (Fintype.card ι : ℝ) / (4 * η) + KC') * ENormSq k u := by
        have hle : KB' * η * ENormSq (k + 1) u ≤ (lam / 8) * ENormSq (k + 1) u :=
          mul_le_mul_of_nonneg_right hKBη hE1
        nlinarith [hle]

end Work.Diff.STE
