import Mathlib
import Submission.Work.Diff.STE.flat.TowerDefs
import Submission.Work.Diff.STE.flat.limit_aux
import Submission.Work.Diff.STE.flat.limit_prep
import Submission.Work.Diff.STE.flat.hasDerivWithinAt_seriesFunM
import Submission.Work.Diff.STE.flat.hasDerivWithinAt_fourierCoeff
import Submission.Work.Diff.STE.flat.towerExp_contDiff
import Submission.Work.Diff.STE.flat.towerExp_congr
import Submission.Work.Diff.STE.flat.towerExp_hasDerivWithinAt
import Submission.Work.Diff.STE.flat.hasDerivWithinAt_jetM_seriesFunM
import Submission.Work.Diff.STE.flat.norm_jetM_le_of_decay

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open scoped BigOperators Topology
open Filter MeasureTheory

noncomputable section

variable {n : ℕ}

/-!
## Auxiliary material for the time-derivative tower of the limit solution

The target `dd_deriv` differentiates, in time, every level of the formal time-derivative tower
`dd Φ cinf j` of the limit solution, starting from the level `0` statement `hder0` and the
*uniform decay* of all levels `hdec`.

The structure of the proof is a strong induction on the level `j`.  At level `j + 1` the family is
the Fourier coefficient of the tower expression

`dd Φ cinf (j+1) s k = fourierCoeffM (fun x => towerExp Φ (j+1) (x, jets of dd Φ cinf i s)) k`,

so `hasDerivWithinAt_fourierCoeff` reduces the claim to

* a *pointwise* time derivative of the tower expression along the path of jet families
  (`towerExp_hasDerivWithinAt`, which uses the induction hypothesis through the jet-level
  derivatives `hasDerivWithinAt_jetM_seriesFunM`), and
* a *Lipschitz* bound in time of the tower expression, which is the mean value theorem applied
  to the very same pointwise derivative, with a uniform bound on the level `j + 2` tower
  expression over the compact set of possible jets (`exists_bound_Tfun`).

The two remaining ingredients of the tower calculus are delegated:
`Work.Diff.STE.flat.hasDerivWithinAt_jetM_seriesFunM` (the jet-level derivative) and
`Work.Diff.STE.flat.norm_jetM_le_of_decay` (the sup bound on the jet of a Fourier series from the
pointwise decay of its coefficients).  They are passed to the induction step as the explicit
hypotheses `hD2`, `hD3`, so that this file can be developed independently of them; the final
assembly `dd_deriv_main` instantiates them.
-/

/-- The tuple of spatial `2`-jets of the first `m` families of the tower `dd Φ cinf`. -/
abbrev Jsfun (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (m : ℕ) (s : ℝ) : (Fin n → ℝ) → (Fin m → Jet n) :=
  fun x i => jetM (seriesFunM (dd Φ cinf (i : ℕ) s)) x

/-- The tower expression of level `m` evaluated at the jets of the tower families.
`Φt` is the nonlinearity used in the tower recursion, `Φj` the one whose tower families
`dd Φj cinf i s` provide the jet arguments. -/
abbrev Tfun (Φt Φj : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (m : ℕ) (s : ℝ) : Torus n :=
  fun x => towerExp Φt m (x, Jsfun Φj cinf m s x)

/-- The level `m + 1` family of the tower is the Fourier coefficient family of the level `m + 1`
tower expression. -/
lemma dd_eq_fourierCoeffM_Tfun (Φ : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (m : ℕ) (s : ℝ) (k : Fin n → ℤ) :
    dd Φ cinf (m + 1) s k = fourierCoeffM (Tfun Φ Φ cinf (m + 1) s) k := by
  have h : (fun x : Fin n → ℝ => towerExp Φ (m + 1)
      (x, fun i : Fin (m + 1) => jetM (seriesFunM (ddseq Φ cinf (m + 1) s i)) x))
      = Tfun Φ Φ cinf (m + 1) s := by
    funext x
    simp only [Tfun, Jsfun]
    rw [show (fun i : Fin (m + 1) => jetM (seriesFunM (ddseq Φ cinf (m + 1) s i)) x)
        = (fun i : Fin (m + 1) => jetM (seriesFunM (dd Φ cinf (i : ℕ) s)) x) from
      funext (fun i => by rw [ddseq_apply])]
  rw [dd_succ, h]

/-- Locality of the tower: replacing the nonlinearity `Φ` by `Φ'`, which agrees with it on the
open set `V'` of jets, does not change the tower expression as long as the first jet slot lies
in `V'`. -/
lemma Tfun_eq_of_agrees {T : ℝ} (Φ Φ' : (Fin n → ℝ) × Jet n → MatC n)
    (V' : Set (Jet n)) (hV' : IsOpen V')
    (hagr : ∀ (x : Fin n → ℝ) (w : Jet n), w ∈ V' → Φ' (x, w) = Φ (x, w))
    (cinf : ℝ → (Fin n → ℤ) → MatC n)
    (hconf : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : Fin n → ℝ, jetM (seriesFunM (cinf t)) x ∈ V')
    (m : ℕ) (s : ℝ) (hs : s ∈ Set.Ico (0 : ℝ) T) :
    Tfun Φ Φ cinf (m + 1) s = Tfun Φ' Φ cinf (m + 1) s := by
  funext x
  have hmem : Jsfun Φ cinf (m + 1) s x 0 ∈ V' := by
    change jetM (seriesFunM (dd Φ cinf 0 s)) x ∈ V'
    rw [dd_zero]
    exact hconf s hs x
  simpa only [Tfun] using (towerExp_congr_aux Φ Φ' V' hV' (fun x w hw => (hagr x w hw).symm) m
    (x, Jsfun Φ cinf (m + 1) s x) hmem)

/-! ## Summability of the weights -/

lemma summable_inv_wt_pow {n : ℕ} (N : ℕ) (hN : n < 2 * N) :
    Summable (fun k : Fin n → ℤ => ((wt k) ^ N)⁻¹) := by
  have h := Work.Diff.STE.summable_wt_zpow (ι := Fin n) N (by simpa using hN)
  refine h.congr (fun k => ?_)
  rw [zpow_neg, zpow_natCast]

/-- The decay function `k ↦ C / ⟨k⟩^N` and its second moment are both summable. -/
lemma summable_decay_pair {n : ℕ} {N : ℕ} (hN2 : 2 ≤ N) (hN : n < 2 * (N - 2)) (C : ℝ) :
    Summable (fun k : Fin n → ℤ => C * ((wt k) ^ N)⁻¹) ∧
    Summable (fun k : Fin n → ℤ => (wt k) ^ 2 * (C * ((wt k) ^ N)⁻¹)) := by
  have h1 : Summable (fun k : Fin n → ℤ => ((wt k) ^ (N - 2))⁻¹) := summable_inv_wt_pow (N - 2) hN
  refine ⟨(summable_inv_wt_pow N (by omega)).mul_left C, ?_⟩
  refine (h1.mul_left C).congr (fun k => ?_)
  have hw : (wt k) ≠ 0 := ne_of_gt (wt_pos k)
  have hpow : (wt k) ^ N = (wt k) ^ 2 * (wt k) ^ (N - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, mul_inv]
  field_simp

/-- A pointwise weighted decay bound on a coefficient family gives the summability of all its
weighted moments. -/
lemma summable_wt_pow_mul_norm_of_decay {n : ℕ} {c : (Fin n → ℤ) → MatC n} (N M : ℕ) (C : ℝ)
    (h : ∀ (k : Fin n → ℤ) (a b : Fin n), ‖c k a b‖ * (wt k) ^ M ≤ C) (hNM : N ≤ M)
    (hN : n < 2 * (M - N)) :
    ∀ a b : Fin n, Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖c k a b‖) := by
  intro a b
  have hb : Summable (fun k : Fin n → ℤ => C * ((wt k) ^ (M - N))⁻¹) :=
    (summable_inv_wt_pow (M - N) hN).mul_left C
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hb
  · exact mul_nonneg (pow_nonneg (wt_pos k).le N) (norm_nonneg _)
  · have hle : ‖c k a b‖ ≤ C * ((wt k) ^ M)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (wt_pos k) M)]
      exact h k a b
    refine (mul_le_mul_of_nonneg_left hle (pow_nonneg (wt_pos k).le N)).trans (le_of_eq ?_)
    have hw : (wt k) ≠ 0 := ne_of_gt (wt_pos k)
    have hpow : (wt k) ^ M = (wt k) ^ N * (wt k) ^ (M - N) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, mul_inv]
    field_simp

/-! ## The mean value inequality in the time variable -/

/-- The mean value inequality on the half-open interval `[0, T)`: if `f` has derivative `g u` at
every `u ∈ [0, T)` and `‖g u‖ ≤ D` there, then `‖f s - f t‖ ≤ D |s - t|` for `s, t ∈ [0, T)`. -/
lemma norm_sub_le_of_hasDerivWithinAt_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : ℝ → F} {T s t D : ℝ}
    (hg : ∀ u ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt f (g u) (Set.Ico (0 : ℝ) T) u)
    (hb : ∀ u ∈ Set.Ico (0 : ℝ) T, ‖g u‖ ≤ D)
    (hs : s ∈ Set.Ico (0 : ℝ) T) (ht : t ∈ Set.Ico (0 : ℝ) T) :
    ‖f s - f t‖ ≤ D * |s - t| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.Ico (0 : ℝ) T)
    (f := f) (f' := g) (C := D) (fun u hu => hg u hu) (fun u hu => hb u hu)
    (convex_Ico 0 T) ht hs
  rwa [Real.norm_eq_abs] at h

/-! ## Continuity and the uniform bound on the tower expression -/

/-- Continuity of a matrix-valued function implies continuity of its entries. -/
lemma continuous_entryM {n : ℕ} {X : Type*} [TopologicalSpace X] {f : X → MatC n}
    (hf : Continuous f) (a b : Fin n) : Continuous (fun x => f x a b) :=
  (continuous_apply b).comp ((continuous_apply a).comp hf)

/-- Smoothness of the tower expression as a function of the space point. -/
lemma contDiff_Tfun (Φt Φj : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (m : ℕ) (s : ℝ)
    (hΦt : ContDiff ℝ (⊤ : ℕ∞) Φt)
    (hmom : ∀ (i : Fin m) (N : ℕ) (a b : Fin n),
      Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖dd Φj cinf (i : ℕ) s k a b‖)) :
    ContDiff ℝ (⊤ : ℕ∞) (Tfun Φt Φj cinf m s) := by
  have hjets : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => Jsfun Φj cinf m s x) :=
    contDiff_pi.mpr (fun i => contDiff_jetM_of_mom (fun a b N => hmom i N a b))
  exact (towerExp_contDiff Φt hΦt m).comp (contDiff_id.prodMk hjets)

/-- A continuous complex-valued function is integrable on the unit cube.  (`private`: a sibling
module declares the same name.) -/
private lemma integrableOn_unitCube_of_continuous {E : Type*} [NormedAddCommGroup E]
    {f : (Fin n → ℝ) → E} (hf : Continuous f) :
    MeasureTheory.IntegrableOn f unitCube := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : unitCube ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC hf.continuousOn).mono_set hsub

/-- **Uniform bound on the tower expression on the compact set of possible jets.**  If the jets of
the level `m + 1` are uniformly bounded by `R` on the slab, the level `m + 1` tower expression is
bounded on `unitCube` by a constant depending only on `R`, `T` and the nonlinearity. -/
lemma exists_bound_Tfun (Φt Φj : (Fin n → ℝ) × Jet n → MatC n)
    (cinf : ℝ → (Fin n → ℤ) → MatC n) (T : ℝ) (m : ℕ)
    (hΦt : ContDiff ℝ (⊤ : ℕ∞) Φt)
    (hB : ∃ R : ℝ, 0 ≤ R ∧ ∀ (i : Fin (m + 1)) (s : ℝ), s ∈ Set.Ico 0 T →
      ∀ x : Fin n → ℝ, ‖Jsfun Φj cinf (m + 1) s x i‖ ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Ico 0 T, ∀ x ∈ unitCube, ‖Tfun Φt Φj cinf (m + 1) s x‖ ≤ B := by
  obtain ⟨R, hR0, hR⟩ := hB
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) ×ˢ
      Set.pi Set.univ (fun _ : Fin (m + 1) => Metric.closedBall (0 : Jet n) R)) :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).prod
      (isCompact_univ_pi (fun _ => isCompact_closedBall (0 : Jet n) R))
  obtain ⟨B, hBnd⟩ := hK.exists_bound_of_continuousOn
    ((towerExp_contDiff Φt hΦt (m + 1)).continuous.continuousOn)
  refine ⟨max B 0, le_max_right _ _, fun s hs x hx => ?_⟩
  simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx
  have hmem : (x, Jsfun Φj cinf (m + 1) s x) ∈ Set.pi Set.univ
      (fun _ : Fin n => Set.Icc (0 : ℝ) 1) ×ˢ
      Set.pi Set.univ (fun _ : Fin (m + 1) => Metric.closedBall (0 : Jet n) R) := by
    refine ⟨?_, ?_⟩
    · intro i _
      exact ⟨le_of_lt (hx i).1, (hx i).2⟩
    · intro i _
      simpa [Metric.mem_closedBall, dist_eq_norm] using hR i s hs x
  exact le_trans (hBnd _ hmem) (le_max_left _ _)

/-- **One step of the induction.**  Assuming the derivative statement at all levels `< M + 1`, the
level `M + 1` family of the tower is differentiable in time with derivative the level `M + 2`
family.  The two deleted lemmas of the tower calculus enter as `hD2` (sup bound on jets) and `hD3`
(jet-level derivative). -/
theorem dd_deriv_step {n : ℕ} (T : ℝ) (hT : 0 < T)
    (Φ Φ' : (Fin n → ℝ) × Jet n → MatC n)
    (hΦ' : ContDiff ℝ (⊤ : ℕ∞) Φ')
    (V' : Set (Jet n)) (hV' : IsOpen V')
    (hagr : ∀ (x : Fin n → ℝ) (w : Jet n), w ∈ V' → Φ' (x, w) = Φ (x, w))
    (cinf : ℝ → (Fin n → ℤ) → MatC n)
    (hconf : ∀ t ∈ Set.Ico 0 T, ∀ x : Fin n → ℝ, jetM (seriesFunM (cinf t)) x ∈ V')
    (hdec : ∀ (j M : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico 0 T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      ‖dd Φ cinf j t k' a b‖ * (wt k') ^ M ≤ C)
    (hD2 : ∀ (M : ℕ), n + 4 < 2 * M → ∃ C' : ℝ, 0 ≤ C' ∧
        ∀ (C : ℝ) (hC : 0 ≤ C) (c : (Fin n → ℤ) → MatC n),
        (∀ (k : Fin n → ℤ) (a b : Fin n), ‖c k a b‖ * (wt k) ^ M ≤ C) →
        ∀ x : Fin n → ℝ, ‖jetM (seriesFunM c) x‖ ≤ C' * C)
    (hD3 : ∀ {τ t : ℝ}, 0 < τ → t ∈ Set.Ico (0 : ℝ) τ → ∀ (x : Fin n → ℝ)
        (d : ℝ → (Fin n → ℤ) → MatC n) (d' : (Fin n → ℤ) → MatC n)
        (G : (Fin n → ℤ) → ℝ), Summable G → (∀ k, 0 ≤ G k) →
        Summable (fun k : Fin n → ℤ => (wt k) ^ 2 * G k) →
        (∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (N : ℕ) (a b : Fin n),
          Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖d s k a b‖)) →
        (∀ (N : ℕ) (a b : Fin n),
          Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖d' k a b‖)) →
        (∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (k : Fin n → ℤ) (a b : Fin n),
          ‖d s k a b - d t k a b‖ ≤ |s - t| * G k) →
        (∀ (k : Fin n → ℤ) (a b : Fin n),
          HasDerivWithinAt (fun s : ℝ => d s k a b) (d' k a b) (Set.Ico (0 : ℝ) τ) t) →
        HasDerivWithinAt (fun s : ℝ => jetM (seriesFunM (d s)) x)
          (jetM (seriesFunM d') x) (Set.Ico (0 : ℝ) τ) t)
    (M : ℕ)
    (ih : ∀ i < M + 1, ∀ t ∈ Set.Ico 0 T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s => dd Φ cinf i s k' a b) (dd Φ cinf (i + 1) t k' a b)
        (Set.Ico 0 T) t) :
    ∀ t ∈ Set.Ico 0 T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s => dd Φ cinf (M + 1) s k' a b) (dd Φ cinf (M + 2) t k' a b)
        (Set.Ico 0 T) t := by
  -- uniform bound on the jets of the levels `0, …, M+1`
  have hjetR : ∃ R : ℝ, 0 ≤ R ∧ ∀ (i : Fin (M + 2)) (s : ℝ), s ∈ Set.Ico 0 T →
      ∀ x : Fin n → ℝ, ‖Jsfun Φ cinf (M + 2) s x i‖ ≤ R := by
    classical
    choose C hC0 hCb using fun (i : Fin (M + 2)) => hdec (i : ℕ) (n + 4)
    obtain ⟨C', hC'0, hC'b⟩ := hD2 (n + 4) (by omega)
    refine ⟨∑ i : Fin (M + 2), C' * C i, Finset.sum_nonneg (fun i _ => mul_nonneg hC'0 (hC0 i)),
      ?_⟩
    intro i s hs x
    refine le_trans (hC'b (C i) (hC0 i) (dd Φ cinf (i : ℕ) s) (hCb i s hs) x) ?_
    exact Finset.single_le_sum (fun j _ => mul_nonneg hC'0 (hC0 j)) (Finset.mem_univ i)
  obtain ⟨B, hB0, hB⟩ := exists_bound_Tfun Φ' Φ cinf T (M + 1) hΦ' hjetR
  -- the jet-level derivative statements, from the induction hypothesis and `hD3`
  have hjetD : ∀ (i : Fin (M + 1)) (u : ℝ), u ∈ Set.Ico 0 T → ∀ x : Fin n → ℝ,
      HasDerivWithinAt (fun s => jetM (seriesFunM (dd Φ cinf (i : ℕ) s)) x)
        (jetM (seriesFunM (dd Φ cinf ((i : ℕ) + 1) u)) x) (Set.Ico 0 T) u := by
    intro i u hu x
    obtain ⟨C, hC0, hCb⟩ := hdec ((i : ℕ) + 1) (n + 4)
    have hdiff : ∀ s ∈ Set.Ico 0 T, ∀ (k : Fin n → ℤ) (a b : Fin n),
        ‖dd Φ cinf (i : ℕ) s k a b - dd Φ cinf (i : ℕ) u k a b‖
          ≤ |s - u| * (C * ((wt k) ^ (n + 4))⁻¹) := by
      intro s hs k a b
      have hb : ∀ v ∈ Set.Ico 0 T,
          ‖dd Φ cinf ((i : ℕ) + 1) v k a b‖ ≤ C * ((wt k) ^ (n + 4))⁻¹ := by
        intro v hv
        have h1 : ‖dd Φ cinf ((i : ℕ) + 1) v k a b‖ ≤ C / (wt k) ^ (n + 4) := by
          rw [le_div_iff₀ (pow_pos (wt_pos k) (n + 4))]
          exact hCb v hv k a b
        rwa [div_eq_mul_inv] at h1
      have hmvt := norm_sub_le_of_hasDerivWithinAt_le
        (f := fun v => dd Φ cinf (i : ℕ) v k a b)
        (g := fun v => dd Φ cinf ((i : ℕ) + 1) v k a b) (T := T)
        (D := C * ((wt k) ^ (n + 4))⁻¹)
        (fun v hv => ih (i : ℕ) i.isLt v hv k a b) hb hs hu
      simpa [mul_comm] using hmvt
    have hG : Summable (fun k : Fin n → ℤ => C * ((wt k) ^ (n + 4))⁻¹) :=
      (summable_decay_pair (n := n) (N := n + 4) (by omega) (by omega) C).1
    have hG2 : Summable (fun k : Fin n → ℤ => (wt k) ^ 2 * (C * ((wt k) ^ (n + 4))⁻¹)) :=
      (summable_decay_pair (n := n) (N := n + 4) (by omega) (by omega) C).2
    have hmom : ∀ s ∈ Set.Ico 0 T, ∀ (N : ℕ) (a b : Fin n),
        Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖dd Φ cinf (i : ℕ) s k a b‖) := by
      intro s hs N a b
      obtain ⟨C₂, -, hC₂⟩ := hdec (i : ℕ) (N + n + 1)
      exact summable_wt_pow_mul_norm_of_decay N (N + n + 1) C₂ (hC₂ s hs) (by omega) (by omega) a b
    have hmom' : ∀ (N : ℕ) (a b : Fin n),
        Summable (fun k : Fin n → ℤ => (wt k) ^ N * ‖dd Φ cinf ((i : ℕ) + 1) u k a b‖) := by
      intro N a b
      obtain ⟨C₂, -, hC₂⟩ := hdec ((i : ℕ) + 1) (N + n + 1)
      exact summable_wt_pow_mul_norm_of_decay N (N + n + 1) C₂ (hC₂ u hu) (by omega) (by omega) a b
    exact hD3 hT hu x (dd Φ cinf (i : ℕ)) (dd Φ cinf ((i : ℕ) + 1) u)
      (fun k => C * ((wt k) ^ (n + 4))⁻¹) hG
      (fun k => mul_nonneg hC0 (inv_nonneg.mpr (pow_nonneg (wt_pos k).le (n + 4)))) hG2 hmom hmom'
      hdiff (fun k a b => ih (i : ℕ) i.isLt u hu k a b)
  -- the time derivative of the tower expression along the path of jets
  have hdir : ∀ u ∈ Set.Ico 0 T, ∀ x : Fin n → ℝ,
      HasDerivWithinAt (fun s => Tfun Φ' Φ cinf (M + 1) s x)
        (Tfun Φ' Φ cinf (M + 2) u x) (Set.Ico 0 T) u := by
    intro u hu x
    refine towerExp_hasDerivWithinAt (τ := T) hT (j := M + 1) (by omega) Φ' x u
      (Δ := fun l (s : ℝ) => Jsfun Φ cinf (M + 2) s x l) ?_ ?_
    · exact ((towerExp_contDiff Φ' hΦ' (M + 1)).differentiable (by simp)).differentiableAt
    · intro i
      exact hjetD i u hu x
  intro t ht k' a b
  -- the Lipschitz bound in time of the tower expression
  have hlip : ∀ s ∈ Set.Ico 0 T, ∀ x ∈ unitCube,
      ‖Tfun Φ' Φ cinf (M + 1) s x - Tfun Φ' Φ cinf (M + 1) t x‖ ≤ max B 0 * |s - t| := by
    intro s hs x hx
    exact norm_sub_le_of_hasDerivWithinAt_le (f := fun u => Tfun Φ' Φ cinf (M + 1) u x)
      (g := fun u => Tfun Φ' Φ cinf (M + 2) u x) (T := T) (D := max B 0)
      (fun u hu => hdir u hu x) (fun u hu => le_trans (hB u hu x hx) (le_max_left _ _)) hs ht
  have hlip' : ∀ s ∈ Set.Ico 0 T, ∀ x ∈ unitCube,
      ‖Tfun Φ' Φ cinf (M + 1) s x a b - Tfun Φ' Φ cinf (M + 1) t x a b‖
        ≤ |s - t| * max B 0 := by
    intro s hs x hx
    have h1 : ‖(Tfun Φ' Φ cinf (M + 1) s x - Tfun Φ' Φ cinf (M + 1) t x) a‖
        ≤ ‖Tfun Φ' Φ cinf (M + 1) s x - Tfun Φ' Φ cinf (M + 1) t x‖ :=
      norm_le_pi_norm _ a
    have h2 : ‖(Tfun Φ' Φ cinf (M + 1) s x - Tfun Φ' Φ cinf (M + 1) t x) a b‖
        ≤ ‖(Tfun Φ' Φ cinf (M + 1) s x - Tfun Φ' Φ cinf (M + 1) t x) a‖ :=
      norm_le_pi_norm _ b
    have h3 := le_trans (le_trans h2 h1) (hlip s hs x hx)
    simpa only [Pi.sub_apply, mul_comm] using h3
  -- the pointwise derivative at `t`
  have hpoint : ∀ x ∈ unitCube, HasDerivWithinAt
      (fun s => Tfun Φ' Φ cinf (M + 1) s x a b) (Tfun Φ' Φ cinf (M + 2) t x a b)
      (Set.Ico 0 T) t := by
    intro x _
    have h1 := hdir t ht x
    exact (hasDerivWithinAt_pi.mp ((hasDerivWithinAt_pi.mp h1) a)) b
  -- continuity of the integrands
  have hcont : ∀ s ∈ Set.Ico 0 T, Continuous (fun x => Tfun Φ' Φ cinf (M + 1) s x) := by
    intro s hs
    refine (contDiff_Tfun Φ' Φ cinf (M + 1) s hΦ' ?_).continuous
    intro i N a b
    obtain ⟨C₂, -, hC₂⟩ := hdec (i : ℕ) (N + n + 1)
    exact summable_wt_pow_mul_norm_of_decay N (N + n + 1) C₂ (hC₂ s hs) (by omega) (by omega) a b
  have hcont₂ : Continuous (fun x => Tfun Φ' Φ cinf (M + 2) t x) := by
    refine (contDiff_Tfun Φ' Φ cinf (M + 2) t hΦ' ?_).continuous
    intro i N a b
    obtain ⟨C₂, -, hC₂⟩ := hdec (i : ℕ) (N + n + 1)
    exact summable_wt_pow_mul_norm_of_decay N (N + n + 1) C₂ (hC₂ t ht) (by omega) (by omega) a b
  -- differentiation under the integral sign
  have hmain := hasDerivWithinAt_fourierCoeff (τ := T) hT ht k'
    (fun s x => Tfun Φ' Φ cinf (M + 1) s x a b)
    (fun x => Tfun Φ' Φ cinf (M + 2) t x a b) (fun _ => max B 0)
    (integrableOn_unitCube_of_continuous (f := fun _ : Fin n → ℝ => max B 0) continuous_const)
    (integrableOn_unitCube_of_continuous (continuous_entryM (hcont t ht) a b))
    (fun s hs => (continuous_entryM (hcont s hs) a b).aestronglyMeasurable)
    ((continuous_entryM hcont₂ a b).aestronglyMeasurable)
    hlip' hpoint
  -- rewrite both sides as Fourier coefficients of the `Φ'`-tower expression
  have hLgen : ∀ (m : ℕ) (s : ℝ), s ∈ Set.Ico 0 T → ∀ (k : Fin n → ℤ) (a b : Fin n),
      dd Φ cinf (m + 1) s k a b = fourierCoeff (fun x => Tfun Φ' Φ cinf (m + 1) s x a b) k := by
    intro m s hs k a b
    rw [dd_eq_fourierCoeffM_Tfun Φ cinf m s k, fourierCoeffM_apply]
    have hfun : (fun x : Fin n → ℝ => Tfun Φ Φ cinf (m + 1) s x a b)
        = (fun x => Tfun Φ' Φ cinf (m + 1) s x a b) := by
      funext x
      rw [Tfun_eq_of_agrees Φ Φ' V' hV' hagr cinf hconf m s hs]
    rw [hfun]
  have hfun : (fun s : ℝ => dd Φ cinf (M + 1) s k' a b) =ᶠ[𝓝[Set.Ico 0 T] t]
      (fun s => fourierCoeff (fun x => Tfun Φ' Φ cinf (M + 1) s x a b) k') :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun s hs => hLgen M s hs k' a b)
  rw [← hLgen (M + 1) t ht k' a b] at hmain
  exact hmain.congr_of_eventuallyEq hfun (hLgen M t ht k' a b)

/-- **The main induction.**  From the level-`0` statement `hder0` and the uniform decay `hdec`
of all the levels of the tower, every level is differentiable in time. -/
theorem dd_deriv_main {n : ℕ} (T : ℝ) (hT : 0 < T)
    (Φ Φ' : (Fin n → ℝ) × Jet n → MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (hΦ' : ContDiff ℝ (⊤ : ℕ∞) Φ')
    (V' : Set (Work.Diff.STE.Flat.Jet n)) (hV' : IsOpen V')
    (hV'det : ∀ w : Work.Diff.STE.Flat.Jet n, w ∈ V' → (Work.Diff.STE.Flat.reMat w.1).det ≠ 0)
    (hagr : ∀ (x : Fin n → ℝ) (w : Work.Diff.STE.Flat.Jet n), w ∈ V' →
      Φ' (x, w) = Φ (x, w))
    (cinf : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hconf : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : Fin n → ℝ,
      Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (cinf t)) x ∈ V')
    (hdec : ∀ (j M : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ (k' : Fin n → ℤ) (a b : Fin n),
      ‖dd Φ cinf j t k' a b‖ * (Work.Diff.STE.wt k') ^ M ≤ C)
    (hD2 : ∀ (M : ℕ), n + 4 < 2 * M → ∃ C' : ℝ, 0 ≤ C' ∧
        ∀ (C : ℝ) (hC : 0 ≤ C) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ (k : Fin n → ℤ) (a b : Fin n), ‖c k a b‖ * (Work.Diff.STE.wt k) ^ M ≤ C) →
        ∀ x : Fin n → ℝ,
          ‖Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM c) x‖ ≤ C' * C)
    (hD3 : ∀ {τ t : ℝ}, 0 < τ → t ∈ Set.Ico (0 : ℝ) τ → ∀ (x : Fin n → ℝ)
        (d : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
        (d' : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
        (G : (Fin n → ℤ) → ℝ), Summable G → (∀ k, 0 ≤ G k) →
        Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ 2 * G k) →
        (∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (N : ℕ) (a b : Fin n),
          Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖d s k a b‖)) →
        (∀ (N : ℕ) (a b : Fin n),
          Summable (fun k : Fin n → ℤ => (Work.Diff.STE.wt k) ^ N * ‖d' k a b‖)) →
        (∀ s ∈ Set.Ico (0 : ℝ) τ, ∀ (k : Fin n → ℤ) (a b : Fin n),
          ‖d s k a b - d t k a b‖ ≤ |s - t| * G k) →
        (∀ (k : Fin n → ℤ) (a b : Fin n),
          HasDerivWithinAt (fun s : ℝ => d s k a b) (d' k a b) (Set.Ico (0 : ℝ) τ) t) →
        HasDerivWithinAt
          (fun s : ℝ => Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (d s)) x)
          (Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM d') x) (Set.Ico (0 : ℝ) τ) t)
    (hder0 : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => dd Φ cinf 0 s k' a b)
        (dd Φ cinf 1 t k' a b) (Set.Ico (0 : ℝ) T) t) :
    ∀ (j : ℕ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) T → ∀ (k' : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => dd Φ cinf j s k' a b)
        (dd Φ cinf (j + 1) t k' a b) (Set.Ico (0 : ℝ) T) t := by
  have hmain : ∀ m, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => dd Φ cinf m s k' a b)
        (dd Φ cinf (m + 1) t k' a b) (Set.Ico (0 : ℝ) T) t := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases m with _ | M
      · intro t ht k' a b
        exact hder0 t ht k' a b
      · exact dd_deriv_step T hT Φ Φ' hΦ' V' hV' hagr cinf hconf hdec hD2 hD3 M
          (fun i hi t ht k' a b => ih i (by omega) t ht k' a b)
  exact hmain

theorem dd_deriv {n : ℕ} (T : ℝ) (hT : 0 < T)
    (Φ Φ' : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (hΦ' : ContDiff ℝ (⊤ : ℕ∞) Φ')
    (V' : Set (Work.Diff.STE.Flat.Jet n)) (hV' : IsOpen V')
    (hV'det : ∀ w : Work.Diff.STE.Flat.Jet n, w ∈ V' → (Work.Diff.STE.Flat.reMat w.1).det ≠ 0)
    (hagr : ∀ (x : Fin n → ℝ) (w : Work.Diff.STE.Flat.Jet n), w ∈ V' → Φ' (x, w) = Φ (x, w))
    (cinf : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hconf : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : Fin n → ℝ,
      Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (cinf t)) x ∈ V')
    (hdec : ∀ (j M : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) T,
      ∀ (k' : Fin n → ℤ) (a b : Fin n),
      ‖Work.Diff.STE.flat.dd Φ cinf j t k' a b‖ * (Work.Diff.STE.wt k') ^ M ≤ C)
    (hder0 : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (k' : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => Work.Diff.STE.flat.dd Φ cinf 0 s k' a b)
        (Work.Diff.STE.flat.dd Φ cinf 1 t k' a b) (Set.Ico (0 : ℝ) T) t) :
    ∀ (j : ℕ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) T → ∀ (k' : Fin n → ℤ) (a b : Fin n),
      HasDerivWithinAt (fun s : ℝ => Work.Diff.STE.flat.dd Φ cinf j s k' a b)
        (Work.Diff.STE.flat.dd Φ cinf (j + 1) t k' a b) (Set.Ico (0 : ℝ) T) t :=
  dd_deriv_main T hT Φ Φ' hshape hΦ' V' hV' hV'det hagr cinf hconf hdec
    (fun M hM => norm_jetM_le_of_decay M hM)
    (fun {τ t} hτ ht x d d' G hG hG0 hG2 hmom hmom' hdiff hder =>
      hasDerivWithinAt_jetM_seriesFunM hτ ht x d d' G hG hG0 hG2 hmom hmom' hdiff hder)
    hder0

end

end Work.Diff.STE.flat
