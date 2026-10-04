import Mathlib
import Submission.Work.Diff.STE.flat.uniqueness_energy_ineq
import Submission.Work.Diff.STE.flat.antisymN_defs
import Submission.Work.Diff.STE.flat.antisymN_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat
open Set

/-!
## Roadmap

`N` is smooth on the open set `univ ×ˢ {det (reMat ·) ≠ 0}` and its value is *symmetric* whenever
the point `(A,L)` is symmetric (hypothesis `hsymN`).  Claim: the antisymmetrised value
`A ↦ N (x,(A,L)) i j - N (x,(A,L)) j i` is bounded by the "size of the antisymmetric part",
i.e. by `Σ_{ij} ‖A i j - A j i‖ + Σ_{cij} ‖L c i j - L c j i‖`, uniformly on the compact cube of
`x`'s, over the region where `reMat A` has positive-definite quadratic form and the entries are
bounded by `M`.

The proof (Schwarz/Hadamard/mean value) is carried out in the product space
`(Fin n → ℝ) × (MatC n × (Fin n → MatC n))`, and runs as follows.

* `symMat A = (A + Aᵀ)/2` is symmetric, has the same quadratic form as `A` and satisfies the same
  entry bounds (`antisymN_aux`); hence `symPair (A,L) = (symMat A, symMat ∘ L)` satisfies the
  hypotheses of `hsymN` (with `det ≠ 0` supplied by `det_ne_zero_of_quadForm_bound`, which is the
  local copy of `det_ne_zero_of_quadForm_le` avoiding the constant clash with `torus_uniqueness`).
* The region `posSet M lam` of pairs with entries bounded by `M` and quadratic form `≥ lam * ‖·‖²`
  is closed, bounded by the ball of radius `M`, convex, and contained in the domain of `N`
  (`antisymN_aux`), hence compact; `cubeN ×ˢ posSet M lam` is a compact subset of the open domain
  of `N`.
* `ContDiffOn.continuousOn_fderiv_of_isOpen` gives continuity of `fderiv ℝ N` on that open domain,
  so `IsCompact.exists_bound_of_continuousOn` bounds its norm on the compact region by some `C₀`.
* `Convex.norm_image_sub_le_of_norm_fderiv_le` applied to `N` on `cubeN ×ˢ posSet M lam` gives
  `‖N (x,(A,L)) - N (x,symPair (A,L))‖ ≤ C₀ * ‖(A,L) - symPair (A,L)‖`.
* Since `N (x,symPair (A,L))` is symmetric, the antisymmetrised value is a difference of two
  entries of `N (x,(A,L)) - N (x,symPair (A,L))`, and the (sup) norm of a matrix is at most the
  sum of the norms of its entries; finally `‖(A,L) - symPair (A,L)‖` is bounded by the sum of the
  sizes of the antisymmetric parts (`‖(A - symMat A) i j‖ = ‖A i j - A j i‖/2`).

The constants are `C = 2 n² max C₀ 0`.
-/

theorem antisymN_bound {n : ℕ} (hn : 1 ≤ n)
    (N : (Fin n → ℝ) × (Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n)) →
      Work.Diff.STE.Flat.MatC n)
    (hNsm : ContDiffOn ℝ (⊤ : ℕ∞) N
      (Set.univ ×ˢ {w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n) |
        (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}))
    (hsymN : ∀ (x : Fin n → ℝ) (A : Work.Diff.STE.Flat.MatC n)
        (L : Fin n → Work.Diff.STE.Flat.MatC n),
      (Work.Diff.STE.Flat.reMat A).det ≠ 0 → (∀ i j, A i j = A j i) →
      (∀ c i j, L c i j = L c j i) → ∀ i j, N (x, (A, L)) i j = N (x, (A, L)) j i)
    (M lam : ℝ) (hM : 0 ≤ M) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Fin n → ℝ), x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc 0 1) →
      ∀ (A : Work.Diff.STE.Flat.MatC n) (L : Fin n → Work.Diff.STE.Flat.MatC n),
      (∀ i j, ‖A i j‖ ≤ M) →
      (∀ c i j, ‖(L c) i j‖ ≤ M) →
      (∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤
        ∑ i, ∑ j, Work.Diff.STE.Flat.reMat A i j * ξ i * ξ j) →
      ‖fun i j => N (x, (A, L)) i j - N (x, (A, L)) j i‖ ≤
        C * ((∑ i, ∑ j, ‖A i j - A j i‖) + (∑ c, ∑ i, ∑ j, ‖L c i j - L c j i‖)) := by
  -- ## 1. the domain of `N` is open
  have hdetcont : Continuous (fun w : MatC n × (Fin n → MatC n) => (reMat w.1).det) := by
    refine Continuous.matrix_det ?_
    refine continuous_pi (fun i => continuous_pi (fun j => ?_))
    exact Complex.continuous_re.comp
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))
  have hUopen : IsOpen (detNeZeroSet (n := n)) := by
    have hcl : IsClosed {w : MatC n × (Fin n → MatC n) | (reMat w.1).det = 0} :=
      isClosed_eq hdetcont continuous_const
    have hsub : detNeZeroSet (n := n) =
        {w : MatC n × (Fin n → MatC n) | (reMat w.1).det = 0}ᶜ := by
      ext w; simp [detNeZeroSet, Set.mem_compl_iff]
    rw [hsub]; exact hcl.isOpen_compl
  have hDopen : IsOpen (domN (n := n)) :=
    isOpen_univ.prod hUopen
  -- ## 2. the admissible region
  have hPcomp : IsCompact (posSet (n := n) M lam) := posSet_isCompact M lam hM
  have hPconv : Convex ℝ (posSet (n := n) M lam) := posSet_convex M lam
  have hPsub : posSet (n := n) M lam ⊆ detNeZeroSet (n := n) := posSet_subset_detNeZero M lam hlam
  -- ## 3. compactness of `cube × posSet`
  have hKcomp : IsCompact (cubeN (n := n) ×ˢ posSet (n := n) M lam) :=
    (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc)).prod hPcomp
  have hKsub : cubeN (n := n) ×ˢ posSet (n := n) M lam ⊆ domN (n := n) :=
    fun p hp => ⟨trivial, hPsub hp.2⟩
  -- ## 4. the uniform bound on the derivative
  have hcont_fderiv : ContinuousOn
      (fun p : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) => fderiv ℝ N p)
      (domN (n := n)) :=
    hNsm.continuousOn_fderiv_of_isOpen hDopen
      (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C₀, hC₀⟩ := hKcomp.exists_bound_of_continuousOn (hcont_fderiv.norm.mono hKsub)
  have hC₀' : ∀ p ∈ cubeN (n := n) ×ˢ posSet (n := n) M lam,
      ‖fderiv ℝ N p‖ ≤ C₀ := fun p hp => by simpa using hC₀ p hp
  refine ⟨2 * (n:ℝ) * (n:ℝ) * max C₀ 0, by positivity, ?_⟩
  intro x hx A L hA hL hq
  -- ## 5. the two points of the admissible region
  have hmem : (A, L) ∈ posSet (n := n) M lam := ⟨hA, hL, fun ξ => hq ξ⟩
  have hsymA : ∀ i j, symMat A i j = symMat A j i := symMat_symm A
  have hquadA : ∀ ξ : Fin n → ℝ, quadForm (symMat A) ξ = quadForm A ξ := quadForm_symMat A
  have hmem' : symPair (A, L) ∈ posSet (n := n) M lam := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      exact le_trans (norm_symMat_le A i j) (by linarith [hA i j, hA j i])
    · intro c i j
      exact le_trans (norm_symMat_le (L c) i j) (by linarith [hL c i j, hL c j i])
    · intro ξ
      show lam * ∑ i, (ξ i) ^ 2 ≤ quadForm (symMat A) ξ
      rw [hquadA ξ]; exact hq ξ
  have hx' : x ∈ cubeN (n := n) := hx
  have hp1 : (x, (A, L)) ∈ cubeN (n := n) ×ˢ posSet (n := n) M lam := ⟨hx', hmem⟩
  have hp2 : (x, symPair (A, L)) ∈ cubeN (n := n) ×ˢ posSet (n := n) M lam := ⟨hx', hmem'⟩
  -- ## 6. differentiability on the region and the mean value theorem
  have hdiff : ∀ p ∈ cubeN (n := n) ×ˢ posSet (n := n) M lam, DifferentiableAt ℝ N p := by
    intro p hp
    have hpD : p ∈ domN (n := n) := ⟨trivial, hPsub hp.2⟩
    exact (hNsm.contDiffAt (hDopen.mem_nhds hpD)).differentiableAt (by simp)
  have hMVT : ‖N (x, (A, L)) - N (x, symPair (A, L))‖ ≤
      C₀ * ‖(A, L) - symPair (A, L)‖ := by
    have hKconv : Convex ℝ (cubeN (n := n) ×ˢ posSet (n := n) M lam) :=
      (convex_pi (𝕜 := ℝ) (fun _ _ => convex_Icc (0:ℝ) 1)).prod hPconv
    have hmain := Convex.norm_image_sub_le_of_norm_fderiv_le (f := N) hdiff hC₀' hKconv hp2 hp1
    have hnorm : ‖(x, (A, L)) - (x, symPair (A, L))‖ = ‖(A, L) - symPair (A, L)‖ := by
      rw [Prod.norm_def, Prod.mk_sub_mk, sub_self, norm_zero,
        max_eq_right (norm_nonneg ((A, L) - symPair (A, L)))]
    rwa [hnorm] at hmain
  -- ## 7. symmetry of `N` at the symmetrised point
  have hdet' : (reMat (symMat A)).det ≠ 0 := by
    refine det_ne_zero_of_quadForm_bound (reMat (symMat A)) hlam (fun v => ?_)
    have h1 : lam * ∑ i, (v i) ^ 2 ≤ quadForm (symMat A) v := by
      rw [hquadA v]; exact hq v
    simpa [quadForm] using h1
  have hsym' : ∀ i j, N (x, symPair (A, L)) i j = N (x, symPair (A, L)) j i :=
    hsymN x (symMat A) (fun c => symMat (L c)) hdet' (fun i j => hsymA i j)
      (fun c i j => symMat_symm (L c) i j)
  -- ## 8. the estimate
  set Dm : MatC n := N (x, (A, L)) - N (x, symPair (A, L)) with hDm
  have hentry : ∀ i j, N (x, (A, L)) i j - N (x, (A, L)) j i = Dm i j - Dm j i := by
    intro i j
    rw [hDm]
    simp only [Pi.sub_apply]
    rw [hsym' i j]
    ring
  have h1 : ‖fun i j => Dm i j - Dm j i‖ ≤ ∑ i, ∑ j, ‖Dm i j - Dm j i‖ :=
    norm_le_sum_norm_matC (fun i j => Dm i j - Dm j i)
  have h2 : ∑ i, ∑ j, ‖Dm i j - Dm j i‖ ≤ 2 * (n:ℝ) * (n:ℝ) * ‖Dm‖ := by
    have hb : ∀ i j : Fin n, ‖Dm i j - Dm j i‖ ≤ 2 * ‖Dm‖ := fun i j =>
      calc ‖Dm i j - Dm j i‖ ≤ ‖Dm i j‖ + ‖Dm j i‖ := norm_sub_le _ _
        _ ≤ ‖Dm‖ + ‖Dm‖ :=
            add_le_add (norm_entry_le_norm_matC Dm i j) (norm_entry_le_norm_matC Dm j i)
        _ = 2 * ‖Dm‖ := by ring
    calc ∑ i, ∑ j, ‖Dm i j - Dm j i‖ ≤ ∑ i, ∑ j, (2 * ‖Dm‖) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
      _ = 2 * (n:ℝ) * (n:ℝ) * ‖Dm‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have h3 : ‖Dm‖ ≤ C₀ * ‖(A, L) - symPair (A, L)‖ := by
    rw [hDm]; exact hMVT
  have h4 : ‖(A, L) - symPair (A, L)‖ ≤
      (∑ i, ∑ j, ‖A i j - A j i‖) + (∑ c, ∑ i, ∑ j, ‖L c i j - L c j i‖) := by
    have hfst : ‖((A, L) - symPair (A, L)).1‖ ≤ ∑ i, ∑ j, ‖A i j - A j i‖ := by
      show ‖A - symMat A‖ ≤ ∑ i, ∑ j, ‖A i j - A j i‖
      calc ‖A - symMat A‖ ≤ ∑ i, ∑ j, ‖(A - symMat A) i j‖ := norm_le_sum_norm_matC _
        _ = ∑ i, ∑ j, ‖A i j - A j i‖ / 2 := by
              refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
              simp only [Pi.sub_apply]
              exact norm_sub_symMat A i j
        _ ≤ ∑ i, ∑ j, ‖A i j - A j i‖ := by
              refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
              linarith [norm_nonneg (A i j - A j i)]
    have hsnd : ‖((A, L) - symPair (A, L)).2‖ ≤ ∑ c, ∑ i, ∑ j, ‖L c i j - L c j i‖ := by
      show ‖(fun c => L c - symMat (L c))‖ ≤ ∑ c, ∑ i, ∑ j, ‖L c i j - L c j i‖
      calc ‖(fun c => L c - symMat (L c))‖
          ≤ ∑ c, ∑ i, ∑ j, ‖(fun c' => L c' - symMat (L c')) c i j‖ :=
            norm_le_sum_norm_pi_matC _
        _ ≤ ∑ c, ∑ i, ∑ j, ‖L c i j - L c j i‖ := by
              refine Finset.sum_le_sum (fun c _ =>
                Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_)))
              have hgoal : ‖(fun c' => L c' - symMat (L c')) c i j‖ = ‖L c i j - L c j i‖ / 2 :=
                norm_sub_symMat (L c) i j
              rw [hgoal]; linarith [norm_nonneg (L c i j - L c j i)]
    rw [Prod.norm_def]
    exact max_le (le_trans hfst (le_add_of_nonneg_right (Finset.sum_nonneg (fun c _ =>
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg _))))))
      (le_trans hsnd (le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => norm_nonneg _)))))
  calc ‖fun i j => N (x, (A, L)) i j - N (x, (A, L)) j i‖
      = ‖fun i j => Dm i j - Dm j i‖ := by
        congr 1
        funext i j
        exact hentry i j
    _ ≤ ∑ i, ∑ j, ‖Dm i j - Dm j i‖ := h1
    _ ≤ 2 * (n:ℝ) * (n:ℝ) * ‖Dm‖ := h2
    _ ≤ 2 * (n:ℝ) * (n:ℝ) * (max C₀ 0 * ‖(A, L) - symPair (A, L)‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact le_trans h3 (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (norm_nonneg _))
    _ = (2 * (n:ℝ) * (n:ℝ) * max C₀ 0) * ‖(A, L) - symPair (A, L)‖ := by ring
    _ ≤ (2 * (n:ℝ) * (n:ℝ) * max C₀ 0) *
        ((∑ i, ∑ j, ‖A i j - A j i‖) + (∑ c, ∑ i, ∑ j, ‖L c i j - L c j i‖)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

end Work.Diff.STE.flat
