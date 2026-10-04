import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.iteratedFDeriv_fderiv_le_of_pdVec
import Submission.Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary estimates for the composition jet bound `compJetBoundLoc`

This file collects the elementary estimates that convert *bounds on the iterated partial
derivatives* (`pdRVec`, the real-valued counterpart of `pdVec`) at a point `z` into bounds on the
*iterated Fréchet derivatives* `iteratedFDeriv ℝ m` at `z`:

* `norm_iteratedFDeriv_le_of_pdRVec_bound` — scalar functions;
* `norm_iteratedFDeriv_matrix_le_of_pdRVec_bound` — matrix-valued functions (two `Pi` reductions);
* `norm_iteratedFDeriv_pdR_le_of_pdRVec_bound` — the first partial derivatives `pdR c f`;
* `norm_iteratedFDeriv_mat3_le_of_pdRVec_bound` — the triple `(c,a,b) ↦ ∂_c f_{ab}`.

The bridge between `iteratedFDeriv` (within an open set) and the iterated partial derivatives is
`Work.Diff.STE.B3.pdVecX_eq_iteratedFDerivWithin` (proved sorry-free in
`Submission/Work/Diff/STE/B3/iteratedFDeriv_fderiv_le_of_pdVec.lean`), and the basis-expansion
estimate is `Work.Diff.STE.B3.norm_multilinear_le_of_basis`.

The conversion of a `pdVec`-bound for the *complexification* `y ↦ ((f y : ℝ) : ℂ)` into a
`pdRVec`-bound for `f` is the separate lemma `Work.Diff.STE.Lead.Gal.pdVec_ofReal_eq_pdRVec`.
-/

noncomputable section

namespace Work.Diff.STE.Lead.Gal

open Filter
open scoped Topology

variable {n : ℕ}

/-! ## 1. Elementary bounds for multilinear maps -/

/-- The iterated derivatives of the identity map, of order `≥ 1`, have norm at most `1`. -/
lemma norm_iteratedFDeriv_id_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) {p : ℕ} (hp : 1 ≤ p) : ‖iteratedFDeriv ℝ p (fun y : E => y) x‖ ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := fun y : E => y) (x := x)]
  rw [Function.comp_apply, LinearIsometryEquiv.norm_map]
  have hfd : (fun y : E => fderiv ℝ (fun y : E => y) y)
      = fun _ : E => (ContinuousLinearMap.id ℝ E) := funext fun y => fderiv_id
  rw [hfd]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [norm_iteratedFDeriv_zero]
    exact ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by omega : k ≠ 0) (ContinuousLinearMap.id ℝ E)]
    simp

/-- The operator norm of a product of continuous multilinear maps is at most the sum of the
operator norms of the factors. -/
lemma norm_prod_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {m : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) G) :
    ‖T.prod S‖ ≤ ‖T‖ + ‖S‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [ContinuousMultilinearMap.prod_apply, Prod.norm_mk]
  have hprod : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hT : ‖T v‖ ≤ (‖T‖ + ‖S‖) * ∏ i, ‖v i‖ :=
    le_trans (ContinuousMultilinearMap.le_opNorm T v)
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg S)) hprod)
  have hS : ‖S v‖ ≤ (‖T‖ + ‖S‖) * ∏ i, ‖v i‖ :=
    le_trans (ContinuousMultilinearMap.le_opNorm S v)
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg T)) hprod)
  exact max_le hT hS

/-! ## 2. Value bounds from `pdRVec` bounds -/

/-- **Scalar value bound.**  If `f : 𝔼 → ℝ` is `C^∞` on the open set `v ∋ z`, and all its iterated
partial derivatives of order `≤ M` at `z` are bounded by `B ≥ 0`, then
`‖D^m f z‖ ≤ (max n 1)^M * B` for `m ≤ M`. -/
lemma norm_iteratedFDeriv_le_of_pdRVec_bound {v : Set (Fin n → ℝ)} (hv : IsOpen v)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f v)
    {z : Fin n → ℝ} (hz : z ∈ v) {M : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hpd : ∀ m ≤ M, ∀ γ : Fin m → Fin n, ‖Work.Diff.STE.pdRVec m γ f z‖ ≤ B) :
    ∀ m ≤ M, ‖iteratedFDeriv ℝ m f z‖ ≤ (max (n : ℝ) 1) ^ M * B := by
  intro m hm
  have hbasis : ∀ γ : Fin m → Fin n,
      ‖(iteratedFDeriv ℝ m f z) (fun j => Pi.single (γ j) 1)‖ ≤ B := by
    intro γ
    have hK : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) f v :=
      hf.of_le (by exact_mod_cast (le_top : ((m + 1 : ℕ) : ℕ∞) ≤ ⊤))
    have hA : Work.Diff.STE.B3.pdVecX m γ f z
        = iteratedFDeriv ℝ m f z (fun j => Pi.single (γ j) 1) := by
      rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) m hv hz]
      exact (Work.Diff.STE.B3.pdVecX_eq_iteratedFDerivWithin (v := v) hv hK m γ
        le_rfl) hz
    rw [← hA, Work.Diff.STE.B3.pdVecX_eq_pdRVec]
    exact hpd m hm γ
  calc ‖iteratedFDeriv ℝ m f z‖
      ≤ (n : ℝ) ^ m * B := Work.Diff.STE.B3.norm_multilinear_le_of_basis _ hB hbasis
    _ ≤ (max (n : ℝ) 1) ^ M * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB
        exact le_trans (pow_le_pow_left₀ (by positivity) (le_max_left _ _) m)
          (pow_le_pow_right₀ (le_max_right _ _) hm)

/-- **Matrix value bound.**  Same as the scalar bound, for a matrix-valued function, with the
`Pi`-reduction costing a factor `n^2`. -/
lemma norm_iteratedFDeriv_matrix_le_of_pdRVec_bound {v : Set (Fin n → ℝ)} (hv : IsOpen v)
    {u : (Fin n → ℝ) → (Fin n → Fin n → ℝ)}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u v)
    {z : Fin n → ℝ} (hz : z ∈ v) {M : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hpd : ∀ m ≤ M, ∀ γ : Fin m → Fin n, ∀ a b : Fin n,
      ‖Work.Diff.STE.pdRVec m γ (fun y => u y a b) z‖ ≤ B) :
    ∀ m ≤ M, ‖iteratedFDeriv ℝ m u z‖
      ≤ (n : ℝ) ^ 2 * ((max (n : ℝ) 1) ^ M * B) := by
  intro m hm
  have hz' : z ∈ v := hz
  have hua : ∀ a : Fin n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Fin n → ℝ => u y a) v :=
    fun a => contDiffOn_pi.mp hu a
  have hub : ∀ a b : Fin n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Fin n → ℝ => u y a b) v :=
    fun a b => contDiffOn_pi.mp (hua a) b
  have hC : 0 ≤ (max (n : ℝ) 1) ^ M * B := mul_nonneg (by positivity) hB
  have h1 : ‖iteratedFDeriv ℝ m u z‖
      ≤ ∑ a : Fin n, ‖iteratedFDeriv ℝ m (fun y => u y a) z‖ :=
    Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum u z m
      (hu.contDiffAt (hv.mem_nhds hz'))
  refine h1.trans ?_
  have h2 : ∀ a : Fin n, ‖iteratedFDeriv ℝ m (fun y => u y a) z‖
      ≤ ∑ b : Fin n, ‖iteratedFDeriv ℝ m (fun y => u y a b) z‖ := by
    intro a
    exact Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum (fun y => u y a) z m
      ((hua a).contDiffAt (hv.mem_nhds hz'))
  have h3 : ∀ a : Fin n, (∑ b : Fin n, ‖iteratedFDeriv ℝ m (fun y => u y a b) z‖)
      ≤ ∑ _b : Fin n, (max (n : ℝ) 1) ^ M * B := by
    intro a
    refine Finset.sum_le_sum fun b _ => ?_
    exact norm_iteratedFDeriv_le_of_pdRVec_bound hv (hub a b) hz' hB
      (fun m' hm' γ => hpd m' hm' γ a b) m hm
  calc ∑ a : Fin n, ‖iteratedFDeriv ℝ m (fun y => u y a) z‖
      ≤ ∑ _a : Fin n, ∑ _b : Fin n, (max (n : ℝ) 1) ^ M * B :=
        Finset.sum_le_sum fun a _ => (h2 a).trans (h3 a)
    _ = (n : ℝ) ^ 2 * ((max (n : ℝ) 1) ^ M * B) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring

/-- **First-jet value bound.**  The `m`-th (`m ≤ M`) iterated derivative of the first partial
derivative `∂_c f` is bounded by `(max n 1)^(M+1) * B`, provided all iterated partial derivatives
of `f` of order `≤ M + 1` at `z` are bounded by `B ≥ 0`. -/
lemma norm_iteratedFDeriv_pdR_le_of_pdRVec_bound {v : Set (Fin n → ℝ)} (hv : IsOpen v)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f v)
    {z : Fin n → ℝ} (hz : z ∈ v) {M : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (c : Fin n)
    (hpd : ∀ m ≤ M + 1, ∀ γ : Fin m → Fin n, ‖Work.Diff.STE.pdRVec m γ f z‖ ≤ B) :
    ∀ m ≤ M, ‖iteratedFDeriv ℝ m (Work.Diff.STE.pdR c f) z‖ ≤ (max (n : ℝ) 1) ^ (M + 1) * B := by
  intro m hm
  have hbasis : ∀ γ : Fin m → Fin n,
      ‖(iteratedFDeriv ℝ m (Work.Diff.STE.pdR c f) z) (fun j => Pi.single (γ j) 1)‖ ≤ B := by
    intro γ
    have hK2 : ContDiffOn ℝ (((m + 1 : ℕ)) : WithTop ℕ∞) (Work.Diff.STE.pdR c f) v :=
      Work.Diff.STE.B3.contDiffOn_pdR hv (K := m + 1)
        (hf.of_le (by exact_mod_cast (le_top : ((m + 2 : ℕ) : ℕ∞) ≤ ⊤))) c
    have hA : Work.Diff.STE.B3.pdVecX m γ (Work.Diff.STE.pdR c f) z
        = iteratedFDeriv ℝ m (Work.Diff.STE.pdR c f) z (fun j => Pi.single (γ j) 1) := by
      rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := Work.Diff.STE.pdR c f) m hv hz]
      exact (Work.Diff.STE.B3.pdVecX_eq_iteratedFDerivWithin (v := v) hv hK2 m γ le_rfl) hz
    rw [← hA, Work.Diff.STE.B3.pdVecX_eq_pdRVec,
      Work.Diff.STE.B3.pdRVec_pdR_eq_pdRVec_snoc]
    exact hpd (m + 1) (by omega) (Fin.snoc γ c)
  calc ‖iteratedFDeriv ℝ m (Work.Diff.STE.pdR c f) z‖
      ≤ (n : ℝ) ^ m * B := Work.Diff.STE.B3.norm_multilinear_le_of_basis _ hB hbasis
    _ ≤ (max (n : ℝ) 1) ^ (M + 1) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB
        exact le_trans (pow_le_pow_left₀ (by positivity) (le_max_left _ _) m)
          (pow_le_pow_right₀ (le_max_right _ _) (by omega))

/-- **Triple first-jet bound.**  The map `y ↦ (c,a,b) ↦ ∂_c (u · a b) y` into `Fin n → Fin n →
Fin n → ℝ` has its `m`-th (`m ≤ M`) iterated derivative at `z` bounded by
`n^3 * (max n 1)^(M+1) * B`, provided the iterated partial derivatives of the entries `u · a b`
of order `≤ M + 1` at `z` are bounded by `B ≥ 0`. -/
lemma norm_iteratedFDeriv_mat3_le_of_pdRVec_bound {v : Set (Fin n → ℝ)} (hv : IsOpen v)
    {u : (Fin n → ℝ) → (Fin n → Fin n → ℝ)}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u v)
    {z : Fin n → ℝ} (hz : z ∈ v) {M : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hpd : ∀ m ≤ M + 1, ∀ γ : Fin m → Fin n, ∀ a b : Fin n,
      ‖Work.Diff.STE.pdRVec m γ (fun y => u y a b) z‖ ≤ B) :
    ∀ m ≤ M, ‖iteratedFDeriv ℝ m
        (fun y : Fin n → ℝ => fun c a b : Fin n => Work.Diff.STE.pdR c (fun w => u w a b) y) z‖
      ≤ (n : ℝ) ^ 3 * ((max (n : ℝ) 1) ^ (M + 1) * B) := by
  intro m hm
  have hz' : z ∈ v := hz
  have hua : ∀ a : Fin n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Fin n → ℝ => u y a) v := fun a => contDiffOn_pi.mp hu a
  have hub : ∀ a b : Fin n, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Fin n → ℝ => u y a b) v := fun a b => contDiffOn_pi.mp (hua a) b
  -- smoothness at `z` of the first partial derivatives of the entries
  have hF : ∀ a b : Fin n, ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => u y a b) z :=
    fun a b => (contDiffAt_pi.mp (contDiffAt_pi.mp (hu.contDiffAt (hv.mem_nhds hz')) a)) b
  have hD : ∀ c a b : Fin n, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : Fin n → ℝ => Work.Diff.STE.pdR c (fun w => u w a b) y) z := by
    intro c a b
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fderiv ℝ (fun y : Fin n → ℝ => u y a b)) z :=
      (hF a b).fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    have h2 := h1.clm_apply
      (contDiffAt_const (c := ((Pi.single c (1 : ℝ)) : Fin n → ℝ)))
    simpa only [Work.Diff.STE.pdR] using h2
  set C1 : ℝ := (max (n : ℝ) 1) ^ (M + 1) * B with hC1def
  have hterm : ∀ c a b : Fin n,
      ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdR c (fun w => u w a b) y) z‖ ≤ C1 :=
    fun c a b => norm_iteratedFDeriv_pdR_le_of_pdRVec_bound hv (hub a b) hz hB c
      (fun m' hm' γ => hpd m' hm' γ a b) m hm
  -- three successive `Pi` reductions
  have h1 : ‖iteratedFDeriv ℝ m
        (fun y : Fin n → ℝ => fun c a b : Fin n => Work.Diff.STE.pdR c (fun w => u w a b) y) z‖
      ≤ ∑ c : Fin n, ‖iteratedFDeriv ℝ m
          (fun y : Fin n → ℝ => fun a b : Fin n =>
            Work.Diff.STE.pdR c (fun w => u w a b) y) z‖ := by
    refine Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum _ z m ?_
    exact contDiffAt_pi.mpr fun c => contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b =>
      hD c a b
  calc ‖iteratedFDeriv ℝ m
        (fun y : Fin n → ℝ => fun c a b : Fin n => Work.Diff.STE.pdR c (fun w => u w a b) y) z‖
      ≤ ∑ c : Fin n, ‖iteratedFDeriv ℝ m
          (fun y : Fin n → ℝ => fun a b : Fin n =>
            Work.Diff.STE.pdR c (fun w => u w a b) y) z‖ := h1
    _ ≤ ∑ c : Fin n, ∑ a : Fin n, ∑ b : Fin n, C1 := by
        refine Finset.sum_le_sum fun c _ => ?_
        have h2a : ‖iteratedFDeriv ℝ m
            (fun y : Fin n → ℝ => fun a b : Fin n =>
              Work.Diff.STE.pdR c (fun w => u w a b) y) z‖
          ≤ ∑ a : Fin n, ‖iteratedFDeriv ℝ m
              (fun y : Fin n → ℝ => fun b : Fin n =>
                Work.Diff.STE.pdR c (fun w => u w a b) y) z‖ :=
          Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum _ z m
            (contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => hD c a b)
        refine h2a.trans (Finset.sum_le_sum fun a _ => ?_)
        have h2b : ‖iteratedFDeriv ℝ m
            (fun y : Fin n → ℝ => fun b : Fin n =>
              Work.Diff.STE.pdR c (fun w => u w a b) y) z‖
          ≤ ∑ b : Fin n, ‖iteratedFDeriv ℝ m
              (fun y => Work.Diff.STE.pdR c (fun w => u w a b) y) z‖ :=
          Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum _ z m
            (contDiffAt_pi.mpr fun b => hD c a b)
        exact h2b.trans (Finset.sum_le_sum fun b _ => hterm c a b)
    _ = (n : ℝ) ^ 3 * ((max (n : ℝ) 1) ^ (M + 1) * B) := by
        rw [hC1def, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring

/-! ## 4. The real/complex bridge for the iterated partial derivatives -/

/-- Global smoothness of the first partial derivative `pdR c f` of a smooth function. -/
lemma contDiff_pdR_top {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (c : Fin n) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Diff.STE.pdR c f) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  exact h1.clm_apply (contDiff_const (c := (Pi.single c (1 : ℝ) : Fin n → ℝ)))

/-- **One-step real/complex bridge.**  The partial derivative of the complexification of a
real-valued function is the complexification of its partial derivative (as functions). -/
lemma pdX_ofReal_eq (i : Fin n) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.B3.pdX i (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.B3.pdX i f x : ℝ) : ℂ) := by
  have key : ∀ x : Fin n → ℝ,
      fderiv ℝ (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) x
        = Complex.ofRealCLM ∘SL (fderiv ℝ f x) := by
    intro x
    by_cases hf : DifferentiableAt ℝ f x
    · have h1 : HasFDerivAt (fun y : Fin n → ℝ => Complex.ofRealCLM (f y))
          (Complex.ofRealCLM ∘SL fderiv ℝ f x) x :=
        (Complex.ofRealCLM.hasFDerivAt).comp x hf.hasFDerivAt
      have h2 : HasFDerivAt (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
          (Complex.ofRealCLM ∘SL fderiv ℝ f x) x := h1
      exact h2.fderiv
    · have hnf : ¬ DifferentiableAt ℝ (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) x := by
        intro h
        refine hf ?_
        have h2 : DifferentiableAt ℝ (fun y : Fin n → ℝ =>
            Complex.reCLM (((f y : ℝ) : ℂ))) x :=
          Complex.reCLM.differentiableAt.comp x h
        exact h2.congr_of_eventuallyEq
          (Filter.EventuallyEq.of_eq (funext fun y => Complex.ofReal_re (f y)))
      rw [fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt hnf]
      simp
  funext x
  simp only [Work.Diff.STE.B3.pdX]
  rw [key x]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]

/-- **Iterated real/complex bridge.** -/
lemma pdVecX_ofReal_eq {k : ℕ} (γ : Fin k → Fin n) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.B3.pdVecX k γ (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.B3.pdVecX k γ f x : ℝ) : ℂ) := by
  have h : ∀ l : List (Fin n),
      List.foldr (fun (i : Fin n) (g : (Fin n → ℝ) → ℂ) => Work.Diff.STE.B3.pdX i g)
          (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) l
        = fun x : Fin n → ℝ =>
          ((List.foldr (fun (i : Fin n) (g : (Fin n → ℝ) → ℝ) =>
            Work.Diff.STE.B3.pdX i g) f l x : ℝ) : ℂ) := by
    intro l
    induction l with
    | nil => rfl
    | cons i t ih =>
        simp only [List.foldr_cons]
        rw [ih]
        exact pdX_ofReal_eq i (List.foldr (fun (i : Fin n) (g : (Fin n → ℝ) → ℝ) =>
          Work.Diff.STE.B3.pdX i g) f t)
  simpa only [Work.Diff.STE.B3.pdVecX] using h (List.ofFn γ)

/-! ## 5. Locality of the iterated partial derivatives -/

/-- The partial derivative of functions that agree near a point agree near that point. -/
lemma pdX_eventuallyEq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : (Fin n → ℝ) → F} {x : Fin n → ℝ} (h : f =ᶠ[nhds x] g) (i : Fin n) :
    Work.Diff.STE.B3.pdX i f =ᶠ[nhds x] Work.Diff.STE.B3.pdX i g := by
  obtain ⟨U, hU, hUopen, hxU⟩ := eventually_nhds_iff.mp h
  filter_upwards [hUopen.mem_nhds hxU] with y hy
  simp only [Work.Diff.STE.B3.pdX]
  exact congrArg (fun (L : (Fin n → ℝ) →L[ℝ] F) => L (Pi.single i 1))
    (Filter.EventuallyEq.fderiv_eq (eventually_nhds_iff.mpr ⟨U, hU, hUopen, hy⟩))

/-- Locality of the iterated partial derivatives along a list. -/
lemma pdListX_eventuallyEq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : List (Fin n)) {f g : (Fin n → ℝ) → F} {x : Fin n → ℝ}
    (h : f =ᶠ[nhds x] g) :
    List.foldr (fun (i : Fin n) (g : (Fin n → ℝ) → F) => Work.Diff.STE.B3.pdX i g) f l
      =ᶠ[nhds x]
      List.foldr (fun (i : Fin n) (g : (Fin n → ℝ) → F) => Work.Diff.STE.B3.pdX i g) g l := by
  induction l with
  | nil => exact h
  | cons i t ih => simpa only [List.foldr_cons] using pdX_eventuallyEq ih i

/-- Locality of the iterated partial derivatives `pdVecX`. -/
lemma pdVecX_eventuallyEq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} (γ : Fin k → Fin n) {f g : (Fin n → ℝ) → F} {x : Fin n → ℝ}
    (h : f =ᶠ[nhds x] g) :
    Work.Diff.STE.B3.pdVecX k γ f =ᶠ[nhds x] Work.Diff.STE.B3.pdVecX k γ g :=
  pdListX_eventuallyEq (List.ofFn γ) h

/-- Pointwise form of `pdVecX_eventuallyEq`. -/
lemma pdVecX_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} (γ : Fin k → Fin n) {f g : (Fin n → ℝ) → F} {x : Fin n → ℝ}
    (h : f =ᶠ[nhds x] g) :
    Work.Diff.STE.B3.pdVecX k γ f x = Work.Diff.STE.B3.pdVecX k γ g x :=
  (pdVecX_eventuallyEq γ h).eq_of_nhds

/-! ## 6. Smoothing against a bump supported in an open set -/

/-- If `f` is `C^∞` on the open set `U` and the closed support of `φ` lies in `U`, then
`z ↦ φ z • f z` is `C^∞` everywhere. -/
lemma contDiff_smul_of_tsupport_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {φ : E → ℝ} {f : E → F}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f U)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hsupp : tsupport φ ⊆ U) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ z • f z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · exact hφ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hz))
  · have hz' : z ∉ tsupport φ := fun h => hz (hsupp h)
    have hφ0 : φ =ᶠ[nhds z] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hz'] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have h0 : (fun z => φ z • f z) =ᶠ[nhds z] fun _ => (0 : F) := by
      filter_upwards [hφ0] with y hy
      rw [hy, zero_smul]
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq h0

end Work.Diff.STE.Lead.Gal
