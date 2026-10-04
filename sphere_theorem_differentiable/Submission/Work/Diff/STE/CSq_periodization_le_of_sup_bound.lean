import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.pd_periodization
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The periodization of a cube-supported smooth function: an `Hᵏ` bound from a sup bound

Layer B of the STE development (`DESIGN.md`): the "sup-bound comparison".  It converts a
*pointwise* bound on the iterated partial derivatives of a smooth function `f` supported in the
open unit cube `(-1/2, 1/2)^ι` into a bound for the weighted `ℓ²` norm of the Fourier
coefficients of the periodization `P y = ∑' n : ι → ℤ, f (y + n)`.

The main theorem is `CSq_periodization_le_of_sup_bound`: a constant `C` depending only on `k`
and `ι` satisfies `CSq k (fourierCoeff P) ≤ C * M ^ 2` whenever `‖∂^l f‖ ≤ M` for every
`l : Fin k → ι`.

## Ingredients

1. **The periodization is locally a finite sum of translates.**  On the open box `(-1/4, 5/4)^ι`
   — a neighbourhood of the closed unit cube — every lattice vector `n` with `f (y + n) ≠ 0` has
   all coordinates in `{-1, 0}`, so the `tsum` defining `P` reduces to the finite sum over the box
   `csqp_boxIdx ι = ∏ᵢ {-1, 0}` (`csqp_periodization_eq_sum_boxIdx`).  This holds on a
   neighbourhood of *every* point of the closed unit cube, which is what the derivative
   congruence `csqp_pdList_congr` needs.

2. **Derivatives of the periodization.**  `pdList` is compatible with eventual equality, with
   translations of the argument and with finite sums, so on the closed unit cube `∂^l P` is the
   sum of the `2 ^{card ι}` translates `∂^l f (· + n)` (`csqp_pdVec_periodization_le`); hence
   `‖∂^l P‖ ≤ 2 ^{card ι} M` there and Bessel's inequality (`CSq_le_ENormSq`) gives
   `CSq k (fourierCoeff P) ≤ 2 ^k (ENormSq k P + ENormSq 0 P)`.

3. **A Poincaré bound for the zeroth order term.**  The hypothesis bounds only the *top* order
   `k` derivatives of `f`, but `f` is compactly supported in the cube, so all lower order
   derivatives are controlled as well (`csqp_pdVec_le_of_pdVec_bound`: one-dimensional mean value
   theorem, plus the fact that the support of every iterated derivative lies in the closed cube).
   In particular `‖f‖ ≤ C M`, and this bounds `ENormSq 0 P`.
-/

noncomputable section

namespace Work.Diff.STE

set_option maxHeartbeats 1000000

open MeasureTheory BigOperators Filter
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. `pd` and `pdList`: congruence, translation and finite sums -/

/-- If two functions agree in a neighbourhood of `x`, so do their partial derivatives `pd i`. -/
lemma csqp_pd_eventuallyEq {g h : (ι → ℝ) → ℂ} {x : ι → ℝ} (i : ι)
    (hgh : g =ᶠ[𝓝 x] h) : pd i g =ᶠ[𝓝 x] pd i h := by
  filter_upwards [hgh.fderiv (𝕜 := ℝ)] with y hy
  simp only [pd]
  rw [hy]

/-- If two functions agree in a neighbourhood of `x`, so do all their iterated partial
derivatives (as functions, near `x`). -/
lemma csqp_pdList_eventuallyEq (l : List ι) {g h : (ι → ℝ) → ℂ} {x : ι → ℝ}
    (hgh : g =ᶠ[𝓝 x] h) : pdList l g =ᶠ[𝓝 x] pdList l h := by
  induction l with
  | nil => exact hgh
  | cons i t ih =>
      have h2 : pd i (pdList t g) =ᶠ[𝓝 x] pd i (pdList t h) := csqp_pd_eventuallyEq i ih
      simpa only [pdList, List.foldr_cons] using h2

/-- If two functions agree in a neighbourhood of `x`, their iterated partial derivatives agree
at `x`. -/
lemma csqp_pdList_congr (l : List ι) {g h : (ι → ℝ) → ℂ} {x : ι → ℝ}
    (hgh : g =ᶠ[𝓝 x] h) : pdList l g x = pdList l h x :=
  (csqp_pdList_eventuallyEq l hgh).eq_of_nhds

/-- `Fin`-indexed version of `csqp_pdList_congr`. -/
lemma csqp_pdVec_congr {j : ℕ} (l : Fin j → ι) {g h : (ι → ℝ) → ℂ} {x : ι → ℝ}
    (hgh : g =ᶠ[𝓝 x] h) : pdVec j l g x = pdVec j l h x :=
  csqp_pdList_congr (List.ofFn l) hgh

/-- `pdList` of a smooth function is smooth. -/
lemma csqp_contDiff_pdList_top (l : List ι) {f : (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (pdList l f) := by
  induction l with
  | nil => simpa [pdList] using hf
  | cons i t ih =>
      have h2 : ContDiff ℝ (⊤ : ℕ∞) (pd i (pdList t f)) := ste_contDiff_pd i ih
      simpa only [pdList, List.foldr_cons] using h2

/-- Translation of the argument commutes with `pdList`. -/
lemma csqp_pdList_comp_add_right (l : List ι) (g : (ι → ℝ) → ℂ) (c x : ι → ℝ) :
    pdList l (fun y => g (y + c)) x = pdList l g (x + c) := by
  induction l generalizing x with
  | nil => rfl
  | cons i t ih =>
      have hfun : pdList t (fun z => g (z + c)) = fun y => pdList t g (y + c) :=
        funext fun y => ih y
      change pd i (pdList t (fun z => g (z + c))) x = pd i (pdList t g) (x + c)
      rw [hfun]
      simp only [pd, fderiv_comp_add_right]

/-- `Fin`-indexed version of `csqp_pdList_comp_add_right`. -/
lemma csqp_pdVec_comp_add_right {j : ℕ} (l : Fin j → ι) (g : (ι → ℝ) → ℂ) (c x : ι → ℝ) :
    pdVec j l (fun y => g (y + c)) x = pdVec j l g (x + c) :=
  csqp_pdList_comp_add_right (List.ofFn l) g c x

/-- Iterated partial derivatives are additive over finite sums of smooth functions. -/
lemma csqp_pdList_finset_sum {α : Type*} (l : List ι) (u : Finset α) (G : α → (ι → ℝ) → ℂ)
    (x : ι → ℝ) (hG : ∀ m ∈ u, ContDiff ℝ (⊤ : ℕ∞) (G m)) :
    pdList l (fun y => ∑ m ∈ u, G m y) x = ∑ m ∈ u, pdList l (G m) x := by
  have hcd : ∀ (t : List ι) (m : α), m ∈ u → ContDiff ℝ (⊤ : ℕ∞) (pdList t (G m)) :=
    fun t m hm => csqp_contDiff_pdList_top t (hG m hm)
  induction l generalizing x with
  | nil => simp [pdList]
  | cons i t ih =>
      have hsumfun : pdList t (fun z => ∑ m ∈ u, G m z) = fun y => ∑ m ∈ u, pdList t (G m) y :=
        funext fun y => ih y
      change pd i (pdList t (fun z => ∑ m ∈ u, G m z)) x = ∑ m ∈ u, pd i (pdList t (G m)) x
      rw [hsumfun]
      simp only [pd]
      rw [fderiv_fun_sum (fun m hm => ((hcd t m hm).differentiable (by simp)).differentiableAt),
        ContinuousLinearMap.sum_apply]

/-- `Fin`-indexed version of `csqp_pdList_finset_sum`. -/
lemma csqp_pdVec_finset_sum {α : Type*} {j : ℕ} (l : Fin j → ι) (u : Finset α)
    (G : α → (ι → ℝ) → ℂ) (x : ι → ℝ)
    (hG : ∀ m ∈ u, ContDiff ℝ (⊤ : ℕ∞) (G m)) :
    pdVec j l (fun y => ∑ m ∈ u, G m y) x = ∑ m ∈ u, pdVec j l (G m) x :=
  csqp_pdList_finset_sum (List.ofFn l) u G x hG

/-! ## 2. The box of contributing lattice vectors -/

/-- The lattice vectors all of whose coordinates lie in `{-1, 0}`.  These are the only
translations that can meet the open unit cube, hence the only ones contributing to the
periodization near the cube. -/
def csqp_boxIdx (ι : Type*) [Fintype ι] [DecidableEq ι] : Finset (ι → ℤ) :=
  Fintype.piFinset (fun _ : ι => Finset.Icc (-1 : ℤ) 0)

lemma csqp_mem_boxIdx {n : ι → ℤ} :
    n ∈ csqp_boxIdx ι ↔ ∀ i : ι, n i ∈ Finset.Icc (-1 : ℤ) 0 := by
  simp [csqp_boxIdx]

lemma csqp_card_boxIdx : (csqp_boxIdx ι).card = 2 ^ Fintype.card ι := by
  have h : ∀ i : ι, (Finset.Icc (-1 : ℤ) 0).card = 2 := by
    intro i
    rw [Int.card_Icc]
    norm_num
  rw [csqp_boxIdx, Fintype.card_piFinset]
  simp [h]

/-- **The contributing lattice vectors.**  If `f` is supported in the open unit cube and `z` is
close to the cube (`-1/4 < zᵢ < 5/4` for every `i`), then `f (z + n) ≠ 0` forces every
coordinate of `n` into `{-1, 0}`. -/
lemma csqp_mem_boxIdx_of_support {f : (ι → ℝ) → ℂ}
    (hsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    {z : ι → ℝ} (hz : ∀ i, z i ∈ Set.Ioo (-(1 / 4 : ℝ)) (5 / 4)) {n : ι → ℤ}
    (hn : f (z + (fun i => (n i : ℝ))) ≠ 0) : n ∈ csqp_boxIdx ι := by
  have hmem : z + (fun i => (n i : ℝ)) ∈ Function.support f := hn
  have hcoord : ∀ i : ι, z i + (n i : ℝ) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    intro i
    have := Set.mem_pi.mp (hsupp hmem) i (Set.mem_univ i)
    simpa using this
  rw [csqp_mem_boxIdx]
  intro i
  have hi := hcoord i
  rw [Set.mem_Ioo] at hi
  have hzlo : -(1 / 4 : ℝ) < z i := (Set.mem_Ioo.mp (hz i)).1
  have hzhi : z i < 5 / 4 := (Set.mem_Ioo.mp (hz i)).2
  rw [Finset.mem_Icc]
  constructor
  · have h2 : (-2 : ℝ) < ((n i : ℤ) : ℝ) := by linarith [hi.1]
    have h3 : (-2 : ℤ) < n i := by exact_mod_cast h2
    omega
  · have h2 : ((n i : ℤ) : ℝ) < 1 := by linarith [hi.2]
    have h3 : n i < (1 : ℤ) := by exact_mod_cast h2
    omega

/-- On the box `(-1/4, 5/4)^ι` the periodization is the finite sum over the contributing
lattice vectors. -/
lemma csqp_periodization_eq_sum_boxIdx {f : (ι → ℝ) → ℂ}
    (hsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    {z : ι → ℝ} (hz : ∀ i, z i ∈ Set.Ioo (-(1 / 4 : ℝ)) (5 / 4)) :
    (∑' n : ι → ℤ, f (z + (fun i => (n i : ℝ))))
      = ∑ n ∈ csqp_boxIdx ι, f (z + (fun i => (n i : ℝ))) :=
  tsum_eq_sum fun n hn => by
    by_contra hc
    exact hn (csqp_mem_boxIdx_of_support hsupp hz hc)

/-- At every point `x` of the closed unit cube the periodization agrees with the finite sum over
the contributing lattice vectors in a whole neighbourhood of `x`. -/
lemma csqp_periodization_eventuallyEq_sum_boxIdx {f : (ι → ℝ) → ℂ}
    (hsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    {x : ι → ℝ} (hx : x ∈ unitCube (ι := ι)) :
    (fun y : ι → ℝ => ∑' n : ι → ℤ, f (y + (fun i => (n i : ℝ))))
      =ᶠ[𝓝 x] (fun y : ι → ℝ => ∑ n ∈ csqp_boxIdx ι, f (y + (fun i => (n i : ℝ)))) := by
  have hBopen : IsOpen (Set.pi Set.univ fun _ : ι => Set.Ioo (-(1 / 4 : ℝ)) (5 / 4)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
  have hxB : x ∈ Set.pi Set.univ fun _ : ι => Set.Ioo (-(1 / 4 : ℝ)) (5 / 4) := by
    rw [Set.mem_pi]
    intro i _
    have hxi : x i ∈ Set.Ioc (0 : ℝ) 1 := by
      have := Set.mem_pi.mp hx i (Set.mem_univ i)
      simpa only [unitCube, Set.mem_Ioc] using this
    exact ⟨by linarith [(Set.mem_Ioc.mp hxi).1], by linarith [(Set.mem_Ioc.mp hxi).2]⟩
  refine Filter.eventually_of_mem (hBopen.mem_nhds hxB) fun y hy => ?_
  exact csqp_periodization_eq_sum_boxIdx hsupp fun i => Set.mem_pi.mp hy i (Set.mem_univ i)

/-- The periodization of a smooth cube-supported function is smooth. -/
lemma csqp_periodization_contDiff {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => ∑' n : ι → ℤ, f (y + (fun i => (n i : ℝ)))) :=
  (periodization_contDiff_periodic f hf hsupp).1

/-! ## 3. Derivatives of the periodization on the cube -/

/-- A continuous real-valued function is integrable on the (bounded) unit cube. -/
lemma csqp_integrableOn_unitCube_of_continuous_real {F : (ι → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F (volume.restrict (unitCube (ι := ι))) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : unitCube (ι := ι) ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (hF.continuousOn.integrableOn_compact hC).mono_set hsub

/-- On the closed unit cube, the `l`-th iterated derivative of the periodization is the sum of
the `2 ^{card ι}` translates of `∂^l f`, and is therefore bounded by `card (boxIdx) * M`. -/
lemma csqp_pdVec_periodization_le {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    {j : ℕ} (l : Fin j → ι) {M : ℝ} (hM : ∀ x : ι → ℝ, ‖pdVec j l f x‖ ≤ M)
    {x : ι → ℝ} (hx : x ∈ unitCube (ι := ι)) :
    ‖pdVec j l (fun y : ι → ℝ => ∑' n : ι → ℤ, f (y + (fun i => (n i : ℝ)))) x‖
      ≤ ((csqp_boxIdx ι).card : ℝ) * M := by
  have hfe := csqp_periodization_eventuallyEq_sum_boxIdx hsupp hx
  have hsum : pdVec j l (fun y : ι → ℝ => ∑ n ∈ csqp_boxIdx ι,
        f (y + (fun i => (n i : ℝ)))) x
      = ∑ n ∈ csqp_boxIdx ι, pdVec j l f (x + (fun i => (n i : ℝ))) := by
    rw [csqp_pdVec_finset_sum]
    · exact Finset.sum_congr rfl fun n _ => csqp_pdVec_comp_add_right l f _ x
    · intro n _
      exact hf.comp (contDiff_id.add contDiff_const)
  have hcongr := csqp_pdVec_congr l hfe
  calc ‖pdVec j l (fun y : ι → ℝ => ∑' n : ι → ℤ, f (y + (fun i => (n i : ℝ)))) x‖
      = ‖∑ n ∈ csqp_boxIdx ι, pdVec j l f (x + (fun i => (n i : ℝ)))‖ := by rw [hcongr, hsum]
    _ ≤ ∑ n ∈ csqp_boxIdx ι, ‖pdVec j l f (x + (fun i => (n i : ℝ)))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ csqp_boxIdx ι, M := Finset.sum_le_sum fun n _ => hM _
    _ = ((csqp_boxIdx ι).card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The `Hᵏ` energy of the periodization is bounded by `card (Fin j → ι) * (card boxIdx * M)^2`
as soon as *every* `j`-th derivative of `f` is bounded by `M` on all of `ι → ℝ`. -/
lemma csqp_ENormSq_periodization_le {f : (ι → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    {j : ℕ} {M : ℝ} (hM : ∀ (l : Fin j → ι) (x : ι → ℝ), ‖pdVec j l f x‖ ≤ M)
    (hMnn : 0 ≤ M) :
    ENormSq j (fun y : ι → ℝ => ∑' n : ι → ℤ, f (y + (fun i => (n i : ℝ))))
      ≤ (Fintype.card (Fin j → ι) : ℝ) * (((csqp_boxIdx ι).card : ℝ) * M) ^ 2 := by
  set P : (ι → ℝ) → ℂ := fun y : ι → ℝ => ∑' n : ι → ℤ, f (y + (fun i => (n i : ℝ))) with hP
  have hcd : ContDiff ℝ j P := by
    rw [hP]
    exact (csqp_periodization_contDiff hf hsupp).of_le (by exact_mod_cast le_top)
  have hterm : ∀ l : Fin j → ι,
      (∫ x in unitCube (ι := ι), ‖pdVec j l P x‖ ^ 2)
        ≤ (((csqp_boxIdx ι).card : ℝ) * M) ^ 2 := by
    intro l
    have hpt : ∀ x ∈ unitCube (ι := ι),
        ‖pdVec j l P x‖ ^ 2 ≤ (((csqp_boxIdx ι).card : ℝ) * M) ^ 2 := by
      intro x hx
      have h1 : ‖pdVec j l P x‖ ≤ ((csqp_boxIdx ι).card : ℝ) * M := by
        rw [hP]
        exact csqp_pdVec_periodization_le hf hsupp l (fun x => hM l x) hx
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hInt1 : Integrable (fun x : ι → ℝ => ‖pdVec j l P x‖ ^ 2)
        (volume.restrict (unitCube (ι := ι))) :=
      csqp_integrableOn_unitCube_of_continuous_real ((continuous_pdVec j l P hcd).norm.pow 2)
    have hInt2 : Integrable
        (fun _ : ι → ℝ => (((csqp_boxIdx ι).card : ℝ) * M) ^ 2)
        (volume.restrict (unitCube (ι := ι))) :=
      csqp_integrableOn_unitCube_of_continuous_real continuous_const
    have hm := setIntegral_mono_on hInt1 hInt2 BesselCont.measSet_unitCube hpt
    have hconst : (∫ _x in unitCube (ι := ι), (((csqp_boxIdx ι).card : ℝ) * M) ^ 2)
        = (((csqp_boxIdx ι).card : ℝ) * M) ^ 2 := by
      rw [setIntegral_const, Measure.real_def, BesselCont.vol_unitCube, ENNReal.toReal_one]
      simp
    rwa [hconst] at hm
  calc ENormSq j P
      = ∑ l : Fin j → ι, ∫ x in unitCube (ι := ι), ‖pdVec j l P x‖ ^ 2 := rfl
    _ ≤ ∑ _l : Fin j → ι, (((csqp_boxIdx ι).card : ℝ) * M) ^ 2 :=
        Finset.sum_le_sum fun l _ => hterm l
    _ = (Fintype.card (Fin j → ι) : ℝ) * (((csqp_boxIdx ι).card : ℝ) * M) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## 4. The Poincaré bound: lower order derivatives are controlled by the top order

The hypothesis of the main theorem bounds only the derivatives of order exactly `k`.  Since `f`
is supported in the open cube, every lower order derivative is bounded by a constant times the
same `M`: this is the classical Poincaré-type inequality for compactly supported functions, and
it is proved here by the one-dimensional mean value theorem.
-/

/-- The support of a partial derivative is contained in the closure of the support. -/
lemma csqp_support_pd_subset_closure {g : (ι → ℝ) → ℂ} (i : ι) :
    Function.support (pd i g) ⊆ closure (Function.support g) := by
  intro x hx
  by_contra hxc
  have hzero : g =ᶠ[𝓝 x] (fun _ : ι → ℝ => (0 : ℂ)) := by
    refine Filter.eventually_of_mem (isClosed_closure.isOpen_compl.mem_nhds hxc) ?_
    intro y hy
    rw [Set.mem_compl_iff] at hy
    by_contra hgy
    exact hy (subset_closure (Function.mem_support.mpr hgy))
  have hpd : pd i g x = 0 := by
    simp only [pd]
    rw [hzero.fderiv_eq]
    simp
  exact hx hpd

/-- Iterated version: the support of `pdList l g` is contained in the closure of the support
of `g`. -/
lemma csqp_support_pdList_subset_closure (l : List ι) (g : (ι → ℝ) → ℂ) :
    Function.support (pdList l g) ⊆ closure (Function.support g) := by
  induction l with
  | nil => intro y hy; exact subset_closure hy
  | cons i t ih =>
      have hpd : pdList (i :: t) g = pd i (pdList t g) := by
        simp only [pdList, List.foldr_cons]
      rw [hpd]
      intro y hy
      have h1 : y ∈ closure (Function.support (pdList t g)) := csqp_support_pd_subset_closure i hy
      have h2 : y ∈ closure (closure (Function.support g)) := closure_mono ih h1
      simpa using h2

/-- For a smooth function supported in the open unit cube, the support of every iterated
derivative is contained in the closed unit cube. -/
lemma csqp_support_pdVec_subset_closedCube {f : (ι → ℝ) → ℂ}
    (hsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (m : ℕ) (l : Fin m → ι) :
    Function.support (pdVec m l f) ⊆ Set.pi Set.univ
      (fun _ : ι => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
  refine (csqp_support_pdList_subset_closure (List.ofFn l) f).trans
    (closure_minimal (hsupp.trans ?_) (isClosed_set_pi fun _ _ => isClosed_Icc))
  intro y hy
  rw [Set.mem_pi]
  intro i _
  have h1 := Set.mem_pi.mp hy i (Set.mem_univ i)
  exact ⟨le_of_lt (Set.mem_Ioo.mp h1).1, le_of_lt (Set.mem_Ioo.mp h1).2⟩

/-- A function vanishing off the closed unit cube vanishes at every point outside it. -/
lemma csqp_eq_zero_of_not_mem_closedCube {g : (ι → ℝ) → ℂ}
    (hg : Function.support g ⊆ Set.pi Set.univ
      (fun _ : ι => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)))
    {y : ι → ℝ} (hy : y ∉ Set.pi Set.univ (fun _ : ι => Set.Icc (-(1 / 2 : ℝ)) (1 / 2))) :
    g y = 0 := by
  by_contra h
  exact hy (hg (Function.mem_support.mpr h))

/-- **One-dimensional mean value bound.**  If the partial derivative `∂ᵢ g` is bounded by `B`
everywhere and `xᵢ ≤ 1`, then moving from `x` to the point with `i`-th coordinate `1` changes
the value of `g` by at most `B * (1 - xᵢ)`. -/
lemma csqp_norm_sub_le_of_pd_bound {g : (ι → ℝ) → ℂ} (i : ι) {B : ℝ}
    (hg : Differentiable ℝ g) (hB : ∀ y, ‖pd i g y‖ ≤ B) {x : ι → ℝ} (hx : x i ≤ 1) :
    ‖g (x + (1 - x i) • (Pi.single i (1 : ℝ))) - g x‖ ≤ B * (1 - x i) := by
  set e : ι → ℝ := Pi.single i (1 : ℝ) with he
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => g (x + (s - x i) • e)) (pd i g (x + (t - x i) • e)) t := by
    intro t
    have hsub : HasDerivAt (fun s : ℝ => s - x i) 1 t := (hasDerivAt_id t).sub_const (x i)
    have hsmul : HasDerivAt (fun s : ℝ => (s - x i) • e) ((1 : ℝ) • e) t := hsub.smul_const e
    have hadd : HasDerivAt (fun s : ℝ => x + (s - x i) • e) ((1 : ℝ) • e) t := hsmul.const_add x
    have hcurve : HasDerivAt (fun s : ℝ => x + (s - x i) • e) e t := by simpa using hadd
    have h3 : HasFDerivAt g (fderiv ℝ g (x + (t - x i) • e)) (x + (t - x i) • e) :=
      (hg (x + (t - x i) • e)).hasFDerivAt
    have h4 := h3.comp_hasDerivAt t hcurve
    have h5 : HasDerivAt (fun s : ℝ => g (x + (s - x i) • e))
        ((fderiv ℝ g (x + (t - x i) • e)) e) t := h4
    simpa [pd, he] using h5
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun t : ℝ => g (x + (t - x i) • e)) (s := Set.Icc (x i) 1) (C := B)
    (x := x i) (y := 1)
    (fun t _ => (hderiv t).differentiableAt)
    (fun t _ => by rw [(hderiv t).deriv]; exact hB _)
    (convex_Icc _ _) (Set.left_mem_Icc.mpr hx) (Set.right_mem_Icc.mpr hx)
  have hmain' : ‖g (x + (1 - x i) • e) - g x‖ ≤ B * ‖(1 : ℝ) - x i‖ := by
    simpa using hmain
  have hnorm : ‖(1 : ℝ) - x i‖ = 1 - x i := by
    rw [Real.norm_eq_abs, abs_of_nonneg]; linarith
  rw [hnorm] at hmain'
  simpa [he] using hmain'

/-- The `m + 1`-fold iterated derivative along `Fin.cons i l` is `∂ᵢ` applied to the `m`-fold
iterated derivative along `l` (the head of the word is the outermost derivative). -/
lemma csqp_pdVec_cons {m : ℕ} (l : Fin m → ι) (i : ι) (g : (ι → ℝ) → ℂ) :
    pdVec (m + 1) (Fin.cons i l) g = pd i (pdVec m l g) := by
  have h1 : List.ofFn (Fin.cons i l) = i :: List.ofFn l := List.ofFn_cons i l
  simp only [pdVec, h1, pdList, List.foldr_cons]

/-- **Poincaré bound.**  For a smooth `f` supported in the open unit cube, if *all* `k`-th
iterated derivatives of `f` are bounded by `M` on all of `ι → ℝ`, then `f` itself is bounded by
`(3/2)^k * M`.  The induction runs on `k`: the mean value theorem along a coordinate direction
bounds every `k`-fold derivative by `(3/2) M` (using the `(k+1)`-fold bound and the fact that
iterated derivatives of `f` vanish off the closed cube), which is exactly the hypothesis of the
`k`-fold statement. -/
theorem csqp_norm_le_of_pdVec_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (ι → ℝ) → ℂ) (M : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      Function.support f ⊆ Set.pi Set.univ
        (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
      (∀ (l : Fin k → ι) (x : ι → ℝ), ‖pdVec k l f x‖ ≤ M) →
      ∀ x : ι → ℝ, ‖f x‖ ≤ C * M := by
  classical
  intro k
  induction k with
  | zero =>
      refine ⟨1, zero_le_one, fun f M hf hsupp hM x => ?_⟩
      have h := hM (fun _ : Fin 0 => Classical.arbitrary ι) x
      simpa [pdVec, pdList] using h
  | succ k ih =>
      obtain ⟨C, hC, hkey⟩ := ih
      refine ⟨C * (3 / 2), by positivity, fun f M hf hsupp hM x => ?_⟩
      have hMnn : 0 ≤ M :=
        le_trans (norm_nonneg _) (hM (fun _ : Fin (k + 1) => Classical.arbitrary ι) 0)
      -- every `k`-fold derivative of `f` is bounded by `(3/2) M`
      have hstep : ∀ (l : Fin k → ι) (y : ι → ℝ), ‖pdVec k l f y‖ ≤ (3 / 2) * M := by
        intro l y
        set i₀ : ι := Classical.arbitrary ι with hi₀
        set g : (ι → ℝ) → ℂ := pdVec k l f with hgdef
        have hgd : Differentiable ℝ g := by
          rw [hgdef]
          exact (csqp_contDiff_pdList_top (List.ofFn l) hf).differentiable (by simp)
        have hsuppg : Function.support g ⊆ Set.pi Set.univ
            (fun _ : ι => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
          rw [hgdef]
          exact csqp_support_pdVec_subset_closedCube hsupp k l
        have hbound : ∀ z : ι → ℝ, ‖pd i₀ g z‖ ≤ M := by
          intro z
          have h1 : pd i₀ g = pdVec (k + 1) (Fin.cons i₀ l) f := by
            rw [hgdef, csqp_pdVec_cons]
          rw [h1]
          exact hM (Fin.cons i₀ l) z
        by_cases hy : y ∈ Set.pi Set.univ (fun _ : ι => Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
        · have hyi := Set.mem_pi.mp hy i₀ (Set.mem_univ i₀)
          have hyle : y i₀ ≤ 1 := by linarith [(Set.mem_Icc.mp hyi).2]
          have hyge : -(1 / 2 : ℝ) ≤ y i₀ := (Set.mem_Icc.mp hyi).1
          have hmvt := csqp_norm_sub_le_of_pd_bound (g := g) i₀ hgd hbound hyle
          have hend : g (y + (1 - y i₀) • (Pi.single i₀ (1 : ℝ))) = 0 := by
            refine csqp_eq_zero_of_not_mem_closedCube hsuppg fun hmem => ?_
            have h1 := Set.mem_pi.mp hmem i₀ (Set.mem_univ i₀)
            have h2 : (y + (1 - y i₀) • (Pi.single i₀ (1 : ℝ) : ι → ℝ)) i₀ = 1 := by
              simp [Pi.single_eq_same]
            rw [h2] at h1
            have h3 := (Set.mem_Icc.mp h1).2
            norm_num at h3
          have hzero : ‖g y‖ = ‖g (y + (1 - y i₀) • (Pi.single i₀ (1 : ℝ))) - g y‖ := by
            rw [hend, zero_sub, norm_neg]
          have h3 : 1 - y i₀ ≤ 3 / 2 := by linarith
          calc ‖g y‖
              = ‖g (y + (1 - y i₀) • (Pi.single i₀ (1 : ℝ))) - g y‖ := hzero
            _ ≤ M * (1 - y i₀) := hmvt
            _ ≤ M * (3 / 2) := mul_le_mul_of_nonneg_left h3 hMnn
            _ = (3 / 2) * M := by ring
        · rw [csqp_eq_zero_of_not_mem_closedCube hsuppg hy, norm_zero]
          exact mul_nonneg (by norm_num) hMnn
      have h := hkey f ((3 / 2) * M) hf hsupp hstep x
      calc ‖f x‖ ≤ C * ((3 / 2) * M) := h
        _ = C * (3 / 2) * M := by ring

/-! ## 5. The target theorem -/

theorem CSq_periodization_le_of_sup_bound {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (ι → ℝ) → ℂ) (M : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      Function.support f ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) →
      (∀ (l : Fin k → ι) (x : ι → ℝ), ‖Work.Diff.STE.pdVec k l f x‖ ≤ M) →
      Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ k *
        ‖Work.Diff.STE.fourierCoeff
          (fun y : ι → ℝ => ∑' n : ι → ℤ, f (y + fun i => (n i : ℝ))) m‖ ^ 2) ∧
      Work.Diff.STE.CSq k
          (Work.Diff.STE.fourierCoeff
            (fun y : ι → ℝ => ∑' n : ι → ℤ, f (y + fun i => (n i : ℝ))))
        ≤ C * M ^ 2 := by
  classical
  obtain ⟨C₀, hC₀nn, hC₀⟩ := csqp_norm_le_of_pdVec_bound (ι := ι) k
  obtain ⟨C₁, hC₁nn, hC₁⟩ := CSq_le_ENormSq (ι := ι) k
  refine ⟨C₁ * ((Fintype.card ι : ℝ) ^ k + 1) * ((csqp_boxIdx ι).card : ℝ) ^ 2 * (C₀ + 1) ^ 2,
    by positivity, ?_⟩
  intro f M hf hsupp hM
  set P : (ι → ℝ) → ℂ := fun y : ι → ℝ => ∑' n : ι → ℤ, f (y + (fun i => (n i : ℝ))) with hP
  have hPcd : ContDiff ℝ (⊤ : ℕ∞) P := by
    rw [hP]
    exact csqp_periodization_contDiff hf hsupp
  have hPper : Periodic1 P := by
    rw [hP]
    exact (periodization_contDiff_periodic f hf hsupp).2.1
  have hsum : Summable (fun m : ι → ℤ => (wt m) ^ k * ‖fourierCoeff P m‖ ^ 2) :=
    summable_weighted_fourierCoeff_of_contDiff P hPcd hPper k
  refine ⟨hsum, ?_⟩
  have hMnn : 0 ≤ M :=
    le_trans (norm_nonneg _) (hM (fun _ : Fin k => Classical.arbitrary ι) 0)
  have hC₀b : ∀ x : ι → ℝ, ‖f x‖ ≤ C₀ * M := fun x => hC₀ f M hf hsupp hM x
  have hC₀M : 0 ≤ C₀ * M := mul_nonneg hC₀nn hMnn
  have hcsq : CSq k (fourierCoeff P) ≤ C₁ * (ENormSq k P + ENormSq 0 P) :=
    hC₁ P (hPcd.of_le (by exact_mod_cast le_top)) hPper
  have hENk : ENormSq k P
      ≤ (Fintype.card (Fin k → ι) : ℝ) * (((csqp_boxIdx ι).card : ℝ) * M) ^ 2 :=
    csqp_ENormSq_periodization_le hf hsupp hM hMnn
  have hEN0 : ENormSq 0 P
      ≤ (Fintype.card (Fin 0 → ι) : ℝ) *
          (((csqp_boxIdx ι).card : ℝ) * (C₀ * M)) ^ 2 :=
    csqp_ENormSq_periodization_le hf hsupp (j := 0) (M := C₀ * M)
      (fun l x => hC₀b x) hC₀M
  have hcardk : (Fintype.card (Fin k → ι) : ℝ) = (Fintype.card ι : ℝ) ^ k := by
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hcard0 : (Fintype.card (Fin 0 → ι) : ℝ) = 1 := by
    rw [Fintype.card_fun, Fintype.card_fin]
    simp
  -- elementary arithmetic for the final constant
  have hone : (1 : ℝ) ≤ (C₀ + 1) ^ 2 := by nlinarith
  have hC₀sq : C₀ ^ 2 ≤ (C₀ + 1) ^ 2 := by nlinarith
  have hstep1 : (((csqp_boxIdx ι).card : ℝ) * M) ^ 2
      ≤ ((csqp_boxIdx ι).card : ℝ) ^ 2 * (C₀ + 1) ^ 2 * M ^ 2 := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right (show ((csqp_boxIdx ι).card : ℝ) ^ 2
        ≤ ((csqp_boxIdx ι).card : ℝ) ^ 2 * (C₀ + 1) ^ 2 from ?_) (sq_nonneg M)
    simpa using mul_le_mul_of_nonneg_left hone (sq_nonneg ((csqp_boxIdx ι).card : ℝ))
  have hstep2 : (((csqp_boxIdx ι).card : ℝ) * (C₀ * M)) ^ 2
      ≤ ((csqp_boxIdx ι).card : ℝ) ^ 2 * (C₀ + 1) ^ 2 * M ^ 2 := by
    rw [mul_pow, mul_pow]
    calc ((csqp_boxIdx ι).card : ℝ) ^ 2 * (C₀ ^ 2 * M ^ 2)
        = ((csqp_boxIdx ι).card : ℝ) ^ 2 * C₀ ^ 2 * M ^ 2 := by ring
      _ ≤ ((csqp_boxIdx ι).card : ℝ) ^ 2 * (C₀ + 1) ^ 2 * M ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC₀sq (sq_nonneg _))
            (sq_nonneg M)
  have hinner : (Fintype.card ι : ℝ) ^ k * (((csqp_boxIdx ι).card : ℝ) * M) ^ 2
        + (((csqp_boxIdx ι).card : ℝ) * (C₀ * M)) ^ 2
      ≤ ((Fintype.card ι : ℝ) ^ k + 1)
        * (((csqp_boxIdx ι).card : ℝ) ^ 2 * (C₀ + 1) ^ 2 * M ^ 2) := by
    have hck : (0 : ℝ) ≤ (Fintype.card ι : ℝ) ^ k := by positivity
    calc (Fintype.card ι : ℝ) ^ k * (((csqp_boxIdx ι).card : ℝ) * M) ^ 2
          + (((csqp_boxIdx ι).card : ℝ) * (C₀ * M)) ^ 2
        ≤ (Fintype.card ι : ℝ) ^ k
            * (((csqp_boxIdx ι).card : ℝ) ^ 2 * (C₀ + 1) ^ 2 * M ^ 2)
          + ((csqp_boxIdx ι).card : ℝ) ^ 2 * (C₀ + 1) ^ 2 * M ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hstep1 hck) hstep2
      _ = ((Fintype.card ι : ℝ) ^ k + 1)
            * (((csqp_boxIdx ι).card : ℝ) ^ 2 * (C₀ + 1) ^ 2 * M ^ 2) := by ring
  calc CSq k (fourierCoeff P)
      ≤ C₁ * (ENormSq k P + ENormSq 0 P) := hcsq
    _ ≤ C₁ * ((Fintype.card (Fin k → ι) : ℝ) * (((csqp_boxIdx ι).card : ℝ) * M) ^ 2
          + (Fintype.card (Fin 0 → ι) : ℝ)
            * (((csqp_boxIdx ι).card : ℝ) * (C₀ * M)) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hENk hEN0) hC₁nn
    _ ≤ C₁ * ((Fintype.card ι : ℝ) ^ k + 1) * ((csqp_boxIdx ι).card : ℝ) ^ 2
          * (C₀ + 1) ^ 2 * M ^ 2 := by
        rw [hcardk, hcard0, one_mul]
        calc C₁ * ((Fintype.card ι : ℝ) ^ k * (((csqp_boxIdx ι).card : ℝ) * M) ^ 2
              + (((csqp_boxIdx ι).card : ℝ) * (C₀ * M)) ^ 2)
            ≤ C₁ * (((Fintype.card ι : ℝ) ^ k + 1)
                * (((csqp_boxIdx ι).card : ℝ) ^ 2 * (C₀ + 1) ^ 2 * M ^ 2)) :=
              mul_le_mul_of_nonneg_left hinner hC₁nn
          _ = C₁ * ((Fintype.card ι : ℝ) ^ k + 1) * ((csqp_boxIdx ι).card : ℝ) ^ 2
                * (C₀ + 1) ^ 2 * M ^ 2 := by ring

end Work.Diff.STE
