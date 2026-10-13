/-
  WilE4 / CAD — preconnectedness of a cylindrical cell.

  A cell of the CAD is `cell C G v = C.pad ∩ {sign vector of G = v}`.  We show that if the base
  cell `C` is preconnected, the family `G` is closed under differentiation in the last variable,
  the coefficient signs of every `spec (G i) x` are constant on `C`, and the sign vector `v` is
  realised over every point of `C`, then the cell is preconnected.

  The univariate content (the sign-condition set of a differentiated-closed family of polynomials
  is an interval, and its closure is the corresponding non-strict sign-condition set) is proved in
  `Fibre.lean` and the two lemmas about `pcell`/`pcellCl`.
-/
import Mathlib
import Submission.Work.WilE4.Tower
import Submission.Work.WilE4.CAD.Decomp
import Submission.Work.WilE4.CAD.Fibre
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.pcell_ordConnected
import Submission.Work.WilE4.CAD.pcellCl_eq_closure_pcell
import Submission.Work.WilE4.CAD.isPreconnected_of_closed_fibers
import Submission.Work.WilE4.CAD.isPreconnected_of_closed_fibers_rel
import Submission.Work.WilE4.Poly.spec_pderiv
import Submission.Work.WilE4.Ana.root_bound

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Filter
open scoped Topology

namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (spec)

variable {m : ℕ}

/-! ## Degree bookkeeping for `spec` -/

theorem rot_symm_zero (m : ℕ) : (Work.WilE4.rot m).symm 0 = Fin.last m := by
  rw [Equiv.symm_apply_eq]; exact (Work.WilE4.rot_last m).symm

/-- `spec P x` has degree at most the degree of `P` in the last variable. -/
theorem natDegree_spec_le (P : MvPolynomial (Fin (m + 1)) ℝ) (x : Fin m → ℝ) :
    (spec P x).natDegree ≤ P.degreeOf (Fin.last m) := by
  have h1 : (spec P x).natDegree ≤
      ((MvPolynomial.finSuccEquiv ℝ m) (MvPolynomial.rename (Work.WilE4.rot m) P)).natDegree := by
    rw [spec]; exact Polynomial.natDegree_map_le
  have h2 : ((MvPolynomial.finSuccEquiv ℝ m) (MvPolynomial.rename (Work.WilE4.rot m) P)).natDegree
      = (MvPolynomial.rename (Work.WilE4.rot m) P).degreeOf 0 :=
    MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := m) _
  rw [h2] at h1
  have h3 : (MvPolynomial.rename (Work.WilE4.rot m) P).degreeOf 0 = P.degreeOf (Fin.last m) := by
    rw [show (0 : Fin (m + 1)) = (Work.WilE4.rot m) ((Work.WilE4.rot m).symm 0) from
      (Equiv.apply_symm_apply (Work.WilE4.rot m) 0).symm]
    rw [MvPolynomial.degreeOf_rename_of_injective (R := ℝ) (Work.WilE4.rot m).injective]
    rw [rot_symm_zero m]
  linarith [h1, h3]

/-- Coefficients of `spec P x` beyond the degree in the last variable vanish. -/
theorem coeff_spec_eq_zero (P : MvPolynomial (Fin (m + 1)) ℝ) (x : Fin m → ℝ) {j : ℕ}
    (hj : P.degreeOf (Fin.last m) < j) : (spec P x).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_spec_le P x) hj)

/-- `spec P x` vanishes identically on `C.set` either for all `x ∈ C.set` or for none. -/
theorem spec_zero_iff (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (C : SAd m)
    (v : Fin G.length → SignType)
    (hconst : ∀ i : Fin G.length, ∀ j : ℕ, j ≤ (G.get i).degreeOf (Fin.last m) →
      ∀ x ∈ C.set, ∀ x' ∈ C.set,
      SignType.sign ((spec (G.get i) x).coeff j)
        = SignType.sign ((spec (G.get i) x').coeff j))
    (i : Fin G.length) {x x' : Fin m → ℝ} (hx : x ∈ C.set) (hx' : x' ∈ C.set) :
    spec (G.get i) x = 0 ↔ spec (G.get i) x' = 0 := by
  have key : ∀ {y y' : Fin m → ℝ}, y ∈ C.set → y' ∈ C.set →
      spec (G.get i) y = 0 → spec (G.get i) y' = 0 := by
    intro y y' hy hy' hy0
    apply Polynomial.ext
    intro j
    by_cases hj : j ≤ (G.get i).degreeOf (Fin.last m)
    · have hc := hconst i j hj y hy y' hy'
      have h0 : (spec (G.get i) y).coeff j = 0 := by rw [hy0]; simp
      rw [h0, sign_zero] at hc
      exact sign_eq_zero_iff.mp hc.symm
    · push Not at hj
      exact coeff_spec_eq_zero (G.get i) y' hj
  exact ⟨key hx hx', key hx' hx⟩

/-- The family of specialisations is closed under differentiation. -/
theorem spec_deriv_closed (G : List (MvPolynomial (Fin (m + 1)) ℝ))
    (hderiv : ∀ i : Fin G.length,
      MvPolynomial.pderiv (Fin.last m) (G.get i) = 0 ∨
        ∃ j : Fin G.length, G.get j = MvPolynomial.pderiv (Fin.last m) (G.get i))
    (x : Fin m → ℝ) :
    ∀ i : Fin G.length, (spec (G.get i) x).derivative = 0 ∨
      ∃ j : Fin G.length, spec (G.get j) x = (spec (G.get i) x).derivative := by
  intro i
  rcases hderiv i with h | ⟨j, hj⟩
  · left
    rw [← Work.WilE4.Poly.spec_pderiv, h]
    simp [spec]
  · right
    exact ⟨j, by rw [← Work.WilE4.Poly.spec_pderiv, hj]⟩

/-- The fibre is an interval. -/
theorem Fib_ordConnected (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (v : Fin G.length → SignType)
    (hderiv : ∀ i : Fin G.length,
      MvPolynomial.pderiv (Fin.last m) (G.get i) = 0 ∨
        ∃ j : Fin G.length, G.get j = MvPolynomial.pderiv (Fin.last m) (G.get i))
    (x : Fin m → ℝ) : Set.OrdConnected (Fib G v x) := by
  rw [Fib_eq_pcell]
  exact pcell_ordConnected _ _ (spec_deriv_closed G hderiv x)

/-! ## Continuity of the specialisation -/

theorem continuous_eval_snoc (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (i : Fin G.length)
    (t : ℝ) : Continuous fun x : Fin m → ℝ => MvPolynomial.eval (Fin.snoc x t) (G.get i) :=
  (MvPolynomial.continuous_eval (G.get i)).comp
    (Continuous.finSnoc (A := fun _ : Fin (m + 1) => ℝ) continuous_id continuous_const)

theorem continuous_snoc (t : ℝ) :
    Continuous fun x : Fin m → ℝ => (Fin.snoc x t : Fin (m + 1) → ℝ) :=
  Continuous.finSnoc (A := fun _ : Fin (m + 1) => ℝ) continuous_id continuous_const

theorem continuous_snoc_snd (x : Fin m → ℝ) :
    Continuous fun t : ℝ => (Fin.snoc x t : Fin (m + 1) → ℝ) := by
  rw [continuous_pi_iff]
  intro k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
  · have : (fun t : ℝ => (Fin.snoc x t : Fin (m + 1) → ℝ) j.castSucc) =
        fun _ : ℝ => x j := by
      funext t; rw [Fin.snoc_castSucc]
    rw [this]; exact continuous_const
  · have : (fun t : ℝ => (Fin.snoc x t : Fin (m + 1) → ℝ) (Fin.last m)) =
        fun t : ℝ => t := by
      funext t; rw [Fin.snoc_last]
    rw [this]; exact continuous_id

theorem continuous_snoc_prod :
    Continuous fun p : (Fin m → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (m + 1) → ℝ) :=
  Continuous.finSnoc (A := fun _ : Fin (m + 1) => ℝ) continuous_fst continuous_snd

theorem continuous_eval_snoc_prod (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (i : Fin G.length) :
    Continuous fun p : (Fin m → ℝ) × ℝ => MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i) :=
  (MvPolynomial.continuous_eval (G.get i)).comp continuous_snoc_prod

/-- A non-zero polynomial that vanishes on an ord-connected set vanishes on a single point. -/
theorem subsingleton_of_ordConnected_of_eval_eq_zero {p : Polynomial ℝ} (hp : p ≠ 0)
    {S : Set ℝ} (hS : S.OrdConnected) (hroot : ∀ t ∈ S, p.eval t = 0) : S.Subsingleton := by
  intro t₁ ht₁ t₂ ht₂
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hsub : Set.Icc t₁ t₂ ⊆ (p.roots.toFinset : Set ℝ) := by
      intro t ht
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr
        (Polynomial.IsRoot.def.mpr (hroot t (hS.out ht₁ ht₂ ht))))
    obtain ⟨t, ht, htnot⟩ := (Set.Icc_infinite hlt).exists_notMem_finset p.roots.toFinset
    exact htnot (hsub ht)
  · have hsub : Set.Icc t₂ t₁ ⊆ (p.roots.toFinset : Set ℝ) := by
      intro t ht
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr
        (Polynomial.IsRoot.def.mpr (hroot t (hS.out ht₂ ht₁ ht))))
    obtain ⟨t, ht, htnot⟩ := (Set.Icc_infinite hlt).exists_notMem_finset p.roots.toFinset
    exact htnot (hsub ht)

/-! ## Local boundedness of the roots -/

/-- The roots of `spec P x` are locally bounded, given the sign-constancy of the coefficients. -/
theorem roots_bdd_near (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (C : SAd m)
    (v : Fin G.length → SignType)
    (hconst : ∀ i : Fin G.length, ∀ j : ℕ, j ≤ (G.get i).degreeOf (Fin.last m) →
      ∀ x ∈ C.set, ∀ x' ∈ C.set,
      SignType.sign ((spec (G.get i) x).coeff j)
        = SignType.sign ((spec (G.get i) x').coeff j))
    (i₀ : Fin G.length) (hpos : ∀ x ∈ C.set, spec (G.get i₀) x ≠ 0)
    {x₀ : Fin m → ℝ} (hx₀ : x₀ ∈ C.set) :
    ∃ B : ℝ, ∀ᶠ x in 𝓝 x₀,
      (x ∈ C.set → ∀ t : ℝ, (spec (G.get i₀) x).eval t = 0 → |t| ≤ B) := by
  classical
  set d : ℕ := (spec (G.get i₀) x₀).natDegree with hd
  have hc0 : (spec (G.get i₀) x₀).coeff d ≠ 0 := by
    rw [hd, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr (hpos x₀ hx₀)
  have hcont : ∀ j : ℕ, Continuous fun x : Fin m → ℝ => (spec (G.get i₀) x).coeff j := by
    intro j
    rw [show (fun x : Fin m → ℝ => (spec (G.get i₀) x).coeff j)
        = fun x => MvPolynomial.eval x ((Work.WilE4.CAD.F (G.get i₀)).coeff j) from by
      funext x; exact Work.WilE4.CAD.coeff_spec (G.get i₀) x j]
    exact MvPolynomial.continuous_eval _
  have hM1 : ∀ᶠ x in 𝓝 x₀, ∀ j ∈ Finset.range d,
      |(spec (G.get i₀) x).coeff j| ≤ |(spec (G.get i₀) x₀).coeff j| + 1 := by
    rw [Filter.eventually_all_finset]
    intro j _
    filter_upwards [Metric.tendsto_nhds.mp (hcont j).continuousAt 1 (by norm_num)] with x hx
    have h2 : |(spec (G.get i₀) x).coeff j| - |(spec (G.get i₀) x₀).coeff j| ≤
        |(spec (G.get i₀) x).coeff j - (spec (G.get i₀) x₀).coeff j| :=
      abs_sub_abs_le_abs_sub _ _
    rw [Real.dist_eq] at hx
    linarith
  have hM : ∀ᶠ x in 𝓝 x₀, (∑ j ∈ Finset.range d, |(spec (G.get i₀) x).coeff j|) ≤
      ∑ j ∈ Finset.range d, (|(spec (G.get i₀) x₀).coeff j| + 1) :=
    hM1.mono fun x hx => Finset.sum_le_sum fun j hj => hx j hj
  have hMnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range d, (|(spec (G.get i₀) x₀).coeff j| + 1) :=
    Finset.sum_nonneg fun j _ => by positivity
  have hδ : ∀ᶠ x in 𝓝 x₀,
      |(spec (G.get i₀) x₀).coeff d| / 2 ≤ |(spec (G.get i₀) x).coeff d| := by
    have hpos0 : 0 < |(spec (G.get i₀) x₀).coeff d| := abs_pos.mpr hc0
    filter_upwards [Metric.tendsto_nhds.mp (hcont d).continuousAt
      (|(spec (G.get i₀) x₀).coeff d| / 2) (by positivity)] with x hx
    have h2 : |(spec (G.get i₀) x₀).coeff d| - |(spec (G.get i₀) x).coeff d| ≤
        |(spec (G.get i₀) x).coeff d - (spec (G.get i₀) x₀).coeff d| := by
      rw [abs_sub_comm ((spec (G.get i₀) x).coeff d) ((spec (G.get i₀) x₀).coeff d)]
      exact abs_sub_abs_le_abs_sub _ _
    rw [Real.dist_eq] at hx
    linarith
  refine ⟨1 + (∑ j ∈ Finset.range d, (|(spec (G.get i₀) x₀).coeff j| + 1))
      / (|(spec (G.get i₀) x₀).coeff d| / 2), ?_⟩
  filter_upwards [hM, hδ] with x hxM hxδ hxC t ht
  have hle : (spec (G.get i₀) x).natDegree ≤ d := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    by_cases hNdeg : N ≤ (G.get i₀).degreeOf (Fin.last m)
    · have hc := hconst i₀ N hNdeg x hxC x₀ hx₀
      have hz : (spec (G.get i₀) x₀).coeff N = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [← hd]; exact hN)
      rw [hz, sign_zero] at hc
      exact sign_eq_zero_iff.mp hc
    · push Not at hNdeg
      exact coeff_spec_eq_zero (G.get i₀) x hNdeg
  have hcdeq : (spec (G.get i₀) x).natDegree = d := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle ?_
    intro h0
    have hc := hconst i₀ d (by rw [hd]; exact natDegree_spec_le (G.get i₀) x₀) x hxC x₀ hx₀
    rw [h0, sign_zero] at hc
    exact hc0 (sign_eq_zero_iff.mp hc.symm)
  have hrb := Work.WilE4.Ana.root_bound (p := spec (G.get i₀) x) (hpos x hxC)
    (Polynomial.IsRoot.def.mpr ht)
  rw [hcdeq, Polynomial.leadingCoeff, hcdeq] at hrb
  have hpos' : (0 : ℝ) < |(spec (G.get i₀) x₀).coeff d| / 2 := by
    have := abs_pos.mpr hc0; linarith
  have hSnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range d, |(spec (G.get i₀) x).coeff j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  calc |t| ≤ 1 + (∑ j ∈ Finset.range d, |(spec (G.get i₀) x).coeff j|)
            / |(spec (G.get i₀) x).coeff d| := hrb
    _ ≤ 1 + (∑ j ∈ Finset.range d, (|(spec (G.get i₀) x₀).coeff j| + 1))
            / (|(spec (G.get i₀) x₀).coeff d| / 2) := by
        exact add_le_add (le_refl 1) (div_le_div₀ hMnn hxM hpos' hxδ)

/-! ## Case I: all zero-coordinates are identically zero, so the fibre is open -/

theorem preconnected_cell_caseI (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (C : SAd m)
    (v : Fin G.length → SignType) (hC : IsPreconnected C.set)
    (hI : ∀ i : Fin G.length, v i = 0 → ∀ x ∈ C.set, spec (G.get i) x = 0)
    (hord : ∀ x : Fin m → ℝ, Set.OrdConnected (Fib G v x))
    (hne : ∀ x ∈ C.set, (Fib G v x).Nonempty) :
    IsPreconnected (Work.WilE4.cell C G v).set := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u w hu hw hcover hdisj
  have hevent : ∀ x : Fin m → ℝ, ∀ t ∈ Fib G v x, ∀ xs : ℕ → Fin m → ℝ,
      (∀ n, xs n ∈ closure C.set) → Tendsto xs atTop (𝓝 x) →
        ∀ᶠ n in atTop, t ∈ Fib G v (xs n) := by
    intro x t ht xs hxs hlim
    simp only [Fib, Set.mem_setOf_eq]
    rw [Filter.eventually_all]
    intro i
    rcases eq_or_ne (v i) 0 with hvi | hvi
    · have hsub : C.set ⊆ {y : Fin m → ℝ |
          MvPolynomial.eval (Fin.snoc y t) (G.get i) = 0} := by
        intro y hy
        show MvPolynomial.eval (Fin.snoc y t) (G.get i) = 0
        rw [← spec_eval_snoc, hI i hvi y hy]
        simp [spec]
      have hcl : IsClosed {y : Fin m → ℝ |
          MvPolynomial.eval (Fin.snoc y t) (G.get i) = 0} :=
        isClosed_eq (continuous_eval_snoc G i t) continuous_const
      refine Filter.Eventually.of_forall fun n => ?_
      rw [hcl.closure_subset_iff.mpr hsub (hxs n), hvi, sign_zero]
    · have hne0 : MvPolynomial.eval (Fin.snoc x t) (G.get i) ≠ 0 := by
        intro h0
        have h1 := ht i
        rw [h0, sign_zero] at h1
        exact hvi h1.symm
      rcases lt_trichotomy (MvPolynomial.eval (Fin.snoc x t) (G.get i)) 0 with hneg | heq | hpos
      · have hev : ∀ᶠ y in 𝓝 x,
            SignType.sign (MvPolynomial.eval (Fin.snoc y t) (G.get i)) = v i := by
          filter_upwards [(continuous_eval_snoc G i t).continuousAt.tendsto.eventually
            (IsOpen.mem_nhds isOpen_Iio hneg)] with y hy
          exact (sign_neg hy).trans ((sign_neg hneg).symm.trans (ht i))
        exact hlim.eventually hev
      · exact absurd heq hne0
      · have hev : ∀ᶠ y in 𝓝 x,
            SignType.sign (MvPolynomial.eval (Fin.snoc y t) (G.get i)) = v i := by
          filter_upwards [(continuous_eval_snoc G i t).continuousAt.tendsto.eventually
            (IsOpen.mem_nhds isOpen_Ioi hpos)] with y hy
          exact (sign_pos hy).trans ((sign_pos hpos).symm.trans (ht i))
        exact hlim.eventually hev
  let A : Set (Fin m → ℝ) :=
    {x | x ∈ closure C.set ∧ ∀ t : ℝ, t ∈ Fib G v x → Fin.snoc x t ∈ u}
  let B : Set (Fin m → ℝ) :=
    {x | x ∈ closure C.set ∧ ∀ t : ℝ, t ∈ Fib G v x → Fin.snoc x t ∈ w}
  have hAcl : IsClosed A := by
    refine isClosed_of_closure_subset ?_
    intro x hx
    obtain ⟨xs, hxs, hxlim⟩ := mem_closure_iff_seq_limit.mp hx
    refine ⟨closure_minimal (fun y hy => hy.1) isClosed_closure hx, ?_⟩
    intro t ht
    refine hu.mem_of_tendsto ((continuous_snoc t).tendsto x |>.comp hxlim) ?_
    exact (hevent x t ht xs (fun n => (hxs n).1) hxlim).mono fun n hn => (hxs n).2 t hn
  have hBcl : IsClosed B := by
    refine isClosed_of_closure_subset ?_
    intro x hx
    obtain ⟨xs, hxs, hxlim⟩ := mem_closure_iff_seq_limit.mp hx
    refine ⟨closure_minimal (fun y hy => hy.1) isClosed_closure hx, ?_⟩
    intro t ht
    refine hw.mem_of_tendsto ((continuous_snoc t).tendsto x |>.comp hxlim) ?_
    exact (hevent x t ht xs (fun n => (hxs n).1) hxlim).mono fun n hn => (hxs n).2 t hn
  have hAB : C.set ⊆ A ∪ B := by
    intro x hx
    have himg : IsPreconnected ((fun t : ℝ => (Fin.snoc x t : Fin (m + 1) → ℝ)) '' Fib G v x) :=
      (hord x).isPreconnected.image _ (continuous_snoc_snd x).continuousOn
    have hsubZ : ((fun t : ℝ => (Fin.snoc x t : Fin (m + 1) → ℝ)) '' Fib G v x) ⊆
        (Work.WilE4.cell C G v).set := by
      rintro z ⟨t, ht, rfl⟩
      rw [mem_cell_iff]
      exact ⟨by rw [Fin.init_snoc]; exact hx, ht⟩
    have hdisjZ : ((fun t : ℝ => (Fin.snoc x t : Fin (m + 1) → ℝ)) '' Fib G v x) ∩ (u ∩ w) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hz, hzu, hzw⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj) z ⟨hsubZ hz, hzu, hzw⟩
    have hx' : x ∈ closure C.set := subset_closure hx
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp himg) u w hu hw
        (hsubZ.trans hcover) hdisjZ with h | h
    · exact Or.inl ⟨hx', fun t ht => h ⟨t, ht, rfl⟩⟩
    · exact Or.inr ⟨hx', fun t ht => h ⟨t, ht, rfl⟩⟩
  have hdisjAB : C.set ∩ (A ∩ B) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx, hxA, hxB⟩
    obtain ⟨t, ht⟩ := hne x hx
    have h3 : Fin.snoc x t ∈ (Work.WilE4.cell C G v).set := by
      rw [mem_cell_iff]; exact ⟨by rw [Fin.init_snoc]; exact hx, ht⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) _ ⟨h3, hxA.2 t ht, hxB.2 t ht⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hC) A B hAcl hBcl hAB hdisjAB with h | h
  · left
    intro z hz
    rw [mem_cell_iff] at hz
    have hz2 : z (Fin.last m) ∈ Fib G v (Fin.init z) := by
      rw [Fib_eq_pcell]
      intro i
      rw [spec_eval_snoc, Fin.snoc_init_self z]
      exact hz.2 i
    have hgoal : Fin.snoc (Fin.init z) (z (Fin.last m)) ∈ u := (h hz.1).2 (z (Fin.last m)) hz2
    rwa [Fin.snoc_init_self z] at hgoal
  · right
    intro z hz
    rw [mem_cell_iff] at hz
    have hz2 : z (Fin.last m) ∈ Fib G v (Fin.init z) := by
      rw [Fib_eq_pcell]
      intro i
      rw [spec_eval_snoc, Fin.snoc_init_self z]
      exact hz.2 i
    have hgoal : Fin.snoc (Fin.init z) (z (Fin.last m)) ∈ w := (h hz.1).2 (z (Fin.last m)) hz2
    rwa [Fin.snoc_init_self z] at hgoal

/-! ## Case S: some zero-coordinate is non-zero, so the fibre is a point -/

theorem preconnected_cell_caseS (G : List (MvPolynomial (Fin (m + 1)) ℝ)) (C : SAd m)
    (v : Fin G.length → SignType) (i₀ : Fin G.length) (hvi₀ : v i₀ = 0)
    (hpos : ∀ x ∈ C.set, spec (G.get i₀) x ≠ 0)
    (hzero : ∀ x ∈ C.set, ∀ i : Fin G.length, spec (G.get i) x = 0 → v i = 0)
    (hderivs : ∀ x : Fin m → ℝ, ∀ i : Fin G.length,
      (spec (G.get i) x).derivative = 0 ∨
        ∃ j : Fin G.length, spec (G.get j) x = (spec (G.get i) x).derivative)
    (hne : ∀ x ∈ C.set, (Fib G v x).Nonempty)
    (hord : ∀ x : Fin m → ℝ, Set.OrdConnected (Fib G v x))
    (hbdd : ∀ x ∈ C.set, ∃ B : ℝ, ∀ᶠ x' in 𝓝 x,
      (x' ∈ C.set → ∀ t : ℝ, (spec (G.get i₀) x').eval t = 0 → |t| ≤ B))
    (hC : IsPreconnected C.set) :
    IsPreconnected (Work.WilE4.cell C G v).set := by
  classical
  have hsub : ∀ x ∈ C.set, (Fib G v x).Subsingleton := by
    intro x hx
    refine subsingleton_of_ordConnected_of_eval_eq_zero (hpos x hx) (hord x) ?_
    intro t ht
    have h1 := ht i₀
    rw [← spec_eval_snoc] at h1
    exact sign_eq_zero_iff.mp (by rw [h1, hvi₀])
  have hFibCl : ∀ x ∈ C.set, FibCl G v x = Fib G v x := by
    intro x hx
    have hpc := pcellCl_eq_closure_pcell (fun i => spec (G.get i) x) v
      (fun i hi => hzero x hx i hi) (hderivs x) (by rw [← Fib_eq_pcell]; exact hne x hx)
    rw [FibCl_eq_pcellCl, hpc, ← Fib_eq_pcell]
    exact (Set.Subsingleton.isClosed (hsub x hx)).closure_eq
  set D : Set ((Fin m → ℝ) × ℝ) := {p | ∀ i : Fin G.length,
      (v i = 1 → 0 ≤ MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i)) ∧
      (v i = -1 → MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i) ≤ 0) ∧
      (v i = 0 → MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i) = 0)} with hD
  have hDclosed : IsClosed D := by
    rw [hD]
    have hsplit : {p : (Fin m → ℝ) × ℝ | ∀ i : Fin G.length,
        (v i = 1 → 0 ≤ MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i)) ∧
        (v i = -1 → MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i) ≤ 0) ∧
        (v i = 0 → MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i) = 0)} =
        (⋂ i : Fin G.length, {p : (Fin m → ℝ) × ℝ |
              v i = 1 → 0 ≤ MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i)}) ∩
        (⋂ i : Fin G.length, {p : (Fin m → ℝ) × ℝ |
              v i = -1 → MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i) ≤ 0}) ∩
        (⋂ i : Fin G.length, {p : (Fin m → ℝ) × ℝ |
              v i = 0 → MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i) = 0}) := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨⟨fun i => (h i).1, fun i => (h i).2.1⟩, fun i => (h i).2.2⟩
      · intro h i; exact ⟨h.1.1 i, h.1.2 i, h.2 i⟩
    rw [hsplit]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_iInter fun i => by
        have hh : {p : (Fin m → ℝ) × ℝ |
              v i = 1 → 0 ≤ MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i)} =
            if v i = 1 then {p : (Fin m → ℝ) × ℝ |
                0 ≤ MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i)} else Set.univ := by
          by_cases h1 : v i = 1 <;> simp [h1]
        rw [hh]
        by_cases h1 : v i = 1
        · rw [ite_eq_left h1]
          exact isClosed_le continuous_const (continuous_eval_snoc_prod G i)
        · rw [ite_eq_right h1]; exact isClosed_univ
    · exact isClosed_iInter fun i => by
        have hh : {p : (Fin m → ℝ) × ℝ |
              v i = -1 → MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i) ≤ 0} =
            if v i = -1 then {p : (Fin m → ℝ) × ℝ |
                MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i) ≤ 0} else Set.univ := by
          by_cases h1 : v i = -1 <;> simp [h1]
        rw [hh]
        by_cases h1 : v i = -1
        · rw [ite_eq_left h1]
          exact isClosed_le (continuous_eval_snoc_prod G i) continuous_const
        · rw [ite_eq_right h1]; exact isClosed_univ
    · exact isClosed_iInter fun i => by
        have hh : {p : (Fin m → ℝ) × ℝ |
              v i = 0 → MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i) = 0} =
            if v i = 0 then {p : (Fin m → ℝ) × ℝ |
                MvPolynomial.eval (Fin.snoc p.1 p.2) (G.get i) = 0} else Set.univ := by
          by_cases h1 : v i = 0 <;> simp [h1]
        rw [hh]
        by_cases h1 : v i = 0
        · rw [ite_eq_left h1]
          exact isClosed_eq (continuous_eval_snoc_prod G i) continuous_const
        · rw [ite_eq_right h1]; exact isClosed_univ
  let X : Set ((Fin m → ℝ) × ℝ) := {p | p.1 ∈ C.set} ∩ D
  have hXeq : X = {p : (Fin m → ℝ) × ℝ | p.1 ∈ C.set} ∩ D := rfl
  have hfibeq : ∀ x ∈ C.set, {t : ℝ | (x, t) ∈ X} = Fib G v x := by
    intro x hx
    ext t
    simp only [X, Set.mem_ofPred_eq, Set.mem_inter_iff, hD]
    constructor
    · rintro ⟨-, h⟩
      rw [← hFibCl x hx]
      exact h
    · intro ht
      exact ⟨hx, Fib_subset_FibCl G v x ht⟩
  have hres := isPreconnected_of_closed_fibers_rel hC hDclosed hXeq
    (fun x hx => by rw [hfibeq x hx]; exact (hord x).isPreconnected)
    (fun x hx => by
      obtain ⟨t, ht⟩ := hne x hx
      refine ⟨t, ?_⟩
      rw [← hfibeq x hx] at ht
      exact ht)
    (fun x hx => by
      obtain ⟨B, hB⟩ := hbdd x hx
      refine ⟨B, hB.mono ?_⟩
      intro x' hx' t htX
      have h1 : t ∈ Fib G v x' := by rw [← hfibeq x' htX.1]; exact htX
      have h2 := h1 i₀
      rw [← spec_eval_snoc] at h2
      exact hx' htX.1 t (sign_eq_zero_iff.mp (by rw [h2, hvi₀])))
  have hcell : (Work.WilE4.cell C G v).set =
      (fun p : (Fin m → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (m + 1) → ℝ)) '' X := by
    ext z
    constructor
    · intro hz
      rw [mem_cell_iff] at hz
      refine ⟨(Fin.init z, z (Fin.last m)), ?_, Fin.snoc_init_self z⟩
      rw [hXeq]
      refine ⟨hz.1, ?_⟩
      rw [hD]
      have h1 : z (Fin.last m) ∈ Fib G v (Fin.init z) := by
        rw [Fib_eq_pcell]
        intro i
        rw [spec_eval_snoc, Fin.snoc_init_self z]
        exact hz.2 i
      exact fun i => (Fib_subset_FibCl G v (Fin.init z)) h1 i
    · rintro ⟨p, hp, rfl⟩
      rw [mem_cell_iff, Fin.init_snoc]
      refine ⟨hp.1, ?_⟩
      have h1 : ∀ i : Fin G.length,
          SignType.sign ((spec (G.get i) p.1).eval p.2) = v i := by
        have hDp : p.2 ∈ FibCl G v p.1 := fun i => hp.2 i
        rw [hFibCl p.1 hp.1] at hDp
        rwa [Fib_eq_pcell G v p.1] at hDp
      intro i
      rw [← spec_eval_snoc]
      exact h1 i
  rw [hcell]
  exact hres.image _ continuous_snoc_prod.continuousOn

/-! ## The main theorem -/

theorem cell_preconnected {m : ℕ} (G : List (MvPolynomial (Fin (m + 1)) ℝ))
    (C : Work.WilE4.SAd m) (v : Fin G.length → SignType)
    (hC : IsPreconnected C.set)
    (hderiv : ∀ i : Fin G.length,
      MvPolynomial.pderiv (Fin.last m) (G.get i) = 0 ∨
        ∃ j : Fin G.length, G.get j = MvPolynomial.pderiv (Fin.last m) (G.get i))
    (hconst : ∀ i : Fin G.length, ∀ j : ℕ, j ≤ (G.get i).degreeOf (Fin.last m) →
      ∀ x ∈ C.set, ∀ x' ∈ C.set,
      SignType.sign ((Work.WilE4.spec (G.get i) x).coeff j)
        = SignType.sign ((Work.WilE4.spec (G.get i) x').coeff j))
    (hreal : ∀ x ∈ C.set, ∃ t : ℝ, ∀ i : Fin G.length,
      SignType.sign (MvPolynomial.eval (Fin.snoc x t) (G.get i)) = v i) :
    IsPreconnected (Work.WilE4.cell C G v).set := by
  classical
  by_cases hCne : C.set.Nonempty
  swap
  · have hempty : (Work.WilE4.cell C G v).set = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [mem_cell_iff] at hz
      exact hCne ⟨_, hz.1⟩
    rw [hempty]
    exact isPreconnected_empty
  obtain ⟨x₀, hx₀⟩ := hCne
  have hne : ∀ x ∈ C.set, (Fib G v x).Nonempty := by
    intro x hx
    obtain ⟨t, ht⟩ := hreal x hx
    exact ⟨t, ht⟩
  have hord : ∀ x : Fin m → ℝ, Set.OrdConnected (Fib G v x) := fun x => Fib_ordConnected G v hderiv x
  by_cases hS : ∃ i : Fin G.length, v i = 0 ∧ spec (G.get i) x₀ ≠ 0
  · obtain ⟨i₀, hvi₀, hpos₀⟩ := hS
    have hpos : ∀ x ∈ C.set, spec (G.get i₀) x ≠ 0 := fun x hx h =>
      hpos₀ ((spec_zero_iff G C v hconst i₀ hx hx₀).mp h)
    have hzero : ∀ x ∈ C.set, ∀ i : Fin G.length, spec (G.get i) x = 0 → v i = 0 := by
      intro x hx i hi
      obtain ⟨t, ht⟩ := hreal x hx
      have h1 := ht i
      rw [← spec_eval_snoc, hi] at h1
      simp only [Polynomial.eval_zero, sign_zero] at h1
      exact h1.symm
    refine preconnected_cell_caseS G C v i₀ hvi₀ hpos hzero
      (fun x => spec_deriv_closed G hderiv x) hne hord ?_ hC
    intro x hx
    exact roots_bdd_near G C v hconst i₀ hpos hx
  · push Not at hS
    refine preconnected_cell_caseI G C v hC ?_ hord hne
    intro i hi x hx
    exact (spec_zero_iff G C v hconst i hx₀ hx).mp (hS i hi)

end Work.WilE4.CAD
