import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.exists_enum_critical
import Submission.Work.Drive.N2.exists_chart_ball_noOtherCritical
import Submission.Work.Drive.N2.exists_disjoint_chart_neighborhoods
import Submission.Work.Drive.N2.exists_perturbation_delta
import Submission.Work.Drive.N2.isCritical_nondegCrit_congr_add

/-!
# Perturbing a Morse function to distinct critical values (compact surfaces)

The target `Work.Drive.N2.exists_distinct_criticalValues` is the statement that a smooth function on a
compact surface whose critical points are all nondegenerate can be perturbed, without moving its
critical set, to a function whose critical values are pairwise distinct.

The proof is the standard `f + ε χ` construction: a smooth bump `χ` equal to `1` near a critical point
`p` and supported in a small neighbourhood of `p` (small enough that the closure of the support
contains no other critical point) leaves the critical set unchanged for sufficiently small `ε`, while
moving the value at `p` by `ε`.  Doing this for all critical points simultaneously, with small
multiples `ε * (i + 1)` of a single generic `ε`, gives pairwise distinct critical values.  The bricks
used are

* `Work.Drive.N2.exists_smooth_bump_manifold` (here) — the bump itself;
* `Work.Drive.N2.exists_chart_ball_noOtherCritical` — a nondegenerate critical point is isolated;
* `Work.Drive.N2.exists_injective_enum_critical` (here) — the critical set is finite;
* `Work.Drive.N2.exists_disjoint_chart_neighborhoods` — disjoint chart neighbourhoods;
* `Work.Drive.N2.exists_perturbation_delta` — the perturbation does not move the critical set;
* `Work.Drive.N2.isCritical_nondegCrit_congr_add` — criticality is a local (germ) condition.
-/

-- A local `Fintype` instance is needed for `Fintype.equivFin` in the enumeration lemma; the style
-- linter's suggestion to use `let` does not apply.
set_option linter.style.haveILetI false

namespace Work.Drive.N2

open scoped Manifold ContDiff
open Filter Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

section Bump

/-- A smooth bump on a surface: for a point `p` and an open neighbourhood `T` of it, there is a
smooth `χ : M → ℝ` with values in `[0,1]`, equal to `1` on a neighbourhood of `p`, whose support is
contained in `T`. -/
theorem exists_smooth_bump_manifold [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (p : M) (T : Set M) (hT : IsOpen T) (hpT : p ∈ T) :
    ∃ χ : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ χ p = 1 ∧
      Function.support χ ⊆ T ∧ ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ ∀ x ∈ V, χ x = 1 := by
  have hclosed : IsClosed ({p} : Set M) := isClosed_singleton
  have hsub : ({p} : Set M) ⊆ interior T := by
    rw [hT.interior_eq]
    exact Set.singleton_subset_iff.mpr hpT
  obtain ⟨f, hf1, hf2, hf3⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓡 2) (n := (⊤ : ℕ∞)) hclosed hsub
  rw [nhdsSet_singleton] at hf1
  obtain ⟨V, hVs, hVopen, hpV⟩ := _root_.mem_nhds_iff.mp hf1
  exact ⟨(f : M → ℝ), f.contMDiff, fun x => ⟨(hf3 x).1, (hf3 x).2⟩, hVs hpV,
    Function.support_subset_iff'.mpr hf2, V, hVopen, hpV, hVs⟩

end Bump

section Enumerate

/-- A finite subset of `ℝ` cannot exhaust an interval `(0, δ)` with `δ > 0`. -/
lemma exists_pos_lt_notMem_of_finite {S : Set ℝ} (hS : S.Finite) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε ∉ S := by
  obtain ⟨T, hT⟩ := hS.exists_finset
  rcases (T.filter fun t => t ∈ Set.Ioo (0 : ℝ) δ).eq_empty_or_nonempty with hemp | hne
  · refine ⟨δ / 2, half_pos hδ, half_lt_self hδ, fun hmem => ?_⟩
    have : δ / 2 ∈ T.filter (fun t => t ∈ Set.Ioo (0 : ℝ) δ) := by
      rw [Finset.mem_filter]
      exact ⟨(hT _).mpr hmem, half_pos hδ, half_lt_self hδ⟩
    rw [hemp] at this
    exact absurd this (Finset.notMem_empty _)
  · set t := (T.filter fun t => t ∈ Set.Ioo (0 : ℝ) δ).max' hne with ht
    have htmem : t ∈ T.filter (fun t => t ∈ Set.Ioo (0 : ℝ) δ) := Finset.max'_mem _ _
    have htf : t ∈ Set.Ioo (0 : ℝ) δ := (Finset.mem_filter.mp htmem).2
    have htT : t ∈ T := (Finset.mem_filter.mp htmem).1
    refine ⟨(t + δ) / 2, by linarith [htf.1, hδ], by linarith [htf.2], fun hmem => ?_⟩
    have hmem' : (t + δ) / 2 ∈ T.filter (fun t => t ∈ Set.Ioo (0 : ℝ) δ) := by
      rw [Finset.mem_filter]
      exact ⟨(hT _).mpr hmem, by linarith [htf.1, hδ], by linarith [htf.2]⟩
    have hle : (t + δ) / 2 ≤ t := Finset.le_max' _ _ hmem'
    linarith [htf.2]

/-- For a finite family of positive reals `d i` (`i ∈ s`) and a finite forbidden set `S`, there is
`ε > 0` with `ε < d i` for all `i ∈ s` and `ε ∉ S`. -/
lemma exists_pos_lt_all_of_finite {ι : Type*} (s : Finset ι) (d : ι → ℝ) (hd : ∀ i, 0 < d i)
    {S : Set ℝ} (hS : S.Finite) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ i ∈ s, ε < d i) ∧ ε ∉ S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨ε, hε, -, hεS⟩ := exists_pos_lt_notMem_of_finite hS one_pos
      exact ⟨ε, hε, by simp, hεS⟩
  | insert a s ha ih =>
      obtain ⟨ε, hεpos, hεd, hεS⟩ := ih
      obtain ⟨ε', hε'pos, hε'lt, hε'S⟩ :=
        exists_pos_lt_notMem_of_finite (hS.union (Set.finite_singleton (min ε (d a))))
          (lt_min hεpos (hd a))
      refine ⟨ε', hε'pos, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact lt_of_lt_of_le hε'lt (min_le_right _ _)
        · exact lt_of_lt_of_le (lt_of_lt_of_le hε'lt (min_le_left _ _)) (le_of_lt (hεd i hi))
      · intro hmem
        exact hε'S (Set.mem_union_left _ hmem)

/-- The critical set of a Morse function on a compact surface can be listed injectively. -/
theorem exists_injective_enum_critical [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, Work.Drive.Morse.IsCritical f x → Work.Drive.Morse.NondegCrit f x) :
    ∃ (k : ℕ) (p : Fin k → M), Function.Injective p ∧
      (∀ i, Work.Drive.Morse.IsCritical f (p i)) ∧
      (∀ x, Work.Drive.Morse.IsCritical f x → ∃ i, p i = x) := by
  obtain ⟨k₀, p₀, hcrit₀, hcover₀⟩ := exists_enum_critical f hf hnd
  have hfin : (Set.range p₀).Finite := Set.finite_range p₀
  letI := hfin.fintype
  let e := Fintype.equivFin (Set.range p₀)
  refine ⟨Fintype.card (Set.range p₀), fun i => (e.symm i).1, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro i
    obtain ⟨j, hj⟩ := (e.symm i).2
    show Work.Drive.Morse.IsCritical f ((e.symm i).1)
    rw [← hj]
    exact hcrit₀ j
  · intro x hx
    obtain ⟨j, hj⟩ := hcover₀ x hx
    refine ⟨e ⟨p₀ j, ⟨j, rfl⟩⟩, ?_⟩
    show (e.symm (e ⟨p₀ j, ⟨j, rfl⟩⟩)).1 = x
    rw [Equiv.symm_apply_apply]
    exact hj

end Enumerate

open scoped Manifold ContDiff in
/-- A Morse function on a compact surface can be perturbed to a Morse function with the *same* set of
critical points and with pairwise distinct critical values.  (The "same critical points" requirement
forces the perturbation to be small enough not to create or destroy critical points; it is what the
consumer needs, and it prevents the statement from being discharged by an unrelated existence
theorem.) -/
theorem exists_distinct_criticalValues {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] (f : M → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, Work.Drive.Morse.IsCritical f x → Work.Drive.Morse.NondegCrit f x) :
    ∃ g : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ x, Work.Drive.Morse.IsCritical g x ↔ Work.Drive.Morse.IsCritical f x) ∧
      (∀ x, Work.Drive.Morse.IsCritical g x → Work.Drive.Morse.NondegCrit g x) ∧
      (∀ x y, Work.Drive.Morse.IsCritical g x → Work.Drive.Morse.IsCritical g y →
        g x = g y → x = y) := by
  classical
  obtain ⟨k, p, hinj, hcrit, hcover⟩ := exists_injective_enum_critical f hf hnd
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine ⟨f, hf, fun x => Iff.rfl, hnd, ?_⟩
    intro x y hx hy hxy
    obtain ⟨i, hi⟩ := hcover x hx
    exact absurd i.2 (Nat.not_lt_zero _)
  · obtain ⟨T, hTopen, hpT, hTchart, hTnd, hTdisj⟩ := exists_disjoint_chart_neighborhoods f hf hnd p hinj hcrit hcover
    -- bump functions
    have hbump : ∀ i : Fin k, ∃ χ : M → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ ∧
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ χ (p i) = 1 ∧ Function.support χ ⊆ T i ∧
        ∃ V : Set M, IsOpen V ∧ p i ∈ V ∧ ∀ x ∈ V, χ x = 1 :=
      fun i => exists_smooth_bump_manifold (p i) (T i) (hTopen i) (hpT i)
    choose χ hχsm hχ01 hχp hχsupp hχV using hbump
    -- the sizes
    have hδex : ∀ i : Fin k, ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => f x + ε * χ i x) ∧
        (∀ x, Work.Drive.Morse.IsCritical (fun x => f x + ε * χ i x) x ↔
          Work.Drive.Morse.IsCritical f x) ∧
        (∀ x, Work.Drive.Morse.IsCritical (fun x => f x + ε * χ i x) x →
          Work.Drive.Morse.NondegCrit (fun x => f x + ε * χ i x) x) ∧
        (∀ x, Work.Drive.Morse.IsCritical f x → x ≠ p i → f x + ε * χ i x = f x) ∧
        (fun x => f x + ε * χ i x) (p i) = f (p i) + ε :=
      fun i => exists_perturbation_delta f hf hnd (p i) (hnd (p i) (hcrit i)) (T i) (hTopen i) (hpT i)
        (hTnd i) (hTchart i) (χ i) (hχsm i) (hχ01 i) (hχp i) (hχsupp i) (hχV i)
    choose δ hδpos hδprop using hδex
    -- the weights
    let w : Fin k → ℝ := fun i => (i : ℝ) + 1
    have hwpos : ∀ i : Fin k, 0 < w i := by intro i; simp only [w]; positivity
    have hwinj : Function.Injective w := by
      intro i j hij
      have h1 : (i : ℝ) = (j : ℝ) := by have h2 := hij; simp only [w] at h2; linarith
      exact Fin.ext (Nat.cast_inj.mp h1)
    -- the forbidden values
    set Bad : Set ℝ := (fun q : {ij : Fin k × Fin k // ij.1 ≠ ij.2} =>
        (f (p q.1.2) - f (p q.1.1)) / (w q.1.1 - w q.1.2)) '' Set.univ with hBad
    have hBadfin : Bad.Finite := by
      rw [hBad]
      exact Set.Finite.image _ Set.finite_univ
    obtain ⟨ε, hεpos, hεlt, hεbad⟩ :=
      exists_pos_lt_all_of_finite (Finset.univ : Finset (Fin k)) (fun i => δ i / w i)
        (fun i => div_pos (hδpos i) (hwpos i)) hBadfin
    have hεw : ∀ i : Fin k, 0 < ε * w i ∧ ε * w i < δ i := by
      intro i
      refine ⟨mul_pos hεpos (hwpos i), ?_⟩
      have h2 : ε * w i < (δ i / w i) * w i :=
        mul_lt_mul_of_pos_right (hεlt i (Finset.mem_univ i)) (hwpos i)
      rwa [div_mul_cancel₀ _ (ne_of_gt (hwpos i))] at h2
    -- the perturbed function
    set g : M → ℝ := fun x => f x + ∑ i : Fin k, (ε * w i) * χ i x with hgdef
    have hg_sm : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ g := by
      rw [hgdef]
      exact hf.add (ContMDiff.sum fun i _ => contMDiff_const.mul (hχsm i))
    have hsm_i : ∀ i : Fin k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
        (fun y => f y + (ε * w i) * χ i y) :=
      fun i => hf.add (contMDiff_const.mul (hχsm i))
    -- a bump vanishes near a point outside the closure of its own neighbourhood
    have hχzero_of_notMem : ∀ (i : Fin k) (x : M), x ∉ closure (T i) →
        ∀ᶠ y in 𝓝 x, χ i y = 0 := by
      intro i x hx
      have htsub : tsupport (χ i) ⊆ closure (T i) := closure_mono (hχsupp i)
      have hmem_nhds : (tsupport (χ i))ᶜ ∈ 𝓝 x :=
        (isClosed_tsupport _).isOpen_compl.mem_nhds (fun hmem => hx (htsub hmem))
      filter_upwards [hmem_nhds] with y hy
      by_contra hne
      exact hy (subset_tsupport _ (Function.mem_support.mpr hne))
    -- values of the bumps at the critical points
    have hχval : ∀ (i j : Fin k), j ≠ i → χ j (p i) = 0 := by
      intro i j hji
      have hxi : p i ∈ closure (T i) := subset_closure (hpT i)
      have hxnot : p i ∉ closure (T j) :=
        fun hmem => (Set.disjoint_left.mp (hTdisj i j (fun h => hji h.symm))) hxi hmem
      by_contra hne
      exact hxnot (subset_closure (hχsupp j (Function.mem_support.mpr hne)))
    -- germ: `g` agrees with the single perturbation where that bump lives
    have hgerm : ∀ (i : Fin k) (x : M), x ∈ closure (T i) →
        g =ᶠ[𝓝 x] (fun y => f y + (ε * w i) * χ i y) := by
      intro i x hx
      have hall : ∀ᶠ y in 𝓝 x, ∀ j : Fin k, j ≠ i → χ j y = 0 := by
        rw [Filter.eventually_all]
        intro j
        by_cases hji : j = i
        · subst hji
          exact Filter.Eventually.of_forall (fun y hy => absurd rfl hy)
        · have hxnot : x ∉ closure (T j) :=
            fun hmem => (Set.disjoint_left.mp (hTdisj i j (fun h => hji h.symm))) hx hmem
          exact (hχzero_of_notMem j x hxnot).mono (fun y hy _ => hy)
      have hsum : ∀ᶠ y in 𝓝 x, (∑ j : Fin k, (ε * w j) * χ j y) = (ε * w i) * χ i y := by
        filter_upwards [hall] with y hy
        exact Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
          (fun b _ hb => by rw [hy b hb, mul_zero])
      filter_upwards [hsum] with y hy
      rw [hgdef]
      exact congrArg (fun t => f y + t) hy
    -- germ: `g` agrees with `f` far from all the neighbourhoods
    have hgermf : ∀ x : M, (∀ i : Fin k, x ∉ closure (T i)) → g =ᶠ[𝓝 x] f := by
      intro x hx
      have hall : ∀ᶠ y in 𝓝 x, ∀ i : Fin k, χ i y = 0 := by
        rw [Filter.eventually_all]
        intro i
        exact hχzero_of_notMem i x (hx i)
      filter_upwards [hall] with y hy
      rw [hgdef]
      simp [hy]
    have hcrit_iff : ∀ x, Work.Drive.Morse.IsCritical g x ↔ Work.Drive.Morse.IsCritical f x := by
      intro x
      by_cases hx : ∃ i : Fin k, x ∈ closure (T i)
      · obtain ⟨i, hxi⟩ := hx
        have hδi := hδprop i (ε * w i) (hεw i).1 (hεw i).2
        exact (isCritical_nondegCrit_congr_add hg_sm (hsm_i i) x 0 (by simpa using hgerm i x hxi)).1.trans (hδi.2.1 x)
      · exact (isCritical_nondegCrit_congr_add hg_sm hf x 0 (by
          simpa using hgermf x (fun i hi => hx ⟨i, hi⟩))).1
    have hnd_g : ∀ x, Work.Drive.Morse.IsCritical g x → Work.Drive.Morse.NondegCrit g x := by
      intro x hx
      have hxf : Work.Drive.Morse.IsCritical f x := (hcrit_iff x).mp hx
      obtain ⟨i, hi⟩ := hcover x hxf
      subst hi
      have hxi : p i ∈ closure (T i) := subset_closure (hpT i)
      have hδi := hδprop i (ε * w i) (hεw i).1 (hεw i).2
      have hcrit_ge : Work.Drive.Morse.IsCritical (fun y => f y + (ε * w i) * χ i y) (p i) :=
        (hδi.2.1 (p i)).mpr (hcrit i)
      have hndge : Work.Drive.Morse.NondegCrit (fun y => f y + (ε * w i) * χ i y) (p i) :=
        hδi.2.2.1 (p i) hcrit_ge
      exact (isCritical_nondegCrit_congr_add hg_sm (hsm_i i) (p i) 0 (by simpa using hgerm i (p i) hxi)).2.mpr hndge
    have hval : ∀ i : Fin k, g (p i) = f (p i) + ε * w i := by
      intro i
      show f (p i) + (∑ j : Fin k, (ε * w j) * χ j (p i)) = f (p i) + ε * w i
      have hsum : (∑ j : Fin k, (ε * w j) * χ j (p i)) = (ε * w i) * χ i (p i) :=
        Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
          (fun b _ hb => by rw [hχval i b hb, mul_zero])
      rw [hsum, hχp i, mul_one]
    refine ⟨g, hg_sm, hcrit_iff, hnd_g, ?_⟩
    intro x y hx hy hxy
    have hxf : Work.Drive.Morse.IsCritical f x := (hcrit_iff x).mp hx
    have hyf : Work.Drive.Morse.IsCritical f y := (hcrit_iff y).mp hy
    obtain ⟨i, hi⟩ := hcover x hxf
    obtain ⟨j, hj⟩ := hcover y hyf
    by_cases hij : i = j
    · rw [← hi, ← hj, hij]
    · exfalso
      have hbad : ε * (w i - w j) = f (p j) - f (p i) := by
        have h := hxy
        rw [← hi, ← hj, hval i, hval j] at h
        linarith
      have hmemBad : ε ∈ Bad := by
        rw [hBad]
        refine ⟨⟨(i, j), hij⟩, Set.mem_univ _, ?_⟩
        change (f (p j) - f (p i)) / (w i - w j) = ε
        have hne : w i - w j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hwinj h))
        rw [← hbad]
        field_simp
      exact hεbad hmemBad

end Work.Drive.N2
