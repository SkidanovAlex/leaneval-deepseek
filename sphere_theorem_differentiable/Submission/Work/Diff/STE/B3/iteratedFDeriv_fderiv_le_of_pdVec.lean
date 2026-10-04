import Mathlib
import Submission.Work.Diff.STE.B3.LowJetDefs
import Submission.Work.Diff.STE.B3.norm_multilinear_le_of_basis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Iterated derivatives of a first partial derivative, bounded by the `pdVec` data

The target of this file is `Work.Diff.STE.B3.iteratedFDeriv_fderiv_le_of_pdVec`: the `m`-th
iterated derivative at `z` of the first partial derivative `pdR c f` of a smooth function
`f : (Fin n → ℝ) → ℝ` is bounded by a constant times a quantity `Kd` which dominates all
`pdVec`-norms of the complexified `f` up to order `M + 1`.

The mathematical content is:

* `‖D^m (D_c f) z‖ ≤ n^m · max_γ |∂^β f (z)|` where `β` runs over the multi-indices of order
  `m + 1` (in fact each coordinate value is *exactly* one such iterated partial derivative);
* an iterated partial derivative of `f` has the same modulus as the corresponding `pdVec`
  quantity of the complexification of `f`.

The bridge between `iteratedFDeriv` and the iterated partial derivatives `pdX`/`pdVecX` is
proved *locally* (on an open set on which `f` is `C^K`): the key identity is
`pdVecX k l H y = iteratedFDerivWithin ℝ k H v y (fun j => Pi.single (l j) 1)`, an induction
which "peels the first direction" using
`fderiv_continuousMultilinear_apply_const` in its `fderivWithin` form.
-/

namespace Work.Diff.STE.B3

open scoped ContDiff

set_option maxHeartbeats 1000000

/-- The partial derivative of `h` in the coordinate direction `i`, for an arbitrary codomain. -/
noncomputable def pdX {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin n) (h : (Fin n → ℝ) → F) : (Fin n → ℝ) → F :=
  fun x => fderiv ℝ h x (Pi.single i 1)

/-- The iterated partial derivative of `h` along the directions `l`. -/
noncomputable def pdVecX {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (l : Fin k → Fin n) (h : (Fin n → ℝ) → F) : (Fin n → ℝ) → F :=
  (List.ofFn l).foldr (fun i g => pdX i g) h

lemma pdVecX_eq_pdVec {n : ℕ} (k : ℕ) (l : Fin k → Fin n)
    (h : (Fin n → ℝ) → ℂ) : pdVecX k l h = Work.Diff.STE.pdVec k l h := rfl

lemma pdVecX_eq_pdRVec {n : ℕ} (k : ℕ) (l : Fin k → Fin n)
    (h : (Fin n → ℝ) → ℝ) : pdVecX k l h = Work.Diff.STE.pdRVec k l h := rfl

/-! ## The local identity between iterated derivatives and iterated partial derivatives -/

/-- **The core local identity.**  On an open set `v` on which `H` is `C^K`, the `k`-th iterated
derivative of `H` within `v`, evaluated on the constant directions
`Pi.single (l j) 1` (`j : Fin k`), is the iterated partial derivative `pdVecX k l H`. -/
lemma pdVecX_eq_iteratedFDerivWithin {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : Set (Fin n → ℝ)} (hv : IsOpen v) {H : (Fin n → ℝ) → F} {K : ℕ}
    (hK : ContDiffOn ℝ ((K : ℕ) : ℕ∞ω) H v) :
    ∀ (k : ℕ) (l : Fin k → Fin n), k + 1 ≤ K →
      Set.EqOn (pdVecX k l H)
        (fun y => iteratedFDerivWithin ℝ k H v y (fun j => Pi.single (l j) 1)) v := by
  intro k
  induction k with
  | zero =>
    intro l _ y _
    rw [pdVecX, List.ofFn_zero, List.foldr_nil]
    exact (iteratedFDerivWithin_zero_apply (𝕜 := ℝ) (f := H) (s := v) (x := y)
      (fun j => Pi.single (l j) 1)).symm
  | succ k ih =>
    intro l hk y hy
    have hk' : k + 1 ≤ K := by omega
    have hK1 : ContDiffOn ℝ (((k + 1 : ℕ)) : ℕ∞ω) H v :=
      hK.of_le (by exact_mod_cast (show k + 1 ≤ K by omega))
    -- peel the first direction
    have hpd : pdVecX (k + 1) l H = pdX (l 0) (pdVecX k (Fin.tail l) H) := by
      have hcons : List.ofFn l = l 0 :: List.ofFn (Fin.tail l) := by
        conv_lhs => rw [← Fin.cons_self_tail l]
        rw [List.ofFn_cons]
      simp only [pdVecX]
      rw [hcons, List.foldr_cons]
    have hIH : Set.EqOn
        (fun y' => iteratedFDerivWithin ℝ k H v y' (fun j => Pi.single ((Fin.tail l) j) 1))
        (pdVecX k (Fin.tail l) H) v := ((ih (Fin.tail l) hk').symm)
    have hdiff : DifferentiableWithinAt ℝ (iteratedFDerivWithin ℝ k H v) v y :=
      (hK1.differentiableOn_iteratedFDerivWithin (by exact_mod_cast Nat.lt_succ_self k)
        hv.uniqueDiffOn) y hy
    rw [hpd]
    simp only [pdX]
    rw [← fderivWithin_of_isOpen hv hy]
    rw [← fderivWithin_congr' hIH hy]
    rw [fderivWithin_continuousMultilinear_apply_const_apply (hv.uniqueDiffWithinAt hy) hdiff
      (fun j => Pi.single ((Fin.tail l) j) 1) (Pi.single (l 0) 1)]
    rw [iteratedFDerivWithin_succ_apply_left (𝕜 := ℝ) (f := H) (s := v) (x := y) (n := k)
      (m := fun j => Pi.single (l j) 1)]
    rfl

/-! ## Smoothness of the first partial derivative and of the complexification -/

/-- If `f` is `C^{K}` on the open set `v`, so is `pdR c f`. -/
lemma contDiffOn_pdR {n : ℕ} {f : (Fin n → ℝ) → ℝ} {v : Set (Fin n → ℝ)} (hv : IsOpen v)
    {K : ℕ} (hK : ContDiffOn ℝ ((K + 1 : ℕ) : ℕ∞ω) f v) (c : Fin n) :
    ContDiffOn ℝ ((K : ℕ) : ℕ∞ω) (Work.Diff.STE.pdR c f) v := by
  have hfd : ContDiffOn ℝ ((K : ℕ) : ℕ∞ω) (fderivWithin ℝ f v) v :=
    hK.fderivWithin hv.uniqueDiffOn (by rw [← Nat.cast_add_one])
  refine ContDiffOn.congr (hfd.clm_apply (contDiffOn_const (c := Pi.single c (1 : ℝ)))) ?_
  intro y hy
  simp only [Work.Diff.STE.pdR]
  rw [fderivWithin_of_isOpen hv hy]

/-- The complexification of a function that is `C^K` on `v` is `C^K` on `v`. -/
lemma contDiffOn_ofReal_comp {n : ℕ} {f : (Fin n → ℝ) → ℝ} {v : Set (Fin n → ℝ)}
    {K : ℕ} (h : ContDiffOn ℝ ((K : ℕ) : ℕ∞ω) f v) :
    ContDiffOn ℝ ((K : ℕ) : ℕ∞ω) (fun y => ((f y : ℝ) : ℂ)) v :=
  h.continuousLinearMap_comp Complex.ofRealCLM

/-- A neighbourhood on which `f` is `C^K`, extracted from smoothness at a point. -/
lemma exists_contDiffOn_nhds {n : ℕ} {f : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ} (K : ℕ)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) :
    ∃ v : Set (Fin n → ℝ), IsOpen v ∧ z ∈ v ∧ ContDiffOn ℝ ((K : ℕ) : ℕ∞ω) f v := by
  have hle : ((K : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) :=
    by exact_mod_cast (le_top : ((K : ℕ) : ℕ∞) ≤ ⊤)
  have h' : ((K : ℕ) : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) → ((K : ℕ) : ℕ∞ω) = (⊤ : ℕ∞ω) := by
    intro h; simp at h
  obtain ⟨u, hu, hcont⟩ := (hf.of_le hle).contDiffOn le_rfl h'
  obtain ⟨v, hvu, hvopen, hzv⟩ := mem_nhds_iff.mp hu
  exact ⟨v, hvopen, hzv, hcont.mono hvu⟩

/-! ## The list identity moving `pdR c` inside the iterated derivative -/

lemma pdRVec_pdR_eq_pdRVec_snoc {n : ℕ} (m : ℕ) (γ : Fin m → Fin n) (c : Fin n)
    (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) :
    Work.Diff.STE.pdRVec m γ (Work.Diff.STE.pdR c f) z
      = Work.Diff.STE.pdRVec (m + 1) (Fin.snoc γ c) f z := by
  have hlist : List.ofFn (Fin.snoc γ c) = List.ofFn γ ++ [c] := by
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [Fin.snoc_last, Fin.snoc_castSucc]
  simp only [Work.Diff.STE.pdRVec, Work.Diff.STE.pdRList]
  rw [hlist, List.foldr_append, List.foldr_cons, List.foldr_nil]

/-! ## The main theorem -/

theorem iteratedFDeriv_fderiv_le_of_pdVec {n M : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (c : Fin n) (Kd : ℝ), 0 ≤ Kd →
        ContDiffAt ℝ (⊤ : ℕ∞) f z →
        (∀ m ≤ M + 1, ∀ β : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m β (fun y => ((f y : ℝ) : ℂ)) z‖ ≤ Kd) →
        ∀ m ≤ M, ‖iteratedFDeriv ℝ m (fun y => Work.Diff.STE.pdR c f y) z‖ ≤ C * Kd := by
  classical
  refine ⟨(max (n : ℝ) 1) ^ M, by positivity, ?_⟩
  intro f z c Kd hKd hf hpd m hm
  obtain ⟨v, hvopen, hzv, hcont⟩ := exists_contDiffOn_nhds (f := f) (z := z) (m + 2) hf
  set F2 : (Fin n → ℝ) → ℂ := fun y => ((f y : ℝ) : ℂ) with hF2
  have hcont_pdR : ContDiffOn ℝ (((m + 1 : ℕ)) : ℕ∞ω) (Work.Diff.STE.pdR c f) v :=
    contDiffOn_pdR hvopen hcont c
  have hcont_F2 : ContDiffOn ℝ (((m + 2 : ℕ)) : ℕ∞ω) F2 v := by
    have h := contDiffOn_ofReal_comp (f := f) (v := v) (K := m + 2) hcont
    rwa [hF2]
  -- the value of the `m`-th derivative on a basis tuple
  have hbound : ∀ γ : Fin m → Fin n,
      ‖iteratedFDeriv ℝ m (Work.Diff.STE.pdR c f) z (fun i => Pi.single (γ i) 1)‖ ≤ Kd := by
    intro γ
    set β : Fin (m + 1) → Fin n := Fin.snoc γ c with hβ
    have hA1 := pdVecX_eq_iteratedFDerivWithin (v := v) hvopen
      (H := Work.Diff.STE.pdR c f) (K := m + 1) hcont_pdR
    have hA2 := pdVecX_eq_iteratedFDerivWithin (v := v) hvopen (H := f) (K := m + 2) hcont
    have hA3 := pdVecX_eq_iteratedFDerivWithin (v := v) hvopen (H := F2) (K := m + 2) hcont_F2
    have e1 : iteratedFDeriv ℝ m (Work.Diff.STE.pdR c f) z (fun i => Pi.single (γ i) 1)
        = Work.Diff.STE.pdRVec m γ (Work.Diff.STE.pdR c f) z := by
      have hA : pdVecX m γ (Work.Diff.STE.pdR c f) z
          = iteratedFDerivWithin ℝ m (Work.Diff.STE.pdR c f) v z (fun i => Pi.single (γ i) 1) :=
        (hA1 m γ le_rfl) hzv
      rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := Work.Diff.STE.pdR c f) m hvopen hzv, ← hA, pdVecX_eq_pdRVec]
    have e2 : Work.Diff.STE.pdRVec m γ (Work.Diff.STE.pdR c f) z
        = Work.Diff.STE.pdRVec (m + 1) β f z := by
      rw [hβ]
      exact pdRVec_pdR_eq_pdRVec_snoc m γ c f z
    have e3 : Work.Diff.STE.pdRVec (m + 1) β f z
        = iteratedFDeriv ℝ (m + 1) f z (fun i => Pi.single (β i) 1) := by
      have hA : iteratedFDerivWithin ℝ (m + 1) f v z (fun i => Pi.single (β i) 1)
          = pdVecX (m + 1) β f z := ((hA2 (m + 1) β le_rfl).symm) hzv
      rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) (m + 1) hvopen hzv, hA,
        pdVecX_eq_pdRVec]
    have hi : (((m + 1 : ℕ)) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) :=
      by exact_mod_cast (le_top : (((m + 1 : ℕ)) : ℕ∞) ≤ ⊤)
    have hcomp : iteratedFDeriv ℝ (m + 1) F2 z
        = Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ (m + 1) f z) := by
      have h := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ) Complex.ofRealCLM
        (f := f) hf (i := m + 1) hi
      rw [hF2]
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using h
    have e4 : ((iteratedFDeriv ℝ (m + 1) f z (fun i => Pi.single (β i) 1) : ℝ) : ℂ)
        = iteratedFDeriv ℝ (m + 1) F2 z (fun i => Pi.single (β i) 1) := by
      rw [hcomp, ContinuousLinearMap.compContinuousMultilinearMap_coe]
      simp only [Function.comp_apply, Complex.ofRealCLM_apply]
    have e5 : iteratedFDeriv ℝ (m + 1) F2 z (fun i => Pi.single (β i) 1)
        = Work.Diff.STE.pdVec (m + 1) β F2 z := by
      have hA : iteratedFDerivWithin ℝ (m + 1) F2 v z (fun i => Pi.single (β i) 1)
          = pdVecX (m + 1) β F2 z := ((hA3 (m + 1) β le_rfl).symm) hzv
      rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := F2) (m + 1) hvopen hzv, hA,
        pdVecX_eq_pdVec]
    have hmain : ((iteratedFDeriv ℝ m (Work.Diff.STE.pdR c f) z
          (fun i => Pi.single (γ i) 1) : ℝ) : ℂ) = Work.Diff.STE.pdVec (m + 1) β F2 z := by
      rw [e1, e2, e3, e4, e5]
    have h1 := hpd (m + 1) (by omega) β
    rw [← hmain] at h1
    simpa using h1
  refine le_trans (norm_multilinear_le_of_basis (n := n) (N := m) (G := ℝ)
    (iteratedFDeriv ℝ m (Work.Diff.STE.pdR c f) z) hKd hbound) ?_
  apply mul_le_mul_of_nonneg_right _ hKd
  calc (n : ℝ) ^ m ≤ (max (n : ℝ) 1) ^ m :=
        pow_le_pow_left₀ (by positivity) (le_max_left _ _) m
    _ ≤ (max (n : ℝ) 1) ^ M := pow_le_pow_right₀ (le_max_right _ _) hm

end Work.Diff.STE.B3
