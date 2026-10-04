import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.frame_deps
import Submission.Work.Diff.GE.derivWithin_Ico_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The evolution estimate for `∇Rm` in a moving orthonormal frame (fixed-vector input)

`Work.Diff.GE.frame_evol_of_fixed` turns the **fixed-vector** evolution estimate for `∇Rm`
(hypothesis `hfix`: for fixed `v a b c d ∈ TₓM` the function `s ↦ covRm (G s) x v a b c d` is
differentiable at `t` with derivative bounded by `Δ∇Rm` plus `C₀|Rm||∇Rm| ‖v‖‖a‖‖b‖‖c‖‖d‖`) into
the estimate for the components of `∇Rm` in a **moving frame** `s ↦ e s` which is `G s`-orthonormal
near `t` and whose derivative `edot` is bounded by `K |Rm|²` (`|edot i|² ≤ K |Rm|²`).

The proof is a product rule.  Expanding the frame in the fixed `G t`-orthonormal frame `e t`
(`∑_k ⟪e t k, e s p⟫ • e t k = e s p`), the component becomes

`covRm (G s) x (e s m) … (e s l) = ∑_{r : Fin 5 → Fin n} (∏_p ⟪e t (r p), e s (ι p)⟫) * κ_r s`,

where `κ_r s = covRm (G s) x (e t (r 0)) … (e t (r 4))` is a *fixed-vector* component and
`s ↦ ⟪e t (r p), e s (ι p)⟫` is differentiable with derivative `⟪e t (r p), edot (ι p)⟫`.  The
product rule then gives a derivative whose `κ_r(t)`-part is bounded by `C (1+K) |Rm| |∇Rm|` (using
`|⟪e t k, edot (ι p)⟫| ≤ √⟨edot,edot⟩ ≤ √(K |Rm|²)` and the pointwise bound `hbound`), while the
`Dfun`-part collapses to the single fixed-vector derivative `Dfun ι` because the coefficients at `t`
are the Kronecker delta `⟪e t k, e t (ι p)⟫ = δ`.  Adding the two gives the stated constant.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Work.Diff.GE

/-- **Cauchy–Schwarz with respect to a Riemannian metric**, in the frame form used by the moving
frame estimate: for a `g`-orthonormal family `e` (not necessarily spanning), the pairing of `e i`
with any vector is bounded by the `g`-length `√(g(v,v))` of that vector. -/
private theorem frame_evol_inner_abs_le_sqrt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M) {m : ℕ} (e : Fin m → TangentSpace I x)
    (he : ∀ i j, g.inner x (e i) (e j) = if i = j then (1:ℝ) else 0)
    (i : Fin m) (v : TangentSpace I x) :
    |g.inner x (e i) v| ≤ Real.sqrt (g.inner x v v) := by
  open Bundle in
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have key : ∀ v z : TangentSpace I x, inner ℝ v z = g.inner x v z := fun v z => rfl
  have h1 : ‖e i‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, key (e i) (e i), he i i, if_pos rfl, Real.sqrt_one]
  have h2 : ‖v‖ = Real.sqrt (g.inner x v v) := by
    rw [norm_eq_sqrt_real_inner, key v v]
  calc |g.inner x (e i) v| = |inner ℝ (e i) v| := by rw [key]
    _ ≤ ‖e i‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ = Real.sqrt (g.inner x v v) := by rw [h1, one_mul, h2]

/-- The metric pairing with a fixed vector is differentiable along a curve (it is a continuous
linear functional), in the form needed for the coefficients of the frame expansion. -/
private theorem frame_evol_inner_const_hasDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x : M) (t : ℝ) (u : TangentSpace I x)
    {γ : ℝ → TangentSpace I x} {γ' : TangentSpace I x} {σ : Set ℝ}
    (h : HasDerivWithinAt γ γ' σ t) :
    HasDerivWithinAt (fun s => (G t).inner x u (γ s)) ((G t).inner x u γ') σ t := by
  open Bundle in
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  exact (ContinuousLinearMap.hasFDerivAt ((G t).inner x u)).comp_hasDerivWithinAt t h

/-- `∇Rm` as a genuine five-fold multilinear form: this is the `MultilinearMap` whose value on a
tuple `w` is `covRm g x (w 0) (w 1) (w 2) (w 3) (w 4)`.  Multilinearity is read off from the five
per-slot linearity lemmas `covRm_linear_fst`, `covRm_linear_snd`, `covRm_linear_thd`,
`covRm_linear_fth`, `Kato3.covRm_linear_fith`. -/
private noncomputable def frameEvolCovRm5M
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) :
    MultilinearMap ℝ (fun _ : Fin 5 => TangentSpace I x) ℝ :=
  MultilinearMap.mk' (fun w => Submission.Diff.covRm g x (w 0) (w 1) (w 2) (w 3) (w 4))
    (by
      intro m i a b
      fin_cases i <;>
        simp only [Function.update_apply, Fin.isValue] <;>
        first
          | simpa using covRm_linear_fst hLC g x 1 1 a b (m 1) (m 2) (m 3) (m 4)
          | simpa using covRm_linear_snd hLC g x (m 0) 1 1 a b (m 2) (m 3) (m 4)
          | simpa using covRm_linear_thd hLC g x (m 0) (m 1) 1 1 a b (m 3) (m 4)
          | simpa using covRm_linear_fth hLC g x (m 0) (m 1) (m 2) 1 1 a b (m 4)
          | simpa using Kato3.covRm_linear_fith hLC g x (m 0) (m 1) (m 2) (m 3) 1 1 a b)
    (by
      intro m i c a
      fin_cases i <;>
        simp only [Function.update_apply, Fin.isValue] <;>
        first
          | simpa using covRm_linear_fst hLC g x c 0 a 0 (m 1) (m 2) (m 3) (m 4)
          | simpa using covRm_linear_snd hLC g x (m 0) c 0 a 0 (m 2) (m 3) (m 4)
          | simpa using covRm_linear_thd hLC g x (m 0) (m 1) c 0 a 0 (m 3) (m 4)
          | simpa using covRm_linear_fth hLC g x (m 0) (m 1) (m 2) c 0 a 0 (m 4)
          | simpa using Kato3.covRm_linear_fith hLC g x (m 0) (m 1) (m 2) (m 3) c 0 a 0)

private lemma frameEvolCovRm5M_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (w : Fin 5 → TangentSpace I x) :
    frameEvolCovRm5M hLC g x w = Submission.Diff.covRm g x (w 0) (w 1) (w 2) (w 3) (w 4) := rfl

/-- **The frame expansion of `∇Rm`**: expanding the five arguments of the `(0,5)`-tensor `∇Rm` in a
family `a` of tangent vectors turns the value into the sum over all choices of one index per
argument of the product of the coefficients times the corresponding value of `∇Rm` on the
family.  (`multilinear expansion`, in the `∑_{r : Fin 5 → Fin n}` form needed by the product rule
for a moving frame.) -/
private theorem frameEvolCovRm_sum_expand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) {n : ℕ}
    (a : Fin n → TangentSpace I x) (c : Fin 5 → Fin n → ℝ) :
    Submission.Diff.covRm g x (∑ k, c 0 k • a k) (∑ k, c 1 k • a k) (∑ k, c 2 k • a k)
        (∑ k, c 3 k • a k) (∑ k, c 4 k • a k)
      = ∑ r : Fin 5 → Fin n, (∏ p : Fin 5, c p (r p)) *
          Submission.Diff.covRm g x (a (r 0)) (a (r 1)) (a (r 2)) (a (r 3)) (a (r 4)) := by
  have hsum := (frameEvolCovRm5M hLC g x).map_sum (g := fun p k => c p k • a k)
  rw [← frameEvolCovRm5M_apply hLC g x (fun i => ∑ j, c i j • a j)]
  rw [hsum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [MultilinearMap.map_smul_univ]
  simp only [frameEvolCovRm5M_apply, smul_eq_mul]

theorem frame_evol_of_fixed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hLV : Submission.Diff.LCVariation I M)
    (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hfix : ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
      Submission.Diff.IsRicciFlow G T →
      ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ v a b c d : TangentSpace I x, ∃ D : ℝ,
        HasDerivWithinAt (fun s ↦ Submission.Diff.covRm (G s) x v a b c d) D (Set.Ico 0 T) t ∧
        |D - Work.Diff.GE.lapCovRmAt (G t) x v a b c d|
          ≤ C0 * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
            * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
            * (Real.sqrt ((G t).inner x v v) * Real.sqrt ((G t).inner x a a)
               * Real.sqrt ((G t).inner x b b) * Real.sqrt ((G t).inner x c c)
               * Real.sqrt ((G t).inner x d d)))
    (hbound : ∀ (g : Submission.Diff.SMet I M) (x : M)
        (v a b c d : TangentSpace I x),
      |Submission.Diff.covRm g x v a b c d|
        ≤ Real.sqrt (Submission.Diff.dRmNormSq g x)
          * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
             * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
             * Real.sqrt (g.inner x d d))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : ℝ → Submission.Diff.SMet I M) (T : ℝ),
      Submission.Diff.IsRicciFlow G T → ∀ t ∈ Set.Ico 0 T, ∀ x : M,
      ∀ (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
        (edot : Fin (Module.finrank ℝ E) → TangentSpace I x) (K : ℝ), 0 ≤ K →
      (∀ᶠ s in nhdsWithin t (Set.Ico 0 T), Submission.Diff.IsONFrame (G s) x (e s)) →
      (∀ i, HasDerivWithinAt (fun s ↦ e s i) (edot i) (Set.Ico 0 T) t) →
      (∀ i, (G t).inner x (edot i) (edot i) ≤ K * Submission.Diff.rmNormSq (G t) x) →
      ∀ m i j k l : Fin (Module.finrank ℝ E), ∃ D : ℝ,
        HasDerivWithinAt
          (fun s ↦ Submission.Diff.covRm (G s) x (e s m) (e s i) (e s j) (e s k) (e s l)) D
          (Set.Ico 0 T) t ∧
        |D - Work.Diff.GE.lapCovRmAt (G t) x (e t m) (e t i) (e t j) (e t k) (e t l)|
          ≤ C * (1 + K) * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
              * Real.sqrt (Submission.Diff.dRmNormSq (G t) x) := by
  classical
  refine ⟨C0 + 5 * ((Module.finrank ℝ E : ℝ)) ^ 5, ?_, ?_⟩
  · positivity
  · intro G T hflow t ht x e edot K hK hON hder hKbd
    have hONt : Submission.Diff.IsONFrame (G t) x (e t) := hON.self_of_nhdsWithin ht
    rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hn0 | hn
    · intro m
      exact Fin.elim0 (hn0 ▸ m)
    · intro m i j k l
      -- the tuple `(m,i,j,k,l)` of frame indices, as a function `Fin 5 → Fin (finrank ℝ E)`
      let ι : Fin 5 → Fin (Module.finrank ℝ E) := ![m, i, j, k, l]
      have hFder : ∀ p : Fin 5, HasDerivWithinAt (fun s : ℝ => e s (ι p)) (edot (ι p)) (Set.Ico 0 T) t := by
        intro p
        fin_cases p <;>
          simp only [ι, Matrix.cons_val_zero, Matrix.cons_val, Nat.succ_eq_add_one,
            Nat.reduceAdd, Fin.isValue] <;>
          (first | exact hder m | exact hder i | exact hder j | exact hder k | exact hder l)
      -- expansion of the moving frame in the fixed `G t`-orthonormal frame at every time `s`
      have hexpand : ∀ s : ℝ,
          Submission.Diff.covRm (G s) x (e s (ι 0)) (e s (ι 1)) (e s (ι 2)) (e s (ι 3)) (e s (ι 4))
            = ∑ r : Fin 5 → Fin (Module.finrank ℝ E),
                (∏ p : Fin 5, (G t).inner x (e t (r p)) (e s (ι p)))
                  * Submission.Diff.covRm (G s) x (e t (r 0)) (e t (r 1)) (e t (r 2)) (e t (r 3)) (e t (r 4)) := by
        intro s
        let c : Fin 5 → Fin (Module.finrank ℝ E) → ℝ := fun p k => (G t).inner x (e t k) (e s (ι p))
        have hcp : ∀ p : Fin 5, (∑ k, c p k • e t k) = e s (ι p) :=
          fun p => sum_inner_smul_eq_self (G t) x hn (e t) hONt (e s (ι p))
        have h := frameEvolCovRm_sum_expand (hLC := hLC) (g := G s) (x := x) (a := fun k => e t k) (c := c)
        rw [hcp 0, hcp 1, hcp 2, hcp 3, hcp 4] at h
        simpa only [c] using h
      -- the fixed-vector derivatives at the tuples `(e t (r 0), …, e t (r 4))`, from `hfix`
      choose Dfun hDfun hDbd using fun r : Fin 5 → Fin (Module.finrank ℝ E) =>
        hfix G T hflow t ht x (e t (r 0)) (e t (r 1)) (e t (r 2)) (e t (r 3)) (e t (r 4))
      -- the two parts of the derivative: frame-motion (`A`) and fixed-vector (`B`)
      let A : (Fin 5 → Fin (Module.finrank ℝ E)) → ℝ := fun r =>
        (∑ p ∈ Finset.univ, (∏ q ∈ Finset.univ.erase p, (G t).inner x (e t (r q)) (e t (ι q)))
            * (G t).inner x (e t (r p)) (edot (ι p)))
          * Submission.Diff.covRm (G t) x (e t (r 0)) (e t (r 1)) (e t (r 2)) (e t (r 3)) (e t (r 4))
      let B : (Fin 5 → Fin (Module.finrank ℝ E)) → ℝ := fun r =>
        (∏ p : Fin 5, (G t).inner x (e t (r p)) (e t (ι p))) * Dfun r
      have hder : HasDerivWithinAt
          (fun s : ℝ => Submission.Diff.covRm (G s) x (e s (ι 0)) (e s (ι 1)) (e s (ι 2)) (e s (ι 3)) (e s (ι 4)))
          (∑ r : Fin 5 → Fin (Module.finrank ℝ E), (A r + B r)) (Set.Ico 0 T) t := by
        rw [show (fun s : ℝ => Submission.Diff.covRm (G s) x (e s (ι 0)) (e s (ι 1)) (e s (ι 2)) (e s (ι 3)) (e s (ι 4)))
            = ∑ r ∈ (Finset.univ : Finset (Fin 5 → Fin (Module.finrank ℝ E))),
                (fun s : ℝ => (∏ p : Fin 5, (G t).inner x (e t (r p)) (e s (ι p)))
                  * Submission.Diff.covRm (G s) x (e t (r 0)) (e t (r 1)) (e t (r 2)) (e t (r 3)) (e t (r 4))) from by
          funext s
          simp only [Finset.sum_apply]
          exact (hexpand s).symm ▸ rfl]
        refine HasDerivWithinAt.sum (u := Finset.univ) (fun r _ => ?_)
        have hcder : ∀ p : Fin 5, HasDerivWithinAt (fun s : ℝ => (G t).inner x (e t (r p)) (e s (ι p)))
            ((G t).inner x (e t (r p)) (edot (ι p))) (Set.Ico 0 T) t := by
          intro p
          exact frame_evol_inner_const_hasDerivWithinAt G x t (e t (r p)) (hFder p)
        refine HasDerivWithinAt.mul ?_ ?_
        · refine HasDerivWithinAt.fun_finsetProd (u := Finset.univ)
            (f := fun p => fun s : ℝ => (G t).inner x (e t (r p)) (e s (ι p)))
            (f' := fun p => (G t).inner x (e t (r p)) (edot (ι p))) ?_
          intro p _
          exact hcder p
        · exact hDfun r
      -- at time `t` the coefficients are the Kronecker delta
      have hdiag : ∀ k : Fin (Module.finrank ℝ E), (G t).inner x (e t k) (e t k) = 1 :=
        fun k => by rw [hONt k k]; simp
      have hιprod : (∏ p : Fin 5, (G t).inner x (e t (ι p)) (e t (ι p))) = 1 :=
        Finset.prod_eq_one (fun p _ => hdiag (ι p))
      have hBsum : (∑ r : Fin 5 → Fin (Module.finrank ℝ E), B r) = Dfun ι := by
        simp only [B]
        rw [show Dfun ι = (∏ p : Fin 5, (G t).inner x (e t (ι p)) (e t (ι p))) * Dfun ι from by
          rw [hιprod, one_mul]]
        refine Fintype.sum_eq_single ι ?_
        intro r hr
        obtain ⟨p, hp⟩ := Function.ne_iff.mp hr
        have hzero : (G t).inner x (e t (r p)) (e t (ι p)) = 0 := by
          rw [hONt (r p) (ι p)]; simp [hp]
        rw [Finset.prod_eq_zero (Finset.mem_univ p) hzero, zero_mul]
      have hderot : (∑ r : Fin 5 → Fin (Module.finrank ℝ E), (A r + B r))
          = (∑ r : Fin 5 → Fin (Module.finrank ℝ E), A r) + Dfun ι := by
        rw [Finset.sum_add_distrib, hBsum]
      -- bounds on the pieces
      have hone : ∀ k q : Fin (Module.finrank ℝ E), |(G t).inner x (e t k) (e t q)| ≤ 1 := by
        intro k q
        rw [hONt k q]
        split_ifs <;> norm_num
      have hedotbd : ∀ (k : Fin (Module.finrank ℝ E)) (p : Fin 5),
          |(G t).inner x (e t k) (edot (ι p))| ≤ Real.sqrt (K * Submission.Diff.rmNormSq (G t) x) := by
        intro k p
        refine le_trans (frame_evol_inner_abs_le_sqrt (g := G t) (x := x) (e := e t) hONt k (edot (ι p))) ?_
        exact Real.sqrt_le_sqrt (hKbd (ι p))
      have hcovbd : ∀ r : Fin 5 → Fin (Module.finrank ℝ E),
          |Submission.Diff.covRm (G t) x (e t (r 0)) (e t (r 1)) (e t (r 2)) (e t (r 3)) (e t (r 4))|
            ≤ Real.sqrt (Submission.Diff.dRmNormSq (G t) x) := by
        intro r
        have hb := hbound (G t) x (e t (r 0)) (e t (r 1)) (e t (r 2)) (e t (r 3)) (e t (r 4))
        simp only [hdiag, Real.sqrt_one, mul_one] at hb
        exact hb
      have hprodbd : ∀ (r : Fin 5 → Fin (Module.finrank ℝ E)) (p : Fin 5),
          |∏ q ∈ Finset.univ.erase p, (G t).inner x (e t (r q)) (e t (ι q))| ≤ 1 := by
        intro r p
        rw [Finset.abs_prod]
        exact Finset.prod_le_one₀ (fun q _ => abs_nonneg _) (fun q _ => hone (r q) (ι q))
      have hterm : ∀ r : Fin 5 → Fin (Module.finrank ℝ E),
          |(∑ p ∈ Finset.univ, (∏ q ∈ Finset.univ.erase p, (G t).inner x (e t (r q)) (e t (ι q)))
              * (G t).inner x (e t (r p)) (edot (ι p)))
              * Submission.Diff.covRm (G t) x (e t (r 0)) (e t (r 1)) (e t (r 2)) (e t (r 3)) (e t (r 4))|
            ≤ 5 * (Real.sqrt (K * Submission.Diff.rmNormSq (G t) x)
                * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)) := by
        intro r
        have hsum : |∑ p ∈ Finset.univ, (∏ q ∈ Finset.univ.erase p, (G t).inner x (e t (r q)) (e t (ι q)))
              * (G t).inner x (e t (r p)) (edot (ι p))|
            ≤ 5 * Real.sqrt (K * Submission.Diff.rmNormSq (G t) x) := by
          calc |∑ p ∈ Finset.univ, (∏ q ∈ Finset.univ.erase p, (G t).inner x (e t (r q)) (e t (ι q)))
                * (G t).inner x (e t (r p)) (edot (ι p))|
              ≤ ∑ p ∈ Finset.univ, |(∏ q ∈ Finset.univ.erase p, (G t).inner x (e t (r q)) (e t (ι q)))
                * (G t).inner x (e t (r p)) (edot (ι p))| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ p ∈ Finset.univ, (1 * Real.sqrt (K * Submission.Diff.rmNormSq (G t) x)) := by
                refine Finset.sum_le_sum (fun p _ => ?_)
                rw [abs_mul]
                exact mul_le_mul (hprodbd r p) (hedotbd (r p) p) (abs_nonneg _) zero_le_one
            _ = 5 * Real.sqrt (K * Submission.Diff.rmNormSq (G t) x) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                norm_num
        calc |(∑ p ∈ Finset.univ, (∏ q ∈ Finset.univ.erase p, (G t).inner x (e t (r q)) (e t (ι q)))
              * (G t).inner x (e t (r p)) (edot (ι p)))
              * Submission.Diff.covRm (G t) x (e t (r 0)) (e t (r 1)) (e t (r 2)) (e t (r 3)) (e t (r 4))|
            = |∑ p ∈ Finset.univ, (∏ q ∈ Finset.univ.erase p, (G t).inner x (e t (r q)) (e t (ι q)))
                * (G t).inner x (e t (r p)) (edot (ι p))|
              * |Submission.Diff.covRm (G t) x (e t (r 0)) (e t (r 1)) (e t (r 2)) (e t (r 3)) (e t (r 4))| := abs_mul _ _
          _ ≤ (5 * Real.sqrt (K * Submission.Diff.rmNormSq (G t) x))
              * Real.sqrt (Submission.Diff.dRmNormSq (G t) x) :=
                mul_le_mul hsum (hcovbd r) (abs_nonneg _) (by positivity)
          _ = 5 * (Real.sqrt (K * Submission.Diff.rmNormSq (G t) x)
              * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)) := by ring
      have hfm : |∑ r : Fin 5 → Fin (Module.finrank ℝ E), A r|
          ≤ ((Module.finrank ℝ E : ℝ)) ^ 5 * (5 * (Real.sqrt (K * Submission.Diff.rmNormSq (G t) x)
              * Real.sqrt (Submission.Diff.dRmNormSq (G t) x))) := by
        have hA : (∑ r : Fin 5 → Fin (Module.finrank ℝ E), A r)
            = ∑ r : Fin 5 → Fin (Module.finrank ℝ E),
              (∑ p ∈ Finset.univ, (∏ q ∈ Finset.univ.erase p, (G t).inner x (e t (r q)) (e t (ι q)))
                * (G t).inner x (e t (r p)) (edot (ι p)))
              * Submission.Diff.covRm (G t) x (e t (r 0)) (e t (r 1)) (e t (r 2)) (e t (r 3)) (e t (r 4)) := by
          simp only [A]
        rw [hA]
        calc |∑ r : Fin 5 → Fin (Module.finrank ℝ E),
              (∑ p ∈ Finset.univ, (∏ q ∈ Finset.univ.erase p, (G t).inner x (e t (r q)) (e t (ι q)))
                * (G t).inner x (e t (r p)) (edot (ι p)))
              * Submission.Diff.covRm (G t) x (e t (r 0)) (e t (r 1)) (e t (r 2)) (e t (r 3)) (e t (r 4))|
            ≤ ∑ r : Fin 5 → Fin (Module.finrank ℝ E),
                |(∑ p ∈ Finset.univ, (∏ q ∈ Finset.univ.erase p, (G t).inner x (e t (r q)) (e t (ι q)))
                  * (G t).inner x (e t (r p)) (edot (ι p)))
                  * Submission.Diff.covRm (G t) x (e t (r 0)) (e t (r 1)) (e t (r 2)) (e t (r 3)) (e t (r 4))| :=
                Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ r : Fin 5 → Fin (Module.finrank ℝ E),
                (5 * (Real.sqrt (K * Submission.Diff.rmNormSq (G t) x)
                  * Real.sqrt (Submission.Diff.dRmNormSq (G t) x))) := Finset.sum_le_sum (fun r _ => hterm r)
          _ = (Fintype.card (Fin 5 → Fin (Module.finrank ℝ E)) : ℝ)
                * (5 * (Real.sqrt (K * Submission.Diff.rmNormSq (G t) x)
                  * Real.sqrt (Submission.Diff.dRmNormSq (G t) x))) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ = ((Module.finrank ℝ E : ℝ)) ^ 5 * (5 * (Real.sqrt (K * Submission.Diff.rmNormSq (G t) x)
                  * Real.sqrt (Submission.Diff.dRmNormSq (G t) x))) := by
                rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
      have hb1 : |Dfun ι - Work.Diff.GE.lapCovRmAt (G t) x (e t (ι 0)) (e t (ι 1)) (e t (ι 2)) (e t (ι 3)) (e t (ι 4))|
          ≤ C0 * Real.sqrt (Submission.Diff.rmNormSq (G t) x) * Real.sqrt (Submission.Diff.dRmNormSq (G t) x) := by
        have h := hDbd ι
        simp only [hdiag, Real.sqrt_one, mul_one, one_mul] at h
        exact h
      -- assemble: prove the statement in the `ι`-form and rewrite `ι` back to `(m,i,j,k,l)`
      suffices h : ∃ D : ℝ,
          HasDerivWithinAt (fun s : ℝ => Submission.Diff.covRm (G s) x (e s (ι 0)) (e s (ι 1)) (e s (ι 2)) (e s (ι 3)) (e s (ι 4))) D (Set.Ico 0 T) t ∧
          |D - Work.Diff.GE.lapCovRmAt (G t) x (e t (ι 0)) (e t (ι 1)) (e t (ι 2)) (e t (ι 3)) (e t (ι 4))|
            ≤ (C0 + 5 * ((Module.finrank ℝ E : ℝ)) ^ 5) * (1 + K)
              * Real.sqrt (Submission.Diff.rmNormSq (G t) x) * Real.sqrt (Submission.Diff.dRmNormSq (G t) x) by
        simpa only [ι, Matrix.cons_val_zero, Matrix.cons_val, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue] using h
      refine ⟨Dfun ι + ∑ r : Fin 5 → Fin (Module.finrank ℝ E), A r, ?_, ?_⟩
      · refine hder.congr_deriv ?_
        rw [hderot, add_comm]
      · have hrm0 : 0 ≤ Real.sqrt (Submission.Diff.rmNormSq (G t) x) := Real.sqrt_nonneg _
        have hdm0 : 0 ≤ Real.sqrt (Submission.Diff.dRmNormSq (G t) x) := Real.sqrt_nonneg _
        have hsqrtK : Real.sqrt K ≤ 1 + K := by
          rw [Real.sqrt_le_iff]
          exact ⟨by linarith, by nlinarith [hK, sq_nonneg K]⟩
        have hn5 : (0:ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 5 := by positivity
        have hcore : C0 + 5 * ((Module.finrank ℝ E : ℝ) ^ 5) * Real.sqrt K
            ≤ (C0 + 5 * ((Module.finrank ℝ E : ℝ) ^ 5)) * (1 + K) := by
          nlinarith [hsqrtK, hC0, hK, hn5]
        have hlast : C0 * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
              * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
            + ((Module.finrank ℝ E : ℝ)) ^ 5 * (5 * (Real.sqrt (K * Submission.Diff.rmNormSq (G t) x)
              * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)))
            ≤ (C0 + 5 * ((Module.finrank ℝ E : ℝ)) ^ 5) * (1 + K)
              * Real.sqrt (Submission.Diff.rmNormSq (G t) x) * Real.sqrt (Submission.Diff.dRmNormSq (G t) x) := by
          rw [Real.sqrt_mul hK (Submission.Diff.rmNormSq (G t) x)]
          calc C0 * Real.sqrt (Submission.Diff.rmNormSq (G t) x) * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
                + ((Module.finrank ℝ E : ℝ)) ^ 5 * (5 * (Real.sqrt K * Real.sqrt (Submission.Diff.rmNormSq (G t) x)
                  * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)))
              = (C0 + 5 * ((Module.finrank ℝ E : ℝ) ^ 5) * Real.sqrt K)
                  * (Real.sqrt (Submission.Diff.rmNormSq (G t) x) * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)) := by ring
            _ ≤ ((C0 + 5 * ((Module.finrank ℝ E : ℝ) ^ 5)) * (1 + K))
                  * (Real.sqrt (Submission.Diff.rmNormSq (G t) x) * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)) :=
                mul_le_mul_of_nonneg_right hcore (mul_nonneg hrm0 hdm0)
            _ = (C0 + 5 * ((Module.finrank ℝ E : ℝ)) ^ 5) * (1 + K)
                  * Real.sqrt (Submission.Diff.rmNormSq (G t) x) * Real.sqrt (Submission.Diff.dRmNormSq (G t) x) := by ring
        calc |(Dfun ι + ∑ r : Fin 5 → Fin (Module.finrank ℝ E), A r)
              - Work.Diff.GE.lapCovRmAt (G t) x (e t (ι 0)) (e t (ι 1)) (e t (ι 2)) (e t (ι 3)) (e t (ι 4))|
            = |(Dfun ι - Work.Diff.GE.lapCovRmAt (G t) x (e t (ι 0)) (e t (ι 1)) (e t (ι 2)) (e t (ι 3)) (e t (ι 4)))
                + ∑ r : Fin 5 → Fin (Module.finrank ℝ E), A r| := by
                rw [show (Dfun ι + ∑ r : Fin 5 → Fin (Module.finrank ℝ E), A r)
                    - Work.Diff.GE.lapCovRmAt (G t) x (e t (ι 0)) (e t (ι 1)) (e t (ι 2)) (e t (ι 3)) (e t (ι 4))
                    = (Dfun ι - Work.Diff.GE.lapCovRmAt (G t) x (e t (ι 0)) (e t (ι 1)) (e t (ι 2)) (e t (ι 3)) (e t (ι 4)))
                      + ∑ r : Fin 5 → Fin (Module.finrank ℝ E), A r by ring]
          _ ≤ |Dfun ι - Work.Diff.GE.lapCovRmAt (G t) x (e t (ι 0)) (e t (ι 1)) (e t (ι 2)) (e t (ι 3)) (e t (ι 4))|
                + |∑ r : Fin 5 → Fin (Module.finrank ℝ E), A r| := abs_add_le _ _
          _ ≤ C0 * Real.sqrt (Submission.Diff.rmNormSq (G t) x) * Real.sqrt (Submission.Diff.dRmNormSq (G t) x)
                + ((Module.finrank ℝ E : ℝ)) ^ 5 * (5 * (Real.sqrt (K * Submission.Diff.rmNormSq (G t) x)
                  * Real.sqrt (Submission.Diff.dRmNormSq (G t) x))) := add_le_add hb1 hfm
          _ ≤ (C0 + 5 * ((Module.finrank ℝ E : ℝ)) ^ 5) * (1 + K)
                * Real.sqrt (Submission.Diff.rmNormSq (G t) x) * Real.sqrt (Submission.Diff.dRmNormSq (G t) x) := hlast

end Work.Diff.GE
