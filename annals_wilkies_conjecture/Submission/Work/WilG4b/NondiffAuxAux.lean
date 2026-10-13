/-
  Area G4b, own copy of the auxiliary vocabulary needed for the finiteness of the non-`C¹`
  locus of a definable function of one variable.

  Everything here is proved (on the basis of `S.SharpDeriv`, `S.hyp` and the elementary
  `Ω`-operations); the file is a re-statement, in namespace `Work.WilG4bF`, of the material
  of `Submission/Work/WilG4b/nondiff_finite.lean` (which cannot be imported together with
  `Submission/Work/WilG4b/badSet_mem.lean`: both declare `Work.WilG4b.derivGraph_mem`).

  * `fin1`, `pt1`, `contDiffAt_fin1_iff` : the `ℝ¹`-model of a one-variable function;
  * `badMem` : the non-`C¹` locus is `Ω`-definable (uses `SharpDeriv`);
  * `isDeriv`, `DRset` and bridges : the `ε`-`δ` derivative relation;
  * `derivGraph_mem` : the graph of `deriv G` is `Ω`-definable when the derivative relation
    is.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4b.thrSet_mem

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Classical

namespace Work.WilG4bF

open WilkiesDesign

/-- `G` read as a function on `ℝ¹ = Fin 1 → ℝ`. -/
abbrev fin1 (G : ℝ → ℝ) : (Fin 1 → ℝ) → ℝ := fun x => G (x 0)

/-- The point `t` of `ℝ¹`. -/
abbrev pt1 (t : ℝ) : Fin 1 → ℝ := fun _ => t

/-- `ContDiffAt` of `G` at `t` is `ContDiffAt` of its `ℝ¹`-model at the point `t`. -/
lemma contDiffAt_fin1_iff {G : ℝ → ℝ} {t : ℝ} :
    ContDiffAt ℝ 1 G t ↔ ContDiffAt ℝ 1 (fin1 G) (pt1 t) := by
  constructor
  · intro h
    have hproj : ContDiffAt ℝ 1 (fun x : Fin 1 → ℝ => x 0) (pt1 t) :=
      ((ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt)
    have h' : ContDiffAt ℝ 1 G ((fun x : Fin 1 → ℝ => x 0) (pt1 t)) := h
    have hcomp := ContDiffAt.comp (pt1 t) h' hproj
    simpa [fin1, pt1, Function.comp_def] using hcomp
  · intro h
    have hphi : ContDiffAt ℝ 1 (fun s : ℝ => pt1 s) t :=
      contDiffAt_pi' (fun _ => contDiffAt_id)
    have hcomp := ContDiffAt.comp t h hphi
    simpa [fin1, pt1, Function.comp_def] using hcomp

/-! ## The non-`C¹` locus is `Ω`-definable -/

theorem badMem (S : SOMin) (hder : S.SharpDeriv) {F D : ℕ} (G : ℝ → ℝ)
    (hG : graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∈ S.Ω F D 2) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      {z : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 (fin1 G) z} ∈ S.Ω a (b.eval D) 1 := by
  obtain ⟨a, b, hb⟩ := hder F 1
  have hsd : {z : Fin 2 → ℝ |
      Fin.init z ∈ interior {x : Fin 1 → ℝ | ContDiffAt ℝ 1 (fin1 G) x} ∧
      z (Fin.last 1) = iteratedFDeriv ℝ 1 (fin1 G) (Fin.init z)
        (fun _ : Fin 1 => Pi.single (0 : Fin 1) 1)}
      ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) 2 :=
    hb D (fin1 G) (by simpa [fin1] using hG) 1 (fun _ : Fin 1 => (0 : Fin 1))
  have hproj : projLast {z : Fin 2 → ℝ |
      Fin.init z ∈ interior {x : Fin 1 → ℝ | ContDiffAt ℝ 1 (fin1 G) x} ∧
      z (Fin.last 1) = iteratedFDeriv ℝ 1 (fin1 G) (Fin.init z)
        (fun _ : Fin 1 => Pi.single (0 : Fin 1) 1)}
      = interior {x : Fin 1 → ℝ | ContDiffAt ℝ 1 (fin1 G) x} := by
    ext x
    constructor
    · rintro ⟨t, ht⟩
      simp only [Set.mem_ofPred_eq] at ht
      rw [Fin.init_snoc] at ht
      exact ht.1
    · intro hx
      simp only [projLast, Set.mem_ofPred_eq]
      set M : ℝ := iteratedFDeriv ℝ 1 (fin1 G) x (fun _ : Fin 1 => Pi.single (0 : Fin 1) 1)
        with hM
      refine ⟨M, ?_⟩
      have hgoal : (Fin.init (Fin.snoc x M : Fin 2 → ℝ) ∈
            interior {x : Fin 1 → ℝ | ContDiffAt ℝ 1 (fin1 G) x}) ∧
          (Fin.snoc x M : Fin 2 → ℝ) (Fin.last 1)
            = iteratedFDeriv ℝ 1 (fin1 G) (Fin.init (Fin.snoc x M : Fin 2 → ℝ))
              (fun _ : Fin 1 => Pi.single (0 : Fin 1) 1) := by
        rw [Fin.init_snoc, Fin.snoc_last]
        exact ⟨hx, rfl⟩
      exact hgoal
  have h1 : interior {x : Fin 1 → ℝ | ContDiffAt ℝ 1 (fin1 G) x}
      ∈ S.Ω (a + 1) (MvPolynomial.eval ![D, 1] b) 1 := by
    have h := S.proj hsd
    rw [hproj] at h
    exact h
  have hset : {z : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 (fin1 G) z}
      = (interior {x : Fin 1 → ℝ | ContDiffAt ℝ 1 (Work.WilG4b.thrDinG G) x})ᶜ := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
    rw [Work.WilG4b.thrMem_interior_c1]
    exact not_congr (Work.WilG4b.thrContDiffAt_dinG_iff G z)
  refine ⟨a + 2, Work.WilG1.psubst b 1, ?_⟩
  rw [Work.WilG1.eval_psubst, hset]
  exact Work.WilG1.Omega.mono (S.compl h1) (by omega) le_rfl

/-! ## The derivative relation and its bridges -/

/-- The `ε`-`δ` formulation of "`L` is the derivative of `G` at `x`". -/
def isDeriv (G : ℝ → ℝ) (x L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, 0 < |y - x| → |y - x| < δ →
    |(G y - G x) / (y - x) - L| ≤ ε

/-- The derivative relation, as a subset of `ℝ²`. -/
def DRset (G : ℝ → ℝ) : Set (Fin 2 → ℝ) := {z | isDeriv G (z 0) (z 1)}

lemma isDeriv_iff_hasDerivAt {G : ℝ → ℝ} {x L : ℝ} :
    isDeriv G x L ↔ HasDerivAt G L x := by
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h (ε / 2) (half_pos hε)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨δ, hδ, fun y hy hyne => ?_⟩
    have hyne' : y ≠ x := by simpa using hyne
    rw [Real.dist_eq] at hy
    have h0 : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr hyne')
    have hle := hδ' y h0 hy
    rw [slope_def_field, Real.dist_eq]
    exact lt_of_le_of_lt hle (by linarith)
  · intro h ε hε
    have hh := h ε hε
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hh
    obtain ⟨δ, hδ, hδ'⟩ := hh
    refine ⟨δ, hδ, fun y hy hylt => ?_⟩
    have hyne : y ≠ x := sub_ne_zero.mp (abs_pos.mp hy)
    have hdist : dist y x < δ := by rw [Real.dist_eq]; exact hylt
    have hd : dist (slope G x y) L < ε := hδ' hdist (by simpa using hyne)
    rw [slope_def_field, Real.dist_eq] at hd
    exact le_of_lt hd

lemma mem_projLast_DRset_iff {G : ℝ → ℝ} {x : Fin 1 → ℝ} :
    x ∈ projLast (DRset G) ↔ DifferentiableAt ℝ G (x 0) := by
  constructor
  · rintro ⟨L, hL⟩
    rw [DRset, Set.mem_ofPred_eq] at hL
    have h0 : (Fin.snoc x L : Fin 2 → ℝ) 0 = x 0 := by
      rw [show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from rfl, Fin.snoc_castSucc]
    have h1 : (Fin.snoc x L : Fin 2 → ℝ) 1 = L := by
      rw [show (1 : Fin 2) = Fin.last 1 from rfl, Fin.snoc_last]
    rw [h0, h1] at hL
    exact (isDeriv_iff_hasDerivAt.mp hL).differentiableAt
  · intro h
    refine ⟨deriv G (x 0), ?_⟩
    rw [DRset, Set.mem_ofPred_eq]
    have h0 : (Fin.snoc x (deriv G (x 0)) : Fin 2 → ℝ) 0 = x 0 := by
      rw [show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from rfl, Fin.snoc_castSucc]
    have h1 : (Fin.snoc x (deriv G (x 0)) : Fin 2 → ℝ) 1 = deriv G (x 0) := by
      rw [show (1 : Fin 2) = Fin.last 1 from rfl, Fin.snoc_last]
    rw [h0, h1]
    exact isDeriv_iff_hasDerivAt.mpr h.hasDerivAt

/-- The graph of `deriv G` is `Ω`-definable whenever the derivative relation is. -/
lemma derivGraph_mem (S : SOMin) {G : ℝ → ℝ} {a D : ℕ} {b : Polynomial ℕ}
    (hDR : DRset G ∈ S.Ω a (b.eval D) 2) :
    ∃ (K : ℕ) (p : Polynomial ℕ),
      graphOf (fun x : Fin 1 → ℝ => deriv G (x 0)) ∈ S.Ω (a + K) (p.eval D) 2 := by
  have hproj : projLast (DRset G) ∈ S.Ω (a + 1) (b.eval D) 1 := S.proj hDR
  have hcompl : (projLast (DRset G))ᶜ ∈ S.Ω (a + 2) (b.eval D) 1 := S.compl hproj
  have hlift : {z : Fin 2 → ℝ | Fin.init z ∈ (projLast (DRset G))ᶜ}
      ∈ S.Ω (max (a + 3) 2) (b.eval D) 2 :=
    Work.WilG1.Omega.mono (S.prod_right hcompl) (le_max_left _ _) le_rfl
  have hzero : {z : Fin 2 → ℝ | z 1 = 0}
      ∈ S.Ω (max (a + 3) 2) ((b + Polynomial.C 1).eval D) 2 := by
    have h := S.hyp 2 (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ)
    have hset : {z : Fin 2 → ℝ |
        MvPolynomial.eval z (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ) = 0}
        = {z : Fin 2 → ℝ | z 1 = 0} := by
      ext z; simp
    rw [hset] at h
    refine Work.WilG1.Omega.mono h (le_max_right _ _) ?_
    have hc : (Polynomial.C 1).eval D ≤ (b + Polynomial.C 1).eval D := by simp
    simpa using hc
  have hz := Work.WilG1.Omega.inter₂ (a₁ := max (a + 3) 2) (a₂ := max (a + 3) 2)
    (b₁ := b) (b₂ := b + Polynomial.C 1) hlift hzero
  have hset : graphOf (fun x : Fin 1 → ℝ => deriv G (x 0))
      = DRset G ∪ {z : Fin 2 → ℝ | Fin.init z ∈ (projLast (DRset G))ᶜ ∧ z 1 = 0} := by
    ext z
    constructor
    · intro hzin
      have hz1 : z 1 = deriv G (z 0) := hzin
      by_cases hd : DifferentiableAt ℝ G (z 0)
      · left
        rw [DRset, Set.mem_ofPred_eq]
        rw [hz1]
        exact isDeriv_iff_hasDerivAt.mpr hd.hasDerivAt
      · right
        refine ⟨?_, ?_⟩
        · intro hmem
          exact hd ((mem_projLast_DRset_iff (G := G)).mp hmem)
        · rw [hz1, deriv_zero_of_not_differentiableAt hd]
    · rintro (h | ⟨h1, h2⟩)
      · rw [DRset, Set.mem_ofPred_eq] at h
        show z 1 = deriv G (z 0)
        rw [← (isDeriv_iff_hasDerivAt.mp h).deriv]
      · show z 1 = deriv G (z 0)
        rw [h2, deriv_zero_of_not_differentiableAt]
        intro hd
        exact h1 ((mem_projLast_DRset_iff (G := G)).mpr hd)
  have hmono : DRset G ∈ S.Ω (max (a + 3) 2) (b.eval D) 2 :=
    Work.WilG1.Omega.mono hDR (by omega) le_rfl
  have hunion := Work.WilG1.Omega.union₂ (b₁ := b) (b₂ := b + (b + Polynomial.C 1)) hmono hz
  rw [hset]
  refine ⟨4 * (a + 3) + 8,
    Polynomial.C 2 * (b + (b + Polynomial.C 1)) + Polynomial.C 2, ?_⟩
  refine Work.WilG1.Omega.mono hunion (by omega) ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  omega

end Work.WilG4bF
