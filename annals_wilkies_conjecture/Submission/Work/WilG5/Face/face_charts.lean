/-
  WilG5 / Face — the *boundary* half of the algebraic lemma (`AlgLemma S F n`).

  The algebraic lemma splits its covering task into the interior of the cube
  (`Work.WilG5.Interior.interior_charts`) and its boundary, which is the content of the theorem
  below: for `X ⊆ [0,1]ⁿ` an `Ω`-set of `DimLE`-dimension `μ`, the part `X \ (0,1)ⁿ` of `X` on
  the boundary of the cube is `ε`-covered by charts `Fin μ → Fin n` that are `C^r` with all
  iterated derivative norms `≤ 1`, the number of charts being bounded by a polynomial in
  `D`, `r`, `-log ε` with nonnegative coefficients.

  Proof (induction on the ambient dimension, exactly BNZ Lemma 3's boundary case).  A point of
  `X` outside the open cube has some coordinate `x i` equal to `0` or `1`; cutting `X` by the
  hyperplane `{x i = c}` and forgetting the coordinate `i` gives the *face*
  `faceProj i c X ⊆ ℝ^{n-1}` (`Work.WilG5.Face.Defs`).  There are `2n` faces, they cover the
  boundary of `X`, each face is again an `Ω`-set (with a format and a degree which are
  *constants in the data*: format `ffs F n`, degree `D + dfs n`, `face_proj_mem`), has
  `DimLE`-dimension `min μ (n-1) ≤ n-1` (`face_dimle`), and lies in `[0,1]^{n-1}`.  So the
  induction hypothesis `hIH` applies to each face and produces a family of charts of `ℝ^{n-1}`.
  Each of those charts is pushed back into `ℝⁿ` by inserting the coordinate `i` (`face_insert`),
  and its source dimension is raised from `min μ (n-1)` to `μ` by precomposing with the
  coordinate projection `projCoord` (`proj_charts`).  The `2n` families are collected into one
  `Finset`; its cardinality is at most `2n` times the single face bound, and the shift
  `D ↦ D + dfs n` together with the factor `2n` is absorbed into a polynomial with nonnegative
  coefficients by `face_count_poly`.

  The parametrisation of a chart of `ℝ^{n-1}` back into `ℝⁿ` is supplied by
  `Work.WilG5.Face.Defs`: `insCoord i c` inserts the coordinate, `insCoord_mem_faceProj` is the
  round trip `insCoord i c y ∈ X ↔ y ∈ faceProj i c X`, and `projCoord`/`extHalf` show that a
  point of `openCube μ` may be chosen over any prescribed point of `openCube (min μ (n-1))`.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG5.Defs
import Submission.Work.WilG5.Face.Defs
import Submission.Work.WilG5.Face.face_proj_mem
import Submission.Work.WilG5.Face.face_dimle
import Submission.Work.WilG5.Face.face_count_poly
import Submission.Work.WilG5.Face.proj_charts
import Submission.Work.WilG5.Face.face_insert

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG5.Face

open WilkiesDesign WilkiesConjecture Work.WilG5

/-- Inserting a coordinate is a `1`-Lipschitz operation: the distance of two tuples is not
increased by replacing the `i`-th coordinate of both by the same value `c`.  (Equivalently:
`insCoord i c` is the isometry `insCLM i` followed by a translation.) -/
theorem dist_insCoord_le {n : ℕ} (i : Fin n) (c : ℝ) (u v : Fin (n - 1) → ℝ) :
    dist (insCoord i c u) (insCoord i c v) ≤ dist u v := by
  have hsub : insCoord i c u - insCoord i c v = insCLM i (u - v) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [insCoord]
    · rw [Pi.sub_apply, insCoord_of_ne i j c u hj, insCoord_of_ne i j c v hj,
        insCLM_apply, insCoord_of_ne i j 0 (u - v) hj, Pi.sub_apply]
  rw [dist_eq_norm, dist_eq_norm, hsub]
  calc ‖insCLM i (u - v)‖ ≤ ‖insCLM i‖ * ‖u - v‖ := (insCLM i).le_opNorm (u - v)
    _ ≤ 1 * ‖u - v‖ := by gcongr; exact norm_insCLM_le_one i
    _ = ‖u - v‖ := one_mul _

theorem face_charts (S : WilkiesDesign.SOMin) (n : ℕ) (hn : 1 ≤ n)
    (hIH : ∀ F : ℕ, WilkiesDesign.AlgLemma S F (n - 1)) (F : ℕ) :
    ∃ p : MvPolynomial (Fin 3) ℝ, (∀ m ∈ p.support, 0 ≤ p.coeff m) ∧
      ∀ (D r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∀ (μ : ℕ) (X : Set (Fin n → ℝ)),
        μ ≤ n → X ⊆ WilkiesDesign.cube01 n → X ∈ S.Ω F D n → WilkiesDesign.DimLE X μ →
        ∃ Φ : Finset ((Fin μ → ℝ) → (Fin n → ℝ)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), -Real.log ε] p ∧
          (∀ φ ∈ Φ, (∀ t ∈ WilkiesDesign.openCube μ, φ t ∈ X) ∧
            ContDiffOn ℝ r φ (WilkiesDesign.openCube μ) ∧
            ∀ k ≤ r, ∀ t ∈ WilkiesDesign.openCube μ, ‖iteratedFDeriv ℝ k φ t‖ ≤ 1) ∧
          ∀ x ∈ X, x ∉ WilkiesDesign.openCube n → ∃ φ ∈ Φ, ∃ t ∈ WilkiesDesign.openCube μ, dist (φ t) x < ε := by
  classical
  -- the polynomial of the induction hypothesis, at the format of a face
  obtain ⟨p₀, hp₀⟩ := hIH (ffs F n)
  -- absorb the degree shift `dfs n` and the number `2n` of faces into a polynomial
  obtain ⟨p, hpnn, hpd⟩ := face_count_poly p₀ (dfs n) (n * 2)
  refine ⟨p, hpnn, ?_⟩
  intro D r ε hε0 hε1 μ X hμ hXcube hXΩ hXdim
  have hs : 0 ≤ -Real.log ε := by have := Real.log_neg hε0 hε1; linarith
  -- the source dimension of the face charts
  let μ' : ℕ := min μ (n - 1)
  have hμ'le : μ' ≤ n - 1 := Nat.min_le_right μ (n - 1)
  have hμ'leμ : μ' ≤ μ := Nat.min_le_left μ (n - 1)
  -- the induction hypothesis applied to each of the `2n` faces
  have hface : ∀ ic : Fin n × Fin 2,
      ∃ Φ : Finset ((Fin μ' → ℝ) → (Fin (n - 1) → ℝ)),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![((D + dfs n : ℕ) : ℝ), (r : ℝ), -Real.log ε] p₀ ∧
        (∀ φ ∈ Φ, (∀ t ∈ openCube μ', φ t ∈ faceProj ic.1 ((ic.2 : ℕ) : ℝ) X) ∧
          ContDiffOn ℝ r φ (openCube μ') ∧
          ∀ k ≤ r, ∀ t ∈ openCube μ', ‖iteratedFDeriv ℝ k φ t‖ ≤ 1) ∧
        (∀ y ∈ faceProj ic.1 ((ic.2 : ℕ) : ℝ) X,
          ∃ φ ∈ Φ, ∃ t ∈ openCube μ', dist (φ t) y < ε) := by
    intro ic
    exact hp₀ (D + dfs n) r ε hε0 hε1 μ' (faceProj ic.1 ((ic.2 : ℕ) : ℝ) X)
      hμ'le (faceProj_subset_cube01 hXcube ic.1 _)
      (face_proj_mem hXΩ ic.1 _) (face_dimle hμ ic.1 _ hXdim)
  choose Φic hΦic using hface
  -- push every face chart back into `ℝⁿ` and raise its source dimension to `μ`
  let liftF : (Fin n × Fin 2) → ((Fin μ' → ℝ) → (Fin (n - 1) → ℝ)) →
      ((Fin μ → ℝ) → (Fin n → ℝ)) :=
    fun ic φ t => insCoord ic.1 ((ic.2 : ℕ) : ℝ) (φ (projCoord hμ'leμ t))
  let Ψ : (Fin n × Fin 2) → Finset ((Fin μ → ℝ) → (Fin n → ℝ)) :=
    fun ic => (Φic ic).image (liftF ic)
  let Φ : Finset ((Fin μ → ℝ) → (Fin n → ℝ)) :=
    (Finset.univ : Finset (Fin n × Fin 2)).biUnion Ψ
  refine ⟨Φ, ?_, ?_, ?_⟩
  · -- the cardinality: at most `2n` times the face bound, then `face_count_poly`
    have h1nat : Φ.card ≤ ∑ ic ∈ (Finset.univ : Finset (Fin n × Fin 2)), (Ψ ic).card := by
      simpa only [Φ] using
        Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin n × Fin 2))) (t := Ψ)
    have h1 : (Φ.card : ℝ) ≤
        ∑ ic ∈ (Finset.univ : Finset (Fin n × Fin 2)), ((Ψ ic).card : ℝ) := by
      exact_mod_cast h1nat
    have h2 : ∑ ic ∈ (Finset.univ : Finset (Fin n × Fin 2)), ((Ψ ic).card : ℝ) ≤
        ∑ ic ∈ (Finset.univ : Finset (Fin n × Fin 2)), ((Φic ic).card : ℝ) := by
      refine Finset.sum_le_sum fun ic _ => ?_
      have h := Finset.card_image_le (s := Φic ic) (f := liftF ic)
      simp only [Ψ]
      exact_mod_cast h
    have h3 : ∑ ic ∈ (Finset.univ : Finset (Fin n × Fin 2)), ((Φic ic).card : ℝ) ≤
        ∑ _ic ∈ (Finset.univ : Finset (Fin n × Fin 2)),
          MvPolynomial.eval ![((D + dfs n : ℕ) : ℝ), (r : ℝ), -Real.log ε] p₀ :=
      Finset.sum_le_sum fun ic _ => (hΦic ic).1
    have h4 : ∑ _ic ∈ (Finset.univ : Finset (Fin n × Fin 2)),
          MvPolynomial.eval ![((D + dfs n : ℕ) : ℝ), (r : ℝ), -Real.log ε] p₀
        = ((n * 2 : ℕ) : ℝ) *
          MvPolynomial.eval ![((D + dfs n : ℕ) : ℝ), (r : ℝ), -Real.log ε] p₀ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      simp [nsmul_eq_mul]
    have h5 : ((n * 2 : ℕ) : ℝ) *
          MvPolynomial.eval ![((D + dfs n : ℕ) : ℝ), (r : ℝ), -Real.log ε] p₀
        ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), -Real.log ε] p := hpd D r (-Real.log ε) hs
    exact le_trans (le_trans (le_trans h1 h2) h3) (le_trans (le_of_eq h4) h5)
  · -- every chart of `Φ` is a chart of the required kind
    intro φ hφ
    rw [show Φ = (Finset.univ : Finset (Fin n × Fin 2)).biUnion Ψ from rfl,
      Finset.mem_biUnion] at hφ
    obtain ⟨ic, -, hφ⟩ := hφ
    rw [show Ψ ic = (Φic ic).image (liftF ic) from rfl, Finset.mem_image] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    obtain ⟨hψmem, hψcd, hψbd⟩ := (hΦic ic).2.1 ψ hψ
    have hproj : ∀ t ∈ openCube μ, projCoord hμ'leμ t ∈ openCube μ' :=
      fun t ht => projCoord_mem_openCube hμ'leμ ht
    have hcube : ∀ t ∈ openCube μ, ψ (projCoord hμ'leμ t) ∈ cube01 (n - 1) :=
      fun t ht => faceProj_subset_cube01 hXcube ic.1 _ (hψmem _ (hproj t ht))
    have hc01 : ((ic.2 : ℕ) : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
      rw [Set.mem_Icc]
      exact ⟨Nat.cast_nonneg _,
        by have := ic.2.isLt; exact_mod_cast (show (ic.2 : ℕ) ≤ 1 by omega)⟩
    have hpc := proj_charts hμ'leμ ψ hψcd hψbd
    obtain ⟨hcd, hbd⟩ := face_insert hn ic.1 hc01 (fun t => ψ (projCoord hμ'leμ t))
      hpc.1 hpc.2 hcube
    refine ⟨?_, hcd, hbd⟩
    dsimp only [liftF]
    intro t ht
    rw [insCoord_mem_faceProj ic.1 ((ic.2 : ℕ) : ℝ) X (ψ (projCoord hμ'leμ t))]
    exact hψmem _ (hproj t ht)
  · -- covering the boundary of the cube
    intro x hxX hxnot
    have hxcube : x ∈ cube01 n := hXcube hxX
    obtain ⟨i, hi⟩ := not_forall.mp (show ¬ (∀ i, x i ∈ Set.Ioo (0:ℝ) 1) from hxnot)
    rw [Set.mem_Ioo] at hi
    have hxi := hxcube i
    rw [Set.mem_Icc] at hxi
    have h01 : x i = 0 ∨ x i = 1 := by
      rcases lt_or_ge (x i) 1 with h | h
      · left; have := not_lt.mp (fun h0 => hi ⟨h0, h⟩); linarith
      · right; linarith
    -- for the face at `i` with value `k : Fin 2` (so `k = 0` or `k = 1`)
    have step : ∀ k : Fin 2, x i = ((k : ℕ) : ℝ) →
        ∃ φ ∈ Φ, ∃ t ∈ openCube μ, dist (φ t) x < ε := by
      intro k hk
      have hc : x (i, k).1 = (((i, k).2 : ℕ) : ℝ) := hk
      obtain ⟨ψ, hψmem, s, hs', hdist⟩ :=
        (hΦic (i, k)).2.2 (fun j => x (delSplit i j)) (by
          rw [← insCoord_mem_faceProj (i, k).1 (((i, k).2 : ℕ) : ℝ) X]
          rw [← eq_insCoord_of (i, k).1 (((i, k).2 : ℕ) : ℝ) x hc]
          exact hxX)
      refine ⟨liftF (i, k) ψ, ?_, extHalf (μ := μ) s, extHalf_mem_openCube (μ := μ) hs', ?_⟩
      · rw [show Φ = (Finset.univ : Finset (Fin n × Fin 2)).biUnion Ψ from rfl,
          Finset.mem_biUnion]
        refine ⟨(i, k), Finset.mem_univ _, ?_⟩
        rw [show Ψ (i, k) = (Φic (i, k)).image (liftF (i, k)) from rfl, Finset.mem_image]
        exact ⟨ψ, hψmem, rfl⟩
      · dsimp only [liftF]
        rw [projCoord_extHalf hμ'leμ]
        have hxeq : x = insCoord (i, k).1 (((i, k).2 : ℕ) : ℝ)
            (fun j => x (delSplit (i, k).1 j)) := eq_insCoord_of _ _ x hc
        have hle : dist (insCoord (i, k).1 (((i, k).2 : ℕ) : ℝ) (ψ s)) x ≤
            dist (ψ s) (fun j => x (delSplit (i, k).1 j)) := by
          have h := dist_insCoord_le (i, k).1 (((i, k).2 : ℕ) : ℝ) (ψ s)
            (fun j => x (delSplit (i, k).1 j))
          rw [← hxeq] at h
          exact h
        exact lt_of_le_of_lt hle hdist
    rcases h01 with h0 | h1
    · exact step 0 (by simpa using h0)
    · exact step 1 (by simpa using h1)

end Work.WilG5.Face
