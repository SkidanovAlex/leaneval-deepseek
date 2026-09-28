import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic
import Submission.Work.HP.HPgram
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Lat.detL_span_gram
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.Vero.SecondCaseDefs
import Submission.Work.HP.Vero.span_realify_latOrth_inf

set_option autoImplicit false

noncomputable section

namespace Work.HP.Vero

open Work.HP
open Work.HP.Transf
open scoped Pointwise

/-! ## Auxiliary real linear algebra

We need two facts about the explicit Euclidean form `dotR` on `ι → ℝ`:

* the orthogonal projection of `v` onto the plane `span ℝ {u1, u2}` realises the Euclidean
  distance `eucDist v (span ℝ {u1,u2})` when the Gram matrix of `u1, u2` is invertible;
* the `3 × 3` Gram determinant of `(u1, u2, v)` equals `det Gram(u1,u2) * dotR q q` when `v` is the
  sum of an element of the plane and a vector `q` orthogonal to `u1, u2`.
-/

/-- First row of the solution of the `2 × 2` Gram system. -/
lemma aux_solve1 (a b c x y : ℝ) (h : a * c - b * b ≠ 0) :
    (c * x - b * y) / (a * c - b * b) * a + (a * y - b * x) / (a * c - b * b) * b = x := by
  have h2 : c * a - b ^ 2 ≠ 0 := by
    rw [show c * a - b ^ 2 = a * c - b * b by ring]; exact h
  field_simp
  ring

/-- Second row of the solution of the `2 × 2` Gram system. -/
lemma aux_solve2 (a b c x y : ℝ) (h : a * c - b * b ≠ 0) :
    (c * x - b * y) / (a * c - b * b) * b + (a * y - b * x) / (a * c - b * b) * c = y := by
  have h2 : c * a - b ^ 2 ≠ 0 := by
    rw [show c * a - b ^ 2 = a * c - b * b by ring]; exact h
  field_simp
  ring

/-- Orthogonal projection onto the plane spanned by `u1, u2` (assumed to have invertible Gram
matrix) and its characterisation as the Euclidean distance. -/
lemma aux_proj_eucDist_pair {ι : Type*} [Fintype ι] (u1 u2 v : ι → ℝ)
    (hdet : dotR u1 u1 * dotR u2 u2 - dotR u1 u2 * dotR u2 u1 ≠ 0) :
    ∃ q : ι → ℝ, v - q ∈ Submodule.span ℝ ({u1, u2} : Set (ι → ℝ)) ∧
      dotR q u1 = 0 ∧ dotR q u2 = 0 ∧
      eucDist v (Submodule.span ℝ ({u1, u2} : Set (ι → ℝ))) = rNorm q := by
  have hdet' : dotR u1 u1 * dotR u2 u2 - dotR u1 u2 * dotR u1 u2 ≠ 0 := by
    simpa only [dotR_comm u2 u1] using hdet
  set Δ : ℝ := dotR u1 u1 * dotR u2 u2 - dotR u1 u2 * dotR u1 u2 with hΔ
  have hΔ0 : Δ ≠ 0 := by rw [hΔ]; exact hdet'
  set α : ℝ := (dotR u2 u2 * dotR u1 v - dotR u1 u2 * dotR u2 v) / Δ with hα
  set β : ℝ := (dotR u1 u1 * dotR u2 v - dotR u1 u2 * dotR u1 v) / Δ with hβ
  set p : ι → ℝ := α • u1 + β • u2 with hp
  have hpmem : p ∈ Submodule.span ℝ ({u1, u2} : Set (ι → ℝ)) := by
    rw [hp]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hq1 : dotR (v - p) u1 = 0 := by
    rw [dotR_sub_left, dotR_add_left, dotR_smul_left, dotR_smul_left, hα, hβ, hΔ,
      dotR_comm v u1, dotR_comm u2 u1]
    exact sub_eq_zero.mpr ((aux_solve1 (dotR u1 u1) (dotR u1 u2) (dotR u2 u2)
      (dotR u1 v) (dotR u2 v) hdet')).symm
  have hq2 : dotR (v - p) u2 = 0 := by
    rw [dotR_sub_left, dotR_add_left, dotR_smul_left, dotR_smul_left, hα, hβ, hΔ,
      dotR_comm v u2]
    exact sub_eq_zero.mpr ((aux_solve2 (dotR u1 u1) (dotR u1 u2) (dotR u2 u2)
      (dotR u1 v) (dotR u2 v) hdet')).symm
  refine ⟨v - p, ?_, hq1, hq2, ?_⟩
  · rw [show v - (v - p) = p from by abel]
    exact hpmem
  · refine le_antisymm (eucDist_le v _ hpmem) ?_
    rw [eucDist]
    refine le_csInf ⟨rNorm (v - p), p, hpmem, rfl⟩ ?_
    rintro r ⟨z, hz, rfl⟩
    have horth : dotR (v - p) (p - z) = 0 := by
      obtain ⟨r1, r2, hr⟩ := Submodule.mem_span_pair.mp (Submodule.sub_mem _ hpmem hz)
      rw [← hr, dotR_add_right, dotR_smul_right, dotR_smul_right, hq1, hq2]
      ring
    have hsq : rNorm (v - p) ^ 2 ≤ rNorm (v - z) ^ 2 := by
      have hab : v - z = (v - p) + (p - z) := by abel
      rw [hab, Transf.rNorm_add_sq_of_orthogonal horth]
      exact le_add_of_nonneg_right (sq_nonneg _)
    have hle := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (Transf.rNorm_nonneg _), abs_of_nonneg (Transf.rNorm_nonneg _)] at hle

/-- The `3 × 3` Gram determinant of `(u1, u2, v)` when `v` is the sum of an element of the plane
`span ℝ {u1, u2}` and a vector `q` orthogonal to `u1` and `u2`. -/
lemma aux_det_gram_three_eq {ι : Type*} [Fintype ι] (u1 u2 v q : ι → ℝ)
    (h1 : dotR q u1 = 0) (h2 : dotR q u2 = 0)
    (hp : v - q ∈ Submodule.span ℝ ({u1, u2} : Set (ι → ℝ))) :
    Matrix.det (Matrix.of fun i j : Fin 3 => dotR (![u1, u2, v] i) (![u1, u2, v] j))
      = (dotR u1 u1 * dotR u2 u2 - dotR u1 u2 * dotR u2 u1) * dotR q q := by
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hp
  have hv : v = q + (α • u1 + β • u2) := by rw [hαβ]; abel
  have h1' : dotR u1 q = 0 := by rw [dotR_comm]; exact h1
  have h2' : dotR u2 q = 0 := by rw [dotR_comm]; exact h2
  have h02 : dotR u1 v = α * dotR u1 u1 + β * dotR u1 u2 := by
    rw [hv]
    simp only [dotR_add_right, dotR_smul_right, h1', zero_add]
  have h12 : dotR u2 v = α * dotR u2 u1 + β * dotR u2 u2 := by
    rw [hv]
    simp only [dotR_add_right, dotR_smul_right, h2', zero_add]
  have h22 : dotR v v = dotR q q
      + (α * α * dotR u1 u1 + 2 * (α * β) * dotR u1 u2 + β * β * dotR u2 u2) := by
    rw [hv]
    simp only [dotR_add_left, dotR_add_right, dotR_smul_left, dotR_smul_right, h1, h2, h1', h2',
      dotR_comm u2 u1]
    ring
  have hM : (Matrix.of fun i j : Fin 3 => dotR (![u1, u2, v] i) (![u1, u2, v] j))
      = !![dotR u1 u1, dotR u1 u2, α * dotR u1 u1 + β * dotR u1 u2;
           dotR u2 u1, dotR u2 u2, α * dotR u2 u1 + β * dotR u2 u2;
           α * dotR u1 u1 + β * dotR u1 u2, α * dotR u2 u1 + β * dotR u2 u2,
           dotR q q + (α * α * dotR u1 u1 + 2 * (α * β) * dotR u1 u2
             + β * β * dotR u2 u2)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h02, h12, h22, dotR_comm v u1, dotR_comm v u2]
  rw [hM, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [dotR_comm u2 u1]
  ring

/-- An element of a lattice lies in the `ℤ`-span of the underlying vectors of any basis. -/
lemma aux_mem_span_range_basis {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin 2) ℤ L) {x : ι → ℤ} (hx : x ∈ L) :
    x ∈ Submodule.span ℤ (Set.range fun i : Fin 2 => ((b i : L) : ι → ℤ)) := by
  have h1 : (⟨x, hx⟩ : L) ∈ Submodule.span ℤ (Set.range b) := by
    rw [b.span_eq]; exact Submodule.mem_top
  have h2 : x ∈ Submodule.map (Submodule.subtype L) (Submodule.span ℤ (Set.range b)) :=
    ⟨⟨x, hx⟩, h1, rfl⟩
  rw [Submodule.map_span] at h2
  refine Submodule.span_mono ?_ h2
  rintro z ⟨w, hw, rfl⟩
  obtain ⟨i, rfl⟩ := hw
  exact ⟨i, rfl⟩

/-- The realification of an element of a lattice lies in the real span of the realified basis. -/
lemma aux_toR_mem_span_basis {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin 2) ℤ L) {x : ι → ℤ} (hx : x ∈ L) :
    toR x ∈ Submodule.span ℝ (Set.range fun i : Fin 2 => toR (b i : ι → ℤ)) := by
  have hxmem := aux_mem_span_range_basis L b hx
  refine Submodule.span_induction (p := fun z _ =>
    toR z ∈ Submodule.span ℝ (Set.range fun i : Fin 2 => toR (b i : ι → ℤ))) ?_ ?_ ?_ ?_ hxmem
  · rintro z ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · have h0 : toR (0 : ι → ℤ) = 0 := by funext i; simp [toR]
    rw [h0]; exact Submodule.zero_mem _
  · intro u v _ _ hu hv
    have h : toR (u + v) = toR u + toR v := by funext i; simp [toR]
    rw [h]; exact Submodule.add_mem _ hu hv
  · intro c u _ hu
    have h : toR (c • u) = (c : ℝ) • toR u := by funext i; simp [toR]
    rw [h]; exact Submodule.smul_mem _ _ hu

/-- The real span of the realified vectors of a `ℤ`-basis of a rank-two lattice containing the
`ℤ`-independent vectors `x` and `y` is `span ℝ {toR x, toR y}`. -/
lemma aux_span_range_basis_eq_span_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin 2) ℤ L) (x y : ι → ℤ)
    (hxy : LinearIndependent ℤ ![x, y]) (hx : x ∈ L) (hy : y ∈ L) :
    Submodule.span ℝ (Set.range fun i : Fin 2 => toR (b i : ι → ℤ))
      = Submodule.span ℝ ({toR x, toR y} : Set (ι → ℝ)) := by
  have hLIℤ : LinearIndependent ℤ (fun i : Fin 2 => (b i : ι → ℤ)) :=
    b.linearIndependent.map' (Submodule.subtype L) (Submodule.ker_subtype L)
  have hLIb : LinearIndependent ℝ (fun i : Fin 2 => toR (b i : ι → ℤ)) := by
    have h := linInd_intCastPi hLIℤ
    have hfun : (fun i : Fin 2 => intCastPi (b i : ι → ℤ)) = fun i : Fin 2 => toR (b i : ι → ℤ) := by
      funext i; rfl
    rwa [hfun] at h
  have hLIxy : LinearIndependent ℝ ![toR x, toR y] := by
    have h := linInd_intCastPi hxy
    have hfun : (fun i : Fin 2 => intCastPi (![x, y] i)) = ![toR x, toR y] := by
      funext i; fin_cases i <;> rfl
    rwa [hfun] at h
  have hle : Submodule.span ℝ ({toR x, toR y} : Set (ι → ℝ)) ≤
      Submodule.span ℝ (Set.range fun i : Fin 2 => toR (b i : ι → ℤ)) := by
    rw [Submodule.span_le]
    rintro z (rfl | rfl)
    · exact aux_toR_mem_span_basis L b hx
    · exact aux_toR_mem_span_basis L b hy
  have hfin : Module.finrank ℝ ↥(Submodule.span ℝ ({toR x, toR y} : Set (ι → ℝ)))
      = Module.finrank ℝ ↥(Submodule.span ℝ (Set.range fun i : Fin 2 => toR (b i : ι → ℤ))) := by
    rw [← Matrix.range_cons_cons_empty (toR x) (toR y) Matrix.vecEmpty]
    rw [finrank_span_eq_card hLIxy, finrank_span_eq_card hLIb]
  haveI : FiniteDimensional ℝ
      ↥(Submodule.span ℝ (Set.range fun i : Fin 2 => toR (b i : ι → ℤ))) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm

/-- The basis vectors of a rank-two lattice together with a vector whose realification is outside
`span ℝ {toR x, toR y}` are `ℤ`-linearly independent. -/
lemma aux_linInd_basis_pair_w {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin 2) ℤ L) (x y w : ι → ℤ)
    (hxy : LinearIndependent ℤ ![x, y]) (hx : x ∈ L) (hy : y ∈ L)
    (hw : toR w ∉ Submodule.span ℝ ({toR x, toR y} : Set (ι → ℝ))) :
    LinearIndependent ℤ ![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w] := by
  have hspan := aux_span_range_basis_eq_span_pair L b x y hxy hx hy
  have hw' : toR w ∉ Submodule.span ℝ (Set.range fun i : Fin 2 => toR (b i : ι → ℤ)) := by
    intro h; rw [hspan] at h; exact hw h
  have hLIℤ : LinearIndependent ℤ (fun i : Fin 2 => (b i : ι → ℤ)) :=
    b.linearIndependent.map' (Submodule.subtype L) (Submodule.ker_subtype L)
  have hLIb : LinearIndependent ℝ ![toR (b 0 : ι → ℤ), toR (b 1 : ι → ℤ)] := by
    have h := linInd_intCastPi hLIℤ
    have hfun : (fun i : Fin 2 => intCastPi (b i : ι → ℤ)) = ![toR (b 0 : ι → ℤ), toR (b 1 : ι → ℤ)] := by
      funext i; fin_cases i <;> rfl
    rwa [hfun] at h
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum : c 0 • ((b 0 : L) : ι → ℤ) + c 1 • ((b 1 : L) : ι → ℤ) + c 2 • w = 0 := by
    have h := hc
    rw [Fin.sum_univ_three] at h
    simpa using h
  have hR : (c 0 : ℝ) • toR (b 0 : ι → ℤ) + (c 1 : ℝ) • toR (b 1 : ι → ℤ)
      + (c 2 : ℝ) • toR w = 0 := by
    funext i
    have h := congrFun hsum i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h
    have h' : (c 0 : ℝ) * ↑((b 0 : ι → ℤ) i) + (c 1 : ℝ) * ↑((b 1 : ι → ℤ) i)
        + (c 2 : ℝ) * ↑(w i) = 0 := by exact_mod_cast h
    simpa only [toR, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h'
  have hA : (c 0 : ℝ) • toR (b 0 : ι → ℤ) + (c 1 : ℝ) • toR (b 1 : ι → ℤ)
      ∈ Submodule.span ℝ (Set.range fun i : Fin 2 => toR (b i : ι → ℤ)) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hc2 : c 2 = 0 := by
    by_contra h2
    apply hw'
    have hc2R : (c 2 : ℝ) ≠ 0 := by exact_mod_cast h2
    have hmem : (c 2 : ℝ) • toR w
        ∈ Submodule.span ℝ (Set.range fun i : Fin 2 => toR (b i : ι → ℤ)) := by
      have hz : (c 2 : ℝ) • toR w
          = -((c 0 : ℝ) • toR (b 0 : ι → ℤ) + (c 1 : ℝ) • toR (b 1 : ι → ℤ)) := by
        linear_combination hR
      rw [hz]; exact Submodule.neg_mem _ hA
    rw [show toR w = (c 2 : ℝ)⁻¹ • ((c 2 : ℝ) • toR w) from by
      rw [smul_smul, inv_mul_cancel₀ hc2R, one_smul]]
    exact Submodule.smul_mem _ _ hmem
  have hR2 : (c 0 : ℝ) • toR (b 0 : ι → ℤ) + (c 1 : ℝ) • toR (b 1 : ι → ℤ) = 0 := by
    simpa [hc2] using hR
  have hpair := (LinearIndependent.pair_iff.mp hLIb) (c 0 : ℝ) (c 1 : ℝ) hR2
  have hc0 : c 0 = 0 := by exact_mod_cast hpair.1
  have hc1 : c 1 = 0 := by exact_mod_cast hpair.2
  intro i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2

/-- Passing from a per-lattice bound to the bound involving `dmin 2`. -/
lemma aux_dmin_three_le_dmin_two_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℤ) (hxy : LinearIndependent ℤ ![x, y]) (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ L : Submodule ℤ (ι → ℤ), rk L = 2 → ({x, y} : Set (ι → ℤ)) ⊆ L →
      dmin 3 ({x, y} : Set (ι → ℤ)) ≤ detL L * d) :
    dmin 3 ({x, y} : Set (ι → ℤ)) ≤ dmin 2 ({x, y} : Set (ι → ℤ)) * d := by
  set S : Set ℝ := {D : ℝ | ∃ L : Submodule ℤ (ι → ℤ), rk L = 2 ∧
    ({x, y} : Set (ι → ℤ)) ⊆ L ∧ detL L = D} with hS
  have hSdef : dmin 2 ({x, y} : Set (ι → ℤ)) = sInf S := rfl
  have hne : S.Nonempty := by
    refine ⟨detL (Submodule.span ℤ ({x, y} : Set (ι → ℤ))),
      Submodule.span ℤ ({x, y} : Set (ι → ℤ)), ?_, ?_, rfl⟩
    · rw [rk, ← Matrix.range_cons_cons_empty x y Matrix.vecEmpty, finrank_span_eq_card hxy]
      simp
    · intro z hz
      exact Submodule.subset_span hz
  have hmain : dmin 3 ({x, y} : Set (ι → ℤ)) ≤ sInf (d • S : Set ℝ) := by
    refine le_csInf ?_ ?_
    · rcases hne with ⟨D, hD⟩
      exact ⟨d • D, ⟨D, hD, rfl⟩⟩
    · rintro r ⟨D, hD, rfl⟩
      rw [hS, Set.mem_ofPred_eq] at hD
      obtain ⟨L, hrk, hsub, hdet⟩ := hD
      show dmin 3 ({x, y} : Set (ι → ℤ)) ≤ d • D
      rw [smul_eq_mul, mul_comm, ← hdet]
      exact h L hrk hsub
  rw [Real.sInf_smul_of_nonneg hd S, smul_eq_mul] at hmain
  rw [← hSdef] at hmain
  rwa [mul_comm] at hmain

theorem dmin_three_le_eucDist {ι : Type*} [Fintype ι] [DecidableEq ι] (x y w : ι → ℤ)
    (hxy : LinearIndependent ℤ ![x, y])
    (hw : toR w ∉ Submodule.span ℝ ({toR x, toR y} : Set (ι → ℝ))) :
    dmin 3 ({x, y} : Set (ι → ℤ)) ≤ dmin 2 ({x, y} : Set (ι → ℤ)) *
      eucDist (toR w) ((Submodule.span ℝ ({toR x, toR y} : Set (ι → ℝ)) :
        Submodule ℝ (ι → ℝ)) : Set (ι → ℝ)) := by
  set d : ℝ := eucDist (toR w) (Submodule.span ℝ ({toR x, toR y} : Set (ι → ℝ))) with hd
  have hd0 : 0 ≤ d := by rw [hd]; exact eucDist_nonneg _ _
  have hkey : ∀ L : Submodule ℤ (ι → ℤ), rk L = 2 → ({x, y} : Set (ι → ℤ)) ⊆ L →
      dmin 3 ({x, y} : Set (ι → ℤ)) ≤ detL L * d := by
    intro L hrk hsub
    have hxL : x ∈ L := hsub (by simp)
    have hyL : y ∈ L := hsub (by simp)
    obtain ⟨k, bk⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
    have hk : k = 2 := by
      have h1 : Module.finrank ℤ L = k := by rw [Module.finrank_eq_card_basis bk]; simp
      rw [← h1]; exact hrk
    let b : Module.Basis (Fin 2) ℤ L := bk.reindex (finCongr hk)
    have hdetpos : 0 < (Work.HP.gramMat 2 L b).det := Work.HP.Lat.gramMat_det_pos 2 L b
    have hG2det : (Work.HP.gramMat 2 L b).det
        = dotR (toR (b 0 : ι → ℤ)) (toR (b 0 : ι → ℤ))
            * dotR (toR (b 1 : ι → ℤ)) (toR (b 1 : ι → ℤ))
          - dotR (toR (b 0 : ι → ℤ)) (toR (b 1 : ι → ℤ))
            * dotR (toR (b 1 : ι → ℤ)) (toR (b 0 : ι → ℤ)) := by
      rw [Work.HP.gramMat, Matrix.det_fin_two]
      simp only [Matrix.of_apply, dotR, toR]
    have hG2nn : 0 ≤ (Work.HP.gramMat 2 L b).det := le_of_lt hdetpos
    have hG2ne : dotR (toR (b 0 : ι → ℤ)) (toR (b 0 : ι → ℤ))
          * dotR (toR (b 1 : ι → ℤ)) (toR (b 1 : ι → ℤ))
        - dotR (toR (b 0 : ι → ℤ)) (toR (b 1 : ι → ℤ))
          * dotR (toR (b 1 : ι → ℤ)) (toR (b 0 : ι → ℤ)) ≠ 0 := by
      rw [← hG2det]; exact ne_of_gt hdetpos
    obtain ⟨q, hqspan, hq1, hq2, hqd⟩ :=
      aux_proj_eucDist_pair (toR (b 0 : ι → ℤ)) (toR (b 1 : ι → ℤ)) (toR w) hG2ne
    have hG3 := aux_det_gram_three_eq (toR (b 0 : ι → ℤ)) (toR (b 1 : ι → ℤ)) (toR w) q hq1 hq2 hqspan
    have hLI3 := aux_linInd_basis_pair_w L b x y w hxy hxL hyL hw
    have hspanB := aux_span_range_basis_eq_span_pair L b x y hxy hxL hyL
    have hrangeB : (Set.range fun i : Fin 2 => toR (b i : ι → ℤ))
        = ({toR (b 0 : ι → ℤ), toR (b 1 : ι → ℤ)} : Set (ι → ℝ)) := by
      ext z; constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · rintro (hz | hz)
        · exact ⟨0, by simpa using hz.symm⟩
        · exact ⟨1, by simpa using hz.symm⟩
    have hd_eq : d = rNorm q := by
      rw [hd]
      have hV : Submodule.span ℝ ({toR x, toR y} : Set (ι → ℝ))
          = Submodule.span ℝ ({toR (b 0 : ι → ℤ), toR (b 1 : ι → ℤ)} : Set (ι → ℝ)) := by
        rw [← hspanB, hrangeB]
      rw [hV]; exact hqd
    have hxM : x ∈ Submodule.span ℤ
        (Set.range ![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w]) := by
      have hgen : (Set.range fun i : Fin 2 => ((b i : L) : ι → ℤ))
          ⊆ Set.range ![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w] := by
        rintro z ⟨i, rfl⟩
        fin_cases i
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
      exact Submodule.span_mono hgen (aux_mem_span_range_basis L b hxL)
    have hyM : y ∈ Submodule.span ℤ
        (Set.range ![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w]) := by
      have hgen : (Set.range fun i : Fin 2 => ((b i : L) : ι → ℤ))
          ⊆ Set.range ![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w] := by
        rintro z ⟨i, rfl⟩
        fin_cases i
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
      exact Submodule.span_mono hgen (aux_mem_span_range_basis L b hyL)
    have hsubM : ({x, y} : Set (ι → ℤ)) ⊆ Submodule.span ℤ
        (Set.range ![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w]) := by
      intro z hz
      rcases hz with hz | hz
      · rw [hz]; exact hxM
      · rw [hz]; exact hyM
    have hrkM : rk (Submodule.span ℤ
        (Set.range ![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w])) = 3 := by
      rw [rk, finrank_span_eq_card hLI3, Fintype.card_fin]
    have hdmin3 : dmin 3 ({x, y} : Set (ι → ℤ)) ≤ detL (Submodule.span ℤ
        (Set.range ![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w])) := by
      rw [dmin]
      refine csInf_le ⟨0, ?_⟩ ⟨_, hrkM, hsubM, rfl⟩
      rintro D ⟨L', _, _, rfl⟩
      exact detL_nonneg_gram L'
    have hdetL : detL L = Real.sqrt ((Work.HP.gramMat 2 L b).det) :=
      Work.HP.Lat.detL_basis_gram L b
    have hdetM1 : detL (Submodule.span ℤ
        (Set.range ![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w]))
        = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin 3 =>
            dotR (toR (![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w] i))
              (toR (![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w] j)))) :=
      Work.HP.Lat.detL_span_gram 3 ![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w] hLI3
    have hmats : (Matrix.of fun i j : Fin 3 =>
          dotR (toR (![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w] i))
            (toR (![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w] j)))
        = (Matrix.of fun i j : Fin 3 =>
            dotR (![toR (b 0 : ι → ℤ), toR (b 1 : ι → ℤ), toR w] i)
              (![toR (b 0 : ι → ℤ), toR (b 1 : ι → ℤ), toR w] j)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hG3' : Matrix.det (Matrix.of fun i j : Fin 3 =>
          dotR (![toR (b 0 : ι → ℤ), toR (b 1 : ι → ℤ), toR w] i)
            (![toR (b 0 : ι → ℤ), toR (b 1 : ι → ℤ), toR w] j))
        = (Work.HP.gramMat 2 L b).det * d ^ 2 := by
      rw [hG3, ← hG2det, hd_eq, ← Transf.rNorm_sq]
    have hdetM : detL (Submodule.span ℤ
        (Set.range ![((b 0 : L) : ι → ℤ), ((b 1 : L) : ι → ℤ), w])) = detL L * d := by
      rw [hdetM1, hmats, hG3', Real.sqrt_mul hG2nn, Real.sqrt_sq hd0, hdetL]
    exact hdmin3.trans_eq hdetM
  have hmain := aux_dmin_three_le_dmin_two_mul x y hxy d hd0 hkey
  rw [hd] at hmain
  exact hmain

end Work.HP.Vero
