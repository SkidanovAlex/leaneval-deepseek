/-
  WilE8 / Box — `boxZero_starR`: the box-zero sets of exp-polynomials are `StarR`-sets.

  The presentation of `boxZero M P = {z | (∀ i, |z i| ≤ M) ∧ P (z, exp z) = 0}` for `M ≥ 0`
  is built in `Submission/Work/WilE8/Box/Defs.lean`: it is the `t`-block projection of the
  semi-Pfaffian set `boxSet N M P` on three blocks `(t, s, u)` with

  * `t i = psi (z i)`, `s i = z i / M`, `u i ^ 2 = t i * s i`,

  the chain of the semi-Pfaffian set being `exp (M * s i)`.  The format is `4N` and the degree
  is bounded by `8N + d + 1`, both independent of `M`; the number of connected components is
  controlled by the hypothesis `hE2` (the frozen `E2_components`), which supplies
  representatives of the connected components of a semi-Pfaffian set, polynomially many in its
  degree.  This makes `psiV '' boxZero M P` a `*`-set, and `StarR` is its `psiV`-preimage.

  The case `M < 0` is degenerate (`boxZero M P = ∅` for `N ≥ 1`, and `∅` or `univ` for `N = 0`)
  and is handled separately.
-/
import Mathlib
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.E2.star_of_semipf
import Submission.Work.WilE10.Psi
import Submission.Work.WilE8.Poly.eval_mono_nat
import Submission.Work.WilE8.Box.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE8.Box

open WilkiesDesign WilkiesDesign.E

/-! ## `psiV`: injectivity and preimages -/

lemma psiV_injective {N : ℕ} : Function.Injective (WilkiesDesign.E.psiV (n := N)) := by
  intro x y h
  funext i
  exact Work.WilE10.psi_injective (congrFun h i)

/-- Since `psiV` is injective, pulling back the `psiV`-image of a set gives the set back. -/
lemma psiV_preimage_image {N : ℕ} (Y : Set (Fin N → ℝ)) :
    WilkiesDesign.E.psiV ⁻¹' (WilkiesDesign.E.psiV '' Y) = Y :=
  Set.preimage_image_eq Y psiV_injective

/-- A `Star`-set presented on the `psiV`-image of `Y` gives a `StarR`-presentation of `Y`. -/
theorem StarR_of_star_image {F D N : ℕ} {Y : Set (Fin N → ℝ)}
    (h : WilkiesDesign.E.Star F D N (WilkiesDesign.E.psiV '' Y)) :
    WilkiesDesign.E.StarR F D N Y :=
  ⟨_, h, (psiV_preimage_image Y).symm⟩

/-! ## The point with prescribed blocks -/

/-- The point of `Fin (N + (N + N))` whose `t`-, `s`- and `u`-blocks are `f`, `g` and `h`. -/
def boxPoint (N : ℕ) (f g h : Fin N → ℝ) : Fin (N + (N + N)) → ℝ :=
  fun j => if hj : (j : ℕ) < N then f ⟨j, hj⟩
    else if hj2 : (j : ℕ) < N + N then g ⟨(j : ℕ) - N, by omega⟩
    else h ⟨(j : ℕ) - (N + N), by omega⟩

/-- Every coordinate is in one of the three blocks. -/
lemma boxPoint_cases (N : ℕ) (j : Fin (N + (N + N))) :
    (∃ i : Fin N, j = tCoord N i) ∨ (∃ i : Fin N, j = sCoord N i) ∨
      (∃ i : Fin N, j = uCoord N i) := by
  by_cases hj : (j : ℕ) < N
  · exact Or.inl ⟨⟨j, hj⟩, by ext; simp [tCoord]⟩
  · by_cases hj2 : (j : ℕ) < N + N
    · refine Or.inr (Or.inl ⟨⟨(j : ℕ) - N, by omega⟩, ?_⟩)
      ext
      show (j : ℕ) = N + ((j : ℕ) - N)
      omega
    · refine Or.inr (Or.inr ⟨⟨(j : ℕ) - (N + N), by omega⟩, ?_⟩)
      ext
      show (j : ℕ) = N + N + ((j : ℕ) - (N + N))
      omega

lemma boxPoint_tCoord (N : ℕ) (f g h : Fin N → ℝ) (i : Fin N) :
    boxPoint N f g h (tCoord N i) = f i := by
  have hlt : ((tCoord N i : Fin (N + (N + N))) : ℕ) < N := by simp [tCoord]
  have hfin : (⟨((tCoord N i : Fin (N + (N + N))) : ℕ), hlt⟩ : Fin N) = i :=
    Fin.ext (by simp [tCoord])
  simp only [boxPoint, hlt, dite_true, hfin]

lemma boxPoint_sCoord (N : ℕ) (f g h : Fin N → ℝ) (i : Fin N) :
    boxPoint N f g h (sCoord N i) = g i := by
  have hv : ((sCoord N i : Fin (N + (N + N))) : ℕ) = N + i.1 := rfl
  have h1 : ¬ ((sCoord N i : Fin (N + (N + N))) : ℕ) < N := by omega
  have h2 : ((sCoord N i : Fin (N + (N + N))) : ℕ) < N + N := by omega
  have hfin : (⟨((sCoord N i : Fin (N + (N + N))) : ℕ) - N, by omega⟩ : Fin N) = i :=
    Fin.ext (by show (sCoord N i : Fin (N + (N + N))).1 - N = i.1; omega)
  simp only [boxPoint, h1, h2, dite_false, dite_true, hfin]

lemma boxPoint_uCoord (N : ℕ) (f g h : Fin N → ℝ) (i : Fin N) :
    boxPoint N f g h (uCoord N i) = h i := by
  have hv : ((uCoord N i : Fin (N + (N + N))) : ℕ) = N + N + i.1 := rfl
  have h1 : ¬ ((uCoord N i : Fin (N + (N + N))) : ℕ) < N := by omega
  have h2 : ¬ ((uCoord N i : Fin (N + (N + N))) : ℕ) < N + N := by omega
  have hfin : (⟨((uCoord N i : Fin (N + (N + N))) : ℕ) - (N + N), by omega⟩ : Fin N) = i :=
    Fin.ext (by show (uCoord N i : Fin (N + (N + N))).1 - (N + N) = i.1; omega)
  simp only [boxPoint, h1, h2, dite_false, hfin]

lemma boxPoint_mem_cube (N : ℕ) {f g h : Fin N → ℝ}
    (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) (hh : ∀ i, |h i| ≤ 1) :
    boxPoint N f g h ∈ cubeC (N + (N + N)) := by
  intro j
  rcases boxPoint_cases N j with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [boxPoint_tCoord]; exact hf i
  · rw [boxPoint_sCoord]; exact hg i
  · rw [boxPoint_uCoord]; exact hh i

/-! ## An elementary identity for `psi` -/

lemma psi_sq_mul_self (x : ℝ) : psi x ^ 2 * (1 + x ^ 2) = x ^ 2 := by
  rw [Work.WilE10.psi_sq, div_mul_cancel₀ _ (by positivity : (1 : ℝ) + x ^ 2 ≠ 0)]

/-! ## The projection identity

`projFirst N (N+N) '' boxSet N M P = psiV '' boxZero M P`, for `M ≥ 0`. -/

/-- The forward inclusion: a point of the presentation projects into the `psiV`-image of the
box-zero set. -/
lemma projFirst_mem_psiV_image {N : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) {x : Fin (N + (N + N)) → ℝ}
    (hx : x ∈ boxSet N M P) :
    WilkiesDesign.E.projFirst N (N + N) x ∈ WilkiesDesign.E.psiV '' WilkiesDesign.boxZero M P := by
  obtain ⟨hcube, h1, h2, h3⟩ := mem_boxSet_iff.mp hx
  refine ⟨fun i => M * x (sCoord N i), ⟨fun i => ?_, h3⟩, ?_⟩
  · rw [abs_mul, abs_of_nonneg hM]
    have hxi : |x (sCoord N i)| ≤ 1 := hcube (sCoord N i)
    nlinarith
  · funext i
    show psi (M * x (sCoord N i)) = x (tCoord N i)
    have hsq : x (tCoord N i) ^ 2 * (1 + (M * x (sCoord N i)) ^ 2) =
        (M * x (sCoord N i)) ^ 2 := by
      have h := h1 i
      have hm : (M * x (sCoord N i)) ^ 2 = M ^ 2 * x (sCoord N i) ^ 2 := by ring
      rw [hm]
      exact h
    have hsgn : 0 ≤ x (tCoord N i) * (M * x (sCoord N i)) := by
      have h := h2 i
      have h4 : x (tCoord N i) * (M * x (sCoord N i)) = M * x (uCoord N i) ^ 2 := by
        rw [← h]; ring
      rw [h4]
      exact mul_nonneg hM (sq_nonneg _)
    exact (Work.WilE10.psi_eq_of_sq hsq hsgn).symm

/-- The backward inclusion: every point of the box-zero set occurs as the projection of a point
of the presentation, with `s i = z i / M`, `t i = psi (z i)` and `u i ^ 2 = t i * s i`. -/
lemma boxSet_mem_of_boxZero {N : ℕ} {M : ℝ} (hM : 0 ≤ M)
    {P : MvPolynomial (Fin N ⊕ Fin N) ℝ} {z : Fin N → ℝ}
    (hz : z ∈ WilkiesDesign.boxZero M P) :
    ∃ x ∈ boxSet N M P, WilkiesDesign.E.projFirst N (N + N) x = WilkiesDesign.E.psiV z := by
  obtain ⟨hzM, hzP⟩ := hz
  have hs : ∀ i, M * (z i / M) = z i := by
    intro i
    by_cases hM0 : M = 0
    · subst hM0
      have hz0 : z i = 0 := by
        have h := hzM i
        rw [abs_le] at h
        linarith [h.1, h.2]
      rw [hz0]; ring
    · rw [mul_comm, div_mul_cancel₀ _ hM0]
  have hsabs : ∀ i, |z i / M| ≤ 1 := by
    intro i
    by_cases hM0 : M = 0
    · subst hM0; simp
    · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
      have hzi : |z i| ≤ M := hzM i
      rw [abs_div, abs_of_pos hMpos]
      exact (div_le_one hMpos).mpr hzi
  have hspos : ∀ i, 0 ≤ psi (z i) * (z i / M) := by
    intro i
    by_cases hM0 : M = 0
    · subst hM0; simp
    · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
      rw [show psi (z i) * (z i / M) = psi (z i) * z i / M from by ring]
      exact div_nonneg (psi_mul_self_nonneg (z i)) (le_of_lt hMpos)
  have huabs : ∀ i, |Real.sqrt (psi (z i) * (z i / M))| ≤ 1 := by
    intro i
    refine abs_le_one_iff_mul_self_le_one.mpr ?_
    rw [show Real.sqrt (psi (z i) * (z i / M)) * Real.sqrt (psi (z i) * (z i / M)) =
        Real.sqrt (psi (z i) * (z i / M)) ^ 2 from by ring,
      Real.sq_sqrt (hspos i)]
    have hpsi : |psi (z i)| ≤ 1 := Work.WilE10.psi_abs_le_one (z i)
    have hsl : |z i / M| ≤ 1 := hsabs i
    calc psi (z i) * (z i / M) ≤ |psi (z i) * (z i / M)| := le_abs_self _
      _ = |psi (z i)| * |z i / M| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul hpsi hsl (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  refine ⟨boxPoint N (fun i => psi (z i)) (fun i => z i / M)
    (fun i => Real.sqrt (psi (z i) * (z i / M))), ?_, ?_⟩
  · refine mem_boxSet_iff.mpr ⟨?_, ?_, ?_, ?_⟩
    · exact boxPoint_mem_cube N (fun i => Work.WilE10.psi_abs_le_one (z i)) hsabs huabs
    · intro i
      have hsq : M ^ 2 * (z i / M) ^ 2 = z i ^ 2 := by
        rw [show M ^ 2 * (z i / M) ^ 2 = (M * (z i / M)) ^ 2 from by ring, hs i]
      rw [boxPoint_tCoord, boxPoint_sCoord, hsq, psi_sq_mul_self]
    · intro i
      rw [boxPoint_tCoord, boxPoint_sCoord, boxPoint_uCoord]
      exact (Real.sq_sqrt (hspos i)).symm
    · have hfun : (fun i => M * boxPoint N (fun i => psi (z i)) (fun i => z i / M)
          (fun i => Real.sqrt (psi (z i) * (z i / M))) (sCoord N i)) = z := by
        funext i
        rw [boxPoint_sCoord]
        exact hs i
      rw [hfun, hzP]
  · funext i
    exact boxPoint_tCoord N _ _ _ i

/-- The projection of the presentation is the `psiV`-image of the box-zero set. -/
theorem projFirst_boxSet {N : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) :
    WilkiesDesign.E.projFirst N (N + N) '' boxSet N M P =
      WilkiesDesign.E.psiV '' WilkiesDesign.boxZero M P := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro t ⟨x, hx, rfl⟩
    exact projFirst_mem_psiV_image hM P hx
  · rintro t ⟨z, hz, rfl⟩
    exact boxSet_mem_of_boxZero hM hz

/-! ## The main bounds -/

/-- For `M ≥ 0`, `boxZero M P` is a `StarR`-set with format and degree bounded uniformly in
`M` and in `P` (the bounds depend only on `N` and on the degree bound `d` of `P`). -/
theorem boxZero_starR_nonneg
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y)
    (N d : ℕ) :
    ∃ F D : ℕ, ∀ (M : ℝ), 0 ≤ M → ∀ (P : MvPolynomial (Fin N ⊕ Fin N) ℝ),
      P.totalDegree ≤ d → WilkiesDesign.E.StarR F D N (WilkiesDesign.boxZero M P) := by
  refine ⟨(N + (N + N)) + N,
    (hE2 ((N + (N + N)) + N)).choose.eval (8 * N + d + 1) * (8 * N + d + 1), ?_⟩
  intro M hM P hd
  have hstar := Work.WilE8.E2.star_of_semipf hE2 N (N + N) (boxSemiPf N M P)
  have hpoly : (hE2 (boxSemiPf N M P).fmt).choose = (hE2 ((N + (N + N)) + N)).choose := by
    rw [boxSemiPf_fmt]
  have hdegX : (boxSemiPf N M P).deg ≤ 8 * N + d + 1 := boxSemiPf_deg_le N M d P hd
  have hfmt : (boxSemiPf N M P).fmt ≤ (N + (N + N)) + N := le_of_eq (boxSemiPf_fmt N M P)
  have hdeg : (hE2 (boxSemiPf N M P).fmt).choose.eval (boxSemiPf N M P).deg *
      (boxSemiPf N M P).deg ≤
      (hE2 ((N + (N + N)) + N)).choose.eval (8 * N + d + 1) * (8 * N + d + 1) := by
    rw [hpoly]
    exact Nat.mul_le_mul (Work.WilE8.Poly.eval_mono_nat _ hdegX) hdegX
  have hmono := Work.WilE8.Star.mono hstar hfmt hdeg
  rw [boxSemiPf_set, projFirst_boxSet hM P] at hmono
  exact StarR_of_star_image hmono

/-! ## The degenerate negative case -/

/-- For `N ≥ 1` and `M < 0` the box is empty. -/
lemma boxZero_eq_empty {N : ℕ} (hN : 0 < N) {M : ℝ} (hM : M < 0)
    (P : MvPolynomial (Fin N ⊕ Fin N) ℝ) : WilkiesDesign.boxZero M P = ∅ := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzM, -⟩ := hz
    have h1 : |z ⟨0, hN⟩| ≤ M := hzM ⟨0, hN⟩
    have h2 : 0 ≤ |z ⟨0, hN⟩| := abs_nonneg _
    linarith
  · intro hz
    exact absurd hz (by simp)

/-- In dimension `0` the box-zero set is `univ` or `∅`. -/
lemma boxZero_zero_dim {M : ℝ} (P : MvPolynomial (Fin 0 ⊕ Fin 0) ℝ) :
    WilkiesDesign.boxZero M P = Set.univ ∨ WilkiesDesign.boxZero M P = ∅ := by
  by_cases hp : expPolyEval P (fun i : Fin 0 => i.elim0) = 0
  · left
    ext z
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    refine ⟨fun i : Fin 0 => i.elim0, ?_⟩
    have hz : z = fun i : Fin 0 => i.elim0 := by funext i; exact i.elim0
    rw [hz]
    exact hp
  · right
    ext z
    refine ⟨fun hz => ?_, fun hz => absurd hz (by simp)⟩
    obtain ⟨-, hz'⟩ := hz
    have hz0 : z = fun i : Fin 0 => i.elim0 := by funext i; exact i.elim0
    rw [hz0] at hz'
    exact absurd hz' hp

/-- For `M < 0` the box-zero set is `StarR` with format and degree `0`. -/
theorem boxZero_starR_neg (N d : ℕ) :
    ∃ F D : ℕ, ∀ (M : ℝ), M < 0 → ∀ (P : MvPolynomial (Fin N ⊕ Fin N) ℝ),
      P.totalDegree ≤ d → WilkiesDesign.E.StarR F D N (WilkiesDesign.boxZero M P) := by
  refine ⟨0, 0, fun M hM P _ => ?_⟩
  by_cases hN : N = 0
  · subst hN
    rcases boxZero_zero_dim (M := M) P with h | h
    · rw [h]; exact StarR.univ 0 0 le_rfl
    · rw [h]; exact StarR.empty 0 0
  · rw [boxZero_eq_empty (Nat.pos_of_ne_zero hN) hM P]
    exact StarR.empty 0 N

/-! ## The target -/

theorem boxZero_starR
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y)
    (N d : ℕ) :
    ∃ F D : ℕ, ∀ (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ), P.totalDegree ≤ d →
      WilkiesDesign.E.StarR F D N (WilkiesDesign.boxZero M P) := by
  obtain ⟨F₁, D₁, h₁⟩ := boxZero_starR_nonneg hE2 N d
  obtain ⟨F₂, D₂, h₂⟩ := boxZero_starR_neg N d
  refine ⟨F₁ + F₂, D₁ + D₂, fun M P hd => ?_⟩
  rcases lt_or_ge M 0 with h | h
  · exact StarR.mono (h₂ M h P hd) (Nat.le_add_left F₂ F₁) (Nat.le_add_left D₂ D₁)
  · exact StarR.mono (h₁ M h P hd) (Nat.le_add_right F₁ F₂) (Nat.le_add_right D₁ D₂)

end Work.WilE8.Box
