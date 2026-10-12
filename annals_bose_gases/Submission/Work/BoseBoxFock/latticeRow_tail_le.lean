import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.BoseBoxFock.LatFourierDefs
import Submission.Work.BoseBoxFock.lattice_cubeTail_le
import Submission.Work.BoseBoxFock.summable_vec_inv_one_add_norm_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latticeRow_tail_le`

The finite lattice row sum of a rapidly decaying coefficient family converges to the full lattice
series, **uniformly in the phase** `z`:

`∑_{k : Lab N'} F (labVec N' k) e^{i⟪kmomLab ℓ N' k, z⟫} ⟶ ∑'_n F n e^{i⟪kmomInt ℓ n, z⟫}`.

Since `‖e^{iθ}‖ = 1` the phase is irrelevant and the whole content is the tail estimate for the
coefficient family on the lattice complement of the cube `[-N',N']³`, which is exactly
`Work.BoseBoxFock.lattice_cubeTail_le` at `g = ‖F ·‖`.

## Proof

* `labVec N` maps the label group `Lab N` bijectively onto the cube `[-N,N]³ ∩ ℤ³` (`latCube`), so
  the finite sum reindexes (`sum_labVec_eq_latCube`);
* `kmomLab ℓ N k` and `kmomInt ℓ (labVec N k)` are *definitionally* equal, so the characters agree;
* splitting `∑'_n` at the cube (`Summable.sum_add_tsum_compl`) exhibits the difference
  (finite sum `−` full series) as the `tsum` over the complement of the cube;
* the complement of `[-N,N]³` is exactly `{n | ∃ i, N < |n i|}` (`not_mem_latCube`), so
  `lattice_cubeTail_le` bounds that `tsum` by `ε`, for every `N' ≥ N` and every `z`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The lattice cube `[-N,N]³ ∩ ℤ³` -/

/-- The cube `[-N,N]³ ∩ ℤ³` of lattice indices. -/
private def latCube (N : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(N : ℤ)) (N : ℤ))

private lemma mem_latCube {N : ℕ} {m : Fin 3 → ℤ} :
    m ∈ latCube N ↔ ∀ i : Fin 3, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ) := by
  rw [latCube, Fintype.mem_piFinset]
  constructor
  · intro h i; simpa using h i
  · intro h i; simpa using h i

private lemma card_latCube (N : ℕ) : (latCube N).card = (2 * N + 1) ^ 3 := by
  rw [latCube, Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 from by
    rw [Int.card_Icc]
    have h : ((N : ℤ) + 1 - (-(N : ℤ))) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]]

private lemma card_lab (N : ℕ) : Fintype.card (Lab N) = (2 * N + 1) ^ 3 := by
  simp [Lab, ZMod.card]

/-- `|x.valMinAbs| ≤ N` for `x : ZMod (2N+1)`: the least-absolute representative lies in the
canonical window. -/
private lemma abs_valMinAbs_le (N : ℕ) (x : ZMod (2 * N + 1)) : |x.valMinAbs| ≤ (N : ℤ) := by
  have h := (ZMod.valMinAbs_spec x x.valMinAbs).mp rfl
  have h2 := h.2
  rw [Set.mem_Ioc] at h2
  obtain ⟨h1, h2⟩ := h2
  rw [abs_le]
  constructor <;> omega

private lemma labVec_injective (N : ℕ) : Function.Injective (labVec N) := by
  intro a b hab
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun hab i)

private lemma labVec_mem_latCube (N : ℕ) (n : Lab N) : labVec N n ∈ latCube N := by
  rw [mem_latCube]
  intro i
  exact abs_le.mp (abs_valMinAbs_le N (n i))

/-- **`labVec N` maps the label group onto the cube `[-N,N]³`.** -/
private lemma image_labVec_latCube (N : ℕ) :
    (Finset.univ.image (labVec N)) = latCube N := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro m hm
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hm
    exact labVec_mem_latCube N n
  · rw [Finset.card_image_of_injective _ (labVec_injective N), Finset.card_univ, card_lab,
      card_latCube]

/-- The complement of the cube `[-N,N]³` inside `ℤ³` is the truncation set
`{n | ∃ i, N < |n i|}`. -/
private lemma not_mem_latCube {N : ℕ} {m : Fin 3 → ℤ} :
    m ∉ latCube N ↔ ∃ i : Fin 3, (N : ℤ) < |m i| := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h (mem_latCube.mpr (fun i => abs_le.mp (hc i)))
  · rintro ⟨i, hi⟩ h
    exact absurd (abs_le.mpr ((mem_latCube.mp h) i)) (not_le.mpr hi)

/-- **Reindexing** a `Lab N`-indexed sum onto the cube. -/
private lemma sum_labVec_eq_latCube {M : Type*} [AddCommMonoid M] (N : ℕ)
    (G : (Fin 3 → ℤ) → M) :
    (∑ k : Lab N, G (labVec N k)) = ∑ d ∈ latCube N, G d := by
  rw [← Finset.sum_image (f := G) (labVec_injective N).injOn, image_labVec_latCube]

/-! ## 2. The lattice character -/

/-- The lattice character `z ↦ e^{i⟪kmomInt ℓ n, z⟫}`. -/
private def latChr (ℓ : ℝ) (n : Fin 3 → ℤ) (z : E3) : ℂ :=
  Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))

private lemma norm_exp_I_mul (r : ℝ) : ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

private lemma norm_latChr (ℓ : ℝ) (n : Fin 3 → ℤ) (z : E3) : ‖latChr ℓ n z‖ = 1 := by
  change ‖Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℝ) : ℂ))‖ = 1
  exact norm_exp_I_mul _

/-! ## 3. The tail estimate -/

theorem latticeRow_tail_le {ℓ : ℝ} (hℓ : 0 < ℓ) {F : (Fin 3 → ℤ) → ℂ}
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖F n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ z : EuclideanSpace ℝ (Fin 3),
      ‖(∑ k : Work.BoseBoxFock.Lab N', F (Work.BoseBoxFock.labVec N' k)
            * Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomLab ℓ N' k) z : ℝ) : ℂ)))
        - (∑' n : Fin 3 → ℤ, F n
            * Complex.exp (Complex.I * ((inner ℝ (Work.BoseBoxFock.kmomInt ℓ n) z : ℝ) : ℂ)))‖ ≤ ε := by
  obtain ⟨C, hC0, hC⟩ := hF
  -- summability of the coefficient norms, by comparison with the `52`-power lattice majorant
  have hgsum : Summable (fun n : Fin 3 → ℤ => ‖F n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hC
      (Summable.mul_left C (summable_vec_inv_one_add_norm_sq (k := 52) (by norm_num)))
  intro ε hε
  obtain ⟨N, hN⟩ := lattice_cubeTail_le (g := fun n : Fin 3 → ℤ => ‖F n‖)
    (fun n => norm_nonneg _) hgsum ε hε
  refine ⟨N, fun N' hN' z => ?_⟩
  -- rewrite the goal in the `latChr` vocabulary
  change ‖(∑ k : Lab N', F (labVec N' k) * latChr ℓ (labVec N' k) z)
      - (∑' n : Fin 3 → ℤ, F n * latChr ℓ n z)‖ ≤ ε
  -- the summand is summable (the character has modulus `1`)
  have hfsum : Summable (fun n : Fin 3 → ℤ => F n * latChr ℓ n z) :=
    Summable.of_norm_bounded hgsum (fun n => by simp [norm_latChr])
  -- split the full series at the cube
  have hsplit : (∑ n ∈ latCube N', F n * latChr ℓ n z)
      + (∑' x : ↑(↑(latCube N') : Set (Fin 3 → ℤ))ᶜ, F ↑x * latChr ℓ ↑x z)
      = ∑' n : Fin 3 → ℤ, F n * latChr ℓ n z :=
    hfsum.sum_add_tsum_compl (s := latCube N')
  -- reindex the finite sum from the label group onto the cube
  have hrow : (∑ k : Lab N', F (labVec N' k) * latChr ℓ (labVec N' k) z)
      = ∑ n ∈ latCube N', F n * latChr ℓ n z :=
    sum_labVec_eq_latCube N' (fun n => F n * latChr ℓ n z)
  have hdiff : (∑ k : Lab N', F (labVec N' k) * latChr ℓ (labVec N' k) z)
      - (∑' n : Fin 3 → ℤ, F n * latChr ℓ n z)
      = - (∑' x : ↑(↑(latCube N') : Set (Fin 3 → ℤ))ᶜ, F ↑x * latChr ℓ ↑x z) := by
    rw [hrow, ← hsplit]
    ring
  rw [hdiff, norm_neg]
  calc ‖∑' x : ↑(↑(latCube N') : Set (Fin 3 → ℤ))ᶜ, F ↑x * latChr ℓ ↑x z‖
      ≤ ∑' x : ↑(↑(latCube N') : Set (Fin 3 → ℤ))ᶜ, ‖F ↑x * latChr ℓ ↑x z‖ :=
        norm_tsum_le_tsum_norm ((hfsum.subtype _).norm)
    _ = ∑' n : Fin 3 → ℤ, ((↑(latCube N') : Set (Fin 3 → ℤ))ᶜ).indicator
          (fun n => ‖F n * latChr ℓ n z‖) n :=
        tsum_subtype ((↑(latCube N') : Set (Fin 3 → ℤ))ᶜ) (fun n => ‖F n * latChr ℓ n z‖)
    _ = ∑' n : Fin 3 → ℤ, (if ∃ i : Fin 3, (N' : ℤ) < |n i| then ‖F n‖ else 0) := by
        refine tsum_congr (fun n => ?_)
        by_cases hn : n ∈ latCube N'
        · rw [Set.indicator_of_notMem (by simpa using hn),
            if_neg (fun hc => (not_mem_latCube.mpr hc) hn)]
        · rw [Set.indicator_of_mem (by simpa using hn), if_pos (not_mem_latCube.mp hn)]
          simp [norm_latChr]
    _ ≤ ε := hN N' hN'

end Work.BoseBoxFock
