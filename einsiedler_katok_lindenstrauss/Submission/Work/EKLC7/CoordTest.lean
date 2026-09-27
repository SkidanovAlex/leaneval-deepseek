import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.HeisMul

/-!
# C7 (`CoordTest`): cutting down a coordinate-function on the Heisenberg triple to `SL₃(ℝ)`

For a triple `i, j, k` of *distinct* indices of `Fin 3` and continuous compactly supported
functions `F : ℝ × ℝ → ℝ`, `h : ℝ → ℝ`, the function `(p, q, r) ↦ F (p, r) * h q` on the
Heisenberg parametrisation `heis p q r` extends to a compactly supported continuous function on
`SL₃(ℝ)`.

The construction is the obvious one: `g ↦ F (gᵢⱼ, gⱼₖ) * h (gᵢₖ) * χ g`, where `χ` is a bump
function on the space of `3 × 3` matrices which is `1` on all matrices of the form
`1 + p Eᵢⱼ + q Eᵢₖ + r Eⱼₖ` with `(p, r)` in the support of `F` and `q` in the support of `h`,
and which is compactly supported (a product of a one dimensional bump over the nine entries).
The product is continuous, and on `heis p q r` the three entries `(i,j)`, `(i,k)`, `(j,k)` are
`p`, `q`, `r` (lemma `pcoord_heis` etc.); when `F (p, r) * h q ≠ 0` the point `(p, r)` lies in
the (compact) support of `F` and `q` in the support of `h`, so the bump takes the value `1`
there, and otherwise a factor is `0` and there is nothing to check.  Compact support is
transferred from the matrix space to `SL₃(ℝ)` along the closed embedding `toMat`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open Work.EKLContract

namespace Work.EKLC7

/-! ## Bounding a continuous coordinate on a compact set -/

/-- An absolute bound on a compact subset of `ℝ`. -/
lemma isCompact_exists_abs_bound (K : Set ℝ) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |x| ≤ M := by
  by_cases hne : K.Nonempty
  · obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hK.isBounded
    obtain ⟨x₀, hx₀⟩ := hne
    have hC0 : 0 ≤ C := by have := hC hx₀ hx₀; simpa using this
    refine ⟨C + |x₀|, by positivity, fun x hx => ?_⟩
    have hd : dist x x₀ ≤ C := hC hx hx₀
    rw [Real.dist_eq] at hd
    calc |x| = |(x - x₀) + x₀| := by ring_nf
      _ ≤ |x - x₀| + |x₀| := abs_add_le _ _
      _ ≤ C + |x₀| := by linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨0, le_refl 0, fun x hx => ?_⟩
    rw [hne] at hx
    exact absurd hx (Set.notMem_empty x)

/-- An absolute bound on both coordinates of a compact subset of `ℝ × ℝ`. -/
lemma isCompact_exists_abs_bound_prod (K : Set (ℝ × ℝ)) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, |z.1| ≤ M ∧ |z.2| ≤ M := by
  obtain ⟨M1, hM1nn, hM1⟩ := isCompact_exists_abs_bound (Prod.fst '' K) (hK.image continuous_fst)
  obtain ⟨M2, hM2nn, hM2⟩ := isCompact_exists_abs_bound (Prod.snd '' K) (hK.image continuous_snd)
  exact ⟨max M1 M2, le_trans hM1nn (le_max_left _ _),
    fun z hz => ⟨le_trans (hM1 z.1 ⟨z, hz, rfl⟩) (le_max_left _ _),
                  le_trans (hM2 z.2 ⟨z, hz, rfl⟩) (le_max_right _ _)⟩⟩

/-! ## A bump function on the space of matrices -/

/-- A product of one bump function over the nine entries of a matrix is continuous. -/
lemma continuous_prod_entries {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => ∏ a : Fin 3, ∏ b : Fin 3, ψ (A a b)) := by
  fun_prop

/-- A product of one bump function over the nine entries of a matrix has compact support: its
support is contained in the (compact) product of nine copies of the support of the bump. -/
lemma hasCompactSupport_prod_entries {ψ : ℝ → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (fun A : Matrix (Fin 3) (Fin 3) ℝ => ∏ a : Fin 3, ∏ b : Fin 3, ψ (A a b)) := by
  rw [hasCompactSupport_def]
  refine IsCompact.of_isClosed_subset hψ.matrix isClosed_closure
    (closure_minimal ?_ hψ.matrix.isClosed)
  intro A hA
  simp only [Function.support, Set.mem_ofPred_eq, Finset.prod_ne_zero_iff, Finset.mem_univ,
    true_implies] at hA
  simp only [Set.matrix, Set.mem_ofPred_eq]
  intro a b
  exact subset_tsupport ψ (hA a b)

/-- All nine entries of `heis p q r` are bounded by `1 + |p| + |q| + |r|` (the entries are of the
form `0`, `1`, `p`, `q` or `r`, and at most one of the off-diagonal ones is non-zero). -/
lemma abs_toMat_heis_apply_le {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (p q r : ℝ) (a b : Fin 3) :
    |toMat (heis hij hjk hik p q r) a b| ≤ 1 + |p| + |q| + |r| := by
  rw [toMat_heis hij hjk hik, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply, Matrix.single_apply, Matrix.single_apply]
  set X : ℝ := (if a = b then (1 : ℝ) else 0) with hX
  set Y : ℝ := (if i = a ∧ j = b then p else 0) with hY
  set Z : ℝ := (if i = a ∧ k = b then q else 0) with hZ
  set W : ℝ := (if j = a ∧ k = b then r else 0) with hW
  have h1 : |X| ≤ 1 := by rw [hX]; split_ifs <;> simp
  have h2 : |Y| ≤ |p| := by rw [hY]; split_ifs <;> simp
  have h3 : |Z| ≤ |q| := by rw [hZ]; split_ifs <;> simp
  have h4 : |W| ≤ |r| := by rw [hW]; split_ifs <;> simp
  have hsum : |((X + Y) + Z) + W| ≤ |X| + |Y| + |Z| + |W| := by
    calc |((X + Y) + Z) + W| ≤ |(X + Y) + Z| + |W| := abs_add_le _ _
      _ ≤ (|X + Y| + |Z|) + |W| := by linarith [abs_add_le (X + Y) Z]
      _ ≤ ((|X| + |Y|) + |Z|) + |W| := by linarith [abs_add_le X Y]
  linarith

/-! ## The coordinate test function -/

theorem CoordTest : ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (F : ℝ × ℝ → ℝ) (h : ℝ → ℝ), Continuous F → Continuous h →
    HasCompactSupport F → HasCompactSupport h →
    ∃ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      ∀ p q r : ℝ, f (Work.EKLC7.heis hij hjk hik p q r) = F (p, r) * h q := by
  intro i j k hij hjk hik F h hFc hhc hFsup hhsup
  -- bounds on the (compact) supports of `F` and `h`
  obtain ⟨M1, hM1nn, hM1⟩ := isCompact_exists_abs_bound_prod (tsupport F) hFsup
  obtain ⟨M2, hM2nn, hM2⟩ := isCompact_exists_abs_bound (tsupport h) hhsup
  set M : ℝ := max 1 (max M1 M2) with hMdef
  have hM1le : M1 ≤ M := by rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hM2le : M2 ≤ M := by rw [hMdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have h1M : (1 : ℝ) ≤ M := by rw [hMdef]; exact le_max_left _ _
  have h0M : (0 : ℝ) ≤ M := le_trans zero_le_one h1M
  set N : ℝ := 4 * M + 1 with hNdef
  have hMN : M ≤ N := by rw [hNdef]; linarith
  have h0N : (0 : ℝ) ≤ N := by rw [hNdef]; linarith
  have h1N : (1 : ℝ) ≤ N := by rw [hNdef]; linarith
  -- a one dimensional bump which is `1` on `[-N, N]`
  obtain ⟨ψ, hψ1, -, hψsup, -⟩ :=
    exists_continuous_one_zero_of_isCompact (s := Set.Icc (-N) N) (t := ∅) isCompact_Icc
      isClosed_empty (Set.disjoint_empty _)
  -- the matrix bump `χ`: the product of `ψ` over the nine entries
  let χ : Matrix (Fin 3) (Fin 3) ℝ → ℝ := fun A => ∏ a : Fin 3, ∏ b : Fin 3, ψ (A a b)
  have hχcont : Continuous χ := by
    show Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => ∏ a : Fin 3, ∏ b : Fin 3, ⇑ψ (A a b))
    exact continuous_prod_entries ψ.continuous
  have hχsup : HasCompactSupport χ := by
    show HasCompactSupport (fun A : Matrix (Fin 3) (Fin 3) ℝ =>
      ∏ a : Fin 3, ∏ b : Fin 3, ⇑ψ (A a b))
    exact hasCompactSupport_prod_entries hψsup
  -- the test function on `SL₃(ℝ)`
  let f0 : SL3 → ℝ := fun g => F (pcoord i j g, rcoord j k g) * h (qcoord i k g) * χ (toMat g)
  have hf0cont : Continuous f0 := by
    have hA : Continuous fun g : SL3 => F (pcoord i j g, rcoord j k g) :=
      hFc.comp ((continuous_pcoord i j).prodMk (continuous_rcoord j k))
    have hB : Continuous fun g : SL3 => h (qcoord i k g) := hhc.comp (continuous_qcoord i k)
    have hC : Continuous fun g : SL3 => χ (toMat g) := hχcont.comp continuous_subtype_val
    exact (hA.mul hB).mul hC
  have hf0sup : HasCompactSupport f0 := by
    have htoMat : Topology.IsClosedEmbedding (toMat : SL3 → Matrix (Fin 3) (Fin 3) ℝ) :=
      Topology.IsClosedEmbedding.subtypeVal (p := fun A : Matrix (Fin 3) (Fin 3) ℝ => A.det = 1)
        (isClosed_eq (Continuous.matrix_det continuous_id) continuous_const)
    have hC : HasCompactSupport fun g : SL3 => χ (toMat g) :=
      HasCompactSupport.comp_isClosedEmbedding hχsup htoMat
    exact HasCompactSupport.mul_left hC
  refine ⟨⟨⟨f0, hf0cont⟩, hf0sup⟩, ?_⟩
  intro p q r
  have hval : f0 (heis hij hjk hik p q r)
      = F (p, r) * h q * χ (toMat (heis hij hjk hik p q r)) := by
    simp only [f0, pcoord_heis hij hjk hik, qcoord_heis hij hjk hik, rcoord_heis hij hjk hik]
  show f0 (heis hij hjk hik p q r) = F (p, r) * h q
  rw [hval]
  by_cases hz : F (p, r) * h q = 0
  · rw [hz]; simp
  · have hFne : F (p, r) ≠ 0 := fun hc => hz (by rw [hc, zero_mul])
    have hhne : h q ≠ 0 := fun hc => hz (by rw [hc, mul_zero])
    have hpr : (p, r) ∈ tsupport F := subset_tsupport F (by simpa using hFne)
    have hqK : q ∈ tsupport h := subset_tsupport h (by simpa using hhne)
    have hp : |p| ≤ M := le_trans (hM1 (p, r) hpr).1 hM1le
    have hr : |r| ≤ M := le_trans (hM1 (p, r) hpr).2 hM1le
    have hq : |q| ≤ M := le_trans (hM2 q hqK) hM2le
    -- the bump is `1` at `heis p q r`, because all nine entries lie in `[-N, N]`
    have hχval : χ (toMat (heis hij hjk hik p q r)) = 1 := by
      show (∏ a : Fin 3, ∏ b : Fin 3, ⇑ψ (toMat (heis hij hjk hik p q r) a b)) = 1
      apply Finset.prod_eq_one
      intro a _
      apply Finset.prod_eq_one
      intro b _
      apply hψ1
      rw [Set.mem_Icc]
      exact abs_le.mp (le_trans (abs_toMat_heis_apply_le hij hjk hik p q r a b) (by linarith))
    rw [hχval, mul_one]

end Work.EKLC7
