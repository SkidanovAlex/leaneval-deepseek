import Mathlib
import Submission.Work.HP.BCSDefs
import Submission.Work.HP.BCS.lat_span_u_zsmul
import Submission.Work.HP.BCS.map_projU_ball_finite

/-!
# The fibre count for the orthogonal projection onto `u^⊥`

Let `Λ ≤ EuclideanSpace ℝ ι` be a lattice (a `ℤ`-submodule meeting every ball in finitely many
points) and let `u ∈ Λ` be a nonzero vector of minimal norm.  Projecting `Λ` orthogonally onto
`u^⊥` divides its points of norm at most `T` into fibres of at most `2 ⌈T / ‖u‖⌉₊ + 3` points,
whence

`#{x ∈ Λ : ‖x‖ ≤ T} ≤ (2 ⌈T / ‖u‖⌉₊ + 3) * #{y ∈ projU u '' Λ : ‖y‖ ≤ T}`.

The proof is the induction step of Schmidt's bound (as used in `Work.HP.ball_count_schmidt`):
the fibres of `projU u` on `Λ` are cosets of `ℤu` (`projU_coset`), and along such a coset the
squared norm grows like `‖projU u x‖² + n²‖u‖²`, so a fixed fibre meets the ball of radius `T`
in an interval of integers of length at most `2T/‖u‖`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option maxHeartbeats 1000000

noncomputable section

open Work.HP

namespace Work.HP.BCS

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sCnt_le_proj (ι : Type) [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (EuclideanSpace ℝ ι))
    (hfin : ∀ T : ℝ, {x | x ∈ Λ ∧ ‖x‖ ≤ T}.Finite) {u : EuclideanSpace ℝ ι} (hu : u ∈ Λ)
    (hu0 : u ≠ 0) (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖u‖ ≤ ‖x‖) {T : ℝ} (hT : 0 ≤ T) :
    {y | y ∈ Λ.map (projUZ u) ∧ ‖y‖ ≤ T}.Finite ∧
      (sCnt Λ T : ℝ) ≤ (2 * (⌈T / ‖u‖⌉₊ : ℝ) + 3) * (sCnt (Λ.map (projUZ u)) T : ℝ) := by
  classical
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  set K : ℕ := ⌈T / ‖u‖⌉₊ with hK
  set M : Submodule ℤ (EuclideanSpace ℝ ι) := Λ.map (projUZ u) with hM
  set A : Set (EuclideanSpace ℝ ι) := {x | x ∈ Λ ∧ ‖x‖ ≤ T} with hA
  set B : Set (EuclideanSpace ℝ ι) := {y | y ∈ M ∧ ‖y‖ ≤ T} with hB
  set S : Set ℤ := Set.Icc (-((K : ℤ) + 1)) (K : ℤ) with hS
  have hA1 : ∀ {x}, x ∈ A → x ∈ Λ := by intro x hx; rw [hA] at hx; exact hx.1
  have hA2 : ∀ {x}, x ∈ A → ‖x‖ ≤ T := by intro x hx; rw [hA] at hx; exact hx.2
  have hBfin0 : {y : EuclideanSpace ℝ ι | y ∈ Λ.map (projUZ u) ∧ ‖y‖ ≤ T}.Finite :=
    map_projU_ball_finite ι Λ hfin hu hu0 T
  have hBfin : B.Finite := by rw [hB, hM]; exact hBfin0
  have hprojM : ∀ x ∈ Λ, projU u x ∈ M := by
    intro x hx
    rw [hM]
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  have hYex : ∀ y ∈ M, ∃ x : EuclideanSpace ℝ ι, x ∈ Λ ∧ projU u x = y := by
    intro y hy
    rw [hM] at hy
    obtain ⟨x, hx, hxl⟩ := Submodule.mem_map.mp hy
    exact ⟨x, hx, by simpa using hxl⟩
  let Y : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
    fun y => if hy : y ∈ M then Classical.choose (hYex y hy) else 0
  have hY_mem : ∀ y (hy : y ∈ M), Y y ∈ Λ := by
    intro y hy
    have h1 : Y y = Classical.choose (hYex y hy) := by
      simp only [Y, dif_pos hy]
    rw [h1]
    exact (Classical.choose_spec (hYex y hy)).1
  have hY_proj : ∀ y (hy : y ∈ M), projU u (Y y) = y := by
    intro y hy
    have h1 : Y y = Classical.choose (hYex y hy) := by
      simp only [Y, dif_pos hy]
    rw [h1]
    exact (Classical.choose_spec (hYex y hy)).2
  have hnex : ∀ x ∈ A, ∃ m : ℤ, x = Y (projU u x) + (m : ℝ) • u := by
    intro x hx
    have hxΛ := hA1 hx
    have hpM := hprojM x hxΛ
    obtain ⟨m, hm⟩ := projU_coset Λ hu hu0 hmin (hY_mem _ hpM) hxΛ (hY_proj _ hpM)
    exact ⟨m, by rw [Int.cast_smul_eq_zsmul]; exact hm⟩
  let n : EuclideanSpace ℝ ι → ℤ :=
    fun x => if hx : x ∈ A then Classical.choose (hnex x hx) else 0
  have hn : ∀ x (hx : x ∈ A), x = Y (projU u x) + (n x : ℝ) • u := by
    intro x hx
    have h1 : n x = Classical.choose (hnex x hx) := by
      simp only [n, dif_pos hx]
    rw [h1]
    exact Classical.choose_spec (hnex x hx)
  let c : EuclideanSpace ℝ ι → ℝ := fun y => (‖u‖ ^ 2)⁻¹ * inner ℝ (Y y) u
  let k : EuclideanSpace ℝ ι → ℤ := fun y => ⌈-(c y)⌉
  let Φ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι × ℤ :=
    fun x => (projU u x, n x - k (projU u x))
  have hYdecomp : ∀ y (hy : y ∈ M), Y y = y + c y • u := by
    intro y hy
    have h1 : Y y - ((‖u‖ ^ 2)⁻¹ * inner ℝ (Y y) u) • u = projU u (Y y) :=
      (projU_apply u (Y y)).symm
    rw [hY_proj y hy] at h1
    have h2 : Y y = (Y y - ((‖u‖ ^ 2)⁻¹ * inner ℝ (Y y) u) • u)
        + ((‖u‖ ^ 2)⁻¹ * inner ℝ (Y y) u) • u := by abel
    rw [h1] at h2
    exact h2
  have hbound : ∀ x (hx : x ∈ A), |c (projU u x) + (n x : ℝ)| ≤ T / ‖u‖ := by
    intro x hx
    have hxΛ := hA1 hx
    have hpM := hprojM x hxΛ
    have hdecomp : x = projU u x + (c (projU u x) + (n x : ℝ)) • u := by
      conv_lhs => rw [hn x hx]
      rw [hYdecomp (projU u x) hpM, add_assoc, ← add_smul]
    have hpyth : ‖x‖ ^ 2 = ‖projU u x‖ ^ 2 + ((c (projU u x) + (n x : ℝ)) * ‖u‖) ^ 2 := by
      conv_lhs => rw [hdecomp]
      exact norm_sq_add_smul' u (c (projU u x) + (n x : ℝ)) x
    have h1 : ((c (projU u x) + (n x : ℝ)) * ‖u‖) ^ 2 ≤ T ^ 2 := by
      have h2 : ‖x‖ ^ 2 ≤ T ^ 2 := by
        have h3 := hA2 hx
        nlinarith [norm_nonneg x, hT]
      nlinarith [hpyth, sq_nonneg ‖projU u x‖, h2]
    have h3 : |(c (projU u x) + (n x : ℝ)) * ‖u‖| ≤ T := by
      have h4 := sq_le_sq.mp h1
      rwa [abs_of_nonneg hT] at h4
    rw [abs_mul, abs_of_pos hu_norm_pos] at h3
    exact (le_div_iff₀ hu_norm_pos).mpr h3
  have hmemS : ∀ x (hx : x ∈ A), n x - k (projU u x) ∈ S := by
    intro x hx
    have hb := hbound x hx
    have hkeq : (k (projU u x) : ℝ) = ((⌈-(c (projU u x))⌉ : ℤ) : ℝ) := rfl
    have hk1 : (0 : ℝ) ≤ c (projU u x) + (k (projU u x) : ℝ) := by
      rw [hkeq]
      have := Int.le_ceil (-(c (projU u x)))
      linarith
    have hk2 : c (projU u x) + (k (projU u x) : ℝ) < 1 := by
      rw [hkeq]
      have := Int.ceil_lt_add_one (-(c (projU u x)))
      linarith
    have hcast : ((n x - k (projU u x) : ℤ) : ℝ)
        = (c (projU u x) + (n x : ℝ)) - (c (projU u x) + (k (projU u x) : ℝ)) := by
      push_cast
      ring
    have hRK : T / ‖u‖ ≤ (K : ℝ) := Nat.le_ceil _
    have h4 : ((n x - k (projU u x) : ℤ) : ℝ) ≤ (K : ℝ) := by
      rw [hcast]
      have := (abs_le.mp hb).2
      linarith
    have h5 : -((K : ℝ) + 1) ≤ ((n x - k (projU u x) : ℤ) : ℝ) := by
      rw [hcast]
      have := (abs_le.mp hb).1
      linarith
    rw [hS]
    exact ⟨by exact_mod_cast h5, by exact_mod_cast h4⟩
  have hsub : Φ '' A ⊆ B ×ˢ S := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨by
      rw [hB]
      exact ⟨hprojM x (hA1 hx), le_trans (norm_projU_le u x) (hA2 hx)⟩, hmemS x hx⟩
  have hinj : Set.InjOn Φ A := by
    intro x hx x' hx' heq
    have hp : projU u x = projU u x' := congrArg Prod.fst heq
    have hk : n x - k (projU u x) = n x' - k (projU u x') := congrArg Prod.snd heq
    rw [hp] at hk
    have hnn : n x = n x' := by omega
    rw [hn x hx, hn x' hx', hp, hnn]
  have hSfin : S.Finite := Set.finite_Icc _ _
  have hSncard : S.ncard = 2 * K + 2 := by
    rw [hS, Set.ncard_Icc, Int.card_Icc]
    have h2 : (K : ℤ) + 1 - (-((K : ℤ) + 1)) = ((2 * K + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [h2, Int.toNat_natCast]
  have hcount : A.ncard ≤ sCnt (Λ.map (projUZ u)) T * (2 * K + 2) := by
    have hAncard : A.ncard = (Φ '' A).ncard := hinj.ncard_image.symm
    rw [hAncard]
    calc (Φ '' A).ncard ≤ (B ×ˢ S).ncard := Set.ncard_le_ncard hsub (hBfin.prod hSfin)
      _ = B.ncard * S.ncard := Set.ncard_prod
      _ = sCnt (Λ.map (projUZ u)) T * (2 * K + 2) := by
          rw [hSncard]
          congr 1
  have hAcard : A.ncard = sCnt Λ T := by rw [hA]; rfl
  have hmain : sCnt Λ T ≤ sCnt (Λ.map (projUZ u)) T * (2 * K + 2) := by
    rw [← hAcard]
    exact hcount
  have hKcast : (K : ℝ) = (⌈T / ‖u‖⌉₊ : ℝ) := by rw [hK]
  refine ⟨hBfin0, ?_⟩
  · have h1 : (sCnt Λ T : ℝ) ≤ (sCnt (Λ.map (projUZ u)) T : ℝ) * (2 * (K : ℝ) + 2) := by
      have h3 : ((sCnt (Λ.map (projUZ u)) T * (2 * K + 2) : ℕ) : ℝ)
          = (sCnt (Λ.map (projUZ u)) T : ℝ) * (2 * (K : ℝ) + 2) := by push_cast; ring
      calc (sCnt Λ T : ℝ) ≤ ((sCnt (Λ.map (projUZ u)) T * (2 * K + 2) : ℕ) : ℝ) :=
            by exact_mod_cast hmain
        _ = _ := h3
    have h4 : (sCnt (Λ.map (projUZ u)) T : ℝ) * (2 * (K : ℝ) + 2)
        ≤ (sCnt (Λ.map (projUZ u)) T : ℝ) * (2 * (K : ℝ) + 3) := by
      have h5 : (0:ℝ) ≤ (sCnt (Λ.map (projUZ u)) T : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc (sCnt Λ T : ℝ) ≤ (sCnt (Λ.map (projUZ u)) T : ℝ) * (2 * (K : ℝ) + 2) := h1
      _ ≤ (sCnt (Λ.map (projUZ u)) T : ℝ) * (2 * (K : ℝ) + 3) := h4
      _ = (2 * (K : ℝ) + 3) * (sCnt (Λ.map (projUZ u)) T : ℝ) := by ring
      _ = (2 * (⌈T / ‖u‖⌉₊ : ℝ) + 3) * (sCnt (Λ.map (projUZ u)) T : ℝ) := by rw [hKcast]


end Work.HP.BCS
