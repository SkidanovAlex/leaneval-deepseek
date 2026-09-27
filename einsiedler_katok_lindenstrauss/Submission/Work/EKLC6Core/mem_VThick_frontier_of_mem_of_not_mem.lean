import Mathlib
import Submission.Work.EKLC6Core.cut_defs
import Submission.Work.EKLC6Core.path_unipotent_in_V
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.exists_mem_frontier_of_continuousOn

namespace Work.EKLC6Core

private lemma det_one_add_of_cube_eq_zero (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A ^ 3 = 0) :
    (1 + A).det = 1 := by
  have hnil : IsNilpotent (Matrix.toLin' A) := by
    refine ⟨3, ?_⟩
    rw [← Matrix.toLin'_pow, hA]
    exact map_zero _
  have hcp : A.charpoly = Polynomial.X ^ 3 := by
    have h1 : (Matrix.toLin' A).charpoly
        = Polynomial.X ^ (Module.finrank ℝ (Fin 3 → ℝ)) :=
      IsNilpotent.charpoly_eq_X_pow_finrank hnil
    rw [← Matrix.charpoly_toLin', h1]
    congr 1
    simp
  have he := Matrix.eval_charpoly A (-1)
  rw [hcp] at he
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at he
  have hscalar : Matrix.scalar (Fin 3) (-1 : ℝ) - A = -(1 + A) := by
    rw [map_neg, map_one]
    abel
  rw [hscalar, Matrix.det_neg, Fintype.card_fin] at he
  norm_num at he
  linarith

private lemma cube_smul_add_smul_sq_eq_zero (N : Matrix (Fin 3) (Fin 3) ℝ) (hN : N ^ 3 = 0)
    (a b : ℝ) : (a • N + b • (N * N)) ^ 3 = 0 := by
  have hPN : Commute (a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + b • N) N := by
    show (a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + b • N) * N
        = N * (a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + b • N)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hA : (a • N + b • (N * N)) = (a • (1 : Matrix (Fin 3) (Fin 3) ℝ) + b • N) * N := by
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
  rw [hA, Commute.mul_pow hPN 3, hN, mul_zero]

private lemma mul_smul_add_smul_sq (N : Matrix (Fin 3) (Fin 3) ℝ) (hN : N ^ 3 = 0)
    (a b c d : ℝ) :
    (a • N + b • (N * N)) * (c • N + d • (N * N)) = (a * c) • (N * N) := by
  have hNNN : N * N * N = 0 := by simpa [pow_succ, pow_two] using hN
  have hNss : N * (N * N) = 0 := by rw [← Matrix.mul_assoc N N N, hNNN]
  have hsss : (N * N) * (N * N) = 0 := by
    rw [← Matrix.mul_assoc (N * N) N N, hNNN, Matrix.zero_mul]
  have hss : ∀ (x y : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ), x • y • M = (x * y) • M := by
    intro x y M
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  have hp1 : (a • N) * (c • N) = (a * c) • (N * N) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hss]
  have hp2 : (a • N) * (d • (N * N)) = (a * d) • (N * (N * N)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hss]
  have hp3 : (b • (N * N)) * (c • N) = (b * c) • ((N * N) * N) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hss]
  have hp4 : (b • (N * N)) * (d • (N * N)) = (b * d) • ((N * N) * (N * N)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hss]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  rw [hp1, hp2, hp3, hp4]
  rw [hNss, hNNN, hsss]
  simp

private lemma entry_bound {N : Matrix (Fin 3) (Fin 3) ℝ} {c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1) (hN : ∀ i j, |N i j| < c) {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (i j : Fin 3) : |(a • N + b • (N * N)) i j| < 4 * c := by
  have hNN : |(N * N) i j| < 3 * c ^ 2 := by
    have hk : ∀ k : Fin 3, |N i k * N k j| < c ^ 2 := fun k => by
      rw [abs_mul]
      calc |N i k| * |N k j| < c * c :=
            mul_lt_mul'' (hN i k) (hN k j) (abs_nonneg _) (abs_nonneg _)
        _ = c ^ 2 := by ring
    calc |(N * N) i j| ≤ ∑ k : Fin 3, |N i k * N k j| := by
          rw [Matrix.mul_apply]
          exact Finset.abs_sum_le_sum_abs _ _
      _ < ∑ _k : Fin 3, c ^ 2 :=
          Finset.sum_lt_sum (fun k _ => le_of_lt (hk k)) ⟨0, Finset.mem_univ _, hk 0⟩
      _ = 3 * c ^ 2 := by rw [Fin.sum_univ_three]; ring
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  have h1 : |a * N i j| < c := by
    rw [abs_mul]
    calc |a| * |N i j| ≤ 1 * |N i j| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      _ = |N i j| := one_mul _
      _ < c := hN i j
  have h2 : |b * (N * N) i j| < 3 * c ^ 2 := by
    rw [abs_mul]
    calc |b| * |(N * N) i j| ≤ 1 * |(N * N) i j| :=
          mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = |(N * N) i j| := one_mul _
      _ < 3 * c ^ 2 := hNN
  have htri := abs_add_le (a * N i j) (b * (N * N) i j)
  have hc2 : c ^ 2 ≤ c := by nlinarith
  linarith [htri, h1, h2, hc, hc2]

/-- **A path in `V (20 c)` from `1` to a unipotent `q ∈ V c`, with inverses still in
`V (20 c)`.**  The explicit polynomial path `s ↦ 1 + s • N + ((s²-s)/2) • N²` (`N = q - 1`,
`N³ = 0`) is used: it satisfies `F s * F (-s) = 1` and `det (F s) = 1`, and every entry of
`F s - 1` and (for `s ∈ [0,1]`) of `F (-s) - 1 = (F s)⁻¹ - 1` is `< c + 3c² ≤ 4c ≤ 20c`. -/
private theorem unipotent_path_V_inv_local {q : Work.EKLContract.SL3} {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hV : q ∈ Work.EKLContract.V c)
    (hnil : ((q : Matrix (Fin 3) (Fin 3) ℝ) - 1) ^ 3 = 0) :
    ∃ γ : ℝ → Work.EKLContract.SL3, Continuous γ ∧ γ 0 = 1 ∧ γ 1 = q ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ Work.EKLContract.V (20 * c) ∧
        (γ s)⁻¹ ∈ Work.EKLContract.V (20 * c) := by
  set N : Matrix (Fin 3) (Fin 3) ℝ := (q : Matrix (Fin 3) (Fin 3) ℝ) - 1 with hN
  have hN3 : N ^ 3 = 0 := by rw [hN]; exact hnil
  have hNen : ∀ i j, |N i j| < c := by
    intro i j
    have h := hV i j
    rw [hN, Matrix.sub_apply]
    exact h
  let A : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun s => s • N + ((s ^ 2 - s) / 2) • (N * N)
  let F : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun s => 1 + A s
  have hF0 : F 0 = 1 := by simp [F, A]
  have hF1 : F 1 = (q : Matrix (Fin 3) (Fin 3) ℝ) := by
    simp only [F, A, one_pow, sub_self, zero_div, zero_smul, add_zero, one_smul]
    rw [hN]
    abel
  have hmul : ∀ s : ℝ, F s * F (-s) = 1 := by
    intro s
    have hPQ : A s * A (-s) = (s * (-s)) • (N * N) :=
      mul_smul_add_smul_sq N hN3 s ((s ^ 2 - s) / 2) (-s) (((-s) ^ 2 - (-s)) / 2)
    have hexp : F s * F (-s) = 1 + A (-s) + (A s + A s * A (-s)) := by
      simp only [F, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [hexp]
    simp only [A] at hPQ ⊢
    rw [hPQ]
    module
  have hdet : ∀ s : ℝ, (F s).det = 1 := fun s =>
    det_one_add_of_cube_eq_zero (A s) (by
      simpa only [A] using cube_smul_add_smul_sq_eq_zero N hN3 s ((s ^ 2 - s) / 2))
  let hpath : ℝ → Work.EKLContract.SL3 := fun s => ⟨F s, hdet s⟩
  refine ⟨hpath, ?_, ?_, ?_, ?_⟩
  · have hcont : Continuous F := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      show Continuous fun s : ℝ => F s i j
      simp only [F, A, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      fun_prop
    have hsl3 : Continuous (fun s : ℝ => (⟨F s, hdet s⟩ : Work.EKLContract.SL3)) :=
      hcont.subtype_mk _
    exact hsl3
  · apply Subtype.ext
    ext i j
    show F 0 i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
    rw [hF0]
  · apply Subtype.ext
    ext i j
    show F 1 i j = (q : Matrix (Fin 3) (Fin 3) ℝ) i j
    rw [hF1]
  · intro s hs
    have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
    have hs2 : |(s ^ 2 - s) / 2| ≤ 1 := by
      have h1 : s ^ 2 - s ≤ 1 / 2 := by nlinarith [hs.1, hs.2]
      have h2 : -(1 / 2) ≤ s ^ 2 - s := by nlinarith [hs.1, hs.2]
      have h3 : |s ^ 2 - s| ≤ 1 / 2 := abs_le.mpr ⟨h2, h1⟩
      calc |(s ^ 2 - s) / 2| = |s ^ 2 - s| / 2 := by rw [abs_div]; norm_num
        _ ≤ (1 / 2) / 2 := by linarith
        _ ≤ 1 := by norm_num
    have hs1' : |-s| ≤ 1 := by rw [abs_neg]; exact hs1
    have hs2' : |((-s) ^ 2 - (-s)) / 2| ≤ 1 := by
      have h2 : ((-s) ^ 2 - (-s)) / 2 ≤ 1 := by
        nlinarith [hs.1, hs.2, mul_self_le_mul_self hs.1 hs.2]
      have h3 : -(1 : ℝ) ≤ ((-s) ^ 2 - (-s)) / 2 := by nlinarith [hs.1, sq_nonneg s]
      exact abs_le.mpr ⟨h3, h2⟩
    constructor
    · intro i j
      show |F s i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 20 * c
      rw [show F s i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = A s i j by
        simp only [F, A, Matrix.add_apply]; ring]
      exact lt_of_lt_of_le
        (entry_bound hc hc1 hNen (a := s) (b := (s ^ 2 - s) / 2) hs1 hs2 i j)
        (by linarith)
    · have hadj : (F s).adjugate = F (-s) := by
        have h1 : (F s)⁻¹ = F (-s) := Matrix.inv_eq_right_inv (hmul s)
        have h2 : (F s)⁻¹ = (F s).adjugate := Matrix.inv_eq_left_inv (by
          rw [Matrix.adjugate_mul, hdet s, one_smul])
        rw [← h2, h1]
      intro i j
      show |(F s).adjugate i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 20 * c
      rw [hadj]
      show |F (-s) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 20 * c
      rw [show F (-s) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j = A (-s) i j by
        simp only [F, A, Matrix.add_apply]; ring]
      exact lt_of_lt_of_le
        (entry_bound hc hc1 hNen (a := -s) (b := ((-s) ^ 2 - (-s)) / 2) hs1' hs2' i j)
        (by linarith)


/-- **The crossing lemma (Pisa 7.31, geometric half).**

Let `Y ⊆ X₃` be open, `U ≤ SL₃(ℝ)` a subgroup all of whose elements are unipotent
(`(u - 1)³ = 0`, which holds for every `u` in a subgroup contracted by a diagonal flow), and let
`q ∈ U ∩ V t` with `0 < t ≤ 1`.  If `z` and `q • z` are separated by `Y` (one in `Y`, the other
outside), then `z` lies in the `20 t`-thickening of the frontier of `Y`:

    z ∈ VThick (20 t) (frontier Y),   VThick η S = (V η) • S.

This is the step that turns the "thin boundary" estimate of Pisa 7.27 into the shell/Borel–Cantelli
estimate of Pisa 7.31: the failure of the "point is deep inside its cell" condition at level `n`
then forces the orbit point `aⁿ x` into the `c·λⁿ`-thickening of the union of the cell frontiers.

Proof: let `p s := γ s • z` for a continuous path `γ` from `1` to `q` inside `V (4t)` (sibling
lemma `Work.EKLC6Core.path_unipotent_in_V` with `c := t ≤ 1`; its hypothesis `c ≤ 1` is `ht1`).
The set `{s | p s ∈ Y}` is relatively open in `[0,1]` (with `Y` open), contains one end of `[0,1]`
and not the other; at the crossing time `s₀` the point `p s₀` lies in
`closure Y ∩ closure Yᶜ = frontier Y`.  Finally `z = (γ s₀)⁻¹ • (γ s₀ • z)`.

NOTE for the constant: use the *explicit* polynomial path element
`F s = 1 + s·N + ((s² - s)/2)·N²` (with `N = q - 1`, `N³ = 0`), whose inverse is
`F s⁻¹ = 1 - s·N + ((s² + s)/2)·N²`, entrywise within `t + 3t² ≤ 4t ≤ 20t` of `1`.  (The generic
inverse bound `g ∈ V η ⟹ g⁻¹ ∈ V (10η)` would give only `40t`, so the explicit form matters.) -/
theorem mem_VThick_frontier_of_mem_of_not_mem {U : Subgroup Work.EKLContract.SL3}
    (huni : ∀ u ∈ U, ((u : Matrix (Fin 3) (Fin 3) ℝ) - 1) ^ 3 = 0)
    {Y : Set Work.EKLContract.X3} (hY : IsOpen Y) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    {z : Work.EKLContract.X3} (q : Work.EKLContract.SL3) (hqU : q ∈ U)
    (hqV : q ∈ Work.EKLContract.V t)
    (h : (z ∈ Y ∧ q • z ∉ Y) ∨ (z ∉ Y ∧ q • z ∈ Y)) :
    z ∈ Work.EKLC6Core.VThick (20 * t) (frontier Y) := by
  obtain ⟨γ, hγcont, hγ0, hγ1, hγmem⟩ :=
    unipotent_path_V_inv_local ht0 ht1 hqV (huni q hqU)
  have hcont : ContinuousOn (fun s : ℝ => γ s • z) (Set.Icc (0 : ℝ) 1) :=
    ContinuousOn.smul hγcont.continuousOn continuousOn_const
  rcases h with ⟨hzY, hqzY⟩ | ⟨hzY, hqzY⟩
  · obtain ⟨s₀, hs₀, hfr⟩ := exists_mem_frontier_of_continuousOn hcont (S := Y)
      (by rw [hγ0, one_smul]; exact hzY) (by rw [hγ1]; exact hqzY)
    exact mem_VThick.mpr ⟨γ s₀ • z, hfr, (γ s₀)⁻¹, (hγmem s₀ hs₀).2, by
      rw [← mul_smul, inv_mul_cancel, one_smul]⟩
  · obtain ⟨s₀, hs₀, hfr⟩ := exists_mem_frontier_of_continuousOn hcont (S := Yᶜ)
      (by rw [hγ0, one_smul]; exact hzY) (by rw [hγ1]; simpa using hqzY)
    rw [frontier_compl] at hfr
    exact mem_VThick.mpr ⟨γ s₀ • z, hfr, (γ s₀)⁻¹, (hγmem s₀ hs₀).2, by
      rw [← mul_smul, inv_mul_cancel, one_smul]⟩

end Work.EKLC6Core
