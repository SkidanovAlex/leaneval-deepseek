import Mathlib
import Submission.Work.Q44Geom.Basic
import Submission.Work.Q44Geom.BadFiberAux
import Submission.Work.Q44Geom.class_rep
import Submission.Work.Q44Geom.exists_close_lam_two
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Q44Child.SuperDefs

namespace Work.Q44Geom

open Work.HP
open Work.HP.Q44Child

/-- A lattice of rank `2` contains no three `ℤ`-linearly independent vectors. -/
private lemma not_three_linIndep_rank_two (N : Submodule ℤ (Fin 5 → ℤ)) (hrk : Work.HP.rk N = 2)
    (f : Fin 3 → (Fin 5 → ℤ)) (hmem : ∀ i, f i ∈ N) : ¬ LinearIndependent ℤ f := by
  intro hf
  let g : Fin 3 → N := fun i => ⟨f i, hmem i⟩
  have hg : LinearIndependent ℤ g := by
    refine LinearIndependent.of_comp (Submodule.subtype N) ?_
    simpa [g, Function.comp_def] using hf
  have hle := hg.fintype_card_le_finrank
  rw [Fintype.card_fin] at hle
  have hrk' : Module.finrank ℤ N = 2 := hrk
  omega

theorem exists_gen_of_lat {c : Work.HP.Mon 4 4 → ℤ} {s : Fin 3 → ℝ}
    {N L : Submodule ℤ (Fin 5 → ℤ)}
    (hNprim : Work.HP.IsPrimLat N) (hNrk : Work.HP.rk N = 2) (hNlam : Work.HP.lam N 2 ≤ s 1)
    (hs12 : s 1 ≤ s 2) (hNL : N ≤ L) (hL : L ∈ Work.Q44Geom.Sset c s) :
    ∃ z : Fin 5 → ℤ, z ∈ L ∧ (∀ w ∈ L, ∃ k : ℤ, ∃ n ∈ N, w = k • z + n) ∧
      1 ≤ Work.HP.eNorm z ∧ Work.HP.eNorm z ≤ 4 * s 2 := by
  obtain ⟨hLprim, hLrk, hs, hvan⟩ := hL
  -- a generator of `L` over the primitive rank-`2` sublattice `N`
  obtain ⟨z₀, hz₀L, hz₀gen⟩ := Work.Q44Geom.BF.gen_of_le N L hNL hNprim hNrk hLrk
  -- three independent vectors of `L` with norm at most `lam L 3`
  obtain ⟨f, hfL, hfind, hfb⟩ :=
    Work.HP.Q44Child.lam_attained L 3 (by norm_num) (by omega)
  have hfb3 : ∀ i, Work.HP.eNorm (f i) ≤ Work.HP.lam L 3 := fun i =>
    (hfb i).trans (Work.HP.lam_mono L (by have h := i.isLt; omega) (by omega))
  -- write each `f i = kk i • z₀ + nn i`
  choose kk nn hnn using fun i => hz₀gen (f i) (hfL i)
  have hex : ∃ i : Fin 3, kk i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    exact not_three_linIndep_rank_two N hNrk f (fun i => by
      have h2 : f i = kk i • z₀ + nn i := (hnn i).2
      rw [h i, zero_smul, zero_add] at h2
      rw [h2]
      exact (hnn i).1) hfind
  obtain ⟨i₀, hk0⟩ := hex
  -- `toE (f i₀) = kk i₀ • toE z₀ + toE (nn i₀)`
  have hto : toE (f i₀) = kk i₀ • toE z₀ + toE (nn i₀) := by
    rw [(hnn i₀).2, map_add, map_zsmul]
  have hπ : proj N (toE (f i₀)) = kk i₀ • proj N (toE z₀) := by
    rw [hto, map_add, map_zsmul, proj_kills_toE N (hnn i₀).1, add_zero]
  -- the orthogonal component of a generator has length at most `lam L 3`
  have hq_le : ‖proj N (toE z₀)‖ ≤ Work.HP.lam L 3 := by
    have hkabs : (1 : ℝ) ≤ |(kk i₀ : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |kk i₀| := Int.one_le_abs hk0
      exact_mod_cast h1
    have h1 : ‖proj N (toE z₀)‖ ≤ ‖proj N (toE (f i₀))‖ := by
      have hmul : ‖proj N (toE (f i₀))‖ = |(kk i₀ : ℝ)| * ‖proj N (toE z₀)‖ := by
        rw [hπ, norm_zsmul ℝ (kk i₀) (proj N (toE z₀)), Real.norm_eq_abs]
      rw [hmul]
      calc ‖proj N (toE z₀)‖
          = 1 * ‖proj N (toE z₀)‖ := (one_mul _).symm
        _ ≤ |(kk i₀ : ℝ)| * ‖proj N (toE z₀)‖ :=
            mul_le_mul_of_nonneg_right hkabs (norm_nonneg _)
    refine h1.trans ?_
    calc ‖proj N (toE (f i₀))‖ ≤ ‖toE (f i₀)‖ := norm_proj_le N _
      _ = Work.HP.eNorm (f i₀) := norm_toE (f i₀)
      _ ≤ Work.HP.lam L 3 := hfb3 i₀
  -- the component of `toE z₀` in `Lℝ N`
  have hp_mem : toE z₀ - proj N (toE z₀) ∈ Lℝ N := by
    have h := Submodule.sub_starProjection_mem_orthogonal (K := W N) (toE z₀)
    have h2 : (W N)ᗮ = Lℝ N := by
      rw [W, Submodule.orthogonal_orthogonal]
    simpa [proj, h2] using h
  obtain ⟨n, hnN, hbound⟩ := exists_close_lam_two N hNrk (toE z₀ - proj N (toE z₀)) hp_mem
  refine ⟨z₀ - n, Submodule.sub_mem L hz₀L (hNL hnN), ?_, ?_, ?_⟩
  · intro w hwL
    obtain ⟨k, m, hmN, hwm⟩ := hz₀gen w hwL
    refine ⟨k, k • n + m, Submodule.add_mem N (Submodule.smul_mem N k hnN) hmN, ?_⟩
    rw [hwm]
    show k • z₀ + m = k • (z₀ - n) + (k • n + m)
    rw [smul_sub]
    abel
  · -- the generator is nonzero, hence of norm at least `1`
    have hz_ne : z₀ - n ≠ 0 := by
      intro hz0
      have hz₀N : z₀ ∈ N := by
        have hzn : z₀ = n := sub_eq_zero.mp hz0
        rw [hzn]; exact hnN
      have hLleN : L ≤ N := by
        intro w hw
        obtain ⟨k, m, hmN, hwm⟩ := hz₀gen w hw
        rw [hwm]
        exact Submodule.add_mem N (Submodule.smul_mem N k hz₀N) hmN
      have hEq : L = N := le_antisymm hLleN hNL
      have hrk : Work.HP.rk L = Work.HP.rk N := by rw [hEq]
      rw [hLrk, hNrk] at hrk
      exact absurd hrk (by norm_num)
    exact Work.HP.one_le_eNorm_of_ne_zero hz_ne
  · -- the sharp norm bound, and `lam N 2, lam L 3 ≤ s 2`
    have htoz : toE (z₀ - n)
        = (toE z₀ - proj N (toE z₀) - toE n) + proj N (toE z₀) := by
      rw [map_sub]; abel
    have hnorm : Work.HP.eNorm (z₀ - n) ≤ Work.HP.lam N 2 + Work.HP.lam L 3 := by
      rw [← norm_toE (z₀ - n), htoz]
      exact (norm_add_le _ _).trans (add_le_add hbound hq_le)
    have hL3 : Work.HP.lam L 3 ≤ s 2 := hs 2
    have hN2 : Work.HP.lam N 2 ≤ s 2 := le_trans hNlam hs12
    have hs2 : (0 : ℝ) ≤ s 2 := le_trans (le_trans (Work.HP.lam_nonneg N 2) hNlam) hs12
    calc Work.HP.eNorm (z₀ - n) ≤ Work.HP.lam N 2 + Work.HP.lam L 3 := hnorm
      _ ≤ s 2 + s 2 := add_le_add hN2 hL3
      _ = 2 * s 2 := by ring
      _ ≤ 4 * s 2 := by linarith

end Work.Q44Geom
